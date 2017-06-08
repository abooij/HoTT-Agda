{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.Coinduction {{_ : COIND}} where

infix 100 ♯_

postulate  -- Coinduction
  ∞  : ∀ {i} (A : Type i) → Type i
  ♯_ : ∀ {i} {A : Type i} → A → ∞ A
  ♭  : ∀ {i} {A : Type i} → ∞ A → A
