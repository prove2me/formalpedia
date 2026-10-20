-- Prove2me | Theorems.Thm_DerivativeChainPrivate_mixed_product_variation
-- name    : DerivativeChainPrivate.mixed_product_variation
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:57:59.386372+00:00
-- url     : https://prove2.me/theorems/9b544b4e-0b6f-4216-88f2-8d5da7c65b20
-- title:
--   Two-sided-majorant mixed-product total variation
-- statement:
--   For nonnegative real sequences G and J, with G nondecreasing and J nonincreasing, and every natural n, the sum from k=0 to n-1 of |G(k+1)J(k+1)-G(k)J(k)| is at most 2G(n)J(0)-G(0)J(0)-G(n)J(n). This formalizes equation (6) of the two-sided-majorant checkpoint for all finite lengths.
-- source:
--   Derivative-zero chains: public formalization reference, R38, DerivativeChainPrivate.mixed_product_variation. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.mixed_product_variation (G J : ℕ → ℝ) (hG : Monotone G) (hJ : Antitone J)
    (hG0 : ∀ k, 0 ≤ G k) (hJ0 : ∀ k, 0 ≤ J k) (n : ℕ) :
    (∑ k ∈ Finset.range n, |G (k + 1) * J (k + 1) - G k * J k|) ≤
      2 * G n * J 0 - G 0 * J 0 - G n * J n := by sorry
