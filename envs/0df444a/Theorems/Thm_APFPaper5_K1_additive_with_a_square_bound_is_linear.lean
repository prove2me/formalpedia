-- Prove2me | Theorems.Thm_APFPaper5_K1_additive_with_a_square_bound_is_linear
-- name    : APFPaper5.K1.additive_with_a_square_bound_is_linear
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T03:56:59.50728+00:00
-- url     : https://prove2.me/theorems/ecb60d64-4f73-4ffd-a745-1711c8a83ed5
-- title:
--   additive with a square bound is linear
-- statement:
--   A function on the reals that adds, and is bounded by a multiple of (s squared and one), is a multiple
--   of its argument.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem additive_with_a_square_bound_is_linear (φ : ℝ → ℝ) (K : ℝ)
--       (hadd : ∀ s t : ℝ, φ (s + t) = φ s + φ t)
--       (hb : ∀ s : ℝ, |φ s| ≤ K * (s * s + 1)) :
--       ∀ s : ℝ, φ s = s * φ 1
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:126; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.additive_with_a_square_bound_is_linear :
∀ (φ : Real → Real) (K : Real)
  (hadd :
    ∀ (s t : Real),
      @Eq.{1} Real (φ (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) s t))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (φ s) (φ t)))
  (hb :
    ∀ (s : Real),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (φ s))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) K
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (s : Real),
  @Eq.{1} Real (φ s)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s
      (φ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) := by sorry
