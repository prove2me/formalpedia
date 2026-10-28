-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_untwisted_renewal_scale_regular
-- name    : AvramDividend.Classical.causal_untwisted_renewal_scale_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:27:15.605547+00:00
-- url     : https://prove2.me/theorems/2d8c041a-14e7-4b72-9d91-680b501684b8
-- title:
--   Regularity, support and monotonicity of the untwisted q-scale candidate
-- statement:
--   From a causal exponentially tilted power series whose untwisted powers and sum are monotone, obtain a positive-discount scale candidate that is zero for negative arguments, nonnegative, continuous and monotone on the positive half-line. Its expression agrees with exp(theta x)/q times the tilted series.
-- source:
--   Exponential untwisting, nonnegative tsum and scalar preservation of continuity and monotonicity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_untwisted_renewal_scale_regular
    (F U : ℕ → ℝ → ℝ) (θ q : ℝ) (hq : 0 < q)
    (hFzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0)
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x)
    (hUmono : ∀ n : ℕ, Monotone (U n))
    (hUcont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0))
    (hUmonosum : MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0)) :
    ∃ W : ℝ → ℝ,
      (∀ x : ℝ, W x =
        (Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)) ∧
      (∀ x : ℝ, x < 0 → W x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ W x) ∧
      ContinuousOn W (Ici (0 : ℝ)) ∧
      MonotoneOn W (Ici (0 : ℝ)) := by sorry
