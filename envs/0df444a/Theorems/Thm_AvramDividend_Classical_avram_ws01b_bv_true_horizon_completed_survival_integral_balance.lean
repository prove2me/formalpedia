-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_true_horizon_completed_survival_integral_balance
-- name    : AvramDividend.Classical.avram_ws01b_bv_true_horizon_completed_survival_integral_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T14:18:16.33467+00:00
-- url     : https://prove2.me/theorems/f8432a5a-ff52-4e5e-b018-35f118949f9c
-- title:
--   Original bounded variation killed horizon completed/surviving payoff expectation identity
-- statement:
--   The explicit sum of genuine original Lévy completed upper-first discounted scale reward and surviving finite-horizon discounted scale reward is Bochner integrable and has expectation Wq(x) under Standing BV, q>0; no mesh or moment assumptions.
-- source:
--   Canonical original finite-horizon expectation without mesh and pointwise true stopped horizon reward split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation_no_mesh
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_horizon_killed_reward_two_way_split

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_true_horizon_completed_survival_integral_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let S : Ω → ℝ := fun ω =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0);
    Integrable S P ∧ (∫ ω, S ω ∂P) = W x) := by sorry
