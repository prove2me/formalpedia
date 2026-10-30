-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
-- name    : AvramDividend.Classical.avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:25:52.762983+00:00
-- url     : https://prove2.me/theorems/36dd3377-7103-4517-889e-e6fc08644c45
-- title:
--   Actual UBV completed upper-first and surviving horizon killed reward expectation balance
-- statement:
--   For every unbounded variation original source Levy law, q>0, 0<=x<=a, every finite horizon, the sum of the completed upper-first and surviving-horizon discounted q-scale rewards is integrable with original-P expectation W(x). Use the exact already-Proved pathwise two-way split of the genuine finite-horizon payoff, and no-mesh UBV finite horizon identity.
-- source:
--   UBV source no-mesh expectation and accepted actual two-way finite-horizon reward pointwise split.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_horizon_killed_reward_two_way_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual UBV completed-upper plus surviving-horizon reward integrates exactly to Wq(x). -/

theorem AvramDividend.Classical.avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
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
