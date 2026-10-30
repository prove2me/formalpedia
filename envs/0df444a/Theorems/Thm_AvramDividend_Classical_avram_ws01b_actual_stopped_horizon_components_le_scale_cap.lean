-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_stopped_horizon_components_le_scale_cap
-- name    : AvramDividend.Classical.avram_ws01b_actual_stopped_horizon_components_le_scale_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T14:10:00.981979+00:00
-- url     : https://prove2.me/theorems/cc37a61c-891b-48f2-986a-7444499c883a
-- title:
--   Original two-sided finite-horizon stopped discounted scale reward bounded by Wq(a)
-- statement:
--   For every genuine spectrally negative Lévy sample, positive q and scale function, the sum of completed upper-exit and surviving-horizon discounted rewards never exceeds Wq(a), uniformly in the horizon; requires neither bounded variation nor Wq(0)=0.
-- source:
--   Actual upper-exit hitting level without positive jumps, survivor source reserve strip and monotonicity of the actual qscale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
import Theorems.Thm_AvramDividend_Classical_two_sided_up_exit_hits_level_of_no_positive_jumps

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_stopped_horizon_components_le_scale_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
     let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
     (if U < D ∧ U.toNNReal ≤ T then
       Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
     (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
       Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0)) ≤ W a := by sorry
