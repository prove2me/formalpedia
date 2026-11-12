-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_nojump_U_horizon_mask_measurable
-- name    : AvramDividend.Classical.avram_bva22_original_nojump_U_horizon_mask_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:27:59.352724+00:00
-- url     : https://prove2.me/theorems/0b6320eb-663f-42ea-9c47-4575c985f27a
-- title:
--   Original zero-jump prepayment reserve masked to positive finite horizon is measurable
-- statement:
--   The actual original Lévy source obeys X_t=t times drift through S. The Proved exact positive-time identity f0f86efa rewrites its prepayment U left-limit as x+t drift minus the actual right-limit-dividend left-limit. That dividend left limit is jointly measurable by Proved theorem 1816332a, so its time section is measurable. Restricting U to strictly positive times within S and extending by zero yields a measurable function. This is necessary to establish source J measurability for the K integral in 7ccc2a1a without assuming the unrestricted X path is measurable everywhere.
-- source:
--   Physical BV original no-jump source U measurable finite-horizon mask, needed to close 7ccc2a1a K kernel measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_nojump_U_horizon_mask_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hLeft : Measurable (fun t : ℝ≥0 =>
      Function.leftLim (fun r : ℝ≥0 => rightLimit D r ω) t)) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ S then
        Function.leftLim (fun r : ℝ≥0 =>
          x + X.X r ω - rightLimit D r ω) t
      else 0) := by sorry
