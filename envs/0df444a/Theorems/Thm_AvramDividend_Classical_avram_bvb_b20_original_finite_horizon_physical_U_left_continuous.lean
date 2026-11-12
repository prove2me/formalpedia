-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
-- name    : AvramDividend.Classical.avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:08:36.245022+00:00
-- url     : https://prove2.me/theorems/d50e649e-158f-4c3c-a2db-e2d48323055e
-- title:
--   Original finite-horizon physical prepayment reserve is left-continuous on positive time
-- statement:
--   On the original physical no-source-jump event up to S, the actual prepayment reserve left limit used by the stopped marked compensator is left-continuous on positive times, retaining the exact original X and right-limit dividend process.
-- source:
--   Source-exact BV-B20 quadrature prerequisite; uses original finite-horizon phys126 and original dividend-path monotonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift) :
    ContinuousWithinAt
      (fun r : ℝ≥0 => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r)
      (Ioc 0 t) t := by sorry
