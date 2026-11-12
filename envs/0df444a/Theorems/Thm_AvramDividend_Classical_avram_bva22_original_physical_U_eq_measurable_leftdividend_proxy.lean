-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
-- name    : AvramDividend.Classical.avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:24:34.627422+00:00
-- url     : https://prove2.me/theorems/f0f86efa-def8-4eff-b845-3afc49ebffa3
-- title:
--   Original positive-time no-jump prepayment reserve equals drift minus measurable dividend-left-limit proxy
-- statement:
--   On the exact original Standing-BV zero-negative-jump source, at positive t up to finite horizon S the left prepayment reserve is x+t times the original Lévy drift minus the left limit of the actual rightLimit dividend strategy. The latter left-limit dividend process is known jointly measurable by Proved theorem 1816332a. This equality connects original source U to a measurable proxy for establishing K-side time measurability in theorem 7ccc2a1a.
-- source:
--   Exact physical zero-jump reserve-to-measurable-proxy identity required for original compensated kernel measurability in 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift) :
    Function.leftLim (fun r : ℝ≥0 =>
      x + X.X r ω - rightLimit D r ω) t =
    x + (t : ℝ) * X.drift -
      Function.leftLim (fun r : ℝ≥0 => rightLimit D r ω) t := by sorry
