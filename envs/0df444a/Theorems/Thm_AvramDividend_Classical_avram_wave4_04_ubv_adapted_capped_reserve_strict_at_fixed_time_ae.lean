-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:32:43.104017+00:00
-- url     : https://prove2.me/theorems/6f35bc03-dcf7-4cce-8358-6160ba421d27
-- title:
--   Actual unbounded-variation Lévy reserve is strictly below a finite cap at almost every fixed surviving capped time
-- statement:
--   For the original unbounded-variation spectrally negative Lévy process X and any adapted nondecreasing left-continuous actual dividend strategy D, a fixed strictly positive deterministic time cannot attain finite cap c if the controlled reserve x+X-D has remained at or below c throughout the preceding interval. This holds almost surely on the same probability space and common filtration, without replacing X by an equal-law copy or imposing generator/HJB assumptions. The fixed-time source strict drawdown is almost sure by genuine Lévy time reversal and zero downward regularity. Since D is increasing, a strictly negative source terminal drawdown makes the controlled reserve strictly below its earlier reserve, hence below c. This is the zero Lebesgue cap occupation route once adapted-prefix measurability and time Fubini are justified; it does not alone prove the cap payment Stieltjes term or stopped Ito-Meyer formula.
-- source:
--   Canonical source SpectrallyNegativeLevy.isProbability and genuine IsDividendStrategy path monotonicity; Proved source fixed-time strict terminal drawdown (Wave 4 Chat04), Proved actual Lévy joint random-horizon strict event measurability UUID 19746984-73d9-4626-8cad-22ff858602dd. Source-faithful cap contact lemma for corrected UBV stochastic verification 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (∀ s : ℝ≥0, s ≤ T → riskProcess X x D s ω ≤ c) →
        riskProcess X x D T ω < c := by sorry
