-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:07:32.499801+00:00
-- url     : https://prove2.me/theorems/51c7ab38-4295-458a-b686-6b270e8ac5f8
-- title:
--   Genuine controlled UBV cap contact has zero integral for every nonnegative arbitrary weight and fixed s-finite time clock, even infinite weights
-- statement:
--   For the original same-filtration unbounded-variation spectrally negative Levy source X and genuine nondecreasing dividend strategy D constrained below a cap up to ruin, the positive-time cap-contact set is null under each fixed s-finite time clock on almost every original trajectory. Consequently, integration of any nonnegative (possibly infinite and not globally bounded) state/time dependent density weight supported on such cap contacts is exactly zero. The result may be used for physical-time Gaussian bracket and compensated Levy jump intensity densities at the cap, but never for random path-dependent cap reflection local time or dividend Stieltjes clock. The theorem includes t=0 and x=c as admissible inputs but explicitly restricts this physical-time integral to t>0 so atoms at initial time are excluded.
-- source:
--   Source-faithful Proved cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3; stochastic/generator cap boundary of Avram corrected canonical 429e17ca-5528-40b5-b593-7c03973d0706; no core modification or milestone changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ]
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            riskProcess X x D t ω = c
        then weight t ω else 0 ∂μ) = 0 := by sorry
