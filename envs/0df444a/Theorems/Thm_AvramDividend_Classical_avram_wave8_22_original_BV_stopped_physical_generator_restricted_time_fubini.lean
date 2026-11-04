-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:06:34.174525+00:00
-- url     : https://prove2.me/theorems/0c8bc99e-f099-427e-a089-11071282761b
-- title:
--   Actual original BV stopped physical generator restricted-time random integral is L1 and its mean is the genuine source product integral
-- statement:
--   For unchanged original Levy process and dividend strategy, its actual signed BV generator drift with negative Levy kernel and discount on the stopped original random time set A has a Bochner integrable random time integral and its expectation equals the genuine original clock product integral whenever the source predictable product integrand is integrable. Measurable time slices, the original clock identity and the physical generator expression are explicit. Mathlib integral_indicator and Fubini discharge the expectation bridge.
-- source:
--   Pinned Mathlib integral_indicator, Integrable.integral_prod_right, integral_prod_symm; original BV physical drift formula and X.ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (hFI : Integrable F (μT.prod P)) :
  Integrable (fun ω => ∫ t in A ω, K t ω ∂μT) P ∧
    (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) =
      (∫ p, F p ∂(μT.prod P)) := by sorry
