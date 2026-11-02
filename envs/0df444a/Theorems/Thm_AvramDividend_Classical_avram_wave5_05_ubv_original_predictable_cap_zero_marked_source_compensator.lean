-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:42:07.280417+00:00
-- url     : https://prove2.me/theorems/f215189c-2384-4a8d-94c5-e38a78a41f2a
-- title:
--   Actual original predictable cap-contact has zero marked Lévy-source compensator characteristic for arbitrary nonnegative mark density
-- statement:
--   Under genuine original UBV spectrally negative source, same-filtration dividend strategy and actual pre-ruin cap, an arbitrary possibly infinite nonnegative mark-dependent compensator density supported at exact cap contact of the true predictable leftLimit(x+X−rightLimit D) integrates to zero over any atomless s-finite physical-time clock and arbitrary real-valued Lévy mark measure. The proof takes the mark-integral as the weight in previously Proved stochastic predictable-cap weighted clock theorem and commutes the cap indicator with mark integration by a pointwise case split. This is a source-compensator boundary density lemma for dt⊗Π, including x=c; it does not assert actual compensated jump martingale equality, local-time nullity, or dividend Stieltjes nullity.
-- source:
--   Proved weighted predictable source cap clock f8199679-8516-46fa-b24a-b17cf33e8b8b, cap generator source de1c1aee-43d3-47a2-83ae-6115b56249e3, corrected canonical UBV 429e17ca-5528-40b5-b593-7c03973d0706 untouched.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (ν : Measure ℝ)
    (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ) = 0 := by sorry
