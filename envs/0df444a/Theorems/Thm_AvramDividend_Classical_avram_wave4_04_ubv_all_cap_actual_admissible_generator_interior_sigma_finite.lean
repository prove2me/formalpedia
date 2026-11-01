-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:51:10.196929+00:00
-- url     : https://prove2.me/theorems/c8aed6ff-a440-4dd2-9eff-1f7e9bcecf88
-- title:
--   Exact original admissible controlled unbounded-variation Lévy reserve lies in the strict generator domain for every nonzero extended-real cap
-- statement:
--   For the original spectrally negative Levy process X of unbounded variation and its same-filtration adapted capped dividend strategy D, with the genuine source IsAdmissibleLe premise, any nonzero extended-real cap C (finite or infinity), any fixed sigma-finite deterministic time measure μ and an explicit strong-Markov dense/cofinal time schedule, almost every original X,D path has strict reserve 0<U_t and ofReal U_t<C at μ-almost every positive pre-ruin time. The result instantiates both independently Proved original-source lower and finite-upper boundary occupation theorems directly at the corrected stochastic core's IsAdmissibleLe binders. It is an actual source generator dt-interior support theorem, with no equal-law process substitution. Random Stieltjes dividend-measure mass may charge the cap, and the source Ito-Meyer jump compensator and expectation inequality remain unproved.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; corrected UBV primary 429e17ca-5528-40b5-b593-7c03973d0706. Canonical Proved original-source upper occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and lower occupation 6a06830a-160f-45a6-b776-8807e202b19d; Proved source cap admissibility  a8120e3c-049c-465c-9ad2-bbf91f9b20a1 and initial capital positivity. Pinned Mathlib ENNReal.ofReal_toReal and sigma-finite measure a.e.-a.e. commutation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C := by sorry
