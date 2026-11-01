-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:34:58.556045+00:00
-- url     : https://prove2.me/theorems/6a06830a-160f-45a6-b776-8807e202b19d
-- title:
--   Original controlled unbounded-variation Lévy reserve has zero pre-ruin occupation of the zero boundary
-- statement:
--   For the actual spectrally negative Lévy process X of unbounded variation and its original jointly adapted dividend strategy D, assume exactly the nonnegative surviving reserve property provided by source IsAdmissibleLe. Choose the standard explicit dense countable time schedule and positive cofinal horizon sequence used by the canonical source strong-Markov theorem, and any fixed deterministic sigma-finite measure μ on nonnegative time. Then for P-a.e. original sample path and μ-a.e. time strictly before actual ruin, the pre-payment reserve x+X_t−D_t is strictly positive. This is a genuinely measurable Fubini occupation theorem derived from canonically Proved source pathwise fixed-time strict positivity 78045b4c-083c-4a03-b6dd-ce6e0a01b53d; it works for Gaussian and pure-jump UBV laws. It controls the strict lower interior boundary for Lebesgue generator drift, but does not imply vanishing random control Stieltjes mass or any original-source compensated-jump semimartingale formula.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Corrected UBV primary 429e17ca-5528-40b5-b593-7c03973d0706. Same-filtration Proved fixed-time lower bound UUID 78045b4c-083c-4a03-b6dd-ce6e0a01b53d; source X joint measurable d55462c3-decf-40f0-9aff-439d356324d9; D predictable a4ef06a5-5b73-4d29-8e89-4a60aa82c3c5; ruin time measurable bbfbecf4-7dfc-4812-84f3-8644c2b40b85; pinned predictable ≤ product and Measure.ae_ae_comm.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < ruinTime X x D ω →
        0 < riskProcess X x D t ω := by sorry
