-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:31:42.639302+00:00
-- url     : https://prove2.me/theorems/2f3d862d-8700-4df1-9bac-380f8760150d
-- title:
--   Original Gaussian left-grid survival mask remains predictable through the genuine final sampled cell
-- statement:
--   Original same-source physical Gaussian C2 ledger interface for a338c453-58c0-411c-aaca-5cec689ed807 and 249c532d-4ec0-498c-81f0-b380dd476344. Given a true sampled-filtration stopping index K on the original right-continuous physical grid, the strict survival event i<K is measurable at the original left endpoint e(i). Original prepayment gradient and Hessian coefficients, measurable at this left endpoint, stay measurable after multiplying by the survival indicator. This includes the randomly included final Gaussian cell and never assumes floor of an arbitrary clock is stopping. Combined with Proved 4a4b4e27 and 48b4b851, it supplies exact conditional source centring for each finite original physical mesh.

import Mathlib.Probability.Process.Stopping
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)))
    (G H : ℕ → Ω → ℝ)
    (hG : ∀ i, Measurable[𝓕.rightCont (e i)] (G i))
    (hH : ∀ i, Measurable[𝓕.rightCont (e i)] (H i)) :
    ∀ i,
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then G i ω else 0) ∧
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then H i ω else 0) := by
  sorry
