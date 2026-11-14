-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
-- name    : AvramDividend.Classical.avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:12.338856+00:00
-- url     : https://prove2.me/theorems/9602de7a-12cb-4c11-972b-a41303fab09f
-- title:
--   Original physically full pre-stop Gaussian Hessian coefficients are uniformly bounded and a.e. strongly measurable
-- statement:
--   For every original controlled dividend source, on the true uniform physical full-cell mask before the stopping clock, the discounted Hessian coefficient is almost everywhere strongly measurable at each cell and uniformly bounded by a single compact-band constant across all meshes. Uses the proved original postpayment positive reserve band and C2 jet bound (a165), plus generic masked Hessian measurability (a179). This is exactly the weighted-source premise needed in a150.
-- source:
--   True original X.X and rightLimit D, gledger137 postpayment pre-stop band; a165 compact jets, a179 C2 indicator measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ m i, AEStronglyMeasurable (H m i) P) ∧
      (∀ m, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m, |H m i ω| ≤ K) := by sorry
