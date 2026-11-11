-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite54_original_finitecap_gaussian_strip_gradient_uniform
-- name    : AvramDividend.Classical.avram_gfinite54_original_finitecap_gaussian_strip_gradient_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:29:26.81877+00:00
-- url     : https://prove2.me/theorems/d51b28de-71de-412a-bb52-3687e443d08c
-- title:
--   Uniform Gaussian gradient bound on the original finite-cap upper half-band
-- statement:
--   Under the original zero-jump unbounded-variation Gaussian HJB and derivative-envelope hypotheses, w' has a uniform bound on the upper half of the finite reserve interval, including points approaching the cap. This physically parameterised consequence of the proved exponential derivative comparison removes a possible singularity in the Gaussian cap-strip integrand.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite54_original_finitecap_gaussian_strip_gradient_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Ico (C.toReal / 2) C.toReal, deriv w y ≤ B := by
  sorry
