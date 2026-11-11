-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin30_original_compact_kernel_product_integrable
-- name    : AvramDividend.Classical.avram_mix_fin30_original_compact_kernel_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:49:21.766375+00:00
-- url     : https://prove2.me/theorems/83ad34a3-34f3-4807-b10a-33a239a920c4
-- title:
--   Compact original mixed negative-jump generator kernel is L1 under finite activity
-- statement:
--   For the original spectrally negative Levy source and positive finite-cap HJB reward, a predictable-base-space reserve state Y in a compact positive strip has a uniformly bounded negative-mark generator kernel. Its source-defined kernel on time-state × marks, set to zero for nonnegative marks, is integrable against the finite predictable reference measure times the original negative-jump Levy intensity. The proof uses the Proved original uniform compensated kernel estimate 86bc48a7 and the new Proved product bounded-kernel integrability theorem b811413f, with only finite negative-jump activity. This supplies exactly hGiN for the Proved original stopped-source compensated martingale f445799e once measurability of the actual marked prepayment reserve is established.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compact_compensated_kernel_uniform
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin29_finite_product_bounded_kernel_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin30_original_compact_kernel_product_integrable
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q u v : ℝ) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C)
    (hσ : X.σ ≠ 0)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (μ : Measure α) (hμfinite : μ Set.univ < ⊤)
    (Y : α → ℝ) (hY : ∀ a, Y a ∈ Ico u v)
    (G : α × ℝ → ℝ)
    (hG : ∀ p, G p =
      if p.2 < 0 then SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2
      else 0)
    (hGmeas : AEStronglyMeasurable G
      (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
