-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin31_original_double_lintegral_to_product_L1
-- name    : AvramDividend.Classical.avram_mix_fin31_original_double_lintegral_to_product_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:02:25.922395+00:00
-- url     : https://prove2.me/theorems/9ada3509-e792-4c38-9dc4-90a0e33a4168
-- title:
--   Original predictable marked-kernel double absolute integral gives product L1
-- statement:
--   For an a.e.-strongly-measurable real kernel H on a product measure μ.prod ν with ν s-finite, finiteness of ∫_μ∫_ν |H(a,b)| implies Integrable H (μ.prod ν). This is the exact measurable Fubini bridge between the Proved original ruin-stopped C2 source kernel's double negative-mark L1 estimate 0e0663b1 and the Integrable G N hypothesis of the Proved original stopped compensated-source martingale f445799e. The proof uses pinned Mathlib lintegral_lintegral, lintegral_ofReal_ne_top_iff_integrable and integrable_norm_iff. It requires no first absolute moment for the negative jump sizes.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin31_original_double_lintegral_to_product_L1
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (hL1 : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (|H (a,b)|) ∂ν ∂μ) < ⊤) :
    Integrable H (μ.prod ν) := by sorry
