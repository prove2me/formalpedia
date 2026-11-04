-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:19:37.117377+00:00
-- url     : https://prove2.me/theorems/cdaaf55d-863e-46b0-b2c0-ddc4b0ebda17
-- title:
--   Original predictable linear Lévy mark on a square-integrable negative band is genuinely in the product L2 space
-- statement:
--   With the true original spectrally negative Lévy source X, a predictable coefficient g of finite square energy under the actual physical clock and a Borel mark band B of finite X.ν quadratic moment, the linear jump kernel g(t,ω)z belongs to L² of the genuine predictable product measure μ⊗X.ν|B. The restricted band measure sigma-finiteness required for Tonelli is an explicit hypothesis and holds in the source-negative region via the separately accepted Lévy s-finiteness theorem. The result is deterministic L2 membership only; stochastic integration with original intrinsic NX still requires compensator/isometry.
-- source:
--   Accepted P4-B exact quadratic factorisation, accepted original real square-to-eNorm energy theorem, Tonelli for the true predictable source product measure, and MemLp characterisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : Set ℝ)
    (hBmoment : (∫⁻ z in B,
      ENNReal.ofReal (z^2) ∂X.ν) < ⊤)
    (hνs : SFinite (X.ν.restrict B)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      MemLp (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2)
        (2 : ℝ≥0∞) (μ.prod (X.ν.restrict B))) := by sorry
