-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
-- name    : AvramDividend.Classical.avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:54:31.715323+00:00
-- url     : https://prove2.me/theorems/d2214670-28f5-42cd-88e6-31184ca5c681
-- title:
--   Genuine Lévy generator integrability of vcstar on the whole interior under all three original smoothness branches
-- statement:
--   Under the verbatim original generator_vcstar_eq_zero assumptions, including Standing, q>0, IsScaleFunction W, cstar>0 and Gaussian∨bounded-variation∨C2 on the interior, the true original compensated Lévy generator of vcstar is in its integrability domain for every reserve x strictly between zero and cstar. This closes the integrability conjunct of the original open source generator theorem independently of P2's still-missing pure-jump pointwise harmonicity identity. It uses the canonically Proved source scale-function generator-domain theorem for all three branches, nonzero barrier scale normaliser, constant-scalar preservation of source jump integrability, the exact divE scalar identity and source interior candidate-scaled-W generator-domain equivalence.
-- source:
--   Original source generator_vcstar_eq_zero, canonical 44b032f3, 17ab0fe2, f464799e, 680b65bf

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_standing_nonzero_scale_normaliser
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_integrable_of_nonzero_factor
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_congr_scaledW_inside_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x := by sorry
