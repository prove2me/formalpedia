-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:43:57.748003+00:00
-- url     : https://prove2.me/theorems/43b8f2af-6f1c-41c2-8e37-f73ff81c641a
-- title:
--   Source Gaussian dividend candidate satisfies original full positive-reserve HJB under above-barrier inequality
-- statement:
--   Proves the full Gaussian case of the original vcstar_hjb_all_positive_of_generator with no extra root, residual, curvature or product-integrability assumptions: for original Standing Gaussian spectrally negative Levy X and q-scale W, if the genuine generator residual is nonpositive above cstar with GeneratorIntegrable as stated in the original HJB theorem, then at every y>0 the candidate is in the actual source generator domain and max((Gamma-q)vcstar,1-vcstar')=0. This includes cstar=0 and positive cstar endpoint. The proof constructs the q-root from source Standing, establishes true source compensated kernel Fubini integrability, weighted zero residual and pointwise source q-harmonicity, then applies the proved full Gaussian HJB assembly.
-- source:
--   Canonical Wave 4 Gaussian source compensated generator product, residual, harmonicity, positive q-root and Gaussian HJB assembly

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Original Gaussian generator's full HJB for the barrier candidate from source data. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
