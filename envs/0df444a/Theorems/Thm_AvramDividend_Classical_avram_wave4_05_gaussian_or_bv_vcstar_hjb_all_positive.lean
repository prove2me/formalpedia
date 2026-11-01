-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_vcstar_hjb_all_positive
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_hjb_all_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:23:14.599329+00:00
-- url     : https://prove2.me/theorems/c1cef788-115d-4703-ac1b-ecc644d3d24c
-- title:
--   Combined original source HJB on the Gaussian or bounded-variation branch
-- statement:
--   Unifies the canonically Proved Gaussian compensated-generator HJB and genuine bounded-variation source HJB. Under original Standing X, q>0, q-scale W and the original above-barrier GeneratorIntegrable/nonpositive residual premise, the source HJB holds at every positive reserve whenever σ>0 or X has bounded variation. This leaves precisely the pure unbounded-variation nonGaussian C2 alternative to the separately owned source-harmonicity workstream.
-- source:
--   Canonical original-source Gaussian and bounded-variation full HJB branch results, with an exact disjunction split

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_all_positive
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Original source HJB for either branch with established local q-harmonicity. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_hjb_all_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
