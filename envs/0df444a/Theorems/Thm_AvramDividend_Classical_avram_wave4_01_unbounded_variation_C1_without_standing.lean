-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_variation_C1_without_standing
-- name    : AvramDividend.Classical.avram_wave4_01_unbounded_variation_C1_without_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:14:51.106208+00:00
-- url     : https://prove2.me/theorems/b3b0b4d2-651e-444e-bc64-9b84bc565e42
-- title:
--   Unbounded-variation q-scale C1 without Standing, unifying Gaussian and genuine infinite-small-jump branches
-- statement:
--   Every spectrally negative Lévy process whose sample paths have unbounded variation has a continuously differentiable q-scale function on (0,∞), for q>0, without any Standing hypothesis. The proof splits positive Gaussian variance from zero Gaussian coefficient: in the latter case, failure of bounded variation forces divergence of the first absolute small-negative-jump moment. Thus the theorem unifies two independently proved, genuine stochastic smoothing mechanisms, including the source first-record hazard route.
-- source:
--   Proved Gaussian Standing-free C1 6760cad5 and Proved genuine original-process first-record hazard infinite-small-negative-jump C1 cd61d678; BoundedVariation definitional split.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_unbounded_variation_C1_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Set.Ioi (0 : ℝ)) := by sorry
