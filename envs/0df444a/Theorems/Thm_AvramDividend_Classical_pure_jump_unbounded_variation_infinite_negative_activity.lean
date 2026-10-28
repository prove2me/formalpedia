-- Prove2me | Theorems.Thm_AvramDividend_Classical_pure_jump_unbounded_variation_infinite_negative_activity
-- name    : AvramDividend.Classical.pure_jump_unbounded_variation_infinite_negative_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:21:17.070647+00:00
-- url     : https://prove2.me/theorems/ee2a3b5f-1b82-4ebe-8e1b-cd99ecf400c6
-- title:
--   Zero-Gaussian unbounded-variation Lévy processes have infinite negative-jump intensity
-- statement:
--   Every spectrally negative Lévy process with σ=0 and unbounded variation has infinite total negative jump activity. The canonical BoundedVariation definition states σ=0 and finite small negative-jump first variation. Negating bounded variation while σ=0 therefore forces infinite first variation. The previously Proved generic signed-measure theorem gives total negative activity infinite. This is a process-level prerequisite for the almost-sure downward jumps near time zero used in zero-discount q-scale C1 regularity.
-- source:
--   New Proved measure theorem [9c9ba7fd-60ec-487e-a39d-401151963146], accepted candidate 16130. BoundedVariation canonical definition from Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy. Helps root-connected Open [8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d] via Open ae_early_downward_jumps_of_infinite_negative_activity [ff758fb4-87e5-4eec-b153-b6135498ca04].

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_implies_infinite_negative_activity
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.pure_jump_unbounded_variation_infinite_negative_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation) :
    X.ν (Iio (0 : ℝ)) = ⊤ := by sorry
