-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_triplet_bv
-- name    : AvramDividend.Classical.avram_a06_uniform_triplet_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:29:01.049675+00:00
-- url     : https://prove2.me/theorems/e3e85c0a-ab63-402b-aa7a-14634b08c132
-- title:
--   An Avram Lévy process with zero Gaussian variance and compact negative jump law has bounded variation
-- statement:
--   For an original SpectrallyNegativeLevy with zero Gaussian coefficient and Lévy measure uniform on (-1,0), prove its exact BoundedVariation predicate, using the accepted small-jump absolute-moment bound.
-- source:
--   Extracted source definition BoundedVariation : σ = 0 ∧ ∫ in (-1,0) |y| dν < ∞; the necessary integral was Proved as 51e4a4b3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_triplet_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (L : SpectrallyNegativeLevy P 𝓕)
    (hσ : L.σ = 0)
    (hν : L.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) :
    L.BoundedVariation := by sorry
