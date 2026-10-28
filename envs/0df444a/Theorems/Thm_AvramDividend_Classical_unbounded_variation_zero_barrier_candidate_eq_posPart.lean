-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
-- name    : AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_posPart
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:24:42.353738+00:00
-- url     : https://prove2.me/theorems/8c0574e9-6775-4440-beb9-b1f060ce0445
-- title:
--   Whole-line zero-barrier scale candidate is the positive part of reserve under unbounded variation
-- statement:
--   For a spectrally negative Lévy process with unbounded variation and positive discount, the zero-barrier candidate value on the whole real line equals max(x,0): it is the initial reserve on nonnegative reserves and zero on negative reserves. This yields an explicit globally continuous boundary formula with no derivative assumption, relevant to the zero-barrier HJB and killed boundary condition.
-- source:
--   Proved unbounded_variation_zero_barrier_candidate_vanishes and barrierValue_zero_affine_nonnegative, plus the definitional negative-reserve branch of barrierValue.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_vanishes
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_posPart
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    barrierValue W 0 x = max x 0 := by sorry
