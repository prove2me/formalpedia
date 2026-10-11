-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_add_boundedPotential_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:18:57.205303+00:00
-- url     : https://prove2.me/theorems/85dd8070-cc01-439a-9a56-981e76736b33
-- title:
--   `BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint` (n : ℕ) (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) (hW : ∀ᵐ x ∂(volume : Measure (SpaceTime
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveBoundedPotential`.
--
--   `BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint` (n : ℕ) (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) (hW : ∀ᵐ x ∂(volume : Measure (SpaceTime n)), (starRingEnd ℂ) (W x) = W x) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n 0) + ((mulL2 W).toLinearMap ∘ₗ (schwartzDomain (SpaceTime n)).subtype))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint`.

-- Generated from ChapterWaveBoundedPotential.lean — theorem BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.wave_add_boundedPotential_essentiallySelfAdjoint (n : ℕ)
    (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n)))
    (hW : ∀ᵐ x ∂(volume : Measure (SpaceTime n)), (starRingEnd ℂ) (W x) = W x) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0) +
        ((mulL2 W).toLinearMap ∘ₗ (schwartzDomain (SpaceTime n)).subtype)) := by sorry
