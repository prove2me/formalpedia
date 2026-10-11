-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_add_potential_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:00.791468+00:00
-- url     : https://prove2.me/theorems/19441e12-921a-48ab-a12b-8ba1535e5190
-- title:
--   `BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) : B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveBoundedPotential`.
--
--   `BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n 0) + ((mulL2 (hW.toLp _)).toLinearMap ∘ₗ (schwartzDomain (SpaceTime n)).subtype))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint`.

-- Generated from ChapterWaveBoundedPotential.lean — theorem BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0) +
        ((mulL2 (hW.toLp _)).toLinearMap ∘ₗ (schwartzDomain (SpaceTime n)).subtype)) := by sorry
