-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_polyharmonic_multiplier_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:22.683773+00:00
-- url     : https://prove2.me/theorems/5bdc28a5-705a-4557-a7a8-7ee0e9f4cf58
-- title:
--   `BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint` (k : ℕ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (multiplierOp (fun ξ : V
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint` (k : ℕ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (multiplierOp (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k)))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint (k : ℕ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (multiplierOp (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k))) := by sorry
