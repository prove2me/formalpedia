-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_momentumOp_essentiallySelfAdjoint
-- name    : BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:37.236282+00:00
-- url     : https://prove2.me/theorems/ce8cff7c-6a60-4e99-8805-424947bec65f
-- title:
--   `BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint` (m : V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (momentumOp m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint` (m : V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (momentumOp m))
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint (m : V) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (momentumOp m)) := by sorry
