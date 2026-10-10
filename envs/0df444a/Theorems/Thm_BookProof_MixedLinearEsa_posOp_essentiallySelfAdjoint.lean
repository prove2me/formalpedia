-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_posOp_essentiallySelfAdjoint
-- name    : BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:03:40.717976+00:00
-- url     : https://prove2.me/theorems/b0c34607-6464-49c8-8b1c-a5908fff1d91
-- title:
--   `BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint` (b : V) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (posOp b))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint` (b : V) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (posOp b))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint (b : V) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (posOp b)) := by sorry
