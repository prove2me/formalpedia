-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_essentiallySelfAdjoint
-- name    : BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:06:34.036501+00:00
-- url     : https://prove2.me/theorems/d2202605-7fc7-48e3-9fbe-6d238ea3a470
-- title:
--   `BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint` (b m : V) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedLinearOp b m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint` (b m : V) : EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedLinearOp b m))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint
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

theorem BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint (b m : V) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedLinearOp b m)) := by sorry
