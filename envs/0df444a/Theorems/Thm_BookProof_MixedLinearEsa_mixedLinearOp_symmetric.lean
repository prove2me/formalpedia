-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_symmetric
-- name    : BookProof.MixedLinearEsa.mixedLinearOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:05:45.202007+00:00
-- url     : https://prove2.me/theorems/11eed265-6d3c-4669-9c2a-42abaf40a4a5
-- title:
--   `BookProof.MixedLinearEsa.mixedLinearOp_symmetric` (b m : V) : SymmetricOn (schwartzDomain V) (opL2 (mixedLinearOp b m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.mixedLinearOp_symmetric` (b m : V) : SymmetricOn (schwartzDomain V) (opL2 (mixedLinearOp b m))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.mixedLinearOp_symmetric`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_symmetric
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.mixedLinearOp_symmetric (b m : V) :
    SymmetricOn (schwartzDomain V) (opL2 (mixedLinearOp b m)) := by sorry
