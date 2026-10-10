-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_posOp_symmetric
-- name    : BookProof.MixedLinearEsa.posOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:03:12.666789+00:00
-- url     : https://prove2.me/theorems/207ae4c0-d0a7-4984-968d-b9a2f9899b4f
-- title:
--   `BookProof.MixedLinearEsa.posOp_symmetric` (b : V) : SymmetricOn (schwartzDomain V) (opL2 (posOp b))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.posOp_symmetric` (b : V) : SymmetricOn (schwartzDomain V) (opL2 (posOp b))
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.posOp_symmetric`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.posOp_symmetric
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

theorem BookProof.MixedLinearEsa.posOp_symmetric (b : V) :
    SymmetricOn (schwartzDomain V) (opL2 (posOp b)) := by sorry
