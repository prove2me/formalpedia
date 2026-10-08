-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_firstOrderOp_symmetric
-- name    : BookProof.FourierMultiplierEsa.firstOrderOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:15.724384+00:00
-- url     : https://prove2.me/theorems/08e2adf5-93c8-4400-ac9f-da17193de708
-- title:
--   `BookProof.FourierMultiplierEsa.firstOrderOp_symmetric` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (firstOrderOp c w))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.firstOrderOp_symmetric` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (firstOrderOp c w))
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.firstOrderOp_symmetric`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.firstOrderOp_symmetric
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

theorem BookProof.FourierMultiplierEsa.firstOrderOp_symmetric (c : ι → ℝ) (w : ι → V) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (firstOrderOp c w)) := by sorry
