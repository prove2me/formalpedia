-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_mixedOp_symmetric
-- name    : BookProof.FourierMultiplierEsa.mixedOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:07.032226+00:00
-- url     : https://prove2.me/theorems/0fea3c34-5ea6-443a-a5ee-f89862f37342
-- title:
--   `BookProof.FourierMultiplierEsa.mixedOp_symmetric` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (mixedOp a c w κ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.mixedOp_symmetric` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (mixedOp a c w κ))
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.mixedOp_symmetric`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.mixedOp_symmetric
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

theorem BookProof.FourierMultiplierEsa.mixedOp_symmetric (a c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (mixedOp a c w κ)) := by sorry
