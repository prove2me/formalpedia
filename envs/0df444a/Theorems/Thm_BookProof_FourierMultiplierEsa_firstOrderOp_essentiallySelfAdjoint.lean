-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_firstOrderOp_essentiallySelfAdjoint
-- name    : BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:31.918919+00:00
-- url     : https://prove2.me/theorems/2b6905b8-cac7-4f05-871d-eb7c38d741eb
-- title:
--   `BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (firstOrderOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (firstOrderOp c w))
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint
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

theorem BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint (c : ι → ℝ) (w : ι → V) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (firstOrderOp c w)) := by sorry
