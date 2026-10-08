-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_mixedOp_essentiallySelfAdjoint
-- name    : BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:14.172537+00:00
-- url     : https://prove2.me/theorems/d0c2be63-c080-4cf6-9502-a97cb0c1aa6d
-- title:
--   `BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedOp a c w κ))
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint
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

theorem BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint (a c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (mixedOp a c w κ)) := by sorry
