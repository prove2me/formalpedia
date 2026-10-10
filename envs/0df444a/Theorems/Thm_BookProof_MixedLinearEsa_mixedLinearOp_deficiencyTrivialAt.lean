-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_deficiencyTrivialAt
-- name    : BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:06:13.917919+00:00
-- url     : https://prove2.me/theorems/697266c2-60e5-4924-8bb2-891d1ca01534
-- title:
--   `BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt` (b m : V) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (schwartzDomain V) (opL2 (mixedLinearOp b m)) z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt` (b m : V) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (schwartzDomain V) (opL2 (mixedLinearOp b m)) z
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt
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

theorem BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt (b m : V) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (mixedLinearOp b m)) z := by sorry
