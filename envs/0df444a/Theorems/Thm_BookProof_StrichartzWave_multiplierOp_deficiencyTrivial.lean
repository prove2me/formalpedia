-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_multiplierOp_deficiencyTrivial
-- name    : BookProof.StrichartzWave.multiplierOp_deficiencyTrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:22.626216+00:00
-- url     : https://prove2.me/theorems/4c98dd74-c847-4c8d-b44c-3bdc62546e0f
-- title:
--   `BookProof.StrichartzWave.multiplierOp_deficiencyTrivial` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) {z : ℂ} (hz : z.im ≠ 0) : BookProof.FarisLavine.DeficiencyTrivialAt (schw
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.multiplierOp_deficiencyTrivial` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) {z : ℂ} (hz : z.im ≠ 0) : BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (multiplierOp m)) z
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.multiplierOp_deficiencyTrivial`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.multiplierOp_deficiencyTrivial
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.multiplierOp_deficiencyTrivial (m : V → ℝ) (hm : Function.HasTemperateGrowth m)
    {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (multiplierOp m)) z := by sorry
