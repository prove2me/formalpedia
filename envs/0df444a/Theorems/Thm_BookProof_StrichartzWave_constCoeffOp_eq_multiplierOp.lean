-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_eq_multiplierOp
-- name    : BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:52.592762+00:00
-- url     : https://prove2.me/theorems/6079fdcb-8f69-4b73-a18d-897394bba4bd
-- title:
--   `BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp` (c : ι → ℝ) (w : ι → V) (κ : ℝ) : constCoeffOp c w κ = multiplierOp (symbolFn c w κ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp` (c : ι → ℝ) (w : ι → V) (κ : ℝ) : constCoeffOp c w κ = multiplierOp (symbolFn c w κ)
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    constCoeffOp c w κ = multiplierOp (symbolFn c w κ) := by sorry
