-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_hasTemperateGrowth_symbolFn
-- name    : BookProof.StrichartzWave.hasTemperateGrowth_symbolFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:16.889454+00:00
-- url     : https://prove2.me/theorems/d7a003ff-de3f-47d3-b74d-75cadfae2d99
-- title:
--   `BookProof.StrichartzWave.hasTemperateGrowth_symbolFn` (c : ι → ℝ) (w : ι → V) (κ : ℝ) : Function.HasTemperateGrowth (symbolFn c w κ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.hasTemperateGrowth_symbolFn` (c : ι → ℝ) (w : ι → V) (κ : ℝ) : Function.HasTemperateGrowth (symbolFn c w κ)
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.hasTemperateGrowth_symbolFn`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.hasTemperateGrowth_symbolFn
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.StrichartzWave.hasTemperateGrowth_symbolFn (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    Function.HasTemperateGrowth (symbolFn c w κ) := by sorry
