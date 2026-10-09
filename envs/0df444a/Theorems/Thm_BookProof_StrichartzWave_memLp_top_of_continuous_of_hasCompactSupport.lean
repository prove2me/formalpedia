-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_memLp_top_of_continuous_of_hasCompactSupport
-- name    : BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T20:36:01.920809+00:00
-- url     : https://prove2.me/theorems/bcec09d8-ffd4-453b-a8c0-3083a7d5f2fb
-- title:
--   `BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport` {W : V → ℝ} (hW : Continuous W) (hWc : HasCompactSupport W) : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport` {W : V → ℝ} (hW : Continuous W) (hWc : HasCompactSupport W) : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.memLp_top_of_continuous_of_hasCompactSupport {W : V → ℝ} (hW : Continuous W)
    (hWc : HasCompactSupport W) :
    MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V) := by sorry
