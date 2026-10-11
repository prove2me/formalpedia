-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_add_truncatedPotential_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:30.24406+00:00
-- url     : https://prove2.me/theorems/95548919-b746-44e1-af68-d246cec1907e
-- title:
--   `BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) (R : ℝ) : ∃ WR : SpaceTime n → ℝ, F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) (R : ℝ) : ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧ (∀ x, ‖x‖ ≤ R → WR x = W x) ∧ (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧ BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n 0 + potentialOp WR))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = W x) ∧ (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) := by sorry
