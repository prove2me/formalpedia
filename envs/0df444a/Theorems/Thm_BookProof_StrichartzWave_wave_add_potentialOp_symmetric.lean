-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_add_potentialOp_symmetric
-- name    : BookProof.StrichartzWave.wave_add_potentialOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:15.927065+00:00
-- url     : https://prove2.me/theorems/ec107139-9165-4768-92d2-558d63845639
-- title:
--   `BookProof.StrichartzWave.wave_add_potentialOp_symmetric` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.SymmetricOn (schwartzDomain (Sp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.wave_add_potentialOp_symmetric` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.SymmetricOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n 0 + potentialOp W))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.wave_add_potentialOp_symmetric`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.wave_add_potentialOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.wave_add_potentialOp_symmetric (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0 + potentialOp W)) := by sorry
