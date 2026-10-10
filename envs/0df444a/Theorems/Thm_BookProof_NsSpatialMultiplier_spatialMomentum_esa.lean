-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_spatialMomentum_esa
-- name    : BookProof.NsSpatialMultiplier.spatialMomentum_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:40.062981+00:00
-- url     : https://prove2.me/theorems/4ba9beeb-d110-4e2c-bc7a-4c2ddd1c9538
-- title:
--   `BookProof.NsSpatialMultiplier.spatialMomentum_esa` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (firstOrderOp c w))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.spatialMomentum_esa` (c : ι → ℝ) (w : ι → V) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (firstOrderOp c w))
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.spatialMomentum_esa`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.spatialMomentum_esa
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

theorem BookProof.NsSpatialMultiplier.spatialMomentum_esa (c : ι → ℝ) (w : ι → V) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (firstOrderOp c w)) := by sorry
