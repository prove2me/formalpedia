-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_l2Fourier_norm
-- name    : BookProof.NsSpatialMultiplier.l2Fourier_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:38.563136+00:00
-- url     : https://prove2.me/theorems/aa77d00f-b8ed-4207-84ab-bc535cf41540
-- title:
--   `BookProof.NsSpatialMultiplier.l2Fourier_norm` (v : Lp ℂ 2 (volume : Measure V)) : ‖l2Fourier V v‖ = ‖v‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.l2Fourier_norm` (v : Lp ℂ 2 (volume : Measure V)) : ‖l2Fourier V v‖ = ‖v‖
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.l2Fourier_norm`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.l2Fourier_norm
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in

theorem BookProof.NsSpatialMultiplier.l2Fourier_norm (v : Lp ℂ 2 (volume : Measure V)) : ‖l2Fourier V v‖ = ‖v‖ := by sorry
