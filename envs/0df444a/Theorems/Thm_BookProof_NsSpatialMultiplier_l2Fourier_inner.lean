-- Prove2me | Theorems.Thm_BookProof_NsSpatialMultiplier_l2Fourier_inner
-- name    : BookProof.NsSpatialMultiplier.l2Fourier_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:46.899987+00:00
-- url     : https://prove2.me/theorems/ee29c76f-12a4-4335-83eb-bfed3e01b367
-- title:
--   `BookProof.NsSpatialMultiplier.l2Fourier_inner` (v u : Lp ℂ 2 (volume : Measure V)) : (inner ℂ (l2Fourier V v) (l2Fourier V u) : ℂ) = inner ℂ v u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsSpatialMomentumMultiplier`.
--
--   `BookProof.NsSpatialMultiplier.l2Fourier_inner` (v u : Lp ℂ 2 (volume : Measure V)) : (inner ℂ (l2Fourier V v) (l2Fourier V u) : ℂ) = inner ℂ v u
--
--   Formalization note: Lean 4 identifier `BookProof.NsSpatialMultiplier.l2Fourier_inner`.

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.l2Fourier_inner
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

theorem BookProof.NsSpatialMultiplier.l2Fourier_inner (v u : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (l2Fourier V v) (l2Fourier V u) : ℂ) = inner ℂ v u := by sorry
