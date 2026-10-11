-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_mulL2_coeFn
-- name    : BookProof.StrichartzWave.mulL2_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:51:23.314989+00:00
-- url     : https://prove2.me/theorems/64f07081-9b3e-40a7-bf0e-dd55594e8106
-- title:
--   `BookProof.StrichartzWave.mulL2_coeFn` (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (u : Lp ℂ 2 (volume : Measure V)) : (mulL2 W u : V → ℂ) =ᵐ[(volume : Measure V)] fun x => (W x) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveBoundedPotential`.
--
--   `BookProof.StrichartzWave.mulL2_coeFn` (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (u : Lp ℂ 2 (volume : Measure V)) : (mulL2 W u : V → ℂ) =ᵐ[(volume : Measure V)] fun x => (W x) * (u x)
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.mulL2_coeFn`.

-- Generated from ChapterWaveBoundedPotential.lean — theorem BookProof.StrichartzWave.mulL2_coeFn
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.mulL2_coeFn (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
    (u : Lp ℂ 2 (volume : Measure V)) :
    (mulL2 W u : V → ℂ) =ᵐ[(volume : Measure V)] fun x => (W x) * (u x) := by sorry
