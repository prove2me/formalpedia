-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_mulL2_symmetric
-- name    : BookProof.StrichartzWave.mulL2_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:51:18.515044+00:00
-- url     : https://prove2.me/theorems/1589fb39-8a7a-4fa2-8e74-a4bec8d2aac4
-- title:
--   `BookProof.StrichartzWave.mulL2_symmetric` (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (hW : ∀ᵐ x ∂(volume : Measure V), (starRingEnd ℂ) (W x) = W x) (u w : Lp ℂ 2 (volume : Measure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveBoundedPotential`.
--
--   `BookProof.StrichartzWave.mulL2_symmetric` (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (hW : ∀ᵐ x ∂(volume : Measure V), (starRingEnd ℂ) (W x) = W x) (u w : Lp ℂ 2 (volume : Measure V)) : (inner ℂ (mulL2 W u) w : ℂ) = inner ℂ u (mulL2 W w)
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.mulL2_symmetric`.

-- Generated from ChapterWaveBoundedPotential.lean — theorem BookProof.StrichartzWave.mulL2_symmetric
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.mulL2_symmetric (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
    (hW : ∀ᵐ x ∂(volume : Measure V), (starRingEnd ℂ) (W x) = W x)
    (u w : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (mulL2 W u) w : ℂ) = inner ℂ u (mulL2 W w) := by sorry
