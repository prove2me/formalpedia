-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_fibreOp_apply
-- name    : BookProof.NsPartialFourier.fibreOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:10:40.566652+00:00
-- url     : https://prove2.me/theorems/cdac6029-6dd6-46fb-8c7a-600f77f12d64
-- title:
--   `BookProof.NsPartialFourier.fibreOp_apply` (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) : fibreOp V T f = T.compLp f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.fibreOp_apply` (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) : fibreOp V T f = T.compLp f
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.fibreOp_apply`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.fibreOp_apply
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in

theorem BookProof.NsPartialFourier.fibreOp_apply (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) :
    fibreOp V T f = T.compLp f := by sorry
