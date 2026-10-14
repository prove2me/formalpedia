-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_postcompCLM_vecMomentumOp
-- name    : BookProof.NsPartialFourier.postcompCLM_vecMomentumOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:26.682652+00:00
-- url     : https://prove2.me/theorems/0c613f8b-9272-4f72-abb9-0b0e9057c65d
-- title:
--   `BookProof.NsPartialFourier.postcompCLM_vecMomentumOp` (T : F →L[ℂ] G) (m : V) (f : 𝓢(V, F)) : postcompCLM T (vecMomentumOp m f) = vecMomentumOp m (postcompCLM T f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.postcompCLM_vecMomentumOp` (T : F →L[ℂ] G) (m : V) (f : 𝓢(V, F)) : postcompCLM T (vecMomentumOp m f) = vecMomentumOp m (postcompCLM T f)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.postcompCLM_vecMomentumOp`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.postcompCLM_vecMomentumOp
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

theorem BookProof.NsPartialFourier.postcompCLM_vecMomentumOp (T : F →L[ℂ] G) (m : V) (f : 𝓢(V, F)) :
    postcompCLM T (vecMomentumOp m f) = vecMomentumOp m (postcompCLM T f) := by sorry
