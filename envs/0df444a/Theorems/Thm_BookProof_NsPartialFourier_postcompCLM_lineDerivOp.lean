-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_postcompCLM_lineDerivOp
-- name    : BookProof.NsPartialFourier.postcompCLM_lineDerivOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:12.67884+00:00
-- url     : https://prove2.me/theorems/50e4757a-5df5-43ef-a0b1-d12637b5a940
-- title:
--   `BookProof.NsPartialFourier.postcompCLM_lineDerivOp` (T : F →L[ℂ] G) (f : 𝓢(V, F)) (m : V) : postcompCLM T (∂_{m} f : 𝓢(V, F)) = (∂_{m} (postcompCLM T f) : 𝓢(V, G))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.postcompCLM_lineDerivOp` (T : F →L[ℂ] G) (f : 𝓢(V, F)) (m : V) : postcompCLM T (∂_{m} f : 𝓢(V, F)) = (∂_{m} (postcompCLM T f) : 𝓢(V, G))
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.postcompCLM_lineDerivOp`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.postcompCLM_lineDerivOp
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem BookProof.NsPartialFourier.postcompCLM_lineDerivOp (T : F →L[ℂ] G) (f : 𝓢(V, F)) (m : V) :
    postcompCLM T (∂_{m} f : 𝓢(V, F)) = (∂_{m} (postcompCLM T f) : 𝓢(V, G)) := by sorry
