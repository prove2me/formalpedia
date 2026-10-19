-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_fourier_postcompCLM
-- name    : BookProof.NsPartialFourier.fourier_postcompCLM
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:25.119976+00:00
-- url     : https://prove2.me/theorems/ec2ab19f-4d87-410f-877f-85f1ddf3f58b
-- title:
--   `BookProof.NsPartialFourier.fourier_postcompCLM` [CompleteSpace F] [CompleteSpace G] (T : F →L[ℂ] G) (f : 𝓢(V, F)) : (𝓕 (postcompCLM T f) : 𝓢(V, G)) = postcompCLM T (𝓕 f : 𝓢(V, F))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.fourier_postcompCLM` [CompleteSpace F] [CompleteSpace G] (T : F →L[ℂ] G) (f : 𝓢(V, F)) : (𝓕 (postcompCLM T f) : 𝓢(V, G)) = postcompCLM T (𝓕 f : 𝓢(V, F))
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.fourier_postcompCLM`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.fourier_postcompCLM
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem BookProof.NsPartialFourier.fourier_postcompCLM [CompleteSpace F] [CompleteSpace G] (T : F →L[ℂ] G) (f : 𝓢(V, F)) :
    (𝓕 (postcompCLM T f) : 𝓢(V, G)) = postcompCLM T (𝓕 f : 𝓢(V, F)) := by sorry
