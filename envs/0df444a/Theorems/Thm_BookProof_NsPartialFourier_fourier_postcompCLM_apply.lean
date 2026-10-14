-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_fourier_postcompCLM_apply
-- name    : BookProof.NsPartialFourier.fourier_postcompCLM_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:14.13141+00:00
-- url     : https://prove2.me/theorems/204803b6-7a8b-476f-9085-ca212a9d6073
-- title:
--   `BookProof.NsPartialFourier.fourier_postcompCLM_apply` [CompleteSpace F] [CompleteSpace G] (T : F →L[ℂ] G) (f : 𝓢(V, F)) (x : V) : (𝓕 (postcompCLM T f) : 𝓢(V, G)) x = T ((𝓕 f : 𝓢(V
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.fourier_postcompCLM_apply` [CompleteSpace F] [CompleteSpace G] (T : F →L[ℂ] G) (f : 𝓢(V, F)) (x : V) : (𝓕 (postcompCLM T f) : 𝓢(V, G)) x = T ((𝓕 f : 𝓢(V, F)) x)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.fourier_postcompCLM_apply`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.fourier_postcompCLM_apply
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem BookProof.NsPartialFourier.fourier_postcompCLM_apply [CompleteSpace F] [CompleteSpace G]
    (T : F →L[ℂ] G) (f : 𝓢(V, F)) (x : V) :
    (𝓕 (postcompCLM T f) : 𝓢(V, G)) x = T ((𝓕 f : 𝓢(V, F)) x) := by sorry
