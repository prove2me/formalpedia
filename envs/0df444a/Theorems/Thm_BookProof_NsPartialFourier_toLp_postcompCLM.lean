-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_toLp_postcompCLM
-- name    : BookProof.NsPartialFourier.toLp_postcompCLM
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:23.336282+00:00
-- url     : https://prove2.me/theorems/7f63a9fc-38fc-4022-b4f3-85d099b5d86f
-- title:
--   `BookProof.NsPartialFourier.toLp_postcompCLM` (T : F →L[ℂ] G) (f : 𝓢(V, F)) : (postcompCLM T f).toLp 2 (volume : Measure V) = T.compLp (f.toLp 2 (volume : Measure V))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.toLp_postcompCLM` (T : F →L[ℂ] G) (f : 𝓢(V, F)) : (postcompCLM T f).toLp 2 (volume : Measure V) = T.compLp (f.toLp 2 (volume : Measure V))
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.toLp_postcompCLM`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.toLp_postcompCLM
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem BookProof.NsPartialFourier.toLp_postcompCLM (T : F →L[ℂ] G) (f : 𝓢(V, F)) :
    (postcompCLM T f).toLp 2 (volume : Measure V)
      = T.compLp (f.toLp 2 (volume : Measure V)) := by sorry
