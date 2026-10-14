-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_band_refinement_krylov
-- name    : BookProof.ChapterH8.sirk_band_refinement_krylov
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:42:16.560995+00:00
-- url     : https://prove2.me/theorems/79dc4cd0-c94e-4e16-abec-228759fb47d6
-- title:
--   The Lean 4 theorem `sirk_band_refinement_krylov` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_band_refinement_krylov` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.sirk_band_refinement_krylov
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_krylov_li_of_le
open BookProof.ChapterH4
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.sirk_band_refinement_krylov {m n : ℕ} (hmn : m ≤ n) (H : E →ₗ[ℂ] E) (v : E)
    (X : E →L[ℂ] E) (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v))
    (hinvm : ∀ x : EuclideanSpace ℂ (Fin m), ∃ y : EuclideanSpace ℂ (Fin m),
      X (krylovEmbedding H v (krylov_li_of_le hmn hli) x)
        = krylovEmbedding H v (krylov_li_of_le hmn hli) y)
    (hinvn : ∀ x : EuclideanSpace ℂ (Fin n), ∃ y : EuclideanSpace ℂ (Fin n),
      X (krylovEmbedding H v hli x) = krylovEmbedding H v hli y)
    (p : Polynomial ℂ) (u : E)
    (hu : krylovEmbedding H v (krylov_li_of_le hmn hli)
      ((adjoint (krylovEmbedding H v (krylov_li_of_le hmn hli))) u) = u) :
    krylovEmbedding H v hli
        ((Polynomial.aeval (compress (krylovEmbedding H v hli) X) p)
          ((adjoint (krylovEmbedding H v hli)) u))
      = krylovEmbedding H v (krylov_li_of_le hmn hli)
        ((Polynomial.aeval (compress (krylovEmbedding H v (krylov_li_of_le hmn hli)) X) p)
          ((adjoint (krylovEmbedding H v (krylov_li_of_le hmn hli))) u)) := by sorry
