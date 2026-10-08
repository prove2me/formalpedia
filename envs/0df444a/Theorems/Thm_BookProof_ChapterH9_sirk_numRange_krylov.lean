-- Prove2me | Theorems.Thm_BookProof_ChapterH9_sirk_numRange_krylov
-- name    : BookProof.ChapterH9.sirk_numRange_krylov
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T11:32:31.311042+00:00
-- url     : https://prove2.me/theorems/faeefb3e-f8f5-4acf-af02-3be1d25a7ad9
-- title:
--   The Lean 4 theorem `sirk_numRange_krylov` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_numRange_krylov` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.sirk_numRange_krylov
import Definitions.Def_ChapterH1
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH8
import Mathlib
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH8Bases
import Theorems.Thm_BookProof_ChapterH8_krylov_li_of_le
open BookProof.ChapterH4
open BookProof.ChapterH9

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap

theorem BookProof.ChapterH9.sirk_numRange_krylov {m n : ℕ} (hmn : m ≤ n) (H : E →ₗ[ℂ] E) (v : E)
    (X : E →L[ℂ] E) (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    numRange (compress (krylovEmbedding H v (krylov_li_of_le hmn hli)) X)
        ⊆ numRange (compress (krylovEmbedding H v hli) X)
      ∧ numRange (compress (krylovEmbedding H v hli) X) ⊆ numRange X := by sorry
