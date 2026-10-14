-- Prove2me | Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_nested
-- name    : BookProof.ChapterH8.orthonormalEmbedding_nested
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-12T13:29:34.744118+00:00
-- url     : https://prove2.me/theorems/1ff6cd03-3f5b-4a3e-89f7-65b08f19c582
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_nested` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_nested` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_nested
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.orthonormalEmbedding_nested {m n : ℕ} (hmn : m ≤ n)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    orthonormalEmbedding w hw = (orthonormalEmbedding w' hw').comp (coordIncl hmn) := by sorry
