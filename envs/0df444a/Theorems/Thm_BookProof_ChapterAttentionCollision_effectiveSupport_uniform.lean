-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_effectiveSupport_uniform
-- name    : BookProof.ChapterAttentionCollision.effectiveSupport_uniform
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:21:49.775102+00:00
-- url     : https://prove2.me/theorems/2aa1f790-24ff-4b6b-b2f2-c0932c861d6b
-- title:
--   `BookProof.ChapterAttentionCollision.effectiveSupport_uniform` (hm : 0 < m) : effectiveSupport (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.effectiveSupport_uniform` (hm : 0 < m) : effectiveSupport (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.effectiveSupport_uniform`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.effectiveSupport_uniform
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.effectiveSupport_uniform (hm : 0 < m) :
    effectiveSupport (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ) := by sorry
