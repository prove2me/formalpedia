-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCapacity_norm_headOutput_distScore_sub_le_of_separated
-- name    : BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:20:05.924095+00:00
-- url     : https://prove2.me/theorems/dcfd3495-f759-4995-be8d-77d2085073ed
-- title:
--   `BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {v : Fin m → E} {r beta C : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCapacity`.
--
--   `BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {v : Fin m → E} {r beta C : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (hv : ∀ l, ‖v l‖ ≤ C) (i : Fin m) : ‖headOutput beta (distScore (k i) k) v - v i‖ ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated`.

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated
    {k : Fin m → EuclideanSpace ℝ (Fin n)} {v : Fin m → E} {r beta C : ℝ}
    (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (hv : ∀ l, ‖v l‖ ≤ C)
    (i : Fin m) :
    ‖headOutput beta (distScore (k i) k) v - v i‖
      ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2))) := by sorry
