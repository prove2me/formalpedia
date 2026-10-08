-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCapacity_distScore_margin_of_separated
-- name    : BookProof.ChapterAttentionCapacity.distScore_margin_of_separated
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:40.065069+00:00
-- url     : https://prove2.me/theorems/dfe11f7b-3114-46b6-a6a6-ede9fc60529a
-- title:
--   `BookProof.ChapterAttentionCapacity.distScore_margin_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) : ∀ l, l ≠ i →
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCapacity`.
--
--   `BookProof.ChapterAttentionCapacity.distScore_margin_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) : ∀ l, l ≠ i → distScore (k i) k l + r ^ 2 ≤ distScore (k i) k i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCapacity.distScore_margin_of_separated`.

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.distScore_margin_of_separated
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCapacity.distScore_margin_of_separated {k : Fin m → EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) :
    ∀ l, l ≠ i → distScore (k i) k l + r ^ 2 ≤ distScore (k i) k i := by sorry
