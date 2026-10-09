-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_smul_right
-- name    : BookProof.ChapterF7.l2pair_smul_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:36.133018+00:00
-- url     : https://prove2.me/theorems/3d4e718d-637b-4642-8afa-d85c52cae46f
-- title:
--   `BookProof.ChapterF7.l2pair_smul_right` (c : ℂ) (f g : 𝓢(ℝ, ℂ)) : l2pair f (c • g) = c * l2pair f g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_smul_right` (c : ℂ) (f g : 𝓢(ℝ, ℂ)) : l2pair f (c • g) = c * l2pair f g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_smul_right`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_smul_right
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_smul_right (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    l2pair f (c • g) = c * l2pair f g := by sorry
