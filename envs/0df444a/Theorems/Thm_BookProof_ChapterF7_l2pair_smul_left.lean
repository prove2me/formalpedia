-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_smul_left
-- name    : BookProof.ChapterF7.l2pair_smul_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:32.475782+00:00
-- url     : https://prove2.me/theorems/fc9c505c-eb61-493d-acdf-b0cf6bb6a93d
-- title:
--   `BookProof.ChapterF7.l2pair_smul_left` (c : ℂ) (f g : 𝓢(ℝ, ℂ)) : l2pair (c • f) g = (starRingEnd ℂ) c * l2pair f g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_smul_left` (c : ℂ) (f g : 𝓢(ℝ, ℂ)) : l2pair (c • f) g = (starRingEnd ℂ) c * l2pair f g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_smul_left`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_smul_left
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_smul_left (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    l2pair (c • f) g = (starRingEnd ℂ) c * l2pair f g := by sorry
