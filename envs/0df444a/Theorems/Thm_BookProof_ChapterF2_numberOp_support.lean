-- Prove2me | Theorems.Thm_BookProof_ChapterF2_numberOp_support
-- name    : BookProof.ChapterF2.numberOp_support
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:46:55.410177+00:00
-- url     : https://prove2.me/theorems/276382b0-fff5-4493-8133-763573079eb9
-- title:
--   `BookProof.ChapterF2.numberOp_support` (p : ℂ[X]) : (numberOp p).support ⊆ p.support
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF2`.
--
--   `BookProof.ChapterF2.numberOp_support` (p : ℂ[X]) : (numberOp p).support ⊆ p.support
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF2.numberOp_support`.

-- Generated from ChapterF2.lean — theorem BookProof.ChapterF2.numberOp_support
import Definitions.Def_ChapterF1
import Mathlib
import Definitions.Def_ChapterF2
import Definitions.Def_ChapterGhostField
open BookProof.GhostField
open BookProof.ChapterF2


open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

theorem BookProof.ChapterF2.numberOp_support (p : ℂ[X]) : (numberOp p).support ⊆ p.support := by sorry
