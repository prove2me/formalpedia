-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_eq_self_iff
-- name    : BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:39:31.309999+00:00
-- url     : https://prove2.me/theorems/dff4540d-2c96-475f-832d-2347e1a999e4
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff` {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)} : boolFlip b x = x ↔ ∀ k, x k ≠ 0 → b k = false
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff` {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)} : boolFlip b x = x ↔ ∀ k, x k ≠ 0 → b k = false
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_eq_self_iff {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)} :
    boolFlip b x = x ↔ ∀ k, x k ≠ 0 → b k = false := by sorry
