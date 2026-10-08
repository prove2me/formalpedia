-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_free_of_pos
-- name    : BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:40:05.592821+00:00
-- url     : https://prove2.me/theorems/5d071bf2-61b1-47e9-8159-dc2a9705b0a0
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos` {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ k, x k ≠ 0) : boolFlip b x = x ↔ b = (fun _ => false)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos` {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ k, x k ≠ 0) : boolFlip b x = x ↔ b = (fun _ => false)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ k, x k ≠ 0) :
    boolFlip b x = x ↔ b = (fun _ => false) := by sorry
