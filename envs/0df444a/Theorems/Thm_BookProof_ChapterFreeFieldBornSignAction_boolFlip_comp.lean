-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_comp
-- name    : BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:16:59.387044+00:00
-- url     : https://prove2.me/theorems/dab857e9-60fe-4e05-ad0b-ce1555845730
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp` (b₁ b₂ : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : boolFlip b₁ (boolFlip b₂ x) = boolFlip (fun k => xor (b₁ k) (b₂ k))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp` (b₁ b₂ : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : boolFlip b₁ (boolFlip b₂ x) = boolFlip (fun k => xor (b₁ k) (b₂ k)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp (b₁ b₂ : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    boolFlip b₁ (boolFlip b₂ x) = boolFlip (fun k => xor (b₁ k) (b₂ k)) x := by sorry
