-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignFiber_bornMap_eq_iff_signFlip
-- name    : BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:57:13.866118+00:00
-- url     : https://prove2.me/theorems/5842a97f-8255-45e2-ace4-e8991d8c4e96
-- title:
--   `BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip` (x y : EuclideanSpace ℝ (Fin n)) : bornMap y = bornMap x ↔ ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ y = signFl
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignFiber`.
--
--   `BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip` (x y : EuclideanSpace ℝ (Fin n)) : bornMap y = bornMap x ↔ ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ y = signFlip s x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip`.

-- Generated from ChapterFreeFieldBornSignFiber.lean — theorem BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignFiber
open BookProof.ChapterFreeFieldBornSignFiber

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip (x y : EuclideanSpace ℝ (Fin n)) :
    bornMap y = bornMap x ↔
      ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ y = signFlip s x := by sorry
