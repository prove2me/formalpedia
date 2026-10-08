-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_bornMap_signFlip
-- name    : BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:49.976062+00:00
-- url     : https://prove2.me/theorems/6b4c6888-bd6e-4347-9548-2acb2756cafc
-- title:
--   `BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) (x : EuclideanSpace ℝ (Fin n)) : bornMap (signFlip s x) = bornMap x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignGauge`.
--
--   `BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) (x : EuclideanSpace ℝ (Fin n)) : bornMap (signFlip s x) = bornMap x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip`.

-- Generated from ChapterFreeFieldBornSignGauge.lean — theorem BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    bornMap (signFlip s x) = bornMap x := by sorry
