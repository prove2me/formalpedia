-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_norm
-- name    : BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:29.434127+00:00
-- url     : https://prove2.me/theorems/9a1f2f3d-0e7d-41d7-a0e6-4fa6fd0ea2c9
-- title:
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) (x : EuclideanSpace ℝ (Fin n)) : ‖signFlip s x‖ = ‖x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignGauge`.
--
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) (x : EuclideanSpace ℝ (Fin n)) : ‖signFlip s x‖ = ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm`.

-- Generated from ChapterFreeFieldBornSignGauge.lean — theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖signFlip s x‖ = ‖x‖ := by sorry
