-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignFiber_signFlip_comp
-- name    : BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:56:27.078113+00:00
-- url     : https://prove2.me/theorems/1ac53764-4f2c-4514-b189-dc207521c7b7
-- title:
--   `BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp` (s t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) : signFlip s (signFlip t x) = signFlip (fun k => s k * t k) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignFiber`.
--
--   `BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp` (s t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) : signFlip s (signFlip t x) = signFlip (fun k => s k * t k) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp`.

-- Generated from ChapterFreeFieldBornSignFiber.lean — theorem BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignFiber
open BookProof.ChapterFreeFieldBornSignFiber

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp (s t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    signFlip s (signFlip t x) = signFlip (fun k => s k * t k) x := by sorry
