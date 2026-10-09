-- Prove2me | Theorems.Thm_BookProof_ChapterF8_twoLevelHash_total
-- name    : BookProof.ChapterF8.twoLevelHash_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:08:07.218833+00:00
-- url     : https://prove2.me/theorems/41262228-0297-48e6-9aca-34bbf76c29e1
-- title:
--   `BookProof.ChapterF8.twoLevelHash_total` {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K) (x : Fin d → ℝ) : twoLevelHash h g x ∈ singleExcitation K
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF8`.
--
--   `BookProof.ChapterF8.twoLevelHash_total` {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K) (x : Fin d → ℝ) : twoLevelHash h g x ∈ singleExcitation K
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF8.twoLevelHash_total`.

-- Generated from ChapterF8.lean — theorem BookProof.ChapterF8.twoLevelHash_total
import Mathlib
import Definitions.Def_ChapterF8
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.ChapterF8


noncomputable section

open scoped BigOperators

theorem BookProof.ChapterF8.twoLevelHash_total {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K)
    (x : Fin d → ℝ) : twoLevelHash h g x ∈ singleExcitation K := by sorry
