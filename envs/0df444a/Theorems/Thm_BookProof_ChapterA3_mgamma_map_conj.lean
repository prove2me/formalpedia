-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_map_conj
-- name    : BookProof.ChapterA3.mgamma_map_conj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:38:49.075242+00:00
-- url     : https://prove2.me/theorems/e0efd64f-5c34-44a6-90c1-a2533c989bc1
-- title:
--   `BookProof.ChapterA3.mgamma_map_conj` (μ : Fin 4) : (mgamma μ).map (starRingEnd ℂ) = mgamma μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.mgamma_map_conj` (μ : Fin 4) : (mgamma μ).map (starRingEnd ℂ) = mgamma μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_map_conj`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.mgamma_map_conj
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_map_conj (μ : Fin 4) :
    (mgamma μ).map (starRingEnd ℂ) = mgamma μ := by sorry
