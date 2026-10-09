-- Prove2me | Theorems.Thm_BookProof_ChapterEntropy_card_selfMaps
-- name    : BookProof.ChapterEntropy.card_selfMaps
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:47:03.974149+00:00
-- url     : https://prove2.me/theorems/d7404844-9ad4-44be-8de5-00cdf378e7ee
-- title:
--   `BookProof.ChapterEntropy.card_selfMaps` (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropy`.
--
--   `BookProof.ChapterEntropy.card_selfMaps` (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropy.card_selfMaps`.

-- Generated from ChapterEntropy.lean — theorem BookProof.ChapterEntropy.card_selfMaps
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy



open Filter Asymptotics
open scoped Topology

theorem BookProof.ChapterEntropy.card_selfMaps (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n := by sorry
