-- Prove2me | Theorems.Thm_BookProof_ChapterBijectionProbability_card_fun_fin
-- name    : BookProof.ChapterBijectionProbability.card_fun_fin
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:55:41.468314+00:00
-- url     : https://prove2.me/theorems/1e4c432c-ab89-4858-a9d1-66a3dd5610ce
-- title:
--   `BookProof.ChapterBijectionProbability.card_fun_fin` (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBijectionProbability`.
--
--   `BookProof.ChapterBijectionProbability.card_fun_fin` (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBijectionProbability.card_fun_fin`.

-- Generated from ChapterBijectionProbability.lean — theorem BookProof.ChapterBijectionProbability.card_fun_fin
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability


open scoped Nat
open Filter Asymptotics

theorem BookProof.ChapterBijectionProbability.card_fun_fin (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n := by sorry
