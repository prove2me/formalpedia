-- Prove2me | Theorems.Thm_BookProof_ChapterBijectionProbability_card_bijective_fin
-- name    : BookProof.ChapterBijectionProbability.card_bijective_fin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:55:56.96098+00:00
-- url     : https://prove2.me/theorems/6f6bde35-99d4-4541-90bc-13ae0e7e441c
-- title:
--   `BookProof.ChapterBijectionProbability.card_bijective_fin` (n : ℕ) : Fintype.card {f : Fin n → Fin n // Function.Bijective f} = n !
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBijectionProbability`.
--
--   `BookProof.ChapterBijectionProbability.card_bijective_fin` (n : ℕ) : Fintype.card {f : Fin n → Fin n // Function.Bijective f} = n !
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBijectionProbability.card_bijective_fin`.

-- Generated from ChapterBijectionProbability.lean — theorem BookProof.ChapterBijectionProbability.card_bijective_fin
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability


open scoped Nat
open Filter Asymptotics

theorem BookProof.ChapterBijectionProbability.card_bijective_fin (n : ℕ) :
    Fintype.card {f : Fin n → Fin n // Function.Bijective f} = n ! := by sorry
