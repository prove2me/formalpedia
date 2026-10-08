-- Prove2me | Theorems.Thm_BookProof_ChapterBijectionProbability_bijProb_eq_card_ratio
-- name    : BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:55:40.721366+00:00
-- url     : https://prove2.me/theorems/35164a77-7794-4241-962e-8fc6345c54d0
-- title:
--   `BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio` (n : ℕ) : bijProb n = (Fintype.card {f : Fin n → Fin n // Function.Bijective f} : ℝ) / (Fintype.card (Fin n → Fin n) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBijectionProbability`.
--
--   `BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio` (n : ℕ) : bijProb n = (Fintype.card {f : Fin n → Fin n // Function.Bijective f} : ℝ) / (Fintype.card (Fin n → Fin n) : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio`.

-- Generated from ChapterBijectionProbability.lean — theorem BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability


open scoped Nat
open Filter Asymptotics

theorem BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio (n : ℕ) :
    bijProb n =
      (Fintype.card {f : Fin n → Fin n // Function.Bijective f} : ℝ)
        / (Fintype.card (Fin n → Fin n) : ℝ) := by sorry
