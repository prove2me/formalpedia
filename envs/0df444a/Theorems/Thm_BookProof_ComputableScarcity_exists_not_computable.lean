-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_exists_not_computable
-- name    : BookProof.ComputableScarcity.exists_not_computable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:18:02.944995+00:00
-- url     : https://prove2.me/theorems/2ae1176d-d1a2-4b04-a712-07a7cb7a3cd2
-- title:
--   `BookProof.ComputableScarcity.exists_not_computable` : ∃ f : ℕ → ℕ, ¬ Computable f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.exists_not_computable` : ∃ f : ℕ → ℕ, ¬ Computable f
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.exists_not_computable`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.exists_not_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.exists_not_computable : ∃ f : ℕ → ℕ, ¬ Computable f := by sorry
