-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_countable_computable
-- name    : BookProof.ComputableScarcity.countable_computable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:17:07.284814+00:00
-- url     : https://prove2.me/theorems/44c2c08e-e44a-408f-bedd-7c566e1a0ac8
-- title:
--   `BookProof.ComputableScarcity.countable_computable` : {f : ℕ → ℕ | Computable f}.Countable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.countable_computable` : {f : ℕ → ℕ | Computable f}.Countable
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.countable_computable`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.countable_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.countable_computable : {f : ℕ → ℕ | Computable f}.Countable := by sorry
