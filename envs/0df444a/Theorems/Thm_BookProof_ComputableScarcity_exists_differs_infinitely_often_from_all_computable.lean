-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_exists_differs_infinitely_often_from_all_computable
-- name    : BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:17:49.215984+00:00
-- url     : https://prove2.me/theorems/8df6fb64-88c3-40f9-ad31-6a4af97fe62c
-- title:
--   `BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable` : ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → {n | f n ≠ g n}.Infinite
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable` : ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → {n | f n ≠ g n}.Infinite
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable :
    ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → {n | f n ≠ g n}.Infinite := by sorry
