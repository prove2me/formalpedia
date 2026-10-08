-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_exists_infinitely_often_ne
-- name    : BookProof.ComputableScarcity.exists_infinitely_often_ne
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:17:12.079397+00:00
-- url     : https://prove2.me/theorems/0818e609-0b90-4922-b447-95503b08c595
-- title:
--   `BookProof.ComputableScarcity.exists_infinitely_often_ne` (e : ℕ → (ℕ → ℕ)) : ∃ f : ℕ → ℕ, ∀ k, {n | f n ≠ e k n}.Infinite
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.exists_infinitely_often_ne` (e : ℕ → (ℕ → ℕ)) : ∃ f : ℕ → ℕ, ∀ k, {n | f n ≠ e k n}.Infinite
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.exists_infinitely_often_ne`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.exists_infinitely_often_ne
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.exists_infinitely_often_ne (e : ℕ → (ℕ → ℕ)) :
    ∃ f : ℕ → ℕ, ∀ k, {n | f n ≠ e k n}.Infinite := by sorry
