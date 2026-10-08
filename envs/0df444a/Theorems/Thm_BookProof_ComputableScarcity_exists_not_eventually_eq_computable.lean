-- Prove2me | Theorems.Thm_BookProof_ComputableScarcity_exists_not_eventually_eq_computable
-- name    : BookProof.ComputableScarcity.exists_not_eventually_eq_computable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:18:12.933032+00:00
-- url     : https://prove2.me/theorems/07bddd4c-a068-4837-a545-9e8b981a7dc6
-- title:
--   `BookProof.ComputableScarcity.exists_not_eventually_eq_computable` : ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → ¬ (∀ᶠ n in Filter.atTop, f n = g n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterComputableScarcity`.
--
--   `BookProof.ComputableScarcity.exists_not_eventually_eq_computable` : ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → ¬ (∀ᶠ n in Filter.atTop, f n = g n)
--
--   Formalization note: Lean 4 identifier `BookProof.ComputableScarcity.exists_not_eventually_eq_computable`.

-- Generated from ChapterComputableScarcity.lean — theorem BookProof.ComputableScarcity.exists_not_eventually_eq_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity



open Nat.Partrec

open Classical

theorem BookProof.ComputableScarcity.exists_not_eventually_eq_computable :
    ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → ¬ (∀ᶠ n in Filter.atTop, f n = g n) := by sorry
