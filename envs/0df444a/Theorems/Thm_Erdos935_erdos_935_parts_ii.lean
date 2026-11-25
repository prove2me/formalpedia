-- Prove2me | Theorems.Thm_Erdos935_erdos_935_parts_ii
-- name    : Erdos935.erdos_935.parts.ii
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T12:38:58.778596+00:00
-- url     : https://prove2.me/theorems/e3fd9b3d-2505-5ddf-a806-975e6dc86fca
-- title:
--   parts: ii
-- statement:
--   The parts construction uses the ii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L206-L209
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L206-L209

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935

theorem Erdos935.erdos_935.parts.ii :
    ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by sorry
