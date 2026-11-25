-- Prove2me | Theorems.Thm_Finset_choose_le_card_mul_choose
-- name    : Finset.choose_le_card_mul_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:34.159458+00:00
-- url     : https://prove2.me/theorems/a998b1a5-1673-51b0-b2cb-ffcb84a238f4
-- title:
--   Finset: choose le card mul choose
-- statement:
--   **Averaging over `m`-sets.** If every `m`-subset of `s` contains a member of a family `𝓕` of
--   `t`-subsets of `s`, then `C(|s|, t) ≤ |𝓕| · C(m, t)`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L69-L101
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L69-L101

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
set_option autoImplicit true
@[expose] public section
public section
open Finset

theorem Finset.choose_le_card_mul_choose {α : Type*} {s : Finset α}
    {𝓕 : Finset (Finset α)} {t m : ℕ} (h𝓕 : 𝓕 ⊆ s.powersetCard t) (htm : t ≤ m) (hms : m ≤ #s)
    (hcover : ∀ M ∈ s.powersetCard m, ∃ F ∈ 𝓕, F ⊆ M) :
    (#s).choose t ≤ #𝓕 * m.choose t := by sorry
