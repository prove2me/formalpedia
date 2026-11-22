-- Prove2me | Theorems.Thm_Finpartition_card_of_mem_equipartitionToIco_parts
-- name    : Finpartition.card_of_mem_equipartitionToIco_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:16.674172+00:00
-- url     : https://prove2.me/theorems/d6559c43-d3ca-4043-9233-f1981ca2c8f4
-- title:
--   Finpartition: card of mem equipartition To Ico parts
-- statement:
--   The Finpartition construction uses the card of mem equipartition To Ico parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L253-L262
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L253-L262

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Finpartition

theorem Finpartition.card_of_mem_equipartitionToIco_parts
    {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a)
    (i : Finset ℕ) (hi : i ∈ (equipartitionToIco a b k).parts) :
    #i = (b - a) / k ∨ #i = (b - a) / k + 1 := by sorry
