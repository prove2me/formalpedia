-- Prove2me | Theorems.Thm_Finpartition_card_equipartitionToIco_parts
-- name    : Finpartition.card_equipartitionToIco_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:38.434436+00:00
-- url     : https://prove2.me/theorems/0fbbd41f-0a9c-4195-b1b3-a34721e99134
-- title:
--   Finpartition: card equipartition To Ico parts
-- statement:
--   The Finpartition construction uses the card equipartition To Ico parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L237-L247
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L237-L247

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Finpartition

theorem Finpartition.card_equipartitionToIco_parts {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    #(equipartitionToIco a b k).parts = k := by sorry
