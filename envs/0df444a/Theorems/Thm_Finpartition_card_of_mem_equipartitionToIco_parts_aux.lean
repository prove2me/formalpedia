-- Prove2me | Theorems.Thm_Finpartition_card_of_mem_equipartitionToIco_parts_aux
-- name    : Finpartition.card_of_mem_equipartitionToIco_parts_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:40.679178+00:00
-- url     : https://prove2.me/theorems/7b899dac-b238-45ab-a13e-4d9cd1d73fe8
-- title:
--   Finpartition: card of mem equipartition To Ico parts aux
-- statement:
--   The Finpartition construction uses the card of mem equipartition To Ico parts aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L249-L251
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L249-L251

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Finpartition

theorem Finpartition.card_of_mem_equipartitionToIco_parts_aux {n k i : ℕ} :
    equiEndpoint n k (i + 1) - equiEndpoint n k i = if i < n % k then n / k + 1 else n / k := by sorry
