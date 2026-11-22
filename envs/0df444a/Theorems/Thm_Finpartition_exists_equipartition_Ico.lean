-- Prove2me | Theorems.Thm_Finpartition_exists_equipartition_Ico
-- name    : Finpartition.exists_equipartition_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:15.9053+00:00
-- url     : https://prove2.me/theorems/82cba104-be75-4e70-93d3-805a0d894897
-- title:
--   Finpartition: exists equipartition Ico
-- statement:
--   The Finpartition construction uses the exists equipartition Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L276-L283
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L276-L283

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Finpartition

theorem Finpartition.exists_equipartition_Ico {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    ∃ P : Finpartition (Finset.Ico a b),
      P.IsEquipartition ∧ #P.parts = k ∧ ∀ i ∈ P.parts, ∃ c d, i = Finset.Ico c d := by sorry
