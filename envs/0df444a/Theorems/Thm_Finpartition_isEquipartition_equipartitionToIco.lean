-- Prove2me | Theorems.Thm_Finpartition_isEquipartition_equipartitionToIco
-- name    : Finpartition.isEquipartition_equipartitionToIco
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:15.204097+00:00
-- url     : https://prove2.me/theorems/face95d1-849a-4754-b63c-dbd66bcc40ec
-- title:
--   Finpartition: is Equipartition equipartition To Ico
-- statement:
--   The Finpartition construction uses the is Equipartition equipartition To Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L264-L274
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L264-L274

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Finpartition

theorem Finpartition.isEquipartition_equipartitionToIco {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    (equipartitionToIco a b k).IsEquipartition := by sorry
