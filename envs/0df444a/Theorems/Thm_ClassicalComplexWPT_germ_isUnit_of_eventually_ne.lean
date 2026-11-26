-- Prove2me | Theorems.Thm_ClassicalComplexWPT_germ_isUnit_of_eventually_ne
-- name    : ClassicalComplexWPT.germ_isUnit_of_eventually_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:06.624634+00:00
-- url     : https://prove2.me/theorems/0e1c80a8-693a-5c0e-9d36-9e0d5528b309
-- title:
--   Classical Complex WPT: germ is Unit of eventually ne
-- statement:
--   A representative which is eventually nonzero defines a unit in the function-germ ring.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Germs.lean#L18-L26
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Germs.lean#L18-L26

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Order.Filter.Germ.Basic
import Definitions.Def_ClassicalComplexWPT_Germs
set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.germ_isUnit_of_eventually_ne {X : Type*} {l : Filter X} {g : X → ℂ}
    (hg : ∀ᶠ x in l, g x ≠ 0) : IsUnit (g : Filter.Germ l ℂ) := by sorry
