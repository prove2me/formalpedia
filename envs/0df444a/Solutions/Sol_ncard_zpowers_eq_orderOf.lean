-- Prove2me | solution 1 for ncard_zpowers_eq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:36.645907+00:00
-- url     : https://prove2.me/submissions/b9316618-543f-4b92-a366-81aab4005e2c

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {G : Type*} [Group G] (g : G) :
    (Subgroup.zpowers g : Set G).ncard = orderOf g := by
  simp only [Set.ncard, ← Nat.card_zpowers]
  rfl
