-- Prove2me | solution 1 for permPattern_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:40.140246+00:00
-- url     : https://prove2.me/submissions/976140ee-cfef-4243-9f02-cb1ea6ee71e0

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
public import Definitions.Def_ForbiddenMatrix_PermutationPatterns

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
theorem _root_.solution (n : ℕ) :
    PermPattern (1 : Equiv.Perm (Fin n)) = IdentityPattern n := rfl
