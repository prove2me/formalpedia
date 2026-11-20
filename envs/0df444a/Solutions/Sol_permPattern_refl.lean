-- Prove2me | solution 1 for permPattern_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:27.962178+00:00
-- url     : https://prove2.me/submissions/2a94c086-861a-4bcf-9735-262e8d12cb67

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
    PermPattern (.refl _ : Equiv.Perm (Fin n)) = IdentityPattern n := rfl
