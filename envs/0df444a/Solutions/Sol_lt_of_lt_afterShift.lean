-- Prove2me | solution 1 for lt_of_lt_afterShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:13.649149+00:00
-- url     : https://prove2.me/submissions/325963e9-de44-4f95-ab76-5c8af45fab34

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
theorem _root_.solution {a k : ℕ} (hk : k < afterShift M a) : M k ≤ a := by
  by_contra h
  have hle : afterShift M a ≤ k := Nat.sInf_le (Nat.lt_of_not_le h)
  omega
