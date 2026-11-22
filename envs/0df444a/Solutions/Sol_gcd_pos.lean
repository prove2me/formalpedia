-- Prove2me | solution 1 for gcd_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:49.247578+00:00
-- url     : https://prove2.me/submissions/57449a88-c47b-4d39-8d9d-105a5502bead

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
theorem _root_.solution {ι : Type*} {f : ι → ℤ} {s : Finset ι} (hf : ∃ i ∈ s, f i ≠ 0) : 0 < s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp at hf
  | cons a s has ih =>
    classical
    rw [cons_eq_insert, gcd_insert, ← Int.coe_gcd, Int.natCast_pos]
    simp only [Int.gcd_pos_iff, ne_eq]
    simp only [cons_eq_insert, mem_insert, ne_eq, exists_eq_or_imp] at hf
    grind
