-- Prove2me | Theorems.Thm_APFPaper5_K2_shared_record_counts_four_r2
-- name    : APFPaper5.K2.shared_record_counts_four_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:02:09.664271+00:00
-- url     : https://prove2.me/theorems/724c8301-1b32-4ca4-bd80-e71281fce340
-- title:
--   shared record counts four
-- statement:
--   Scope and conditions: The successor retains the existing mathematical candidate results while moving three unchanged record-cost lemmas to their own source. The active indicator transforms by permutation without flips and by complementation with flips; the signed candidate transforms with signs. Supplied shared-record examples yield self-overlap four or cancellation to zero. They demonstrate limitations of these candidates and do not adopt a state representation, positive definite physical carrier, or physical hold action. Old native versions and dependents remain unchanged.
--
--   Exact source statement:
--
--   theorem shared_record_counts_four :
--       tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
--         (fun _ => 1) (fun _ => 1) = 4
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:220; USB pullbacks v58 batch B; SHA-256 431ae59f5fdcf92750d333fb33ea70e7067fe8197aab1fa0b80f8447d982d9b6']

import Definitions.Def_APFPaper5_K2_StateClass_r2
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem APFPaper5.K2.shared_record_counts_four_r2 :
@Eq.{1} Real
  (@APFPaper5.K1.tableForm.{0} Bool Bool.fintype
    (@APFPaper5.K1.atomTable.{0, 0} Bool Unit PUnit.fintype.{0}
      (fun (x : Unit) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      fun (x : Bool) (x_1 : Unit) => Bool.true)
    (fun (x : Bool) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) fun (x : Bool) =>
    @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
  (@OfNat.ofNat.{0} Real (nat_lit 4)
    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := by sorry
