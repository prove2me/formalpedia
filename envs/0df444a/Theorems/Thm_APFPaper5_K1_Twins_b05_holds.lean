-- Prove2me | Theorems.Thm_APFPaper5_K1_Twins_b05_holds
-- name    : APFPaper5.K1.Twins.b05_holds
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:19:42.683703+00:00
-- url     : https://prove2.me/theorems/6b941b07-7aa8-4fb2-9623-5ed29f32da3b
-- title:
--   b05 holds
-- statement:
--   Result: b05 holds. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem b05_holds :
--       APFB05.MarginalFloor (Context := Unit) (D := fun _ => Fin 2) (P := fun _ => Prot)
--         (R := fun _ => Finset (Fin 2)) (Record := fun _ => Fin 2) (fun _ => ledger.wholeResource)
--         (fun _ => ledger.calibration) (fun _ => ledger.maintained) (fun _ => ledger.sufficient)
--         (fun _ => ledger.usesToRealize) (fun _ _ => True) (fun _ => 2) (fun _ => 1)
--   ```
--
--   Module context and limits: The Twins ledger satisfies B05, singleton floor and earlier LedgerCounted but has a degenerate party score. It fails the stronger Counted definition with own paid records. Other declared forms and physical realization are not checked.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_twins_same_records:178; pullbacks v39; source SHA-256 4947d29785facbbbf72c6ffafa3db80c95241039017a85b271de766684e47b02']

import Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem APFPaper5.K1.Twins.b05_holds :
@APFB05.MarginalFloor.{0, 0, 0, 0, 0} Unit
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) => APFPaper5.K1.Twins.Prot)
  (fun (x : Unit) => Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (g : Unit) => instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.wholeResource.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.calibration.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.maintained.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.sufficient.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.usesToRealize.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      APFPaper5.K1.Twins.ledger)
  (fun (x : Unit) (x_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
  (fun (x : Unit) =>
    @OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  fun (x : Unit) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne) := by sorry
