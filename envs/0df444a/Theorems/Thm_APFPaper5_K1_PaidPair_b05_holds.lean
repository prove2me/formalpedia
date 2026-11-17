-- Prove2me | Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
-- name    : APFPaper5.K1.PaidPair.b05_holds
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:18:31.996668+00:00
-- url     : https://prove2.me/theorems/a96f9ab0-a8c9-4ecd-b065-1445370d7aa6
-- title:
--   b05 holds
-- statement:
--   Result: b05 holds. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem b05_holds :
--       APFB05.MarginalFloor (Context := Unit) (D := fun _ => Fin 2) (P := fun _ => Finset (Fin 3))
--         (R := fun _ => Finset (Fin 3)) (Record := fun _ => Fin 3) (fun _ => ledger.wholeResource)
--         (fun _ => ledger.calibration) (fun _ => ledger.maintained) (fun _ => ledger.sufficient)
--         (fun _ => ledger.usesToRealize) (fun _ _ => True) (fun _ => 3) (fun _ => 1)
--   ```
--
--   Module context and limits: The supplied three-record ledger has costs 0,1,1,3, capacity 3 and floor 1. It satisfies the encoded B05 and stronger Counted predicate, with a joint record. Other declared forms and physical realization are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_counted_pair_with_relation:180; pullbacks v39; source SHA-256 48803b7b623de995419686f2ee9303a33ebaa48a3fd1aae8458e4bccb7c112c5']

import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem APFPaper5.K1.PaidPair.b05_holds :
@APFB05.MarginalFloor.{0, 0, 0, 0, 0} Unit
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) => Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (fun (x : Unit) => Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (fun (x : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (fun (g : Unit) => instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.wholeResource.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.calibration.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.maintained.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.sufficient.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
  (fun (x : Unit) =>
    @APFPaper1.RecordLedger.usesToRealize.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
  (fun (x : Unit) (x_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
  (fun (x : Unit) =>
    @OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  fun (x : Unit) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne) := by sorry
