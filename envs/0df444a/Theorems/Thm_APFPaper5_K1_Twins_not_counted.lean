-- Prove2me | Theorems.Thm_APFPaper5_K1_Twins_not_counted
-- name    : APFPaper5.K1.Twins.not_counted
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:42:55.943538+00:00
-- url     : https://prove2.me/theorems/d636304d-cf9d-49ea-a682-e00853313cfc
-- title:
--   not counted
-- statement:
--   Result: not counted. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem Twins.not_counted :
--       ¬ Counted Twins.ledger (fun _ => True) 2 (fun i : Fin 2 => i)
--   ```
--
--   Module context and limits: Counted explicitly includes own paid records and gives a faithful nonnegative diagonal on a finite record type. Deriving it from LedgerCounted additionally requires the declared marginal floor and LedgerAvailable. FreePair and Twins fail this stronger definition.
--
--   Source scope parameters:
--
--   ```lean
--   variable {D P Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_counted_family:104; pullbacks v39; source SHA-256 1516b4a976fe16e975b9aecfb11d8c455ad72d97076ec2ad17d2e8501c8b7e57']

import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_free_pair_paid_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_FreePair_b05_holds
import Theorems.Thm_APFPaper5_K1_FreePair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_FreePair_party_score_not_faithful
import Theorems.Thm_APFPaper5_K1_FreePair_no_own_paid_record
import Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
import Theorems.Thm_APFPaper5_K1_Twins_fc_single
import Theorems.Thm_APFPaper5_K1_Twins_b05_holds
import Theorems.Thm_APFPaper5_K1_Twins_single_novel_over_empty
import Theorems.Thm_APFPaper5_K1_Twins_pair_is_counted
import Theorems.Thm_APFPaper5_K1_Twins_party_all
import Theorems.Thm_APFPaper5_K1_Twins_party_score_not_faithful
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint
set_option autoImplicit false

theorem APFPaper5.K1.Twins.not_counted :
Not
  (@APFPaper5.K1.Counted.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    APFPaper5.K1.Twins.Prot (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.Twins.ledger
    (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i) := by sorry
