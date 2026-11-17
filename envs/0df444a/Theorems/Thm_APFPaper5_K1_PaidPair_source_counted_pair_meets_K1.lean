-- Prove2me | Theorems.Thm_APFPaper5_K1_PaidPair_source_counted_pair_meets_K1
-- name    : APFPaper5.K1.PaidPair.source_counted_pair_meets_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:32:03.620347+00:00
-- url     : https://prove2.me/theorems/6e5eb0a6-622d-4d73-b76c-25fa9eed0100
-- title:
--   source counted pair meets K1
-- statement:
--   Result: source counted pair meets K1. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem PaidPair.source_counted_pair_meets_K1 :
--       SourceCounted
--           (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
--             PaidPair.ledger.maintained)
--           PaidPair.ledger.wholeResource PaidPair.ledger.calibration PaidPair.ledger.maintained
--           PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize (fun _ => True) 3
--           (fun i : Fin 2 => i) ∧
--         (IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ)
--             (tableForm (sourcePartyScore
--               (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
--                 PaidPair.ledger.maintained)
--               PaidPair.ledger.maintained PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize
--               (fun i : Fin 2 => i))) ∧
--           FaithfulNonnegDiagonal
--             (tableForm (sourcePartyScore
--               (leastBill PaidPair.ledger.wholeResource PaidPair.ledger.calibration
--                 PaidPair.ledger.maintained)
--               PaidPair.ledger.maintained PaidPair.ledger.sufficient PaidPair.ledger.usesToRealize
--               (fun i : Fin 2 => i)))
--             (LinearEquiv.refl ℝ (Fin 2 → ℝ)))
--   ```
--
--   Module context and limits: Theorems retain the supplied support predicates, finite record type, nonnegative weights and own-record or SourceCounted hypotheses. leastBill remains an unruled candidate with empty real infimum zero. Ledger specialization is proved without asserting all source bills are additive.
--
--   Source scope parameters:
--
--   ```lean
--   variable {D P R Record : Type*}
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   variable [Fintype Record]
--   variable {P R Record : Type*}
--   variable {D : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D] [Fintype Record]
--   variable {D P Record : Type*}
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:320; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint
set_option autoImplicit false

theorem APFPaper5.K1.PaidPair.source_counted_pair_meets_K1 :
And
  (@APFPaper5.K1.SourceCounted.{0, 0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@APFPaper5.K1.leastBill.{0, 0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@APFPaper1.RecordLedger.wholeResource.{0, 0, 0}
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
      (@APFPaper1.RecordLedger.calibration.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
      (@APFPaper1.RecordLedger.maintained.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger))
    (@APFPaper1.RecordLedger.wholeResource.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
    (@APFPaper1.RecordLedger.calibration.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
    (@APFPaper1.RecordLedger.maintained.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
    (@APFPaper1.RecordLedger.sufficient.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
    (@APFPaper1.RecordLedger.usesToRealize.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
    (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => True)
    (@OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (And
    (@APFPaper5.K1.IsBilinear.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@APFPaper5.K1.sourcePartyScore.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@APFPaper5.K1.leastBill.{0, 0, 0}
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@APFPaper1.RecordLedger.wholeResource.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
            (@APFPaper1.RecordLedger.calibration.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
            (@APFPaper1.RecordLedger.maintained.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger))
          (@APFPaper1.RecordLedger.maintained.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          (@APFPaper1.RecordLedger.sufficient.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          (@APFPaper1.RecordLedger.usesToRealize.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@APFPaper5.K1.sourcePartyScore.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@APFPaper5.K1.leastBill.{0, 0, 0}
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@APFPaper1.RecordLedger.wholeResource.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
            (@APFPaper1.RecordLedger.calibration.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
            (@APFPaper1.RecordLedger.maintained.{0, 0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger))
          (@APFPaper1.RecordLedger.maintained.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          (@APFPaper1.RecordLedger.sufficient.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          (@APFPaper1.RecordLedger.usesToRealize.{0, 0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.PaidPair.ledger)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i))
      (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
        Real.semiring
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))))) := by sorry
