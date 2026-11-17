-- Prove2me | Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
-- name    : APFPaper5.K1.ledger_party_score_meets_K1_explicit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:38:54.595554+00:00
-- url     : https://prove2.me/theorems/e55b8a29-a8ba-4525-8703-5beb94b85163
-- title:
--   ledger party score meets K1
-- statement:
--   Result: ledger party score meets K1. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem ledger_party_score_meets_K1 (L : RecordLedger D P Record) (dist : ι → D)
--       (hown : ∀ i, ∃ a, 0 < L.cost a ∧ a ∈ familyNeeds L {dist i} ∧
--         a ∉ familyNeeds L ((Finset.univ.erase i).image dist)) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (ledgerPartyScore L dist)) ∧
--         FaithfulNonnegDiagonal (tableForm (ledgerPartyScore L dist)) (LinearEquiv.refl ℝ (ι → ℝ))
--   ```
--
--   Module context and limits: Nonnegative weights and a positive record unique to each party suffice for a faithful finite table. The record-ledger result obtains those records from the stated B05, LedgerAvailable and earlier LedgerCounted hypotheses. They remain explicit.
--
--   Source scope parameters:
--
--   ```lean
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]
--   variable {D P Record : Type*}
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   variable [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_ledger_party_score:155; pullbacks v39; source SHA-256 19932323ca9bc3929ce337b30dcb27ca42f759b1c4a87a7627abad8aa1f9950c']

import Definitions.Def_APFPaper5_K1_LedgerPartyScore
import Definitions.Def_APFPaper5_K1_LedgerScore
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
import Theorems.Thm_APFPaper1_RecordLedger_maintained_eq_kept
import Theorems.Thm_APFPaper1_RecordLedger_needsFin_subset_of_sufficient
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

theorem APFPaper5.K1.ledger_party_score_meets_K1_explicit :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (dist : ι → D)
  (hown :
    ∀ (i : ι),
      @Exists.{apfNative_u_3 + 1} Record fun (a : Record) =>
        And
          (@LT.lt.{0} NNReal (@Preorder.toLT.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
            (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero))
            (@APFPaper1.RecordLedger.cost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L a))
          (And
            (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
              (@Set.instMembership.{apfNative_u_3} Record)
              (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
                  (@Finset.instSingleton.{apfNative_u_1} D) (dist i)))
              a)
            (Not
              (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
                (@Set.instMembership.{apfNative_u_3} Record)
                (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                  (@Finset.image.{apfNative_u_4, apfNative_u_1} ι D inst_2 dist
                    (@Finset.erase.{apfNative_u_4} ι inst_1 (@Finset.univ.{apfNative_u_4} ι inst) i)))
                a)))),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist))
      (@LinearEquiv.refl.{0, apfNative_u_4} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by sorry
