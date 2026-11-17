-- Prove2me | Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
-- name    : APFPaper5.K1.memberNeeds_subset_familyNeeds_explicit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:42:05.83483+00:00
-- url     : https://prove2.me/theorems/28a3c75e-d65b-4904-b6d6-74ec9e1bf55d
-- title:
--   memberNeeds subset familyNeeds
-- statement:
--   Result: memberNeeds subset familyNeeds. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem memberNeeds_subset_familyNeeds (L : RecordLedger D P Record) {S : Finset D} {d : D}
--       (hd : d ∈ S) {a : Record} (ha : a ∈ L.needsFin d) : a ∈ familyNeeds L S
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
--   ['Theorems.Thm_APFPaper5_K1_ledger_party_score:91; pullbacks v39; source SHA-256 19932323ca9bc3929ce337b30dcb27ca42f759b1c4a87a7627abad8aa1f9950c']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_3

theorem APFPaper5.K1.memberNeeds_subset_familyNeeds_explicit :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) {S : Finset.{apfNative_u_1} D}
  {d : D}
  (hd :
    @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
      (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
        (@Finset.instSetLike.{apfNative_u_1} D))
      S d)
  {a : Record}
  (ha :
    @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Finset.{apfNative_u_3} Record)
      (@SetLike.instMembership.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
        (@Finset.instSetLike.{apfNative_u_3} Record))
      (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L d) a),
  @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
    (@Set.instMembership.{apfNative_u_3} Record)
    (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L S) a := by sorry
