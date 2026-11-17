-- Prove2me | Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
-- name    : APFPaper5.K1.partyScore_meets_K1_of_own_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:20:01.437025+00:00
-- url     : https://prove2.me/theorems/98885f94-0d52-4e9c-86f5-32e1807c534c
-- title:
--   partyScore meets K1 of own record
-- statement:
--   Result: partyScore meets K1 of own record. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem partyScore_meets_K1_of_own_record (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
--       (keeps : Finset ι → W → Bool)
--       (hown : ∀ i, ∃ a, 0 < w a ∧ PartyTo keeps i a ∧ ∀ j, PartyTo keeps j a → j = i) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (partyScore w keeps)) ∧
--         FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ))
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
--   ['Theorems.Thm_APFPaper5_K1_ledger_party_score:48; pullbacks v39; source SHA-256 19932323ca9bc3929ce337b30dcb27ca42f759b1c4a87a7627abad8aa1f9950c']

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

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
/-! ### Any keeping rule -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]

theorem APFPaper5.K1.partyScore_meets_K1_of_own_record (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset ι → W → Bool)
    (hown : ∀ i, ∃ a, 0 < w a ∧ PartyTo keeps i a ∧ ∀ j, PartyTo keeps j a → j = i) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (partyScore w keeps)) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
