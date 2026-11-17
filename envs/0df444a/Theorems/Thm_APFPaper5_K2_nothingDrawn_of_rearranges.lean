-- Prove2me | Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
-- name    : APFPaper5.K2.nothingDrawn_of_rearranges
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:50:45.418126+00:00
-- url     : https://prove2.me/theorems/7df54687-8369-462b-b757-f9b37bc944f5
-- title:
--   nothingDrawn of rearranges
-- statement:
--   Result: nothingDrawn of rearranges. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem nothingDrawn_of_rearranges {X : Type uX} {D : Type uD} (reads : D → X → Bool) (h : X → X)
--       (sigma : D → D) (flip : D → Bool) (r : RearrangesFamily reads id h sigma flip) :
--       APFB02.NothingDrawn reads h
--   ```
--
--   Module context and limits: The score uses a supplied table and precomposition of classes; side flips do not enter it. KeepsTable is an explicit hypothesis for inverse-as-adjoint and orientation results. The later author reading adopts preservation for holds but does not remove this Lean hypothesis or amend FOUNDATION_INPUTS.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uK
--   variable {ι : Type uI}
--   variable [Fintype ι] [DecidableEq ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_score:82; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

import Definitions.Def_APFPaper5_K2_HoldScore
import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
import Theorems.Thm_APFPaper5_K1_tableForm_markClass
import Theorems.Thm_APFPaper5_K1_table_linearizes
import Theorems.Thm_APFPaper5_K1_nondegenerate_of_faithful_identity
import Theorems.Thm_APFPaper5_K1_orientationForm_zero_of_symm
import Theorems.Thm_APFPaper5_K1_ledgerForm_eq_of_symm
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_symm
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_all_of_K1_with_identity_exchange
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
set_option autoImplicit false
universe apfNative_uX apfNative_uD

theorem APFPaper5.K2.nothingDrawn_of_rearranges :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (h : X → X) (sigma : D → D) (flip : D → Bool)
  (r :
    @APFPaper5.K2.RearrangesFamily.{apfNative_uD, apfNative_uX, apfNative_uD} D X D reads (@id.{apfNative_uD + 1} D) h
      sigma flip),
  @APFB02.NothingDrawn.{apfNative_uX, apfNative_uD} X D reads h := by sorry
