-- Prove2me | Theorems.Thm_APFPaper5_K2_heldAfter_smul
-- name    : APFPaper5.K2.heldAfter_smul
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:41:22.050409+00:00
-- url     : https://prove2.me/theorems/5afbd587-bbf2-4784-ae70-774096e3b99e
-- title:
--   heldAfter smul
-- statement:
--   Result: heldAfter smul. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem heldAfter_smul (sigma : ι → ι) (r : ℝ) (x : ι → ℝ) :
--       heldAfter sigma (r • x) = r • heldAfter sigma x
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
--   ['Theorems.Thm_APFPaper5_K2_hold_score:105; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

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
universe apfNative_uI

theorem APFPaper5.K2.heldAfter_smul :
∀ {ι : Type apfNative_uI} (sigma : ι → ι) (r : Real) (x : ι → Real),
  @Eq.{apfNative_uI + 1} (ι → Real)
    (@APFPaper5.K2.heldAfter.{apfNative_uI} ι sigma
      (@HSMul.hSMul.{0, apfNative_uI, apfNative_uI} Real (ι → Real) (ι → Real)
        (@instHSMul.{0, apfNative_uI} Real (ι → Real)
          (@Function.hasSMul.{apfNative_uI, 0, 0} ι Real Real (@instSMulOfMul.{0} Real Real.instMul)))
        r x))
    (@HSMul.hSMul.{0, apfNative_uI, apfNative_uI} Real (ι → Real) (ι → Real)
      (@instHSMul.{0, apfNative_uI} Real (ι → Real)
        (@Function.hasSMul.{apfNative_uI, 0, 0} ι Real Real (@instSMulOfMul.{0} Real Real.instMul)))
      r (@APFPaper5.K2.heldAfter.{apfNative_uI} ι sigma x)) := by sorry
