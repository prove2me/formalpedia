-- Prove2me | Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
-- name    : APFPaper5.K2.reverse_is_inverse_of_keeps
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:55:17.873132+00:00
-- url     : https://prove2.me/theorems/c008fc98-6d0e-41b7-b931-5e09b165b071
-- title:
--   reverse is inverse of keeps
-- statement:
--   Result: reverse is inverse of keeps. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   omit [DecidableEq ι] in
--   theorem reverse_is_inverse_of_keeps (G : ι → ι → ℝ) (sigma : Equiv.Perm ι)
--       (hk : KeepsTable G sigma) (x y : ι → ℝ) :
--       holdScore G sigma x y = tableForm G x (heldAfter sigma.symm y)
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
--   ['Theorems.Thm_APFPaper5_K2_hold_score:163; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

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

theorem APFPaper5.K2.reverse_is_inverse_of_keeps :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] (G : ι → ι → Real) (sigma : Equiv.Perm.{apfNative_uI + 1} ι)
  (hk :
    @APFPaper5.K2.KeepsTable.{apfNative_uI} ι G
      (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
        (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        sigma))
  (x y : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G
      (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
        (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        sigma)
      x y)
    (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst G x
      (@APFPaper5.K2.heldAfter.{apfNative_uI} ι
        (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
          (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι (fun (x : ι) => ι)
          (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
            (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι ι
            (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
          (@Equiv.symm.{apfNative_uI + 1, apfNative_uI + 1} ι ι sigma))
        y)) := by sorry
