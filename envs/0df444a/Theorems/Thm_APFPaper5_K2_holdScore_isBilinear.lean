-- Prove2me | Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
-- name    : APFPaper5.K2.holdScore_isBilinear
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:47:13.90804+00:00
-- url     : https://prove2.me/theorems/72f84f0c-1234-45b2-af30-fb4ec27b179a
-- title:
--   holdScore isBilinear
-- statement:
--   Result: holdScore isBilinear. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   omit [DecidableEq ι] in
--   theorem holdScore_isBilinear (G : ι → ι → ℝ) (sigma : ι → ι) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (holdScore G sigma)
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
--   ['Theorems.Thm_APFPaper5_K2_hold_score:133; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

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

theorem APFPaper5.K2.holdScore_isBilinear :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] (G : ι → ι → Real) (sigma : ι → ι),
  @APFPaper5.K1.IsBilinear.{apfNative_uI, apfNative_uI} (ι → Real) (ι → Real)
    (@Pi.addCommGroup.{apfNative_uI, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@Pi.Function.module.{apfNative_uI, 0, 0} ι Real Real Real.semiring
      (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{apfNative_uI, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@Pi.Function.module.{apfNative_uI, 0, 0} ι Real Real Real.semiring
      (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G sigma) := by sorry
