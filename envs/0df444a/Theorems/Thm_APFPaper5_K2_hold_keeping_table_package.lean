-- Prove2me | Theorems.Thm_APFPaper5_K2_hold_keeping_table_package
-- name    : APFPaper5.K2.hold_keeping_table_package
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:40:29.261019+00:00
-- url     : https://prove2.me/theorems/c037f4a1-5d8b-49bb-8887-13ba8e189849
-- title:
--   hold keeping table package
-- statement:
--   Result: hold keeping table package. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem hold_keeping_table_package (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i)
--       (hf : FaithfulNonnegDiagonal (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G)
--         (LinearEquiv.refl ℝ (ι → ℝ)))
--       (sigma : Equiv.Perm ι) (hk : KeepsTable G sigma) : HoldKeepsLedger G sigma
--   ```
--
--   Module context and limits: KeepsTable remains explicit, as do symmetry, faithful diagonal and SourceCounted where used. The author-adopted reading is not a derivation from installed inputs. Inverse permutations and null-combination closure do not establish admitted inverse words or full K2 closure.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uK
--   variable {ι : Type uI}
--   variable [Fintype ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_holds_keep_table:120; pullbacks v39; source SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd']

import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
set_option autoImplicit false
universe apfNative_uI

theorem APFPaper5.K2.hold_keeping_table_package :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] (G : ι → ι → Real)
  (hG : ∀ (i j : ι), @Eq.{1} Real (G i j) (G j i))
  (hf :
    @APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_uI, apfNative_uI} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_uI, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_uI, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_uI, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_uI, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst G)
      (@LinearEquiv.refl.{0, apfNative_uI} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_uI, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_uI, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring))))
  (sigma : Equiv.Perm.{apfNative_uI + 1} ι)
  (hk :
    @APFPaper5.K2.KeepsTable.{apfNative_uI} ι G
      (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
        (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        sigma)),
  @APFPaper5.K2.HoldKeepsLedger.{apfNative_uI} ι inst G sigma := by sorry
