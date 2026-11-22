-- Prove2me | Theorems.Thm_APFPaper5_K2_isHold_keeps_ledger
-- name    : APFPaper5.K2.isHold_keeps_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:49:48.026283+00:00
-- url     : https://prove2.me/theorems/a14a1b12-7305-4065-beba-ec23466c8b80
-- title:
--   isHold keeps ledger
-- statement:
--   Scope and conditions: Identity and composition preserve IsHold. With the complete list and every combination of readings held, a hold leaves every combination available; a rearrangement leaving all combinations available has an injective index map. Preserving the ledger additionally assumes a symmetric table and a faithful nonnegative diagonal. NothingDrawn and the reading conclusions do not supply an executable word, raw-state inverse, or physical identification of this hold predicate.
--
--   Exact source statement:
--
--   theorem isHold_keeps_ledger {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
--       (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i)
--       (hf : FaithfulNonnegDiagonal (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G)
--         (LinearEquiv.refl ℝ (ι → ℝ)))
--       (h : X → X) (sigma : Equiv.Perm ι) (flip : ι → Bool) (hh : IsHold reads dist G h sigma flip) :
--       HoldKeepsLedger G sigma
--
--   Source parameters:
--
--   universe uI uX uD
--   variable {ι : Type uI}
--   variable [Fintype ι]
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_as_defined:238; USB pullbacks v58 batch B; SHA-256 6e82637a94bacb0c916dc97d59cf5372b7d8e3e65518f925ad3b71d60d94e855']

import Definitions.Def_APFPaper5_K2_Hold
import Definitions.Def_APFB02_EachTakesBothSides
import Definitions.Def_APFB02_HoldOnDistinctions
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
import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Theorems.Thm_APFPaper5_K2_keepsTable_id
import Theorems.Thm_APFPaper5_K2_keepsTable_comp
import Theorems.Thm_APFPaper5_K2_keepsTable_symm
import Theorems.Thm_APFPaper5_K2_hold_keeps_cost
import Theorems.Thm_APFPaper5_K2_holdScoreNull_before
import Theorems.Thm_APFPaper5_K2_holdScoreNull_after_of_keeps
import Theorems.Thm_APFPaper5_K2_holdScoreNull_reverse_of_keeps
import Theorems.Thm_APFPaper5_K2_hold_keeping_table_package
import Theorems.Thm_APFPaper5_K2_source_counted_hold_package
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_uI apfNative_uX apfNative_uD

theorem APFPaper5.K2.isHold_keeps_ledger :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] {X : Type apfNative_uX} {D : Type apfNative_uD}
  (reads : D → X → Bool) (dist : ι → D) (G : ι → ι → Real) (hG : ∀ (i j : ι), @Eq.{1} Real (G i j) (G j i))
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
  (h : X → X) (sigma : Equiv.Perm.{apfNative_uI + 1} ι) (flip : ι → Bool)
  (hh : @APFPaper5.K2.IsHold.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist G h sigma flip),
  @APFPaper5.K2.HoldKeepsLedger.{apfNative_uI} ι inst G sigma := by sorry
