-- Prove2me | Theorems.Thm_APFPaper5_K2_source_counted_hold_package
-- name    : APFPaper5.K2.source_counted_hold_package
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:40:23.673717+00:00
-- url     : https://prove2.me/theorems/222367fc-725e-4325-9fd0-45d0a7294f9b
-- title:
--   source counted hold package
-- statement:
--   Result: source counted hold package. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem source_counted_hold_package (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a) (wholeResource : P → R)
--       (calibration : R → NNReal) (maintained : P → Set Record)
--       (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
--       (tested : D → Prop) (C : ℝ) (dist : ι' → D)
--       (h : SourceCounted w wholeResource calibration maintained sufficient usesToRealize tested C dist)
--       (sigma : Equiv.Perm ι')
--       (hk : KeepsTable (sourcePartyScore w maintained sufficient usesToRealize dist) sigma) :
--       HoldKeepsLedger (sourcePartyScore w maintained sufficient usesToRealize dist) sigma
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
--   ['Theorems.Thm_APFPaper5_K2_holds_keep_table:141; pullbacks v39; source SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5

theorem APFPaper5.K2.source_counted_hold_package :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  {ι' : Type apfNative_u_5} [inst : Fintype.{apfNative_u_5} ι'] [inst_1 : DecidableEq.{apfNative_u_5 + 1} ι']
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_4} Record] (w : Record → Real)
  (hw :
    ∀ (a : Record),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w a))
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (tested : D → Prop) (C : Real) (dist : ι' → D)
  (h :
    @APFPaper5.K1.SourceCounted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} D P R Record
      ι' inst inst_1 inst_2 w wholeResource calibration maintained sufficient usesToRealize tested C dist)
  (sigma : Equiv.Perm.{apfNative_u_5 + 1} ι')
  (hk :
    @APFPaper5.K2.KeepsTable.{apfNative_u_5} ι'
      (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι' inst
        inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)
      (@DFunLike.coe.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1} (Equiv.Perm.{apfNative_u_5 + 1} ι') ι'
        (fun (x : ι') => ι')
        (@EquivLike.toFunLike.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1}
          (Equiv.Perm.{apfNative_u_5 + 1} ι') ι' ι' (@Equiv.instEquivLike.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι'))
        sigma)),
  @APFPaper5.K2.HoldKeepsLedger.{apfNative_u_5} ι' inst
    (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι' inst
      inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)
    sigma := by sorry
