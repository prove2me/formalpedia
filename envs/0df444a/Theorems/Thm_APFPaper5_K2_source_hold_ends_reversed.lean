-- Prove2me | Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
-- name    : APFPaper5.K2.source_hold_ends_reversed
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:00:20.817417+00:00
-- url     : https://prove2.me/theorems/eb975b07-b9c7-4500-b669-19d3180d0169
-- title:
--   source hold ends reversed
-- statement:
--   Result: source hold ends reversed. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem source_hold_ends_reversed (w : Record → ℝ) (maintained : P → Set Record)
--       (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
--       (dist : ι' → D) (sigma : Equiv.Perm ι')
--       (hk : KeepsTable (sourcePartyScore w maintained sufficient usesToRealize dist) sigma)
--       (x y : ι' → ℝ) :
--       holdScore (sourcePartyScore w maintained sufficient usesToRealize dist) sigma x y =
--         holdScore (sourcePartyScore w maintained sufficient usesToRealize dist) sigma.symm y x
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
--   ['Theorems.Thm_APFPaper5_K2_hold_score:265; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_4 apfNative_u_5

theorem APFPaper5.K2.source_hold_ends_reversed :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_4} {ι' : Type apfNative_u_5}
  [inst : Fintype.{apfNative_u_5} ι'] [inst_1 : DecidableEq.{apfNative_u_5 + 1} ι']
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_4} Record] (w : Record → Real)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (dist : ι' → D)
  (sigma : Equiv.Perm.{apfNative_u_5 + 1} ι')
  (hk :
    @APFPaper5.K2.KeepsTable.{apfNative_u_5} ι'
      (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι' inst
        inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)
      (@DFunLike.coe.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1} (Equiv.Perm.{apfNative_u_5 + 1} ι') ι'
        (fun (x : ι') => ι')
        (@EquivLike.toFunLike.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1}
          (Equiv.Perm.{apfNative_u_5 + 1} ι') ι' ι' (@Equiv.instEquivLike.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι'))
        sigma))
  (x y : ι' → Real),
  @Eq.{1} Real
    (@APFPaper5.K2.holdScore.{apfNative_u_5} ι' inst
      (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι' inst
        inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)
      (@DFunLike.coe.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1} (Equiv.Perm.{apfNative_u_5 + 1} ι') ι'
        (fun (x : ι') => ι')
        (@EquivLike.toFunLike.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1}
          (Equiv.Perm.{apfNative_u_5 + 1} ι') ι' ι' (@Equiv.instEquivLike.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι'))
        sigma)
      x y)
    (@APFPaper5.K2.holdScore.{apfNative_u_5} ι' inst
      (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι' inst
        inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)
      (@DFunLike.coe.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1}
        (Equiv.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι') ι' (fun (x : ι') => ι')
        (@EquivLike.toFunLike.{apfNative_u_5 + 1, apfNative_u_5 + 1, apfNative_u_5 + 1}
          (Equiv.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι') ι' ι'
          (@Equiv.instEquivLike.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι'))
        (@Equiv.symm.{apfNative_u_5 + 1, apfNative_u_5 + 1} ι' ι' sigma))
      y x) := by sorry
