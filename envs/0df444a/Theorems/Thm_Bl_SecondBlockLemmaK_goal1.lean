-- Prove2me | Theorems.Thm_Bl_SecondBlockLemmaK_goal1
-- name    : Bl.SecondBlockLemmaK.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:05.605461+00:00
-- url     : https://prove2.me/theorems/735524b2-1d11-43c1-9629-546157925ce8
-- title:
--   Second Block Lemma K: goal1
-- statement:
--   The Second Block Lemma K construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasJ/Imports.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasJ/Imports.lean#L5-L37

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasJ_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.SecondBlockLemmaK

theorem Bl.SecondBlockLemmaK.goal1 :
  ∀ {R F X : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : Field.{0} F] [inst_3 : Algebra.{0, 0} R F]
  [IsFractionRing.{0, 0} R F] [inst_5 : AddCommGroup.{0} X] [inst_6 : Module.{0, 0} F X] [inst_7 : Module.{0, 0} R X]
  [IsScalarTower.{0, 0, 0} R F X] (S : Submodule.{0, 0} R X) {x : X},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} F (SetLike.coe.{0, 0} S)) x →
    Exists.{1} fun (d : R) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} S (HSMul.hSMul.{0, 0, 0} d x)) := by sorry
