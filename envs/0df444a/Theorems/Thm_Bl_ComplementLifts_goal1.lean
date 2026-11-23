-- Prove2me | Theorems.Thm_Bl_ComplementLifts_goal1
-- name    : Bl.ComplementLifts.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:04.781887+00:00
-- url     : https://prove2.me/theorems/729469a2-41fb-4c6d-8158-8296357edd9b
-- title:
--   Complement Lifts: goal1
-- statement:
--   The Complement Lifts construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/ComplementLifts/ComplLift.lean#L29-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/ComplementLifts/ComplLift.lean#L29-L74

import Mathlib
import Definitions.Def_Lemmata_ComplementLifts_ComplLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.ComplementLifts

theorem Bl.ComplementLifts.goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [IsDomain.{u_1} R] [IsPrincipalIdealRing.{u_1} R]
  [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M] (N N' S : Submodule.{u_1, u_2} R M),
  IsCompl.{u_2} N N' →
    ∀ [Module.Finite.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)],
      LE.le.{u_2} S N →
        (∀ (a : R) (x : M),
            Ne.{u_1 + 1} a 0 →
              Membership.mem.{u_2, u_2} S (HSMul.hSMul.{u_1, u_2, u_2} a x) → Membership.mem.{u_2, u_2} S x) →
          Exists.{u_2 + 1} fun (T : Submodule.{u_1, u_2} R M) ↦ IsCompl.{u_2} S T := by sorry
