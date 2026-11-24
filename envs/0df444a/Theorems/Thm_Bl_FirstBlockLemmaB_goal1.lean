-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaB_goal1
-- name    : Bl.FirstBlockLemmaB.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:16.078927+00:00
-- url     : https://prove2.me/theorems/4e825ab6-11a9-4408-b561-2c673235ac50
-- title:
--   First Block Lemma B: goal1
-- statement:
--   The First Block Lemma B construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaB/Imports.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaB/Imports.lean#L7-L22

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_4
open Bl Bl.FirstBlockLemmaB

theorem Bl.FirstBlockLemmaB.goal1 :
  ∀ {R : Type u_4} [inst : CommRing.{u_4} R] {P Q : Ideal.{u_4} R} [Ideal.IsPrime.{u_4} P],
  LE.le.{u_4} P Q →
    ∀ {x : R},
      Membership.mem.{u_4, u_4} Q x →
        Not (Membership.mem.{u_4, u_4} P x) →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R Q)) 1)
            (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R P)) := by sorry
