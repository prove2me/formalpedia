-- Prove2me | Theorems.Thm_Bl_FirstLemmaK_goal1
-- name    : Bl.FirstLemmaK.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:04.726816+00:00
-- url     : https://prove2.me/theorems/9b685543-69bf-4e8c-bb59-07c1fea84a39
-- title:
--   First Lemma K: goal1
-- statement:
--   The First Lemma K construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaK.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaK.lean#L5-L29

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaK

theorem Bl.FirstLemmaK.goal1 :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by sorry
