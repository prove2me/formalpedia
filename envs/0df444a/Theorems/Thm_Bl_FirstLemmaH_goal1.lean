-- Prove2me | Theorems.Thm_Bl_FirstLemmaH_goal1
-- name    : Bl.FirstLemmaH.goal1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:22.14036+00:00
-- url     : https://prove2.me/theorems/633530cc-dddb-44f3-985a-017e9c15bbc6
-- title:
--   First Lemma H: goal1
-- statement:
--   The First Lemma H construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaH.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaH.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaH

theorem Bl.FirstLemmaH.goal1 :
  ∀ {A : Type} (W : Submodule.{0, 0} Complex (A → Complex)),
  FiniteDimensional.{0, 0} Complex (Subtype.{1} fun (x : A → Complex) ↦ Membership.mem.{0, 0} W x) →
    Exists.{1} fun (S : Finset.{0} A) ↦
      ∀ (w : A → Complex),
        Membership.mem.{0, 0} W w → (∀ (a : A), Membership.mem.{0, 0} S a → Eq.{1} (w a) 0) → Eq.{1} w 0 := by sorry
