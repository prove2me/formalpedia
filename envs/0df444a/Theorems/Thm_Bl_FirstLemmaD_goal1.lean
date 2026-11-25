-- Prove2me | Theorems.Thm_Bl_FirstLemmaD_goal1
-- name    : Bl.FirstLemmaD.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:19.082184+00:00
-- url     : https://prove2.me/theorems/7f9a1183-5d65-46d1-85d3-c60ecee6754a
-- title:
--   First Lemma D: goal1
-- statement:
--   The First Lemma D construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaD.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaD.lean#L5-L23

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaD

theorem Bl.FirstLemmaD.goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F)),
  Exists.{1} fun (p : Nat) ↦
    And (Nat.Prime p) (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} v) (Nat.cast.{0} p)) := by sorry
