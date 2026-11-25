-- Prove2me | Theorems.Thm_Bl_FirstLemmaG_goal1
-- name    : Bl.FirstLemmaG.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:53.145961+00:00
-- url     : https://prove2.me/theorems/11924303-7304-5fef-aa23-6dbae7062724
-- title:
--   First Lemma G: goal1
-- statement:
--   The First Lemma G construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaG.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaG.lean#L8-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.FirstLemmaG

theorem Bl.FirstLemmaG.goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries.{u_1, 0} σ (PadicComplex p)} (i : σ),
  PI.JetsPhW.IntegralMv.{u_1} F →
    PI.JetsPhW.IntegralMv.{u_1}
      (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (MvPowerSeries.pderiv.{u_1, 0} (PadicComplex p) i) F) := by sorry
