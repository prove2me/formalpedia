-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_two
-- name    : Formalism.BaseCaseIdentities.Data.wt_two
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:45.120885+00:00
-- url     : https://prove2.me/theorems/e633bae7-9b18-46e6-8050-1da9b72882ba
-- title:
--   Data: wt two
-- statement:
--   The Data construction uses the wt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L81-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L81-L144

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

theorem Formalism.BaseCaseIdentities.Data.wt_two (J : ℕ) (hJK : J ≤ D.K) (c b : C) (hcJ : D.lev c < J) (τ : MvPowerSeries Z k)
    (hν : D.Wt D.top (τ - D.m (D.lev c) c)) :
    D.Wt D.top (MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b) := by sorry
