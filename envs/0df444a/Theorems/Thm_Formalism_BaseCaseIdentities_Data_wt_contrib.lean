-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_contrib
-- name    : Formalism.BaseCaseIdentities.Data.wt_contrib
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:42.771635+00:00
-- url     : https://prove2.me/theorems/d14a8dd9-c8c4-4165-944c-b8527dde32b7
-- title:
--   Data: wt contrib
-- statement:
--   The Data construction uses the wt contrib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L146-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L146-L200

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

theorem Formalism.BaseCaseIdentities.Data.wt_contrib (J : ℕ) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (ht : ∀ c, D.Wt D.top (t c - D.mu J c)) (N : ℕ) (hN : 2 ≤ N) (c b : C) :
    D.Wt D.top
      (∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by sorry
