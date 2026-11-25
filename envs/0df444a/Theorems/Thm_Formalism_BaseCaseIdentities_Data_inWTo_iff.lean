-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_inWTo_iff
-- name    : Formalism.BaseCaseIdentities.Data.inWTo_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:01.217593+00:00
-- url     : https://prove2.me/theorems/66b9dc5a-eee4-453c-b545-c5f172e24911
-- title:
--   Data: in WTo iff
-- statement:
--   The Data construction uses the in WTo iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L18-L31

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

theorem Formalism.BaseCaseIdentities.Data.inWTo_iff (J : ℕ) (t : C → MvPowerSeries Z k) :
    D.InWTo J t ↔ ∀ c, D.Wt D.top (t c - D.mu J c) := by sorry
