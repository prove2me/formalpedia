-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_step
-- name    : Formalism.BaseCaseIdentities.Data.step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:39.022476+00:00
-- url     : https://prove2.me/theorems/209e56cc-640f-45ef-9e23-76c1f9a5de09
-- title:
--   Data: step
-- statement:
--   The Data construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L202-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean#L202-L217

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

theorem Formalism.BaseCaseIdentities.Data.step (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (hnc : NoConst t) (ht : D.InWTo J t) : D.InWTo (min (J + 1) D.K) (D.Psi t) := by sorry
