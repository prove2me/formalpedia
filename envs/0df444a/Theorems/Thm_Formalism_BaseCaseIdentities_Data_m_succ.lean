-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_succ
-- name    : Formalism.BaseCaseIdentities.Data.m_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:58.269506+00:00
-- url     : https://prove2.me/theorems/5b3b02ed-340e-4b29-bb5a-71bdf98fdfc9
-- title:
--   Data: m succ
-- statement:
--   The Data construction uses the m succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L109-L110

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
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
variable {k : Type*} [Field k] {Z C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem Formalism.BaseCaseIdentities.Data.m_succ (s : ℕ) (b : C) : D.m (s + 1) b = MvPowerSeries.C (-(D.l : k)⁻¹) *
    ∑ c, frob D.q (D.m s c) * MvPowerSeries.C (D.g c b) := by sorry
