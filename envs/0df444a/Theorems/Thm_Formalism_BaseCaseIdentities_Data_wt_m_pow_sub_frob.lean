-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m_pow_sub_frob
-- name    : Formalism.BaseCaseIdentities.Data.wt_m_pow_sub_frob
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:41.446194+00:00
-- url     : https://prove2.me/theorems/57fe0c07-c037-41b2-967c-9b8034a64332
-- title:
--   Data: wt m pow sub frob
-- statement:
--   The Data construction uses the wt m pow sub frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L234-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L234-L248

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

theorem Formalism.BaseCaseIdentities.Data.wt_m_pow_sub_frob {s : ℕ} (hs : s < D.K) (c : C) :
    D.Wt (1 + qnum D.l * rho D.l) (D.m s c ^ D.q - frob D.q (D.m s c)) := by sorry
