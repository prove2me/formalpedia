-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_closed
-- name    : Formalism.BaseCaseIdentities.Data.m_closed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:20.89848+00:00
-- url     : https://prove2.me/theorems/a8c0ff89-7347-455c-b817-1e696a4e82ba
-- title:
--   Data: m closed
-- statement:
--   The Data construction uses the m closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L149-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L149-L216

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.BaseCaseIdentities.Data.m_closed (s : ℕ) (hs : s < D.K) :
    ∃ P : C → Z → k, (∀ c d, 0 ≤ D.v (P c d)) ∧ (∀ c, D.lev c ≠ s → ∀ d, P c d = 0) ∧
    ∀ c, D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P c d) * X d ^ (D.q ^ s) := by sorry
