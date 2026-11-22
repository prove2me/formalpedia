-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_mem_invOn
-- name    : Formalism.DworkPowerSeriesWeights.mem_invOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:58.754005+00:00
-- url     : https://prove2.me/theorems/e237775d-dbd0-4ee8-ba2b-a547e0f5823e
-- title:
--   Dwork Power Series Weights: mem inv On
-- statement:
--   The Dwork Power Series Weights construction uses the mem inv On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L162-L164

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}

theorem Formalism.DworkPowerSeriesWeights.mem_invOn {s : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ invOn s ↔ σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i := by sorry
