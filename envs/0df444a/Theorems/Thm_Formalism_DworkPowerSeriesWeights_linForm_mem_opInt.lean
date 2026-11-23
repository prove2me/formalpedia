-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_linForm_mem_opInt
-- name    : Formalism.DworkPowerSeriesWeights.linForm_mem_opInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:37.772799+00:00
-- url     : https://prove2.me/theorems/37bf5029-e318-4b6c-9aba-5fbec264a70c
-- title:
--   Dwork Power Series Weights: lin Form mem op Int
-- statement:
--   The Dwork Power Series Weights construction uses the lin Form mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/IntegralOperatorsOnJets.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/IntegralOperatorsOnJets.lean#L21-L29

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
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

theorem Formalism.DworkPowerSeriesWeights.linForm_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (L : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1) : linForm L ∈ opInt K ι := by sorry
