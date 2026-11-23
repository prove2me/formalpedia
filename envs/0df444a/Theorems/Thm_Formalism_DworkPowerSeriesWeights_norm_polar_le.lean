-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_polar_le
-- name    : Formalism.DworkPowerSeriesWeights.norm_polar_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:37.078545+00:00
-- url     : https://prove2.me/theorems/e89fcb10-8251-48ad-bac8-c0695e1d0135
-- title:
--   Dwork Power Series Weights: norm polar le
-- statement:
--   The Dwork Power Series Weights construction uses the norm polar le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/IntegralOperatorsOnJets.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/IntegralOperatorsOnJets.lean#L31-L43

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

theorem Formalism.DworkPowerSeriesWeights.norm_polar_le {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (c : ι → ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1) (L L' : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1)
    (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by sorry
