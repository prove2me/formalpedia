-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_min_sum_le
-- name    : Formalism.DworkPowerSeriesWeights.min_sum_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:47.374622+00:00
-- url     : https://prove2.me/theorems/f9e72d1a-49d9-4af3-9845-27b6d7e2a982
-- title:
--   Dwork Power Series Weights: min sum le
-- statement:
--   The Dwork Power Series Weights construction uses the min sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L183-L185

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
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
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.min_sum_le {σ : Type} [Fintype σ] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) ≤ ∑ y, u y := by sorry
