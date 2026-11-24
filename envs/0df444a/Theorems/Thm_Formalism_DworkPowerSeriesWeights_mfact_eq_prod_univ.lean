-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_eq_prod_univ
-- name    : Formalism.DworkPowerSeriesWeights.mfact_eq_prod_univ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:43.724526+00:00
-- url     : https://prove2.me/theorems/a2a9020b-b2bf-4b52-a777-301ac5da3de2
-- title:
--   Dwork Power Series Weights: mfact eq prod univ
-- statement:
--   The Dwork Power Series Weights construction uses the mfact eq prod univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L13-L16

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
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

theorem Formalism.DworkPowerSeriesWeights.mfact_eq_prod_univ {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) :
    mfact κ = ∏ x, (κ x).factorial := by sorry
