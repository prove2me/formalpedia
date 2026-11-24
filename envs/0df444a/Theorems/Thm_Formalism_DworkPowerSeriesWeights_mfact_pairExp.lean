-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_pairExp
-- name    : Formalism.DworkPowerSeriesWeights.mfact_pairExp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:44:04.742139+00:00
-- url     : https://prove2.me/theorems/52153d22-9e55-4787-8ba1-56db70f40047
-- title:
--   Dwork Power Series Weights: mfact pair Exp
-- statement:
--   The Dwork Power Series Weights construction uses the mfact pair Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L38-L42

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

theorem Formalism.DworkPowerSeriesWeights.mfact_pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) :
    mfact (pairExp n) = (∏ i, (n i).factorial) * ∏ i, (n i).factorial := by sorry
