-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_glue_apply
-- name    : Formalism.DworkPowerSeriesWeights.sat_glue_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:34.016026+00:00
-- url     : https://prove2.me/theorems/ea4fa821-484f-481d-a26e-90836394cec5
-- title:
--   Dwork Power Series Weights: sat glue apply
-- statement:
--   The Dwork Power Series Weights construction uses the sat glue apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L33-L42

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
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
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility

theorem Formalism.DworkPowerSeriesWeights.sat_glue_apply {S τ σ : Type} [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (m : S → τ →₀ ℕ) (s : S) (v : τ) :
    (∑ t, (m t).mapDomain (e t)) (e s v) = m s v := by sorry
