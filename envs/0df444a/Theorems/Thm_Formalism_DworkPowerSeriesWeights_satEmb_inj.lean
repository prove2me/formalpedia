-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_satEmb_inj
-- name    : Formalism.DworkPowerSeriesWeights.satEmb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:47.400923+00:00
-- url     : https://prove2.me/theorems/b6b8868d-0f42-48ad-b15b-5f14edab9b8c
-- title:
--   Dwork Power Series Weights: sat Emb inj
-- statement:
--   The Dwork Power Series Weights construction uses the sat Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L173-L176

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

theorem Formalism.DworkPowerSeriesWeights.satEmb_inj (d N0 : ℕ) (s t : ZMod d) (v w : Fin N0 × Fin N0) (h : satEmb d N0 s v = satEmb d N0 t w) :
    s = t ∧ v = w := by sorry
