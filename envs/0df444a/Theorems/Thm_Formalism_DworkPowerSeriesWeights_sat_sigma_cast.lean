-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_sigma_cast
-- name    : Formalism.DworkPowerSeriesWeights.sat_sigma_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:26.914199+00:00
-- url     : https://prove2.me/theorems/2f462589-a3a9-43f6-ae4d-17251cb5228e
-- title:
--   Dwork Power Series Weights: sat sigma cast
-- statement:
--   The Dwork Power Series Weights construction uses the sat sigma cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L127-L129

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

theorem Formalism.DworkPowerSeriesWeights.sat_sigma_cast {r a b : ℕ} (h : a = b) (I : Fin b → Fin r) :
    (⟨a, fun i => I (Fin.cast h i)⟩ : (j : ℕ) × (Fin j → Fin r)) = ⟨b, I⟩ := by sorry
