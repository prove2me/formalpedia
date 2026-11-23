-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_prod_monomial
-- name    : Formalism.DworkPowerSeriesWeights.sat_prod_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:39.819047+00:00
-- url     : https://prove2.me/theorems/8862f016-f127-4f09-95cb-5568b7202173
-- title:
--   Dwork Power Series Weights: sat prod monomial
-- statement:
--   The Dwork Power Series Weights construction uses the sat prod monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L44-L49

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

theorem Formalism.DworkPowerSeriesWeights.sat_prod_monomial {R α σ : Type} [CommSemiring R] (s : Finset α) (a : α → σ →₀ ℕ) (c : α → R) :
    ∏ i ∈ s, monomial (a i) (c i) = monomial (∑ i ∈ s, a i) (∏ i ∈ s, c i) := by sorry
