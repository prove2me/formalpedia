-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_split
-- name    : Formalism.DworkPowerSeriesWeights.sat_card_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:10.502862+00:00
-- url     : https://prove2.me/theorems/65b223ca-8de8-48aa-9e9d-c34642f1dbaa
-- title:
--   Dwork Power Series Weights: sat card split
-- statement:
--   The Dwork Power Series Weights construction uses the sat card split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L92-L98

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

theorem Formalism.DworkPowerSeriesWeights.sat_card_split {k : ℕ} (sz : Fin k → ℕ) (j : ℕ) :
    (Finset.univ.filter fun i => sz i = j + 1).card + (Finset.univ.filter fun i => j + 1 < sz i).card =
      (Finset.univ.filter fun i => j < sz i).card := by sorry
