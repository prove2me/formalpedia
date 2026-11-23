-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_coreL_dot_fintype
-- name    : Formalism.DworkPowerSeriesWeights.coreL_dot_fintype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:10.823803+00:00
-- url     : https://prove2.me/theorems/2173d5c8-964a-4dac-a45e-759daba841b9
-- title:
--   Dwork Power Series Weights: core L dot fintype
-- statement:
--   The Dwork Power Series Weights construction uses the core L dot fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/WeightsAddOverOrbits.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/WeightsAddOverOrbits.lean#L14-L17

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.coreL_dot_fintype {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by sorry
