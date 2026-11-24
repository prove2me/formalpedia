-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_slope_bound_saturation
-- name    : Formalism.DworkPowerSeriesWeights.slope_bound_saturation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:55.122604+00:00
-- url     : https://prove2.me/theorems/7320a426-eae2-4a23-8c03-606bd66b79e2
-- title:
--   Dwork Power Series Weights: slope bound saturation
-- statement:
--   The Dwork Power Series Weights construction uses the slope bound saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L202-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L202-L294

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

theorem Formalism.DworkPowerSeriesWeights.slope_bound_saturation : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (d N0 : ℕ) [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0), SBSat K colN p hp := by sorry
