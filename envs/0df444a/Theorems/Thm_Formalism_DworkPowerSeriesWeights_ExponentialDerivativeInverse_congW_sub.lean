-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_sub
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:04.177699+00:00
-- url     : https://prove2.me/theorems/0cab39bb-47af-44a3-8f2a-da0db252799b
-- title:
--   Exponential Derivative Inverse: cong W sub
-- statement:
--   The Exponential Derivative Inverse construction uses the cong W sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L180-L186

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
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
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {ι : Type v}
variable {w : ι → ℤ}
variable {N : ℤ}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_sub {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f - g) := by sorry
