-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_one
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:32.854861+00:00
-- url     : https://prove2.me/theorems/5778353b-e3c3-4881-8f88-bc931ce535a2
-- title:
--   Exponential Derivative Inverse: in Sub one
-- statement:
--   The Exponential Derivative Inverse construction uses the in Sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L29-L35

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
variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_one : InSub K0 (1 : MvPowerSeries ι K) := by sorry
