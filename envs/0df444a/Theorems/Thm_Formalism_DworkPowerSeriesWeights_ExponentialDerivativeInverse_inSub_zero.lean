-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_zero
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:35.970349+00:00
-- url     : https://prove2.me/theorems/f99aceb9-aeaf-4ab9-a75b-a876351e2151
-- title:
--   Exponential Derivative Inverse: in Sub zero
-- statement:
--   The Exponential Derivative Inverse construction uses the in Sub zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L26-L27

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_zero : InSub K0 (0 : MvPowerSeries ι K) := by sorry
