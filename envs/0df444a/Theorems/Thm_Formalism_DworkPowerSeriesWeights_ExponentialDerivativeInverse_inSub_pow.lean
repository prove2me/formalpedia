-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_pow
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:36.181669+00:00
-- url     : https://prove2.me/theorems/d72485fa-6b3d-4a65-9ea4-71117a40c1a2
-- title:
--   Exponential Derivative Inverse: in Sub pow
-- statement:
--   The Exponential Derivative Inverse construction uses the in Sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L52-L55

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_pow {f : MvPowerSeries ι K} (hf : InSub K0 f) (k : ℕ) : InSub K0 (f ^ k) := by sorry
