-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_add
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.wsum_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:51.237272+00:00
-- url     : https://prove2.me/theorems/d52b13f2-d673-42b3-86fb-81d8eb29e52a
-- title:
--   Exponential Derivative Inverse: wsum add
-- statement:
--   The Exponential Derivative Inverse construction uses the wsum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L104-L107

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.wsum_add (w : ι → ℤ) (m n : ι →₀ ℕ) : wsum w (m + n) = wsum w m + wsum w n := by sorry
