-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_mul
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:14.516257+00:00
-- url     : https://prove2.me/theorems/a5de9e93-4c9a-4eda-822f-de14465133ba
-- title:
--   Exponential Derivative Inverse: hom W mul
-- statement:
--   The Exponential Derivative Inverse construction uses the hom W mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L155-L162

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_mul {c c' : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c' g) :
    HomW w (c + c') (f * g) := by sorry
