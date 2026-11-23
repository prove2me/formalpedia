-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_good_sub
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:11.38293+00:00
-- url     : https://prove2.me/theorems/06ee33cb-6de8-4eab-92db-c50821a41e02
-- title:
--   Exponential Derivative Inverse: good sub
-- statement:
--   The Exponential Derivative Inverse construction uses the good sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L283-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L283-L285

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
variable {K : Type u} [NormedField K] {d : ℕ}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_sub {K0 : Subfield K} {N : ℤ} {w : V2 d → ℤ} {f g : MvPowerSeries (V2 d) K}
    (hf : Good K0 N w f) (hg : Good K0 N w g) : Good K0 N w (f - g) := by sorry
