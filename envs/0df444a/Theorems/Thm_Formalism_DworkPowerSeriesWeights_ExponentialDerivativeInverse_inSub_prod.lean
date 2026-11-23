-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_prod
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:13.731187+00:00
-- url     : https://prove2.me/theorems/ffc24c16-d863-42cf-8e05-d38f81985954
-- title:
--   Exponential Derivative Inverse: in Sub prod
-- statement:
--   The Exponential Derivative Inverse construction uses the in Sub prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L57-L65

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_prod {α : Type w} (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, InSub K0 (F i)) : InSub K0 (∏ i ∈ s, F i) := by sorry
