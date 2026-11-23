-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_finsum_mem_sub
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.finsum_mem_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:17.019805+00:00
-- url     : https://prove2.me/theorems/b76d7c8e-e977-42fd-b666-e7aa4b812bce
-- title:
--   Exponential Derivative Inverse: finsum mem sub
-- statement:
--   The Exponential Derivative Inverse construction uses the finsum mem sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L67-L73

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.finsum_mem_sub {α : Type w} (g : α → K) (h : ∀ i, g i ∈ K0) : ∑ᶠ i, g i ∈ K0 := by sorry
