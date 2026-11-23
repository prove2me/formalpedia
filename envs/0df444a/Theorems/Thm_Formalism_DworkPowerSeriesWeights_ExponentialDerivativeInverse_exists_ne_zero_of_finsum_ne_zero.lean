-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_exists_ne_zero_of_finsum_ne_zero
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.exists_ne_zero_of_finsum_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:13.779846+00:00
-- url     : https://prove2.me/theorems/2b354daa-a47d-4935-a59a-ea33bae69485
-- title:
--   Exponential Derivative Inverse: exists ne zero of finsum ne zero
-- statement:
--   The Exponential Derivative Inverse construction uses the exists ne zero of finsum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L120-L124

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.exists_ne_zero_of_finsum_ne_zero {α : Type w} {g : α → K} (h : ∑ᶠ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 := by sorry
