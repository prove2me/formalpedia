-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_prod
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:16.999017+00:00
-- url     : https://prove2.me/theorems/3a9604ce-15b3-4862-be6e-d2dedd7bc97d
-- title:
--   Exponential Derivative Inverse: hom W prod
-- statement:
--   The Exponential Derivative Inverse construction uses the hom W prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L174-L176

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_prod {α : Type w} (s : Finset α) (c : α → ℤ) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, HomW w (c i) (F i)) : HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by sorry
