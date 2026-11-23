-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_oddIndicator_series_family
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.oddIndicator_series_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:24.382116+00:00
-- url     : https://prove2.me/theorems/22236125-4cd0-40b5-8b11-c343475ea732
-- title:
--   Exponential Derivative Inverse: odd Indicator series family
-- statement:
--   The Exponential Derivative Inverse construction uses the odd Indicator series family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L321-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L321-L328

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
variable {K0 : Subfield K} {l : ℕ}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.oddIndicator_series_family : Fam K0 l (s1' (K := K) (d := d)) := by sorry
