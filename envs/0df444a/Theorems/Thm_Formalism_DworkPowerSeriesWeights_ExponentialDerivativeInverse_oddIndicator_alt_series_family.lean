-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_oddIndicator_alt_series_family
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.oddIndicator_alt_series_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:13.407804+00:00
-- url     : https://prove2.me/theorems/68e498ac-ab18-4e0e-b059-956a68212ced
-- title:
--   Exponential Derivative Inverse: odd Indicator alt series family
-- statement:
--   The Exponential Derivative Inverse construction uses the odd Indicator alt series family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L305-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L305-L312

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.oddIndicator_alt_series_family : Fam K0 l (s1 (K := K) (d := d)) := by sorry
