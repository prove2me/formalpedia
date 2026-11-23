-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_subst
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:14.950381+00:00
-- url     : https://prove2.me/theorems/3f2f36a0-0e62-4721-a2c5-91a37fb607a8
-- title:
--   Exponential Derivative Inverse: cong W subst
-- statement:
--   The Exponential Derivative Inverse construction uses the cong W subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L208-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L208-L220

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
variable {N : ℤ}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_subst {σ : Type w} [Finite σ] {w1 : σ → ℤ} {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, HomW w (w1 s) (a s))
    {f : MvPowerSeries σ K} (hf : CongW N w1 f) : CongW N w (MvPowerSeries.subst a f) := by sorry
