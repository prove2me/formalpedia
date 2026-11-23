-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_pow
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:22.46629+00:00
-- url     : https://prove2.me/theorems/accf1b79-0e36-4db4-8e06-83f9cb69d856
-- title:
--   Exponential Derivative Inverse: hom W pow
-- statement:
--   The Exponential Derivative Inverse construction uses the hom W pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L164-L172

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

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_pow {c : ℤ} {f : MvPowerSeries ι K} (hf : HomW w c f) (k : ℕ) :
    HomW w (k * c) (f ^ k) := by sorry
