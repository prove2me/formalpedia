-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPow_single
-- name    : Formalism.DworkPowerSeriesWeights.spPow_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:00.145594+00:00
-- url     : https://prove2.me/theorems/2934476f-1a92-4a44-bc80-864e3d19f13b
-- title:
--   Dwork Power Series Weights: sp Pow single
-- statement:
--   The Dwork Power Series Weights construction uses the sp Pow single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L209-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L209-L245

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
variable (lt : ι → σ) (N : σ → ι → R)
variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN

theorem Formalism.DworkPowerSeriesWeights.spPow_single (s : σ) (i : ι) (a : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i a)
      ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ a) = N s i ^ a := by sorry
