-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPair
-- name    : Formalism.DworkPowerSeriesWeights.spPair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:44.2281+00:00
-- url     : https://prove2.me/theorems/1eef9450-31df-4874-ac89-92d2806ef49e
-- title:
--   Dwork Power Series Weights: sp Pair
-- statement:
--   The Dwork Power Series Weights construction uses the sp Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L247-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L247-L283

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

theorem Formalism.DworkPowerSeriesWeights.spPair (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      ((∑ k, MvPowerSeries.C (N (lt i) k) * MvPowerSeries.X k) ^ a *
        (∑ k, MvPowerSeries.C (N (lt j) k) * MvPowerSeries.X k) ^ b) =
      N (lt i) i ^ a * N (lt j) j ^ b := by sorry
