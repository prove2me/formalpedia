-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spProd_ldeg
-- name    : Formalism.DworkPowerSeriesWeights.spProd_ldeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:47.162985+00:00
-- url     : https://prove2.me/theorems/4977abc3-1cb1-48b3-a007-ff92ca95202a
-- title:
--   Dwork Power Series Weights: sp Prod ldeg
-- statement:
--   The Dwork Power Series Weights construction uses the sp Prod ldeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L187-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L187-L207

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

theorem Formalism.DworkPowerSeriesWeights.spProd_ldeg (S : Finset σ) (e : σ → ℕ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n
      (∏ t ∈ S, (∑ k, MvPowerSeries.C (N t k) * MvPowerSeries.X k) ^ e t) ≠ 0) :
    ∀ t, spLdeg lt t n = if t ∈ S then e t else 0 := by sorry
