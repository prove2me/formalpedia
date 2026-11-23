-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCoeff_lin
-- name    : Formalism.DworkPowerSeriesWeights.spCoeff_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:24.065878+00:00
-- url     : https://prove2.me/theorems/5b21a76f-a99b-4735-a0a4-f089c85d9f61
-- title:
--   Dwork Power Series Weights: sp Coeff lin
-- statement:
--   The Dwork Power Series Weights construction uses the sp Coeff lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L144-L149

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

theorem Formalism.DworkPowerSeriesWeights.spCoeff_lin (s : σ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) =
      ∑ k, N s k * if n = Finsupp.single k 1 then 1 else 0 := by sorry
