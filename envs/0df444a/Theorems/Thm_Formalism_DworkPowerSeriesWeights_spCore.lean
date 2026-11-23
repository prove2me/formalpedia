-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCore
-- name    : Formalism.DworkPowerSeriesWeights.spCore
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:46.384735+00:00
-- url     : https://prove2.me/theorems/f2f34ae5-a406-40e6-a9a8-2f9f1b2991e1
-- title:
--   Dwork Power Series Weights: sp Core
-- statement:
--   The Dwork Power Series Weights construction uses the sp Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L285-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L285-L313

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

theorem Formalism.DworkPowerSeriesWeights.spCore (f : MvPowerSeries σ R) (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      (MvPowerSeries.subst (fun s => ∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) f) =
      MvPowerSeries.coeff (Finsupp.single (lt i) a + Finsupp.single (lt j) b) f *
        (N (lt i) i ^ a * N (lt j) j ^ b) := by sorry
