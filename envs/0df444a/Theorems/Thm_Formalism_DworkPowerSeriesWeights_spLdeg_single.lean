-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_single
-- name    : Formalism.DworkPowerSeriesWeights.spLdeg_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:44.443323+00:00
-- url     : https://prove2.me/theorems/d9a0f57b-0b7c-457d-9b38-ba6e03df8f49
-- title:
--   Dwork Power Series Weights: sp Ldeg single
-- statement:
--   The Dwork Power Series Weights construction uses the sp Ldeg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L124-L131

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

theorem Formalism.DworkPowerSeriesWeights.spLdeg_single (lt : ι → σ) (t : σ) (k : ι) (c : ℕ) :
    spLdeg lt t (Finsupp.single k c) = if lt k = t then c else 0 := by sorry
