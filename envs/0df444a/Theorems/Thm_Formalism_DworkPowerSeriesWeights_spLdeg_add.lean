-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_add
-- name    : Formalism.DworkPowerSeriesWeights.spLdeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:29.163552+00:00
-- url     : https://prove2.me/theorems/5a999973-43e7-4b46-998e-fb1aa0ef153e
-- title:
--   Dwork Power Series Weights: sp Ldeg add
-- statement:
--   The Dwork Power Series Weights construction uses the sp Ldeg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L117-L122

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

theorem Formalism.DworkPowerSeriesWeights.spLdeg_add (lt : ι → σ) (t : σ) (n n' : ι →₀ ℕ) :
    spLdeg lt t (n + n') = spLdeg lt t n + spLdeg lt t n' := by sorry
