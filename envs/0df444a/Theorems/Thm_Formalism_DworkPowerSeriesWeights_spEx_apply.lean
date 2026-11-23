-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spEx_apply
-- name    : Formalism.DworkPowerSeriesWeights.spEx_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:45.897331+00:00
-- url     : https://prove2.me/theorems/8556d79d-ccc7-4d3e-af9b-fc0fb2ed8159
-- title:
--   Dwork Power Series Weights: sp Ex apply
-- statement:
--   The Dwork Power Series Weights construction uses the sp Ex apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L345-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L345-L349

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
variable {R : Type*} [CommRing R] {m p : ℕ}

theorem Formalism.DworkPowerSeriesWeights.spEx_apply (o : Option (Fin m)) (c c' : Fin (p + 1)) (k : Fin m) :
    spEx o c (k, c') = if o = some k ∧ c = c' then 1 else 0 := by sorry
