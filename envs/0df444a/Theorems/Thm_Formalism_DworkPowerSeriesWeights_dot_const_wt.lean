-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const_wt
-- name    : Formalism.DworkPowerSeriesWeights.dot_const_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:54.81142+00:00
-- url     : https://prove2.me/theorems/1b5d1ea2-ff67-4471-80eb-d5f3314db4a0
-- title:
--   Dwork Power Series Weights: dot const wt
-- statement:
--   The Dwork Power Series Weights construction uses the dot const wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneLetterRadiusIdentity.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneLetterRadiusIdentity.lean#L44-L46

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.dot_const_wt {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (∑ x ∈ n.support, (n x : ℝ)) * c := by sorry
