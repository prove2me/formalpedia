-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bddAbove_norm_coeff
-- name    : Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:11.286347+00:00
-- url     : https://prove2.me/theorems/5e68a2b2-f8cf-452b-955c-6708f6c0fad6
-- title:
--   Dwork Power Series Weights: bdd Above norm coeff
-- statement:
--   The Dwork Power Series Weights construction uses the bdd Above norm coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Labels.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Labels.lean#L11-L23

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff {R : Type} [NormedField R] {σ : Type} (Q : MvPolynomial σ R) :
    BddAbove (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖) := by sorry
