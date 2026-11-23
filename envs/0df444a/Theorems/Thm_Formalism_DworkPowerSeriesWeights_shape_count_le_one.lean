-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_count_le_one
-- name    : Formalism.DworkPowerSeriesWeights.shape_count_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:00.708803+00:00
-- url     : https://prove2.me/theorems/1da2fe43-073e-4149-ab40-1715de7b7b1d
-- title:
--   Dwork Power Series Weights: shape count le one
-- statement:
--   The Dwork Power Series Weights construction uses the shape count le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L67-L73

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
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
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.shape_count_le_one {J : Type} [DecidableEq J] {p : ℕ} (τ : Fin p → J)
    (hτ : Function.Injective τ) (j : J) :
    (Finset.univ.filter (fun i => τ i = j)).card ≤ 1 := by sorry
