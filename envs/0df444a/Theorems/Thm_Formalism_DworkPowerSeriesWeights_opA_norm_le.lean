-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_opA_norm_le
-- name    : Formalism.DworkPowerSeriesWeights.opA_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:56.289058+00:00
-- url     : https://prove2.me/theorems/859accc9-f9b0-4cd7-901d-2695ab7afc11
-- title:
--   Dwork Power Series Weights: op A norm le
-- statement:
--   The Dwork Power Series Weights construction uses the op A norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L60-L64

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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
open Formalism.IncomingBounds MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.opA_norm_le {K : Type u} [NormedField K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (hT : ∀ s i k, ‖T s i k‖ ≤ 1) (s : ZMod d) (i k : Fin N0) :
    ‖opA TT T s i k‖ ≤ 1 := by sorry
