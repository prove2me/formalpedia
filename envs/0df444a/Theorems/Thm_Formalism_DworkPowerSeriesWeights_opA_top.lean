-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_opA_top
-- name    : Formalism.DworkPowerSeriesWeights.opA_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:22.298789+00:00
-- url     : https://prove2.me/theorems/32958378-3bed-4024-9c5d-6226573a8fcf
-- title:
--   Dwork Power Series Weights: op A top
-- statement:
--   The Dwork Power Series Weights construction uses the op A top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L66-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L66-L80

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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

theorem Formalism.DworkPowerSeriesWeights.opA_top {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (hs : s ∈ TT) (i k : Fin N0)
    (h : opA TT T s i k ≠ 0) : i.val = 0 ↔ k.val = 0 := by sorry
