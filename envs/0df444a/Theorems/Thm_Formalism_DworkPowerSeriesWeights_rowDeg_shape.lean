-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_shape
-- name    : Formalism.DworkPowerSeriesWeights.rowDeg_shape
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:18.051957+00:00
-- url     : https://prove2.me/theorems/e874ec71-1ad1-454c-8f49-a50f92128ba1
-- title:
--   Dwork Power Series Weights: row Deg shape
-- statement:
--   The Dwork Power Series Weights construction uses the row Deg shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L118-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L118-L136

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

theorem Formalism.DworkPowerSeriesWeights.rowDeg_shape {d N0 N1 p : ℕ} (s s' : ZMod d) (k : Fin N0) (τ : Fin p → Fin N0)
    (I : Fin p → Fin N1) :
    rowDeg s' k (∑ i, Finsupp.single ((s, τ i, I i) : ZV d N0 N1) 1) =
      if s' = s then (Finset.univ.filter (fun i => τ i = k)).card else 0 := by sorry
