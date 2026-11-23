-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowOp_mem_opInt
-- name    : Formalism.DworkPowerSeriesWeights.rowOp_mem_opInt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:20.100934+00:00
-- url     : https://prove2.me/theorems/f0dff997-50cb-43a7-b1c8-5e7d27a23a45
-- title:
--   Dwork Power Series Weights: row Op mem op Int
-- statement:
--   The Dwork Power Series Weights construction uses the row Op mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L82-L92

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

theorem Formalism.DworkPowerSeriesWeights.rowOp_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ}
    (TT : Finset (ZMod d)) (T : ZMod d → Fin N0 → Fin N0 → K) (hT : ∀ s i k, ‖T s i k‖ ≤ 1)
    (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    rowOp (N1 := N1) TT T s i b ∈ opInt K (ZV d N0 N1) := by sorry
