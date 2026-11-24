-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_castSucc
-- name    : Formalism.FourierDecayAlt.P.Qx6.bS_succAbove_castSucc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:21.036929+00:00
-- url     : https://prove2.me/theorems/4cbed878-2b55-4077-bdbe-18e50125be36
-- title:
--   Qx6: b S succ Above cast Succ
-- statement:
--   The Qx6 construction uses the b S succ Above cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L218-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L218-L225

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {n : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx6.bS_succAbove_castSucc {m : ℕ} (e : Fin n) (v : Fin (m + 1) → Fin n) (w : Fin (m + 1)) :
    bS v e ∘ w.castSucc.succAbove = bS (v ∘ w.succAbove) e := by sorry
