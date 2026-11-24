-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_comp_castSucc
-- name    : Formalism.FourierDecayAlt.P.Qx6.bS_comp_castSucc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:19.705431+00:00
-- url     : https://prove2.me/theorems/e338cbcb-e683-46c4-bc86-2f7f7fb4e928
-- title:
--   Qx6: b S comp cast Succ
-- statement:
--   The Qx6 construction uses the b S comp cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L195-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L195-L197

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

theorem Formalism.FourierDecayAlt.P.Qx6.bS_comp_castSucc {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e ∘ Fin.castSucc = v := by sorry
