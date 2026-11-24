-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_bS
-- name    : Formalism.FourierDecayAlt.P.Qx6.bE_bS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:03.675294+00:00
-- url     : https://prove2.me/theorems/580c1b15-55c6-44ac-aefd-7476eae72da3
-- title:
--   Qx6: b E b S
-- statement:
--   The Qx6 construction uses the b E b S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L199-L201

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

theorem Formalism.FourierDecayAlt.P.Qx6.bE_bS {m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : bE e (bS v es) = bS (bE e v) es := by sorry
