-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_oMul
-- name    : Formalism.FourierDecayAlt.P.Qx6.good_oMul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:54.609553+00:00
-- url     : https://prove2.me/theorems/df5aefb0-6624-4a48-9942-4f263b1f98ab
-- title:
--   Qx6: good o Mul
-- statement:
--   The Qx6 construction uses the good o Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1783-L1786
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1783-L1786

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
variable {H}

theorem Formalism.FourierDecayAlt.P.Qx6.good_oMul {M N : OM X} (hM : ∀ a b, H.Good (M a b)) (hN : ∀ a b, H.Good (N a b)) (a b : Fin 2) :
    H.Good (oMul M N a b) := by sorry
