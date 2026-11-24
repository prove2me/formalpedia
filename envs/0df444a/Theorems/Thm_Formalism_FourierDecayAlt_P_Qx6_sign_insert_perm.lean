-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_insert_perm
-- name    : Formalism.FourierDecayAlt.P.Qx6.sign_insert_perm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:05.757739+00:00
-- url     : https://prove2.me/theorems/32e2b67f-3ab1-4183-8d3e-7c612d92b654
-- title:
--   Qx6: sign insert perm
-- statement:
--   The Qx6 construction uses the sign insert perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L39-L41

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

theorem Formalism.FourierDecayAlt.P.Qx6.sign_insert_perm (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m p) = (-1) ^ (p.1 : ℕ) * Equiv.Perm.sign p.2 := by sorry
