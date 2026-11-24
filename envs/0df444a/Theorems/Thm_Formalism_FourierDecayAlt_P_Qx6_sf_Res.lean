-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sf_Res
-- name    : Formalism.FourierDecayAlt.P.Qx6.sf_Res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:35:59.218628+00:00
-- url     : https://prove2.me/theorems/fdf80b0b-ca28-4a6f-b1d8-8f456dfbdec8
-- title:
--   Qx6: sf Res
-- statement:
--   The Qx6 construction uses the sf Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L958-L961
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L958-L961

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Qx6.sf_Res (hW : WeylLevelElementFacts) (l : Fin r) {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r l.castSucc (UU Dc) Φ) : SmoothFam k r l.succ (UU (stepD l Dc)) (Res k r l Φ) := by sorry
