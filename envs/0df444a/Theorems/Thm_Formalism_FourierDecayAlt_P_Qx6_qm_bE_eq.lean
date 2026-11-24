-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_bE_eq
-- name    : Formalism.FourierDecayAlt.P.Qx6.qm_bE_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:35:55.999249+00:00
-- url     : https://prove2.me/theorems/27d5229c-28a7-4134-94d6-e998d2ddc233
-- title:
--   Qx6: qm b E eq
-- statement:
--   The Qx6 construction uses the qm b E eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L270-L272

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem Formalism.FourierDecayAlt.P.Qx6.qm_bE_eq (hSk : QSkewRow) {t : ℕ} (f : Fin t → Fin n) (e : Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = ((-1 : ℤ) ^ t) • qminor E (bS f e) b u := by sorry
