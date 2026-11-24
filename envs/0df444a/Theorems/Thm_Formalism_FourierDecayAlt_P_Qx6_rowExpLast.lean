-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_rowExpLast
-- name    : Formalism.FourierDecayAlt.P.Qx6.rowExpLast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:49.672959+00:00
-- url     : https://prove2.me/theorems/108fde26-a1a0-4fc1-bcf0-64c1ff2f8e85
-- title:
--   Qx6: row Exp Last
-- statement:
--   The Qx6 construction uses the row Exp Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L82-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L82-L104

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

theorem Formalism.FourierDecayAlt.P.Qx6.rowExpLast {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminorRow E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l)) := by sorry
