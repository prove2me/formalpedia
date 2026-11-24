-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_opOrder_le
-- name    : Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.opOrder_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:13:12.136928+00:00
-- url     : https://prove2.me/theorems/a017c1eb-d172-4bad-ab0f-8e0dbebdfb85
-- title:
--   Differential Operator Classes: op Order le
-- statement:
--   The Differential Operator Classes construction uses the op Order le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L50-L62

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.opOrder_le (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) (h : C6.InDDPlus D fib L o κ Θ) :
    B.opOrder Θ ≤ o := by sorry
