-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_opOrder_le_of
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.opOrder_le_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:19:26.11356+00:00
-- url     : https://prove2.me/theorems/a75e5547-6ffe-47fa-a53f-bf8562173dc5
-- title:
--   Minor Polynomials: op Order le of
-- statement:
--   The Minor Polynomials construction uses the op Order le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L80-L86

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.opOrder_le_of (Θ : DiffOp k r Wp Wq) {n : ℕ} (h : ∀ T ∈ Θ, T.word.length ≤ n) : opOrder Θ ≤ n := by sorry
