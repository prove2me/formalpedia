-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_good_mul
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.good_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:59.051877+00:00
-- url     : https://prove2.me/theorems/21f27e62-81f8-4be4-aa85-d2449f8b46f4
-- title:
--   Minor Polynomials: good mul
-- statement:
--   The Minor Polynomials construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L142-L156

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.good_mul {nf : ℕ} {L : Finset (Fin (r + 2))} {e₁ e : CT k r nf × List (Mat k r)} (h₁ : Good L e₁)
    (h : Good L e) : Good L (mulCT e₁.1 e.1, e.2) := by sorry
