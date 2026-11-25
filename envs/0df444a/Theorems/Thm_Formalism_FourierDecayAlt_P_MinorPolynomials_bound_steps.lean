-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_bound_steps
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.bound_steps
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:00.238501+00:00
-- url     : https://prove2.me/theorems/f3a5eba9-8867-4623-ab9a-98b131e37cfe
-- title:
--   Minor Polynomials: bound steps
-- statement:
--   The Minor Polynomials construction uses the bound steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L209-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L209-L228

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.bound_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by sorry
