-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_compFS_bound
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.compFS_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:23.393289+00:00
-- url     : https://prove2.me/theorems/b7dcde55-5596-4134-bdd6-a6b5e8b8e32d
-- title:
--   Minor Polynomials: comp FS bound
-- statement:
--   The Minor Polynomials construction uses the comp FS bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L104-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L104-L146

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.compFS_bound (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by sorry
