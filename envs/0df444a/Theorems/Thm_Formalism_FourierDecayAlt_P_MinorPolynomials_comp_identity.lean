-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_comp_identity
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.comp_identity
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:20.533868+00:00
-- url     : https://prove2.me/theorems/d8fdb764-6a97-42ff-a61e-50ad6109d289
-- title:
--   Minor Polynomials: comp identity
-- statement:
--   The Minor Polynomials construction uses the comp identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L171-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L171-L189

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.comp_identity (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by sorry
