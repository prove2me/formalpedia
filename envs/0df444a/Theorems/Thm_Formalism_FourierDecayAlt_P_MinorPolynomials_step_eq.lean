-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_step_eq
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.step_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:26.416372+00:00
-- url     : https://prove2.me/theorems/a8bb514c-ef14-5ca0-85c4-cf3d31259caf
-- title:
--   Minor Polynomials: step eq
-- statement:
--   The Minor Polynomials construction uses the step eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenBigCellSet.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenBigCellSet.lean#L117-L124

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_step_eq

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.step_eq (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by sorry
