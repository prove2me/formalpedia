-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_rsmul
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_rsmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:30.048195+00:00
-- url     : https://prove2.me/theorems/2943511d-c215-4168-8bb6-f8f784aa5ba9
-- title:
--   Minor Polynomials: ck On rsmul
-- statement:
--   The Minor Polynomials construction uses the ck On rsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L53-L58

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_rsmul {m : ℕ∞} {b : Mat k r → ℝ} (hb : ContDiff ℝ ∞ b) {Φ : Mat k r → (Wq →L[ℂ] Wp)}
    (hΦ : CkOn m (GV k r) Φ) : CkOn m (GV k r) (fun x => b x • Φ x) := by sorry
