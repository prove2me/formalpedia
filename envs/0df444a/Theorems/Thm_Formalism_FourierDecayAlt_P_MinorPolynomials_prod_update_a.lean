-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_prod_update_a
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.prod_update_a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:43.500467+00:00
-- url     : https://prove2.me/theorems/b3e3dbf1-481f-4202-b173-e3063707e062
-- title:
--   Minor Polynomials: prod update a
-- statement:
--   The Minor Polynomials construction uses the prod update a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L23-L33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.prod_update_a (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ (a l + 1) * (star (Dmin k r z z' g l))⁻¹ ^ b l) =
      ∏ j, fct z z' (a + Pi.single l 1) b g j := by sorry
