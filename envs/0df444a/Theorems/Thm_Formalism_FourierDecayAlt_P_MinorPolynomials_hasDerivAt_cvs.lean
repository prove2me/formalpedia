-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_cvs
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_cvs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:04.485233+00:00
-- url     : https://prove2.me/theorems/4c4d4d56-e0dc-4dd6-9dc7-6106c39159d3
-- title:
--   Minor Polynomials: has Deriv At cvs
-- statement:
--   The Minor Polynomials construction uses the has Deriv At cvs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L47-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L47-L146

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X g : Mat k r) (t : CT k r nf)
    (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) :
    HasDerivAt (fun s => cvs D t (crv (false, X) g s)) (((dscal D X t).map fun t' => cvs D t' g).sum) 0 := by sorry
