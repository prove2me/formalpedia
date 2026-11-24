-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_epart
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_epart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:51.805177+00:00
-- url     : https://prove2.me/theorems/08477af3-8e90-4519-94e1-b216ba4a3ae3
-- title:
--   Minor Polynomials: has Deriv At epart
-- statement:
--   The Minor Polynomials construction uses the has Deriv At epart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L30-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L30-L54

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) →
      HasDerivAt (fun s => C6.Epart fib es (crv (false, X) g s))
        (∑ i : Fin es.length, C6.Epart fib (es.set i ((es.get i).1, X :: (es.get i).2)) g) 0 := by sorry
