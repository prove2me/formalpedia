-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_coeffHom_shear_X
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:44.017344+00:00
-- url     : https://prove2.me/theorems/7caa2e8a-9858-41fd-92bd-e9d7e83bf673
-- title:
--   Shear Coefficients: coeff Hom shear X
-- statement:
--   The Shear Coefficients construction uses the coeff Hom shear X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L119-L129

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_X {N n : ℕ} (i j : Fin N) (p : Fin N × Fin n) :
    CoeffHom (R := R) (coordWt N n) (coordWt N n p)
      (Polynomial.C (X p) +
        (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)) := by sorry
