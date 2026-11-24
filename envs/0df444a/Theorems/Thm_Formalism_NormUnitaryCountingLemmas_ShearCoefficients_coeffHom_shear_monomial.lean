-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_coeffHom_shear_monomial
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_monomial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:43.920986+00:00
-- url     : https://prove2.me/theorems/540f5d5d-f4a9-4164-84e5-9b69f1a945a4
-- title:
--   Shear Coefficients: coeff Hom shear monomial
-- statement:
--   The Shear Coefficients construction uses the coeff Hom shear monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L131-L137

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

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_monomial {N n : ℕ} (i j : Fin N) (d : (Fin N × Fin n) →₀ ℕ) (r : R) :
    CoeffHom (coordWt N n) (Finsupp.weight (coordWt N n) d) (shear R i j (monomial d r)) := by sorry
