-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_comp_coeff_shear
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.comp_coeff_shear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:48.402799+00:00
-- url     : https://prove2.me/theorems/f8cf19aa-5434-47bc-a4b5-7802ec1e1951
-- title:
--   Shear Coefficients: comp coeff shear
-- statement:
--   The Shear Coefficients construction uses the comp coeff shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L139-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L139-L151

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

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.comp_coeff_shear {N n : ℕ} (i j : Fin N) (w : Fin n → ℕ)
    (F : MvPolynomial (Fin N × Fin n) R) (k : ℕ) :
    weightedHomogeneousComponent (coordWt N n) w ((shear R i j F).coeff k) =
      (shear R i j (weightedHomogeneousComponent (coordWt N n) w F)).coeff k := by sorry
