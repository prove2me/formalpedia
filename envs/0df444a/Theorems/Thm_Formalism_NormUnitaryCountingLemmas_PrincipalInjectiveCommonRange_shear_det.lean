-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_det
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:23.716702+00:00
-- url     : https://prove2.me/theorems/ce6bacaf-3400-4b80-92b1-78506e94c2e6
-- title:
--   Principal Injective Common Range: shear det
-- statement:
--   The Principal Injective Common Range construction uses the shear det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L69-L83

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
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
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_det {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    shear R i j (detPoly R n) = Polynomial.C (detPoly R n) := by sorry
