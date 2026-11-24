-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_isWH_det
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:00.416813+00:00
-- url     : https://prove2.me/theorems/eef7e241-777a-4486-8421-7f1876deec59
-- title:
--   Principal Injective Common Range: is WH det
-- statement:
--   The Principal Injective Common Range construction uses the is WH det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L45-L59

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

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_det (n : ℕ) :
    (detPoly R n).IsWeightedHomogeneous (blockWt n n) (fun _ => 1) := by sorry
