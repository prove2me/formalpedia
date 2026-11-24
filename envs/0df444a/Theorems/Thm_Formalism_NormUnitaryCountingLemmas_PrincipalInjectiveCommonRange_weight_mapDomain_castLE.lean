-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_weight_mapDomain_castLE
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.weight_mapDomain_castLE
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:41.889896+00:00
-- url     : https://prove2.me/theorems/df93742a-506a-46a0-8c5c-48016f2c1d06
-- title:
--   Principal Injective Common Range: weight map Domain cast LE
-- statement:
--   The Principal Injective Common Range construction uses the weight map Domain cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L14-L31

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

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.weight_mapDomain_castLE {N N' n : ℕ} (hN : N ≤ N') (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (blockWt N' n)
        (Finsupp.mapDomain (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) d) =
      extW (Finsupp.weight (blockWt N n) d) := by sorry
