-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_sum_coordWt
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_coordWt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:40.596088+00:00
-- url     : https://prove2.me/theorems/5c875593-35f5-4c19-9ea3-41d0684a8a5c
-- title:
--   Weight Compositions: sum coord Wt
-- statement:
--   The Weight Compositions construction uses the sum coord Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L28-L33

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight

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
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_coordWt (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ k, Finsupp.weight (coordWt N n) d k = ∑ p, d p := by sorry
