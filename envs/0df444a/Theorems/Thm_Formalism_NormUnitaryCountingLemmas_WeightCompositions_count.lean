-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_count
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.count
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:06.515233+00:00
-- url     : https://prove2.me/theorems/03439592-f79c-47bc-8fbd-34dc6c81df79
-- title:
--   Weight Compositions: count
-- statement:
--   The Weight Compositions construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L267-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L267-L325

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
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
variable {K : Type u} [Field K] (ν : Fin N → ℕ)

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.count (h3p : NormUnitaryPermutationInvariance.{u}) (h3w : NormUnitaryWeight.{u}) (ν : Fin N → ℕ) (k : Fin n) :
    n * ∑ i ∈ Finset.range (∑ j, ν j + 1),
        i * Module.finrank K (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i :
          Submodule K (MvPolynomial (Fin N × Fin n) K)) =
      (∑ j, ν j) * Module.finrank K (H K (n := n) ν) := by sorry
