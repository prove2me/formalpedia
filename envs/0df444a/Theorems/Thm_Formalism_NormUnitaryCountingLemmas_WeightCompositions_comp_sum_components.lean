-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_comp_sum_components
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_sum_components
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:52.94605+00:00
-- url     : https://prove2.me/theorems/e5011e9f-890b-46be-b4ff-98baf0b5fb54
-- title:
--   Weight Compositions: comp sum components
-- statement:
--   The Weight Compositions construction uses the comp sum components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L53-L64

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_sum_components {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (S : Finset M) (g : S → MvPolynomial σ K)
    (hg : ∀ m : S, g m ∈ weightedHomogeneousSubmodule K φ (m : M)) (m : S) :
    weightedHomogeneousComponent φ (m : M) (∑ m', g m') = g m := by sorry
