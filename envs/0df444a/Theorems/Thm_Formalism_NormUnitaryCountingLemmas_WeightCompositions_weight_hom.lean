-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_hom
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_hom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:35.925741+00:00
-- url     : https://prove2.me/theorems/34daa143-ce82-4c5c-8228-77b778987983
-- title:
--   Weight Compositions: weight hom
-- statement:
--   The Weight Compositions construction uses the weight hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L14-L17

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_hom {σ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (g : M →+ M')
    (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun i => g (w i)) d = g (Finsupp.weight w d) := by sorry
