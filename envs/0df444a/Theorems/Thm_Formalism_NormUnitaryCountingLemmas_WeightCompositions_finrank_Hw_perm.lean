-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_Hw_perm
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_Hw_perm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:11.670022+00:00
-- url     : https://prove2.me/theorems/7411fcec-d029-4d64-97c9-7e216eec4069
-- title:
--   Weight Compositions: finrank Hw perm
-- statement:
--   The Weight Compositions construction uses the finrank Hw perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L203-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L203-L211

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_Hw_perm (h3p : NormUnitaryPermutationInvariance.{u}) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ)) =
      Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) := by sorry
