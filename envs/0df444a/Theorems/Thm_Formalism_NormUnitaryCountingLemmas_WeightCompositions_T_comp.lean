-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_T_comp
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.T_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:53.279465+00:00
-- url     : https://prove2.me/theorems/a42ca1cd-443d-4b08-b2e6-4b0bb2d63f9d
-- title:
--   Weight Compositions: T comp
-- statement:
--   The Weight Compositions construction uses the T comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L250-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L250-L265

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.T_comp (h3w : NormUnitaryWeight.{u}) (k : Fin n) (i : ℕ) :
    ∀ F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i, ∀ w,
      weightedHomogeneousComponent (coordWt N n) w F ∈
        H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i := by sorry
