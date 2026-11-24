-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_eq_sum_components
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_eq_sum_components
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:42.921658+00:00
-- url     : https://prove2.me/theorems/cf5da20a-1719-4a0c-9d52-4e0228dddd94
-- title:
--   Weight Compositions: finrank eq sum components
-- statement:
--   The Weight Compositions construction uses the finrank eq sum components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L66-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L66-L109

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_eq_sum_components {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (V : Submodule K (MvPolynomial σ K)) [FiniteDimensional K V] (S : Finset M)
    (hcomp : ∀ F ∈ V, ∀ m, weightedHomogeneousComponent φ m F ∈ V)
    (hS : ∀ F ∈ V, ∀ m ∉ S, weightedHomogeneousComponent φ m F = 0) :
    Module.finrank K V =
      ∑ m ∈ S, Module.finrank K ↥(V ⊓ weightedHomogeneousSubmodule K φ m) := by sorry
