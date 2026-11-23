-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_prod_monomial_eq_monomial_sum_prod
-- name    : Formalism.MainNotions.G.GLWeightTheory.prod_monomial_eq_monomial_sum_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:38.528631+00:00
-- url     : https://prove2.me/theorems/da6059bf-7979-4994-84d7-513f401285ec
-- title:
--   GLWeight Theory: prod monomial eq monomial sum prod
-- statement:
--   The GLWeight Theory construction uses the prod monomial eq monomial sum prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L11-L18

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G

theorem Formalism.MainNotions.G.GLWeightTheory.prod_monomial_eq_monomial_sum_prod {B σ α : Type*} [CommRing B] (s : Finset α) (f : α → σ →₀ ℕ) (c : α → B) :
    ∏ i ∈ s, monomial (f i) (c i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by sorry
