-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_mapDomain
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_mapDomain
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:53.585595+00:00
-- url     : https://prove2.me/theorems/82e15994-c034-4489-aa78-e2194dc0ee1e
-- title:
--   Weight Compositions: weight map Domain
-- statement:
--   The Weight Compositions construction uses the weight map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L19-L24

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight_mapDomain

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (f : σ → τ) (w : τ → M)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (fun i => w (f i)) d := by sorry
