-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_coordKWt
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_coordKWt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:33.618898+00:00
-- url     : https://prove2.me/theorems/ef369090-2936-492b-9073-4b0f98024e6b
-- title:
--   Weight Compositions: weight coord KWt
-- statement:
--   The Weight Compositions construction uses the weight coord KWt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L46-L51

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_coordKWt (k : Fin n) (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (coordKWt N n k) d = Finsupp.weight (coordWt N n) d k := by sorry
