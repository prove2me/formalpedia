-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_comp_eq_zero
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:53.879276+00:00
-- url     : https://prove2.me/theorems/ed27e383-e8e3-427f-b48c-2e1acd6ea417
-- title:
--   Weight Compositions: comp eq zero
-- statement:
--   The Weight Compositions construction uses the comp eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L151-L158

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_eq_zero {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) (w : Fin n → ℕ)
    (hw : w ∉ S0 n (∑ j, ν j)) : weightedHomogeneousComponent (coordWt N n) w F = 0 := by sorry
