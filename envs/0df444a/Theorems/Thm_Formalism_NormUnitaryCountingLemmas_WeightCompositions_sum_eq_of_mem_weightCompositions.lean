-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_sum_eq_of_mem_weightCompositions
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_eq_of_mem_weightCompositions
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:51.252547+00:00
-- url     : https://prove2.me/theorems/8e17f8c8-6fa7-4efd-a280-8268b9d7fa03
-- title:
--   Weight Compositions: sum eq of mem weight Compositions
-- statement:
--   The Weight Compositions construction uses the sum eq of mem weight Compositions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L143-L144

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_eq_of_mem_weightCompositions {s : ℕ} {w : Fin n → ℕ} (h : w ∈ S0 n s) : ∑ k, w k = s := by sorry
