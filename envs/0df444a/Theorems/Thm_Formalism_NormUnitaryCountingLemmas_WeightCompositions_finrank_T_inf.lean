-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_T_inf
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_T_inf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:13.696793+00:00
-- url     : https://prove2.me/theorems/e6736191-419a-4ad2-be89-6257392f19d1
-- title:
--   Weight Compositions: finrank T inf
-- statement:
--   The Weight Compositions construction uses the finrank T inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L223-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L223-L248

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_T_inf (k : Fin n) (i : ℕ) (w : Fin n → ℕ) :
    Module.finrank K ↥((H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w) =
      if w k = i then Dw K ν w else 0 := by sorry
