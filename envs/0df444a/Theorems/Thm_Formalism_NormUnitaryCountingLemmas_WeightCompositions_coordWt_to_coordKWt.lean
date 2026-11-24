-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_coordWt_to_coordKWt
-- name    : Formalism.NormUnitaryCountingLemmas.WeightCompositions.coordWt_to_coordKWt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:28.342148+00:00
-- url     : https://prove2.me/theorems/8eb36963-1e2e-4bc2-aecf-82fe73e33ee3
-- title:
--   Weight Compositions: coord Wt to coord KWt
-- statement:
--   The Weight Compositions construction uses the coord Wt to coord KWt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean#L216-L221

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

theorem Formalism.NormUnitaryCountingLemmas.WeightCompositions.coordWt_to_coordKWt (k : Fin n) {w : Fin n → ℕ} {G : MvPolynomial (Fin N × Fin n) K}
    (hG : G ∈ weightedHomogeneousSubmodule K (coordWt N n) w) :
    G ∈ weightedHomogeneousSubmodule K (coordKWt N n k) (w k) := by sorry
