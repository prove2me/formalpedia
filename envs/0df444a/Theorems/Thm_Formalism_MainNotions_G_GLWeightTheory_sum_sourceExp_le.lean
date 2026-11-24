-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_sourceExp_le
-- name    : Formalism.MainNotions.G.GLWeightTheory.sum_sourceExp_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:08.312811+00:00
-- url     : https://prove2.me/theorems/afc37767-ddcf-47d3-8f39-9257176d485b
-- title:
--   GLWeight Theory: sum source Exp le
-- statement:
--   The GLWeight Theory construction uses the sum source Exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L96-L107

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset
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
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)

theorem Formalism.MainNotions.G.GLWeightTheory.sum_sourceExp_le : ∑ l : ι, sourceExp LL S a b m l ≤ m.sum fun _ e => e := by sorry
