-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_finsuppAntidiag_eq_sum_piFinset
-- name    : Formalism.MainNotions.G.GLWeightTheory.sum_finsuppAntidiag_eq_sum_piFinset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:56.83396+00:00
-- url     : https://prove2.me/theorems/76f62e01-af8d-44eb-9216-63f02e8eeeb8
-- title:
--   GLWeight Theory: sum finsupp Antidiag eq sum pi Finset
-- statement:
--   The GLWeight Theory construction uses the sum finsupp Antidiag eq sum pi Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L33-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L33-L94

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
open Classical

theorem Formalism.MainNotions.G.GLWeightTheory.sum_finsuppAntidiag_eq_sum_piFinset (k : ℕ) :
    ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) =
    ∑ p ∈ (Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1))).filter (fun p => ∑ l, p l = k),
      monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by sorry
