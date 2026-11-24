-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_dividedPowerMonomial_eq_sum
-- name    : Formalism.MainNotions.G.GLWeightTheory.dividedPowerMonomial_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:59.387839+00:00
-- url     : https://prove2.me/theorems/452072da-5f5e-4916-8edc-7f771e2be262
-- title:
--   GLWeight Theory: divided Power Monomial eq sum
-- statement:
--   The GLWeight Theory construction uses the divided Power Monomial eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L17-L30

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

theorem Formalism.MainNotions.G.GLWeightTheory.dividedPowerMonomial_eq_sum (k : ℕ) :
    divPowMono B LL S a b k m = ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) := by sorry
