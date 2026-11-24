-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_map_dividedPowerMonomial
-- name    : Formalism.MainNotions.G.GLWeightTheory.map_dividedPowerMonomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:05.590072+00:00
-- url     : https://prove2.me/theorems/dceb806c-ac26-4bd9-a207-132439d1dc8b
-- title:
--   GLWeight Theory: map divided Power Monomial
-- statement:
--   The GLWeight Theory construction uses the map divided Power Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L132-L140

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
variable {R : Type*} [CommRing R] (φ : R →+* B)

theorem Formalism.MainNotions.G.GLWeightTheory.map_dividedPowerMonomial (k : ℕ) :
    MvPolynomial.map φ (divPowMono R LL S a b k m) = divPowMono B LL S a b k m := by sorry
