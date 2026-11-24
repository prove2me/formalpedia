-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_dividedPower_monomial
-- name    : Formalism.MainNotions.G.GLWeightTheory.dividedPower_monomial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:09.229067+00:00
-- url     : https://prove2.me/theorems/075ef1f1-113d-436d-bfe9-e2aa431e078e
-- title:
--   GLWeight Theory: divided Power monomial
-- statement:
--   The GLWeight Theory construction uses the divided Power monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L142-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L142-L148

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

theorem Formalism.MainNotions.G.GLWeightTheory.dividedPower_monomial (k : ℕ) (c : R) :
    divPow R LL S a b k (monomial m c) = c • divPowMono R LL S a b k m := by sorry
