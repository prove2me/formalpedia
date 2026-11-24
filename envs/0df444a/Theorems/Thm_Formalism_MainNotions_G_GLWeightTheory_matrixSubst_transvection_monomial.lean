-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:07.291115+00:00
-- url     : https://prove2.me/theorems/7179a38b-5f6a-4059-b9d9-8de6ffe779b3
-- title:
--   GLWeight Theory: matrix Subst transvection monomial
-- statement:
--   The GLWeight Theory construction uses the matrix Subst transvection monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L111-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/SumFinsuppAntidiagEqSumPiFinset.lean#L111-L130

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

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial (N : ℕ) (hN : (m.sum fun _ e => e) < N) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ k ∈ Finset.range N, C (t ^ k) * divPowMono B LL S a b k m := by sorry
