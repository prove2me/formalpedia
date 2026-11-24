-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial_sum
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:52.41143+00:00
-- url     : https://prove2.me/theorems/17301734-9aa7-4af6-b52c-49957d99ef62
-- title:
--   GLWeight Theory: matrix Subst transvection monomial sum
-- statement:
--   The GLWeight Theory construction uses the matrix Subst transvection monomial sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L163-L174

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
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
open Classical

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_sum :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ p ∈ Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1)),
        C (t ^ (∑ l, p l)) * monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by sorry
