-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial_prod
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:07.395627+00:00
-- url     : https://prove2.me/theorems/9460976f-621c-4933-b4e4-bf31feed883d
-- title:
--   GLWeight Theory: matrix Subst transvection monomial prod
-- statement:
--   The GLWeight Theory construction uses the matrix Subst transvection monomial prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L72-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L72-L96

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

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_prod :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      monomial (m - sourceVariableExponent LL S a b m) 1 *
        ∏ l : ι, (C (letterSign B LL l * t) * X (targetVar LL a b l) + X (sourceVar LL a b l)) ^ (sourceExp LL S a b m l) := by sorry
