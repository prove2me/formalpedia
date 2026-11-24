-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_repMap_bijective
-- name    : Formalism.L2.Th1.H.repMap_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:56.840857+00:00
-- url     : https://prove2.me/theorems/a9b876df-642e-45e8-addb-04f000bca50c
-- title:
--   H: rep Map bijective
-- statement:
--   The H construction uses the rep Map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnfoldingIntegral.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnfoldingIntegral.lean#L44-L63

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnfoldingIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open scoped Pointwise
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.repMap_bijective {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S) :
    Function.Bijective (repMap Ae hle hS) := by sorry
