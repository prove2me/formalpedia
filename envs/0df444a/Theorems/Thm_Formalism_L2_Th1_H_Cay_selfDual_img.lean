-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Cay_selfDual_img
-- name    : Formalism.L2.Th1.H.Cay.selfDual_img
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:18.599103+00:00
-- url     : https://prove2.me/theorems/6f57da82-e5e5-4cb3-b608-5c28a8002076
-- title:
--   Cay: self Dual img
-- statement:
--   The Cay construction uses the self Dual img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnitaryEighthOf.lean#L81-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnitaryEighthOf.lean#L81-L113

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.Cay

theorem Formalism.L2.Th1.H.Cay.selfDual_img {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (δ : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hΛ : IsSelfDual H Λ) :
    IsSelfDual H (imgLat (δ : V →ₗ[ℂ] V) Λ) := by sorry
