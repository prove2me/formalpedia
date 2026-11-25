-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_relIdx_smul_mem
-- name    : Formalism.L2.Th1.H.relIdx_smul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:51.95789+00:00
-- url     : https://prove2.me/theorems/2321d6b8-5494-5e8e-bc0c-cd20bfb49697
-- title:
--   H: rel Idx smul mem
-- statement:
--   The H construction uses the rel Idx smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/QuadraticSemicharactersOfProductThetaMem.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/QuadraticSemicharactersOfProductThetaMem.lean#L15-L21

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.relIdx_smul_mem (Λ₁ Λ₂ : AddSubgroup V) {x : V} (hx : x ∈ Λ₂) :
    (relIdx Λ₁ Λ₂ : ℂ) • x ∈ Λ₁ := by sorry
