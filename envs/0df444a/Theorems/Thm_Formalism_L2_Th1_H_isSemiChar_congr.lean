-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_isSemiChar_congr
-- name    : Formalism.L2.Th1.H.isSemiChar_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:27.373422+00:00
-- url     : https://prove2.me/theorems/e00e268b-5ebc-4173-8511-ee6b0a8ef4e1
-- title:
--   H: is Semi Char congr
-- statement:
--   The H construction uses the is Semi Char congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlockFirstBlockEmb.lean#L244-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlockFirstBlockEmb.lean#L244-L248

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
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

theorem Formalism.L2.Th1.H.isSemiChar_congr {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (α β : V → ℂ) (hab : ∀ x ∈ Λ, α x = β x) (hβ : IsSemiChar H Λ β) : IsSemiChar H Λ α := by sorry
