-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_repClass_bijective
-- name    : Formalism.L2.Th1.H.repClass_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:21.533646+00:00
-- url     : https://prove2.me/theorems/20cb04b7-2d90-48e2-b361-623d2de81f43
-- title:
--   H: rep Class bijective
-- statement:
--   The H construction uses the rep Class bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LocalComponentGL.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LocalComponentGL.lean#L30-L39

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.repClass_bijective {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    Function.Bijective (repClass hS) := by sorry
