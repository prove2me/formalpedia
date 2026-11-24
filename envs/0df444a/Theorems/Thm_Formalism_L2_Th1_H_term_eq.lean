-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_term_eq
-- name    : Formalism.L2.Th1.H.term_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:18.615815+00:00
-- url     : https://prove2.me/theorems/67d9a71f-5340-4251-af12-157cc21b0228
-- title:
--   H: term eq
-- statement:
--   The H construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L169-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L169-L178

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.Th1.H.term_eq (H : Sesq V) (α : V → ℂ) (w x z : V) :
    α x * opU H x (kerK H w) z = kC H α w x * Complex.exp (kL H w x z) := by sorry
