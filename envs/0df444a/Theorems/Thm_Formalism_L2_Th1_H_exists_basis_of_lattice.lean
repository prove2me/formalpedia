-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_exists_basis_of_lattice
-- name    : Formalism.L2.Th1.H.exists_basis_of_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:26.656769+00:00
-- url     : https://prove2.me/theorems/0e45ba34-a2f5-43a8-9dfd-e35a0f4fc6d7
-- title:
--   H: exists basis of lattice
-- statement:
--   The H construction uses the exists basis of lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexEqAbsDetReal.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexEqAbsDetReal.lean#L62-L77

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
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
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.exists_basis_of_lattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : AddSubgroup E) (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set E) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, Λ = .closure (Set.range b) := by sorry
