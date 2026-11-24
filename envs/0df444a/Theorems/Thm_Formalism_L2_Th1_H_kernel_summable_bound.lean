-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_kernel_summable_bound
-- name    : Formalism.L2.Th1.H.kernel_summable_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:59.897231+00:00
-- url     : https://prove2.me/theorems/38b10530-50b9-44e8-90d5-1a172c7aed72
-- title:
--   H: kernel summable bound
-- statement:
--   The H construction uses the kernel summable bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L188-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L188-L237

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

theorem Formalism.L2.Th1.H.kernel_summable_bound (hS : LatGaussSummable) (hN : FormNorm) (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (w : V) (r : ℝ) :
    Summable fun x : Λ => ‖kC H α w x‖ * Real.exp (r * ‖kL H w x‖) := by sorry
