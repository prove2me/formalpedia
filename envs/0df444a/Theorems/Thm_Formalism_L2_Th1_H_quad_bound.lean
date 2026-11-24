-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_quad_bound
-- name    : Formalism.L2.Th1.H.quad_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:08.33838+00:00
-- url     : https://prove2.me/theorems/55ff6f3a-201e-45d8-8d5a-e2c3f46e2f96
-- title:
--   H: quad bound
-- statement:
--   The H construction uses the quad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L180-L186

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

theorem Formalism.L2.Th1.H.quad_bound (a b t : ℝ) (ha : 0 < a) : b * t ≤ a * t ^ 2 + b ^ 2 / (4 * a) := by sorry
