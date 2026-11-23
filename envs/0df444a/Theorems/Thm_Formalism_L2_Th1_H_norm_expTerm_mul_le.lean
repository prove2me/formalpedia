-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_norm_expTerm_mul_le
-- name    : Formalism.L2.Th1.H.norm_expTerm_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:59.362228+00:00
-- url     : https://prove2.me/theorems/3114f9e7-ca58-4dd8-a205-38cd5227445f
-- title:
--   H: norm exp Term mul le
-- statement:
--   The H construction uses the norm exp Term mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L36-L42

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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.L2.Th1.H.norm_expTerm_mul_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) (r : ℝ)
    (hr : 0 ≤ r) : ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * Real.exp (r * ‖l x‖) := by sorry
