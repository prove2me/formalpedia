-- Prove2me | Theorems.Thm_Formalism_IndefR_U2_isAdj_adjoint
-- name    : Formalism.IndefR.U2.isAdj_adjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:23.200477+00:00
-- url     : https://prove2.me/theorems/fbb18d55-bfd4-43c7-8a09-489ae79f953d
-- title:
--   U2: is Adj adjoint
-- statement:
--   The U2 construction uses the is Adj adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L117-L118

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]

theorem Formalism.IndefR.U2.isAdj_adjoint (θ : A →ₗ[ℂ] B) : IsAdj θ (LinearMap.adjoint θ) := by sorry
