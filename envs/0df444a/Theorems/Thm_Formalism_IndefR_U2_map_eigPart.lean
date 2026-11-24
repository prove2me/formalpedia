-- Prove2me | Theorems.Thm_Formalism_IndefR_U2_map_eigPart
-- name    : Formalism.IndefR.U2.map_eigPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:24.236468+00:00
-- url     : https://prove2.me/theorems/cff44dd7-4697-4f9b-ae55-1ba2f4ce3169
-- title:
--   U2: map eig Part
-- statement:
--   The U2 construction uses the map eig Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L55-L58

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

theorem Formalism.IndefR.U2.map_eigPart (hI : Intw θ op opB) {c : I → ℂ} {x : A} (hx : x ∈ eigPart op c) : θ x ∈ eigPart opB c := by sorry
