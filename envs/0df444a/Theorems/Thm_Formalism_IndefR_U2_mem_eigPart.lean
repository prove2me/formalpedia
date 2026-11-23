-- Prove2me | Theorems.Thm_Formalism_IndefR_U2_mem_eigPart
-- name    : Formalism.IndefR.U2.mem_eigPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:24.781148+00:00
-- url     : https://prove2.me/theorems/550e11fa-f02f-4832-9a12-1c78d4964559
-- title:
--   U2: mem eig Part
-- statement:
--   The U2 construction uses the mem eig Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L15-L18

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

theorem Formalism.IndefR.U2.mem_eigPart {op : I → Module.End ℂ A} {c : I → ℂ} {x : A} :
    x ∈ eigPart op c ↔ ∀ i, op i x = c i • x := by sorry
