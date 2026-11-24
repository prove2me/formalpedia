-- Prove2me | Theorems.Thm_Formalism_IndefR_U2_notLifted_le_ker
-- name    : Formalism.IndefR.U2.notLifted_le_ker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:15.457344+00:00
-- url     : https://prove2.me/theorems/86d5a19e-d864-4abc-bca6-48415153adb9
-- title:
--   U2: not Lifted le ker
-- statement:
--   The U2 construction uses the not Lifted le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L60-L68

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

theorem Formalism.IndefR.U2.notLifted_le_ker (hI : Intw θ op opB) (hG : GoodIn θ good goodB) {c : I → ℂ} (hc : c ∈ Ix)
    (hn : c ∉ Lifted opB goodB Ix) : eigPart op c ⊓ good ≤ LinearMap.ker θ := by sorry
