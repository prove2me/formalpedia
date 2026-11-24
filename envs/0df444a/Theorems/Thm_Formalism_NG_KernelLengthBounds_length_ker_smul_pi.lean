-- Prove2me | Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_pi
-- name    : Formalism.NG.KernelLengthBounds.length_ker_smul_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:12.421432+00:00
-- url     : https://prove2.me/theorems/4604a534-a157-49fe-9a67-9b5a82066708
-- title:
--   Kernel Length Bounds: length ker smul pi
-- statement:
--   The Kernel Length Bounds construction uses the length ker smul pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L15-L28

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.KernelLengthBounds.length_ker_smul_pi (d : Type) [Fintype d] (a : O) :
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) a)) =
      (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O a := by sorry
