-- Prove2me | Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_le
-- name    : Formalism.NG.KernelLengthBounds.length_ker_smul_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:04.859121+00:00
-- url     : https://prove2.me/theorems/084e8240-ebe2-40c0-89a1-4718a4f7196d
-- title:
--   Kernel Length Bounds: length ker smul le
-- statement:
--   The Kernel Length Bounds construction uses the length ker smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L30-L46

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

theorem Formalism.NG.KernelLengthBounds.length_ker_smul_le (a : O) :
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (KO O) a)) ≤
      IsDiscreteValuationRing.addVal O a := by sorry
