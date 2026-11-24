-- Prove2me | Theorems.Thm_Formalism_NG_KernelLengthBounds_length_colData_le
-- name    : Formalism.NG.KernelLengthBounds.length_colData_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:25.817827+00:00
-- url     : https://prove2.me/theorems/f06f19f0-1ee6-461b-95b8-41c7529bcc52
-- title:
--   Kernel Length Bounds: length col Data le
-- statement:
--   The Kernel Length Bounds construction uses the length col Data le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L123-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean#L123-L143

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

theorem Formalism.NG.KernelLengthBounds.length_colData_le (ℓ : ℕ) (δ : O) (e' j : ℕ) (Xw : Type*) [AddCommGroup Xw]
    [Module O Xw] (d : Type) [Fintype d] (h0 : ℕ∞) (hX : Module.length O Xw ≤ h0) :
    Module.length O (ColData O ℓ δ e' j Xw d) ≤
      ((j : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' : ℕ∞) +
          IsDiscreteValuationRing.addVal O δ) + h0) +
        (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δ := by sorry
