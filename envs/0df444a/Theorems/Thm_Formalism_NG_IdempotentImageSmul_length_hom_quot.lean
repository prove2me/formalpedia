-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentImageSmul_length_hom_quot
-- name    : Formalism.NG.IdempotentImageSmul.length_hom_quot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:43.49781+00:00
-- url     : https://prove2.me/theorems/8c18a210-bdd4-4155-b1e7-14d5f630b888
-- title:
--   Idempotent Image Smul: length hom quot
-- statement:
--   The Idempotent Image Smul construction uses the length hom quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L147-L150

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentImageSmul
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.IdempotentImageSmul.length_hom_quot (a : O) :
    Module.length O ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) = addVal O a := by sorry
