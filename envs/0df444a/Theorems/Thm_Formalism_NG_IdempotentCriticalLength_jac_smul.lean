-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentCriticalLength_jac_smul
-- name    : Formalism.NG.IdempotentCriticalLength.jac_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:49.491347+00:00
-- url     : https://prove2.me/theorems/e028093f-7c0a-4dc5-878e-2ea13c486db8
-- title:
--   Idempotent Critical Length: jac smul
-- statement:
--   The Idempotent Critical Length construction uses the jac smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SmulEqZeroIffCrit.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SmulEqZeroIffCrit.lean#L15-L17

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

theorem Formalism.NG.IdempotentCriticalLength.jac_smul {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {a : Λ} (ha : a ∈ Ring.jacobson Λ) (w : V) : a • w = 0 := by sorry
