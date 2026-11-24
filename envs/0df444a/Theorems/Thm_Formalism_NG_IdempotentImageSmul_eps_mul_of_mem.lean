-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentImageSmul_eps_mul_of_mem
-- name    : Formalism.NG.IdempotentImageSmul.eps_mul_of_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:42.789129+00:00
-- url     : https://prove2.me/theorems/aeaf162f-dd75-42d6-9afb-b35ee2eaeb3a
-- title:
--   Idempotent Image Smul: eps mul of mem
-- statement:
--   The Idempotent Image Smul construction uses the eps mul of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L30-L33

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
variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)
variable {ε}

theorem Formalism.NG.IdempotentImageSmul.eps_mul_of_mem (hε : IsIdempotentElem ε) (x : epsIdeal O ε) : ε * x.1 = x.1 := by sorry
