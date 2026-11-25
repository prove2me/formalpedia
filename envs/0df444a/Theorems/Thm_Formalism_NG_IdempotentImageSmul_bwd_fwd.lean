-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentImageSmul_bwd_fwd
-- name    : Formalism.NG.IdempotentImageSmul.bwd_fwd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:38.223578+00:00
-- url     : https://prove2.me/theorems/6184e43e-6c9b-4f80-84cc-2a19ee5564a5
-- title:
--   Idempotent Image Smul: bwd fwd
-- statement:
--   The Idempotent Image Smul construction uses the bwd fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L92-L103

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
variable (ε) [SMulCommClass OO O (EpsDual O OO Q ε)]
variable {ε}

theorem Formalism.NG.IdempotentImageSmul.bwd_fwd (hε : IsIdempotentElem ε) (Φ : M →ₗ[OO] EpsDual O OO Q ε) :
    bwd ε (fwd ε Φ) = Φ := by sorry
