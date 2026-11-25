-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentImageSmul_fwd_bwd
-- name    : Formalism.NG.IdempotentImageSmul.fwd_bwd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:31.096259+00:00
-- url     : https://prove2.me/theorems/70d5688f-1e78-4918-9565-8074a6d83aed
-- title:
--   Idempotent Image Smul: fwd bwd
-- statement:
--   The Idempotent Image Smul construction uses the fwd bwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean#L105-L112

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

theorem Formalism.NG.IdempotentImageSmul.fwd_bwd (hε : IsIdempotentElem ε) (ψ : epsImg O (M := M) ε →ₗ[O] Q) :
    fwd ε (bwd ε ψ) = ψ := by sorry
