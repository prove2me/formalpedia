-- Prove2me | Theorems.Thm_Formalism_NG_epsMap_apply
-- name    : Formalism.NG.epsMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:21.671339+00:00
-- url     : https://prove2.me/theorems/ab8bc984-c304-4992-9d1b-40fa2231552c
-- title:
--   NG: eps Map apply
-- statement:
--   The NG construction uses the eps Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEpsImgEqAdd.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEpsImgEqAdd.lean#L27-L31

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.NG
universe u
variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]

theorem Formalism.NG.epsMap_apply {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A]
    [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) (x : epsImg O (M := A) ε) :
    ((epsMap (O := O) φ ε x : epsImg O (M := B) ε) : B) = φ x := by sorry

attribute [defeq] Formalism.NG.epsMap_apply
