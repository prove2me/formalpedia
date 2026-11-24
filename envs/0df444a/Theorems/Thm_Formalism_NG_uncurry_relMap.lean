-- Prove2me | Theorems.Thm_Formalism_NG_uncurry_relMap
-- name    : Formalism.NG.uncurry_relMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:54.478736+00:00
-- url     : https://prove2.me/theorems/6bc75735-1959-42a0-a60c-8c65517a5f90
-- title:
--   NG: uncurry rel Map
-- statement:
--   The NG construction uses the uncurry rel Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L61-L70

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)
variable [SMulCommClass R O (LatQ O d ρ)]

theorem Formalism.NG.uncurry_relMap (Θ : Matrix g g R) (v : g → LatQ O d ρ) :
    uncurryEquiv ρ (relMap O (LatQ O d ρ) Θ v) = matQ O (bigMat ρ Θ) (uncurryEquiv ρ v) := by sorry
