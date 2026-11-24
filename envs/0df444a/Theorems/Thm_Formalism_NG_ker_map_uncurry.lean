-- Prove2me | Theorems.Thm_Formalism_NG_ker_map_uncurry
-- name    : Formalism.NG.ker_map_uncurry
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:42.10057+00:00
-- url     : https://prove2.me/theorems/f6a6f9b4-28b4-4b6f-b761-487475d1784d
-- title:
--   NG: ker map uncurry
-- statement:
--   The NG construction uses the ker map uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L72-L77

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

theorem Formalism.NG.ker_map_uncurry (Θ : Matrix g g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) Θ)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (matQ O (bigMat ρ Θ)) := by sorry
