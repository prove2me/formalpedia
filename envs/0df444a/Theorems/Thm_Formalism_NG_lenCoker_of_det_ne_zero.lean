-- Prove2me | Theorems.Thm_Formalism_NG_lenCoker_of_det_ne_zero
-- name    : Formalism.NG.lenCoker_of_det_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:57.579843+00:00
-- url     : https://prove2.me/theorems/09899df5-83b1-4e37-bd33-0e81f800c0e2
-- title:
--   NG: len Coker of det ne zero
-- statement:
--   The NG construction uses the len Coker of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L92-L102

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.NG.lenCoker_of_det_ne_zero (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = addVal O A.det := by sorry
