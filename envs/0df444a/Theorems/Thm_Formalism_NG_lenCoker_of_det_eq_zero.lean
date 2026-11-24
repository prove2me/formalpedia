-- Prove2me | Theorems.Thm_Formalism_NG_lenCoker_of_det_eq_zero
-- name    : Formalism.NG.lenCoker_of_det_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:28.646752+00:00
-- url     : https://prove2.me/theorems/bc2fa27e-b0c9-40b8-bb91-8488627dccf4
-- title:
--   NG: len Coker of det eq zero
-- statement:
--   The NG construction uses the len Coker of det eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L109-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L109-L148

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

theorem Formalism.NG.lenCoker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = ⊤ := by sorry
