-- Prove2me | Theorems.Thm_Formalism_NG_genfin_det_totalDegree
-- name    : Formalism.NG.genfin_det_totalDegree
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:03.844883+00:00
-- url     : https://prove2.me/theorems/3114e9c9-0d6a-4c54-9569-3ec2249914a5
-- title:
--   NG: genfin det total Degree
-- statement:
--   The NG construction uses the genfin det total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L14-L27

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.genfin_det_totalDegree {ι K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι K)) (h : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ Fintype.card n := by sorry
