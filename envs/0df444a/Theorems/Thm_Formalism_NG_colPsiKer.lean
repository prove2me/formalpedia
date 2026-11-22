-- Prove2me | Theorems.Thm_Formalism_NG_colPsiKer
-- name    : Formalism.NG.colPsiKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:50.583652+00:00
-- url     : https://prove2.me/theorems/330f5627-ae3f-459b-884b-0896892c6766
-- title:
--   NG: col Psi Ker
-- statement:
--   The NG construction uses the col Psi Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockRhoFull.lean#L11-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockRhoFull.lean#L11-L49

import Definitions.Def_Formalism_CharacterColumnKernels_StatementPsi
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.colPsiKer : StatColPsiKer := by sorry
