-- Prove2me | Theorems.Thm_Formalism_NG_splitAlg
-- name    : Formalism.NG.splitAlg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:48.694703+00:00
-- url     : https://prove2.me/theorems/017f8416-4285-56a5-b627-d0a8a1d0ac39
-- title:
--   NG: split Alg
-- statement:
--   The NG construction uses the split Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SplitFibre.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SplitFibre.lean#L139-L148

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SplitFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
universe u

theorem Formalism.NG.splitAlg : StatSplitAlg := by sorry
