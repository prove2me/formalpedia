-- Prove2me | Theorems.Thm_Formalism_GM_extendBijOn
-- name    : Formalism.GM.extendBijOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:54.969914+00:00
-- url     : https://prove2.me/theorems/fe6c4bd3-4b7c-4d7a-af53-110068dad2f4
-- title:
--   GM: extend Bij On
-- statement:
--   The GM construction uses the extend Bij On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L403-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L403-L453

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM
open MvPolynomial Finset M.FB

theorem Formalism.GM.extendBijOn : M.FreezeBij := by sorry
