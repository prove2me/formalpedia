-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_last
-- name    : Formalism.GM.FrozenVariableLemmas.snoc_vec_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:38.573775+00:00
-- url     : https://prove2.me/theorems/0eff475b-12e5-49ac-ab66-b854abd8204e
-- title:
--   Frozen Variable Lemmas: snoc vec last
-- statement:
--   The Frozen Variable Lemmas construction uses the snoc vec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L160-L162

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset

theorem Formalism.GM.FrozenVariableLemmas.snoc_vec_last {N : ℕ} (LL : M.Letters N) (n : ℕ) :
    (LL.snoc n).vec (Fin.last N) = false := by sorry
