-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- name    : Formalism.GM.M.FB.snoc_vec_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:37.144795+00:00
-- url     : https://prove2.me/theorems/0d489ba0-bcc9-41aa-b98a-7a9420c09a5a
-- title:
--   FB: snoc vec last
-- statement:
--   The FB construction uses the snoc vec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L147-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L147-L148

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
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.snoc_vec_last (LL : Letters N) (n : ℕ) : (LL.snoc n).vec (Fin.last N) = false := by sorry
