-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
-- name    : Formalism.GM.M.FB.snoc_vec_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:08.925795+00:00
-- url     : https://prove2.me/theorems/476856f0-16dd-496f-8907-070ddc66fa88
-- title:
--   FB: snoc vec cast Succ
-- statement:
--   The FB construction uses the snoc vec cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L150-L152

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

theorem Formalism.GM.M.FB.snoc_vec_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by sorry
