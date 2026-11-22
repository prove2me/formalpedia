-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
-- name    : Formalism.GM.M.FB.evVal_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:15.790797+00:00
-- url     : https://prove2.me/theorems/3bcbfa56-55c1-4478-b609-9778ac95cbb1
-- title:
--   FB: ev Val cast Succ
-- statement:
--   The FB construction uses the ev Val cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L22-L24

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

theorem Formalism.GM.M.FB.evVal_castSucc (ρ c : Fin r) (i : Fin N) :
    evVal p ρ (Fin.castSucc i, c) = X (i, c) := by sorry
