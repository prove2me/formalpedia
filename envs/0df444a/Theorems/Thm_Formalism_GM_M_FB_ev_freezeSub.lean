-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_ev_freezeSub
-- name    : Formalism.GM.M.FB.ev_freezeSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:02.39765+00:00
-- url     : https://prove2.me/theorems/256da75b-2f68-47c9-aa83-a44358831599
-- title:
--   FB: ev freeze Sub
-- statement:
--   The FB construction uses the ev freeze Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L26-L30

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

theorem Formalism.GM.M.FB.ev_freezeSub (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    ev p ρ (freezeSub p LL ρ v) = X v := by sorry
