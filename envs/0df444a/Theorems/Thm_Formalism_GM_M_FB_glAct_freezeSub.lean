-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_glAct_freezeSub
-- name    : Formalism.GM.M.FB.glAct_freezeSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:57.267809+00:00
-- url     : https://prove2.me/theorems/e7e1a161-d8f1-408c-ba87-ebe08782969e
-- title:
--   FB: gl Act freeze Sub
-- statement:
--   The FB construction uses the gl Act freeze Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L161-L166

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

theorem Formalism.GM.M.FB.glAct_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ) (v : Fin N × Fin r) :
    glAct p (LL.snoc n) (N + 1) c ρ (freezeSub p LL ρ v) = 0 := by sorry
