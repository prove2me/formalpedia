-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_glAct_aeval_freezeSub
-- name    : Formalism.GM.M.FB.glAct_aeval_freezeSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:58.638136+00:00
-- url     : https://prove2.me/theorems/ca45e631-3acd-4006-a629-ab9ee022c58f
-- title:
--   FB: gl Act aeval freeze Sub
-- statement:
--   The FB construction uses the gl Act aeval freeze Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L168-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L168-L181

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

theorem Formalism.GM.M.FB.glAct_aeval_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (N + 1) c ρ (aeval (freezeSub p LL ρ) f) = 0 := by sorry
