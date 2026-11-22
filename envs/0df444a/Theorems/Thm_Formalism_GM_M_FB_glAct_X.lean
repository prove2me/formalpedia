-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_glAct_X
-- name    : Formalism.GM.M.FB.glAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:46.489775+00:00
-- url     : https://prove2.me/theorems/64ed8b7a-aea3-4ebd-be8e-a5f70cb277d5
-- title:
--   FB: gl Act X
-- statement:
--   The FB construction uses the gl Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L135-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L135-L145

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

theorem Formalism.GM.M.FB.glAct_X {M : ℕ} (LL : Letters M) (c d : Fin r) (j : Fin M) (a : Fin r) :
    glAct p LL M c d (X (j, a)) =
      if LL.vec j then (if a = d then X (j, c) else 0) else (if a = c then -X (j, d) else 0) := by sorry
