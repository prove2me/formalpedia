-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_glAct_mul
-- name    : Formalism.GM.M.FB.glAct_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:05.078791+00:00
-- url     : https://prove2.me/theorems/8d9c2312-91ca-4731-bf00-4e7f386c94cf
-- title:
--   FB: gl Act mul
-- statement:
--   The FB construction uses the gl Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L127-L133

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

theorem Formalism.GM.M.FB.glAct_mul {M : ℕ} (LL : Letters M) (j : ℕ) (c d : Fin r)
    (a b : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    glAct p LL j c d (a * b) = a * glAct p LL j c d b + b * glAct p LL j c d a := by sorry
