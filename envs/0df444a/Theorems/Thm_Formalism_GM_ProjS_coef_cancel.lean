-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_coef_cancel
-- name    : Formalism.GM.ProjS.coef_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:09.673621+00:00
-- url     : https://prove2.me/theorems/c835f641-86d0-46af-9c4a-832194aa2b78
-- title:
--   Proj S: coef cancel
-- statement:
--   The Proj S construction uses the coef cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L641-L677
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L641-L677

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset

theorem Formalism.GM.ProjS.coef_cancel {k : Type} [Field k] [CharZero k] (o n r z j : ℕ) (hr : 1 ≤ r) (hj : j < o) :
    ((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((o + n + r + z - 1).choose j : k)) +
      ((-1 : k) ^ (j + 1)) / ((((j + 1).factorial : k) ^ 2) * ((o + n + r + z - 1).choose (j + 1) : k)) *
        (((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
          ((r + 1 : ℕ) : k) + j)) = 0 := by sorry
