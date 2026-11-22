-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
-- name    : Formalism.GM.M.FB.snoc_deg_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:12.322793+00:00
-- url     : https://prove2.me/theorems/65e65391-5a3f-4e40-b0b0-468ea0b1decc
-- title:
--   FB: snoc deg last
-- statement:
--   The FB construction uses the snoc deg last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L154-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L154-L155

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

theorem Formalism.GM.M.FB.snoc_deg_last (LL : Letters N) (n : ℕ) : (LL.snoc n).deg (Fin.last N) = n := by sorry
