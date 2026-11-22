-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_weight_wL
-- name    : Formalism.GM.M.FB.weight_wL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:53.543662+00:00
-- url     : https://prove2.me/theorems/a05e9061-c874-49a7-a6ef-5d657135f502
-- title:
--   FB: weight w L
-- statement:
--   The FB construction uses the weight w L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L195-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L195-L199

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
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.weight_wL (m : Fin (N + 1) × Fin r →₀ ℕ) :
    Finsupp.weight (wL N r) m = ∑ c, m (Fin.last N, c) := by sorry
