-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_evVal_last
-- name    : Formalism.GM.M.FB.evVal_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:55.263669+00:00
-- url     : https://prove2.me/theorems/b5f99202-98a3-4f3a-9b22-f14b4653cfae
-- title:
--   FB: ev Val last
-- statement:
--   The FB construction uses the ev Val last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L18-L20

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

theorem Formalism.GM.M.FB.evVal_last (ρ c : Fin r) :
    evVal p (N := N) ρ (Fin.last N, c) = if c = ρ then 1 else 0 := by sorry
