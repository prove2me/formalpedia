-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_ev_freeze
-- name    : Formalism.GM.M.FB.ev_freeze
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:12.849503+00:00
-- url     : https://prove2.me/theorems/58ac7012-0f6f-49c6-9eea-162e6f0f279d
-- title:
--   FB: ev freeze
-- statement:
--   The FB construction uses the ev freeze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L32-L40

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

theorem Formalism.GM.M.FB.ev_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ev p ρ (freeze p LL ρ n f) = f := by sorry
