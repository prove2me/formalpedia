-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_freeze_inv
-- name    : Formalism.GM.M.FB.freeze_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:38.344416+00:00
-- url     : https://prove2.me/theorems/52d4d2e7-2cac-4a07-ac4b-1bfb4d81ff68
-- title:
--   FB: freeze inv
-- statement:
--   The FB construction uses the freeze inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L265-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L265-L277

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

theorem Formalism.GM.M.FB.freeze_inv (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsFrozenInv p LL ρ n (freeze p LL ρ n f) := by sorry
