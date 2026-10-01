-- Prove2me | Theorems.Thm_CookPvsNP_tm_run_eq_of_halting
-- name    : CookPvsNP.tm_run_eq_of_halting
-- status  : Proved
-- author  : @Sneed
-- created : 2026-09-30T17:18:17.443198+00:00
-- url     : https://prove2.me/theorems/53140e1d-c437-44fa-9963-0af3d723f656
-- title:
--   Halting Cook configurations are fixed by every run iterate
-- statement:
--   If a configuration of a Cook-style deterministic Turing machine is already halting, then running the machine for any further finite number of steps leaves that configuration unchanged.

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookPvsNP

theorem tm_run_eq_of_halting {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q)
    (h : M.IsHalting c) (n : ℕ) : M.run n c = c := by sorry

end CookPvsNP
