-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
-- name    : Eden.asymptoticDimension_periodic_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:40.622802+00:00
-- url     : https://prove2.me/theorems/dfb88446-5bb6-439c-a27c-0b000e6be26f
-- title:
--   Eden: asymptotic Dimension periodic is Greatest
-- statement:
--   The largest limiting Kaplan--Yorke dimension over all periodic points and
--   equilibria in the attractor is three, attained on a unit circle.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L18-L26
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L18-L26

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 := by sorry
