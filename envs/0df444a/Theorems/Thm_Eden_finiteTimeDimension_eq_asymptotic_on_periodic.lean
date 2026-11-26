-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_eq_asymptotic_on_periodic
-- name    : Eden.finiteTimeDimension_eq_asymptotic_on_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:09.127562+00:00
-- url     : https://prove2.me/theorems/233782f9-ba8c-4a7a-a490-a12cc940e03d
-- title:
--   Eden: finite Time Dimension eq asymptotic on periodic
-- statement:
--   Both dimensions agree at every positive time throughout the periodic/equilibrium
--   set, using the ordered singular-value exponents.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L80-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L80-L88

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_eq_asymptotic_on_periodic {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) :
    finiteTimeDimension c t p = asymptoticDimension c p := by sorry
