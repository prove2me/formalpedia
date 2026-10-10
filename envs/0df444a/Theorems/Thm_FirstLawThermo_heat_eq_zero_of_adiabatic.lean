-- Prove2me | Theorems.Thm_FirstLawThermo_heat_eq_zero_of_adiabatic
-- name    : FirstLawThermo.heat_eq_zero_of_adiabatic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:51:12.531479+00:00
-- url     : https://prove2.me/theorems/664fd409-e9f1-492c-b244-079e516d707d
-- title:
--   No heat is exchanged in an adiabatic process
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $U$ be an internal energy for $\mathcal P$. For every adiabatic process $p\in\mathcal P$, the heat supplied vanishes:
--   $$Q_U(p)=0.$$
--
--   This is the consistency of the residual definition of heat with the meaning of "adiabatic": in an adiabatic process there is transfer of energy as work but not as heat.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Evidence for the first law of thermodynamics for closed systems": adiabatic processes are those "in which there is no transfer as heat"; subsection "Adiabatic processes": "In an adiabatic process, there is transfer of energy as work but not as heat."

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.heat_eq_zero_of_adiabatic {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (p : Process σ) (hp : p ∈ procs)
    (had : p.adiabatic) :
    heat U p = 0 := by sorry
