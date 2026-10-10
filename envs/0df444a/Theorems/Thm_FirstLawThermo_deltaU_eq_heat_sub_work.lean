-- Prove2me | Theorems.Thm_FirstLawThermo_deltaU_eq_heat_sub_work
-- name    : FirstLawThermo.deltaU_eq_heat_sub_work
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:50:45.376974+00:00
-- url     : https://prove2.me/theorems/048fe3ce-9805-4b31-9221-2bbfdffb1043
-- title:
--   Clausius form of the first law: $\Delta U = Q - W$
-- statement:
--   Let $\sigma$ be the state set of a closed system, $U:\sigma\to\mathbb R$ a function, and $p$ any process, with work $W(p)$ done by the system. With the heat supplied defined as the residual $Q_U(p)=U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})+W(p)$,
--   $$U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})=Q_U(p)-W(p).$$
--
--   This is the first law in the sign convention of Clausius, $\Delta U=Q-W$: heat supplied to the system counts as positive and work done by the system is subtracted. In the mechanical approach followed here it holds for every process, because heat is defined as the part of the change of internal energy not accounted for by work.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Definition": "With the sign convention of Rudolf Clausius, that heat supplied to the system is positive, but work done by the system is subtracted, a change in the internal energy, $\Delta U$, is written $\Delta U = Q - W$."; Section "Various statements of the law for closed systems": heat "is defined as a residual difference between change of internal energy and work done on the system".

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.deltaU_eq_heat_sub_work {σ : Type*} (U : σ → ℝ) (p : Process σ) :
    U p.finish - U p.start = heat U p - p.work := by sorry
