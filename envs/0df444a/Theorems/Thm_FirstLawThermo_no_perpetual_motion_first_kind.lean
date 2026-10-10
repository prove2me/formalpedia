-- Prove2me | Theorems.Thm_FirstLawThermo_no_perpetual_motion_first_kind
-- name    : FirstLawThermo.no_perpetual_motion_first_kind
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:54:40.689779+00:00
-- url     : https://prove2.me/theorems/0aad5dc2-9211-4bb7-bcd9-56d2a7015903
-- title:
--   No perpetual motion machine of the first kind
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $U$ be an internal energy for $\mathcal P$. If $p\in\mathcal P$ is adiabatic and cyclic ($p_{\mathrm{start}}=p_{\mathrm{finish}}$), then the system does no net work:
--   $$W(p)=0.$$
--
--   This is the impossibility of a perpetual motion machine of the first kind: no engine working in a cycle can produce net work "from nothing", that is, without energy being resupplied as heat.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; lead section: "An equivalent statement is that perpetual motion machines of the first kind are impossible; work done by a system on its surroundings requires that the system's internal energy be consumed ..."; Section "Various statements of the law for closed systems": Planck (1897/1903) "it is impossible to construct an engine which will work in a cycle and produce continuous work, or kinetic energy, from nothing."

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.no_perpetual_motion_first_kind {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (p : Process σ) (hp : p ∈ procs)
    (had : p.adiabatic) (hcyc : p.IsCyclic) :
    p.work = 0 := by sorry
