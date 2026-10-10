-- Prove2me | Theorems.Thm_FirstLawThermo_work_eq_heat_of_cyclic
-- name    : FirstLawThermo.work_eq_heat_of_cyclic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:53:34.561585+00:00
-- url     : https://prove2.me/theorems/22eb26cc-21ef-4268-849d-4dae493b1d62
-- title:
--   Over a cycle, net work done equals net heat taken in
-- statement:
--   Let $\sigma$ be the state set of a closed system, $U:\sigma\to\mathbb R$ a function, and $p$ a cyclic process, i.e. one returning the system to its initial state: $p_{\mathrm{start}}=p_{\mathrm{finish}}$. Then the net work done by the system equals the net heat taken in:
--   $$W(p)=Q_U(p).$$
--
--   This is Clausius' cyclic form of the first law: in each repetition of a cyclic process, the net work done by the system is proportional to the heat consumed (equal, when heat and work are measured in the same units).
--
--   **Formalization Note** Heat and work are measured in the same units, so Joule's mechanical equivalent of heat is normalized to $1$.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Description", subsection "Cyclic processes": "A cyclic process is one that can be repeated indefinitely often, returning the system to its initial state. Of particular interest for single cycle of a cyclic process are the net work done, and the net heat taken in ... In each repetition of a cyclic process, the net work done by the system, measured in mechanical units, is proportional to the heat consumed, measured in calorimetric units."; Section "Original statements": Clausius, "a quantity of heat is consumed which is proportional to the work done".

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.work_eq_heat_of_cyclic {σ : Type*} (U : σ → ℝ) (p : Process σ)
    (hcyc : p.IsCyclic) :
    p.work = heat U p := by sorry
