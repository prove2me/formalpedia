-- Prove2me | Theorems.Thm_FirstLawThermo_heat_eq_deltaU_of_adynamic
-- name    : FirstLawThermo.heat_eq_deltaU_of_adynamic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:52:27.068626+00:00
-- url     : https://prove2.me/theorems/713a41e8-7df2-4645-a8a3-27bcce756f9b
-- title:
--   In an adynamic process the heat supplied equals $\Delta U$
-- statement:
--   Let $\sigma$ be the state set of a closed system, $U:\sigma\to\mathbb R$ a function, and $p$ an adynamic process, i.e. one with no transfer of energy as work, $W(p)=0$. Then the heat supplied to the system equals the increase of its internal energy:
--   $$Q_U(p)=U(p_{\mathrm{finish}})-U(p_{\mathrm{start}}).$$
--
--   This is the article's statement $Q^{\text{adynamic}}_{A\to B}=\Delta U$, the observable aspect of the first law that concerns heat transfer and is measured by calorimetry.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Evidence for the first law of thermodynamics for closed systems", subsection "Adynamic processes": "When the system evolves with transfer of energy as heat, without energy being transferred as work, in an adynamic process, the heat transferred to the system is equal to the increase in its internal energy: $Q^{\text{adynamic}}_{A\to B}=\Delta U$."

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.heat_eq_deltaU_of_adynamic {σ : Type*} (U : σ → ℝ) (p : Process σ)
    (hp : p.IsAdynamic) :
    heat U p = U p.finish - U p.start := by sorry
