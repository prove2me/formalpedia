-- Prove2me | Theorems.Thm_ConnesRZ_weil_positivity_of_RH
-- name    : ConnesRZ.weil_positivity_of_RH
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T13:06:39.76044+00:00
-- url     : https://prove2.me/theorems/cc989399-02ab-4a37-a06c-bed0555b8a9a
-- title:
--   RH implies positivity of the Weil distribution
-- statement:
--   **Converse direction of the equivalence.** Assume the Riemann hypothesis: every zero $\rho$ of $\zeta$ with $0<\operatorname{Re}\rho<1$ satisfies $\operatorname{Re}\rho=\tfrac12$. Then for every smooth compactly supported $g:\mathbb{R}\to\mathbb{C}$,
--   $$\operatorname{Re}\,W\bigl(g\star g^{*}\bigr)\;\ge\;0,$$
--   where $W$ is the Weil distribution of the mission's definition bundle and $g^{*}(t)=\overline{g(-t)}$.
--
--   Together with the goal theorem of the mission this is the equivalence asserted on p. 22 of the paper — "the validity of this trace formula implies (in fact is equivalent to) the positivity of the Weil distribution, i.e. RH" — in the case $k=\mathbb{Q}$, trivial Grössencharakter. Under RH every zero contributes $m_\rho|\widehat g(\rho)|^{2}\ge 0$ to the spectral side, so the statement follows from the explicit formula together with the $*$-identity on the critical line.
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, in: Mathematics: Frontiers and Perspectives, AMS (2000); section 3 "Weil positivity and the Trace formula", pp. 13-22. Transform: eq. (12), p. 15. Explicit formula: eq. (11), p. 15. Positivity/RH equivalence: concluding paragraph, p. 22. Specialised throughout to the global field k = Q with trivial Grossencharakter, so that the L-function is the Riemann zeta function.

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

open Complex

namespace ConnesRZ

theorem weil_positivity_of_RH (hRH : ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2)
    (g : ℝ → ℂ) (hg : IsTest g) :
    0 ≤ (weilDistribution (conv g (starInv g))).re := by sorry

end ConnesRZ
