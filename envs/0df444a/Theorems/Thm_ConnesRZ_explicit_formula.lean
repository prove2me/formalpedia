-- Prove2me | Theorems.Thm_ConnesRZ_explicit_formula
-- name    : ConnesRZ.explicit_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T13:02:47.978355+00:00
-- url     : https://prove2.me/theorems/57f950e0-75ff-4e78-8619-c0ced98597f5
-- title:
--   Riemann--Weil explicit formula for $\zeta$ (Connes eq. (11), $k=\mathbb{Q}$)
-- statement:
--   **The explicit formula.** For every smooth compactly supported $g:\mathbb{R}\to\mathbb{C}$, the family
--   $$\rho\;\longmapsto\;m_{\rho}\,\widehat g(\rho),\qquad \rho \text{ a zero of }\zeta \text{ with } 0<\operatorname{Re}\rho<1,\ m_\rho \text{ its multiplicity},$$
--   is summable, and
--   $$\sum_{\rho} m_{\rho}\,\widehat g(\rho)\;=\;\widehat g(0)+\widehat g(1)-\sum_{n\ge 2}\frac{\Lambda(n)}{\sqrt n}\bigl(g(\log n)+g(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb{R}}\widehat g\!\left(\tfrac12+ir\right)\left(\operatorname{Re}\psi\!\left(\tfrac14+\tfrac{ir}{2}\right)-\log\pi\right)dr,$$
--   where $\widehat g(z)=\int_{\mathbb{R}}g(t)e^{(z-1/2)t}\,dt$, $\Lambda$ is the von Mangoldt function and $\psi=\Gamma'/\Gamma$.
--
--   This is eq. (11) of the paper,
--   $$\sum_{L(\chi,\rho)=0}\widehat h(\chi,\rho)-\widehat h(0)-\widehat h(1)=-\sum_{v}\int'_{k_v^{*}}\frac{h(u^{-1})}{|1-u|}\,d^{*}u ,$$
--   for $k=\mathbb{Q}$ and trivial Grössencharakter: the sum over the finite places $v=p$ is the prime-power sum, and the local term at the real place is written here through $\Gamma'/\Gamma$ rather than as Weil's principal value. Both sides of the displayed identity have been checked numerically for a smooth bump test function, using the first $300$ zeros of $\zeta$, to a relative agreement of about $10^{-8}$.
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, in: Mathematics: Frontiers and Perspectives, AMS (2000); section 3 "Weil positivity and the Trace formula", pp. 13-22. Transform: eq. (12), p. 15. Explicit formula: eq. (11), p. 15. Positivity/RH equivalence: concluding paragraph, p. 22. Specialised throughout to the global field k = Q with trivial Grossencharakter, so that the L-function is the Riemann zeta function.

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

open Complex

namespace ConnesRZ

theorem explicit_formula (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} => (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1)
      (weilDistribution g) := by sorry

end ConnesRZ
