-- Prove2me | Theorems.Thm_ConnesRZ_mellinHat_conv_starInv_critical
-- name    : ConnesRZ.mellinHat_conv_starInv_critical
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:59:28.471105+00:00
-- url     : https://prove2.me/theorems/8596fb99-12fa-4094-a40c-1e79fda330dc
-- title:
--   On the critical line, $\widehat{g \star g^{*}} = |\widehat{g}|^{2}$
-- statement:
--   For a test function $g$ and a real number $r$,
--   $$\widehat{g\star g^{*}}\!\left(\tfrac12+ir\right)\;=\;\left|\widehat g\!\left(\tfrac12+ir\right)\right|^{2},$$
--   where $\widehat g(z)=\int_{\mathbb{R}}g(t)e^{(z-1/2)t}dt$ and $g^{*}(t)=\overline{g(-t)}$.
--
--   This is the reason positivity is a statement about the critical line: the transform turns convolution into multiplication and the involution into conjugation, but the two only combine into a square modulus at points $z$ with $z=1-\bar z$, i.e. exactly on $\operatorname{Re}z=\tfrac12$. It is the elementary counterpart, for $k=\mathbb{Q}$ and trivial Grössencharakter, of the positivity of the trace of a $*$-square used in section 3 of the paper.
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, in: Mathematics: Frontiers and Perspectives, AMS (2000); section 3 "Weil positivity and the Trace formula", pp. 13-22. Transform: eq. (12), p. 15. Explicit formula: eq. (11), p. 15. Positivity/RH equivalence: concluding paragraph, p. 22. Specialised throughout to the global field k = Q with trivial Grossencharakter, so that the L-function is the Riemann zeta function.

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

open Complex

namespace ConnesRZ

theorem mellinHat_conv_starInv_critical (g : ℝ → ℂ) (hg : IsTest g) (r : ℝ) :
    mellinHat (conv g (starInv g)) (1 / 2 + I * r) =
      ((‖mellinHat g (1 / 2 + I * r)‖ ^ 2 : ℝ) : ℂ) := by sorry

end ConnesRZ
