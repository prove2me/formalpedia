-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_kappa_strictAntiOn
-- name    : FVRPricing.DecayBalancing.kappa_strictAntiOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:17.275284+00:00
-- url     : https://prove2.me/theorems/ff6a2d64-09dc-4d6f-8e4b-be5aae231664
-- title:
--   §6 and §6.2 — $\kappa(a)$ is decreasing in $a$
-- statement:
--   The function
--   $$\kappa(a) = \frac{a\Gamma(a)}{\Gamma(a+1)-\Gamma(a+1,a)+a\Gamma(a,a)}$$
--   is strictly decreasing on $(0,\infty)$.
--
--   Consequently the bounds of Theorem 2 improve along every sample path, since the shape parameter $a_t = a + n_t$ only grows; Theorem 3 uses $\kappa(a+1)\le\kappa(1)$.
--
--   **Formalization Note** The paper says "decreasing"; numerically $\kappa(0.5)\approx1.94$, $\kappa(1)\approx1.58$, $\kappa(2)\approx1.37$, $\kappa(10)\approx1.14$, and the decrease is strict, which is what is stated.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 18, §6 overview ("κ(·) is a certain decreasing function"), and p. 21, §6.2 ("since κ(a) is decreasing in a")

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies
import Definitions.Def_FVRPricing_DecayBalancing_Kappa

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem kappa_strictAntiOn : StrictAntiOn kappa (Set.Ioi 0) := by sorry

end FVRPricing.DecayBalancing
