-- Prove2me | Theorems.Thm_AdSCFT_focusing_of_riccati
-- name    : AdSCFT.focusing_of_riccati
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:44:05.210067+00:00
-- url     : https://prove2.me/theorems/6f1eb776-5a8b-40dd-82c6-fccae1dd0040
-- title:
--   Riccati equation implies the focusing inequality $\varphi' \ge \rho\varphi^2/n$
-- statement:
--   This is the reduction step of Anderson, *Geometric aspects of the AdS/CFT correspondence* ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087)), §4: equations (4.3)–(4.7) of the proof of Theorem 4.1.
--
--   Along the $\bar g$-geodesics normal to the boundary component $\partial_0 M$, the mean curvature $H = \bar\Delta\rho$ of the level set $S(\rho)$, the squared norm $|K|^2 = |\bar D^2\rho|^2$ of the second fundamental form, and the energy term $S = (\mathrm{Ric}_g + n g)(T, T)$ obey the Riccati equation (4.3) in the form
--
--   $$H'(\rho) + |K|^2(\rho) - \frac{H(\rho)}{\rho} + \frac{S(\rho)}{\rho^2} \;=\; 0 ,$$
--
--   with $|K|^2 \ge H^2/n$ by Cauchy–Schwarz and $S \ge 0$ by the curvature hypothesis (4.1).
--
--   The statement asserts that, for $\varphi(\rho) = -H(\rho)/\rho$ differentiable on $(0, L)$ with derivative $\varphi'$, these three facts imply the focusing inequality (4.7)
--
--   $$\varphi'(\rho) \;\ge\; \frac{\rho\,\varphi(\rho)^2}{n}, \qquad \rho \in (0, L).$$
--
--   This is the step that converts the second-order geometry of the normal geodesics into the single scalar differential inequality on which the distance estimate rests; it is reusable for any comparison argument of Riccati type.
--
--   **Formalization Note** The Riccati equation, the Cauchy–Schwarz bound and the non-negativity of the energy term are supplied as a bundle of hypotheses on real functions of $\rho$, and $\varphi$ is required to agree with $-H(\rho)/\rho$ at every real $\rho$, with its derivative named separately. The dimension $n$ is a positive natural number coerced to a real number; the interval is open at both ends, so $\rho = 0$, where $-H(\rho)/\rho$ is not defined by the formula, is excluded.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, pp. 13-14, Section 4, proof of Theorem 4.1, equations (4.3)-(4.7)

import Definitions.Def_AdSCFTFocusingProfiles

namespace AdSCFT

theorem focusing_of_riccati (n : ℕ) (hn : 0 < n) (L : ℝ) (D : RiccatiData n L)
    (phi phi' : ℝ → ℝ) (hphi : ∀ r, phi r = -D.H r / r)
    (hphi' : ∀ r ∈ Set.Ioo (0 : ℝ) L, HasDerivAt phi (phi' r) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) L, r * (phi r) ^ 2 / n ≤ phi' r := by sorry

end AdSCFT
