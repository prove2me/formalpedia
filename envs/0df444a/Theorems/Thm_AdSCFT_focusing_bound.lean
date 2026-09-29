-- Prove2me | Theorems.Thm_AdSCFT_focusing_bound
-- name    : AdSCFT.focusing_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:02:45.410914+00:00
-- url     : https://prove2.me/theorems/3879440f-0c46-4561-b27e-bf35b45a3e1e
-- title:
--   Integration of the focusing inequality: $L^2 \le 2n/\varphi(0)$
-- statement:
--   This is the integration step (4.9) in the proof of Theorem 4.1 of Anderson, *Geometric aspects of the AdS/CFT correspondence* ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087)), §4: "A simple integration then gives $\rho^2 \le 2n/\varphi(0)$".
--
--   Let $n \ge 1$ and let $\varphi$ be a real function of the distance parameter, differentiable at every point of $[0, L]$ with derivative $\varphi'$, satisfying the focusing inequality (4.7)
--
--   $$\varphi'(\rho) \;\ge\; \frac{\rho\,\varphi(\rho)^2}{n}, \qquad \rho \in [0, L],$$
--
--   and starting from a positive value $\varphi(0) > 0$. The statement asserts
--
--   $$L^2 \;\le\; \frac{2n}{\varphi(0)} .$$
--
--   The content is that a positive initial value makes the focusing inequality blow up in finite parameter time: the profile cannot be defined on an interval longer than $\sqrt{2n/\varphi(0)}$. Applied to $\varphi = -\bar\Delta\rho/\rho$, whose domain of definition is the full range of the distance function, this is what bounds the distance of any point of $M$ to the boundary.
--
--   **Formalization Note** The hypotheses are stated for the closed interval $[0, L]$, with the derivative required to exist in the two-sided sense at each of its points, including the endpoints; $L \ge 0$ is assumed and $L = 0$ is allowed, in which case the conclusion is trivial. The dimension $n$ is a positive natural number coerced to a real number, and the bound $2n/\varphi(0)$ is a genuine division of real numbers with a positive denominator.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, p. 14, Section 4, proof of Theorem 4.1, equation (4.9)

import Definitions.Def_AdSCFTFocusingProfiles

namespace AdSCFT

theorem focusing_bound (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L) (phi phi' : ℝ → ℝ)
    (hpos : 0 < phi 0) (hprofile : FocusingProfileAH n L phi phi') :
    L ^ 2 ≤ 2 * n / phi 0 := by sorry

end AdSCFT
