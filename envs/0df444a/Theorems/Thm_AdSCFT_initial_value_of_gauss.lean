-- Prove2me | Theorems.Thm_AdSCFT_initial_value_of_gauss
-- name    : AdSCFT.initial_value_of_gauss
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:12:12.485582+00:00
-- url     : https://prove2.me/theorems/7c1fdfc7-322b-4f34-9c11-43db3e6e8b39
-- title:
--   Initial value (4.8): $(n-1)\varphi(0) = \tfrac12 R_\gamma$ gives $\varphi(0)>0$
-- statement:
--   This records the consequence of the initial-value identity (4.8) used at the end of the proof of Theorem 4.1 of Anderson, *Geometric aspects of the AdS/CFT correspondence* ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087)), §4.
--
--   The Gauss equation at the boundary, together with the vanishing of the second fundamental form of $\partial_0 M$ in the compactification and the decay hypothesis $|\mathrm{Ric}_g + n g| = o(\rho^2)$, gives
--
--   $$(n-1)\,\varphi(0) \;=\; \tfrac12 R_\gamma ,$$
--
--   where $\varphi(\rho) = -\bar\Delta\rho/\rho$ and $R_\gamma$ is the (constant) scalar curvature of the boundary metric.
--
--   The statement asserts, for $n \ge 2$, $R_\gamma > 0$ and a real number $c$ with $(n-1)c = \tfrac12 R_\gamma$, the two conclusions
--
--   1. $c > 0$; and
--   2. $\dfrac{2n}{c} \;=\; \dfrac{4n(n-1)}{R_\gamma}$.
--
--   The first is the positivity of $\varphi(0)$ that the integration step (4.9) requires, and the second is the arithmetic that turns the bound $2n/\varphi(0)$ into the constant $4n(n-1)/R_\gamma$ appearing in estimate (4.2).
--
--   **Formalization Note** The hypothesis $n \ge 2$ is needed to make $n - 1$ positive; the identity is stated with $n$ a natural number coerced to a real number, and $c$ an arbitrary real number rather than the value of a function.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, p. 14, Section 4, proof of Theorem 4.1, equation (4.8) and the constant in estimate (4.2)

import Definitions.Def_AdSCFTFocusingProfiles

namespace AdSCFT

theorem initial_value_of_gauss (n : ℕ) (hn : 2 ≤ n) (Rgamma c : ℝ) (hR : 0 < Rgamma)
    (hc : ((n : ℝ) - 1) * c = Rgamma / 2) :
    0 < c ∧ 2 * n / c = 4 * n * ((n : ℝ) - 1) / Rgamma := by sorry

end AdSCFT
