-- Prove2me | Theorems.Thm_BoundedNV_Uniform_optimum_eq_mu
-- name    : BoundedNV.Uniform.optimum_eq_mu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:34.128234+00:00
-- url     : https://prove2.me/theorems/6e12e9ec-6969-4db8-b73c-e4226589c101
-- title:
--   §4, p. 572, and p. 573 — under uniform demand π is uniquely maximized at x* = F⁻¹(1 − c/p) = μ
-- statement:
--   Let the demand $D$ be uniformly distributed on $[a, b]$ with $b > a \ge 0$, and let $0 < c < p$. Write $\pi(x) = p\,\mathbb E\min(D,x) - cx$ and
--   $$\mu = b - \frac{c}{p}(b-a).$$
--   Then:
--   1. $\pi(\mu) \ge \pi(x)$ for every real $x$;
--   2. every maximizer of $\pi$ over $\mathbb R$ equals $\mu$;
--   3. $F(\mu) = 1 - c/p$, where $F$ is the distribution function of $D$, i.e. $\mu = F^{-1}(\xi)$ with critical fractile $\xi = 1 - c/p$.
--
--   This is the uniform case of the paper's statement that $\pi$ is uniquely maximized at $x^* = F^{-1}(\xi)$, together with the remark (p. 573) that the parameter $\mu$ of the behavioral solution coincides with the optimal solution $x^*$. It turns the hypothesis "$x^*$ is the optimal solution" of Proposition 3 into the closed form $\mu$ and shows that this hypothesis can be met.
--
--   **Formalization Note** The optimum is taken over all real order quantities. The hypothesis $c > 0$ (with $c < p$) is the reading under which $x^* = F^{-1}(1 - c/p)$ lies in $(a, b)$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 572 (PDF 7), §4 after eq. (3), and p. 573 (PDF 8), remark after Corollary 1

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

namespace BoundedNV.Uniform

/-- §4, p. 572, and p. 573: for demand `D ∼ U[a, b]` with `0 ≤ a < b` and `0 < c < p`, the expected
profit (3) is maximized over all of `ℝ` at `μ = b − (c/p)(b − a)`, it has no other maximizer, and
`μ` is the critical fractile `F⁻¹(1 − c/p)` of the demand distribution. -/
theorem optimum_eq_mu (a b p c : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    IsMaxOn (nvProfit (unifDensity a b) p c) Set.univ (unifMu a b p c) ∧
      (∀ x, IsMaxOn (nvProfit (unifDensity a b) p c) Set.univ x → x = unifMu a b p c) ∧
      demandCDF (unifDensity a b) (unifMu a b p c) = 1 - c / p := by sorry

end BoundedNV.Uniform
