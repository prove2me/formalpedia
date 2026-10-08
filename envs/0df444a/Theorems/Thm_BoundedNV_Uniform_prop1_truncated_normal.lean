-- Prove2me | Theorems.Thm_BoundedNV_Uniform_prop1_truncated_normal
-- name    : BoundedNV.Uniform.prop1_truncated_normal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:33.554633+00:00
-- url     : https://prove2.me/theorems/160018a3-7503-4da8-9fe5-155dd69fb19b
-- title:
--   Proposition 1, pp. 572–573 — under uniform demand the behavioral solution is truncated normal on [a, b]
-- statement:
--   Let the demand $D$ be uniformly distributed on $[a, b]$ with $b > a \ge 0$, let $0 < c < p$, and let $\beta > 0$. The behavioral solution $X^\flat$ of the newsvendor problem has the logit density over $S = [a, b]$,
--   $$\psi(x) = \frac{e^{\pi(x)/\beta}}{\int_a^b e^{\pi(v)/\beta}\,dv}\ \ (x \in [a,b]), \qquad \psi(x) = 0 \ \ (x \notin [a,b]),$$
--   with $\pi(x) = p\,\mathbb E\min(D,x) - cx$. Then for every real $x$,
--   $$\psi(x) = \zeta(x),$$
--   where $\zeta$ is the density of the normal law with parameters
--   $$\mu = b - \frac{c}{p}(b-a), \qquad \sigma^2 = \beta\,\frac{b-a}{p},$$
--   truncated to $[a, b]$.
--
--   So under uniform demand the boundedly rational order is a truncated normal random variable whose location parameter is the optimal order and whose scale grows with $\beta$ and with the demand range.
--
--   **Formalization Note** The paper says the truncated normal has "mean $\mu$ and variance $\sigma^2$". These are the parameters of the normal law before truncation (as in eq. (37), p. 586), not the mean and variance of $X^\flat$: the mean of $X^\flat$ is eq. (8) of Corollary 1, which differs from $\mu$ unless $\mu = (a+b)/2$. The statement is therefore the equality of densities, with $\sigma$ the positive square root of (7). The decision domain is $[a,b]$, the smallest interval containing the support of the uniform density.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 572–573 (PDF 7–8), Proposition 1, eqs. (6)–(7); proof p. 586 (PDF 21), eqs. (36)–(41)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand
import Definitions.Def_BoundedNV_Uniform_TruncNormal

namespace BoundedNV.Uniform

/-- Proposition 1, pp. 572–573: for demand `D ∼ U[a, b]`, the density (4) of the behavioral solution,
the logit density of the expected profit over `S = [a, b]`, is the density of the normal law with
parameters `μ = b − (c/p)(b − a)` (6) and `σ² = β(b − a)/p` (7), truncated to `[a, b]`. -/
theorem prop1_truncated_normal (a b p c β : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hβ : 0 < β) :
    ∀ x, logitDensity (Set.Icc a b) (nvProfit (unifDensity a b) p c) β x =
      truncNormalDensity a b (unifMu a b p c) (unifSigma a b p β) x := by sorry

end BoundedNV.Uniform
