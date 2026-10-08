-- Prove2me | Theorems.Thm_BoundedNV_Uniform_prop3_midpoint_bias
-- name    : BoundedNV.Uniform.prop3_midpoint_bias
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:42.085635+00:00
-- url     : https://prove2.me/theorems/06cfb5f3-dd0c-4e31-b082-ff5e0205edf8
-- title:
--   Proposition 3, p. 577 — under uniform demand E X♭ < x* when x* > (a + b)/2 and E X♭ > x* when x* < (a + b)/2
-- statement:
--   Let the demand $D$ be uniformly distributed on $[a, b]$ with $b > a \ge 0$ (a demand density constant over $[a, b]$), let $0 < c < p$ and $\beta > 0$. Let $x^*$ be a maximizer over $\mathbb R$ of the expected profit $\pi(x) = p\,\mathbb E\min(D,x) - cx$, and let $X^\flat$ be the behavioral solution, with density $\psi(x) \propto e^{\pi(x)/\beta}$ on $[a, b]$. Write $m = (a+b)/2$ for the midpoint. Then
--   $$x^* > m \implies \mathbb E X^\flat < x^*, \qquad\qquad x^* < m \implies \mathbb E X^\flat > x^*.$$
--
--   This is the **midpoint bias**: the boundedly rational newsvendor's mean order is pulled from the optimal order toward the middle of the demand range. It gives an explanation of the pull-to-center effect observed by Schweitzer and Cachon (2000).
--
--   **Formalization Note** The paper's hypothesis "the demand density $f$ is constant over $[a,b]$" is read, as in its proof (p. 586), as uniform demand on $[a, b]$: a density that is constant on its support $[a,b]$ equals $1/(b-a)$ there. The conclusion is written as inequalities on $\mathbb E X^\flat$ rather than with the words "underordering"/"overordering", because §6 (p. 577) defines those words with the inequalities swapped ("overorders (i.e., when $EX^\flat < x^*$)"), whereas the proof (p. 586) uses "$EX^\flat < \mu = x^*$, so there is underordering"; the statement follows the proof. $x^*$ is any maximizer of $\pi$ over $\mathbb R$; it exists and is unique (it equals $b - (c/p)(b-a)$).
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 577 (PDF 12), Proposition 3; proof p. 586 (PDF 21), eq. (42)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

namespace BoundedNV.Uniform

/-- Proposition 3, p. 577: for demand `D ∼ U[a, b]` (a demand density constant over `[a, b]`), let
`x*` maximize the expected profit (3). If `x*` lies above the midpoint `m = (a + b)/2`, the expected
behavioral solution `E X♭` is strictly below `x*`; if `x*` lies below `m`, `E X♭` is strictly
above `x*`. -/
theorem prop3_midpoint_bias (a b p c β xstar : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c)
    (hcp : c < p) (hβ : 0 < β)
    (hxstar : IsMaxOn (nvProfit (unifDensity a b) p c) Set.univ xstar) :
    ((a + b) / 2 < xstar →
        logitExp (Set.Icc a b) (nvProfit (unifDensity a b) p c) β id < xstar) ∧
      (xstar < (a + b) / 2 →
        xstar < logitExp (Set.Icc a b) (nvProfit (unifDensity a b) p c) β id) := by sorry

end BoundedNV.Uniform
