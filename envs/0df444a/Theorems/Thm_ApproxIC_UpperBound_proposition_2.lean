-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_proposition_2
-- name    : ApproxIC.UpperBound.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:21.683821+00:00
-- url     : https://prove2.me/theorems/347bfab1-5320-478c-ab19-0a0ecad52e7c
-- title:
--   Proposition 2, p. 22 — under eq. (9) the number of steps is K = O(log(1/ε)/ε^β)
-- statement:
--   Let $0<p^\star<\bar v$ and $\beta\in(0,1/2)$, and let $K(\varepsilon)$ be the number of steps of the path of eq. (9), that is, the first index $K$ with $\nu_K\le\mu$ for the thresholds $\nu_{-1}=\bar v$, $\nu_k=v^\star(\nu_{k-1})$. Then there are constants $C>0$ and $\varepsilon_0>0$ such that
--   $$K(\varepsilon)\le C\,\frac{\log(1/\varepsilon)}{\varepsilon^\beta}\qquad\text{for all }\varepsilon\in(0,\varepsilon_0].$$
--
--   Combined with Lemma 3, this gives $\Phi_1(\lambda^\star)=\tilde O(\varepsilon^{1-\beta})$.
--
--   **Formalization Note** $O(\cdot)$ follows the paper's definition (p. 13): $C$ and $\varepsilon_0$ may depend on $\bar v,p^\star,\beta$ but not on $\varepsilon$. Eq. (9) involves no distribution, so $p^\star$ is any interior point of $(0,\bar v)$ (the proof never uses optimality of $p^\star$). $K$ is defined by an infimum over $\mathbb N$, which is $0$ for an empty set; for small $\varepsilon$ the set is nonempty.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 22, Proposition 2 and eq. (9) (proof pp. 43–45)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Eq9

namespace ApproxIC.UpperBound

theorem proposition_2 (vbar pstar β : ℝ) (hp : 0 < pstar) (hpv : pstar < vbar)
    (hβ : β ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
      (stepsEq9 vbar pstar β ε : ℝ) ≤ C * Real.log (1 / ε) / ε ^ β := by sorry

end ApproxIC.UpperBound
