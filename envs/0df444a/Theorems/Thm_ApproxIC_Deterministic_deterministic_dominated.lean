-- Prove2me | Theorems.Thm_ApproxIC_Deterministic_deterministic_dominated
-- name    : ApproxIC.Deterministic.deterministic_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:26.500325+00:00
-- url     : https://prove2.me/theorems/781e825a-0a80-464b-9e8e-e4cbe113ca89
-- title:
--   Appendix B, proof of Theorem 2, eq. (23), pp. 52–53 — every deterministic ε-IC mechanism is dominated by a hard/soft floor m_d(r)
-- statement:
--   Let the buyer's value have a density on $S=[0,\bar v]$ (standing assumptions of §2), let $\varepsilon\ge0$, and let $m=(x,t)\in\mathcal M_d(\varepsilon)$ be any deterministic $\varepsilon$-IC, individually rational mechanism. Then there is $r\in S$ such that the payments of $m$ are bounded pointwise by those of the hard/soft floor mechanism $m_d(r)$ with hard floor $r$ and soft floor $r+\varepsilon$,
--   $$t(v)\le\begin{cases}0 & v\in[0,r),\\ v & v\in[r,r+\varepsilon),\\ r+\varepsilon & v\in[r+\varepsilon,\bar v],\end{cases}$$
--   and consequently
--   $$\Pi(m)\le\Pi(m_d(r)).$$
--
--   In the paper, $r=\inf\{v\in[0,\bar v]:x(v)=1\}$ and the pointwise bound is eq. (23); together with the feasibility of $m_d(r)$ it shows that among deterministic mechanisms the hard/soft floor mechanisms are optimal.
--
--   **Formalization Note** The paper assumes an optimal deterministic mechanism exists and takes $x$ right-continuous "without loss of generality". The statement here needs neither: it is about every mechanism of $\mathcal M_d(\varepsilon)$, with no monotonicity or continuity assumption on $x$. The bound $t(v)\le v$ on $[r,r+\varepsilon)$ is eq. (23)'s $t(v)\le v\cdot x(v)$ combined with $x\le1$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), pp. 52–53, Appendix B, proof of Theorem 2, eq. (23) and the conclusion "among the deterministic mechanisms, the hard/soft floor mechanisms are optimal"

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

namespace ApproxIC.Deterministic

theorem deterministic_dominated (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (m : Mech) (hm : m ∈ Mdset M ε) :
    ∃ r ∈ Set.Icc 0 M.vbar,
      (∀ v ∈ Set.Icc 0 M.vbar, m.t v ≤ (hardSoft r (r + ε)).t v) ∧
      revenue M m ≤ revenue M (hardSoft r (r + ε)) := by sorry

end ApproxIC.Deterministic
