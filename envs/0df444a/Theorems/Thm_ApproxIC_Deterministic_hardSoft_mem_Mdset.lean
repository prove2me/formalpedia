-- Prove2me | Theorems.Thm_ApproxIC_Deterministic_hardSoft_mem_Mdset
-- name    : ApproxIC.Deterministic.hardSoft_mem_Mdset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:27.511538+00:00
-- url     : https://prove2.me/theorems/d61555ad-6500-43cf-9a3b-cea0cb9a4122
-- title:
--   Appendix B, proof of Theorem 2, p. 53 — the hard/soft floor mechanism with p = r, s = r + ε is a deterministic ε-IC mechanism
-- statement:
--   Let the buyer's value have a density on $S=[0,\bar v]$ (standing assumptions of §2), let $\varepsilon\ge 0$ and $r\in S$. Then the hard/soft floor mechanism $m_d(r)$ with hard floor $r$ and soft floor $r+\varepsilon$,
--   $$x(v)=\mathbf 1\{v\ge r\},\qquad t(v)=v\,\mathbf 1\{v\in[r,r+\varepsilon)\}+(r+\varepsilon)\,\mathbf 1\{v\ge r+\varepsilon\},$$
--   is a feasible deterministic mechanism for $(\mathcal P_\varepsilon)$:
--   $$m_d(r)\in\mathcal M_d(\varepsilon).$$
--   That is, it is measurable, allocates either $0$ or $1$, is individually rational, and is $\varepsilon$-incentive compatible.
--
--   In the proof of Theorem 2 this is the step that makes the hard/soft floor family a valid replacement for an arbitrary deterministic $\varepsilon$-IC mechanism.
--
--   **Formalization Note** For $r+\varepsilon>\bar v$ the soft floor lies beyond the support; the mechanism restricted to $S$ is still well defined and the statement still holds.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 53, Appendix B, proof of Theorem 2, second paragraph ("Note that this mechanism is also feasible")

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

namespace ApproxIC.Deterministic

theorem hardSoft_mem_Mdset (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (r : ℝ) (hr : r ∈ Set.Icc 0 M.vbar) :
    hardSoft r (r + ε) ∈ Mdset M ε := by sorry

end ApproxIC.Deterministic
