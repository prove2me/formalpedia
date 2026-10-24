-- Prove2me | Theorems.Thm_ApproxIC_Deterministic_revenue_hardSoft
-- name    : ApproxIC.Deterministic.revenue_hardSoft
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:49.605978+00:00
-- url     : https://prove2.me/theorems/f2a8aaf3-ae2e-48a8-ac05-9e74b24043c6
-- title:
--   Appendix B, proof of Theorem 2, p. 53 — Π(m_d(r)) = ∫_r^{r+ε} v f(v)dv + (r+ε)F̄(r+ε) = r·F̄(r) + ∫_r^{r+ε} F̄(v)dv
-- statement:
--   Let the buyer's value have a density $f$ on $S=[0,\bar v]$ (standing assumptions of §2), with $\bar F=1-F$. Let $\varepsilon\ge0$, $r\in S$, and let $m_d(r)$ be the hard/soft floor mechanism with hard floor $r$ and soft floor $r+\varepsilon$. Its expected revenue is
--   $$\Pi(m_d(r))=\int_r^{r+\varepsilon} v f(v)\,dv+(r+\varepsilon)\,\bar F(r+\varepsilon)=r\,\bar F(r)+\int_r^{r+\varepsilon}\bar F(v)\,dv .$$
--
--   The second form shows that the hard/soft floor earns the posted-price revenue $R(r)=r\bar F(r)$ plus a term of size at most $\varepsilon$; the proof of Theorem 2 derives both the $\mathcal O(\varepsilon)$ upper bound and the $\Omega(\varepsilon)$ lower bound from it.
--
--   **Formalization Note** Both printed equalities are stated. When $r+\varepsilon>\bar v$ they still hold, since $f=0$ and $\bar F=0$ beyond $\bar v$. The paper calls the second step an inequality obtained by integration by parts; it is an equality.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 53, Appendix B, proof of Theorem 2, first display (also displayed on p. 26)

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

namespace ApproxIC.Deterministic

theorem revenue_hardSoft (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (r : ℝ) (hr : r ∈ Set.Icc 0 M.vbar) :
    revenue M (hardSoft r (r + ε)) =
        (∫ v in r..(r + ε), v * M.f v) + (r + ε) * cdfBar M (r + ε) ∧
      revenue M (hardSoft r (r + ε)) = r * cdfBar M r + ∫ v in r..(r + ε), cdfBar M v := by sorry

end ApproxIC.Deterministic
