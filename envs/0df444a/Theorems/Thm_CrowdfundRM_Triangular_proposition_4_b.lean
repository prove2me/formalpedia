-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_4_b
-- name    : CrowdfundRM.Triangular.proposition_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:15.882836+00:00
-- url     : https://prove2.me/theorems/128acd0e-7413-4f27-bc5f-238e6b94058d
-- title:
--   Proposition 4(b), p. 15 — no herding, k = r, triangular valuations with mode v̄: optimal duration (25) and optimal pledge level (26)
-- statement:
--   Consider a campaign satisfying the standing assumptions with no herding backers ($\Lambda_h=0$), with $k=r$, and with independent valuations right-triangular on $[0,\bar v]$ with mode $v^m_i=\bar v$, i.e. $\bar F_i(y)=1-(y/\bar v)^2$ on $[0,\bar v)$.
--
--   1. For every pledge level $0<p\le\bar v$, the unique maximizer of $T\mapsto\pi(p,T)$ over $0\le T\le\frac1r\ln(\bar v/p)$ is
--   $$T^*(p)=\frac1{3r}\ln\left(\frac12\Bigl(3\bigl(\tfrac{\bar v}{p}\bigr)^2-1\Bigr)\right).\qquad(25)$$
--   2. For every duration $T>0$, the unique maximizer of $p\mapsto\pi(p,T)$ over $0<p\le\bar v$ with $T\le\frac1r\ln(\bar v/p)$ is
--   $$p^*(T)=\bar v\,\frac{1}{\sqrt{1+e^{rT}+e^{2rT}}}.\qquad(26)$$
--
--   These limited-flexibility policies are the building blocks of the jointly optimal policy of Proposition 7(a).
--
--   **Formalization Note** "The optimal" is stated as: feasible, maximal, and the unique maximizer. $T=0$ is excluded for $p^*(T)$ because $\pi(\cdot,0)\equiv0$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 15, Proposition 4(b), (25)–(26)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_4_b (M : Campaign) (hM : M.Standing) (hLh : M.Lh = 0) (hkr : M.k = M.r)
    (hFi : M.Fbi = triBar1 M.vbar) :
    (∀ p : ℝ, 0 < p → p ≤ M.vbar →
      IsUniqueMaxOn (M.revenue p) {T | M.Feasible p T}
        (Real.log (1 / 2 * (3 * (M.vbar / p) ^ 2 - 1)) / (3 * M.r))) ∧
    (∀ T : ℝ, 0 < T →
      IsUniqueMaxOn (fun p => M.revenue p T) {p | M.Feasible p T}
        (M.vbar * (1 / Real.sqrt (1 + Real.exp (M.r * T) + Real.exp (2 * M.r * T))))) := by sorry
end CrowdfundRM.Triangular
