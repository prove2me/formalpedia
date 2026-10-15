-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_4_a
-- name    : CrowdfundRM.Triangular.proposition_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:20.657999+00:00
-- url     : https://prove2.me/theorems/ce772d21-a050-4e14-9905-9dc4bb92b187
-- title:
--   Proposition 4(a), pp. 14–15 — no herding, k = r, triangular valuations with mode 0: optimal duration (23) and optimal pledge level (24)
-- statement:
--   Consider a campaign satisfying the standing assumptions with no herding backers ($\Lambda_h=0$), with $k=r$, and with independent valuations right-triangular on $[0,\bar v]$ with mode $v^m_i=0$, i.e. $\bar F_i(y)=(1-y/\bar v)^2$ on $[0,\bar v)$.
--
--   1. For every pledge level $0<p\le\bar v$, the unique maximizer of $T\mapsto\pi(p,T)$ over $0\le T\le\frac1r\ln(\bar v/p)$ is
--   $$T^*(p)=\frac1r\ln\left(\frac{\sqrt{1-(1-p/\bar v)^3}}{2\,(p/\bar v)\cos\!\Bigl(\frac{\pi-\arcsin\left((1-p/\bar v)^{3/2}\right)}{3}\Bigr)}\right).\qquad(23)$$
--   2. For every duration $T>0$, the unique maximizer of $p\mapsto\pi(p,T)$ over $0<p\le\bar v$ with $T\le\frac1r\ln(\bar v/p)$ is
--   $$p^*(T)=\bar v\,\frac{e^{rT}-e^{rT/2}+1}{e^{2rT}+e^{rT}+1}.\qquad(24)$$
--
--   These limited-flexibility policies are the building blocks of the jointly optimal policy of Proposition 7(a).
--
--   **Formalization Note** "The optimal" is stated as: feasible, maximal, and the unique maximizer. $T=0$ is excluded for $p^*(T)$ because $\pi(\cdot,0)\equiv0$. In (23), $\pi$ is the constant $3.14159\ldots$, not the revenue.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 14–15, Proposition 4(a), (23)–(24)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_4_a (M : Campaign) (hM : M.Standing) (hLh : M.Lh = 0) (hkr : M.k = M.r)
    (hFi : M.Fbi = triBar0 M.vbar) :
    (∀ p : ℝ, 0 < p → p ≤ M.vbar →
      IsUniqueMaxOn (M.revenue p) {T | M.Feasible p T}
        (Real.log (Real.sqrt (1 - (1 - p / M.vbar) ^ 3) /
          (2 * (p / M.vbar) *
            Real.cos ((Real.pi - Real.arcsin ((1 - p / M.vbar) ^ ((3:ℝ) / 2))) / 3))) / M.r)) ∧
    (∀ T : ℝ, 0 < T →
      IsUniqueMaxOn (fun p => M.revenue p T) {p | M.Feasible p T}
        (M.vbar * ((Real.exp (M.r * T) - Real.exp (M.r * T / 2) + 1) /
          (Real.exp (2 * M.r * T) + Real.exp (M.r * T) + 1)))) := by sorry
end CrowdfundRM.Triangular
