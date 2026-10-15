-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_5_b
-- name    : CrowdfundRM.Triangular.proposition_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:18.687726+00:00
-- url     : https://prove2.me/theorems/d21c3b85-8269-448f-a92d-e85dfdac817a
-- title:
--   Proposition 5(b), p. 16 — herding proxy R_h, triangular herding valuations with mode v̄: duration (30) and pledge level (31) maximize (27)
-- statement:
--   Consider a campaign satisfying the standing assumptions whose herding valuations are right-triangular on $[0,\bar v]$ with mode $v^m_h=\bar v$, i.e. $\bar F_h(y)=1-(y/\bar v)^2$ on $[0,\bar v)$, and the herding-dominated revenue proxy $R_h(p,T)=p\int_0^T\bar F_h(pe^{ry})\,dy$ of (27).
--
--   1. For every pledge level $0<p\le\bar v$, the unique maximizer of $T\mapsto R_h(p,T)$ over $0\le T\le\frac1r\ln(\bar v/p)$ is
--   $$T^*(p)=\frac1r\ln\Bigl(\frac{\bar v}{p}\Bigr).\qquad(30)$$
--   2. For every duration $T>0$, the unique maximizer of $p\mapsto R_h(p,T)$ over $0<p\le\bar v$ with $T\le\frac1r\ln(\bar v/p)$ is
--   $$p^*(T)=\bar v\min\left(\sqrt{\frac{2rT}{3(e^{2rT}-1)}},\;e^{-rT}\right).\qquad(31)$$
--
--   Together with Proposition 5(a) these are the limited-flexibility policies of herding-dominated campaigns; Proposition 7(b) optimizes both levers jointly.
--
--   **Formalization Note** The proxy (27) is maximized explicitly; no limit $\Lambda_h\to\infty$ is taken. "Maximizes" is stated as: feasible, maximal, and the unique maximizer. $T=0$ is excluded because $R_h(\cdot,0)\equiv0$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 15–16, (27) and Proposition 5(b), (30)–(31)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_5_b (M : Campaign) (hM : M.Standing) (hFh : M.Fbh = triBar1 M.vbar) :
    (∀ p : ℝ, 0 < p → p ≤ M.vbar →
      IsUniqueMaxOn (M.Rh p) {T | M.Feasible p T} (Real.log (M.vbar / p) / M.r)) ∧
    (∀ T : ℝ, 0 < T →
      IsUniqueMaxOn (fun p => M.Rh p T) {p | M.Feasible p T}
        (M.vbar * min (Real.sqrt (2 * M.r * T / (3 * (Real.exp (2 * M.r * T) - 1))))
          (Real.exp (-M.r * T)))) := by sorry
end CrowdfundRM.Triangular
