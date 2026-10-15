-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_5_a
-- name    : CrowdfundRM.Triangular.proposition_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:27.153642+00:00
-- url     : https://prove2.me/theorems/5f90c701-6a80-4653-a284-770722f7fe06
-- title:
--   Proposition 5(a), p. 16 — herding proxy R_h, triangular herding valuations with mode 0: duration (28) and pledge level (29) maximize (27)
-- statement:
--   Consider a campaign satisfying the standing assumptions whose herding valuations are right-triangular on $[0,\bar v]$ with mode $v^m_h=0$, i.e. $\bar F_h(y)=(1-y/\bar v)^2$ on $[0,\bar v)$, and the herding-dominated revenue proxy $R_h(p,T)=p\int_0^T\bar F_h(pe^{ry})\,dy$ of (27).
--
--   1. For every pledge level $0<p\le\bar v$, the unique maximizer of $T\mapsto R_h(p,T)$ over $0\le T\le\frac1r\ln(\bar v/p)$ is
--   $$T^*(p)=\frac1r\ln\Bigl(\frac{\bar v}{p}\Bigr).\qquad(28)$$
--   2. For every duration $T>0$, the unique maximizer of $p\mapsto R_h(p,T)$ over $0<p\le\bar v$ with $T\le\frac1r\ln(\bar v/p)$ is
--   $$p^*(T)=\bar v\min\left(\frac43\,\frac1{e^{rT}+1}\left(1-\sqrt{1-\frac{3rT(e^{rT}+1)}{8(e^{rT}-1)}}\right),\;e^{-rT}\right).\qquad(29)$$
--
--   Together with Proposition 5(b) these are the limited-flexibility policies of herding-dominated campaigns; Proposition 7(b) optimizes both levers jointly.
--
--   **Formalization Note** The proxy (27) is maximized explicitly; no limit $\Lambda_h\to\infty$ is taken, and $k$, $\Lambda_h$ play no role. The square root is Lean's `Real.sqrt`, which is $0$ on negative arguments; the argument in (29) turns negative only for $rT>2.068$, where the minimum is already $e^{-rT}$ (it switches near $rT\approx1.973$), so the display is the paper's for every $T>0$. "Maximizes" is stated as: feasible, maximal, and the unique maximizer. $T=0$ is excluded because $R_h(\cdot,0)\equiv0$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 15–16, (27) and Proposition 5(a), (28)–(29)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_5_a (M : Campaign) (hM : M.Standing) (hFh : M.Fbh = triBar0 M.vbar) :
    (∀ p : ℝ, 0 < p → p ≤ M.vbar →
      IsUniqueMaxOn (M.Rh p) {T | M.Feasible p T} (Real.log (M.vbar / p) / M.r)) ∧
    (∀ T : ℝ, 0 < T →
      IsUniqueMaxOn (fun p => M.Rh p T) {p | M.Feasible p T}
        (M.vbar * min (4 / 3 * (1 / (Real.exp (M.r * T) + 1)) *
            (1 - Real.sqrt (1 - 3 * M.r * T * (Real.exp (M.r * T) + 1) /
              (8 * (Real.exp (M.r * T) - 1)))))
          (Real.exp (-M.r * T)))) := by sorry
end CrowdfundRM.Triangular
