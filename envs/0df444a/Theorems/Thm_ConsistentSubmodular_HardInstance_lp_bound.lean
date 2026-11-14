-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_lp_bound
-- name    : ConsistentSubmodular.HardInstance.lp_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:54.931213+00:00
-- url     : https://prove2.me/theorems/b7a0eba6-48cf-40e2-abbb-8cebbbe420b8
-- title:
--   Linear-program bound with error terms at the root of $\Phi$
-- statement:
--   Let $\Phi(x)=x^4+x^3-2x^2-3x+2$ and, for $x>0$, put $y=x^2(1+x)$, $\mu_1=x(1+x)(1-x)$, $\mu_2=1-x(1+x)$, and
--   $$N=1+x-y,\qquad D=1+x+y-xy-x^3(1+x)^2,\qquad E=\mu_1x+2\mu_2y.$$
--   Let $x,\varepsilon,k,C\in\mathbb R$ satisfy $x>0$, $x(1+x)\le1$, $\Phi(x)=0$, $0<\varepsilon\le1/6$, $k>0$, $1\le\varepsilon k$, and $0\le C\le\varepsilon k$. Then
--   $$kN+E\,C\;\le\;\Bigl(\frac{1}{1+x^3(1+x)}+12\varepsilon\Bigr)\bigl(kD-E\bigr).$$
--
--   On the left are the recourse terms of the time bounds; on the right, the corrections $k-1$ and $k-2$ of the optima enter the denominator with a minus sign, as in Appendix A.2. At the root of $\Phi$ the ratio $1/(1+x^3(1+x))$ equals $\xi_\star$, so this inequality yields the bound $\xi_\star+O(\varepsilon)$ of Theorem 1.
--
--   **Formalization Note** The quantities $N$, $D$, $E$ are `lpNumerator`, `lpDenominator` and `lpError`; here $y^2/x$ is written as $x^3(1+x)^2$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardScalar.lean#L67-L133 (`ConsistentSubmodular.HardInstance.lp_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardScalar

open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem ConsistentSubmodular.HardInstance.lp_bound {x ε k C : ℝ} (hx0 : 0 < x) (hs : x * (1 + x) ≤ 1) (hphi : phi x = 0)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) (hk : 0 < k) (hεk : 1 ≤ ε * k) (hC0 : 0 ≤ C)
    (hC : C ≤ ε * k) :
    k * lpNumerator x + lpError x * C ≤
      (1 / (1 + x ^ 3 * (1 + x)) + 12 * ε) * (k * lpDenominator x - lpError x) := by sorry
