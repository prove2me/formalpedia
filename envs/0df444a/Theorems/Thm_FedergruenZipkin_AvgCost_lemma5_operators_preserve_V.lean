-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma5_operators_preserve_V
-- name    : FedergruenZipkin.AvgCost.lemma5_operators_preserve_V
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:38:31.860821+00:00
-- url     : https://prove2.me/theorems/7c287321-d018-4a26-b225-a21bb83bc38e
-- title:
--   Lemma 5 (p. 202) — $S$ and $Q$ map $V$ into itself, and $S_L = S$, $Q_L = Q$ on $V$ when $L \le \bar y^\infty - b$
-- statement:
--   In the capacitated inventory model with storage capacity $U \ge \bar y^\infty$, where $\bar y^\infty$ is the smallest global minimizer of $G$, define
--   $$V = \{v : v \in V_{\rho+3},\ v(x) \text{ is nonincreasing for } x < \bar y^\infty,\ v \text{ is convex}\},$$
--   where $v \in V_{\rho+3}$ means $|v(x)| \le A + B|x|^{\rho+3}$ on $x \le U$. Let $Rv(y) = G(y) + E\,v(y - D)$, $Sv(x) = \min_{y\in Y(x)} Rv(y)$, $Qv(x) = Sv(x) - Sv(\bar y^\infty)$, and $S_L$, $Q_L$ the analogues for the restricted action sets $Y_L$.
--
--   **Lemma 5.** For every $v \in V$: the expectation $E\,v(y - D)$ converges for every $y \le U$; $Sv \in V$ and $Qv \in V$; and for every $L \le \bar y^\infty - b$,
--   $$S_L v(x) = Sv(x),\qquad Q_L v(x) = Qv(x)\qquad (x \le U),$$
--   so $S_L$ and $Q_L$ also map $V$ into itself.
--
--   The invariance of $V$ under the value-iteration operators is what makes the fixed-point argument for the optimality equation (6) in Theorem 1(a) work, and it gives the convexity of the relative value function.
--
--   **Formalization Note** "Nonincreasing, $x < \bar y^\infty$" is read as $v(x+1) \le v(x)$ for every $x < \bar y^\infty$ (the step into $\bar y^\infty$ included), as the proof requires ("$Rv$ is nonincreasing below $\bar y^\infty$ … $Rv$ has a global minimum $\bar y \ge \bar y^\infty$"). Convexity and growth are required on $x \le U$ only. The convergence of $E\,v(y-D)$ is an added conclusion; the paper asserts it right after defining $R$ ("the expectations are well defined and finite by Assumption 2"), and it ensures that $Rv$ is not computed from a divergent series.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 202, Lemma 5 (with the definition of V preceding it)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
theorem lemma5_operators_preserve_V (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (v : ℤ → ℝ) (hv : InV M U yInf v) :
    (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
    InV M U yInf (S M U v) ∧ InV M U yInf (Q M U yInf v) ∧
    ∀ L : ℤ, L ≤ yInf - M.b →
      (∀ x ≤ U, SL M U L v x = S M U v x) ∧ (∀ x ≤ U, QL M U L yInf v x = Q M U yInf v x) := by sorry
end FedergruenZipkin.AvgCost
