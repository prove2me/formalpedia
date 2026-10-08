-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_corollary2_cesaro_vanish
-- name    : FedergruenZipkin.AvgCost.corollary2_cesaro_vanish
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:38:07.027356+00:00
-- url     : https://prove2.me/theorems/b9a61012-9c8e-4e20-a671-52305eab6672
-- title:
--   Corollary 2 (p. 201) — $(t+1)^{-1}P[\delta_{0t}]\cdots P[\delta_{tt}](H_\iota v1 + H_\iota G) \to 0$
-- statement:
--   In the capacitated inventory model with storage capacity $U \ge \bar y^\infty$, where $\bar y^\infty$ is the smallest global minimizer of $G$, set $L = \bar y^\infty - b$. For a policy $\delta$ let $P[\delta]$ be the transition operator $P[\delta]w(x) = E\,w(\delta(x) - D)$. Let $\iota = [l, u]$ satisfy the assumptions of Lemma 3 ($0 \le u \le U$, $l \le u - b$), and let $\{(\delta_{0t}, \delta_{1t}, \dots, \delta_{tt})\}_{t \ge 0}$ be any sequence of $(t+1)$-period policies with every $\delta_{st} \in \Delta_L$ (feasible and ordering to capacity at or below $L$). Then for all $x \le U$
--   $$\lim_{t\to\infty} (t+1)^{-1}\, P[\delta_{0t}]P[\delta_{1t}]\cdots P[\delta_{tt}]\bigl(H_\iota v1 + H_\iota G\bigr)(x) = 0.$$
--
--   This is the condition that lets the paper pass from the optimality equation to strong optimality in Theorem 1(b): the expected relative value at time $t$ grows sublinearly under any sequence of policies in $\Delta_L$.
--
--   **Formalization Note** The corollary leaves $\iota$ implicit; it is stated here for every $\iota$ satisfying the assumptions of Lemma 3, as in Corollary 1 (the proof of Theorem 1(b) uses $\iota = [L, U]$). The sequence of policies is a function $\sigma(t, s) = \delta_{st}$, constrained only for $s \le t$. Values are in $[0, \infty]$.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, pp. 200-201, Corollary 2 (with the definition of P[δ] and L preceding it)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
open Filter Topology
theorem corollary2_cesaro_vanish (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b)
    (σ : ℕ → ℕ → ℤ → ℤ) (hσ : ∀ t s, s ≤ t → FeasibleL M U (yInf - M.b) (σ t s)) :
    ∀ x ≤ U, Tendsto (fun t : ℕ =>
        Pcomp M (σ t) t (H M U l u (fun _ => (1 : ℝ≥0∞)) + H M U l u (fun y => ENNReal.ofReal (M.G y))) x /
          ((t : ℝ≥0∞) + 1)) atTop (𝓝 0) := by sorry
end FedergruenZipkin.AvgCost
