-- Prove2me | Theorems.Thm_AVHighway_DPolicy_eq_16_closed_form
-- name    : AVHighway.DPolicy.eq_16_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:09.251786+00:00
-- url     : https://prove2.me/theorems/143d9ca9-6d07-43f7-b961-04a597c17ee3
-- title:
--   Display (16), Online Appendix p. 4 — closed form W = L Σ_{n<c} (Lλ)^n/(n!V_{n+1}⋯V_1) / (1 + Σ_{n=1}^{c−1} (Lλ)^n/(n!V_n⋯V_1))
-- statement:
--   Consider the $M/G_n/c/c$ loss queue with segment length $L > 0$, capacity $c \ge 1$, speeds $V_1, \dots, V_c > 0$ and arrival rate $\lambda > 0$, with stationary law (12) and mean travel time $W = \bigl(\sum_{n=1}^c n\pi_n\bigr)/\bigl(\lambda(1-\pi_c)\bigr)$ of (13). Then
--   $$W = \frac{L \sum_{n=0}^{c-1} \dfrac{(L\lambda)^n}{n!\,V_{n+1}V_n\cdots V_1}}{1 + \sum_{n=1}^{c-1} \dfrac{(L\lambda)^n}{n!\,V_n\cdots V_1}}.$$
--
--   This closed form, obtained in the proof of Lemma 1, is the expression from which both the monotonicity of $W$ in $\lambda$ and its heavy-traffic limit (20) are read off.
--
--   **Formalization Note** Only the final equality of (16) is stated; its middle expression is the definition (12)–(13) unfolded. $c - 1$ is natural-number subtraction, harmless as $c \ge 1$. $\lambda > 0$ is assumed because at $\lambda = 0$ the throughput is $0$ and Lean's $x/0 = 0$ makes the left side $0$, while the right side is $L/V_1$.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), proof of Lemma 1, display (16), Online Appendix p. 4

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

namespace AVHighway.DPolicy
theorem eq_16_closed_form (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) :
    meanTravelTime L V cap lam =
      L * (∑ n ∈ Finset.range cap,
          (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 (n + 1), V k)) /
        (1 + ∑ n ∈ Finset.Icc 1 (cap - 1),
          (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 n, V k)) := by sorry
end AVHighway.DPolicy
