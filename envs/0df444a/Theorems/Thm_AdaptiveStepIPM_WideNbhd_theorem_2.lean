-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_theorem_2
-- name    : AdaptiveStepIPM.WideNbhd.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:06.557987+00:00
-- url     : https://prove2.me/theorems/cbb31241-b1dd-4f8c-88b2-643349224ceb
-- title:
--   Theorem 2 — Algorithm 2 in $\mathcal N_\infty(\beta)$ or $\mathcal N^-_\infty(\beta)$ with $\gamma\le2(1-\beta)$ reaches precision $t$ in $\lceil nt\ln 2/(2\beta\gamma(1-\gamma))\rceil$ steps
-- statement:
--   Consider the linear program (P) $\min c^Tx$ s.t. $Ax=b$, $x\ge0$, and its dual (D), with $n\ge1$ variables. Let $\beta\in(0,1)$ and $\gamma\in(0,1)$ be constants with $\gamma\le 2(1-\beta)$, and let $\mathcal N$ be $\mathcal N_\infty(\beta)$ or $\mathcal N^-_\infty(\beta)$.
--
--   **Algorithm 2.** Given $(x^0,s^0)\in\mathcal N$ with $(x^0)^Ts^0\le 2^t$, set $k = 0$. While $(x^k)^Ts^k > 2^{-t}$: compute $d = d(x^k,s^k,\gamma)$ from (2), compute the largest $\bar\theta$ such that $(x(\theta),s(\theta))\in\mathcal N$ for all $\theta\in[0,\bar\theta]$, set $(x^{k+1},s^{k+1}) = (x(\bar\theta),s(\bar\theta))$ and $k = k+1$.
--
--   **Theorem.** Every run of Algorithm 2 reaches $(x^k)^Ts^k\le2^{-t}$ for some
--   $$
--   k \;\le\; K := \Big\lceil \frac{\ln 2\cdot n\,t}{2\beta\gamma(1-\gamma)}\Big\rceil ,
--   $$
--   so the algorithm terminates in $O(nt)$ iterations.
--
--   This is the classical $O(nt)$ bound of Kojima, Mizuno and Yoshise, obtained for an adaptive-step method in the wide neighbourhoods, which with $\beta$ close to $1$ cover almost all strictly feasible pairs.
--
--   **Formalization Note** The paper states "$O(nt)$ iterations"; $K$ is the explicit count that its inequality (15), $\mu^{k+1}\le(1-4\beta\gamma(1-\gamma)/n)\mu^k$, gives: $(x^k)^Ts^k\le e^{-4k\beta\gamma(1-\gamma)/n}\,2^t\le 2^{-t}$ once $k\ge K$. A run is any pair of sequences $(x^k,s^k)$ that starts as required and makes one Algorithm 2 iteration from every iterate with $(x^k)^Ts^k>2^{-t}$; what happens after the stopping test is met is unconstrained. "The largest $\bar\theta$" is encoded as a greatest element, so a run exists only while such a maximum exists (for $n=1$ it never does, and the theorem holds trivially). No sign condition on $t$ is imposed: for $t\le0$ the starting pair already satisfies $(x^0)^Ts^0\le2^t\le2^{-t}$ and $K=0$. The two neighbourhoods are handled by a hypothesis $\mathcal N = \mathcal N_\infty(\beta)$ or $\mathcal N = \mathcal N^-_\infty(\beta)$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 10, Theorem 2 (Algorithm 2, pp. 9–10)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Theorem 2 of Mizuno–Todd–Ye (p. 10): let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`. Algorithm 2 with
`N = N_∞(β)` or `N_∞⁻(β)`, started at `(x⁰, s⁰) ∈ N` with `(x⁰)ᵀs⁰ ≤ 2^t`, reaches
`(x^k)ᵀs^k ≤ 2^{−t}` within `K = ⌈ln 2 · n · t / (2βγ(1 − γ))⌉` iterations — the explicit count
behind the paper's `O(nt)`, from (15). A run is any sequence of pairs that starts as required
and makes an Algorithm 2 step from every iterate with `(x^k)ᵀs^k > 2^{−t}`. -/
theorem theorem_2 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (t : ℝ) (x s : ℕ → Fin n → ℝ)
    (h0 : (x 0, s 0) ∈ N) (h0t : x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t)
    (hrun : ∀ k, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k → Alg2Step A N γ (x k) (s k) (x (k + 1)) (s (k + 1))) :
    ∃ k ≤ ⌈Real.log 2 * n * t / (2 * β * γ * (1 - γ))⌉₊, x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.WideNbhd
