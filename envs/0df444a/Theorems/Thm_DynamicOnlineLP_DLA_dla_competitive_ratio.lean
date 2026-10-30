-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_dla_competitive_ratio
-- name    : DynamicOnlineLP.DLA.dla_competitive_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:53:43.365984+00:00
-- url     : https://prove2.me/theorems/b5ba88a1-060c-48da-80f9-4751db1269e3
-- title:
--   Theorem 1 — the dynamic learning algorithm is 1 − O(ε) competitive when B = min_i b_i ≥ Ω(m log(n/ε)/ε²)
-- statement:
--   Consider the online linear program: $n$ columns $(\pi_t,a_t)$ with $\pi_t\ge0$ and $a_t\in[0,1]^m$ ($m\ge1$), a right-hand side $b\in\mathbb R^m$, and the offline optimum
--
--   $$\mathrm{OPT}=\max\Big\{\sum_{t=1}^n\pi_tx_t:\ \sum_{t=1}^n a_{it}x_t\le b_i\ (i\le m),\ 0\le x_t\le1\Big\}.$$
--
--   The columns are chosen adversarially but arrive in a uniformly random order $\sigma$ (Assumption 1), $n$ is known in advance (Assumption 2), and the inputs are in general position (Assumption 3: for any price vector $p\in\mathbb R^m$ at most $m$ columns satisfy $p^{\top}a_t=\pi_t$). Let $\varepsilon=2^{-E}$ with $E\ge1$ and let $\varepsilon n$ be a positive integer. Let $x_t$ be the decisions of the **dynamic learning algorithm** (DLA): it accepts nothing up to time $\varepsilon n$; at each time $t$ in a period $(\ell,2\ell]$, $\ell\in\{\varepsilon n,2\varepsilon n,\dots\}$, it proposes $x_t(\hat p^{\ell})$, the threshold decision at an optimal dual price $\hat p^\ell$ of the partial LP (13) on the first $\ell$ arrivals with right-hand side $(1-h_\ell)\frac{\ell}{n}b$, $h_\ell=\varepsilon\sqrt{n/\ell}$, and executes it if no constraint is violated.
--
--   There are absolute constants $C_1,C_2>0$ such that, whenever
--
--   $$B=\min_i b_i\ \ge\ \frac{C_1\,m\log(n/\varepsilon)}{\varepsilon^2},$$
--
--   the DLA is $1-C_2\varepsilon$ competitive in the random permutation model:
--
--   $$\mathbb E_\sigma\Big[\sum_{t=1}^n\pi_tx_t\Big]\ \ge\ (1-C_2\,\varepsilon)\,\mathrm{OPT}.$$
--
--   This is the main result of Agrawal, Wang and Ye: a $1-O(\varepsilon)$ competitive ratio for online linear programming under random order, with a right-hand-side requirement whose dependence on $\varepsilon$ matches the lower bound for the one-dimensional secretary problem.
--
--   **Formalization Note** The paper writes $1-O(\varepsilon)$ and $B\ge\Omega(m\log(n/\varepsilon)/\varepsilon^2)$; its proof aims at $C_1=10$, $C_2=15$ but the constant $10$ does not survive the union-bound arithmetic of Appendix B.1, so the statement asserts absolute constants $C_1,C_2$, quantified before $m$, $n$, $\varepsilon$, the instance and the algorithm. The expectation is the average over all $n!$ arrival orders. Because optimal dual prices need not be unique, the DLA is parametrized by a dual-selection rule, and the theorem holds for every valid rule (one that returns an optimal dual price of the partial LP and looks only at the first $\ell$ arrivals). $\varepsilon=2^{-E}$ and the integrality of $\varepsilon n$ are the paper's standing assumptions of §3; $\log$ is the natural logarithm.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 878, Theorem 1 (proof: p. 885, §3.1)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm

namespace DynamicOnlineLP.DLA

/-- Theorem 1 (Agrawal–Wang–Ye 2014, p. 878), with absolute constants `C₁, C₂` in place of the
paper's `Ω(·)` and `O(·)`: under Assumptions 1–3, `ε = 2^{-E}` and `εn ∈ ℕ`, if
`B = min_i b_i ≥ C₁ m log(n/ε)/ε²`, then Algorithm DLA (with any valid dual-selection rule) is
`1 - C₂ ε` competitive in the random permutation model:
`E_σ[∑_t π_t x_t] ≥ (1 - C₂ ε) OPT`. -/
theorem dla_competitive_ratio :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (m n E : ℕ) (I : Instance m n) (rule : DualRule m n),
        1 ≤ m → 1 ≤ E → 0 < n → 2 ^ E ∣ n → I.GeneralPosition → IsValidDualRule rule →
        (∀ i : Fin m, C₁ * (m : ℝ) * Real.log ((n : ℝ) / eps E) / eps E ^ 2 ≤ I.b i) →
        (1 - C₂ * eps E) * I.OPT ≤ avgPerm (fun σ : Equiv.Perm (Fin n) => dlaValue I rule E σ) := by sorry

end DynamicOnlineLP.DLA
