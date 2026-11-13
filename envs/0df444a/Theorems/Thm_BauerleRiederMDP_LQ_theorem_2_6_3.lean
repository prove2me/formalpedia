-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_theorem_2_6_3
-- name    : BauerleRiederMDP.LQ.theorem_2_6_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:25:09.149997+00:00
-- url     : https://prove2.me/theorems/52e31deb-d734-4044-82e6-0220a312df5f
-- title:
--   Theorem 2.6.3 — the stochastic LQ problem has minimal cost $x^\top\tilde Q_nx$ and the linear optimal policy $f^*_n$ given by the Riccati recursion
-- statement:
--   Consider the stochastic linear-quadratic problem with state $x\in\mathbb R^m$, action $a\in\mathbb R^d$, system equation $X_{n+1}=A_{n+1}X_n+B_{n+1}a_n$ with independent random coefficient pairs $(A_{n+1},B_{n+1})$ whose entries have finite second moments, cost $\sum_{k=0}^{N}X_k^\top Q_kX_k$ with deterministic symmetric positive definite $Q_0,\dots,Q_N$, and $\mathbb E[B_{n+1}^\top QB_{n+1}]$ positive definite for every symmetric positive definite $Q$. Let $V_n(x)$ be the minimal expected cost in the period $[n,N]$ from state $x$, over all Markov policies of measurable decision rules.
--
--   1. Let the matrices $\tilde Q_n$ be recursively defined by $\tilde Q_N:=Q_N$ and
--   $$
--   \tilde Q_n:=Q_n+\mathbb E[A_{n+1}^\top\tilde Q_{n+1}A_{n+1}]-\mathbb E[A_{n+1}^\top\tilde Q_{n+1}B_{n+1}]\big(\mathbb E[B_{n+1}^\top\tilde Q_{n+1}B_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top\tilde Q_{n+1}A_{n+1}].
--   $$
--   Then for $n=0,\dots,N$ the matrix $\tilde Q_n$ is symmetric and positive semidefinite and $V_n(x)=x^\top\tilde Q_nx$ for all $x\in\mathbb R^m$.
--   2. The optimal policy $(f^*_0,\dots,f^*_{N-1})$ is given by
--   $$
--   f^*_n(x):=-\big(\mathbb E[B_{n+1}^\top\tilde Q_{n+1}B_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top\tilde Q_{n+1}A_{n+1}]\,x .
--   $$
--
--   The optimal decision rule is linear in the state, its coefficient matrix can be computed off-line, and the minimal cost is quadratic.
--
--   **Formalization Note** The problem is an instance of the published Markov Decision Model of Definition 2.1.1 with reward $-x^\top Q_nx$; $V_n$ and the cost $V_{n\pi}$ of a policy are minus its reward value functions (Remark 2.3.15) and take values in extended reals. Part 2 is stated for every policy whose decision rules at the times $n<N$ are the $f^*_n$.
--
--   Differences from the source:
--   - generalization: optimal policy means $V_{0\pi^*}=V_0$ (p.18) → $V_{n\pi^*}(x)=V_n(x)$ for every $n\le N$ and every $x$; reason: the case $n=0$ is the book's statement.
--   - encoding: $V_n$ the minimal cost → minus the published reward value function `MDPFinance.Bellman.V` of the model with $r_n=-x^\top Q_nx$, $g_N=-x^\top Q_Nx$; reason: Remark 2.3.15 and §2.6.3 ("we suppose that $V_n$ is the minimal cost"); extended-real values.
--   - encoding: $Z_1,Z_2,\dots$ independent, law not influenced by state or action → transition kernel at time $n$ is the law of $A_{n+1}x+B_{n+1}a$ under the law $\nu_{n+1}$ of $Z_{n+1}$; reason: the book's own data list ($Q^Z(\cdot\mid x,a)$ := distribution of $Z_{n+1}$) and Theorem 2.1.3.
--   - encoding: "finite expectation and covariance" → every entry of $A_k$, $B_k$ square integrable, $k=1,\dots,N$; reason: same condition, on the indices the problem uses.
--   - encoding: $(\cdot)^{-1}$ → Mathlib's matrix inverse ($0$ on singular matrices); reason: every inverted matrix is positive definite under the hypotheses.
--   - reading: "The optimal policy is given by" → every policy with these rules at $n<N$ is optimal, no uniqueness; reason: under the definition of p.18 the optimal policy is not unique: for $m=d=1$, $N=2$, $A_k=B_k=1$, $Q_k=1$ one gets $\tilde Q_1=1$, $f^*_0(x)=f^*_1(x)=-x$, so $X_1=0$ and $f_1$ can be changed off $0$ without changing $V_{0\pi}$.
--   - encoding: $\pi=(f_0,\dots,f_{N-1})$ → `MDPFinance.Bellman.Policy`, an $\mathbb N$-indexed sequence of measurable rules; reason: the entries at $n\ge N$ are never used.
--   - encoding: $\mathbb E[\cdot]$ of a random matrix → entrywise Bochner integral under the law of $(A_{n+1},B_{n+1})$; reason: every entry is integrable under the square-integrability assumption, so it is the expectation.
--   - encoding: $\mathbb R^m$, $\mathbb R^d$ → `Fin m → ℝ`, `Fin d → ℝ`; reason: the same spaces.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.6.3, p.52 (PDF 67); model §2.6.3, pp.50–51 (PDF 65–66)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_BauerleRiederMDP_LQ_Model
import Definitions.Def_BauerleRiederMDP_LQ_Riccati

open MeasureTheory ProbabilityTheory Matrix

namespace BauerleRiederMDP.LQ

/-- **Theorem 2.6.3** (Bäuerle & Rieder 2011, p.52, PDF 67), the stochastic linear-quadratic
problem of §2.6.3 (pp.50–52, PDF 65–67): state `x ∈ ℝ^m`, action `a ∈ ℝ^d`, transition
`X_{n+1} = A_{n+1} X_n + B_{n+1} a_n` with independent random coefficient pairs `(A_{n+1}, B_{n+1})`
of finite expectation and covariance, cost `Σ_{k=0}^{N} X_k^⊤ Q_k X_k` with deterministic symmetric
positive definite `Q_k`, and `𝔼[B_{n+1}^⊤ Q B_{n+1}]` positive definite for every symmetric positive
definite `Q`.

a) Let `Q̃_N := Q_N` and `Q̃_n := Q_n + 𝔼[A_{n+1}^⊤ Q̃_{n+1} A_{n+1}] − 𝔼[A_{n+1}^⊤ Q̃_{n+1} B_{n+1}]
(𝔼[B_{n+1}^⊤ Q̃_{n+1} B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q̃_{n+1} A_{n+1}]`. Then `Q̃_n` are symmetric, positive
semidefinite and `V_n(x) = x^⊤ Q̃_n x` for `x ∈ E` (`n = 0, …, N`), `V_n` being the minimal expected
cost in the period `[n, N]`.

b) The optimal policy `(f*_0, …, f*_{N−1})` is given by
`f*_n(x) := −(𝔼[B_{n+1}^⊤ Q̃_{n+1} B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q̃_{n+1} A_{n+1}] x`: every Markov policy
whose decision rules at the times `n < N` are the `f*_n` attains the minimal cost `V_n` from every
time `n ≤ N` and every state.

**Formalization Note.** The model is `LQData.toMDP`, an instance of the published Markov Decision
Model `MDPFinance.Bellman.MarkovDecisionModel` with reward `−x^⊤ Q_n x`; `V_n` (`LQData.Vcost`) and
`V_{nπ}` (`LQData.VcostPi`) are minus its reward value functions (Remark 2.3.15), so they are
infima/expectations of the cost over all Markov policies of measurable decision rules
`ℝ^m → ℝ^d`. Values are in `EReal`. `Q̃` is `LQData.Qt`. -/
theorem theorem_2_6_3 {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) :
    (∀ n ≤ N, (M.Qt n).IsSymm ∧ (M.Qt n).PosSemidef ∧
      ∀ x : Fin m → ℝ, M.Vcost n x = ((quadForm (M.Qt n) x : ℝ) : EReal)) ∧
    (∀ π : MDPFinance.Bellman.Policy M.toMDP, (∀ n < N, π.1 n = M.fstar n) →
      ∀ n ≤ N, ∀ x : Fin m → ℝ, M.VcostPi π n x = M.Vcost n x) := by sorry

end BauerleRiederMDP.LQ
