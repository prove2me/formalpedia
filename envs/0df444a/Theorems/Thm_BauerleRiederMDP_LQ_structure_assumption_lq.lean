-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_structure_assumption_lq
-- name    : BauerleRiederMDP.LQ.structure_assumption_lq
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:24:58.351197+00:00
-- url     : https://prove2.me/theorems/bc0b5976-e537-47fe-b01e-e2f8d3d3050a
-- title:
--   §2.6.3 — the Structure Assumption (SA$_N$) for the LQ problem: $T_n$ maps $x^\top Qx$ to $x^\top\tilde Qx$ with $\tilde Q$ symmetric positive definite, and the minimizer is linear
-- statement:
--   In the stochastic linear-quadratic problem under its standing assumptions, let $0\le n<N$ and $v(x)=x^\top Qx$ with $Q$ symmetric positive definite. Put
--   $$
--   \tilde Q=Q_n+\mathbb E[A_{n+1}^\top QA_{n+1}]-\mathbb E[A_{n+1}^\top QB_{n+1}]\big(\mathbb E[B_{n+1}^\top QB_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top QA_{n+1}].
--   $$
--   Then the Structure Assumption $(\mathrm{SA}_N)$ holds for $\mathbb{IM}_n=\{x\mapsto x^\top Qx: Q\text{ symmetric positive definite}\}$ and the linear rules $\Delta$:
--
--   1. $x^\top Q_Nx\in\mathbb{IM}_N$, i.e. $Q_N$ is symmetric and positive definite;
--   2. $\tilde Q$ is symmetric and positive definite, and for every $x\in\mathbb R^m$
--   $$
--   T_nv(x)=\inf_{a\in\mathbb R^d}\big\{x^\top Q_nx+\mathbb E\,v(A_{n+1}x+B_{n+1}a)\big\}=x^\top\tilde Qx ,
--   $$
--   so $T_nv\in\mathbb{IM}_n$;
--   3. the linear rule $x\mapsto Cx$ with $C=-(\mathbb E[B_{n+1}^\top QB_{n+1}])^{-1}\mathbb E[B_{n+1}^\top QA_{n+1}]$ attains this infimum at every $x$, so $v$ has a minimizer in $\Delta_n=\Delta\cap F_n$.
--
--   **Formalization Note** $T_nv(x)$ is a real infimum over $\mathbb R^d$; the expectation is under the law of $(A_{n+1},B_{n+1})$.
--
--   Differences from the source:
--   - encoding: "$Tv\in\mathbb{IM}_n$" → $\tilde Q$ symmetric and positive definite together with $T_nv(x)=x^\top\tilde Qx$ for all $x$; reason: membership in $\mathbb{IM}_n$ is exactly this.
--   - encoding: (SA$_N$)(iii) "there exists a maximizer $f_n\in\Delta_n$" → the rule with the explicit matrix `gainOf n Q` attains the infimum at every $x$; reason: it is the minimum point the page inserts; a linear rule is measurable and every action is admissible, so it lies in $\Delta\cap F_n$.
--   - encoding: (SA$_N$) is printed with maximizers of rewards → minimizers of costs; reason: §2.6.3 treats the cost problem, Remark 2.3.15.
--   - encoding: "finite expectation and covariance" → every entry of $A_k$, $B_k$ square integrable, $k=1,\dots,N$; reason: same condition, on the indices the problem uses.
--   - encoding: $(\cdot)^{-1}$ → Mathlib's matrix inverse ($0$ on singular matrices); reason: the inverted matrix is positive definite under the hypotheses.
--   - encoding: $\mathbb E[\cdot]$ of a random matrix → entrywise Bochner integral under the law of $(A_{n+1},B_{n+1})$; reason: every entry is integrable under the square-integrability assumption, so it is the expectation.
--   - encoding: $\mathbb R^m$, $\mathbb R^d$ → `Fin m → ℝ`, `Fin d → ℝ`; reason: the same spaces.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.6.3, pp.51–52 (PDF 66–67), unnumbered claim before Theorem 2.6.3

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Model
import Definitions.Def_BauerleRiederMDP_LQ_Riccati

open MeasureTheory ProbabilityTheory Matrix

namespace BauerleRiederMDP.LQ

/-- **§2.6.3, the Structure Assumption (SA_N) for the LQ problem** (Bäuerle & Rieder 2011, §2.6.3,
pp.51–52, PDF 66–67, unnumbered claim): with `𝕀M_n := {v : ℝ^m → ℝ_+ | v(x) = x^⊤ Q x with Q
symmetric, positive definite}`, let `v(x) = x^⊤ Q x ∈ 𝕀M_{n+1}` and `0 ≤ n < N`. "Inserting the
minimum point into the equation for `T_n v` yields
`T_n v(x) = x^⊤ (Q_n + 𝔼[A_{n+1}^⊤ Q A_{n+1}] − 𝔼[A_{n+1}^⊤ Q B_{n+1}] (𝔼[B_{n+1}^⊤ Q B_{n+1}])^{−1}
𝔼[B_{n+1}^⊤ Q A_{n+1}]) x = x^⊤ Q̃ x` where `Q̃` is defined as the expression in the brackets. Note
that `Q̃` is symmetric and since `x^⊤ Q̃ x = T_n v(x) ≥ x^⊤ Q_n x`, it is also positive definite. Thus
`T v ∈ 𝕀M_n`."

The conclusion states the three clauses of (SA_N) (p.23, PDF 38) for `𝕀M_n` and
`Δ := {f | f(x) = C x for some C ∈ ℝ^{(d,m)}}`:

(i) `g_N ∈ 𝕀M_N` ("Obviously `x^⊤ Q_N x ∈ 𝕀M_N`", p.51): `Q_N` is symmetric and positive definite;

(ii) `T_n v ∈ 𝕀M_n`: `Q̃ = LQData.riccatiStep n Q` is symmetric and positive definite and the minimal
cost operator `T_n v(x) = inf_{a ∈ ℝ^d} {x^⊤ Q_n x + 𝔼 v(A_{n+1} x + B_{n+1} a)}` (`LQData.costOp`)
equals `x^⊤ Q̃ x` for every `x ∈ ℝ^m`;

(iii) `v` has a minimizer in `Δ_n = Δ ∩ F_n`: the linear rule `x ↦ C x` with
`C = LQData.gainOf n Q` attains the infimum defining `T_n v(x)` at every `x`. (A linear rule is
measurable and every action is admissible, so it lies in `F_n`.)

**Formalization Note.** `E = Fin m → ℝ`, `A = Fin d → ℝ`; expectations under the law `ν (n+1)` of
`(A_{n+1}, B_{n+1})`; `T_n v(x)` is a real infimum over `ℝ^d`. (SA_N) is printed for a reward model;
§2.6.3 reads it for the cost problem (Remark 2.3.15), so "maximizer" is minimizer here. -/
theorem structure_assumption_lq {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) {n : ℕ}
    (hn : n < N) (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) :
    ((M.Q N).IsSymm ∧ (M.Q N).PosDef) ∧
      ((M.riccatiStep n Q).IsSymm ∧ (M.riccatiStep n Q).PosDef ∧
        ∀ x : Fin m → ℝ, M.costOp n Q x = quadForm (M.riccatiStep n Q) x) ∧
      ∀ x : Fin m → ℝ, M.costArg n Q x (M.gainOf n Q *ᵥ x) = M.costOp n Q x := by sorry

end BauerleRiederMDP.LQ
