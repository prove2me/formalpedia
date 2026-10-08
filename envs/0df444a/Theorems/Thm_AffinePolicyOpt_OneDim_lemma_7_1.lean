-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_7_1
-- name    : AffinePolicyOpt.OneDim.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:25.071595+00:00
-- url     : https://prove2.me/theorems/e488bacb-458a-4136-aaeb-20e48c94d396
-- title:
--   Lemma 7.1, p. 28 (with (8)–(9), P2) — J*_k and g_k are convex and the clamp max(L_k, min(U_k, y* − x)) is an optimal control
-- statement:
--   Consider the min-max control model (DP) under its standing hypotheses ($c_k\ge0$, $h_k$ convex and coercive, nonempty control and disturbance intervals), with Bellman functions $g_k$ and $J^*_k$. Fix a stage $k$ and write $\varphi_k(y)=c_ky+g_k(y)$. Then:
--
--   1. $J^*_k$ is convex on $\mathbb R$, and $g_k$ is convex on $\mathbb R$.
--   2. For every minimizer $y^*$ of $\varphi_k$ on $\mathbb R$ and every state $x$, the control
--   $$u^*_k(x)=\max\big(L_k,\ \min(U_k,\ y^*-x)\big)$$
--   minimizes $u\mapsto c_ku+g_k(x+u)$ over $[L_k,U_k]$, and $J^*_k(x)=c_ku^*_k(x)+g_k(x+u^*_k(x))$.
--   3. If $\varphi_k$ has no minimizer on $\mathbb R$, then $u=L_k$ is optimal at every state $x$, and $J^*_k(x)=c_kL_k+g_k(x+L_k)$.
--
--   The clamp is piecewise affine with at most three pieces ($U_k$, $y^*-x$, $L_k$), continuous and non-increasing in $x$; this is the paper's description of the optimal control law, and the convexity of $J^*_k$ and $g_k$ is property P2. These facts are what make the reduction of the induction step to a planar problem possible.
--
--   **Formalization Note** Stages are 0-based: `k : Fin T` is the paper's stage $K=k+1$ and `Jstar M j` is the paper's $J^*_{j+1}$, so `Jstar M k` is $J^*_K$ and `Jstar M (k+1)` is $J^*_{K+1}$. The page writes the optimal law (8) with thresholds $\underline y_k-U_k$ and $\overline y_k-L_k$; that form is infeasible when the minimizer set $[\underline y_k,\overline y_k]$ is a nondegenerate interval, and the clamp (thresholds $y^*-U_k$, $y^*-L_k$, as in Figure 1) is stated instead. The page asserts that the minimizer set of $\varphi_k$ is compact and (implicitly) nonempty; this can fail (e.g. $T=1$, $h(x)=|x|/2$, $c=1$, $\mathcal W=\{0\}$, where $\varphi(y)=y+|y|/2$ is unbounded below), so the clamp clause is stated for every minimizer, and clause 3 covers the case with none (where the clamp with $y^*=-\infty$ gives $L_k$). "Monotonically decreasing" on the page means non-increasing, and "convex in $x_t$" means convex in $x_k$.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 28, Lemma 7.1; p. 4, (8)–(9) and P1–P2

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Setting

namespace AffinePolicyOpt.OneDim

/-- Lemma 7.1 with (8)–(9) and P2: `J*_k` and `g_k` are convex; for every minimizer `y*` of
`c_k y + g_k(y)` the clamp `max(L_k, min(U_k, y* − x))` is an optimal control at state `x` and
`J*_k(x)` is its value; if `c_k y + g_k(y)` has no minimizer, `u = L_k` is optimal at every `x`. -/
theorem lemma_7_1 {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) :
    ConvexOn ℝ Set.univ (Jstar M k) ∧
    ConvexOn ℝ Set.univ (gFun M k (Jstar M ((k : ℕ) + 1))) ∧
    (∀ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (max (M.L k) (min (M.U k) (ystar - x))) ∧
          Jstar M k x = M.c k * max (M.L k) (min (M.U k) (ystar - x)) +
              gFun M k (Jstar M ((k : ℕ) + 1)) (x + max (M.L k) (min (M.U k) (ystar - x)))) ∧
    ((¬ ∃ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar) →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (M.L k) ∧
          Jstar M k x = M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k)) := by sorry

end AffinePolicyOpt.OneDim
