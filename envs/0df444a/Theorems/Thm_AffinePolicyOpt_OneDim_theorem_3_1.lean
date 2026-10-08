-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_theorem_3_1
-- name    : AffinePolicyOpt.OneDim.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:34.734158+00:00
-- url     : https://prove2.me/theorems/172ae934-b5a3-4dbd-bbea-6895449b21da
-- title:
--   Theorem 3.1, p. 5 — affine policies q_k and affine costs z_k exist with robust feasibility (12), domination (13) and J_mM preserved (14) at every k
-- statement:
--   Consider the one-dimensional min-max control problem (DP): state $x_{k+1}=x_k+u_k+w_k$ from a given $x_1$, controls $u_k\in[L_k,U_k]$, disturbances $w_k\in\mathcal W_k=[\underline w_k,\overline w_k]$, per-unit control costs $c_k\ge0$ and convex, coercive state costs $h_k$, over stages $k=1,\dots,T$. Let $J_{mM}=J^*_1(x_1)$ be its min-max value, computed by the Bellman recursion, and $J^*_{k+1}$ the optimal cost-to-go.
--
--   Then there exist coefficients $q_{k,0},q_{k,t}$ and $z_{k,0},z_{k,t}$ defining, for every stage $k$, an affine control policy and an affine running cost
--   $$q_k(w)=q_{k,0}+\sum_{t=1}^{k-1}q_{k,t}w_t,\qquad z_k(w)=z_{k,0}+\sum_{t=1}^{k}z_{k,t}w_t,$$
--   such that for every $k=1,\dots,T$:
--   $$L_k\le q_k(w)\le U_k\quad\forall w\in\mathcal W_1\times\dots\times\mathcal W_{k-1},\tag{12}$$
--   $$z_k(w)\ge h_k\Big(x_1+\sum_{t=1}^k\big(q_t(w)+w_t\big)\Big)\quad\forall w\in\mathcal W_1\times\dots\times\mathcal W_k,\tag{13}$$
--   $$J_{mM}=\max_{w_1,\dots,w_k}\Big[\sum_{t=1}^k\big(c_tq_t(w)+z_t(w)\big)+J^*_{k+1}\Big(x_1+\sum_{t=1}^k\big(q_t(w)+w_t\big)\Big)\Big].\tag{14}$$
--
--   At $k=T$ (where $J^*_{T+1}\equiv0$), (12)–(14) say that the disturbance-affine policies $q_k$ are robustly feasible and, with affine costs $z_k$ that dominate the true costs, achieve the min-max value: affine policies are optimal for this problem.
--
--   **Formalization Note** Stages are 0-based in Lean: `k : Fin T` is the paper's stage $K=k+1$, `Jstar M j` is the paper's $J^*_{j+1}$, so `Jstar M (k+1)` is $J^*_{K+1}$, the cost-to-go after stage $K$. One family $\{q_t,z_t\}$ is required to satisfy (12)–(14) at every stage simultaneously (the existential precedes "for every $k$"), which is how the proof builds them and implies the per-stage reading. The maximum in (14) is stated as `IsGreatest` over the image of the full disturbance box, so it asserts attainment as well as the value; quantifying over full sequences $w\in\mathcal W_1\times\dots\times\mathcal W_T$ is equivalent to quantifying over $(w_1,\dots,w_k)$ because the expression reads only coordinates up to $k$ and the box is a nonempty product. $J_{mM}$ is the Bellman value $J^*_1(x_1)$ over all state-feedback controls, not the value of the affine problem. The goal carries none of the proof's normalizations (Assumptions 1–3, the unique minimizer of footnote 4). The hypotheses $L_k\le U_k$ and $\underline w_k\le\overline w_k$ are added (the page writes nonempty intervals).
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 5, Theorem 3.1, (10)–(14)

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Setting

namespace AffinePolicyOpt.OneDim

/-- Theorem 3.1: affine policies `q_k` and affine running costs `z_k` exist such that, at every
stage `k`, (12) the policy is robustly feasible, (13) the affine cost dominates the convex state
cost, and (14) the min-max value `J_mM` is the worst case of the affine costs plus `J*_{k+1}`. -/
theorem theorem_3_1 {T : ℕ} (M : Model T) (hM : M.Standing) :
    ∃ (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ),
      ∀ k : Fin T,
        (∀ w, M.inBox w → M.L k ≤ qEval q0 q k w ∧ qEval q0 q k w ≤ M.U k) ∧
        (∀ w, M.inBox w → M.h k (M.xAff q0 q k w) ≤ zEval z0 z k w) ∧
        IsGreatest
          ((fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
                (M.c t * qEval q0 q t w + zEval z0 z t w)) +
              Jstar M ((k : ℕ) + 1) (M.xAff q0 q k w)) '' {w | M.inBox w})
          (JmM M) := by sorry

end AffinePolicyOpt.OneDim
