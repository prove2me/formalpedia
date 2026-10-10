-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_eq_26
-- name    : ConvexSDDP.Stoch.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:09.009365+00:00
-- url     : https://prove2.me/theorems/d858e16e-69eb-4ca4-98df-6a036ab95ddf
-- title:
--   (26), p. 16 — the new cut is tight at the current stock: $V^k_n(x^k_n)=\theta^k_n$
-- statement:
--   Assume $(H_2)$, fix choice rules, any selection path, and a run of the algorithm. Then for every iteration $k$ and every non-leaf node $n$,
--   $$V^k_n(x^k_n)=\max\big(V^{k-1}_n(x^k_n),\theta^k_n\big)=\theta^k_n,$$
--   and if $n$ is selected at iteration $k$,
--   $$\theta^k_n=\sum_{m\in r(n)}\frac{\Phi_m}{\Phi_n}\,W^{k-1}_m(x^k_n,u^k_m),\qquad W^{k-1}_m(x,u)=C_m(x,u)+V^{k-1}_m\big(f_m(x,u)\big).$$
--
--   The cut computed at iteration $k$ is never dominated by the previous approximation at the point where it is computed. This is used in the proof of Lemma 3.2 and of Theorem 3.1.
--
--   **Formalization Note** Index shift: the paper's $V^k_n$ is `r.Vc (k + 1) n` and $V^{k-1}_m$ is `r.Vc k m`. $W^{k-1}_m(x^k_n,u^k_m)$ is written $C_m(x^k_n,u^k_m)+V^{k-1}_m(x^k_m)$, using $x^k_m=f_m(x^k_n,u^k_m)$. The statement holds along every selection path; no probability is involved.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 16, (26) and the note after it

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace ConvexSDDP.Stoch

theorem eq_26 {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ k n, ¬ IsLeaf T n →
      r.Vc (k + 1) n (r.x k n) = r.θ k n ∧
      (ys k n = true → r.θ k n = ∑ m ∈ T.children n,
        ((M.Φ m / M.Φ n : ℝ) : EReal) * (M.C m (r.x k n) (r.u k m) + r.Vc k m (r.x k m))) := by sorry

end ConvexSDDP.Stoch
