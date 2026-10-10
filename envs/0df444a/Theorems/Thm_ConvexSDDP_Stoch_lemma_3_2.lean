-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_3_2
-- name    : ConvexSDDP.Stoch.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:13.280979+00:00
-- url     : https://prove2.me/theorems/9eb0432b-526f-4543-9846-c5962cf4b571
-- title:
--   Lemma 3.2, p. 17 — exact cuts at the children make the decisions at a node asymptotically optimal
-- statement:
--   Assume $(H_2)$, fix choice rules, any selection path, and a run of the algorithm. Let $n$ be a non-leaf node and $\tau'>0$ an integer such that for every child $m\in r(n)$
--   $$\lim_{k\to+\infty}V_m\big(x^{k\tau'}_m\big)-V^{k\tau'}_m\big(x^{k\tau'}_m\big)=0.$$
--   Then
--   $$\lim_{k\to+\infty}\ \sum_{m\in r(n)}\frac{\Phi_m}{\Phi_n}W_m\big(x^{k\tau'}_n,u^{k\tau'}_m\big)-V_n\big(x^{k\tau'}_n\big)=0,$$
--   where $W_m(x,u)=C_m(x,u)+V_m(f_m(x,u))$ is the true cost-to-go of (24).
--
--   This propagates exactness of the approximations from the children of a node to the optimality of the decisions taken at the node; it is the inductive step of Theorem 3.1.
--
--   **Formalization Note** Index shift: the paper's $V^{k\tau'}_m$ is `r.Vc (k * τ' + 1) m`. Limits are taken in $\overline{\mathbb R}$, so convergence to $0$ forces the differences to be finite from some index on. As on the page, no property of the selection path is assumed.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 17, Lemma 3.2

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace ConvexSDDP.Stoch

theorem lemma_3_2 {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) (n : T.Node) (hn : ¬ IsLeaf T n) (τ' : ℕ) (hτ' : 0 < τ')
    (hch : ∀ m ∈ T.children n,
      Tendsto (fun k => M.V m (r.x (k * τ') m) - r.Vc (k * τ' + 1) m (r.x (k * τ') m))
        atTop (𝓝 0)) :
    Tendsto (fun k => (∑ m ∈ T.children n,
        ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m (r.x (k * τ') n) (r.u (k * τ') m)) -
        M.V n (r.x (k * τ') n)) atTop (𝓝 0) := by sorry

end ConvexSDDP.Stoch
