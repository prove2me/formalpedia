-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_ii
-- name    : ConvexSDDP.Stoch.lemma_3_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:57.00883+00:00
-- url     : https://prove2.me/theorems/4cddf5e9-5a03-4e6c-abc8-110f1a7319b4
-- title:
--   Lemma 3.1 (ii), p. 16 — the approximations stay below $\tilde V_n$ on $\operatorname{Aff}(\mathcal X_n)$, and $\tilde V_n\le V_n$
-- statement:
--   Assume $(H_2)$, fix choice rules, any selection path, and a run of the algorithm. For every non-leaf node $n$ and every iteration $k$ (including the initial approximation $V^{-1}_n\equiv-\infty$),
--   $$V^{k-1}_n(y)\le\tilde V_n(y)\quad(y\in\operatorname{Aff}(\mathcal X_n)),\qquad \tilde V_n(y)\le V_n(y)\quad(y\in\mathbb R^d).$$
--
--   So the cutting-plane approximations are valid lower bounds of the future cost functions; this is used in Lemma 3.1 (iii), Lemma 3.2 and Theorem 3.1.
--
--   **Formalization Note** Index shift: `r.Vc k n` is the paper's $V^{k-1}_n$. The page states $V^k_n\le\tilde V_n$ without restriction; the Lean restricts the first inequality to the affine hull of $\mathcal X_n$, where the Lagrange multipliers of (21) are defined. Off the affine hull the printed inequality can fail: with $\mathcal X_n=\{0\}\subset\mathbb R$, one leaf child $m$, $\mathcal U_m\equiv\{0\}$, $f_m=0$, $\mathcal X_m=\{0\}$, $V_m\equiv0$ and $C_m(x,u)=-x$, one has $\tilde V_n(y)=-y$, the multiplier is $0$, and after the first cut $V^k_n\equiv0>\tilde V_n(1)$. The proofs only evaluate the approximations on $\operatorname{Aff}(\mathcal X_n)$. Ṽ is defined only at non-leaves; at a leaf $V^k_n=V_n$ by definition. "$\beta^k_n$ is defined" is the companion statement `run_exists`.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 16, Lemma 3.1 (ii)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace ConvexSDDP.Stoch

theorem lemma_3_1_ii {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ k n, ¬ IsLeaf T n →
      (∀ y ∈ affineSpan ℝ (M.X n), r.Vc k n y ≤ M.Vtilde n y) ∧
      ∀ y, M.Vtilde n y ≤ M.V n y := by sorry

end ConvexSDDP.Stoch
