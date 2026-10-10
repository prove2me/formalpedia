-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_iii
-- name    : ConvexSDDP.Stoch.lemma_3_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:22.640338+00:00
-- url     : https://prove2.me/theorems/f6d5802c-22f1-4d6f-bcc2-9d052d202da0
-- title:
--   Lemma 3.1 (iii), p. 16 — the cut slopes are bounded and the approximations are uniformly Lipschitz
-- statement:
--   Assume $(H_2)$, fix choice rules, any selection path, and a run of the algorithm. For every non-leaf node $n$ there is $\alpha_n\ge0$ such that
--   1. $\|\beta^k_n\|\le\alpha_n$ for every iteration $k$ at which the cut value $\theta^k_n$ is finite, and
--   2. for every $k$, if the approximation $V^{k-1}_n$ is finite at some point, then it is finite everywhere and $\alpha_n$-Lipschitz:
--   $$|V^{k-1}_n(y)-V^{k-1}_n(z)|\le\alpha_n\|y-z\|\qquad(y,z\in\mathbb R^d).$$
--
--   The uniform Lipschitz constant is what allows Lemma 5.2 to be applied in the proof of Theorem 3.1 (footnote 5, p. 21).
--
--   **Formalization Note** Index shift: `r.Vc k n` is the paper's $V^{k-1}_n$. The page states that "the sequences $(\beta^k_n)_{k}$ are bounded". With the initialisation $V^{-1}_n\equiv-\infty$, the approximation stays $-\infty$ until a finite cut has been computed at $n$; during those iterations $\theta^k_n=-\infty$ and any vector is a subgradient of $-\infty$, so the printed claim fails for those iterations. The Lean bounds the slopes of the finite cuts and the Lipschitz constant where the approximation is finite, which is what the proofs use.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 16, Lemma 3.1 (iii); p. 17, (27)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace ConvexSDDP.Stoch

theorem lemma_3_1_iii {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ n, ¬ IsLeaf T n → ∃ α : ℝ, 0 ≤ α ∧
      (∀ k, r.θ k n ≠ ⊥ → ‖r.β k n‖ ≤ α) ∧
      ∀ k y z, r.Vc k n y ≠ ⊥ →
        (r.Vc k n z ≠ ⊥ ∧ |(r.Vc k n y).toReal - (r.Vc k n z).toReal| ≤ α * ‖y - z‖) := by sorry

end ConvexSDDP.Stoch
