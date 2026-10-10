-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_i
-- name    : ConvexSDDP.Stoch.lemma_3_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:46.156808+00:00
-- url     : https://prove2.me/theorems/9539c52b-d2db-438d-b3df-4a21f7776796
-- title:
--   Lemma 3.1 (i), p. 16 — every future cost function $V_n$ is convex, and finite and Lipschitz on $\mathcal X_n$
-- statement:
--   Assume $(H_2)$. For every node $n$ of the tree, the future cost function $V_n$ of (20) is convex on $\mathbb R^d$ (as a function with values in $\mathbb R\cup\{+\infty\}$), finite on $\mathcal X_n$, and Lipschitz continuous on $\mathcal X_n$: there is $L$ with
--   $$|V_n(y)-V_n(z)|\le L\,\|y-z\|\qquad(y,z\in\mathcal X_n).$$
--
--   The Lipschitz constants of the $V_n$ control how fast the approximation errors propagate in the proof of Lemma 3.2.
--
--   **Formalization Note** The page writes "Lipschitz-continuous on $\mathcal X_t$"; in §3 the node set is $\mathcal X_n$. $V_n$ is $+\infty$ off $\mathcal X_n$ (constraint (19d)), so convexity is the convexity of its epigraph; finiteness on $\mathcal X_n$ is stated explicitly because the Lipschitz bound is written on real values.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 16, Lemma 3.1 (i)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
open StochasticProg.Multistage

namespace ConvexSDDP.Stoch

theorem lemma_3_1_i {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2) :
    ∀ n, ConvexSDDP.Det.EConvex (M.V n) ∧ (∀ y ∈ M.X n, M.V n y ≠ ⊤ ∧ M.V n y ≠ ⊥) ∧
      ∃ L : ℝ, ∀ y ∈ M.X n, ∀ z ∈ M.X n,
        |(M.V n y).toReal - (M.V n z).toReal| ≤ L * ‖y - z‖ := by sorry

end ConvexSDDP.Stoch
