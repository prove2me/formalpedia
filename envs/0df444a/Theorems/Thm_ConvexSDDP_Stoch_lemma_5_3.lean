-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_5_3
-- name    : ConvexSDDP.Stoch.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:44.328975+00:00
-- url     : https://prove2.me/theorems/1a37e813-5e6b-4e95-b38d-bf0a78cceb41
-- title:
--   Lemma 5.3, p. 25 — under Definition 1 (i), a node selected inside a block sees the stock and approximation of the block's start
-- statement:
--   Fix choice rules, a selection path satisfying property (i) of Definition 1 for an integer $\tau>0$, and a run of the algorithm. Then for every $k\in\mathbb N$, $\kappa\in\{0,\dots,\tau-1\}$ and every non-leaf node $n$,
--   $$y^{k\tau+\kappa}_n=1\ \Longrightarrow\ \begin{cases}x^{k\tau+\kappa}_n=x^{k\tau}_n,\\ V^{k\tau+\kappa-1}_n=V^{k\tau-1}_n&\text{if }k\ge1.\end{cases}$$
--
--   Inside a block of $\tau$ iterations the cuts are computed backwards, so a node selected at step $\kappa$ of the block is visited at the stock it had at the start of the block, with the approximation it had then. This lets the proof of Theorem 3.1 compare iterations $k\tau$ and $k\tau+\kappa$.
--
--   **Formalization Note** Index shift: the paper's $V^{k\tau+\kappa-1}_n$ is `r.Vc (k * τ + κ) n` and $V^{k\tau-1}_n$ is `r.Vc (k * τ) n`; the page's "if $k\ge1$" is kept. Only property (i) of Definition 1 is used, along the given path, so assumptions $(H_2)$ and the probabilistic properties (ii)–(iii) are not hypotheses. The statement depends on the choices being made by fixed rules (footnote 6, p. 26): two iterations solving the same stage problem make the same choice.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 25, Lemma 5.3; p. 26, footnote 6

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
open StochasticProg.Multistage

namespace ConvexSDDP.Stoch

theorem lemma_5_3 {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) (τ : ℕ) (hτ : 0 < τ) (hadm : AdmissibleI T ys τ) :
    ∀ k κ n, κ < τ → ¬ IsLeaf T n → ys (k * τ + κ) n = true →
      r.x (k * τ + κ) n = r.x (k * τ) n ∧
      (1 ≤ k → r.Vc (k * τ + κ) n = r.Vc (k * τ) n) := by sorry

end ConvexSDDP.Stoch
