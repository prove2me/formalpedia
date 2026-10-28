-- Prove2me | Theorems.Thm_DecisionForest_Universal_forest_marginal
-- name    : DecisionForest.Universal.forest_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:36.747962+00:00
-- url     : https://prove2.me/theorems/4ce7e5fc-6e4f-45dc-9cae-6647a643fb1d
-- title:
--   Proof of Theorem 1, p. ec3 — the forest of all (N + 1)^{2^N} balanced trees with weights (EC.5) reproduces P(o | S)
-- statement:
--   Let $\mathbf P(\cdot\mid\cdot)$ be a discrete choice model on $N$ products. For every tuple $\mathbf o=(o_S)_{S\subseteq\mathcal N}$ of purchase options let $t_{\mathbf o}$ be the balanced tree of the proof of Theorem 1 and $\lambda_{\mathbf o}=\prod_{S}\mathbf P(o_S\mid S)$ its weight (EC.5). Then for every assortment $S\subseteq\mathcal N$ and every option $o\in\mathcal N^+$,
--   $$\sum_{\mathbf o}\lambda_{\mathbf o}\cdot\mathbb I\{o=\hat A(S,t_{\mathbf o})\}=\mathbf P(o\mid S),$$
--   the sum running over all $(N+1)^{2^N}$ tuples.
--
--   The left-hand side is the decision forest model (3) of the forest $\{t_{\mathbf o}\}$ with weights $\lambda$, before the trees violating Requirement 2 are removed; this identity is the last step of the proof of Theorem 1.
--
--   **Formalization Note** The sum is over all functions `o : Finset (Fin N) → Option (Fin N)`, and $\mathbb I\{o=\hat A(S,t_{\mathbf o})\}$ is `if choose (fullTree o) S = o' then 1 else 0`.
--
--   Differences from the source:
--   - encoding: the forest $F$ of trees $t=1,\dots,(N+1)^{2^N}$ and $\mathbf P^{(F,\lambda)}(o\mid S_i)$ → the sum over tuples $\mathbf o$ of $\lambda_{\mathbf o}\,\mathbb I\{o=\hat A(S,t_{\mathbf o})\}$; reason: the trees of the forest are indexed by the tuples, same sum.
--   - encoding: products $\{1,\dots,N\}$ → `Fin N`, options $\mathcal N^+$ → `Option (Fin N)` with `none` the option $0$; reason: Lean convention, same instances.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, p. ec3 (PDF 32), proof of Theorem 1, final display

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem forest_marginal (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (S : Finset (Fin N)) (o' : Option (Fin N)) :
    ∑ o : Finset (Fin N) → Option (Fin N),
      prodWeight P o * (if choose (fullTree o) S = o' then 1 else 0) = P o' S := by sorry

end DecisionForest.Universal
