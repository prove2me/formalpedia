-- Prove2me | Theorems.Thm_DecisionForest_Universal_theorem_1
-- name    : DecisionForest.Universal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:32.279985+00:00
-- url     : https://prove2.me/theorems/c6d6dc3a-ddb1-42df-be7e-c35e016c3d6b
-- title:
--   Theorem 1, p. 11 — every customer choice model is a decision forest model over the purchase decision trees of depth at most N + 1
-- statement:
--   Consider $N$ products $\mathcal N=\{1,\dots,N\}$ and the purchase options $\mathcal N^+=\{0,1,\dots,N\}$, where $0$ is the no-purchase option. A **customer choice model** $\mathbf P(\cdot\mid\cdot)$ gives, for every assortment $S\subseteq\mathcal N$ (the empty one included), a probability distribution $\mathbf P(\cdot\mid S)$ on $\mathcal N^+$ with $\mathbf P(p\mid S)=0$ for every product $p\notin S$. Let $F_d$ be the set of purchase decision trees that satisfy Requirements 1–3 of §3.2 and have depth at most $d$, and for a finite forest $F$ with weights $\lambda$ let $\mathbf P^{(F,\lambda)}(o\mid S)=\sum_{t\in F}\lambda_t\,\mathbb I\{o=\hat A(S,t)\}$ be the decision forest model (3).
--
--   **Theorem 1.** For every customer choice model $\mathbf P(\cdot\mid\cdot)$ there is a probability distribution $\lambda$ over $F_{N+1}$ such that
--   $$\mathbf P(o\mid S)=\mathbf P^{(F_{N+1},\lambda)}(o\mid S)$$
--   for every assortment $S\subseteq\mathcal N$ and every purchase option $o\in\mathcal N^+$.
--
--   The theorem says that the decision forest model is universal: it represents every choice model, whether or not it is a random utility model or satisfies regularity, and trees of depth $N+1$ always suffice.
--
--   **Formalization Note** The distribution is given by a finite set `F` of trees contained in $F_{N+1}$ (`FSet N (N + 1)`) and weights `lam` that are nonnegative on `F` and sum to one over `F`; weights outside `F` never enter. Products are `Fin N`, options `Option (Fin N)` with `none` the no-purchase option, assortments `Finset (Fin N)`.
--
--   Differences from the source:
--   - encoding: a distribution $\lambda$ over $F_{N+1}$ → a finite set $F\subseteq F_{N+1}$ with weights nonnegative on $F$ summing to one over $F$; reason: $F_{N+1}$ is finite (p. 8), so every distribution on it is of this form (take $F=F_{N+1}$ or its support), and $\mathbf P^{(F_{N+1},\lambda)}=\mathbf P^{(F,\lambda)}$ when $\lambda$ vanishes off $F$.
--   - encoding: products $\{1,\dots,N\}$ → `Fin N` (product $k$ is `k - 1`), options $\mathcal N^+$ → `Option (Fin N)` with `none` the option $0$; reason: Lean convention, same instances.
--   - encoding: Requirement 1 → built into the type of trees `PTree N`; reason: every split carries a product by construction, same trees.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, p. 11, Theorem 1, (4)

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem theorem_1 (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P) :
    ∃ (F : Finset (PTree N)) (lam : PTree N → ℝ),
      (↑F ⊆ FSet N (N + 1)) ∧ (∀ t ∈ F, 0 ≤ lam t) ∧ ∑ t ∈ F, lam t = 1 ∧
      ∀ (S : Finset (Fin N)) (o : Option (Fin N)), P o S = forestProb F lam o S := by sorry

end DecisionForest.Universal
