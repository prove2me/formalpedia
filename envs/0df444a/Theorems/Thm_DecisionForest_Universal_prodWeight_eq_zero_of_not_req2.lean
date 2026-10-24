-- Prove2me | Theorems.Thm_DecisionForest_Universal_prodWeight_eq_zero_of_not_req2
-- name    : DecisionForest.Universal.prodWeight_eq_zero_of_not_req2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:41.747252+00:00
-- url     : https://prove2.me/theorems/02299bde-b0ff-41e6-8c93-a6cee597332d
-- title:
--   Proof of Theorem 1, p. ec2 — a constructed tree that violates Requirement 2 has weight λ_t = 0 in (EC.5)
-- statement:
--   Let $\mathbf P(\cdot\mid\cdot)$ be a discrete choice model on $N$ products and let $\mathbf o=(o_S)_{S\subseteq\mathcal N}$ be a tuple of purchase options. If the balanced tree $t_{\mathbf o}$ of the proof of Theorem 1 violates Requirement 2, i.e. some leaf of $t_{\mathbf o}$ buys a product that is not among the products found present on the path to it, then its weight (EC.5) vanishes:
--   $$\lambda_{\mathbf o}=\prod_{S\subseteq\mathcal N}\mathbf P(o_S\mid S)=0 .$$
--
--   Consequently the trees violating Requirement 2 can be removed from the forest without changing the model, and the remaining trees lie in $F_{N+1}$.
--
--   **Formalization Note** The hypothesis is `¬ Req2 (fullTree o)`. In `fullTree o` the products found present on the way to the leaf of assortment $S$ are exactly the products of $S$, so the hypothesis says that $o_S$ is a product outside $S$ for some $S$.
--
--   Differences from the source:
--   - reading: "for some trees $o^t_j$ will not be contained in $S_j$ … $\mathbf P(o^t_j\mid S_j)$ is zero whenever $o^t_j\notin S_j$" → the hypothesis is that the tree violates Requirement 2, i.e. some $o_S$ is a product outside $S$; reason: the no-purchase option $0$ is never in $S_j$, never violates Requirement 2, and $\mathbf P(0\mid S_j)$ need not vanish (taking $\mathbf P(0\mid S)=1$ for all $S$ gives a choice model), so the sentence is about products; the literal reading for $o=0$ is false.
--   - encoding: products $\{1,\dots,N\}$ → `Fin N`, options $\mathcal N^+$ → `Option (Fin N)`; tuples indexed by assortments instead of $j=1,\dots,2^N$; reason: Lean convention, same instances.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, p. ec2 (PDF 31), proof of Theorem 1, paragraph after (EC.5)

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem prodWeight_eq_zero_of_not_req2 (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (o : Finset (Fin N) → Option (Fin N))
    (h : ¬ Req2 (fullTree o)) : prodWeight P o = 0 := by sorry

end DecisionForest.Universal
