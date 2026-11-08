-- Prove2me | Theorems.Thm_DilatableEntropy_sum_parent_le_MQ
-- name    : DilatableEntropy.sum_parent_le_MQ
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:52:23.979397+00:00
-- url     : https://prove2.me/theorems/4686446c-434d-42e1-ae8d-1b5ade62c9c6
-- title:
--   Proof of Theorem 6 — $\sum_{j\in J}x_{p_j}\le M_Q$ on $Q$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   For every sequence-form strategy $x\in Q$,
--   $$
--   \sum_{j\in J}x_{p_j}\ \le\ M_Q .
--   $$
--
--   This is the fifth inequality in the proof of the range bound (Theorem 6).
--
--   Differences from the source:
--   - encoding: M_Q := max_{x∈Q} ‖x‖₁ (p.4) → MQ P := sSup ((fun x => ∑ σ, |x σ|) '' Q); reason: Q is nonempty and compact, so the supremum is the maximum
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, proof of Theorem 6, p.13 (fifth inequality)

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_MQ

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, proof of Theorem 6, p.13 (the fifth inequality "upper bounds `∑_{j ∈ J} x_{p_j}` by
`M_Q`"): for every `x ∈ Q`, `∑_{j ∈ J} x_{p_j} ≤ M_Q`. -/
theorem sum_parent_le_MQ (P : SeqDecisionProblem) :
    ∀ x ∈ seqFormPolytope P, ∑ j : P.J, x (P.parent j) ≤ MQ P := by sorry

end DilatableEntropy
