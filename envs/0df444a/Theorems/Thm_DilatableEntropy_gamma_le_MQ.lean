-- Prove2me | Theorems.Thm_DilatableEntropy_gamma_le_MQ
-- name    : DilatableEntropy.gamma_le_MQ
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:19.0071+00:00
-- url     : https://prove2.me/theorems/e65083ec-7ffd-4378-aae2-20009652b870
-- title:
--   Proof of Theorem 6 — $\gamma$ is largest at root decision points, and $\gamma_j\le M_Q$ for every decision point
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   The weights $\gamma_j$ of (8) are largest at root decision points, and every one of them is at most the largest $\ell_1$ norm of a sequence-form strategy:
--   $$
--   \forall j\in J\ \exists r\in J:\ p_r=\varnothing,\ \gamma_j\le\gamma_r;\qquad
--   \gamma_j\le M_Q=\max_{x\in Q}\|x\|_1\quad\text{for all }j\in J .
--   $$
--
--   This is the fourth inequality in the proof of the range bound (Theorem 6).
--
--   Differences from the source:
--   - reading: γ_j is largest at root decision points, where it is at most M_Q → the maximum of γ over J is attained at a root (∀ j, ∃ r, p_r = ∅ ∧ γ_j ≤ γ_r), and γ_j ≤ M_Q for every j ∈ J; reason: that is the literal sense of 'largest at root decision points'; given the first clause, the bound at the roots and the bound for all j are equivalent, and the fourth inequality of the proof uses the latter
--   - encoding: M_Q := max_{x∈Q} ‖x‖₁ (p.4) → MQ P := sSup ((fun x => ∑ σ, |x σ|) '' Q); reason: Q is nonempty and compact, so the supremum is the maximum
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, proof of Theorem 6, p.13 (fourth inequality; cf. the remark on p.11)

import Mathlib
import Definitions.Def_DilatableEntropy_gamma
import Definitions.Def_DilatableEntropy_MQ

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, proof of Theorem 6, p.13 (the fourth inequality): "`γ_j` is largest at root decision
points, where it is at most `M_Q`": the maximum of `γ` over `J` is attained at a root decision
point (`p_r = ∅`), and `γ_j ≤ M_Q` for every decision point `j`. -/
theorem gamma_le_MQ (P : SeqDecisionProblem) :
    (∀ j : P.J, ∃ r : P.J, P.parent r = none ∧ gamma P j ≤ gamma P r) ∧
      ∀ j : P.J, gamma P j ≤ MQ P := by sorry

end DilatableEntropy
