-- Prove2me | Theorems.Thm_DilatableEntropy_one_le_gamma
-- name    : DilatableEntropy.one_le_gamma
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:45.0956+00:00
-- url     : https://prove2.me/theorems/9cd23bcc-51cb-45d9-97b7-db59b573a395
-- title:
--   Definition 4 — the weights satisfy $\gamma_j\ge1$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   Every weight $\gamma_j$ of the dilatable global entropy (Definition 4, eq. (8)) is at least one:
--   $$
--   \gamma_j\ge 1\qquad(j\in J).
--   $$
--
--   Together with $w_\sigma\ge1$ it controls the size and the curvature of $\tilde\varphi$.
--
--   Differences from the source:
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, p.10 (γ_j ≥ 1)

import Mathlib
import Definitions.Def_DilatableEntropy_gamma

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, p.10: every weight `γ_j` (`j ∈ J`) of the dilatable global entropy is at
least `1` ("where each `γ_j ≥ 1` (`j ∈ J`) is defined resursively as"). -/
theorem one_le_gamma (P : SeqDecisionProblem) : ∀ j : P.J, 1 ≤ gamma P j := by sorry

end DilatableEntropy
