-- Prove2me | Theorems.Thm_DilatableEntropy_one_le_weight
-- name    : DilatableEntropy.one_le_weight
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:04.320221+00:00
-- url     : https://prove2.me/theorems/e271c2a9-6579-4cb6-b220-c0a32fa41bbc
-- title:
--   Definition 4 — the weights satisfy $w_\sigma\ge1$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   Every weight $w_\sigma$ of the dilatable global entropy (Definition 4) is at least one:
--   $$
--   w_\sigma\ge1\qquad(\sigma\in\Sigma).
--   $$
--   In particular $w_\varnothing=1$.
--
--   The bound $w_{ja}\ge1$ is what makes the Hessian of $\tilde\varphi$ dominate the identity on $(0,1]^\Sigma$ (Theorems 4 and 5).
--
--   Differences from the source:
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, p.10 (w_σ ≥ 1)

import Mathlib
import Definitions.Def_DilatableEntropy_weight

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, p.10: every weight `w_σ` (`σ ∈ Σ`, including `w_∅`) of the dilatable
global entropy is at least `1` ("and each `w_σ ≥ 1` (`σ ∈ Σ`) is defined recursively as"). -/
theorem one_le_weight (P : SeqDecisionProblem) : ∀ σ : Seq P, 1 ≤ weight P σ := by sorry

end DilatableEntropy
