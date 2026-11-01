-- Prove2me | Theorems.Thm_DilatableEntropy_dge_eq_dilatedEntropy
-- name    : DilatableEntropy.dge_eq_dilatedEntropy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:14.806936+00:00
-- url     : https://prove2.me/theorems/dd72b2e1-d8e1-45bd-930e-3a5074fc43e4
-- title:
--   Theorem 3 — dilatability: $\tilde\varphi=\varphi$ on $Q$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   The dilatable global entropy $\tilde\varphi$ (Definition 4) and the dilated entropy $\varphi$ with weights $\gamma$ coincide on the polytope of sequence-form strategies:
--   $$
--   \tilde\varphi(x)=\varphi(x)\qquad\text{for all }x\in Q .
--   $$
--
--   Consequently the smoothed support function $\nabla\tilde\varphi^*$ equals $\nabla\varphi^*$ and is computable in linear time, as for every dilated DGF.
--
--   Differences from the source:
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Theorem 3, p.11

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_dge
import Definitions.Def_DilatableEntropy_dilatedEntropy

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Theorem 3, p.11 (dilatability): the dilatable global entropy and the dilated entropy
with weights `γ` coincide on the sequence-form polytope: `φ̃(x) = φ(x)` for all `x ∈ Q`. -/
theorem dge_eq_dilatedEntropy (P : SeqDecisionProblem) :
    ∀ x ∈ seqFormPolytope P, dge P x = dilatedEntropy P x := by sorry

end DilatableEntropy
