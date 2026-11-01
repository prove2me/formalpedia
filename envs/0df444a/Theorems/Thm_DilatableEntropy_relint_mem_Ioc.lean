-- Prove2me | Theorems.Thm_DilatableEntropy_relint_mem_Ioc
-- name    : DilatableEntropy.relint_mem_Ioc
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:05.318123+00:00
-- url     : https://prove2.me/theorems/3026342e-539e-498b-b3c6-5f8945021a78
-- title:
--   Proof of Theorem 4 — $\operatorname{relint}Q\subseteq(0,1]^\Sigma$ (corrected: $(0,1]$ instead of $(0,1)$)
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   Every point of the relative interior of $Q$ has all its coordinates in $(0,1]$:
--   $$
--   x\in\operatorname{relint}Q\ \Longrightarrow\ 0<x_\sigma\le 1\quad\text{for all }\sigma\in\Sigma .
--   $$
--
--   This is where $\tilde\varphi$ is differentiable, and $x_\sigma\le1$ is the inequality behind the Hessian bound $\nabla^2\tilde\varphi(x)\succeq I$ in the proof of Theorem 4.
--
--   **Formalization Note** The relative interior is Mathlib's `intrinsicInterior ℝ`, the interior of $Q$ inside its affine span.
--
--   Differences from the source:
--   - correction: relint Q ⊆ (0,1)^{|Σ|} → every x ∈ relint Q has 0 < x_σ ≤ 1; reason: x_∅ = 1 for every x ∈ Q (and x_{ja} = 1 when j is reached surely and |A_j| = 1), so the open cube excludes every point of Q; the proof only uses 0 < x_σ ≤ 1
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, proof of Theorem 4, p.12

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, proof of Theorem 4, p.12 ("The function `φ̃` is twice-differentiable on
`(0,1)^{|Σ|} ⊇ relint Q`"), corrected: every point of the relative interior of the
sequence-form polytope has all coordinates in `(0, 1]`.

**Formalization Note** The printed inclusion `relint Q ⊆ (0,1)^{|Σ|}` is false: `x_∅ = 1` for
every `x ∈ Q` (and `x_{ja} = 1` whenever `j` is reached with certainty and has one action).
The proof only uses `0 < x_σ ≤ 1`. The relative interior is Mathlib's `intrinsicInterior ℝ`. -/
theorem relint_mem_Ioc (P : SeqDecisionProblem) :
    ∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P), ∀ σ : Seq P, 0 < x σ ∧ x σ ≤ 1 := by sorry

end DilatableEntropy
