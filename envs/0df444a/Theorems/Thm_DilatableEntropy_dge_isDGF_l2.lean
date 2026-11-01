-- Prove2me | Theorems.Thm_DilatableEntropy_dge_isDGF_l2
-- name    : DilatableEntropy.dge_isDGF_l2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:54.422818+00:00
-- url     : https://prove2.me/theorems/bbc70911-083c-447d-a83d-0c9fb93e1d9e
-- title:
--   Theorem 4 — $\tilde\varphi$ is a DGF for $Q$, 1-strongly convex on $\operatorname{relint}Q$ in $\ell_2$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   The dilatable global entropy $\tilde\varphi$ is a distance-generating function for $Q$ that is $1$-strongly convex on $\operatorname{relint}Q$ with respect to the $\ell_2$ norm:
--
--   1. $\tilde\varphi$ is continuous on $Q$;
--   2. $\tilde\varphi$ is differentiable at every point of $\operatorname{relint}Q$;
--   3. $\tilde\varphi\ge0$ on $Q$ and $\tilde\varphi(x)=0$ for some $x\in Q$;
--   4. for all $x,x'\in\operatorname{relint}Q$,
--   $$
--   \big(\nabla\tilde\varphi(x)-\nabla\tilde\varphi(x')\big)^{\top}(x-x')\ \ge\ \|x-x'\|_2^2=\sum_{\sigma\in\Sigma}(x_\sigma-x'_\sigma)^2 .
--   $$
--
--   With the $\ell_2$ norm this gives the proximal setup for EGT and mirror prox with modulus one, independent of the depth of the tree.
--
--   **Formalization Note** $\nabla\tilde\varphi(x)^\top v$ is the Fréchet derivative of the formula of Definition 4 at $x$ applied to $v$; the squared $\ell_2$ norm is the explicit sum of squares; the relative interior is `intrinsicInterior ℝ`.
--
--   Differences from the source:
--   - reading: φ̃ is a DGF for Q (Definition 1: continuous on Q, differentiable on relint Q, strongly convex on relint Q; common assumption min_Q d = 0; Definition 4 codomain ℝ≥0) → ContinuousOn (dge P) Q ∧ DifferentiableAt ℝ (dge P) x for x ∈ relint Q ∧ (0 ≤ dge P on Q ∧ ∃ x ∈ Q, dge P x = 0), with strong convexity given by the ℓ2 clause; reason: Definition 1 lists these properties and the proof of Theorem 4 verifies the minimum 0; compactness and convexity of Q are Definition 1's precondition on the domain, not a property of φ̃, and hold because Q is a polytope
--   - encoding: ∇φ̃ of φ̃ : Q → ℝ≥0, with the closed form (1 + log x_σ) w_σ + Σ_{j∈C_σ} γ_j log|A_j| on relint Q (p.11) → dge P defined by the formula of Definition 4 on all of ℝ^Σ (Real.log, 0·log 0 = 0); ∇φ̃(x)ᵀv = fderiv ℝ (dge P) x v; reason: the paper differentiates the formula of Definition 4; x − x′ is tangent to Q, so the inner product does not depend on the extension
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Theorem 4, p.12

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_dge

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Theorem 4, p.12: the dilatable global entropy `φ̃ : Q → ℝ_{≥0}` is a DGF for the
sequence-form polytope `Q` (Definition 1, p.4), `1`-strongly convex on `relint Q` with respect
to the `ℓ2` norm:
1. `φ̃` is continuous on `Q`;
2. `φ̃` is differentiable at every point of `relint Q`;
3. `φ̃ ≥ 0` on `Q` and `min_{x ∈ Q} φ̃(x) = 0`;
4. `(∇φ̃(x) − ∇φ̃(x'))ᵀ(x − x') ≥ ‖x − x'‖₂²` for all `x, x' ∈ relint Q`.

**Formalization Note** `φ̃` is the formula of Definition 4 on all of `ℝ^Σ` and `∇φ̃(x)ᵀv` is
`fderiv ℝ (dge P) x v`; the squared `ℓ2` norm is the explicit sum `∑_σ v_σ²` (Mathlib's norm on
`Seq P → ℝ` is the sup norm). The relative interior is `intrinsicInterior ℝ`. -/
theorem dge_isDGF_l2 (P : SeqDecisionProblem) :
    ContinuousOn (dge P) (seqFormPolytope P) ∧
      (∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P), DifferentiableAt ℝ (dge P) x) ∧
      ((∀ x ∈ seqFormPolytope P, 0 ≤ dge P x) ∧ ∃ x ∈ seqFormPolytope P, dge P x = 0) ∧
      ∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P),
        ∀ x' ∈ intrinsicInterior ℝ (seqFormPolytope P),
          ∑ σ, (x σ - x' σ) ^ 2 ≤ fderiv ℝ (dge P) x (x - x') - fderiv ℝ (dge P) x' (x - x') := by sorry

end DilatableEntropy
