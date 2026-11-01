-- Prove2me | Theorems.Thm_DilatableEntropy_dge_strongly_convex_l1
-- name    : DilatableEntropy.dge_strongly_convex_l1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:26.861676+00:00
-- url     : https://prove2.me/theorems/c5245c77-bb47-4043-8c44-d3316319a61e
-- title:
--   Theorem 5 — $\tilde\varphi$ is $1/M_Q$-strongly convex on $\operatorname{relint}Q$ in $\ell_1$
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   The dilatable global entropy $\tilde\varphi$ is strongly convex with modulus $1/M_Q$ with respect to the $\ell_1$ norm on $\operatorname{relint}Q$: for all $x,x'\in\operatorname{relint}Q$,
--   $$
--   \big(\nabla\tilde\varphi(x)-\nabla\tilde\varphi(x')\big)^{\top}(x-x')\ \ge\ \frac1{M_Q}\,\|x-x'\|_1^2=\frac1{M_Q}\Big(\sum_{\sigma\in\Sigma}|x_\sigma-x'_\sigma|\Big)^2 ,
--   $$
--   where $M_Q=\max_{x\in Q}\|x\|_1$.
--
--   This matches the modulus of the Kroer et al. dilated entropy, whose weights grow exponentially in the depth, while the weights of $\tilde\varphi$ grow linearly.
--
--   **Formalization Note** $\nabla\tilde\varphi(x)^\top v$ is the Fréchet derivative of the formula of Definition 4; the $\ell_1$ norm is the explicit sum of absolute values; the relative interior is `intrinsicInterior ℝ`.
--
--   Differences from the source:
--   - encoding: ∇φ̃ of φ̃ : Q → ℝ≥0, with the closed form (1 + log x_σ) w_σ + Σ_{j∈C_σ} γ_j log|A_j| on relint Q (p.11) → dge P defined by the formula of Definition 4 on all of ℝ^Σ (Real.log, 0·log 0 = 0); ∇φ̃(x)ᵀv = fderiv ℝ (dge P) x v; reason: the paper differentiates the formula of Definition 4; x − x′ is tangent to Q, so the inner product does not depend on the extension
--   - encoding: M_Q := max_{x∈Q} ‖x‖₁ (p.4) → MQ P := sSup ((fun x => ∑ σ, |x σ|) '' Q); reason: Q is nonempty and compact, so the supremum is the maximum
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Theorem 5, p.12

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_dge
import Definitions.Def_DilatableEntropy_MQ

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Theorem 5, p.12: the dilatable global entropy `φ̃` is strongly convex modulus `1/M_Q`
with respect to the `ℓ1` norm on `relint Q`:
`(∇φ̃(x) − ∇φ̃(x'))ᵀ(x − x') ≥ (1/M_Q) ‖x − x'‖₁²` for all `x, x' ∈ relint Q`.

**Formalization Note** `∇φ̃(x)ᵀv` is `fderiv ℝ (dge P) x v` of the formula of Definition 4;
the `ℓ1` norm is the explicit sum `∑_σ |v_σ|`; `M_Q` is `MQ P` (`x_∅` counted); the relative
interior is `intrinsicInterior ℝ`. -/
theorem dge_strongly_convex_l1 (P : SeqDecisionProblem) :
    ∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P),
      ∀ x' ∈ intrinsicInterior ℝ (seqFormPolytope P),
        1 / MQ P * (∑ σ, |x σ - x' σ|) ^ 2 ≤
          fderiv ℝ (dge P) x (x - x') - fderiv ℝ (dge P) x' (x - x') := by sorry

end DilatableEntropy
