-- Prove2me | Theorems.Thm_DilatableEntropy_dge_dgf_strongly_convex_range
-- name    : DilatableEntropy.dge_dgf_strongly_convex_range
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:12.443378+00:00
-- url     : https://prove2.me/theorems/ebbdad6a-0d27-4b2c-90e8-ae25f82239e7
-- title:
--   Theorems 4–6 — $\tilde\varphi$ is a DGF on $Q$, 1-strongly convex in $\ell_2$, $1/M_Q$ in $\ell_1$, range $\le M_Q^2\max_j\log|A_j|$ (corrected: diameter is max − min of $\tilde\varphi$ on $Q$)
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   For every sequential decision problem, the dilatable global entropy $\tilde\varphi$ (Definition 4) satisfies:
--
--   1. $\tilde\varphi$ is continuous on $Q$;
--   2. $\tilde\varphi$ is differentiable at every point of $\operatorname{relint}Q$;
--   3. $\tilde\varphi\ge0$ on $Q$ and $\tilde\varphi(x)=0$ for some $x\in Q$ (with 1, 2 and 4, $\tilde\varphi$ is a DGF for $Q$);
--   4. ($\ell_2$, Theorem 4) for all $x,x'\in\operatorname{relint}Q$:
--   $$\big(\nabla\tilde\varphi(x)-\nabla\tilde\varphi(x')\big)^{\top}(x-x')\ge\sum_{\sigma\in\Sigma}(x_\sigma-x'_\sigma)^2;$$
--   5. ($\ell_1$, Theorem 5) for all $x,x'\in\operatorname{relint}Q$:
--   $$\big(\nabla\tilde\varphi(x)-\nabla\tilde\varphi(x')\big)^{\top}(x-x')\ge\frac1{M_Q}\Big(\sum_{\sigma\in\Sigma}|x_\sigma-x'_\sigma|\Big)^2;$$
--   6. (range, Theorem 6 corrected) for all $x,x'\in Q$:
--   $$\tilde\varphi(x)-\tilde\varphi(x')\le M_Q^2\max_{j\in J}\log|A_j| ,$$
--   that is, $\max_Q\tilde\varphi-\min_Q\tilde\varphi\le M_Q^2\max_{j}\log|A_j|$.
--
--   Here $M_Q=\max_{x\in Q}\|x\|_1$. Plugged into the convergence bounds of EGT and mirror prox, the range bound improves the previous best (the Kroer et al. dilated entropy) by a factor $2^{\mathfrak D_Q+2}$, where $\mathfrak D_Q$ is the depth of the tree.
--
--   **Formalization Note** $\nabla\tilde\varphi(x)^\top v$ is the Fréchet derivative of the formula of Definition 4; $\ell_1$ and $\ell_2$ norms are explicit sums; the relative interior is `intrinsicInterior ℝ`.
--
--   Differences from the source:
--   - correction: the φ̃-diameter Ω_{φ̃,Q} = max_{x,x′} D_φ̃(x‖x′) is at most M_Q² max_j log|A_j| → φ̃(x) − φ̃(x′) ≤ M_Q² · maxLogActions for all x, x′ ∈ Q (max_Q φ̃ − min_Q φ̃); reason: the printed Ω is +∞: with one decision point and two actions (Q = {(1,t,1−t)}, γ_j = 1, w ≡ 1, M_Q = 2, bound 4 log 2), x = (1,1,0) and x′ = (1,ε,1−ε) ∈ relint Q give D_φ̃(x‖x′) = −log ε → ∞; the proof bounds max_Q φ̃ − min_Q φ̃, the quantity EGT and mirror prox use
--   - reading: φ̃ is a DGF for Q (Definition 1: continuous on Q, differentiable on relint Q, strongly convex on relint Q; common assumption min_Q d = 0; Definition 4 codomain ℝ≥0) → ContinuousOn (dge P) Q ∧ DifferentiableAt ℝ (dge P) x for x ∈ relint Q ∧ (0 ≤ dge P on Q ∧ ∃ x ∈ Q, dge P x = 0), with strong convexity given by the ℓ2 clause; reason: Definition 1 lists these properties and the proof of Theorem 4 verifies the minimum 0; compactness and convexity of Q are Definition 1's precondition on the domain, not a property of φ̃, and hold because Q is a polytope
--   - encoding: ∇φ̃ of φ̃ : Q → ℝ≥0, with the closed form (1 + log x_σ) w_σ + Σ_{j∈C_σ} γ_j log|A_j| on relint Q (p.11) → dge P defined by the formula of Definition 4 on all of ℝ^Σ (Real.log, 0·log 0 = 0); ∇φ̃(x)ᵀv = fderiv ℝ (dge P) x v; reason: the paper differentiates the formula of Definition 4; x − x′ is tangent to Q, so the inner product does not depend on the extension
--   - encoding: max_{j′∈J} log|A_{j′}| → maxLogActions P = log (max_j |A_j|), which is 0 for J = ∅; reason: log is increasing on [1,∞) and |A_j| ≥ 1, so the two agree for J ≠ ∅; for J = ∅ the paper's maximum is empty, Q = {e_∅} and both sides of the bound are 0
--   - encoding: M_Q := max_{x∈Q} ‖x‖₁ (p.4) → MQ P := sSup ((fun x => ∑ σ, |x σ|) '' Q); reason: Q is nonempty and compact, so the supremum is the maximum
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Theorems 4 and 5, p.12; Theorem 6, p.13

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_dge
import Definitions.Def_DilatableEntropy_MQ
import Definitions.Def_DilatableEntropy_maxLogActions

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Theorems 4 and 5 (p.12) and Theorem 6 (p.13, corrected). For every sequential decision
problem, the dilatable global entropy `φ̃` (Definition 4) on the sequence-form polytope `Q`:
1. is continuous on `Q`;
2. is differentiable at every point of `relint Q`;
3. satisfies `φ̃ ≥ 0` on `Q` and `min_{x ∈ Q} φ̃(x) = 0` (so with 4 it is a DGF for `Q`,
   Definition 1, p.4);
4. is `1`-strongly convex on `relint Q` w.r.t. the `ℓ2` norm:
   `(∇φ̃(x) − ∇φ̃(x'))ᵀ(x − x') ≥ ‖x − x'‖₂²` (Theorem 4);
5. is `1/M_Q`-strongly convex on `relint Q` w.r.t. the `ℓ1` norm:
   `(∇φ̃(x) − ∇φ̃(x'))ᵀ(x − x') ≥ (1/M_Q) ‖x − x'‖₁²` (Theorem 5);
6. has range `max_Q φ̃ − min_Q φ̃ ≤ M_Q² max_{j ∈ J} log |A_j|`:
   `φ̃(x) − φ̃(x') ≤ M_Q² max_j log |A_j|` for all `x, x' ∈ Q` (Theorem 6, corrected).

**Formalization Note** Theorem 6 as printed bounds the `φ̃`-diameter
`Ω = max_{x,x'} D_φ̃(x ‖ x')` (p.4), which is `+∞`: with one decision point and two actions,
`x = (1, 1, 0)` and `x' = (1, ε, 1 − ε)` give `D_φ̃(x ‖ x') = −log ε`. Its proof bounds
`max_Q φ̃ − min_Q φ̃`, which is what is stated. `φ̃` is the formula of Definition 4 on all of
`ℝ^Σ` and `∇φ̃(x)ᵀv = fderiv ℝ (dge P) x v`; `ℓ1`/`ℓ2` norms are explicit sums; `M_Q` is
`MQ P`; `max_j log |A_j|` is `maxLogActions P`; relint is `intrinsicInterior ℝ`. -/
theorem dge_dgf_strongly_convex_range (P : SeqDecisionProblem) :
    ContinuousOn (dge P) (seqFormPolytope P) ∧
      (∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P), DifferentiableAt ℝ (dge P) x) ∧
      ((∀ x ∈ seqFormPolytope P, 0 ≤ dge P x) ∧ ∃ x ∈ seqFormPolytope P, dge P x = 0) ∧
      (∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P),
        ∀ x' ∈ intrinsicInterior ℝ (seqFormPolytope P),
          ∑ σ, (x σ - x' σ) ^ 2 ≤
            fderiv ℝ (dge P) x (x - x') - fderiv ℝ (dge P) x' (x - x')) ∧
      (∀ x ∈ intrinsicInterior ℝ (seqFormPolytope P),
        ∀ x' ∈ intrinsicInterior ℝ (seqFormPolytope P),
          1 / MQ P * (∑ σ, |x σ - x' σ|) ^ 2 ≤
            fderiv ℝ (dge P) x (x - x') - fderiv ℝ (dge P) x' (x - x')) ∧
      ∀ x ∈ seqFormPolytope P, ∀ x' ∈ seqFormPolytope P,
        dge P x - dge P x' ≤ MQ P ^ 2 * maxLogActions P := by sorry

end DilatableEntropy
