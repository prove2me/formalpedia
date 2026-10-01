-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_projGrad_tendsto_zero_of_subseq_bounded
-- name    : CalamaiMore.Convergence.projGrad_tendsto_zero_of_subseq_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:34:58.595685+00:00
-- url     : https://prove2.me/theorems/98a66da6-2785-4bbe-86a1-d6d61a71fb44
-- title:
--   Theorem 3.4 — projected gradients vanish along a bounded subsequence
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, let $f : E \to \mathbb R$ be continuously differentiable on $\Omega$, and let $(x_k, \alpha_k)$ be a run of the gradient projection method defined by (2.1) and (2.2), with constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$, whose steps satisfy (3.2), $\alpha_k \le \gamma_3$ for some constant $\gamma_3$. If some subsequence $\{x_k : k \in K\}$ (with $K \subseteq \mathbb N$ infinite) is bounded, then
--
--   $$
--   \lim_{k \in K,\ k \to \infty} \|\nabla_\Omega f(x_{k+1})\| = 0.
--   $$
--
--   This variant of Theorem 3.2 replaces the lower bound on $f$ and the uniform continuity of $\nabla f$ by boundedness of one subsequence; note that the conclusion concerns the next iterates $x_{k+1}$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 104, Theorem 3.4

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Theorem 3.4 (p. 104): with bounded steps `α_k ≤ γ₃` (3.2), if some
subsequence `{x_k : k ∈ K}` is bounded then `‖∇_Ω f(x_{k+1})‖ → 0` along `K`. -/
theorem projGrad_tendsto_zero_of_subseq_bounded {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (γ₃ : ℝ) (hα₃ : ∀ k, α k ≤ γ₃)
    (K : Set ℕ) (hK : K.Infinite) (hKb : Bornology.IsBounded (x '' K)) :
    Filter.Tendsto (fun k => ‖projGrad f Ω (x (k + 1))‖)
        (Filter.atTop ⊓ Filter.principal K) (nhds 0) := by sorry

end CalamaiMore.Convergence
