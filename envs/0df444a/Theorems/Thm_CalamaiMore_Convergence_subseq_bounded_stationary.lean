-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_subseq_bounded_stationary
-- name    : CalamaiMore.Convergence.subseq_bounded_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:33:37.683484+00:00
-- url     : https://prove2.me/theorems/4a875d2b-1fb2-4d79-8850-b8f1349903cf
-- title:
--   Theorem 2.4 — bounded subsequences and stationarity of limit points
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, let $f : E \to \mathbb R$ be continuously differentiable on $\Omega$, and let $(x_k, \alpha_k)$ be a run of the gradient projection method defined by (2.1) and (2.2), with constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$. If some subsequence $\{x_k : k \in K\}$ (with $K \subseteq \mathbb N$ infinite) is bounded, then
--
--   $$
--   \lim_{k \in K,\ k \to \infty} \frac{\|x_{k+1} - x_k\|}{\alpha_k} = 0.
--   $$
--
--   Moreover, any limit point of $\{x_k\}$ is a stationary point of $\min\{f(x) : x \in \Omega\}$.
--
--   Unlike Theorem 2.3, neither a lower bound on $f$ nor uniform continuity of $\nabla f$ is assumed; boundedness of one subsequence replaces them.
--
--   **Formalization Note** A limit point of $\{x_k\}$ is a cluster point of the sequence (`MapClusterPt x⋆ atTop x`), and the limit along $K$ is taken along the filter `atTop ⊓ 𝓟 K`.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 100, Theorem 2.4

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Theorem 2.4 (p. 100): if some subsequence `{x_k : k ∈ K}` is bounded, then
`‖x_{k+1} - x_k‖ / α_k → 0` along `K`; moreover every limit (cluster) point of `{x_k}` is a
stationary point. -/
theorem subseq_bounded_stationary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (K : Set ℕ) (hK : K.Infinite) (hKb : Bornology.IsBounded (x '' K)) :
    Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ / α k)
        (Filter.atTop ⊓ Filter.principal K) (nhds 0) ∧
    ∀ xstar : E, MapClusterPt xstar Filter.atTop x → CalamaiMore.Shared.IsStationaryPoint f Ω xstar := by sorry

end CalamaiMore.Convergence
