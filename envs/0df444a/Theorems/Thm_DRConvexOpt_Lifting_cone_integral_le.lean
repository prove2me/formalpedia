-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_cone_integral_le
-- name    : DRConvexOpt.Lifting.cone_integral_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:41.546376+00:00
-- url     : https://prove2.me/theorems/f5ce1fdf-25c7-4249-b1eb-9c991528dec4
-- title:
--   Proof of Theorem 5, p. 40 — for a convex cone K, φ ≼_K ψ almost surely implies E[φ] ≼_K E[ψ]
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\Omega$, let $\mathcal K \subseteq \mathbb R^M$ be a proper cone, and let $\varphi, \psi : \Omega \to \mathbb R^M$ be $\mu$-integrable. If $\varphi(\omega) \preccurlyeq_{\mathcal K} \psi(\omega)$ for $\mu$-almost every $\omega$, that is, $\psi(\omega) - \varphi(\omega) \in \mathcal K$ almost surely, then
--   $$
--   \mathbb E_\mu[\varphi] \preccurlyeq_{\mathcal K} \mathbb E_\mu[\psi], \qquad\text{i.e.}\qquad \mathbb E_\mu[\psi] - \mathbb E_\mu[\varphi] \in \mathcal K.
--   $$
--
--   This conic form of monotonicity of the expectation is the step of the Lifting Theorem's proof that turns the almost-sure constraint $g(\tilde z) \preccurlyeq_{\mathcal K} \tilde u$ into the bound $\mathbb E[g(\tilde z)] \preccurlyeq_{\mathcal K} \mathbb E[\tilde u]$.
--
--   **Formalization Note** The paper says "since $\mathcal K$ is a convex cone"; the statement assumes the full proper-cone hypothesis of the paper, of which only closedness and convexity are relevant.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 40, proof of Theorem 5, "Since K is a convex cone, g(z̃) ≼_K ũ P-a.s. implies that E_P[g(z̃)] ≼_K E_P[ũ]"

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Proof of Theorem 5, p. 40: since K is a convex cone, φ ≼_K ψ almost surely implies
E[φ] ≼_K E[ψ] (for a probability measure and integrable φ, ψ). -/
theorem cone_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {nM : ℕ} (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (φ ψ : Ω → (Fin nM → ℝ)) (hφ : Integrable φ μ) (hψ : Integrable ψ μ)
    (h : ∀ᵐ ω ∂μ, ψ ω - φ ω ∈ K) :
    ∫ ω, ψ ω ∂μ - ∫ ω, φ ω ∂μ ∈ K := by sorry

end DRConvexOpt.Lifting
