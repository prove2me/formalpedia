-- Prove2me | Theorems.Thm_CertDRO_SGD_summed_bound
-- name    : CertDRO.SGD.summed_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:46.045171+00:00
-- url     : https://prove2.me/theorems/6005a049-6497-47e9-ad7d-c35ab26146e4
-- title:
--   §B.3 — the averaged bound (1/T)Σ E‖∇F(θᵗ)‖² ≤ 2ε̂ + 2Δ_F/(αT) + 2L_φασ² for any α ≤ 1/L_φ
-- statement:
--   Assume the hypotheses of Theorem 2, except that the constant stepsize $\alpha$ is arbitrary with $\alpha>0$ and $L_\varphi\alpha\le1$: the standing hypotheses ($Z$ nonempty, convex, closed; Assumptions A and B for the Euclidean norm; $\gamma>L_{zz}$); a probability measure $P_0$ with $P_0(Z)=1$ such that every $\varphi_\gamma(\theta;\cdot)$ is integrable; $F(\theta)=\mathbb E_{P_0}[\varphi_\gamma(\theta;Z)]$ bounded below; $\Delta_F\ge F(\theta^0)-\inf_\theta F(\theta)$; the variance bound $\mathbb E_{P_0}\|\nabla F(\theta)-\nabla_\theta\varphi_\gamma(\theta;Z)\|_2^2\le\sigma^2$ for all $\theta$, with $\sigma>0$; a jointly measurable $\epsilon$-approximate maximization oracle, $\epsilon\ge0$; and $T\ge1$. Let $\theta^0,\dots,\theta^{T-1}$ be the iterates of Algorithm 1 driven by i.i.d. samples $z^0,\dots,z^{T-1}\sim P_0$. Then
--   $$\frac1T\sum_{t=0}^{T-1}\mathbb E\big[\|\nabla F(\theta^t)\|_2^2\big]\le2\hat\epsilon+\frac{2\Delta_F}{\alpha T}+2L_\varphi\alpha\sigma^2,\qquad\hat\epsilon=\frac{2L_{\theta z}^2}{\gamma-L_{zz}}\epsilon .$$
--
--   Theorem 2 is this bound at the stepsize $\alpha=\sqrt{\Delta_F/(L_\varphi T\sigma^2)}$, which balances the last two terms.
--
--   **Formalization Note** The paper prints the bound with $2\hat\epsilon$ subtracted on the left; it is moved to the right, which is equivalent since all terms are finite. The expectations are lower Lebesgue integrals in $[0,\infty]$ over the product measure $P_0^{\otimes T}$, so a non-integrable $\|\nabla F(\theta^t)\|^2$ is not read as $0$. The infimum is a real infimum, made meaningful by the hypothesis that $F$ is bounded below.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 41, §B.3, last display

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

open MeasureTheory

/-- §B.3, last display of p. 41: under the hypotheses of Theorem 2 but with an arbitrary constant
stepsize `0 < α ≤ 1/L_φ`, the iterates `θ⁰, …, θ^{T−1}` of Algorithm 1, driven by i.i.d. samples
`z⁰, …, z^{T−1} ∼ P₀`, satisfy
`(1/T) Σ_{t<T} E‖∇F(θ^t)‖² ≤ 2 ε̂ + 2Δ_F/(αT) + 2 L_φ α σ²`, with `ε̂ = 2 Lθz² ε / (γ − Lzz)`. -/
theorem summed_bound {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀] (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (ε : ℝ) (hε : 0 ≤ ε) (zhat : Param d → Data m → Data m)
    (hzhat : IsOracle Z ℓ c γ ε zhat) (hzhat_meas : Measurable (Function.uncurry zhat))
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
        gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ‖ ^ 2) ∂P₀ ≤ ENNReal.ofReal (σ ^ 2))
    (θ₀ : Param d) (ΔF : ℝ) (hbdd : BddBelow (Set.range (robustObjective Z ℓ c γ P₀)))
    (hΔF : robustObjective Z ℓ c γ P₀ θ₀ - ⨅ θ, robustObjective Z ℓ c γ P₀ θ ≤ ΔF)
    (T : ℕ) (hT : 0 < T)
    (α : ℝ) (hα : 0 < α) (hαL : Lphi Lθθ Lzz Lθz Lzθ γ * α ≤ 1) :
    (T : ENNReal)⁻¹ * ∑ t ∈ Finset.range T,
        ∫⁻ ω, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) (run gθ zhat α θ₀ ω t)‖ ^ 2)
          ∂(Measure.pi fun _ : Fin T => P₀) ≤
      ENNReal.ofReal (2 * (2 * Lθz ^ 2 / (γ - Lzz) * ε) + 2 * ΔF / (α * T)
        + 2 * Lphi Lθθ Lzz Lθz Lzθ γ * α * σ ^ 2) := by sorry

end CertDRO.SGD
