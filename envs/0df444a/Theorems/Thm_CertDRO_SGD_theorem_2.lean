-- Prove2me | Theorems.Thm_CertDRO_SGD_theorem_2
-- name    : CertDRO.SGD.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:19:41.542349+00:00
-- url     : https://prove2.me/theorems/4b511002-8868-4145-9d1e-f15cf3973e11
-- title:
--   Theorem 2 — nonconvex SGD on the robust surrogate: (1/T)Σ E‖∇F(θᵗ)‖² − 4L_θz²ε/(γ − L_zz) ≤ 4σ√(L_φΔ_F/T)
-- statement:
--   Let $Z\subseteq\mathbb R^m$ be nonempty, convex and closed; let the cost $c$ satisfy Assumption A and the loss $\ell:\mathbb R^d\times\mathbb R^m\to\mathbb R$ satisfy Assumption B, both with the Euclidean norm, and let $\Theta=\mathbb R^d$. Let $\gamma>L_{zz}$ and
--   $$\varphi_\gamma(\theta;z_0)=\sup_{z\in Z}\{\ell(\theta;z)-\gamma c(z,z_0)\},\qquad F(\theta)=\mathbb E_{P_0}[\varphi_\gamma(\theta;Z)],\qquad L_\varphi=L_{\theta\theta}+\frac{L_{\theta z}L_{z\theta}}{\gamma-L_{zz}},$$
--   where $P_0$ is a probability distribution with $P_0(Z)=1$ and each $\varphi_\gamma(\theta;\cdot)$ is $P_0$-integrable. Suppose:
--
--   1. $F$ is bounded below and $\Delta_F>0$ satisfies $\Delta_F\ge F(\theta^0)-\inf_\theta F(\theta)$;
--   2. $\sigma>0$ and $\mathbb E_{P_0}\|\nabla F(\theta)-\nabla_\theta\varphi_\gamma(\theta;Z)\|_2^2\le\sigma^2$ for every $\theta$;
--   3. $\epsilon\ge0$ and the inner maximization is solved by a jointly measurable $\epsilon$-approximate oracle $\hat z(\theta,z_0)\in Z$;
--   4. $T\ge1$ and $T\ge L_\varphi\Delta_F/\sigma^2$.
--
--   Run Algorithm 1 from $\theta^0$ for $T$ steps with i.i.d. samples $z^t\sim P_0$ and constant stepsize $\alpha=\sqrt{\Delta_F/(L_\varphi T\sigma^2)}$, i.e. $\theta^{t+1}=\theta^t-\alpha\nabla_\theta\ell(\theta^t;\hat z(\theta^t,z^t))$. Then
--   $$\frac1T\sum_{t=0}^{T-1}\mathbb E\big[\|\nabla F(\theta^t)\|_2^2\big]-\frac{4L_{\theta z}^2}{\gamma-L_{zz}}\epsilon\le4\sigma\sqrt{\frac{L_\varphi\Delta_F}{T}} .$$
--
--   This is the paper's computational guarantee: stochastic gradient descent with an approximate adversary reaches an approximate stationary point of the Wasserstein penalty objective at the rate $T^{-1/2}$ of smooth nonconvex optimization, up to an additive bias proportional to the accuracy $\epsilon$ of the inner maximization.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$ with the $\epsilon$-term moved to the right-hand side, which is equivalent because all terms are finite and nonnegative; the expectations are lower Lebesgue integrals over $P_0^{\otimes T}$, so a non-integrable integrand is never read as $0$. Hypotheses implicit in the paper and made explicit: $\gamma>L_{zz}$ (the paper writes $\gamma\ge L_{zz}$ but divides by $\gamma-L_{zz}$), $Z$ convex and closed, $\sigma>0$ and $\Delta_F>0$ (needed for a positive stepsize), $T\ge1$, $\epsilon\ge0$, $F$ bounded below, integrability of $\varphi_\gamma(\theta;\cdot)$, and measurability of the oracle. The cost is not assumed differentiable.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 6, Theorem 2 (proof in §B.3, pp. 40–41)

import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.SGD

open MeasureTheory

/-- Theorem 2 (Convergence of Nonconvex SGD), p. 6. Let Assumptions A and B hold with the ℓ²-norm,
`Θ = ℝ^d`, `γ > Lzz`, and let `F(θ) = E_{P₀}[φ_γ(θ; Z)]`. Let `Δ_F ≥ F(θ⁰) − inf_θ F(θ)`, assume
`E‖∇F(θ) − ∇_θ φ_γ(θ, Z)‖² ≤ σ²` for all `θ`, and run Algorithm 1 with an `ε`-approximate maximization
oracle and constant stepsize `α = √(Δ_F / (L_φ T σ²))`, `L_φ = Lθθ + Lθz Lzθ / (γ − Lzz)`. If
`T ≥ L_φ Δ_F / σ²`, then
`(1/T) Σ_{t=0}^{T−1} E‖∇F(θ^t)‖² − (4 Lθz² / (γ − Lzz)) ε ≤ 4σ √(L_φ Δ_F / T)`
(stated with the `ε`-term moved to the right-hand side, in `ℝ≥0∞`). -/
theorem theorem_2 {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
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
    (θ₀ : Param d) (ΔF : ℝ) (hΔF_pos : 0 < ΔF)
    (hbdd : BddBelow (Set.range (robustObjective Z ℓ c γ P₀)))
    (hΔF : robustObjective Z ℓ c γ P₀ θ₀ - ⨅ θ, robustObjective Z ℓ c γ P₀ θ ≤ ΔF)
    (T : ℕ) (hT : 0 < T) (hTL : Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / σ ^ 2 ≤ T) :
    (T : ENNReal)⁻¹ * ∑ t ∈ Finset.range T,
        ∫⁻ ω, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀)
            (run gθ zhat (Real.sqrt (ΔF / (Lphi Lθθ Lzz Lθz Lzθ γ * T * σ ^ 2))) θ₀ ω t)‖ ^ 2)
          ∂(Measure.pi fun _ : Fin T => P₀) ≤
      ENNReal.ofReal (4 * Lθz ^ 2 / (γ - Lzz) * ε
        + 4 * σ * Real.sqrt (Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / T)) := by sorry

end CertDRO.SGD
