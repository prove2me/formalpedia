-- Prove2me | Theorems.Thm_DynPricingCov_eq_26
-- name    : DynPricingCov.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:39.988554+00:00
-- url     : https://prove2.me/theorems/6f118bb4-c6c2-4a65-b06f-ea3a47b28b89
-- title:
--   (26) and the single-period regret bound $2\bar g\bar p\bar\gamma\|z_t\|_{M_{t-1}^{-1}}$ (corrected: $0\le\underline p$)
-- statement:
--   Fix a period $t$ with covariate $x_t\in\mathcal X$, under Assumptions 1 and 2 with nonnegative prices, $0\le\underline p$. Let $\hat\theta\in\Theta$, let $M$ be positive definite, and let $\Theta_t=\{\theta\in\Theta:\|\theta-\hat\theta\|_M\le\bar\gamma\}$ with $\bar\gamma=2\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log T+2d\log\frac{2d+T}{2d}}$. Let $\theta_t=(\alpha_t,\beta_t)$ maximize $r^*(x_t^\top\alpha,x_t^\top\beta)$ over $\Theta_t$, and let $p_t$ maximize $r(\cdot\,;x_t^\top\alpha_t,x_t^\top\beta_t)$ over $[\underline p,\bar p]$. If $\theta^*\in\Theta_t$, then
--
--   $$
--   r^*(x_t^\top\alpha_t,x_t^\top\beta_t)\ \ge\ r^*(x_t^\top\alpha^*,x_t^\top\beta^*)\qquad(26)
--   $$
--
--   and the single-period regret satisfies
--
--   $$
--   r^*(x_t^\top\alpha^*,x_t^\top\beta^*)-r(p_t;x_t^\top\alpha^*,x_t^\top\beta^*)\ \le\ 2\bar g\,\bar p\,\bar\gamma\,\|z_t\|_{M^{-1}},
--   $$
--
--   where $z_t=(x_t,p_tx_t)$. In Algorithm 1 with $\lambda=1$, $\hat\theta=\hat\theta_{t-1}$ and $M=M_{t-1}$; summing these bounds over $t$ on the good event gives the main term of Theorem 1.
--
--   Differences from the source:
--   - correction: Assumption 1(b): prices in a range [p̲, p̄], p̲ any real → 0 ≤ p̲; reason: the printed statement is false for negative prices: d = T = 1, 𝒳 = {1/√101}, p̲ = −10, p̄ = 1, g(u) = u (g̲ = ḡ = 1), θ̄ = 1, D̄ = 1, σ̄ = 0.01, ε ≡ 0, θ* = −θ₁ with θ₁ = (−10, 100)/√10100 satisfies Assumptions 1–3, Algorithm 1 picks θ₁ and p₁ = −10, and the regret is 10.0 > 6.14 = the Theorem 1 bound (and > 4.04 = 2ḡp̄γ̄‖z₁‖ of the single-period display); the proof's step ≤ ḡp̄|zₜᵀ(θₜ − θ*)| needs |pₜ| ≤ p̄; every price range in the paper is nonnegative
--   - generalization: θ̂ₜ₋₁ and Mₜ₋₁ of Algorithm 1 with λ = 1, under the event E = {θ* ∈ Θ_s for s = 1..T} → any θ̂ ∈ Θ, any positive definite M, and only θ* ∈ Θₜ for this t; reason: the display uses only these properties; Algorithm 1's θ̂ₜ₋₁ ∈ Θ and Mₜ₋₁ ≻ 0, and E implies θ* ∈ Θₜ, so the source's display is an instance
--   - generalization: θ̂ₜ, (αₜ, βₜ), pₜ := arg max → any maximizers (maximality predicates), any tie-breaking; reason: every tie-breaking rule the source may intend is an instance
--   - generalization: Assumption 2: g has a bounded derivative over its domain, with g̲ ≤ g′ ≤ ḡ on Z → g : ℝ → ℝ strictly increasing and differentiable on ℝ, g̲ ≤ g′ ≤ ḡ on Z only; reason: the "Specifically" clause pins the bounds to Z and the proof uses g′ only on Z; the paper uses g on all of ℝ (h(u) = g′(g⁻¹(u)) for u ∈ ℝ, p.5), so every g of the source satisfies the Lean hypothesis
--   - encoding: θ = (α, β) ∈ ℝ^{2d}, r* as a max, dimension and horizon → Fin (d + d) → ℝ with Fin.append; r* as sSup over [p̲, p̄] (attained); 1 ≤ d, 1 ≤ T; σ̄ > 0; reason: Lean conventions; the source's d, T, σ̄ are positive
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, proof of Theorem 1, (26) and the display "the single period regret can be bounded by", p.28

import Mathlib
import Definitions.Def_DynPricingCov_Model
import Definitions.Def_DynPricingCov_UCBPricing

open Matrix

namespace DynPricingCov

/-- **(26) and the single-period regret bound**, proof of Theorem 1, Wang, Talluri & Li, On Dynamic
Pricing with Covariates, arXiv:2112.13254v3, p.28: at time `t`, under the event
`θ* ∈ Θ_t`, the choice of `θ_t = (α_t, β_t)` in Algorithm 1 ensures
`r*(x_tᵀα_t, x_tᵀβ_t) ≥ r*(x_tᵀα*, x_tᵀβ*)` (26), and the single-period regret satisfies
`r*(x_tᵀα*, x_tᵀβ*) − r(p_t; x_tᵀα*, x_tᵀβ*) ≤ 2 ḡ p̄ γ̄ ‖z_t‖_{M_{t−1}⁻¹}`.

**Formalization Note** One period, deterministic: `θh` plays `θ̂_{t−1} ∈ Θ`, `M` plays `M_{t−1}`
and may be any positive definite matrix; the confidence set has the `λ = 1` radius `γ̄`;
`θt` maximizes `r*` over it and `pt` maximizes `r(·; x_tᵀα_t, x_tᵀβ_t)` over `[p̲, p̄]`.
Prices are nonnegative, `0 ≤ p̲` (a correction of the printed statement). -/
theorem eq_26 {d T : ℕ} (hd : 1 ≤ d) (hT : 1 ≤ T)
    {X : Set (Fin d → ℝ)} {xt : Fin d → ℝ} (hxt : xt ∈ X)
    {θbar plo phi Dbar glo ghi σbar : ℝ} {g : ℝ → ℝ} {θstar : Fin (d + d) → ℝ}
    (h1 : Assumption1 X θbar plo phi Dbar g θstar) (h2 : Assumption2 X θbar plo phi glo ghi g)
    (hplo : 0 ≤ plo) (hσ : 0 < σbar)
    {θh : Fin (d + d) → ℝ} (hθh : θh ∈ Theta d θbar)
    {M : Matrix (Fin (d + d)) (Fin (d + d)) ℝ} (hM : M.PosDef)
    {θt : Fin (d + d) → ℝ} (hθt : θt ∈ confSet d θbar θh M (gammaBar d T θbar σbar glo))
    (hθt_max : ∀ θ ∈ confSet d θbar θh M (gammaBar d T θbar σbar glo),
      rstar g plo phi (xt ⬝ᵥ alphaOf θ) (xt ⬝ᵥ betaOf θ) ≤
        rstar g plo phi (xt ⬝ᵥ alphaOf θt) (xt ⬝ᵥ betaOf θt))
    {pt : ℝ} (hpt : pt ∈ Set.Icc plo phi)
    (hpt_max : ∀ q ∈ Set.Icc plo phi,
      r g q (xt ⬝ᵥ alphaOf θt) (xt ⬝ᵥ betaOf θt) ≤ r g pt (xt ⬝ᵥ alphaOf θt) (xt ⬝ᵥ betaOf θt))
    (hgood : θstar ∈ confSet d θbar θh M (gammaBar d T θbar σbar glo)) :
    rstar g plo phi (xt ⬝ᵥ alphaOf θstar) (xt ⬝ᵥ betaOf θstar) ≤
        rstar g plo phi (xt ⬝ᵥ alphaOf θt) (xt ⬝ᵥ betaOf θt) ∧
      rstar g plo phi (xt ⬝ᵥ alphaOf θstar) (xt ⬝ᵥ betaOf θstar) -
          r g pt (xt ⬝ᵥ alphaOf θstar) (xt ⬝ᵥ betaOf θstar) ≤
        2 * ghi * phi * gammaBar d T θbar σbar glo * mNorm M⁻¹ (z xt pt) := by sorry

end DynPricingCov
