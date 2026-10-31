-- Prove2me | Theorems.Thm_CompInvestBayes_eq_EC_79
-- name    : CompInvestBayes.eq_EC_79
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:48.821289+00:00
-- url     : https://prove2.me/theorems/e7cda6d6-ef1d-4968-9b02-d93e27ecbd6f
-- title:
--   (EC.79) — the belief derivative $\partial H_1/\partial y_0$ for $S_1\in(\mu_L,\mu_H]$
-- statement:
--   Let the standing assumptions hold, $\sigma>0$, $S_1\in(\mu_L,\mu_H]$, $\eta=\eta(S_1)$, thresholds $0<\ell<h<1$, and $y_0\in(0,1)$. Then
--
--   1. $f_1'(y_0)=\frac{\eta+1}2\big(\frac{y_0}{1-y_0}\big)^{\frac{\eta-1}2}+\frac{\eta-1}2\big(\frac{y_0}{1-y_0}\big)^{\frac{\eta+1}2}>0$;
--   2. $f_2'(y_0)=-\frac{\eta-1}2\big(\frac{1-y_0}{y_0}\big)^{\frac{\eta+1}2}-\frac{\eta+1}2\big(\frac{1-y_0}{y_0}\big)^{\frac{\eta-1}2}<0$;
--   3. $\partial\varphi_{\ell^*}/\partial y_0=a(\ell,h)f_1'(y_0)+b(\ell,h)f_2'(y_0)$ and $\partial\varphi_{h^*}/\partial y_0=a(h,\ell)f_1'(y_0)+b(h,\ell)f_2'(y_0)$;
--   4. (EC.79)
--   $$
--   \frac{\partial H_1(S_1,y_0)}{\partial y_0}=-\frac{\xi_1(\ell)-\xi_2(\ell)}{\lambda}\frac{\partial\varphi_{\ell^*}}{\partial y_0}-\frac{\xi_1(h)-\xi_2(h)}{\lambda}\frac{\partial\varphi_{h^*}}{\partial y_0}+\frac{S_1-\mu_L}{\lambda}.
--   $$
--
--   This is Step A of the proof of Theorem 4: the derivative of the leader's profit in the waiting region, which the envelope argument evaluates at $y_0=c_2\lambda$.
--
--   Differences from the source:
--   - generalization: the thresholds ℓ*(S₁), h*(S₁) → any thresholds 0 < ℓ < h < 1; reason: (EC.79) and the formulas for f₁', f₂', ∂φ/∂y₀ are calculus identities in y₀ that hold for every such pair
--   - reading: ∂H₁(S₁, y₀)/∂y₀ → HasDerivAt (fun y => H1 … y) (RHS) y₀ for y₀ ∈ (0, 1); reason: the partial derivative in y₀ with S₁ fixed, asserted to exist
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), proof of Theorem 4, Step A, (EC.79), p.ec24 (PDF 56), with f₁', f₂' and ∂φ/∂y₀ from p.ec25 (PDF 57)

import Mathlib
import Definitions.Def_CompInvestBayes_closedForms

namespace CompInvestBayes

/-- **The belief derivative of `H₁`** (SSRN 3408260, proof of Theorem 4, Step A, (EC.79), p.ec24,
PDF 56, with `f₁'`, `f₂'` and `∂φ/∂y₀` from p.ec25, PDF 57). Let `S₁ ∈ (µ_L, µ_H]`, `η = η(S₁)`
(16), thresholds `0 < ℓ < h < 1`, and `y₀ ∈ (0, 1)`. Then
1. `f₁'(y₀) = (η+1)/2 (y₀/(1−y₀))^{(η−1)/2} + (η−1)/2 (y₀/(1−y₀))^{(η+1)/2} > 0`;
2. `f₂'(y₀) = −(η−1)/2 ((1−y₀)/y₀)^{(η+1)/2} − (η+1)/2 ((1−y₀)/y₀)^{(η−1)/2} < 0`;
3. `∂φ_{ℓ*}/∂y₀ = a(ℓ, h) f₁'(y₀) + b(ℓ, h) f₂'(y₀)` and `∂φ_{h*}/∂y₀ = a(h, ℓ) f₁'(y₀) + b(h, ℓ) f₂'(y₀)`;
4. (EC.79) `∂H₁(S₁, y₀)/∂y₀ = −(ξ₁(ℓ) − ξ₂(ℓ))/λ · ∂φ_{ℓ*}/∂y₀ − (ξ₁(h) − ξ₂(h))/λ · ∂φ_{h*}/∂y₀
   + (S₁ − µ_L)/λ`. -/
theorem eq_EC_79 (p : Params) (hp : p.Standing) {σ : ℝ} (hσ : 0 < σ) {S1 ℓ h y0 : ℝ}
    (hS1 : p.muL < S1) (hS1' : S1 ≤ p.muH) (hℓ : 0 < ℓ) (hℓh : ℓ < h) (hh : h < 1)
    (hy0 : y0 ∈ Set.Ioo (0 : ℝ) 1) :
    let η := eta p σ S1
    let f1' := (η + 1) / 2 * (y0 / (1 - y0)) ^ ((η - 1) / 2)
      + (η - 1) / 2 * (y0 / (1 - y0)) ^ ((η + 1) / 2)
    let f2' := -((η - 1) / 2) * ((1 - y0) / y0) ^ ((η + 1) / 2)
      - (η + 1) / 2 * ((1 - y0) / y0) ^ ((η - 1) / 2)
    let dphiL := aCoef η ℓ h * f1' + bCoef η ℓ h * f2'
    let dphiH := aCoef η h ℓ * f1' + bCoef η h ℓ * f2'
    (HasDerivAt (f1 η) f1' y0 ∧ 0 < f1') ∧
      (HasDerivAt (f2 η) f2' y0 ∧ f2' < 0) ∧
      HasDerivAt (fun y => phiL p σ S1 ℓ h y) dphiL y0 ∧
      HasDerivAt (fun y => phiH p σ S1 ℓ h y) dphiH y0 ∧
      HasDerivAt (fun y => H1 p σ S1 ℓ h y)
        (-((xi1 p S1 ℓ - xi2 p S1 ℓ) / p.lam) * dphiL
          - (xi1 p S1 h - xi2 p S1 h) / p.lam * dphiH + (S1 - p.muL) / p.lam) y0 := by sorry

end CompInvestBayes
