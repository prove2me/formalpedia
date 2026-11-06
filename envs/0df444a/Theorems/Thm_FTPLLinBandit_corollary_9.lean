-- Prove2me | Theorems.Thm_FTPLLinBandit_corollary_9
-- name    : FTPLLinBandit.corollary_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:21.990999+00:00
-- url     : https://prove2.me/theorems/5199698b-19c5-4f86-a810-7bcbbffc9c13
-- title:
--   Corollary 9 — elliptical: $\|\hat\theta_t\|_2\le\sqrt\lambda/8\Rightarrow A_t\lesssim\sqrt{\hat\theta_t^\top\Sigma_t^{-1}\hat\theta_t}\sqrt{\hat\theta_t^\top M_t\hat\theta_t}$
-- statement:
--   There is a universal constant $c>0$ with the following property. Assume Assumption 1 (any $d\ge1$, $A$, $\nu$, $r$, $R$), let $x$ be an argmax selection, $f$ any radial profile of Table 4 and $\lambda>0$. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be any past estimates, $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$, $\rho_t=P_{\Sigma_t}$, $\Theta\in\mathbb R^d$, and let $\|\hat\theta\|_2\le\sqrt\lambda/8$. Then, with $\mu_t$, $M_t$ the action mean and covariance under $\rho_t$ at $\Theta$,
--   $$A_t=\Psi_t(\Theta+\hat\theta)-\Psi_t(\Theta)-\langle\mu_t,\hat\theta\rangle\le c\,\sqrt{\hat\theta^\top\Sigma_t^{-1}\hat\theta}\,\sqrt{\hat\theta^\top M_t\hat\theta}.$$
--
--   Differences from the source:
--   - encoding: ≲ (f ≤ c g for a universal constant c > 0, p.3) → ∃ c > 0 chosen before every instance (d, A, ν, r, R, x, the law, λ, the past, Θ, θ̂); reason: the paper's definition of ≲
--   - generalization: ‖θ̂_t‖₂ ≤ … almost surely (for the run's estimates) → the bound assumed for the current vector θ̂ only, pathwise; the past list and Θ arbitrary; reason: the paper applies the corollary pathwise (Appendix F, p.33); the run's estimates satisfy the hypothesis on every path where the a.s. bound holds
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Corollary 9, p.12 (proof Appendix F, p.33)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Corollary 9 (`A_t` under elliptical perturbations).** Wei, arXiv:2610.17818, Corollary 9,
p.12: "Suppose λ is chosen such that ‖θ̂_t‖₂ ≤ √λ/8 almost surely. Then for every perturbation in
Table 4, it holds that A_t ≲ √(θ̂_tᵀΣ_t⁻¹θ̂_t) √(θ̂_tᵀM_tθ̂_t)".

There is a universal constant `c > 0` such that, under Assumption 1 (any `d ≥ 1`, `A`, `ν`, `r`,
`R`), for every argmax selection `x`, every profile `f` of Table 4, `λ > 0`, past `θs`, `Θ` and
current estimate `θ̂` with `‖θ̂‖ ≤ √λ/8`: with `Σ_t = shapeMat λ θs` and `ρ_t = P_{Σ_t}`,
`A_t = Ψ_t(Θ + θ̂) − Ψ_t(Θ) − ⟨µ_t, θ̂⟩ ≤ c √(θ̂ᵀΣ_t⁻¹θ̂) √(θ̂ᵀM_tθ̂)`.

**Formalization Note.** `c` is chosen before every instance (`≲`, §2, p.3). "Almost surely" is
applied pathwise to the current estimate; the past is arbitrary. -/
theorem corollary_9 : ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ), IsNormalized A ν r R →
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
    ∀ (f : RadialProfile) (lam : ℝ), 0 < lam →
    ∀ (t : ℕ) (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)),
      ‖θh‖ ≤ Real.sqrt lam / 8 →
      potential A (perturbDens (.elliptical f) lam θs) (Θ + θh) -
          potential A (perturbDens (.elliptical f) lam θs) Θ -
          ⟪actMean x (perturbDens (.elliptical f) lam θs) Θ, θh⟫_ℝ ≤
        c * Real.sqrt (quadForm (shapeMat lam θs)⁻¹ θh) *
          Real.sqrt (actCovQ x (perturbDens (.elliptical f) lam θs) Θ θh) := by sorry

end FTPLLinBandit
