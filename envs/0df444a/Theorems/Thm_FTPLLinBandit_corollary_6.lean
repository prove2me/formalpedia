-- Prove2me | Theorems.Thm_FTPLLinBandit_corollary_6
-- name    : FTPLLinBandit.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:30.392854+00:00
-- url     : https://prove2.me/theorems/0ac2d0d9-d033-44d9-a8f2-b865c21c51d4
-- title:
--   Corollary 6 — random weighting: $\|\hat\theta_t\|_2\le\sqrt\lambda/8\Rightarrow A_t\lesssim\sqrt{\hat\theta_t^\top M_t\hat\theta_t}\sqrt{\hat\theta_t^\top\Sigma_t^{-1}\hat\theta_t}$
-- statement:
--   There is a universal constant $c>0$ with the following property. Assume Assumption 1 (any $d\ge1$, $A$, $\nu$, $r$, $R$), let $x$ be an argmax selection, $\rho_1=P_{\lambda I}$ any initializer of Table 2 with $\lambda>0$ and $\varphi$ any scalar law of Table 3. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be any past estimates, $\rho_t$ the random-weighting density and $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$, $\Theta\in\mathbb R^d$, and let $\hat\theta$ satisfy $\|\hat\theta\|_2\le\sqrt\lambda/8$. Then, with $\mu_t$, $M_t$ the action mean and covariance under $\rho_t$ at $\Theta$,
--   $$A_t=\Psi_t(\Theta+\hat\theta)-\Psi_t(\Theta)-\langle\mu_t,\hat\theta\rangle\le c\,\sqrt{\hat\theta^\top M_t\hat\theta}\,\sqrt{\hat\theta^\top\Sigma_t^{-1}\hat\theta}.$$
--
--   This is the stability bound for $A_t$ that, summed over rounds with the elliptical potential lemma, gives the $\tilde O(d\sqrt T)$ stability contribution in the proof of Theorem 13.
--
--   Differences from the source:
--   - encoding: ≲ (f ≤ c g for a universal constant c > 0, p.3) → ∃ c > 0 chosen before every instance (d, A, ν, r, R, x, the law, λ, the past, Θ, θ̂); reason: the paper's definition of ≲
--   - generalization: ‖θ̂_t‖₂ ≤ … almost surely (for the run's estimates) → the bound assumed for the current vector θ̂ only, pathwise; the past list and Θ arbitrary; reason: the paper applies the corollary pathwise (Appendix F, p.33); the run's estimates satisfy the hypothesis on every path where the a.s. bound holds
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Corollary 6, p.11 (proof Appendix F, p.33)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Corollary 6 (`A_t` under random weighting).** Wei, arXiv:2610.17818, Corollary 6, p.11:
"Suppose λ is chosen such that ‖θ̂_t‖₂ ≤ √λ/8 almost surely. Then for every combination of ρ₁ in
Table 2 and φ in Table 3, it holds that A_t ≲ √(θ̂_tᵀM_tθ̂_t) √(θ̂_tᵀΣ_t⁻¹θ̂_t)."

There is a universal constant `c > 0` such that, under Assumption 1 (any `d ≥ 1`, `A`, `ν`, `r`,
`R`), for every argmax selection `x`, every profile `f` of Table 2 and scalar law `φ` of Table 3,
every `λ > 0`, every past `θs` (the paper's `θ̂_1, …, θ̂_{t−1}`), every `Θ` (the paper's `Θ̂_t`)
and every `θ̂` with `‖θ̂‖ ≤ √λ/8`:
`A_t = Ψ_t(Θ + θ̂) − Ψ_t(Θ) − ⟨µ_t, θ̂⟩ ≤ c √(θ̂ᵀM_tθ̂) √(θ̂ᵀΣ_t⁻¹θ̂)`, with
`ρ_t = perturbDens (randomWeighting f φ) λ θs = rwDens ρ₁ φ θs`, `ρ₁ = P_{λI}`,
`Σ_t = shapeMat λ θs`.

**Formalization Note.** `≲` is "≤ a universal constant times" (§2, p.3), so `c` is chosen before
every instance. "Almost surely" is applied pathwise: the bound holds for every current estimate
with `‖θ̂‖ ≤ √λ/8`, whatever the past and `Θ`. -/
theorem corollary_6 : ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ), IsNormalized A ν r R →
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
    ∀ (f : RadialProfile) (φ : ScalarLaw) (lam : ℝ), 0 < lam →
    ∀ (t : ℕ) (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)),
      ‖θh‖ ≤ Real.sqrt lam / 8 →
      potential A (perturbDens (.randomWeighting f φ) lam θs) (Θ + θh) -
          potential A (perturbDens (.randomWeighting f φ) lam θs) Θ -
          ⟪actMean x (perturbDens (.randomWeighting f φ) lam θs) Θ, θh⟫_ℝ ≤
        c * Real.sqrt (actCovQ x (perturbDens (.randomWeighting f φ) lam θs) Θ θh) *
          Real.sqrt (quadForm (shapeMat lam θs)⁻¹ θh) := by sorry

end FTPLLinBandit
