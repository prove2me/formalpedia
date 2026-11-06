-- Prove2me | Theorems.Thm_FTPLLinBandit_corollary_11
-- name    : FTPLLinBandit.corollary_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:26.677683+00:00
-- url     : https://prove2.me/theorems/b555585b-9a84-4574-87c0-7ce600ff6883
-- title:
--   Corollary 11 — elliptical: $\|\hat\theta_t\|_2\le\sqrt\lambda/8\Rightarrow B_t\lesssim\sqrt{\log(dRGT)}\sqrt{\hat\theta_t^\top M_t\hat\theta_t}\sqrt{\hat\theta_t^\top\Sigma_t^{-1}\hat\theta_t}+T^{-1}$
-- statement:
--   There is a universal constant $c>0$ with the following property. Assume Assumption 1 (any $d\ge1$, $A$, $\nu$, $r$, $R$), let $x$ be an argmax selection, $f$ any radial profile of Table 4, $\lambda>0$, $T\ge1$ the horizon and $G$ a deterministic bound. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be any past estimates, $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$, $\rho_t=P_{\Sigma_t}$, $\rho_{t+1}=P_{\Sigma_t+\hat\theta\hat\theta^\top}$, $\Theta\in\mathbb R^d$, and let the current estimate satisfy $\|\hat\theta\|_2\le G$ and $\|\hat\theta\|_2\le\sqrt\lambda/8$. Then, with $M_t$ the action covariance under $\rho_t$ at $\Theta$,
--   $$B_t=\Psi_{t+1}(\Theta+\hat\theta)-\Psi_t(\Theta+\hat\theta)\le c\Big(\sqrt{\log(dRGT)}\,\sqrt{\hat\theta^\top M_t\hat\theta}\,\sqrt{\hat\theta^\top\Sigma_t^{-1}\hat\theta}+\frac1T\Big).$$
--
--   **Formalization Note** For $dRGT<1$ the Lean value of $\sqrt{\log(dRGT)}$ is $0$, so the statement then asserts $B_t\le c/T$.
--
--   Differences from the source:
--   - encoding: ≲ (f ≤ c g for a universal constant c > 0, p.3) → ∃ c > 0 chosen before every instance (d, A, ν, r, R, x, the law, λ, the past, Θ, θ̂); reason: the paper's definition of ≲
--   - generalization: ‖θ̂_t‖₂ ≤ … almost surely (for the run's estimates) → the bound assumed for the current vector θ̂ only, pathwise; the past list and Θ arbitrary; reason: the paper applies the corollary pathwise (Appendix F, p.33); the run's estimates satisfy the hypothesis on every path where the a.s. bound holds
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: G, undefined in the statement; √log(dRGT) → G any real with ‖θ̂‖ ≤ G (Appendix F, p.33: "let G be a deterministic upper bound on ‖θ̂_t‖₂"); Real.sqrt (Real.log (d·R·G·T)), which is 0 for dRGT < 1; reason: the paper's own fixing of G; for dRGT < 1 the elliptical term satisfies |B_t| ≲ R‖θ̂‖ ≤ RG < 1/T, so the reading keeps the statement true
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Corollary 11, p.13 (proof Appendix F, p.33)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Corollary 11 (`B_t` under elliptical perturbations).** Wei, arXiv:2610.17818, Corollary 11,
p.13: "Suppose λ is chosen such that ‖θ̂_t‖₂ ≤ √λ/8 almost surely. Then for every perturbation in
Table 4, it holds that B_t ≲ √(log(dRGT)) √(θ̂_tᵀM_tθ̂_t) √(θ̂_tᵀΣ_t⁻¹θ̂_t) + T⁻¹"; Appendix F,
p.33: "Throughout, let G be a deterministic upper bound on ‖θ̂_t‖₂".

There is a universal constant `c > 0` such that, under Assumption 1 (any `d ≥ 1`, `A`, `ν`, `r`,
`R`), for every argmax selection `x`, profile `f` of Table 4, `λ > 0`, horizon `T ≥ 1`,
deterministic bound `G`, past `θs`, `Θ` and current estimate `θ̂` with `‖θ̂‖ ≤ G` and
`‖θ̂‖ ≤ √λ/8`: with `Σ_t = shapeMat λ θs`, `ρ_t = P_{Σ_t}`, `ρ_{t+1} = P_{Σ_t + θ̂θ̂ᵀ}`,
`B_t = Ψ_{t+1}(Θ + θ̂) − Ψ_t(Θ + θ̂) ≤ c (√(log(dRGT)) √(θ̂ᵀM_tθ̂) √(θ̂ᵀΣ_t⁻¹θ̂) + 1/T)`.

**Formalization Note.** `c` is chosen before every instance. "Almost surely" is applied pathwise
to the current estimate; the past is arbitrary. `log` and `√` are `Real.log` and `Real.sqrt`:
for `dRGT < 1` the factor `√(log(dRGT))` is `0` in Lean, and the statement then asserts
`B_t ≤ c/T`. -/
theorem corollary_11 : ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ), IsNormalized A ν r R →
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
    ∀ (f : RadialProfile) (lam : ℝ), 0 < lam →
    ∀ (T : ℕ), 1 ≤ T → ∀ (G : ℝ),
    ∀ (t : ℕ) (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)),
      ‖θh‖ ≤ G → ‖θh‖ ≤ Real.sqrt lam / 8 →
      potential A (perturbDens (.elliptical f) lam
            (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d)) θs θh)) (Θ + θh) -
          potential A (perturbDens (.elliptical f) lam θs) (Θ + θh) ≤
        c * (Real.sqrt (Real.log (d * R * G * T)) *
            Real.sqrt (actCovQ x (perturbDens (.elliptical f) lam θs) Θ θh) *
            Real.sqrt (quadForm (shapeMat lam θs)⁻¹ θh) + 1 / (T : ℝ)) := by sorry

end FTPLLinBandit
