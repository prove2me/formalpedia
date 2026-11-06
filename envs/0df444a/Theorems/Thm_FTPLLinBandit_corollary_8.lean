-- Prove2me | Theorems.Thm_FTPLLinBandit_corollary_8
-- name    : FTPLLinBandit.corollary_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:43.506903+00:00
-- url     : https://prove2.me/theorems/88707d71-bb39-4170-9296-2f574be67098
-- title:
--   Corollary 8 — random weighting with $\lambda\ge CG^2\log^2(RGT)$: $B_t\lesssim\sqrt{\hat\theta_t^\top M_t\hat\theta_t}\sqrt{\hat\theta_t^\top\Sigma_t^{-1}\hat\theta_t}+T^{-1}$
-- statement:
--   There are universal constants $C>0$ and $c>0$ with the following property. Assume Assumption 1 (any $d\ge1$, $A$, $\nu$, $r$, $R$), let $x$ be an argmax selection, $\rho_1=P_{\lambda I}$ any initializer of Table 2 with $\lambda>0$ and $\varphi$ any scalar law of Table 3, let $T\ge1$ be the horizon and $G$ a deterministic bound. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be any past estimates, $\Theta\in\mathbb R^d$, and let the current estimate satisfy $\|\hat\theta\|_2\le G$, and suppose
--   $$\lambda\ge C\,G^2\log^2(RGT).$$
--   Then, with $\rho_t,\rho_{t+1}$ the random-weighting densities before and after appending $\hat\theta$, $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$ and $M_t$ the action covariance under $\rho_t$ at $\Theta$,
--   $$B_t=\Psi_{t+1}(\Theta+\hat\theta)-\Psi_t(\Theta+\hat\theta)\le c\Big(\sqrt{\hat\theta^\top M_t\hat\theta}\,\sqrt{\hat\theta^\top\Sigma_t^{-1}\hat\theta}+\frac1T\Big).$$
--
--   Differences from the source:
--   - encoding: ≲, and "λ ≥ CG² log²(RGT) for a sufficiently large universal constant C" → ∃ C > 0, ∃ c > 0, chosen before every instance; reason: the paper's definition of ≲; the hypothesis on λ only strengthens as C grows, so "for all C ≥ C₀" and "for some C" are equivalent
--   - generalization: ‖θ̂_t‖₂ ≤ … almost surely (for the run's estimates) → the bound assumed for the current vector θ̂ only, pathwise; the past list and Θ arbitrary; reason: the paper applies the corollary pathwise (Appendix F, p.33); the run's estimates satisfy the hypothesis on every path where the a.s. bound holds
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: log²(RGT) with T the horizon and G a deterministic bound on ‖θ̂_t‖₂ (Appendix F, p.33) → Real.log (R·G·T) ^ 2 with T : ℕ, T ≥ 1, G : ℝ; reason: same instances (the square makes RGT < 1 meaningful)
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Corollary 8, p.12 (proof Appendix F, p.33)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Corollary 8 (`B_t` under random weighting).** Wei, arXiv:2610.17818, Corollary 8, p.12:
"Suppose ‖θ̂_t‖₂ ≤ G almost surely and λ ≥ CG² log²(RGT) for a sufficiently large universal
constant C. Then for every combination of ρ₁ in Table 2 and φ in Table 3, it holds that
B_t ≲ √(θ̂_tᵀM_tθ̂_t) √(θ̂_tᵀΣ_t⁻¹θ̂_t) + T⁻¹."

There are universal constants `C > 0` and `c > 0` such that, under Assumption 1 (any `d ≥ 1`, `A`,
`ν`, `r`, `R`), for every argmax selection `x`, profile `f` of Table 2, scalar law `φ` of Table 3,
`λ > 0`, horizon `T ≥ 1`, deterministic bound `G`, past `θs`, `Θ` and current estimate `θ̂` with
`‖θ̂‖ ≤ G` and `λ ≥ C G² log²(RGT)`:
`B_t = Ψ_{t+1}(Θ + θ̂) − Ψ_t(Θ + θ̂) ≤ c (√(θ̂ᵀM_tθ̂) √(θ̂ᵀΣ_t⁻¹θ̂) + 1/T)`.

**Formalization Note.** `≲` and "a sufficiently large universal constant C" are both chosen before
every instance. Because the hypothesis `λ ≥ C G² log²(RGT)` only gets stronger as `C` grows, "for
all `C ≥ C₀`" and "for some `C`" are equivalent here. "Almost surely" is applied pathwise to the
current estimate; the past is arbitrary. `log` is `Real.log` (its square is used, so `RGT < 1`
is meaningful, and `RGT = 1` gives the condition `λ ≥ 0`). `G` is "a deterministic upper bound on
‖θ̂_t‖₂" (Appendix F, p.33). -/
theorem corollary_8 : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ), IsNormalized A ν r R →
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
    ∀ (f : RadialProfile) (φ : ScalarLaw) (lam : ℝ), 0 < lam →
    ∀ (T : ℕ), 1 ≤ T → ∀ (G : ℝ),
    ∀ (t : ℕ) (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)),
      ‖θh‖ ≤ G → C * G ^ 2 * Real.log (R * G * T) ^ 2 ≤ lam →
      potential A (perturbDens (.randomWeighting f φ) lam
            (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d)) θs θh)) (Θ + θh) -
          potential A (perturbDens (.randomWeighting f φ) lam θs) (Θ + θh) ≤
        c * (Real.sqrt (actCovQ x (perturbDens (.randomWeighting f φ) lam θs) Θ θh) *
            Real.sqrt (quadForm (shapeMat lam θs)⁻¹ θh) + 1 / (T : ℝ)) := by sorry

end FTPLLinBandit
