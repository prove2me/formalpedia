-- Prove2me | Theorems.Thm_FTPLLinBandit_theorem_4
-- name    : FTPLLinBandit.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:57.992302+00:00
-- url     : https://prove2.me/theorems/fbbb325e-d678-44a7-bfbb-bb21ee36c8d3
-- title:
--   Theorem 4 — $A_t\le\frac12\sqrt{\hat\theta_t^\top M_t\hat\theta_t}\,\sup_{s\in[0,1]}\sqrt{\hat\theta_t^\top\mathcal I^{s\hat\theta_t}_t\hat\theta_t}$
-- statement:
--   Let $A\subseteq RB^d_2$ and let $x$ be an argmax selection of $A$ (so $A$ is nonempty). Let $\rho$ be a regular perturbation density that is positive almost everywhere, $\Psi(\Theta)=\mathbb E_{Z\sim\rho}[h(\Theta+Z)]$, and for $\Theta,\hat\theta\in\mathbb R^d$ let $\mu$ and $M$ be the mean and covariance of $x(\Theta+Z)$, $Z\sim\rho$. Then the stability term
--   $$A=\Psi(\Theta+\hat\theta)-\Psi(\Theta)-\langle\mu,\hat\theta\rangle$$
--   satisfies
--   $$A\le\frac12\sqrt{\hat\theta^\top M\hat\theta}\;\sup_{s\in[0,1]}\sqrt{\hat\theta^\top\mathcal I^{s\hat\theta}(\rho)\,\hat\theta},$$
--   where $\mathcal I^v(\rho)$ is the shifted Fisher-information matrix of Definition 1 (the right side may be $+\infty$). With $\rho=\rho_t$, $\Theta=\hat\Theta_t$, $\hat\theta=\hat\theta_t$ this is the paper's (12) for $A_t$ (7); it holds for both random-weighting and elliptical perturbations.
--
--   Differences from the source:
--   - generalization: ρ_t of either construction of Figure 2 → any regular density ρ positive almost everywhere; reason: both run densities are regular (Lemma 18: "all perturbations in this paper are regular") and positive; the proof uses only Lemma 18 and Definition 1
--   - generalization: the standing Assumption 1 (rB ⊆ conv A ⊆ RB, ν, Cov(ν) = I/d) → only A ⊆ R·B^d_2, with an argmax selection x of A (which makes A nonempty); reason: Assumption 1 implies A ⊆ conv A ⊆ RB, and the oracle gives the selection; the proof uses only these, so the Lean statement specializes to the paper's
--   - generalization: Θ̂_t and θ̂_t of the run → arbitrary Θ and θ̂; reason: conditionally on the history these are fixed vectors; the paper's statement is the special case
--   - encoding: information quantities that may be +∞ (the bound is then vacuous) → values in [0, ∞] (lower Lebesgue integrals), compared with the real left side in EReal; 0·∞ = 0; reason: an infinite right side is +∞ exactly as in the paper; where the paper's product is the undefined 0·∞ (θ̂ᵀMθ̂ = 0), the Lean bound reads ≤ 0, which the proof gives (f > 0, so ⟨x(Θ + w) − µ, θ̂⟩ = 0 for a.e. w and the integrand of B_t vanishes)
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 4, Eq. (12), p.11 (proof Appendix E.1, p.27)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_IsRegularDensity
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ
import Definitions.Def_FTPLLinBandit_fisherQ

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace FTPLLinBandit

/-- **Theorem 4 (Bounding `A_t` with `I^v_t`).** Wei, arXiv:2610.17818, Theorem 4, Eq. (12), p.11:
"The theorem below holds for both random-weighting and elliptical perturbations. … We have
A_t ≤ (1/2) √(θ̂_tᵀ M_t θ̂_t) sup_{s∈[0,1]} √(θ̂_tᵀ I^{sθ̂_t}_t θ̂_t)", with
`A_t = Ψ_t(Θ̂_{t+1}) − Ψ_t(Θ̂_t) − ⟨µ_t, θ̂_t⟩` (7), p.10.

For every regular density `ρ` positive almost everywhere, every `Θ` (the paper's `Θ̂_t`) and every
`θ̂` (the paper's `θ̂_t`, with `Θ̂_{t+1} = Θ + θ̂`):
`Ψ(Θ + θ̂) − Ψ(Θ) − ⟨µ, θ̂⟩ ≤ ½ √(θ̂ᵀMθ̂) · sup_{s∈[0,1]} √(θ̂ᵀ I^{sθ̂}(ρ) θ̂)`.

**Formalization Note.** The right side is in `[0, ∞]` (the information may be infinite, in which
case the bound is vacuous, as the proof notes) and is compared in `EReal` with the real left side.
In `[0, ∞]`, `0 · ∞ = 0`. The statement covers every regular a.e.-positive density, in particular
both run densities; Assumption 1 is replaced by `A ⊆ R·B^d_2` (`A` is nonempty because the argmax
selection `x` takes values in it). -/
theorem theorem_4 {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall 0 R)
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hx : IsArgmaxSel A x)
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : IsRegularDensity ρ) (hpos : ∀ᵐ z, 0 < ρ z)
    (Θ θh : EuclideanSpace ℝ (Fin d)) :
    ((potential A ρ (Θ + θh) - potential A ρ Θ - ⟪actMean x ρ Θ, θh⟫_ℝ : ℝ) : EReal) ≤
      ((ENNReal.ofReal (1 / 2 * Real.sqrt (actCovQ x ρ Θ θh)) *
        ⨆ s ∈ Set.Icc (0 : ℝ) 1, fisherQ ρ (s • θh) θh ^ (1 / 2 : ℝ) : ℝ≥0∞) : EReal) := by sorry

end FTPLLinBandit
