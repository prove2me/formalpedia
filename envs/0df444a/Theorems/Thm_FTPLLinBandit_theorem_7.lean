-- Prove2me | Theorems.Thm_FTPLLinBandit_theorem_7
-- name    : FTPLLinBandit.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:28.010348+00:00
-- url     : https://prove2.me/theorems/87cde4c5-ab60-4830-8c14-da5a947884ee
-- title:
--   Theorem 7 — random weighting: the clipped bound (14) on $B_t$ for every threshold $L\ge1$
-- statement:
--   Let $d\ge1$, $A\subseteq RB^d_2$, $x$ an argmax selection of $A$ (so $A$ is nonempty), $\rho_1=P_{\lambda I}$ an initializer of Table 2 with $\lambda>0$ and $\varphi$ a scalar law of Table 3. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be past estimates, $\hat\theta$ the current one, $\rho_t$ and $\rho_{t+1}$ the random-weighting densities built from $(\hat\theta_1,\dots,\hat\theta_{t-1})$ and $(\hat\theta_1,\dots,\hat\theta_{t-1},\hat\theta)$, $\Theta\in\mathbb R^d$ (the paper's $\hat\Theta_t$), and $M_t$ the action covariance under $\rho_t$ at $\Theta$. Then for every $L\ge1$ the stability term $B_t=\Psi_{t+1}(\Theta+\hat\theta)-\Psi_t(\Theta+\hat\theta)$ satisfies
--   $$B_t\le\frac12\sqrt{\hat\theta^\top M_t\hat\theta}\;\mathbb E_{\xi\sim\varphi}\Big[\xi^2\mathbf 1\{|\xi|\le L\}\sup_{s\in[0,1]}\sqrt{\hat\theta^\top\mathcal I^{(1+s\xi)\hat\theta}(\rho_t)\,\hat\theta}\Big]+2R\|\hat\theta\|_2\,\mathbb E_{\xi\sim\varphi}\big[|\xi|\mathbf 1\{|\xi|>L\}\big].$$
--
--   The second term handles the rare large weights; with the tail bounds of Table 3 it becomes the $T^{-1}$ remainder of Corollary 8.
--
--   Differences from the source:
--   - generalization: the standing Assumption 1 (rB ⊆ conv A ⊆ RB, ν, Cov(ν) = I/d) → only A ⊆ R·B^d_2, with an argmax selection x of A (which makes A nonempty); reason: Assumption 1 implies A ⊆ conv A ⊆ RB, and the oracle gives the selection; the proof uses only these, so the Lean statement specializes to the paper's
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: the expectation E_{ξ∼φ}[ξ²1{|ξ|≤L} sup_s √(…)] (possibly infinite) and the tail E_{ξ∼φ}[|ξ|1{|ξ|>L}] → a lower Lebesgue integral in [0, ∞] against the density φ, and a real integral; the comparison in EReal with 0·∞ = 0; reason: the tail is finite for both laws; an infinite first term is +∞ as in the paper; at the undefined 0·∞ (θ̂ᵀM_tθ̂ = 0) the proof gives the bound without the first term
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: the standing d ≥ 1 → the hypothesis 1 ≤ d; reason: the paper's standing assumption (§2.1, p.4)
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 7, Eq. (14), p.11 (proof Appendix E.3, pp.29–30)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ
import Definitions.Def_FTPLLinBandit_fisherQ

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace FTPLLinBandit

/-- **Theorem 7 (Bounding `B_t` with `I^v_t` under random-weighting perturbations).** Wei,
arXiv:2610.17818, Theorem 7, Eq. (14), p.11: "Under the random-weighting setup in Figure 2, for
every threshold L ≥ 1, we have
B_t ≤ (1/2) √(θ̂_tᵀM_tθ̂_t) E_{ξ∼φ}[ξ² 1{|ξ|≤L} sup_{s∈[0,1]} √(θ̂_tᵀ I^{(1+sξ)θ̂_t}_t θ̂_t)]
+ 2R‖θ̂_t‖₂ E_{ξ∼φ}[|ξ| 1{|ξ|>L}]", with `B_t = Ψ_{t+1}(Θ̂_{t+1}) − Ψ_t(Θ̂_{t+1})` (8), p.10.

For `A ⊆ R·B^d_2`, an argmax selection `x` (so `A` is nonempty), a profile `f` of Table 2, a scalar
law `φ` of Table 3, `λ > 0`, past estimates `θs`, `Θ` (the paper's `Θ̂_t`), the current estimate
`θ̂` and every `L ≥ 1`: with `ρ_t = rwDens ρ₁ φ θs`, `ρ_{t+1} = rwDens ρ₁ φ (θs, θ̂)`,
`Θ̂_{t+1} = Θ + θ̂` and `M_t` the action covariance under `ρ_t` at `Θ`,
`Ψ_{ρ_{t+1}}(Θ + θ̂) − Ψ_{ρ_t}(Θ + θ̂)` is at most the right side of (14).

**Formalization Note.** The first expectation is a lower Lebesgue integral in `[0, ∞]` against the
density `φ` (its integrand may be infinite); the tail expectation is a real integral (finite for
both laws of Table 3). The comparison is in `EReal`; in `[0, ∞]`, `0 · ∞ = 0`. `R` is any outer
radius of `A` (Assumption 1 is replaced by what the proof uses, `A ⊆ R·B^d_2`). `ρ_{t+1}` appends `θ̂` to the past (`Fin.snoc`). -/
theorem theorem_7 {d t : ℕ} (hd : 1 ≤ d) (A : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall 0 R)
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hx : IsArgmaxSel A x)
    (f : RadialProfile) (φ : ScalarLaw) (lam : ℝ) (hlam : 0 < lam)
    (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (hL : 1 ≤ L) :
    ((potential A (perturbDens (.randomWeighting f φ) lam
          (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d)) θs θh)) (Θ + θh) -
        potential A (perturbDens (.randomWeighting f φ) lam θs) (Θ + θh) : ℝ) : EReal) ≤
      ((ENNReal.ofReal (1 / 2 *
            Real.sqrt (actCovQ x (perturbDens (.randomWeighting f φ) lam θs) Θ θh)) *
          ∫⁻ ξ, (if |ξ| ≤ L then
              ENNReal.ofReal (scalarDens φ ξ * ξ ^ 2) *
                ⨆ s ∈ Set.Icc (0 : ℝ) 1,
                  fisherQ (perturbDens (.randomWeighting f φ) lam θs) ((1 + s * ξ) • θh) θh ^
                    (1 / 2 : ℝ)
            else 0) : ℝ≥0∞) : EReal) +
        ((2 * R * ‖θh‖ * ∫ ξ, (if L < |ξ| then scalarDens φ ξ * |ξ| else 0) : ℝ) : EReal) := by sorry

end FTPLLinBandit
