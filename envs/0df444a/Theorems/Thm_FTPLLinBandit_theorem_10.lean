-- Prove2me | Theorems.Thm_FTPLLinBandit_theorem_10
-- name    : FTPLLinBandit.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:03:57.325058+00:00
-- url     : https://prove2.me/theorems/7cd829fb-9d6f-4a23-85e6-b450594d1125
-- title:
--   Theorem 10 — elliptical: $B_t\le\frac12\sqrt{\hat\theta_t^\top M_t\hat\theta_t}\sqrt{\hat\theta_t^\top\mathcal J^{\hat\theta_t}_t\hat\theta_t}$ (17) and the clipped bound (18)
-- statement:
--   Let $d\ge1$, $A\subseteq RB^d_2$, $x$ an argmax selection of $A$ (so $A$ is nonempty), $f$ a radial profile that is positive and nonincreasing on $[0,\infty)$, with $z\mapsto f(\|z\|_2)$ and $z\mapsto\|z\|_2f(\|z\|_2)$ integrable (so that $P_\Sigma\propto f(\|z\|_{\Sigma^{-1}})$ is a density with finite first moment; the three profiles of Table 4 are instances), and $\lambda>0$. Let $\hat\theta_1,\dots,\hat\theta_{t-1}$ be past estimates, $\hat\theta$ the current one, $\Sigma=\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$, $\Sigma_{t+1}=\Sigma+\hat\theta\hat\theta^\top$, $\rho_t=P_\Sigma$, $\rho_{t+1}=P_{\Sigma_{t+1}}$, $\Theta\in\mathbb R^d$, $M_t$ the action covariance under $\rho_t$ at $\Theta$, $B_t=\Psi_{t+1}(\Theta+\hat\theta)-\Psi_t(\Theta+\hat\theta)$ and $\kappa=\|\hat\theta\|_{\Sigma^{-1}}$. Then
--
--   1. $\displaystyle B_t\le\frac12\sqrt{\hat\theta^\top M_t\hat\theta}\,\sqrt{\hat\theta^\top\mathcal J^{\hat\theta}(P_\Sigma)\,\hat\theta}$;
--   2. for every finite clipping radius $L\ge\sqrt{1+\kappa^2}$,
--   $$B_t\le\frac12\sqrt{\hat\theta^\top M_t\hat\theta}\,\sqrt{\hat\theta^\top\mathcal J^{\hat\theta,L}(P_\Sigma)\,\hat\theta}+\frac{2R\|\hat\theta\|_2\,\kappa}{\sqrt d}\,\mathbb E_{Z\sim P_\Sigma}\Big[\|Z\|_{\Sigma^{-1}}\mathbf 1\Big\{\|Z\|_{\Sigma^{-1}}>\frac{L}{\sqrt{1+\kappa^2}}\Big\}\Big].$$
--
--   Here $\mathcal J^v$, $\mathcal J^{v,L}$ are the shifted elliptical information matrices of Definition 2; (17) is vacuous for Student-$t_2$, whose $\mathcal J^v$ is infinite, and the clipped (18) is what Corollary 11 uses for it.
--
--   Differences from the source:
--   - reading: "assume the radial profile f is positive and nonincreasing"; the theorem does not repeat that P_Σ is a density with finite first moment, which Lemma 21 (p.34) and the proof (p.31: "P_Σ has finite first moment") take as given → f : ℝ → ℝ positive and antitone on [0, ∞), with z ↦ f(‖z‖) and z ↦ ‖z‖f(‖z‖) integrable; reason: integrability is what makes P_Σ a density, and without the first moment Ψ_t is not finite, so B_t is undefined; these exclude no case in which the statement has a meaning; the three profiles of Table 4 are instances
--   - generalization: the standing Assumption 1 (rB ⊆ conv A ⊆ RB, ν, Cov(ν) = I/d) → only A ⊆ R·B^d_2, with an argmax selection x of A (which makes A nonempty); reason: Assumption 1 implies A ⊆ conv A ⊆ RB, and the oracle gives the selection; the proof uses only these, so the Lean statement specializes to the paper's
--   - generalization: the history-conditioned quantities Θ̂_t = Σ_{τ<t} θ̂_τ, θ̂_1, …, θ̂_{t−1}, θ̂_t of the run → an arbitrary point Θ, an arbitrary finite past list θs and an arbitrary current vector θ̂; reason: conditionally on the history these are fixed vectors; taking Θ = Σ θs recovers the paper's statement
--   - encoding: information quantities that may be +∞ (the bound is then vacuous) → values in [0, ∞] (lower Lebesgue integrals), compared with the real left side in EReal; 0·∞ = 0; reason: an infinite right side is +∞ exactly as in the paper; where the paper's product is the undefined 0·∞ (θ̂ᵀMθ̂ = 0), the Lean bound reads ≤ 0, which the proof gives (f > 0, so ⟨x(Θ + w) − µ, θ̂⟩ = 0 for a.e. w and the integrand of B_t vanishes)
--   - encoding: κ_t² = ‖θ̂_t‖²_{Σ_t⁻¹} and E_{Z∼P_Σ}[…] → κ² = θ̂ᵀΣ⁻¹θ̂ and a real integral against the density P_Σ; reason: same instances
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: the standing d ≥ 1 → the hypothesis 1 ≤ d; reason: the paper's standing assumption (§2.1, p.4)
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 10, Eqs. (17)–(18), p.13 (proof Appendix E.4, pp.30–33)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_ellDens
import Definitions.Def_FTPLLinBandit_shapeMat
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ
import Definitions.Def_FTPLLinBandit_ellipsoid
import Definitions.Def_FTPLLinBandit_ellInfoQ

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace FTPLLinBandit

/-- **Theorem 10 (Bounding `B_t` with `J^v_t` under elliptical perturbation).** Wei,
arXiv:2610.17818, Theorem 10, Eqs. (17)–(18), p.13: "Under the elliptical perturbation setup in
Figure 2, assume the radial profile f is positive and nonincreasing. Then
B_t ≤ (1/2) √(θ̂_tᵀM_tθ̂_t) √(θ̂_tᵀ J^{θ̂_t}_t θ̂_t). (17) Write κ_t = ‖θ̂_t‖_{Σ_t⁻¹}. For every
finite clipping radius L ≥ √(1 + κ_t²),
B_t ≤ (1/2) √(θ̂_tᵀM_tθ̂_t) √(θ̂_tᵀ J^{θ̂_t,L}_t θ̂_t)
+ (2R‖θ̂_t‖₂κ_t/√d) E_{Z∼P_{Σ_t}}[‖Z‖_{Σ_t⁻¹} 1{‖Z‖_{Σ_t⁻¹} > L/√(1 + κ_t²)}]. (18)"

For `A ⊆ R·B^d_2`, an argmax selection `x` (so `A` is nonempty), a radial profile `f` that is
positive and nonincreasing on `[0, ∞)` with `P_Σ ∝ f(‖z‖_{Σ⁻¹})` a density of finite first moment,
`λ > 0`, past estimates `θs`, `Θ` (the paper's `Θ̂_t`) and the current estimate `θ̂`: with
`Σ = Σ_t = shapeMat λ θs`, `Σ_{t+1} = Σ + θ̂θ̂ᵀ`, `ρ_t = P_Σ`, `ρ_{t+1} = P_{Σ_{t+1}}`,
`B_t = Ψ_{t+1}(Θ + θ̂) − Ψ_t(Θ + θ̂)` and `κ = ‖θ̂‖_{Σ⁻¹}`, both (17) and, for every real
`L ≥ √(1 + κ²)`, (18) hold.

**Formalization Note.** `f` is any profile with the theorem's own hypotheses, not only the three
of Table 4 (each of which satisfies them). `hfint` is Lemma 21's "nonnegative integrable radial
profile", which makes `P_Σ` a density. `hfmom` is the finite first moment the proof cites (p.31:
"P_Σ has finite first moment"), without which `Ψ_t` is not finite. Only the values of `f` on
`[0, ∞)` are read. The information terms are in `[0, ∞]` (`J^v` is infinite for Student-t₂,
Table 4, so (17) is then vacuous) and the comparison is in `EReal`; in `[0, ∞]`, `0 · ∞ = 0`. The
tail expectation is a real integral against `P_Σ`. `R` is any outer radius of `A`. -/
theorem theorem_10 {d t : ℕ} (hd : 1 ≤ d) (A : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall 0 R)
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hx : IsArgmaxSel A x)
    (f : ℝ → ℝ) (hfpos : ∀ s, 0 ≤ s → 0 < f s) (hfanti : AntitoneOn f (Set.Ici 0))
    (hfint : Integrable fun z : EuclideanSpace ℝ (Fin d) => f ‖z‖)
    (hfmom : Integrable fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ * f ‖z‖)
    (lam : ℝ) (hlam : 0 < lam)
    (θs : Fin t → EuclideanSpace ℝ (Fin d)) (Θ θh : EuclideanSpace ℝ (Fin d)) :
    ((potential A (ellDens f
          (shapeMat lam (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d)) θs θh))) (Θ + θh) -
        potential A (ellDens f (shapeMat lam θs)) (Θ + θh) : ℝ) : EReal) ≤
      ((ENNReal.ofReal (1 / 2 *
            Real.sqrt (actCovQ x (ellDens f (shapeMat lam θs)) Θ θh)) *
          ellInfoQ f (shapeMat lam θs) θh Set.univ θh ^ (1 / 2 : ℝ) : ℝ≥0∞) :
        EReal) ∧
    ∀ L : ℝ, Real.sqrt (1 + quadForm (shapeMat lam θs)⁻¹ θh) ≤ L →
      ((potential A (ellDens f
            (shapeMat lam (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d)) θs θh))) (Θ + θh) -
          potential A (ellDens f (shapeMat lam θs)) (Θ + θh) : ℝ) : EReal) ≤
        ((ENNReal.ofReal (1 / 2 *
              Real.sqrt (actCovQ x (ellDens f (shapeMat lam θs)) Θ θh)) *
            ellInfoQ f (shapeMat lam θs) θh
              (ellipsoid (shapeMat lam θs) L) θh ^ (1 / 2 : ℝ) : ℝ≥0∞) : EReal) +
          ((2 * R * ‖θh‖ * Real.sqrt (quadForm (shapeMat lam θs)⁻¹ θh) / Real.sqrt d *
              ∫ z, ellDens f (shapeMat lam θs) z *
                (if L / Real.sqrt (1 + quadForm (shapeMat lam θs)⁻¹ θh) <
                    Real.sqrt (quadForm (shapeMat lam θs)⁻¹ z)
                  then Real.sqrt (quadForm (shapeMat lam θs)⁻¹ z) else 0) : ℝ) : EReal) := by sorry

end FTPLLinBandit
