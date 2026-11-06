-- Prove2me | Theorems.Thm_FTPLLinBandit_theorem_12
-- name    : FTPLLinBandit.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:09:58.594721+00:00
-- url     : https://prove2.me/theorems/11e40be2-f443-4644-a46b-a4344aa7e72b
-- title:
--   Theorem 12 — geometric resampling: bias $\le e^{-\beta\gamma(N+1)/d}/r$, range $\|\hat\theta_t\|\le2R\beta(N+1)$, $\mathbb E_t[\hat\theta_t^\top M_t\hat\theta_t]\le\frac{4d}{1-\gamma}$
-- statement:
--   Assume Assumption 1 with radii $r,R$ and $d\ge1$, and let $x$ be an argmax selection of $A$. Run Algorithm 1 with any perturbation scheme of Figure 2 with scale $\lambda>0$, exploration rate $\gamma\in(0,1)$, truncation $N\in\mathbb N$ and step size
--   $$0<\beta\le\frac1{2R^2},$$
--   against an adaptive adversary with $|\langle a,\theta_t\rangle+b_t|\le1$ on $A$. Let $\mathbb E_t$ denote conditional expectation given the information $\mathcal F_t$ before round $t$, let $\hat\theta_t=H_t(a_t-\bar a_t)y_t$ be the geometric-resampling estimate, and let $M_t$ be the covariance of $x(\hat\Theta_t+Z)$, $Z\sim\rho_t$. Then for every round $t$, almost surely,
--
--   1. $\varepsilon_t:=\big\|\mathbb E_t[\hat\theta_t]-\theta_t\big\|_2\le \dfrac{e^{-\beta\gamma(N+1)/d}}{r}$;
--   2. $\|\hat\theta_t\|_2\le2R\beta(N+1)$;
--   3. $\mathbb E_t\big[\hat\theta_t^\top M_t\hat\theta_t\big]\le\dfrac{4d}{1-\gamma}$.
--
--   The bias enters the regret decomposition (10) directly, the range bound fixes how large the perturbation scale $\lambda$ must be, and the second-moment bound controls a factor of the stability terms.
--
--   **Formalization Note** The bounds are stated almost surely because the exploration draws lie in $A$ only $\nu$-almost surely.
--
--   Differences from the source:
--   - generalization: an adversary that may depend on the past and chooses θ_t, b_t before round t's draws; E_t is conditioning on the history before round t → θ_t, b_t adapted to any filtration 𝓕 with the round-t draws independent of 𝓕_t and 𝓕_{t+1}-measurable; E_t is conditional expectation given 𝓕_t; reason: the history filtration of a deterministic adaptive adversary is an instance; the filtration may also carry the adversary's own randomness
--   - encoding: the bounds of (19), for the conditional expectation and the estimate → each bound holds P-almost surely; reason: conditional expectations are defined up to null sets, and the exploration draws lie in A only ν-almost surely
--   - encoding: e ∼ Bernoulli(γ), explore iff e = 1 → a uniform coin U on [0, 1], explore iff U < γ; reason: same law for γ ∈ [0, 1]
--   - generalization: elliptical sampling Z_t = Σ_t^{1/2} S U → Z_t = B(Σ_t) W with W ∼ P_I and any measurable B with B(Σ)B(Σ)ᵀ = Σ for positive definite Σ; reason: every such factor gives Z_t ∼ P_{Σ_t}; B = Σ^{1/2} with W = SU is the paper's sampler
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: the covariance matrix M_t (and matrix inequalities ⪯) → its quadratic form actCovQ (inequalities between quadratic forms in every direction); reason: a symmetric matrix is determined by its quadratic form; same instances
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
--   - encoding: SampleAction draws e, then either a ∼ ν or Z ∼ ρ_t; for random weighting Z = Z′ + Σ ξ_τ θ̂_τ with Z′ ∼ ρ₁ → every call (2N + 2 slots per round, Fin (2N + 2)) draws its coin, X ∼ ν, W ∼ P_I and weights up front and uses what it needs; Z = √λ W + Σ ξ_τ θ̂_τ; reason: √λ W ∼ P_{λI} = ρ₁, and a draw that is not used changes no law; the slots are independent, as the calls of Algorithm 1 are
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 12, Eq. (19), p.13 (proof Appendix I.3, p.47)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_actCovQ
import Definitions.Def_FTPLLinBandit_FTPLRun_thetaHat

open MeasureTheory ProbabilityTheory

namespace FTPLLinBandit

/-- **Theorem 12 (Geometric-resampling estimator bounds).** Wei, arXiv:2610.17818, Theorem 12,
Eq. (19), p.13: "In the normalized setting, let γ ∈ (0, 1), N ≥ 0 be an integer, and
0 < β ≤ 1/(2R²). For the geometric-resampling estimator θ̂_t = H_t(a_t − ā_t)y_t in Algorithm 1,
set ε_t = ‖E_t[θ̂_t] − θ_t‖₂. Then ε_t ≤ e^{−βγ(N+1)/d}/r, ‖θ̂_t‖₂ ≤ 2Rβ(N + 1),
E_t[θ̂_tᵀM_tθ̂_t] ≤ 4d/(1 − γ)."

Under Assumption 1 (with `d ≥ 1`), for every argmax selection `x`, every perturbation scheme `s`
with scale `λ > 0`, every `γ ∈ (0, 1)`, `0 < β ≤ 1/(2R²)`, `N ∈ ℕ`, every run of Algorithm 1 on a
probability space and every round `t`, almost surely:

1. `‖E[θ̂_t | 𝓕_t] − θ_t‖ ≤ e^{−βγ(N+1)/d}/r`;
2. `‖θ̂_t‖ ≤ 2Rβ(N + 1)`;
3. `E[θ̂_tᵀ M_t θ̂_t | 𝓕_t] ≤ 4d/(1 − γ)`, where `M_t` is the covariance of `x(Θ̂_t + Z)`,
   `Z ∼ ρ_t`, with `ρ_t` the scheme's density built from `θ̂_0, …, θ̂_{t−1}` and
   `Θ̂_t = ∑_{τ<t} θ̂_τ`.

**Formalization Note.** `E_t` is the conditional expectation given `𝓕 t`, the information before
round `t` (rounds indexed from `0`). The inequalities hold almost surely (exploration draws lie in
`A` only `ν`-almost surely). -/
theorem theorem_12 {d : ℕ} (hd : 1 ≤ d) {A : Set (EuclideanSpace ℝ (Fin d))}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} {r R : ℝ} (hn : IsNormalized A ν r R)
    {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hx : IsArgmaxSel A x)
    (s : Scheme) (γ β : ℝ) (N : ℕ) (lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hβ0 : 0 < β)
    (hβ : β ≤ 1 / (2 * R ^ 2)) (hlam : 0 < lam)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : FTPLRun A ν x s γ β N lam Ω P) (t : ℕ) :
    (∀ᵐ ω ∂P, ‖(P[run.thetaHat t | run.𝓕 t]) ω - run.θ t ω‖ ≤
        Real.exp (-(β * γ * ((N : ℝ) + 1) / d)) / r) ∧
    (∀ᵐ ω ∂P, ‖run.thetaHat t ω‖ ≤ 2 * R * β * ((N : ℝ) + 1)) ∧
    (∀ᵐ ω ∂P, (P[fun ω' => actCovQ x (perturbDens s lam (fun τ : Fin t => run.thetaHat τ ω'))
          (∑ τ ∈ Finset.range t, run.thetaHat τ ω') (run.thetaHat t ω') | run.𝓕 t]) ω ≤
        4 * d / (1 - γ)) := by sorry

end FTPLLinBandit
