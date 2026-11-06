-- Prove2me | Theorems.Thm_FTPLLinBandit_eq_10
-- name    : FTPLLinBandit.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:10:40.57411+00:00
-- url     : https://prove2.me/theorems/a643faf1-8a57-49d5-9e33-f8dd1d387f72
-- title:
--   Eq. (10) — regret decomposition $\mathrm{Reg}_T(a)\le\mathbb E[\Psi_1(0)-\langle a,\mathbb E_{\rho_{T+1}}Z\rangle+\sum_t(A_t+B_t)]+2R\sum_t\mathbb E\varepsilon_t+2\gamma T$
-- statement:
--   Assume Assumption 1 with $d\ge1$, let $x$ be an argmax selection, and run Algorithm 1 with any perturbation scheme with $\lambda>0$, any $\gamma\in[0,1]$, $\beta>0$ and $N\in\mathbb N$ against an adaptive adversary. On each outcome let $\rho_t$ be the perturbation density built from $\hat\theta_1,\dots,\hat\theta_{t-1}$, $\hat\Theta_t=\sum_{\tau<t}\hat\theta_\tau$, $\Psi_t$ the potential under $\rho_t$, $\mu_t$ the action mean under $\rho_t$ at $\hat\Theta_t$,
--   $$A_t=\Psi_t(\hat\Theta_{t+1})-\Psi_t(\hat\Theta_t)-\langle\mu_t,\hat\theta_t\rangle,\qquad B_t=\Psi_{t+1}(\hat\Theta_{t+1})-\Psi_t(\hat\Theta_{t+1}),$$
--   and let $\varepsilon_t=\|\mathbb E_t[\hat\theta_t]-\theta_t\|_2$ be the conditional estimation bias. Then for every horizon $T$ and every comparator $a\in A$,
--   $$\mathrm{Reg}_T(a)\le\mathbb E\Big[\Psi_1(0)-\big\langle a,\mathbb E_{Z\sim\rho_{T+1}}[Z]\big\rangle+\sum_{t=1}^T(A_t+B_t)\Big]+2R\sum_{t=1}^T\mathbb E[\varepsilon_t]+2\gamma T .$$
--
--   The decomposition splits the regret into the penalty $\Psi_1(0)$, the two stability terms bounded in Sections 6–7, the geometric-resampling bias of Theorem 12, and the exploration cost.
--
--   Differences from the source:
--   - generalization: an adversary that may depend on the past and chooses θ_t, b_t before round t's draws; E_t is conditioning on the history before round t → θ_t, b_t adapted to any filtration 𝓕 with the round-t draws independent of 𝓕_t and 𝓕_{t+1}-measurable; E_t is conditional expectation given 𝓕_t; reason: the history filtration of a deterministic adaptive adversary is an instance; the filtration may also carry the adversary's own randomness
--   - encoding: ε_t ≥ 0 any quantity determined by the past with ‖E_t[θ̂_t] − θ_t‖₂ ≤ ε_t → ε_t equal to ‖E_t[θ̂_t] − θ_t‖₂; reason: the bias itself is determined by the past and is the smallest admissible ε_t; the display for any larger ε_t follows
--   - encoding: e ∼ Bernoulli(γ), explore iff e = 1 → a uniform coin U on [0, 1], explore iff U < γ; reason: same law for γ ∈ [0, 1]
--   - generalization: elliptical sampling Z_t = Σ_t^{1/2} S U → Z_t = B(Σ_t) W with W ∼ P_I and any measurable B with B(Σ)B(Σ)ᵀ = Σ for positive definite Σ; reason: every such factor gives Z_t ∼ P_{Σ_t}; B = Σ^{1/2} with W = SU is the paper's sampler
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
--   - encoding: SampleAction draws e, then either a ∼ ν or Z ∼ ρ_t; for random weighting Z = Z′ + Σ ξ_τ θ̂_τ with Z′ ∼ ρ₁ → every call (2N + 2 slots per round, Fin (2N + 2)) draws its coin, X ∼ ν, W ∼ P_I and weights up front and uses what it needs; Z = √λ W + Σ ξ_τ θ̂_τ; reason: √λ W ∼ P_{λI} = ρ₁, and a draw that is not used changes no law; the slots are independent, as the calls of Algorithm 1 are
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Eq. (10), §5, p.10

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_perturbDens
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actMean
import Definitions.Def_FTPLLinBandit_FTPLRun_regret

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Eq. (10) (regret decomposition).** Wei, arXiv:2610.17818, §5, Eq. (10), p.10: "suppose the
conditional estimation bias satisfies ‖E_t[θ̂_t] − θ_t‖₂ ≤ ε_t, where ε_t ≥ 0 is determined by the
past. Then, … Summing and applying Equation (9) gives
Reg_T(a) ≤ E[Ψ₁(0) − ⟨a, E_{Z∼ρ_{T+1}}[Z]⟩ + ∑_{t=1}^T (A_t + B_t)] + 2R ∑_{t=1}^T E[ε_t] + 2γT."

Under Assumption 1 (with `d ≥ 1`), for every argmax selection `x`, every scheme `s` with `λ > 0`,
every `γ ∈ [0, 1]`, `β > 0`, `N ∈ ℕ`, every run of Algorithm 1 on a probability space, every
horizon `T` and every comparator `a ∈ A`: writing, on each outcome, `ρ_t` for the scheme's density
built from `θ̂_0, …, θ̂_{t−1}`, `Θ̂_t = ∑_{τ<t} θ̂_τ`,
`A_t = Ψ_{ρ_t}(Θ̂_{t+1}) − Ψ_{ρ_t}(Θ̂_t) − ⟨µ_t, θ̂_t⟩` (7) and
`B_t = Ψ_{ρ_{t+1}}(Θ̂_{t+1}) − Ψ_{ρ_t}(Θ̂_{t+1})` (8), and `ε_t = ‖E[θ̂_t | 𝓕_t] − θ_t‖`,
`Reg_T(a) ≤ E[Ψ_{ρ_0}(0) − ⟨a, E_{Z∼ρ_T}[Z]⟩ + ∑_{t<T}(A_t + B_t)] + 2R ∑_{t<T} E[ε_t] + 2γT`.

**Formalization Note.** Rounds are indexed from `0`: `ρ_0` is the paper's `ρ_1` and `ρ_T` the
paper's `ρ_{T+1}`. `ε_t` is taken equal to the conditional bias itself, the smallest admissible
choice; the display for any larger `ε_t` follows. `E_t` is the conditional expectation given
`𝓕 t`. -/
theorem eq_10 {d : ℕ} (hd : 1 ≤ d) {A : Set (EuclideanSpace ℝ (Fin d))}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} {r R : ℝ} (hn : IsNormalized A ν r R)
    {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hx : IsArgmaxSel A x)
    (s : Scheme) (γ β : ℝ) (N : ℕ) (lam : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hβ0 : 0 < β)
    (hlam : 0 < lam)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : FTPLRun A ν x s γ β N lam Ω P) (T : ℕ) (a : EuclideanSpace ℝ (Fin d))
    (ha : a ∈ A) :
    run.regret T a ≤
      ∫ ω, (potential A (perturbDens s lam (fun τ : Fin 0 => run.thetaHat τ ω)) 0 -
          ⟪a, ∫ z, perturbDens s lam (fun τ : Fin T => run.thetaHat τ ω) z • z⟫_ℝ +
          ∑ t ∈ Finset.range T,
            ((potential A (perturbDens s lam (fun τ : Fin t => run.thetaHat τ ω))
                (∑ τ ∈ Finset.range (t + 1), run.thetaHat τ ω) -
              potential A (perturbDens s lam (fun τ : Fin t => run.thetaHat τ ω))
                (∑ τ ∈ Finset.range t, run.thetaHat τ ω) -
              ⟪actMean x (perturbDens s lam (fun τ : Fin t => run.thetaHat τ ω))
                (∑ τ ∈ Finset.range t, run.thetaHat τ ω), run.thetaHat t ω⟫_ℝ) +
            (potential A (perturbDens s lam (fun τ : Fin (t + 1) => run.thetaHat τ ω))
                (∑ τ ∈ Finset.range (t + 1), run.thetaHat τ ω) -
              potential A (perturbDens s lam (fun τ : Fin t => run.thetaHat τ ω))
                (∑ τ ∈ Finset.range (t + 1), run.thetaHat τ ω)))) ∂P +
        2 * R * ∑ t ∈ Finset.range T, ∫ ω, ‖(P[run.thetaHat t | run.𝓕 t]) ω - run.θ t ω‖ ∂P +
        2 * γ * T := by sorry

end FTPLLinBandit
