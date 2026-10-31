-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_2
-- name    : ExitGamePrivate.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:00.925689+00:00
-- url     : https://prove2.me/theorems/34a98227-06c3-4702-933e-c943b1201a49
-- title:
--   Lemma 4.2 — integrating out the opponent's type, (4.7)
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   Let $(A_t)_{t\ge0}$ be an $(\mathcal F_t)$-adapted process whose paths are right-continuous and increasing with $A_{0-}=0$, and let player $i$ use $\tau_i=\inf\{t\ge0:Y(A_t)<\theta_i\}$, which is (4.1) with $Y_t=Y(A_t)$. Then for every $x\in\mathcal I$, every exit value $\gamma\in[\theta_L,\theta_U]$ and every $(\mathcal F_t)$-stopping time $\sigma$,
--   $$J(x,\sigma,\tau_i;\gamma)=E_x\Big[\int_0^\sigma e^{-rs-A_s}D(X_s)\,ds+\gamma e^{-r\sigma-A_{\sigma-}}+\int_{[0,\sigma)}e^{-rs-A_s}m(X_s)\,dA_s\Big], \tag{4.7}$$
--   for $i=1$ and for $i=2$. Here $dA_s$ is the Lebesgue–Stieltjes measure of the path of $A$.
--
--   Since $\theta_i$ is independent of the public information, the opponent's random exit can be replaced by the survival weight $e^{-A}$ and an exit intensity $dA$: the best response becomes a Markovian stopping problem.
--
--   Differences from the source:
--   - encoding: A right-continuous and increasing with A₀₋ = 0 → every path is right-continuous on [0, ∞), increasing on [0, ∞) and A₀ ≥ 0; the path is extended by 0 to t < 0 (extZero), so A₀₋ = 0; reason: an increasing path with A₀₋ = 0 is exactly one with A₀ ≥ 0 extended by 0
--   - encoding: A_{σ−} and ∫_{[0,σ)} … dA_s → Function.leftLim of the extended path at σ, and the set integral over [0, σ) against the Stieltjes measure of the extended path (stieltjesMeasure), which charges the jump A₀ at 0; reason: same quantities
--   - encoding: τᵢ of the form (4.1), x, γ → both players i = 1, 2 stated; x ∈ 𝓘 and γ ∈ [θ_L, θ_U] as hypotheses; reason: J(x, σ, τ; γ) of (2.3) is defined for γ ∈ [θ_L, θ_U] and initial states in 𝓘
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: types θᵢ on complete probability spaces, product space (2.2), Fⁱₜ = F̃ₜ ∨ σ(θᵢ), Assumptions 2.2 and 4.1 (θᵢ have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U]) → TypeSpace with complete probability measures Q₁, Q₂ and measurable θ₁, θ₂ with Qᵢ{θᵢ ≤ y} = F(y); F continuous, strictly increasing on [θ_L, θ_U], 0 on (−∞, θ_L], 1 on [θ_U, ∞); filtrations on Ω × Θ₁ × Θ₂ built as comap σ-algebras; reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.2, p.14 ((4.7))

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.2** (arXiv:2210.01610v2, p.14). "Let τᵢ be of the form (4.1) with Yₜ = Y(Aₜ) for a
process (Aₜ)ₜ≥₀ which is (Fₜ)-adapted, right-continuous and increasing with A₀₋ = 0. For any
(Fₜ)-stopping time σ we have (4.7) J(x, σ, τᵢ; γ) =
Eₓ[∫_0^σ e^{−rs−A_s} D(X_s) ds + γ e^{−rσ−A_{σ−}} + ∫_{[0,σ)} e^{−rs−A_s} m(X_s) dA_s]."

Stated for both `τ₁ = inf{t ≥ 0 : Y(Aₜ) < θ₁}` and `τ₂ = inf{t ≥ 0 : Y(Aₜ) < θ₂}`, every
`x ∈ 𝓘` and every exit value `γ ∈ [θ_L, θ_U]`, under the standing assumptions of §4.

**Formalization Note** The path of `A` is extended by `0` to `t < 0` (`extZero`), which encodes
`A₀₋ = 0`; `A_{σ−}` is the left limit of the extended path at `σ`, and `dA_s` is the
Lebesgue–Stieltjes measure of the extended path (`stieltjesMeasure`), so `∫_{[0,σ)}` includes the
jump `A₀` at time `0`. "Increasing" is non-strict and, with right-continuity, required for every
path; `A₀₋ = 0` together with monotonicity gives `A₀ ≥ 0`. On `{σ = ∞}` the term
`γ e^{−rσ−A_{σ−}}` is `0`. -/
theorem lemma_4_2 {Ω Θ₁ Θ₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ₁]
    [MeasurableSpace Θ₂] (G : Model Ω) (T : TypeSpace Θ₁ Θ₂) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) (hT : T.IsComplete) (hF : T.HasCDF G.F)
    (A : ℝ → Ω → ℝ) (hA_adapt : ∀ t : ℝ, 0 ≤ t → Measurable[G.𝔽 t] (A t))
    (hA_rc : ∀ ω, ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (fun s => A s ω) (Ici t) t)
    (hA_mono : ∀ ω, MonotoneOn (fun s => A s ω) (Ici 0)) (hA0 : ∀ ω, 0 ≤ A 0 ω)
    (x : ℝ) (hx : x ∈ G.I) (σ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime G.filt σ)
    (γ : ℝ) (hγ : γ ∈ Icc G.θL G.θU) :
    let rhs : ℝ := ∫ ω, ((∫ s in window (σ ω),
          Real.exp (-(G.r * s) - A s ω) * G.D (G.X x s ω)) +
        γ * (disc G.r (σ ω) *
          Real.exp (-(Function.leftLim (extZero (fun s => A s ω)) (((σ ω).untopD 0 : ℝ≥0) : ℝ)))) +
        ∫ s in window (σ ω), Real.exp (-(G.r * s) - A s ω) * G.m (G.X x s ω)
          ∂(stieltjesMeasure (extZero (fun s => A s ω)))) ∂G.P
    G.Jgam T x σ (fun ω => hittingAfter (fun (t : ℝ≥0) ω' => G.Y (A t ω')) (Iio (T.θ₁ ω.2.1)) 0 ω.1)
        γ = rhs ∧
      G.Jgam T x σ
        (fun ω => hittingAfter (fun (t : ℝ≥0) ω' => G.Y (A t ω')) (Iio (T.θ₂ ω.2.2)) 0 ω.1)
        γ = rhs := by sorry

end ExitGamePrivate
