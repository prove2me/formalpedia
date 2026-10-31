-- Prove2me | Theorems.Thm_ExitGamePrivate_theorem_4_17
-- name    : ExitGamePrivate.theorem_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:03.710992+00:00
-- url     : https://prove2.me/theorems/da8603e4-c13a-424a-ba6d-31491ea64cf3
-- title:
--   Theorem 4.17 — the belief-driven profile $\tau_i=\inf\{t\ge0:Y(A_t)<\theta_i\}$ is a Nash equilibrium
-- statement:
--   Consider the exit game of §2 under Assumptions 2.2, 2.3, 2.4, 3.1 and 4.1: a diffusion $dX_t=\mu(X_t)dt+b(X_t)dW_t$ on $\mathcal I=(x_L,x_U)$, two firms earning the duopoly flow $D(X_t)$, private exit values $\theta_1,\theta_2$ i.i.d. with continuous CDF $F$ strictly increasing on $[\theta_L,\theta_U]$, and a survivor who collects the monopoly value $m(X)$.
--
--   For every initial state $x\in\mathcal I$, let $A$ be the (largest) Carathéodory solution of
--   $$A_t=\int_0^t\lambda\big(X_s,Y(A_s)\big)\,ds,\qquad \lambda(x,y)=\frac{ry-D(x)}{m(x)-y}1_{x\le\alpha(y)},\quad Y(a)=F^{-1}(e^{-a}),$$
--   along the path of $X^x$, and let
--   $$\tau_i=\inf\{t\ge0:Y(A_t)<\theta_i\},\qquad i=1,2. \tag{4.1}$$
--   Then $(\tau_1,\tau_2)$ is a Nash equilibrium for $x$ in the sense of Definition 2.6:
--   1. $\tau_1$ is an $(\mathcal F^1_t)$-stopping time and $\tau_2$ an $(\mathcal F^2_t)$-stopping time;
--   2. $J_1(x,\tau_1',\tau_2)\le J_1(x,\tau_1,\tau_2)$ for every $(\mathcal F^1_t)$-stopping time $\tau_1'$;
--   3. $J_2(x,\tau_1,\tau_2')\le J_2(x,\tau_1,\tau_2)$ for every $(\mathcal F^2_t)$-stopping time $\tau_2'$.
--
--   Here $\alpha(\theta)$ is the optimal exit threshold of a firm of type $\theta$ whose rival never exits (Assumption 3.1), and $Y(A_t)$ is the highest type still in the game. The theorem gives an explicit symmetric equilibrium of a war of attrition with private information driven by a diffusion.
--
--   Differences from the source:
--   - reading: the process (Aₜ) of Proposition 4.6, constructed as A⁰ = lim_{ε↓0} A^ε from (4.35)–(4.36) (p.26), with A^{x,a} its version started at (x, a) (p.16) → Model.Asol α x a: the pathwise supremum of all Carathéodory solutions of (4.13) along Xˣ(ω) started at a (the largest solution); reason: the paper identifies A⁰ as the largest Carathéodory solution (Remark 4.7, p.16; p.32); every solution lies below each A^ε by comparison and A⁰ solves (4.13) a.s., so the two agree a.s.; (4.35) itself needs α^{−1} outside [α(θ_L), α(θ_U)], where it is undefined
--   - reading: "Let τ₁, τ₂ be given by (4.1) with (Aₜ) stated in (4.3)" → τᵢ = tauHat α x · θᵢ with A = Asol α x 0, the process of Proposition 4.6 started at A₀ = 0; reason: (4.3) defines only Y(a); the process is that of Proposition 4.6, and the proof (p.22) uses v(x, 0; θ), i.e. A₀ = 0
--   - reading: "(τ₁, τ₂) is a Nash equilibrium in the sense of Definition 2.6" (Definition 2.6 is "for x") → for every x ∈ 𝓘; reason: the proof (p.22) shows the best-response property for every θ ∈ [θ_L, θ_U] and x ∈ 𝓘
--   - encoding: Nash inequalities "P̃ₓ-a.s." (Definition 2.6) → plain inequalities between the real payoffs J₁, J₂; reason: both sides are expectations
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: types θᵢ on complete probability spaces, product space (2.2), Fⁱₜ = F̃ₜ ∨ σ(θᵢ), Assumptions 2.2 and 4.1 (θᵢ have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U]) → TypeSpace with complete probability measures Q₁, Q₂ and measurable θ₁, θ₂ with Qᵢ{θᵢ ≤ y} = F(y); F continuous, strictly increasing on [θ_L, θ_U], 0 on (−∞, θ_L], 1 on [θ_U, ∞); filtrations on Ω × Θ₁ × Θ₂ built as comap σ-algebras; reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Theorem 4.17, p.21 (proof p.22)

import Mathlib
import Definitions.Def_ExitGamePrivate_BestResponse

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Theorem 4.17** (Kwon & Palczewski, *Exit Game with Private Information*,
arXiv:2210.01610v2, p.21; proof p.22). "Let τ₁, τ₂ be given by (4.1) with (Aₜ) stated in (4.3).
Then (τ₁, τ₂) is a Nash equilibrium in the sense of Definition 2.6."

Under the setting of §2 and Assumptions 2.2–2.4, 3.1 and 4.1, for every initial state `x ∈ 𝓘`,
with `A = A^{x,0}` the maximal Carathéodory solution of (4.13) started at `A₀ = 0` along `Xˣ`,
the profile `τᵢ = inf{t ≥ 0 : Y(Aₜ) < θᵢ}`, `i = 1, 2`, is a Nash equilibrium for `x`: each `τᵢ`
is an `(Fⁱₜ)`-stopping time, and no `(Fⁱₜ)`-stopping time improves player `i`'s payoff.

**Formalization Note** "(Aₜ) stated in (4.3)" points to the process of Proposition 4.6 (4.3 only
defines `Y`); `A` is the pathwise largest Carathéodory solution (`Model.Asol`, Remark 4.7).
Stopping times take values in `[0, ∞]`; `φ` is normalised at the reference point `c ∈ 𝓘`, which
changes no instance of Assumption 3.1. -/
theorem theorem_4_17 {Ω Θ₁ Θ₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ₁]
    [MeasurableSpace Θ₂] (G : Model Ω) (T : TypeSpace Θ₁ Θ₂) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) (hT : T.IsComplete) (hF : T.HasCDF G.F) :
    ∀ x ∈ G.I, G.IsNash T x (fun ω => G.tauHat α x ω.1 (T.θ₁ ω.2.1))
      (fun ω => G.tauHat α x ω.1 (T.θ₂ ω.2.2)) := by sorry

end ExitGamePrivate
