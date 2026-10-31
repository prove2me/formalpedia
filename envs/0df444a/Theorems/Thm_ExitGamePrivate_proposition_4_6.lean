-- Prove2me | Theorems.Thm_ExitGamePrivate_proposition_4_6
-- name    : ExitGamePrivate.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:29.932232+00:00
-- url     : https://prove2.me/theorems/67351a77-c74b-4d85-9faf-e71574af88d1
-- title:
--   Proposition 4.6 — $(X,A)$ is strong Markov and $A$ is a continuous Carathéodory solution of (4.13)
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   For $x\in\mathcal I$ and $a\ge0$ let $A^{x,a}$ be the largest Carathéodory solution of (4.13) along $X^x$ started at $a$. Then:
--   1. $A^{x,a}$ is $(\mathcal F_t)$-adapted and, almost surely, it is continuous on $[0,\infty)$ and satisfies
--   $$A_t=A_0+\int_0^t\lambda\big(X_s,Y(A_s)\big)\,ds\quad\text{for all }t\ge0,\qquad A_0=a; \tag{4.13}$$
--   2. the family $(X^x,A^{x,a})$ is strong Markov: for every $(\mathcal F_t)$-stopping time $\sigma$ and every bounded measurable functional $\Phi$ of paths $\mathbb R_{\ge0}\to\mathbb R^2$,
--   $$E\big[1_{\{\sigma<\infty\}}\Phi\big((X,A)_{\sigma+\cdot}\big)\,\big|\,\mathcal F_\sigma\big]=1_{\{\sigma<\infty\}}\,g(X_\sigma,A_\sigma)\quad\text{a.s.},\qquad g(y,b)=E\big[\Phi\big((X^y,A^{y,b})\big)\big].$$
--
--   The random ODE $dA_t=\lambda(X_t,Y(A_t))dt$ has a right-hand side that is discontinuous along $x=\alpha(y)$, so classical ODE theory gives no solution; this proposition supplies the process on which the equilibrium is built.
--
--   Differences from the source:
--   - reading: the process (Aₜ) of Proposition 4.6, constructed as A⁰ = lim_{ε↓0} A^ε from (4.35)–(4.36) (p.26), with A^{x,a} its version started at (x, a) (p.16) → Model.Asol α x a: the pathwise supremum of all Carathéodory solutions of (4.13) along Xˣ(ω) started at a (the largest solution); reason: the paper identifies A⁰ as the largest Carathéodory solution (Remark 4.7, p.16; p.32); every solution lies below each A^ε by comparison and A⁰ solves (4.13) a.s., so the two agree a.s.; (4.35) itself needs α^{−1} outside [α(θ_L), α(θ_U)], where it is undefined
--   - reading: "There is a strong Markov process (Xₜ, Aₜ)" → the family (Xˣ, A^{x,a}) indexed by (x, a) ∈ 𝓘 × [0, ∞), with the strong Markov property stated as the conditional-expectation identity at every (Fₜ)-stopping time for bounded measurable path functionals; reason: the paper indexes the process by its initial point (p.16) and uses the strong Markov property at stopping times (Lemma 4.16, Proposition 4.10)
--   - encoding: (4.13) holds for t ≥ 0, Pₓ-a.s.; continuity → almost surely, IsCaratheodory: continuity on [0, ∞), local integrability of the integrand and (4.13) for all t ≥ 0 simultaneously; adaptedness at each t ≥ 0; reason: a Carathéodory solution has an integrable right-hand side; all t at once is the paper's continuous-process reading
--   - encoding: F_σ, path space → IsStoppingTime.measurableSpace; the product σ-algebra on ℝ≥0 → ℝ × ℝ; reason: standard
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: Assumption 4.1 with Assumption 2.2: the exit values have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U] → Assumption4_1: F continuous, strictly increasing on [θ_L, θ_U], F = 0 on (−∞, θ_L], F = 1 on [θ_U, ∞); reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there; the type spaces themselves do not occur in this statement
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Proposition 4.6, p.15 ((4.13)); construction in its proof, p.26; Remark 4.7, p.16

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Proposition 4.6** (arXiv:2210.01610v2, p.15). "There is a strong Markov process
(Xₜ, Aₜ)ₜ≥₀ such that (Xₜ) solves (2.1) and (Aₜ) is a continuous process which satisfies (4.13)
Aₜ = A₀ + ∫_0^t λ(X_s, Y(A_s)) ds, t ≥ 0, Pₓ − a.s. i.e., it is a Carathéodory solution to
(4.2)."

For `A = A^{x,a}` the largest Carathéodory solution along `Xˣ` from `A₀ = a` (`Model.Asol`), for
every `x ∈ 𝓘` and `a ≥ 0`: (a) `A` is `(Fₜ)`-adapted and, almost surely, continuous on `[0, ∞)`
and satisfies (4.13) for all `t ≥ 0` simultaneously; (b) the family `(Xˣ, A^{x,a})` is strong
Markov: for every `(Fₜ)`-stopping time `σ` and every bounded measurable functional `Φ` of paths
`ℝ≥0 → ℝ × ℝ`,
`E[1_{σ<∞} Φ((X, A)_{σ+·}) | F_σ] = 1_{σ<∞} g(X_σ, A_σ)` a.s., `g(y, b) = E[Φ((X^y, A^{y,b}))]`.

**Formalization Note** The paper's "there is" is answered by the maximal solution, which is the
process the paper constructs (Remark 4.7). `F_σ` is Mathlib's `IsStoppingTime.measurableSpace`;
the path space carries the product σ-algebra. -/
theorem proposition_4_6 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) :
    ∀ x ∈ G.I, ∀ a : ℝ, 0 ≤ a →
      ((∀ t : ℝ, 0 ≤ t → Measurable[G.𝔽 t] (G.Asol α x a t)) ∧
        ∀ᵐ ω ∂G.P, G.IsCaratheodory α x a ω (fun t => G.Asol α x a t ω)) ∧
      ∀ (σ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime G.filt σ) (Φ : (ℝ≥0 → ℝ × ℝ) → ℝ),
        Measurable Φ → (∃ C : ℝ, ∀ z, |Φ z| ≤ C) →
        G.P[{ω | σ ω < ⊤}.indicator (fun ω =>
            Φ (fun t => (G.X x ((((σ ω).untopD 0 : ℝ≥0) : ℝ) + t) ω,
              G.Asol α x a ((((σ ω).untopD 0 : ℝ≥0) : ℝ) + t) ω))) | hσ.measurableSpace]
          =ᵐ[G.P] {ω | σ ω < ⊤}.indicator (fun ω =>
            ∫ ω', Φ (fun t =>
              (G.X (G.X x (((σ ω).untopD 0 : ℝ≥0) : ℝ) ω) t ω',
                G.Asol α (G.X x (((σ ω).untopD 0 : ℝ≥0) : ℝ) ω)
                  (G.Asol α x a (((σ ω).untopD 0 : ℝ≥0) : ℝ) ω) t ω')) ∂G.P) := by sorry

end ExitGamePrivate
