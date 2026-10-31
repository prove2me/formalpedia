-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_13
-- name    : ExitGamePrivate.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:38.571686+00:00
-- url     : https://prove2.me/theorems/decf0b89-3406-4b18-a650-d66d779f0c76
-- title:
--   Lemma 4.13 — $\tilde v(x,a;\theta)>0$ when $x<\alpha(Y(a))$ and $a<A(\theta)$
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   For every $\theta\in[\theta_L,\theta_U]$ and every $(x,a)\in\mathcal I\times[0,\infty)$ with $x<\alpha(Y(a))$ and $a<A(\theta)$, where $A(\theta)=-\log F(\theta)$ ($A(\theta_L)=\infty$),
--   $$\tilde v(x,a;\theta)>0.$$
--
--   While higher types than $\theta$ are still in the game and the state is below their threshold, a type-$\theta$ player strictly prefers to wait for them to exit.
--
--   Differences from the source:
--   - encoding: A(θ) = −log F(θ) for θ ∈ (θ_L, θ_U], A(θ_L) = ∞ (4.5) → Acum θ ∈ EReal (⊤ for θ ≤ θ_L); comparisons with a ∈ ℝ through the coercion ℝ → EReal; reason: the value ∞ at θ_L is representable; only order comparisons are used, no EReal arithmetic
--   - reading: the process (Aₜ) of Proposition 4.6, constructed as A⁰ = lim_{ε↓0} A^ε from (4.35)–(4.36) (p.26), with A^{x,a} its version started at (x, a) (p.16) → Model.Asol α x a: the pathwise supremum of all Carathéodory solutions of (4.13) along Xˣ(ω) started at a (the largest solution); reason: the paper identifies A⁰ as the largest Carathéodory solution (Remark 4.7, p.16; p.32); every solution lies below each A^ε by comparison and A⁰ solves (4.13) a.s., so the two agree a.s.; (4.35) itself needs α^{−1} outside [α(θ_L), α(θ_U)], where it is undefined
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: Assumption 4.1 with Assumption 2.2: the exit values have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U] → Assumption4_1: F continuous, strictly increasing on [θ_L, θ_U], F = 0 on (−∞, θ_L], F = 1 on [θ_U, ∞); reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there; the type spaces themselves do not occur in this statement
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.13, p.18

import Mathlib
import Definitions.Def_ExitGamePrivate_BestResponse

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.13** (arXiv:2210.01610v2, p.18). "ṽ(x, a; θ) > 0 for (x, a) ∈ 𝓘 × [0, ∞) such that
x < α(Y(a)) and a < A(θ)."

For `θ ∈ [θ_L, θ_U]`, under the standing assumptions of §4; `A(θ) = Acum θ ∈ (−∞, ∞]`
(`A(θ_L) = ∞`). -/
theorem lemma_4_13 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) (θ : ℝ) (hθ : θ ∈ Icc G.θL G.θU) :
    ∀ x ∈ G.I, ∀ a : ℝ, 0 ≤ a → x < α (G.Y a) → (a : EReal) < G.Acum θ →
      0 < G.vtil α x a θ := by sorry

end ExitGamePrivate
