-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_8
-- name    : ExitGamePrivate.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:34.9331+00:00
-- url     : https://prove2.me/theorems/40a86544-0eb6-43ff-a4cc-7ea823c46993
-- title:
--   Lemma 4.8 — $A^{x,a}$ is increasing and 1-Lipschitz in $a$, decreasing and sequentially continuous in $x$
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   Write $A^{x,a}$ for the largest Carathéodory solution of (4.13) along $X^x$ started at $a$.
--   1. For $x\in\mathcal I$ and $0\le a\le a'$: almost surely $A^{x,a}_t\le A^{x,a'}_t$ for all $t\ge0$.
--   2. For $x\in\mathcal I$ and $a,a'\ge0$: almost surely
--   $$|A^{x,a}_t-A^{x,a'}_t|\le|a-a'|,\qquad t\ge0.$$
--   3. For $a\ge0$ and $x\le x'$ in $\mathcal I$: almost surely $A^{x',a}_t\le A^{x,a}_t$ for all $t\ge0$.
--   4. For $a\ge0$, $T>0$, $x_0\in\mathcal I$ and $x_n\to x_0$ in $\mathcal I$: outside a $P$-null set, $A^{x_n,a}\to A^{x_0,a}$ in the supremum norm $\|Z\|_T=\sup_{t\in[0,T]}|Z_t|$.
--
--   The Lipschitz dependence on $a$ is what yields the continuity of the best-response value function (Proposition 4.10).
--
--   Differences from the source:
--   - reading: the process (Aₜ) of Proposition 4.6, constructed as A⁰ = lim_{ε↓0} A^ε from (4.35)–(4.36) (p.26), with A^{x,a} its version started at (x, a) (p.16) → Model.Asol α x a: the pathwise supremum of all Carathéodory solutions of (4.13) along Xˣ(ω) started at a (the largest solution); reason: the paper identifies A⁰ as the largest Carathéodory solution (Remark 4.7, p.16; p.32); every solution lies below each A^ε by comparison and A⁰ solves (4.13) a.s., so the two agree a.s.; (4.35) itself needs α^{−1} outside [α(θ_L), α(θ_U)], where it is undefined
--   - reading: "the mapping a ↦ A^{x,a}_t is increasing", "|A^a_t − A^{a′}_t| ≤ |a − a′|", "x ↦ A^{x,a}_t is decreasing" (pathwise) → almost surely, for each pair of initial points, for all t ≥ 0; reason: for the maximal solution these properties hold on the full-measure set where it coincides with the paper's A⁰, which depends on the initial point
--   - encoding: convergence in ‖Z‖_T = sup_{t∈[0,T]} |Z_t| → TendstoUniformlyOn on [0, T]; reason: uniform convergence on [0, T] is convergence in ‖·‖_T
--   - encoding: x₀ ∈ 𝓘 and xₙ → x₀ → xₙ ∈ 𝓘 for all n; reason: Xˣ is only defined for initial points in 𝓘
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: Assumption 4.1 with Assumption 2.2: the exit values have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U] → Assumption4_1: F continuous, strictly increasing on [θ_L, θ_U], F = 0 on (−∞, θ_L], F = 1 on [θ_U, ∞); reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there; the type spaces themselves do not occur in this statement
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.8, p.16

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.8** (arXiv:2210.01610v2, p.16). "For any x ∈ 𝓘, the mapping a ↦ A^{x,a}_t =: A^a_t
is increasing and for a, a′ ≥ 0 |A^a_t − A^{a′}_t| ≤ |a − a′|, t ≥ 0. For any a ≥ 0, the mapping
x ↦ A^{x,a}_t is decreasing and sequentially continuous in the following sense: for every T > 0,
x₀ ∈ 𝓘 and xₙ → x₀, there is a P-negligible subset of Ω outside of which A^{xₙ,a}_t converges to
A^{x₀,a}_t in the supremum norm ‖Z‖_T = sup_{t∈[0,T]} |Z_t|."

**Formalization Note** `A^{x,a} = Model.Asol α x a` is the largest Carathéodory solution, which
is the paper's process almost surely; the pathwise monotonicity and Lipschitz claims are stated
almost surely, for each pair of initial points. Convergence in `‖·‖_T` is uniform convergence on
`[0, T]`. Standing assumptions of §4. -/
theorem lemma_4_8 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) :
    (∀ x ∈ G.I,
      (∀ a a' : ℝ, 0 ≤ a → a ≤ a' →
        ∀ᵐ ω ∂G.P, ∀ t : ℝ, 0 ≤ t → G.Asol α x a t ω ≤ G.Asol α x a' t ω) ∧
      (∀ a a' : ℝ, 0 ≤ a → 0 ≤ a' →
        ∀ᵐ ω ∂G.P, ∀ t : ℝ, 0 ≤ t → |G.Asol α x a t ω - G.Asol α x a' t ω| ≤ |a - a'|)) ∧
    (∀ a : ℝ, 0 ≤ a →
      (∀ x ∈ G.I, ∀ x' ∈ G.I, x ≤ x' →
        ∀ᵐ ω ∂G.P, ∀ t : ℝ, 0 ≤ t → G.Asol α x' a t ω ≤ G.Asol α x a t ω) ∧
      (∀ T : ℝ, 0 < T → ∀ x₀ ∈ G.I, ∀ xs : ℕ → ℝ, (∀ n, xs n ∈ G.I) →
        Tendsto xs atTop (𝓝 x₀) →
        ∀ᵐ ω ∂G.P, TendstoUniformlyOn (fun n t => G.Asol α (xs n) a t ω)
          (fun t => G.Asol α x₀ a t ω) atTop (Icc 0 T))) := by sorry

end ExitGamePrivate
