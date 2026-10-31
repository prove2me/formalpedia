-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_5
-- name    : ExitGamePrivate.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:56.526991+00:00
-- url     : https://prove2.me/theorems/02a4bcc7-99c9-4871-9d0c-3154bec86c3c
-- title:
--   Lemma 4.5 — $(x,a)\mapsto\lambda(x,Y(a))$ is decreasing in $x$ and in $a$
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   The exit rate along the belief, $(x,a)\mapsto\lambda(x,Y(a))$ with $\lambda$ from (4.4) and $Y(a)=F^{-1}(e^{-a})$, is decreasing (non-strictly) in $x\in\mathcal I$ for each fixed $a\ge0$, and decreasing in $a\ge0$ for each fixed $x\in\mathcal I$.
--
--   Monotonicity of the right-hand side of (4.2) is what makes the maximal solution of the random ODE well behaved and monotone in its initial data.
--
--   Differences from the source:
--   - encoding: "decreasing in x and a" → AntitoneOn in x on 𝓘 for each a ≥ 0, and AntitoneOn in a on [0, ∞) for each x ∈ 𝓘; reason: the paper's "decreasing" is non-strict (p.5); the domain is 𝓘 × [0, ∞)
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: Assumption 4.1 with Assumption 2.2: the exit values have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U] → Assumption4_1: F continuous, strictly increasing on [θ_L, θ_U], F = 0 on (−∞, θ_L], F = 1 on [θ_U, ∞); reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there; the type spaces themselves do not occur in this statement
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.5, p.15

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.5** (arXiv:2210.01610v2, p.15). "The mapping (x, a) ↦ λ(x, Y(a)) is decreasing in x
and a."

"Decreasing" is non-strict (p.5): `x ↦ λ(x, Y(a))` is antitone on `𝓘` for each `a ≥ 0`, and
`a ↦ λ(x, Y(a))` is antitone on `[0, ∞)` for each `x ∈ 𝓘`; standing assumptions of §4. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) :
    (∀ a : ℝ, 0 ≤ a → AntitoneOn (fun x => G.lam α x (G.Y a)) G.I) ∧
      ∀ x ∈ G.I, AntitoneOn (fun a => G.lam α x (G.Y a)) (Ici 0) := by sorry

end ExitGamePrivate
