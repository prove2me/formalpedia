-- Prove2me | Theorems.Thm_ExitGamePrivate_corollary_2_8
-- name    : ExitGamePrivate.corollary_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:58.572525+00:00
-- url     : https://prove2.me/theorems/8ba547df-50d7-473a-bd83-7473ccfbb12b
-- title:
--   Corollary 2.8 — type-wise best responses against each other form a Nash equilibrium
-- statement:
--   Let the setting of §2 and Assumptions 2.2–2.4 hold, and fix an initial state $x\in\mathcal I$. Let $\hat\tau_1,\hat\tau_2$ be admissible type-indexed stopping times as in Proposition 2.7 and put $\tau_1=\hat\tau_1(\cdot,\theta_1)$, $\tau_2=\hat\tau_2(\cdot,\theta_2)$. If for each $\theta\in[\theta_L,\theta_U]$
--   $$\hat\tau_1(\cdot,\theta)\in\operatorname*{arg\,max}_{\sigma\in\mathcal T(\mathcal F_t)}J(x,\sigma,\tau_2;\theta)\quad\text{and}\quad\hat\tau_2(\cdot,\theta)\in\operatorname*{arg\,max}_{\sigma\in\mathcal T(\mathcal F_t)}J(x,\sigma,\tau_1;\theta),$$
--   with $J$ the payoff (2.3) for a deterministic exit value, then $(\tau_1,\tau_2)$ is a Nash equilibrium for $x$ (Definition 2.6).
--
--   This is the sufficient condition used to prove Theorem 4.17: it suffices to solve one optimal stopping problem per type.
--
--   Differences from the source:
--   - generalization: τ̂ takes values in [0, ∞) → τ̂ takes values in [0, ∞] (WithTop ℝ≥0); reason: a [0, ∞)-valued τ̂ is a special case; the paper applies the result to τ̂(·, θ) = inf{t : Y(Aₜ) < θ}, which is ∞ for θ = θ_L (proof of Theorem 4.17, p.22)
--   - encoding: τ̂ : Ω × [θ_L, θ_U] → [0, ∞) is F ⊗ 𝓑([θ_L, θ_U])-measurable and τ = τ̂(·, θᵢ) → τ̂ : Ω × ℝ → [0, ∞] jointly measurable with τ̂(·, θ) a stopping time for θ ∈ [θ_L, θ_U], read at clampθ θ_L θ_U θᵢ = max θ_L (min θ_U θᵢ); reason: every measurable map on Ω × [θ_L, θ_U] extends to Ω × ℝ through the clamp; clampθ θᵢ = θᵢ whenever θᵢ ∈ [θ_L, θ_U], i.e. almost surely, and only sections at θ ∈ [θ_L, θ_U] are read
--   - reading: "Let Assumption 2.2 hold" → Assumptions 2.2, 2.3 and 2.4 together with the §2 setting; reason: Assumptions 2.3–2.4 are made for the whole paper on p.6, before Definition 2.6; they make the payoffs finite
--   - encoding: x an initial value → x ∈ 𝓘 as a hypothesis; reason: Eₓ is defined for initial states in 𝓘
--   - encoding: τ̂₁(·, θ) ∈ arg max_{σ∈𝒯(Fₜ)} J(x, σ, τ₂; θ) → τ̂₁(·, θ) is an (Fₜ)-stopping time (part of admissibility) and J(x, σ, τ₂; θ) ≤ J(x, τ̂₁(·, θ), τ₂; θ) for every (Fₜ)-stopping time σ; reason: the definition of arg max over 𝒯(Fₜ)
--   - encoding: Nash equilibrium with "P̃ₓ-a.s." inequalities (Definition 2.6) → plain inequalities between the real payoffs; reason: both sides are expectations
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: types θᵢ on complete probability spaces, product space (2.2), Fⁱₜ = F̃ₜ ∨ σ(θᵢ), Assumption 2.2 (θᵢ have support [θ_L, θ_U]) → TypeSpace with complete probability measures and measurable θᵢ; HasSupport: θᵢ ∈ [θ_L, θ_U] a.s. and every neighbourhood of a point of [θ_L, θ_U] has positive probability; filtrations built as comap σ-algebras on Ω × Θ₁ × Θ₂; reason: this is the topological support of the law of θᵢ being [θ_L, θ_U]
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Corollary 2.8, p.7

import Mathlib
import Definitions.Def_ExitGamePrivate_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Corollary 2.8** (arXiv:2210.01610v2, p.7). "Let Assumption 2.2 hold and assume that
τ̂₁, τ̂₂ : Ω × [θ_L, θ_U] → [0, ∞) are as in Proposition 2.7. Define τ₁ = τ̂₁(·, θ₁) and
τ₂ = τ̂₂(·, θ₂). If for each θ ∈ [θ_L, θ_U] we have τ̂₁(·, θ) ∈ arg max_{σ∈𝒯(Fₜ)} J(x, σ, τ₂; θ)
and τ̂₂(·, θ) ∈ arg max_{σ∈𝒯(Fₜ)} J(x, σ, τ₁; θ) then (τ₁, τ₂) is a Nash equilibrium."

Under the setting of §2 and the standing Assumptions 2.3–2.4 (p.6), for an initial state
`x ∈ 𝓘`.

**Formalization Note** `J` is (2.3) (`Model.Jgam`). `τ̂ᵢ` take values in `[0, ∞]` (a
`[0, ∞)`-valued map is a special case) and are read at `clampθ θ_L θ_U θᵢ` (see Proposition
2.7). "`τ̂₁(·, θ) ∈ arg max`" is: `τ̂₁(·, θ)` is an `(Fₜ)`-stopping time (part of being as in
Proposition 2.7) whose value is at least that of every `(Fₜ)`-stopping time. -/
theorem corollary_2_8 {Ω Θ₁ Θ₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ₁]
    [MeasurableSpace Θ₂] (G : Model Ω) (T : TypeSpace Θ₁ Θ₂)
    (hreg : G.IsRegular) (h23 : G.Assumption2_3) (hT : T.IsComplete)
    (hS : T.HasSupport G.θL G.θU) (x : ℝ) (hx : x ∈ G.I)
    (τh₁ τh₂ : Ω → ℝ → WithTop ℝ≥0)
    (h₁ : IsTypedStopping G.toDiffusion G.θL G.θU τh₁)
    (h₂ : IsTypedStopping G.toDiffusion G.θL G.θU τh₂)
    (hbr₁ : ∀ θ ∈ Icc G.θL G.θU, ∀ σ : Ω → WithTop ℝ≥0, IsStoppingTime G.filt σ →
      G.Jgam T x σ (fun ω => τh₂ ω.1 (clampθ G.θL G.θU (T.θ₂ ω.2.2))) θ ≤
        G.Jgam T x (fun ω => τh₁ ω θ) (fun ω => τh₂ ω.1 (clampθ G.θL G.θU (T.θ₂ ω.2.2))) θ)
    (hbr₂ : ∀ θ ∈ Icc G.θL G.θU, ∀ σ : Ω → WithTop ℝ≥0, IsStoppingTime G.filt σ →
      G.Jgam T x σ (fun ω => τh₁ ω.1 (clampθ G.θL G.θU (T.θ₁ ω.2.1))) θ ≤
        G.Jgam T x (fun ω => τh₂ ω θ) (fun ω => τh₁ ω.1 (clampθ G.θL G.θU (T.θ₁ ω.2.1))) θ) :
    G.IsNash T x (fun ω => τh₁ ω.1 (clampθ G.θL G.θU (T.θ₁ ω.2.1)))
      (fun ω => τh₂ ω.1 (clampθ G.θL G.θU (T.θ₂ ω.2.2))) := by sorry

end ExitGamePrivate
