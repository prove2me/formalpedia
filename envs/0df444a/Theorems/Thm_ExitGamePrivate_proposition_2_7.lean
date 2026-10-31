-- Prove2me | Theorems.Thm_ExitGamePrivate_proposition_2_7
-- name    : ExitGamePrivate.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:56.303242+00:00
-- url     : https://prove2.me/theorems/23cb4b6f-31c4-41b4-b2b2-a81b75df5113
-- title:
--   Proposition 2.7 — $(\mathcal F^i_t)$-stopping times are exactly $\hat\tau(\cdot,\theta_i)$ for type-indexed $(\mathcal F_t)$-stopping times
-- statement:
--   Let the setting of §2 hold and let the exit values $\theta_1,\theta_2$ have support $[\theta_L,\theta_U]$ (Assumption 2.2). Call $\hat\tau:\Omega\times[\theta_L,\theta_U]\to[0,\infty]$ **admissible** if it is $\mathcal F\otimes\mathcal B$-measurable and $\hat\tau(\cdot,\theta)$ is an $(\mathcal F_t)$-stopping time for each $\theta\in[\theta_L,\theta_U]$. Then, for each player $i=1,2$:
--   1. if $\hat\tau$ is admissible, $\tau=\hat\tau(\cdot,\theta_i)$ is an $(\mathcal F^i_t)$-stopping time on $\tilde\Omega$;
--   2. conversely, for every $(\mathcal F^i_t)$-stopping time $\tau$ there is an admissible $\hat\tau$ with
--   $$\tau=\hat\tau(\cdot,\theta_i)\qquad \tilde P\text{-a.s.}$$
--   If $\tau$ is finite, $\hat\tau$ can be chosen finite on $\Omega\times[\theta_L,\theta_U]$.
--
--   A player's information consists of the public filtration plus his own type, so a strategy is a family of public stopping rules indexed by the type. This is what reduces the Nash property to type-by-type best responses (Corollary 2.8).
--
--   Differences from the source:
--   - generalization: τ̂ takes values in [0, ∞) → τ̂ takes values in [0, ∞] (WithTop ℝ≥0); reason: a [0, ∞)-valued τ̂ is a special case; the paper applies the result to τ̂(·, θ) = inf{t : Y(Aₜ) < θ}, which is ∞ for θ = θ_L (proof of Theorem 4.17, p.22)
--   - generalization: the converse for (Fⁱₜ)-stopping times τ, with a [0, ∞)-valued τ̂ → the converse for every [0, ∞]-valued (Fⁱₜ)-stopping time τ, with a [0, ∞]-valued τ̂, which is finite on Ω × [θ_L, θ_U] whenever τ is finite everywhere; reason: for a finite τ this is the paper's claim; the paper also applies it to stopping times that take the value ∞ (Theorem 4.17, p.22)
--   - encoding: τ̂ : Ω × [θ_L, θ_U] → [0, ∞) is F ⊗ 𝓑([θ_L, θ_U])-measurable and τ = τ̂(·, θᵢ) → τ̂ : Ω × ℝ → [0, ∞] jointly measurable with τ̂(·, θ) a stopping time for θ ∈ [θ_L, θ_U], read at clampθ θ_L θ_U θᵢ = max θ_L (min θ_U θᵢ); reason: every measurable map on Ω × [θ_L, θ_U] extends to Ω × ℝ through the clamp; clampθ θᵢ = θᵢ whenever θᵢ ∈ [θ_L, θ_U], i.e. almost surely, and only sections at θ ∈ [θ_L, θ_U] are read
--   - reading: "τ = τ̂(·, θᵢ), P-a.s." for a random time on Ω̃ → almost surely with respect to the product measure P̃; reason: τ and τ̂(·, θᵢ) live on Ω̃, where the measure is P̃
--   - encoding: the statement for a generic player i → both players stated, as a conjunction; reason: same content
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: types θᵢ on complete probability spaces, product space (2.2), Fⁱₜ = F̃ₜ ∨ σ(θᵢ), Assumption 2.2 (θᵢ have support [θ_L, θ_U]) → TypeSpace with complete probability measures and measurable θᵢ; HasSupport: θᵢ ∈ [θ_L, θ_U] a.s. and every neighbourhood of a point of [θ_L, θ_U] has positive probability; filtrations built as comap σ-algebras on Ω × Θ₁ × Θ₂; reason: this is the topological support of the law of θᵢ being [θ_L, θ_U]
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Proposition 2.7, p.7

import Mathlib
import Definitions.Def_ExitGamePrivate_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Proposition 2.7** (arXiv:2210.01610v2, p.7). "Let Assumption 2.2 hold. If
τ̂ : (Ω, F) ⊗ ([θ_L, θ_U], 𝓑([θ_L, θ_U])) → ([0, ∞), 𝓑([0, ∞))) is measurable and the mapping
τ̂(·, θ) : Ω → [0, ∞) is an (Fₜ)-stopping time for each θ ∈ [θ_L, θ_U], then τ = τ̂(·, θᵢ) is an
(Fⁱₜ)-stopping time. Conversely, for every (Fⁱₜ)-stopping time τ there is a mapping τ̂ satisfying
the above conditions such that τ = τ̂(·, θᵢ), P-a.s."

Stated for both players `i = 1, 2`.

**Formalization Note** `τ̂` takes values in `[0, ∞]` (the paper's own use of the proposition in
the proof of Theorem 4.17 needs the value `∞`); a `[0, ∞)`-valued `τ̂` is a special case. In the
converse, a finite `τ` gets a `τ̂` that is finite on `Ω × [θ_L, θ_U]`, which is the paper's claim
for `[0, ∞)`-valued stopping times. `τ̂` is read at `clampθ θ_L θ_U θᵢ`, which equals `θᵢ`
whenever `θᵢ ∈ [θ_L, θ_U]` (almost surely), so that only the sections `θ ∈ [θ_L, θ_U]` of `τ̂`
enter, as in the paper. "P-a.s." is with respect to the
product measure `P̃`. -/
theorem proposition_2_7 {Ω Θ₁ Θ₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ₁]
    [MeasurableSpace Θ₂] (Dif : Diffusion Ω) (T : TypeSpace Θ₁ Θ₂) (θL θU : ℝ)
    (hDif : Dif.IsRegular) (hT : T.IsComplete) (hS : T.HasSupport θL θU) :
    ((∀ τh : Ω → ℝ → WithTop ℝ≥0, IsTypedStopping Dif θL θU τh →
        IsStoppingTime (filt₁ Dif T) (fun ω => τh ω.1 (clampθ θL θU (T.θ₁ ω.2.1)))) ∧
      (∀ τ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0, IsStoppingTime (filt₁ Dif T) τ →
        ∃ τh : Ω → ℝ → WithTop ℝ≥0, IsTypedStopping Dif θL θU τh ∧
          ((∀ ω, τ ω ≠ ⊤) → ∀ ω, ∀ θ ∈ Icc θL θU, τh ω θ ≠ ⊤) ∧
          ∀ᵐ ω ∂(Ptil Dif T), τ ω = τh ω.1 (clampθ θL θU (T.θ₁ ω.2.1)))) ∧
    ((∀ τh : Ω → ℝ → WithTop ℝ≥0, IsTypedStopping Dif θL θU τh →
        IsStoppingTime (filt₂ Dif T) (fun ω => τh ω.1 (clampθ θL θU (T.θ₂ ω.2.2)))) ∧
      (∀ τ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0, IsStoppingTime (filt₂ Dif T) τ →
        ∃ τh : Ω → ℝ → WithTop ℝ≥0, IsTypedStopping Dif θL θU τh ∧
          ((∀ ω, τ ω ≠ ⊤) → ∀ ω, ∀ θ ∈ Icc θL θU, τh ω θ ≠ ⊤) ∧
          ∀ᵐ ω ∂(Ptil Dif T), τ ω = τh ω.1 (clampθ θL θU (T.θ₂ ω.2.2)))) := by sorry

end ExitGamePrivate
