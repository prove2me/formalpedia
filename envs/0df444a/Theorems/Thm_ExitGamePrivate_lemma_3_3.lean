-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_3_3
-- name    : ExitGamePrivate.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:05.72522+00:00
-- url     : https://prove2.me/theorems/eecdeab2-c8d0-4ade-963e-0991e429b2a0
-- title:
--   Lemma 3.3 — the single-player problem is solved by the threshold rule $\tau^*_\theta=\inf\{t:X_t\le\alpha(\theta)\}$
-- statement:
--   Consider the single-player problem (3.1)–(3.2), in which the opponent never exits, under the setting of §2 and Assumptions 2.3, 2.4 and 3.1. Then:
--   1. for each $\theta\in[\theta_L,\theta_U]$ and each $x\in\mathcal I$, the first entry time
--   $$\tau^*_\theta=\inf\{t\ge0:X_t\le\alpha(\theta)\} \tag{3.5}$$
--   is an $(\mathcal F_t)$-stopping time that is optimal, $J(x,\tau;\theta)\le J(x,\tau^*_\theta;\theta)$ for every stopping time $\tau$, the value function is
--   $$u(x;\theta)=\begin{cases}a_\theta(\alpha(\theta))\,\varphi(x)+d(x), & x>\alpha(\theta),\\ \theta, & x\le\alpha(\theta),\end{cases} \tag{3.6}$$
--   and $u(x;\theta)>\theta$ for all $x>\alpha(\theta)$;
--   2. $\theta\mapsto u(x;\theta)$ is continuous on $[\theta_L,\theta_U]$ for each $x\in\mathcal I$;
--   3. $\alpha$ is continuous on $[\theta_L,\theta_U]$, and $\alpha(\theta)\le c(\theta)$ for every critical value $c(\theta)$ of Assumption 3.1(i).
--
--   Part 1 is Alvarez's characterisation of exit from a declining market (cited as [1, Thm. 3]). The threshold $\alpha$ is the exit level of the equilibrium, and $\alpha\le c$ makes the exit rate $\lambda$ non-negative.
--
--   Differences from the source:
--   - reading: "the optimal policy is to exit at τ*_θ" → τ*_θ is an (Fₜ)-stopping time and J(x, τ; θ) ≤ J(x, τ*_θ; θ) for every (Fₜ)-stopping time τ and every x ∈ 𝓘; reason: this is optimality in (3.2)
--   - reading: α(θ) ≤ c(θ) for the critical value c(θ) → α(θ) ≤ c(θ) for every c(θ) ∈ 𝓘 ∪ {x_U} satisfying Assumption 3.1(i), as an element of EReal; reason: Assumption 3.1(i) asserts existence of c(θ) without uniqueness; the claim holds for each
--   - encoding: u(x; θ) continuous in θ → ContinuousOn in θ on [θ_L, θ_U] for each x ∈ 𝓘; reason: θ ranges over the support
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: stopping times τ, discount e^{−rτ}, integrals ∫_0^τ → WithTop ℝ≥0-valued stopping times (Mathlib IsStoppingTime), disc r ⊤ = 0, set integrals over the window [0, τ); reason: same values; τ = ∞ is allowed and pays e^{−r·∞} = 0 as in the paper
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 3.3, p.9 ((3.5), (3.6)); part (i) cited from Alvarez (2001), Thm. 3

import Mathlib
import Definitions.Def_ExitGamePrivate_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 3.3** (arXiv:2210.01610v2, p.9; part (i) is cited from Alvarez 2001, Thm. 3).
"Under Assumptions 2.3, 2.4 and 3.1, we have: (i) for each θ ∈ [θ_L, θ_U], the optimal policy is
to exit at the stopping time (3.5) τ*_θ = inf{t ≥ 0 : Xₜ ≤ α(θ)}, where α(θ) is defined in
Assumption 3.1. Furthermore, u(x; θ) is given by (3.6) u(x; θ) = a_θ(α(θ))φ(x) + d(x) for
x > α(θ), θ for x ≤ α(θ), and u(x; θ) > θ for all x > α(θ). (ii) u(x; θ) is continuous in θ.
(iii) Function α is continuous and α(θ) ≤ c(θ)."

**Formalization Note** "Optimal policy" is: `τ*_θ` is an `(Fₜ)`-stopping time and
`J(x, τ; θ) ≤ J(x, τ*_θ; θ)` for every `(Fₜ)`-stopping time `τ` and every `x ∈ 𝓘`. In (iii),
`α(θ) ≤ c(θ)` holds for every critical value `c(θ)` of Assumption 3.1(i). `φ` is normalised at
`c ∈ 𝓘`; (3.6) does not depend on the normalisation. -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hreg : G.IsRegular) (hc : c ∈ G.I) (h23 : G.Assumption2_3) (h31 : G.Assumption3_1 c α) :
    (∀ θ ∈ Icc G.θL G.θU, ∀ x ∈ G.I,
      IsStoppingTime G.filt (hittingAfter (fun (t : ℝ≥0) ω => G.X x (t : ℝ) ω) (Iic (α θ)) 0) ∧
      (∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime G.filt τ →
        G.Jsp x τ θ ≤
          G.Jsp x (hittingAfter (fun (t : ℝ≥0) ω => G.X x (t : ℝ) ω) (Iic (α θ)) 0) θ) ∧
      G.u x θ = (if α θ < x then G.a c θ (α θ) * G.phi G.r c x + G.d x else θ) ∧
      (α θ < x → θ < G.u x θ)) ∧
    (∀ x ∈ G.I, ContinuousOn (fun θ => G.u x θ) (Icc G.θL G.θU)) ∧
    (ContinuousOn α (Icc G.θL G.θU) ∧
      ∀ θ ∈ Icc G.θL G.θU, ∀ cθ : EReal, G.IsCritical θ cθ → ((α θ : ℝ) : EReal) ≤ cθ) := by sorry

end ExitGamePrivate
