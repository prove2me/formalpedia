-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_4
-- name    : ExitGamePrivate.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:15.483393+00:00
-- url     : https://prove2.me/theorems/a8ef5f66-9247-4d39-b83b-6e5ade0a14bb
-- title:
--   Lemma 4.4 — $y\mapsto l(x,y)$ is strictly increasing for $x\le\alpha(\theta_U)$, with the derivative bound (4.12)
-- statement:
--   Throughout, $X^x$ is the diffusion (2.1) started at $x\in\mathcal I=(x_L,x_U)$, and the setting of §2 together with Assumptions 2.3, 2.4, 3.1 and 4.1 is in force (the standing assumptions of §4).
--
--   Let $m_{\min}=\inf_{x\in\mathcal I}m(x)$. For every $x\in\mathcal I$ with $x\le\alpha(\theta_U)$, the map
--   $$[\theta_L,\theta_U]\ni y\mapsto l(x,y)=\frac{ry-D(x)}{m(x)-y}$$
--   is strictly increasing, and at every $y\in[\theta_L,\theta_U]$ it has the derivative
--   $$0<\frac{rm(x)-D(x)}{(m(x)-y)^2}\le\frac{r\,m_{\min}}{(m_{\min}-\theta_U)^2}. \tag{4.12}$$
--
--   The uniform bound makes the exit rate Lipschitz in the belief variable, which drives the comparison and continuity arguments for $A$.
--
--   Differences from the source:
--   - encoding: x ≤ α(θ_U); "with the derivative" → x ∈ 𝓘 with x ≤ α(θ_U); HasDerivAt (l x) at every y ∈ [θ_L, θ_U] (a two-sided derivative, which exists since m(x) > θ_U ≥ y); reason: l(x, ·) is only defined for x ∈ 𝓘; the two-sided derivative restricts to the interval
--   - encoding: m_min = inf_{x∈𝓘} m(x) → sInf (m '' 𝓘); reason: m '' 𝓘 is nonempty and bounded below by 0
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
--   - encoding: φ is the decreasing fundamental solution of (𝓛_X − r)φ = 0 with 𝓛_X = ½σ²(x)∂² + µ(x)∂ (p.8) → φ_c(x) = Eₓ[e^{−rH_c}] for x ≥ c and 1/E_c[e^{−rH_x}] for x < c (H_y the hitting time of y), with a reference point c ∈ 𝓘 as a parameter; reason: φ is determined only up to a positive factor (Borodin–Salminen II.10); Assumption 3.1 and (3.6) depend on φ only through quantities invariant under that factor; σ² in (3.3) is b², and no generator appears in the Lean
--   - encoding: α(θ) is defined in Assumption 3.1(ii) as the unique maximiser of a_θ → α is an argument constrained by Assumption3_1: on [θ_L, θ_U] it is the unique maximiser of a_θ; reason: the constraint determines α on [θ_L, θ_U], the only values that enter
--   - encoding: Assumption 2.3: D, M : 𝓘 → [0, ∞) continuous, increasing, bounded, M > D, inf_{x∈𝓘} m(x) > θ_U, r > 0 (p.6) → Assumption2_3 with the infimum condition written as ∃ κ > θ_U with m ≥ κ on 𝓘; reason: equivalent conditions; avoids a real sInf
--   - encoding: Assumption 4.1 with Assumption 2.2: the exit values have the common CDF F, continuous and strictly increasing on the support [θ_L, θ_U] → Assumption4_1: F continuous, strictly increasing on [θ_L, θ_U], F = 0 on (−∞, θ_L], F = 1 on [θ_U, ∞); reason: these are exactly the CDFs of continuous laws with support [θ_L, θ_U] that are strictly increasing there; the type spaces themselves do not occur in this statement
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.4, p.15 ((4.12))

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.4** (arXiv:2210.01610v2, p.15). "For any x ≤ α(θ_U), the mapping
[θ_L, θ_U] ∋ y ↦ l(x, y) := (ry − D(x))/(m(x) − y) is strictly increasing with the derivative
(4.12) 0 < (rm(x) − D(x))/(m(x) − y)² ≤ r m_min/(m_min − θ_U)², where m_min = inf_{x∈𝓘} m(x)."

For `x ∈ 𝓘`, under the standing assumptions of §4. -/
theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω) (c : ℝ) (α : ℝ → ℝ)
    (hG : G.Standing c α) :
    ∀ x ∈ G.I, x ≤ α G.θU →
      StrictMonoOn (G.l x) (Icc G.θL G.θU) ∧
      ∀ y ∈ Icc G.θL G.θU,
        HasDerivAt (G.l x) ((G.r * G.m x - G.D x) / (G.m x - y) ^ 2) y ∧
        0 < (G.r * G.m x - G.D x) / (G.m x - y) ^ 2 ∧
        (G.r * G.m x - G.D x) / (G.m x - y) ^ 2 ≤
          G.r * sInf (G.m '' G.I) / (sInf (G.m '' G.I) - G.θU) ^ 2 := by sorry

end ExitGamePrivate
