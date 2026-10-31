-- Prove2me | Theorems.Thm_ExitGamePrivate_lemma_4_3
-- name    : ExitGamePrivate.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:28.994994+00:00
-- url     : https://prove2.me/theorems/c8c9deb4-0d4f-4a57-bb1a-6d8e7fffe1d2
-- title:
--   Lemma 4.3 — the diffusion spends zero time on any càdlàg finite-variation adapted curve
-- statement:
--   Let $X$ be the diffusion (2.1) under the setting of §2 and Assumption 2.4. For any process $(\varphi_t)_{t\ge0}$ that is $(\mathcal F_t)$-adapted, càdlàg, and of finite variation on every bounded interval, and any $x\in\mathcal I$,
--   $$\int_0^\infty 1_{\{X_s=\varphi_s\}}\,ds=0\qquad P_x\text{-a.s.}$$
--
--   This is why modifying the exit rate $\lambda$ on curves $x=h(y)$ does not change the solutions of (4.2); it is used in the construction of Proposition 4.6.
--
--   Differences from the source:
--   - generalization: stated under the standing assumptions of §4 (Assumptions 2.3, 3.1, 4.1 included) → the setting of §2 and Assumption 2.4 only (Diffusion.IsRegular); reason: the other assumptions concern D, M, θ, F, which do not occur; the statement specializes to the paper's
--   - encoding: càdlàg finite variation process; ∫_0^∞ 1_{X_s=φ_s} ds → every path right-continuous with left limits on [0, ∞) and of bounded variation on every [0, T]; the Lebesgue measure of {s ≥ 0 : Xˣ_s = φ_s}; reason: same notions
--   - encoding: a complete probability space (Ω, F, P) with a filtration (Fₜ) satisfying the usual conditions and an (Fₜ)-Brownian motion W (p.5) → EntropyMFG.Enhanced.BrownianOn P 𝔽 W T for every horizon T > 0 (P-null sets in F₀, right-continuity, Gaussian increments independent of the past); time is ℝ and the filtration is restricted to ℝ≥0 for stopping times; reason: the reused platform definitions index time by ℝ on finite horizons; requiring them on every horizon is the infinite-horizon setting of the paper
--   - encoding: Xˣ is the unique strong solution of (2.1) from x, with values in 𝓘 = (x_L, x_U) whose boundaries are not attainable (p.5) → a family X with X x a StrongSolution of (2.1) from x on every [0, T] and, almost surely, Xˣₜ ∈ 𝓘 for all t ≥ 0; x_L, x_U ∈ [−∞, ∞] with 𝓘 nonempty; reason: strong solutions are indistinguishable under Assumption 2.4, so a statement for every such family is the statement for the paper's Xˣ; nonemptiness only excludes an empty state space
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, Lemma 4.3, p.15

import Mathlib
import Definitions.Def_ExitGamePrivate_Diffusion

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExitGamePrivate

/-- **Lemma 4.3** (arXiv:2210.01610v2, p.15). "For any càdlàg finite variation (Fₜ)-adapted
process (φₜ), we have ∫_0^∞ 1_{X_s=φ_s} ds = 0, Pₓ − a.s. for any x ∈ 𝓘."

**Formalization Note** Stated for the diffusion alone, under the setting of §2 and Assumption 2.4
(the other standing assumptions of §4 concern `D, M, θ, F`, which do not occur). Càdlàg and finite
variation (on every `[0, T]`) are required of every path; the integral is the Lebesgue measure
of the time set `{s ≥ 0 : Xˣ_s = φ_s}`. -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (Dif : Diffusion Ω) (hreg : Dif.IsRegular)
    (φp : ℝ → Ω → ℝ) (hadapt : ∀ t : ℝ, 0 ≤ t → Measurable[Dif.𝔽 t] (φp t))
    (hrc : ∀ ω, ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (fun s => φp s ω) (Ici t) t)
    (hll : ∀ ω, ∀ t : ℝ, 0 < t → ∃ z : ℝ, Tendsto (fun s => φp s ω) (𝓝[<] t) (𝓝 z))
    (hfv : ∀ ω, ∀ T : ℝ, 0 ≤ T → BoundedVariationOn (fun s => φp s ω) (Icc 0 T)) :
    ∀ x ∈ Dif.I, ∀ᵐ ω ∂Dif.P, volume {s : ℝ | 0 ≤ s ∧ Dif.X x s ω = φp s ω} = 0 := by sorry

end ExitGamePrivate
