-- Prove2me | Theorems.Thm_DeltaSLearning_theorem_2_b
-- name    : DeltaSLearning.theorem_2_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:58.158289+00:00
-- url     : https://prove2.me/theorems/71e0eab2-a99d-45b9-ac5b-033c66a1fb48
-- title:
--   Theorem 2(b) — $\tilde\nabla$ is an unbiased $S$-gradient of $\mathbb E[G(\delta,S)]$
-- statement:
--   Assume Assumption 1 and the cost parameters of §2. For $0\le\delta\le S\le\beta$, the cycle pseudo cost $G(\delta,S)$ and the stochastic gradient $\tilde\nabla$ of (11) are integrable, and
--   $$\frac{\partial}{\partial S}\mathbb E[G(\delta,S)]=\mathbb E[\tilde\nabla],$$
--   the derivative taken within $[\delta,\beta]$.
--
--   The algorithm's SGD step uses $\tilde\nabla$ computed from one simulated cycle; this theorem says it is an unbiased gradient.
--
--   Differences from the source:
--   - encoding: ∇_S E[G(δ, S)] for S in [δ, β] → HasDerivWithinAt on [δ, β] at S; reason: the function is considered on its domain [δ, β]; one-sided at the endpoints
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[G(δ, S) and of ∇̃] (finiteness presupposed) → integrability of G(δ, S) and of ∇̃ stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(b), eq. (11), p.12

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_cycleCost
import Definitions.Def_DeltaSLearning_cycleGrad

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Theorem 2(b)** (unbiased stochastic gradient). For `0 ≤ δ ≤ S ≤ β`, the cycle quantity
`∇̃` of (11) is an unbiased stochastic `S`-partial gradient of `E[G(δ, S)]`:
`∇_S E[G(δ, S)] = E[∇̃]`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(b) and eq. (11), p.12.

**Formalization Note** The derivative is taken within `[δ, β]` (one-sided at the endpoints).
Integrability of `G` and `∇̃`, which the expectations presuppose, is stated as a conclusion. -/
theorem theorem_2_b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    ∀ δ ∈ Set.Icc 0 cp.β, ∀ S ∈ Set.Icc δ cp.β,
      Integrable (fun ω => cycleCost cp δ S (fun t => D t ω)) P ∧
        Integrable (fun ω => cycleGrad cp δ S (fun t => D t ω)) P ∧
        HasDerivWithinAt (fun S' => ∫ ω, cycleCost cp δ S' (fun t => D t ω) ∂P)
          (∫ ω, cycleGrad cp δ S (fun t => D t ω) ∂P) (Set.Icc δ cp.β) S := by sorry

end DeltaSLearning
