-- Prove2me | Theorems.Thm_DeltaSLearning_theorem_2_a
-- name    : DeltaSLearning.theorem_2_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:19.854931+00:00
-- url     : https://prove2.me/theorems/9b3406e9-efac-43f0-9127-184c5842d279
-- title:
--   Theorem 2(a) — $V(\delta,\cdot)$ is convex and Lipschitz, uniformly in $\delta$
-- statement:
--   Assume Assumption 1 and the cost parameters of §2. For $0\le\delta\le S\le\beta$ the cycle pseudo cost $G(\delta,S)$ is integrable, and there is a constant $M$ such that for every fixed $\delta\in[0,\beta]$ the map $S\mapsto V(\delta,S)$ is convex on $[\delta,\beta]$ and
--   $$|V(\delta,S_1)-V(\delta,S_2)|\le M|S_1-S_2|\qquad(S_1,S_2\in[\delta,\beta]).$$
--
--   Convexity in $S$ is what makes stochastic gradient descent on the target work for each fixed gap, and the uniform Lipschitz constant converts target errors into cost errors (Propositions 3 and 4).
--
--   Differences from the source:
--   - reading: Lipschitz constant independent of δ → ∃ M before ∀ δ ∈ [0, β]; reason: the page's "can be chosen independent of δ"
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[G(δ, S)] (finiteness presupposed) → integrability of G(δ, S) stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(a), p.12

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_avgCost

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Theorem 2(a)** (structure of the objective). For `0 ≤ δ ≤ S ≤ β`: the cycle pseudo cost
`G(δ, S)` is integrable, and for each fixed `δ ∈ [0, β]` the objective `V(δ, ·)` is convex and
Lipschitz on `[δ, β]`, with a Lipschitz constant `M` that does not depend on `δ`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 2(a), p.12.

**Formalization Note** `∃ M` precedes `∀ δ`: the constant is independent of `δ`. Integrability
of `G`, which `V = E[G]/E[L]` presupposes, is stated as a conclusion. -/
theorem theorem_2_a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) :
    (∀ δ S : ℝ, 0 ≤ δ → δ ≤ S → S ≤ cp.β →
        Integrable (fun ω => cycleCost cp δ S (fun t => D t ω)) P) ∧
      ∃ M : NNReal, ∀ δ ∈ Set.Icc 0 cp.β,
        LipschitzOnWith M (fun S => avgCost P D cp δ S) (Set.Icc δ cp.β) ∧
          ConvexOn ℝ (Set.Icc δ cp.β) (fun S => avgCost P D cp δ S) := by sorry

end DeltaSLearning
