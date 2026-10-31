-- Prove2me | Theorems.Thm_DeltaSLearning_corollary_1
-- name    : DeltaSLearning.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:31.895986+00:00
-- url     : https://prove2.me/theorems/03b79bb4-8409-4f28-87d3-da69bf2856fc
-- title:
--   Corollary 1 — $\mathbb E[\bar L]\le1+6\rho\beta$
-- statement:
--   Under the assumptions of Lemma 2, the maximum cycle length $\bar L:=L(\beta)$, for $\beta\ge0$, satisfies
--   $$\mathbb E[\bar L]\le 1+6\rho\beta .$$
--   Every cycle length $L(\delta)$, $\delta\le\beta$, is at most $\bar L$, so this bounds the expected length of every cycle and, up to a factor 2, of every epoch.
--
--   Differences from the source:
--   - encoding: i.i.d. positive random variables with densities bounded by ρ (Lemma 2's setting) → D satisfies Assumption 1; reason: same set of laws, as in Lemma 2
--   - encoding: E[L̄] (a real expectation) → lower Lebesgue integral of L(β) in [0, ∞]; reason: the bound in [0, ∞] also asserts finiteness; same value when finite
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Corollary 1, p.12

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_cycleLength

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Corollary 1** (bounded expected cycle length). The maximum cycle length `L̄ := L(β)`
satisfies `E[L̄] ≤ 1 + 6ρβ`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Corollary 1, p.12.

**Formalization Note** The expectation is the lower Lebesgue integral in `ℝ≥0∞`, so the bound
also asserts that `E[L̄]` is finite. -/
theorem corollary_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (ρ β : ℝ) (hρ : 0 < ρ) (hβ : 0 ≤ β) (hD : IsDemandProcess P D ρ) :
    ∫⁻ ω, ((cycleLength β (fun t => D t ω) : ℕ) : ENNReal) ∂P ≤ ENNReal.ofReal (1 + 6 * ρ * β) := by sorry

end DeltaSLearning
