-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_lemma_3_4
-- name    : CalibratedMA.Randomized.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:07.832361+00:00
-- url     : https://prove2.me/theorems/ba3006fa-6b2c-4892-af48-1c656aa8617a
-- title:
--   Lemma 3.4 — population grid rounding rule (for the greedy partition of its proof)
-- statement:
--   Let $\nu$ be any distribution on $[0,1]$, let $m\in\mathbb R$ with $m\ge2$, and let $\rho>0$ with $1/\rho$ an integer and $\rho\le m^{-2}$. Let $\Gamma$ be the greedy partition of $\nu$ with threshold $\tau=1/(64m^2)$ on the grid $\Lambda_\rho$, the construction in the proof of Lemma 3.4 that Algorithm 1 uses in step 4. Then the partition points of $\Gamma$ belong to $\Lambda_\rho=\{0,\rho,2\rho,\dots,1\}$, $\Gamma$ has at most $4m+2$ intervals, and, for a universal constant $C$,
--   $$\mathrm{RoundErr}(\nu,\Gamma)\le\frac{C}{m^2}.$$
--
--   The point of the $m^{-2}$ rate is that rounding to about $m$ values costs only $O(m^{-2})$ in calibration, rather than the $O(m^{-1})$ obtained by summing interval contributions separately. Theorem 4.1 applies this lemma to the empirical score distribution $\hat\nu$.
--
--   **Formalization Note.** $\rho=1/K$ with $K\ge1$ a natural number, so $\rho\le m^{-2}$ reads $1/K\le(m^2)^{-1}$. The conclusion includes that the greedy output is a grid partition (`IsGridPartition`). $C$ is quantified before $\nu$, $m$ and $K$.
--
--   Differences from the source:
--   - generalization: "There is a partition $\Gamma$" → the conclusion holds for the explicit greedy partition of the proof; reason: this is the partition Algorithm 1 uses, and the existence statement follows by taking it.
--   - encoding: $\rho>0$ with $1/\rho$ an integer → $K\in\mathbb N$, $K\ge1$, $\rho=1/K$; reason: same instances.
--   - encoding: a distribution on [0,1] → a probability measure on ℝ assigning zero mass to the complement of [0,1]; reason: extension by zero and restriction identify the same distributions.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 16, Lemma 3.4 (greedy construction in its proof, pp. 16–17)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding
import Definitions.Def_CalibratedMA_Randomized_Algorithm1

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Lemma 3.4 (p. 16), population grid rounding rule, for the greedy partition constructed in
its proof: for every distribution `ν` on `[0,1]`, every `m ≥ 2` and every grid `Λ_ρ` with
`1/ρ = K` an integer and `ρ ≤ m^{-2}`, the greedy partition is a grid partition of `Λ_ρ` with at
most `4m + 2` intervals and `RoundErr(ν, Γ) ≤ C/m²`, for a universal constant `C`. -/
theorem lemma_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      ∀ (m : ℝ) (K : ℕ), 2 ≤ m → 1 ≤ K → (1 : ℝ) / K ≤ (m ^ 2)⁻¹ →
        IsGridPartition K (greedyPartition ν m K).1 (greedyPartition ν m K).2 ∧
        ((greedyPartition ν m K).1 : ℝ) ≤ 4 * m + 2 ∧
        RoundErr ν (greedyPartition ν m K).1 (greedyPartition ν m K).2 ≤ C / m ^ 2 := by sorry

end CalibratedMA.Randomized
