-- Prove2me | Theorems.Thm_BousquetElisseeff_KLReg_pinsker_l1
-- name    : BousquetElisseeff.KLReg.pinsker_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:46.069171+00:00
-- url     : https://prove2.me/theorems/24391448-f3f6-49ab-97cb-381950d3f5b1
-- title:
--   Pinsker's inequality: $\frac12\left(\int_\Theta |g-g'|\right)^2 \le K(g,g')$
-- statement:
--   Let $\mu$ be a reference measure on a measurable space $\Theta$ and let $g, g'$ be probability densities with respect to $\mu$. Then
--   $$\frac12 \left(\int_\Theta |g(\theta) - g'(\theta)|\, d\mu(\theta)\right)^2 \le K(g, g'),$$
--   where $K(g,g') \in [0,\infty]$ is the relative entropy (natural logarithm).
--
--   This is the step of the proof of Theorem 24 that converts a bound on relative entropies into a bound in $L^1$ distance between the regularized posteriors.
--
--   **Formalization Note** The left side is a nonnegative real number embedded in $[0,\infty]$; when $K(g,g') = +\infty$ the inequality is trivial.
--
--   Differences from the source:
--   - generalization: standing assumption "all sets are countable" (p. 501) → Θ any measurable space, Z any type, μ any measure; reason: no step of the argument uses countability; the countable case is an instance
--   - encoding: 𝓕 = probability distributions dominated by the reference measure, given by their densities (p. 517) → IsDensity μ g: g measurable, g ≥ 0, ∫ g dμ = 1; reason: this is the paper's 𝓕; densities equal μ-a.e. give the same ℓ and K
--   - encoding: K(g, g′) = ∫_Θ g ln(g/g′) dθ (p. 517) → relEnt μ g g′ = klDiv (g·μ) (g′·μ) ∈ [0, ∞]; reason: for probability measures Mathlib's klDiv is ∫ g ln(g/g′) when finite and +∞ otherwise; same values
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, proof of Theorem 24, unnumbered display, p. 518 (citing Cover and Thomas 1991)

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **Pinsker's inequality in L¹ form** (proof of Theorem 24).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, proof of Theorem 24, unnumbered display, p. 518: "Recall the following property of the
relative entropy (see e.g. Cover and Thomas 1991), for any g, g′,
(1/2) (∫_Θ |g(θ) − g′(θ)|dθ)² ≤ K(g, g′)."

For any two densities `g`, `g'` with respect to an arbitrary reference measure `μ`,
`(1/2) (∫ |g − g'| dμ)² ≤ K(g, g')`, where K is `relEnt` (value in `[0, ∞]`).

**Formalization Note.** "for any g, g′" ranges over 𝓕, the densities (`IsDensity`). The left
side is a nonnegative real number, embedded in `[0, ∞]` by `ENNReal.ofReal` (no clamping
occurs); the inequality holds trivially when K = +∞. K is in nats (natural logarithm), as the
paper's `ln`. -/
theorem pinsker_l1 {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (g g' : Θ → ℝ)
    (hg : IsDensity μ g) (hg' : IsDensity μ g') :
    ENNReal.ofReal ((1 / 2) * (∫ θ, |g θ - g' θ| ∂μ) ^ 2) ≤ relEnt μ g g' := by sorry

end BousquetElisseeff.KLReg
