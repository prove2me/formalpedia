-- Prove2me | Theorems.Thm_BousquetElisseeff_KLReg_avgLoss_lipschitz_l1
-- name    : BousquetElisseeff.KLReg.avgLoss_lipschitz_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:19.88942+00:00
-- url     : https://prove2.me/theorems/d3a851b8-bd27-47f5-bf86-5c6c00829ae4
-- title:
--   The averaged loss $\ell(\cdot, z)$ is $M$-Lipschitz in $L^1$
-- statement:
--   Let $\mu$ be a reference measure on a measurable space $\Theta$, and let $r(\theta, z)$ be a loss, measurable in $\theta$, with $|r(\theta,z)| \le M$ for all $\theta, z$. For any two probability densities $g, g'$ with respect to $\mu$ and every example $z$,
--   $$|\ell(g,z) - \ell(g',z)| \le M \int_\Theta |g(\theta) - g'(\theta)|\, d\mu(\theta),$$
--   where $\ell(g,z) = \int_\Theta r(\theta,z) g(\theta)\, d\mu(\theta)$ is the averaged loss (28).
--
--   This is the $M$-admissibility of $\ell$ used twice in the proof of Theorem 24.
--
--   Differences from the source:
--   - generalization: standing assumption "all sets are countable" (p. 501) → Θ any measurable space, Z any type, μ any measure; reason: no step of the argument uses countability; the countable case is an instance
--   - encoding: 𝓕 = probability distributions dominated by the reference measure, given by their densities (p. 517) → IsDensity μ g: g measurable, g ≥ 0, ∫ g dμ = 1; reason: this is the paper's 𝓕; densities equal μ-a.e. give the same ℓ and K
--   - generalization: a bound M on the loss r(h_θ, z), with nonnegative costs (p. 502) → ∀ θ z, |r θ z| ≤ M (r may be negative); reason: 0 ≤ r ≤ M implies |r| ≤ M, so the paper's case is an instance
--   - encoding: r(h_θ, z) on 𝓗 × 𝓩, all functions measurable (p. 501) → r : Θ → Z → ℝ with θ ↦ r θ z measurable; reason: r depends on h only through θ
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, §5.2.3, unnumbered display before Theorem 24, p. 518

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **The averaged loss is M-Lipschitz in L¹ (M-admissibility of ℓ)** (§5.2.3).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, §5.2.3, unnumbered display before Theorem 24, p. 518: "Let's analyze this algorithm. We
will assume that we know a bound M on the loss r(h_θ, z). First, notice that ℓ is linear in g
and is thus convex and M-Lipschitz with respect to the L1 norm
|ℓ(g, z) − ℓ(g′, z)| ≤ M ∫_Θ |g(θ) − g′(θ)|dθ."

If `θ ↦ r θ z` is measurable for every `z` and `|r θ z| ≤ M` everywhere, then for any two
densities `g`, `g'` and every example `z`,
`|ℓ(g, z) − ℓ(g', z)| ≤ M ∫ |g − g'| dμ`, with `ℓ = avgLoss μ r` (eq. (28)).

**Formalization Note.** "a bound M on the loss" is read as `|r| ≤ M`; the mission's standing
`0 ≤ r ≤ M` (nonnegative costs, p. 502) is a special case. Measurability of `r` in θ is the
paper's standing assumption (p. 501). -/
theorem avgLoss_lipschitz_l1 {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M : ℝ) (hr_meas : ∀ z, Measurable (fun θ => r θ z)) (hr : ∀ θ z, |r θ z| ≤ M)
    (g g' : Θ → ℝ) (hg : IsDensity μ g) (hg' : IsDensity μ g') (z : Z) :
    |avgLoss μ r g z - avgLoss μ r g' z| ≤ M * ∫ θ, |g θ - g' θ| ∂μ := by sorry

end BousquetElisseeff.KLReg
