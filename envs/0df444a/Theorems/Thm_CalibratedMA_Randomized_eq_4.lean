-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_eq_4
-- name    : CalibratedMA.Randomized.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:29.46212+00:00
-- url     : https://prove2.me/theorems/db1e9c88-beb5-4930-9e72-a70c26515b00
-- title:
--   Section 3.2, Eq. (4) — mean preservation: E[P | S] = S
-- statement:
--   Let $\Gamma=(\gamma_0,\dots,\gamma_M)$ be a grid partition. The mean-preserving rounding preserves the conditional mean: for every $s\in[0,1]$,
--   $$\mathbb E[\mathrm{Round}_\Gamma(s)]=s,\qquad\text{so that}\qquad \mathbb E[P\mid S]=S\quad\text{for }P=\mathrm{Round}_\Gamma(S).\tag{4}$$
--
--   Mean preservation is why rounding leaves the multiaccuracy residuals $g(X)(Y-S)$ unchanged in expectation; only the calibration residual pays for rounding.
--
--   **Formalization Note.** The statement is pointwise in $s$: the integral of the identity against the law `roundMeasure M γ s` equals $s$.
--
--   Differences from the source:
--   - encoding: $\mathbb E[P\mid S]=S$ → $\int p\,\mathrm{Round}_\Gamma(s)(dp)=s$ for every $s\in[0,1]$; reason: given $S=s$, $P$ has law $\mathrm{Round}_\Gamma(s)$, so the pointwise identity is the conditional one.
--   - encoding: $\rho>0$ with $1/\rho$ an integer → $K\in\mathbb N$, $\rho=1/K$; reason: same instances.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 13, Section 3.2, Eq. (4)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Section 3.2, Eq. (4) (p. 13): mean-preserving rounding, `E[Round_Γ(s)] = s` for every
`s ∈ [0,1]`, i.e. `E[P | S] = S` for `P = Round_Γ(S)`. -/
theorem eq_4 (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p, p ∂(roundMeasure M γ s) = s := by sorry

end CalibratedMA.Randomized
