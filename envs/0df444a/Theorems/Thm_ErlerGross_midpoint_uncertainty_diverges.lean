-- Prove2me | Theorems.Thm_ErlerGross_midpoint_uncertainty_diverges
-- name    : ErlerGross.midpoint_uncertainty_diverges
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:57:52.13466+00:00
-- url     : https://prove2.me/theorems/9ca4a194-be44-41c2-94ba-c61429176eef
-- title:
--   Midpoint regulators: $\sum\frac{((-1)^n-\omega_{2n})^2}{2n}$ diverges
-- statement:
--   For a midpoint regulator $\omega_{2n}$ with $\lim_{n\to\infty}\omega_{2n}=0$, the mean-square uncertainty of the midpoint $$\langle\Delta x(\tfrac{\pi}{2})\rangle^2(\omega)=D\sum_{n\ge1}\frac{((-1)^n-\omega_{2n})^2}{2n}$$ is infinite: the partial sums of the series tend to $+\infty$ (the factor $D>0$ is omitted).
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Section 2, pp. 9-10 ('Unless the midpoint limit has already been reached, for any acceptable regulator $\lim\omega_{2n}=0$. Therefore, this sum is logarithmically divergent.')

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem midpoint_uncertainty_diverges (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => ω (2 * n)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((-1 : ℝ) ^ (n + 1) - ω (2 * (n + 1))) ^ 2 / (2 * ((n : ℝ) + 1)))
      atTop atTop := by
  sorry

end ErlerGross
