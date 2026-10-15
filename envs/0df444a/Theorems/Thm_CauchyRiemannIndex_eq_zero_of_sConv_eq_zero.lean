-- Prove2me | Theorems.Thm_CauchyRiemannIndex_eq_zero_of_sConv_eq_zero
-- name    : CauchyRiemannIndex.eq_zero_of_sConv_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:02:00.920453+00:00
-- url     : https://prove2.me/theorems/fd1dc27e-f2ff-4551-8088-9209e1bf9c53
-- title:
--   An $L^q$ map on the cylinder all of whose convolutions in the $s$-variable vanish is zero
-- statement:
--   Let $1\le q\le\infty$ and $g\in L^q(\mathbb R\times S^1,\mathbb R^{2n})$. Suppose that for every $\rho\in C^\infty_c(\mathbb R)$ the function
--   $$G_\rho(s,t)=\int_{\mathbb R}\rho(\sigma)\,g(s-\sigma,t)\,d\sigma$$
--   vanishes almost everywhere on $\mathbb R\times S^1$. Then $g=0$.
--
--   So convolutions in one variable with test functions separate $L^q$ functions on the cylinder: a function vanishes once all its regularizations in $s$ do.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$, and $L^q(\mathbb R\times S^1)$ is `LpCyl n q`, i.e. $L^q$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`), with values in $\mathbb R^{2n}$ = `Vec n`. The convolution is written pointwise, `fun x => ∫ σ, ρ σ • g (x.1 - σ, x.2)`, with `g` the chosen representative of the $L^q$ class; $\rho$ is `ContDiff ℝ ∞` with `HasCompactSupport`. $q$ is in `ℝ≥0∞` with `Fact (1 ≤ q)`.
-- source:
--   G. B. Folland, Real Analysis, 2nd ed., Wiley 1999, Theorem 8.14 (approximate identities), p. 242, applied in the first variable

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

/-- If `g ∈ L^q` of the cylinder (`1 ≤ q ≤ ∞`) and, for every smooth compactly supported
`ρ : ℝ → ℝ`, the convolution `G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ` of `g` with `ρ` in the
`s`-variable vanishes almost everywhere on the cylinder, then `g = 0`. -/
theorem eq_zero_of_sConv_eq_zero (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q)
    (h : ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) =ᵐ[cylMeasure] 0) :
    g = 0 := by
  sorry

end CauchyRiemannIndex
