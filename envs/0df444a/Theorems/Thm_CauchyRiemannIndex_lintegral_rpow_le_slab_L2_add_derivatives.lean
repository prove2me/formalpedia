-- Prove2me | Theorems.Thm_CauchyRiemannIndex_lintegral_rpow_le_slab_L2_add_derivatives
-- name    : CauchyRiemannIndex.lintegral_rpow_le_slab_L2_add_derivatives
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T20:51:20.350988+00:00
-- url     : https://prove2.me/theorems/bf5a4ad2-e6a6-4e58-b6a3-b8458ed5c529
-- title:
--   $L^p$ norm on the strip $\mathbb R\times[0,1)$ bounded by an $L^2$ slab amalgam norm plus $h^p$ times the gradient, $p\ge2$
-- statement:
--   Let $2\le p<\infty$, let $N\ge1$ be an integer and $h=1/N$. Every $C^1$ map $u:\mathbb R^2\to\mathbb R^{2n}$ satisfies
--   $$\int_{\mathbb R\times[0,1)}|u|^p\;\le\;3^{p-1}\Big(N^{p-1}\int_{\mathbb R}\Big(\int_{[s,s+h]\times[0,1)}|u|^2\Big)^{p/2}ds\;+\;N^{-p}\Big(\int_{\mathbb R\times[0,1)}|\partial_su|^p+\int_{\mathbb R\times[0,1)}|\partial_tu|^p\Big)\Big).$$
--
--   So on the strip $\mathbb R\times[0,1)$ the $L^p$ norm is controlled by the $\ell^p(L^2)$ amalgam norm over slabs of width $h$, with an explicit constant depending on $h$, plus $h^p$ times the $L^p$ norms of the first partial derivatives, with a constant independent of $h$. It is used to pass from slab-wise $L^2$ bounds to $L^p$ bounds for maps on the cylinder $\mathbb R\times S^1$ (Wendl, Theorem 4.11, case $k=1$).
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $(s,t)\in\mathbb R\times\mathbb R$, and integrals over $\mathbb R\times[0,1)$ are against `cylMeasure` (Lebesgue measure on the strip). The slab $[s,s+h]\times[0,1)$ is `Set.Icc s (s + 1 / N) ×ˢ Set.Ico 0 1` with Lebesgue measure. $\partial_su$ and $\partial_tu$ are `partialS u` and `partialT u` (the Fréchet derivative applied to $(1,0)$ and $(0,1)$). All integrals are lower Lebesgue integrals of `‖·‖ₑ` powers in $[0,\infty]$, so the inequality holds without integrability assumptions; $p$ is real with $2\le p$ and the powers of $3$ and $N$ are real powers in $[0,\infty]$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator, case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `2 ≤ p < ∞`, `N ≥ 1` and `h = 1/N`. Every `C¹` map `u : ℝ × ℝ → ℝ²ⁿ` satisfies
`∫_{ℝ × [0,1)} |u|^p ≤ 3^{p-1} (N^{p-1} ∫_ℝ (∫_{[s, s+h] × [0,1)} |u|²)^{p/2} ds
  + N^{-p} (∫_{ℝ × [0,1)} |∂ₛu|^p + ∫_{ℝ × [0,1)} |∂ₜu|^p))`.

The `L^p` norm on the strip `ℝ × [0,1)` is controlled by the `L²` amalgam norm over slabs of
width `h` plus `h^p` times the `L^p` norms of the first derivatives, with constants explicit
in `h`. -/
theorem lintegral_rpow_le_slab_L2_add_derivatives (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (N : ℕ)
    (hN : 1 ≤ N) (u : ℝ × ℝ → Vec n) (hu : ContDiff ℝ 1 u) :
    ∫⁻ x, ‖u x‖ₑ ^ p ∂cylMeasure ≤
      (3 : ℝ≥0∞) ^ (p - 1) *
        ((N : ℝ≥0∞) ^ (p - 1) *
            (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1 / (N : ℝ)) ×ˢ Set.Ico (0 : ℝ) 1,
              ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) +
          (N : ℝ≥0∞) ^ (-p) *
            (∫⁻ x, ‖partialS u x‖ₑ ^ p ∂cylMeasure + ∫⁻ x, ‖partialT u x‖ₑ ^ p ∂cylMeasure)) := by
  sorry

end CauchyRiemannIndex
