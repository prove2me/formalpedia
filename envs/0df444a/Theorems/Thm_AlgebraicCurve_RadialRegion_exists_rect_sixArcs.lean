-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_rect_sixArcs
-- name    : AlgebraicCurve.RadialRegion.exists_rect_sixArcs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/5f646965-2885-50b1-8814-39826e510a76
-- title:
--   A rectangle is a radial region with six arcs
-- statement:
--   Let $x_0,x_1,y_0,y_1,y_L$ be real numbers and $p$ a complex number, and assume $x_0 < \operatorname{Re} p < x_1$, $y_0 < \operatorname{Im} p < y_1$ and $y_0 < y_L < y_1$. Then there is a radial region $R$ — that is, a centre $R.q$, a continuous, $2\pi$-periodic, everywhere positive radius function $R.r$, a number $R.N$ of arcs, and strictly increasing break points $R.\varphi s : \mathrm{Fin}(R.N+1) \to \mathbb{R}$ with $R.\varphi s(0)=0$, $R.\varphi s(\mathrm{last})=2\pi$, on each closed interval $[R.\varphi s(k), R.\varphi s(k+1)]$ of which $R.r$ is twice continuously differentiable — such that: $R.q = p$ and $R.N = 6$; the set `R.K` is the closed rectangle $\{z : \operatorname{Re} z \in [x_0,x_1],\ \operatorname{Im} z \in [y_0,y_1]\}$, while $R.\mathrm{Kint} = \{z : \lVert z - p\rVert < R.r(\arg(z-p))\}$ is the open rectangle $(x_0,x_1)\times(y_0,y_1)$; the six arc sets $R.\mathrm{arcSet}\,k$, the images under $R.\mathrm{loop}\,\varphi = R.q + R.r(\varphi)e^{i\varphi}$ of the intervals $R.\mathrm{arcIcc}\,k$, are respectively the right side above the height of $p$, the top side, the part of the left side above height $y_L$, the part of the left side below $y_L$, the bottom side, and the right side below the height of $p$; the seven values $R.\mathrm{loop}(R.\varphi s(k))$, $k=0,\dots,6$, are $(x_1,\operatorname{Im} p)$, $(x_1,y_1)$, $(x_0,y_1)$, $(x_0,y_L)$, $(x_0,y_0)$, $(x_1,y_0)$, $(x_1,\operatorname{Im} p)$; on the arc intervals for $k=0,5$ one has $R.r(t) = (\cos t/(x_1-\operatorname{Re} p))^{-1}$, for $k=1$ that $R.r(t) = (\sin t/(y_1-\operatorname{Im} p))^{-1}$, for $k=2,3$ that $R.r(t) = (-\cos t/(\operatorname{Re} p - x_0))^{-1}$, and for $k=4$ that $R.r(t) = (-\sin t/(\operatorname{Im} p - y_0))^{-1}$; the arc intervals are contained in $[0,\pi/2)$, $(0,\pi)$, $(\pi/2,3\pi/2)$ (for $k=2,3$), $(\pi,2\pi)$ and $(3\pi/2,2\pi]$ respectively; every $z \in R.K \setminus R.\mathrm{Kint}$ satisfies $R.\mathrm{loop}(\theta) = z$ where $\theta$ is $\arg(z-p)$ normalised to $[0,2\pi)$ by adding $2\pi$ when negative; and for $t_1 \le t_2$ in a single $R.\mathrm{arcIcc}\,k$ the image $R.\mathrm{loop}\,''\,[t_1,t_2]$ is the real segment joining $R.\mathrm{loop}\,t_1$ to $R.\mathrm{loop}\,t_2$.
--
--   This realises a closed coordinate rectangle, viewed from an interior point, as a star-shaped region described in polar form, with the four sides cut into six arcs (the two vertical sides being split, the right one at the height of the centre and the left one at a prescribed height $y_L$) and with the radius on each arc given by the reciprocal support function of the corresponding side. It is a building block of the grid construction for cell dissections, used by [`AlgebraicCurve.RadialRegion.exists_window_perimeter`](thm.html#AlgebraicCurve.RadialRegion.exists_window_perimeter) and [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_rect_sixArcs (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    ∃ R : RadialRegion,
      R.q = p ∧ R.N = 6 ∧
      R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
      (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
      (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ R.K, z ∉ R.Kint →
        R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
          = z) ∧
      (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
        R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂)) := by sorry
