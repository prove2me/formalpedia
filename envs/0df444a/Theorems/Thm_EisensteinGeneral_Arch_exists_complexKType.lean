-- Prove2me | Theorems.Thm_EisensteinGeneral_Arch_exists_complexKType
-- name    : EisensteinGeneral.Arch.exists_complexKType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/8be6708b-d9c5-561b-8fa5-b986003c0300
-- title:
--   Entire continuation and exponential decay of the complex K-type integral
-- statement:
--   For every pair of natural numbers $a, b$ there exists a function $J : \mathbb{C} \to \mathbb{C} \to \mathbb{C}$, of a complex exponent $w$ and a complex frequency $\zeta$, with the following three properties simultaneously. First, for each $\zeta \neq 0$ the function $w \mapsto J(w,\zeta)$ is differentiable on all of $\mathbb{C}$, i.e. entire. Second, for all $w, \zeta$ with $\operatorname{Re} w > (a+b)/2 + 1$ and $\zeta \neq 0$, the value $J(w,\zeta)$ is given by the integral over $z \in \mathbb{C}$, with respect to the Lebesgue (Haar) measure on $\mathbb{C}$, of $z^{a}\,\overline{z}^{\,b}\,(1+\lVert z\rVert^{2})^{-w}\,\exp\bigl(-4\pi i\,\operatorname{Re}(\zeta z)\bigr)$, where $\overline{\phantom{z}}$ is complex conjugation, the real number $1+\lVert z\rVert^{2}$ is viewed in $\mathbb{C}$ and raised to the power $-w$ in the sense of the complex power function. Third, the bound is uniform on bounded sets of exponents with exponential decay in the frequency: for every real $R$ there are reals $C>0$, $c'>0$ and a natural number $N$ such that $\lVert J(w,\zeta)\rVert \le C \cdot \max\bigl(1, \lVert\zeta\rVert^{-N}\bigr) \cdot \exp(-c'\lVert\zeta\rVert)$ for all $w$ with $\lVert w\rVert \le R$ and all $\zeta \neq 0$. Nothing is asserted about $J(w,0)$.
--
--   This is the archimedean local factor attached to the $K$-type of weight $(a,b)$ in the Whittaker integral of $GL(2)$ over $\mathbb{C}$: the weight-$(a,b)$ integral, convergent only in the half-plane $\operatorname{Re} w > (a+b)/2+1$, is packaged as an entire function of the exponent together with rapid decay in the frequency. It is used in the computation of Whittaker coefficients of Bruhat–Eisenstein series, where the entirety in $w$ permits the Euler-product identity to be propagated off the region of absolute convergence and the decay in $\zeta$ controls the resulting sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Arch_exists_complexKType.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_complexKType (a b : ℕ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by sorry
