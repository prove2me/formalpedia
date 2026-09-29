-- Prove2me | Theorems.Thm_EisensteinGeneral_Arch_exists_norm_archIntegral_le
-- name    : EisensteinGeneral.Arch.exists_norm_archIntegral_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/a0683b75-0b5e-5ba1-9314-91d7076fc43d
-- title:
--   Uniform exponential bound for a K-Bessel archimedean integral
-- statement:
--   Let $c$ be a complex number with $\operatorname{Re} c > 0$ and let $M$ be a real number. The assertion is the existence of real constants $C > 0$ and $c' > 0$ and a natural number $N$, depending only on $c$ and $M$, such that for every complex number $z$ with $|\operatorname{Re} z| \le M$ and every nonzero real number $r$, the Bochner integral over the open half-line $(0,\infty)$, with respect to Lebesgue measure, of $u \mapsto u^{z}\exp\bigl(-c(u + r^{2}/u)\bigr)$ (the power $u^{z}$ being the complex power of the real variable $u$ viewed in $\mathbb{C}$) satisfies $$\Bigl\| \int_{0}^{\infty} u^{z}\,e^{-c(u + r^{2}/u)}\,du \Bigr\| \le C \cdot \max\bigl(1, |r|^{-N}\bigr)\cdot e^{-c'|r|},$$ where $|r|^{-N}$ is the real power with exponent $-(N : \mathbb{R})$. The bound is thus uniform in $z$ over the vertical strip $|\operatorname{Re} z| \le M$, in particular uniform in $\operatorname{Im} z$, and in the parameter $r$: it exhibits exponential decay in $|r|$ as $|r| \to \infty$, at the cost of a possible pole-type blow-up of order at most $N$ as $|r| \to 0$. No integrability hypothesis is imposed; the inequality is asserted for the integral as defined.
--
--   The integral is the standard archimedean Whittaker, or $K$-Bessel, integral attached to the parameters $c$ and $r$, and the statement is the elementary uniform estimate for it: exponential decay in $|r|$ with an allowance for small $|r|$. It feeds the construction of the archimedean local factors in [`EisensteinGeneral.Arch.exists_complexKType`](thm.html#EisensteinGeneral.Arch.exists_complexKType) and [`EisensteinGeneral.Arch.exists_realKType`](thm.html#EisensteinGeneral.Arch.exists_realKType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Arch_exists_norm_archIntegral_le.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_norm_archIntegral_le (c : ℂ) (hc : 0 < c.re) (M : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (z : ℂ) (r : ℝ), |z.re| ≤ M → r ≠ 0 →
      ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by sorry
