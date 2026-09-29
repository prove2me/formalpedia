-- Prove2me | Theorems.Thm_EisensteinGeneral_Arch_exists_realKType
-- name    : EisensteinGeneral.Arch.exists_realKType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/3c1a85a4-2eb8-5345-8ad1-d4f8a6d1c974
-- title:
--   Entire continuation and decay of the real K-type integral
-- statement:
--   For every integer $k$ there exists a function $J \colon \mathbb{C} \times \mathbb{R} \to \mathbb{C}$, written $J(w,t)$ with $w$ a complex exponent and $t$ a real frequency, having simultaneously the following three properties. First, for each nonzero real $t$ the map $w \mapsto J(w,t)$ is complex differentiable at every point of $\mathbb{C}$, i.e. entire. Second, for every complex $w$ with $\operatorname{Re} w > 1/2$ and every nonzero real $t$, the value $J(w,t)$ is given by the Lebesgue integral over the whole real line $$J(w,t) = \int_{\mathbb{R}} \Bigl(\frac{x - i}{\sqrt{1+x^{2}}}\Bigr)^{k} (1+x^{2})^{-w} e^{-2\pi i t x}\,dx,$$ where the $k$-th power is the integer power of a complex number, $(1+x^{2})^{-w}$ is the complex power of the positive real $1+x^{2}$, and $\sqrt{\cdot}$ is the real square root. Third, for every real $R$ there are real constants $C > 0$ and $c' > 0$ and a natural number $N$ such that $\|J(w,t)\| \le C \max(1, |t|^{-N}) e^{-c'|t|}$ for all complex $w$ with $\|w\| \le R$ and all nonzero real $t$; thus on each bounded region of the $w$-plane the function decays exponentially in $|t|$, with at most a fixed polynomial blow-up as $|t| \to 0$.
--
--   This is the archimedean $K$-type (weight-$k$) factor of the Whittaker integral for $\mathrm{GL}_2$ over $\mathbb{R}$: the integral converges only in the half-plane $\operatorname{Re} w > 1/2$, and the statement packages its entire continuation in the exponent together with uniform exponential decay in the frequency. It is used in the computation of Whittaker coefficients of Bruhat-cell Eisenstein series, where the real place contributes such a factor to the Euler product, and it is deduced from the corresponding bound [`EisensteinGeneral.Arch.exists_norm_archIntegral_le`](thm.html#EisensteinGeneral.Arch.exists_norm_archIntegral_le) for integrals $\int_0^{\infty} u^{z} e^{-c(u + r^{2}/u)}\,du$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Arch_exists_realKType.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_realKType (k : ℤ) :
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 →
        J w t = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w : ℂ) (t : ℝ), ‖w‖ ≤ R → t ≠ 0 →
        ‖J w t‖ ≤ C * max 1 (|t| ^ (-(N : ℝ))) * Real.exp (-c' * |t|)) := by sorry
