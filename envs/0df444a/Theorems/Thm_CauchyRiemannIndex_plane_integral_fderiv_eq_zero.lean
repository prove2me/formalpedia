-- Prove2me | Theorems.Thm_CauchyRiemannIndex_plane_integral_fderiv_eq_zero
-- name    : CauchyRiemannIndex.plane_integral_fderiv_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:49:57.262566+00:00
-- url     : https://prove2.me/theorems/13335963-7fc3-4737-afbf-dac72880fbc9
-- title:
--   The integral of a directional derivative of a compactly supported C¹ map ℂ → ℂ vanishes
-- statement:
--   Let $g:\mathbb{C}\to\mathbb{C}$ be $C^1$ (in the real sense) with compact support, and let $v\in\mathbb{C}$. Then
--   $$\int_{\mathbb{C}} Dg(z)\,v\;dz=0,$$
--   where $dz$ is Lebesgue measure on $\mathbb{C}\cong\mathbb{R}^2$.
--
--   **Formalization Note** $Dg(z)\,v$ is `fderiv ℝ g z v`; $C^1$ is `ContDiff ℝ 1 g`; compact support is `HasCompactSupport g`; the integral is the Bochner integral for `volume` on `ℂ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Proposition 5.20, p. 96 (auxiliary lemma)

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace CauchyRiemannIndex

open MeasureTheory

/-- For a compactly supported `C¹` map `g : ℂ → ℂ` and a direction `v ∈ ℂ`, the integral over
the plane (Lebesgue measure) of the directional derivative `Dg(z) v` is zero. -/
theorem plane_integral_fderiv_eq_zero (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : ℂ) :
    ∫ z, fderiv ℝ g z v = 0 := by
  sorry

end CauchyRiemannIndex
