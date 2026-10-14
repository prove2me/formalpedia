-- Prove2me | Theorems.Thm_CauchyRiemannIndex_plane_holomorphic_solutions
-- name    : CauchyRiemannIndex.plane_holomorphic_solutions
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:04:44.487976+00:00
-- url     : https://prove2.me/theorems/16a43f35-e38e-4369-8b7d-2d6a053d9bee
-- title:
--   The L² solutions of ∂̄f + z f̄ = 0 on the plane are real multiples of a Gaussian
-- statement:
--   Let $\bar\partial=\partial_s+i\partial_t$ on $\mathbb{C}$, $z=s+it$. Every smooth $f:\mathbb{C}\to\mathbb{C}$ with $f\in L^2(\mathbb{C})$ and
--   $$\bar\partial f+z\,\bar f=0$$
--   is of the form $f(z)=c\,e^{-|z|^2/2}$ for a real constant $c$.
--
--   **Formalization Note** $\partial_sf$, $\partial_tf$ are `fderiv ℝ f z 1` and `fderiv ℝ f z Complex.I`; smoothness is `ContDiff ℝ ∞ f` and square integrability is `MemLp f 2 volume`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Proposition 5.21, p. 96

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Proposition 5.21 (p. 96): with `∂̄ = ∂ₛ + i ∂ₜ`, every smooth solution `f ∈ L²(ℂ, ℂ)`
of `∂̄f + z f̄ = 0` is a constant real multiple of `e^{-|z|²/2}`. -/
theorem plane_holomorphic_solutions (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (h2 : MemLp f 2 volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      z * (starRingEnd ℂ) (f z) = 0) :
    ∃ c : ℝ, ∀ z, f z = c * Complex.exp (-(‖z‖ ^ 2 / 2 : ℝ)) := by
  sorry

end CauchyRiemannIndex
