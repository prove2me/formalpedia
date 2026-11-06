-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_uniform_rightInverse_of_fderiv_small
-- name    : FiniteEnergyPlane.exists_uniform_rightInverse_of_fderiv_small
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:24:26.884197+00:00
-- url     : https://prove2.me/theorems/f2918be8-5569-49e5-899d-ab335b753eba
-- title:
--   Right inverses persist, uniformly, under $C^1$-small perturbations
-- statement:
--   Let $X,Y$ be real Banach spaces, $X\neq\{0\}$, $\Phi:X\to Y$ be $C^1$ near $p_0$ with $D\Phi(p_0)=e$ an isomorphism, and let $d_k:X\to Y$ be differentiable on $B(p_0,R)$ with $\sup_{B(p_0,R)}\|Dd_k\|\to 0$ and $d_k(p_0)\to 0$. Then there are $K,R_0>0$ such that for all $\eta\in(0,R_0]$ there is $\delta>0$ with: for all large $k$ there is a map $\Psi_k$, continuous on $B(\Phi(p_0),\delta)$, with values in $B(p_0,\eta)$ and $(\Phi+d_k)\circ\Psi_k=\mathrm{id}$ on that ball, and $\|p-\Psi_k(y)\|\le K\|y-(\Phi+d_k)(p)\|$ for all $p\in B(p_0,\eta)$ and $y\in B(\Phi(p_0),\delta)$.
--
--   Role: local solvability with continuous dependence and a uniform constant for a sequence of maps converging in $C^1$ on a ball.
-- source:
--   Standard quantitative form of the inverse function theorem

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace FiniteEnergyPlane

open Metric Filter Topology

/-- Let `Φ : X → Y` be `C¹` near `p₀` with `DΦ(p₀) = e` an isomorphism, and let `d k` be differentiable
on `B(p₀, R)` with `sup ‖D(d k)‖ → 0` there and `d k p₀ → 0`. Then there are `K, R₀ > 0` such that for every
`η ∈ (0, R₀]` there is `δ > 0` with: for all large `k` there is a map `Ψ`, continuous on
`B(Φ p₀, δ)`, with values in `B(p₀, η)` and `(Φ + d k) ∘ Ψ = id` on that ball, and
`‖p - Ψ y‖ ≤ K ‖y - (Φ + d k) p‖` for `p ∈ B(p₀, η)`, `y ∈ B(Φ p₀, δ)`. -/
theorem exists_uniform_rightInverse_of_fderiv_small {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Φ : X → Y) (d : ℕ → X → Y) (e : X ≃L[ℝ] Y) (p₀ : X) (R : ℝ) (hR : 0 < R)
    (hΦ : ContDiffAt ℝ 1 Φ p₀) (he : fderiv ℝ Φ p₀ = (e : X →L[ℝ] Y))
    (hd : ∀ k, ∀ p ∈ ball p₀ R, DifferentiableAt ℝ (d k) p)
    (hdu : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ p ∈ ball p₀ R, ‖fderiv ℝ (d k) p‖ ≤ ε)
    (hd0 : Tendsto (fun k => d k p₀) atTop (𝓝 0)) :
    ∃ K > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ η ∈ Set.Ioc 0 R₀, ∃ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ Ψ : Y → X,
      ContinuousOn Ψ (ball (Φ p₀) δ) ∧
      (∀ y ∈ ball (Φ p₀) δ, Ψ y ∈ ball p₀ η ∧ Φ (Ψ y) + d k (Ψ y) = y) ∧
      ∀ p ∈ ball p₀ η, ∀ y ∈ ball (Φ p₀) δ, ‖p - Ψ y‖ ≤ K * ‖y - (Φ p + d k p)‖ := by
  sorry

end FiniteEnergyPlane
