-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero
-- name    : FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T19:31:53.650202+00:00
-- url     : https://prove2.me/theorems/e08b2b15-527b-4734-9337-5edb2bee5d37
-- title:
--   Non-vanishing on the plane from a spectral window at the end
-- statement:
--   Let $S$ be smooth on $(s_1,\infty)\times\mathbb R$, $1$-periodic in $t$, and exponentially asymptotic to a smooth symmetric loop $S_\infty$, and let $\delta$ be such that every eigenvalue $\mu$ of $S_\infty$ of winding $k$ satisfies $\mu<\delta,\ k\le 1$ or $\delta<\mu,\ 2\le k$. Let $\nu_e,\nu$ be smooth $1$-periodic solutions of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on $s>s_1$, with $\nu_e$ bounded and of winding number $1$ on all loops with large $s$, and with $\|\nu\|\le C_0e^{\delta s}+c_0\|\nu_e\|$. Let $Y:\mathbb C\to\mathbb C$ be smooth with $|\partial_sY+i\partial_tY|\le M|Y|$ locally, and suppose $\nu=Y(e^{2\pi(s+it)})\,\nu_e$ as complex numbers. Then either $Y\equiv 0$ or $Y$ has no zeros.
--
--   The statement turns a spectral window for the asymptotic operator into a global non-vanishing property on the plane.
--
--   Formalization Note: `cylInf s t` is $e^{2\pi(s+it)}$; `vecToC` identifies $\mathbb R^2$ with $\mathbb C$; the equation is `CauchyRiemannIndex.crOp S ζ = 0`; decay of $S-S_\infty$ is `IsExpAsymptoticTo`.
-- source:
--   Hofer-Wysocki-Zehnder, Finite energy foliations of tight three-spheres and Hamiltonian dynamics (2003); Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere (2014), Section 6

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `S` be exponentially asymptotic to a symmetric loop `S∞` on a half-cylinder `s > s₁`, with
every eigenvalue `μ` of `S∞` of winding `k` satisfying `μ < δ, k ≤ 1` or `δ < μ, 2 ≤ k`. Let `νe, ν`
be `1`-periodic solutions of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` there, with `νe` bounded and of winding number
`1` on large loops, `ν = Y(e^{2π(s+it)}) νe` as complex numbers, and
`‖ν‖ ≤ C₀ e^{δ s} + c₀ ‖νe‖`. If `Y : ℂ → ℂ` is smooth with `|∂ₛY + i ∂ₜY| ≤ M |Y|` locally, then
`Y` vanishes identically or has no zeros. -/
theorem forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero (Y : ℂ → ℂ) (hY : ContDiff ℝ ∞ Y)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ Y z 1 + Complex.I * fderiv ℝ Y z Complex.I‖ ≤ M * ‖Y z‖)
    (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (hSper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (δ : ℝ)
    (hwinS : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k →
      (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (νe ν : ℝ × ℝ → CauchyRiemannIndex.Vec 1)
    (hνe : ContDiffOn ℝ ∞ νe (Set.Ioi s₁ ×ˢ Set.univ))
    (hν : ContDiffOn ℝ ∞ ν (Set.Ioi s₁ ×ˢ Set.univ))
    (hνep : ∀ s > s₁, ∀ t : ℝ, νe (s, t + 1) = νe (s, t))
    (hνp : ∀ s > s₁, ∀ t : ℝ, ν (s, t + 1) = ν (s, t))
    (heqe : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S νe (s, t) = 0)
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ν (s, t) = 0)
    (B : ℝ) (hB : ∀ s > s₁, ∀ t : ℝ, ‖νe (s, t)‖ ≤ B)
    (s₂ : ℝ) (hw : ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (νe (s, t))) 1)
    (hrel : ∀ s > s₁, ∀ t : ℝ, vecToC (ν (s, t)) = Y (cylInf s t) * vecToC (νe (s, t)))
    (C₀ c₀ : ℝ) (hgrow : ∀ s > s₁, ∀ t : ℝ,
      ‖ν (s, t)‖ ≤ C₀ * Real.exp (δ * s) + c₀ * ‖νe (s, t)‖) :
    (∀ z, Y z = 0) ∨ ∀ z, Y z ≠ 0 := by
  sorry

end FiniteEnergyPlane
