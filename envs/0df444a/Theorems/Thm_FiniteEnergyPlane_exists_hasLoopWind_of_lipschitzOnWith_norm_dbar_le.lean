-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le
-- name    : FiniteEnergyPlane.exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-27T00:15:37.439689+00:00
-- url     : https://prove2.me/theorems/7ae99f29-36e4-5c6f-81a8-e08c5f73ee35
-- title:
--   Zeros of Lipschitz solutions of a Cauchy-Riemann type inequality are isolated with positive winding
-- statement:
--   Let $g:\mathbb C\to\mathbb C$ be $K$-Lipschitz on the disk $B(z_0,\rho)$ and satisfy $|\partial_s g + i\,\partial_t g|\le M|g|$ almost everywhere on it (with the Fréchet derivative, taken as $0$ where $g$ is not differentiable). Suppose $g(z_0)=0$ and $g$ takes nonzero values arbitrarily close to $z_0$. Then there are an integer $m\ge 1$ and $0<r\le\rho$ such that $g$ has no zero in $B(z_0,r)\setminus\{z_0\}$ and, for every $0<\rho'<r$, the loop $t\mapsto g(z_0+\rho' e^{2\pi i t})$ has winding number $m$.
--
--   Role: the isolated-zero and positive-winding property of solutions of Cauchy–Riemann type inequalities, for functions that are only Lipschitz (for example reflections across a boundary curve), where smooth versions do not apply.
-- source:
--   I. N. Vekua, Generalized Analytic Functions (1962), Ch. III (similarity principle); C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, § 2.13

import Definitions.Def_FiniteEnergyPlane_Winding

open Metric MeasureTheory Filter Topology
open scoped NNReal

namespace FiniteEnergyPlane

/-- Let `g : ℂ → ℂ` be Lipschitz on `ball z₀ ρ` with `|∂ₛg + i ∂ₜg| ≤ M |g|` almost everywhere there. If
`g z₀ = 0` and `g` takes nonzero values arbitrarily close to `z₀`, then `z₀` is an isolated zero of `g` and the
loops `t ↦ g (z₀ + ρ' e^{2πit})` on all small circles have the same winding number `m ≥ 1`. -/
theorem exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ℝ≥0) (hg : LipschitzOnWith K g (ball z₀ ρ)) (M : ℝ)
    (hM : ∀ᵐ z ∂(volume.restrict (ball z₀ ρ)),
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hg₀ : g z₀ = 0) (hfreq : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), r ≤ ρ ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → g z ≠ 0) ∧
      ∀ ρ' ∈ Set.Ioo 0 r, HasLoopWind (fun t => g (z₀ + ccwLoop ρ' t)) m := by
  sorry

end FiniteEnergyPlane
