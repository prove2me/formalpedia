-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reflect_of_norm_dbar_le
-- name    : FiniteEnergyPlane.exists_lipschitzOnWith_reflect_of_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-27T00:15:36.14257+00:00
-- url     : https://prove2.me/theorems/7129a858-3f0b-463b-9c5a-e42169d3da7e
-- title:
--   Reflection of a Cauchy-Riemann type solution with real boundary values across the unit circle
-- statement:
--   Let $z_1$ be a point of the unit circle, $r>0$, and $D=\{|z|\le 1\}\cap\{|z-z_1|<r\}$. Let $g$ be $C^1$ on $D$ with $|\partial_s g + i\,\partial_t g|\le M|g|$ at the interior points $\{|z|<1\}\cap\{|z-z_1|<r\}$, and real on the arc $\{|z|=1\}\cap\{|z-z_1|<r\}$. Define the reflection $G(z)=g(z)$ for $|z|\le 1$ and $G(z)=\overline{g(1/\bar z)}$ for $|z|>1$. Then there are $\rho>0$, $K\ge 0$ and $M'$ such that $G$ is $K$-Lipschitz on the disk $\{|z-z_1|<\rho\}$ and $|\partial_s G + i\,\partial_t G|\le M'|G|$ almost everywhere on that disk (with the Fréchet derivative, taken as $0$ where $G$ is not differentiable).
--
--   Role: extends a solution of a Cauchy–Riemann type inequality with real boundary values on a circular arc to a full neighbourhood of a boundary point, so that interior results for Lipschitz solutions apply at boundary points.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), Theorem 4.4 (boundary part); I. N. Vekua, Generalized Analytic Functions (1962), Ch. III

import Definitions.Def_FiniteEnergyPlane_Setting

open Metric MeasureTheory
open scoped NNReal

namespace FiniteEnergyPlane

/-- Let `z₁` lie on the unit circle, `r > 0`, and let `g` be `C¹` on `closedBall 0 1 ∩ ball z₁ r`, with
`|∂ₛg + i ∂ₜg| ≤ M |g|` at the interior points and `g` real on the arc `sphere 0 1 ∩ ball z₁ r`. Then the
reflection `G z = g z` for `‖z‖ ≤ 1`, `G z = conj (g (conj z)⁻¹)` for `‖z‖ > 1`, is Lipschitz on some ball
around `z₁` and satisfies `|∂ₛG + i ∂ₜG| ≤ M' |G|` almost everywhere there. -/
theorem exists_lipschitzOnWith_reflect_of_norm_dbar_le (g : ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ 1 g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) :
    ∃ ρ > (0 : ℝ), ∃ K : ℝ≥0, ∃ M' : ℝ,
      LipschitzOnWith K
        (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) (ball z₁ ρ) ∧
      ∀ᵐ z ∂(volume.restrict (ball z₁ ρ)),
        ‖fderiv ℝ (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z 1 +
            Complex.I * fderiv ℝ
              (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z
              Complex.I‖ ≤
          M' * ‖(fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z‖ := by
  sorry

end FiniteEnergyPlane
