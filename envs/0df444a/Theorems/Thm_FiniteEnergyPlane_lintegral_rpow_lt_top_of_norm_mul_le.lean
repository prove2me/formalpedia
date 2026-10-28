-- Prove2me | Theorems.Thm_FiniteEnergyPlane_lintegral_rpow_lt_top_of_norm_mul_le
-- name    : FiniteEnergyPlane.lintegral_rpow_lt_top_of_norm_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:14:37.364976+00:00
-- url     : https://prove2.me/theorems/bd1d8903-42ff-40a5-ace7-cc01da9ae6fb
-- title:
--   Higher integrability from a 1/|z| bound and power decay of the L² mass
-- statement:
--   Let $r>0$, $\mu>0$, and let $g\ge 0$ be a measurable function on the disc $B_r=\{|z|<r\}\subset\mathbb{C}$ such that
--   $$|z|\,g(z)\le C\quad(0<|z|<r),\qquad \int_{|z|<s}g^2\,dz\le K\,s^{2\mu}\quad(0<s\le r).$$
--   Then
--   $$\int_{B_r}g^p\,dz<\infty\qquad\text{for every }2\le p<2+2\mu .$$
--
--   A function with a $1/|z|$ bound whose $L^2$ mass on small discs decays like a power of the radius has strictly better than square integrability. This is used for derivatives of maps near a puncture.
--
--   **Formalization Note** The integrals are lower integrals in `ℝ≥0∞` of `ENNReal.ofReal (g z ^ 2)` and `ENNReal.ofReal (g z ^ p)` with real powers; `g` is `AEMeasurable` for the restriction of Lebesgue measure to `ball 0 r`.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, proof of Proposition 4.8

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Higher integrability from a `1/|z|` bound and power decay of the `L²` mass. Let `g ≥ 0` be
measurable on the disc of radius `r > 0` about `0`, with `|z| g(z) ≤ C` for `0 < |z| < r` and
`∫_{|z| < s} g² ≤ K s^{2μ}` for `0 < s ≤ r`, where `μ > 0`. Then `∫_{|z| < r} g^p < ∞` for every
`2 ≤ p < 2 + 2μ`. -/
theorem lintegral_rpow_lt_top_of_norm_mul_le (g : ℂ → ℝ) {r C K μ : ℝ} (hr : 0 < r)
    (hμ : 0 < μ) (hg0 : ∀ z, 0 ≤ g z) (hg : AEMeasurable g (volume.restrict (ball 0 r)))
    (hbd : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * g z ≤ C)
    (hdec : ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (g z ^ 2) ≤ ENNReal.ofReal (K * s ^ (2 * μ)))
    (p : ℝ) (hp2 : 2 ≤ p) (hp : p < 2 + 2 * μ) :
    ∫⁻ z in ball 0 r, ENNReal.ofReal (g z ^ p) < ⊤ := by
  sorry

end FiniteEnergyPlane
