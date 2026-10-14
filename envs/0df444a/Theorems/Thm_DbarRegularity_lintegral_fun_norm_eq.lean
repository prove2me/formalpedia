-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_fun_norm_eq
-- name    : DbarRegularity.lintegral_fun_norm_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:27:38.976028+00:00
-- url     : https://prove2.me/theorems/5d737367-1e51-4ce8-97b4-3d0e905f0eda
-- title:
--   Lower Lebesgue integral of a radial function on R^d
-- statement:
--   Let $d\ge1$ and let $F:\mathbb{R}\to[0,\infty]$ be measurable. Then
--   $$\int_{\mathbb{R}^d}F(|x|)\,dx \;=\; d\,|B(0,1)|\int_0^\infty r^{d-1}F(r)\,dr ,$$
--   where $|B(0,1)|$ is the Lebesgue measure of the unit ball. Both sides may be $+\infty$.
--
--   This is the radial integration formula for nonnegative functions, in the form of lower Lebesgue integrals, complementing Mathlib's Bochner-integral version `integral_fun_norm_addHaar`.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; the integrals are lower Lebesgue integrals `∫⁻` with values in `ℝ≥0∞`; $d\,|B(0,1)|$ is `(d : ℝ≥0∞) * volume (ball 0 1)` and $r^{d-1}$ is `ENNReal.ofReal (r ^ (d - 1))` (natural-number exponent); the radial integral is over `Ioi 0`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Lower Lebesgue integral of a radial function on `ℝ^d`, `d ≥ 1`:
`∫ F(|x|) dx = d |B(0,1)| ∫₀^∞ r^{d-1} F(r) dr` for measurable `F : ℝ → [0, ∞]`. -/
theorem lintegral_fun_norm_eq {d : ℕ} (hd : 0 < d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d), F ‖x‖ =
      d * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r := by sorry

end DbarRegularity
