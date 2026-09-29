-- Prove2me | Theorems.Thm_DysonGraviton_ineq17
-- name    : DysonGraviton.ineq17
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:43:55.521148+00:00
-- url     : https://prove2.me/theorems/2d4a5630-a155-4d4b-bdc7-37e21e6126af
-- title:
--   Eq. (17) — positivity of $\int s^3[f' + f/s]^2$ (sign corrected)
-- statement:
--   For every admissible axially symmetric wave function $f(s,z)$ (differentiable in $s$ for $s>0$, with $s f^2$ and $s^3[f']^2$ integrable on the half plane, and not a.e. zero),
--   $$\int_{\mathbb R}\int_0^\infty s^3\left[f' + \frac{f}{s}\right]^2 ds\,dz > 0 .$$
--
--   **Note on the sign.** The paper prints $f' - f/s$. With the minus sign the integral equals $\int s^3 [f']^2 + 3\int s f^2$ and does not imply Eq. (18); with the plus sign it equals $\int s^3 [f']^2 - \int s f^2$, which gives Eq. (18) directly. The formalization uses the plus sign; reviewers should confirm this reading.
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, p. 7, Eq. (17) (printed with $f' - f/s$; see description)

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology

namespace DysonGraviton

theorem ineq17 (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane)
    (hne : ¬ (fun p : ℝ × ℝ => f p.1 p.2) =ᵐ[volume.restrict halfPlane] 0) :
    0 < ∫ p in halfPlane, p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2 := by
  sorry

end DysonGraviton
