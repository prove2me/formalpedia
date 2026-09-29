-- Prove2me | Theorems.Thm_DysonGraviton_Q_gt_half
-- name    : DysonGraviton.Q_gt_half
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:46:49.06954+00:00
-- url     : https://prove2.me/theorems/66dbf165-a097-4cc9-a349-ca7829fd0f5d
-- title:
--   Eq. (18) — the quadrupole factor satisfies $Q > 1/2$
-- statement:
--   Let $f(s,z)$ be the wave function of an electron with zero angular momentum about the $z$-axis, in cylindrical coordinates. Assume $f(\cdot,z)$ is differentiable at every $s > 0$, that $s f^2$ and $s^3 [f']^2$ are integrable over the half plane $\{s>0\}\times\mathbb R$, and that $f$ is not almost everywhere zero there. Then the quadrupole factor of Eq. (16) satisfies
--   $$Q = \frac{\int\!\!\int s^3 [f']^2\, ds\, dz}{2\int\!\!\int s f^2\, ds\, dz} > \frac12 .$$
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, p. 7, Eqs. (16)–(18)

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology

namespace DysonGraviton

theorem Q_gt_half (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane)
    (hne : ¬ (fun p : ℝ × ℝ => f p.1 p.2) =ᵐ[volume.restrict halfPlane] 0) :
    1 / 2 < Q f := by
  sorry

end DysonGraviton
