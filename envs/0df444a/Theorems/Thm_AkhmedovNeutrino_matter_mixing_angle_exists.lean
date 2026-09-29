-- Prove2me | Theorems.Thm_AkhmedovNeutrino_matter_mixing_angle_exists
-- name    : AkhmedovNeutrino.matter_mixing_angle_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:09:11.422669+00:00
-- url     : https://prove2.me/theorems/5f53bf9d-5710-49c9-a25e-34d6e83479ac
-- title:
--   Mixing angle in matter: $\tan 2\theta = \frac{(\Delta m^2/2E)\sin2\theta_0}{(\Delta m^2/2E)\cos2\theta_0-\sqrt2G_FN_e}$ (eq. (93))
-- statement:
--   Let $\Delta m^2,\theta_0,G_F,N_e\in\mathbb R$ and $E>0$; put $a=\Delta m^2/(2E)$, $V_{CC}=\sqrt2G_FN_e$ and let $\Delta_m=\sqrt{(a\cos2\theta_0-V_{CC})^2+a^2\sin^22\theta_0}$ be the energy gap in matter. Then there exists an angle $\theta\in\mathbb R$ such that
--   $$\Delta_m\cos2\theta=a\cos2\theta_0-V_{CC},\qquad \Delta_m\sin2\theta=a\sin2\theta_0,$$
--   and, whenever $a\cos2\theta_0-V_{CC}\neq0$,
--   $$\tan2\theta=\frac{a\sin2\theta_0}{a\cos2\theta_0-V_{CC}}.$$
--
--   This is the mixing angle in matter of eq. (93). When $\Delta_m>0$ the two equations for $\cos2\theta$ and $\sin2\theta$ determine $2\theta$ modulo $2\pi$, which the tangent formula alone does not.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, eq. (93), p. 31

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem matter_mixing_angle_exists (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E) :
    ∃ θ : ℝ,
      matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
          Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne ∧
      matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
          Δm2 / (2 * E) * Real.sin (2 * θ0) ∧
      (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne ≠ 0 →
        Real.tan (2 * θ) = Δm2 / (2 * E) * Real.sin (2 * θ0) /
          (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)) := by
  sorry
end AkhmedovNeutrino
