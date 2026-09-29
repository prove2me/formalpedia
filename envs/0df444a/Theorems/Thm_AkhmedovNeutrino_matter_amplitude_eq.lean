-- Prove2me | Theorems.Thm_AkhmedovNeutrino_matter_amplitude_eq
-- name    : AkhmedovNeutrino.matter_amplitude_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:14:23.249513+00:00
-- url     : https://prove2.me/theorems/46708c97-1816-45e8-abd0-ad96a3e296c4
-- title:
--   Oscillation amplitude in matter $\sin^2 2\theta$ (eq. (97))
-- statement:
--   Let $\Delta m^2,\theta_0,G_F,N_e,\theta\in\mathbb R$, $E>0$, $a=\Delta m^2/(2E)$, $V_{CC}=\sqrt2G_FN_e$, and suppose the energy gap in matter $\Delta_m$ (eq. (94)) is non-zero. If $\theta$ satisfies
--   $$\Delta_m\cos2\theta=a\cos2\theta_0-V_{CC},\qquad \Delta_m\sin2\theta=a\sin2\theta_0,$$
--   then
--   $$\sin^22\theta=\frac{a^2\sin^22\theta_0}{(a\cos2\theta_0-V_{CC})^2+a^2\sin^22\theta_0}.$$
--   This identifies the amplitude appearing in the transition probability (95) with the explicit resonance-shaped expression (97).
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, eq. (97), p. 31

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem matter_amplitude_eq (Δm2 E θ0 GF Ne θ : ℝ) (hE : 0 < E)
    (hgap : matterEnergyGap Δm2 E θ0 GF Ne ≠ 0)
    (hcos : matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
      Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)
    (hsin : matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
      Δm2 / (2 * E) * Real.sin (2 * θ0)) :
    Real.sin (2 * θ) ^ 2 = matterOscAmplitude Δm2 E θ0 GF Ne := by
  sorry
end AkhmedovNeutrino
