-- Prove2me | Theorems.Thm_AkhmedovNeutrino_msw_resonance
-- name    : AkhmedovNeutrino.msw_resonance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:14:49.743978+00:00
-- url     : https://prove2.me/theorems/9cb0d1a1-5b0b-423d-b415-fe11acd139f8
-- title:
--   MSW resonance: $\sin^22\theta\le1$, with equality iff $\sqrt2G_FN_e=\frac{\Delta m^2}{2E}\cos2\theta_0$ (eq. (98))
-- statement:
--   Let $\Delta m^2,\theta_0,G_F,N_e\in\mathbb R$, $E>0$, $a=\Delta m^2/(2E)$, $V_{CC}=\sqrt2G_FN_e$, and let
--   $$\sin^22\theta=\frac{a^2\sin^22\theta_0}{(a\cos2\theta_0-V_{CC})^2+a^2\sin^22\theta_0}$$
--   be the oscillation amplitude in matter (eq. (97)). Then
--
--   1. $\sin^22\theta\le1$;
--   2. if $a\sin2\theta_0\neq0$, then $\sin^22\theta=1$ if and only if the MSW resonance condition holds:
--   $$\sqrt2\,G_FN_e=\frac{\Delta m^2}{2E}\cos2\theta_0 .$$
--
--   At resonance the mixing in matter is maximal regardless of how small the vacuum mixing angle is.
--
--   **Formalization Note** The hypothesis $a\sin2\theta_0\ne0$ excludes the no-mixing case, in which the amplitude is identically $0$ (with the convention $0/0=0$).
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, eq. (98) and surrounding text, pp. 31-32

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem msw_resonance (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E) :
    matterOscAmplitude Δm2 E θ0 GF Ne ≤ 1 ∧
    (Δm2 / (2 * E) * Real.sin (2 * θ0) ≠ 0 →
      (matterOscAmplitude Δm2 E θ0 GF Ne = 1 ↔
        ccPotential GF Ne = Δm2 / (2 * E) * Real.cos (2 * θ0))) := by
  sorry
end AkhmedovNeutrino
