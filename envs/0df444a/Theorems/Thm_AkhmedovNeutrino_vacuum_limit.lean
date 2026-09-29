-- Prove2me | Theorems.Thm_AkhmedovNeutrino_vacuum_limit
-- name    : AkhmedovNeutrino.vacuum_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:16:41.367785+00:00
-- url     : https://prove2.me/theorems/e6f81be2-4f98-4843-94d3-c24245294dbc
-- title:
--   Zero-density limit: $\theta=\theta_0$, $l_m=l_{osc}$ (Sec. 8.2)
-- statement:
--   Let $\Delta m^2,\theta_0,G_F\in\mathbb R$ with $\Delta m^2\neq0$, and $E>0$. At zero electron density $N_e=0$:
--
--   1. the oscillation amplitude in matter (eq. (97)) reduces to the vacuum amplitude, $\sin^22\theta=\sin^22\theta_0$;
--   2. the oscillation length in matter (eq. (96)) reduces to the vacuum oscillation length (eq. (61)) in absolute value:
--   $$l_m=\Big|\frac{4\pi E}{\Delta m^2}\Big|=|l_{osc}|.$$
--
--   **Formalization Note** The source writes $l_m=l_{osc}$, tacitly with $\Delta m^2>0$; since $l_m=2\pi/\Delta_m$ is non-negative, the absolute value is needed for $\Delta m^2<0$.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, text after eq. (96), p. 31; eq. (61), p. 21

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem vacuum_limit (Δm2 E θ0 GF : ℝ) (hE : 0 < E) (hΔ : Δm2 ≠ 0) :
    matterOscAmplitude Δm2 E θ0 GF 0 = Real.sin (2 * θ0) ^ 2 ∧
    matterOscLength Δm2 E θ0 GF 0 = |vacuumOscLength Δm2 E| := by
  sorry
end AkhmedovNeutrino
