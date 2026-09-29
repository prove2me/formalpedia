-- Prove2me | Theorems.Thm_AkhmedovNeutrino_matter_eigenstates
-- name    : AkhmedovNeutrino.matter_eigenstates
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:13:47.79952+00:00
-- url     : https://prove2.me/theorems/7752ee3a-f349-4f5c-ba91-2a32f31286cc
-- title:
--   Matter eigenstates and eigenenergy difference (eqs. (92), (94))
-- statement:
--   Let $\Delta m^2,\theta_0,G_F,N_e,\theta\in\mathbb R$, $E>0$, $a=\Delta m^2/(2E)$, $V_{CC}=\sqrt2G_FN_e$, and let $\Delta_m$ be the energy gap in matter (eq. (94)). Assume that $\theta$ is a matter mixing angle in the sense of eq. (93):
--   $$\Delta_m\cos2\theta=a\cos2\theta_0-V_{CC},\qquad \Delta_m\sin2\theta=a\sin2\theta_0 .$$
--   Then, with $H$ the MSW Hamiltonian of eq. (91),
--   $$H\begin{pmatrix}\cos\theta\\-\sin\theta\end{pmatrix}=\frac{V_{CC}-\Delta_m}{2}\begin{pmatrix}\cos\theta\\-\sin\theta\end{pmatrix},\qquad H\begin{pmatrix}\sin\theta\\\cos\theta\end{pmatrix}=\frac{V_{CC}+\Delta_m}{2}\begin{pmatrix}\sin\theta\\\cos\theta\end{pmatrix}.$$
--   So $H$ is diagonalized by the rotation through $\theta$, and the two eigenenergies in matter differ by exactly $\Delta_m$, eq. (94).
--
--   **Formalization Note** The source's eq. (92) writes the eigenstates as field combinations $\nu_A=\nu_e\cos\theta+\nu_\mu\sin\theta$, $\nu_B=-\nu_e\sin\theta+\nu_\mu\cos\theta$. Here the eigenvectors are flavour-amplitude vectors, with the sign convention that reduces to the vacuum relation (57) at zero density; the eigenvalue difference (94) does not depend on this convention.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, eqs. (92) and (94), p. 31

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem matter_eigenstates (Δm2 E θ0 GF Ne θ : ℝ) (hE : 0 < E)
    (hcos : matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
      Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)
    (hsin : matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
      Δm2 / (2 * E) * Real.sin (2 * θ0)) :
    (mswHamiltonian Δm2 E θ0 GF Ne).mulVec ![Real.cos θ, -Real.sin θ] =
        ((ccPotential GF Ne - matterEnergyGap Δm2 E θ0 GF Ne) / 2) •
          ![Real.cos θ, -Real.sin θ] ∧
    (mswHamiltonian Δm2 E θ0 GF Ne).mulVec ![Real.sin θ, Real.cos θ] =
        ((ccPotential GF Ne + matterEnergyGap Δm2 E θ0 GF Ne) / 2) •
          ![Real.sin θ, Real.cos θ] := by
  sorry
end AkhmedovNeutrino
