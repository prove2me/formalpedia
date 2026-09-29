-- Prove2me | Theorems.Thm_AKR2008_photon2_same_reduced_state
-- name    : AKR2008.photon2_same_reduced_state
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:34:42.895777+00:00
-- url     : https://prove2.me/theorems/217a4388-a230-4f35-822c-998d3a18d513
-- title:
--   No signalling in the Eppley–Hannah EPR set-up: photon 2 is in the same state $\hat\rho$ before and after the measurement of photon 1
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (the detector), and let $\Phi_0,\Phi_\uparrow,\Phi_\downarrow\in\mathcal H$ be unit vectors: $\Phi_0$ is the initial (switched-off) detector state and $\Phi_\uparrow$, $\Phi_\downarrow$ are the detector states after recording horizontal, resp. vertical, polarization of photon 1. Consider the joint states of photon 1, photon 2 and the detector before and after the measurement,
--   $$|\Psi_0\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2 - |\downarrow\rangle_1|\uparrow\rangle_2\bigr)|\Phi_0\rangle,\qquad |\Psi\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2|\Phi_\uparrow\rangle - |\downarrow\rangle_1|\uparrow\rangle_2|\Phi_\downarrow\rangle\bigr).$$
--   Then both lead to the same reduced density operator of photon 2:
--   $$\rho_2(\Psi_0) = \hat\rho \quad\text{and}\quad \rho_2(\Psi) = \hat\rho, \qquad \hat\rho = \tfrac12\bigl(|\uparrow\rangle_2\langle\uparrow|_2 + |\downarrow\rangle_2\langle\downarrow|_2\bigr).$$
--
--   This is the statement on which the paper bases its rebuttal of the superluminal-signalling branch of the Eppley–Hannah argument: a probe (such as a classical gravitational wave) interacting with photon 2 alone sees the same mixed state whether or not photon 1 has been measured.
--
--   **Formalization Note** The detector states are only required to be unit vectors; see the mission description for the representation of the tensor product and the partial trace.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-2, Sec. II, Eqs. (1)–(3) and the sentence "This leads for both (1) and (2) to the same density operator for photon 2"

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem photon2_same_reduced_state
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ Φup Φdown : H) (h₀ : ‖Φ₀‖ = 1) (hup : ‖Φup‖ = 1) (hdown : ‖Φdown‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat ∧ reducedPhoton2 (psiAfter Φup Φdown) = rhoHat := by
  sorry

end AKR2008
