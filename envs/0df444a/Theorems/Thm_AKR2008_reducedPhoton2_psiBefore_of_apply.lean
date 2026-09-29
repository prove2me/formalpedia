-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_of_apply
-- name    : AKR2008.reducedPhoton2_psiBefore_of_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:32:48.531988+00:00
-- url     : https://prove2.me/theorems/a79be1ee-4163-478a-86e0-3701baa5570c
-- title:
--   Reduced state equality from entrywise agreement
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector. If the reduced density matrix $\rho_2(\Psi_0)$ agrees entrywise with $\hat\rho$ for all $j, j' \in \{0, 1\}$, then the two density operators are identical:
--
--   $$ \rho_2(\Psi_0) = \hat\rho. $$
--
--   This follows from matrix extensionality on the $2 \times 2$ matrix algebra over $\mathbb C$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_of_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h_entry : ∀ j j', reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j') :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat := by sorry

end AKR2008
