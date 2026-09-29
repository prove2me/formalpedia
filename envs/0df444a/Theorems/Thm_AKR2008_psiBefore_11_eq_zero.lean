-- Prove2me | Theorems.Thm_AKR2008_psiBefore_11_eq_zero
-- name    : AKR2008.psiBefore_11_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:12:28.47877+00:00
-- url     : https://prove2.me/theorems/0a943858-8582-474c-823d-cf14cce2e307
-- title:
--   Parallel vertical component of singlet state vanishes
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$. In the pre-measurement EPR singlet state, the component along $|1\rangle_1 |1\rangle_2$ vanishes identically:
--
--   $$ (\Psi_0)_{11} = 0. $$
--
--   This reflects the antisymmetric nature of the singlet state, which forbids both photons from simultaneously occupying the vertical polarization state.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (1)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem psiBefore_11_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 1 1 = 0 := by sorry

end AKR2008
