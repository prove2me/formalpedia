-- Prove2me | Theorems.Thm_AKR2008_psiBefore_00_eq_zero
-- name    : AKR2008.psiBefore_00_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:12:13.655983+00:00
-- url     : https://prove2.me/theorems/988307ba-0efb-45ca-adee-32e0c87f96f4
-- title:
--   Parallel horizontal component of singlet state vanishes
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$. In the pre-measurement EPR singlet state, the component along $|0\rangle_1 |0\rangle_2$ vanishes identically:
--
--   $$ (\Psi_0)_{00} = 0. $$
--
--   This reflects the antisymmetric nature of the singlet state, which forbids both photons from simultaneously occupying the horizontal polarization state.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (1)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem psiBefore_00_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 0 0 = 0 := by sorry

end AKR2008
