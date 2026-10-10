-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_vacuumStressEnergy_eq_perfectFluid
-- name    : EinsteinFieldEquationsD.vacuumStressEnergy_eq_perfectFluid
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:19:13.092584+00:00
-- url     : https://prove2.me/theorems/8b4b8ce8-104a-463b-bd8f-d92c06110506
-- title:
--   Vacuum energy density and pressure
-- statement:
--   The vacuum stress–energy tensor $T^{(\mathrm{vac})}_{\mu\nu}=-\frac\Lambda\kappa g_{\mu\nu}$ is the stress–energy tensor of a perfect fluid with constant energy density and isotropic pressure
--   $$\rho_{\mathrm{vac}}=-p_{\mathrm{vac}}=\frac\Lambda\kappa,$$
--   for any velocity field $u$: $T^{(\mathrm{vac})}_{\mu\nu}=(\rho_{\mathrm{vac}}+p_{\mathrm{vac}})u_\mu u_\nu+p_{\mathrm{vac}}g_{\mu\nu}$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Cosmological constant'

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem vacuumStressEnergy_eq_perfectFluid {D : ℕ} (g : Tensor2 D) (Λ κ : ℝ) (u : Coord D → Fin D → ℝ) :
    vacuumStressEnergy g Λ κ = perfectFluid g (Λ / κ) (-(Λ / κ)) u := by sorry

end EinsteinFieldEquationsD
