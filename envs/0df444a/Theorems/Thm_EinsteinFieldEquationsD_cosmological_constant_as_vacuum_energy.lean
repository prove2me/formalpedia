-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_cosmological_constant_as_vacuum_energy
-- name    : EinsteinFieldEquationsD.cosmological_constant_as_vacuum_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:17:31.788579+00:00
-- url     : https://prove2.me/theorems/5ac87ca5-0550-45ef-bb1c-3bc6042e5440
-- title:
--   Cosmological term as vacuum stress–energy
-- statement:
--   Let $\kappa\neq0$. For any fields $g,T$, any $\Lambda$ and any set $U$, the field equations $G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}$ hold on $U$ if and only if
--   $$G_{\mu\nu}=\kappa\big(T_{\mu\nu}+T^{(\mathrm{vac})}_{\mu\nu}\big)\quad\text{on }U,\qquad T^{(\mathrm{vac})}_{\mu\nu}=-\frac\Lambda\kappa g_{\mu\nu}.$$
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Cosmological constant'

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem cosmological_constant_as_vacuum_energy {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D)) (Λ κ : ℝ) (hκ : κ ≠ 0) :
    EinsteinFieldEquationsOn g T Λ κ U ↔
      ∀ x ∈ U, ∀ a b : Fin D,
        einsteinTensor g x a b = κ * (T x a b + vacuumStressEnergy g Λ κ x a b) := by sorry

end EinsteinFieldEquationsD
