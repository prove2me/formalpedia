-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_differential_bianchi_identity
-- name    : EinsteinFieldEquationsD.differential_bianchi_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:35.40426+00:00
-- url     : https://prove2.me/theorems/825e611a-f1f5-4031-8e78-513742007a8c
-- title:
--   Differential Bianchi identity
-- statement:
--   Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$. Then the Riemann tensor satisfies the differential (second) Bianchi identity on $U$:
--   $$\nabla_\varepsilon R^\mu{}_{\alpha\beta\gamma}+\nabla_\beta R^\mu{}_{\alpha\gamma\varepsilon}+\nabla_\gamma R^\mu{}_{\alpha\varepsilon\beta}=0,$$
--   i.e. $R^\mu{}_{\alpha[\beta\gamma;\varepsilon]}=0$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Features — Conservation of energy and momentum', derivation box, first display

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem differential_bianchi_identity {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ e m a b c : Fin D,
      covDerivRiemann g x e m a b c + covDerivRiemann g x b m a c e
        + covDerivRiemann g x c m a e b = 0 := by sorry

end EinsteinFieldEquationsD
