-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_einsteinTensor_symm
-- name    : EinsteinFieldEquationsD.einsteinTensor_symm
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:11:33.747121+00:00
-- url     : https://prove2.me/theorems/be11952b-6b75-4561-a1d6-2b169919b96a
-- title:
--   Symmetry of the Einstein tensor
-- statement:
--   Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$. Then the Einstein tensor $G_{\mu\nu}=R_{\mu\nu}-\tfrac12Rg_{\mu\nu}$ is symmetric at every point of $U$:
--   $$G_{\mu\nu}(x)=G_{\nu\mu}(x)\qquad(x\in U).$$
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Mathematical form'

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem einsteinTensor_symm {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ a b : Fin D, einsteinTensor g x a b = einsteinTensor g x b a := by sorry

end EinsteinFieldEquationsD
