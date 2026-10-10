-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_einsteinTensor_divergence_free
-- name    : EinsteinFieldEquationsD.einsteinTensor_divergence_free
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:13:45.619+00:00
-- url     : https://prove2.me/theorems/46aff207-2a19-4149-982f-f9a6f059d7fe
-- title:
--   Contracted Bianchi identity: the Einstein tensor is divergence-free
-- statement:
--   Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$. Then the Einstein tensor is divergence-free on $U$:
--   $$g^{\beta\lambda}\nabla_\lambda G_{\alpha\beta}=0,$$
--   the index-lowered form of $G^{\alpha\beta}{}_{;\beta}=0$ (contracted Bianchi identity).
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Features — Conservation of energy and momentum', derivation box

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem einsteinTensor_divergence_free {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ a : Fin D, divergence g (einsteinTensor g) x a = 0 := by sorry

end EinsteinFieldEquationsD
