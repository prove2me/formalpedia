-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_vacuum_field_equations_iff
-- name    : EinsteinFieldEquationsD.vacuum_field_equations_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:15:14.514773+00:00
-- url     : https://prove2.me/theorems/09b144de-7744-4ddb-baac-65bdc52db925
-- title:
--   Vacuum field equations: Einstein-manifold form
-- statement:
--   Let $D\neq2$, let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$, $x\in U$, and suppose $T_{\mu\nu}(x)=0$. Then at $x$ the field equations are equivalent to the vacuum (Einstein-manifold) equations
--   $$R_{\mu\nu}=\frac{\Lambda}{\frac D2-1}\,g_{\mu\nu},$$
--   which for $\Lambda=0$ read $R_{\mu\nu}=0$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Vacuum field equations'

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem vacuum_field_equations_iff {D : ℕ} (hD : D ≠ 2) (g T : Tensor2 D) (U : Set (Coord D)) (Λ κ : ℝ)
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (hT : ∀ a b : Fin D, T x a b = 0) :
    (∀ a b : Fin D, einsteinTensor g x a b + Λ * g x a b = κ * T x a b) ↔
      (∀ a b : Fin D, ricci g x a b = Λ / ((D : ℝ) / 2 - 1) * g x a b) := by sorry

end EinsteinFieldEquationsD
