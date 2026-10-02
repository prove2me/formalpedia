-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m_convex_cone_iff_polar_is_l_convex
-- name    : DiscreteConvex.ConjugacyDualityB.m_convex_cone_iff_polar_is_l_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:18.125995+00:00
-- url     : https://prove2.me/theorems/9d743c91-e7a5-4a80-bcd9-f8130171e7fa
-- title:
--   Theorem 8.5 -- m_convex_cone_iff_polar_is_l_convex
-- statement:
--   **Theorem 8.5** (p.210). A polyhedral cone is M-convex if and only if its polar cone is L-convex; hence the classes of M-convex cones and L-convex cones are in one-to-one correspondence under polarity.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Theorem 8.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Theorem 8.5

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsCone
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_PolarCone
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsMConvexCone
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsLConvexCone
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedronW

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.5 (p.210). A **polyhedral** cone is M-convex iff its polar cone is L-convex.
`IsCone` alone asks only for `0` and nonnegative scaling, and the backward direction then fails:
removing the ray `{x₁ = 0, x ≠ 0}` from the M-convex cone `{x₁ + x₂ + x₃ = 0, x₁ ≥ 0, x₂ ≥ 0}`
leaves the polar unchanged while the remainder is no M-convex polyhedron. -/
theorem m_convex_cone_iff_polar_is_l_convex (C : Set (V → ℝ)) (hC : IsCone C)
    (hpoly : IsPolyhedronW C) :
    IsMConvexCone C ↔ IsLConvexCone (PolarCone C) := by sorry

end DiscreteConvex.ConjugacyDualityB
