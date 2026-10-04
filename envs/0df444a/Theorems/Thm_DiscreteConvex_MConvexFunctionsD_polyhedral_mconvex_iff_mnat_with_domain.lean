-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_mconvex_iff_mnat_with_domain
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_mconvex_iff_mnat_with_domain
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:45.709411+00:00
-- url     : https://prove2.me/theorems/6b865213-9fab-4c56-a2b0-adb4e9d7539d
-- title:
--   Theorem 6.48 -- polyhedral_mconvex_iff_mnat_with_domain
-- statement:
--   **Theorem 6.48** (p.162). A polyhedral M-convex function is polyhedral M$^\natural$-convex. Conversely, a polyhedral M$^\natural$-convex function is polyhedral M-convex if and only if its effective domain is contained in $\{x:x(V)=r\}$ for some $r\in\mathbb R$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, Theorem 6.48.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, Theorem 6.48

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.48 (p.181). -/
theorem polyhedral_mconvex_iff_mnat_with_domain (g : (V → ℝ) → WithTop ℝ) :
    (MExchangeAxiomR g → MNaturalConvexR g) ∧
    (MNaturalConvexR g → (MExchangeAxiomR g ↔ ∃ r : ℝ, ∀ x ∈ DomR g, ∑ v, x v = r)) := by sorry

end DiscreteConvex.MConvexFunctionsD
