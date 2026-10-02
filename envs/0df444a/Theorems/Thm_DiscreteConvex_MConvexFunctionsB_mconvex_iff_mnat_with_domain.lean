-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_iff_mnat_with_domain
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_iff_mnat_with_domain
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:21.228564+00:00
-- url     : https://prove2.me/theorems/191cc676-baf2-4c65-8ee8-2c5d751df72e
-- title:
--   Theorem 6.3 -- mconvex_iff_mnat_with_domain
-- statement:
--   **Theorem 6.3** (p.135). An M-convex function is M$^\natural$-convex. Conversely, an M$^\natural$-convex function is M-convex if and only if its effective domain is contained in $\{x \in \mathbb Z^V : x(V)=r\}$ for some $r \in \mathbb Z$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Theorem 6.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Theorem 6.3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.135, Theorem 6.3, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.3 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.135). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_iff_mnat_with_domain {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → MNaturalConvex f) ∧
    (MNaturalConvex f → (MExchangeAxiom f ↔ ∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r)) := by sorry

end DiscreteConvex.MConvexFunctionsB
