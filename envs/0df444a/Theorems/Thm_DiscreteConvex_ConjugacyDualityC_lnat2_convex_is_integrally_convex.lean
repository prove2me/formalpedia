-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_lnat2_convex_is_integrally_convex
-- name    : DiscreteConvex.ConjugacyDualityC.lnat2_convex_is_integrally_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:46:49.008786+00:00
-- url     : https://prove2.me/theorems/7d18bedc-02fa-4401-8dad-d7831892ffb2
-- title:
--   Theorem 8.42 -- lnat2_convex_is_integrally_convex
-- statement:
--   **Theorem 8.42** (p.231-232). GOAL. An L$^\natural_2$-convex function is integrally convex; in particular, an L$^\natural_2$-convex set is integrally convex.
--
--   The technically deepest result in this chunk: the book's own proof is an intricate two-page combinatorial argument (sorted fractional-part values, threshold sets, and an explicit representation of any point of the Minkowski sum as a convex combination of integer points within its own integral neighborhood) rather than a direct consequence of the M2-side analogue (Theorem 8.31, mission `29-ch08b-conjugacyduality`) — L2-convexity does not reduce to M2-convexity's proof technique.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.231-232, Theorem 8.42.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.231-232, Theorem 8.42

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvexFunction
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvex

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.42 (p.231-232). GOAL. An L♮₂-convex function is integrally convex; in particular,
an L♮₂-convex set is integrally convex. -/
theorem lnat2_convex_is_integrally_convex :
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → IsIntegrallyConvexFunction g) ∧
    (∀ D : Set (V → ℤ), LNat2ConvexSet D → IsIntegrallyConvex D) := by sorry

end DiscreteConvex.ConjugacyDualityC
