-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_Lagrange_weak_duality
-- name    : DiscreteConvex.ConjugacyDuality.Lagrange.weak_duality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:15:18.759621+00:00
-- url     : https://prove2.me/theorems/1177b483-70bf-4280-8909-ce68f2d663e3
-- title:
--   Theorem 8.52 -- weak duality
-- statement:
--   **Theorem 8.52** (p.237). $\inf(P) \ge \sup(D)$: the primal optimal value is always at least the dual optimal value, for any perturbation $F$ (no biconjugacy hypothesis needed). This holds in far greater generality than the M-convex setting the chapter specializes to, and is the baseline the saddle-point and strong-duality theorems sharpen to equality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Theorem 8.52.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Theorem 8.52

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- Theorem 8.52, weak duality (Murota, *Discrete Convex Analysis*, SIAM 2003, p.237).
`inf(P) ≥ sup(D)`. -/
theorem weak_duality {V U : Type*} [Fintype U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) :
    InfP F ≥ SupD F := by sorry

end DiscreteConvex.ConjugacyDuality.Lagrange
