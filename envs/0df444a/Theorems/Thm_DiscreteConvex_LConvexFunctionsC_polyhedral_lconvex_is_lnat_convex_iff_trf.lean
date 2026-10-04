-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_lconvex_is_lnat_convex_iff_trf
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_is_lnat_convex_iff_trf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:38:33.618822+00:00
-- url     : https://prove2.me/theorems/71fc9957-4b82-49ec-95c9-7a3e59f90263
-- title:
--   Theorem 7.30 -- polyhedral_lconvex_is_lnat_convex_iff_trf
-- statement:
--   **Theorem 7.30** (p.192). A polyhedral L-convex function is polyhedral L$^\natural$-convex. Conversely, a polyhedral L$^\natural$-convex function is polyhedral L-convex if and only if it satisfies (TRF[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.30.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.30

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.30 (p.192). A polyhedral L-convex function is polyhedral L♮-convex; conversely a
polyhedral L♮-convex function is polyhedral L-convex iff it satisfies (TRF[R]). -/
theorem polyhedral_lconvex_is_lnat_convex_iff_trf (g : (V → ℝ) → WithTop ℝ) :
    ((SBFR g ∧ TRFR g) → LNaturalConvexR g) ∧ (LNaturalConvexR g → (TRFR g → SBFR g)) := by sorry

end DiscreteConvex.LConvexFunctionsC
