-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_swgs_characterizes_mnat_convex
-- name    : DiscreteConvex.MConvexFunctionsC.swgs_characterizes_mnat_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:43:37.045741+00:00
-- url     : https://prove2.me/theorems/38c4d4c0-918d-4088-8b4d-e31c16a7d6e9
-- title:
--   Theorem 6.36 -- swgs_characterizes_mnat_convex
-- statement:
--   **Theorem 6.36** (p.155). For a convex-extensible function $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ with nonempty effective domain, $f$ is M$^\natural$-convex iff it satisfies (M$^\natural$-SWGS[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155, Theorem 6.36.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155, Theorem 6.36

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.36 (p.155). -/
theorem swgs_characterizes_mnat_convex (f : (V → ℤ) → WithTop ℝ) (hce : ConvexExtensible f)
    (hne : (DomZ f).Nonempty) : MNaturalConvex f ↔ MNatSWGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
