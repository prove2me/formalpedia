-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_separable_convex_iff_m2_and_l2
-- name    : DiscreteConvex.ConjugacyDualityD.separable_convex_iff_m2_and_l2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:14.766908+00:00
-- url     : https://prove2.me/theorems/a63d3b0e-6ad0-461c-983a-2576c0f3cdbb
-- title:
--   Theorem 8.49 -- separable_convex_iff_m2_and_l2
-- statement:
--   **Theorem 8.49** (p.234). A function is both M$^\natural_2$-convex and L$^\natural_2$-convex if and only if it is both M$^\natural$-convex and L$^\natural$-convex, if and only if it is separable convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, Theorem 8.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, Theorem 8.49

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsSeparableConvex

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.49 (p.234). A function is both M♮₂- and L♮₂-convex iff it is both M♮- and
L♮-convex iff it is separable convex. -/
theorem separable_convex_iff_m2_and_l2 (f : (V → ℤ) → WithTop ℝ) :
    [MNat2Convex f ∧ LNat2Convex f, MNaturalConvex f ∧ LNaturalConvex f,
        IsSeparableConvex f].TFAE := by sorry

end DiscreteConvex.ConjugacyDualityD
