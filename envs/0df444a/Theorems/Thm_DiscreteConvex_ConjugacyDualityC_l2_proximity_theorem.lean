-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_proximity_theorem
-- name    : DiscreteConvex.ConjugacyDualityC.l2_proximity_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:31.386126+00:00
-- url     : https://prove2.me/theorems/01cfd409-8271-49a7-bd85-3777a3bd6a68
-- title:
--   Theorem 8.44 -- l2_proximity_theorem
-- statement:
--   **Theorem 8.44** (L2-proximity theorem; p.232-233). A scaling version of Theorem 8.43's condition guarantees $\arg\min g\ne\emptyset$ with an explicit box proximity bound $2(n-1)(\alpha-1)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.232-233, Theorem 8.44.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.232-233, Theorem 8.44

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.44 (L2-proximity theorem; p.232-233). A scaling version of Theorem 8.43 gives an
explicit proximity bound for `arg min g`. -/
theorem l2_proximity_theorem (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g)
    (hper : ∀ p : V → ℤ, g (p + 1) = g p) (alpha : ℤ) (halpha : 0 < alpha) (palpha : V → ℤ)
    (hpalpha : palpha ∈ DomZ g)
    (hcond : ∀ Y : Finset V, g palpha ≤ g (fun v => palpha v + alpha * IndicatorVec Y v)) :
    (ArgMin g).Nonempty ∧
      ∃ pstar ∈ ArgMin g, ∀ v : V, palpha v ≤ pstar v ∧
        pstar v ≤ palpha v + 2 * ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by sorry

end DiscreteConvex.ConjugacyDualityC
