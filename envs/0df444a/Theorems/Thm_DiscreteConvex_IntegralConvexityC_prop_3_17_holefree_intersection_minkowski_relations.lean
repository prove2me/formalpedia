-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_17_holefree_intersection_minkowski_relations
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_17_holefree_intersection_minkowski_relations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:12:23.54355+00:00
-- url     : https://prove2.me/theorems/faa60660-ae49-4878-8959-0b29220b3b5b
-- title:
--   Proposition 3.17 -- basic hole-free intersection/Minkowski-sum relations
-- statement:
--   For hole-free $S_1,S_2$: containment and equality facts relating $S_1\cap S_2$, $S_1+S_2$ and the closures $\bar S_1,\bar S_2$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Proposition 3.17.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Proposition 3.17

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_HoleFree
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_MinkowskiSumZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.92, Proposition 3.17, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

open scoped Pointwise

/-- **Proposition 3.17.** Assume `Sk = S̄k ∩ Zⁿ` for `k=1,2`. (1) `S̄1∩S̄2 ⊇ (S1∩S2)‾`.
(2) `S1∩S2 = (S̄1∩S̄2)∩Zⁿ`. (3) `S1+S2 ⊆ (S̄1+S̄2)∩Zⁿ`. (4) `(S1+S2)‾ = S̄1+S̄2`. -/
theorem prop_3_17_holefree_intersection_minkowski_relations {n : ℕ} (S1 S2 : Set (Fin n → ℤ))
    (h1 : HoleFree S1) (h2 : HoleFree S2) :
    (ConvexClosureSet S1 ∩ ConvexClosureSet S2 ⊇ ConvexClosureSet (S1 ∩ S2)) ∧
      (S1 ∩ S2 = {x : Fin n → ℤ | EmbedZR x ∈ ConvexClosureSet S1 ∩ ConvexClosureSet S2}) ∧
      (MinkowskiSumZ S1 S2 ⊆
          {x : Fin n → ℤ | EmbedZR x ∈ ConvexClosureSet S1 + ConvexClosureSet S2}) ∧
      (ConvexClosureSet (MinkowskiSumZ S1 S2) =
        ConvexClosureSet S1 + ConvexClosureSet S2) := by sorry

end DiscreteConvex.IntegralConvexityC
