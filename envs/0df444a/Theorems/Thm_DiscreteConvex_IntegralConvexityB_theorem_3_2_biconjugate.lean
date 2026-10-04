-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_2_biconjugate
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_2_biconjugate
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:05:27.944612+00:00
-- url     : https://prove2.me/theorems/5defcf37-45e6-4975-aee9-0bbf090938a1
-- title:
--   Theorem 3.2 -- biconjugation
-- statement:
--   $f^\bullet$ is closed proper convex whenever $\operatorname{dom}f\ne\emptyset$, and $g^{\bullet\bullet}=g$ for closed proper convex $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, Theorem 3.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, Theorem 3.2

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.102, Theorem 3.2, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.2.** The Legendre-Fenchel transform `f•` is a closed proper convex function for
any `f` with `dom f ≠ ∅`, and `f•• = f` for a closed proper convex function `f`. -/
theorem theorem_3_2_biconjugate {V : Type*} [Fintype V] (f : (V → ℝ) → EReal)
    (hdom : (DomE f).Nonempty) (hnb : NeverBot f) :
    (IsProperConvex (ConjF f) ∧ IsClosedConvexF (ConjF f)) ∧
      (∀ g : (V → ℝ) → EReal, IsClosedConvexF g → IsProperConvex g →
        ConjF (ConjF g) = g) := by sorry

end DiscreteConvex.IntegralConvexityB
