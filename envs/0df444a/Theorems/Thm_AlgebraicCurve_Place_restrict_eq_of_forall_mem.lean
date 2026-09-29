-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_restrict_eq_of_forall_mem
-- name    : AlgebraicCurve.Place.restrict_eq_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c496a92c-e2ff-549d-b25c-0a4d7a593cbb
-- title:
--   A place restricts to w once its ring contains w's
-- statement:
--   Let $K$, $F$, $L$ be fields with $K$-algebra structures on $F$ and $L$ and an $F$-algebra structure on $L$, forming a scalar tower $K \subseteq F \subseteq L$, and assume $L$ is integral over $F$. Let $w$ be a place of $F$ over $K$, that is (in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22)) a valuation subring $\mathcal{O}_w \subseteq F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose underlying ring is a principal ideal ring; and let $Q$ be a place of $L$ over $K$ in the same sense, with valuation subring $\mathcal{O}_Q \subseteq L$. Assume that every $y \in \mathcal{O}_w$ has image $\operatorname{algebraMap} F L\,(y) \in \mathcal{O}_Q$. The conclusion is the equality of places $Q.\mathrm{restrict}\,F = w$, where $Q.\mathrm{restrict}\,F$ is the place of $F$ over $K$ whose valuation subring is the preimage $(\operatorname{algebraMap} F L)^{-1}(\mathcal{O}_Q)$; thus mere containment of $\mathcal{O}_w$ in the contracted ring forces the two to coincide.
--
--   This is the maximality of a discrete valuation ring among the proper valuation subrings of its fraction field, in the form used to identify restrictions of places along a field extension: a place of $L$ whose ring dominates that of $w$ restricts to $w$ exactly. It is used in the comparison of places of a curve with points of its base change, where the restriction map along a tower must be pinned down.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_restrict_eq_of_forall_mem.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.restrict_eq_of_forall_mem {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Algebra.IsIntegral F L]
    (w : AlgebraicCurve.Place K F) (Q : AlgebraicCurve.Place K L)
    (hQ : ∀ y ∈ w.toValuationSubring, algebraMap F L y ∈ Q.toValuationSubring) :
    Q.restrict F = w := by sorry
