-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
-- name    : AlgebraicCurve.Place.one_le_ramificationIndexAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2002ab92-a49e-5418-b6e7-beec6aa3853c
-- title:
--   Positivity of ramification indices along an integral map
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral (every element of $F'$ satisfies a monic polynomial over the image of $F$), and let $w$ be a place of $F'$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F'$ containing $\operatorname{algebraMap} K F'(a)$ for every $a \in K$, distinct from all of $F'$, and a principal ideal ring. The conclusion is that $1 \le$ [`AlgebraicCurve.Place.ramificationIndexAlong`](def/AlgebraicCurve_Correspondence.html#L211) $\varphi\, w$, where the latter is obtained by equipping $F'$ with the $F$-algebra structure induced by $\varphi$ and forming $w$.`ramificationIndex` $F$, namely the infimum over $\mathbb{N}$ of the set of $n$ with $0 < n$ for which some nonzero $f \in F$ satisfies $w.\mathrm{ord}(\varphi(f)) = n$. Since the infimum of an empty set of naturals is $0$, the assertion is exactly that this set is nonempty: some nonzero element of $F$ has strictly positive order at $w$, and the ramification index so defined is then a genuine positive integer.
--
--   This is the basic positivity statement underlying the notion of ramification index of a place of $F'$ over the subfield $\varphi(F)$ in the project's theory of places of function fields; the integrality hypothesis is what rules out the degenerate situation in which the valuation of $w$ is trivial on the image of $F$ and the defining infimum is empty. It is used throughout the divisor push–pull and correspondence machinery, for instance in the comparison of the cardinality of the fibre of a place with the degree of the extension and in the construction of correspondences acting on Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.one_le_ramificationIndexAlong
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by sorry
