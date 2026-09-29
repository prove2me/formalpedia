-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
-- name    : AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/da9f7904-7cb8-509e-89da-ac3f63c43108
-- title:
--   Separable constant extensions are unramified: e=1
-- statement:
--   Let $K$, $K'$, $F$, $F'$ be fields with $K'$ a $K$-algebra, $F'$ a $K'$-algebra, $F$ a $K$-algebra and $F'$ an $F$-algebra, the $K$-algebra structure on $F'$ being compatible both with $K \to K' \to F'$ and with $K \to F \to F'$. Assume $K'/K$ is algebraic and separable and $F'/F$ is integral, and assume that $F'$ is generated as an $F$-algebra by the image of $K'$, i.e. $\mathrm{Algebra.adjoin}\ F(\mathrm{range}(\mathrm{algebraMap}\ K'\ F')) = \top$. Let $W$ be a place of $F'$ over $K'$, that is, a valuation subring of $F'$ which contains the image of $K'$, is not all of $F'$, and is a principal ideal ring. Write $W$ also for the place of $F'$ over $K$ obtained by `forgetConstants`, which has literally the same valuation subring (the image of $K$ lies in it via the tower $K \to K' \to F'$). The assertion is that the ramification index of $W$ over $F$ equals $1$, where this index is by definition the infimum of the set of positive natural numbers $n$ for which some nonzero $f \in F$ satisfies $\operatorname{ord}_W(\mathrm{algebraMap}\ F\ F'\ f) = n$.
--
--   This is the classical statement that extension of the constant field by separable algebraic constants is unramified (Stichtenoth, Thm. III.6.3(a)), but without the hypothesis that $K$ be the exact constant field of $F$, i.e. algebraically closed in $F$; the generation hypothesis $F' = F\cdot K'$ replaces it. It feeds the comparison of valuations [`AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top`](thm.html#AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top), and its proof passes through the identification of this ramification index with the ramification index of the corresponding maximal ideals, [`AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter`](thm.html#AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (W : AlgebraicCurve.Place K' F') :
    (W.forgetConstants (K := K)).ramificationIndex F = 1 := by sorry
