-- Prove2me | Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional
-- name    : AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/278ed94d-e639-5b07-8175-a5977bd66386
-- title:
--   Genus is invariant under a finite separable constant extension
-- statement:
--   Let $K$, $K'$, $F$, $F'$ be fields with $K'$ and $F$ algebras over $K$, $F'$ an algebra over each of $K$, $K'$ and $F$, the two towers $K \subseteq K' \subseteq F'$ and $K \subseteq F \subseteq F'$ being compatible with the map $K \to F'$. Assume $K'/K$ is finite and separable, $F'/F$ is integral, and $F$ is essentially of finite type over $K$. Assume further that $F$ is a curve over $K$ and $F'$ a curve over $K'$ in the sense of the predicate `IsCurveOver`: for a place, meaning a valuation subring of the function field that contains the image of the constant field, is not the whole field, and is a principal ideal ring, every residue field is finite-dimensional over the constant field; the module of Kähler differentials of the function field over the constant field is free of rank one; and every nonzero element $f$ has a degree-zero divisor whose value at each place $v$ is $v.\mathrm{ord}(f)$. The two remaining hypotheses are that $F'$ is generated as an $F$-algebra by the image of $K'$, and that every element of $F$ algebraic over $K$ lies in the image of $K$. The conclusion is the equality of natural numbers $\mathrm{genusFF}\,K'\,F' = \mathrm{genusFF}\,K\,F$, where $\mathrm{genusFF}$ of a pair is the dimension over the constant field of the space `H1` attached to the zero divisor, divisors being the finitely supported $\mathbb{Z}$-valued functions on places.
--
--   This is the invariance of the genus of an algebraic function field of one variable under a constant field extension, as in Stichtenoth's Theorem 3.6.3(b), here in the adelic currency (the genus as $\dim H^1(0)$) and for a finite separable extension of the exact constant field. It is used in the place-counting estimate [`AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even`](thm.html#AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even), and the argument invokes the approximation statement [`AlgebraicCurve.Place.exists_forall_ord_eq`](thm.html#AlgebraicCurve.Place.exists_forall_ord_eq), which produces a nonzero function with prescribed orders at finitely many places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finiteDimensional
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    AlgebraicCurve.genusFF K' F' = AlgebraicCurve.genusFF K F := by sorry
