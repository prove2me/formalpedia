-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.Pic0.exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/915817e7-bac1-5aad-98fd-86f2098f7eb5
-- title:
--   Injectivity of the conorm on Pic⁰ under constant field extension
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, and the two towers $K \to K' \to F'$ and $K \to F \to F'$ compatible, with $K$ and $K'$ algebraically closed. Assume $F$ contains an element transcendental over $K$ with $F$ finite-dimensional over the subfield it generates over $K$, and likewise for $F'$ over $K'$; assume `IsCurveOver K F` and `IsCurveOver K' F'`, i.e. in each case every nonzero function has a degree-zero divisor recording its orders at all places, every place has residue field of finite dimension over the constant field, and the module of Kähler differentials is free of rank one over the function field; and assume $F'$ is generated over $K'$ by the image of $F$. Here a place is a valuation subring, distinct from the whole field, containing the constants and a principal ideal ring; divisors are finitely supported integer functions on places, $\mathrm{Pic}^0$ is the group of divisors of degree zero modulo those of the form $v \mapsto \mathrm{ord}_v f$ with $f \neq 0$. Then there is an injective group homomorphism $\iota : \mathrm{Pic}^0(F/K) \to \mathrm{Pic}^0(F'/K')$ such that for all degree-zero divisors $D$ of $F/K$ and $D'$ of $F'/K'$, if $D'(v') = D(v)$ whenever the valuation subring of $v'$ contracts along $F \to F'$ to that of $v$, and $D'(v') = 0$ whenever it contracts to no place of $F/K$, then $\iota([D]) = [D']$.
--
--   This is the injectivity of the conorm map on degree-zero divisor classes along a constant field extension of a one-variable function field, classically the injectivity of $J(K) \to J(K')$ on points of the Jacobian of the associated curve; the second clause fixes $\iota$ as the conorm, place by place. It is used in the computations of $\mathrm{Pic}^0$ torsion and of Frobenius fixed points on $\mathrm{Pic}^0$ over finite constant fields, such as [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ ι : Pic0 K F →+ Pic0 K' F', Function.Injective ι ∧
      ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
        (∀ (v' : Place K' F') (v : Place K F),
          v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
            (D' : Divisor K' F') v' = (D : Divisor K F) v) →
        (∀ v' : Place K' F',
          (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
            (D' : Divisor K' F') v' = 0) →
        ι (Pic0.mk D) = Pic0.mk D' := by sorry
