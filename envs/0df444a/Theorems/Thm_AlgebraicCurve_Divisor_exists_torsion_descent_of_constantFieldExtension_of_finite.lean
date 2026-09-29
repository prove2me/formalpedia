-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
-- name    : AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/7210da5e-0136-5d3a-b23a-37cbac35f6b4
-- title:
--   Descent of n-torsion divisor classes along constant field extensions
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with algebra maps $K \to F$, $K' \to F'$, $K \to K'$, $F \to F'$ and $K \to F'$ forming compatible scalar towers $K \to K' \to F'$ and $K \to F \to F'$, with $K$ algebraically closed of characteristic zero and $K'$ algebraically closed. Assume $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and likewise for $F'$ over $K'$; assume the predicate `IsCurveOver` for $K \subseteq F$ and for $K' \subseteq F'$, that is: every nonzero element has a degree-zero divisor recording its orders at all places, each place has residue field finite over the constant field, and the module of Kähler differentials is free of rank one; and assume $F'$ is generated over $K'$ by the image of $F$. Here a place of $F/K$ is a valuation subring of $F$ containing $K$, distinct from $F$, and a principal ideal ring; a divisor is a finitely supported $\mathbb{Z}$-valued function on places; $\operatorname{ord}_v$ is the associated normalised valuation; and $\mathrm{Pic}^0$ is the group of degree-zero divisors modulo those of the form $v \mapsto \operatorname{ord}_v(f)$. Let $n \neq 0$ be a natural number, suppose the $n$-torsion subgroup $\{c \in \mathrm{Pic}^0(K',F') : n \cdot c = 0\}$ is finite, and let $D'$ be a divisor of $F'/K'$ with $n D'$ principal, i.e. there is $g' \neq 0$ in $F'$ with $n \, D'(v') = \operatorname{ord}_{v'}(g')$ for every place $v'$ of $F'/K'$. Then there exist a divisor $D$ of $F/K$ and a nonzero $h' \in F'$ such that $n D$ is principal (there is $g \neq 0$ in $F$ with $n \, D(v) = \operatorname{ord}_v(g)$ for all places $v$ of $F/K$), such that $D'(v') = D(v) + \operatorname{ord}_{v'}(h')$ whenever the valuation subring of $v'$ meets $F$ in that of $v$, and such that $D'(v') = \operatorname{ord}_{v'}(h')$ for every $v'$ whose valuation subring contracts to the valuation subring of no place of $F/K$.
--
--   This is the surjectivity half of the rigidity of Jacobian torsion under extension of an algebraically closed constant field: granted finiteness of the $n$-torsion upstairs, the base-change map $\mathrm{Pic}^0(F/K)[n] \to \mathrm{Pic}^0(F'/K')[n]$ hits every class. It is used in the construction of an injective Hecke-equivariant homomorphism out of the degree-zero Picard group of a modular curve over the complex numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hfin : Finite {c : Pic0 K' F' // n • c = 0}) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by sorry
