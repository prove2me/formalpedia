-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension
-- name    : AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8ebbb935-fcea-556d-9ebe-5d84c009eabd
-- title:
--   Functions integral at all new places lie in K'· F
-- statement:
--   Let $K\subseteq K'$ and $F$, $F'$ be fields with algebra maps $K\to F$, $K'\to F'$, $K\to K'$, $F\to F'$ and $K\to F'$, the latter compatible via the two scalar-tower conditions $K\to K'\to F'$ and $K\to F\to F'$; assume $K$ is algebraically closed of characteristic zero and $K'$ is algebraically closed. Assume there exists $x\in F$ transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x)$, and likewise an $x\in F'$ transcendental over $K'$ with $F'$ finite-dimensional over $K'(x)$. Assume further $\mathrm{IsCurveOver}\ K\ F$ and $\mathrm{IsCurveOver}\ K'\ F'$: for each of the two pairs, every nonzero element $f$ admits a divisor of degree $0$ whose value at each place equals $\mathrm{ord}_v f$, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume the image of $F$ generates $F'$ as a field over $K'$, i.e. $K'(\mathrm{range}(F\to F'))=F'$. Let $z\in F'$ be such that $z$ lies in the valuation subring of every place $v'$ of $F'/K'$ whose contraction along $F\to F'$ is not the valuation subring of any place of $F/K$. Then $z$ lies in the $K'$-submodule of $F'$ spanned by the image of $F$.
--
--   This is the constant-field-extension statement that a function on $F'=K'\cdot F$ with no poles at the places not lying over places of $F$ is a $K'$-linear combination of functions from $F$, so that the span of the image of $F$ is the ring of such functions; classically it is part of the theory of extensions of the field of constants of an algebraic function field of one variable, and amounts to flat base change for the spaces $H^0(X,\mathcal O(D))$. It is used in the proofs that a divisor becoming principal after constant-field extension descends, [`AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension`](thm.html#AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension), and that suitable derivations can be produced after such an extension, [`AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem`](thm.html#AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) := by sorry
