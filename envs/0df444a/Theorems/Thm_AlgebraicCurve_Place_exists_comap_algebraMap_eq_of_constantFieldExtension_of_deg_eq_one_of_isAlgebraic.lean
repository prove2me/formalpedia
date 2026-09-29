-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
-- name    : AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/34fd87c6-7850-5028-94f8-14e1ff492500
-- title:
--   Unique unramified extension of a rational place under algebraic constant extension
-- statement:
--   Let $K$, $F$, $K'$, $F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, $K'$ a $K$-algebra that is algebraic over $K$, and $F'$ an $F$- and $K$-algebra compatibly, the towers $K \subseteq K' \subseteq F'$ and $K \subseteq F \subseteq F'$ being scalar towers; assume $K$ is perfect. Assume $F$ is finitely generated of transcendence degree one over $K$, in the form that some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and likewise that some $x \in F'$ is transcendental over $K'$ with $F'$ finite-dimensional over $K'(x)$. Assume `IsCurveOver K F`: every nonzero $f \in F$ has a divisor of degree $0$ recording the orders $\mathrm{ord}_v(f)$ at all places $v$, each place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor is exactly the image of $K$ in $F$, and that $K'$ adjoined to the image of $F$ generates $F'$. Let $P$ be a place of $F/K$ — a valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring — with $\deg P := \dim_K \kappa(P) = 1$. Then there is a place $P'$ of $F'/K'$ whose valuation subring pulls back along $F \to F'$ to that of $P$, which satisfies $\mathrm{ord}_{P'}(f) = \mathrm{ord}_P(f)$ for all $f \in F$ (orders being taken via the associated height-one-spectrum valuations), and which is the only place of $F'/K'$ pulling back to $P$.
--
--   This is the classical statement that a rational place of a one-dimensional function field extends uniquely, and without ramification, to an algebraic extension of the constant field, in the form needed when the base constant field is merely perfect rather than algebraically closed. It is used in the study of places of the $q$-expansion function field, where periodicity of places under the action on coefficients is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra.IsAlgebraic K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [PerfectField K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : Place K F)
    (hP : P.deg = 1) :
    ∃ P' : Place K' F',
      P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, P'.ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q' = P' := by sorry
