-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
-- name    : AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f5d585d3-aa3d-546c-9d43-06e1bbf44c63
-- title:
--   Places of a constant-field extension centred at K-embeddings
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a field extension of $K$ which is a curve over $K$ in the project's sense: $K$-rational divisors of nonzero elements exist with degree $0$ (for every $f \neq 0$ there is a divisor $D$ with $D v = v.\mathrm{ord}\, f$ at every place $v$ and $\deg D = 0$), every place of $F/K$ has residue field finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$; here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume moreover that $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$. Let $E$ be an algebraically closed extension of $K$ and $FE$ a field which is simultaneously an $E$-algebra and an $F$-algebra, compatibly with $K$ over both, such that $FE$ is a curve over $E$ in the same sense, contains an element transcendental over $E$ over which $FE$ is finite-dimensional, and is generated over $E$ by the image of $F$, i.e. $E(\operatorname{im}(F \to FE)) = FE$. Call a place $P$ of $FE/E$ centred at a $K$-algebra homomorphism $e \colon F \to E$ if the valuation attached to $P$ satisfies $v_P(f - e(f)) < 1$ for all $f \in F$ (images in $FE$ understood). The conclusion is a conjunction: first, for every $K$-algebra homomorphism $e \colon F \to E$ there is exactly one place of $FE/E$ centred at $e$; second, every place $P$ of $FE/E$ whose valuation subring contains the image of $F$ is centred at some $K$-algebra homomorphism $e \colon F \to E$.
--
--   This is the classical comparison, for the constant-field extension of a function field in one variable, between the $E$-valued points of the curve and the places of the extended function field: $\operatorname{Hom}_K(F,E)$ parametrises exactly those places of $FE/E$ at which all of $F$ is integral. It is used in the project's treatment of divisors and degree-zero divisor classes under constant-field extension, in particular in the results on the correspondence induced by reduction of places and on principal geometric cycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    (∀ e : F →ₐ[K] E, ∃! P : Place E FE, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) ∧
    (∀ P : Place E FE, (∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) →
      ∃ e : F →ₐ[K] E, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) := by sorry
