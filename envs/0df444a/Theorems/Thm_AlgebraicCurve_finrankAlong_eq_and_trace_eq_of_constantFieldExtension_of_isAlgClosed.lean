-- Prove2me | Theorems.Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/3f005163-728e-5705-afeb-6a5a894f9f67
-- title:
--   Degree and trace unchanged by algebraically closed constant field extension
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is a curve over $K$ in the sense of `IsCurveOver`, i.e. $F/K$ admits principal divisors (every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}\, f$), every place of $F/K$ has residue field finite-dimensional over $K$, and $\Omega[F/K]$ is free of rank $1$ over $F$; assume moreover that $F$ is finitely generated in the sense that there is a transcendental $x \in F$ with $F$ finite-dimensional over $K(x)$. Let $F'$ be a second such curve over $K$, with the same finite-generation hypothesis, and let $\varphi \colon F \to F'$ be a $K$-algebra homomorphism whose underlying ring map is integral. Let $E$ be an algebraically closed extension of $K$, let $FE$ be a curve over $E$ that is an extension of both $E$ and $F$ compatibly with $K$, satisfying the same finite-generation hypothesis over $E$ and generated over $E$ by the image of $F$ (that is, $E$ adjoined to the range of $F \to FE$ is all of $FE$); let $F'E$ be likewise a curve over $E$ extending $E$ and $F'$ compatibly with $K$, finitely generated over $E$ and generated over $E$ by the image of $F'$. Let $\varphi_E \colon FE \to F'E$ be an $E$-algebra homomorphism with integral underlying ring map which agrees with $\varphi$ on the image of $F$, i.e. $\varphi_E(\mathrm{alg}_{F \to FE}(f)) = \mathrm{alg}_{F' \to F'E}(\varphi f)$ for all $f \in F$. The conclusion is fourfold: $F'$ is a finite module over $F$ for the algebra structure given by $\varphi$; $F'E$ is a finite module over $FE$ for the algebra structure given by $\varphi_E$; the two ranks agree, $\mathrm{finrankAlong}\, E\, \varphi_E = \mathrm{finrankAlong}\, K\, \varphi$; and for every $u \in F'$ the trace of the image of $u$ in $F'E$ over $FE$ (with respect to $\varphi_E$) equals the image in $FE$ of the trace of $u$ in $F'$ over $F$ (with respect to $\varphi$).
--
--   This is the invariance of the degree and of the trace map of a finite morphism of function fields of one variable under extension of an algebraically closed constant field, in any characteristic. It is used in establishing compatibility of differentials and correspondences under constant field extension, and in the construction of Shimura curve models with good reduction and equivariant uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hφE : φE.toRingHom.IsIntegral) :
    FiniteAlong K φ ∧ FiniteAlong E φE ∧ finrankAlong E φE = finrankAlong K φ ∧
    ∀ u : F',
      (letI := algebraAlong φE; Algebra.trace FE F'E (algebraMap F' F'E u)) =
        algebraMap F FE (letI := algebraAlong φ; Algebra.trace F F' u) := by sorry
