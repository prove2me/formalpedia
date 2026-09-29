-- Prove2me | Theorems.Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension
-- name    : AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/dfafcd77-5ad2-5762-b4c0-9c47191a3079
-- title:
--   Degree and trace under constant field extension
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a field extension of $K$ which is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ of $F/K$ is $v.\mathrm{ord}(f)$, every such place has residue field finite-dimensional over $K$, and $\Omega[F/K]$ is free of rank $1$ over $F$; assume moreover that $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$. Let $F'$ be a second such extension of $K$, satisfying the same two conditions, and let $\varphi \colon F \to F'$ be a $K$-algebra map whose underlying ring homomorphism is integral. Let $E$ be an algebraically closed extension of $K$, and let $FE$, $F'E$ be fields that are curves over $E$ in the same sense, each containing an element transcendental over $E$ over which it is finite-dimensional, with compatible towers $K \subseteq E \subseteq FE$, $K \subseteq F \subseteq FE$ and $K \subseteq E \subseteq F'E$, $K \subseteq F' \subseteq F'E$, and such that $FE$ is generated over $E$ by the image of $F$ and $F'E$ by the image of $F'$ ($E$-adjunction of those images is $\top$). Finally let $\varphi_E \colon FE \to F'E$ be an $E$-algebra map with integral underlying ring homomorphism which extends $\varphi$, in the sense that $\varphi_E(\mathrm{algebraMap}\,F\,FE\,f) = \mathrm{algebraMap}\,F'\,F'E\,(\varphi f)$ for all $f \in F$. Then: $F'$ is a finite module over $F$ for the algebra structure given by $\varphi$; $F'E$ is a finite module over $FE$ for the algebra structure given by $\varphi_E$; the two ranks agree, $\mathrm{finrank}_{FE} F'E = \mathrm{finrank}_F F'$; and for every $u \in F'$ the trace of the image of $u$ in $F'E$ relative to $\varphi_E$ equals the image in $FE$ of the trace of $u$ relative to $\varphi$.
--
--   This is the classical invariance of the degree and of the trace form of a finite morphism of curves under extension of an algebraically closed constant field, the content being that an $F$-basis of $F'$ remains an $FE$-basis of $F'E$. It is used in the comparison of regular differentials and of correspondences under constant field extension, and in the integrality statement for matrices of correspondences acting on Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
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
