-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver
-- name    : AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/e0eddd01-7a71-5ff8-ba0e-3b441edc4043
-- title:
--   Push-forward of divisors commutes with constant extension
-- statement:
--   Let $K$, $F$, $F'$, $E$, $F_E$, $F'_E$ be fields with $F,F',E$ algebras over $K$, $F_E$ an algebra over both $E$ and $F$ compatibly with $K$, and $F'_E$ an algebra over both $E$ and $F'$ compatibly with $K$; assume $K$ is algebraically closed of characteristic $0$ and $E$ is algebraically closed. Assume each of $F/K$, $F'/K$, $F_E/E$, $F'_E/E$ contains a transcendental element over which the field is finite-dimensional, and that $F$, $F'$ are curves over $K$ and $F_E$, $F'_E$ curves over $E$, where `IsCurveOver` means: every nonzero function has a divisor of degree $0$ recording its orders at all places, each place has residue field finite over the base, and the module of Kähler differentials is free of rank $1$. Assume $F_E$ is generated over $E$ by the image of $F$ and $F'_E$ by the image of $F'$, and that $K,F'$ and $E,F'_E$ satisfy `HasPrincipalDivisors`. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring map is integral, $\varphi_E : F_E \to F'_E$ an $E$-algebra map whose ring map is integral, with $\varphi_E \circ (F \to F_E) = (F' \to F'_E) \circ \varphi$. Here a place of $F$ over $K$ is a valuation subring containing the image of $K$, different from $F$, and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $D$ be a divisor of $F'$ over $K$ and $D_E$ a divisor of $F'_E$ over $E$ such that $D_E(w') = D(w)$ whenever the valuation subring of $w'$ contracts along $F' \to F'_E$ to that of $w$, and $D_E(w') = 0$ when $w'$ contracts to the subring of no place of $F'$ over $K$. The conclusion is that the same two conditions hold for the push-forwards along $\varphi_E$ and $\varphi$ with respect to $F \to F_E$: namely $(\varphi_E)_* D_E(v') = \varphi_* D(v)$ whenever $v'$ contracts to $v$, and $(\varphi_E)_* D_E(v') = 0$ whenever $v'$ contracts to no place of $F$ over $K$, where `pushforwardAlong` is the push-forward for the algebra structure induced by the given map, sending a place to its restriction weighted by the inertia degree.
--
--   This is the compatibility of the divisor push-forward (trace) along a finite morphism of curves with the conorm map attached to an extension of the algebraically closed field of constants, the push-forward counterpart of the analogous statement for pull-backs. It is used in the proof that divisorial correspondences on degree-zero divisor classes commute with constant field extension, in [`AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm`](thm.html#AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [AlgebraicCurve.IsCurveOver E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    [AlgebraicCurve.HasPrincipalDivisors K F'] [AlgebraicCurve.HasPrincipalDivisors E F'E]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (D : AlgebraicCurve.Divisor K F') (DE : AlgebraicCurve.Divisor E F'E)
    (hover : ∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
      w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring → DE w' = D w)
    (hoff : ∀ w' : AlgebraicCurve.Place E F'E,
      (∀ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) ≠ w.toValuationSubring) → DE w' = 0) :
    (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' = AlgebraicCurve.Divisor.pushforwardAlong φ hφ D v) ∧
    (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' = 0) := by sorry
