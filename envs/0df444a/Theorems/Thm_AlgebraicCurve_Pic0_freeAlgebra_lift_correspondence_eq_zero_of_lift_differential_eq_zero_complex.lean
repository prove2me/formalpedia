-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
-- name    : AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/12f5af1c-aade-5d25-9b50-ae4075109b47
-- title:
--   Faithfulness of the cotangent action of correspondences over ℂ
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure satisfying `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}(f)$, each place has residue field of finite dimension over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$. Assume `hfg`: some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over $\mathbb{C}(x)$. Let $\iota$ be an index type and, for each $i$, let $F'_i$ be a field with a $\mathbb{C}$-algebra structure having principal divisors, together with $\mathbb{C}$-algebra maps $\varphi_i, \psi_i \colon F \to F'_i$ whose underlying ring maps are integral, such that the fundamental identity holds for the extension $F \to F'_i$ given by $\varphi_i$, $F'_i$ is a finite $F$-module via $\psi_i$, and the pushforward norm formula holds along $\psi_i$. Let $p \in \mathrm{FreeAlgebra}\ \mathbb{Z}\ \iota$ be a noncommutative polynomial with integer coefficients. Suppose that the evaluation of $p$ at the $\mathbb{C}$-linear operators $\mathrm{tr}_{\varphi_i} \circ \psi_i^{*}$ on $\Omega[F/\mathbb{C}]$, taken in the opposite algebra so that words are evaluated with the order of factors reversed, annihilates every $\omega$ in `regularDifferentials ℂ F`, i.e. every $\omega$ such that at each place $v$ one has $\omega = f \cdot v.\mathrm{dCoord}$ with $f$ in the valuation subring of $v$. Then the evaluation of $p$, as a $\mathbb{Z}$-linear endomorphism of $\mathrm{Pic}^0(\mathbb{C}, F)$ (degree-zero divisors modulo principal ones), at the correspondences $(\psi_i)_* \varphi_i^{*}$ is zero.
--
--   This is the transcendental, $K = \mathbb{C}$ case of the statement that the representation of correspondences on the space of differentials of the first kind is faithful on the Jacobian, in the form classically obtained from Hurwitz's formula for the analytic representation of a correspondence together with Abel's theorem. It is cited by [`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero), which extends it to an arbitrary base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra ℂ (F' i)]
    [∀ i, HasPrincipalDivisors ℂ (F' i)]
    (φ ψ : ∀ i, F →ₐ[ℂ] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong ℂ (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong ℂ (ψ i)) (hN : ∀ i, NormFormulaAlong ℂ (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : ∀ ω ∈ regularDifferentials ℂ F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0 := by sorry
