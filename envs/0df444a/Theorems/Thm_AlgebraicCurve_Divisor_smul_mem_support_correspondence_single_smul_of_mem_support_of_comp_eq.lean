-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
-- name    : AlgebraicCurve.Divisor.smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/8facecc7-7c49-523f-80e1-03b07fbe8962
-- title:
--   Leg-exchange symmetry for supports of divisorial correspondences
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$, and assume both $F$ and $F'$ have principal divisors over $K$, i.e. every nonzero element $f$ admits a finitely supported integer-valued function on places whose value at each place $v$ is $\operatorname{ord}_v(f)$ and whose degree is $0$ (a place of $F/K$ being a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring). Let $\varphi, \psi : F \to F'$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, and suppose that $F'$ is module-finite over $F$ through $\varphi$ and through $\psi$. Let $W$ be a $K$-algebra automorphism of $F'$ and $\tau_1, \tau_2$ be $K$-algebra automorphisms of $F$ satisfying the leg-exchange laws $W(\varphi x) = \psi(\tau_1 x)$ and $W(\psi x) = \varphi(\tau_2 x)$ for all $x \in F$. Write $\mathrm{Corr}(\varphi,\psi)$ for the additive endomorphism of divisors of $F/K$ obtained by pulling back along $\varphi$ and then pushing forward along $\psi$. Then for places $P, Q$ of $F/K$, if $Q$ lies in the support of $\mathrm{Corr}(\varphi,\psi)$ applied to the divisor $P$ with coefficient $1$, then the place $\tau_1 \cdot P$ (the action of $\tau_1$ through the semilinear automorphism $(\tau_1, \mathrm{id}_K)$) lies in the support of $\mathrm{Corr}(\varphi,\psi)$ applied to the divisor $\tau_2 \cdot Q$ with coefficient $1$.
--
--   This records how the support of a correspondence $\psi_*\varphi^*$ on divisors of a function field transforms under an automorphism $W$ of the upper field that interchanges the two legs, the situation of an Atkin–Lehner involution acting on the degeneracy maps defining a Hecke correspondence. It is used in the construction of divisors on $X_1$-type modular curves, in the statement producing coprimality data for Hecke divisors twisted by diamond operators and Atkin–Lehner involutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ)
    (W : F' ≃ₐ[K] F') (τ₁ τ₂ : F ≃ₐ[K] F)
    (hWφ : ∀ x : F, W (φ x) = ψ (τ₁ x)) (hWψ : ∀ x : F, W (ψ x) = φ (τ₂ x))
    (P Q : AlgebraicCurve.Place K F)
    (hQ : Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support) :
    SemilinearAut.ofAlgAut τ₁ • P ∈
      (Divisor.correspondence φ ψ hφ hψ (Finsupp.single (SemilinearAut.ofAlgAut τ₂ • Q) 1)).support := by sorry
