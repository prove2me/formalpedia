-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
-- name    : AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/f0949acb-e648-53d4-9c53-89665534cddd
-- title:
--   Pull-back after push-forward equals the sum over deck transformations
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$ of characteristic $0$, with $F$ and $F'$ given as $K$-algebras, and assume $F'$ has principal divisors over $K$, i.e. every nonzero $f \in F'$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ of $F'/K$ and $\deg D = 0$. Let $\varphi \colon F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and suppose $F'$ is finite as a module over $F$ via $\varphi$, of rank $n$ for a natural number $n$. Let $\sigma \colon \{0,\dots,n-1\} \to \mathrm{Aut}_K(F')$ be injective with $\sigma_i \circ \varphi = \varphi$ for every $i$. Then for every divisor $D$ of $F'/K$, i.e. every finitely supported function from the places of $F'/K$ to $\mathbb{Z}$, the pull-back along $\varphi$ of the push-forward along $\varphi$ of $D$ equals $\sum_{i} \sigma_i \cdot D$. Here the push-forward is the additive extension sending a place $w$ of $F'$ to its restriction to $F$ with multiplicity the inertia degree of $w$ over that restriction, the pull-back is the additive extension of the place-by-place pull-back, and $\sigma_i \cdot D$ denotes the action on divisors of the semilinear automorphism $(\sigma_i, \mathrm{id}_K)$ attached to $\sigma_i$.
--
--   This is the classical identity $\varphi^*\varphi_* D = \sum_i \sigma_i D$ for a Galois covering of function fields, here in the form in which the covering group is presented by $n$ distinct $K$-automorphisms of $F'$ fixing the image of $\varphi$ pointwise. It feeds the construction of correspondences and roof data on degree-zero divisor class groups, being used in [`AlgebraicCurve.Pic0.roof_package_of_surjective`](thm.html#AlgebraicCurve.Pic0.roof_package_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
    {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero K]
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K φ)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n)
    (σ : Fin n → (F' ≃ₐ[K] F')) (hσ : ∀ i, ((σ i : F' ≃ₐ[K] F') : F' →ₐ[K] F').comp φ = φ)
    (hinj : Function.Injective σ)
    (D : AlgebraicCurve.Divisor K F') :
    AlgebraicCurve.Divisor.pullbackAlong φ hφ (AlgebraicCurve.Divisor.pushforwardAlong φ hφ D) =
      ∑ i, AlgebraicCurve.SemilinearAut.ofAlgAut (σ i) • D := by sorry
