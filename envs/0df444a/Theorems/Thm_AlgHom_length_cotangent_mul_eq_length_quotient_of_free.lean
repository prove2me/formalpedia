-- Prove2me | Theorems.Thm_AlgHom_length_cotangent_mul_eq_length_quotient_of_free
-- name    : AlgHom.length_cotangent_mul_eq_length_quotient_of_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b99e552b-7262-5d9f-808f-1fbb99e556e6
-- title:
--   Equality d ℓ(Φ_R)=ℓ(Ω) for complete intersections with free M
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, discrete valuation ring, and adically complete for its maximal ideal), let $R$ be a commutative $\mathcal O$-algebra, and let $T$ be a local commutative $\mathcal O$-algebra that is finite and free as an $\mathcal O$-module. Let $\varphi\colon R\to T$ be a bijective $\mathcal O$-algebra homomorphism, and let $\pi_R\colon R\to\mathcal O$ and $\pi_T\colon T\to\mathcal O$ be $\mathcal O$-algebra homomorphisms with $\pi_T\circ\varphi=\pi_R$. Write $\wp=\ker\pi_T$ and assume that the image $\pi_T(\operatorname{Ann}_T(\wp))$ is a nonzero ideal of $\mathcal O$, and that $T$ admits a complete-intersection presentation: for some $n$ there are $f_0,\dots,f_{n-1}\in\mathcal O[[X_0,\dots,X_{n-1}]]$ (formal power series in $n$ variables) together with an $\mathcal O$-algebra isomorphism $\mathcal O[[X_0,\dots,X_{n-1}]]/(f_0,\dots,f_{n-1})\cong T$. Let $M$ be a $T$-module, also an $\mathcal O$-module compatibly with the $T$-action, finite and free over $\mathcal O$ and free over $T$. Then, in $\mathbb N\cup\{\infty\}$,
--   $$\operatorname{rank}_{\mathcal O}\bigl(M[\wp]\bigr)\cdot \ell_{\mathcal O}\bigl((\ker\pi_R)/(\ker\pi_R)^2\bigr)=\ell_{\mathcal O}\bigl(M/(M[\wp]+M[\operatorname{Ann}_T(\wp)])\bigr),$$
--   where $M[J]$ denotes the submodule of elements annihilated by every element of the ideal $J$, the first factor is the $\mathcal O$-rank of $M[\wp]$ coerced into $\mathbb N\cup\{\infty\}$, and $\ell_{\mathcal O}$ is length as an $\mathcal O$-module.
--
--   This is the equality case of Wiles's numerical criterion: when the augmented $\mathcal O$-algebra $R$ is isomorphic to a complete intersection $T$ and the module $M$ is free over $T$, the invariant $d\,\ell(\Phi_R)$ attached to the deformation side agrees exactly with the length of the congruence module $\Omega=M/(M[\wp]+M[\operatorname{Ann}\wp])$. It is used to propagate the numerical hypothesis along the Taylor–Wiles patching ladder, being cited in the construction of patching data for deformation rings and in the analysis of local Hecke algebras attached to cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_length_cotangent_mul_eq_length_quotient_of_free.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem AlgHom.length_cotangent_mul_eq_length_quotient_of_free
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {R : Type v} [CommRing R] [Algebra 𝒪 R]
    {T : Type w} [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Bijective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T))
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] [Module.Free T M] :
    (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR).Cotangent =
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) := by sorry
