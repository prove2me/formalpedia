-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
-- name    : AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/7fe21863-a850-51fa-9489-e2c20713f60f
-- title:
--   Finiteness of H¹_{fppf}(Specℤ, L) for odd prime order
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, and let $K$ be a type carrying a commutative ring structure, a Hopf algebra structure over $\mathbb Z$, finite type as a $\mathbb Z$-algebra and flat as a $\mathbb Z$-module. Assume: for every prime $\ell \neq p$, the tensor product $\mathrm{ratLocalizedAt}\,\ell \otimes_{\mathbb Z} K$ is a finite module over $\mathrm{ratLocalizedAt}\,\ell$, the subring of $\mathbb Q$ of rationals whose denominator is coprime to $\ell$; the number of $\mathbb Z$-algebra homomorphisms $K \to \overline{\mathbb Q}$ is exactly $q$; and every ring automorphism $\sigma$ of $\overline{\mathbb Q}$ satisfies $\sigma(\psi(k)) = \psi(k)$ for every such homomorphism $\psi$ and every $k \in K$. Let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$, whose underlying category has as objects the morphisms to $\operatorname{Spec}\mathbb Z$ that are flat and locally of finite presentation. Assume given, for each object $U$, an isomorphism of additive groups $e_U$ from $L(U)$ to the additive group underlying the convolution group structure on $K \to_{\mathbb Z\text{-alg}} \Gamma(U, \mathcal O_U)$, compatible with restriction in the sense that for $f : U \to V$, $s \in L(V)$ and $k \in K$ one has $e_U(L(f)(s))(k) = \Gamma(f)\bigl(e_V(s)(k)\bigr)$. Then the degree-one fppf cohomology group $H^1$ of $L$ on $\operatorname{Spec}\mathbb Z$ is finite.
--
--   This is the constant-kind case of Mazur's analysis of finite flat group schemes over $\operatorname{Spec}\mathbb Z$ of odd prime order $q$ which are finite flat away from one prime $p$: the sheaf of points of such a group embeds into the constant sheaf $\mathbb Z/q$, whose first fppf cohomology over $\operatorname{Spec}\mathbb Z$ vanishes. It is used in the study of the primary torsion of the Néron model attached to $J_0$, in the form of a finiteness statement for the relevant first cohomology of a cokernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k)) :
    Finite (fppfCohomology specInt L 1) := by sorry
