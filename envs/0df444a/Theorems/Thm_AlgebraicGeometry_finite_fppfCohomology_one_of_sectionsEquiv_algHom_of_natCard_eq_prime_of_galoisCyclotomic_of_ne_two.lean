-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
-- name    : AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5e201a2e-2cde-55b2-97e0-b668a420b143
-- title:
--   Finiteness of H¹_{fppf}(Specℤ,L) for multiplicative-type layers
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, and let $K$ be a commutative ring equipped with a $\mathbb{Z}$-Hopf algebra structure, of finite type as a $\mathbb{Z}$-algebra and flat as a $\mathbb{Z}$-module. Assume: for every prime $\ell \neq p$, the base change $\mathbb{Z}_{(\ell)} \otimes_{\mathbb{Z}} K$ is a finite module over the subring $\mathbb{Z}_{(\ell)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $\ell$; the set of $\mathbb{Z}$-algebra maps $K \to \overline{\mathbb{Q}}$ has exactly $q$ elements; and for every ring automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $n_\sigma \in \mathbb{N}$ with $\sigma\zeta = \zeta^{n_\sigma}$ for all $\zeta$ with $\zeta^q = 1$, one has $\sigma \circ \psi = \psi^{n_\sigma}$ for every $\psi : K \to \overline{\mathbb{Q}}$, the power being taken in the convolution monoid `WithConv` on such maps. Let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb{Z}$ (coverings by morphisms that are flat and locally of finite presentation), together with additive isomorphisms $L(U) \cong \operatorname{Hom}_{\mathbb{Z}\text{-alg}}(K, \Gamma(U,\mathcal{O}))$ (convolution turned into addition) for all objects $U$, natural in the sense that restriction along $f : U \to V$ corresponds to post-composition with $\Gamma(f)$. Finally let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit, and suppose $\operatorname{Hom}_{\mathbb{Z}\text{-alg}}(K, A)$ has cardinality $q^{d_t}$ for some $d_t \in \mathbb{N}$. Then $H^1$ of the small fppf site of $\operatorname{Spec}\mathbb{Z}$ with coefficients in $L$ is finite.
--
--   This is the multiplicative-type step in Mazur's dévissage of finite flat group schemes over $\mathbb{Z}$ ramified only at $p$: a group scheme $G = \operatorname{Spec} K$ of odd prime order $q$ with cyclotomic Galois action on its $\overline{\mathbb{Q}}$-points is, away from $p$, a form of $\mu_q$, and the finiteness of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z}, L)$ follows. It feeds into the finiteness statements for cokernels attached to multiplicative-kind layers of the Néron model of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open AlgebraicGeometry

theorem AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (dt : ℕ) (hKA : Nat.card (K →ₐ[ℤ] ↥A) = q ^ dt) :
    Finite (fppfCohomology specInt L 1) := by sorry
