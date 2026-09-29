-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
-- name    : AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/01863849-bcc9-5493-aaa7-9ccd3f60527f
-- title:
--   The Hilbert scheme of Pⁿ_ℤ is proper and finitely presented
-- statement:
--   Fix $n \in \mathbb{N}$ and $P \in \mathbb{Q}[t]$, and assume $P$ is realised as a Hilbert polynomial: there are a field $K$ and an ideal $I \subseteq K[x_0,\dots,x_n]$ closed under taking homogeneous components of its elements, together with $d_1$ such that for all $d \ge d_1$ the $K$-dimension of `piece I d`, the degree-$d$ homogeneous part of the polynomial ring modulo its intersection with $I$, equals $P(d)$. The assertion is that there is $D_0$ such that for every $m \ge D_0$ the functor sending a commutative ring $A$ to the set `Point A n (hilbertFunctionOf n P m)` — ideals $J \subseteq A[x_0,\dots,x_n]$ closed under homogeneous components, each `piece J d` being a finite projective $A$-module whose rank at every prime of $A$ is $\binom{n+d}{n}$ for $d < m$ and $\lfloor P(d)\rfloor$ (truncated at $0$) for $d \ge m$ — is represented by a scheme $\mathrm{Hilb}$ over $\mathbb{Z}$: there are $p : \mathrm{Hilb} \to \operatorname{Spec}\mathbb{Z}$ and bijections $\mathrm{pt}_A : \mathtt{Point}\ A\ n\ (\ldots) \simeq \operatorname{Hom}(\operatorname{Spec} A, \mathrm{Hilb})$ for all commutative rings $A$ such that: for every ring map $\varphi : A \to B$ and every $x$ over $A$ the extended ideal $\varphi_*(x.I)B[x_0,\dots,x_n]$ is again a point over $B$; for $\varphi$, $x$ over $A$ and $y$ over $B$, one has $y.I = \varphi_*(x.I)B[x_0,\dots,x_n]$ if and only if $\mathrm{pt}_B(y) = \operatorname{Spec}\varphi$ followed by $\mathrm{pt}_A(x)$; each $\mathrm{pt}_A(x)$ followed by $p$ is the structure morphism $\operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}$; $p$ is proper and locally of finite presentation; every finite set of points of $\mathrm{Hilb}$ is contained in an affine open; and there are $N$ and a closed immersion $\iota : \mathrm{Hilb} \to \operatorname{Proj}\mathbb{Z}[x_0,\dots,x_N]$ with $\iota$ followed by the projection $\mathbb{P}^N_{\mathbb{Z}} \to \operatorname{Spec}\mathbb{Z}$ equal to $p$.
--
--   This is the existence theorem for the Hilbert scheme of $\mathbb{P}^n_{\mathbb{Z}}$ with prescribed Hilbert polynomial, in the form in which it is used later: projective over $\mathbb{Z}$, with the functor-of-points bijection natural in both directions and with every finite set of points in an affine open. It is the input to the construction of moduli of framed polarised abelian schemes and to the representability of flat families of closed subschemes with given Hilbert polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ))
        (pt : ∀ (A : Type) [CommRing A],
          Point A n (hilbertFunctionOf n P m) ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
        (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)),
            ∃ y : Point B n (hilbertFunctionOf n P m), y.I = Ideal.map (MvPolynomial.map φ) x.I) ∧
        (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)) (y : Point B n (hilbertFunctionOf n P m)),
            y.I = Ideal.map (MvPolynomial.map φ) x.I ↔
            pt B y = Spec.map (CommRingCat.ofHom φ) ≫ pt A x) ∧
        (∀ (A : Type) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
            pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
        IsProper p ∧ LocallyOfFinitePresentation p ∧
        (∀ F : Finset Hilb, ∃ U : Hilb.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
        ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
          IsClosedImmersion ι ∧ ι ≫ ProjSpace.π ℤ N = p := by sorry
