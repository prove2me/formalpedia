-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_of_point_hilbertFunctionOf
-- name    : AlgebraicGeometry.HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_of_point_hilbertFunctionOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ce63f1a9-b61e-5789-985c-2c495b8e8835
-- title:
--   Hilbert points of Pⁿ versus flat closed subschemes
-- statement:
--   Fix $n \in \mathbb{N}$ and $P \in \mathbb{Q}[t]$, and assume $P$ is realisable: there are a field $K$ and an ideal $I \subseteq K[x_0,\dots,x_n]$ closed under taking homogeneous components, together with $d_1$, such that for all $d \ge d_1$ the $K$-dimension of `piece I d` — the degree-$d$ forms modulo those lying in $I$ — equals $P(d)$. Then there is $D_0$ such that for every $m \ge D_0$ there is an assignment $\Phi$ which, for each commutative ring $A$, sends a point $p$ of the Hilbert functor over $A$ — an ideal $p.I \subseteq A[x_0,\dots,x_n]$ closed under homogeneous components whose graded pieces `piece p.I d` are finite projective $A$-modules of rank $\mathrm{hilbertFunctionOf}\ n\ P\ m\ d$ (equal to $\binom{n+d}{n}$ for $d<m$ and to $\lfloor P(d)\rfloor$, truncated at $0$, for $d \ge m$) at every prime of $A$ — to a pair consisting of a scheme $(\Phi\,A\,p).1$ and a morphism $(\Phi\,A\,p).2$ to $\operatorname{Proj}$ of the graded ring $A[x_0,\dots,x_n]$, subject to five clauses. (1) Each $(\Phi\,A\,p).2$ is a closed immersion whose composite with the structure morphism $\pi$ to $\operatorname{Spec} A$ is flat and locally of finite presentation. (2) If $(\Phi\,A\,p).1 \cong (\Phi\,A\,q).1$ compatibly with the two morphisms to $\operatorname{Proj}$, then $p=q$. (3) For an $A$-algebra $B$ and points $p$ over $A$, $q$ over $B$ with $q.I =$ the image of $p.I$ under coefficientwise base change, there is $e : (\Phi\,B\,q).1 \to (\Phi\,A\,p).1$ making a pullback square of $(\Phi\,B\,q).2 \mathbin{;} \pi_B$ and $(\Phi\,A\,p).2 \mathbin{;} \pi_A$ over $\operatorname{Spec}(B) \to \operatorname{Spec}(A)$, with $e$ followed by $(\Phi\,A\,p).2$ equal to $(\Phi\,B\,q).2$ followed by `ProjSpace.map A B n`. (4) Conversely, if $\iota : Z \to \operatorname{Proj}$ is a closed immersion with $\iota \mathbin{;} \pi_A$ flat and locally of finite presentation, and if for every algebraically closed field $k$ that is an $A$-algebra some point $q$ over $k$ has $(\Phi\,k\,q).2$ realising the geometric fibre of $\iota$ (as a pullback compatible with `ProjSpace.map A k n`), then $Z$ over $\operatorname{Proj}$ is isomorphic to $(\Phi\,A\,p).2$ for some point $p$ over $A$. (5) For every $A$, every point $p$, every $d \ge m$ and every $F$ homogeneous of degree $d$: $F \in p.I$ if and only if for each $i$ the pullback along $(\Phi\,A\,p).2$ of the section of $\operatorname{Proj}$ over the basic open set of $x_i$ determined by the homogeneous localisation $F/x_i^{d}$ vanishes.
--
--   This is the comparison, in the shape needed for the construction of Hilbert schemes, between the functor of graded ideal points with prescribed Hilbert function and the functor of flat, finitely presented closed subschemes of $\mathbb{P}^n_A$, clause (5) recording the dictionary that recovers the ideal $p.I$ in degrees $\ge m$ from scheme-theoretic vanishing on $\Phi(p)$. It is used in the construction of moduli of framed polarised abelian schemes, via [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_of_point_hilbertFunctionOf.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_of_point_hilbertFunctionOf
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ Φ : ∀ (A : Type) [CommRing A], Point A n (hilbertFunctionOf n P m) →
          (Z : Scheme.{0}) × (Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),

        (∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)),
          IsClosedImmersion (Φ A p).2 ∧ Flat ((Φ A p).2 ≫ ProjSpace.π A n) ∧
            LocallyOfFinitePresentation ((Φ A p).2 ≫ ProjSpace.π A n)) ∧

        (∀ (A : Type) [CommRing A] (p q : Point A n (hilbertFunctionOf n P m)),
          (∃ e : (Φ A p).1 ≅ (Φ A q).1, e.hom ≫ (Φ A q).2 = (Φ A p).2) → p = q) ∧

        (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
            (p : Point A n (hilbertFunctionOf n P m)) (q : Point B n (hilbertFunctionOf n P m)),
          q.I = Ideal.map (MvPolynomial.map (algebraMap A B)) p.I →
          ∃ e : (Φ B q).1 ⟶ (Φ A p).1,
            IsPullback e ((Φ B q).2 ≫ ProjSpace.π B n) ((Φ A p).2 ≫ ProjSpace.π A n)
              (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
            e ≫ (Φ A p).2 = (Φ B q).2 ≫ ProjSpace.map A B n) ∧

        (∀ (A : Type) [CommRing A] (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),
          IsClosedImmersion ι → Flat (ι ≫ ProjSpace.π A n) → LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k],
            ∃ (q : Point k n (hilbertFunctionOf n P m)) (e : (Φ k q).1 ⟶ Z),
              IsPullback e ((Φ k q).2 ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n)
                (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
              e ≫ ι = (Φ k q).2 ≫ ProjSpace.map A k n) →
          ∃ (p : Point A n (hilbertFunctionOf n P m)) (e : (Φ A p).1 ≅ Z), e.hom ≫ ι = (Φ A p).2) ∧

        (∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)) (d : ℕ), m ≤ d →
          ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
            (F ∈ p.I ↔ ∀ i : Fin (n + 1),
              ((Φ A p).2.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)))
                ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })) = 0)) := by sorry
