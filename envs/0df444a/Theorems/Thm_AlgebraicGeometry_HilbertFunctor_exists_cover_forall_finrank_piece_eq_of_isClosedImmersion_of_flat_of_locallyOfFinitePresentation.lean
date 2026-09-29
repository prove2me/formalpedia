-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/edb3967a-94e7-5f7d-a1a6-99888eec00f9
-- title:
--   Locally constant Hilbert polynomial of flat finitely presented families
-- statement:
--   Fix $n \in \mathbb{N}$ and a commutative ring $A$, a scheme $Z$ and a morphism $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous parts of $A[x_0,\dots,x_n]$, i.e. $\mathbb{P}^n_A$, such that $\iota$ is a closed immersion and the composite of $\iota$ with the projection `ProjSpace.π A n` to the base is flat and locally of finite presentation. The assertion is that there exist a finite type $J$ and elements $r : J \to A$ whose range spans the unit ideal, such that for each $j \in J$ there are a polynomial $P \in \mathbb{Q}[t]$, a witness that $P$ is the Hilbert polynomial of some homogeneous ideal over some field (a field $K$ and an ideal $I \subseteq K[x_0,\dots,x_n]$ containing all homogeneous components of each of its elements, together with $d_1$ such that $\dim_K(K[x]_d / (I \cap K[x]_d)) = P(d)$ for all $d \ge d_1$), and a single bound $D_0 \in \mathbb{N}$ with the following property. For every algebraically closed field $k$ with an $A$-algebra structure making $r_j$ a unit in $k$, every scheme $Z_k$ with a closed immersion $\iota_k : Z_k \to \mathbb{P}^n_k$ and every $e : Z_k \to Z$ such that the square formed by $e$, $\iota_k$ followed by `ProjSpace.π k n`, $\iota$ followed by `ProjSpace.π A n` and $\operatorname{Spec}$ of $A \to k$ is a pullback, and such that $e$ followed by $\iota$ equals $\iota_k$ followed by the base-change morphism $\mathbb{P}^n_k \to \mathbb{P}^n_A$ induced by $\operatorname{MvPolynomial.map}(A \to k)$, and for every ideal $I \subseteq k[x_0,\dots,x_n]$ closed under taking homogeneous components and satisfying, for each $d$ and each $F$ homogeneous of degree $d$, that $F \in I$ if and only if for every $i$ the section $F/x_i^d$ restricts to $0$ along $\iota_k$ over the basic open $D_+(x_i)$, one has $\dim_k\bigl(k[x]_d / (I \cap k[x]_d)\bigr) = P(d)$ for all $d \ge D_0$.
--
--   This is the constancy of the Hilbert polynomial in flat, locally finitely presented families of closed subschemes of $\mathbb{P}^n_A$, in the form needed to stratify the base by Hilbert polynomial: the base is covered by finitely many basic opens on each of which a single polynomial $P$ and a single degree bound $D_0$ control the Hilbert function of the saturated ideal of every geometric fibre. It feeds the construction of points of the Hilbert functor, being cited by [`AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
    (n : ℕ) (A : Type) [CommRing A]
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ ProjSpace.π A n))
    (hfp : LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n)) :
    ∃ (J : Type) (_ : Fintype J) (r : J → A), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : J, ∃ (P : Polynomial ℚ)
        (_ : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
          (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
          ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ))
        (D₀ : ℕ), ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], IsUnit (algebraMap A k (r j)) →
          ∀ (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
            IsClosedImmersion ιk →
            IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A k))) →
            e ≫ ι = ιk ≫ ProjSpace.map A k n →
            ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
              (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) →
              (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
                (F ∈ I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) →
              ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by sorry
