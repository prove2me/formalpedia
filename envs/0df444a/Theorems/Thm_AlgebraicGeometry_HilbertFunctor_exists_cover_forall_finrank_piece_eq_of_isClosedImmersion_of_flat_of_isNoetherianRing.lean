-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing
-- name    : AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a0df551c-976a-5480-a904-9a9fbf94d1ff
-- title:
--   Local constancy of geometric fibre Hilbert polynomials, Noetherian base
-- statement:
--   Fix $n \in \mathbb{N}$ and a commutative Noetherian ring $A$ (in `Type`), a scheme $Z$ and a morphism $\iota : Z \to \operatorname{Proj}$ of the graded ring $A[x_0,\dots ,x_n]$ with its grading by `MvPolynomial.homogeneousSubmodule (Fin (n+1)) A`, assumed to be a closed immersion, and assume the composite of $\iota$ with the structure morphism `ProjSpace.π A n` to $\operatorname{Spec} A$ is flat. The assertion is that there exist a finite index type $J$ and elements $r_j \in A$ ($j \in J$) whose span is the unit ideal such that for every $j$ there are a polynomial $P \in \mathbb{Q}[t]$, a witness that $P$ is the eventual Hilbert function of some homogeneous ideal over some field (namely a field $K$, an ideal $I \subseteq K[x_0,\dots ,x_n]$ closed under taking homogeneous components, and $d_1$ with $\dim_K\bigl(K[x]_d/(I \cap K[x]_d)\bigr) = P(d)$ for all $d \ge d_1$), and a bound $D_0 \in \mathbb{N}$, with the following property: for every algebraically closed field $k$ that is an $A$-algebra in which the image of $r_j$ is a unit, every scheme $Z_k$, closed immersion $\iota_k : Z_k \to \operatorname{Proj}$ of $k[x_0,\dots ,x_n]$ and morphism $e : Z_k \to Z$ such that the square formed by $e$, $\iota_k$ followed by `ProjSpace.π k n`, $\iota$ followed by `ProjSpace.π A n` and $\operatorname{Spec}$ of $A \to k$ is cartesian and $e$ followed by $\iota$ equals $\iota_k$ followed by `ProjSpace.map A k n`, and every ideal $I \subseteq k[x_0,\dots ,x_n]$ closed under taking homogeneous components such that for all $d$ and all $F$ homogeneous of degree $d$ one has $F \in I$ if and only if for each $i$ the section of $Z_k$ obtained by pulling back along $\iota_k$ the section of the basic open $D_+(x_i)$ given by the homogeneous localisation $F/x_i^{\,d}$ vanishes, one has $\dim_k\bigl(k[x]_d/(I \cap k[x]_d)\bigr) = P(d)$ for all $d \ge D_0$, where the quotient is the degree-$d$ homogeneous part modulo its intersection with $I$, as in `piece`.
--
--   This is the statement that the Hilbert polynomial of the geometric fibres of a flat closed subscheme of $\mathbb{P}^n_A$ is locally constant on $\operatorname{Spec} A$, together with a bound $D_0$, valid uniformly over each piece of the cover, beyond which the Hilbert function of each fibre agrees with that polynomial. It is the Noetherian-base form of the result, and is used to deduce the corresponding statement for bases that are merely locally of finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing
    (n : ℕ) (A : Type) [CommRing A] [IsNoetherianRing A]
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ ProjSpace.π A n)) :
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
