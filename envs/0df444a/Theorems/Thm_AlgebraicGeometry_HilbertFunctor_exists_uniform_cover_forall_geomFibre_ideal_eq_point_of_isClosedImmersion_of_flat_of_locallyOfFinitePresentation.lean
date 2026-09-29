-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/436e39da-40a6-5e18-a2b3-feff1ad5fdc0
-- title:
--   Uniform truncation level for geometric fibres in Pⁿ
-- statement:
--   Fix $n \in \mathbb{N}$. The assertion is the existence of a function $D_0 \colon \mathbb{Q}[t] \to \mathbb{N}$ with the following property. Let $A$ be a commutative ring (in `Type`), let $Z$ be a scheme and let $\iota \colon Z \to \operatorname{Proj}$ of the graded ring $\bigoplus_d (\text{homogeneous polynomials of degree } d)$ in $n+1$ variables over $A$ be a closed immersion such that the composite of $\iota$ with the structure morphism `ProjSpace.π A n` is flat and locally of finite presentation. Then there are a finite type $J$ and elements $r \colon J \to A$ whose span is the unit ideal (so the basic opens $D(r_j)$ cover $\operatorname{Spec} A$) such that for each $j$ there is a polynomial $P \in \mathbb{Q}[t]$ which is realised as a Hilbert polynomial in the following weak sense: there exist a field $K$ and an ideal $I \subseteq K[x_0,\dots,x_n]$ closed under taking homogeneous components, together with $d_1$ such that $\dim_K$ of the degree-$d$ piece $\;(\text{degree-}d\ \text{forms})/(I \cap \text{degree-}d\ \text{forms})\;$ equals $P(d)$ for all $d \ge d_1$; and such that, for every $m \ge D_0(P)$, every algebraically closed field $k$ with an $A$-algebra structure for which the image of $r_j$ in $k$ is a unit, there exist a point $q$ of `Point k n (hilbertFunctionOf n P m)` — that is, an ideal $q.I \subseteq k[x_0,\dots,x_n]$ closed under homogeneous components whose degree-$d$ pieces are finite and projective $k$-modules of rank at every prime equal to $\binom{n+d}{n}$ for $d < m$ and to $\lfloor P(d)\rfloor$ for $d \ge m$ — together with a scheme $Z_k$, a closed immersion $\iota_k \colon Z_k \to \operatorname{Proj}$ of the corresponding graded ring over $k$, and a morphism $e \colon Z_k \to Z$, such that the square formed by $e$, $\iota_k$ followed by `ProjSpace.π k n`, $\iota$ followed by `ProjSpace.π A n`, and $\operatorname{Spec}$ of $A \to k$ is a pullback, $e$ followed by $\iota$ equals $\iota_k$ followed by `ProjSpace.map A k n`, and for every $d \ge m$ and every form $F$ of degree $d$ one has $F \in q.I$ if and only if, for each $i \in \{0,\dots,n\}$, the section of the structure sheaf on the basic open $D(x_i)$ given by the homogeneous localisation $F/x_i^d$ pulls back to $0$ along $\iota_k$.
--
--   This is the uniform form of the exhaustion statement underlying the construction of the Hilbert scheme of $\mathbb{P}^n$: the truncation level $m$ at which a flat, locally finitely presented closed subscheme may be read off from its degree-$\ge m$ equations is bounded in terms of the Hilbert polynomial alone, the bound being chosen before the family $Z$ rather than after it (a Gotzmann-type regularity bound). It feeds the stratification $\operatorname{Hilb} = \coprod_P \operatorname{Hilb}^{P,m_P}$, and is cited in the construction of the representing scheme and in the comparison of geometric-fibre Hilbert functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
    (n : ℕ) :
    ∃ D₀ : Polynomial ℚ → ℕ, ∀ (A : Type) [CommRing A]
      (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),
      IsClosedImmersion ι → Flat (ι ≫ ProjSpace.π A n) → LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n) →
      ∃ (J : Type) (_ : Fintype J) (r : J → A), Ideal.span (Set.range r) = ⊤ ∧
        ∀ j : J, ∃ (P : Polynomial ℚ)
          (_ : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
            (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
            ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)),
          ∀ (m : ℕ), D₀ P ≤ m →
            ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], IsUnit (algebraMap A k (r j)) →

            ∃ (q : Point k n (hilbertFunctionOf n P m)) (Zk : Scheme.{0})
              (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
              IsClosedImmersion ιk ∧
              IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
              e ≫ ι = ιk ≫ ProjSpace.map A k n ∧

              (∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
                (F ∈ q.I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) := by sorry
