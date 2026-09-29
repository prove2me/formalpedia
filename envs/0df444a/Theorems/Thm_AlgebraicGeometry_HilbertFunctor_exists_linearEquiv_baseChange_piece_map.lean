-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
-- name    : AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/fdbc4de5-503f-521c-af7c-599c69839532
-- title:
--   Base change of the graded pieces of a homogeneous ideal
-- statement:
--   Let $n$ be a natural number, let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $I$ be an ideal of the polynomial ring $A[x_0,\dots,x_n]$ in $n+1$ variables which is homogeneous in the sense that for every $p \in I$ and every degree $d$ the degree-$d$ homogeneous component of $p$ again lies in $I$. Write $J = I \cdot B[x_0,\dots,x_n]$ for the image of $I$ under the coefficient map $A[x] \to B[x]$ induced by the structure morphism $A \to B$, and for an ideal recall that its degree-$d$ piece is the quotient of the $A$- (resp. $B$-) module of forms of degree $d$ by the submodule of those forms lying in the ideal. The assertion is twofold: first, $J$ is again homogeneous, i.e. every homogeneous component of every element of $J$ lies in $J$; second, for every $d$ there is a $B$-linear isomorphism $e : B \otimes_A (A[x]/I)_d \to (B[x]/J)_d$ which is compatible with the evident maps, in that for every $p \in A[x]$ homogeneous of degree $d$ one has $e(1 \otimes \overline{p}) = \overline{\,p^{B}\,}$, where $p^{B}$ denotes the image of $p$ in $B[x]$ (again homogeneous of degree $d$).
--
--   This is the base-change compatibility of the graded pieces of the quotient by a homogeneous ideal, the statement that makes the Hilbert functor of projective $n$-space a functor and allows the ranks of the graded pieces to be compared over a base and over its fibres. It is used in the results that recover a homogeneous ideal from the dimensions of its graded quotients and in the analysis of the Hilbert function of such ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    (∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
        homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B))) ∧
    ∀ d : ℕ, ∃ e : B ⊗[A] piece I d ≃ₗ[B] piece (I.map (MvPolynomial.map (algebraMap A B))) d,
      ∀ (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d),
        e (1 ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
          Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ := by sorry
