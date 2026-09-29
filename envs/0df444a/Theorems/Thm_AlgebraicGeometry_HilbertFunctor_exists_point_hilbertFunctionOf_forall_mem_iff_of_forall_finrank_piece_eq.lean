-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
-- name    : AlgebraicGeometry.HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f4deb365-120a-5d69-9734-68db8f94a61a
-- title:
--   Truncating a homogeneous ideal to a Hilbert-functor point
-- statement:
--   Fix $n \in \mathbb{N}$, a field $k$, a polynomial $P \in \mathbb{Q}[t]$, a natural number $m$, and an ideal $I$ of $k[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n + 1)) k`. Assume $I$ is homogeneous in the sense that every homogeneous component `homogeneousComponent d p` of every $p \in I$ again lies in $I$, and assume that for every $d \ge m$ the $k$-dimension of `piece I d`, the quotient of the degree-$d$ homogeneous forms by those lying in $I$, equals $P(d)$ (as an equality of rationals). The conclusion produces a term $q$ of the structure `Point k n (hilbertFunctionOf n P m)`, that is an ideal $q.I$ of $k[x_0,\dots,x_n]$ closed under taking homogeneous components, all of whose pieces `piece q.I d` are finite and projective $k$-modules and satisfy `Module.rankAtStalk (piece q.I d) p = hilbertFunctionOf n P m d` at every point $p$ of $\operatorname{Spec} k$, where `hilbertFunctionOf n P m d` is $\binom{n+d}{n}$ for $d < m$ and $\max(\lfloor P(d)\rfloor, 0)$ for $d \ge m$; moreover $q.I$ and $I$ contain the same homogeneous forms of each degree $d \ge m$.
--
--   This is the packaging step turning a homogeneous ideal over a field whose Hilbert function agrees with a polynomial $P$ from degree $m$ on into a $k$-valued point of the Hilbert functor with Hilbert function `hilbertFunctionOf n P m`, by replacing $I$ with its truncation in degrees $\ge m$. It is used in the treatment of Hilbert schemes and of framed polarised abelian schemes, in particular by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.isEmpty_of_not_exists_hilbertPolynomial`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.isEmpty_of_not_exists_hilbertPolynomial) and by the statements deducing points from closed immersions with prescribed fibrewise $H^0$ dimensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
    (n : ℕ) (k : Type) [Field k] (P : Polynomial ℚ) (m : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hP : ∀ d : ℕ, m ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ q : Point k n (hilbertFunctionOf n P m),
      ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k), F.IsHomogeneous d → (F ∈ q.I ↔ F ∈ I) := by sorry
