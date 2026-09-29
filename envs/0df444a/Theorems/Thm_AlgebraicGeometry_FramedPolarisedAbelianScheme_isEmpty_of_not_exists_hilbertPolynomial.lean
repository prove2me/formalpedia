-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isEmpty_of_not_exists_hilbertPolynomial
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isEmpty_of_not_exists_hilbertPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/cc40afff-88e1-51cf-9a4e-7b60de9a8023
-- title:
--   Emptiness of framed polarised abelian schemes without Hilbert polynomial (N+1)t^g
-- statement:
--   Let $g$, $N$, $n$ be natural numbers and suppose that the following existential statement fails: there is a field $K$ and an ideal $I$ of the polynomial ring $K[x_0,\dots,x_N]$ in $N+1$ variables such that $I$ is homogeneous, in the sense that every homogeneous component of every element of $I$ again lies in $I$, and such that for some $d_1$ and all $d \ge d_1$ the $K$-dimension of `piece I d`, the quotient of the space of degree-$d$ homogeneous polynomials by those that lie in $I$, equals the value at $d$ of the polynomial $(N+1)t^g$. Then for every non-trivial commutative ring $R$ the type `FramedPolarisedAbelianScheme g N n R` is empty: there is no datum consisting of a scheme $A$ over $\operatorname{Spec} R$ carrying a commutative relative group law with the stated abelian-scheme property bundle, all of whose fibres have topological Krull dimension $g$, together with $2g$ $n$-torsion sections which are independent and generate the $n$-torsion of every geometric fibre, an invertible module `pol` on $A$ which is a closed immersion by sections with geometric fibre $H^0$-rank $N+1$, and a presentation of `pol` by $N+1$ sections over projective space whose associated morphism to $\operatorname{Proj}$ is a closed immersion and whose sections form a section basis on all of $A$.
--
--   This is the degenerate case in the construction of the Hilbert-scheme parameter space for framed polarised abelian schemes: if the numerical polynomial $(N+1)t^g$ occurs as the eventual Hilbert function of no homogeneous ideal in $N+1$ variables over any field, then there is nothing to parametrise over any non-zero base. It is used by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing), which may then take the empty scheme as its representing object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isEmpty_of_not_exists_hilbertPolynomial.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isEmpty_of_not_exists_hilbertPolynomial
    (g N n : ℕ)
    (hP : ¬ ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) =
        (Polynomial.C ((N : ℚ) + 1) * Polynomial.X ^ g).eval (d : ℚ))
    (R : Type) [CommRing R] [Nontrivial R] :
    IsEmpty (FramedPolarisedAbelianScheme g N n R) := by sorry
