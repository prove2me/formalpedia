-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
-- name    : AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/4944ccf9-b21e-54cf-92b4-1e33fd2c271b
-- title:
--   Connected locally Noetherian schemes with domain stalks are integral
-- statement:
--   Let $X$ be a scheme, assumed locally Noetherian in the sense of Mathlib's `IsLocallyNoetherian`, i.e. the ring of sections over every affine open subscheme is a Noetherian ring, and assumed to have connected underlying topological space (`ConnectedSpace`, which in particular requires the space to be nonempty). Suppose further that for every point $x$ of $X$ the local ring $\mathcal{O}_{X,x}$, realised as the stalk at $x$ of the structure presheaf `X.presheaf`, is an integral domain (a nontrivial commutative ring without zero divisors). The conclusion is `IsIntegral X`: the underlying space of $X$ is irreducible and nonempty, and $X$ is reduced, i.e. the sections over every open subset form a reduced ring. No separate quasi-compactness or affineness hypothesis is imposed.
--
--   This is the standard criterion identifying integral schemes among connected locally Noetherian ones by a pointwise condition on the local rings: disjointness of the irreducible components is forced by the absence of two distinct minimal primes in a domain, and local finiteness of the components on a locally Noetherian space makes each component clopen. It is used in the project to recognise integrality of smooth connected schemes, for instance in [`AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace`](thm.html#AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace) and its geometric variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by sorry
