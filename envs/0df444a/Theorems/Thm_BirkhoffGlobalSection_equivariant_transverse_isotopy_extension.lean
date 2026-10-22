-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_equivariant_transverse_isotopy_extension
-- name    : BirkhoffGlobalSection.equivariant_transverse_isotopy_extension
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T03:05:13.66876+00:00
-- url     : https://prove2.me/theorems/36c0927f-f846-4d4a-a282-a22c1fb2f5f4
-- title:
--   Equivariant isotopy extension for the transverse Hopf circle
-- statement:
--   Let $K \subset S^3$ admit an equivariant transverse Hopf isotopy $I$. This is a smooth family $u \mapsto I(t,u)$, $t \in [0,1]$, of embedded circles on the round three-sphere. Each circle commutes with the antipodal map and is positively transverse to the radial contact form $\lambda_y(v) = -\tfrac12\,\omega(y,v)$. The family starts at the standard Hopf circle $u \mapsto (u_0, 0, -u_1, 0)$ and ends with image $K$. Then there is an antipodally equivariant, coorientation-preserving contactomorphism $F$ of the standard sphere such that
--
--   $$F\bigl(\text{standard Hopf circle}\bigr) = K.$$
--
--   This is the isotopy extension theorem for transverse knots (one-dimensional contact submanifolds), applied in $\mathbb{RP}^3 = S^3/\{\pm 1\}$ with the descended standard contact structure.
--   - The family descends to a transverse isotopy of embedded knots in $\mathbb{RP}^3$: $I(t,u) = -I(t,v)$ forces $v = -u$ by injectivity and equivariance.
--   - It therefore extends to an ambient contact isotopy $\psi_t$ of $\mathbb{RP}^3$ with $\psi_t \circ \bar I_0 = \bar I_t$.
--   - The lift of $\psi_t$ to $S^3$ starting at the identity commutes with the antipodal map and preserves the coorientation.
--   - By uniqueness of path lifting, its time-one map sends $I(0,u)$ to $I(1,u)$.
--
--   **Formalization Note.** The conclusion is an `EquivariantSphereContactomorphism`. Its ambient representatives need only be smooth at sphere points, for example the radial extension $y \mapsto \psi_1(y/|y|)$, and the contact identity is required only on sphere-tangent vectors. No contact isotopy is asserted in the conclusion.
-- source:
--   Geiges, An Introduction to Contact Topology, Cambridge Studies in Advanced Mathematics 109 (2008), https://assets.cambridge.org/97805218/65852/frontmatter/9780521865852_frontmatter.pdf, Section 2.6 (isotopy extension theorem for contact submanifolds; transverse knots are one-dimensional contact submanifolds). Applied in RP^3 = S^3/{+-1} with the descended standard contact structure and lifted to the sphere.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

open scoped ContDiff

namespace BirkhoffGlobalSection

theorem equivariant_transverse_isotopy_extension (K : Set Phase)
    (I : EquivariantTransverseHopfIsotopy K) :
    ∃ F : EquivariantSphereContactomorphism,
      F.toFun '' (standardHopfCircle '' unitCircle) = K := by sorry

end BirkhoffGlobalSection
