-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_equivariant_sphere_contact_group_connected
-- name    : BirkhoffGlobalSection.equivariant_sphere_contact_group_connected
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:38:39.55622+00:00
-- url     : https://prove2.me/theorems/dc17e5ff-ead1-4508-b37f-1f6e55058b05
-- title:
--   Connectedness of the equivariant standard sphere contactomorphism group
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere which commutes with the antipodal involution. There is a jointly smooth contact isotopy, commuting with that involution at every time, from the identity to $F$:
--
--   $$F_0=\operatorname{id}_{S^3},\qquad F_1=F,\qquad F_t(-y)=-F_t(y).$$
--
--   This is the equivariant sphere-cover formulation of the triviality of the coorientation-preserving contact mapping class group of standard $\mathbb{RP}^3=L(2,1)$. It is independent of any Hamiltonian or distinguished knot.
--
--   **Formalization Note.** Start and finish are exact equalities on the sphere. In particular, the conclusion includes resolution of the possible antipodal deck discrepancy at the endpoint of a lifted quotient isotopy. Ambient representatives are jointly smooth at every point of the closed time cylinder.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/pdf/2207.03590, Theorem 1.1, p. 2, specialized to (p,q)=(2,1). Lift to the antipodal sphere cover; the deck transformation is joined to the identity by scalar complex rotation. The ambient smooth-extension convention is a coordinate formulation of the smooth sphere isotopy.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem equivariant_sphere_contact_group_connected
    (F : EquivariantSphereContactomorphism) :
    Nonempty (EquivariantSphereContactIsotopy F) := by sorry

end BirkhoffGlobalSection
