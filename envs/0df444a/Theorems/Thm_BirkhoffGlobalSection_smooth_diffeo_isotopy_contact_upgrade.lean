-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_smooth_diffeo_isotopy_contact_upgrade
-- name    : BirkhoffGlobalSection.smooth_diffeo_isotopy_contact_upgrade
-- status  : Open
-- author  : @caleb
-- created : 2026-10-02T21:53:07.964311+00:00
-- url     : https://prove2.me/theorems/6e644261-5059-4bf5-9fea-60f210f87d86
-- title:
--   Diffeomorphism isotopies upgrade to contact isotopies
-- statement:
--   Any smooth antipodally symmetric diffeomorphism isotopy from the identity to an equivariant contactomorphism upgrades to a genuine contact isotopy.
--
--   Let $F$ be an equivariant contactomorphism of $(S^3, \xi_{\mathrm{std}})$ and let $H_t$ be a smooth antipodally symmetric diffeomorphism isotopy with $H_0 = \mathrm{id}$ and $H_1 = F$ on the sphere. Then there exists an equivariant contact isotopy $I$ from $\mathrm{id}$ to $F$: the slices are equivariant contactomorphisms, jointly smooth in $(t, y)$, with $I_0 = \mathrm{id}$ and $I_1 = F$ on the sphere.
--
--   $$I : [0,1] \to \mathrm{Cont}^{\mathbb{Z}/2}(S^3), \quad I_0 = \mathrm{id},\; I_1 = F.$$
--
--   This is equivariant Gray stability with exact endpoints: the loop of pushed-forward contact structures along the diffeomorphism isotopy is null-homotopic, so the Gray machine deforms it into a contact isotopy with the endpoints fixed. Together with the diffeomorphism-isotopy existence half it yields an equivariant contact isotopy from the identity to every equivariant contactomorphism.
--
--   **Formalization Note** The diffeomorphism family $H$ is a hypothesis; the conclusion produces the contact isotopy structure. Invertibility of every slice is what makes the pushed-forward contact data available.
-- source:
--   Gray, J. W., Some global properties of contact structures, Ann. of Math. 69 (1959) (Gray stability; see also Geiges, An Introduction to Contact Topology, Thm. 2.2.2); Eliashberg, Y., contactomorphism group of standard tight S^3 connected (Thm. 2.4.2); contact mapping class triviality for (L(2,1), standard structure), arXiv:2207.03590, Thm. 1.1 (otherwise case).

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_BirkhoffGlobalSection_SphereDiffeoIsotopy
open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem smooth_diffeo_isotopy_contact_upgrade
    (F : EquivariantSphereContactomorphism)
    (H : EquivariantSphereDiffeoIsotopy F) :
    Nonempty (EquivariantSphereContactIsotopy F) := by sorry

end BirkhoffGlobalSection
