-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_smooth_isotopy_contact_upgrade
-- name    : BirkhoffGlobalSection.smooth_isotopy_contact_upgrade
-- status  : Open
-- author  : @caleb
-- created : 2026-10-01T01:07:22.459795+00:00
-- url     : https://prove2.me/theorems/448a1cf8-072b-48cc-a912-506a331a55a1
-- title:
--   Smooth equivariant isotopies upgrade to contact isotopies
-- statement:
--   Any smooth antipodally symmetric isotopy from the identity to an equivariant contactomorphism upgrades to a genuine contact isotopy.
--
--   Let $F$ be an equivariant contactomorphism of $(S^3, \xi_{\mathrm{std}})$ and let $G_t$ be a smooth antipodally symmetric isotopy with $G_0 = \mathrm{id}$ and $G_1 = F$ on the sphere. Then there exists an equivariant contact isotopy $I$ from $\mathrm{id}$ to $F$: the slices are equivariant contactomorphisms, jointly smooth in $(t, y)$, with $I_0 = \mathrm{id}$ and $I_1 = F$ on the sphere.
--
--   $$I : [0,1] \to \mathrm{Cont}^{\mathbb{Z}/2}(S^3), \quad I_0 = \mathrm{id},\; I_1 = F.
--   $$
--
--   This is the contact-flexibility half of the connectedness of the equivariant contactomorphism group: the loop of pushed-forward contact structures is null-homotopic, so equivariant Gray stability deforms the smooth isotopy into a contact one. Together with the smooth-existence half it yields an equivariant contact isotopy from the identity to every equivariant contactomorphism.
--
--   **Formalization Note** The smooth family $G$ is a hypothesis; the conclusion produces the contact isotopy structure.
-- source:
--   Gray, J. W., Some global properties of contact structures, Ann. of Math. 69 (1959) (Gray stability; see also Geiges, An Introduction to Contact Topology, Thm. 2.2.2); Eliashberg, Y., contactomorphism group of standard tight S^3 connected (Thm. 2.4.2); contact mapping class triviality for (L(2,1), standard structure), arXiv:2207.03590, Thm. 1.1 (otherwise case).

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem smooth_isotopy_contact_upgrade
    (F : EquivariantSphereContactomorphism)
    (Gto : ℝ → Phase → Phase)
    (hGsmooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => Gto p.1 p.2) (t, y))
    (hGmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Set.MapsTo (Gto t) unitThreeSphere unitThreeSphere)
    (hGanti : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
      Gto t (-y) = -Gto t y)
    (hGstart : ∀ y ∈ unitThreeSphere, Gto 0 y = y)
    (hGfinish : ∀ y ∈ unitThreeSphere, Gto 1 y = F.toFun y) :
    Nonempty (EquivariantSphereContactIsotopy F) := by sorry

end BirkhoffGlobalSection
