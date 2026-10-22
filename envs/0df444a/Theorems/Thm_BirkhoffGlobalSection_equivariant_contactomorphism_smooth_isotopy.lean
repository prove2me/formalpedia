-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_equivariant_contactomorphism_smooth_isotopy
-- name    : BirkhoffGlobalSection.equivariant_contactomorphism_smooth_isotopy
-- status  : Open
-- author  : @caleb
-- created : 2026-10-01T01:07:20.444047+00:00
-- url     : https://prove2.me/theorems/3cf6d687-d98b-4c16-a98d-7935041651b6
-- title:
--   Smooth equivariant isotopy to any equivariant contactomorphism
-- statement:
--   Every antipodally symmetric contactomorphism of the round three-sphere can be joined to the identity by a smooth antipodally symmetric isotopy.
--
--   Let $F$ be an equivariant contactomorphism of the unit three-sphere $S^3 \subset \mathbb{R}^4$ (antipodal symmetry, smooth with smooth inverse on the sphere). Then there is a one-parameter family $G_t$ of sphere maps, jointly smooth in $(t, y)$ on $[0,1] \times S^3$, with each slice antipodally symmetric, $G_0 = \mathrm{id}$, and $G_1 = F$ on the sphere.
--
--   $$G : [0,1] \times S^3 \to S^3, \quad G_0 = \mathrm{id},\; G_1 = F,\; G_t(-y) = -G_t(y).
--   $$
--
--   This is the smooth (non-contact) half of the connectedness of the equivariant contactomorphism group: $F$ descends to the real projective space $\mathbb{R}P^3$, the descended diffeomorphism is isotopic to the identity there, the isotopy lifts back to $S^3$, and the antipodal endpoint ambiguity is resolved by an explicit rotation isotopy.
--
--   **Formalization Note** Only joint smoothness, sphere preservation, antipodal symmetry, and the endpoint equalities are asserted; no contact condition is imposed on the slices.
-- source:
--   Hatcher, A. E., A proof of the Smale conjecture Diff(S^3) ≃ O(4), Ann. of Math. 117 (1983), 553-607; Bonahon, F., Difféotopies des espaces lenticulaires, Topology 22 (1983), 305-314 (mapping classes of L(2,1)); covering homotopy lift, e.g. Hatcher, Algebraic Topology, Prop. 1.33.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem equivariant_contactomorphism_smooth_isotopy
    (F : EquivariantSphereContactomorphism) :
    ∃ Gto : ℝ → Phase → Phase,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
        ContDiffAt ℝ ∞ (fun p : ℝ × Phase => Gto p.1 p.2) (t, y))
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Set.MapsTo (Gto t) unitThreeSphere unitThreeSphere)
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
        Gto t (-y) = -Gto t y)
      ∧ (∀ y ∈ unitThreeSphere, Gto 0 y = y)
      ∧ (∀ y ∈ unitThreeSphere, Gto 1 y = F.toFun y) := by sorry

end BirkhoffGlobalSection
