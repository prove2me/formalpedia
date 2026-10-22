-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_equivariant_diffeomorphism_smooth_isotopy
-- name    : BirkhoffGlobalSection.equivariant_diffeomorphism_smooth_isotopy
-- status  : Open
-- author  : @caleb
-- created : 2026-10-02T21:53:14.351875+00:00
-- url     : https://prove2.me/theorems/43c6cd8f-1c2f-4553-b12f-9f33803e6aea
-- title:
--   Diffeomorphism isotopy joining any equivariant contactomorphism
-- statement:
--   Every antipodally symmetric contactomorphism of the round three-sphere can be joined to the identity by a smooth antipodally symmetric isotopy through genuine diffeomorphisms.
--
--   Let $F$ be an equivariant contactomorphism of the unit three-sphere $S^3 \subset \mathbb{R}^4$ (antipodal symmetry, smooth with smooth inverse on the sphere). Then there is a one-parameter family $H_t$ of equivariant sphere diffeomorphisms, jointly smooth in $(t, y)$ in both directions on $[0,1] \times S^3$, with $H_0 = \mathrm{id}$ and $H_1 = F$ on the sphere.
--
--   $$H : [0,1] \times S^3 \to S^3, \quad H_0 = \mathrm{id},\; H_1 = F,$$
--
--   each slice a diffeomorphism with smoothly varying inverse.
--
--   This strengthens the smooth-maps isotopy to the diffeomorphism isotopy that Gray stability needs as input: $F$ descends to the real projective space $\mathbb{R}P^3$, the descended diffeomorphism is isotopic to the identity there through diffeomorphisms, the isotopy lifts back to $S^3$, and the antipodal endpoint ambiguity is resolved by an explicit rotation isotopy.
--
--   **Formalization Note** Unlike the maps-only version, every slice comes with a smooth inverse varying jointly smoothly in $(t, y)$; no contact condition is imposed on the slices.
-- source:
--   Hatcher, A. E., A proof of the Smale conjecture Diff(S^3) ≃ O(4), Ann. of Math. 117 (1983), 553-607; Bonahon, F., Difféotopies des espaces lenticulaires, Topology 22 (1983), 305-314 (mapping classes of L(2,1)); covering homotopy lift, e.g. Hatcher, Algebraic Topology, Prop. 1.33.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_BirkhoffGlobalSection_SphereDiffeoIsotopy
open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem equivariant_diffeomorphism_smooth_isotopy
    (F : EquivariantSphereContactomorphism) :
    Nonempty (EquivariantSphereDiffeoIsotopy F) := by sorry

end BirkhoffGlobalSection
