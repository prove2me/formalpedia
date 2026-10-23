-- Prove2me | Theorems.Thm_CTB_preimage_bieberbach
-- name    : CTB.preimage_bieberbach
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:08:48.559379+00:00
-- url     : https://prove2.me/theorems/1d5c2988-a2fe-464b-9bf5-a7481aa57826
-- title:
--   The preimage of a two-power holonomy subgroup is Bieberbach (Proposition 2.5)
-- statement:
--   The full preimage of a finite 2-group of holonomies is Bieberbach. If a subgroup of the symmetric group consists of elements of two-power order, then the preimage under the holonomy projection is torsion-free - the absence of even-order torsion in the braid quotient forces any torsion element into the translation lattice, where powers vanish only trivially - the holonomy projection maps the preimage back onto the subgroup, and the translation lattice is contained in it. This is Proposition 2.5 of the paper, the preimage lemma of the companion paper restated in the present setting.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 2 (Proposition 2.5).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 1 (Proposition 2.5): the full preimage of a finite
2-group of holonomies is Bieberbach. If H is a subgroup of the symmetric
group all of whose elements are of two-power order, then the preimage of
H under the holonomy projection is torsion-free - a Bieberbach group -
and the holonomy projection maps this preimage back onto H, while the
translation lattice is contained in it. -/
theorem preimage_bieberbach {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ g : Equiv.Perm (Fin n), g ∈ H → IsTwoTorsion g) :
    TorsionFree ↥(Subgroup.comap W.hol H) ∧
    Subgroup.map W.hol (Subgroup.comap W.hol H) = H ∧
    W.lattice ≤ Subgroup.comap W.hol H := by sorry

end CTB
