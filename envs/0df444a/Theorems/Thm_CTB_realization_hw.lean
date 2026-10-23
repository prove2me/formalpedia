-- Prove2me | Theorems.Thm_CTB_realization_hw
-- name    : CTB.realization_hw
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:50.494081+00:00
-- url     : https://prove2.me/theorems/b5eab80e-c4c8-4ac4-a862-78afc77819be
-- title:
--   The Hantzsche-Wendt class is realized (Theorem 3.9)
-- statement:
--   The Hantzsche-Wendt class is realized. For every n of at least four strings there is a realization of the class G6 - the fundamental group of the Hantzsche-Wendt manifold - by a torsion-free subgroup of the crystallographic braid quotient whose holonomy group is the Klein four group. This is Theorem 3.9 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 3 (Theorem 3.9).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 4 (Theorem 3.9): the Hantzsche-Wendt class is realized.
For every n of at least four strings there is a realization of the class
G6, the fundamental group of the Hantzsche-Wendt manifold, by a
torsion-free subgroup of the crystallographic braid quotient whose
holonomy group is the Klein four group. -/
theorem realization_hw {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    {G6 : Type*} [Group G6] (hn : 4 ≤ n) :
    ∃ (Gam Ker : Subgroup Q) (f : Q →* G6),
      IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
      Nonempty (Subgroup.map W.hol Gam ≃* Multiplicative (Fin 2 → ZMod 2)) := by sorry

end CTB
