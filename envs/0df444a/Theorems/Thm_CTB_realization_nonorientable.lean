-- Prove2me | Theorems.Thm_CTB_realization_nonorientable
-- name    : CTB.realization_nonorientable
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:26.636505+00:00
-- url     : https://prove2.me/theorems/81e8e128-f003-4769-a49e-93b9ec007c5d
-- title:
--   The four non-orientable classes are realized (Theorems 4.1 and 4.5)
-- statement:
--   The four non-orientable classes are realized. For every n of at least three strings there are realizations of the classes B1 and B2, each with holonomy of order two; and for every n of at least four strings there are realizations of the classes B3 and B4, each with holonomy the Klein four group. Every realization is by a torsion-free subgroup of the crystallographic braid quotient. These are Theorems 4.1 and 4.5 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 4 (Theorems 4.1 and 4.5).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 5 (Theorems 4.1 and 4.5): the four non-orientable
classes are realized. For every n of at least three strings there are
realizations of the classes B1 and B2, each with holonomy of order two;
and for every n of at least four strings there are realizations of the
classes B3 and B4, each with holonomy the Klein four group. Every
realization is by a torsion-free subgroup of the crystallographic braid
quotient. -/
theorem realization_nonorientable {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    {B1 B2 B3 B4 : Type*} [Group B1] [Group B2] [Group B3] [Group B4] :
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B1),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) := by sorry

end CTB
