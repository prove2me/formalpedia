-- Prove2me | Theorems.Thm_CTB_realization_cyclic
-- name    : CTB.realization_cyclic
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:12.655919+00:00
-- url     : https://prove2.me/theorems/4332c227-d62e-485d-9bdb-9e90031942d5
-- title:
--   The orientable classes with cyclic holonomy are realized (Theorems 3.1, 3.2, 3.3, and 3.7)
-- statement:
--   The orientable classes with cyclic holonomy are realized. For every n of at least four strings there is a realization of the class G2 with holonomy of order two; for every n of at least three strings a realization of the class G3 with holonomy of order three; for every n of at least four strings a realization of the class G4 with holonomy of order four; and for every n of at least five strings a realization of the class G5 with holonomy of order six. Each realization is by a torsion-free subgroup of the crystallographic braid quotient. These are Theorems 3.1, 3.2, 3.3, and 3.7 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 3 (Theorems 3.1, 3.2, 3.3, and 3.7).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 3 (Theorems 3.1, 3.2, 3.3 and 3.7): the orientable
classes with cyclic holonomy are realized. For every n of at least four
strings there is a realization of the class G2 with holonomy of order
two; for every n of at least three strings there is a realization of the
class G3 with holonomy of order three; for every n of at least four
strings there is a realization of the class G4 with holonomy of order
four; and for every n of at least five strings there is a realization of
the class G5 with holonomy of order six. Each realization is by a
torsion-free subgroup of the crystallographic braid quotient. -/
theorem realization_cyclic {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    {G2 G3 G4 G5 : Type*} [Group G2] [Group G3] [Group G4] [Group G5] :
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) ∧
    (5 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G5),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam) := by sorry

end CTB
