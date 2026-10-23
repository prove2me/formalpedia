-- Prove2me | Theorems.Thm_CTB_splitting_classification
-- name    : CTB.splitting_classification
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:12:37.375576+00:00
-- url     : https://prove2.me/theorems/25ab5c38-16e2-474e-9980-36b2498d72ba
-- title:
--   The torus-bundle extensions split for exactly four classes (Theorem 5.3)
-- statement:
--   The torus-bundle extensions of the realizations split for the torus and for the classes with holonomy of order three and the two order-two non-orientable classes, and do not split for the remaining six classes. A section of a realization is a homomorphism from the model group back into the braid quotient, landing in the total-space subgroup and composed with the realization map to the identity. The classes G1, G3, B1, and B2 admit a realization with a section; the classes G2, G4, G5, G6, B3, and B4 admit a realization with no section. This is Theorem 5.3 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 5 (Theorem 5.3).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 7 (Theorem 5.3): the torus-bundle extensions of the
realizations split for the torus and for the classes with holonomy of
order three and the two order-two non-orientable classes, and do not
split for the remaining six classes. A section of a realization is a
homomorphism from the model group back into the braid quotient, landing
in the total-space subgroup and composed with f to the identity. The
classes G1, G3, B1 and B2 admit a realization with a section; the
classes G2, G4, G5, G6, B3 and B4 admit a realization with no section. -/
theorem splitting_classification {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    {G1 G2 G3 G4 G5 G6 B1 B2 B3 B4 : Type*}
    [Group G1] [Group G2] [Group G3] [Group G4] [Group G5] [Group G6]
    [Group B1] [Group B2] [Group B3] [Group B4] :
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G1),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : G1 →* Q, (∀ y : G1, s y ∈ Gam) ∧ ∀ y : G1, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G2 →* Q, (∀ y : G2, s y ∈ Gam) ∧ ∀ y : G2, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : G3 →* Q, (∀ y : G3, s y ∈ Gam) ∧ ∀ y : G3, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G4 →* Q, (∀ y : G4, s y ∈ Gam) ∧ ∀ y : G4, f (s y) = y) ∧
    (5 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G5),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G5 →* Q, (∀ y : G5, s y ∈ Gam) ∧ ∀ y : G5, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G6),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G6 →* Q, (∀ y : G6, s y ∈ Gam) ∧ ∀ y : G6, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B1),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : B1 →* Q, (∀ y : B1, s y ∈ Gam) ∧ ∀ y : B1, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : B2 →* Q, (∀ y : B2, s y ∈ Gam) ∧ ∀ y : B2, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : B3 →* Q, (∀ y : B3, s y ∈ Gam) ∧ ∀ y : B3, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : B4 →* Q, (∀ y : B4, s y ∈ Gam) ∧ ∀ y : B4, f (s y) = y) := by sorry

end CTB
