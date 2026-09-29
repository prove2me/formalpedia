-- Prove2me | Theorems.Thm_FamousTheorems_finite_nilpotent_group_characterization_6c
-- name    : FamousTheorems.finite_nilpotent_group_characterization_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:13.507068+00:00
-- url     : https://prove2.me/theorems/66e6cd55-8fd3-4d81-b512-badf1f67c276
-- title:
--   Characterisation of finite nilpotent groups (direct product of Sylow subgroups)
-- statement:
--   **Characterisation of finite nilpotent groups.** For a finite group $G$, the following are equivalent:
--   1. $G$ is nilpotent;
--   2. $G$ satisfies the normaliser condition: every proper subgroup $H$ is properly contained in its normaliser $N_G(H)$;
--   3. every maximal subgroup of $G$ is normal;
--   4. every Sylow subgroup of $G$ is normal;
--   5. $G$ is isomorphic to the direct product of its Sylow subgroups.
--
--   This is the standard structure theorem for finite nilpotent groups. It reduces their study to finite $p$-groups, and it shows that a finite nilpotent group has a unique Sylow $p$-subgroup for each prime $p$.
--
--   **Formalization note.** Mathlib's `Group.isNilpotent_of_finite_tfae`. `NormalizerCondition G` is condition 2, and maximal subgroups are the coatoms of the subgroup lattice. The direct product in (5) runs over all primes $p$ dividing $|G|$ and all Sylow $p$-subgroups; since (5) forces each Sylow subgroup to be unique, this is the product of one Sylow subgroup for each prime.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Group.isNilpotent_of_finite_tfae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem finite_nilpotent_group_characterization_6c {G : Type*} [Group G] [Finite G] :
    List.TFAE
      [Group.IsNilpotent G, NormalizerCondition G, ∀ H : Subgroup G, IsCoatom H → H.Normal,
        ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Normal,
        Nonempty ((∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, (P : Subgroup G)) ≃* G)] := by sorry

end FamousTheorems
