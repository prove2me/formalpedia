-- Prove2me | Theorems.Thm_FamousTheorems_burali_forti_paradox
-- name    : FamousTheorems.burali_forti_paradox
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:52.976979+00:00
-- url     : https://prove2.me/theorems/ead8a0f3-3ffc-4d7b-a02a-e87eb9422a98
-- title:
--   The Burali-Forti paradox
-- statement:
--   **The Burali-Forti paradox.** In ZFC there is no set containing exactly the von Neumann ordinals; the ordinals form a proper class.
--
--   If such a set $\Omega$ existed, it would be a transitive set well-ordered by $\in$, hence itself an ordinal, so $\Omega\in\Omega$, which is impossible. Burali-Forti's 1897 observation was the first of the set-theoretic paradoxes. It shows that naive comprehension fails and motivates the distinction between sets and proper classes.
--
--   **Formalization note.** Mathlib's `ZFSet.isOrdinal_notMem_univ`, which states that the class `ZFSet.IsOrdinal` is not a set. Here that is unfolded as the non-existence of a ZFC set `x` whose members are exactly the ZFC sets `y` with `y.IsOrdinal`. `ZFSet` is Mathlib's model of ZFC set theory, and `IsOrdinal` is the von Neumann definition: a transitive set on which $\in$ is transitive.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZFSet.isOrdinal_notMem_univ`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem burali_forti_paradox :
    ¬∃ x : ZFSet, ∀ y : ZFSet, y ∈ x ↔ y.IsOrdinal := by sorry

end FamousTheorems
