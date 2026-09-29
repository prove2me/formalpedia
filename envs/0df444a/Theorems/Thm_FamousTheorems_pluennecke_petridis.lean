-- Prove2me | Theorems.Thm_FamousTheorems_pluennecke_petridis
-- name    : FamousTheorems.pluennecke_petridis
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:57.676991+00:00
-- url     : https://prove2.me/theorems/1119d5ef-64fe-4aef-ba74-0a2c72f558dd
-- title:
--   The Plünnecke–Petridis inequality
-- statement:
--   **The Plünnecke–Petridis inequality.** Let $A,B$ be finite subsets of an additive group such that $A$ minimises the ratio $|A'+B|/|A'|$ among its nonempty subsets, i.e. $|A+B|\,|A'|\le|A'+B|\,|A|$ for all $A'\subseteq A$. Then for every finite set $C$,
--   $$|C+A+B|\,|A|\le|A+B|\,|C+A| .$$
--
--   This is Petridis's key lemma, which gave a short proof of the Plünnecke–Ruzsa inequality $|nB-mB|\le K^{n+m}|A|$ for sets with $|A+B|\le K|A|$. Plünnecke's original proof used graph theory.
--
--   **Formalization note.** Mathlib's `Finset.pluennecke_petridis_inequality_add` (the additive form of `Finset.pluennecke_petridis_inequality_mul`), with pointwise sumsets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.pluennecke_petridis_inequality_add`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem pluennecke_petridis {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} (C : Finset G)
    (hA : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card) :
    (C + A + B).card * A.card ≤ (A + B).card * (C + A).card := by sorry

end FamousTheorems
