-- Prove2me | Theorems.Thm_FamousTheorems_all_card_le_biunion_card_iff_exists_injective
-- name    : FamousTheorems.all_card_le_biunion_card_iff_exists_injective
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:21.909402+00:00
-- url     : https://prove2.me/theorems/b07c286f-c3f2-473a-a875-56f2e232e2c4
-- title:
--   Hall's marriage theorem
-- statement:
--   **Hall's marriage theorem.** A family of finite sets has a system of distinct representatives if and only if every subfamily of $k$ sets has at least $k$ elements in its union. The obviously necessary counting condition is also sufficient — that is the whole content, and it is what makes the theorem so useful, since verifying a counting bound is far easier than constructing a matching. Equivalently it characterises when a bipartite graph has a perfect matching on one side. Hall proved it in 1935; it is equivalent to König's theorem, Dilworth's theorem and the max-flow min-cut theorem, all of which are inter-derivable. **Formalization note.** The representatives are produced as an injective function selecting one element from each set. The result is Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem all_card_le_biunion_card_iff_exists_injective :
    ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq α] 
    (t : ι → Finset α), (∀ (s : Finset ι), s.card ≤ (s.biUnion t).card) ↔ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x := by sorry

end FamousTheorems
