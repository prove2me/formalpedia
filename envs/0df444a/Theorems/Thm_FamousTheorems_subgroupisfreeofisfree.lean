-- Prove2me | Theorems.Thm_FamousTheorems_subgroupisfreeofisfree
-- name    : FamousTheorems.subgroupisfreeofisfree
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:59.496985+00:00
-- url     : https://prove2.me/theorems/61b9883d-b211-4bfc-80ca-e312d12b71ce
-- title:
--   The Nielsen–Schreier theorem
-- statement:
--   **The Nielsen-Schreier theorem.** Every subgroup of a free group is free. This fails for most algebraic structures and is a defining structural feature of free groups. The modern proof is topological: a free group is the fundamental group of a wedge of circles, subgroups correspond to covering spaces, a covering of a graph is a graph, and the fundamental group of a graph is free. The rank behaves counterintuitively, a finite-index subgroup of a free group of rank $r$ having rank $1 + [G:H](r-1)$, so subgroups can have far larger rank than the ambient group. Nielsen proved the finitely generated case in 1921, Schreier the general one in 1927. **Formalization note.** The hypothesis is `IsFreeGroup` on the ambient group. The result is Mathlib's `subgroupIsFreeOfIsFree`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem subgroupisfreeofisfree :
    ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G] (H : Subgroup G), IsFreeGroup ↥H := by sorry

end FamousTheorems
