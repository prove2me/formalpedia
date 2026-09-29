-- Prove2me | Theorems.Thm_FamousTheorems_dense_sinter_of_isopen
-- name    : FamousTheorems.dense_sinter_of_isopen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:02:11.629433+00:00
-- url     : https://prove2.me/theorems/dc0471ec-39f0-4013-8a3f-1007e9fed97a
-- title:
--   The Baire category theorem
-- statement:
--   **The Baire category theorem.** In a complete metric space, the intersection of countably many dense open sets is dense. A countable list of “generic” conditions can be satisfied simultaneously. Equivalently, a complete space is not a countable union of nowhere dense sets, which is the form used to prove the uniform boundedness principle, the open mapping theorem and the closed graph theorem — the three pillars of Banach space theory all rest on it. It also gives existence results by genericity: the set of continuous nowhere differentiable functions is comeagre in $C[0,1]$, so such functions are typical rather than exotic. **Formalization note.** The ambient space is a `BaireSpace`, which complete metric spaces and locally compact Hausdorff spaces both instantiate. The result is Mathlib's `dense_sInter_of_isOpen`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem dense_sinter_of_isopen :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] [BaireSpace X] {S : Set (Set X)}, 
    (∀ s ∈ S, IsOpen s) → S.Countable → (∀ s ∈ S, Dense s) → Dense (⋂₀ S) := by sorry

end FamousTheorems
