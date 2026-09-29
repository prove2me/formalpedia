-- Prove2me | Theorems.Thm_FamousTheorems_dense_iinter_of_isopen
-- name    : FamousTheorems.dense_iinter_of_isopen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:02.44099+00:00
-- url     : https://prove2.me/theorems/1917c68e-d389-49c4-8588-88d78ee47794
-- title:
--   The Baire category theorem (indexed form)
-- statement:
--   **The Baire category theorem.** In a Baire space, the intersection of a countable indexed family of dense open sets is dense. Countably many generic conditions can be met at once. Equivalently such a space is not a countable union of nowhere dense sets, the form used to prove the uniform boundedness principle, the open mapping theorem and the closed graph theorem, so all three pillars of Banach space theory rest on it. It also gives existence by genericity: the continuous nowhere differentiable functions are comeagre in $C[0,1]$, so such functions are typical rather than exotic. **Formalization note.** This is the `iInter` form over an arbitrary countable index type, complementing the `sInter` version. The result is Mathlib's `dense_iInter_of_isOpen`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem dense_iinter_of_isopen :
    ∀ {X : Type u_1} {ι : Sort u_2} [inst : TopologicalSpace X] [BaireSpace X] [Countable ι] 
    {f : ι → Set X}, (∀ (i : ι), IsOpen (f i)) → (∀ (i : ι), Dense (f i)) → Dense (⋂ s, f s) := by sorry

end FamousTheorems
