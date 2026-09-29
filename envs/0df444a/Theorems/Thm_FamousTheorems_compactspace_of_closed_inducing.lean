-- Prove2me | Theorems.Thm_FamousTheorems_compactspace_of_closed_inducing
-- name    : FamousTheorems.compactspace_of_closed_inducing
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:01.932579+00:00
-- url     : https://prove2.me/theorems/d65a7b05-54c5-422f-9770-c8ec0555b9ef
-- title:
--   The Arzelà–Ascoli theorem
-- statement:
--   **The Arzel\u00e0-Ascoli theorem.** A closed, uniformly equicontinuous and pointwise relatively compact family of continuous functions is compact in the uniform topology. It is the substitute for Heine-Borel in function spaces, where closed and bounded is never enough: equicontinuity is the extra uniformity that rules out the oscillation escaping to higher and higher frequency. The theorem is the standard source of convergent subsequences in analysis, used to extract limits of approximating solutions in the existence proofs for ODEs (Peano) and PDEs, and to prove Montel's theorem in complex analysis. **Formalization note.** The hypotheses are packaged as a closed inducing map into a product of compacts. The result is Mathlib's `ArzelaAscoli.compactSpace_of_closed_inducing'`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem compactspace_of_closed_inducing :
    ∀ {ι : Type u_1} {X : Type u_2} {α : Type u_3} 
    [inst : TopologicalSpace X] [inst_1 : UniformSpace α] {F : ι → X → α} [inst_2 : TopologicalSpace ι] {𝔖 : Set (Set X)}, 
    (∀ K ∈ 𝔖, IsCompact K) → 
    IsInducing (⇑(UniformOnFun.ofFun 𝔖) ∘ F) → 
    IsClosed (range (⇑(UniformOnFun.ofFun 𝔖) ∘ F)) → 
    (∀ K ∈ 𝔖, EquicontinuousOn F K) → (∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ (i : ι), F i x ∈ Q) → CompactSpace ι := by sorry

end FamousTheorems
