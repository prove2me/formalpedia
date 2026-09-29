-- Prove2me | solution 1 for topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/fb3e33ce-9c02-578a-ad7a-e09c3bcb3e0a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open TopologicalSpace in

theorem solution
    {T : Type} [TopologicalSpace T] {ι : Type} (W : ι → Set T) (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = Set.univ) :
    topologicalKrullDim T = ⨆ i, topologicalKrullDim ↥(W i) := by
  classical
  apply le_antisymm
  ·
    show Order.krullDim (IrreducibleCloseds T) ≤ ⨆ i, Order.krullDim (IrreducibleCloseds ↥(W i))
    rw [Order.krullDim]
    refine iSup_le (fun p => ?_)
    obtain ⟨x, hx⟩ := (p 0).isIrreducible'.nonempty
    obtain ⟨i, hi⟩ : ∃ i, x ∈ W i := by
      have : x ∈ ⋃ i, W i := by rw [hcov]; trivial
      simpa only [Set.mem_iUnion] using this
    have hmono : Monotone p := p.monotone
    have hxj : ∀ j : Fin (p.length + 1), x ∈ (p j : Set T) := fun j => hmono (Fin.zero_le j) hx
    have hne : ∀ j : Fin (p.length + 1), (((p j : Set T)) ∩ W i).Nonempty := fun j => ⟨x, hxj j, hi⟩
    have key : ∀ k : Fin (p.length + 1), (p k : Set T) = closure ((p k : Set T) ∩ W i) := by
      intro k
      apply le_antisymm
      · exact subset_closure_inter_of_isPreirreducible_of_isOpen (p k).isIrreducible'.isPreirreducible (hW i) (hne k)
      · exact (p k).isClosed'.closure_subset_iff.2 Set.inter_subset_left
    let r : Fin (p.length + 1) → IrreducibleCloseds ↥(W i) := fun j =>
      { carrier := Subtype.val ⁻¹' (p j : Set T)
        isIrreducible' := ⟨⟨⟨x, hi⟩, hxj j⟩,
          ((p j).isIrreducible'.isPreirreducible).preimage (hW i).isOpenEmbedding_subtypeVal⟩
        isClosed' := (p j).isClosed'.preimage continuous_subtype_val }
    have hr_carrier : ∀ j, ((r j : Set ↥(W i))) = Subtype.val ⁻¹' (p j : Set T) := fun j => rfl
    have hstep : ∀ j : Fin p.length, r (Fin.castSucc j) < r j.succ := by
      intro j
      have hlt : p (Fin.castSucc j) < p j.succ := p.step j
      refine lt_of_le_of_ne ?_ ?_
      · intro y hy
        show (y : T) ∈ (p j.succ : Set T)
        exact (le_of_lt hlt) hy
      · intro heq
        apply ne_of_lt hlt
        have h1 : (Subtype.val : ↥(W i) → T) ⁻¹' (p (Fin.castSucc j) : Set T) = Subtype.val ⁻¹' (p j.succ : Set T) := by
          rw [← hr_carrier, ← hr_carrier, heq]
        have hsets : (p (Fin.castSucc j) : Set T) ∩ W i = (p j.succ : Set T) ∩ W i := by
          have := congrArg (fun A : Set ↥(W i) => (Subtype.val '' A)) h1
          simpa only [Subtype.image_preimage_coe, Set.inter_comm] using this
        apply IrreducibleCloseds.ext
        rw [key (Fin.castSucc j), key j.succ, hsets]
    let q : LTSeries (IrreducibleCloseds ↥(W i)) := { length := p.length, toFun := r, step := hstep }
    calc ((p.length : ℕ) : WithBot ℕ∞) = q.length := rfl
      _ ≤ Order.krullDim (IrreducibleCloseds ↥(W i)) := Order.LTSeries.length_le_krullDim q
      _ ≤ ⨆ i, Order.krullDim (IrreducibleCloseds ↥(W i)) := le_iSup (fun i => Order.krullDim (IrreducibleCloseds ↥(W i))) i
  · exact iSup_le (fun i => topologicalKrullDim_subspace_le T (W i))

end S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
end P2MW
export P2MW.S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ (solution)
