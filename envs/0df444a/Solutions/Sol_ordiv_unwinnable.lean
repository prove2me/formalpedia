-- Prove2me | solution 1 for ordiv_unwinnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:23.139814+00:00
-- url     : https://prove2.me/submissions/1b38b88e-4952-48d1-9eee-60e7c7c9dd5d

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_principal_iff_eq_prin
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (O : CFOrientation G) :
  is_acyclic G O → ¬ winnable G (ordiv G O) := by
  intro h_acyclic
  by_contra h_win
  let D := ordiv G O
  rcases h_win with ⟨E, E_eff, E_equiv⟩
  dsimp only [Eff] at E_eff
  dsimp only [linear_equiv] at E_equiv
  rw [principal_iff_eq_prin] at E_equiv
  rcases E_equiv with ⟨σ, h_σ⟩
  apply eq_add_of_sub_eq at h_σ

  obtain ⟨v_max, -, h_max⟩ := Finset.exists_max_image Finset.univ σ Finset.univ_nonempty
  have h_max : ∀ w : G.V, σ w ≤ σ v_max := fun w => h_max w (Finset.mem_univ w)
  let S := {v : G.V | σ v = σ v_max}
  have S_nonempty : S.Nonempty := by
    use v_max
    simp only [Set.mem_ofPred_eq, S]

  have h_lt (u : G.V) (h_u : u ∉ S):  σ u ≤ σ v_max - 1 := by
    specialize h_max u
    suffices σ u < σ v_max by linarith
    apply lt_of_le_of_ne h_max
    simp only [Set.mem_ofPred_eq, S] at h_u
    exact h_u

  suffices h_v : ∃ v ∈ S, ∀ w : G.V, flow O w v > 0 → w ∉ S by
    rcases h_v with ⟨v, h_v, h_flow⟩
    have h_prin : (prin G) σ v + indeg G O v ≤ 0 := by
      rw [prin_apply]
      rw [indeg_eq_sum_flow O v]
      have h_diff : ∀ u : G.V, σ u - σ v ≤ if u ∈ S then 0 else -1 := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp only [h_u_in_S, ↓reduceIte, tsub_le_iff_right, zero_add]
          -- Goal is now: σ u ≤ σ v
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
        · simp only [h_u_in_S, ↓reduceIte, Int.reduceNeg, tsub_le_iff_right, le_neg_add_iff_add_le]
          -- Goal is now: σ u - σ v ≤ -1
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          have := h_lt u h_u_in_S
          rw [h_v]
          linarith [this]
      have h_diff_mul : ∀ u : G.V, (σ u - σ v) * ↑(num_edges G v u) ≤ if u ∈ S then 0 else -↑(num_edges G v u) := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp only [h_u_in_S, ↓reduceIte]
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
          simp only [sub_self, zero_mul, Std.le_refl]
        · simp only [h_u_in_S, ↓reduceIte]
          have ineq := h_lt u h_u_in_S
          rw [← h_v] at ineq
          apply le_of_sub_nonneg
          rw [neg_eq_neg_one_mul, ← sub_mul]
          apply mul_nonneg
          linarith
          exact Nat.cast_nonneg _
      have h_sum : ∑ w : G.V, (σ w - σ v) * ↑(num_edges G v w) ≤ ∑ w : G.V, if w ∈ S then 0 else -↑(num_edges G v w) := by
        apply Finset.sum_le_sum
        intro u _
        specialize h_diff_mul u

        exact h_diff_mul
      suffices ∑ u : G.V, ((σ u - σ v) * ↑(num_edges G v u)) ≤ -↑ (∑ u: G.V, (flow O u v)) by linarith
      refine le_trans h_sum ?_
      apply le_of_neg_le_neg
      rw [neg_neg, Nat.cast_sum, neg_eq_neg_one_mul, mul_comm (-1), Finset.sum_mul]


      apply sum_le_sum

      intro u _
      by_cases h_u_in_S : u ∈ S
      · -- Case: u ∈ S. No edges from u to v.
        simp only [h_u_in_S]
        rw [ite_true]
        contrapose! h_flow
        use u
        norm_num at h_flow
        exact ⟨h_flow, h_u_in_S⟩
      · -- Case : u ∉ S.
        simp only [h_u_in_S, ↓reduceIte, Int.reduceNeg, mul_neg, mul_one, neg_neg, Nat.cast_le]
        -- Goal: flow O u v ≤ num_edges G v u
        rw [← opp_flow O v u]
        linarith
    specialize E_eff v
    rw [h_σ] at E_eff
    rw [Pi.add_apply] at E_eff
    dsimp only [ordiv] at E_eff
    linarith
  -- Now we must find a source of O relative to S
  let S' := Finset.filter (λ v => v ∈ S) Finset.univ
  have S'_nonempty : S'.Nonempty := by
    rcases S_nonempty with ⟨v, h_v_in_S⟩
    use v
    simp only [Finset.mem_filter, mem_univ, true_and, S']
    exact h_v_in_S
  have h := subset_source G O S' S'_nonempty h_acyclic
  rcases h with ⟨v, h_v_in_S', h_flow⟩
  use v
  simp only [Finset.mem_filter, mem_univ, true_and, S'] at h_v_in_S'
  constructor
  · exact h_v_in_S'
  · intro w h_flow_w_v
    specialize h_flow w
    by_contra!
    have : w ∈ S' := by
      simp only [Finset.mem_filter, mem_univ, true_and, S']
      exact this
    apply h_flow at this
    linarith
