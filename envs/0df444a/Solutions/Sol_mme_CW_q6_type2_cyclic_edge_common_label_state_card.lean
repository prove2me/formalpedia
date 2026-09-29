-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_edge_common_label_state_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:58:55.054529+00:00
-- url     : https://prove2.me/submissions/d7a4cd32-6d59-487f-8f19-c0a71931b8b3

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hN : 0 < N)
    (e : CWQ6Type2CyclicEdge N L G) (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cwQ6Type2CyclicAffineHash p N L G
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
    cwQ6Type2CyclicAffineHash p N L G
      (weights q.1, (6 : ZMod p)⁻¹ * q.2) i e
  change ((Finset.univ.filter
    (fun q : (I → ZMod p) × ZMod p ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) = _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  obtain ⟨r, j, hpivot⟩ :=
    mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
      hp hN e (0 : Fin 3)
  let c : I → ZMod p
    | Sum.inl x => cwQ6Type2CyclicHashModeCode p N 0
        (cwQ6Type2CyclicModeWord e 0) x.1 x.2
    | Sum.inr _ => 0
  have hc : c (Sum.inl (r, j)) ≠ 0 := by
    simpa [c] using hpivot
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N 0
        (cwQ6Type2CyclicModeWord e 0) r j * w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N 2
        (cwQ6Type2CyclicModeWord e 2) r j * w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) : H q 0 = L0 q.1 := by
    simpa [H, weights, L0] using
      (mme_CW_q6_type2_cyclic_affine_hash_normal_form
        (p := p) (N := N) (L := L) (G := G)
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) : H q 2 = q.2 + L2 q.1 := by
    rw [show H q 2 = 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, L2] using
        (mme_CW_q6_type2_cyclic_affine_hash_normal_form
          (p := p) (N := N) (L := L) (G := G)
          (weights q.1, (6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hAP (q : (I → ZMod p) × ZMod p) :
      H q 0 + H q 1 = 2 * H q 2 := by
    let q0 : ZMod p := (6 : ZMod p)⁻¹ * q.2
    have ha := mme_CW_q6_doubled_hash_AP_identity
      (2 * q0) (weights q.1 0) e.1.1 e.1.1 e.1.1 e.1.2.1
    have hb := mme_CW_q6_doubled_hash_AP_identity
      0 (weights q.1 1) e.2.1.1 e.2.1.1 e.2.1.1 e.2.1.2.1
    have hd := mme_CW_q6_doubled_hash_AP_identity
      q0 (weights q.1 2) e.2.2.1 e.2.2.1 e.2.2.1 e.2.2.2.1
    dsimp only [H, cwQ6Type2CyclicAffineHash]
    change _ + _ = 2 * _
    linear_combination ha - 2 * hb - 2 * hd
  have hret (q : (I → ZMod p) × ZMod p) :
      (∃ s ∈ S, ∀ i : Fin 3, H q i = s) ↔
        L0 q.1 ∈ S ∧ q.2 = offset q.1 := by
    constructor
    · rintro ⟨s, hs, hcommon⟩
      refine ⟨?_, ?_⟩
      · have h0 := hcommon 0
        rw [hH0 q] at h0
        exact h0 ▸ hs
      · have h0 := hcommon 0
        have h2 := hcommon 2
        rw [hH0 q] at h0
        rw [hH2 q] at h2
        dsimp only [offset]
        linear_combination h2 - h0
    · rintro ⟨hS, hq⟩
      refine ⟨L0 q.1, hS, ?_⟩
      intro i
      fin_cases i
      · exact hH0 q
      · change H q 1 = L0 q.1
        have hap := hAP q
        rw [hH0 q] at hap
        have h2 : H q 2 = L0 q.1 := by
          rw [hH2 q]
          dsimp only [offset] at hq
          linear_combination hq
        rw [h2] at hap
        linear_combination hap
      · change H q 2 = L0 q.1
        rw [hH2 q]
        dsimp only [offset] at hq
        linear_combination hq
  have hL0sum (w : I → ZMod p) :
      L0 w = ∑ x : I, c x * w x := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c, L0]
  have hset :
      Finset.univ.filter
          (fun q : (I → ZMod p) × ZMod p ↦
            ∃ s ∈ S, ∀ i : Fin 3, H q i = s) =
        Finset.univ.filter
          (fun q : (I → ZMod p) × ZMod p ↦
            (∑ x, c x * q.1 x) ∈ S ∧ q.2 = offset q.1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hret q, hL0sum q.1]
  rw [hset]
  exact mme_ZMod_prime_linear_hash_affine_graph_fintype_card
    hcard c (Sum.inl (r, j)) hc S offset
