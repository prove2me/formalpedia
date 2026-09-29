-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_edge_retention_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:52:37.569901+00:00
-- url     : https://prove2.me/submissions/b6df9709-f1c4-40e5-8272-ef63dad644bd

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_AP
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : CyclicAmbientEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
    cyclicAffineHash p N alpha beta gamma delta
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
  change ((Finset.univ.filter
    (fun q : (I → ZMod p) × ZMod p ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) = _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  let c : I → ZMod p
    | Sum.inl x => cyclicHashModeCode p N 0
        (cyclicModeWord e 0) x.1 x.2
    | Sum.inr _ => 1
  have hc : c (Sum.inr ()) ≠ 0 := by
    simp [c]
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 0 (cyclicModeWord e 0) r j *
        w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 2 (cyclicModeWord e 2) r j *
        w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) :
      H q 0 = shift q.1 + L0 q.1 := by
    simpa [H, weights, shift, L0] using
      (mme_stothers_phi233_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) (delta := delta)
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi233_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hAP (q : (I → ZMod p) × ZMod p) :
      H q 0 + H q 1 = 2 * H q 2 := by
    have hmixed (a : MarginalAddress N alpha beta gamma delta) :
        mixedAddress a a a = a.1 := by
      funext i j
      fin_cases i <;> rfl
    have hsupp : CyclicCoordinatewiseSupported e e e := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hmixed]
        exact e.1.2.1
      · rw [hmixed]
        exact e.2.1.2.1
      · rw [hmixed]
        exact e.2.2.2.1
    exact mme_stothers_phi233_cyclic_affine_hash_AP
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2)
      e e e hsupp
  have hret (q : (I → ZMod p) × ZMod p) :
      (∃ s ∈ S, ∀ i : Fin 3, H q i = s) ↔
        shift q.1 + L0 q.1 ∈ S ∧ q.2 = offset q.1 := by
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
      refine ⟨shift q.1 + L0 q.1, hS, ?_⟩
      intro i
      fin_cases i
      · exact hH0 q
      · change H q 1 = shift q.1 + L0 q.1
        have hap := hAP q
        rw [hH0 q] at hap
        have h2 : H q 2 = shift q.1 + L0 q.1 := by
          rw [hH2 q]
          dsimp only [offset] at hq
          linear_combination hq
        rw [h2] at hap
        linear_combination hap
      · change H q 2 = shift q.1 + L0 q.1
        rw [hH2 q]
        dsimp only [offset] at hq
        linear_combination hq
  have hL0sum (w : I → ZMod p) :
      shift w + L0 w = ∑ x : I, c x * w x := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c, shift, L0]
    ring
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
    hcard c (Sum.inr ()) hc S offset
