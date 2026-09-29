-- Prove2me | solution 1 for mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:04:25.854617+00:00
-- url     : https://prove2.me/submissions/fcec76f8-89a5-4a13-bf91-3d93bea0cc7f

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem card_product_filter_eq_sum_gap
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (B : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    ((W.product B).filter (fun p => P p.1 p.2)).card =
      ∑ w ∈ W, (B.filter (fun b => P w b)).card := by
  simp only [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ W.product B, if P a.1 a.2 then 1 else 0) =
        ∑ w ∈ W, ∑ b ∈ B, if P w b then 1 else 0 := by
      exact Finset.sum_product W B
        (fun p => if P p.1 p.2 then 1 else 0)
    _ = ∑ w ∈ W, ∑ b ∈ B with P w b, 1 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_filter]

/-- Pre-averaging form of the arbitrary-gap aggregation.  Keeping the whole
sum over affine parameters makes this directly composable with a collision
moment indexed by the same parameter. -/
theorem solution
    {M n L G B H R : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (Z : Finset (Fin (2 * (n + 1)) → Fin 3))
    (A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (hz : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z)
    (hcard : ∀ z ∈ Z, (A z).card = B)
    (hgap : M * H + R ≤ B)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let degree :
        (Fin (2 * (n + 1)) → Fin 3) →
          (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
      ((A z).attach.filter (fun e =>
        ∑ i,
          ((2 * ((e.1.1 0 i).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
    R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card ≤
      R ^ 2 *
          (∑ q : ((Fin (2 * n + 2) → ZMod M) × ZMod M),
            (Z.filter (fun z =>
              H ≤ degree z q.1 ∧
                ∃ s ∈ S,
                  cwQ6DoubledZHash q.2 q.1 z =
                    2 * (s : ZMod M))).card) +
        2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
  classical
  let degree :
      (Fin (2 * (n + 1)) → Fin 3) →
        (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
    ((A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
  let W : Finset (Fin (2 * n + 2) → ZMod M) := Finset.univ
  let O : Finset (ZMod M) := Finset.univ
  let Ω : Finset ((Fin (2 * n + 2) → ZMod M) × ZMod M) := W.product O
  let P : (Fin (2 * (n + 1)) → Fin 3) →
      ((Fin (2 * n + 2) → ZMod M) × ZMod M) → Prop := fun z q =>
    H ≤ degree z q.1 ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash q.2 q.1 z = 2 * (s : ZMod M)
  have hWcard : W.card = M ^ (2 * n + 2) := by
    simp [W]
  have hperZ : ∀ z ∈ Z,
      R ^ 2 * M ^ (2 * n + 2) * S.card ≤
        R ^ 2 * (Ω.filter (fun q => P z q)).card +
          2 * B * M ^ (2 * n + 3) * S.card := by
    intro z hzZ
    have htail := mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
      hM h2 hG (A z) z
      (hz z hzZ) (hcard z hzZ) hgap
    change
      R ^ 2 * (W.filter (fun w => ¬ H ≤ degree z w)).card ≤
        2 * B * M ^ (2 * n + 3) at htail
    have hpair :
        (Ω.filter (fun q => P z q)).card =
          (W.filter (fun w => H ≤ degree z w)).card * S.card := by
      calc
        (Ω.filter (fun q => P z q)).card =
            ∑ w ∈ W, (O.filter (fun b0 => P z (w, b0))).card := by
          simpa only [Ω] using
            card_product_filter_eq_sum_gap W O (fun w b0 => P z (w, b0))
        _ = ∑ w ∈ W,
              if H ≤ degree z w then S.card else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hgood : H ≤ degree z w
          · have hoff := mme_CW_q6_z_hash_offset_label_card
                h2 S hSrange w z
            simp only [P, hgood, true_and, O] at hoff ⊢
            exact hoff
          · simp [P, hgood]
        _ = (W.filter (fun w => H ≤ degree z w)).card * S.card := by
          rw [← Finset.sum_filter]
          simp
    have hpartition :
        (W.filter (fun w => H ≤ degree z w)).card +
            (W.filter (fun w => ¬ H ≤ degree z w)).card = W.card := by
      exact W.card_filter_add_card_filter_not (fun w => H ≤ degree z w)
    have hraw :
        R ^ 2 * W.card * S.card ≤
          R ^ 2 *
              (W.filter (fun w => H ≤ degree z w)).card * S.card +
            2 * B * M ^ (2 * n + 3) * S.card := by
      calc
        R ^ 2 * W.card * S.card =
            R ^ 2 *
                ((W.filter (fun w => H ≤ degree z w)).card +
                  (W.filter (fun w => ¬ H ≤ degree z w)).card) * S.card := by
              rw [hpartition]
        _ = R ^ 2 *
                (W.filter (fun w => H ≤ degree z w)).card * S.card +
              (R ^ 2 *
                (W.filter (fun w => ¬ H ≤ degree z w)).card) * S.card := by
              ring
        _ ≤ R ^ 2 *
                (W.filter (fun w => H ≤ degree z w)).card * S.card +
              (2 * B * M ^ (2 * n + 3)) * S.card := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_right S.card htail) _
    rw [hWcard] at hraw
    rw [hpair]
    simpa [Nat.mul_assoc] using hraw
  have hdouble :
      (∑ z ∈ Z, (Ω.filter (fun q => P z q)).card) =
        ∑ q ∈ Ω, (Z.filter (fun z => P z q)).card := by
    exact mme_finset_incidence_double_count Z Ω (fun z q => P z q)
  calc
    R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card =
        ∑ _z ∈ Z, R ^ 2 * M ^ (2 * n + 2) * S.card := by
      simp [Nat.mul_comm]
    _ ≤ ∑ z ∈ Z,
        (R ^ 2 * (Ω.filter (fun q => P z q)).card +
          2 * B * M ^ (2 * n + 3) * S.card) := by
      exact Finset.sum_le_sum hperZ
    _ = R ^ 2 * (∑ z ∈ Z, (Ω.filter (fun q => P z q)).card) +
          2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      simp [Nat.mul_comm]
    _ = R ^ 2 * (∑ q ∈ Ω, (Z.filter (fun z => P z q)).card) +
          2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
      rw [hdouble]
    _ = R ^ 2 *
          (∑ q : ((Fin (2 * n + 2) → ZMod M) × ZMod M),
            (Z.filter (fun z => P z q)).card) +
          2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
      simp [Ω, W, O]
    _ = R ^ 2 *
          (∑ q : ((Fin (2 * n + 2) → ZMod M) × ZMod M),
            (Z.filter (fun z =>
              H ≤ degree z q.1 ∧
                ∃ s ∈ S,
                  cwQ6DoubledZHash q.2 q.1 z =
                    2 * (s : ZMod M))).card) +
          2 * B * M ^ (2 * n + 3) * S.card * Z.card := by
      rfl
