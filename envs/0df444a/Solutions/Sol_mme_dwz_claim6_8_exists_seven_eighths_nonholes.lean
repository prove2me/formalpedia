-- Prove2me | solution 1 for mme_dwz_claim6_8_exists_seven_eighths_nonholes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:34:57.37063+00:00
-- url     : https://prove2.me/submissions/0dee5dce-2c60-4153-a040-bd59f99a932d

import Theorems.Thm_mme_finset_incidence_double_count
import Theorems.Thm_mme_finite_collision_budget_averaging

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Weight Block : Type}
    [Fintype Weight] [DecidableEq Weight] [Nonempty Weight]
    [Fintype Block] [DecidableEq Block]
    (bad : Block → Weight → Prop) [DecidableRel bad]
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (bad z)).card ≤ Fintype.card Weight) :
    ∃ w : Weight,
      7 * Fintype.card Block ≤
        8 * (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card := by
  classical
  let badCount : Weight → ℕ := fun w ↦
    (Finset.univ.filter (fun z : Block ↦ bad z w)).card
  have hdouble :
      ∑ w : Weight, badCount w =
        ∑ z : Block, (Finset.univ.filter (bad z)).card := by
    simpa only [badCount] using
      (mme_finset_incidence_double_count
        (Finset.univ : Finset Weight) (Finset.univ : Finset Block)
        (fun w z ↦ bad z w))
  have hbudget :
      Fintype.card Weight * 0 + ∑ w : Weight, 8 * badCount w ≤
        ∑ _w : Weight, Fintype.card Block := by
    simp only [Nat.mul_zero, zero_add]
    calc
      ∑ w : Weight, 8 * badCount w =
          8 * ∑ w : Weight, badCount w := by
            rw [Finset.mul_sum]
      _ = 8 * ∑ z : Block,
          (Finset.univ.filter (bad z)).card := by rw [hdouble]
      _ = ∑ z : Block,
          8 * (Finset.univ.filter (bad z)).card := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _z : Block, Fintype.card Weight := by
            exact Finset.sum_le_sum fun z _ ↦ hpointwise z
      _ = ∑ _w : Weight, Fintype.card Block := by
            simp [Nat.mul_comm]
  obtain ⟨w, hw⟩ := mme_finite_collision_budget_averaging (Ω := Weight)
    (fun _ : Weight ↦ Fintype.card Block)
    (fun w ↦ 8 * badCount w) 0 hbudget
  refine ⟨w, ?_⟩
  have hbad : 8 * badCount w ≤ Fintype.card Block := by
    simpa using hw
  have hpartition :
      badCount w +
          (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card =
        Fintype.card Block := by
    simpa only [badCount, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Block))
        (p := fun z : Block ↦ bad z w))
  omega
