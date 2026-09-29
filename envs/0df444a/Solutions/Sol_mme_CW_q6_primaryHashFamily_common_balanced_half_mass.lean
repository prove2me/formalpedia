-- Prove2me | solution 1 for mme_CW_q6_primaryHashFamily_common_balanced_half_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:40:13.426832+00:00
-- url     : https://prove2.me/submissions/14a95581-bbe6-471f-9b95-de6263cd8fff

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_many_central_balanced_halves
import Theorems.Thm_mme_CW_q6_central_four_cell_choice_polynomial_capacity
import Theorems.Thm_mme_finset_common_witness_of_uniform_many

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- Double counting selects one coordinate half that balances a polynomial
fraction of all entries of a primary q=6 hash family. -/
theorem solution
    {n L G A H : ℕ} (hLG : L + G = 2 * n)
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H) :
    ∃ S : Finset (Fin (2 * (2 * n))),
      ∃ P : Finset (Fin A × Fin H),
        S.card = 2 * n ∧
        (∀ p ∈ P,
          (∀ grade : Fin 3,
            (S.filter (fun j ↦ (family.entry p).1 0 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) ∧
          (∀ grade : Fin 3,
            ((Finset.univ \ S).filter
              (fun j ↦ (family.entry p).1 1 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0)) ∧
        A * H ≤ (2 * n + 1) ^ 4 * P.card := by
  classical
  let B :=
    (Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
      (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2))
  let E : Finset (Fin A × Fin H) := Finset.univ
  let U : Finset (Finset (Fin (2 * (2 * n)))) :=
    Finset.univ.powersetCard (2 * n)
  let W : (Fin A × Fin H) → Finset (Finset (Fin (2 * (2 * n)))) :=
    fun p ↦ Classical.choose
      (mme_CW_q6_exact_address_many_central_balanced_halves
        hLG (family.entry p))
  have hWspec (p : Fin A × Fin H) :
      (W p).card = B ∧
        ∀ S ∈ W p,
          S.card = 2 * n ∧
            (∀ grade : Fin 3,
              (S.filter
                (fun j ↦ (family.entry p).1 0 j = grade)).card =
                if grade = 0 then n else if grade = 1 then n else 0) ∧
            (∀ grade : Fin 3,
              ((Finset.univ \ S).filter
                (fun j ↦ (family.entry p).1 1 j = grade)).card =
                if grade = 0 then n else if grade = 1 then n else 0) := by
    exact Classical.choose_spec
      (mme_CW_q6_exact_address_many_central_balanced_halves
        hLG (family.entry p))
  have hWU : ∀ p ∈ E, W p ⊆ U := by
    intro p _ S hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, (hWspec p).2 S hS |>.1⟩
  have hWB : ∀ p ∈ E, B ≤ (W p).card := by
    intro p _
    exact (hWspec p).1.ge
  have hUne : U.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨S, hSU, hincidence⟩ :=
    mme_finset_common_witness_of_uniform_many E U W B hWU hWB hUne
  let P : Finset (Fin A × Fin H) := E.filter (fun p ↦ S ∈ W p)
  refine ⟨S, P, ?_, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp hSU).2
  · intro p hp
    have hpW : S ∈ W p := (Finset.mem_filter.mp hp).2
    exact (hWspec p).2 S hpW |>.2
  · have hEcard : E.card = A * H := by
      simp [E]
    have hUcard : U.card = Nat.choose (2 * (2 * n)) (2 * n) := by
      simp [U, Finset.card_powersetCard]
    have hcap : U.card ≤ (2 * n + 1) ^ 4 * B := by
      rw [hUcard]
      exact mme_CW_q6_central_four_cell_choice_polynomial_capacity hLG
    have hincidence' : A * H * B ≤ U.card * P.card := by
      simpa only [hEcard, P] using hincidence
    have hBpos : 0 < B := by
      have hLpos : 0 < Nat.choose L (L / 2) :=
        Nat.choose_pos (Nat.div_le_self L 2)
      have hGindex : n - L / 2 ≤ G := by omega
      have hGpos : 0 < Nat.choose G (n - L / 2) :=
        Nat.choose_pos hGindex
      dsimp [B]
      positivity
    have hcancel : (A * H) * B ≤
        ((2 * n + 1) ^ 4 * P.card) * B := by
      calc
        (A * H) * B ≤ U.card * P.card := hincidence'
        _ ≤ ((2 * n + 1) ^ 4 * B) * P.card :=
          Nat.mul_le_mul_right P.card hcap
        _ = ((2 * n + 1) ^ 4 * P.card) * B := by ring
    exact Nat.le_of_mul_le_mul_right hcancel hBpos
