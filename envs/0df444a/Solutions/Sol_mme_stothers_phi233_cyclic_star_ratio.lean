-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_star_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:08:59.883002+00:00
-- url     : https://prove2.me/submissions/dcf4ce71-6388-4e31-a131-76684e591d54

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_address_star_ratio

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- The three one-mode completion ratios multiply to the cubic cyclic degree
ratio required by the cyclic type-2 extraction. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (R : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    ((∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l}) : ℝ) ≤
      R ^ 3 *
        ((∏ l : Fin 3,
          Nat.card
            {b : MME.StothersFourth.Phi233.ExactProfileAddress
                N alpha beta gamma delta // b.1.1 l = a.1.1 l}) : ℝ) := by
  let A : Fin 3 → ℕ := fun l ↦ Nat.card
    {b : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta // b.1 l = a.1.1 l}
  let T : Fin 3 → ℕ := fun l ↦ Nat.card
    {b : MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta // b.1.1 l = a.1.1 l}
  have h0 : (A 0 : ℝ) ≤ R * (T 0 : ℝ) := by
    simpa only [A, T] using
      (mme_stothers_phi233_address_star_ratio
        N alpha beta gamma delta hsum a 0 R hratio)
  have h1 : (A 1 : ℝ) ≤ R * (T 1 : ℝ) := by
    simpa only [A, T] using
      (mme_stothers_phi233_address_star_ratio
        N alpha beta gamma delta hsum a 1 R hratio)
  have h2 : (A 2 : ℝ) ≤ R * (T 2 : ℝ) := by
    simpa only [A, T] using
      (mme_stothers_phi233_address_star_ratio
        N alpha beta gamma delta hsum a 2 R hratio)
  have hA0 : (0 : ℝ) ≤ A 0 := Nat.cast_nonneg _
  have hA1 : (0 : ℝ) ≤ A 1 := Nat.cast_nonneg _
  have hA2 : (0 : ℝ) ≤ A 2 := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ T 0 := Nat.cast_nonneg _
  have hT1 : (0 : ℝ) ≤ T 1 := Nat.cast_nonneg _
  have hT2 : (0 : ℝ) ≤ T 2 := Nat.cast_nonneg _
  have hprod :
      (A 0 : ℝ) * A 1 * A 2 ≤
        (R * T 0) * (R * T 1) * (R * T 2) := by
    gcongr
  calc
    ((∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l}) : ℝ) =
        (A 0 : ℝ) * A 1 * A 2 := by
      simp [A, Fin.prod_univ_succ]
      ring
    _ ≤ (R * T 0) * (R * T 1) * (R * T 2) := hprod
    _ = R ^ 3 * ((T 0 * T 1 * T 2 : ℕ) : ℝ) := by
      push_cast
      ring
    _ = R ^ 3 *
        ((∏ l : Fin 3,
          Nat.card
            {b : MME.StothersFourth.Phi233.ExactProfileAddress
                N alpha beta gamma delta // b.1.1 l = a.1.1 l}) : ℝ) := by
      congr 1
      simp [T, Fin.prod_univ_succ]
      ring
