-- Prove2me | solution 1 for mme_stothers_phi233_address_star_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:02:05.532905+00:00
-- url     : https://prove2.me/submissions/5722a168-6d23-486c-bc12-a3a6c07a9e08

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_marginal_star_factorization
import Theorems.Thm_mme_stothers_phi233_exact_star_factorization

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option warningAsError true

/-- A global same-marginal/exact-profile cardinality ratio transfers without
loss to every fixed-word star in every mode. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) (R : ℝ)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    (Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 i = a.1.1 i} : ℝ) ≤
      R *
        (Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 i = a.1.1 i} : ℝ) := by
  classical
  let : Fintype (MME.StothersFourth.Phi233.ProfileAddress N) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 5))
  let : Fintype
      (MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) :=
    @Subtype.fintype _ _ (Classical.decPred _) inferInstance
  let : Fintype
      (MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) :=
    @Subtype.fintype _ _ (Classical.decPred _) inferInstance
  let wordCount : ℕ :=
    (2 * N).factorial /
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i s).factorial
  let ambientDegree : ℕ := Nat.card
    {b : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta // b.1 i = a.1.1 i}
  let targetDegree : ℕ := Nat.card
    {b : MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta // b.1.1 i = a.1.1 i}
  have hambient : Nat.card
      (MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) = wordCount * ambientDegree := by
    simpa only [wordCount, ambientDegree] using
      (mme_stothers_phi233_marginal_star_factorization
        N alpha beta gamma delta a.1 i)
  have htarget : Nat.card
      (MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) = wordCount * targetDegree := by
    simpa only [wordCount, targetDegree] using
      (mme_stothers_phi233_exact_star_factorization
        N alpha beta gamma delta hsum a i)
  have htargetPos : 0 < Nat.card
      (MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) := by
    let : Nonempty
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) := ⟨a⟩
    exact Nat.card_pos
  have hword : 0 < wordCount := by
    rw [htarget] at htargetPos
    exact Nat.pos_of_mul_pos_right htargetPos
  have hwordR : (0 : ℝ) < wordCount := by exact_mod_cast hword
  have hscaled :
      (wordCount : ℝ) * (ambientDegree : ℝ) ≤
        (wordCount : ℝ) * (R * (targetDegree : ℝ)) := by
    calc
      (wordCount : ℝ) * (ambientDegree : ℝ) =
          (Nat.card
            (MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta) : ℝ) := by
        exact_mod_cast hambient.symm
      _ ≤ R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ) := hratio
      _ = (wordCount : ℝ) * (R * (targetDegree : ℝ)) := by
        rw [htarget]
        push_cast
        ring
  simpa only [ambientDegree, targetDegree] using
    (mul_le_mul_iff_of_pos_left hwordR).mp hscaled
