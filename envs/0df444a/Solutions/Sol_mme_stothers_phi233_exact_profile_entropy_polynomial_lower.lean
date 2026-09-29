-- Prove2me | solution 1 for mme_stothers_phi233_exact_profile_entropy_polynomial_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:36:43.009138+00:00
-- url     : https://prove2.me/submissions/e7fc3e74-09cc-4825-8f3a-af964662c6d9

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_card
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

/-- The exact `phi_233` profile family has its expected multinomial
entropy rate, up to the explicit degree-ten polynomial loss.  This is the
finite counting half of the exceptional constituent argument. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Real.exp
        (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((delta : ℝ) / ((2 * N : ℕ) : ℝ)))) ≤
      (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10 *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) := by
  let w : Fin 10 → ℕ :=
    MME.StothersFourth.Phi233.profileMultiplicity alpha beta gamma delta
  have htotal : (∑ r : Fin 10, w r) = 2 * N := by
    simp [w, MME.StothersFourth.Phi233.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  have hW : 0 < ∑ r : Fin 10, w r := by omega
  have hmulti :
      Nat.multinomial Finset.univ w =
        Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) := by
    rw [mme_stothers_phi233_exact_profile_card
      N alpha beta gamma delta hsum]
    simp only [Nat.multinomial, htotal, w]
  have hlower := mme_dwz_multinomial_entropy_polynomial_lower
    w 1 (by norm_num) hW
  simp only [Nat.mul_one] at hlower
  rw [hmulti] at hlower
  have hlogNe : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hentropy :
      (((2 * N : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun r : Fin 10 ↦ (w r : ℝ) / ((2 * N : ℕ) : ℝ))) =
        ((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((delta : ℝ) / ((2 * N : ℕ) : ℝ))) := by
    simp [mme_modern_entropyBits, w,
      MME.StothersFourth.Phi233.profileMultiplicity,
      Fin.sum_univ_succ]
    field_simp [hlogNe]
    ring
  rw [htotal] at hlower
  norm_num only [one_mul, Nat.mul_one, Fintype.card_fin] at hlower
  rw [hentropy] at hlower
  simpa only using hlower
