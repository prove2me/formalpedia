-- Prove2me | solution 1 for mme_stothers_phi233_rounded_completion_ratio_subexponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:58:44.657459+00:00
-- url     : https://prove2.me/submissions/0d72e5ed-8246-422a-ad8a-26acb3c0af4d

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_stationary_marginal_address_entropy_upper
import Theorems.Thm_mme_stothers_phi233_uniform_entropy_stability

open MME Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option warningAsError true

/-- Along any sequence of integral profiles converging to a positive
stationary `phi_233` profile, a compatible stationary completion profile
makes the ambient family larger than the exact family by only the explicit
polynomial factors and an arbitrarily small exponential loss. -/
theorem solution
    (N A B C D : ℕ → ℕ) (X Y Z W : ℕ → ℝ)
    (a b c d : ℝ)
    (hN : ∀ n, 0 < N n)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = N n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (N n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (N n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (N n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (N n : ℝ)) atTop (nhds d))
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hZ : ∀ n, 0 < Z n) (hW : ∀ n, 0 < W n)
    (htotalX : ∀ n, 2 * X n + Y n + Z n + W n = 1)
    (hsigmaX : ∀ n,
      2 * X n + Y n =
        2 * ((A n : ℝ) / (N n : ℝ)) + (B n : ℝ) / (N n : ℝ))
    (hmuX : ∀ n,
      X n + Z n = (A n : ℝ) / (N n : ℝ) + (C n : ℝ) / (N n : ℝ))
    (hsigmaUpper : ∀ n,
      2 * ((A n : ℝ) / (N n : ℝ)) + (B n : ℝ) / (N n : ℝ) < 2 / 3)
    (hmuUpper : ∀ n,
      (A n : ℝ) / (N n : ℝ) + (C n : ℝ) / (N n : ℝ) < 1 / 2)
    (hcritical : ∀ n,
      (X n) ^ (2 : ℕ) * W n = (Y n) ^ (2 : ℕ) * Z n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (Nat.card
            (MME.StothersFourth.Phi233.MarginalAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) ≤
          (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
            Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
            (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
            (Nat.card
              (MME.StothersFourth.Phi233.ExactProfileAddress
                (N n) (A n) (B n) (C n) (D n)) : ℝ) := by
  let Ar : ℕ → ℝ := fun n ↦ (A n : ℝ) / (N n : ℝ)
  let Br : ℕ → ℝ := fun n ↦ (B n : ℝ) / (N n : ℝ)
  let Cr : ℕ → ℝ := fun n ↦ (C n : ℝ) / (N n : ℝ)
  let Dr : ℕ → ℝ := fun n ↦ (D n : ℝ) / (N n : ℝ)
  have hUniform := mme_stothers_phi233_uniform_entropy_stability
    a b c d Ar Br Cr Dr X Y Z W ha hb hc hd htotal hstation
    (by simpa only [Ar] using hA)
    (by simpa only [Br] using hB)
    (by simpa only [Cr] using hC)
    (by simpa only [Dr] using hD)
    (fun n ↦ (hX n).le) (fun n ↦ (hY n).le)
    (fun n ↦ (hZ n).le) (fun n ↦ (hW n).le) htotalX
    (by simpa only [Ar, Br] using hsigmaX)
    (by simpa only [Ar, Cr] using hmuX)
  intro ε hε
  filter_upwards [hUniform ε hε] with n hentropy
  have hNR : (N n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hN n))
  have hsigmaCast :
      (((2 * A n + B n : ℕ) : ℝ) / (N n : ℝ)) =
        2 * Ar n + Br n := by
    dsimp only [Ar, Br]
    push_cast
    ring
  have hmuCast :
      (((A n + C n : ℕ) : ℝ) / (N n : ℝ)) =
        Ar n + Cr n := by
    dsimp only [Ar, Cr]
    push_cast
    ring
  have hsigma0 : 0 < 2 * Ar n + Br n := by
    rw [← hsigmaX n]
    linarith [hX n, hY n]
  have hmu0 : 0 < Ar n + Cr n := by
    rw [← hmuX n]
    linarith [hX n, hZ n]
  have hstationX :=
    mme_stothers_phi233_log_stationarity_of_critical_product
      (X n) (Y n) (Z n) (W n) (hX n) (hY n) (hZ n) (hW n)
      (hcritical n)
  have hAmbient :=
    mme_stothers_phi233_stationary_marginal_address_entropy_upper
      (N n) (A n) (B n) (C n) (D n) (hN n)
      (2 * Ar n + Br n) (Ar n + Cr n)
      (X n) (Y n) (Z n) (W n)
      hsigma0 (by simpa only [Ar, Br] using hsigmaUpper n)
      hmu0 (by simpa only [Ar, Cr] using hmuUpper n)
      hsigmaCast hmuCast (hX n) (hY n) (hZ n) (hW n)
      (htotalX n) (by simpa only [Ar, Br] using hsigmaX n)
      (by simpa only [Ar, Cr] using hmuX n) hstationX
  have hExact :=
    mme_stothers_phi233_exact_profile_entropy_polynomial_lower
      (N n) (A n) (B n) (C n) (D n) (hN n) (hsum n)
  let targetEntropy : ℝ :=
    4 * Real.negMulLog (Ar n / 2) +
      2 * Real.negMulLog (Br n / 2) +
      2 * Real.negMulLog (Cr n / 2) +
      2 * Real.negMulLog (Dr n / 2)
  let exactEntropy : ℝ :=
    4 * Real.negMulLog ((A n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((B n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((C n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((D n : ℝ) / ((2 * N n : ℕ) : ℝ))
  have hAhalf : Ar n / 2 =
      (A n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Ar]
    push_cast
    ring
  have hBhalf : Br n / 2 =
      (B n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Br]
    push_cast
    ring
  have hChalf : Cr n / 2 =
      (C n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Cr]
    push_cast
    ring
  have hDhalf : Dr n / 2 =
      (D n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Dr]
    push_cast
    ring
  have hEntropyEq : targetEntropy = exactEntropy := by
    simp only [targetEntropy, exactEntropy, hAhalf, hBhalf, hChalf, hDhalf]
  have hentropy' :
      4 * Real.negMulLog (X n / 2) +
            2 * Real.negMulLog (Y n / 2) +
            2 * Real.negMulLog (Z n / 2) +
            2 * Real.negMulLog (W n / 2) ≤
        targetEntropy + ε := by
    simpa only [targetEntropy, Ar, Br, Cr, Dr] using hentropy
  have hexpMono :
      Real.exp (((2 * N n : ℕ) : ℝ) *
          (4 * Real.negMulLog (X n / 2) +
            2 * Real.negMulLog (Y n / 2) +
            2 * Real.negMulLog (Z n / 2) +
            2 * Real.negMulLog (W n / 2))) ≤
        Real.exp (((2 * N n : ℕ) : ℝ) * (targetEntropy + ε)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hentropy' (by positivity)
  have hExact' :
      Real.exp (((2 * N n : ℕ) : ℝ) * exactEntropy) ≤
        (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) := by
    simpa only [exactEntropy] using hExact
  calc
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          (N n) (A n) (B n) (C n) (D n)) : ℝ) ≤
        (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) *
            (4 * Real.negMulLog (X n / 2) +
              2 * Real.negMulLog (Y n / 2) +
              2 * Real.negMulLog (Z n / 2) +
              2 * Real.negMulLog (W n / 2))) := hAmbient
    _ ≤ (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * (targetEntropy + ε)) :=
      mul_le_mul_of_nonneg_left hexpMono (by positivity)
    _ = (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          Real.exp (((2 * N n : ℕ) : ℝ) * exactEntropy) := by
      rw [← hEntropyEq]
      rw [mul_add, Real.exp_add]
      ring
    _ ≤ (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          ((6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
            (Nat.card
              (MME.StothersFourth.Phi233.ExactProfileAddress
                (N n) (A n) (B n) (C n) (D n)) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hExact' (by positivity)
    _ = (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) := by ring
