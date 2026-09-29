-- Prove2me | solution 1 for mme_dwz_two_branch_common_prime_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:36:16.052588+00:00
-- url     : https://prove2.me/submissions/9532065b-4c57-48bf-8b59-131a357ca8d2

import Mathlib

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (A Z T d p : ℕ) (R Pa Pd Pz Pr xA xZ xd xp : ℝ)
    (hfactor : A = Z * T)
    (hdpos : 0 < d)
    (_hPa : 0 < Pa) (hPd : 0 < Pd) (_hPz : 0 < Pz) (hPr : 0 < Pr)
    (hA : Real.exp xA ≤ Pa * (A : ℝ))
    (hZ : Real.exp xZ ≤ Pz * (Z : ℝ))
    (hd : (d : ℝ) ≤ Pd * Real.exp xd)
    (hR : R = Pr * (T : ℝ) * Real.exp xp)
    (hp : (p : ℝ) ≤ 16 * max (d : ℝ) R) :
    (p : ℝ) * Real.exp (min (xA - xd) (xZ - xp)) ≤
      16 * max (Pa * Pd) (Pz * Pr) * (A : ℝ) := by
  let e : ℝ := Real.exp (min (xA - xd) (xZ - xp))
  let Q : ℝ := max (Pa * Pd) (Pz * Pr)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have heA : e ≤ Real.exp (xA - xd) := by
    dsimp only [e]
    exact Real.exp_le_exp.mpr (min_le_left _ _)
  have heZ : e ≤ Real.exp (xZ - xp) := by
    dsimp only [e]
    exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hQAP : Pa * Pd ≤ Q := le_max_left _ _
  have hQZP : Pz * Pr ≤ Q := le_max_right _ _
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hTnonneg : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hZnonneg : (0 : ℝ) ≤ (Z : ℝ) := by positivity
  have hAcast : (A : ℝ) = (Z : ℝ) * (T : ℝ) := by
    exact_mod_cast hfactor
  have hbranchA : e * (d : ℝ) ≤ Q * (A : ℝ) := by
    calc
      e * (d : ℝ) ≤ Real.exp (xA - xd) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right heA hdnonneg
      _ ≤ Real.exp (xA - xd) * (Pd * Real.exp xd) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      _ = Pd * Real.exp xA := by
        rw [show Real.exp (xA - xd) * (Pd * Real.exp xd) =
          Pd * (Real.exp (xA - xd) * Real.exp xd) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ Pd * (Pa * (A : ℝ)) :=
        mul_le_mul_of_nonneg_left hA hPd.le
      _ = (Pa * Pd) * (A : ℝ) := by ring
      _ ≤ Q * (A : ℝ) :=
        mul_le_mul_of_nonneg_right hQAP (by positivity)
  have hbranchZ : e * R ≤ Q * (A : ℝ) := by
    rw [hR]
    calc
      e * (Pr * (T : ℝ) * Real.exp xp) ≤
          Real.exp (xZ - xp) * (Pr * (T : ℝ) * Real.exp xp) :=
        mul_le_mul_of_nonneg_right heZ (by positivity)
      _ = Pr * (T : ℝ) * Real.exp xZ := by
        rw [show Real.exp (xZ - xp) * (Pr * (T : ℝ) * Real.exp xp) =
          Pr * (T : ℝ) * (Real.exp (xZ - xp) * Real.exp xp) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ Pr * (T : ℝ) * (Pz * (Z : ℝ)) :=
        mul_le_mul_of_nonneg_left hZ (mul_nonneg hPr.le hTnonneg)
      _ = (Pz * Pr) * (A : ℝ) := by rw [hAcast]; ring
      _ ≤ Q * (A : ℝ) :=
        mul_le_mul_of_nonneg_right hQZP (by positivity)
  have hmax : e * max (d : ℝ) R ≤ Q * (A : ℝ) := by
    rcases le_total (d : ℝ) R with hdr | hrd
    · rw [max_eq_right hdr]
      exact hbranchZ
    · rw [max_eq_left hrd]
      exact hbranchA
  calc
    (p : ℝ) * e ≤ (16 * max (d : ℝ) R) * e :=
      mul_le_mul_of_nonneg_right hp he
    _ = 16 * (e * max (d : ℝ) R) := by ring
    _ ≤ 16 * (Q * (A : ℝ)) := by gcongr
    _ = 16 * Q * (A : ℝ) := by ring
