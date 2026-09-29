-- Prove2me | solution 1 for mme_CW_2376_prime_hash_collision_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:33:43.5153+00:00
-- url     : https://prove2.me/submissions/257fa260-799d-44bb-85ac-dad2e6350674

import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-- The numerical margin used by the outer CW affine hash.  A full compatible
completion degree within a polynomial factor of the target degree is absorbed
by the large square-root exponential reserve. -/
theorem solution
    (N D Dstar p S : ℕ)
    (hD1 : 1 ≤ D)
    (hDdom : D ≤ (N + 1) ^ 15 * Dstar)
    (hS : (6 * D : ℝ) ≤ (S : ℝ))
    (hp : (p : ℝ) ≤ (D : ℝ) *
      Real.exp (2000 * Real.sqrt (((N + 1 : ℕ) : ℝ)))) :
    (p : ℝ) ^ 2 *
          Real.exp (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) +
        3 * (Dstar : ℝ) * (D : ℝ) ≤
      (Dstar : ℝ) * (S : ℝ) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hrexp : r ≤ Real.exp r := by
    calc
      r ≤ r + 1 := by linarith
      _ ≤ Real.exp r := by
        simpa [add_comm] using Real.add_one_le_exp r
  have hpoly : ((((N + 1) ^ 15 : ℕ) : ℝ)) ≤ Real.exp (30 * r) := by
    have hr2' : r ^ 2 = (N : ℝ) + 1 := by
      simpa using hr2
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← hr2', ← pow_mul]
    norm_num
    calc
      r ^ 30 ≤ (Real.exp r) ^ 30 := by gcongr
      _ = Real.exp (30 * r) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hdecay :
      ((((N + 1) ^ 15 : ℕ) : ℝ)) * Real.exp (-96000 * r) ≤ 1 := by
    calc
      ((((N + 1) ^ 15 : ℕ) : ℝ)) * Real.exp (-96000 * r)
          ≤ Real.exp (30 * r) * Real.exp (-96000 * r) := by
            gcongr
      _ = Real.exp (-95970 * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith
  have hDdomR :
      (D : ℝ) ≤ ((((N + 1) ^ 15 : ℕ) : ℝ)) * (Dstar : ℝ) := by
    exact_mod_cast hDdom
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hD0 : 0 ≤ (D : ℝ) := by positivity
  have hE0 : 0 ≤ Real.exp (2000 * r) := (Real.exp_pos _).le
  have hfirst :
      (p : ℝ) ^ 2 * Real.exp (-100000 * r) ≤
        3 * (Dstar : ℝ) * (D : ℝ) := by
    calc
      (p : ℝ) ^ 2 * Real.exp (-100000 * r)
          ≤ ((D : ℝ) * Real.exp (2000 * r)) ^ 2 *
              Real.exp (-100000 * r) := by gcongr
      _ = (D : ℝ) ^ 2 * Real.exp (-96000 * r) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ ((D : ℝ) *
              ((((N + 1) ^ 15 : ℕ) : ℝ)) * (Dstar : ℝ)) *
            Real.exp (-96000 * r) := by
        have hmul := mul_le_mul_of_nonneg_left hDdomR hD0
        have hsquare :
            (D : ℝ) ^ 2 ≤
              (D : ℝ) *
                (((((N + 1) ^ 15 : ℕ) : ℝ)) * (Dstar : ℝ)) := by
          simpa [pow_two] using hmul
        exact mul_le_mul_of_nonneg_right
          (by simpa [mul_assoc] using hsquare) (Real.exp_pos _).le
      _ = ((D : ℝ) * (Dstar : ℝ)) *
            (((((N + 1) ^ 15 : ℕ) : ℝ)) *
              Real.exp (-96000 * r)) := by ring
      _ ≤ ((D : ℝ) * (Dstar : ℝ)) * 1 := by
        gcongr
      _ ≤ 3 * (Dstar : ℝ) * (D : ℝ) := by
        nlinarith
  have hmargin :
      3 * (Dstar : ℝ) * (D : ℝ) +
          3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S : ℝ) := by
    have hDstar0 : 0 ≤ (Dstar : ℝ) := by positivity
    nlinarith
  dsimp [r] at hfirst ⊢
  exact (add_le_add hfirst (le_refl _)).trans hmargin
