-- Prove2me | solution 1 for revenue_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:35:39.302988+00:00
-- url     : https://prove2.me/submissions/28ccc2ac-3fb8-47c4-bcea-a88fe3924b16

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (f p x : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ j, 1 ≤ j → 0 ≤ p j) (hx : ∀ j, 0 ≤ x j) :
    ∀ n s, 0 ≤ s → (∀ j, 1 ≤ j → j ≤ n → |f j| ≤ M) →
      |revenue f p x n s| ≤ (n : ℝ) * M * s := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro s hs hfare
      simp [revenue]
  | one =>
      intro s hs hfare
      simp only [revenue]
      by_cases h : s < x 1
      · simp only [if_pos h, abs_mul, abs_of_nonneg hs]
        have hf := hfare 1 (by omega) (by omega)
        simpa using (mul_le_mul_of_nonneg_right hf hs)
      · have hx1 : x 1 ≤ s := le_of_not_gt h
        simp only [if_neg h, abs_mul, abs_of_nonneg (hx 1)]
        have hf := hfare 1 (by omega) (by omega)
        have hmul : |f 1| * x 1 ≤ M * s := by
          calc
            |f 1| * x 1 ≤ M * x 1 := mul_le_mul_of_nonneg_right hf (hx 1)
            _ ≤ M * s := mul_le_mul_of_nonneg_left hx1 hM
        simpa using hmul
  | more n ih0 ih1 =>
      intro s hs hfare
      simp only [revenue]
      by_cases h1 : s < p (n + 1)
      · simp only [if_pos h1]
        have hrec := ih1 s hs (by
          intro j hj1 hjn
          exact hfare j hj1 (by omega))
        calc
          |revenue f p x (n + 1) s| ≤ ((n + 1 : ℕ) : ℝ) * M * s := hrec
          _ ≤ ((n + 2 : ℕ) : ℝ) * M * s := by
            have hNat : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
              exact_mod_cast (Nat.le_succ (n + 1))
            calc
              ((n + 1 : ℕ) : ℝ) * M * s =
                  ((n + 1 : ℕ) : ℝ) * (M * s) := by ring
              _ ≤ ((n + 2 : ℕ) : ℝ) * (M * s) :=
                mul_le_mul_of_nonneg_right hNat (mul_nonneg hM hs)
              _ = ((n + 2 : ℕ) : ℝ) * M * s := by ring
      · have hp0 : 0 ≤ p (n + 1) := hp (n + 1) (by omega)
        have hps : p (n + 1) ≤ s := le_of_not_gt h1
        by_cases h2 : s < p (n + 1) + x (n + 2)
        · simp only [if_neg h1, if_pos h2]
          have hA : 0 ≤ s - p (n + 1) := sub_nonneg.mpr hps
          have hAs : s - p (n + 1) ≤ s := by linarith
          have hrec := ih1 (p (n + 1)) hp0 (by
            intro j hj1 hjn
            exact hfare j hj1 (by omega))
          have hf := hfare (n + 2) (by omega) (by omega)
          have hterm : |(s - p (n + 1)) * f (n + 2)| =
              (s - p (n + 1)) * |f (n + 2)| := by
            rw [abs_mul, abs_of_nonneg hA]
          have hterm' : (s - p (n + 1)) * |f (n + 2)| ≤
              M * (s - p (n + 1)) := by
            calc
              (s - p (n + 1)) * |f (n + 2)| =
                  |f (n + 2)| * (s - p (n + 1)) := by ring
              _ ≤ M * (s - p (n + 1)) := mul_le_mul_of_nonneg_right hf hA
          have hbase : M * (s - p (n + 1)) ≤ M * s :=
            mul_le_mul_of_nonneg_left hAs hM
          have hcoef : 0 ≤ ((n + 1 : ℕ) : ℝ) * M :=
            mul_nonneg (by positivity) hM
          have hrec' : ((n + 1 : ℕ) : ℝ) * M * p (n + 1) ≤
              ((n + 1 : ℕ) : ℝ) * M * s :=
            mul_le_mul_of_nonneg_left hps hcoef
          calc
            |(s - p (n + 1)) * f (n + 2) +
                revenue f p x (n + 1) (p (n + 1))| ≤
                |(s - p (n + 1)) * f (n + 2)| +
                  |revenue f p x (n + 1) (p (n + 1))| := abs_add_le _ _
            _ ≤ M * (s - p (n + 1)) +
                  ((n + 1 : ℕ) : ℝ) * M * p (n + 1) := by
                rw [hterm]
                exact add_le_add hterm' hrec
            _ ≤ M * s + ((n + 1 : ℕ) : ℝ) * M * s :=
                add_le_add hbase hrec'
            _ = ((n + 2 : ℕ) : ℝ) * M * s := by push_cast; ring
        · simp only [if_neg h1, if_neg h2]
          have hdemand_nonneg : 0 ≤ x (n + 2) := hx (n + 2)
          have hpx : p (n + 1) + x (n + 2) ≤ s := le_of_not_gt h2
          have hxs : x (n + 2) ≤ s := by linarith
          have hrs : 0 ≤ s - x (n + 2) := sub_nonneg.mpr hxs
          have hrle : s - x (n + 2) ≤ s := by linarith
          have hrec := ih1 (s - x (n + 2)) hrs (by
            intro j hj1 hjn
            exact hfare j hj1 (by omega))
          have hf := hfare (n + 2) (by omega) (by omega)
          have hterm : |x (n + 2) * f (n + 2)| =
              x (n + 2) * |f (n + 2)| := by
            rw [abs_mul, abs_of_nonneg hdemand_nonneg]
          have hterm' : x (n + 2) * |f (n + 2)| ≤ M * s := by
            calc
              x (n + 2) * |f (n + 2)| ≤ M * x (n + 2) := by
                calc
                  x (n + 2) * |f (n + 2)| =
                      |f (n + 2)| * x (n + 2) := by ring
                  _ ≤ M * x (n + 2) :=
                    mul_le_mul_of_nonneg_right hf hdemand_nonneg
              _ ≤ M * s := mul_le_mul_of_nonneg_left hxs hM
          have hcoef : 0 ≤ ((n + 1 : ℕ) : ℝ) * M :=
            mul_nonneg (by positivity) hM
          have hrec' : ((n + 1 : ℕ) : ℝ) * M * (s - x (n + 2)) ≤
              ((n + 1 : ℕ) : ℝ) * M * s :=
            mul_le_mul_of_nonneg_left hrle hcoef
          calc
            |x (n + 2) * f (n + 2) +
                revenue f p x (n + 1) (s - x (n + 2))| ≤
                |x (n + 2) * f (n + 2)| +
                  |revenue f p x (n + 1) (s - x (n + 2))| := abs_add_le _ _
            _ ≤ M * s + ((n + 1 : ℕ) : ℝ) * M * (s - x (n + 2)) := by
                rw [hterm]
                exact add_le_add hterm' hrec
            _ ≤ M * s + ((n + 1 : ℕ) : ℝ) * M * s :=
                add_le_add le_rfl hrec'
            _ = ((n + 2 : ℕ) : ℝ) * M * s := by push_cast; ring
