-- Prove2me | solution 1 for weightedLogMassReal_odd_recip_le_three
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-12T22:44:42.895095+00:00
-- url     : https://prove2.me/submissions/22f948c0-74cd-4f58-b529-cdea74f57fa1

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_weightedLogMassReal

open scoped BigOperators
open Classical

/-- Reciprocal-sum bound: `∑_{k=1}^{N} 1/k ≤ 1 + log N`, written over
`Finset.range (N+1)` with the `k = 0` term set to `0`. -/
private lemma recip_sum_le (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), if k = 0 then (0 : ℝ) else 1 / (k : ℝ))
      ≤ 1 + Real.log (N : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => norm_num [Finset.sum_range_succ]
    | succ m =>
      have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      have step : (1 : ℝ) / ((m + 2 : ℕ) : ℝ)
          ≤ Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        have h := Real.one_sub_inv_le_log_of_pos
          (show (0 : ℝ) < ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) by positivity)
        rw [Real.log_div (by positivity : (((m + 2 : ℕ) : ℝ)) ≠ 0)
          (by positivity : (((m + 1 : ℕ) : ℝ)) ≠ 0)] at h
        have hcast : (1 : ℝ) - (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))⁻¹
            = 1 / ((m + 2 : ℕ) : ℝ) := by
          field_simp
          push_cast
          ring_nf
        rw [hcast] at h
        exact h
      rw [Finset.sum_range_succ]
      have hterm : (if m + 1 + 1 = 0 then (0 : ℝ) else 1 / ((m + 1 + 1 : ℕ) : ℝ))
          = 1 / ((m + 2 : ℕ) : ℝ) := by
        rw [if_neg (by omega)]
      rw [hterm]
      have ih' : (∑ k ∈ Finset.range (m + 1 + 1), if k = 0 then (0 : ℝ) else 1 / (k : ℝ))
          ≤ 1 + Real.log ((m + 1 : ℕ) : ℝ) := by
        have := ih
        norm_num at this ⊢
        exact this
      have hlogcast : Real.log ((m + 1 + 1 : ℕ) : ℝ) = Real.log ((m + 2 : ℕ) : ℝ) := by
        congr 1
      rw [hlogcast]
      linarith

theorem solution (E : ℕ → Prop) (x : ℝ) (hx : 2 ≤ x) :
    weightedLogMassReal (fun n => 0 < n ∧ Odd n) E (fun n => 1 / (n : ℝ)) x ≤ 3 := by
  unfold weightedLogMassReal
  simp only []
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hN : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hpoint : ∀ k : ℕ,
      (if (0 < k ∧ Odd k) ∧ E k then (1 : ℝ) / (k : ℝ) else 0)
        ≤ (if k = 0 then (0 : ℝ) else 1 / (k : ℝ)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [if_neg hk]
      split_ifs with h
      · exact le_rfl
      · positivity
  have hsum : (∑ k ∈ Finset.range (⌊x⌋₊ + 1),
        if (0 < k ∧ Odd k) ∧ E k then (1 : ℝ) / (k : ℝ) else 0)
      ≤ 1 + Real.log x := by
    calc (∑ k ∈ Finset.range (⌊x⌋₊ + 1),
          if (0 < k ∧ Odd k) ∧ E k then (1 : ℝ) / (k : ℝ) else 0)
        ≤ ∑ k ∈ Finset.range (⌊x⌋₊ + 1), (if k = 0 then (0 : ℝ) else 1 / (k : ℝ)) :=
          Finset.sum_le_sum (fun k _ => hpoint k)
      _ ≤ 1 + Real.log (⌊x⌋₊ : ℝ) := recip_sum_le ⌊x⌋₊
      _ ≤ 1 + Real.log x := by
          have hfx : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by
            have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
            positivity
          linarith [Real.log_le_log hfx hN]
  rw [div_le_iff₀ hlogx]
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  nlinarith [hsum, h2, Real.log_two_gt_d9]
