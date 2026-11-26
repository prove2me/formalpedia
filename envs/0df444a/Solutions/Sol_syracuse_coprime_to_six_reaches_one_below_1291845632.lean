-- Prove2me | solution 1 for syracuse_coprime_to_six_reaches_one_below_1291845632
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:59:50.207245+00:00
-- url     : https://prove2.me/submissions/30b533bc-af10-4552-a0cf-d0181b2df241

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_syracuse_coprime_to_six_reaches_one_below_1241513984
import Theorems.Thm_syracuse_descent_coprime_to_six_1241513984_to_1254096896
import Theorems.Thm_syracuse_descent_coprime_to_six_1254096896_to_1266679808
import Theorems.Thm_syracuse_descent_coprime_to_six_1266679808_to_1279262720
import Theorems.Thm_syracuse_descent_coprime_to_six_1279262720_to_1291845632

private theorem stepImage (n : ℕ) :
    0 < syracuseStep n ∧ ¬ 2 ∣ syracuseStep n ∧ ¬ 3 ∣ syracuseStep n := by
  have hn : 3*n+1 ≠ 0 := by omega
  refine ⟨Nat.ordCompl_pos 2 hn, Nat.not_dvd_ordCompl Nat.prime_two hn, ?_⟩
  intro hd
  have h3 := dvd_trans hd (Nat.ordCompl_dvd (3*n+1) 2)
  omega

private theorem addedDescent (n : ℕ) (hl : 1241513984 ≤ n) (hu : n < 1291845632)
    (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases h : n < 1254096896
  · exact syracuse_descent_coprime_to_six_1241513984_to_1254096896 n (by omega) h ho h3
  by_cases h : n < 1266679808
  · exact syracuse_descent_coprime_to_six_1254096896_to_1266679808 n (by omega) h ho h3
  by_cases h : n < 1279262720
  · exact syracuse_descent_coprime_to_six_1266679808_to_1279262720 n (by omega) h ho h3
  exact syracuse_descent_coprime_to_six_1279262720_to_1291845632 n (by omega) hu ho h3

set_option maxHeartbeats 0 in
theorem solution (n : ℕ) (hn : 0 < n) (hlt : n < 1291845632)
    (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : ∃ t : ℕ, syracuseStep^[t] n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    by_cases hs : n < 1241513984
    · exact syracuse_coprime_to_six_reaches_one_below_1241513984 n hn hs ho h3
    obtain ⟨t, ht⟩ := addedDescent n (by omega) hlt ho h3
    cases t with
    | zero => exact False.elim ((Nat.lt_irrefl n) ht)
    | succ t =>
      have hstep := stepImage (syracuseStep^[t] n)
      rw [← Function.iterate_succ_apply' syracuseStep] at hstep
      obtain ⟨j, hj⟩ := ih _ ht hstep.1 (ht.trans hlt) hstep.2.1 hstep.2.2
      exact ⟨j + (t + 1), by rwa [Function.iterate_add_apply]⟩
