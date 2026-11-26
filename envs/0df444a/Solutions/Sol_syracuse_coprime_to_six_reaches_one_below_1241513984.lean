-- Prove2me | solution 1 for syracuse_coprime_to_six_reaches_one_below_1241513984
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:31:16.903969+00:00
-- url     : https://prove2.me/submissions/fab178b9-2ad3-46fe-8a6c-189434fc1a06

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_syracuse_descent_7_mod12_from_2_to_8388608
import Theorems.Thm_syracuse_descent_11_mod12_from_2_to_8388608
import Theorems.Thm_syracuse_descent_7_mod12_from_8388608_to_20971520
import Theorems.Thm_syracuse_descent_11_mod12_from_8388608_to_20971520
import Theorems.Thm_syracuse_descent_coprime_to_six_combined_20971520_to_423624704
import Theorems.Thm_syracuse_descent_coprime_to_six_combined_423624704_to_826277888
import Theorems.Thm_syracuse_descent_coprime_to_six_combined_826277888_to_1241513984

private theorem bandDescent (n : ℕ) (hn : 1 < n) (hlt : n < 1241513984)
    (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hs : n < 20971520
  · by_cases hone : n % 4 = 1
    · have hd : 4 ∣ 3*n+1 := by omega
      obtain ⟨q,hq⟩ := hd
      have hq' : (3*n+1)/2/2 = q := by omega
      have hoddPart : syracuseStep n = ordCompl[2] q := by
        rw [syracuseStep,
          ← Nat.ordCompl_div_of_dvd Nat.prime_two (by omega : 2 ∣ 3*n+1),
          ← Nat.ordCompl_div_of_dvd Nat.prime_two (by omega : 2 ∣ (3*n+1)/2), hq']
      have hle : ordCompl[2] q ≤ q := Nat.div_le_self _ _
      refine ⟨1, ?_⟩
      rw [Function.iterate_one, hoddPart]
      omega
    · by_cases he : n % 12 = 7
      · by_cases hm : n < 8388608
        · exact syracuse_descent_7_mod12_from_2_to_8388608 n (by omega) hm he
        · exact syracuse_descent_7_mod12_from_8388608_to_20971520 n (by omega) hs he
      · have he' : n % 12 = 11 := by omega
        by_cases hm : n < 8388608
        · exact syracuse_descent_11_mod12_from_2_to_8388608 n (by omega) hm he'
        · exact syracuse_descent_11_mod12_from_8388608_to_20971520 n (by omega) hs he'
  · by_cases hBand1 : n < 423624704
    · exact syracuse_descent_coprime_to_six_combined_20971520_to_423624704 n (by omega) (by omega) ho h3
    · by_cases hBand2 : n < 826277888
      · exact syracuse_descent_coprime_to_six_combined_423624704_to_826277888 n (by omega) (by omega) ho h3
      · exact syracuse_descent_coprime_to_six_combined_826277888_to_1241513984 n (by omega) (by omega) ho h3

private theorem stepImage (n : ℕ) :
    0 < syracuseStep n ∧ ¬ 2 ∣ syracuseStep n ∧ ¬ 3 ∣ syracuseStep n := by
  have hn : 3*n+1 ≠ 0 := by omega
  refine ⟨Nat.ordCompl_pos 2 hn, Nat.not_dvd_ordCompl Nat.prime_two hn, ?_⟩
  intro hd
  have h3 := dvd_trans hd (Nat.ordCompl_dvd (3*n+1) 2)
  omega

set_option maxHeartbeats 0 in
theorem solution (n : ℕ) (hn : 0 < n) (hlt : n < 1241513984)
    (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : ∃ t : ℕ, syracuseStep^[t] n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    obtain ⟨t, ht⟩ := bandDescent n (by omega) hlt ho h3
    cases t with
    | zero => exact False.elim ((Nat.lt_irrefl n) ht)
    | succ t =>
      have hstep := stepImage (syracuseStep^[t] n)
      rw [← Function.iterate_succ_apply' syracuseStep] at hstep
      obtain ⟨j, hj⟩ := ih _ ht hstep.1 (ht.trans hlt) hstep.2.1 hstep.2.2
      exact ⟨j + (t + 1), by rwa [Function.iterate_add_apply]⟩
