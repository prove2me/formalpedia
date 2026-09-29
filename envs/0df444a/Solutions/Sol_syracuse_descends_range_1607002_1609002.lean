-- Prove2me | solution 1 for syracuse_descends_range_1607002_1609002
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:11:27.23259+00:00
-- url     : https://prove2.me/submissions/5880f2e8-c761-4eeb-b90f-5a0bca5896b3

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B10305589 : Blo 1607002 10305589 := bbase (se 5 (by rfl) ⟨483074, by rfl⟩ : syracuseStep 10305589 = 966149) (by norm_num)
theorem B4071485 : Blo 1607002 4071485 := bbase (se 3 (by rfl) ⟨763403, by rfl⟩ : syracuseStep 4071485 = 1526807) (by norm_num)
theorem B3432557 : Blo 1607002 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B3432565 : Blo 1607002 3432565 := bbase (se 5 (by rfl) ⟨160901, by rfl⟩ : syracuseStep 3432565 = 321803) (by norm_num)
theorem B6701173 : Blo 1607002 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B1630369 : Blo 1607002 1630369 := bbase (se 2 (by rfl) ⟨611388, by rfl⟩ : syracuseStep 1630369 = 1222777) (by norm_num)
theorem B5152949 : Blo 1607002 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B1859809 : Blo 1607002 1859809 := bbase (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) (by norm_num)
theorem B2711893 : Blo 1607002 2711893 := bbase (se 10 (by rfl) ⟨3972, by rfl⟩ : syracuseStep 2711893 = 7945) (by norm_num)
theorem B4579669 : Blo 1607002 4579669 := bbase (se 10 (by rfl) ⟨6708, by rfl⟩ : syracuseStep 4579669 = 13417) (by norm_num)
theorem B8143253 : Blo 1607002 8143253 := bbase (se 6 (by rfl) ⟨190857, by rfl⟩ : syracuseStep 8143253 = 381715) (by norm_num)
theorem B4071829 : Blo 1607002 4071829 := bbase (se 6 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 4071829 = 190867) (by norm_num)
theorem B2711981 : Blo 1607002 2711981 := bbase (se 3 (by rfl) ⟨508496, by rfl⟩ : syracuseStep 2711981 = 1016993) (by norm_num)
theorem B1630681 : Blo 1607002 1630681 := bbase (se 2 (by rfl) ⟨611505, by rfl⟩ : syracuseStep 1630681 = 1223011) (by norm_num)
theorem B1630685 : Blo 1607002 1630685 := bbase (se 3 (by rfl) ⟨305753, by rfl⟩ : syracuseStep 1630685 = 611507) (by norm_num)
theorem B4071941 : Blo 1607002 4071941 := bbase (se 4 (by rfl) ⟨381744, by rfl⟩ : syracuseStep 4071941 = 763489) (by norm_num)
theorem B2712109 : Blo 1607002 2712109 := bbase (se 3 (by rfl) ⟨508520, by rfl⟩ : syracuseStep 2712109 = 1017041) (by norm_num)
theorem B2712197 : Blo 1607002 2712197 := bbase (se 4 (by rfl) ⟨254268, by rfl⟩ : syracuseStep 2712197 = 508537) (by norm_num)
theorem B9159317 : Blo 1607002 9159317 := bbase (se 6 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 9159317 = 429343) (by norm_num)
theorem B5423813 : Blo 1607002 5423813 := bbase (se 4 (by rfl) ⟨508482, by rfl⟩ : syracuseStep 5423813 = 1016965) (by norm_num)
theorem B4072133 : Blo 1607002 4072133 := bbase (se 4 (by rfl) ⟨381762, by rfl⟩ : syracuseStep 4072133 = 763525) (by norm_num)
theorem B6103781 : Blo 1607002 6103781 := bbase (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) (by norm_num)
theorem B2712325 : Blo 1607002 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B8135477 : Blo 1607002 8135477 := bbase (se 5 (by rfl) ⟨381350, by rfl⟩ : syracuseStep 8135477 = 762701) (by norm_num)
theorem B2712413 : Blo 1607002 2712413 := bbase (se 3 (by rfl) ⟨508577, by rfl⟩ : syracuseStep 2712413 = 1017155) (by norm_num)
theorem B6865813 : Blo 1607002 6865813 := bbase (se 6 (by rfl) ⟨160917, by rfl⟩ : syracuseStep 6865813 = 321835) (by norm_num)
theorem B2712541 : Blo 1607002 2712541 := bbase (se 3 (by rfl) ⟨508601, by rfl⟩ : syracuseStep 2712541 = 1017203) (by norm_num)
theorem B6104069 : Blo 1607002 6104069 := bbase (se 4 (by rfl) ⟨572256, by rfl⟩ : syracuseStep 6104069 = 1144513) (by norm_num)
theorem B4072477 : Blo 1607002 4072477 := bbase (se 3 (by rfl) ⟨763589, by rfl⟩ : syracuseStep 4072477 = 1527179) (by norm_num)
theorem B7726117 : Blo 1607002 7726117 := bbase (se 4 (by rfl) ⟨724323, by rfl⟩ : syracuseStep 7726117 = 1448647) (by norm_num)
theorem B2712629 : Blo 1607002 2712629 := bbase (se 5 (by rfl) ⟨127154, by rfl⟩ : syracuseStep 2712629 = 254309) (by norm_num)
theorem B5424245 : Blo 1607002 5424245 := bbase (se 5 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 5424245 = 508523) (by norm_num)
theorem B4072589 : Blo 1607002 4072589 := bbase (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) (by norm_num)
theorem B2712757 : Blo 1607002 2712757 := bbase (se 5 (by rfl) ⟨127160, by rfl⟩ : syracuseStep 2712757 = 254321) (by norm_num)
theorem B3433693 : Blo 1607002 3433693 := bbase (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) (by norm_num)
theorem B1983745 : Blo 1607002 1983745 := bbase (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) (by norm_num)
theorem B4891909 : Blo 1607002 4891909 := bbase (se 4 (by rfl) ⟨458616, by rfl⟩ : syracuseStep 4891909 = 917233) (by norm_num)
theorem B2712845 : Blo 1607002 2712845 := bbase (se 3 (by rfl) ⟨508658, by rfl⟩ : syracuseStep 2712845 = 1017317) (by norm_num)
theorem B1959185 : Blo 1607002 1959185 := bbase (se 2 (by rfl) ⟨734694, by rfl⟩ : syracuseStep 1959185 = 1469389) (by norm_num)
theorem B4072781 : Blo 1607002 4072781 := bbase (se 3 (by rfl) ⟨763646, by rfl⟩ : syracuseStep 4072781 = 1527293) (by norm_num)
theorem B13034837 : Blo 1607002 13034837 := bbase (se 12 (by rfl) ⟨4773, by rfl⟩ : syracuseStep 13034837 = 9547) (by norm_num)
theorem B2172253 : Blo 1607002 2172253 := bbase (se 3 (by rfl) ⟨407297, by rfl⟩ : syracuseStep 2172253 = 814595) (by norm_num)
theorem B2712973 : Blo 1607002 2712973 := bbase (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) (by norm_num)
theorem B2713061 : Blo 1607002 2713061 := bbase (se 4 (by rfl) ⟨254349, by rfl⟩ : syracuseStep 2713061 = 508699) (by norm_num)
theorem B5424677 : Blo 1607002 5424677 := bbase (se 4 (by rfl) ⟨508563, by rfl⟩ : syracuseStep 5424677 = 1017127) (by norm_num)
theorem B3434069 : Blo 1607002 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B2713189 : Blo 1607002 2713189 := bbase (se 4 (by rfl) ⟨254361, by rfl⟩ : syracuseStep 2713189 = 508723) (by norm_num)
theorem B8144549 : Blo 1607002 8144549 := bbase (se 4 (by rfl) ⟨763551, by rfl⟩ : syracuseStep 8144549 = 1527103) (by norm_num)
theorem B2713277 : Blo 1607002 2713277 := bbase (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) (by norm_num)
theorem B2172701 : Blo 1607002 2172701 := bbase (se 3 (by rfl) ⟨407381, by rfl⟩ : syracuseStep 2172701 = 814763) (by norm_num)
theorem B4581173 : Blo 1607002 4581173 := bbase (se 5 (by rfl) ⟨214742, by rfl⟩ : syracuseStep 4581173 = 429485) (by norm_num)
theorem B2713405 : Blo 1607002 2713405 := bbase (se 3 (by rfl) ⟨508763, by rfl⟩ : syracuseStep 2713405 = 1017527) (by norm_num)
theorem B11585429 : Blo 1607002 11585429 := bbase (se 6 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 11585429 = 543067) (by norm_num)
theorem B2713493 : Blo 1607002 2713493 := bbase (se 6 (by rfl) ⟨63597, by rfl⟩ : syracuseStep 2713493 = 127195) (by norm_num)
theorem B5425109 : Blo 1607002 5425109 := bbase (se 7 (by rfl) ⟨63575, by rfl⟩ : syracuseStep 5425109 = 127151) (by norm_num)
theorem B17393621 : Blo 1607002 17393621 := bbase (se 7 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 17393621 = 407663) (by norm_num)
theorem B2410517 : Blo 1607002 2410517 := bbase (se 6 (by rfl) ⟨56496, by rfl⟩ : syracuseStep 2410517 = 112993) (by norm_num)
theorem B2713621 : Blo 1607002 2713621 := bbase (se 6 (by rfl) ⟨63600, by rfl⟩ : syracuseStep 2713621 = 127201) (by norm_num)
theorem B2410541 : Blo 1607002 2410541 := bbase (se 3 (by rfl) ⟨451976, by rfl⟩ : syracuseStep 2410541 = 903953) (by norm_num)
theorem B2410565 : Blo 1607002 2410565 := bbase (se 4 (by rfl) ⟨225990, by rfl⟩ : syracuseStep 2410565 = 451981) (by norm_num)
theorem B8136773 : Blo 1607002 8136773 := bbase (se 4 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 8136773 = 1525645) (by norm_num)
theorem B2410589 : Blo 1607002 2410589 := bbase (se 3 (by rfl) ⟨451985, by rfl⟩ : syracuseStep 2410589 = 903971) (by norm_num)
theorem B2713709 : Blo 1607002 2713709 := bbase (se 3 (by rfl) ⟨508820, by rfl⟩ : syracuseStep 2713709 = 1017641) (by norm_num)
theorem B2410613 : Blo 1607002 2410613 := bbase (se 5 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 2410613 = 225995) (by norm_num)
theorem B2410637 : Blo 1607002 2410637 := bbase (se 3 (by rfl) ⟨451994, by rfl⟩ : syracuseStep 2410637 = 903989) (by norm_num)
theorem B2410661 : Blo 1607002 2410661 := bbase (se 4 (by rfl) ⟨225999, by rfl⟩ : syracuseStep 2410661 = 451999) (by norm_num)
theorem B6105253 : Blo 1607002 6105253 := bbase (se 4 (by rfl) ⟨572367, by rfl⟩ : syracuseStep 6105253 = 1144735) (by norm_num)
theorem B2410685 : Blo 1607002 2410685 := bbase (se 3 (by rfl) ⟨452003, by rfl⟩ : syracuseStep 2410685 = 904007) (by norm_num)
theorem B2410709 : Blo 1607002 2410709 := bbase (se 7 (by rfl) ⟨28250, by rfl⟩ : syracuseStep 2410709 = 56501) (by norm_num)
theorem B2410733 : Blo 1607002 2410733 := bbase (se 3 (by rfl) ⟨452012, by rfl⟩ : syracuseStep 2410733 = 904025) (by norm_num)
theorem B2713837 : Blo 1607002 2713837 := bbase (se 3 (by rfl) ⟨508844, by rfl⟩ : syracuseStep 2713837 = 1017689) (by norm_num)
theorem B2033905 : Blo 1607002 2033905 := bbase (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) (by norm_num)
theorem B2410757 : Blo 1607002 2410757 := bbase (se 4 (by rfl) ⟨226008, by rfl⟩ : syracuseStep 2410757 = 452017) (by norm_num)
theorem B2410781 : Blo 1607002 2410781 := bbase (se 3 (by rfl) ⟨452021, by rfl⟩ : syracuseStep 2410781 = 904043) (by norm_num)
theorem B2410805 : Blo 1607002 2410805 := bbase (se 5 (by rfl) ⟨113006, by rfl⟩ : syracuseStep 2410805 = 226013) (by norm_num)
theorem B2713925 : Blo 1607002 2713925 := bbase (se 4 (by rfl) ⟨254430, by rfl⟩ : syracuseStep 2713925 = 508861) (by norm_num)
theorem B2410829 : Blo 1607002 2410829 := bbase (se 3 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 2410829 = 904061) (by norm_num)
theorem B2034001 : Blo 1607002 2034001 := bbase (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) (by norm_num)
theorem B2410853 : Blo 1607002 2410853 := bbase (se 4 (by rfl) ⟨226017, by rfl⟩ : syracuseStep 2410853 = 452035) (by norm_num)
theorem B6867301 : Blo 1607002 6867301 := bbase (se 4 (by rfl) ⟨643809, by rfl⟩ : syracuseStep 6867301 = 1287619) (by norm_num)
theorem B6867317 : Blo 1607002 6867317 := bbase (se 5 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 6867317 = 643811) (by norm_num)
theorem B2410877 : Blo 1607002 2410877 := bbase (se 3 (by rfl) ⟨452039, by rfl⟩ : syracuseStep 2410877 = 904079) (by norm_num)
theorem B5425541 : Blo 1607002 5425541 := bbase (se 4 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 5425541 = 1017289) (by norm_num)
theorem B2410901 : Blo 1607002 2410901 := bbase (se 6 (by rfl) ⟨56505, by rfl⟩ : syracuseStep 2410901 = 113011) (by norm_num)
theorem B2574757 : Blo 1607002 2574757 := bbase (se 4 (by rfl) ⟨241383, by rfl⟩ : syracuseStep 2574757 = 482767) (by norm_num)
theorem B2410925 : Blo 1607002 2410925 := bbase (se 3 (by rfl) ⟨452048, by rfl⟩ : syracuseStep 2410925 = 904097) (by norm_num)
theorem B2410949 : Blo 1607002 2410949 := bbase (se 4 (by rfl) ⟨226026, by rfl⟩ : syracuseStep 2410949 = 452053) (by norm_num)
theorem B2714053 : Blo 1607002 2714053 := bbase (se 4 (by rfl) ⟨254442, by rfl⟩ : syracuseStep 2714053 = 508885) (by norm_num)
theorem B6105557 : Blo 1607002 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B2410973 : Blo 1607002 2410973 := bbase (se 3 (by rfl) ⟨452057, by rfl⟩ : syracuseStep 2410973 = 904115) (by norm_num)
theorem B2410997 : Blo 1607002 2410997 := bbase (se 5 (by rfl) ⟨113015, by rfl⟩ : syracuseStep 2410997 = 226031) (by norm_num)
theorem B2034173 : Blo 1607002 2034173 := bbase (se 3 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 2034173 = 762815) (by norm_num)
theorem B2411021 : Blo 1607002 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B2714141 : Blo 1607002 2714141 := bbase (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) (by norm_num)
theorem B2411045 : Blo 1607002 2411045 := bbase (se 4 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 2411045 = 452071) (by norm_num)
theorem B2034229 : Blo 1607002 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2288189 : Blo 1607002 2288189 := bbase (se 3 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 2288189 = 858071) (by norm_num)
theorem B2411069 : Blo 1607002 2411069 := bbase (se 3 (by rfl) ⟨452075, by rfl⟩ : syracuseStep 2411069 = 904151) (by norm_num)
theorem B2411093 : Blo 1607002 2411093 := bbase (se 8 (by rfl) ⟨14127, by rfl⟩ : syracuseStep 2411093 = 28255) (by norm_num)
theorem B2411117 : Blo 1607002 2411117 := bbase (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) (by norm_num)
theorem B2411141 : Blo 1607002 2411141 := bbase (se 4 (by rfl) ⟨226044, by rfl⟩ : syracuseStep 2411141 = 452089) (by norm_num)
theorem B2034325 : Blo 1607002 2034325 := bbase (se 6 (by rfl) ⟨47679, by rfl⟩ : syracuseStep 2034325 = 95359) (by norm_num)
theorem B2411165 : Blo 1607002 2411165 := bbase (se 3 (by rfl) ⟨452093, by rfl⟩ : syracuseStep 2411165 = 904187) (by norm_num)
theorem B2714269 : Blo 1607002 2714269 := bbase (se 3 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 2714269 = 1017851) (by norm_num)
theorem B2411189 : Blo 1607002 2411189 := bbase (se 5 (by rfl) ⟨113024, by rfl⟩ : syracuseStep 2411189 = 226049) (by norm_num)
theorem B2411213 : Blo 1607002 2411213 := bbase (se 3 (by rfl) ⟨452102, by rfl⟩ : syracuseStep 2411213 = 904205) (by norm_num)
theorem B5794517 : Blo 1607002 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B2411237 : Blo 1607002 2411237 := bbase (se 4 (by rfl) ⟨226053, by rfl⟩ : syracuseStep 2411237 = 452107) (by norm_num)
theorem B2714357 : Blo 1607002 2714357 := bbase (se 5 (by rfl) ⟨127235, by rfl⟩ : syracuseStep 2714357 = 254471) (by norm_num)
theorem B2411261 : Blo 1607002 2411261 := bbase (se 3 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 2411261 = 904223) (by norm_num)
theorem B2411285 : Blo 1607002 2411285 := bbase (se 6 (by rfl) ⟨56514, by rfl⟩ : syracuseStep 2411285 = 113029) (by norm_num)
theorem B2411309 : Blo 1607002 2411309 := bbase (se 3 (by rfl) ⟨452120, by rfl⟩ : syracuseStep 2411309 = 904241) (by norm_num)
theorem B5425973 : Blo 1607002 5425973 := bbase (se 5 (by rfl) ⟨254342, by rfl⟩ : syracuseStep 5425973 = 508685) (by norm_num)
theorem B9161525 : Blo 1607002 9161525 := bbase (se 5 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 9161525 = 858893) (by norm_num)
theorem B2034497 : Blo 1607002 2034497 := bbase (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) (by norm_num)
theorem B2411333 : Blo 1607002 2411333 := bbase (se 4 (by rfl) ⟨226062, by rfl⟩ : syracuseStep 2411333 = 452125) (by norm_num)
theorem B5794645 : Blo 1607002 5794645 := bbase (se 9 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 5794645 = 33953) (by norm_num)
theorem B2411357 : Blo 1607002 2411357 := bbase (se 3 (by rfl) ⟨452129, by rfl⟩ : syracuseStep 2411357 = 904259) (by norm_num)
theorem B2411381 : Blo 1607002 2411381 := bbase (se 5 (by rfl) ⟨113033, by rfl⟩ : syracuseStep 2411381 = 226067) (by norm_num)
theorem B2714485 : Blo 1607002 2714485 := bbase (se 5 (by rfl) ⟨127241, by rfl⟩ : syracuseStep 2714485 = 254483) (by norm_num)
theorem B2034553 : Blo 1607002 2034553 := bbase (se 2 (by rfl) ⟨762957, by rfl⟩ : syracuseStep 2034553 = 1525915) (by norm_num)
theorem B2411405 : Blo 1607002 2411405 := bbase (se 3 (by rfl) ⟨452138, by rfl⟩ : syracuseStep 2411405 = 904277) (by norm_num)
theorem B1739665 : Blo 1607002 1739665 := bbase (se 2 (by rfl) ⟨652374, by rfl⟩ : syracuseStep 1739665 = 1304749) (by norm_num)
theorem B2411429 : Blo 1607002 2411429 := bbase (se 4 (by rfl) ⟨226071, by rfl⟩ : syracuseStep 2411429 = 452143) (by norm_num)
theorem B2411453 : Blo 1607002 2411453 := bbase (se 3 (by rfl) ⟨452147, by rfl⟩ : syracuseStep 2411453 = 904295) (by norm_num)
theorem B3861445 : Blo 1607002 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B2575309 : Blo 1607002 2575309 := bbase (se 3 (by rfl) ⟨482870, by rfl⟩ : syracuseStep 2575309 = 965741) (by norm_num)
theorem B2714573 : Blo 1607002 2714573 := bbase (se 3 (by rfl) ⟨508982, by rfl⟩ : syracuseStep 2714573 = 1017965) (by norm_num)
theorem B2411477 : Blo 1607002 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B2034649 : Blo 1607002 2034649 := bbase (se 2 (by rfl) ⟨762993, by rfl⟩ : syracuseStep 2034649 = 1525987) (by norm_num)
theorem B2411501 : Blo 1607002 2411501 := bbase (se 3 (by rfl) ⟨452156, by rfl⟩ : syracuseStep 2411501 = 904313) (by norm_num)
theorem B6605813 : Blo 1607002 6605813 := bbase (se 5 (by rfl) ⟨309647, by rfl⟩ : syracuseStep 6605813 = 619295) (by norm_num)
theorem B2411525 : Blo 1607002 2411525 := bbase (se 4 (by rfl) ⟨226080, by rfl⟩ : syracuseStep 2411525 = 452161) (by norm_num)
theorem B2411549 : Blo 1607002 2411549 := bbase (se 3 (by rfl) ⟨452165, by rfl⟩ : syracuseStep 2411549 = 904331) (by norm_num)
theorem B2411573 : Blo 1607002 2411573 := bbase (se 5 (by rfl) ⟨113042, by rfl⟩ : syracuseStep 2411573 = 226085) (by norm_num)
theorem B3615821 : Blo 1607002 3615821 := bbase (se 3 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 3615821 = 1355933) (by norm_num)
theorem B2411597 : Blo 1607002 2411597 := bbase (se 3 (by rfl) ⟨452174, by rfl⟩ : syracuseStep 2411597 = 904349) (by norm_num)
theorem B2714701 : Blo 1607002 2714701 := bbase (se 3 (by rfl) ⟨509006, by rfl⟩ : syracuseStep 2714701 = 1018013) (by norm_num)
theorem B2288741 : Blo 1607002 2288741 := bbase (se 4 (by rfl) ⟨214569, by rfl⟩ : syracuseStep 2288741 = 429139) (by norm_num)
theorem B2411621 : Blo 1607002 2411621 := bbase (se 4 (by rfl) ⟨226089, by rfl⟩ : syracuseStep 2411621 = 452179) (by norm_num)
theorem B2411645 : Blo 1607002 2411645 := bbase (se 3 (by rfl) ⟨452183, by rfl⟩ : syracuseStep 2411645 = 904367) (by norm_num)
theorem B2034821 : Blo 1607002 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B3615893 : Blo 1607002 3615893 := bbase (se 6 (by rfl) ⟨84747, by rfl⟩ : syracuseStep 3615893 = 169495) (by norm_num)
theorem B2411669 : Blo 1607002 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B2714789 : Blo 1607002 2714789 := bbase (se 4 (by rfl) ⟨254511, by rfl⟩ : syracuseStep 2714789 = 509023) (by norm_num)
theorem B2411693 : Blo 1607002 2411693 := bbase (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) (by norm_num)
theorem B2034877 : Blo 1607002 2034877 := bbase (se 3 (by rfl) ⟨381539, by rfl⟩ : syracuseStep 2034877 = 763079) (by norm_num)
theorem B3435709 : Blo 1607002 3435709 := bbase (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) (by norm_num)
theorem B2411717 : Blo 1607002 2411717 := bbase (se 4 (by rfl) ⟨226098, by rfl⟩ : syracuseStep 2411717 = 452197) (by norm_num)
theorem B2575565 : Blo 1607002 2575565 := bbase (se 3 (by rfl) ⟨482918, by rfl⟩ : syracuseStep 2575565 = 965837) (by norm_num)
theorem B3615965 : Blo 1607002 3615965 := bbase (se 3 (by rfl) ⟨677993, by rfl⟩ : syracuseStep 3615965 = 1355987) (by norm_num)
theorem B2411741 : Blo 1607002 2411741 := bbase (se 3 (by rfl) ⟨452201, by rfl⟩ : syracuseStep 2411741 = 904403) (by norm_num)
theorem B5426405 : Blo 1607002 5426405 := bbase (se 4 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 5426405 = 1017451) (by norm_num)
theorem B2411765 : Blo 1607002 2411765 := bbase (se 5 (by rfl) ⟨113051, by rfl⟩ : syracuseStep 2411765 = 226103) (by norm_num)
theorem B2411789 : Blo 1607002 2411789 := bbase (se 3 (by rfl) ⟨452210, by rfl⟩ : syracuseStep 2411789 = 904421) (by norm_num)
theorem B3665173 : Blo 1607002 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B9784597 : Blo 1607002 9784597 := bbase (se 6 (by rfl) ⟨229326, by rfl⟩ : syracuseStep 9784597 = 458653) (by norm_num)
theorem B2034973 : Blo 1607002 2034973 := bbase (se 3 (by rfl) ⟨381557, by rfl⟩ : syracuseStep 2034973 = 763115) (by norm_num)
theorem B3616037 : Blo 1607002 3616037 := bbase (se 4 (by rfl) ⟨339003, by rfl⟩ : syracuseStep 3616037 = 678007) (by norm_num)
theorem B2411813 : Blo 1607002 2411813 := bbase (se 4 (by rfl) ⟨226107, by rfl⟩ : syracuseStep 2411813 = 452215) (by norm_num)
theorem B2714917 : Blo 1607002 2714917 := bbase (se 4 (by rfl) ⟨254523, by rfl⟩ : syracuseStep 2714917 = 509047) (by norm_num)
theorem B3050797 : Blo 1607002 3050797 := bbase (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) (by norm_num)
theorem B2411837 : Blo 1607002 2411837 := bbase (se 3 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 2411837 = 904439) (by norm_num)
theorem B8138069 : Blo 1607002 8138069 := bbase (se 11 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 8138069 = 11921) (by norm_num)
theorem B2411861 : Blo 1607002 2411861 := bbase (se 11 (by rfl) ⟨1766, by rfl⟩ : syracuseStep 2411861 = 3533) (by norm_num)
theorem B3616109 : Blo 1607002 3616109 := bbase (se 3 (by rfl) ⟨678020, by rfl⟩ : syracuseStep 3616109 = 1356041) (by norm_num)
theorem B2411885 : Blo 1607002 2411885 := bbase (se 3 (by rfl) ⟨452228, by rfl⟩ : syracuseStep 2411885 = 904457) (by norm_num)
theorem B2715005 : Blo 1607002 2715005 := bbase (se 3 (by rfl) ⟨509063, by rfl⟩ : syracuseStep 2715005 = 1018127) (by norm_num)
theorem B2411909 : Blo 1607002 2411909 := bbase (se 4 (by rfl) ⟨226116, by rfl⟩ : syracuseStep 2411909 = 452233) (by norm_num)
theorem B2411933 : Blo 1607002 2411933 := bbase (se 3 (by rfl) ⟨452237, by rfl⟩ : syracuseStep 2411933 = 904475) (by norm_num)
theorem B3616181 : Blo 1607002 3616181 := bbase (se 5 (by rfl) ⟨169508, by rfl⟩ : syracuseStep 3616181 = 339017) (by norm_num)
theorem B2411957 : Blo 1607002 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B3050941 : Blo 1607002 3050941 := bbase (se 3 (by rfl) ⟨572051, by rfl⟩ : syracuseStep 3050941 = 1144103) (by norm_num)
theorem B2035145 : Blo 1607002 2035145 := bbase (se 2 (by rfl) ⟨763179, by rfl⟩ : syracuseStep 2035145 = 1526359) (by norm_num)
theorem B2411981 : Blo 1607002 2411981 := bbase (se 3 (by rfl) ⟨452246, by rfl⟩ : syracuseStep 2411981 = 904493) (by norm_num)
theorem B2412005 : Blo 1607002 2412005 := bbase (se 4 (by rfl) ⟨226125, by rfl⟩ : syracuseStep 2412005 = 452251) (by norm_num)
theorem B3616253 : Blo 1607002 3616253 := bbase (se 3 (by rfl) ⟨678047, by rfl⟩ : syracuseStep 3616253 = 1356095) (by norm_num)
theorem B2412029 : Blo 1607002 2412029 := bbase (se 3 (by rfl) ⟨452255, by rfl⟩ : syracuseStep 2412029 = 904511) (by norm_num)
theorem B2715133 : Blo 1607002 2715133 := bbase (se 3 (by rfl) ⟨509087, by rfl⟩ : syracuseStep 2715133 = 1018175) (by norm_num)
theorem B2035201 : Blo 1607002 2035201 := bbase (se 2 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 2035201 = 1526401) (by norm_num)
theorem B2412053 : Blo 1607002 2412053 := bbase (se 6 (by rfl) ⟨56532, by rfl⟩ : syracuseStep 2412053 = 113065) (by norm_num)
theorem B2412077 : Blo 1607002 2412077 := bbase (se 3 (by rfl) ⟨452264, by rfl⟩ : syracuseStep 2412077 = 904529) (by norm_num)
theorem B3616325 : Blo 1607002 3616325 := bbase (se 4 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 3616325 = 678061) (by norm_num)
theorem B2412101 : Blo 1607002 2412101 := bbase (se 4 (by rfl) ⟨226134, by rfl⟩ : syracuseStep 2412101 = 452269) (by norm_num)
theorem B12381781 : Blo 1607002 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B3051101 : Blo 1607002 3051101 := bbase (se 3 (by rfl) ⟨572081, by rfl⟩ : syracuseStep 3051101 = 1144163) (by norm_num)
theorem B2412125 : Blo 1607002 2412125 := bbase (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) (by norm_num)
theorem B2035297 : Blo 1607002 2035297 := bbase (se 2 (by rfl) ⟨763236, by rfl⟩ : syracuseStep 2035297 = 1526473) (by norm_num)
theorem B3862117 : Blo 1607002 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B2412149 : Blo 1607002 2412149 := bbase (se 5 (by rfl) ⟨113069, by rfl⟩ : syracuseStep 2412149 = 226139) (by norm_num)
theorem B3616397 : Blo 1607002 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B2412173 : Blo 1607002 2412173 := bbase (se 3 (by rfl) ⟨452282, by rfl⟩ : syracuseStep 2412173 = 904565) (by norm_num)
theorem B5426837 : Blo 1607002 5426837 := bbase (se 6 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 5426837 = 254383) (by norm_num)
theorem B2412197 : Blo 1607002 2412197 := bbase (se 4 (by rfl) ⟨226143, by rfl⟩ : syracuseStep 2412197 = 452287) (by norm_num)
theorem B2412221 : Blo 1607002 2412221 := bbase (se 3 (by rfl) ⟨452291, by rfl⟩ : syracuseStep 2412221 = 904583) (by norm_num)
theorem B3616469 : Blo 1607002 3616469 := bbase (se 7 (by rfl) ⟨42380, by rfl⟩ : syracuseStep 3616469 = 84761) (by norm_num)
theorem B2412245 : Blo 1607002 2412245 := bbase (se 7 (by rfl) ⟨28268, by rfl⟩ : syracuseStep 2412245 = 56537) (by norm_num)
theorem B5590757 : Blo 1607002 5590757 := bbase (se 4 (by rfl) ⟨524133, by rfl⟩ : syracuseStep 5590757 = 1048267) (by norm_num)
theorem B3051245 : Blo 1607002 3051245 := bbase (se 3 (by rfl) ⟨572108, by rfl⟩ : syracuseStep 3051245 = 1144217) (by norm_num)
theorem B2412269 : Blo 1607002 2412269 := bbase (se 3 (by rfl) ⟨452300, by rfl⟩ : syracuseStep 2412269 = 904601) (by norm_num)
theorem B2412293 : Blo 1607002 2412293 := bbase (se 4 (by rfl) ⟨226152, by rfl⟩ : syracuseStep 2412293 = 452305) (by norm_num)
theorem B2035469 : Blo 1607002 2035469 := bbase (se 3 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 2035469 = 763301) (by norm_num)
theorem B3616541 : Blo 1607002 3616541 := bbase (se 3 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 3616541 = 1356203) (by norm_num)
theorem B2412317 : Blo 1607002 2412317 := bbase (se 3 (by rfl) ⟨452309, by rfl⟩ : syracuseStep 2412317 = 904619) (by norm_num)
theorem B2412341 : Blo 1607002 2412341 := bbase (se 5 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 2412341 = 226157) (by norm_num)
theorem B2035525 : Blo 1607002 2035525 := bbase (se 4 (by rfl) ⟨190830, by rfl⟩ : syracuseStep 2035525 = 381661) (by norm_num)
theorem B3862349 : Blo 1607002 3862349 := bbase (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) (by norm_num)
theorem B2412365 : Blo 1607002 2412365 := bbase (se 3 (by rfl) ⟨452318, by rfl⟩ : syracuseStep 2412365 = 904637) (by norm_num)
theorem B2289493 : Blo 1607002 2289493 := bbase (se 9 (by rfl) ⟨6707, by rfl⟩ : syracuseStep 2289493 = 13415) (by norm_num)
theorem B3616613 : Blo 1607002 3616613 := bbase (se 4 (by rfl) ⟨339057, by rfl⟩ : syracuseStep 3616613 = 678115) (by norm_num)
theorem B2412389 : Blo 1607002 2412389 := bbase (se 4 (by rfl) ⟨226161, by rfl⟩ : syracuseStep 2412389 = 452323) (by norm_num)
theorem B2477933 : Blo 1607002 2477933 := bbase (se 3 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 2477933 = 929225) (by norm_num)
theorem B11587445 : Blo 1607002 11587445 := bbase (se 5 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 11587445 = 1086323) (by norm_num)
theorem B3305333 : Blo 1607002 3305333 := bbase (se 5 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 3305333 = 309875) (by norm_num)
theorem B3862397 : Blo 1607002 3862397 := bbase (se 3 (by rfl) ⟨724199, by rfl⟩ : syracuseStep 3862397 = 1448399) (by norm_num)
theorem B2412413 : Blo 1607002 2412413 := bbase (se 3 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 2412413 = 904655) (by norm_num)
theorem B2576269 : Blo 1607002 2576269 := bbase (se 3 (by rfl) ⟨483050, by rfl⟩ : syracuseStep 2576269 = 966101) (by norm_num)
theorem B2412437 : Blo 1607002 2412437 := bbase (se 6 (by rfl) ⟨56541, by rfl⟩ : syracuseStep 2412437 = 113083) (by norm_num)
theorem B4124573 : Blo 1607002 4124573 := bbase (se 3 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 4124573 = 1546715) (by norm_num)
theorem B2035621 : Blo 1607002 2035621 := bbase (se 4 (by rfl) ⟨190839, by rfl⟩ : syracuseStep 2035621 = 381679) (by norm_num)
theorem B3616685 : Blo 1607002 3616685 := bbase (se 3 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 3616685 = 1356257) (by norm_num)
theorem B2412461 : Blo 1607002 2412461 := bbase (se 3 (by rfl) ⟨452336, by rfl⟩ : syracuseStep 2412461 = 904673) (by norm_num)
theorem B13733813 : Blo 1607002 13733813 := bbase (se 5 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 13733813 = 1287545) (by norm_num)
theorem B2412485 : Blo 1607002 2412485 := bbase (se 4 (by rfl) ⟨226170, by rfl⟩ : syracuseStep 2412485 = 452341) (by norm_num)
theorem B2412509 : Blo 1607002 2412509 := bbase (se 3 (by rfl) ⟨452345, by rfl⟩ : syracuseStep 2412509 = 904691) (by norm_num)
theorem B3616757 : Blo 1607002 3616757 := bbase (se 5 (by rfl) ⟨169535, by rfl⟩ : syracuseStep 3616757 = 339071) (by norm_num)
theorem B2412533 : Blo 1607002 2412533 := bbase (se 5 (by rfl) ⟨113087, by rfl⟩ : syracuseStep 2412533 = 226175) (by norm_num)
theorem B3051533 : Blo 1607002 3051533 := bbase (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) (by norm_num)
theorem B2412557 : Blo 1607002 2412557 := bbase (se 3 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 2412557 = 904709) (by norm_num)
theorem B2412581 : Blo 1607002 2412581 := bbase (se 4 (by rfl) ⟨226179, by rfl⟩ : syracuseStep 2412581 = 452359) (by norm_num)
theorem B3616829 : Blo 1607002 3616829 := bbase (se 3 (by rfl) ⟨678155, by rfl⟩ : syracuseStep 3616829 = 1356311) (by norm_num)
theorem B2412605 : Blo 1607002 2412605 := bbase (se 3 (by rfl) ⟨452363, by rfl⟩ : syracuseStep 2412605 = 904727) (by norm_num)
theorem B5427269 : Blo 1607002 5427269 := bbase (se 4 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 5427269 = 1017613) (by norm_num)
theorem B2035793 : Blo 1607002 2035793 := bbase (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) (by norm_num)
theorem B2412629 : Blo 1607002 2412629 := bbase (se 8 (by rfl) ⟨14136, by rfl⟩ : syracuseStep 2412629 = 28273) (by norm_num)
theorem B7729253 : Blo 1607002 7729253 := bbase (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) (by norm_num)
theorem B2412653 : Blo 1607002 2412653 := bbase (se 3 (by rfl) ⟨452372, by rfl⟩ : syracuseStep 2412653 = 904745) (by norm_num)
theorem B3616901 : Blo 1607002 3616901 := bbase (se 4 (by rfl) ⟨339084, by rfl⟩ : syracuseStep 3616901 = 678169) (by norm_num)
theorem B2412677 : Blo 1607002 2412677 := bbase (se 4 (by rfl) ⟨226188, by rfl⟩ : syracuseStep 2412677 = 452377) (by norm_num)
theorem B2035849 : Blo 1607002 2035849 := bbase (se 2 (by rfl) ⟨763443, by rfl⟩ : syracuseStep 2035849 = 1526887) (by norm_num)
theorem B2412701 : Blo 1607002 2412701 := bbase (se 3 (by rfl) ⟨452381, by rfl⟩ : syracuseStep 2412701 = 904763) (by norm_num)
theorem B3051685 : Blo 1607002 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B2412725 : Blo 1607002 2412725 := bbase (se 5 (by rfl) ⟨113096, by rfl⟩ : syracuseStep 2412725 = 226193) (by norm_num)
theorem B3616973 : Blo 1607002 3616973 := bbase (se 3 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 3616973 = 1356365) (by norm_num)
theorem B2412749 : Blo 1607002 2412749 := bbase (se 3 (by rfl) ⟨452390, by rfl⟩ : syracuseStep 2412749 = 904781) (by norm_num)
theorem B2412773 : Blo 1607002 2412773 := bbase (se 4 (by rfl) ⟨226197, by rfl⟩ : syracuseStep 2412773 = 452395) (by norm_num)
theorem B2035945 : Blo 1607002 2035945 := bbase (se 2 (by rfl) ⟨763479, by rfl⟩ : syracuseStep 2035945 = 1526959) (by norm_num)
theorem B2412797 : Blo 1607002 2412797 := bbase (se 3 (by rfl) ⟨452399, by rfl⟩ : syracuseStep 2412797 = 904799) (by norm_num)
theorem B4403461 : Blo 1607002 4403461 := bbase (se 4 (by rfl) ⟨412824, by rfl⟩ : syracuseStep 4403461 = 825649) (by norm_num)
theorem B2896141 : Blo 1607002 2896141 := bbase (se 3 (by rfl) ⟨543026, by rfl⟩ : syracuseStep 2896141 = 1086053) (by norm_num)
theorem B3617045 : Blo 1607002 3617045 := bbase (se 6 (by rfl) ⟨84774, by rfl⟩ : syracuseStep 3617045 = 169549) (by norm_num)
theorem B2412821 : Blo 1607002 2412821 := bbase (se 6 (by rfl) ⟨56550, by rfl⟩ : syracuseStep 2412821 = 113101) (by norm_num)
theorem B1675561 : Blo 1607002 1675561 := bbase (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) (by norm_num)
theorem B2412845 : Blo 1607002 2412845 := bbase (se 3 (by rfl) ⟨452408, by rfl⟩ : syracuseStep 2412845 = 904817) (by norm_num)
theorem B2576693 : Blo 1607002 2576693 := bbase (se 5 (by rfl) ⟨120782, by rfl⟩ : syracuseStep 2576693 = 241565) (by norm_num)
theorem B2412869 : Blo 1607002 2412869 := bbase (se 4 (by rfl) ⟨226206, by rfl⟩ : syracuseStep 2412869 = 452413) (by norm_num)
theorem B3617117 : Blo 1607002 3617117 := bbase (se 3 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 3617117 = 1356419) (by norm_num)
theorem B2412893 : Blo 1607002 2412893 := bbase (se 3 (by rfl) ⟨452417, by rfl⟩ : syracuseStep 2412893 = 904835) (by norm_num)
theorem B8687989 : Blo 1607002 8687989 := bbase (se 5 (by rfl) ⟨407249, by rfl⟩ : syracuseStep 8687989 = 814499) (by norm_num)
theorem B2412917 : Blo 1607002 2412917 := bbase (se 5 (by rfl) ⟨113105, by rfl⟩ : syracuseStep 2412917 = 226211) (by norm_num)
theorem B2412941 : Blo 1607002 2412941 := bbase (se 3 (by rfl) ⟨452426, by rfl⟩ : syracuseStep 2412941 = 904853) (by norm_num)
theorem B2036117 : Blo 1607002 2036117 := bbase (se 6 (by rfl) ⟨47721, by rfl⟩ : syracuseStep 2036117 = 95443) (by norm_num)
theorem B3617189 : Blo 1607002 3617189 := bbase (se 4 (by rfl) ⟨339111, by rfl⟩ : syracuseStep 3617189 = 678223) (by norm_num)
theorem B2412965 : Blo 1607002 2412965 := bbase (se 4 (by rfl) ⟨226215, by rfl⟩ : syracuseStep 2412965 = 452431) (by norm_num)
theorem B2412989 : Blo 1607002 2412989 := bbase (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) (by norm_num)
theorem B2036173 : Blo 1607002 2036173 := bbase (se 3 (by rfl) ⟨381782, by rfl⟩ : syracuseStep 2036173 = 763565) (by norm_num)
theorem B3051989 : Blo 1607002 3051989 := bbase (se 7 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 3051989 = 71531) (by norm_num)
theorem B2413013 : Blo 1607002 2413013 := bbase (se 7 (by rfl) ⟨28277, by rfl⟩ : syracuseStep 2413013 = 56555) (by norm_num)
theorem B3617261 : Blo 1607002 3617261 := bbase (se 3 (by rfl) ⟨678236, by rfl⟩ : syracuseStep 3617261 = 1356473) (by norm_num)
theorem B2413037 : Blo 1607002 2413037 := bbase (se 3 (by rfl) ⟨452444, by rfl⟩ : syracuseStep 2413037 = 904889) (by norm_num)
theorem B5427701 : Blo 1607002 5427701 := bbase (se 5 (by rfl) ⟨254423, by rfl⟩ : syracuseStep 5427701 = 508847) (by norm_num)
theorem B2413061 : Blo 1607002 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B6107669 : Blo 1607002 6107669 := bbase (se 6 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 6107669 = 286297) (by norm_num)
theorem B1716761 : Blo 1607002 1716761 := bbase (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) (by norm_num)
theorem B2413085 : Blo 1607002 2413085 := bbase (se 3 (by rfl) ⟨452453, by rfl⟩ : syracuseStep 2413085 = 904907) (by norm_num)
theorem B2036269 : Blo 1607002 2036269 := bbase (se 3 (by rfl) ⟨381800, by rfl⟩ : syracuseStep 2036269 = 763601) (by norm_num)
theorem B3617333 : Blo 1607002 3617333 := bbase (se 5 (by rfl) ⟨169562, by rfl⟩ : syracuseStep 3617333 = 339125) (by norm_num)
theorem B2413109 : Blo 1607002 2413109 := bbase (se 5 (by rfl) ⟨113114, by rfl⟩ : syracuseStep 2413109 = 226229) (by norm_num)
theorem B6869573 : Blo 1607002 6869573 := bbase (se 4 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 6869573 = 1288045) (by norm_num)
theorem B2413133 : Blo 1607002 2413133 := bbase (se 3 (by rfl) ⟨452462, by rfl⟩ : syracuseStep 2413133 = 904925) (by norm_num)
theorem B69530197 : Blo 1607002 69530197 := bbase (se 8 (by rfl) ⟨407403, by rfl⟩ : syracuseStep 69530197 = 814807) (by norm_num)
theorem B2576981 : Blo 1607002 2576981 := bbase (se 8 (by rfl) ⟨15099, by rfl⟩ : syracuseStep 2576981 = 30199) (by norm_num)
theorem B4067941 : Blo 1607002 4067941 := bbase (se 4 (by rfl) ⟨381369, by rfl⟩ : syracuseStep 4067941 = 762739) (by norm_num)
theorem B8139365 : Blo 1607002 8139365 := bbase (se 4 (by rfl) ⟨763065, by rfl⟩ : syracuseStep 8139365 = 1526131) (by norm_num)
theorem B2413157 : Blo 1607002 2413157 := bbase (se 4 (by rfl) ⟨226233, by rfl⟩ : syracuseStep 2413157 = 452467) (by norm_num)
theorem B2290285 : Blo 1607002 2290285 := bbase (se 3 (by rfl) ⟨429428, by rfl⟩ : syracuseStep 2290285 = 858857) (by norm_num)
theorem B3617405 : Blo 1607002 3617405 := bbase (se 3 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 3617405 = 1356527) (by norm_num)
theorem B2413181 : Blo 1607002 2413181 := bbase (se 3 (by rfl) ⟨452471, by rfl⟩ : syracuseStep 2413181 = 904943) (by norm_num)
theorem B2413205 : Blo 1607002 2413205 := bbase (se 6 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 2413205 = 113119) (by norm_num)
theorem B2413229 : Blo 1607002 2413229 := bbase (se 3 (by rfl) ⟨452480, by rfl⟩ : syracuseStep 2413229 = 904961) (by norm_num)
theorem B5501621 : Blo 1607002 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B3617477 : Blo 1607002 3617477 := bbase (se 4 (by rfl) ⟨339138, by rfl⟩ : syracuseStep 3617477 = 678277) (by norm_num)
theorem B2413253 : Blo 1607002 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B4068053 : Blo 1607002 4068053 := bbase (se 7 (by rfl) ⟨47672, by rfl⟩ : syracuseStep 4068053 = 95345) (by norm_num)
theorem B2413277 : Blo 1607002 2413277 := bbase (se 3 (by rfl) ⟨452489, by rfl⟩ : syracuseStep 2413277 = 904979) (by norm_num)
theorem B2413301 : Blo 1607002 2413301 := bbase (se 5 (by rfl) ⟨113123, by rfl⟩ : syracuseStep 2413301 = 226247) (by norm_num)
theorem B2749181 : Blo 1607002 2749181 := bbase (se 3 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 2749181 = 1030943) (by norm_num)
theorem B3617549 : Blo 1607002 3617549 := bbase (se 3 (by rfl) ⟨678290, by rfl⟩ : syracuseStep 3617549 = 1356581) (by norm_num)
theorem B2413325 : Blo 1607002 2413325 := bbase (se 3 (by rfl) ⟨452498, by rfl⟩ : syracuseStep 2413325 = 904997) (by norm_num)
theorem B2413349 : Blo 1607002 2413349 := bbase (se 4 (by rfl) ⟨226251, by rfl⟩ : syracuseStep 2413349 = 452503) (by norm_num)
theorem B6107957 : Blo 1607002 6107957 := bbase (se 5 (by rfl) ⟨286310, by rfl⟩ : syracuseStep 6107957 = 572621) (by norm_num)
theorem B2577205 : Blo 1607002 2577205 := bbase (se 5 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 2577205 = 241613) (by norm_num)
theorem B2413373 : Blo 1607002 2413373 := bbase (se 3 (by rfl) ⟨452507, by rfl⟩ : syracuseStep 2413373 = 905015) (by norm_num)
theorem B3617621 : Blo 1607002 3617621 := bbase (se 9 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 3617621 = 21197) (by norm_num)
theorem B2413397 : Blo 1607002 2413397 := bbase (se 9 (by rfl) ⟨7070, by rfl⟩ : syracuseStep 2413397 = 14141) (by norm_num)
theorem B2413421 : Blo 1607002 2413421 := bbase (se 3 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 2413421 = 905033) (by norm_num)
theorem B2413445 : Blo 1607002 2413445 := bbase (se 4 (by rfl) ⟨226260, by rfl⟩ : syracuseStep 2413445 = 452521) (by norm_num)
theorem B4068245 : Blo 1607002 4068245 := bbase (se 6 (by rfl) ⟨95349, by rfl⟩ : syracuseStep 4068245 = 190699) (by norm_num)
theorem B3617693 : Blo 1607002 3617693 := bbase (se 3 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 3617693 = 1356635) (by norm_num)
theorem B2413469 : Blo 1607002 2413469 := bbase (se 3 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 2413469 = 905051) (by norm_num)
theorem B5428133 : Blo 1607002 5428133 := bbase (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) (by norm_num)
theorem B10302389 : Blo 1607002 10302389 := bbase (se 5 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 10302389 = 965849) (by norm_num)
theorem B2413493 : Blo 1607002 2413493 := bbase (se 5 (by rfl) ⟨113132, by rfl⟩ : syracuseStep 2413493 = 226265) (by norm_num)
theorem B2749373 : Blo 1607002 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B2290621 : Blo 1607002 2290621 := bbase (se 3 (by rfl) ⟨429491, by rfl⟩ : syracuseStep 2290621 = 858983) (by norm_num)
theorem B1717205 : Blo 1607002 1717205 := bbase (se 7 (by rfl) ⟨20123, by rfl⟩ : syracuseStep 1717205 = 40247) (by norm_num)
theorem B3617765 : Blo 1607002 3617765 := bbase (se 4 (by rfl) ⟨339165, by rfl⟩ : syracuseStep 3617765 = 678331) (by norm_num)
theorem B2610173 : Blo 1607002 2610173 := bbase (se 3 (by rfl) ⟨489407, by rfl⟩ : syracuseStep 2610173 = 978815) (by norm_num)
theorem B3617837 : Blo 1607002 3617837 := bbase (se 3 (by rfl) ⟨678344, by rfl⟩ : syracuseStep 3617837 = 1356689) (by norm_num)
theorem B3666997 : Blo 1607002 3666997 := bbase (se 5 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 3666997 = 343781) (by norm_num)
theorem B2864189 : Blo 1607002 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B6886469 : Blo 1607002 6886469 := bbase (se 4 (by rfl) ⟨645606, by rfl⟩ : syracuseStep 6886469 = 1291213) (by norm_num)
theorem B4641877 : Blo 1607002 4641877 := bbase (se 8 (by rfl) ⟨27198, by rfl⟩ : syracuseStep 4641877 = 54397) (by norm_num)
theorem B3617909 : Blo 1607002 3617909 := bbase (se 5 (by rfl) ⟨169589, by rfl⟩ : syracuseStep 3617909 = 339179) (by norm_num)
theorem B2290837 : Blo 1607002 2290837 := bbase (se 6 (by rfl) ⟨53691, by rfl⟩ : syracuseStep 2290837 = 107383) (by norm_num)
theorem B3617981 : Blo 1607002 3617981 := bbase (se 3 (by rfl) ⟨678371, by rfl⟩ : syracuseStep 3617981 = 1356743) (by norm_num)
theorem B3052741 : Blo 1607002 3052741 := bbase (se 4 (by rfl) ⟨286194, by rfl⟩ : syracuseStep 3052741 = 572389) (by norm_num)
theorem B1717453 : Blo 1607002 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B5149925 : Blo 1607002 5149925 := bbase (se 4 (by rfl) ⟨482805, by rfl⟩ : syracuseStep 5149925 = 965611) (by norm_num)
theorem B4068589 : Blo 1607002 4068589 := bbase (se 3 (by rfl) ⟨762860, by rfl⟩ : syracuseStep 4068589 = 1525721) (by norm_num)
theorem B3863789 : Blo 1607002 3863789 := bbase (se 3 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 3863789 = 1448921) (by norm_num)
theorem B3618053 : Blo 1607002 3618053 := bbase (se 4 (by rfl) ⟨339192, by rfl⟩ : syracuseStep 3618053 = 678385) (by norm_num)
theorem B3618125 : Blo 1607002 3618125 := bbase (se 3 (by rfl) ⟨678398, by rfl⟩ : syracuseStep 3618125 = 1356797) (by norm_num)
theorem B3052885 : Blo 1607002 3052885 := bbase (se 14 (by rfl) ⟨279, by rfl⟩ : syracuseStep 3052885 = 559) (by norm_num)
theorem B5428565 : Blo 1607002 5428565 := bbase (se 15 (by rfl) ⟨248, by rfl⟩ : syracuseStep 5428565 = 497) (by norm_num)
theorem B4068701 : Blo 1607002 4068701 := bbase (se 3 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 4068701 = 1525763) (by norm_num)
theorem B1930597 : Blo 1607002 1930597 := bbase (se 4 (by rfl) ⟨180993, by rfl⟩ : syracuseStep 1930597 = 361987) (by norm_num)
theorem B3618197 : Blo 1607002 3618197 := bbase (se 6 (by rfl) ⟨84801, by rfl⟩ : syracuseStep 3618197 = 169603) (by norm_num)
theorem B3863981 : Blo 1607002 3863981 := bbase (se 3 (by rfl) ⟨724496, by rfl⟩ : syracuseStep 3863981 = 1448993) (by norm_num)
theorem B3618269 : Blo 1607002 3618269 := bbase (se 3 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 3618269 = 1356851) (by norm_num)
theorem B3053045 : Blo 1607002 3053045 := bbase (se 5 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 3053045 = 286223) (by norm_num)
theorem B1807897 : Blo 1607002 1807897 := bbase (se 2 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 1807897 = 1355923) (by norm_num)
theorem B4068893 : Blo 1607002 4068893 := bbase (se 3 (by rfl) ⟨762917, by rfl⟩ : syracuseStep 4068893 = 1525835) (by norm_num)
theorem B3618341 : Blo 1607002 3618341 := bbase (se 4 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 3618341 = 678439) (by norm_num)
theorem B9156149 : Blo 1607002 9156149 := bbase (se 5 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 9156149 = 858389) (by norm_num)
theorem B4347445 : Blo 1607002 4347445 := bbase (se 5 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 4347445 = 407573) (by norm_num)
theorem B1807933 : Blo 1607002 1807933 := bbase (se 3 (by rfl) ⟨338987, by rfl⟩ : syracuseStep 1807933 = 677975) (by norm_num)
theorem B1807969 : Blo 1607002 1807969 := bbase (se 2 (by rfl) ⟨677988, by rfl⟩ : syracuseStep 1807969 = 1355977) (by norm_num)
theorem B3618413 : Blo 1607002 3618413 := bbase (se 3 (by rfl) ⟨678452, by rfl⟩ : syracuseStep 3618413 = 1356905) (by norm_num)
theorem B1652341 : Blo 1607002 1652341 := bbase (se 5 (by rfl) ⟨77453, by rfl⟩ : syracuseStep 1652341 = 154907) (by norm_num)
theorem B1717885 : Blo 1607002 1717885 := bbase (se 3 (by rfl) ⟨322103, by rfl⟩ : syracuseStep 1717885 = 644207) (by norm_num)
theorem B2479741 : Blo 1607002 2479741 := bbase (se 3 (by rfl) ⟨464951, by rfl⟩ : syracuseStep 2479741 = 929903) (by norm_num)
theorem B1808005 : Blo 1607002 1808005 := bbase (se 4 (by rfl) ⟨169500, by rfl⟩ : syracuseStep 1808005 = 339001) (by norm_num)
theorem B3053189 : Blo 1607002 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B4347541 : Blo 1607002 4347541 := bbase (se 6 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 4347541 = 203791) (by norm_num)
theorem B1808041 : Blo 1607002 1808041 := bbase (se 2 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 1808041 = 1356031) (by norm_num)
theorem B3618485 : Blo 1607002 3618485 := bbase (se 5 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 3618485 = 339233) (by norm_num)
theorem B1717957 : Blo 1607002 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B1808077 : Blo 1607002 1808077 := bbase (se 3 (by rfl) ⟨339014, by rfl⟩ : syracuseStep 1808077 = 678029) (by norm_num)
theorem B4576981 : Blo 1607002 4576981 := bbase (se 7 (by rfl) ⟨53636, by rfl⟩ : syracuseStep 4576981 = 107273) (by norm_num)
theorem B14669525 : Blo 1607002 14669525 := bbase (se 7 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 14669525 = 343817) (by norm_num)
theorem B1808113 : Blo 1607002 1808113 := bbase (se 2 (by rfl) ⟨678042, by rfl⟩ : syracuseStep 1808113 = 1356085) (by norm_num)
theorem B3618557 : Blo 1607002 3618557 := bbase (se 3 (by rfl) ⟨678479, by rfl⟩ : syracuseStep 3618557 = 1356959) (by norm_num)
theorem B2897669 : Blo 1607002 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B5428997 : Blo 1607002 5428997 := bbase (se 4 (by rfl) ⟨508968, by rfl⟩ : syracuseStep 5428997 = 1017937) (by norm_num)
theorem B1808149 : Blo 1607002 1808149 := bbase (se 6 (by rfl) ⟨42378, by rfl⟩ : syracuseStep 1808149 = 84757) (by norm_num)
theorem B16512821 : Blo 1607002 16512821 := bbase (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) (by norm_num)
theorem B1808185 : Blo 1607002 1808185 := bbase (se 2 (by rfl) ⟨678069, by rfl⟩ : syracuseStep 1808185 = 1356139) (by norm_num)
theorem B3618629 : Blo 1607002 3618629 := bbase (se 4 (by rfl) ⟨339246, by rfl⟩ : syracuseStep 3618629 = 678493) (by norm_num)
theorem B2897741 : Blo 1607002 2897741 := bbase (se 3 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 2897741 = 1086653) (by norm_num)
theorem B1808221 : Blo 1607002 1808221 := bbase (se 3 (by rfl) ⟨339041, by rfl⟩ : syracuseStep 1808221 = 678083) (by norm_num)
theorem B4126565 : Blo 1607002 4126565 := bbase (se 4 (by rfl) ⟨386865, by rfl⟩ : syracuseStep 4126565 = 773731) (by norm_num)
theorem B2062189 : Blo 1607002 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B4577141 : Blo 1607002 4577141 := bbase (se 5 (by rfl) ⟨214553, by rfl⟩ : syracuseStep 4577141 = 429107) (by norm_num)
theorem B4069237 : Blo 1607002 4069237 := bbase (se 5 (by rfl) ⟨190745, by rfl⟩ : syracuseStep 4069237 = 381491) (by norm_num)
theorem B8140661 : Blo 1607002 8140661 := bbase (se 5 (by rfl) ⟨381593, by rfl⟩ : syracuseStep 8140661 = 763187) (by norm_num)
theorem B1808257 : Blo 1607002 1808257 := bbase (se 2 (by rfl) ⟨678096, by rfl⟩ : syracuseStep 1808257 = 1356193) (by norm_num)
theorem B3618701 : Blo 1607002 3618701 := bbase (se 3 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 3618701 = 1357013) (by norm_num)
theorem B1808293 : Blo 1607002 1808293 := bbase (se 4 (by rfl) ⟨169527, by rfl⟩ : syracuseStep 1808293 = 339055) (by norm_num)
theorem B3053477 : Blo 1607002 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B1808329 : Blo 1607002 1808329 := bbase (se 2 (by rfl) ⟨678123, by rfl⟩ : syracuseStep 1808329 = 1356247) (by norm_num)
theorem B7722965 : Blo 1607002 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B3618773 : Blo 1607002 3618773 := bbase (se 7 (by rfl) ⟨42407, by rfl⟩ : syracuseStep 3618773 = 84815) (by norm_num)
theorem B6109141 : Blo 1607002 6109141 := bbase (se 7 (by rfl) ⟨71591, by rfl⟩ : syracuseStep 6109141 = 143183) (by norm_num)
theorem B4069349 : Blo 1607002 4069349 := bbase (se 4 (by rfl) ⟨381501, by rfl⟩ : syracuseStep 4069349 = 763003) (by norm_num)
theorem B1808365 : Blo 1607002 1808365 := bbase (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) (by norm_num)
theorem B3094517 : Blo 1607002 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B1808401 : Blo 1607002 1808401 := bbase (se 2 (by rfl) ⟨678150, by rfl⟩ : syracuseStep 1808401 = 1356301) (by norm_num)
theorem B3618845 : Blo 1607002 3618845 := bbase (se 3 (by rfl) ⟨678533, by rfl⟩ : syracuseStep 3618845 = 1357067) (by norm_num)
theorem B1808437 : Blo 1607002 1808437 := bbase (se 5 (by rfl) ⟨84770, by rfl⟩ : syracuseStep 1808437 = 169541) (by norm_num)
theorem B3053629 : Blo 1607002 3053629 := bbase (se 3 (by rfl) ⟨572555, by rfl⟩ : syracuseStep 3053629 = 1145111) (by norm_num)
theorem B8697941 : Blo 1607002 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B1808473 : Blo 1607002 1808473 := bbase (se 2 (by rfl) ⟨678177, by rfl⟩ : syracuseStep 1808473 = 1356355) (by norm_num)
theorem B4577381 : Blo 1607002 4577381 := bbase (se 4 (by rfl) ⟨429129, by rfl⟩ : syracuseStep 4577381 = 858259) (by norm_num)
theorem B3618917 : Blo 1607002 3618917 := bbase (se 4 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 3618917 = 678547) (by norm_num)
theorem B3479669 : Blo 1607002 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B1808509 : Blo 1607002 1808509 := bbase (se 3 (by rfl) ⟨339095, by rfl⟩ : syracuseStep 1808509 = 678191) (by norm_num)
theorem B2062477 : Blo 1607002 2062477 := bbase (se 3 (by rfl) ⟨386714, by rfl⟩ : syracuseStep 2062477 = 773429) (by norm_num)
theorem B1808545 : Blo 1607002 1808545 := bbase (se 2 (by rfl) ⟨678204, by rfl⟩ : syracuseStep 1808545 = 1356409) (by norm_num)
theorem B4069541 : Blo 1607002 4069541 := bbase (se 4 (by rfl) ⟨381519, by rfl⟩ : syracuseStep 4069541 = 763039) (by norm_num)
theorem B3618989 : Blo 1607002 3618989 := bbase (se 3 (by rfl) ⟨678560, by rfl⟩ : syracuseStep 3618989 = 1357121) (by norm_num)
theorem B5429429 : Blo 1607002 5429429 := bbase (se 5 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 5429429 = 509009) (by norm_num)
theorem B1808581 : Blo 1607002 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B24762581 : Blo 1607002 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B1808617 : Blo 1607002 1808617 := bbase (se 2 (by rfl) ⟨678231, by rfl⟩ : syracuseStep 1808617 = 1356463) (by norm_num)
theorem B3258613 : Blo 1607002 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B3619061 : Blo 1607002 3619061 := bbase (se 5 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 3619061 = 339287) (by norm_num)
theorem B1808653 : Blo 1607002 1808653 := bbase (se 3 (by rfl) ⟨339122, by rfl⟩ : syracuseStep 1808653 = 678245) (by norm_num)
theorem B4577573 : Blo 1607002 4577573 := bbase (se 4 (by rfl) ⟨429147, by rfl⟩ : syracuseStep 4577573 = 858295) (by norm_num)
theorem B1808689 : Blo 1607002 1808689 := bbase (se 2 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 1808689 = 1356517) (by norm_num)
theorem B3619133 : Blo 1607002 3619133 := bbase (se 3 (by rfl) ⟨678587, by rfl⟩ : syracuseStep 3619133 = 1357175) (by norm_num)
theorem B2898245 : Blo 1607002 2898245 := bbase (se 4 (by rfl) ⟨271710, by rfl⟩ : syracuseStep 2898245 = 543421) (by norm_num)
theorem B1808725 : Blo 1607002 1808725 := bbase (se 10 (by rfl) ⟨2649, by rfl⟩ : syracuseStep 1808725 = 5299) (by norm_num)
theorem B3053933 : Blo 1607002 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B9288053 : Blo 1607002 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B1808761 : Blo 1607002 1808761 := bbase (se 2 (by rfl) ⟨678285, by rfl⟩ : syracuseStep 1808761 = 1356571) (by norm_num)
theorem B1931645 : Blo 1607002 1931645 := bbase (se 3 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 1931645 = 724367) (by norm_num)
theorem B3619205 : Blo 1607002 3619205 := bbase (se 4 (by rfl) ⟨339300, by rfl⟩ : syracuseStep 3619205 = 678601) (by norm_num)
theorem B1808797 : Blo 1607002 1808797 := bbase (se 3 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 1808797 = 678299) (by norm_num)
theorem B1808833 : Blo 1607002 1808833 := bbase (se 2 (by rfl) ⟨678312, by rfl⟩ : syracuseStep 1808833 = 1356625) (by norm_num)
theorem B3619277 : Blo 1607002 3619277 := bbase (se 3 (by rfl) ⟨678614, by rfl⟩ : syracuseStep 3619277 = 1357229) (by norm_num)
theorem B12212693 : Blo 1607002 12212693 := bbase (se 7 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 12212693 = 286235) (by norm_num)
theorem B1808869 : Blo 1607002 1808869 := bbase (se 4 (by rfl) ⟨169581, by rfl⟩ : syracuseStep 1808869 = 339163) (by norm_num)
theorem B5151205 : Blo 1607002 5151205 := bbase (se 4 (by rfl) ⟨482925, by rfl⟩ : syracuseStep 5151205 = 965851) (by norm_num)
theorem B4069885 : Blo 1607002 4069885 := bbase (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) (by norm_num)
theorem B1808905 : Blo 1607002 1808905 := bbase (se 2 (by rfl) ⟨678339, by rfl⟩ : syracuseStep 1808905 = 1356679) (by norm_num)
theorem B3619349 : Blo 1607002 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B1808941 : Blo 1607002 1808941 := bbase (se 3 (by rfl) ⟨339176, by rfl⟩ : syracuseStep 1808941 = 678353) (by norm_num)
theorem B1808977 : Blo 1607002 1808977 := bbase (se 2 (by rfl) ⟨678366, by rfl⟩ : syracuseStep 1808977 = 1356733) (by norm_num)
theorem B3619421 : Blo 1607002 3619421 := bbase (se 3 (by rfl) ⟨678641, by rfl⟩ : syracuseStep 3619421 = 1357283) (by norm_num)
theorem B5429861 : Blo 1607002 5429861 := bbase (se 4 (by rfl) ⟨509049, by rfl⟩ : syracuseStep 5429861 = 1018099) (by norm_num)
theorem B4299365 : Blo 1607002 4299365 := bbase (se 4 (by rfl) ⟨403065, by rfl⟩ : syracuseStep 4299365 = 806131) (by norm_num)
theorem B4069997 : Blo 1607002 4069997 := bbase (se 3 (by rfl) ⟨763124, by rfl⟩ : syracuseStep 4069997 = 1526249) (by norm_num)
theorem B1809013 : Blo 1607002 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B1809049 : Blo 1607002 1809049 := bbase (se 2 (by rfl) ⟨678393, by rfl⟩ : syracuseStep 1809049 = 1356787) (by norm_num)
theorem B6101669 : Blo 1607002 6101669 := bbase (se 4 (by rfl) ⟨572031, by rfl⟩ : syracuseStep 6101669 = 1144063) (by norm_num)
theorem B3619493 : Blo 1607002 3619493 := bbase (se 4 (by rfl) ⟨339327, by rfl⟩ : syracuseStep 3619493 = 678655) (by norm_num)
theorem B1931953 : Blo 1607002 1931953 := bbase (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) (by norm_num)
theorem B1809085 : Blo 1607002 1809085 := bbase (se 3 (by rfl) ⟨339203, by rfl⟩ : syracuseStep 1809085 = 678407) (by norm_num)
theorem B9157333 : Blo 1607002 9157333 := bbase (se 7 (by rfl) ⟨107312, by rfl⟩ : syracuseStep 9157333 = 214625) (by norm_num)
theorem B1809121 : Blo 1607002 1809121 := bbase (se 2 (by rfl) ⟨678420, by rfl⟩ : syracuseStep 1809121 = 1356841) (by norm_num)
theorem B3619565 : Blo 1607002 3619565 := bbase (se 3 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 3619565 = 1357337) (by norm_num)
theorem B1809157 : Blo 1607002 1809157 := bbase (se 4 (by rfl) ⟨169608, by rfl⟩ : syracuseStep 1809157 = 339217) (by norm_num)
theorem B1809193 : Blo 1607002 1809193 := bbase (se 2 (by rfl) ⟨678447, by rfl⟩ : syracuseStep 1809193 = 1356895) (by norm_num)
theorem B4070189 : Blo 1607002 4070189 := bbase (se 3 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 4070189 = 1526321) (by norm_num)
theorem B3619637 : Blo 1607002 3619637 := bbase (se 5 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 3619637 = 339341) (by norm_num)
theorem B1809229 : Blo 1607002 1809229 := bbase (se 3 (by rfl) ⟨339230, by rfl⟩ : syracuseStep 1809229 = 678461) (by norm_num)
theorem B13736789 : Blo 1607002 13736789 := bbase (se 9 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 13736789 = 80489) (by norm_num)
theorem B1932121 : Blo 1607002 1932121 := bbase (se 2 (by rfl) ⟨724545, by rfl⟩ : syracuseStep 1932121 = 1449091) (by norm_num)
theorem B1809265 : Blo 1607002 1809265 := bbase (se 2 (by rfl) ⟨678474, by rfl⟩ : syracuseStep 1809265 = 1356949) (by norm_num)
theorem B12204917 : Blo 1607002 12204917 := bbase (se 5 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 12204917 = 1144211) (by norm_num)
theorem B3619709 : Blo 1607002 3619709 := bbase (se 3 (by rfl) ⟨678695, by rfl⟩ : syracuseStep 3619709 = 1357391) (by norm_num)
theorem B1809301 : Blo 1607002 1809301 := bbase (se 6 (by rfl) ⟨42405, by rfl⟩ : syracuseStep 1809301 = 84811) (by norm_num)
theorem B2751413 : Blo 1607002 2751413 := bbase (se 5 (by rfl) ⟨128972, by rfl⟩ : syracuseStep 2751413 = 257945) (by norm_num)
theorem B1809337 : Blo 1607002 1809337 := bbase (se 2 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 1809337 = 1357003) (by norm_num)
theorem B3619781 : Blo 1607002 3619781 := bbase (se 4 (by rfl) ⟨339354, by rfl⟩ : syracuseStep 3619781 = 678709) (by norm_num)
theorem B1809373 : Blo 1607002 1809373 := bbase (se 3 (by rfl) ⟨339257, by rfl⟩ : syracuseStep 1809373 = 678515) (by norm_num)
theorem B4889573 : Blo 1607002 4889573 := bbase (se 4 (by rfl) ⟨458397, by rfl⟩ : syracuseStep 4889573 = 916795) (by norm_num)
theorem B1809409 : Blo 1607002 1809409 := bbase (se 2 (by rfl) ⟨678528, by rfl⟩ : syracuseStep 1809409 = 1357057) (by norm_num)
theorem B3619853 : Blo 1607002 3619853 := bbase (se 3 (by rfl) ⟨678722, by rfl⟩ : syracuseStep 3619853 = 1357445) (by norm_num)
theorem B5430293 : Blo 1607002 5430293 := bbase (se 6 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 5430293 = 254545) (by norm_num)
theorem B1932317 : Blo 1607002 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B1809445 : Blo 1607002 1809445 := bbase (se 4 (by rfl) ⟨169635, by rfl⟩ : syracuseStep 1809445 = 339271) (by norm_num)
theorem B1809481 : Blo 1607002 1809481 := bbase (se 2 (by rfl) ⟨678555, by rfl⟩ : syracuseStep 1809481 = 1357111) (by norm_num)
theorem B3619925 : Blo 1607002 3619925 := bbase (se 8 (by rfl) ⟨21210, by rfl⟩ : syracuseStep 3619925 = 42421) (by norm_num)
theorem B1809517 : Blo 1607002 1809517 := bbase (se 3 (by rfl) ⟨339284, by rfl⟩ : syracuseStep 1809517 = 678569) (by norm_num)
theorem B4070533 : Blo 1607002 4070533 := bbase (se 4 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 4070533 = 763225) (by norm_num)
theorem B8141957 : Blo 1607002 8141957 := bbase (se 4 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 8141957 = 1526617) (by norm_num)
theorem B1809553 : Blo 1607002 1809553 := bbase (se 2 (by rfl) ⟨678582, by rfl⟩ : syracuseStep 1809553 = 1357165) (by norm_num)
theorem B3619997 : Blo 1607002 3619997 := bbase (se 3 (by rfl) ⟨678749, by rfl⟩ : syracuseStep 3619997 = 1357499) (by norm_num)
theorem B1809589 : Blo 1607002 1809589 := bbase (se 5 (by rfl) ⟨84824, by rfl⟩ : syracuseStep 1809589 = 169649) (by norm_num)
theorem B1809625 : Blo 1607002 1809625 := bbase (se 2 (by rfl) ⟨678609, by rfl⟩ : syracuseStep 1809625 = 1357219) (by norm_num)
theorem B3620069 : Blo 1607002 3620069 := bbase (se 4 (by rfl) ⟨339381, by rfl⟩ : syracuseStep 3620069 = 678763) (by norm_num)
theorem B4070645 : Blo 1607002 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B1809661 : Blo 1607002 1809661 := bbase (se 3 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 1809661 = 678623) (by norm_num)
theorem B4578565 : Blo 1607002 4578565 := bbase (se 4 (by rfl) ⟨429240, by rfl⟩ : syracuseStep 4578565 = 858481) (by norm_num)
theorem B1809697 : Blo 1607002 1809697 := bbase (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) (by norm_num)
theorem B3620141 : Blo 1607002 3620141 := bbase (se 3 (by rfl) ⟨678776, by rfl⟩ : syracuseStep 3620141 = 1357553) (by norm_num)
theorem B1809733 : Blo 1607002 1809733 := bbase (se 4 (by rfl) ⟨169662, by rfl⟩ : syracuseStep 1809733 = 339325) (by norm_num)
theorem B1834321 : Blo 1607002 1834321 := bbase (se 2 (by rfl) ⟨687870, by rfl⟩ : syracuseStep 1834321 = 1375741) (by norm_num)
theorem B2063713 : Blo 1607002 2063713 := bbase (se 2 (by rfl) ⟨773892, by rfl⟩ : syracuseStep 2063713 = 1547785) (by norm_num)
theorem B1809769 : Blo 1607002 1809769 := bbase (se 2 (by rfl) ⟨678663, by rfl⟩ : syracuseStep 1809769 = 1357327) (by norm_num)
theorem B3620213 : Blo 1607002 3620213 := bbase (se 5 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 3620213 = 339395) (by norm_num)
theorem B1809805 : Blo 1607002 1809805 := bbase (se 3 (by rfl) ⟨339338, by rfl⟩ : syracuseStep 1809805 = 678677) (by norm_num)
theorem B1809841 : Blo 1607002 1809841 := bbase (se 2 (by rfl) ⟨678690, by rfl⟩ : syracuseStep 1809841 = 1357381) (by norm_num)
theorem B4070837 : Blo 1607002 4070837 := bbase (se 5 (by rfl) ⟨190820, by rfl⟩ : syracuseStep 4070837 = 381641) (by norm_num)
theorem B1809877 : Blo 1607002 1809877 := bbase (se 7 (by rfl) ⟨21209, by rfl⟩ : syracuseStep 1809877 = 42419) (by norm_num)
theorem B1809913 : Blo 1607002 1809913 := bbase (se 2 (by rfl) ⟨678717, by rfl⟩ : syracuseStep 1809913 = 1357435) (by norm_num)
theorem B1809949 : Blo 1607002 1809949 := bbase (se 3 (by rfl) ⟨339365, by rfl⟩ : syracuseStep 1809949 = 678731) (by norm_num)
theorem B1809985 : Blo 1607002 1809985 := bbase (se 2 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 1809985 = 1357489) (by norm_num)
theorem B1629785 : Blo 1607002 1629785 := bbase (se 2 (by rfl) ⟨611169, by rfl⟩ : syracuseStep 1629785 = 1222339) (by norm_num)
theorem B1810021 : Blo 1607002 1810021 := bbase (se 4 (by rfl) ⟨169689, by rfl⟩ : syracuseStep 1810021 = 339379) (by norm_num)
theorem B1810057 : Blo 1607002 1810057 := bbase (se 2 (by rfl) ⟨678771, by rfl⟩ : syracuseStep 1810057 = 1357543) (by norm_num)
theorem B1810093 : Blo 1607002 1810093 := bbase (se 3 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 1810093 = 678785) (by norm_num)
theorem B2752213 : Blo 1607002 2752213 := bbase (se 7 (by rfl) ⟨32252, by rfl⟩ : syracuseStep 2752213 = 64505) (by norm_num)
theorem B4071181 : Blo 1607002 4071181 := bbase (se 3 (by rfl) ⟨763346, by rfl⟩ : syracuseStep 4071181 = 1526693) (by norm_num)
theorem B5152565 : Blo 1607002 5152565 := bbase (se 5 (by rfl) ⟨241526, by rfl⟩ : syracuseStep 5152565 = 483053) (by norm_num)
theorem B4071293 : Blo 1607002 4071293 := bbase (se 3 (by rfl) ⟨763367, by rfl⟩ : syracuseStep 4071293 = 1526735) (by norm_num)
theorem B1630133 : Blo 1607002 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B5152693 : Blo 1607002 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B5152835 : Blo 1607002 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B4071505 : Blo 1607002 4071505 := bstep (se 2 (by rfl) ⟨1526814, by rfl⟩ : syracuseStep 4071505 = 3053629) B3053629
theorem B6103309 : Blo 1607002 6103309 := bstep (se 3 (by rfl) ⟨1144370, by rfl⟩ : syracuseStep 6103309 = 2288741) B2288741
theorem B20611381 : Blo 1607002 20611381 := bstep (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) B1932317
theorem B2711873 : Blo 1607002 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B4071779 : Blo 1607002 4071779 := bstep (se 1 (by rfl) ⟨3053834, by rfl⟩ : syracuseStep 4071779 = 6107669) B6107669
theorem B4579715 : Blo 1607002 4579715 := bstep (se 1 (by rfl) ⟨3434786, by rfl⟩ : syracuseStep 4579715 = 6869573) B6869573
theorem B2712001 : Blo 1607002 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B2712035 : Blo 1607002 2712035 := bstep (se 1 (by rfl) ⟨2034026, by rfl⟩ : syracuseStep 2712035 = 4068053) B4068053
theorem B11583985 : Blo 1607002 11583985 := bstep (se 2 (by rfl) ⟨4343994, by rfl⟩ : syracuseStep 11583985 = 8687989) B8687989
theorem B5423651 : Blo 1607002 5423651 := bstep (se 1 (by rfl) ⟨4067738, by rfl⟩ : syracuseStep 5423651 = 8135477) B8135477
theorem B4071971 : Blo 1607002 4071971 := bstep (se 1 (by rfl) ⟨3053978, by rfl⟩ : syracuseStep 4071971 = 6107957) B6107957
theorem B2712163 : Blo 1607002 2712163 := bstep (se 1 (by rfl) ⟨2034122, by rfl⟩ : syracuseStep 2712163 = 4068245) B4068245
theorem B1909459 : Blo 1607002 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B2712305 : Blo 1607002 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B12206861 : Blo 1607002 12206861 := bstep (se 3 (by rfl) ⟨2288786, by rfl⟩ : syracuseStep 12206861 = 4577573) B4577573
theorem B5423921 : Blo 1607002 5423921 := bstep (se 2 (by rfl) ⟨2033970, by rfl⟩ : syracuseStep 5423921 = 4067941) B4067941
theorem B3433283 : Blo 1607002 3433283 := bstep (se 1 (by rfl) ⟨2574962, by rfl⟩ : syracuseStep 3433283 = 5149925) B5149925
theorem B2712433 : Blo 1607002 2712433 := bstep (se 2 (by rfl) ⟨1017162, by rfl⟩ : syracuseStep 2712433 = 2034325) B2034325
theorem B2712467 : Blo 1607002 2712467 := bstep (se 1 (by rfl) ⟨2034350, by rfl⟩ : syracuseStep 2712467 = 4068701) B4068701
theorem B2712595 : Blo 1607002 2712595 := bstep (se 1 (by rfl) ⟨2034446, by rfl⟩ : syracuseStep 2712595 = 4068893) B4068893
theorem B6104099 : Blo 1607002 6104099 := bstep (se 1 (by rfl) ⟨4578074, by rfl⟩ : syracuseStep 6104099 = 9156149) B9156149
theorem B9159749 : Blo 1607002 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B7726193 : Blo 1607002 7726193 := bstep (se 2 (by rfl) ⟨2897322, by rfl⟩ : syracuseStep 7726193 = 5794645) B5794645
theorem B2712737 : Blo 1607002 2712737 := bstep (se 2 (by rfl) ⟨1017276, by rfl⟩ : syracuseStep 2712737 = 2034553) B2034553
theorem B2319553 : Blo 1607002 2319553 := bstep (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) B1739665
theorem B3433745 : Blo 1607002 3433745 := bstep (se 2 (by rfl) ⟨1287654, by rfl⟩ : syracuseStep 3433745 = 2575309) B2575309
theorem B2712865 : Blo 1607002 2712865 := bstep (se 2 (by rfl) ⟨1017324, by rfl⟩ : syracuseStep 2712865 = 2034649) B2034649
theorem B2712899 : Blo 1607002 2712899 := bstep (se 1 (by rfl) ⟨2034674, by rfl⟩ : syracuseStep 2712899 = 4069349) B4069349
theorem B5424461 : Blo 1607002 5424461 := bstep (se 3 (by rfl) ⟨1017086, by rfl⟩ : syracuseStep 5424461 = 2034173) B2034173
theorem B1607011 : Blo 1607002 1607011 := bstep (se 1 (by rfl) ⟨1205258, by rfl⟩ : syracuseStep 1607011 = 2410517) B2410517
theorem B1607027 : Blo 1607002 1607027 := bstep (se 1 (by rfl) ⟨1205270, by rfl⟩ : syracuseStep 1607027 = 2410541) B2410541
theorem B1607043 : Blo 1607002 1607043 := bstep (se 1 (by rfl) ⟨1205282, by rfl⟩ : syracuseStep 1607043 = 2410565) B2410565
theorem B5424515 : Blo 1607002 5424515 := bstep (se 1 (by rfl) ⟨4068386, by rfl⟩ : syracuseStep 5424515 = 8136773) B8136773
theorem B1607059 : Blo 1607002 1607059 := bstep (se 1 (by rfl) ⟨1205294, by rfl⟩ : syracuseStep 1607059 = 2410589) B2410589
theorem B1607075 : Blo 1607002 1607075 := bstep (se 1 (by rfl) ⟨1205306, by rfl⟩ : syracuseStep 1607075 = 2410613) B2410613
theorem B2319779 : Blo 1607002 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B1607091 : Blo 1607002 1607091 := bstep (se 1 (by rfl) ⟨1205318, by rfl⟩ : syracuseStep 1607091 = 2410637) B2410637
theorem B1607107 : Blo 1607002 1607107 := bstep (se 1 (by rfl) ⟨1205330, by rfl⟩ : syracuseStep 1607107 = 2410661) B2410661
theorem B2713027 : Blo 1607002 2713027 := bstep (se 1 (by rfl) ⟨2034770, by rfl⟩ : syracuseStep 2713027 = 4069541) B4069541
theorem B1607123 : Blo 1607002 1607123 := bstep (se 1 (by rfl) ⟨1205342, by rfl⟩ : syracuseStep 1607123 = 2410685) B2410685
theorem B1607139 : Blo 1607002 1607139 := bstep (se 1 (by rfl) ⟨1205354, by rfl⟩ : syracuseStep 1607139 = 2410709) B2410709
theorem B16508387 : Blo 1607002 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B1607155 : Blo 1607002 1607155 := bstep (se 1 (by rfl) ⟨1205366, by rfl⟩ : syracuseStep 1607155 = 2410733) B2410733
theorem B1607171 : Blo 1607002 1607171 := bstep (se 1 (by rfl) ⟨1205378, by rfl⟩ : syracuseStep 1607171 = 2410757) B2410757
theorem B1607187 : Blo 1607002 1607187 := bstep (se 1 (by rfl) ⟨1205390, by rfl⟩ : syracuseStep 1607187 = 2410781) B2410781
theorem B1607203 : Blo 1607002 1607203 := bstep (se 1 (by rfl) ⟨1205402, by rfl⟩ : syracuseStep 1607203 = 2410805) B2410805
theorem B1607219 : Blo 1607002 1607219 := bstep (se 1 (by rfl) ⟨1205414, by rfl⟩ : syracuseStep 1607219 = 2410829) B2410829
theorem B1607235 : Blo 1607002 1607235 := bstep (se 1 (by rfl) ⟨1205426, by rfl⟩ : syracuseStep 1607235 = 2410853) B2410853
theorem B2713169 : Blo 1607002 2713169 := bstep (se 2 (by rfl) ⟨1017438, by rfl⟩ : syracuseStep 2713169 = 2034877) B2034877
theorem B4580945 : Blo 1607002 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B1607251 : Blo 1607002 1607251 := bstep (se 1 (by rfl) ⟨1205438, by rfl⟩ : syracuseStep 1607251 = 2410877) B2410877
theorem B1607267 : Blo 1607002 1607267 := bstep (se 1 (by rfl) ⟨1205450, by rfl⟩ : syracuseStep 1607267 = 2410901) B2410901
theorem B1607283 : Blo 1607002 1607283 := bstep (se 1 (by rfl) ⟨1205462, by rfl⟩ : syracuseStep 1607283 = 2410925) B2410925
theorem B1607299 : Blo 1607002 1607299 := bstep (se 1 (by rfl) ⟨1205474, by rfl⟩ : syracuseStep 1607299 = 2410949) B2410949
theorem B5424785 : Blo 1607002 5424785 := bstep (se 2 (by rfl) ⟨2034294, by rfl⟩ : syracuseStep 5424785 = 4068589) B4068589
theorem B1607315 : Blo 1607002 1607315 := bstep (se 1 (by rfl) ⟨1205486, by rfl⟩ : syracuseStep 1607315 = 2410973) B2410973
theorem B1607331 : Blo 1607002 1607331 := bstep (se 1 (by rfl) ⟨1205498, by rfl⟩ : syracuseStep 1607331 = 2410997) B2410997
theorem B6104753 : Blo 1607002 6104753 := bstep (se 2 (by rfl) ⟨2289282, by rfl⟩ : syracuseStep 6104753 = 4578565) B4578565
theorem B1607347 : Blo 1607002 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B6522545 : Blo 1607002 6522545 := bstep (se 2 (by rfl) ⟨2445954, by rfl⟩ : syracuseStep 6522545 = 4891909) B4891909
theorem B1607363 : Blo 1607002 1607363 := bstep (se 1 (by rfl) ⟨1205522, by rfl⟩ : syracuseStep 1607363 = 2411045) B2411045
theorem B2713297 : Blo 1607002 2713297 := bstep (se 2 (by rfl) ⟨1017486, by rfl⟩ : syracuseStep 2713297 = 2034973) B2034973
theorem B1607379 : Blo 1607002 1607379 := bstep (se 1 (by rfl) ⟨1205534, by rfl⟩ : syracuseStep 1607379 = 2411069) B2411069
theorem B1607395 : Blo 1607002 1607395 := bstep (se 1 (by rfl) ⟨1205546, by rfl⟩ : syracuseStep 1607395 = 2411093) B2411093
theorem B1607411 : Blo 1607002 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B2713331 : Blo 1607002 2713331 := bstep (se 1 (by rfl) ⟨2034998, by rfl⟩ : syracuseStep 2713331 = 4069997) B4069997
theorem B1607427 : Blo 1607002 1607427 := bstep (se 1 (by rfl) ⟨1205570, by rfl⟩ : syracuseStep 1607427 = 2411141) B2411141
theorem B1607443 : Blo 1607002 1607443 := bstep (se 1 (by rfl) ⟨1205582, by rfl⟩ : syracuseStep 1607443 = 2411165) B2411165
theorem B1607459 : Blo 1607002 1607459 := bstep (se 1 (by rfl) ⟨1205594, by rfl⟩ : syracuseStep 1607459 = 2411189) B2411189
theorem B1607475 : Blo 1607002 1607475 := bstep (se 1 (by rfl) ⟨1205606, by rfl⟩ : syracuseStep 1607475 = 2411213) B2411213
theorem B1607491 : Blo 1607002 1607491 := bstep (se 1 (by rfl) ⟨1205618, by rfl⟩ : syracuseStep 1607491 = 2411237) B2411237
theorem B1607507 : Blo 1607002 1607507 := bstep (se 1 (by rfl) ⟨1205630, by rfl⟩ : syracuseStep 1607507 = 2411261) B2411261
theorem B1607523 : Blo 1607002 1607523 := bstep (se 1 (by rfl) ⟨1205642, by rfl⟩ : syracuseStep 1607523 = 2411285) B2411285
theorem B1607539 : Blo 1607002 1607539 := bstep (se 1 (by rfl) ⟨1205654, by rfl⟩ : syracuseStep 1607539 = 2411309) B2411309
theorem B2713459 : Blo 1607002 2713459 := bstep (se 1 (by rfl) ⟨2035094, by rfl⟩ : syracuseStep 2713459 = 4070189) B4070189
theorem B1607555 : Blo 1607002 1607555 := bstep (se 1 (by rfl) ⟨1205666, by rfl⟩ : syracuseStep 1607555 = 2411333) B2411333
theorem B15452045 : Blo 1607002 15452045 := bstep (se 3 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 15452045 = 5794517) B5794517
theorem B39118733 : Blo 1607002 39118733 := bstep (se 3 (by rfl) ⟨7334762, by rfl⟩ : syracuseStep 39118733 = 14669525) B14669525
theorem B1607571 : Blo 1607002 1607571 := bstep (se 1 (by rfl) ⟨1205678, by rfl⟩ : syracuseStep 1607571 = 2411357) B2411357
theorem B8136611 : Blo 1607002 8136611 := bstep (se 1 (by rfl) ⟨6102458, by rfl⟩ : syracuseStep 8136611 = 12204917) B12204917
theorem B1607587 : Blo 1607002 1607587 := bstep (se 1 (by rfl) ⟨1205690, by rfl⟩ : syracuseStep 1607587 = 2411381) B2411381
theorem B1607603 : Blo 1607002 1607603 := bstep (se 1 (by rfl) ⟨1205702, by rfl⟩ : syracuseStep 1607603 = 2411405) B2411405
theorem B1607619 : Blo 1607002 1607619 := bstep (se 1 (by rfl) ⟨1205714, by rfl⟩ : syracuseStep 1607619 = 2411429) B2411429
theorem B1607635 : Blo 1607002 1607635 := bstep (se 1 (by rfl) ⟨1205726, by rfl⟩ : syracuseStep 1607635 = 2411453) B2411453
theorem B1607651 : Blo 1607002 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B1607667 : Blo 1607002 1607667 := bstep (se 1 (by rfl) ⟨1205750, by rfl⟩ : syracuseStep 1607667 = 2411501) B2411501
theorem B2713601 : Blo 1607002 2713601 := bstep (se 2 (by rfl) ⟨1017600, by rfl⟩ : syracuseStep 2713601 = 2035201) B2035201
theorem B1607683 : Blo 1607002 1607683 := bstep (se 1 (by rfl) ⟨1205762, by rfl⟩ : syracuseStep 1607683 = 2411525) B2411525
theorem B1607699 : Blo 1607002 1607699 := bstep (se 1 (by rfl) ⟨1205774, by rfl⟩ : syracuseStep 1607699 = 2411549) B2411549
theorem B2410529 : Blo 1607002 2410529 := bstep (se 2 (by rfl) ⟨903948, by rfl⟩ : syracuseStep 2410529 = 1807897) B1807897
theorem B1607715 : Blo 1607002 1607715 := bstep (se 1 (by rfl) ⟨1205786, by rfl⟩ : syracuseStep 1607715 = 2411573) B2411573
theorem B2410547 : Blo 1607002 2410547 := bstep (se 1 (by rfl) ⟨1807910, by rfl⟩ : syracuseStep 2410547 = 3615821) B3615821
theorem B1607731 : Blo 1607002 1607731 := bstep (se 1 (by rfl) ⟨1205798, by rfl⟩ : syracuseStep 1607731 = 2411597) B2411597
theorem B1607747 : Blo 1607002 1607747 := bstep (se 1 (by rfl) ⟨1205810, by rfl⟩ : syracuseStep 1607747 = 2411621) B2411621
theorem B13740101 : Blo 1607002 13740101 := bstep (se 4 (by rfl) ⟨1288134, by rfl⟩ : syracuseStep 13740101 = 2576269) B2576269
theorem B5793869 : Blo 1607002 5793869 := bstep (se 3 (by rfl) ⟨1086350, by rfl⟩ : syracuseStep 5793869 = 2172701) B2172701
theorem B2410577 : Blo 1607002 2410577 := bstep (se 2 (by rfl) ⟨903966, by rfl⟩ : syracuseStep 2410577 = 1807933) B1807933
theorem B1607763 : Blo 1607002 1607763 := bstep (se 1 (by rfl) ⟨1205822, by rfl⟩ : syracuseStep 1607763 = 2411645) B2411645
theorem B2410595 : Blo 1607002 2410595 := bstep (se 1 (by rfl) ⟨1807946, by rfl⟩ : syracuseStep 2410595 = 3615893) B3615893
theorem B1607779 : Blo 1607002 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B16509041 : Blo 1607002 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B1607795 : Blo 1607002 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B2410625 : Blo 1607002 2410625 := bstep (se 2 (by rfl) ⟨903984, by rfl⟩ : syracuseStep 2410625 = 1807969) B1807969
theorem B2713729 : Blo 1607002 2713729 := bstep (se 2 (by rfl) ⟨1017648, by rfl⟩ : syracuseStep 2713729 = 2035297) B2035297
theorem B1607811 : Blo 1607002 1607811 := bstep (se 1 (by rfl) ⟨1205858, by rfl⟩ : syracuseStep 1607811 = 2411717) B2411717
theorem B2410643 : Blo 1607002 2410643 := bstep (se 1 (by rfl) ⟨1807982, by rfl⟩ : syracuseStep 2410643 = 3615965) B3615965
theorem B1607827 : Blo 1607002 1607827 := bstep (se 1 (by rfl) ⟨1205870, by rfl⟩ : syracuseStep 1607827 = 2411741) B2411741
theorem B1607843 : Blo 1607002 1607843 := bstep (se 1 (by rfl) ⟨1205882, by rfl⟩ : syracuseStep 1607843 = 2411765) B2411765
theorem B2713763 : Blo 1607002 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B5425325 : Blo 1607002 5425325 := bstep (se 3 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 5425325 = 2034497) B2034497
theorem B2410673 : Blo 1607002 2410673 := bstep (se 2 (by rfl) ⟨904002, by rfl⟩ : syracuseStep 2410673 = 1808005) B1808005
theorem B1607859 : Blo 1607002 1607859 := bstep (se 1 (by rfl) ⟨1205894, by rfl⟩ : syracuseStep 1607859 = 2411789) B2411789
theorem B2410691 : Blo 1607002 2410691 := bstep (se 1 (by rfl) ⟨1808018, by rfl⟩ : syracuseStep 2410691 = 3616037) B3616037
theorem B1607875 : Blo 1607002 1607875 := bstep (se 1 (by rfl) ⟨1205906, by rfl⟩ : syracuseStep 1607875 = 2411813) B2411813
theorem B13732037 : Blo 1607002 13732037 := bstep (se 4 (by rfl) ⟨1287378, by rfl⟩ : syracuseStep 13732037 = 2574757) B2574757
theorem B7727309 : Blo 1607002 7727309 := bstep (se 3 (by rfl) ⟨1448870, by rfl⟩ : syracuseStep 7727309 = 2897741) B2897741
theorem B1607891 : Blo 1607002 1607891 := bstep (se 1 (by rfl) ⟨1205918, by rfl⟩ : syracuseStep 1607891 = 2411837) B2411837
theorem B69552341 : Blo 1607002 69552341 := bstep (se 7 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 69552341 = 1630133) B1630133
theorem B2410721 : Blo 1607002 2410721 := bstep (se 2 (by rfl) ⟨904020, by rfl⟩ : syracuseStep 2410721 = 1808041) B1808041
theorem B5425379 : Blo 1607002 5425379 := bstep (se 1 (by rfl) ⟨4069034, by rfl⟩ : syracuseStep 5425379 = 8138069) B8138069
theorem B1607907 : Blo 1607002 1607907 := bstep (se 1 (by rfl) ⟨1205930, by rfl⟩ : syracuseStep 1607907 = 2411861) B2411861
theorem B2410739 : Blo 1607002 2410739 := bstep (se 1 (by rfl) ⟨1808054, by rfl⟩ : syracuseStep 2410739 = 3616109) B3616109
theorem B1607923 : Blo 1607002 1607923 := bstep (se 1 (by rfl) ⟨1205942, by rfl⟩ : syracuseStep 1607923 = 2411885) B2411885
theorem B1607939 : Blo 1607002 1607939 := bstep (se 1 (by rfl) ⟨1205954, by rfl⟩ : syracuseStep 1607939 = 2411909) B2411909
theorem B11004173 : Blo 1607002 11004173 := bstep (se 3 (by rfl) ⟨2063282, by rfl⟩ : syracuseStep 11004173 = 4126565) B4126565
theorem B2410769 : Blo 1607002 2410769 := bstep (se 2 (by rfl) ⟨904038, by rfl⟩ : syracuseStep 2410769 = 1808077) B1808077
theorem B1607955 : Blo 1607002 1607955 := bstep (se 1 (by rfl) ⟨1205966, by rfl⟩ : syracuseStep 1607955 = 2411933) B2411933
theorem B2410787 : Blo 1607002 2410787 := bstep (se 1 (by rfl) ⟨1808090, by rfl⟩ : syracuseStep 2410787 = 3616181) B3616181
theorem B1607971 : Blo 1607002 1607971 := bstep (se 1 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 1607971 = 2411957) B2411957
theorem B2713891 : Blo 1607002 2713891 := bstep (se 1 (by rfl) ⟨2035418, by rfl⟩ : syracuseStep 2713891 = 4070837) B4070837
theorem B1607987 : Blo 1607002 1607987 := bstep (se 1 (by rfl) ⟨1205990, by rfl⟩ : syracuseStep 1607987 = 2411981) B2411981
theorem B2410817 : Blo 1607002 2410817 := bstep (se 2 (by rfl) ⟨904056, by rfl⟩ : syracuseStep 2410817 = 1808113) B1808113
theorem B1608003 : Blo 1607002 1608003 := bstep (se 1 (by rfl) ⟨1206002, by rfl⟩ : syracuseStep 1608003 = 2412005) B2412005
theorem B2410835 : Blo 1607002 2410835 := bstep (se 1 (by rfl) ⟨1808126, by rfl⟩ : syracuseStep 2410835 = 3616253) B3616253
theorem B1608019 : Blo 1607002 1608019 := bstep (se 1 (by rfl) ⟨1206014, by rfl⟩ : syracuseStep 1608019 = 2412029) B2412029
theorem B1608035 : Blo 1607002 1608035 := bstep (se 1 (by rfl) ⟨1206026, by rfl⟩ : syracuseStep 1608035 = 2412053) B2412053
theorem B2410865 : Blo 1607002 2410865 := bstep (se 2 (by rfl) ⟨904074, by rfl⟩ : syracuseStep 2410865 = 1808149) B1808149
theorem B1608051 : Blo 1607002 1608051 := bstep (se 1 (by rfl) ⟨1206038, by rfl⟩ : syracuseStep 1608051 = 2412077) B2412077
theorem B2410883 : Blo 1607002 2410883 := bstep (se 1 (by rfl) ⟨1808162, by rfl⟩ : syracuseStep 2410883 = 3616325) B3616325
theorem B1608067 : Blo 1607002 1608067 := bstep (se 1 (by rfl) ⟨1206050, by rfl⟩ : syracuseStep 1608067 = 2412101) B2412101
theorem B2034067 : Blo 1607002 2034067 := bstep (se 1 (by rfl) ⟨1525550, by rfl⟩ : syracuseStep 2034067 = 3051101) B3051101
theorem B1608083 : Blo 1607002 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B2410913 : Blo 1607002 2410913 := bstep (se 2 (by rfl) ⟨904092, by rfl⟩ : syracuseStep 2410913 = 1808185) B1808185
theorem B1608099 : Blo 1607002 1608099 := bstep (se 1 (by rfl) ⟨1206074, by rfl⟩ : syracuseStep 1608099 = 2412149) B2412149
theorem B2714033 : Blo 1607002 2714033 := bstep (se 2 (by rfl) ⟨1017762, by rfl⟩ : syracuseStep 2714033 = 2035525) B2035525
theorem B2410931 : Blo 1607002 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B1608115 : Blo 1607002 1608115 := bstep (se 1 (by rfl) ⟨1206086, by rfl⟩ : syracuseStep 1608115 = 2412173) B2412173
theorem B1608131 : Blo 1607002 1608131 := bstep (se 1 (by rfl) ⟨1206098, by rfl⟩ : syracuseStep 1608131 = 2412197) B2412197
theorem B2410961 : Blo 1607002 2410961 := bstep (se 2 (by rfl) ⟨904110, by rfl⟩ : syracuseStep 2410961 = 1808221) B1808221
theorem B1608147 : Blo 1607002 1608147 := bstep (se 1 (by rfl) ⟨1206110, by rfl⟩ : syracuseStep 1608147 = 2412221) B2412221
theorem B2410979 : Blo 1607002 2410979 := bstep (se 1 (by rfl) ⟨1808234, by rfl⟩ : syracuseStep 2410979 = 3616469) B3616469
theorem B1608163 : Blo 1607002 1608163 := bstep (se 1 (by rfl) ⟨1206122, by rfl⟩ : syracuseStep 1608163 = 2412245) B2412245
theorem B5425649 : Blo 1607002 5425649 := bstep (se 2 (by rfl) ⟨2034618, by rfl⟩ : syracuseStep 5425649 = 4069237) B4069237
theorem B2034163 : Blo 1607002 2034163 := bstep (se 1 (by rfl) ⟨1525622, by rfl⟩ : syracuseStep 2034163 = 3051245) B3051245
theorem B1608179 : Blo 1607002 1608179 := bstep (se 1 (by rfl) ⟨1206134, by rfl⟩ : syracuseStep 1608179 = 2412269) B2412269
theorem B2411009 : Blo 1607002 2411009 := bstep (se 2 (by rfl) ⟨904128, by rfl⟩ : syracuseStep 2411009 = 1808257) B1808257
theorem B1608195 : Blo 1607002 1608195 := bstep (se 1 (by rfl) ⟨1206146, by rfl⟩ : syracuseStep 1608195 = 2412293) B2412293
theorem B2411027 : Blo 1607002 2411027 := bstep (se 1 (by rfl) ⟨1808270, by rfl⟩ : syracuseStep 2411027 = 3616541) B3616541
theorem B1608211 : Blo 1607002 1608211 := bstep (se 1 (by rfl) ⟨1206158, by rfl⟩ : syracuseStep 1608211 = 2412317) B2412317
theorem B1608227 : Blo 1607002 1608227 := bstep (se 1 (by rfl) ⟨1206170, by rfl⟩ : syracuseStep 1608227 = 2412341) B2412341
theorem B3435043 : Blo 1607002 3435043 := bstep (se 1 (by rfl) ⟨2576282, by rfl⟩ : syracuseStep 3435043 = 5152565) B5152565
theorem B2411057 : Blo 1607002 2411057 := bstep (se 2 (by rfl) ⟨904146, by rfl⟩ : syracuseStep 2411057 = 1808293) B1808293
theorem B2714161 : Blo 1607002 2714161 := bstep (se 2 (by rfl) ⟨1017810, by rfl⟩ : syracuseStep 2714161 = 2035621) B2035621
theorem B2574899 : Blo 1607002 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B1608243 : Blo 1607002 1608243 := bstep (se 1 (by rfl) ⟨1206182, by rfl⟩ : syracuseStep 1608243 = 2412365) B2412365
theorem B2411075 : Blo 1607002 2411075 := bstep (se 1 (by rfl) ⟨1808306, by rfl⟩ : syracuseStep 2411075 = 3616613) B3616613
theorem B1608259 : Blo 1607002 1608259 := bstep (se 1 (by rfl) ⟨1206194, by rfl⟩ : syracuseStep 1608259 = 2412389) B2412389
theorem B2574931 : Blo 1607002 2574931 := bstep (se 1 (by rfl) ⟨1931198, by rfl⟩ : syracuseStep 2574931 = 3862397) B3862397
theorem B1608275 : Blo 1607002 1608275 := bstep (se 1 (by rfl) ⟨1206206, by rfl⟩ : syracuseStep 1608275 = 2412413) B2412413
theorem B2714195 : Blo 1607002 2714195 := bstep (se 1 (by rfl) ⟨2035646, by rfl⟩ : syracuseStep 2714195 = 4071293) B4071293
theorem B2411105 : Blo 1607002 2411105 := bstep (se 2 (by rfl) ⟨904164, by rfl⟩ : syracuseStep 2411105 = 1808329) B1808329
theorem B1608291 : Blo 1607002 1608291 := bstep (se 1 (by rfl) ⟨1206218, by rfl⟩ : syracuseStep 1608291 = 2412437) B2412437
theorem B8145521 : Blo 1607002 8145521 := bstep (se 2 (by rfl) ⟨3054570, by rfl⟩ : syracuseStep 8145521 = 6109141) B6109141
theorem B2411123 : Blo 1607002 2411123 := bstep (se 1 (by rfl) ⟨1808342, by rfl⟩ : syracuseStep 2411123 = 3616685) B3616685
theorem B1608307 : Blo 1607002 1608307 := bstep (se 1 (by rfl) ⟨1206230, by rfl⟩ : syracuseStep 1608307 = 2412461) B2412461
theorem B1608323 : Blo 1607002 1608323 := bstep (se 1 (by rfl) ⟨1206242, by rfl⟩ : syracuseStep 1608323 = 2412485) B2412485
theorem B2411153 : Blo 1607002 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B1608339 : Blo 1607002 1608339 := bstep (se 1 (by rfl) ⟨1206254, by rfl⟩ : syracuseStep 1608339 = 2412509) B2412509
theorem B2411171 : Blo 1607002 2411171 := bstep (se 1 (by rfl) ⟨1808378, by rfl⟩ : syracuseStep 2411171 = 3616757) B3616757
theorem B1608355 : Blo 1607002 1608355 := bstep (se 1 (by rfl) ⟨1206266, by rfl⟩ : syracuseStep 1608355 = 2412533) B2412533
theorem B1608371 : Blo 1607002 1608371 := bstep (se 1 (by rfl) ⟨1206278, by rfl⟩ : syracuseStep 1608371 = 2412557) B2412557
theorem B2411201 : Blo 1607002 2411201 := bstep (se 2 (by rfl) ⟨904200, by rfl⟩ : syracuseStep 2411201 = 1808401) B1808401
theorem B1608387 : Blo 1607002 1608387 := bstep (se 1 (by rfl) ⟨1206290, by rfl⟩ : syracuseStep 1608387 = 2412581) B2412581
theorem B8137421 : Blo 1607002 8137421 := bstep (se 3 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 8137421 = 3051533) B3051533
theorem B2411219 : Blo 1607002 2411219 := bstep (se 1 (by rfl) ⟨1808414, by rfl⟩ : syracuseStep 2411219 = 3616829) B3616829
theorem B1608403 : Blo 1607002 1608403 := bstep (se 1 (by rfl) ⟨1206302, by rfl⟩ : syracuseStep 1608403 = 2412605) B2412605
theorem B2714323 : Blo 1607002 2714323 := bstep (se 1 (by rfl) ⟨2035742, by rfl⟩ : syracuseStep 2714323 = 4071485) B4071485
theorem B1608419 : Blo 1607002 1608419 := bstep (se 1 (by rfl) ⟨1206314, by rfl⟩ : syracuseStep 1608419 = 2412629) B2412629
theorem B2411249 : Blo 1607002 2411249 := bstep (se 2 (by rfl) ⟨904218, by rfl⟩ : syracuseStep 2411249 = 1808437) B1808437
theorem B13740785 : Blo 1607002 13740785 := bstep (se 2 (by rfl) ⟨5152794, by rfl⟩ : syracuseStep 13740785 = 10305589) B10305589
theorem B1608435 : Blo 1607002 1608435 := bstep (se 1 (by rfl) ⟨1206326, by rfl⟩ : syracuseStep 1608435 = 2412653) B2412653
theorem B2411267 : Blo 1607002 2411267 := bstep (se 1 (by rfl) ⟨1808450, by rfl⟩ : syracuseStep 2411267 = 3616901) B3616901
theorem B1608451 : Blo 1607002 1608451 := bstep (se 1 (by rfl) ⟨1206338, by rfl⟩ : syracuseStep 1608451 = 2412677) B2412677
theorem B1608467 : Blo 1607002 1608467 := bstep (se 1 (by rfl) ⟨1206350, by rfl⟩ : syracuseStep 1608467 = 2412701) B2412701
theorem B93940501 : Blo 1607002 93940501 := bstep (se 6 (by rfl) ⟨2201730, by rfl⟩ : syracuseStep 93940501 = 4403461) B4403461
theorem B2411297 : Blo 1607002 2411297 := bstep (se 2 (by rfl) ⟨904236, by rfl⟩ : syracuseStep 2411297 = 1808473) B1808473
theorem B3435299 : Blo 1607002 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B1608483 : Blo 1607002 1608483 := bstep (se 1 (by rfl) ⟨1206362, by rfl⟩ : syracuseStep 1608483 = 2412725) B2412725
theorem B2411315 : Blo 1607002 2411315 := bstep (se 1 (by rfl) ⟨1808486, by rfl⟩ : syracuseStep 2411315 = 3616973) B3616973
theorem B1608499 : Blo 1607002 1608499 := bstep (se 1 (by rfl) ⟨1206374, by rfl⟩ : syracuseStep 1608499 = 2412749) B2412749
theorem B1608515 : Blo 1607002 1608515 := bstep (se 1 (by rfl) ⟨1206386, by rfl⟩ : syracuseStep 1608515 = 2412773) B2412773
theorem B2411345 : Blo 1607002 2411345 := bstep (se 2 (by rfl) ⟨904254, by rfl⟩ : syracuseStep 2411345 = 1808509) B1808509
theorem B1608531 : Blo 1607002 1608531 := bstep (se 1 (by rfl) ⟨1206398, by rfl⟩ : syracuseStep 1608531 = 2412797) B2412797
theorem B2714465 : Blo 1607002 2714465 := bstep (se 2 (by rfl) ⟨1017924, by rfl⟩ : syracuseStep 2714465 = 2035849) B2035849
theorem B2411363 : Blo 1607002 2411363 := bstep (se 1 (by rfl) ⟨1808522, by rfl⟩ : syracuseStep 2411363 = 3617045) B3617045
theorem B1608547 : Blo 1607002 1608547 := bstep (se 1 (by rfl) ⟨1206410, by rfl⟩ : syracuseStep 1608547 = 2412821) B2412821
theorem B1608563 : Blo 1607002 1608563 := bstep (se 1 (by rfl) ⟨1206422, by rfl⟩ : syracuseStep 1608563 = 2412845) B2412845
theorem B2411393 : Blo 1607002 2411393 := bstep (se 2 (by rfl) ⟨904272, by rfl⟩ : syracuseStep 2411393 = 1808545) B1808545
theorem B2173825 : Blo 1607002 2173825 := bstep (se 2 (by rfl) ⟨815184, by rfl⟩ : syracuseStep 2173825 = 1630369) B1630369
theorem B1608579 : Blo 1607002 1608579 := bstep (se 1 (by rfl) ⟨1206434, by rfl⟩ : syracuseStep 1608579 = 2412869) B2412869
theorem B2411411 : Blo 1607002 2411411 := bstep (se 1 (by rfl) ⟨1808558, by rfl⟩ : syracuseStep 2411411 = 3617117) B3617117
theorem B1608595 : Blo 1607002 1608595 := bstep (se 1 (by rfl) ⟨1206446, by rfl⟩ : syracuseStep 1608595 = 2412893) B2412893
theorem B1608611 : Blo 1607002 1608611 := bstep (se 1 (by rfl) ⟨1206458, by rfl⟩ : syracuseStep 1608611 = 2412917) B2412917
theorem B2411441 : Blo 1607002 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B1608627 : Blo 1607002 1608627 := bstep (se 1 (by rfl) ⟨1206470, by rfl⟩ : syracuseStep 1608627 = 2412941) B2412941
theorem B2411459 : Blo 1607002 2411459 := bstep (se 1 (by rfl) ⟨1808594, by rfl⟩ : syracuseStep 2411459 = 3617189) B3617189
theorem B1608643 : Blo 1607002 1608643 := bstep (se 1 (by rfl) ⟨1206482, by rfl⟩ : syracuseStep 1608643 = 2412965) B2412965
theorem B9153485 : Blo 1607002 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B1608659 : Blo 1607002 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B2411489 : Blo 1607002 2411489 := bstep (se 2 (by rfl) ⟨904308, by rfl⟩ : syracuseStep 2411489 = 1808617) B1808617
theorem B2714593 : Blo 1607002 2714593 := bstep (se 2 (by rfl) ⟨1017972, by rfl⟩ : syracuseStep 2714593 = 2035945) B2035945
theorem B2034659 : Blo 1607002 2034659 := bstep (se 1 (by rfl) ⟨1525994, by rfl⟩ : syracuseStep 2034659 = 3051989) B3051989
theorem B1608675 : Blo 1607002 1608675 := bstep (se 1 (by rfl) ⟨1206506, by rfl⟩ : syracuseStep 1608675 = 2413013) B2413013
theorem B2411507 : Blo 1607002 2411507 := bstep (se 1 (by rfl) ⟨1808630, by rfl⟩ : syracuseStep 2411507 = 3617261) B3617261
theorem B1608691 : Blo 1607002 1608691 := bstep (se 1 (by rfl) ⟨1206518, by rfl⟩ : syracuseStep 1608691 = 2413037) B2413037
theorem B2714627 : Blo 1607002 2714627 := bstep (se 1 (by rfl) ⟨2035970, by rfl⟩ : syracuseStep 2714627 = 4071941) B4071941
theorem B1608707 : Blo 1607002 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B5426189 : Blo 1607002 5426189 := bstep (se 3 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 5426189 = 2034821) B2034821
theorem B3861521 : Blo 1607002 3861521 := bstep (se 2 (by rfl) ⟨1448070, by rfl⟩ : syracuseStep 3861521 = 2896141) B2896141
theorem B2411537 : Blo 1607002 2411537 := bstep (se 2 (by rfl) ⟨904326, by rfl⟩ : syracuseStep 2411537 = 1808653) B1808653
theorem B1608723 : Blo 1607002 1608723 := bstep (se 1 (by rfl) ⟨1206542, by rfl⟩ : syracuseStep 1608723 = 2413085) B2413085
theorem B2411555 : Blo 1607002 2411555 := bstep (se 1 (by rfl) ⟨1808666, by rfl⟩ : syracuseStep 2411555 = 3617333) B3617333
theorem B1608739 : Blo 1607002 1608739 := bstep (se 1 (by rfl) ⟨1206554, by rfl⟩ : syracuseStep 1608739 = 2413109) B2413109
theorem B1608755 : Blo 1607002 1608755 := bstep (se 1 (by rfl) ⟨1206566, by rfl⟩ : syracuseStep 1608755 = 2413133) B2413133
theorem B2411585 : Blo 1607002 2411585 := bstep (se 2 (by rfl) ⟨904344, by rfl⟩ : syracuseStep 2411585 = 1808689) B1808689
theorem B5426243 : Blo 1607002 5426243 := bstep (se 1 (by rfl) ⟨4069682, by rfl⟩ : syracuseStep 5426243 = 8139365) B8139365
theorem B1608771 : Blo 1607002 1608771 := bstep (se 1 (by rfl) ⟨1206578, by rfl⟩ : syracuseStep 1608771 = 2413157) B2413157
theorem B2411603 : Blo 1607002 2411603 := bstep (se 1 (by rfl) ⟨1808702, by rfl⟩ : syracuseStep 2411603 = 3617405) B3617405
theorem B1608787 : Blo 1607002 1608787 := bstep (se 1 (by rfl) ⟨1206590, by rfl⟩ : syracuseStep 1608787 = 2413181) B2413181
theorem B6106211 : Blo 1607002 6106211 := bstep (se 1 (by rfl) ⟨4579658, by rfl⟩ : syracuseStep 6106211 = 9159317) B9159317
theorem B1608803 : Blo 1607002 1608803 := bstep (se 1 (by rfl) ⟨1206602, by rfl⟩ : syracuseStep 1608803 = 2413205) B2413205
theorem B3615857 : Blo 1607002 3615857 := bstep (se 2 (by rfl) ⟨1355946, by rfl⟩ : syracuseStep 3615857 = 2711893) B2711893
theorem B2411633 : Blo 1607002 2411633 := bstep (se 2 (by rfl) ⟨904362, by rfl⟩ : syracuseStep 2411633 = 1808725) B1808725
theorem B6106225 : Blo 1607002 6106225 := bstep (se 2 (by rfl) ⟨2289834, by rfl⟩ : syracuseStep 6106225 = 4579669) B4579669
theorem B1608819 : Blo 1607002 1608819 := bstep (se 1 (by rfl) ⟨1206614, by rfl⟩ : syracuseStep 1608819 = 2413229) B2413229
theorem B3615875 : Blo 1607002 3615875 := bstep (se 1 (by rfl) ⟨2711906, by rfl⟩ : syracuseStep 3615875 = 5423813) B5423813
theorem B2411651 : Blo 1607002 2411651 := bstep (se 1 (by rfl) ⟨1808738, by rfl⟩ : syracuseStep 2411651 = 3617477) B3617477
theorem B2714755 : Blo 1607002 2714755 := bstep (se 1 (by rfl) ⟨2036066, by rfl⟩ : syracuseStep 2714755 = 4072133) B4072133
theorem B1608835 : Blo 1607002 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B1608851 : Blo 1607002 1608851 := bstep (se 1 (by rfl) ⟨1206638, by rfl⟩ : syracuseStep 1608851 = 2413277) B2413277
theorem B2411681 : Blo 1607002 2411681 := bstep (se 2 (by rfl) ⟨904380, by rfl⟩ : syracuseStep 2411681 = 1808761) B1808761
theorem B1608867 : Blo 1607002 1608867 := bstep (se 1 (by rfl) ⟨1206650, by rfl⟩ : syracuseStep 1608867 = 2413301) B2413301
theorem B2411699 : Blo 1607002 2411699 := bstep (se 1 (by rfl) ⟨1808774, by rfl⟩ : syracuseStep 2411699 = 3617549) B3617549
theorem B1608883 : Blo 1607002 1608883 := bstep (se 1 (by rfl) ⟨1206662, by rfl⟩ : syracuseStep 1608883 = 2413325) B2413325
theorem B1608899 : Blo 1607002 1608899 := bstep (se 1 (by rfl) ⟨1206674, by rfl⟩ : syracuseStep 1608899 = 2413349) B2413349
theorem B2411729 : Blo 1607002 2411729 := bstep (se 2 (by rfl) ⟨904398, by rfl⟩ : syracuseStep 2411729 = 1808797) B1808797
theorem B1608915 : Blo 1607002 1608915 := bstep (se 1 (by rfl) ⟨1206686, by rfl⟩ : syracuseStep 1608915 = 2413373) B2413373
theorem B2411747 : Blo 1607002 2411747 := bstep (se 1 (by rfl) ⟨1808810, by rfl⟩ : syracuseStep 2411747 = 3617621) B3617621
theorem B1608931 : Blo 1607002 1608931 := bstep (se 1 (by rfl) ⟨1206698, by rfl⟩ : syracuseStep 1608931 = 2413397) B2413397
theorem B1608947 : Blo 1607002 1608947 := bstep (se 1 (by rfl) ⟨1206710, by rfl⟩ : syracuseStep 1608947 = 2413421) B2413421
theorem B2411777 : Blo 1607002 2411777 := bstep (se 2 (by rfl) ⟨904416, by rfl⟩ : syracuseStep 2411777 = 1808833) B1808833
theorem B1608963 : Blo 1607002 1608963 := bstep (se 1 (by rfl) ⟨1206722, by rfl⟩ : syracuseStep 1608963 = 2413445) B2413445
theorem B2714897 : Blo 1607002 2714897 := bstep (se 2 (by rfl) ⟨1018086, by rfl⟩ : syracuseStep 2714897 = 2036173) B2036173
theorem B2411795 : Blo 1607002 2411795 := bstep (se 1 (by rfl) ⟨1808846, by rfl⟩ : syracuseStep 2411795 = 3617693) B3617693
theorem B1608979 : Blo 1607002 1608979 := bstep (se 1 (by rfl) ⟨1206734, by rfl⟩ : syracuseStep 1608979 = 2413469) B2413469
theorem B6868259 : Blo 1607002 6868259 := bstep (se 1 (by rfl) ⟨5151194, by rfl⟩ : syracuseStep 6868259 = 10302389) B10302389
theorem B1608995 : Blo 1607002 1608995 := bstep (se 1 (by rfl) ⟨1206746, by rfl⟩ : syracuseStep 1608995 = 2413493) B2413493
theorem B2411825 : Blo 1607002 2411825 := bstep (se 2 (by rfl) ⟨904434, by rfl⟩ : syracuseStep 2411825 = 1808869) B1808869
theorem B2411843 : Blo 1607002 2411843 := bstep (se 1 (by rfl) ⟨1808882, by rfl⟩ : syracuseStep 2411843 = 3617765) B3617765
theorem B13225285 : Blo 1607002 13225285 := bstep (se 4 (by rfl) ⟨1239870, by rfl⟩ : syracuseStep 13225285 = 2479741) B2479741
theorem B5426513 : Blo 1607002 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B1740115 : Blo 1607002 1740115 := bstep (se 1 (by rfl) ⟨1305086, by rfl⟩ : syracuseStep 1740115 = 2610173) B2610173
theorem B2411873 : Blo 1607002 2411873 := bstep (se 2 (by rfl) ⟨904452, by rfl⟩ : syracuseStep 2411873 = 1808905) B1808905
theorem B2411891 : Blo 1607002 2411891 := bstep (se 1 (by rfl) ⟨1808918, by rfl⟩ : syracuseStep 2411891 = 3617837) B3617837
theorem B3616145 : Blo 1607002 3616145 := bstep (se 2 (by rfl) ⟨1356054, by rfl⟩ : syracuseStep 3616145 = 2712109) B2712109
theorem B2411921 : Blo 1607002 2411921 := bstep (se 2 (by rfl) ⟨904470, by rfl⟩ : syracuseStep 2411921 = 1808941) B1808941
theorem B2715025 : Blo 1607002 2715025 := bstep (se 2 (by rfl) ⟨1018134, by rfl⟩ : syracuseStep 2715025 = 2036269) B2036269
theorem B3616163 : Blo 1607002 3616163 := bstep (se 1 (by rfl) ⟨2712122, by rfl⟩ : syracuseStep 3616163 = 5424245) B5424245
theorem B2411939 : Blo 1607002 2411939 := bstep (se 1 (by rfl) ⟨1808954, by rfl⟩ : syracuseStep 2411939 = 3617909) B3617909
theorem B2715059 : Blo 1607002 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B2411969 : Blo 1607002 2411969 := bstep (se 2 (by rfl) ⟨904488, by rfl⟩ : syracuseStep 2411969 = 1808977) B1808977
theorem B2411987 : Blo 1607002 2411987 := bstep (se 1 (by rfl) ⟨1808990, by rfl⟩ : syracuseStep 2411987 = 3617981) B3617981
theorem B2412017 : Blo 1607002 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B2575859 : Blo 1607002 2575859 := bstep (se 1 (by rfl) ⟨1931894, by rfl⟩ : syracuseStep 2575859 = 3863789) B3863789
theorem B2412035 : Blo 1607002 2412035 := bstep (se 1 (by rfl) ⟨1809026, by rfl⟩ : syracuseStep 2412035 = 3618053) B3618053
theorem B7728653 : Blo 1607002 7728653 := bstep (se 3 (by rfl) ⟨1449122, by rfl⟩ : syracuseStep 7728653 = 2898245) B2898245
theorem B2412065 : Blo 1607002 2412065 := bstep (se 2 (by rfl) ⟨904524, by rfl⟩ : syracuseStep 2412065 = 1809049) B1809049
theorem B2412083 : Blo 1607002 2412083 := bstep (se 1 (by rfl) ⟨1809062, by rfl⟩ : syracuseStep 2412083 = 3618125) B3618125
theorem B2715187 : Blo 1607002 2715187 := bstep (se 1 (by rfl) ⟨2036390, by rfl⟩ : syracuseStep 2715187 = 4072781) B4072781
theorem B2575937 : Blo 1607002 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B2412113 : Blo 1607002 2412113 := bstep (se 2 (by rfl) ⟨904542, by rfl⟩ : syracuseStep 2412113 = 1809085) B1809085
theorem B2412131 : Blo 1607002 2412131 := bstep (se 1 (by rfl) ⟨1809098, by rfl⟩ : syracuseStep 2412131 = 3618197) B3618197
theorem B12209777 : Blo 1607002 12209777 := bstep (se 2 (by rfl) ⟨4578666, by rfl⟩ : syracuseStep 12209777 = 9157333) B9157333
theorem B2412161 : Blo 1607002 2412161 := bstep (se 2 (by rfl) ⟨904560, by rfl⟩ : syracuseStep 2412161 = 1809121) B1809121
theorem B2412179 : Blo 1607002 2412179 := bstep (se 1 (by rfl) ⟨1809134, by rfl⟩ : syracuseStep 2412179 = 3618269) B3618269
theorem B2035363 : Blo 1607002 2035363 := bstep (se 1 (by rfl) ⟨1526522, by rfl⟩ : syracuseStep 2035363 = 3053045) B3053045
theorem B3616433 : Blo 1607002 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B2412209 : Blo 1607002 2412209 := bstep (se 2 (by rfl) ⟨904578, by rfl⟩ : syracuseStep 2412209 = 1809157) B1809157
theorem B3616451 : Blo 1607002 3616451 := bstep (se 1 (by rfl) ⟨2712338, by rfl⟩ : syracuseStep 3616451 = 5424677) B5424677
theorem B2412227 : Blo 1607002 2412227 := bstep (se 1 (by rfl) ⟨1809170, by rfl⟩ : syracuseStep 2412227 = 3618341) B3618341
theorem B2412257 : Blo 1607002 2412257 := bstep (se 2 (by rfl) ⟨904596, by rfl⟩ : syracuseStep 2412257 = 1809193) B1809193
theorem B2289379 : Blo 1607002 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B3436273 : Blo 1607002 3436273 := bstep (se 2 (by rfl) ⟨1288602, by rfl⟩ : syracuseStep 3436273 = 2577205) B2577205
theorem B2412275 : Blo 1607002 2412275 := bstep (se 1 (by rfl) ⟨1809206, by rfl⟩ : syracuseStep 2412275 = 3618413) B3618413
theorem B2035459 : Blo 1607002 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B2412305 : Blo 1607002 2412305 := bstep (se 2 (by rfl) ⟨904614, by rfl⟩ : syracuseStep 2412305 = 1809229) B1809229
theorem B2576161 : Blo 1607002 2576161 := bstep (se 2 (by rfl) ⟨966060, by rfl⟩ : syracuseStep 2576161 = 1932121) B1932121
theorem B2412323 : Blo 1607002 2412323 := bstep (se 1 (by rfl) ⟨1809242, by rfl⟩ : syracuseStep 2412323 = 3618485) B3618485
theorem B2412353 : Blo 1607002 2412353 := bstep (se 2 (by rfl) ⟨904632, by rfl⟩ : syracuseStep 2412353 = 1809265) B1809265
theorem B2412371 : Blo 1607002 2412371 := bstep (se 1 (by rfl) ⟨1809278, by rfl⟩ : syracuseStep 2412371 = 3618557) B3618557
theorem B5427053 : Blo 1607002 5427053 := bstep (se 3 (by rfl) ⟨1017572, by rfl⟩ : syracuseStep 5427053 = 2035145) B2035145
theorem B9154417 : Blo 1607002 9154417 := bstep (se 2 (by rfl) ⟨3432906, by rfl⟩ : syracuseStep 9154417 = 6865813) B6865813
theorem B2412401 : Blo 1607002 2412401 := bstep (se 2 (by rfl) ⟨904650, by rfl⟩ : syracuseStep 2412401 = 1809301) B1809301
theorem B2412419 : Blo 1607002 2412419 := bstep (se 1 (by rfl) ⟨1809314, by rfl⟩ : syracuseStep 2412419 = 3618629) B3618629
theorem B2412449 : Blo 1607002 2412449 := bstep (se 2 (by rfl) ⟨904668, by rfl⟩ : syracuseStep 2412449 = 1809337) B1809337
theorem B3051427 : Blo 1607002 3051427 := bstep (se 1 (by rfl) ⟨2288570, by rfl⟩ : syracuseStep 3051427 = 4577141) B4577141
theorem B5427107 : Blo 1607002 5427107 := bstep (se 1 (by rfl) ⟨4070330, by rfl⟩ : syracuseStep 5427107 = 8140661) B8140661
theorem B5148593 : Blo 1607002 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B2412467 : Blo 1607002 2412467 := bstep (se 1 (by rfl) ⟨1809350, by rfl⟩ : syracuseStep 2412467 = 3618701) B3618701
theorem B17379269 : Blo 1607002 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B3616721 : Blo 1607002 3616721 := bstep (se 2 (by rfl) ⟨1356270, by rfl⟩ : syracuseStep 3616721 = 2712541) B2712541
theorem B2412497 : Blo 1607002 2412497 := bstep (se 2 (by rfl) ⟨904686, by rfl⟩ : syracuseStep 2412497 = 1809373) B1809373
theorem B5148643 : Blo 1607002 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B3616739 : Blo 1607002 3616739 := bstep (se 1 (by rfl) ⟨2712554, by rfl⟩ : syracuseStep 3616739 = 5425109) B5425109
theorem B2412515 : Blo 1607002 2412515 := bstep (se 1 (by rfl) ⟨1809386, by rfl⟩ : syracuseStep 2412515 = 3618773) B3618773
theorem B2412545 : Blo 1607002 2412545 := bstep (se 2 (by rfl) ⟨904704, by rfl⟩ : syracuseStep 2412545 = 1809409) B1809409
theorem B2412563 : Blo 1607002 2412563 := bstep (se 1 (by rfl) ⟨1809422, by rfl⟩ : syracuseStep 2412563 = 3618845) B3618845
theorem B10301489 : Blo 1607002 10301489 := bstep (se 2 (by rfl) ⟨3863058, by rfl⟩ : syracuseStep 10301489 = 7726117) B7726117
theorem B2412593 : Blo 1607002 2412593 := bstep (se 2 (by rfl) ⟨904722, by rfl⟩ : syracuseStep 2412593 = 1809445) B1809445
theorem B3051587 : Blo 1607002 3051587 := bstep (se 1 (by rfl) ⟨2288690, by rfl⟩ : syracuseStep 3051587 = 4577381) B4577381
theorem B2412611 : Blo 1607002 2412611 := bstep (se 1 (by rfl) ⟨1809458, by rfl⟩ : syracuseStep 2412611 = 3618917) B3618917
theorem B2412641 : Blo 1607002 2412641 := bstep (se 2 (by rfl) ⟨904740, by rfl⟩ : syracuseStep 2412641 = 1809481) B1809481
theorem B6189169 : Blo 1607002 6189169 := bstep (se 2 (by rfl) ⟨2320938, by rfl⟩ : syracuseStep 6189169 = 4641877) B4641877
theorem B2412659 : Blo 1607002 2412659 := bstep (se 1 (by rfl) ⟨1809494, by rfl⟩ : syracuseStep 2412659 = 3618989) B3618989
theorem B2412689 : Blo 1607002 2412689 := bstep (se 2 (by rfl) ⟨904758, by rfl⟩ : syracuseStep 2412689 = 1809517) B1809517
theorem B2412707 : Blo 1607002 2412707 := bstep (se 1 (by rfl) ⟨1809530, by rfl⟩ : syracuseStep 2412707 = 3619061) B3619061
theorem B5427377 : Blo 1607002 5427377 := bstep (se 2 (by rfl) ⟨2035266, by rfl⟩ : syracuseStep 5427377 = 4070533) B4070533
theorem B2412737 : Blo 1607002 2412737 := bstep (se 2 (by rfl) ⟨904776, by rfl⟩ : syracuseStep 2412737 = 1809553) B1809553
theorem B2412755 : Blo 1607002 2412755 := bstep (se 1 (by rfl) ⟨1809566, by rfl⟩ : syracuseStep 2412755 = 3619133) B3619133
theorem B4346093 : Blo 1607002 4346093 := bstep (se 3 (by rfl) ⟨814892, by rfl⟩ : syracuseStep 4346093 = 1629785) B1629785
theorem B3617009 : Blo 1607002 3617009 := bstep (se 2 (by rfl) ⟨1356378, by rfl⟩ : syracuseStep 3617009 = 2712757) B2712757
theorem B2412785 : Blo 1607002 2412785 := bstep (se 2 (by rfl) ⟨904794, by rfl⟩ : syracuseStep 2412785 = 1809589) B1809589
theorem B2035955 : Blo 1607002 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B3617027 : Blo 1607002 3617027 := bstep (se 1 (by rfl) ⟨2712770, by rfl⟩ : syracuseStep 3617027 = 5425541) B5425541
theorem B2412803 : Blo 1607002 2412803 := bstep (se 1 (by rfl) ⟨1809602, by rfl⟩ : syracuseStep 2412803 = 3619205) B3619205
theorem B11464973 : Blo 1607002 11464973 := bstep (se 3 (by rfl) ⟨2149682, by rfl⟩ : syracuseStep 11464973 = 4299365) B4299365
theorem B2412833 : Blo 1607002 2412833 := bstep (se 2 (by rfl) ⟨904812, by rfl⟩ : syracuseStep 2412833 = 1809625) B1809625
theorem B2412851 : Blo 1607002 2412851 := bstep (se 1 (by rfl) ⟨1809638, by rfl⟩ : syracuseStep 2412851 = 3619277) B3619277
theorem B2412881 : Blo 1607002 2412881 := bstep (se 2 (by rfl) ⟨904830, by rfl⟩ : syracuseStep 2412881 = 1809661) B1809661
theorem B2412899 : Blo 1607002 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B4886897 : Blo 1607002 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B13046129 : Blo 1607002 13046129 := bstep (se 2 (by rfl) ⟨4892298, by rfl⟩ : syracuseStep 13046129 = 9784597) B9784597
theorem B2412929 : Blo 1607002 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B4067729 : Blo 1607002 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B2412947 : Blo 1607002 2412947 := bstep (se 1 (by rfl) ⟨1809710, by rfl⟩ : syracuseStep 2412947 = 3619421) B3619421
theorem B2412977 : Blo 1607002 2412977 := bstep (se 2 (by rfl) ⟨904866, by rfl⟩ : syracuseStep 2412977 = 1809733) B1809733
theorem B2445761 : Blo 1607002 2445761 := bstep (se 2 (by rfl) ⟨917160, by rfl⟩ : syracuseStep 2445761 = 1834321) B1834321
theorem B4067779 : Blo 1607002 4067779 := bstep (se 1 (by rfl) ⟨3050834, by rfl⟩ : syracuseStep 4067779 = 6101669) B6101669
theorem B2412995 : Blo 1607002 2412995 := bstep (se 1 (by rfl) ⟨1809746, by rfl⟩ : syracuseStep 2412995 = 3619493) B3619493
theorem B2896337 : Blo 1607002 2896337 := bstep (se 2 (by rfl) ⟨1086126, by rfl⟩ : syracuseStep 2896337 = 2172253) B2172253
theorem B2413025 : Blo 1607002 2413025 := bstep (se 2 (by rfl) ⟨904884, by rfl⟩ : syracuseStep 2413025 = 1809769) B1809769
theorem B2413043 : Blo 1607002 2413043 := bstep (se 1 (by rfl) ⟨1809782, by rfl⟩ : syracuseStep 2413043 = 3619565) B3619565
theorem B3617297 : Blo 1607002 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B2413073 : Blo 1607002 2413073 := bstep (se 2 (by rfl) ⟨904902, by rfl⟩ : syracuseStep 2413073 = 1809805) B1809805
theorem B3617315 : Blo 1607002 3617315 := bstep (se 1 (by rfl) ⟨2712986, by rfl⟩ : syracuseStep 3617315 = 5425973) B5425973
theorem B6107683 : Blo 1607002 6107683 := bstep (se 1 (by rfl) ⟨4580762, by rfl⟩ : syracuseStep 6107683 = 9161525) B9161525
theorem B2413091 : Blo 1607002 2413091 := bstep (se 1 (by rfl) ⟨1809818, by rfl⟩ : syracuseStep 2413091 = 3619637) B3619637
theorem B2413121 : Blo 1607002 2413121 := bstep (se 2 (by rfl) ⟨904920, by rfl⟩ : syracuseStep 2413121 = 1809841) B1809841
theorem B4067921 : Blo 1607002 4067921 := bstep (se 2 (by rfl) ⟨1525470, by rfl⟩ : syracuseStep 4067921 = 3050941) B3050941
theorem B2413139 : Blo 1607002 2413139 := bstep (se 1 (by rfl) ⟨1809854, by rfl⟩ : syracuseStep 2413139 = 3619709) B3619709
theorem B2413169 : Blo 1607002 2413169 := bstep (se 2 (by rfl) ⟨904938, by rfl⟩ : syracuseStep 2413169 = 1809877) B1809877
theorem B2413187 : Blo 1607002 2413187 := bstep (se 1 (by rfl) ⟨1809890, by rfl⟩ : syracuseStep 2413187 = 3619781) B3619781
theorem B2413217 : Blo 1607002 2413217 := bstep (se 2 (by rfl) ⟨904956, by rfl⟩ : syracuseStep 2413217 = 1809913) B1809913
theorem B4403875 : Blo 1607002 4403875 := bstep (se 1 (by rfl) ⟨3302906, by rfl⟩ : syracuseStep 4403875 = 6605813) B6605813
theorem B2413235 : Blo 1607002 2413235 := bstep (se 1 (by rfl) ⟨1809926, by rfl⟩ : syracuseStep 2413235 = 3619853) B3619853
theorem B5427917 : Blo 1607002 5427917 := bstep (se 3 (by rfl) ⟨1017734, by rfl⟩ : syracuseStep 5427917 = 2035469) B2035469
theorem B2413265 : Blo 1607002 2413265 := bstep (se 2 (by rfl) ⟨904974, by rfl⟩ : syracuseStep 2413265 = 1809949) B1809949
theorem B2413283 : Blo 1607002 2413283 := bstep (se 1 (by rfl) ⟨1809962, by rfl⟩ : syracuseStep 2413283 = 3619925) B3619925
theorem B5796593 : Blo 1607002 5796593 := bstep (se 2 (by rfl) ⟨2173722, by rfl⟩ : syracuseStep 5796593 = 4347445) B4347445
theorem B2413313 : Blo 1607002 2413313 := bstep (se 2 (by rfl) ⟨904992, by rfl⟩ : syracuseStep 2413313 = 1809985) B1809985
theorem B5427971 : Blo 1607002 5427971 := bstep (se 1 (by rfl) ⟨4070978, by rfl⟩ : syracuseStep 5427971 = 8141957) B8141957
theorem B2413331 : Blo 1607002 2413331 := bstep (se 1 (by rfl) ⟨1809998, by rfl⟩ : syracuseStep 2413331 = 3619997) B3619997
theorem B5149489 : Blo 1607002 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B3617585 : Blo 1607002 3617585 := bstep (se 2 (by rfl) ⟨1356594, by rfl⟩ : syracuseStep 3617585 = 2713189) B2713189
theorem B1717043 : Blo 1607002 1717043 := bstep (se 1 (by rfl) ⟨1287782, by rfl⟩ : syracuseStep 1717043 = 2575565) B2575565
theorem B2413361 : Blo 1607002 2413361 := bstep (se 2 (by rfl) ⟨905010, by rfl⟩ : syracuseStep 2413361 = 1810021) B1810021
theorem B3617603 : Blo 1607002 3617603 := bstep (se 1 (by rfl) ⟨2713202, by rfl⟩ : syracuseStep 3617603 = 5426405) B5426405
theorem B2413379 : Blo 1607002 2413379 := bstep (se 1 (by rfl) ⟨1810034, by rfl⟩ : syracuseStep 2413379 = 3620069) B3620069
theorem B2290513 : Blo 1607002 2290513 := bstep (se 2 (by rfl) ⟨858942, by rfl⟩ : syracuseStep 2290513 = 1717885) B1717885
theorem B2413409 : Blo 1607002 2413409 := bstep (se 2 (by rfl) ⟨905028, by rfl⟩ : syracuseStep 2413409 = 1810057) B1810057
theorem B5796721 : Blo 1607002 5796721 := bstep (se 2 (by rfl) ⟨2173770, by rfl⟩ : syracuseStep 5796721 = 4347541) B4347541
theorem B2413427 : Blo 1607002 2413427 := bstep (se 1 (by rfl) ⟨1810070, by rfl⟩ : syracuseStep 2413427 = 3620141) B3620141
theorem B2413457 : Blo 1607002 2413457 := bstep (se 2 (by rfl) ⟨905046, by rfl⟩ : syracuseStep 2413457 = 1810093) B1810093
theorem B2413475 : Blo 1607002 2413475 := bstep (se 1 (by rfl) ⟨1810106, by rfl⟩ : syracuseStep 2413475 = 3620213) B3620213
theorem B2290609 : Blo 1607002 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B5428241 : Blo 1607002 5428241 := bstep (se 2 (by rfl) ⟨2035590, by rfl⟩ : syracuseStep 5428241 = 4071181) B4071181
theorem B3617873 : Blo 1607002 3617873 := bstep (se 2 (by rfl) ⟨1356702, by rfl⟩ : syracuseStep 3617873 = 2713405) B2713405
theorem B3617891 : Blo 1607002 3617891 := bstep (se 1 (by rfl) ⟨2713418, by rfl⟩ : syracuseStep 3617891 = 5426837) B5426837
theorem B3052657 : Blo 1607002 3052657 := bstep (se 2 (by rfl) ⟨1144746, by rfl⟩ : syracuseStep 3052657 = 2289493) B2289493
theorem B8696965 : Blo 1607002 8696965 := bstep (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) B1630681
theorem B7337101 : Blo 1607002 7337101 := bstep (se 3 (by rfl) ⟨1375706, by rfl⟩ : syracuseStep 7337101 = 2751413) B2751413
theorem B2749585 : Blo 1607002 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B27473093 : Blo 1607002 27473093 := bstep (se 4 (by rfl) ⟨2575602, by rfl⟩ : syracuseStep 27473093 = 5151205) B5151205
theorem B6870257 : Blo 1607002 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B1651955 : Blo 1607002 1651955 := bstep (se 1 (by rfl) ⟨1238966, by rfl⟩ : syracuseStep 1651955 = 2477933) B2477933
theorem B2749715 : Blo 1607002 2749715 := bstep (se 1 (by rfl) ⟨2062286, by rfl⟩ : syracuseStep 2749715 = 4124573) B4124573
theorem B9155875 : Blo 1607002 9155875 := bstep (se 1 (by rfl) ⟨6866906, by rfl⟩ : syracuseStep 9155875 = 13733813) B13733813
theorem B3618161 : Blo 1607002 3618161 := bstep (se 2 (by rfl) ⟨1356810, by rfl⟩ : syracuseStep 3618161 = 2713621) B2713621
theorem B3618179 : Blo 1607002 3618179 := bstep (se 1 (by rfl) ⟨2713634, by rfl⟩ : syracuseStep 3618179 = 5427269) B5427269
theorem B4576753 : Blo 1607002 4576753 := bstep (se 2 (by rfl) ⟨1716282, by rfl⟩ : syracuseStep 4576753 = 3432565) B3432565
theorem B18363917 : Blo 1607002 18363917 := bstep (se 3 (by rfl) ⟨3443234, by rfl⟩ : syracuseStep 18363917 = 6886469) B6886469
theorem B2749969 : Blo 1607002 2749969 := bstep (se 2 (by rfl) ⟨1031238, by rfl⟩ : syracuseStep 2749969 = 2062477) B2062477
theorem B1717795 : Blo 1607002 1717795 := bstep (se 1 (by rfl) ⟨1288346, by rfl⟩ : syracuseStep 1717795 = 2576693) B2576693
theorem B5428781 : Blo 1607002 5428781 := bstep (se 3 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 5428781 = 2035793) B2035793
theorem B4068913 : Blo 1607002 4068913 := bstep (se 2 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 4068913 = 3051685) B3051685
theorem B8140337 : Blo 1607002 8140337 := bstep (se 2 (by rfl) ⟨3052626, by rfl⟩ : syracuseStep 8140337 = 6105253) B6105253
theorem B5428835 : Blo 1607002 5428835 := bstep (se 1 (by rfl) ⟨4071626, by rfl⟩ : syracuseStep 5428835 = 8143253) B8143253
theorem B1807987 : Blo 1607002 1807987 := bstep (se 1 (by rfl) ⟨1355990, by rfl⟩ : syracuseStep 1807987 = 2711981) B2711981
theorem B2479745 : Blo 1607002 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B3618449 : Blo 1607002 3618449 := bstep (se 2 (by rfl) ⟨1356918, by rfl⟩ : syracuseStep 3618449 = 2713837) B2713837
theorem B3618467 : Blo 1607002 3618467 := bstep (se 1 (by rfl) ⟨2713850, by rfl⟩ : syracuseStep 3618467 = 5427701) B5427701
theorem B2234081 : Blo 1607002 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B1808131 : Blo 1607002 1808131 := bstep (se 1 (by rfl) ⟨1356098, by rfl⟩ : syracuseStep 1808131 = 2712197) B2712197
theorem B9156401 : Blo 1607002 9156401 := bstep (se 2 (by rfl) ⟨3433650, by rfl⟩ : syracuseStep 9156401 = 6867301) B6867301
theorem B4069187 : Blo 1607002 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B5429105 : Blo 1607002 5429105 := bstep (se 2 (by rfl) ⟨2035914, by rfl⟩ : syracuseStep 5429105 = 4071829) B4071829
theorem B1808275 : Blo 1607002 1808275 := bstep (se 1 (by rfl) ⟨1356206, by rfl⟩ : syracuseStep 1808275 = 2712413) B2712413
theorem B3618737 : Blo 1607002 3618737 := bstep (se 2 (by rfl) ⟨1357026, by rfl⟩ : syracuseStep 3618737 = 2714053) B2714053
theorem B3618755 : Blo 1607002 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B35739589 : Blo 1607002 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B1832915 : Blo 1607002 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B4069379 : Blo 1607002 4069379 := bstep (se 1 (by rfl) ⟨3052034, by rfl⟩ : syracuseStep 4069379 = 6104069) B6104069
theorem B1808419 : Blo 1607002 1808419 := bstep (se 1 (by rfl) ⟨1356314, by rfl⟩ : syracuseStep 1808419 = 2712629) B2712629
theorem B5224493 : Blo 1607002 5224493 := bstep (se 3 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 5224493 = 1959185) B1959185
theorem B92706929 : Blo 1607002 92706929 := bstep (se 2 (by rfl) ⟨34765098, by rfl⟩ : syracuseStep 92706929 = 69530197) B69530197
theorem B3053713 : Blo 1607002 3053713 := bstep (se 2 (by rfl) ⟨1145142, by rfl⟩ : syracuseStep 3053713 = 2290285) B2290285
theorem B1808563 : Blo 1607002 1808563 := bstep (se 1 (by rfl) ⟨1356422, by rfl⟩ : syracuseStep 1808563 = 2712845) B2712845
theorem B3619025 : Blo 1607002 3619025 := bstep (se 2 (by rfl) ⟨1357134, by rfl⟩ : syracuseStep 3619025 = 2714269) B2714269
theorem B8689891 : Blo 1607002 8689891 := bstep (se 1 (by rfl) ⟨6517418, by rfl⟩ : syracuseStep 8689891 = 13034837) B13034837
theorem B3619043 : Blo 1607002 3619043 := bstep (se 1 (by rfl) ⟨2714282, by rfl⟩ : syracuseStep 3619043 = 5428565) B5428565
theorem B1808707 : Blo 1607002 1808707 := bstep (se 1 (by rfl) ⟨1356530, by rfl⟩ : syracuseStep 1808707 = 2713061) B2713061
theorem B5151053 : Blo 1607002 5151053 := bstep (se 3 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 5151053 = 1931645) B1931645
theorem B5429645 : Blo 1607002 5429645 := bstep (se 3 (by rfl) ⟨1018058, by rfl⟩ : syracuseStep 5429645 = 2036117) B2036117
theorem B5429699 : Blo 1607002 5429699 := bstep (se 1 (by rfl) ⟨4072274, by rfl⟩ : syracuseStep 5429699 = 8144549) B8144549
theorem B10303949 : Blo 1607002 10303949 := bstep (se 3 (by rfl) ⟨1931990, by rfl⟩ : syracuseStep 10303949 = 3863981) B3863981
theorem B1808851 : Blo 1607002 1808851 := bstep (se 1 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 1808851 = 2713277) B2713277
theorem B3619313 : Blo 1607002 3619313 := bstep (se 2 (by rfl) ⟨1357242, by rfl⟩ : syracuseStep 3619313 = 2714485) B2714485
theorem B1931779 : Blo 1607002 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B3619331 : Blo 1607002 3619331 := bstep (se 1 (by rfl) ⟨2714498, by rfl⟩ : syracuseStep 3619331 = 5428997) B5428997
theorem B3054115 : Blo 1607002 3054115 := bstep (se 1 (by rfl) ⟨2290586, by rfl⟩ : syracuseStep 3054115 = 4581173) B4581173
theorem B11008547 : Blo 1607002 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B4348493 : Blo 1607002 4348493 := bstep (se 3 (by rfl) ⟨815342, by rfl⟩ : syracuseStep 4348493 = 1630685) B1630685
theorem B3054161 : Blo 1607002 3054161 := bstep (se 2 (by rfl) ⟨1145310, by rfl⟩ : syracuseStep 3054161 = 2290621) B2290621
theorem B7723619 : Blo 1607002 7723619 := bstep (se 1 (by rfl) ⟨5792714, by rfl⟩ : syracuseStep 7723619 = 11585429) B11585429
theorem B1808995 : Blo 1607002 1808995 := bstep (se 1 (by rfl) ⟨1356746, by rfl⟩ : syracuseStep 1808995 = 2713493) B2713493
theorem B2063011 : Blo 1607002 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B5429969 : Blo 1607002 5429969 := bstep (se 2 (by rfl) ⟨2036238, by rfl⟩ : syracuseStep 5429969 = 4072477) B4072477
theorem B5798627 : Blo 1607002 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B4578029 : Blo 1607002 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B4889329 : Blo 1607002 4889329 := bstep (se 2 (by rfl) ⟨1833498, by rfl⟩ : syracuseStep 4889329 = 3666997) B3666997
theorem B1809139 : Blo 1607002 1809139 := bstep (se 1 (by rfl) ⟨1356854, by rfl⟩ : syracuseStep 1809139 = 2713709) B2713709
theorem B3619601 : Blo 1607002 3619601 := bstep (se 2 (by rfl) ⟨1357350, by rfl⟩ : syracuseStep 3619601 = 2714701) B2714701
theorem B3619619 : Blo 1607002 3619619 := bstep (se 1 (by rfl) ⟨2714714, by rfl⟩ : syracuseStep 3619619 = 5429429) B5429429
theorem B6101837 : Blo 1607002 6101837 := bstep (se 3 (by rfl) ⟨1144094, by rfl⟩ : syracuseStep 6101837 = 2288189) B2288189
theorem B3054449 : Blo 1607002 3054449 := bstep (se 2 (by rfl) ⟨1145418, by rfl⟩ : syracuseStep 3054449 = 2290837) B2290837
theorem B1809283 : Blo 1607002 1809283 := bstep (se 1 (by rfl) ⟨1356962, by rfl⟩ : syracuseStep 1809283 = 2713925) B2713925
theorem B6871949 : Blo 1607002 6871949 := bstep (se 3 (by rfl) ⟨1288490, by rfl⟩ : syracuseStep 6871949 = 2576981) B2576981
theorem B4578211 : Blo 1607002 4578211 := bstep (se 1 (by rfl) ⟨3433658, by rfl⟩ : syracuseStep 4578211 = 6867317) B6867317
theorem B6192035 : Blo 1607002 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B4070321 : Blo 1607002 4070321 := bstep (se 2 (by rfl) ⟨1526370, by rfl⟩ : syracuseStep 4070321 = 3052741) B3052741
theorem B4578257 : Blo 1607002 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B4070371 : Blo 1607002 4070371 := bstep (se 1 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 4070371 = 6105557) B6105557
theorem B8141795 : Blo 1607002 8141795 := bstep (se 1 (by rfl) ⟨6106346, by rfl⟩ : syracuseStep 8141795 = 12212693) B12212693
theorem B2644993 : Blo 1607002 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B1809427 : Blo 1607002 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B3619889 : Blo 1607002 3619889 := bstep (se 2 (by rfl) ⟨1357458, by rfl⟩ : syracuseStep 3619889 = 2714917) B2714917
theorem B3619907 : Blo 1607002 3619907 := bstep (se 1 (by rfl) ⟨2714930, by rfl⟩ : syracuseStep 3619907 = 5429861) B5429861
theorem B4070513 : Blo 1607002 4070513 := bstep (se 2 (by rfl) ⟨1526442, by rfl⟩ : syracuseStep 4070513 = 3052885) B3052885
theorem B2751617 : Blo 1607002 2751617 := bstep (se 2 (by rfl) ⟨1031856, by rfl⟩ : syracuseStep 2751617 = 2063713) B2063713
theorem B14670989 : Blo 1607002 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B1809571 : Blo 1607002 1809571 := bstep (se 1 (by rfl) ⟨1357178, by rfl⟩ : syracuseStep 1809571 = 2714357) B2714357
theorem B10296517 : Blo 1607002 10296517 := bstep (se 4 (by rfl) ⟨965298, by rfl⟩ : syracuseStep 10296517 = 1930597) B1930597
theorem B9157859 : Blo 1607002 9157859 := bstep (se 1 (by rfl) ⟨6868394, by rfl⟩ : syracuseStep 9157859 = 13736789) B13736789
theorem B1809715 : Blo 1607002 1809715 := bstep (se 1 (by rfl) ⟨1357286, by rfl⟩ : syracuseStep 1809715 = 2714573) B2714573
theorem B3259715 : Blo 1607002 3259715 := bstep (se 1 (by rfl) ⟨2444786, by rfl⟩ : syracuseStep 3259715 = 4889573) B4889573
theorem B7331149 : Blo 1607002 7331149 := bstep (se 3 (by rfl) ⟨1374590, by rfl⟩ : syracuseStep 7331149 = 2749181) B2749181
theorem B3620177 : Blo 1607002 3620177 := bstep (se 2 (by rfl) ⟨1357566, by rfl⟩ : syracuseStep 3620177 = 2715133) B2715133
theorem B3620195 : Blo 1607002 3620195 := bstep (se 1 (by rfl) ⟨2715146, by rfl⟩ : syracuseStep 3620195 = 5430293) B5430293
theorem B1809859 : Blo 1607002 1809859 := bstep (se 1 (by rfl) ⟨1357394, by rfl⟩ : syracuseStep 1809859 = 2714789) B2714789
theorem B18316853 : Blo 1607002 18316853 := bstep (se 5 (by rfl) ⟨858602, by rfl⟩ : syracuseStep 18316853 = 1717205) B1717205
theorem B1810003 : Blo 1607002 1810003 := bstep (se 1 (by rfl) ⟨1357502, by rfl⟩ : syracuseStep 1810003 = 2715005) B2715005
theorem B6102641 : Blo 1607002 6102641 := bstep (se 2 (by rfl) ⟨2288490, by rfl⟩ : syracuseStep 6102641 = 4576981) B4576981
theorem B3669617 : Blo 1607002 3669617 := bstep (se 2 (by rfl) ⟨1376106, by rfl⟩ : syracuseStep 3669617 = 2752213) B2752213
theorem B8814221 : Blo 1607002 8814221 := bstep (se 3 (by rfl) ⟨1652666, by rfl⟩ : syracuseStep 8814221 = 3305333) B3305333
theorem B8142605 : Blo 1607002 8142605 := bstep (se 3 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 8142605 = 3053477) B3053477
theorem B35249941 : Blo 1607002 35249941 := bstep (se 6 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 35249941 = 1652341) B1652341
theorem B3727171 : Blo 1607002 3727171 := bstep (se 1 (by rfl) ⟨2795378, by rfl⟩ : syracuseStep 3727171 = 5590757) B5590757
theorem B46382989 : Blo 1607002 46382989 := bstep (se 3 (by rfl) ⟨8696810, by rfl⟩ : syracuseStep 46382989 = 17393621) B17393621
theorem B7724963 : Blo 1607002 7724963 := bstep (se 1 (by rfl) ⟨5793722, by rfl⟩ : syracuseStep 7724963 = 11587445) B11587445
theorem B14106629 : Blo 1607002 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B7643315 : Blo 1607002 7643315 := bstep (se 1 (by rfl) ⟨5732486, by rfl⟩ : syracuseStep 7643315 = 11464973) B11464973
theorem B4071617 : Blo 1607002 4071617 := bstep (se 2 (by rfl) ⟨1526856, by rfl⟩ : syracuseStep 4071617 = 3053713) B3053713
theorem B2711819 : Blo 1607002 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B2711947 : Blo 1607002 2711947 := bstep (se 1 (by rfl) ⟨2033960, by rfl⟩ : syracuseStep 2711947 = 4067921) B4067921
theorem B2712089 : Blo 1607002 2712089 := bstep (se 2 (by rfl) ⟨1017033, by rfl⟩ : syracuseStep 2712089 = 2034067) B2034067
theorem B5423705 : Blo 1607002 5423705 := bstep (se 2 (by rfl) ⟨2033889, by rfl⟩ : syracuseStep 5423705 = 4067779) B4067779
theorem B2712217 : Blo 1607002 2712217 := bstep (se 2 (by rfl) ⟨1017081, by rfl⟩ : syracuseStep 2712217 = 2034163) B2034163
theorem B4580057 : Blo 1607002 4580057 := bstep (se 2 (by rfl) ⟨1717521, by rfl⟩ : syracuseStep 4580057 = 3435043) B3435043
theorem B8143577 : Blo 1607002 8143577 := bstep (se 2 (by rfl) ⟨3053841, by rfl⟩ : syracuseStep 8143577 = 6107683) B6107683
theorem B4072153 : Blo 1607002 4072153 := bstep (se 2 (by rfl) ⟨1527057, by rfl⟩ : syracuseStep 4072153 = 3054115) B3054115
theorem B3433241 : Blo 1607002 3433241 := bstep (se 2 (by rfl) ⟨1287465, by rfl⟩ : syracuseStep 3433241 = 2574931) B2574931
theorem B4580171 : Blo 1607002 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B6865985 : Blo 1607002 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B6186077 : Blo 1607002 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B10183781 : Blo 1607002 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B6522029 : Blo 1607002 6522029 := bstep (se 3 (by rfl) ⟨1222880, by rfl⟩ : syracuseStep 6522029 = 2445761) B2445761
theorem B6104267 : Blo 1607002 6104267 := bstep (se 1 (by rfl) ⟨4578200, by rfl⟩ : syracuseStep 6104267 = 9156401) B9156401
theorem B2712791 : Blo 1607002 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B6104281 : Blo 1607002 6104281 := bstep (se 2 (by rfl) ⟨2289105, by rfl⟩ : syracuseStep 6104281 = 4578211) B4578211
theorem B26076421 : Blo 1607002 26076421 := bstep (se 4 (by rfl) ⟨2444664, by rfl⟩ : syracuseStep 26076421 = 4889329) B4889329
theorem B5424407 : Blo 1607002 5424407 := bstep (se 1 (by rfl) ⟨4068305, by rfl⟩ : syracuseStep 5424407 = 8136611) B8136611
theorem B2712919 : Blo 1607002 2712919 := bstep (se 1 (by rfl) ⟨2034689, by rfl⟩ : syracuseStep 2712919 = 4069379) B4069379
theorem B1607019 : Blo 1607002 1607019 := bstep (se 1 (by rfl) ⟨1205264, by rfl⟩ : syracuseStep 1607019 = 2410529) B2410529
theorem B3482995 : Blo 1607002 3482995 := bstep (se 1 (by rfl) ⟨2612246, by rfl⟩ : syracuseStep 3482995 = 5224493) B5224493
theorem B1607031 : Blo 1607002 1607031 := bstep (se 1 (by rfl) ⟨1205273, by rfl⟩ : syracuseStep 1607031 = 2410547) B2410547
theorem B9160067 : Blo 1607002 9160067 := bstep (se 1 (by rfl) ⟨6870050, by rfl⟩ : syracuseStep 9160067 = 13740101) B13740101
theorem B1607051 : Blo 1607002 1607051 := bstep (se 1 (by rfl) ⟨1205288, by rfl⟩ : syracuseStep 1607051 = 2410577) B2410577
theorem B1607063 : Blo 1607002 1607063 := bstep (se 1 (by rfl) ⟨1205297, by rfl⟩ : syracuseStep 1607063 = 2410595) B2410595
theorem B1607083 : Blo 1607002 1607083 := bstep (se 1 (by rfl) ⟨1205312, by rfl⟩ : syracuseStep 1607083 = 2410625) B2410625
theorem B1607095 : Blo 1607002 1607095 := bstep (se 1 (by rfl) ⟨1205321, by rfl⟩ : syracuseStep 1607095 = 2410643) B2410643
theorem B1607115 : Blo 1607002 1607115 := bstep (se 1 (by rfl) ⟨1205336, by rfl⟩ : syracuseStep 1607115 = 2410673) B2410673
theorem B1607127 : Blo 1607002 1607127 := bstep (se 1 (by rfl) ⟨1205345, by rfl⟩ : syracuseStep 1607127 = 2410691) B2410691
theorem B46368227 : Blo 1607002 46368227 := bstep (se 1 (by rfl) ⟨34776170, by rfl⟩ : syracuseStep 46368227 = 69552341) B69552341
theorem B1607147 : Blo 1607002 1607147 := bstep (se 1 (by rfl) ⟨1205360, by rfl⟩ : syracuseStep 1607147 = 2410721) B2410721
theorem B1607159 : Blo 1607002 1607159 := bstep (se 1 (by rfl) ⟨1205369, by rfl⟩ : syracuseStep 1607159 = 2410739) B2410739
theorem B1607179 : Blo 1607002 1607179 := bstep (se 1 (by rfl) ⟨1205384, by rfl⟩ : syracuseStep 1607179 = 2410769) B2410769
theorem B9782801 : Blo 1607002 9782801 := bstep (se 2 (by rfl) ⟨3668550, by rfl⟩ : syracuseStep 9782801 = 7337101) B7337101
theorem B1607191 : Blo 1607002 1607191 := bstep (se 1 (by rfl) ⟨1205393, by rfl⟩ : syracuseStep 1607191 = 2410787) B2410787
theorem B1607211 : Blo 1607002 1607211 := bstep (se 1 (by rfl) ⟨1205408, by rfl⟩ : syracuseStep 1607211 = 2410817) B2410817
theorem B3434035 : Blo 1607002 3434035 := bstep (se 1 (by rfl) ⟨2575526, by rfl⟩ : syracuseStep 3434035 = 5151053) B5151053
theorem B1607223 : Blo 1607002 1607223 := bstep (se 1 (by rfl) ⟨1205417, by rfl⟩ : syracuseStep 1607223 = 2410835) B2410835
theorem B1607243 : Blo 1607002 1607243 := bstep (se 1 (by rfl) ⟨1205432, by rfl⟩ : syracuseStep 1607243 = 2410865) B2410865
theorem B1607255 : Blo 1607002 1607255 := bstep (se 1 (by rfl) ⟨1205441, by rfl⟩ : syracuseStep 1607255 = 2410883) B2410883
theorem B1607275 : Blo 1607002 1607275 := bstep (se 1 (by rfl) ⟨1205456, by rfl⟩ : syracuseStep 1607275 = 2410913) B2410913
theorem B1607287 : Blo 1607002 1607287 := bstep (se 1 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 1607287 = 2410931) B2410931
theorem B1607307 : Blo 1607002 1607307 := bstep (se 1 (by rfl) ⟨1205480, by rfl⟩ : syracuseStep 1607307 = 2410961) B2410961
theorem B1607319 : Blo 1607002 1607319 := bstep (se 1 (by rfl) ⟨1205489, by rfl⟩ : syracuseStep 1607319 = 2410979) B2410979
theorem B1607339 : Blo 1607002 1607339 := bstep (se 1 (by rfl) ⟨1205504, by rfl⟩ : syracuseStep 1607339 = 2411009) B2411009
theorem B6612653 : Blo 1607002 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B1607351 : Blo 1607002 1607351 := bstep (se 1 (by rfl) ⟨1205513, by rfl⟩ : syracuseStep 1607351 = 2411027) B2411027
theorem B1607371 : Blo 1607002 1607371 := bstep (se 1 (by rfl) ⟨1205528, by rfl⟩ : syracuseStep 1607371 = 2411057) B2411057
theorem B1607383 : Blo 1607002 1607383 := bstep (se 1 (by rfl) ⟨1205537, by rfl⟩ : syracuseStep 1607383 = 2411075) B2411075
theorem B12207833 : Blo 1607002 12207833 := bstep (se 2 (by rfl) ⟨4577937, by rfl⟩ : syracuseStep 12207833 = 9155875) B9155875
theorem B1607403 : Blo 1607002 1607403 := bstep (se 1 (by rfl) ⟨1205552, by rfl⟩ : syracuseStep 1607403 = 2411105) B2411105
theorem B1607415 : Blo 1607002 1607415 := bstep (se 1 (by rfl) ⟨1205561, by rfl⟩ : syracuseStep 1607415 = 2411123) B2411123
theorem B1607435 : Blo 1607002 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B9774865 : Blo 1607002 9774865 := bstep (se 2 (by rfl) ⟨3665574, by rfl⟩ : syracuseStep 9774865 = 7331149) B7331149
theorem B1607447 : Blo 1607002 1607447 := bstep (se 1 (by rfl) ⟨1205585, by rfl⟩ : syracuseStep 1607447 = 2411171) B2411171
theorem B2320153 : Blo 1607002 2320153 := bstep (se 2 (by rfl) ⟨870057, by rfl⟩ : syracuseStep 2320153 = 1740115) B1740115
theorem B1607467 : Blo 1607002 1607467 := bstep (se 1 (by rfl) ⟨1205600, by rfl⟩ : syracuseStep 1607467 = 2411201) B2411201
theorem B17393453 : Blo 1607002 17393453 := bstep (se 3 (by rfl) ⟨3261272, by rfl⟩ : syracuseStep 17393453 = 6522545) B6522545
theorem B5424947 : Blo 1607002 5424947 := bstep (se 1 (by rfl) ⟨4068710, by rfl⟩ : syracuseStep 5424947 = 8137421) B8137421
theorem B1607479 : Blo 1607002 1607479 := bstep (se 1 (by rfl) ⟨1205609, by rfl⟩ : syracuseStep 1607479 = 2411219) B2411219
theorem B1607499 : Blo 1607002 1607499 := bstep (se 1 (by rfl) ⟨1205624, by rfl⟩ : syracuseStep 1607499 = 2411249) B2411249
theorem B9160523 : Blo 1607002 9160523 := bstep (se 1 (by rfl) ⟨6870392, by rfl⟩ : syracuseStep 9160523 = 13740785) B13740785
theorem B1607511 : Blo 1607002 1607511 := bstep (se 1 (by rfl) ⟨1205633, by rfl⟩ : syracuseStep 1607511 = 2411267) B2411267
theorem B1607531 : Blo 1607002 1607531 := bstep (se 1 (by rfl) ⟨1205648, by rfl⟩ : syracuseStep 1607531 = 2411297) B2411297
theorem B1607543 : Blo 1607002 1607543 := bstep (se 1 (by rfl) ⟨1205657, by rfl⟩ : syracuseStep 1607543 = 2411315) B2411315
theorem B1607563 : Blo 1607002 1607563 := bstep (se 1 (by rfl) ⟨1205672, by rfl⟩ : syracuseStep 1607563 = 2411345) B2411345
theorem B1607575 : Blo 1607002 1607575 := bstep (se 1 (by rfl) ⟨1205681, by rfl⟩ : syracuseStep 1607575 = 2411363) B2411363
theorem B1607595 : Blo 1607002 1607595 := bstep (se 1 (by rfl) ⟨1205696, by rfl⟩ : syracuseStep 1607595 = 2411393) B2411393
theorem B5957549 : Blo 1607002 5957549 := bstep (se 3 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 5957549 = 2234081) B2234081
theorem B4581299 : Blo 1607002 4581299 := bstep (se 1 (by rfl) ⟨3435974, by rfl⟩ : syracuseStep 4581299 = 6871949) B6871949
theorem B1607607 : Blo 1607002 1607607 := bstep (se 1 (by rfl) ⟨1205705, by rfl⟩ : syracuseStep 1607607 = 2411411) B2411411
theorem B1607627 : Blo 1607002 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B2713547 : Blo 1607002 2713547 := bstep (se 1 (by rfl) ⟨2035160, by rfl⟩ : syracuseStep 2713547 = 4070321) B4070321
theorem B1607639 : Blo 1607002 1607639 := bstep (se 1 (by rfl) ⟨1205729, by rfl⟩ : syracuseStep 1607639 = 2411459) B2411459
theorem B1607659 : Blo 1607002 1607659 := bstep (se 1 (by rfl) ⟨1205744, by rfl⟩ : syracuseStep 1607659 = 2411489) B2411489
theorem B1607671 : Blo 1607002 1607671 := bstep (se 1 (by rfl) ⟨1205753, by rfl⟩ : syracuseStep 1607671 = 2411507) B2411507
theorem B2574347 : Blo 1607002 2574347 := bstep (se 1 (by rfl) ⟨1930760, by rfl⟩ : syracuseStep 2574347 = 3861521) B3861521
theorem B1607691 : Blo 1607002 1607691 := bstep (se 1 (by rfl) ⟨1205768, by rfl⟩ : syracuseStep 1607691 = 2411537) B2411537
theorem B1607703 : Blo 1607002 1607703 := bstep (se 1 (by rfl) ⟨1205777, by rfl⟩ : syracuseStep 1607703 = 2411555) B2411555
theorem B1607723 : Blo 1607002 1607723 := bstep (se 1 (by rfl) ⟨1205792, by rfl⟩ : syracuseStep 1607723 = 2411585) B2411585
theorem B1607735 : Blo 1607002 1607735 := bstep (se 1 (by rfl) ⟨1205801, by rfl⟩ : syracuseStep 1607735 = 2411603) B2411603
theorem B5425217 : Blo 1607002 5425217 := bstep (se 2 (by rfl) ⟨2034456, by rfl⟩ : syracuseStep 5425217 = 4068913) B4068913
theorem B2410571 : Blo 1607002 2410571 := bstep (se 1 (by rfl) ⟨1807928, by rfl⟩ : syracuseStep 2410571 = 3615857) B3615857
theorem B1607755 : Blo 1607002 1607755 := bstep (se 1 (by rfl) ⟨1205816, by rfl⟩ : syracuseStep 1607755 = 2411633) B2411633
theorem B2713675 : Blo 1607002 2713675 := bstep (se 1 (by rfl) ⟨2035256, by rfl⟩ : syracuseStep 2713675 = 4070513) B4070513
theorem B2410583 : Blo 1607002 2410583 := bstep (se 1 (by rfl) ⟨1807937, by rfl⟩ : syracuseStep 2410583 = 3615875) B3615875
theorem B1607767 : Blo 1607002 1607767 := bstep (se 1 (by rfl) ⟨1205825, by rfl⟩ : syracuseStep 1607767 = 2411651) B2411651
theorem B1607787 : Blo 1607002 1607787 := bstep (se 1 (by rfl) ⟨1205840, by rfl⟩ : syracuseStep 1607787 = 2411681) B2411681
theorem B1607799 : Blo 1607002 1607799 := bstep (se 1 (by rfl) ⟨1205849, by rfl⟩ : syracuseStep 1607799 = 2411699) B2411699
theorem B1607819 : Blo 1607002 1607819 := bstep (se 1 (by rfl) ⟨1205864, by rfl⟩ : syracuseStep 1607819 = 2411729) B2411729
theorem B1607831 : Blo 1607002 1607831 := bstep (se 1 (by rfl) ⟨1205873, by rfl⟩ : syracuseStep 1607831 = 2411747) B2411747
theorem B6105239 : Blo 1607002 6105239 := bstep (se 1 (by rfl) ⟨4578929, by rfl⟩ : syracuseStep 6105239 = 9157859) B9157859
theorem B2410649 : Blo 1607002 2410649 := bstep (se 2 (by rfl) ⟨903993, by rfl⟩ : syracuseStep 2410649 = 1807987) B1807987
theorem B1607851 : Blo 1607002 1607851 := bstep (se 1 (by rfl) ⟨1205888, by rfl⟩ : syracuseStep 1607851 = 2411777) B2411777
theorem B1607863 : Blo 1607002 1607863 := bstep (se 1 (by rfl) ⟨1205897, by rfl⟩ : syracuseStep 1607863 = 2411795) B2411795
theorem B1607883 : Blo 1607002 1607883 := bstep (se 1 (by rfl) ⟨1205912, by rfl⟩ : syracuseStep 1607883 = 2411825) B2411825
theorem B1607895 : Blo 1607002 1607895 := bstep (se 1 (by rfl) ⟨1205921, by rfl⟩ : syracuseStep 1607895 = 2411843) B2411843
theorem B2713817 : Blo 1607002 2713817 := bstep (se 2 (by rfl) ⟨1017681, by rfl⟩ : syracuseStep 2713817 = 2035363) B2035363
theorem B1607915 : Blo 1607002 1607915 := bstep (se 1 (by rfl) ⟨1205936, by rfl⟩ : syracuseStep 1607915 = 2411873) B2411873
theorem B1607927 : Blo 1607002 1607927 := bstep (se 1 (by rfl) ⟨1205945, by rfl⟩ : syracuseStep 1607927 = 2411891) B2411891
theorem B12216581 : Blo 1607002 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B2410763 : Blo 1607002 2410763 := bstep (se 1 (by rfl) ⟨1808072, by rfl⟩ : syracuseStep 2410763 = 3616145) B3616145
theorem B1607947 : Blo 1607002 1607947 := bstep (se 1 (by rfl) ⟨1205960, by rfl⟩ : syracuseStep 1607947 = 2411921) B2411921
theorem B2410775 : Blo 1607002 2410775 := bstep (se 1 (by rfl) ⟨1808081, by rfl⟩ : syracuseStep 2410775 = 3616163) B3616163
theorem B1607959 : Blo 1607002 1607959 := bstep (se 1 (by rfl) ⟨1205969, by rfl⟩ : syracuseStep 1607959 = 2411939) B2411939
theorem B1607979 : Blo 1607002 1607979 := bstep (se 1 (by rfl) ⟨1205984, by rfl⟩ : syracuseStep 1607979 = 2411969) B2411969
theorem B8145197 : Blo 1607002 8145197 := bstep (se 3 (by rfl) ⟨1527224, by rfl⟩ : syracuseStep 8145197 = 3054449) B3054449
theorem B1607991 : Blo 1607002 1607991 := bstep (se 1 (by rfl) ⟨1205993, by rfl⟩ : syracuseStep 1607991 = 2411987) B2411987
theorem B4581697 : Blo 1607002 4581697 := bstep (se 2 (by rfl) ⟨1718136, by rfl⟩ : syracuseStep 4581697 = 3436273) B3436273
theorem B1608011 : Blo 1607002 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B1608023 : Blo 1607002 1608023 := bstep (se 1 (by rfl) ⟨1206017, by rfl⟩ : syracuseStep 1608023 = 2412035) B2412035
theorem B2410841 : Blo 1607002 2410841 := bstep (se 2 (by rfl) ⟨904065, by rfl⟩ : syracuseStep 2410841 = 1808131) B1808131
theorem B2713945 : Blo 1607002 2713945 := bstep (se 2 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 2713945 = 2035459) B2035459
theorem B1608043 : Blo 1607002 1608043 := bstep (se 1 (by rfl) ⟨1206032, by rfl⟩ : syracuseStep 1608043 = 2412065) B2412065
theorem B46999921 : Blo 1607002 46999921 := bstep (se 2 (by rfl) ⟨17624970, by rfl⟩ : syracuseStep 46999921 = 35249941) B35249941
theorem B1608055 : Blo 1607002 1608055 := bstep (se 1 (by rfl) ⟨1206041, by rfl⟩ : syracuseStep 1608055 = 2412083) B2412083
theorem B3434881 : Blo 1607002 3434881 := bstep (se 2 (by rfl) ⟨1288080, by rfl⟩ : syracuseStep 3434881 = 2576161) B2576161
theorem B1608075 : Blo 1607002 1608075 := bstep (se 1 (by rfl) ⟨1206056, by rfl⟩ : syracuseStep 1608075 = 2412113) B2412113
theorem B1608087 : Blo 1607002 1608087 := bstep (se 1 (by rfl) ⟨1206065, by rfl⟩ : syracuseStep 1608087 = 2412131) B2412131
theorem B1608107 : Blo 1607002 1608107 := bstep (se 1 (by rfl) ⟨1206080, by rfl⟩ : syracuseStep 1608107 = 2412161) B2412161
theorem B5876147 : Blo 1607002 5876147 := bstep (se 1 (by rfl) ⟨4407110, by rfl⟩ : syracuseStep 5876147 = 8814221) B8814221
theorem B1608119 : Blo 1607002 1608119 := bstep (se 1 (by rfl) ⟨1206089, by rfl⟩ : syracuseStep 1608119 = 2412179) B2412179
theorem B2410955 : Blo 1607002 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B1608139 : Blo 1607002 1608139 := bstep (se 1 (by rfl) ⟨1206104, by rfl⟩ : syracuseStep 1608139 = 2412209) B2412209
theorem B2410967 : Blo 1607002 2410967 := bstep (se 1 (by rfl) ⟨1808225, by rfl⟩ : syracuseStep 2410967 = 3616451) B3616451
theorem B1608151 : Blo 1607002 1608151 := bstep (se 1 (by rfl) ⟨1206113, by rfl⟩ : syracuseStep 1608151 = 2412227) B2412227
theorem B1608171 : Blo 1607002 1608171 := bstep (se 1 (by rfl) ⟨1206128, by rfl⟩ : syracuseStep 1608171 = 2412257) B2412257
theorem B1608183 : Blo 1607002 1608183 := bstep (se 1 (by rfl) ⟨1206137, by rfl⟩ : syracuseStep 1608183 = 2412275) B2412275
theorem B1608203 : Blo 1607002 1608203 := bstep (se 1 (by rfl) ⟨1206152, by rfl⟩ : syracuseStep 1608203 = 2412305) B2412305
theorem B61843985 : Blo 1607002 61843985 := bstep (se 2 (by rfl) ⟨23191494, by rfl⟩ : syracuseStep 61843985 = 46382989) B46382989
theorem B1608215 : Blo 1607002 1608215 := bstep (se 1 (by rfl) ⟨1206161, by rfl⟩ : syracuseStep 1608215 = 2412323) B2412323
theorem B2411033 : Blo 1607002 2411033 := bstep (se 2 (by rfl) ⟨904137, by rfl⟩ : syracuseStep 2411033 = 1808275) B1808275
theorem B1608235 : Blo 1607002 1608235 := bstep (se 1 (by rfl) ⟨1206176, by rfl⟩ : syracuseStep 1608235 = 2412353) B2412353
theorem B1608247 : Blo 1607002 1608247 := bstep (se 1 (by rfl) ⟨1206185, by rfl⟩ : syracuseStep 1608247 = 2412371) B2412371
theorem B1608267 : Blo 1607002 1608267 := bstep (se 1 (by rfl) ⟨1206200, by rfl⟩ : syracuseStep 1608267 = 2412401) B2412401
theorem B1608279 : Blo 1607002 1608279 := bstep (se 1 (by rfl) ⟨1206209, by rfl⟩ : syracuseStep 1608279 = 2412419) B2412419
theorem B5425757 : Blo 1607002 5425757 := bstep (se 3 (by rfl) ⟨1017329, by rfl⟩ : syracuseStep 5425757 = 2034659) B2034659
theorem B1608299 : Blo 1607002 1608299 := bstep (se 1 (by rfl) ⟨1206224, by rfl⟩ : syracuseStep 1608299 = 2412449) B2412449
theorem B1608311 : Blo 1607002 1608311 := bstep (se 1 (by rfl) ⟨1206233, by rfl⟩ : syracuseStep 1608311 = 2412467) B2412467
theorem B11586179 : Blo 1607002 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B2411147 : Blo 1607002 2411147 := bstep (se 1 (by rfl) ⟨1808360, by rfl⟩ : syracuseStep 2411147 = 3616721) B3616721
theorem B1608331 : Blo 1607002 1608331 := bstep (se 1 (by rfl) ⟨1206248, by rfl⟩ : syracuseStep 1608331 = 2412497) B2412497
theorem B2411159 : Blo 1607002 2411159 := bstep (se 1 (by rfl) ⟨1808369, by rfl⟩ : syracuseStep 2411159 = 3616739) B3616739
theorem B1608343 : Blo 1607002 1608343 := bstep (se 1 (by rfl) ⟨1206257, by rfl⟩ : syracuseStep 1608343 = 2412515) B2412515
theorem B1608363 : Blo 1607002 1608363 := bstep (se 1 (by rfl) ⟨1206272, by rfl⟩ : syracuseStep 1608363 = 2412545) B2412545
theorem B1608375 : Blo 1607002 1608375 := bstep (se 1 (by rfl) ⟨1206281, by rfl⟩ : syracuseStep 1608375 = 2412563) B2412563
theorem B6867659 : Blo 1607002 6867659 := bstep (se 1 (by rfl) ⟨5150744, by rfl⟩ : syracuseStep 6867659 = 10301489) B10301489
theorem B1608395 : Blo 1607002 1608395 := bstep (se 1 (by rfl) ⟨1206296, by rfl⟩ : syracuseStep 1608395 = 2412593) B2412593
theorem B2034391 : Blo 1607002 2034391 := bstep (se 1 (by rfl) ⟨1525793, by rfl⟩ : syracuseStep 2034391 = 3051587) B3051587
theorem B1608407 : Blo 1607002 1608407 := bstep (se 1 (by rfl) ⟨1206305, by rfl⟩ : syracuseStep 1608407 = 2412611) B2412611
theorem B2411225 : Blo 1607002 2411225 := bstep (se 2 (by rfl) ⟨904209, by rfl⟩ : syracuseStep 2411225 = 1808419) B1808419
theorem B3435223 : Blo 1607002 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B1608427 : Blo 1607002 1608427 := bstep (se 1 (by rfl) ⟨1206320, by rfl⟩ : syracuseStep 1608427 = 2412641) B2412641
theorem B1608439 : Blo 1607002 1608439 := bstep (se 1 (by rfl) ⟨1206329, by rfl⟩ : syracuseStep 1608439 = 2412659) B2412659
theorem B14666501 : Blo 1607002 14666501 := bstep (se 4 (by rfl) ⟨1374984, by rfl⟩ : syracuseStep 14666501 = 2749969) B2749969
theorem B1608459 : Blo 1607002 1608459 := bstep (se 1 (by rfl) ⟨1206344, by rfl⟩ : syracuseStep 1608459 = 2412689) B2412689
theorem B1608471 : Blo 1607002 1608471 := bstep (se 1 (by rfl) ⟨1206353, by rfl⟩ : syracuseStep 1608471 = 2412707) B2412707
theorem B1608491 : Blo 1607002 1608491 := bstep (se 1 (by rfl) ⟨1206368, by rfl⟩ : syracuseStep 1608491 = 2412737) B2412737
theorem B1608503 : Blo 1607002 1608503 := bstep (se 1 (by rfl) ⟨1206377, by rfl⟩ : syracuseStep 1608503 = 2412755) B2412755
theorem B8252225 : Blo 1607002 8252225 := bstep (se 2 (by rfl) ⟨3094584, by rfl⟩ : syracuseStep 8252225 = 6189169) B6189169
theorem B2411339 : Blo 1607002 2411339 := bstep (se 1 (by rfl) ⟨1808504, by rfl⟩ : syracuseStep 2411339 = 3617009) B3617009
theorem B1608523 : Blo 1607002 1608523 := bstep (se 1 (by rfl) ⟨1206392, by rfl⟩ : syracuseStep 1608523 = 2412785) B2412785
theorem B2411351 : Blo 1607002 2411351 := bstep (se 1 (by rfl) ⟨1808513, by rfl⟩ : syracuseStep 2411351 = 3617027) B3617027
theorem B1608535 : Blo 1607002 1608535 := bstep (se 1 (by rfl) ⟨1206401, by rfl⟩ : syracuseStep 1608535 = 2412803) B2412803
theorem B1608555 : Blo 1607002 1608555 := bstep (se 1 (by rfl) ⟨1206416, by rfl⟩ : syracuseStep 1608555 = 2412833) B2412833
theorem B1608567 : Blo 1607002 1608567 := bstep (se 1 (by rfl) ⟨1206425, by rfl⟩ : syracuseStep 1608567 = 2412851) B2412851
theorem B1608587 : Blo 1607002 1608587 := bstep (se 1 (by rfl) ⟨1206440, by rfl⟩ : syracuseStep 1608587 = 2412881) B2412881
theorem B1608599 : Blo 1607002 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B2714519 : Blo 1607002 2714519 := bstep (se 1 (by rfl) ⟨2035889, by rfl⟩ : syracuseStep 2714519 = 4071779) B4071779
theorem B2411417 : Blo 1607002 2411417 := bstep (se 2 (by rfl) ⟨904281, by rfl⟩ : syracuseStep 2411417 = 1808563) B1808563
theorem B1608619 : Blo 1607002 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B1608631 : Blo 1607002 1608631 := bstep (se 1 (by rfl) ⟨1206473, by rfl⟩ : syracuseStep 1608631 = 2412947) B2412947
theorem B1608651 : Blo 1607002 1608651 := bstep (se 1 (by rfl) ⟨1206488, by rfl⟩ : syracuseStep 1608651 = 2412977) B2412977
theorem B1608663 : Blo 1607002 1608663 := bstep (se 1 (by rfl) ⟨1206497, by rfl⟩ : syracuseStep 1608663 = 2412995) B2412995
theorem B11586521 : Blo 1607002 11586521 := bstep (se 2 (by rfl) ⟨4344945, by rfl⟩ : syracuseStep 11586521 = 8689891) B8689891
theorem B1608683 : Blo 1607002 1608683 := bstep (se 1 (by rfl) ⟨1206512, by rfl⟩ : syracuseStep 1608683 = 2413025) B2413025
theorem B1608695 : Blo 1607002 1608695 := bstep (se 1 (by rfl) ⟨1206521, by rfl⟩ : syracuseStep 1608695 = 2413043) B2413043
theorem B2411531 : Blo 1607002 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B1608715 : Blo 1607002 1608715 := bstep (se 1 (by rfl) ⟨1206536, by rfl⟩ : syracuseStep 1608715 = 2413073) B2413073
theorem B8137745 : Blo 1607002 8137745 := bstep (se 2 (by rfl) ⟨3051654, by rfl⟩ : syracuseStep 8137745 = 6103309) B6103309
theorem B3615767 : Blo 1607002 3615767 := bstep (se 1 (by rfl) ⟨2711825, by rfl⟩ : syracuseStep 3615767 = 5423651) B5423651
theorem B2411543 : Blo 1607002 2411543 := bstep (se 1 (by rfl) ⟨1808657, by rfl⟩ : syracuseStep 2411543 = 3617315) B3617315
theorem B2714647 : Blo 1607002 2714647 := bstep (se 1 (by rfl) ⟨2035985, by rfl⟩ : syracuseStep 2714647 = 4071971) B4071971
theorem B1608727 : Blo 1607002 1608727 := bstep (se 1 (by rfl) ⟨1206545, by rfl⟩ : syracuseStep 1608727 = 2413091) B2413091
theorem B1608747 : Blo 1607002 1608747 := bstep (se 1 (by rfl) ⟨1206560, by rfl⟩ : syracuseStep 1608747 = 2413121) B2413121
theorem B1608759 : Blo 1607002 1608759 := bstep (se 1 (by rfl) ⟨1206569, by rfl⟩ : syracuseStep 1608759 = 2413139) B2413139
theorem B1608779 : Blo 1607002 1608779 := bstep (se 1 (by rfl) ⟨1206584, by rfl⟩ : syracuseStep 1608779 = 2413169) B2413169
theorem B1608791 : Blo 1607002 1608791 := bstep (se 1 (by rfl) ⟨1206593, by rfl⟩ : syracuseStep 1608791 = 2413187) B2413187
theorem B2411609 : Blo 1607002 2411609 := bstep (se 2 (by rfl) ⟨904353, by rfl⟩ : syracuseStep 2411609 = 1808707) B1808707
theorem B1608811 : Blo 1607002 1608811 := bstep (se 1 (by rfl) ⟨1206608, by rfl⟩ : syracuseStep 1608811 = 2413217) B2413217
theorem B1608823 : Blo 1607002 1608823 := bstep (se 1 (by rfl) ⟨1206617, by rfl⟩ : syracuseStep 1608823 = 2413235) B2413235
theorem B1608843 : Blo 1607002 1608843 := bstep (se 1 (by rfl) ⟨1206632, by rfl⟩ : syracuseStep 1608843 = 2413265) B2413265
theorem B1608855 : Blo 1607002 1608855 := bstep (se 1 (by rfl) ⟨1206641, by rfl⟩ : syracuseStep 1608855 = 2413283) B2413283
theorem B1608875 : Blo 1607002 1608875 := bstep (se 1 (by rfl) ⟨1206656, by rfl⟩ : syracuseStep 1608875 = 2413313) B2413313
theorem B8137907 : Blo 1607002 8137907 := bstep (se 1 (by rfl) ⟨6103430, by rfl⟩ : syracuseStep 8137907 = 12206861) B12206861
theorem B1608887 : Blo 1607002 1608887 := bstep (se 1 (by rfl) ⟨1206665, by rfl⟩ : syracuseStep 1608887 = 2413331) B2413331
theorem B3615947 : Blo 1607002 3615947 := bstep (se 1 (by rfl) ⟨2711960, by rfl⟩ : syracuseStep 3615947 = 5423921) B5423921
theorem B2411723 : Blo 1607002 2411723 := bstep (se 1 (by rfl) ⟨1808792, by rfl⟩ : syracuseStep 2411723 = 3617585) B3617585
theorem B1608907 : Blo 1607002 1608907 := bstep (se 1 (by rfl) ⟨1206680, by rfl⟩ : syracuseStep 1608907 = 2413361) B2413361
theorem B2288855 : Blo 1607002 2288855 := bstep (se 1 (by rfl) ⟨1716641, by rfl⟩ : syracuseStep 2288855 = 3433283) B3433283
theorem B2411735 : Blo 1607002 2411735 := bstep (se 1 (by rfl) ⟨1808801, by rfl⟩ : syracuseStep 2411735 = 3617603) B3617603
theorem B1608919 : Blo 1607002 1608919 := bstep (se 1 (by rfl) ⟨1206689, by rfl⟩ : syracuseStep 1608919 = 2413379) B2413379
theorem B1608939 : Blo 1607002 1608939 := bstep (se 1 (by rfl) ⟨1206704, by rfl⟩ : syracuseStep 1608939 = 2413409) B2413409
theorem B1608951 : Blo 1607002 1608951 := bstep (se 1 (by rfl) ⟨1206713, by rfl⟩ : syracuseStep 1608951 = 2413427) B2413427
theorem B3616001 : Blo 1607002 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B1608971 : Blo 1607002 1608971 := bstep (se 1 (by rfl) ⟨1206728, by rfl⟩ : syracuseStep 1608971 = 2413457) B2413457
theorem B2411801 : Blo 1607002 2411801 := bstep (se 2 (by rfl) ⟨904425, by rfl⟩ : syracuseStep 2411801 = 1808851) B1808851
theorem B1608983 : Blo 1607002 1608983 := bstep (se 1 (by rfl) ⟨1206737, by rfl⟩ : syracuseStep 1608983 = 2413475) B2413475
theorem B15445313 : Blo 1607002 15445313 := bstep (se 2 (by rfl) ⟨5791992, by rfl⟩ : syracuseStep 15445313 = 11583985) B11583985
theorem B34770293 : Blo 1607002 34770293 := bstep (se 5 (by rfl) ⟨1629857, by rfl⟩ : syracuseStep 34770293 = 3259715) B3259715
theorem B6106499 : Blo 1607002 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B2411915 : Blo 1607002 2411915 := bstep (se 1 (by rfl) ⟨1808936, by rfl⟩ : syracuseStep 2411915 = 3617873) B3617873
theorem B2411927 : Blo 1607002 2411927 := bstep (se 1 (by rfl) ⟨1808945, by rfl⟩ : syracuseStep 2411927 = 3617891) B3617891
theorem B3616217 : Blo 1607002 3616217 := bstep (se 2 (by rfl) ⟨1356081, by rfl⟩ : syracuseStep 3616217 = 2712163) B2712163
theorem B2411993 : Blo 1607002 2411993 := bstep (se 2 (by rfl) ⟨904497, by rfl⟩ : syracuseStep 2411993 = 1808995) B1808995
theorem B2289163 : Blo 1607002 2289163 := bstep (se 1 (by rfl) ⟨1716872, by rfl⟩ : syracuseStep 2289163 = 3433745) B3433745
theorem B3616307 : Blo 1607002 3616307 := bstep (se 1 (by rfl) ⟨2712230, by rfl⟩ : syracuseStep 3616307 = 5424461) B5424461
theorem B2412107 : Blo 1607002 2412107 := bstep (se 1 (by rfl) ⟨1809080, by rfl⟩ : syracuseStep 2412107 = 3618161) B3618161
theorem B3616343 : Blo 1607002 3616343 := bstep (se 1 (by rfl) ⟨2712257, by rfl⟩ : syracuseStep 3616343 = 5424515) B5424515
theorem B2412119 : Blo 1607002 2412119 := bstep (se 1 (by rfl) ⟨1809089, by rfl⟩ : syracuseStep 2412119 = 3618179) B3618179
theorem B2412185 : Blo 1607002 2412185 := bstep (se 2 (by rfl) ⟨904569, by rfl⟩ : syracuseStep 2412185 = 1809139) B1809139
theorem B12242611 : Blo 1607002 12242611 := bstep (se 1 (by rfl) ⟨9181958, by rfl⟩ : syracuseStep 12242611 = 18363917) B18363917
theorem B5426891 : Blo 1607002 5426891 := bstep (se 1 (by rfl) ⟨4070168, by rfl⟩ : syracuseStep 5426891 = 8140337) B8140337
theorem B3616523 : Blo 1607002 3616523 := bstep (se 1 (by rfl) ⟨2712392, by rfl⟩ : syracuseStep 3616523 = 5424785) B5424785
theorem B2412299 : Blo 1607002 2412299 := bstep (se 1 (by rfl) ⟨1809224, by rfl⟩ : syracuseStep 2412299 = 3618449) B3618449
theorem B2412311 : Blo 1607002 2412311 := bstep (se 1 (by rfl) ⟨1809233, by rfl⟩ : syracuseStep 2412311 = 3618467) B3618467
theorem B3616577 : Blo 1607002 3616577 := bstep (se 2 (by rfl) ⟨1356216, by rfl⟩ : syracuseStep 3616577 = 2712433) B2712433
theorem B7728961 : Blo 1607002 7728961 := bstep (se 2 (by rfl) ⟨2898360, by rfl⟩ : syracuseStep 7728961 = 5796721) B5796721
theorem B2412377 : Blo 1607002 2412377 := bstep (se 2 (by rfl) ⟨904641, by rfl⟩ : syracuseStep 2412377 = 1809283) B1809283
theorem B10301363 : Blo 1607002 10301363 := bstep (se 1 (by rfl) ⟨7726022, by rfl⟩ : syracuseStep 10301363 = 15452045) B15452045
theorem B26079155 : Blo 1607002 26079155 := bstep (se 1 (by rfl) ⟨19559366, by rfl⟩ : syracuseStep 26079155 = 39118733) B39118733
theorem B2412491 : Blo 1607002 2412491 := bstep (se 1 (by rfl) ⟨1809368, by rfl⟩ : syracuseStep 2412491 = 3618737) B3618737
theorem B2412503 : Blo 1607002 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B5427161 : Blo 1607002 5427161 := bstep (se 2 (by rfl) ⟨2035185, by rfl⟩ : syracuseStep 5427161 = 4070371) B4070371
theorem B6868957 : Blo 1607002 6868957 := bstep (se 3 (by rfl) ⟨1287929, by rfl⟩ : syracuseStep 6868957 = 2575859) B2575859
theorem B3616793 : Blo 1607002 3616793 := bstep (se 2 (by rfl) ⟨1356297, by rfl⟩ : syracuseStep 3616793 = 2712595) B2712595
theorem B2412569 : Blo 1607002 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B3862579 : Blo 1607002 3862579 := bstep (se 1 (by rfl) ⟨2896934, by rfl⟩ : syracuseStep 3862579 = 5793869) B5793869
theorem B61804619 : Blo 1607002 61804619 := bstep (se 1 (by rfl) ⟨46353464, by rfl⟩ : syracuseStep 61804619 = 92706929) B92706929
theorem B11006027 : Blo 1607002 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B3616883 : Blo 1607002 3616883 := bstep (se 1 (by rfl) ⟨2712662, by rfl⟩ : syracuseStep 3616883 = 5425325) B5425325
theorem B9154691 : Blo 1607002 9154691 := bstep (se 1 (by rfl) ⟨6866018, by rfl⟩ : syracuseStep 9154691 = 13732037) B13732037
theorem B2412683 : Blo 1607002 2412683 := bstep (se 1 (by rfl) ⟨1809512, by rfl⟩ : syracuseStep 2412683 = 3619025) B3619025
theorem B3616919 : Blo 1607002 3616919 := bstep (se 1 (by rfl) ⟨2712689, by rfl⟩ : syracuseStep 3616919 = 5425379) B5425379
theorem B2412695 : Blo 1607002 2412695 := bstep (se 1 (by rfl) ⟨1809521, by rfl⟩ : syracuseStep 2412695 = 3619043) B3619043
theorem B11595953 : Blo 1607002 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B7336115 : Blo 1607002 7336115 := bstep (se 1 (by rfl) ⟨5502086, by rfl⟩ : syracuseStep 7336115 = 11004173) B11004173
theorem B3666113 : Blo 1607002 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B2412761 : Blo 1607002 2412761 := bstep (se 2 (by rfl) ⟨904785, by rfl⟩ : syracuseStep 2412761 = 1809571) B1809571
theorem B3092737 : Blo 1607002 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B6869299 : Blo 1607002 6869299 := bstep (se 1 (by rfl) ⟨5151974, by rfl⟩ : syracuseStep 6869299 = 10303949) B10303949
theorem B3617099 : Blo 1607002 3617099 := bstep (se 1 (by rfl) ⟨2712824, by rfl⟩ : syracuseStep 3617099 = 5425649) B5425649
theorem B2412875 : Blo 1607002 2412875 := bstep (se 1 (by rfl) ⟨1809656, by rfl⟩ : syracuseStep 2412875 = 3619313) B3619313
theorem B2412887 : Blo 1607002 2412887 := bstep (se 1 (by rfl) ⟨1809665, by rfl⟩ : syracuseStep 2412887 = 3619331) B3619331
theorem B1716599 : Blo 1607002 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B3617153 : Blo 1607002 3617153 := bstep (se 2 (by rfl) ⟨1356432, by rfl⟩ : syracuseStep 3617153 = 2712865) B2712865
theorem B2036107 : Blo 1607002 2036107 := bstep (se 1 (by rfl) ⟨1527080, by rfl⟩ : syracuseStep 2036107 = 3054161) B3054161
theorem B5149079 : Blo 1607002 5149079 := bstep (se 1 (by rfl) ⟨3861809, by rfl⟩ : syracuseStep 5149079 = 7723619) B7723619
theorem B2412953 : Blo 1607002 2412953 := bstep (se 2 (by rfl) ⟨904857, by rfl⟩ : syracuseStep 2412953 = 1809715) B1809715
theorem B17633713 : Blo 1607002 17633713 := bstep (se 2 (by rfl) ⟨6612642, by rfl⟩ : syracuseStep 17633713 = 13225285) B13225285
theorem B3052019 : Blo 1607002 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B2413067 : Blo 1607002 2413067 := bstep (se 1 (by rfl) ⟨1809800, by rfl⟩ : syracuseStep 2413067 = 3619601) B3619601
theorem B2290199 : Blo 1607002 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B2413079 : Blo 1607002 2413079 := bstep (se 1 (by rfl) ⟨1809809, by rfl⟩ : syracuseStep 2413079 = 3619619) B3619619
theorem B4067891 : Blo 1607002 4067891 := bstep (se 1 (by rfl) ⟨3050918, by rfl⟩ : syracuseStep 4067891 = 6101837) B6101837
theorem B3617369 : Blo 1607002 3617369 := bstep (se 2 (by rfl) ⟨1356513, by rfl⟩ : syracuseStep 3617369 = 2713027) B2713027
theorem B2413145 : Blo 1607002 2413145 := bstep (se 2 (by rfl) ⟨904929, by rfl⟩ : syracuseStep 2413145 = 1809859) B1809859
theorem B3052171 : Blo 1607002 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B5427863 : Blo 1607002 5427863 := bstep (se 1 (by rfl) ⟨4070897, by rfl⟩ : syracuseStep 5427863 = 8141795) B8141795
theorem B3617459 : Blo 1607002 3617459 := bstep (se 1 (by rfl) ⟨2713094, by rfl⟩ : syracuseStep 3617459 = 5426189) B5426189
theorem B2413259 : Blo 1607002 2413259 := bstep (se 1 (by rfl) ⟨1809944, by rfl⟩ : syracuseStep 2413259 = 3619889) B3619889
theorem B3617495 : Blo 1607002 3617495 := bstep (se 1 (by rfl) ⟨2713121, by rfl⟩ : syracuseStep 3617495 = 5426243) B5426243
theorem B2413271 : Blo 1607002 2413271 := bstep (se 1 (by rfl) ⟨1809953, by rfl⟩ : syracuseStep 2413271 = 3619907) B3619907
theorem B2290393 : Blo 1607002 2290393 := bstep (se 2 (by rfl) ⟨858897, by rfl⟩ : syracuseStep 2290393 = 1717795) B1717795
theorem B2413337 : Blo 1607002 2413337 := bstep (se 2 (by rfl) ⟨905001, by rfl⟩ : syracuseStep 2413337 = 1810003) B1810003
theorem B3617675 : Blo 1607002 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B2413451 : Blo 1607002 2413451 := bstep (se 1 (by rfl) ⟨1810088, by rfl⟩ : syracuseStep 2413451 = 3620177) B3620177
theorem B2413463 : Blo 1607002 2413463 := bstep (se 1 (by rfl) ⟨1810097, by rfl⟩ : syracuseStep 2413463 = 3620195) B3620195
theorem B3617729 : Blo 1607002 3617729 := bstep (se 2 (by rfl) ⟨1356648, by rfl⟩ : syracuseStep 3617729 = 2713297) B2713297
theorem B3052505 : Blo 1607002 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B12211235 : Blo 1607002 12211235 := bstep (se 1 (by rfl) ⟨9158426, by rfl⟩ : syracuseStep 12211235 = 18316853) B18316853
theorem B1717291 : Blo 1607002 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B4068427 : Blo 1607002 4068427 := bstep (se 1 (by rfl) ⟨3051320, by rfl⟩ : syracuseStep 4068427 = 6102641) B6102641
theorem B8139851 : Blo 1607002 8139851 := bstep (se 1 (by rfl) ⟨6104888, by rfl⟩ : syracuseStep 8139851 = 12209777) B12209777
theorem B2446411 : Blo 1607002 2446411 := bstep (se 1 (by rfl) ⟨1834808, by rfl⟩ : syracuseStep 2446411 = 3669617) B3669617
theorem B4969561 : Blo 1607002 4969561 := bstep (se 2 (by rfl) ⟨1863585, by rfl⟩ : syracuseStep 4969561 = 3727171) B3727171
theorem B3617945 : Blo 1607002 3617945 := bstep (se 2 (by rfl) ⟨1356729, by rfl⟩ : syracuseStep 3617945 = 2713459) B2713459
theorem B5428403 : Blo 1607002 5428403 := bstep (se 1 (by rfl) ⟨4071302, by rfl⟩ : syracuseStep 5428403 = 8142605) B8142605
theorem B4068569 : Blo 1607002 4068569 := bstep (se 2 (by rfl) ⟨1525713, by rfl⟩ : syracuseStep 4068569 = 3051427) B3051427
theorem B4887773 : Blo 1607002 4887773 := bstep (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) B1832915
theorem B3618035 : Blo 1607002 3618035 := bstep (se 1 (by rfl) ⟨2713526, by rfl⟩ : syracuseStep 3618035 = 5427053) B5427053
theorem B5149975 : Blo 1607002 5149975 := bstep (se 1 (by rfl) ⟨3862481, by rfl⟩ : syracuseStep 5149975 = 7724963) B7724963
theorem B3618071 : Blo 1607002 3618071 := bstep (se 1 (by rfl) ⟨2713553, by rfl⟩ : syracuseStep 3618071 = 5427107) B5427107
theorem B10302821 : Blo 1607002 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B5428673 : Blo 1607002 5428673 := bstep (se 2 (by rfl) ⟨2035752, by rfl⟩ : syracuseStep 5428673 = 4071505) B4071505
theorem B3618251 : Blo 1607002 3618251 := bstep (se 1 (by rfl) ⟨2713688, by rfl⟩ : syracuseStep 3618251 = 5427377) B5427377
theorem B3618305 : Blo 1607002 3618305 := bstep (se 2 (by rfl) ⟨1356864, by rfl⟩ : syracuseStep 3618305 = 2713729) B2713729
theorem B1807915 : Blo 1607002 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B8697419 : Blo 1607002 8697419 := bstep (se 1 (by rfl) ⟨6523064, by rfl⟩ : syracuseStep 8697419 = 13046129) B13046129
theorem B3053143 : Blo 1607002 3053143 := bstep (se 1 (by rfl) ⟨2289857, by rfl⟩ : syracuseStep 3053143 = 4579715) B4579715
theorem B1930891 : Blo 1607002 1930891 := bstep (se 1 (by rfl) ⟨1448168, by rfl⟩ : syracuseStep 1930891 = 2896337) B2896337
theorem B1808023 : Blo 1607002 1808023 := bstep (se 1 (by rfl) ⟨1356017, by rfl⟩ : syracuseStep 1808023 = 2712035) B2712035
theorem B3618521 : Blo 1607002 3618521 := bstep (se 2 (by rfl) ⟨1356945, by rfl⟩ : syracuseStep 3618521 = 2713891) B2713891
theorem B27481841 : Blo 1607002 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B3618611 : Blo 1607002 3618611 := bstep (se 1 (by rfl) ⟨2713958, by rfl⟩ : syracuseStep 3618611 = 5427917) B5427917
theorem B1808203 : Blo 1607002 1808203 := bstep (se 1 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 1808203 = 2712305) B2712305
theorem B3864395 : Blo 1607002 3864395 := bstep (se 1 (by rfl) ⟨2898296, by rfl⟩ : syracuseStep 3864395 = 5796593) B5796593
theorem B3618647 : Blo 1607002 3618647 := bstep (se 1 (by rfl) ⟨2713985, by rfl⟩ : syracuseStep 3618647 = 5427971) B5427971
theorem B1808311 : Blo 1607002 1808311 := bstep (se 1 (by rfl) ⟨1356233, by rfl⟩ : syracuseStep 1808311 = 2712467) B2712467
theorem B11589581 : Blo 1607002 11589581 := bstep (se 3 (by rfl) ⟨2173046, by rfl⟩ : syracuseStep 11589581 = 4346093) B4346093
theorem B4405213 : Blo 1607002 4405213 := bstep (se 3 (by rfl) ⟨825977, by rfl⟩ : syracuseStep 4405213 = 1651955) B1651955
theorem B5429213 : Blo 1607002 5429213 := bstep (se 3 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 5429213 = 2035955) B2035955
theorem B3618827 : Blo 1607002 3618827 := bstep (se 1 (by rfl) ⟨2714120, by rfl⟩ : syracuseStep 3618827 = 5428241) B5428241
theorem B4069399 : Blo 1607002 4069399 := bstep (se 1 (by rfl) ⟨3052049, by rfl⟩ : syracuseStep 4069399 = 6104099) B6104099
theorem B3618881 : Blo 1607002 3618881 := bstep (se 2 (by rfl) ⟨1357080, by rfl⟩ : syracuseStep 3618881 = 2714161) B2714161
theorem B5150795 : Blo 1607002 5150795 := bstep (se 1 (by rfl) ⟨3863096, by rfl⟩ : syracuseStep 5150795 = 7726193) B7726193
theorem B1808491 : Blo 1607002 1808491 := bstep (se 1 (by rfl) ⟨1356368, by rfl⟩ : syracuseStep 1808491 = 2712737) B2712737
theorem B18315395 : Blo 1607002 18315395 := bstep (se 1 (by rfl) ⟨13736546, by rfl⟩ : syracuseStep 18315395 = 27473093) B27473093
theorem B1833143 : Blo 1607002 1833143 := bstep (se 1 (by rfl) ⟨1374857, by rfl⟩ : syracuseStep 1833143 = 2749715) B2749715
theorem B1808599 : Blo 1607002 1808599 := bstep (se 1 (by rfl) ⟨1356449, by rfl⟩ : syracuseStep 1808599 = 2712899) B2712899
theorem B5871833 : Blo 1607002 5871833 := bstep (se 2 (by rfl) ⟨2201937, by rfl⟩ : syracuseStep 5871833 = 4403875) B4403875
theorem B2750681 : Blo 1607002 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B3619097 : Blo 1607002 3619097 := bstep (se 2 (by rfl) ⟨1357161, by rfl⟩ : syracuseStep 3619097 = 2714323) B2714323
theorem B13031725 : Blo 1607002 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B125254001 : Blo 1607002 125254001 := bstep (se 2 (by rfl) ⟨46970250, by rfl⟩ : syracuseStep 125254001 = 93940501) B93940501
theorem B3619187 : Blo 1607002 3619187 := bstep (se 1 (by rfl) ⟨2714390, by rfl⟩ : syracuseStep 3619187 = 5428781) B5428781
theorem B1808779 : Blo 1607002 1808779 := bstep (se 1 (by rfl) ⟨1356584, by rfl⟩ : syracuseStep 1808779 = 2713169) B2713169
theorem B3053963 : Blo 1607002 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B3619223 : Blo 1607002 3619223 := bstep (se 1 (by rfl) ⟨2714417, by rfl⟩ : syracuseStep 3619223 = 5428835) B5428835
theorem B3054017 : Blo 1607002 3054017 := bstep (se 2 (by rfl) ⟨1145256, by rfl⟩ : syracuseStep 3054017 = 2290513) B2290513
theorem B4069835 : Blo 1607002 4069835 := bstep (se 1 (by rfl) ⟨3052376, by rfl⟩ : syracuseStep 4069835 = 6104753) B6104753
theorem B1808887 : Blo 1607002 1808887 := bstep (se 1 (by rfl) ⟨1356665, by rfl⟩ : syracuseStep 1808887 = 2713331) B2713331
theorem B2898433 : Blo 1607002 2898433 := bstep (se 2 (by rfl) ⟨1086912, by rfl⟩ : syracuseStep 2898433 = 2173825) B2173825
theorem B3619403 : Blo 1607002 3619403 := bstep (se 1 (by rfl) ⟨2714552, by rfl⟩ : syracuseStep 3619403 = 5429105) B5429105
theorem B44022365 : Blo 1607002 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B3619457 : Blo 1607002 3619457 := bstep (se 2 (by rfl) ⟨1357296, by rfl⟩ : syracuseStep 3619457 = 2714593) B2714593
theorem B1809067 : Blo 1607002 1809067 := bstep (se 1 (by rfl) ⟨1356800, by rfl⟩ : syracuseStep 1809067 = 2713601) B2713601
theorem B20609741 : Blo 1607002 20609741 := bstep (se 3 (by rfl) ⟨3864326, by rfl⟩ : syracuseStep 20609741 = 7728653) B7728653
theorem B1809175 : Blo 1607002 1809175 := bstep (se 1 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 1809175 = 2713763) B2713763
theorem B5151539 : Blo 1607002 5151539 := bstep (se 1 (by rfl) ⟨3863654, by rfl⟩ : syracuseStep 5151539 = 7727309) B7727309
theorem B4070209 : Blo 1607002 4070209 := bstep (se 2 (by rfl) ⟨1526328, by rfl⟩ : syracuseStep 4070209 = 3052657) B3052657
theorem B8141633 : Blo 1607002 8141633 := bstep (se 2 (by rfl) ⟨3053112, by rfl⟩ : syracuseStep 8141633 = 6106225) B6106225
theorem B3619673 : Blo 1607002 3619673 := bstep (se 2 (by rfl) ⟨1357377, by rfl⟩ : syracuseStep 3619673 = 2714755) B2714755
theorem B13728689 : Blo 1607002 13728689 := bstep (se 2 (by rfl) ⟨5148258, by rfl⟩ : syracuseStep 13728689 = 10296517) B10296517
theorem B3619763 : Blo 1607002 3619763 := bstep (se 1 (by rfl) ⟨2714822, by rfl⟩ : syracuseStep 3619763 = 5429645) B5429645
theorem B1809355 : Blo 1607002 1809355 := bstep (se 1 (by rfl) ⟨1357016, by rfl⟩ : syracuseStep 1809355 = 2714033) B2714033
theorem B3619799 : Blo 1607002 3619799 := bstep (se 1 (by rfl) ⟨2714849, by rfl⟩ : syracuseStep 3619799 = 5429699) B5429699
theorem B7339031 : Blo 1607002 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B2898995 : Blo 1607002 2898995 := bstep (se 1 (by rfl) ⟨2174246, by rfl⟩ : syracuseStep 2898995 = 4348493) B4348493
theorem B1809463 : Blo 1607002 1809463 := bstep (se 1 (by rfl) ⟨1357097, by rfl⟩ : syracuseStep 1809463 = 2714195) B2714195
theorem B5430347 : Blo 1607002 5430347 := bstep (se 1 (by rfl) ⟨4072760, by rfl⟩ : syracuseStep 5430347 = 8145521) B8145521
theorem B3619979 : Blo 1607002 3619979 := bstep (se 1 (by rfl) ⟨2714984, by rfl⟩ : syracuseStep 3619979 = 5429969) B5429969
theorem B3865751 : Blo 1607002 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B3620033 : Blo 1607002 3620033 := bstep (se 2 (by rfl) ⟨1357512, by rfl⟩ : syracuseStep 3620033 = 2715025) B2715025
theorem B1809643 : Blo 1607002 1809643 := bstep (se 1 (by rfl) ⟨1357232, by rfl⟩ : syracuseStep 1809643 = 2714465) B2714465
theorem B4128023 : Blo 1607002 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B6102323 : Blo 1607002 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B6102337 : Blo 1607002 6102337 := bstep (se 2 (by rfl) ⟨2288376, by rfl⟩ : syracuseStep 6102337 = 4576753) B4576753
theorem B1809751 : Blo 1607002 1809751 := bstep (se 1 (by rfl) ⟨1357313, by rfl⟩ : syracuseStep 1809751 = 2714627) B2714627
theorem B4070807 : Blo 1607002 4070807 := bstep (se 1 (by rfl) ⟨3053105, by rfl⟩ : syracuseStep 4070807 = 6106211) B6106211
theorem B3620249 : Blo 1607002 3620249 := bstep (se 2 (by rfl) ⟨1357593, by rfl⟩ : syracuseStep 3620249 = 2715187) B2715187
theorem B1834411 : Blo 1607002 1834411 := bstep (se 1 (by rfl) ⟨1375808, by rfl⟩ : syracuseStep 1834411 = 2751617) B2751617
theorem B9780659 : Blo 1607002 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B4578781 : Blo 1607002 4578781 := bstep (se 3 (by rfl) ⟨858521, by rfl⟩ : syracuseStep 4578781 = 1717043) B1717043
theorem B1809931 : Blo 1607002 1809931 := bstep (se 1 (by rfl) ⟨1357448, by rfl⟩ : syracuseStep 1809931 = 2714897) B2714897
theorem B4578839 : Blo 1607002 4578839 := bstep (se 1 (by rfl) ⟨3434129, by rfl⟩ : syracuseStep 4578839 = 6868259) B6868259
theorem B1810039 : Blo 1607002 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B12205889 : Blo 1607002 12205889 := bstep (se 2 (by rfl) ⟨4577208, by rfl⟩ : syracuseStep 12205889 = 9154417) B9154417
theorem B47652785 : Blo 1607002 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B3432395 : Blo 1607002 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B6864857 : Blo 1607002 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B9404419 : Blo 1607002 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B15458309 : Blo 1607002 15458309 := bstep (se 4 (by rfl) ⟨1449216, by rfl⟩ : syracuseStep 15458309 = 2898433) B2898433
theorem B6864925 : Blo 1607002 6864925 := bstep (se 3 (by rfl) ⟨1287173, by rfl⟩ : syracuseStep 6864925 = 2574347) B2574347
theorem B6103127 : Blo 1607002 6103127 := bstep (se 1 (by rfl) ⟨4577345, by rfl⟩ : syracuseStep 6103127 = 9154691) B9154691
theorem B4890743 : Blo 1607002 4890743 := bstep (se 1 (by rfl) ⟨3668057, by rfl⟩ : syracuseStep 4890743 = 7336115) B7336115
theorem B5095543 : Blo 1607002 5095543 := bstep (se 1 (by rfl) ⟨3821657, by rfl⟩ : syracuseStep 5095543 = 7643315) B7643315
theorem B3432719 : Blo 1607002 3432719 := bstep (se 1 (by rfl) ⟨2574539, by rfl⟩ : syracuseStep 3432719 = 5149079) B5149079
theorem B2711927 : Blo 1607002 2711927 := bstep (se 1 (by rfl) ⟨2033945, by rfl⟩ : syracuseStep 2711927 = 4067891) B4067891
theorem B17375633 : Blo 1607002 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B9159065 : Blo 1607002 9159065 := bstep (se 2 (by rfl) ⟨3434649, by rfl⟩ : syracuseStep 9159065 = 6869299) B6869299
theorem B4579841 : Blo 1607002 4579841 := bstep (se 2 (by rfl) ⟨1717440, by rfl⟩ : syracuseStep 4579841 = 3434881) B3434881
theorem B6103613 : Blo 1607002 6103613 := bstep (se 3 (by rfl) ⟨1144427, by rfl⟩ : syracuseStep 6103613 = 2288855) B2288855
theorem B23511617 : Blo 1607002 23511617 := bstep (se 2 (by rfl) ⟨8816856, by rfl⟩ : syracuseStep 23511617 = 17633713) B17633713
theorem B2712379 : Blo 1607002 2712379 := bstep (se 1 (by rfl) ⟨2034284, by rfl⟩ : syracuseStep 2712379 = 4068569) B4068569
theorem B2712521 : Blo 1607002 2712521 := bstep (se 2 (by rfl) ⟨1017195, by rfl⟩ : syracuseStep 2712521 = 2034391) B2034391
theorem B4580297 : Blo 1607002 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B6521867 : Blo 1607002 6521867 := bstep (se 1 (by rfl) ⟨4891400, by rfl⟩ : syracuseStep 6521867 = 9782801) B9782801
theorem B8143901 : Blo 1607002 8143901 := bstep (se 3 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 8143901 = 3053963) B3053963
theorem B4408435 : Blo 1607002 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B7726387 : Blo 1607002 7726387 := bstep (se 1 (by rfl) ⟨5794790, by rfl⟩ : syracuseStep 7726387 = 11589581) B11589581
theorem B1607047 : Blo 1607002 1607047 := bstep (se 1 (by rfl) ⟨1205285, by rfl⟩ : syracuseStep 1607047 = 2410571) B2410571
theorem B1607055 : Blo 1607002 1607055 := bstep (se 1 (by rfl) ⟨1205291, by rfl⟩ : syracuseStep 1607055 = 2410583) B2410583
theorem B5424569 : Blo 1607002 5424569 := bstep (se 2 (by rfl) ⟨2034213, by rfl⟩ : syracuseStep 5424569 = 4068427) B4068427
theorem B3261881 : Blo 1607002 3261881 := bstep (se 2 (by rfl) ⟨1223205, by rfl⟩ : syracuseStep 3261881 = 2446411) B2446411
theorem B1607099 : Blo 1607002 1607099 := bstep (se 1 (by rfl) ⟨1205324, by rfl⟩ : syracuseStep 1607099 = 2410649) B2410649
theorem B8144387 : Blo 1607002 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B1607175 : Blo 1607002 1607175 := bstep (se 1 (by rfl) ⟨1205381, by rfl⟩ : syracuseStep 1607175 = 2410763) B2410763
theorem B1607183 : Blo 1607002 1607183 := bstep (se 1 (by rfl) ⟨1205387, by rfl⟩ : syracuseStep 1607183 = 2410775) B2410775
theorem B1607227 : Blo 1607002 1607227 := bstep (se 1 (by rfl) ⟨1205420, by rfl⟩ : syracuseStep 1607227 = 2410841) B2410841
theorem B83502667 : Blo 1607002 83502667 := bstep (se 1 (by rfl) ⟨62627000, by rfl⟩ : syracuseStep 83502667 = 125254001) B125254001
theorem B3917431 : Blo 1607002 3917431 := bstep (se 1 (by rfl) ⟨2938073, by rfl⟩ : syracuseStep 3917431 = 5876147) B5876147
theorem B1607303 : Blo 1607002 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B2713223 : Blo 1607002 2713223 := bstep (se 1 (by rfl) ⟨2034917, by rfl⟩ : syracuseStep 2713223 = 4069835) B4069835
theorem B1607311 : Blo 1607002 1607311 := bstep (se 1 (by rfl) ⟨1205483, by rfl⟩ : syracuseStep 1607311 = 2410967) B2410967
theorem B34768561 : Blo 1607002 34768561 := bstep (se 2 (by rfl) ⟨13038210, by rfl⟩ : syracuseStep 34768561 = 26076421) B26076421
theorem B1607355 : Blo 1607002 1607355 := bstep (se 1 (by rfl) ⟨1205516, by rfl⟩ : syracuseStep 1607355 = 2411033) B2411033
theorem B6866633 : Blo 1607002 6866633 := bstep (se 2 (by rfl) ⟨2574987, by rfl⟩ : syracuseStep 6866633 = 5149975) B5149975
theorem B8136449 : Blo 1607002 8136449 := bstep (se 2 (by rfl) ⟨3051168, by rfl⟩ : syracuseStep 8136449 = 6102337) B6102337
theorem B1607431 : Blo 1607002 1607431 := bstep (se 1 (by rfl) ⟨1205573, by rfl⟩ : syracuseStep 1607431 = 2411147) B2411147
theorem B1607439 : Blo 1607002 1607439 := bstep (se 1 (by rfl) ⟨1205579, by rfl⟩ : syracuseStep 1607439 = 2411159) B2411159
theorem B13739827 : Blo 1607002 13739827 := bstep (se 1 (by rfl) ⟨10304870, by rfl⟩ : syracuseStep 13739827 = 20609741) B20609741
theorem B1607483 : Blo 1607002 1607483 := bstep (se 1 (by rfl) ⟨1205612, by rfl⟩ : syracuseStep 1607483 = 2411225) B2411225
theorem B1607559 : Blo 1607002 1607559 := bstep (se 1 (by rfl) ⟨1205669, by rfl⟩ : syracuseStep 1607559 = 2411339) B2411339
theorem B1607567 : Blo 1607002 1607567 := bstep (se 1 (by rfl) ⟨1205675, by rfl⟩ : syracuseStep 1607567 = 2411351) B2411351
theorem B1607611 : Blo 1607002 1607611 := bstep (se 1 (by rfl) ⟨1205708, by rfl⟩ : syracuseStep 1607611 = 2411417) B2411417
theorem B9152459 : Blo 1607002 9152459 := bstep (se 1 (by rfl) ⟨6864344, by rfl⟩ : syracuseStep 9152459 = 13728689) B13728689
theorem B6105041 : Blo 1607002 6105041 := bstep (se 2 (by rfl) ⟨2289390, by rfl⟩ : syracuseStep 6105041 = 4578781) B4578781
theorem B1607687 : Blo 1607002 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B5425163 : Blo 1607002 5425163 := bstep (se 1 (by rfl) ⟨4068872, by rfl⟩ : syracuseStep 5425163 = 8137745) B8137745
theorem B2410511 : Blo 1607002 2410511 := bstep (se 1 (by rfl) ⟨1807883, by rfl⟩ : syracuseStep 2410511 = 3615767) B3615767
theorem B1607695 : Blo 1607002 1607695 := bstep (se 1 (by rfl) ⟨1205771, by rfl⟩ : syracuseStep 1607695 = 2411543) B2411543
theorem B4892687 : Blo 1607002 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B2410553 : Blo 1607002 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B1607739 : Blo 1607002 1607739 := bstep (se 1 (by rfl) ⟨1205804, by rfl⟩ : syracuseStep 1607739 = 2411609) B2411609
theorem B5425271 : Blo 1607002 5425271 := bstep (se 1 (by rfl) ⟨4068953, by rfl⟩ : syracuseStep 5425271 = 8137907) B8137907
theorem B2410631 : Blo 1607002 2410631 := bstep (se 1 (by rfl) ⟨1807973, by rfl⟩ : syracuseStep 2410631 = 3615947) B3615947
theorem B1607815 : Blo 1607002 1607815 := bstep (se 1 (by rfl) ⟨1205861, by rfl⟩ : syracuseStep 1607815 = 2411723) B2411723
theorem B1607823 : Blo 1607002 1607823 := bstep (se 1 (by rfl) ⟨1205867, by rfl⟩ : syracuseStep 1607823 = 2411735) B2411735
theorem B2410667 : Blo 1607002 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B2574521 : Blo 1607002 2574521 := bstep (se 2 (by rfl) ⟨965445, by rfl⟩ : syracuseStep 2574521 = 1930891) B1930891
theorem B1607867 : Blo 1607002 1607867 := bstep (se 1 (by rfl) ⟨1205900, by rfl⟩ : syracuseStep 1607867 = 2411801) B2411801
theorem B2410697 : Blo 1607002 2410697 := bstep (se 2 (by rfl) ⟨904011, by rfl⟩ : syracuseStep 2410697 = 1808023) B1808023
theorem B1607943 : Blo 1607002 1607943 := bstep (se 1 (by rfl) ⟨1205957, by rfl⟩ : syracuseStep 1607943 = 2411915) B2411915
theorem B1607951 : Blo 1607002 1607951 := bstep (se 1 (by rfl) ⟨1205963, by rfl⟩ : syracuseStep 1607951 = 2411927) B2411927
theorem B2713871 : Blo 1607002 2713871 := bstep (se 1 (by rfl) ⟨2035403, by rfl⟩ : syracuseStep 2713871 = 4070807) B4070807
theorem B2410811 : Blo 1607002 2410811 := bstep (se 1 (by rfl) ⟨1808108, by rfl⟩ : syracuseStep 2410811 = 3616217) B3616217
theorem B1607995 : Blo 1607002 1607995 := bstep (se 1 (by rfl) ⟨1205996, by rfl⟩ : syracuseStep 1607995 = 2411993) B2411993
theorem B2410871 : Blo 1607002 2410871 := bstep (se 1 (by rfl) ⟨1808153, by rfl⟩ : syracuseStep 2410871 = 3616307) B3616307
theorem B1608071 : Blo 1607002 1608071 := bstep (se 1 (by rfl) ⟨1206053, by rfl⟩ : syracuseStep 1608071 = 2412107) B2412107
theorem B2410895 : Blo 1607002 2410895 := bstep (se 1 (by rfl) ⟨1808171, by rfl⟩ : syracuseStep 2410895 = 3616343) B3616343
theorem B1608079 : Blo 1607002 1608079 := bstep (se 1 (by rfl) ⟨1206059, by rfl⟩ : syracuseStep 1608079 = 2412119) B2412119
theorem B2410937 : Blo 1607002 2410937 := bstep (se 2 (by rfl) ⟨904101, by rfl⟩ : syracuseStep 2410937 = 1808203) B1808203
theorem B1608123 : Blo 1607002 1608123 := bstep (se 1 (by rfl) ⟨1206092, by rfl⟩ : syracuseStep 1608123 = 2412185) B2412185
theorem B2411015 : Blo 1607002 2411015 := bstep (se 1 (by rfl) ⟨1808261, by rfl⟩ : syracuseStep 2411015 = 3616523) B3616523
theorem B1608199 : Blo 1607002 1608199 := bstep (se 1 (by rfl) ⟨1206149, by rfl⟩ : syracuseStep 1608199 = 2412299) B2412299
theorem B1608207 : Blo 1607002 1608207 := bstep (se 1 (by rfl) ⟨1206155, by rfl⟩ : syracuseStep 1608207 = 2412311) B2412311
theorem B8137259 : Blo 1607002 8137259 := bstep (se 1 (by rfl) ⟨6102944, by rfl⟩ : syracuseStep 8137259 = 12205889) B12205889
theorem B2411051 : Blo 1607002 2411051 := bstep (se 1 (by rfl) ⟨1808288, by rfl⟩ : syracuseStep 2411051 = 3616577) B3616577
theorem B1608251 : Blo 1607002 1608251 := bstep (se 1 (by rfl) ⟨1206188, by rfl⟩ : syracuseStep 1608251 = 2412377) B2412377
theorem B2411081 : Blo 1607002 2411081 := bstep (se 2 (by rfl) ⟨904155, by rfl⟩ : syracuseStep 2411081 = 1808311) B1808311
theorem B6867575 : Blo 1607002 6867575 := bstep (se 1 (by rfl) ⟨5150681, by rfl⟩ : syracuseStep 6867575 = 10301363) B10301363
theorem B17386103 : Blo 1607002 17386103 := bstep (se 1 (by rfl) ⟨13039577, by rfl⟩ : syracuseStep 17386103 = 26079155) B26079155
theorem B2288263 : Blo 1607002 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B1608327 : Blo 1607002 1608327 := bstep (se 1 (by rfl) ⟨1206245, by rfl⟩ : syracuseStep 1608327 = 2412491) B2412491
theorem B1608335 : Blo 1607002 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B2411195 : Blo 1607002 2411195 := bstep (se 1 (by rfl) ⟨1808396, by rfl⟩ : syracuseStep 2411195 = 3616793) B3616793
theorem B1608379 : Blo 1607002 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B5425865 : Blo 1607002 5425865 := bstep (se 2 (by rfl) ⟨2034699, by rfl⟩ : syracuseStep 5425865 = 4069399) B4069399
theorem B2411255 : Blo 1607002 2411255 := bstep (se 1 (by rfl) ⟨1808441, by rfl⟩ : syracuseStep 2411255 = 3616883) B3616883
theorem B1608455 : Blo 1607002 1608455 := bstep (se 1 (by rfl) ⟨1206341, by rfl⟩ : syracuseStep 1608455 = 2412683) B2412683
theorem B2411279 : Blo 1607002 2411279 := bstep (se 1 (by rfl) ⟨1808459, by rfl⟩ : syracuseStep 2411279 = 3616919) B3616919
theorem B1608463 : Blo 1607002 1608463 := bstep (se 1 (by rfl) ⟨1206347, by rfl⟩ : syracuseStep 1608463 = 2412695) B2412695
theorem B2444075 : Blo 1607002 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B2714411 : Blo 1607002 2714411 := bstep (se 1 (by rfl) ⟨2035808, by rfl⟩ : syracuseStep 2714411 = 4071617) B4071617
theorem B2411321 : Blo 1607002 2411321 := bstep (se 2 (by rfl) ⟨904245, by rfl⟩ : syracuseStep 2411321 = 1808491) B1808491
theorem B1608507 : Blo 1607002 1608507 := bstep (se 1 (by rfl) ⟨1206380, by rfl⟩ : syracuseStep 1608507 = 2412761) B2412761
theorem B2411399 : Blo 1607002 2411399 := bstep (se 1 (by rfl) ⟨1808549, by rfl⟩ : syracuseStep 2411399 = 3617099) B3617099
theorem B1608583 : Blo 1607002 1608583 := bstep (se 1 (by rfl) ⟨1206437, by rfl⟩ : syracuseStep 1608583 = 2412875) B2412875
theorem B1608591 : Blo 1607002 1608591 := bstep (se 1 (by rfl) ⟨1206443, by rfl⟩ : syracuseStep 1608591 = 2412887) B2412887
theorem B2411435 : Blo 1607002 2411435 := bstep (se 1 (by rfl) ⟨1808576, by rfl⟩ : syracuseStep 2411435 = 3617153) B3617153
theorem B1608635 : Blo 1607002 1608635 := bstep (se 1 (by rfl) ⟨1206476, by rfl⟩ : syracuseStep 1608635 = 2412953) B2412953
theorem B2411465 : Blo 1607002 2411465 := bstep (se 2 (by rfl) ⟨904299, by rfl⟩ : syracuseStep 2411465 = 1808599) B1808599
theorem B4123649 : Blo 1607002 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B1608711 : Blo 1607002 1608711 := bstep (se 1 (by rfl) ⟨1206533, by rfl⟩ : syracuseStep 1608711 = 2413067) B2413067
theorem B1608719 : Blo 1607002 1608719 := bstep (se 1 (by rfl) ⟨1206539, by rfl⟩ : syracuseStep 1608719 = 2413079) B2413079
theorem B3615803 : Blo 1607002 3615803 := bstep (se 1 (by rfl) ⟨2711852, by rfl⟩ : syracuseStep 3615803 = 5423705) B5423705
theorem B2411579 : Blo 1607002 2411579 := bstep (se 1 (by rfl) ⟨1808684, by rfl⟩ : syracuseStep 2411579 = 3617369) B3617369
theorem B1608763 : Blo 1607002 1608763 := bstep (se 1 (by rfl) ⟨1206572, by rfl⟩ : syracuseStep 1608763 = 2413145) B2413145
theorem B2411639 : Blo 1607002 2411639 := bstep (se 1 (by rfl) ⟨1808729, by rfl⟩ : syracuseStep 2411639 = 3617459) B3617459
theorem B1608839 : Blo 1607002 1608839 := bstep (se 1 (by rfl) ⟨1206629, by rfl⟩ : syracuseStep 1608839 = 2413259) B2413259
theorem B2411663 : Blo 1607002 2411663 := bstep (se 1 (by rfl) ⟨1808747, by rfl⟩ : syracuseStep 2411663 = 3617495) B3617495
theorem B1608847 : Blo 1607002 1608847 := bstep (se 1 (by rfl) ⟨1206635, by rfl⟩ : syracuseStep 1608847 = 2413271) B2413271
theorem B3615929 : Blo 1607002 3615929 := bstep (se 2 (by rfl) ⟨1355973, by rfl⟩ : syracuseStep 3615929 = 2711947) B2711947
theorem B2411705 : Blo 1607002 2411705 := bstep (se 2 (by rfl) ⟨904389, by rfl⟩ : syracuseStep 2411705 = 1808779) B1808779
theorem B2288827 : Blo 1607002 2288827 := bstep (se 1 (by rfl) ⟨1716620, by rfl⟩ : syracuseStep 2288827 = 3433241) B3433241
theorem B2714809 : Blo 1607002 2714809 := bstep (se 2 (by rfl) ⟨1018053, by rfl⟩ : syracuseStep 2714809 = 2036107) B2036107
theorem B1608891 : Blo 1607002 1608891 := bstep (se 1 (by rfl) ⟨1206668, by rfl⟩ : syracuseStep 1608891 = 2413337) B2413337
theorem B2411783 : Blo 1607002 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1608967 : Blo 1607002 1608967 := bstep (se 1 (by rfl) ⟨1206725, by rfl⟩ : syracuseStep 1608967 = 2413451) B2413451
theorem B1608975 : Blo 1607002 1608975 := bstep (se 1 (by rfl) ⟨1206731, by rfl⟩ : syracuseStep 1608975 = 2413463) B2413463
theorem B2411819 : Blo 1607002 2411819 := bstep (se 1 (by rfl) ⟨1808864, by rfl⟩ : syracuseStep 2411819 = 3617729) B3617729
theorem B2411849 : Blo 1607002 2411849 := bstep (se 2 (by rfl) ⟨904443, by rfl⟩ : syracuseStep 2411849 = 1808887) B1808887
theorem B5426567 : Blo 1607002 5426567 := bstep (se 1 (by rfl) ⟨4069925, by rfl⟩ : syracuseStep 5426567 = 8139851) B8139851
theorem B4124051 : Blo 1607002 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B2411963 : Blo 1607002 2411963 := bstep (se 1 (by rfl) ⟨1808972, by rfl⟩ : syracuseStep 2411963 = 3617945) B3617945
theorem B2412023 : Blo 1607002 2412023 := bstep (se 1 (by rfl) ⟨1809017, by rfl⟩ : syracuseStep 2412023 = 3618035) B3618035
theorem B3616271 : Blo 1607002 3616271 := bstep (se 1 (by rfl) ⟨2712203, by rfl⟩ : syracuseStep 3616271 = 5424407) B5424407
theorem B2412047 : Blo 1607002 2412047 := bstep (se 1 (by rfl) ⟨1809035, by rfl⟩ : syracuseStep 2412047 = 3618071) B3618071
theorem B3616289 : Blo 1607002 3616289 := bstep (se 2 (by rfl) ⟨1356108, by rfl⟩ : syracuseStep 3616289 = 2712217) B2712217
theorem B2412089 : Blo 1607002 2412089 := bstep (se 2 (by rfl) ⟨904533, by rfl⟩ : syracuseStep 2412089 = 1809067) B1809067
theorem B6868547 : Blo 1607002 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B6106711 : Blo 1607002 6106711 := bstep (se 1 (by rfl) ⟨4580033, by rfl⟩ : syracuseStep 6106711 = 9160067) B9160067
theorem B2412167 : Blo 1607002 2412167 := bstep (se 1 (by rfl) ⟨1809125, by rfl⟩ : syracuseStep 2412167 = 3618251) B3618251
theorem B30912151 : Blo 1607002 30912151 := bstep (se 1 (by rfl) ⟨23184113, by rfl⟩ : syracuseStep 30912151 = 46368227) B46368227
theorem B2412203 : Blo 1607002 2412203 := bstep (se 1 (by rfl) ⟨1809152, by rfl⟩ : syracuseStep 2412203 = 3618305) B3618305
theorem B2412233 : Blo 1607002 2412233 := bstep (se 2 (by rfl) ⟨904587, by rfl⟩ : syracuseStep 2412233 = 1809175) B1809175
theorem B5426945 : Blo 1607002 5426945 := bstep (se 2 (by rfl) ⟨2035104, by rfl⟩ : syracuseStep 5426945 = 4070209) B4070209
theorem B8138555 : Blo 1607002 8138555 := bstep (se 1 (by rfl) ⟨6103916, by rfl⟩ : syracuseStep 8138555 = 12207833) B12207833
theorem B2412347 : Blo 1607002 2412347 := bstep (se 1 (by rfl) ⟨1809260, by rfl⟩ : syracuseStep 2412347 = 3618521) B3618521
theorem B18321227 : Blo 1607002 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B11595635 : Blo 1607002 11595635 := bstep (se 1 (by rfl) ⟨8696726, by rfl⟩ : syracuseStep 11595635 = 17393453) B17393453
theorem B3616631 : Blo 1607002 3616631 := bstep (se 1 (by rfl) ⟨2712473, by rfl⟩ : syracuseStep 3616631 = 5424947) B5424947
theorem B2412407 : Blo 1607002 2412407 := bstep (se 1 (by rfl) ⟨1809305, by rfl⟩ : syracuseStep 2412407 = 3618611) B3618611
theorem B6107015 : Blo 1607002 6107015 := bstep (se 1 (by rfl) ⟨4580261, by rfl⟩ : syracuseStep 6107015 = 9160523) B9160523
theorem B2412431 : Blo 1607002 2412431 := bstep (se 1 (by rfl) ⟨1809323, by rfl⟩ : syracuseStep 2412431 = 3618647) B3618647
theorem B2412473 : Blo 1607002 2412473 := bstep (se 2 (by rfl) ⟨904677, by rfl⟩ : syracuseStep 2412473 = 1809355) B1809355
theorem B8138717 : Blo 1607002 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B2412551 : Blo 1607002 2412551 := bstep (se 1 (by rfl) ⟨1809413, by rfl⟩ : syracuseStep 2412551 = 3618827) B3618827
theorem B3616811 : Blo 1607002 3616811 := bstep (se 1 (by rfl) ⟨2712608, by rfl⟩ : syracuseStep 3616811 = 5425217) B5425217
theorem B2412587 : Blo 1607002 2412587 := bstep (se 1 (by rfl) ⟨1809440, by rfl⟩ : syracuseStep 2412587 = 3618881) B3618881
theorem B2289721 : Blo 1607002 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B6107197 : Blo 1607002 6107197 := bstep (se 3 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 6107197 = 2290199) B2290199
theorem B2412617 : Blo 1607002 2412617 := bstep (se 2 (by rfl) ⟨904731, by rfl⟩ : syracuseStep 2412617 = 1809463) B1809463
theorem B12210263 : Blo 1607002 12210263 := bstep (se 1 (by rfl) ⟨9157697, by rfl⟩ : syracuseStep 12210263 = 18315395) B18315395
theorem B12374149 : Blo 1607002 12374149 := bstep (se 4 (by rfl) ⟨1160076, by rfl⟩ : syracuseStep 12374149 = 2320153) B2320153
theorem B2412731 : Blo 1607002 2412731 := bstep (se 1 (by rfl) ⟨1809548, by rfl⟩ : syracuseStep 2412731 = 3619097) B3619097
theorem B2412791 : Blo 1607002 2412791 := bstep (se 1 (by rfl) ⟨1809593, by rfl⟩ : syracuseStep 2412791 = 3619187) B3619187
theorem B2412815 : Blo 1607002 2412815 := bstep (se 1 (by rfl) ⟨1809611, by rfl⟩ : syracuseStep 2412815 = 3619223) B3619223
theorem B8139041 : Blo 1607002 8139041 := bstep (se 2 (by rfl) ⟨3052140, by rfl⟩ : syracuseStep 8139041 = 6104281) B6104281
theorem B2036011 : Blo 1607002 2036011 := bstep (se 1 (by rfl) ⟨1527008, by rfl⟩ : syracuseStep 2036011 = 3054017) B3054017
theorem B2412857 : Blo 1607002 2412857 := bstep (se 2 (by rfl) ⟨904821, by rfl⟩ : syracuseStep 2412857 = 1809643) B1809643
theorem B2412935 : Blo 1607002 2412935 := bstep (se 1 (by rfl) ⟨1809701, by rfl⟩ : syracuseStep 2412935 = 3619403) B3619403
theorem B3617171 : Blo 1607002 3617171 := bstep (se 1 (by rfl) ⟨2712878, by rfl⟩ : syracuseStep 3617171 = 5425757) B5425757
theorem B29348243 : Blo 1607002 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B2412971 : Blo 1607002 2412971 := bstep (se 1 (by rfl) ⟨1809728, by rfl⟩ : syracuseStep 2412971 = 3619457) B3619457
theorem B3617225 : Blo 1607002 3617225 := bstep (se 2 (by rfl) ⟨1356459, by rfl⟩ : syracuseStep 3617225 = 2712919) B2712919
theorem B2413001 : Blo 1607002 2413001 := bstep (se 2 (by rfl) ⟨904875, by rfl⟩ : syracuseStep 2413001 = 1809751) B1809751
theorem B9777667 : Blo 1607002 9777667 := bstep (se 1 (by rfl) ⟨7333250, by rfl⟩ : syracuseStep 9777667 = 14666501) B14666501
theorem B5501483 : Blo 1607002 5501483 := bstep (se 1 (by rfl) ⟨4126112, by rfl⟩ : syracuseStep 5501483 = 8252225) B8252225
theorem B5427755 : Blo 1607002 5427755 := bstep (se 1 (by rfl) ⟨4070816, by rfl⟩ : syracuseStep 5427755 = 8141633) B8141633
theorem B2445881 : Blo 1607002 2445881 := bstep (se 2 (by rfl) ⟨917205, by rfl⟩ : syracuseStep 2445881 = 1834411) B1834411
theorem B2413115 : Blo 1607002 2413115 := bstep (se 1 (by rfl) ⟨1809836, by rfl⟩ : syracuseStep 2413115 = 3619673) B3619673
theorem B2413175 : Blo 1607002 2413175 := bstep (se 1 (by rfl) ⟨1809881, by rfl⟩ : syracuseStep 2413175 = 3619763) B3619763
theorem B2413199 : Blo 1607002 2413199 := bstep (se 1 (by rfl) ⟨1809899, by rfl⟩ : syracuseStep 2413199 = 3619799) B3619799
theorem B3052217 : Blo 1607002 3052217 := bstep (se 2 (by rfl) ⟨1144581, by rfl⟩ : syracuseStep 3052217 = 2289163) B2289163
theorem B2413241 : Blo 1607002 2413241 := bstep (se 2 (by rfl) ⟨904965, by rfl⟩ : syracuseStep 2413241 = 1809931) B1809931
theorem B2413319 : Blo 1607002 2413319 := bstep (se 1 (by rfl) ⟨1809989, by rfl⟩ : syracuseStep 2413319 = 3619979) B3619979
theorem B2577167 : Blo 1607002 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2413355 : Blo 1607002 2413355 := bstep (se 1 (by rfl) ⟨1810016, by rfl⟩ : syracuseStep 2413355 = 3620033) B3620033
theorem B2413385 : Blo 1607002 2413385 := bstep (se 2 (by rfl) ⟨905019, by rfl⟩ : syracuseStep 2413385 = 1810039) B1810039
theorem B4068215 : Blo 1607002 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B16323481 : Blo 1607002 16323481 := bstep (se 2 (by rfl) ⟨6121305, by rfl⟩ : syracuseStep 16323481 = 12242611) B12242611
theorem B23180195 : Blo 1607002 23180195 := bstep (se 1 (by rfl) ⟨17385146, by rfl⟩ : syracuseStep 23180195 = 34770293) B34770293
theorem B62632885 : Blo 1607002 62632885 := bstep (se 5 (by rfl) ⟨2935916, by rfl⟩ : syracuseStep 62632885 = 5871833) B5871833
theorem B2413499 : Blo 1607002 2413499 := bstep (se 1 (by rfl) ⟨1810124, by rfl⟩ : syracuseStep 2413499 = 3620249) B3620249
theorem B3052559 : Blo 1607002 3052559 := bstep (se 1 (by rfl) ⟨2289419, by rfl⟩ : syracuseStep 3052559 = 4578839) B4578839
theorem B3617927 : Blo 1607002 3617927 := bstep (se 1 (by rfl) ⟨2713445, by rfl⟩ : syracuseStep 3617927 = 5426891) B5426891
theorem B30897389 : Blo 1607002 30897389 := bstep (se 3 (by rfl) ⟨5793260, by rfl⟩ : syracuseStep 30897389 = 11586521) B11586521
theorem B8140013 : Blo 1607002 8140013 := bstep (se 3 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 8140013 = 3052505) B3052505
theorem B4576571 : Blo 1607002 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B3618107 : Blo 1607002 3618107 := bstep (se 1 (by rfl) ⟨2713580, by rfl⟩ : syracuseStep 3618107 = 5427161) B5427161
theorem B41203079 : Blo 1607002 41203079 := bstep (se 1 (by rfl) ⟨30902309, by rfl⟩ : syracuseStep 41203079 = 61804619) B61804619
theorem B7337351 : Blo 1607002 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B5150105 : Blo 1607002 5150105 := bstep (se 2 (by rfl) ⟨1931289, by rfl⟩ : syracuseStep 5150105 = 3862579) B3862579
theorem B3618233 : Blo 1607002 3618233 := bstep (se 2 (by rfl) ⟨1356837, by rfl⟩ : syracuseStep 3618233 = 2713675) B2713675
theorem B7730635 : Blo 1607002 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B7730653 : Blo 1607002 7730653 := bstep (se 3 (by rfl) ⟨1449497, by rfl⟩ : syracuseStep 7730653 = 2898995) B2898995
theorem B1807879 : Blo 1607002 1807879 := bstep (se 1 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 1807879 = 2711819) B2711819
theorem B13735453 : Blo 1607002 13735453 := bstep (se 3 (by rfl) ⟨2575397, by rfl⟩ : syracuseStep 13735453 = 5150795) B5150795
theorem B1808059 : Blo 1607002 1808059 := bstep (se 1 (by rfl) ⟨1356044, by rfl⟩ : syracuseStep 1808059 = 2712089) B2712089
theorem B6108929 : Blo 1607002 6108929 := bstep (se 2 (by rfl) ⟨2290848, by rfl⟩ : syracuseStep 6108929 = 4581697) B4581697
theorem B3618575 : Blo 1607002 3618575 := bstep (se 1 (by rfl) ⟨2713931, by rfl⟩ : syracuseStep 3618575 = 5427863) B5427863
theorem B3618593 : Blo 1607002 3618593 := bstep (se 2 (by rfl) ⟨1356972, by rfl⟩ : syracuseStep 3618593 = 2713945) B2713945
theorem B3053371 : Blo 1607002 3053371 := bstep (se 1 (by rfl) ⟨2290028, by rfl⟩ : syracuseStep 3053371 = 4580057) B4580057
theorem B5429051 : Blo 1607002 5429051 := bstep (se 1 (by rfl) ⟨4071788, by rfl⟩ : syracuseStep 5429051 = 8143577) B8143577
theorem B4888381 : Blo 1607002 4888381 := bstep (se 3 (by rfl) ⟨916571, by rfl⟩ : syracuseStep 4888381 = 1833143) B1833143
theorem B62666561 : Blo 1607002 62666561 := bstep (se 2 (by rfl) ⟨23499960, by rfl⟩ : syracuseStep 62666561 = 46999921) B46999921
theorem B3053447 : Blo 1607002 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B8140823 : Blo 1607002 8140823 := bstep (se 1 (by rfl) ⟨6105617, by rfl⟩ : syracuseStep 8140823 = 12211235) B12211235
theorem B4577323 : Blo 1607002 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B11008061 : Blo 1607002 11008061 := bstep (se 3 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 11008061 = 4128023) B4128023
theorem B6789187 : Blo 1607002 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B4348019 : Blo 1607002 4348019 := bstep (se 1 (by rfl) ⟨3261014, by rfl⟩ : syracuseStep 4348019 = 6522029) B6522029
theorem B3618935 : Blo 1607002 3618935 := bstep (se 1 (by rfl) ⟨2714201, by rfl⟩ : syracuseStep 3618935 = 5428403) B5428403
theorem B4069511 : Blo 1607002 4069511 := bstep (se 1 (by rfl) ⟨3052133, by rfl⟩ : syracuseStep 4069511 = 6104267) B6104267
theorem B1808527 : Blo 1607002 1808527 := bstep (se 1 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 1808527 = 2712791) B2712791
theorem B3258515 : Blo 1607002 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B4069561 : Blo 1607002 4069561 := bstep (se 2 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 4069561 = 3052171) B3052171
theorem B3053857 : Blo 1607002 3053857 := bstep (se 2 (by rfl) ⟨1145196, by rfl⟩ : syracuseStep 3053857 = 2290393) B2290393
theorem B5429537 : Blo 1607002 5429537 := bstep (se 2 (by rfl) ⟨2036076, by rfl⟩ : syracuseStep 5429537 = 4072153) B4072153
theorem B3619115 : Blo 1607002 3619115 := bstep (se 1 (by rfl) ⟨2714336, by rfl⟩ : syracuseStep 3619115 = 5428673) B5428673
theorem B4577597 : Blo 1607002 4577597 := bstep (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) B1716599
theorem B5798279 : Blo 1607002 5798279 := bstep (se 1 (by rfl) ⟨4348709, by rfl⟩ : syracuseStep 5798279 = 8697419) B8697419
theorem B3971699 : Blo 1607002 3971699 := bstep (se 1 (by rfl) ⟨2978774, by rfl⟩ : syracuseStep 3971699 = 5957549) B5957549
theorem B3054199 : Blo 1607002 3054199 := bstep (se 1 (by rfl) ⟨2290649, by rfl⟩ : syracuseStep 3054199 = 4581299) B4581299
theorem B1809031 : Blo 1607002 1809031 := bstep (se 1 (by rfl) ⟨1356773, by rfl⟩ : syracuseStep 1809031 = 2713547) B2713547
theorem B3619475 : Blo 1607002 3619475 := bstep (se 1 (by rfl) ⟨2714606, by rfl⟩ : syracuseStep 3619475 = 5429213) B5429213
theorem B3619529 : Blo 1607002 3619529 := bstep (se 2 (by rfl) ⟨1357323, by rfl⟩ : syracuseStep 3619529 = 2714647) B2714647
theorem B4070159 : Blo 1607002 4070159 := bstep (se 1 (by rfl) ⟨3052619, by rfl⟩ : syracuseStep 4070159 = 6105239) B6105239
theorem B6626081 : Blo 1607002 6626081 := bstep (se 2 (by rfl) ⟨2484780, by rfl⟩ : syracuseStep 6626081 = 4969561) B4969561
theorem B1833787 : Blo 1607002 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B1809211 : Blo 1607002 1809211 := bstep (se 1 (by rfl) ⟨1356908, by rfl⟩ : syracuseStep 1809211 = 2713817) B2713817
theorem B5430131 : Blo 1607002 5430131 := bstep (se 1 (by rfl) ⟨4072598, by rfl⟩ : syracuseStep 5430131 = 8145197) B8145197
theorem B41229323 : Blo 1607002 41229323 := bstep (se 1 (by rfl) ⟨30921992, by rfl⟩ : syracuseStep 41229323 = 61843985) B61843985
theorem B7724119 : Blo 1607002 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B4578439 : Blo 1607002 4578439 := bstep (se 1 (by rfl) ⟨3433829, by rfl⟩ : syracuseStep 4578439 = 6867659) B6867659
theorem B4643993 : Blo 1607002 4643993 := bstep (se 2 (by rfl) ⟨1741497, by rfl⟩ : syracuseStep 4643993 = 3482995) B3482995
theorem B1809679 : Blo 1607002 1809679 := bstep (se 1 (by rfl) ⟨1357259, by rfl⟩ : syracuseStep 1809679 = 2714519) B2714519
theorem B3620231 : Blo 1607002 3620231 := bstep (se 1 (by rfl) ⟨2715173, by rfl⟩ : syracuseStep 3620231 = 5430347) B5430347
theorem B4578713 : Blo 1607002 4578713 := bstep (se 2 (by rfl) ⟨1717017, by rfl⟩ : syracuseStep 4578713 = 3434035) B3434035
theorem B4070857 : Blo 1607002 4070857 := bstep (se 2 (by rfl) ⟨1526571, by rfl⟩ : syracuseStep 4070857 = 3053143) B3053143
theorem B13737437 : Blo 1607002 13737437 := bstep (se 3 (by rfl) ⟨2575769, by rfl⟩ : syracuseStep 13737437 = 5151539) B5151539
theorem B10305053 : Blo 1607002 10305053 := bstep (se 3 (by rfl) ⟨1932197, by rfl⟩ : syracuseStep 10305053 = 3864395) B3864395
theorem B10296875 : Blo 1607002 10296875 := bstep (se 1 (by rfl) ⟨7722656, by rfl⟩ : syracuseStep 10296875 = 15445313) B15445313
theorem B4070999 : Blo 1607002 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B6520439 : Blo 1607002 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B13033153 : Blo 1607002 13033153 := bstep (se 2 (by rfl) ⟨4887432, by rfl⟩ : syracuseStep 13033153 = 9774865) B9774865
theorem B10305281 : Blo 1607002 10305281 := bstep (se 2 (by rfl) ⟨3864480, by rfl⟩ : syracuseStep 10305281 = 7728961) B7728961
theorem B31768523 : Blo 1607002 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B5873617 : Blo 1607002 5873617 := bstep (se 2 (by rfl) ⟨2202606, by rfl⟩ : syracuseStep 5873617 = 4405213) B4405213
theorem B9158609 : Blo 1607002 9158609 := bstep (se 2 (by rfl) ⟨3434478, by rfl⟩ : syracuseStep 9158609 = 6868957) B6868957
theorem B10305539 : Blo 1607002 10305539 := bstep (se 1 (by rfl) ⟨7729154, by rfl⟩ : syracuseStep 10305539 = 15458309) B15458309
theorem B6103097 : Blo 1607002 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B3260495 : Blo 1607002 3260495 := bstep (se 1 (by rfl) ⟨2445371, by rfl⟩ : syracuseStep 3260495 = 4890743) B4890743
theorem B8142929 : Blo 1607002 8142929 := bstep (se 2 (by rfl) ⟨3053598, by rfl⟩ : syracuseStep 8142929 = 6107197) B6107197
theorem B9052249 : Blo 1607002 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B16498865 : Blo 1607002 16498865 := bstep (se 2 (by rfl) ⟨6187074, by rfl⟩ : syracuseStep 16498865 = 12374149) B12374149
theorem B11583755 : Blo 1607002 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B4071809 : Blo 1607002 4071809 := bstep (se 2 (by rfl) ⟨1526928, by rfl⟩ : syracuseStep 4071809 = 3053857) B3053857
theorem B2712143 : Blo 1607002 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B23511653 : Blo 1607002 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B4072265 : Blo 1607002 4072265 := bstep (se 2 (by rfl) ⟨1527099, by rfl⟩ : syracuseStep 4072265 = 3054199) B3054199
theorem B27468719 : Blo 1607002 27468719 := bstep (se 1 (by rfl) ⟨20601539, by rfl⟩ : syracuseStep 27468719 = 41203079) B41203079
theorem B3433403 : Blo 1607002 3433403 := bstep (se 1 (by rfl) ⟨2575052, by rfl⟩ : syracuseStep 3433403 = 5150105) B5150105
theorem B5424299 : Blo 1607002 5424299 := bstep (se 1 (by rfl) ⟨4068224, by rfl⟩ : syracuseStep 5424299 = 8136449) B8136449
theorem B4072619 : Blo 1607002 4072619 := bstep (se 1 (by rfl) ⟨3054464, by rfl⟩ : syracuseStep 4072619 = 6108929) B6108929
theorem B83510513 : Blo 1607002 83510513 := bstep (se 2 (by rfl) ⟨31316442, by rfl⟩ : syracuseStep 83510513 = 62632885) B62632885
theorem B1607007 : Blo 1607002 1607007 := bstep (se 1 (by rfl) ⟨1205255, by rfl⟩ : syracuseStep 1607007 = 2410511) B2410511
theorem B3261791 : Blo 1607002 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B1607035 : Blo 1607002 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B1607087 : Blo 1607002 1607087 := bstep (se 1 (by rfl) ⟨1205315, by rfl⟩ : syracuseStep 1607087 = 2410631) B2410631
theorem B2713007 : Blo 1607002 2713007 := bstep (se 1 (by rfl) ⟨2034755, by rfl⟩ : syracuseStep 2713007 = 4069511) B4069511
theorem B1607111 : Blo 1607002 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B10298825 : Blo 1607002 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B1607131 : Blo 1607002 1607131 := bstep (se 1 (by rfl) ⟨1205348, by rfl⟩ : syracuseStep 1607131 = 2410697) B2410697
theorem B6104585 : Blo 1607002 6104585 := bstep (se 2 (by rfl) ⟨2289219, by rfl⟩ : syracuseStep 6104585 = 4578439) B4578439
theorem B1607207 : Blo 1607002 1607207 := bstep (se 1 (by rfl) ⟨1205405, by rfl⟩ : syracuseStep 1607207 = 2410811) B2410811
theorem B1607247 : Blo 1607002 1607247 := bstep (se 1 (by rfl) ⟨1205435, by rfl⟩ : syracuseStep 1607247 = 2410871) B2410871
theorem B1607263 : Blo 1607002 1607263 := bstep (se 1 (by rfl) ⟨1205447, by rfl⟩ : syracuseStep 1607263 = 2410895) B2410895
theorem B1607291 : Blo 1607002 1607291 := bstep (se 1 (by rfl) ⟨1205468, by rfl⟩ : syracuseStep 1607291 = 2410937) B2410937
theorem B1607343 : Blo 1607002 1607343 := bstep (se 1 (by rfl) ⟨1205507, by rfl⟩ : syracuseStep 1607343 = 2411015) B2411015
theorem B5424839 : Blo 1607002 5424839 := bstep (se 1 (by rfl) ⟨4068629, by rfl⟩ : syracuseStep 5424839 = 8137259) B8137259
theorem B1607367 : Blo 1607002 1607367 := bstep (se 1 (by rfl) ⟨1205525, by rfl⟩ : syracuseStep 1607367 = 2411051) B2411051
theorem B1607387 : Blo 1607002 1607387 := bstep (se 1 (by rfl) ⟨1205540, by rfl⟩ : syracuseStep 1607387 = 2411081) B2411081
theorem B2647799 : Blo 1607002 2647799 := bstep (se 1 (by rfl) ⟨1985849, by rfl⟩ : syracuseStep 2647799 = 3971699) B3971699
theorem B1607463 : Blo 1607002 1607463 := bstep (se 1 (by rfl) ⟨1205597, by rfl⟩ : syracuseStep 1607463 = 2411195) B2411195
theorem B1607503 : Blo 1607002 1607503 := bstep (se 1 (by rfl) ⟨1205627, by rfl⟩ : syracuseStep 1607503 = 2411255) B2411255
theorem B1607519 : Blo 1607002 1607519 := bstep (se 1 (by rfl) ⟨1205639, by rfl⟩ : syracuseStep 1607519 = 2411279) B2411279
theorem B2713439 : Blo 1607002 2713439 := bstep (se 1 (by rfl) ⟨2035079, by rfl⟩ : syracuseStep 2713439 = 4070159) B4070159
theorem B18311021 : Blo 1607002 18311021 := bstep (se 3 (by rfl) ⟨3433316, by rfl⟩ : syracuseStep 18311021 = 6866633) B6866633
theorem B1607547 : Blo 1607002 1607547 := bstep (se 1 (by rfl) ⟨1205660, by rfl⟩ : syracuseStep 1607547 = 2411321) B2411321
theorem B1607599 : Blo 1607002 1607599 := bstep (se 1 (by rfl) ⟨1205699, by rfl⟩ : syracuseStep 1607599 = 2411399) B2411399
theorem B10307513 : Blo 1607002 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B1607623 : Blo 1607002 1607623 := bstep (se 1 (by rfl) ⟨1205717, by rfl⟩ : syracuseStep 1607623 = 2411435) B2411435
theorem B10307537 : Blo 1607002 10307537 := bstep (se 2 (by rfl) ⟨3865326, by rfl⟩ : syracuseStep 10307537 = 7730653) B7730653
theorem B1607643 : Blo 1607002 1607643 := bstep (se 1 (by rfl) ⟨1205732, by rfl⟩ : syracuseStep 1607643 = 2411465) B2411465
theorem B27486215 : Blo 1607002 27486215 := bstep (se 1 (by rfl) ⟨20614661, by rfl⟩ : syracuseStep 27486215 = 41229323) B41229323
theorem B2410505 : Blo 1607002 2410505 := bstep (se 2 (by rfl) ⟨903939, by rfl⟩ : syracuseStep 2410505 = 1807879) B1807879
theorem B2410535 : Blo 1607002 2410535 := bstep (se 1 (by rfl) ⟨1807901, by rfl⟩ : syracuseStep 2410535 = 3615803) B3615803
theorem B1607719 : Blo 1607002 1607719 := bstep (se 1 (by rfl) ⟨1205789, by rfl⟩ : syracuseStep 1607719 = 2411579) B2411579
theorem B1607759 : Blo 1607002 1607759 := bstep (se 1 (by rfl) ⟨1205819, by rfl⟩ : syracuseStep 1607759 = 2411639) B2411639
theorem B1607775 : Blo 1607002 1607775 := bstep (se 1 (by rfl) ⟨1205831, by rfl⟩ : syracuseStep 1607775 = 2411663) B2411663
theorem B2410619 : Blo 1607002 2410619 := bstep (se 1 (by rfl) ⟨1807964, by rfl⟩ : syracuseStep 2410619 = 3615929) B3615929
theorem B1607803 : Blo 1607002 1607803 := bstep (se 1 (by rfl) ⟨1205852, by rfl⟩ : syracuseStep 1607803 = 2411705) B2411705
theorem B1607855 : Blo 1607002 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B1607879 : Blo 1607002 1607879 := bstep (se 1 (by rfl) ⟨1205909, by rfl⟩ : syracuseStep 1607879 = 2411819) B2411819
theorem B41216201 : Blo 1607002 41216201 := bstep (se 2 (by rfl) ⟨15456075, by rfl⟩ : syracuseStep 41216201 = 30912151) B30912151
theorem B1607899 : Blo 1607002 1607899 := bstep (se 1 (by rfl) ⟨1205924, by rfl⟩ : syracuseStep 1607899 = 2411849) B2411849
theorem B2410745 : Blo 1607002 2410745 := bstep (se 2 (by rfl) ⟨904029, by rfl⟩ : syracuseStep 2410745 = 1808059) B1808059
theorem B17377537 : Blo 1607002 17377537 := bstep (se 2 (by rfl) ⟨6516576, by rfl⟩ : syracuseStep 17377537 = 13033153) B13033153
theorem B1607975 : Blo 1607002 1607975 := bstep (se 1 (by rfl) ⟨1205981, by rfl⟩ : syracuseStep 1607975 = 2411963) B2411963
theorem B1608015 : Blo 1607002 1608015 := bstep (se 1 (by rfl) ⟨1206011, by rfl⟩ : syracuseStep 1608015 = 2412023) B2412023
theorem B2410847 : Blo 1607002 2410847 := bstep (se 1 (by rfl) ⟨1808135, by rfl⟩ : syracuseStep 2410847 = 3616271) B3616271
theorem B1608031 : Blo 1607002 1608031 := bstep (se 1 (by rfl) ⟨1206023, by rfl⟩ : syracuseStep 1608031 = 2412047) B2412047
theorem B2410859 : Blo 1607002 2410859 := bstep (se 1 (by rfl) ⟨1808144, by rfl⟩ : syracuseStep 2410859 = 3616289) B3616289
theorem B1608059 : Blo 1607002 1608059 := bstep (se 1 (by rfl) ⟨1206044, by rfl⟩ : syracuseStep 1608059 = 2412089) B2412089
theorem B2713999 : Blo 1607002 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B18319769 : Blo 1607002 18319769 := bstep (se 2 (by rfl) ⟨6869913, by rfl⟩ : syracuseStep 18319769 = 13739827) B13739827
theorem B1608111 : Blo 1607002 1608111 := bstep (se 1 (by rfl) ⟨1206083, by rfl⟩ : syracuseStep 1608111 = 2412167) B2412167
theorem B1608135 : Blo 1607002 1608135 := bstep (se 1 (by rfl) ⟨1206101, by rfl⟩ : syracuseStep 1608135 = 2412203) B2412203
theorem B1608155 : Blo 1607002 1608155 := bstep (se 1 (by rfl) ⟨1206116, by rfl⟩ : syracuseStep 1608155 = 2412233) B2412233
theorem B5425703 : Blo 1607002 5425703 := bstep (se 1 (by rfl) ⟨4069277, by rfl⟩ : syracuseStep 5425703 = 8138555) B8138555
theorem B1608231 : Blo 1607002 1608231 := bstep (se 1 (by rfl) ⟨1206173, by rfl⟩ : syracuseStep 1608231 = 2412347) B2412347
theorem B2411087 : Blo 1607002 2411087 := bstep (se 1 (by rfl) ⟨1808315, by rfl⟩ : syracuseStep 2411087 = 3616631) B3616631
theorem B1608271 : Blo 1607002 1608271 := bstep (se 1 (by rfl) ⟨1206203, by rfl⟩ : syracuseStep 1608271 = 2412407) B2412407
theorem B1608287 : Blo 1607002 1608287 := bstep (se 1 (by rfl) ⟨1206215, by rfl⟩ : syracuseStep 1608287 = 2412431) B2412431
theorem B1608315 : Blo 1607002 1608315 := bstep (se 1 (by rfl) ⟨1206236, by rfl⟩ : syracuseStep 1608315 = 2412473) B2412473
theorem B21179015 : Blo 1607002 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B6105739 : Blo 1607002 6105739 := bstep (se 1 (by rfl) ⟨4579304, by rfl⟩ : syracuseStep 6105739 = 9158609) B9158609
theorem B5425811 : Blo 1607002 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B10996397 : Blo 1607002 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B1608367 : Blo 1607002 1608367 := bstep (se 1 (by rfl) ⟨1206275, by rfl⟩ : syracuseStep 1608367 = 2412551) B2412551
theorem B2411207 : Blo 1607002 2411207 := bstep (se 1 (by rfl) ⟨1808405, by rfl⟩ : syracuseStep 2411207 = 3616811) B3616811
theorem B1608391 : Blo 1607002 1608391 := bstep (se 1 (by rfl) ⟨1206293, by rfl⟩ : syracuseStep 1608391 = 2412587) B2412587
theorem B9153233 : Blo 1607002 9153233 := bstep (se 2 (by rfl) ⟨3432462, by rfl⟩ : syracuseStep 9153233 = 6864925) B6864925
theorem B1608411 : Blo 1607002 1608411 := bstep (se 1 (by rfl) ⟨1206308, by rfl⟩ : syracuseStep 1608411 = 2412617) B2412617
theorem B1608487 : Blo 1607002 1608487 := bstep (se 1 (by rfl) ⟨1206365, by rfl⟩ : syracuseStep 1608487 = 2412731) B2412731
theorem B6794057 : Blo 1607002 6794057 := bstep (se 2 (by rfl) ⟨2547771, by rfl⟩ : syracuseStep 6794057 = 5095543) B5095543
theorem B1608527 : Blo 1607002 1608527 := bstep (se 1 (by rfl) ⟨1206395, by rfl⟩ : syracuseStep 1608527 = 2412791) B2412791
theorem B1608543 : Blo 1607002 1608543 := bstep (se 1 (by rfl) ⟨1206407, by rfl⟩ : syracuseStep 1608543 = 2412815) B2412815
theorem B2411369 : Blo 1607002 2411369 := bstep (se 2 (by rfl) ⟨904263, by rfl⟩ : syracuseStep 2411369 = 1808527) B1808527
theorem B5426027 : Blo 1607002 5426027 := bstep (se 1 (by rfl) ⟨4069520, by rfl⟩ : syracuseStep 5426027 = 8139041) B8139041
theorem B1608571 : Blo 1607002 1608571 := bstep (se 1 (by rfl) ⟨1206428, by rfl⟩ : syracuseStep 1608571 = 2412857) B2412857
theorem B5426081 : Blo 1607002 5426081 := bstep (se 2 (by rfl) ⟨2034780, by rfl⟩ : syracuseStep 5426081 = 4069561) B4069561
theorem B1608623 : Blo 1607002 1608623 := bstep (se 1 (by rfl) ⟨1206467, by rfl⟩ : syracuseStep 1608623 = 2412935) B2412935
theorem B2411447 : Blo 1607002 2411447 := bstep (se 1 (by rfl) ⟨1808585, by rfl⟩ : syracuseStep 2411447 = 3617171) B3617171
theorem B19565495 : Blo 1607002 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B6106043 : Blo 1607002 6106043 := bstep (se 1 (by rfl) ⟨4579532, by rfl⟩ : syracuseStep 6106043 = 9159065) B9159065
theorem B1608647 : Blo 1607002 1608647 := bstep (se 1 (by rfl) ⟨1206485, by rfl⟩ : syracuseStep 1608647 = 2412971) B2412971
theorem B2411483 : Blo 1607002 2411483 := bstep (se 1 (by rfl) ⟨1808612, by rfl⟩ : syracuseStep 2411483 = 3617225) B3617225
theorem B1608667 : Blo 1607002 1608667 := bstep (se 1 (by rfl) ⟨1206500, by rfl⟩ : syracuseStep 1608667 = 2413001) B2413001
theorem B1608743 : Blo 1607002 1608743 := bstep (se 1 (by rfl) ⟨1206557, by rfl⟩ : syracuseStep 1608743 = 2413115) B2413115
theorem B15674411 : Blo 1607002 15674411 := bstep (se 1 (by rfl) ⟨11755808, by rfl⟩ : syracuseStep 15674411 = 23511617) B23511617
theorem B2714681 : Blo 1607002 2714681 := bstep (se 2 (by rfl) ⟨1018005, by rfl⟩ : syracuseStep 2714681 = 2036011) B2036011
theorem B1608783 : Blo 1607002 1608783 := bstep (se 1 (by rfl) ⟨1206587, by rfl⟩ : syracuseStep 1608783 = 2413175) B2413175
theorem B1608799 : Blo 1607002 1608799 := bstep (se 1 (by rfl) ⟨1206599, by rfl⟩ : syracuseStep 1608799 = 2413199) B2413199
theorem B2034811 : Blo 1607002 2034811 := bstep (se 1 (by rfl) ⟨1526108, by rfl⟩ : syracuseStep 2034811 = 3052217) B3052217
theorem B1608827 : Blo 1607002 1608827 := bstep (se 1 (by rfl) ⟨1206620, by rfl⟩ : syracuseStep 1608827 = 2413241) B2413241
theorem B1608879 : Blo 1607002 1608879 := bstep (se 1 (by rfl) ⟨1206659, by rfl⟩ : syracuseStep 1608879 = 2413319) B2413319
theorem B1608903 : Blo 1607002 1608903 := bstep (se 1 (by rfl) ⟨1206677, by rfl⟩ : syracuseStep 1608903 = 2413355) B2413355
theorem B1608923 : Blo 1607002 1608923 := bstep (se 1 (by rfl) ⟨1206692, by rfl⟩ : syracuseStep 1608923 = 2413385) B2413385
theorem B15453463 : Blo 1607002 15453463 := bstep (se 1 (by rfl) ⟨11590097, by rfl⟩ : syracuseStep 15453463 = 23180195) B23180195
theorem B1608999 : Blo 1607002 1608999 := bstep (se 1 (by rfl) ⟨1206749, by rfl⟩ : syracuseStep 1608999 = 2413499) B2413499
theorem B13036889 : Blo 1607002 13036889 := bstep (se 2 (by rfl) ⟨4888833, by rfl⟩ : syracuseStep 13036889 = 9777667) B9777667
theorem B2035039 : Blo 1607002 2035039 := bstep (se 1 (by rfl) ⟨1526279, by rfl⟩ : syracuseStep 2035039 = 3052559) B3052559
theorem B9153917 : Blo 1607002 9153917 := bstep (se 3 (by rfl) ⟨1716359, by rfl⟩ : syracuseStep 9153917 = 3432719) B3432719
theorem B2411951 : Blo 1607002 2411951 := bstep (se 1 (by rfl) ⟨1808963, by rfl⟩ : syracuseStep 2411951 = 3617927) B3617927
theorem B20598259 : Blo 1607002 20598259 := bstep (se 1 (by rfl) ⟨15448694, by rfl⟩ : syracuseStep 20598259 = 30897389) B30897389
theorem B5426675 : Blo 1607002 5426675 := bstep (se 1 (by rfl) ⟨4070006, by rfl⟩ : syracuseStep 5426675 = 8140013) B8140013
theorem B3051017 : Blo 1607002 3051017 := bstep (se 2 (by rfl) ⟨1144131, by rfl⟩ : syracuseStep 3051017 = 2288263) B2288263
theorem B2412041 : Blo 1607002 2412041 := bstep (se 2 (by rfl) ⟨904515, by rfl⟩ : syracuseStep 2412041 = 1809031) B1809031
theorem B3051047 : Blo 1607002 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B2412071 : Blo 1607002 2412071 := bstep (se 1 (by rfl) ⟨1809053, by rfl⟩ : syracuseStep 2412071 = 3618107) B3618107
theorem B3616379 : Blo 1607002 3616379 := bstep (se 1 (by rfl) ⟨2712284, by rfl⟩ : syracuseStep 3616379 = 5424569) B5424569
theorem B2412155 : Blo 1607002 2412155 := bstep (se 1 (by rfl) ⟨1809116, by rfl⟩ : syracuseStep 2412155 = 3618233) B3618233
theorem B19566269 : Blo 1607002 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B3616505 : Blo 1607002 3616505 := bstep (se 2 (by rfl) ⟨1356189, by rfl⟩ : syracuseStep 3616505 = 2712379) B2712379
theorem B2445049 : Blo 1607002 2445049 := bstep (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) B1833787
theorem B2412281 : Blo 1607002 2412281 := bstep (se 2 (by rfl) ⟨904605, by rfl⟩ : syracuseStep 2412281 = 1809211) B1809211
theorem B2412383 : Blo 1607002 2412383 := bstep (se 1 (by rfl) ⟨1809287, by rfl⟩ : syracuseStep 2412383 = 3618575) B3618575
theorem B2412395 : Blo 1607002 2412395 := bstep (se 1 (by rfl) ⟨1809296, by rfl⟩ : syracuseStep 2412395 = 3618593) B3618593
theorem B2035631 : Blo 1607002 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B3616775 : Blo 1607002 3616775 := bstep (se 1 (by rfl) ⟨2712581, by rfl⟩ : syracuseStep 3616775 = 5425163) B5425163
theorem B5427215 : Blo 1607002 5427215 := bstep (se 1 (by rfl) ⟨4070411, by rfl⟩ : syracuseStep 5427215 = 8140823) B8140823
theorem B3616847 : Blo 1607002 3616847 := bstep (se 1 (by rfl) ⟨2712635, by rfl⟩ : syracuseStep 3616847 = 5425271) B5425271
theorem B2412623 : Blo 1607002 2412623 := bstep (se 1 (by rfl) ⟨1809467, by rfl⟩ : syracuseStep 2412623 = 3618935) B3618935
theorem B1716347 : Blo 1607002 1716347 := bstep (se 1 (by rfl) ⟨1287260, by rfl⟩ : syracuseStep 1716347 = 2574521) B2574521
theorem B2412743 : Blo 1607002 2412743 := bstep (se 1 (by rfl) ⟨1809557, by rfl⟩ : syracuseStep 2412743 = 3619115) B3619115
theorem B3051731 : Blo 1607002 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B3051769 : Blo 1607002 3051769 := bstep (se 2 (by rfl) ⟨1144413, by rfl⟩ : syracuseStep 3051769 = 2288827) B2288827
theorem B2412905 : Blo 1607002 2412905 := bstep (se 2 (by rfl) ⟨904839, by rfl⟩ : syracuseStep 2412905 = 1809679) B1809679
theorem B10301849 : Blo 1607002 10301849 := bstep (se 2 (by rfl) ⟨3863193, by rfl⟩ : syracuseStep 10301849 = 7726387) B7726387
theorem B2412983 : Blo 1607002 2412983 := bstep (se 1 (by rfl) ⟨1809737, by rfl⟩ : syracuseStep 2412983 = 3619475) B3619475
theorem B104280533 : Blo 1607002 104280533 := bstep (se 7 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 104280533 = 2444075) B2444075
theorem B3617243 : Blo 1607002 3617243 := bstep (se 1 (by rfl) ⟨2712932, by rfl⟩ : syracuseStep 3617243 = 5425865) B5425865
theorem B2413019 : Blo 1607002 2413019 := bstep (se 1 (by rfl) ⟨1809764, by rfl⟩ : syracuseStep 2413019 = 3619529) B3619529
theorem B5427809 : Blo 1607002 5427809 := bstep (se 2 (by rfl) ⟨2035428, by rfl⟩ : syracuseStep 5427809 = 4070857) B4070857
theorem B18313937 : Blo 1607002 18313937 := bstep (se 2 (by rfl) ⟨6867726, by rfl⟩ : syracuseStep 18313937 = 13735453) B13735453
theorem B5223241 : Blo 1607002 5223241 := bstep (se 2 (by rfl) ⟨1958715, by rfl⟩ : syracuseStep 5223241 = 3917431) B3917431
theorem B3617711 : Blo 1607002 3617711 := bstep (se 1 (by rfl) ⟨2713283, by rfl⟩ : syracuseStep 3617711 = 5426567) B5426567
theorem B2413487 : Blo 1607002 2413487 := bstep (se 1 (by rfl) ⟨1810115, by rfl⟩ : syracuseStep 2413487 = 3620231) B3620231
theorem B2749367 : Blo 1607002 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B3052475 : Blo 1607002 3052475 := bstep (se 1 (by rfl) ⟨2289356, by rfl⟩ : syracuseStep 3052475 = 4578713) B4578713
theorem B6870035 : Blo 1607002 6870035 := bstep (se 1 (by rfl) ⟨5152526, by rfl⟩ : syracuseStep 6870035 = 10305053) B10305053
theorem B4346959 : Blo 1607002 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B6517841 : Blo 1607002 6517841 := bstep (se 2 (by rfl) ⟨2444190, by rfl⟩ : syracuseStep 6517841 = 4888381) B4888381
theorem B3617963 : Blo 1607002 3617963 := bstep (se 1 (by rfl) ⟨2713472, by rfl⟩ : syracuseStep 3617963 = 5426945) B5426945
theorem B6870187 : Blo 1607002 6870187 := bstep (se 1 (by rfl) ⟨5152640, by rfl⟩ : syracuseStep 6870187 = 10305281) B10305281
theorem B7730423 : Blo 1607002 7730423 := bstep (se 1 (by rfl) ⟨5797817, by rfl⟩ : syracuseStep 7730423 = 11595635) B11595635
theorem B12539225 : Blo 1607002 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B4068751 : Blo 1607002 4068751 := bstep (se 1 (by rfl) ⟨3051563, by rfl⟩ : syracuseStep 4068751 = 6103127) B6103127
theorem B8140175 : Blo 1607002 8140175 := bstep (se 1 (by rfl) ⟨6105131, by rfl⟩ : syracuseStep 8140175 = 12210263) B12210263
theorem B3052961 : Blo 1607002 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B1807951 : Blo 1607002 1807951 := bstep (se 1 (by rfl) ⟨1355963, by rfl⟩ : syracuseStep 1807951 = 2711927) B2711927
theorem B3053227 : Blo 1607002 3053227 := bstep (se 1 (by rfl) ⟨2289920, by rfl⟩ : syracuseStep 3053227 = 4579841) B4579841
theorem B3667655 : Blo 1607002 3667655 := bstep (se 1 (by rfl) ⟨2750741, by rfl⟩ : syracuseStep 3667655 = 5501483) B5501483
theorem B3618503 : Blo 1607002 3618503 := bstep (se 1 (by rfl) ⟨2713877, by rfl⟩ : syracuseStep 3618503 = 5427755) B5427755
theorem B4069075 : Blo 1607002 4069075 := bstep (se 1 (by rfl) ⟨3051806, by rfl⟩ : syracuseStep 4069075 = 6103613) B6103613
theorem B8689373 : Blo 1607002 8689373 := bstep (se 3 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 8689373 = 3258515) B3258515
theorem B1718111 : Blo 1607002 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B26089397 : Blo 1607002 26089397 := bstep (se 5 (by rfl) ⟨1222940, by rfl⟩ : syracuseStep 26089397 = 2445881) B2445881
theorem B1808347 : Blo 1607002 1808347 := bstep (se 1 (by rfl) ⟨1356260, by rfl⟩ : syracuseStep 1808347 = 2712521) B2712521
theorem B3053531 : Blo 1607002 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B4347911 : Blo 1607002 4347911 := bstep (se 1 (by rfl) ⟨3260933, by rfl⟩ : syracuseStep 4347911 = 6521867) B6521867
theorem B5429267 : Blo 1607002 5429267 := bstep (se 1 (by rfl) ⟨4071950, by rfl⟩ : syracuseStep 5429267 = 8143901) B8143901
theorem B5429591 : Blo 1607002 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B1808815 : Blo 1607002 1808815 := bstep (se 1 (by rfl) ⟨1356611, by rfl⟩ : syracuseStep 1808815 = 2713223) B2713223
theorem B8698349 : Blo 1607002 8698349 := bstep (se 3 (by rfl) ⟨1630940, by rfl⟩ : syracuseStep 8698349 = 3261881) B3261881
theorem B21764641 : Blo 1607002 21764641 := bstep (se 2 (by rfl) ⟨8161740, by rfl⟩ : syracuseStep 21764641 = 16323481) B16323481
theorem B3619367 : Blo 1607002 3619367 := bstep (se 1 (by rfl) ⟨2714525, by rfl⟩ : syracuseStep 3619367 = 5429051) B5429051
theorem B41777707 : Blo 1607002 41777707 := bstep (se 1 (by rfl) ⟨31333280, by rfl⟩ : syracuseStep 41777707 = 62666561) B62666561
theorem B6101639 : Blo 1607002 6101639 := bstep (se 1 (by rfl) ⟨4576229, by rfl⟩ : syracuseStep 6101639 = 9152459) B9152459
theorem B4070027 : Blo 1607002 4070027 := bstep (se 1 (by rfl) ⟨3052520, by rfl⟩ : syracuseStep 4070027 = 6105041) B6105041
theorem B7338707 : Blo 1607002 7338707 := bstep (se 1 (by rfl) ⟨5504030, by rfl⟩ : syracuseStep 7338707 = 11008061) B11008061
theorem B2898679 : Blo 1607002 2898679 := bstep (se 1 (by rfl) ⟨2174009, by rfl⟩ : syracuseStep 2898679 = 4348019) B4348019
theorem B1809247 : Blo 1607002 1809247 := bstep (se 1 (by rfl) ⟨1356935, by rfl⟩ : syracuseStep 1809247 = 2713871) B2713871
theorem B3619691 : Blo 1607002 3619691 := bstep (se 1 (by rfl) ⟨2714768, by rfl⟩ : syracuseStep 3619691 = 5429537) B5429537
theorem B3619745 : Blo 1607002 3619745 := bstep (se 2 (by rfl) ⟨1357404, by rfl⟩ : syracuseStep 3619745 = 2714809) B2714809
theorem B3865519 : Blo 1607002 3865519 := bstep (se 1 (by rfl) ⟨2899139, by rfl⟩ : syracuseStep 3865519 = 5798279) B5798279
theorem B4578383 : Blo 1607002 4578383 := bstep (se 1 (by rfl) ⟨3433787, by rfl⟩ : syracuseStep 4578383 = 6867575) B6867575
theorem B11590735 : Blo 1607002 11590735 := bstep (se 1 (by rfl) ⟨8693051, by rfl⟩ : syracuseStep 11590735 = 17386103) B17386103
theorem B1809607 : Blo 1607002 1809607 := bstep (se 1 (by rfl) ⟨1357205, by rfl⟩ : syracuseStep 1809607 = 2714411) B2714411
theorem B3620087 : Blo 1607002 3620087 := bstep (se 1 (by rfl) ⟨2715065, by rfl⟩ : syracuseStep 3620087 = 5430131) B5430131
theorem B17669549 : Blo 1607002 17669549 := bstep (se 3 (by rfl) ⟨3313040, by rfl⟩ : syracuseStep 17669549 = 6626081) B6626081
theorem B111336889 : Blo 1607002 111336889 := bstep (se 2 (by rfl) ⟨41751333, by rfl⟩ : syracuseStep 111336889 = 83502667) B83502667
theorem B3095995 : Blo 1607002 3095995 := bstep (se 1 (by rfl) ⟨2321996, by rfl⟩ : syracuseStep 3095995 = 4643993) B4643993
theorem B8142281 : Blo 1607002 8142281 := bstep (se 2 (by rfl) ⟨3053355, by rfl⟩ : syracuseStep 8142281 = 6106711) B6106711
theorem B46358081 : Blo 1607002 46358081 := bstep (se 2 (by rfl) ⟨17384280, by rfl⟩ : syracuseStep 46358081 = 34768561) B34768561
theorem B9158291 : Blo 1607002 9158291 := bstep (se 1 (by rfl) ⟨6868718, by rfl⟩ : syracuseStep 9158291 = 13737437) B13737437
theorem B6864583 : Blo 1607002 6864583 := bstep (se 1 (by rfl) ⟨5148437, by rfl⟩ : syracuseStep 6864583 = 10296875) B10296875
theorem B4579031 : Blo 1607002 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B4071161 : Blo 1607002 4071161 := bstep (se 2 (by rfl) ⟨1526685, by rfl⟩ : syracuseStep 4071161 = 3053371) B3053371
theorem B31325957 : Blo 1607002 31325957 := bstep (se 4 (by rfl) ⟨2936808, by rfl⟩ : syracuseStep 31325957 = 5873617) B5873617
theorem B12214151 : Blo 1607002 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B4071343 : Blo 1607002 4071343 := bstep (se 1 (by rfl) ⟨3053507, by rfl⟩ : syracuseStep 4071343 = 6107015) B6107015
theorem B4580023 : Blo 1607002 4580023 := bstep (se 1 (by rfl) ⟨3435017, by rfl⟩ : syracuseStep 4580023 = 6870035) B6870035
theorem B55673675 : Blo 1607002 55673675 := bstep (se 1 (by rfl) ⟨41755256, by rfl⟩ : syracuseStep 55673675 = 83510513) B83510513
theorem B5153615 : Blo 1607002 5153615 := bstep (se 1 (by rfl) ⟨3865211, by rfl⟩ : syracuseStep 5153615 = 7730423) B7730423
theorem B6865883 : Blo 1607002 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B6964321 : Blo 1607002 6964321 := bstep (se 2 (by rfl) ⟨2611620, by rfl⟩ : syracuseStep 6964321 = 5223241) B5223241
theorem B5792915 : Blo 1607002 5792915 := bstep (se 1 (by rfl) ⟨4344686, by rfl⟩ : syracuseStep 5792915 = 8689373) B8689373
theorem B5154025 : Blo 1607002 5154025 := bstep (se 2 (by rfl) ⟨1932759, by rfl⟩ : syracuseStep 5154025 = 3865519) B3865519
theorem B12207347 : Blo 1607002 12207347 := bstep (se 1 (by rfl) ⟨9155510, by rfl⟩ : syracuseStep 12207347 = 18311021) B18311021
theorem B17392931 : Blo 1607002 17392931 := bstep (se 1 (by rfl) ⟨13044698, by rfl⟩ : syracuseStep 17392931 = 26089397) B26089397
theorem B1607003 : Blo 1607002 1607003 := bstep (se 1 (by rfl) ⟨1205252, by rfl⟩ : syracuseStep 1607003 = 2410505) B2410505
theorem B1607023 : Blo 1607002 1607023 := bstep (se 1 (by rfl) ⟨1205267, by rfl⟩ : syracuseStep 1607023 = 2410535) B2410535
theorem B1607079 : Blo 1607002 1607079 := bstep (se 1 (by rfl) ⟨1205309, by rfl⟩ : syracuseStep 1607079 = 2410619) B2410619
theorem B8136125 : Blo 1607002 8136125 := bstep (se 3 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 8136125 = 3051047) B3051047
theorem B27477467 : Blo 1607002 27477467 := bstep (se 1 (by rfl) ⟨20608100, by rfl⟩ : syracuseStep 27477467 = 41216201) B41216201
theorem B2713081 : Blo 1607002 2713081 := bstep (se 2 (by rfl) ⟨1017405, by rfl⟩ : syracuseStep 2713081 = 2034811) B2034811
theorem B1607163 : Blo 1607002 1607163 := bstep (se 1 (by rfl) ⟨1205372, by rfl⟩ : syracuseStep 1607163 = 2410745) B2410745
theorem B9160249 : Blo 1607002 9160249 := bstep (se 2 (by rfl) ⟨3435093, by rfl⟩ : syracuseStep 9160249 = 6870187) B6870187
theorem B1607231 : Blo 1607002 1607231 := bstep (se 1 (by rfl) ⟨1205423, by rfl⟩ : syracuseStep 1607231 = 2410847) B2410847
theorem B1607239 : Blo 1607002 1607239 := bstep (se 1 (by rfl) ⟨1205429, by rfl⟩ : syracuseStep 1607239 = 2410859) B2410859
theorem B20604617 : Blo 1607002 20604617 := bstep (se 2 (by rfl) ⟨7726731, by rfl⟩ : syracuseStep 20604617 = 15453463) B15453463
theorem B1607391 : Blo 1607002 1607391 := bstep (se 1 (by rfl) ⟨1205543, by rfl⟩ : syracuseStep 1607391 = 2411087) B2411087
theorem B2713351 : Blo 1607002 2713351 := bstep (se 1 (by rfl) ⟨2035013, by rfl⟩ : syracuseStep 2713351 = 4070027) B4070027
theorem B2713385 : Blo 1607002 2713385 := bstep (se 2 (by rfl) ⟨1017519, by rfl⟩ : syracuseStep 2713385 = 2035039) B2035039
theorem B1607471 : Blo 1607002 1607471 := bstep (se 1 (by rfl) ⟨1205603, by rfl⟩ : syracuseStep 1607471 = 2411207) B2411207
theorem B4892471 : Blo 1607002 4892471 := bstep (se 1 (by rfl) ⟨3669353, by rfl⟩ : syracuseStep 4892471 = 7338707) B7338707
theorem B5425001 : Blo 1607002 5425001 := bstep (se 2 (by rfl) ⟨2034375, by rfl⟩ : syracuseStep 5425001 = 4068751) B4068751
theorem B1607579 : Blo 1607002 1607579 := bstep (se 1 (by rfl) ⟨1205684, by rfl⟩ : syracuseStep 1607579 = 2411369) B2411369
theorem B148449185 : Blo 1607002 148449185 := bstep (se 2 (by rfl) ⟨55668444, by rfl⟩ : syracuseStep 148449185 = 111336889) B111336889
theorem B1607631 : Blo 1607002 1607631 := bstep (se 1 (by rfl) ⟨1205723, by rfl⟩ : syracuseStep 1607631 = 2411447) B2411447
theorem B13043663 : Blo 1607002 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B1607655 : Blo 1607002 1607655 := bstep (se 1 (by rfl) ⟨1205741, by rfl⟩ : syracuseStep 1607655 = 2411483) B2411483
theorem B2410601 : Blo 1607002 2410601 := bstep (se 2 (by rfl) ⟨903975, by rfl⟩ : syracuseStep 2410601 = 1807951) B1807951
theorem B4581629 : Blo 1607002 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B9152777 : Blo 1607002 9152777 := bstep (se 2 (by rfl) ⟨3432291, by rfl⟩ : syracuseStep 9152777 = 6864583) B6864583
theorem B5425433 : Blo 1607002 5425433 := bstep (se 2 (by rfl) ⟨2034537, by rfl⟩ : syracuseStep 5425433 = 4069075) B4069075
theorem B1607967 : Blo 1607002 1607967 := bstep (se 1 (by rfl) ⟨1205975, by rfl⟩ : syracuseStep 1607967 = 2411951) B2411951
theorem B2034011 : Blo 1607002 2034011 := bstep (se 1 (by rfl) ⟨1525508, by rfl⟩ : syracuseStep 2034011 = 3051017) B3051017
theorem B1608027 : Blo 1607002 1608027 := bstep (se 1 (by rfl) ⟨1206020, by rfl⟩ : syracuseStep 1608027 = 2412041) B2412041
theorem B1608047 : Blo 1607002 1608047 := bstep (se 1 (by rfl) ⟨1206035, by rfl⟩ : syracuseStep 1608047 = 2412071) B2412071
theorem B2410919 : Blo 1607002 2410919 := bstep (se 1 (by rfl) ⟨1808189, by rfl⟩ : syracuseStep 2410919 = 3616379) B3616379
theorem B1608103 : Blo 1607002 1608103 := bstep (se 1 (by rfl) ⟨1206077, by rfl⟩ : syracuseStep 1608103 = 2412155) B2412155
theorem B6105527 : Blo 1607002 6105527 := bstep (se 1 (by rfl) ⟨4579145, by rfl⟩ : syracuseStep 6105527 = 9158291) B9158291
theorem B13044179 : Blo 1607002 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B2411003 : Blo 1607002 2411003 := bstep (se 1 (by rfl) ⟨1808252, by rfl⟩ : syracuseStep 2411003 = 3616505) B3616505
theorem B1608187 : Blo 1607002 1608187 := bstep (se 1 (by rfl) ⟨1206140, by rfl⟩ : syracuseStep 1608187 = 2412281) B2412281
theorem B2714107 : Blo 1607002 2714107 := bstep (se 1 (by rfl) ⟨2035580, by rfl⟩ : syracuseStep 2714107 = 4071161) B4071161
theorem B20883971 : Blo 1607002 20883971 := bstep (se 1 (by rfl) ⟨15662978, by rfl⟩ : syracuseStep 20883971 = 31325957) B31325957
theorem B1608255 : Blo 1607002 1608255 := bstep (se 1 (by rfl) ⟨1206191, by rfl⟩ : syracuseStep 1608255 = 2412383) B2412383
theorem B1608263 : Blo 1607002 1608263 := bstep (se 1 (by rfl) ⟨1206197, by rfl⟩ : syracuseStep 1608263 = 2412395) B2412395
theorem B2411129 : Blo 1607002 2411129 := bstep (se 2 (by rfl) ⟨904173, by rfl⟩ : syracuseStep 2411129 = 1808347) B1808347
theorem B2411183 : Blo 1607002 2411183 := bstep (se 1 (by rfl) ⟨1808387, by rfl⟩ : syracuseStep 2411183 = 3616775) B3616775
theorem B2411231 : Blo 1607002 2411231 := bstep (se 1 (by rfl) ⟨1808423, by rfl⟩ : syracuseStep 2411231 = 3616847) B3616847
theorem B2173663 : Blo 1607002 2173663 := bstep (se 1 (by rfl) ⟨1630247, by rfl⟩ : syracuseStep 2173663 = 3260495) B3260495
theorem B1608415 : Blo 1607002 1608415 := bstep (se 1 (by rfl) ⟨1206311, by rfl⟩ : syracuseStep 1608415 = 2412623) B2412623
theorem B12069665 : Blo 1607002 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B1608495 : Blo 1607002 1608495 := bstep (se 1 (by rfl) ⟨1206371, by rfl⟩ : syracuseStep 1608495 = 2412743) B2412743
theorem B2034487 : Blo 1607002 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B1608603 : Blo 1607002 1608603 := bstep (se 1 (by rfl) ⟨1206452, by rfl⟩ : syracuseStep 1608603 = 2412905) B2412905
theorem B2714539 : Blo 1607002 2714539 := bstep (se 1 (by rfl) ⟨2035904, by rfl⟩ : syracuseStep 2714539 = 4071809) B4071809
theorem B6867899 : Blo 1607002 6867899 := bstep (se 1 (by rfl) ⟨5150924, by rfl⟩ : syracuseStep 6867899 = 10301849) B10301849
theorem B1608655 : Blo 1607002 1608655 := bstep (se 1 (by rfl) ⟨1206491, by rfl⟩ : syracuseStep 1608655 = 2412983) B2412983
theorem B69520355 : Blo 1607002 69520355 := bstep (se 1 (by rfl) ⟨52140266, by rfl⟩ : syracuseStep 69520355 = 104280533) B104280533
theorem B2411495 : Blo 1607002 2411495 := bstep (se 1 (by rfl) ⟨1808621, by rfl⟩ : syracuseStep 2411495 = 3617243) B3617243
theorem B1608679 : Blo 1607002 1608679 := bstep (se 1 (by rfl) ⟨1206509, by rfl⟩ : syracuseStep 1608679 = 2413019) B2413019
theorem B23170049 : Blo 1607002 23170049 := bstep (se 2 (by rfl) ⟨8688768, by rfl⟩ : syracuseStep 23170049 = 17377537) B17377537
theorem B15674435 : Blo 1607002 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B12209291 : Blo 1607002 12209291 := bstep (se 1 (by rfl) ⟨9156968, by rfl⟩ : syracuseStep 12209291 = 18313937) B18313937
theorem B2714843 : Blo 1607002 2714843 := bstep (se 1 (by rfl) ⟨2036132, by rfl⟩ : syracuseStep 2714843 = 4072265) B4072265
theorem B2411753 : Blo 1607002 2411753 := bstep (se 2 (by rfl) ⟨904407, by rfl⟩ : syracuseStep 2411753 = 1808815) B1808815
theorem B18312479 : Blo 1607002 18312479 := bstep (se 1 (by rfl) ⟨13734359, by rfl⟩ : syracuseStep 18312479 = 27468719) B27468719
theorem B2411807 : Blo 1607002 2411807 := bstep (se 1 (by rfl) ⟨1808855, by rfl⟩ : syracuseStep 2411807 = 3617711) B3617711
theorem B1608991 : Blo 1607002 1608991 := bstep (se 1 (by rfl) ⟨1206743, by rfl⟩ : syracuseStep 1608991 = 2413487) B2413487
theorem B2288935 : Blo 1607002 2288935 := bstep (se 1 (by rfl) ⟨1716701, by rfl⟩ : syracuseStep 2288935 = 3433403) B3433403
theorem B2034983 : Blo 1607002 2034983 := bstep (se 1 (by rfl) ⟨1526237, by rfl⟩ : syracuseStep 2034983 = 3052475) B3052475
theorem B29019521 : Blo 1607002 29019521 := bstep (se 2 (by rfl) ⟨10882320, by rfl⟩ : syracuseStep 29019521 = 21764641) B21764641
theorem B3616199 : Blo 1607002 3616199 := bstep (se 1 (by rfl) ⟨2712149, by rfl⟩ : syracuseStep 3616199 = 5424299) B5424299
theorem B2411975 : Blo 1607002 2411975 := bstep (se 1 (by rfl) ⟨1808981, by rfl⟩ : syracuseStep 2411975 = 3617963) B3617963
theorem B2715079 : Blo 1607002 2715079 := bstep (se 1 (by rfl) ⟨2036309, by rfl⟩ : syracuseStep 2715079 = 4072619) B4072619
theorem B5426783 : Blo 1607002 5426783 := bstep (se 1 (by rfl) ⟨4070087, by rfl⟩ : syracuseStep 5426783 = 8140175) B8140175
theorem B2035307 : Blo 1607002 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B2412329 : Blo 1607002 2412329 := bstep (se 2 (by rfl) ⟨904623, by rfl⟩ : syracuseStep 2412329 = 1809247) B1809247
theorem B3616559 : Blo 1607002 3616559 := bstep (se 1 (by rfl) ⟨2712419, by rfl⟩ : syracuseStep 3616559 = 5424839) B5424839
theorem B2445103 : Blo 1607002 2445103 := bstep (se 1 (by rfl) ⟨1833827, by rfl⟩ : syracuseStep 2445103 = 3667655) B3667655
theorem B2412335 : Blo 1607002 2412335 := bstep (se 1 (by rfl) ⟨1809251, by rfl⟩ : syracuseStep 2412335 = 3618503) B3618503
theorem B1765199 : Blo 1607002 1765199 := bstep (se 1 (by rfl) ⟨1323899, by rfl⟩ : syracuseStep 1765199 = 2647799) B2647799
theorem B2035687 : Blo 1607002 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B15454313 : Blo 1607002 15454313 := bstep (se 2 (by rfl) ⟨5795367, by rfl⟩ : syracuseStep 15454313 = 11590735) B11590735
theorem B5795945 : Blo 1607002 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B2412809 : Blo 1607002 2412809 := bstep (se 2 (by rfl) ⟨904803, by rfl⟩ : syracuseStep 2412809 = 1809607) B1809607
theorem B3617135 : Blo 1607002 3617135 := bstep (se 1 (by rfl) ⟨2712851, by rfl⟩ : syracuseStep 3617135 = 5425703) B5425703
theorem B2412911 : Blo 1607002 2412911 := bstep (se 1 (by rfl) ⟨1809683, by rfl⟩ : syracuseStep 2412911 = 3619367) B3619367
theorem B4067759 : Blo 1607002 4067759 := bstep (se 1 (by rfl) ⟨3050819, by rfl⟩ : syracuseStep 4067759 = 6101639) B6101639
theorem B14119343 : Blo 1607002 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B3617207 : Blo 1607002 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B12210749 : Blo 1607002 12210749 := bstep (se 3 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 12210749 = 4579031) B4579031
theorem B3617351 : Blo 1607002 3617351 := bstep (se 1 (by rfl) ⟨2713013, by rfl⟩ : syracuseStep 3617351 = 5426027) B5426027
theorem B2413127 : Blo 1607002 2413127 := bstep (se 1 (by rfl) ⟨1809845, by rfl⟩ : syracuseStep 2413127 = 3619691) B3619691
theorem B3617387 : Blo 1607002 3617387 := bstep (se 1 (by rfl) ⟨2713040, by rfl⟩ : syracuseStep 3617387 = 5426081) B5426081
theorem B2413163 : Blo 1607002 2413163 := bstep (se 1 (by rfl) ⟨1809872, by rfl⟩ : syracuseStep 2413163 = 3619745) B3619745
theorem B27464345 : Blo 1607002 27464345 := bstep (se 2 (by rfl) ⟨10299129, by rfl⟩ : syracuseStep 27464345 = 20598259) B20598259
theorem B10449607 : Blo 1607002 10449607 := bstep (se 1 (by rfl) ⟨7837205, by rfl⟩ : syracuseStep 10449607 = 15674411) B15674411
theorem B3052255 : Blo 1607002 3052255 := bstep (se 1 (by rfl) ⟨2289191, by rfl⟩ : syracuseStep 3052255 = 4578383) B4578383
theorem B2413391 : Blo 1607002 2413391 := bstep (se 1 (by rfl) ⟨1810043, by rfl⟩ : syracuseStep 2413391 = 3620087) B3620087
theorem B5428187 : Blo 1607002 5428187 := bstep (se 1 (by rfl) ⟨4071140, by rfl⟩ : syracuseStep 5428187 = 8142281) B8142281
theorem B3617783 : Blo 1607002 3617783 := bstep (se 1 (by rfl) ⟨2713337, by rfl⟩ : syracuseStep 3617783 = 5426675) B5426675
theorem B30905387 : Blo 1607002 30905387 := bstep (se 1 (by rfl) ⟨23179040, by rfl⟩ : syracuseStep 30905387 = 46358081) B46358081
theorem B5428349 : Blo 1607002 5428349 := bstep (se 3 (by rfl) ⟨1017815, by rfl⟩ : syracuseStep 5428349 = 2035631) B2035631
theorem B5428457 : Blo 1607002 5428457 := bstep (se 2 (by rfl) ⟨2035671, by rfl⟩ : syracuseStep 5428457 = 4071343) B4071343
theorem B6870359 : Blo 1607002 6870359 := bstep (se 1 (by rfl) ⟨5152769, by rfl⟩ : syracuseStep 6870359 = 10305539) B10305539
theorem B3618143 : Blo 1607002 3618143 := bstep (se 1 (by rfl) ⟨2713607, by rfl⟩ : syracuseStep 3618143 = 5427215) B5427215
theorem B4068731 : Blo 1607002 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B5428619 : Blo 1607002 5428619 := bstep (se 1 (by rfl) ⟨4071464, by rfl⟩ : syracuseStep 5428619 = 8142929) B8142929
theorem B10999243 : Blo 1607002 10999243 := bstep (se 1 (by rfl) ⟨8249432, by rfl⟩ : syracuseStep 10999243 = 16498865) B16498865
theorem B7722503 : Blo 1607002 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B17380909 : Blo 1607002 17380909 := bstep (se 3 (by rfl) ⟨3258920, by rfl⟩ : syracuseStep 17380909 = 6517841) B6517841
theorem B4576925 : Blo 1607002 4576925 := bstep (se 3 (by rfl) ⟨858173, by rfl⟩ : syracuseStep 4576925 = 1716347) B1716347
theorem B4069025 : Blo 1607002 4069025 := bstep (se 2 (by rfl) ⟨1525884, by rfl⟩ : syracuseStep 4069025 = 3051769) B3051769
theorem B1808095 : Blo 1607002 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B3618539 : Blo 1607002 3618539 := bstep (se 1 (by rfl) ⟨2713904, by rfl⟩ : syracuseStep 3618539 = 5427809) B5427809
theorem B3618665 : Blo 1607002 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B1832911 : Blo 1607002 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B55703609 : Blo 1607002 55703609 := bstep (se 2 (by rfl) ⟨20888853, by rfl⟩ : syracuseStep 55703609 = 41777707) B41777707
theorem B8140985 : Blo 1607002 8140985 := bstep (se 2 (by rfl) ⟨3052869, by rfl⟩ : syracuseStep 8140985 = 6105739) B6105739
theorem B33437933 : Blo 1607002 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B8698109 : Blo 1607002 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B1808671 : Blo 1607002 1808671 := bstep (se 1 (by rfl) ⟨1356503, by rfl⟩ : syracuseStep 1808671 = 2713007) B2713007
theorem B3864905 : Blo 1607002 3864905 := bstep (se 2 (by rfl) ⟨1449339, by rfl⟩ : syracuseStep 3864905 = 2898679) B2898679
theorem B4069723 : Blo 1607002 4069723 := bstep (se 1 (by rfl) ⟨3052292, by rfl⟩ : syracuseStep 4069723 = 6104585) B6104585
theorem B47118797 : Blo 1607002 47118797 := bstep (se 3 (by rfl) ⟨8834774, by rfl⟩ : syracuseStep 47118797 = 17669549) B17669549
theorem B1808959 : Blo 1607002 1808959 := bstep (se 1 (by rfl) ⟨1356719, by rfl⟩ : syracuseStep 1808959 = 2713439) B2713439
theorem B6871675 : Blo 1607002 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B13040261 : Blo 1607002 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B6871691 : Blo 1607002 6871691 := bstep (se 1 (by rfl) ⟨5153768, by rfl⟩ : syracuseStep 6871691 = 10307537) B10307537
theorem B2898607 : Blo 1607002 2898607 := bstep (se 1 (by rfl) ⟨2173955, by rfl⟩ : syracuseStep 2898607 = 4347911) B4347911
theorem B18324143 : Blo 1607002 18324143 := bstep (se 1 (by rfl) ⟨13743107, by rfl⟩ : syracuseStep 18324143 = 27486215) B27486215
theorem B3619511 : Blo 1607002 3619511 := bstep (se 1 (by rfl) ⟨2714633, by rfl⟩ : syracuseStep 3619511 = 5429267) B5429267
theorem B3619727 : Blo 1607002 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B12213179 : Blo 1607002 12213179 := bstep (se 1 (by rfl) ⟨9159884, by rfl⟩ : syracuseStep 12213179 = 18319769) B18319769
theorem B5798899 : Blo 1607002 5798899 := bstep (se 1 (by rfl) ⟨4349174, by rfl⟩ : syracuseStep 5798899 = 8698349) B8698349
theorem B7330931 : Blo 1607002 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B6102155 : Blo 1607002 6102155 := bstep (se 1 (by rfl) ⟨4576616, by rfl⟩ : syracuseStep 6102155 = 9153233) B9153233
theorem B4529371 : Blo 1607002 4529371 := bstep (se 1 (by rfl) ⟨3397028, by rfl⟩ : syracuseStep 4529371 = 6794057) B6794057
theorem B4127993 : Blo 1607002 4127993 := bstep (se 2 (by rfl) ⟨1547997, by rfl⟩ : syracuseStep 4127993 = 3095995) B3095995
theorem B4070695 : Blo 1607002 4070695 := bstep (se 1 (by rfl) ⟨3053021, by rfl⟩ : syracuseStep 4070695 = 6106043) B6106043
theorem B1809787 : Blo 1607002 1809787 := bstep (se 1 (by rfl) ⟨1357340, by rfl⟩ : syracuseStep 1809787 = 2714681) B2714681
theorem B4070969 : Blo 1607002 4070969 := bstep (se 2 (by rfl) ⟨1526613, by rfl⟩ : syracuseStep 4070969 = 3053227) B3053227
theorem B8691259 : Blo 1607002 8691259 := bstep (se 1 (by rfl) ⟨6518444, by rfl⟩ : syracuseStep 8691259 = 13036889) B13036889
theorem B6102611 : Blo 1607002 6102611 := bstep (se 1 (by rfl) ⟨4576958, by rfl⟩ : syracuseStep 6102611 = 9153917) B9153917
theorem B8142767 : Blo 1607002 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B2711839 : Blo 1607002 2711839 := bstep (se 1 (by rfl) ⟨2033879, by rfl⟩ : syracuseStep 2711839 = 4067759) B4067759
theorem B9412895 : Blo 1607002 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B18309563 : Blo 1607002 18309563 := bstep (se 1 (by rfl) ⟨13732172, by rfl⟩ : syracuseStep 18309563 = 27464345) B27464345
theorem B20603591 : Blo 1607002 20603591 := bstep (se 1 (by rfl) ⟨15452693, by rfl⟩ : syracuseStep 20603591 = 30905387) B30905387
theorem B4580239 : Blo 1607002 4580239 := bstep (se 1 (by rfl) ⟨3435179, by rfl⟩ : syracuseStep 4580239 = 6870359) B6870359
theorem B5424029 : Blo 1607002 5424029 := bstep (se 3 (by rfl) ⟨1017005, by rfl⟩ : syracuseStep 5424029 = 2034011) B2034011
theorem B2712487 : Blo 1607002 2712487 := bstep (se 1 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 2712487 = 4068731) B4068731
theorem B5424083 : Blo 1607002 5424083 := bstep (se 1 (by rfl) ⟨4068062, by rfl⟩ : syracuseStep 5424083 = 8136125) B8136125
theorem B18318311 : Blo 1607002 18318311 := bstep (se 1 (by rfl) ⟨13738733, by rfl⟩ : syracuseStep 18318311 = 27477467) B27477467
theorem B2712649 : Blo 1607002 2712649 := bstep (se 2 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 2712649 = 2034487) B2034487
theorem B2712683 : Blo 1607002 2712683 := bstep (se 1 (by rfl) ⟨2034512, by rfl⟩ : syracuseStep 2712683 = 4069025) B4069025
theorem B3261647 : Blo 1607002 3261647 := bstep (se 1 (by rfl) ⟨2446235, by rfl⟩ : syracuseStep 3261647 = 4892471) B4892471
theorem B34784477 : Blo 1607002 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B37135739 : Blo 1607002 37135739 := bstep (se 1 (by rfl) ⟨27851804, by rfl⟩ : syracuseStep 37135739 = 55703609) B55703609
theorem B1607067 : Blo 1607002 1607067 := bstep (se 1 (by rfl) ⟨1205300, by rfl⟩ : syracuseStep 1607067 = 2410601) B2410601
theorem B22291955 : Blo 1607002 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B1607279 : Blo 1607002 1607279 := bstep (se 1 (by rfl) ⟨1205459, by rfl⟩ : syracuseStep 1607279 = 2410919) B2410919
theorem B6039161 : Blo 1607002 6039161 := bstep (se 2 (by rfl) ⟨2264685, by rfl⟩ : syracuseStep 6039161 = 4529371) B4529371
theorem B1607335 : Blo 1607002 1607335 := bstep (se 1 (by rfl) ⟨1205501, by rfl⟩ : syracuseStep 1607335 = 2411003) B2411003
theorem B1607419 : Blo 1607002 1607419 := bstep (se 1 (by rfl) ⟨1205564, by rfl⟩ : syracuseStep 1607419 = 2411129) B2411129
theorem B8693507 : Blo 1607002 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B4581127 : Blo 1607002 4581127 := bstep (se 1 (by rfl) ⟨3435845, by rfl⟩ : syracuseStep 4581127 = 6871691) B6871691
theorem B1607455 : Blo 1607002 1607455 := bstep (se 1 (by rfl) ⟨1205591, by rfl⟩ : syracuseStep 1607455 = 2411183) B2411183
theorem B12216095 : Blo 1607002 12216095 := bstep (se 1 (by rfl) ⟨9162071, by rfl⟩ : syracuseStep 12216095 = 18324143) B18324143
theorem B1607487 : Blo 1607002 1607487 := bstep (se 1 (by rfl) ⟨1205615, by rfl⟩ : syracuseStep 1607487 = 2411231) B2411231
theorem B8046443 : Blo 1607002 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B14665657 : Blo 1607002 14665657 := bstep (se 2 (by rfl) ⟨5499621, by rfl⟩ : syracuseStep 14665657 = 10999243) B10999243
theorem B1607663 : Blo 1607002 1607663 := bstep (se 1 (by rfl) ⟨1205747, by rfl⟩ : syracuseStep 1607663 = 2411495) B2411495
theorem B1607835 : Blo 1607002 1607835 := bstep (se 1 (by rfl) ⟨1205876, by rfl⟩ : syracuseStep 1607835 = 2411753) B2411753
theorem B12208319 : Blo 1607002 12208319 := bstep (se 1 (by rfl) ⟨9156239, by rfl⟩ : syracuseStep 12208319 = 18312479) B18312479
theorem B1607871 : Blo 1607002 1607871 := bstep (se 1 (by rfl) ⟨1205903, by rfl⟩ : syracuseStep 1607871 = 2411807) B2411807
theorem B2410793 : Blo 1607002 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B2410799 : Blo 1607002 2410799 := bstep (se 1 (by rfl) ⟨1808099, by rfl⟩ : syracuseStep 2410799 = 3616199) B3616199
theorem B1607983 : Blo 1607002 1607983 := bstep (se 1 (by rfl) ⟨1205987, by rfl⟩ : syracuseStep 1607983 = 2411975) B2411975
theorem B2713979 : Blo 1607002 2713979 := bstep (se 1 (by rfl) ⟨2035484, by rfl⟩ : syracuseStep 2713979 = 4070969) B4070969
theorem B9775525 : Blo 1607002 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B1608219 : Blo 1607002 1608219 := bstep (se 1 (by rfl) ⟨1206164, by rfl⟩ : syracuseStep 1608219 = 2412329) B2412329
theorem B2411039 : Blo 1607002 2411039 := bstep (se 1 (by rfl) ⟨1808279, by rfl⟩ : syracuseStep 2411039 = 3616559) B3616559
theorem B1608223 : Blo 1607002 1608223 := bstep (se 1 (by rfl) ⟨1206167, by rfl⟩ : syracuseStep 1608223 = 2412335) B2412335
theorem B2714249 : Blo 1607002 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B1608539 : Blo 1607002 1608539 := bstep (se 1 (by rfl) ⟨1206404, by rfl⟩ : syracuseStep 1608539 = 2412809) B2412809
theorem B2411423 : Blo 1607002 2411423 := bstep (se 1 (by rfl) ⟨1808567, by rfl⟩ : syracuseStep 2411423 = 3617135) B3617135
theorem B1608607 : Blo 1607002 1608607 := bstep (se 1 (by rfl) ⟨1206455, by rfl⟩ : syracuseStep 1608607 = 2412911) B2412911
theorem B2411471 : Blo 1607002 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B2411561 : Blo 1607002 2411561 := bstep (se 2 (by rfl) ⟨904335, by rfl⟩ : syracuseStep 2411561 = 1808671) B1808671
theorem B2411567 : Blo 1607002 2411567 := bstep (se 1 (by rfl) ⟨1808675, by rfl⟩ : syracuseStep 2411567 = 3617351) B3617351
theorem B1608751 : Blo 1607002 1608751 := bstep (se 1 (by rfl) ⟨1206563, by rfl⟩ : syracuseStep 1608751 = 2413127) B2413127
theorem B2411591 : Blo 1607002 2411591 := bstep (se 1 (by rfl) ⟨1808693, by rfl⟩ : syracuseStep 2411591 = 3617387) B3617387
theorem B1608775 : Blo 1607002 1608775 := bstep (se 1 (by rfl) ⟨1206581, by rfl⟩ : syracuseStep 1608775 = 2413163) B2413163
theorem B5426297 : Blo 1607002 5426297 := bstep (se 2 (by rfl) ⟨2034861, by rfl⟩ : syracuseStep 5426297 = 4069723) B4069723
theorem B3435743 : Blo 1607002 3435743 := bstep (se 1 (by rfl) ⟨2576807, by rfl⟩ : syracuseStep 3435743 = 5153615) B5153615
theorem B1608927 : Blo 1607002 1608927 := bstep (se 1 (by rfl) ⟨1206695, by rfl⟩ : syracuseStep 1608927 = 2413391) B2413391
theorem B23194957 : Blo 1607002 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B2411855 : Blo 1607002 2411855 := bstep (se 1 (by rfl) ⟨1808891, by rfl⟩ : syracuseStep 2411855 = 3617783) B3617783
theorem B2411945 : Blo 1607002 2411945 := bstep (se 2 (by rfl) ⟨904479, by rfl⟩ : syracuseStep 2411945 = 1808959) B1808959
theorem B5426621 : Blo 1607002 5426621 := bstep (se 3 (by rfl) ⟨1017491, by rfl⟩ : syracuseStep 5426621 = 2034983) B2034983
theorem B8138231 : Blo 1607002 8138231 := bstep (se 1 (by rfl) ⟨6103673, by rfl⟩ : syracuseStep 8138231 = 12207347) B12207347
theorem B9162233 : Blo 1607002 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B11595287 : Blo 1607002 11595287 := bstep (se 1 (by rfl) ⟨8696465, by rfl⟩ : syracuseStep 11595287 = 17392931) B17392931
theorem B2412095 : Blo 1607002 2412095 := bstep (se 1 (by rfl) ⟨1809071, by rfl⟩ : syracuseStep 2412095 = 3618143) B3618143
theorem B6106697 : Blo 1607002 6106697 := bstep (se 2 (by rfl) ⟨2290011, by rfl⟩ : syracuseStep 6106697 = 4580023) B4580023
theorem B5148335 : Blo 1607002 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B3051283 : Blo 1607002 3051283 := bstep (se 1 (by rfl) ⟨2288462, by rfl⟩ : syracuseStep 3051283 = 4576925) B4576925
theorem B2412359 : Blo 1607002 2412359 := bstep (se 1 (by rfl) ⟨1809269, by rfl⟩ : syracuseStep 2412359 = 3618539) B3618539
theorem B3616667 : Blo 1607002 3616667 := bstep (se 1 (by rfl) ⟨2712500, by rfl⟩ : syracuseStep 3616667 = 5425001) B5425001
theorem B2412443 : Blo 1607002 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B8695775 : Blo 1607002 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B5427323 : Blo 1607002 5427323 := bstep (se 1 (by rfl) ⟨4070492, by rfl⟩ : syracuseStep 5427323 = 8140985) B8140985
theorem B9285761 : Blo 1607002 9285761 := bstep (se 2 (by rfl) ⟨3482160, by rfl⟩ : syracuseStep 9285761 = 6964321) B6964321
theorem B3616955 : Blo 1607002 3616955 := bstep (se 1 (by rfl) ⟨2712716, by rfl⟩ : syracuseStep 3616955 = 5425433) B5425433
theorem B2576603 : Blo 1607002 2576603 := bstep (se 1 (by rfl) ⟨1932452, by rfl⟩ : syracuseStep 2576603 = 3864905) B3864905
theorem B5427485 : Blo 1607002 5427485 := bstep (se 3 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 5427485 = 2035307) B2035307
theorem B31412531 : Blo 1607002 31412531 := bstep (se 1 (by rfl) ⟨23559398, by rfl⟩ : syracuseStep 31412531 = 47118797) B47118797
theorem B13922647 : Blo 1607002 13922647 := bstep (se 1 (by rfl) ⟨10441985, by rfl⟩ : syracuseStep 13922647 = 20883971) B20883971
theorem B3051913 : Blo 1607002 3051913 := bstep (se 2 (by rfl) ⟨1144467, by rfl⟩ : syracuseStep 3051913 = 2288935) B2288935
theorem B5427593 : Blo 1607002 5427593 := bstep (se 2 (by rfl) ⟨2035347, by rfl⟩ : syracuseStep 5427593 = 4070695) B4070695
theorem B2413007 : Blo 1607002 2413007 := bstep (se 1 (by rfl) ⟨1809755, by rfl⟩ : syracuseStep 2413007 = 3619511) B3619511
theorem B2413049 : Blo 1607002 2413049 := bstep (se 2 (by rfl) ⟨904893, by rfl⟩ : syracuseStep 2413049 = 1809787) B1809787
theorem B2413151 : Blo 1607002 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B46346903 : Blo 1607002 46346903 := bstep (se 1 (by rfl) ⟨34760177, by rfl⟩ : syracuseStep 46346903 = 69520355) B69520355
theorem B3617441 : Blo 1607002 3617441 := bstep (se 2 (by rfl) ⟨1356540, by rfl⟩ : syracuseStep 3617441 = 2713081) B2713081
theorem B15446699 : Blo 1607002 15446699 := bstep (se 1 (by rfl) ⟨11585024, by rfl⟩ : syracuseStep 15446699 = 23170049) B23170049
theorem B10449623 : Blo 1607002 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B4887287 : Blo 1607002 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B11588345 : Blo 1607002 11588345 := bstep (se 2 (by rfl) ⟨4345629, by rfl⟩ : syracuseStep 11588345 = 8691259) B8691259
theorem B4068103 : Blo 1607002 4068103 := bstep (se 1 (by rfl) ⟨3051077, by rfl⟩ : syracuseStep 4068103 = 6102155) B6102155
theorem B8139527 : Blo 1607002 8139527 := bstep (se 1 (by rfl) ⟨6104645, by rfl⟩ : syracuseStep 8139527 = 12209291) B12209291
theorem B4707197 : Blo 1607002 4707197 := bstep (se 3 (by rfl) ⟨882599, by rfl⟩ : syracuseStep 4707197 = 1765199) B1765199
theorem B19346347 : Blo 1607002 19346347 := bstep (se 1 (by rfl) ⟨14509760, by rfl⟩ : syracuseStep 19346347 = 29019521) B29019521
theorem B3617801 : Blo 1607002 3617801 := bstep (se 2 (by rfl) ⟨1356675, by rfl⟩ : syracuseStep 3617801 = 2713351) B2713351
theorem B4068407 : Blo 1607002 4068407 := bstep (se 1 (by rfl) ⟨3051305, by rfl⟩ : syracuseStep 4068407 = 6102611) B6102611
theorem B3617855 : Blo 1607002 3617855 := bstep (se 1 (by rfl) ⟨2713391, by rfl⟩ : syracuseStep 3617855 = 5426783) B5426783
theorem B5428511 : Blo 1607002 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B10302875 : Blo 1607002 10302875 := bstep (se 1 (by rfl) ⟨7727156, by rfl⟩ : syracuseStep 10302875 = 15454313) B15454313
theorem B3863963 : Blo 1607002 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B8140499 : Blo 1607002 8140499 := bstep (se 1 (by rfl) ⟨6105374, by rfl⟩ : syracuseStep 8140499 = 12210749) B12210749
theorem B15447773 : Blo 1607002 15447773 := bstep (se 3 (by rfl) ⟨2896457, by rfl⟩ : syracuseStep 15447773 = 5792915) B5792915
theorem B37115783 : Blo 1607002 37115783 := bstep (se 1 (by rfl) ⟨27836837, by rfl⟩ : syracuseStep 37115783 = 55673675) B55673675
theorem B4577255 : Blo 1607002 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B3618791 : Blo 1607002 3618791 := bstep (se 1 (by rfl) ⟨2714093, by rfl⟩ : syracuseStep 3618791 = 5428187) B5428187
theorem B3618809 : Blo 1607002 3618809 := bstep (se 2 (by rfl) ⟨1357053, by rfl⟩ : syracuseStep 3618809 = 2714107) B2714107
theorem B3618899 : Blo 1607002 3618899 := bstep (se 1 (by rfl) ⟨2714174, by rfl⟩ : syracuseStep 3618899 = 5428349) B5428349
theorem B3618971 : Blo 1607002 3618971 := bstep (se 1 (by rfl) ⟨2714228, by rfl⟩ : syracuseStep 3618971 = 5428457) B5428457
theorem B3864809 : Blo 1607002 3864809 := bstep (se 2 (by rfl) ⟨1449303, by rfl⟩ : syracuseStep 3864809 = 2898607) B2898607
theorem B3619079 : Blo 1607002 3619079 := bstep (se 1 (by rfl) ⟨2714309, by rfl⟩ : syracuseStep 3619079 = 5428619) B5428619
theorem B13932809 : Blo 1607002 13932809 := bstep (se 2 (by rfl) ⟨5224803, by rfl⟩ : syracuseStep 13932809 = 10449607) B10449607
theorem B4069673 : Blo 1607002 4069673 := bstep (se 2 (by rfl) ⟨1526127, by rfl⟩ : syracuseStep 4069673 = 3052255) B3052255
theorem B2898217 : Blo 1607002 2898217 := bstep (se 2 (by rfl) ⟨1086831, by rfl⟩ : syracuseStep 2898217 = 2173663) B2173663
theorem B13736411 : Blo 1607002 13736411 := bstep (se 1 (by rfl) ⟨10302308, by rfl⟩ : syracuseStep 13736411 = 20604617) B20604617
theorem B1808923 : Blo 1607002 1808923 := bstep (se 1 (by rfl) ⟨1356692, by rfl⟩ : syracuseStep 1808923 = 2713385) B2713385
theorem B3619385 : Blo 1607002 3619385 := bstep (se 2 (by rfl) ⟨1357269, by rfl⟩ : syracuseStep 3619385 = 2714539) B2714539
theorem B98966123 : Blo 1607002 98966123 := bstep (se 1 (by rfl) ⟨74224592, by rfl⟩ : syracuseStep 98966123 = 148449185) B148449185
theorem B7731865 : Blo 1607002 7731865 := bstep (se 2 (by rfl) ⟨2899449, by rfl⟩ : syracuseStep 7731865 = 5798899) B5798899
theorem B3054419 : Blo 1607002 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B6101851 : Blo 1607002 6101851 := bstep (se 1 (by rfl) ⟨4576388, by rfl⟩ : syracuseStep 6101851 = 9152777) B9152777
theorem B4070351 : Blo 1607002 4070351 := bstep (se 1 (by rfl) ⟨3052763, by rfl⟩ : syracuseStep 4070351 = 6105527) B6105527
theorem B6872033 : Blo 1607002 6872033 := bstep (se 2 (by rfl) ⟨2577012, by rfl⟩ : syracuseStep 6872033 = 5154025) B5154025
theorem B3620105 : Blo 1607002 3620105 := bstep (se 2 (by rfl) ⟨1357539, by rfl⟩ : syracuseStep 3620105 = 2715079) B2715079
theorem B4578599 : Blo 1607002 4578599 := bstep (se 1 (by rfl) ⟨3433949, by rfl⟩ : syracuseStep 4578599 = 6867899) B6867899
theorem B8142119 : Blo 1607002 8142119 := bstep (se 1 (by rfl) ⟨6106589, by rfl⟩ : syracuseStep 8142119 = 12213179) B12213179
theorem B23174545 : Blo 1607002 23174545 := bstep (se 2 (by rfl) ⟨8690454, by rfl⟩ : syracuseStep 23174545 = 17380909) B17380909
theorem B12213665 : Blo 1607002 12213665 := bstep (se 2 (by rfl) ⟨4580124, by rfl⟩ : syracuseStep 12213665 = 9160249) B9160249
theorem B1809895 : Blo 1607002 1809895 := bstep (se 1 (by rfl) ⟨1357421, by rfl⟩ : syracuseStep 1809895 = 2714843) B2714843
theorem B2751995 : Blo 1607002 2751995 := bstep (se 1 (by rfl) ⟨2063996, by rfl⟩ : syracuseStep 2751995 = 4127993) B4127993
theorem B3260137 : Blo 1607002 3260137 := bstep (se 2 (by rfl) ⟨1222551, by rfl⟩ : syracuseStep 3260137 = 2445103) B2445103
theorem B12206375 : Blo 1607002 12206375 := bstep (se 1 (by rfl) ⟨9154781, by rfl⟩ : syracuseStep 12206375 = 18309563) B18309563
theorem B10297799 : Blo 1607002 10297799 := bstep (se 1 (by rfl) ⟨7723349, by rfl⟩ : syracuseStep 10297799 = 15446699) B15446699
theorem B7725563 : Blo 1607002 7725563 := bstep (se 1 (by rfl) ⟨5794172, by rfl⟩ : syracuseStep 7725563 = 11588345) B11588345
theorem B13034033 : Blo 1607002 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B3138131 : Blo 1607002 3138131 := bstep (se 1 (by rfl) ⟨2353598, by rfl⟩ : syracuseStep 3138131 = 4707197) B4707197
theorem B2712271 : Blo 1607002 2712271 := bstep (se 1 (by rfl) ⟨2034203, by rfl⟩ : syracuseStep 2712271 = 4068407) B4068407
theorem B25101053 : Blo 1607002 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B24757159 : Blo 1607002 24757159 := bstep (se 1 (by rfl) ⟨18567869, by rfl⟩ : syracuseStep 24757159 = 37135739) B37135739
theorem B14861303 : Blo 1607002 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B5424137 : Blo 1607002 5424137 := bstep (se 2 (by rfl) ⟨2034051, by rfl⟩ : syracuseStep 5424137 = 4068103) B4068103
theorem B8135801 : Blo 1607002 8135801 := bstep (se 2 (by rfl) ⟨3050925, by rfl⟩ : syracuseStep 8135801 = 6101851) B6101851
theorem B10298515 : Blo 1607002 10298515 := bstep (se 1 (by rfl) ⟨7723886, by rfl⟩ : syracuseStep 10298515 = 15447773) B15447773
theorem B8144063 : Blo 1607002 8144063 := bstep (se 1 (by rfl) ⟨6108047, by rfl⟩ : syracuseStep 8144063 = 12216095) B12216095
theorem B1607195 : Blo 1607002 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B2713115 : Blo 1607002 2713115 := bstep (se 1 (by rfl) ⟨2034836, by rfl⟩ : syracuseStep 2713115 = 4069673) B4069673
theorem B1607199 : Blo 1607002 1607199 := bstep (se 1 (by rfl) ⟨1205399, by rfl⟩ : syracuseStep 1607199 = 2410799) B2410799
theorem B1607359 : Blo 1607002 1607359 := bstep (se 1 (by rfl) ⟨1205519, by rfl⟩ : syracuseStep 1607359 = 2411039) B2411039
theorem B30926609 : Blo 1607002 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B1607615 : Blo 1607002 1607615 := bstep (se 1 (by rfl) ⟨1205711, by rfl⟩ : syracuseStep 1607615 = 2411423) B2411423
theorem B1607647 : Blo 1607002 1607647 := bstep (se 1 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 1607647 = 2411471) B2411471
theorem B2713567 : Blo 1607002 2713567 := bstep (se 1 (by rfl) ⟨2035175, by rfl⟩ : syracuseStep 2713567 = 4070351) B4070351
theorem B4581355 : Blo 1607002 4581355 := bstep (se 1 (by rfl) ⟨3436016, by rfl⟩ : syracuseStep 4581355 = 6872033) B6872033
theorem B1607707 : Blo 1607002 1607707 := bstep (se 1 (by rfl) ⟨1205780, by rfl⟩ : syracuseStep 1607707 = 2411561) B2411561
theorem B1607711 : Blo 1607002 1607711 := bstep (se 1 (by rfl) ⟨1205783, by rfl⟩ : syracuseStep 1607711 = 2411567) B2411567
theorem B1607727 : Blo 1607002 1607727 := bstep (se 1 (by rfl) ⟨1205795, by rfl⟩ : syracuseStep 1607727 = 2411591) B2411591
theorem B1607903 : Blo 1607002 1607903 := bstep (se 1 (by rfl) ⟨1205927, by rfl⟩ : syracuseStep 1607903 = 2411855) B2411855
theorem B103180517 : Blo 1607002 103180517 := bstep (se 4 (by rfl) ⟨9673173, by rfl⟩ : syracuseStep 103180517 = 19346347) B19346347
theorem B1607963 : Blo 1607002 1607963 := bstep (se 1 (by rfl) ⟨1205972, by rfl⟩ : syracuseStep 1607963 = 2411945) B2411945
theorem B21457181 : Blo 1607002 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B5425487 : Blo 1607002 5425487 := bstep (se 1 (by rfl) ⟨4069115, by rfl⟩ : syracuseStep 5425487 = 8138231) B8138231
theorem B1608063 : Blo 1607002 1608063 := bstep (se 1 (by rfl) ⟨1206047, by rfl⟩ : syracuseStep 1608063 = 2412095) B2412095
theorem B1608239 : Blo 1607002 1608239 := bstep (se 1 (by rfl) ⟨1206179, by rfl⟩ : syracuseStep 1608239 = 2412359) B2412359
theorem B2411111 : Blo 1607002 2411111 := bstep (se 1 (by rfl) ⟨1808333, by rfl⟩ : syracuseStep 2411111 = 3616667) B3616667
theorem B1608295 : Blo 1607002 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B2411303 : Blo 1607002 2411303 := bstep (se 1 (by rfl) ⟨1808477, by rfl⟩ : syracuseStep 2411303 = 3616955) B3616955
theorem B20941687 : Blo 1607002 20941687 := bstep (se 1 (by rfl) ⟨15706265, by rfl⟩ : syracuseStep 20941687 = 31412531) B31412531
theorem B1608671 : Blo 1607002 1608671 := bstep (se 1 (by rfl) ⟨1206503, by rfl⟩ : syracuseStep 1608671 = 2413007) B2413007
theorem B1608699 : Blo 1607002 1608699 := bstep (se 1 (by rfl) ⟨1206524, by rfl⟩ : syracuseStep 1608699 = 2413049) B2413049
theorem B3615785 : Blo 1607002 3615785 := bstep (se 2 (by rfl) ⟨1355919, by rfl⟩ : syracuseStep 3615785 = 2711839) B2711839
theorem B1608767 : Blo 1607002 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B2411627 : Blo 1607002 2411627 := bstep (se 1 (by rfl) ⟨1808720, by rfl⟩ : syracuseStep 2411627 = 3617441) B3617441
theorem B6966415 : Blo 1607002 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B5426351 : Blo 1607002 5426351 := bstep (se 1 (by rfl) ⟨4069763, by rfl⟩ : syracuseStep 5426351 = 8139527) B8139527
theorem B9161981 : Blo 1607002 9161981 := bstep (se 3 (by rfl) ⟨1717871, by rfl⟩ : syracuseStep 9161981 = 3435743) B3435743
theorem B3616019 : Blo 1607002 3616019 := bstep (se 1 (by rfl) ⟨2712014, by rfl⟩ : syracuseStep 3616019 = 5424029) B5424029
theorem B3616055 : Blo 1607002 3616055 := bstep (se 1 (by rfl) ⟨2712041, by rfl⟩ : syracuseStep 3616055 = 5424083) B5424083
theorem B2411867 : Blo 1607002 2411867 := bstep (se 1 (by rfl) ⟨1808900, by rfl⟩ : syracuseStep 2411867 = 3617801) B3617801
theorem B2411897 : Blo 1607002 2411897 := bstep (se 2 (by rfl) ⟨904461, by rfl⟩ : syracuseStep 2411897 = 1808923) B1808923
theorem B2411903 : Blo 1607002 2411903 := bstep (se 1 (by rfl) ⟨1808927, by rfl⟩ : syracuseStep 2411903 = 3617855) B3617855
theorem B2174431 : Blo 1607002 2174431 := bstep (se 1 (by rfl) ⟨1630823, by rfl⟩ : syracuseStep 2174431 = 3261647) B3261647
theorem B10309153 : Blo 1607002 10309153 := bstep (se 2 (by rfl) ⟨3865932, by rfl⟩ : syracuseStep 10309153 = 7731865) B7731865
theorem B6868583 : Blo 1607002 6868583 := bstep (se 1 (by rfl) ⟨5151437, by rfl⟩ : syracuseStep 6868583 = 10302875) B10302875
theorem B2575975 : Blo 1607002 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B4026107 : Blo 1607002 4026107 := bstep (se 1 (by rfl) ⟨3019580, by rfl⟩ : syracuseStep 4026107 = 6039161) B6039161
theorem B5426999 : Blo 1607002 5426999 := bstep (se 1 (by rfl) ⟨4070249, by rfl⟩ : syracuseStep 5426999 = 8140499) B8140499
theorem B5795671 : Blo 1607002 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B6106985 : Blo 1607002 6106985 := bstep (se 2 (by rfl) ⟨2290119, by rfl⟩ : syracuseStep 6106985 = 4580239) B4580239
theorem B3616649 : Blo 1607002 3616649 := bstep (se 2 (by rfl) ⟨1356243, by rfl⟩ : syracuseStep 3616649 = 2712487) B2712487
theorem B24743855 : Blo 1607002 24743855 := bstep (se 1 (by rfl) ⟨18557891, by rfl⟩ : syracuseStep 24743855 = 37115783) B37115783
theorem B3051503 : Blo 1607002 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B2412527 : Blo 1607002 2412527 := bstep (se 1 (by rfl) ⟨1809395, by rfl⟩ : syracuseStep 2412527 = 3618791) B3618791
theorem B2412539 : Blo 1607002 2412539 := bstep (se 1 (by rfl) ⟨1809404, by rfl⟩ : syracuseStep 2412539 = 3618809) B3618809
theorem B2412599 : Blo 1607002 2412599 := bstep (se 1 (by rfl) ⟨1809449, by rfl⟩ : syracuseStep 2412599 = 3618899) B3618899
theorem B3616865 : Blo 1607002 3616865 := bstep (se 2 (by rfl) ⟨1356324, by rfl⟩ : syracuseStep 3616865 = 2712649) B2712649
theorem B2412647 : Blo 1607002 2412647 := bstep (se 1 (by rfl) ⟨1809485, by rfl⟩ : syracuseStep 2412647 = 3618971) B3618971
theorem B8138879 : Blo 1607002 8138879 := bstep (se 1 (by rfl) ⟨6104159, by rfl⟩ : syracuseStep 8138879 = 12208319) B12208319
theorem B2576539 : Blo 1607002 2576539 := bstep (se 1 (by rfl) ⟨1932404, by rfl⟩ : syracuseStep 2576539 = 3864809) B3864809
theorem B2412719 : Blo 1607002 2412719 := bstep (se 1 (by rfl) ⟨1809539, by rfl⟩ : syracuseStep 2412719 = 3619079) B3619079
theorem B2412923 : Blo 1607002 2412923 := bstep (se 1 (by rfl) ⟨1809692, by rfl⟩ : syracuseStep 2412923 = 3619385) B3619385
theorem B2036279 : Blo 1607002 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B2413193 : Blo 1607002 2413193 := bstep (se 2 (by rfl) ⟨904947, by rfl⟩ : syracuseStep 2413193 = 1809895) B1809895
theorem B3617531 : Blo 1607002 3617531 := bstep (se 1 (by rfl) ⟨2713148, by rfl⟩ : syracuseStep 3617531 = 5426297) B5426297
theorem B2413403 : Blo 1607002 2413403 := bstep (se 1 (by rfl) ⟨1810052, by rfl⟩ : syracuseStep 2413403 = 3620105) B3620105
theorem B3052399 : Blo 1607002 3052399 := bstep (se 1 (by rfl) ⟨2289299, by rfl⟩ : syracuseStep 3052399 = 4578599) B4578599
theorem B5428079 : Blo 1607002 5428079 := bstep (se 1 (by rfl) ⟨4071059, by rfl⟩ : syracuseStep 5428079 = 8142119) B8142119
theorem B3617747 : Blo 1607002 3617747 := bstep (se 1 (by rfl) ⟨2713310, by rfl⟩ : syracuseStep 3617747 = 5426621) B5426621
theorem B4346849 : Blo 1607002 4346849 := bstep (se 2 (by rfl) ⟨1630068, by rfl⟩ : syracuseStep 4346849 = 3260137) B3260137
theorem B6108155 : Blo 1607002 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B6108169 : Blo 1607002 6108169 := bstep (se 2 (by rfl) ⟨2290563, by rfl⟩ : syracuseStep 6108169 = 4581127) B4581127
theorem B7730191 : Blo 1607002 7730191 := bstep (se 1 (by rfl) ⟨5797643, by rfl⟩ : syracuseStep 7730191 = 11595287) B11595287
theorem B4068377 : Blo 1607002 4068377 := bstep (se 2 (by rfl) ⟨1525641, by rfl⟩ : syracuseStep 4068377 = 3051283) B3051283
theorem B5797183 : Blo 1607002 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B3618215 : Blo 1607002 3618215 := bstep (se 1 (by rfl) ⟨2713661, by rfl⟩ : syracuseStep 3618215 = 5427323) B5427323
theorem B6190507 : Blo 1607002 6190507 := bstep (se 1 (by rfl) ⟨4642880, by rfl⟩ : syracuseStep 6190507 = 9285761) B9285761
theorem B1717735 : Blo 1607002 1717735 := bstep (se 1 (by rfl) ⟨1288301, by rfl⟩ : syracuseStep 1717735 = 2576603) B2576603
theorem B3618323 : Blo 1607002 3618323 := bstep (se 1 (by rfl) ⟨2713742, by rfl⟩ : syracuseStep 3618323 = 5427485) B5427485
theorem B3618395 : Blo 1607002 3618395 := bstep (se 1 (by rfl) ⟨2713796, by rfl⟩ : syracuseStep 3618395 = 5427593) B5427593
theorem B3864289 : Blo 1607002 3864289 := bstep (se 2 (by rfl) ⟨1449108, by rfl⟩ : syracuseStep 3864289 = 2898217) B2898217
theorem B30897935 : Blo 1607002 30897935 := bstep (se 1 (by rfl) ⟨23173451, by rfl⟩ : syracuseStep 30897935 = 46346903) B46346903
theorem B13735727 : Blo 1607002 13735727 := bstep (se 1 (by rfl) ⟨10301795, by rfl⟩ : syracuseStep 13735727 = 20603591) B20603591
theorem B3258191 : Blo 1607002 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B4069217 : Blo 1607002 4069217 := bstep (se 2 (by rfl) ⟨1525956, by rfl⟩ : syracuseStep 4069217 = 3051913) B3051913
theorem B12212207 : Blo 1607002 12212207 := bstep (se 1 (by rfl) ⟨9159155, by rfl⟩ : syracuseStep 12212207 = 18318311) B18318311
theorem B1808455 : Blo 1607002 1808455 := bstep (se 1 (by rfl) ⟨1356341, by rfl⟩ : syracuseStep 1808455 = 2712683) B2712683
theorem B23189651 : Blo 1607002 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B3619007 : Blo 1607002 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B9288539 : Blo 1607002 9288539 := bstep (se 1 (by rfl) ⟨6966404, by rfl⟩ : syracuseStep 9288539 = 13932809) B13932809
theorem B1809319 : Blo 1607002 1809319 := bstep (se 1 (by rfl) ⟨1356989, by rfl⟩ : syracuseStep 1809319 = 2713979) B2713979
theorem B9157607 : Blo 1607002 9157607 := bstep (se 1 (by rfl) ⟨6868205, by rfl⟩ : syracuseStep 9157607 = 13736411) B13736411
theorem B65977415 : Blo 1607002 65977415 := bstep (se 1 (by rfl) ⟨49483061, by rfl⟩ : syracuseStep 65977415 = 98966123) B98966123
theorem B1809499 : Blo 1607002 1809499 := bstep (se 1 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 1809499 = 2714249) B2714249
theorem B297016469 : Blo 1607002 297016469 := bstep (se 6 (by rfl) ⟨6961323, by rfl⟩ : syracuseStep 297016469 = 13922647) B13922647
theorem B30899393 : Blo 1607002 30899393 := bstep (se 2 (by rfl) ⟨11587272, by rfl⟩ : syracuseStep 30899393 = 23174545) B23174545
theorem B8142443 : Blo 1607002 8142443 := bstep (se 1 (by rfl) ⟨6106832, by rfl⟩ : syracuseStep 8142443 = 12213665) B12213665
theorem B1834663 : Blo 1607002 1834663 := bstep (se 1 (by rfl) ⟨1375997, by rfl⟩ : syracuseStep 1834663 = 2751995) B2751995
theorem B4071131 : Blo 1607002 4071131 := bstep (se 1 (by rfl) ⟨3053348, by rfl⟩ : syracuseStep 4071131 = 6106697) B6106697
theorem B3432223 : Blo 1607002 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B19554209 : Blo 1607002 19554209 := bstep (se 2 (by rfl) ⟨7332828, by rfl⟩ : syracuseStep 19554209 = 14665657) B14665657
theorem B6865199 : Blo 1607002 6865199 := bstep (se 1 (by rfl) ⟨5148899, by rfl⟩ : syracuseStep 6865199 = 10297799) B10297799
theorem B4072103 : Blo 1607002 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B2712251 : Blo 1607002 2712251 := bstep (se 1 (by rfl) ⟨2034188, by rfl⟩ : syracuseStep 2712251 = 4068377) B4068377
theorem B5423867 : Blo 1607002 5423867 := bstep (se 1 (by rfl) ⟨4067900, by rfl⟩ : syracuseStep 5423867 = 8135801) B8135801
theorem B2172127 : Blo 1607002 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B2712811 : Blo 1607002 2712811 := bstep (se 1 (by rfl) ⟨2034608, by rfl⟩ : syracuseStep 2712811 = 4069217) B4069217
theorem B8144225 : Blo 1607002 8144225 := bstep (se 2 (by rfl) ⟨3054084, by rfl⟩ : syracuseStep 8144225 = 6108169) B6108169
theorem B10306921 : Blo 1607002 10306921 := bstep (se 2 (by rfl) ⟨3865095, by rfl⟩ : syracuseStep 10306921 = 7730191) B7730191
theorem B15459767 : Blo 1607002 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B13731353 : Blo 1607002 13731353 := bstep (se 2 (by rfl) ⟨5149257, by rfl⟩ : syracuseStep 13731353 = 10298515) B10298515
theorem B1607407 : Blo 1607002 1607407 := bstep (se 1 (by rfl) ⟨1205555, by rfl⟩ : syracuseStep 1607407 = 2411111) B2411111
theorem B1607535 : Blo 1607002 1607535 := bstep (se 1 (by rfl) ⟨1205651, by rfl⟩ : syracuseStep 1607535 = 2411303) B2411303
theorem B6105071 : Blo 1607002 6105071 := bstep (se 1 (by rfl) ⟨4578803, by rfl⟩ : syracuseStep 6105071 = 9157607) B9157607
theorem B2410523 : Blo 1607002 2410523 := bstep (se 1 (by rfl) ⟨1807892, by rfl⟩ : syracuseStep 2410523 = 3615785) B3615785
theorem B43984943 : Blo 1607002 43984943 := bstep (se 1 (by rfl) ⟨32988707, by rfl⟩ : syracuseStep 43984943 = 65977415) B65977415
theorem B1607751 : Blo 1607002 1607751 := bstep (se 1 (by rfl) ⟨1205813, by rfl⟩ : syracuseStep 1607751 = 2411627) B2411627
theorem B198010979 : Blo 1607002 198010979 := bstep (se 1 (by rfl) ⟨148508234, by rfl⟩ : syracuseStep 198010979 = 297016469) B297016469
theorem B3434633 : Blo 1607002 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B2410679 : Blo 1607002 2410679 := bstep (se 1 (by rfl) ⟨1808009, by rfl⟩ : syracuseStep 2410679 = 3616019) B3616019
theorem B2410703 : Blo 1607002 2410703 := bstep (se 1 (by rfl) ⟨1808027, by rfl⟩ : syracuseStep 2410703 = 3616055) B3616055
theorem B1607911 : Blo 1607002 1607911 := bstep (se 1 (by rfl) ⟨1205933, by rfl⟩ : syracuseStep 1607911 = 2411867) B2411867
theorem B1607931 : Blo 1607002 1607931 := bstep (se 1 (by rfl) ⟨1205948, by rfl⟩ : syracuseStep 1607931 = 2411897) B2411897
theorem B1607935 : Blo 1607002 1607935 := bstep (se 1 (by rfl) ⟨1205951, by rfl⟩ : syracuseStep 1607935 = 2411903) B2411903
theorem B7727561 : Blo 1607002 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B2714087 : Blo 1607002 2714087 := bstep (se 1 (by rfl) ⟨2035565, by rfl⟩ : syracuseStep 2714087 = 4071131) B4071131
theorem B2411099 : Blo 1607002 2411099 := bstep (se 1 (by rfl) ⟨1808324, by rfl⟩ : syracuseStep 2411099 = 3616649) B3616649
theorem B13036139 : Blo 1607002 13036139 := bstep (se 1 (by rfl) ⟨9777104, by rfl⟩ : syracuseStep 13036139 = 19554209) B19554209
theorem B2034335 : Blo 1607002 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B1608351 : Blo 1607002 1608351 := bstep (se 1 (by rfl) ⟨1206263, by rfl⟩ : syracuseStep 1608351 = 2412527) B2412527
theorem B1608359 : Blo 1607002 1608359 := bstep (se 1 (by rfl) ⟨1206269, by rfl⟩ : syracuseStep 1608359 = 2412539) B2412539
theorem B1608399 : Blo 1607002 1608399 := bstep (se 1 (by rfl) ⟨1206299, by rfl⟩ : syracuseStep 1608399 = 2412599) B2412599
theorem B2411243 : Blo 1607002 2411243 := bstep (se 1 (by rfl) ⟨1808432, by rfl⟩ : syracuseStep 2411243 = 3616865) B3616865
theorem B1608431 : Blo 1607002 1608431 := bstep (se 1 (by rfl) ⟨1206323, by rfl⟩ : syracuseStep 1608431 = 2412647) B2412647
theorem B5425919 : Blo 1607002 5425919 := bstep (se 1 (by rfl) ⟨4069439, by rfl⟩ : syracuseStep 5425919 = 8138879) B8138879
theorem B2411273 : Blo 1607002 2411273 := bstep (se 2 (by rfl) ⟨904227, by rfl⟩ : syracuseStep 2411273 = 1808455) B1808455
theorem B1608479 : Blo 1607002 1608479 := bstep (se 1 (by rfl) ⟨1206359, by rfl⟩ : syracuseStep 1608479 = 2412719) B2412719
theorem B8137583 : Blo 1607002 8137583 := bstep (se 1 (by rfl) ⟨6103187, by rfl⟩ : syracuseStep 8137583 = 12206375) B12206375
theorem B3435385 : Blo 1607002 3435385 := bstep (se 2 (by rfl) ⟨1288269, by rfl⟩ : syracuseStep 3435385 = 2576539) B2576539
theorem B1608615 : Blo 1607002 1608615 := bstep (se 1 (by rfl) ⟨1206461, by rfl⟩ : syracuseStep 1608615 = 2412923) B2412923
theorem B2092087 : Blo 1607002 2092087 := bstep (se 1 (by rfl) ⟨1569065, by rfl⟩ : syracuseStep 2092087 = 3138131) B3138131
theorem B1608795 : Blo 1607002 1608795 := bstep (se 1 (by rfl) ⟨1206596, by rfl⟩ : syracuseStep 1608795 = 2413193) B2413193
theorem B2411687 : Blo 1607002 2411687 := bstep (se 1 (by rfl) ⟨1808765, by rfl⟩ : syracuseStep 2411687 = 3617531) B3617531
theorem B1608935 : Blo 1607002 1608935 := bstep (se 1 (by rfl) ⟨1206701, by rfl⟩ : syracuseStep 1608935 = 2413403) B2413403
theorem B2411831 : Blo 1607002 2411831 := bstep (se 1 (by rfl) ⟨1808873, by rfl⟩ : syracuseStep 2411831 = 3617747) B3617747
theorem B9907535 : Blo 1607002 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B3616091 : Blo 1607002 3616091 := bstep (se 1 (by rfl) ⟨2712068, by rfl⟩ : syracuseStep 3616091 = 5424137) B5424137
theorem B37154213 : Blo 1607002 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B3616361 : Blo 1607002 3616361 := bstep (se 2 (by rfl) ⟨1356135, by rfl⟩ : syracuseStep 3616361 = 2712271) B2712271
theorem B2412143 : Blo 1607002 2412143 := bstep (se 1 (by rfl) ⟨1809107, by rfl⟩ : syracuseStep 2412143 = 3618215) B3618215
theorem B2412215 : Blo 1607002 2412215 := bstep (se 1 (by rfl) ⟨1809161, by rfl⟩ : syracuseStep 2412215 = 3618323) B3618323
theorem B2412263 : Blo 1607002 2412263 := bstep (se 1 (by rfl) ⟨1809197, by rfl⟩ : syracuseStep 2412263 = 3618395) B3618395
theorem B27922249 : Blo 1607002 27922249 := bstep (se 2 (by rfl) ⟨10470843, by rfl⟩ : syracuseStep 27922249 = 20941687) B20941687
theorem B20598623 : Blo 1607002 20598623 := bstep (se 1 (by rfl) ⟨15448967, by rfl⟩ : syracuseStep 20598623 = 30897935) B30897935
theorem B33009545 : Blo 1607002 33009545 := bstep (se 2 (by rfl) ⟨12378579, by rfl⟩ : syracuseStep 33009545 = 24757159) B24757159
theorem B2412425 : Blo 1607002 2412425 := bstep (se 2 (by rfl) ⟨904659, by rfl⟩ : syracuseStep 2412425 = 1809319) B1809319
theorem B2412665 : Blo 1607002 2412665 := bstep (se 2 (by rfl) ⟨904749, by rfl⟩ : syracuseStep 2412665 = 1809499) B1809499
theorem B2412671 : Blo 1607002 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B18305189 : Blo 1607002 18305189 := bstep (se 4 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 18305189 = 3432223) B3432223
theorem B3616991 : Blo 1607002 3616991 := bstep (se 1 (by rfl) ⟨2712743, by rfl⟩ : syracuseStep 3616991 = 5425487) B5425487
theorem B7729577 : Blo 1607002 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B8254009 : Blo 1607002 8254009 := bstep (se 2 (by rfl) ⟨3095253, by rfl⟩ : syracuseStep 8254009 = 6190507) B6190507
theorem B2290313 : Blo 1607002 2290313 := bstep (se 2 (by rfl) ⟨858867, by rfl⟩ : syracuseStep 2290313 = 1717735) B1717735
theorem B3617567 : Blo 1607002 3617567 := bstep (se 1 (by rfl) ⟨2713175, by rfl⟩ : syracuseStep 3617567 = 5426351) B5426351
theorem B20599595 : Blo 1607002 20599595 := bstep (se 1 (by rfl) ⟨15449696, by rfl⟩ : syracuseStep 20599595 = 30899393) B30899393
theorem B6107987 : Blo 1607002 6107987 := bstep (se 1 (by rfl) ⟨4580990, by rfl⟩ : syracuseStep 6107987 = 9161981) B9161981
theorem B2446217 : Blo 1607002 2446217 := bstep (se 2 (by rfl) ⟨917331, by rfl⟩ : syracuseStep 2446217 = 1834663) B1834663
theorem B5428295 : Blo 1607002 5428295 := bstep (se 1 (by rfl) ⟨4071221, by rfl⟩ : syracuseStep 5428295 = 8142443) B8142443
theorem B2684071 : Blo 1607002 2684071 := bstep (se 1 (by rfl) ⟨2013053, by rfl⟩ : syracuseStep 2684071 = 4026107) B4026107
theorem B3617999 : Blo 1607002 3617999 := bstep (se 1 (by rfl) ⟨2713499, by rfl⟩ : syracuseStep 3617999 = 5426999) B5426999
theorem B16495903 : Blo 1607002 16495903 := bstep (se 1 (by rfl) ⟨12371927, by rfl⟩ : syracuseStep 16495903 = 24743855) B24743855
theorem B3618089 : Blo 1607002 3618089 := bstep (se 2 (by rfl) ⟨1356783, by rfl⟩ : syracuseStep 3618089 = 2713567) B2713567
theorem B6108473 : Blo 1607002 6108473 := bstep (se 2 (by rfl) ⟨2290677, by rfl⟩ : syracuseStep 6108473 = 4581355) B4581355
theorem B5150375 : Blo 1607002 5150375 := bstep (se 1 (by rfl) ⟨3862781, by rfl⟩ : syracuseStep 5150375 = 7725563) B7725563
theorem B8689355 : Blo 1607002 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B16734035 : Blo 1607002 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B3618719 : Blo 1607002 3618719 := bstep (se 1 (by rfl) ⟨2714039, by rfl⟩ : syracuseStep 3618719 = 5428079) B5428079
theorem B2897899 : Blo 1607002 2897899 := bstep (se 1 (by rfl) ⟨2173424, by rfl⟩ : syracuseStep 2897899 = 4346849) B4346849
theorem B57219149 : Blo 1607002 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B5429375 : Blo 1607002 5429375 := bstep (se 1 (by rfl) ⟨4072031, by rfl⟩ : syracuseStep 5429375 = 8144063) B8144063
theorem B1808743 : Blo 1607002 1808743 := bstep (se 1 (by rfl) ⟨1356557, by rfl⟩ : syracuseStep 1808743 = 2713115) B2713115
theorem B4069865 : Blo 1607002 4069865 := bstep (se 2 (by rfl) ⟨1526199, by rfl⟩ : syracuseStep 4069865 = 3052399) B3052399
theorem B20617739 : Blo 1607002 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B9157151 : Blo 1607002 9157151 := bstep (se 1 (by rfl) ⟨6867863, by rfl⟩ : syracuseStep 9157151 = 13735727) B13735727
theorem B8141471 : Blo 1607002 8141471 := bstep (se 1 (by rfl) ⟨6106103, by rfl⟩ : syracuseStep 8141471 = 12212207) B12212207
theorem B5430077 : Blo 1607002 5430077 := bstep (se 3 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 5430077 = 2036279) B2036279
theorem B68787011 : Blo 1607002 68787011 := bstep (se 1 (by rfl) ⟨51590258, by rfl⟩ : syracuseStep 68787011 = 103180517) B103180517
theorem B6192359 : Blo 1607002 6192359 := bstep (se 1 (by rfl) ⟨4644269, by rfl⟩ : syracuseStep 6192359 = 9288539) B9288539
theorem B2899241 : Blo 1607002 2899241 := bstep (se 2 (by rfl) ⟨1087215, by rfl⟩ : syracuseStep 2899241 = 2174431) B2174431
theorem B13745537 : Blo 1607002 13745537 := bstep (se 2 (by rfl) ⟨5154576, by rfl⟩ : syracuseStep 13745537 = 10309153) B10309153
theorem B5152385 : Blo 1607002 5152385 := bstep (se 2 (by rfl) ⟨1932144, by rfl⟩ : syracuseStep 5152385 = 3864289) B3864289
theorem B4579055 : Blo 1607002 4579055 := bstep (se 1 (by rfl) ⟨3434291, by rfl⟩ : syracuseStep 4579055 = 6868583) B6868583
theorem B4071323 : Blo 1607002 4071323 := bstep (se 1 (by rfl) ⟨3053492, by rfl⟩ : syracuseStep 4071323 = 6106985) B6106985
theorem B152584397 : Blo 1607002 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B5153051 : Blo 1607002 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B4071991 : Blo 1607002 4071991 := bstep (se 1 (by rfl) ⟨3053993, by rfl⟩ : syracuseStep 4071991 = 6107987) B6107987
theorem B1630811 : Blo 1607002 1630811 := bstep (se 1 (by rfl) ⟨1223108, by rfl⟩ : syracuseStep 1630811 = 2446217) B2446217
theorem B4072315 : Blo 1607002 4072315 := bstep (se 1 (by rfl) ⟨3054236, by rfl⟩ : syracuseStep 4072315 = 6108473) B6108473
theorem B26420093 : Blo 1607002 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B10306511 : Blo 1607002 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B3433583 : Blo 1607002 3433583 := bstep (se 1 (by rfl) ⟨2575187, by rfl⟩ : syracuseStep 3433583 = 5150375) B5150375
theorem B5792903 : Blo 1607002 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B4580513 : Blo 1607002 4580513 := bstep (se 2 (by rfl) ⟨1717692, by rfl⟩ : syracuseStep 4580513 = 3435385) B3435385
theorem B1607015 : Blo 1607002 1607015 := bstep (se 1 (by rfl) ⟨1205261, by rfl⟩ : syracuseStep 1607015 = 2410523) B2410523
theorem B132007319 : Blo 1607002 132007319 := bstep (se 1 (by rfl) ⟨99005489, by rfl⟩ : syracuseStep 132007319 = 198010979) B198010979
theorem B1607119 : Blo 1607002 1607119 := bstep (se 1 (by rfl) ⟨1205339, by rfl⟩ : syracuseStep 1607119 = 2410679) B2410679
theorem B1607135 : Blo 1607002 1607135 := bstep (se 1 (by rfl) ⟨1205351, by rfl⟩ : syracuseStep 1607135 = 2410703) B2410703
theorem B2713243 : Blo 1607002 2713243 := bstep (se 1 (by rfl) ⟨2034932, by rfl⟩ : syracuseStep 2713243 = 4069865) B4069865
theorem B6104767 : Blo 1607002 6104767 := bstep (se 1 (by rfl) ⟨4578575, by rfl⟩ : syracuseStep 6104767 = 9157151) B9157151
theorem B1607399 : Blo 1607002 1607399 := bstep (se 1 (by rfl) ⟨1205549, by rfl⟩ : syracuseStep 1607399 = 2411099) B2411099
theorem B5424893 : Blo 1607002 5424893 := bstep (se 3 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 5424893 = 2034335) B2034335
theorem B1607495 : Blo 1607002 1607495 := bstep (se 1 (by rfl) ⟨1205621, by rfl⟩ : syracuseStep 1607495 = 2411243) B2411243
theorem B1607515 : Blo 1607002 1607515 := bstep (se 1 (by rfl) ⟨1205636, by rfl⟩ : syracuseStep 1607515 = 2411273) B2411273
theorem B5425055 : Blo 1607002 5425055 := bstep (se 1 (by rfl) ⟨4068791, by rfl⟩ : syracuseStep 5425055 = 8137583) B8137583
theorem B1607791 : Blo 1607002 1607791 := bstep (se 1 (by rfl) ⟨1205843, by rfl⟩ : syracuseStep 1607791 = 2411687) B2411687
theorem B1607887 : Blo 1607002 1607887 := bstep (se 1 (by rfl) ⟨1205915, by rfl⟩ : syracuseStep 1607887 = 2411831) B2411831
theorem B2410727 : Blo 1607002 2410727 := bstep (se 1 (by rfl) ⟨1808045, by rfl⟩ : syracuseStep 2410727 = 3616091) B3616091
theorem B88025453 : Blo 1607002 88025453 := bstep (se 3 (by rfl) ⟨16504772, by rfl⟩ : syracuseStep 88025453 = 33009545) B33009545
theorem B2410907 : Blo 1607002 2410907 := bstep (se 1 (by rfl) ⟨1808180, by rfl⟩ : syracuseStep 2410907 = 3616361) B3616361
theorem B1608095 : Blo 1607002 1608095 := bstep (se 1 (by rfl) ⟨1206071, by rfl⟩ : syracuseStep 1608095 = 2412143) B2412143
theorem B3434923 : Blo 1607002 3434923 := bstep (se 1 (by rfl) ⟨2576192, by rfl⟩ : syracuseStep 3434923 = 5152385) B5152385
theorem B1608143 : Blo 1607002 1608143 := bstep (se 1 (by rfl) ⟨1206107, by rfl⟩ : syracuseStep 1608143 = 2412215) B2412215
theorem B1608175 : Blo 1607002 1608175 := bstep (se 1 (by rfl) ⟨1206131, by rfl⟩ : syracuseStep 1608175 = 2412263) B2412263
theorem B13732415 : Blo 1607002 13732415 := bstep (se 1 (by rfl) ⟨10299311, by rfl⟩ : syracuseStep 13732415 = 20598623) B20598623
theorem B1608283 : Blo 1607002 1608283 := bstep (se 1 (by rfl) ⟨1206212, by rfl⟩ : syracuseStep 1608283 = 2412425) B2412425
theorem B2714215 : Blo 1607002 2714215 := bstep (se 1 (by rfl) ⟨2035661, by rfl⟩ : syracuseStep 2714215 = 4071323) B4071323
theorem B1608443 : Blo 1607002 1608443 := bstep (se 1 (by rfl) ⟨1206332, by rfl⟩ : syracuseStep 1608443 = 2412665) B2412665
theorem B1608447 : Blo 1607002 1608447 := bstep (se 1 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 1608447 = 2412671) B2412671
theorem B2411327 : Blo 1607002 2411327 := bstep (se 1 (by rfl) ⟨1808495, by rfl⟩ : syracuseStep 2411327 = 3616991) B3616991
theorem B2714735 : Blo 1607002 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B2411657 : Blo 1607002 2411657 := bstep (se 2 (by rfl) ⟨904371, by rfl⟩ : syracuseStep 2411657 = 1808743) B1808743
theorem B3615911 : Blo 1607002 3615911 := bstep (se 1 (by rfl) ⟨2711933, by rfl⟩ : syracuseStep 3615911 = 5423867) B5423867
theorem B2411711 : Blo 1607002 2411711 := bstep (se 1 (by rfl) ⟨1808783, by rfl⟩ : syracuseStep 2411711 = 3617567) B3617567
theorem B13733063 : Blo 1607002 13733063 := bstep (se 1 (by rfl) ⟨10299797, by rfl⟩ : syracuseStep 13733063 = 20599595) B20599595
theorem B11005345 : Blo 1607002 11005345 := bstep (se 2 (by rfl) ⟨4127004, by rfl⟩ : syracuseStep 11005345 = 8254009) B8254009
theorem B2411999 : Blo 1607002 2411999 := bstep (se 1 (by rfl) ⟨1808999, by rfl⟩ : syracuseStep 2411999 = 3617999) B3617999
theorem B2412059 : Blo 1607002 2412059 := bstep (se 1 (by rfl) ⟨1809044, by rfl⟩ : syracuseStep 2412059 = 3618089) B3618089
theorem B9154235 : Blo 1607002 9154235 := bstep (se 1 (by rfl) ⟨6865676, by rfl⟩ : syracuseStep 9154235 = 13731353) B13731353
theorem B2412479 : Blo 1607002 2412479 := bstep (se 1 (by rfl) ⟨1809359, by rfl⟩ : syracuseStep 2412479 = 3618719) B3618719
theorem B29323295 : Blo 1607002 29323295 := bstep (se 1 (by rfl) ⟨21992471, by rfl⟩ : syracuseStep 29323295 = 43984943) B43984943
theorem B2789449 : Blo 1607002 2789449 := bstep (se 2 (by rfl) ⟨1046043, by rfl⟩ : syracuseStep 2789449 = 2092087) B2092087
theorem B2289755 : Blo 1607002 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B2896169 : Blo 1607002 2896169 := bstep (se 2 (by rfl) ⟨1086063, by rfl⟩ : syracuseStep 2896169 = 2172127) B2172127
theorem B3617081 : Blo 1607002 3617081 := bstep (se 2 (by rfl) ⟨1356405, by rfl⟩ : syracuseStep 3617081 = 2712811) B2712811
theorem B6107501 : Blo 1607002 6107501 := bstep (se 3 (by rfl) ⟨1145156, by rfl⟩ : syracuseStep 6107501 = 2290313) B2290313
theorem B5427647 : Blo 1607002 5427647 := bstep (se 1 (by rfl) ⟨4070735, by rfl⟩ : syracuseStep 5427647 = 8141471) B8141471
theorem B13742561 : Blo 1607002 13742561 := bstep (se 2 (by rfl) ⟨5153460, by rfl⟩ : syracuseStep 13742561 = 10306921) B10306921
theorem B3617279 : Blo 1607002 3617279 := bstep (se 1 (by rfl) ⟨2712959, by rfl⟩ : syracuseStep 3617279 = 5425919) B5425919
theorem B9163691 : Blo 1607002 9163691 := bstep (se 1 (by rfl) ⟨6872768, by rfl⟩ : syracuseStep 9163691 = 13745537) B13745537
theorem B24769475 : Blo 1607002 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B37229665 : Blo 1607002 37229665 := bstep (se 2 (by rfl) ⟨13961124, by rfl⟩ : syracuseStep 37229665 = 27922249) B27922249
theorem B3052703 : Blo 1607002 3052703 := bstep (se 1 (by rfl) ⟨2289527, by rfl⟩ : syracuseStep 3052703 = 4579055) B4579055
theorem B15455461 : Blo 1607002 15455461 := bstep (se 4 (by rfl) ⟨1448949, by rfl⟩ : syracuseStep 15455461 = 2897899) B2897899
theorem B12203459 : Blo 1607002 12203459 := bstep (se 1 (by rfl) ⟨9152594, by rfl⟩ : syracuseStep 12203459 = 18305189) B18305189
theorem B4576799 : Blo 1607002 4576799 := bstep (se 1 (by rfl) ⟨3432599, by rfl⟩ : syracuseStep 4576799 = 6865199) B6865199
theorem B1808167 : Blo 1607002 1808167 := bstep (se 1 (by rfl) ⟨1356125, by rfl⟩ : syracuseStep 1808167 = 2712251) B2712251
theorem B3618863 : Blo 1607002 3618863 := bstep (se 1 (by rfl) ⟨2714147, by rfl⟩ : syracuseStep 3618863 = 5428295) B5428295
theorem B5429483 : Blo 1607002 5429483 := bstep (se 1 (by rfl) ⟨4072112, by rfl⟩ : syracuseStep 5429483 = 8144225) B8144225
theorem B11156023 : Blo 1607002 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B4070047 : Blo 1607002 4070047 := bstep (se 1 (by rfl) ⟨3052535, by rfl⟩ : syracuseStep 4070047 = 6105071) B6105071
theorem B3619583 : Blo 1607002 3619583 := bstep (se 1 (by rfl) ⟨2714687, by rfl⟩ : syracuseStep 3619583 = 5429375) B5429375
theorem B3578761 : Blo 1607002 3578761 := bstep (se 2 (by rfl) ⟨1342035, by rfl⟩ : syracuseStep 3578761 = 2684071) B2684071
theorem B5151707 : Blo 1607002 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B1809391 : Blo 1607002 1809391 := bstep (se 1 (by rfl) ⟨1357043, by rfl⟩ : syracuseStep 1809391 = 2714087) B2714087
theorem B13745159 : Blo 1607002 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B21994537 : Blo 1607002 21994537 := bstep (se 2 (by rfl) ⟨8247951, by rfl⟩ : syracuseStep 21994537 = 16495903) B16495903
theorem B8690759 : Blo 1607002 8690759 := bstep (se 1 (by rfl) ⟨6518069, by rfl⟩ : syracuseStep 8690759 = 13036139) B13036139
theorem B3620051 : Blo 1607002 3620051 := bstep (se 1 (by rfl) ⟨2715038, by rfl⟩ : syracuseStep 3620051 = 5430077) B5430077
theorem B45858007 : Blo 1607002 45858007 := bstep (se 1 (by rfl) ⟨34393505, by rfl⟩ : syracuseStep 45858007 = 68787011) B68787011
theorem B4128239 : Blo 1607002 4128239 := bstep (se 1 (by rfl) ⟨3096179, by rfl⟩ : syracuseStep 4128239 = 6192359) B6192359
theorem B1932827 : Blo 1607002 1932827 := bstep (se 1 (by rfl) ⟨1449620, by rfl⟩ : syracuseStep 1932827 = 2899241) B2899241
theorem B4071667 : Blo 1607002 4071667 := bstep (se 1 (by rfl) ⟨3053750, by rfl⟩ : syracuseStep 4071667 = 6107501) B6107501
theorem B4579897 : Blo 1607002 4579897 := bstep (se 2 (by rfl) ⟨1717461, by rfl⟩ : syracuseStep 4579897 = 3434923) B3434923
theorem B17613395 : Blo 1607002 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B8135639 : Blo 1607002 8135639 := bstep (se 1 (by rfl) ⟨6101729, by rfl⟩ : syracuseStep 8135639 = 12203459) B12203459
theorem B5154205 : Blo 1607002 5154205 := bstep (se 3 (by rfl) ⟨966413, by rfl⟩ : syracuseStep 5154205 = 1932827) B1932827
theorem B1607151 : Blo 1607002 1607151 := bstep (se 1 (by rfl) ⟨1205363, by rfl⟩ : syracuseStep 1607151 = 2410727) B2410727
theorem B59508245 : Blo 1607002 59508245 := bstep (se 6 (by rfl) ⟨1394724, by rfl⟩ : syracuseStep 59508245 = 2789449) B2789449
theorem B1607271 : Blo 1607002 1607271 := bstep (se 1 (by rfl) ⟨1205453, by rfl⟩ : syracuseStep 1607271 = 2410907) B2410907
theorem B1607551 : Blo 1607002 1607551 := bstep (se 1 (by rfl) ⟨1205663, by rfl⟩ : syracuseStep 1607551 = 2411327) B2411327
theorem B14673793 : Blo 1607002 14673793 := bstep (se 2 (by rfl) ⟨5502672, by rfl⟩ : syracuseStep 14673793 = 11005345) B11005345
theorem B3434471 : Blo 1607002 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B5793839 : Blo 1607002 5793839 := bstep (se 1 (by rfl) ⟨4345379, by rfl⟩ : syracuseStep 5793839 = 8690759) B8690759
theorem B1607771 : Blo 1607002 1607771 := bstep (se 1 (by rfl) ⟨1205828, by rfl⟩ : syracuseStep 1607771 = 2411657) B2411657
theorem B2410607 : Blo 1607002 2410607 := bstep (se 1 (by rfl) ⟨1807955, by rfl⟩ : syracuseStep 2410607 = 3615911) B3615911
theorem B1607807 : Blo 1607002 1607807 := bstep (se 1 (by rfl) ⟨1205855, by rfl⟩ : syracuseStep 1607807 = 2411711) B2411711
theorem B1607999 : Blo 1607002 1607999 := bstep (se 1 (by rfl) ⟨1205999, by rfl⟩ : syracuseStep 1607999 = 2411999) B2411999
theorem B1608039 : Blo 1607002 1608039 := bstep (se 1 (by rfl) ⟨1206029, by rfl⟩ : syracuseStep 1608039 = 2412059) B2412059
theorem B2410889 : Blo 1607002 2410889 := bstep (se 2 (by rfl) ⟨904083, by rfl⟩ : syracuseStep 2410889 = 1808167) B1808167
theorem B1608319 : Blo 1607002 1608319 := bstep (se 1 (by rfl) ⟨1206239, by rfl⟩ : syracuseStep 1608319 = 2412479) B2412479
theorem B19548863 : Blo 1607002 19548863 := bstep (se 1 (by rfl) ⟨14661647, by rfl⟩ : syracuseStep 19548863 = 29323295) B29323295
theorem B101722931 : Blo 1607002 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B3435367 : Blo 1607002 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B2411387 : Blo 1607002 2411387 := bstep (se 1 (by rfl) ⟨1808540, by rfl⟩ : syracuseStep 2411387 = 3617081) B3617081
theorem B6106013 : Blo 1607002 6106013 := bstep (se 3 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 6106013 = 2289755) B2289755
theorem B9161707 : Blo 1607002 9161707 := bstep (se 1 (by rfl) ⟨6871280, by rfl⟩ : syracuseStep 9161707 = 13742561) B13742561
theorem B2411519 : Blo 1607002 2411519 := bstep (se 1 (by rfl) ⟨1808639, by rfl⟩ : syracuseStep 2411519 = 3617279) B3617279
theorem B2289055 : Blo 1607002 2289055 := bstep (se 1 (by rfl) ⟨1716791, by rfl⟩ : syracuseStep 2289055 = 3433583) B3433583
theorem B3861935 : Blo 1607002 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B2035135 : Blo 1607002 2035135 := bstep (se 1 (by rfl) ⟨1526351, by rfl⟩ : syracuseStep 2035135 = 3052703) B3052703
theorem B5426729 : Blo 1607002 5426729 := bstep (se 2 (by rfl) ⟨2035023, by rfl⟩ : syracuseStep 5426729 = 4070047) B4070047
theorem B3051199 : Blo 1607002 3051199 := bstep (se 1 (by rfl) ⟨2288399, by rfl⟩ : syracuseStep 3051199 = 4576799) B4576799
theorem B244576037 : Blo 1607002 244576037 := bstep (se 4 (by rfl) ⟨22929003, by rfl⟩ : syracuseStep 244576037 = 45858007) B45858007
theorem B3616595 : Blo 1607002 3616595 := bstep (se 1 (by rfl) ⟨2712446, by rfl⟩ : syracuseStep 3616595 = 5424893) B5424893
theorem B3616703 : Blo 1607002 3616703 := bstep (se 1 (by rfl) ⟨2712527, by rfl⟩ : syracuseStep 3616703 = 5425055) B5425055
theorem B2412521 : Blo 1607002 2412521 := bstep (se 2 (by rfl) ⟨904695, by rfl⟩ : syracuseStep 2412521 = 1809391) B1809391
theorem B2412575 : Blo 1607002 2412575 := bstep (se 1 (by rfl) ⟨1809431, by rfl⟩ : syracuseStep 2412575 = 3618863) B3618863
theorem B49639553 : Blo 1607002 49639553 := bstep (se 2 (by rfl) ⟨18614832, by rfl⟩ : syracuseStep 49639553 = 37229665) B37229665
theorem B58683635 : Blo 1607002 58683635 := bstep (se 1 (by rfl) ⟨44012726, by rfl⟩ : syracuseStep 58683635 = 88025453) B88025453
theorem B20607281 : Blo 1607002 20607281 := bstep (se 2 (by rfl) ⟨7727730, by rfl⟩ : syracuseStep 20607281 = 15455461) B15455461
theorem B9154943 : Blo 1607002 9154943 := bstep (se 1 (by rfl) ⟨6866207, by rfl⟩ : syracuseStep 9154943 = 13732415) B13732415
theorem B2413055 : Blo 1607002 2413055 := bstep (se 1 (by rfl) ⟨1809791, by rfl⟩ : syracuseStep 2413055 = 3619583) B3619583
theorem B9163439 : Blo 1607002 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B9155375 : Blo 1607002 9155375 := bstep (se 1 (by rfl) ⟨6866531, by rfl⟩ : syracuseStep 9155375 = 13733063) B13733063
theorem B2413367 : Blo 1607002 2413367 := bstep (se 1 (by rfl) ⟨1810025, by rfl⟩ : syracuseStep 2413367 = 3620051) B3620051
theorem B3617657 : Blo 1607002 3617657 := bstep (se 2 (by rfl) ⟨1356621, by rfl⟩ : syracuseStep 3617657 = 2713243) B2713243
theorem B8139689 : Blo 1607002 8139689 := bstep (se 2 (by rfl) ⟨3052383, by rfl⟩ : syracuseStep 8139689 = 6104767) B6104767
theorem B3618431 : Blo 1607002 3618431 := bstep (se 1 (by rfl) ⟨2713823, by rfl⟩ : syracuseStep 3618431 = 5427647) B5427647
theorem B6109127 : Blo 1607002 6109127 := bstep (se 1 (by rfl) ⟨4581845, by rfl⟩ : syracuseStep 6109127 = 9163691) B9163691
theorem B16512983 : Blo 1607002 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B6871007 : Blo 1607002 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B14874697 : Blo 1607002 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B5429321 : Blo 1607002 5429321 := bstep (se 2 (by rfl) ⟨2035995, by rfl⟩ : syracuseStep 5429321 = 4071991) B4071991
theorem B3053675 : Blo 1607002 3053675 := bstep (se 1 (by rfl) ⟨2290256, by rfl⟩ : syracuseStep 3053675 = 4580513) B4580513
theorem B7723117 : Blo 1607002 7723117 := bstep (se 3 (by rfl) ⟨1448084, by rfl⟩ : syracuseStep 7723117 = 2896169) B2896169
theorem B3618953 : Blo 1607002 3618953 := bstep (se 2 (by rfl) ⟨1357107, by rfl⟩ : syracuseStep 3618953 = 2714215) B2714215
theorem B88004879 : Blo 1607002 88004879 := bstep (se 1 (by rfl) ⟨66003659, by rfl⟩ : syracuseStep 88004879 = 132007319) B132007319
theorem B5429753 : Blo 1607002 5429753 := bstep (se 2 (by rfl) ⟨2036157, by rfl⟩ : syracuseStep 5429753 = 4072315) B4072315
theorem B29326049 : Blo 1607002 29326049 := bstep (se 2 (by rfl) ⟨10997268, by rfl⟩ : syracuseStep 29326049 = 21994537) B21994537
theorem B3619655 : Blo 1607002 3619655 := bstep (se 1 (by rfl) ⟨2714741, by rfl⟩ : syracuseStep 3619655 = 5429483) B5429483
theorem B4348829 : Blo 1607002 4348829 := bstep (se 3 (by rfl) ⟨815405, by rfl⟩ : syracuseStep 4348829 = 1630811) B1630811
theorem B19086725 : Blo 1607002 19086725 := bstep (se 4 (by rfl) ⟨1789380, by rfl⟩ : syracuseStep 19086725 = 3578761) B3578761
theorem B1809823 : Blo 1607002 1809823 := bstep (se 1 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 1809823 = 2714735) B2714735
theorem B2752159 : Blo 1607002 2752159 := bstep (se 1 (by rfl) ⟨2064119, by rfl⟩ : syracuseStep 2752159 = 4128239) B4128239
theorem B6102823 : Blo 1607002 6102823 := bstep (se 1 (by rfl) ⟨4577117, by rfl⟩ : syracuseStep 6102823 = 9154235) B9154235
theorem B13738187 : Blo 1607002 13738187 := bstep (se 1 (by rfl) ⟨10303640, by rfl⟩ : syracuseStep 13738187 = 20607281) B20607281
theorem B6103295 : Blo 1607002 6103295 := bstep (se 1 (by rfl) ⟨4577471, by rfl⟩ : syracuseStep 6103295 = 9154943) B9154943
theorem B79331717 : Blo 1607002 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B6103583 : Blo 1607002 6103583 := bstep (se 1 (by rfl) ⟨4577687, by rfl⟩ : syracuseStep 6103583 = 9155375) B9155375
theorem B41189957 : Blo 1607002 41189957 := bstep (se 4 (by rfl) ⟨3861558, by rfl⟩ : syracuseStep 41189957 = 7723117) B7723117
theorem B5423759 : Blo 1607002 5423759 := bstep (se 1 (by rfl) ⟨4067819, by rfl⟩ : syracuseStep 5423759 = 8135639) B8135639
theorem B50897933 : Blo 1607002 50897933 := bstep (se 3 (by rfl) ⟨9543362, by rfl⟩ : syracuseStep 50897933 = 19086725) B19086725
theorem B4580489 : Blo 1607002 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B4072751 : Blo 1607002 4072751 := bstep (se 1 (by rfl) ⟨3054563, by rfl⟩ : syracuseStep 4072751 = 6109127) B6109127
theorem B12215609 : Blo 1607002 12215609 := bstep (se 2 (by rfl) ⟨4580853, by rfl⟩ : syracuseStep 12215609 = 9161707) B9161707
theorem B1607071 : Blo 1607002 1607071 := bstep (se 1 (by rfl) ⟨1205303, by rfl⟩ : syracuseStep 1607071 = 2410607) B2410607
theorem B1607259 : Blo 1607002 1607259 := bstep (se 1 (by rfl) ⟨1205444, by rfl⟩ : syracuseStep 1607259 = 2410889) B2410889
theorem B67815287 : Blo 1607002 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B1607591 : Blo 1607002 1607591 := bstep (se 1 (by rfl) ⟨1205693, by rfl⟩ : syracuseStep 1607591 = 2411387) B2411387
theorem B2713513 : Blo 1607002 2713513 := bstep (se 2 (by rfl) ⟨1017567, by rfl⟩ : syracuseStep 2713513 = 2035135) B2035135
theorem B1607679 : Blo 1607002 1607679 := bstep (se 1 (by rfl) ⟨1205759, by rfl⟩ : syracuseStep 1607679 = 2411519) B2411519
theorem B2574623 : Blo 1607002 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B8137097 : Blo 1607002 8137097 := bstep (se 2 (by rfl) ⟨3051411, by rfl⟩ : syracuseStep 8137097 = 6102823) B6102823
theorem B19565057 : Blo 1607002 19565057 := bstep (se 2 (by rfl) ⟨7336896, by rfl⟩ : syracuseStep 19565057 = 14673793) B14673793
theorem B2411063 : Blo 1607002 2411063 := bstep (se 1 (by rfl) ⟨1808297, by rfl⟩ : syracuseStep 2411063 = 3616595) B3616595
theorem B2411135 : Blo 1607002 2411135 := bstep (se 1 (by rfl) ⟨1808351, by rfl⟩ : syracuseStep 2411135 = 3616703) B3616703
theorem B1608347 : Blo 1607002 1608347 := bstep (se 1 (by rfl) ⟨1206260, by rfl⟩ : syracuseStep 1608347 = 2412521) B2412521
theorem B1608383 : Blo 1607002 1608383 := bstep (se 1 (by rfl) ⟨1206287, by rfl⟩ : syracuseStep 1608383 = 2412575) B2412575
theorem B1608703 : Blo 1607002 1608703 := bstep (se 1 (by rfl) ⟨1206527, by rfl⟩ : syracuseStep 1608703 = 2413055) B2413055
theorem B11742263 : Blo 1607002 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B1608911 : Blo 1607002 1608911 := bstep (se 1 (by rfl) ⟨1206683, by rfl⟩ : syracuseStep 1608911 = 2413367) B2413367
theorem B2411771 : Blo 1607002 2411771 := bstep (se 1 (by rfl) ⟨1808828, by rfl⟩ : syracuseStep 2411771 = 3617657) B3617657
theorem B5426459 : Blo 1607002 5426459 := bstep (se 1 (by rfl) ⟨4069844, by rfl⟩ : syracuseStep 5426459 = 8139689) B8139689
theorem B6106529 : Blo 1607002 6106529 := bstep (se 2 (by rfl) ⟨2289948, by rfl⟩ : syracuseStep 6106529 = 4579897) B4579897
theorem B2412287 : Blo 1607002 2412287 := bstep (se 1 (by rfl) ⟨1809215, by rfl⟩ : syracuseStep 2412287 = 3618431) B3618431
theorem B2289647 : Blo 1607002 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B3862559 : Blo 1607002 3862559 := bstep (se 1 (by rfl) ⟨2896919, by rfl⟩ : syracuseStep 3862559 = 5793839) B5793839
theorem B2035783 : Blo 1607002 2035783 := bstep (se 1 (by rfl) ⟨1526837, by rfl⟩ : syracuseStep 2035783 = 3053675) B3053675
theorem B2412635 : Blo 1607002 2412635 := bstep (se 1 (by rfl) ⟨1809476, by rfl⟩ : syracuseStep 2412635 = 3618953) B3618953
theorem B19550699 : Blo 1607002 19550699 := bstep (se 1 (by rfl) ⟨14663024, by rfl⟩ : syracuseStep 19550699 = 29326049) B29326049
theorem B3052073 : Blo 1607002 3052073 := bstep (se 2 (by rfl) ⟨1144527, by rfl⟩ : syracuseStep 3052073 = 2289055) B2289055
theorem B2413097 : Blo 1607002 2413097 := bstep (se 2 (by rfl) ⟨904911, by rfl⟩ : syracuseStep 2413097 = 1809823) B1809823
theorem B2413103 : Blo 1607002 2413103 := bstep (se 1 (by rfl) ⟨1809827, by rfl⟩ : syracuseStep 2413103 = 3619655) B3619655
theorem B4068265 : Blo 1607002 4068265 := bstep (se 2 (by rfl) ⟨1525599, by rfl⟩ : syracuseStep 4068265 = 3051199) B3051199
theorem B3617819 : Blo 1607002 3617819 := bstep (se 1 (by rfl) ⟨2713364, by rfl⟩ : syracuseStep 3617819 = 5426729) B5426729
theorem B11596877 : Blo 1607002 11596877 := bstep (se 3 (by rfl) ⟨2174414, by rfl⟩ : syracuseStep 11596877 = 4348829) B4348829
theorem B163050691 : Blo 1607002 163050691 := bstep (se 1 (by rfl) ⟨122288018, by rfl⟩ : syracuseStep 163050691 = 244576037) B244576037
theorem B18322685 : Blo 1607002 18322685 := bstep (se 3 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 18322685 = 6871007) B6871007
theorem B33093035 : Blo 1607002 33093035 := bstep (se 1 (by rfl) ⟨24819776, by rfl⟩ : syracuseStep 33093035 = 49639553) B49639553
theorem B39122423 : Blo 1607002 39122423 := bstep (se 1 (by rfl) ⟨29341817, by rfl⟩ : syracuseStep 39122423 = 58683635) B58683635
theorem B5428889 : Blo 1607002 5428889 := bstep (se 2 (by rfl) ⟨2035833, by rfl⟩ : syracuseStep 5428889 = 4071667) B4071667
theorem B6108959 : Blo 1607002 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B39672163 : Blo 1607002 39672163 := bstep (se 1 (by rfl) ⟨29754122, by rfl⟩ : syracuseStep 39672163 = 59508245) B59508245
theorem B11008655 : Blo 1607002 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B3619547 : Blo 1607002 3619547 := bstep (se 1 (by rfl) ⟨2714660, by rfl⟩ : syracuseStep 3619547 = 5429321) B5429321
theorem B58669919 : Blo 1607002 58669919 := bstep (se 1 (by rfl) ⟨44002439, by rfl⟩ : syracuseStep 58669919 = 88004879) B88004879
theorem B3619835 : Blo 1607002 3619835 := bstep (se 1 (by rfl) ⟨2714876, by rfl⟩ : syracuseStep 3619835 = 5429753) B5429753
theorem B13032575 : Blo 1607002 13032575 := bstep (se 1 (by rfl) ⟨9774431, by rfl⟩ : syracuseStep 13032575 = 19548863) B19548863
theorem B6872273 : Blo 1607002 6872273 := bstep (se 2 (by rfl) ⟨2577102, by rfl⟩ : syracuseStep 6872273 = 5154205) B5154205
theorem B4070675 : Blo 1607002 4070675 := bstep (se 1 (by rfl) ⟨3053006, by rfl⟩ : syracuseStep 4070675 = 6106013) B6106013
theorem B3669545 : Blo 1607002 3669545 := bstep (se 2 (by rfl) ⟨1376079, by rfl⟩ : syracuseStep 3669545 = 2752159) B2752159
theorem B9158791 : Blo 1607002 9158791 := bstep (se 1 (by rfl) ⟨6869093, by rfl⟩ : syracuseStep 9158791 = 13738187) B13738187
theorem B52887811 : Blo 1607002 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B13033799 : Blo 1607002 13033799 := bstep (se 1 (by rfl) ⟨9775349, by rfl⟩ : syracuseStep 13033799 = 19550699) B19550699
theorem B12214637 : Blo 1607002 12214637 := bstep (se 3 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 12214637 = 4580489) B4580489
theorem B27459971 : Blo 1607002 27459971 := bstep (se 1 (by rfl) ⟨20594978, by rfl⟩ : syracuseStep 27459971 = 41189957) B41189957
theorem B33931955 : Blo 1607002 33931955 := bstep (se 1 (by rfl) ⟨25448966, by rfl⟩ : syracuseStep 33931955 = 50897933) B50897933
theorem B6865661 : Blo 1607002 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B12215123 : Blo 1607002 12215123 := bstep (se 1 (by rfl) ⟨9161342, by rfl⟩ : syracuseStep 12215123 = 18322685) B18322685
theorem B8143739 : Blo 1607002 8143739 := bstep (se 1 (by rfl) ⟨6107804, by rfl⟩ : syracuseStep 8143739 = 12215609) B12215609
theorem B22062023 : Blo 1607002 22062023 := bstep (se 1 (by rfl) ⟨16546517, by rfl⟩ : syracuseStep 22062023 = 33093035) B33093035
theorem B4072639 : Blo 1607002 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B5424353 : Blo 1607002 5424353 := bstep (se 2 (by rfl) ⟨2034132, by rfl⟩ : syracuseStep 5424353 = 4068265) B4068265
theorem B217400921 : Blo 1607002 217400921 := bstep (se 2 (by rfl) ⟨81525345, by rfl⟩ : syracuseStep 217400921 = 163050691) B163050691
theorem B5424731 : Blo 1607002 5424731 := bstep (se 1 (by rfl) ⟨4068548, by rfl⟩ : syracuseStep 5424731 = 8137097) B8137097
theorem B13043371 : Blo 1607002 13043371 := bstep (se 1 (by rfl) ⟨9782528, by rfl⟩ : syracuseStep 13043371 = 19565057) B19565057
theorem B1607375 : Blo 1607002 1607375 := bstep (se 1 (by rfl) ⟨1205531, by rfl⟩ : syracuseStep 1607375 = 2411063) B2411063
theorem B1607423 : Blo 1607002 1607423 := bstep (se 1 (by rfl) ⟨1205567, by rfl⟩ : syracuseStep 1607423 = 2411135) B2411135
theorem B211584869 : Blo 1607002 211584869 := bstep (se 4 (by rfl) ⟨19836081, by rfl⟩ : syracuseStep 211584869 = 39672163) B39672163
theorem B4581515 : Blo 1607002 4581515 := bstep (se 1 (by rfl) ⟨3436136, by rfl⟩ : syracuseStep 4581515 = 6872273) B6872273
theorem B1607847 : Blo 1607002 1607847 := bstep (se 1 (by rfl) ⟨1205885, by rfl⟩ : syracuseStep 1607847 = 2411771) B2411771
theorem B2713783 : Blo 1607002 2713783 := bstep (se 1 (by rfl) ⟨2035337, by rfl⟩ : syracuseStep 2713783 = 4070675) B4070675
theorem B1608191 : Blo 1607002 1608191 := bstep (se 1 (by rfl) ⟨1206143, by rfl⟩ : syracuseStep 1608191 = 2412287) B2412287
theorem B6105725 : Blo 1607002 6105725 := bstep (se 3 (by rfl) ⟨1144823, by rfl⟩ : syracuseStep 6105725 = 2289647) B2289647
theorem B2575039 : Blo 1607002 2575039 := bstep (se 1 (by rfl) ⟨1931279, by rfl⟩ : syracuseStep 2575039 = 3862559) B3862559
theorem B1608423 : Blo 1607002 1608423 := bstep (se 1 (by rfl) ⟨1206317, by rfl⟩ : syracuseStep 1608423 = 2412635) B2412635
theorem B2714377 : Blo 1607002 2714377 := bstep (se 2 (by rfl) ⟨1017891, by rfl⟩ : syracuseStep 2714377 = 2035783) B2035783
theorem B2034715 : Blo 1607002 2034715 := bstep (se 1 (by rfl) ⟨1526036, by rfl⟩ : syracuseStep 2034715 = 3052073) B3052073
theorem B1608731 : Blo 1607002 1608731 := bstep (se 1 (by rfl) ⟨1206548, by rfl⟩ : syracuseStep 1608731 = 2413097) B2413097
theorem B1608735 : Blo 1607002 1608735 := bstep (se 1 (by rfl) ⟨1206551, by rfl⟩ : syracuseStep 1608735 = 2413103) B2413103
theorem B3615839 : Blo 1607002 3615839 := bstep (se 1 (by rfl) ⟨2711879, by rfl⟩ : syracuseStep 3615839 = 5423759) B5423759
theorem B2411879 : Blo 1607002 2411879 := bstep (se 1 (by rfl) ⟨1808909, by rfl⟩ : syracuseStep 2411879 = 3617819) B3617819
theorem B2715167 : Blo 1607002 2715167 := bstep (se 1 (by rfl) ⟨2036375, by rfl⟩ : syracuseStep 2715167 = 4072751) B4072751
theorem B2413031 : Blo 1607002 2413031 := bstep (se 1 (by rfl) ⟨1809773, by rfl⟩ : syracuseStep 2413031 = 3619547) B3619547
theorem B39113279 : Blo 1607002 39113279 := bstep (se 1 (by rfl) ⟨29334959, by rfl⟩ : syracuseStep 39113279 = 58669919) B58669919
theorem B2413223 : Blo 1607002 2413223 := bstep (se 1 (by rfl) ⟨1809917, by rfl⟩ : syracuseStep 2413223 = 3619835) B3619835
theorem B7828175 : Blo 1607002 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B8688383 : Blo 1607002 8688383 := bstep (se 1 (by rfl) ⟨6516287, by rfl⟩ : syracuseStep 8688383 = 13032575) B13032575
theorem B3617639 : Blo 1607002 3617639 := bstep (se 1 (by rfl) ⟨2713229, by rfl⟩ : syracuseStep 3617639 = 5426459) B5426459
theorem B2446363 : Blo 1607002 2446363 := bstep (se 1 (by rfl) ⟨1834772, by rfl⟩ : syracuseStep 2446363 = 3669545) B3669545
theorem B3618017 : Blo 1607002 3618017 := bstep (se 2 (by rfl) ⟨1356756, by rfl⟩ : syracuseStep 3618017 = 2713513) B2713513
theorem B4068863 : Blo 1607002 4068863 := bstep (se 1 (by rfl) ⟨3051647, by rfl⟩ : syracuseStep 4068863 = 6103295) B6103295
theorem B4069055 : Blo 1607002 4069055 := bstep (se 1 (by rfl) ⟨3051791, by rfl⟩ : syracuseStep 4069055 = 6103583) B6103583
theorem B7731251 : Blo 1607002 7731251 := bstep (se 1 (by rfl) ⟨5798438, by rfl⟩ : syracuseStep 7731251 = 11596877) B11596877
theorem B26081615 : Blo 1607002 26081615 := bstep (se 1 (by rfl) ⟨19561211, by rfl⟩ : syracuseStep 26081615 = 39122423) B39122423
theorem B3619259 : Blo 1607002 3619259 := bstep (se 1 (by rfl) ⟨2714444, by rfl⟩ : syracuseStep 3619259 = 5428889) B5428889
theorem B45210191 : Blo 1607002 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B7339103 : Blo 1607002 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B4071019 : Blo 1607002 4071019 := bstep (se 1 (by rfl) ⟨3053264, by rfl⟩ : syracuseStep 4071019 = 6106529) B6106529
theorem B8143091 : Blo 1607002 8143091 := bstep (se 1 (by rfl) ⟨6107318, by rfl⟩ : syracuseStep 8143091 = 12214637) B12214637
theorem B70517081 : Blo 1607002 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B26075519 : Blo 1607002 26075519 := bstep (se 1 (by rfl) ⟨19556639, by rfl⟩ : syracuseStep 26075519 = 39113279) B39113279
theorem B5792255 : Blo 1607002 5792255 := bstep (se 1 (by rfl) ⟨4344191, by rfl⟩ : syracuseStep 5792255 = 8688383) B8688383
theorem B8143415 : Blo 1607002 8143415 := bstep (se 1 (by rfl) ⟨6107561, by rfl⟩ : syracuseStep 8143415 = 12215123) B12215123
theorem B3433385 : Blo 1607002 3433385 := bstep (se 2 (by rfl) ⟨1287519, by rfl⟩ : syracuseStep 3433385 = 2575039) B2575039
theorem B2712575 : Blo 1607002 2712575 := bstep (se 1 (by rfl) ⟨2034431, by rfl⟩ : syracuseStep 2712575 = 4068863) B4068863
theorem B144933947 : Blo 1607002 144933947 := bstep (se 1 (by rfl) ⟨108700460, by rfl⟩ : syracuseStep 144933947 = 217400921) B217400921
theorem B2712703 : Blo 1607002 2712703 := bstep (se 1 (by rfl) ⟨2034527, by rfl⟩ : syracuseStep 2712703 = 4069055) B4069055
theorem B5154167 : Blo 1607002 5154167 := bstep (se 1 (by rfl) ⟨3865625, by rfl⟩ : syracuseStep 5154167 = 7731251) B7731251
theorem B2712953 : Blo 1607002 2712953 := bstep (se 2 (by rfl) ⟨1017357, by rfl⟩ : syracuseStep 2712953 = 2034715) B2034715
theorem B3261817 : Blo 1607002 3261817 := bstep (se 2 (by rfl) ⟨1223181, by rfl⟩ : syracuseStep 3261817 = 2446363) B2446363
theorem B20875133 : Blo 1607002 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B2410559 : Blo 1607002 2410559 := bstep (se 1 (by rfl) ⟨1807919, by rfl⟩ : syracuseStep 2410559 = 3615839) B3615839
theorem B4892735 : Blo 1607002 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B1607919 : Blo 1607002 1607919 := bstep (se 1 (by rfl) ⟨1205939, by rfl⟩ : syracuseStep 1607919 = 2411879) B2411879
theorem B1608687 : Blo 1607002 1608687 := bstep (se 1 (by rfl) ⟨1206515, by rfl⟩ : syracuseStep 1608687 = 2413031) B2413031
theorem B1608815 : Blo 1607002 1608815 := bstep (se 1 (by rfl) ⟨1206611, by rfl⟩ : syracuseStep 1608815 = 2413223) B2413223
theorem B22621303 : Blo 1607002 22621303 := bstep (se 1 (by rfl) ⟨16965977, by rfl⟩ : syracuseStep 22621303 = 33931955) B33931955
theorem B2411759 : Blo 1607002 2411759 := bstep (se 1 (by rfl) ⟨1808819, by rfl⟩ : syracuseStep 2411759 = 3617639) B3617639
theorem B14708015 : Blo 1607002 14708015 := bstep (se 1 (by rfl) ⟨11031011, by rfl⟩ : syracuseStep 14708015 = 22062023) B22062023
theorem B3616235 : Blo 1607002 3616235 := bstep (se 1 (by rfl) ⟨2712176, by rfl⟩ : syracuseStep 3616235 = 5424353) B5424353
theorem B2412011 : Blo 1607002 2412011 := bstep (se 1 (by rfl) ⟨1809008, by rfl⟩ : syracuseStep 2412011 = 3618017) B3618017
theorem B3616487 : Blo 1607002 3616487 := bstep (se 1 (by rfl) ⟨2712365, by rfl⟩ : syracuseStep 3616487 = 5424731) B5424731
theorem B17387743 : Blo 1607002 17387743 := bstep (se 1 (by rfl) ⟨13040807, by rfl⟩ : syracuseStep 17387743 = 26081615) B26081615
theorem B2412839 : Blo 1607002 2412839 := bstep (se 1 (by rfl) ⟨1809629, by rfl⟩ : syracuseStep 2412839 = 3619259) B3619259
theorem B5428025 : Blo 1607002 5428025 := bstep (se 2 (by rfl) ⟨2035509, by rfl⟩ : syracuseStep 5428025 = 4071019) B4071019
theorem B12211721 : Blo 1607002 12211721 := bstep (se 2 (by rfl) ⟨4579395, by rfl⟩ : syracuseStep 12211721 = 9158791) B9158791
theorem B8689199 : Blo 1607002 8689199 := bstep (se 1 (by rfl) ⟨6516899, by rfl⟩ : syracuseStep 8689199 = 13033799) B13033799
theorem B3618377 : Blo 1607002 3618377 := bstep (se 2 (by rfl) ⟨1356891, by rfl⟩ : syracuseStep 3618377 = 2713783) B2713783
theorem B18306647 : Blo 1607002 18306647 := bstep (se 1 (by rfl) ⟨13729985, by rfl⟩ : syracuseStep 18306647 = 27459971) B27459971
theorem B4577107 : Blo 1607002 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B5429159 : Blo 1607002 5429159 := bstep (se 1 (by rfl) ⟨4071869, by rfl⟩ : syracuseStep 5429159 = 8143739) B8143739
theorem B3619169 : Blo 1607002 3619169 := bstep (se 2 (by rfl) ⟨1357188, by rfl⟩ : syracuseStep 3619169 = 2714377) B2714377
theorem B141056579 : Blo 1607002 141056579 := bstep (se 1 (by rfl) ⟨105792434, by rfl⟩ : syracuseStep 141056579 = 211584869) B211584869
theorem B3054343 : Blo 1607002 3054343 := bstep (se 1 (by rfl) ⟨2290757, by rfl⟩ : syracuseStep 3054343 = 4581515) B4581515
theorem B120560509 : Blo 1607002 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B5430185 : Blo 1607002 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B4070483 : Blo 1607002 4070483 := bstep (se 1 (by rfl) ⟨3052862, by rfl⟩ : syracuseStep 4070483 = 6105725) B6105725
theorem B17391161 : Blo 1607002 17391161 := bstep (se 2 (by rfl) ⟨6521685, by rfl⟩ : syracuseStep 17391161 = 13043371) B13043371
theorem B1810111 : Blo 1607002 1810111 := bstep (se 1 (by rfl) ⟨1357583, by rfl⟩ : syracuseStep 1810111 = 2715167) B2715167
theorem B17383679 : Blo 1607002 17383679 := bstep (se 1 (by rfl) ⟨13037759, by rfl⟩ : syracuseStep 17383679 = 26075519) B26075519
theorem B23183657 : Blo 1607002 23183657 := bstep (se 2 (by rfl) ⟨8693871, by rfl⟩ : syracuseStep 23183657 = 17387743) B17387743
theorem B156885493 : Blo 1607002 156885493 := bstep (se 5 (by rfl) ⟨7354007, by rfl⟩ : syracuseStep 156885493 = 14708015) B14708015
theorem B4072457 : Blo 1607002 4072457 := bstep (se 2 (by rfl) ⟨1527171, by rfl⟩ : syracuseStep 4072457 = 3054343) B3054343
theorem B1607039 : Blo 1607002 1607039 := bstep (se 1 (by rfl) ⟨1205279, by rfl⟩ : syracuseStep 1607039 = 2410559) B2410559
theorem B94037719 : Blo 1607002 94037719 := bstep (se 1 (by rfl) ⟨70528289, by rfl⟩ : syracuseStep 94037719 = 141056579) B141056579
theorem B2713655 : Blo 1607002 2713655 := bstep (se 1 (by rfl) ⟨2035241, by rfl⟩ : syracuseStep 2713655 = 4070483) B4070483
theorem B1607839 : Blo 1607002 1607839 := bstep (se 1 (by rfl) ⟨1205879, by rfl⟩ : syracuseStep 1607839 = 2411759) B2411759
theorem B2410823 : Blo 1607002 2410823 := bstep (se 1 (by rfl) ⟨1808117, by rfl⟩ : syracuseStep 2410823 = 3616235) B3616235
theorem B1608007 : Blo 1607002 1608007 := bstep (se 1 (by rfl) ⟨1206005, by rfl⟩ : syracuseStep 1608007 = 2412011) B2412011
theorem B11594107 : Blo 1607002 11594107 := bstep (se 1 (by rfl) ⟨8695580, by rfl⟩ : syracuseStep 11594107 = 17391161) B17391161
theorem B2410991 : Blo 1607002 2410991 := bstep (se 1 (by rfl) ⟨1808243, by rfl⟩ : syracuseStep 2410991 = 3616487) B3616487
theorem B1608559 : Blo 1607002 1608559 := bstep (se 1 (by rfl) ⟨1206419, by rfl⟩ : syracuseStep 1608559 = 2412839) B2412839
theorem B3861503 : Blo 1607002 3861503 := bstep (se 1 (by rfl) ⟨2896127, by rfl⟩ : syracuseStep 3861503 = 5792255) B5792255
theorem B3436111 : Blo 1607002 3436111 := bstep (se 1 (by rfl) ⟨2577083, by rfl⟩ : syracuseStep 3436111 = 5154167) B5154167
theorem B2412251 : Blo 1607002 2412251 := bstep (se 1 (by rfl) ⟨1809188, by rfl⟩ : syracuseStep 2412251 = 3618377) B3618377
theorem B160747345 : Blo 1607002 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B23171197 : Blo 1607002 23171197 := bstep (se 3 (by rfl) ⟨4344599, by rfl⟩ : syracuseStep 23171197 = 8689199) B8689199
theorem B3616937 : Blo 1607002 3616937 := bstep (se 2 (by rfl) ⟨1356351, by rfl⟩ : syracuseStep 3616937 = 2712703) B2712703
theorem B2412779 : Blo 1607002 2412779 := bstep (se 1 (by rfl) ⟨1809584, by rfl⟩ : syracuseStep 2412779 = 3619169) B3619169
theorem B2413481 : Blo 1607002 2413481 := bstep (se 2 (by rfl) ⟨905055, by rfl⟩ : syracuseStep 2413481 = 1810111) B1810111
theorem B9155693 : Blo 1607002 9155693 := bstep (se 3 (by rfl) ⟨1716692, by rfl⟩ : syracuseStep 9155693 = 3433385) B3433385
theorem B5428727 : Blo 1607002 5428727 := bstep (se 1 (by rfl) ⟨4071545, by rfl⟩ : syracuseStep 5428727 = 8143091) B8143091
theorem B13047293 : Blo 1607002 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B47011387 : Blo 1607002 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B5428943 : Blo 1607002 5428943 := bstep (se 1 (by rfl) ⟨4071707, by rfl⟩ : syracuseStep 5428943 = 8143415) B8143415
theorem B3618683 : Blo 1607002 3618683 := bstep (se 1 (by rfl) ⟨2714012, by rfl⟩ : syracuseStep 3618683 = 5428025) B5428025
theorem B1808383 : Blo 1607002 1808383 := bstep (se 1 (by rfl) ⟨1356287, by rfl⟩ : syracuseStep 1808383 = 2712575) B2712575
theorem B96622631 : Blo 1607002 96622631 := bstep (se 1 (by rfl) ⟨72466973, by rfl⟩ : syracuseStep 96622631 = 144933947) B144933947
theorem B1808635 : Blo 1607002 1808635 := bstep (se 1 (by rfl) ⟨1356476, by rfl⟩ : syracuseStep 1808635 = 2712953) B2712953
theorem B8141147 : Blo 1607002 8141147 := bstep (se 1 (by rfl) ⟨6105860, by rfl⟩ : syracuseStep 8141147 = 12211721) B12211721
theorem B12204431 : Blo 1607002 12204431 := bstep (se 1 (by rfl) ⟨9153323, by rfl⟩ : syracuseStep 12204431 = 18306647) B18306647
theorem B13916755 : Blo 1607002 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B3619439 : Blo 1607002 3619439 := bstep (se 1 (by rfl) ⟨2714579, by rfl⟩ : syracuseStep 3619439 = 5429159) B5429159
theorem B30161737 : Blo 1607002 30161737 := bstep (se 2 (by rfl) ⟨11310651, by rfl⟩ : syracuseStep 30161737 = 22621303) B22621303
theorem B4349089 : Blo 1607002 4349089 := bstep (se 2 (by rfl) ⟨1630908, by rfl⟩ : syracuseStep 4349089 = 3261817) B3261817
theorem B3620123 : Blo 1607002 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B6102809 : Blo 1607002 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B15458809 : Blo 1607002 15458809 := bstep (se 2 (by rfl) ⟨5797053, by rfl⟩ : syracuseStep 15458809 = 11594107) B11594107
theorem B6103795 : Blo 1607002 6103795 := bstep (se 1 (by rfl) ⟨4577846, by rfl⟩ : syracuseStep 6103795 = 9155693) B9155693
theorem B18555673 : Blo 1607002 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B40215649 : Blo 1607002 40215649 := bstep (se 2 (by rfl) ⟨15080868, by rfl⟩ : syracuseStep 40215649 = 30161737) B30161737
theorem B64415087 : Blo 1607002 64415087 := bstep (se 1 (by rfl) ⟨48311315, by rfl⟩ : syracuseStep 64415087 = 96622631) B96622631
theorem B1607215 : Blo 1607002 1607215 := bstep (se 1 (by rfl) ⟨1205411, by rfl⟩ : syracuseStep 1607215 = 2410823) B2410823
theorem B8136287 : Blo 1607002 8136287 := bstep (se 1 (by rfl) ⟨6102215, by rfl⟩ : syracuseStep 8136287 = 12204431) B12204431
theorem B1607327 : Blo 1607002 1607327 := bstep (se 1 (by rfl) ⟨1205495, by rfl⟩ : syracuseStep 1607327 = 2410991) B2410991
theorem B857319173 : Blo 1607002 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B2574335 : Blo 1607002 2574335 := bstep (se 1 (by rfl) ⟨1930751, by rfl⟩ : syracuseStep 2574335 = 3861503) B3861503
theorem B4581481 : Blo 1607002 4581481 := bstep (se 2 (by rfl) ⟨1718055, by rfl⟩ : syracuseStep 4581481 = 3436111) B3436111
theorem B1608167 : Blo 1607002 1608167 := bstep (se 1 (by rfl) ⟨1206125, by rfl⟩ : syracuseStep 1608167 = 2412251) B2412251
theorem B2411177 : Blo 1607002 2411177 := bstep (se 2 (by rfl) ⟨904191, by rfl⟩ : syracuseStep 2411177 = 1808383) B1808383
theorem B2411291 : Blo 1607002 2411291 := bstep (se 1 (by rfl) ⟨1808468, by rfl⟩ : syracuseStep 2411291 = 3616937) B3616937
theorem B1608519 : Blo 1607002 1608519 := bstep (se 1 (by rfl) ⟨1206389, by rfl⟩ : syracuseStep 1608519 = 2412779) B2412779
theorem B30894929 : Blo 1607002 30894929 := bstep (se 2 (by rfl) ⟨11585598, by rfl⟩ : syracuseStep 30894929 = 23171197) B23171197
theorem B2411513 : Blo 1607002 2411513 := bstep (se 2 (by rfl) ⟨904317, by rfl⟩ : syracuseStep 2411513 = 1808635) B1808635
theorem B1608987 : Blo 1607002 1608987 := bstep (se 1 (by rfl) ⟨1206740, by rfl⟩ : syracuseStep 1608987 = 2413481) B2413481
theorem B2714971 : Blo 1607002 2714971 := bstep (se 1 (by rfl) ⟨2036228, by rfl⟩ : syracuseStep 2714971 = 4072457) B4072457
theorem B2412455 : Blo 1607002 2412455 := bstep (se 1 (by rfl) ⟨1809341, by rfl⟩ : syracuseStep 2412455 = 3618683) B3618683
theorem B5427431 : Blo 1607002 5427431 := bstep (se 1 (by rfl) ⟨4070573, by rfl⟩ : syracuseStep 5427431 = 8141147) B8141147
theorem B2412959 : Blo 1607002 2412959 := bstep (se 1 (by rfl) ⟨1809719, by rfl⟩ : syracuseStep 2412959 = 3619439) B3619439
theorem B62681849 : Blo 1607002 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B2413415 : Blo 1607002 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B125383625 : Blo 1607002 125383625 := bstep (se 2 (by rfl) ⟨47018859, by rfl⟩ : syracuseStep 125383625 = 94037719) B94037719
theorem B4068539 : Blo 1607002 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B11589119 : Blo 1607002 11589119 := bstep (se 1 (by rfl) ⟨8691839, by rfl⟩ : syracuseStep 11589119 = 17383679) B17383679
theorem B15455771 : Blo 1607002 15455771 := bstep (se 1 (by rfl) ⟨11591828, by rfl⟩ : syracuseStep 15455771 = 23183657) B23183657
theorem B209180657 : Blo 1607002 209180657 := bstep (se 2 (by rfl) ⟨78442746, by rfl⟩ : syracuseStep 209180657 = 156885493) B156885493
theorem B3619151 : Blo 1607002 3619151 := bstep (se 1 (by rfl) ⟨2714363, by rfl⟩ : syracuseStep 3619151 = 5428727) B5428727
theorem B8698195 : Blo 1607002 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B3619295 : Blo 1607002 3619295 := bstep (se 1 (by rfl) ⟨2714471, by rfl⟩ : syracuseStep 3619295 = 5428943) B5428943
theorem B1809103 : Blo 1607002 1809103 := bstep (se 1 (by rfl) ⟨1356827, by rfl⟩ : syracuseStep 1809103 = 2713655) B2713655
theorem B5798785 : Blo 1607002 5798785 := bstep (se 2 (by rfl) ⟨2174544, by rfl⟩ : syracuseStep 5798785 = 4349089) B4349089
theorem B41787899 : Blo 1607002 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B20611745 : Blo 1607002 20611745 := bstep (se 2 (by rfl) ⟨7729404, by rfl⟩ : syracuseStep 20611745 = 15458809) B15458809
theorem B2712359 : Blo 1607002 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B42943391 : Blo 1607002 42943391 := bstep (se 1 (by rfl) ⟨32207543, by rfl⟩ : syracuseStep 42943391 = 64415087) B64415087
theorem B7726079 : Blo 1607002 7726079 := bstep (se 1 (by rfl) ⟨5794559, by rfl⟩ : syracuseStep 7726079 = 11589119) B11589119
theorem B24740897 : Blo 1607002 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B5424191 : Blo 1607002 5424191 := bstep (se 1 (by rfl) ⟨4068143, by rfl⟩ : syracuseStep 5424191 = 8136287) B8136287
theorem B139453771 : Blo 1607002 139453771 := bstep (se 1 (by rfl) ⟨104590328, by rfl⟩ : syracuseStep 139453771 = 209180657) B209180657
theorem B1607451 : Blo 1607002 1607451 := bstep (se 1 (by rfl) ⟨1205588, by rfl⟩ : syracuseStep 1607451 = 2411177) B2411177
theorem B1607527 : Blo 1607002 1607527 := bstep (se 1 (by rfl) ⟨1205645, by rfl⟩ : syracuseStep 1607527 = 2411291) B2411291
theorem B20596619 : Blo 1607002 20596619 := bstep (se 1 (by rfl) ⟨15447464, by rfl⟩ : syracuseStep 20596619 = 30894929) B30894929
theorem B1607675 : Blo 1607002 1607675 := bstep (se 1 (by rfl) ⟨1205756, by rfl⟩ : syracuseStep 1607675 = 2411513) B2411513
theorem B1608303 : Blo 1607002 1608303 := bstep (se 1 (by rfl) ⟨1206227, by rfl⟩ : syracuseStep 1608303 = 2412455) B2412455
theorem B1608639 : Blo 1607002 1608639 := bstep (se 1 (by rfl) ⟨1206479, by rfl⟩ : syracuseStep 1608639 = 2412959) B2412959
theorem B1608943 : Blo 1607002 1608943 := bstep (se 1 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 1608943 = 2413415) B2413415
theorem B2412137 : Blo 1607002 2412137 := bstep (se 2 (by rfl) ⟨904551, by rfl⟩ : syracuseStep 2412137 = 1809103) B1809103
theorem B8138393 : Blo 1607002 8138393 := bstep (se 2 (by rfl) ⟨3051897, by rfl⟩ : syracuseStep 8138393 = 6103795) B6103795
theorem B1716223 : Blo 1607002 1716223 := bstep (se 1 (by rfl) ⟨1287167, by rfl⟩ : syracuseStep 1716223 = 2574335) B2574335
theorem B53620865 : Blo 1607002 53620865 := bstep (se 2 (by rfl) ⟨20107824, by rfl⟩ : syracuseStep 53620865 = 40215649) B40215649
theorem B2412767 : Blo 1607002 2412767 := bstep (se 1 (by rfl) ⟨1809575, by rfl⟩ : syracuseStep 2412767 = 3619151) B3619151
theorem B2412863 : Blo 1607002 2412863 := bstep (se 1 (by rfl) ⟨1809647, by rfl⟩ : syracuseStep 2412863 = 3619295) B3619295
theorem B6108641 : Blo 1607002 6108641 := bstep (se 2 (by rfl) ⟨2290740, by rfl⟩ : syracuseStep 6108641 = 4581481) B4581481
theorem B3618287 : Blo 1607002 3618287 := bstep (se 1 (by rfl) ⟨2713715, by rfl⟩ : syracuseStep 3618287 = 5427431) B5427431
theorem B11597593 : Blo 1607002 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B83589083 : Blo 1607002 83589083 := bstep (se 1 (by rfl) ⟨62691812, by rfl⟩ : syracuseStep 83589083 = 125383625) B125383625
theorem B10303847 : Blo 1607002 10303847 := bstep (se 1 (by rfl) ⟨7727885, by rfl⟩ : syracuseStep 10303847 = 15455771) B15455771
theorem B7731713 : Blo 1607002 7731713 := bstep (se 2 (by rfl) ⟨2899392, by rfl⟩ : syracuseStep 7731713 = 5798785) B5798785
theorem B571546115 : Blo 1607002 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B3619961 : Blo 1607002 3619961 := bstep (se 2 (by rfl) ⟨1357485, by rfl⟩ : syracuseStep 3619961 = 2714971) B2714971
theorem B4072427 : Blo 1607002 4072427 := bstep (se 1 (by rfl) ⟨3054320, by rfl⟩ : syracuseStep 4072427 = 6108641) B6108641
theorem B13731079 : Blo 1607002 13731079 := bstep (se 1 (by rfl) ⟨10298309, by rfl⟩ : syracuseStep 13731079 = 20596619) B20596619
theorem B5154475 : Blo 1607002 5154475 := bstep (se 1 (by rfl) ⟨3865856, by rfl⟩ : syracuseStep 5154475 = 7731713) B7731713
theorem B1608091 : Blo 1607002 1608091 := bstep (se 1 (by rfl) ⟨1206068, by rfl⟩ : syracuseStep 1608091 = 2412137) B2412137
theorem B5425595 : Blo 1607002 5425595 := bstep (se 1 (by rfl) ⟨4069196, by rfl⟩ : syracuseStep 5425595 = 8138393) B8138393
theorem B2288297 : Blo 1607002 2288297 := bstep (se 2 (by rfl) ⟨858111, by rfl⟩ : syracuseStep 2288297 = 1716223) B1716223
theorem B1608511 : Blo 1607002 1608511 := bstep (se 1 (by rfl) ⟨1206383, by rfl⟩ : syracuseStep 1608511 = 2412767) B2412767
theorem B1608575 : Blo 1607002 1608575 := bstep (se 1 (by rfl) ⟨1206431, by rfl⟩ : syracuseStep 1608575 = 2412863) B2412863
theorem B13741163 : Blo 1607002 13741163 := bstep (se 1 (by rfl) ⟨10305872, by rfl⟩ : syracuseStep 13741163 = 20611745) B20611745
theorem B3616127 : Blo 1607002 3616127 := bstep (se 1 (by rfl) ⟨2712095, by rfl⟩ : syracuseStep 3616127 = 5424191) B5424191
theorem B2412191 : Blo 1607002 2412191 := bstep (se 1 (by rfl) ⟨1809143, by rfl⟩ : syracuseStep 2412191 = 3618287) B3618287
theorem B55726055 : Blo 1607002 55726055 := bstep (se 1 (by rfl) ⟨41794541, by rfl⟩ : syracuseStep 55726055 = 83589083) B83589083
theorem B6869231 : Blo 1607002 6869231 := bstep (se 1 (by rfl) ⟨5151923, by rfl⟩ : syracuseStep 6869231 = 10303847) B10303847
theorem B381030743 : Blo 1607002 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B185938361 : Blo 1607002 185938361 := bstep (se 2 (by rfl) ⟨69726885, by rfl⟩ : syracuseStep 185938361 = 139453771) B139453771
theorem B2413307 : Blo 1607002 2413307 := bstep (se 1 (by rfl) ⟨1809980, by rfl⟩ : syracuseStep 2413307 = 3619961) B3619961
theorem B15463457 : Blo 1607002 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B65975725 : Blo 1607002 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B35747243 : Blo 1607002 35747243 := bstep (se 1 (by rfl) ⟨26810432, by rfl⟩ : syracuseStep 35747243 = 53620865) B53620865
theorem B27858599 : Blo 1607002 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B1808239 : Blo 1607002 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B28628927 : Blo 1607002 28628927 := bstep (se 1 (by rfl) ⟨21471695, by rfl⟩ : syracuseStep 28628927 = 42943391) B42943391
theorem B5150719 : Blo 1607002 5150719 := bstep (se 1 (by rfl) ⟨3863039, by rfl⟩ : syracuseStep 5150719 = 7726079) B7726079
theorem B4579487 : Blo 1607002 4579487 := bstep (se 1 (by rfl) ⟨3434615, by rfl⟩ : syracuseStep 4579487 = 6869231) B6869231
theorem B23831495 : Blo 1607002 23831495 := bstep (se 1 (by rfl) ⟨17873621, by rfl⟩ : syracuseStep 23831495 = 35747243) B35747243
theorem B18572399 : Blo 1607002 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B87967633 : Blo 1607002 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B9160775 : Blo 1607002 9160775 := bstep (se 1 (by rfl) ⟨6870581, by rfl⟩ : syracuseStep 9160775 = 13741163) B13741163
theorem B2410751 : Blo 1607002 2410751 := bstep (se 1 (by rfl) ⟨1808063, by rfl⟩ : syracuseStep 2410751 = 3616127) B3616127
theorem B1608127 : Blo 1607002 1608127 := bstep (se 1 (by rfl) ⟨1206095, by rfl⟩ : syracuseStep 1608127 = 2412191) B2412191
theorem B2410985 : Blo 1607002 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B6867625 : Blo 1607002 6867625 := bstep (se 2 (by rfl) ⟨2575359, by rfl⟩ : syracuseStep 6867625 = 5150719) B5150719
theorem B254020495 : Blo 1607002 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B1608871 : Blo 1607002 1608871 := bstep (se 1 (by rfl) ⟨1206653, by rfl⟩ : syracuseStep 1608871 = 2413307) B2413307
theorem B2714951 : Blo 1607002 2714951 := bstep (se 1 (by rfl) ⟨2036213, by rfl⟩ : syracuseStep 2714951 = 4072427) B4072427
theorem B10308971 : Blo 1607002 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B3617063 : Blo 1607002 3617063 := bstep (se 1 (by rfl) ⟨2712797, by rfl⟩ : syracuseStep 3617063 = 5425595) B5425595
theorem B123958907 : Blo 1607002 123958907 := bstep (se 1 (by rfl) ⟨92969180, by rfl⟩ : syracuseStep 123958907 = 185938361) B185938361
theorem B19085951 : Blo 1607002 19085951 := bstep (se 1 (by rfl) ⟨14314463, by rfl⟩ : syracuseStep 19085951 = 28628927) B28628927
theorem B18308105 : Blo 1607002 18308105 := bstep (se 2 (by rfl) ⟨6865539, by rfl⟩ : syracuseStep 18308105 = 13731079) B13731079
theorem B6102125 : Blo 1607002 6102125 := bstep (se 3 (by rfl) ⟨1144148, by rfl⟩ : syracuseStep 6102125 = 2288297) B2288297
theorem B6872633 : Blo 1607002 6872633 := bstep (se 2 (by rfl) ⟨2577237, by rfl⟩ : syracuseStep 6872633 = 5154475) B5154475
theorem B37150703 : Blo 1607002 37150703 := bstep (se 1 (by rfl) ⟨27863027, by rfl⟩ : syracuseStep 37150703 = 55726055) B55726055
theorem B1607167 : Blo 1607002 1607167 := bstep (se 1 (by rfl) ⟨1205375, by rfl⟩ : syracuseStep 1607167 = 2410751) B2410751
theorem B1607323 : Blo 1607002 1607323 := bstep (se 1 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 1607323 = 2410985) B2410985
theorem B12723967 : Blo 1607002 12723967 := bstep (se 1 (by rfl) ⟨9542975, by rfl⟩ : syracuseStep 12723967 = 19085951) B19085951
theorem B4581755 : Blo 1607002 4581755 := bstep (se 1 (by rfl) ⟨3436316, by rfl⟩ : syracuseStep 4581755 = 6872633) B6872633
theorem B24767135 : Blo 1607002 24767135 := bstep (se 1 (by rfl) ⟨18575351, by rfl⟩ : syracuseStep 24767135 = 37150703) B37150703
theorem B2411375 : Blo 1607002 2411375 := bstep (se 1 (by rfl) ⟨1808531, by rfl⟩ : syracuseStep 2411375 = 3617063) B3617063
theorem B15887663 : Blo 1607002 15887663 := bstep (se 1 (by rfl) ⟨11915747, by rfl⟩ : syracuseStep 15887663 = 23831495) B23831495
theorem B12381599 : Blo 1607002 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B338693993 : Blo 1607002 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B6107183 : Blo 1607002 6107183 := bstep (se 1 (by rfl) ⟨4580387, by rfl⟩ : syracuseStep 6107183 = 9160775) B9160775
theorem B4068083 : Blo 1607002 4068083 := bstep (se 1 (by rfl) ⟨3051062, by rfl⟩ : syracuseStep 4068083 = 6102125) B6102125
theorem B117290177 : Blo 1607002 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B3052991 : Blo 1607002 3052991 := bstep (se 1 (by rfl) ⟨2289743, by rfl⟩ : syracuseStep 3052991 = 4579487) B4579487
theorem B9156833 : Blo 1607002 9156833 := bstep (se 2 (by rfl) ⟨3433812, by rfl⟩ : syracuseStep 9156833 = 6867625) B6867625
theorem B27490589 : Blo 1607002 27490589 := bstep (se 3 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 27490589 = 10308971) B10308971
theorem B82639271 : Blo 1607002 82639271 := bstep (se 1 (by rfl) ⟨61979453, by rfl⟩ : syracuseStep 82639271 = 123958907) B123958907
theorem B12205403 : Blo 1607002 12205403 := bstep (se 1 (by rfl) ⟨9154052, by rfl⟩ : syracuseStep 12205403 = 18308105) B18308105
theorem B1809967 : Blo 1607002 1809967 := bstep (se 1 (by rfl) ⟨1357475, by rfl⟩ : syracuseStep 1809967 = 2714951) B2714951
theorem B4071455 : Blo 1607002 4071455 := bstep (se 1 (by rfl) ⟨3053591, by rfl⟩ : syracuseStep 4071455 = 6107183) B6107183
theorem B2712055 : Blo 1607002 2712055 := bstep (se 1 (by rfl) ⟨2034041, by rfl⟩ : syracuseStep 2712055 = 4068083) B4068083
theorem B78193451 : Blo 1607002 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B6104555 : Blo 1607002 6104555 := bstep (se 1 (by rfl) ⟨4578416, by rfl⟩ : syracuseStep 6104555 = 9156833) B9156833
theorem B18327059 : Blo 1607002 18327059 := bstep (se 1 (by rfl) ⟨13745294, by rfl⟩ : syracuseStep 18327059 = 27490589) B27490589
theorem B55092847 : Blo 1607002 55092847 := bstep (se 1 (by rfl) ⟨41319635, by rfl⟩ : syracuseStep 55092847 = 82639271) B82639271
theorem B1607583 : Blo 1607002 1607583 := bstep (se 1 (by rfl) ⟨1205687, by rfl⟩ : syracuseStep 1607583 = 2411375) B2411375
theorem B8136935 : Blo 1607002 8136935 := bstep (se 1 (by rfl) ⟨6102701, by rfl⟩ : syracuseStep 8136935 = 12205403) B12205403
theorem B16511423 : Blo 1607002 16511423 := bstep (se 1 (by rfl) ⟨12383567, by rfl⟩ : syracuseStep 16511423 = 24767135) B24767135
theorem B2413289 : Blo 1607002 2413289 := bstep (se 2 (by rfl) ⟨904983, by rfl⟩ : syracuseStep 2413289 = 1809967) B1809967
theorem B8254399 : Blo 1607002 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B8141309 : Blo 1607002 8141309 := bstep (se 3 (by rfl) ⟨1526495, by rfl⟩ : syracuseStep 8141309 = 3052991) B3052991
theorem B3054503 : Blo 1607002 3054503 := bstep (se 1 (by rfl) ⟨2290877, by rfl⟩ : syracuseStep 3054503 = 4581755) B4581755
theorem B10591775 : Blo 1607002 10591775 := bstep (se 1 (by rfl) ⟨7943831, by rfl⟩ : syracuseStep 10591775 = 15887663) B15887663
theorem B16965289 : Blo 1607002 16965289 := bstep (se 2 (by rfl) ⟨6361983, by rfl⟩ : syracuseStep 16965289 = 12723967) B12723967
theorem B225795995 : Blo 1607002 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B5424623 : Blo 1607002 5424623 := bstep (se 1 (by rfl) ⟨4068467, by rfl⟩ : syracuseStep 5424623 = 8136935) B8136935
theorem B22620385 : Blo 1607002 22620385 := bstep (se 2 (by rfl) ⟨8482644, by rfl⟩ : syracuseStep 22620385 = 16965289) B16965289
theorem B150530663 : Blo 1607002 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B2714303 : Blo 1607002 2714303 := bstep (se 1 (by rfl) ⟨2035727, by rfl⟩ : syracuseStep 2714303 = 4071455) B4071455
theorem B1608859 : Blo 1607002 1608859 := bstep (se 1 (by rfl) ⟨1206644, by rfl⟩ : syracuseStep 1608859 = 2413289) B2413289
theorem B52128967 : Blo 1607002 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B3616073 : Blo 1607002 3616073 := bstep (se 2 (by rfl) ⟨1356027, by rfl⟩ : syracuseStep 3616073 = 2712055) B2712055
theorem B12218039 : Blo 1607002 12218039 := bstep (se 1 (by rfl) ⟨9163529, by rfl⟩ : syracuseStep 12218039 = 18327059) B18327059
theorem B11005865 : Blo 1607002 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B5427539 : Blo 1607002 5427539 := bstep (se 1 (by rfl) ⟨4070654, by rfl⟩ : syracuseStep 5427539 = 8141309) B8141309
theorem B2036335 : Blo 1607002 2036335 := bstep (se 1 (by rfl) ⟨1527251, by rfl⟩ : syracuseStep 2036335 = 3054503) B3054503
theorem B4069703 : Blo 1607002 4069703 := bstep (se 1 (by rfl) ⟨3052277, by rfl⟩ : syracuseStep 4069703 = 6104555) B6104555
theorem B44030461 : Blo 1607002 44030461 := bstep (se 3 (by rfl) ⟨8255711, by rfl⟩ : syracuseStep 44030461 = 16511423) B16511423
theorem B73457129 : Blo 1607002 73457129 := bstep (se 2 (by rfl) ⟨27546423, by rfl⟩ : syracuseStep 73457129 = 55092847) B55092847
theorem B7061183 : Blo 1607002 7061183 := bstep (se 1 (by rfl) ⟨5295887, by rfl⟩ : syracuseStep 7061183 = 10591775) B10591775
theorem B2713135 : Blo 1607002 2713135 := bstep (se 1 (by rfl) ⟨2034851, by rfl⟩ : syracuseStep 2713135 = 4069703) B4069703
theorem B3134170837 : Blo 1607002 3134170837 := bstep (se 7 (by rfl) ⟨36728564, by rfl⟩ : syracuseStep 3134170837 = 73457129) B73457129
theorem B2410715 : Blo 1607002 2410715 := bstep (se 1 (by rfl) ⟨1808036, by rfl⟩ : syracuseStep 2410715 = 3616073) B3616073
theorem B8145359 : Blo 1607002 8145359 := bstep (se 1 (by rfl) ⟨6109019, by rfl⟩ : syracuseStep 8145359 = 12218039) B12218039
theorem B58707281 : Blo 1607002 58707281 := bstep (se 2 (by rfl) ⟨22015230, by rfl⟩ : syracuseStep 58707281 = 44030461) B44030461
theorem B2715113 : Blo 1607002 2715113 := bstep (se 2 (by rfl) ⟨1018167, by rfl⟩ : syracuseStep 2715113 = 2036335) B2036335
theorem B3616415 : Blo 1607002 3616415 := bstep (se 1 (by rfl) ⟨2712311, by rfl⟩ : syracuseStep 3616415 = 5424623) B5424623
theorem B69505289 : Blo 1607002 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B4707455 : Blo 1607002 4707455 := bstep (se 1 (by rfl) ⟨3530591, by rfl⟩ : syracuseStep 4707455 = 7061183) B7061183
theorem B7337243 : Blo 1607002 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B3618359 : Blo 1607002 3618359 := bstep (se 1 (by rfl) ⟨2713769, by rfl⟩ : syracuseStep 3618359 = 5427539) B5427539
theorem B30160513 : Blo 1607002 30160513 := bstep (se 2 (by rfl) ⟨11310192, by rfl⟩ : syracuseStep 30160513 = 22620385) B22620385
theorem B401415101 : Blo 1607002 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B1809535 : Blo 1607002 1809535 := bstep (se 1 (by rfl) ⟨1357151, by rfl⟩ : syracuseStep 1809535 = 2714303) B2714303
theorem B1607143 : Blo 1607002 1607143 := bstep (se 1 (by rfl) ⟨1205357, by rfl⟩ : syracuseStep 1607143 = 2410715) B2410715
theorem B267610067 : Blo 1607002 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B2410943 : Blo 1607002 2410943 := bstep (se 1 (by rfl) ⟨1808207, by rfl⟩ : syracuseStep 2410943 = 3616415) B3616415
theorem B46336859 : Blo 1607002 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B12553213 : Blo 1607002 12553213 := bstep (se 3 (by rfl) ⟨2353727, by rfl⟩ : syracuseStep 12553213 = 4707455) B4707455
theorem B19565981 : Blo 1607002 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B2412239 : Blo 1607002 2412239 := bstep (se 1 (by rfl) ⟨1809179, by rfl⟩ : syracuseStep 2412239 = 3618359) B3618359
theorem B2412713 : Blo 1607002 2412713 := bstep (se 2 (by rfl) ⟨904767, by rfl⟩ : syracuseStep 2412713 = 1809535) B1809535
theorem B3617513 : Blo 1607002 3617513 := bstep (se 2 (by rfl) ⟨1356567, by rfl⟩ : syracuseStep 3617513 = 2713135) B2713135
theorem B39138187 : Blo 1607002 39138187 := bstep (se 1 (by rfl) ⟨29353640, by rfl⟩ : syracuseStep 39138187 = 58707281) B58707281
theorem B5430239 : Blo 1607002 5430239 := bstep (se 1 (by rfl) ⟨4072679, by rfl⟩ : syracuseStep 5430239 = 8145359) B8145359
theorem B40214017 : Blo 1607002 40214017 := bstep (se 2 (by rfl) ⟨15080256, by rfl⟩ : syracuseStep 40214017 = 30160513) B30160513
theorem B4178894449 : Blo 1607002 4178894449 := bstep (se 2 (by rfl) ⟨1567085418, by rfl⟩ : syracuseStep 4178894449 = 3134170837) B3134170837
theorem B1810075 : Blo 1607002 1810075 := bstep (se 1 (by rfl) ⟨1357556, by rfl⟩ : syracuseStep 1810075 = 2715113) B2715113
theorem B52184249 : Blo 1607002 52184249 := bstep (se 2 (by rfl) ⟨19569093, by rfl⟩ : syracuseStep 52184249 = 39138187) B39138187
theorem B178406711 : Blo 1607002 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B16737617 : Blo 1607002 16737617 := bstep (se 2 (by rfl) ⟨6276606, by rfl⟩ : syracuseStep 16737617 = 12553213) B12553213
theorem B1607295 : Blo 1607002 1607295 := bstep (se 1 (by rfl) ⟨1205471, by rfl⟩ : syracuseStep 1607295 = 2410943) B2410943
theorem B53618689 : Blo 1607002 53618689 := bstep (se 2 (by rfl) ⟨20107008, by rfl⟩ : syracuseStep 53618689 = 40214017) B40214017
theorem B13043987 : Blo 1607002 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B1608159 : Blo 1607002 1608159 := bstep (se 1 (by rfl) ⟨1206119, by rfl⟩ : syracuseStep 1608159 = 2412239) B2412239
theorem B1608475 : Blo 1607002 1608475 := bstep (se 1 (by rfl) ⟨1206356, by rfl⟩ : syracuseStep 1608475 = 2412713) B2412713
theorem B2411675 : Blo 1607002 2411675 := bstep (se 1 (by rfl) ⟨1808756, by rfl⟩ : syracuseStep 2411675 = 3617513) B3617513
theorem B5571859265 : Blo 1607002 5571859265 := bstep (se 2 (by rfl) ⟨2089447224, by rfl⟩ : syracuseStep 5571859265 = 4178894449) B4178894449
theorem B2413433 : Blo 1607002 2413433 := bstep (se 2 (by rfl) ⟨905037, by rfl⟩ : syracuseStep 2413433 = 1810075) B1810075
theorem B30891239 : Blo 1607002 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B3620159 : Blo 1607002 3620159 := bstep (se 1 (by rfl) ⟨2715119, by rfl⟩ : syracuseStep 3620159 = 5430239) B5430239
theorem B71491585 : Blo 1607002 71491585 := bstep (se 2 (by rfl) ⟨26809344, by rfl⟩ : syracuseStep 71491585 = 53618689) B53618689
theorem B3714572843 : Blo 1607002 3714572843 := bstep (se 1 (by rfl) ⟨2785929632, by rfl⟩ : syracuseStep 3714572843 = 5571859265) B5571859265
theorem B11158411 : Blo 1607002 11158411 := bstep (se 1 (by rfl) ⟨8368808, by rfl⟩ : syracuseStep 11158411 = 16737617) B16737617
theorem B1607783 : Blo 1607002 1607783 := bstep (se 1 (by rfl) ⟨1205837, by rfl⟩ : syracuseStep 1607783 = 2411675) B2411675
theorem B1608955 : Blo 1607002 1608955 := bstep (se 1 (by rfl) ⟨1206716, by rfl⟩ : syracuseStep 1608955 = 2413433) B2413433
theorem B8695991 : Blo 1607002 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B2413439 : Blo 1607002 2413439 := bstep (se 1 (by rfl) ⟨1810079, by rfl⟩ : syracuseStep 2413439 = 3620159) B3620159
theorem B34789499 : Blo 1607002 34789499 := bstep (se 1 (by rfl) ⟨26092124, by rfl⟩ : syracuseStep 34789499 = 52184249) B52184249
theorem B118937807 : Blo 1607002 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B20594159 : Blo 1607002 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B95322113 : Blo 1607002 95322113 := bstep (se 2 (by rfl) ⟨35745792, by rfl⟩ : syracuseStep 95322113 = 71491585) B71491585
theorem B14877881 : Blo 1607002 14877881 := bstep (se 2 (by rfl) ⟨5579205, by rfl⟩ : syracuseStep 14877881 = 11158411) B11158411
theorem B23192999 : Blo 1607002 23192999 := bstep (se 1 (by rfl) ⟨17394749, by rfl⟩ : syracuseStep 23192999 = 34789499) B34789499
theorem B79291871 : Blo 1607002 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B1608959 : Blo 1607002 1608959 := bstep (se 1 (by rfl) ⟨1206719, by rfl⟩ : syracuseStep 1608959 = 2413439) B2413439
theorem B5797327 : Blo 1607002 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B2476381895 : Blo 1607002 2476381895 := bstep (se 1 (by rfl) ⟨1857286421, by rfl⟩ : syracuseStep 2476381895 = 3714572843) B3714572843
theorem B13729439 : Blo 1607002 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B9152959 : Blo 1607002 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B63548075 : Blo 1607002 63548075 := bstep (se 1 (by rfl) ⟨47661056, by rfl⟩ : syracuseStep 63548075 = 95322113) B95322113
theorem B15461999 : Blo 1607002 15461999 := bstep (se 1 (by rfl) ⟨11596499, by rfl⟩ : syracuseStep 15461999 = 23192999) B23192999
theorem B1650921263 : Blo 1607002 1650921263 := bstep (se 1 (by rfl) ⟨1238190947, by rfl⟩ : syracuseStep 1650921263 = 2476381895) B2476381895
theorem B7729769 : Blo 1607002 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B9918587 : Blo 1607002 9918587 := bstep (se 1 (by rfl) ⟨7438940, by rfl⟩ : syracuseStep 9918587 = 14877881) B14877881
theorem B52861247 : Blo 1607002 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B6612391 : Blo 1607002 6612391 := bstep (se 1 (by rfl) ⟨4959293, by rfl⟩ : syracuseStep 6612391 = 9918587) B9918587
theorem B20612717 : Blo 1607002 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B169461533 : Blo 1607002 169461533 := bstep (se 3 (by rfl) ⟨31774037, by rfl⟩ : syracuseStep 169461533 = 63548075) B63548075
theorem B10307999 : Blo 1607002 10307999 := bstep (se 1 (by rfl) ⟨7730999, by rfl⟩ : syracuseStep 10307999 = 15461999) B15461999
theorem B1100614175 : Blo 1607002 1100614175 := bstep (se 1 (by rfl) ⟨825460631, by rfl⟩ : syracuseStep 1100614175 = 1650921263) B1650921263
theorem B12203945 : Blo 1607002 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B35240831 : Blo 1607002 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B8135963 : Blo 1607002 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B733742783 : Blo 1607002 733742783 := bstep (se 1 (by rfl) ⟨550307087, by rfl⟩ : syracuseStep 733742783 = 1100614175) B1100614175
theorem B8816521 : Blo 1607002 8816521 := bstep (se 2 (by rfl) ⟨3306195, by rfl⟩ : syracuseStep 8816521 = 6612391) B6612391
theorem B13741811 : Blo 1607002 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B112974355 : Blo 1607002 112974355 := bstep (se 1 (by rfl) ⟨84730766, by rfl⟩ : syracuseStep 112974355 = 169461533) B169461533
theorem B6871999 : Blo 1607002 6871999 := bstep (se 1 (by rfl) ⟨5153999, by rfl⟩ : syracuseStep 6871999 = 10307999) B10307999
theorem B23493887 : Blo 1607002 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B5423975 : Blo 1607002 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B489161855 : Blo 1607002 489161855 := bstep (se 1 (by rfl) ⟨366871391, by rfl⟩ : syracuseStep 489161855 = 733742783) B733742783
theorem B9161207 : Blo 1607002 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B9162665 : Blo 1607002 9162665 := bstep (se 2 (by rfl) ⟨3435999, by rfl⟩ : syracuseStep 9162665 = 6871999) B6871999
theorem B150632473 : Blo 1607002 150632473 := bstep (se 2 (by rfl) ⟨56487177, by rfl⟩ : syracuseStep 150632473 = 112974355) B112974355
theorem B15662591 : Blo 1607002 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B11755361 : Blo 1607002 11755361 := bstep (se 2 (by rfl) ⟨4408260, by rfl⟩ : syracuseStep 11755361 = 8816521) B8816521
theorem B200843297 : Blo 1607002 200843297 := bstep (se 2 (by rfl) ⟨75316236, by rfl⟩ : syracuseStep 200843297 = 150632473) B150632473
theorem B326107903 : Blo 1607002 326107903 := bstep (se 1 (by rfl) ⟨244580927, by rfl⟩ : syracuseStep 326107903 = 489161855) B489161855
theorem B3615983 : Blo 1607002 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B6107471 : Blo 1607002 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B10441727 : Blo 1607002 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B7836907 : Blo 1607002 7836907 := bstep (se 1 (by rfl) ⟨5877680, by rfl⟩ : syracuseStep 7836907 = 11755361) B11755361
theorem B6108443 : Blo 1607002 6108443 := bstep (se 1 (by rfl) ⟨4581332, by rfl⟩ : syracuseStep 6108443 = 9162665) B9162665
theorem B4071647 : Blo 1607002 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B4072295 : Blo 1607002 4072295 := bstep (se 1 (by rfl) ⟨3054221, by rfl⟩ : syracuseStep 4072295 = 6108443) B6108443
theorem B2410655 : Blo 1607002 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B434810537 : Blo 1607002 434810537 := bstep (se 2 (by rfl) ⟨163053951, by rfl⟩ : syracuseStep 434810537 = 326107903) B326107903
theorem B10449209 : Blo 1607002 10449209 := bstep (se 2 (by rfl) ⟨3918453, by rfl⟩ : syracuseStep 10449209 = 7836907) B7836907
theorem B133895531 : Blo 1607002 133895531 := bstep (se 1 (by rfl) ⟨100421648, by rfl⟩ : syracuseStep 133895531 = 200843297) B200843297
theorem B6961151 : Blo 1607002 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B1607103 : Blo 1607002 1607103 := bstep (se 1 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 1607103 = 2410655) B2410655
theorem B2714431 : Blo 1607002 2714431 := bstep (se 1 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 2714431 = 4071647) B4071647
theorem B2714863 : Blo 1607002 2714863 := bstep (se 1 (by rfl) ⟨2036147, by rfl⟩ : syracuseStep 2714863 = 4072295) B4072295
theorem B27864557 : Blo 1607002 27864557 := bstep (se 3 (by rfl) ⟨5224604, by rfl⟩ : syracuseStep 27864557 = 10449209) B10449209
theorem B89263687 : Blo 1607002 89263687 := bstep (se 1 (by rfl) ⟨66947765, by rfl⟩ : syracuseStep 89263687 = 133895531) B133895531
theorem B289873691 : Blo 1607002 289873691 := bstep (se 1 (by rfl) ⟨217405268, by rfl⟩ : syracuseStep 289873691 = 434810537) B434810537
theorem B18563069 : Blo 1607002 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B119018249 : Blo 1607002 119018249 := bstep (se 2 (by rfl) ⟨44631843, by rfl⟩ : syracuseStep 119018249 = 89263687) B89263687
theorem B18576371 : Blo 1607002 18576371 := bstep (se 1 (by rfl) ⟨13932278, by rfl⟩ : syracuseStep 18576371 = 27864557) B27864557
theorem B12375379 : Blo 1607002 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B3619241 : Blo 1607002 3619241 := bstep (se 2 (by rfl) ⟨1357215, by rfl⟩ : syracuseStep 3619241 = 2714431) B2714431
theorem B3619817 : Blo 1607002 3619817 := bstep (se 2 (by rfl) ⟨1357431, by rfl⟩ : syracuseStep 3619817 = 2714863) B2714863
theorem B193249127 : Blo 1607002 193249127 := bstep (se 1 (by rfl) ⟨144936845, by rfl⟩ : syracuseStep 193249127 = 289873691) B289873691
theorem B16500505 : Blo 1607002 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B2412827 : Blo 1607002 2412827 := bstep (se 1 (by rfl) ⟨1809620, by rfl⟩ : syracuseStep 2412827 = 3619241) B3619241
theorem B2413211 : Blo 1607002 2413211 := bstep (se 1 (by rfl) ⟨1809908, by rfl⟩ : syracuseStep 2413211 = 3619817) B3619817
theorem B128832751 : Blo 1607002 128832751 := bstep (se 1 (by rfl) ⟨96624563, by rfl⟩ : syracuseStep 128832751 = 193249127) B193249127
theorem B79345499 : Blo 1607002 79345499 := bstep (se 1 (by rfl) ⟨59509124, by rfl⟩ : syracuseStep 79345499 = 119018249) B119018249
theorem B12384247 : Blo 1607002 12384247 := bstep (se 1 (by rfl) ⟨9288185, by rfl⟩ : syracuseStep 12384247 = 18576371) B18576371
theorem B1608551 : Blo 1607002 1608551 := bstep (se 1 (by rfl) ⟨1206413, by rfl⟩ : syracuseStep 1608551 = 2412827) B2412827
theorem B1608807 : Blo 1607002 1608807 := bstep (se 1 (by rfl) ⟨1206605, by rfl⟩ : syracuseStep 1608807 = 2413211) B2413211
theorem B687108005 : Blo 1607002 687108005 := bstep (se 4 (by rfl) ⟨64416375, by rfl⟩ : syracuseStep 687108005 = 128832751) B128832751
theorem B211587997 : Blo 1607002 211587997 := bstep (se 3 (by rfl) ⟨39672749, by rfl⟩ : syracuseStep 211587997 = 79345499) B79345499
theorem B22000673 : Blo 1607002 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B16512329 : Blo 1607002 16512329 := bstep (se 2 (by rfl) ⟨6192123, by rfl⟩ : syracuseStep 16512329 = 12384247) B12384247
theorem B282117329 : Blo 1607002 282117329 := bstep (se 2 (by rfl) ⟨105793998, by rfl⟩ : syracuseStep 282117329 = 211587997) B211587997
theorem B58668461 : Blo 1607002 58668461 := bstep (se 3 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 58668461 = 22000673) B22000673
theorem B11008219 : Blo 1607002 11008219 := bstep (se 1 (by rfl) ⟨8256164, by rfl⟩ : syracuseStep 11008219 = 16512329) B16512329
theorem B458072003 : Blo 1607002 458072003 := bstep (se 1 (by rfl) ⟨343554002, by rfl⟩ : syracuseStep 458072003 = 687108005) B687108005
theorem B39112307 : Blo 1607002 39112307 := bstep (se 1 (by rfl) ⟨29334230, by rfl⟩ : syracuseStep 39112307 = 58668461) B58668461
theorem B14677625 : Blo 1607002 14677625 := bstep (se 2 (by rfl) ⟨5504109, by rfl⟩ : syracuseStep 14677625 = 11008219) B11008219
theorem B188078219 : Blo 1607002 188078219 := bstep (se 1 (by rfl) ⟨141058664, by rfl⟩ : syracuseStep 188078219 = 282117329) B282117329
theorem B305381335 : Blo 1607002 305381335 := bstep (se 1 (by rfl) ⟨229036001, by rfl⟩ : syracuseStep 305381335 = 458072003) B458072003
theorem B9785083 : Blo 1607002 9785083 := bstep (se 1 (by rfl) ⟨7338812, by rfl⟩ : syracuseStep 9785083 = 14677625) B14677625
theorem B125385479 : Blo 1607002 125385479 := bstep (se 1 (by rfl) ⟨94039109, by rfl⟩ : syracuseStep 125385479 = 188078219) B188078219
theorem B26074871 : Blo 1607002 26074871 := bstep (se 1 (by rfl) ⟨19556153, by rfl⟩ : syracuseStep 26074871 = 39112307) B39112307
theorem B407175113 : Blo 1607002 407175113 := bstep (se 2 (by rfl) ⟨152690667, by rfl⟩ : syracuseStep 407175113 = 305381335) B305381335
theorem B13046777 : Blo 1607002 13046777 := bstep (se 2 (by rfl) ⟨4892541, by rfl⟩ : syracuseStep 13046777 = 9785083) B9785083
theorem B83590319 : Blo 1607002 83590319 := bstep (se 1 (by rfl) ⟨62692739, by rfl⟩ : syracuseStep 83590319 = 125385479) B125385479
theorem B17383247 : Blo 1607002 17383247 := bstep (se 1 (by rfl) ⟨13037435, by rfl⟩ : syracuseStep 17383247 = 26074871) B26074871
theorem B271450075 : Blo 1607002 271450075 := bstep (se 1 (by rfl) ⟨203587556, by rfl⟩ : syracuseStep 271450075 = 407175113) B407175113
theorem B361933433 : Blo 1607002 361933433 := bstep (se 2 (by rfl) ⟨135725037, by rfl⟩ : syracuseStep 361933433 = 271450075) B271450075
theorem B55726879 : Blo 1607002 55726879 := bstep (se 1 (by rfl) ⟨41795159, by rfl⟩ : syracuseStep 55726879 = 83590319) B83590319
theorem B11588831 : Blo 1607002 11588831 := bstep (se 1 (by rfl) ⟨8691623, by rfl⟩ : syracuseStep 11588831 = 17383247) B17383247
theorem B8697851 : Blo 1607002 8697851 := bstep (se 1 (by rfl) ⟨6523388, by rfl⟩ : syracuseStep 8697851 = 13046777) B13046777
theorem B7725887 : Blo 1607002 7725887 := bstep (se 1 (by rfl) ⟨5794415, by rfl⟩ : syracuseStep 7725887 = 11588831) B11588831
theorem B74302505 : Blo 1607002 74302505 := bstep (se 2 (by rfl) ⟨27863439, by rfl⟩ : syracuseStep 74302505 = 55726879) B55726879
theorem B241288955 : Blo 1607002 241288955 := bstep (se 1 (by rfl) ⟨180966716, by rfl⟩ : syracuseStep 241288955 = 361933433) B361933433
theorem B5798567 : Blo 1607002 5798567 := bstep (se 1 (by rfl) ⟨4348925, by rfl⟩ : syracuseStep 5798567 = 8697851) B8697851
theorem B160859303 : Blo 1607002 160859303 := bstep (se 1 (by rfl) ⟨120644477, by rfl⟩ : syracuseStep 160859303 = 241288955) B241288955
theorem B5150591 : Blo 1607002 5150591 := bstep (se 1 (by rfl) ⟨3862943, by rfl⟩ : syracuseStep 5150591 = 7725887) B7725887
theorem B49535003 : Blo 1607002 49535003 := bstep (se 1 (by rfl) ⟨37151252, by rfl⟩ : syracuseStep 49535003 = 74302505) B74302505
theorem B3865711 : Blo 1607002 3865711 := bstep (se 1 (by rfl) ⟨2899283, by rfl⟩ : syracuseStep 3865711 = 5798567) B5798567
theorem B3433727 : Blo 1607002 3433727 := bstep (se 1 (by rfl) ⟨2575295, by rfl⟩ : syracuseStep 3433727 = 5150591) B5150591
theorem B33023335 : Blo 1607002 33023335 := bstep (se 1 (by rfl) ⟨24767501, by rfl⟩ : syracuseStep 33023335 = 49535003) B49535003
theorem B5154281 : Blo 1607002 5154281 := bstep (se 2 (by rfl) ⟨1932855, by rfl⟩ : syracuseStep 5154281 = 3865711) B3865711
theorem B107239535 : Blo 1607002 107239535 := bstep (se 1 (by rfl) ⟨80429651, by rfl⟩ : syracuseStep 107239535 = 160859303) B160859303
theorem B71493023 : Blo 1607002 71493023 := bstep (se 1 (by rfl) ⟨53619767, by rfl⟩ : syracuseStep 71493023 = 107239535) B107239535
theorem B2289151 : Blo 1607002 2289151 := bstep (se 1 (by rfl) ⟨1716863, by rfl⟩ : syracuseStep 2289151 = 3433727) B3433727
theorem B3436187 : Blo 1607002 3436187 := bstep (se 1 (by rfl) ⟨2577140, by rfl⟩ : syracuseStep 3436187 = 5154281) B5154281
theorem B44031113 : Blo 1607002 44031113 := bstep (se 2 (by rfl) ⟨16511667, by rfl⟩ : syracuseStep 44031113 = 33023335) B33023335
theorem B47662015 : Blo 1607002 47662015 := bstep (se 1 (by rfl) ⟨35746511, by rfl⟩ : syracuseStep 47662015 = 71493023) B71493023
theorem B29354075 : Blo 1607002 29354075 := bstep (se 1 (by rfl) ⟨22015556, by rfl⟩ : syracuseStep 29354075 = 44031113) B44031113
theorem B12208805 : Blo 1607002 12208805 := bstep (se 4 (by rfl) ⟨1144575, by rfl⟩ : syracuseStep 12208805 = 2289151) B2289151
theorem B9163165 : Blo 1607002 9163165 := bstep (se 3 (by rfl) ⟨1718093, by rfl⟩ : syracuseStep 9163165 = 3436187) B3436187
theorem B12217553 : Blo 1607002 12217553 := bstep (se 2 (by rfl) ⟨4581582, by rfl⟩ : syracuseStep 12217553 = 9163165) B9163165
theorem B63549353 : Blo 1607002 63549353 := bstep (se 2 (by rfl) ⟨23831007, by rfl⟩ : syracuseStep 63549353 = 47662015) B47662015
theorem B8139203 : Blo 1607002 8139203 := bstep (se 1 (by rfl) ⟨6104402, by rfl⟩ : syracuseStep 8139203 = 12208805) B12208805
theorem B19569383 : Blo 1607002 19569383 := bstep (se 1 (by rfl) ⟨14677037, by rfl⟩ : syracuseStep 19569383 = 29354075) B29354075
theorem B8145035 : Blo 1607002 8145035 := bstep (se 1 (by rfl) ⟨6108776, by rfl⟩ : syracuseStep 8145035 = 12217553) B12217553
theorem B5426135 : Blo 1607002 5426135 := bstep (se 1 (by rfl) ⟨4069601, by rfl⟩ : syracuseStep 5426135 = 8139203) B8139203
theorem B13046255 : Blo 1607002 13046255 := bstep (se 1 (by rfl) ⟨9784691, by rfl⟩ : syracuseStep 13046255 = 19569383) B19569383
theorem B42366235 : Blo 1607002 42366235 := bstep (se 1 (by rfl) ⟨31774676, by rfl⟩ : syracuseStep 42366235 = 63549353) B63549353
theorem B56488313 : Blo 1607002 56488313 := bstep (se 2 (by rfl) ⟨21183117, by rfl⟩ : syracuseStep 56488313 = 42366235) B42366235
theorem B3617423 : Blo 1607002 3617423 := bstep (se 1 (by rfl) ⟨2713067, by rfl⟩ : syracuseStep 3617423 = 5426135) B5426135
theorem B8697503 : Blo 1607002 8697503 := bstep (se 1 (by rfl) ⟨6523127, by rfl⟩ : syracuseStep 8697503 = 13046255) B13046255
theorem B5430023 : Blo 1607002 5430023 := bstep (se 1 (by rfl) ⟨4072517, by rfl⟩ : syracuseStep 5430023 = 8145035) B8145035
theorem B37658875 : Blo 1607002 37658875 := bstep (se 1 (by rfl) ⟨28244156, by rfl⟩ : syracuseStep 37658875 = 56488313) B56488313
theorem B23193341 : Blo 1607002 23193341 := bstep (se 3 (by rfl) ⟨4348751, by rfl⟩ : syracuseStep 23193341 = 8697503) B8697503
theorem B2411615 : Blo 1607002 2411615 := bstep (se 1 (by rfl) ⟨1808711, by rfl⟩ : syracuseStep 2411615 = 3617423) B3617423
theorem B3620015 : Blo 1607002 3620015 := bstep (se 1 (by rfl) ⟨2715011, by rfl⟩ : syracuseStep 3620015 = 5430023) B5430023
theorem B1607743 : Blo 1607002 1607743 := bstep (se 1 (by rfl) ⟨1205807, by rfl⟩ : syracuseStep 1607743 = 2411615) B2411615
theorem B50211833 : Blo 1607002 50211833 := bstep (se 2 (by rfl) ⟨18829437, by rfl⟩ : syracuseStep 50211833 = 37658875) B37658875
theorem B15462227 : Blo 1607002 15462227 := bstep (se 1 (by rfl) ⟨11596670, by rfl⟩ : syracuseStep 15462227 = 23193341) B23193341
theorem B2413343 : Blo 1607002 2413343 := bstep (se 1 (by rfl) ⟨1810007, by rfl⟩ : syracuseStep 2413343 = 3620015) B3620015
theorem B10308151 : Blo 1607002 10308151 := bstep (se 1 (by rfl) ⟨7731113, by rfl⟩ : syracuseStep 10308151 = 15462227) B15462227
theorem B1608895 : Blo 1607002 1608895 := bstep (se 1 (by rfl) ⟨1206671, by rfl⟩ : syracuseStep 1608895 = 2413343) B2413343
theorem B133898221 : Blo 1607002 133898221 := bstep (se 3 (by rfl) ⟨25105916, by rfl⟩ : syracuseStep 133898221 = 50211833) B50211833
theorem B178530961 : Blo 1607002 178530961 := bstep (se 2 (by rfl) ⟨66949110, by rfl⟩ : syracuseStep 178530961 = 133898221) B133898221
theorem B13744201 : Blo 1607002 13744201 := bstep (se 2 (by rfl) ⟨5154075, by rfl⟩ : syracuseStep 13744201 = 10308151) B10308151
theorem B18325601 : Blo 1607002 18325601 := bstep (se 2 (by rfl) ⟨6872100, by rfl⟩ : syracuseStep 18325601 = 13744201) B13744201
theorem B238041281 : Blo 1607002 238041281 := bstep (se 2 (by rfl) ⟨89265480, by rfl⟩ : syracuseStep 238041281 = 178530961) B178530961
theorem B12217067 : Blo 1607002 12217067 := bstep (se 1 (by rfl) ⟨9162800, by rfl⟩ : syracuseStep 12217067 = 18325601) B18325601
theorem B158694187 : Blo 1607002 158694187 := bstep (se 1 (by rfl) ⟨119020640, by rfl⟩ : syracuseStep 158694187 = 238041281) B238041281
theorem B211592249 : Blo 1607002 211592249 := bstep (se 2 (by rfl) ⟨79347093, by rfl⟩ : syracuseStep 211592249 = 158694187) B158694187
theorem B8144711 : Blo 1607002 8144711 := bstep (se 1 (by rfl) ⟨6108533, by rfl⟩ : syracuseStep 8144711 = 12217067) B12217067
theorem B141061499 : Blo 1607002 141061499 := bstep (se 1 (by rfl) ⟨105796124, by rfl⟩ : syracuseStep 141061499 = 211592249) B211592249
theorem B5429807 : Blo 1607002 5429807 := bstep (se 1 (by rfl) ⟨4072355, by rfl⟩ : syracuseStep 5429807 = 8144711) B8144711
theorem B94040999 : Blo 1607002 94040999 := bstep (se 1 (by rfl) ⟨70530749, by rfl⟩ : syracuseStep 94040999 = 141061499) B141061499
theorem B3619871 : Blo 1607002 3619871 := bstep (se 1 (by rfl) ⟨2714903, by rfl⟩ : syracuseStep 3619871 = 5429807) B5429807
theorem B62693999 : Blo 1607002 62693999 := bstep (se 1 (by rfl) ⟨47020499, by rfl⟩ : syracuseStep 62693999 = 94040999) B94040999
theorem B2413247 : Blo 1607002 2413247 := bstep (se 1 (by rfl) ⟨1809935, by rfl⟩ : syracuseStep 2413247 = 3619871) B3619871
theorem B41795999 : Blo 1607002 41795999 := bstep (se 1 (by rfl) ⟨31346999, by rfl⟩ : syracuseStep 41795999 = 62693999) B62693999
theorem B1608831 : Blo 1607002 1608831 := bstep (se 1 (by rfl) ⟨1206623, by rfl⟩ : syracuseStep 1608831 = 2413247) B2413247
theorem B27863999 : Blo 1607002 27863999 := bstep (se 1 (by rfl) ⟨20897999, by rfl⟩ : syracuseStep 27863999 = 41795999) B41795999
theorem B18575999 : Blo 1607002 18575999 := bstep (se 1 (by rfl) ⟨13931999, by rfl⟩ : syracuseStep 18575999 = 27863999) B27863999
theorem B12383999 : Blo 1607002 12383999 := bstep (se 1 (by rfl) ⟨9287999, by rfl⟩ : syracuseStep 12383999 = 18575999) B18575999
theorem B8255999 : Blo 1607002 8255999 := bstep (se 1 (by rfl) ⟨6191999, by rfl⟩ : syracuseStep 8255999 = 12383999) B12383999
theorem B5503999 : Blo 1607002 5503999 := bstep (se 1 (by rfl) ⟨4127999, by rfl⟩ : syracuseStep 5503999 = 8255999) B8255999
theorem B7338665 : Blo 1607002 7338665 := bstep (se 2 (by rfl) ⟨2751999, by rfl⟩ : syracuseStep 7338665 = 5503999) B5503999
theorem B4892443 : Blo 1607002 4892443 := bstep (se 1 (by rfl) ⟨3669332, by rfl⟩ : syracuseStep 4892443 = 7338665) B7338665
theorem B26093029 : Blo 1607002 26093029 := bstep (se 4 (by rfl) ⟨2446221, by rfl⟩ : syracuseStep 26093029 = 4892443) B4892443
theorem B34790705 : Blo 1607002 34790705 := bstep (se 2 (by rfl) ⟨13046514, by rfl⟩ : syracuseStep 34790705 = 26093029) B26093029
theorem B23193803 : Blo 1607002 23193803 := bstep (se 1 (by rfl) ⟨17395352, by rfl⟩ : syracuseStep 23193803 = 34790705) B34790705
theorem B15462535 : Blo 1607002 15462535 := bstep (se 1 (by rfl) ⟨11596901, by rfl⟩ : syracuseStep 15462535 = 23193803) B23193803
theorem B20616713 : Blo 1607002 20616713 := bstep (se 2 (by rfl) ⟨7731267, by rfl⟩ : syracuseStep 20616713 = 15462535) B15462535
theorem B13744475 : Blo 1607002 13744475 := bstep (se 1 (by rfl) ⟨10308356, by rfl⟩ : syracuseStep 13744475 = 20616713) B20616713
theorem B9162983 : Blo 1607002 9162983 := bstep (se 1 (by rfl) ⟨6872237, by rfl⟩ : syracuseStep 9162983 = 13744475) B13744475
theorem B6108655 : Blo 1607002 6108655 := bstep (se 1 (by rfl) ⟨4581491, by rfl⟩ : syracuseStep 6108655 = 9162983) B9162983
theorem B8144873 : Blo 1607002 8144873 := bstep (se 2 (by rfl) ⟨3054327, by rfl⟩ : syracuseStep 8144873 = 6108655) B6108655
theorem B5429915 : Blo 1607002 5429915 := bstep (se 1 (by rfl) ⟨4072436, by rfl⟩ : syracuseStep 5429915 = 8144873) B8144873
theorem B3619943 : Blo 1607002 3619943 := bstep (se 1 (by rfl) ⟨2714957, by rfl⟩ : syracuseStep 3619943 = 5429915) B5429915
theorem B2413295 : Blo 1607002 2413295 := bstep (se 1 (by rfl) ⟨1809971, by rfl⟩ : syracuseStep 2413295 = 3619943) B3619943
theorem B1608863 : Blo 1607002 1608863 := bstep (se 1 (by rfl) ⟨1206647, by rfl⟩ : syracuseStep 1608863 = 2413295) B2413295

theorem C0 (j : ℕ) (h1 : 401750 ≤ j) (h2 : j ≤ 402249) : Blo 1607002 (4 * j + 3) := by
  interval_cases j
  · exact B1607003
  · exact B1607007
  · exact B1607011
  · exact B1607015
  · exact B1607019
  · exact B1607023
  · exact B1607027
  · exact B1607031
  · exact B1607035
  · exact B1607039
  · exact B1607043
  · exact B1607047
  · exact B1607051
  · exact B1607055
  · exact B1607059
  · exact B1607063
  · exact B1607067
  · exact B1607071
  · exact B1607075
  · exact B1607079
  · exact B1607083
  · exact B1607087
  · exact B1607091
  · exact B1607095
  · exact B1607099
  · exact B1607103
  · exact B1607107
  · exact B1607111
  · exact B1607115
  · exact B1607119
  · exact B1607123
  · exact B1607127
  · exact B1607131
  · exact B1607135
  · exact B1607139
  · exact B1607143
  · exact B1607147
  · exact B1607151
  · exact B1607155
  · exact B1607159
  · exact B1607163
  · exact B1607167
  · exact B1607171
  · exact B1607175
  · exact B1607179
  · exact B1607183
  · exact B1607187
  · exact B1607191
  · exact B1607195
  · exact B1607199
  · exact B1607203
  · exact B1607207
  · exact B1607211
  · exact B1607215
  · exact B1607219
  · exact B1607223
  · exact B1607227
  · exact B1607231
  · exact B1607235
  · exact B1607239
  · exact B1607243
  · exact B1607247
  · exact B1607251
  · exact B1607255
  · exact B1607259
  · exact B1607263
  · exact B1607267
  · exact B1607271
  · exact B1607275
  · exact B1607279
  · exact B1607283
  · exact B1607287
  · exact B1607291
  · exact B1607295
  · exact B1607299
  · exact B1607303
  · exact B1607307
  · exact B1607311
  · exact B1607315
  · exact B1607319
  · exact B1607323
  · exact B1607327
  · exact B1607331
  · exact B1607335
  · exact B1607339
  · exact B1607343
  · exact B1607347
  · exact B1607351
  · exact B1607355
  · exact B1607359
  · exact B1607363
  · exact B1607367
  · exact B1607371
  · exact B1607375
  · exact B1607379
  · exact B1607383
  · exact B1607387
  · exact B1607391
  · exact B1607395
  · exact B1607399
  · exact B1607403
  · exact B1607407
  · exact B1607411
  · exact B1607415
  · exact B1607419
  · exact B1607423
  · exact B1607427
  · exact B1607431
  · exact B1607435
  · exact B1607439
  · exact B1607443
  · exact B1607447
  · exact B1607451
  · exact B1607455
  · exact B1607459
  · exact B1607463
  · exact B1607467
  · exact B1607471
  · exact B1607475
  · exact B1607479
  · exact B1607483
  · exact B1607487
  · exact B1607491
  · exact B1607495
  · exact B1607499
  · exact B1607503
  · exact B1607507
  · exact B1607511
  · exact B1607515
  · exact B1607519
  · exact B1607523
  · exact B1607527
  · exact B1607531
  · exact B1607535
  · exact B1607539
  · exact B1607543
  · exact B1607547
  · exact B1607551
  · exact B1607555
  · exact B1607559
  · exact B1607563
  · exact B1607567
  · exact B1607571
  · exact B1607575
  · exact B1607579
  · exact B1607583
  · exact B1607587
  · exact B1607591
  · exact B1607595
  · exact B1607599
  · exact B1607603
  · exact B1607607
  · exact B1607611
  · exact B1607615
  · exact B1607619
  · exact B1607623
  · exact B1607627
  · exact B1607631
  · exact B1607635
  · exact B1607639
  · exact B1607643
  · exact B1607647
  · exact B1607651
  · exact B1607655
  · exact B1607659
  · exact B1607663
  · exact B1607667
  · exact B1607671
  · exact B1607675
  · exact B1607679
  · exact B1607683
  · exact B1607687
  · exact B1607691
  · exact B1607695
  · exact B1607699
  · exact B1607703
  · exact B1607707
  · exact B1607711
  · exact B1607715
  · exact B1607719
  · exact B1607723
  · exact B1607727
  · exact B1607731
  · exact B1607735
  · exact B1607739
  · exact B1607743
  · exact B1607747
  · exact B1607751
  · exact B1607755
  · exact B1607759
  · exact B1607763
  · exact B1607767
  · exact B1607771
  · exact B1607775
  · exact B1607779
  · exact B1607783
  · exact B1607787
  · exact B1607791
  · exact B1607795
  · exact B1607799
  · exact B1607803
  · exact B1607807
  · exact B1607811
  · exact B1607815
  · exact B1607819
  · exact B1607823
  · exact B1607827
  · exact B1607831
  · exact B1607835
  · exact B1607839
  · exact B1607843
  · exact B1607847
  · exact B1607851
  · exact B1607855
  · exact B1607859
  · exact B1607863
  · exact B1607867
  · exact B1607871
  · exact B1607875
  · exact B1607879
  · exact B1607883
  · exact B1607887
  · exact B1607891
  · exact B1607895
  · exact B1607899
  · exact B1607903
  · exact B1607907
  · exact B1607911
  · exact B1607915
  · exact B1607919
  · exact B1607923
  · exact B1607927
  · exact B1607931
  · exact B1607935
  · exact B1607939
  · exact B1607943
  · exact B1607947
  · exact B1607951
  · exact B1607955
  · exact B1607959
  · exact B1607963
  · exact B1607967
  · exact B1607971
  · exact B1607975
  · exact B1607979
  · exact B1607983
  · exact B1607987
  · exact B1607991
  · exact B1607995
  · exact B1607999
  · exact B1608003
  · exact B1608007
  · exact B1608011
  · exact B1608015
  · exact B1608019
  · exact B1608023
  · exact B1608027
  · exact B1608031
  · exact B1608035
  · exact B1608039
  · exact B1608043
  · exact B1608047
  · exact B1608051
  · exact B1608055
  · exact B1608059
  · exact B1608063
  · exact B1608067
  · exact B1608071
  · exact B1608075
  · exact B1608079
  · exact B1608083
  · exact B1608087
  · exact B1608091
  · exact B1608095
  · exact B1608099
  · exact B1608103
  · exact B1608107
  · exact B1608111
  · exact B1608115
  · exact B1608119
  · exact B1608123
  · exact B1608127
  · exact B1608131
  · exact B1608135
  · exact B1608139
  · exact B1608143
  · exact B1608147
  · exact B1608151
  · exact B1608155
  · exact B1608159
  · exact B1608163
  · exact B1608167
  · exact B1608171
  · exact B1608175
  · exact B1608179
  · exact B1608183
  · exact B1608187
  · exact B1608191
  · exact B1608195
  · exact B1608199
  · exact B1608203
  · exact B1608207
  · exact B1608211
  · exact B1608215
  · exact B1608219
  · exact B1608223
  · exact B1608227
  · exact B1608231
  · exact B1608235
  · exact B1608239
  · exact B1608243
  · exact B1608247
  · exact B1608251
  · exact B1608255
  · exact B1608259
  · exact B1608263
  · exact B1608267
  · exact B1608271
  · exact B1608275
  · exact B1608279
  · exact B1608283
  · exact B1608287
  · exact B1608291
  · exact B1608295
  · exact B1608299
  · exact B1608303
  · exact B1608307
  · exact B1608311
  · exact B1608315
  · exact B1608319
  · exact B1608323
  · exact B1608327
  · exact B1608331
  · exact B1608335
  · exact B1608339
  · exact B1608343
  · exact B1608347
  · exact B1608351
  · exact B1608355
  · exact B1608359
  · exact B1608363
  · exact B1608367
  · exact B1608371
  · exact B1608375
  · exact B1608379
  · exact B1608383
  · exact B1608387
  · exact B1608391
  · exact B1608395
  · exact B1608399
  · exact B1608403
  · exact B1608407
  · exact B1608411
  · exact B1608415
  · exact B1608419
  · exact B1608423
  · exact B1608427
  · exact B1608431
  · exact B1608435
  · exact B1608439
  · exact B1608443
  · exact B1608447
  · exact B1608451
  · exact B1608455
  · exact B1608459
  · exact B1608463
  · exact B1608467
  · exact B1608471
  · exact B1608475
  · exact B1608479
  · exact B1608483
  · exact B1608487
  · exact B1608491
  · exact B1608495
  · exact B1608499
  · exact B1608503
  · exact B1608507
  · exact B1608511
  · exact B1608515
  · exact B1608519
  · exact B1608523
  · exact B1608527
  · exact B1608531
  · exact B1608535
  · exact B1608539
  · exact B1608543
  · exact B1608547
  · exact B1608551
  · exact B1608555
  · exact B1608559
  · exact B1608563
  · exact B1608567
  · exact B1608571
  · exact B1608575
  · exact B1608579
  · exact B1608583
  · exact B1608587
  · exact B1608591
  · exact B1608595
  · exact B1608599
  · exact B1608603
  · exact B1608607
  · exact B1608611
  · exact B1608615
  · exact B1608619
  · exact B1608623
  · exact B1608627
  · exact B1608631
  · exact B1608635
  · exact B1608639
  · exact B1608643
  · exact B1608647
  · exact B1608651
  · exact B1608655
  · exact B1608659
  · exact B1608663
  · exact B1608667
  · exact B1608671
  · exact B1608675
  · exact B1608679
  · exact B1608683
  · exact B1608687
  · exact B1608691
  · exact B1608695
  · exact B1608699
  · exact B1608703
  · exact B1608707
  · exact B1608711
  · exact B1608715
  · exact B1608719
  · exact B1608723
  · exact B1608727
  · exact B1608731
  · exact B1608735
  · exact B1608739
  · exact B1608743
  · exact B1608747
  · exact B1608751
  · exact B1608755
  · exact B1608759
  · exact B1608763
  · exact B1608767
  · exact B1608771
  · exact B1608775
  · exact B1608779
  · exact B1608783
  · exact B1608787
  · exact B1608791
  · exact B1608795
  · exact B1608799
  · exact B1608803
  · exact B1608807
  · exact B1608811
  · exact B1608815
  · exact B1608819
  · exact B1608823
  · exact B1608827
  · exact B1608831
  · exact B1608835
  · exact B1608839
  · exact B1608843
  · exact B1608847
  · exact B1608851
  · exact B1608855
  · exact B1608859
  · exact B1608863
  · exact B1608867
  · exact B1608871
  · exact B1608875
  · exact B1608879
  · exact B1608883
  · exact B1608887
  · exact B1608891
  · exact B1608895
  · exact B1608899
  · exact B1608903
  · exact B1608907
  · exact B1608911
  · exact B1608915
  · exact B1608919
  · exact B1608923
  · exact B1608927
  · exact B1608931
  · exact B1608935
  · exact B1608939
  · exact B1608943
  · exact B1608947
  · exact B1608951
  · exact B1608955
  · exact B1608959
  · exact B1608963
  · exact B1608967
  · exact B1608971
  · exact B1608975
  · exact B1608979
  · exact B1608983
  · exact B1608987
  · exact B1608991
  · exact B1608995
  · exact B1608999

theorem solution (m : ℕ) (hlo : 1607002 ≤ m) (hhi : m ≤ 1609002) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 401750 ≤ j := by omega
    have hj2 : j ≤ 402249 := by omega
    have hb : Blo 1607002 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
