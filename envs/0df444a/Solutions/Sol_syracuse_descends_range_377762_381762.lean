-- Prove2me | solution 1 for syracuse_descends_range_377762_381762
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:42.442987+00:00
-- url     : https://prove2.me/submissions/fef196b7-c0b6-4984-82d3-65ddbabaad8e

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


theorem B426001 : Blo 377762 426001 := bbase (se 2 (by rfl) ⟨159750, by rfl⟩ : syracuseStep 426001 = 319501) (by norm_num)
theorem B819229 : Blo 377762 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B426037 : Blo 377762 426037 := bbase (se 5 (by rfl) ⟨19970, by rfl⟩ : syracuseStep 426037 = 39941) (by norm_num)
theorem B852029 : Blo 377762 852029 := bbase (se 3 (by rfl) ⟨159755, by rfl⟩ : syracuseStep 852029 = 319511) (by norm_num)
theorem B426073 : Blo 377762 426073 := bbase (se 2 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 426073 = 319555) (by norm_num)
theorem B426109 : Blo 377762 426109 := bbase (se 3 (by rfl) ⟨79895, by rfl⟩ : syracuseStep 426109 = 159791) (by norm_num)
theorem B852101 : Blo 377762 852101 := bbase (se 4 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 852101 = 159769) (by norm_num)
theorem B426145 : Blo 377762 426145 := bbase (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) (by norm_num)
theorem B426181 : Blo 377762 426181 := bbase (se 4 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 426181 = 79909) (by norm_num)
theorem B852173 : Blo 377762 852173 := bbase (se 3 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 852173 = 319565) (by norm_num)
theorem B426217 : Blo 377762 426217 := bbase (se 2 (by rfl) ⟨159831, by rfl⟩ : syracuseStep 426217 = 319663) (by norm_num)
theorem B721133 : Blo 377762 721133 := bbase (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) (by norm_num)
theorem B426253 : Blo 377762 426253 := bbase (se 3 (by rfl) ⟨79922, by rfl⟩ : syracuseStep 426253 = 159845) (by norm_num)
theorem B852245 : Blo 377762 852245 := bbase (se 6 (by rfl) ⟨19974, by rfl⟩ : syracuseStep 852245 = 39949) (by norm_num)
theorem B1442069 : Blo 377762 1442069 := bbase (se 6 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 1442069 = 67597) (by norm_num)
theorem B426289 : Blo 377762 426289 := bbase (se 2 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 426289 = 319717) (by norm_num)
theorem B426325 : Blo 377762 426325 := bbase (se 10 (by rfl) ⟨624, by rfl⟩ : syracuseStep 426325 = 1249) (by norm_num)
theorem B852317 : Blo 377762 852317 := bbase (se 3 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 852317 = 319619) (by norm_num)
theorem B426361 : Blo 377762 426361 := bbase (se 2 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 426361 = 319771) (by norm_num)
theorem B1278341 : Blo 377762 1278341 := bbase (se 4 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 1278341 = 239689) (by norm_num)
theorem B426397 : Blo 377762 426397 := bbase (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) (by norm_num)
theorem B852389 : Blo 377762 852389 := bbase (se 4 (by rfl) ⟨79911, by rfl⟩ : syracuseStep 852389 = 159823) (by norm_num)
theorem B2163125 : Blo 377762 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B426433 : Blo 377762 426433 := bbase (se 2 (by rfl) ⟨159912, by rfl⟩ : syracuseStep 426433 = 319825) (by norm_num)
theorem B819677 : Blo 377762 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B426469 : Blo 377762 426469 := bbase (se 4 (by rfl) ⟨39981, by rfl⟩ : syracuseStep 426469 = 79963) (by norm_num)
theorem B852461 : Blo 377762 852461 := bbase (se 3 (by rfl) ⟨159836, by rfl⟩ : syracuseStep 852461 = 319673) (by norm_num)
theorem B426505 : Blo 377762 426505 := bbase (se 2 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 426505 = 319879) (by norm_num)
theorem B426541 : Blo 377762 426541 := bbase (se 3 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 426541 = 159953) (by norm_num)
theorem B852533 : Blo 377762 852533 := bbase (se 5 (by rfl) ⟨39962, by rfl⟩ : syracuseStep 852533 = 79925) (by norm_num)
theorem B1442357 : Blo 377762 1442357 := bbase (se 5 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 1442357 = 135221) (by norm_num)
theorem B426577 : Blo 377762 426577 := bbase (se 2 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 426577 = 319933) (by norm_num)
theorem B426613 : Blo 377762 426613 := bbase (se 5 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 426613 = 39995) (by norm_num)
theorem B1081973 : Blo 377762 1081973 := bbase (se 5 (by rfl) ⟨50717, by rfl⟩ : syracuseStep 1081973 = 101435) (by norm_num)
theorem B852605 : Blo 377762 852605 := bbase (se 3 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 852605 = 319727) (by norm_num)
theorem B426649 : Blo 377762 426649 := bbase (se 2 (by rfl) ⟨159993, by rfl⟩ : syracuseStep 426649 = 319987) (by norm_num)
theorem B426685 : Blo 377762 426685 := bbase (se 3 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 426685 = 160007) (by norm_num)
theorem B852677 : Blo 377762 852677 := bbase (se 4 (by rfl) ⟨79938, by rfl⟩ : syracuseStep 852677 = 159877) (by norm_num)
theorem B3637973 : Blo 377762 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B426721 : Blo 377762 426721 := bbase (se 2 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 426721 = 320041) (by norm_num)
theorem B426757 : Blo 377762 426757 := bbase (se 4 (by rfl) ⟨40008, by rfl⟩ : syracuseStep 426757 = 80017) (by norm_num)
theorem B852749 : Blo 377762 852749 := bbase (se 3 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 852749 = 319781) (by norm_num)
theorem B426793 : Blo 377762 426793 := bbase (se 2 (by rfl) ⟨160047, by rfl⟩ : syracuseStep 426793 = 320095) (by norm_num)
theorem B1278773 : Blo 377762 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B426829 : Blo 377762 426829 := bbase (se 3 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 426829 = 160061) (by norm_num)
theorem B852821 : Blo 377762 852821 := bbase (se 9 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 852821 = 4997) (by norm_num)
theorem B426865 : Blo 377762 426865 := bbase (se 2 (by rfl) ⟨160074, by rfl⟩ : syracuseStep 426865 = 320149) (by norm_num)
theorem B2196341 : Blo 377762 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B426901 : Blo 377762 426901 := bbase (se 6 (by rfl) ⟨10005, by rfl⟩ : syracuseStep 426901 = 20011) (by norm_num)
theorem B852893 : Blo 377762 852893 := bbase (se 3 (by rfl) ⟨159917, by rfl⟩ : syracuseStep 852893 = 319835) (by norm_num)
theorem B426937 : Blo 377762 426937 := bbase (se 2 (by rfl) ⟨160101, by rfl⟩ : syracuseStep 426937 = 320203) (by norm_num)
theorem B394177 : Blo 377762 394177 := bbase (se 2 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 394177 = 295633) (by norm_num)
theorem B426973 : Blo 377762 426973 := bbase (se 3 (by rfl) ⟨80057, by rfl⟩ : syracuseStep 426973 = 160115) (by norm_num)
theorem B721885 : Blo 377762 721885 := bbase (se 3 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 721885 = 270707) (by norm_num)
theorem B852965 : Blo 377762 852965 := bbase (se 4 (by rfl) ⟨79965, by rfl⟩ : syracuseStep 852965 = 159931) (by norm_num)
theorem B427009 : Blo 377762 427009 := bbase (se 2 (by rfl) ⟨160128, by rfl⟩ : syracuseStep 427009 = 320257) (by norm_num)
theorem B427045 : Blo 377762 427045 := bbase (se 4 (by rfl) ⟨40035, by rfl⟩ : syracuseStep 427045 = 80071) (by norm_num)
theorem B853037 : Blo 377762 853037 := bbase (se 3 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 853037 = 319889) (by norm_num)
theorem B427081 : Blo 377762 427081 := bbase (se 2 (by rfl) ⟨160155, by rfl⟩ : syracuseStep 427081 = 320311) (by norm_num)
theorem B427117 : Blo 377762 427117 := bbase (se 3 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 427117 = 160169) (by norm_num)
theorem B722029 : Blo 377762 722029 := bbase (se 3 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 722029 = 270761) (by norm_num)
theorem B853109 : Blo 377762 853109 := bbase (se 5 (by rfl) ⟨39989, by rfl⟩ : syracuseStep 853109 = 79979) (by norm_num)
theorem B427153 : Blo 377762 427153 := bbase (se 2 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 427153 = 320365) (by norm_num)
theorem B427189 : Blo 377762 427189 := bbase (se 5 (by rfl) ⟨20024, by rfl⟩ : syracuseStep 427189 = 40049) (by norm_num)
theorem B853181 : Blo 377762 853181 := bbase (se 3 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 853181 = 319943) (by norm_num)
theorem B427225 : Blo 377762 427225 := bbase (se 2 (by rfl) ⟨160209, by rfl⟩ : syracuseStep 427225 = 320419) (by norm_num)
theorem B1279205 : Blo 377762 1279205 := bbase (se 4 (by rfl) ⟨119925, by rfl⟩ : syracuseStep 1279205 = 239851) (by norm_num)
theorem B427261 : Blo 377762 427261 := bbase (se 3 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 427261 = 160223) (by norm_num)
theorem B853253 : Blo 377762 853253 := bbase (se 4 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 853253 = 159985) (by norm_num)
theorem B722189 : Blo 377762 722189 := bbase (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) (by norm_num)
theorem B427297 : Blo 377762 427297 := bbase (se 2 (by rfl) ⟨160236, by rfl⟩ : syracuseStep 427297 = 320473) (by norm_num)
theorem B427333 : Blo 377762 427333 := bbase (se 4 (by rfl) ⟨40062, by rfl⟩ : syracuseStep 427333 = 80125) (by norm_num)
theorem B853325 : Blo 377762 853325 := bbase (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) (by norm_num)
theorem B427369 : Blo 377762 427369 := bbase (se 2 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 427369 = 320527) (by norm_num)
theorem B427405 : Blo 377762 427405 := bbase (se 3 (by rfl) ⟨80138, by rfl⟩ : syracuseStep 427405 = 160277) (by norm_num)
theorem B853397 : Blo 377762 853397 := bbase (se 6 (by rfl) ⟨20001, by rfl⟩ : syracuseStep 853397 = 40003) (by norm_num)
theorem B722333 : Blo 377762 722333 := bbase (se 3 (by rfl) ⟨135437, by rfl⟩ : syracuseStep 722333 = 270875) (by norm_num)
theorem B427441 : Blo 377762 427441 := bbase (se 2 (by rfl) ⟨160290, by rfl⟩ : syracuseStep 427441 = 320581) (by norm_num)
theorem B427477 : Blo 377762 427477 := bbase (se 7 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 427477 = 10019) (by norm_num)
theorem B853469 : Blo 377762 853469 := bbase (se 3 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 853469 = 320051) (by norm_num)
theorem B460261 : Blo 377762 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B624109 : Blo 377762 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B427513 : Blo 377762 427513 := bbase (se 2 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 427513 = 320635) (by norm_num)
theorem B427549 : Blo 377762 427549 := bbase (se 3 (by rfl) ⟨80165, by rfl⟩ : syracuseStep 427549 = 160331) (by norm_num)
theorem B853541 : Blo 377762 853541 := bbase (se 4 (by rfl) ⟨80019, by rfl⟩ : syracuseStep 853541 = 160039) (by norm_num)
theorem B427585 : Blo 377762 427585 := bbase (se 2 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 427585 = 320689) (by norm_num)
theorem B427621 : Blo 377762 427621 := bbase (se 4 (by rfl) ⟨40089, by rfl⟩ : syracuseStep 427621 = 80179) (by norm_num)
theorem B853613 : Blo 377762 853613 := bbase (se 3 (by rfl) ⟨160052, by rfl⟩ : syracuseStep 853613 = 320105) (by norm_num)
theorem B427657 : Blo 377762 427657 := bbase (se 2 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 427657 = 320743) (by norm_num)
theorem B1279637 : Blo 377762 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B427693 : Blo 377762 427693 := bbase (se 3 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 427693 = 160385) (by norm_num)
theorem B853685 : Blo 377762 853685 := bbase (se 5 (by rfl) ⟨40016, by rfl⟩ : syracuseStep 853685 = 80033) (by norm_num)
theorem B722621 : Blo 377762 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B427729 : Blo 377762 427729 := bbase (se 2 (by rfl) ⟨160398, by rfl⟩ : syracuseStep 427729 = 320797) (by norm_num)
theorem B1443541 : Blo 377762 1443541 := bbase (se 7 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 1443541 = 33833) (by norm_num)
theorem B984797 : Blo 377762 984797 := bbase (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) (by norm_num)
theorem B427765 : Blo 377762 427765 := bbase (se 5 (by rfl) ⟨20051, by rfl⟩ : syracuseStep 427765 = 40103) (by norm_num)
theorem B853757 : Blo 377762 853757 := bbase (se 3 (by rfl) ⟨160079, by rfl⟩ : syracuseStep 853757 = 320159) (by norm_num)
theorem B427801 : Blo 377762 427801 := bbase (se 2 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 427801 = 320851) (by norm_num)
theorem B427837 : Blo 377762 427837 := bbase (se 3 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 427837 = 160439) (by norm_num)
theorem B853829 : Blo 377762 853829 := bbase (se 4 (by rfl) ⟨80046, by rfl⟩ : syracuseStep 853829 = 160093) (by norm_num)
theorem B722773 : Blo 377762 722773 := bbase (se 9 (by rfl) ⟨2117, by rfl⟩ : syracuseStep 722773 = 4235) (by norm_num)
theorem B427873 : Blo 377762 427873 := bbase (se 2 (by rfl) ⟨160452, by rfl⟩ : syracuseStep 427873 = 320905) (by norm_num)
theorem B427909 : Blo 377762 427909 := bbase (se 4 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 427909 = 80233) (by norm_num)
theorem B853901 : Blo 377762 853901 := bbase (se 3 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 853901 = 320213) (by norm_num)
theorem B1542037 : Blo 377762 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B427945 : Blo 377762 427945 := bbase (se 2 (by rfl) ⟨160479, by rfl⟩ : syracuseStep 427945 = 320959) (by norm_num)
theorem B427981 : Blo 377762 427981 := bbase (se 3 (by rfl) ⟨80246, by rfl⟩ : syracuseStep 427981 = 160493) (by norm_num)
theorem B853973 : Blo 377762 853973 := bbase (se 7 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 853973 = 20015) (by norm_num)
theorem B428017 : Blo 377762 428017 := bbase (se 2 (by rfl) ⟨160506, by rfl⟩ : syracuseStep 428017 = 321013) (by norm_num)
theorem B1214453 : Blo 377762 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B1443845 : Blo 377762 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B526357 : Blo 377762 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B428053 : Blo 377762 428053 := bbase (se 6 (by rfl) ⟨10032, by rfl⟩ : syracuseStep 428053 = 20065) (by norm_num)
theorem B854045 : Blo 377762 854045 := bbase (se 3 (by rfl) ⟨160133, by rfl⟩ : syracuseStep 854045 = 320267) (by norm_num)
theorem B428089 : Blo 377762 428089 := bbase (se 2 (by rfl) ⟨160533, by rfl⟩ : syracuseStep 428089 = 321067) (by norm_num)
theorem B1280069 : Blo 377762 1280069 := bbase (se 4 (by rfl) ⟨120006, by rfl⟩ : syracuseStep 1280069 = 240013) (by norm_num)
theorem B428125 : Blo 377762 428125 := bbase (se 3 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 428125 = 160547) (by norm_num)
theorem B854117 : Blo 377762 854117 := bbase (se 4 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 854117 = 160147) (by norm_num)
theorem B428161 : Blo 377762 428161 := bbase (se 2 (by rfl) ⟨160560, by rfl⟩ : syracuseStep 428161 = 321121) (by norm_num)
theorem B723077 : Blo 377762 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B1083557 : Blo 377762 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B428197 : Blo 377762 428197 := bbase (se 4 (by rfl) ⟨40143, by rfl⟩ : syracuseStep 428197 = 80287) (by norm_num)
theorem B854189 : Blo 377762 854189 := bbase (se 3 (by rfl) ⟨160160, by rfl⟩ : syracuseStep 854189 = 320321) (by norm_num)
theorem B428233 : Blo 377762 428233 := bbase (se 2 (by rfl) ⟨160587, by rfl⟩ : syracuseStep 428233 = 321175) (by norm_num)
theorem B428269 : Blo 377762 428269 := bbase (se 3 (by rfl) ⟨80300, by rfl⟩ : syracuseStep 428269 = 160601) (by norm_num)
theorem B854261 : Blo 377762 854261 := bbase (se 5 (by rfl) ⟨40043, by rfl⟩ : syracuseStep 854261 = 80087) (by norm_num)
theorem B428305 : Blo 377762 428305 := bbase (se 2 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 428305 = 321229) (by norm_num)
theorem B428341 : Blo 377762 428341 := bbase (se 5 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 428341 = 40157) (by norm_num)
theorem B854333 : Blo 377762 854333 := bbase (se 3 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 854333 = 320375) (by norm_num)
theorem B428377 : Blo 377762 428377 := bbase (se 2 (by rfl) ⟨160641, by rfl⟩ : syracuseStep 428377 = 321283) (by norm_num)
theorem B428413 : Blo 377762 428413 := bbase (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) (by norm_num)
theorem B854405 : Blo 377762 854405 := bbase (se 4 (by rfl) ⟨80100, by rfl⟩ : syracuseStep 854405 = 160201) (by norm_num)
theorem B3082645 : Blo 377762 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B428449 : Blo 377762 428449 := bbase (se 2 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 428449 = 321337) (by norm_num)
theorem B428485 : Blo 377762 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B854477 : Blo 377762 854477 := bbase (se 3 (by rfl) ⟨160214, by rfl⟩ : syracuseStep 854477 = 320429) (by norm_num)
theorem B428521 : Blo 377762 428521 := bbase (se 2 (by rfl) ⟨160695, by rfl⟩ : syracuseStep 428521 = 321391) (by norm_num)
theorem B1280501 : Blo 377762 1280501 := bbase (se 5 (by rfl) ⟨60023, by rfl⟩ : syracuseStep 1280501 = 120047) (by norm_num)
theorem B428557 : Blo 377762 428557 := bbase (se 3 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 428557 = 160709) (by norm_num)
theorem B854549 : Blo 377762 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B428593 : Blo 377762 428593 := bbase (se 2 (by rfl) ⟨160722, by rfl⟩ : syracuseStep 428593 = 321445) (by norm_num)
theorem B428629 : Blo 377762 428629 := bbase (se 8 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 428629 = 5023) (by norm_num)
theorem B854621 : Blo 377762 854621 := bbase (se 3 (by rfl) ⟨160241, by rfl⟩ : syracuseStep 854621 = 320483) (by norm_num)
theorem B428665 : Blo 377762 428665 := bbase (se 2 (by rfl) ⟨160749, by rfl⟩ : syracuseStep 428665 = 321499) (by norm_num)
theorem B428701 : Blo 377762 428701 := bbase (se 3 (by rfl) ⟨80381, by rfl⟩ : syracuseStep 428701 = 160763) (by norm_num)
theorem B854693 : Blo 377762 854693 := bbase (se 4 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 854693 = 160255) (by norm_num)
theorem B428737 : Blo 377762 428737 := bbase (se 2 (by rfl) ⟨160776, by rfl⟩ : syracuseStep 428737 = 321553) (by norm_num)
theorem B428773 : Blo 377762 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B854765 : Blo 377762 854765 := bbase (se 3 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 854765 = 320537) (by norm_num)
theorem B428809 : Blo 377762 428809 := bbase (se 2 (by rfl) ⟨160803, by rfl⟩ : syracuseStep 428809 = 321607) (by norm_num)
theorem B428845 : Blo 377762 428845 := bbase (se 3 (by rfl) ⟨80408, by rfl⟩ : syracuseStep 428845 = 160817) (by norm_num)
theorem B854837 : Blo 377762 854837 := bbase (se 5 (by rfl) ⟨40070, by rfl⟩ : syracuseStep 854837 = 80141) (by norm_num)
theorem B1084229 : Blo 377762 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B428881 : Blo 377762 428881 := bbase (se 2 (by rfl) ⟨160830, by rfl⟩ : syracuseStep 428881 = 321661) (by norm_num)
theorem B428917 : Blo 377762 428917 := bbase (se 5 (by rfl) ⟨20105, by rfl⟩ : syracuseStep 428917 = 40211) (by norm_num)
theorem B723829 : Blo 377762 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B854909 : Blo 377762 854909 := bbase (se 3 (by rfl) ⟨160295, by rfl⟩ : syracuseStep 854909 = 320591) (by norm_num)
theorem B428953 : Blo 377762 428953 := bbase (se 2 (by rfl) ⟨160857, by rfl⟩ : syracuseStep 428953 = 321715) (by norm_num)
theorem B1280933 : Blo 377762 1280933 := bbase (se 4 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 1280933 = 240175) (by norm_num)
theorem B428989 : Blo 377762 428989 := bbase (se 3 (by rfl) ⟨80435, by rfl⟩ : syracuseStep 428989 = 160871) (by norm_num)
theorem B854981 : Blo 377762 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B429025 : Blo 377762 429025 := bbase (se 2 (by rfl) ⟨160884, by rfl⟩ : syracuseStep 429025 = 321769) (by norm_num)
theorem B592877 : Blo 377762 592877 := bbase (se 3 (by rfl) ⟨111164, by rfl⟩ : syracuseStep 592877 = 222329) (by norm_num)
theorem B723973 : Blo 377762 723973 := bbase (se 4 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 723973 = 135745) (by norm_num)
theorem B429061 : Blo 377762 429061 := bbase (se 4 (by rfl) ⟨40224, by rfl⟩ : syracuseStep 429061 = 80449) (by norm_num)
theorem B855053 : Blo 377762 855053 := bbase (se 3 (by rfl) ⟨160322, by rfl⟩ : syracuseStep 855053 = 320645) (by norm_num)
theorem B1543205 : Blo 377762 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B429097 : Blo 377762 429097 := bbase (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) (by norm_num)
theorem B429133 : Blo 377762 429133 := bbase (se 3 (by rfl) ⟨80462, by rfl⟩ : syracuseStep 429133 = 160925) (by norm_num)
theorem B855125 : Blo 377762 855125 := bbase (se 8 (by rfl) ⟨5010, by rfl⟩ : syracuseStep 855125 = 10021) (by norm_num)
theorem B429169 : Blo 377762 429169 := bbase (se 2 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 429169 = 321877) (by norm_num)
theorem B429205 : Blo 377762 429205 := bbase (se 6 (by rfl) ⟨10059, by rfl⟩ : syracuseStep 429205 = 20119) (by norm_num)
theorem B855197 : Blo 377762 855197 := bbase (se 3 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 855197 = 320699) (by norm_num)
theorem B724133 : Blo 377762 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B429241 : Blo 377762 429241 := bbase (se 2 (by rfl) ⟨160965, by rfl⟩ : syracuseStep 429241 = 321931) (by norm_num)
theorem B429277 : Blo 377762 429277 := bbase (se 3 (by rfl) ⟨80489, by rfl⟩ : syracuseStep 429277 = 160979) (by norm_num)
theorem B855269 : Blo 377762 855269 := bbase (se 4 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 855269 = 160363) (by norm_num)
theorem B1084661 : Blo 377762 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B429313 : Blo 377762 429313 := bbase (se 2 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 429313 = 321985) (by norm_num)
theorem B429349 : Blo 377762 429349 := bbase (se 4 (by rfl) ⟨40251, by rfl⟩ : syracuseStep 429349 = 80503) (by norm_num)
theorem B855341 : Blo 377762 855341 := bbase (se 3 (by rfl) ⟨160376, by rfl⟩ : syracuseStep 855341 = 320753) (by norm_num)
theorem B724277 : Blo 377762 724277 := bbase (se 5 (by rfl) ⟨33950, by rfl⟩ : syracuseStep 724277 = 67901) (by norm_num)
theorem B691517 : Blo 377762 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B429385 : Blo 377762 429385 := bbase (se 2 (by rfl) ⟨161019, by rfl⟩ : syracuseStep 429385 = 322039) (by norm_num)
theorem B1281365 : Blo 377762 1281365 := bbase (se 11 (by rfl) ⟨938, by rfl⟩ : syracuseStep 1281365 = 1877) (by norm_num)
theorem B429421 : Blo 377762 429421 := bbase (se 3 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 429421 = 161033) (by norm_num)
theorem B855413 : Blo 377762 855413 := bbase (se 5 (by rfl) ⟨40097, by rfl⟩ : syracuseStep 855413 = 80195) (by norm_num)
theorem B429457 : Blo 377762 429457 := bbase (se 2 (by rfl) ⟨161046, by rfl⟩ : syracuseStep 429457 = 322093) (by norm_num)
theorem B855485 : Blo 377762 855485 := bbase (se 3 (by rfl) ⟨160403, by rfl⟩ : syracuseStep 855485 = 320807) (by norm_num)
theorem B855557 : Blo 377762 855557 := bbase (se 4 (by rfl) ⟨80208, by rfl⟩ : syracuseStep 855557 = 160417) (by norm_num)
theorem B1248821 : Blo 377762 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B1674821 : Blo 377762 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B855629 : Blo 377762 855629 := bbase (se 3 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 855629 = 320861) (by norm_num)
theorem B724565 : Blo 377762 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B855701 : Blo 377762 855701 := bbase (se 6 (by rfl) ⟨20055, by rfl⟩ : syracuseStep 855701 = 40111) (by norm_num)
theorem B855773 : Blo 377762 855773 := bbase (se 3 (by rfl) ⟨160457, by rfl⟩ : syracuseStep 855773 = 320915) (by norm_num)
theorem B724717 : Blo 377762 724717 := bbase (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) (by norm_num)
theorem B1281797 : Blo 377762 1281797 := bbase (se 4 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 1281797 = 240337) (by norm_num)
theorem B855845 : Blo 377762 855845 := bbase (se 4 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 855845 = 160471) (by norm_num)
theorem B1740613 : Blo 377762 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B855917 : Blo 377762 855917 := bbase (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) (by norm_num)
theorem B855989 : Blo 377762 855989 := bbase (se 5 (by rfl) ⟨40124, by rfl⟩ : syracuseStep 855989 = 80249) (by norm_num)
theorem B1085413 : Blo 377762 1085413 := bbase (se 4 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 1085413 = 203515) (by norm_num)
theorem B856061 : Blo 377762 856061 := bbase (se 3 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 856061 = 321023) (by norm_num)
theorem B856133 : Blo 377762 856133 := bbase (se 4 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 856133 = 160525) (by norm_num)
theorem B1445957 : Blo 377762 1445957 := bbase (se 4 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 1445957 = 271117) (by norm_num)
theorem B1478741 : Blo 377762 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B856205 : Blo 377762 856205 := bbase (se 3 (by rfl) ⟨160538, by rfl⟩ : syracuseStep 856205 = 321077) (by norm_num)
theorem B1282229 : Blo 377762 1282229 := bbase (se 5 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 1282229 = 120209) (by norm_num)
theorem B856277 : Blo 377762 856277 := bbase (se 7 (by rfl) ⟨10034, by rfl⟩ : syracuseStep 856277 = 20069) (by norm_num)
theorem B856349 : Blo 377762 856349 := bbase (se 3 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 856349 = 321131) (by norm_num)
theorem B856421 : Blo 377762 856421 := bbase (se 4 (by rfl) ⟨80289, by rfl⟩ : syracuseStep 856421 = 160579) (by norm_num)
theorem B1446245 : Blo 377762 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B856493 : Blo 377762 856493 := bbase (se 3 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 856493 = 321185) (by norm_num)
theorem B856565 : Blo 377762 856565 := bbase (se 5 (by rfl) ⟨40151, by rfl⟩ : syracuseStep 856565 = 80303) (by norm_num)
theorem B856637 : Blo 377762 856637 := bbase (se 3 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 856637 = 321239) (by norm_num)
theorem B4887125 : Blo 377762 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B1282661 : Blo 377762 1282661 := bbase (se 4 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 1282661 = 240499) (by norm_num)
theorem B856709 : Blo 377762 856709 := bbase (se 4 (by rfl) ⟨80316, by rfl⟩ : syracuseStep 856709 = 160633) (by norm_num)
theorem B1151653 : Blo 377762 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B2429621 : Blo 377762 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B856781 : Blo 377762 856781 := bbase (se 3 (by rfl) ⟨160646, by rfl⟩ : syracuseStep 856781 = 321293) (by norm_num)
theorem B856853 : Blo 377762 856853 := bbase (se 6 (by rfl) ⟨20082, by rfl⟩ : syracuseStep 856853 = 40165) (by norm_num)
theorem B856925 : Blo 377762 856925 := bbase (se 3 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 856925 = 321347) (by norm_num)
theorem B856997 : Blo 377762 856997 := bbase (se 4 (by rfl) ⟨80343, by rfl⟩ : syracuseStep 856997 = 160687) (by norm_num)
theorem B857069 : Blo 377762 857069 := bbase (se 3 (by rfl) ⟨160700, by rfl⟩ : syracuseStep 857069 = 321401) (by norm_num)
theorem B1283093 : Blo 377762 1283093 := bbase (se 6 (by rfl) ⟨30072, by rfl⟩ : syracuseStep 1283093 = 60145) (by norm_num)
theorem B857141 : Blo 377762 857141 := bbase (se 5 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 857141 = 80357) (by norm_num)
theorem B1217605 : Blo 377762 1217605 := bbase (se 4 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 1217605 = 228301) (by norm_num)
theorem B857213 : Blo 377762 857213 := bbase (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) (by norm_num)
theorem B431245 : Blo 377762 431245 := bbase (se 3 (by rfl) ⟨80858, by rfl⟩ : syracuseStep 431245 = 161717) (by norm_num)
theorem B857285 : Blo 377762 857285 := bbase (se 4 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 857285 = 160741) (by norm_num)
theorem B857357 : Blo 377762 857357 := bbase (se 3 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 857357 = 321509) (by norm_num)
theorem B857429 : Blo 377762 857429 := bbase (se 14 (by rfl) ⟨78, by rfl⟩ : syracuseStep 857429 = 157) (by norm_num)
theorem B464221 : Blo 377762 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B857501 : Blo 377762 857501 := bbase (se 3 (by rfl) ⟨160781, by rfl⟩ : syracuseStep 857501 = 321563) (by norm_num)
theorem B1283525 : Blo 377762 1283525 := bbase (se 4 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 1283525 = 240661) (by norm_num)
theorem B857573 : Blo 377762 857573 := bbase (se 4 (by rfl) ⟨80397, by rfl⟩ : syracuseStep 857573 = 160795) (by norm_num)
theorem B1447429 : Blo 377762 1447429 := bbase (se 4 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 1447429 = 271393) (by norm_num)
theorem B857645 : Blo 377762 857645 := bbase (se 3 (by rfl) ⟨160808, by rfl⟩ : syracuseStep 857645 = 321617) (by norm_num)
theorem B2889269 : Blo 377762 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B824909 : Blo 377762 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B857717 : Blo 377762 857717 := bbase (se 5 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 857717 = 80411) (by norm_num)
theorem B857789 : Blo 377762 857789 := bbase (se 3 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 857789 = 321671) (by norm_num)
theorem B857861 : Blo 377762 857861 := bbase (se 4 (by rfl) ⟨80424, by rfl⟩ : syracuseStep 857861 = 160849) (by norm_num)
theorem B1447733 : Blo 377762 1447733 := bbase (se 5 (by rfl) ⟨67862, by rfl⟩ : syracuseStep 1447733 = 135725) (by norm_num)
theorem B857933 : Blo 377762 857933 := bbase (se 3 (by rfl) ⟨160862, by rfl⟩ : syracuseStep 857933 = 321725) (by norm_num)
theorem B956245 : Blo 377762 956245 := bbase (se 9 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 956245 = 5603) (by norm_num)
theorem B2463605 : Blo 377762 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1283957 : Blo 377762 1283957 := bbase (se 5 (by rfl) ⟨60185, by rfl⟩ : syracuseStep 1283957 = 120371) (by norm_num)
theorem B858005 : Blo 377762 858005 := bbase (se 6 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 858005 = 40219) (by norm_num)
theorem B956357 : Blo 377762 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B858077 : Blo 377762 858077 := bbase (se 3 (by rfl) ⟨160889, by rfl⟩ : syracuseStep 858077 = 321779) (by norm_num)
theorem B858149 : Blo 377762 858149 := bbase (se 4 (by rfl) ⟨80451, by rfl⟩ : syracuseStep 858149 = 160903) (by norm_num)
theorem B858221 : Blo 377762 858221 := bbase (se 3 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 858221 = 321833) (by norm_num)
theorem B956549 : Blo 377762 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B858293 : Blo 377762 858293 := bbase (se 5 (by rfl) ⟨40232, by rfl⟩ : syracuseStep 858293 = 80465) (by norm_num)
theorem B858365 : Blo 377762 858365 := bbase (se 3 (by rfl) ⟨160943, by rfl⟩ : syracuseStep 858365 = 321887) (by norm_num)
theorem B1284389 : Blo 377762 1284389 := bbase (se 4 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 1284389 = 240823) (by norm_num)
theorem B858437 : Blo 377762 858437 := bbase (se 4 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 858437 = 160957) (by norm_num)
theorem B858509 : Blo 377762 858509 := bbase (se 3 (by rfl) ⟨160970, by rfl⟩ : syracuseStep 858509 = 321941) (by norm_num)
theorem B858581 : Blo 377762 858581 := bbase (se 7 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 858581 = 20123) (by norm_num)
theorem B956893 : Blo 377762 956893 := bbase (se 3 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 956893 = 358835) (by norm_num)
theorem B858653 : Blo 377762 858653 := bbase (se 3 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 858653 = 321995) (by norm_num)
theorem B957005 : Blo 377762 957005 := bbase (se 3 (by rfl) ⟨179438, by rfl⟩ : syracuseStep 957005 = 358877) (by norm_num)
theorem B858725 : Blo 377762 858725 := bbase (se 4 (by rfl) ⟨80505, by rfl⟩ : syracuseStep 858725 = 161011) (by norm_num)
theorem B858797 : Blo 377762 858797 := bbase (se 3 (by rfl) ⟨161024, by rfl⟩ : syracuseStep 858797 = 322049) (by norm_num)
theorem B3480245 : Blo 377762 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B1284821 : Blo 377762 1284821 := bbase (se 7 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 1284821 = 30113) (by norm_num)
theorem B858869 : Blo 377762 858869 := bbase (se 5 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 858869 = 80519) (by norm_num)
theorem B957197 : Blo 377762 957197 := bbase (se 3 (by rfl) ⟨179474, by rfl⟩ : syracuseStep 957197 = 358949) (by norm_num)
theorem B858941 : Blo 377762 858941 := bbase (se 3 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 858941 = 322103) (by norm_num)
theorem B990053 : Blo 377762 990053 := bbase (se 4 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 990053 = 185635) (by norm_num)
theorem B957541 : Blo 377762 957541 := bbase (se 4 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 957541 = 179539) (by norm_num)
theorem B1285253 : Blo 377762 1285253 := bbase (se 4 (by rfl) ⟨120492, by rfl⟩ : syracuseStep 1285253 = 240985) (by norm_num)
theorem B957653 : Blo 377762 957653 := bbase (se 7 (by rfl) ⟨11222, by rfl⟩ : syracuseStep 957653 = 22445) (by norm_num)
theorem B1187093 : Blo 377762 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B957845 : Blo 377762 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B1285685 : Blo 377762 1285685 := bbase (se 5 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 1285685 = 120533) (by norm_num)
theorem B1023637 : Blo 377762 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B958189 : Blo 377762 958189 := bbase (se 3 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 958189 = 359321) (by norm_num)
theorem B3448565 : Blo 377762 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B1220437 : Blo 377762 1220437 := bbase (se 9 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 1220437 = 7151) (by norm_num)
theorem B958301 : Blo 377762 958301 := bbase (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) (by norm_num)
theorem B1220501 : Blo 377762 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B991133 : Blo 377762 991133 := bbase (se 3 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 991133 = 371675) (by norm_num)
theorem B1286117 : Blo 377762 1286117 := bbase (se 4 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 1286117 = 241147) (by norm_num)
theorem B958493 : Blo 377762 958493 := bbase (se 3 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 958493 = 359435) (by norm_num)
theorem B696397 : Blo 377762 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B7610453 : Blo 377762 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1646837 : Blo 377762 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B958837 : Blo 377762 958837 := bbase (se 5 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 958837 = 89891) (by norm_num)
theorem B1286549 : Blo 377762 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B729557 : Blo 377762 729557 := bbase (se 7 (by rfl) ⟨8549, by rfl⟩ : syracuseStep 729557 = 17099) (by norm_num)
theorem B958949 : Blo 377762 958949 := bbase (se 4 (by rfl) ⟨89901, by rfl⟩ : syracuseStep 958949 = 179803) (by norm_num)
theorem B434665 : Blo 377762 434665 := bbase (se 2 (by rfl) ⟨162999, by rfl⟩ : syracuseStep 434665 = 325999) (by norm_num)
theorem B1614485 : Blo 377762 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B959141 : Blo 377762 959141 := bbase (se 4 (by rfl) ⟨89919, by rfl⟩ : syracuseStep 959141 = 179839) (by norm_num)
theorem B12264149 : Blo 377762 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B1286981 : Blo 377762 1286981 := bbase (se 4 (by rfl) ⟨120654, by rfl⟩ : syracuseStep 1286981 = 241309) (by norm_num)
theorem B1614725 : Blo 377762 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B959485 : Blo 377762 959485 := bbase (se 3 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 959485 = 359807) (by norm_num)
theorem B959597 : Blo 377762 959597 := bbase (se 3 (by rfl) ⟨179924, by rfl⟩ : syracuseStep 959597 = 359849) (by norm_num)
theorem B1287413 : Blo 377762 1287413 := bbase (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) (by norm_num)
theorem B959789 : Blo 377762 959789 := bbase (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) (by norm_num)
theorem B566645 : Blo 377762 566645 := bbase (se 5 (by rfl) ⟨26561, by rfl⟩ : syracuseStep 566645 = 53123) (by norm_num)
theorem B566669 : Blo 377762 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B566693 : Blo 377762 566693 := bbase (se 4 (by rfl) ⟨53127, by rfl⟩ : syracuseStep 566693 = 106255) (by norm_num)
theorem B566717 : Blo 377762 566717 := bbase (se 3 (by rfl) ⟨106259, by rfl⟩ : syracuseStep 566717 = 212519) (by norm_num)
theorem B566741 : Blo 377762 566741 := bbase (se 7 (by rfl) ⟨6641, by rfl⟩ : syracuseStep 566741 = 13283) (by norm_num)
theorem B566765 : Blo 377762 566765 := bbase (se 3 (by rfl) ⟨106268, by rfl⟩ : syracuseStep 566765 = 212537) (by norm_num)
theorem B566789 : Blo 377762 566789 := bbase (se 4 (by rfl) ⟨53136, by rfl⟩ : syracuseStep 566789 = 106273) (by norm_num)
theorem B566813 : Blo 377762 566813 := bbase (se 3 (by rfl) ⟨106277, by rfl⟩ : syracuseStep 566813 = 212555) (by norm_num)
theorem B566837 : Blo 377762 566837 := bbase (se 5 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 566837 = 53141) (by norm_num)
theorem B566861 : Blo 377762 566861 := bbase (se 3 (by rfl) ⟨106286, by rfl⟩ : syracuseStep 566861 = 212573) (by norm_num)
theorem B566885 : Blo 377762 566885 := bbase (se 4 (by rfl) ⟨53145, by rfl⟩ : syracuseStep 566885 = 106291) (by norm_num)
theorem B566909 : Blo 377762 566909 := bbase (se 3 (by rfl) ⟨106295, by rfl⟩ : syracuseStep 566909 = 212591) (by norm_num)
theorem B960133 : Blo 377762 960133 := bbase (se 4 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 960133 = 180025) (by norm_num)
theorem B566933 : Blo 377762 566933 := bbase (se 6 (by rfl) ⟨13287, by rfl⟩ : syracuseStep 566933 = 26575) (by norm_num)
theorem B1287845 : Blo 377762 1287845 := bbase (se 4 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 1287845 = 241471) (by norm_num)
theorem B566957 : Blo 377762 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B566981 : Blo 377762 566981 := bbase (se 4 (by rfl) ⟨53154, by rfl⟩ : syracuseStep 566981 = 106309) (by norm_num)
theorem B567005 : Blo 377762 567005 := bbase (se 3 (by rfl) ⟨106313, by rfl⟩ : syracuseStep 567005 = 212627) (by norm_num)
theorem B567029 : Blo 377762 567029 := bbase (se 5 (by rfl) ⟨26579, by rfl⟩ : syracuseStep 567029 = 53159) (by norm_num)
theorem B960245 : Blo 377762 960245 := bbase (se 5 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 960245 = 90023) (by norm_num)
theorem B567053 : Blo 377762 567053 := bbase (se 3 (by rfl) ⟨106322, by rfl⟩ : syracuseStep 567053 = 212645) (by norm_num)
theorem B567077 : Blo 377762 567077 := bbase (se 4 (by rfl) ⟨53163, by rfl⟩ : syracuseStep 567077 = 106327) (by norm_num)
theorem B567101 : Blo 377762 567101 := bbase (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) (by norm_num)
theorem B567125 : Blo 377762 567125 := bbase (se 9 (by rfl) ⟨1661, by rfl⟩ : syracuseStep 567125 = 3323) (by norm_num)
theorem B567149 : Blo 377762 567149 := bbase (se 3 (by rfl) ⟨106340, by rfl⟩ : syracuseStep 567149 = 212681) (by norm_num)
theorem B567173 : Blo 377762 567173 := bbase (se 4 (by rfl) ⟨53172, by rfl⟩ : syracuseStep 567173 = 106345) (by norm_num)
theorem B567197 : Blo 377762 567197 := bbase (se 3 (by rfl) ⟨106349, by rfl⟩ : syracuseStep 567197 = 212699) (by norm_num)
theorem B567221 : Blo 377762 567221 := bbase (se 5 (by rfl) ⟨26588, by rfl⟩ : syracuseStep 567221 = 53177) (by norm_num)
theorem B960437 : Blo 377762 960437 := bbase (se 5 (by rfl) ⟨45020, by rfl⟩ : syracuseStep 960437 = 90041) (by norm_num)
theorem B567245 : Blo 377762 567245 := bbase (se 3 (by rfl) ⟨106358, by rfl⟩ : syracuseStep 567245 = 212717) (by norm_num)
theorem B567269 : Blo 377762 567269 := bbase (se 4 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 567269 = 106363) (by norm_num)
theorem B567293 : Blo 377762 567293 := bbase (se 3 (by rfl) ⟨106367, by rfl⟩ : syracuseStep 567293 = 212735) (by norm_num)
theorem B567317 : Blo 377762 567317 := bbase (se 6 (by rfl) ⟨13296, by rfl⟩ : syracuseStep 567317 = 26593) (by norm_num)
theorem B567341 : Blo 377762 567341 := bbase (se 3 (by rfl) ⟨106376, by rfl⟩ : syracuseStep 567341 = 212753) (by norm_num)
theorem B567365 : Blo 377762 567365 := bbase (se 4 (by rfl) ⟨53190, by rfl⟩ : syracuseStep 567365 = 106381) (by norm_num)
theorem B2173013 : Blo 377762 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1288277 : Blo 377762 1288277 := bbase (se 8 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 1288277 = 15097) (by norm_num)
theorem B567389 : Blo 377762 567389 := bbase (se 3 (by rfl) ⟨106385, by rfl⟩ : syracuseStep 567389 = 212771) (by norm_num)
theorem B403553 : Blo 377762 403553 := bbase (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) (by norm_num)
theorem B567413 : Blo 377762 567413 := bbase (se 5 (by rfl) ⟨26597, by rfl⟩ : syracuseStep 567413 = 53195) (by norm_num)
theorem B567437 : Blo 377762 567437 := bbase (se 3 (by rfl) ⟨106394, by rfl⟩ : syracuseStep 567437 = 212789) (by norm_num)
theorem B567461 : Blo 377762 567461 := bbase (se 4 (by rfl) ⟨53199, by rfl⟩ : syracuseStep 567461 = 106399) (by norm_num)
theorem B567485 : Blo 377762 567485 := bbase (se 3 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 567485 = 212807) (by norm_num)
theorem B567509 : Blo 377762 567509 := bbase (se 7 (by rfl) ⟨6650, by rfl⟩ : syracuseStep 567509 = 13301) (by norm_num)
theorem B567533 : Blo 377762 567533 := bbase (se 3 (by rfl) ⟨106412, by rfl⟩ : syracuseStep 567533 = 212825) (by norm_num)
theorem B567557 : Blo 377762 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B960781 : Blo 377762 960781 := bbase (se 3 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 960781 = 360293) (by norm_num)
theorem B403741 : Blo 377762 403741 := bbase (se 3 (by rfl) ⟨75701, by rfl⟩ : syracuseStep 403741 = 151403) (by norm_num)
theorem B567581 : Blo 377762 567581 := bbase (se 3 (by rfl) ⟨106421, by rfl⟩ : syracuseStep 567581 = 212843) (by norm_num)
theorem B3451189 : Blo 377762 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B567605 : Blo 377762 567605 := bbase (se 5 (by rfl) ⟨26606, by rfl⟩ : syracuseStep 567605 = 53213) (by norm_num)
theorem B567629 : Blo 377762 567629 := bbase (se 3 (by rfl) ⟨106430, by rfl⟩ : syracuseStep 567629 = 212861) (by norm_num)
theorem B567653 : Blo 377762 567653 := bbase (se 4 (by rfl) ⟨53217, by rfl⟩ : syracuseStep 567653 = 106435) (by norm_num)
theorem B567677 : Blo 377762 567677 := bbase (se 3 (by rfl) ⟨106439, by rfl⟩ : syracuseStep 567677 = 212879) (by norm_num)
theorem B960893 : Blo 377762 960893 := bbase (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) (by norm_num)
theorem B567701 : Blo 377762 567701 := bbase (se 6 (by rfl) ⟨13305, by rfl⟩ : syracuseStep 567701 = 26611) (by norm_num)
theorem B567725 : Blo 377762 567725 := bbase (se 3 (by rfl) ⟨106448, by rfl⟩ : syracuseStep 567725 = 212897) (by norm_num)
theorem B567749 : Blo 377762 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B567773 : Blo 377762 567773 := bbase (se 3 (by rfl) ⟨106457, by rfl⟩ : syracuseStep 567773 = 212915) (by norm_num)
theorem B567797 : Blo 377762 567797 := bbase (se 5 (by rfl) ⟨26615, by rfl⟩ : syracuseStep 567797 = 53231) (by norm_num)
theorem B567821 : Blo 377762 567821 := bbase (se 3 (by rfl) ⟨106466, by rfl⟩ : syracuseStep 567821 = 212933) (by norm_num)
theorem B567845 : Blo 377762 567845 := bbase (se 4 (by rfl) ⟨53235, by rfl⟩ : syracuseStep 567845 = 106471) (by norm_num)
theorem B567869 : Blo 377762 567869 := bbase (se 3 (by rfl) ⟨106475, by rfl⟩ : syracuseStep 567869 = 212951) (by norm_num)
theorem B961085 : Blo 377762 961085 := bbase (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) (by norm_num)
theorem B567893 : Blo 377762 567893 := bbase (se 8 (by rfl) ⟨3327, by rfl⟩ : syracuseStep 567893 = 6655) (by norm_num)
theorem B567917 : Blo 377762 567917 := bbase (se 3 (by rfl) ⟨106484, by rfl⟩ : syracuseStep 567917 = 212969) (by norm_num)
theorem B567941 : Blo 377762 567941 := bbase (se 4 (by rfl) ⟨53244, by rfl⟩ : syracuseStep 567941 = 106489) (by norm_num)
theorem B567965 : Blo 377762 567965 := bbase (se 3 (by rfl) ⟨106493, by rfl⟩ : syracuseStep 567965 = 212987) (by norm_num)
theorem B567989 : Blo 377762 567989 := bbase (se 5 (by rfl) ⟨26624, by rfl⟩ : syracuseStep 567989 = 53249) (by norm_num)
theorem B568013 : Blo 377762 568013 := bbase (se 3 (by rfl) ⟨106502, by rfl⟩ : syracuseStep 568013 = 213005) (by norm_num)
theorem B568037 : Blo 377762 568037 := bbase (se 4 (by rfl) ⟨53253, by rfl⟩ : syracuseStep 568037 = 106507) (by norm_num)
theorem B568061 : Blo 377762 568061 := bbase (se 3 (by rfl) ⟨106511, by rfl⟩ : syracuseStep 568061 = 213023) (by norm_num)
theorem B568085 : Blo 377762 568085 := bbase (se 6 (by rfl) ⟨13314, by rfl⟩ : syracuseStep 568085 = 26629) (by norm_num)
theorem B568109 : Blo 377762 568109 := bbase (se 3 (by rfl) ⟨106520, by rfl⟩ : syracuseStep 568109 = 213041) (by norm_num)
theorem B568133 : Blo 377762 568133 := bbase (se 4 (by rfl) ⟨53262, by rfl⟩ : syracuseStep 568133 = 106525) (by norm_num)
theorem B568157 : Blo 377762 568157 := bbase (se 3 (by rfl) ⟨106529, by rfl⟩ : syracuseStep 568157 = 213059) (by norm_num)
theorem B568181 : Blo 377762 568181 := bbase (se 5 (by rfl) ⟨26633, by rfl⟩ : syracuseStep 568181 = 53267) (by norm_num)
theorem B568205 : Blo 377762 568205 := bbase (se 3 (by rfl) ⟨106538, by rfl⟩ : syracuseStep 568205 = 213077) (by norm_num)
theorem B961429 : Blo 377762 961429 := bbase (se 6 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 961429 = 45067) (by norm_num)
theorem B568229 : Blo 377762 568229 := bbase (se 4 (by rfl) ⟨53271, by rfl⟩ : syracuseStep 568229 = 106543) (by norm_num)
theorem B568253 : Blo 377762 568253 := bbase (se 3 (by rfl) ⟨106547, by rfl⟩ : syracuseStep 568253 = 213095) (by norm_num)
theorem B1158085 : Blo 377762 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B568277 : Blo 377762 568277 := bbase (se 7 (by rfl) ⟨6659, by rfl⟩ : syracuseStep 568277 = 13319) (by norm_num)
theorem B568301 : Blo 377762 568301 := bbase (se 3 (by rfl) ⟨106556, by rfl⟩ : syracuseStep 568301 = 213113) (by norm_num)
theorem B568325 : Blo 377762 568325 := bbase (se 4 (by rfl) ⟨53280, by rfl⟩ : syracuseStep 568325 = 106561) (by norm_num)
theorem B961541 : Blo 377762 961541 := bbase (se 4 (by rfl) ⟨90144, by rfl⟩ : syracuseStep 961541 = 180289) (by norm_num)
theorem B568349 : Blo 377762 568349 := bbase (se 3 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 568349 = 213131) (by norm_num)
theorem B568373 : Blo 377762 568373 := bbase (se 5 (by rfl) ⟨26642, by rfl⟩ : syracuseStep 568373 = 53285) (by norm_num)
theorem B3255349 : Blo 377762 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B568397 : Blo 377762 568397 := bbase (se 3 (by rfl) ⟨106574, by rfl⟩ : syracuseStep 568397 = 213149) (by norm_num)
theorem B404561 : Blo 377762 404561 := bbase (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) (by norm_num)
theorem B568421 : Blo 377762 568421 := bbase (se 4 (by rfl) ⟨53289, by rfl⟩ : syracuseStep 568421 = 106579) (by norm_num)
theorem B1617013 : Blo 377762 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B568445 : Blo 377762 568445 := bbase (se 3 (by rfl) ⟨106583, by rfl⟩ : syracuseStep 568445 = 213167) (by norm_num)
theorem B568469 : Blo 377762 568469 := bbase (se 6 (by rfl) ⟨13323, by rfl⟩ : syracuseStep 568469 = 26647) (by norm_num)
theorem B568493 : Blo 377762 568493 := bbase (se 3 (by rfl) ⟨106592, by rfl⟩ : syracuseStep 568493 = 213185) (by norm_num)
theorem B568517 : Blo 377762 568517 := bbase (se 4 (by rfl) ⟨53298, by rfl⟩ : syracuseStep 568517 = 106597) (by norm_num)
theorem B961733 : Blo 377762 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B568541 : Blo 377762 568541 := bbase (se 3 (by rfl) ⟨106601, by rfl⟩ : syracuseStep 568541 = 213203) (by norm_num)
theorem B928997 : Blo 377762 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B568565 : Blo 377762 568565 := bbase (se 5 (by rfl) ⟨26651, by rfl⟩ : syracuseStep 568565 = 53303) (by norm_num)
theorem B568589 : Blo 377762 568589 := bbase (se 3 (by rfl) ⟨106610, by rfl⟩ : syracuseStep 568589 = 213221) (by norm_num)
theorem B568613 : Blo 377762 568613 := bbase (se 4 (by rfl) ⟨53307, by rfl⟩ : syracuseStep 568613 = 106615) (by norm_num)
theorem B568637 : Blo 377762 568637 := bbase (se 3 (by rfl) ⟨106619, by rfl⟩ : syracuseStep 568637 = 213239) (by norm_num)
theorem B568661 : Blo 377762 568661 := bbase (se 11 (by rfl) ⟨416, by rfl⟩ : syracuseStep 568661 = 833) (by norm_num)
theorem B568685 : Blo 377762 568685 := bbase (se 3 (by rfl) ⟨106628, by rfl⟩ : syracuseStep 568685 = 213257) (by norm_num)
theorem B568709 : Blo 377762 568709 := bbase (se 4 (by rfl) ⟨53316, by rfl⟩ : syracuseStep 568709 = 106633) (by norm_num)
theorem B568733 : Blo 377762 568733 := bbase (se 3 (by rfl) ⟨106637, by rfl⟩ : syracuseStep 568733 = 213275) (by norm_num)
theorem B568757 : Blo 377762 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B568781 : Blo 377762 568781 := bbase (se 3 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 568781 = 213293) (by norm_num)
theorem B568805 : Blo 377762 568805 := bbase (se 4 (by rfl) ⟨53325, by rfl⟩ : syracuseStep 568805 = 106651) (by norm_num)
theorem B568829 : Blo 377762 568829 := bbase (se 3 (by rfl) ⟨106655, by rfl⟩ : syracuseStep 568829 = 213311) (by norm_num)
theorem B405005 : Blo 377762 405005 := bbase (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) (by norm_num)
theorem B568853 : Blo 377762 568853 := bbase (se 6 (by rfl) ⟨13332, by rfl⟩ : syracuseStep 568853 = 26665) (by norm_num)
theorem B962077 : Blo 377762 962077 := bbase (se 3 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 962077 = 360779) (by norm_num)
theorem B568877 : Blo 377762 568877 := bbase (se 3 (by rfl) ⟨106664, by rfl⟩ : syracuseStep 568877 = 213329) (by norm_num)
theorem B568901 : Blo 377762 568901 := bbase (se 4 (by rfl) ⟨53334, by rfl⟩ : syracuseStep 568901 = 106669) (by norm_num)
theorem B568925 : Blo 377762 568925 := bbase (se 3 (by rfl) ⟨106673, by rfl⟩ : syracuseStep 568925 = 213347) (by norm_num)
theorem B568949 : Blo 377762 568949 := bbase (se 5 (by rfl) ⟨26669, by rfl⟩ : syracuseStep 568949 = 53339) (by norm_num)
theorem B568973 : Blo 377762 568973 := bbase (se 3 (by rfl) ⟨106682, by rfl⟩ : syracuseStep 568973 = 213365) (by norm_num)
theorem B962189 : Blo 377762 962189 := bbase (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) (by norm_num)
theorem B568997 : Blo 377762 568997 := bbase (se 4 (by rfl) ⟨53343, by rfl⟩ : syracuseStep 568997 = 106687) (by norm_num)
theorem B1027765 : Blo 377762 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B700093 : Blo 377762 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B569021 : Blo 377762 569021 := bbase (se 3 (by rfl) ⟨106691, by rfl⟩ : syracuseStep 569021 = 213383) (by norm_num)
theorem B569045 : Blo 377762 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B1388261 : Blo 377762 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B569069 : Blo 377762 569069 := bbase (se 3 (by rfl) ⟨106700, by rfl⟩ : syracuseStep 569069 = 213401) (by norm_num)
theorem B569093 : Blo 377762 569093 := bbase (se 4 (by rfl) ⟨53352, by rfl⟩ : syracuseStep 569093 = 106705) (by norm_num)
theorem B405253 : Blo 377762 405253 := bbase (se 4 (by rfl) ⟨37992, by rfl⟩ : syracuseStep 405253 = 75985) (by norm_num)
theorem B569117 : Blo 377762 569117 := bbase (se 3 (by rfl) ⟨106709, by rfl⟩ : syracuseStep 569117 = 213419) (by norm_num)
theorem B569141 : Blo 377762 569141 := bbase (se 5 (by rfl) ⟨26678, by rfl⟩ : syracuseStep 569141 = 53357) (by norm_num)
theorem B569165 : Blo 377762 569165 := bbase (se 3 (by rfl) ⟨106718, by rfl⟩ : syracuseStep 569165 = 213437) (by norm_num)
theorem B962381 : Blo 377762 962381 := bbase (se 3 (by rfl) ⟨180446, by rfl⟩ : syracuseStep 962381 = 360893) (by norm_num)
theorem B569189 : Blo 377762 569189 := bbase (se 4 (by rfl) ⟨53361, by rfl⟩ : syracuseStep 569189 = 106723) (by norm_num)
theorem B569213 : Blo 377762 569213 := bbase (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) (by norm_num)
theorem B569237 : Blo 377762 569237 := bbase (se 6 (by rfl) ⟨13341, by rfl⟩ : syracuseStep 569237 = 26683) (by norm_num)
theorem B569261 : Blo 377762 569261 := bbase (se 3 (by rfl) ⟨106736, by rfl⟩ : syracuseStep 569261 = 213473) (by norm_num)
theorem B765893 : Blo 377762 765893 := bbase (se 4 (by rfl) ⟨71802, by rfl⟩ : syracuseStep 765893 = 143605) (by norm_num)
theorem B569285 : Blo 377762 569285 := bbase (se 4 (by rfl) ⟨53370, by rfl⟩ : syracuseStep 569285 = 106741) (by norm_num)
theorem B569309 : Blo 377762 569309 := bbase (se 3 (by rfl) ⟨106745, by rfl⟩ : syracuseStep 569309 = 213491) (by norm_num)
theorem B569333 : Blo 377762 569333 := bbase (se 5 (by rfl) ⟨26687, by rfl⟩ : syracuseStep 569333 = 53375) (by norm_num)
theorem B569357 : Blo 377762 569357 := bbase (se 3 (by rfl) ⟨106754, by rfl⟩ : syracuseStep 569357 = 213509) (by norm_num)
theorem B569381 : Blo 377762 569381 := bbase (se 4 (by rfl) ⟨53379, by rfl⟩ : syracuseStep 569381 = 106759) (by norm_num)
theorem B569405 : Blo 377762 569405 := bbase (se 3 (by rfl) ⟨106763, by rfl⟩ : syracuseStep 569405 = 213527) (by norm_num)
theorem B569429 : Blo 377762 569429 := bbase (se 8 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 569429 = 6673) (by norm_num)
theorem B569453 : Blo 377762 569453 := bbase (se 3 (by rfl) ⟨106772, by rfl⟩ : syracuseStep 569453 = 213545) (by norm_num)
theorem B569477 : Blo 377762 569477 := bbase (se 4 (by rfl) ⟨53388, by rfl⟩ : syracuseStep 569477 = 106777) (by norm_num)
theorem B569501 : Blo 377762 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B962725 : Blo 377762 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B569525 : Blo 377762 569525 := bbase (se 5 (by rfl) ⟨26696, by rfl⟩ : syracuseStep 569525 = 53393) (by norm_num)
theorem B405685 : Blo 377762 405685 := bbase (se 5 (by rfl) ⟨19016, by rfl⟩ : syracuseStep 405685 = 38033) (by norm_num)
theorem B569549 : Blo 377762 569549 := bbase (se 3 (by rfl) ⟨106790, by rfl⟩ : syracuseStep 569549 = 213581) (by norm_num)
theorem B569573 : Blo 377762 569573 := bbase (se 4 (by rfl) ⟨53397, by rfl⟩ : syracuseStep 569573 = 106795) (by norm_num)
theorem B569597 : Blo 377762 569597 := bbase (se 3 (by rfl) ⟨106799, by rfl⟩ : syracuseStep 569597 = 213599) (by norm_num)
theorem B405757 : Blo 377762 405757 := bbase (se 3 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 405757 = 152159) (by norm_num)
theorem B1454357 : Blo 377762 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B569621 : Blo 377762 569621 := bbase (se 6 (by rfl) ⟨13350, by rfl⟩ : syracuseStep 569621 = 26701) (by norm_num)
theorem B962837 : Blo 377762 962837 := bbase (se 6 (by rfl) ⟨22566, by rfl⟩ : syracuseStep 962837 = 45133) (by norm_num)
theorem B569645 : Blo 377762 569645 := bbase (se 3 (by rfl) ⟨106808, by rfl⟩ : syracuseStep 569645 = 213617) (by norm_num)
theorem B569669 : Blo 377762 569669 := bbase (se 4 (by rfl) ⟨53406, by rfl⟩ : syracuseStep 569669 = 106813) (by norm_num)
theorem B569693 : Blo 377762 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B569717 : Blo 377762 569717 := bbase (se 5 (by rfl) ⟨26705, by rfl⟩ : syracuseStep 569717 = 53411) (by norm_num)
theorem B569741 : Blo 377762 569741 := bbase (se 3 (by rfl) ⟨106826, by rfl⟩ : syracuseStep 569741 = 213653) (by norm_num)
theorem B569765 : Blo 377762 569765 := bbase (se 4 (by rfl) ⟨53415, by rfl⟩ : syracuseStep 569765 = 106831) (by norm_num)
theorem B569789 : Blo 377762 569789 := bbase (se 3 (by rfl) ⟨106835, by rfl⟩ : syracuseStep 569789 = 213671) (by norm_num)
theorem B569813 : Blo 377762 569813 := bbase (se 7 (by rfl) ⟨6677, by rfl⟩ : syracuseStep 569813 = 13355) (by norm_num)
theorem B963029 : Blo 377762 963029 := bbase (se 7 (by rfl) ⟨11285, by rfl⟩ : syracuseStep 963029 = 22571) (by norm_num)
theorem B569837 : Blo 377762 569837 := bbase (se 3 (by rfl) ⟨106844, by rfl⟩ : syracuseStep 569837 = 213689) (by norm_num)
theorem B569861 : Blo 377762 569861 := bbase (se 4 (by rfl) ⟨53424, by rfl⟩ : syracuseStep 569861 = 106849) (by norm_num)
theorem B569885 : Blo 377762 569885 := bbase (se 3 (by rfl) ⟨106853, by rfl⟩ : syracuseStep 569885 = 213707) (by norm_num)
theorem B1913381 : Blo 377762 1913381 := bbase (se 4 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 1913381 = 358759) (by norm_num)
theorem B569909 : Blo 377762 569909 := bbase (se 5 (by rfl) ⟨26714, by rfl⟩ : syracuseStep 569909 = 53429) (by norm_num)
theorem B1618501 : Blo 377762 1618501 := bbase (se 4 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 1618501 = 303469) (by norm_num)
theorem B569933 : Blo 377762 569933 := bbase (se 3 (by rfl) ⟨106862, by rfl⟩ : syracuseStep 569933 = 213725) (by norm_num)
theorem B1618517 : Blo 377762 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B569957 : Blo 377762 569957 := bbase (se 4 (by rfl) ⟨53433, by rfl⟩ : syracuseStep 569957 = 106867) (by norm_num)
theorem B406129 : Blo 377762 406129 := bbase (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) (by norm_num)
theorem B569981 : Blo 377762 569981 := bbase (se 3 (by rfl) ⟨106871, by rfl⟩ : syracuseStep 569981 = 213743) (by norm_num)
theorem B570005 : Blo 377762 570005 := bbase (se 6 (by rfl) ⟨13359, by rfl⟩ : syracuseStep 570005 = 26719) (by norm_num)
theorem B570029 : Blo 377762 570029 := bbase (se 3 (by rfl) ⟨106880, by rfl⟩ : syracuseStep 570029 = 213761) (by norm_num)
theorem B570053 : Blo 377762 570053 := bbase (se 4 (by rfl) ⟨53442, by rfl⟩ : syracuseStep 570053 = 106885) (by norm_num)
theorem B570077 : Blo 377762 570077 := bbase (se 3 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 570077 = 213779) (by norm_num)
theorem B570101 : Blo 377762 570101 := bbase (se 5 (by rfl) ⟨26723, by rfl⟩ : syracuseStep 570101 = 53447) (by norm_num)
theorem B570125 : Blo 377762 570125 := bbase (se 3 (by rfl) ⟨106898, by rfl⟩ : syracuseStep 570125 = 213797) (by norm_num)
theorem B1946389 : Blo 377762 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B570149 : Blo 377762 570149 := bbase (se 4 (by rfl) ⟨53451, by rfl⟩ : syracuseStep 570149 = 106903) (by norm_num)
theorem B963373 : Blo 377762 963373 := bbase (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) (by norm_num)
theorem B570173 : Blo 377762 570173 := bbase (se 3 (by rfl) ⟨106907, by rfl⟩ : syracuseStep 570173 = 213815) (by norm_num)
theorem B1028933 : Blo 377762 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B570197 : Blo 377762 570197 := bbase (se 9 (by rfl) ⟨1670, by rfl⟩ : syracuseStep 570197 = 3341) (by norm_num)
theorem B1160021 : Blo 377762 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B570221 : Blo 377762 570221 := bbase (se 3 (by rfl) ⟨106916, by rfl⟩ : syracuseStep 570221 = 213833) (by norm_num)
theorem B570245 : Blo 377762 570245 := bbase (se 4 (by rfl) ⟨53460, by rfl⟩ : syracuseStep 570245 = 106921) (by norm_num)
theorem B570269 : Blo 377762 570269 := bbase (se 3 (by rfl) ⟨106925, by rfl⟩ : syracuseStep 570269 = 213851) (by norm_num)
theorem B963485 : Blo 377762 963485 := bbase (se 3 (by rfl) ⟨180653, by rfl⟩ : syracuseStep 963485 = 361307) (by norm_num)
theorem B570293 : Blo 377762 570293 := bbase (se 5 (by rfl) ⟨26732, by rfl⟩ : syracuseStep 570293 = 53465) (by norm_num)
theorem B570317 : Blo 377762 570317 := bbase (se 3 (by rfl) ⟨106934, by rfl⟩ : syracuseStep 570317 = 213869) (by norm_num)
theorem B570341 : Blo 377762 570341 := bbase (se 4 (by rfl) ⟨53469, by rfl⟩ : syracuseStep 570341 = 106939) (by norm_num)
theorem B406505 : Blo 377762 406505 := bbase (se 2 (by rfl) ⟨152439, by rfl⟩ : syracuseStep 406505 = 304879) (by norm_num)
theorem B3257333 : Blo 377762 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B570365 : Blo 377762 570365 := bbase (se 3 (by rfl) ⟨106943, by rfl⟩ : syracuseStep 570365 = 213887) (by norm_num)
theorem B766997 : Blo 377762 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B570389 : Blo 377762 570389 := bbase (se 6 (by rfl) ⟨13368, by rfl⟩ : syracuseStep 570389 = 26737) (by norm_num)
theorem B570413 : Blo 377762 570413 := bbase (se 3 (by rfl) ⟨106952, by rfl⟩ : syracuseStep 570413 = 213905) (by norm_num)
theorem B406577 : Blo 377762 406577 := bbase (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) (by norm_num)
theorem B1815605 : Blo 377762 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B570437 : Blo 377762 570437 := bbase (se 4 (by rfl) ⟨53478, by rfl⟩ : syracuseStep 570437 = 106957) (by norm_num)
theorem B570461 : Blo 377762 570461 := bbase (se 3 (by rfl) ⟨106961, by rfl⟩ : syracuseStep 570461 = 213923) (by norm_num)
theorem B963677 : Blo 377762 963677 := bbase (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) (by norm_num)
theorem B570485 : Blo 377762 570485 := bbase (se 5 (by rfl) ⟨26741, by rfl⟩ : syracuseStep 570485 = 53483) (by norm_num)
theorem B570509 : Blo 377762 570509 := bbase (se 3 (by rfl) ⟨106970, by rfl⟩ : syracuseStep 570509 = 213941) (by norm_num)
theorem B2897045 : Blo 377762 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B570533 : Blo 377762 570533 := bbase (se 4 (by rfl) ⟨53487, by rfl⟩ : syracuseStep 570533 = 106975) (by norm_num)
theorem B570557 : Blo 377762 570557 := bbase (se 3 (by rfl) ⟨106979, by rfl⟩ : syracuseStep 570557 = 213959) (by norm_num)
theorem B570581 : Blo 377762 570581 := bbase (se 7 (by rfl) ⟨6686, by rfl⟩ : syracuseStep 570581 = 13373) (by norm_num)
theorem B570605 : Blo 377762 570605 := bbase (se 3 (by rfl) ⟨106988, by rfl⟩ : syracuseStep 570605 = 213977) (by norm_num)
theorem B406765 : Blo 377762 406765 := bbase (se 3 (by rfl) ⟨76268, by rfl⟩ : syracuseStep 406765 = 152537) (by norm_num)
theorem B570629 : Blo 377762 570629 := bbase (se 4 (by rfl) ⟨53496, by rfl⟩ : syracuseStep 570629 = 106993) (by norm_num)
theorem B537877 : Blo 377762 537877 := bbase (se 6 (by rfl) ⟨12606, by rfl⟩ : syracuseStep 537877 = 25213) (by norm_num)
theorem B570653 : Blo 377762 570653 := bbase (se 3 (by rfl) ⟨106997, by rfl⟩ : syracuseStep 570653 = 213995) (by norm_num)
theorem B570677 : Blo 377762 570677 := bbase (se 5 (by rfl) ⟨26750, by rfl⟩ : syracuseStep 570677 = 53501) (by norm_num)
theorem B570701 : Blo 377762 570701 := bbase (se 3 (by rfl) ⟨107006, by rfl⟩ : syracuseStep 570701 = 214013) (by norm_num)
theorem B865637 : Blo 377762 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B570725 : Blo 377762 570725 := bbase (se 4 (by rfl) ⟨53505, by rfl⟩ : syracuseStep 570725 = 107011) (by norm_num)
theorem B1095029 : Blo 377762 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B570749 : Blo 377762 570749 := bbase (se 3 (by rfl) ⟨107015, by rfl⟩ : syracuseStep 570749 = 214031) (by norm_num)
theorem B537997 : Blo 377762 537997 := bbase (se 3 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 537997 = 201749) (by norm_num)
theorem B570773 : Blo 377762 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B406949 : Blo 377762 406949 := bbase (se 4 (by rfl) ⟨38151, by rfl⟩ : syracuseStep 406949 = 76303) (by norm_num)
theorem B570797 : Blo 377762 570797 := bbase (se 3 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 570797 = 214049) (by norm_num)
theorem B964021 : Blo 377762 964021 := bbase (se 5 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 964021 = 90377) (by norm_num)
theorem B570821 : Blo 377762 570821 := bbase (se 4 (by rfl) ⟨53514, by rfl⟩ : syracuseStep 570821 = 107029) (by norm_num)
theorem B570845 : Blo 377762 570845 := bbase (se 3 (by rfl) ⟨107033, by rfl⟩ : syracuseStep 570845 = 214067) (by norm_num)
theorem B538093 : Blo 377762 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B570869 : Blo 377762 570869 := bbase (se 5 (by rfl) ⟨26759, by rfl⟩ : syracuseStep 570869 = 53519) (by norm_num)
theorem B570893 : Blo 377762 570893 := bbase (se 3 (by rfl) ⟨107042, by rfl⟩ : syracuseStep 570893 = 214085) (by norm_num)
theorem B570917 : Blo 377762 570917 := bbase (se 4 (by rfl) ⟨53523, by rfl⟩ : syracuseStep 570917 = 107047) (by norm_num)
theorem B964133 : Blo 377762 964133 := bbase (se 4 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 964133 = 180775) (by norm_num)
theorem B767549 : Blo 377762 767549 := bbase (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) (by norm_num)
theorem B570941 : Blo 377762 570941 := bbase (se 3 (by rfl) ⟨107051, by rfl⟩ : syracuseStep 570941 = 214103) (by norm_num)
theorem B570965 : Blo 377762 570965 := bbase (se 8 (by rfl) ⟨3345, by rfl⟩ : syracuseStep 570965 = 6691) (by norm_num)
theorem B570989 : Blo 377762 570989 := bbase (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) (by norm_num)
theorem B571013 : Blo 377762 571013 := bbase (se 4 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 571013 = 107065) (by norm_num)
theorem B571037 : Blo 377762 571037 := bbase (se 3 (by rfl) ⟨107069, by rfl⟩ : syracuseStep 571037 = 214139) (by norm_num)
theorem B571061 : Blo 377762 571061 := bbase (se 5 (by rfl) ⟨26768, by rfl⟩ : syracuseStep 571061 = 53537) (by norm_num)
theorem B571085 : Blo 377762 571085 := bbase (se 3 (by rfl) ⟨107078, by rfl⟩ : syracuseStep 571085 = 214157) (by norm_num)
theorem B571109 : Blo 377762 571109 := bbase (se 4 (by rfl) ⟨53541, by rfl⟩ : syracuseStep 571109 = 107083) (by norm_num)
theorem B964325 : Blo 377762 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B571133 : Blo 377762 571133 := bbase (se 3 (by rfl) ⟨107087, by rfl⟩ : syracuseStep 571133 = 214175) (by norm_num)
theorem B571157 : Blo 377762 571157 := bbase (se 6 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 571157 = 26773) (by norm_num)
theorem B571181 : Blo 377762 571181 := bbase (se 3 (by rfl) ⟨107096, by rfl⟩ : syracuseStep 571181 = 214193) (by norm_num)
theorem B1914677 : Blo 377762 1914677 := bbase (se 5 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 1914677 = 179501) (by norm_num)
theorem B571205 : Blo 377762 571205 := bbase (se 4 (by rfl) ⟨53550, by rfl⟩ : syracuseStep 571205 = 107101) (by norm_num)
theorem B571229 : Blo 377762 571229 := bbase (se 3 (by rfl) ⟨107105, by rfl⟩ : syracuseStep 571229 = 214211) (by norm_num)
theorem B571253 : Blo 377762 571253 := bbase (se 5 (by rfl) ⟨26777, by rfl⟩ : syracuseStep 571253 = 53555) (by norm_num)
theorem B571277 : Blo 377762 571277 := bbase (se 3 (by rfl) ⟨107114, by rfl⟩ : syracuseStep 571277 = 214229) (by norm_num)
theorem B571301 : Blo 377762 571301 := bbase (se 4 (by rfl) ⟨53559, by rfl⟩ : syracuseStep 571301 = 107119) (by norm_num)
theorem B571325 : Blo 377762 571325 := bbase (se 3 (by rfl) ⟨107123, by rfl⟩ : syracuseStep 571325 = 214247) (by norm_num)
theorem B571349 : Blo 377762 571349 := bbase (se 7 (by rfl) ⟨6695, by rfl⟩ : syracuseStep 571349 = 13391) (by norm_num)
theorem B538589 : Blo 377762 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B571373 : Blo 377762 571373 := bbase (se 3 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 571373 = 214265) (by norm_num)
theorem B571397 : Blo 377762 571397 := bbase (se 4 (by rfl) ⟨53568, by rfl⟩ : syracuseStep 571397 = 107137) (by norm_num)
theorem B571421 : Blo 377762 571421 := bbase (se 3 (by rfl) ⟨107141, by rfl⟩ : syracuseStep 571421 = 214283) (by norm_num)
theorem B571445 : Blo 377762 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B964669 : Blo 377762 964669 := bbase (se 3 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 964669 = 361751) (by norm_num)
theorem B571469 : Blo 377762 571469 := bbase (se 3 (by rfl) ⟨107150, by rfl⟩ : syracuseStep 571469 = 214301) (by norm_num)
theorem B571493 : Blo 377762 571493 := bbase (se 4 (by rfl) ⟨53577, by rfl⟩ : syracuseStep 571493 = 107155) (by norm_num)
theorem B571517 : Blo 377762 571517 := bbase (se 3 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 571517 = 214319) (by norm_num)
theorem B571541 : Blo 377762 571541 := bbase (se 6 (by rfl) ⟨13395, by rfl⟩ : syracuseStep 571541 = 26791) (by norm_num)
theorem B571565 : Blo 377762 571565 := bbase (se 3 (by rfl) ⟨107168, by rfl⟩ : syracuseStep 571565 = 214337) (by norm_num)
theorem B964781 : Blo 377762 964781 := bbase (se 3 (by rfl) ⟨180896, by rfl⟩ : syracuseStep 964781 = 361793) (by norm_num)
theorem B571589 : Blo 377762 571589 := bbase (se 4 (by rfl) ⟨53586, by rfl⟩ : syracuseStep 571589 = 107173) (by norm_num)
theorem B571613 : Blo 377762 571613 := bbase (se 3 (by rfl) ⟨107177, by rfl⟩ : syracuseStep 571613 = 214355) (by norm_num)
theorem B571637 : Blo 377762 571637 := bbase (se 5 (by rfl) ⟨26795, by rfl⟩ : syracuseStep 571637 = 53591) (by norm_num)
theorem B571661 : Blo 377762 571661 := bbase (se 3 (by rfl) ⟨107186, by rfl⟩ : syracuseStep 571661 = 214373) (by norm_num)
theorem B571685 : Blo 377762 571685 := bbase (se 4 (by rfl) ⟨53595, by rfl⟩ : syracuseStep 571685 = 107191) (by norm_num)
theorem B571709 : Blo 377762 571709 := bbase (se 3 (by rfl) ⟨107195, by rfl⟩ : syracuseStep 571709 = 214391) (by norm_num)
theorem B571733 : Blo 377762 571733 := bbase (se 10 (by rfl) ⟨837, by rfl⟩ : syracuseStep 571733 = 1675) (by norm_num)
theorem B571757 : Blo 377762 571757 := bbase (se 3 (by rfl) ⟨107204, by rfl⟩ : syracuseStep 571757 = 214409) (by norm_num)
theorem B964973 : Blo 377762 964973 := bbase (se 3 (by rfl) ⟨180932, by rfl⟩ : syracuseStep 964973 = 361865) (by norm_num)
theorem B1227125 : Blo 377762 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B571781 : Blo 377762 571781 := bbase (se 4 (by rfl) ⟨53604, by rfl⟩ : syracuseStep 571781 = 107209) (by norm_num)
theorem B571805 : Blo 377762 571805 := bbase (se 3 (by rfl) ⟨107213, by rfl⟩ : syracuseStep 571805 = 214427) (by norm_num)
theorem B702893 : Blo 377762 702893 := bbase (se 3 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 702893 = 263585) (by norm_num)
theorem B571829 : Blo 377762 571829 := bbase (se 5 (by rfl) ⟨26804, by rfl⟩ : syracuseStep 571829 = 53609) (by norm_num)
theorem B571853 : Blo 377762 571853 := bbase (se 3 (by rfl) ⟨107222, by rfl⟩ : syracuseStep 571853 = 214445) (by norm_num)
theorem B571877 : Blo 377762 571877 := bbase (se 4 (by rfl) ⟨53613, by rfl⟩ : syracuseStep 571877 = 107227) (by norm_num)
theorem B571901 : Blo 377762 571901 := bbase (se 3 (by rfl) ⟨107231, by rfl⟩ : syracuseStep 571901 = 214463) (by norm_num)
theorem B539141 : Blo 377762 539141 := bbase (se 4 (by rfl) ⟨50544, by rfl⟩ : syracuseStep 539141 = 101089) (by norm_num)
theorem B571925 : Blo 377762 571925 := bbase (se 6 (by rfl) ⟨13404, by rfl⟩ : syracuseStep 571925 = 26809) (by norm_num)
theorem B571949 : Blo 377762 571949 := bbase (se 3 (by rfl) ⟨107240, by rfl⟩ : syracuseStep 571949 = 214481) (by norm_num)
theorem B571973 : Blo 377762 571973 := bbase (se 4 (by rfl) ⟨53622, by rfl⟩ : syracuseStep 571973 = 107245) (by norm_num)
theorem B637517 : Blo 377762 637517 := bbase (se 3 (by rfl) ⟨119534, by rfl⟩ : syracuseStep 637517 = 239069) (by norm_num)
theorem B571997 : Blo 377762 571997 := bbase (se 3 (by rfl) ⟨107249, by rfl⟩ : syracuseStep 571997 = 214499) (by norm_num)
theorem B572021 : Blo 377762 572021 := bbase (se 5 (by rfl) ⟨26813, by rfl⟩ : syracuseStep 572021 = 53627) (by norm_num)
theorem B572045 : Blo 377762 572045 := bbase (se 3 (by rfl) ⟨107258, by rfl⟩ : syracuseStep 572045 = 214517) (by norm_num)
theorem B572069 : Blo 377762 572069 := bbase (se 4 (by rfl) ⟨53631, by rfl⟩ : syracuseStep 572069 = 107263) (by norm_num)
theorem B572093 : Blo 377762 572093 := bbase (se 3 (by rfl) ⟨107267, by rfl⟩ : syracuseStep 572093 = 214535) (by norm_num)
theorem B965317 : Blo 377762 965317 := bbase (se 4 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 965317 = 180997) (by norm_num)
theorem B637645 : Blo 377762 637645 := bbase (se 3 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 637645 = 239117) (by norm_num)
theorem B572117 : Blo 377762 572117 := bbase (se 7 (by rfl) ⟨6704, by rfl⟩ : syracuseStep 572117 = 13409) (by norm_num)
theorem B572141 : Blo 377762 572141 := bbase (se 3 (by rfl) ⟨107276, by rfl⟩ : syracuseStep 572141 = 214553) (by norm_num)
theorem B572165 : Blo 377762 572165 := bbase (se 4 (by rfl) ⟨53640, by rfl⟩ : syracuseStep 572165 = 107281) (by norm_num)
theorem B572189 : Blo 377762 572189 := bbase (se 3 (by rfl) ⟨107285, by rfl⟩ : syracuseStep 572189 = 214571) (by norm_num)
theorem B637733 : Blo 377762 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B1620773 : Blo 377762 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B473897 : Blo 377762 473897 := bbase (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) (by norm_num)
theorem B965429 : Blo 377762 965429 := bbase (se 5 (by rfl) ⟨45254, by rfl⟩ : syracuseStep 965429 = 90509) (by norm_num)
theorem B572213 : Blo 377762 572213 := bbase (se 5 (by rfl) ⟨26822, by rfl⟩ : syracuseStep 572213 = 53645) (by norm_num)
theorem B572237 : Blo 377762 572237 := bbase (se 3 (by rfl) ⟨107294, by rfl⟩ : syracuseStep 572237 = 214589) (by norm_num)
theorem B2308949 : Blo 377762 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B572261 : Blo 377762 572261 := bbase (se 4 (by rfl) ⟨53649, by rfl⟩ : syracuseStep 572261 = 107299) (by norm_num)
theorem B572285 : Blo 377762 572285 := bbase (se 3 (by rfl) ⟨107303, by rfl⟩ : syracuseStep 572285 = 214607) (by norm_num)
theorem B572309 : Blo 377762 572309 := bbase (se 6 (by rfl) ⟨13413, by rfl⟩ : syracuseStep 572309 = 26827) (by norm_num)
theorem B637861 : Blo 377762 637861 := bbase (se 4 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 637861 = 119599) (by norm_num)
theorem B572333 : Blo 377762 572333 := bbase (se 3 (by rfl) ⟨107312, by rfl⟩ : syracuseStep 572333 = 214625) (by norm_num)
theorem B867269 : Blo 377762 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B572357 : Blo 377762 572357 := bbase (se 4 (by rfl) ⟨53658, by rfl⟩ : syracuseStep 572357 = 107317) (by norm_num)
theorem B4864981 : Blo 377762 4864981 := bbase (se 7 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 4864981 = 114023) (by norm_num)
theorem B572381 : Blo 377762 572381 := bbase (se 3 (by rfl) ⟨107321, by rfl⟩ : syracuseStep 572381 = 214643) (by norm_num)
theorem B965621 : Blo 377762 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B572405 : Blo 377762 572405 := bbase (se 5 (by rfl) ⟨26831, by rfl⟩ : syracuseStep 572405 = 53663) (by norm_num)
theorem B637949 : Blo 377762 637949 := bbase (se 3 (by rfl) ⟨119615, by rfl⟩ : syracuseStep 637949 = 239231) (by norm_num)
theorem B572429 : Blo 377762 572429 := bbase (se 3 (by rfl) ⟨107330, by rfl⟩ : syracuseStep 572429 = 214661) (by norm_num)
theorem B572453 : Blo 377762 572453 := bbase (se 4 (by rfl) ⟨53667, by rfl⟩ : syracuseStep 572453 = 107335) (by norm_num)
theorem B572477 : Blo 377762 572477 := bbase (se 3 (by rfl) ⟨107339, by rfl⟩ : syracuseStep 572477 = 214679) (by norm_num)
theorem B1915973 : Blo 377762 1915973 := bbase (se 4 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 1915973 = 359245) (by norm_num)
theorem B572501 : Blo 377762 572501 := bbase (se 8 (by rfl) ⟨3354, by rfl⟩ : syracuseStep 572501 = 6709) (by norm_num)
theorem B572525 : Blo 377762 572525 := bbase (se 3 (by rfl) ⟨107348, by rfl⟩ : syracuseStep 572525 = 214697) (by norm_num)
theorem B638077 : Blo 377762 638077 := bbase (se 3 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 638077 = 239279) (by norm_num)
theorem B572549 : Blo 377762 572549 := bbase (se 4 (by rfl) ⟨53676, by rfl⟩ : syracuseStep 572549 = 107353) (by norm_num)
theorem B572573 : Blo 377762 572573 := bbase (se 3 (by rfl) ⟨107357, by rfl⟩ : syracuseStep 572573 = 214715) (by norm_num)
theorem B572597 : Blo 377762 572597 := bbase (se 5 (by rfl) ⟨26840, by rfl⟩ : syracuseStep 572597 = 53681) (by norm_num)
theorem B572621 : Blo 377762 572621 := bbase (se 3 (by rfl) ⟨107366, by rfl⟩ : syracuseStep 572621 = 214733) (by norm_num)
theorem B638165 : Blo 377762 638165 := bbase (se 7 (by rfl) ⟨7478, by rfl⟩ : syracuseStep 638165 = 14957) (by norm_num)
theorem B539893 : Blo 377762 539893 := bbase (se 5 (by rfl) ⟨25307, by rfl⟩ : syracuseStep 539893 = 50615) (by norm_num)
theorem B965965 : Blo 377762 965965 := bbase (se 3 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 965965 = 362237) (by norm_num)
theorem B638293 : Blo 377762 638293 := bbase (se 11 (by rfl) ⟨467, by rfl⟩ : syracuseStep 638293 = 935) (by norm_num)
theorem B638381 : Blo 377762 638381 := bbase (se 3 (by rfl) ⟨119696, by rfl⟩ : syracuseStep 638381 = 239393) (by norm_num)
theorem B966077 : Blo 377762 966077 := bbase (se 3 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 966077 = 362279) (by norm_num)
theorem B1457605 : Blo 377762 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B638509 : Blo 377762 638509 := bbase (se 3 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 638509 = 239441) (by norm_num)
theorem B605765 : Blo 377762 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B1228373 : Blo 377762 1228373 := bbase (se 8 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 1228373 = 14395) (by norm_num)
theorem B409177 : Blo 377762 409177 := bbase (se 2 (by rfl) ⟨153441, by rfl⟩ : syracuseStep 409177 = 306883) (by norm_num)
theorem B966269 : Blo 377762 966269 := bbase (se 3 (by rfl) ⟨181175, by rfl⟩ : syracuseStep 966269 = 362351) (by norm_num)
theorem B638597 : Blo 377762 638597 := bbase (se 4 (by rfl) ⟨59868, by rfl⟩ : syracuseStep 638597 = 119737) (by norm_num)
theorem B2244341 : Blo 377762 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B638725 : Blo 377762 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B638813 : Blo 377762 638813 := bbase (se 3 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 638813 = 239555) (by norm_num)
theorem B638941 : Blo 377762 638941 := bbase (se 3 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 638941 = 239603) (by norm_num)
theorem B770045 : Blo 377762 770045 := bbase (se 3 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 770045 = 288767) (by norm_num)
theorem B606221 : Blo 377762 606221 := bbase (se 3 (by rfl) ⟨113666, by rfl⟩ : syracuseStep 606221 = 227333) (by norm_num)
theorem B540685 : Blo 377762 540685 := bbase (se 3 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 540685 = 202757) (by norm_num)
theorem B639029 : Blo 377762 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B639157 : Blo 377762 639157 := bbase (se 5 (by rfl) ⟨29960, by rfl⟩ : syracuseStep 639157 = 59921) (by norm_num)
theorem B639245 : Blo 377762 639245 := bbase (se 3 (by rfl) ⟨119858, by rfl⟩ : syracuseStep 639245 = 239717) (by norm_num)
theorem B1917269 : Blo 377762 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B541021 : Blo 377762 541021 := bbase (se 3 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 541021 = 202883) (by norm_num)
theorem B3457397 : Blo 377762 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B639373 : Blo 377762 639373 := bbase (se 3 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 639373 = 239765) (by norm_num)
theorem B639461 : Blo 377762 639461 := bbase (se 4 (by rfl) ⟨59949, by rfl⟩ : syracuseStep 639461 = 119899) (by norm_num)
theorem B410113 : Blo 377762 410113 := bbase (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) (by norm_num)
theorem B541237 : Blo 377762 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B639589 : Blo 377762 639589 := bbase (se 4 (by rfl) ⟨59961, by rfl⟩ : syracuseStep 639589 = 119923) (by norm_num)
theorem B2736757 : Blo 377762 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B639677 : Blo 377762 639677 := bbase (se 3 (by rfl) ⟨119939, by rfl⟩ : syracuseStep 639677 = 239879) (by norm_num)
theorem B639805 : Blo 377762 639805 := bbase (se 3 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 639805 = 239927) (by norm_num)
theorem B639893 : Blo 377762 639893 := bbase (se 6 (by rfl) ⟨14997, by rfl⟩ : syracuseStep 639893 = 29995) (by norm_num)
theorem B541613 : Blo 377762 541613 := bbase (se 3 (by rfl) ⟨101552, by rfl⟩ : syracuseStep 541613 = 203105) (by norm_num)
theorem B1098677 : Blo 377762 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B640021 : Blo 377762 640021 := bbase (se 6 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 640021 = 30001) (by norm_num)
theorem B574517 : Blo 377762 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B640109 : Blo 377762 640109 := bbase (se 3 (by rfl) ⟨120020, by rfl⟩ : syracuseStep 640109 = 240041) (by norm_num)
theorem B640237 : Blo 377762 640237 := bbase (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) (by norm_num)
theorem B640325 : Blo 377762 640325 := bbase (se 4 (by rfl) ⟨60030, by rfl⟩ : syracuseStep 640325 = 120061) (by norm_num)
theorem B607637 : Blo 377762 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B640453 : Blo 377762 640453 := bbase (se 4 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 640453 = 120085) (by norm_num)
theorem B640541 : Blo 377762 640541 := bbase (se 3 (by rfl) ⟨120101, by rfl⟩ : syracuseStep 640541 = 240203) (by norm_num)
theorem B4343381 : Blo 377762 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B1918565 : Blo 377762 1918565 := bbase (se 4 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 1918565 = 359731) (by norm_num)
theorem B607861 : Blo 377762 607861 := bbase (se 5 (by rfl) ⟨28493, by rfl⟩ : syracuseStep 607861 = 56987) (by norm_num)
theorem B640669 : Blo 377762 640669 := bbase (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) (by norm_num)
theorem B640757 : Blo 377762 640757 := bbase (se 5 (by rfl) ⟨30035, by rfl⟩ : syracuseStep 640757 = 60071) (by norm_num)
theorem B640885 : Blo 377762 640885 := bbase (se 5 (by rfl) ⟨30041, by rfl⟩ : syracuseStep 640885 = 60083) (by norm_num)
theorem B640973 : Blo 377762 640973 := bbase (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) (by norm_num)
theorem B870389 : Blo 377762 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B4769813 : Blo 377762 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B641101 : Blo 377762 641101 := bbase (se 3 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 641101 = 240413) (by norm_num)
theorem B641189 : Blo 377762 641189 := bbase (se 4 (by rfl) ⟨60111, by rfl⟩ : syracuseStep 641189 = 120223) (by norm_num)
theorem B641317 : Blo 377762 641317 := bbase (se 4 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 641317 = 120247) (by norm_num)
theorem B543037 : Blo 377762 543037 := bbase (se 3 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 543037 = 203639) (by norm_num)
theorem B641405 : Blo 377762 641405 := bbase (se 3 (by rfl) ⟨120263, by rfl⟩ : syracuseStep 641405 = 240527) (by norm_num)
theorem B3656117 : Blo 377762 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B641533 : Blo 377762 641533 := bbase (se 3 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 641533 = 240575) (by norm_num)
theorem B641621 : Blo 377762 641621 := bbase (se 8 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 641621 = 7519) (by norm_num)
theorem B510661 : Blo 377762 510661 := bbase (se 4 (by rfl) ⟨47874, by rfl⟩ : syracuseStep 510661 = 95749) (by norm_num)
theorem B641749 : Blo 377762 641749 := bbase (se 7 (by rfl) ⟨7520, by rfl⟩ : syracuseStep 641749 = 15041) (by norm_num)
theorem B1624805 : Blo 377762 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B576245 : Blo 377762 576245 := bbase (se 5 (by rfl) ⟨27011, by rfl⟩ : syracuseStep 576245 = 54023) (by norm_num)
theorem B641837 : Blo 377762 641837 := bbase (se 3 (by rfl) ⟨120344, by rfl⟩ : syracuseStep 641837 = 240689) (by norm_num)
theorem B510781 : Blo 377762 510781 := bbase (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) (by norm_num)
theorem B1919861 : Blo 377762 1919861 := bbase (se 5 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 1919861 = 179987) (by norm_num)
theorem B641965 : Blo 377762 641965 := bbase (se 3 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 641965 = 240737) (by norm_num)
theorem B478153 : Blo 377762 478153 := bbase (se 2 (by rfl) ⟨179307, by rfl⟩ : syracuseStep 478153 = 358615) (by norm_num)
theorem B609277 : Blo 377762 609277 := bbase (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) (by norm_num)
theorem B642053 : Blo 377762 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B478325 : Blo 377762 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B642181 : Blo 377762 642181 := bbase (se 4 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 642181 = 120409) (by norm_num)
theorem B478381 : Blo 377762 478381 := bbase (se 3 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 478381 = 179393) (by norm_num)
theorem B642269 : Blo 377762 642269 := bbase (se 3 (by rfl) ⟨120425, by rfl⟩ : syracuseStep 642269 = 240851) (by norm_num)
theorem B609533 : Blo 377762 609533 := bbase (se 3 (by rfl) ⟨114287, by rfl⟩ : syracuseStep 609533 = 228575) (by norm_num)
theorem B478477 : Blo 377762 478477 := bbase (se 3 (by rfl) ⟨89714, by rfl⟩ : syracuseStep 478477 = 179429) (by norm_num)
theorem B576829 : Blo 377762 576829 := bbase (se 3 (by rfl) ⟨108155, by rfl⟩ : syracuseStep 576829 = 216311) (by norm_num)
theorem B642397 : Blo 377762 642397 := bbase (se 3 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 642397 = 240899) (by norm_num)
theorem B773477 : Blo 377762 773477 := bbase (se 4 (by rfl) ⟨72513, by rfl⟩ : syracuseStep 773477 = 145027) (by norm_num)
theorem B642485 : Blo 377762 642485 := bbase (se 5 (by rfl) ⟨30116, by rfl⟩ : syracuseStep 642485 = 60233) (by norm_num)
theorem B478649 : Blo 377762 478649 := bbase (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) (by norm_num)
theorem B609725 : Blo 377762 609725 := bbase (se 3 (by rfl) ⟨114323, by rfl⟩ : syracuseStep 609725 = 228647) (by norm_num)
theorem B478705 : Blo 377762 478705 := bbase (se 2 (by rfl) ⟨179514, by rfl⟩ : syracuseStep 478705 = 359029) (by norm_num)
theorem B1363493 : Blo 377762 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B1461797 : Blo 377762 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B642613 : Blo 377762 642613 := bbase (se 5 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 642613 = 60245) (by norm_num)
theorem B478801 : Blo 377762 478801 := bbase (se 2 (by rfl) ⟨179550, by rfl⟩ : syracuseStep 478801 = 359101) (by norm_num)
theorem B642701 : Blo 377762 642701 := bbase (se 3 (by rfl) ⟨120506, by rfl⟩ : syracuseStep 642701 = 241013) (by norm_num)
theorem B478973 : Blo 377762 478973 := bbase (se 3 (by rfl) ⟨89807, by rfl⟩ : syracuseStep 478973 = 179615) (by norm_num)
theorem B642829 : Blo 377762 642829 := bbase (se 3 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 642829 = 241061) (by norm_num)
theorem B479029 : Blo 377762 479029 := bbase (se 5 (by rfl) ⟨22454, by rfl⟩ : syracuseStep 479029 = 44909) (by norm_num)
theorem B642917 : Blo 377762 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B479125 : Blo 377762 479125 := bbase (se 6 (by rfl) ⟨11229, by rfl⟩ : syracuseStep 479125 = 22459) (by norm_num)
theorem B1298357 : Blo 377762 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B1822661 : Blo 377762 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B643045 : Blo 377762 643045 := bbase (se 4 (by rfl) ⟨60285, by rfl⟩ : syracuseStep 643045 = 120571) (by norm_num)
theorem B643133 : Blo 377762 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B479297 : Blo 377762 479297 := bbase (se 2 (by rfl) ⟨179736, by rfl⟩ : syracuseStep 479297 = 359473) (by norm_num)
theorem B479353 : Blo 377762 479353 := bbase (se 2 (by rfl) ⟨179757, by rfl⟩ : syracuseStep 479353 = 359515) (by norm_num)
theorem B1921157 : Blo 377762 1921157 := bbase (se 4 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 1921157 = 360217) (by norm_num)
theorem B2445461 : Blo 377762 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B643261 : Blo 377762 643261 := bbase (se 3 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 643261 = 241223) (by norm_num)
theorem B3068117 : Blo 377762 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B479449 : Blo 377762 479449 := bbase (se 2 (by rfl) ⟨179793, by rfl⟩ : syracuseStep 479449 = 359587) (by norm_num)
theorem B643349 : Blo 377762 643349 := bbase (se 6 (by rfl) ⟨15078, by rfl⟩ : syracuseStep 643349 = 30157) (by norm_num)
theorem B610661 : Blo 377762 610661 := bbase (se 4 (by rfl) ⟨57249, by rfl⟩ : syracuseStep 610661 = 114499) (by norm_num)
theorem B479621 : Blo 377762 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B643477 : Blo 377762 643477 := bbase (se 6 (by rfl) ⟨15081, by rfl⟩ : syracuseStep 643477 = 30163) (by norm_num)
theorem B479677 : Blo 377762 479677 := bbase (se 3 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 479677 = 179879) (by norm_num)
theorem B1626581 : Blo 377762 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B643565 : Blo 377762 643565 := bbase (se 3 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 643565 = 241337) (by norm_num)
theorem B807413 : Blo 377762 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B1364501 : Blo 377762 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B479773 : Blo 377762 479773 := bbase (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) (by norm_num)
theorem B643693 : Blo 377762 643693 := bbase (se 3 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 643693 = 241385) (by norm_num)
theorem B643781 : Blo 377762 643781 := bbase (se 4 (by rfl) ⟨60354, by rfl⟩ : syracuseStep 643781 = 120709) (by norm_num)
theorem B479945 : Blo 377762 479945 := bbase (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) (by norm_num)
theorem B807653 : Blo 377762 807653 := bbase (se 4 (by rfl) ⟨75717, by rfl⟩ : syracuseStep 807653 = 151435) (by norm_num)
theorem B611045 : Blo 377762 611045 := bbase (se 4 (by rfl) ⟨57285, by rfl⟩ : syracuseStep 611045 = 114571) (by norm_num)
theorem B480001 : Blo 377762 480001 := bbase (se 2 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 480001 = 360001) (by norm_num)
theorem B643909 : Blo 377762 643909 := bbase (se 4 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 643909 = 120733) (by norm_num)
theorem B480097 : Blo 377762 480097 := bbase (se 2 (by rfl) ⟨180036, by rfl⟩ : syracuseStep 480097 = 360073) (by norm_num)
theorem B611173 : Blo 377762 611173 := bbase (se 4 (by rfl) ⟨57297, by rfl⟩ : syracuseStep 611173 = 114595) (by norm_num)
theorem B643997 : Blo 377762 643997 := bbase (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) (by norm_num)
theorem B480269 : Blo 377762 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B644125 : Blo 377762 644125 := bbase (se 3 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 644125 = 241547) (by norm_num)
theorem B480325 : Blo 377762 480325 := bbase (se 4 (by rfl) ⟨45030, by rfl⟩ : syracuseStep 480325 = 90061) (by norm_num)
theorem B644213 : Blo 377762 644213 := bbase (se 5 (by rfl) ⟨30197, by rfl⟩ : syracuseStep 644213 = 60395) (by norm_num)
theorem B480421 : Blo 377762 480421 := bbase (se 4 (by rfl) ⟨45039, by rfl⟩ : syracuseStep 480421 = 90079) (by norm_num)
theorem B808157 : Blo 377762 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B808165 : Blo 377762 808165 := bbase (se 4 (by rfl) ⟨75765, by rfl⟩ : syracuseStep 808165 = 151531) (by norm_num)
theorem B480593 : Blo 377762 480593 := bbase (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) (by norm_num)
theorem B480649 : Blo 377762 480649 := bbase (se 2 (by rfl) ⟨180243, by rfl⟩ : syracuseStep 480649 = 360487) (by norm_num)
theorem B578957 : Blo 377762 578957 := bbase (se 3 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 578957 = 217109) (by norm_num)
theorem B1922453 : Blo 377762 1922453 := bbase (se 6 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 1922453 = 90115) (by norm_num)
theorem B1627573 : Blo 377762 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B480745 : Blo 377762 480745 := bbase (se 2 (by rfl) ⟨180279, by rfl⟩ : syracuseStep 480745 = 360559) (by norm_num)
theorem B1299989 : Blo 377762 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B480917 : Blo 377762 480917 := bbase (se 6 (by rfl) ⟨11271, by rfl⟩ : syracuseStep 480917 = 22543) (by norm_num)
theorem B480973 : Blo 377762 480973 := bbase (se 3 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 480973 = 180365) (by norm_num)
theorem B481069 : Blo 377762 481069 := bbase (se 3 (by rfl) ⟨90200, by rfl⟩ : syracuseStep 481069 = 180401) (by norm_num)
theorem B2053973 : Blo 377762 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B1824677 : Blo 377762 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B481241 : Blo 377762 481241 := bbase (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) (by norm_num)
theorem B481297 : Blo 377762 481297 := bbase (se 2 (by rfl) ⟨180486, by rfl⟩ : syracuseStep 481297 = 360973) (by norm_num)
theorem B1824869 : Blo 377762 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B481393 : Blo 377762 481393 := bbase (se 2 (by rfl) ⟨180522, by rfl⟩ : syracuseStep 481393 = 361045) (by norm_num)
theorem B481565 : Blo 377762 481565 := bbase (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) (by norm_num)
theorem B809293 : Blo 377762 809293 := bbase (se 3 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 809293 = 303485) (by norm_num)
theorem B481621 : Blo 377762 481621 := bbase (se 10 (by rfl) ⟨705, by rfl⟩ : syracuseStep 481621 = 1411) (by norm_num)
theorem B2873717 : Blo 377762 2873717 := bbase (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) (by norm_num)
theorem B383401 : Blo 377762 383401 := bbase (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) (by norm_num)
theorem B481717 : Blo 377762 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B481889 : Blo 377762 481889 := bbase (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) (by norm_num)
theorem B481945 : Blo 377762 481945 := bbase (se 2 (by rfl) ⟨180729, by rfl⟩ : syracuseStep 481945 = 361459) (by norm_num)
theorem B1923749 : Blo 377762 1923749 := bbase (se 4 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 1923749 = 360703) (by norm_num)
theorem B809669 : Blo 377762 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B482041 : Blo 377762 482041 := bbase (se 2 (by rfl) ⟨180765, by rfl⟩ : syracuseStep 482041 = 361531) (by norm_num)
theorem B908101 : Blo 377762 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B482213 : Blo 377762 482213 := bbase (se 4 (by rfl) ⟨45207, by rfl⟩ : syracuseStep 482213 = 90415) (by norm_num)
theorem B3464117 : Blo 377762 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B482269 : Blo 377762 482269 := bbase (se 3 (by rfl) ⟨90425, by rfl⟩ : syracuseStep 482269 = 180851) (by norm_num)
theorem B482365 : Blo 377762 482365 := bbase (se 3 (by rfl) ⟨90443, by rfl⟩ : syracuseStep 482365 = 180887) (by norm_num)
theorem B908437 : Blo 377762 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B482537 : Blo 377762 482537 := bbase (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) (by norm_num)
theorem B482593 : Blo 377762 482593 := bbase (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) (by norm_num)
theorem B482689 : Blo 377762 482689 := bbase (se 2 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 482689 = 362017) (by norm_num)
theorem B384545 : Blo 377762 384545 := bbase (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) (by norm_num)
theorem B482861 : Blo 377762 482861 := bbase (se 3 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 482861 = 181073) (by norm_num)
theorem B613973 : Blo 377762 613973 := bbase (se 8 (by rfl) ⟨3597, by rfl⟩ : syracuseStep 613973 = 7195) (by norm_num)
theorem B482917 : Blo 377762 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B483013 : Blo 377762 483013 := bbase (se 4 (by rfl) ⟨45282, by rfl⟩ : syracuseStep 483013 = 90565) (by norm_num)
theorem B909053 : Blo 377762 909053 := bbase (se 3 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 909053 = 340895) (by norm_num)
theorem B1925045 : Blo 377762 1925045 := bbase (se 5 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 1925045 = 180473) (by norm_num)
theorem B1826965 : Blo 377762 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B909485 : Blo 377762 909485 := bbase (se 3 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 909485 = 341057) (by norm_num)
theorem B385217 : Blo 377762 385217 := bbase (se 2 (by rfl) ⟨144456, by rfl⟩ : syracuseStep 385217 = 288913) (by norm_num)
theorem B811309 : Blo 377762 811309 := bbase (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) (by norm_num)
theorem B3236213 : Blo 377762 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B385765 : Blo 377762 385765 := bbase (se 4 (by rfl) ⟨36165, by rfl⟩ : syracuseStep 385765 = 72331) (by norm_num)
theorem B385769 : Blo 377762 385769 := bbase (se 2 (by rfl) ⟨144663, by rfl⟩ : syracuseStep 385769 = 289327) (by norm_num)
theorem B1303285 : Blo 377762 1303285 := bbase (se 5 (by rfl) ⟨61091, by rfl⟩ : syracuseStep 1303285 = 122183) (by norm_num)
theorem B615173 : Blo 377762 615173 := bbase (se 4 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 615173 = 115345) (by norm_num)
theorem B910109 : Blo 377762 910109 := bbase (se 3 (by rfl) ⟨170645, by rfl⟩ : syracuseStep 910109 = 341291) (by norm_num)
theorem B3072917 : Blo 377762 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B615325 : Blo 377762 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B1041349 : Blo 377762 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1434581 : Blo 377762 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B812197 : Blo 377762 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B1926341 : Blo 377762 1926341 := bbase (se 4 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 1926341 = 361189) (by norm_num)
theorem B550141 : Blo 377762 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B386353 : Blo 377762 386353 := bbase (se 2 (by rfl) ⟨144882, by rfl⟩ : syracuseStep 386353 = 289765) (by norm_num)
theorem B681365 : Blo 377762 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B812693 : Blo 377762 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B550885 : Blo 377762 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B1304597 : Blo 377762 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1435765 : Blo 377762 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B780653 : Blo 377762 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B616837 : Blo 377762 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1436069 : Blo 377762 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B1927637 : Blo 377762 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B813557 : Blo 377762 813557 := bbase (se 5 (by rfl) ⟨38135, by rfl⟩ : syracuseStep 813557 = 76271) (by norm_num)
theorem B682597 : Blo 377762 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B813701 : Blo 377762 813701 := bbase (se 4 (by rfl) ⟨76284, by rfl⟩ : syracuseStep 813701 = 152569) (by norm_num)
theorem B1174181 : Blo 377762 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B519229 : Blo 377762 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B650357 : Blo 377762 650357 := bbase (se 5 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 650357 = 60971) (by norm_num)
theorem B4942997 : Blo 377762 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2157749 : Blo 377762 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B3075317 : Blo 377762 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B3239189 : Blo 377762 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B814445 : Blo 377762 814445 := bbase (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) (by norm_num)
theorem B1076597 : Blo 377762 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B454093 : Blo 377762 454093 := bbase (se 3 (by rfl) ⟨85142, by rfl⟩ : syracuseStep 454093 = 170285) (by norm_num)
theorem B1371653 : Blo 377762 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B913069 : Blo 377762 913069 := bbase (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) (by norm_num)
theorem B1732309 : Blo 377762 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B978653 : Blo 377762 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B1928933 : Blo 377762 1928933 := bbase (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) (by norm_num)
theorem B487193 : Blo 377762 487193 := bbase (se 2 (by rfl) ⟨182697, by rfl⟩ : syracuseStep 487193 = 365395) (by norm_num)
theorem B913261 : Blo 377762 913261 := bbase (se 3 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 913261 = 342473) (by norm_num)
theorem B913301 : Blo 377762 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B1372069 : Blo 377762 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1372085 : Blo 377762 1372085 := bbase (se 5 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 1372085 = 128633) (by norm_num)
theorem B683981 : Blo 377762 683981 := bbase (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) (by norm_num)
theorem B1830869 : Blo 377762 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B2060245 : Blo 377762 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B684053 : Blo 377762 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B6582293 : Blo 377762 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B815197 : Blo 377762 815197 := bbase (se 3 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 815197 = 305699) (by norm_num)
theorem B782453 : Blo 377762 782453 := bbase (se 5 (by rfl) ⟨36677, by rfl⟩ : syracuseStep 782453 = 73355) (by norm_num)
theorem B684197 : Blo 377762 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B913589 : Blo 377762 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B1372373 : Blo 377762 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B815341 : Blo 377762 815341 := bbase (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) (by norm_num)
theorem B487705 : Blo 377762 487705 := bbase (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) (by norm_num)
theorem B454997 : Blo 377762 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B2158933 : Blo 377762 2158933 := bbase (se 10 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 2158933 = 6325) (by norm_num)
theorem B717245 : Blo 377762 717245 := bbase (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) (by norm_num)
theorem B4092373 : Blo 377762 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B1438181 : Blo 377762 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B1077781 : Blo 377762 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B455257 : Blo 377762 455257 := bbase (se 2 (by rfl) ⟨170721, by rfl⟩ : syracuseStep 455257 = 341443) (by norm_num)
theorem B1110629 : Blo 377762 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B1077941 : Blo 377762 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B1438469 : Blo 377762 1438469 := bbase (se 4 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 1438469 = 269713) (by norm_num)
theorem B455449 : Blo 377762 455449 := bbase (se 2 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 455449 = 341587) (by norm_num)
theorem B455473 : Blo 377762 455473 := bbase (se 2 (by rfl) ⟨170802, by rfl⟩ : syracuseStep 455473 = 341605) (by norm_num)
theorem B455477 : Blo 377762 455477 := bbase (se 5 (by rfl) ⟨21350, by rfl⟩ : syracuseStep 455477 = 42701) (by norm_num)
theorem B2749301 : Blo 377762 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B1930133 : Blo 377762 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B1078181 : Blo 377762 1078181 := bbase (se 4 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 1078181 = 202159) (by norm_num)
theorem B1930229 : Blo 377762 1930229 := bbase (se 5 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 1930229 = 180959) (by norm_num)
theorem B1078373 : Blo 377762 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B717997 : Blo 377762 717997 := bbase (se 3 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 717997 = 269249) (by norm_num)
theorem B3667189 : Blo 377762 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B1045781 : Blo 377762 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B455977 : Blo 377762 455977 := bbase (se 2 (by rfl) ⟨170991, by rfl⟩ : syracuseStep 455977 = 341983) (by norm_num)
theorem B718141 : Blo 377762 718141 := bbase (se 3 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 718141 = 269303) (by norm_num)
theorem B1733957 : Blo 377762 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B456073 : Blo 377762 456073 := bbase (se 2 (by rfl) ⟨171027, by rfl⟩ : syracuseStep 456073 = 342055) (by norm_num)
theorem B1275317 : Blo 377762 1275317 := bbase (se 5 (by rfl) ⟨59780, by rfl⟩ : syracuseStep 1275317 = 119561) (by norm_num)
theorem B718301 : Blo 377762 718301 := bbase (se 3 (by rfl) ⟨134681, by rfl⟩ : syracuseStep 718301 = 269363) (by norm_num)
theorem B718445 : Blo 377762 718445 := bbase (se 3 (by rfl) ⟨134708, by rfl⟩ : syracuseStep 718445 = 269417) (by norm_num)
theorem B1373813 : Blo 377762 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B1275749 : Blo 377762 1275749 := bbase (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) (by norm_num)
theorem B718733 : Blo 377762 718733 := bbase (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) (by norm_num)
theorem B1439653 : Blo 377762 1439653 := bbase (se 4 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 1439653 = 269935) (by norm_num)
theorem B2881493 : Blo 377762 2881493 := bbase (se 7 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 2881493 = 67535) (by norm_num)
theorem B718885 : Blo 377762 718885 := bbase (se 4 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 718885 = 134791) (by norm_num)
theorem B1079365 : Blo 377762 1079365 := bbase (se 4 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 1079365 = 202381) (by norm_num)
theorem B850013 : Blo 377762 850013 := bbase (se 3 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 850013 = 318755) (by norm_num)
theorem B850085 : Blo 377762 850085 := bbase (se 4 (by rfl) ⟨79695, by rfl⟩ : syracuseStep 850085 = 159391) (by norm_num)
theorem B1439957 : Blo 377762 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B850157 : Blo 377762 850157 := bbase (se 3 (by rfl) ⟨159404, by rfl⟩ : syracuseStep 850157 = 318809) (by norm_num)
theorem B1931525 : Blo 377762 1931525 := bbase (se 4 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 1931525 = 362161) (by norm_num)
theorem B1276181 : Blo 377762 1276181 := bbase (se 6 (by rfl) ⟨29910, by rfl⟩ : syracuseStep 1276181 = 59821) (by norm_num)
theorem B2160917 : Blo 377762 2160917 := bbase (se 6 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 2160917 = 101293) (by norm_num)
theorem B522517 : Blo 377762 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B850229 : Blo 377762 850229 := bbase (se 5 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 850229 = 79709) (by norm_num)
theorem B719189 : Blo 377762 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B457049 : Blo 377762 457049 := bbase (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) (by norm_num)
theorem B850301 : Blo 377762 850301 := bbase (se 3 (by rfl) ⟨159431, by rfl⟩ : syracuseStep 850301 = 318863) (by norm_num)
theorem B850373 : Blo 377762 850373 := bbase (se 4 (by rfl) ⟨79722, by rfl⟩ : syracuseStep 850373 = 159445) (by norm_num)
theorem B1735157 : Blo 377762 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B850445 : Blo 377762 850445 := bbase (se 3 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 850445 = 318917) (by norm_num)
theorem B2423317 : Blo 377762 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B850517 : Blo 377762 850517 := bbase (se 8 (by rfl) ⟨4983, by rfl⟩ : syracuseStep 850517 = 9967) (by norm_num)
theorem B850589 : Blo 377762 850589 := bbase (se 3 (by rfl) ⟨159485, by rfl⟩ : syracuseStep 850589 = 318971) (by norm_num)
theorem B1276613 : Blo 377762 1276613 := bbase (se 4 (by rfl) ⟨119682, by rfl⟩ : syracuseStep 1276613 = 239365) (by norm_num)
theorem B850661 : Blo 377762 850661 := bbase (se 4 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 850661 = 159499) (by norm_num)
theorem B686821 : Blo 377762 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B1833749 : Blo 377762 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B850733 : Blo 377762 850733 := bbase (se 3 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 850733 = 319025) (by norm_num)
theorem B457525 : Blo 377762 457525 := bbase (se 5 (by rfl) ⟨21446, by rfl⟩ : syracuseStep 457525 = 42893) (by norm_num)
theorem B457553 : Blo 377762 457553 := bbase (se 2 (by rfl) ⟨171582, by rfl⟩ : syracuseStep 457553 = 343165) (by norm_num)
theorem B850805 : Blo 377762 850805 := bbase (se 5 (by rfl) ⟨39881, by rfl⟩ : syracuseStep 850805 = 79763) (by norm_num)
theorem B850877 : Blo 377762 850877 := bbase (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) (by norm_num)
theorem B687037 : Blo 377762 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B850949 : Blo 377762 850949 := bbase (se 4 (by rfl) ⟨79776, by rfl⟩ : syracuseStep 850949 = 159553) (by norm_num)
theorem B457741 : Blo 377762 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B424993 : Blo 377762 424993 := bbase (se 2 (by rfl) ⟨159372, by rfl⟩ : syracuseStep 424993 = 318745) (by norm_num)
theorem B425029 : Blo 377762 425029 := bbase (se 4 (by rfl) ⟨39846, by rfl⟩ : syracuseStep 425029 = 79693) (by norm_num)
theorem B719941 : Blo 377762 719941 := bbase (se 4 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 719941 = 134989) (by norm_num)
theorem B851021 : Blo 377762 851021 := bbase (se 3 (by rfl) ⟨159566, by rfl⟩ : syracuseStep 851021 = 319133) (by norm_num)
theorem B425065 : Blo 377762 425065 := bbase (se 2 (by rfl) ⟨159399, by rfl⟩ : syracuseStep 425065 = 318799) (by norm_num)
theorem B1277045 : Blo 377762 1277045 := bbase (se 5 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 1277045 = 119723) (by norm_num)
theorem B457861 : Blo 377762 457861 := bbase (se 4 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 457861 = 85849) (by norm_num)
theorem B425101 : Blo 377762 425101 := bbase (se 3 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 425101 = 159413) (by norm_num)
theorem B851093 : Blo 377762 851093 := bbase (se 6 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 851093 = 39895) (by norm_num)
theorem B1080469 : Blo 377762 1080469 := bbase (se 6 (by rfl) ⟨25323, by rfl⟩ : syracuseStep 1080469 = 50647) (by norm_num)
theorem B1211557 : Blo 377762 1211557 := bbase (se 4 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 1211557 = 227167) (by norm_num)
theorem B425137 : Blo 377762 425137 := bbase (se 2 (by rfl) ⟨159426, by rfl⟩ : syracuseStep 425137 = 318853) (by norm_num)
theorem B425173 : Blo 377762 425173 := bbase (se 7 (by rfl) ⟨4982, by rfl⟩ : syracuseStep 425173 = 9965) (by norm_num)
theorem B720085 : Blo 377762 720085 := bbase (se 7 (by rfl) ⟨8438, by rfl⟩ : syracuseStep 720085 = 16877) (by norm_num)
theorem B851165 : Blo 377762 851165 := bbase (se 3 (by rfl) ⟨159593, by rfl⟩ : syracuseStep 851165 = 319187) (by norm_num)
theorem B425209 : Blo 377762 425209 := bbase (se 2 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 425209 = 318907) (by norm_num)
theorem B425245 : Blo 377762 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B851237 : Blo 377762 851237 := bbase (se 4 (by rfl) ⟨79803, by rfl⟩ : syracuseStep 851237 = 159607) (by norm_num)
theorem B425281 : Blo 377762 425281 := bbase (se 2 (by rfl) ⟨159480, by rfl⟩ : syracuseStep 425281 = 318961) (by norm_num)
theorem B425317 : Blo 377762 425317 := bbase (se 4 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 425317 = 79747) (by norm_num)
theorem B851309 : Blo 377762 851309 := bbase (se 3 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 851309 = 319241) (by norm_num)
theorem B720245 : Blo 377762 720245 := bbase (se 5 (by rfl) ⟨33761, by rfl⟩ : syracuseStep 720245 = 67523) (by norm_num)
theorem B425353 : Blo 377762 425353 := bbase (se 2 (by rfl) ⟨159507, by rfl⟩ : syracuseStep 425353 = 319015) (by norm_num)
theorem B425389 : Blo 377762 425389 := bbase (se 3 (by rfl) ⟨79760, by rfl⟩ : syracuseStep 425389 = 159521) (by norm_num)
theorem B851381 : Blo 377762 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B425425 : Blo 377762 425425 := bbase (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) (by norm_num)
theorem B425461 : Blo 377762 425461 := bbase (se 5 (by rfl) ⟨19943, by rfl⟩ : syracuseStep 425461 = 39887) (by norm_num)
theorem B851453 : Blo 377762 851453 := bbase (se 3 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 851453 = 319295) (by norm_num)
theorem B720389 : Blo 377762 720389 := bbase (se 4 (by rfl) ⟨67536, by rfl⟩ : syracuseStep 720389 = 135073) (by norm_num)
theorem B425497 : Blo 377762 425497 := bbase (se 2 (by rfl) ⟨159561, by rfl⟩ : syracuseStep 425497 = 319123) (by norm_num)
theorem B1277477 : Blo 377762 1277477 := bbase (se 4 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 1277477 = 239527) (by norm_num)
theorem B425533 : Blo 377762 425533 := bbase (se 3 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 425533 = 159575) (by norm_num)
theorem B851525 : Blo 377762 851525 := bbase (se 4 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 851525 = 159661) (by norm_num)
theorem B425569 : Blo 377762 425569 := bbase (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) (by norm_num)
theorem B425605 : Blo 377762 425605 := bbase (se 4 (by rfl) ⟨39900, by rfl⟩ : syracuseStep 425605 = 79801) (by norm_num)
theorem B851597 : Blo 377762 851597 := bbase (se 3 (by rfl) ⟨159674, by rfl⟩ : syracuseStep 851597 = 319349) (by norm_num)
theorem B425641 : Blo 377762 425641 := bbase (se 2 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 425641 = 319231) (by norm_num)
theorem B917173 : Blo 377762 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B425677 : Blo 377762 425677 := bbase (se 3 (by rfl) ⟨79814, by rfl⟩ : syracuseStep 425677 = 159629) (by norm_num)
theorem B851669 : Blo 377762 851669 := bbase (se 7 (by rfl) ⟨9980, by rfl⟩ : syracuseStep 851669 = 19961) (by norm_num)
theorem B425713 : Blo 377762 425713 := bbase (se 2 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 425713 = 319285) (by norm_num)
theorem B425749 : Blo 377762 425749 := bbase (se 6 (by rfl) ⟨9978, by rfl⟩ : syracuseStep 425749 = 19957) (by norm_num)
theorem B851741 : Blo 377762 851741 := bbase (se 3 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 851741 = 319403) (by norm_num)
theorem B720677 : Blo 377762 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B425785 : Blo 377762 425785 := bbase (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) (by norm_num)
theorem B425821 : Blo 377762 425821 := bbase (se 3 (by rfl) ⟨79841, by rfl⟩ : syracuseStep 425821 = 159683) (by norm_num)
theorem B851813 : Blo 377762 851813 := bbase (se 4 (by rfl) ⟨79857, by rfl⟩ : syracuseStep 851813 = 159715) (by norm_num)
theorem B425857 : Blo 377762 425857 := bbase (se 2 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 425857 = 319393) (by norm_num)
theorem B425893 : Blo 377762 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B851885 : Blo 377762 851885 := bbase (se 3 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 851885 = 319457) (by norm_num)
theorem B720829 : Blo 377762 720829 := bbase (se 3 (by rfl) ⟨135155, by rfl⟩ : syracuseStep 720829 = 270311) (by norm_num)
theorem B425929 : Blo 377762 425929 := bbase (se 2 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 425929 = 319447) (by norm_num)
theorem B1277909 : Blo 377762 1277909 := bbase (se 7 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 1277909 = 29951) (by norm_num)
theorem B425965 : Blo 377762 425965 := bbase (se 3 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 425965 = 159737) (by norm_num)
theorem B851957 : Blo 377762 851957 := bbase (se 5 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 851957 = 79871) (by norm_num)
theorem B720913 : Blo 377762 720913 := bstep (se 2 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 720913 = 540685) B540685
theorem B426019 : Blo 377762 426019 := bstep (se 1 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 426019 = 639029) B639029
theorem B1278125 : Blo 377762 1278125 := bstep (se 3 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 1278125 = 479297) B479297
theorem B426163 : Blo 377762 426163 := bstep (se 1 (by rfl) ⟨319622, by rfl⟩ : syracuseStep 426163 = 639245) B639245
theorem B1278179 : Blo 377762 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B852209 : Blo 377762 852209 := bstep (se 2 (by rfl) ⟨319578, by rfl⟩ : syracuseStep 852209 = 639157) B639157
theorem B852227 : Blo 377762 852227 := bstep (se 1 (by rfl) ⟨639170, by rfl⟩ : syracuseStep 852227 = 1278341) B1278341
theorem B1442083 : Blo 377762 1442083 := bstep (se 1 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 1442083 = 2163125) B2163125
theorem B426307 : Blo 377762 426307 := bstep (se 1 (by rfl) ⟨319730, by rfl⟩ : syracuseStep 426307 = 639461) B639461
theorem B1081745 : Blo 377762 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B721315 : Blo 377762 721315 := bstep (se 1 (by rfl) ⟨540986, by rfl⟩ : syracuseStep 721315 = 1081973) B1081973
theorem B721361 : Blo 377762 721361 := bstep (se 2 (by rfl) ⟨270510, by rfl⟩ : syracuseStep 721361 = 541021) B541021
theorem B426451 : Blo 377762 426451 := bstep (se 1 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 426451 = 639677) B639677
theorem B2425315 : Blo 377762 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B1278449 : Blo 377762 1278449 := bstep (se 2 (by rfl) ⟨479418, by rfl⟩ : syracuseStep 1278449 = 958837) B958837
theorem B852497 : Blo 377762 852497 := bstep (se 2 (by rfl) ⟨319686, by rfl⟩ : syracuseStep 852497 = 639373) B639373
theorem B852515 : Blo 377762 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B426595 : Blo 377762 426595 := bstep (se 1 (by rfl) ⟨319946, by rfl⟩ : syracuseStep 426595 = 639893) B639893
theorem B721649 : Blo 377762 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B426739 : Blo 377762 426739 := bstep (se 1 (by rfl) ⟨320054, by rfl⟩ : syracuseStep 426739 = 640109) B640109
theorem B852785 : Blo 377762 852785 := bstep (se 2 (by rfl) ⟨319794, by rfl⟩ : syracuseStep 852785 = 639589) B639589
theorem B852803 : Blo 377762 852803 := bstep (se 1 (by rfl) ⟨639602, by rfl⟩ : syracuseStep 852803 = 1279205) B1279205
theorem B426883 : Blo 377762 426883 := bstep (se 1 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 426883 = 640325) B640325
theorem B1213325 : Blo 377762 1213325 := bstep (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) B454997
theorem B1737713 : Blo 377762 1737713 := bstep (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) B1303285
theorem B1278989 : Blo 377762 1278989 := bstep (se 3 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 1278989 = 479621) B479621
theorem B427027 : Blo 377762 427027 := bstep (se 1 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 427027 = 640541) B640541
theorem B1279043 : Blo 377762 1279043 := bstep (se 1 (by rfl) ⟨959282, by rfl⟩ : syracuseStep 1279043 = 1918565) B1918565
theorem B853073 : Blo 377762 853073 := bstep (se 2 (by rfl) ⟨319902, by rfl⟩ : syracuseStep 853073 = 639805) B639805
theorem B853091 : Blo 377762 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B656531 : Blo 377762 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B427171 : Blo 377762 427171 := bstep (se 1 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 427171 = 640757) B640757
theorem B820433 : Blo 377762 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B525569 : Blo 377762 525569 := bstep (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) B394177
theorem B427315 : Blo 377762 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B1279313 : Blo 377762 1279313 := bstep (se 2 (by rfl) ⟨479742, by rfl⟩ : syracuseStep 1279313 = 959485) B959485
theorem B853361 : Blo 377762 853361 := bstep (se 2 (by rfl) ⟨320010, by rfl⟩ : syracuseStep 853361 = 640021) B640021
theorem B853379 : Blo 377762 853379 := bstep (se 1 (by rfl) ⟨640034, by rfl⟩ : syracuseStep 853379 = 1280069) B1280069
theorem B427459 : Blo 377762 427459 := bstep (se 1 (by rfl) ⟨320594, by rfl⟩ : syracuseStep 427459 = 641189) B641189
theorem B722371 : Blo 377762 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B427603 : Blo 377762 427603 := bstep (se 1 (by rfl) ⟨320702, by rfl⟩ : syracuseStep 427603 = 641405) B641405
theorem B853649 : Blo 377762 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B853667 : Blo 377762 853667 := bstep (se 1 (by rfl) ⟨640250, by rfl⟩ : syracuseStep 853667 = 1280501) B1280501
theorem B427747 : Blo 377762 427747 := bstep (se 1 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 427747 = 641621) B641621
theorem B1083203 : Blo 377762 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B1279853 : Blo 377762 1279853 := bstep (se 3 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 1279853 = 479945) B479945
theorem B427891 : Blo 377762 427891 := bstep (se 1 (by rfl) ⟨320918, by rfl⟩ : syracuseStep 427891 = 641837) B641837
theorem B722819 : Blo 377762 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B1279907 : Blo 377762 1279907 := bstep (se 1 (by rfl) ⟨959930, by rfl⟩ : syracuseStep 1279907 = 1919861) B1919861
theorem B853937 : Blo 377762 853937 := bstep (se 2 (by rfl) ⟨320226, by rfl⟩ : syracuseStep 853937 = 640453) B640453
theorem B853955 : Blo 377762 853955 := bstep (se 1 (by rfl) ⟨640466, by rfl⟩ : syracuseStep 853955 = 1280933) B1280933
theorem B395251 : Blo 377762 395251 := bstep (se 1 (by rfl) ⟨296438, by rfl⟩ : syracuseStep 395251 = 592877) B592877
theorem B428035 : Blo 377762 428035 := bstep (se 1 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 428035 = 642053) B642053
theorem B1640461 : Blo 377762 1640461 := bstep (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) B615173
theorem B1214605 : Blo 377762 1214605 := bstep (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) B455477
theorem B428179 : Blo 377762 428179 := bstep (se 1 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 428179 = 642269) B642269
theorem B723107 : Blo 377762 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B1280177 : Blo 377762 1280177 := bstep (se 2 (by rfl) ⟨480066, by rfl⟩ : syracuseStep 1280177 = 960133) B960133
theorem B854225 : Blo 377762 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B854243 : Blo 377762 854243 := bstep (se 1 (by rfl) ⟨640682, by rfl⟩ : syracuseStep 854243 = 1281365) B1281365
theorem B428323 : Blo 377762 428323 := bstep (se 1 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 428323 = 642485) B642485
theorem B1116547 : Blo 377762 1116547 := bstep (se 1 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 1116547 = 1674821) B1674821
theorem B5147021 : Blo 377762 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B428467 : Blo 377762 428467 := bstep (se 1 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 428467 = 642701) B642701
theorem B1444301 : Blo 377762 1444301 := bstep (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) B541613
theorem B854513 : Blo 377762 854513 := bstep (se 2 (by rfl) ⟨320442, by rfl⟩ : syracuseStep 854513 = 640885) B640885
theorem B854531 : Blo 377762 854531 := bstep (se 1 (by rfl) ⟨640898, by rfl⟩ : syracuseStep 854531 = 1281797) B1281797
theorem B428611 : Blo 377762 428611 := bstep (se 1 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 428611 = 642917) B642917
theorem B1084013 : Blo 377762 1084013 := bstep (se 3 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 1084013 = 406505) B406505
theorem B1215107 : Blo 377762 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B1280717 : Blo 377762 1280717 := bstep (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) B480269
theorem B428755 : Blo 377762 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B1280771 : Blo 377762 1280771 := bstep (se 1 (by rfl) ⟨960578, by rfl⟩ : syracuseStep 1280771 = 1921157) B1921157
theorem B854801 : Blo 377762 854801 := bstep (se 2 (by rfl) ⟨320550, by rfl⟩ : syracuseStep 854801 = 641101) B641101
theorem B854819 : Blo 377762 854819 := bstep (se 1 (by rfl) ⟨641114, by rfl⟩ : syracuseStep 854819 = 1282229) B1282229
theorem B1084205 : Blo 377762 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B428899 : Blo 377762 428899 := bstep (se 1 (by rfl) ⟨321674, by rfl⟩ : syracuseStep 428899 = 643349) B643349
theorem B429043 : Blo 377762 429043 := bstep (se 1 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 429043 = 643565) B643565
theorem B1281041 : Blo 377762 1281041 := bstep (se 2 (by rfl) ⟨480390, by rfl⟩ : syracuseStep 1281041 = 960781) B960781
theorem B855089 : Blo 377762 855089 := bstep (se 2 (by rfl) ⟨320658, by rfl⟩ : syracuseStep 855089 = 641317) B641317
theorem B855107 : Blo 377762 855107 := bstep (se 1 (by rfl) ⟨641330, by rfl⟩ : syracuseStep 855107 = 1282661) B1282661
theorem B724049 : Blo 377762 724049 := bstep (se 2 (by rfl) ⟨271518, by rfl⟩ : syracuseStep 724049 = 543037) B543037
theorem B429187 : Blo 377762 429187 := bstep (se 1 (by rfl) ⟨321890, by rfl⟩ : syracuseStep 429187 = 643781) B643781
theorem B822449 : Blo 377762 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B429331 : Blo 377762 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B855377 : Blo 377762 855377 := bstep (se 2 (by rfl) ⟨320766, by rfl⟩ : syracuseStep 855377 = 641533) B641533
theorem B855395 : Blo 377762 855395 := bstep (se 1 (by rfl) ⟨641546, by rfl⟩ : syracuseStep 855395 = 1283093) B1283093
theorem B429475 : Blo 377762 429475 := bstep (se 1 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 429475 = 644213) B644213
theorem B1281581 : Blo 377762 1281581 := bstep (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) B480593
theorem B1281635 : Blo 377762 1281635 := bstep (se 1 (by rfl) ⟨961226, by rfl⟩ : syracuseStep 1281635 = 1922453) B1922453
theorem B855665 : Blo 377762 855665 := bstep (se 2 (by rfl) ⟨320874, by rfl⟩ : syracuseStep 855665 = 641749) B641749
theorem B855683 : Blo 377762 855683 := bstep (se 1 (by rfl) ⟨641762, by rfl⟩ : syracuseStep 855683 = 1283525) B1283525
theorem B1085197 : Blo 377762 1085197 := bstep (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) B406949
theorem B1281905 : Blo 377762 1281905 := bstep (se 2 (by rfl) ⟨480714, by rfl⟩ : syracuseStep 1281905 = 961429) B961429
theorem B855953 : Blo 377762 855953 := bstep (se 2 (by rfl) ⟨320982, by rfl⟩ : syracuseStep 855953 = 641965) B641965
theorem B1642403 : Blo 377762 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B855971 : Blo 377762 855971 := bstep (se 1 (by rfl) ⟨641978, by rfl⟩ : syracuseStep 855971 = 1283957) B1283957
theorem B1544113 : Blo 377762 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1216451 : Blo 377762 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B856241 : Blo 377762 856241 := bstep (se 2 (by rfl) ⟨321090, by rfl⟩ : syracuseStep 856241 = 642181) B642181
theorem B856259 : Blo 377762 856259 := bstep (se 1 (by rfl) ⟨642194, by rfl⟩ : syracuseStep 856259 = 1284389) B1284389
theorem B2199757 : Blo 377762 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B2429189 : Blo 377762 2429189 := bstep (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) B455473
theorem B1282445 : Blo 377762 1282445 := bstep (se 3 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 1282445 = 480917) B480917
theorem B2167181 : Blo 377762 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B1282499 : Blo 377762 1282499 := bstep (se 1 (by rfl) ⟨961874, by rfl⟩ : syracuseStep 1282499 = 1923749) B1923749
theorem B856529 : Blo 377762 856529 := bstep (se 2 (by rfl) ⟨321198, by rfl⟩ : syracuseStep 856529 = 642397) B642397
theorem B856547 : Blo 377762 856547 := bstep (se 1 (by rfl) ⟨642410, by rfl⟩ : syracuseStep 856547 = 1284821) B1284821
theorem B660035 : Blo 377762 660035 := bstep (se 1 (by rfl) ⟨495026, by rfl⟩ : syracuseStep 660035 = 990053) B990053
theorem B1282769 : Blo 377762 1282769 := bstep (se 2 (by rfl) ⟨481038, by rfl⟩ : syracuseStep 1282769 = 962077) B962077
theorem B856817 : Blo 377762 856817 := bstep (se 2 (by rfl) ⟨321306, by rfl⟩ : syracuseStep 856817 = 642613) B642613
theorem B856835 : Blo 377762 856835 := bstep (se 1 (by rfl) ⟨642626, by rfl⟩ : syracuseStep 856835 = 1285253) B1285253
theorem B1217425 : Blo 377762 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B857105 : Blo 377762 857105 := bstep (se 2 (by rfl) ⟨321414, by rfl⟩ : syracuseStep 857105 = 642829) B642829
theorem B857123 : Blo 377762 857123 := bstep (se 1 (by rfl) ⟨642842, by rfl⟩ : syracuseStep 857123 = 1285685) B1285685
theorem B1217681 : Blo 377762 1217681 := bstep (se 2 (by rfl) ⟨456630, by rfl⟩ : syracuseStep 1217681 = 913261) B913261
theorem B2299043 : Blo 377762 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B1283309 : Blo 377762 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B660755 : Blo 377762 660755 := bstep (se 1 (by rfl) ⟨495566, by rfl⟩ : syracuseStep 660755 = 991133) B991133
theorem B1283363 : Blo 377762 1283363 := bstep (se 1 (by rfl) ⟨962522, by rfl⟩ : syracuseStep 1283363 = 1925045) B1925045
theorem B857393 : Blo 377762 857393 := bstep (se 2 (by rfl) ⟨321522, by rfl⟩ : syracuseStep 857393 = 643045) B643045
theorem B1447217 : Blo 377762 1447217 := bstep (se 2 (by rfl) ⟨542706, by rfl⟩ : syracuseStep 1447217 = 1085413) B1085413
theorem B857411 : Blo 377762 857411 := bstep (se 1 (by rfl) ⟨643058, by rfl⟩ : syracuseStep 857411 = 1286117) B1286117
theorem B3478925 : Blo 377762 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B12719501 : Blo 377762 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1086929 : Blo 377762 1086929 := bstep (se 2 (by rfl) ⟨407598, by rfl⟩ : syracuseStep 1086929 = 815197) B815197
theorem B1283633 : Blo 377762 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B857681 : Blo 377762 857681 := bstep (se 2 (by rfl) ⟨321630, by rfl⟩ : syracuseStep 857681 = 643261) B643261
theorem B857699 : Blo 377762 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B1087121 : Blo 377762 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B857969 : Blo 377762 857969 := bstep (se 2 (by rfl) ⟨321738, by rfl⟩ : syracuseStep 857969 = 643477) B643477
theorem B857987 : Blo 377762 857987 := bstep (se 1 (by rfl) ⟨643490, by rfl⟩ : syracuseStep 857987 = 1286981) B1286981
theorem B956387 : Blo 377762 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B1284173 : Blo 377762 1284173 := bstep (se 3 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 1284173 = 481565) B481565
theorem B1284227 : Blo 377762 1284227 := bstep (se 1 (by rfl) ⟨963170, by rfl⟩ : syracuseStep 1284227 = 1926341) B1926341
theorem B858257 : Blo 377762 858257 := bstep (se 2 (by rfl) ⟨321846, by rfl⟩ : syracuseStep 858257 = 643693) B643693
theorem B858275 : Blo 377762 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B4331717 : Blo 377762 4331717 := bstep (se 4 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 4331717 = 812197) B812197
theorem B1218797 : Blo 377762 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B2595185 : Blo 377762 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B1284497 : Blo 377762 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B858545 : Blo 377762 858545 := bstep (se 2 (by rfl) ⟨321954, by rfl⟩ : syracuseStep 858545 = 643909) B643909
theorem B858563 : Blo 377762 858563 := bstep (se 1 (by rfl) ⟨643922, by rfl⟩ : syracuseStep 858563 = 1287845) B1287845
theorem B2169413 : Blo 377762 2169413 := bstep (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) B406765
theorem B858833 : Blo 377762 858833 := bstep (se 2 (by rfl) ⟨322062, by rfl⟩ : syracuseStep 858833 = 644125) B644125
theorem B1448675 : Blo 377762 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B858851 : Blo 377762 858851 := bstep (se 1 (by rfl) ⟨644138, by rfl⟩ : syracuseStep 858851 = 1288277) B1288277
theorem B957329 : Blo 377762 957329 := bstep (se 2 (by rfl) ⟨358998, by rfl⟩ : syracuseStep 957329 = 717997) B717997
theorem B1285037 : Blo 377762 1285037 := bstep (se 3 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 1285037 = 481889) B481889
theorem B957379 : Blo 377762 957379 := bstep (se 1 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 957379 = 1436069) B1436069
theorem B1285091 : Blo 377762 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B4889585 : Blo 377762 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B957521 : Blo 377762 957521 := bstep (se 2 (by rfl) ⟨359070, by rfl⟩ : syracuseStep 957521 = 718141) B718141
theorem B1285361 : Blo 377762 1285361 := bstep (se 2 (by rfl) ⟨482010, by rfl⟩ : syracuseStep 1285361 = 964021) B964021
theorem B2170097 : Blo 377762 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B2432389 : Blo 377762 2432389 := bstep (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) B456073
theorem B433571 : Blo 377762 433571 := bstep (se 1 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 433571 = 650357) B650357
theorem B1220141 : Blo 377762 1220141 := bstep (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) B457553
theorem B1285901 : Blo 377762 1285901 := bstep (se 3 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 1285901 = 482213) B482213
theorem B1285955 : Blo 377762 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B1220579 : Blo 377762 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B958513 : Blo 377762 958513 := bstep (se 2 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 958513 = 718885) B718885
theorem B1286225 : Blo 377762 1286225 := bstep (se 2 (by rfl) ⟨482334, by rfl⟩ : syracuseStep 1286225 = 964669) B964669
theorem B958787 : Blo 377762 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B696689 : Blo 377762 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B958979 : Blo 377762 958979 := bstep (se 1 (by rfl) ⟨719234, by rfl⟩ : syracuseStep 958979 = 1438469) B1438469
theorem B1286765 : Blo 377762 1286765 := bstep (se 3 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 1286765 = 482537) B482537
theorem B1286819 : Blo 377762 1286819 := bstep (se 1 (by rfl) ⟨965114, by rfl⟩ : syracuseStep 1286819 = 1930229) B1930229
theorem B2171555 : Blo 377762 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B1844045 : Blo 377762 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B697187 : Blo 377762 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B1155971 : Blo 377762 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B730019 : Blo 377762 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B1287089 : Blo 377762 1287089 := bstep (se 2 (by rfl) ⟨482658, by rfl⟩ : syracuseStep 1287089 = 965317) B965317
theorem B4891589 : Blo 377762 4891589 := bstep (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) B917173
theorem B566657 : Blo 377762 566657 := bstep (se 2 (by rfl) ⟨212496, by rfl⟩ : syracuseStep 566657 = 424993) B424993
theorem B566675 : Blo 377762 566675 := bstep (se 1 (by rfl) ⟨425006, by rfl⟩ : syracuseStep 566675 = 850013) B850013
theorem B1025453 : Blo 377762 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B566705 : Blo 377762 566705 := bstep (se 2 (by rfl) ⟨212514, by rfl⟩ : syracuseStep 566705 = 425029) B425029
theorem B959921 : Blo 377762 959921 := bstep (se 2 (by rfl) ⟨359970, by rfl⟩ : syracuseStep 959921 = 719941) B719941
theorem B566723 : Blo 377762 566723 := bstep (se 1 (by rfl) ⟨425042, by rfl⟩ : syracuseStep 566723 = 850085) B850085
theorem B1287629 : Blo 377762 1287629 := bstep (se 3 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 1287629 = 482861) B482861
theorem B566753 : Blo 377762 566753 := bstep (se 2 (by rfl) ⟨212532, by rfl⟩ : syracuseStep 566753 = 425065) B425065
theorem B959971 : Blo 377762 959971 := bstep (se 1 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 959971 = 1439957) B1439957
theorem B566771 : Blo 377762 566771 := bstep (se 1 (by rfl) ⟨425078, by rfl⟩ : syracuseStep 566771 = 850157) B850157
theorem B1287683 : Blo 377762 1287683 := bstep (se 1 (by rfl) ⟨965762, by rfl⟩ : syracuseStep 1287683 = 1931525) B1931525
theorem B1615373 : Blo 377762 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B566801 : Blo 377762 566801 := bstep (se 2 (by rfl) ⟨212550, by rfl⟩ : syracuseStep 566801 = 425101) B425101
theorem B566819 : Blo 377762 566819 := bstep (se 1 (by rfl) ⟨425114, by rfl⟩ : syracuseStep 566819 = 850229) B850229
theorem B1615409 : Blo 377762 1615409 := bstep (se 2 (by rfl) ⟨605778, by rfl⟩ : syracuseStep 1615409 = 1211557) B1211557
theorem B566849 : Blo 377762 566849 := bstep (se 2 (by rfl) ⟨212568, by rfl⟩ : syracuseStep 566849 = 425137) B425137
theorem B566867 : Blo 377762 566867 := bstep (se 1 (by rfl) ⟨425150, by rfl⟩ : syracuseStep 566867 = 850301) B850301
theorem B566897 : Blo 377762 566897 := bstep (se 2 (by rfl) ⟨212586, by rfl⟩ : syracuseStep 566897 = 425173) B425173
theorem B960113 : Blo 377762 960113 := bstep (se 2 (by rfl) ⟨360042, by rfl⟩ : syracuseStep 960113 = 720085) B720085
theorem B468595 : Blo 377762 468595 := bstep (se 1 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 468595 = 702893) B702893
theorem B566915 : Blo 377762 566915 := bstep (se 1 (by rfl) ⟨425186, by rfl⟩ : syracuseStep 566915 = 850373) B850373
theorem B566945 : Blo 377762 566945 := bstep (se 2 (by rfl) ⟨212604, by rfl⟩ : syracuseStep 566945 = 425209) B425209
theorem B1156771 : Blo 377762 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B566963 : Blo 377762 566963 := bstep (se 1 (by rfl) ⟨425222, by rfl⟩ : syracuseStep 566963 = 850445) B850445
theorem B566993 : Blo 377762 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B567011 : Blo 377762 567011 := bstep (se 1 (by rfl) ⟨425258, by rfl⟩ : syracuseStep 567011 = 850517) B850517
theorem B567041 : Blo 377762 567041 := bstep (se 2 (by rfl) ⟨212640, by rfl⟩ : syracuseStep 567041 = 425281) B425281
theorem B1287953 : Blo 377762 1287953 := bstep (se 2 (by rfl) ⟨482982, by rfl⟩ : syracuseStep 1287953 = 965965) B965965
theorem B567059 : Blo 377762 567059 := bstep (se 1 (by rfl) ⟨425294, by rfl⟩ : syracuseStep 567059 = 850589) B850589
theorem B567089 : Blo 377762 567089 := bstep (se 2 (by rfl) ⟨212658, by rfl⟩ : syracuseStep 567089 = 425317) B425317
theorem B567107 : Blo 377762 567107 := bstep (se 1 (by rfl) ⟨425330, by rfl⟩ : syracuseStep 567107 = 850661) B850661
theorem B567137 : Blo 377762 567137 := bstep (se 2 (by rfl) ⟨212676, by rfl⟩ : syracuseStep 567137 = 425353) B425353
theorem B1222499 : Blo 377762 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B567155 : Blo 377762 567155 := bstep (se 1 (by rfl) ⟨425366, by rfl⟩ : syracuseStep 567155 = 850733) B850733
theorem B567185 : Blo 377762 567185 := bstep (se 2 (by rfl) ⟨212694, by rfl⟩ : syracuseStep 567185 = 425389) B425389
theorem B567203 : Blo 377762 567203 := bstep (se 1 (by rfl) ⟨425402, by rfl⟩ : syracuseStep 567203 = 850805) B850805
theorem B1943473 : Blo 377762 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B567233 : Blo 377762 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B567251 : Blo 377762 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B567281 : Blo 377762 567281 := bstep (se 2 (by rfl) ⟨212730, by rfl⟩ : syracuseStep 567281 = 425461) B425461
theorem B567299 : Blo 377762 567299 := bstep (se 1 (by rfl) ⟨425474, by rfl⟩ : syracuseStep 567299 = 850949) B850949
theorem B567329 : Blo 377762 567329 := bstep (se 2 (by rfl) ⟨212748, by rfl⟩ : syracuseStep 567329 = 425497) B425497
theorem B567347 : Blo 377762 567347 := bstep (se 1 (by rfl) ⟨425510, by rfl⟩ : syracuseStep 567347 = 851021) B851021
theorem B567377 : Blo 377762 567377 := bstep (se 2 (by rfl) ⟨212766, by rfl⟩ : syracuseStep 567377 = 425533) B425533
theorem B567395 : Blo 377762 567395 := bstep (se 1 (by rfl) ⟨425546, by rfl⟩ : syracuseStep 567395 = 851093) B851093
theorem B567425 : Blo 377762 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B567443 : Blo 377762 567443 := bstep (se 1 (by rfl) ⟨425582, by rfl⟩ : syracuseStep 567443 = 851165) B851165
theorem B567473 : Blo 377762 567473 := bstep (se 2 (by rfl) ⟨212802, by rfl⟩ : syracuseStep 567473 = 425605) B425605
theorem B567491 : Blo 377762 567491 := bstep (se 1 (by rfl) ⟨425618, by rfl⟩ : syracuseStep 567491 = 851237) B851237
theorem B7317701 : Blo 377762 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B567521 : Blo 377762 567521 := bstep (se 2 (by rfl) ⟨212820, by rfl⟩ : syracuseStep 567521 = 425641) B425641
theorem B567539 : Blo 377762 567539 := bstep (se 1 (by rfl) ⟨425654, by rfl⟩ : syracuseStep 567539 = 851309) B851309
theorem B567569 : Blo 377762 567569 := bstep (se 2 (by rfl) ⟨212838, by rfl⟩ : syracuseStep 567569 = 425677) B425677
theorem B567587 : Blo 377762 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B567617 : Blo 377762 567617 := bstep (se 2 (by rfl) ⟨212856, by rfl⟩ : syracuseStep 567617 = 425713) B425713
theorem B567635 : Blo 377762 567635 := bstep (se 1 (by rfl) ⟨425726, by rfl⟩ : syracuseStep 567635 = 851453) B851453
theorem B567665 : Blo 377762 567665 := bstep (se 2 (by rfl) ⟨212874, by rfl⟩ : syracuseStep 567665 = 425749) B425749
theorem B567683 : Blo 377762 567683 := bstep (se 1 (by rfl) ⟨425762, by rfl⟩ : syracuseStep 567683 = 851525) B851525
theorem B567713 : Blo 377762 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B567731 : Blo 377762 567731 := bstep (se 1 (by rfl) ⟨425798, by rfl⟩ : syracuseStep 567731 = 851597) B851597
theorem B567761 : Blo 377762 567761 := bstep (se 2 (by rfl) ⟨212910, by rfl⟩ : syracuseStep 567761 = 425821) B425821
theorem B567779 : Blo 377762 567779 := bstep (se 1 (by rfl) ⟨425834, by rfl⟩ : syracuseStep 567779 = 851669) B851669
theorem B567809 : Blo 377762 567809 := bstep (se 2 (by rfl) ⟨212928, by rfl⟩ : syracuseStep 567809 = 425857) B425857
theorem B2042381 : Blo 377762 2042381 := bstep (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) B765893
theorem B567827 : Blo 377762 567827 := bstep (se 1 (by rfl) ⟨425870, by rfl⟩ : syracuseStep 567827 = 851741) B851741
theorem B567857 : Blo 377762 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B567875 : Blo 377762 567875 := bstep (se 1 (by rfl) ⟨425906, by rfl⟩ : syracuseStep 567875 = 851813) B851813
theorem B961105 : Blo 377762 961105 := bstep (se 2 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 961105 = 720829) B720829
theorem B567905 : Blo 377762 567905 := bstep (se 2 (by rfl) ⟨212964, by rfl⟩ : syracuseStep 567905 = 425929) B425929
theorem B567923 : Blo 377762 567923 := bstep (se 1 (by rfl) ⟨425942, by rfl⟩ : syracuseStep 567923 = 851885) B851885
theorem B567953 : Blo 377762 567953 := bstep (se 2 (by rfl) ⟨212982, by rfl⟩ : syracuseStep 567953 = 425965) B425965
theorem B567971 : Blo 377762 567971 := bstep (se 1 (by rfl) ⟨425978, by rfl⟩ : syracuseStep 567971 = 851957) B851957
theorem B404147 : Blo 377762 404147 := bstep (se 1 (by rfl) ⟨303110, by rfl⟩ : syracuseStep 404147 = 606221) B606221
theorem B568001 : Blo 377762 568001 := bstep (se 2 (by rfl) ⟨213000, by rfl⟩ : syracuseStep 568001 = 426001) B426001
theorem B1092305 : Blo 377762 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B568019 : Blo 377762 568019 := bstep (se 1 (by rfl) ⟨426014, by rfl⟩ : syracuseStep 568019 = 852029) B852029
theorem B568049 : Blo 377762 568049 := bstep (se 2 (by rfl) ⟨213018, by rfl⟩ : syracuseStep 568049 = 426037) B426037
theorem B568067 : Blo 377762 568067 := bstep (se 1 (by rfl) ⟨426050, by rfl⟩ : syracuseStep 568067 = 852101) B852101
theorem B928529 : Blo 377762 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B568097 : Blo 377762 568097 := bstep (se 2 (by rfl) ⟨213036, by rfl⟩ : syracuseStep 568097 = 426073) B426073
theorem B568115 : Blo 377762 568115 := bstep (se 1 (by rfl) ⟨426086, by rfl⟩ : syracuseStep 568115 = 852173) B852173
theorem B568145 : Blo 377762 568145 := bstep (se 2 (by rfl) ⟨213054, by rfl⟩ : syracuseStep 568145 = 426109) B426109
theorem B568163 : Blo 377762 568163 := bstep (se 1 (by rfl) ⟨426122, by rfl⟩ : syracuseStep 568163 = 852245) B852245
theorem B961379 : Blo 377762 961379 := bstep (se 1 (by rfl) ⟨721034, by rfl⟩ : syracuseStep 961379 = 1442069) B1442069
theorem B2435953 : Blo 377762 2435953 := bstep (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) B1826965
theorem B568193 : Blo 377762 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B568211 : Blo 377762 568211 := bstep (se 1 (by rfl) ⟨426158, by rfl⟩ : syracuseStep 568211 = 852317) B852317
theorem B2304931 : Blo 377762 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B568241 : Blo 377762 568241 := bstep (se 2 (by rfl) ⟨213090, by rfl⟩ : syracuseStep 568241 = 426181) B426181
theorem B568259 : Blo 377762 568259 := bstep (se 1 (by rfl) ⟨426194, by rfl⟩ : syracuseStep 568259 = 852389) B852389
theorem B568289 : Blo 377762 568289 := bstep (se 2 (by rfl) ⟨213108, by rfl⟩ : syracuseStep 568289 = 426217) B426217
theorem B568307 : Blo 377762 568307 := bstep (se 1 (by rfl) ⟨426230, by rfl⟩ : syracuseStep 568307 = 852461) B852461
theorem B568337 : Blo 377762 568337 := bstep (se 2 (by rfl) ⟨213126, by rfl⟩ : syracuseStep 568337 = 426253) B426253
theorem B568355 : Blo 377762 568355 := bstep (se 1 (by rfl) ⟨426266, by rfl⟩ : syracuseStep 568355 = 852533) B852533
theorem B961571 : Blo 377762 961571 := bstep (se 1 (by rfl) ⟨721178, by rfl⟩ : syracuseStep 961571 = 1442357) B1442357
theorem B568385 : Blo 377762 568385 := bstep (se 2 (by rfl) ⟨213144, by rfl⟩ : syracuseStep 568385 = 426289) B426289
theorem B568403 : Blo 377762 568403 := bstep (se 1 (by rfl) ⟨426302, by rfl⟩ : syracuseStep 568403 = 852605) B852605
theorem B568433 : Blo 377762 568433 := bstep (se 2 (by rfl) ⟨213162, by rfl⟩ : syracuseStep 568433 = 426325) B426325
theorem B568451 : Blo 377762 568451 := bstep (se 1 (by rfl) ⟨426338, by rfl⟩ : syracuseStep 568451 = 852677) B852677
theorem B568481 : Blo 377762 568481 := bstep (se 2 (by rfl) ⟨213180, by rfl⟩ : syracuseStep 568481 = 426361) B426361
theorem B568499 : Blo 377762 568499 := bstep (se 1 (by rfl) ⟨426374, by rfl⟩ : syracuseStep 568499 = 852749) B852749
theorem B568529 : Blo 377762 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B568547 : Blo 377762 568547 := bstep (se 1 (by rfl) ⟨426410, by rfl⟩ : syracuseStep 568547 = 852821) B852821
theorem B568577 : Blo 377762 568577 := bstep (se 2 (by rfl) ⟨213216, by rfl⟩ : syracuseStep 568577 = 426433) B426433
theorem B568595 : Blo 377762 568595 := bstep (se 1 (by rfl) ⟨426446, by rfl⟩ : syracuseStep 568595 = 852893) B852893
theorem B732451 : Blo 377762 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B568625 : Blo 377762 568625 := bstep (se 2 (by rfl) ⟨213234, by rfl⟩ : syracuseStep 568625 = 426469) B426469
theorem B568643 : Blo 377762 568643 := bstep (se 1 (by rfl) ⟨426482, by rfl⟩ : syracuseStep 568643 = 852965) B852965
theorem B568673 : Blo 377762 568673 := bstep (se 2 (by rfl) ⟨213252, by rfl⟩ : syracuseStep 568673 = 426505) B426505
theorem B568691 : Blo 377762 568691 := bstep (se 1 (by rfl) ⟨426518, by rfl⟩ : syracuseStep 568691 = 853037) B853037
theorem B568721 : Blo 377762 568721 := bstep (se 2 (by rfl) ⟨213270, by rfl⟩ : syracuseStep 568721 = 426541) B426541
theorem B568739 : Blo 377762 568739 := bstep (se 1 (by rfl) ⟨426554, by rfl⟩ : syracuseStep 568739 = 853109) B853109
theorem B568769 : Blo 377762 568769 := bstep (se 2 (by rfl) ⟨213288, by rfl⟩ : syracuseStep 568769 = 426577) B426577
theorem B568787 : Blo 377762 568787 := bstep (se 1 (by rfl) ⟨426590, by rfl⟩ : syracuseStep 568787 = 853181) B853181
theorem B568817 : Blo 377762 568817 := bstep (se 2 (by rfl) ⟨213306, by rfl⟩ : syracuseStep 568817 = 426613) B426613
theorem B3649009 : Blo 377762 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B568835 : Blo 377762 568835 := bstep (se 1 (by rfl) ⟨426626, by rfl⟩ : syracuseStep 568835 = 853253) B853253
theorem B568865 : Blo 377762 568865 := bstep (se 2 (by rfl) ⟨213324, by rfl⟩ : syracuseStep 568865 = 426649) B426649
theorem B568883 : Blo 377762 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B15773237 : Blo 377762 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B568913 : Blo 377762 568913 := bstep (se 2 (by rfl) ⟨213342, by rfl⟩ : syracuseStep 568913 = 426685) B426685
theorem B568931 : Blo 377762 568931 := bstep (se 1 (by rfl) ⟨426698, by rfl⟩ : syracuseStep 568931 = 853397) B853397
theorem B405091 : Blo 377762 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B568961 : Blo 377762 568961 := bstep (se 2 (by rfl) ⟨213360, by rfl⟩ : syracuseStep 568961 = 426721) B426721
theorem B568979 : Blo 377762 568979 := bstep (se 1 (by rfl) ⟨426734, by rfl⟩ : syracuseStep 568979 = 853469) B853469
theorem B569009 : Blo 377762 569009 := bstep (se 2 (by rfl) ⟨213378, by rfl⟩ : syracuseStep 569009 = 426757) B426757
theorem B569027 : Blo 377762 569027 := bstep (se 1 (by rfl) ⟨426770, by rfl⟩ : syracuseStep 569027 = 853541) B853541
theorem B569057 : Blo 377762 569057 := bstep (se 2 (by rfl) ⟨213396, by rfl⟩ : syracuseStep 569057 = 426793) B426793
theorem B2895587 : Blo 377762 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B569075 : Blo 377762 569075 := bstep (se 1 (by rfl) ⟨426806, by rfl⟩ : syracuseStep 569075 = 853613) B853613
theorem B569105 : Blo 377762 569105 := bstep (se 2 (by rfl) ⟨213414, by rfl⟩ : syracuseStep 569105 = 426829) B426829
theorem B569123 : Blo 377762 569123 := bstep (se 1 (by rfl) ⟨426842, by rfl⟩ : syracuseStep 569123 = 853685) B853685
theorem B569153 : Blo 377762 569153 := bstep (se 2 (by rfl) ⟨213432, by rfl⟩ : syracuseStep 569153 = 426865) B426865
theorem B569171 : Blo 377762 569171 := bstep (se 1 (by rfl) ⟨426878, by rfl⟩ : syracuseStep 569171 = 853757) B853757
theorem B569201 : Blo 377762 569201 := bstep (se 2 (by rfl) ⟨213450, by rfl⟩ : syracuseStep 569201 = 426901) B426901
theorem B569219 : Blo 377762 569219 := bstep (se 1 (by rfl) ⟨426914, by rfl⟩ : syracuseStep 569219 = 853829) B853829
theorem B4337549 : Blo 377762 4337549 := bstep (se 3 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 4337549 = 1626581) B1626581
theorem B569249 : Blo 377762 569249 := bstep (se 2 (by rfl) ⟨213468, by rfl⟩ : syracuseStep 569249 = 426937) B426937
theorem B1388465 : Blo 377762 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B569267 : Blo 377762 569267 := bstep (se 1 (by rfl) ⟨426950, by rfl⟩ : syracuseStep 569267 = 853901) B853901
theorem B569297 : Blo 377762 569297 := bstep (se 2 (by rfl) ⟨213486, by rfl⟩ : syracuseStep 569297 = 426973) B426973
theorem B962513 : Blo 377762 962513 := bstep (se 2 (by rfl) ⟨360942, by rfl⟩ : syracuseStep 962513 = 721885) B721885
theorem B569315 : Blo 377762 569315 := bstep (se 1 (by rfl) ⟨426986, by rfl⟩ : syracuseStep 569315 = 853973) B853973
theorem B569345 : Blo 377762 569345 := bstep (se 2 (by rfl) ⟨213504, by rfl⟩ : syracuseStep 569345 = 427009) B427009
theorem B962563 : Blo 377762 962563 := bstep (se 1 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 962563 = 1443845) B1443845
theorem B569363 : Blo 377762 569363 := bstep (se 1 (by rfl) ⟨427022, by rfl⟩ : syracuseStep 569363 = 854045) B854045
theorem B569393 : Blo 377762 569393 := bstep (se 2 (by rfl) ⟨213522, by rfl⟩ : syracuseStep 569393 = 427045) B427045
theorem B569411 : Blo 377762 569411 := bstep (se 1 (by rfl) ⟨427058, by rfl⟩ : syracuseStep 569411 = 854117) B854117
theorem B569441 : Blo 377762 569441 := bstep (se 2 (by rfl) ⟨213540, by rfl⟩ : syracuseStep 569441 = 427081) B427081
theorem B569459 : Blo 377762 569459 := bstep (se 1 (by rfl) ⟨427094, by rfl⟩ : syracuseStep 569459 = 854189) B854189
theorem B569489 : Blo 377762 569489 := bstep (se 2 (by rfl) ⟨213558, by rfl⟩ : syracuseStep 569489 = 427117) B427117
theorem B962705 : Blo 377762 962705 := bstep (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) B722029
theorem B569507 : Blo 377762 569507 := bstep (se 1 (by rfl) ⟨427130, by rfl⟩ : syracuseStep 569507 = 854261) B854261
theorem B569537 : Blo 377762 569537 := bstep (se 2 (by rfl) ⟨213576, by rfl⟩ : syracuseStep 569537 = 427153) B427153
theorem B569555 : Blo 377762 569555 := bstep (se 1 (by rfl) ⟨427166, by rfl⟩ : syracuseStep 569555 = 854333) B854333
theorem B569585 : Blo 377762 569585 := bstep (se 2 (by rfl) ⟨213594, by rfl⟩ : syracuseStep 569585 = 427189) B427189
theorem B569603 : Blo 377762 569603 := bstep (se 1 (by rfl) ⟨427202, by rfl⟩ : syracuseStep 569603 = 854405) B854405
theorem B2961677 : Blo 377762 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B569633 : Blo 377762 569633 := bstep (se 2 (by rfl) ⟨213612, by rfl⟩ : syracuseStep 569633 = 427225) B427225
theorem B569651 : Blo 377762 569651 := bstep (se 1 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 569651 = 854477) B854477
theorem B569681 : Blo 377762 569681 := bstep (se 2 (by rfl) ⟨213630, by rfl⟩ : syracuseStep 569681 = 427261) B427261
theorem B569699 : Blo 377762 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B569729 : Blo 377762 569729 := bstep (se 2 (by rfl) ⟨213648, by rfl⟩ : syracuseStep 569729 = 427297) B427297
theorem B569747 : Blo 377762 569747 := bstep (se 1 (by rfl) ⟨427310, by rfl⟩ : syracuseStep 569747 = 854621) B854621
theorem B569777 : Blo 377762 569777 := bstep (se 2 (by rfl) ⟨213666, by rfl⟩ : syracuseStep 569777 = 427333) B427333
theorem B569795 : Blo 377762 569795 := bstep (se 1 (by rfl) ⟨427346, by rfl⟩ : syracuseStep 569795 = 854693) B854693
theorem B569825 : Blo 377762 569825 := bstep (se 2 (by rfl) ⟨213684, by rfl⟩ : syracuseStep 569825 = 427369) B427369
theorem B569843 : Blo 377762 569843 := bstep (se 1 (by rfl) ⟨427382, by rfl⟩ : syracuseStep 569843 = 854765) B854765
theorem B569873 : Blo 377762 569873 := bstep (se 2 (by rfl) ⟨213702, by rfl⟩ : syracuseStep 569873 = 427405) B427405
theorem B569891 : Blo 377762 569891 := bstep (se 1 (by rfl) ⟨427418, by rfl⟩ : syracuseStep 569891 = 854837) B854837
theorem B569921 : Blo 377762 569921 := bstep (se 2 (by rfl) ⟨213720, by rfl⟩ : syracuseStep 569921 = 427441) B427441
theorem B569939 : Blo 377762 569939 := bstep (se 1 (by rfl) ⟨427454, by rfl⟩ : syracuseStep 569939 = 854909) B854909
theorem B1028717 : Blo 377762 1028717 := bstep (se 3 (by rfl) ⟨192884, by rfl⟩ : syracuseStep 1028717 = 385769) B385769
theorem B569969 : Blo 377762 569969 := bstep (se 2 (by rfl) ⟨213738, by rfl⟩ : syracuseStep 569969 = 427477) B427477
theorem B569987 : Blo 377762 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B832145 : Blo 377762 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B570017 : Blo 377762 570017 := bstep (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) B427513
theorem B570035 : Blo 377762 570035 := bstep (se 1 (by rfl) ⟨427526, by rfl⟩ : syracuseStep 570035 = 855053) B855053
theorem B4108981 : Blo 377762 4108981 := bstep (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) B385217
theorem B1028803 : Blo 377762 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B570065 : Blo 377762 570065 := bstep (se 2 (by rfl) ⟨213774, by rfl⟩ : syracuseStep 570065 = 427549) B427549
theorem B570083 : Blo 377762 570083 := bstep (se 1 (by rfl) ⟨427562, by rfl⟩ : syracuseStep 570083 = 855125) B855125
theorem B570113 : Blo 377762 570113 := bstep (se 2 (by rfl) ⟨213792, by rfl⟩ : syracuseStep 570113 = 427585) B427585
theorem B570131 : Blo 377762 570131 := bstep (se 1 (by rfl) ⟨427598, by rfl⟩ : syracuseStep 570131 = 855197) B855197
theorem B570161 : Blo 377762 570161 := bstep (se 2 (by rfl) ⟨213810, by rfl⟩ : syracuseStep 570161 = 427621) B427621
theorem B570179 : Blo 377762 570179 := bstep (se 1 (by rfl) ⟨427634, by rfl⟩ : syracuseStep 570179 = 855269) B855269
theorem B406355 : Blo 377762 406355 := bstep (se 1 (by rfl) ⟨304766, by rfl⟩ : syracuseStep 406355 = 609533) B609533
theorem B570209 : Blo 377762 570209 := bstep (se 2 (by rfl) ⟨213828, by rfl⟩ : syracuseStep 570209 = 427657) B427657
theorem B570227 : Blo 377762 570227 := bstep (se 1 (by rfl) ⟨427670, by rfl⟩ : syracuseStep 570227 = 855341) B855341
theorem B3093389 : Blo 377762 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B570257 : Blo 377762 570257 := bstep (se 2 (by rfl) ⟨213846, by rfl⟩ : syracuseStep 570257 = 427693) B427693
theorem B570275 : Blo 377762 570275 := bstep (se 1 (by rfl) ⟨427706, by rfl⟩ : syracuseStep 570275 = 855413) B855413
theorem B570305 : Blo 377762 570305 := bstep (se 2 (by rfl) ⟨213864, by rfl⟩ : syracuseStep 570305 = 427729) B427729
theorem B570323 : Blo 377762 570323 := bstep (se 1 (by rfl) ⟨427742, by rfl⟩ : syracuseStep 570323 = 855485) B855485
theorem B570353 : Blo 377762 570353 := bstep (se 2 (by rfl) ⟨213882, by rfl⟩ : syracuseStep 570353 = 427765) B427765
theorem B570371 : Blo 377762 570371 := bstep (se 1 (by rfl) ⟨427778, by rfl⟩ : syracuseStep 570371 = 855557) B855557
theorem B570401 : Blo 377762 570401 := bstep (se 2 (by rfl) ⟨213900, by rfl⟩ : syracuseStep 570401 = 427801) B427801
theorem B832547 : Blo 377762 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B570419 : Blo 377762 570419 := bstep (se 1 (by rfl) ⟨427814, by rfl⟩ : syracuseStep 570419 = 855629) B855629
theorem B570449 : Blo 377762 570449 := bstep (se 2 (by rfl) ⟨213918, by rfl⟩ : syracuseStep 570449 = 427837) B427837
theorem B570467 : Blo 377762 570467 := bstep (se 1 (by rfl) ⟨427850, by rfl⟩ : syracuseStep 570467 = 855701) B855701
theorem B963697 : Blo 377762 963697 := bstep (se 2 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 963697 = 722773) B722773
theorem B570497 : Blo 377762 570497 := bstep (se 2 (by rfl) ⟨213936, by rfl⟩ : syracuseStep 570497 = 427873) B427873
theorem B570515 : Blo 377762 570515 := bstep (se 1 (by rfl) ⟨427886, by rfl⟩ : syracuseStep 570515 = 855773) B855773
theorem B570545 : Blo 377762 570545 := bstep (se 2 (by rfl) ⟨213954, by rfl⟩ : syracuseStep 570545 = 427909) B427909
theorem B570563 : Blo 377762 570563 := bstep (se 1 (by rfl) ⟨427922, by rfl⟩ : syracuseStep 570563 = 855845) B855845
theorem B570593 : Blo 377762 570593 := bstep (se 2 (by rfl) ⟨213972, by rfl⟩ : syracuseStep 570593 = 427945) B427945
theorem B570611 : Blo 377762 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B570641 : Blo 377762 570641 := bstep (se 2 (by rfl) ⟨213990, by rfl⟩ : syracuseStep 570641 = 427981) B427981
theorem B865571 : Blo 377762 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B570659 : Blo 377762 570659 := bstep (se 1 (by rfl) ⟨427994, by rfl⟩ : syracuseStep 570659 = 855989) B855989
theorem B734513 : Blo 377762 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B570689 : Blo 377762 570689 := bstep (se 2 (by rfl) ⟨214008, by rfl⟩ : syracuseStep 570689 = 428017) B428017
theorem B570707 : Blo 377762 570707 := bstep (se 1 (by rfl) ⟨428030, by rfl⟩ : syracuseStep 570707 = 856061) B856061
theorem B570737 : Blo 377762 570737 := bstep (se 2 (by rfl) ⟨214026, by rfl⟩ : syracuseStep 570737 = 428053) B428053
theorem B570755 : Blo 377762 570755 := bstep (se 1 (by rfl) ⟨428066, by rfl⟩ : syracuseStep 570755 = 856133) B856133
theorem B963971 : Blo 377762 963971 := bstep (se 1 (by rfl) ⟨722978, by rfl⟩ : syracuseStep 963971 = 1445957) B1445957
theorem B570785 : Blo 377762 570785 := bstep (se 2 (by rfl) ⟨214044, by rfl⟩ : syracuseStep 570785 = 428089) B428089
theorem B570803 : Blo 377762 570803 := bstep (se 1 (by rfl) ⟨428102, by rfl⟩ : syracuseStep 570803 = 856205) B856205
theorem B570833 : Blo 377762 570833 := bstep (se 2 (by rfl) ⟨214062, by rfl⟩ : syracuseStep 570833 = 428125) B428125
theorem B2045411 : Blo 377762 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B570851 : Blo 377762 570851 := bstep (se 1 (by rfl) ⟨428138, by rfl⟩ : syracuseStep 570851 = 856277) B856277
theorem B1914353 : Blo 377762 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B570881 : Blo 377762 570881 := bstep (se 2 (by rfl) ⟨214080, by rfl⟩ : syracuseStep 570881 = 428161) B428161
theorem B570899 : Blo 377762 570899 := bstep (se 1 (by rfl) ⟨428174, by rfl⟩ : syracuseStep 570899 = 856349) B856349
theorem B570929 : Blo 377762 570929 := bstep (se 2 (by rfl) ⟨214098, by rfl⟩ : syracuseStep 570929 = 428197) B428197
theorem B570947 : Blo 377762 570947 := bstep (se 1 (by rfl) ⟨428210, by rfl⟩ : syracuseStep 570947 = 856421) B856421
theorem B964163 : Blo 377762 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B407107 : Blo 377762 407107 := bstep (se 1 (by rfl) ⟨305330, by rfl⟩ : syracuseStep 407107 = 610661) B610661
theorem B570977 : Blo 377762 570977 := bstep (se 2 (by rfl) ⟨214116, by rfl⟩ : syracuseStep 570977 = 428233) B428233
theorem B570995 : Blo 377762 570995 := bstep (se 1 (by rfl) ⟨428246, by rfl⟩ : syracuseStep 570995 = 856493) B856493
theorem B571025 : Blo 377762 571025 := bstep (se 2 (by rfl) ⟨214134, by rfl⟩ : syracuseStep 571025 = 428269) B428269
theorem B571043 : Blo 377762 571043 := bstep (se 1 (by rfl) ⟨428282, by rfl⟩ : syracuseStep 571043 = 856565) B856565
theorem B571073 : Blo 377762 571073 := bstep (se 2 (by rfl) ⟨214152, by rfl⟩ : syracuseStep 571073 = 428305) B428305
theorem B538321 : Blo 377762 538321 := bstep (se 2 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 538321 = 403741) B403741
theorem B571091 : Blo 377762 571091 := bstep (se 1 (by rfl) ⟨428318, by rfl⟩ : syracuseStep 571091 = 856637) B856637
theorem B3258083 : Blo 377762 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B4601585 : Blo 377762 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B571121 : Blo 377762 571121 := bstep (se 2 (by rfl) ⟨214170, by rfl⟩ : syracuseStep 571121 = 428341) B428341
theorem B571139 : Blo 377762 571139 := bstep (se 1 (by rfl) ⟨428354, by rfl⟩ : syracuseStep 571139 = 856709) B856709
theorem B571169 : Blo 377762 571169 := bstep (se 2 (by rfl) ⟨214188, by rfl⟩ : syracuseStep 571169 = 428377) B428377
theorem B1619747 : Blo 377762 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B571187 : Blo 377762 571187 := bstep (se 1 (by rfl) ⟨428390, by rfl⟩ : syracuseStep 571187 = 856781) B856781
theorem B538435 : Blo 377762 538435 := bstep (se 1 (by rfl) ⟨403826, by rfl⟩ : syracuseStep 538435 = 807653) B807653
theorem B407363 : Blo 377762 407363 := bstep (se 1 (by rfl) ⟨305522, by rfl⟩ : syracuseStep 407363 = 611045) B611045
theorem B571217 : Blo 377762 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B571235 : Blo 377762 571235 := bstep (se 1 (by rfl) ⟨428426, by rfl⟩ : syracuseStep 571235 = 856853) B856853
theorem B4110193 : Blo 377762 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B571265 : Blo 377762 571265 := bstep (se 2 (by rfl) ⟨214224, by rfl⟩ : syracuseStep 571265 = 428449) B428449
theorem B571283 : Blo 377762 571283 := bstep (se 1 (by rfl) ⟨428462, by rfl⟩ : syracuseStep 571283 = 856925) B856925
theorem B571313 : Blo 377762 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B571331 : Blo 377762 571331 := bstep (se 1 (by rfl) ⟨428498, by rfl⟩ : syracuseStep 571331 = 856997) B856997
theorem B571361 : Blo 377762 571361 := bstep (se 2 (by rfl) ⟨214260, by rfl⟩ : syracuseStep 571361 = 428521) B428521
theorem B571379 : Blo 377762 571379 := bstep (se 1 (by rfl) ⟨428534, by rfl⟩ : syracuseStep 571379 = 857069) B857069
theorem B571409 : Blo 377762 571409 := bstep (se 2 (by rfl) ⟨214278, by rfl⟩ : syracuseStep 571409 = 428557) B428557
theorem B571427 : Blo 377762 571427 := bstep (se 1 (by rfl) ⟨428570, by rfl⟩ : syracuseStep 571427 = 857141) B857141
theorem B571457 : Blo 377762 571457 := bstep (se 2 (by rfl) ⟨214296, by rfl⟩ : syracuseStep 571457 = 428593) B428593
theorem B571475 : Blo 377762 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B571505 : Blo 377762 571505 := bstep (se 2 (by rfl) ⟨214314, by rfl⟩ : syracuseStep 571505 = 428629) B428629
theorem B571523 : Blo 377762 571523 := bstep (se 1 (by rfl) ⟨428642, by rfl⟩ : syracuseStep 571523 = 857285) B857285
theorem B571553 : Blo 377762 571553 := bstep (se 2 (by rfl) ⟨214332, by rfl⟩ : syracuseStep 571553 = 428665) B428665
theorem B571571 : Blo 377762 571571 := bstep (se 1 (by rfl) ⟨428678, by rfl⟩ : syracuseStep 571571 = 857357) B857357
theorem B571601 : Blo 377762 571601 := bstep (se 2 (by rfl) ⟨214350, by rfl⟩ : syracuseStep 571601 = 428701) B428701
theorem B571619 : Blo 377762 571619 := bstep (se 1 (by rfl) ⟨428714, by rfl⟩ : syracuseStep 571619 = 857429) B857429
theorem B571649 : Blo 377762 571649 := bstep (se 2 (by rfl) ⟨214368, by rfl⟩ : syracuseStep 571649 = 428737) B428737
theorem B571667 : Blo 377762 571667 := bstep (se 1 (by rfl) ⟨428750, by rfl⟩ : syracuseStep 571667 = 857501) B857501
theorem B571697 : Blo 377762 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B571715 : Blo 377762 571715 := bstep (se 1 (by rfl) ⟨428786, by rfl⟩ : syracuseStep 571715 = 857573) B857573
theorem B571745 : Blo 377762 571745 := bstep (se 2 (by rfl) ⟨214404, by rfl⟩ : syracuseStep 571745 = 428809) B428809
theorem B571763 : Blo 377762 571763 := bstep (se 1 (by rfl) ⟨428822, by rfl⟩ : syracuseStep 571763 = 857645) B857645
theorem B571793 : Blo 377762 571793 := bstep (se 2 (by rfl) ⟨214422, by rfl⟩ : syracuseStep 571793 = 428845) B428845
theorem B571811 : Blo 377762 571811 := bstep (se 1 (by rfl) ⟨428858, by rfl⟩ : syracuseStep 571811 = 857717) B857717
theorem B571841 : Blo 377762 571841 := bstep (se 2 (by rfl) ⟨214440, by rfl⟩ : syracuseStep 571841 = 428881) B428881
theorem B571859 : Blo 377762 571859 := bstep (se 1 (by rfl) ⟨428894, by rfl⟩ : syracuseStep 571859 = 857789) B857789
theorem B571889 : Blo 377762 571889 := bstep (se 2 (by rfl) ⟨214458, by rfl⟩ : syracuseStep 571889 = 428917) B428917
theorem B965105 : Blo 377762 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B571907 : Blo 377762 571907 := bstep (se 1 (by rfl) ⟨428930, by rfl⟩ : syracuseStep 571907 = 857861) B857861
theorem B571937 : Blo 377762 571937 := bstep (se 2 (by rfl) ⟨214476, by rfl⟩ : syracuseStep 571937 = 428953) B428953
theorem B965155 : Blo 377762 965155 := bstep (se 1 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 965155 = 1447733) B1447733
theorem B571955 : Blo 377762 571955 := bstep (se 1 (by rfl) ⟨428966, by rfl⟩ : syracuseStep 571955 = 857933) B857933
theorem B571985 : Blo 377762 571985 := bstep (se 2 (by rfl) ⟨214494, by rfl⟩ : syracuseStep 571985 = 428989) B428989
theorem B637537 : Blo 377762 637537 := bstep (se 2 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 637537 = 478153) B478153
theorem B572003 : Blo 377762 572003 := bstep (se 1 (by rfl) ⟨429002, by rfl⟩ : syracuseStep 572003 = 858005) B858005
theorem B572033 : Blo 377762 572033 := bstep (se 2 (by rfl) ⟨214512, by rfl⟩ : syracuseStep 572033 = 429025) B429025
theorem B637571 : Blo 377762 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B572051 : Blo 377762 572051 := bstep (se 1 (by rfl) ⟨429038, by rfl⟩ : syracuseStep 572051 = 858077) B858077
theorem B965297 : Blo 377762 965297 := bstep (se 2 (by rfl) ⟨361986, by rfl⟩ : syracuseStep 965297 = 723973) B723973
theorem B572081 : Blo 377762 572081 := bstep (se 2 (by rfl) ⟨214530, by rfl⟩ : syracuseStep 572081 = 429061) B429061
theorem B572099 : Blo 377762 572099 := bstep (se 1 (by rfl) ⟨429074, by rfl⟩ : syracuseStep 572099 = 858149) B858149
theorem B572129 : Blo 377762 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B4340465 : Blo 377762 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B572147 : Blo 377762 572147 := bstep (se 1 (by rfl) ⟨429110, by rfl⟩ : syracuseStep 572147 = 858221) B858221
theorem B637699 : Blo 377762 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B572177 : Blo 377762 572177 := bstep (se 2 (by rfl) ⟨214566, by rfl⟩ : syracuseStep 572177 = 429133) B429133
theorem B572195 : Blo 377762 572195 := bstep (se 1 (by rfl) ⟨429146, by rfl⟩ : syracuseStep 572195 = 858293) B858293
theorem B6175541 : Blo 377762 6175541 := bstep (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) B578957
theorem B572225 : Blo 377762 572225 := bstep (se 2 (by rfl) ⟨214584, by rfl⟩ : syracuseStep 572225 = 429169) B429169
theorem B572243 : Blo 377762 572243 := bstep (se 1 (by rfl) ⟨429182, by rfl⟩ : syracuseStep 572243 = 858365) B858365
theorem B572273 : Blo 377762 572273 := bstep (se 2 (by rfl) ⟨214602, by rfl⟩ : syracuseStep 572273 = 429205) B429205
theorem B572291 : Blo 377762 572291 := bstep (se 1 (by rfl) ⟨429218, by rfl⟩ : syracuseStep 572291 = 858437) B858437
theorem B637841 : Blo 377762 637841 := bstep (se 2 (by rfl) ⟨239190, by rfl⟩ : syracuseStep 637841 = 478381) B478381
theorem B572321 : Blo 377762 572321 := bstep (se 2 (by rfl) ⟨214620, by rfl⟩ : syracuseStep 572321 = 429241) B429241
theorem B1915811 : Blo 377762 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B572339 : Blo 377762 572339 := bstep (se 1 (by rfl) ⟨429254, by rfl⟩ : syracuseStep 572339 = 858509) B858509
theorem B572369 : Blo 377762 572369 := bstep (se 2 (by rfl) ⟨214638, by rfl⟩ : syracuseStep 572369 = 429277) B429277
theorem B572387 : Blo 377762 572387 := bstep (se 1 (by rfl) ⟨429290, by rfl⟩ : syracuseStep 572387 = 858581) B858581
theorem B572417 : Blo 377762 572417 := bstep (se 2 (by rfl) ⟨214656, by rfl⟩ : syracuseStep 572417 = 429313) B429313
theorem B637969 : Blo 377762 637969 := bstep (se 2 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 637969 = 478477) B478477
theorem B572435 : Blo 377762 572435 := bstep (se 1 (by rfl) ⟨429326, by rfl⟩ : syracuseStep 572435 = 858653) B858653
theorem B572465 : Blo 377762 572465 := bstep (se 2 (by rfl) ⟨214674, by rfl⟩ : syracuseStep 572465 = 429349) B429349
theorem B638003 : Blo 377762 638003 := bstep (se 1 (by rfl) ⟨478502, by rfl⟩ : syracuseStep 638003 = 957005) B957005
theorem B572483 : Blo 377762 572483 := bstep (se 1 (by rfl) ⟨429362, by rfl⟩ : syracuseStep 572483 = 858725) B858725
theorem B769105 : Blo 377762 769105 := bstep (se 2 (by rfl) ⟨288414, by rfl⟩ : syracuseStep 769105 = 576829) B576829
theorem B572513 : Blo 377762 572513 := bstep (se 2 (by rfl) ⟨214692, by rfl⟩ : syracuseStep 572513 = 429385) B429385
theorem B572531 : Blo 377762 572531 := bstep (se 1 (by rfl) ⟨429398, by rfl⟩ : syracuseStep 572531 = 858797) B858797
theorem B539779 : Blo 377762 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B572561 : Blo 377762 572561 := bstep (se 2 (by rfl) ⟨214710, by rfl⟩ : syracuseStep 572561 = 429421) B429421
theorem B572579 : Blo 377762 572579 := bstep (se 1 (by rfl) ⟨429434, by rfl⟩ : syracuseStep 572579 = 858869) B858869
theorem B638131 : Blo 377762 638131 := bstep (se 1 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 638131 = 957197) B957197
theorem B572609 : Blo 377762 572609 := bstep (se 2 (by rfl) ⟨214728, by rfl⟩ : syracuseStep 572609 = 429457) B429457
theorem B572627 : Blo 377762 572627 := bstep (se 1 (by rfl) ⟨429470, by rfl⟩ : syracuseStep 572627 = 858941) B858941
theorem B2309411 : Blo 377762 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B638273 : Blo 377762 638273 := bstep (se 2 (by rfl) ⟨239352, by rfl⟩ : syracuseStep 638273 = 478705) B478705
theorem B638401 : Blo 377762 638401 := bstep (se 2 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 638401 = 478801) B478801
theorem B638435 : Blo 377762 638435 := bstep (se 1 (by rfl) ⟨478826, by rfl⟩ : syracuseStep 638435 = 957653) B957653
theorem B933457 : Blo 377762 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B638563 : Blo 377762 638563 := bstep (se 1 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 638563 = 957845) B957845
theorem B966289 : Blo 377762 966289 := bstep (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) B724717
theorem B1916621 : Blo 377762 1916621 := bstep (se 3 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 1916621 = 718733) B718733
theorem B409315 : Blo 377762 409315 := bstep (se 1 (by rfl) ⟨306986, by rfl⟩ : syracuseStep 409315 = 613973) B613973
theorem B638705 : Blo 377762 638705 := bstep (se 2 (by rfl) ⟨239514, by rfl⟩ : syracuseStep 638705 = 479029) B479029
theorem B606035 : Blo 377762 606035 := bstep (se 1 (by rfl) ⟨454526, by rfl⟩ : syracuseStep 606035 = 909053) B909053
theorem B638833 : Blo 377762 638833 := bstep (se 2 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 638833 = 479125) B479125
theorem B638867 : Blo 377762 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B638995 : Blo 377762 638995 := bstep (se 1 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 638995 = 958493) B958493
theorem B2441285 : Blo 377762 2441285 := bstep (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) B457741
theorem B606323 : Blo 377762 606323 := bstep (se 1 (by rfl) ⟨454742, by rfl⟩ : syracuseStep 606323 = 909485) B909485
theorem B639137 : Blo 377762 639137 := bstep (se 2 (by rfl) ⟨239676, by rfl⟩ : syracuseStep 639137 = 479353) B479353
theorem B1097891 : Blo 377762 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B540913 : Blo 377762 540913 := bstep (se 2 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 540913 = 405685) B405685
theorem B4866317 : Blo 377762 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B639265 : Blo 377762 639265 := bstep (se 2 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 639265 = 479449) B479449
theorem B639299 : Blo 377762 639299 := bstep (se 1 (by rfl) ⟨479474, by rfl⟩ : syracuseStep 639299 = 958949) B958949
theorem B2769221 : Blo 377762 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B541009 : Blo 377762 541009 := bstep (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) B405757
theorem B639427 : Blo 377762 639427 := bstep (se 1 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 639427 = 959141) B959141
theorem B8176099 : Blo 377762 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B606739 : Blo 377762 606739 := bstep (se 1 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 606739 = 910109) B910109
theorem B639569 : Blo 377762 639569 := bstep (se 2 (by rfl) ⟨239838, by rfl⟩ : syracuseStep 639569 = 479677) B479677
theorem B2048611 : Blo 377762 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B5456497 : Blo 377762 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B639697 : Blo 377762 639697 := bstep (se 2 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 639697 = 479773) B479773
theorem B639731 : Blo 377762 639731 := bstep (se 1 (by rfl) ⟨479798, by rfl⟩ : syracuseStep 639731 = 959597) B959597
theorem B607009 : Blo 377762 607009 := bstep (se 2 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 607009 = 455257) B455257
theorem B541505 : Blo 377762 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B639859 : Blo 377762 639859 := bstep (se 1 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 639859 = 959789) B959789
theorem B377763 : Blo 377762 377763 := bstep (se 1 (by rfl) ⟨283322, by rfl⟩ : syracuseStep 377763 = 566645) B566645
theorem B377779 : Blo 377762 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B377795 : Blo 377762 377795 := bstep (se 1 (by rfl) ⟨283346, by rfl⟩ : syracuseStep 377795 = 566693) B566693
theorem B377811 : Blo 377762 377811 := bstep (se 1 (by rfl) ⟨283358, by rfl⟩ : syracuseStep 377811 = 566717) B566717
theorem B377827 : Blo 377762 377827 := bstep (se 1 (by rfl) ⟨283370, by rfl⟩ : syracuseStep 377827 = 566741) B566741
theorem B377843 : Blo 377762 377843 := bstep (se 1 (by rfl) ⟨283382, by rfl⟩ : syracuseStep 377843 = 566765) B566765
theorem B640001 : Blo 377762 640001 := bstep (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) B480001
theorem B377859 : Blo 377762 377859 := bstep (se 1 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 377859 = 566789) B566789
theorem B377875 : Blo 377762 377875 := bstep (se 1 (by rfl) ⟨283406, by rfl⟩ : syracuseStep 377875 = 566813) B566813
theorem B607265 : Blo 377762 607265 := bstep (se 2 (by rfl) ⟨227724, by rfl⟩ : syracuseStep 607265 = 455449) B455449
theorem B377891 : Blo 377762 377891 := bstep (se 1 (by rfl) ⟨283418, by rfl⟩ : syracuseStep 377891 = 566837) B566837
theorem B377907 : Blo 377762 377907 := bstep (se 1 (by rfl) ⟨283430, by rfl⟩ : syracuseStep 377907 = 566861) B566861
theorem B377923 : Blo 377762 377923 := bstep (se 1 (by rfl) ⟨283442, by rfl⟩ : syracuseStep 377923 = 566885) B566885
theorem B377939 : Blo 377762 377939 := bstep (se 1 (by rfl) ⟨283454, by rfl⟩ : syracuseStep 377939 = 566909) B566909
theorem B377955 : Blo 377762 377955 := bstep (se 1 (by rfl) ⟨283466, by rfl⟩ : syracuseStep 377955 = 566933) B566933
theorem B377971 : Blo 377762 377971 := bstep (se 1 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 377971 = 566957) B566957
theorem B640129 : Blo 377762 640129 := bstep (se 2 (by rfl) ⟨240048, by rfl⟩ : syracuseStep 640129 = 480097) B480097
theorem B377987 : Blo 377762 377987 := bstep (se 1 (by rfl) ⟨283490, by rfl⟩ : syracuseStep 377987 = 566981) B566981
theorem B9749645 : Blo 377762 9749645 := bstep (se 3 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 9749645 = 3656117) B3656117
theorem B378003 : Blo 377762 378003 := bstep (se 1 (by rfl) ⟨283502, by rfl⟩ : syracuseStep 378003 = 567005) B567005
theorem B378019 : Blo 377762 378019 := bstep (se 1 (by rfl) ⟨283514, by rfl⟩ : syracuseStep 378019 = 567029) B567029
theorem B640163 : Blo 377762 640163 := bstep (se 1 (by rfl) ⟨480122, by rfl⟩ : syracuseStep 640163 = 960245) B960245
theorem B378035 : Blo 377762 378035 := bstep (se 1 (by rfl) ⟨283526, by rfl⟩ : syracuseStep 378035 = 567053) B567053
theorem B378051 : Blo 377762 378051 := bstep (se 1 (by rfl) ⟨283538, by rfl⟩ : syracuseStep 378051 = 567077) B567077
theorem B378067 : Blo 377762 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B378083 : Blo 377762 378083 := bstep (se 1 (by rfl) ⟨283562, by rfl⟩ : syracuseStep 378083 = 567125) B567125
theorem B378099 : Blo 377762 378099 := bstep (se 1 (by rfl) ⟨283574, by rfl⟩ : syracuseStep 378099 = 567149) B567149
theorem B378115 : Blo 377762 378115 := bstep (se 1 (by rfl) ⟨283586, by rfl⟩ : syracuseStep 378115 = 567173) B567173
theorem B378131 : Blo 377762 378131 := bstep (se 1 (by rfl) ⟨283598, by rfl⟩ : syracuseStep 378131 = 567197) B567197
theorem B378147 : Blo 377762 378147 := bstep (se 1 (by rfl) ⟨283610, by rfl⟩ : syracuseStep 378147 = 567221) B567221
theorem B640291 : Blo 377762 640291 := bstep (se 1 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 640291 = 960437) B960437
theorem B378163 : Blo 377762 378163 := bstep (se 1 (by rfl) ⟨283622, by rfl⟩ : syracuseStep 378163 = 567245) B567245
theorem B378179 : Blo 377762 378179 := bstep (se 1 (by rfl) ⟨283634, by rfl⟩ : syracuseStep 378179 = 567269) B567269
theorem B2934085 : Blo 377762 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B378195 : Blo 377762 378195 := bstep (se 1 (by rfl) ⟨283646, by rfl⟩ : syracuseStep 378195 = 567293) B567293
theorem B378211 : Blo 377762 378211 := bstep (se 1 (by rfl) ⟨283658, by rfl⟩ : syracuseStep 378211 = 567317) B567317
theorem B378227 : Blo 377762 378227 := bstep (se 1 (by rfl) ⟨283670, by rfl⟩ : syracuseStep 378227 = 567341) B567341
theorem B378243 : Blo 377762 378243 := bstep (se 1 (by rfl) ⟨283682, by rfl⟩ : syracuseStep 378243 = 567365) B567365
theorem B378259 : Blo 377762 378259 := bstep (se 1 (by rfl) ⟨283694, by rfl⟩ : syracuseStep 378259 = 567389) B567389
theorem B378275 : Blo 377762 378275 := bstep (se 1 (by rfl) ⟨283706, by rfl⟩ : syracuseStep 378275 = 567413) B567413
theorem B640433 : Blo 377762 640433 := bstep (se 2 (by rfl) ⟨240162, by rfl⟩ : syracuseStep 640433 = 480325) B480325
theorem B378291 : Blo 377762 378291 := bstep (se 1 (by rfl) ⟨283718, by rfl⟩ : syracuseStep 378291 = 567437) B567437
theorem B1623473 : Blo 377762 1623473 := bstep (se 2 (by rfl) ⟨608802, by rfl⟩ : syracuseStep 1623473 = 1217605) B1217605
theorem B378307 : Blo 377762 378307 := bstep (se 1 (by rfl) ⟨283730, by rfl⟩ : syracuseStep 378307 = 567461) B567461
theorem B378323 : Blo 377762 378323 := bstep (se 1 (by rfl) ⟨283742, by rfl⟩ : syracuseStep 378323 = 567485) B567485
theorem B378339 : Blo 377762 378339 := bstep (se 1 (by rfl) ⟨283754, by rfl⟩ : syracuseStep 378339 = 567509) B567509
theorem B378355 : Blo 377762 378355 := bstep (se 1 (by rfl) ⟨283766, by rfl⟩ : syracuseStep 378355 = 567533) B567533
theorem B378371 : Blo 377762 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B574993 : Blo 377762 574993 := bstep (se 2 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 574993 = 431245) B431245
theorem B378387 : Blo 377762 378387 := bstep (se 1 (by rfl) ⟨283790, by rfl⟩ : syracuseStep 378387 = 567581) B567581
theorem B378403 : Blo 377762 378403 := bstep (se 1 (by rfl) ⟨283802, by rfl⟩ : syracuseStep 378403 = 567605) B567605
theorem B640561 : Blo 377762 640561 := bstep (se 2 (by rfl) ⟨240210, by rfl⟩ : syracuseStep 640561 = 480421) B480421
theorem B378419 : Blo 377762 378419 := bstep (se 1 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 378419 = 567629) B567629
theorem B378435 : Blo 377762 378435 := bstep (se 1 (by rfl) ⟨283826, by rfl⟩ : syracuseStep 378435 = 567653) B567653
theorem B378451 : Blo 377762 378451 := bstep (se 1 (by rfl) ⟨283838, by rfl⟩ : syracuseStep 378451 = 567677) B567677
theorem B640595 : Blo 377762 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B378467 : Blo 377762 378467 := bstep (se 1 (by rfl) ⟨283850, by rfl⟩ : syracuseStep 378467 = 567701) B567701
theorem B378483 : Blo 377762 378483 := bstep (se 1 (by rfl) ⟨283862, by rfl⟩ : syracuseStep 378483 = 567725) B567725
theorem B378499 : Blo 377762 378499 := bstep (se 1 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 378499 = 567749) B567749
theorem B378515 : Blo 377762 378515 := bstep (se 1 (by rfl) ⟨283886, by rfl⟩ : syracuseStep 378515 = 567773) B567773
theorem B542371 : Blo 377762 542371 := bstep (se 1 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 542371 = 813557) B813557
theorem B378531 : Blo 377762 378531 := bstep (se 1 (by rfl) ⟨283898, by rfl⟩ : syracuseStep 378531 = 567797) B567797
theorem B378547 : Blo 377762 378547 := bstep (se 1 (by rfl) ⟨283910, by rfl⟩ : syracuseStep 378547 = 567821) B567821
theorem B378563 : Blo 377762 378563 := bstep (se 1 (by rfl) ⟨283922, by rfl⟩ : syracuseStep 378563 = 567845) B567845
theorem B378579 : Blo 377762 378579 := bstep (se 1 (by rfl) ⟨283934, by rfl⟩ : syracuseStep 378579 = 567869) B567869
theorem B640723 : Blo 377762 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B607969 : Blo 377762 607969 := bstep (se 2 (by rfl) ⟨227988, by rfl⟩ : syracuseStep 607969 = 455977) B455977
theorem B378595 : Blo 377762 378595 := bstep (se 1 (by rfl) ⟨283946, by rfl⟩ : syracuseStep 378595 = 567893) B567893
theorem B378611 : Blo 377762 378611 := bstep (se 1 (by rfl) ⟨283958, by rfl⟩ : syracuseStep 378611 = 567917) B567917
theorem B542467 : Blo 377762 542467 := bstep (se 1 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 542467 = 813701) B813701
theorem B378627 : Blo 377762 378627 := bstep (se 1 (by rfl) ⟨283970, by rfl⟩ : syracuseStep 378627 = 567941) B567941
theorem B3131149 : Blo 377762 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B378643 : Blo 377762 378643 := bstep (se 1 (by rfl) ⟨283982, by rfl⟩ : syracuseStep 378643 = 567965) B567965
theorem B378659 : Blo 377762 378659 := bstep (se 1 (by rfl) ⟨283994, by rfl⟩ : syracuseStep 378659 = 567989) B567989
theorem B378675 : Blo 377762 378675 := bstep (se 1 (by rfl) ⟨284006, by rfl⟩ : syracuseStep 378675 = 568013) B568013
theorem B378691 : Blo 377762 378691 := bstep (se 1 (by rfl) ⟨284018, by rfl⟩ : syracuseStep 378691 = 568037) B568037
theorem B2475845 : Blo 377762 2475845 := bstep (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) B464221
theorem B378707 : Blo 377762 378707 := bstep (se 1 (by rfl) ⟨284030, by rfl⟩ : syracuseStep 378707 = 568061) B568061
theorem B640865 : Blo 377762 640865 := bstep (se 2 (by rfl) ⟨240324, by rfl⟩ : syracuseStep 640865 = 480649) B480649
theorem B378723 : Blo 377762 378723 := bstep (se 1 (by rfl) ⟨284042, by rfl⟩ : syracuseStep 378723 = 568085) B568085
theorem B378739 : Blo 377762 378739 := bstep (se 1 (by rfl) ⟨284054, by rfl⟩ : syracuseStep 378739 = 568109) B568109
theorem B378755 : Blo 377762 378755 := bstep (se 1 (by rfl) ⟨284066, by rfl⟩ : syracuseStep 378755 = 568133) B568133
theorem B378771 : Blo 377762 378771 := bstep (se 1 (by rfl) ⟨284078, by rfl⟩ : syracuseStep 378771 = 568157) B568157
theorem B378787 : Blo 377762 378787 := bstep (se 1 (by rfl) ⟨284090, by rfl⟩ : syracuseStep 378787 = 568181) B568181
theorem B378803 : Blo 377762 378803 := bstep (se 1 (by rfl) ⟨284102, by rfl⟩ : syracuseStep 378803 = 568205) B568205
theorem B378819 : Blo 377762 378819 := bstep (se 1 (by rfl) ⟨284114, by rfl⟩ : syracuseStep 378819 = 568229) B568229
theorem B378835 : Blo 377762 378835 := bstep (se 1 (by rfl) ⟨284126, by rfl⟩ : syracuseStep 378835 = 568253) B568253
theorem B640993 : Blo 377762 640993 := bstep (se 2 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 640993 = 480745) B480745
theorem B378851 : Blo 377762 378851 := bstep (se 1 (by rfl) ⟨284138, by rfl⟩ : syracuseStep 378851 = 568277) B568277
theorem B378867 : Blo 377762 378867 := bstep (se 1 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 378867 = 568301) B568301
theorem B378883 : Blo 377762 378883 := bstep (se 1 (by rfl) ⟨284162, by rfl⟩ : syracuseStep 378883 = 568325) B568325
theorem B641027 : Blo 377762 641027 := bstep (se 1 (by rfl) ⟨480770, by rfl⟩ : syracuseStep 641027 = 961541) B961541
theorem B378899 : Blo 377762 378899 := bstep (se 1 (by rfl) ⟨284174, by rfl⟩ : syracuseStep 378899 = 568349) B568349
theorem B378915 : Blo 377762 378915 := bstep (se 1 (by rfl) ⟨284186, by rfl⟩ : syracuseStep 378915 = 568373) B568373
theorem B378931 : Blo 377762 378931 := bstep (se 1 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 378931 = 568397) B568397
theorem B378947 : Blo 377762 378947 := bstep (se 1 (by rfl) ⟨284210, by rfl⟩ : syracuseStep 378947 = 568421) B568421
theorem B378963 : Blo 377762 378963 := bstep (se 1 (by rfl) ⟨284222, by rfl⟩ : syracuseStep 378963 = 568445) B568445
theorem B378979 : Blo 377762 378979 := bstep (se 1 (by rfl) ⟨284234, by rfl⟩ : syracuseStep 378979 = 568469) B568469
theorem B3295331 : Blo 377762 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1263725 : Blo 377762 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B378995 : Blo 377762 378995 := bstep (se 1 (by rfl) ⟨284246, by rfl⟩ : syracuseStep 378995 = 568493) B568493
theorem B379011 : Blo 377762 379011 := bstep (se 1 (by rfl) ⟨284258, by rfl⟩ : syracuseStep 379011 = 568517) B568517
theorem B641155 : Blo 377762 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B379027 : Blo 377762 379027 := bstep (se 1 (by rfl) ⟨284270, by rfl⟩ : syracuseStep 379027 = 568541) B568541
theorem B379043 : Blo 377762 379043 := bstep (se 1 (by rfl) ⟨284282, by rfl⟩ : syracuseStep 379043 = 568565) B568565
theorem B2050211 : Blo 377762 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B379059 : Blo 377762 379059 := bstep (se 1 (by rfl) ⟨284294, by rfl⟩ : syracuseStep 379059 = 568589) B568589
theorem B379075 : Blo 377762 379075 := bstep (se 1 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 379075 = 568613) B568613
theorem B379091 : Blo 377762 379091 := bstep (se 1 (by rfl) ⟨284318, by rfl⟩ : syracuseStep 379091 = 568637) B568637
theorem B379107 : Blo 377762 379107 := bstep (se 1 (by rfl) ⟨284330, by rfl⟩ : syracuseStep 379107 = 568661) B568661
theorem B379123 : Blo 377762 379123 := bstep (se 1 (by rfl) ⟨284342, by rfl⟩ : syracuseStep 379123 = 568685) B568685
theorem B542963 : Blo 377762 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B379139 : Blo 377762 379139 := bstep (se 1 (by rfl) ⟨284354, by rfl⟩ : syracuseStep 379139 = 568709) B568709
theorem B641297 : Blo 377762 641297 := bstep (se 2 (by rfl) ⟨240486, by rfl⟩ : syracuseStep 641297 = 480973) B480973
theorem B379155 : Blo 377762 379155 := bstep (se 1 (by rfl) ⟨284366, by rfl⟩ : syracuseStep 379155 = 568733) B568733
theorem B379171 : Blo 377762 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B379187 : Blo 377762 379187 := bstep (se 1 (by rfl) ⟨284390, by rfl⟩ : syracuseStep 379187 = 568781) B568781
theorem B379203 : Blo 377762 379203 := bstep (se 1 (by rfl) ⟨284402, by rfl⟩ : syracuseStep 379203 = 568805) B568805
theorem B379219 : Blo 377762 379219 := bstep (se 1 (by rfl) ⟨284414, by rfl⟩ : syracuseStep 379219 = 568829) B568829
theorem B379235 : Blo 377762 379235 := bstep (se 1 (by rfl) ⟨284426, by rfl⟩ : syracuseStep 379235 = 568853) B568853
theorem B379251 : Blo 377762 379251 := bstep (se 1 (by rfl) ⟨284438, by rfl⟩ : syracuseStep 379251 = 568877) B568877
theorem B379267 : Blo 377762 379267 := bstep (se 1 (by rfl) ⟨284450, by rfl⟩ : syracuseStep 379267 = 568901) B568901
theorem B641425 : Blo 377762 641425 := bstep (se 2 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 641425 = 481069) B481069
theorem B379283 : Blo 377762 379283 := bstep (se 1 (by rfl) ⟨284462, by rfl⟩ : syracuseStep 379283 = 568925) B568925
theorem B379299 : Blo 377762 379299 := bstep (se 1 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 379299 = 568949) B568949
theorem B379315 : Blo 377762 379315 := bstep (se 1 (by rfl) ⟨284486, by rfl⟩ : syracuseStep 379315 = 568973) B568973
theorem B641459 : Blo 377762 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B379331 : Blo 377762 379331 := bstep (se 1 (by rfl) ⟨284498, by rfl⟩ : syracuseStep 379331 = 568997) B568997
theorem B379347 : Blo 377762 379347 := bstep (se 1 (by rfl) ⟨284510, by rfl⟩ : syracuseStep 379347 = 569021) B569021
theorem B379363 : Blo 377762 379363 := bstep (se 1 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 379363 = 569045) B569045
theorem B379379 : Blo 377762 379379 := bstep (se 1 (by rfl) ⟨284534, by rfl⟩ : syracuseStep 379379 = 569069) B569069
theorem B379395 : Blo 377762 379395 := bstep (se 1 (by rfl) ⟨284546, by rfl⟩ : syracuseStep 379395 = 569093) B569093
theorem B379411 : Blo 377762 379411 := bstep (se 1 (by rfl) ⟨284558, by rfl⟩ : syracuseStep 379411 = 569117) B569117
theorem B379427 : Blo 377762 379427 := bstep (se 1 (by rfl) ⟨284570, by rfl⟩ : syracuseStep 379427 = 569141) B569141
theorem B1919537 : Blo 377762 1919537 := bstep (se 2 (by rfl) ⟨719826, by rfl⟩ : syracuseStep 1919537 = 1439653) B1439653
theorem B379443 : Blo 377762 379443 := bstep (se 1 (by rfl) ⟨284582, by rfl⟩ : syracuseStep 379443 = 569165) B569165
theorem B641587 : Blo 377762 641587 := bstep (se 1 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 641587 = 962381) B962381
theorem B379459 : Blo 377762 379459 := bstep (se 1 (by rfl) ⟨284594, by rfl⟩ : syracuseStep 379459 = 569189) B569189
theorem B2869829 : Blo 377762 2869829 := bstep (se 4 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 2869829 = 538093) B538093
theorem B379475 : Blo 377762 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B379491 : Blo 377762 379491 := bstep (se 1 (by rfl) ⟨284618, by rfl⟩ : syracuseStep 379491 = 569237) B569237
theorem B608867 : Blo 377762 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B379507 : Blo 377762 379507 := bstep (se 1 (by rfl) ⟨284630, by rfl⟩ : syracuseStep 379507 = 569261) B569261
theorem B379523 : Blo 377762 379523 := bstep (se 1 (by rfl) ⟨284642, by rfl⟩ : syracuseStep 379523 = 569285) B569285
theorem B379539 : Blo 377762 379539 := bstep (se 1 (by rfl) ⟨284654, by rfl⟩ : syracuseStep 379539 = 569309) B569309
theorem B379555 : Blo 377762 379555 := bstep (se 1 (by rfl) ⟨284666, by rfl⟩ : syracuseStep 379555 = 569333) B569333
theorem B379571 : Blo 377762 379571 := bstep (se 1 (by rfl) ⟨284678, by rfl⟩ : syracuseStep 379571 = 569357) B569357
theorem B641729 : Blo 377762 641729 := bstep (se 2 (by rfl) ⟨240648, by rfl⟩ : syracuseStep 641729 = 481297) B481297
theorem B379587 : Blo 377762 379587 := bstep (se 1 (by rfl) ⟨284690, by rfl⟩ : syracuseStep 379587 = 569381) B569381
theorem B379603 : Blo 377762 379603 := bstep (se 1 (by rfl) ⟨284702, by rfl⟩ : syracuseStep 379603 = 569405) B569405
theorem B379619 : Blo 377762 379619 := bstep (se 1 (by rfl) ⟨284714, by rfl⟩ : syracuseStep 379619 = 569429) B569429
theorem B379635 : Blo 377762 379635 := bstep (se 1 (by rfl) ⟨284726, by rfl⟩ : syracuseStep 379635 = 569453) B569453
theorem B379651 : Blo 377762 379651 := bstep (se 1 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 379651 = 569477) B569477
theorem B379667 : Blo 377762 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B609059 : Blo 377762 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B379683 : Blo 377762 379683 := bstep (se 1 (by rfl) ⟨284762, by rfl⟩ : syracuseStep 379683 = 569525) B569525
theorem B379699 : Blo 377762 379699 := bstep (se 1 (by rfl) ⟨284774, by rfl⟩ : syracuseStep 379699 = 569549) B569549
theorem B641857 : Blo 377762 641857 := bstep (se 2 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 641857 = 481393) B481393
theorem B379715 : Blo 377762 379715 := bstep (se 1 (by rfl) ⟨284786, by rfl⟩ : syracuseStep 379715 = 569573) B569573
theorem B379731 : Blo 377762 379731 := bstep (se 1 (by rfl) ⟨284798, by rfl⟩ : syracuseStep 379731 = 569597) B569597
theorem B969571 : Blo 377762 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B379747 : Blo 377762 379747 := bstep (se 1 (by rfl) ⟨284810, by rfl⟩ : syracuseStep 379747 = 569621) B569621
theorem B641891 : Blo 377762 641891 := bstep (se 1 (by rfl) ⟨481418, by rfl⟩ : syracuseStep 641891 = 962837) B962837
theorem B379763 : Blo 377762 379763 := bstep (se 1 (by rfl) ⟨284822, by rfl⟩ : syracuseStep 379763 = 569645) B569645
theorem B379779 : Blo 377762 379779 := bstep (se 1 (by rfl) ⟨284834, by rfl⟩ : syracuseStep 379779 = 569669) B569669
theorem B379795 : Blo 377762 379795 := bstep (se 1 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 379795 = 569693) B569693
theorem B379811 : Blo 377762 379811 := bstep (se 1 (by rfl) ⟨284858, by rfl⟩ : syracuseStep 379811 = 569717) B569717
theorem B379827 : Blo 377762 379827 := bstep (se 1 (by rfl) ⟨284870, by rfl⟩ : syracuseStep 379827 = 569741) B569741
theorem B379843 : Blo 377762 379843 := bstep (se 1 (by rfl) ⟨284882, by rfl⟩ : syracuseStep 379843 = 569765) B569765
theorem B478163 : Blo 377762 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B379859 : Blo 377762 379859 := bstep (se 1 (by rfl) ⟨284894, by rfl⟩ : syracuseStep 379859 = 569789) B569789
theorem B379875 : Blo 377762 379875 := bstep (se 1 (by rfl) ⟨284906, by rfl⟩ : syracuseStep 379875 = 569813) B569813
theorem B642019 : Blo 377762 642019 := bstep (se 1 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 642019 = 963029) B963029
theorem B379891 : Blo 377762 379891 := bstep (se 1 (by rfl) ⟨284918, by rfl⟩ : syracuseStep 379891 = 569837) B569837
theorem B379907 : Blo 377762 379907 := bstep (se 1 (by rfl) ⟨284930, by rfl⟩ : syracuseStep 379907 = 569861) B569861
theorem B379923 : Blo 377762 379923 := bstep (se 1 (by rfl) ⟨284942, by rfl⟩ : syracuseStep 379923 = 569885) B569885
theorem B379939 : Blo 377762 379939 := bstep (se 1 (by rfl) ⟨284954, by rfl⟩ : syracuseStep 379939 = 569909) B569909
theorem B379955 : Blo 377762 379955 := bstep (se 1 (by rfl) ⟨284966, by rfl⟩ : syracuseStep 379955 = 569933) B569933
theorem B379971 : Blo 377762 379971 := bstep (se 1 (by rfl) ⟨284978, by rfl⟩ : syracuseStep 379971 = 569957) B569957
theorem B379987 : Blo 377762 379987 := bstep (se 1 (by rfl) ⟨284990, by rfl⟩ : syracuseStep 379987 = 569981) B569981
theorem B380003 : Blo 377762 380003 := bstep (se 1 (by rfl) ⟨285002, by rfl⟩ : syracuseStep 380003 = 570005) B570005
theorem B642161 : Blo 377762 642161 := bstep (se 2 (by rfl) ⟨240810, by rfl⟩ : syracuseStep 642161 = 481621) B481621
theorem B380019 : Blo 377762 380019 := bstep (se 1 (by rfl) ⟨285014, by rfl⟩ : syracuseStep 380019 = 570029) B570029
theorem B380035 : Blo 377762 380035 := bstep (se 1 (by rfl) ⟨285026, by rfl⟩ : syracuseStep 380035 = 570053) B570053
theorem B2182277 : Blo 377762 2182277 := bstep (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) B409177
theorem B380051 : Blo 377762 380051 := bstep (se 1 (by rfl) ⟨285038, by rfl⟩ : syracuseStep 380051 = 570077) B570077
theorem B380067 : Blo 377762 380067 := bstep (se 1 (by rfl) ⟨285050, by rfl⟩ : syracuseStep 380067 = 570101) B570101
theorem B380083 : Blo 377762 380083 := bstep (se 1 (by rfl) ⟨285062, by rfl⟩ : syracuseStep 380083 = 570125) B570125
theorem B380099 : Blo 377762 380099 := bstep (se 1 (by rfl) ⟨285074, by rfl⟩ : syracuseStep 380099 = 570149) B570149
theorem B380115 : Blo 377762 380115 := bstep (se 1 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 380115 = 570173) B570173
theorem B511201 : Blo 377762 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B380131 : Blo 377762 380131 := bstep (se 1 (by rfl) ⟨285098, by rfl⟩ : syracuseStep 380131 = 570197) B570197
theorem B642289 : Blo 377762 642289 := bstep (se 2 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 642289 = 481717) B481717
theorem B380147 : Blo 377762 380147 := bstep (se 1 (by rfl) ⟨285110, by rfl⟩ : syracuseStep 380147 = 570221) B570221
theorem B380163 : Blo 377762 380163 := bstep (se 1 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 380163 = 570245) B570245
theorem B380179 : Blo 377762 380179 := bstep (se 1 (by rfl) ⟨285134, by rfl⟩ : syracuseStep 380179 = 570269) B570269
theorem B642323 : Blo 377762 642323 := bstep (se 1 (by rfl) ⟨481742, by rfl⟩ : syracuseStep 642323 = 963485) B963485
theorem B380195 : Blo 377762 380195 := bstep (se 1 (by rfl) ⟨285146, by rfl⟩ : syracuseStep 380195 = 570293) B570293
theorem B380211 : Blo 377762 380211 := bstep (se 1 (by rfl) ⟨285158, by rfl⟩ : syracuseStep 380211 = 570317) B570317
theorem B380227 : Blo 377762 380227 := bstep (se 1 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 380227 = 570341) B570341
theorem B380243 : Blo 377762 380243 := bstep (se 1 (by rfl) ⟨285182, by rfl⟩ : syracuseStep 380243 = 570365) B570365
theorem B511331 : Blo 377762 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B380259 : Blo 377762 380259 := bstep (se 1 (by rfl) ⟨285194, by rfl⟩ : syracuseStep 380259 = 570389) B570389
theorem B3231089 : Blo 377762 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B380275 : Blo 377762 380275 := bstep (se 1 (by rfl) ⟨285206, by rfl⟩ : syracuseStep 380275 = 570413) B570413
theorem B380291 : Blo 377762 380291 := bstep (se 1 (by rfl) ⟨285218, by rfl⟩ : syracuseStep 380291 = 570437) B570437
theorem B3165581 : Blo 377762 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B380307 : Blo 377762 380307 := bstep (se 1 (by rfl) ⟨285230, by rfl⟩ : syracuseStep 380307 = 570461) B570461
theorem B642451 : Blo 377762 642451 := bstep (se 1 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 642451 = 963677) B963677
theorem B380323 : Blo 377762 380323 := bstep (se 1 (by rfl) ⟨285242, by rfl⟩ : syracuseStep 380323 = 570485) B570485
theorem B380339 : Blo 377762 380339 := bstep (se 1 (by rfl) ⟨285254, by rfl⟩ : syracuseStep 380339 = 570509) B570509
theorem B380355 : Blo 377762 380355 := bstep (se 1 (by rfl) ⟨285266, by rfl⟩ : syracuseStep 380355 = 570533) B570533
theorem B380371 : Blo 377762 380371 := bstep (se 1 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 380371 = 570557) B570557
theorem B380387 : Blo 377762 380387 := bstep (se 1 (by rfl) ⟨285290, by rfl⟩ : syracuseStep 380387 = 570581) B570581
theorem B380403 : Blo 377762 380403 := bstep (se 1 (by rfl) ⟨285302, by rfl⟩ : syracuseStep 380403 = 570605) B570605
theorem B380419 : Blo 377762 380419 := bstep (se 1 (by rfl) ⟨285314, by rfl⟩ : syracuseStep 380419 = 570629) B570629
theorem B380435 : Blo 377762 380435 := bstep (se 1 (by rfl) ⟨285326, by rfl⟩ : syracuseStep 380435 = 570653) B570653
theorem B642593 : Blo 377762 642593 := bstep (se 2 (by rfl) ⟨240972, by rfl⟩ : syracuseStep 642593 = 481945) B481945
theorem B380451 : Blo 377762 380451 := bstep (se 1 (by rfl) ⟨285338, by rfl⟩ : syracuseStep 380451 = 570677) B570677
theorem B380467 : Blo 377762 380467 := bstep (se 1 (by rfl) ⟨285350, by rfl⟩ : syracuseStep 380467 = 570701) B570701
theorem B577091 : Blo 377762 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B380483 : Blo 377762 380483 := bstep (se 1 (by rfl) ⟨285362, by rfl⟩ : syracuseStep 380483 = 570725) B570725
theorem B380499 : Blo 377762 380499 := bstep (se 1 (by rfl) ⟨285374, by rfl⟩ : syracuseStep 380499 = 570749) B570749
theorem B380515 : Blo 377762 380515 := bstep (se 1 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 380515 = 570773) B570773
theorem B380531 : Blo 377762 380531 := bstep (se 1 (by rfl) ⟨285398, by rfl⟩ : syracuseStep 380531 = 570797) B570797
theorem B380547 : Blo 377762 380547 := bstep (se 1 (by rfl) ⟨285410, by rfl⟩ : syracuseStep 380547 = 570821) B570821
theorem B478867 : Blo 377762 478867 := bstep (se 1 (by rfl) ⟨359150, by rfl⟩ : syracuseStep 478867 = 718301) B718301
theorem B380563 : Blo 377762 380563 := bstep (se 1 (by rfl) ⟨285422, by rfl⟩ : syracuseStep 380563 = 570845) B570845
theorem B642721 : Blo 377762 642721 := bstep (se 2 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 642721 = 482041) B482041
theorem B380579 : Blo 377762 380579 := bstep (se 1 (by rfl) ⟨285434, by rfl⟩ : syracuseStep 380579 = 570869) B570869
theorem B380595 : Blo 377762 380595 := bstep (se 1 (by rfl) ⟨285446, by rfl⟩ : syracuseStep 380595 = 570893) B570893
theorem B380611 : Blo 377762 380611 := bstep (se 1 (by rfl) ⟨285458, by rfl⟩ : syracuseStep 380611 = 570917) B570917
theorem B642755 : Blo 377762 642755 := bstep (se 1 (by rfl) ⟨482066, by rfl⟩ : syracuseStep 642755 = 964133) B964133
theorem B511699 : Blo 377762 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B380627 : Blo 377762 380627 := bstep (se 1 (by rfl) ⟨285470, by rfl⟩ : syracuseStep 380627 = 570941) B570941
theorem B380643 : Blo 377762 380643 := bstep (se 1 (by rfl) ⟨285482, by rfl⟩ : syracuseStep 380643 = 570965) B570965
theorem B610033 : Blo 377762 610033 := bstep (se 2 (by rfl) ⟨228762, by rfl⟩ : syracuseStep 610033 = 457525) B457525
theorem B478963 : Blo 377762 478963 := bstep (se 1 (by rfl) ⟨359222, by rfl⟩ : syracuseStep 478963 = 718445) B718445
theorem B380659 : Blo 377762 380659 := bstep (se 1 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 380659 = 570989) B570989
theorem B380675 : Blo 377762 380675 := bstep (se 1 (by rfl) ⟨285506, by rfl⟩ : syracuseStep 380675 = 571013) B571013
theorem B380691 : Blo 377762 380691 := bstep (se 1 (by rfl) ⟨285518, by rfl⟩ : syracuseStep 380691 = 571037) B571037
theorem B380707 : Blo 377762 380707 := bstep (se 1 (by rfl) ⟨285530, by rfl⟩ : syracuseStep 380707 = 571061) B571061
theorem B380723 : Blo 377762 380723 := bstep (se 1 (by rfl) ⟨285542, by rfl⟩ : syracuseStep 380723 = 571085) B571085
theorem B380739 : Blo 377762 380739 := bstep (se 1 (by rfl) ⟨285554, by rfl⟩ : syracuseStep 380739 = 571109) B571109
theorem B642883 : Blo 377762 642883 := bstep (se 1 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 642883 = 964325) B964325
theorem B1625933 : Blo 377762 1625933 := bstep (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) B609725
theorem B380755 : Blo 377762 380755 := bstep (se 1 (by rfl) ⟨285566, by rfl⟩ : syracuseStep 380755 = 571133) B571133
theorem B380771 : Blo 377762 380771 := bstep (se 1 (by rfl) ⟨285578, by rfl⟩ : syracuseStep 380771 = 571157) B571157
theorem B380787 : Blo 377762 380787 := bstep (se 1 (by rfl) ⟨285590, by rfl⟩ : syracuseStep 380787 = 571181) B571181
theorem B380803 : Blo 377762 380803 := bstep (se 1 (by rfl) ⟨285602, by rfl⟩ : syracuseStep 380803 = 571205) B571205
theorem B380819 : Blo 377762 380819 := bstep (se 1 (by rfl) ⟨285614, by rfl⟩ : syracuseStep 380819 = 571229) B571229
theorem B380835 : Blo 377762 380835 := bstep (se 1 (by rfl) ⟨285626, by rfl⟩ : syracuseStep 380835 = 571253) B571253
theorem B380851 : Blo 377762 380851 := bstep (se 1 (by rfl) ⟨285638, by rfl⟩ : syracuseStep 380851 = 571277) B571277
theorem B380867 : Blo 377762 380867 := bstep (se 1 (by rfl) ⟨285650, by rfl⟩ : syracuseStep 380867 = 571301) B571301
theorem B643025 : Blo 377762 643025 := bstep (se 2 (by rfl) ⟨241134, by rfl⟩ : syracuseStep 643025 = 482269) B482269
theorem B380883 : Blo 377762 380883 := bstep (se 1 (by rfl) ⟨285662, by rfl⟩ : syracuseStep 380883 = 571325) B571325
theorem B1920995 : Blo 377762 1920995 := bstep (se 1 (by rfl) ⟨1440746, by rfl⟩ : syracuseStep 1920995 = 2881493) B2881493
theorem B380899 : Blo 377762 380899 := bstep (se 1 (by rfl) ⟨285674, by rfl⟩ : syracuseStep 380899 = 571349) B571349
theorem B380915 : Blo 377762 380915 := bstep (se 1 (by rfl) ⟨285686, by rfl⟩ : syracuseStep 380915 = 571373) B571373
theorem B380931 : Blo 377762 380931 := bstep (se 1 (by rfl) ⟨285698, by rfl⟩ : syracuseStep 380931 = 571397) B571397
theorem B380947 : Blo 377762 380947 := bstep (se 1 (by rfl) ⟨285710, by rfl⟩ : syracuseStep 380947 = 571421) B571421
theorem B380963 : Blo 377762 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B380979 : Blo 377762 380979 := bstep (se 1 (by rfl) ⟨285734, by rfl⟩ : syracuseStep 380979 = 571469) B571469
theorem B380995 : Blo 377762 380995 := bstep (se 1 (by rfl) ⟨285746, by rfl⟩ : syracuseStep 380995 = 571493) B571493
theorem B643153 : Blo 377762 643153 := bstep (se 2 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 643153 = 482365) B482365
theorem B381011 : Blo 377762 381011 := bstep (se 1 (by rfl) ⟨285758, by rfl⟩ : syracuseStep 381011 = 571517) B571517
theorem B381027 : Blo 377762 381027 := bstep (se 1 (by rfl) ⟨285770, by rfl⟩ : syracuseStep 381027 = 571541) B571541
theorem B381043 : Blo 377762 381043 := bstep (se 1 (by rfl) ⟨285782, by rfl⟩ : syracuseStep 381043 = 571565) B571565
theorem B643187 : Blo 377762 643187 := bstep (se 1 (by rfl) ⟨482390, by rfl⟩ : syracuseStep 643187 = 964781) B964781
theorem B381059 : Blo 377762 381059 := bstep (se 1 (by rfl) ⟨285794, by rfl⟩ : syracuseStep 381059 = 571589) B571589
theorem B381075 : Blo 377762 381075 := bstep (se 1 (by rfl) ⟨285806, by rfl⟩ : syracuseStep 381075 = 571613) B571613
theorem B381091 : Blo 377762 381091 := bstep (se 1 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 381091 = 571637) B571637
theorem B610481 : Blo 377762 610481 := bstep (se 2 (by rfl) ⟨228930, by rfl⟩ : syracuseStep 610481 = 457861) B457861
theorem B381107 : Blo 377762 381107 := bstep (se 1 (by rfl) ⟨285830, by rfl⟩ : syracuseStep 381107 = 571661) B571661
theorem B381123 : Blo 377762 381123 := bstep (se 1 (by rfl) ⟨285842, by rfl⟩ : syracuseStep 381123 = 571685) B571685
theorem B381139 : Blo 377762 381139 := bstep (se 1 (by rfl) ⟨285854, by rfl⟩ : syracuseStep 381139 = 571709) B571709
theorem B479459 : Blo 377762 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B381155 : Blo 377762 381155 := bstep (se 1 (by rfl) ⟨285866, by rfl⟩ : syracuseStep 381155 = 571733) B571733
theorem B381171 : Blo 377762 381171 := bstep (se 1 (by rfl) ⟨285878, by rfl⟩ : syracuseStep 381171 = 571757) B571757
theorem B643315 : Blo 377762 643315 := bstep (se 1 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 643315 = 964973) B964973
theorem B381187 : Blo 377762 381187 := bstep (se 1 (by rfl) ⟨285890, by rfl⟩ : syracuseStep 381187 = 571781) B571781
theorem B381203 : Blo 377762 381203 := bstep (se 1 (by rfl) ⟨285902, by rfl⟩ : syracuseStep 381203 = 571805) B571805
theorem B381219 : Blo 377762 381219 := bstep (se 1 (by rfl) ⟨285914, by rfl⟩ : syracuseStep 381219 = 571829) B571829
theorem B381235 : Blo 377762 381235 := bstep (se 1 (by rfl) ⟨285926, by rfl⟩ : syracuseStep 381235 = 571853) B571853
theorem B381251 : Blo 377762 381251 := bstep (se 1 (by rfl) ⟨285938, by rfl⟩ : syracuseStep 381251 = 571877) B571877
theorem B381267 : Blo 377762 381267 := bstep (se 1 (by rfl) ⟨285950, by rfl⟩ : syracuseStep 381267 = 571901) B571901
theorem B381283 : Blo 377762 381283 := bstep (se 1 (by rfl) ⟨285962, by rfl⟩ : syracuseStep 381283 = 571925) B571925
theorem B381299 : Blo 377762 381299 := bstep (se 1 (by rfl) ⟨285974, by rfl⟩ : syracuseStep 381299 = 571949) B571949
theorem B643457 : Blo 377762 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B381315 : Blo 377762 381315 := bstep (se 1 (by rfl) ⟨285986, by rfl⟩ : syracuseStep 381315 = 571973) B571973
theorem B381331 : Blo 377762 381331 := bstep (se 1 (by rfl) ⟨285998, by rfl⟩ : syracuseStep 381331 = 571997) B571997
theorem B381347 : Blo 377762 381347 := bstep (se 1 (by rfl) ⟨286010, by rfl⟩ : syracuseStep 381347 = 572021) B572021
theorem B381363 : Blo 377762 381363 := bstep (se 1 (by rfl) ⟨286022, by rfl⟩ : syracuseStep 381363 = 572045) B572045
theorem B381379 : Blo 377762 381379 := bstep (se 1 (by rfl) ⟨286034, by rfl⟩ : syracuseStep 381379 = 572069) B572069
theorem B381395 : Blo 377762 381395 := bstep (se 1 (by rfl) ⟨286046, by rfl⟩ : syracuseStep 381395 = 572093) B572093
theorem B381411 : Blo 377762 381411 := bstep (se 1 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 381411 = 572117) B572117
theorem B381427 : Blo 377762 381427 := bstep (se 1 (by rfl) ⟨286070, by rfl⟩ : syracuseStep 381427 = 572141) B572141
theorem B643585 : Blo 377762 643585 := bstep (se 2 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 643585 = 482689) B482689
theorem B381443 : Blo 377762 381443 := bstep (se 1 (by rfl) ⟨286082, by rfl⟩ : syracuseStep 381443 = 572165) B572165
theorem B381459 : Blo 377762 381459 := bstep (se 1 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 381459 = 572189) B572189
theorem B643619 : Blo 377762 643619 := bstep (se 1 (by rfl) ⟨482714, by rfl⟩ : syracuseStep 643619 = 965429) B965429
theorem B381475 : Blo 377762 381475 := bstep (se 1 (by rfl) ⟨286106, by rfl⟩ : syracuseStep 381475 = 572213) B572213
theorem B381491 : Blo 377762 381491 := bstep (se 1 (by rfl) ⟨286118, by rfl⟩ : syracuseStep 381491 = 572237) B572237
theorem B381507 : Blo 377762 381507 := bstep (se 1 (by rfl) ⟨286130, by rfl⟩ : syracuseStep 381507 = 572261) B572261
theorem B2609741 : Blo 377762 2609741 := bstep (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) B978653
theorem B381523 : Blo 377762 381523 := bstep (se 1 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 381523 = 572285) B572285
theorem B381539 : Blo 377762 381539 := bstep (se 1 (by rfl) ⟨286154, by rfl⟩ : syracuseStep 381539 = 572309) B572309
theorem B381555 : Blo 377762 381555 := bstep (se 1 (by rfl) ⟨286166, by rfl⟩ : syracuseStep 381555 = 572333) B572333
theorem B578179 : Blo 377762 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B381571 : Blo 377762 381571 := bstep (se 1 (by rfl) ⟨286178, by rfl⟩ : syracuseStep 381571 = 572357) B572357
theorem B381587 : Blo 377762 381587 := bstep (se 1 (by rfl) ⟨286190, by rfl⟩ : syracuseStep 381587 = 572381) B572381
theorem B643747 : Blo 377762 643747 := bstep (se 1 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 643747 = 965621) B965621
theorem B381603 : Blo 377762 381603 := bstep (se 1 (by rfl) ⟨286202, by rfl⟩ : syracuseStep 381603 = 572405) B572405
theorem B381619 : Blo 377762 381619 := bstep (se 1 (by rfl) ⟨286214, by rfl⟩ : syracuseStep 381619 = 572429) B572429
theorem B381635 : Blo 377762 381635 := bstep (se 1 (by rfl) ⟨286226, by rfl⟩ : syracuseStep 381635 = 572453) B572453
theorem B381651 : Blo 377762 381651 := bstep (se 1 (by rfl) ⟨286238, by rfl⟩ : syracuseStep 381651 = 572477) B572477
theorem B381667 : Blo 377762 381667 := bstep (se 1 (by rfl) ⟨286250, by rfl⟩ : syracuseStep 381667 = 572501) B572501
theorem B1299181 : Blo 377762 1299181 := bstep (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) B487193
theorem B381683 : Blo 377762 381683 := bstep (se 1 (by rfl) ⟨286262, by rfl⟩ : syracuseStep 381683 = 572525) B572525
theorem B381699 : Blo 377762 381699 := bstep (se 1 (by rfl) ⟨286274, by rfl⟩ : syracuseStep 381699 = 572549) B572549
theorem B1921805 : Blo 377762 1921805 := bstep (se 3 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 1921805 = 720677) B720677
theorem B381715 : Blo 377762 381715 := bstep (se 1 (by rfl) ⟨286286, by rfl⟩ : syracuseStep 381715 = 572573) B572573
theorem B381731 : Blo 377762 381731 := bstep (se 1 (by rfl) ⟨286298, by rfl⟩ : syracuseStep 381731 = 572597) B572597
theorem B643889 : Blo 377762 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B381747 : Blo 377762 381747 := bstep (se 1 (by rfl) ⟨286310, by rfl⟩ : syracuseStep 381747 = 572621) B572621
theorem B1364849 : Blo 377762 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B480163 : Blo 377762 480163 := bstep (se 1 (by rfl) ⟨360122, by rfl⟩ : syracuseStep 480163 = 720245) B720245
theorem B644017 : Blo 377762 644017 := bstep (se 2 (by rfl) ⟨241506, by rfl⟩ : syracuseStep 644017 = 483013) B483013
theorem B644051 : Blo 377762 644051 := bstep (se 1 (by rfl) ⟨483038, by rfl⟩ : syracuseStep 644051 = 966077) B966077
theorem B480259 : Blo 377762 480259 := bstep (se 1 (by rfl) ⟨360194, by rfl⟩ : syracuseStep 480259 = 720389) B720389
theorem B644179 : Blo 377762 644179 := bstep (se 1 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 644179 = 966269) B966269
theorem B1627249 : Blo 377762 1627249 := bstep (se 2 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 1627249 = 1220437) B1220437
theorem B1496227 : Blo 377762 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B2053453 : Blo 377762 2053453 := bstep (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) B770045
theorem B2807237 : Blo 377762 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B480755 : Blo 377762 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B1464227 : Blo 377762 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B546817 : Blo 377762 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B481459 : Blo 377762 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B481555 : Blo 377762 481555 := bstep (se 1 (by rfl) ⟨361166, by rfl⟩ : syracuseStep 481555 = 722333) B722333
theorem B2185805 : Blo 377762 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B2153101 : Blo 377762 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B809635 : Blo 377762 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B580259 : Blo 377762 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B482051 : Blo 377762 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B482755 : Blo 377762 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B810481 : Blo 377762 810481 := bstep (se 2 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 810481 = 607861) B607861
theorem B482851 : Blo 377762 482851 := bstep (se 1 (by rfl) ⟨362138, by rfl⟩ : syracuseStep 482851 = 724277) B724277
theorem B515651 : Blo 377762 515651 := bstep (se 1 (by rfl) ⟨386738, by rfl⟩ : syracuseStep 515651 = 773477) B773477
theorem B1924721 : Blo 377762 1924721 := bstep (se 2 (by rfl) ⟨721770, by rfl⟩ : syracuseStep 1924721 = 1443541) B1443541
theorem B908995 : Blo 377762 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B974531 : Blo 377762 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B2056049 : Blo 377762 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B2318213 : Blo 377762 2318213 := bstep (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) B434665
theorem B1630307 : Blo 377762 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B1532045 : Blo 377762 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B2875661 : Blo 377762 2875661 := bstep (se 3 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 2875661 = 1078373) B1078373
theorem B909667 : Blo 377762 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B2155085 : Blo 377762 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B910129 : Blo 377762 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B680881 : Blo 377762 680881 := bstep (se 2 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 680881 = 510661) B510661
theorem B1926179 : Blo 377762 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B681041 : Blo 377762 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B2057413 : Blo 377762 2057413 := bstep (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) B385765
theorem B1369315 : Blo 377762 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B812369 : Blo 377762 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B3466637 : Blo 377762 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B2156017 : Blo 377762 2156017 := bstep (se 2 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 2156017 = 1617013) B1617013
theorem B2320163 : Blo 377762 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B1926989 : Blo 377762 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B1370353 : Blo 377762 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B2320817 : Blo 377762 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1436237 : Blo 377762 1436237 := bstep (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) B538589
theorem B813667 : Blo 377762 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B2746993 : Blo 377762 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B5073635 : Blo 377762 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B4320053 : Blo 377762 4320053 := bstep (se 5 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 4320053 = 405005) B405005
theorem B2157475 : Blo 377762 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B1076141 : Blo 377762 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B486371 : Blo 377762 486371 := bstep (se 1 (by rfl) ⟨364778, by rfl⟩ : syracuseStep 486371 = 729557) B729557
theorem B650273 : Blo 377762 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B1076323 : Blo 377762 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B2878577 : Blo 377762 2878577 := bstep (se 2 (by rfl) ⟨1079466, by rfl⟩ : syracuseStep 2878577 = 2158933) B2158933
theorem B1076483 : Blo 377762 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B1437041 : Blo 377762 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B2158001 : Blo 377762 2158001 := bstep (se 2 (by rfl) ⟨809250, by rfl⟩ : syracuseStep 2158001 = 1618501) B1618501
theorem B1535537 : Blo 377762 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B454243 : Blo 377762 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B3272333 : Blo 377762 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B814897 : Blo 377762 814897 := bstep (se 2 (by rfl) ⟨305586, by rfl⟩ : syracuseStep 814897 = 611173) B611173
theorem B1437709 : Blo 377762 1437709 := bstep (se 3 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 1437709 = 539141) B539141
theorem B520435 : Blo 377762 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B2060549 : Blo 377762 2060549 := bstep (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) B386353
theorem B1077553 : Blo 377762 1077553 := bstep (se 2 (by rfl) ⟨404082, by rfl⟩ : syracuseStep 1077553 = 808165) B808165
theorem B717169 : Blo 377762 717169 := bstep (se 2 (by rfl) ⟨268938, by rfl⟩ : syracuseStep 717169 = 537877) B537877
theorem B717329 : Blo 377762 717329 := bstep (se 2 (by rfl) ⟨268998, by rfl⟩ : syracuseStep 717329 = 537997) B537997
theorem B1536653 : Blo 377762 1536653 := bstep (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) B576245
theorem B1929905 : Blo 377762 1929905 := bstep (se 2 (by rfl) ⟨723714, by rfl⟩ : syracuseStep 1929905 = 1447429) B1447429
theorem B1438499 : Blo 377762 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B619331 : Blo 377762 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B2159459 : Blo 377762 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B717731 : Blo 377762 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B914435 : Blo 377762 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B2421829 : Blo 377762 2421829 := bstep (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) B454093
theorem B1274993 : Blo 377762 1274993 := bstep (se 2 (by rfl) ⟨478122, by rfl⟩ : syracuseStep 1274993 = 956245) B956245
theorem B2454725 : Blo 377762 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B914723 : Blo 377762 914723 := bstep (se 1 (by rfl) ⟨686042, by rfl⟩ : syracuseStep 914723 = 1372085) B1372085
theorem B455987 : Blo 377762 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B456035 : Blo 377762 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B4388195 : Blo 377762 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B521635 : Blo 377762 521635 := bstep (se 1 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 521635 = 782453) B782453
theorem B1439153 : Blo 377762 1439153 := bstep (se 2 (by rfl) ⟨539682, by rfl⟩ : syracuseStep 1439153 = 1079365) B1079365
theorem B456131 : Blo 377762 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B914915 : Blo 377762 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B1078829 : Blo 377762 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B1275533 : Blo 377762 1275533 := bstep (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) B478325
theorem B1275587 : Blo 377762 1275587 := bstep (se 1 (by rfl) ⟨956690, by rfl⟩ : syracuseStep 1275587 = 1913381) B1913381
theorem B1079011 : Blo 377762 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B1079057 : Blo 377762 1079057 := bstep (se 2 (by rfl) ⟨404646, by rfl⟩ : syracuseStep 1079057 = 809293) B809293
theorem B718627 : Blo 377762 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B685955 : Blo 377762 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B1832867 : Blo 377762 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B718787 : Blo 377762 718787 := bstep (se 1 (by rfl) ⟨539090, by rfl⟩ : syracuseStep 718787 = 1078181) B1078181
theorem B1275857 : Blo 377762 1275857 := bstep (se 2 (by rfl) ⟨478446, by rfl⟩ : syracuseStep 1275857 = 956893) B956893
theorem B1210403 : Blo 377762 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B1931363 : Blo 377762 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B850193 : Blo 377762 850193 := bstep (se 2 (by rfl) ⟨318822, by rfl⟩ : syracuseStep 850193 = 637645) B637645
theorem B850211 : Blo 377762 850211 := bstep (se 1 (by rfl) ⟨637658, by rfl⟩ : syracuseStep 850211 = 1275317) B1275317
theorem B915761 : Blo 377762 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B915875 : Blo 377762 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B1210801 : Blo 377762 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B9238981 : Blo 377762 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B1276397 : Blo 377762 1276397 := bstep (se 3 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 1276397 = 478649) B478649
theorem B1276451 : Blo 377762 1276451 := bstep (se 1 (by rfl) ⟨957338, by rfl⟩ : syracuseStep 1276451 = 1914677) B1914677
theorem B850481 : Blo 377762 850481 := bstep (se 2 (by rfl) ⟨318930, by rfl⟩ : syracuseStep 850481 = 637861) B637861
theorem B850499 : Blo 377762 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B916049 : Blo 377762 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B6486641 : Blo 377762 6486641 := bstep (se 2 (by rfl) ⟨2432490, by rfl⟩ : syracuseStep 6486641 = 4864981) B4864981
theorem B2161349 : Blo 377762 2161349 := bstep (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) B405253
theorem B1276721 : Blo 377762 1276721 := bstep (se 2 (by rfl) ⟨478770, by rfl⟩ : syracuseStep 1276721 = 957541) B957541
theorem B850769 : Blo 377762 850769 := bstep (se 2 (by rfl) ⟨319038, by rfl⟩ : syracuseStep 850769 = 638077) B638077
theorem B850787 : Blo 377762 850787 := bstep (se 1 (by rfl) ⟨638090, by rfl⟩ : syracuseStep 850787 = 1276181) B1276181
theorem B1440611 : Blo 377762 1440611 := bstep (se 1 (by rfl) ⟨1080458, by rfl⟩ : syracuseStep 1440611 = 2160917) B2160917
theorem B1211249 : Blo 377762 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B1440625 : Blo 377762 1440625 := bstep (se 2 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 1440625 = 1080469) B1080469
theorem B1932173 : Blo 377762 1932173 := bstep (se 3 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 1932173 = 724565) B724565
theorem B719857 : Blo 377762 719857 := bstep (se 2 (by rfl) ⟨269946, by rfl⟩ : syracuseStep 719857 = 539893) B539893
theorem B425011 : Blo 377762 425011 := bstep (se 1 (by rfl) ⟨318758, by rfl⟩ : syracuseStep 425011 = 637517) B637517
theorem B851057 : Blo 377762 851057 := bstep (se 2 (by rfl) ⟨319146, by rfl⟩ : syracuseStep 851057 = 638293) B638293
theorem B851075 : Blo 377762 851075 := bstep (se 1 (by rfl) ⟨638306, by rfl⟩ : syracuseStep 851075 = 1276613) B1276613
theorem B425155 : Blo 377762 425155 := bstep (se 1 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 425155 = 637733) B637733
theorem B1080515 : Blo 377762 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B1539299 : Blo 377762 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B3702029 : Blo 377762 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B1277261 : Blo 377762 1277261 := bstep (se 3 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 1277261 = 478973) B478973
theorem B425299 : Blo 377762 425299 := bstep (se 1 (by rfl) ⟨318974, by rfl⟩ : syracuseStep 425299 = 637949) B637949
theorem B1277315 : Blo 377762 1277315 := bstep (se 1 (by rfl) ⟨957986, by rfl⟩ : syracuseStep 1277315 = 1915973) B1915973
theorem B851345 : Blo 377762 851345 := bstep (se 2 (by rfl) ⟨319254, by rfl⟩ : syracuseStep 851345 = 638509) B638509
theorem B851363 : Blo 377762 851363 := bstep (se 1 (by rfl) ⟨638522, by rfl⟩ : syracuseStep 851363 = 1277045) B1277045
theorem B425443 : Blo 377762 425443 := bstep (se 1 (by rfl) ⟨319082, by rfl⟩ : syracuseStep 425443 = 638165) B638165
theorem B425587 : Blo 377762 425587 := bstep (se 1 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 425587 = 638381) B638381
theorem B1277585 : Blo 377762 1277585 := bstep (se 2 (by rfl) ⟨479094, by rfl⟩ : syracuseStep 1277585 = 958189) B958189
theorem B851633 : Blo 377762 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B851651 : Blo 377762 851651 := bstep (se 1 (by rfl) ⟨638738, by rfl⟩ : syracuseStep 851651 = 1277477) B1277477
theorem B818915 : Blo 377762 818915 := bstep (se 1 (by rfl) ⟨614186, by rfl⟩ : syracuseStep 818915 = 1228373) B1228373
theorem B425731 : Blo 377762 425731 := bstep (se 1 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 425731 = 638597) B638597
theorem B425875 : Blo 377762 425875 := bstep (se 1 (by rfl) ⟨319406, by rfl⟩ : syracuseStep 425875 = 638813) B638813
theorem B851921 : Blo 377762 851921 := bstep (se 2 (by rfl) ⟨319470, by rfl⟩ : syracuseStep 851921 = 638941) B638941
theorem B851939 : Blo 377762 851939 := bstep (se 1 (by rfl) ⟨638954, by rfl⟩ : syracuseStep 851939 = 1277909) B1277909
theorem B851993 : Blo 377762 851993 := bstep (se 2 (by rfl) ⟨319497, by rfl⟩ : syracuseStep 851993 = 638995) B638995
theorem B1278017 : Blo 377762 1278017 := bstep (se 2 (by rfl) ⟨479256, by rfl⟩ : syracuseStep 1278017 = 958513) B958513
theorem B426091 : Blo 377762 426091 := bstep (se 1 (by rfl) ⟨319568, by rfl⟩ : syracuseStep 426091 = 639137) B639137
theorem B852083 : Blo 377762 852083 := bstep (se 1 (by rfl) ⟨639062, by rfl⟩ : syracuseStep 852083 = 1278125) B1278125
theorem B852119 : Blo 377762 852119 := bstep (se 1 (by rfl) ⟨639089, by rfl⟩ : syracuseStep 852119 = 1278179) B1278179
theorem B3244211 : Blo 377762 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B426199 : Blo 377762 426199 := bstep (se 1 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 426199 = 639299) B639299
theorem B721163 : Blo 377762 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B721217 : Blo 377762 721217 := bstep (se 2 (by rfl) ⟨270456, by rfl⟩ : syracuseStep 721217 = 540913) B540913
theorem B852299 : Blo 377762 852299 := bstep (se 1 (by rfl) ⟨639224, by rfl⟩ : syracuseStep 852299 = 1278449) B1278449
theorem B852353 : Blo 377762 852353 := bstep (se 2 (by rfl) ⟨319632, by rfl⟩ : syracuseStep 852353 = 639265) B639265
theorem B426379 : Blo 377762 426379 := bstep (se 1 (by rfl) ⟨319784, by rfl⟩ : syracuseStep 426379 = 639569) B639569
theorem B1212889 : Blo 377762 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B426487 : Blo 377762 426487 := bstep (se 1 (by rfl) ⟨319865, by rfl⟩ : syracuseStep 426487 = 639731) B639731
theorem B852569 : Blo 377762 852569 := bstep (se 2 (by rfl) ⟨319713, by rfl⟩ : syracuseStep 852569 = 639427) B639427
theorem B1278557 : Blo 377762 1278557 := bstep (se 3 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 1278557 = 479459) B479459
theorem B426667 : Blo 377762 426667 := bstep (se 1 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 426667 = 640001) B640001
theorem B852659 : Blo 377762 852659 := bstep (se 1 (by rfl) ⟨639494, by rfl⟩ : syracuseStep 852659 = 1278989) B1278989
theorem B852695 : Blo 377762 852695 := bstep (se 1 (by rfl) ⟨639521, by rfl⟩ : syracuseStep 852695 = 1279043) B1279043
theorem B426775 : Blo 377762 426775 := bstep (se 1 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 426775 = 640163) B640163
theorem B7275329 : Blo 377762 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B852875 : Blo 377762 852875 := bstep (se 1 (by rfl) ⟨639656, by rfl⟩ : syracuseStep 852875 = 1279313) B1279313
theorem B852929 : Blo 377762 852929 := bstep (se 2 (by rfl) ⟨319848, by rfl⟩ : syracuseStep 852929 = 639697) B639697
theorem B426955 : Blo 377762 426955 := bstep (se 1 (by rfl) ⟨320216, by rfl⟩ : syracuseStep 426955 = 640433) B640433
theorem B1082315 : Blo 377762 1082315 := bstep (se 1 (by rfl) ⟨811736, by rfl⟩ : syracuseStep 1082315 = 1623473) B1623473
theorem B427063 : Blo 377762 427063 := bstep (se 1 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 427063 = 640595) B640595
theorem B1213505 : Blo 377762 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B853145 : Blo 377762 853145 := bstep (se 2 (by rfl) ⟨319929, by rfl⟩ : syracuseStep 853145 = 639859) B639859
theorem B722135 : Blo 377762 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B427243 : Blo 377762 427243 := bstep (se 1 (by rfl) ⟨320432, by rfl⟩ : syracuseStep 427243 = 640865) B640865
theorem B853235 : Blo 377762 853235 := bstep (se 1 (by rfl) ⟨639926, by rfl⟩ : syracuseStep 853235 = 1279853) B1279853
theorem B853271 : Blo 377762 853271 := bstep (se 1 (by rfl) ⟨639953, by rfl⟩ : syracuseStep 853271 = 1279907) B1279907
theorem B427351 : Blo 377762 427351 := bstep (se 1 (by rfl) ⟨320513, by rfl⟩ : syracuseStep 427351 = 641027) B641027
theorem B2196887 : Blo 377762 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B853451 : Blo 377762 853451 := bstep (se 1 (by rfl) ⟨640088, by rfl⟩ : syracuseStep 853451 = 1280177) B1280177
theorem B853505 : Blo 377762 853505 := bstep (se 2 (by rfl) ⟨320064, by rfl⟩ : syracuseStep 853505 = 640129) B640129
theorem B427531 : Blo 377762 427531 := bstep (se 1 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 427531 = 641297) B641297
theorem B427639 : Blo 377762 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B1279691 : Blo 377762 1279691 := bstep (se 1 (by rfl) ⟨959768, by rfl⟩ : syracuseStep 1279691 = 1919537) B1919537
theorem B853721 : Blo 377762 853721 := bstep (se 2 (by rfl) ⟨320145, by rfl⟩ : syracuseStep 853721 = 640291) B640291
theorem B722675 : Blo 377762 722675 := bstep (se 1 (by rfl) ⟨542006, by rfl⟩ : syracuseStep 722675 = 1084013) B1084013
theorem B2885381 : Blo 377762 2885381 := bstep (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) B541009
theorem B427819 : Blo 377762 427819 := bstep (se 1 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 427819 = 641729) B641729
theorem B853811 : Blo 377762 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B853847 : Blo 377762 853847 := bstep (se 1 (by rfl) ⟨640385, by rfl⟩ : syracuseStep 853847 = 1280771) B1280771
theorem B427927 : Blo 377762 427927 := bstep (se 1 (by rfl) ⟨320945, by rfl⟩ : syracuseStep 427927 = 641891) B641891
theorem B1279961 : Blo 377762 1279961 := bstep (se 2 (by rfl) ⟨479985, by rfl⟩ : syracuseStep 1279961 = 959971) B959971
theorem B854027 : Blo 377762 854027 := bstep (se 1 (by rfl) ⟨640520, by rfl⟩ : syracuseStep 854027 = 1281041) B1281041
theorem B854081 : Blo 377762 854081 := bstep (se 2 (by rfl) ⟨320280, by rfl⟩ : syracuseStep 854081 = 640561) B640561
theorem B428107 : Blo 377762 428107 := bstep (se 1 (by rfl) ⟨321080, by rfl⟩ : syracuseStep 428107 = 642161) B642161
theorem B1444013 : Blo 377762 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B428215 : Blo 377762 428215 := bstep (se 1 (by rfl) ⟨321161, by rfl⟩ : syracuseStep 428215 = 642323) B642323
theorem B723161 : Blo 377762 723161 := bstep (se 2 (by rfl) ⟨271185, by rfl⟩ : syracuseStep 723161 = 542371) B542371
theorem B1083613 : Blo 377762 1083613 := bstep (se 3 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 1083613 = 406355) B406355
theorem B854297 : Blo 377762 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B428395 : Blo 377762 428395 := bstep (se 1 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 428395 = 642593) B642593
theorem B854387 : Blo 377762 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B854423 : Blo 377762 854423 := bstep (se 1 (by rfl) ⟨640817, by rfl⟩ : syracuseStep 854423 = 1281635) B1281635
theorem B428503 : Blo 377762 428503 := bstep (se 1 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 428503 = 642755) B642755
theorem B1083955 : Blo 377762 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B2591297 : Blo 377762 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B854603 : Blo 377762 854603 := bstep (se 1 (by rfl) ⟨640952, by rfl⟩ : syracuseStep 854603 = 1281905) B1281905
theorem B854657 : Blo 377762 854657 := bstep (se 2 (by rfl) ⟨320496, by rfl⟩ : syracuseStep 854657 = 640993) B640993
theorem B428683 : Blo 377762 428683 := bstep (se 1 (by rfl) ⟨321512, by rfl⟩ : syracuseStep 428683 = 643025) B643025
theorem B1280663 : Blo 377762 1280663 := bstep (se 1 (by rfl) ⟨960497, by rfl⟩ : syracuseStep 1280663 = 1920995) B1920995
theorem B428791 : Blo 377762 428791 := bstep (se 1 (by rfl) ⟨321593, by rfl⟩ : syracuseStep 428791 = 643187) B643187
theorem B854873 : Blo 377762 854873 := bstep (se 2 (by rfl) ⟨320577, by rfl⟩ : syracuseStep 854873 = 641155) B641155
theorem B428971 : Blo 377762 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B854963 : Blo 377762 854963 := bstep (se 1 (by rfl) ⟨641222, by rfl⟩ : syracuseStep 854963 = 1282445) B1282445
theorem B1444787 : Blo 377762 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B854999 : Blo 377762 854999 := bstep (se 1 (by rfl) ⟨641249, by rfl⟩ : syracuseStep 854999 = 1282499) B1282499
theorem B429079 : Blo 377762 429079 := bstep (se 1 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 429079 = 643619) B643619
theorem B1739827 : Blo 377762 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B855179 : Blo 377762 855179 := bstep (se 1 (by rfl) ⟨641384, by rfl⟩ : syracuseStep 855179 = 1282769) B1282769
theorem B1281203 : Blo 377762 1281203 := bstep (se 1 (by rfl) ⟨960902, by rfl⟩ : syracuseStep 1281203 = 1921805) B1921805
theorem B7834805 : Blo 377762 7834805 := bstep (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) B734513
theorem B855233 : Blo 377762 855233 := bstep (se 2 (by rfl) ⟨320712, by rfl⟩ : syracuseStep 855233 = 641425) B641425
theorem B429259 : Blo 377762 429259 := bstep (se 1 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 429259 = 643889) B643889
theorem B429367 : Blo 377762 429367 := bstep (se 1 (by rfl) ⟨322025, by rfl⟩ : syracuseStep 429367 = 644051) B644051
theorem B855449 : Blo 377762 855449 := bstep (se 2 (by rfl) ⟨320793, by rfl⟩ : syracuseStep 855449 = 641587) B641587
theorem B1281473 : Blo 377762 1281473 := bstep (se 2 (by rfl) ⟨480552, by rfl⟩ : syracuseStep 1281473 = 961105) B961105
theorem B1084889 : Blo 377762 1084889 := bstep (se 2 (by rfl) ⟨406833, by rfl⟩ : syracuseStep 1084889 = 813667) B813667
theorem B1215965 : Blo 377762 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B855539 : Blo 377762 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B855575 : Blo 377762 855575 := bstep (se 1 (by rfl) ⟨641681, by rfl⟩ : syracuseStep 855575 = 1283363) B1283363
theorem B1216093 : Blo 377762 1216093 := bstep (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) B456035
theorem B11701853 : Blo 377762 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B724619 : Blo 377762 724619 := bstep (se 1 (by rfl) ⟨543464, by rfl⟩ : syracuseStep 724619 = 1086929) B1086929
theorem B855755 : Blo 377762 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B855809 : Blo 377762 855809 := bstep (se 2 (by rfl) ⟨320928, by rfl⟩ : syracuseStep 855809 = 641857) B641857
theorem B3247937 : Blo 377762 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B1216349 : Blo 377762 1216349 := bstep (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) B456131
theorem B856025 : Blo 377762 856025 := bstep (se 2 (by rfl) ⟨321009, by rfl⟩ : syracuseStep 856025 = 642019) B642019
theorem B1282013 : Blo 377762 1282013 := bstep (se 3 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 1282013 = 480755) B480755
theorem B856115 : Blo 377762 856115 := bstep (se 1 (by rfl) ⟨642086, by rfl⟩ : syracuseStep 856115 = 1284173) B1284173
theorem B856151 : Blo 377762 856151 := bstep (se 1 (by rfl) ⟨642113, by rfl⟩ : syracuseStep 856151 = 1284227) B1284227
theorem B2887811 : Blo 377762 2887811 := bstep (se 1 (by rfl) ⟨2165858, by rfl⟩ : syracuseStep 2887811 = 4331717) B4331717
theorem B856331 : Blo 377762 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B856385 : Blo 377762 856385 := bstep (se 2 (by rfl) ⟨321144, by rfl⟩ : syracuseStep 856385 = 642289) B642289
theorem B1446275 : Blo 377762 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B856601 : Blo 377762 856601 := bstep (se 2 (by rfl) ⟨321225, by rfl⟩ : syracuseStep 856601 = 642451) B642451
theorem B856691 : Blo 377762 856691 := bstep (se 1 (by rfl) ⟨642518, by rfl⟩ : syracuseStep 856691 = 1285037) B1285037
theorem B856727 : Blo 377762 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B856907 : Blo 377762 856907 := bstep (se 1 (by rfl) ⟨642680, by rfl⟩ : syracuseStep 856907 = 1285361) B1285361
theorem B1446731 : Blo 377762 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B1086301 : Blo 377762 1086301 := bstep (se 3 (by rfl) ⟨203681, by rfl⟩ : syracuseStep 1086301 = 407363) B407363
theorem B856961 : Blo 377762 856961 := bstep (se 2 (by rfl) ⟨321360, by rfl⟩ : syracuseStep 856961 = 642721) B642721
theorem B1446929 : Blo 377762 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B1086529 : Blo 377762 1086529 := bstep (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) B814897
theorem B1283147 : Blo 377762 1283147 := bstep (se 1 (by rfl) ⟨962360, by rfl⟩ : syracuseStep 1283147 = 1924721) B1924721
theorem B857177 : Blo 377762 857177 := bstep (se 2 (by rfl) ⟨321441, by rfl⟩ : syracuseStep 857177 = 642883) B642883
theorem B857267 : Blo 377762 857267 := bstep (se 1 (by rfl) ⟨642950, by rfl⟩ : syracuseStep 857267 = 1285901) B1285901
theorem B857303 : Blo 377762 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B1545475 : Blo 377762 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1283417 : Blo 377762 1283417 := bstep (se 2 (by rfl) ⟨481281, by rfl⟩ : syracuseStep 1283417 = 962563) B962563
theorem B857483 : Blo 377762 857483 := bstep (se 1 (by rfl) ⟨643112, by rfl⟩ : syracuseStep 857483 = 1286225) B1286225
theorem B1086871 : Blo 377762 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B857537 : Blo 377762 857537 := bstep (se 2 (by rfl) ⟨321576, by rfl⟩ : syracuseStep 857537 = 643153) B643153
theorem B464459 : Blo 377762 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B857753 : Blo 377762 857753 := bstep (se 2 (by rfl) ⟨321657, by rfl⟩ : syracuseStep 857753 = 643315) B643315
theorem B857843 : Blo 377762 857843 := bstep (se 1 (by rfl) ⟨643382, by rfl⟩ : syracuseStep 857843 = 1286765) B1286765
theorem B857879 : Blo 377762 857879 := bstep (se 1 (by rfl) ⟨643409, by rfl⟩ : syracuseStep 857879 = 1286819) B1286819
theorem B1447703 : Blo 377762 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B956225 : Blo 377762 956225 := bstep (se 2 (by rfl) ⟨358584, by rfl⟩ : syracuseStep 956225 = 717169) B717169
theorem B464791 : Blo 377762 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B858059 : Blo 377762 858059 := bstep (se 1 (by rfl) ⟨643544, by rfl⟩ : syracuseStep 858059 = 1287089) B1287089
theorem B1447901 : Blo 377762 1447901 := bstep (se 3 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 1447901 = 542963) B542963
theorem B858113 : Blo 377762 858113 := bstep (se 2 (by rfl) ⟨321792, by rfl⟩ : syracuseStep 858113 = 643585) B643585
theorem B1284119 : Blo 377762 1284119 := bstep (se 1 (by rfl) ⟨963089, by rfl⟩ : syracuseStep 1284119 = 1926179) B1926179
theorem B858329 : Blo 377762 858329 := bstep (se 2 (by rfl) ⟨321873, by rfl⟩ : syracuseStep 858329 = 643747) B643747
theorem B5478641 : Blo 377762 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B858419 : Blo 377762 858419 := bstep (se 1 (by rfl) ⟨643814, by rfl⟩ : syracuseStep 858419 = 1287629) B1287629
theorem B858455 : Blo 377762 858455 := bstep (se 1 (by rfl) ⟨643841, by rfl⟩ : syracuseStep 858455 = 1287683) B1287683
theorem B2726405 : Blo 377762 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B858635 : Blo 377762 858635 := bstep (se 1 (by rfl) ⟨643976, by rfl⟩ : syracuseStep 858635 = 1287953) B1287953
theorem B1546775 : Blo 377762 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1284659 : Blo 377762 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B858689 : Blo 377762 858689 := bstep (se 2 (by rfl) ⟨322008, by rfl⟩ : syracuseStep 858689 = 644017) B644017
theorem B5446349 : Blo 377762 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B858905 : Blo 377762 858905 := bstep (se 2 (by rfl) ⟨322089, by rfl⟩ : syracuseStep 858905 = 644179) B644179
theorem B1284929 : Blo 377762 1284929 := bstep (se 2 (by rfl) ⟨481848, by rfl⟩ : syracuseStep 1284929 = 963697) B963697
theorem B2169665 : Blo 377762 2169665 := bstep (se 2 (by rfl) ⟨813624, by rfl⟩ : syracuseStep 2169665 = 1627249) B1627249
theorem B957491 : Blo 377762 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B728203 : Blo 377762 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B695513 : Blo 377762 695513 := bstep (se 2 (by rfl) ⟨260817, by rfl⟩ : syracuseStep 695513 = 521635) B521635
theorem B1285469 : Blo 377762 1285469 := bstep (se 3 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 1285469 = 482051) B482051
theorem B2891213 : Blo 377762 2891213 := bstep (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) B1084205
theorem B958027 : Blo 377762 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B1023691 : Blo 377762 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B958169 : Blo 377762 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B5480257 : Blo 377762 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B2891699 : Blo 377762 2891699 := bstep (se 1 (by rfl) ⟨2168774, by rfl⟩ : syracuseStep 2891699 = 4337549) B4337549
theorem B925643 : Blo 377762 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B729089 : Blo 377762 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B1974451 : Blo 377762 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B1024435 : Blo 377762 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B1286603 : Blo 377762 1286603 := bstep (se 1 (by rfl) ⟨964952, by rfl⟩ : syracuseStep 1286603 = 1929905) B1929905
theorem B958999 : Blo 377762 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B1614401 : Blo 377762 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B2499173 : Blo 377762 2499173 := bstep (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) B468595
theorem B9872077 : Blo 377762 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B1286873 : Blo 377762 1286873 := bstep (se 2 (by rfl) ⟨482577, by rfl⟩ : syracuseStep 1286873 = 965155) B965155
theorem B6169445 : Blo 377762 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B959435 : Blo 377762 959435 := bstep (se 1 (by rfl) ⟨719576, by rfl⟩ : syracuseStep 959435 = 1439153) B1439153
theorem B1156189 : Blo 377762 1156189 := bstep (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) B433571
theorem B2172055 : Blo 377762 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B1221911 : Blo 377762 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B959809 : Blo 377762 959809 := bstep (se 2 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 959809 = 719857) B719857
theorem B2893157 : Blo 377762 2893157 := bstep (se 4 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 2893157 = 542467) B542467
theorem B1287575 : Blo 377762 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B566681 : Blo 377762 566681 := bstep (se 2 (by rfl) ⟨212505, by rfl⟩ : syracuseStep 566681 = 425011) B425011
theorem B1025473 : Blo 377762 1025473 := bstep (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) B769105
theorem B3253709 : Blo 377762 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B566795 : Blo 377762 566795 := bstep (se 1 (by rfl) ⟨425096, by rfl⟩ : syracuseStep 566795 = 850193) B850193
theorem B566807 : Blo 377762 566807 := bstep (se 1 (by rfl) ⟨425105, by rfl⟩ : syracuseStep 566807 = 850211) B850211
theorem B566873 : Blo 377762 566873 := bstep (se 2 (by rfl) ⟨212577, by rfl⟩ : syracuseStep 566873 = 425155) B425155
theorem B566987 : Blo 377762 566987 := bstep (se 1 (by rfl) ⟨425240, by rfl⟩ : syracuseStep 566987 = 850481) B850481
theorem B8726221 : Blo 377762 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B566999 : Blo 377762 566999 := bstep (se 1 (by rfl) ⟨425249, by rfl⟩ : syracuseStep 566999 = 850499) B850499
theorem B567065 : Blo 377762 567065 := bstep (se 2 (by rfl) ⟨212649, by rfl⟩ : syracuseStep 567065 = 425299) B425299
theorem B2893643 : Blo 377762 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B2598749 : Blo 377762 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B567179 : Blo 377762 567179 := bstep (se 1 (by rfl) ⟨425384, by rfl⟩ : syracuseStep 567179 = 850769) B850769
theorem B567191 : Blo 377762 567191 := bstep (se 1 (by rfl) ⟨425393, by rfl⟩ : syracuseStep 567191 = 850787) B850787
theorem B960407 : Blo 377762 960407 := bstep (se 1 (by rfl) ⟨720305, by rfl⟩ : syracuseStep 960407 = 1440611) B1440611
theorem B1288115 : Blo 377762 1288115 := bstep (se 1 (by rfl) ⟨966086, by rfl⟩ : syracuseStep 1288115 = 1932173) B1932173
theorem B567257 : Blo 377762 567257 := bstep (se 2 (by rfl) ⟨212721, by rfl⟩ : syracuseStep 567257 = 425443) B425443
theorem B567371 : Blo 377762 567371 := bstep (se 1 (by rfl) ⟨425528, by rfl⟩ : syracuseStep 567371 = 851057) B851057
theorem B567383 : Blo 377762 567383 := bstep (se 1 (by rfl) ⟨425537, by rfl⟩ : syracuseStep 567383 = 851075) B851075
theorem B1026199 : Blo 377762 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B567449 : Blo 377762 567449 := bstep (se 2 (by rfl) ⟨212793, by rfl⟩ : syracuseStep 567449 = 425587) B425587
theorem B1288385 : Blo 377762 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B567563 : Blo 377762 567563 := bstep (se 1 (by rfl) ⟨425672, by rfl⟩ : syracuseStep 567563 = 851345) B851345
theorem B567575 : Blo 377762 567575 := bstep (se 1 (by rfl) ⟨425681, by rfl⟩ : syracuseStep 567575 = 851363) B851363
theorem B567641 : Blo 377762 567641 := bstep (se 2 (by rfl) ⟨212865, by rfl⟩ : syracuseStep 567641 = 425731) B425731
theorem B567755 : Blo 377762 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B567767 : Blo 377762 567767 := bstep (se 1 (by rfl) ⟨425825, by rfl⟩ : syracuseStep 567767 = 851651) B851651
theorem B567833 : Blo 377762 567833 := bstep (se 2 (by rfl) ⟨212937, by rfl⟩ : syracuseStep 567833 = 425875) B425875
theorem B404023 : Blo 377762 404023 := bstep (se 1 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 404023 = 606035) B606035
theorem B2108005 : Blo 377762 2108005 := bstep (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) B395251
theorem B567947 : Blo 377762 567947 := bstep (se 1 (by rfl) ⟨425960, by rfl⟩ : syracuseStep 567947 = 851921) B851921
theorem B567959 : Blo 377762 567959 := bstep (se 1 (by rfl) ⟨425969, by rfl⟩ : syracuseStep 567959 = 851939) B851939
theorem B961217 : Blo 377762 961217 := bstep (se 2 (by rfl) ⟨360456, by rfl⟩ : syracuseStep 961217 = 720913) B720913
theorem B568025 : Blo 377762 568025 := bstep (se 2 (by rfl) ⟨213009, by rfl⟩ : syracuseStep 568025 = 426019) B426019
theorem B731927 : Blo 377762 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B568139 : Blo 377762 568139 := bstep (se 1 (by rfl) ⟨426104, by rfl⟩ : syracuseStep 568139 = 852209) B852209
theorem B568151 : Blo 377762 568151 := bstep (se 1 (by rfl) ⟨426113, by rfl⟩ : syracuseStep 568151 = 852227) B852227
theorem B1846147 : Blo 377762 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B568217 : Blo 377762 568217 := bstep (se 2 (by rfl) ⟨213081, by rfl⟩ : syracuseStep 568217 = 426163) B426163
theorem B1616861 : Blo 377762 1616861 := bstep (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) B606323
theorem B568331 : Blo 377762 568331 := bstep (se 1 (by rfl) ⟨426248, by rfl⟩ : syracuseStep 568331 = 852497) B852497
theorem B568343 : Blo 377762 568343 := bstep (se 1 (by rfl) ⟨426257, by rfl⟩ : syracuseStep 568343 = 852515) B852515
theorem B568409 : Blo 377762 568409 := bstep (se 2 (by rfl) ⟨213153, by rfl⟩ : syracuseStep 568409 = 426307) B426307
theorem B568523 : Blo 377762 568523 := bstep (se 1 (by rfl) ⟨426392, by rfl⟩ : syracuseStep 568523 = 852785) B852785
theorem B568535 : Blo 377762 568535 := bstep (se 1 (by rfl) ⟨426401, by rfl⟩ : syracuseStep 568535 = 852803) B852803
theorem B961753 : Blo 377762 961753 := bstep (se 2 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 961753 = 721315) B721315
theorem B568601 : Blo 377762 568601 := bstep (se 2 (by rfl) ⟨213225, by rfl⟩ : syracuseStep 568601 = 426451) B426451
theorem B1158475 : Blo 377762 1158475 := bstep (se 1 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 1158475 = 1737713) B1737713
theorem B404843 : Blo 377762 404843 := bstep (se 1 (by rfl) ⟨303632, by rfl⟩ : syracuseStep 404843 = 607265) B607265
theorem B568715 : Blo 377762 568715 := bstep (se 1 (by rfl) ⟨426536, by rfl⟩ : syracuseStep 568715 = 853073) B853073
theorem B568727 : Blo 377762 568727 := bstep (se 1 (by rfl) ⟨426545, by rfl⟩ : syracuseStep 568727 = 853091) B853091
theorem B6499763 : Blo 377762 6499763 := bstep (se 1 (by rfl) ⟨4874822, by rfl⟩ : syracuseStep 6499763 = 9749645) B9749645
theorem B437687 : Blo 377762 437687 := bstep (se 1 (by rfl) ⟨328265, by rfl⟩ : syracuseStep 437687 = 656531) B656531
theorem B2731481 : Blo 377762 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B568793 : Blo 377762 568793 := bstep (se 2 (by rfl) ⟨213297, by rfl⟩ : syracuseStep 568793 = 426595) B426595
theorem B568907 : Blo 377762 568907 := bstep (se 1 (by rfl) ⟨426680, by rfl⟩ : syracuseStep 568907 = 853361) B853361
theorem B568919 : Blo 377762 568919 := bstep (se 1 (by rfl) ⟨426689, by rfl⟩ : syracuseStep 568919 = 853379) B853379
theorem B568985 : Blo 377762 568985 := bstep (se 2 (by rfl) ⟨213369, by rfl⟩ : syracuseStep 568985 = 426739) B426739
theorem B569099 : Blo 377762 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B569111 : Blo 377762 569111 := bstep (se 1 (by rfl) ⟨426833, by rfl⟩ : syracuseStep 569111 = 853667) B853667
theorem B569177 : Blo 377762 569177 := bstep (se 2 (by rfl) ⟨213441, by rfl⟩ : syracuseStep 569177 = 426883) B426883
theorem B1650563 : Blo 377762 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B569291 : Blo 377762 569291 := bstep (se 1 (by rfl) ⟨426968, by rfl⟩ : syracuseStep 569291 = 853937) B853937
theorem B569303 : Blo 377762 569303 := bstep (se 1 (by rfl) ⟨426977, by rfl⟩ : syracuseStep 569303 = 853955) B853955
theorem B569369 : Blo 377762 569369 := bstep (se 2 (by rfl) ⟨213513, by rfl⟩ : syracuseStep 569369 = 427027) B427027
theorem B569483 : Blo 377762 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B569495 : Blo 377762 569495 := bstep (se 1 (by rfl) ⟨427121, by rfl⟩ : syracuseStep 569495 = 854243) B854243
theorem B569561 : Blo 377762 569561 := bstep (se 2 (by rfl) ⟨213585, by rfl⟩ : syracuseStep 569561 = 427171) B427171
theorem B962867 : Blo 377762 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B569675 : Blo 377762 569675 := bstep (se 1 (by rfl) ⟨427256, by rfl⟩ : syracuseStep 569675 = 854513) B854513
theorem B569687 : Blo 377762 569687 := bstep (se 1 (by rfl) ⟨427265, by rfl⟩ : syracuseStep 569687 = 854531) B854531
theorem B1913219 : Blo 377762 1913219 := bstep (se 1 (by rfl) ⟨1434914, by rfl⟩ : syracuseStep 1913219 = 2869829) B2869829
theorem B405911 : Blo 377762 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B569753 : Blo 377762 569753 := bstep (se 2 (by rfl) ⟨213657, by rfl⟩ : syracuseStep 569753 = 427315) B427315
theorem B3912113 : Blo 377762 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B569867 : Blo 377762 569867 := bstep (se 1 (by rfl) ⟨427400, by rfl⟩ : syracuseStep 569867 = 854801) B854801
theorem B569879 : Blo 377762 569879 := bstep (se 1 (by rfl) ⟨427409, by rfl⟩ : syracuseStep 569879 = 854819) B854819
theorem B569945 : Blo 377762 569945 := bstep (se 2 (by rfl) ⟨213729, by rfl⟩ : syracuseStep 569945 = 427459) B427459
theorem B963161 : Blo 377762 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B766657 : Blo 377762 766657 := bstep (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) B574993
theorem B570059 : Blo 377762 570059 := bstep (se 1 (by rfl) ⟨427544, by rfl⟩ : syracuseStep 570059 = 855089) B855089
theorem B570071 : Blo 377762 570071 := bstep (se 1 (by rfl) ⟨427553, by rfl⟩ : syracuseStep 570071 = 855107) B855107
theorem B1454851 : Blo 377762 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B570137 : Blo 377762 570137 := bstep (se 2 (by rfl) ⟨213801, by rfl⟩ : syracuseStep 570137 = 427603) B427603
theorem B1651549 : Blo 377762 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B570251 : Blo 377762 570251 := bstep (se 1 (by rfl) ⟨427688, by rfl⟩ : syracuseStep 570251 = 855377) B855377
theorem B570263 : Blo 377762 570263 := bstep (se 1 (by rfl) ⟨427697, by rfl⟩ : syracuseStep 570263 = 855395) B855395
theorem B2110387 : Blo 377762 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B570329 : Blo 377762 570329 := bstep (se 2 (by rfl) ⟨213873, by rfl⟩ : syracuseStep 570329 = 427747) B427747
theorem B4174865 : Blo 377762 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B570443 : Blo 377762 570443 := bstep (se 1 (by rfl) ⟨427832, by rfl⟩ : syracuseStep 570443 = 855665) B855665
theorem B570455 : Blo 377762 570455 := bstep (se 1 (by rfl) ⟨427841, by rfl⟩ : syracuseStep 570455 = 855683) B855683
theorem B570521 : Blo 377762 570521 := bstep (se 2 (by rfl) ⟨213945, by rfl⟩ : syracuseStep 570521 = 427891) B427891
theorem B570635 : Blo 377762 570635 := bstep (se 1 (by rfl) ⟨427976, by rfl⟩ : syracuseStep 570635 = 855953) B855953
theorem B570647 : Blo 377762 570647 := bstep (se 1 (by rfl) ⟨427985, by rfl⟩ : syracuseStep 570647 = 855971) B855971
theorem B570713 : Blo 377762 570713 := bstep (se 2 (by rfl) ⟨214017, by rfl⟩ : syracuseStep 570713 = 428035) B428035
theorem B570827 : Blo 377762 570827 := bstep (se 1 (by rfl) ⟨428120, by rfl⟩ : syracuseStep 570827 = 856241) B856241
theorem B406987 : Blo 377762 406987 := bstep (se 1 (by rfl) ⟨305240, by rfl⟩ : syracuseStep 406987 = 610481) B610481
theorem B570839 : Blo 377762 570839 := bstep (se 1 (by rfl) ⟨428129, by rfl⟩ : syracuseStep 570839 = 856259) B856259
theorem B1619459 : Blo 377762 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B570905 : Blo 377762 570905 := bstep (se 2 (by rfl) ⟨214089, by rfl⟩ : syracuseStep 570905 = 428179) B428179
theorem B571019 : Blo 377762 571019 := bstep (se 1 (by rfl) ⟨428264, by rfl⟩ : syracuseStep 571019 = 856529) B856529
theorem B571031 : Blo 377762 571031 := bstep (se 1 (by rfl) ⟨428273, by rfl⟩ : syracuseStep 571031 = 856547) B856547
theorem B440023 : Blo 377762 440023 := bstep (se 1 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 440023 = 660035) B660035
theorem B571097 : Blo 377762 571097 := bstep (se 2 (by rfl) ⟨214161, by rfl⟩ : syracuseStep 571097 = 428323) B428323
theorem B571211 : Blo 377762 571211 := bstep (se 1 (by rfl) ⟨428408, by rfl⟩ : syracuseStep 571211 = 856817) B856817
theorem B571223 : Blo 377762 571223 := bstep (se 1 (by rfl) ⟨428417, by rfl⟩ : syracuseStep 571223 = 856835) B856835
theorem B571289 : Blo 377762 571289 := bstep (se 2 (by rfl) ⟨214233, by rfl⟩ : syracuseStep 571289 = 428467) B428467
theorem B571403 : Blo 377762 571403 := bstep (se 1 (by rfl) ⟨428552, by rfl⟩ : syracuseStep 571403 = 857105) B857105
theorem B571415 : Blo 377762 571415 := bstep (se 1 (by rfl) ⟨428561, by rfl⟩ : syracuseStep 571415 = 857123) B857123
theorem B571481 : Blo 377762 571481 := bstep (se 2 (by rfl) ⟨214305, by rfl⟩ : syracuseStep 571481 = 428611) B428611
theorem B2308189 : Blo 377762 2308189 := bstep (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) B865571
theorem B571595 : Blo 377762 571595 := bstep (se 1 (by rfl) ⟨428696, by rfl⟩ : syracuseStep 571595 = 857393) B857393
theorem B964811 : Blo 377762 964811 := bstep (se 1 (by rfl) ⟨723608, by rfl⟩ : syracuseStep 964811 = 1447217) B1447217
theorem B571607 : Blo 377762 571607 := bstep (se 1 (by rfl) ⟨428705, by rfl⟩ : syracuseStep 571607 = 857411) B857411
theorem B571673 : Blo 377762 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B571787 : Blo 377762 571787 := bstep (se 1 (by rfl) ⟨428840, by rfl⟩ : syracuseStep 571787 = 857681) B857681
theorem B571799 : Blo 377762 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B1292761 : Blo 377762 1292761 := bstep (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) B969571
theorem B571865 : Blo 377762 571865 := bstep (se 2 (by rfl) ⟨214449, by rfl⟩ : syracuseStep 571865 = 428899) B428899
theorem B7485965 : Blo 377762 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B571979 : Blo 377762 571979 := bstep (se 1 (by rfl) ⟨428984, by rfl⟩ : syracuseStep 571979 = 857969) B857969
theorem B571991 : Blo 377762 571991 := bstep (se 1 (by rfl) ⟨428993, by rfl⟩ : syracuseStep 571991 = 857987) B857987
theorem B637591 : Blo 377762 637591 := bstep (se 1 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 637591 = 956387) B956387
theorem B572057 : Blo 377762 572057 := bstep (se 2 (by rfl) ⟨214521, by rfl⟩ : syracuseStep 572057 = 429043) B429043
theorem B572171 : Blo 377762 572171 := bstep (se 1 (by rfl) ⟨429128, by rfl⟩ : syracuseStep 572171 = 858257) B858257
theorem B572183 : Blo 377762 572183 := bstep (se 1 (by rfl) ⟨429137, by rfl⟩ : syracuseStep 572183 = 858275) B858275
theorem B572249 : Blo 377762 572249 := bstep (se 2 (by rfl) ⟨214593, by rfl⟩ : syracuseStep 572249 = 429187) B429187
theorem B572363 : Blo 377762 572363 := bstep (se 1 (by rfl) ⟨429272, by rfl⟩ : syracuseStep 572363 = 858545) B858545
theorem B572375 : Blo 377762 572375 := bstep (se 1 (by rfl) ⟨429281, by rfl⟩ : syracuseStep 572375 = 858563) B858563
theorem B572441 : Blo 377762 572441 := bstep (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) B429331
theorem B2898989 : Blo 377762 2898989 := bstep (se 3 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 2898989 = 1087121) B1087121
theorem B1457203 : Blo 377762 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B572555 : Blo 377762 572555 := bstep (se 1 (by rfl) ⟨429416, by rfl⟩ : syracuseStep 572555 = 858833) B858833
theorem B965783 : Blo 377762 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B572567 : Blo 377762 572567 := bstep (se 1 (by rfl) ⟨429425, by rfl⟩ : syracuseStep 572567 = 858851) B858851
theorem B572633 : Blo 377762 572633 := bstep (se 2 (by rfl) ⟨214737, by rfl⟩ : syracuseStep 572633 = 429475) B429475
theorem B638219 : Blo 377762 638219 := bstep (se 1 (by rfl) ⟨478664, by rfl⟩ : syracuseStep 638219 = 957329) B957329
theorem B4865345 : Blo 377762 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B3259723 : Blo 377762 3259723 := bstep (se 1 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 3259723 = 4889585) B4889585
theorem B638347 : Blo 377762 638347 := bstep (se 1 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 638347 = 957521) B957521
theorem B605657 : Blo 377762 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B540121 : Blo 377762 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B638489 : Blo 377762 638489 := bstep (se 2 (by rfl) ⟨239433, by rfl⟩ : syracuseStep 638489 = 478867) B478867
theorem B3259997 : Blo 377762 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B638617 : Blo 377762 638617 := bstep (se 2 (by rfl) ⟨239481, by rfl⟩ : syracuseStep 638617 = 478963) B478963
theorem B1916945 : Blo 377762 1916945 := bstep (se 2 (by rfl) ⟨718854, by rfl⟩ : syracuseStep 1916945 = 1437709) B1437709
theorem B1917107 : Blo 377762 1917107 := bstep (se 1 (by rfl) ⟨1437830, by rfl⟩ : syracuseStep 1917107 = 2875661) B2875661
theorem B639191 : Blo 377762 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B2933009 : Blo 377762 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B639319 : Blo 377762 639319 := bstep (se 1 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 639319 = 958979) B958979
theorem B1229363 : Blo 377762 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B770647 : Blo 377762 770647 := bstep (se 1 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 770647 = 1155971) B1155971
theorem B3261059 : Blo 377762 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B770905 : Blo 377762 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B541579 : Blo 377762 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B377771 : Blo 377762 377771 := bstep (se 1 (by rfl) ⟨283328, by rfl⟩ : syracuseStep 377771 = 566657) B566657
theorem B2311091 : Blo 377762 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B377783 : Blo 377762 377783 := bstep (se 1 (by rfl) ⟨283337, by rfl⟩ : syracuseStep 377783 = 566675) B566675
theorem B377803 : Blo 377762 377803 := bstep (se 1 (by rfl) ⟨283352, by rfl⟩ : syracuseStep 377803 = 566705) B566705
theorem B639947 : Blo 377762 639947 := bstep (se 1 (by rfl) ⟨479960, by rfl⟩ : syracuseStep 639947 = 959921) B959921
theorem B377815 : Blo 377762 377815 := bstep (se 1 (by rfl) ⟨283361, by rfl⟩ : syracuseStep 377815 = 566723) B566723
theorem B377835 : Blo 377762 377835 := bstep (se 1 (by rfl) ⟨283376, by rfl⟩ : syracuseStep 377835 = 566753) B566753
theorem B377847 : Blo 377762 377847 := bstep (se 1 (by rfl) ⟨283385, by rfl⟩ : syracuseStep 377847 = 566771) B566771
theorem B377867 : Blo 377762 377867 := bstep (se 1 (by rfl) ⟨283400, by rfl⟩ : syracuseStep 377867 = 566801) B566801
theorem B377879 : Blo 377762 377879 := bstep (se 1 (by rfl) ⟨283409, by rfl⟩ : syracuseStep 377879 = 566819) B566819
theorem B377899 : Blo 377762 377899 := bstep (se 1 (by rfl) ⟨283424, by rfl⟩ : syracuseStep 377899 = 566849) B566849
theorem B377911 : Blo 377762 377911 := bstep (se 1 (by rfl) ⟨283433, by rfl⟩ : syracuseStep 377911 = 566867) B566867
theorem B377931 : Blo 377762 377931 := bstep (se 1 (by rfl) ⟨283448, by rfl⟩ : syracuseStep 377931 = 566897) B566897
theorem B640075 : Blo 377762 640075 := bstep (se 1 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 640075 = 960113) B960113
theorem B377943 : Blo 377762 377943 := bstep (se 1 (by rfl) ⟨283457, by rfl⟩ : syracuseStep 377943 = 566915) B566915
theorem B377963 : Blo 377762 377963 := bstep (se 1 (by rfl) ⟨283472, by rfl⟩ : syracuseStep 377963 = 566945) B566945
theorem B377975 : Blo 377762 377975 := bstep (se 1 (by rfl) ⟨283481, by rfl⟩ : syracuseStep 377975 = 566963) B566963
theorem B377995 : Blo 377762 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B378007 : Blo 377762 378007 := bstep (se 1 (by rfl) ⟨283505, by rfl⟩ : syracuseStep 378007 = 567011) B567011
theorem B378027 : Blo 377762 378027 := bstep (se 1 (by rfl) ⟨283520, by rfl⟩ : syracuseStep 378027 = 567041) B567041
theorem B378039 : Blo 377762 378039 := bstep (se 1 (by rfl) ⟨283529, by rfl⟩ : syracuseStep 378039 = 567059) B567059
theorem B1623233 : Blo 377762 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B378059 : Blo 377762 378059 := bstep (se 1 (by rfl) ⟨283544, by rfl⟩ : syracuseStep 378059 = 567089) B567089
theorem B378071 : Blo 377762 378071 := bstep (se 1 (by rfl) ⟨283553, by rfl⟩ : syracuseStep 378071 = 567107) B567107
theorem B640217 : Blo 377762 640217 := bstep (se 2 (by rfl) ⟨240081, by rfl⟩ : syracuseStep 640217 = 480163) B480163
theorem B378091 : Blo 377762 378091 := bstep (se 1 (by rfl) ⟨283568, by rfl⟩ : syracuseStep 378091 = 567137) B567137
theorem B378103 : Blo 377762 378103 := bstep (se 1 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 378103 = 567155) B567155
theorem B378123 : Blo 377762 378123 := bstep (se 1 (by rfl) ⟨283592, by rfl⟩ : syracuseStep 378123 = 567185) B567185
theorem B378135 : Blo 377762 378135 := bstep (se 1 (by rfl) ⟨283601, by rfl⟩ : syracuseStep 378135 = 567203) B567203
theorem B378155 : Blo 377762 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B378167 : Blo 377762 378167 := bstep (se 1 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 378167 = 567251) B567251
theorem B378187 : Blo 377762 378187 := bstep (se 1 (by rfl) ⟨283640, by rfl⟩ : syracuseStep 378187 = 567281) B567281
theorem B378199 : Blo 377762 378199 := bstep (se 1 (by rfl) ⟨283649, by rfl⟩ : syracuseStep 378199 = 567299) B567299
theorem B640345 : Blo 377762 640345 := bstep (se 2 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 640345 = 480259) B480259
theorem B378219 : Blo 377762 378219 := bstep (se 1 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 378219 = 567329) B567329
theorem B378231 : Blo 377762 378231 := bstep (se 1 (by rfl) ⟨283673, by rfl⟩ : syracuseStep 378231 = 567347) B567347
theorem B378251 : Blo 377762 378251 := bstep (se 1 (by rfl) ⟨283688, by rfl⟩ : syracuseStep 378251 = 567377) B567377
theorem B378263 : Blo 377762 378263 := bstep (se 1 (by rfl) ⟨283697, by rfl⟩ : syracuseStep 378263 = 567395) B567395
theorem B378283 : Blo 377762 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B3229105 : Blo 377762 3229105 := bstep (se 2 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 3229105 = 2421829) B2421829
theorem B378295 : Blo 377762 378295 := bstep (se 1 (by rfl) ⟨283721, by rfl⟩ : syracuseStep 378295 = 567443) B567443
theorem B378315 : Blo 377762 378315 := bstep (se 1 (by rfl) ⟨283736, by rfl⟩ : syracuseStep 378315 = 567473) B567473
theorem B378327 : Blo 377762 378327 := bstep (se 1 (by rfl) ⟨283745, by rfl⟩ : syracuseStep 378327 = 567491) B567491
theorem B378347 : Blo 377762 378347 := bstep (se 1 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 378347 = 567521) B567521
theorem B378359 : Blo 377762 378359 := bstep (se 1 (by rfl) ⟨283769, by rfl⟩ : syracuseStep 378359 = 567539) B567539
theorem B378379 : Blo 377762 378379 := bstep (se 1 (by rfl) ⟨283784, by rfl⟩ : syracuseStep 378379 = 567569) B567569
theorem B378391 : Blo 377762 378391 := bstep (se 1 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 378391 = 567587) B567587
theorem B378411 : Blo 377762 378411 := bstep (se 1 (by rfl) ⟨283808, by rfl⟩ : syracuseStep 378411 = 567617) B567617
theorem B2442797 : Blo 377762 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B378423 : Blo 377762 378423 := bstep (se 1 (by rfl) ⟨283817, by rfl⟩ : syracuseStep 378423 = 567635) B567635
theorem B378443 : Blo 377762 378443 := bstep (se 1 (by rfl) ⟨283832, by rfl⟩ : syracuseStep 378443 = 567665) B567665
theorem B378455 : Blo 377762 378455 := bstep (se 1 (by rfl) ⟨283841, by rfl⟩ : syracuseStep 378455 = 567683) B567683
theorem B378475 : Blo 377762 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B378487 : Blo 377762 378487 := bstep (se 1 (by rfl) ⟨283865, by rfl⟩ : syracuseStep 378487 = 567731) B567731
theorem B378507 : Blo 377762 378507 := bstep (se 1 (by rfl) ⟨283880, by rfl⟩ : syracuseStep 378507 = 567761) B567761
theorem B378519 : Blo 377762 378519 := bstep (se 1 (by rfl) ⟨283889, by rfl⟩ : syracuseStep 378519 = 567779) B567779
theorem B378539 : Blo 377762 378539 := bstep (se 1 (by rfl) ⟨283904, by rfl⟩ : syracuseStep 378539 = 567809) B567809
theorem B378551 : Blo 377762 378551 := bstep (se 1 (by rfl) ⟨283913, by rfl⟩ : syracuseStep 378551 = 567827) B567827
theorem B378571 : Blo 377762 378571 := bstep (se 1 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 378571 = 567857) B567857
theorem B378583 : Blo 377762 378583 := bstep (se 1 (by rfl) ⟨283937, by rfl⟩ : syracuseStep 378583 = 567875) B567875
theorem B378603 : Blo 377762 378603 := bstep (se 1 (by rfl) ⟨283952, by rfl⟩ : syracuseStep 378603 = 567905) B567905
theorem B378615 : Blo 377762 378615 := bstep (se 1 (by rfl) ⟨283961, by rfl⟩ : syracuseStep 378615 = 567923) B567923
theorem B378635 : Blo 377762 378635 := bstep (se 1 (by rfl) ⟨283976, by rfl⟩ : syracuseStep 378635 = 567953) B567953
theorem B2737937 : Blo 377762 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B378647 : Blo 377762 378647 := bstep (se 1 (by rfl) ⟨283985, by rfl⟩ : syracuseStep 378647 = 567971) B567971
theorem B378667 : Blo 377762 378667 := bstep (se 1 (by rfl) ⟨284000, by rfl⟩ : syracuseStep 378667 = 568001) B568001
theorem B378679 : Blo 377762 378679 := bstep (se 1 (by rfl) ⟨284009, by rfl⟩ : syracuseStep 378679 = 568019) B568019
theorem B378699 : Blo 377762 378699 := bstep (se 1 (by rfl) ⟨284024, by rfl⟩ : syracuseStep 378699 = 568049) B568049
theorem B378711 : Blo 377762 378711 := bstep (se 1 (by rfl) ⟨284033, by rfl⟩ : syracuseStep 378711 = 568067) B568067
theorem B378731 : Blo 377762 378731 := bstep (se 1 (by rfl) ⟨284048, by rfl⟩ : syracuseStep 378731 = 568097) B568097
theorem B378743 : Blo 377762 378743 := bstep (se 1 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 378743 = 568115) B568115
theorem B378763 : Blo 377762 378763 := bstep (se 1 (by rfl) ⟨284072, by rfl⟩ : syracuseStep 378763 = 568145) B568145
theorem B378775 : Blo 377762 378775 := bstep (se 1 (by rfl) ⟨284081, by rfl⟩ : syracuseStep 378775 = 568163) B568163
theorem B640919 : Blo 377762 640919 := bstep (se 1 (by rfl) ⟨480689, by rfl⟩ : syracuseStep 640919 = 961379) B961379
theorem B378795 : Blo 377762 378795 := bstep (se 1 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 378795 = 568193) B568193
theorem B378807 : Blo 377762 378807 := bstep (se 1 (by rfl) ⟨284105, by rfl⟩ : syracuseStep 378807 = 568211) B568211
theorem B378827 : Blo 377762 378827 := bstep (se 1 (by rfl) ⟨284120, by rfl⟩ : syracuseStep 378827 = 568241) B568241
theorem B378839 : Blo 377762 378839 := bstep (se 1 (by rfl) ⟨284129, by rfl⟩ : syracuseStep 378839 = 568259) B568259
theorem B378859 : Blo 377762 378859 := bstep (se 1 (by rfl) ⟨284144, by rfl⟩ : syracuseStep 378859 = 568289) B568289
theorem B378871 : Blo 377762 378871 := bstep (se 1 (by rfl) ⟨284153, by rfl⟩ : syracuseStep 378871 = 568307) B568307
theorem B378891 : Blo 377762 378891 := bstep (se 1 (by rfl) ⟨284168, by rfl⟩ : syracuseStep 378891 = 568337) B568337
theorem B378903 : Blo 377762 378903 := bstep (se 1 (by rfl) ⟨284177, by rfl⟩ : syracuseStep 378903 = 568355) B568355
theorem B641047 : Blo 377762 641047 := bstep (se 1 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 641047 = 961571) B961571
theorem B378923 : Blo 377762 378923 := bstep (se 1 (by rfl) ⟨284192, by rfl⟩ : syracuseStep 378923 = 568385) B568385
theorem B378935 : Blo 377762 378935 := bstep (se 1 (by rfl) ⟨284201, by rfl⟩ : syracuseStep 378935 = 568403) B568403
theorem B378955 : Blo 377762 378955 := bstep (se 1 (by rfl) ⟨284216, by rfl⟩ : syracuseStep 378955 = 568433) B568433
theorem B1919051 : Blo 377762 1919051 := bstep (se 1 (by rfl) ⟨1439288, by rfl⟩ : syracuseStep 1919051 = 2878577) B2878577
theorem B378967 : Blo 377762 378967 := bstep (se 1 (by rfl) ⟨284225, by rfl⟩ : syracuseStep 378967 = 568451) B568451
theorem B542809 : Blo 377762 542809 := bstep (se 2 (by rfl) ⟨203553, by rfl⟩ : syracuseStep 542809 = 407107) B407107
theorem B1624157 : Blo 377762 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B378987 : Blo 377762 378987 := bstep (se 1 (by rfl) ⟨284240, by rfl⟩ : syracuseStep 378987 = 568481) B568481
theorem B378999 : Blo 377762 378999 := bstep (se 1 (by rfl) ⟨284249, by rfl⟩ : syracuseStep 378999 = 568499) B568499
theorem B379019 : Blo 377762 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B16468109 : Blo 377762 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B379031 : Blo 377762 379031 := bstep (se 1 (by rfl) ⟨284273, by rfl⟩ : syracuseStep 379031 = 568547) B568547
theorem B379051 : Blo 377762 379051 := bstep (se 1 (by rfl) ⟨284288, by rfl⟩ : syracuseStep 379051 = 568577) B568577
theorem B379063 : Blo 377762 379063 := bstep (se 1 (by rfl) ⟨284297, by rfl⟩ : syracuseStep 379063 = 568595) B568595
theorem B379083 : Blo 377762 379083 := bstep (se 1 (by rfl) ⟨284312, by rfl⟩ : syracuseStep 379083 = 568625) B568625
theorem B379095 : Blo 377762 379095 := bstep (se 1 (by rfl) ⟨284321, by rfl⟩ : syracuseStep 379095 = 568643) B568643
theorem B379115 : Blo 377762 379115 := bstep (se 1 (by rfl) ⟨284336, by rfl⟩ : syracuseStep 379115 = 568673) B568673
theorem B379127 : Blo 377762 379127 := bstep (se 1 (by rfl) ⟨284345, by rfl⟩ : syracuseStep 379127 = 568691) B568691
theorem B379147 : Blo 377762 379147 := bstep (se 1 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 379147 = 568721) B568721
theorem B379159 : Blo 377762 379159 := bstep (se 1 (by rfl) ⟨284369, by rfl⟩ : syracuseStep 379159 = 568739) B568739
theorem B379179 : Blo 377762 379179 := bstep (se 1 (by rfl) ⟨284384, by rfl⟩ : syracuseStep 379179 = 568769) B568769
theorem B379191 : Blo 377762 379191 := bstep (se 1 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 379191 = 568787) B568787
theorem B379211 : Blo 377762 379211 := bstep (se 1 (by rfl) ⟨284408, by rfl⟩ : syracuseStep 379211 = 568817) B568817
theorem B379223 : Blo 377762 379223 := bstep (se 1 (by rfl) ⟨284417, by rfl⟩ : syracuseStep 379223 = 568835) B568835
theorem B379243 : Blo 377762 379243 := bstep (se 1 (by rfl) ⟨284432, by rfl⟩ : syracuseStep 379243 = 568865) B568865
theorem B379255 : Blo 377762 379255 := bstep (se 1 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 379255 = 568883) B568883
theorem B379275 : Blo 377762 379275 := bstep (se 1 (by rfl) ⟨284456, by rfl⟩ : syracuseStep 379275 = 568913) B568913
theorem B379287 : Blo 377762 379287 := bstep (se 1 (by rfl) ⟨284465, by rfl⟩ : syracuseStep 379287 = 568931) B568931
theorem B379307 : Blo 377762 379307 := bstep (se 1 (by rfl) ⟨284480, by rfl⟩ : syracuseStep 379307 = 568961) B568961
theorem B379319 : Blo 377762 379319 := bstep (se 1 (by rfl) ⟨284489, by rfl⟩ : syracuseStep 379319 = 568979) B568979
theorem B379339 : Blo 377762 379339 := bstep (se 1 (by rfl) ⟨284504, by rfl⟩ : syracuseStep 379339 = 569009) B569009
theorem B379351 : Blo 377762 379351 := bstep (se 1 (by rfl) ⟨284513, by rfl⟩ : syracuseStep 379351 = 569027) B569027
theorem B379371 : Blo 377762 379371 := bstep (se 1 (by rfl) ⟨284528, by rfl⟩ : syracuseStep 379371 = 569057) B569057
theorem B379383 : Blo 377762 379383 := bstep (se 1 (by rfl) ⟨284537, by rfl⟩ : syracuseStep 379383 = 569075) B569075
theorem B379403 : Blo 377762 379403 := bstep (se 1 (by rfl) ⟨284552, by rfl⟩ : syracuseStep 379403 = 569105) B569105
theorem B379415 : Blo 377762 379415 := bstep (se 1 (by rfl) ⟨284561, by rfl⟩ : syracuseStep 379415 = 569123) B569123
theorem B379435 : Blo 377762 379435 := bstep (se 1 (by rfl) ⟨284576, by rfl⟩ : syracuseStep 379435 = 569153) B569153
theorem B379447 : Blo 377762 379447 := bstep (se 1 (by rfl) ⟨284585, by rfl⟩ : syracuseStep 379447 = 569171) B569171
theorem B379467 : Blo 377762 379467 := bstep (se 1 (by rfl) ⟨284600, by rfl⟩ : syracuseStep 379467 = 569201) B569201
theorem B379479 : Blo 377762 379479 := bstep (se 1 (by rfl) ⟨284609, by rfl⟩ : syracuseStep 379479 = 569219) B569219
theorem B1296989 : Blo 377762 1296989 := bstep (se 3 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 1296989 = 486371) B486371
theorem B379499 : Blo 377762 379499 := bstep (se 1 (by rfl) ⟨284624, by rfl⟩ : syracuseStep 379499 = 569249) B569249
theorem B379511 : Blo 377762 379511 := bstep (se 1 (by rfl) ⟨284633, by rfl⟩ : syracuseStep 379511 = 569267) B569267
theorem B379531 : Blo 377762 379531 := bstep (se 1 (by rfl) ⟨284648, by rfl⟩ : syracuseStep 379531 = 569297) B569297
theorem B641675 : Blo 377762 641675 := bstep (se 1 (by rfl) ⟨481256, by rfl⟩ : syracuseStep 641675 = 962513) B962513
theorem B379543 : Blo 377762 379543 := bstep (se 1 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 379543 = 569315) B569315
theorem B379563 : Blo 377762 379563 := bstep (se 1 (by rfl) ⟨284672, by rfl⟩ : syracuseStep 379563 = 569345) B569345
theorem B379575 : Blo 377762 379575 := bstep (se 1 (by rfl) ⟨284681, by rfl⟩ : syracuseStep 379575 = 569363) B569363
theorem B379595 : Blo 377762 379595 := bstep (se 1 (by rfl) ⟨284696, by rfl⟩ : syracuseStep 379595 = 569393) B569393
theorem B379607 : Blo 377762 379607 := bstep (se 1 (by rfl) ⟨284705, by rfl⟩ : syracuseStep 379607 = 569411) B569411
theorem B379627 : Blo 377762 379627 := bstep (se 1 (by rfl) ⟨284720, by rfl⟩ : syracuseStep 379627 = 569441) B569441
theorem B379639 : Blo 377762 379639 := bstep (se 1 (by rfl) ⟨284729, by rfl⟩ : syracuseStep 379639 = 569459) B569459
theorem B379659 : Blo 377762 379659 := bstep (se 1 (by rfl) ⟨284744, by rfl⟩ : syracuseStep 379659 = 569489) B569489
theorem B641803 : Blo 377762 641803 := bstep (se 1 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 641803 = 962705) B962705
theorem B379671 : Blo 377762 379671 := bstep (se 1 (by rfl) ⟨284753, by rfl⟩ : syracuseStep 379671 = 569507) B569507
theorem B379691 : Blo 377762 379691 := bstep (se 1 (by rfl) ⟨284768, by rfl⟩ : syracuseStep 379691 = 569537) B569537
theorem B379703 : Blo 377762 379703 := bstep (se 1 (by rfl) ⟨284777, by rfl⟩ : syracuseStep 379703 = 569555) B569555
theorem B379723 : Blo 377762 379723 := bstep (se 1 (by rfl) ⟨284792, by rfl⟩ : syracuseStep 379723 = 569585) B569585
theorem B379735 : Blo 377762 379735 := bstep (se 1 (by rfl) ⟨284801, by rfl⟩ : syracuseStep 379735 = 569603) B569603
theorem B379755 : Blo 377762 379755 := bstep (se 1 (by rfl) ⟨284816, by rfl⟩ : syracuseStep 379755 = 569633) B569633
theorem B379767 : Blo 377762 379767 := bstep (se 1 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 379767 = 569651) B569651
theorem B379787 : Blo 377762 379787 := bstep (se 1 (by rfl) ⟨284840, by rfl⟩ : syracuseStep 379787 = 569681) B569681
theorem B379799 : Blo 377762 379799 := bstep (se 1 (by rfl) ⟨284849, by rfl⟩ : syracuseStep 379799 = 569699) B569699
theorem B641945 : Blo 377762 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B379819 : Blo 377762 379819 := bstep (se 1 (by rfl) ⟨284864, by rfl⟩ : syracuseStep 379819 = 569729) B569729
theorem B379831 : Blo 377762 379831 := bstep (se 1 (by rfl) ⟨284873, by rfl⟩ : syracuseStep 379831 = 569747) B569747
theorem B379851 : Blo 377762 379851 := bstep (se 1 (by rfl) ⟨284888, by rfl⟩ : syracuseStep 379851 = 569777) B569777
theorem B379863 : Blo 377762 379863 := bstep (se 1 (by rfl) ⟨284897, by rfl⟩ : syracuseStep 379863 = 569795) B569795
theorem B379883 : Blo 377762 379883 := bstep (se 1 (by rfl) ⟨284912, by rfl⟩ : syracuseStep 379883 = 569825) B569825
theorem B379895 : Blo 377762 379895 := bstep (se 1 (by rfl) ⟨284921, by rfl⟩ : syracuseStep 379895 = 569843) B569843
theorem B478219 : Blo 377762 478219 := bstep (se 1 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 478219 = 717329) B717329
theorem B379915 : Blo 377762 379915 := bstep (se 1 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 379915 = 569873) B569873
theorem B379927 : Blo 377762 379927 := bstep (se 1 (by rfl) ⟨284945, by rfl⟩ : syracuseStep 379927 = 569891) B569891
theorem B642073 : Blo 377762 642073 := bstep (se 2 (by rfl) ⟨240777, by rfl⟩ : syracuseStep 642073 = 481555) B481555
theorem B379947 : Blo 377762 379947 := bstep (se 1 (by rfl) ⟨284960, by rfl⟩ : syracuseStep 379947 = 569921) B569921
theorem B379959 : Blo 377762 379959 := bstep (se 1 (by rfl) ⟨284969, by rfl⟩ : syracuseStep 379959 = 569939) B569939
theorem B379979 : Blo 377762 379979 := bstep (se 1 (by rfl) ⟨284984, by rfl⟩ : syracuseStep 379979 = 569969) B569969
theorem B379991 : Blo 377762 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B380011 : Blo 377762 380011 := bstep (se 1 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 380011 = 570017) B570017
theorem B380023 : Blo 377762 380023 := bstep (se 1 (by rfl) ⟨285017, by rfl⟩ : syracuseStep 380023 = 570035) B570035
theorem B380043 : Blo 377762 380043 := bstep (se 1 (by rfl) ⟨285032, by rfl⟩ : syracuseStep 380043 = 570065) B570065
theorem B380055 : Blo 377762 380055 := bstep (se 1 (by rfl) ⟨285041, by rfl⟩ : syracuseStep 380055 = 570083) B570083
theorem B380075 : Blo 377762 380075 := bstep (se 1 (by rfl) ⟨285056, by rfl⟩ : syracuseStep 380075 = 570113) B570113
theorem B380087 : Blo 377762 380087 := bstep (se 1 (by rfl) ⟨285065, by rfl⟩ : syracuseStep 380087 = 570131) B570131
theorem B380107 : Blo 377762 380107 := bstep (se 1 (by rfl) ⟨285080, by rfl⟩ : syracuseStep 380107 = 570161) B570161
theorem B380119 : Blo 377762 380119 := bstep (se 1 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 380119 = 570179) B570179
theorem B380139 : Blo 377762 380139 := bstep (se 1 (by rfl) ⟨285104, by rfl⟩ : syracuseStep 380139 = 570209) B570209
theorem B380151 : Blo 377762 380151 := bstep (se 1 (by rfl) ⟨285113, by rfl⟩ : syracuseStep 380151 = 570227) B570227
theorem B380171 : Blo 377762 380171 := bstep (se 1 (by rfl) ⟨285128, by rfl⟩ : syracuseStep 380171 = 570257) B570257
theorem B478487 : Blo 377762 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B380183 : Blo 377762 380183 := bstep (se 1 (by rfl) ⟨285137, by rfl⟩ : syracuseStep 380183 = 570275) B570275
theorem B380203 : Blo 377762 380203 := bstep (se 1 (by rfl) ⟨285152, by rfl⟩ : syracuseStep 380203 = 570305) B570305
theorem B380215 : Blo 377762 380215 := bstep (se 1 (by rfl) ⟨285161, by rfl⟩ : syracuseStep 380215 = 570323) B570323
theorem B380235 : Blo 377762 380235 := bstep (se 1 (by rfl) ⟨285176, by rfl⟩ : syracuseStep 380235 = 570353) B570353
theorem B380247 : Blo 377762 380247 := bstep (se 1 (by rfl) ⟨285185, by rfl⟩ : syracuseStep 380247 = 570371) B570371
theorem B609623 : Blo 377762 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B380267 : Blo 377762 380267 := bstep (se 1 (by rfl) ⟨285200, by rfl⟩ : syracuseStep 380267 = 570401) B570401
theorem B380279 : Blo 377762 380279 := bstep (se 1 (by rfl) ⟨285209, by rfl⟩ : syracuseStep 380279 = 570419) B570419
theorem B380299 : Blo 377762 380299 := bstep (se 1 (by rfl) ⟨285224, by rfl⟩ : syracuseStep 380299 = 570449) B570449
theorem B380311 : Blo 377762 380311 := bstep (se 1 (by rfl) ⟨285233, by rfl⟩ : syracuseStep 380311 = 570467) B570467
theorem B380331 : Blo 377762 380331 := bstep (se 1 (by rfl) ⟨285248, by rfl⟩ : syracuseStep 380331 = 570497) B570497
theorem B380343 : Blo 377762 380343 := bstep (se 1 (by rfl) ⟨285257, by rfl⟩ : syracuseStep 380343 = 570515) B570515
theorem B380363 : Blo 377762 380363 := bstep (se 1 (by rfl) ⟨285272, by rfl⟩ : syracuseStep 380363 = 570545) B570545
theorem B380375 : Blo 377762 380375 := bstep (se 1 (by rfl) ⟨285281, by rfl⟩ : syracuseStep 380375 = 570563) B570563
theorem B380395 : Blo 377762 380395 := bstep (se 1 (by rfl) ⟨285296, by rfl⟩ : syracuseStep 380395 = 570593) B570593
theorem B380407 : Blo 377762 380407 := bstep (se 1 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 380407 = 570611) B570611
theorem B380427 : Blo 377762 380427 := bstep (se 1 (by rfl) ⟨285320, by rfl⟩ : syracuseStep 380427 = 570641) B570641
theorem B2870801 : Blo 377762 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B380439 : Blo 377762 380439 := bstep (se 1 (by rfl) ⟨285329, by rfl⟩ : syracuseStep 380439 = 570659) B570659
theorem B609815 : Blo 377762 609815 := bstep (se 1 (by rfl) ⟨457361, by rfl⟩ : syracuseStep 609815 = 914723) B914723
theorem B380459 : Blo 377762 380459 := bstep (se 1 (by rfl) ⟨285344, by rfl⟩ : syracuseStep 380459 = 570689) B570689
theorem B380471 : Blo 377762 380471 := bstep (se 1 (by rfl) ⟨285353, by rfl⟩ : syracuseStep 380471 = 570707) B570707
theorem B380491 : Blo 377762 380491 := bstep (se 1 (by rfl) ⟨285368, by rfl⟩ : syracuseStep 380491 = 570737) B570737
theorem B380503 : Blo 377762 380503 := bstep (se 1 (by rfl) ⟨285377, by rfl⟩ : syracuseStep 380503 = 570755) B570755
theorem B642647 : Blo 377762 642647 := bstep (se 1 (by rfl) ⟨481985, by rfl⟩ : syracuseStep 642647 = 963971) B963971
theorem B1363549 : Blo 377762 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B380523 : Blo 377762 380523 := bstep (se 1 (by rfl) ⟨285392, by rfl⟩ : syracuseStep 380523 = 570785) B570785
theorem B380535 : Blo 377762 380535 := bstep (se 1 (by rfl) ⟨285401, by rfl⟩ : syracuseStep 380535 = 570803) B570803
theorem B380555 : Blo 377762 380555 := bstep (se 1 (by rfl) ⟨285416, by rfl⟩ : syracuseStep 380555 = 570833) B570833
theorem B1363607 : Blo 377762 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B380567 : Blo 377762 380567 := bstep (se 1 (by rfl) ⟨285425, by rfl⟩ : syracuseStep 380567 = 570851) B570851
theorem B609943 : Blo 377762 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B380587 : Blo 377762 380587 := bstep (se 1 (by rfl) ⟨285440, by rfl⟩ : syracuseStep 380587 = 570881) B570881
theorem B380599 : Blo 377762 380599 := bstep (se 1 (by rfl) ⟨285449, by rfl⟩ : syracuseStep 380599 = 570899) B570899
theorem B380619 : Blo 377762 380619 := bstep (se 1 (by rfl) ⟨285464, by rfl⟩ : syracuseStep 380619 = 570929) B570929
theorem B380631 : Blo 377762 380631 := bstep (se 1 (by rfl) ⟨285473, by rfl⟩ : syracuseStep 380631 = 570947) B570947
theorem B642775 : Blo 377762 642775 := bstep (se 1 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 642775 = 964163) B964163
theorem B380651 : Blo 377762 380651 := bstep (se 1 (by rfl) ⟨285488, by rfl⟩ : syracuseStep 380651 = 570977) B570977
theorem B380663 : Blo 377762 380663 := bstep (se 1 (by rfl) ⟨285497, by rfl⟩ : syracuseStep 380663 = 570995) B570995
theorem B380683 : Blo 377762 380683 := bstep (se 1 (by rfl) ⟨285512, by rfl⟩ : syracuseStep 380683 = 571025) B571025
theorem B380695 : Blo 377762 380695 := bstep (se 1 (by rfl) ⟨285521, by rfl⟩ : syracuseStep 380695 = 571043) B571043
theorem B380715 : Blo 377762 380715 := bstep (se 1 (by rfl) ⟨285536, by rfl⟩ : syracuseStep 380715 = 571073) B571073
theorem B380727 : Blo 377762 380727 := bstep (se 1 (by rfl) ⟨285545, by rfl⟩ : syracuseStep 380727 = 571091) B571091
theorem B1920833 : Blo 377762 1920833 := bstep (se 2 (by rfl) ⟨720312, by rfl⟩ : syracuseStep 1920833 = 1440625) B1440625
theorem B3067723 : Blo 377762 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B380747 : Blo 377762 380747 := bstep (se 1 (by rfl) ⟨285560, by rfl⟩ : syracuseStep 380747 = 571121) B571121
theorem B380759 : Blo 377762 380759 := bstep (se 1 (by rfl) ⟨285569, by rfl⟩ : syracuseStep 380759 = 571139) B571139
theorem B380779 : Blo 377762 380779 := bstep (se 1 (by rfl) ⟨285584, by rfl⟩ : syracuseStep 380779 = 571169) B571169
theorem B380791 : Blo 377762 380791 := bstep (se 1 (by rfl) ⟨285593, by rfl⟩ : syracuseStep 380791 = 571187) B571187
theorem B380811 : Blo 377762 380811 := bstep (se 1 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 380811 = 571217) B571217
theorem B380823 : Blo 377762 380823 := bstep (se 1 (by rfl) ⟨285617, by rfl⟩ : syracuseStep 380823 = 571235) B571235
theorem B380843 : Blo 377762 380843 := bstep (se 1 (by rfl) ⟨285632, by rfl⟩ : syracuseStep 380843 = 571265) B571265
theorem B380855 : Blo 377762 380855 := bstep (se 1 (by rfl) ⟨285641, by rfl⟩ : syracuseStep 380855 = 571283) B571283
theorem B380875 : Blo 377762 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B479191 : Blo 377762 479191 := bstep (se 1 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 479191 = 718787) B718787
theorem B380887 : Blo 377762 380887 := bstep (se 1 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 380887 = 571331) B571331
theorem B380907 : Blo 377762 380907 := bstep (se 1 (by rfl) ⟨285680, by rfl⟩ : syracuseStep 380907 = 571361) B571361
theorem B380919 : Blo 377762 380919 := bstep (se 1 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 380919 = 571379) B571379
theorem B380939 : Blo 377762 380939 := bstep (se 1 (by rfl) ⟨285704, by rfl⟩ : syracuseStep 380939 = 571409) B571409
theorem B806935 : Blo 377762 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B380951 : Blo 377762 380951 := bstep (se 1 (by rfl) ⟨285713, by rfl⟩ : syracuseStep 380951 = 571427) B571427
theorem B380971 : Blo 377762 380971 := bstep (se 1 (by rfl) ⟨285728, by rfl⟩ : syracuseStep 380971 = 571457) B571457
theorem B380983 : Blo 377762 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B381003 : Blo 377762 381003 := bstep (se 1 (by rfl) ⟨285752, by rfl⟩ : syracuseStep 381003 = 571505) B571505
theorem B381015 : Blo 377762 381015 := bstep (se 1 (by rfl) ⟨285761, by rfl⟩ : syracuseStep 381015 = 571523) B571523
theorem B381035 : Blo 377762 381035 := bstep (se 1 (by rfl) ⟨285776, by rfl⟩ : syracuseStep 381035 = 571553) B571553
theorem B381047 : Blo 377762 381047 := bstep (se 1 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 381047 = 571571) B571571
theorem B381067 : Blo 377762 381067 := bstep (se 1 (by rfl) ⟨285800, by rfl⟩ : syracuseStep 381067 = 571601) B571601
theorem B381079 : Blo 377762 381079 := bstep (se 1 (by rfl) ⟨285809, by rfl⟩ : syracuseStep 381079 = 571619) B571619
theorem B381099 : Blo 377762 381099 := bstep (se 1 (by rfl) ⟨285824, by rfl⟩ : syracuseStep 381099 = 571649) B571649
theorem B381111 : Blo 377762 381111 := bstep (se 1 (by rfl) ⟨285833, by rfl⟩ : syracuseStep 381111 = 571667) B571667
theorem B381131 : Blo 377762 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B610507 : Blo 377762 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B381143 : Blo 377762 381143 := bstep (se 1 (by rfl) ⟨285857, by rfl⟩ : syracuseStep 381143 = 571715) B571715
theorem B381163 : Blo 377762 381163 := bstep (se 1 (by rfl) ⟨285872, by rfl⟩ : syracuseStep 381163 = 571745) B571745
theorem B381175 : Blo 377762 381175 := bstep (se 1 (by rfl) ⟨285881, by rfl⟩ : syracuseStep 381175 = 571763) B571763
theorem B381195 : Blo 377762 381195 := bstep (se 1 (by rfl) ⟨285896, by rfl⟩ : syracuseStep 381195 = 571793) B571793
theorem B610583 : Blo 377762 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B381207 : Blo 377762 381207 := bstep (se 1 (by rfl) ⟨285905, by rfl⟩ : syracuseStep 381207 = 571811) B571811
theorem B381227 : Blo 377762 381227 := bstep (se 1 (by rfl) ⟨285920, by rfl⟩ : syracuseStep 381227 = 571841) B571841
theorem B381239 : Blo 377762 381239 := bstep (se 1 (by rfl) ⟨285929, by rfl⟩ : syracuseStep 381239 = 571859) B571859
theorem B381259 : Blo 377762 381259 := bstep (se 1 (by rfl) ⟨285944, by rfl⟩ : syracuseStep 381259 = 571889) B571889
theorem B643403 : Blo 377762 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B381271 : Blo 377762 381271 := bstep (se 1 (by rfl) ⟨285953, by rfl⟩ : syracuseStep 381271 = 571907) B571907
theorem B381291 : Blo 377762 381291 := bstep (se 1 (by rfl) ⟨285968, by rfl⟩ : syracuseStep 381291 = 571937) B571937
theorem B381303 : Blo 377762 381303 := bstep (se 1 (by rfl) ⟨285977, by rfl⟩ : syracuseStep 381303 = 571955) B571955
theorem B381323 : Blo 377762 381323 := bstep (se 1 (by rfl) ⟨285992, by rfl⟩ : syracuseStep 381323 = 571985) B571985
theorem B381335 : Blo 377762 381335 := bstep (se 1 (by rfl) ⟨286001, by rfl⟩ : syracuseStep 381335 = 572003) B572003
theorem B381355 : Blo 377762 381355 := bstep (se 1 (by rfl) ⟨286016, by rfl⟩ : syracuseStep 381355 = 572033) B572033
theorem B381367 : Blo 377762 381367 := bstep (se 1 (by rfl) ⟨286025, by rfl⟩ : syracuseStep 381367 = 572051) B572051
theorem B643531 : Blo 377762 643531 := bstep (se 1 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 643531 = 965297) B965297
theorem B381387 : Blo 377762 381387 := bstep (se 1 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 381387 = 572081) B572081
theorem B381399 : Blo 377762 381399 := bstep (se 1 (by rfl) ⟨286049, by rfl⟩ : syracuseStep 381399 = 572099) B572099
theorem B381419 : Blo 377762 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B381431 : Blo 377762 381431 := bstep (se 1 (by rfl) ⟨286073, by rfl⟩ : syracuseStep 381431 = 572147) B572147
theorem B381451 : Blo 377762 381451 := bstep (se 1 (by rfl) ⟨286088, by rfl⟩ : syracuseStep 381451 = 572177) B572177
theorem B381463 : Blo 377762 381463 := bstep (se 1 (by rfl) ⟨286097, by rfl⟩ : syracuseStep 381463 = 572195) B572195
theorem B381483 : Blo 377762 381483 := bstep (se 1 (by rfl) ⟨286112, by rfl⟩ : syracuseStep 381483 = 572225) B572225
theorem B381495 : Blo 377762 381495 := bstep (se 1 (by rfl) ⟨286121, by rfl⟩ : syracuseStep 381495 = 572243) B572243
theorem B807499 : Blo 377762 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B381515 : Blo 377762 381515 := bstep (se 1 (by rfl) ⟨286136, by rfl⟩ : syracuseStep 381515 = 572273) B572273
theorem B381527 : Blo 377762 381527 := bstep (se 1 (by rfl) ⟨286145, by rfl⟩ : syracuseStep 381527 = 572291) B572291
theorem B643673 : Blo 377762 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B2183773 : Blo 377762 2183773 := bstep (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) B818915
theorem B381547 : Blo 377762 381547 := bstep (se 1 (by rfl) ⟨286160, by rfl⟩ : syracuseStep 381547 = 572321) B572321
theorem B381559 : Blo 377762 381559 := bstep (se 1 (by rfl) ⟨286169, by rfl⟩ : syracuseStep 381559 = 572339) B572339
theorem B381579 : Blo 377762 381579 := bstep (se 1 (by rfl) ⟨286184, by rfl⟩ : syracuseStep 381579 = 572369) B572369
theorem B381591 : Blo 377762 381591 := bstep (se 1 (by rfl) ⟨286193, by rfl⟩ : syracuseStep 381591 = 572387) B572387
theorem B381611 : Blo 377762 381611 := bstep (se 1 (by rfl) ⟨286208, by rfl⟩ : syracuseStep 381611 = 572417) B572417
theorem B381623 : Blo 377762 381623 := bstep (se 1 (by rfl) ⟨286217, by rfl⟩ : syracuseStep 381623 = 572435) B572435
theorem B381643 : Blo 377762 381643 := bstep (se 1 (by rfl) ⟨286232, by rfl⟩ : syracuseStep 381643 = 572465) B572465
theorem B381655 : Blo 377762 381655 := bstep (se 1 (by rfl) ⟨286241, by rfl⟩ : syracuseStep 381655 = 572483) B572483
theorem B643801 : Blo 377762 643801 := bstep (se 2 (by rfl) ⟨241425, by rfl⟩ : syracuseStep 643801 = 482851) B482851
theorem B381675 : Blo 377762 381675 := bstep (se 1 (by rfl) ⟨286256, by rfl⟩ : syracuseStep 381675 = 572513) B572513
theorem B381687 : Blo 377762 381687 := bstep (se 1 (by rfl) ⟨286265, by rfl⟩ : syracuseStep 381687 = 572531) B572531
theorem B381707 : Blo 377762 381707 := bstep (se 1 (by rfl) ⟨286280, by rfl⟩ : syracuseStep 381707 = 572561) B572561
theorem B381719 : Blo 377762 381719 := bstep (se 1 (by rfl) ⟨286289, by rfl⟩ : syracuseStep 381719 = 572579) B572579
theorem B381739 : Blo 377762 381739 := bstep (se 1 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 381739 = 572609) B572609
theorem B381751 : Blo 377762 381751 := bstep (se 1 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 381751 = 572627) B572627
theorem B545753 : Blo 377762 545753 := bstep (se 2 (by rfl) ⟨204657, by rfl⟩ : syracuseStep 545753 = 409315) B409315
theorem B4379741 : Blo 377762 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1627523 : Blo 377762 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B480907 : Blo 377762 480907 := bstep (se 1 (by rfl) ⟨360680, by rfl⟩ : syracuseStep 480907 = 721361) B721361
theorem B4085453 : Blo 377762 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B1922777 : Blo 377762 1922777 := bstep (se 2 (by rfl) ⟨721041, by rfl⟩ : syracuseStep 1922777 = 1442083) B1442083
theorem B808883 : Blo 377762 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B10901465 : Blo 377762 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 377762 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B808985 : Blo 377762 808985 := bstep (se 2 (by rfl) ⟨303369, by rfl⟩ : syracuseStep 808985 = 606739) B606739
theorem B6477893 : Blo 377762 6477893 := bstep (se 4 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 6477893 = 1214605) B1214605
theorem B546955 : Blo 377762 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B809345 : Blo 377762 809345 := bstep (se 2 (by rfl) ⟨303504, by rfl⟩ : syracuseStep 809345 = 607009) B607009
theorem B907841 : Blo 377762 907841 := bstep (se 2 (by rfl) ⟨340440, by rfl⟩ : syracuseStep 907841 = 680881) B680881
theorem B481879 : Blo 377762 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B2775653 : Blo 377762 2775653 := bstep (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) B520435
theorem B842483 : Blo 377762 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B1366807 : Blo 377762 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B2743217 : Blo 377762 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B3431347 : Blo 377762 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B1825753 : Blo 377762 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B810071 : Blo 377762 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B1924397 : Blo 377762 1924397 := bstep (se 3 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 1924397 = 721649) B721649
theorem B2874689 : Blo 377762 2874689 := bstep (se 2 (by rfl) ⟨1078008, by rfl⟩ : syracuseStep 2874689 = 2156017) B2156017
theorem B5954917 : Blo 377762 5954917 := bstep (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) B1116547
theorem B482699 : Blo 377762 482699 := bstep (se 1 (by rfl) ⟨362024, by rfl⟩ : syracuseStep 482699 = 724049) B724049
theorem B548299 : Blo 377762 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B2154059 : Blo 377762 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B810967 : Blo 377762 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B2187281 : Blo 377762 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B1827137 : Blo 377762 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B6545933 : Blo 377762 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B909899 : Blo 377762 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B1401517 : Blo 377762 1401517 := bstep (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) B525569
theorem B1762013 : Blo 377762 1762013 := bstep (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) B660755
theorem B811787 : Blo 377762 811787 := bstep (se 1 (by rfl) ⟨608840, by rfl⟩ : syracuseStep 811787 = 1217681) B1217681
theorem B1532695 : Blo 377762 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B3662657 : Blo 377762 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B2319283 : Blo 377762 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B8479667 : Blo 377762 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B2876633 : Blo 377762 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B3073241 : Blo 377762 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B976151 : Blo 377762 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1435097 : Blo 377762 1435097 := bstep (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) B1076323
theorem B812531 : Blo 377762 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1730123 : Blo 377762 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B976601 : Blo 377762 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B386839 : Blo 377762 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B682265 : Blo 377762 682265 := bstep (se 2 (by rfl) ⟨255849, by rfl⟩ : syracuseStep 682265 = 511699) B511699
theorem B813377 : Blo 377762 813377 := bstep (se 2 (by rfl) ⟨305016, by rfl⟩ : syracuseStep 813377 = 610033) B610033
theorem B1829213 : Blo 377762 1829213 := bstep (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) B685955
theorem B2058817 : Blo 377762 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1370699 : Blo 377762 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B813719 : Blo 377762 813719 := bstep (se 1 (by rfl) ⟨610289, by rfl⟩ : syracuseStep 813719 = 1220579) B1220579
theorem B1436723 : Blo 377762 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1436737 : Blo 377762 1436737 := bstep (se 2 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 1436737 = 1077553) B1077553
theorem B1928285 : Blo 377762 1928285 := bstep (se 3 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 1928285 = 723107) B723107
theorem B486679 : Blo 377762 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B454027 : Blo 377762 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B1371737 : Blo 377762 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B683635 : Blo 377762 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B1732241 : Blo 377762 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B1076915 : Blo 377762 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B1076939 : Blo 377762 1076939 := bstep (se 1 (by rfl) ⟨807704, by rfl⟩ : syracuseStep 1076939 = 1615409) B1615409
theorem B6188845 : Blo 377762 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B4878467 : Blo 377762 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B8876213 : Blo 377762 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B1994969 : Blo 377762 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1077725 : Blo 377762 1077725 := bstep (se 3 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 1077725 = 404147) B404147
theorem B619019 : Blo 377762 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B2880035 : Blo 377762 2880035 := bstep (se 1 (by rfl) ⟨2160026, by rfl⟩ : syracuseStep 2880035 = 4320053) B4320053
theorem B13529693 : Blo 377762 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B717427 : Blo 377762 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B717655 : Blo 377762 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B717761 : Blo 377762 717761 := bstep (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) B538321
theorem B1438667 : Blo 377762 1438667 := bstep (se 1 (by rfl) ⟨1079000, by rfl⟩ : syracuseStep 1438667 = 2158001) B2158001
theorem B1438681 : Blo 377762 1438681 := bstep (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) B1079011
theorem B10515491 : Blo 377762 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B717913 : Blo 377762 717913 := bstep (se 2 (by rfl) ⟨269217, by rfl⟩ : syracuseStep 717913 = 538435) B538435
theorem B1930391 : Blo 377762 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B1275101 : Blo 377762 1275101 := bstep (se 3 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 1275101 = 478163) B478163
theorem B1734061 : Blo 377762 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B1373699 : Blo 377762 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B685811 : Blo 377762 685811 := bstep (se 1 (by rfl) ⟨514358, by rfl⟩ : syracuseStep 685811 = 1028717) B1028717
theorem B1439639 : Blo 377762 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B12318641 : Blo 377762 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2062259 : Blo 377762 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B555031 : Blo 377762 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B849995 : Blo 377762 849995 := bstep (se 1 (by rfl) ⟨637496, by rfl⟩ : syracuseStep 849995 = 1274993) B1274993
theorem B850049 : Blo 377762 850049 := bstep (se 2 (by rfl) ⟨318768, by rfl⟩ : syracuseStep 850049 = 637537) B637537
theorem B1079513 : Blo 377762 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B1276235 : Blo 377762 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B850265 : Blo 377762 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B719219 : Blo 377762 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B850355 : Blo 377762 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B850391 : Blo 377762 850391 := bstep (se 1 (by rfl) ⟨637793, by rfl⟩ : syracuseStep 850391 = 1275587) B1275587
theorem B3242501 : Blo 377762 3242501 := bstep (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) B607969
theorem B719371 : Blo 377762 719371 := bstep (se 1 (by rfl) ⟨539528, by rfl⟩ : syracuseStep 719371 = 1079057) B1079057
theorem B1079831 : Blo 377762 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B1276505 : Blo 377762 1276505 := bstep (se 2 (by rfl) ⟨478689, by rfl⟩ : syracuseStep 1276505 = 957379) B957379
theorem B850571 : Blo 377762 850571 := bstep (se 1 (by rfl) ⟨637928, by rfl⟩ : syracuseStep 850571 = 1275857) B1275857
theorem B850625 : Blo 377762 850625 := bstep (se 2 (by rfl) ⟨318984, by rfl⟩ : syracuseStep 850625 = 637969) B637969
theorem B719705 : Blo 377762 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1538909 : Blo 377762 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B1375069 : Blo 377762 1375069 := bstep (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) B515651
theorem B850841 : Blo 377762 850841 := bstep (se 2 (by rfl) ⟨319065, by rfl⟩ : syracuseStep 850841 = 638131) B638131
theorem B850931 : Blo 377762 850931 := bstep (se 1 (by rfl) ⟨638198, by rfl⟩ : syracuseStep 850931 = 1276397) B1276397
theorem B850967 : Blo 377762 850967 := bstep (se 1 (by rfl) ⟨638225, by rfl⟩ : syracuseStep 850967 = 1276451) B1276451
theorem B4324427 : Blo 377762 4324427 := bstep (se 1 (by rfl) ⟨3243320, by rfl⟩ : syracuseStep 4324427 = 6486641) B6486641
theorem B425047 : Blo 377762 425047 := bstep (se 1 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 425047 = 637571) B637571
theorem B1440899 : Blo 377762 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B3243185 : Blo 377762 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B851147 : Blo 377762 851147 := bstep (se 1 (by rfl) ⟨638360, by rfl⟩ : syracuseStep 851147 = 1276721) B1276721
theorem B851201 : Blo 377762 851201 := bstep (se 2 (by rfl) ⟨319200, by rfl⟩ : syracuseStep 851201 = 638401) B638401
theorem B425227 : Blo 377762 425227 := bstep (se 1 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 425227 = 637841) B637841
theorem B1277207 : Blo 377762 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B1080641 : Blo 377762 1080641 := bstep (se 2 (by rfl) ⟨405240, by rfl⟩ : syracuseStep 1080641 = 810481) B810481
theorem B425335 : Blo 377762 425335 := bstep (se 1 (by rfl) ⟨319001, by rfl⟩ : syracuseStep 425335 = 638003) B638003
theorem B1244609 : Blo 377762 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B720343 : Blo 377762 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B851417 : Blo 377762 851417 := bstep (se 2 (by rfl) ⟨319281, by rfl⟩ : syracuseStep 851417 = 638563) B638563
theorem B1539607 : Blo 377762 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B425515 : Blo 377762 425515 := bstep (se 1 (by rfl) ⟨319136, by rfl⟩ : syracuseStep 425515 = 638273) B638273
theorem B851507 : Blo 377762 851507 := bstep (se 1 (by rfl) ⟨638630, by rfl⟩ : syracuseStep 851507 = 1277261) B1277261
theorem B851543 : Blo 377762 851543 := bstep (se 1 (by rfl) ⟨638657, by rfl⟩ : syracuseStep 851543 = 1277315) B1277315
theorem B1211993 : Blo 377762 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B425623 : Blo 377762 425623 := bstep (se 1 (by rfl) ⟨319217, by rfl⟩ : syracuseStep 425623 = 638435) B638435
theorem B851723 : Blo 377762 851723 := bstep (se 1 (by rfl) ⟨638792, by rfl⟩ : syracuseStep 851723 = 1277585) B1277585
theorem B1277747 : Blo 377762 1277747 := bstep (se 1 (by rfl) ⟨958310, by rfl⟩ : syracuseStep 1277747 = 1916621) B1916621
theorem B851777 : Blo 377762 851777 := bstep (se 2 (by rfl) ⟨319416, by rfl⟩ : syracuseStep 851777 = 638833) B638833
theorem B425803 : Blo 377762 425803 := bstep (se 1 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 425803 = 638705) B638705
theorem B425911 : Blo 377762 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B1277963 : Blo 377762 1277963 := bstep (se 1 (by rfl) ⟨958472, by rfl⟩ : syracuseStep 1277963 = 1916945) B1916945
theorem B852011 : Blo 377762 852011 := bstep (se 1 (by rfl) ⟨639008, by rfl⟩ : syracuseStep 852011 = 1278017) B1278017
theorem B5832749 : Blo 377762 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B1278071 : Blo 377762 1278071 := bstep (se 1 (by rfl) ⟨958553, by rfl⟩ : syracuseStep 1278071 = 1917107) B1917107
theorem B2162807 : Blo 377762 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B426127 : Blo 377762 426127 := bstep (se 1 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 426127 = 639191) B639191
theorem B819575 : Blo 377762 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B852371 : Blo 377762 852371 := bstep (se 1 (by rfl) ⟨639278, by rfl⟩ : syracuseStep 852371 = 1278557) B1278557
theorem B852425 : Blo 377762 852425 := bstep (se 2 (by rfl) ⟨319659, by rfl⟩ : syracuseStep 852425 = 639319) B639319
theorem B4850219 : Blo 377762 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B1540727 : Blo 377762 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B426631 : Blo 377762 426631 := bstep (se 1 (by rfl) ⟨319973, by rfl⟩ : syracuseStep 426631 = 639947) B639947
theorem B721543 : Blo 377762 721543 := bstep (se 1 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 721543 = 1082315) B1082315
theorem B1278665 : Blo 377762 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B2917093 : Blo 377762 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B1082155 : Blo 377762 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B426811 : Blo 377762 426811 := bstep (se 1 (by rfl) ⟨320108, by rfl⟩ : syracuseStep 426811 = 640217) B640217
theorem B1868689 : Blo 377762 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1082429 : Blo 377762 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B853127 : Blo 377762 853127 := bstep (se 1 (by rfl) ⟨639845, by rfl⟩ : syracuseStep 853127 = 1279691) B1279691
theorem B722105 : Blo 377762 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B427279 : Blo 377762 427279 := bstep (se 1 (by rfl) ⟨320459, by rfl⟩ : syracuseStep 427279 = 640919) B640919
theorem B853307 : Blo 377762 853307 := bstep (se 1 (by rfl) ⟨639980, by rfl⟩ : syracuseStep 853307 = 1279961) B1279961
theorem B1279367 : Blo 377762 1279367 := bstep (se 1 (by rfl) ⟨959525, by rfl⟩ : syracuseStep 1279367 = 1919051) B1919051
theorem B1082771 : Blo 377762 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B10978739 : Blo 377762 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B853433 : Blo 377762 853433 := bstep (se 2 (by rfl) ⟨320037, by rfl⟩ : syracuseStep 853433 = 640075) B640075
theorem B1541585 : Blo 377762 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B36079181 : Blo 377762 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B1279745 : Blo 377762 1279745 := bstep (se 2 (by rfl) ⟨479904, by rfl⟩ : syracuseStep 1279745 = 959809) B959809
theorem B427783 : Blo 377762 427783 := bstep (se 1 (by rfl) ⟨320837, by rfl⟩ : syracuseStep 427783 = 641675) B641675
theorem B853775 : Blo 377762 853775 := bstep (se 1 (by rfl) ⟨640331, by rfl⟩ : syracuseStep 853775 = 1280663) B1280663
theorem B853793 : Blo 377762 853793 := bstep (se 2 (by rfl) ⟨320172, by rfl⟩ : syracuseStep 853793 = 640345) B640345
theorem B427963 : Blo 377762 427963 := bstep (se 1 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 427963 = 641945) B641945
theorem B2164765 : Blo 377762 2164765 := bstep (se 3 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 2164765 = 811787) B811787
theorem B854135 : Blo 377762 854135 := bstep (se 1 (by rfl) ⟨640601, by rfl⟩ : syracuseStep 854135 = 1281203) B1281203
theorem B11634961 : Blo 377762 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B854315 : Blo 377762 854315 := bstep (se 1 (by rfl) ⟨640736, by rfl⟩ : syracuseStep 854315 = 1281473) B1281473
theorem B723259 : Blo 377762 723259 := bstep (se 1 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 723259 = 1084889) B1084889
theorem B428431 : Blo 377762 428431 := bstep (se 1 (by rfl) ⟨321323, by rfl⟩ : syracuseStep 428431 = 642647) B642647
theorem B7801235 : Blo 377762 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B1280555 : Blo 377762 1280555 := bstep (se 1 (by rfl) ⟨960416, by rfl⟩ : syracuseStep 1280555 = 1920833) B1920833
theorem B2165291 : Blo 377762 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B854675 : Blo 377762 854675 := bstep (se 1 (by rfl) ⟨641006, by rfl⟩ : syracuseStep 854675 = 1282013) B1282013
theorem B854729 : Blo 377762 854729 := bstep (se 2 (by rfl) ⟨320523, by rfl⟩ : syracuseStep 854729 = 641047) B641047
theorem B723745 : Blo 377762 723745 := bstep (se 2 (by rfl) ⟨271404, by rfl⟩ : syracuseStep 723745 = 542809) B542809
theorem B428935 : Blo 377762 428935 := bstep (se 1 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 428935 = 643403) B643403
theorem B1444817 : Blo 377762 1444817 := bstep (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) B1083613
theorem B429115 : Blo 377762 429115 := bstep (se 1 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 429115 = 643673) B643673
theorem B855431 : Blo 377762 855431 := bstep (se 1 (by rfl) ⟨641573, by rfl⟩ : syracuseStep 855431 = 1283147) B1283147
theorem B2919827 : Blo 377762 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B1445273 : Blo 377762 1445273 := bstep (se 2 (by rfl) ⟨541977, by rfl⟩ : syracuseStep 1445273 = 1083955) B1083955
theorem B855611 : Blo 377762 855611 := bstep (se 1 (by rfl) ⟨641708, by rfl⟩ : syracuseStep 855611 = 1283417) B1283417
theorem B1085015 : Blo 377762 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B855737 : Blo 377762 855737 := bstep (se 2 (by rfl) ⟨320901, by rfl⟩ : syracuseStep 855737 = 641803) B641803
theorem B2723635 : Blo 377762 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B1281851 : Blo 377762 1281851 := bstep (se 1 (by rfl) ⟨961388, by rfl⟩ : syracuseStep 1281851 = 1922777) B1922777
theorem B2461529 : Blo 377762 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B2166749 : Blo 377762 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B856079 : Blo 377762 856079 := bstep (se 1 (by rfl) ⟨642059, by rfl⟩ : syracuseStep 856079 = 1284119) B1284119
theorem B856097 : Blo 377762 856097 := bstep (se 2 (by rfl) ⟨321036, by rfl⟩ : syracuseStep 856097 = 642073) B642073
theorem B23433461 : Blo 377762 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1282337 : Blo 377762 1282337 := bstep (se 2 (by rfl) ⟨480876, by rfl⟩ : syracuseStep 1282337 = 961753) B961753
theorem B856439 : Blo 377762 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B1544633 : Blo 377762 1544633 := bstep (se 2 (by rfl) ⟨579237, by rfl⟩ : syracuseStep 1544633 = 1158475) B1158475
theorem B561655 : Blo 377762 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B856619 : Blo 377762 856619 := bstep (se 1 (by rfl) ⟨642464, by rfl⟩ : syracuseStep 856619 = 1284929) B1284929
theorem B1446443 : Blo 377762 1446443 := bstep (se 1 (by rfl) ⟨1084832, by rfl⟩ : syracuseStep 1446443 = 2169665) B2169665
theorem B463675 : Blo 377762 463675 := bstep (se 1 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 463675 = 695513) B695513
theorem B1282931 : Blo 377762 1282931 := bstep (se 1 (by rfl) ⟨962198, by rfl⟩ : syracuseStep 1282931 = 1924397) B1924397
theorem B856979 : Blo 377762 856979 := bstep (se 1 (by rfl) ⟨642734, by rfl⟩ : syracuseStep 856979 = 1285469) B1285469
theorem B857033 : Blo 377762 857033 := bstep (se 2 (by rfl) ⟨321387, by rfl⟩ : syracuseStep 857033 = 642775) B642775
theorem B1218091 : Blo 377762 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B857735 : Blo 377762 857735 := bstep (se 1 (by rfl) ⟨643301, by rfl⟩ : syracuseStep 857735 = 1286603) B1286603
theorem B4363955 : Blo 377762 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B857915 : Blo 377762 857915 := bstep (se 1 (by rfl) ⟨643436, by rfl⟩ : syracuseStep 857915 = 1286873) B1286873
theorem B858041 : Blo 377762 858041 := bstep (se 2 (by rfl) ⟨321765, by rfl⟩ : syracuseStep 858041 = 643531) B643531
theorem B4954229 : Blo 377762 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B956569 : Blo 377762 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B1022209 : Blo 377762 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B858383 : Blo 377762 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B858401 : Blo 377762 858401 := bstep (se 2 (by rfl) ⟨321900, by rfl⟩ : syracuseStep 858401 = 643801) B643801
theorem B2169139 : Blo 377762 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B956731 : Blo 377762 956731 := bstep (se 1 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 956731 = 1435097) B1435097
theorem B1939801 : Blo 377762 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B1153415 : Blo 377762 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B956873 : Blo 377762 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B2202065 : Blo 377762 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B1448401 : Blo 377762 1448401 := bstep (se 2 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 1448401 = 1086301) B1086301
theorem B858743 : Blo 377762 858743 := bstep (se 1 (by rfl) ⟨644057, by rfl⟩ : syracuseStep 858743 = 1288115) B1288115
theorem B1448705 : Blo 377762 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B957217 : Blo 377762 957217 := bstep (se 2 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 957217 = 717913) B717913
theorem B858923 : Blo 377762 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B1219475 : Blo 377762 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1449161 : Blo 377762 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B957815 : Blo 377762 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B1285523 : Blo 377762 1285523 := bstep (se 1 (by rfl) ⟨964142, by rfl⟩ : syracuseStep 1285523 = 1928285) B1928285
theorem B4333175 : Blo 377762 4333175 := bstep (se 1 (by rfl) ⟨3249881, by rfl⟩ : syracuseStep 4333175 = 6499763) B6499763
theorem B2924261 : Blo 377762 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B2170597 : Blo 377762 2170597 := bstep (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) B406987
theorem B1154827 : Blo 377762 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B3252311 : Blo 377762 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B959111 : Blo 377762 959111 := bstep (se 1 (by rfl) ⟨719333, by rfl⟩ : syracuseStep 959111 = 1438667) B1438667
theorem B959161 : Blo 377762 959161 := bstep (se 2 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 959161 = 719371) B719371
theorem B1286927 : Blo 377762 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B1287197 : Blo 377762 1287197 := bstep (se 3 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 1287197 = 482699) B482699
theorem B1615085 : Blo 377762 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B959759 : Blo 377762 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B2434337 : Blo 377762 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B566663 : Blo 377762 566663 := bstep (se 1 (by rfl) ⟨424997, by rfl⟩ : syracuseStep 566663 = 849995) B849995
theorem B1942937 : Blo 377762 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B566699 : Blo 377762 566699 := bstep (se 1 (by rfl) ⟨425024, by rfl⟩ : syracuseStep 566699 = 850049) B850049
theorem B566729 : Blo 377762 566729 := bstep (se 2 (by rfl) ⟨212523, by rfl⟩ : syracuseStep 566729 = 425047) B425047
theorem B566843 : Blo 377762 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B566903 : Blo 377762 566903 := bstep (se 1 (by rfl) ⟨425177, by rfl⟩ : syracuseStep 566903 = 850355) B850355
theorem B566927 : Blo 377762 566927 := bstep (se 1 (by rfl) ⟨425195, by rfl⟩ : syracuseStep 566927 = 850391) B850391
theorem B4990643 : Blo 377762 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B566969 : Blo 377762 566969 := bstep (se 2 (by rfl) ⟨212613, by rfl⟩ : syracuseStep 566969 = 425227) B425227
theorem B16361189 : Blo 377762 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B567047 : Blo 377762 567047 := bstep (se 1 (by rfl) ⟨425285, by rfl⟩ : syracuseStep 567047 = 850571) B850571
theorem B567083 : Blo 377762 567083 := bstep (se 1 (by rfl) ⟨425312, by rfl⟩ : syracuseStep 567083 = 850625) B850625
theorem B7939889 : Blo 377762 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B567113 : Blo 377762 567113 := bstep (se 2 (by rfl) ⟨212667, by rfl⟩ : syracuseStep 567113 = 425335) B425335
theorem B1025939 : Blo 377762 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B567227 : Blo 377762 567227 := bstep (se 1 (by rfl) ⟨425420, by rfl⟩ : syracuseStep 567227 = 850841) B850841
theorem B960457 : Blo 377762 960457 := bstep (se 2 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 960457 = 720343) B720343
theorem B567287 : Blo 377762 567287 := bstep (se 1 (by rfl) ⟨425465, by rfl⟩ : syracuseStep 567287 = 850931) B850931
theorem B567311 : Blo 377762 567311 := bstep (se 1 (by rfl) ⟨425483, by rfl⟩ : syracuseStep 567311 = 850967) B850967
theorem B567353 : Blo 377762 567353 := bstep (se 2 (by rfl) ⟨212757, by rfl⟩ : syracuseStep 567353 = 425515) B425515
theorem B960599 : Blo 377762 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B567431 : Blo 377762 567431 := bstep (se 1 (by rfl) ⟨425573, by rfl⟩ : syracuseStep 567431 = 851147) B851147
theorem B567467 : Blo 377762 567467 := bstep (se 1 (by rfl) ⟨425600, by rfl⟩ : syracuseStep 567467 = 851201) B851201
theorem B567497 : Blo 377762 567497 := bstep (se 2 (by rfl) ⟨212811, by rfl⟩ : syracuseStep 567497 = 425623) B425623
theorem B829739 : Blo 377762 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B567611 : Blo 377762 567611 := bstep (se 1 (by rfl) ⟨425708, by rfl⟩ : syracuseStep 567611 = 851417) B851417
theorem B567671 : Blo 377762 567671 := bstep (se 1 (by rfl) ⟨425753, by rfl⟩ : syracuseStep 567671 = 851507) B851507
theorem B567695 : Blo 377762 567695 := bstep (se 1 (by rfl) ⟨425771, by rfl⟩ : syracuseStep 567695 = 851543) B851543
theorem B2173331 : Blo 377762 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B567737 : Blo 377762 567737 := bstep (se 2 (by rfl) ⟨212901, by rfl⟩ : syracuseStep 567737 = 425803) B425803
theorem B567815 : Blo 377762 567815 := bstep (se 1 (by rfl) ⟨425861, by rfl⟩ : syracuseStep 567815 = 851723) B851723
theorem B2468381 : Blo 377762 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B567851 : Blo 377762 567851 := bstep (se 1 (by rfl) ⟨425888, by rfl⟩ : syracuseStep 567851 = 851777) B851777
theorem B567881 : Blo 377762 567881 := bstep (se 2 (by rfl) ⟨212955, by rfl⟩ : syracuseStep 567881 = 425911) B425911
theorem B567995 : Blo 377762 567995 := bstep (se 1 (by rfl) ⟨425996, by rfl⟩ : syracuseStep 567995 = 851993) B851993
theorem B568055 : Blo 377762 568055 := bstep (se 1 (by rfl) ⟨426041, by rfl⟩ : syracuseStep 568055 = 852083) B852083
theorem B568079 : Blo 377762 568079 := bstep (se 1 (by rfl) ⟨426059, by rfl⟩ : syracuseStep 568079 = 852119) B852119
theorem B2960165 : Blo 377762 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B568121 : Blo 377762 568121 := bstep (se 2 (by rfl) ⟨213045, by rfl⟩ : syracuseStep 568121 = 426091) B426091
theorem B568199 : Blo 377762 568199 := bstep (se 1 (by rfl) ⟨426149, by rfl⟩ : syracuseStep 568199 = 852299) B852299
theorem B2632601 : Blo 377762 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B568235 : Blo 377762 568235 := bstep (se 1 (by rfl) ⟨426176, by rfl⟩ : syracuseStep 568235 = 852353) B852353
theorem B568265 : Blo 377762 568265 := bstep (se 2 (by rfl) ⟨213099, by rfl⟩ : syracuseStep 568265 = 426199) B426199
theorem B568379 : Blo 377762 568379 := bstep (se 1 (by rfl) ⟨426284, by rfl⟩ : syracuseStep 568379 = 852569) B852569
theorem B2174039 : Blo 377762 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B568439 : Blo 377762 568439 := bstep (se 1 (by rfl) ⟨426329, by rfl⟩ : syracuseStep 568439 = 852659) B852659
theorem B568463 : Blo 377762 568463 := bstep (se 1 (by rfl) ⟨426347, by rfl⟩ : syracuseStep 568463 = 852695) B852695
theorem B568505 : Blo 377762 568505 := bstep (se 2 (by rfl) ⟨213189, by rfl⟩ : syracuseStep 568505 = 426379) B426379
theorem B568583 : Blo 377762 568583 := bstep (se 1 (by rfl) ⟨426437, by rfl⟩ : syracuseStep 568583 = 852875) B852875
theorem B1617185 : Blo 377762 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B568619 : Blo 377762 568619 := bstep (se 1 (by rfl) ⟨426464, by rfl⟩ : syracuseStep 568619 = 852929) B852929
theorem B568649 : Blo 377762 568649 := bstep (se 2 (by rfl) ⟨213243, by rfl⟩ : syracuseStep 568649 = 426487) B426487
theorem B568763 : Blo 377762 568763 := bstep (se 1 (by rfl) ⟨426572, by rfl⟩ : syracuseStep 568763 = 853145) B853145
theorem B1027529 : Blo 377762 1027529 := bstep (se 2 (by rfl) ⟨385323, by rfl⟩ : syracuseStep 1027529 = 770647) B770647
theorem B568823 : Blo 377762 568823 := bstep (se 1 (by rfl) ⟨426617, by rfl⟩ : syracuseStep 568823 = 853235) B853235
theorem B568847 : Blo 377762 568847 := bstep (se 1 (by rfl) ⟨426635, by rfl⟩ : syracuseStep 568847 = 853271) B853271
theorem B568889 : Blo 377762 568889 := bstep (se 2 (by rfl) ⟨213333, by rfl⟩ : syracuseStep 568889 = 426667) B426667
theorem B568967 : Blo 377762 568967 := bstep (se 1 (by rfl) ⟨426725, by rfl⟩ : syracuseStep 568967 = 853451) B853451
theorem B569003 : Blo 377762 569003 := bstep (se 1 (by rfl) ⟨426752, by rfl⟩ : syracuseStep 569003 = 853505) B853505
theorem B2043593 : Blo 377762 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B569033 : Blo 377762 569033 := bstep (se 2 (by rfl) ⟨213387, by rfl⟩ : syracuseStep 569033 = 426775) B426775
theorem B1027873 : Blo 377762 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B569147 : Blo 377762 569147 := bstep (se 1 (by rfl) ⟨426860, by rfl⟩ : syracuseStep 569147 = 853721) B853721
theorem B569207 : Blo 377762 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B569231 : Blo 377762 569231 := bstep (se 1 (by rfl) ⟨426923, by rfl⟩ : syracuseStep 569231 = 853847) B853847
theorem B3092377 : Blo 377762 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B569273 : Blo 377762 569273 := bstep (se 2 (by rfl) ⟨213477, by rfl⟩ : syracuseStep 569273 = 426955) B426955
theorem B569351 : Blo 377762 569351 := bstep (se 1 (by rfl) ⟨427013, by rfl⟩ : syracuseStep 569351 = 854027) B854027
theorem B569387 : Blo 377762 569387 := bstep (se 1 (by rfl) ⟨427040, by rfl⟩ : syracuseStep 569387 = 854081) B854081
theorem B569417 : Blo 377762 569417 := bstep (se 2 (by rfl) ⟨213531, by rfl⟩ : syracuseStep 569417 = 427063) B427063
theorem B962675 : Blo 377762 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B569531 : Blo 377762 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B2896073 : Blo 377762 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B569591 : Blo 377762 569591 := bstep (se 1 (by rfl) ⟨427193, by rfl⟩ : syracuseStep 569591 = 854387) B854387
theorem B569615 : Blo 377762 569615 := bstep (se 1 (by rfl) ⟨427211, by rfl⟩ : syracuseStep 569615 = 854423) B854423
theorem B569657 : Blo 377762 569657 := bstep (se 2 (by rfl) ⟨213621, by rfl⟩ : syracuseStep 569657 = 427243) B427243
theorem B569735 : Blo 377762 569735 := bstep (se 1 (by rfl) ⟨427301, by rfl⟩ : syracuseStep 569735 = 854603) B854603
theorem B864659 : Blo 377762 864659 := bstep (se 1 (by rfl) ⟨648494, by rfl⟩ : syracuseStep 864659 = 1296989) B1296989
theorem B569771 : Blo 377762 569771 := bstep (se 1 (by rfl) ⟨427328, by rfl⟩ : syracuseStep 569771 = 854657) B854657
theorem B569801 : Blo 377762 569801 := bstep (se 2 (by rfl) ⟨213675, by rfl⟩ : syracuseStep 569801 = 427351) B427351
theorem B569915 : Blo 377762 569915 := bstep (se 1 (by rfl) ⟨427436, by rfl⟩ : syracuseStep 569915 = 854873) B854873
theorem B4305473 : Blo 377762 4305473 := bstep (se 2 (by rfl) ⟨1614552, by rfl⟩ : syracuseStep 4305473 = 3229105) B3229105
theorem B569975 : Blo 377762 569975 := bstep (se 1 (by rfl) ⟨427481, by rfl⟩ : syracuseStep 569975 = 854963) B854963
theorem B963191 : Blo 377762 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B569999 : Blo 377762 569999 := bstep (se 1 (by rfl) ⟨427499, by rfl⟩ : syracuseStep 569999 = 854999) B854999
theorem B570041 : Blo 377762 570041 := bstep (se 2 (by rfl) ⟨213765, by rfl⟩ : syracuseStep 570041 = 427531) B427531
theorem B570119 : Blo 377762 570119 := bstep (se 1 (by rfl) ⟨427589, by rfl⟩ : syracuseStep 570119 = 855179) B855179
theorem B44970773 : Blo 377762 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B5223203 : Blo 377762 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B570155 : Blo 377762 570155 := bstep (se 1 (by rfl) ⟨427616, by rfl⟩ : syracuseStep 570155 = 855233) B855233
theorem B570185 : Blo 377762 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B406415 : Blo 377762 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B570299 : Blo 377762 570299 := bstep (se 1 (by rfl) ⟨427724, by rfl⟩ : syracuseStep 570299 = 855449) B855449
theorem B570359 : Blo 377762 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B1913867 : Blo 377762 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B570383 : Blo 377762 570383 := bstep (se 1 (by rfl) ⟨427787, by rfl⟩ : syracuseStep 570383 = 855575) B855575
theorem B406543 : Blo 377762 406543 := bstep (se 1 (by rfl) ⟨304907, by rfl⟩ : syracuseStep 406543 = 609815) B609815
theorem B570425 : Blo 377762 570425 := bstep (se 2 (by rfl) ⟨213909, by rfl⟩ : syracuseStep 570425 = 427819) B427819
theorem B570503 : Blo 377762 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B570539 : Blo 377762 570539 := bstep (se 1 (by rfl) ⟨427904, by rfl⟩ : syracuseStep 570539 = 855809) B855809
theorem B1914029 : Blo 377762 1914029 := bstep (se 3 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 1914029 = 717761) B717761
theorem B570569 : Blo 377762 570569 := bstep (se 2 (by rfl) ⟨213963, by rfl⟩ : syracuseStep 570569 = 427927) B427927
theorem B1455341 : Blo 377762 1455341 := bstep (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) B545753
theorem B570683 : Blo 377762 570683 := bstep (se 1 (by rfl) ⟨428012, by rfl⟩ : syracuseStep 570683 = 856025) B856025
theorem B570743 : Blo 377762 570743 := bstep (se 1 (by rfl) ⟨428057, by rfl⟩ : syracuseStep 570743 = 856115) B856115
theorem B570767 : Blo 377762 570767 := bstep (se 1 (by rfl) ⟨428075, by rfl⟩ : syracuseStep 570767 = 856151) B856151
theorem B570809 : Blo 377762 570809 := bstep (se 2 (by rfl) ⟨214053, by rfl⟩ : syracuseStep 570809 = 428107) B428107
theorem B570887 : Blo 377762 570887 := bstep (se 1 (by rfl) ⟨428165, by rfl⟩ : syracuseStep 570887 = 856331) B856331
theorem B570923 : Blo 377762 570923 := bstep (se 1 (by rfl) ⟨428192, by rfl⟩ : syracuseStep 570923 = 856385) B856385
theorem B570953 : Blo 377762 570953 := bstep (se 2 (by rfl) ⟨214107, by rfl⟩ : syracuseStep 570953 = 428215) B428215
theorem B964183 : Blo 377762 964183 := bstep (se 1 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 964183 = 1446275) B1446275
theorem B571067 : Blo 377762 571067 := bstep (se 1 (by rfl) ⟨428300, by rfl⟩ : syracuseStep 571067 = 856601) B856601
theorem B571127 : Blo 377762 571127 := bstep (se 1 (by rfl) ⟨428345, by rfl⟩ : syracuseStep 571127 = 856691) B856691
theorem B571151 : Blo 377762 571151 := bstep (se 1 (by rfl) ⟨428363, by rfl⟩ : syracuseStep 571151 = 856727) B856727
theorem B571193 : Blo 377762 571193 := bstep (se 2 (by rfl) ⟨214197, by rfl⟩ : syracuseStep 571193 = 428395) B428395
theorem B571271 : Blo 377762 571271 := bstep (se 1 (by rfl) ⟨428453, by rfl⟩ : syracuseStep 571271 = 856907) B856907
theorem B964487 : Blo 377762 964487 := bstep (se 1 (by rfl) ⟨723365, by rfl⟩ : syracuseStep 964487 = 1446731) B1446731
theorem B571307 : Blo 377762 571307 := bstep (se 1 (by rfl) ⟨428480, by rfl⟩ : syracuseStep 571307 = 856961) B856961
theorem B571337 : Blo 377762 571337 := bstep (se 2 (by rfl) ⟨214251, by rfl⟩ : syracuseStep 571337 = 428503) B428503
theorem B964619 : Blo 377762 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B571451 : Blo 377762 571451 := bstep (se 1 (by rfl) ⟨428588, by rfl⟩ : syracuseStep 571451 = 857177) B857177
theorem B538697 : Blo 377762 538697 := bstep (se 2 (by rfl) ⟨202011, by rfl⟩ : syracuseStep 538697 = 404023) B404023
theorem B571511 : Blo 377762 571511 := bstep (se 1 (by rfl) ⟨428633, by rfl⟩ : syracuseStep 571511 = 857267) B857267
theorem B571535 : Blo 377762 571535 := bstep (se 1 (by rfl) ⟨428651, by rfl⟩ : syracuseStep 571535 = 857303) B857303
theorem B571577 : Blo 377762 571577 := bstep (se 2 (by rfl) ⟨214341, by rfl⟩ : syracuseStep 571577 = 428683) B428683
theorem B571655 : Blo 377762 571655 := bstep (se 1 (by rfl) ⟨428741, by rfl⟩ : syracuseStep 571655 = 857483) B857483
theorem B571691 : Blo 377762 571691 := bstep (se 1 (by rfl) ⟨428768, by rfl⟩ : syracuseStep 571691 = 857537) B857537
theorem B571721 : Blo 377762 571721 := bstep (se 2 (by rfl) ⟨214395, by rfl⟩ : syracuseStep 571721 = 428791) B428791
theorem B571835 : Blo 377762 571835 := bstep (se 1 (by rfl) ⟨428876, by rfl⟩ : syracuseStep 571835 = 857753) B857753
theorem B571895 : Blo 377762 571895 := bstep (se 1 (by rfl) ⟨428921, by rfl⟩ : syracuseStep 571895 = 857843) B857843
theorem B571919 : Blo 377762 571919 := bstep (se 1 (by rfl) ⟨428939, by rfl⟩ : syracuseStep 571919 = 857879) B857879
theorem B965135 : Blo 377762 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B637483 : Blo 377762 637483 := bstep (se 1 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 637483 = 956225) B956225
theorem B571961 : Blo 377762 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B539255 : Blo 377762 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B572039 : Blo 377762 572039 := bstep (se 1 (by rfl) ⟨429029, by rfl⟩ : syracuseStep 572039 = 858059) B858059
theorem B965267 : Blo 377762 965267 := bstep (se 1 (by rfl) ⟨723950, by rfl⟩ : syracuseStep 965267 = 1447901) B1447901
theorem B572075 : Blo 377762 572075 := bstep (se 1 (by rfl) ⟨429056, by rfl⟩ : syracuseStep 572075 = 858113) B858113
theorem B637625 : Blo 377762 637625 := bstep (se 2 (by rfl) ⟨239109, by rfl⟩ : syracuseStep 637625 = 478219) B478219
theorem B572105 : Blo 377762 572105 := bstep (se 2 (by rfl) ⟨214539, by rfl⟩ : syracuseStep 572105 = 429079) B429079
theorem B1915649 : Blo 377762 1915649 := bstep (se 2 (by rfl) ⟨718368, by rfl⟩ : syracuseStep 1915649 = 1436737) B1436737
theorem B572219 : Blo 377762 572219 := bstep (se 1 (by rfl) ⟨429164, by rfl⟩ : syracuseStep 572219 = 858329) B858329
theorem B3652427 : Blo 377762 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B572279 : Blo 377762 572279 := bstep (se 1 (by rfl) ⟨429209, by rfl⟩ : syracuseStep 572279 = 858419) B858419
theorem B572303 : Blo 377762 572303 := bstep (se 1 (by rfl) ⟨429227, by rfl⟩ : syracuseStep 572303 = 858455) B858455
theorem B539563 : Blo 377762 539563 := bstep (se 1 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 539563 = 809345) B809345
theorem B572345 : Blo 377762 572345 := bstep (se 2 (by rfl) ⟨214629, by rfl⟩ : syracuseStep 572345 = 429259) B429259
theorem B1817603 : Blo 377762 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B572423 : Blo 377762 572423 := bstep (se 1 (by rfl) ⟨429317, by rfl⟩ : syracuseStep 572423 = 858635) B858635
theorem B1031183 : Blo 377762 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B605227 : Blo 377762 605227 := bstep (se 1 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 605227 = 907841) B907841
theorem B572459 : Blo 377762 572459 := bstep (se 1 (by rfl) ⟨429344, by rfl⟩ : syracuseStep 572459 = 858689) B858689
theorem B1850435 : Blo 377762 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B572489 : Blo 377762 572489 := bstep (se 2 (by rfl) ⟨214683, by rfl⟩ : syracuseStep 572489 = 429367) B429367
theorem B605369 : Blo 377762 605369 := bstep (se 2 (by rfl) ⟨227013, by rfl⟩ : syracuseStep 605369 = 454027) B454027
theorem B572603 : Blo 377762 572603 := bstep (se 1 (by rfl) ⟨429452, by rfl⟩ : syracuseStep 572603 = 858905) B858905
theorem B2604269 : Blo 377762 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B4668661 : Blo 377762 4668661 := bstep (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) B437687
theorem B638327 : Blo 377762 638327 := bstep (se 1 (by rfl) ⟨478745, by rfl⟩ : syracuseStep 638327 = 957491) B957491
theorem B540047 : Blo 377762 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B1818065 : Blo 377762 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B1621457 : Blo 377762 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B1916459 : Blo 377762 1916459 := bstep (se 1 (by rfl) ⟨1437344, by rfl⟩ : syracuseStep 1916459 = 2874689) B2874689
theorem B638779 : Blo 377762 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B638921 : Blo 377762 638921 := bstep (se 2 (by rfl) ⟨239595, by rfl⟩ : syracuseStep 638921 = 479191) B479191
theorem B606599 : Blo 377762 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B2441771 : Blo 377762 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B4112963 : Blo 377762 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B5653111 : Blo 377762 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B639623 : Blo 377762 639623 := bstep (se 1 (by rfl) ⟨479717, by rfl⟩ : syracuseStep 639623 = 959435) B959435
theorem B1917755 : Blo 377762 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B2048827 : Blo 377762 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B377787 : Blo 377762 377787 := bstep (se 1 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 377787 = 566681) B566681
theorem B1917917 : Blo 377762 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B377863 : Blo 377762 377863 := bstep (se 1 (by rfl) ⟨283397, by rfl⟩ : syracuseStep 377863 = 566795) B566795
theorem B377871 : Blo 377762 377871 := bstep (se 1 (by rfl) ⟨283403, by rfl⟩ : syracuseStep 377871 = 566807) B566807
theorem B377915 : Blo 377762 377915 := bstep (se 1 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 377915 = 566873) B566873
theorem B377991 : Blo 377762 377991 := bstep (se 1 (by rfl) ⟨283493, by rfl⟩ : syracuseStep 377991 = 566987) B566987
theorem B377999 : Blo 377762 377999 := bstep (se 1 (by rfl) ⟨283499, by rfl⟩ : syracuseStep 377999 = 566999) B566999
theorem B378043 : Blo 377762 378043 := bstep (se 1 (by rfl) ⟨283532, by rfl⟩ : syracuseStep 378043 = 567065) B567065
theorem B378119 : Blo 377762 378119 := bstep (se 1 (by rfl) ⟨283589, by rfl⟩ : syracuseStep 378119 = 567179) B567179
theorem B378127 : Blo 377762 378127 := bstep (se 1 (by rfl) ⟨283595, by rfl⟩ : syracuseStep 378127 = 567191) B567191
theorem B640271 : Blo 377762 640271 := bstep (se 1 (by rfl) ⟨480203, by rfl⟩ : syracuseStep 640271 = 960407) B960407
theorem B1918241 : Blo 377762 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B378171 : Blo 377762 378171 := bstep (se 1 (by rfl) ⟨283628, by rfl⟩ : syracuseStep 378171 = 567257) B567257
theorem B378247 : Blo 377762 378247 := bstep (se 1 (by rfl) ⟨283685, by rfl⟩ : syracuseStep 378247 = 567371) B567371
theorem B378255 : Blo 377762 378255 := bstep (se 1 (by rfl) ⟨283691, by rfl⟩ : syracuseStep 378255 = 567383) B567383
theorem B378299 : Blo 377762 378299 := bstep (se 1 (by rfl) ⟨283724, by rfl⟩ : syracuseStep 378299 = 567449) B567449
theorem B378375 : Blo 377762 378375 := bstep (se 1 (by rfl) ⟨283781, by rfl⟩ : syracuseStep 378375 = 567563) B567563
theorem B378383 : Blo 377762 378383 := bstep (se 1 (by rfl) ⟨283787, by rfl⟩ : syracuseStep 378383 = 567575) B567575
theorem B542251 : Blo 377762 542251 := bstep (se 1 (by rfl) ⟨406688, by rfl⟩ : syracuseStep 542251 = 813377) B813377
theorem B378427 : Blo 377762 378427 := bstep (se 1 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 378427 = 567641) B567641
theorem B378503 : Blo 377762 378503 := bstep (se 1 (by rfl) ⟨283877, by rfl⟩ : syracuseStep 378503 = 567755) B567755
theorem B378511 : Blo 377762 378511 := bstep (se 1 (by rfl) ⟨283883, by rfl⟩ : syracuseStep 378511 = 567767) B567767
theorem B378555 : Blo 377762 378555 := bstep (se 1 (by rfl) ⟨283916, by rfl⟩ : syracuseStep 378555 = 567833) B567833
theorem B378631 : Blo 377762 378631 := bstep (se 1 (by rfl) ⟨283973, by rfl⟩ : syracuseStep 378631 = 567947) B567947
theorem B378639 : Blo 377762 378639 := bstep (se 1 (by rfl) ⟨283979, by rfl⟩ : syracuseStep 378639 = 567959) B567959
theorem B542479 : Blo 377762 542479 := bstep (se 1 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 542479 = 813719) B813719
theorem B640811 : Blo 377762 640811 := bstep (se 1 (by rfl) ⟨480608, by rfl⟩ : syracuseStep 640811 = 961217) B961217
theorem B378683 : Blo 377762 378683 := bstep (se 1 (by rfl) ⟨284012, by rfl⟩ : syracuseStep 378683 = 568025) B568025
theorem B378759 : Blo 377762 378759 := bstep (se 1 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 378759 = 568139) B568139
theorem B378767 : Blo 377762 378767 := bstep (se 1 (by rfl) ⟨284075, by rfl⟩ : syracuseStep 378767 = 568151) B568151
theorem B2312081 : Blo 377762 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B378811 : Blo 377762 378811 := bstep (se 1 (by rfl) ⟨284108, by rfl⟩ : syracuseStep 378811 = 568217) B568217
theorem B378887 : Blo 377762 378887 := bstep (se 1 (by rfl) ⟨284165, by rfl⟩ : syracuseStep 378887 = 568331) B568331
theorem B378895 : Blo 377762 378895 := bstep (se 1 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 378895 = 568343) B568343
theorem B378939 : Blo 377762 378939 := bstep (se 1 (by rfl) ⟨284204, by rfl⟩ : syracuseStep 378939 = 568409) B568409
theorem B379015 : Blo 377762 379015 := bstep (se 1 (by rfl) ⟨284261, by rfl⟩ : syracuseStep 379015 = 568523) B568523
theorem B379023 : Blo 377762 379023 := bstep (se 1 (by rfl) ⟨284267, by rfl⟩ : syracuseStep 379023 = 568535) B568535
theorem B641209 : Blo 377762 641209 := bstep (se 2 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 641209 = 480907) B480907
theorem B379067 : Blo 377762 379067 := bstep (se 1 (by rfl) ⟨284300, by rfl⟩ : syracuseStep 379067 = 568601) B568601
theorem B1919213 : Blo 377762 1919213 := bstep (se 3 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 1919213 = 719705) B719705
theorem B379143 : Blo 377762 379143 := bstep (se 1 (by rfl) ⟨284357, by rfl⟩ : syracuseStep 379143 = 568715) B568715
theorem B379151 : Blo 377762 379151 := bstep (se 1 (by rfl) ⟨284363, by rfl⟩ : syracuseStep 379151 = 568727) B568727
theorem B1820987 : Blo 377762 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B379195 : Blo 377762 379195 := bstep (se 1 (by rfl) ⟨284396, by rfl⟩ : syracuseStep 379195 = 568793) B568793
theorem B379271 : Blo 377762 379271 := bstep (se 1 (by rfl) ⟨284453, by rfl⟩ : syracuseStep 379271 = 568907) B568907
theorem B379279 : Blo 377762 379279 := bstep (se 1 (by rfl) ⟨284459, by rfl⟩ : syracuseStep 379279 = 568919) B568919
theorem B379323 : Blo 377762 379323 := bstep (se 1 (by rfl) ⟨284492, by rfl⟩ : syracuseStep 379323 = 568985) B568985
theorem B379399 : Blo 377762 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B379407 : Blo 377762 379407 := bstep (se 1 (by rfl) ⟨284555, by rfl⟩ : syracuseStep 379407 = 569111) B569111
theorem B379451 : Blo 377762 379451 := bstep (se 1 (by rfl) ⟨284588, by rfl⟩ : syracuseStep 379451 = 569177) B569177
theorem B1100375 : Blo 377762 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B379527 : Blo 377762 379527 := bstep (se 1 (by rfl) ⟨284645, by rfl⟩ : syracuseStep 379527 = 569291) B569291
theorem B379535 : Blo 377762 379535 := bstep (se 1 (by rfl) ⟨284651, by rfl⟩ : syracuseStep 379535 = 569303) B569303
theorem B379579 : Blo 377762 379579 := bstep (se 1 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 379579 = 569369) B569369
theorem B379655 : Blo 377762 379655 := bstep (se 1 (by rfl) ⟨284741, by rfl⟩ : syracuseStep 379655 = 569483) B569483
theorem B379663 : Blo 377762 379663 := bstep (se 1 (by rfl) ⟨284747, by rfl⟩ : syracuseStep 379663 = 569495) B569495
theorem B5917475 : Blo 377762 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B1329979 : Blo 377762 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B379707 : Blo 377762 379707 := bstep (se 1 (by rfl) ⟨284780, by rfl⟩ : syracuseStep 379707 = 569561) B569561
theorem B641911 : Blo 377762 641911 := bstep (se 1 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 641911 = 962867) B962867
theorem B379783 : Blo 377762 379783 := bstep (se 1 (by rfl) ⟨284837, by rfl⟩ : syracuseStep 379783 = 569675) B569675
theorem B379791 : Blo 377762 379791 := bstep (se 1 (by rfl) ⟨284843, by rfl⟩ : syracuseStep 379791 = 569687) B569687
theorem B379835 : Blo 377762 379835 := bstep (se 1 (by rfl) ⟨284876, by rfl⟩ : syracuseStep 379835 = 569753) B569753
theorem B2608075 : Blo 377762 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B379911 : Blo 377762 379911 := bstep (se 1 (by rfl) ⟨284933, by rfl⟩ : syracuseStep 379911 = 569867) B569867
theorem B412679 : Blo 377762 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B379919 : Blo 377762 379919 := bstep (se 1 (by rfl) ⟨284939, by rfl⟩ : syracuseStep 379919 = 569879) B569879
theorem B1920023 : Blo 377762 1920023 := bstep (se 1 (by rfl) ⟨1440017, by rfl⟩ : syracuseStep 1920023 = 2880035) B2880035
theorem B642107 : Blo 377762 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B379963 : Blo 377762 379963 := bstep (se 1 (by rfl) ⟨284972, by rfl⟩ : syracuseStep 379963 = 569945) B569945
theorem B380039 : Blo 377762 380039 := bstep (se 1 (by rfl) ⟨285029, by rfl⟩ : syracuseStep 380039 = 570059) B570059
theorem B380047 : Blo 377762 380047 := bstep (se 1 (by rfl) ⟨285035, by rfl⟩ : syracuseStep 380047 = 570071) B570071
theorem B380091 : Blo 377762 380091 := bstep (se 1 (by rfl) ⟨285068, by rfl⟩ : syracuseStep 380091 = 570137) B570137
theorem B380167 : Blo 377762 380167 := bstep (se 1 (by rfl) ⟨285125, by rfl⟩ : syracuseStep 380167 = 570251) B570251
theorem B380175 : Blo 377762 380175 := bstep (se 1 (by rfl) ⟨285131, by rfl⟩ : syracuseStep 380175 = 570263) B570263
theorem B1723681 : Blo 377762 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B380219 : Blo 377762 380219 := bstep (se 1 (by rfl) ⟨285164, by rfl⟩ : syracuseStep 380219 = 570329) B570329
theorem B380295 : Blo 377762 380295 := bstep (se 1 (by rfl) ⟨285221, by rfl⟩ : syracuseStep 380295 = 570443) B570443
theorem B380303 : Blo 377762 380303 := bstep (se 1 (by rfl) ⟨285227, by rfl⟩ : syracuseStep 380303 = 570455) B570455
theorem B380347 : Blo 377762 380347 := bstep (se 1 (by rfl) ⟨285260, by rfl⟩ : syracuseStep 380347 = 570521) B570521
theorem B642505 : Blo 377762 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B380423 : Blo 377762 380423 := bstep (se 1 (by rfl) ⟨285317, by rfl⟩ : syracuseStep 380423 = 570635) B570635
theorem B380431 : Blo 377762 380431 := bstep (se 1 (by rfl) ⟨285323, by rfl⟩ : syracuseStep 380431 = 570647) B570647
theorem B380475 : Blo 377762 380475 := bstep (se 1 (by rfl) ⟨285356, by rfl⟩ : syracuseStep 380475 = 570713) B570713
theorem B380551 : Blo 377762 380551 := bstep (se 1 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 380551 = 570827) B570827
theorem B380559 : Blo 377762 380559 := bstep (se 1 (by rfl) ⟨285419, by rfl⟩ : syracuseStep 380559 = 570839) B570839
theorem B380603 : Blo 377762 380603 := bstep (se 1 (by rfl) ⟨285452, by rfl⟩ : syracuseStep 380603 = 570905) B570905
theorem B1822409 : Blo 377762 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B380679 : Blo 377762 380679 := bstep (se 1 (by rfl) ⟨285509, by rfl⟩ : syracuseStep 380679 = 571019) B571019
theorem B380687 : Blo 377762 380687 := bstep (se 1 (by rfl) ⟨285515, by rfl⟩ : syracuseStep 380687 = 571031) B571031
theorem B380731 : Blo 377762 380731 := bstep (se 1 (by rfl) ⟨285548, by rfl⟩ : syracuseStep 380731 = 571097) B571097
theorem B380807 : Blo 377762 380807 := bstep (se 1 (by rfl) ⟨285605, by rfl⟩ : syracuseStep 380807 = 571211) B571211
theorem B380815 : Blo 377762 380815 := bstep (se 1 (by rfl) ⟨285611, by rfl⟩ : syracuseStep 380815 = 571223) B571223
theorem B380859 : Blo 377762 380859 := bstep (se 1 (by rfl) ⟨285644, by rfl⟩ : syracuseStep 380859 = 571289) B571289
theorem B8212427 : Blo 377762 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B380935 : Blo 377762 380935 := bstep (se 1 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 380935 = 571403) B571403
theorem B380943 : Blo 377762 380943 := bstep (se 1 (by rfl) ⟨285707, by rfl⟩ : syracuseStep 380943 = 571415) B571415
theorem B380987 : Blo 377762 380987 := bstep (se 1 (by rfl) ⟨285740, by rfl⟩ : syracuseStep 380987 = 571481) B571481
theorem B381063 : Blo 377762 381063 := bstep (se 1 (by rfl) ⟨285797, by rfl⟩ : syracuseStep 381063 = 571595) B571595
theorem B643207 : Blo 377762 643207 := bstep (se 1 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 643207 = 964811) B964811
theorem B381071 : Blo 377762 381071 := bstep (se 1 (by rfl) ⟨285803, by rfl⟩ : syracuseStep 381071 = 571607) B571607
theorem B970937 : Blo 377762 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B381115 : Blo 377762 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B381191 : Blo 377762 381191 := bstep (se 1 (by rfl) ⟨285893, by rfl⟩ : syracuseStep 381191 = 571787) B571787
theorem B381199 : Blo 377762 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B381243 : Blo 377762 381243 := bstep (se 1 (by rfl) ⟨285932, by rfl⟩ : syracuseStep 381243 = 571865) B571865
theorem B381319 : Blo 377762 381319 := bstep (se 1 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 381319 = 571979) B571979
theorem B381327 : Blo 377762 381327 := bstep (se 1 (by rfl) ⟨285995, by rfl⟩ : syracuseStep 381327 = 571991) B571991
theorem B4346297 : Blo 377762 4346297 := bstep (se 2 (by rfl) ⟨1629861, by rfl⟩ : syracuseStep 4346297 = 3259723) B3259723
theorem B381371 : Blo 377762 381371 := bstep (se 1 (by rfl) ⟨286028, by rfl⟩ : syracuseStep 381371 = 572057) B572057
theorem B2871773 : Blo 377762 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B381447 : Blo 377762 381447 := bstep (se 1 (by rfl) ⟨286085, by rfl⟩ : syracuseStep 381447 = 572171) B572171
theorem B381455 : Blo 377762 381455 := bstep (se 1 (by rfl) ⟨286091, by rfl⟩ : syracuseStep 381455 = 572183) B572183
theorem B381499 : Blo 377762 381499 := bstep (se 1 (by rfl) ⟨286124, by rfl⟩ : syracuseStep 381499 = 572249) B572249
theorem B381575 : Blo 377762 381575 := bstep (se 1 (by rfl) ⟨286181, by rfl⟩ : syracuseStep 381575 = 572363) B572363
theorem B381583 : Blo 377762 381583 := bstep (se 1 (by rfl) ⟨286187, by rfl⟩ : syracuseStep 381583 = 572375) B572375
theorem B381627 : Blo 377762 381627 := bstep (se 1 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 381627 = 572441) B572441
theorem B2052809 : Blo 377762 2052809 := bstep (se 2 (by rfl) ⟨769803, by rfl⟩ : syracuseStep 2052809 = 1539607) B1539607
theorem B381703 : Blo 377762 381703 := bstep (se 1 (by rfl) ⟨286277, by rfl⟩ : syracuseStep 381703 = 572555) B572555
theorem B643855 : Blo 377762 643855 := bstep (se 1 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 643855 = 965783) B965783
theorem B381711 : Blo 377762 381711 := bstep (se 1 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 381711 = 572567) B572567
theorem B381755 : Blo 377762 381755 := bstep (se 1 (by rfl) ⟨286316, by rfl⟩ : syracuseStep 381755 = 572633) B572633
theorem B1364921 : Blo 377762 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B807995 : Blo 377762 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B1955339 : Blo 377762 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B480811 : Blo 377762 480811 := bstep (se 1 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 480811 = 721217) B721217
theorem B1365913 : Blo 377762 1365913 := bstep (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) B1024435
theorem B1923101 : Blo 377762 1923101 := bstep (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) B721163
theorem B809003 : Blo 377762 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B13162769 : Blo 377762 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B1628531 : Blo 377762 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B481783 : Blo 377762 481783 := bstep (se 1 (by rfl) ⟨361337, by rfl⟩ : syracuseStep 481783 = 722675) B722675
theorem B1923587 : Blo 377762 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B1825291 : Blo 377762 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B482107 : Blo 377762 482107 := bstep (se 1 (by rfl) ⟨361580, by rfl⟩ : syracuseStep 482107 = 723161) B723161
theorem B1727531 : Blo 377762 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B1367297 : Blo 377762 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B810643 : Blo 377762 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B483079 : Blo 377762 483079 := bstep (se 1 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 483079 = 724619) B724619
theorem B909071 : Blo 377762 909071 := bstep (se 1 (by rfl) ⟨681803, by rfl⟩ : syracuseStep 909071 = 1363607) B1363607
theorem B810899 : Blo 377762 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B1925207 : Blo 377762 1925207 := bstep (se 1 (by rfl) ⟨1443905, by rfl⟩ : syracuseStep 1925207 = 2887811) B2887811
theorem B1368265 : Blo 377762 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B6512885 : Blo 377762 6512885 := bstep (se 5 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 6512885 = 610583) B610583
theorem B1925693 : Blo 377762 1925693 := bstep (se 3 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 1925693 = 722135) B722135
theorem B2745089 : Blo 377762 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B7267643 : Blo 377762 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 377762 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B4318595 : Blo 377762 4318595 := bstep (se 1 (by rfl) ⟨3238946, by rfl⟩ : syracuseStep 4318595 = 6477893) B6477893
theorem B2319769 : Blo 377762 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B648905 : Blo 377762 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B3630899 : Blo 377762 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B1828811 : Blo 377762 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B911513 : Blo 377762 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B813257 : Blo 377762 813257 := bstep (se 2 (by rfl) ⟨304971, by rfl⟩ : syracuseStep 813257 = 609943) B609943
theorem B1927475 : Blo 377762 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B1436039 : Blo 377762 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B8251793 : Blo 377762 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B1927799 : Blo 377762 1927799 := bstep (se 1 (by rfl) ⟨1445849, by rfl⟩ : syracuseStep 1927799 = 2891699) B2891699
theorem B486059 : Blo 377762 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B1075913 : Blo 377762 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B2157293 : Blo 377762 2157293 := bstep (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) B808985
theorem B814009 : Blo 377762 814009 := bstep (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) B610507
theorem B1076267 : Blo 377762 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B1666115 : Blo 377762 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B1174675 : Blo 377762 1174675 := bstep (se 1 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 1174675 = 1762013) B1762013
theorem B1076665 : Blo 377762 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B2911697 : Blo 377762 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B650767 : Blo 377762 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B814607 : Blo 377762 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B1928771 : Blo 377762 1928771 := bstep (se 1 (by rfl) ⟨1446578, by rfl⟩ : syracuseStep 1928771 = 2893157) B2893157
theorem B1929095 : Blo 377762 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B1732499 : Blo 377762 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B2813849 : Blo 377762 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B2879549 : Blo 377762 2879549 := bstep (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) B1079831
theorem B454843 : Blo 377762 454843 := bstep (se 1 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 454843 = 682265) B682265
theorem B2060633 : Blo 377762 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B913799 : Blo 377762 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B487951 : Blo 377762 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B1077907 : Blo 377762 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B586697 : Blo 377762 586697 := bstep (se 2 (by rfl) ⟨220011, by rfl⟩ : syracuseStep 586697 = 440023) B440023
theorem B914491 : Blo 377762 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B717959 : Blo 377762 717959 := bstep (se 1 (by rfl) ⟨538469, by rfl⟩ : syracuseStep 717959 = 1076939) B1076939
theorem B619721 : Blo 377762 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B3077585 : Blo 377762 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1275479 : Blo 377762 1275479 := bstep (se 1 (by rfl) ⟨956609, by rfl⟩ : syracuseStep 1275479 = 1913219) B1913219
theorem B718483 : Blo 377762 718483 := bstep (se 1 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 718483 = 1077725) B1077725
theorem B2783243 : Blo 377762 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B7010327 : Blo 377762 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B1275965 : Blo 377762 1275965 := bstep (se 3 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 1275965 = 478487) B478487
theorem B850067 : Blo 377762 850067 := bstep (se 1 (by rfl) ⟨637550, by rfl⟩ : syracuseStep 850067 = 1275101) B1275101
theorem B850121 : Blo 377762 850121 := bstep (se 2 (by rfl) ⟨318795, by rfl⟩ : syracuseStep 850121 = 637591) B637591
theorem B1079581 : Blo 377762 1079581 := bstep (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) B404843
theorem B1079639 : Blo 377762 1079639 := bstep (se 1 (by rfl) ⟨809729, by rfl⟩ : syracuseStep 1079639 = 1619459) B1619459
theorem B915799 : Blo 377762 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B73202069 : Blo 377762 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B1833425 : Blo 377762 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B457207 : Blo 377762 457207 := bstep (se 1 (by rfl) ⟨342905, by rfl⟩ : syracuseStep 457207 = 685811) B685811
theorem B1374839 : Blo 377762 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B2063141 : Blo 377762 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B719675 : Blo 377762 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B850823 : Blo 377762 850823 := bstep (se 1 (by rfl) ⟨638117, by rfl⟩ : syracuseStep 850823 = 1276235) B1276235
theorem B2161667 : Blo 377762 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B851003 : Blo 377762 851003 := bstep (se 1 (by rfl) ⟨638252, by rfl⟩ : syracuseStep 851003 = 1276505) B1276505
theorem B851129 : Blo 377762 851129 := bstep (se 2 (by rfl) ⟨319173, by rfl⟩ : syracuseStep 851129 = 638347) B638347
theorem B720161 : Blo 377762 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B1932659 : Blo 377762 1932659 := bstep (se 1 (by rfl) ⟨1449494, by rfl⟩ : syracuseStep 1932659 = 2898989) B2898989
theorem B2882951 : Blo 377762 2882951 := bstep (se 1 (by rfl) ⟨2162213, by rfl⟩ : syracuseStep 2882951 = 4324427) B4324427
theorem B1277369 : Blo 377762 1277369 := bstep (se 2 (by rfl) ⟨479013, by rfl⟩ : syracuseStep 1277369 = 958027) B958027
theorem B2162123 : Blo 377762 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B425479 : Blo 377762 425479 := bstep (se 1 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 425479 = 638219) B638219
theorem B851471 : Blo 377762 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B851489 : Blo 377762 851489 := bstep (se 2 (by rfl) ⟨319308, by rfl⟩ : syracuseStep 851489 = 638617) B638617
theorem B720427 : Blo 377762 720427 := bstep (se 1 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 720427 = 1080641) B1080641
theorem B3243563 : Blo 377762 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B425659 : Blo 377762 425659 := bstep (se 1 (by rfl) ⟨319244, by rfl⟩ : syracuseStep 425659 = 638489) B638489
theorem B7307009 : Blo 377762 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B851831 : Blo 377762 851831 := bstep (se 1 (by rfl) ⟨638873, by rfl⟩ : syracuseStep 851831 = 1277747) B1277747
theorem B1081289 : Blo 377762 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B851975 : Blo 377762 851975 := bstep (se 1 (by rfl) ⟨638981, by rfl⟩ : syracuseStep 851975 = 1277963) B1277963
theorem B852047 : Blo 377762 852047 := bstep (se 1 (by rfl) ⟨639035, by rfl⟩ : syracuseStep 852047 = 1278071) B1278071
theorem B1441871 : Blo 377762 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B426415 : Blo 377762 426415 := bstep (se 1 (by rfl) ⟨319811, by rfl⟩ : syracuseStep 426415 = 639623) B639623
theorem B852443 : Blo 377762 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B1278503 : Blo 377762 1278503 := bstep (se 1 (by rfl) ⟨958877, by rfl⟩ : syracuseStep 1278503 = 1917755) B1917755
theorem B1278611 : Blo 377762 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B721619 : Blo 377762 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B7537481 : Blo 377762 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B426847 : Blo 377762 426847 := bstep (se 1 (by rfl) ⟨320135, by rfl⟩ : syracuseStep 426847 = 640271) B640271
theorem B1278827 : Blo 377762 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B1278881 : Blo 377762 1278881 := bstep (se 2 (by rfl) ⟨479580, by rfl⟩ : syracuseStep 1278881 = 959161) B959161
theorem B852911 : Blo 377762 852911 := bstep (se 1 (by rfl) ⟨639683, by rfl⟩ : syracuseStep 852911 = 1279367) B1279367
theorem B721847 : Blo 377762 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B24052787 : Blo 377762 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1442873 : Blo 377762 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B853163 : Blo 377762 853163 := bstep (se 1 (by rfl) ⟨639872, by rfl⟩ : syracuseStep 853163 = 1279745) B1279745
theorem B427207 : Blo 377762 427207 := bstep (se 1 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 427207 = 640811) B640811
theorem B1541387 : Blo 377762 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1279475 : Blo 377762 1279475 := bstep (se 1 (by rfl) ⟨959606, by rfl⟩ : syracuseStep 1279475 = 1919213) B1919213
theorem B1213991 : Blo 377762 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B853703 : Blo 377762 853703 := bstep (se 1 (by rfl) ⟨640277, by rfl⟩ : syracuseStep 853703 = 1280555) B1280555
theorem B1443527 : Blo 377762 1443527 := bstep (se 1 (by rfl) ⟨1082645, by rfl⟩ : syracuseStep 1443527 = 2165291) B2165291
theorem B1280015 : Blo 377762 1280015 := bstep (se 1 (by rfl) ⟨960011, by rfl⟩ : syracuseStep 1280015 = 1920023) B1920023
theorem B428071 : Blo 377762 428071 := bstep (se 1 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 428071 = 642107) B642107
theorem B723001 : Blo 377762 723001 := bstep (se 2 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 723001 = 542251) B542251
theorem B723305 : Blo 377762 723305 := bstep (se 2 (by rfl) ⟨271239, by rfl⟩ : syracuseStep 723305 = 542479) B542479
theorem B1083773 : Blo 377762 1083773 := bstep (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) B406415
theorem B723343 : Blo 377762 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B1214939 : Blo 377762 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B854567 : Blo 377762 854567 := bstep (se 1 (by rfl) ⟨640925, by rfl⟩ : syracuseStep 854567 = 1281851) B1281851
theorem B1280609 : Blo 377762 1280609 := bstep (se 2 (by rfl) ⟨480228, by rfl⟩ : syracuseStep 1280609 = 960457) B960457
theorem B5474951 : Blo 377762 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B1444499 : Blo 377762 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B2886353 : Blo 377762 2886353 := bstep (se 2 (by rfl) ⟨1082382, by rfl⟩ : syracuseStep 2886353 = 2164765) B2164765
theorem B854891 : Blo 377762 854891 := bstep (se 1 (by rfl) ⟨641168, by rfl⟩ : syracuseStep 854891 = 1282337) B1282337
theorem B854945 : Blo 377762 854945 := bstep (se 2 (by rfl) ⟨320604, by rfl⟩ : syracuseStep 854945 = 641209) B641209
theorem B855287 : Blo 377762 855287 := bstep (se 1 (by rfl) ⟨641465, by rfl⟩ : syracuseStep 855287 = 1282931) B1282931
theorem B1773305 : Blo 377762 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B855881 : Blo 377762 855881 := bstep (se 2 (by rfl) ⟨320955, by rfl⟩ : syracuseStep 855881 = 641911) B641911
theorem B1085345 : Blo 377762 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B3477433 : Blo 377762 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B1282067 : Blo 377762 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B1085687 : Blo 377762 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B1282391 : Blo 377762 1282391 := bstep (se 1 (by rfl) ⟨961793, by rfl⟩ : syracuseStep 1282391 = 1923587) B1923587
theorem B2298241 : Blo 377762 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B856673 : Blo 377762 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B1151687 : Blo 377762 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B9966341 : Blo 377762 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B857015 : Blo 377762 857015 := bstep (se 1 (by rfl) ⟨642761, by rfl⟩ : syracuseStep 857015 = 1285523) B1285523
theorem B2888783 : Blo 377762 2888783 := bstep (se 1 (by rfl) ⟨2166587, by rfl⟩ : syracuseStep 2888783 = 4333175) B4333175
theorem B1283471 : Blo 377762 1283471 := bstep (se 1 (by rfl) ⟨962603, by rfl⟩ : syracuseStep 1283471 = 1925207) B1925207
theorem B2168207 : Blo 377762 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B857609 : Blo 377762 857609 := bstep (se 2 (by rfl) ⟨321603, by rfl⟩ : syracuseStep 857609 = 643207) B643207
theorem B1283795 : Blo 377762 1283795 := bstep (se 1 (by rfl) ⟨962846, by rfl⟩ : syracuseStep 1283795 = 1925693) B1925693
theorem B857951 : Blo 377762 857951 := bstep (se 1 (by rfl) ⟨643463, by rfl⟩ : syracuseStep 857951 = 1286927) B1286927
theorem B858131 : Blo 377762 858131 := bstep (se 1 (by rfl) ⟨643598, by rfl⟩ : syracuseStep 858131 = 1287197) B1287197
theorem B858473 : Blo 377762 858473 := bstep (se 2 (by rfl) ⟨321927, by rfl⟩ : syracuseStep 858473 = 643855) B643855
theorem B1219207 : Blo 377762 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B1219321 : Blo 377762 1219321 := bstep (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) B914491
theorem B1284983 : Blo 377762 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B957359 : Blo 377762 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B1448887 : Blo 377762 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B1285199 : Blo 377762 1285199 := bstep (se 1 (by rfl) ⟨963899, by rfl⟩ : syracuseStep 1285199 = 1927799) B1927799
theorem B1973443 : Blo 377762 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B1449359 : Blo 377762 1449359 := bstep (se 1 (by rfl) ⟨1087019, by rfl⟩ : syracuseStep 1449359 = 2174039) B2174039
theorem B1285577 : Blo 377762 1285577 := bstep (se 2 (by rfl) ⟨482091, by rfl⟩ : syracuseStep 1285577 = 964183) B964183
theorem B957977 : Blo 377762 957977 := bstep (se 2 (by rfl) ⟨359241, by rfl⟩ : syracuseStep 957977 = 718483) B718483
theorem B1941131 : Blo 377762 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B1285847 : Blo 377762 1285847 := bstep (se 1 (by rfl) ⟨964385, by rfl⟩ : syracuseStep 1285847 = 1928771) B1928771
theorem B3251933 : Blo 377762 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B7020269 : Blo 377762 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B1286063 : Blo 377762 1286063 := bstep (se 1 (by rfl) ⟨964547, by rfl⟩ : syracuseStep 1286063 = 1929095) B1929095
theorem B1154999 : Blo 377762 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B1875899 : Blo 377762 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B2892185 : Blo 377762 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B1221065 : Blo 377762 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B3482135 : Blo 377762 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B2433721 : Blo 377762 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B566711 : Blo 377762 566711 := bstep (se 1 (by rfl) ⟨425033, by rfl⟩ : syracuseStep 566711 = 850067) B850067
theorem B566747 : Blo 377762 566747 := bstep (se 1 (by rfl) ⟨425060, by rfl⟩ : syracuseStep 566747 = 850121) B850121
theorem B5481989 : Blo 377762 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B48801379 : Blo 377762 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B14526053 : Blo 377762 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B1222283 : Blo 377762 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B2434951 : Blo 377762 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B567215 : Blo 377762 567215 := bstep (se 1 (by rfl) ⟨425411, by rfl⟩ : syracuseStep 567215 = 850823) B850823
theorem B567305 : Blo 377762 567305 := bstep (se 2 (by rfl) ⟨212739, by rfl⟩ : syracuseStep 567305 = 425479) B425479
theorem B567335 : Blo 377762 567335 := bstep (se 1 (by rfl) ⟨425501, by rfl⟩ : syracuseStep 567335 = 851003) B851003
theorem B960569 : Blo 377762 960569 := bstep (se 2 (by rfl) ⟨360213, by rfl⟩ : syracuseStep 960569 = 720427) B720427
theorem B403579 : Blo 377762 403579 := bstep (se 1 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 403579 = 605369) B605369
theorem B567419 : Blo 377762 567419 := bstep (se 1 (by rfl) ⟨425564, by rfl⟩ : syracuseStep 567419 = 851129) B851129
theorem B6564077 : Blo 377762 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B1288439 : Blo 377762 1288439 := bstep (se 1 (by rfl) ⟨966329, by rfl⟩ : syracuseStep 1288439 = 1932659) B1932659
theorem B567545 : Blo 377762 567545 := bstep (se 2 (by rfl) ⟨212829, by rfl⟩ : syracuseStep 567545 = 425659) B425659
theorem B2894129 : Blo 377762 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B567647 : Blo 377762 567647 := bstep (se 1 (by rfl) ⟨425735, by rfl⟩ : syracuseStep 567647 = 851471) B851471
theorem B567659 : Blo 377762 567659 := bstep (se 1 (by rfl) ⟨425744, by rfl⟩ : syracuseStep 567659 = 851489) B851489
theorem B567887 : Blo 377762 567887 := bstep (se 1 (by rfl) ⟨425915, by rfl⟩ : syracuseStep 567887 = 851831) B851831
theorem B568007 : Blo 377762 568007 := bstep (se 1 (by rfl) ⟨426005, by rfl⟩ : syracuseStep 568007 = 852011) B852011
theorem B568169 : Blo 377762 568169 := bstep (se 2 (by rfl) ⟨213063, by rfl⟩ : syracuseStep 568169 = 426127) B426127
theorem B404399 : Blo 377762 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B568247 : Blo 377762 568247 := bstep (se 1 (by rfl) ⟨426185, by rfl⟩ : syracuseStep 568247 = 852371) B852371
theorem B568283 : Blo 377762 568283 := bstep (se 1 (by rfl) ⟨426212, by rfl⟩ : syracuseStep 568283 = 852425) B852425
theorem B1027151 : Blo 377762 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B568751 : Blo 377762 568751 := bstep (se 1 (by rfl) ⟨426563, by rfl⟩ : syracuseStep 568751 = 853127) B853127
theorem B568841 : Blo 377762 568841 := bstep (se 2 (by rfl) ⟨213315, by rfl⟩ : syracuseStep 568841 = 426631) B426631
theorem B962057 : Blo 377762 962057 := bstep (se 2 (by rfl) ⟨360771, by rfl⟩ : syracuseStep 962057 = 721543) B721543
theorem B568871 : Blo 377762 568871 := bstep (se 1 (by rfl) ⟨426653, by rfl⟩ : syracuseStep 568871 = 853307) B853307
theorem B7319159 : Blo 377762 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B568955 : Blo 377762 568955 := bstep (se 1 (by rfl) ⟨426716, by rfl⟩ : syracuseStep 568955 = 853433) B853433
theorem B1027723 : Blo 377762 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B2436797 : Blo 377762 2436797 := bstep (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) B913799
theorem B2731769 : Blo 377762 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B569081 : Blo 377762 569081 := bstep (se 2 (by rfl) ⟨213405, by rfl⟩ : syracuseStep 569081 = 426811) B426811
theorem B569183 : Blo 377762 569183 := bstep (se 1 (by rfl) ⟨426887, by rfl⟩ : syracuseStep 569183 = 853775) B853775
theorem B569195 : Blo 377762 569195 := bstep (se 1 (by rfl) ⟨426896, by rfl⟩ : syracuseStep 569195 = 853793) B853793
theorem B5451781 : Blo 377762 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B569423 : Blo 377762 569423 := bstep (se 1 (by rfl) ⟨427067, by rfl⟩ : syracuseStep 569423 = 854135) B854135
theorem B569543 : Blo 377762 569543 := bstep (se 1 (by rfl) ⟨427157, by rfl⟩ : syracuseStep 569543 = 854315) B854315
theorem B569705 : Blo 377762 569705 := bstep (se 2 (by rfl) ⟨213639, by rfl⟩ : syracuseStep 569705 = 427279) B427279
theorem B733583 : Blo 377762 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B569783 : Blo 377762 569783 := bstep (se 1 (by rfl) ⟨427337, by rfl⟩ : syracuseStep 569783 = 854675) B854675
theorem B569819 : Blo 377762 569819 := bstep (se 1 (by rfl) ⟨427364, by rfl⟩ : syracuseStep 569819 = 854729) B854729
theorem B3944983 : Blo 377762 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B963211 : Blo 377762 963211 := bstep (se 1 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 963211 = 1444817) B1444817
theorem B570287 : Blo 377762 570287 := bstep (se 1 (by rfl) ⟨427715, by rfl⟩ : syracuseStep 570287 = 855431) B855431
theorem B1946551 : Blo 377762 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B963515 : Blo 377762 963515 := bstep (se 1 (by rfl) ⟨722636, by rfl⟩ : syracuseStep 963515 = 1445273) B1445273
theorem B570377 : Blo 377762 570377 := bstep (se 2 (by rfl) ⟨213891, by rfl⟩ : syracuseStep 570377 = 427783) B427783
theorem B570407 : Blo 377762 570407 := bstep (se 1 (by rfl) ⟨427805, by rfl⟩ : syracuseStep 570407 = 855611) B855611
theorem B570491 : Blo 377762 570491 := bstep (se 1 (by rfl) ⟨427868, by rfl⟩ : syracuseStep 570491 = 855737) B855737
theorem B570617 : Blo 377762 570617 := bstep (se 2 (by rfl) ⟨213981, by rfl⟩ : syracuseStep 570617 = 427963) B427963
theorem B2438437 : Blo 377762 2438437 := bstep (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) B457207
theorem B570719 : Blo 377762 570719 := bstep (se 1 (by rfl) ⟨428039, by rfl⟩ : syracuseStep 570719 = 856079) B856079
theorem B570731 : Blo 377762 570731 := bstep (se 1 (by rfl) ⟨428048, by rfl⟩ : syracuseStep 570731 = 856097) B856097
theorem B2602405 : Blo 377762 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B570959 : Blo 377762 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B1029755 : Blo 377762 1029755 := bstep (se 1 (by rfl) ⟨772316, by rfl⟩ : syracuseStep 1029755 = 1544633) B1544633
theorem B2897531 : Blo 377762 2897531 := bstep (se 1 (by rfl) ⟨2173148, by rfl⟩ : syracuseStep 2897531 = 4346297) B4346297
theorem B1914515 : Blo 377762 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B15513281 : Blo 377762 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B571079 : Blo 377762 571079 := bstep (se 1 (by rfl) ⟨428309, by rfl⟩ : syracuseStep 571079 = 856619) B856619
theorem B964295 : Blo 377762 964295 := bstep (se 1 (by rfl) ⟨723221, by rfl⟩ : syracuseStep 964295 = 1446443) B1446443
theorem B964345 : Blo 377762 964345 := bstep (se 2 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 964345 = 723259) B723259
theorem B571241 : Blo 377762 571241 := bstep (se 2 (by rfl) ⟨214215, by rfl⟩ : syracuseStep 571241 = 428431) B428431
theorem B571319 : Blo 377762 571319 := bstep (se 1 (by rfl) ⟨428489, by rfl⟩ : syracuseStep 571319 = 856979) B856979
theorem B3880909 : Blo 377762 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B571355 : Blo 377762 571355 := bstep (se 1 (by rfl) ⟨428516, by rfl⟩ : syracuseStep 571355 = 857033) B857033
theorem B538663 : Blo 377762 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B964993 : Blo 377762 964993 := bstep (se 2 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 964993 = 723745) B723745
theorem B571823 : Blo 377762 571823 := bstep (se 1 (by rfl) ⟨428867, by rfl⟩ : syracuseStep 571823 = 857735) B857735
theorem B571913 : Blo 377762 571913 := bstep (se 2 (by rfl) ⟨214467, by rfl⟩ : syracuseStep 571913 = 428935) B428935
theorem B571943 : Blo 377762 571943 := bstep (se 1 (by rfl) ⟨428957, by rfl⟩ : syracuseStep 571943 = 857915) B857915
theorem B572027 : Blo 377762 572027 := bstep (se 1 (by rfl) ⟨429020, by rfl⟩ : syracuseStep 572027 = 858041) B858041
theorem B539335 : Blo 377762 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B572153 : Blo 377762 572153 := bstep (se 2 (by rfl) ⟨214557, by rfl⟩ : syracuseStep 572153 = 429115) B429115
theorem B572255 : Blo 377762 572255 := bstep (se 1 (by rfl) ⟨429191, by rfl⟩ : syracuseStep 572255 = 858383) B858383
theorem B572267 : Blo 377762 572267 := bstep (se 1 (by rfl) ⟨429200, by rfl⟩ : syracuseStep 572267 = 858401) B858401
theorem B768943 : Blo 377762 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B637915 : Blo 377762 637915 := bstep (se 1 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 637915 = 956873) B956873
theorem B572495 : Blo 377762 572495 := bstep (se 1 (by rfl) ⟨429371, by rfl⟩ : syracuseStep 572495 = 858743) B858743
theorem B965803 : Blo 377762 965803 := bstep (se 1 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 965803 = 1448705) B1448705
theorem B572615 : Blo 377762 572615 := bstep (se 1 (by rfl) ⟨429461, by rfl⟩ : syracuseStep 572615 = 858923) B858923
theorem B867689 : Blo 377762 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B966107 : Blo 377762 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B638543 : Blo 377762 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B1949507 : Blo 377762 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B606047 : Blo 377762 606047 := bstep (se 1 (by rfl) ⟨454535, by rfl⟩ : syracuseStep 606047 = 909071) B909071
theorem B540599 : Blo 377762 540599 := bstep (se 1 (by rfl) ⟨405449, by rfl⟩ : syracuseStep 540599 = 810899) B810899
theorem B4341923 : Blo 377762 4341923 := bstep (se 1 (by rfl) ⟨3256442, by rfl⟩ : syracuseStep 4341923 = 6512885) B6512885
theorem B606457 : Blo 377762 606457 := bstep (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) B454843
theorem B639407 : Blo 377762 639407 := bstep (se 1 (by rfl) ⟨479555, by rfl⟩ : syracuseStep 639407 = 959111) B959111
theorem B639839 : Blo 377762 639839 := bstep (se 1 (by rfl) ⟨479879, by rfl⟩ : syracuseStep 639839 = 959759) B959759
theorem B1622891 : Blo 377762 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B377775 : Blo 377762 377775 := bstep (se 1 (by rfl) ⟨283331, by rfl⟩ : syracuseStep 377775 = 566663) B566663
theorem B1295291 : Blo 377762 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B377799 : Blo 377762 377799 := bstep (se 1 (by rfl) ⟨283349, by rfl⟩ : syracuseStep 377799 = 566699) B566699
theorem B377819 : Blo 377762 377819 := bstep (se 1 (by rfl) ⟨283364, by rfl⟩ : syracuseStep 377819 = 566729) B566729
theorem B377895 : Blo 377762 377895 := bstep (se 1 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 377895 = 566843) B566843
theorem B377935 : Blo 377762 377935 := bstep (se 1 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 377935 = 566903) B566903
theorem B377951 : Blo 377762 377951 := bstep (se 1 (by rfl) ⟨283463, by rfl⟩ : syracuseStep 377951 = 566927) B566927
theorem B3327095 : Blo 377762 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B377979 : Blo 377762 377979 := bstep (se 1 (by rfl) ⟨283484, by rfl⟩ : syracuseStep 377979 = 566969) B566969
theorem B378031 : Blo 377762 378031 := bstep (se 1 (by rfl) ⟨283523, by rfl⟩ : syracuseStep 378031 = 567047) B567047
theorem B378055 : Blo 377762 378055 := bstep (se 1 (by rfl) ⟨283541, by rfl⟩ : syracuseStep 378055 = 567083) B567083
theorem B5293259 : Blo 377762 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B378075 : Blo 377762 378075 := bstep (se 1 (by rfl) ⟨283556, by rfl⟩ : syracuseStep 378075 = 567113) B567113
theorem B378151 : Blo 377762 378151 := bstep (se 1 (by rfl) ⟨283613, by rfl⟩ : syracuseStep 378151 = 567227) B567227
theorem B378191 : Blo 377762 378191 := bstep (se 1 (by rfl) ⟨283643, by rfl⟩ : syracuseStep 378191 = 567287) B567287
theorem B378207 : Blo 377762 378207 := bstep (se 1 (by rfl) ⟨283655, by rfl⟩ : syracuseStep 378207 = 567311) B567311
theorem B542057 : Blo 377762 542057 := bstep (se 2 (by rfl) ⟨203271, by rfl⟩ : syracuseStep 542057 = 406543) B406543
theorem B378235 : Blo 377762 378235 := bstep (se 1 (by rfl) ⟨283676, by rfl⟩ : syracuseStep 378235 = 567353) B567353
theorem B640399 : Blo 377762 640399 := bstep (se 1 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 640399 = 960599) B960599
theorem B378287 : Blo 377762 378287 := bstep (se 1 (by rfl) ⟨283715, by rfl⟩ : syracuseStep 378287 = 567431) B567431
theorem B607675 : Blo 377762 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B378311 : Blo 377762 378311 := bstep (se 1 (by rfl) ⟨283733, by rfl⟩ : syracuseStep 378311 = 567467) B567467
theorem B378331 : Blo 377762 378331 := bstep (se 1 (by rfl) ⟨283748, by rfl⟩ : syracuseStep 378331 = 567497) B567497
theorem B542171 : Blo 377762 542171 := bstep (se 1 (by rfl) ⟨406628, by rfl⟩ : syracuseStep 542171 = 813257) B813257
theorem B378407 : Blo 377762 378407 := bstep (se 1 (by rfl) ⟨283805, by rfl⟩ : syracuseStep 378407 = 567611) B567611
theorem B378447 : Blo 377762 378447 := bstep (se 1 (by rfl) ⟨283835, by rfl⟩ : syracuseStep 378447 = 567671) B567671
theorem B378463 : Blo 377762 378463 := bstep (se 1 (by rfl) ⟨283847, by rfl⟩ : syracuseStep 378463 = 567695) B567695
theorem B378491 : Blo 377762 378491 := bstep (se 1 (by rfl) ⟨283868, by rfl⟩ : syracuseStep 378491 = 567737) B567737
theorem B378543 : Blo 377762 378543 := bstep (se 1 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 378543 = 567815) B567815
theorem B378567 : Blo 377762 378567 := bstep (se 1 (by rfl) ⟨283925, by rfl⟩ : syracuseStep 378567 = 567851) B567851
theorem B378587 : Blo 377762 378587 := bstep (se 1 (by rfl) ⟨283940, by rfl⟩ : syracuseStep 378587 = 567881) B567881
theorem B1296157 : Blo 377762 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B378663 : Blo 377762 378663 := bstep (se 1 (by rfl) ⟨283997, by rfl⟩ : syracuseStep 378663 = 567995) B567995
theorem B378703 : Blo 377762 378703 := bstep (se 1 (by rfl) ⟨284027, by rfl⟩ : syracuseStep 378703 = 568055) B568055
theorem B378719 : Blo 377762 378719 := bstep (se 1 (by rfl) ⟨284039, by rfl⟩ : syracuseStep 378719 = 568079) B568079
theorem B378747 : Blo 377762 378747 := bstep (se 1 (by rfl) ⟨284060, by rfl⟩ : syracuseStep 378747 = 568121) B568121
theorem B378799 : Blo 377762 378799 := bstep (se 1 (by rfl) ⟨284099, by rfl⟩ : syracuseStep 378799 = 568199) B568199
theorem B378823 : Blo 377762 378823 := bstep (se 1 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 378823 = 568235) B568235
theorem B378843 : Blo 377762 378843 := bstep (se 1 (by rfl) ⟨284132, by rfl⟩ : syracuseStep 378843 = 568265) B568265
theorem B378919 : Blo 377762 378919 := bstep (se 1 (by rfl) ⟨284189, by rfl⟩ : syracuseStep 378919 = 568379) B568379
theorem B641081 : Blo 377762 641081 := bstep (se 2 (by rfl) ⟨240405, by rfl⟩ : syracuseStep 641081 = 480811) B480811
theorem B1624121 : Blo 377762 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B378959 : Blo 377762 378959 := bstep (se 1 (by rfl) ⟨284219, by rfl⟩ : syracuseStep 378959 = 568439) B568439
theorem B378975 : Blo 377762 378975 := bstep (se 1 (by rfl) ⟨284231, by rfl⟩ : syracuseStep 378975 = 568463) B568463
theorem B379003 : Blo 377762 379003 := bstep (se 1 (by rfl) ⟨284252, by rfl⟩ : syracuseStep 379003 = 568505) B568505
theorem B12372101 : Blo 377762 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B379055 : Blo 377762 379055 := bstep (se 1 (by rfl) ⟨284291, by rfl⟩ : syracuseStep 379055 = 568583) B568583
theorem B379079 : Blo 377762 379079 := bstep (se 1 (by rfl) ⟨284309, by rfl⟩ : syracuseStep 379079 = 568619) B568619
theorem B379099 : Blo 377762 379099 := bstep (se 1 (by rfl) ⟨284324, by rfl⟩ : syracuseStep 379099 = 568649) B568649
theorem B379175 : Blo 377762 379175 := bstep (se 1 (by rfl) ⟨284381, by rfl⟩ : syracuseStep 379175 = 568763) B568763
theorem B379215 : Blo 377762 379215 := bstep (se 1 (by rfl) ⟨284411, by rfl⟩ : syracuseStep 379215 = 568823) B568823
theorem B379231 : Blo 377762 379231 := bstep (se 1 (by rfl) ⟨284423, by rfl⟩ : syracuseStep 379231 = 568847) B568847
theorem B543071 : Blo 377762 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B379259 : Blo 377762 379259 := bstep (se 1 (by rfl) ⟨284444, by rfl⟩ : syracuseStep 379259 = 568889) B568889
theorem B379311 : Blo 377762 379311 := bstep (se 1 (by rfl) ⟨284483, by rfl⟩ : syracuseStep 379311 = 568967) B568967
theorem B379335 : Blo 377762 379335 := bstep (se 1 (by rfl) ⟨284501, by rfl⟩ : syracuseStep 379335 = 569003) B569003
theorem B1362395 : Blo 377762 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B379355 : Blo 377762 379355 := bstep (se 1 (by rfl) ⟨284516, by rfl⟩ : syracuseStep 379355 = 569033) B569033
theorem B1821217 : Blo 377762 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B379431 : Blo 377762 379431 := bstep (se 1 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 379431 = 569147) B569147
theorem B379471 : Blo 377762 379471 := bstep (se 1 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 379471 = 569207) B569207
theorem B379487 : Blo 377762 379487 := bstep (se 1 (by rfl) ⟨284615, by rfl⟩ : syracuseStep 379487 = 569231) B569231
theorem B379515 : Blo 377762 379515 := bstep (se 1 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 379515 = 569273) B569273
theorem B379567 : Blo 377762 379567 := bstep (se 1 (by rfl) ⟨284675, by rfl⟩ : syracuseStep 379567 = 569351) B569351
theorem B1100477 : Blo 377762 1100477 := bstep (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) B412679
theorem B379591 : Blo 377762 379591 := bstep (se 1 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 379591 = 569387) B569387
theorem B1919699 : Blo 377762 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B379611 : Blo 377762 379611 := bstep (se 1 (by rfl) ⟨284708, by rfl⟩ : syracuseStep 379611 = 569417) B569417
theorem B641783 : Blo 377762 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B379687 : Blo 377762 379687 := bstep (se 1 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 379687 = 569531) B569531
theorem B379727 : Blo 377762 379727 := bstep (se 1 (by rfl) ⟨284795, by rfl⟩ : syracuseStep 379727 = 569591) B569591
theorem B379743 : Blo 377762 379743 := bstep (se 1 (by rfl) ⟨284807, by rfl⟩ : syracuseStep 379743 = 569615) B569615
theorem B379771 : Blo 377762 379771 := bstep (se 1 (by rfl) ⟨284828, by rfl⟩ : syracuseStep 379771 = 569657) B569657
theorem B379823 : Blo 377762 379823 := bstep (se 1 (by rfl) ⟨284867, by rfl⟩ : syracuseStep 379823 = 569735) B569735
theorem B576439 : Blo 377762 576439 := bstep (se 1 (by rfl) ⟨432329, by rfl⟩ : syracuseStep 576439 = 864659) B864659
theorem B379847 : Blo 377762 379847 := bstep (se 1 (by rfl) ⟨284885, by rfl⟩ : syracuseStep 379847 = 569771) B569771
theorem B379867 : Blo 377762 379867 := bstep (se 1 (by rfl) ⟨284900, by rfl⟩ : syracuseStep 379867 = 569801) B569801
theorem B379943 : Blo 377762 379943 := bstep (se 1 (by rfl) ⟨284957, by rfl⟩ : syracuseStep 379943 = 569915) B569915
theorem B2870315 : Blo 377762 2870315 := bstep (se 1 (by rfl) ⟨2152736, by rfl⟩ : syracuseStep 2870315 = 4305473) B4305473
theorem B379983 : Blo 377762 379983 := bstep (se 1 (by rfl) ⟨284987, by rfl⟩ : syracuseStep 379983 = 569975) B569975
theorem B642127 : Blo 377762 642127 := bstep (se 1 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 642127 = 963191) B963191
theorem B379999 : Blo 377762 379999 := bstep (se 1 (by rfl) ⟨284999, by rfl⟩ : syracuseStep 379999 = 569999) B569999
theorem B380027 : Blo 377762 380027 := bstep (se 1 (by rfl) ⟨285020, by rfl⟩ : syracuseStep 380027 = 570041) B570041
theorem B380079 : Blo 377762 380079 := bstep (se 1 (by rfl) ⟨285059, by rfl⟩ : syracuseStep 380079 = 570119) B570119
theorem B380103 : Blo 377762 380103 := bstep (se 1 (by rfl) ⟨285077, by rfl⟩ : syracuseStep 380103 = 570155) B570155
theorem B380123 : Blo 377762 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B380199 : Blo 377762 380199 := bstep (se 1 (by rfl) ⟨285149, by rfl⟩ : syracuseStep 380199 = 570299) B570299
theorem B642377 : Blo 377762 642377 := bstep (se 2 (by rfl) ⟨240891, by rfl⟩ : syracuseStep 642377 = 481783) B481783
theorem B380239 : Blo 377762 380239 := bstep (se 1 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 380239 = 570359) B570359
theorem B380255 : Blo 377762 380255 := bstep (se 1 (by rfl) ⟨285191, by rfl⟩ : syracuseStep 380255 = 570383) B570383
theorem B380283 : Blo 377762 380283 := bstep (se 1 (by rfl) ⟨285212, by rfl⟩ : syracuseStep 380283 = 570425) B570425
theorem B478639 : Blo 377762 478639 := bstep (se 1 (by rfl) ⟨358979, by rfl⟩ : syracuseStep 478639 = 717959) B717959
theorem B380335 : Blo 377762 380335 := bstep (se 1 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 380335 = 570503) B570503
theorem B380359 : Blo 377762 380359 := bstep (se 1 (by rfl) ⟨285269, by rfl⟩ : syracuseStep 380359 = 570539) B570539
theorem B380379 : Blo 377762 380379 := bstep (se 1 (by rfl) ⟨285284, by rfl⟩ : syracuseStep 380379 = 570569) B570569
theorem B413147 : Blo 377762 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B380455 : Blo 377762 380455 := bstep (se 1 (by rfl) ⟨285341, by rfl⟩ : syracuseStep 380455 = 570683) B570683
theorem B380495 : Blo 377762 380495 := bstep (se 1 (by rfl) ⟨285371, by rfl⟩ : syracuseStep 380495 = 570743) B570743
theorem B380511 : Blo 377762 380511 := bstep (se 1 (by rfl) ⟨285383, by rfl⟩ : syracuseStep 380511 = 570767) B570767
theorem B380539 : Blo 377762 380539 := bstep (se 1 (by rfl) ⟨285404, by rfl⟩ : syracuseStep 380539 = 570809) B570809
theorem B2051723 : Blo 377762 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B380591 : Blo 377762 380591 := bstep (se 1 (by rfl) ⟨285443, by rfl⟩ : syracuseStep 380591 = 570887) B570887
theorem B380615 : Blo 377762 380615 := bstep (se 1 (by rfl) ⟨285461, by rfl⟩ : syracuseStep 380615 = 570923) B570923
theorem B380635 : Blo 377762 380635 := bstep (se 1 (by rfl) ⟨285476, by rfl⟩ : syracuseStep 380635 = 570953) B570953
theorem B642809 : Blo 377762 642809 := bstep (se 2 (by rfl) ⟨241053, by rfl⟩ : syracuseStep 642809 = 482107) B482107
theorem B380711 : Blo 377762 380711 := bstep (se 1 (by rfl) ⟨285533, by rfl⟩ : syracuseStep 380711 = 571067) B571067
theorem B380751 : Blo 377762 380751 := bstep (se 1 (by rfl) ⟨285563, by rfl⟩ : syracuseStep 380751 = 571127) B571127
theorem B380767 : Blo 377762 380767 := bstep (se 1 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 380767 = 571151) B571151
theorem B380795 : Blo 377762 380795 := bstep (se 1 (by rfl) ⟨285596, by rfl⟩ : syracuseStep 380795 = 571193) B571193
theorem B380847 : Blo 377762 380847 := bstep (se 1 (by rfl) ⟨285635, by rfl⟩ : syracuseStep 380847 = 571271) B571271
theorem B642991 : Blo 377762 642991 := bstep (se 1 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 642991 = 964487) B964487
theorem B380871 : Blo 377762 380871 := bstep (se 1 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 380871 = 571307) B571307
theorem B380891 : Blo 377762 380891 := bstep (se 1 (by rfl) ⟨285668, by rfl⟩ : syracuseStep 380891 = 571337) B571337
theorem B1855495 : Blo 377762 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B643079 : Blo 377762 643079 := bstep (se 1 (by rfl) ⟨482309, by rfl⟩ : syracuseStep 643079 = 964619) B964619
theorem B4673551 : Blo 377762 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B380967 : Blo 377762 380967 := bstep (se 1 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 380967 = 571451) B571451
theorem B806969 : Blo 377762 806969 := bstep (se 2 (by rfl) ⟨302613, by rfl⟩ : syracuseStep 806969 = 605227) B605227
theorem B381007 : Blo 377762 381007 := bstep (se 1 (by rfl) ⟨285755, by rfl⟩ : syracuseStep 381007 = 571511) B571511
theorem B381023 : Blo 377762 381023 := bstep (se 1 (by rfl) ⟨285767, by rfl⟩ : syracuseStep 381023 = 571535) B571535
theorem B381051 : Blo 377762 381051 := bstep (se 1 (by rfl) ⟨285788, by rfl⟩ : syracuseStep 381051 = 571577) B571577
theorem B381103 : Blo 377762 381103 := bstep (se 1 (by rfl) ⟨285827, by rfl⟩ : syracuseStep 381103 = 571655) B571655
theorem B381127 : Blo 377762 381127 := bstep (se 1 (by rfl) ⟨285845, by rfl⟩ : syracuseStep 381127 = 571691) B571691
theorem B381147 : Blo 377762 381147 := bstep (se 1 (by rfl) ⟨285860, by rfl⟩ : syracuseStep 381147 = 571721) B571721
theorem B381223 : Blo 377762 381223 := bstep (se 1 (by rfl) ⟨285917, by rfl⟩ : syracuseStep 381223 = 571835) B571835
theorem B381263 : Blo 377762 381263 := bstep (se 1 (by rfl) ⟨285947, by rfl⟩ : syracuseStep 381263 = 571895) B571895
theorem B381279 : Blo 377762 381279 := bstep (se 1 (by rfl) ⟨285959, by rfl⟩ : syracuseStep 381279 = 571919) B571919
theorem B643423 : Blo 377762 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B381307 : Blo 377762 381307 := bstep (se 1 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 381307 = 571961) B571961
theorem B381359 : Blo 377762 381359 := bstep (se 1 (by rfl) ⟨286019, by rfl⟩ : syracuseStep 381359 = 572039) B572039
theorem B643511 : Blo 377762 643511 := bstep (se 1 (by rfl) ⟨482633, by rfl⟩ : syracuseStep 643511 = 965267) B965267
theorem B381383 : Blo 377762 381383 := bstep (se 1 (by rfl) ⟨286037, by rfl⟩ : syracuseStep 381383 = 572075) B572075
theorem B381403 : Blo 377762 381403 := bstep (se 1 (by rfl) ⟨286052, by rfl⟩ : syracuseStep 381403 = 572105) B572105
theorem B479783 : Blo 377762 479783 := bstep (se 1 (by rfl) ⟨359837, by rfl⟩ : syracuseStep 479783 = 719675) B719675
theorem B381479 : Blo 377762 381479 := bstep (se 1 (by rfl) ⟨286109, by rfl⟩ : syracuseStep 381479 = 572219) B572219
theorem B381519 : Blo 377762 381519 := bstep (se 1 (by rfl) ⟨286139, by rfl⟩ : syracuseStep 381519 = 572279) B572279
theorem B381535 : Blo 377762 381535 := bstep (se 1 (by rfl) ⟨286151, by rfl⟩ : syracuseStep 381535 = 572303) B572303
theorem B381563 : Blo 377762 381563 := bstep (se 1 (by rfl) ⟨286172, by rfl⟩ : syracuseStep 381563 = 572345) B572345
theorem B381615 : Blo 377762 381615 := bstep (se 1 (by rfl) ⟨286211, by rfl⟩ : syracuseStep 381615 = 572423) B572423
theorem B381639 : Blo 377762 381639 := bstep (se 1 (by rfl) ⟨286229, by rfl⟩ : syracuseStep 381639 = 572459) B572459
theorem B1233623 : Blo 377762 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B381659 : Blo 377762 381659 := bstep (se 1 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 381659 = 572489) B572489
theorem B381735 : Blo 377762 381735 := bstep (se 1 (by rfl) ⟨286301, by rfl⟩ : syracuseStep 381735 = 572603) B572603
theorem B480107 : Blo 377762 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B1921967 : Blo 377762 1921967 := bstep (se 1 (by rfl) ⟨1441475, by rfl⟩ : syracuseStep 1921967 = 2882951) B2882951
theorem B644105 : Blo 377762 644105 := bstep (se 2 (by rfl) ⟨241539, by rfl⟩ : syracuseStep 644105 = 483079) B483079
theorem B4871339 : Blo 377762 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B3888499 : Blo 377762 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B546383 : Blo 377762 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B1824353 : Blo 377762 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B3233479 : Blo 377762 3233479 := bstep (se 1 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 3233479 = 4850219) B4850219
theorem B1627847 : Blo 377762 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B2741975 : Blo 377762 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B481403 : Blo 377762 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B3889457 : Blo 377762 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B5200823 : Blo 377762 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B119922061 : Blo 377762 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B1564525 : Blo 377762 1564525 := bstep (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) B586697
theorem B647291 : Blo 377762 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B15622307 : Blo 377762 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B1368539 : Blo 377762 1368539 := bstep (se 1 (by rfl) ⟨1026404, by rfl⟩ : syracuseStep 1368539 = 2052809) B2052809
theorem B909947 : Blo 377762 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B1303559 : Blo 377762 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B2909303 : Blo 377762 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B3302819 : Blo 377762 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B8775179 : Blo 377762 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1566233 : Blo 377762 1566233 := bstep (se 2 (by rfl) ⟨587337, by rfl⟩ : syracuseStep 1566233 = 1174675) B1174675
theorem B1468043 : Blo 377762 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B1730413 : Blo 377762 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B1435553 : Blo 377762 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B911531 : Blo 377762 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B4123169 : Blo 377762 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B1436525 : Blo 377762 1436525 := bstep (se 3 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 1436525 = 538697) B538697
theorem B1830059 : Blo 377762 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B748873 : Blo 377762 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B1076723 : Blo 377762 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1437209 : Blo 377762 1437209 := bstep (se 2 (by rfl) ⟨538953, by rfl⟩ : syracuseStep 1437209 = 1077907) B1077907
theorem B4845095 : Blo 377762 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437223 : Blo 377762 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B2879063 : Blo 377762 2879063 := bstep (se 1 (by rfl) ⟨2159297, by rfl⟩ : syracuseStep 2879063 = 4318595) B4318595
theorem B10907459 : Blo 377762 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B2420599 : Blo 377762 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B9891733 : Blo 377762 9891733 := bstep (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) B463675
theorem B683959 : Blo 377762 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B6582349 : Blo 377762 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B553159 : Blo 377762 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B5501195 : Blo 377762 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B1438013 : Blo 377762 1438013 := bstep (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) B539255
theorem B717275 : Blo 377762 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B1438195 : Blo 377762 1438195 := bstep (se 1 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 1438195 = 2157293) B2157293
theorem B717511 : Blo 377762 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B1110743 : Blo 377762 1110743 := bstep (se 1 (by rfl) ⟨833057, by rfl⟩ : syracuseStep 1110743 = 1666115) B1666115
theorem B1078123 : Blo 377762 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B685019 : Blo 377762 685019 := bstep (se 1 (by rfl) ⟨513764, by rfl⟩ : syracuseStep 685019 = 1027529) B1027529
theorem B1930715 : Blo 377762 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B1275425 : Blo 377762 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B1373755 : Blo 377762 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B1439441 : Blo 377762 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B1275641 : Blo 377762 1275641 := bstep (se 2 (by rfl) ⟨478365, by rfl⟩ : syracuseStep 1275641 = 956731) B956731
theorem B2586401 : Blo 377762 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B1931201 : Blo 377762 1931201 := bstep (se 2 (by rfl) ⟨724200, by rfl⟩ : syracuseStep 1931201 = 1448401) B1448401
theorem B6944717 : Blo 377762 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B1275911 : Blo 377762 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B849977 : Blo 377762 849977 := bstep (se 2 (by rfl) ⟨318741, by rfl⟩ : syracuseStep 849977 = 637483) B637483
theorem B1276019 : Blo 377762 1276019 := bstep (se 1 (by rfl) ⟨957014, by rfl⟩ : syracuseStep 1276019 = 1914029) B1914029
theorem B1440125 : Blo 377762 1440125 := bstep (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) B540047
theorem B1276289 : Blo 377762 1276289 := bstep (se 2 (by rfl) ⟨478608, by rfl⟩ : syracuseStep 1276289 = 957217) B957217
theorem B850319 : Blo 377762 850319 := bstep (se 1 (by rfl) ⟨637739, by rfl⟩ : syracuseStep 850319 = 1275479) B1275479
theorem B719417 : Blo 377762 719417 := bstep (se 2 (by rfl) ⟨269781, by rfl⟩ : syracuseStep 719417 = 539563) B539563
theorem B850643 : Blo 377762 850643 := bstep (se 1 (by rfl) ⟨637982, by rfl⟩ : syracuseStep 850643 = 1275965) B1275965
theorem B719759 : Blo 377762 719759 := bstep (se 1 (by rfl) ⟨539819, by rfl⟩ : syracuseStep 719759 = 1079639) B1079639
theorem B6224881 : Blo 377762 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B916559 : Blo 377762 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B425083 : Blo 377762 425083 := bstep (se 1 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 425083 = 637625) B637625
theorem B1277099 : Blo 377762 1277099 := bstep (se 1 (by rfl) ⟨957824, by rfl⟩ : syracuseStep 1277099 = 1915649) B1915649
theorem B1375427 : Blo 377762 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B1211735 : Blo 377762 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B1441111 : Blo 377762 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B687455 : Blo 377762 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B1080857 : Blo 377762 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B425551 : Blo 377762 425551 := bstep (se 1 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 425551 = 638327) B638327
theorem B851579 : Blo 377762 851579 := bstep (se 1 (by rfl) ⟨638684, by rfl⟩ : syracuseStep 851579 = 1277369) B1277369
theorem B1441415 : Blo 377762 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B1212043 : Blo 377762 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1080971 : Blo 377762 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1539769 : Blo 377762 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B1277639 : Blo 377762 1277639 := bstep (se 1 (by rfl) ⟨958229, by rfl⟩ : syracuseStep 1277639 = 1916459) B1916459
theorem B2162375 : Blo 377762 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B851705 : Blo 377762 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B2883437 : Blo 377762 2883437 := bstep (se 3 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 2883437 = 1081289) B1081289
theorem B425947 : Blo 377762 425947 := bstep (se 1 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 425947 = 638921) B638921
theorem B426271 : Blo 377762 426271 := bstep (se 1 (by rfl) ⟨319703, by rfl⟩ : syracuseStep 426271 = 639407) B639407
theorem B852335 : Blo 377762 852335 := bstep (se 1 (by rfl) ⟨639251, by rfl⟩ : syracuseStep 852335 = 1278503) B1278503
theorem B852407 : Blo 377762 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B426559 : Blo 377762 426559 := bstep (se 1 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 426559 = 639839) B639839
theorem B852551 : Blo 377762 852551 := bstep (se 1 (by rfl) ⟨639413, by rfl⟩ : syracuseStep 852551 = 1278827) B1278827
theorem B1081927 : Blo 377762 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B852587 : Blo 377762 852587 := bstep (se 1 (by rfl) ⟨639440, by rfl⟩ : syracuseStep 852587 = 1278881) B1278881
theorem B3244961 : Blo 377762 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B852983 : Blo 377762 852983 := bstep (se 1 (by rfl) ⟨639737, by rfl⟩ : syracuseStep 852983 = 1279475) B1279475
theorem B2950181 : Blo 377762 2950181 := bstep (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) B553159
theorem B853343 : Blo 377762 853343 := bstep (se 1 (by rfl) ⟨640007, by rfl⟩ : syracuseStep 853343 = 1280015) B1280015
theorem B427387 : Blo 377762 427387 := bstep (se 1 (by rfl) ⟨320540, by rfl⟩ : syracuseStep 427387 = 641081) B641081
theorem B1082747 : Blo 377762 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B1279421 : Blo 377762 1279421 := bstep (se 3 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 1279421 = 479783) B479783
theorem B722515 : Blo 377762 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B853739 : Blo 377762 853739 := bstep (se 1 (by rfl) ⟨640304, by rfl⟩ : syracuseStep 853739 = 1280609) B1280609
theorem B1279799 : Blo 377762 1279799 := bstep (se 1 (by rfl) ⟨959849, by rfl⟩ : syracuseStep 1279799 = 1919699) B1919699
theorem B427855 : Blo 377762 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B853865 : Blo 377762 853865 := bstep (se 2 (by rfl) ⟨320199, by rfl⟩ : syracuseStep 853865 = 640399) B640399
theorem B428251 : Blo 377762 428251 := bstep (se 1 (by rfl) ⟨321188, by rfl⟩ : syracuseStep 428251 = 642377) B642377
theorem B1280285 : Blo 377762 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B428539 : Blo 377762 428539 := bstep (se 1 (by rfl) ⟨321404, by rfl⟩ : syracuseStep 428539 = 642809) B642809
theorem B1182203 : Blo 377762 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B3246601 : Blo 377762 3246601 := bstep (se 2 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 3246601 = 2434951) B2434951
theorem B723563 : Blo 377762 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B428719 : Blo 377762 428719 := bstep (se 1 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 428719 = 643079) B643079
theorem B854711 : Blo 377762 854711 := bstep (se 1 (by rfl) ⟨641033, by rfl⟩ : syracuseStep 854711 = 1282067) B1282067
theorem B723791 : Blo 377762 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B854927 : Blo 377762 854927 := bstep (se 1 (by rfl) ⟨641195, by rfl⟩ : syracuseStep 854927 = 1282391) B1282391
theorem B429007 : Blo 377762 429007 := bstep (se 1 (by rfl) ⟨321755, by rfl⟩ : syracuseStep 429007 = 643511) B643511
theorem B822415 : Blo 377762 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B1281311 : Blo 377762 1281311 := bstep (se 1 (by rfl) ⟨960983, by rfl⟩ : syracuseStep 1281311 = 1921967) B1921967
theorem B429403 : Blo 377762 429403 := bstep (se 1 (by rfl) ⟨322052, by rfl⟩ : syracuseStep 429403 = 644105) B644105
theorem B2428289 : Blo 377762 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B3247559 : Blo 377762 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B855647 : Blo 377762 855647 := bstep (se 1 (by rfl) ⟨641735, by rfl⟩ : syracuseStep 855647 = 1283471) B1283471
theorem B1445471 : Blo 377762 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B1445485 : Blo 377762 1445485 := bstep (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) B542057
theorem B1216235 : Blo 377762 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B1085231 : Blo 377762 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B855863 : Blo 377762 855863 := bstep (se 1 (by rfl) ⟨641897, by rfl⟩ : syracuseStep 855863 = 1283795) B1283795
theorem B1445789 : Blo 377762 1445789 := bstep (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) B542171
theorem B856169 : Blo 377762 856169 := bstep (se 2 (by rfl) ⟨321063, by rfl⟩ : syracuseStep 856169 = 642127) B642127
theorem B2592971 : Blo 377762 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B856655 : Blo 377762 856655 := bstep (se 1 (by rfl) ⟨642491, by rfl⟩ : syracuseStep 856655 = 1284983) B1284983
theorem B856799 : Blo 377762 856799 := bstep (se 1 (by rfl) ⟨642599, by rfl⟩ : syracuseStep 856799 = 1285199) B1285199
theorem B857051 : Blo 377762 857051 := bstep (se 1 (by rfl) ⟨642788, by rfl⟩ : syracuseStep 857051 = 1285577) B1285577
theorem B857231 : Blo 377762 857231 := bstep (se 1 (by rfl) ⟨642923, by rfl⟩ : syracuseStep 857231 = 1285847) B1285847
theorem B2167955 : Blo 377762 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B857321 : Blo 377762 857321 := bstep (se 2 (by rfl) ⟨321495, by rfl⟩ : syracuseStep 857321 = 642991) B642991
theorem B857375 : Blo 377762 857375 := bstep (se 1 (by rfl) ⟨643031, by rfl⟩ : syracuseStep 857375 = 1286063) B1286063
theorem B6231401 : Blo 377762 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B1283741 : Blo 377762 1283741 := bstep (se 3 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 1283741 = 481403) B481403
theorem B2430749 : Blo 377762 2430749 := bstep (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) B911531
theorem B857897 : Blo 377762 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B1939535 : Blo 377762 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B1284281 : Blo 377762 1284281 := bstep (se 2 (by rfl) ⟨481605, by rfl⟩ : syracuseStep 1284281 = 963211) B963211
theorem B1448189 : Blo 377762 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B956681 : Blo 377762 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B2201879 : Blo 377762 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B2595401 : Blo 377762 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B957035 : Blo 377762 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B858959 : Blo 377762 858959 := bstep (se 1 (by rfl) ⟨644219, by rfl⟩ : syracuseStep 858959 = 1288439) B1288439
theorem B3251249 : Blo 377762 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B5184665 : Blo 377762 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B957683 : Blo 377762 957683 := bstep (se 1 (by rfl) ⟨718262, by rfl⟩ : syracuseStep 957683 = 1436525) B1436525
theorem B1220039 : Blo 377762 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1285793 : Blo 377762 1285793 := bstep (se 2 (by rfl) ⟨482172, by rfl⟩ : syracuseStep 1285793 = 964345) B964345
theorem B958139 : Blo 377762 958139 := bstep (se 1 (by rfl) ⟨718604, by rfl⟩ : syracuseStep 958139 = 1437209) B1437209
theorem B958675 : Blo 377762 958675 := bstep (se 1 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 958675 = 1438013) B1438013
theorem B1286657 : Blo 377762 1286657 := bstep (se 2 (by rfl) ⟨482496, by rfl⟩ : syracuseStep 1286657 = 964993) B964993
theorem B1287143 : Blo 377762 1287143 := bstep (se 1 (by rfl) ⟨965357, by rfl⟩ : syracuseStep 1287143 = 1930715) B1930715
theorem B959627 : Blo 377762 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B12297365 : Blo 377762 12297365 := bstep (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) B576439
theorem B1025257 : Blo 377762 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B1287467 : Blo 377762 1287467 := bstep (se 1 (by rfl) ⟨965600, by rfl⟩ : syracuseStep 1287467 = 1931201) B1931201
theorem B4629811 : Blo 377762 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B8299841 : Blo 377762 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B566651 : Blo 377762 566651 := bstep (se 1 (by rfl) ⟨424988, by rfl⟩ : syracuseStep 566651 = 849977) B849977
theorem B566777 : Blo 377762 566777 := bstep (se 2 (by rfl) ⟨212541, by rfl⟩ : syracuseStep 566777 = 425083) B425083
theorem B1287737 : Blo 377762 1287737 := bstep (se 2 (by rfl) ⟨482901, by rfl⟩ : syracuseStep 1287737 = 965803) B965803
theorem B960083 : Blo 377762 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B2631257 : Blo 377762 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B566879 : Blo 377762 566879 := bstep (se 1 (by rfl) ⟨425159, by rfl⟩ : syracuseStep 566879 = 850319) B850319
theorem B567095 : Blo 377762 567095 := bstep (se 1 (by rfl) ⟨425321, by rfl⟩ : syracuseStep 567095 = 850643) B850643
theorem B567401 : Blo 377762 567401 := bstep (se 2 (by rfl) ⟨212775, by rfl⟩ : syracuseStep 567401 = 425551) B425551
theorem B1616057 : Blo 377762 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B1616125 : Blo 377762 1616125 := bstep (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) B606047
theorem B567719 : Blo 377762 567719 := bstep (se 1 (by rfl) ⟨425789, by rfl⟩ : syracuseStep 567719 = 851579) B851579
theorem B960943 : Blo 377762 960943 := bstep (se 1 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 960943 = 1441415) B1441415
theorem B567803 : Blo 377762 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B567929 : Blo 377762 567929 := bstep (se 2 (by rfl) ⟨212973, by rfl⟩ : syracuseStep 567929 = 425947) B425947
theorem B567983 : Blo 377762 567983 := bstep (se 1 (by rfl) ⟨425987, by rfl⟩ : syracuseStep 567983 = 851975) B851975
theorem B568031 : Blo 377762 568031 := bstep (se 1 (by rfl) ⟨426023, by rfl⟩ : syracuseStep 568031 = 852047) B852047
theorem B961247 : Blo 377762 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B2894615 : Blo 377762 2894615 := bstep (se 1 (by rfl) ⟨2170961, by rfl⟩ : syracuseStep 2894615 = 4341923) B4341923
theorem B568295 : Blo 377762 568295 := bstep (se 1 (by rfl) ⟨426221, by rfl⟩ : syracuseStep 568295 = 852443) B852443
theorem B35105861 : Blo 377762 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B5024987 : Blo 377762 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B568553 : Blo 377762 568553 := bstep (se 2 (by rfl) ⟨213207, by rfl⟩ : syracuseStep 568553 = 426415) B426415
theorem B568607 : Blo 377762 568607 := bstep (se 1 (by rfl) ⟨426455, by rfl⟩ : syracuseStep 568607 = 852911) B852911
theorem B16035191 : Blo 377762 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B961915 : Blo 377762 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B568775 : Blo 377762 568775 := bstep (se 1 (by rfl) ⟨426581, by rfl⟩ : syracuseStep 568775 = 853163) B853163
theorem B569129 : Blo 377762 569129 := bstep (se 2 (by rfl) ⟨213423, by rfl⟩ : syracuseStep 569129 = 426847) B426847
theorem B569135 : Blo 377762 569135 := bstep (se 1 (by rfl) ⟨426851, by rfl⟩ : syracuseStep 569135 = 853703) B853703
theorem B962351 : Blo 377762 962351 := bstep (se 1 (by rfl) ⟨721763, by rfl⟩ : syracuseStep 962351 = 1443527) B1443527
theorem B1912733 : Blo 377762 1912733 := bstep (se 3 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 1912733 = 717275) B717275
theorem B569609 : Blo 377762 569609 := bstep (se 2 (by rfl) ⟨213603, by rfl⟩ : syracuseStep 569609 = 427207) B427207
theorem B569711 : Blo 377762 569711 := bstep (se 1 (by rfl) ⟨427283, by rfl⟩ : syracuseStep 569711 = 854567) B854567
theorem B3649967 : Blo 377762 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B962999 : Blo 377762 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B569927 : Blo 377762 569927 := bstep (se 1 (by rfl) ⟨427445, by rfl⟩ : syracuseStep 569927 = 854891) B854891
theorem B569963 : Blo 377762 569963 := bstep (se 1 (by rfl) ⟨427472, by rfl⟩ : syracuseStep 569963 = 854945) B854945
theorem B1913543 : Blo 377762 1913543 := bstep (se 1 (by rfl) ⟨1435157, by rfl⟩ : syracuseStep 1913543 = 2870315) B2870315
theorem B570191 : Blo 377762 570191 := bstep (se 1 (by rfl) ⟨427643, by rfl⟩ : syracuseStep 570191 = 855287) B855287
theorem B2307217 : Blo 377762 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B3454109 : Blo 377762 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B570587 : Blo 377762 570587 := bstep (se 1 (by rfl) ⟨427940, by rfl⟩ : syracuseStep 570587 = 855881) B855881
theorem B570761 : Blo 377762 570761 := bstep (se 2 (by rfl) ⟨214035, by rfl⟩ : syracuseStep 570761 = 428071) B428071
theorem B964001 : Blo 377762 964001 := bstep (se 2 (by rfl) ⟨361500, by rfl⟩ : syracuseStep 964001 = 723001) B723001
theorem B538105 : Blo 377762 538105 := bstep (se 2 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 538105 = 403579) B403579
theorem B571115 : Blo 377762 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B767791 : Blo 377762 767791 := bstep (se 1 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 767791 = 1151687) B1151687
theorem B964457 : Blo 377762 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B571343 : Blo 377762 571343 := bstep (se 1 (by rfl) ⟨428507, by rfl⟩ : syracuseStep 571343 = 857015) B857015
theorem B4110365 : Blo 377762 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B571739 : Blo 377762 571739 := bstep (se 1 (by rfl) ⟨428804, by rfl⟩ : syracuseStep 571739 = 857609) B857609
theorem B571967 : Blo 377762 571967 := bstep (se 1 (by rfl) ⟨428975, by rfl⟩ : syracuseStep 571967 = 857951) B857951
theorem B572087 : Blo 377762 572087 := bstep (se 1 (by rfl) ⟨429065, by rfl⟩ : syracuseStep 572087 = 858131) B858131
theorem B1457021 : Blo 377762 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B572315 : Blo 377762 572315 := bstep (se 1 (by rfl) ⟨429236, by rfl⟩ : syracuseStep 572315 = 858473) B858473
theorem B998497 : Blo 377762 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B638185 : Blo 377762 638185 := bstep (se 2 (by rfl) ⟨239319, by rfl⟩ : syracuseStep 638185 = 478639) B478639
theorem B638239 : Blo 377762 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B1916297 : Blo 377762 1916297 := bstep (se 2 (by rfl) ⟨718611, by rfl⟩ : syracuseStep 1916297 = 1437223) B1437223
theorem B966239 : Blo 377762 966239 := bstep (se 1 (by rfl) ⟨724679, by rfl⟩ : syracuseStep 966239 = 1449359) B1449359
theorem B638651 : Blo 377762 638651 := bstep (se 1 (by rfl) ⟨478988, by rfl⟩ : syracuseStep 638651 = 957977) B957977
theorem B3227465 : Blo 377762 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B13188977 : Blo 377762 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B4636577 : Blo 377762 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B769999 : Blo 377762 769999 := bstep (se 1 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 769999 = 1154999) B1154999
theorem B2473993 : Blo 377762 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B606631 : Blo 377762 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B3064321 : Blo 377762 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B1917593 : Blo 377762 1917593 := bstep (se 2 (by rfl) ⟨719097, by rfl⟩ : syracuseStep 1917593 = 1438195) B1438195
theorem B869039 : Blo 377762 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B5259977 : Blo 377762 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B377807 : Blo 377762 377807 := bstep (se 1 (by rfl) ⟨283355, by rfl⟩ : syracuseStep 377807 = 566711) B566711
theorem B377831 : Blo 377762 377831 := bstep (se 1 (by rfl) ⟨283373, by rfl⟩ : syracuseStep 377831 = 566747) B566747
theorem B3654659 : Blo 377762 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B5850119 : Blo 377762 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B9684035 : Blo 377762 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B378143 : Blo 377762 378143 := bstep (se 1 (by rfl) ⟨283607, by rfl⟩ : syracuseStep 378143 = 567215) B567215
theorem B378203 : Blo 377762 378203 := bstep (se 1 (by rfl) ⟨283652, by rfl⟩ : syracuseStep 378203 = 567305) B567305
theorem B378223 : Blo 377762 378223 := bstep (se 1 (by rfl) ⟨283667, by rfl⟩ : syracuseStep 378223 = 567335) B567335
theorem B640379 : Blo 377762 640379 := bstep (se 1 (by rfl) ⟨480284, by rfl⟩ : syracuseStep 640379 = 960569) B960569
theorem B378279 : Blo 377762 378279 := bstep (se 1 (by rfl) ⟨283709, by rfl⟩ : syracuseStep 378279 = 567419) B567419
theorem B4376051 : Blo 377762 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B378363 : Blo 377762 378363 := bstep (se 1 (by rfl) ⟨283772, by rfl⟩ : syracuseStep 378363 = 567545) B567545
theorem B378431 : Blo 377762 378431 := bstep (se 1 (by rfl) ⟨283823, by rfl⟩ : syracuseStep 378431 = 567647) B567647
theorem B378439 : Blo 377762 378439 := bstep (se 1 (by rfl) ⟨283829, by rfl⟩ : syracuseStep 378439 = 567659) B567659
theorem B378591 : Blo 377762 378591 := bstep (se 1 (by rfl) ⟨283943, by rfl⟩ : syracuseStep 378591 = 567887) B567887
theorem B378671 : Blo 377762 378671 := bstep (se 1 (by rfl) ⟨284003, by rfl⟩ : syracuseStep 378671 = 568007) B568007
theorem B2934605 : Blo 377762 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B378779 : Blo 377762 378779 := bstep (se 1 (by rfl) ⟨284084, by rfl⟩ : syracuseStep 378779 = 568169) B568169
theorem B378831 : Blo 377762 378831 := bstep (se 1 (by rfl) ⟨284123, by rfl⟩ : syracuseStep 378831 = 568247) B568247
theorem B378855 : Blo 377762 378855 := bstep (se 1 (by rfl) ⟨284141, by rfl⟩ : syracuseStep 378855 = 568283) B568283
theorem B4311305 : Blo 377762 4311305 := bstep (se 2 (by rfl) ⟨1616739, by rfl⟩ : syracuseStep 4311305 = 3233479) B3233479
theorem B379167 : Blo 377762 379167 := bstep (se 1 (by rfl) ⟨284375, by rfl⟩ : syracuseStep 379167 = 568751) B568751
theorem B379227 : Blo 377762 379227 := bstep (se 1 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 379227 = 568841) B568841
theorem B641371 : Blo 377762 641371 := bstep (se 1 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 641371 = 962057) B962057
theorem B3230063 : Blo 377762 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B379247 : Blo 377762 379247 := bstep (se 1 (by rfl) ⟨284435, by rfl⟩ : syracuseStep 379247 = 568871) B568871
theorem B1919375 : Blo 377762 1919375 := bstep (se 1 (by rfl) ⟨1439531, by rfl⟩ : syracuseStep 1919375 = 2879063) B2879063
theorem B379303 : Blo 377762 379303 := bstep (se 1 (by rfl) ⟨284477, by rfl⟩ : syracuseStep 379303 = 568955) B568955
theorem B1624531 : Blo 377762 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B1821179 : Blo 377762 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B379387 : Blo 377762 379387 := bstep (se 1 (by rfl) ⟨284540, by rfl⟩ : syracuseStep 379387 = 569081) B569081
theorem B379455 : Blo 377762 379455 := bstep (se 1 (by rfl) ⟨284591, by rfl⟩ : syracuseStep 379455 = 569183) B569183
theorem B379463 : Blo 377762 379463 := bstep (se 1 (by rfl) ⟨284597, by rfl⟩ : syracuseStep 379463 = 569195) B569195
theorem B379615 : Blo 377762 379615 := bstep (se 1 (by rfl) ⟨284711, by rfl⟩ : syracuseStep 379615 = 569423) B569423
theorem B379695 : Blo 377762 379695 := bstep (se 1 (by rfl) ⟨284771, by rfl⟩ : syracuseStep 379695 = 569543) B569543
theorem B379803 : Blo 377762 379803 := bstep (se 1 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 379803 = 569705) B569705
theorem B379855 : Blo 377762 379855 := bstep (se 1 (by rfl) ⟨284891, by rfl⟩ : syracuseStep 379855 = 569783) B569783
theorem B379879 : Blo 377762 379879 := bstep (se 1 (by rfl) ⟨284909, by rfl⟩ : syracuseStep 379879 = 569819) B569819
theorem B740495 : Blo 377762 740495 := bstep (se 1 (by rfl) ⟨555371, by rfl⟩ : syracuseStep 740495 = 1110743) B1110743
theorem B380191 : Blo 377762 380191 := bstep (se 1 (by rfl) ⟨285143, by rfl⟩ : syracuseStep 380191 = 570287) B570287
theorem B642343 : Blo 377762 642343 := bstep (se 1 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 642343 = 963515) B963515
theorem B380251 : Blo 377762 380251 := bstep (se 1 (by rfl) ⟨285188, by rfl⟩ : syracuseStep 380251 = 570377) B570377
theorem B380271 : Blo 377762 380271 := bstep (se 1 (by rfl) ⟨285203, by rfl⟩ : syracuseStep 380271 = 570407) B570407
theorem B380327 : Blo 377762 380327 := bstep (se 1 (by rfl) ⟨285245, by rfl⟩ : syracuseStep 380327 = 570491) B570491
theorem B380411 : Blo 377762 380411 := bstep (se 1 (by rfl) ⟨285308, by rfl⟩ : syracuseStep 380411 = 570617) B570617
theorem B1625609 : Blo 377762 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B380479 : Blo 377762 380479 := bstep (se 1 (by rfl) ⟨285359, by rfl⟩ : syracuseStep 380479 = 570719) B570719
theorem B380487 : Blo 377762 380487 := bstep (se 1 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 380487 = 570731) B570731
theorem B1625761 : Blo 377762 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B380639 : Blo 377762 380639 := bstep (se 1 (by rfl) ⟨285479, by rfl⟩ : syracuseStep 380639 = 570959) B570959
theorem B10342187 : Blo 377762 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B380719 : Blo 377762 380719 := bstep (se 1 (by rfl) ⟨285539, by rfl⟩ : syracuseStep 380719 = 571079) B571079
theorem B642863 : Blo 377762 642863 := bstep (se 1 (by rfl) ⟨482147, by rfl⟩ : syracuseStep 642863 = 964295) B964295
theorem B1724267 : Blo 377762 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B380827 : Blo 377762 380827 := bstep (se 1 (by rfl) ⟨285620, by rfl⟩ : syracuseStep 380827 = 571241) B571241
theorem B1101725 : Blo 377762 1101725 := bstep (se 3 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 1101725 = 413147) B413147
theorem B380879 : Blo 377762 380879 := bstep (se 1 (by rfl) ⟨285659, by rfl⟩ : syracuseStep 380879 = 571319) B571319
theorem B380903 : Blo 377762 380903 := bstep (se 1 (by rfl) ⟨285677, by rfl⟩ : syracuseStep 380903 = 571355) B571355
theorem B381215 : Blo 377762 381215 := bstep (se 1 (by rfl) ⟨285911, by rfl⟩ : syracuseStep 381215 = 571823) B571823
theorem B381275 : Blo 377762 381275 := bstep (se 1 (by rfl) ⟨285956, by rfl⟩ : syracuseStep 381275 = 571913) B571913
theorem B381295 : Blo 377762 381295 := bstep (se 1 (by rfl) ⟨285971, by rfl⟩ : syracuseStep 381295 = 571943) B571943
theorem B479611 : Blo 377762 479611 := bstep (se 1 (by rfl) ⟨359708, by rfl⟩ : syracuseStep 479611 = 719417) B719417
theorem B381351 : Blo 377762 381351 := bstep (se 1 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 381351 = 572027) B572027
theorem B1921481 : Blo 377762 1921481 := bstep (se 2 (by rfl) ⟨720555, by rfl⟩ : syracuseStep 1921481 = 1441111) B1441111
theorem B381435 : Blo 377762 381435 := bstep (se 1 (by rfl) ⟨286076, by rfl⟩ : syracuseStep 381435 = 572153) B572153
theorem B159896081 : Blo 377762 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B381503 : Blo 377762 381503 := bstep (se 1 (by rfl) ⟨286127, by rfl⟩ : syracuseStep 381503 = 572255) B572255
theorem B381511 : Blo 377762 381511 := bstep (se 1 (by rfl) ⟨286133, by rfl⟩ : syracuseStep 381511 = 572267) B572267
theorem B479839 : Blo 377762 479839 := bstep (se 1 (by rfl) ⟨359879, by rfl⟩ : syracuseStep 479839 = 719759) B719759
theorem B611039 : Blo 377762 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B381663 : Blo 377762 381663 := bstep (se 1 (by rfl) ⟨286247, by rfl⟩ : syracuseStep 381663 = 572495) B572495
theorem B381743 : Blo 377762 381743 := bstep (se 1 (by rfl) ⟨286307, by rfl⟩ : syracuseStep 381743 = 572615) B572615
theorem B807823 : Blo 377762 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B578459 : Blo 377762 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B2053025 : Blo 377762 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B644071 : Blo 377762 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B2086033 : Blo 377762 2086033 := bstep (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) B1564525
theorem B5002397 : Blo 377762 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B1299671 : Blo 377762 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B1922291 : Blo 377762 1922291 := bstep (se 1 (by rfl) ⟨1441718, by rfl⟩ : syracuseStep 1922291 = 2883437) B2883437
theorem B2151917 : Blo 377762 2151917 := bstep (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) B806969
theorem B1726109 : Blo 377762 1726109 := bstep (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) B647291
theorem B481079 : Blo 377762 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B481231 : Blo 377762 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B2218063 : Blo 377762 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B3528839 : Blo 377762 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B809327 : Blo 377762 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B1956221 : Blo 377762 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B3234437 : Blo 377762 3234437 := bstep (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) B606457
theorem B8248067 : Blo 377762 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B482203 : Blo 377762 482203 := bstep (se 1 (by rfl) ⟨361652, by rfl⟩ : syracuseStep 482203 = 723305) B723305
theorem B908263 : Blo 377762 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B1924235 : Blo 377762 1924235 := bstep (se 1 (by rfl) ⟨1443176, by rfl⟩ : syracuseStep 1924235 = 2886353) B2886353
theorem B810233 : Blo 377762 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B65068505 : Blo 377762 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B1728209 : Blo 377762 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B1367815 : Blo 377762 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B6644227 : Blo 377762 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1925855 : Blo 377762 1925855 := bstep (se 1 (by rfl) ⟨1444391, by rfl⟩ : syracuseStep 1925855 = 2888783) B2888783
theorem B1827983 : Blo 377762 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B3467215 : Blo 377762 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B1370297 : Blo 377762 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B4680179 : Blo 377762 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B911945 : Blo 377762 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B7269041 : Blo 377762 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B10414871 : Blo 377762 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1928123 : Blo 377762 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B814043 : Blo 377762 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B912359 : Blo 377762 912359 := bstep (se 1 (by rfl) ⟨684269, by rfl⟩ : syracuseStep 912359 = 1368539) B1368539
theorem B2321423 : Blo 377762 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B1044155 : Blo 377762 1044155 := bstep (se 1 (by rfl) ⟨783116, by rfl⟩ : syracuseStep 1044155 = 1566233) B1566233
theorem B978695 : Blo 377762 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B814855 : Blo 377762 814855 := bstep (se 1 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 814855 = 1222283) B1222283
theorem B1437497 : Blo 377762 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B3239837 : Blo 377762 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B1929419 : Blo 377762 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B2748779 : Blo 377762 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B3469873 : Blo 377762 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B684767 : Blo 377762 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B1831673 : Blo 377762 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B717815 : Blo 377762 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B4879439 : Blo 377762 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B1078397 : Blo 377762 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B7271639 : Blo 377762 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B5174545 : Blo 377762 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B718217 : Blo 377762 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B3667463 : Blo 377762 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B3667805 : Blo 377762 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B456679 : Blo 377762 456679 := bstep (se 1 (by rfl) ⟨342509, by rfl⟩ : syracuseStep 456679 = 685019) B685019
theorem B719113 : Blo 377762 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B850283 : Blo 377762 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B686503 : Blo 377762 686503 := bstep (se 1 (by rfl) ⟨514877, by rfl⟩ : syracuseStep 686503 = 1029755) B1029755
theorem B1931687 : Blo 377762 1931687 := bstep (se 1 (by rfl) ⟨1448765, by rfl⟩ : syracuseStep 1931687 = 2897531) B2897531
theorem B1276343 : Blo 377762 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B850427 : Blo 377762 850427 := bstep (se 1 (by rfl) ⟨637820, by rfl⟩ : syracuseStep 850427 = 1275641) B1275641
theorem B1931849 : Blo 377762 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B850553 : Blo 377762 850553 := bstep (se 2 (by rfl) ⟨318957, by rfl⟩ : syracuseStep 850553 = 637915) B637915
theorem B850607 : Blo 377762 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B850679 : Blo 377762 850679 := bstep (se 1 (by rfl) ⟨638009, by rfl⟩ : syracuseStep 850679 = 1276019) B1276019
theorem B850859 : Blo 377762 850859 := bstep (se 1 (by rfl) ⟨638144, by rfl⟩ : syracuseStep 850859 = 1276289) B1276289
theorem B5176349 : Blo 377762 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B851399 : Blo 377762 851399 := bstep (se 1 (by rfl) ⟨638549, by rfl⟩ : syracuseStep 851399 = 1277099) B1277099
theorem B458303 : Blo 377762 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B720571 : Blo 377762 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B425695 : Blo 377762 425695 := bstep (se 1 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 425695 = 638543) B638543
theorem B720647 : Blo 377762 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B851759 : Blo 377762 851759 := bstep (se 1 (by rfl) ⟨638819, by rfl⟩ : syracuseStep 851759 = 1277639) B1277639
theorem B1441583 : Blo 377762 1441583 := bstep (se 1 (by rfl) ⟨1081187, by rfl⟩ : syracuseStep 1441583 = 2162375) B2162375
theorem B1441597 : Blo 377762 1441597 := bstep (se 3 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 1441597 = 540599) B540599
theorem B1278233 : Blo 377762 1278233 := bstep (se 2 (by rfl) ⟨479337, by rfl⟩ : syracuseStep 1278233 = 958675) B958675
theorem B1278395 : Blo 377762 1278395 := bstep (se 1 (by rfl) ⟨958796, by rfl⟩ : syracuseStep 1278395 = 1917593) B1917593
theorem B3506651 : Blo 377762 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B2163307 : Blo 377762 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B3900079 : Blo 377762 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B1966787 : Blo 377762 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B6456023 : Blo 377762 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B1442569 : Blo 377762 1442569 := bstep (se 2 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 1442569 = 1081927) B1081927
theorem B426919 : Blo 377762 426919 := bstep (se 1 (by rfl) ⟨320189, by rfl⟩ : syracuseStep 426919 = 640379) B640379
theorem B852947 : Blo 377762 852947 := bstep (se 1 (by rfl) ⟨639710, by rfl⟩ : syracuseStep 852947 = 1279421) B1279421
theorem B2917367 : Blo 377762 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B853199 : Blo 377762 853199 := bstep (se 1 (by rfl) ⟨639899, by rfl⟩ : syracuseStep 853199 = 1279799) B1279799
theorem B853523 : Blo 377762 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B1279583 : Blo 377762 1279583 := bstep (se 1 (by rfl) ⟨959687, by rfl⟩ : syracuseStep 1279583 = 1919375) B1919375
theorem B788135 : Blo 377762 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1214119 : Blo 377762 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B4884461 : Blo 377762 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B493663 : Blo 377762 493663 := bstep (se 1 (by rfl) ⟨370247, by rfl⟩ : syracuseStep 493663 = 740495) B740495
theorem B854207 : Blo 377762 854207 := bstep (se 1 (by rfl) ⟨640655, by rfl⟩ : syracuseStep 854207 = 1281311) B1281311
theorem B2165039 : Blo 377762 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B1083739 : Blo 377762 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B1542557 : Blo 377762 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B428575 : Blo 377762 428575 := bstep (se 1 (by rfl) ⟨321431, by rfl⟩ : syracuseStep 428575 = 642863) B642863
theorem B723487 : Blo 377762 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B4622953 : Blo 377762 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B1280987 : Blo 377762 1280987 := bstep (se 1 (by rfl) ⟨960740, by rfl⟩ : syracuseStep 1280987 = 1921481) B1921481
theorem B106597387 : Blo 377762 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B855161 : Blo 377762 855161 := bstep (se 2 (by rfl) ⟨320685, by rfl⟩ : syracuseStep 855161 = 641371) B641371
theorem B1281257 : Blo 377762 1281257 := bstep (se 2 (by rfl) ⟨480471, by rfl⟩ : syracuseStep 1281257 = 960943) B960943
theorem B2166041 : Blo 377762 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B4328801 : Blo 377762 4328801 := bstep (se 2 (by rfl) ⟨1623300, by rfl⟩ : syracuseStep 4328801 = 3246601) B3246601
theorem B1445303 : Blo 377762 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B1281527 : Blo 377762 1281527 := bstep (se 1 (by rfl) ⟨961145, by rfl⟩ : syracuseStep 1281527 = 1922291) B1922291
theorem B2887325 : Blo 377762 2887325 := bstep (se 3 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 2887325 = 1082747) B1082747
theorem B1150739 : Blo 377762 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B855827 : Blo 377762 855827 := bstep (se 1 (by rfl) ⟨641870, by rfl⟩ : syracuseStep 855827 = 1283741) B1283741
theorem B856187 : Blo 377762 856187 := bstep (se 1 (by rfl) ⟨642140, by rfl⟩ : syracuseStep 856187 = 1284281) B1284281
theorem B856457 : Blo 377762 856457 := bstep (se 2 (by rfl) ⟨321171, by rfl⟩ : syracuseStep 856457 = 642343) B642343
theorem B1282553 : Blo 377762 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B2167499 : Blo 377762 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B1282823 : Blo 377762 1282823 := bstep (se 1 (by rfl) ⟨962117, by rfl⟩ : syracuseStep 1282823 = 1924235) B1924235
theorem B1282877 : Blo 377762 1282877 := bstep (se 3 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 1282877 = 481079) B481079
theorem B2167681 : Blo 377762 2167681 := bstep (se 2 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 2167681 = 1625761) B1625761
theorem B1086473 : Blo 377762 1086473 := bstep (se 2 (by rfl) ⟨407427, by rfl⟩ : syracuseStep 1086473 = 814855) B814855
theorem B857195 : Blo 377762 857195 := bstep (se 1 (by rfl) ⟨642896, by rfl⟩ : syracuseStep 857195 = 1285793) B1285793
theorem B1152139 : Blo 377762 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B857771 : Blo 377762 857771 := bstep (se 1 (by rfl) ⟨643328, by rfl⟩ : syracuseStep 857771 = 1286657) B1286657
theorem B1283903 : Blo 377762 1283903 := bstep (se 1 (by rfl) ⟨962927, by rfl⟩ : syracuseStep 1283903 = 1925855) B1925855
theorem B858095 : Blo 377762 858095 := bstep (se 1 (by rfl) ⟨643571, by rfl⟩ : syracuseStep 858095 = 1287143) B1287143
theorem B4626497 : Blo 377762 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B1218655 : Blo 377762 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B8198243 : Blo 377762 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B858311 : Blo 377762 858311 := bstep (se 1 (by rfl) ⟨643733, by rfl⟩ : syracuseStep 858311 = 1287467) B1287467
theorem B858491 : Blo 377762 858491 := bstep (se 1 (by rfl) ⟨643868, by rfl⟩ : syracuseStep 858491 = 1287737) B1287737
theorem B858761 : Blo 377762 858761 := bstep (se 2 (by rfl) ⟨322035, by rfl⟩ : syracuseStep 858761 = 644071) B644071
theorem B2431853 : Blo 377762 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B3120119 : Blo 377762 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B1285415 : Blo 377762 1285415 := bstep (se 1 (by rfl) ⟨964061, by rfl⟩ : syracuseStep 1285415 = 1928123) B1928123
theorem B1547615 : Blo 377762 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B23403907 : Blo 377762 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B3349991 : Blo 377762 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B10690127 : Blo 377762 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B1023721 : Blo 377762 1023721 := bstep (se 2 (by rfl) ⟨383895, by rfl⟩ : syracuseStep 1023721 = 767791) B767791
theorem B696103 : Blo 377762 696103 := bstep (se 1 (by rfl) ⟨522077, by rfl⟩ : syracuseStep 696103 = 1044155) B1044155
theorem B958331 : Blo 377762 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B2957417 : Blo 377762 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B1286279 : Blo 377762 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B2433311 : Blo 377762 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B958817 : Blo 377762 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B3252959 : Blo 377762 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B2302739 : Blo 377762 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B1222141 : Blo 377762 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B566855 : Blo 377762 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B1287791 : Blo 377762 1287791 := bstep (se 1 (by rfl) ⟨965843, by rfl⟩ : syracuseStep 1287791 = 1931687) B1931687
theorem B566951 : Blo 377762 566951 := bstep (se 1 (by rfl) ⟨425213, by rfl⟩ : syracuseStep 566951 = 850427) B850427
theorem B1287899 : Blo 377762 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B567035 : Blo 377762 567035 := bstep (se 1 (by rfl) ⟨425276, by rfl⟩ : syracuseStep 567035 = 850553) B850553
theorem B567071 : Blo 377762 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B567119 : Blo 377762 567119 := bstep (se 1 (by rfl) ⟨425339, by rfl⟩ : syracuseStep 567119 = 850679) B850679
theorem B567239 : Blo 377762 567239 := bstep (se 1 (by rfl) ⟨425429, by rfl⟩ : syracuseStep 567239 = 850859) B850859
theorem B3450899 : Blo 377762 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B960761 : Blo 377762 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B4598045 : Blo 377762 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B567593 : Blo 377762 567593 := bstep (se 2 (by rfl) ⟨212847, by rfl⟩ : syracuseStep 567593 = 425695) B425695
theorem B567599 : Blo 377762 567599 := bstep (se 1 (by rfl) ⟨425699, by rfl⟩ : syracuseStep 567599 = 851399) B851399
theorem B567839 : Blo 377762 567839 := bstep (se 1 (by rfl) ⟨425879, by rfl⟩ : syracuseStep 567839 = 851759) B851759
theorem B961055 : Blo 377762 961055 := bstep (se 1 (by rfl) ⟨720791, by rfl⟩ : syracuseStep 961055 = 1441583) B1441583
theorem B8792651 : Blo 377762 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B1026665 : Blo 377762 1026665 := bstep (se 2 (by rfl) ⟨384999, by rfl⟩ : syracuseStep 1026665 = 769999) B769999
theorem B3091051 : Blo 377762 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B568223 : Blo 377762 568223 := bstep (se 1 (by rfl) ⟨426167, by rfl⟩ : syracuseStep 568223 = 852335) B852335
theorem B568271 : Blo 377762 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B568361 : Blo 377762 568361 := bstep (se 2 (by rfl) ⟨213135, by rfl⟩ : syracuseStep 568361 = 426271) B426271
theorem B568367 : Blo 377762 568367 := bstep (se 1 (by rfl) ⟨426275, by rfl⟩ : syracuseStep 568367 = 852551) B852551
theorem B568391 : Blo 377762 568391 := bstep (se 1 (by rfl) ⟨426293, by rfl⟩ : syracuseStep 568391 = 852587) B852587
theorem B568655 : Blo 377762 568655 := bstep (se 1 (by rfl) ⟨426491, by rfl⟩ : syracuseStep 568655 = 852983) B852983
theorem B2436439 : Blo 377762 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B8858969 : Blo 377762 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B568745 : Blo 377762 568745 := bstep (se 2 (by rfl) ⟨213279, by rfl⟩ : syracuseStep 568745 = 426559) B426559
theorem B568895 : Blo 377762 568895 := bstep (se 1 (by rfl) ⟨426671, by rfl⟩ : syracuseStep 568895 = 853343) B853343
theorem B569159 : Blo 377762 569159 := bstep (se 1 (by rfl) ⟨426869, by rfl⟩ : syracuseStep 569159 = 853739) B853739
theorem B569243 : Blo 377762 569243 := bstep (se 1 (by rfl) ⟨426932, by rfl⟩ : syracuseStep 569243 = 853865) B853865
theorem B6173081 : Blo 377762 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B569807 : Blo 377762 569807 := bstep (se 1 (by rfl) ⟨427355, by rfl⟩ : syracuseStep 569807 = 854711) B854711
theorem B569849 : Blo 377762 569849 := bstep (se 2 (by rfl) ⟨213693, by rfl⟩ : syracuseStep 569849 = 427387) B427387
theorem B569951 : Blo 377762 569951 := bstep (se 1 (by rfl) ⟨427463, by rfl⟩ : syracuseStep 569951 = 854927) B854927
theorem B963353 : Blo 377762 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B1618859 : Blo 377762 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B570431 : Blo 377762 570431 := bstep (se 1 (by rfl) ⟨427823, by rfl⟩ : syracuseStep 570431 = 855647) B855647
theorem B963647 : Blo 377762 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B570473 : Blo 377762 570473 := bstep (se 2 (by rfl) ⟨213927, by rfl⟩ : syracuseStep 570473 = 427855) B427855
theorem B6894791 : Blo 377762 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B570575 : Blo 377762 570575 := bstep (se 1 (by rfl) ⟨427931, by rfl⟩ : syracuseStep 570575 = 855863) B855863
theorem B963859 : Blo 377762 963859 := bstep (se 1 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 963859 = 1445789) B1445789
theorem B734483 : Blo 377762 734483 := bstep (se 1 (by rfl) ⟨550862, by rfl⟩ : syracuseStep 734483 = 1101725) B1101725
theorem B570779 : Blo 377762 570779 := bstep (se 1 (by rfl) ⟨428084, by rfl⟩ : syracuseStep 570779 = 856169) B856169
theorem B571001 : Blo 377762 571001 := bstep (se 2 (by rfl) ⟨214125, by rfl⟩ : syracuseStep 571001 = 428251) B428251
theorem B571103 : Blo 377762 571103 := bstep (se 1 (by rfl) ⟨428327, by rfl⟩ : syracuseStep 571103 = 856655) B856655
theorem B571199 : Blo 377762 571199 := bstep (se 1 (by rfl) ⟨428399, by rfl⟩ : syracuseStep 571199 = 856799) B856799
theorem B407359 : Blo 377762 407359 := bstep (se 1 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 407359 = 611039) B611039
theorem B571367 : Blo 377762 571367 := bstep (se 1 (by rfl) ⟨428525, by rfl⟩ : syracuseStep 571367 = 857051) B857051
theorem B571385 : Blo 377762 571385 := bstep (se 2 (by rfl) ⟨214269, by rfl⟩ : syracuseStep 571385 = 428539) B428539
theorem B571487 : Blo 377762 571487 := bstep (se 1 (by rfl) ⟨428615, by rfl⟩ : syracuseStep 571487 = 857231) B857231
theorem B866447 : Blo 377762 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B571547 : Blo 377762 571547 := bstep (se 1 (by rfl) ⟨428660, by rfl⟩ : syracuseStep 571547 = 857321) B857321
theorem B22132909 : Blo 377762 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B571583 : Blo 377762 571583 := bstep (se 1 (by rfl) ⟨428687, by rfl⟩ : syracuseStep 571583 = 857375) B857375
theorem B571625 : Blo 377762 571625 := bstep (se 2 (by rfl) ⟨214359, by rfl⟩ : syracuseStep 571625 = 428719) B428719
theorem B1620499 : Blo 377762 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B571931 : Blo 377762 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B572009 : Blo 377762 572009 := bstep (se 2 (by rfl) ⟨214503, by rfl⟩ : syracuseStep 572009 = 429007) B429007
theorem B1293023 : Blo 377762 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B965459 : Blo 377762 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B637787 : Blo 377762 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B1096553 : Blo 377762 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B539551 : Blo 377762 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B638023 : Blo 377762 638023 := bstep (se 1 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 638023 = 957035) B957035
theorem B572537 : Blo 377762 572537 := bstep (se 2 (by rfl) ⟨214701, by rfl⟩ : syracuseStep 572537 = 429403) B429403
theorem B572639 : Blo 377762 572639 := bstep (se 1 (by rfl) ⟨429479, by rfl⟩ : syracuseStep 572639 = 858959) B858959
theorem B4308389 : Blo 377762 4308389 := bstep (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) B807823
theorem B3456443 : Blo 377762 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B638455 : Blo 377762 638455 := bstep (se 1 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 638455 = 957683) B957683
theorem B540155 : Blo 377762 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B638759 : Blo 377762 638759 := bstep (se 1 (by rfl) ⟨479069, by rfl⟩ : syracuseStep 638759 = 958139) B958139
theorem B639481 : Blo 377762 639481 := bstep (se 2 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 639481 = 479611) B479611
theorem B639751 : Blo 377762 639751 := bstep (se 1 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 639751 = 959627) B959627
theorem B639785 : Blo 377762 639785 := bstep (se 2 (by rfl) ⟨239919, by rfl⟩ : syracuseStep 639785 = 479839) B479839
theorem B377767 : Blo 377762 377767 := bstep (se 1 (by rfl) ⟨283325, by rfl⟩ : syracuseStep 377767 = 566651) B566651
theorem B377851 : Blo 377762 377851 := bstep (se 1 (by rfl) ⟨283388, by rfl⟩ : syracuseStep 377851 = 566777) B566777
theorem B640055 : Blo 377762 640055 := bstep (se 1 (by rfl) ⟨480041, by rfl⟩ : syracuseStep 640055 = 960083) B960083
theorem B1754171 : Blo 377762 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B377919 : Blo 377762 377919 := bstep (se 1 (by rfl) ⟨283439, by rfl⟩ : syracuseStep 377919 = 566879) B566879
theorem B378063 : Blo 377762 378063 := bstep (se 1 (by rfl) ⟨283547, by rfl⟩ : syracuseStep 378063 = 567095) B567095
theorem B378267 : Blo 377762 378267 := bstep (se 1 (by rfl) ⟨283700, by rfl⟩ : syracuseStep 378267 = 567401) B567401
theorem B378479 : Blo 377762 378479 := bstep (se 1 (by rfl) ⟨283859, by rfl⟩ : syracuseStep 378479 = 567719) B567719
theorem B378535 : Blo 377762 378535 := bstep (se 1 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 378535 = 567803) B567803
theorem B6899393 : Blo 377762 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B378619 : Blo 377762 378619 := bstep (se 1 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 378619 = 567929) B567929
theorem B378655 : Blo 377762 378655 := bstep (se 1 (by rfl) ⟨283991, by rfl⟩ : syracuseStep 378655 = 567983) B567983
theorem B19384109 : Blo 377762 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B378687 : Blo 377762 378687 := bstep (se 1 (by rfl) ⟨284015, by rfl⟩ : syracuseStep 378687 = 568031) B568031
theorem B640831 : Blo 377762 640831 := bstep (se 1 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 640831 = 961247) B961247
theorem B542695 : Blo 377762 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B378863 : Blo 377762 378863 := bstep (se 1 (by rfl) ⟨284147, by rfl⟩ : syracuseStep 378863 = 568295) B568295
theorem B608239 : Blo 377762 608239 := bstep (se 1 (by rfl) ⟨456179, by rfl⟩ : syracuseStep 608239 = 912359) B912359
theorem B379035 : Blo 377762 379035 := bstep (se 1 (by rfl) ⟨284276, by rfl⟩ : syracuseStep 379035 = 568553) B568553
theorem B379071 : Blo 377762 379071 := bstep (se 1 (by rfl) ⟨284303, by rfl⟩ : syracuseStep 379071 = 568607) B568607
theorem B379183 : Blo 377762 379183 := bstep (se 1 (by rfl) ⟨284387, by rfl⟩ : syracuseStep 379183 = 568775) B568775
theorem B379419 : Blo 377762 379419 := bstep (se 1 (by rfl) ⟨284564, by rfl⟩ : syracuseStep 379419 = 569129) B569129
theorem B379423 : Blo 377762 379423 := bstep (se 1 (by rfl) ⟨284567, by rfl⟩ : syracuseStep 379423 = 569135) B569135
theorem B641567 : Blo 377762 641567 := bstep (se 1 (by rfl) ⟨481175, by rfl⟩ : syracuseStep 641567 = 962351) B962351
theorem B641641 : Blo 377762 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B608905 : Blo 377762 608905 := bstep (se 2 (by rfl) ⟨228339, by rfl⟩ : syracuseStep 608905 = 456679) B456679
theorem B379739 : Blo 377762 379739 := bstep (se 1 (by rfl) ⟨284804, by rfl⟩ : syracuseStep 379739 = 569609) B569609
theorem B379807 : Blo 377762 379807 := bstep (se 1 (by rfl) ⟨284855, by rfl⟩ : syracuseStep 379807 = 569711) B569711
theorem B641999 : Blo 377762 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B379951 : Blo 377762 379951 := bstep (se 1 (by rfl) ⟨284963, by rfl⟩ : syracuseStep 379951 = 569927) B569927
theorem B379975 : Blo 377762 379975 := bstep (se 1 (by rfl) ⟨284981, by rfl⟩ : syracuseStep 379975 = 569963) B569963
theorem B380127 : Blo 377762 380127 := bstep (se 1 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 380127 = 570191) B570191
theorem B478543 : Blo 377762 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B380391 : Blo 377762 380391 := bstep (se 1 (by rfl) ⟨285293, by rfl⟩ : syracuseStep 380391 = 570587) B570587
theorem B478811 : Blo 377762 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B380507 : Blo 377762 380507 := bstep (se 1 (by rfl) ⟨285380, by rfl⟩ : syracuseStep 380507 = 570761) B570761
theorem B642667 : Blo 377762 642667 := bstep (se 1 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 642667 = 964001) B964001
theorem B2444975 : Blo 377762 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B380743 : Blo 377762 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B642937 : Blo 377762 642937 := bstep (se 2 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 642937 = 482203) B482203
theorem B2445203 : Blo 377762 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B642971 : Blo 377762 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B380895 : Blo 377762 380895 := bstep (se 1 (by rfl) ⟨285671, by rfl⟩ : syracuseStep 380895 = 571343) B571343
theorem B2740243 : Blo 377762 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1331329 : Blo 377762 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B381159 : Blo 377762 381159 := bstep (se 1 (by rfl) ⟨285869, by rfl⟩ : syracuseStep 381159 = 571739) B571739
theorem B381311 : Blo 377762 381311 := bstep (se 1 (by rfl) ⟨285983, by rfl⟩ : syracuseStep 381311 = 571967) B571967
theorem B381391 : Blo 377762 381391 := bstep (se 1 (by rfl) ⟨286043, by rfl⟩ : syracuseStep 381391 = 572087) B572087
theorem B971347 : Blo 377762 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B381543 : Blo 377762 381543 := bstep (se 1 (by rfl) ⟨286157, by rfl⟩ : syracuseStep 381543 = 572315) B572315
theorem B1823753 : Blo 377762 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B644159 : Blo 377762 644159 := bstep (se 1 (by rfl) ⟨483119, by rfl⟩ : syracuseStep 644159 = 966239) B966239
theorem B1922129 : Blo 377762 1922129 := bstep (se 2 (by rfl) ⟨720798, by rfl⟩ : syracuseStep 1922129 = 1441597) B1441597
theorem B480431 : Blo 377762 480431 := bstep (se 1 (by rfl) ⟨360323, by rfl⟩ : syracuseStep 480431 = 720647) B720647
theorem B2151643 : Blo 377762 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B3298657 : Blo 377762 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B579359 : Blo 377762 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B808841 : Blo 377762 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B4085761 : Blo 377762 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B1956403 : Blo 377762 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B2874203 : Blo 377762 2874203 := bstep (se 1 (by rfl) ⟨2155652, by rfl⟩ : syracuseStep 2874203 = 4311305) B4311305
theorem B2153375 : Blo 377762 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B1367009 : Blo 377762 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B482375 : Blo 377762 482375 := bstep (se 1 (by rfl) ⟨361781, by rfl⟩ : syracuseStep 482375 = 723563) B723563
theorem B482527 : Blo 377762 482527 := bstep (se 1 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 482527 = 723791) B723791
theorem B810823 : Blo 377762 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B1728647 : Blo 377762 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B2154833 : Blo 377762 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B1368683 : Blo 377762 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B3334931 : Blo 377762 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B4154267 : Blo 377762 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B1434611 : Blo 377762 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B2352559 : Blo 377762 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B1467919 : Blo 377762 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B1304147 : Blo 377762 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B1730267 : Blo 377762 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B2156291 : Blo 377762 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B5498711 : Blo 377762 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B1927313 : Blo 377762 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B813359 : Blo 377762 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B43379003 : Blo 377762 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B4844069 : Blo 377762 4844069 := bstep (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) B908263
theorem B1077371 : Blo 377762 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B913531 : Blo 377762 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B3076289 : Blo 377762 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B2781377 : Blo 377762 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B6943247 : Blo 377762 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B1929743 : Blo 377762 1929743 := bstep (se 1 (by rfl) ⟨1447307, by rfl⟩ : syracuseStep 1929743 = 2894615) B2894615
theorem B717473 : Blo 377762 717473 := bstep (se 2 (by rfl) ⟨269052, by rfl⟩ : syracuseStep 717473 = 538105) B538105
theorem B652463 : Blo 377762 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B1275155 : Blo 377762 1275155 := bstep (se 1 (by rfl) ⟨956366, by rfl⟩ : syracuseStep 1275155 = 1912733) B1912733
theorem B2159891 : Blo 377762 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B1832519 : Blo 377762 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B1275695 : Blo 377762 1275695 := bstep (se 1 (by rfl) ⟨956771, by rfl⟩ : syracuseStep 1275695 = 1913543) B1913543
theorem B456511 : Blo 377762 456511 := bstep (se 1 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 456511 = 684767) B684767
theorem B915337 : Blo 377762 915337 := bstep (se 2 (by rfl) ⟨343251, by rfl⟩ : syracuseStep 915337 = 686503) B686503
theorem B718931 : Blo 377762 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B4847759 : Blo 377762 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B850895 : Blo 377762 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B850913 : Blo 377762 850913 := bstep (se 2 (by rfl) ⟨319092, by rfl⟩ : syracuseStep 850913 = 638185) B638185
theorem B850985 : Blo 377762 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B1277531 : Blo 377762 1277531 := bstep (se 1 (by rfl) ⟨958148, by rfl⟩ : syracuseStep 1277531 = 1916297) B1916297
theorem B425767 : Blo 377762 425767 := bstep (se 1 (by rfl) ⟨319325, by rfl⟩ : syracuseStep 425767 = 638651) B638651
theorem B852155 : Blo 377762 852155 := bstep (se 1 (by rfl) ⟨639116, by rfl⟩ : syracuseStep 852155 = 1278233) B1278233
theorem B852263 : Blo 377762 852263 := bstep (se 1 (by rfl) ⟨639197, by rfl⟩ : syracuseStep 852263 = 1278395) B1278395
theorem B1311191 : Blo 377762 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B426523 : Blo 377762 426523 := bstep (se 1 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 426523 = 639785) B639785
theorem B852641 : Blo 377762 852641 := bstep (se 2 (by rfl) ⟨319740, by rfl⟩ : syracuseStep 852641 = 639481) B639481
theorem B426703 : Blo 377762 426703 := bstep (se 1 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 426703 = 640055) B640055
theorem B2884409 : Blo 377762 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B853001 : Blo 377762 853001 := bstep (se 2 (by rfl) ⟨319875, by rfl⟩ : syracuseStep 853001 = 639751) B639751
theorem B853055 : Blo 377762 853055 := bstep (se 1 (by rfl) ⟨639791, by rfl⟩ : syracuseStep 853055 = 1279583) B1279583
theorem B1443359 : Blo 377762 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B427711 : Blo 377762 427711 := bstep (se 1 (by rfl) ⟨320783, by rfl⟩ : syracuseStep 427711 = 641567) B641567
theorem B427999 : Blo 377762 427999 := bstep (se 1 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 427999 = 641999) B641999
theorem B853991 : Blo 377762 853991 := bstep (se 1 (by rfl) ⟨640493, by rfl⟩ : syracuseStep 853991 = 1280987) B1280987
theorem B854171 : Blo 377762 854171 := bstep (se 1 (by rfl) ⟨640628, by rfl⟩ : syracuseStep 854171 = 1281257) B1281257
theorem B1444027 : Blo 377762 1444027 := bstep (se 1 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 1444027 = 2166041) B2166041
theorem B2885867 : Blo 377762 2885867 := bstep (se 1 (by rfl) ⟨2164400, by rfl⟩ : syracuseStep 2885867 = 4328801) B4328801
theorem B854351 : Blo 377762 854351 := bstep (se 1 (by rfl) ⟨640763, by rfl⟩ : syracuseStep 854351 = 1281527) B1281527
theorem B11078045 : Blo 377762 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B854441 : Blo 377762 854441 := bstep (se 2 (by rfl) ⟨320415, by rfl⟩ : syracuseStep 854441 = 640831) B640831
theorem B428647 : Blo 377762 428647 := bstep (se 1 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 428647 = 642971) B642971
theorem B723593 : Blo 377762 723593 := bstep (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) B542695
theorem B658217 : Blo 377762 658217 := bstep (se 2 (by rfl) ⟨246831, by rfl⟩ : syracuseStep 658217 = 493663) B493663
theorem B855035 : Blo 377762 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B1444985 : Blo 377762 1444985 := bstep (se 2 (by rfl) ⟨541869, by rfl⟩ : syracuseStep 1444985 = 1083739) B1083739
theorem B1281149 : Blo 377762 1281149 := bstep (se 3 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 1281149 = 480431) B480431
theorem B1444999 : Blo 377762 1444999 := bstep (se 1 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 1444999 = 2167499) B2167499
theorem B855215 : Blo 377762 855215 := bstep (se 1 (by rfl) ⟨641411, by rfl⟩ : syracuseStep 855215 = 1282823) B1282823
theorem B855251 : Blo 377762 855251 := bstep (se 1 (by rfl) ⟨641438, by rfl⟩ : syracuseStep 855251 = 1282877) B1282877
theorem B724315 : Blo 377762 724315 := bstep (se 1 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 724315 = 1086473) B1086473
theorem B429439 : Blo 377762 429439 := bstep (se 1 (by rfl) ⟨322079, by rfl⟩ : syracuseStep 429439 = 644159) B644159
theorem B1281419 : Blo 377762 1281419 := bstep (se 1 (by rfl) ⟨961064, by rfl⟩ : syracuseStep 1281419 = 1922129) B1922129
theorem B6163937 : Blo 377762 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B855521 : Blo 377762 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B855935 : Blo 377762 855935 := bstep (se 1 (by rfl) ⟨641951, by rfl⟩ : syracuseStep 855935 = 1283903) B1283903
theorem B3084331 : Blo 377762 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B3477725 : Blo 377762 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B3248585 : Blo 377762 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B1544957 : Blo 377762 1544957 := bstep (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) B579359
theorem B856889 : Blo 377762 856889 := bstep (se 2 (by rfl) ⟨321333, by rfl⟩ : syracuseStep 856889 = 642667) B642667
theorem B856943 : Blo 377762 856943 := bstep (se 1 (by rfl) ⟨642707, by rfl⟩ : syracuseStep 856943 = 1285415) B1285415
theorem B2233327 : Blo 377762 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B857249 : Blo 377762 857249 := bstep (se 2 (by rfl) ⟨321468, by rfl⟩ : syracuseStep 857249 = 642937) B642937
theorem B1971611 : Blo 377762 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1152431 : Blo 377762 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B857519 : Blo 377762 857519 := bstep (se 1 (by rfl) ⟨643139, by rfl⟩ : syracuseStep 857519 = 1286279) B1286279
theorem B1218041 : Blo 377762 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B1775105 : Blo 377762 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B2168639 : Blo 377762 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B956407 : Blo 377762 956407 := bstep (se 1 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 956407 = 1434611) B1434611
theorem B2168957 : Blo 377762 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B115677341 : Blo 377762 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B858527 : Blo 377762 858527 := bstep (se 1 (by rfl) ⟨643895, by rfl⟩ : syracuseStep 858527 = 1287791) B1287791
theorem B1153511 : Blo 377762 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B858599 : Blo 377762 858599 := bstep (se 1 (by rfl) ⟨643949, by rfl⟩ : syracuseStep 858599 = 1287899) B1287899
theorem B2890241 : Blo 377762 2890241 := bstep (se 2 (by rfl) ⟨1083840, by rfl⟩ : syracuseStep 2890241 = 2167681) B2167681
theorem B2300599 : Blo 377762 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B1284875 : Blo 377762 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B1285145 : Blo 377762 1285145 := bstep (se 2 (by rfl) ⟨481929, by rfl⟩ : syracuseStep 1285145 = 963859) B963859
theorem B4398209 : Blo 377762 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B5905979 : Blo 377762 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B1220449 : Blo 377762 1220449 := bstep (se 2 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 1220449 = 915337) B915337
theorem B5447681 : Blo 377762 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B1286333 : Blo 377762 1286333 := bstep (se 3 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 1286333 = 482375) B482375
theorem B4628831 : Blo 377762 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B1286495 : Blo 377762 1286495 := bstep (se 1 (by rfl) ⟨964871, by rfl⟩ : syracuseStep 1286495 = 1929743) B1929743
theorem B434975 : Blo 377762 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B4596527 : Blo 377762 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B1221679 : Blo 377762 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B3712549 : Blo 377762 3712549 := bstep (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) B696103
theorem B2172581 : Blo 377762 2172581 := bstep (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) B407359
theorem B862015 : Blo 377762 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B31205209 : Blo 377762 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B731035 : Blo 377762 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B567263 : Blo 377762 567263 := bstep (se 1 (by rfl) ⟨425447, by rfl⟩ : syracuseStep 567263 = 850895) B850895
theorem B567275 : Blo 377762 567275 := bstep (se 1 (by rfl) ⟨425456, by rfl⟩ : syracuseStep 567275 = 850913) B850913
theorem B567323 : Blo 377762 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B2304295 : Blo 377762 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B567689 : Blo 377762 567689 := bstep (se 2 (by rfl) ⟨212883, by rfl⟩ : syracuseStep 567689 = 425767) B425767
theorem B2337767 : Blo 377762 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B4304015 : Blo 377762 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B568631 : Blo 377762 568631 := bstep (se 1 (by rfl) ⟨426473, by rfl⟩ : syracuseStep 568631 = 852947) B852947
theorem B1944911 : Blo 377762 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B568799 : Blo 377762 568799 := bstep (se 1 (by rfl) ⟨426599, by rfl⟩ : syracuseStep 568799 = 853199) B853199
theorem B118042181 : Blo 377762 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B569015 : Blo 377762 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B4599595 : Blo 377762 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B12922739 : Blo 377762 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B569225 : Blo 377762 569225 := bstep (se 2 (by rfl) ⟨213459, by rfl⟩ : syracuseStep 569225 = 426919) B426919
theorem B3256307 : Blo 377762 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B569471 : Blo 377762 569471 := bstep (se 1 (by rfl) ⟨427103, by rfl⟩ : syracuseStep 569471 = 854207) B854207
theorem B1028371 : Blo 377762 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B570107 : Blo 377762 570107 := bstep (se 1 (by rfl) ⟨427580, by rfl⟩ : syracuseStep 570107 = 855161) B855161
theorem B1618825 : Blo 377762 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B963535 : Blo 377762 963535 := bstep (se 1 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 963535 = 1445303) B1445303
theorem B767159 : Blo 377762 767159 := bstep (se 1 (by rfl) ⟨575369, by rfl⟩ : syracuseStep 767159 = 1150739) B1150739
theorem B570551 : Blo 377762 570551 := bstep (se 1 (by rfl) ⟨427913, by rfl⟩ : syracuseStep 570551 = 855827) B855827
theorem B4863341 : Blo 377762 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B570791 : Blo 377762 570791 := bstep (se 1 (by rfl) ⟨428093, by rfl⟩ : syracuseStep 570791 = 856187) B856187
theorem B570971 : Blo 377762 570971 := bstep (se 1 (by rfl) ⟨428228, by rfl⟩ : syracuseStep 570971 = 856457) B856457
theorem B571433 : Blo 377762 571433 := bstep (se 2 (by rfl) ⟨214287, by rfl⟩ : syracuseStep 571433 = 428575) B428575
theorem B964649 : Blo 377762 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B571463 : Blo 377762 571463 := bstep (se 1 (by rfl) ⟨428597, by rfl⟩ : syracuseStep 571463 = 857195) B857195
theorem B571847 : Blo 377762 571847 := bstep (se 1 (by rfl) ⟨428885, by rfl⟩ : syracuseStep 571847 = 857771) B857771
theorem B539227 : Blo 377762 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B572063 : Blo 377762 572063 := bstep (se 1 (by rfl) ⟨429047, by rfl⟩ : syracuseStep 572063 = 858095) B858095
theorem B572207 : Blo 377762 572207 := bstep (se 1 (by rfl) ⟨429155, by rfl⟩ : syracuseStep 572207 = 858311) B858311
theorem B572327 : Blo 377762 572327 := bstep (se 1 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 572327 = 858491) B858491
theorem B572507 : Blo 377762 572507 := bstep (se 1 (by rfl) ⟨429380, by rfl⟩ : syracuseStep 572507 = 858761) B858761
theorem B638057 : Blo 377762 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B1916135 : Blo 377762 1916135 := bstep (se 1 (by rfl) ⟨1437101, by rfl⟩ : syracuseStep 1916135 = 2874203) B2874203
theorem B1621235 : Blo 377762 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2080079 : Blo 377762 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B1031743 : Blo 377762 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B7126751 : Blo 377762 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B638887 : Blo 377762 638887 := bstep (se 1 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 638887 = 958331) B958331
theorem B3653657 : Blo 377762 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B1622207 : Blo 377762 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B639211 : Blo 377762 639211 := bstep (se 1 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 639211 = 958817) B958817
theorem B1295129 : Blo 377762 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B377903 : Blo 377762 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B377967 : Blo 377762 377967 := bstep (se 1 (by rfl) ⟨283475, by rfl⟩ : syracuseStep 377967 = 566951) B566951
theorem B378023 : Blo 377762 378023 := bstep (se 1 (by rfl) ⟨283517, by rfl⟩ : syracuseStep 378023 = 567035) B567035
theorem B378047 : Blo 377762 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B378079 : Blo 377762 378079 := bstep (se 1 (by rfl) ⟨283559, by rfl⟩ : syracuseStep 378079 = 567119) B567119
theorem B378159 : Blo 377762 378159 := bstep (se 1 (by rfl) ⟨283619, by rfl⟩ : syracuseStep 378159 = 567239) B567239
theorem B640507 : Blo 377762 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B3065363 : Blo 377762 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B378395 : Blo 377762 378395 := bstep (se 1 (by rfl) ⟨283796, by rfl⟩ : syracuseStep 378395 = 567593) B567593
theorem B23447069 : Blo 377762 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B378399 : Blo 377762 378399 := bstep (se 1 (by rfl) ⟨283799, by rfl⟩ : syracuseStep 378399 = 567599) B567599
theorem B2868857 : Blo 377762 2868857 := bstep (se 2 (by rfl) ⟨1075821, by rfl⟩ : syracuseStep 2868857 = 2151643) B2151643
theorem B378559 : Blo 377762 378559 := bstep (se 1 (by rfl) ⟨283919, by rfl⟩ : syracuseStep 378559 = 567839) B567839
theorem B640703 : Blo 377762 640703 := bstep (se 1 (by rfl) ⟨480527, by rfl⟩ : syracuseStep 640703 = 961055) B961055
theorem B3229379 : Blo 377762 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B8406773 : Blo 377762 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B378815 : Blo 377762 378815 := bstep (se 1 (by rfl) ⟨284111, by rfl⟩ : syracuseStep 378815 = 568223) B568223
theorem B378847 : Blo 377762 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B378907 : Blo 377762 378907 := bstep (se 1 (by rfl) ⟨284180, by rfl⟩ : syracuseStep 378907 = 568361) B568361
theorem B378911 : Blo 377762 378911 := bstep (se 1 (by rfl) ⟨284183, by rfl⟩ : syracuseStep 378911 = 568367) B568367
theorem B378927 : Blo 377762 378927 := bstep (se 1 (by rfl) ⟨284195, by rfl⟩ : syracuseStep 378927 = 568391) B568391
theorem B379103 : Blo 377762 379103 := bstep (se 1 (by rfl) ⟨284327, by rfl⟩ : syracuseStep 379103 = 568655) B568655
theorem B379163 : Blo 377762 379163 := bstep (se 1 (by rfl) ⟨284372, by rfl⟩ : syracuseStep 379163 = 568745) B568745
theorem B379263 : Blo 377762 379263 := bstep (se 1 (by rfl) ⟨284447, by rfl⟩ : syracuseStep 379263 = 568895) B568895
theorem B608681 : Blo 377762 608681 := bstep (se 2 (by rfl) ⟨228255, by rfl⟩ : syracuseStep 608681 = 456511) B456511
theorem B379439 : Blo 377762 379439 := bstep (se 1 (by rfl) ⟨284579, by rfl⟩ : syracuseStep 379439 = 569159) B569159
theorem B379495 : Blo 377762 379495 := bstep (se 1 (by rfl) ⟨284621, by rfl⟩ : syracuseStep 379495 = 569243) B569243
theorem B1624873 : Blo 377762 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B2050859 : Blo 377762 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1854251 : Blo 377762 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B4115387 : Blo 377762 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B379871 : Blo 377762 379871 := bstep (se 1 (by rfl) ⟨284903, by rfl⟩ : syracuseStep 379871 = 569807) B569807
theorem B379899 : Blo 377762 379899 := bstep (se 1 (by rfl) ⟨284924, by rfl⟩ : syracuseStep 379899 = 569849) B569849
theorem B379967 : Blo 377762 379967 := bstep (se 1 (by rfl) ⟨284975, by rfl⟩ : syracuseStep 379967 = 569951) B569951
theorem B478315 : Blo 377762 478315 := bstep (se 1 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 478315 = 717473) B717473
theorem B642235 : Blo 377762 642235 := bstep (se 1 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 642235 = 963353) B963353
theorem B380287 : Blo 377762 380287 := bstep (se 1 (by rfl) ⟨285215, by rfl⟩ : syracuseStep 380287 = 570431) B570431
theorem B642431 : Blo 377762 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B2608537 : Blo 377762 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B380315 : Blo 377762 380315 := bstep (se 1 (by rfl) ⟨285236, by rfl⟩ : syracuseStep 380315 = 570473) B570473
theorem B380383 : Blo 377762 380383 := bstep (se 1 (by rfl) ⟨285287, by rfl⟩ : syracuseStep 380383 = 570575) B570575
theorem B380519 : Blo 377762 380519 := bstep (se 1 (by rfl) ⟨285389, by rfl⟩ : syracuseStep 380519 = 570779) B570779
theorem B380667 : Blo 377762 380667 := bstep (se 1 (by rfl) ⟨285500, by rfl⟩ : syracuseStep 380667 = 571001) B571001
theorem B380735 : Blo 377762 380735 := bstep (se 1 (by rfl) ⟨285551, by rfl⟩ : syracuseStep 380735 = 571103) B571103
theorem B380799 : Blo 377762 380799 := bstep (se 1 (by rfl) ⟨285599, by rfl⟩ : syracuseStep 380799 = 571199) B571199
theorem B5459845 : Blo 377762 5459845 := bstep (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) B1023721
theorem B380911 : Blo 377762 380911 := bstep (se 1 (by rfl) ⟨285683, by rfl⟩ : syracuseStep 380911 = 571367) B571367
theorem B380923 : Blo 377762 380923 := bstep (se 1 (by rfl) ⟨285692, by rfl⟩ : syracuseStep 380923 = 571385) B571385
theorem B479287 : Blo 377762 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B380991 : Blo 377762 380991 := bstep (se 1 (by rfl) ⟨285743, by rfl⟩ : syracuseStep 380991 = 571487) B571487
theorem B3231839 : Blo 377762 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B577631 : Blo 377762 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B381031 : Blo 377762 381031 := bstep (se 1 (by rfl) ⟨285773, by rfl⟩ : syracuseStep 381031 = 571547) B571547
theorem B381055 : Blo 377762 381055 := bstep (se 1 (by rfl) ⟨285791, by rfl⟩ : syracuseStep 381055 = 571583) B571583
theorem B381083 : Blo 377762 381083 := bstep (se 1 (by rfl) ⟨285812, by rfl⟩ : syracuseStep 381083 = 571625) B571625
theorem B643369 : Blo 377762 643369 := bstep (se 2 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 643369 = 482527) B482527
theorem B381287 : Blo 377762 381287 := bstep (se 1 (by rfl) ⟨285965, by rfl⟩ : syracuseStep 381287 = 571931) B571931
theorem B381339 : Blo 377762 381339 := bstep (se 1 (by rfl) ⟨286004, by rfl⟩ : syracuseStep 381339 = 572009) B572009
theorem B643639 : Blo 377762 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B381691 : Blo 377762 381691 := bstep (se 1 (by rfl) ⟨286268, by rfl⟩ : syracuseStep 381691 = 572537) B572537
theorem B381759 : Blo 377762 381759 := bstep (se 1 (by rfl) ⟨286319, by rfl⟩ : syracuseStep 381759 = 572639) B572639
theorem B2872259 : Blo 377762 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B1169447 : Blo 377762 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B1923425 : Blo 377762 1923425 := bstep (se 2 (by rfl) ⟨721284, by rfl⟩ : syracuseStep 1923425 = 1442569) B1442569
theorem B3136745 : Blo 377762 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B1629521 : Blo 377762 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B1957225 : Blo 377762 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B1924883 : Blo 377762 1924883 := bstep (se 1 (by rfl) ⟨1443662, by rfl⟩ : syracuseStep 1924883 = 2887325) B2887325
theorem B1629983 : Blo 377762 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B1630135 : Blo 377762 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B810985 : Blo 377762 810985 := bstep (se 2 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 810985 = 608239) B608239
theorem B4121401 : Blo 377762 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B811873 : Blo 377762 811873 := bstep (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) B608905
theorem B20800421 : Blo 377762 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B5465495 : Blo 377762 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B1435583 : Blo 377762 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B911339 : Blo 377762 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B2877605 : Blo 377762 2877605 := bstep (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) B539551
theorem B568519397 : Blo 377762 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B1436555 : Blo 377762 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B912455 : Blo 377762 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B1535159 : Blo 377762 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B2223287 : Blo 377762 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B1437527 : Blo 377762 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B3665807 : Blo 377762 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B1536185 : Blo 377762 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B684443 : Blo 377762 684443 := bstep (se 1 (by rfl) ⟨513332, by rfl⟩ : syracuseStep 684443 = 1026665) B1026665
theorem B718247 : Blo 377762 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1079239 : Blo 377762 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B2160665 : Blo 377762 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B850103 : Blo 377762 850103 := bstep (se 1 (by rfl) ⟨637577, by rfl⟩ : syracuseStep 850103 = 1275155) B1275155
theorem B1439927 : Blo 377762 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B489655 : Blo 377762 489655 := bstep (se 1 (by rfl) ⟨367241, by rfl⟩ : syracuseStep 489655 = 734483) B734483
theorem B850463 : Blo 377762 850463 := bstep (se 1 (by rfl) ⟨637847, by rfl⟩ : syracuseStep 850463 = 1275695) B1275695
theorem B1440413 : Blo 377762 1440413 := bstep (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) B540155
theorem B850697 : Blo 377762 850697 := bstep (se 2 (by rfl) ⟨319011, by rfl⟩ : syracuseStep 850697 = 638023) B638023
theorem B1276829 : Blo 377762 1276829 := bstep (se 3 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 1276829 = 478811) B478811
theorem B425191 : Blo 377762 425191 := bstep (se 1 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 425191 = 637787) B637787
theorem B851273 : Blo 377762 851273 := bstep (se 2 (by rfl) ⟨319227, by rfl⟩ : syracuseStep 851273 = 638455) B638455
theorem B851687 : Blo 377762 851687 := bstep (se 1 (by rfl) ⟨638765, by rfl⟩ : syracuseStep 851687 = 1277531) B1277531
theorem B1081097 : Blo 377762 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B425839 : Blo 377762 425839 := bstep (se 1 (by rfl) ⟨319379, by rfl⟩ : syracuseStep 425839 = 638759) B638759
theorem B1540349 : Blo 377762 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B852281 : Blo 377762 852281 := bstep (se 2 (by rfl) ⟨319605, by rfl⟩ : syracuseStep 852281 = 639211) B639211
theorem B4096493 : Blo 377762 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B4325885 : Blo 377762 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B15631379 : Blo 377762 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B427135 : Blo 377762 427135 := bstep (se 1 (by rfl) ⟨320351, by rfl⟩ : syracuseStep 427135 = 640703) B640703
theorem B1082497 : Blo 377762 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B5604515 : Blo 377762 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B12289573 : Blo 377762 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B854009 : Blo 377762 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B4950065 : Blo 377762 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B854099 : Blo 377762 854099 := bstep (se 1 (by rfl) ⟨640574, by rfl⟩ : syracuseStep 854099 = 1281149) B1281149
theorem B12257405 : Blo 377762 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B428287 : Blo 377762 428287 := bstep (se 1 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 428287 = 642431) B642431
theorem B854279 : Blo 377762 854279 := bstep (se 1 (by rfl) ⟨640709, by rfl⟩ : syracuseStep 854279 = 1281419) B1281419
theorem B1149353 : Blo 377762 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B2165723 : Blo 377762 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B1314407 : Blo 377762 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1183403 : Blo 377762 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B2166497 : Blo 377762 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1445759 : Blo 377762 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B1445971 : Blo 377762 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B1282283 : Blo 377762 1282283 := bstep (se 1 (by rfl) ⟨961712, by rfl⟩ : syracuseStep 1282283 = 1923425) B1923425
theorem B856313 : Blo 377762 856313 := bstep (se 2 (by rfl) ⟨321117, by rfl⟩ : syracuseStep 856313 = 642235) B642235
theorem B856583 : Blo 377762 856583 := bstep (se 1 (by rfl) ⟨642437, by rfl⟩ : syracuseStep 856583 = 1284875) B1284875
theorem B3478049 : Blo 377762 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B856763 : Blo 377762 856763 := bstep (se 1 (by rfl) ⟨642572, by rfl⟩ : syracuseStep 856763 = 1285145) B1285145
theorem B1086347 : Blo 377762 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B3937319 : Blo 377762 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B6132793 : Blo 377762 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B7279793 : Blo 377762 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B1283255 : Blo 377762 1283255 := bstep (se 1 (by rfl) ⟨962441, by rfl⟩ : syracuseStep 1283255 = 1924883) B1924883
theorem B1086655 : Blo 377762 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B857555 : Blo 377762 857555 := bstep (se 1 (by rfl) ⟨643166, by rfl⟩ : syracuseStep 857555 = 1286333) B1286333
theorem B857663 : Blo 377762 857663 := bstep (se 1 (by rfl) ⟨643247, by rfl⟩ : syracuseStep 857663 = 1286495) B1286495
theorem B857825 : Blo 377762 857825 := bstep (se 2 (by rfl) ⟨321684, by rfl⟩ : syracuseStep 857825 = 643369) B643369
theorem B13866947 : Blo 377762 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B858185 : Blo 377762 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B3643663 : Blo 377762 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B1448387 : Blo 377762 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B1284713 : Blo 377762 1284713 := bstep (se 2 (by rfl) ⟨481767, by rfl⟩ : syracuseStep 1284713 = 963535) B963535
theorem B957055 : Blo 377762 957055 := bstep (se 1 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 957055 = 1435583) B1435583
theorem B957703 : Blo 377762 957703 := bstep (se 1 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 957703 = 1436555) B1436555
theorem B1482191 : Blo 377762 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B958351 : Blo 377762 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B2170871 : Blo 377762 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B8364653 : Blo 377762 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B566735 : Blo 377762 566735 := bstep (se 1 (by rfl) ⟨425051, by rfl⟩ : syracuseStep 566735 = 850103) B850103
theorem B959951 : Blo 377762 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B566921 : Blo 377762 566921 := bstep (se 2 (by rfl) ⟨212595, by rfl⟩ : syracuseStep 566921 = 425191) B425191
theorem B566975 : Blo 377762 566975 := bstep (se 1 (by rfl) ⟨425231, by rfl⟩ : syracuseStep 566975 = 850463) B850463
theorem B960275 : Blo 377762 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B567131 : Blo 377762 567131 := bstep (se 1 (by rfl) ⟨425348, by rfl⟩ : syracuseStep 567131 = 850697) B850697
theorem B567515 : Blo 377762 567515 := bstep (se 1 (by rfl) ⟨425636, by rfl⟩ : syracuseStep 567515 = 851273) B851273
theorem B1386719 : Blo 377762 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B567785 : Blo 377762 567785 := bstep (se 2 (by rfl) ⟨212919, by rfl⟩ : syracuseStep 567785 = 425839) B425839
theorem B567791 : Blo 377762 567791 := bstep (se 1 (by rfl) ⟨425843, by rfl⟩ : syracuseStep 567791 = 851687) B851687
theorem B2173513 : Blo 377762 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B2435771 : Blo 377762 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B568103 : Blo 377762 568103 := bstep (se 1 (by rfl) ⟨426077, by rfl⟩ : syracuseStep 568103 = 852155) B852155
theorem B568175 : Blo 377762 568175 := bstep (se 1 (by rfl) ⟨426131, by rfl⟩ : syracuseStep 568175 = 852263) B852263
theorem B568427 : Blo 377762 568427 := bstep (se 1 (by rfl) ⟨426320, by rfl⟩ : syracuseStep 568427 = 852641) B852641
theorem B568667 : Blo 377762 568667 := bstep (se 1 (by rfl) ⟨426500, by rfl⟩ : syracuseStep 568667 = 853001) B853001
theorem B568697 : Blo 377762 568697 := bstep (se 2 (by rfl) ⟨213261, by rfl⟩ : syracuseStep 568697 = 426523) B426523
theorem B568703 : Blo 377762 568703 := bstep (se 1 (by rfl) ⟨426527, by rfl⟩ : syracuseStep 568703 = 853055) B853055
theorem B568937 : Blo 377762 568937 := bstep (se 2 (by rfl) ⟨213351, by rfl⟩ : syracuseStep 568937 = 426703) B426703
theorem B2043575 : Blo 377762 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B962239 : Blo 377762 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B1912571 : Blo 377762 1912571 := bstep (se 1 (by rfl) ⟨1434428, by rfl⟩ : syracuseStep 1912571 = 2868857) B2868857
theorem B569327 : Blo 377762 569327 := bstep (se 1 (by rfl) ⟨426995, by rfl⟩ : syracuseStep 569327 = 853991) B853991
theorem B569447 : Blo 377762 569447 := bstep (se 1 (by rfl) ⟨427085, by rfl⟩ : syracuseStep 569447 = 854171) B854171
theorem B569567 : Blo 377762 569567 := bstep (se 1 (by rfl) ⟨427175, by rfl⟩ : syracuseStep 569567 = 854351) B854351
theorem B7385363 : Blo 377762 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B569627 : Blo 377762 569627 := bstep (se 1 (by rfl) ⟨427220, by rfl⟩ : syracuseStep 569627 = 854441) B854441
theorem B570023 : Blo 377762 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B3453677 : Blo 377762 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B963323 : Blo 377762 963323 := bstep (se 1 (by rfl) ⟨722492, by rfl⟩ : syracuseStep 963323 = 1444985) B1444985
theorem B1159933 : Blo 377762 1159933 := bstep (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) B434975
theorem B570143 : Blo 377762 570143 := bstep (se 1 (by rfl) ⟨427607, by rfl⟩ : syracuseStep 570143 = 855215) B855215
theorem B570167 : Blo 377762 570167 := bstep (se 1 (by rfl) ⟨427625, by rfl⟩ : syracuseStep 570167 = 855251) B855251
theorem B570281 : Blo 377762 570281 := bstep (se 2 (by rfl) ⟨213855, by rfl⟩ : syracuseStep 570281 = 427711) B427711
theorem B4109291 : Blo 377762 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B570347 : Blo 377762 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B570623 : Blo 377762 570623 := bstep (se 1 (by rfl) ⟨427967, by rfl⟩ : syracuseStep 570623 = 855935) B855935
theorem B570665 : Blo 377762 570665 := bstep (se 2 (by rfl) ⟨213999, by rfl⟩ : syracuseStep 570665 = 427999) B427999
theorem B1029971 : Blo 377762 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B571259 : Blo 377762 571259 := bstep (se 1 (by rfl) ⟨428444, by rfl⟩ : syracuseStep 571259 = 856889) B856889
theorem B571295 : Blo 377762 571295 := bstep (se 1 (by rfl) ⟨428471, by rfl⟩ : syracuseStep 571295 = 856943) B856943
theorem B1914839 : Blo 377762 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B571499 : Blo 377762 571499 := bstep (se 1 (by rfl) ⟨428624, by rfl⟩ : syracuseStep 571499 = 857249) B857249
theorem B571529 : Blo 377762 571529 := bstep (se 2 (by rfl) ⟨214323, by rfl⟩ : syracuseStep 571529 = 428647) B428647
theorem B768287 : Blo 377762 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B571679 : Blo 377762 571679 := bstep (se 1 (by rfl) ⟨428759, by rfl⟩ : syracuseStep 571679 = 857519) B857519
theorem B1915325 : Blo 377762 1915325 := bstep (se 3 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 1915325 = 718247) B718247
theorem B77118227 : Blo 377762 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B637753 : Blo 377762 637753 := bstep (se 2 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 637753 = 478315) B478315
theorem B572351 : Blo 377762 572351 := bstep (se 1 (by rfl) ⟨429263, by rfl⟩ : syracuseStep 572351 = 858527) B858527
theorem B769007 : Blo 377762 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B572399 : Blo 377762 572399 := bstep (se 1 (by rfl) ⟨429299, by rfl⟩ : syracuseStep 572399 = 858599) B858599
theorem B965753 : Blo 377762 965753 := bstep (se 2 (by rfl) ⟨362157, by rfl⟩ : syracuseStep 965753 = 724315) B724315
theorem B572585 : Blo 377762 572585 := bstep (se 2 (by rfl) ⟨214719, by rfl⟩ : syracuseStep 572585 = 429439) B429439
theorem B2932139 : Blo 377762 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B4112441 : Blo 377762 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B639049 : Blo 377762 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B1623149 : Blo 377762 1623149 := bstep (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) B608681
theorem B378175 : Blo 377762 378175 := bstep (se 1 (by rfl) ⟨283631, by rfl⟩ : syracuseStep 378175 = 567263) B567263
theorem B378183 : Blo 377762 378183 := bstep (se 1 (by rfl) ⟨283637, by rfl⟩ : syracuseStep 378183 = 567275) B567275
theorem B607559 : Blo 377762 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B378215 : Blo 377762 378215 := bstep (se 1 (by rfl) ⟨283661, by rfl⟩ : syracuseStep 378215 = 567323) B567323
theorem B1918403 : Blo 377762 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B378459 : Blo 377762 378459 := bstep (se 1 (by rfl) ⟨283844, by rfl⟩ : syracuseStep 378459 = 567689) B567689
theorem B379012931 : Blo 377762 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B1558511 : Blo 377762 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B608303 : Blo 377762 608303 := bstep (se 1 (by rfl) ⟨456227, by rfl⟩ : syracuseStep 608303 = 912455) B912455
theorem B2869343 : Blo 377762 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B1755245 : Blo 377762 1755245 := bstep (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) B658217
theorem B379087 : Blo 377762 379087 := bstep (se 1 (by rfl) ⟨284315, by rfl⟩ : syracuseStep 379087 = 568631) B568631
theorem B1296607 : Blo 377762 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B379199 : Blo 377762 379199 := bstep (se 1 (by rfl) ⟨284399, by rfl⟩ : syracuseStep 379199 = 568799) B568799
theorem B78694787 : Blo 377762 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B379343 : Blo 377762 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B379483 : Blo 377762 379483 := bstep (se 1 (by rfl) ⟨284612, by rfl⟩ : syracuseStep 379483 = 569225) B569225
theorem B2443871 : Blo 377762 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B379647 : Blo 377762 379647 := bstep (se 1 (by rfl) ⟨284735, by rfl⟩ : syracuseStep 379647 = 569471) B569471
theorem B380071 : Blo 377762 380071 := bstep (se 1 (by rfl) ⟨285053, by rfl⟩ : syracuseStep 380071 = 570107) B570107
theorem B511439 : Blo 377762 511439 := bstep (se 1 (by rfl) ⟨383579, by rfl⟩ : syracuseStep 511439 = 767159) B767159
theorem B380367 : Blo 377762 380367 := bstep (se 1 (by rfl) ⟨285275, by rfl⟩ : syracuseStep 380367 = 570551) B570551
theorem B3067465 : Blo 377762 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B380527 : Blo 377762 380527 := bstep (se 1 (by rfl) ⟨285395, by rfl⟩ : syracuseStep 380527 = 570791) B570791
theorem B380647 : Blo 377762 380647 := bstep (se 1 (by rfl) ⟨285485, by rfl⟩ : syracuseStep 380647 = 570971) B570971
theorem B380955 : Blo 377762 380955 := bstep (se 1 (by rfl) ⟨285716, by rfl⟩ : syracuseStep 380955 = 571433) B571433
theorem B643099 : Blo 377762 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B380975 : Blo 377762 380975 := bstep (se 1 (by rfl) ⟨285731, by rfl⟩ : syracuseStep 380975 = 571463) B571463
theorem B381231 : Blo 377762 381231 := bstep (se 1 (by rfl) ⟨285923, by rfl⟩ : syracuseStep 381231 = 571847) B571847
theorem B381375 : Blo 377762 381375 := bstep (se 1 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 381375 = 572063) B572063
theorem B2609633 : Blo 377762 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B381471 : Blo 377762 381471 := bstep (se 1 (by rfl) ⟨286103, by rfl⟩ : syracuseStep 381471 = 572207) B572207
theorem B381551 : Blo 377762 381551 := bstep (se 1 (by rfl) ⟨286163, by rfl⟩ : syracuseStep 381551 = 572327) B572327
theorem B381671 : Blo 377762 381671 := bstep (se 1 (by rfl) ⟨286253, by rfl⟩ : syracuseStep 381671 = 572507) B572507
theorem B1627265 : Blo 377762 1627265 := bstep (se 2 (by rfl) ⟨610224, by rfl⟩ : syracuseStep 1627265 = 1220449) B1220449
theorem B874127 : Blo 377762 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B12474101 : Blo 377762 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B1922939 : Blo 377762 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B12343549 : Blo 377762 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B2611493 : Blo 377762 2611493 := bstep (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) B489655
theorem B5495201 : Blo 377762 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B2152919 : Blo 377762 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B1628905 : Blo 377762 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B1923911 : Blo 377762 1923911 := bstep (se 1 (by rfl) ⟨1442933, by rfl⟩ : syracuseStep 1923911 = 2885867) B2885867
theorem B1236167 : Blo 377762 1236167 := bstep (se 1 (by rfl) ⟨927125, by rfl⟩ : syracuseStep 1236167 = 1854251) B1854251
theorem B2743591 : Blo 377762 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B41606945 : Blo 377762 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B2154559 : Blo 377762 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B2318483 : Blo 377762 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B1925369 : Blo 377762 1925369 := bstep (se 2 (by rfl) ⟨722013, by rfl⟩ : syracuseStep 1925369 = 1444027) B1444027
theorem B812027 : Blo 377762 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B1926665 : Blo 377762 1926665 := bstep (se 2 (by rfl) ⟨722499, by rfl⟩ : syracuseStep 1926665 = 1444999) B1444999
theorem B1926827 : Blo 377762 1926827 := bstep (se 1 (by rfl) ⟨1445120, by rfl⟩ : syracuseStep 1926827 = 2890241) B2890241
theorem B3631787 : Blo 377762 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B1371161 : Blo 377762 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B2158433 : Blo 377762 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B2977769 : Blo 377762 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B1929581 : Blo 377762 1929581 := bstep (se 3 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 1929581 = 723593) B723593
theorem B5468957 : Blo 377762 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B8615159 : Blo 377762 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B1438985 : Blo 377762 1438985 := bstep (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) B1079239
theorem B1275209 : Blo 377762 1275209 := bstep (se 2 (by rfl) ⟨478203, by rfl⟩ : syracuseStep 1275209 = 956407) B956407
theorem B456295 : Blo 377762 456295 := bstep (se 1 (by rfl) ⟨342221, by rfl⟩ : syracuseStep 456295 = 684443) B684443
theorem B5502629 : Blo 377762 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B4093757 : Blo 377762 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B718969 : Blo 377762 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B3242227 : Blo 377762 3242227 := bstep (se 1 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 3242227 = 4863341) B4863341
theorem B1440443 : Blo 377762 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B19004669 : Blo 377762 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B851219 : Blo 377762 851219 := bstep (se 1 (by rfl) ⟨638414, by rfl⟩ : syracuseStep 851219 = 1276829) B1276829
theorem B425371 : Blo 377762 425371 := bstep (se 1 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 425371 = 638057) B638057
theorem B3898853 : Blo 377762 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B1277423 : Blo 377762 1277423 := bstep (se 1 (by rfl) ⟨958067, by rfl⟩ : syracuseStep 1277423 = 1916135) B1916135
theorem B1080823 : Blo 377762 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B720731 : Blo 377762 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B851849 : Blo 377762 851849 := bstep (se 2 (by rfl) ⟨319443, by rfl⟩ : syracuseStep 851849 = 638887) B638887
theorem B1081313 : Blo 377762 1081313 := bstep (se 2 (by rfl) ⟨405492, by rfl⟩ : syracuseStep 1081313 = 810985) B810985
theorem B852065 : Blo 377762 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B2883923 : Blo 377762 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B10420919 : Blo 377762 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B1082099 : Blo 377762 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B3736343 : Blo 377762 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B1278935 : Blo 377762 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B252675287 : Blo 377762 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B1443329 : Blo 377762 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B1443815 : Blo 377762 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B16386097 : Blo 377762 16386097 := bstep (se 2 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 16386097 = 12289573) B12289573
theorem B788935 : Blo 377762 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B1444331 : Blo 377762 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B854855 : Blo 377762 854855 := bstep (se 1 (by rfl) ⟨641141, by rfl⟩ : syracuseStep 854855 = 1282283) B1282283
theorem B1739755 : Blo 377762 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B724231 : Blo 377762 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B2624879 : Blo 377762 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1084843 : Blo 377762 1084843 := bstep (se 1 (by rfl) ⟨813632, by rfl⟩ : syracuseStep 1084843 = 1627265) B1627265
theorem B4853195 : Blo 377762 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B855503 : Blo 377762 855503 := bstep (se 1 (by rfl) ⟨641627, by rfl⟩ : syracuseStep 855503 = 1283255) B1283255
theorem B1281959 : Blo 377762 1281959 := bstep (se 1 (by rfl) ⟨961469, by rfl⟩ : syracuseStep 1281959 = 1922939) B1922939
theorem B9244631 : Blo 377762 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B1740995 : Blo 377762 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B856475 : Blo 377762 856475 := bstep (se 1 (by rfl) ⟨642356, by rfl⟩ : syracuseStep 856475 = 1284713) B1284713
theorem B1282607 : Blo 377762 1282607 := bstep (se 1 (by rfl) ⟨961955, by rfl⟩ : syracuseStep 1282607 = 1923911) B1923911
theorem B824111 : Blo 377762 824111 := bstep (se 1 (by rfl) ⟨618083, by rfl⟩ : syracuseStep 824111 = 1236167) B1236167
theorem B1282985 : Blo 377762 1282985 := bstep (se 2 (by rfl) ⟨481119, by rfl⟩ : syracuseStep 1282985 = 962239) B962239
theorem B988127 : Blo 377762 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B1447247 : Blo 377762 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B857465 : Blo 377762 857465 := bstep (se 2 (by rfl) ⟨321549, by rfl⟩ : syracuseStep 857465 = 643099) B643099
theorem B1545655 : Blo 377762 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1283579 : Blo 377762 1283579 := bstep (se 1 (by rfl) ⟨962684, by rfl⟩ : syracuseStep 1283579 = 1925369) B1925369
theorem B5576435 : Blo 377762 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B1546577 : Blo 377762 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B1284443 : Blo 377762 1284443 := bstep (se 1 (by rfl) ⟨963332, by rfl⟩ : syracuseStep 1284443 = 1926665) B1926665
theorem B209852765 : Blo 377762 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B1284551 : Blo 377762 1284551 := bstep (se 1 (by rfl) ⟨963413, by rfl⟩ : syracuseStep 1284551 = 1926827) B1926827
theorem B924479 : Blo 377762 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B1448873 : Blo 377762 1448873 := bstep (se 2 (by rfl) ⟨543327, by rfl⟩ : syracuseStep 1448873 = 1086655) B1086655
theorem B6495389 : Blo 377762 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B958625 : Blo 377762 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B4923575 : Blo 377762 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B1286387 : Blo 377762 1286387 := bstep (se 1 (by rfl) ⟨964790, by rfl⟩ : syracuseStep 1286387 = 1929581) B1929581
theorem B16458065 : Blo 377762 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B4858217 : Blo 377762 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B2302451 : Blo 377762 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B3645971 : Blo 377762 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B5743439 : Blo 377762 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B959323 : Blo 377762 959323 := bstep (se 1 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 959323 = 1438985) B1438985
theorem B2171873 : Blo 377762 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2729171 : Blo 377762 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B960295 : Blo 377762 960295 := bstep (se 1 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 960295 = 1440443) B1440443
theorem B567161 : Blo 377762 567161 := bstep (se 2 (by rfl) ⟨212685, by rfl⟩ : syracuseStep 567161 = 425371) B425371
theorem B567479 : Blo 377762 567479 := bstep (se 1 (by rfl) ⟨425609, by rfl⟩ : syracuseStep 567479 = 851219) B851219
theorem B2599235 : Blo 377762 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B567899 : Blo 377762 567899 := bstep (se 1 (by rfl) ⟨425924, by rfl⟩ : syracuseStep 567899 = 851849) B851849
theorem B7940717 : Blo 377762 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B1026899 : Blo 377762 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B568187 : Blo 377762 568187 := bstep (se 1 (by rfl) ⟨426140, by rfl⟩ : syracuseStep 568187 = 852281) B852281
theorem B2730995 : Blo 377762 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B569339 : Blo 377762 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B405535 : Blo 377762 405535 := bstep (se 1 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 405535 = 608303) B608303
theorem B569399 : Blo 377762 569399 := bstep (se 1 (by rfl) ⟨427049, by rfl⟩ : syracuseStep 569399 = 854099) B854099
theorem B1912895 : Blo 377762 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B8171603 : Blo 377762 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B569513 : Blo 377762 569513 := bstep (se 2 (by rfl) ⟨213567, by rfl⟩ : syracuseStep 569513 = 427135) B427135
theorem B569519 : Blo 377762 569519 := bstep (se 1 (by rfl) ⟨427139, by rfl⟩ : syracuseStep 569519 = 854279) B854279
theorem B766235 : Blo 377762 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B963839 : Blo 377762 963839 := bstep (se 1 (by rfl) ⟨722879, by rfl⟩ : syracuseStep 963839 = 1445759) B1445759
theorem B570875 : Blo 377762 570875 := bstep (se 1 (by rfl) ⟨428156, by rfl⟩ : syracuseStep 570875 = 856313) B856313
theorem B571049 : Blo 377762 571049 := bstep (se 2 (by rfl) ⟨214143, by rfl⟩ : syracuseStep 571049 = 428287) B428287
theorem B571055 : Blo 377762 571055 := bstep (se 1 (by rfl) ⟨428291, by rfl⟩ : syracuseStep 571055 = 856583) B856583
theorem B571175 : Blo 377762 571175 := bstep (se 1 (by rfl) ⟨428381, by rfl⟩ : syracuseStep 571175 = 856763) B856763
theorem B2898017 : Blo 377762 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B1620157 : Blo 377762 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B571703 : Blo 377762 571703 := bstep (se 1 (by rfl) ⟨428777, by rfl⟩ : syracuseStep 571703 = 857555) B857555
theorem B571775 : Blo 377762 571775 := bstep (se 1 (by rfl) ⟨428831, by rfl⟩ : syracuseStep 571775 = 857663) B857663
theorem B571883 : Blo 377762 571883 := bstep (se 1 (by rfl) ⟨428912, by rfl⟩ : syracuseStep 571883 = 857825) B857825
theorem B572123 : Blo 377762 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B965591 : Blo 377762 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B5455349 : Blo 377762 5455349 := bstep (se 5 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 5455349 = 511439) B511439
theorem B27737963 : Blo 377762 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B541351 : Blo 377762 541351 := bstep (se 1 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 541351 = 812027) B812027
theorem B377823 : Blo 377762 377823 := bstep (se 1 (by rfl) ⟨283367, by rfl⟩ : syracuseStep 377823 = 566735) B566735
theorem B639967 : Blo 377762 639967 := bstep (se 1 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 639967 = 959951) B959951
theorem B377947 : Blo 377762 377947 := bstep (se 1 (by rfl) ⟨283460, by rfl⟩ : syracuseStep 377947 = 566921) B566921
theorem B377983 : Blo 377762 377983 := bstep (se 1 (by rfl) ⟨283487, by rfl⟩ : syracuseStep 377983 = 566975) B566975
theorem B640183 : Blo 377762 640183 := bstep (se 1 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 640183 = 960275) B960275
theorem B378087 : Blo 377762 378087 := bstep (se 1 (by rfl) ⟨283565, by rfl⟩ : syracuseStep 378087 = 567131) B567131
theorem B8177057 : Blo 377762 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B378343 : Blo 377762 378343 := bstep (se 1 (by rfl) ⟨283757, by rfl⟩ : syracuseStep 378343 = 567515) B567515
theorem B378523 : Blo 377762 378523 := bstep (se 1 (by rfl) ⟨283892, by rfl⟩ : syracuseStep 378523 = 567785) B567785
theorem B378527 : Blo 377762 378527 := bstep (se 1 (by rfl) ⟨283895, by rfl⟩ : syracuseStep 378527 = 567791) B567791
theorem B378735 : Blo 377762 378735 := bstep (se 1 (by rfl) ⟨284051, by rfl⟩ : syracuseStep 378735 = 568103) B568103
theorem B378783 : Blo 377762 378783 := bstep (se 1 (by rfl) ⟨284087, by rfl⟩ : syracuseStep 378783 = 568175) B568175
theorem B378951 : Blo 377762 378951 := bstep (se 1 (by rfl) ⟨284213, by rfl⟩ : syracuseStep 378951 = 568427) B568427
theorem B608393 : Blo 377762 608393 := bstep (se 2 (by rfl) ⟨228147, by rfl⟩ : syracuseStep 608393 = 456295) B456295
theorem B379111 : Blo 377762 379111 := bstep (se 1 (by rfl) ⟨284333, by rfl⟩ : syracuseStep 379111 = 568667) B568667
theorem B379131 : Blo 377762 379131 := bstep (se 1 (by rfl) ⟨284348, by rfl⟩ : syracuseStep 379131 = 568697) B568697
theorem B379135 : Blo 377762 379135 := bstep (se 1 (by rfl) ⟨284351, by rfl⟩ : syracuseStep 379135 = 568703) B568703
theorem B379291 : Blo 377762 379291 := bstep (se 1 (by rfl) ⟨284468, by rfl⟩ : syracuseStep 379291 = 568937) B568937
theorem B1362383 : Blo 377762 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B2050685 : Blo 377762 2050685 := bstep (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) B769007
theorem B379551 : Blo 377762 379551 := bstep (se 1 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 379551 = 569327) B569327
theorem B379631 : Blo 377762 379631 := bstep (se 1 (by rfl) ⟨284723, by rfl⟩ : syracuseStep 379631 = 569447) B569447
theorem B379711 : Blo 377762 379711 := bstep (se 1 (by rfl) ⟨284783, by rfl⟩ : syracuseStep 379711 = 569567) B569567
theorem B379751 : Blo 377762 379751 := bstep (se 1 (by rfl) ⟨284813, by rfl⟩ : syracuseStep 379751 = 569627) B569627
theorem B380015 : Blo 377762 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B642215 : Blo 377762 642215 := bstep (se 1 (by rfl) ⟨481661, by rfl⟩ : syracuseStep 642215 = 963323) B963323
theorem B380095 : Blo 377762 380095 := bstep (se 1 (by rfl) ⟨285071, by rfl⟩ : syracuseStep 380095 = 570143) B570143
theorem B380111 : Blo 377762 380111 := bstep (se 1 (by rfl) ⟨285083, by rfl⟩ : syracuseStep 380111 = 570167) B570167
theorem B380187 : Blo 377762 380187 := bstep (se 1 (by rfl) ⟨285140, by rfl⟩ : syracuseStep 380187 = 570281) B570281
theorem B2739527 : Blo 377762 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B380231 : Blo 377762 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B380415 : Blo 377762 380415 := bstep (se 1 (by rfl) ⟨285311, by rfl⟩ : syracuseStep 380415 = 570623) B570623
theorem B380443 : Blo 377762 380443 := bstep (se 1 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 380443 = 570665) B570665
theorem B380839 : Blo 377762 380839 := bstep (se 1 (by rfl) ⟨285629, by rfl⟩ : syracuseStep 380839 = 571259) B571259
theorem B380863 : Blo 377762 380863 := bstep (se 1 (by rfl) ⟨285647, by rfl⟩ : syracuseStep 380863 = 571295) B571295
theorem B380999 : Blo 377762 380999 := bstep (se 1 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 380999 = 571499) B571499
theorem B381019 : Blo 377762 381019 := bstep (se 1 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 381019 = 571529) B571529
theorem B512191 : Blo 377762 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B381119 : Blo 377762 381119 := bstep (se 1 (by rfl) ⟨285839, by rfl⟩ : syracuseStep 381119 = 571679) B571679
theorem B3658121 : Blo 377762 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B381567 : Blo 377762 381567 := bstep (se 1 (by rfl) ⟨286175, by rfl⟩ : syracuseStep 381567 = 572351) B572351
theorem B381599 : Blo 377762 381599 := bstep (se 1 (by rfl) ⟨286199, by rfl⟩ : syracuseStep 381599 = 572399) B572399
theorem B643835 : Blo 377762 643835 := bstep (se 1 (by rfl) ⟨482876, by rfl⟩ : syracuseStep 643835 = 965753) B965753
theorem B381723 : Blo 377762 381723 := bstep (se 1 (by rfl) ⟨286292, by rfl⟩ : syracuseStep 381723 = 572585) B572585
theorem B12669779 : Blo 377762 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B1954759 : Blo 377762 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B480487 : Blo 377762 480487 := bstep (se 1 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 480487 = 720731) B720731
theorem B2741627 : Blo 377762 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B2872745 : Blo 377762 2872745 := bstep (se 2 (by rfl) ⟨1077279, by rfl⟩ : syracuseStep 2872745 = 2154559) B2154559
theorem B1039007 : Blo 377762 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B3300043 : Blo 377762 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B1170163 : Blo 377762 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1629247 : Blo 377762 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B876271 : Blo 377762 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B1728809 : Blo 377762 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B2318699 : Blo 377762 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B582751 : Blo 377762 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B8316067 : Blo 377762 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B3663467 : Blo 377762 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B1435279 : Blo 377762 1435279 := bstep (se 1 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 1435279 = 2152919) B2152919
theorem B4089953 : Blo 377762 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B1927961 : Blo 377762 1927961 := bstep (se 2 (by rfl) ⟨722985, by rfl⟩ : syracuseStep 1927961 = 1445971) B1445971
theorem B2421191 : Blo 377762 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B914107 : Blo 377762 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1275047 : Blo 377762 1275047 := bstep (se 1 (by rfl) ⟨956285, by rfl⟩ : syracuseStep 1275047 = 1912571) B1912571
theorem B1438955 : Blo 377762 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B4322969 : Blo 377762 4322969 := bstep (se 2 (by rfl) ⟨1621113, by rfl⟩ : syracuseStep 4322969 = 3242227) B3242227
theorem B1276073 : Blo 377762 1276073 := bstep (se 2 (by rfl) ⟨478527, by rfl⟩ : syracuseStep 1276073 = 957055) B957055
theorem B850139 : Blo 377762 850139 := bstep (se 1 (by rfl) ⟨637604, by rfl⟩ : syracuseStep 850139 = 1275209) B1275209
theorem B850337 : Blo 377762 850337 := bstep (se 2 (by rfl) ⟨318876, by rfl⟩ : syracuseStep 850337 = 637753) B637753
theorem B3668419 : Blo 377762 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B686647 : Blo 377762 686647 := bstep (se 1 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 686647 = 1029971) B1029971
theorem B1276559 : Blo 377762 1276559 := bstep (se 1 (by rfl) ⟨957419, by rfl⟩ : syracuseStep 1276559 = 1914839) B1914839
theorem B1276883 : Blo 377762 1276883 := bstep (se 1 (by rfl) ⟨957662, by rfl⟩ : syracuseStep 1276883 = 1915325) B1915325
theorem B1276937 : Blo 377762 1276937 := bstep (se 2 (by rfl) ⟨478851, by rfl⟩ : syracuseStep 1276937 = 957703) B957703
theorem B51412151 : Blo 377762 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B1441097 : Blo 377762 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B851615 : Blo 377762 851615 := bstep (se 1 (by rfl) ⟨638711, by rfl⟩ : syracuseStep 851615 = 1277423) B1277423
theorem B1277801 : Blo 377762 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B720875 : Blo 377762 720875 := bstep (se 1 (by rfl) ⟨540656, by rfl⟩ : syracuseStep 720875 = 1081313) B1081313
theorem B6947279 : Blo 377762 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B721399 : Blo 377762 721399 := bstep (se 1 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 721399 = 1082099) B1082099
theorem B2490895 : Blo 377762 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B852623 : Blo 377762 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B721801 : Blo 377762 721801 := bstep (se 2 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 721801 = 541351) B541351
theorem B1279097 : Blo 377762 1279097 := bstep (se 2 (by rfl) ⟨479661, by rfl⟩ : syracuseStep 1279097 = 959323) B959323
theorem B853289 : Blo 377762 853289 := bstep (se 2 (by rfl) ⟨319983, by rfl⟩ : syracuseStep 853289 = 639967) B639967
theorem B853577 : Blo 377762 853577 := bstep (se 2 (by rfl) ⟨320091, by rfl⟩ : syracuseStep 853577 = 640183) B640183
theorem B428143 : Blo 377762 428143 := bstep (se 1 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 428143 = 642215) B642215
theorem B1280393 : Blo 377762 1280393 := bstep (se 2 (by rfl) ⟨480147, by rfl⟩ : syracuseStep 1280393 = 960295) B960295
theorem B854639 : Blo 377762 854639 := bstep (se 1 (by rfl) ⟨640979, by rfl⟩ : syracuseStep 854639 = 1281959) B1281959
theorem B6163087 : Blo 377762 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B855071 : Blo 377762 855071 := bstep (se 1 (by rfl) ⟨641303, by rfl⟩ : syracuseStep 855071 = 1282607) B1282607
theorem B429223 : Blo 377762 429223 := bstep (se 1 (by rfl) ⟨321917, by rfl⟩ : syracuseStep 429223 = 643835) B643835
theorem B7277789 : Blo 377762 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B1051913 : Blo 377762 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B855323 : Blo 377762 855323 := bstep (se 1 (by rfl) ⟨641492, by rfl⟩ : syracuseStep 855323 = 1282985) B1282985
theorem B658751 : Blo 377762 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B7311005 : Blo 377762 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B855719 : Blo 377762 855719 := bstep (se 1 (by rfl) ⟨641789, by rfl⟩ : syracuseStep 855719 = 1283579) B1283579
theorem B856295 : Blo 377762 856295 := bstep (se 1 (by rfl) ⟨642221, by rfl⟩ : syracuseStep 856295 = 1284443) B1284443
theorem B856367 : Blo 377762 856367 := bstep (se 1 (by rfl) ⟨642275, by rfl⟩ : syracuseStep 856367 = 1284551) B1284551
theorem B1446457 : Blo 377762 1446457 := bstep (se 2 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 1446457 = 1084843) B1084843
theorem B4330259 : Blo 377762 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B3282383 : Blo 377762 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B857591 : Blo 377762 857591 := bstep (se 1 (by rfl) ⟨643193, by rfl⟩ : syracuseStep 857591 = 1286387) B1286387
theorem B1152539 : Blo 377762 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B1545799 : Blo 377762 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B2430647 : Blo 377762 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B1447915 : Blo 377762 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1218809 : Blo 377762 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B2726635 : Blo 377762 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B1285307 : Blo 377762 1285307 := bstep (se 1 (by rfl) ⟨963980, by rfl⟩ : syracuseStep 1285307 = 1927961) B1927961
theorem B5447735 : Blo 377762 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B1614127 : Blo 377762 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B4891225 : Blo 377762 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B959303 : Blo 377762 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B10953589 : Blo 377762 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B4400057 : Blo 377762 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B2172329 : Blo 377762 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B566759 : Blo 377762 566759 := bstep (se 1 (by rfl) ⟨425069, by rfl⟩ : syracuseStep 566759 = 850139) B850139
theorem B566891 : Blo 377762 566891 := bstep (se 1 (by rfl) ⟨425168, by rfl⟩ : syracuseStep 566891 = 850337) B850337
theorem B960731 : Blo 377762 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B567743 : Blo 377762 567743 := bstep (se 1 (by rfl) ⟨425807, by rfl⟩ : syracuseStep 567743 = 851615) B851615
theorem B18491975 : Blo 377762 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B568043 : Blo 377762 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B5451371 : Blo 377762 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B962219 : Blo 377762 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B962543 : Blo 377762 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B405595 : Blo 377762 405595 := bstep (se 1 (by rfl) ⟨304196, by rfl⟩ : syracuseStep 405595 = 608393) B608393
theorem B11088089 : Blo 377762 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B962887 : Blo 377762 962887 := bstep (se 1 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 962887 = 1444331) B1444331
theorem B569903 : Blo 377762 569903 := bstep (se 1 (by rfl) ⟨427427, by rfl⟩ : syracuseStep 569903 = 854855) B854855
theorem B1913705 : Blo 377762 1913705 := bstep (se 2 (by rfl) ⟨717639, by rfl⟩ : syracuseStep 1913705 = 1435279) B1435279
theorem B1749919 : Blo 377762 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B570335 : Blo 377762 570335 := bstep (se 1 (by rfl) ⟨427751, by rfl⟩ : syracuseStep 570335 = 855503) B855503
theorem B1160663 : Blo 377762 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B2438747 : Blo 377762 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B570983 : Blo 377762 570983 := bstep (se 1 (by rfl) ⟨428237, by rfl⟩ : syracuseStep 570983 = 856475) B856475
theorem B964831 : Blo 377762 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B571643 : Blo 377762 571643 := bstep (se 1 (by rfl) ⟨428732, by rfl⟩ : syracuseStep 571643 = 857465) B857465
theorem B1915163 : Blo 377762 1915163 := bstep (se 1 (by rfl) ⟨1436372, by rfl⟩ : syracuseStep 1915163 = 2872745) B2872745
theorem B3717623 : Blo 377762 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B1031051 : Blo 377762 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B139901843 : Blo 377762 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B965641 : Blo 377762 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B965915 : Blo 377762 965915 := bstep (se 1 (by rfl) ⟨724436, by rfl⟩ : syracuseStep 965915 = 1448873) B1448873
theorem B540713 : Blo 377762 540713 := bstep (se 2 (by rfl) ⟨202767, by rfl⟩ : syracuseStep 540713 = 405535) B405535
theorem B639083 : Blo 377762 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B2442311 : Blo 377762 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B378107 : Blo 377762 378107 := bstep (se 1 (by rfl) ⟨283580, by rfl⟩ : syracuseStep 378107 = 567161) B567161
theorem B2606345 : Blo 377762 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B378319 : Blo 377762 378319 := bstep (se 1 (by rfl) ⟨283739, by rfl⟩ : syracuseStep 378319 = 567479) B567479
theorem B640649 : Blo 377762 640649 := bstep (se 2 (by rfl) ⟨240243, by rfl⟩ : syracuseStep 640649 = 480487) B480487
theorem B378599 : Blo 377762 378599 := bstep (se 1 (by rfl) ⟨283949, by rfl⟩ : syracuseStep 378599 = 567899) B567899
theorem B5293811 : Blo 377762 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2770685 : Blo 377762 2770685 := bstep (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) B1039007
theorem B378791 : Blo 377762 378791 := bstep (se 1 (by rfl) ⟨284093, by rfl⟩ : syracuseStep 378791 = 568187) B568187
theorem B1820663 : Blo 377762 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B379559 : Blo 377762 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B379599 : Blo 377762 379599 := bstep (se 1 (by rfl) ⟨284699, by rfl⟩ : syracuseStep 379599 = 569399) B569399
theorem B379675 : Blo 377762 379675 := bstep (se 1 (by rfl) ⟨284756, by rfl⟩ : syracuseStep 379675 = 569513) B569513
theorem B379679 : Blo 377762 379679 := bstep (se 1 (by rfl) ⟨284759, by rfl⟩ : syracuseStep 379679 = 569519) B569519
theorem B510823 : Blo 377762 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B642559 : Blo 377762 642559 := bstep (se 1 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 642559 = 963839) B963839
theorem B1560217 : Blo 377762 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B380583 : Blo 377762 380583 := bstep (se 1 (by rfl) ⟨285437, by rfl⟩ : syracuseStep 380583 = 570875) B570875
theorem B380699 : Blo 377762 380699 := bstep (se 1 (by rfl) ⟨285524, by rfl⟩ : syracuseStep 380699 = 571049) B571049
theorem B380703 : Blo 377762 380703 := bstep (se 1 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 380703 = 571055) B571055
theorem B380783 : Blo 377762 380783 := bstep (se 1 (by rfl) ⟨285587, by rfl⟩ : syracuseStep 380783 = 571175) B571175
theorem B381135 : Blo 377762 381135 := bstep (se 1 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 381135 = 571703) B571703
theorem B381183 : Blo 377762 381183 := bstep (se 1 (by rfl) ⟨285887, by rfl⟩ : syracuseStep 381183 = 571775) B571775
theorem B381255 : Blo 377762 381255 := bstep (se 1 (by rfl) ⟨285941, by rfl⟩ : syracuseStep 381255 = 571883) B571883
theorem B381415 : Blo 377762 381415 := bstep (se 1 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 381415 = 572123) B572123
theorem B643727 : Blo 377762 643727 := bstep (se 1 (by rfl) ⟨482795, by rfl⟩ : syracuseStep 643727 = 965591) B965591
theorem B1168361 : Blo 377762 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B480583 : Blo 377762 480583 := bstep (se 1 (by rfl) ⟨360437, by rfl⟩ : syracuseStep 480583 = 720875) B720875
theorem B1922615 : Blo 377762 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B168450191 : Blo 377762 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B777001 : Blo 377762 777001 := bstep (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) B582751
theorem B908255 : Blo 377762 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B1367123 : Blo 377762 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B1826351 : Blo 377762 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B3235463 : Blo 377762 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B21848129 : Blo 377762 21848129 := bstep (se 2 (by rfl) ⟨8193048, by rfl⟩ : syracuseStep 21848129 = 16386097) B16386097
theorem B3662117 : Blo 377762 3662117 := bstep (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) B686647
theorem B549407 : Blo 377762 549407 := bstep (se 1 (by rfl) ⟨412055, by rfl⟩ : syracuseStep 549407 = 824111) B824111
theorem B8446519 : Blo 377762 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B2319673 : Blo 377762 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B616319 : Blo 377762 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B10972043 : Blo 377762 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B3238811 : Blo 377762 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B682921 : Blo 377762 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B1534967 : Blo 377762 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B3828959 : Blo 377762 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1732823 : Blo 377762 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B2060873 : Blo 377762 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B1275263 : Blo 377762 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B2160209 : Blo 377762 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B850031 : Blo 377762 850031 := bstep (se 1 (by rfl) ⟨637523, by rfl⟩ : syracuseStep 850031 = 1275047) B1275047
theorem B2881979 : Blo 377762 2881979 := bstep (se 1 (by rfl) ⟨2161484, by rfl⟩ : syracuseStep 2881979 = 4322969) B4322969
theorem B1932011 : Blo 377762 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B850715 : Blo 377762 850715 := bstep (se 1 (by rfl) ⟨638036, by rfl⟩ : syracuseStep 850715 = 1276073) B1276073
theorem B851039 : Blo 377762 851039 := bstep (se 1 (by rfl) ⟨638279, by rfl⟩ : syracuseStep 851039 = 1276559) B1276559
theorem B851255 : Blo 377762 851255 := bstep (se 1 (by rfl) ⟨638441, by rfl⟩ : syracuseStep 851255 = 1276883) B1276883
theorem B851291 : Blo 377762 851291 := bstep (se 1 (by rfl) ⟨638468, by rfl⟩ : syracuseStep 851291 = 1276937) B1276937
theorem B34274767 : Blo 377762 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B3636899 : Blo 377762 3636899 := bstep (se 1 (by rfl) ⟨2727674, by rfl⟩ : syracuseStep 3636899 = 5455349) B5455349
theorem B851867 : Blo 377762 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B426055 : Blo 377762 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B1441901 : Blo 377762 1441901 := bstep (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) B540713
theorem B852731 : Blo 377762 852731 := bstep (se 1 (by rfl) ⟨639548, by rfl⟩ : syracuseStep 852731 = 1279097) B1279097
theorem B6521633 : Blo 377762 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B1737563 : Blo 377762 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B427099 : Blo 377762 427099 := bstep (se 1 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 427099 = 640649) B640649
theorem B1213775 : Blo 377762 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B853595 : Blo 377762 853595 := bstep (se 1 (by rfl) ⟨640196, by rfl⟩ : syracuseStep 853595 = 1280393) B1280393
theorem B4851859 : Blo 377762 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B429151 : Blo 377762 429151 := bstep (se 1 (by rfl) ⟨321863, by rfl⟩ : syracuseStep 429151 = 643727) B643727
theorem B2886839 : Blo 377762 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B1281743 : Blo 377762 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B112300127 : Blo 377762 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B856745 : Blo 377762 856745 := bstep (se 2 (by rfl) ⟨321279, by rfl⟩ : syracuseStep 856745 = 642559) B642559
theorem B856871 : Blo 377762 856871 := bstep (se 1 (by rfl) ⟨642653, by rfl⟩ : syracuseStep 856871 = 1285307) B1285307
theorem B3642245 : Blo 377762 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1217567 : Blo 377762 1217567 := bstep (se 1 (by rfl) ⟨913175, by rfl⟩ : syracuseStep 1217567 = 1826351) B1826351
theorem B1283849 : Blo 377762 1283849 := bstep (se 2 (by rfl) ⟨481443, by rfl⟩ : syracuseStep 1283849 = 962887) B962887
theorem B1448219 : Blo 377762 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B2333225 : Blo 377762 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B12327983 : Blo 377762 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B7314695 : Blo 377762 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1023311 : Blo 377762 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B1155215 : Blo 377762 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B3645661 : Blo 377762 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B1286441 : Blo 377762 1286441 := bstep (se 2 (by rfl) ⟨482415, by rfl⟩ : syracuseStep 1286441 = 964831) B964831
theorem B1287521 : Blo 377762 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B566687 : Blo 377762 566687 := bstep (se 1 (by rfl) ⟨425015, by rfl⟩ : syracuseStep 566687 = 850031) B850031
theorem B1288007 : Blo 377762 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B567143 : Blo 377762 567143 := bstep (se 1 (by rfl) ⟨425357, by rfl⟩ : syracuseStep 567143 = 850715) B850715
theorem B93267895 : Blo 377762 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B567359 : Blo 377762 567359 := bstep (se 1 (by rfl) ⟨425519, by rfl⟩ : syracuseStep 567359 = 851039) B851039
theorem B567503 : Blo 377762 567503 := bstep (se 1 (by rfl) ⟨425627, by rfl⟩ : syracuseStep 567503 = 851255) B851255
theorem B567527 : Blo 377762 567527 := bstep (se 1 (by rfl) ⟨425645, by rfl⟩ : syracuseStep 567527 = 851291) B851291
theorem B567911 : Blo 377762 567911 := bstep (se 1 (by rfl) ⟨425933, by rfl⟩ : syracuseStep 567911 = 851867) B851867
theorem B4631519 : Blo 377762 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B568415 : Blo 377762 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B961865 : Blo 377762 961865 := bstep (se 2 (by rfl) ⟨360699, by rfl⟩ : syracuseStep 961865 = 721399) B721399
theorem B568859 : Blo 377762 568859 := bstep (se 1 (by rfl) ⟨426644, by rfl⟩ : syracuseStep 568859 = 853289) B853289
theorem B569051 : Blo 377762 569051 := bstep (se 1 (by rfl) ⟨426788, by rfl⟩ : syracuseStep 569051 = 853577) B853577
theorem B1847123 : Blo 377762 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B962401 : Blo 377762 962401 := bstep (se 2 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 962401 = 721801) B721801
theorem B569759 : Blo 377762 569759 := bstep (se 1 (by rfl) ⟨427319, by rfl⟩ : syracuseStep 569759 = 854639) B854639
theorem B3092897 : Blo 377762 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B570047 : Blo 377762 570047 := bstep (se 1 (by rfl) ⟨427535, by rfl⟩ : syracuseStep 570047 = 855071) B855071
theorem B570215 : Blo 377762 570215 := bstep (se 1 (by rfl) ⟨427661, by rfl⟩ : syracuseStep 570215 = 855323) B855323
theorem B570479 : Blo 377762 570479 := bstep (se 1 (by rfl) ⟨427859, by rfl⟩ : syracuseStep 570479 = 855719) B855719
theorem B13284773 : Blo 377762 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B570857 : Blo 377762 570857 := bstep (se 2 (by rfl) ⟨214071, by rfl⟩ : syracuseStep 570857 = 428143) B428143
theorem B570863 : Blo 377762 570863 := bstep (se 1 (by rfl) ⟨428147, by rfl⟩ : syracuseStep 570863 = 856295) B856295
theorem B570911 : Blo 377762 570911 := bstep (se 1 (by rfl) ⟨428183, by rfl⟩ : syracuseStep 570911 = 856367) B856367
theorem B571727 : Blo 377762 571727 := bstep (se 1 (by rfl) ⟨428795, by rfl⟩ : syracuseStep 571727 = 857591) B857591
theorem B768359 : Blo 377762 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B1620431 : Blo 377762 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B3095101 : Blo 377762 3095101 := bstep (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) B1160663
theorem B572297 : Blo 377762 572297 := bstep (se 2 (by rfl) ⟨214611, by rfl⟩ : syracuseStep 572297 = 429223) B429223
theorem B605503 : Blo 377762 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B2080289 : Blo 377762 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B14565419 : Blo 377762 14565419 := bstep (se 1 (by rfl) ⟨10924064, by rfl⟩ : syracuseStep 14565419 = 21848129) B21848129
theorem B540793 : Blo 377762 540793 := bstep (se 2 (by rfl) ⟨202797, by rfl⟩ : syracuseStep 540793 = 405595) B405595
theorem B2441411 : Blo 377762 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B639535 : Blo 377762 639535 := bstep (se 1 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 639535 = 959303) B959303
theorem B2933371 : Blo 377762 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B377839 : Blo 377762 377839 := bstep (se 1 (by rfl) ⟨283379, by rfl⟩ : syracuseStep 377839 = 566759) B566759
theorem B377927 : Blo 377762 377927 := bstep (se 1 (by rfl) ⟨283445, by rfl⟩ : syracuseStep 377927 = 566891) B566891
theorem B410879 : Blo 377762 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B9913661 : Blo 377762 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B640487 : Blo 377762 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B378495 : Blo 377762 378495 := bstep (se 1 (by rfl) ⟨283871, by rfl⟩ : syracuseStep 378495 = 567743) B567743
theorem B640777 : Blo 377762 640777 := bstep (se 2 (by rfl) ⟨240291, by rfl⟩ : syracuseStep 640777 = 480583) B480583
theorem B378695 : Blo 377762 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B641479 : Blo 377762 641479 := bstep (se 1 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 641479 = 962219) B962219
theorem B641695 : Blo 377762 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B7392059 : Blo 377762 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B379935 : Blo 377762 379935 := bstep (se 1 (by rfl) ⟨284951, by rfl⟩ : syracuseStep 379935 = 569903) B569903
theorem B380223 : Blo 377762 380223 := bstep (se 1 (by rfl) ⟨285167, by rfl⟩ : syracuseStep 380223 = 570335) B570335
theorem B2805101 : Blo 377762 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B1756669 : Blo 377762 1756669 := bstep (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) B658751
theorem B1036001 : Blo 377762 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B1625831 : Blo 377762 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B380655 : Blo 377762 380655 := bstep (se 1 (by rfl) ⟨285491, by rfl⟩ : syracuseStep 380655 = 570983) B570983
theorem B381095 : Blo 377762 381095 := bstep (se 1 (by rfl) ⟨285821, by rfl⟩ : syracuseStep 381095 = 571643) B571643
theorem B1921319 : Blo 377762 1921319 := bstep (se 1 (by rfl) ⟨1440989, by rfl⟩ : syracuseStep 1921319 = 2881979) B2881979
theorem B45699689 : Blo 377762 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B643943 : Blo 377762 643943 := bstep (se 1 (by rfl) ⟨482957, by rfl⟩ : syracuseStep 643943 = 965915) B965915
theorem B2152169 : Blo 377762 2152169 := bstep (se 2 (by rfl) ⟨807063, by rfl⟩ : syracuseStep 2152169 = 1614127) B1614127
theorem B1628207 : Blo 377762 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B11262025 : Blo 377762 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B14604785 : Blo 377762 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B3529207 : Blo 377762 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1465085 : Blo 377762 1465085 := bstep (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) B549407
theorem B4874003 : Blo 377762 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B778907 : Blo 377762 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B8217449 : Blo 377762 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B2188255 : Blo 377762 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B681097 : Blo 377762 681097 := bstep (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) B510823
theorem B812539 : Blo 377762 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B2156975 : Blo 377762 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B3631823 : Blo 377762 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B1928609 : Blo 377762 1928609 := bstep (se 2 (by rfl) ⟨723228, by rfl⟩ : syracuseStep 1928609 = 1446457) B1446457
theorem B2159207 : Blo 377762 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B2061065 : Blo 377762 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B2552639 : Blo 377762 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B2749469 : Blo 377762 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B3634247 : Blo 377762 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B1930553 : Blo 377762 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B1373915 : Blo 377762 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B1275803 : Blo 377762 1275803 := bstep (se 1 (by rfl) ⟨956852, by rfl⟩ : syracuseStep 1275803 = 1913705) B1913705
theorem B850175 : Blo 377762 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B3635513 : Blo 377762 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1440139 : Blo 377762 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B1276775 : Blo 377762 1276775 := bstep (se 1 (by rfl) ⟨957581, by rfl⟩ : syracuseStep 1276775 = 1915163) B1915163
theorem B2424599 : Blo 377762 2424599 := bstep (se 1 (by rfl) ⟨1818449, by rfl⟩ : syracuseStep 2424599 = 3636899) B3636899
theorem B721057 : Blo 377762 721057 := bstep (se 2 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 721057 = 540793) B540793
theorem B852713 : Blo 377762 852713 := bstep (se 2 (by rfl) ⟨319767, by rfl⟩ : syracuseStep 852713 = 639535) B639535
theorem B426991 : Blo 377762 426991 := bstep (se 1 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 426991 = 640487) B640487
theorem B2917673 : Blo 377762 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B1083385 : Blo 377762 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B1870067 : Blo 377762 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B854369 : Blo 377762 854369 := bstep (se 2 (by rfl) ⟨320388, by rfl⟩ : syracuseStep 854369 = 640777) B640777
theorem B854495 : Blo 377762 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B1083887 : Blo 377762 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B124357193 : Blo 377762 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B1280879 : Blo 377762 1280879 := bstep (se 1 (by rfl) ⟨960659, by rfl⟩ : syracuseStep 1280879 = 1921319) B1921319
theorem B429295 : Blo 377762 429295 := bstep (se 1 (by rfl) ⟨321971, by rfl⟩ : syracuseStep 429295 = 643943) B643943
theorem B2428163 : Blo 377762 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B855305 : Blo 377762 855305 := bstep (se 2 (by rfl) ⟨320739, by rfl⟩ : syracuseStep 855305 = 641479) B641479
theorem B855593 : Blo 377762 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B855899 : Blo 377762 855899 := bstep (se 1 (by rfl) ⟨641924, by rfl⟩ : syracuseStep 855899 = 1283849) B1283849
theorem B1085471 : Blo 377762 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B9736523 : Blo 377762 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B1283201 : Blo 377762 1283201 := bstep (se 2 (by rfl) ⟨481200, by rfl⟩ : syracuseStep 1283201 = 962401) B962401
theorem B3249335 : Blo 377762 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B857627 : Blo 377762 857627 := bstep (se 1 (by rfl) ⟨643220, by rfl⟩ : syracuseStep 857627 = 1286441) B1286441
theorem B5478299 : Blo 377762 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B858347 : Blo 377762 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B858671 : Blo 377762 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B3087679 : Blo 377762 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B3906893 : Blo 377762 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B1285739 : Blo 377762 1285739 := bstep (se 1 (by rfl) ⟨964304, by rfl⟩ : syracuseStep 1285739 = 1928609) B1928609
theorem B15016033 : Blo 377762 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1287035 : Blo 377762 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B2728829 : Blo 377762 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B8856515 : Blo 377762 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B5547437 : Blo 377762 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B566783 : Blo 377762 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B2762669 : Blo 377762 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B1616399 : Blo 377762 1616399 := bstep (se 1 (by rfl) ⟨1212299, by rfl⟩ : syracuseStep 1616399 = 2424599) B2424599
theorem B9710279 : Blo 377762 9710279 := bstep (se 1 (by rfl) ⟨7282709, by rfl⟩ : syracuseStep 9710279 = 14565419) B14565419
theorem B961267 : Blo 377762 961267 := bstep (se 1 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 961267 = 1441901) B1441901
theorem B568073 : Blo 377762 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B4860881 : Blo 377762 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B568487 : Blo 377762 568487 := bstep (se 1 (by rfl) ⟨426365, by rfl⟩ : syracuseStep 568487 = 852731) B852731
theorem B3911161 : Blo 377762 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B569063 : Blo 377762 569063 := bstep (se 1 (by rfl) ⟨426797, by rfl⟩ : syracuseStep 569063 = 853595) B853595
theorem B569465 : Blo 377762 569465 := bstep (se 2 (by rfl) ⟨213549, by rfl⟩ : syracuseStep 569465 = 427099) B427099
theorem B2077085 : Blo 377762 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B4928039 : Blo 377762 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B6469145 : Blo 377762 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B571163 : Blo 377762 571163 := bstep (se 1 (by rfl) ⟨428372, by rfl⟩ : syracuseStep 571163 = 856745) B856745
theorem B571247 : Blo 377762 571247 := bstep (se 1 (by rfl) ⟨428435, by rfl⟩ : syracuseStep 571247 = 856871) B856871
theorem B1095677 : Blo 377762 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B572201 : Blo 377762 572201 := bstep (se 2 (by rfl) ⟨214575, by rfl⟩ : syracuseStep 572201 = 429151) B429151
theorem B965479 : Blo 377762 965479 := bstep (se 1 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 965479 = 1448219) B1448219
theorem B2342225 : Blo 377762 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B770143 : Blo 377762 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B377791 : Blo 377762 377791 := bstep (se 1 (by rfl) ⟨283343, by rfl⟩ : syracuseStep 377791 = 566687) B566687
theorem B378095 : Blo 377762 378095 := bstep (se 1 (by rfl) ⟨283571, by rfl⟩ : syracuseStep 378095 = 567143) B567143
theorem B378239 : Blo 377762 378239 := bstep (se 1 (by rfl) ⟨283679, by rfl⟩ : syracuseStep 378239 = 567359) B567359
theorem B378335 : Blo 377762 378335 := bstep (se 1 (by rfl) ⟨283751, by rfl⟩ : syracuseStep 378335 = 567503) B567503
theorem B378351 : Blo 377762 378351 := bstep (se 1 (by rfl) ⟨283763, by rfl⟩ : syracuseStep 378351 = 567527) B567527
theorem B378607 : Blo 377762 378607 := bstep (se 1 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 378607 = 567911) B567911
theorem B378943 : Blo 377762 378943 := bstep (se 1 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 378943 = 568415) B568415
theorem B641243 : Blo 377762 641243 := bstep (se 1 (by rfl) ⟨480932, by rfl⟩ : syracuseStep 641243 = 961865) B961865
theorem B379239 : Blo 377762 379239 := bstep (se 1 (by rfl) ⟨284429, by rfl⟩ : syracuseStep 379239 = 568859) B568859
theorem B379367 : Blo 377762 379367 := bstep (se 1 (by rfl) ⟨284525, by rfl⟩ : syracuseStep 379367 = 569051) B569051
theorem B1231415 : Blo 377762 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B379839 : Blo 377762 379839 := bstep (se 1 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 379839 = 569759) B569759
theorem B380031 : Blo 377762 380031 := bstep (se 1 (by rfl) ⟨285023, by rfl⟩ : syracuseStep 380031 = 570047) B570047
theorem B1920185 : Blo 377762 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B380143 : Blo 377762 380143 := bstep (se 1 (by rfl) ⟨285107, by rfl⟩ : syracuseStep 380143 = 570215) B570215
theorem B4705609 : Blo 377762 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B380319 : Blo 377762 380319 := bstep (se 1 (by rfl) ⟨285239, by rfl⟩ : syracuseStep 380319 = 570479) B570479
theorem B18534005 : Blo 377762 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B380571 : Blo 377762 380571 := bstep (se 1 (by rfl) ⟨285428, by rfl⟩ : syracuseStep 380571 = 570857) B570857
theorem B380575 : Blo 377762 380575 := bstep (se 1 (by rfl) ⟨285431, by rfl⟩ : syracuseStep 380575 = 570863) B570863
theorem B380607 : Blo 377762 380607 := bstep (se 1 (by rfl) ⟨285455, by rfl⟩ : syracuseStep 380607 = 570911) B570911
theorem B381151 : Blo 377762 381151 := bstep (se 1 (by rfl) ⟨285863, by rfl⟩ : syracuseStep 381151 = 571727) B571727
theorem B512239 : Blo 377762 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B807337 : Blo 377762 807337 := bstep (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) B605503
theorem B381531 : Blo 377762 381531 := bstep (se 1 (by rfl) ⟨286148, by rfl⟩ : syracuseStep 381531 = 572297) B572297
theorem B1627607 : Blo 377762 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B4347755 : Blo 377762 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B6609107 : Blo 377762 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B809183 : Blo 377762 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B908129 : Blo 377762 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B5496173 : Blo 377762 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B1924559 : Blo 377762 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B74866751 : Blo 377762 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B7331917 : Blo 377762 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B30466459 : Blo 377762 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B811711 : Blo 377762 811711 := bstep (se 1 (by rfl) ⟨608783, by rfl⟩ : syracuseStep 811711 = 1217567) B1217567
theorem B1434779 : Blo 377762 1434779 := bstep (se 1 (by rfl) ⟨1076084, by rfl⟩ : syracuseStep 1434779 = 2152169) B2152169
theorem B8218655 : Blo 377762 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4876463 : Blo 377762 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B6221933 : Blo 377762 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1437983 : Blo 377762 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B2421215 : Blo 377762 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B2061931 : Blo 377762 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1439471 : Blo 377762 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B27228149 : Blo 377762 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B2422831 : Blo 377762 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B4126801 : Blo 377762 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B915943 : Blo 377762 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B850535 : Blo 377762 850535 := bstep (se 1 (by rfl) ⟨637901, by rfl⟩ : syracuseStep 850535 = 1275803) B1275803
theorem B2423675 : Blo 377762 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B1080287 : Blo 377762 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B851183 : Blo 377762 851183 := bstep (se 1 (by rfl) ⟨638387, by rfl⟩ : syracuseStep 851183 = 1276775) B1276775
theorem B20021377 : Blo 377762 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B1082281 : Blo 377762 1082281 := bstep (se 2 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 1082281 = 811711) B811711
theorem B5538893 : Blo 377762 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B427495 : Blo 377762 427495 := bstep (se 1 (by rfl) ⟨320621, by rfl⟩ : syracuseStep 427495 = 641243) B641243
theorem B722591 : Blo 377762 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B820943 : Blo 377762 820943 := bstep (se 1 (by rfl) ⟨615707, by rfl⟩ : syracuseStep 820943 = 1231415) B1231415
theorem B82904795 : Blo 377762 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B853919 : Blo 377762 853919 := bstep (se 1 (by rfl) ⟨640439, by rfl⟩ : syracuseStep 853919 = 1280879) B1280879
theorem B1280123 : Blo 377762 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B12356003 : Blo 377762 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B1444513 : Blo 377762 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B723647 : Blo 377762 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B6491015 : Blo 377762 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B855467 : Blo 377762 855467 := bstep (se 1 (by rfl) ⟨641600, by rfl⟩ : syracuseStep 855467 = 1283201) B1283201
theorem B2166223 : Blo 377762 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B1085071 : Blo 377762 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B1281689 : Blo 377762 1281689 := bstep (se 2 (by rfl) ⟨480633, by rfl⟩ : syracuseStep 1281689 = 961267) B961267
theorem B5214881 : Blo 377762 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B1283039 : Blo 377762 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B857159 : Blo 377762 857159 := bstep (se 1 (by rfl) ⟨642869, by rfl⟩ : syracuseStep 857159 = 1285739) B1285739
theorem B49911167 : Blo 377762 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B858023 : Blo 377762 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B5904343 : Blo 377762 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B4986845 : Blo 377762 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B956519 : Blo 377762 956519 := bstep (se 1 (by rfl) ⟨717389, by rfl⟩ : syracuseStep 956519 = 1434779) B1434779
theorem B1841779 : Blo 377762 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B5479103 : Blo 377762 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B3250975 : Blo 377762 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B958655 : Blo 377762 958655 := bstep (se 1 (by rfl) ⟨718991, by rfl⟩ : syracuseStep 958655 = 1437983) B1437983
theorem B1614143 : Blo 377762 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B3285359 : Blo 377762 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B1221257 : Blo 377762 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B1287305 : Blo 377762 1287305 := bstep (se 2 (by rfl) ⟨482739, by rfl⟩ : syracuseStep 1287305 = 965479) B965479
theorem B959647 : Blo 377762 959647 := bstep (se 1 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 959647 = 1439471) B1439471
theorem B730451 : Blo 377762 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B567023 : Blo 377762 567023 := bstep (se 1 (by rfl) ⟨425267, by rfl⟩ : syracuseStep 567023 = 850535) B850535
theorem B1615783 : Blo 377762 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B567455 : Blo 377762 567455 := bstep (se 1 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 567455 = 851183) B851183
theorem B9775889 : Blo 377762 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B1026857 : Blo 377762 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B961409 : Blo 377762 961409 := bstep (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) B721057
theorem B568475 : Blo 377762 568475 := bstep (se 1 (by rfl) ⟨426356, by rfl⟩ : syracuseStep 568475 = 852713) B852713
theorem B1945115 : Blo 377762 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B569321 : Blo 377762 569321 := bstep (se 2 (by rfl) ⟨213495, by rfl⟩ : syracuseStep 569321 = 426991) B426991
theorem B569579 : Blo 377762 569579 := bstep (se 1 (by rfl) ⟨427184, by rfl⟩ : syracuseStep 569579 = 854369) B854369
theorem B569663 : Blo 377762 569663 := bstep (se 1 (by rfl) ⟨427247, by rfl⟩ : syracuseStep 569663 = 854495) B854495
theorem B1618775 : Blo 377762 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B570203 : Blo 377762 570203 := bstep (se 1 (by rfl) ⟨427652, by rfl⟩ : syracuseStep 570203 = 855305) B855305
theorem B570395 : Blo 377762 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B570599 : Blo 377762 570599 := bstep (se 1 (by rfl) ⟨427949, by rfl⟩ : syracuseStep 570599 = 855899) B855899
theorem B571751 : Blo 377762 571751 := bstep (se 1 (by rfl) ⟨428813, by rfl⟩ : syracuseStep 571751 = 857627) B857627
theorem B2898503 : Blo 377762 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B3652199 : Blo 377762 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B4406071 : Blo 377762 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B539455 : Blo 377762 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B572231 : Blo 377762 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B572393 : Blo 377762 572393 := bstep (se 2 (by rfl) ⟨214647, by rfl⟩ : syracuseStep 572393 = 429295) B429295
theorem B572447 : Blo 377762 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B6274145 : Blo 377762 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B2604595 : Blo 377762 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B1819219 : Blo 377762 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B377855 : Blo 377762 377855 := bstep (se 1 (by rfl) ⟨283391, by rfl⟩ : syracuseStep 377855 = 566783) B566783
theorem B6473519 : Blo 377762 6473519 := bstep (se 1 (by rfl) ⟨4855139, by rfl⟩ : syracuseStep 6473519 = 9710279) B9710279
theorem B378715 : Blo 377762 378715 := bstep (se 1 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 378715 = 568073) B568073
theorem B378991 : Blo 377762 378991 := bstep (se 1 (by rfl) ⟨284243, by rfl⟩ : syracuseStep 378991 = 568487) B568487
theorem B379375 : Blo 377762 379375 := bstep (se 1 (by rfl) ⟨284531, by rfl⟩ : syracuseStep 379375 = 569063) B569063
theorem B3230441 : Blo 377762 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B4147955 : Blo 377762 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B379643 : Blo 377762 379643 := bstep (se 1 (by rfl) ⟨284732, by rfl⟩ : syracuseStep 379643 = 569465) B569465
theorem B4312763 : Blo 377762 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B380775 : Blo 377762 380775 := bstep (se 1 (by rfl) ⟨285581, by rfl⟩ : syracuseStep 380775 = 571163) B571163
theorem B380831 : Blo 377762 380831 := bstep (se 1 (by rfl) ⟨285623, by rfl⟩ : syracuseStep 380831 = 571247) B571247
theorem B4116905 : Blo 377762 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B381467 : Blo 377762 381467 := bstep (se 1 (by rfl) ⟨286100, by rfl⟩ : syracuseStep 381467 = 572201) B572201
theorem B1561483 : Blo 377762 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B162487781 : Blo 377762 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B3664115 : Blo 377762 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B682985 : Blo 377762 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B1076449 : Blo 377762 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B3698291 : Blo 377762 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1077599 : Blo 377762 1077599 := bstep (se 1 (by rfl) ⟨808199, by rfl⟩ : syracuseStep 1077599 = 1616399) B1616399
theorem B3240587 : Blo 377762 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2749241 : Blo 377762 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B2421677 : Blo 377762 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B5502401 : Blo 377762 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B18152099 : Blo 377762 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B720191 : Blo 377762 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B2425625 : Blo 377762 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B59081525 : Blo 377762 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B1443041 : Blo 377762 1443041 := bstep (se 2 (by rfl) ⟨541140, by rfl⟩ : syracuseStep 1443041 = 1082281) B1082281
theorem B853415 : Blo 377762 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B1279529 : Blo 377762 1279529 := bstep (se 2 (by rfl) ⟨479823, by rfl⟩ : syracuseStep 1279529 = 959647) B959647
theorem B4327343 : Blo 377762 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B854459 : Blo 377762 854459 := bstep (se 1 (by rfl) ⟨640844, by rfl⟩ : syracuseStep 854459 = 1281689) B1281689
theorem B855359 : Blo 377762 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B2888297 : Blo 377762 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B8327909 : Blo 377762 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B1446761 : Blo 377762 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B858203 : Blo 377762 858203 := bstep (se 1 (by rfl) ⟨643652, by rfl⟩ : syracuseStep 858203 = 1287305) B1287305
theorem B2465527 : Blo 377762 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B1614451 : Blo 377762 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B4334633 : Blo 377762 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B5874761 : Blo 377762 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B2434799 : Blo 377762 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B12101399 : Blo 377762 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B569279 : Blo 377762 569279 := bstep (se 1 (by rfl) ⟨426959, by rfl⟩ : syracuseStep 569279 = 853919) B853919
theorem B3256685 : Blo 377762 3256685 := bstep (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) B1221257
theorem B13906349 : Blo 377762 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B2765303 : Blo 377762 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B569993 : Blo 377762 569993 := bstep (se 2 (by rfl) ⟨213747, by rfl⟩ : syracuseStep 569993 = 427495) B427495
theorem B570311 : Blo 377762 570311 := bstep (se 1 (by rfl) ⟨427733, by rfl⟩ : syracuseStep 570311 = 855467) B855467
theorem B571439 : Blo 377762 571439 := bstep (se 1 (by rfl) ⟨428579, by rfl⟩ : syracuseStep 571439 = 857159) B857159
theorem B33274111 : Blo 377762 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B572015 : Blo 377762 572015 := bstep (se 1 (by rfl) ⟨429011, by rfl⟩ : syracuseStep 572015 = 858023) B858023
theorem B3324563 : Blo 377762 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B637679 : Blo 377762 637679 := bstep (se 1 (by rfl) ⟨478259, by rfl⟩ : syracuseStep 637679 = 956519) B956519
theorem B3652735 : Blo 377762 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B639103 : Blo 377762 639103 := bstep (se 1 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 639103 = 958655) B958655
theorem B32949341 : Blo 377762 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B378015 : Blo 377762 378015 := bstep (se 1 (by rfl) ⟨283511, by rfl⟩ : syracuseStep 378015 = 567023) B567023
theorem B378303 : Blo 377762 378303 := bstep (se 1 (by rfl) ⟨283727, by rfl⟩ : syracuseStep 378303 = 567455) B567455
theorem B2442743 : Blo 377762 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B640939 : Blo 377762 640939 := bstep (se 1 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 640939 = 961409) B961409
theorem B378983 : Blo 377762 378983 := bstep (se 1 (by rfl) ⟨284237, by rfl⟩ : syracuseStep 378983 = 568475) B568475
theorem B2738285 : Blo 377762 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B1296743 : Blo 377762 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B1821293 : Blo 377762 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B379547 : Blo 377762 379547 := bstep (se 1 (by rfl) ⟨284660, by rfl⟩ : syracuseStep 379547 = 569321) B569321
theorem B379719 : Blo 377762 379719 := bstep (se 1 (by rfl) ⟨284789, by rfl⟩ : syracuseStep 379719 = 569579) B569579
theorem B379775 : Blo 377762 379775 := bstep (se 1 (by rfl) ⟨284831, by rfl⟩ : syracuseStep 379775 = 569663) B569663
theorem B380135 : Blo 377762 380135 := bstep (se 1 (by rfl) ⟨285101, by rfl⟩ : syracuseStep 380135 = 570203) B570203
theorem B380263 : Blo 377762 380263 := bstep (se 1 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 380263 = 570395) B570395
theorem B380399 : Blo 377762 380399 := bstep (se 1 (by rfl) ⟨285299, by rfl⟩ : syracuseStep 380399 = 570599) B570599
theorem B1920509 : Blo 377762 1920509 := bstep (se 3 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 1920509 = 720191) B720191
theorem B381167 : Blo 377762 381167 := bstep (se 1 (by rfl) ⟨285875, by rfl⟩ : syracuseStep 381167 = 571751) B571751
theorem B381487 : Blo 377762 381487 := bstep (se 1 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 381487 = 572231) B572231
theorem B381595 : Blo 377762 381595 := bstep (se 1 (by rfl) ⟨286196, by rfl⟩ : syracuseStep 381595 = 572393) B572393
theorem B381631 : Blo 377762 381631 := bstep (se 1 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 381631 = 572447) B572447
theorem B4182763 : Blo 377762 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B26695169 : Blo 377762 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B481727 : Blo 377762 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B547295 : Blo 377762 547295 := bstep (se 1 (by rfl) ⟨410471, by rfl⟩ : syracuseStep 547295 = 820943) B820943
theorem B55269863 : Blo 377762 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B4315679 : Blo 377762 4315679 := bstep (se 1 (by rfl) ⟨3236759, by rfl⟩ : syracuseStep 4315679 = 6473519) B6473519
theorem B482431 : Blo 377762 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B2153627 : Blo 377762 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B2875175 : Blo 377762 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B2154377 : Blo 377762 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B2744603 : Blo 377762 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B1926017 : Blo 377762 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B1435265 : Blo 377762 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B108325187 : Blo 377762 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B1076095 : Blo 377762 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B2190239 : Blo 377762 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B486967 : Blo 377762 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B6517259 : Blo 377762 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B718399 : Blo 377762 718399 := bstep (se 1 (by rfl) ⟨538799, by rfl⟩ : syracuseStep 718399 = 1077599) B1077599
theorem B2160391 : Blo 377762 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B1832827 : Blo 377762 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1079183 : Blo 377762 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B2455705 : Blo 377762 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B3668267 : Blo 377762 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B719273 : Blo 377762 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B1932335 : Blo 377762 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B3472793 : Blo 377762 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B31489829 : Blo 377762 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B852137 : Blo 377762 852137 := bstep (se 2 (by rfl) ⟨319551, by rfl⟩ : syracuseStep 852137 = 639103) B639103
theorem B39387683 : Blo 377762 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B853019 : Blo 377762 853019 := bstep (se 1 (by rfl) ⟨639764, by rfl⟩ : syracuseStep 853019 = 1279529) B1279529
theorem B2884895 : Blo 377762 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B1214195 : Blo 377762 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B1280339 : Blo 377762 1280339 := bstep (se 1 (by rfl) ⟨960254, by rfl⟩ : syracuseStep 1280339 = 1920509) B1920509
theorem B854585 : Blo 377762 854585 := bstep (se 2 (by rfl) ⟨320469, by rfl⟩ : syracuseStep 854585 = 640939) B640939
theorem B17796779 : Blo 377762 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B1284011 : Blo 377762 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B2889755 : Blo 377762 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B5577017 : Blo 377762 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B956843 : Blo 377762 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B1284605 : Blo 377762 1284605 := bstep (se 3 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 1284605 = 481727) B481727
theorem B8067599 : Blo 377762 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B957865 : Blo 377762 957865 := bstep (se 2 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 957865 = 718399) B718399
theorem B2171123 : Blo 377762 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B1843535 : Blo 377762 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1288223 : Blo 377762 1288223 := bstep (se 1 (by rfl) ⟨966167, by rfl⟩ : syracuseStep 1288223 = 1932335) B1932335
theorem B3287369 : Blo 377762 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B1617083 : Blo 377762 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B21966227 : Blo 377762 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B962027 : Blo 377762 962027 := bstep (se 1 (by rfl) ⟨721520, by rfl⟩ : syracuseStep 962027 = 1443041) B1443041
theorem B568943 : Blo 377762 568943 := bstep (se 1 (by rfl) ⟨426707, by rfl⟩ : syracuseStep 568943 = 853415) B853415
theorem B569639 : Blo 377762 569639 := bstep (se 1 (by rfl) ⟨427229, by rfl⟩ : syracuseStep 569639 = 854459) B854459
theorem B570239 : Blo 377762 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B5551939 : Blo 377762 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B964507 : Blo 377762 964507 := bstep (se 1 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 964507 = 1446761) B1446761
theorem B572135 : Blo 377762 572135 := bstep (se 1 (by rfl) ⟨429101, by rfl⟩ : syracuseStep 572135 = 858203) B858203
theorem B36846575 : Blo 377762 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B1916783 : Blo 377762 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B3916507 : Blo 377762 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B3457981 : Blo 377762 3457981 := bstep (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) B1296743
theorem B1623199 : Blo 377762 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B1459453 : Blo 377762 1459453 := bstep (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) B547295
theorem B1460159 : Blo 377762 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B2443769 : Blo 377762 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B379519 : Blo 377762 379519 := bstep (se 1 (by rfl) ⟨284639, by rfl⟩ : syracuseStep 379519 = 569279) B569279
theorem B4344839 : Blo 377762 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B379995 : Blo 377762 379995 := bstep (se 1 (by rfl) ⟨284996, by rfl⟩ : syracuseStep 379995 = 569993) B569993
theorem B380207 : Blo 377762 380207 := bstep (se 1 (by rfl) ⟨285155, by rfl⟩ : syracuseStep 380207 = 570311) B570311
theorem B380959 : Blo 377762 380959 := bstep (se 1 (by rfl) ⟨285719, by rfl⟩ : syracuseStep 380959 = 571439) B571439
theorem B4870313 : Blo 377762 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B643241 : Blo 377762 643241 := bstep (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) B482431
theorem B2445511 : Blo 377762 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B479515 : Blo 377762 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B381343 : Blo 377762 381343 := bstep (se 1 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 381343 = 572015) B572015
theorem B2216375 : Blo 377762 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B2315195 : Blo 377762 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B20993219 : Blo 377762 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B2152601 : Blo 377762 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B1628495 : Blo 377762 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B1825523 : Blo 377762 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B1925531 : Blo 377762 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B1434793 : Blo 377762 1434793 := bstep (se 2 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 1434793 = 1076095) B1076095
theorem B2877119 : Blo 377762 2877119 := bstep (se 1 (by rfl) ⟨2157839, by rfl⟩ : syracuseStep 2877119 = 4315679) B4315679
theorem B649289 : Blo 377762 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B1435751 : Blo 377762 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1436251 : Blo 377762 1436251 := bstep (se 1 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 1436251 = 2154377) B2154377
theorem B1829735 : Blo 377762 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B72216791 : Blo 377762 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B2880521 : Blo 377762 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B3274273 : Blo 377762 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B9270899 : Blo 377762 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B44365481 : Blo 377762 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B719455 : Blo 377762 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B425119 : Blo 377762 425119 := bstep (se 1 (by rfl) ⟨318839, by rfl⟩ : syracuseStep 425119 = 637679) B637679
theorem B2164265 : Blo 377762 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B853559 : Blo 377762 853559 := bstep (se 1 (by rfl) ⟨640169, by rfl⟩ : syracuseStep 853559 = 1280339) B1280339
theorem B11864519 : Blo 377762 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B3246875 : Blo 377762 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B428827 : Blo 377762 428827 := bstep (se 1 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 428827 = 643241) B643241
theorem B1543463 : Blo 377762 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B13995479 : Blo 377762 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B856007 : Blo 377762 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B1085663 : Blo 377762 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B856403 : Blo 377762 856403 := bstep (se 1 (by rfl) ⟨642302, by rfl⟩ : syracuseStep 856403 = 1284605) B1284605
theorem B5378399 : Blo 377762 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B1217015 : Blo 377762 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B1447415 : Blo 377762 1447415 := bstep (se 1 (by rfl) ⟨1085561, by rfl⟩ : syracuseStep 1447415 = 2171123) B2171123
theorem B1283687 : Blo 377762 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B858815 : Blo 377762 858815 := bstep (se 1 (by rfl) ⟨644111, by rfl⟩ : syracuseStep 858815 = 1288223) B1288223
theorem B432859 : Blo 377762 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B957167 : Blo 377762 957167 := bstep (se 1 (by rfl) ⟨717875, by rfl⟩ : syracuseStep 957167 = 1435751) B1435751
theorem B1219823 : Blo 377762 1219823 := bstep (se 1 (by rfl) ⟨914867, by rfl⟩ : syracuseStep 1219823 = 1829735) B1829735
theorem B4365697 : Blo 377762 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B1286009 : Blo 377762 1286009 := bstep (se 2 (by rfl) ⟨482253, by rfl⟩ : syracuseStep 1286009 = 964507) B964507
theorem B48144527 : Blo 377762 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B959273 : Blo 377762 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B566825 : Blo 377762 566825 := bstep (se 2 (by rfl) ⟨212559, by rfl⟩ : syracuseStep 566825 = 425119) B425119
theorem B568091 : Blo 377762 568091 := bstep (se 1 (by rfl) ⟨426068, by rfl⟩ : syracuseStep 568091 = 852137) B852137
theorem B26258455 : Blo 377762 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B568679 : Blo 377762 568679 := bstep (se 1 (by rfl) ⟨426509, by rfl⟩ : syracuseStep 568679 = 853019) B853019
theorem B5222009 : Blo 377762 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B1913057 : Blo 377762 1913057 := bstep (se 2 (by rfl) ⟨717396, by rfl⟩ : syracuseStep 1913057 = 1434793) B1434793
theorem B1945937 : Blo 377762 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B569723 : Blo 377762 569723 := bstep (se 1 (by rfl) ⟨427292, by rfl⟩ : syracuseStep 569723 = 854585) B854585
theorem B2896559 : Blo 377762 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B1915001 : Blo 377762 1915001 := bstep (se 2 (by rfl) ⟨718125, by rfl⟩ : syracuseStep 1915001 = 1436251) B1436251
theorem B637895 : Blo 377762 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B1229023 : Blo 377762 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B3260681 : Blo 377762 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B639353 : Blo 377762 639353 := bstep (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) B479515
theorem B1918079 : Blo 377762 1918079 := bstep (se 1 (by rfl) ⟨1438559, by rfl⟩ : syracuseStep 1918079 = 2877119) B2877119
theorem B641351 : Blo 377762 641351 := bstep (se 1 (by rfl) ⟨481013, by rfl⟩ : syracuseStep 641351 = 962027) B962027
theorem B379295 : Blo 377762 379295 := bstep (se 1 (by rfl) ⟨284471, by rfl⟩ : syracuseStep 379295 = 568943) B568943
theorem B379759 : Blo 377762 379759 := bstep (se 1 (by rfl) ⟨284819, by rfl⟩ : syracuseStep 379759 = 569639) B569639
theorem B380159 : Blo 377762 380159 := bstep (se 1 (by rfl) ⟨285119, by rfl⟩ : syracuseStep 380159 = 570239) B570239
theorem B1920347 : Blo 377762 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B6180599 : Blo 377762 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B29576987 : Blo 377762 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B381423 : Blo 377762 381423 := bstep (se 1 (by rfl) ⟨286067, by rfl⟩ : syracuseStep 381423 = 572135) B572135
theorem B24564383 : Blo 377762 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B1923263 : Blo 377762 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B4610641 : Blo 377762 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B973439 : Blo 377762 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B1629179 : Blo 377762 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B1926503 : Blo 377762 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B1435067 : Blo 377762 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B3237853 : Blo 377762 3237853 := bstep (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) B1214195
theorem B14872045 : Blo 377762 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B2191579 : Blo 377762 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B1078055 : Blo 377762 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B14644151 : Blo 377762 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B94565333 : Blo 377762 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B7402585 : Blo 377762 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B1277153 : Blo 377762 1277153 := bstep (se 2 (by rfl) ⟨478932, by rfl⟩ : syracuseStep 1277153 = 957865) B957865
theorem B1277855 : Blo 377762 1277855 := bstep (se 1 (by rfl) ⟨958391, by rfl⟩ : syracuseStep 1277855 = 1916783) B1916783
theorem B426235 : Blo 377762 426235 := bstep (se 1 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 426235 = 639353) B639353
theorem B1278719 : Blo 377762 1278719 := bstep (se 1 (by rfl) ⟨959039, by rfl⟩ : syracuseStep 1278719 = 1918079) B1918079
theorem B1442843 : Blo 377762 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B6554789 : Blo 377762 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B427567 : Blo 377762 427567 := bstep (se 1 (by rfl) ⟨320675, by rfl⟩ : syracuseStep 427567 = 641351) B641351
theorem B2164583 : Blo 377762 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B1280231 : Blo 377762 1280231 := bstep (se 1 (by rfl) ⟨960173, by rfl⟩ : syracuseStep 1280231 = 1920347) B1920347
theorem B855791 : Blo 377762 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B1282175 : Blo 377762 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B19829393 : Blo 377762 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1086119 : Blo 377762 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B857339 : Blo 377762 857339 := bstep (se 1 (by rfl) ⟨643004, by rfl⟩ : syracuseStep 857339 = 1286009) B1286009
theorem B1284335 : Blo 377762 1284335 := bstep (se 1 (by rfl) ⟨963251, by rfl⟩ : syracuseStep 1284335 = 1926503) B1926503
theorem B956711 : Blo 377762 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B9870113 : Blo 377762 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B3481339 : Blo 377762 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B2173787 : Blo 377762 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B2895101 : Blo 377762 2895101 := bstep (se 3 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 2895101 = 1085663) B1085663
theorem B569039 : Blo 377762 569039 := bstep (se 1 (by rfl) ⟨426779, by rfl⟩ : syracuseStep 569039 = 853559) B853559
theorem B7909679 : Blo 377762 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B1028975 : Blo 377762 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B570671 : Blo 377762 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B570935 : Blo 377762 570935 := bstep (se 1 (by rfl) ⟨428201, by rfl⟩ : syracuseStep 570935 = 856403) B856403
theorem B3585599 : Blo 377762 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B964943 : Blo 377762 964943 := bstep (se 1 (by rfl) ⟨723707, by rfl⟩ : syracuseStep 964943 = 1447415) B1447415
theorem B571769 : Blo 377762 571769 := bstep (se 2 (by rfl) ⟨214413, by rfl⟩ : syracuseStep 571769 = 428827) B428827
theorem B35011273 : Blo 377762 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B572543 : Blo 377762 572543 := bstep (se 1 (by rfl) ⟨429407, by rfl⟩ : syracuseStep 572543 = 858815) B858815
theorem B638111 : Blo 377762 638111 := bstep (se 1 (by rfl) ⟨478583, by rfl⟩ : syracuseStep 638111 = 957167) B957167
theorem B32096351 : Blo 377762 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B639515 : Blo 377762 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B377883 : Blo 377762 377883 := bstep (se 1 (by rfl) ⟨283412, by rfl⟩ : syracuseStep 377883 = 566825) B566825
theorem B378727 : Blo 377762 378727 := bstep (se 1 (by rfl) ⟨284045, by rfl⟩ : syracuseStep 378727 = 568091) B568091
theorem B379119 : Blo 377762 379119 := bstep (se 1 (by rfl) ⟨284339, by rfl⟩ : syracuseStep 379119 = 568679) B568679
theorem B1297291 : Blo 377762 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B379815 : Blo 377762 379815 := bstep (se 1 (by rfl) ⟨284861, by rfl⟩ : syracuseStep 379815 = 569723) B569723
theorem B6147521 : Blo 377762 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B577145 : Blo 377762 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B5820929 : Blo 377762 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B11688421 : Blo 377762 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B9330319 : Blo 377762 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B4120399 : Blo 377762 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B19717991 : Blo 377762 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B252174221 : Blo 377762 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B4317137 : Blo 377762 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B811343 : Blo 377762 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B16376255 : Blo 377762 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B648959 : Blo 377762 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B813215 : Blo 377762 813215 := bstep (se 1 (by rfl) ⟨609911, by rfl⟩ : syracuseStep 813215 = 1219823) B1219823
theorem B1275371 : Blo 377762 1275371 := bstep (se 1 (by rfl) ⟨956528, by rfl⟩ : syracuseStep 1275371 = 1913057) B1913057
theorem B1931039 : Blo 377762 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B718703 : Blo 377762 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B9762767 : Blo 377762 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B1276667 : Blo 377762 1276667 := bstep (se 1 (by rfl) ⟨957500, by rfl⟩ : syracuseStep 1276667 = 1915001) B1915001
theorem B425263 : Blo 377762 425263 := bstep (se 1 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 425263 = 637895) B637895
theorem B851435 : Blo 377762 851435 := bstep (se 1 (by rfl) ⟨638576, by rfl⟩ : syracuseStep 851435 = 1277153) B1277153
theorem B851903 : Blo 377762 851903 := bstep (se 1 (by rfl) ⟨638927, by rfl⟩ : syracuseStep 851903 = 1277855) B1277855
theorem B21397567 : Blo 377762 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B426343 : Blo 377762 426343 := bstep (se 1 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 426343 = 639515) B639515
theorem B852479 : Blo 377762 852479 := bstep (se 1 (by rfl) ⟨639359, by rfl⟩ : syracuseStep 852479 = 1278719) B1278719
theorem B2163581 : Blo 377762 2163581 := bstep (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) B811343
theorem B1443055 : Blo 377762 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B853487 : Blo 377762 853487 := bstep (se 1 (by rfl) ⟨640115, by rfl⟩ : syracuseStep 853487 = 1280231) B1280231
theorem B4098347 : Blo 377762 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B854783 : Blo 377762 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B724079 : Blo 377762 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B856223 : Blo 377762 856223 := bstep (se 1 (by rfl) ⟨642167, by rfl⟩ : syracuseStep 856223 = 1284335) B1284335
theorem B13145327 : Blo 377762 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B10917503 : Blo 377762 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B1449191 : Blo 377762 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B1287359 : Blo 377762 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B567017 : Blo 377762 567017 := bstep (se 2 (by rfl) ⟨212631, by rfl⟩ : syracuseStep 567017 = 425263) B425263
theorem B567623 : Blo 377762 567623 := bstep (se 1 (by rfl) ⟨425717, by rfl⟩ : syracuseStep 567623 = 851435) B851435
theorem B567935 : Blo 377762 567935 := bstep (se 1 (by rfl) ⟨425951, by rfl⟩ : syracuseStep 567935 = 851903) B851903
theorem B568313 : Blo 377762 568313 := bstep (se 2 (by rfl) ⟨213117, by rfl⟩ : syracuseStep 568313 = 426235) B426235
theorem B961895 : Blo 377762 961895 := bstep (se 1 (by rfl) ⟨721421, by rfl⟩ : syracuseStep 961895 = 1442843) B1442843
theorem B4369859 : Blo 377762 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B570089 : Blo 377762 570089 := bstep (se 2 (by rfl) ⟨213783, by rfl⟩ : syracuseStep 570089 = 427567) B427567
theorem B570527 : Blo 377762 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B3880619 : Blo 377762 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B13219595 : Blo 377762 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B571559 : Blo 377762 571559 := bstep (se 1 (by rfl) ⟨428669, by rfl⟩ : syracuseStep 571559 = 857339) B857339
theorem B637807 : Blo 377762 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B168116147 : Blo 377762 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B542143 : Blo 377762 542143 := bstep (se 1 (by rfl) ⟨406607, by rfl⟩ : syracuseStep 542143 = 813215) B813215
theorem B379359 : Blo 377762 379359 := bstep (se 1 (by rfl) ⟨284519, by rfl⟩ : syracuseStep 379359 = 569039) B569039
theorem B15584561 : Blo 377762 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B49761701 : Blo 377762 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B380447 : Blo 377762 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B46681697 : Blo 377762 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B380623 : Blo 377762 380623 := bstep (se 1 (by rfl) ⟨285467, by rfl⟩ : syracuseStep 380623 = 570935) B570935
theorem B479135 : Blo 377762 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B6508511 : Blo 377762 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B643295 : Blo 377762 643295 := bstep (se 1 (by rfl) ⟨482471, by rfl⟩ : syracuseStep 643295 = 964943) B964943
theorem B381179 : Blo 377762 381179 := bstep (se 1 (by rfl) ⟨285884, by rfl⟩ : syracuseStep 381179 = 571769) B571769
theorem B381695 : Blo 377762 381695 := bstep (se 1 (by rfl) ⟨286271, by rfl⟩ : syracuseStep 381695 = 572543) B572543
theorem B4641785 : Blo 377762 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B5493865 : Blo 377762 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B1729721 : Blo 377762 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B6580075 : Blo 377762 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B1730557 : Blo 377762 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B2878091 : Blo 377762 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B1930067 : Blo 377762 1930067 := bstep (se 1 (by rfl) ⟨1447550, by rfl⟩ : syracuseStep 1930067 = 2895101) B2895101
theorem B5273119 : Blo 377762 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B850247 : Blo 377762 850247 := bstep (se 1 (by rfl) ⟨637685, by rfl⟩ : syracuseStep 850247 = 1275371) B1275371
theorem B2390399 : Blo 377762 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B10975733 : Blo 377762 10975733 := bstep (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) B1028975
theorem B1539053 : Blo 377762 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B851111 : Blo 377762 851111 := bstep (se 1 (by rfl) ⟨638333, by rfl⟩ : syracuseStep 851111 = 1276667) B1276667
theorem B425407 : Blo 377762 425407 := bstep (se 1 (by rfl) ⟨319055, by rfl⟩ : syracuseStep 425407 = 638111) B638111
theorem B1442387 : Blo 377762 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B722857 : Blo 377762 722857 := bstep (se 2 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 722857 = 542143) B542143
theorem B10389707 : Blo 377762 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B428863 : Blo 377762 428863 := bstep (se 1 (by rfl) ⟨321647, by rfl⟩ : syracuseStep 428863 = 643295) B643295
theorem B7278335 : Blo 377762 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B858239 : Blo 377762 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B28123301 : Blo 377762 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B1286711 : Blo 377762 1286711 := bstep (se 1 (by rfl) ⟨965033, by rfl⟩ : syracuseStep 1286711 = 1930067) B1930067
theorem B566831 : Blo 377762 566831 := bstep (se 1 (by rfl) ⟨425123, by rfl⟩ : syracuseStep 566831 = 850247) B850247
theorem B7317155 : Blo 377762 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B567209 : Blo 377762 567209 := bstep (se 2 (by rfl) ⟨212703, by rfl⟩ : syracuseStep 567209 = 425407) B425407
theorem B1026035 : Blo 377762 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B567407 : Blo 377762 567407 := bstep (se 1 (by rfl) ⟨425555, by rfl⟩ : syracuseStep 567407 = 851111) B851111
theorem B112077431 : Blo 377762 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B568319 : Blo 377762 568319 := bstep (se 1 (by rfl) ⟨426239, by rfl⟩ : syracuseStep 568319 = 852479) B852479
theorem B568457 : Blo 377762 568457 := bstep (se 2 (by rfl) ⟨213171, by rfl⟩ : syracuseStep 568457 = 426343) B426343
theorem B568991 : Blo 377762 568991 := bstep (se 1 (by rfl) ⟨426743, by rfl⟩ : syracuseStep 568991 = 853487) B853487
theorem B2732231 : Blo 377762 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B569855 : Blo 377762 569855 := bstep (se 1 (by rfl) ⟨427391, by rfl⟩ : syracuseStep 569855 = 854783) B854783
theorem B33174467 : Blo 377762 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B4339007 : Blo 377762 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2307409 : Blo 377762 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B570815 : Blo 377762 570815 := bstep (se 1 (by rfl) ⟨428111, by rfl⟩ : syracuseStep 570815 = 856223) B856223
theorem B3094523 : Blo 377762 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B8763551 : Blo 377762 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B966127 : Blo 377762 966127 := bstep (se 1 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 966127 = 1449191) B1449191
theorem B378011 : Blo 377762 378011 := bstep (se 1 (by rfl) ⟨283508, by rfl⟩ : syracuseStep 378011 = 567017) B567017
theorem B7325153 : Blo 377762 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B378415 : Blo 377762 378415 := bstep (se 1 (by rfl) ⟨283811, by rfl⟩ : syracuseStep 378415 = 567623) B567623
theorem B378623 : Blo 377762 378623 := bstep (se 1 (by rfl) ⟨283967, by rfl⟩ : syracuseStep 378623 = 567935) B567935
theorem B1918727 : Blo 377762 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B378875 : Blo 377762 378875 := bstep (se 1 (by rfl) ⟨284156, by rfl⟩ : syracuseStep 378875 = 568313) B568313
theorem B641263 : Blo 377762 641263 := bstep (se 1 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 641263 = 961895) B961895
theorem B380059 : Blo 377762 380059 := bstep (se 1 (by rfl) ⟨285044, by rfl⟩ : syracuseStep 380059 = 570089) B570089
theorem B380351 : Blo 377762 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B381039 : Blo 377762 381039 := bstep (se 1 (by rfl) ⟨285779, by rfl⟩ : syracuseStep 381039 = 571559) B571559
theorem B1593599 : Blo 377762 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B28530089 : Blo 377762 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B1924073 : Blo 377762 1924073 := bstep (se 2 (by rfl) ⟨721527, by rfl⟩ : syracuseStep 1924073 = 1443055) B1443055
theorem B31121131 : Blo 377762 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B8773433 : Blo 377762 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B4612589 : Blo 377762 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B2913239 : Blo 377762 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B1930877 : Blo 377762 1930877 := bstep (se 3 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 1930877 = 724079) B724079
theorem B2587079 : Blo 377762 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B850409 : Blo 377762 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B8813063 : Blo 377762 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B1277693 : Blo 377762 1277693 := bstep (se 3 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 1277693 = 479135) B479135
theorem B4883435 : Blo 377762 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B1279151 : Blo 377762 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B4852223 : Blo 377762 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B855017 : Blo 377762 855017 := bstep (se 2 (by rfl) ⟨320631, by rfl⟩ : syracuseStep 855017 = 641263) B641263
theorem B1282715 : Blo 377762 1282715 := bstep (se 1 (by rfl) ⟨962036, by rfl⟩ : syracuseStep 1282715 = 1924073) B1924073
theorem B18748867 : Blo 377762 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B857807 : Blo 377762 857807 := bstep (se 1 (by rfl) ⟨643355, by rfl⟩ : syracuseStep 857807 = 1286711) B1286711
theorem B23501501 : Blo 377762 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B74718287 : Blo 377762 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B1942159 : Blo 377762 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2892671 : Blo 377762 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B1287251 : Blo 377762 1287251 := bstep (se 1 (by rfl) ⟨965438, by rfl⟩ : syracuseStep 1287251 = 1930877) B1930877
theorem B5842367 : Blo 377762 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B566939 : Blo 377762 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B1288169 : Blo 377762 1288169 := bstep (se 2 (by rfl) ⟨483063, by rfl⟩ : syracuseStep 1288169 = 966127) B966127
theorem B41494841 : Blo 377762 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B961591 : Blo 377762 961591 := bstep (se 1 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 961591 = 1442387) B1442387
theorem B6926471 : Blo 377762 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B963809 : Blo 377762 963809 := bstep (se 2 (by rfl) ⟨361428, by rfl⟩ : syracuseStep 963809 = 722857) B722857
theorem B19020059 : Blo 377762 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B571817 : Blo 377762 571817 := bstep (se 2 (by rfl) ⟨214431, by rfl⟩ : syracuseStep 571817 = 428863) B428863
theorem B572159 : Blo 377762 572159 := bstep (se 1 (by rfl) ⟨429119, by rfl⟩ : syracuseStep 572159 = 858239) B858239
theorem B5848955 : Blo 377762 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B377887 : Blo 377762 377887 := bstep (se 1 (by rfl) ⟨283415, by rfl⟩ : syracuseStep 377887 = 566831) B566831
theorem B6898877 : Blo 377762 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B378139 : Blo 377762 378139 := bstep (se 1 (by rfl) ⟨283604, by rfl⟩ : syracuseStep 378139 = 567209) B567209
theorem B378271 : Blo 377762 378271 := bstep (se 1 (by rfl) ⟨283703, by rfl⟩ : syracuseStep 378271 = 567407) B567407
theorem B12306181 : Blo 377762 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B378879 : Blo 377762 378879 := bstep (se 1 (by rfl) ⟨284159, by rfl⟩ : syracuseStep 378879 = 568319) B568319
theorem B378971 : Blo 377762 378971 := bstep (se 1 (by rfl) ⟨284228, by rfl⟩ : syracuseStep 378971 = 568457) B568457
theorem B379327 : Blo 377762 379327 := bstep (se 1 (by rfl) ⟨284495, by rfl⟩ : syracuseStep 379327 = 568991) B568991
theorem B1821487 : Blo 377762 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B379903 : Blo 377762 379903 := bstep (se 1 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 379903 = 569855) B569855
theorem B380543 : Blo 377762 380543 := bstep (se 1 (by rfl) ⟨285407, by rfl⟩ : syracuseStep 380543 = 570815) B570815
theorem B4249597 : Blo 377762 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B3075059 : Blo 377762 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B4878103 : Blo 377762 4878103 := bstep (se 1 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 4878103 = 7317155) B7317155
theorem B684023 : Blo 377762 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B22116311 : Blo 377762 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B2063015 : Blo 377762 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B851795 : Blo 377762 851795 := bstep (se 1 (by rfl) ⟨638846, by rfl⟩ : syracuseStep 851795 = 1277693) B1277693
theorem B852767 : Blo 377762 852767 := bstep (se 1 (by rfl) ⟨639575, by rfl⟩ : syracuseStep 852767 = 1279151) B1279151
theorem B2589545 : Blo 377762 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B855143 : Blo 377762 855143 := bstep (se 1 (by rfl) ⟨641357, by rfl⟩ : syracuseStep 855143 = 1282715) B1282715
theorem B2428649 : Blo 377762 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B1282121 : Blo 377762 1282121 := bstep (se 2 (by rfl) ⟨480795, by rfl⟩ : syracuseStep 1282121 = 961591) B961591
theorem B15667667 : Blo 377762 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B49812191 : Blo 377762 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B858167 : Blo 377762 858167 := bstep (se 1 (by rfl) ⟨643625, by rfl⟩ : syracuseStep 858167 = 1287251) B1287251
theorem B858779 : Blo 377762 858779 := bstep (se 1 (by rfl) ⟨644084, by rfl⟩ : syracuseStep 858779 = 1288169) B1288169
theorem B27663227 : Blo 377762 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B567863 : Blo 377762 567863 := bstep (se 1 (by rfl) ⟨425897, by rfl⟩ : syracuseStep 567863 = 851795) B851795
theorem B3255623 : Blo 377762 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B4599251 : Blo 377762 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B570011 : Blo 377762 570011 := bstep (se 1 (by rfl) ⟨427508, by rfl⟩ : syracuseStep 570011 = 855017) B855017
theorem B571871 : Blo 377762 571871 := bstep (se 1 (by rfl) ⟨428903, by rfl⟩ : syracuseStep 571871 = 857807) B857807
theorem B6504137 : Blo 377762 6504137 := bstep (se 2 (by rfl) ⟨2439051, by rfl⟩ : syracuseStep 6504137 = 4878103) B4878103
theorem B377959 : Blo 377762 377959 := bstep (se 1 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 377959 = 566939) B566939
theorem B2050039 : Blo 377762 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B642539 : Blo 377762 642539 := bstep (se 1 (by rfl) ⟨481904, by rfl⟩ : syracuseStep 642539 = 963809) B963809
theorem B381211 : Blo 377762 381211 := bstep (se 1 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 381211 = 571817) B571817
theorem B381439 : Blo 377762 381439 := bstep (se 1 (by rfl) ⟨286079, by rfl⟩ : syracuseStep 381439 = 572159) B572159
theorem B1824061 : Blo 377762 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B3234815 : Blo 377762 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B16408241 : Blo 377762 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B1928447 : Blo 377762 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B3894911 : Blo 377762 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B24998489 : Blo 377762 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B5666129 : Blo 377762 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B4617647 : Blo 377762 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B14744207 : Blo 377762 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B12680039 : Blo 377762 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B1375343 : Blo 377762 1375343 := bstep (se 1 (by rfl) ⟨1031507, by rfl⟩ : syracuseStep 1375343 = 2063015) B2063015
theorem B3899303 : Blo 377762 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B428359 : Blo 377762 428359 := bstep (se 1 (by rfl) ⟨321269, by rfl⟩ : syracuseStep 428359 = 642539) B642539
theorem B854747 : Blo 377762 854747 := bstep (se 1 (by rfl) ⟨641060, by rfl⟩ : syracuseStep 854747 = 1282121) B1282121
theorem B2432081 : Blo 377762 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B1285631 : Blo 377762 1285631 := bstep (se 1 (by rfl) ⟨964223, by rfl⟩ : syracuseStep 1285631 = 1928447) B1928447
theorem B2170415 : Blo 377762 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B2596607 : Blo 377762 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B3777419 : Blo 377762 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B4336091 : Blo 377762 4336091 := bstep (se 1 (by rfl) ⟨3252068, by rfl⟩ : syracuseStep 4336091 = 6504137) B6504137
theorem B2599535 : Blo 377762 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B568511 : Blo 377762 568511 := bstep (se 1 (by rfl) ⟨426383, by rfl⟩ : syracuseStep 568511 = 852767) B852767
theorem B570095 : Blo 377762 570095 := bstep (se 1 (by rfl) ⟨427571, by rfl⟩ : syracuseStep 570095 = 855143) B855143
theorem B1619099 : Blo 377762 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B2733385 : Blo 377762 2733385 := bstep (se 2 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 2733385 = 2050039) B2050039
theorem B33208127 : Blo 377762 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B572111 : Blo 377762 572111 := bstep (se 1 (by rfl) ⟨429083, by rfl⟩ : syracuseStep 572111 = 858167) B858167
theorem B572519 : Blo 377762 572519 := bstep (se 1 (by rfl) ⟨429389, by rfl⟩ : syracuseStep 572519 = 858779) B858779
theorem B378575 : Blo 377762 378575 := bstep (se 1 (by rfl) ⟨283931, by rfl⟩ : syracuseStep 378575 = 567863) B567863
theorem B3066167 : Blo 377762 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B16665659 : Blo 377762 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B380007 : Blo 377762 380007 := bstep (se 1 (by rfl) ⟨285005, by rfl⟩ : syracuseStep 380007 = 570011) B570011
theorem B381247 : Blo 377762 381247 := bstep (se 1 (by rfl) ⟨285935, by rfl⟩ : syracuseStep 381247 = 571871) B571871
theorem B1726363 : Blo 377762 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B10445111 : Blo 377762 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B18442151 : Blo 377762 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B2156543 : Blo 377762 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B10938827 : Blo 377762 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B3078431 : Blo 377762 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B9829471 : Blo 377762 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B8453359 : Blo 377762 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B916895 : Blo 377762 916895 := bstep (se 1 (by rfl) ⟨687671, by rfl⟩ : syracuseStep 916895 = 1375343) B1375343
theorem B11110439 : Blo 377762 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B857087 : Blo 377762 857087 := bstep (se 1 (by rfl) ⟨642815, by rfl⟩ : syracuseStep 857087 = 1285631) B1285631
theorem B1446943 : Blo 377762 1446943 := bstep (se 1 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 1446943 = 2170415) B2170415
theorem B12294767 : Blo 377762 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B2890727 : Blo 377762 2890727 := bstep (se 1 (by rfl) ⟨2168045, by rfl⟩ : syracuseStep 2890727 = 4336091) B4336091
theorem B3644513 : Blo 377762 3644513 := bstep (se 2 (by rfl) ⟨1366692, by rfl⟩ : syracuseStep 3644513 = 2733385) B2733385
theorem B2044111 : Blo 377762 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B569831 : Blo 377762 569831 := bstep (se 1 (by rfl) ⟨427373, by rfl⟩ : syracuseStep 569831 = 854747) B854747
theorem B10073117 : Blo 377762 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B571145 : Blo 377762 571145 := bstep (se 2 (by rfl) ⟨214179, by rfl⟩ : syracuseStep 571145 = 428359) B428359
theorem B1621387 : Blo 377762 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B6963407 : Blo 377762 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B7292551 : Blo 377762 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B379007 : Blo 377762 379007 := bstep (se 1 (by rfl) ⟨284255, by rfl⟩ : syracuseStep 379007 = 568511) B568511
theorem B380063 : Blo 377762 380063 := bstep (se 1 (by rfl) ⟨285047, by rfl⟩ : syracuseStep 380063 = 570095) B570095
theorem B22138751 : Blo 377762 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B2052287 : Blo 377762 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B381407 : Blo 377762 381407 := bstep (se 1 (by rfl) ⟨286055, by rfl⟩ : syracuseStep 381407 = 572111) B572111
theorem B381679 : Blo 377762 381679 := bstep (se 1 (by rfl) ⟨286259, by rfl⟩ : syracuseStep 381679 = 572519) B572519
theorem B611263 : Blo 377762 611263 := bstep (se 1 (by rfl) ⟨458447, by rfl⟩ : syracuseStep 611263 = 916895) B916895
theorem B1731071 : Blo 377762 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B1437695 : Blo 377762 1437695 := bstep (se 1 (by rfl) ⟨1078271, by rfl⟩ : syracuseStep 1437695 = 2156543) B2156543
theorem B1733023 : Blo 377762 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B1079399 : Blo 377762 1079399 := bstep (se 1 (by rfl) ⟨809549, by rfl⟩ : syracuseStep 1079399 = 1619099) B1619099
theorem B13105961 : Blo 377762 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B11271145 : Blo 377762 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B9207269 : Blo 377762 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B7406959 : Blo 377762 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B8196511 : Blo 377762 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B2429675 : Blo 377762 2429675 := bstep (se 1 (by rfl) ⟨1822256, by rfl⟩ : syracuseStep 2429675 = 3644513) B3644513
theorem B2725481 : Blo 377762 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B958463 : Blo 377762 958463 := bstep (se 1 (by rfl) ⟨718847, by rfl⟩ : syracuseStep 958463 = 1437695) B1437695
theorem B6138179 : Blo 377762 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B14759167 : Blo 377762 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B571391 : Blo 377762 571391 := bstep (se 1 (by rfl) ⟨428543, by rfl⟩ : syracuseStep 571391 = 857087) B857087
theorem B2310697 : Blo 377762 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B379887 : Blo 377762 379887 := bstep (se 1 (by rfl) ⟨284915, by rfl⟩ : syracuseStep 379887 = 569831) B569831
theorem B380763 : Blo 377762 380763 := bstep (se 1 (by rfl) ⟨285572, by rfl⟩ : syracuseStep 380763 = 571145) B571145
theorem B15028193 : Blo 377762 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B8737307 : Blo 377762 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B4642271 : Blo 377762 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B9723401 : Blo 377762 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B26861645 : Blo 377762 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B1368191 : Blo 377762 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B1927151 : Blo 377762 1927151 := bstep (se 1 (by rfl) ⟨1445363, by rfl⟩ : syracuseStep 1927151 = 2890727) B2890727
theorem B815017 : Blo 377762 815017 := bstep (se 2 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 815017 = 611263) B611263
theorem B4616189 : Blo 377762 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B1929257 : Blo 377762 1929257 := bstep (se 2 (by rfl) ⟨723471, by rfl⟩ : syracuseStep 1929257 = 1446943) B1446943
theorem B719599 : Blo 377762 719599 := bstep (se 1 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 719599 = 1079399) B1079399
theorem B2161849 : Blo 377762 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B71631053 : Blo 377762 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B3080929 : Blo 377762 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B1086689 : Blo 377762 1086689 := bstep (se 2 (by rfl) ⟨407508, by rfl⟩ : syracuseStep 1086689 = 815017) B815017
theorem B1284767 : Blo 377762 1284767 := bstep (se 1 (by rfl) ⟨963575, by rfl⟩ : syracuseStep 1284767 = 1927151) B1927151
theorem B1286171 : Blo 377762 1286171 := bstep (se 1 (by rfl) ⟨964628, by rfl⟩ : syracuseStep 1286171 = 1929257) B1929257
theorem B959465 : Blo 377762 959465 := bstep (se 2 (by rfl) ⟨359799, by rfl⟩ : syracuseStep 959465 = 719599) B719599
theorem B3648509 : Blo 377762 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B9875945 : Blo 377762 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B1619783 : Blo 377762 1619783 := bstep (se 1 (by rfl) ⟨1214837, by rfl⟩ : syracuseStep 1619783 = 2429675) B2429675
theorem B3094847 : Blo 377762 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1816987 : Blo 377762 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B638975 : Blo 377762 638975 := bstep (se 1 (by rfl) ⟨479231, by rfl⟩ : syracuseStep 638975 = 958463) B958463
theorem B10928681 : Blo 377762 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B19678889 : Blo 377762 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B380927 : Blo 377762 380927 := bstep (se 1 (by rfl) ⟨285695, by rfl⟩ : syracuseStep 380927 = 571391) B571391
theorem B5824871 : Blo 377762 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B6482267 : Blo 377762 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B4092119 : Blo 377762 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B3077459 : Blo 377762 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B2882465 : Blo 377762 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B40075181 : Blo 377762 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B724459 : Blo 377762 724459 := bstep (se 1 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 724459 = 1086689) B1086689
theorem B856511 : Blo 377762 856511 := bstep (se 1 (by rfl) ⟨642383, by rfl⟩ : syracuseStep 856511 = 1284767) B1284767
theorem B857447 : Blo 377762 857447 := bstep (se 1 (by rfl) ⟨643085, by rfl⟩ : syracuseStep 857447 = 1286171) B1286171
theorem B2432339 : Blo 377762 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B2728079 : Blo 377762 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B26716787 : Blo 377762 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B47754035 : Blo 377762 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B7285787 : Blo 377762 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B4107905 : Blo 377762 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B13119259 : Blo 377762 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B3883247 : Blo 377762 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B639643 : Blo 377762 639643 := bstep (se 1 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 639643 = 959465) B959465
theorem B2051639 : Blo 377762 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B1921643 : Blo 377762 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B26335853 : Blo 377762 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B4321511 : Blo 377762 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B2422649 : Blo 377762 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B1079855 : Blo 377762 1079855 := bstep (se 1 (by rfl) ⟨809891, by rfl⟩ : syracuseStep 1079855 = 1619783) B1619783
theorem B2063231 : Blo 377762 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B425983 : Blo 377762 425983 := bstep (se 1 (by rfl) ⟨319487, by rfl⟩ : syracuseStep 425983 = 638975) B638975
theorem B2588831 : Blo 377762 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B852857 : Blo 377762 852857 := bstep (se 2 (by rfl) ⟨319821, by rfl⟩ : syracuseStep 852857 = 639643) B639643
theorem B1281095 : Blo 377762 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B6460397 : Blo 377762 6460397 := bstep (se 3 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 6460397 = 2422649) B2422649
theorem B4857191 : Blo 377762 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B567977 : Blo 377762 567977 := bstep (se 2 (by rfl) ⟨212991, by rfl⟩ : syracuseStep 567977 = 425983) B425983
theorem B571007 : Blo 377762 571007 := bstep (se 1 (by rfl) ⟨428255, by rfl⟩ : syracuseStep 571007 = 856511) B856511
theorem B571631 : Blo 377762 571631 := bstep (se 1 (by rfl) ⟨428723, by rfl⟩ : syracuseStep 571631 = 857447) B857447
theorem B965945 : Blo 377762 965945 := bstep (se 2 (by rfl) ⟨362229, by rfl⟩ : syracuseStep 965945 = 724459) B724459
theorem B1621559 : Blo 377762 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B1818719 : Blo 377762 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B17811191 : Blo 377762 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B31836023 : Blo 377762 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B2738603 : Blo 377762 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B1367759 : Blo 377762 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B17557235 : Blo 377762 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B17492345 : Blo 377762 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B2881007 : Blo 377762 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B719903 : Blo 377762 719903 := bstep (se 1 (by rfl) ⟨539927, by rfl⟩ : syracuseStep 719903 = 1079855) B1079855
theorem B1375487 : Blo 377762 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1212479 : Blo 377762 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B854063 : Blo 377762 854063 := bstep (se 1 (by rfl) ⟨640547, by rfl⟩ : syracuseStep 854063 = 1281095) B1281095
theorem B11704823 : Blo 377762 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B568571 : Blo 377762 568571 := bstep (se 1 (by rfl) ⟨426428, by rfl⟩ : syracuseStep 568571 = 852857) B852857
theorem B11874127 : Blo 377762 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B4306931 : Blo 377762 4306931 := bstep (se 1 (by rfl) ⟨3230198, by rfl⟩ : syracuseStep 4306931 = 6460397) B6460397
theorem B378651 : Blo 377762 378651 := bstep (se 1 (by rfl) ⟨283988, by rfl⟩ : syracuseStep 378651 = 567977) B567977
theorem B1920671 : Blo 377762 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B380671 : Blo 377762 380671 := bstep (se 1 (by rfl) ⟨285503, by rfl⟩ : syracuseStep 380671 = 571007) B571007
theorem B381087 : Blo 377762 381087 := bstep (se 1 (by rfl) ⟨285815, by rfl⟩ : syracuseStep 381087 = 571631) B571631
theorem B479935 : Blo 377762 479935 := bstep (se 1 (by rfl) ⟨359951, by rfl⟩ : syracuseStep 479935 = 719903) B719903
theorem B643963 : Blo 377762 643963 := bstep (se 1 (by rfl) ⟨482972, by rfl⟩ : syracuseStep 643963 = 965945) B965945
theorem B1725887 : Blo 377762 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B21224015 : Blo 377762 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B1825735 : Blo 377762 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B3238127 : Blo 377762 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B911839 : Blo 377762 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B11661563 : Blo 377762 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B916991 : Blo 377762 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B1081039 : Blo 377762 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B1280447 : Blo 377762 1280447 := bstep (se 1 (by rfl) ⟨960335, by rfl⟩ : syracuseStep 1280447 = 1920671) B1920671
theorem B1215785 : Blo 377762 1215785 := bstep (se 2 (by rfl) ⟨455919, by rfl⟩ : syracuseStep 1215785 = 911839) B911839
theorem B7803215 : Blo 377762 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B15832169 : Blo 377762 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B858617 : Blo 377762 858617 := bstep (se 2 (by rfl) ⟨321981, by rfl⟩ : syracuseStep 858617 = 643963) B643963
theorem B7774375 : Blo 377762 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B2434313 : Blo 377762 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B569375 : Blo 377762 569375 := bstep (se 1 (by rfl) ⟨427031, by rfl⟩ : syracuseStep 569375 = 854063) B854063
theorem B4602365 : Blo 377762 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B639913 : Blo 377762 639913 := bstep (se 2 (by rfl) ⟨239967, by rfl⟩ : syracuseStep 639913 = 479935) B479935
theorem B379047 : Blo 377762 379047 := bstep (se 1 (by rfl) ⟨284285, by rfl⟩ : syracuseStep 379047 = 568571) B568571
theorem B2871287 : Blo 377762 2871287 := bstep (se 1 (by rfl) ⟨2153465, by rfl⟩ : syracuseStep 2871287 = 4306931) B4306931
theorem B611327 : Blo 377762 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B808319 : Blo 377762 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B14149343 : Blo 377762 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B2158751 : Blo 377762 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B1441385 : Blo 377762 1441385 := bstep (se 2 (by rfl) ⟨540519, by rfl⟩ : syracuseStep 1441385 = 1081039) B1081039
theorem B853217 : Blo 377762 853217 := bstep (se 2 (by rfl) ⟨319956, by rfl⟩ : syracuseStep 853217 = 639913) B639913
theorem B853631 : Blo 377762 853631 := bstep (se 1 (by rfl) ⟨640223, by rfl⟩ : syracuseStep 853631 = 1280447) B1280447
theorem B10554779 : Blo 377762 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B960923 : Blo 377762 960923 := bstep (se 1 (by rfl) ⟨720692, by rfl⟩ : syracuseStep 960923 = 1441385) B1441385
theorem B10365833 : Blo 377762 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B1914191 : Blo 377762 1914191 := bstep (se 1 (by rfl) ⟨1435643, by rfl⟩ : syracuseStep 1914191 = 2871287) B2871287
theorem B572411 : Blo 377762 572411 := bstep (se 1 (by rfl) ⟨429308, by rfl⟩ : syracuseStep 572411 = 858617) B858617
theorem B1622875 : Blo 377762 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B379583 : Blo 377762 379583 := bstep (se 1 (by rfl) ⟨284687, by rfl⟩ : syracuseStep 379583 = 569375) B569375
theorem B3068243 : Blo 377762 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B810523 : Blo 377762 810523 := bstep (se 1 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 810523 = 1215785) B1215785
theorem B1630205 : Blo 377762 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B5202143 : Blo 377762 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B2155517 : Blo 377762 2155517 := bstep (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) B808319
theorem B9432895 : Blo 377762 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B1439167 : Blo 377762 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B2163833 : Blo 377762 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B1086803 : Blo 377762 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B568811 : Blo 377762 568811 := bstep (se 1 (by rfl) ⟨426608, by rfl⟩ : syracuseStep 568811 = 853217) B853217
theorem B569087 : Blo 377762 569087 := bstep (se 1 (by rfl) ⟨426815, by rfl⟩ : syracuseStep 569087 = 853631) B853631
theorem B2045495 : Blo 377762 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B640615 : Blo 377762 640615 := bstep (se 1 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 640615 = 960923) B960923
theorem B1918889 : Blo 377762 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B381607 : Blo 377762 381607 := bstep (se 1 (by rfl) ⟨286205, by rfl⟩ : syracuseStep 381607 = 572411) B572411
theorem B7036519 : Blo 377762 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B12577193 : Blo 377762 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B3468095 : Blo 377762 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B1437011 : Blo 377762 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B6910555 : Blo 377762 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B1276127 : Blo 377762 1276127 := bstep (se 1 (by rfl) ⟨957095, by rfl⟩ : syracuseStep 1276127 = 1914191) B1914191
theorem B1080697 : Blo 377762 1080697 := bstep (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) B810523
theorem B1442555 : Blo 377762 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B1279259 : Blo 377762 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B854153 : Blo 377762 854153 := bstep (se 2 (by rfl) ⟨320307, by rfl⟩ : syracuseStep 854153 = 640615) B640615
theorem B724535 : Blo 377762 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B9214073 : Blo 377762 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B958007 : Blo 377762 958007 := bstep (se 1 (by rfl) ⟨718505, by rfl⟩ : syracuseStep 958007 = 1437011) B1437011
theorem B9382025 : Blo 377762 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B2312063 : Blo 377762 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B379207 : Blo 377762 379207 := bstep (se 1 (by rfl) ⟨284405, by rfl⟩ : syracuseStep 379207 = 568811) B568811
theorem B379391 : Blo 377762 379391 := bstep (se 1 (by rfl) ⟨284543, by rfl⟩ : syracuseStep 379391 = 569087) B569087
theorem B1363663 : Blo 377762 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B8384795 : Blo 377762 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B850751 : Blo 377762 850751 := bstep (se 1 (by rfl) ⟨638063, by rfl⟩ : syracuseStep 850751 = 1276127) B1276127
theorem B1440929 : Blo 377762 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B852839 : Blo 377762 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B1541375 : Blo 377762 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B567167 : Blo 377762 567167 := bstep (se 1 (by rfl) ⟨425375, by rfl⟩ : syracuseStep 567167 = 850751) B850751
theorem B960619 : Blo 377762 960619 := bstep (se 1 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 960619 = 1440929) B1440929
theorem B961703 : Blo 377762 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B569435 : Blo 377762 569435 := bstep (se 1 (by rfl) ⟨427076, by rfl⟩ : syracuseStep 569435 = 854153) B854153
theorem B6142715 : Blo 377762 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B1818217 : Blo 377762 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B638671 : Blo 377762 638671 := bstep (se 1 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 638671 = 958007) B958007
theorem B25018733 : Blo 377762 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B5589863 : Blo 377762 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B483023 : Blo 377762 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B16679155 : Blo 377762 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B1280825 : Blo 377762 1280825 := bstep (se 2 (by rfl) ⟨480309, by rfl⟩ : syracuseStep 1280825 = 960619) B960619
theorem B1288061 : Blo 377762 1288061 := bstep (se 3 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 1288061 = 483023) B483023
theorem B568559 : Blo 377762 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B1027583 : Blo 377762 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B378111 : Blo 377762 378111 := bstep (se 1 (by rfl) ⟨283583, by rfl⟩ : syracuseStep 378111 = 567167) B567167
theorem B641135 : Blo 377762 641135 := bstep (se 1 (by rfl) ⟨480851, by rfl⟩ : syracuseStep 641135 = 961703) B961703
theorem B379623 : Blo 377762 379623 := bstep (se 1 (by rfl) ⟨284717, by rfl⟩ : syracuseStep 379623 = 569435) B569435
theorem B3726575 : Blo 377762 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B9697157 : Blo 377762 9697157 := bstep (se 4 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 9697157 = 1818217) B1818217
theorem B4095143 : Blo 377762 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B851561 : Blo 377762 851561 := bstep (se 2 (by rfl) ⟨319335, by rfl⟩ : syracuseStep 851561 = 638671) B638671
theorem B427423 : Blo 377762 427423 := bstep (se 1 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 427423 = 641135) B641135
theorem B853883 : Blo 377762 853883 := bstep (se 1 (by rfl) ⟨640412, by rfl⟩ : syracuseStep 853883 = 1280825) B1280825
theorem B858707 : Blo 377762 858707 := bstep (se 1 (by rfl) ⟨644030, by rfl⟩ : syracuseStep 858707 = 1288061) B1288061
theorem B6464771 : Blo 377762 6464771 := bstep (se 1 (by rfl) ⟨4848578, by rfl⟩ : syracuseStep 6464771 = 9697157) B9697157
theorem B2730095 : Blo 377762 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B567707 : Blo 377762 567707 := bstep (se 1 (by rfl) ⟨425780, by rfl⟩ : syracuseStep 567707 = 851561) B851561
theorem B379039 : Blo 377762 379039 := bstep (se 1 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 379039 = 568559) B568559
theorem B22238873 : Blo 377762 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B2484383 : Blo 377762 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B685055 : Blo 377762 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B6625021 : Blo 377762 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B569255 : Blo 377762 569255 := bstep (se 1 (by rfl) ⟨426941, by rfl⟩ : syracuseStep 569255 = 853883) B853883
theorem B569897 : Blo 377762 569897 := bstep (se 2 (by rfl) ⟨213711, by rfl⟩ : syracuseStep 569897 = 427423) B427423
theorem B14825915 : Blo 377762 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B572471 : Blo 377762 572471 := bstep (se 1 (by rfl) ⟨429353, by rfl⟩ : syracuseStep 572471 = 858707) B858707
theorem B4309847 : Blo 377762 4309847 := bstep (se 1 (by rfl) ⟨3232385, by rfl⟩ : syracuseStep 4309847 = 6464771) B6464771
theorem B1820063 : Blo 377762 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B378471 : Blo 377762 378471 := bstep (se 1 (by rfl) ⟨283853, by rfl⟩ : syracuseStep 378471 = 567707) B567707
theorem B1826813 : Blo 377762 1826813 := bstep (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) B685055
theorem B1213375 : Blo 377762 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B141333781 : Blo 377762 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B1217875 : Blo 377762 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B379503 : Blo 377762 379503 := bstep (se 1 (by rfl) ⟨284627, by rfl⟩ : syracuseStep 379503 = 569255) B569255
theorem B379931 : Blo 377762 379931 := bstep (se 1 (by rfl) ⟨284948, by rfl⟩ : syracuseStep 379931 = 569897) B569897
theorem B9883943 : Blo 377762 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B381647 : Blo 377762 381647 := bstep (se 1 (by rfl) ⟨286235, by rfl⟩ : syracuseStep 381647 = 572471) B572471
theorem B2873231 : Blo 377762 2873231 := bstep (se 1 (by rfl) ⟨2154923, by rfl⟩ : syracuseStep 2873231 = 4309847) B4309847
theorem B6589295 : Blo 377762 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B1617833 : Blo 377762 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B1915487 : Blo 377762 1915487 := bstep (se 1 (by rfl) ⟨1436615, by rfl⟩ : syracuseStep 1915487 = 2873231) B2873231
theorem B1623833 : Blo 377762 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B188445041 : Blo 377762 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B1082555 : Blo 377762 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B4392863 : Blo 377762 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B4314221 : Blo 377762 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B125630027 : Blo 377762 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B1276991 : Blo 377762 1276991 := bstep (se 1 (by rfl) ⟨957743, by rfl⟩ : syracuseStep 1276991 = 1915487) B1915487
theorem B721703 : Blo 377762 721703 := bstep (se 1 (by rfl) ⟨541277, by rfl⟩ : syracuseStep 721703 = 1082555) B1082555
theorem B2928575 : Blo 377762 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B2876147 : Blo 377762 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B83753351 : Blo 377762 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B851327 : Blo 377762 851327 := bstep (se 1 (by rfl) ⟨638495, by rfl⟩ : syracuseStep 851327 = 1276991) B1276991
theorem B567551 : Blo 377762 567551 := bstep (se 1 (by rfl) ⟨425663, by rfl⟩ : syracuseStep 567551 = 851327) B851327
theorem B1917431 : Blo 377762 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B1952383 : Blo 377762 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B481135 : Blo 377762 481135 := bstep (se 1 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 481135 = 721703) B721703
theorem B55835567 : Blo 377762 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B1278287 : Blo 377762 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B2603177 : Blo 377762 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B378367 : Blo 377762 378367 := bstep (se 1 (by rfl) ⟨283775, by rfl⟩ : syracuseStep 378367 = 567551) B567551
theorem B641513 : Blo 377762 641513 := bstep (se 2 (by rfl) ⟨240567, by rfl⟩ : syracuseStep 641513 = 481135) B481135
theorem B37223711 : Blo 377762 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B852191 : Blo 377762 852191 := bstep (se 1 (by rfl) ⟨639143, by rfl⟩ : syracuseStep 852191 = 1278287) B1278287
theorem B427675 : Blo 377762 427675 := bstep (se 1 (by rfl) ⟨320756, by rfl⟩ : syracuseStep 427675 = 641513) B641513
theorem B24815807 : Blo 377762 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B1735451 : Blo 377762 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B1156967 : Blo 377762 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B568127 : Blo 377762 568127 := bstep (se 1 (by rfl) ⟨426095, by rfl⟩ : syracuseStep 568127 = 852191) B852191
theorem B570233 : Blo 377762 570233 := bstep (se 2 (by rfl) ⟨213837, by rfl⟩ : syracuseStep 570233 = 427675) B427675
theorem B16543871 : Blo 377762 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B771311 : Blo 377762 771311 := bstep (se 1 (by rfl) ⟨578483, by rfl⟩ : syracuseStep 771311 = 1156967) B1156967
theorem B378751 : Blo 377762 378751 := bstep (se 1 (by rfl) ⟨284063, by rfl⟩ : syracuseStep 378751 = 568127) B568127
theorem B11029247 : Blo 377762 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B380155 : Blo 377762 380155 := bstep (se 1 (by rfl) ⟨285116, by rfl⟩ : syracuseStep 380155 = 570233) B570233
theorem B7352831 : Blo 377762 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B514207 : Blo 377762 514207 := bstep (se 1 (by rfl) ⟨385655, by rfl⟩ : syracuseStep 514207 = 771311) B771311
theorem B4901887 : Blo 377762 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B2742437 : Blo 377762 2742437 := bstep (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) B514207
theorem B6535849 : Blo 377762 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B1828291 : Blo 377762 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B2437721 : Blo 377762 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B8714465 : Blo 377762 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 377762 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B1625147 : Blo 377762 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B1083431 : Blo 377762 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B3873095 : Blo 377762 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B722287 : Blo 377762 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B2582063 : Blo 377762 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B963049 : Blo 377762 963049 := bstep (se 2 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 963049 = 722287) B722287
theorem B1721375 : Blo 377762 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B1147583 : Blo 377762 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B1284065 : Blo 377762 1284065 := bstep (se 2 (by rfl) ⟨481524, by rfl⟩ : syracuseStep 1284065 = 963049) B963049
theorem B856043 : Blo 377762 856043 := bstep (se 1 (by rfl) ⟨642032, by rfl⟩ : syracuseStep 856043 = 1284065) B1284065
theorem B765055 : Blo 377762 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B570695 : Blo 377762 570695 := bstep (se 1 (by rfl) ⟨428021, by rfl⟩ : syracuseStep 570695 = 856043) B856043
theorem B4080293 : Blo 377762 4080293 := bstep (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) B765055
theorem B2720195 : Blo 377762 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B380463 : Blo 377762 380463 := bstep (se 1 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 380463 = 570695) B570695
theorem B1813463 : Blo 377762 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B1208975 : Blo 377762 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B12895733 : Blo 377762 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B34388621 : Blo 377762 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B22925747 : Blo 377762 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B15283831 : Blo 377762 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B20378441 : Blo 377762 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B13585627 : Blo 377762 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B72456677 : Blo 377762 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B48304451 : Blo 377762 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B32202967 : Blo 377762 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 377762 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B28624859 : Blo 377762 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B19083239 : Blo 377762 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B12722159 : Blo 377762 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B8481439 : Blo 377762 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 377762 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B15078113 : Blo 377762 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B10052075 : Blo 377762 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B6701383 : Blo 377762 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B8935177 : Blo 377762 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B11913569 : Blo 377762 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 377762 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B84718709 : Blo 377762 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B56479139 : Blo 377762 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B37652759 : Blo 377762 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B25101839 : Blo 377762 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B16734559 : Blo 377762 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B22312745 : Blo 377762 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 377762 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 377762 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 377762 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 377762 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 377762 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 377762 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 377762 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 377762 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 377762 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 377762 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 377762 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1375775 : Blo 377762 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B917183 : Blo 377762 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B611455 : Blo 377762 611455 := bstep (se 1 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 611455 = 917183) B917183
theorem B815273 : Blo 377762 815273 := bstep (se 2 (by rfl) ⟨305727, by rfl⟩ : syracuseStep 815273 = 611455) B611455
theorem B543515 : Blo 377762 543515 := bstep (se 1 (by rfl) ⟨407636, by rfl⟩ : syracuseStep 543515 = 815273) B815273
theorem B1449373 : Blo 377762 1449373 := bstep (se 3 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 1449373 = 543515) B543515
theorem B1932497 : Blo 377762 1932497 := bstep (se 2 (by rfl) ⟨724686, by rfl⟩ : syracuseStep 1932497 = 1449373) B1449373
theorem B1288331 : Blo 377762 1288331 := bstep (se 1 (by rfl) ⟨966248, by rfl⟩ : syracuseStep 1288331 = 1932497) B1932497
theorem B858887 : Blo 377762 858887 := bstep (se 1 (by rfl) ⟨644165, by rfl⟩ : syracuseStep 858887 = 1288331) B1288331
theorem B572591 : Blo 377762 572591 := bstep (se 1 (by rfl) ⟨429443, by rfl⟩ : syracuseStep 572591 = 858887) B858887
theorem B381727 : Blo 377762 381727 := bstep (se 1 (by rfl) ⟨286295, by rfl⟩ : syracuseStep 381727 = 572591) B572591

theorem C0 (j : ℕ) (h1 : 94440 ≤ j) (h2 : j ≤ 95139) : Blo 377762 (4 * j + 3) := by
  interval_cases j
  · exact B377763
  · exact B377767
  · exact B377771
  · exact B377775
  · exact B377779
  · exact B377783
  · exact B377787
  · exact B377791
  · exact B377795
  · exact B377799
  · exact B377803
  · exact B377807
  · exact B377811
  · exact B377815
  · exact B377819
  · exact B377823
  · exact B377827
  · exact B377831
  · exact B377835
  · exact B377839
  · exact B377843
  · exact B377847
  · exact B377851
  · exact B377855
  · exact B377859
  · exact B377863
  · exact B377867
  · exact B377871
  · exact B377875
  · exact B377879
  · exact B377883
  · exact B377887
  · exact B377891
  · exact B377895
  · exact B377899
  · exact B377903
  · exact B377907
  · exact B377911
  · exact B377915
  · exact B377919
  · exact B377923
  · exact B377927
  · exact B377931
  · exact B377935
  · exact B377939
  · exact B377943
  · exact B377947
  · exact B377951
  · exact B377955
  · exact B377959
  · exact B377963
  · exact B377967
  · exact B377971
  · exact B377975
  · exact B377979
  · exact B377983
  · exact B377987
  · exact B377991
  · exact B377995
  · exact B377999
  · exact B378003
  · exact B378007
  · exact B378011
  · exact B378015
  · exact B378019
  · exact B378023
  · exact B378027
  · exact B378031
  · exact B378035
  · exact B378039
  · exact B378043
  · exact B378047
  · exact B378051
  · exact B378055
  · exact B378059
  · exact B378063
  · exact B378067
  · exact B378071
  · exact B378075
  · exact B378079
  · exact B378083
  · exact B378087
  · exact B378091
  · exact B378095
  · exact B378099
  · exact B378103
  · exact B378107
  · exact B378111
  · exact B378115
  · exact B378119
  · exact B378123
  · exact B378127
  · exact B378131
  · exact B378135
  · exact B378139
  · exact B378143
  · exact B378147
  · exact B378151
  · exact B378155
  · exact B378159
  · exact B378163
  · exact B378167
  · exact B378171
  · exact B378175
  · exact B378179
  · exact B378183
  · exact B378187
  · exact B378191
  · exact B378195
  · exact B378199
  · exact B378203
  · exact B378207
  · exact B378211
  · exact B378215
  · exact B378219
  · exact B378223
  · exact B378227
  · exact B378231
  · exact B378235
  · exact B378239
  · exact B378243
  · exact B378247
  · exact B378251
  · exact B378255
  · exact B378259
  · exact B378263
  · exact B378267
  · exact B378271
  · exact B378275
  · exact B378279
  · exact B378283
  · exact B378287
  · exact B378291
  · exact B378295
  · exact B378299
  · exact B378303
  · exact B378307
  · exact B378311
  · exact B378315
  · exact B378319
  · exact B378323
  · exact B378327
  · exact B378331
  · exact B378335
  · exact B378339
  · exact B378343
  · exact B378347
  · exact B378351
  · exact B378355
  · exact B378359
  · exact B378363
  · exact B378367
  · exact B378371
  · exact B378375
  · exact B378379
  · exact B378383
  · exact B378387
  · exact B378391
  · exact B378395
  · exact B378399
  · exact B378403
  · exact B378407
  · exact B378411
  · exact B378415
  · exact B378419
  · exact B378423
  · exact B378427
  · exact B378431
  · exact B378435
  · exact B378439
  · exact B378443
  · exact B378447
  · exact B378451
  · exact B378455
  · exact B378459
  · exact B378463
  · exact B378467
  · exact B378471
  · exact B378475
  · exact B378479
  · exact B378483
  · exact B378487
  · exact B378491
  · exact B378495
  · exact B378499
  · exact B378503
  · exact B378507
  · exact B378511
  · exact B378515
  · exact B378519
  · exact B378523
  · exact B378527
  · exact B378531
  · exact B378535
  · exact B378539
  · exact B378543
  · exact B378547
  · exact B378551
  · exact B378555
  · exact B378559
  · exact B378563
  · exact B378567
  · exact B378571
  · exact B378575
  · exact B378579
  · exact B378583
  · exact B378587
  · exact B378591
  · exact B378595
  · exact B378599
  · exact B378603
  · exact B378607
  · exact B378611
  · exact B378615
  · exact B378619
  · exact B378623
  · exact B378627
  · exact B378631
  · exact B378635
  · exact B378639
  · exact B378643
  · exact B378647
  · exact B378651
  · exact B378655
  · exact B378659
  · exact B378663
  · exact B378667
  · exact B378671
  · exact B378675
  · exact B378679
  · exact B378683
  · exact B378687
  · exact B378691
  · exact B378695
  · exact B378699
  · exact B378703
  · exact B378707
  · exact B378711
  · exact B378715
  · exact B378719
  · exact B378723
  · exact B378727
  · exact B378731
  · exact B378735
  · exact B378739
  · exact B378743
  · exact B378747
  · exact B378751
  · exact B378755
  · exact B378759
  · exact B378763
  · exact B378767
  · exact B378771
  · exact B378775
  · exact B378779
  · exact B378783
  · exact B378787
  · exact B378791
  · exact B378795
  · exact B378799
  · exact B378803
  · exact B378807
  · exact B378811
  · exact B378815
  · exact B378819
  · exact B378823
  · exact B378827
  · exact B378831
  · exact B378835
  · exact B378839
  · exact B378843
  · exact B378847
  · exact B378851
  · exact B378855
  · exact B378859
  · exact B378863
  · exact B378867
  · exact B378871
  · exact B378875
  · exact B378879
  · exact B378883
  · exact B378887
  · exact B378891
  · exact B378895
  · exact B378899
  · exact B378903
  · exact B378907
  · exact B378911
  · exact B378915
  · exact B378919
  · exact B378923
  · exact B378927
  · exact B378931
  · exact B378935
  · exact B378939
  · exact B378943
  · exact B378947
  · exact B378951
  · exact B378955
  · exact B378959
  · exact B378963
  · exact B378967
  · exact B378971
  · exact B378975
  · exact B378979
  · exact B378983
  · exact B378987
  · exact B378991
  · exact B378995
  · exact B378999
  · exact B379003
  · exact B379007
  · exact B379011
  · exact B379015
  · exact B379019
  · exact B379023
  · exact B379027
  · exact B379031
  · exact B379035
  · exact B379039
  · exact B379043
  · exact B379047
  · exact B379051
  · exact B379055
  · exact B379059
  · exact B379063
  · exact B379067
  · exact B379071
  · exact B379075
  · exact B379079
  · exact B379083
  · exact B379087
  · exact B379091
  · exact B379095
  · exact B379099
  · exact B379103
  · exact B379107
  · exact B379111
  · exact B379115
  · exact B379119
  · exact B379123
  · exact B379127
  · exact B379131
  · exact B379135
  · exact B379139
  · exact B379143
  · exact B379147
  · exact B379151
  · exact B379155
  · exact B379159
  · exact B379163
  · exact B379167
  · exact B379171
  · exact B379175
  · exact B379179
  · exact B379183
  · exact B379187
  · exact B379191
  · exact B379195
  · exact B379199
  · exact B379203
  · exact B379207
  · exact B379211
  · exact B379215
  · exact B379219
  · exact B379223
  · exact B379227
  · exact B379231
  · exact B379235
  · exact B379239
  · exact B379243
  · exact B379247
  · exact B379251
  · exact B379255
  · exact B379259
  · exact B379263
  · exact B379267
  · exact B379271
  · exact B379275
  · exact B379279
  · exact B379283
  · exact B379287
  · exact B379291
  · exact B379295
  · exact B379299
  · exact B379303
  · exact B379307
  · exact B379311
  · exact B379315
  · exact B379319
  · exact B379323
  · exact B379327
  · exact B379331
  · exact B379335
  · exact B379339
  · exact B379343
  · exact B379347
  · exact B379351
  · exact B379355
  · exact B379359
  · exact B379363
  · exact B379367
  · exact B379371
  · exact B379375
  · exact B379379
  · exact B379383
  · exact B379387
  · exact B379391
  · exact B379395
  · exact B379399
  · exact B379403
  · exact B379407
  · exact B379411
  · exact B379415
  · exact B379419
  · exact B379423
  · exact B379427
  · exact B379431
  · exact B379435
  · exact B379439
  · exact B379443
  · exact B379447
  · exact B379451
  · exact B379455
  · exact B379459
  · exact B379463
  · exact B379467
  · exact B379471
  · exact B379475
  · exact B379479
  · exact B379483
  · exact B379487
  · exact B379491
  · exact B379495
  · exact B379499
  · exact B379503
  · exact B379507
  · exact B379511
  · exact B379515
  · exact B379519
  · exact B379523
  · exact B379527
  · exact B379531
  · exact B379535
  · exact B379539
  · exact B379543
  · exact B379547
  · exact B379551
  · exact B379555
  · exact B379559
  · exact B379563
  · exact B379567
  · exact B379571
  · exact B379575
  · exact B379579
  · exact B379583
  · exact B379587
  · exact B379591
  · exact B379595
  · exact B379599
  · exact B379603
  · exact B379607
  · exact B379611
  · exact B379615
  · exact B379619
  · exact B379623
  · exact B379627
  · exact B379631
  · exact B379635
  · exact B379639
  · exact B379643
  · exact B379647
  · exact B379651
  · exact B379655
  · exact B379659
  · exact B379663
  · exact B379667
  · exact B379671
  · exact B379675
  · exact B379679
  · exact B379683
  · exact B379687
  · exact B379691
  · exact B379695
  · exact B379699
  · exact B379703
  · exact B379707
  · exact B379711
  · exact B379715
  · exact B379719
  · exact B379723
  · exact B379727
  · exact B379731
  · exact B379735
  · exact B379739
  · exact B379743
  · exact B379747
  · exact B379751
  · exact B379755
  · exact B379759
  · exact B379763
  · exact B379767
  · exact B379771
  · exact B379775
  · exact B379779
  · exact B379783
  · exact B379787
  · exact B379791
  · exact B379795
  · exact B379799
  · exact B379803
  · exact B379807
  · exact B379811
  · exact B379815
  · exact B379819
  · exact B379823
  · exact B379827
  · exact B379831
  · exact B379835
  · exact B379839
  · exact B379843
  · exact B379847
  · exact B379851
  · exact B379855
  · exact B379859
  · exact B379863
  · exact B379867
  · exact B379871
  · exact B379875
  · exact B379879
  · exact B379883
  · exact B379887
  · exact B379891
  · exact B379895
  · exact B379899
  · exact B379903
  · exact B379907
  · exact B379911
  · exact B379915
  · exact B379919
  · exact B379923
  · exact B379927
  · exact B379931
  · exact B379935
  · exact B379939
  · exact B379943
  · exact B379947
  · exact B379951
  · exact B379955
  · exact B379959
  · exact B379963
  · exact B379967
  · exact B379971
  · exact B379975
  · exact B379979
  · exact B379983
  · exact B379987
  · exact B379991
  · exact B379995
  · exact B379999
  · exact B380003
  · exact B380007
  · exact B380011
  · exact B380015
  · exact B380019
  · exact B380023
  · exact B380027
  · exact B380031
  · exact B380035
  · exact B380039
  · exact B380043
  · exact B380047
  · exact B380051
  · exact B380055
  · exact B380059
  · exact B380063
  · exact B380067
  · exact B380071
  · exact B380075
  · exact B380079
  · exact B380083
  · exact B380087
  · exact B380091
  · exact B380095
  · exact B380099
  · exact B380103
  · exact B380107
  · exact B380111
  · exact B380115
  · exact B380119
  · exact B380123
  · exact B380127
  · exact B380131
  · exact B380135
  · exact B380139
  · exact B380143
  · exact B380147
  · exact B380151
  · exact B380155
  · exact B380159
  · exact B380163
  · exact B380167
  · exact B380171
  · exact B380175
  · exact B380179
  · exact B380183
  · exact B380187
  · exact B380191
  · exact B380195
  · exact B380199
  · exact B380203
  · exact B380207
  · exact B380211
  · exact B380215
  · exact B380219
  · exact B380223
  · exact B380227
  · exact B380231
  · exact B380235
  · exact B380239
  · exact B380243
  · exact B380247
  · exact B380251
  · exact B380255
  · exact B380259
  · exact B380263
  · exact B380267
  · exact B380271
  · exact B380275
  · exact B380279
  · exact B380283
  · exact B380287
  · exact B380291
  · exact B380295
  · exact B380299
  · exact B380303
  · exact B380307
  · exact B380311
  · exact B380315
  · exact B380319
  · exact B380323
  · exact B380327
  · exact B380331
  · exact B380335
  · exact B380339
  · exact B380343
  · exact B380347
  · exact B380351
  · exact B380355
  · exact B380359
  · exact B380363
  · exact B380367
  · exact B380371
  · exact B380375
  · exact B380379
  · exact B380383
  · exact B380387
  · exact B380391
  · exact B380395
  · exact B380399
  · exact B380403
  · exact B380407
  · exact B380411
  · exact B380415
  · exact B380419
  · exact B380423
  · exact B380427
  · exact B380431
  · exact B380435
  · exact B380439
  · exact B380443
  · exact B380447
  · exact B380451
  · exact B380455
  · exact B380459
  · exact B380463
  · exact B380467
  · exact B380471
  · exact B380475
  · exact B380479
  · exact B380483
  · exact B380487
  · exact B380491
  · exact B380495
  · exact B380499
  · exact B380503
  · exact B380507
  · exact B380511
  · exact B380515
  · exact B380519
  · exact B380523
  · exact B380527
  · exact B380531
  · exact B380535
  · exact B380539
  · exact B380543
  · exact B380547
  · exact B380551
  · exact B380555
  · exact B380559

theorem C1 (j : ℕ) (h1 : 95140 ≤ j) (h2 : j ≤ 95439) : Blo 377762 (4 * j + 3) := by
  interval_cases j
  · exact B380563
  · exact B380567
  · exact B380571
  · exact B380575
  · exact B380579
  · exact B380583
  · exact B380587
  · exact B380591
  · exact B380595
  · exact B380599
  · exact B380603
  · exact B380607
  · exact B380611
  · exact B380615
  · exact B380619
  · exact B380623
  · exact B380627
  · exact B380631
  · exact B380635
  · exact B380639
  · exact B380643
  · exact B380647
  · exact B380651
  · exact B380655
  · exact B380659
  · exact B380663
  · exact B380667
  · exact B380671
  · exact B380675
  · exact B380679
  · exact B380683
  · exact B380687
  · exact B380691
  · exact B380695
  · exact B380699
  · exact B380703
  · exact B380707
  · exact B380711
  · exact B380715
  · exact B380719
  · exact B380723
  · exact B380727
  · exact B380731
  · exact B380735
  · exact B380739
  · exact B380743
  · exact B380747
  · exact B380751
  · exact B380755
  · exact B380759
  · exact B380763
  · exact B380767
  · exact B380771
  · exact B380775
  · exact B380779
  · exact B380783
  · exact B380787
  · exact B380791
  · exact B380795
  · exact B380799
  · exact B380803
  · exact B380807
  · exact B380811
  · exact B380815
  · exact B380819
  · exact B380823
  · exact B380827
  · exact B380831
  · exact B380835
  · exact B380839
  · exact B380843
  · exact B380847
  · exact B380851
  · exact B380855
  · exact B380859
  · exact B380863
  · exact B380867
  · exact B380871
  · exact B380875
  · exact B380879
  · exact B380883
  · exact B380887
  · exact B380891
  · exact B380895
  · exact B380899
  · exact B380903
  · exact B380907
  · exact B380911
  · exact B380915
  · exact B380919
  · exact B380923
  · exact B380927
  · exact B380931
  · exact B380935
  · exact B380939
  · exact B380943
  · exact B380947
  · exact B380951
  · exact B380955
  · exact B380959
  · exact B380963
  · exact B380967
  · exact B380971
  · exact B380975
  · exact B380979
  · exact B380983
  · exact B380987
  · exact B380991
  · exact B380995
  · exact B380999
  · exact B381003
  · exact B381007
  · exact B381011
  · exact B381015
  · exact B381019
  · exact B381023
  · exact B381027
  · exact B381031
  · exact B381035
  · exact B381039
  · exact B381043
  · exact B381047
  · exact B381051
  · exact B381055
  · exact B381059
  · exact B381063
  · exact B381067
  · exact B381071
  · exact B381075
  · exact B381079
  · exact B381083
  · exact B381087
  · exact B381091
  · exact B381095
  · exact B381099
  · exact B381103
  · exact B381107
  · exact B381111
  · exact B381115
  · exact B381119
  · exact B381123
  · exact B381127
  · exact B381131
  · exact B381135
  · exact B381139
  · exact B381143
  · exact B381147
  · exact B381151
  · exact B381155
  · exact B381159
  · exact B381163
  · exact B381167
  · exact B381171
  · exact B381175
  · exact B381179
  · exact B381183
  · exact B381187
  · exact B381191
  · exact B381195
  · exact B381199
  · exact B381203
  · exact B381207
  · exact B381211
  · exact B381215
  · exact B381219
  · exact B381223
  · exact B381227
  · exact B381231
  · exact B381235
  · exact B381239
  · exact B381243
  · exact B381247
  · exact B381251
  · exact B381255
  · exact B381259
  · exact B381263
  · exact B381267
  · exact B381271
  · exact B381275
  · exact B381279
  · exact B381283
  · exact B381287
  · exact B381291
  · exact B381295
  · exact B381299
  · exact B381303
  · exact B381307
  · exact B381311
  · exact B381315
  · exact B381319
  · exact B381323
  · exact B381327
  · exact B381331
  · exact B381335
  · exact B381339
  · exact B381343
  · exact B381347
  · exact B381351
  · exact B381355
  · exact B381359
  · exact B381363
  · exact B381367
  · exact B381371
  · exact B381375
  · exact B381379
  · exact B381383
  · exact B381387
  · exact B381391
  · exact B381395
  · exact B381399
  · exact B381403
  · exact B381407
  · exact B381411
  · exact B381415
  · exact B381419
  · exact B381423
  · exact B381427
  · exact B381431
  · exact B381435
  · exact B381439
  · exact B381443
  · exact B381447
  · exact B381451
  · exact B381455
  · exact B381459
  · exact B381463
  · exact B381467
  · exact B381471
  · exact B381475
  · exact B381479
  · exact B381483
  · exact B381487
  · exact B381491
  · exact B381495
  · exact B381499
  · exact B381503
  · exact B381507
  · exact B381511
  · exact B381515
  · exact B381519
  · exact B381523
  · exact B381527
  · exact B381531
  · exact B381535
  · exact B381539
  · exact B381543
  · exact B381547
  · exact B381551
  · exact B381555
  · exact B381559
  · exact B381563
  · exact B381567
  · exact B381571
  · exact B381575
  · exact B381579
  · exact B381583
  · exact B381587
  · exact B381591
  · exact B381595
  · exact B381599
  · exact B381603
  · exact B381607
  · exact B381611
  · exact B381615
  · exact B381619
  · exact B381623
  · exact B381627
  · exact B381631
  · exact B381635
  · exact B381639
  · exact B381643
  · exact B381647
  · exact B381651
  · exact B381655
  · exact B381659
  · exact B381663
  · exact B381667
  · exact B381671
  · exact B381675
  · exact B381679
  · exact B381683
  · exact B381687
  · exact B381691
  · exact B381695
  · exact B381699
  · exact B381703
  · exact B381707
  · exact B381711
  · exact B381715
  · exact B381719
  · exact B381723
  · exact B381727
  · exact B381731
  · exact B381735
  · exact B381739
  · exact B381743
  · exact B381747
  · exact B381751
  · exact B381755
  · exact B381759

theorem solution (m : ℕ) (hlo : 377762 ≤ m) (hhi : m ≤ 381762) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 94440 ≤ j := by omega
    have hj2 : j ≤ 95439 := by omega
    have hb : Blo 377762 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 95140 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
