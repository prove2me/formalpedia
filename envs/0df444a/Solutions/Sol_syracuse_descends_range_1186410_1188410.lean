-- Prove2me | solution 1 for syracuse_descends_range_1186410_1188410
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:35.903081+00:00
-- url     : https://prove2.me/submissions/40902f65-dec8-49b1-9ff7-5f06037d8d3d

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


theorem B2670605 : Blo 1186410 2670605 := bbase (se 3 (by rfl) ⟨500738, by rfl⟩ : syracuseStep 2670605 = 1001477) (by norm_num)
theorem B5070869 : Blo 1186410 5070869 := bbase (se 6 (by rfl) ⟨118848, by rfl⟩ : syracuseStep 5070869 = 237697) (by norm_num)
theorem B1335325 : Blo 1186410 1335325 := bbase (se 3 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 1335325 = 500747) (by norm_num)
theorem B3006517 : Blo 1186410 3006517 := bbase (se 5 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 3006517 = 281861) (by norm_num)
theorem B1335361 : Blo 1186410 1335361 := bbase (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) (by norm_num)
theorem B2670677 : Blo 1186410 2670677 := bbase (se 8 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 2670677 = 31297) (by norm_num)
theorem B4005989 : Blo 1186410 4005989 := bbase (se 4 (by rfl) ⟨375561, by rfl⟩ : syracuseStep 4005989 = 751123) (by norm_num)
theorem B1335397 : Blo 1186410 1335397 := bbase (se 4 (by rfl) ⟨125193, by rfl⟩ : syracuseStep 1335397 = 250387) (by norm_num)
theorem B3211397 : Blo 1186410 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B1335433 : Blo 1186410 1335433 := bbase (se 2 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 1335433 = 1001575) (by norm_num)
theorem B1425557 : Blo 1186410 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B2670749 : Blo 1186410 2670749 := bbase (se 3 (by rfl) ⟨500765, by rfl⟩ : syracuseStep 2670749 = 1001531) (by norm_num)
theorem B3006629 : Blo 1186410 3006629 := bbase (se 4 (by rfl) ⟨281871, by rfl⟩ : syracuseStep 3006629 = 563743) (by norm_num)
theorem B1335469 : Blo 1186410 1335469 := bbase (se 3 (by rfl) ⟨250400, by rfl⟩ : syracuseStep 1335469 = 500801) (by norm_num)
theorem B3801269 : Blo 1186410 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B1425605 : Blo 1186410 1425605 := bbase (se 4 (by rfl) ⟨133650, by rfl⟩ : syracuseStep 1425605 = 267301) (by norm_num)
theorem B2253005 : Blo 1186410 2253005 := bbase (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) (by norm_num)
theorem B1335505 : Blo 1186410 1335505 := bbase (se 2 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 1335505 = 1001629) (by norm_num)
theorem B4505813 : Blo 1186410 4505813 := bbase (se 7 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 4505813 = 105605) (by norm_num)
theorem B2670821 : Blo 1186410 2670821 := bbase (se 4 (by rfl) ⟨250389, by rfl⟩ : syracuseStep 2670821 = 500779) (by norm_num)
theorem B1204465 : Blo 1186410 1204465 := bbase (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) (by norm_num)
theorem B1335541 : Blo 1186410 1335541 := bbase (se 5 (by rfl) ⟨62603, by rfl⟩ : syracuseStep 1335541 = 125207) (by norm_num)
theorem B2031877 : Blo 1186410 2031877 := bbase (se 4 (by rfl) ⟨190488, by rfl⟩ : syracuseStep 2031877 = 380977) (by norm_num)
theorem B1335577 : Blo 1186410 1335577 := bbase (se 2 (by rfl) ⟨500841, by rfl⟩ : syracuseStep 1335577 = 1001683) (by norm_num)
theorem B2670893 : Blo 1186410 2670893 := bbase (se 3 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 2670893 = 1001585) (by norm_num)
theorem B2007349 : Blo 1186410 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B1335613 : Blo 1186410 1335613 := bbase (se 3 (by rfl) ⟨250427, by rfl⟩ : syracuseStep 1335613 = 500855) (by norm_num)
theorem B6758741 : Blo 1186410 6758741 := bbase (se 10 (by rfl) ⟨9900, by rfl⟩ : syracuseStep 6758741 = 19801) (by norm_num)
theorem B1335649 : Blo 1186410 1335649 := bbase (se 2 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 1335649 = 1001737) (by norm_num)
theorem B3006821 : Blo 1186410 3006821 := bbase (se 4 (by rfl) ⟨281889, by rfl⟩ : syracuseStep 3006821 = 563779) (by norm_num)
theorem B2670965 : Blo 1186410 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B1335685 : Blo 1186410 1335685 := bbase (se 4 (by rfl) ⟨125220, by rfl⟩ : syracuseStep 1335685 = 250441) (by norm_num)
theorem B1712549 : Blo 1186410 1712549 := bbase (se 4 (by rfl) ⟨160551, by rfl⟩ : syracuseStep 1712549 = 321103) (by norm_num)
theorem B1335721 : Blo 1186410 1335721 := bbase (se 2 (by rfl) ⟨500895, by rfl⟩ : syracuseStep 1335721 = 1001791) (by norm_num)
theorem B2671037 : Blo 1186410 2671037 := bbase (se 3 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 2671037 = 1001639) (by norm_num)
theorem B1425865 : Blo 1186410 1425865 := bbase (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) (by norm_num)
theorem B1335757 : Blo 1186410 1335757 := bbase (se 3 (by rfl) ⟨250454, by rfl⟩ : syracuseStep 1335757 = 500909) (by norm_num)
theorem B1335793 : Blo 1186410 1335793 := bbase (se 2 (by rfl) ⟨500922, by rfl⟩ : syracuseStep 1335793 = 1001845) (by norm_num)
theorem B4506101 : Blo 1186410 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B1901045 : Blo 1186410 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B2671109 : Blo 1186410 2671109 := bbase (se 4 (by rfl) ⟨250416, by rfl⟩ : syracuseStep 2671109 = 500833) (by norm_num)
theorem B4006421 : Blo 1186410 4006421 := bbase (se 6 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 4006421 = 187801) (by norm_num)
theorem B1335829 : Blo 1186410 1335829 := bbase (se 6 (by rfl) ⟨31308, by rfl⟩ : syracuseStep 1335829 = 62617) (by norm_num)
theorem B2138653 : Blo 1186410 2138653 := bbase (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) (by norm_num)
theorem B12182069 : Blo 1186410 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B1335865 : Blo 1186410 1335865 := bbase (se 2 (by rfl) ⟨500949, by rfl⟩ : syracuseStep 1335865 = 1001899) (by norm_num)
theorem B2671181 : Blo 1186410 2671181 := bbase (se 3 (by rfl) ⟨500846, by rfl⟩ : syracuseStep 2671181 = 1001693) (by norm_num)
theorem B2851421 : Blo 1186410 2851421 := bbase (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) (by norm_num)
theorem B1335901 : Blo 1186410 1335901 := bbase (se 3 (by rfl) ⟨250481, by rfl⟩ : syracuseStep 1335901 = 500963) (by norm_num)
theorem B1335937 : Blo 1186410 1335937 := bbase (se 2 (by rfl) ⟨500976, by rfl⟩ : syracuseStep 1335937 = 1001953) (by norm_num)
theorem B2671253 : Blo 1186410 2671253 := bbase (se 6 (by rfl) ⟨62607, by rfl⟩ : syracuseStep 2671253 = 125215) (by norm_num)
theorem B4276901 : Blo 1186410 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B1335973 : Blo 1186410 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B3007165 : Blo 1186410 3007165 := bbase (se 3 (by rfl) ⟨563843, by rfl⟩ : syracuseStep 3007165 = 1127687) (by norm_num)
theorem B1336009 : Blo 1186410 1336009 := bbase (se 2 (by rfl) ⟨501003, by rfl⟩ : syracuseStep 1336009 = 1002007) (by norm_num)
theorem B1426129 : Blo 1186410 1426129 := bbase (se 2 (by rfl) ⟨534798, by rfl⟩ : syracuseStep 1426129 = 1069597) (by norm_num)
theorem B1335289 : Blo 1186410 1335289 := bbase (se 2 (by rfl) ⟨500733, by rfl⟩ : syracuseStep 1335289 = 1001467) (by norm_num)
theorem B2671325 : Blo 1186410 2671325 := bbase (se 3 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 2671325 = 1001747) (by norm_num)
theorem B1336045 : Blo 1186410 1336045 := bbase (se 3 (by rfl) ⟨250508, by rfl⟩ : syracuseStep 1336045 = 501017) (by norm_num)
theorem B2138869 : Blo 1186410 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B1336081 : Blo 1186410 1336081 := bbase (se 2 (by rfl) ⟨501030, by rfl⟩ : syracuseStep 1336081 = 1002061) (by norm_num)
theorem B2671397 : Blo 1186410 2671397 := bbase (se 4 (by rfl) ⟨250443, by rfl⟩ : syracuseStep 2671397 = 500887) (by norm_num)
theorem B3007277 : Blo 1186410 3007277 := bbase (se 3 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 3007277 = 1127729) (by norm_num)
theorem B1336117 : Blo 1186410 1336117 := bbase (se 5 (by rfl) ⟨62630, by rfl⟩ : syracuseStep 1336117 = 125261) (by norm_num)
theorem B1426249 : Blo 1186410 1426249 := bbase (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) (by norm_num)
theorem B1336153 : Blo 1186410 1336153 := bbase (se 2 (by rfl) ⟨501057, by rfl⟩ : syracuseStep 1336153 = 1002115) (by norm_num)
theorem B5137253 : Blo 1186410 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B2671469 : Blo 1186410 2671469 := bbase (se 3 (by rfl) ⟨500900, by rfl⟩ : syracuseStep 2671469 = 1001801) (by norm_num)
theorem B1336189 : Blo 1186410 1336189 := bbase (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) (by norm_num)
theorem B2032541 : Blo 1186410 2032541 := bbase (se 3 (by rfl) ⟨381101, by rfl⟩ : syracuseStep 2032541 = 762203) (by norm_num)
theorem B1336225 : Blo 1186410 1336225 := bbase (se 2 (by rfl) ⟨501084, by rfl⟩ : syracuseStep 1336225 = 1002169) (by norm_num)
theorem B2671541 : Blo 1186410 2671541 := bbase (se 5 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 2671541 = 250457) (by norm_num)
theorem B2253757 : Blo 1186410 2253757 := bbase (se 3 (by rfl) ⟨422579, by rfl⟩ : syracuseStep 2253757 = 845159) (by norm_num)
theorem B4006853 : Blo 1186410 4006853 := bbase (se 4 (by rfl) ⟨375642, by rfl⟩ : syracuseStep 4006853 = 751285) (by norm_num)
theorem B1336261 : Blo 1186410 1336261 := bbase (se 4 (by rfl) ⟨125274, by rfl⟩ : syracuseStep 1336261 = 250549) (by norm_num)
theorem B6013925 : Blo 1186410 6013925 := bbase (se 4 (by rfl) ⟨563805, by rfl⟩ : syracuseStep 6013925 = 1127611) (by norm_num)
theorem B1336297 : Blo 1186410 1336297 := bbase (se 2 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 1336297 = 1002223) (by norm_num)
theorem B3007469 : Blo 1186410 3007469 := bbase (se 3 (by rfl) ⟨563900, by rfl⟩ : syracuseStep 3007469 = 1127801) (by norm_num)
theorem B2671613 : Blo 1186410 2671613 := bbase (se 3 (by rfl) ⟨500927, by rfl⟩ : syracuseStep 2671613 = 1001855) (by norm_num)
theorem B1336333 : Blo 1186410 1336333 := bbase (se 3 (by rfl) ⟨250562, by rfl⟩ : syracuseStep 1336333 = 501125) (by norm_num)
theorem B1336369 : Blo 1186410 1336369 := bbase (se 2 (by rfl) ⟨501138, by rfl⟩ : syracuseStep 1336369 = 1002277) (by norm_num)
theorem B6947893 : Blo 1186410 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B2671685 : Blo 1186410 2671685 := bbase (se 4 (by rfl) ⟨250470, by rfl⟩ : syracuseStep 2671685 = 500941) (by norm_num)
theorem B2253901 : Blo 1186410 2253901 := bbase (se 3 (by rfl) ⟨422606, by rfl⟩ : syracuseStep 2253901 = 845213) (by norm_num)
theorem B1336405 : Blo 1186410 1336405 := bbase (se 8 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 1336405 = 15661) (by norm_num)
theorem B26395733 : Blo 1186410 26395733 := bbase (se 8 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 26395733 = 309325) (by norm_num)
theorem B1336441 : Blo 1186410 1336441 := bbase (se 2 (by rfl) ⟨501165, by rfl⟩ : syracuseStep 1336441 = 1002331) (by norm_num)
theorem B2671757 : Blo 1186410 2671757 := bbase (se 3 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 2671757 = 1001909) (by norm_num)
theorem B2892941 : Blo 1186410 2892941 := bbase (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) (by norm_num)
theorem B1336477 : Blo 1186410 1336477 := bbase (se 3 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 1336477 = 501179) (by norm_num)
theorem B1336513 : Blo 1186410 1336513 := bbase (se 2 (by rfl) ⟨501192, by rfl⟩ : syracuseStep 1336513 = 1002385) (by norm_num)
theorem B2671829 : Blo 1186410 2671829 := bbase (se 7 (by rfl) ⟨31310, by rfl⟩ : syracuseStep 2671829 = 62621) (by norm_num)
theorem B1336549 : Blo 1186410 1336549 := bbase (se 4 (by rfl) ⟨125301, by rfl⟩ : syracuseStep 1336549 = 250603) (by norm_num)
theorem B2254061 : Blo 1186410 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B1336585 : Blo 1186410 1336585 := bbase (se 2 (by rfl) ⟨501219, by rfl⟩ : syracuseStep 1336585 = 1002439) (by norm_num)
theorem B4818197 : Blo 1186410 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B2671901 : Blo 1186410 2671901 := bbase (se 3 (by rfl) ⟨500981, by rfl⟩ : syracuseStep 2671901 = 1001963) (by norm_num)
theorem B1336621 : Blo 1186410 1336621 := bbase (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) (by norm_num)
theorem B2475317 : Blo 1186410 2475317 := bbase (se 5 (by rfl) ⟨116030, by rfl⟩ : syracuseStep 2475317 = 232061) (by norm_num)
theorem B3007813 : Blo 1186410 3007813 := bbase (se 4 (by rfl) ⟨281982, by rfl⟩ : syracuseStep 3007813 = 563965) (by norm_num)
theorem B1336657 : Blo 1186410 1336657 := bbase (se 2 (by rfl) ⟨501246, by rfl⟩ : syracuseStep 1336657 = 1002493) (by norm_num)
theorem B2671973 : Blo 1186410 2671973 := bbase (se 4 (by rfl) ⟨250497, by rfl⟩ : syracuseStep 2671973 = 500995) (by norm_num)
theorem B4007285 : Blo 1186410 4007285 := bbase (se 5 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 4007285 = 375683) (by norm_num)
theorem B1336693 : Blo 1186410 1336693 := bbase (se 5 (by rfl) ⟨62657, by rfl⟩ : syracuseStep 1336693 = 125315) (by norm_num)
theorem B2254205 : Blo 1186410 2254205 := bbase (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) (by norm_num)
theorem B13534613 : Blo 1186410 13534613 := bbase (se 6 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 13534613 = 634435) (by norm_num)
theorem B1336729 : Blo 1186410 1336729 := bbase (se 2 (by rfl) ⟨501273, by rfl⟩ : syracuseStep 1336729 = 1002547) (by norm_num)
theorem B2672045 : Blo 1186410 2672045 := bbase (se 3 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 2672045 = 1002017) (by norm_num)
theorem B3007925 : Blo 1186410 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B1336765 : Blo 1186410 1336765 := bbase (se 3 (by rfl) ⟨250643, by rfl⟩ : syracuseStep 1336765 = 501287) (by norm_num)
theorem B3048893 : Blo 1186410 3048893 := bbase (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) (by norm_num)
theorem B1902037 : Blo 1186410 1902037 := bbase (se 7 (by rfl) ⟨22289, by rfl⟩ : syracuseStep 1902037 = 44579) (by norm_num)
theorem B1336801 : Blo 1186410 1336801 := bbase (se 2 (by rfl) ⟨501300, by rfl⟩ : syracuseStep 1336801 = 1002601) (by norm_num)
theorem B2672117 : Blo 1186410 2672117 := bbase (se 5 (by rfl) ⟨125255, by rfl⟩ : syracuseStep 2672117 = 250511) (by norm_num)
theorem B3253765 : Blo 1186410 3253765 := bbase (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) (by norm_num)
theorem B1336837 : Blo 1186410 1336837 := bbase (se 4 (by rfl) ⟨125328, by rfl⟩ : syracuseStep 1336837 = 250657) (by norm_num)
theorem B3048997 : Blo 1186410 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B1336873 : Blo 1186410 1336873 := bbase (se 2 (by rfl) ⟨501327, by rfl⟩ : syracuseStep 1336873 = 1002655) (by norm_num)
theorem B2672189 : Blo 1186410 2672189 := bbase (se 3 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 2672189 = 1002071) (by norm_num)
theorem B1336909 : Blo 1186410 1336909 := bbase (se 3 (by rfl) ⟨250670, by rfl⟩ : syracuseStep 1336909 = 501341) (by norm_num)
theorem B1336945 : Blo 1186410 1336945 := bbase (se 2 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 1336945 = 1002709) (by norm_num)
theorem B3008117 : Blo 1186410 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B1353349 : Blo 1186410 1353349 := bbase (se 4 (by rfl) ⟨126876, by rfl⟩ : syracuseStep 1353349 = 253753) (by norm_num)
theorem B2672261 : Blo 1186410 2672261 := bbase (se 4 (by rfl) ⟨250524, by rfl⟩ : syracuseStep 2672261 = 501049) (by norm_num)
theorem B4507285 : Blo 1186410 4507285 := bbase (se 6 (by rfl) ⟨105639, by rfl⟩ : syracuseStep 4507285 = 211279) (by norm_num)
theorem B2254493 : Blo 1186410 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B1427105 : Blo 1186410 1427105 := bbase (se 2 (by rfl) ⟨535164, by rfl⟩ : syracuseStep 1427105 = 1070329) (by norm_num)
theorem B2672333 : Blo 1186410 2672333 := bbase (se 3 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 2672333 = 1002125) (by norm_num)
theorem B3049181 : Blo 1186410 3049181 := bbase (se 3 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 3049181 = 1143443) (by norm_num)
theorem B5072645 : Blo 1186410 5072645 := bbase (se 4 (by rfl) ⟨475560, by rfl⟩ : syracuseStep 5072645 = 951121) (by norm_num)
theorem B2672405 : Blo 1186410 2672405 := bbase (se 6 (by rfl) ⟨62634, by rfl⟩ : syracuseStep 2672405 = 125269) (by norm_num)
theorem B4007717 : Blo 1186410 4007717 := bbase (se 4 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 4007717 = 751447) (by norm_num)
theorem B10282805 : Blo 1186410 10282805 := bbase (se 5 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 10282805 = 964013) (by norm_num)
theorem B2254645 : Blo 1186410 2254645 := bbase (se 5 (by rfl) ⟨105686, by rfl⟩ : syracuseStep 2254645 = 211373) (by norm_num)
theorem B2672477 : Blo 1186410 2672477 := bbase (se 3 (by rfl) ⟨501089, by rfl⟩ : syracuseStep 2672477 = 1002179) (by norm_num)
theorem B1353577 : Blo 1186410 1353577 := bbase (se 2 (by rfl) ⟨507591, by rfl⟩ : syracuseStep 1353577 = 1015183) (by norm_num)
theorem B2140037 : Blo 1186410 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B1902485 : Blo 1186410 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B2672549 : Blo 1186410 2672549 := bbase (se 4 (by rfl) ⟨250551, by rfl⟩ : syracuseStep 2672549 = 501103) (by norm_num)
theorem B1779629 : Blo 1186410 1779629 := bbase (se 3 (by rfl) ⟨333680, by rfl⟩ : syracuseStep 1779629 = 667361) (by norm_num)
theorem B1779653 : Blo 1186410 1779653 := bbase (se 4 (by rfl) ⟨166842, by rfl⟩ : syracuseStep 1779653 = 333685) (by norm_num)
theorem B4507589 : Blo 1186410 4507589 := bbase (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) (by norm_num)
theorem B1779677 : Blo 1186410 1779677 := bbase (se 3 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 1779677 = 667379) (by norm_num)
theorem B2672621 : Blo 1186410 2672621 := bbase (se 3 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 2672621 = 1002233) (by norm_num)
theorem B1779701 : Blo 1186410 1779701 := bbase (se 5 (by rfl) ⟨83423, by rfl⟩ : syracuseStep 1779701 = 166847) (by norm_num)
theorem B1689589 : Blo 1186410 1689589 := bbase (se 5 (by rfl) ⟨79199, by rfl⟩ : syracuseStep 1689589 = 158399) (by norm_num)
theorem B3803125 : Blo 1186410 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B1779725 : Blo 1186410 1779725 := bbase (se 3 (by rfl) ⟨333698, by rfl⟩ : syracuseStep 1779725 = 667397) (by norm_num)
theorem B1779749 : Blo 1186410 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B2672693 : Blo 1186410 2672693 := bbase (se 5 (by rfl) ⟨125282, by rfl⟩ : syracuseStep 2672693 = 250565) (by norm_num)
theorem B1779773 : Blo 1186410 1779773 := bbase (se 3 (by rfl) ⟨333707, by rfl⟩ : syracuseStep 1779773 = 667415) (by norm_num)
theorem B1779797 : Blo 1186410 1779797 := bbase (se 8 (by rfl) ⟨10428, by rfl⟩ : syracuseStep 1779797 = 20857) (by norm_num)
theorem B8562773 : Blo 1186410 8562773 := bbase (se 8 (by rfl) ⟨50172, by rfl⟩ : syracuseStep 8562773 = 100345) (by norm_num)
theorem B1902685 : Blo 1186410 1902685 := bbase (se 3 (by rfl) ⟨356753, by rfl⟩ : syracuseStep 1902685 = 713507) (by norm_num)
theorem B2254949 : Blo 1186410 2254949 := bbase (se 4 (by rfl) ⟨211401, by rfl⟩ : syracuseStep 2254949 = 422803) (by norm_num)
theorem B1779821 : Blo 1186410 1779821 := bbase (se 3 (by rfl) ⟨333716, by rfl⟩ : syracuseStep 1779821 = 667433) (by norm_num)
theorem B2672765 : Blo 1186410 2672765 := bbase (se 3 (by rfl) ⟨501143, by rfl⟩ : syracuseStep 2672765 = 1002287) (by norm_num)
theorem B1779845 : Blo 1186410 1779845 := bbase (se 4 (by rfl) ⟨166860, by rfl⟩ : syracuseStep 1779845 = 333721) (by norm_num)
theorem B1779869 : Blo 1186410 1779869 := bbase (se 3 (by rfl) ⟨333725, by rfl⟩ : syracuseStep 1779869 = 667451) (by norm_num)
theorem B1779893 : Blo 1186410 1779893 := bbase (se 5 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 1779893 = 166865) (by norm_num)
theorem B7604405 : Blo 1186410 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B2672837 : Blo 1186410 2672837 := bbase (se 4 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 2672837 = 501157) (by norm_num)
theorem B1779917 : Blo 1186410 1779917 := bbase (se 3 (by rfl) ⟨333734, by rfl⟩ : syracuseStep 1779917 = 667469) (by norm_num)
theorem B4008149 : Blo 1186410 4008149 := bbase (se 7 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 4008149 = 93941) (by norm_num)
theorem B1779941 : Blo 1186410 1779941 := bbase (se 4 (by rfl) ⟨166869, by rfl⟩ : syracuseStep 1779941 = 333739) (by norm_num)
theorem B6015221 : Blo 1186410 6015221 := bbase (se 5 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 6015221 = 563927) (by norm_num)
theorem B1779965 : Blo 1186410 1779965 := bbase (se 3 (by rfl) ⟨333743, by rfl⟩ : syracuseStep 1779965 = 667487) (by norm_num)
theorem B2672909 : Blo 1186410 2672909 := bbase (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) (by norm_num)
theorem B1354001 : Blo 1186410 1354001 := bbase (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) (by norm_num)
theorem B1779989 : Blo 1186410 1779989 := bbase (se 6 (by rfl) ⟨41718, by rfl⟩ : syracuseStep 1779989 = 83437) (by norm_num)
theorem B1780013 : Blo 1186410 1780013 := bbase (se 3 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 1780013 = 667505) (by norm_num)
theorem B2853181 : Blo 1186410 2853181 := bbase (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) (by norm_num)
theorem B1780037 : Blo 1186410 1780037 := bbase (se 4 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 1780037 = 333757) (by norm_num)
theorem B1689925 : Blo 1186410 1689925 := bbase (se 4 (by rfl) ⟨158430, by rfl⟩ : syracuseStep 1689925 = 316861) (by norm_num)
theorem B3254597 : Blo 1186410 3254597 := bbase (se 4 (by rfl) ⟨305118, by rfl⟩ : syracuseStep 3254597 = 610237) (by norm_num)
theorem B2672981 : Blo 1186410 2672981 := bbase (se 10 (by rfl) ⟨3915, by rfl⟩ : syracuseStep 2672981 = 7831) (by norm_num)
theorem B1780061 : Blo 1186410 1780061 := bbase (se 3 (by rfl) ⟨333761, by rfl⟩ : syracuseStep 1780061 = 667523) (by norm_num)
theorem B1902941 : Blo 1186410 1902941 := bbase (se 3 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 1902941 = 713603) (by norm_num)
theorem B10135925 : Blo 1186410 10135925 := bbase (se 5 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 10135925 = 950243) (by norm_num)
theorem B1780085 : Blo 1186410 1780085 := bbase (se 5 (by rfl) ⟨83441, by rfl⟩ : syracuseStep 1780085 = 166883) (by norm_num)
theorem B1501573 : Blo 1186410 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B1780109 : Blo 1186410 1780109 := bbase (se 3 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 1780109 = 667541) (by norm_num)
theorem B2673053 : Blo 1186410 2673053 := bbase (se 3 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 2673053 = 1002395) (by norm_num)
theorem B1780133 : Blo 1186410 1780133 := bbase (se 4 (by rfl) ⟨166887, by rfl⟩ : syracuseStep 1780133 = 333775) (by norm_num)
theorem B1780157 : Blo 1186410 1780157 := bbase (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) (by norm_num)
theorem B1780181 : Blo 1186410 1780181 := bbase (se 7 (by rfl) ⟨20861, by rfl⟩ : syracuseStep 1780181 = 41723) (by norm_num)
theorem B21121493 : Blo 1186410 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B1501669 : Blo 1186410 1501669 := bbase (se 4 (by rfl) ⟨140781, by rfl⟩ : syracuseStep 1501669 = 281563) (by norm_num)
theorem B2673125 : Blo 1186410 2673125 := bbase (se 4 (by rfl) ⟨250605, by rfl⟩ : syracuseStep 2673125 = 501211) (by norm_num)
theorem B1780205 : Blo 1186410 1780205 := bbase (se 3 (by rfl) ⟨333788, by rfl⟩ : syracuseStep 1780205 = 667577) (by norm_num)
theorem B1780229 : Blo 1186410 1780229 := bbase (se 4 (by rfl) ⟨166896, by rfl⟩ : syracuseStep 1780229 = 333793) (by norm_num)
theorem B1780253 : Blo 1186410 1780253 := bbase (se 3 (by rfl) ⟨333797, by rfl⟩ : syracuseStep 1780253 = 667595) (by norm_num)
theorem B1690141 : Blo 1186410 1690141 := bbase (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) (by norm_num)
theorem B2853413 : Blo 1186410 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B2673197 : Blo 1186410 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B1780277 : Blo 1186410 1780277 := bbase (se 5 (by rfl) ⟨83450, by rfl⟩ : syracuseStep 1780277 = 166901) (by norm_num)
theorem B1780301 : Blo 1186410 1780301 := bbase (se 3 (by rfl) ⟨333806, by rfl⟩ : syracuseStep 1780301 = 667613) (by norm_num)
theorem B1780325 : Blo 1186410 1780325 := bbase (se 4 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 1780325 = 333811) (by norm_num)
theorem B2673269 : Blo 1186410 2673269 := bbase (se 5 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 2673269 = 250619) (by norm_num)
theorem B1780349 : Blo 1186410 1780349 := bbase (se 3 (by rfl) ⟨333815, by rfl⟩ : syracuseStep 1780349 = 667631) (by norm_num)
theorem B4008581 : Blo 1186410 4008581 := bbase (se 4 (by rfl) ⟨375804, by rfl⟩ : syracuseStep 4008581 = 751609) (by norm_num)
theorem B1501841 : Blo 1186410 1501841 := bbase (se 2 (by rfl) ⟨563190, by rfl⟩ : syracuseStep 1501841 = 1126381) (by norm_num)
theorem B6007445 : Blo 1186410 6007445 := bbase (se 6 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 6007445 = 281599) (by norm_num)
theorem B1780373 : Blo 1186410 1780373 := bbase (se 6 (by rfl) ⟨41727, by rfl⟩ : syracuseStep 1780373 = 83455) (by norm_num)
theorem B2706077 : Blo 1186410 2706077 := bbase (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) (by norm_num)
theorem B1780397 : Blo 1186410 1780397 := bbase (se 3 (by rfl) ⟨333824, by rfl⟩ : syracuseStep 1780397 = 667649) (by norm_num)
theorem B2673341 : Blo 1186410 2673341 := bbase (se 3 (by rfl) ⟨501251, by rfl⟩ : syracuseStep 2673341 = 1002503) (by norm_num)
theorem B1780421 : Blo 1186410 1780421 := bbase (se 4 (by rfl) ⟨166914, by rfl⟩ : syracuseStep 1780421 = 333829) (by norm_num)
theorem B1501897 : Blo 1186410 1501897 := bbase (se 2 (by rfl) ⟨563211, by rfl⟩ : syracuseStep 1501897 = 1126423) (by norm_num)
theorem B1780445 : Blo 1186410 1780445 := bbase (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) (by norm_num)
theorem B2706149 : Blo 1186410 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B1780469 : Blo 1186410 1780469 := bbase (se 5 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 1780469 = 166919) (by norm_num)
theorem B2673413 : Blo 1186410 2673413 := bbase (se 4 (by rfl) ⟨250632, by rfl⟩ : syracuseStep 2673413 = 501265) (by norm_num)
theorem B1780493 : Blo 1186410 1780493 := bbase (se 3 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 1780493 = 667685) (by norm_num)
theorem B1780517 : Blo 1186410 1780517 := bbase (se 4 (by rfl) ⟨166923, by rfl⟩ : syracuseStep 1780517 = 333847) (by norm_num)
theorem B1501993 : Blo 1186410 1501993 := bbase (se 2 (by rfl) ⟨563247, by rfl⟩ : syracuseStep 1501993 = 1126495) (by norm_num)
theorem B1780541 : Blo 1186410 1780541 := bbase (se 3 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 1780541 = 667703) (by norm_num)
theorem B2673485 : Blo 1186410 2673485 := bbase (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) (by norm_num)
theorem B1805141 : Blo 1186410 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B1780565 : Blo 1186410 1780565 := bbase (se 9 (by rfl) ⟨5216, by rfl⟩ : syracuseStep 1780565 = 10433) (by norm_num)
theorem B2255701 : Blo 1186410 2255701 := bbase (se 9 (by rfl) ⟨6608, by rfl⟩ : syracuseStep 2255701 = 13217) (by norm_num)
theorem B1780589 : Blo 1186410 1780589 := bbase (se 3 (by rfl) ⟨333860, by rfl⟩ : syracuseStep 1780589 = 667721) (by norm_num)
theorem B1780613 : Blo 1186410 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B1690517 : Blo 1186410 1690517 := bbase (se 6 (by rfl) ⟨39621, by rfl⟩ : syracuseStep 1690517 = 79243) (by norm_num)
theorem B2673557 : Blo 1186410 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B1780637 : Blo 1186410 1780637 := bbase (se 3 (by rfl) ⟨333869, by rfl⟩ : syracuseStep 1780637 = 667739) (by norm_num)
theorem B5704613 : Blo 1186410 5704613 := bbase (se 4 (by rfl) ⟨534807, by rfl⟩ : syracuseStep 5704613 = 1069615) (by norm_num)
theorem B2853805 : Blo 1186410 2853805 := bbase (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) (by norm_num)
theorem B1780661 : Blo 1186410 1780661 := bbase (se 5 (by rfl) ⟨83468, by rfl⟩ : syracuseStep 1780661 = 166937) (by norm_num)
theorem B2534341 : Blo 1186410 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B1780685 : Blo 1186410 1780685 := bbase (se 3 (by rfl) ⟨333878, by rfl⟩ : syracuseStep 1780685 = 667757) (by norm_num)
theorem B1502165 : Blo 1186410 1502165 := bbase (se 7 (by rfl) ⟨17603, by rfl⟩ : syracuseStep 1502165 = 35207) (by norm_num)
theorem B2673629 : Blo 1186410 2673629 := bbase (se 3 (by rfl) ⟨501305, by rfl⟩ : syracuseStep 2673629 = 1002611) (by norm_num)
theorem B1780709 : Blo 1186410 1780709 := bbase (se 4 (by rfl) ⟨166941, by rfl⟩ : syracuseStep 1780709 = 333883) (by norm_num)
theorem B2255845 : Blo 1186410 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B1780733 : Blo 1186410 1780733 := bbase (se 3 (by rfl) ⟨333887, by rfl⟩ : syracuseStep 1780733 = 667775) (by norm_num)
theorem B1502221 : Blo 1186410 1502221 := bbase (se 3 (by rfl) ⟨281666, by rfl⟩ : syracuseStep 1502221 = 563333) (by norm_num)
theorem B1780757 : Blo 1186410 1780757 := bbase (se 6 (by rfl) ⟨41736, by rfl⟩ : syracuseStep 1780757 = 83473) (by norm_num)
theorem B2673701 : Blo 1186410 2673701 := bbase (se 4 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 2673701 = 501319) (by norm_num)
theorem B1780781 : Blo 1186410 1780781 := bbase (se 3 (by rfl) ⟨333896, by rfl⟩ : syracuseStep 1780781 = 667793) (by norm_num)
theorem B1805365 : Blo 1186410 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B4009013 : Blo 1186410 4009013 := bbase (se 5 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 4009013 = 375845) (by norm_num)
theorem B1780805 : Blo 1186410 1780805 := bbase (se 4 (by rfl) ⟨166950, by rfl⟩ : syracuseStep 1780805 = 333901) (by norm_num)
theorem B1780829 : Blo 1186410 1780829 := bbase (se 3 (by rfl) ⟨333905, by rfl⟩ : syracuseStep 1780829 = 667811) (by norm_num)
theorem B1444969 : Blo 1186410 1444969 := bbase (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) (by norm_num)
theorem B1502317 : Blo 1186410 1502317 := bbase (se 3 (by rfl) ⟨281684, by rfl⟩ : syracuseStep 1502317 = 563369) (by norm_num)
theorem B2673773 : Blo 1186410 2673773 := bbase (se 3 (by rfl) ⟨501332, by rfl⟩ : syracuseStep 2673773 = 1002665) (by norm_num)
theorem B1780853 : Blo 1186410 1780853 := bbase (se 5 (by rfl) ⟨83477, by rfl⟩ : syracuseStep 1780853 = 166955) (by norm_num)
theorem B2256005 : Blo 1186410 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1780877 : Blo 1186410 1780877 := bbase (se 3 (by rfl) ⟨333914, by rfl⟩ : syracuseStep 1780877 = 667829) (by norm_num)
theorem B1780901 : Blo 1186410 1780901 := bbase (se 4 (by rfl) ⟨166959, by rfl⟩ : syracuseStep 1780901 = 333919) (by norm_num)
theorem B2673845 : Blo 1186410 2673845 := bbase (se 5 (by rfl) ⟨125336, by rfl⟩ : syracuseStep 2673845 = 250673) (by norm_num)
theorem B1780925 : Blo 1186410 1780925 := bbase (se 3 (by rfl) ⟨333923, by rfl⟩ : syracuseStep 1780925 = 667847) (by norm_num)
theorem B2002117 : Blo 1186410 2002117 := bbase (se 4 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 2002117 = 375397) (by norm_num)
theorem B1780949 : Blo 1186410 1780949 := bbase (se 7 (by rfl) ⟨20870, by rfl⟩ : syracuseStep 1780949 = 41741) (by norm_num)
theorem B1780973 : Blo 1186410 1780973 := bbase (se 3 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 1780973 = 667865) (by norm_num)
theorem B2673917 : Blo 1186410 2673917 := bbase (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) (by norm_num)
theorem B1780997 : Blo 1186410 1780997 := bbase (se 4 (by rfl) ⟨166968, by rfl⟩ : syracuseStep 1780997 = 333937) (by norm_num)
theorem B1502489 : Blo 1186410 1502489 := bbase (se 2 (by rfl) ⟨563433, by rfl⟩ : syracuseStep 1502489 = 1126867) (by norm_num)
theorem B2002205 : Blo 1186410 2002205 := bbase (se 3 (by rfl) ⟨375413, by rfl⟩ : syracuseStep 2002205 = 750827) (by norm_num)
theorem B1781021 : Blo 1186410 1781021 := bbase (se 3 (by rfl) ⟨333941, by rfl⟩ : syracuseStep 1781021 = 667883) (by norm_num)
theorem B1781045 : Blo 1186410 1781045 := bbase (se 5 (by rfl) ⟨83486, by rfl⟩ : syracuseStep 1781045 = 166973) (by norm_num)
theorem B1781069 : Blo 1186410 1781069 := bbase (se 3 (by rfl) ⟨333950, by rfl⟩ : syracuseStep 1781069 = 667901) (by norm_num)
theorem B1502545 : Blo 1186410 1502545 := bbase (se 2 (by rfl) ⟨563454, by rfl⟩ : syracuseStep 1502545 = 1126909) (by norm_num)
theorem B1781093 : Blo 1186410 1781093 := bbase (se 4 (by rfl) ⟨166977, by rfl⟩ : syracuseStep 1781093 = 333955) (by norm_num)
theorem B4812149 : Blo 1186410 4812149 := bbase (se 5 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 4812149 = 451139) (by norm_num)
theorem B1781117 : Blo 1186410 1781117 := bbase (se 3 (by rfl) ⟨333959, by rfl⟩ : syracuseStep 1781117 = 667919) (by norm_num)
theorem B1781141 : Blo 1186410 1781141 := bbase (se 6 (by rfl) ⟨41745, by rfl⟩ : syracuseStep 1781141 = 83491) (by norm_num)
theorem B2002333 : Blo 1186410 2002333 := bbase (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) (by norm_num)
theorem B1781165 : Blo 1186410 1781165 := bbase (se 3 (by rfl) ⟨333968, by rfl⟩ : syracuseStep 1781165 = 667937) (by norm_num)
theorem B1502641 : Blo 1186410 1502641 := bbase (se 2 (by rfl) ⟨563490, by rfl⟩ : syracuseStep 1502641 = 1126981) (by norm_num)
theorem B1781189 : Blo 1186410 1781189 := bbase (se 4 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 1781189 = 333973) (by norm_num)
theorem B1781213 : Blo 1186410 1781213 := bbase (se 3 (by rfl) ⟨333977, by rfl⟩ : syracuseStep 1781213 = 667955) (by norm_num)
theorem B4009445 : Blo 1186410 4009445 := bbase (se 4 (by rfl) ⟨375885, by rfl⟩ : syracuseStep 4009445 = 751771) (by norm_num)
theorem B2002421 : Blo 1186410 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B1781237 : Blo 1186410 1781237 := bbase (se 5 (by rfl) ⟨83495, by rfl⟩ : syracuseStep 1781237 = 166991) (by norm_num)
theorem B1781261 : Blo 1186410 1781261 := bbase (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) (by norm_num)
theorem B1781285 : Blo 1186410 1781285 := bbase (se 4 (by rfl) ⟨166995, by rfl⟩ : syracuseStep 1781285 = 333991) (by norm_num)
theorem B1781309 : Blo 1186410 1781309 := bbase (se 3 (by rfl) ⟨333995, by rfl⟩ : syracuseStep 1781309 = 667991) (by norm_num)
theorem B1781333 : Blo 1186410 1781333 := bbase (se 8 (by rfl) ⟨10437, by rfl⟩ : syracuseStep 1781333 = 20875) (by norm_num)
theorem B1502813 : Blo 1186410 1502813 := bbase (se 3 (by rfl) ⟨281777, by rfl⟩ : syracuseStep 1502813 = 563555) (by norm_num)
theorem B1781357 : Blo 1186410 1781357 := bbase (se 3 (by rfl) ⟨334004, by rfl⟩ : syracuseStep 1781357 = 668009) (by norm_num)
theorem B2002549 : Blo 1186410 2002549 := bbase (se 5 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 2002549 = 187739) (by norm_num)
theorem B1781381 : Blo 1186410 1781381 := bbase (se 4 (by rfl) ⟨167004, by rfl⟩ : syracuseStep 1781381 = 334009) (by norm_num)
theorem B1502869 : Blo 1186410 1502869 := bbase (se 6 (by rfl) ⟨35223, by rfl⟩ : syracuseStep 1502869 = 70447) (by norm_num)
theorem B1781405 : Blo 1186410 1781405 := bbase (se 3 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 1781405 = 668027) (by norm_num)
theorem B1781429 : Blo 1186410 1781429 := bbase (se 5 (by rfl) ⟨83504, by rfl⟩ : syracuseStep 1781429 = 167009) (by norm_num)
theorem B2002637 : Blo 1186410 2002637 := bbase (se 3 (by rfl) ⟨375494, by rfl⟩ : syracuseStep 2002637 = 750989) (by norm_num)
theorem B1781453 : Blo 1186410 1781453 := bbase (se 3 (by rfl) ⟨334022, by rfl⟩ : syracuseStep 1781453 = 668045) (by norm_num)
theorem B1781477 : Blo 1186410 1781477 := bbase (se 4 (by rfl) ⟨167013, by rfl⟩ : syracuseStep 1781477 = 334027) (by norm_num)
theorem B1502965 : Blo 1186410 1502965 := bbase (se 5 (by rfl) ⟨70451, by rfl⟩ : syracuseStep 1502965 = 140903) (by norm_num)
theorem B1781501 : Blo 1186410 1781501 := bbase (se 3 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 1781501 = 668063) (by norm_num)
theorem B1781525 : Blo 1186410 1781525 := bbase (se 6 (by rfl) ⟨41754, by rfl⟩ : syracuseStep 1781525 = 83509) (by norm_num)
theorem B15224597 : Blo 1186410 15224597 := bbase (se 6 (by rfl) ⟨356826, by rfl⟩ : syracuseStep 15224597 = 713653) (by norm_num)
theorem B1781549 : Blo 1186410 1781549 := bbase (se 3 (by rfl) ⟨334040, by rfl⟩ : syracuseStep 1781549 = 668081) (by norm_num)
theorem B2535229 : Blo 1186410 2535229 := bbase (se 3 (by rfl) ⟨475355, by rfl⟩ : syracuseStep 2535229 = 950711) (by norm_num)
theorem B1781573 : Blo 1186410 1781573 := bbase (se 4 (by rfl) ⟨167022, by rfl⟩ : syracuseStep 1781573 = 334045) (by norm_num)
theorem B2002765 : Blo 1186410 2002765 := bbase (se 3 (by rfl) ⟨375518, by rfl⟩ : syracuseStep 2002765 = 751037) (by norm_num)
theorem B1781597 : Blo 1186410 1781597 := bbase (se 3 (by rfl) ⟨334049, by rfl⟩ : syracuseStep 1781597 = 668099) (by norm_num)
theorem B1781621 : Blo 1186410 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B1781645 : Blo 1186410 1781645 := bbase (se 3 (by rfl) ⟨334058, by rfl⟩ : syracuseStep 1781645 = 668117) (by norm_num)
theorem B3207061 : Blo 1186410 3207061 := bbase (se 6 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 3207061 = 150331) (by norm_num)
theorem B1806229 : Blo 1186410 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B4009877 : Blo 1186410 4009877 := bbase (se 6 (by rfl) ⟨93981, by rfl⟩ : syracuseStep 4009877 = 187963) (by norm_num)
theorem B1503137 : Blo 1186410 1503137 := bbase (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) (by norm_num)
theorem B2002853 : Blo 1186410 2002853 := bbase (se 4 (by rfl) ⟨187767, by rfl⟩ : syracuseStep 2002853 = 375535) (by norm_num)
theorem B6008741 : Blo 1186410 6008741 := bbase (se 4 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 6008741 = 1126639) (by norm_num)
theorem B1781669 : Blo 1186410 1781669 := bbase (se 4 (by rfl) ⟨167031, by rfl⟩ : syracuseStep 1781669 = 334063) (by norm_num)
theorem B1781693 : Blo 1186410 1781693 := bbase (se 3 (by rfl) ⟨334067, by rfl⟩ : syracuseStep 1781693 = 668135) (by norm_num)
theorem B1781717 : Blo 1186410 1781717 := bbase (se 7 (by rfl) ⟨20879, by rfl⟩ : syracuseStep 1781717 = 41759) (by norm_num)
theorem B1503193 : Blo 1186410 1503193 := bbase (se 2 (by rfl) ⟨563697, by rfl⟩ : syracuseStep 1503193 = 1127395) (by norm_num)
theorem B1781741 : Blo 1186410 1781741 := bbase (se 3 (by rfl) ⟨334076, by rfl⟩ : syracuseStep 1781741 = 668153) (by norm_num)
theorem B2854901 : Blo 1186410 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B4509701 : Blo 1186410 4509701 := bbase (se 4 (by rfl) ⟨422784, by rfl⟩ : syracuseStep 4509701 = 845569) (by norm_num)
theorem B1781765 : Blo 1186410 1781765 := bbase (se 4 (by rfl) ⟨167040, by rfl⟩ : syracuseStep 1781765 = 334081) (by norm_num)
theorem B1781789 : Blo 1186410 1781789 := bbase (se 3 (by rfl) ⟨334085, by rfl⟩ : syracuseStep 1781789 = 668171) (by norm_num)
theorem B2002981 : Blo 1186410 2002981 := bbase (se 4 (by rfl) ⟨187779, by rfl⟩ : syracuseStep 2002981 = 375559) (by norm_num)
theorem B5705765 : Blo 1186410 5705765 := bbase (se 4 (by rfl) ⟨534915, by rfl⟩ : syracuseStep 5705765 = 1069831) (by norm_num)
theorem B1781813 : Blo 1186410 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B1503289 : Blo 1186410 1503289 := bbase (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) (by norm_num)
theorem B1781837 : Blo 1186410 1781837 := bbase (se 3 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 1781837 = 668189) (by norm_num)
theorem B1781861 : Blo 1186410 1781861 := bbase (se 4 (by rfl) ⟨167049, by rfl⟩ : syracuseStep 1781861 = 334099) (by norm_num)
theorem B2003069 : Blo 1186410 2003069 := bbase (se 3 (by rfl) ⟨375575, by rfl⟩ : syracuseStep 2003069 = 751151) (by norm_num)
theorem B1781885 : Blo 1186410 1781885 := bbase (se 3 (by rfl) ⟨334103, by rfl⟩ : syracuseStep 1781885 = 668207) (by norm_num)
theorem B1781909 : Blo 1186410 1781909 := bbase (se 6 (by rfl) ⟨41763, by rfl⟩ : syracuseStep 1781909 = 83527) (by norm_num)
theorem B1781933 : Blo 1186410 1781933 := bbase (se 3 (by rfl) ⟨334112, by rfl⟩ : syracuseStep 1781933 = 668225) (by norm_num)
theorem B1781957 : Blo 1186410 1781957 := bbase (se 4 (by rfl) ⟨167058, by rfl⟩ : syracuseStep 1781957 = 334117) (by norm_num)
theorem B1781981 : Blo 1186410 1781981 := bbase (se 3 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 1781981 = 668243) (by norm_num)
theorem B1503461 : Blo 1186410 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B1782005 : Blo 1186410 1782005 := bbase (se 5 (by rfl) ⟨83531, by rfl⟩ : syracuseStep 1782005 = 167063) (by norm_num)
theorem B2003197 : Blo 1186410 2003197 := bbase (se 3 (by rfl) ⟨375599, by rfl⟩ : syracuseStep 2003197 = 751199) (by norm_num)
theorem B1782029 : Blo 1186410 1782029 := bbase (se 3 (by rfl) ⟨334130, by rfl⟩ : syracuseStep 1782029 = 668261) (by norm_num)
theorem B2855189 : Blo 1186410 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B1503517 : Blo 1186410 1503517 := bbase (se 3 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 1503517 = 563819) (by norm_num)
theorem B4509989 : Blo 1186410 4509989 := bbase (se 4 (by rfl) ⟨422811, by rfl⟩ : syracuseStep 4509989 = 845623) (by norm_num)
theorem B1782053 : Blo 1186410 1782053 := bbase (se 4 (by rfl) ⟨167067, by rfl⟩ : syracuseStep 1782053 = 334135) (by norm_num)
theorem B1691941 : Blo 1186410 1691941 := bbase (se 4 (by rfl) ⟨158619, by rfl⟩ : syracuseStep 1691941 = 317239) (by norm_num)
theorem B2535725 : Blo 1186410 2535725 := bbase (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) (by norm_num)
theorem B1782077 : Blo 1186410 1782077 := bbase (se 3 (by rfl) ⟨334139, by rfl⟩ : syracuseStep 1782077 = 668279) (by norm_num)
theorem B4010309 : Blo 1186410 4010309 := bbase (se 4 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 4010309 = 751933) (by norm_num)
theorem B2003285 : Blo 1186410 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B1782101 : Blo 1186410 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B1782125 : Blo 1186410 1782125 := bbase (se 3 (by rfl) ⟨334148, by rfl⟩ : syracuseStep 1782125 = 668297) (by norm_num)
theorem B1503613 : Blo 1186410 1503613 := bbase (se 3 (by rfl) ⟨281927, by rfl⟩ : syracuseStep 1503613 = 563855) (by norm_num)
theorem B1782149 : Blo 1186410 1782149 := bbase (se 4 (by rfl) ⟨167076, by rfl⟩ : syracuseStep 1782149 = 334153) (by norm_num)
theorem B1782173 : Blo 1186410 1782173 := bbase (se 3 (by rfl) ⟨334157, by rfl⟩ : syracuseStep 1782173 = 668315) (by norm_num)
theorem B1782197 : Blo 1186410 1782197 := bbase (se 5 (by rfl) ⟨83540, by rfl⟩ : syracuseStep 1782197 = 167081) (by norm_num)
theorem B1782221 : Blo 1186410 1782221 := bbase (se 3 (by rfl) ⟨334166, by rfl⟩ : syracuseStep 1782221 = 668333) (by norm_num)
theorem B2003413 : Blo 1186410 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B1782245 : Blo 1186410 1782245 := bbase (se 4 (by rfl) ⟨167085, by rfl⟩ : syracuseStep 1782245 = 334171) (by norm_num)
theorem B1782269 : Blo 1186410 1782269 := bbase (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) (by norm_num)
theorem B1782293 : Blo 1186410 1782293 := bbase (se 6 (by rfl) ⟨41772, by rfl⟩ : syracuseStep 1782293 = 83545) (by norm_num)
theorem B1503785 : Blo 1186410 1503785 := bbase (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) (by norm_num)
theorem B2003501 : Blo 1186410 2003501 := bbase (se 3 (by rfl) ⟨375656, by rfl⟩ : syracuseStep 2003501 = 751313) (by norm_num)
theorem B1782317 : Blo 1186410 1782317 := bbase (se 3 (by rfl) ⟨334184, by rfl⟩ : syracuseStep 1782317 = 668369) (by norm_num)
theorem B3379781 : Blo 1186410 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B1782341 : Blo 1186410 1782341 := bbase (se 4 (by rfl) ⟨167094, by rfl⟩ : syracuseStep 1782341 = 334189) (by norm_num)
theorem B1782365 : Blo 1186410 1782365 := bbase (se 3 (by rfl) ⟨334193, by rfl⟩ : syracuseStep 1782365 = 668387) (by norm_num)
theorem B1503841 : Blo 1186410 1503841 := bbase (se 2 (by rfl) ⟨563940, by rfl⟩ : syracuseStep 1503841 = 1127881) (by norm_num)
theorem B1782389 : Blo 1186410 1782389 := bbase (se 5 (by rfl) ⟨83549, by rfl⟩ : syracuseStep 1782389 = 167099) (by norm_num)
theorem B1782413 : Blo 1186410 1782413 := bbase (se 3 (by rfl) ⟨334202, by rfl⟩ : syracuseStep 1782413 = 668405) (by norm_num)
theorem B5419669 : Blo 1186410 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B1782437 : Blo 1186410 1782437 := bbase (se 4 (by rfl) ⟨167103, by rfl⟩ : syracuseStep 1782437 = 334207) (by norm_num)
theorem B2003629 : Blo 1186410 2003629 := bbase (se 3 (by rfl) ⟨375680, by rfl⟩ : syracuseStep 2003629 = 751361) (by norm_num)
theorem B1782461 : Blo 1186410 1782461 := bbase (se 3 (by rfl) ⟨334211, by rfl⟩ : syracuseStep 1782461 = 668423) (by norm_num)
theorem B1503937 : Blo 1186410 1503937 := bbase (se 2 (by rfl) ⟨563976, by rfl⟩ : syracuseStep 1503937 = 1127953) (by norm_num)
theorem B1782485 : Blo 1186410 1782485 := bbase (se 7 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 1782485 = 41777) (by norm_num)
theorem B1782509 : Blo 1186410 1782509 := bbase (se 3 (by rfl) ⟨334220, by rfl⟩ : syracuseStep 1782509 = 668441) (by norm_num)
theorem B4010741 : Blo 1186410 4010741 := bbase (se 5 (by rfl) ⟨188003, by rfl⟩ : syracuseStep 4010741 = 376007) (by norm_num)
theorem B2003717 : Blo 1186410 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B1782533 : Blo 1186410 1782533 := bbase (se 4 (by rfl) ⟨167112, by rfl⟩ : syracuseStep 1782533 = 334225) (by norm_num)
theorem B1782557 : Blo 1186410 1782557 := bbase (se 3 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 1782557 = 668459) (by norm_num)
theorem B5706533 : Blo 1186410 5706533 := bbase (se 4 (by rfl) ⟨534987, by rfl⟩ : syracuseStep 5706533 = 1069975) (by norm_num)
theorem B1782581 : Blo 1186410 1782581 := bbase (se 5 (by rfl) ⟨83558, by rfl⟩ : syracuseStep 1782581 = 167117) (by norm_num)
theorem B1782605 : Blo 1186410 1782605 := bbase (se 3 (by rfl) ⟨334238, by rfl⟩ : syracuseStep 1782605 = 668477) (by norm_num)
theorem B5411717 : Blo 1186410 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B2003845 : Blo 1186410 2003845 := bbase (se 4 (by rfl) ⟨187860, by rfl⟩ : syracuseStep 2003845 = 375721) (by norm_num)
theorem B3003277 : Blo 1186410 3003277 := bbase (se 3 (by rfl) ⟨563114, by rfl⟩ : syracuseStep 3003277 = 1126229) (by norm_num)
theorem B6853589 : Blo 1186410 6853589 := bbase (se 7 (by rfl) ⟨80315, by rfl⟩ : syracuseStep 6853589 = 160631) (by norm_num)
theorem B2003933 : Blo 1186410 2003933 := bbase (se 3 (by rfl) ⟨375737, by rfl⟩ : syracuseStep 2003933 = 751475) (by norm_num)
theorem B1446889 : Blo 1186410 1446889 := bbase (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) (by norm_num)
theorem B3003389 : Blo 1186410 3003389 := bbase (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) (by norm_num)
theorem B2004061 : Blo 1186410 2004061 := bbase (se 3 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 2004061 = 751523) (by norm_num)
theorem B2536613 : Blo 1186410 2536613 := bbase (se 4 (by rfl) ⟨237807, by rfl⟩ : syracuseStep 2536613 = 475615) (by norm_num)
theorem B6010037 : Blo 1186410 6010037 := bbase (se 5 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 6010037 = 563441) (by norm_num)
theorem B2004149 : Blo 1186410 2004149 := bbase (se 5 (by rfl) ⟨93944, by rfl⟩ : syracuseStep 2004149 = 187889) (by norm_num)
theorem B3003581 : Blo 1186410 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B3855637 : Blo 1186410 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B2536733 : Blo 1186410 2536733 := bbase (se 3 (by rfl) ⟨475637, by rfl⟩ : syracuseStep 2536733 = 951275) (by norm_num)
theorem B2004277 : Blo 1186410 2004277 := bbase (se 5 (by rfl) ⟨93950, by rfl⟩ : syracuseStep 2004277 = 187901) (by norm_num)
theorem B2004365 : Blo 1186410 2004365 := bbase (se 3 (by rfl) ⟨375818, by rfl⟩ : syracuseStep 2004365 = 751637) (by norm_num)
theorem B9016757 : Blo 1186410 9016757 := bbase (se 5 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 9016757 = 845321) (by norm_num)
theorem B4511173 : Blo 1186410 4511173 := bbase (se 4 (by rfl) ⟨422922, by rfl⟩ : syracuseStep 4511173 = 845845) (by norm_num)
theorem B2569733 : Blo 1186410 2569733 := bbase (se 4 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 2569733 = 481825) (by norm_num)
theorem B1267213 : Blo 1186410 1267213 := bbase (se 3 (by rfl) ⟨237602, by rfl⟩ : syracuseStep 1267213 = 475205) (by norm_num)
theorem B2004493 : Blo 1186410 2004493 := bbase (se 3 (by rfl) ⟨375842, by rfl⟩ : syracuseStep 2004493 = 751685) (by norm_num)
theorem B3003925 : Blo 1186410 3003925 := bbase (se 6 (by rfl) ⟨70404, by rfl⟩ : syracuseStep 3003925 = 140809) (by norm_num)
theorem B1267273 : Blo 1186410 1267273 := bbase (se 2 (by rfl) ⟨475227, by rfl⟩ : syracuseStep 1267273 = 950455) (by norm_num)
theorem B2004581 : Blo 1186410 2004581 := bbase (se 4 (by rfl) ⟨187929, by rfl⟩ : syracuseStep 2004581 = 375859) (by norm_num)
theorem B3004037 : Blo 1186410 3004037 := bbase (se 4 (by rfl) ⟨281628, by rfl⟩ : syracuseStep 3004037 = 563257) (by norm_num)
theorem B21649045 : Blo 1186410 21649045 := bbase (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) (by norm_num)
theorem B2004709 : Blo 1186410 2004709 := bbase (se 4 (by rfl) ⟨187941, by rfl⟩ : syracuseStep 2004709 = 375883) (by norm_num)
theorem B4511477 : Blo 1186410 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B12515093 : Blo 1186410 12515093 := bbase (se 6 (by rfl) ⟨293322, by rfl⟩ : syracuseStep 12515093 = 586645) (by norm_num)
theorem B2004797 : Blo 1186410 2004797 := bbase (se 3 (by rfl) ⟨375899, by rfl⟩ : syracuseStep 2004797 = 751799) (by norm_num)
theorem B3004229 : Blo 1186410 3004229 := bbase (se 4 (by rfl) ⟨281646, by rfl⟩ : syracuseStep 3004229 = 563293) (by norm_num)
theorem B4061029 : Blo 1186410 4061029 := bbase (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) (by norm_num)
theorem B1267589 : Blo 1186410 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B2709397 : Blo 1186410 2709397 := bbase (se 6 (by rfl) ⟨63501, by rfl⟩ : syracuseStep 2709397 = 127003) (by norm_num)
theorem B2537365 : Blo 1186410 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B2004925 : Blo 1186410 2004925 := bbase (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) (by norm_num)
theorem B2406341 : Blo 1186410 2406341 := bbase (se 4 (by rfl) ⟨225594, by rfl⟩ : syracuseStep 2406341 = 451189) (by norm_num)
theorem B2709469 : Blo 1186410 2709469 := bbase (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) (by norm_num)
theorem B6510581 : Blo 1186410 6510581 := bbase (se 5 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 6510581 = 610367) (by norm_num)
theorem B2005013 : Blo 1186410 2005013 := bbase (se 6 (by rfl) ⟨46992, by rfl⟩ : syracuseStep 2005013 = 93985) (by norm_num)
theorem B3381365 : Blo 1186410 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B2005141 : Blo 1186410 2005141 := bbase (se 6 (by rfl) ⟨46995, by rfl⟩ : syracuseStep 2005141 = 93991) (by norm_num)
theorem B3004573 : Blo 1186410 3004573 := bbase (se 3 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 3004573 = 1126715) (by norm_num)
theorem B2316493 : Blo 1186410 2316493 := bbase (se 3 (by rfl) ⟨434342, by rfl⟩ : syracuseStep 2316493 = 868685) (by norm_num)
theorem B2005229 : Blo 1186410 2005229 := bbase (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) (by norm_num)
theorem B3004685 : Blo 1186410 3004685 := bbase (se 3 (by rfl) ⟨563378, by rfl⟩ : syracuseStep 3004685 = 1126757) (by norm_num)
theorem B1268033 : Blo 1186410 1268033 := bbase (se 2 (by rfl) ⟨475512, by rfl⟩ : syracuseStep 1268033 = 951025) (by norm_num)
theorem B2005357 : Blo 1186410 2005357 := bbase (se 3 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 2005357 = 752009) (by norm_num)
theorem B1268093 : Blo 1186410 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B4004261 : Blo 1186410 4004261 := bbase (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) (by norm_num)
theorem B1522117 : Blo 1186410 1522117 := bbase (se 4 (by rfl) ⟨142698, by rfl⟩ : syracuseStep 1522117 = 285397) (by norm_num)
theorem B6011333 : Blo 1186410 6011333 := bbase (se 4 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 6011333 = 1127125) (by norm_num)
theorem B3004877 : Blo 1186410 3004877 := bbase (se 3 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 3004877 = 1126829) (by norm_num)
theorem B2169317 : Blo 1186410 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B1268221 : Blo 1186410 1268221 := bbase (se 3 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 1268221 = 475583) (by norm_num)
theorem B2570773 : Blo 1186410 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B1522229 : Blo 1186410 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B2030269 : Blo 1186410 2030269 := bbase (se 3 (by rfl) ⟨380675, by rfl⟩ : syracuseStep 2030269 = 761351) (by norm_num)
theorem B3382037 : Blo 1186410 3382037 := bbase (se 6 (by rfl) ⟨79266, by rfl⟩ : syracuseStep 3382037 = 158533) (by norm_num)
theorem B3005221 : Blo 1186410 3005221 := bbase (se 4 (by rfl) ⟨281739, by rfl⟩ : syracuseStep 3005221 = 563479) (by norm_num)
theorem B4004693 : Blo 1186410 4004693 := bbase (se 9 (by rfl) ⟨11732, by rfl⟩ : syracuseStep 4004693 = 23465) (by norm_num)
theorem B7322453 : Blo 1186410 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B2669453 : Blo 1186410 2669453 := bbase (se 3 (by rfl) ⟨500522, by rfl⟩ : syracuseStep 2669453 = 1001045) (by norm_num)
theorem B3005333 : Blo 1186410 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B3611557 : Blo 1186410 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B1268665 : Blo 1186410 1268665 := bbase (se 2 (by rfl) ⟨475749, by rfl⟩ : syracuseStep 1268665 = 951499) (by norm_num)
theorem B3046349 : Blo 1186410 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B2669525 : Blo 1186410 2669525 := bbase (se 7 (by rfl) ⟨31283, by rfl⟩ : syracuseStep 2669525 = 62567) (by norm_num)
theorem B2169821 : Blo 1186410 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B2669597 : Blo 1186410 2669597 := bbase (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) (by norm_num)
theorem B5069861 : Blo 1186410 5069861 := bbase (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) (by norm_num)
theorem B1268785 : Blo 1186410 1268785 := bbase (se 2 (by rfl) ⟨475794, by rfl⟩ : syracuseStep 1268785 = 951589) (by norm_num)
theorem B1203265 : Blo 1186410 1203265 := bbase (se 2 (by rfl) ⟨451224, by rfl⟩ : syracuseStep 1203265 = 902449) (by norm_num)
theorem B3005525 : Blo 1186410 3005525 := bbase (se 8 (by rfl) ⟨17610, by rfl⟩ : syracuseStep 3005525 = 35221) (by norm_num)
theorem B2669669 : Blo 1186410 2669669 := bbase (se 4 (by rfl) ⟨250281, by rfl⟩ : syracuseStep 2669669 = 500563) (by norm_num)
theorem B15203477 : Blo 1186410 15203477 := bbase (se 6 (by rfl) ⟨356331, by rfl⟩ : syracuseStep 15203477 = 712663) (by norm_num)
theorem B2669741 : Blo 1186410 2669741 := bbase (se 3 (by rfl) ⟨500576, by rfl⟩ : syracuseStep 2669741 = 1001153) (by norm_num)
theorem B2030789 : Blo 1186410 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B3382469 : Blo 1186410 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B2669813 : Blo 1186410 2669813 := bbase (se 5 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 2669813 = 250295) (by norm_num)
theorem B4005125 : Blo 1186410 4005125 := bbase (se 4 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 4005125 = 750961) (by norm_num)
theorem B1269037 : Blo 1186410 1269037 := bbase (se 3 (by rfl) ⟨237944, by rfl⟩ : syracuseStep 1269037 = 475889) (by norm_num)
theorem B1269041 : Blo 1186410 1269041 := bbase (se 2 (by rfl) ⟨475890, by rfl⟩ : syracuseStep 1269041 = 951781) (by norm_num)
theorem B2669885 : Blo 1186410 2669885 := bbase (se 3 (by rfl) ⟨500603, by rfl⟩ : syracuseStep 2669885 = 1001207) (by norm_num)
theorem B2571605 : Blo 1186410 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B2669957 : Blo 1186410 2669957 := bbase (se 4 (by rfl) ⟨250308, by rfl⟩ : syracuseStep 2669957 = 500617) (by norm_num)
theorem B2170253 : Blo 1186410 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B3005869 : Blo 1186410 3005869 := bbase (se 3 (by rfl) ⟨563600, by rfl⟩ : syracuseStep 3005869 = 1127201) (by norm_num)
theorem B1334713 : Blo 1186410 1334713 := bbase (se 2 (by rfl) ⟨500517, by rfl⟩ : syracuseStep 1334713 = 1001035) (by norm_num)
theorem B2670029 : Blo 1186410 2670029 := bbase (se 3 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 2670029 = 1001261) (by norm_num)
theorem B3087829 : Blo 1186410 3087829 := bbase (se 7 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 3087829 = 72371) (by norm_num)
theorem B1334749 : Blo 1186410 1334749 := bbase (se 3 (by rfl) ⟨250265, by rfl⟩ : syracuseStep 1334749 = 500531) (by norm_num)
theorem B1334785 : Blo 1186410 1334785 := bbase (se 2 (by rfl) ⟨500544, by rfl⟩ : syracuseStep 1334785 = 1001089) (by norm_num)
theorem B2670101 : Blo 1186410 2670101 := bbase (se 6 (by rfl) ⟨62580, by rfl⟩ : syracuseStep 2670101 = 125161) (by norm_num)
theorem B3005981 : Blo 1186410 3005981 := bbase (se 3 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 3005981 = 1127243) (by norm_num)
theorem B1334821 : Blo 1186410 1334821 := bbase (se 4 (by rfl) ⟨125139, by rfl⟩ : syracuseStep 1334821 = 250279) (by norm_num)
theorem B1334857 : Blo 1186410 1334857 := bbase (se 2 (by rfl) ⟨500571, by rfl⟩ : syracuseStep 1334857 = 1001143) (by norm_num)
theorem B2670173 : Blo 1186410 2670173 := bbase (se 3 (by rfl) ⟨500657, by rfl⟩ : syracuseStep 2670173 = 1001315) (by norm_num)
theorem B1334893 : Blo 1186410 1334893 := bbase (se 3 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 1334893 = 500585) (by norm_num)
theorem B1334929 : Blo 1186410 1334929 := bbase (se 2 (by rfl) ⟨500598, by rfl⟩ : syracuseStep 1334929 = 1001197) (by norm_num)
theorem B2670245 : Blo 1186410 2670245 := bbase (se 4 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 2670245 = 500671) (by norm_num)
theorem B1203881 : Blo 1186410 1203881 := bbase (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) (by norm_num)
theorem B1334965 : Blo 1186410 1334965 := bbase (se 5 (by rfl) ⟨62576, by rfl⟩ : syracuseStep 1334965 = 125153) (by norm_num)
theorem B4005557 : Blo 1186410 4005557 := bbase (se 5 (by rfl) ⟨187760, by rfl⟩ : syracuseStep 4005557 = 375521) (by norm_num)
theorem B6012629 : Blo 1186410 6012629 := bbase (se 7 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 6012629 = 140921) (by norm_num)
theorem B3210965 : Blo 1186410 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B1335001 : Blo 1186410 1335001 := bbase (se 2 (by rfl) ⟨500625, by rfl⟩ : syracuseStep 1335001 = 1001251) (by norm_num)
theorem B3006173 : Blo 1186410 3006173 := bbase (se 3 (by rfl) ⟨563657, by rfl⟩ : syracuseStep 3006173 = 1127315) (by norm_num)
theorem B2670317 : Blo 1186410 2670317 := bbase (se 3 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 2670317 = 1001369) (by norm_num)
theorem B1335037 : Blo 1186410 1335037 := bbase (se 3 (by rfl) ⟨250319, by rfl⟩ : syracuseStep 1335037 = 500639) (by norm_num)
theorem B2252549 : Blo 1186410 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B1335073 : Blo 1186410 1335073 := bbase (se 2 (by rfl) ⟨500652, by rfl⟩ : syracuseStep 1335073 = 1001305) (by norm_num)
theorem B2670389 : Blo 1186410 2670389 := bbase (se 5 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 2670389 = 250349) (by norm_num)
theorem B1335109 : Blo 1186410 1335109 := bbase (se 4 (by rfl) ⟨125166, by rfl⟩ : syracuseStep 1335109 = 250333) (by norm_num)
theorem B3211093 : Blo 1186410 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1335145 : Blo 1186410 1335145 := bbase (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) (by norm_num)
theorem B2670461 : Blo 1186410 2670461 := bbase (se 3 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 2670461 = 1001423) (by norm_num)
theorem B1335181 : Blo 1186410 1335181 := bbase (se 3 (by rfl) ⟨250346, by rfl⟩ : syracuseStep 1335181 = 500693) (by norm_num)
theorem B2252701 : Blo 1186410 2252701 := bbase (se 3 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 2252701 = 844763) (by norm_num)
theorem B1335217 : Blo 1186410 1335217 := bbase (se 2 (by rfl) ⟨500706, by rfl⟩ : syracuseStep 1335217 = 1001413) (by norm_num)
theorem B3383221 : Blo 1186410 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B2670533 : Blo 1186410 2670533 := bbase (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) (by norm_num)
theorem B1335253 : Blo 1186410 1335253 := bbase (se 7 (by rfl) ⟨15647, by rfl⟩ : syracuseStep 1335253 = 31295) (by norm_num)
theorem B20299733 : Blo 1186410 20299733 := bbase (se 7 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 20299733 = 475775) (by norm_num)
theorem B1523677 : Blo 1186410 1523677 := bbase (se 3 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 1523677 = 571379) (by norm_num)
theorem B3006467 : Blo 1186410 3006467 := bstep (se 1 (by rfl) ⟨2254850, by rfl⟩ : syracuseStep 3006467 = 4509701) B4509701
theorem B1187843 : Blo 1186410 1187843 := bstep (se 1 (by rfl) ⟨890882, by rfl⟩ : syracuseStep 1187843 = 1781765) B1781765
theorem B1187859 : Blo 1186410 1187859 := bstep (se 1 (by rfl) ⟨890894, by rfl⟩ : syracuseStep 1187859 = 1781789) B1781789
theorem B1187875 : Blo 1186410 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B2670641 : Blo 1186410 2670641 := bstep (se 2 (by rfl) ⟨1001490, by rfl⟩ : syracuseStep 2670641 = 2002981) B2002981
theorem B1187891 : Blo 1186410 1187891 := bstep (se 1 (by rfl) ⟨890918, by rfl⟩ : syracuseStep 1187891 = 1781837) B1781837
theorem B2670659 : Blo 1186410 2670659 := bstep (se 1 (by rfl) ⟨2002994, by rfl⟩ : syracuseStep 2670659 = 4005989) B4005989
theorem B1187907 : Blo 1186410 1187907 := bstep (se 1 (by rfl) ⟨890930, by rfl⟩ : syracuseStep 1187907 = 1781861) B1781861
theorem B1335379 : Blo 1186410 1335379 := bstep (se 1 (by rfl) ⟨1001534, by rfl⟩ : syracuseStep 1335379 = 2003069) B2003069
theorem B1187923 : Blo 1186410 1187923 := bstep (se 1 (by rfl) ⟨890942, by rfl⟩ : syracuseStep 1187923 = 1781885) B1781885
theorem B1187939 : Blo 1186410 1187939 := bstep (se 1 (by rfl) ⟨890954, by rfl⟩ : syracuseStep 1187939 = 1781909) B1781909
theorem B1187955 : Blo 1186410 1187955 := bstep (se 1 (by rfl) ⟨890966, by rfl⟩ : syracuseStep 1187955 = 1781933) B1781933
theorem B1187971 : Blo 1186410 1187971 := bstep (se 1 (by rfl) ⟨890978, by rfl⟩ : syracuseStep 1187971 = 1781957) B1781957
theorem B1187987 : Blo 1186410 1187987 := bstep (se 1 (by rfl) ⟨890990, by rfl⟩ : syracuseStep 1187987 = 1781981) B1781981
theorem B1188003 : Blo 1186410 1188003 := bstep (se 1 (by rfl) ⟨891002, by rfl⟩ : syracuseStep 1188003 = 1782005) B1782005
theorem B1188019 : Blo 1186410 1188019 := bstep (se 1 (by rfl) ⟨891014, by rfl⟩ : syracuseStep 1188019 = 1782029) B1782029
theorem B3006659 : Blo 1186410 3006659 := bstep (se 1 (by rfl) ⟨2254994, by rfl⟩ : syracuseStep 3006659 = 4509989) B4509989
theorem B1188035 : Blo 1186410 1188035 := bstep (se 1 (by rfl) ⟨891026, by rfl⟩ : syracuseStep 1188035 = 1782053) B1782053
theorem B4006097 : Blo 1186410 4006097 := bstep (se 2 (by rfl) ⟨1502286, by rfl⟩ : syracuseStep 4006097 = 3004573) B3004573
theorem B1188051 : Blo 1186410 1188051 := bstep (se 1 (by rfl) ⟨891038, by rfl⟩ : syracuseStep 1188051 = 1782077) B1782077
theorem B4505827 : Blo 1186410 4505827 := bstep (se 1 (by rfl) ⟨3379370, by rfl⟩ : syracuseStep 4505827 = 6758741) B6758741
theorem B1335523 : Blo 1186410 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B1188067 : Blo 1186410 1188067 := bstep (se 1 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 1188067 = 1782101) B1782101
theorem B1188083 : Blo 1186410 1188083 := bstep (se 1 (by rfl) ⟨891062, by rfl⟩ : syracuseStep 1188083 = 1782125) B1782125
theorem B1188099 : Blo 1186410 1188099 := bstep (se 1 (by rfl) ⟨891074, by rfl⟩ : syracuseStep 1188099 = 1782149) B1782149
theorem B1188115 : Blo 1186410 1188115 := bstep (se 1 (by rfl) ⟨891086, by rfl⟩ : syracuseStep 1188115 = 1782173) B1782173
theorem B1188131 : Blo 1186410 1188131 := bstep (se 1 (by rfl) ⟨891098, by rfl⟩ : syracuseStep 1188131 = 1782197) B1782197
theorem B1188147 : Blo 1186410 1188147 := bstep (se 1 (by rfl) ⟨891110, by rfl⟩ : syracuseStep 1188147 = 1782221) B1782221
theorem B1188163 : Blo 1186410 1188163 := bstep (se 1 (by rfl) ⟨891122, by rfl⟩ : syracuseStep 1188163 = 1782245) B1782245
theorem B1605953 : Blo 1186410 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B2670929 : Blo 1186410 2670929 := bstep (se 2 (by rfl) ⟨1001598, by rfl⟩ : syracuseStep 2670929 = 2003197) B2003197
theorem B1188179 : Blo 1186410 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B2670947 : Blo 1186410 2670947 := bstep (se 1 (by rfl) ⟨2003210, by rfl⟩ : syracuseStep 2670947 = 4006421) B4006421
theorem B1188195 : Blo 1186410 1188195 := bstep (se 1 (by rfl) ⟨891146, by rfl⟩ : syracuseStep 1188195 = 1782293) B1782293
theorem B1335667 : Blo 1186410 1335667 := bstep (se 1 (by rfl) ⟨1001750, by rfl⟩ : syracuseStep 1335667 = 2003501) B2003501
theorem B1188211 : Blo 1186410 1188211 := bstep (se 1 (by rfl) ⟨891158, by rfl⟩ : syracuseStep 1188211 = 1782317) B1782317
theorem B2253187 : Blo 1186410 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B1188227 : Blo 1186410 1188227 := bstep (se 1 (by rfl) ⟨891170, by rfl⟩ : syracuseStep 1188227 = 1782341) B1782341
theorem B3801485 : Blo 1186410 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B1188243 : Blo 1186410 1188243 := bstep (se 1 (by rfl) ⟨891182, by rfl⟩ : syracuseStep 1188243 = 1782365) B1782365
theorem B1188259 : Blo 1186410 1188259 := bstep (se 1 (by rfl) ⟨891194, by rfl⟩ : syracuseStep 1188259 = 1782389) B1782389
theorem B2253233 : Blo 1186410 2253233 := bstep (se 2 (by rfl) ⟨844962, by rfl⟩ : syracuseStep 2253233 = 1689925) B1689925
theorem B1188275 : Blo 1186410 1188275 := bstep (se 1 (by rfl) ⟨891206, by rfl⟩ : syracuseStep 1188275 = 1782413) B1782413
theorem B1188291 : Blo 1186410 1188291 := bstep (se 1 (by rfl) ⟨891218, by rfl⟩ : syracuseStep 1188291 = 1782437) B1782437
theorem B1188307 : Blo 1186410 1188307 := bstep (se 1 (by rfl) ⟨891230, by rfl⟩ : syracuseStep 1188307 = 1782461) B1782461
theorem B1188323 : Blo 1186410 1188323 := bstep (se 1 (by rfl) ⟨891242, by rfl⟩ : syracuseStep 1188323 = 1782485) B1782485
theorem B1188339 : Blo 1186410 1188339 := bstep (se 1 (by rfl) ⟨891254, by rfl⟩ : syracuseStep 1188339 = 1782509) B1782509
theorem B1335811 : Blo 1186410 1335811 := bstep (se 1 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 1335811 = 2003717) B2003717
theorem B1188355 : Blo 1186410 1188355 := bstep (se 1 (by rfl) ⟨891266, by rfl⟩ : syracuseStep 1188355 = 1782533) B1782533
theorem B5415437 : Blo 1186410 5415437 := bstep (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) B2030789
theorem B1188371 : Blo 1186410 1188371 := bstep (se 1 (by rfl) ⟨891278, by rfl⟩ : syracuseStep 1188371 = 1782557) B1782557
theorem B1188387 : Blo 1186410 1188387 := bstep (se 1 (by rfl) ⟨891290, by rfl⟩ : syracuseStep 1188387 = 1782581) B1782581
theorem B1188403 : Blo 1186410 1188403 := bstep (se 1 (by rfl) ⟨891302, by rfl⟩ : syracuseStep 1188403 = 1782605) B1782605
theorem B3424835 : Blo 1186410 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B1901153 : Blo 1186410 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B2671217 : Blo 1186410 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B2671235 : Blo 1186410 2671235 := bstep (se 1 (by rfl) ⟨2003426, by rfl⟩ : syracuseStep 2671235 = 4006853) B4006853
theorem B1335955 : Blo 1186410 1335955 := bstep (se 1 (by rfl) ⟨1001966, by rfl⟩ : syracuseStep 1335955 = 2003933) B2003933
theorem B2851537 : Blo 1186410 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B2253521 : Blo 1186410 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B17597155 : Blo 1186410 17597155 := bstep (se 1 (by rfl) ⟨13197866, by rfl⟩ : syracuseStep 17597155 = 26395733) B26395733
theorem B4006637 : Blo 1186410 4006637 := bstep (se 3 (by rfl) ⟨751244, by rfl⟩ : syracuseStep 4006637 = 1502489) B1502489
theorem B4006691 : Blo 1186410 4006691 := bstep (se 1 (by rfl) ⟨3005018, by rfl⟩ : syracuseStep 4006691 = 6010037) B6010037
theorem B1336099 : Blo 1186410 1336099 := bstep (se 1 (by rfl) ⟨1002074, by rfl⟩ : syracuseStep 1336099 = 2004149) B2004149
theorem B3384109 : Blo 1186410 3384109 := bstep (se 3 (by rfl) ⟨634520, by rfl⟩ : syracuseStep 3384109 = 1269041) B1269041
theorem B3212131 : Blo 1186410 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B7226225 : Blo 1186410 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B2671505 : Blo 1186410 2671505 := bstep (se 2 (by rfl) ⟨1001814, by rfl⟩ : syracuseStep 2671505 = 2003629) B2003629
theorem B2671523 : Blo 1186410 2671523 := bstep (se 1 (by rfl) ⟨2003642, by rfl⟩ : syracuseStep 2671523 = 4007285) B4007285
theorem B1336243 : Blo 1186410 1336243 := bstep (se 1 (by rfl) ⟨1002182, by rfl⟩ : syracuseStep 1336243 = 2004365) B2004365
theorem B2032595 : Blo 1186410 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B1713155 : Blo 1186410 1713155 := bstep (se 1 (by rfl) ⟨1284866, by rfl⟩ : syracuseStep 1713155 = 2569733) B2569733
theorem B4006961 : Blo 1186410 4006961 := bstep (se 2 (by rfl) ⟨1502610, by rfl⟩ : syracuseStep 4006961 = 3005221) B3005221
theorem B1336387 : Blo 1186410 1336387 := bstep (se 1 (by rfl) ⟨1002290, by rfl⟩ : syracuseStep 1336387 = 2004581) B2004581
theorem B12354629 : Blo 1186410 12354629 := bstep (se 4 (by rfl) ⟨1158246, by rfl⟩ : syracuseStep 12354629 = 2316493) B2316493
theorem B1901665 : Blo 1186410 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B3007601 : Blo 1186410 3007601 := bstep (se 2 (by rfl) ⟨1127850, by rfl⟩ : syracuseStep 3007601 = 2255701) B2255701
theorem B2032787 : Blo 1186410 2032787 := bstep (se 1 (by rfl) ⟨1524590, by rfl⟩ : syracuseStep 2032787 = 3049181) B3049181
theorem B3007651 : Blo 1186410 3007651 := bstep (se 1 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 3007651 = 4511477) B4511477
theorem B2671793 : Blo 1186410 2671793 := bstep (se 2 (by rfl) ⟨1001922, by rfl⟩ : syracuseStep 2671793 = 2003845) B2003845
theorem B2671811 : Blo 1186410 2671811 := bstep (se 1 (by rfl) ⟨2003858, by rfl⟩ : syracuseStep 2671811 = 4007717) B4007717
theorem B1336531 : Blo 1186410 1336531 := bstep (se 1 (by rfl) ⟨1002398, by rfl⟩ : syracuseStep 1336531 = 2004797) B2004797
theorem B1426691 : Blo 1186410 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B3007793 : Blo 1186410 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B1336675 : Blo 1186410 1336675 := bstep (se 1 (by rfl) ⟨1002506, by rfl⟩ : syracuseStep 1336675 = 2005013) B2005013
theorem B2254243 : Blo 1186410 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B2672081 : Blo 1186410 2672081 := bstep (se 2 (by rfl) ⟨1002030, by rfl⟩ : syracuseStep 2672081 = 2004061) B2004061
theorem B2672099 : Blo 1186410 2672099 := bstep (se 1 (by rfl) ⟨2004074, by rfl⟩ : syracuseStep 2672099 = 4008149) B4008149
theorem B1336819 : Blo 1186410 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B6768197 : Blo 1186410 6768197 := bstep (se 4 (by rfl) ⟨634518, by rfl⟩ : syracuseStep 6768197 = 1269037) B1269037
theorem B7603789 : Blo 1186410 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B4007501 : Blo 1186410 4007501 := bstep (se 3 (by rfl) ⟨751406, by rfl⟩ : syracuseStep 4007501 = 1502813) B1502813
theorem B4007555 : Blo 1186410 4007555 := bstep (se 1 (by rfl) ⟨3005666, by rfl⟩ : syracuseStep 4007555 = 6011333) B6011333
theorem B1902275 : Blo 1186410 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B2672369 : Blo 1186410 2672369 := bstep (se 2 (by rfl) ⟨1002138, by rfl⟩ : syracuseStep 2672369 = 2004277) B2004277
theorem B2672387 : Blo 1186410 2672387 := bstep (se 1 (by rfl) ⟨2004290, by rfl⟩ : syracuseStep 2672387 = 4008581) B4008581
theorem B11405069 : Blo 1186410 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B1804051 : Blo 1186410 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B2254691 : Blo 1186410 2254691 := bstep (se 1 (by rfl) ⟨1691018, by rfl⟩ : syracuseStep 2254691 = 3382037) B3382037
theorem B4007825 : Blo 1186410 4007825 := bstep (se 2 (by rfl) ⟨1502934, by rfl⟩ : syracuseStep 4007825 = 3005869) B3005869
theorem B1779617 : Blo 1186410 1779617 := bstep (se 2 (by rfl) ⟨667356, by rfl⟩ : syracuseStep 1779617 = 1334713) B1334713
theorem B6014897 : Blo 1186410 6014897 := bstep (se 2 (by rfl) ⟨2255586, by rfl⟩ : syracuseStep 6014897 = 4511173) B4511173
theorem B1779635 : Blo 1186410 1779635 := bstep (se 1 (by rfl) ⟨1334726, by rfl⟩ : syracuseStep 1779635 = 2669453) B2669453
theorem B3803075 : Blo 1186410 3803075 := bstep (se 1 (by rfl) ⟨2852306, by rfl⟩ : syracuseStep 3803075 = 5704613) B5704613
theorem B1779665 : Blo 1186410 1779665 := bstep (se 2 (by rfl) ⟨667374, by rfl⟩ : syracuseStep 1779665 = 1334749) B1334749
theorem B1779683 : Blo 1186410 1779683 := bstep (se 1 (by rfl) ⟨1334762, by rfl⟩ : syracuseStep 1779683 = 2669525) B2669525
theorem B1779713 : Blo 1186410 1779713 := bstep (se 2 (by rfl) ⟨667392, by rfl⟩ : syracuseStep 1779713 = 1334785) B1334785
theorem B6006797 : Blo 1186410 6006797 := bstep (se 3 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 6006797 = 2252549) B2252549
theorem B1689617 : Blo 1186410 1689617 := bstep (se 2 (by rfl) ⟨633606, by rfl⟩ : syracuseStep 1689617 = 1267213) B1267213
theorem B2672657 : Blo 1186410 2672657 := bstep (se 2 (by rfl) ⟨1002246, by rfl⟩ : syracuseStep 2672657 = 2004493) B2004493
theorem B1779731 : Blo 1186410 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B2672675 : Blo 1186410 2672675 := bstep (se 1 (by rfl) ⟨2004506, by rfl⟩ : syracuseStep 2672675 = 4009013) B4009013
theorem B1779761 : Blo 1186410 1779761 := bstep (se 2 (by rfl) ⟨667410, by rfl⟩ : syracuseStep 1779761 = 1334821) B1334821
theorem B4065329 : Blo 1186410 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B15206453 : Blo 1186410 15206453 := bstep (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) B1425605
theorem B1779779 : Blo 1186410 1779779 := bstep (se 1 (by rfl) ⟨1334834, by rfl⟩ : syracuseStep 1779779 = 2669669) B2669669
theorem B1779809 : Blo 1186410 1779809 := bstep (se 2 (by rfl) ⟨667428, by rfl⟩ : syracuseStep 1779809 = 1334857) B1334857
theorem B1689697 : Blo 1186410 1689697 := bstep (se 2 (by rfl) ⟨633636, by rfl⟩ : syracuseStep 1689697 = 1267273) B1267273
theorem B10135651 : Blo 1186410 10135651 := bstep (se 1 (by rfl) ⟨7601738, by rfl⟩ : syracuseStep 10135651 = 15203477) B15203477
theorem B1779827 : Blo 1186410 1779827 := bstep (se 1 (by rfl) ⟨1334870, by rfl⟩ : syracuseStep 1779827 = 2669741) B2669741
theorem B2254979 : Blo 1186410 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B1779857 : Blo 1186410 1779857 := bstep (se 2 (by rfl) ⟨667446, by rfl⟩ : syracuseStep 1779857 = 1334893) B1334893
theorem B1779875 : Blo 1186410 1779875 := bstep (se 1 (by rfl) ⟨1334906, by rfl⟩ : syracuseStep 1779875 = 2669813) B2669813
theorem B1804465 : Blo 1186410 1804465 := bstep (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) B1353349
theorem B1779905 : Blo 1186410 1779905 := bstep (se 2 (by rfl) ⟨667464, by rfl⟩ : syracuseStep 1779905 = 1334929) B1334929
theorem B1779923 : Blo 1186410 1779923 := bstep (se 1 (by rfl) ⟨1334942, by rfl⟩ : syracuseStep 1779923 = 2669885) B2669885
theorem B1714403 : Blo 1186410 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1779953 : Blo 1186410 1779953 := bstep (se 2 (by rfl) ⟨667482, by rfl⟩ : syracuseStep 1779953 = 1334965) B1334965
theorem B1779971 : Blo 1186410 1779971 := bstep (se 1 (by rfl) ⟨1334978, by rfl⟩ : syracuseStep 1779971 = 2669957) B2669957
theorem B1780001 : Blo 1186410 1780001 := bstep (se 2 (by rfl) ⟨667500, by rfl⟩ : syracuseStep 1780001 = 1335001) B1335001
theorem B2672945 : Blo 1186410 2672945 := bstep (se 2 (by rfl) ⟨1002354, by rfl⟩ : syracuseStep 2672945 = 2004709) B2004709
theorem B1780019 : Blo 1186410 1780019 := bstep (se 1 (by rfl) ⟨1335014, by rfl⟩ : syracuseStep 1780019 = 2670029) B2670029
theorem B2672963 : Blo 1186410 2672963 := bstep (se 1 (by rfl) ⟨2004722, by rfl⟩ : syracuseStep 2672963 = 4009445) B4009445
theorem B1780049 : Blo 1186410 1780049 := bstep (se 2 (by rfl) ⟨667518, by rfl⟩ : syracuseStep 1780049 = 1335037) B1335037
theorem B1780067 : Blo 1186410 1780067 := bstep (se 1 (by rfl) ⟨1335050, by rfl⟩ : syracuseStep 1780067 = 2670101) B2670101
theorem B1780097 : Blo 1186410 1780097 := bstep (se 2 (by rfl) ⟨667536, by rfl⟩ : syracuseStep 1780097 = 1335073) B1335073
theorem B4508045 : Blo 1186410 4508045 := bstep (se 3 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 4508045 = 1690517) B1690517
theorem B5073293 : Blo 1186410 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B1780115 : Blo 1186410 1780115 := bstep (se 1 (by rfl) ⟨1335086, by rfl⟩ : syracuseStep 1780115 = 2670173) B2670173
theorem B4008365 : Blo 1186410 4008365 := bstep (se 3 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 4008365 = 1503137) B1503137
theorem B1780145 : Blo 1186410 1780145 := bstep (se 2 (by rfl) ⟨667554, by rfl⟩ : syracuseStep 1780145 = 1335109) B1335109
theorem B1780163 : Blo 1186410 1780163 := bstep (se 1 (by rfl) ⟨1335122, by rfl⟩ : syracuseStep 1780163 = 2670245) B2670245
theorem B1780193 : Blo 1186410 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B1804769 : Blo 1186410 1804769 := bstep (se 2 (by rfl) ⟨676788, by rfl⟩ : syracuseStep 1804769 = 1353577) B1353577
theorem B4008419 : Blo 1186410 4008419 := bstep (se 1 (by rfl) ⟨3006314, by rfl⟩ : syracuseStep 4008419 = 6012629) B6012629
theorem B2140643 : Blo 1186410 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B1780211 : Blo 1186410 1780211 := bstep (se 1 (by rfl) ⟨1335158, by rfl⟩ : syracuseStep 1780211 = 2670317) B2670317
theorem B6416909 : Blo 1186410 6416909 := bstep (se 3 (by rfl) ⟨1203170, by rfl⟩ : syracuseStep 6416909 = 2406341) B2406341
theorem B1780241 : Blo 1186410 1780241 := bstep (se 2 (by rfl) ⟨667590, by rfl⟩ : syracuseStep 1780241 = 1335181) B1335181
theorem B1780259 : Blo 1186410 1780259 := bstep (se 1 (by rfl) ⟨1335194, by rfl⟩ : syracuseStep 1780259 = 2670389) B2670389
theorem B1780289 : Blo 1186410 1780289 := bstep (se 2 (by rfl) ⟨667608, by rfl⟩ : syracuseStep 1780289 = 1335217) B1335217
theorem B2673233 : Blo 1186410 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B1780307 : Blo 1186410 1780307 := bstep (se 1 (by rfl) ⟨1335230, by rfl⟩ : syracuseStep 1780307 = 2670461) B2670461
theorem B2673251 : Blo 1186410 2673251 := bstep (se 1 (by rfl) ⟨2004938, by rfl⟩ : syracuseStep 2673251 = 4009877) B4009877
theorem B1780337 : Blo 1186410 1780337 := bstep (se 2 (by rfl) ⟨667626, by rfl⟩ : syracuseStep 1780337 = 1335253) B1335253
theorem B1780355 : Blo 1186410 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B1780385 : Blo 1186410 1780385 := bstep (se 2 (by rfl) ⟨667644, by rfl⟩ : syracuseStep 1780385 = 1335289) B1335289
theorem B1903267 : Blo 1186410 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B1780403 : Blo 1186410 1780403 := bstep (se 1 (by rfl) ⟨1335302, by rfl⟩ : syracuseStep 1780403 = 2670605) B2670605
theorem B3803843 : Blo 1186410 3803843 := bstep (se 1 (by rfl) ⟨2852882, by rfl⟩ : syracuseStep 3803843 = 5705765) B5705765
theorem B1780433 : Blo 1186410 1780433 := bstep (se 2 (by rfl) ⟨667662, by rfl⟩ : syracuseStep 1780433 = 1335325) B1335325
theorem B1780451 : Blo 1186410 1780451 := bstep (se 1 (by rfl) ⟨1335338, by rfl⟩ : syracuseStep 1780451 = 2670677) B2670677
theorem B4008689 : Blo 1186410 4008689 := bstep (se 2 (by rfl) ⟨1503258, by rfl⟩ : syracuseStep 4008689 = 3006517) B3006517
theorem B1780481 : Blo 1186410 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B2140931 : Blo 1186410 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B1780499 : Blo 1186410 1780499 := bstep (se 1 (by rfl) ⟨1335374, by rfl⟩ : syracuseStep 1780499 = 2670749) B2670749
theorem B2534179 : Blo 1186410 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B1780529 : Blo 1186410 1780529 := bstep (se 2 (by rfl) ⟨667698, by rfl⟩ : syracuseStep 1780529 = 1335397) B1335397
theorem B1502003 : Blo 1186410 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1780547 : Blo 1186410 1780547 := bstep (se 1 (by rfl) ⟨1335410, by rfl⟩ : syracuseStep 1780547 = 2670821) B2670821
theorem B1780577 : Blo 1186410 1780577 := bstep (se 2 (by rfl) ⟨667716, by rfl⟩ : syracuseStep 1780577 = 1335433) B1335433
theorem B2673521 : Blo 1186410 2673521 := bstep (se 2 (by rfl) ⟨1002570, by rfl⟩ : syracuseStep 2673521 = 2005141) B2005141
theorem B1780595 : Blo 1186410 1780595 := bstep (se 1 (by rfl) ⟨1335446, by rfl⟩ : syracuseStep 1780595 = 2670893) B2670893
theorem B1690483 : Blo 1186410 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B2673539 : Blo 1186410 2673539 := bstep (se 1 (by rfl) ⟨2005154, by rfl⟩ : syracuseStep 2673539 = 4010309) B4010309
theorem B1780625 : Blo 1186410 1780625 := bstep (se 2 (by rfl) ⟨667734, by rfl⟩ : syracuseStep 1780625 = 1335469) B1335469
theorem B1780643 : Blo 1186410 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1780673 : Blo 1186410 1780673 := bstep (se 2 (by rfl) ⟨667752, by rfl⟩ : syracuseStep 1780673 = 1335505) B1335505
theorem B1780691 : Blo 1186410 1780691 := bstep (se 1 (by rfl) ⟨1335518, by rfl⟩ : syracuseStep 1780691 = 2671037) B2671037
theorem B1780721 : Blo 1186410 1780721 := bstep (se 2 (by rfl) ⟨667770, by rfl⟩ : syracuseStep 1780721 = 1335541) B1335541
theorem B1780739 : Blo 1186410 1780739 := bstep (se 1 (by rfl) ⟨1335554, by rfl⟩ : syracuseStep 1780739 = 2671109) B2671109
theorem B1780769 : Blo 1186410 1780769 := bstep (se 2 (by rfl) ⟨667788, by rfl⟩ : syracuseStep 1780769 = 1335577) B1335577
theorem B8121379 : Blo 1186410 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B2255921 : Blo 1186410 2255921 := bstep (se 2 (by rfl) ⟨845970, by rfl⟩ : syracuseStep 2255921 = 1691941) B1691941
theorem B1780787 : Blo 1186410 1780787 := bstep (se 1 (by rfl) ⟨1335590, by rfl⟩ : syracuseStep 1780787 = 2671181) B2671181
theorem B1780817 : Blo 1186410 1780817 := bstep (se 2 (by rfl) ⟨667806, by rfl⟩ : syracuseStep 1780817 = 1335613) B1335613
theorem B3804241 : Blo 1186410 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B1780835 : Blo 1186410 1780835 := bstep (se 1 (by rfl) ⟨1335626, by rfl⟩ : syracuseStep 1780835 = 2671253) B2671253
theorem B1780865 : Blo 1186410 1780865 := bstep (se 2 (by rfl) ⟨667824, by rfl⟩ : syracuseStep 1780865 = 1335649) B1335649
theorem B2673809 : Blo 1186410 2673809 := bstep (se 2 (by rfl) ⟨1002678, by rfl⟩ : syracuseStep 2673809 = 2005357) B2005357
theorem B1780883 : Blo 1186410 1780883 := bstep (se 1 (by rfl) ⟨1335662, by rfl⟩ : syracuseStep 1780883 = 2671325) B2671325
theorem B2673827 : Blo 1186410 2673827 := bstep (se 1 (by rfl) ⟨2005370, by rfl⟩ : syracuseStep 2673827 = 4010741) B4010741
theorem B2002097 : Blo 1186410 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B1780913 : Blo 1186410 1780913 := bstep (se 2 (by rfl) ⟨667842, by rfl⟩ : syracuseStep 1780913 = 1335685) B1335685
theorem B1780931 : Blo 1186410 1780931 := bstep (se 1 (by rfl) ⟨1335698, by rfl⟩ : syracuseStep 1780931 = 2671397) B2671397
theorem B3804355 : Blo 1186410 3804355 := bstep (se 1 (by rfl) ⟨2853266, by rfl⟩ : syracuseStep 3804355 = 5706533) B5706533
theorem B1780961 : Blo 1186410 1780961 := bstep (se 2 (by rfl) ⟨667860, by rfl⟩ : syracuseStep 1780961 = 1335721) B1335721
theorem B1780979 : Blo 1186410 1780979 := bstep (se 1 (by rfl) ⟨1335734, by rfl⟩ : syracuseStep 1780979 = 2671469) B2671469
theorem B3607811 : Blo 1186410 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B4009229 : Blo 1186410 4009229 := bstep (se 3 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 4009229 = 1503461) B1503461
theorem B1781009 : Blo 1186410 1781009 := bstep (se 2 (by rfl) ⟨667878, by rfl⟩ : syracuseStep 1781009 = 1335757) B1335757
theorem B1355027 : Blo 1186410 1355027 := bstep (se 1 (by rfl) ⟨1016270, by rfl⟩ : syracuseStep 1355027 = 2032541) B2032541
theorem B1781027 : Blo 1186410 1781027 := bstep (se 1 (by rfl) ⟨1335770, by rfl⟩ : syracuseStep 1781027 = 2671541) B2671541
theorem B2002225 : Blo 1186410 2002225 := bstep (se 2 (by rfl) ⟨750834, by rfl⟩ : syracuseStep 2002225 = 1501669) B1501669
theorem B1781057 : Blo 1186410 1781057 := bstep (se 2 (by rfl) ⟨667896, by rfl⟩ : syracuseStep 1781057 = 1335793) B1335793
theorem B4009283 : Blo 1186410 4009283 := bstep (se 1 (by rfl) ⟨3006962, by rfl⟩ : syracuseStep 4009283 = 6013925) B6013925
theorem B1690961 : Blo 1186410 1690961 := bstep (se 2 (by rfl) ⟨634110, by rfl⟩ : syracuseStep 1690961 = 1268221) B1268221
theorem B2002259 : Blo 1186410 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B1781075 : Blo 1186410 1781075 := bstep (se 1 (by rfl) ⟨1335806, by rfl⟩ : syracuseStep 1781075 = 2671613) B2671613
theorem B1781105 : Blo 1186410 1781105 := bstep (se 2 (by rfl) ⟨667914, by rfl⟩ : syracuseStep 1781105 = 1335829) B1335829
theorem B3427697 : Blo 1186410 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B1781123 : Blo 1186410 1781123 := bstep (se 1 (by rfl) ⟨1335842, by rfl⟩ : syracuseStep 1781123 = 2671685) B2671685
theorem B7613837 : Blo 1186410 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B1781153 : Blo 1186410 1781153 := bstep (se 2 (by rfl) ⟨667932, by rfl⟩ : syracuseStep 1781153 = 1335865) B1335865
theorem B1781171 : Blo 1186410 1781171 := bstep (se 1 (by rfl) ⟨1335878, by rfl⟩ : syracuseStep 1781171 = 2671757) B2671757
theorem B1928627 : Blo 1186410 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1691075 : Blo 1186410 1691075 := bstep (se 1 (by rfl) ⟨1268306, by rfl⟩ : syracuseStep 1691075 = 2536613) B2536613
theorem B1781201 : Blo 1186410 1781201 := bstep (se 2 (by rfl) ⟨667950, by rfl⟩ : syracuseStep 1781201 = 1335901) B1335901
theorem B2002387 : Blo 1186410 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B1781219 : Blo 1186410 1781219 := bstep (se 1 (by rfl) ⟨1335914, by rfl⟩ : syracuseStep 1781219 = 2671829) B2671829
theorem B1502707 : Blo 1186410 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B1781249 : Blo 1186410 1781249 := bstep (se 2 (by rfl) ⟨667968, by rfl⟩ : syracuseStep 1781249 = 1335937) B1335937
theorem B1781267 : Blo 1186410 1781267 := bstep (se 1 (by rfl) ⟨1335950, by rfl⟩ : syracuseStep 1781267 = 2671901) B2671901
theorem B1691155 : Blo 1186410 1691155 := bstep (se 1 (by rfl) ⟨1268366, by rfl⟩ : syracuseStep 1691155 = 2536733) B2536733
theorem B1781297 : Blo 1186410 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B1781315 : Blo 1186410 1781315 := bstep (se 1 (by rfl) ⟨1335986, by rfl⟩ : syracuseStep 1781315 = 2671973) B2671973
theorem B2707025 : Blo 1186410 2707025 := bstep (se 2 (by rfl) ⟨1015134, by rfl⟩ : syracuseStep 2707025 = 2030269) B2030269
theorem B4009553 : Blo 1186410 4009553 := bstep (se 2 (by rfl) ⟨1503582, by rfl⟩ : syracuseStep 4009553 = 3007165) B3007165
theorem B1502803 : Blo 1186410 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B2002529 : Blo 1186410 2002529 := bstep (se 2 (by rfl) ⟨750948, by rfl⟩ : syracuseStep 2002529 = 1501897) B1501897
theorem B1781345 : Blo 1186410 1781345 := bstep (se 2 (by rfl) ⟨668004, by rfl⟩ : syracuseStep 1781345 = 1336009) B1336009
theorem B9023075 : Blo 1186410 9023075 := bstep (se 1 (by rfl) ⟨6767306, by rfl⟩ : syracuseStep 9023075 = 13534613) B13534613
theorem B1781363 : Blo 1186410 1781363 := bstep (se 1 (by rfl) ⟨1336022, by rfl⟩ : syracuseStep 1781363 = 2672045) B2672045
theorem B1781393 : Blo 1186410 1781393 := bstep (se 2 (by rfl) ⟨668022, by rfl⟩ : syracuseStep 1781393 = 1336045) B1336045
theorem B1781411 : Blo 1186410 1781411 := bstep (se 1 (by rfl) ⟨1336058, by rfl⟩ : syracuseStep 1781411 = 2672117) B2672117
theorem B1781441 : Blo 1186410 1781441 := bstep (se 2 (by rfl) ⟨668040, by rfl⟩ : syracuseStep 1781441 = 1336081) B1336081
theorem B1781459 : Blo 1186410 1781459 := bstep (se 1 (by rfl) ⟨1336094, by rfl⟩ : syracuseStep 1781459 = 2672189) B2672189
theorem B2002657 : Blo 1186410 2002657 := bstep (se 2 (by rfl) ⟨750996, by rfl⟩ : syracuseStep 2002657 = 1501993) B1501993
theorem B1781489 : Blo 1186410 1781489 := bstep (se 2 (by rfl) ⟨668058, by rfl⟩ : syracuseStep 1781489 = 1336117) B1336117
theorem B2002691 : Blo 1186410 2002691 := bstep (se 1 (by rfl) ⟨1502018, by rfl⟩ : syracuseStep 2002691 = 3004037) B3004037
theorem B7606021 : Blo 1186410 7606021 := bstep (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) B1426129
theorem B1781507 : Blo 1186410 1781507 := bstep (se 1 (by rfl) ⟨1336130, by rfl⟩ : syracuseStep 1781507 = 2672261) B2672261
theorem B4566797 : Blo 1186410 4566797 := bstep (se 3 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 4566797 = 1712549) B1712549
theorem B1781537 : Blo 1186410 1781537 := bstep (se 2 (by rfl) ⟨668076, by rfl⟩ : syracuseStep 1781537 = 1336153) B1336153
theorem B1781555 : Blo 1186410 1781555 := bstep (se 1 (by rfl) ⟨1336166, by rfl⟩ : syracuseStep 1781555 = 2672333) B2672333
theorem B1781585 : Blo 1186410 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B8343395 : Blo 1186410 8343395 := bstep (se 1 (by rfl) ⟨6257546, by rfl⟩ : syracuseStep 8343395 = 12515093) B12515093
theorem B1781603 : Blo 1186410 1781603 := bstep (se 1 (by rfl) ⟨1336202, by rfl⟩ : syracuseStep 1781603 = 2672405) B2672405
theorem B1781633 : Blo 1186410 1781633 := bstep (se 2 (by rfl) ⟨668112, by rfl⟩ : syracuseStep 1781633 = 1336225) B1336225
theorem B2002819 : Blo 1186410 2002819 := bstep (se 1 (by rfl) ⟨1502114, by rfl⟩ : syracuseStep 2002819 = 3004229) B3004229
theorem B56323981 : Blo 1186410 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B3805073 : Blo 1186410 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B1781651 : Blo 1186410 1781651 := bstep (se 1 (by rfl) ⟨1336238, by rfl⟩ : syracuseStep 1781651 = 2672477) B2672477
theorem B3379121 : Blo 1186410 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B1781681 : Blo 1186410 1781681 := bstep (se 2 (by rfl) ⟨668130, by rfl⟩ : syracuseStep 1781681 = 1336261) B1336261
theorem B1781699 : Blo 1186410 1781699 := bstep (se 1 (by rfl) ⟨1336274, by rfl⟩ : syracuseStep 1781699 = 2672549) B2672549
theorem B11407301 : Blo 1186410 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B1781729 : Blo 1186410 1781729 := bstep (se 2 (by rfl) ⟨668148, by rfl⟩ : syracuseStep 1781729 = 1336297) B1336297
theorem B1929185 : Blo 1186410 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B1781747 : Blo 1186410 1781747 := bstep (se 1 (by rfl) ⟨1336310, by rfl⟩ : syracuseStep 1781747 = 2672621) B2672621
theorem B2002961 : Blo 1186410 2002961 := bstep (se 2 (by rfl) ⟨751110, by rfl⟩ : syracuseStep 2002961 = 1502221) B1502221
theorem B1781777 : Blo 1186410 1781777 := bstep (se 2 (by rfl) ⟨668166, by rfl⟩ : syracuseStep 1781777 = 1336333) B1336333
theorem B1781795 : Blo 1186410 1781795 := bstep (se 1 (by rfl) ⟨1336346, by rfl⟩ : syracuseStep 1781795 = 2672693) B2672693
theorem B1781825 : Blo 1186410 1781825 := bstep (se 2 (by rfl) ⟨668184, by rfl⟩ : syracuseStep 1781825 = 1336369) B1336369
theorem B1691713 : Blo 1186410 1691713 := bstep (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) B1268785
theorem B1503299 : Blo 1186410 1503299 := bstep (se 1 (by rfl) ⟨1127474, by rfl⟩ : syracuseStep 1503299 = 2254949) B2254949
theorem B1781843 : Blo 1186410 1781843 := bstep (se 1 (by rfl) ⟨1336382, by rfl⟩ : syracuseStep 1781843 = 2672765) B2672765
theorem B4010093 : Blo 1186410 4010093 := bstep (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) B1503785
theorem B1781873 : Blo 1186410 1781873 := bstep (se 2 (by rfl) ⟨668202, by rfl⟩ : syracuseStep 1781873 = 1336405) B1336405
theorem B1781891 : Blo 1186410 1781891 := bstep (se 1 (by rfl) ⟨1336418, by rfl⟩ : syracuseStep 1781891 = 2672837) B2672837
theorem B4059277 : Blo 1186410 4059277 := bstep (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) B1522229
theorem B2003089 : Blo 1186410 2003089 := bstep (se 2 (by rfl) ⟨751158, by rfl⟩ : syracuseStep 2003089 = 1502317) B1502317
theorem B1781921 : Blo 1186410 1781921 := bstep (se 2 (by rfl) ⟨668220, by rfl⟩ : syracuseStep 1781921 = 1336441) B1336441
theorem B4010147 : Blo 1186410 4010147 := bstep (se 1 (by rfl) ⟨3007610, by rfl⟩ : syracuseStep 4010147 = 6015221) B6015221
theorem B2003123 : Blo 1186410 2003123 := bstep (se 1 (by rfl) ⟨1502342, by rfl⟩ : syracuseStep 2003123 = 3004685) B3004685
theorem B1781939 : Blo 1186410 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1781969 : Blo 1186410 1781969 := bstep (se 2 (by rfl) ⟨668238, by rfl⟩ : syracuseStep 1781969 = 1336477) B1336477
theorem B1781987 : Blo 1186410 1781987 := bstep (se 1 (by rfl) ⟨1336490, by rfl⟩ : syracuseStep 1781987 = 2672981) B2672981
theorem B1782017 : Blo 1186410 1782017 := bstep (se 2 (by rfl) ⟨668256, by rfl⟩ : syracuseStep 1782017 = 1336513) B1336513
theorem B1782035 : Blo 1186410 1782035 := bstep (se 1 (by rfl) ⟨1336526, by rfl⟩ : syracuseStep 1782035 = 2673053) B2673053
theorem B1782065 : Blo 1186410 1782065 := bstep (se 2 (by rfl) ⟨668274, by rfl⟩ : syracuseStep 1782065 = 1336549) B1336549
theorem B2003251 : Blo 1186410 2003251 := bstep (se 1 (by rfl) ⟨1502438, by rfl⟩ : syracuseStep 2003251 = 3004877) B3004877
theorem B1446211 : Blo 1186410 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B1782083 : Blo 1186410 1782083 := bstep (se 1 (by rfl) ⟨1336562, by rfl⟩ : syracuseStep 1782083 = 2673125) B2673125
theorem B1782113 : Blo 1186410 1782113 := bstep (se 2 (by rfl) ⟨668292, by rfl⟩ : syracuseStep 1782113 = 1336585) B1336585
theorem B5140849 : Blo 1186410 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B1782131 : Blo 1186410 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1782161 : Blo 1186410 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B1782179 : Blo 1186410 1782179 := bstep (se 1 (by rfl) ⟨1336634, by rfl⟩ : syracuseStep 1782179 = 2673269) B2673269
theorem B3805613 : Blo 1186410 3805613 := bstep (se 3 (by rfl) ⟨713552, by rfl⟩ : syracuseStep 3805613 = 1427105) B1427105
theorem B4010417 : Blo 1186410 4010417 := bstep (se 2 (by rfl) ⟨1503906, by rfl⟩ : syracuseStep 4010417 = 3007813) B3007813
theorem B2003393 : Blo 1186410 2003393 := bstep (se 2 (by rfl) ⟨751272, by rfl⟩ : syracuseStep 2003393 = 1502545) B1502545
theorem B1782209 : Blo 1186410 1782209 := bstep (se 2 (by rfl) ⟨668328, by rfl⟩ : syracuseStep 1782209 = 1336657) B1336657
theorem B17125829 : Blo 1186410 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B1782227 : Blo 1186410 1782227 := bstep (se 1 (by rfl) ⟨1336670, by rfl⟩ : syracuseStep 1782227 = 2673341) B2673341
theorem B1782257 : Blo 1186410 1782257 := bstep (se 2 (by rfl) ⟨668346, by rfl⟩ : syracuseStep 1782257 = 1336693) B1336693
theorem B1782275 : Blo 1186410 1782275 := bstep (se 1 (by rfl) ⟨1336706, by rfl⟩ : syracuseStep 1782275 = 2673413) B2673413
theorem B1782305 : Blo 1186410 1782305 := bstep (se 2 (by rfl) ⟨668364, by rfl⟩ : syracuseStep 1782305 = 1336729) B1336729
theorem B1782323 : Blo 1186410 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B2003521 : Blo 1186410 2003521 := bstep (se 2 (by rfl) ⟨751320, by rfl⟩ : syracuseStep 2003521 = 1502641) B1502641
theorem B1782353 : Blo 1186410 1782353 := bstep (se 2 (by rfl) ⟨668382, by rfl⟩ : syracuseStep 1782353 = 1336765) B1336765
theorem B2003555 : Blo 1186410 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B1782371 : Blo 1186410 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B4117105 : Blo 1186410 4117105 := bstep (se 2 (by rfl) ⟨1543914, by rfl⟩ : syracuseStep 4117105 = 3087829) B3087829
theorem B2536049 : Blo 1186410 2536049 := bstep (se 2 (by rfl) ⟨951018, by rfl⟩ : syracuseStep 2536049 = 1902037) B1902037
theorem B1782401 : Blo 1186410 1782401 := bstep (se 2 (by rfl) ⟨668400, by rfl⟩ : syracuseStep 1782401 = 1336801) B1336801
theorem B1446547 : Blo 1186410 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B1782419 : Blo 1186410 1782419 := bstep (se 1 (by rfl) ⟨1336814, by rfl⟩ : syracuseStep 1782419 = 2673629) B2673629
theorem B4338353 : Blo 1186410 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B1782449 : Blo 1186410 1782449 := bstep (se 2 (by rfl) ⟨668418, by rfl⟩ : syracuseStep 1782449 = 1336837) B1336837
theorem B3379907 : Blo 1186410 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B1782467 : Blo 1186410 1782467 := bstep (se 1 (by rfl) ⟨1336850, by rfl⟩ : syracuseStep 1782467 = 2673701) B2673701
theorem B1782497 : Blo 1186410 1782497 := bstep (se 2 (by rfl) ⟨668436, by rfl⟩ : syracuseStep 1782497 = 1336873) B1336873
theorem B2003683 : Blo 1186410 2003683 := bstep (se 1 (by rfl) ⟨1502762, by rfl⟩ : syracuseStep 2003683 = 3005525) B3005525
theorem B1782515 : Blo 1186410 1782515 := bstep (se 1 (by rfl) ⟨1336886, by rfl⟩ : syracuseStep 1782515 = 2673773) B2673773
theorem B1504003 : Blo 1186410 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B1782545 : Blo 1186410 1782545 := bstep (se 2 (by rfl) ⟨668454, by rfl⟩ : syracuseStep 1782545 = 1336909) B1336909
theorem B1782563 : Blo 1186410 1782563 := bstep (se 1 (by rfl) ⟨1336922, by rfl⟩ : syracuseStep 1782563 = 2673845) B2673845
theorem B1782593 : Blo 1186410 1782593 := bstep (se 2 (by rfl) ⟨668472, by rfl⟩ : syracuseStep 1782593 = 1336945) B1336945
theorem B1782611 : Blo 1186410 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B28865393 : Blo 1186410 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B6009713 : Blo 1186410 6009713 := bstep (se 2 (by rfl) ⟨2253642, by rfl⟩ : syracuseStep 6009713 = 4507285) B4507285
theorem B2003825 : Blo 1186410 2003825 := bstep (se 2 (by rfl) ⟨751434, by rfl⟩ : syracuseStep 2003825 = 1502869) B1502869
theorem B3208099 : Blo 1186410 3208099 := bstep (se 1 (by rfl) ⟨2406074, by rfl⟩ : syracuseStep 3208099 = 4812149) B4812149
theorem B1446835 : Blo 1186410 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B2003953 : Blo 1186410 2003953 := bstep (se 2 (by rfl) ⟨751482, by rfl⟩ : syracuseStep 2003953 = 1502965) B1502965
theorem B3380237 : Blo 1186410 3380237 := bstep (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) B1267589
theorem B2003987 : Blo 1186410 2003987 := bstep (se 1 (by rfl) ⟨1502990, by rfl⟩ : syracuseStep 2003987 = 3005981) B3005981
theorem B3380305 : Blo 1186410 3380305 := bstep (se 2 (by rfl) ⟨1267614, by rfl⟩ : syracuseStep 3380305 = 2535229) B2535229
theorem B2004115 : Blo 1186410 2004115 := bstep (se 1 (by rfl) ⟨1503086, by rfl⟩ : syracuseStep 2004115 = 3006173) B3006173
theorem B8123597 : Blo 1186410 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B3003601 : Blo 1186410 3003601 := bstep (se 2 (by rfl) ⟨1126350, by rfl⟩ : syracuseStep 3003601 = 2252701) B2252701
theorem B4510961 : Blo 1186410 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B2004257 : Blo 1186410 2004257 := bstep (se 2 (by rfl) ⟨751596, by rfl⟩ : syracuseStep 2004257 = 1503193) B1503193
theorem B3380579 : Blo 1186410 3380579 := bstep (se 1 (by rfl) ⟨2535434, by rfl⟩ : syracuseStep 3380579 = 5070869) B5070869
theorem B2004385 : Blo 1186410 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B2004419 : Blo 1186410 2004419 := bstep (se 1 (by rfl) ⟨1503314, by rfl⟩ : syracuseStep 2004419 = 3006629) B3006629
theorem B2536913 : Blo 1186410 2536913 := bstep (se 2 (by rfl) ⟨951342, by rfl⟩ : syracuseStep 2536913 = 1902685) B1902685
theorem B3003875 : Blo 1186410 3003875 := bstep (se 1 (by rfl) ⟨2252906, by rfl⟩ : syracuseStep 3003875 = 4505813) B4505813
theorem B2004547 : Blo 1186410 2004547 := bstep (se 1 (by rfl) ⟨1503410, by rfl⟩ : syracuseStep 2004547 = 3006821) B3006821
theorem B3004067 : Blo 1186410 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B1267363 : Blo 1186410 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B2709169 : Blo 1186410 2709169 := bstep (se 2 (by rfl) ⟨1015938, by rfl⟩ : syracuseStep 2709169 = 2031877) B2031877
theorem B2004689 : Blo 1186410 2004689 := bstep (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) B1503517
theorem B2004817 : Blo 1186410 2004817 := bstep (se 2 (by rfl) ⟨751806, by rfl⟩ : syracuseStep 2004817 = 1503613) B1503613
theorem B2004851 : Blo 1186410 2004851 := bstep (se 1 (by rfl) ⟨1503638, by rfl⟩ : syracuseStep 2004851 = 3007277) B3007277
theorem B7706501 : Blo 1186410 7706501 := bstep (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) B1444969
theorem B4569059 : Blo 1186410 4569059 := bstep (se 1 (by rfl) ⟨3426794, by rfl⟩ : syracuseStep 4569059 = 6853589) B6853589
theorem B2004979 : Blo 1186410 2004979 := bstep (se 1 (by rfl) ⟨1503734, by rfl⟩ : syracuseStep 2004979 = 3007469) B3007469
theorem B3610669 : Blo 1186410 3610669 := bstep (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) B1354001
theorem B2005121 : Blo 1186410 2005121 := bstep (se 2 (by rfl) ⟨751920, by rfl⟩ : syracuseStep 2005121 = 1503841) B1503841
theorem B6600845 : Blo 1186410 6600845 := bstep (se 3 (by rfl) ⟨1237658, by rfl⟩ : syracuseStep 6600845 = 2475317) B2475317
theorem B3381421 : Blo 1186410 3381421 := bstep (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) B1268033
theorem B2005249 : Blo 1186410 2005249 := bstep (se 2 (by rfl) ⟨751968, by rfl⟩ : syracuseStep 2005249 = 1503937) B1503937
theorem B6011171 : Blo 1186410 6011171 := bstep (se 1 (by rfl) ⟨4508378, by rfl⟩ : syracuseStep 6011171 = 9016757) B9016757
theorem B2005283 : Blo 1186410 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B3381581 : Blo 1186410 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B2005411 : Blo 1186410 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B3381763 : Blo 1186410 3381763 := bstep (se 1 (by rfl) ⟨2536322, by rfl⟩ : syracuseStep 3381763 = 5072645) B5072645
theorem B4004369 : Blo 1186410 4004369 := bstep (se 2 (by rfl) ⟨1501638, by rfl⟩ : syracuseStep 4004369 = 3003277) B3003277
theorem B6855203 : Blo 1186410 6855203 := bstep (se 1 (by rfl) ⟨5141402, by rfl⟩ : syracuseStep 6855203 = 10282805) B10282805
theorem B4815409 : Blo 1186410 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B3005009 : Blo 1186410 3005009 := bstep (se 2 (by rfl) ⟨1126878, by rfl⟩ : syracuseStep 3005009 = 2253757) B2253757
theorem B1186419 : Blo 1186410 1186419 := bstep (se 1 (by rfl) ⟨889814, by rfl⟩ : syracuseStep 1186419 = 1779629) B1779629
theorem B1186435 : Blo 1186410 1186435 := bstep (se 1 (by rfl) ⟨889826, by rfl⟩ : syracuseStep 1186435 = 1779653) B1779653
theorem B3005059 : Blo 1186410 3005059 := bstep (se 1 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 3005059 = 4507589) B4507589
theorem B1186451 : Blo 1186410 1186451 := bstep (se 1 (by rfl) ⟨889838, by rfl⟩ : syracuseStep 1186451 = 1779677) B1779677
theorem B1186467 : Blo 1186410 1186467 := bstep (se 1 (by rfl) ⟨889850, by rfl⟩ : syracuseStep 1186467 = 1779701) B1779701
theorem B4340387 : Blo 1186410 4340387 := bstep (se 1 (by rfl) ⟨3255290, by rfl⟩ : syracuseStep 4340387 = 6510581) B6510581
theorem B1186483 : Blo 1186410 1186483 := bstep (se 1 (by rfl) ⟨889862, by rfl⟩ : syracuseStep 1186483 = 1779725) B1779725
theorem B1186499 : Blo 1186410 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B1186515 : Blo 1186410 1186515 := bstep (se 1 (by rfl) ⟨889886, by rfl⟩ : syracuseStep 1186515 = 1779773) B1779773
theorem B1186531 : Blo 1186410 1186531 := bstep (se 1 (by rfl) ⟨889898, by rfl⟩ : syracuseStep 1186531 = 1779797) B1779797
theorem B5708515 : Blo 1186410 5708515 := bstep (se 1 (by rfl) ⟨4281386, by rfl⟩ : syracuseStep 5708515 = 8562773) B8562773
theorem B9263857 : Blo 1186410 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B2407153 : Blo 1186410 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B1186547 : Blo 1186410 1186547 := bstep (se 1 (by rfl) ⟨889910, by rfl⟩ : syracuseStep 1186547 = 1779821) B1779821
theorem B1604353 : Blo 1186410 1604353 := bstep (se 2 (by rfl) ⟨601632, by rfl⟩ : syracuseStep 1604353 = 1203265) B1203265
theorem B1186563 : Blo 1186410 1186563 := bstep (se 1 (by rfl) ⟨889922, by rfl⟩ : syracuseStep 1186563 = 1779845) B1779845
theorem B3005201 : Blo 1186410 3005201 := bstep (se 2 (by rfl) ⟨1126950, by rfl⟩ : syracuseStep 3005201 = 2253901) B2253901
theorem B1186579 : Blo 1186410 1186579 := bstep (se 1 (by rfl) ⟨889934, by rfl⟩ : syracuseStep 1186579 = 1779869) B1779869
theorem B1186595 : Blo 1186410 1186595 := bstep (se 1 (by rfl) ⟨889946, by rfl⟩ : syracuseStep 1186595 = 1779893) B1779893
theorem B5069603 : Blo 1186410 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B1186611 : Blo 1186410 1186611 := bstep (se 1 (by rfl) ⟨889958, by rfl⟩ : syracuseStep 1186611 = 1779917) B1779917
theorem B1186627 : Blo 1186410 1186627 := bstep (se 1 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 1186627 = 1779941) B1779941
theorem B1186643 : Blo 1186410 1186643 := bstep (se 1 (by rfl) ⟨889982, by rfl⟩ : syracuseStep 1186643 = 1779965) B1779965
theorem B1186659 : Blo 1186410 1186659 := bstep (se 1 (by rfl) ⟨889994, by rfl⟩ : syracuseStep 1186659 = 1779989) B1779989
theorem B1186675 : Blo 1186410 1186675 := bstep (se 1 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 1186675 = 1780013) B1780013
theorem B1186691 : Blo 1186410 1186691 := bstep (se 1 (by rfl) ⟨890018, by rfl⟩ : syracuseStep 1186691 = 1780037) B1780037
theorem B2169731 : Blo 1186410 2169731 := bstep (se 1 (by rfl) ⟨1627298, by rfl⟩ : syracuseStep 2169731 = 3254597) B3254597
theorem B1186707 : Blo 1186410 1186707 := bstep (se 1 (by rfl) ⟨890030, by rfl⟩ : syracuseStep 1186707 = 1780061) B1780061
theorem B1268627 : Blo 1186410 1268627 := bstep (se 1 (by rfl) ⟨951470, by rfl⟩ : syracuseStep 1268627 = 1902941) B1902941
theorem B6757283 : Blo 1186410 6757283 := bstep (se 1 (by rfl) ⟨5067962, by rfl⟩ : syracuseStep 6757283 = 10135925) B10135925
theorem B1186723 : Blo 1186410 1186723 := bstep (se 1 (by rfl) ⟨890042, by rfl⟩ : syracuseStep 1186723 = 1780085) B1780085
theorem B2669489 : Blo 1186410 2669489 := bstep (se 2 (by rfl) ⟨1001058, by rfl⟩ : syracuseStep 2669489 = 2002117) B2002117
theorem B1186739 : Blo 1186410 1186739 := bstep (se 1 (by rfl) ⟨890054, by rfl⟩ : syracuseStep 1186739 = 1780109) B1780109
theorem B2669507 : Blo 1186410 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B1186755 : Blo 1186410 1186755 := bstep (se 1 (by rfl) ⟨890066, by rfl⟩ : syracuseStep 1186755 = 1780133) B1780133
theorem B10705861 : Blo 1186410 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B1186771 : Blo 1186410 1186771 := bstep (se 1 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 1186771 = 1780157) B1780157
theorem B1186787 : Blo 1186410 1186787 := bstep (se 1 (by rfl) ⟨890090, by rfl⟩ : syracuseStep 1186787 = 1780181) B1780181
theorem B1186803 : Blo 1186410 1186803 := bstep (se 1 (by rfl) ⟨890102, by rfl⟩ : syracuseStep 1186803 = 1780205) B1780205
theorem B1186819 : Blo 1186410 1186819 := bstep (se 1 (by rfl) ⟨890114, by rfl⟩ : syracuseStep 1186819 = 1780229) B1780229
theorem B1186835 : Blo 1186410 1186835 := bstep (se 1 (by rfl) ⟨890126, by rfl⟩ : syracuseStep 1186835 = 1780253) B1780253
theorem B1186851 : Blo 1186410 1186851 := bstep (se 1 (by rfl) ⟨890138, by rfl⟩ : syracuseStep 1186851 = 1780277) B1780277
theorem B4004909 : Blo 1186410 4004909 := bstep (se 3 (by rfl) ⟨750920, by rfl⟩ : syracuseStep 4004909 = 1501841) B1501841
theorem B1186867 : Blo 1186410 1186867 := bstep (se 1 (by rfl) ⟨890150, by rfl⟩ : syracuseStep 1186867 = 1780301) B1780301
theorem B1186883 : Blo 1186410 1186883 := bstep (se 1 (by rfl) ⟨890162, by rfl⟩ : syracuseStep 1186883 = 1780325) B1780325
theorem B6011981 : Blo 1186410 6011981 := bstep (se 3 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 6011981 = 2254493) B2254493
theorem B1186899 : Blo 1186410 1186899 := bstep (se 1 (by rfl) ⟨890174, by rfl⟩ : syracuseStep 1186899 = 1780349) B1780349
theorem B4004963 : Blo 1186410 4004963 := bstep (se 1 (by rfl) ⟨3003722, by rfl⟩ : syracuseStep 4004963 = 6007445) B6007445
theorem B1186915 : Blo 1186410 1186915 := bstep (se 1 (by rfl) ⟨890186, by rfl⟩ : syracuseStep 1186915 = 1780373) B1780373
theorem B3210349 : Blo 1186410 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B1186931 : Blo 1186410 1186931 := bstep (se 1 (by rfl) ⟨890198, by rfl⟩ : syracuseStep 1186931 = 1780397) B1780397
theorem B1186947 : Blo 1186410 1186947 := bstep (se 1 (by rfl) ⟨890210, by rfl⟩ : syracuseStep 1186947 = 1780421) B1780421
theorem B1186963 : Blo 1186410 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B1186979 : Blo 1186410 1186979 := bstep (se 1 (by rfl) ⟨890234, by rfl⟩ : syracuseStep 1186979 = 1780469) B1780469
theorem B1186995 : Blo 1186410 1186995 := bstep (se 1 (by rfl) ⟨890246, by rfl⟩ : syracuseStep 1186995 = 1780493) B1780493
theorem B1187011 : Blo 1186410 1187011 := bstep (se 1 (by rfl) ⟨890258, by rfl⟩ : syracuseStep 1187011 = 1780517) B1780517
theorem B2669777 : Blo 1186410 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B1187027 : Blo 1186410 1187027 := bstep (se 1 (by rfl) ⟨890270, by rfl⟩ : syracuseStep 1187027 = 1780541) B1780541
theorem B2669795 : Blo 1186410 2669795 := bstep (se 1 (by rfl) ⟨2002346, by rfl⟩ : syracuseStep 2669795 = 4004693) B4004693
theorem B1187043 : Blo 1186410 1187043 := bstep (se 1 (by rfl) ⟨890282, by rfl⟩ : syracuseStep 1187043 = 1780565) B1780565
theorem B1203427 : Blo 1186410 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B4881635 : Blo 1186410 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B1187059 : Blo 1186410 1187059 := bstep (se 1 (by rfl) ⟨890294, by rfl⟩ : syracuseStep 1187059 = 1780589) B1780589
theorem B1187075 : Blo 1186410 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B7216397 : Blo 1186410 7216397 := bstep (se 3 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 7216397 = 2706149) B2706149
theorem B1187091 : Blo 1186410 1187091 := bstep (se 1 (by rfl) ⟨890318, by rfl⟩ : syracuseStep 1187091 = 1780637) B1780637
theorem B1187107 : Blo 1186410 1187107 := bstep (se 1 (by rfl) ⟨890330, by rfl⟩ : syracuseStep 1187107 = 1780661) B1780661
theorem B1187123 : Blo 1186410 1187123 := bstep (se 1 (by rfl) ⟨890342, by rfl⟩ : syracuseStep 1187123 = 1780685) B1780685
theorem B1187139 : Blo 1186410 1187139 := bstep (se 1 (by rfl) ⟨890354, by rfl⟩ : syracuseStep 1187139 = 1780709) B1780709
theorem B1187155 : Blo 1186410 1187155 := bstep (se 1 (by rfl) ⟨890366, by rfl⟩ : syracuseStep 1187155 = 1780733) B1780733
theorem B1187171 : Blo 1186410 1187171 := bstep (se 1 (by rfl) ⟨890378, by rfl⟩ : syracuseStep 1187171 = 1780757) B1780757
theorem B4005233 : Blo 1186410 4005233 := bstep (se 2 (by rfl) ⟨1501962, by rfl⟩ : syracuseStep 4005233 = 3003925) B3003925
theorem B1187187 : Blo 1186410 1187187 := bstep (se 1 (by rfl) ⟨890390, by rfl⟩ : syracuseStep 1187187 = 1780781) B1780781
theorem B1187203 : Blo 1186410 1187203 := bstep (se 1 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 1187203 = 1780805) B1780805
theorem B1187219 : Blo 1186410 1187219 := bstep (se 1 (by rfl) ⟨890414, by rfl⟩ : syracuseStep 1187219 = 1780829) B1780829
theorem B1187235 : Blo 1186410 1187235 := bstep (se 1 (by rfl) ⟨890426, by rfl⟩ : syracuseStep 1187235 = 1780853) B1780853
theorem B1187251 : Blo 1186410 1187251 := bstep (se 1 (by rfl) ⟨890438, by rfl⟩ : syracuseStep 1187251 = 1780877) B1780877
theorem B1187267 : Blo 1186410 1187267 := bstep (se 1 (by rfl) ⟨890450, by rfl⟩ : syracuseStep 1187267 = 1780901) B1780901
theorem B1187283 : Blo 1186410 1187283 := bstep (se 1 (by rfl) ⟨890462, by rfl⟩ : syracuseStep 1187283 = 1780925) B1780925
theorem B1187299 : Blo 1186410 1187299 := bstep (se 1 (by rfl) ⟨890474, by rfl⟩ : syracuseStep 1187299 = 1780949) B1780949
theorem B2670065 : Blo 1186410 2670065 := bstep (se 2 (by rfl) ⟨1001274, by rfl⟩ : syracuseStep 2670065 = 2002549) B2002549
theorem B1187315 : Blo 1186410 1187315 := bstep (se 1 (by rfl) ⟨890486, by rfl⟩ : syracuseStep 1187315 = 1780973) B1780973
theorem B2670083 : Blo 1186410 2670083 := bstep (se 1 (by rfl) ⟨2002562, by rfl⟩ : syracuseStep 2670083 = 4005125) B4005125
theorem B1187331 : Blo 1186410 1187331 := bstep (se 1 (by rfl) ⟨890498, by rfl⟩ : syracuseStep 1187331 = 1780997) B1780997
theorem B1334803 : Blo 1186410 1334803 := bstep (se 1 (by rfl) ⟨1001102, by rfl⟩ : syracuseStep 1334803 = 2002205) B2002205
theorem B1187347 : Blo 1186410 1187347 := bstep (se 1 (by rfl) ⟨890510, by rfl⟩ : syracuseStep 1187347 = 1781021) B1781021
theorem B1187363 : Blo 1186410 1187363 := bstep (se 1 (by rfl) ⟨890522, by rfl⟩ : syracuseStep 1187363 = 1781045) B1781045
theorem B1187379 : Blo 1186410 1187379 := bstep (se 1 (by rfl) ⟨890534, by rfl⟩ : syracuseStep 1187379 = 1781069) B1781069
theorem B1187395 : Blo 1186410 1187395 := bstep (se 1 (by rfl) ⟨890546, by rfl⟩ : syracuseStep 1187395 = 1781093) B1781093
theorem B1187411 : Blo 1186410 1187411 := bstep (se 1 (by rfl) ⟨890558, by rfl⟩ : syracuseStep 1187411 = 1781117) B1781117
theorem B1187427 : Blo 1186410 1187427 := bstep (se 1 (by rfl) ⟨890570, by rfl⟩ : syracuseStep 1187427 = 1781141) B1781141
theorem B1187443 : Blo 1186410 1187443 := bstep (se 1 (by rfl) ⟨890582, by rfl⟩ : syracuseStep 1187443 = 1781165) B1781165
theorem B1187459 : Blo 1186410 1187459 := bstep (se 1 (by rfl) ⟨890594, by rfl⟩ : syracuseStep 1187459 = 1781189) B1781189
theorem B6766213 : Blo 1186410 6766213 := bstep (se 4 (by rfl) ⟨634332, by rfl⟩ : syracuseStep 6766213 = 1268665) B1268665
theorem B1187475 : Blo 1186410 1187475 := bstep (se 1 (by rfl) ⟨890606, by rfl⟩ : syracuseStep 1187475 = 1781213) B1781213
theorem B1334947 : Blo 1186410 1334947 := bstep (se 1 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 1334947 = 2002421) B2002421
theorem B1187491 : Blo 1186410 1187491 := bstep (se 1 (by rfl) ⟨890618, by rfl⟩ : syracuseStep 1187491 = 1781237) B1781237
theorem B1187507 : Blo 1186410 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B1187523 : Blo 1186410 1187523 := bstep (se 1 (by rfl) ⟨890642, by rfl⟩ : syracuseStep 1187523 = 1781285) B1781285
theorem B8117957 : Blo 1186410 8117957 := bstep (se 4 (by rfl) ⟨761058, by rfl⟩ : syracuseStep 8117957 = 1522117) B1522117
theorem B1187539 : Blo 1186410 1187539 := bstep (se 1 (by rfl) ⟨890654, by rfl⟩ : syracuseStep 1187539 = 1781309) B1781309
theorem B1187555 : Blo 1186410 1187555 := bstep (se 1 (by rfl) ⟨890666, by rfl⟩ : syracuseStep 1187555 = 1781333) B1781333
theorem B3006193 : Blo 1186410 3006193 := bstep (se 2 (by rfl) ⟨1127322, by rfl⟩ : syracuseStep 3006193 = 2254645) B2254645
theorem B1187571 : Blo 1186410 1187571 := bstep (se 1 (by rfl) ⟨890678, by rfl⟩ : syracuseStep 1187571 = 1781357) B1781357
theorem B1187587 : Blo 1186410 1187587 := bstep (se 1 (by rfl) ⟨890690, by rfl⟩ : syracuseStep 1187587 = 1781381) B1781381
theorem B2670353 : Blo 1186410 2670353 := bstep (se 2 (by rfl) ⟨1001382, by rfl⟩ : syracuseStep 2670353 = 2002765) B2002765
theorem B1187603 : Blo 1186410 1187603 := bstep (se 1 (by rfl) ⟨890702, by rfl⟩ : syracuseStep 1187603 = 1781405) B1781405
theorem B2670371 : Blo 1186410 2670371 := bstep (se 1 (by rfl) ⟨2002778, by rfl⟩ : syracuseStep 2670371 = 4005557) B4005557
theorem B1187619 : Blo 1186410 1187619 := bstep (se 1 (by rfl) ⟨890714, by rfl⟩ : syracuseStep 1187619 = 1781429) B1781429
theorem B5414705 : Blo 1186410 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B1335091 : Blo 1186410 1335091 := bstep (se 1 (by rfl) ⟨1001318, by rfl⟩ : syracuseStep 1335091 = 2002637) B2002637
theorem B1187635 : Blo 1186410 1187635 := bstep (se 1 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 1187635 = 1781453) B1781453
theorem B1187651 : Blo 1186410 1187651 := bstep (se 1 (by rfl) ⟨890738, by rfl⟩ : syracuseStep 1187651 = 1781477) B1781477
theorem B14450501 : Blo 1186410 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B1187667 : Blo 1186410 1187667 := bstep (se 1 (by rfl) ⟨890750, by rfl⟩ : syracuseStep 1187667 = 1781501) B1781501
theorem B1187683 : Blo 1186410 1187683 := bstep (se 1 (by rfl) ⟨890762, by rfl⟩ : syracuseStep 1187683 = 1781525) B1781525
theorem B10149731 : Blo 1186410 10149731 := bstep (se 1 (by rfl) ⟨7612298, by rfl⟩ : syracuseStep 10149731 = 15224597) B15224597
theorem B4276081 : Blo 1186410 4276081 := bstep (se 2 (by rfl) ⟨1603530, by rfl⟩ : syracuseStep 4276081 = 3207061) B3207061
theorem B2408305 : Blo 1186410 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B1187699 : Blo 1186410 1187699 := bstep (se 1 (by rfl) ⟨890774, by rfl⟩ : syracuseStep 1187699 = 1781549) B1781549
theorem B3612529 : Blo 1186410 3612529 := bstep (se 2 (by rfl) ⟨1354698, by rfl⟩ : syracuseStep 3612529 = 2709397) B2709397
theorem B3383153 : Blo 1186410 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B1187715 : Blo 1186410 1187715 := bstep (se 1 (by rfl) ⟨890786, by rfl⟩ : syracuseStep 1187715 = 1781573) B1781573
theorem B4005773 : Blo 1186410 4005773 := bstep (se 3 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 4005773 = 1502165) B1502165
theorem B1187731 : Blo 1186410 1187731 := bstep (se 1 (by rfl) ⟨890798, by rfl⟩ : syracuseStep 1187731 = 1781597) B1781597
theorem B1187747 : Blo 1186410 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B1187763 : Blo 1186410 1187763 := bstep (se 1 (by rfl) ⟨890822, by rfl⟩ : syracuseStep 1187763 = 1781645) B1781645
theorem B1335235 : Blo 1186410 1335235 := bstep (se 1 (by rfl) ⟨1001426, by rfl⟩ : syracuseStep 1335235 = 2002853) B2002853
theorem B4005827 : Blo 1186410 4005827 := bstep (se 1 (by rfl) ⟨3004370, by rfl⟩ : syracuseStep 4005827 = 6008741) B6008741
theorem B1187779 : Blo 1186410 1187779 := bstep (se 1 (by rfl) ⟨890834, by rfl⟩ : syracuseStep 1187779 = 1781669) B1781669
theorem B2031569 : Blo 1186410 2031569 := bstep (se 2 (by rfl) ⟨761838, by rfl⟩ : syracuseStep 2031569 = 1523677) B1523677
theorem B1187795 : Blo 1186410 1187795 := bstep (se 1 (by rfl) ⟨890846, by rfl⟩ : syracuseStep 1187795 = 1781693) B1781693
theorem B1187811 : Blo 1186410 1187811 := bstep (se 1 (by rfl) ⟨890858, by rfl⟩ : syracuseStep 1187811 = 1781717) B1781717
theorem B13533155 : Blo 1186410 13533155 := bstep (se 1 (by rfl) ⟨10149866, by rfl⟩ : syracuseStep 13533155 = 20299733) B20299733
theorem B2252785 : Blo 1186410 2252785 := bstep (se 2 (by rfl) ⟨844794, by rfl⟩ : syracuseStep 2252785 = 1689589) B1689589
theorem B5070833 : Blo 1186410 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B1187827 : Blo 1186410 1187827 := bstep (se 1 (by rfl) ⟨890870, by rfl⟩ : syracuseStep 1187827 = 1781741) B1781741
theorem B1335307 : Blo 1186410 1335307 := bstep (se 1 (by rfl) ⟨1001480, by rfl⟩ : syracuseStep 1335307 = 2002961) B2002961
theorem B1187851 : Blo 1186410 1187851 := bstep (se 1 (by rfl) ⟨890888, by rfl⟩ : syracuseStep 1187851 = 1781777) B1781777
theorem B1187863 : Blo 1186410 1187863 := bstep (se 1 (by rfl) ⟨890897, by rfl⟩ : syracuseStep 1187863 = 1781795) B1781795
theorem B1187883 : Blo 1186410 1187883 := bstep (se 1 (by rfl) ⟨890912, by rfl⟩ : syracuseStep 1187883 = 1781825) B1781825
theorem B4505645 : Blo 1186410 4505645 := bstep (se 3 (by rfl) ⟨844808, by rfl⟩ : syracuseStep 4505645 = 1689617) B1689617
theorem B1187895 : Blo 1186410 1187895 := bstep (se 1 (by rfl) ⟨890921, by rfl⟩ : syracuseStep 1187895 = 1781843) B1781843
theorem B1187915 : Blo 1186410 1187915 := bstep (se 1 (by rfl) ⟨890936, by rfl⟩ : syracuseStep 1187915 = 1781873) B1781873
theorem B1187927 : Blo 1186410 1187927 := bstep (se 1 (by rfl) ⟨890945, by rfl⟩ : syracuseStep 1187927 = 1781891) B1781891
theorem B1187947 : Blo 1186410 1187947 := bstep (se 1 (by rfl) ⟨890960, by rfl⟩ : syracuseStep 1187947 = 1781921) B1781921
theorem B1335415 : Blo 1186410 1335415 := bstep (se 1 (by rfl) ⟨1001561, by rfl⟩ : syracuseStep 1335415 = 2003123) B2003123
theorem B1187959 : Blo 1186410 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B2252929 : Blo 1186410 2252929 := bstep (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) B1689697
theorem B2670731 : Blo 1186410 2670731 := bstep (se 1 (by rfl) ⟨2003048, by rfl⟩ : syracuseStep 2670731 = 4006097) B4006097
theorem B1187979 : Blo 1186410 1187979 := bstep (se 1 (by rfl) ⟨890984, by rfl⟩ : syracuseStep 1187979 = 1781969) B1781969
theorem B1187991 : Blo 1186410 1187991 := bstep (se 1 (by rfl) ⟨890993, by rfl⟩ : syracuseStep 1187991 = 1781987) B1781987
theorem B1188011 : Blo 1186410 1188011 := bstep (se 1 (by rfl) ⟨891008, by rfl⟩ : syracuseStep 1188011 = 1782017) B1782017
theorem B1188023 : Blo 1186410 1188023 := bstep (se 1 (by rfl) ⟨891017, by rfl⟩ : syracuseStep 1188023 = 1782035) B1782035
theorem B2670785 : Blo 1186410 2670785 := bstep (se 2 (by rfl) ⟨1001544, by rfl⟩ : syracuseStep 2670785 = 2003089) B2003089
theorem B1188043 : Blo 1186410 1188043 := bstep (se 1 (by rfl) ⟨891032, by rfl⟩ : syracuseStep 1188043 = 1782065) B1782065
theorem B1188055 : Blo 1186410 1188055 := bstep (se 1 (by rfl) ⟨891041, by rfl⟩ : syracuseStep 1188055 = 1782083) B1782083
theorem B1188075 : Blo 1186410 1188075 := bstep (se 1 (by rfl) ⟨891056, by rfl⟩ : syracuseStep 1188075 = 1782113) B1782113
theorem B1188087 : Blo 1186410 1188087 := bstep (se 1 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 1188087 = 1782131) B1782131
theorem B1188107 : Blo 1186410 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B1188119 : Blo 1186410 1188119 := bstep (se 1 (by rfl) ⟨891089, by rfl⟩ : syracuseStep 1188119 = 1782179) B1782179
theorem B1335595 : Blo 1186410 1335595 := bstep (se 1 (by rfl) ⟨1001696, by rfl⟩ : syracuseStep 1335595 = 2003393) B2003393
theorem B1188139 : Blo 1186410 1188139 := bstep (se 1 (by rfl) ⟨891104, by rfl⟩ : syracuseStep 1188139 = 1782209) B1782209
theorem B1188151 : Blo 1186410 1188151 := bstep (se 1 (by rfl) ⟨891113, by rfl⟩ : syracuseStep 1188151 = 1782227) B1782227
theorem B1188171 : Blo 1186410 1188171 := bstep (se 1 (by rfl) ⟨891128, by rfl⟩ : syracuseStep 1188171 = 1782257) B1782257
theorem B1188183 : Blo 1186410 1188183 := bstep (se 1 (by rfl) ⟨891137, by rfl⟩ : syracuseStep 1188183 = 1782275) B1782275
theorem B6013277 : Blo 1186410 6013277 := bstep (se 3 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 6013277 = 2254979) B2254979
theorem B1188203 : Blo 1186410 1188203 := bstep (se 1 (by rfl) ⟨891152, by rfl⟩ : syracuseStep 1188203 = 1782305) B1782305
theorem B1188215 : Blo 1186410 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B1188235 : Blo 1186410 1188235 := bstep (se 1 (by rfl) ⟨891176, by rfl⟩ : syracuseStep 1188235 = 1782353) B1782353
theorem B1335703 : Blo 1186410 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B1188247 : Blo 1186410 1188247 := bstep (se 1 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 1188247 = 1782371) B1782371
theorem B2671001 : Blo 1186410 2671001 := bstep (se 2 (by rfl) ⟨1001625, by rfl⟩ : syracuseStep 2671001 = 2003251) B2003251
theorem B1188267 : Blo 1186410 1188267 := bstep (se 1 (by rfl) ⟨891200, by rfl⟩ : syracuseStep 1188267 = 1782401) B1782401
theorem B1188279 : Blo 1186410 1188279 := bstep (se 1 (by rfl) ⟨891209, by rfl⟩ : syracuseStep 1188279 = 1782419) B1782419
theorem B2892235 : Blo 1186410 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B1188299 : Blo 1186410 1188299 := bstep (se 1 (by rfl) ⟨891224, by rfl⟩ : syracuseStep 1188299 = 1782449) B1782449
theorem B2253271 : Blo 1186410 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B1188311 : Blo 1186410 1188311 := bstep (se 1 (by rfl) ⟨891233, by rfl⟩ : syracuseStep 1188311 = 1782467) B1782467
theorem B1188331 : Blo 1186410 1188331 := bstep (se 1 (by rfl) ⟨891248, by rfl⟩ : syracuseStep 1188331 = 1782497) B1782497
theorem B2671091 : Blo 1186410 2671091 := bstep (se 1 (by rfl) ⟨2003318, by rfl⟩ : syracuseStep 2671091 = 4006637) B4006637
theorem B1188343 : Blo 1186410 1188343 := bstep (se 1 (by rfl) ⟨891257, by rfl⟩ : syracuseStep 1188343 = 1782515) B1782515
theorem B1188363 : Blo 1186410 1188363 := bstep (se 1 (by rfl) ⟨891272, by rfl⟩ : syracuseStep 1188363 = 1782545) B1782545
theorem B2671127 : Blo 1186410 2671127 := bstep (se 1 (by rfl) ⟨2003345, by rfl⟩ : syracuseStep 2671127 = 4006691) B4006691
theorem B1188375 : Blo 1186410 1188375 := bstep (se 1 (by rfl) ⟨891281, by rfl⟩ : syracuseStep 1188375 = 1782563) B1782563
theorem B1188395 : Blo 1186410 1188395 := bstep (se 1 (by rfl) ⟨891296, by rfl⟩ : syracuseStep 1188395 = 1782593) B1782593
theorem B1188407 : Blo 1186410 1188407 := bstep (se 1 (by rfl) ⟨891305, by rfl⟩ : syracuseStep 1188407 = 1782611) B1782611
theorem B19243595 : Blo 1186410 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B4006475 : Blo 1186410 4006475 := bstep (se 1 (by rfl) ⟨3004856, by rfl⟩ : syracuseStep 4006475 = 6009713) B6009713
theorem B1335883 : Blo 1186410 1335883 := bstep (se 1 (by rfl) ⟨1001912, by rfl⟩ : syracuseStep 1335883 = 2003825) B2003825
theorem B4817483 : Blo 1186410 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B4571741 : Blo 1186410 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B2253491 : Blo 1186410 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B1335991 : Blo 1186410 1335991 := bstep (se 1 (by rfl) ⟨1001993, by rfl⟩ : syracuseStep 1335991 = 2003987) B2003987
theorem B2671307 : Blo 1186410 2671307 := bstep (se 1 (by rfl) ⟨2003480, by rfl⟩ : syracuseStep 2671307 = 4006961) B4006961
theorem B3613405 : Blo 1186410 3613405 := bstep (se 3 (by rfl) ⟨677513, by rfl⟩ : syracuseStep 3613405 = 1355027) B1355027
theorem B2671361 : Blo 1186410 2671361 := bstep (se 2 (by rfl) ⟨1001760, by rfl⟩ : syracuseStep 2671361 = 2003521) B2003521
theorem B5415731 : Blo 1186410 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B5489473 : Blo 1186410 5489473 := bstep (se 2 (by rfl) ⟨2058552, by rfl⟩ : syracuseStep 5489473 = 4117105) B4117105
theorem B3007307 : Blo 1186410 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B4006745 : Blo 1186410 4006745 := bstep (se 2 (by rfl) ⟨1502529, by rfl⟩ : syracuseStep 4006745 = 3005059) B3005059
theorem B10150757 : Blo 1186410 10150757 := bstep (se 4 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 10150757 = 1903267) B1903267
theorem B1336171 : Blo 1186410 1336171 := bstep (se 1 (by rfl) ⟨1002128, by rfl⟩ : syracuseStep 1336171 = 2004257) B2004257
theorem B2253719 : Blo 1186410 2253719 := bstep (se 1 (by rfl) ⟨1690289, by rfl⟩ : syracuseStep 2253719 = 3380579) B3380579
theorem B3802049 : Blo 1186410 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B1336279 : Blo 1186410 1336279 := bstep (se 1 (by rfl) ⟨1002209, by rfl⟩ : syracuseStep 1336279 = 2004419) B2004419
theorem B2671577 : Blo 1186410 2671577 := bstep (se 2 (by rfl) ⟨1001841, by rfl⟩ : syracuseStep 2671577 = 2003683) B2003683
theorem B7611353 : Blo 1186410 7611353 := bstep (se 2 (by rfl) ⟨2854257, by rfl⟩ : syracuseStep 7611353 = 5708515) B5708515
theorem B23462873 : Blo 1186410 23462873 := bstep (se 2 (by rfl) ⟨8798577, by rfl⟩ : syracuseStep 23462873 = 17597155) B17597155
theorem B2139137 : Blo 1186410 2139137 := bstep (se 2 (by rfl) ⟨802176, by rfl⟩ : syracuseStep 2139137 = 1604353) B1604353
theorem B2671667 : Blo 1186410 2671667 := bstep (se 1 (by rfl) ⟨2003750, by rfl⟩ : syracuseStep 2671667 = 4007501) B4007501
theorem B2671703 : Blo 1186410 2671703 := bstep (se 1 (by rfl) ⟨2003777, by rfl⟩ : syracuseStep 2671703 = 4007555) B4007555
theorem B1336459 : Blo 1186410 1336459 := bstep (se 1 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 1336459 = 2004689) B2004689
theorem B2253977 : Blo 1186410 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B7603379 : Blo 1186410 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B4277465 : Blo 1186410 4277465 := bstep (se 2 (by rfl) ⟨1604049, by rfl⟩ : syracuseStep 4277465 = 3208099) B3208099
theorem B1336567 : Blo 1186410 1336567 := bstep (se 1 (by rfl) ⟨1002425, by rfl⟩ : syracuseStep 1336567 = 2004851) B2004851
theorem B5137667 : Blo 1186410 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B2671883 : Blo 1186410 2671883 := bstep (se 1 (by rfl) ⟨2003912, by rfl⟩ : syracuseStep 2671883 = 4007825) B4007825
theorem B2671937 : Blo 1186410 2671937 := bstep (se 2 (by rfl) ⟨1001976, by rfl⟩ : syracuseStep 2671937 = 2003953) B2003953
theorem B1336747 : Blo 1186410 1336747 := bstep (se 1 (by rfl) ⟨1002560, by rfl⟩ : syracuseStep 1336747 = 2005121) B2005121
theorem B4400563 : Blo 1186410 4400563 := bstep (se 1 (by rfl) ⟨3300422, by rfl⟩ : syracuseStep 4400563 = 6600845) B6600845
theorem B4507073 : Blo 1186410 4507073 := bstep (se 2 (by rfl) ⟨1690152, by rfl⟩ : syracuseStep 4507073 = 3380305) B3380305
theorem B5072321 : Blo 1186410 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B4007447 : Blo 1186410 4007447 := bstep (se 1 (by rfl) ⟨3005585, by rfl⟩ : syracuseStep 4007447 = 6011171) B6011171
theorem B1336855 : Blo 1186410 1336855 := bstep (se 1 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 1336855 = 2005283) B2005283
theorem B2672153 : Blo 1186410 2672153 := bstep (se 2 (by rfl) ⟨1002057, by rfl⟩ : syracuseStep 2672153 = 2004115) B2004115
theorem B7218733 : Blo 1186410 7218733 := bstep (se 3 (by rfl) ⟨1353512, by rfl⟩ : syracuseStep 7218733 = 2707025) B2707025
theorem B2254387 : Blo 1186410 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B5072473 : Blo 1186410 5072473 := bstep (se 2 (by rfl) ⟨1902177, by rfl⟩ : syracuseStep 5072473 = 3804355) B3804355
theorem B2672243 : Blo 1186410 2672243 := bstep (se 1 (by rfl) ⟨2004182, by rfl⟩ : syracuseStep 2672243 = 4008365) B4008365
theorem B2672279 : Blo 1186410 2672279 := bstep (se 1 (by rfl) ⟨2004209, by rfl⟩ : syracuseStep 2672279 = 4008419) B4008419
theorem B1427095 : Blo 1186410 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B4277939 : Blo 1186410 4277939 := bstep (se 1 (by rfl) ⟨3208454, by rfl⟩ : syracuseStep 4277939 = 6416909) B6416909
theorem B2893591 : Blo 1186410 2893591 := bstep (se 1 (by rfl) ⟨2170193, by rfl⟩ : syracuseStep 2893591 = 4340387) B4340387
theorem B2672459 : Blo 1186410 2672459 := bstep (se 1 (by rfl) ⟨2004344, by rfl⟩ : syracuseStep 2672459 = 4008689) B4008689
theorem B2672513 : Blo 1186410 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B1779659 : Blo 1186410 1779659 := bstep (se 1 (by rfl) ⟨1334744, by rfl⟩ : syracuseStep 1779659 = 2669489) B2669489
theorem B1779671 : Blo 1186410 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B1779737 : Blo 1186410 1779737 := bstep (se 2 (by rfl) ⟨667401, by rfl⟩ : syracuseStep 1779737 = 1334803) B1334803
theorem B2254873 : Blo 1186410 2254873 := bstep (se 2 (by rfl) ⟨845577, by rfl⟩ : syracuseStep 2254873 = 1691155) B1691155
theorem B4007987 : Blo 1186410 4007987 := bstep (se 1 (by rfl) ⟨3005990, by rfl⟩ : syracuseStep 4007987 = 6011981) B6011981
theorem B300394565 : Blo 1186410 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B2672729 : Blo 1186410 2672729 := bstep (se 2 (by rfl) ⟨1002273, by rfl⟩ : syracuseStep 2672729 = 2004547) B2004547
theorem B1779851 : Blo 1186410 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B1779863 : Blo 1186410 1779863 := bstep (se 1 (by rfl) ⟨1334897, by rfl⟩ : syracuseStep 1779863 = 2669795) B2669795
theorem B3254423 : Blo 1186410 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B9021617 : Blo 1186410 9021617 := bstep (se 2 (by rfl) ⟨3383106, by rfl⟩ : syracuseStep 9021617 = 6766213) B6766213
theorem B4810931 : Blo 1186410 4810931 := bstep (se 1 (by rfl) ⟨3608198, by rfl⟩ : syracuseStep 4810931 = 7216397) B7216397
theorem B2672819 : Blo 1186410 2672819 := bstep (se 1 (by rfl) ⟨2004614, by rfl⟩ : syracuseStep 2672819 = 4009229) B4009229
theorem B2672855 : Blo 1186410 2672855 := bstep (se 1 (by rfl) ⟨2004641, by rfl⟩ : syracuseStep 2672855 = 4009283) B4009283
theorem B1779929 : Blo 1186410 1779929 := bstep (se 2 (by rfl) ⟨667473, by rfl⟩ : syracuseStep 1779929 = 1334947) B1334947
theorem B1689817 : Blo 1186410 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B4008257 : Blo 1186410 4008257 := bstep (se 2 (by rfl) ⟨1503096, by rfl⟩ : syracuseStep 4008257 = 3006193) B3006193
theorem B1780043 : Blo 1186410 1780043 := bstep (se 1 (by rfl) ⟨1335032, by rfl⟩ : syracuseStep 1780043 = 2670065) B2670065
theorem B1780055 : Blo 1186410 1780055 := bstep (se 1 (by rfl) ⟨1335041, by rfl⟩ : syracuseStep 1780055 = 2670083) B2670083
theorem B2673035 : Blo 1186410 2673035 := bstep (se 1 (by rfl) ⟨2004776, by rfl⟩ : syracuseStep 2673035 = 4009553) B4009553
theorem B6015383 : Blo 1186410 6015383 := bstep (se 1 (by rfl) ⟨4511537, by rfl⟩ : syracuseStep 6015383 = 9023075) B9023075
theorem B1780121 : Blo 1186410 1780121 := bstep (se 2 (by rfl) ⟨667545, by rfl⟩ : syracuseStep 1780121 = 1335091) B1335091
theorem B2673089 : Blo 1186410 2673089 := bstep (se 2 (by rfl) ⟨1002408, by rfl⟩ : syracuseStep 2673089 = 2004817) B2004817
theorem B1780235 : Blo 1186410 1780235 := bstep (se 1 (by rfl) ⟨1335176, by rfl⟩ : syracuseStep 1780235 = 2670353) B2670353
theorem B1780247 : Blo 1186410 1780247 := bstep (se 1 (by rfl) ⟨1335185, by rfl⟩ : syracuseStep 1780247 = 2670371) B2670371
theorem B2255435 : Blo 1186410 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B1780313 : Blo 1186410 1780313 := bstep (se 2 (by rfl) ⟨667617, by rfl⟩ : syracuseStep 1780313 = 1335235) B1335235
theorem B12184157 : Blo 1186410 12184157 := bstep (se 3 (by rfl) ⟨2284529, by rfl⟩ : syracuseStep 12184157 = 4569059) B4569059
theorem B7604867 : Blo 1186410 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B1354379 : Blo 1186410 1354379 := bstep (se 1 (by rfl) ⟨1015784, by rfl⟩ : syracuseStep 1354379 = 2031569) B2031569
theorem B9022103 : Blo 1186410 9022103 := bstep (se 1 (by rfl) ⟨6766577, by rfl⟩ : syracuseStep 9022103 = 13533155) B13533155
theorem B2673305 : Blo 1186410 2673305 := bstep (se 2 (by rfl) ⟨1002489, by rfl⟩ : syracuseStep 2673305 = 2004979) B2004979
theorem B1780427 : Blo 1186410 1780427 := bstep (se 1 (by rfl) ⟨1335320, by rfl⟩ : syracuseStep 1780427 = 2670641) B2670641
theorem B1780439 : Blo 1186410 1780439 := bstep (se 1 (by rfl) ⟨1335329, by rfl⟩ : syracuseStep 1780439 = 2670659) B2670659
theorem B2673395 : Blo 1186410 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B2255617 : Blo 1186410 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B2673431 : Blo 1186410 2673431 := bstep (se 1 (by rfl) ⟨2005073, by rfl⟩ : syracuseStep 2673431 = 4010147) B4010147
theorem B1780505 : Blo 1186410 1780505 := bstep (se 2 (by rfl) ⟨667689, by rfl⟩ : syracuseStep 1780505 = 1335379) B1335379
theorem B10840877 : Blo 1186410 10840877 := bstep (se 3 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 10840877 = 4065329) B4065329
theorem B4008797 : Blo 1186410 4008797 := bstep (se 3 (by rfl) ⟨751649, by rfl⟩ : syracuseStep 4008797 = 1503299) B1503299
theorem B1780619 : Blo 1186410 1780619 := bstep (se 1 (by rfl) ⟨1335464, by rfl⟩ : syracuseStep 1780619 = 2670929) B2670929
theorem B4508561 : Blo 1186410 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B1780631 : Blo 1186410 1780631 := bstep (se 1 (by rfl) ⟨1335473, by rfl⟩ : syracuseStep 1780631 = 2670947) B2670947
theorem B2534323 : Blo 1186410 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B1502155 : Blo 1186410 1502155 := bstep (se 1 (by rfl) ⟨1126616, by rfl⟩ : syracuseStep 1502155 = 2253233) B2253233
theorem B2673611 : Blo 1186410 2673611 := bstep (se 1 (by rfl) ⟨2005208, by rfl⟩ : syracuseStep 2673611 = 4010417) B4010417
theorem B6007769 : Blo 1186410 6007769 := bstep (se 2 (by rfl) ⟨2252913, by rfl⟩ : syracuseStep 6007769 = 4505827) B4505827
theorem B1780697 : Blo 1186410 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B2673665 : Blo 1186410 2673665 := bstep (se 2 (by rfl) ⟨1002624, by rfl⟩ : syracuseStep 2673665 = 2005249) B2005249
theorem B1780811 : Blo 1186410 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B1780823 : Blo 1186410 1780823 := bstep (se 1 (by rfl) ⟨1335617, by rfl⟩ : syracuseStep 1780823 = 2671235) B2671235
theorem B1928281 : Blo 1186410 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B1780889 : Blo 1186410 1780889 := bstep (se 2 (by rfl) ⟨667833, by rfl⟩ : syracuseStep 1780889 = 1335667) B1335667
theorem B2673881 : Blo 1186410 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B1781003 : Blo 1186410 1781003 := bstep (se 1 (by rfl) ⟨1335752, by rfl⟩ : syracuseStep 1781003 = 2671505) B2671505
theorem B1781015 : Blo 1186410 1781015 := bstep (se 1 (by rfl) ⟨1335761, by rfl⟩ : syracuseStep 1781015 = 2671523) B2671523
theorem B1355063 : Blo 1186410 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B1781081 : Blo 1186410 1781081 := bstep (se 2 (by rfl) ⟨667905, by rfl⟩ : syracuseStep 1781081 = 1335811) B1335811
theorem B4509017 : Blo 1186410 4509017 := bstep (se 2 (by rfl) ⟨1690881, by rfl⟩ : syracuseStep 4509017 = 3381763) B3381763
theorem B3804509 : Blo 1186410 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B1781195 : Blo 1186410 1781195 := bstep (se 1 (by rfl) ⟨1335896, by rfl⟩ : syracuseStep 1781195 = 2671793) B2671793
theorem B1781207 : Blo 1186410 1781207 := bstep (se 1 (by rfl) ⟨1335905, by rfl⟩ : syracuseStep 1781207 = 2671811) B2671811
theorem B1781273 : Blo 1186410 1781273 := bstep (se 2 (by rfl) ⟨667977, by rfl⟩ : syracuseStep 1781273 = 1335955) B1335955
theorem B1928729 : Blo 1186410 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B4509229 : Blo 1186410 4509229 := bstep (se 3 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 4509229 = 1690961) B1690961
theorem B1781387 : Blo 1186410 1781387 := bstep (se 1 (by rfl) ⟨1336040, by rfl⟩ : syracuseStep 1781387 = 2672081) B2672081
theorem B1691275 : Blo 1186410 1691275 := bstep (se 1 (by rfl) ⟨1268456, by rfl⟩ : syracuseStep 1691275 = 2536913) B2536913
theorem B2002583 : Blo 1186410 2002583 := bstep (se 1 (by rfl) ⟨1501937, by rfl⟩ : syracuseStep 2002583 = 3003875) B3003875
theorem B1781399 : Blo 1186410 1781399 := bstep (se 1 (by rfl) ⟨1336049, by rfl⟩ : syracuseStep 1781399 = 2672099) B2672099
theorem B13528781 : Blo 1186410 13528781 := bstep (se 3 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 13528781 = 5073293) B5073293
theorem B3378905 : Blo 1186410 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B1781465 : Blo 1186410 1781465 := bstep (se 2 (by rfl) ⟨668049, by rfl⟩ : syracuseStep 1781465 = 1336099) B1336099
theorem B2002711 : Blo 1186410 2002711 := bstep (se 1 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 2002711 = 3004067) B3004067
theorem B1781579 : Blo 1186410 1781579 := bstep (se 1 (by rfl) ⟨1336184, by rfl⟩ : syracuseStep 1781579 = 2672369) B2672369
theorem B1781591 : Blo 1186410 1781591 := bstep (se 1 (by rfl) ⟨1336193, by rfl⟩ : syracuseStep 1781591 = 2672387) B2672387
theorem B4509533 : Blo 1186410 4509533 := bstep (se 3 (by rfl) ⟨845537, by rfl⟩ : syracuseStep 4509533 = 1691075) B1691075
theorem B6418277 : Blo 1186410 6418277 := bstep (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) B1203427
theorem B1503127 : Blo 1186410 1503127 := bstep (se 1 (by rfl) ⟨1127345, by rfl⟩ : syracuseStep 1503127 = 2254691) B2254691
theorem B1781657 : Blo 1186410 1781657 := bstep (se 2 (by rfl) ⟨668121, by rfl⟩ : syracuseStep 1781657 = 1336243) B1336243
theorem B1929113 : Blo 1186410 1929113 := bstep (se 2 (by rfl) ⟨723417, by rfl⟩ : syracuseStep 1929113 = 1446835) B1446835
theorem B14274481 : Blo 1186410 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B4009931 : Blo 1186410 4009931 := bstep (se 1 (by rfl) ⟨3007448, by rfl⟩ : syracuseStep 4009931 = 6014897) B6014897
theorem B2535383 : Blo 1186410 2535383 := bstep (se 1 (by rfl) ⟨1901537, by rfl⟩ : syracuseStep 2535383 = 3803075) B3803075
theorem B1781771 : Blo 1186410 1781771 := bstep (se 1 (by rfl) ⟨1336328, by rfl⟩ : syracuseStep 1781771 = 2672657) B2672657
theorem B1781783 : Blo 1186410 1781783 := bstep (se 1 (by rfl) ⟨1336337, by rfl⟩ : syracuseStep 1781783 = 2672675) B2672675
theorem B10137635 : Blo 1186410 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B1781849 : Blo 1186410 1781849 := bstep (se 2 (by rfl) ⟨668193, by rfl⟩ : syracuseStep 1781849 = 1336387) B1336387
theorem B18280541 : Blo 1186410 18280541 := bstep (se 3 (by rfl) ⟨3427601, by rfl⟩ : syracuseStep 18280541 = 6855203) B6855203
theorem B9621605 : Blo 1186410 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B2535553 : Blo 1186410 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B4280465 : Blo 1186410 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B1781963 : Blo 1186410 1781963 := bstep (se 1 (by rfl) ⟨1336472, by rfl⟩ : syracuseStep 1781963 = 2672945) B2672945
theorem B1781975 : Blo 1186410 1781975 := bstep (se 1 (by rfl) ⟨1336481, by rfl⟩ : syracuseStep 1781975 = 2672963) B2672963
theorem B4010201 : Blo 1186410 4010201 := bstep (se 2 (by rfl) ⟨1503825, by rfl⟩ : syracuseStep 4010201 = 3007651) B3007651
theorem B1782041 : Blo 1186410 1782041 := bstep (se 2 (by rfl) ⟨668265, by rfl⟩ : syracuseStep 1782041 = 1336531) B1336531
theorem B6762797 : Blo 1186410 6762797 := bstep (se 3 (by rfl) ⟨1268024, by rfl⟩ : syracuseStep 6762797 = 2536049) B2536049
theorem B2003339 : Blo 1186410 2003339 := bstep (se 1 (by rfl) ⟨1502504, by rfl⟩ : syracuseStep 2003339 = 3005009) B3005009
theorem B1782155 : Blo 1186410 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B1782167 : Blo 1186410 1782167 := bstep (se 1 (by rfl) ⟨1336625, by rfl⟩ : syracuseStep 1782167 = 2673251) B2673251
theorem B2535895 : Blo 1186410 2535895 := bstep (se 1 (by rfl) ⟨1901921, by rfl⟩ : syracuseStep 2535895 = 3803843) B3803843
theorem B1782233 : Blo 1186410 1782233 := bstep (se 2 (by rfl) ⟨668337, by rfl⟩ : syracuseStep 1782233 = 1336675) B1336675
theorem B2003467 : Blo 1186410 2003467 := bstep (se 1 (by rfl) ⟨1502600, by rfl⟩ : syracuseStep 2003467 = 3005201) B3005201
theorem B3379735 : Blo 1186410 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B6009389 : Blo 1186410 6009389 := bstep (se 3 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 6009389 = 2253521) B2253521
theorem B1782347 : Blo 1186410 1782347 := bstep (se 1 (by rfl) ⟨1336760, by rfl⟩ : syracuseStep 1782347 = 2673521) B2673521
theorem B1446487 : Blo 1186410 1446487 := bstep (se 1 (by rfl) ⟨1084865, by rfl⟩ : syracuseStep 1446487 = 2169731) B2169731
theorem B1782359 : Blo 1186410 1782359 := bstep (se 1 (by rfl) ⟨1336769, by rfl⟩ : syracuseStep 1782359 = 2673539) B2673539
theorem B2003609 : Blo 1186410 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B1782425 : Blo 1186410 1782425 := bstep (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) B1336819
theorem B1503947 : Blo 1186410 1503947 := bstep (se 1 (by rfl) ⟨1127960, by rfl⟩ : syracuseStep 1503947 = 2255921) B2255921
theorem B1782539 : Blo 1186410 1782539 := bstep (se 1 (by rfl) ⟨1336904, by rfl⟩ : syracuseStep 1782539 = 2673809) B2673809
theorem B10138385 : Blo 1186410 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B1782551 : Blo 1186410 1782551 := bstep (se 1 (by rfl) ⟨1336913, by rfl⟩ : syracuseStep 1782551 = 2673827) B2673827
theorem B2003737 : Blo 1186410 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B2405207 : Blo 1186410 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B5075891 : Blo 1186410 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B5411971 : Blo 1186410 5411971 := bstep (se 1 (by rfl) ⟨4058978, by rfl⟩ : syracuseStep 5411971 = 8117957) B8117957
theorem B3044531 : Blo 1186410 3044531 := bstep (se 1 (by rfl) ⟨2283398, by rfl⟩ : syracuseStep 3044531 = 4566797) B4566797
theorem B3609803 : Blo 1186410 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B2536715 : Blo 1186410 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B3003713 : Blo 1186410 3003713 := bstep (se 2 (by rfl) ⟨1126392, by rfl⟩ : syracuseStep 3003713 = 2252785) B2252785
theorem B3380555 : Blo 1186410 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2004311 : Blo 1186410 2004311 := bstep (se 1 (by rfl) ⟨1503233, by rfl⟩ : syracuseStep 2004311 = 3006467) B3006467
theorem B4568413 : Blo 1186410 4568413 := bstep (se 3 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 4568413 = 1713155) B1713155
theorem B4814225 : Blo 1186410 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B2004439 : Blo 1186410 2004439 := bstep (se 1 (by rfl) ⟨1503329, by rfl⟩ : syracuseStep 2004439 = 3006659) B3006659
theorem B13514201 : Blo 1186410 13514201 := bstep (se 2 (by rfl) ⟨5067825, by rfl⟩ : syracuseStep 13514201 = 10135651) B10135651
theorem B2405953 : Blo 1186410 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B2537075 : Blo 1186410 2537075 := bstep (se 1 (by rfl) ⟨1902806, by rfl⟩ : syracuseStep 2537075 = 3805613) B3805613
theorem B11417219 : Blo 1186410 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B3610291 : Blo 1186410 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B2283223 : Blo 1186410 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B5420765 : Blo 1186410 5420765 := bstep (se 3 (by rfl) ⟨1016393, by rfl⟩ : syracuseStep 5420765 = 2032787) B2032787
theorem B1267435 : Blo 1186410 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B6854465 : Blo 1186410 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B3004249 : Blo 1186410 3004249 := bstep (se 2 (by rfl) ⟨1126593, by rfl⟩ : syracuseStep 3004249 = 2253187) B2253187
theorem B131782709 : Blo 1186410 131782709 := bstep (se 5 (by rfl) ⟨6177314, by rfl⟩ : syracuseStep 131782709 = 12354629) B12354629
theorem B6420545 : Blo 1186410 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B21649477 : Blo 1186410 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B2005067 : Blo 1186410 2005067 := bstep (se 1 (by rfl) ⟨1503800, by rfl⟩ : syracuseStep 2005067 = 3007601) B3007601
theorem B4282541 : Blo 1186410 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B2005195 : Blo 1186410 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B14448901 : Blo 1186410 14448901 := bstep (se 4 (by rfl) ⟨1354584, by rfl⟩ : syracuseStep 14448901 = 2709169) B2709169
theorem B12351809 : Blo 1186410 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B3209537 : Blo 1186410 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B2005337 : Blo 1186410 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B4512131 : Blo 1186410 4512131 := bstep (se 1 (by rfl) ⟨3384098, by rfl⟩ : syracuseStep 4512131 = 6768197) B6768197
theorem B4512145 : Blo 1186410 4512145 := bstep (se 2 (by rfl) ⟨1692054, by rfl⟩ : syracuseStep 4512145 = 3384109) B3384109
theorem B1268183 : Blo 1186410 1268183 := bstep (se 1 (by rfl) ⟨951137, by rfl⟩ : syracuseStep 1268183 = 1902275) B1902275
theorem B4282841 : Blo 1186410 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B1186411 : Blo 1186410 1186411 := bstep (se 1 (by rfl) ⟨889808, by rfl⟩ : syracuseStep 1186411 = 1779617) B1779617
theorem B1186423 : Blo 1186410 1186423 := bstep (se 1 (by rfl) ⟨889817, by rfl⟩ : syracuseStep 1186423 = 1779635) B1779635
theorem B1186443 : Blo 1186410 1186443 := bstep (se 1 (by rfl) ⟨889832, by rfl⟩ : syracuseStep 1186443 = 1779665) B1779665
theorem B1186455 : Blo 1186410 1186455 := bstep (se 1 (by rfl) ⟨889841, by rfl⟩ : syracuseStep 1186455 = 1779683) B1779683
theorem B1186475 : Blo 1186410 1186475 := bstep (se 1 (by rfl) ⟨889856, by rfl⟩ : syracuseStep 1186475 = 1779713) B1779713
theorem B4004531 : Blo 1186410 4004531 := bstep (se 1 (by rfl) ⟨3003398, by rfl⟩ : syracuseStep 4004531 = 6006797) B6006797
theorem B1186487 : Blo 1186410 1186487 := bstep (se 1 (by rfl) ⟨889865, by rfl⟩ : syracuseStep 1186487 = 1779731) B1779731
theorem B1186507 : Blo 1186410 1186507 := bstep (se 1 (by rfl) ⟨889880, by rfl⟩ : syracuseStep 1186507 = 1779761) B1779761
theorem B1186519 : Blo 1186410 1186519 := bstep (se 1 (by rfl) ⟨889889, by rfl⟩ : syracuseStep 1186519 = 1779779) B1779779
theorem B10828505 : Blo 1186410 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B1186539 : Blo 1186410 1186539 := bstep (se 1 (by rfl) ⟨889904, by rfl⟩ : syracuseStep 1186539 = 1779809) B1779809
theorem B1186551 : Blo 1186410 1186551 := bstep (se 1 (by rfl) ⟨889913, by rfl⟩ : syracuseStep 1186551 = 1779827) B1779827
theorem B1186571 : Blo 1186410 1186571 := bstep (se 1 (by rfl) ⟨889928, by rfl⟩ : syracuseStep 1186571 = 1779857) B1779857
theorem B1186583 : Blo 1186410 1186583 := bstep (se 1 (by rfl) ⟨889937, by rfl⟩ : syracuseStep 1186583 = 1779875) B1779875
theorem B1186603 : Blo 1186410 1186603 := bstep (se 1 (by rfl) ⟨889952, by rfl⟩ : syracuseStep 1186603 = 1779905) B1779905
theorem B1186615 : Blo 1186410 1186615 := bstep (se 1 (by rfl) ⟨889961, by rfl⟩ : syracuseStep 1186615 = 1779923) B1779923
theorem B1186635 : Blo 1186410 1186635 := bstep (se 1 (by rfl) ⟨889976, by rfl⟩ : syracuseStep 1186635 = 1779953) B1779953
theorem B1186647 : Blo 1186410 1186647 := bstep (se 1 (by rfl) ⟨889985, by rfl⟩ : syracuseStep 1186647 = 1779971) B1779971
theorem B1186667 : Blo 1186410 1186667 := bstep (se 1 (by rfl) ⟨890000, by rfl⟩ : syracuseStep 1186667 = 1780001) B1780001
theorem B1186679 : Blo 1186410 1186679 := bstep (se 1 (by rfl) ⟨890009, by rfl⟩ : syracuseStep 1186679 = 1780019) B1780019
theorem B1186699 : Blo 1186410 1186699 := bstep (se 1 (by rfl) ⟨890024, by rfl⟩ : syracuseStep 1186699 = 1780049) B1780049
theorem B1186711 : Blo 1186410 1186711 := bstep (se 1 (by rfl) ⟨890033, by rfl⟩ : syracuseStep 1186711 = 1780067) B1780067
theorem B1186731 : Blo 1186410 1186731 := bstep (se 1 (by rfl) ⟨890048, by rfl⟩ : syracuseStep 1186731 = 1780097) B1780097
theorem B3005363 : Blo 1186410 3005363 := bstep (se 1 (by rfl) ⟨2254022, by rfl⟩ : syracuseStep 3005363 = 4508045) B4508045
theorem B1186743 : Blo 1186410 1186743 := bstep (se 1 (by rfl) ⟨890057, by rfl⟩ : syracuseStep 1186743 = 1780115) B1780115
theorem B4004801 : Blo 1186410 4004801 := bstep (se 2 (by rfl) ⟨1501800, by rfl⟩ : syracuseStep 4004801 = 3003601) B3003601
theorem B1186763 : Blo 1186410 1186763 := bstep (se 1 (by rfl) ⟨890072, by rfl⟩ : syracuseStep 1186763 = 1780145) B1780145
theorem B1186775 : Blo 1186410 1186775 := bstep (se 1 (by rfl) ⟨890081, by rfl⟩ : syracuseStep 1186775 = 1780163) B1780163
theorem B1186795 : Blo 1186410 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B1203179 : Blo 1186410 1203179 := bstep (se 1 (by rfl) ⟨902384, by rfl⟩ : syracuseStep 1203179 = 1804769) B1804769
theorem B1186807 : Blo 1186410 1186807 := bstep (se 1 (by rfl) ⟨890105, by rfl⟩ : syracuseStep 1186807 = 1780211) B1780211
theorem B2669579 : Blo 1186410 2669579 := bstep (se 1 (by rfl) ⟨2002184, by rfl⟩ : syracuseStep 2669579 = 4004369) B4004369
theorem B1186827 : Blo 1186410 1186827 := bstep (se 1 (by rfl) ⟨890120, by rfl⟩ : syracuseStep 1186827 = 1780241) B1780241
theorem B1186839 : Blo 1186410 1186839 := bstep (se 1 (by rfl) ⟨890129, by rfl⟩ : syracuseStep 1186839 = 1780259) B1780259
theorem B1186859 : Blo 1186410 1186859 := bstep (se 1 (by rfl) ⟨890144, by rfl⟩ : syracuseStep 1186859 = 1780289) B1780289
theorem B1186871 : Blo 1186410 1186871 := bstep (se 1 (by rfl) ⟨890153, by rfl⟩ : syracuseStep 1186871 = 1780307) B1780307
theorem B2669633 : Blo 1186410 2669633 := bstep (se 2 (by rfl) ⟨1001112, by rfl⟩ : syracuseStep 2669633 = 2002225) B2002225
theorem B1186891 : Blo 1186410 1186891 := bstep (se 1 (by rfl) ⟨890168, by rfl⟩ : syracuseStep 1186891 = 1780337) B1780337
theorem B1186903 : Blo 1186410 1186903 := bstep (se 1 (by rfl) ⟨890177, by rfl⟩ : syracuseStep 1186903 = 1780355) B1780355
theorem B1186923 : Blo 1186410 1186923 := bstep (se 1 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 1186923 = 1780385) B1780385
theorem B1186935 : Blo 1186410 1186935 := bstep (se 1 (by rfl) ⟨890201, by rfl⟩ : syracuseStep 1186935 = 1780403) B1780403
theorem B1186955 : Blo 1186410 1186955 := bstep (se 1 (by rfl) ⟨890216, by rfl⟩ : syracuseStep 1186955 = 1780433) B1780433
theorem B1186967 : Blo 1186410 1186967 := bstep (se 1 (by rfl) ⟨890225, by rfl⟩ : syracuseStep 1186967 = 1780451) B1780451
theorem B1186987 : Blo 1186410 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B1186999 : Blo 1186410 1186999 := bstep (se 1 (by rfl) ⟨890249, by rfl⟩ : syracuseStep 1186999 = 1780499) B1780499
theorem B1187019 : Blo 1186410 1187019 := bstep (se 1 (by rfl) ⟨890264, by rfl⟩ : syracuseStep 1187019 = 1780529) B1780529
theorem B1187031 : Blo 1186410 1187031 := bstep (se 1 (by rfl) ⟨890273, by rfl⟩ : syracuseStep 1187031 = 1780547) B1780547
theorem B3005657 : Blo 1186410 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B1187051 : Blo 1186410 1187051 := bstep (se 1 (by rfl) ⟨890288, by rfl⟩ : syracuseStep 1187051 = 1780577) B1780577
theorem B1187063 : Blo 1186410 1187063 := bstep (se 1 (by rfl) ⟨890297, by rfl⟩ : syracuseStep 1187063 = 1780595) B1780595
theorem B1187083 : Blo 1186410 1187083 := bstep (se 1 (by rfl) ⟨890312, by rfl⟩ : syracuseStep 1187083 = 1780625) B1780625
theorem B4504855 : Blo 1186410 4504855 := bstep (se 1 (by rfl) ⟨3378641, by rfl⟩ : syracuseStep 4504855 = 6757283) B6757283
theorem B1187095 : Blo 1186410 1187095 := bstep (se 1 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 1187095 = 1780643) B1780643
theorem B2669849 : Blo 1186410 2669849 := bstep (se 2 (by rfl) ⟨1001193, by rfl⟩ : syracuseStep 2669849 = 2002387) B2002387
theorem B1187115 : Blo 1186410 1187115 := bstep (se 1 (by rfl) ⟨890336, by rfl⟩ : syracuseStep 1187115 = 1780673) B1780673
theorem B1187127 : Blo 1186410 1187127 := bstep (se 1 (by rfl) ⟨890345, by rfl⟩ : syracuseStep 1187127 = 1780691) B1780691
theorem B1187147 : Blo 1186410 1187147 := bstep (se 1 (by rfl) ⟨890360, by rfl⟩ : syracuseStep 1187147 = 1780721) B1780721
theorem B1187159 : Blo 1186410 1187159 := bstep (se 1 (by rfl) ⟨890369, by rfl⟩ : syracuseStep 1187159 = 1780739) B1780739
theorem B5709149 : Blo 1186410 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B1187179 : Blo 1186410 1187179 := bstep (se 1 (by rfl) ⟨890384, by rfl⟩ : syracuseStep 1187179 = 1780769) B1780769
theorem B2669939 : Blo 1186410 2669939 := bstep (se 1 (by rfl) ⟨2002454, by rfl⟩ : syracuseStep 2669939 = 4004909) B4004909
theorem B1187191 : Blo 1186410 1187191 := bstep (se 1 (by rfl) ⟨890393, by rfl⟩ : syracuseStep 1187191 = 1780787) B1780787
theorem B1187211 : Blo 1186410 1187211 := bstep (se 1 (by rfl) ⟨890408, by rfl⟩ : syracuseStep 1187211 = 1780817) B1780817
theorem B2669975 : Blo 1186410 2669975 := bstep (se 1 (by rfl) ⟨2002481, by rfl⟩ : syracuseStep 2669975 = 4004963) B4004963
theorem B1187223 : Blo 1186410 1187223 := bstep (se 1 (by rfl) ⟨890417, by rfl⟩ : syracuseStep 1187223 = 1780835) B1780835
theorem B1187243 : Blo 1186410 1187243 := bstep (se 1 (by rfl) ⟨890432, by rfl⟩ : syracuseStep 1187243 = 1780865) B1780865
theorem B1187255 : Blo 1186410 1187255 := bstep (se 1 (by rfl) ⟨890441, by rfl⟩ : syracuseStep 1187255 = 1780883) B1780883
theorem B1334731 : Blo 1186410 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B1187275 : Blo 1186410 1187275 := bstep (se 1 (by rfl) ⟨890456, by rfl⟩ : syracuseStep 1187275 = 1780913) B1780913
theorem B1187287 : Blo 1186410 1187287 := bstep (se 1 (by rfl) ⟨890465, by rfl⟩ : syracuseStep 1187287 = 1780931) B1780931
theorem B4005341 : Blo 1186410 4005341 := bstep (se 3 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 4005341 = 1502003) B1502003
theorem B1187307 : Blo 1186410 1187307 := bstep (se 1 (by rfl) ⟨890480, by rfl⟩ : syracuseStep 1187307 = 1780961) B1780961
theorem B1187319 : Blo 1186410 1187319 := bstep (se 1 (by rfl) ⟨890489, by rfl⟩ : syracuseStep 1187319 = 1780979) B1780979
theorem B1187339 : Blo 1186410 1187339 := bstep (se 1 (by rfl) ⟨890504, by rfl⟩ : syracuseStep 1187339 = 1781009) B1781009
theorem B1187351 : Blo 1186410 1187351 := bstep (se 1 (by rfl) ⟨890513, by rfl⟩ : syracuseStep 1187351 = 1781027) B1781027
theorem B1187371 : Blo 1186410 1187371 := bstep (se 1 (by rfl) ⟨890528, by rfl⟩ : syracuseStep 1187371 = 1781057) B1781057
theorem B1334839 : Blo 1186410 1334839 := bstep (se 1 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 1334839 = 2002259) B2002259
theorem B1187383 : Blo 1186410 1187383 := bstep (se 1 (by rfl) ⟨890537, by rfl⟩ : syracuseStep 1187383 = 1781075) B1781075
theorem B2670155 : Blo 1186410 2670155 := bstep (se 1 (by rfl) ⟨2002616, by rfl⟩ : syracuseStep 2670155 = 4005233) B4005233
theorem B1187403 : Blo 1186410 1187403 := bstep (se 1 (by rfl) ⟨890552, by rfl⟩ : syracuseStep 1187403 = 1781105) B1781105
theorem B2285131 : Blo 1186410 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B1187415 : Blo 1186410 1187415 := bstep (se 1 (by rfl) ⟨890561, by rfl⟩ : syracuseStep 1187415 = 1781123) B1781123
theorem B1187435 : Blo 1186410 1187435 := bstep (se 1 (by rfl) ⟨890576, by rfl⟩ : syracuseStep 1187435 = 1781153) B1781153
theorem B1187447 : Blo 1186410 1187447 := bstep (se 1 (by rfl) ⟨890585, by rfl⟩ : syracuseStep 1187447 = 1781171) B1781171
theorem B1285751 : Blo 1186410 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B2670209 : Blo 1186410 2670209 := bstep (se 2 (by rfl) ⟨1001328, by rfl⟩ : syracuseStep 2670209 = 2002657) B2002657
theorem B1187467 : Blo 1186410 1187467 := bstep (se 1 (by rfl) ⟨890600, by rfl⟩ : syracuseStep 1187467 = 1781201) B1781201
theorem B1187479 : Blo 1186410 1187479 := bstep (se 1 (by rfl) ⟨890609, by rfl⟩ : syracuseStep 1187479 = 1781219) B1781219
theorem B1187499 : Blo 1186410 1187499 := bstep (se 1 (by rfl) ⟨890624, by rfl⟩ : syracuseStep 1187499 = 1781249) B1781249
theorem B10141361 : Blo 1186410 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B1187511 : Blo 1186410 1187511 := bstep (se 1 (by rfl) ⟨890633, by rfl⟩ : syracuseStep 1187511 = 1781267) B1781267
theorem B1187531 : Blo 1186410 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B1187543 : Blo 1186410 1187543 := bstep (se 1 (by rfl) ⟨890657, by rfl⟩ : syracuseStep 1187543 = 1781315) B1781315
theorem B3383005 : Blo 1186410 3383005 := bstep (se 3 (by rfl) ⟨634313, by rfl⟩ : syracuseStep 3383005 = 1268627) B1268627
theorem B1335019 : Blo 1186410 1335019 := bstep (se 1 (by rfl) ⟨1001264, by rfl⟩ : syracuseStep 1335019 = 2002529) B2002529
theorem B1187563 : Blo 1186410 1187563 := bstep (se 1 (by rfl) ⟨890672, by rfl⟩ : syracuseStep 1187563 = 1781345) B1781345
theorem B1187575 : Blo 1186410 1187575 := bstep (se 1 (by rfl) ⟨890681, by rfl⟩ : syracuseStep 1187575 = 1781363) B1781363
theorem B1187595 : Blo 1186410 1187595 := bstep (se 1 (by rfl) ⟨890696, by rfl⟩ : syracuseStep 1187595 = 1781393) B1781393
theorem B1187607 : Blo 1186410 1187607 := bstep (se 1 (by rfl) ⟨890705, by rfl⟩ : syracuseStep 1187607 = 1781411) B1781411
theorem B1187627 : Blo 1186410 1187627 := bstep (se 1 (by rfl) ⟨890720, by rfl⟩ : syracuseStep 1187627 = 1781441) B1781441
theorem B1187639 : Blo 1186410 1187639 := bstep (se 1 (by rfl) ⟨890729, by rfl⟩ : syracuseStep 1187639 = 1781459) B1781459
theorem B5701441 : Blo 1186410 5701441 := bstep (se 2 (by rfl) ⟨2138040, by rfl⟩ : syracuseStep 5701441 = 4276081) B4276081
theorem B3211073 : Blo 1186410 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B4816705 : Blo 1186410 4816705 := bstep (se 2 (by rfl) ⟨1806264, by rfl⟩ : syracuseStep 4816705 = 3612529) B3612529
theorem B1187659 : Blo 1186410 1187659 := bstep (se 1 (by rfl) ⟨890744, by rfl⟩ : syracuseStep 1187659 = 1781489) B1781489
theorem B1335127 : Blo 1186410 1335127 := bstep (se 1 (by rfl) ⟨1001345, by rfl⟩ : syracuseStep 1335127 = 2002691) B2002691
theorem B2670425 : Blo 1186410 2670425 := bstep (se 2 (by rfl) ⟨1001409, by rfl⟩ : syracuseStep 2670425 = 2002819) B2002819
theorem B1187671 : Blo 1186410 1187671 := bstep (se 1 (by rfl) ⟨890753, by rfl⟩ : syracuseStep 1187671 = 1781507) B1781507
theorem B1187691 : Blo 1186410 1187691 := bstep (se 1 (by rfl) ⟨890768, by rfl⟩ : syracuseStep 1187691 = 1781537) B1781537
theorem B1187703 : Blo 1186410 1187703 := bstep (se 1 (by rfl) ⟨890777, by rfl⟩ : syracuseStep 1187703 = 1781555) B1781555
theorem B9633667 : Blo 1186410 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B1187723 : Blo 1186410 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B5562263 : Blo 1186410 5562263 := bstep (se 1 (by rfl) ⟨4171697, by rfl⟩ : syracuseStep 5562263 = 8343395) B8343395
theorem B1187735 : Blo 1186410 1187735 := bstep (se 1 (by rfl) ⟨890801, by rfl⟩ : syracuseStep 1187735 = 1781603) B1781603
theorem B6766487 : Blo 1186410 6766487 := bstep (se 1 (by rfl) ⟨5074865, by rfl⟩ : syracuseStep 6766487 = 10149731) B10149731
theorem B1187755 : Blo 1186410 1187755 := bstep (se 1 (by rfl) ⟨890816, by rfl⟩ : syracuseStep 1187755 = 1781633) B1781633
theorem B2670515 : Blo 1186410 2670515 := bstep (se 1 (by rfl) ⟨2002886, by rfl⟩ : syracuseStep 2670515 = 4005773) B4005773
theorem B1187767 : Blo 1186410 1187767 := bstep (se 1 (by rfl) ⟨890825, by rfl⟩ : syracuseStep 1187767 = 1781651) B1781651
theorem B2252747 : Blo 1186410 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B1187787 : Blo 1186410 1187787 := bstep (se 1 (by rfl) ⟨890840, by rfl⟩ : syracuseStep 1187787 = 1781681) B1781681
theorem B2670551 : Blo 1186410 2670551 := bstep (se 1 (by rfl) ⟨2002913, by rfl⟩ : syracuseStep 2670551 = 4005827) B4005827
theorem B1187799 : Blo 1186410 1187799 := bstep (se 1 (by rfl) ⟨890849, by rfl⟩ : syracuseStep 1187799 = 1781699) B1781699
theorem B1187819 : Blo 1186410 1187819 := bstep (se 1 (by rfl) ⟨890864, by rfl⟩ : syracuseStep 1187819 = 1781729) B1781729
theorem B1286123 : Blo 1186410 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B1187831 : Blo 1186410 1187831 := bstep (se 1 (by rfl) ⟨890873, by rfl⟩ : syracuseStep 1187831 = 1781747) B1781747
theorem B1187847 : Blo 1186410 1187847 := bstep (se 1 (by rfl) ⟨890885, by rfl⟩ : syracuseStep 1187847 = 1781771) B1781771
theorem B1187855 : Blo 1186410 1187855 := bstep (se 1 (by rfl) ⟨890891, by rfl⟩ : syracuseStep 1187855 = 1781783) B1781783
theorem B6758423 : Blo 1186410 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B3006497 : Blo 1186410 3006497 := bstep (se 2 (by rfl) ⟨1127436, by rfl⟩ : syracuseStep 3006497 = 2254873) B2254873
theorem B1187899 : Blo 1186410 1187899 := bstep (se 1 (by rfl) ⟨890924, by rfl⟩ : syracuseStep 1187899 = 1781849) B1781849
theorem B6414403 : Blo 1186410 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B1187975 : Blo 1186410 1187975 := bstep (se 1 (by rfl) ⟨890981, by rfl⟩ : syracuseStep 1187975 = 1781963) B1781963
theorem B1187983 : Blo 1186410 1187983 := bstep (se 1 (by rfl) ⟨890987, by rfl⟩ : syracuseStep 1187983 = 1781975) B1781975
theorem B1188027 : Blo 1186410 1188027 := bstep (se 1 (by rfl) ⟨891020, by rfl⟩ : syracuseStep 1188027 = 1782041) B1782041
theorem B1335559 : Blo 1186410 1335559 := bstep (se 1 (by rfl) ⟨1001669, by rfl⟩ : syracuseStep 1335559 = 2003339) B2003339
theorem B1188103 : Blo 1186410 1188103 := bstep (se 1 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 1188103 = 1782155) B1782155
theorem B1188111 : Blo 1186410 1188111 := bstep (se 1 (by rfl) ⟨891083, by rfl⟩ : syracuseStep 1188111 = 1782167) B1782167
theorem B2253089 : Blo 1186410 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B1188155 : Blo 1186410 1188155 := bstep (se 1 (by rfl) ⟨891116, by rfl⟩ : syracuseStep 1188155 = 1782233) B1782233
theorem B4006259 : Blo 1186410 4006259 := bstep (se 1 (by rfl) ⟨3004694, by rfl⟩ : syracuseStep 4006259 = 6009389) B6009389
theorem B12829063 : Blo 1186410 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B2670983 : Blo 1186410 2670983 := bstep (se 1 (by rfl) ⟨2003237, by rfl⟩ : syracuseStep 2670983 = 4006475) B4006475
theorem B3211655 : Blo 1186410 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B1188231 : Blo 1186410 1188231 := bstep (se 1 (by rfl) ⟨891173, by rfl⟩ : syracuseStep 1188231 = 1782347) B1782347
theorem B1188239 : Blo 1186410 1188239 := bstep (se 1 (by rfl) ⟨891179, by rfl⟩ : syracuseStep 1188239 = 1782359) B1782359
theorem B3047827 : Blo 1186410 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B1335739 : Blo 1186410 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B1188283 : Blo 1186410 1188283 := bstep (se 1 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 1188283 = 1782425) B1782425
theorem B1188359 : Blo 1186410 1188359 := bstep (se 1 (by rfl) ⟨891269, by rfl⟩ : syracuseStep 1188359 = 1782539) B1782539
theorem B6758923 : Blo 1186410 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1188367 : Blo 1186410 1188367 := bstep (se 1 (by rfl) ⟨891275, by rfl⟩ : syracuseStep 1188367 = 1782551) B1782551
theorem B9626141 : Blo 1186410 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B2671163 : Blo 1186410 2671163 := bstep (se 1 (by rfl) ⟨2003372, by rfl⟩ : syracuseStep 2671163 = 4006745) B4006745
theorem B6767171 : Blo 1186410 6767171 := bstep (se 1 (by rfl) ⟨5075378, by rfl⟩ : syracuseStep 6767171 = 10150757) B10150757
theorem B3383927 : Blo 1186410 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B1426091 : Blo 1186410 1426091 := bstep (se 1 (by rfl) ⟨1069568, by rfl⟩ : syracuseStep 1426091 = 2139137) B2139137
theorem B2671289 : Blo 1186410 2671289 := bstep (se 2 (by rfl) ⟨1001733, by rfl⟩ : syracuseStep 2671289 = 2003467) B2003467
theorem B4506313 : Blo 1186410 4506313 := bstep (se 2 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 4506313 = 3379735) B3379735
theorem B2851643 : Blo 1186410 2851643 := bstep (se 1 (by rfl) ⟨2138732, by rfl⟩ : syracuseStep 2851643 = 4277465) B4277465
theorem B3613501 : Blo 1186410 3613501 := bstep (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) B1355063
theorem B3425111 : Blo 1186410 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B1336207 : Blo 1186410 1336207 := bstep (se 1 (by rfl) ⟨1002155, by rfl⟩ : syracuseStep 1336207 = 2004311) B2004311
theorem B4817873 : Blo 1186410 4817873 := bstep (se 2 (by rfl) ⟨1806702, by rfl⟩ : syracuseStep 4817873 = 3613405) B3613405
theorem B3007489 : Blo 1186410 3007489 := bstep (se 2 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 3007489 = 2255617) B2255617
theorem B2671631 : Blo 1186410 2671631 := bstep (se 1 (by rfl) ⟨2003723, by rfl⟩ : syracuseStep 2671631 = 4007447) B4007447
theorem B2671649 : Blo 1186410 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B7611479 : Blo 1186410 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B3613843 : Blo 1186410 3613843 := bstep (se 1 (by rfl) ⟨2710382, by rfl⟩ : syracuseStep 3613843 = 5420765) B5420765
theorem B11420909 : Blo 1186410 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B2671991 : Blo 1186410 2671991 := bstep (se 1 (by rfl) ⟨2003993, by rfl⟩ : syracuseStep 2671991 = 4007987) B4007987
theorem B200263043 : Blo 1186410 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B1336711 : Blo 1186410 1336711 := bstep (se 1 (by rfl) ⟨1002533, by rfl⟩ : syracuseStep 1336711 = 2005067) B2005067
theorem B6014411 : Blo 1186410 6014411 := bstep (se 1 (by rfl) ⟨4510808, by rfl⟩ : syracuseStep 6014411 = 9021617) B9021617
theorem B2139691 : Blo 1186410 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B2672171 : Blo 1186410 2672171 := bstep (se 1 (by rfl) ⟨2004128, by rfl⟩ : syracuseStep 2672171 = 4008257) B4008257
theorem B1336891 : Blo 1186410 1336891 := bstep (se 1 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 1336891 = 2005337) B2005337
theorem B3008087 : Blo 1186410 3008087 := bstep (se 1 (by rfl) ⟨2256065, by rfl⟩ : syracuseStep 3008087 = 4512131) B4512131
theorem B6006473 : Blo 1186410 6006473 := bstep (se 2 (by rfl) ⟨2252427, by rfl⟩ : syracuseStep 6006473 = 4504855) B4504855
theorem B6014735 : Blo 1186410 6014735 := bstep (se 1 (by rfl) ⟨4511051, by rfl⟩ : syracuseStep 6014735 = 9022103) B9022103
theorem B7219003 : Blo 1186410 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B7227251 : Blo 1186410 7227251 := bstep (se 1 (by rfl) ⟨5420438, by rfl⟩ : syracuseStep 7227251 = 10840877) B10840877
theorem B2672531 : Blo 1186410 2672531 := bstep (se 1 (by rfl) ⟨2004398, by rfl⟩ : syracuseStep 2672531 = 4008797) B4008797
theorem B5867417 : Blo 1186410 5867417 := bstep (se 2 (by rfl) ⟨2200281, by rfl⟩ : syracuseStep 5867417 = 4400563) B4400563
theorem B1779641 : Blo 1186410 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B2672585 : Blo 1186410 2672585 := bstep (se 2 (by rfl) ⟨1002219, by rfl⟩ : syracuseStep 2672585 = 2004439) B2004439
theorem B1779719 : Blo 1186410 1779719 := bstep (se 1 (by rfl) ⟨1334789, by rfl⟩ : syracuseStep 1779719 = 2669579) B2669579
theorem B1779755 : Blo 1186410 1779755 := bstep (se 1 (by rfl) ⟨1334816, by rfl⟩ : syracuseStep 1779755 = 2669633) B2669633
theorem B1779785 : Blo 1186410 1779785 := bstep (se 2 (by rfl) ⟨667419, by rfl⟩ : syracuseStep 1779785 = 1334839) B1334839
theorem B2255033 : Blo 1186410 2255033 := bstep (se 2 (by rfl) ⟨845637, by rfl⟩ : syracuseStep 2255033 = 1691275) B1691275
theorem B1779899 : Blo 1186410 1779899 := bstep (se 1 (by rfl) ⟨1334924, by rfl⟩ : syracuseStep 1779899 = 2669849) B2669849
theorem B1902793 : Blo 1186410 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B1779959 : Blo 1186410 1779959 := bstep (se 1 (by rfl) ⟨1334969, by rfl⟩ : syracuseStep 1779959 = 2669939) B2669939
theorem B1779983 : Blo 1186410 1779983 := bstep (se 1 (by rfl) ⟨1334987, by rfl⟩ : syracuseStep 1779983 = 2669975) B2669975
theorem B1780025 : Blo 1186410 1780025 := bstep (se 2 (by rfl) ⟨667509, by rfl⟩ : syracuseStep 1780025 = 1335019) B1335019
theorem B1689913 : Blo 1186410 1689913 := bstep (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) B1267435
theorem B1780103 : Blo 1186410 1780103 := bstep (se 1 (by rfl) ⟨1335077, by rfl⟩ : syracuseStep 1780103 = 2670155) B2670155
theorem B1780139 : Blo 1186410 1780139 := bstep (se 1 (by rfl) ⟨1335104, by rfl⟩ : syracuseStep 1780139 = 2670209) B2670209
theorem B1780169 : Blo 1186410 1780169 := bstep (se 2 (by rfl) ⟨667563, by rfl⟩ : syracuseStep 1780169 = 1335127) B1335127
theorem B6760907 : Blo 1186410 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B2140715 : Blo 1186410 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B1780283 : Blo 1186410 1780283 := bstep (se 1 (by rfl) ⟨1335212, by rfl⟩ : syracuseStep 1780283 = 2670425) B2670425
theorem B19032641 : Blo 1186410 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B4278851 : Blo 1186410 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B1780343 : Blo 1186410 1780343 := bstep (se 1 (by rfl) ⟨1335257, by rfl⟩ : syracuseStep 1780343 = 2670515) B2670515
theorem B1501831 : Blo 1186410 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B2673287 : Blo 1186410 2673287 := bstep (se 1 (by rfl) ⟨2004965, by rfl⟩ : syracuseStep 2673287 = 4009931) B4009931
theorem B1780367 : Blo 1186410 1780367 := bstep (se 1 (by rfl) ⟨1335275, by rfl⟩ : syracuseStep 1780367 = 2670551) B2670551
theorem B1690255 : Blo 1186410 1690255 := bstep (se 1 (by rfl) ⟨1267691, by rfl⟩ : syracuseStep 1690255 = 2535383) B2535383
theorem B1780409 : Blo 1186410 1780409 := bstep (se 2 (by rfl) ⟨667653, by rfl⟩ : syracuseStep 1780409 = 1335307) B1335307
theorem B1780487 : Blo 1186410 1780487 := bstep (se 1 (by rfl) ⟨1335365, by rfl⟩ : syracuseStep 1780487 = 2670731) B2670731
theorem B2853643 : Blo 1186410 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B1780523 : Blo 1186410 1780523 := bstep (se 1 (by rfl) ⟨1335392, by rfl⟩ : syracuseStep 1780523 = 2670785) B2670785
theorem B2673467 : Blo 1186410 2673467 := bstep (se 1 (by rfl) ⟨2005100, by rfl⟩ : syracuseStep 2673467 = 4010201) B4010201
theorem B1780553 : Blo 1186410 1780553 := bstep (se 2 (by rfl) ⟨667707, by rfl⟩ : syracuseStep 1780553 = 1335415) B1335415
theorem B4508531 : Blo 1186410 4508531 := bstep (se 1 (by rfl) ⟨3381398, by rfl⟩ : syracuseStep 4508531 = 6762797) B6762797
theorem B4008851 : Blo 1186410 4008851 := bstep (se 1 (by rfl) ⟨3006638, by rfl⟩ : syracuseStep 4008851 = 6013277) B6013277
theorem B2673593 : Blo 1186410 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B1780667 : Blo 1186410 1780667 := bstep (se 1 (by rfl) ⟨1335500, by rfl⟩ : syracuseStep 1780667 = 2671001) B2671001
theorem B1780727 : Blo 1186410 1780727 := bstep (se 1 (by rfl) ⟨1335545, by rfl⟩ : syracuseStep 1780727 = 2671091) B2671091
theorem B1780751 : Blo 1186410 1780751 := bstep (se 1 (by rfl) ⟨1335563, by rfl⟩ : syracuseStep 1780751 = 2671127) B2671127
theorem B1780793 : Blo 1186410 1780793 := bstep (se 2 (by rfl) ⟨667797, by rfl⟩ : syracuseStep 1780793 = 1335595) B1335595
theorem B8678461 : Blo 1186410 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B1502327 : Blo 1186410 1502327 := bstep (se 1 (by rfl) ⟨1126745, by rfl⟩ : syracuseStep 1502327 = 2253491) B2253491
theorem B1780871 : Blo 1186410 1780871 := bstep (se 1 (by rfl) ⟨1335653, by rfl⟩ : syracuseStep 1780871 = 2671307) B2671307
theorem B1780907 : Blo 1186410 1780907 := bstep (se 1 (by rfl) ⟨1335680, by rfl⟩ : syracuseStep 1780907 = 2671361) B2671361
theorem B6016193 : Blo 1186410 6016193 := bstep (se 2 (by rfl) ⟨2256072, by rfl⟩ : syracuseStep 6016193 = 4512145) B4512145
theorem B1780937 : Blo 1186410 1780937 := bstep (se 2 (by rfl) ⟨667851, by rfl⟩ : syracuseStep 1780937 = 1335703) B1335703
theorem B1502479 : Blo 1186410 1502479 := bstep (se 1 (by rfl) ⟨1126859, by rfl⟩ : syracuseStep 1502479 = 2253719) B2253719
theorem B2534699 : Blo 1186410 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B1781051 : Blo 1186410 1781051 := bstep (se 1 (by rfl) ⟨1335788, by rfl⟩ : syracuseStep 1781051 = 2671577) B2671577
theorem B5074235 : Blo 1186410 5074235 := bstep (se 1 (by rfl) ⟨3805676, by rfl⟩ : syracuseStep 5074235 = 7611353) B7611353
theorem B1781111 : Blo 1186410 1781111 := bstep (se 1 (by rfl) ⟨1335833, by rfl⟩ : syracuseStep 1781111 = 2671667) B2671667
theorem B1781135 : Blo 1186410 1781135 := bstep (se 1 (by rfl) ⟨1335851, by rfl⟩ : syracuseStep 1781135 = 2671703) B2671703
theorem B1781177 : Blo 1186410 1781177 := bstep (se 2 (by rfl) ⟨667941, by rfl⟩ : syracuseStep 1781177 = 1335883) B1335883
theorem B1502651 : Blo 1186410 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B1781255 : Blo 1186410 1781255 := bstep (se 1 (by rfl) ⟨1335941, by rfl⟩ : syracuseStep 1781255 = 2671883) B2671883
theorem B9014813 : Blo 1186410 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B2002475 : Blo 1186410 2002475 := bstep (se 1 (by rfl) ⟨1501856, by rfl⟩ : syracuseStep 2002475 = 3003713) B3003713
theorem B1781291 : Blo 1186410 1781291 := bstep (se 1 (by rfl) ⟨1335968, by rfl⟩ : syracuseStep 1781291 = 2671937) B2671937
theorem B1781321 : Blo 1186410 1781321 := bstep (se 2 (by rfl) ⟨667995, by rfl⟩ : syracuseStep 1781321 = 1335991) B1335991
theorem B10145357 : Blo 1186410 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B1781435 : Blo 1186410 1781435 := bstep (se 1 (by rfl) ⟨1336076, by rfl⟩ : syracuseStep 1781435 = 2672153) B2672153
theorem B1001082581 : Blo 1186410 1001082581 := bstep (se 7 (by rfl) ⟨11731436, by rfl⟩ : syracuseStep 1001082581 = 23462873) B23462873
theorem B1781495 : Blo 1186410 1781495 := bstep (se 1 (by rfl) ⟨1336121, by rfl⟩ : syracuseStep 1781495 = 2672243) B2672243
theorem B1691383 : Blo 1186410 1691383 := bstep (se 1 (by rfl) ⟨1268537, by rfl⟩ : syracuseStep 1691383 = 2537075) B2537075
theorem B7319297 : Blo 1186410 7319297 := bstep (se 2 (by rfl) ⟨2744736, by rfl⟩ : syracuseStep 7319297 = 5489473) B5489473
theorem B1781519 : Blo 1186410 1781519 := bstep (se 1 (by rfl) ⟨1336139, by rfl⟩ : syracuseStep 1781519 = 2672279) B2672279
theorem B1781561 : Blo 1186410 1781561 := bstep (se 2 (by rfl) ⟨668085, by rfl⟩ : syracuseStep 1781561 = 1336171) B1336171
theorem B1781639 : Blo 1186410 1781639 := bstep (se 1 (by rfl) ⟨1336229, by rfl⟩ : syracuseStep 1781639 = 2672459) B2672459
theorem B3379097 : Blo 1186410 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B1781675 : Blo 1186410 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B2002873 : Blo 1186410 2002873 := bstep (se 2 (by rfl) ⟨751077, by rfl⟩ : syracuseStep 2002873 = 1502155) B1502155
theorem B1781705 : Blo 1186410 1781705 := bstep (se 2 (by rfl) ⟨668139, by rfl⟩ : syracuseStep 1781705 = 1336279) B1336279
theorem B87855139 : Blo 1186410 87855139 := bstep (se 1 (by rfl) ⟨65891354, by rfl⟩ : syracuseStep 87855139 = 131782709) B131782709
theorem B4280363 : Blo 1186410 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B1781819 : Blo 1186410 1781819 := bstep (se 1 (by rfl) ⟨1336364, by rfl⟩ : syracuseStep 1781819 = 2672729) B2672729
theorem B2855027 : Blo 1186410 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B3207287 : Blo 1186410 3207287 := bstep (se 1 (by rfl) ⟨2405465, by rfl⟩ : syracuseStep 3207287 = 4810931) B4810931
theorem B1781879 : Blo 1186410 1781879 := bstep (se 1 (by rfl) ⟨1336409, by rfl⟩ : syracuseStep 1781879 = 2672819) B2672819
theorem B1781903 : Blo 1186410 1781903 := bstep (se 1 (by rfl) ⟨1336427, by rfl⟩ : syracuseStep 1781903 = 2672855) B2672855
theorem B1781945 : Blo 1186410 1781945 := bstep (se 2 (by rfl) ⟨668229, by rfl⟩ : syracuseStep 1781945 = 1336459) B1336459
theorem B1782023 : Blo 1186410 1782023 := bstep (se 1 (by rfl) ⟨1336517, by rfl⟩ : syracuseStep 1782023 = 2673035) B2673035
theorem B4010255 : Blo 1186410 4010255 := bstep (se 1 (by rfl) ⟨3007691, by rfl⟩ : syracuseStep 4010255 = 6015383) B6015383
theorem B1782059 : Blo 1186410 1782059 := bstep (se 1 (by rfl) ⟨1336544, by rfl⟩ : syracuseStep 1782059 = 2673089) B2673089
theorem B3428669 : Blo 1186410 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B1782089 : Blo 1186410 1782089 := bstep (se 2 (by rfl) ⟨668283, by rfl⟩ : syracuseStep 1782089 = 1336567) B1336567
theorem B1503623 : Blo 1186410 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B8122771 : Blo 1186410 8122771 := bstep (se 1 (by rfl) ⟨6092078, by rfl⟩ : syracuseStep 8122771 = 12184157) B12184157
theorem B1782203 : Blo 1186410 1782203 := bstep (se 1 (by rfl) ⟨1336652, by rfl⟩ : syracuseStep 1782203 = 2673305) B2673305
theorem B6091217 : Blo 1186410 6091217 := bstep (se 2 (by rfl) ⟨2284206, by rfl⟩ : syracuseStep 6091217 = 4568413) B4568413
theorem B11407837 : Blo 1186410 11407837 := bstep (se 3 (by rfl) ⟨2138969, by rfl⟩ : syracuseStep 11407837 = 4277939) B4277939
theorem B1782263 : Blo 1186410 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B1782287 : Blo 1186410 1782287 := bstep (se 1 (by rfl) ⟨1336715, by rfl⟩ : syracuseStep 1782287 = 2673431) B2673431
theorem B4010525 : Blo 1186410 4010525 := bstep (se 3 (by rfl) ⟨751973, by rfl⟩ : syracuseStep 4010525 = 1503947) B1503947
theorem B1782329 : Blo 1186410 1782329 := bstep (se 2 (by rfl) ⟨668373, by rfl⟩ : syracuseStep 1782329 = 1336747) B1336747
theorem B2003575 : Blo 1186410 2003575 := bstep (se 1 (by rfl) ⟨1502681, by rfl⟩ : syracuseStep 2003575 = 3005363) B3005363
theorem B1782407 : Blo 1186410 1782407 := bstep (se 1 (by rfl) ⟨1336805, by rfl⟩ : syracuseStep 1782407 = 2673611) B2673611
theorem B1782443 : Blo 1186410 1782443 := bstep (se 1 (by rfl) ⟨1336832, by rfl⟩ : syracuseStep 1782443 = 2673665) B2673665
theorem B1782473 : Blo 1186410 1782473 := bstep (se 2 (by rfl) ⟨668427, by rfl⟩ : syracuseStep 1782473 = 1336855) B1336855
theorem B3207937 : Blo 1186410 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B6763297 : Blo 1186410 6763297 := bstep (se 2 (by rfl) ⟨2536236, by rfl⟩ : syracuseStep 6763297 = 5072473) B5072473
theorem B2003771 : Blo 1186410 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B1782587 : Blo 1186410 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B3806099 : Blo 1186410 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B4813721 : Blo 1186410 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B3044297 : Blo 1186410 3044297 := bstep (se 2 (by rfl) ⟨1141611, by rfl⟩ : syracuseStep 3044297 = 2283223) B2283223
theorem B4510673 : Blo 1186410 4510673 := bstep (se 2 (by rfl) ⟨1691502, by rfl⟩ : syracuseStep 4510673 = 3383005) B3383005
theorem B12833909 : Blo 1186410 12833909 := bstep (se 5 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 12833909 = 1203179) B1203179
theorem B2004169 : Blo 1186410 2004169 := bstep (se 2 (by rfl) ⟨751563, by rfl⟩ : syracuseStep 2004169 = 1503127) B1503127
theorem B3708175 : Blo 1186410 3708175 := bstep (se 1 (by rfl) ⟨2781131, by rfl⟩ : syracuseStep 3708175 = 5562263) B5562263
theorem B4510991 : Blo 1186410 4510991 := bstep (se 1 (by rfl) ⟨3383243, by rfl⟩ : syracuseStep 4510991 = 6766487) B6766487
theorem B3429661 : Blo 1186410 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B3003763 : Blo 1186410 3003763 := bstep (se 1 (by rfl) ⟨2252822, by rfl⟩ : syracuseStep 3003763 = 4505645) B4505645
theorem B12187027 : Blo 1186410 12187027 := bstep (se 1 (by rfl) ⟨9140270, by rfl⟩ : syracuseStep 12187027 = 18280541) B18280541
theorem B28865969 : Blo 1186410 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B3003905 : Blo 1186410 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B19265201 : Blo 1186410 19265201 := bstep (se 2 (by rfl) ⟨7224450, by rfl⟩ : syracuseStep 19265201 = 14448901) B14448901
theorem B7714597 : Blo 1186410 7714597 := bstep (se 4 (by rfl) ⟨723243, by rfl⟩ : syracuseStep 7714597 = 1446487) B1446487
theorem B3610487 : Blo 1186410 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B2004871 : Blo 1186410 2004871 := bstep (se 1 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 2004871 = 3007307) B3007307
theorem B1603471 : Blo 1186410 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B3856313 : Blo 1186410 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B3004361 : Blo 1186410 3004361 := bstep (se 2 (by rfl) ⟨1126635, by rfl⟩ : syracuseStep 3004361 = 2253271) B2253271
theorem B3381193 : Blo 1186410 3381193 := bstep (se 2 (by rfl) ⟨1267947, by rfl⟩ : syracuseStep 3381193 = 2535895) B2535895
theorem B13522949 : Blo 1186410 13522949 := bstep (se 4 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 13522949 = 2535553) B2535553
theorem B6764573 : Blo 1186410 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B2029687 : Blo 1186410 2029687 := bstep (se 1 (by rfl) ⟨1522265, by rfl⟩ : syracuseStep 2029687 = 3044531) B3044531
theorem B5068919 : Blo 1186410 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B32938157 : Blo 1186410 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B3209483 : Blo 1186410 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B3004715 : Blo 1186410 3004715 := bstep (se 1 (by rfl) ⟨2253536, by rfl⟩ : syracuseStep 3004715 = 4507073) B4507073
theorem B3381547 : Blo 1186410 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B9009467 : Blo 1186410 9009467 := bstep (se 1 (by rfl) ⟨6757100, by rfl⟩ : syracuseStep 9009467 = 13514201) B13514201
theorem B4569643 : Blo 1186410 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B3381821 : Blo 1186410 3381821 := bstep (se 3 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 3381821 = 1268183) B1268183
theorem B1186439 : Blo 1186410 1186439 := bstep (se 1 (by rfl) ⟨889829, by rfl⟩ : syracuseStep 1186439 = 1779659) B1779659
theorem B1186447 : Blo 1186410 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B1186491 : Blo 1186410 1186491 := bstep (se 1 (by rfl) ⟨889868, by rfl⟩ : syracuseStep 1186491 = 1779737) B1779737
theorem B5143277 : Blo 1186410 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B1186567 : Blo 1186410 1186567 := bstep (se 1 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 1186567 = 1779851) B1779851
theorem B1186575 : Blo 1186410 1186575 := bstep (se 1 (by rfl) ⟨889931, by rfl⟩ : syracuseStep 1186575 = 1779863) B1779863
theorem B2571041 : Blo 1186410 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B1186619 : Blo 1186410 1186619 := bstep (se 1 (by rfl) ⟨889964, by rfl⟩ : syracuseStep 1186619 = 1779929) B1779929
theorem B7215961 : Blo 1186410 7215961 := bstep (se 2 (by rfl) ⟨2705985, by rfl⟩ : syracuseStep 7215961 = 5411971) B5411971
theorem B1186695 : Blo 1186410 1186695 := bstep (se 1 (by rfl) ⟨890021, by rfl⟩ : syracuseStep 1186695 = 1780043) B1780043
theorem B1186703 : Blo 1186410 1186703 := bstep (se 1 (by rfl) ⟨890027, by rfl⟩ : syracuseStep 1186703 = 1780055) B1780055
theorem B1186747 : Blo 1186410 1186747 := bstep (se 1 (by rfl) ⟨890060, by rfl⟩ : syracuseStep 1186747 = 1780121) B1780121
theorem B1186823 : Blo 1186410 1186823 := bstep (se 1 (by rfl) ⟨890117, by rfl⟩ : syracuseStep 1186823 = 1780235) B1780235
theorem B1186831 : Blo 1186410 1186831 := bstep (se 1 (by rfl) ⟨890123, by rfl⟩ : syracuseStep 1186831 = 1780247) B1780247
theorem B3611677 : Blo 1186410 3611677 := bstep (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) B1354379
theorem B1186875 : Blo 1186410 1186875 := bstep (se 1 (by rfl) ⟨890156, by rfl⟩ : syracuseStep 1186875 = 1780313) B1780313
theorem B5069911 : Blo 1186410 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B2669687 : Blo 1186410 2669687 := bstep (se 1 (by rfl) ⟨2002265, by rfl⟩ : syracuseStep 2669687 = 4004531) B4004531
theorem B1186951 : Blo 1186410 1186951 := bstep (se 1 (by rfl) ⟨890213, by rfl⟩ : syracuseStep 1186951 = 1780427) B1780427
theorem B1186959 : Blo 1186410 1186959 := bstep (se 1 (by rfl) ⟨890219, by rfl⟩ : syracuseStep 1186959 = 1780439) B1780439
theorem B1187003 : Blo 1186410 1187003 := bstep (se 1 (by rfl) ⟨890252, by rfl⟩ : syracuseStep 1187003 = 1780505) B1780505
theorem B1187079 : Blo 1186410 1187079 := bstep (se 1 (by rfl) ⟨890309, by rfl⟩ : syracuseStep 1187079 = 1780619) B1780619
theorem B3005707 : Blo 1186410 3005707 := bstep (se 1 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 3005707 = 4508561) B4508561
theorem B1187087 : Blo 1186410 1187087 := bstep (se 1 (by rfl) ⟨890315, by rfl⟩ : syracuseStep 1187087 = 1780631) B1780631
theorem B2669867 : Blo 1186410 2669867 := bstep (se 1 (by rfl) ⟨2002400, by rfl⟩ : syracuseStep 2669867 = 4004801) B4004801
theorem B4005179 : Blo 1186410 4005179 := bstep (se 1 (by rfl) ⟨3003884, by rfl⟩ : syracuseStep 4005179 = 6007769) B6007769
theorem B1187131 : Blo 1186410 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B1187207 : Blo 1186410 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B1187215 : Blo 1186410 1187215 := bstep (se 1 (by rfl) ⟨890411, by rfl⟩ : syracuseStep 1187215 = 1780823) B1780823
theorem B9624977 : Blo 1186410 9624977 := bstep (se 2 (by rfl) ⟨3609366, by rfl⟩ : syracuseStep 9624977 = 7218733) B7218733
theorem B6012305 : Blo 1186410 6012305 := bstep (se 2 (by rfl) ⟨2254614, by rfl⟩ : syracuseStep 6012305 = 4509229) B4509229
theorem B3005849 : Blo 1186410 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B3046841 : Blo 1186410 3046841 := bstep (se 2 (by rfl) ⟨1142565, by rfl⟩ : syracuseStep 3046841 = 2285131) B2285131
theorem B1187259 : Blo 1186410 1187259 := bstep (se 1 (by rfl) ⟨890444, by rfl⟩ : syracuseStep 1187259 = 1780889) B1780889
theorem B1187335 : Blo 1186410 1187335 := bstep (se 1 (by rfl) ⟨890501, by rfl⟩ : syracuseStep 1187335 = 1781003) B1781003
theorem B1187343 : Blo 1186410 1187343 := bstep (se 1 (by rfl) ⟨890507, by rfl⟩ : syracuseStep 1187343 = 1781015) B1781015
theorem B1187387 : Blo 1186410 1187387 := bstep (se 1 (by rfl) ⟨890540, by rfl⟩ : syracuseStep 1187387 = 1781081) B1781081
theorem B3006011 : Blo 1186410 3006011 := bstep (se 1 (by rfl) ⟨2254508, by rfl⟩ : syracuseStep 3006011 = 4509017) B4509017
theorem B1187463 : Blo 1186410 1187463 := bstep (se 1 (by rfl) ⟨890597, by rfl⟩ : syracuseStep 1187463 = 1781195) B1781195
theorem B1187471 : Blo 1186410 1187471 := bstep (se 1 (by rfl) ⟨890603, by rfl⟩ : syracuseStep 1187471 = 1781207) B1781207
theorem B2670227 : Blo 1186410 2670227 := bstep (se 1 (by rfl) ⟨2002670, by rfl⟩ : syracuseStep 2670227 = 4005341) B4005341
theorem B1187515 : Blo 1186410 1187515 := bstep (se 1 (by rfl) ⟨890636, by rfl⟩ : syracuseStep 1187515 = 1781273) B1781273
theorem B2670281 : Blo 1186410 2670281 := bstep (se 2 (by rfl) ⟨1001355, by rfl⟩ : syracuseStep 2670281 = 2002711) B2002711
theorem B3858121 : Blo 1186410 3858121 := bstep (se 2 (by rfl) ⟨1446795, by rfl⟩ : syracuseStep 3858121 = 2893591) B2893591
theorem B7601921 : Blo 1186410 7601921 := bstep (se 2 (by rfl) ⟨2850720, by rfl⟩ : syracuseStep 7601921 = 5701441) B5701441
theorem B6422273 : Blo 1186410 6422273 := bstep (se 2 (by rfl) ⟨2408352, by rfl⟩ : syracuseStep 6422273 = 4816705) B4816705
theorem B1187591 : Blo 1186410 1187591 := bstep (se 1 (by rfl) ⟨890693, by rfl⟩ : syracuseStep 1187591 = 1781387) B1781387
theorem B1335055 : Blo 1186410 1335055 := bstep (se 1 (by rfl) ⟨1001291, by rfl⟩ : syracuseStep 1335055 = 2002583) B2002583
theorem B1187599 : Blo 1186410 1187599 := bstep (se 1 (by rfl) ⟨890699, by rfl⟩ : syracuseStep 1187599 = 1781399) B1781399
theorem B4005665 : Blo 1186410 4005665 := bstep (se 2 (by rfl) ⟨1502124, by rfl⟩ : syracuseStep 4005665 = 3004249) B3004249
theorem B9019187 : Blo 1186410 9019187 := bstep (se 1 (by rfl) ⟨6764390, by rfl⟩ : syracuseStep 9019187 = 13528781) B13528781
theorem B2252603 : Blo 1186410 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B1187643 : Blo 1186410 1187643 := bstep (se 1 (by rfl) ⟨890732, by rfl⟩ : syracuseStep 1187643 = 1781465) B1781465
theorem B12844889 : Blo 1186410 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B1187719 : Blo 1186410 1187719 := bstep (se 1 (by rfl) ⟨890789, by rfl⟩ : syracuseStep 1187719 = 1781579) B1781579
theorem B1187727 : Blo 1186410 1187727 := bstep (se 1 (by rfl) ⟨890795, by rfl⟩ : syracuseStep 1187727 = 1781591) B1781591
theorem B3006355 : Blo 1186410 3006355 := bstep (se 1 (by rfl) ⟨2254766, by rfl⟩ : syracuseStep 3006355 = 4509533) B4509533
theorem B1187771 : Blo 1186410 1187771 := bstep (se 1 (by rfl) ⟨890828, by rfl⟩ : syracuseStep 1187771 = 1781657) B1781657
theorem B1286075 : Blo 1186410 1286075 := bstep (se 1 (by rfl) ⟨964556, by rfl⟩ : syracuseStep 1286075 = 1929113) B1929113
theorem B4505615 : Blo 1186410 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B1187879 : Blo 1186410 1187879 := bstep (se 1 (by rfl) ⟨890909, by rfl⟩ : syracuseStep 1187879 = 1781819) B1781819
theorem B1187919 : Blo 1186410 1187919 := bstep (se 1 (by rfl) ⟨890939, by rfl⟩ : syracuseStep 1187919 = 1781879) B1781879
theorem B8552537 : Blo 1186410 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B1187935 : Blo 1186410 1187935 := bstep (se 1 (by rfl) ⟨890951, by rfl⟩ : syracuseStep 1187935 = 1781903) B1781903
theorem B1187963 : Blo 1186410 1187963 := bstep (se 1 (by rfl) ⟨890972, by rfl⟩ : syracuseStep 1187963 = 1781945) B1781945
theorem B1188015 : Blo 1186410 1188015 := bstep (se 1 (by rfl) ⟨891011, by rfl⟩ : syracuseStep 1188015 = 1782023) B1782023
theorem B1188039 : Blo 1186410 1188039 := bstep (se 1 (by rfl) ⟨891029, by rfl⟩ : syracuseStep 1188039 = 1782059) B1782059
theorem B1188059 : Blo 1186410 1188059 := bstep (se 1 (by rfl) ⟨891044, by rfl⟩ : syracuseStep 1188059 = 1782089) B1782089
theorem B2670839 : Blo 1186410 2670839 := bstep (se 1 (by rfl) ⟨2003129, by rfl⟩ : syracuseStep 2670839 = 4006259) B4006259
theorem B1188135 : Blo 1186410 1188135 := bstep (se 1 (by rfl) ⟨891101, by rfl⟩ : syracuseStep 1188135 = 1782203) B1782203
theorem B8552765 : Blo 1186410 8552765 := bstep (se 3 (by rfl) ⟨1603643, by rfl⟩ : syracuseStep 8552765 = 3207287) B3207287
theorem B13517117 : Blo 1186410 13517117 := bstep (se 3 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 13517117 = 5068919) B5068919
theorem B4006205 : Blo 1186410 4006205 := bstep (se 3 (by rfl) ⟨751163, by rfl⟩ : syracuseStep 4006205 = 1502327) B1502327
theorem B1188175 : Blo 1186410 1188175 := bstep (se 1 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 1188175 = 1782263) B1782263
theorem B1188191 : Blo 1186410 1188191 := bstep (se 1 (by rfl) ⟨891143, by rfl⟩ : syracuseStep 1188191 = 1782287) B1782287
theorem B1188219 : Blo 1186410 1188219 := bstep (se 1 (by rfl) ⟨891164, by rfl⟩ : syracuseStep 1188219 = 1782329) B1782329
theorem B1188271 : Blo 1186410 1188271 := bstep (se 1 (by rfl) ⟨891203, by rfl⟩ : syracuseStep 1188271 = 1782407) B1782407
theorem B1188295 : Blo 1186410 1188295 := bstep (se 1 (by rfl) ⟨891221, by rfl⟩ : syracuseStep 1188295 = 1782443) B1782443
theorem B1188315 : Blo 1186410 1188315 := bstep (se 1 (by rfl) ⟨891236, by rfl⟩ : syracuseStep 1188315 = 1782473) B1782473
theorem B17105417 : Blo 1186410 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B10830361 : Blo 1186410 10830361 := bstep (se 2 (by rfl) ⟨4061385, by rfl⟩ : syracuseStep 10830361 = 8122771) B8122771
theorem B4063769 : Blo 1186410 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B1335847 : Blo 1186410 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B1188391 : Blo 1186410 1188391 := bstep (se 1 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 1188391 = 1782587) B1782587
theorem B3007115 : Blo 1186410 3007115 := bstep (se 1 (by rfl) ⟨2255336, by rfl⟩ : syracuseStep 3007115 = 4510673) B4510673
theorem B3211915 : Blo 1186410 3211915 := bstep (se 1 (by rfl) ⟨2408936, by rfl⟩ : syracuseStep 3211915 = 4817873) B4817873
theorem B9011897 : Blo 1186410 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B6759197 : Blo 1186410 6759197 := bstep (se 3 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 6759197 = 2534699) B2534699
theorem B2671433 : Blo 1186410 2671433 := bstep (se 2 (by rfl) ⟨1001787, by rfl⟩ : syracuseStep 2671433 = 2003575) B2003575
theorem B9143117 : Blo 1186410 9143117 := bstep (se 3 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 9143117 = 3428669) B3428669
theorem B3007327 : Blo 1186410 3007327 := bstep (se 1 (by rfl) ⟨2255495, by rfl⟩ : syracuseStep 3007327 = 4510991) B4510991
theorem B2253673 : Blo 1186410 2253673 := bstep (se 2 (by rfl) ⟨845127, by rfl⟩ : syracuseStep 2253673 = 1690255) B1690255
theorem B19243979 : Blo 1186410 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B4277249 : Blo 1186410 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B4007069 : Blo 1186410 4007069 := bstep (se 3 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 4007069 = 1502651) B1502651
theorem B4818167 : Blo 1186410 4818167 := bstep (se 1 (by rfl) ⟨3613625, by rfl⟩ : syracuseStep 4818167 = 7227251) B7227251
theorem B6759881 : Blo 1186410 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B4818457 : Blo 1186410 4818457 := bstep (se 2 (by rfl) ⟨1806921, by rfl⟩ : syracuseStep 4818457 = 3613843) B3613843
theorem B6006311 : Blo 1186410 6006311 := bstep (se 1 (by rfl) ⟨4504733, by rfl⟩ : syracuseStep 6006311 = 9009467) B9009467
theorem B2672225 : Blo 1186410 2672225 := bstep (se 2 (by rfl) ⟨1002084, by rfl⟩ : syracuseStep 2672225 = 2004169) B2004169
theorem B9012869 : Blo 1186410 9012869 := bstep (se 4 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 9012869 = 1689913) B1689913
theorem B4507271 : Blo 1186410 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B4007609 : Blo 1186410 4007609 := bstep (se 2 (by rfl) ⟨1502853, by rfl⟩ : syracuseStep 4007609 = 3005707) B3005707
theorem B1427143 : Blo 1186410 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B4572881 : Blo 1186410 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B2254547 : Blo 1186410 2254547 := bstep (se 1 (by rfl) ⟨1690910, by rfl⟩ : syracuseStep 2254547 = 3381821) B3381821
theorem B2852567 : Blo 1186410 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B3802909 : Blo 1186410 3802909 := bstep (se 3 (by rfl) ⟨713045, by rfl⟩ : syracuseStep 3802909 = 1426091) B1426091
theorem B1714027 : Blo 1186410 1714027 := bstep (se 1 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 1714027 = 2571041) B2571041
theorem B2672567 : Blo 1186410 2672567 := bstep (se 1 (by rfl) ⟨2004425, by rfl⟩ : syracuseStep 2672567 = 4008851) B4008851
theorem B13715405 : Blo 1186410 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B2852921 : Blo 1186410 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B1779791 : Blo 1186410 1779791 := bstep (se 1 (by rfl) ⟨1334843, by rfl⟩ : syracuseStep 1779791 = 2669687) B2669687
theorem B7604381 : Blo 1186410 7604381 := bstep (se 3 (by rfl) ⟨1425821, by rfl⟩ : syracuseStep 7604381 = 2851643) B2851643
theorem B1779911 : Blo 1186410 1779911 := bstep (se 1 (by rfl) ⟨1334933, by rfl⟩ : syracuseStep 1779911 = 2669867) B2669867
theorem B6416651 : Blo 1186410 6416651 := bstep (se 1 (by rfl) ⟨4812488, by rfl⟩ : syracuseStep 6416651 = 9624977) B9624977
theorem B4008203 : Blo 1186410 4008203 := bstep (se 1 (by rfl) ⟨3006152, by rfl⟩ : syracuseStep 4008203 = 6012305) B6012305
theorem B2255177 : Blo 1186410 2255177 := bstep (se 2 (by rfl) ⟨845691, by rfl⟩ : syracuseStep 2255177 = 1691383) B1691383
theorem B1780073 : Blo 1186410 1780073 := bstep (se 2 (by rfl) ⟨667527, by rfl⟩ : syracuseStep 1780073 = 1335055) B1335055
theorem B1780151 : Blo 1186410 1780151 := bstep (se 1 (by rfl) ⟨1335113, by rfl⟩ : syracuseStep 1780151 = 2670227) B2670227
theorem B1780187 : Blo 1186410 1780187 := bstep (se 1 (by rfl) ⟨1335140, by rfl⟩ : syracuseStep 1780187 = 2670281) B2670281
theorem B667388387 : Blo 1186410 667388387 := bstep (se 1 (by rfl) ⟨500541290, by rfl⟩ : syracuseStep 667388387 = 1001082581) B1001082581
theorem B10283501 : Blo 1186410 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B2673161 : Blo 1186410 2673161 := bstep (se 2 (by rfl) ⟨1002435, by rfl⟩ : syracuseStep 2673161 = 2004871) B2004871
theorem B4008473 : Blo 1186410 4008473 := bstep (se 2 (by rfl) ⟨1503177, by rfl⟩ : syracuseStep 4008473 = 3006355) B3006355
theorem B1501735 : Blo 1186410 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B8563259 : Blo 1186410 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B4508257 : Blo 1186410 4508257 := bstep (se 2 (by rfl) ⟨1690596, by rfl⟩ : syracuseStep 4508257 = 3381193) B3381193
theorem B2853575 : Blo 1186410 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B117140185 : Blo 1186410 117140185 := bstep (se 2 (by rfl) ⟨43927569, by rfl⟩ : syracuseStep 117140185 = 87855139) B87855139
theorem B1903351 : Blo 1186410 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B2673503 : Blo 1186410 2673503 := bstep (se 1 (by rfl) ⟨2005127, by rfl⟩ : syracuseStep 2673503 = 4010255) B4010255
theorem B1502059 : Blo 1186410 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B1780655 : Blo 1186410 1780655 := bstep (se 1 (by rfl) ⟨1335491, by rfl⟩ : syracuseStep 1780655 = 2670983) B2670983
theorem B1780745 : Blo 1186410 1780745 := bstep (se 2 (by rfl) ⟨667779, by rfl⟩ : syracuseStep 1780745 = 1335559) B1335559
theorem B2673683 : Blo 1186410 2673683 := bstep (se 1 (by rfl) ⟨2005262, by rfl⟩ : syracuseStep 2673683 = 4010525) B4010525
theorem B1780775 : Blo 1186410 1780775 := bstep (se 1 (by rfl) ⟨1335581, by rfl⟩ : syracuseStep 1780775 = 2671163) B2671163
theorem B4508729 : Blo 1186410 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B2255951 : Blo 1186410 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B1780859 : Blo 1186410 1780859 := bstep (se 1 (by rfl) ⟨1335644, by rfl⟩ : syracuseStep 1780859 = 2671289) B2671289
theorem B1780985 : Blo 1186410 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B10824997 : Blo 1186410 10824997 := bstep (se 4 (by rfl) ⟨1014843, by rfl⟩ : syracuseStep 10824997 = 2029687) B2029687
theorem B1781087 : Blo 1186410 1781087 := bstep (se 1 (by rfl) ⟨1335815, by rfl⟩ : syracuseStep 1781087 = 2671631) B2671631
theorem B1781099 : Blo 1186410 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B5074319 : Blo 1186410 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B8555939 : Blo 1186410 8555939 := bstep (se 1 (by rfl) ⟨6416954, by rfl⟩ : syracuseStep 8555939 = 12833909) B12833909
theorem B7613939 : Blo 1186410 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B2002441 : Blo 1186410 2002441 := bstep (se 2 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 2002441 = 1501831) B1501831
theorem B1781327 : Blo 1186410 1781327 := bstep (se 1 (by rfl) ⟨1335995, by rfl⟩ : syracuseStep 1781327 = 2671991) B2671991
theorem B6008417 : Blo 1186410 6008417 := bstep (se 2 (by rfl) ⟨2253156, by rfl⟩ : syracuseStep 6008417 = 4506313) B4506313
theorem B4009607 : Blo 1186410 4009607 := bstep (se 1 (by rfl) ⟨3007205, by rfl⟩ : syracuseStep 4009607 = 6014411) B6014411
theorem B2002603 : Blo 1186410 2002603 := bstep (se 1 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 2002603 = 3003905) B3003905
theorem B3804857 : Blo 1186410 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B4009661 : Blo 1186410 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B8564413 : Blo 1186410 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B1781447 : Blo 1186410 1781447 := bstep (se 1 (by rfl) ⟨1336085, by rfl⟩ : syracuseStep 1781447 = 2672171) B2672171
theorem B9621281 : Blo 1186410 9621281 := bstep (se 2 (by rfl) ⟨3607980, by rfl⟩ : syracuseStep 9621281 = 7215961) B7215961
theorem B4009823 : Blo 1186410 4009823 := bstep (se 1 (by rfl) ⟨3007367, by rfl⟩ : syracuseStep 4009823 = 6014735) B6014735
theorem B1781609 : Blo 1186410 1781609 := bstep (se 2 (by rfl) ⟨668103, by rfl⟩ : syracuseStep 1781609 = 1336207) B1336207
theorem B1781687 : Blo 1186410 1781687 := bstep (se 1 (by rfl) ⟨1336265, by rfl⟩ : syracuseStep 1781687 = 2672531) B2672531
theorem B2002907 : Blo 1186410 2002907 := bstep (se 1 (by rfl) ⟨1502180, by rfl⟩ : syracuseStep 2002907 = 3004361) B3004361
theorem B1781723 : Blo 1186410 1781723 := bstep (se 1 (by rfl) ⟨1336292, by rfl⟩ : syracuseStep 1781723 = 2672585) B2672585
theorem B4009985 : Blo 1186410 4009985 := bstep (se 2 (by rfl) ⟨1503744, by rfl⟩ : syracuseStep 4009985 = 3007489) B3007489
theorem B9015299 : Blo 1186410 9015299 := bstep (se 1 (by rfl) ⟨6761474, by rfl⟩ : syracuseStep 9015299 = 13522949) B13522949
theorem B4509715 : Blo 1186410 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B25669709 : Blo 1186410 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B11571281 : Blo 1186410 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B21958771 : Blo 1186410 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B1503355 : Blo 1186410 1503355 := bstep (se 1 (by rfl) ⟨1127516, by rfl⟩ : syracuseStep 1503355 = 2255033) B2255033
theorem B2003143 : Blo 1186410 2003143 := bstep (se 1 (by rfl) ⟨1502357, by rfl⟩ : syracuseStep 2003143 = 3004715) B3004715
theorem B19272005 : Blo 1186410 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B4944233 : Blo 1186410 4944233 := bstep (se 2 (by rfl) ⟨1854087, by rfl⟩ : syracuseStep 4944233 = 3708175) B3708175
theorem B2003305 : Blo 1186410 2003305 := bstep (se 2 (by rfl) ⟨751239, by rfl⟩ : syracuseStep 2003305 = 1502479) B1502479
theorem B1782191 : Blo 1186410 1782191 := bstep (se 1 (by rfl) ⟨1336643, by rfl⟩ : syracuseStep 1782191 = 2673287) B2673287
theorem B1782281 : Blo 1186410 1782281 := bstep (se 2 (by rfl) ⟨668355, by rfl⟩ : syracuseStep 1782281 = 1336711) B1336711
theorem B16249369 : Blo 1186410 16249369 := bstep (se 2 (by rfl) ⟨6093513, by rfl⟩ : syracuseStep 16249369 = 12187027) B12187027
theorem B1782311 : Blo 1186410 1782311 := bstep (se 1 (by rfl) ⟨1336733, by rfl⟩ : syracuseStep 1782311 = 2673467) B2673467
theorem B1782395 : Blo 1186410 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B1782521 : Blo 1186410 1782521 := bstep (se 2 (by rfl) ⟨668445, by rfl⟩ : syracuseStep 1782521 = 1336891) B1336891
theorem B4010795 : Blo 1186410 4010795 := bstep (se 1 (by rfl) ⟨3008096, by rfl⟩ : syracuseStep 4010795 = 6016193) B6016193
theorem B2003899 : Blo 1186410 2003899 := bstep (se 1 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 2003899 = 3005849) B3005849
theorem B6009875 : Blo 1186410 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B2004007 : Blo 1186410 2004007 := bstep (se 1 (by rfl) ⟨1503005, by rfl⟩ : syracuseStep 2004007 = 3006011) B3006011
theorem B10286129 : Blo 1186410 10286129 := bstep (se 2 (by rfl) ⟨3857298, by rfl⟩ : syracuseStep 10286129 = 7714597) B7714597
theorem B6763571 : Blo 1186410 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B3429533 : Blo 1186410 3429533 := bstep (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) B1286075
theorem B5067947 : Blo 1186410 5067947 := bstep (se 1 (by rfl) ⟨3800960, by rfl⟩ : syracuseStep 5067947 = 7601921) B7601921
theorem B4879531 : Blo 1186410 4879531 := bstep (se 1 (by rfl) ⟨3659648, by rfl⟩ : syracuseStep 4879531 = 7319297) B7319297
theorem B4281515 : Blo 1186410 4281515 := bstep (se 1 (by rfl) ⟨3211136, by rfl⟩ : syracuseStep 4281515 = 6422273) B6422273
theorem B2004331 : Blo 1186410 2004331 := bstep (se 1 (by rfl) ⟨1503248, by rfl⟩ : syracuseStep 2004331 = 3006497) B3006497
theorem B2537057 : Blo 1186410 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B4060811 : Blo 1186410 4060811 := bstep (se 1 (by rfl) ⟨3045608, by rfl⟩ : syracuseStep 4060811 = 6091217) B6091217
theorem B4511447 : Blo 1186410 4511447 := bstep (se 1 (by rfl) ⟨3383585, by rfl⟩ : syracuseStep 4511447 = 6767171) B6767171
theorem B2283407 : Blo 1186410 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B2537399 : Blo 1186410 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B3209147 : Blo 1186410 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B15210449 : Blo 1186410 15210449 := bstep (se 2 (by rfl) ⟨5703918, by rfl⟩ : syracuseStep 15210449 = 11407837) B11407837
theorem B2029531 : Blo 1186410 2029531 := bstep (se 1 (by rfl) ⟨1522148, by rfl⟩ : syracuseStep 2029531 = 3044297) B3044297
theorem B8558621 : Blo 1186410 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B6092857 : Blo 1186410 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B534034781 : Blo 1186410 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B9017729 : Blo 1186410 9017729 := bstep (se 2 (by rfl) ⟨3381648, by rfl⟩ : syracuseStep 9017729 = 6763297) B6763297
theorem B2005391 : Blo 1186410 2005391 := bstep (se 1 (by rfl) ⟨1504043, by rfl⟩ : syracuseStep 2005391 = 3008087) B3008087
theorem B12843467 : Blo 1186410 12843467 := bstep (se 1 (by rfl) ⟨9632600, by rfl⟩ : syracuseStep 12843467 = 19265201) B19265201
theorem B4004315 : Blo 1186410 4004315 := bstep (se 1 (by rfl) ⟨3003236, by rfl⟩ : syracuseStep 4004315 = 6006473) B6006473
theorem B2406991 : Blo 1186410 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B1186427 : Blo 1186410 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B1186479 : Blo 1186410 1186479 := bstep (se 1 (by rfl) ⟨889859, by rfl⟩ : syracuseStep 1186479 = 1779719) B1779719
theorem B1186503 : Blo 1186410 1186503 := bstep (se 1 (by rfl) ⟨889877, by rfl⟩ : syracuseStep 1186503 = 1779755) B1779755
theorem B4815569 : Blo 1186410 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B1186523 : Blo 1186410 1186523 := bstep (se 1 (by rfl) ⟨889892, by rfl⟩ : syracuseStep 1186523 = 1779785) B1779785
theorem B1186599 : Blo 1186410 1186599 := bstep (se 1 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 1186599 = 1779899) B1779899
theorem B1186639 : Blo 1186410 1186639 := bstep (se 1 (by rfl) ⟨889979, by rfl⟩ : syracuseStep 1186639 = 1779959) B1779959
theorem B1186655 : Blo 1186410 1186655 := bstep (se 1 (by rfl) ⟨889991, by rfl⟩ : syracuseStep 1186655 = 1779983) B1779983
theorem B1186683 : Blo 1186410 1186683 := bstep (se 1 (by rfl) ⟨890012, by rfl⟩ : syracuseStep 1186683 = 1780025) B1780025
theorem B1186735 : Blo 1186410 1186735 := bstep (se 1 (by rfl) ⟨890051, by rfl⟩ : syracuseStep 1186735 = 1780103) B1780103
theorem B1186759 : Blo 1186410 1186759 := bstep (se 1 (by rfl) ⟨890069, by rfl⟩ : syracuseStep 1186759 = 1780139) B1780139
theorem B1186779 : Blo 1186410 1186779 := bstep (se 1 (by rfl) ⟨890084, by rfl⟩ : syracuseStep 1186779 = 1780169) B1780169
theorem B1186855 : Blo 1186410 1186855 := bstep (se 1 (by rfl) ⟨890141, by rfl⟩ : syracuseStep 1186855 = 1780283) B1780283
theorem B12688427 : Blo 1186410 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B1186895 : Blo 1186410 1186895 := bstep (se 1 (by rfl) ⟨890171, by rfl⟩ : syracuseStep 1186895 = 1780343) B1780343
theorem B1186911 : Blo 1186410 1186911 := bstep (se 1 (by rfl) ⟨890183, by rfl⟩ : syracuseStep 1186911 = 1780367) B1780367
theorem B1186939 : Blo 1186410 1186939 := bstep (se 1 (by rfl) ⟨890204, by rfl⟩ : syracuseStep 1186939 = 1780409) B1780409
theorem B4005017 : Blo 1186410 4005017 := bstep (se 2 (by rfl) ⟨1501881, by rfl⟩ : syracuseStep 4005017 = 3003763) B3003763
theorem B1186991 : Blo 1186410 1186991 := bstep (se 1 (by rfl) ⟨890243, by rfl⟩ : syracuseStep 1186991 = 1780487) B1780487
theorem B1187015 : Blo 1186410 1187015 := bstep (se 1 (by rfl) ⟨890261, by rfl⟩ : syracuseStep 1187015 = 1780523) B1780523
theorem B1187035 : Blo 1186410 1187035 := bstep (se 1 (by rfl) ⟨890276, by rfl⟩ : syracuseStep 1187035 = 1780553) B1780553
theorem B3005687 : Blo 1186410 3005687 := bstep (se 1 (by rfl) ⟨2254265, by rfl⟩ : syracuseStep 3005687 = 4508531) B4508531
theorem B1187111 : Blo 1186410 1187111 := bstep (se 1 (by rfl) ⟨890333, by rfl⟩ : syracuseStep 1187111 = 1780667) B1780667
theorem B1187151 : Blo 1186410 1187151 := bstep (se 1 (by rfl) ⟨890363, by rfl⟩ : syracuseStep 1187151 = 1780727) B1780727
theorem B1187167 : Blo 1186410 1187167 := bstep (se 1 (by rfl) ⟨890375, by rfl⟩ : syracuseStep 1187167 = 1780751) B1780751
theorem B1187195 : Blo 1186410 1187195 := bstep (se 1 (by rfl) ⟨890396, by rfl⟩ : syracuseStep 1187195 = 1780793) B1780793
theorem B1187247 : Blo 1186410 1187247 := bstep (se 1 (by rfl) ⟨890435, by rfl⟩ : syracuseStep 1187247 = 1780871) B1780871
theorem B1187271 : Blo 1186410 1187271 := bstep (se 1 (by rfl) ⟨890453, by rfl⟩ : syracuseStep 1187271 = 1780907) B1780907
theorem B1187291 : Blo 1186410 1187291 := bstep (se 1 (by rfl) ⟨890468, by rfl⟩ : syracuseStep 1187291 = 1780937) B1780937
theorem B2670119 : Blo 1186410 2670119 := bstep (se 1 (by rfl) ⟨2002589, by rfl⟩ : syracuseStep 2670119 = 4005179) B4005179
theorem B1187367 : Blo 1186410 1187367 := bstep (se 1 (by rfl) ⟨890525, by rfl⟩ : syracuseStep 1187367 = 1781051) B1781051
theorem B3382823 : Blo 1186410 3382823 := bstep (se 1 (by rfl) ⟨2537117, by rfl⟩ : syracuseStep 3382823 = 5074235) B5074235
theorem B1187407 : Blo 1186410 1187407 := bstep (se 1 (by rfl) ⟨890555, by rfl⟩ : syracuseStep 1187407 = 1781111) B1781111
theorem B1187423 : Blo 1186410 1187423 := bstep (se 1 (by rfl) ⟨890567, by rfl⟩ : syracuseStep 1187423 = 1781135) B1781135
theorem B5144161 : Blo 1186410 5144161 := bstep (se 2 (by rfl) ⟨1929060, by rfl⟩ : syracuseStep 5144161 = 3858121) B3858121
theorem B1187451 : Blo 1186410 1187451 := bstep (se 1 (by rfl) ⟨890588, by rfl⟩ : syracuseStep 1187451 = 1781177) B1781177
theorem B2031227 : Blo 1186410 2031227 := bstep (se 1 (by rfl) ⟨1523420, by rfl⟩ : syracuseStep 2031227 = 3046841) B3046841
theorem B1187503 : Blo 1186410 1187503 := bstep (se 1 (by rfl) ⟨890627, by rfl⟩ : syracuseStep 1187503 = 1781255) B1781255
theorem B1334983 : Blo 1186410 1334983 := bstep (se 1 (by rfl) ⟨1001237, by rfl⟩ : syracuseStep 1334983 = 2002475) B2002475
theorem B1187527 : Blo 1186410 1187527 := bstep (se 1 (by rfl) ⟨890645, by rfl⟩ : syracuseStep 1187527 = 1781291) B1781291
theorem B1187547 : Blo 1186410 1187547 := bstep (se 1 (by rfl) ⟨890660, by rfl⟩ : syracuseStep 1187547 = 1781321) B1781321
theorem B9010925 : Blo 1186410 9010925 := bstep (se 3 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 9010925 = 3379097) B3379097
theorem B15646445 : Blo 1186410 15646445 := bstep (se 3 (by rfl) ⟨2933708, by rfl⟩ : syracuseStep 15646445 = 5867417) B5867417
theorem B9625337 : Blo 1186410 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B1187623 : Blo 1186410 1187623 := bstep (se 1 (by rfl) ⟨890717, by rfl⟩ : syracuseStep 1187623 = 1781435) B1781435
theorem B1187663 : Blo 1186410 1187663 := bstep (se 1 (by rfl) ⟨890747, by rfl⟩ : syracuseStep 1187663 = 1781495) B1781495
theorem B1187679 : Blo 1186410 1187679 := bstep (se 1 (by rfl) ⟨890759, by rfl⟩ : syracuseStep 1187679 = 1781519) B1781519
theorem B2137961 : Blo 1186410 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B2670443 : Blo 1186410 2670443 := bstep (se 1 (by rfl) ⟨2002832, by rfl⟩ : syracuseStep 2670443 = 4005665) B4005665
theorem B6012791 : Blo 1186410 6012791 := bstep (se 1 (by rfl) ⟨4509593, by rfl⟩ : syracuseStep 6012791 = 9019187) B9019187
theorem B1187707 : Blo 1186410 1187707 := bstep (se 1 (by rfl) ⟨890780, by rfl⟩ : syracuseStep 1187707 = 1781561) B1781561
theorem B2670497 : Blo 1186410 2670497 := bstep (se 2 (by rfl) ⟨1001436, by rfl⟩ : syracuseStep 2670497 = 2002873) B2002873
theorem B1187759 : Blo 1186410 1187759 := bstep (se 1 (by rfl) ⟨890819, by rfl⟩ : syracuseStep 1187759 = 1781639) B1781639
theorem B1187783 : Blo 1186410 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B1187803 : Blo 1186410 1187803 := bstep (se 1 (by rfl) ⟨890852, by rfl⟩ : syracuseStep 1187803 = 1781705) B1781705
theorem B6012953 : Blo 1186410 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B17113139 : Blo 1186410 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B5701691 : Blo 1186410 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B29278361 : Blo 1186410 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B5701843 : Blo 1186410 5701843 := bstep (se 1 (by rfl) ⟨4276382, by rfl⟩ : syracuseStep 5701843 = 8552765) B8552765
theorem B9011411 : Blo 1186410 9011411 := bstep (se 1 (by rfl) ⟨6758558, by rfl⟩ : syracuseStep 9011411 = 13517117) B13517117
theorem B2670803 : Blo 1186410 2670803 := bstep (se 1 (by rfl) ⟨2003102, by rfl⟩ : syracuseStep 2670803 = 4006205) B4006205
theorem B2670857 : Blo 1186410 2670857 := bstep (se 2 (by rfl) ⟨1001571, by rfl⟩ : syracuseStep 2670857 = 2003143) B2003143
theorem B1188127 : Blo 1186410 1188127 := bstep (se 1 (by rfl) ⟨891095, by rfl⟩ : syracuseStep 1188127 = 1782191) B1782191
theorem B11403611 : Blo 1186410 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B1188187 : Blo 1186410 1188187 := bstep (se 1 (by rfl) ⟨891140, by rfl⟩ : syracuseStep 1188187 = 1782281) B1782281
theorem B1188207 : Blo 1186410 1188207 := bstep (se 1 (by rfl) ⟨891155, by rfl⟩ : syracuseStep 1188207 = 1782311) B1782311
theorem B1188263 : Blo 1186410 1188263 := bstep (se 1 (by rfl) ⟨891197, by rfl⟩ : syracuseStep 1188263 = 1782395) B1782395
theorem B2671073 : Blo 1186410 2671073 := bstep (se 2 (by rfl) ⟨1001652, by rfl⟩ : syracuseStep 2671073 = 2003305) B2003305
theorem B1188347 : Blo 1186410 1188347 := bstep (se 1 (by rfl) ⟨891260, by rfl⟩ : syracuseStep 1188347 = 1782521) B1782521
theorem B4506131 : Blo 1186410 4506131 := bstep (se 1 (by rfl) ⟨3379598, by rfl⟩ : syracuseStep 4506131 = 6759197) B6759197
theorem B6095411 : Blo 1186410 6095411 := bstep (se 1 (by rfl) ⟨4571558, by rfl⟩ : syracuseStep 6095411 = 9143117) B9143117
theorem B12829319 : Blo 1186410 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B2851499 : Blo 1186410 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B4006583 : Blo 1186410 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B6857419 : Blo 1186410 6857419 := bstep (se 1 (by rfl) ⟨5143064, by rfl⟩ : syracuseStep 6857419 = 10286129) B10286129
theorem B2671379 : Blo 1186410 2671379 := bstep (se 1 (by rfl) ⟨2003534, by rfl⟩ : syracuseStep 2671379 = 4007069) B4007069
theorem B2286355 : Blo 1186410 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B3212111 : Blo 1186410 3212111 := bstep (se 1 (by rfl) ⟨2409083, by rfl⟩ : syracuseStep 3212111 = 4818167) B4818167
theorem B4506587 : Blo 1186410 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B2671739 : Blo 1186410 2671739 := bstep (se 1 (by rfl) ⟨2003804, by rfl⟩ : syracuseStep 2671739 = 4007609) B4007609
theorem B3048587 : Blo 1186410 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B1901711 : Blo 1186410 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B3007631 : Blo 1186410 3007631 := bstep (se 1 (by rfl) ⟨2255723, by rfl⟩ : syracuseStep 3007631 = 4511447) B4511447
theorem B2671865 : Blo 1186410 2671865 := bstep (se 2 (by rfl) ⟨1001949, by rfl⟩ : syracuseStep 2671865 = 2003899) B2003899
theorem B2139431 : Blo 1186410 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B9143603 : Blo 1186410 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B2672009 : Blo 1186410 2672009 := bstep (se 2 (by rfl) ⟨1002003, by rfl⟩ : syracuseStep 2672009 = 2004007) B2004007
theorem B4277767 : Blo 1186410 4277767 := bstep (se 1 (by rfl) ⟨3208325, by rfl⟩ : syracuseStep 4277767 = 6416651) B6416651
theorem B2672135 : Blo 1186410 2672135 := bstep (se 1 (by rfl) ⟨2004101, by rfl⟩ : syracuseStep 2672135 = 4008203) B4008203
theorem B6506041 : Blo 1186410 6506041 := bstep (se 2 (by rfl) ⟨2439765, by rfl⟩ : syracuseStep 6506041 = 4879531) B4879531
theorem B1336927 : Blo 1186410 1336927 := bstep (se 1 (by rfl) ⟨1002695, by rfl⟩ : syracuseStep 1336927 = 2005391) B2005391
theorem B8562311 : Blo 1186410 8562311 := bstep (se 1 (by rfl) ⟨6421733, by rfl⟩ : syracuseStep 8562311 = 12843467) B12843467
theorem B444925591 : Blo 1186410 444925591 := bstep (se 1 (by rfl) ⟨333694193, by rfl⟩ : syracuseStep 444925591 = 667388387) B667388387
theorem B2672315 : Blo 1186410 2672315 := bstep (se 1 (by rfl) ⟨2004236, by rfl⟩ : syracuseStep 2672315 = 4008473) B4008473
theorem B1902383 : Blo 1186410 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B2672441 : Blo 1186410 2672441 := bstep (se 2 (by rfl) ⟨1002165, by rfl⟩ : syracuseStep 2672441 = 2004331) B2004331
theorem B6424609 : Blo 1186410 6424609 := bstep (se 2 (by rfl) ⟨2409228, by rfl⟩ : syracuseStep 6424609 = 4818457) B4818457
theorem B6858881 : Blo 1186410 6858881 := bstep (se 2 (by rfl) ⟨2572080, by rfl⟩ : syracuseStep 6858881 = 5144161) B5144161
theorem B1779977 : Blo 1186410 1779977 := bstep (se 2 (by rfl) ⟨667491, by rfl⟩ : syracuseStep 1779977 = 1334983) B1334983
theorem B1902857 : Blo 1186410 1902857 := bstep (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) B1427143
theorem B5703959 : Blo 1186410 5703959 := bstep (se 1 (by rfl) ⟨4277969, by rfl⟩ : syracuseStep 5703959 = 8555939) B8555939
theorem B1780079 : Blo 1186410 1780079 := bstep (se 1 (by rfl) ⟨1335059, by rfl⟩ : syracuseStep 1780079 = 2670119) B2670119
theorem B2255215 : Blo 1186410 2255215 := bstep (se 1 (by rfl) ⟨1691411, by rfl⟩ : syracuseStep 2255215 = 3382823) B3382823
theorem B1354151 : Blo 1186410 1354151 := bstep (se 1 (by rfl) ⟨1015613, by rfl⟩ : syracuseStep 1354151 = 2031227) B2031227
theorem B2673071 : Blo 1186410 2673071 := bstep (se 1 (by rfl) ⟨2004803, by rfl⟩ : syracuseStep 2673071 = 4009607) B4009607
theorem B2673107 : Blo 1186410 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B6007283 : Blo 1186410 6007283 := bstep (se 1 (by rfl) ⟨4505462, by rfl⟩ : syracuseStep 6007283 = 9010925) B9010925
theorem B10430963 : Blo 1186410 10430963 := bstep (se 1 (by rfl) ⟨7823222, by rfl⟩ : syracuseStep 10430963 = 15646445) B15646445
theorem B6416891 : Blo 1186410 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B2673215 : Blo 1186410 2673215 := bstep (se 1 (by rfl) ⟨2004911, by rfl⟩ : syracuseStep 2673215 = 4009823) B4009823
theorem B1780295 : Blo 1186410 1780295 := bstep (se 1 (by rfl) ⟨1335221, by rfl⟩ : syracuseStep 1780295 = 2670443) B2670443
theorem B4008527 : Blo 1186410 4008527 := bstep (se 1 (by rfl) ⟨3006395, by rfl⟩ : syracuseStep 4008527 = 6012791) B6012791
theorem B1780331 : Blo 1186410 1780331 := bstep (se 1 (by rfl) ⟨1335248, by rfl⟩ : syracuseStep 1780331 = 2670497) B2670497
theorem B2706041 : Blo 1186410 2706041 := bstep (se 2 (by rfl) ⟨1014765, by rfl⟩ : syracuseStep 2706041 = 2029531) B2029531
theorem B2673323 : Blo 1186410 2673323 := bstep (se 1 (by rfl) ⟨2004992, by rfl⟩ : syracuseStep 2673323 = 4009985) B4009985
theorem B1780559 : Blo 1186410 1780559 := bstep (se 1 (by rfl) ⟨1335419, by rfl⟩ : syracuseStep 1780559 = 2670839) B2670839
theorem B6015869 : Blo 1186410 6015869 := bstep (se 3 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 6015869 = 2255951) B2255951
theorem B12848003 : Blo 1186410 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B6007931 : Blo 1186410 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B2673863 : Blo 1186410 2673863 := bstep (se 1 (by rfl) ⟨2005397, by rfl⟩ : syracuseStep 2673863 = 4010795) B4010795
theorem B1780955 : Blo 1186410 1780955 := bstep (se 1 (by rfl) ⟨1335716, by rfl⟩ : syracuseStep 1780955 = 2671433) B2671433
theorem B4509047 : Blo 1186410 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B2002313 : Blo 1186410 2002313 := bstep (se 2 (by rfl) ⟨750867, by rfl⟩ : syracuseStep 2002313 = 1501735) B1501735
theorem B1781129 : Blo 1186410 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B3378631 : Blo 1186410 3378631 := bstep (se 1 (by rfl) ⟨2533973, by rfl⟩ : syracuseStep 3378631 = 5067947) B5067947
theorem B2854343 : Blo 1186410 2854343 := bstep (se 1 (by rfl) ⟨2140757, by rfl⟩ : syracuseStep 2854343 = 4281515) B4281515
theorem B13184621 : Blo 1186410 13184621 := bstep (se 3 (by rfl) ⟨2472116, by rfl⟩ : syracuseStep 13184621 = 4944233) B4944233
theorem B1781483 : Blo 1186410 1781483 := bstep (se 1 (by rfl) ⟨1336112, by rfl⟩ : syracuseStep 1781483 = 2672225) B2672225
theorem B1691371 : Blo 1186410 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B6008579 : Blo 1186410 6008579 := bstep (se 1 (by rfl) ⟨4506434, by rfl⟩ : syracuseStep 6008579 = 9012869) B9012869
theorem B4009769 : Blo 1186410 4009769 := bstep (se 2 (by rfl) ⟨1503663, by rfl⟩ : syracuseStep 4009769 = 3007327) B3007327
theorem B1503031 : Blo 1186410 1503031 := bstep (se 1 (by rfl) ⟨1127273, by rfl⟩ : syracuseStep 1503031 = 2254547) B2254547
theorem B2002745 : Blo 1186410 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B1781711 : Blo 1186410 1781711 := bstep (se 1 (by rfl) ⟨1336283, by rfl⟩ : syracuseStep 1781711 = 2672567) B2672567
theorem B1691599 : Blo 1186410 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B5705747 : Blo 1186410 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B22835357 : Blo 1186410 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B1503451 : Blo 1186410 1503451 := bstep (se 1 (by rfl) ⟨1127588, by rfl⟩ : syracuseStep 1503451 = 2255177) B2255177
theorem B1782107 : Blo 1186410 1782107 := bstep (se 1 (by rfl) ⟨1336580, by rfl⟩ : syracuseStep 1782107 = 2673161) B2673161
theorem B12841517 : Blo 1186410 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B1782335 : Blo 1186410 1782335 := bstep (se 1 (by rfl) ⟨1336751, by rfl⟩ : syracuseStep 1782335 = 2673503) B2673503
theorem B1782455 : Blo 1186410 1782455 := bstep (se 1 (by rfl) ⟨1336841, by rfl⟩ : syracuseStep 1782455 = 2673683) B2673683
theorem B8458951 : Blo 1186410 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B2003791 : Blo 1186410 2003791 := bstep (se 1 (by rfl) ⟨1502843, by rfl⟩ : syracuseStep 2003791 = 3005687) B3005687
theorem B5075959 : Blo 1186410 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B2536571 : Blo 1186410 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B6010199 : Blo 1186410 6010199 := bstep (se 1 (by rfl) ⟨4507649, by rfl⟩ : syracuseStep 6010199 = 9015299) B9015299
theorem B3003743 : Blo 1186410 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B7714187 : Blo 1186410 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B8123809 : Blo 1186410 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B7607789 : Blo 1186410 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B2004473 : Blo 1186410 2004473 := bstep (se 2 (by rfl) ⟨751677, by rfl⟩ : syracuseStep 2004473 = 1503355) B1503355
theorem B2709179 : Blo 1186410 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B2004743 : Blo 1186410 2004743 := bstep (se 1 (by rfl) ⟨1503557, by rfl⟩ : syracuseStep 2004743 = 3007115) B3007115
theorem B14440481 : Blo 1186410 14440481 := bstep (se 2 (by rfl) ⟨5415180, by rfl⟩ : syracuseStep 14440481 = 10830361) B10830361
theorem B21665825 : Blo 1186410 21665825 := bstep (se 2 (by rfl) ⟨8124684, by rfl⟩ : syracuseStep 21665825 = 16249369) B16249369
theorem B3209321 : Blo 1186410 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B6011009 : Blo 1186410 6011009 := bstep (se 2 (by rfl) ⟨2254128, by rfl⟩ : syracuseStep 6011009 = 4508257) B4508257
theorem B4282553 : Blo 1186410 4282553 := bstep (se 2 (by rfl) ⟨1605957, by rfl⟩ : syracuseStep 4282553 = 3211915) B3211915
theorem B156186913 : Blo 1186410 156186913 := bstep (se 2 (by rfl) ⟨58570092, by rfl⟩ : syracuseStep 156186913 = 117140185) B117140185
theorem B2537801 : Blo 1186410 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B4004207 : Blo 1186410 4004207 := bstep (se 1 (by rfl) ⟨3003155, by rfl⟩ : syracuseStep 4004207 = 6006311) B6006311
theorem B3004847 : Blo 1186410 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B3004897 : Blo 1186410 3004897 := bstep (se 2 (by rfl) ⟨1126836, by rfl⟩ : syracuseStep 3004897 = 2253673) B2253673
theorem B1522271 : Blo 1186410 1522271 := bstep (se 1 (by rfl) ⟨1141703, by rfl⟩ : syracuseStep 1522271 = 2283407) B2283407
theorem B10140299 : Blo 1186410 10140299 := bstep (se 1 (by rfl) ⟨7605224, by rfl⟩ : syracuseStep 10140299 = 15210449) B15210449
theorem B1186527 : Blo 1186410 1186527 := bstep (se 1 (by rfl) ⟨889895, by rfl⟩ : syracuseStep 1186527 = 1779791) B1779791
theorem B5069587 : Blo 1186410 5069587 := bstep (se 1 (by rfl) ⟨3802190, by rfl⟩ : syracuseStep 5069587 = 7604381) B7604381
theorem B1186607 : Blo 1186410 1186607 := bstep (se 1 (by rfl) ⟨889955, by rfl⟩ : syracuseStep 1186607 = 1779911) B1779911
theorem B356023187 : Blo 1186410 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B1186715 : Blo 1186410 1186715 := bstep (se 1 (by rfl) ⟨890036, by rfl⟩ : syracuseStep 1186715 = 1780073) B1780073
theorem B6011819 : Blo 1186410 6011819 := bstep (se 1 (by rfl) ⟨4508864, by rfl⟩ : syracuseStep 6011819 = 9017729) B9017729
theorem B1186767 : Blo 1186410 1186767 := bstep (se 1 (by rfl) ⟨890075, by rfl⟩ : syracuseStep 1186767 = 1780151) B1780151
theorem B2669543 : Blo 1186410 2669543 := bstep (se 1 (by rfl) ⟨2002157, by rfl⟩ : syracuseStep 2669543 = 4004315) B4004315
theorem B1186791 : Blo 1186410 1186791 := bstep (se 1 (by rfl) ⟨890093, by rfl⟩ : syracuseStep 1186791 = 1780187) B1780187
theorem B6855667 : Blo 1186410 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B10828829 : Blo 1186410 10828829 := bstep (se 3 (by rfl) ⟨2030405, by rfl⟩ : syracuseStep 10828829 = 4060811) B4060811
theorem B14433329 : Blo 1186410 14433329 := bstep (se 2 (by rfl) ⟨5412498, by rfl⟩ : syracuseStep 14433329 = 10824997) B10824997
theorem B1187103 : Blo 1186410 1187103 := bstep (se 1 (by rfl) ⟨890327, by rfl⟩ : syracuseStep 1187103 = 1780655) B1780655
theorem B1187163 : Blo 1186410 1187163 := bstep (se 1 (by rfl) ⟨890372, by rfl⟩ : syracuseStep 1187163 = 1780745) B1780745
theorem B2669921 : Blo 1186410 2669921 := bstep (se 2 (by rfl) ⟨1001220, by rfl⟩ : syracuseStep 2669921 = 2002441) B2002441
theorem B1187183 : Blo 1186410 1187183 := bstep (se 1 (by rfl) ⟨890387, by rfl⟩ : syracuseStep 1187183 = 1780775) B1780775
theorem B3005819 : Blo 1186410 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B1187239 : Blo 1186410 1187239 := bstep (se 1 (by rfl) ⟨890429, by rfl⟩ : syracuseStep 1187239 = 1780859) B1780859
theorem B2670011 : Blo 1186410 2670011 := bstep (se 1 (by rfl) ⟨2002508, by rfl⟩ : syracuseStep 2670011 = 4005017) B4005017
theorem B1187323 : Blo 1186410 1187323 := bstep (se 1 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 1187323 = 1780985) B1780985
theorem B2670137 : Blo 1186410 2670137 := bstep (se 2 (by rfl) ⟨1001301, by rfl⟩ : syracuseStep 2670137 = 2002603) B2002603
theorem B1187391 : Blo 1186410 1187391 := bstep (se 1 (by rfl) ⟨890543, by rfl⟩ : syracuseStep 1187391 = 1781087) B1781087
theorem B1187399 : Blo 1186410 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B11419217 : Blo 1186410 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B3382879 : Blo 1186410 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B5701229 : Blo 1186410 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B5070545 : Blo 1186410 5070545 := bstep (se 2 (by rfl) ⟨1901454, by rfl⟩ : syracuseStep 5070545 = 3802909) B3802909
theorem B1187551 : Blo 1186410 1187551 := bstep (se 1 (by rfl) ⟨890663, by rfl⟩ : syracuseStep 1187551 = 1781327) B1781327
theorem B4005611 : Blo 1186410 4005611 := bstep (se 1 (by rfl) ⟨3004208, by rfl⟩ : syracuseStep 4005611 = 6008417) B6008417
theorem B1187631 : Blo 1186410 1187631 := bstep (se 1 (by rfl) ⟨890723, by rfl⟩ : syracuseStep 1187631 = 1781447) B1781447
theorem B2285369 : Blo 1186410 2285369 := bstep (se 2 (by rfl) ⟨857013, by rfl⟩ : syracuseStep 2285369 = 1714027) B1714027
theorem B6414187 : Blo 1186410 6414187 := bstep (se 1 (by rfl) ⟨4810640, by rfl⟩ : syracuseStep 6414187 = 9621281) B9621281
theorem B1187739 : Blo 1186410 1187739 := bstep (se 1 (by rfl) ⟨890804, by rfl⟩ : syracuseStep 1187739 = 1781609) B1781609
theorem B1187791 : Blo 1186410 1187791 := bstep (se 1 (by rfl) ⟨890843, by rfl⟩ : syracuseStep 1187791 = 1781687) B1781687
theorem B1335271 : Blo 1186410 1335271 := bstep (se 1 (by rfl) ⟨1001453, by rfl⟩ : syracuseStep 1335271 = 2002907) B2002907
theorem B1187815 : Blo 1186410 1187815 := bstep (se 1 (by rfl) ⟨890861, by rfl⟩ : syracuseStep 1187815 = 1781723) B1781723
theorem B3801127 : Blo 1186410 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B7602407 : Blo 1186410 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B1188071 : Blo 1186410 1188071 := bstep (se 1 (by rfl) ⟨891053, by rfl⟩ : syracuseStep 1188071 = 1782107) B1782107
theorem B7602457 : Blo 1186410 7602457 := bstep (se 2 (by rfl) ⟨2850921, by rfl⟩ : syracuseStep 7602457 = 5701843) B5701843
theorem B4063607 : Blo 1186410 4063607 := bstep (se 1 (by rfl) ⟨3047705, by rfl⟩ : syracuseStep 4063607 = 6095411) B6095411
theorem B1188223 : Blo 1186410 1188223 := bstep (se 1 (by rfl) ⟨891167, by rfl⟩ : syracuseStep 1188223 = 1782335) B1782335
theorem B208249217 : Blo 1186410 208249217 := bstep (se 2 (by rfl) ⟨78093456, by rfl⟩ : syracuseStep 208249217 = 156186913) B156186913
theorem B8552879 : Blo 1186410 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B1900999 : Blo 1186410 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B2671055 : Blo 1186410 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B1188303 : Blo 1186410 1188303 := bstep (se 1 (by rfl) ⟨891227, by rfl⟩ : syracuseStep 1188303 = 1782455) B1782455
theorem B3006953 : Blo 1186410 3006953 := bstep (se 2 (by rfl) ⟨1127607, by rfl⟩ : syracuseStep 3006953 = 2255215) B2255215
theorem B4006529 : Blo 1186410 4006529 := bstep (se 2 (by rfl) ⟨1502448, by rfl⟩ : syracuseStep 4006529 = 3004897) B3004897
theorem B2032391 : Blo 1186410 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B2372936485 : Blo 1186410 2372936485 := bstep (se 4 (by rfl) ⟨222462795, by rfl⟩ : syracuseStep 2372936485 = 444925591) B444925591
theorem B6095735 : Blo 1186410 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B4006799 : Blo 1186410 4006799 := bstep (se 1 (by rfl) ⟨3005099, by rfl⟩ : syracuseStep 4006799 = 6010199) B6010199
theorem B9143225 : Blo 1186410 9143225 := bstep (se 2 (by rfl) ⟨3428709, by rfl⟩ : syracuseStep 9143225 = 6857419) B6857419
theorem B5071859 : Blo 1186410 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B1336315 : Blo 1186410 1336315 := bstep (se 1 (by rfl) ⟨1002236, by rfl⟩ : syracuseStep 1336315 = 2004473) B2004473
theorem B6759449 : Blo 1186410 6759449 := bstep (se 2 (by rfl) ⟨2534793, by rfl⟩ : syracuseStep 6759449 = 5069587) B5069587
theorem B3048473 : Blo 1186410 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B2671721 : Blo 1186410 2671721 := bstep (se 2 (by rfl) ⟨1001895, by rfl⟩ : syracuseStep 2671721 = 2003791) B2003791
theorem B1336495 : Blo 1186410 1336495 := bstep (se 1 (by rfl) ⟨1002371, by rfl⟩ : syracuseStep 1336495 = 2004743) B2004743
theorem B9020645 : Blo 1186410 9020645 := bstep (se 4 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 9020645 = 1691371) B1691371
theorem B6767945 : Blo 1186410 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B9626987 : Blo 1186410 9626987 := bstep (se 1 (by rfl) ⟨7220240, by rfl⟩ : syracuseStep 9626987 = 14440481) B14440481
theorem B14443883 : Blo 1186410 14443883 := bstep (se 1 (by rfl) ⟨10832912, by rfl⟩ : syracuseStep 14443883 = 21665825) B21665825
theorem B2139547 : Blo 1186410 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B4007339 : Blo 1186410 4007339 := bstep (se 1 (by rfl) ⟨3005504, by rfl⟩ : syracuseStep 4007339 = 6011009) B6011009
theorem B4572587 : Blo 1186410 4572587 := bstep (se 1 (by rfl) ⟨3429440, by rfl⟩ : syracuseStep 4572587 = 6858881) B6858881
theorem B34244045 : Blo 1186410 34244045 := bstep (se 3 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 34244045 = 12841517) B12841517
theorem B3802639 : Blo 1186410 3802639 := bstep (se 1 (by rfl) ⟨2851979, by rfl⟩ : syracuseStep 3802639 = 5703959) B5703959
theorem B4277927 : Blo 1186410 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B2672351 : Blo 1186410 2672351 := bstep (se 1 (by rfl) ⟨2004263, by rfl⟩ : syracuseStep 2672351 = 4008527) B4008527
theorem B1804027 : Blo 1186410 1804027 := bstep (se 1 (by rfl) ⟨1353020, by rfl⟩ : syracuseStep 1804027 = 2706041) B2706041
theorem B6760199 : Blo 1186410 6760199 := bstep (se 1 (by rfl) ⟨5070149, by rfl⟩ : syracuseStep 6760199 = 10140299) B10140299
theorem B10831745 : Blo 1186410 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B237348791 : Blo 1186410 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B4007879 : Blo 1186410 4007879 := bstep (se 1 (by rfl) ⟨3005909, by rfl⟩ : syracuseStep 4007879 = 6011819) B6011819
theorem B1779695 : Blo 1186410 1779695 := bstep (se 1 (by rfl) ⟨1334771, by rfl⟩ : syracuseStep 1779695 = 2669543) B2669543
theorem B5703689 : Blo 1186410 5703689 := bstep (se 2 (by rfl) ⟨2138883, by rfl⟩ : syracuseStep 5703689 = 4277767) B4277767
theorem B7219219 : Blo 1186410 7219219 := bstep (se 1 (by rfl) ⟨5414414, by rfl⟩ : syracuseStep 7219219 = 10828829) B10828829
theorem B1779947 : Blo 1186410 1779947 := bstep (se 1 (by rfl) ⟨1334960, by rfl⟩ : syracuseStep 1779947 = 2669921) B2669921
theorem B1780007 : Blo 1186410 1780007 := bstep (se 1 (by rfl) ⟨1335005, by rfl⟩ : syracuseStep 1780007 = 2670011) B2670011
theorem B1902895 : Blo 1186410 1902895 := bstep (se 1 (by rfl) ⟨1427171, by rfl⟩ : syracuseStep 1902895 = 2854343) B2854343
theorem B1780091 : Blo 1186410 1780091 := bstep (se 1 (by rfl) ⟨1335068, by rfl⟩ : syracuseStep 1780091 = 2670137) B2670137
theorem B7612811 : Blo 1186410 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B2673179 : Blo 1186410 2673179 := bstep (se 1 (by rfl) ⟨2004884, by rfl⟩ : syracuseStep 2673179 = 4009769) B4009769
theorem B36563557 : Blo 1186410 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B2255465 : Blo 1186410 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B1780361 : Blo 1186410 1780361 := bstep (se 2 (by rfl) ⟨667635, by rfl⟩ : syracuseStep 1780361 = 1335271) B1335271
theorem B3803831 : Blo 1186410 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B4008635 : Blo 1186410 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B15223571 : Blo 1186410 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B38488877 : Blo 1186410 38488877 := bstep (se 3 (by rfl) ⟨7216664, by rfl⟩ : syracuseStep 38488877 = 14433329) B14433329
theorem B6007607 : Blo 1186410 6007607 := bstep (se 1 (by rfl) ⟨4505705, by rfl⟩ : syracuseStep 6007607 = 9011411) B9011411
theorem B1780535 : Blo 1186410 1780535 := bstep (se 1 (by rfl) ⟨1335401, by rfl⟩ : syracuseStep 1780535 = 2670803) B2670803
theorem B1780571 : Blo 1186410 1780571 := bstep (se 1 (by rfl) ⟨1335428, by rfl⟩ : syracuseStep 1780571 = 2670857) B2670857
theorem B1780715 : Blo 1186410 1780715 := bstep (se 1 (by rfl) ⟨1335536, by rfl⟩ : syracuseStep 1780715 = 2671073) B2671073
theorem B1780919 : Blo 1186410 1780919 := bstep (se 1 (by rfl) ⟨1335689, by rfl⟩ : syracuseStep 1780919 = 2671379) B2671379
theorem B2141407 : Blo 1186410 2141407 := bstep (se 1 (by rfl) ⟨1606055, by rfl⟩ : syracuseStep 2141407 = 3212111) B3212111
theorem B5074285 : Blo 1186410 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B1781159 : Blo 1186410 1781159 := bstep (se 1 (by rfl) ⟨1335869, by rfl⟩ : syracuseStep 1781159 = 2671739) B2671739
theorem B1691047 : Blo 1186410 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B5705149 : Blo 1186410 5705149 := bstep (se 3 (by rfl) ⟨1069715, by rfl⟩ : syracuseStep 5705149 = 2139431) B2139431
theorem B1781243 : Blo 1186410 1781243 := bstep (se 1 (by rfl) ⟨1335932, by rfl⟩ : syracuseStep 1781243 = 2671865) B2671865
theorem B2002495 : Blo 1186410 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B1781339 : Blo 1186410 1781339 := bstep (se 1 (by rfl) ⟨1336004, by rfl⟩ : syracuseStep 1781339 = 2672009) B2672009
theorem B1781423 : Blo 1186410 1781423 := bstep (se 1 (by rfl) ⟨1336067, by rfl⟩ : syracuseStep 1781423 = 2672135) B2672135
theorem B1781543 : Blo 1186410 1781543 := bstep (se 1 (by rfl) ⟨1336157, by rfl⟩ : syracuseStep 1781543 = 2672315) B2672315
theorem B1806119 : Blo 1186410 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B1781627 : Blo 1186410 1781627 := bstep (se 1 (by rfl) ⟨1336220, by rfl⟩ : syracuseStep 1781627 = 2672441) B2672441
theorem B2855035 : Blo 1186410 2855035 := bstep (se 1 (by rfl) ⟨2141276, by rfl⟩ : syracuseStep 2855035 = 4282553) B4282553
theorem B1691867 : Blo 1186410 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B4059389 : Blo 1186410 4059389 := bstep (se 3 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 4059389 = 1522271) B1522271
theorem B2003231 : Blo 1186410 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B1782047 : Blo 1186410 1782047 := bstep (se 1 (by rfl) ⟨1336535, by rfl⟩ : syracuseStep 1782047 = 2673071) B2673071
theorem B1782071 : Blo 1186410 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B1782143 : Blo 1186410 1782143 := bstep (se 1 (by rfl) ⟨1336607, by rfl⟩ : syracuseStep 1782143 = 2673215) B2673215
theorem B1782215 : Blo 1186410 1782215 := bstep (se 1 (by rfl) ⟨1336661, by rfl⟩ : syracuseStep 1782215 = 2673323) B2673323
theorem B4010579 : Blo 1186410 4010579 := bstep (se 1 (by rfl) ⟨3007934, by rfl⟩ : syracuseStep 4010579 = 6015869) B6015869
theorem B8565335 : Blo 1186410 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B4510505 : Blo 1186410 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B1782569 : Blo 1186410 1782569 := bstep (se 2 (by rfl) ⟨668463, by rfl⟩ : syracuseStep 1782569 = 1336927) B1336927
theorem B1782575 : Blo 1186410 1782575 := bstep (se 1 (by rfl) ⟨1336931, by rfl⟩ : syracuseStep 1782575 = 2673863) B2673863
theorem B2003879 : Blo 1186410 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B2004041 : Blo 1186410 2004041 := bstep (se 2 (by rfl) ⟨751515, by rfl⟩ : syracuseStep 2004041 = 1503031) B1503031
theorem B3380363 : Blo 1186410 3380363 := bstep (se 1 (by rfl) ⟨2535272, by rfl⟩ : syracuseStep 3380363 = 5070545) B5070545
theorem B11408759 : Blo 1186410 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B8566145 : Blo 1186410 8566145 := bstep (se 2 (by rfl) ⟨3212304, by rfl⟩ : syracuseStep 8566145 = 6424609) B6424609
theorem B19518907 : Blo 1186410 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B2004601 : Blo 1186410 2004601 := bstep (se 2 (by rfl) ⟨751725, by rfl⟩ : syracuseStep 2004601 = 1503451) B1503451
theorem B3004087 : Blo 1186410 3004087 := bstep (se 1 (by rfl) ⟨2253065, by rfl⟩ : syracuseStep 3004087 = 4506131) B4506131
theorem B3004391 : Blo 1186410 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B1267807 : Blo 1186410 1267807 := bstep (se 1 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 1267807 = 1901711) B1901711
theorem B2005087 : Blo 1186410 2005087 := bstep (se 1 (by rfl) ⟨1503815, by rfl⟩ : syracuseStep 2005087 = 3007631) B3007631
theorem B5142791 : Blo 1186410 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B11278601 : Blo 1186410 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B5708207 : Blo 1186410 5708207 := bstep (se 1 (by rfl) ⟨4281155, by rfl⟩ : syracuseStep 5708207 = 8562311) B8562311
theorem B3611069 : Blo 1186410 3611069 := bstep (se 3 (by rfl) ⟨677075, by rfl⟩ : syracuseStep 3611069 = 1354151) B1354151
theorem B1268255 : Blo 1186410 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B1186651 : Blo 1186410 1186651 := bstep (se 1 (by rfl) ⟨889988, by rfl⟩ : syracuseStep 1186651 = 1779977) B1779977
theorem B2669471 : Blo 1186410 2669471 := bstep (se 1 (by rfl) ⟨2002103, by rfl⟩ : syracuseStep 2669471 = 4004207) B4004207
theorem B1186719 : Blo 1186410 1186719 := bstep (se 1 (by rfl) ⟨890039, by rfl⟩ : syracuseStep 1186719 = 1780079) B1780079
theorem B4004855 : Blo 1186410 4004855 := bstep (se 1 (by rfl) ⟨3003641, by rfl⟩ : syracuseStep 4004855 = 6007283) B6007283
theorem B6953975 : Blo 1186410 6953975 := bstep (se 1 (by rfl) ⟨5215481, by rfl⟩ : syracuseStep 6953975 = 10430963) B10430963
theorem B1186863 : Blo 1186410 1186863 := bstep (se 1 (by rfl) ⟨890147, by rfl⟩ : syracuseStep 1186863 = 1780295) B1780295
theorem B1186887 : Blo 1186410 1186887 := bstep (se 1 (by rfl) ⟨890165, by rfl⟩ : syracuseStep 1186887 = 1780331) B1780331
theorem B1187039 : Blo 1186410 1187039 := bstep (se 1 (by rfl) ⟨890279, by rfl⟩ : syracuseStep 1187039 = 1780559) B1780559
theorem B4504841 : Blo 1186410 4504841 := bstep (se 2 (by rfl) ⟨1689315, by rfl⟩ : syracuseStep 4504841 = 3378631) B3378631
theorem B8674721 : Blo 1186410 8674721 := bstep (se 2 (by rfl) ⟨3253020, by rfl⟩ : syracuseStep 8674721 = 6506041) B6506041
theorem B4005287 : Blo 1186410 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B1187303 : Blo 1186410 1187303 := bstep (se 1 (by rfl) ⟨890477, by rfl⟩ : syracuseStep 1187303 = 1780955) B1780955
theorem B3006031 : Blo 1186410 3006031 := bstep (se 1 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 3006031 = 4509047) B4509047
theorem B1334875 : Blo 1186410 1334875 := bstep (se 1 (by rfl) ⟨1001156, by rfl⟩ : syracuseStep 1334875 = 2002313) B2002313
theorem B1187419 : Blo 1186410 1187419 := bstep (se 1 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 1187419 = 1781129) B1781129
theorem B3800819 : Blo 1186410 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B8789747 : Blo 1186410 8789747 := bstep (se 1 (by rfl) ⟨6592310, by rfl⟩ : syracuseStep 8789747 = 13184621) B13184621
theorem B8552249 : Blo 1186410 8552249 := bstep (se 2 (by rfl) ⟨3207093, by rfl⟩ : syracuseStep 8552249 = 6414187) B6414187
theorem B2670407 : Blo 1186410 2670407 := bstep (se 1 (by rfl) ⟨2002805, by rfl⟩ : syracuseStep 2670407 = 4005611) B4005611
theorem B1187655 : Blo 1186410 1187655 := bstep (se 1 (by rfl) ⟨890741, by rfl⟩ : syracuseStep 1187655 = 1781483) B1781483
theorem B4005719 : Blo 1186410 4005719 := bstep (se 1 (by rfl) ⟨3004289, by rfl⟩ : syracuseStep 4005719 = 6008579) B6008579
theorem B1335163 : Blo 1186410 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B1523579 : Blo 1186410 1523579 := bstep (se 1 (by rfl) ⟨1142684, by rfl⟩ : syracuseStep 1523579 = 2285369) B2285369
theorem B1187807 : Blo 1186410 1187807 := bstep (se 1 (by rfl) ⟨890855, by rfl⟩ : syracuseStep 1187807 = 1781711) B1781711
theorem B9625625 : Blo 1186410 9625625 := bstep (se 2 (by rfl) ⟨3609609, by rfl⟩ : syracuseStep 9625625 = 7219219) B7219219
theorem B1335487 : Blo 1186410 1335487 := bstep (se 1 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 1335487 = 2003231) B2003231
theorem B1188031 : Blo 1186410 1188031 := bstep (se 1 (by rfl) ⟨891023, by rfl⟩ : syracuseStep 1188031 = 1782047) B1782047
theorem B1188047 : Blo 1186410 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B1188095 : Blo 1186410 1188095 := bstep (se 1 (by rfl) ⟨891071, by rfl⟩ : syracuseStep 1188095 = 1782143) B1782143
theorem B5701919 : Blo 1186410 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B1188143 : Blo 1186410 1188143 := bstep (se 1 (by rfl) ⟨891107, by rfl⟩ : syracuseStep 1188143 = 1782215) B1782215
theorem B5710223 : Blo 1186410 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B2671019 : Blo 1186410 2671019 := bstep (se 1 (by rfl) ⟨2003264, by rfl⟩ : syracuseStep 2671019 = 4006529) B4006529
theorem B3007003 : Blo 1186410 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B1188379 : Blo 1186410 1188379 := bstep (se 1 (by rfl) ⟨891284, by rfl⟩ : syracuseStep 1188379 = 1782569) B1782569
theorem B1188383 : Blo 1186410 1188383 := bstep (se 1 (by rfl) ⟨891287, by rfl⟩ : syracuseStep 1188383 = 1782575) B1782575
theorem B4063823 : Blo 1186410 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B2671199 : Blo 1186410 2671199 := bstep (se 1 (by rfl) ⟨2003399, by rfl⟩ : syracuseStep 2671199 = 4006799) B4006799
theorem B1335919 : Blo 1186410 1335919 := bstep (se 1 (by rfl) ⟨1001939, by rfl⟩ : syracuseStep 1335919 = 2003879) B2003879
theorem B6095483 : Blo 1186410 6095483 := bstep (se 1 (by rfl) ⟨4571612, by rfl⟩ : syracuseStep 6095483 = 9143225) B9143225
theorem B4506299 : Blo 1186410 4506299 := bstep (se 1 (by rfl) ⟨3379724, by rfl⟩ : syracuseStep 4506299 = 6759449) B6759449
theorem B13714109 : Blo 1186410 13714109 := bstep (se 3 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 13714109 = 5142791) B5142791
theorem B1336027 : Blo 1186410 1336027 := bstep (se 1 (by rfl) ⟨1002020, by rfl⟩ : syracuseStep 1336027 = 2004041) B2004041
theorem B2253575 : Blo 1186410 2253575 := bstep (se 1 (by rfl) ⟨1690181, by rfl⟩ : syracuseStep 2253575 = 3380363) B3380363
theorem B48751409 : Blo 1186410 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B6013763 : Blo 1186410 6013763 := bstep (se 1 (by rfl) ⟨4510322, by rfl⟩ : syracuseStep 6013763 = 9020645) B9020645
theorem B5710763 : Blo 1186410 5710763 := bstep (se 1 (by rfl) ⟨4283072, by rfl⟩ : syracuseStep 5710763 = 8566145) B8566145
theorem B2671559 : Blo 1186410 2671559 := bstep (se 1 (by rfl) ⟨2003669, by rfl⟩ : syracuseStep 2671559 = 4007339) B4007339
theorem B3048391 : Blo 1186410 3048391 := bstep (se 1 (by rfl) ⟨2286293, by rfl⟩ : syracuseStep 3048391 = 4572587) B4572587
theorem B3163915313 : Blo 1186410 3163915313 := bstep (se 2 (by rfl) ⟨1186468242, by rfl⟩ : syracuseStep 3163915313 = 2372936485) B2372936485
theorem B2851951 : Blo 1186410 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B4506799 : Blo 1186410 4506799 := bstep (se 1 (by rfl) ⟨3380099, by rfl⟩ : syracuseStep 4506799 = 6760199) B6760199
theorem B2671919 : Blo 1186410 2671919 := bstep (se 1 (by rfl) ⟨2003939, by rfl⟩ : syracuseStep 2671919 = 4007879) B4007879
theorem B3802459 : Blo 1186410 3802459 := bstep (se 1 (by rfl) ⟨2851844, by rfl⟩ : syracuseStep 3802459 = 5703689) B5703689
theorem B6014573 : Blo 1186410 6014573 := bstep (se 3 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 6014573 = 2255465) B2255465
theorem B2672423 : Blo 1186410 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B25659251 : Blo 1186410 25659251 := bstep (se 1 (by rfl) ⟨19244438, by rfl⟩ : syracuseStep 25659251 = 38488877) B38488877
theorem B2852729 : Blo 1186410 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B2254729 : Blo 1186410 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B1779647 : Blo 1186410 1779647 := bstep (se 1 (by rfl) ⟨1334735, by rfl⟩ : syracuseStep 1779647 = 2669471) B2669471
theorem B4008041 : Blo 1186410 4008041 := bstep (se 2 (by rfl) ⟨1503015, by rfl⟩ : syracuseStep 4008041 = 3006031) B3006031
theorem B1779833 : Blo 1186410 1779833 := bstep (se 2 (by rfl) ⟨667437, by rfl⟩ : syracuseStep 1779833 = 1334875) B1334875
theorem B2672801 : Blo 1186410 2672801 := bstep (se 2 (by rfl) ⟨1002300, by rfl⟩ : syracuseStep 2672801 = 2004601) B2004601
theorem B2533879 : Blo 1186410 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B1780217 : Blo 1186410 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B1780271 : Blo 1186410 1780271 := bstep (se 1 (by rfl) ⟨1335203, by rfl⟩ : syracuseStep 1780271 = 2670407) B2670407
theorem B8129261 : Blo 1186410 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B1690409 : Blo 1186410 1690409 := bstep (se 2 (by rfl) ⟨633903, by rfl⟩ : syracuseStep 1690409 = 1267807) B1267807
theorem B2673449 : Blo 1186410 2673449 := bstep (se 2 (by rfl) ⟨1002543, by rfl⟩ : syracuseStep 2673449 = 2005087) B2005087
theorem B2706259 : Blo 1186410 2706259 := bstep (se 1 (by rfl) ⟨2029694, by rfl⟩ : syracuseStep 2706259 = 4059389) B4059389
theorem B138832811 : Blo 1186410 138832811 := bstep (se 1 (by rfl) ⟨104124608, by rfl⟩ : syracuseStep 138832811 = 208249217) B208249217
theorem B1780703 : Blo 1186410 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B10136609 : Blo 1186410 10136609 := bstep (se 2 (by rfl) ⟨3801228, by rfl⟩ : syracuseStep 10136609 = 7602457) B7602457
theorem B2673719 : Blo 1186410 2673719 := bstep (se 1 (by rfl) ⟨2005289, by rfl⟩ : syracuseStep 2673719 = 4010579) B4010579
theorem B2534665 : Blo 1186410 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B1781147 : Blo 1186410 1781147 := bstep (se 1 (by rfl) ⟨1335860, by rfl⟩ : syracuseStep 1781147 = 2671721) B2671721
theorem B6417991 : Blo 1186410 6417991 := bstep (se 1 (by rfl) ⟨4813493, by rfl⟩ : syracuseStep 6417991 = 9626987) B9626987
theorem B9629255 : Blo 1186410 9629255 := bstep (se 1 (by rfl) ⟨7221941, by rfl⟩ : syracuseStep 9629255 = 14443883) B14443883
theorem B7605839 : Blo 1186410 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B1781567 : Blo 1186410 1781567 := bstep (se 1 (by rfl) ⟨1336175, by rfl⟩ : syracuseStep 1781567 = 2672351) B2672351
theorem B7221163 : Blo 1186410 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B158232527 : Blo 1186410 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B2002927 : Blo 1186410 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B1781753 : Blo 1186410 1781753 := bstep (se 2 (by rfl) ⟨668157, by rfl⟩ : syracuseStep 1781753 = 1336315) B1336315
theorem B1781993 : Blo 1186410 1781993 := bstep (se 2 (by rfl) ⟨668247, by rfl⟩ : syracuseStep 1781993 = 1336495) B1336495
theorem B5075207 : Blo 1186410 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B3805471 : Blo 1186410 3805471 := bstep (se 1 (by rfl) ⟨2854103, by rfl⟩ : syracuseStep 3805471 = 5708207) B5708207
theorem B2855209 : Blo 1186410 2855209 := bstep (se 2 (by rfl) ⟨1070703, by rfl⟩ : syracuseStep 2855209 = 2141407) B2141407
theorem B1782119 : Blo 1186410 1782119 := bstep (se 1 (by rfl) ⟨1336589, by rfl⟩ : syracuseStep 1782119 = 2673179) B2673179
theorem B2535887 : Blo 1186410 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B7606865 : Blo 1186410 7606865 := bstep (se 2 (by rfl) ⟨2852574, by rfl⟩ : syracuseStep 7606865 = 5705149) B5705149
theorem B5419709 : Blo 1186410 5419709 := bstep (se 3 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 5419709 = 2032391) B2032391
theorem B3003227 : Blo 1186410 3003227 := bstep (se 1 (by rfl) ⟨2252420, by rfl⟩ : syracuseStep 3003227 = 4504841) B4504841
theorem B2405369 : Blo 1186410 2405369 := bstep (se 2 (by rfl) ⟨902013, by rfl⟩ : syracuseStep 2405369 = 1804027) B1804027
theorem B5068169 : Blo 1186410 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B5068271 : Blo 1186410 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B3806713 : Blo 1186410 3806713 := bstep (se 2 (by rfl) ⟨1427517, by rfl⟩ : syracuseStep 3806713 = 2855035) B2855035
theorem B2709071 : Blo 1186410 2709071 := bstep (se 1 (by rfl) ⟨2031803, by rfl⟩ : syracuseStep 2709071 = 4063607) B4063607
theorem B2004635 : Blo 1186410 2004635 := bstep (se 1 (by rfl) ⟨1503476, by rfl⟩ : syracuseStep 2004635 = 3006953) B3006953
theorem B4511645 : Blo 1186410 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B3381239 : Blo 1186410 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B4511963 : Blo 1186410 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B22829363 : Blo 1186410 22829363 := bstep (se 1 (by rfl) ⟨17122022, by rfl⟩ : syracuseStep 22829363 = 34244045) B34244045
theorem B16251509 : Blo 1186410 16251509 := bstep (se 5 (by rfl) ⟨761789, by rfl⟩ : syracuseStep 16251509 = 1523579) B1523579
theorem B1186463 : Blo 1186410 1186463 := bstep (se 1 (by rfl) ⟨889847, by rfl⟩ : syracuseStep 1186463 = 1779695) B1779695
theorem B3382013 : Blo 1186410 3382013 := bstep (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) B1268255
theorem B1186631 : Blo 1186410 1186631 := bstep (se 1 (by rfl) ⟨889973, by rfl⟩ : syracuseStep 1186631 = 1779947) B1779947
theorem B7519067 : Blo 1186410 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B1186671 : Blo 1186410 1186671 := bstep (se 1 (by rfl) ⟨890003, by rfl⟩ : syracuseStep 1186671 = 1780007) B1780007
theorem B10148773 : Blo 1186410 10148773 := bstep (se 4 (by rfl) ⟨951447, by rfl⟩ : syracuseStep 10148773 = 1902895) B1902895
theorem B1186727 : Blo 1186410 1186727 := bstep (se 1 (by rfl) ⟨890045, by rfl⟩ : syracuseStep 1186727 = 1780091) B1780091
theorem B2407379 : Blo 1186410 2407379 := bstep (se 1 (by rfl) ⟨1805534, by rfl⟩ : syracuseStep 2407379 = 3611069) B3611069
theorem B1186907 : Blo 1186410 1186907 := bstep (se 1 (by rfl) ⟨890180, by rfl⟩ : syracuseStep 1186907 = 1780361) B1780361
theorem B6765713 : Blo 1186410 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B10149047 : Blo 1186410 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B4005071 : Blo 1186410 4005071 := bstep (se 1 (by rfl) ⟨3003803, by rfl⟩ : syracuseStep 4005071 = 6007607) B6007607
theorem B1187023 : Blo 1186410 1187023 := bstep (se 1 (by rfl) ⟨890267, by rfl⟩ : syracuseStep 1187023 = 1780535) B1780535
theorem B1187047 : Blo 1186410 1187047 := bstep (se 1 (by rfl) ⟨890285, by rfl⟩ : syracuseStep 1187047 = 1780571) B1780571
theorem B26025209 : Blo 1186410 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B1187143 : Blo 1186410 1187143 := bstep (se 1 (by rfl) ⟨890357, by rfl⟩ : syracuseStep 1187143 = 1780715) B1780715
theorem B2669903 : Blo 1186410 2669903 := bstep (se 1 (by rfl) ⟨2002427, by rfl⟩ : syracuseStep 2669903 = 4004855) B4004855
theorem B4635983 : Blo 1186410 4635983 := bstep (se 1 (by rfl) ⟨3476987, by rfl⟩ : syracuseStep 4635983 = 6953975) B6953975
theorem B5070185 : Blo 1186410 5070185 := bstep (se 2 (by rfl) ⟨1901319, by rfl⟩ : syracuseStep 5070185 = 3802639) B3802639
theorem B2669993 : Blo 1186410 2669993 := bstep (se 2 (by rfl) ⟨1001247, by rfl⟩ : syracuseStep 2669993 = 2002495) B2002495
theorem B1187279 : Blo 1186410 1187279 := bstep (se 1 (by rfl) ⟨890459, by rfl⟩ : syracuseStep 1187279 = 1780919) B1780919
theorem B4005449 : Blo 1186410 4005449 := bstep (se 2 (by rfl) ⟨1502043, by rfl⟩ : syracuseStep 4005449 = 3004087) B3004087
theorem B5783147 : Blo 1186410 5783147 := bstep (se 1 (by rfl) ⟨4337360, by rfl⟩ : syracuseStep 5783147 = 8674721) B8674721
theorem B2670191 : Blo 1186410 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B1187439 : Blo 1186410 1187439 := bstep (se 1 (by rfl) ⟨890579, by rfl⟩ : syracuseStep 1187439 = 1781159) B1781159
theorem B1187495 : Blo 1186410 1187495 := bstep (se 1 (by rfl) ⟨890621, by rfl⟩ : syracuseStep 1187495 = 1781243) B1781243
theorem B1187559 : Blo 1186410 1187559 := bstep (se 1 (by rfl) ⟨890669, by rfl⟩ : syracuseStep 1187559 = 1781339) B1781339
theorem B1187615 : Blo 1186410 1187615 := bstep (se 1 (by rfl) ⟨890711, by rfl⟩ : syracuseStep 1187615 = 1781423) B1781423
theorem B1187695 : Blo 1186410 1187695 := bstep (se 1 (by rfl) ⟨890771, by rfl⟩ : syracuseStep 1187695 = 1781543) B1781543
theorem B1204079 : Blo 1186410 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B93757301 : Blo 1186410 93757301 := bstep (se 5 (by rfl) ⟨4394873, by rfl⟩ : syracuseStep 93757301 = 8789747) B8789747
theorem B5701499 : Blo 1186410 5701499 := bstep (se 1 (by rfl) ⟨4276124, by rfl⟩ : syracuseStep 5701499 = 8552249) B8552249
theorem B2670479 : Blo 1186410 2670479 := bstep (se 1 (by rfl) ⟨2002859, by rfl⟩ : syracuseStep 2670479 = 4005719) B4005719
theorem B1187751 : Blo 1186410 1187751 := bstep (se 1 (by rfl) ⟨890813, by rfl⟩ : syracuseStep 1187751 = 1781627) B1781627
theorem B1187995 : Blo 1186410 1187995 := bstep (se 1 (by rfl) ⟨890996, by rfl⟩ : syracuseStep 1187995 = 1781993) B1781993
theorem B3383471 : Blo 1186410 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B1188079 : Blo 1186410 1188079 := bstep (se 1 (by rfl) ⟨891059, by rfl⟩ : syracuseStep 1188079 = 1782119) B1782119
theorem B5071243 : Blo 1186410 5071243 := bstep (se 1 (by rfl) ⟨3803432, by rfl⟩ : syracuseStep 5071243 = 7606865) B7606865
theorem B9142739 : Blo 1186410 9142739 := bstep (se 1 (by rfl) ⟨6857054, by rfl⟩ : syracuseStep 9142739 = 13714109) B13714109
theorem B3613139 : Blo 1186410 3613139 := bstep (se 1 (by rfl) ⟨2709854, by rfl⟩ : syracuseStep 3613139 = 5419709) B5419709
theorem B2109276875 : Blo 1186410 2109276875 := bstep (se 1 (by rfl) ⟨1581957656, by rfl⟩ : syracuseStep 2109276875 = 3163915313) B3163915313
theorem B15205117 : Blo 1186410 15205117 := bstep (se 3 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 15205117 = 5701919) B5701919
theorem B1336423 : Blo 1186410 1336423 := bstep (se 1 (by rfl) ⟨1002317, by rfl⟩ : syracuseStep 1336423 = 2004635) B2004635
theorem B17106167 : Blo 1186410 17106167 := bstep (se 1 (by rfl) ⟨12829625, by rfl⟩ : syracuseStep 17106167 = 25659251) B25659251
theorem B1901819 : Blo 1186410 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B4064521 : Blo 1186410 4064521 := bstep (se 2 (by rfl) ⟨1524195, by rfl⟩ : syracuseStep 4064521 = 3048391) B3048391
theorem B3007763 : Blo 1186410 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B2254159 : Blo 1186410 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B2672027 : Blo 1186410 2672027 := bstep (se 1 (by rfl) ⟨2004020, by rfl⟩ : syracuseStep 2672027 = 4008041) B4008041
theorem B3007975 : Blo 1186410 3007975 := bstep (se 1 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 3007975 = 4511963) B4511963
theorem B3802601 : Blo 1186410 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B92555207 : Blo 1186410 92555207 := bstep (se 1 (by rfl) ⟨69416405, by rfl⟩ : syracuseStep 92555207 = 138832811) B138832811
theorem B4507757 : Blo 1186410 4507757 := bstep (se 3 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 4507757 = 1690409) B1690409
theorem B1779935 : Blo 1186410 1779935 := bstep (se 1 (by rfl) ⟨1334951, by rfl⟩ : syracuseStep 1779935 = 2669903) B2669903
theorem B3090655 : Blo 1186410 3090655 := bstep (se 1 (by rfl) ⟨2317991, by rfl⟩ : syracuseStep 3090655 = 4635983) B4635983
theorem B1779995 : Blo 1186410 1779995 := bstep (se 1 (by rfl) ⟨1334996, by rfl⟩ : syracuseStep 1779995 = 2669993) B2669993
theorem B1780127 : Blo 1186410 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B9628217 : Blo 1186410 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B1780319 : Blo 1186410 1780319 := bstep (se 1 (by rfl) ⟨1335239, by rfl⟩ : syracuseStep 1780319 = 2670479) B2670479
theorem B6417083 : Blo 1186410 6417083 := bstep (se 1 (by rfl) ⟨4812812, by rfl⟩ : syracuseStep 6417083 = 9625625) B9625625
theorem B1780649 : Blo 1186410 1780649 := bstep (se 2 (by rfl) ⟨667743, by rfl⟩ : syracuseStep 1780649 = 1335487) B1335487
theorem B1780679 : Blo 1186410 1780679 := bstep (se 1 (by rfl) ⟨1335509, by rfl⟩ : syracuseStep 1780679 = 2671019) B2671019
theorem B5073961 : Blo 1186410 5073961 := bstep (se 2 (by rfl) ⟨1902735, by rfl⟩ : syracuseStep 5073961 = 3805471) B3805471
theorem B1780799 : Blo 1186410 1780799 := bstep (se 1 (by rfl) ⟨1335599, by rfl⟩ : syracuseStep 1780799 = 2671199) B2671199
theorem B1502383 : Blo 1186410 1502383 := bstep (se 1 (by rfl) ⟨1126787, by rfl⟩ : syracuseStep 1502383 = 2253575) B2253575
theorem B32500939 : Blo 1186410 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B4009175 : Blo 1186410 4009175 := bstep (se 1 (by rfl) ⟨3006881, by rfl⟩ : syracuseStep 4009175 = 6013763) B6013763
theorem B2002151 : Blo 1186410 2002151 := bstep (se 1 (by rfl) ⟨1501613, by rfl⟩ : syracuseStep 2002151 = 3003227) B3003227
theorem B1781039 : Blo 1186410 1781039 := bstep (se 1 (by rfl) ⟨1335779, by rfl⟩ : syracuseStep 1781039 = 2671559) B2671559
theorem B3378505 : Blo 1186410 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B4009337 : Blo 1186410 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1781225 : Blo 1186410 1781225 := bstep (se 2 (by rfl) ⟨667959, by rfl⟩ : syracuseStep 1781225 = 1335919) B1335919
theorem B1781279 : Blo 1186410 1781279 := bstep (se 1 (by rfl) ⟨1335959, by rfl⟩ : syracuseStep 1781279 = 2671919) B2671919
theorem B3378779 : Blo 1186410 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B1781369 : Blo 1186410 1781369 := bstep (se 2 (by rfl) ⟨668013, by rfl⟩ : syracuseStep 1781369 = 1336027) B1336027
theorem B3378847 : Blo 1186410 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B1806047 : Blo 1186410 1806047 := bstep (se 1 (by rfl) ⟨1354535, by rfl⟩ : syracuseStep 1806047 = 2709071) B2709071
theorem B4009715 : Blo 1186410 4009715 := bstep (se 1 (by rfl) ⟨3007286, by rfl⟩ : syracuseStep 4009715 = 6014573) B6014573
theorem B3608345 : Blo 1186410 3608345 := bstep (se 2 (by rfl) ⟨1353129, by rfl⟩ : syracuseStep 3608345 = 2706259) B2706259
theorem B1781615 : Blo 1186410 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B6762365 : Blo 1186410 6762365 := bstep (se 3 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 6762365 = 2535887) B2535887
theorem B1781867 : Blo 1186410 1781867 := bstep (se 1 (by rfl) ⟨1336400, by rfl⟩ : syracuseStep 1781867 = 2672801) B2672801
theorem B1187835 : Blo 1186410 1187835 := bstep (se 1 (by rfl) ⟨890876, by rfl⟩ : syracuseStep 1187835 = 1781753) B1781753
theorem B6009065 : Blo 1186410 6009065 := bstep (se 2 (by rfl) ⟨2253399, by rfl⟩ : syracuseStep 6009065 = 4506799) B4506799
theorem B3379553 : Blo 1186410 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B10834339 : Blo 1186410 10834339 := bstep (se 1 (by rfl) ⟨8125754, by rfl⟩ : syracuseStep 10834339 = 16251509) B16251509
theorem B5419507 : Blo 1186410 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B1782299 : Blo 1186410 1782299 := bstep (se 1 (by rfl) ⟨1336724, by rfl⟩ : syracuseStep 1782299 = 2673449) B2673449
theorem B5075617 : Blo 1186410 5075617 := bstep (se 2 (by rfl) ⟨1903356, by rfl⟩ : syracuseStep 5075617 = 3806713) B3806713
theorem B1782479 : Blo 1186410 1782479 := bstep (se 1 (by rfl) ⟨1336859, by rfl⟩ : syracuseStep 1782479 = 2673719) B2673719
theorem B8557321 : Blo 1186410 8557321 := bstep (se 2 (by rfl) ⟨3208995, by rfl⟩ : syracuseStep 8557321 = 6417991) B6417991
theorem B4510475 : Blo 1186410 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B3380123 : Blo 1186410 3380123 := bstep (se 1 (by rfl) ⟨2535092, by rfl⟩ : syracuseStep 3380123 = 5070185) B5070185
theorem B6419503 : Blo 1186410 6419503 := bstep (se 1 (by rfl) ⟨4814627, by rfl⟩ : syracuseStep 6419503 = 9629255) B9629255
theorem B3855431 : Blo 1186410 3855431 := bstep (se 1 (by rfl) ⟨2891573, by rfl⟩ : syracuseStep 3855431 = 5783147) B5783147
theorem B6419677 : Blo 1186410 6419677 := bstep (se 3 (by rfl) ⟨1203689, by rfl⟩ : syracuseStep 6419677 = 2407379) B2407379
theorem B2709215 : Blo 1186410 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B3806945 : Blo 1186410 3806945 := bstep (se 2 (by rfl) ⟨1427604, by rfl⟩ : syracuseStep 3806945 = 2855209) B2855209
theorem B3004199 : Blo 1186410 3004199 := bstep (se 1 (by rfl) ⟨2253149, by rfl⟩ : syracuseStep 3004199 = 4506299) B4506299
theorem B3807175 : Blo 1186410 3807175 := bstep (se 1 (by rfl) ⟨2855381, by rfl⟩ : syracuseStep 3807175 = 5710763) B5710763
theorem B1603579 : Blo 1186410 1603579 := bstep (se 1 (by rfl) ⟨1202684, by rfl⟩ : syracuseStep 1603579 = 2405369) B2405369
theorem B15227261 : Blo 1186410 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B13531697 : Blo 1186410 13531697 := bstep (se 2 (by rfl) ⟨5074386, by rfl⟩ : syracuseStep 13531697 = 10148773) B10148773
theorem B65018485 : Blo 1186410 65018485 := bstep (se 5 (by rfl) ⟨3047741, by rfl⟩ : syracuseStep 65018485 = 6095483) B6095483
theorem B1186431 : Blo 1186410 1186431 := bstep (se 1 (by rfl) ⟨889823, by rfl⟩ : syracuseStep 1186431 = 1779647) B1779647
theorem B1186555 : Blo 1186410 1186555 := bstep (se 1 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 1186555 = 1779833) B1779833
theorem B15219575 : Blo 1186410 15219575 := bstep (se 1 (by rfl) ⟨11414681, by rfl⟩ : syracuseStep 15219575 = 22829363) B22829363
theorem B20282237 : Blo 1186410 20282237 := bstep (se 3 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 20282237 = 7605839) B7605839
theorem B1186811 : Blo 1186410 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B1186847 : Blo 1186410 1186847 := bstep (se 1 (by rfl) ⟨890135, by rfl⟩ : syracuseStep 1186847 = 1780271) B1780271
theorem B5069945 : Blo 1186410 5069945 := bstep (se 2 (by rfl) ⟨1901229, by rfl⟩ : syracuseStep 5069945 = 3802459) B3802459
theorem B5012711 : Blo 1186410 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B1187135 : Blo 1186410 1187135 := bstep (se 1 (by rfl) ⟨890351, by rfl⟩ : syracuseStep 1187135 = 1780703) B1780703
theorem B9018701 : Blo 1186410 9018701 := bstep (se 3 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 9018701 = 3382013) B3382013
theorem B6757739 : Blo 1186410 6757739 := bstep (se 1 (by rfl) ⟨5068304, by rfl⟩ : syracuseStep 6757739 = 10136609) B10136609
theorem B6766031 : Blo 1186410 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B2670047 : Blo 1186410 2670047 := bstep (se 1 (by rfl) ⟨2002535, by rfl⟩ : syracuseStep 2670047 = 4005071) B4005071
theorem B17350139 : Blo 1186410 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B1187431 : Blo 1186410 1187431 := bstep (se 1 (by rfl) ⟨890573, by rfl⟩ : syracuseStep 1187431 = 1781147) B1781147
theorem B3210877 : Blo 1186410 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B2670299 : Blo 1186410 2670299 := bstep (se 1 (by rfl) ⟨2002724, by rfl⟩ : syracuseStep 2670299 = 4005449) B4005449
theorem B3006305 : Blo 1186410 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B1187711 : Blo 1186410 1187711 := bstep (se 1 (by rfl) ⟨890783, by rfl⟩ : syracuseStep 1187711 = 1781567) B1781567
theorem B62504867 : Blo 1186410 62504867 := bstep (se 1 (by rfl) ⟨46878650, by rfl⟩ : syracuseStep 62504867 = 93757301) B93757301
theorem B3800999 : Blo 1186410 3800999 := bstep (se 1 (by rfl) ⟨2850749, by rfl⟩ : syracuseStep 3800999 = 5701499) B5701499
theorem B105488351 : Blo 1186410 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B2670569 : Blo 1186410 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B1187911 : Blo 1186410 1187911 := bstep (se 1 (by rfl) ⟨890933, by rfl⟩ : syracuseStep 1187911 = 1781867) B1781867
theorem B4006043 : Blo 1186410 4006043 := bstep (se 1 (by rfl) ⟨3004532, by rfl⟩ : syracuseStep 4006043 = 6009065) B6009065
theorem B2253035 : Blo 1186410 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B6095159 : Blo 1186410 6095159 := bstep (se 1 (by rfl) ⟨4571369, by rfl⟩ : syracuseStep 6095159 = 9142739) B9142739
theorem B2408759 : Blo 1186410 2408759 := bstep (se 1 (by rfl) ⟨1806569, by rfl⟩ : syracuseStep 2408759 = 3613139) B3613139
theorem B1188199 : Blo 1186410 1188199 := bstep (se 1 (by rfl) ⟨891149, by rfl⟩ : syracuseStep 1188199 = 1782299) B1782299
theorem B1188319 : Blo 1186410 1188319 := bstep (se 1 (by rfl) ⟨891239, by rfl⟩ : syracuseStep 1188319 = 1782479) B1782479
theorem B3006983 : Blo 1186410 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B2253415 : Blo 1186410 2253415 := bstep (se 1 (by rfl) ⟨1690061, by rfl⟩ : syracuseStep 2253415 = 3380123) B3380123
theorem B7226009 : Blo 1186410 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B5071517 : Blo 1186410 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B11404111 : Blo 1186410 11404111 := bstep (se 1 (by rfl) ⟨8553083, by rfl⟩ : syracuseStep 11404111 = 17106167) B17106167
theorem B6767489 : Blo 1186410 6767489 := bstep (se 2 (by rfl) ⟨2537808, by rfl⟩ : syracuseStep 6767489 = 5075617) B5075617
theorem B16483493 : Blo 1186410 16483493 := bstep (se 4 (by rfl) ⟨1545327, by rfl⟩ : syracuseStep 16483493 = 3090655) B3090655
theorem B2138105 : Blo 1186410 2138105 := bstep (se 2 (by rfl) ⟨801789, by rfl⟩ : syracuseStep 2138105 = 1603579) B1603579
theorem B61703471 : Blo 1186410 61703471 := bstep (se 1 (by rfl) ⟨46277603, by rfl⟩ : syracuseStep 61703471 = 92555207) B92555207
theorem B10151507 : Blo 1186410 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B9021131 : Blo 1186410 9021131 := bstep (se 1 (by rfl) ⟨6765848, by rfl⟩ : syracuseStep 9021131 = 13531697) B13531697
theorem B4278055 : Blo 1186410 4278055 := bstep (se 1 (by rfl) ⟨3208541, by rfl⟩ : syracuseStep 4278055 = 6417083) B6417083
theorem B2672783 : Blo 1186410 2672783 := bstep (se 1 (by rfl) ⟨2004587, by rfl⟩ : syracuseStep 2672783 = 4009175) B4009175
theorem B2672891 : Blo 1186410 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B1780031 : Blo 1186410 1780031 := bstep (se 1 (by rfl) ⟨1335023, by rfl⟩ : syracuseStep 1780031 = 2670047) B2670047
theorem B1780199 : Blo 1186410 1780199 := bstep (se 1 (by rfl) ⟨1335149, by rfl⟩ : syracuseStep 1780199 = 2670299) B2670299
theorem B2673143 : Blo 1186410 2673143 := bstep (se 1 (by rfl) ⟨2004857, by rfl⟩ : syracuseStep 2673143 = 4009715) B4009715
theorem B4508243 : Blo 1186410 4508243 := bstep (se 1 (by rfl) ⟨3381182, by rfl⟩ : syracuseStep 4508243 = 6762365) B6762365
theorem B2533999 : Blo 1186410 2533999 := bstep (se 1 (by rfl) ⟨1900499, by rfl⟩ : syracuseStep 2533999 = 3800999) B3800999
theorem B1780379 : Blo 1186410 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B34237349 : Blo 1186410 34237349 := bstep (se 4 (by rfl) ⟨3209751, by rfl⟩ : syracuseStep 34237349 = 6419503) B6419503
theorem B9022589 : Blo 1186410 9022589 := bstep (se 3 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 9022589 = 3383471) B3383471
theorem B1406184583 : Blo 1186410 1406184583 := bstep (se 1 (by rfl) ⟨1054638437, by rfl⟩ : syracuseStep 1406184583 = 2109276875) B2109276875
theorem B6761657 : Blo 1186410 6761657 := bstep (se 2 (by rfl) ⟨2535621, by rfl⟩ : syracuseStep 6761657 = 5071243) B5071243
theorem B14445785 : Blo 1186410 14445785 := bstep (se 2 (by rfl) ⟨5417169, by rfl⟩ : syracuseStep 14445785 = 10834339) B10834339
theorem B86691313 : Blo 1186410 86691313 := bstep (se 2 (by rfl) ⟨32509242, by rfl⟩ : syracuseStep 86691313 = 65018485) B65018485
theorem B1781351 : Blo 1186410 1781351 := bstep (se 1 (by rfl) ⟨1336013, by rfl⟩ : syracuseStep 1781351 = 2672027) B2672027
theorem B2535067 : Blo 1186410 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B1806143 : Blo 1186410 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B2002799 : Blo 1186410 2002799 := bstep (se 1 (by rfl) ⟨1502099, by rfl⟩ : syracuseStep 2002799 = 3004199) B3004199
theorem B1781897 : Blo 1186410 1781897 := bstep (se 2 (by rfl) ⟨668211, by rfl⟩ : syracuseStep 1781897 = 1336423) B1336423
theorem B2003177 : Blo 1186410 2003177 := bstep (se 2 (by rfl) ⟨751191, by rfl⟩ : syracuseStep 2003177 = 1502383) B1502383
theorem B5419361 : Blo 1186410 5419361 := bstep (se 2 (by rfl) ⟨2032260, by rfl⟩ : syracuseStep 5419361 = 4064521) B4064521
theorem B6418811 : Blo 1186410 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B10146383 : Blo 1186410 10146383 := bstep (se 1 (by rfl) ⟨7609787, by rfl⟩ : syracuseStep 10146383 = 15219575) B15219575
theorem B13521491 : Blo 1186410 13521491 := bstep (se 1 (by rfl) ⟨10141118, by rfl⟩ : syracuseStep 13521491 = 20282237) B20282237
theorem B4010633 : Blo 1186410 4010633 := bstep (se 2 (by rfl) ⟨1503987, by rfl⟩ : syracuseStep 4010633 = 3007975) B3007975
theorem B9622253 : Blo 1186410 9622253 := bstep (se 3 (by rfl) ⟨1804172, by rfl⟩ : syracuseStep 9622253 = 3608345) B3608345
theorem B3379963 : Blo 1186410 3379963 := bstep (se 1 (by rfl) ⟨2534972, by rfl⟩ : syracuseStep 3379963 = 5069945) B5069945
theorem B4281169 : Blo 1186410 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B4510687 : Blo 1186410 4510687 := bstep (se 1 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 4510687 = 6766031) B6766031
theorem B2004203 : Blo 1186410 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B5076233 : Blo 1186410 5076233 := bstep (se 2 (by rfl) ⟨1903587, by rfl⟩ : syracuseStep 5076233 = 3807175) B3807175
theorem B41669911 : Blo 1186410 41669911 := bstep (se 1 (by rfl) ⟨31252433, by rfl⟩ : syracuseStep 41669911 = 62504867) B62504867
theorem B70325567 : Blo 1186410 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B2570287 : Blo 1186410 2570287 := bstep (se 1 (by rfl) ⟨1927715, by rfl⟩ : syracuseStep 2570287 = 3855431) B3855431
theorem B2005175 : Blo 1186410 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B20273489 : Blo 1186410 20273489 := bstep (se 2 (by rfl) ⟨7602558, by rfl⟩ : syracuseStep 20273489 = 15205117) B15205117
theorem B11409761 : Blo 1186410 11409761 := bstep (se 2 (by rfl) ⟨4278660, by rfl⟩ : syracuseStep 11409761 = 8557321) B8557321
theorem B2537963 : Blo 1186410 2537963 := bstep (se 1 (by rfl) ⟨1903472, by rfl⟩ : syracuseStep 2537963 = 3806945) B3806945
theorem B6765281 : Blo 1186410 6765281 := bstep (se 2 (by rfl) ⟨2536980, by rfl⟩ : syracuseStep 6765281 = 5073961) B5073961
theorem B3005171 : Blo 1186410 3005171 := bstep (se 1 (by rfl) ⟨2253878, by rfl⟩ : syracuseStep 3005171 = 4507757) B4507757
theorem B1186623 : Blo 1186410 1186623 := bstep (se 1 (by rfl) ⟨889967, by rfl⟩ : syracuseStep 1186623 = 1779935) B1779935
theorem B1186663 : Blo 1186410 1186663 := bstep (se 1 (by rfl) ⟨889997, by rfl⟩ : syracuseStep 1186663 = 1779995) B1779995
theorem B43334585 : Blo 1186410 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B1186751 : Blo 1186410 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B8559569 : Blo 1186410 8559569 := bstep (se 2 (by rfl) ⟨3209838, by rfl⟩ : syracuseStep 8559569 = 6419677) B6419677
theorem B1186879 : Blo 1186410 1186879 := bstep (se 1 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 1186879 = 1780319) B1780319
theorem B4504673 : Blo 1186410 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B3005545 : Blo 1186410 3005545 := bstep (se 2 (by rfl) ⟨1127079, by rfl⟩ : syracuseStep 3005545 = 2254159) B2254159
theorem B1187099 : Blo 1186410 1187099 := bstep (se 1 (by rfl) ⟨890324, by rfl⟩ : syracuseStep 1187099 = 1780649) B1780649
theorem B1187119 : Blo 1186410 1187119 := bstep (se 1 (by rfl) ⟨890339, by rfl⟩ : syracuseStep 1187119 = 1780679) B1780679
theorem B1187199 : Blo 1186410 1187199 := bstep (se 1 (by rfl) ⟨890399, by rfl⟩ : syracuseStep 1187199 = 1780799) B1780799
theorem B1334767 : Blo 1186410 1334767 := bstep (se 1 (by rfl) ⟨1001075, by rfl⟩ : syracuseStep 1334767 = 2002151) B2002151
theorem B3341807 : Blo 1186410 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B1187359 : Blo 1186410 1187359 := bstep (se 1 (by rfl) ⟨890519, by rfl⟩ : syracuseStep 1187359 = 1781039) B1781039
theorem B4505129 : Blo 1186410 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B6012467 : Blo 1186410 6012467 := bstep (se 1 (by rfl) ⟨4509350, by rfl⟩ : syracuseStep 6012467 = 9018701) B9018701
theorem B4505159 : Blo 1186410 4505159 := bstep (se 1 (by rfl) ⟨3378869, by rfl⟩ : syracuseStep 4505159 = 6757739) B6757739
theorem B1187483 : Blo 1186410 1187483 := bstep (se 1 (by rfl) ⟨890612, by rfl⟩ : syracuseStep 1187483 = 1781225) B1781225
theorem B11566759 : Blo 1186410 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B1187519 : Blo 1186410 1187519 := bstep (se 1 (by rfl) ⟨890639, by rfl⟩ : syracuseStep 1187519 = 1781279) B1781279
theorem B2252519 : Blo 1186410 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B1187579 : Blo 1186410 1187579 := bstep (se 1 (by rfl) ⟨890684, by rfl⟩ : syracuseStep 1187579 = 1781369) B1781369
theorem B1204031 : Blo 1186410 1204031 := bstep (se 1 (by rfl) ⟨903023, by rfl⟩ : syracuseStep 1204031 = 1806047) B1806047
theorem B1187743 : Blo 1186410 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B1187931 : Blo 1186410 1187931 := bstep (se 1 (by rfl) ⟨890948, by rfl⟩ : syracuseStep 1187931 = 1781897) B1781897
theorem B2670695 : Blo 1186410 2670695 := bstep (se 1 (by rfl) ⟨2003021, by rfl⟩ : syracuseStep 2670695 = 4006043) B4006043
theorem B1335451 : Blo 1186410 1335451 := bstep (se 1 (by rfl) ⟨1001588, by rfl⟩ : syracuseStep 1335451 = 2003177) B2003177
theorem B4063439 : Blo 1186410 4063439 := bstep (se 1 (by rfl) ⟨3047579, by rfl⟩ : syracuseStep 4063439 = 6095159) B6095159
theorem B3612907 : Blo 1186410 3612907 := bstep (se 1 (by rfl) ⟨2709680, by rfl⟩ : syracuseStep 3612907 = 5419361) B5419361
theorem B4817339 : Blo 1186410 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B6414835 : Blo 1186410 6414835 := bstep (se 1 (by rfl) ⟨4811126, by rfl⟩ : syracuseStep 6414835 = 9622253) B9622253
theorem B1336135 : Blo 1186410 1336135 := bstep (se 1 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 1336135 = 2004203) B2004203
theorem B3384155 : Blo 1186410 3384155 := bstep (se 1 (by rfl) ⟨2538116, by rfl⟩ : syracuseStep 3384155 = 5076233) B5076233
theorem B46883711 : Blo 1186410 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B4506617 : Blo 1186410 4506617 := bstep (se 2 (by rfl) ⟨1689981, by rfl⟩ : syracuseStep 4506617 = 3379963) B3379963
theorem B6767671 : Blo 1186410 6767671 := bstep (se 1 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 6767671 = 10151507) B10151507
theorem B15205481 : Blo 1186410 15205481 := bstep (se 2 (by rfl) ⟨5702055, by rfl⟩ : syracuseStep 15205481 = 11404111) B11404111
theorem B6014087 : Blo 1186410 6014087 := bstep (se 1 (by rfl) ⟨4510565, by rfl⟩ : syracuseStep 6014087 = 9021131) B9021131
theorem B6014249 : Blo 1186410 6014249 := bstep (se 2 (by rfl) ⟨2255343, by rfl⟩ : syracuseStep 6014249 = 4510687) B4510687
theorem B1336783 : Blo 1186410 1336783 := bstep (se 1 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 1336783 = 2005175) B2005175
theorem B4007393 : Blo 1186410 4007393 := bstep (se 2 (by rfl) ⟨1502772, by rfl⟩ : syracuseStep 4007393 = 3005545) B3005545
theorem B1874912777 : Blo 1186410 1874912777 := bstep (se 2 (by rfl) ⟨703092291, by rfl⟩ : syracuseStep 1874912777 = 1406184583) B1406184583
theorem B55559881 : Blo 1186410 55559881 := bstep (se 2 (by rfl) ⟨20834955, by rfl⟩ : syracuseStep 55559881 = 41669911) B41669911
theorem B22824899 : Blo 1186410 22824899 := bstep (se 1 (by rfl) ⟨17118674, by rfl⟩ : syracuseStep 22824899 = 34237349) B34237349
theorem B1779689 : Blo 1186410 1779689 := bstep (se 2 (by rfl) ⟨667383, by rfl⟩ : syracuseStep 1779689 = 1334767) B1334767
theorem B1605839 : Blo 1186410 1605839 := bstep (se 1 (by rfl) ⟨1204379, by rfl⟩ : syracuseStep 1605839 = 2408759) B2408759
theorem B6015059 : Blo 1186410 6015059 := bstep (se 1 (by rfl) ⟨4511294, by rfl⟩ : syracuseStep 6015059 = 9022589) B9022589
theorem B4507771 : Blo 1186410 4507771 := bstep (se 1 (by rfl) ⟨3380828, by rfl⟩ : syracuseStep 4507771 = 6761657) B6761657
theorem B4008311 : Blo 1186410 4008311 := bstep (se 1 (by rfl) ⟨3006233, by rfl⟩ : syracuseStep 4008311 = 6012467) B6012467
theorem B5704073 : Blo 1186410 5704073 := bstep (se 2 (by rfl) ⟨2139027, by rfl⟩ : syracuseStep 5704073 = 4278055) B4278055
theorem B1501679 : Blo 1186410 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B3427049 : Blo 1186410 3427049 := bstep (se 2 (by rfl) ⟨1285143, by rfl⟩ : syracuseStep 3427049 = 2570287) B2570287
theorem B9014327 : Blo 1186410 9014327 := bstep (se 1 (by rfl) ⟨6760745, by rfl⟩ : syracuseStep 9014327 = 13521491) B13521491
theorem B2673755 : Blo 1186410 2673755 := bstep (se 1 (by rfl) ⟨2005316, by rfl⟩ : syracuseStep 2673755 = 4010633) B4010633
theorem B6008093 : Blo 1186410 6008093 := bstep (se 3 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 6008093 = 2253035) B2253035
theorem B10988995 : Blo 1186410 10988995 := bstep (se 1 (by rfl) ⟨8241746, by rfl⟩ : syracuseStep 10988995 = 16483493) B16483493
theorem B3378665 : Blo 1186410 3378665 := bstep (se 2 (by rfl) ⟨1266999, by rfl⟩ : syracuseStep 3378665 = 2533999) B2533999
theorem B41135647 : Blo 1186410 41135647 := bstep (se 1 (by rfl) ⟨30851735, by rfl⟩ : syracuseStep 41135647 = 61703471) B61703471
theorem B17116829 : Blo 1186410 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B1781855 : Blo 1186410 1781855 := bstep (se 1 (by rfl) ⟨1336391, by rfl⟩ : syracuseStep 1781855 = 2672783) B2672783
theorem B1781927 : Blo 1186410 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B7606507 : Blo 1186410 7606507 := bstep (se 1 (by rfl) ⟨5704880, by rfl⟩ : syracuseStep 7606507 = 11409761) B11409761
theorem B1691975 : Blo 1186410 1691975 := bstep (se 1 (by rfl) ⟨1268981, by rfl⟩ : syracuseStep 1691975 = 2537963) B2537963
theorem B1782095 : Blo 1186410 1782095 := bstep (se 1 (by rfl) ⟨1336571, by rfl⟩ : syracuseStep 1782095 = 2673143) B2673143
theorem B4510187 : Blo 1186410 4510187 := bstep (se 1 (by rfl) ⟨3382640, by rfl⟩ : syracuseStep 4510187 = 6765281) B6765281
theorem B2003447 : Blo 1186410 2003447 := bstep (se 1 (by rfl) ⟨1502585, by rfl⟩ : syracuseStep 2003447 = 3005171) B3005171
theorem B28889723 : Blo 1186410 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B5706379 : Blo 1186410 5706379 := bstep (se 1 (by rfl) ⟨4279784, by rfl⟩ : syracuseStep 5706379 = 8559569) B8559569
theorem B3003115 : Blo 1186410 3003115 := bstep (se 1 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 3003115 = 4504673) B4504673
theorem B9630523 : Blo 1186410 9630523 := bstep (se 1 (by rfl) ⟨7222892, by rfl⟩ : syracuseStep 9630523 = 14445785) B14445785
theorem B3380089 : Blo 1186410 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B15422345 : Blo 1186410 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B3003419 : Blo 1186410 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B3003439 : Blo 1186410 3003439 := bstep (se 1 (by rfl) ⟨2252579, by rfl⟩ : syracuseStep 3003439 = 4505159) B4505159
theorem B2004655 : Blo 1186410 2004655 := bstep (se 1 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 2004655 = 3006983) B3006983
theorem B6764255 : Blo 1186410 6764255 := bstep (se 1 (by rfl) ⟨5073191, by rfl⟩ : syracuseStep 6764255 = 10146383) B10146383
theorem B3381011 : Blo 1186410 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B4511659 : Blo 1186410 4511659 := bstep (se 1 (by rfl) ⟨3383744, by rfl⟩ : syracuseStep 4511659 = 6767489) B6767489
theorem B19265525 : Blo 1186410 19265525 := bstep (se 5 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 19265525 = 1806143) B1806143
theorem B3004553 : Blo 1186410 3004553 := bstep (se 2 (by rfl) ⟨1126707, by rfl⟩ : syracuseStep 3004553 = 2253415) B2253415
theorem B5708225 : Blo 1186410 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B1186687 : Blo 1186410 1186687 := bstep (se 1 (by rfl) ⟨890015, by rfl⟩ : syracuseStep 1186687 = 1780031) B1780031
theorem B13515659 : Blo 1186410 13515659 := bstep (se 1 (by rfl) ⟨10136744, by rfl⟩ : syracuseStep 13515659 = 20273489) B20273489
theorem B1186799 : Blo 1186410 1186799 := bstep (se 1 (by rfl) ⟨890099, by rfl⟩ : syracuseStep 1186799 = 1780199) B1780199
theorem B3005495 : Blo 1186410 3005495 := bstep (se 1 (by rfl) ⟨2254121, by rfl⟩ : syracuseStep 3005495 = 4508243) B4508243
theorem B1186919 : Blo 1186410 1186919 := bstep (se 1 (by rfl) ⟨890189, by rfl⟩ : syracuseStep 1186919 = 1780379) B1780379
theorem B115588417 : Blo 1186410 115588417 := bstep (se 2 (by rfl) ⟨43345656, by rfl⟩ : syracuseStep 115588417 = 86691313) B86691313
theorem B3210749 : Blo 1186410 3210749 := bstep (se 3 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 3210749 = 1204031) B1204031
theorem B2227871 : Blo 1186410 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B1187567 : Blo 1186410 1187567 := bstep (se 1 (by rfl) ⟨890675, by rfl⟩ : syracuseStep 1187567 = 1781351) B1781351
theorem B1335199 : Blo 1186410 1335199 := bstep (se 1 (by rfl) ⟨1001399, by rfl⟩ : syracuseStep 1335199 = 2002799) B2002799
theorem B1425403 : Blo 1186410 1425403 := bstep (se 1 (by rfl) ⟨1069052, by rfl⟩ : syracuseStep 1425403 = 2138105) B2138105
theorem B1187903 : Blo 1186410 1187903 := bstep (se 1 (by rfl) ⟨890927, by rfl⟩ : syracuseStep 1187903 = 1781855) B1781855
theorem B1187951 : Blo 1186410 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B1188063 : Blo 1186410 1188063 := bstep (se 1 (by rfl) ⟨891047, by rfl⟩ : syracuseStep 1188063 = 1782095) B1782095
theorem B3211559 : Blo 1186410 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B10142009 : Blo 1186410 10142009 := bstep (se 2 (by rfl) ⟨3803253, by rfl⟩ : syracuseStep 10142009 = 7606507) B7606507
theorem B3006791 : Blo 1186410 3006791 := bstep (se 1 (by rfl) ⟨2255093, by rfl⟩ : syracuseStep 3006791 = 4510187) B4510187
theorem B1335631 : Blo 1186410 1335631 := bstep (se 1 (by rfl) ⟨1001723, by rfl⟩ : syracuseStep 1335631 = 2003447) B2003447
theorem B19259815 : Blo 1186410 19259815 := bstep (se 1 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 19259815 = 28889723) B28889723
theorem B10281563 : Blo 1186410 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B8553113 : Blo 1186410 8553113 := bstep (se 2 (by rfl) ⟨3207417, by rfl⟩ : syracuseStep 8553113 = 6414835) B6414835
theorem B2671595 : Blo 1186410 2671595 := bstep (se 1 (by rfl) ⟨2003696, by rfl⟩ : syracuseStep 2671595 = 4007393) B4007393
theorem B4506785 : Blo 1186410 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B2254007 : Blo 1186410 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B19268837 : Blo 1186410 19268837 := bstep (se 4 (by rfl) ⟨1806453, by rfl⟩ : syracuseStep 19268837 = 3612907) B3612907
theorem B2672207 : Blo 1186410 2672207 := bstep (se 1 (by rfl) ⟨2004155, by rfl⟩ : syracuseStep 2672207 = 4008311) B4008311
theorem B3802715 : Blo 1186410 3802715 := bstep (se 1 (by rfl) ⟨2852036, by rfl⟩ : syracuseStep 3802715 = 5704073) B5704073
theorem B5940989 : Blo 1186410 5940989 := bstep (se 3 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 5940989 = 2227871) B2227871
theorem B154117889 : Blo 1186410 154117889 := bstep (se 2 (by rfl) ⟨57794208, by rfl⟩ : syracuseStep 154117889 = 115588417) B115588417
theorem B54847529 : Blo 1186410 54847529 := bstep (se 2 (by rfl) ⟨20567823, by rfl⟩ : syracuseStep 54847529 = 41135647) B41135647
theorem B2672873 : Blo 1186410 2672873 := bstep (se 2 (by rfl) ⟨1002327, by rfl⟩ : syracuseStep 2672873 = 2004655) B2004655
theorem B2140499 : Blo 1186410 2140499 := bstep (se 1 (by rfl) ⟨1605374, by rfl⟩ : syracuseStep 2140499 = 3210749) B3210749
theorem B1780265 : Blo 1186410 1780265 := bstep (se 2 (by rfl) ⟨667599, by rfl⟩ : syracuseStep 1780265 = 1335199) B1335199
theorem B6015545 : Blo 1186410 6015545 := bstep (se 2 (by rfl) ⟨2255829, by rfl⟩ : syracuseStep 6015545 = 4511659) B4511659
theorem B1780463 : Blo 1186410 1780463 := bstep (se 1 (by rfl) ⟨1335347, by rfl⟩ : syracuseStep 1780463 = 2670695) B2670695
theorem B1780601 : Blo 1186410 1780601 := bstep (se 2 (by rfl) ⟨667725, by rfl⟩ : syracuseStep 1780601 = 1335451) B1335451
theorem B2256103 : Blo 1186410 2256103 := bstep (se 1 (by rfl) ⟨1692077, by rfl⟩ : syracuseStep 2256103 = 3384155) B3384155
theorem B31255807 : Blo 1186410 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B2002279 : Blo 1186410 2002279 := bstep (se 1 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 2002279 = 3003419) B3003419
theorem B10136987 : Blo 1186410 10136987 := bstep (se 1 (by rfl) ⟨7602740, by rfl⟩ : syracuseStep 10136987 = 15205481) B15205481
theorem B4009391 : Blo 1186410 4009391 := bstep (se 1 (by rfl) ⟨3007043, by rfl⟩ : syracuseStep 4009391 = 6014087) B6014087
theorem B4009499 : Blo 1186410 4009499 := bstep (se 1 (by rfl) ⟨3007124, by rfl⟩ : syracuseStep 4009499 = 6014249) B6014249
theorem B12840697 : Blo 1186410 12840697 := bstep (se 2 (by rfl) ⟨4815261, by rfl⟩ : syracuseStep 12840697 = 9630523) B9630523
theorem B1781513 : Blo 1186410 1781513 := bstep (se 2 (by rfl) ⟨668067, by rfl⟩ : syracuseStep 1781513 = 1336135) B1336135
theorem B4509503 : Blo 1186410 4509503 := bstep (se 1 (by rfl) ⟨3382127, by rfl⟩ : syracuseStep 4509503 = 6764255) B6764255
theorem B15216599 : Blo 1186410 15216599 := bstep (se 1 (by rfl) ⟨11412449, by rfl⟩ : syracuseStep 15216599 = 22824899) B22824899
theorem B4010039 : Blo 1186410 4010039 := bstep (se 1 (by rfl) ⟨3007529, by rfl⟩ : syracuseStep 4010039 = 6015059) B6015059
theorem B9023561 : Blo 1186410 9023561 := bstep (se 2 (by rfl) ⟨3383835, by rfl⟩ : syracuseStep 9023561 = 6767671) B6767671
theorem B2003035 : Blo 1186410 2003035 := bstep (se 1 (by rfl) ⟨1502276, by rfl⟩ : syracuseStep 2003035 = 3004553) B3004553
theorem B3805483 : Blo 1186410 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B14651993 : Blo 1186410 14651993 := bstep (se 2 (by rfl) ⟨5494497, by rfl⟩ : syracuseStep 14651993 = 10988995) B10988995
theorem B1782377 : Blo 1186410 1782377 := bstep (se 2 (by rfl) ⟨668391, by rfl⟩ : syracuseStep 1782377 = 1336783) B1336783
theorem B6009551 : Blo 1186410 6009551 := bstep (se 1 (by rfl) ⟨4507163, by rfl⟩ : syracuseStep 6009551 = 9014327) B9014327
theorem B2003663 : Blo 1186410 2003663 := bstep (se 1 (by rfl) ⟨1502747, by rfl⟩ : syracuseStep 2003663 = 3005495) B3005495
theorem B1782503 : Blo 1186410 1782503 := bstep (se 1 (by rfl) ⟨1336877, by rfl⟩ : syracuseStep 1782503 = 2673755) B2673755
theorem B2708959 : Blo 1186410 2708959 := bstep (se 1 (by rfl) ⟨2031719, by rfl⟩ : syracuseStep 2708959 = 4063439) B4063439
theorem B6010361 : Blo 1186410 6010361 := bstep (se 2 (by rfl) ⟨2253885, by rfl⟩ : syracuseStep 6010361 = 4507771) B4507771
theorem B4282237 : Blo 1186410 4282237 := bstep (se 3 (by rfl) ⟨802919, by rfl⟩ : syracuseStep 4282237 = 1605839) B1605839
theorem B3004411 : Blo 1186410 3004411 := bstep (se 1 (by rfl) ⟨2253308, by rfl⟩ : syracuseStep 3004411 = 4506617) B4506617
theorem B7608505 : Blo 1186410 7608505 := bstep (se 2 (by rfl) ⟨2853189, by rfl⟩ : syracuseStep 7608505 = 5706379) B5706379
theorem B4511933 : Blo 1186410 4511933 := bstep (se 3 (by rfl) ⟨845987, by rfl⟩ : syracuseStep 4511933 = 1691975) B1691975
theorem B4004153 : Blo 1186410 4004153 := bstep (se 2 (by rfl) ⟨1501557, by rfl⟩ : syracuseStep 4004153 = 3003115) B3003115
theorem B1249941851 : Blo 1186410 1249941851 := bstep (se 1 (by rfl) ⟨937456388, by rfl⟩ : syracuseStep 1249941851 = 1874912777) B1874912777
theorem B4004477 : Blo 1186410 4004477 := bstep (se 3 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 4004477 = 1501679) B1501679
theorem B1186459 : Blo 1186410 1186459 := bstep (se 1 (by rfl) ⟨889844, by rfl⟩ : syracuseStep 1186459 = 1779689) B1779689
theorem B12843683 : Blo 1186410 12843683 := bstep (se 1 (by rfl) ⟨9632762, by rfl⟩ : syracuseStep 12843683 = 19265525) B19265525
theorem B4004585 : Blo 1186410 4004585 := bstep (se 2 (by rfl) ⟨1501719, by rfl⟩ : syracuseStep 4004585 = 3003439) B3003439
theorem B2284699 : Blo 1186410 2284699 := bstep (se 1 (by rfl) ⟨1713524, by rfl⟩ : syracuseStep 2284699 = 3427049) B3427049
theorem B9010439 : Blo 1186410 9010439 := bstep (se 1 (by rfl) ⟨6757829, by rfl⟩ : syracuseStep 9010439 = 13515659) B13515659
theorem B4005395 : Blo 1186410 4005395 := bstep (se 1 (by rfl) ⟨3004046, by rfl⟩ : syracuseStep 4005395 = 6008093) B6008093
theorem B74079841 : Blo 1186410 74079841 := bstep (se 2 (by rfl) ⟨27779940, by rfl⟩ : syracuseStep 74079841 = 55559881) B55559881
theorem B2252443 : Blo 1186410 2252443 := bstep (se 1 (by rfl) ⟨1689332, by rfl⟩ : syracuseStep 2252443 = 3378665) B3378665
theorem B11411219 : Blo 1186410 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B7602149 : Blo 1186410 7602149 := bstep (se 4 (by rfl) ⟨712701, by rfl⟩ : syracuseStep 7602149 = 1425403) B1425403
theorem B2670713 : Blo 1186410 2670713 := bstep (se 2 (by rfl) ⟨1001517, by rfl⟩ : syracuseStep 2670713 = 2003035) B2003035
theorem B1188251 : Blo 1186410 1188251 := bstep (se 1 (by rfl) ⟨891188, by rfl⟩ : syracuseStep 1188251 = 1782377) B1782377
theorem B5702075 : Blo 1186410 5702075 := bstep (se 1 (by rfl) ⟨4276556, by rfl⟩ : syracuseStep 5702075 = 8553113) B8553113
theorem B4006367 : Blo 1186410 4006367 := bstep (se 1 (by rfl) ⟨3004775, by rfl⟩ : syracuseStep 4006367 = 6009551) B6009551
theorem B1335775 : Blo 1186410 1335775 := bstep (se 1 (by rfl) ⟨1001831, by rfl⟩ : syracuseStep 1335775 = 2003663) B2003663
theorem B1188335 : Blo 1186410 1188335 := bstep (se 1 (by rfl) ⟨891251, by rfl⟩ : syracuseStep 1188335 = 1782503) B1782503
theorem B12845891 : Blo 1186410 12845891 := bstep (se 1 (by rfl) ⟨9634418, by rfl⟩ : syracuseStep 12845891 = 19268837) B19268837
theorem B4006907 : Blo 1186410 4006907 := bstep (se 1 (by rfl) ⟨3005180, by rfl⟩ : syracuseStep 4006907 = 6010361) B6010361
theorem B102745259 : Blo 1186410 102745259 := bstep (se 1 (by rfl) ⟨77058944, by rfl⟩ : syracuseStep 102745259 = 154117889) B154117889
theorem B3007955 : Blo 1186410 3007955 := bstep (se 1 (by rfl) ⟨2255966, by rfl⟩ : syracuseStep 3007955 = 4511933) B4511933
theorem B1426999 : Blo 1186410 1426999 := bstep (se 1 (by rfl) ⟨1070249, by rfl⟩ : syracuseStep 1426999 = 2140499) B2140499
theorem B3008137 : Blo 1186410 3008137 := bstep (se 2 (by rfl) ⟨1128051, by rfl⟩ : syracuseStep 3008137 = 2256103) B2256103
theorem B41674409 : Blo 1186410 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B8562455 : Blo 1186410 8562455 := bstep (se 1 (by rfl) ⟨6421841, by rfl⟩ : syracuseStep 8562455 = 12843683) B12843683
theorem B98773121 : Blo 1186410 98773121 := bstep (se 2 (by rfl) ⟨37039920, by rfl⟩ : syracuseStep 98773121 = 74079841) B74079841
theorem B6006959 : Blo 1186410 6006959 := bstep (se 1 (by rfl) ⟨4505219, by rfl⟩ : syracuseStep 6006959 = 9010439) B9010439
theorem B2672927 : Blo 1186410 2672927 := bstep (se 1 (by rfl) ⟨2004695, by rfl⟩ : syracuseStep 2672927 = 4009391) B4009391
theorem B2672999 : Blo 1186410 2672999 := bstep (se 1 (by rfl) ⟨2004749, by rfl⟩ : syracuseStep 2672999 = 4009499) B4009499
theorem B10144399 : Blo 1186410 10144399 := bstep (se 1 (by rfl) ⟨7608299, by rfl⟩ : syracuseStep 10144399 = 15216599) B15216599
theorem B2673359 : Blo 1186410 2673359 := bstep (se 1 (by rfl) ⟨2005019, by rfl⟩ : syracuseStep 2673359 = 4010039) B4010039
theorem B6015707 : Blo 1186410 6015707 := bstep (se 1 (by rfl) ⟨4511780, by rfl⟩ : syracuseStep 6015707 = 9023561) B9023561
theorem B2141039 : Blo 1186410 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B6761339 : Blo 1186410 6761339 := bstep (se 1 (by rfl) ⟨5071004, by rfl⟩ : syracuseStep 6761339 = 10142009) B10142009
theorem B10144673 : Blo 1186410 10144673 := bstep (se 2 (by rfl) ⟨3804252, by rfl⟩ : syracuseStep 10144673 = 7608505) B7608505
theorem B5073977 : Blo 1186410 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B9767995 : Blo 1186410 9767995 := bstep (se 1 (by rfl) ⟨7325996, by rfl⟩ : syracuseStep 9767995 = 14651993) B14651993
theorem B1780841 : Blo 1186410 1780841 := bstep (se 2 (by rfl) ⟨667815, by rfl⟩ : syracuseStep 1780841 = 1335631) B1335631
theorem B1781063 : Blo 1186410 1781063 := bstep (se 1 (by rfl) ⟨1335797, by rfl⟩ : syracuseStep 1781063 = 2671595) B2671595
theorem B1781471 : Blo 1186410 1781471 := bstep (se 1 (by rfl) ⟨1336103, by rfl⟩ : syracuseStep 1781471 = 2672207) B2672207
theorem B2535143 : Blo 1186410 2535143 := bstep (se 1 (by rfl) ⟨1901357, by rfl⟩ : syracuseStep 2535143 = 3802715) B3802715
theorem B3960659 : Blo 1186410 3960659 := bstep (se 1 (by rfl) ⟨2970494, by rfl⟩ : syracuseStep 3960659 = 5940989) B5940989
theorem B36565019 : Blo 1186410 36565019 := bstep (se 1 (by rfl) ⟨27423764, by rfl⟩ : syracuseStep 36565019 = 54847529) B54847529
theorem B1781915 : Blo 1186410 1781915 := bstep (se 1 (by rfl) ⟨1336436, by rfl⟩ : syracuseStep 1781915 = 2672873) B2672873
theorem B833294567 : Blo 1186410 833294567 := bstep (se 1 (by rfl) ⟨624970925, by rfl⟩ : syracuseStep 833294567 = 1249941851) B1249941851
theorem B4010363 : Blo 1186410 4010363 := bstep (se 1 (by rfl) ⟨3007772, by rfl⟩ : syracuseStep 4010363 = 6015545) B6015545
theorem B30429917 : Blo 1186410 30429917 := bstep (se 3 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 30429917 = 11411219) B11411219
theorem B3003257 : Blo 1186410 3003257 := bstep (se 2 (by rfl) ⟨1126221, by rfl⟩ : syracuseStep 3003257 = 2252443) B2252443
theorem B5068099 : Blo 1186410 5068099 := bstep (se 1 (by rfl) ⟨3801074, by rfl⟩ : syracuseStep 5068099 = 7602149) B7602149
theorem B2004527 : Blo 1186410 2004527 := bstep (se 1 (by rfl) ⟨1503395, by rfl⟩ : syracuseStep 2004527 = 3006791) B3006791
theorem B6854375 : Blo 1186410 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B6010685 : Blo 1186410 6010685 := bstep (se 3 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 6010685 = 2254007) B2254007
theorem B25679753 : Blo 1186410 25679753 := bstep (se 2 (by rfl) ⟨9629907, by rfl⟩ : syracuseStep 25679753 = 19259815) B19259815
theorem B3004523 : Blo 1186410 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B3046265 : Blo 1186410 3046265 := bstep (se 2 (by rfl) ⟨1142349, by rfl⟩ : syracuseStep 3046265 = 2284699) B2284699
theorem B2669435 : Blo 1186410 2669435 := bstep (se 1 (by rfl) ⟨2002076, by rfl⟩ : syracuseStep 2669435 = 4004153) B4004153
theorem B1186843 : Blo 1186410 1186843 := bstep (se 1 (by rfl) ⟨890132, by rfl⟩ : syracuseStep 1186843 = 1780265) B1780265
theorem B2669651 : Blo 1186410 2669651 := bstep (se 1 (by rfl) ⟨2002238, by rfl⟩ : syracuseStep 2669651 = 4004477) B4004477
theorem B2669705 : Blo 1186410 2669705 := bstep (se 2 (by rfl) ⟨1001139, by rfl⟩ : syracuseStep 2669705 = 2002279) B2002279
theorem B2669723 : Blo 1186410 2669723 := bstep (se 1 (by rfl) ⟨2002292, by rfl⟩ : syracuseStep 2669723 = 4004585) B4004585
theorem B1186975 : Blo 1186410 1186975 := bstep (se 1 (by rfl) ⟨890231, by rfl⟩ : syracuseStep 1186975 = 1780463) B1780463
theorem B1187067 : Blo 1186410 1187067 := bstep (se 1 (by rfl) ⟨890300, by rfl⟩ : syracuseStep 1187067 = 1780601) B1780601
theorem B3611945 : Blo 1186410 3611945 := bstep (se 2 (by rfl) ⟨1354479, by rfl⟩ : syracuseStep 3611945 = 2708959) B2708959
theorem B6757991 : Blo 1186410 6757991 := bstep (se 1 (by rfl) ⟨5068493, by rfl⟩ : syracuseStep 6757991 = 10136987) B10136987
theorem B17120929 : Blo 1186410 17120929 := bstep (se 2 (by rfl) ⟨6420348, by rfl⟩ : syracuseStep 17120929 = 12840697) B12840697
theorem B2670263 : Blo 1186410 2670263 := bstep (se 1 (by rfl) ⟨2002697, by rfl⟩ : syracuseStep 2670263 = 4005395) B4005395
theorem B5709649 : Blo 1186410 5709649 := bstep (se 2 (by rfl) ⟨2141118, by rfl⟩ : syracuseStep 5709649 = 4282237) B4282237
theorem B1187675 : Blo 1186410 1187675 := bstep (se 1 (by rfl) ⟨890756, by rfl⟩ : syracuseStep 1187675 = 1781513) B1781513
theorem B3006335 : Blo 1186410 3006335 := bstep (se 1 (by rfl) ⟨2254751, by rfl⟩ : syracuseStep 3006335 = 4509503) B4509503
theorem B4005881 : Blo 1186410 4005881 := bstep (se 2 (by rfl) ⟨1502205, by rfl⟩ : syracuseStep 4005881 = 3004411) B3004411
theorem B1187943 : Blo 1186410 1187943 := bstep (se 1 (by rfl) ⟨890957, by rfl⟩ : syracuseStep 1187943 = 1781915) B1781915
theorem B3801383 : Blo 1186410 3801383 := bstep (se 1 (by rfl) ⟨2851037, by rfl⟩ : syracuseStep 3801383 = 5702075) B5702075
theorem B2670911 : Blo 1186410 2670911 := bstep (se 1 (by rfl) ⟨2003183, by rfl⟩ : syracuseStep 2670911 = 4006367) B4006367
theorem B2671271 : Blo 1186410 2671271 := bstep (se 1 (by rfl) ⟨2003453, by rfl⟩ : syracuseStep 2671271 = 4006907) B4006907
theorem B13525865 : Blo 1186410 13525865 := bstep (se 2 (by rfl) ⟨5072199, by rfl⟩ : syracuseStep 13525865 = 10144399) B10144399
theorem B1336351 : Blo 1186410 1336351 := bstep (se 1 (by rfl) ⟨1002263, by rfl⟩ : syracuseStep 1336351 = 2004527) B2004527
theorem B4007123 : Blo 1186410 4007123 := bstep (se 1 (by rfl) ⟨3005342, by rfl⟩ : syracuseStep 4007123 = 6010685) B6010685
theorem B2670587 : Blo 1186410 2670587 := bstep (se 1 (by rfl) ⟨2002940, by rfl⟩ : syracuseStep 2670587 = 4005881) B4005881
theorem B1779623 : Blo 1186410 1779623 := bstep (se 1 (by rfl) ⟨1334717, by rfl⟩ : syracuseStep 1779623 = 2669435) B2669435
theorem B4507559 : Blo 1186410 4507559 := bstep (se 1 (by rfl) ⟨3380669, by rfl⟩ : syracuseStep 4507559 = 6761339) B6761339
theorem B6760381 : Blo 1186410 6760381 := bstep (se 3 (by rfl) ⟨1267571, by rfl⟩ : syracuseStep 6760381 = 2535143) B2535143
theorem B1779767 : Blo 1186410 1779767 := bstep (se 1 (by rfl) ⟨1334825, by rfl⟩ : syracuseStep 1779767 = 2669651) B2669651
theorem B1902665 : Blo 1186410 1902665 := bstep (se 2 (by rfl) ⟨713499, by rfl⟩ : syracuseStep 1902665 = 1426999) B1426999
theorem B1779803 : Blo 1186410 1779803 := bstep (se 1 (by rfl) ⟨1334852, by rfl⟩ : syracuseStep 1779803 = 2669705) B2669705
theorem B1779815 : Blo 1186410 1779815 := bstep (se 1 (by rfl) ⟨1334861, by rfl⟩ : syracuseStep 1779815 = 2669723) B2669723
theorem B7612865 : Blo 1186410 7612865 := bstep (se 2 (by rfl) ⟨2854824, by rfl⟩ : syracuseStep 7612865 = 5709649) B5709649
theorem B1780175 : Blo 1186410 1780175 := bstep (se 1 (by rfl) ⟨1335131, by rfl⟩ : syracuseStep 1780175 = 2670263) B2670263
theorem B2640439 : Blo 1186410 2640439 := bstep (se 1 (by rfl) ⟨1980329, by rfl⟩ : syracuseStep 2640439 = 3960659) B3960659
theorem B1780475 : Blo 1186410 1780475 := bstep (se 1 (by rfl) ⟨1335356, by rfl⟩ : syracuseStep 1780475 = 2670713) B2670713
theorem B2673575 : Blo 1186410 2673575 := bstep (se 1 (by rfl) ⟨2005181, by rfl⟩ : syracuseStep 2673575 = 4010363) B4010363
theorem B52095973 : Blo 1186410 52095973 := bstep (se 4 (by rfl) ⟨4883997, by rfl⟩ : syracuseStep 52095973 = 9767995) B9767995
theorem B20286611 : Blo 1186410 20286611 := bstep (se 1 (by rfl) ⟨15214958, by rfl⟩ : syracuseStep 20286611 = 30429917) B30429917
theorem B8563927 : Blo 1186410 8563927 := bstep (se 1 (by rfl) ⟨6422945, by rfl⟩ : syracuseStep 8563927 = 12845891) B12845891
theorem B2002171 : Blo 1186410 2002171 := bstep (se 1 (by rfl) ⟨1501628, by rfl⟩ : syracuseStep 2002171 = 3003257) B3003257
theorem B1781033 : Blo 1186410 1781033 := bstep (se 2 (by rfl) ⟨667887, by rfl⟩ : syracuseStep 1781033 = 1335775) B1335775
theorem B68496839 : Blo 1186410 68496839 := bstep (se 1 (by rfl) ⟨51372629, by rfl⟩ : syracuseStep 68496839 = 102745259) B102745259
theorem B27782939 : Blo 1186410 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B2003015 : Blo 1186410 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B1781951 : Blo 1186410 1781951 := bstep (se 1 (by rfl) ⟨1336463, by rfl⟩ : syracuseStep 1781951 = 2672927) B2672927
theorem B1781999 : Blo 1186410 1781999 := bstep (se 1 (by rfl) ⟨1336499, by rfl⟩ : syracuseStep 1781999 = 2672999) B2672999
theorem B1782239 : Blo 1186410 1782239 := bstep (se 1 (by rfl) ⟨1336679, by rfl⟩ : syracuseStep 1782239 = 2673359) B2673359
theorem B4010471 : Blo 1186410 4010471 := bstep (se 1 (by rfl) ⟨3007853, by rfl⟩ : syracuseStep 4010471 = 6015707) B6015707
theorem B6763115 : Blo 1186410 6763115 := bstep (se 1 (by rfl) ⟨5072336, by rfl⟩ : syracuseStep 6763115 = 10144673) B10144673
theorem B4010849 : Blo 1186410 4010849 := bstep (se 2 (by rfl) ⟨1504068, by rfl⟩ : syracuseStep 4010849 = 3008137) B3008137
theorem B22827905 : Blo 1186410 22827905 := bstep (se 2 (by rfl) ⟨8560464, by rfl⟩ : syracuseStep 22827905 = 17120929) B17120929
theorem B2004223 : Blo 1186410 2004223 := bstep (se 1 (by rfl) ⟨1503167, by rfl⟩ : syracuseStep 2004223 = 3006335) B3006335
theorem B24376679 : Blo 1186410 24376679 := bstep (se 1 (by rfl) ⟨18282509, by rfl⟩ : syracuseStep 24376679 = 36565019) B36565019
theorem B555529711 : Blo 1186410 555529711 := bstep (se 1 (by rfl) ⟨416647283, by rfl⟩ : syracuseStep 555529711 = 833294567) B833294567
theorem B263394989 : Blo 1186410 263394989 := bstep (se 3 (by rfl) ⟨49386560, by rfl⟩ : syracuseStep 263394989 = 98773121) B98773121
theorem B2005303 : Blo 1186410 2005303 := bstep (se 1 (by rfl) ⟨1503977, by rfl⟩ : syracuseStep 2005303 = 3007955) B3007955
theorem B4569583 : Blo 1186410 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B5708303 : Blo 1186410 5708303 := bstep (se 1 (by rfl) ⟨4281227, by rfl⟩ : syracuseStep 5708303 = 8562455) B8562455
theorem B17119835 : Blo 1186410 17119835 := bstep (se 1 (by rfl) ⟨12839876, by rfl⟩ : syracuseStep 17119835 = 25679753) B25679753
theorem B4004639 : Blo 1186410 4004639 := bstep (se 1 (by rfl) ⟨3003479, by rfl⟩ : syracuseStep 4004639 = 6006959) B6006959
theorem B6757465 : Blo 1186410 6757465 := bstep (se 2 (by rfl) ⟨2534049, by rfl⟩ : syracuseStep 6757465 = 5068099) B5068099
theorem B2030843 : Blo 1186410 2030843 := bstep (se 1 (by rfl) ⟨1523132, by rfl⟩ : syracuseStep 2030843 = 3046265) B3046265
theorem B3382651 : Blo 1186410 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1187227 : Blo 1186410 1187227 := bstep (se 1 (by rfl) ⟨890420, by rfl⟩ : syracuseStep 1187227 = 1780841) B1780841
theorem B2407963 : Blo 1186410 2407963 := bstep (se 1 (by rfl) ⟨1805972, by rfl⟩ : syracuseStep 2407963 = 3611945) B3611945
theorem B1187375 : Blo 1186410 1187375 := bstep (se 1 (by rfl) ⟨890531, by rfl⟩ : syracuseStep 1187375 = 1781063) B1781063
theorem B5709437 : Blo 1186410 5709437 := bstep (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) B2141039
theorem B4505327 : Blo 1186410 4505327 := bstep (se 1 (by rfl) ⟨3378995, by rfl⟩ : syracuseStep 4505327 = 6757991) B6757991
theorem B1187647 : Blo 1186410 1187647 := bstep (se 1 (by rfl) ⟨890735, by rfl⟩ : syracuseStep 1187647 = 1781471) B1781471
theorem B1335343 : Blo 1186410 1335343 := bstep (se 1 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 1335343 = 2003015) B2003015
theorem B1187967 : Blo 1186410 1187967 := bstep (se 1 (by rfl) ⟨890975, by rfl⟩ : syracuseStep 1187967 = 1781951) B1781951
theorem B1187999 : Blo 1186410 1187999 := bstep (se 1 (by rfl) ⟨890999, by rfl⟩ : syracuseStep 1187999 = 1781999) B1781999
theorem B14082341 : Blo 1186410 14082341 := bstep (se 4 (by rfl) ⟨1320219, by rfl⟩ : syracuseStep 14082341 = 2640439) B2640439
theorem B1188159 : Blo 1186410 1188159 := bstep (se 1 (by rfl) ⟨891119, by rfl⟩ : syracuseStep 1188159 = 1782239) B1782239
theorem B5415581 : Blo 1186410 5415581 := bstep (se 3 (by rfl) ⟨1015421, by rfl⟩ : syracuseStep 5415581 = 2030843) B2030843
theorem B2671415 : Blo 1186410 2671415 := bstep (se 1 (by rfl) ⟨2003561, by rfl⟩ : syracuseStep 2671415 = 4007123) B4007123
theorem B175596659 : Blo 1186410 175596659 := bstep (se 1 (by rfl) ⟨131697494, by rfl⟩ : syracuseStep 175596659 = 263394989) B263394989
theorem B69461297 : Blo 1186410 69461297 := bstep (se 2 (by rfl) ⟨26047986, by rfl⟩ : syracuseStep 69461297 = 52095973) B52095973
theorem B2672297 : Blo 1186410 2672297 := bstep (se 2 (by rfl) ⟨1002111, by rfl⟩ : syracuseStep 2672297 = 2004223) B2004223
theorem B11413223 : Blo 1186410 11413223 := bstep (se 1 (by rfl) ⟨8559917, by rfl⟩ : syracuseStep 11413223 = 17119835) B17119835
theorem B740706281 : Blo 1186410 740706281 := bstep (se 2 (by rfl) ⟨277764855, by rfl⟩ : syracuseStep 740706281 = 555529711) B555529711
theorem B45664559 : Blo 1186410 45664559 := bstep (se 1 (by rfl) ⟨34248419, by rfl⟩ : syracuseStep 45664559 = 68496839) B68496839
theorem B9013841 : Blo 1186410 9013841 := bstep (se 2 (by rfl) ⟨3380190, by rfl⟩ : syracuseStep 9013841 = 6760381) B6760381
theorem B1780391 : Blo 1186410 1780391 := bstep (se 1 (by rfl) ⟨1335293, by rfl⟩ : syracuseStep 1780391 = 2670587) B2670587
theorem B2534255 : Blo 1186410 2534255 := bstep (se 1 (by rfl) ⟨1900691, by rfl⟩ : syracuseStep 2534255 = 3801383) B3801383
theorem B1780607 : Blo 1186410 1780607 := bstep (se 1 (by rfl) ⟨1335455, by rfl⟩ : syracuseStep 1780607 = 2670911) B2670911
theorem B2673647 : Blo 1186410 2673647 := bstep (se 1 (by rfl) ⟨2005235, by rfl⟩ : syracuseStep 2673647 = 4010471) B4010471
theorem B4508743 : Blo 1186410 4508743 := bstep (se 1 (by rfl) ⟨3381557, by rfl⟩ : syracuseStep 4508743 = 6763115) B6763115
theorem B2673737 : Blo 1186410 2673737 := bstep (se 2 (by rfl) ⟨1002651, by rfl⟩ : syracuseStep 2673737 = 2005303) B2005303
theorem B1780847 : Blo 1186410 1780847 := bstep (se 1 (by rfl) ⟨1335635, by rfl⟩ : syracuseStep 1780847 = 2671271) B2671271
theorem B2673899 : Blo 1186410 2673899 := bstep (se 1 (by rfl) ⟨2005424, by rfl⟩ : syracuseStep 2673899 = 4010849) B4010849
theorem B1781801 : Blo 1186410 1781801 := bstep (se 2 (by rfl) ⟨668175, by rfl⟩ : syracuseStep 1781801 = 1336351) B1336351
theorem B5075243 : Blo 1186410 5075243 := bstep (se 1 (by rfl) ⟨3806432, by rfl⟩ : syracuseStep 5075243 = 7612865) B7612865
theorem B3805535 : Blo 1186410 3805535 := bstep (se 1 (by rfl) ⟨2854151, by rfl⟩ : syracuseStep 3805535 = 5708303) B5708303
theorem B4510201 : Blo 1186410 4510201 := bstep (se 2 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 4510201 = 3382651) B3382651
theorem B1782383 : Blo 1186410 1782383 := bstep (se 1 (by rfl) ⟨1336787, by rfl⟩ : syracuseStep 1782383 = 2673575) B2673575
theorem B3806291 : Blo 1186410 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B3003551 : Blo 1186410 3003551 := bstep (se 1 (by rfl) ⟨2252663, by rfl⟩ : syracuseStep 3003551 = 4505327) B4505327
theorem B9017243 : Blo 1186410 9017243 := bstep (se 1 (by rfl) ⟨6762932, by rfl⟩ : syracuseStep 9017243 = 13525865) B13525865
theorem B15218603 : Blo 1186410 15218603 := bstep (se 1 (by rfl) ⟨11413952, by rfl⟩ : syracuseStep 15218603 = 22827905) B22827905
theorem B6092777 : Blo 1186410 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B16251119 : Blo 1186410 16251119 := bstep (se 1 (by rfl) ⟨12188339, by rfl⟩ : syracuseStep 16251119 = 24376679) B24376679
theorem B1186415 : Blo 1186410 1186415 := bstep (se 1 (by rfl) ⟨889811, by rfl⟩ : syracuseStep 1186415 = 1779623) B1779623
theorem B3005039 : Blo 1186410 3005039 := bstep (se 1 (by rfl) ⟨2253779, by rfl⟩ : syracuseStep 3005039 = 4507559) B4507559
theorem B1186511 : Blo 1186410 1186511 := bstep (se 1 (by rfl) ⟨889883, by rfl⟩ : syracuseStep 1186511 = 1779767) B1779767
theorem B1268443 : Blo 1186410 1268443 := bstep (se 1 (by rfl) ⟨951332, by rfl⟩ : syracuseStep 1268443 = 1902665) B1902665
theorem B1186535 : Blo 1186410 1186535 := bstep (se 1 (by rfl) ⟨889901, by rfl⟩ : syracuseStep 1186535 = 1779803) B1779803
theorem B1186543 : Blo 1186410 1186543 := bstep (se 1 (by rfl) ⟨889907, by rfl⟩ : syracuseStep 1186543 = 1779815) B1779815
theorem B9009953 : Blo 1186410 9009953 := bstep (se 2 (by rfl) ⟨3378732, by rfl⟩ : syracuseStep 9009953 = 6757465) B6757465
theorem B11418569 : Blo 1186410 11418569 := bstep (se 2 (by rfl) ⟨4281963, by rfl⟩ : syracuseStep 11418569 = 8563927) B8563927
theorem B1186783 : Blo 1186410 1186783 := bstep (se 1 (by rfl) ⟨890087, by rfl⟩ : syracuseStep 1186783 = 1780175) B1780175
theorem B2669561 : Blo 1186410 2669561 := bstep (se 2 (by rfl) ⟨1001085, by rfl⟩ : syracuseStep 2669561 = 2002171) B2002171
theorem B1186983 : Blo 1186410 1186983 := bstep (se 1 (by rfl) ⟨890237, by rfl⟩ : syracuseStep 1186983 = 1780475) B1780475
theorem B2669759 : Blo 1186410 2669759 := bstep (se 1 (by rfl) ⟨2002319, by rfl⟩ : syracuseStep 2669759 = 4004639) B4004639
theorem B3210617 : Blo 1186410 3210617 := bstep (se 2 (by rfl) ⟨1203981, by rfl⟩ : syracuseStep 3210617 = 2407963) B2407963
theorem B13524407 : Blo 1186410 13524407 := bstep (se 1 (by rfl) ⟨10143305, by rfl⟩ : syracuseStep 13524407 = 20286611) B20286611
theorem B1187355 : Blo 1186410 1187355 := bstep (se 1 (by rfl) ⟨890516, by rfl⟩ : syracuseStep 1187355 = 1781033) B1781033
theorem B18521959 : Blo 1186410 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B1187867 : Blo 1186410 1187867 := bstep (se 1 (by rfl) ⟨890900, by rfl⟩ : syracuseStep 1187867 = 1781801) B1781801
theorem B3383495 : Blo 1186410 3383495 := bstep (se 1 (by rfl) ⟨2537621, by rfl⟩ : syracuseStep 3383495 = 5075243) B5075243
theorem B10150109 : Blo 1186410 10150109 := bstep (se 3 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 10150109 = 3806291) B3806291
theorem B1188255 : Blo 1186410 1188255 := bstep (se 1 (by rfl) ⟨891191, by rfl⟩ : syracuseStep 1188255 = 1782383) B1782383
theorem B6013601 : Blo 1186410 6013601 := bstep (se 2 (by rfl) ⟨2255100, by rfl⟩ : syracuseStep 6013601 = 4510201) B4510201
theorem B117064439 : Blo 1186410 117064439 := bstep (se 1 (by rfl) ⟨87798329, by rfl⟩ : syracuseStep 117064439 = 175596659) B175596659
theorem B37552909 : Blo 1186410 37552909 := bstep (se 3 (by rfl) ⟨7041170, by rfl⟩ : syracuseStep 37552909 = 14082341) B14082341
theorem B8561645 : Blo 1186410 8561645 := bstep (se 3 (by rfl) ⟨1605308, by rfl⟩ : syracuseStep 8561645 = 3210617) B3210617
theorem B30443039 : Blo 1186410 30443039 := bstep (se 1 (by rfl) ⟨22832279, by rfl⟩ : syracuseStep 30443039 = 45664559) B45664559
theorem B6006635 : Blo 1186410 6006635 := bstep (se 1 (by rfl) ⟨4504976, by rfl⟩ : syracuseStep 6006635 = 9009953) B9009953
theorem B1689503 : Blo 1186410 1689503 := bstep (se 1 (by rfl) ⟨1267127, by rfl⟩ : syracuseStep 1689503 = 2534255) B2534255
theorem B7612379 : Blo 1186410 7612379 := bstep (se 1 (by rfl) ⟨5709284, by rfl⟩ : syracuseStep 7612379 = 11418569) B11418569
theorem B1779707 : Blo 1186410 1779707 := bstep (se 1 (by rfl) ⟨1334780, by rfl⟩ : syracuseStep 1779707 = 2669561) B2669561
theorem B1779839 : Blo 1186410 1779839 := bstep (se 1 (by rfl) ⟨1334879, by rfl⟩ : syracuseStep 1779839 = 2669759) B2669759
theorem B16247405 : Blo 1186410 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B1780457 : Blo 1186410 1780457 := bstep (se 2 (by rfl) ⟨667671, by rfl⟩ : syracuseStep 1780457 = 1335343) B1335343
theorem B1780943 : Blo 1186410 1780943 := bstep (se 1 (by rfl) ⟨1335707, by rfl⟩ : syracuseStep 1780943 = 2671415) B2671415
theorem B2002367 : Blo 1186410 2002367 := bstep (se 1 (by rfl) ⟨1501775, by rfl⟩ : syracuseStep 2002367 = 3003551) B3003551
theorem B1781531 : Blo 1186410 1781531 := bstep (se 1 (by rfl) ⟨1336148, by rfl⟩ : syracuseStep 1781531 = 2672297) B2672297
theorem B10145735 : Blo 1186410 10145735 := bstep (se 1 (by rfl) ⟨7609301, by rfl⟩ : syracuseStep 10145735 = 15218603) B15218603
theorem B10834079 : Blo 1186410 10834079 := bstep (se 1 (by rfl) ⟨8125559, by rfl⟩ : syracuseStep 10834079 = 16251119) B16251119
theorem B6009227 : Blo 1186410 6009227 := bstep (se 1 (by rfl) ⟨4506920, by rfl⟩ : syracuseStep 6009227 = 9013841) B9013841
theorem B2003359 : Blo 1186410 2003359 := bstep (se 1 (by rfl) ⟨1502519, by rfl⟩ : syracuseStep 2003359 = 3005039) B3005039
theorem B1782431 : Blo 1186410 1782431 := bstep (se 1 (by rfl) ⟨1336823, by rfl⟩ : syracuseStep 1782431 = 2673647) B2673647
theorem B1782491 : Blo 1186410 1782491 := bstep (se 1 (by rfl) ⟨1336868, by rfl⟩ : syracuseStep 1782491 = 2673737) B2673737
theorem B1782599 : Blo 1186410 1782599 := bstep (se 1 (by rfl) ⟨1336949, by rfl⟩ : syracuseStep 1782599 = 2673899) B2673899
theorem B9016271 : Blo 1186410 9016271 := bstep (se 1 (by rfl) ⟨6762203, by rfl⟩ : syracuseStep 9016271 = 13524407) B13524407
theorem B24695945 : Blo 1186410 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B2537023 : Blo 1186410 2537023 := bstep (se 1 (by rfl) ⟨1902767, by rfl⟩ : syracuseStep 2537023 = 3805535) B3805535
theorem B3610387 : Blo 1186410 3610387 := bstep (se 1 (by rfl) ⟨2707790, by rfl⟩ : syracuseStep 3610387 = 5415581) B5415581
theorem B46307531 : Blo 1186410 46307531 := bstep (se 1 (by rfl) ⟨34730648, by rfl⟩ : syracuseStep 46307531 = 69461297) B69461297
theorem B6765029 : Blo 1186410 6765029 := bstep (se 4 (by rfl) ⟨634221, by rfl⟩ : syracuseStep 6765029 = 1268443) B1268443
theorem B7608815 : Blo 1186410 7608815 := bstep (se 1 (by rfl) ⟨5706611, by rfl⟩ : syracuseStep 7608815 = 11413223) B11413223
theorem B6011495 : Blo 1186410 6011495 := bstep (se 1 (by rfl) ⟨4508621, by rfl⟩ : syracuseStep 6011495 = 9017243) B9017243
theorem B493804187 : Blo 1186410 493804187 := bstep (se 1 (by rfl) ⟨370353140, by rfl⟩ : syracuseStep 493804187 = 740706281) B740706281
theorem B6011657 : Blo 1186410 6011657 := bstep (se 2 (by rfl) ⟨2254371, by rfl⟩ : syracuseStep 6011657 = 4508743) B4508743
theorem B1186927 : Blo 1186410 1186927 := bstep (se 1 (by rfl) ⟨890195, by rfl⟩ : syracuseStep 1186927 = 1780391) B1780391
theorem B1187071 : Blo 1186410 1187071 := bstep (se 1 (by rfl) ⟨890303, by rfl⟩ : syracuseStep 1187071 = 1780607) B1780607
theorem B1187231 : Blo 1186410 1187231 := bstep (se 1 (by rfl) ⟨890423, by rfl⟩ : syracuseStep 1187231 = 1780847) B1780847
theorem B6766739 : Blo 1186410 6766739 := bstep (se 1 (by rfl) ⟨5075054, by rfl⟩ : syracuseStep 6766739 = 10150109) B10150109
theorem B4006151 : Blo 1186410 4006151 := bstep (se 1 (by rfl) ⟨3004613, by rfl⟩ : syracuseStep 4006151 = 6009227) B6009227
theorem B1188287 : Blo 1186410 1188287 := bstep (se 1 (by rfl) ⟨891215, by rfl⟩ : syracuseStep 1188287 = 1782431) B1782431
theorem B1188327 : Blo 1186410 1188327 := bstep (se 1 (by rfl) ⟨891245, by rfl⟩ : syracuseStep 1188327 = 1782491) B1782491
theorem B2671145 : Blo 1186410 2671145 := bstep (se 2 (by rfl) ⟨1001679, by rfl⟩ : syracuseStep 2671145 = 2003359) B2003359
theorem B1188399 : Blo 1186410 1188399 := bstep (se 1 (by rfl) ⟨891299, by rfl⟩ : syracuseStep 1188399 = 1782599) B1782599
theorem B50070545 : Blo 1186410 50070545 := bstep (se 2 (by rfl) ⟨18776454, by rfl⟩ : syracuseStep 50070545 = 37552909) B37552909
theorem B5072543 : Blo 1186410 5072543 := bstep (se 1 (by rfl) ⟨3804407, by rfl⟩ : syracuseStep 5072543 = 7608815) B7608815
theorem B4007663 : Blo 1186410 4007663 := bstep (se 1 (by rfl) ⟨3005747, by rfl⟩ : syracuseStep 4007663 = 6011495) B6011495
theorem B10831603 : Blo 1186410 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B4007771 : Blo 1186410 4007771 := bstep (se 1 (by rfl) ⟨3005828, by rfl⟩ : syracuseStep 4007771 = 6011657) B6011657
theorem B2255663 : Blo 1186410 2255663 := bstep (se 1 (by rfl) ⟨1691747, by rfl⟩ : syracuseStep 2255663 = 3383495) B3383495
theorem B4009067 : Blo 1186410 4009067 := bstep (se 1 (by rfl) ⟨3006800, by rfl⟩ : syracuseStep 4009067 = 6013601) B6013601
theorem B20295359 : Blo 1186410 20295359 := bstep (se 1 (by rfl) ⟨15221519, by rfl⟩ : syracuseStep 20295359 = 30443039) B30443039
theorem B5074919 : Blo 1186410 5074919 := bstep (se 1 (by rfl) ⟨3806189, by rfl⟩ : syracuseStep 5074919 = 7612379) B7612379
theorem B30871687 : Blo 1186410 30871687 := bstep (se 1 (by rfl) ⟨23153765, by rfl⟩ : syracuseStep 30871687 = 46307531) B46307531
theorem B4510019 : Blo 1186410 4510019 := bstep (se 1 (by rfl) ⟨3382514, by rfl⟩ : syracuseStep 4510019 = 6765029) B6765029
theorem B4813849 : Blo 1186410 4813849 := bstep (se 2 (by rfl) ⟨1805193, by rfl⟩ : syracuseStep 4813849 = 3610387) B3610387
theorem B6763823 : Blo 1186410 6763823 := bstep (se 1 (by rfl) ⟨5072867, by rfl⟩ : syracuseStep 6763823 = 10145735) B10145735
theorem B78042959 : Blo 1186410 78042959 := bstep (se 1 (by rfl) ⟨58532219, by rfl⟩ : syracuseStep 78042959 = 117064439) B117064439
theorem B6010847 : Blo 1186410 6010847 := bstep (se 1 (by rfl) ⟨4508135, by rfl⟩ : syracuseStep 6010847 = 9016271) B9016271
theorem B5707763 : Blo 1186410 5707763 := bstep (se 1 (by rfl) ⟨4280822, by rfl⟩ : syracuseStep 5707763 = 8561645) B8561645
theorem B16463963 : Blo 1186410 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B4004423 : Blo 1186410 4004423 := bstep (se 1 (by rfl) ⟨3003317, by rfl⟩ : syracuseStep 4004423 = 6006635) B6006635
theorem B1186471 : Blo 1186410 1186471 := bstep (se 1 (by rfl) ⟨889853, by rfl⟩ : syracuseStep 1186471 = 1779707) B1779707
theorem B1186559 : Blo 1186410 1186559 := bstep (se 1 (by rfl) ⟨889919, by rfl⟩ : syracuseStep 1186559 = 1779839) B1779839
theorem B115563509 : Blo 1186410 115563509 := bstep (se 5 (by rfl) ⟨5417039, by rfl⟩ : syracuseStep 115563509 = 10834079) B10834079
theorem B329202791 : Blo 1186410 329202791 := bstep (se 1 (by rfl) ⟨246902093, by rfl⟩ : syracuseStep 329202791 = 493804187) B493804187
theorem B1186971 : Blo 1186410 1186971 := bstep (se 1 (by rfl) ⟨890228, by rfl⟩ : syracuseStep 1186971 = 1780457) B1780457
theorem B3382697 : Blo 1186410 3382697 := bstep (se 2 (by rfl) ⟨1268511, by rfl⟩ : syracuseStep 3382697 = 2537023) B2537023
theorem B1187295 : Blo 1186410 1187295 := bstep (se 1 (by rfl) ⟨890471, by rfl⟩ : syracuseStep 1187295 = 1780943) B1780943
theorem B1334911 : Blo 1186410 1334911 := bstep (se 1 (by rfl) ⟨1001183, by rfl⟩ : syracuseStep 1334911 = 2002367) B2002367
theorem B4505341 : Blo 1186410 4505341 := bstep (se 3 (by rfl) ⟨844751, by rfl⟩ : syracuseStep 4505341 = 1689503) B1689503
theorem B1187687 : Blo 1186410 1187687 := bstep (se 1 (by rfl) ⟨890765, by rfl⟩ : syracuseStep 1187687 = 1781531) B1781531
theorem B25673861 : Blo 1186410 25673861 := bstep (se 4 (by rfl) ⟨2406924, by rfl⟩ : syracuseStep 25673861 = 4813849) B4813849
theorem B2670767 : Blo 1186410 2670767 := bstep (se 1 (by rfl) ⟨2003075, by rfl⟩ : syracuseStep 2670767 = 4006151) B4006151
theorem B3006679 : Blo 1186410 3006679 := bstep (se 1 (by rfl) ⟨2255009, by rfl⟩ : syracuseStep 3006679 = 4510019) B4510019
theorem B2671775 : Blo 1186410 2671775 := bstep (se 1 (by rfl) ⟨2003831, by rfl⟩ : syracuseStep 2671775 = 4007663) B4007663
theorem B52028639 : Blo 1186410 52028639 := bstep (se 1 (by rfl) ⟨39021479, by rfl⟩ : syracuseStep 52028639 = 78042959) B78042959
theorem B2671847 : Blo 1186410 2671847 := bstep (se 1 (by rfl) ⟨2003885, by rfl⟩ : syracuseStep 2671847 = 4007771) B4007771
theorem B4007231 : Blo 1186410 4007231 := bstep (se 1 (by rfl) ⟨3005423, by rfl⟩ : syracuseStep 4007231 = 6010847) B6010847
theorem B2672711 : Blo 1186410 2672711 := bstep (se 1 (by rfl) ⟨2004533, by rfl⟩ : syracuseStep 2672711 = 4009067) B4009067
theorem B1779881 : Blo 1186410 1779881 := bstep (se 2 (by rfl) ⟨667455, by rfl⟩ : syracuseStep 1779881 = 1334911) B1334911
theorem B2255131 : Blo 1186410 2255131 := bstep (se 1 (by rfl) ⟨1691348, by rfl⟩ : syracuseStep 2255131 = 3382697) B3382697
theorem B6007121 : Blo 1186410 6007121 := bstep (se 2 (by rfl) ⟨2252670, by rfl⟩ : syracuseStep 6007121 = 4505341) B4505341
theorem B1780763 : Blo 1186410 1780763 := bstep (se 1 (by rfl) ⟨1335572, by rfl⟩ : syracuseStep 1780763 = 2671145) B2671145
theorem B4509215 : Blo 1186410 4509215 := bstep (se 1 (by rfl) ⟨3381911, by rfl⟩ : syracuseStep 4509215 = 6763823) B6763823
theorem B3805175 : Blo 1186410 3805175 := bstep (se 1 (by rfl) ⟨2853881, by rfl⟩ : syracuseStep 3805175 = 5707763) B5707763
theorem B1503775 : Blo 1186410 1503775 := bstep (se 1 (by rfl) ⟨1127831, by rfl⟩ : syracuseStep 1503775 = 2255663) B2255663
theorem B77042339 : Blo 1186410 77042339 := bstep (se 1 (by rfl) ⟨57781754, by rfl⟩ : syracuseStep 77042339 = 115563509) B115563509
theorem B219468527 : Blo 1186410 219468527 := bstep (se 1 (by rfl) ⟨164601395, by rfl⟩ : syracuseStep 219468527 = 329202791) B329202791
theorem B13530239 : Blo 1186410 13530239 := bstep (se 1 (by rfl) ⟨10147679, by rfl⟩ : syracuseStep 13530239 = 20295359) B20295359
theorem B4511159 : Blo 1186410 4511159 := bstep (se 1 (by rfl) ⟨3383369, by rfl⟩ : syracuseStep 4511159 = 6766739) B6766739
theorem B41162249 : Blo 1186410 41162249 := bstep (se 2 (by rfl) ⟨15435843, by rfl⟩ : syracuseStep 41162249 = 30871687) B30871687
theorem B33380363 : Blo 1186410 33380363 := bstep (se 1 (by rfl) ⟨25035272, by rfl⟩ : syracuseStep 33380363 = 50070545) B50070545
theorem B3381695 : Blo 1186410 3381695 := bstep (se 1 (by rfl) ⟨2536271, by rfl⟩ : syracuseStep 3381695 = 5072543) B5072543
theorem B10975975 : Blo 1186410 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B2669615 : Blo 1186410 2669615 := bstep (se 1 (by rfl) ⟨2002211, by rfl⟩ : syracuseStep 2669615 = 4004423) B4004423
theorem B14442137 : Blo 1186410 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B3383279 : Blo 1186410 3383279 := bstep (se 1 (by rfl) ⟨2537459, by rfl⟩ : syracuseStep 3383279 = 5074919) B5074919
theorem B3006841 : Blo 1186410 3006841 := bstep (se 2 (by rfl) ⟨1127565, by rfl⟩ : syracuseStep 3006841 = 2255131) B2255131
theorem B9020159 : Blo 1186410 9020159 := bstep (se 1 (by rfl) ⟨6765119, by rfl⟩ : syracuseStep 9020159 = 13530239) B13530239
theorem B34685759 : Blo 1186410 34685759 := bstep (se 1 (by rfl) ⟨26014319, by rfl⟩ : syracuseStep 34685759 = 52028639) B52028639
theorem B2671487 : Blo 1186410 2671487 := bstep (se 1 (by rfl) ⟨2003615, by rfl⟩ : syracuseStep 2671487 = 4007231) B4007231
theorem B3007439 : Blo 1186410 3007439 := bstep (se 1 (by rfl) ⟨2255579, by rfl⟩ : syracuseStep 3007439 = 4511159) B4511159
theorem B2254463 : Blo 1186410 2254463 := bstep (se 1 (by rfl) ⟨1690847, by rfl⟩ : syracuseStep 2254463 = 3381695) B3381695
theorem B1779743 : Blo 1186410 1779743 := bstep (se 1 (by rfl) ⟨1334807, by rfl⟩ : syracuseStep 1779743 = 2669615) B2669615
theorem B9628091 : Blo 1186410 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B2255519 : Blo 1186410 2255519 := bstep (se 1 (by rfl) ⟨1691639, by rfl⟩ : syracuseStep 2255519 = 3383279) B3383279
theorem B17115907 : Blo 1186410 17115907 := bstep (se 1 (by rfl) ⟨12836930, by rfl⟩ : syracuseStep 17115907 = 25673861) B25673861
theorem B1780511 : Blo 1186410 1780511 := bstep (se 1 (by rfl) ⟨1335383, by rfl⟩ : syracuseStep 1780511 = 2670767) B2670767
theorem B4008905 : Blo 1186410 4008905 := bstep (se 2 (by rfl) ⟨1503339, by rfl⟩ : syracuseStep 4008905 = 3006679) B3006679
theorem B146312351 : Blo 1186410 146312351 := bstep (se 1 (by rfl) ⟨109734263, by rfl⟩ : syracuseStep 146312351 = 219468527) B219468527
theorem B1781183 : Blo 1186410 1781183 := bstep (se 1 (by rfl) ⟨1335887, by rfl⟩ : syracuseStep 1781183 = 2671775) B2671775
theorem B1781231 : Blo 1186410 1781231 := bstep (se 1 (by rfl) ⟨1335923, by rfl⟩ : syracuseStep 1781231 = 2671847) B2671847
theorem B22253575 : Blo 1186410 22253575 := bstep (se 1 (by rfl) ⟨16690181, by rfl⟩ : syracuseStep 22253575 = 33380363) B33380363
theorem B1781807 : Blo 1186410 1781807 := bstep (se 1 (by rfl) ⟨1336355, by rfl⟩ : syracuseStep 1781807 = 2672711) B2672711
theorem B10147133 : Blo 1186410 10147133 := bstep (se 3 (by rfl) ⟨1902587, by rfl⟩ : syracuseStep 10147133 = 3805175) B3805175
theorem B51361559 : Blo 1186410 51361559 := bstep (se 1 (by rfl) ⟨38521169, by rfl⟩ : syracuseStep 51361559 = 77042339) B77042339
theorem B2005033 : Blo 1186410 2005033 := bstep (se 2 (by rfl) ⟨751887, by rfl⟩ : syracuseStep 2005033 = 1503775) B1503775
theorem B27441499 : Blo 1186410 27441499 := bstep (se 1 (by rfl) ⟨20581124, by rfl⟩ : syracuseStep 27441499 = 41162249) B41162249
theorem B58538533 : Blo 1186410 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B1186587 : Blo 1186410 1186587 := bstep (se 1 (by rfl) ⟨889940, by rfl⟩ : syracuseStep 1186587 = 1779881) B1779881
theorem B4004747 : Blo 1186410 4004747 := bstep (se 1 (by rfl) ⟨3003560, by rfl⟩ : syracuseStep 4004747 = 6007121) B6007121
theorem B1187175 : Blo 1186410 1187175 := bstep (se 1 (by rfl) ⟨890381, by rfl⟩ : syracuseStep 1187175 = 1780763) B1780763
theorem B3006143 : Blo 1186410 3006143 := bstep (se 1 (by rfl) ⟨2254607, by rfl⟩ : syracuseStep 3006143 = 4509215) B4509215
theorem B29671433 : Blo 1186410 29671433 := bstep (se 2 (by rfl) ⟨11126787, by rfl⟩ : syracuseStep 29671433 = 22253575) B22253575
theorem B1187871 : Blo 1186410 1187871 := bstep (se 1 (by rfl) ⟨890903, by rfl⟩ : syracuseStep 1187871 = 1781807) B1781807
theorem B6013439 : Blo 1186410 6013439 := bstep (se 1 (by rfl) ⟨4510079, by rfl⟩ : syracuseStep 6013439 = 9020159) B9020159
theorem B2672603 : Blo 1186410 2672603 := bstep (se 1 (by rfl) ⟨2004452, by rfl⟩ : syracuseStep 2672603 = 4008905) B4008905
theorem B2673377 : Blo 1186410 2673377 := bstep (se 2 (by rfl) ⟨1002516, by rfl⟩ : syracuseStep 2673377 = 2005033) B2005033
theorem B36588665 : Blo 1186410 36588665 := bstep (se 2 (by rfl) ⟨13720749, by rfl⟩ : syracuseStep 36588665 = 27441499) B27441499
theorem B4009121 : Blo 1186410 4009121 := bstep (se 2 (by rfl) ⟨1503420, by rfl⟩ : syracuseStep 4009121 = 3006841) B3006841
theorem B1780991 : Blo 1186410 1780991 := bstep (se 1 (by rfl) ⟨1335743, by rfl⟩ : syracuseStep 1780991 = 2671487) B2671487
theorem B1502975 : Blo 1186410 1502975 := bstep (se 1 (by rfl) ⟨1127231, by rfl⟩ : syracuseStep 1502975 = 2254463) B2254463
theorem B6418727 : Blo 1186410 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B1503679 : Blo 1186410 1503679 := bstep (se 1 (by rfl) ⟨1127759, by rfl⟩ : syracuseStep 1503679 = 2255519) B2255519
theorem B2004095 : Blo 1186410 2004095 := bstep (se 1 (by rfl) ⟨1503071, by rfl⟩ : syracuseStep 2004095 = 3006143) B3006143
theorem B23123839 : Blo 1186410 23123839 := bstep (se 1 (by rfl) ⟨17342879, by rfl⟩ : syracuseStep 23123839 = 34685759) B34685759
theorem B2004959 : Blo 1186410 2004959 := bstep (se 1 (by rfl) ⟨1503719, by rfl⟩ : syracuseStep 2004959 = 3007439) B3007439
theorem B78051377 : Blo 1186410 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B6764755 : Blo 1186410 6764755 := bstep (se 1 (by rfl) ⟨5073566, by rfl⟩ : syracuseStep 6764755 = 10147133) B10147133
theorem B22821209 : Blo 1186410 22821209 := bstep (se 2 (by rfl) ⟨8557953, by rfl⟩ : syracuseStep 22821209 = 17115907) B17115907
theorem B34241039 : Blo 1186410 34241039 := bstep (se 1 (by rfl) ⟨25680779, by rfl⟩ : syracuseStep 34241039 = 51361559) B51361559
theorem B1186495 : Blo 1186410 1186495 := bstep (se 1 (by rfl) ⟨889871, by rfl⟩ : syracuseStep 1186495 = 1779743) B1779743
theorem B1187007 : Blo 1186410 1187007 := bstep (se 1 (by rfl) ⟨890255, by rfl⟩ : syracuseStep 1187007 = 1780511) B1780511
theorem B2669831 : Blo 1186410 2669831 := bstep (se 1 (by rfl) ⟨2002373, by rfl⟩ : syracuseStep 2669831 = 4004747) B4004747
theorem B97541567 : Blo 1186410 97541567 := bstep (se 1 (by rfl) ⟨73156175, by rfl⟩ : syracuseStep 97541567 = 146312351) B146312351
theorem B1187455 : Blo 1186410 1187455 := bstep (se 1 (by rfl) ⟨890591, by rfl⟩ : syracuseStep 1187455 = 1781183) B1781183
theorem B1187487 : Blo 1186410 1187487 := bstep (se 1 (by rfl) ⟨890615, by rfl⟩ : syracuseStep 1187487 = 1781231) B1781231
theorem B9019673 : Blo 1186410 9019673 := bstep (se 2 (by rfl) ⟨3382377, by rfl⟩ : syracuseStep 9019673 = 6764755) B6764755
theorem B1336063 : Blo 1186410 1336063 := bstep (se 1 (by rfl) ⟨1002047, by rfl⟩ : syracuseStep 1336063 = 2004095) B2004095
theorem B1336639 : Blo 1186410 1336639 := bstep (se 1 (by rfl) ⟨1002479, by rfl⟩ : syracuseStep 1336639 = 2004959) B2004959
theorem B15214139 : Blo 1186410 15214139 := bstep (se 1 (by rfl) ⟨11410604, by rfl⟩ : syracuseStep 15214139 = 22821209) B22821209
theorem B4007933 : Blo 1186410 4007933 := bstep (se 3 (by rfl) ⟨751487, by rfl⟩ : syracuseStep 4007933 = 1502975) B1502975
theorem B2672747 : Blo 1186410 2672747 := bstep (se 1 (by rfl) ⟨2004560, by rfl⟩ : syracuseStep 2672747 = 4009121) B4009121
theorem B1779887 : Blo 1186410 1779887 := bstep (se 1 (by rfl) ⟨1334915, by rfl⟩ : syracuseStep 1779887 = 2669831) B2669831
theorem B4279151 : Blo 1186410 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B4008959 : Blo 1186410 4008959 := bstep (se 1 (by rfl) ⟨3006719, by rfl⟩ : syracuseStep 4008959 = 6013439) B6013439
theorem B1781735 : Blo 1186410 1781735 := bstep (se 1 (by rfl) ⟨1336301, by rfl⟩ : syracuseStep 1781735 = 2672603) B2672603
theorem B22827359 : Blo 1186410 22827359 := bstep (se 1 (by rfl) ⟨17120519, by rfl⟩ : syracuseStep 22827359 = 34241039) B34241039
theorem B1782251 : Blo 1186410 1782251 := bstep (se 1 (by rfl) ⟨1336688, by rfl⟩ : syracuseStep 1782251 = 2673377) B2673377
theorem B24392443 : Blo 1186410 24392443 := bstep (se 1 (by rfl) ⟨18294332, by rfl⟩ : syracuseStep 24392443 = 36588665) B36588665
theorem B30831785 : Blo 1186410 30831785 := bstep (se 2 (by rfl) ⟨11561919, by rfl⟩ : syracuseStep 30831785 = 23123839) B23123839
theorem B19780955 : Blo 1186410 19780955 := bstep (se 1 (by rfl) ⟨14835716, by rfl⟩ : syracuseStep 19780955 = 29671433) B29671433
theorem B2004905 : Blo 1186410 2004905 := bstep (se 2 (by rfl) ⟨751839, by rfl⟩ : syracuseStep 2004905 = 1503679) B1503679
theorem B52034251 : Blo 1186410 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B1187327 : Blo 1186410 1187327 := bstep (se 1 (by rfl) ⟨890495, by rfl⟩ : syracuseStep 1187327 = 1780991) B1780991
theorem B65027711 : Blo 1186410 65027711 := bstep (se 1 (by rfl) ⟨48770783, by rfl⟩ : syracuseStep 65027711 = 97541567) B97541567
theorem B6013115 : Blo 1186410 6013115 := bstep (se 1 (by rfl) ⟨4509836, by rfl⟩ : syracuseStep 6013115 = 9019673) B9019673
theorem B1188167 : Blo 1186410 1188167 := bstep (se 1 (by rfl) ⟨891125, by rfl⟩ : syracuseStep 1188167 = 1782251) B1782251
theorem B20554523 : Blo 1186410 20554523 := bstep (se 1 (by rfl) ⟨15415892, by rfl⟩ : syracuseStep 20554523 = 30831785) B30831785
theorem B69379001 : Blo 1186410 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B32523257 : Blo 1186410 32523257 := bstep (se 2 (by rfl) ⟨12196221, by rfl⟩ : syracuseStep 32523257 = 24392443) B24392443
theorem B10142759 : Blo 1186410 10142759 := bstep (se 1 (by rfl) ⟨7607069, by rfl⟩ : syracuseStep 10142759 = 15214139) B15214139
theorem B1336603 : Blo 1186410 1336603 := bstep (se 1 (by rfl) ⟨1002452, by rfl⟩ : syracuseStep 1336603 = 2004905) B2004905
theorem B2671955 : Blo 1186410 2671955 := bstep (se 1 (by rfl) ⟨2003966, by rfl⟩ : syracuseStep 2671955 = 4007933) B4007933
theorem B2852767 : Blo 1186410 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B2672639 : Blo 1186410 2672639 := bstep (se 1 (by rfl) ⟨2004479, by rfl⟩ : syracuseStep 2672639 = 4008959) B4008959
theorem B1781417 : Blo 1186410 1781417 := bstep (se 2 (by rfl) ⟨668031, by rfl⟩ : syracuseStep 1781417 = 1336063) B1336063
theorem B1781831 : Blo 1186410 1781831 := bstep (se 1 (by rfl) ⟨1336373, by rfl⟩ : syracuseStep 1781831 = 2672747) B2672747
theorem B1782185 : Blo 1186410 1782185 := bstep (se 2 (by rfl) ⟨668319, by rfl⟩ : syracuseStep 1782185 = 1336639) B1336639
theorem B15218239 : Blo 1186410 15218239 := bstep (se 1 (by rfl) ⟨11413679, by rfl⟩ : syracuseStep 15218239 = 22827359) B22827359
theorem B13187303 : Blo 1186410 13187303 := bstep (se 1 (by rfl) ⟨9890477, by rfl⟩ : syracuseStep 13187303 = 19780955) B19780955
theorem B1186591 : Blo 1186410 1186591 := bstep (se 1 (by rfl) ⟨889943, by rfl⟩ : syracuseStep 1186591 = 1779887) B1779887
theorem B43351807 : Blo 1186410 43351807 := bstep (se 1 (by rfl) ⟨32513855, by rfl⟩ : syracuseStep 43351807 = 65027711) B65027711
theorem B1187823 : Blo 1186410 1187823 := bstep (se 1 (by rfl) ⟨890867, by rfl⟩ : syracuseStep 1187823 = 1781735) B1781735
theorem B1187887 : Blo 1186410 1187887 := bstep (se 1 (by rfl) ⟨890915, by rfl⟩ : syracuseStep 1187887 = 1781831) B1781831
theorem B1188123 : Blo 1186410 1188123 := bstep (se 1 (by rfl) ⟨891092, by rfl⟩ : syracuseStep 1188123 = 1782185) B1782185
theorem B46252667 : Blo 1186410 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B8791535 : Blo 1186410 8791535 := bstep (se 1 (by rfl) ⟨6593651, by rfl⟩ : syracuseStep 8791535 = 13187303) B13187303
theorem B3803689 : Blo 1186410 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B4008743 : Blo 1186410 4008743 := bstep (se 1 (by rfl) ⟨3006557, by rfl⟩ : syracuseStep 4008743 = 6013115) B6013115
theorem B6761839 : Blo 1186410 6761839 := bstep (se 1 (by rfl) ⟨5071379, by rfl⟩ : syracuseStep 6761839 = 10142759) B10142759
theorem B1781303 : Blo 1186410 1781303 := bstep (se 1 (by rfl) ⟨1335977, by rfl⟩ : syracuseStep 1781303 = 2671955) B2671955
theorem B1781759 : Blo 1186410 1781759 := bstep (se 1 (by rfl) ⟨1336319, by rfl⟩ : syracuseStep 1781759 = 2672639) B2672639
theorem B1782137 : Blo 1186410 1782137 := bstep (se 2 (by rfl) ⟨668301, by rfl⟩ : syracuseStep 1782137 = 1336603) B1336603
theorem B13703015 : Blo 1186410 13703015 := bstep (se 1 (by rfl) ⟨10277261, by rfl⟩ : syracuseStep 13703015 = 20554523) B20554523
theorem B21682171 : Blo 1186410 21682171 := bstep (se 1 (by rfl) ⟨16261628, by rfl⟩ : syracuseStep 21682171 = 32523257) B32523257
theorem B20290985 : Blo 1186410 20290985 := bstep (se 2 (by rfl) ⟨7609119, by rfl⟩ : syracuseStep 20290985 = 15218239) B15218239
theorem B57802409 : Blo 1186410 57802409 := bstep (se 2 (by rfl) ⟨21675903, by rfl⟩ : syracuseStep 57802409 = 43351807) B43351807
theorem B1187611 : Blo 1186410 1187611 := bstep (se 1 (by rfl) ⟨890708, by rfl⟩ : syracuseStep 1187611 = 1781417) B1781417
theorem B1188091 : Blo 1186410 1188091 := bstep (se 1 (by rfl) ⟨891068, by rfl⟩ : syracuseStep 1188091 = 1782137) B1782137
theorem B5071585 : Blo 1186410 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B9135343 : Blo 1186410 9135343 := bstep (se 1 (by rfl) ⟨6851507, by rfl⟩ : syracuseStep 9135343 = 13703015) B13703015
theorem B123340445 : Blo 1186410 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B2672495 : Blo 1186410 2672495 := bstep (se 1 (by rfl) ⟨2004371, by rfl⟩ : syracuseStep 2672495 = 4008743) B4008743
theorem B28909561 : Blo 1186410 28909561 := bstep (se 2 (by rfl) ⟨10841085, by rfl⟩ : syracuseStep 28909561 = 21682171) B21682171
theorem B13527323 : Blo 1186410 13527323 := bstep (se 1 (by rfl) ⟨10145492, by rfl⟩ : syracuseStep 13527323 = 20290985) B20290985
theorem B9015785 : Blo 1186410 9015785 := bstep (se 2 (by rfl) ⟨3380919, by rfl⟩ : syracuseStep 9015785 = 6761839) B6761839
theorem B23444093 : Blo 1186410 23444093 := bstep (se 3 (by rfl) ⟨4395767, by rfl⟩ : syracuseStep 23444093 = 8791535) B8791535
theorem B1187535 : Blo 1186410 1187535 := bstep (se 1 (by rfl) ⟨890651, by rfl⟩ : syracuseStep 1187535 = 1781303) B1781303
theorem B38534939 : Blo 1186410 38534939 := bstep (se 1 (by rfl) ⟨28901204, by rfl⟩ : syracuseStep 38534939 = 57802409) B57802409
theorem B1187839 : Blo 1186410 1187839 := bstep (se 1 (by rfl) ⟨890879, by rfl⟩ : syracuseStep 1187839 = 1781759) B1781759
theorem B38546081 : Blo 1186410 38546081 := bstep (se 2 (by rfl) ⟨14454780, by rfl⟩ : syracuseStep 38546081 = 28909561) B28909561
theorem B6762113 : Blo 1186410 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B82226963 : Blo 1186410 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B1781663 : Blo 1186410 1781663 := bstep (se 1 (by rfl) ⟨1336247, by rfl⟩ : syracuseStep 1781663 = 2672495) B2672495
theorem B6010523 : Blo 1186410 6010523 := bstep (se 1 (by rfl) ⟨4507892, by rfl⟩ : syracuseStep 6010523 = 9015785) B9015785
theorem B9018215 : Blo 1186410 9018215 := bstep (se 1 (by rfl) ⟨6763661, by rfl⟩ : syracuseStep 9018215 = 13527323) B13527323
theorem B12180457 : Blo 1186410 12180457 := bstep (se 2 (by rfl) ⟨4567671, by rfl⟩ : syracuseStep 12180457 = 9135343) B9135343
theorem B15629395 : Blo 1186410 15629395 := bstep (se 1 (by rfl) ⟨11722046, by rfl⟩ : syracuseStep 15629395 = 23444093) B23444093
theorem B25689959 : Blo 1186410 25689959 := bstep (se 1 (by rfl) ⟨19267469, by rfl⟩ : syracuseStep 25689959 = 38534939) B38534939
theorem B4007015 : Blo 1186410 4007015 := bstep (se 1 (by rfl) ⟨3005261, by rfl⟩ : syracuseStep 4007015 = 6010523) B6010523
theorem B4508075 : Blo 1186410 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B16240609 : Blo 1186410 16240609 := bstep (se 2 (by rfl) ⟨6090228, by rfl⟩ : syracuseStep 16240609 = 12180457) B12180457
theorem B54817975 : Blo 1186410 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B17126639 : Blo 1186410 17126639 := bstep (se 1 (by rfl) ⟨12844979, by rfl⟩ : syracuseStep 17126639 = 25689959) B25689959
theorem B20839193 : Blo 1186410 20839193 := bstep (se 2 (by rfl) ⟨7814697, by rfl⟩ : syracuseStep 20839193 = 15629395) B15629395
theorem B25697387 : Blo 1186410 25697387 := bstep (se 1 (by rfl) ⟨19273040, by rfl⟩ : syracuseStep 25697387 = 38546081) B38546081
theorem B6012143 : Blo 1186410 6012143 := bstep (se 1 (by rfl) ⟨4509107, by rfl⟩ : syracuseStep 6012143 = 9018215) B9018215
theorem B1187775 : Blo 1186410 1187775 := bstep (se 1 (by rfl) ⟨890831, by rfl⟩ : syracuseStep 1187775 = 1781663) B1781663
theorem B2671343 : Blo 1186410 2671343 := bstep (se 1 (by rfl) ⟨2003507, by rfl⟩ : syracuseStep 2671343 = 4007015) B4007015
theorem B73090633 : Blo 1186410 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B17131591 : Blo 1186410 17131591 := bstep (se 1 (by rfl) ⟨12848693, by rfl⟩ : syracuseStep 17131591 = 25697387) B25697387
theorem B4008095 : Blo 1186410 4008095 := bstep (se 1 (by rfl) ⟨3006071, by rfl⟩ : syracuseStep 4008095 = 6012143) B6012143
theorem B21654145 : Blo 1186410 21654145 := bstep (se 2 (by rfl) ⟨8120304, by rfl⟩ : syracuseStep 21654145 = 16240609) B16240609
theorem B11417759 : Blo 1186410 11417759 := bstep (se 1 (by rfl) ⟨8563319, by rfl⟩ : syracuseStep 11417759 = 17126639) B17126639
theorem B3005383 : Blo 1186410 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B13892795 : Blo 1186410 13892795 := bstep (se 1 (by rfl) ⟨10419596, by rfl⟩ : syracuseStep 13892795 = 20839193) B20839193
theorem B4007177 : Blo 1186410 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B2672063 : Blo 1186410 2672063 := bstep (se 1 (by rfl) ⟨2004047, by rfl⟩ : syracuseStep 2672063 = 4008095) B4008095
theorem B7611839 : Blo 1186410 7611839 := bstep (se 1 (by rfl) ⟨5708879, by rfl⟩ : syracuseStep 7611839 = 11417759) B11417759
theorem B97454177 : Blo 1186410 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B22842121 : Blo 1186410 22842121 := bstep (se 2 (by rfl) ⟨8565795, by rfl⟩ : syracuseStep 22842121 = 17131591) B17131591
theorem B1780895 : Blo 1186410 1780895 := bstep (se 1 (by rfl) ⟨1335671, by rfl⟩ : syracuseStep 1780895 = 2671343) B2671343
theorem B9261863 : Blo 1186410 9261863 := bstep (se 1 (by rfl) ⟨6946397, by rfl⟩ : syracuseStep 9261863 = 13892795) B13892795
theorem B115488773 : Blo 1186410 115488773 := bstep (se 4 (by rfl) ⟨10827072, by rfl⟩ : syracuseStep 115488773 = 21654145) B21654145
theorem B2671451 : Blo 1186410 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B1781375 : Blo 1186410 1781375 := bstep (se 1 (by rfl) ⟨1336031, by rfl⟩ : syracuseStep 1781375 = 2672063) B2672063
theorem B5074559 : Blo 1186410 5074559 := bstep (se 1 (by rfl) ⟨3805919, by rfl⟩ : syracuseStep 5074559 = 7611839) B7611839
theorem B76992515 : Blo 1186410 76992515 := bstep (se 1 (by rfl) ⟨57744386, by rfl⟩ : syracuseStep 76992515 = 115488773) B115488773
theorem B6174575 : Blo 1186410 6174575 := bstep (se 1 (by rfl) ⟨4630931, by rfl⟩ : syracuseStep 6174575 = 9261863) B9261863
theorem B30456161 : Blo 1186410 30456161 := bstep (se 2 (by rfl) ⟨11421060, by rfl⟩ : syracuseStep 30456161 = 22842121) B22842121
theorem B64969451 : Blo 1186410 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B1187263 : Blo 1186410 1187263 := bstep (se 1 (by rfl) ⟨890447, by rfl⟩ : syracuseStep 1187263 = 1780895) B1780895
theorem B43312967 : Blo 1186410 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B1780967 : Blo 1186410 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B4116383 : Blo 1186410 4116383 := bstep (se 1 (by rfl) ⟨3087287, by rfl⟩ : syracuseStep 4116383 = 6174575) B6174575
theorem B20304107 : Blo 1186410 20304107 := bstep (se 1 (by rfl) ⟨15228080, by rfl⟩ : syracuseStep 20304107 = 30456161) B30456161
theorem B51328343 : Blo 1186410 51328343 := bstep (se 1 (by rfl) ⟨38496257, by rfl⟩ : syracuseStep 51328343 = 76992515) B76992515
theorem B1187583 : Blo 1186410 1187583 := bstep (se 1 (by rfl) ⟨890687, by rfl⟩ : syracuseStep 1187583 = 1781375) B1781375
theorem B3383039 : Blo 1186410 3383039 := bstep (se 1 (by rfl) ⟨2537279, by rfl⟩ : syracuseStep 3383039 = 5074559) B5074559
theorem B34218895 : Blo 1186410 34218895 := bstep (se 1 (by rfl) ⟨25664171, by rfl⟩ : syracuseStep 34218895 = 51328343) B51328343
theorem B2255359 : Blo 1186410 2255359 := bstep (se 1 (by rfl) ⟨1691519, by rfl⟩ : syracuseStep 2255359 = 3383039) B3383039
theorem B13536071 : Blo 1186410 13536071 := bstep (se 1 (by rfl) ⟨10152053, by rfl⟩ : syracuseStep 13536071 = 20304107) B20304107
theorem B28875311 : Blo 1186410 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B1187311 : Blo 1186410 1187311 := bstep (se 1 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 1187311 = 1780967) B1780967
theorem B2744255 : Blo 1186410 2744255 := bstep (se 1 (by rfl) ⟨2058191, by rfl⟩ : syracuseStep 2744255 = 4116383) B4116383
theorem B3007145 : Blo 1186410 3007145 := bstep (se 2 (by rfl) ⟨1127679, by rfl⟩ : syracuseStep 3007145 = 2255359) B2255359
theorem B1829503 : Blo 1186410 1829503 := bstep (se 1 (by rfl) ⟨1372127, by rfl⟩ : syracuseStep 1829503 = 2744255) B2744255
theorem B45625193 : Blo 1186410 45625193 := bstep (se 2 (by rfl) ⟨17109447, by rfl⟩ : syracuseStep 45625193 = 34218895) B34218895
theorem B9024047 : Blo 1186410 9024047 := bstep (se 1 (by rfl) ⟨6768035, by rfl⟩ : syracuseStep 9024047 = 13536071) B13536071
theorem B19250207 : Blo 1186410 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B6016031 : Blo 1186410 6016031 := bstep (se 1 (by rfl) ⟨4512023, by rfl⟩ : syracuseStep 6016031 = 9024047) B9024047
theorem B12833471 : Blo 1186410 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B2004763 : Blo 1186410 2004763 := bstep (se 1 (by rfl) ⟨1503572, by rfl⟩ : syracuseStep 2004763 = 3007145) B3007145
theorem B2439337 : Blo 1186410 2439337 := bstep (se 2 (by rfl) ⟨914751, by rfl⟩ : syracuseStep 2439337 = 1829503) B1829503
theorem B30416795 : Blo 1186410 30416795 := bstep (se 1 (by rfl) ⟨22812596, by rfl⟩ : syracuseStep 30416795 = 45625193) B45625193
theorem B3252449 : Blo 1186410 3252449 := bstep (se 2 (by rfl) ⟨1219668, by rfl⟩ : syracuseStep 3252449 = 2439337) B2439337
theorem B2673017 : Blo 1186410 2673017 := bstep (se 2 (by rfl) ⟨1002381, by rfl⟩ : syracuseStep 2673017 = 2004763) B2004763
theorem B20277863 : Blo 1186410 20277863 := bstep (se 1 (by rfl) ⟨15208397, by rfl⟩ : syracuseStep 20277863 = 30416795) B30416795
theorem B8555647 : Blo 1186410 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B4010687 : Blo 1186410 4010687 := bstep (se 1 (by rfl) ⟨3008015, by rfl⟩ : syracuseStep 4010687 = 6016031) B6016031
theorem B13518575 : Blo 1186410 13518575 := bstep (se 1 (by rfl) ⟨10138931, by rfl⟩ : syracuseStep 13518575 = 20277863) B20277863
theorem B2673791 : Blo 1186410 2673791 := bstep (se 1 (by rfl) ⟨2005343, by rfl⟩ : syracuseStep 2673791 = 4010687) B4010687
theorem B11407529 : Blo 1186410 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B1782011 : Blo 1186410 1782011 := bstep (se 1 (by rfl) ⟨1336508, by rfl⟩ : syracuseStep 1782011 = 2673017) B2673017
theorem B2168299 : Blo 1186410 2168299 := bstep (se 1 (by rfl) ⟨1626224, by rfl⟩ : syracuseStep 2168299 = 3252449) B3252449
theorem B1188007 : Blo 1186410 1188007 := bstep (se 1 (by rfl) ⟨891005, by rfl⟩ : syracuseStep 1188007 = 1782011) B1782011
theorem B9012383 : Blo 1186410 9012383 := bstep (se 1 (by rfl) ⟨6759287, by rfl⟩ : syracuseStep 9012383 = 13518575) B13518575
theorem B7605019 : Blo 1186410 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B1782527 : Blo 1186410 1782527 := bstep (se 1 (by rfl) ⟨1336895, by rfl⟩ : syracuseStep 1782527 = 2673791) B2673791
theorem B11564261 : Blo 1186410 11564261 := bstep (se 4 (by rfl) ⟨1084149, by rfl⟩ : syracuseStep 11564261 = 2168299) B2168299
theorem B1188351 : Blo 1186410 1188351 := bstep (se 1 (by rfl) ⟨891263, by rfl⟩ : syracuseStep 1188351 = 1782527) B1782527
theorem B7709507 : Blo 1186410 7709507 := bstep (se 1 (by rfl) ⟨5782130, by rfl⟩ : syracuseStep 7709507 = 11564261) B11564261
theorem B6008255 : Blo 1186410 6008255 := bstep (se 1 (by rfl) ⟨4506191, by rfl⟩ : syracuseStep 6008255 = 9012383) B9012383
theorem B10140025 : Blo 1186410 10140025 := bstep (se 2 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 10140025 = 7605019) B7605019
theorem B13520033 : Blo 1186410 13520033 := bstep (se 2 (by rfl) ⟨5070012, by rfl⟩ : syracuseStep 13520033 = 10140025) B10140025
theorem B5139671 : Blo 1186410 5139671 := bstep (se 1 (by rfl) ⟨3854753, by rfl⟩ : syracuseStep 5139671 = 7709507) B7709507
theorem B4005503 : Blo 1186410 4005503 := bstep (se 1 (by rfl) ⟨3004127, by rfl⟩ : syracuseStep 4005503 = 6008255) B6008255
theorem B13705789 : Blo 1186410 13705789 := bstep (se 3 (by rfl) ⟨2569835, by rfl⟩ : syracuseStep 13705789 = 5139671) B5139671
theorem B9013355 : Blo 1186410 9013355 := bstep (se 1 (by rfl) ⟨6760016, by rfl⟩ : syracuseStep 9013355 = 13520033) B13520033
theorem B2670335 : Blo 1186410 2670335 := bstep (se 1 (by rfl) ⟨2002751, by rfl⟩ : syracuseStep 2670335 = 4005503) B4005503
theorem B1780223 : Blo 1186410 1780223 := bstep (se 1 (by rfl) ⟨1335167, by rfl⟩ : syracuseStep 1780223 = 2670335) B2670335
theorem B6008903 : Blo 1186410 6008903 := bstep (se 1 (by rfl) ⟨4506677, by rfl⟩ : syracuseStep 6008903 = 9013355) B9013355
theorem B18274385 : Blo 1186410 18274385 := bstep (se 2 (by rfl) ⟨6852894, by rfl⟩ : syracuseStep 18274385 = 13705789) B13705789
theorem B4005935 : Blo 1186410 4005935 := bstep (se 1 (by rfl) ⟨3004451, by rfl⟩ : syracuseStep 4005935 = 6008903) B6008903
theorem B12182923 : Blo 1186410 12182923 := bstep (se 1 (by rfl) ⟨9137192, by rfl⟩ : syracuseStep 12182923 = 18274385) B18274385
theorem B1186815 : Blo 1186410 1186815 := bstep (se 1 (by rfl) ⟨890111, by rfl⟩ : syracuseStep 1186815 = 1780223) B1780223
theorem B2670623 : Blo 1186410 2670623 := bstep (se 1 (by rfl) ⟨2002967, by rfl⟩ : syracuseStep 2670623 = 4005935) B4005935
theorem B16243897 : Blo 1186410 16243897 := bstep (se 2 (by rfl) ⟨6091461, by rfl⟩ : syracuseStep 16243897 = 12182923) B12182923
theorem B1780415 : Blo 1186410 1780415 := bstep (se 1 (by rfl) ⟨1335311, by rfl⟩ : syracuseStep 1780415 = 2670623) B2670623
theorem B21658529 : Blo 1186410 21658529 := bstep (se 2 (by rfl) ⟨8121948, by rfl⟩ : syracuseStep 21658529 = 16243897) B16243897
theorem B14439019 : Blo 1186410 14439019 := bstep (se 1 (by rfl) ⟨10829264, by rfl⟩ : syracuseStep 14439019 = 21658529) B21658529
theorem B1186943 : Blo 1186410 1186943 := bstep (se 1 (by rfl) ⟨890207, by rfl⟩ : syracuseStep 1186943 = 1780415) B1780415
theorem B19252025 : Blo 1186410 19252025 := bstep (se 2 (by rfl) ⟨7219509, by rfl⟩ : syracuseStep 19252025 = 14439019) B14439019
theorem B12834683 : Blo 1186410 12834683 := bstep (se 1 (by rfl) ⟨9626012, by rfl⟩ : syracuseStep 12834683 = 19252025) B19252025
theorem B8556455 : Blo 1186410 8556455 := bstep (se 1 (by rfl) ⟨6417341, by rfl⟩ : syracuseStep 8556455 = 12834683) B12834683
theorem B22817213 : Blo 1186410 22817213 := bstep (se 3 (by rfl) ⟨4278227, by rfl⟩ : syracuseStep 22817213 = 8556455) B8556455
theorem B15211475 : Blo 1186410 15211475 := bstep (se 1 (by rfl) ⟨11408606, by rfl⟩ : syracuseStep 15211475 = 22817213) B22817213
theorem B10140983 : Blo 1186410 10140983 := bstep (se 1 (by rfl) ⟨7605737, by rfl⟩ : syracuseStep 10140983 = 15211475) B15211475
theorem B6760655 : Blo 1186410 6760655 := bstep (se 1 (by rfl) ⟨5070491, by rfl⟩ : syracuseStep 6760655 = 10140983) B10140983
theorem B4507103 : Blo 1186410 4507103 := bstep (se 1 (by rfl) ⟨3380327, by rfl⟩ : syracuseStep 4507103 = 6760655) B6760655
theorem B3004735 : Blo 1186410 3004735 := bstep (se 1 (by rfl) ⟨2253551, by rfl⟩ : syracuseStep 3004735 = 4507103) B4507103
theorem B4006313 : Blo 1186410 4006313 := bstep (se 2 (by rfl) ⟨1502367, by rfl⟩ : syracuseStep 4006313 = 3004735) B3004735
theorem B2670875 : Blo 1186410 2670875 := bstep (se 1 (by rfl) ⟨2003156, by rfl⟩ : syracuseStep 2670875 = 4006313) B4006313
theorem B1780583 : Blo 1186410 1780583 := bstep (se 1 (by rfl) ⟨1335437, by rfl⟩ : syracuseStep 1780583 = 2670875) B2670875
theorem B1187055 : Blo 1186410 1187055 := bstep (se 1 (by rfl) ⟨890291, by rfl⟩ : syracuseStep 1187055 = 1780583) B1780583

theorem C0 (j : ℕ) (h1 : 296602 ≤ j) (h2 : j ≤ 297101) : Blo 1186410 (4 * j + 3) := by
  interval_cases j
  · exact B1186411
  · exact B1186415
  · exact B1186419
  · exact B1186423
  · exact B1186427
  · exact B1186431
  · exact B1186435
  · exact B1186439
  · exact B1186443
  · exact B1186447
  · exact B1186451
  · exact B1186455
  · exact B1186459
  · exact B1186463
  · exact B1186467
  · exact B1186471
  · exact B1186475
  · exact B1186479
  · exact B1186483
  · exact B1186487
  · exact B1186491
  · exact B1186495
  · exact B1186499
  · exact B1186503
  · exact B1186507
  · exact B1186511
  · exact B1186515
  · exact B1186519
  · exact B1186523
  · exact B1186527
  · exact B1186531
  · exact B1186535
  · exact B1186539
  · exact B1186543
  · exact B1186547
  · exact B1186551
  · exact B1186555
  · exact B1186559
  · exact B1186563
  · exact B1186567
  · exact B1186571
  · exact B1186575
  · exact B1186579
  · exact B1186583
  · exact B1186587
  · exact B1186591
  · exact B1186595
  · exact B1186599
  · exact B1186603
  · exact B1186607
  · exact B1186611
  · exact B1186615
  · exact B1186619
  · exact B1186623
  · exact B1186627
  · exact B1186631
  · exact B1186635
  · exact B1186639
  · exact B1186643
  · exact B1186647
  · exact B1186651
  · exact B1186655
  · exact B1186659
  · exact B1186663
  · exact B1186667
  · exact B1186671
  · exact B1186675
  · exact B1186679
  · exact B1186683
  · exact B1186687
  · exact B1186691
  · exact B1186695
  · exact B1186699
  · exact B1186703
  · exact B1186707
  · exact B1186711
  · exact B1186715
  · exact B1186719
  · exact B1186723
  · exact B1186727
  · exact B1186731
  · exact B1186735
  · exact B1186739
  · exact B1186743
  · exact B1186747
  · exact B1186751
  · exact B1186755
  · exact B1186759
  · exact B1186763
  · exact B1186767
  · exact B1186771
  · exact B1186775
  · exact B1186779
  · exact B1186783
  · exact B1186787
  · exact B1186791
  · exact B1186795
  · exact B1186799
  · exact B1186803
  · exact B1186807
  · exact B1186811
  · exact B1186815
  · exact B1186819
  · exact B1186823
  · exact B1186827
  · exact B1186831
  · exact B1186835
  · exact B1186839
  · exact B1186843
  · exact B1186847
  · exact B1186851
  · exact B1186855
  · exact B1186859
  · exact B1186863
  · exact B1186867
  · exact B1186871
  · exact B1186875
  · exact B1186879
  · exact B1186883
  · exact B1186887
  · exact B1186891
  · exact B1186895
  · exact B1186899
  · exact B1186903
  · exact B1186907
  · exact B1186911
  · exact B1186915
  · exact B1186919
  · exact B1186923
  · exact B1186927
  · exact B1186931
  · exact B1186935
  · exact B1186939
  · exact B1186943
  · exact B1186947
  · exact B1186951
  · exact B1186955
  · exact B1186959
  · exact B1186963
  · exact B1186967
  · exact B1186971
  · exact B1186975
  · exact B1186979
  · exact B1186983
  · exact B1186987
  · exact B1186991
  · exact B1186995
  · exact B1186999
  · exact B1187003
  · exact B1187007
  · exact B1187011
  · exact B1187015
  · exact B1187019
  · exact B1187023
  · exact B1187027
  · exact B1187031
  · exact B1187035
  · exact B1187039
  · exact B1187043
  · exact B1187047
  · exact B1187051
  · exact B1187055
  · exact B1187059
  · exact B1187063
  · exact B1187067
  · exact B1187071
  · exact B1187075
  · exact B1187079
  · exact B1187083
  · exact B1187087
  · exact B1187091
  · exact B1187095
  · exact B1187099
  · exact B1187103
  · exact B1187107
  · exact B1187111
  · exact B1187115
  · exact B1187119
  · exact B1187123
  · exact B1187127
  · exact B1187131
  · exact B1187135
  · exact B1187139
  · exact B1187143
  · exact B1187147
  · exact B1187151
  · exact B1187155
  · exact B1187159
  · exact B1187163
  · exact B1187167
  · exact B1187171
  · exact B1187175
  · exact B1187179
  · exact B1187183
  · exact B1187187
  · exact B1187191
  · exact B1187195
  · exact B1187199
  · exact B1187203
  · exact B1187207
  · exact B1187211
  · exact B1187215
  · exact B1187219
  · exact B1187223
  · exact B1187227
  · exact B1187231
  · exact B1187235
  · exact B1187239
  · exact B1187243
  · exact B1187247
  · exact B1187251
  · exact B1187255
  · exact B1187259
  · exact B1187263
  · exact B1187267
  · exact B1187271
  · exact B1187275
  · exact B1187279
  · exact B1187283
  · exact B1187287
  · exact B1187291
  · exact B1187295
  · exact B1187299
  · exact B1187303
  · exact B1187307
  · exact B1187311
  · exact B1187315
  · exact B1187319
  · exact B1187323
  · exact B1187327
  · exact B1187331
  · exact B1187335
  · exact B1187339
  · exact B1187343
  · exact B1187347
  · exact B1187351
  · exact B1187355
  · exact B1187359
  · exact B1187363
  · exact B1187367
  · exact B1187371
  · exact B1187375
  · exact B1187379
  · exact B1187383
  · exact B1187387
  · exact B1187391
  · exact B1187395
  · exact B1187399
  · exact B1187403
  · exact B1187407
  · exact B1187411
  · exact B1187415
  · exact B1187419
  · exact B1187423
  · exact B1187427
  · exact B1187431
  · exact B1187435
  · exact B1187439
  · exact B1187443
  · exact B1187447
  · exact B1187451
  · exact B1187455
  · exact B1187459
  · exact B1187463
  · exact B1187467
  · exact B1187471
  · exact B1187475
  · exact B1187479
  · exact B1187483
  · exact B1187487
  · exact B1187491
  · exact B1187495
  · exact B1187499
  · exact B1187503
  · exact B1187507
  · exact B1187511
  · exact B1187515
  · exact B1187519
  · exact B1187523
  · exact B1187527
  · exact B1187531
  · exact B1187535
  · exact B1187539
  · exact B1187543
  · exact B1187547
  · exact B1187551
  · exact B1187555
  · exact B1187559
  · exact B1187563
  · exact B1187567
  · exact B1187571
  · exact B1187575
  · exact B1187579
  · exact B1187583
  · exact B1187587
  · exact B1187591
  · exact B1187595
  · exact B1187599
  · exact B1187603
  · exact B1187607
  · exact B1187611
  · exact B1187615
  · exact B1187619
  · exact B1187623
  · exact B1187627
  · exact B1187631
  · exact B1187635
  · exact B1187639
  · exact B1187643
  · exact B1187647
  · exact B1187651
  · exact B1187655
  · exact B1187659
  · exact B1187663
  · exact B1187667
  · exact B1187671
  · exact B1187675
  · exact B1187679
  · exact B1187683
  · exact B1187687
  · exact B1187691
  · exact B1187695
  · exact B1187699
  · exact B1187703
  · exact B1187707
  · exact B1187711
  · exact B1187715
  · exact B1187719
  · exact B1187723
  · exact B1187727
  · exact B1187731
  · exact B1187735
  · exact B1187739
  · exact B1187743
  · exact B1187747
  · exact B1187751
  · exact B1187755
  · exact B1187759
  · exact B1187763
  · exact B1187767
  · exact B1187771
  · exact B1187775
  · exact B1187779
  · exact B1187783
  · exact B1187787
  · exact B1187791
  · exact B1187795
  · exact B1187799
  · exact B1187803
  · exact B1187807
  · exact B1187811
  · exact B1187815
  · exact B1187819
  · exact B1187823
  · exact B1187827
  · exact B1187831
  · exact B1187835
  · exact B1187839
  · exact B1187843
  · exact B1187847
  · exact B1187851
  · exact B1187855
  · exact B1187859
  · exact B1187863
  · exact B1187867
  · exact B1187871
  · exact B1187875
  · exact B1187879
  · exact B1187883
  · exact B1187887
  · exact B1187891
  · exact B1187895
  · exact B1187899
  · exact B1187903
  · exact B1187907
  · exact B1187911
  · exact B1187915
  · exact B1187919
  · exact B1187923
  · exact B1187927
  · exact B1187931
  · exact B1187935
  · exact B1187939
  · exact B1187943
  · exact B1187947
  · exact B1187951
  · exact B1187955
  · exact B1187959
  · exact B1187963
  · exact B1187967
  · exact B1187971
  · exact B1187975
  · exact B1187979
  · exact B1187983
  · exact B1187987
  · exact B1187991
  · exact B1187995
  · exact B1187999
  · exact B1188003
  · exact B1188007
  · exact B1188011
  · exact B1188015
  · exact B1188019
  · exact B1188023
  · exact B1188027
  · exact B1188031
  · exact B1188035
  · exact B1188039
  · exact B1188043
  · exact B1188047
  · exact B1188051
  · exact B1188055
  · exact B1188059
  · exact B1188063
  · exact B1188067
  · exact B1188071
  · exact B1188075
  · exact B1188079
  · exact B1188083
  · exact B1188087
  · exact B1188091
  · exact B1188095
  · exact B1188099
  · exact B1188103
  · exact B1188107
  · exact B1188111
  · exact B1188115
  · exact B1188119
  · exact B1188123
  · exact B1188127
  · exact B1188131
  · exact B1188135
  · exact B1188139
  · exact B1188143
  · exact B1188147
  · exact B1188151
  · exact B1188155
  · exact B1188159
  · exact B1188163
  · exact B1188167
  · exact B1188171
  · exact B1188175
  · exact B1188179
  · exact B1188183
  · exact B1188187
  · exact B1188191
  · exact B1188195
  · exact B1188199
  · exact B1188203
  · exact B1188207
  · exact B1188211
  · exact B1188215
  · exact B1188219
  · exact B1188223
  · exact B1188227
  · exact B1188231
  · exact B1188235
  · exact B1188239
  · exact B1188243
  · exact B1188247
  · exact B1188251
  · exact B1188255
  · exact B1188259
  · exact B1188263
  · exact B1188267
  · exact B1188271
  · exact B1188275
  · exact B1188279
  · exact B1188283
  · exact B1188287
  · exact B1188291
  · exact B1188295
  · exact B1188299
  · exact B1188303
  · exact B1188307
  · exact B1188311
  · exact B1188315
  · exact B1188319
  · exact B1188323
  · exact B1188327
  · exact B1188331
  · exact B1188335
  · exact B1188339
  · exact B1188343
  · exact B1188347
  · exact B1188351
  · exact B1188355
  · exact B1188359
  · exact B1188363
  · exact B1188367
  · exact B1188371
  · exact B1188375
  · exact B1188379
  · exact B1188383
  · exact B1188387
  · exact B1188391
  · exact B1188395
  · exact B1188399
  · exact B1188403
  · exact B1188407

theorem solution (m : ℕ) (hlo : 1186410 ≤ m) (hhi : m ≤ 1188410) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 296602 ≤ j := by omega
    have hj2 : j ≤ 297101 := by omega
    have hb : Blo 1186410 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
