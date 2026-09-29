-- Prove2me | solution 1 for syracuse_descends_range_471786_475786
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:04.362287+00:00
-- url     : https://prove2.me/submissions/b2d836f5-0eee-45c9-8ac3-6d5bd7e39bc0

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


theorem B3604661 : Blo 471786 3604661 := bbase (se 5 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 3604661 = 337937) (by norm_num)
theorem B1016101 : Blo 471786 1016101 := bbase (se 4 (by rfl) ⟨95259, by rfl⟩ : syracuseStep 1016101 = 190519) (by norm_num)
theorem B6816469 : Blo 471786 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B721693 : Blo 471786 721693 := bbase (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) (by norm_num)
theorem B1278773 : Blo 471786 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B2392901 : Blo 471786 2392901 := bbase (se 4 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 2392901 = 448669) (by norm_num)
theorem B852925 : Blo 471786 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B1705157 : Blo 471786 1705157 := bbase (se 4 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 1705157 = 319717) (by norm_num)
theorem B853213 : Blo 471786 853213 := bbase (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) (by norm_num)
theorem B722197 : Blo 471786 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B1344869 : Blo 471786 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B1803653 : Blo 471786 1803653 := bbase (se 4 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 1803653 = 338185) (by norm_num)
theorem B1705445 : Blo 471786 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B820709 : Blo 471786 820709 := bbase (se 4 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 820709 = 153883) (by norm_num)
theorem B722405 : Blo 471786 722405 := bbase (se 4 (by rfl) ⟨67725, by rfl⟩ : syracuseStep 722405 = 135451) (by norm_num)
theorem B722477 : Blo 471786 722477 := bbase (se 3 (by rfl) ⟨135464, by rfl⟩ : syracuseStep 722477 = 270929) (by norm_num)
theorem B1312405 : Blo 471786 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B1803941 : Blo 471786 1803941 := bbase (se 4 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 1803941 = 338239) (by norm_num)
theorem B853789 : Blo 471786 853789 := bbase (se 3 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 853789 = 320171) (by norm_num)
theorem B722861 : Blo 471786 722861 := bbase (se 3 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 722861 = 271073) (by norm_num)
theorem B755797 : Blo 471786 755797 := bbase (se 8 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 755797 = 8857) (by norm_num)
theorem B2394197 : Blo 471786 2394197 := bbase (se 8 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 2394197 = 28057) (by norm_num)
theorem B1149085 : Blo 471786 1149085 := bbase (se 3 (by rfl) ⟨215453, by rfl⟩ : syracuseStep 1149085 = 430907) (by norm_num)
theorem B854309 : Blo 471786 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B1346053 : Blo 471786 1346053 := bbase (se 4 (by rfl) ⟨126192, by rfl⟩ : syracuseStep 1346053 = 252385) (by norm_num)
theorem B854669 : Blo 471786 854669 := bbase (se 3 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 854669 = 320501) (by norm_num)
theorem B1346213 : Blo 471786 1346213 := bbase (se 4 (by rfl) ⟨126207, by rfl⟩ : syracuseStep 1346213 = 252415) (by norm_num)
theorem B854821 : Blo 471786 854821 := bbase (se 4 (by rfl) ⟨80139, by rfl⟩ : syracuseStep 854821 = 160279) (by norm_num)
theorem B1805125 : Blo 471786 1805125 := bbase (se 4 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 1805125 = 338461) (by norm_num)
theorem B1346453 : Blo 471786 1346453 := bbase (se 6 (by rfl) ⟨31557, by rfl⟩ : syracuseStep 1346453 = 63115) (by norm_num)
theorem B4557845 : Blo 471786 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B1346645 : Blo 471786 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B1805429 : Blo 471786 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B757021 : Blo 471786 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B625957 : Blo 471786 625957 := bbase (se 4 (by rfl) ⟨58683, by rfl⟩ : syracuseStep 625957 = 117367) (by norm_num)
theorem B2395493 : Blo 471786 2395493 := bbase (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) (by norm_num)
theorem B1707493 : Blo 471786 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B1281541 : Blo 471786 1281541 := bbase (se 4 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 1281541 = 240289) (by norm_num)
theorem B2559509 : Blo 471786 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B626213 : Blo 471786 626213 := bbase (se 4 (by rfl) ⟨58707, by rfl⟩ : syracuseStep 626213 = 117415) (by norm_num)
theorem B1248821 : Blo 471786 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B1707637 : Blo 471786 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1707797 : Blo 471786 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B855917 : Blo 471786 855917 := bbase (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) (by norm_num)
theorem B1707925 : Blo 471786 1707925 := bbase (se 6 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 1707925 = 80059) (by norm_num)
theorem B757693 : Blo 471786 757693 := bbase (se 3 (by rfl) ⟨142067, by rfl⟩ : syracuseStep 757693 = 284135) (by norm_num)
theorem B1347637 : Blo 471786 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B2199653 : Blo 471786 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2396789 : Blo 471786 2396789 := bbase (se 5 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 2396789 = 224699) (by norm_num)
theorem B758693 : Blo 471786 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B1348741 : Blo 471786 1348741 := bbase (se 4 (by rfl) ⟨126444, by rfl⟩ : syracuseStep 1348741 = 252889) (by norm_num)
theorem B1283365 : Blo 471786 1283365 := bbase (se 4 (by rfl) ⟨120315, by rfl⟩ : syracuseStep 1283365 = 240631) (by norm_num)
theorem B2594261 : Blo 471786 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B2168309 : Blo 471786 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B1218053 : Blo 471786 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1218277 : Blo 471786 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B5117717 : Blo 471786 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B2398085 : Blo 471786 2398085 := bbase (se 4 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 2398085 = 449641) (by norm_num)
theorem B1513541 : Blo 471786 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B923773 : Blo 471786 923773 := bbase (se 3 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 923773 = 346415) (by norm_num)
theorem B956549 : Blo 471786 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B792845 : Blo 471786 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B5773589 : Blo 471786 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B530761 : Blo 471786 530761 := bbase (se 2 (by rfl) ⟨199035, by rfl⟩ : syracuseStep 530761 = 398071) (by norm_num)
theorem B530797 : Blo 471786 530797 := bbase (se 3 (by rfl) ⟨99524, by rfl⟩ : syracuseStep 530797 = 199049) (by norm_num)
theorem B760205 : Blo 471786 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B530833 : Blo 471786 530833 := bbase (se 2 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 530833 = 398125) (by norm_num)
theorem B530869 : Blo 471786 530869 := bbase (se 5 (by rfl) ⟨24884, by rfl⟩ : syracuseStep 530869 = 49769) (by norm_num)
theorem B530905 : Blo 471786 530905 := bbase (se 2 (by rfl) ⟨199089, by rfl⟩ : syracuseStep 530905 = 398179) (by norm_num)
theorem B530941 : Blo 471786 530941 := bbase (se 3 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 530941 = 199103) (by norm_num)
theorem B530977 : Blo 471786 530977 := bbase (se 2 (by rfl) ⟨199116, by rfl⟩ : syracuseStep 530977 = 398233) (by norm_num)
theorem B3414581 : Blo 471786 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B531013 : Blo 471786 531013 := bbase (se 4 (by rfl) ⟨49782, by rfl⟩ : syracuseStep 531013 = 99565) (by norm_num)
theorem B1350245 : Blo 471786 1350245 := bbase (se 4 (by rfl) ⟨126585, by rfl⟩ : syracuseStep 1350245 = 253171) (by norm_num)
theorem B531049 : Blo 471786 531049 := bbase (se 2 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 531049 = 398287) (by norm_num)
theorem B531085 : Blo 471786 531085 := bbase (se 3 (by rfl) ⟨99578, by rfl⟩ : syracuseStep 531085 = 199157) (by norm_num)
theorem B727693 : Blo 471786 727693 := bbase (se 3 (by rfl) ⟨136442, by rfl⟩ : syracuseStep 727693 = 272885) (by norm_num)
theorem B531121 : Blo 471786 531121 := bbase (se 2 (by rfl) ⟨199170, by rfl⟩ : syracuseStep 531121 = 398341) (by norm_num)
theorem B957109 : Blo 471786 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B531157 : Blo 471786 531157 := bbase (se 7 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 531157 = 12449) (by norm_num)
theorem B531193 : Blo 471786 531193 := bbase (se 2 (by rfl) ⟨199197, by rfl⟩ : syracuseStep 531193 = 398395) (by norm_num)
theorem B531229 : Blo 471786 531229 := bbase (se 3 (by rfl) ⟨99605, by rfl⟩ : syracuseStep 531229 = 199211) (by norm_num)
theorem B531265 : Blo 471786 531265 := bbase (se 2 (by rfl) ⟨199224, by rfl⟩ : syracuseStep 531265 = 398449) (by norm_num)
theorem B957269 : Blo 471786 957269 := bbase (se 9 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 957269 = 5609) (by norm_num)
theorem B760661 : Blo 471786 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B531301 : Blo 471786 531301 := bbase (se 4 (by rfl) ⟨49809, by rfl⟩ : syracuseStep 531301 = 99619) (by norm_num)
theorem B531337 : Blo 471786 531337 := bbase (se 2 (by rfl) ⟨199251, by rfl⟩ : syracuseStep 531337 = 398503) (by norm_num)
theorem B531373 : Blo 471786 531373 := bbase (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) (by norm_num)
theorem B531409 : Blo 471786 531409 := bbase (se 2 (by rfl) ⟨199278, by rfl⟩ : syracuseStep 531409 = 398557) (by norm_num)
theorem B1022933 : Blo 471786 1022933 := bbase (se 7 (by rfl) ⟨11987, by rfl⟩ : syracuseStep 1022933 = 23975) (by norm_num)
theorem B531445 : Blo 471786 531445 := bbase (se 5 (by rfl) ⟨24911, by rfl⟩ : syracuseStep 531445 = 49823) (by norm_num)
theorem B531481 : Blo 471786 531481 := bbase (se 2 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 531481 = 398611) (by norm_num)
theorem B531517 : Blo 471786 531517 := bbase (se 3 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 531517 = 199319) (by norm_num)
theorem B531553 : Blo 471786 531553 := bbase (se 2 (by rfl) ⟨199332, by rfl⟩ : syracuseStep 531553 = 398665) (by norm_num)
theorem B531589 : Blo 471786 531589 := bbase (se 4 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 531589 = 99673) (by norm_num)
theorem B2694293 : Blo 471786 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2399381 : Blo 471786 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B531625 : Blo 471786 531625 := bbase (se 2 (by rfl) ⟨199359, by rfl⟩ : syracuseStep 531625 = 398719) (by norm_num)
theorem B531661 : Blo 471786 531661 := bbase (se 3 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 531661 = 199373) (by norm_num)
theorem B597233 : Blo 471786 597233 := bbase (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) (by norm_num)
theorem B531697 : Blo 471786 531697 := bbase (se 2 (by rfl) ⟨199386, by rfl⟩ : syracuseStep 531697 = 398773) (by norm_num)
theorem B531733 : Blo 471786 531733 := bbase (se 6 (by rfl) ⟨12462, by rfl⟩ : syracuseStep 531733 = 24925) (by norm_num)
theorem B597289 : Blo 471786 597289 := bbase (se 2 (by rfl) ⟨223983, by rfl⟩ : syracuseStep 597289 = 447967) (by norm_num)
theorem B531769 : Blo 471786 531769 := bbase (se 2 (by rfl) ⟨199413, by rfl⟩ : syracuseStep 531769 = 398827) (by norm_num)
theorem B531805 : Blo 471786 531805 := bbase (se 3 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 531805 = 199427) (by norm_num)
theorem B531841 : Blo 471786 531841 := bbase (se 2 (by rfl) ⟨199440, by rfl⟩ : syracuseStep 531841 = 398881) (by norm_num)
theorem B597385 : Blo 471786 597385 := bbase (se 2 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 597385 = 448039) (by norm_num)
theorem B957853 : Blo 471786 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B531877 : Blo 471786 531877 := bbase (se 4 (by rfl) ⟨49863, by rfl⟩ : syracuseStep 531877 = 99727) (by norm_num)
theorem B531913 : Blo 471786 531913 := bbase (se 2 (by rfl) ⟨199467, by rfl⟩ : syracuseStep 531913 = 398935) (by norm_num)
theorem B531949 : Blo 471786 531949 := bbase (se 3 (by rfl) ⟨99740, by rfl⟩ : syracuseStep 531949 = 199481) (by norm_num)
theorem B531985 : Blo 471786 531985 := bbase (se 2 (by rfl) ⟨199494, by rfl⟩ : syracuseStep 531985 = 398989) (by norm_num)
theorem B4562453 : Blo 471786 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B597557 : Blo 471786 597557 := bbase (se 5 (by rfl) ⟨28010, by rfl⟩ : syracuseStep 597557 = 56021) (by norm_num)
theorem B532021 : Blo 471786 532021 := bbase (se 5 (by rfl) ⟨24938, by rfl⟩ : syracuseStep 532021 = 49877) (by norm_num)
theorem B532057 : Blo 471786 532057 := bbase (se 2 (by rfl) ⟨199521, by rfl⟩ : syracuseStep 532057 = 399043) (by norm_num)
theorem B597613 : Blo 471786 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B532093 : Blo 471786 532093 := bbase (se 3 (by rfl) ⟨99767, by rfl⟩ : syracuseStep 532093 = 199535) (by norm_num)
theorem B532129 : Blo 471786 532129 := bbase (se 2 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 532129 = 399097) (by norm_num)
theorem B532165 : Blo 471786 532165 := bbase (se 4 (by rfl) ⟨49890, by rfl⟩ : syracuseStep 532165 = 99781) (by norm_num)
theorem B597709 : Blo 471786 597709 := bbase (se 3 (by rfl) ⟨112070, by rfl⟩ : syracuseStep 597709 = 224141) (by norm_num)
theorem B532201 : Blo 471786 532201 := bbase (se 2 (by rfl) ⟨199575, by rfl⟩ : syracuseStep 532201 = 399151) (by norm_num)
theorem B532237 : Blo 471786 532237 := bbase (se 3 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 532237 = 199589) (by norm_num)
theorem B3612437 : Blo 471786 3612437 := bbase (se 6 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 3612437 = 169333) (by norm_num)
theorem B532273 : Blo 471786 532273 := bbase (se 2 (by rfl) ⟨199602, by rfl⟩ : syracuseStep 532273 = 399205) (by norm_num)
theorem B761653 : Blo 471786 761653 := bbase (se 5 (by rfl) ⟨35702, by rfl⟩ : syracuseStep 761653 = 71405) (by norm_num)
theorem B532309 : Blo 471786 532309 := bbase (se 9 (by rfl) ⟨1559, by rfl⟩ : syracuseStep 532309 = 3119) (by norm_num)
theorem B597881 : Blo 471786 597881 := bbase (se 2 (by rfl) ⟨224205, by rfl⟩ : syracuseStep 597881 = 448411) (by norm_num)
theorem B532345 : Blo 471786 532345 := bbase (se 2 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 532345 = 399259) (by norm_num)
theorem B532381 : Blo 471786 532381 := bbase (se 3 (by rfl) ⟨99821, by rfl⟩ : syracuseStep 532381 = 199643) (by norm_num)
theorem B597937 : Blo 471786 597937 := bbase (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) (by norm_num)
theorem B532417 : Blo 471786 532417 := bbase (se 2 (by rfl) ⟨199656, by rfl⟩ : syracuseStep 532417 = 399313) (by norm_num)
theorem B532453 : Blo 471786 532453 := bbase (se 4 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 532453 = 99835) (by norm_num)
theorem B532489 : Blo 471786 532489 := bbase (se 2 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 532489 = 399367) (by norm_num)
theorem B598033 : Blo 471786 598033 := bbase (se 2 (by rfl) ⟨224262, by rfl⟩ : syracuseStep 598033 = 448525) (by norm_num)
theorem B532525 : Blo 471786 532525 := bbase (se 3 (by rfl) ⟨99848, by rfl⟩ : syracuseStep 532525 = 199697) (by norm_num)
theorem B532561 : Blo 471786 532561 := bbase (se 2 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 532561 = 399421) (by norm_num)
theorem B39297109 : Blo 471786 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B532597 : Blo 471786 532597 := bbase (se 5 (by rfl) ⟨24965, by rfl⟩ : syracuseStep 532597 = 49931) (by norm_num)
theorem B9117845 : Blo 471786 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B1351829 : Blo 471786 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B532633 : Blo 471786 532633 := bbase (se 2 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 532633 = 399475) (by norm_num)
theorem B598205 : Blo 471786 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B532669 : Blo 471786 532669 := bbase (se 3 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 532669 = 199751) (by norm_num)
theorem B532705 : Blo 471786 532705 := bbase (se 2 (by rfl) ⟨199764, by rfl⟩ : syracuseStep 532705 = 399529) (by norm_num)
theorem B598261 : Blo 471786 598261 := bbase (se 5 (by rfl) ⟨28043, by rfl⟩ : syracuseStep 598261 = 56087) (by norm_num)
theorem B532741 : Blo 471786 532741 := bbase (se 4 (by rfl) ⟨49944, by rfl⟩ : syracuseStep 532741 = 99889) (by norm_num)
theorem B1515797 : Blo 471786 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B532777 : Blo 471786 532777 := bbase (se 2 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 532777 = 399583) (by norm_num)
theorem B2695477 : Blo 471786 2695477 := bbase (se 5 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 2695477 = 252701) (by norm_num)
theorem B532813 : Blo 471786 532813 := bbase (se 3 (by rfl) ⟨99902, by rfl⟩ : syracuseStep 532813 = 199805) (by norm_num)
theorem B598357 : Blo 471786 598357 := bbase (se 10 (by rfl) ⟨876, by rfl⟩ : syracuseStep 598357 = 1753) (by norm_num)
theorem B2466133 : Blo 471786 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B532849 : Blo 471786 532849 := bbase (se 2 (by rfl) ⟨199818, by rfl⟩ : syracuseStep 532849 = 399637) (by norm_num)
theorem B1515925 : Blo 471786 1515925 := bbase (se 6 (by rfl) ⟨35529, by rfl⟩ : syracuseStep 1515925 = 71059) (by norm_num)
theorem B532885 : Blo 471786 532885 := bbase (se 6 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 532885 = 24979) (by norm_num)
theorem B2400677 : Blo 471786 2400677 := bbase (se 4 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 2400677 = 450127) (by norm_num)
theorem B532921 : Blo 471786 532921 := bbase (se 2 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 532921 = 399691) (by norm_num)
theorem B532957 : Blo 471786 532957 := bbase (se 3 (by rfl) ⟨99929, by rfl⟩ : syracuseStep 532957 = 199859) (by norm_num)
theorem B598529 : Blo 471786 598529 := bbase (se 2 (by rfl) ⟨224448, by rfl⟩ : syracuseStep 598529 = 448897) (by norm_num)
theorem B532993 : Blo 471786 532993 := bbase (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) (by norm_num)
theorem B533029 : Blo 471786 533029 := bbase (se 4 (by rfl) ⟨49971, by rfl⟩ : syracuseStep 533029 = 99943) (by norm_num)
theorem B598585 : Blo 471786 598585 := bbase (se 2 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 598585 = 448939) (by norm_num)
theorem B533065 : Blo 471786 533065 := bbase (se 2 (by rfl) ⟨199899, by rfl⟩ : syracuseStep 533065 = 399799) (by norm_num)
theorem B4039253 : Blo 471786 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B1614437 : Blo 471786 1614437 := bbase (se 4 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 1614437 = 302707) (by norm_num)
theorem B533101 : Blo 471786 533101 := bbase (se 3 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 533101 = 199913) (by norm_num)
theorem B533137 : Blo 471786 533137 := bbase (se 2 (by rfl) ⟨199926, by rfl⟩ : syracuseStep 533137 = 399853) (by norm_num)
theorem B598681 : Blo 471786 598681 := bbase (se 2 (by rfl) ⟨224505, by rfl⟩ : syracuseStep 598681 = 449011) (by norm_num)
theorem B533173 : Blo 471786 533173 := bbase (se 5 (by rfl) ⟨24992, by rfl⟩ : syracuseStep 533173 = 49985) (by norm_num)
theorem B533209 : Blo 471786 533209 := bbase (se 2 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 533209 = 399907) (by norm_num)
theorem B533245 : Blo 471786 533245 := bbase (se 3 (by rfl) ⟨99983, by rfl⟩ : syracuseStep 533245 = 199967) (by norm_num)
theorem B533281 : Blo 471786 533281 := bbase (se 2 (by rfl) ⟨199980, by rfl⟩ : syracuseStep 533281 = 399961) (by norm_num)
theorem B1352501 : Blo 471786 1352501 := bbase (se 5 (by rfl) ⟨63398, by rfl⟩ : syracuseStep 1352501 = 126797) (by norm_num)
theorem B598853 : Blo 471786 598853 := bbase (se 4 (by rfl) ⟨56142, by rfl⟩ : syracuseStep 598853 = 112285) (by norm_num)
theorem B533317 : Blo 471786 533317 := bbase (se 4 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 533317 = 99997) (by norm_num)
theorem B533353 : Blo 471786 533353 := bbase (se 2 (by rfl) ⟨200007, by rfl⟩ : syracuseStep 533353 = 400015) (by norm_num)
theorem B598909 : Blo 471786 598909 := bbase (se 3 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 598909 = 224591) (by norm_num)
theorem B533389 : Blo 471786 533389 := bbase (se 3 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 533389 = 200021) (by norm_num)
theorem B533425 : Blo 471786 533425 := bbase (se 2 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 533425 = 400069) (by norm_num)
theorem B533461 : Blo 471786 533461 := bbase (se 7 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 533461 = 12503) (by norm_num)
theorem B599005 : Blo 471786 599005 := bbase (se 3 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 599005 = 224627) (by norm_num)
theorem B2270197 : Blo 471786 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B533497 : Blo 471786 533497 := bbase (se 2 (by rfl) ⟨200061, by rfl⟩ : syracuseStep 533497 = 400123) (by norm_num)
theorem B533533 : Blo 471786 533533 := bbase (se 3 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 533533 = 200075) (by norm_num)
theorem B533569 : Blo 471786 533569 := bbase (se 2 (by rfl) ⟨200088, by rfl⟩ : syracuseStep 533569 = 400177) (by norm_num)
theorem B533605 : Blo 471786 533605 := bbase (se 4 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 533605 = 100051) (by norm_num)
theorem B599177 : Blo 471786 599177 := bbase (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) (by norm_num)
theorem B533641 : Blo 471786 533641 := bbase (se 2 (by rfl) ⟨200115, by rfl⟩ : syracuseStep 533641 = 400231) (by norm_num)
theorem B533677 : Blo 471786 533677 := bbase (se 3 (by rfl) ⟨100064, by rfl⟩ : syracuseStep 533677 = 200129) (by norm_num)
theorem B599233 : Blo 471786 599233 := bbase (se 2 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 599233 = 449425) (by norm_num)
theorem B533713 : Blo 471786 533713 := bbase (se 2 (by rfl) ⟨200142, by rfl⟩ : syracuseStep 533713 = 400285) (by norm_num)
theorem B9086165 : Blo 471786 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B1352933 : Blo 471786 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B533749 : Blo 471786 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B533785 : Blo 471786 533785 := bbase (se 2 (by rfl) ⟨200169, by rfl⟩ : syracuseStep 533785 = 400339) (by norm_num)
theorem B599329 : Blo 471786 599329 := bbase (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) (by norm_num)
theorem B533821 : Blo 471786 533821 := bbase (se 3 (by rfl) ⟨100091, by rfl⟩ : syracuseStep 533821 = 200183) (by norm_num)
theorem B533857 : Blo 471786 533857 := bbase (se 2 (by rfl) ⟨200196, by rfl⟩ : syracuseStep 533857 = 400393) (by norm_num)
theorem B533893 : Blo 471786 533893 := bbase (se 4 (by rfl) ⟨50052, by rfl⟩ : syracuseStep 533893 = 100105) (by norm_num)
theorem B533929 : Blo 471786 533929 := bbase (se 2 (by rfl) ⟨200223, by rfl⟩ : syracuseStep 533929 = 400447) (by norm_num)
theorem B599501 : Blo 471786 599501 := bbase (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) (by norm_num)
theorem B533965 : Blo 471786 533965 := bbase (se 3 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 533965 = 200237) (by norm_num)
theorem B534001 : Blo 471786 534001 := bbase (se 2 (by rfl) ⟨200250, by rfl⟩ : syracuseStep 534001 = 400501) (by norm_num)
theorem B599557 : Blo 471786 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B534037 : Blo 471786 534037 := bbase (se 6 (by rfl) ⟨12516, by rfl⟩ : syracuseStep 534037 = 25033) (by norm_num)
theorem B5416469 : Blo 471786 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B796189 : Blo 471786 796189 := bbase (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) (by norm_num)
theorem B534073 : Blo 471786 534073 := bbase (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) (by norm_num)
theorem B534109 : Blo 471786 534109 := bbase (se 3 (by rfl) ⟨100145, by rfl⟩ : syracuseStep 534109 = 200291) (by norm_num)
theorem B599653 : Blo 471786 599653 := bbase (se 4 (by rfl) ⟨56217, by rfl⟩ : syracuseStep 599653 = 112435) (by norm_num)
theorem B796277 : Blo 471786 796277 := bbase (se 5 (by rfl) ⟨37325, by rfl⟩ : syracuseStep 796277 = 74651) (by norm_num)
theorem B534145 : Blo 471786 534145 := bbase (se 2 (by rfl) ⟨200304, by rfl⟩ : syracuseStep 534145 = 400609) (by norm_num)
theorem B534181 : Blo 471786 534181 := bbase (se 4 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 534181 = 100159) (by norm_num)
theorem B2401973 : Blo 471786 2401973 := bbase (se 5 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 2401973 = 225185) (by norm_num)
theorem B534217 : Blo 471786 534217 := bbase (se 2 (by rfl) ⟨200331, by rfl⟩ : syracuseStep 534217 = 400663) (by norm_num)
theorem B534253 : Blo 471786 534253 := bbase (se 3 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 534253 = 200345) (by norm_num)
theorem B796405 : Blo 471786 796405 := bbase (se 5 (by rfl) ⟨37331, by rfl⟩ : syracuseStep 796405 = 74663) (by norm_num)
theorem B861949 : Blo 471786 861949 := bbase (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) (by norm_num)
theorem B599825 : Blo 471786 599825 := bbase (se 2 (by rfl) ⟨224934, by rfl⟩ : syracuseStep 599825 = 449869) (by norm_num)
theorem B534289 : Blo 471786 534289 := bbase (se 2 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 534289 = 400717) (by norm_num)
theorem B534325 : Blo 471786 534325 := bbase (se 5 (by rfl) ⟨25046, by rfl⟩ : syracuseStep 534325 = 50093) (by norm_num)
theorem B599881 : Blo 471786 599881 := bbase (se 2 (by rfl) ⟨224955, by rfl⟩ : syracuseStep 599881 = 449911) (by norm_num)
theorem B796493 : Blo 471786 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B534361 : Blo 471786 534361 := bbase (se 2 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 534361 = 400771) (by norm_num)
theorem B534397 : Blo 471786 534397 := bbase (se 3 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 534397 = 200399) (by norm_num)
theorem B534433 : Blo 471786 534433 := bbase (se 2 (by rfl) ⟨200412, by rfl⟩ : syracuseStep 534433 = 400825) (by norm_num)
theorem B599977 : Blo 471786 599977 := bbase (se 2 (by rfl) ⟨224991, by rfl⟩ : syracuseStep 599977 = 449983) (by norm_num)
theorem B534469 : Blo 471786 534469 := bbase (se 4 (by rfl) ⟨50106, by rfl⟩ : syracuseStep 534469 = 100213) (by norm_num)
theorem B796621 : Blo 471786 796621 := bbase (se 3 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 796621 = 298733) (by norm_num)
theorem B862165 : Blo 471786 862165 := bbase (se 7 (by rfl) ⟨10103, by rfl⟩ : syracuseStep 862165 = 20207) (by norm_num)
theorem B1353685 : Blo 471786 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B534505 : Blo 471786 534505 := bbase (se 2 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 534505 = 400879) (by norm_num)
theorem B534541 : Blo 471786 534541 := bbase (se 3 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 534541 = 200453) (by norm_num)
theorem B796709 : Blo 471786 796709 := bbase (se 4 (by rfl) ⟨74691, by rfl⟩ : syracuseStep 796709 = 149383) (by norm_num)
theorem B534577 : Blo 471786 534577 := bbase (se 2 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 534577 = 400933) (by norm_num)
theorem B600149 : Blo 471786 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B534613 : Blo 471786 534613 := bbase (se 8 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 534613 = 6265) (by norm_num)
theorem B534649 : Blo 471786 534649 := bbase (se 2 (by rfl) ⟨200493, by rfl⟩ : syracuseStep 534649 = 400987) (by norm_num)
theorem B600205 : Blo 471786 600205 := bbase (se 3 (by rfl) ⟨112538, by rfl⟩ : syracuseStep 600205 = 225077) (by norm_num)
theorem B534685 : Blo 471786 534685 := bbase (se 3 (by rfl) ⟨100253, by rfl⟩ : syracuseStep 534685 = 200507) (by norm_num)
theorem B796837 : Blo 471786 796837 := bbase (se 4 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 796837 = 149407) (by norm_num)
theorem B534721 : Blo 471786 534721 := bbase (se 2 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 534721 = 401041) (by norm_num)
theorem B534757 : Blo 471786 534757 := bbase (se 4 (by rfl) ⟨50133, by rfl⟩ : syracuseStep 534757 = 100267) (by norm_num)
theorem B600301 : Blo 471786 600301 := bbase (se 3 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 600301 = 225113) (by norm_num)
theorem B2697461 : Blo 471786 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B796925 : Blo 471786 796925 := bbase (se 3 (by rfl) ⟨149423, by rfl⟩ : syracuseStep 796925 = 298847) (by norm_num)
theorem B534793 : Blo 471786 534793 := bbase (se 2 (by rfl) ⟨200547, by rfl⟩ : syracuseStep 534793 = 401095) (by norm_num)
theorem B534829 : Blo 471786 534829 := bbase (se 3 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 534829 = 200561) (by norm_num)
theorem B534865 : Blo 471786 534865 := bbase (se 2 (by rfl) ⟨200574, by rfl⟩ : syracuseStep 534865 = 401149) (by norm_num)
theorem B1845605 : Blo 471786 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B534901 : Blo 471786 534901 := bbase (se 5 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 534901 = 50147) (by norm_num)
theorem B797053 : Blo 471786 797053 := bbase (se 3 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 797053 = 298895) (by norm_num)
theorem B600473 : Blo 471786 600473 := bbase (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) (by norm_num)
theorem B534937 : Blo 471786 534937 := bbase (se 2 (by rfl) ⟨200601, by rfl⟩ : syracuseStep 534937 = 401203) (by norm_num)
theorem B534973 : Blo 471786 534973 := bbase (se 3 (by rfl) ⟨100307, by rfl⟩ : syracuseStep 534973 = 200615) (by norm_num)
theorem B600529 : Blo 471786 600529 := bbase (se 2 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 600529 = 450397) (by norm_num)
theorem B797141 : Blo 471786 797141 := bbase (se 7 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 797141 = 18683) (by norm_num)
theorem B535009 : Blo 471786 535009 := bbase (se 2 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 535009 = 401257) (by norm_num)
theorem B535045 : Blo 471786 535045 := bbase (se 4 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 535045 = 100321) (by norm_num)
theorem B535081 : Blo 471786 535081 := bbase (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) (by norm_num)
theorem B731693 : Blo 471786 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B567857 : Blo 471786 567857 := bbase (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) (by norm_num)
theorem B600625 : Blo 471786 600625 := bbase (se 2 (by rfl) ⟨225234, by rfl⟩ : syracuseStep 600625 = 450469) (by norm_num)
theorem B535117 : Blo 471786 535117 := bbase (se 3 (by rfl) ⟨100334, by rfl⟩ : syracuseStep 535117 = 200669) (by norm_num)
theorem B797269 : Blo 471786 797269 := bbase (se 8 (by rfl) ⟨4671, by rfl⟩ : syracuseStep 797269 = 9343) (by norm_num)
theorem B535153 : Blo 471786 535153 := bbase (se 2 (by rfl) ⟨200682, by rfl⟩ : syracuseStep 535153 = 401365) (by norm_num)
theorem B535189 : Blo 471786 535189 := bbase (se 6 (by rfl) ⟨12543, by rfl⟩ : syracuseStep 535189 = 25087) (by norm_num)
theorem B797357 : Blo 471786 797357 := bbase (se 3 (by rfl) ⟨149504, by rfl⟩ : syracuseStep 797357 = 299009) (by norm_num)
theorem B535225 : Blo 471786 535225 := bbase (se 2 (by rfl) ⟨200709, by rfl⟩ : syracuseStep 535225 = 401419) (by norm_num)
theorem B600797 : Blo 471786 600797 := bbase (se 3 (by rfl) ⟨112649, by rfl⟩ : syracuseStep 600797 = 225299) (by norm_num)
theorem B600853 : Blo 471786 600853 := bbase (se 6 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 600853 = 28165) (by norm_num)
theorem B895789 : Blo 471786 895789 := bbase (se 3 (by rfl) ⟨167960, by rfl⟩ : syracuseStep 895789 = 335921) (by norm_num)
theorem B797485 : Blo 471786 797485 := bbase (se 3 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 797485 = 299057) (by norm_num)
theorem B961373 : Blo 471786 961373 := bbase (se 3 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 961373 = 360515) (by norm_num)
theorem B600949 : Blo 471786 600949 := bbase (se 5 (by rfl) ⟨28169, by rfl⟩ : syracuseStep 600949 = 56339) (by norm_num)
theorem B568193 : Blo 471786 568193 := bbase (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) (by norm_num)
theorem B797573 : Blo 471786 797573 := bbase (se 4 (by rfl) ⟨74772, by rfl⟩ : syracuseStep 797573 = 149545) (by norm_num)
theorem B1092509 : Blo 471786 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B2403269 : Blo 471786 2403269 := bbase (se 4 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 2403269 = 450613) (by norm_num)
theorem B568309 : Blo 471786 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B797701 : Blo 471786 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B1027093 : Blo 471786 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B601121 : Blo 471786 601121 := bbase (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) (by norm_num)
theorem B568381 : Blo 471786 568381 := bbase (se 3 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 568381 = 213143) (by norm_num)
theorem B568405 : Blo 471786 568405 := bbase (se 8 (by rfl) ⟨3330, by rfl⟩ : syracuseStep 568405 = 6661) (by norm_num)
theorem B601177 : Blo 471786 601177 := bbase (se 2 (by rfl) ⟨225441, by rfl⟩ : syracuseStep 601177 = 450883) (by norm_num)
theorem B896093 : Blo 471786 896093 := bbase (se 3 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 896093 = 336035) (by norm_num)
theorem B797789 : Blo 471786 797789 := bbase (se 3 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 797789 = 299171) (by norm_num)
theorem B601273 : Blo 471786 601273 := bbase (se 2 (by rfl) ⟨225477, by rfl⟩ : syracuseStep 601273 = 450955) (by norm_num)
theorem B797917 : Blo 471786 797917 := bbase (se 3 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 797917 = 299219) (by norm_num)
theorem B568549 : Blo 471786 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B1518821 : Blo 471786 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B798005 : Blo 471786 798005 := bbase (se 5 (by rfl) ⟨37406, by rfl⟩ : syracuseStep 798005 = 74813) (by norm_num)
theorem B3026261 : Blo 471786 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B601445 : Blo 471786 601445 := bbase (se 4 (by rfl) ⟨56385, by rfl⟩ : syracuseStep 601445 = 112771) (by norm_num)
theorem B601501 : Blo 471786 601501 := bbase (se 3 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 601501 = 225563) (by norm_num)
theorem B798133 : Blo 471786 798133 := bbase (se 5 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 798133 = 74825) (by norm_num)
theorem B962005 : Blo 471786 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B601597 : Blo 471786 601597 := bbase (se 3 (by rfl) ⟨112799, by rfl⟩ : syracuseStep 601597 = 225599) (by norm_num)
theorem B798221 : Blo 471786 798221 := bbase (se 3 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 798221 = 299333) (by norm_num)
theorem B831061 : Blo 471786 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B798349 : Blo 471786 798349 := bbase (se 3 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 798349 = 299381) (by norm_num)
theorem B601769 : Blo 471786 601769 := bbase (se 2 (by rfl) ⟨225663, by rfl⟩ : syracuseStep 601769 = 451327) (by norm_num)
theorem B601825 : Blo 471786 601825 := bbase (se 2 (by rfl) ⟨225684, by rfl⟩ : syracuseStep 601825 = 451369) (by norm_num)
theorem B798437 : Blo 471786 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B1945397 : Blo 471786 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B601921 : Blo 471786 601921 := bbase (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) (by norm_num)
theorem B896845 : Blo 471786 896845 := bbase (se 3 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 896845 = 336317) (by norm_num)
theorem B798565 : Blo 471786 798565 := bbase (se 4 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 798565 = 149731) (by norm_num)
theorem B1027957 : Blo 471786 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B798653 : Blo 471786 798653 := bbase (se 3 (by rfl) ⟨149747, by rfl⟩ : syracuseStep 798653 = 299495) (by norm_num)
theorem B896989 : Blo 471786 896989 := bbase (se 3 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 896989 = 336371) (by norm_num)
theorem B602093 : Blo 471786 602093 := bbase (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) (by norm_num)
theorem B602149 : Blo 471786 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B798781 : Blo 471786 798781 := bbase (se 3 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 798781 = 299543) (by norm_num)
theorem B503929 : Blo 471786 503929 := bbase (se 2 (by rfl) ⟨188973, by rfl⟩ : syracuseStep 503929 = 377947) (by norm_num)
theorem B897149 : Blo 471786 897149 := bbase (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) (by norm_num)
theorem B798869 : Blo 471786 798869 := bbase (se 6 (by rfl) ⟨18723, by rfl⟩ : syracuseStep 798869 = 37447) (by norm_num)
theorem B504001 : Blo 471786 504001 := bbase (se 2 (by rfl) ⟨189000, by rfl⟩ : syracuseStep 504001 = 378001) (by norm_num)
theorem B2404565 : Blo 471786 2404565 := bbase (se 7 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 2404565 = 56357) (by norm_num)
theorem B897293 : Blo 471786 897293 := bbase (se 3 (by rfl) ⟨168242, by rfl⟩ : syracuseStep 897293 = 336485) (by norm_num)
theorem B798997 : Blo 471786 798997 := bbase (se 6 (by rfl) ⟨18726, by rfl⟩ : syracuseStep 798997 = 37453) (by norm_num)
theorem B799085 : Blo 471786 799085 := bbase (se 3 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 799085 = 299657) (by norm_num)
theorem B504181 : Blo 471786 504181 := bbase (se 5 (by rfl) ⟨23633, by rfl⟩ : syracuseStep 504181 = 47267) (by norm_num)
theorem B2699669 : Blo 471786 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B569765 : Blo 471786 569765 := bbase (se 4 (by rfl) ⟨53415, by rfl⟩ : syracuseStep 569765 = 106831) (by norm_num)
theorem B799213 : Blo 471786 799213 := bbase (se 3 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 799213 = 299705) (by norm_num)
theorem B897581 : Blo 471786 897581 := bbase (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) (by norm_num)
theorem B799301 : Blo 471786 799301 := bbase (se 4 (by rfl) ⟨74934, by rfl⟩ : syracuseStep 799301 = 149869) (by norm_num)
theorem B1061549 : Blo 471786 1061549 := bbase (se 3 (by rfl) ⟨199040, by rfl⟩ : syracuseStep 1061549 = 398081) (by norm_num)
theorem B897733 : Blo 471786 897733 := bbase (se 4 (by rfl) ⟨84162, by rfl⟩ : syracuseStep 897733 = 168325) (by norm_num)
theorem B799429 : Blo 471786 799429 := bbase (se 4 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 799429 = 149893) (by norm_num)
theorem B570073 : Blo 471786 570073 := bbase (se 2 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 570073 = 427555) (by norm_num)
theorem B1061621 : Blo 471786 1061621 := bbase (se 5 (by rfl) ⟨49763, by rfl⟩ : syracuseStep 1061621 = 99527) (by norm_num)
theorem B799517 : Blo 471786 799517 := bbase (se 3 (by rfl) ⟨149909, by rfl⟩ : syracuseStep 799517 = 299819) (by norm_num)
theorem B504625 : Blo 471786 504625 := bbase (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) (by norm_num)
theorem B1061693 : Blo 471786 1061693 := bbase (se 3 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 1061693 = 398135) (by norm_num)
theorem B570173 : Blo 471786 570173 := bbase (se 3 (by rfl) ⟨106907, by rfl⟩ : syracuseStep 570173 = 213815) (by norm_num)
theorem B1061765 : Blo 471786 1061765 := bbase (se 4 (by rfl) ⟨99540, by rfl⟩ : syracuseStep 1061765 = 199081) (by norm_num)
theorem B799645 : Blo 471786 799645 := bbase (se 3 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 799645 = 299867) (by norm_num)
theorem B504749 : Blo 471786 504749 := bbase (se 3 (by rfl) ⟨94640, by rfl⟩ : syracuseStep 504749 = 189281) (by norm_num)
theorem B1061837 : Blo 471786 1061837 := bbase (se 3 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 1061837 = 398189) (by norm_num)
theorem B898037 : Blo 471786 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B799733 : Blo 471786 799733 := bbase (se 5 (by rfl) ⟨37487, by rfl⟩ : syracuseStep 799733 = 74975) (by norm_num)
theorem B1061909 : Blo 471786 1061909 := bbase (se 6 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 1061909 = 49777) (by norm_num)
theorem B2274389 : Blo 471786 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B1061981 : Blo 471786 1061981 := bbase (se 3 (by rfl) ⟨199121, by rfl⟩ : syracuseStep 1061981 = 398243) (by norm_num)
theorem B799861 : Blo 471786 799861 := bbase (se 5 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 799861 = 74987) (by norm_num)
theorem B1062053 : Blo 471786 1062053 := bbase (se 4 (by rfl) ⟨99567, by rfl⟩ : syracuseStep 1062053 = 199135) (by norm_num)
theorem B505001 : Blo 471786 505001 := bbase (se 2 (by rfl) ⟨189375, by rfl⟩ : syracuseStep 505001 = 378751) (by norm_num)
theorem B799949 : Blo 471786 799949 := bbase (se 3 (by rfl) ⟨149990, by rfl⟩ : syracuseStep 799949 = 299981) (by norm_num)
theorem B570577 : Blo 471786 570577 := bbase (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) (by norm_num)
theorem B1062125 : Blo 471786 1062125 := bbase (se 3 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 1062125 = 398297) (by norm_num)
theorem B1914149 : Blo 471786 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1062197 : Blo 471786 1062197 := bbase (se 5 (by rfl) ⟨49790, by rfl⟩ : syracuseStep 1062197 = 99581) (by norm_num)
theorem B800077 : Blo 471786 800077 := bbase (se 3 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 800077 = 300029) (by norm_num)
theorem B1521013 : Blo 471786 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B1062269 : Blo 471786 1062269 := bbase (se 3 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 1062269 = 398351) (by norm_num)
theorem B800165 : Blo 471786 800165 := bbase (se 4 (by rfl) ⟨75015, by rfl⟩ : syracuseStep 800165 = 150031) (by norm_num)
theorem B1062341 : Blo 471786 1062341 := bbase (se 4 (by rfl) ⟨99594, by rfl⟩ : syracuseStep 1062341 = 199189) (by norm_num)
theorem B2405861 : Blo 471786 2405861 := bbase (se 4 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 2405861 = 451099) (by norm_num)
theorem B1062413 : Blo 471786 1062413 := bbase (se 3 (by rfl) ⟨199202, by rfl⟩ : syracuseStep 1062413 = 398405) (by norm_num)
theorem B800293 : Blo 471786 800293 := bbase (se 4 (by rfl) ⟨75027, by rfl⟩ : syracuseStep 800293 = 150055) (by norm_num)
theorem B570961 : Blo 471786 570961 := bbase (se 2 (by rfl) ⟨214110, by rfl⟩ : syracuseStep 570961 = 428221) (by norm_num)
theorem B1062485 : Blo 471786 1062485 := bbase (se 8 (by rfl) ⟨6225, by rfl⟩ : syracuseStep 1062485 = 12451) (by norm_num)
theorem B505445 : Blo 471786 505445 := bbase (se 4 (by rfl) ⟨47385, by rfl⟩ : syracuseStep 505445 = 94771) (by norm_num)
theorem B800381 : Blo 471786 800381 := bbase (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) (by norm_num)
theorem B1062557 : Blo 471786 1062557 := bbase (se 3 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 1062557 = 398459) (by norm_num)
theorem B1062629 : Blo 471786 1062629 := bbase (se 4 (by rfl) ⟨99621, by rfl⟩ : syracuseStep 1062629 = 199243) (by norm_num)
theorem B898789 : Blo 471786 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B800509 : Blo 471786 800509 := bbase (se 3 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 800509 = 300191) (by norm_num)
theorem B1062701 : Blo 471786 1062701 := bbase (se 3 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 1062701 = 398513) (by norm_num)
theorem B4568885 : Blo 471786 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B800597 : Blo 471786 800597 := bbase (se 9 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 800597 = 4691) (by norm_num)
theorem B505693 : Blo 471786 505693 := bbase (se 3 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 505693 = 189635) (by norm_num)
theorem B1062773 : Blo 471786 1062773 := bbase (se 5 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 1062773 = 99635) (by norm_num)
theorem B898933 : Blo 471786 898933 := bbase (se 5 (by rfl) ⟨42137, by rfl⟩ : syracuseStep 898933 = 84275) (by norm_num)
theorem B538501 : Blo 471786 538501 := bbase (se 4 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 538501 = 100969) (by norm_num)
theorem B1062845 : Blo 471786 1062845 := bbase (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) (by norm_num)
theorem B800725 : Blo 471786 800725 := bbase (se 7 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 800725 = 18767) (by norm_num)
theorem B1062917 : Blo 471786 1062917 := bbase (se 4 (by rfl) ⟨99648, by rfl⟩ : syracuseStep 1062917 = 199297) (by norm_num)
theorem B1619989 : Blo 471786 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B899093 : Blo 471786 899093 := bbase (se 6 (by rfl) ⟨21072, by rfl⟩ : syracuseStep 899093 = 42145) (by norm_num)
theorem B800813 : Blo 471786 800813 := bbase (se 3 (by rfl) ⟨150152, by rfl⟩ : syracuseStep 800813 = 300305) (by norm_num)
theorem B1062989 : Blo 471786 1062989 := bbase (se 3 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 1062989 = 398621) (by norm_num)
theorem B1620101 : Blo 471786 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B1063061 : Blo 471786 1063061 := bbase (se 6 (by rfl) ⟨24915, by rfl⟩ : syracuseStep 1063061 = 49831) (by norm_num)
theorem B899237 : Blo 471786 899237 := bbase (se 4 (by rfl) ⟨84303, by rfl⟩ : syracuseStep 899237 = 168607) (by norm_num)
theorem B800941 : Blo 471786 800941 := bbase (se 3 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 800941 = 300353) (by norm_num)
theorem B1521845 : Blo 471786 1521845 := bbase (se 5 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 1521845 = 142673) (by norm_num)
theorem B1063133 : Blo 471786 1063133 := bbase (se 3 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 1063133 = 398675) (by norm_num)
theorem B3029237 : Blo 471786 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B801029 : Blo 471786 801029 := bbase (se 4 (by rfl) ⟨75096, by rfl⟩ : syracuseStep 801029 = 150193) (by norm_num)
theorem B506137 : Blo 471786 506137 := bbase (se 2 (by rfl) ⟨189801, by rfl⟩ : syracuseStep 506137 = 379603) (by norm_num)
theorem B1063205 : Blo 471786 1063205 := bbase (se 4 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 1063205 = 199351) (by norm_num)
theorem B538957 : Blo 471786 538957 := bbase (se 3 (by rfl) ⟨101054, by rfl⟩ : syracuseStep 538957 = 202109) (by norm_num)
theorem B506197 : Blo 471786 506197 := bbase (se 10 (by rfl) ⟨741, by rfl⟩ : syracuseStep 506197 = 1483) (by norm_num)
theorem B1063277 : Blo 471786 1063277 := bbase (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) (by norm_num)
theorem B1194365 : Blo 471786 1194365 := bbase (se 3 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 1194365 = 447887) (by norm_num)
theorem B801157 : Blo 471786 801157 := bbase (se 4 (by rfl) ⟨75108, by rfl⟩ : syracuseStep 801157 = 150217) (by norm_num)
theorem B1063349 : Blo 471786 1063349 := bbase (se 5 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 1063349 = 99689) (by norm_num)
theorem B899525 : Blo 471786 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B801245 : Blo 471786 801245 := bbase (se 3 (by rfl) ⟨150233, by rfl⟩ : syracuseStep 801245 = 300467) (by norm_num)
theorem B1063421 : Blo 471786 1063421 := bbase (se 3 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 1063421 = 398783) (by norm_num)
theorem B1063493 : Blo 471786 1063493 := bbase (se 4 (by rfl) ⟨99702, by rfl⟩ : syracuseStep 1063493 = 199405) (by norm_num)
theorem B899677 : Blo 471786 899677 := bbase (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) (by norm_num)
theorem B801373 : Blo 471786 801373 := bbase (se 3 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 801373 = 300515) (by norm_num)
theorem B1063565 : Blo 471786 1063565 := bbase (se 3 (by rfl) ⟨199418, by rfl⟩ : syracuseStep 1063565 = 398837) (by norm_num)
theorem B506513 : Blo 471786 506513 := bbase (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) (by norm_num)
theorem B801461 : Blo 471786 801461 := bbase (se 5 (by rfl) ⟨37568, by rfl⟩ : syracuseStep 801461 = 75137) (by norm_num)
theorem B1194709 : Blo 471786 1194709 := bbase (se 7 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 1194709 = 28001) (by norm_num)
theorem B1063637 : Blo 471786 1063637 := bbase (se 7 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 1063637 = 24929) (by norm_num)
theorem B2407157 : Blo 471786 2407157 := bbase (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) (by norm_num)
theorem B1063709 : Blo 471786 1063709 := bbase (se 3 (by rfl) ⟨199445, by rfl⟩ : syracuseStep 1063709 = 398891) (by norm_num)
theorem B801589 : Blo 471786 801589 := bbase (se 5 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 801589 = 75149) (by norm_num)
theorem B1194821 : Blo 471786 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B1063781 : Blo 471786 1063781 := bbase (se 4 (by rfl) ⟨99729, by rfl⟩ : syracuseStep 1063781 = 199459) (by norm_num)
theorem B4537205 : Blo 471786 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B899981 : Blo 471786 899981 := bbase (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) (by norm_num)
theorem B801677 : Blo 471786 801677 := bbase (se 3 (by rfl) ⟨150314, by rfl⟩ : syracuseStep 801677 = 300629) (by norm_num)
theorem B1063853 : Blo 471786 1063853 := bbase (se 3 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 1063853 = 398945) (by norm_num)
theorem B1063925 : Blo 471786 1063925 := bbase (se 5 (by rfl) ⟨49871, by rfl⟩ : syracuseStep 1063925 = 99743) (by norm_num)
theorem B1195013 : Blo 471786 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B801805 : Blo 471786 801805 := bbase (se 3 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 801805 = 300677) (by norm_num)
theorem B1063997 : Blo 471786 1063997 := bbase (se 3 (by rfl) ⟨199499, by rfl⟩ : syracuseStep 1063997 = 398999) (by norm_num)
theorem B506957 : Blo 471786 506957 := bbase (se 3 (by rfl) ⟨95054, by rfl⟩ : syracuseStep 506957 = 190109) (by norm_num)
theorem B801893 : Blo 471786 801893 := bbase (se 4 (by rfl) ⟨75177, by rfl⟩ : syracuseStep 801893 = 150355) (by norm_num)
theorem B1064069 : Blo 471786 1064069 := bbase (se 4 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 1064069 = 199513) (by norm_num)
theorem B507017 : Blo 471786 507017 := bbase (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) (by norm_num)
theorem B1064141 : Blo 471786 1064141 := bbase (se 3 (by rfl) ⟨199526, by rfl⟩ : syracuseStep 1064141 = 399053) (by norm_num)
theorem B802021 : Blo 471786 802021 := bbase (se 4 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 802021 = 150379) (by norm_num)
theorem B507145 : Blo 471786 507145 := bbase (se 2 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 507145 = 380359) (by norm_num)
theorem B1064213 : Blo 471786 1064213 := bbase (se 6 (by rfl) ⟨24942, by rfl⟩ : syracuseStep 1064213 = 49885) (by norm_num)
theorem B802109 : Blo 471786 802109 := bbase (se 3 (by rfl) ⟨150395, by rfl⟩ : syracuseStep 802109 = 300791) (by norm_num)
theorem B11124053 : Blo 471786 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B1195357 : Blo 471786 1195357 := bbase (se 3 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 1195357 = 448259) (by norm_num)
theorem B1064285 : Blo 471786 1064285 := bbase (se 3 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 1064285 = 399107) (by norm_num)
theorem B769429 : Blo 471786 769429 := bbase (se 6 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 769429 = 36067) (by norm_num)
theorem B1064357 : Blo 471786 1064357 := bbase (se 4 (by rfl) ⟨99783, by rfl⟩ : syracuseStep 1064357 = 199567) (by norm_num)
theorem B802237 : Blo 471786 802237 := bbase (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) (by norm_num)
theorem B1195469 : Blo 471786 1195469 := bbase (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) (by norm_num)
theorem B1064429 : Blo 471786 1064429 := bbase (se 3 (by rfl) ⟨199580, by rfl⟩ : syracuseStep 1064429 = 399161) (by norm_num)
theorem B802325 : Blo 471786 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B1064501 : Blo 471786 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B1064573 : Blo 471786 1064573 := bbase (se 3 (by rfl) ⟨199607, by rfl⟩ : syracuseStep 1064573 = 399215) (by norm_num)
theorem B900733 : Blo 471786 900733 := bbase (se 3 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 900733 = 337775) (by norm_num)
theorem B1195661 : Blo 471786 1195661 := bbase (se 3 (by rfl) ⟨224186, by rfl⟩ : syracuseStep 1195661 = 448373) (by norm_num)
theorem B802453 : Blo 471786 802453 := bbase (se 6 (by rfl) ⟨18807, by rfl⟩ : syracuseStep 802453 = 37615) (by norm_num)
theorem B1064645 : Blo 471786 1064645 := bbase (se 4 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 1064645 = 199621) (by norm_num)
theorem B507589 : Blo 471786 507589 := bbase (se 4 (by rfl) ⟨47586, by rfl⟩ : syracuseStep 507589 = 95173) (by norm_num)
theorem B2277077 : Blo 471786 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B802541 : Blo 471786 802541 := bbase (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) (by norm_num)
theorem B1064717 : Blo 471786 1064717 := bbase (se 3 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 1064717 = 399269) (by norm_num)
theorem B900877 : Blo 471786 900877 := bbase (se 3 (by rfl) ⟨168914, by rfl⟩ : syracuseStep 900877 = 337829) (by norm_num)
theorem B507709 : Blo 471786 507709 := bbase (se 3 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 507709 = 190391) (by norm_num)
theorem B1064789 : Blo 471786 1064789 := bbase (se 9 (by rfl) ⟨3119, by rfl⟩ : syracuseStep 1064789 = 6239) (by norm_num)
theorem B802669 : Blo 471786 802669 := bbase (se 3 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 802669 = 301001) (by norm_num)
theorem B1064861 : Blo 471786 1064861 := bbase (se 3 (by rfl) ⟨199661, by rfl⟩ : syracuseStep 1064861 = 399323) (by norm_num)
theorem B901037 : Blo 471786 901037 := bbase (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) (by norm_num)
theorem B802757 : Blo 471786 802757 := bbase (se 4 (by rfl) ⟨75258, by rfl⟩ : syracuseStep 802757 = 150517) (by norm_num)
theorem B1196005 : Blo 471786 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B1064933 : Blo 471786 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B1523717 : Blo 471786 1523717 := bbase (se 4 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 1523717 = 285697) (by norm_num)
theorem B2408453 : Blo 471786 2408453 := bbase (se 4 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 2408453 = 451585) (by norm_num)
theorem B1065005 : Blo 471786 1065005 := bbase (se 3 (by rfl) ⟨199688, by rfl⟩ : syracuseStep 1065005 = 399377) (by norm_num)
theorem B507961 : Blo 471786 507961 := bbase (se 2 (by rfl) ⟨190485, by rfl⟩ : syracuseStep 507961 = 380971) (by norm_num)
theorem B901181 : Blo 471786 901181 := bbase (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) (by norm_num)
theorem B507965 : Blo 471786 507965 := bbase (se 3 (by rfl) ⟨95243, by rfl⟩ : syracuseStep 507965 = 190487) (by norm_num)
theorem B802885 : Blo 471786 802885 := bbase (se 4 (by rfl) ⟨75270, by rfl⟩ : syracuseStep 802885 = 150541) (by norm_num)
theorem B1196117 : Blo 471786 1196117 := bbase (se 8 (by rfl) ⟨7008, by rfl⟩ : syracuseStep 1196117 = 14017) (by norm_num)
theorem B1065077 : Blo 471786 1065077 := bbase (se 5 (by rfl) ⟨49925, by rfl⟩ : syracuseStep 1065077 = 99851) (by norm_num)
theorem B671933 : Blo 471786 671933 := bbase (se 3 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 671933 = 251975) (by norm_num)
theorem B1065149 : Blo 471786 1065149 := bbase (se 3 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 1065149 = 399431) (by norm_num)
theorem B8536277 : Blo 471786 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B1065221 : Blo 471786 1065221 := bbase (se 4 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 1065221 = 199729) (by norm_num)
theorem B672013 : Blo 471786 672013 := bbase (se 3 (by rfl) ⟨126002, by rfl⟩ : syracuseStep 672013 = 252005) (by norm_num)
theorem B1196309 : Blo 471786 1196309 := bbase (se 6 (by rfl) ⟨28038, by rfl⟩ : syracuseStep 1196309 = 56077) (by norm_num)
theorem B1065293 : Blo 471786 1065293 := bbase (se 3 (by rfl) ⟨199742, by rfl⟩ : syracuseStep 1065293 = 399485) (by norm_num)
theorem B901469 : Blo 471786 901469 := bbase (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) (by norm_num)
theorem B672133 : Blo 471786 672133 := bbase (se 4 (by rfl) ⟨63012, by rfl⟩ : syracuseStep 672133 = 126025) (by norm_num)
theorem B1065365 : Blo 471786 1065365 := bbase (se 6 (by rfl) ⟨24969, by rfl⟩ : syracuseStep 1065365 = 49939) (by norm_num)
theorem B4047317 : Blo 471786 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B1065437 : Blo 471786 1065437 := bbase (se 3 (by rfl) ⟨199769, by rfl⟩ : syracuseStep 1065437 = 399539) (by norm_num)
theorem B672229 : Blo 471786 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B901621 : Blo 471786 901621 := bbase (se 5 (by rfl) ⟨42263, by rfl⟩ : syracuseStep 901621 = 84527) (by norm_num)
theorem B6242837 : Blo 471786 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1065509 : Blo 471786 1065509 := bbase (se 4 (by rfl) ⟨99891, by rfl⟩ : syracuseStep 1065509 = 199783) (by norm_num)
theorem B770629 : Blo 471786 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B1196653 : Blo 471786 1196653 := bbase (se 3 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 1196653 = 448745) (by norm_num)
theorem B1065581 : Blo 471786 1065581 := bbase (se 3 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 1065581 = 399593) (by norm_num)
theorem B1917589 : Blo 471786 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B1065653 : Blo 471786 1065653 := bbase (se 5 (by rfl) ⟨49952, by rfl⟩ : syracuseStep 1065653 = 99905) (by norm_num)
theorem B1196765 : Blo 471786 1196765 := bbase (se 3 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 1196765 = 448787) (by norm_num)
theorem B1065725 : Blo 471786 1065725 := bbase (se 3 (by rfl) ⟨199823, by rfl⟩ : syracuseStep 1065725 = 399647) (by norm_num)
theorem B901925 : Blo 471786 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B1065797 : Blo 471786 1065797 := bbase (se 4 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 1065797 = 199837) (by norm_num)
theorem B1065869 : Blo 471786 1065869 := bbase (se 3 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 1065869 = 399701) (by norm_num)
theorem B1196957 : Blo 471786 1196957 := bbase (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) (by norm_num)
theorem B672725 : Blo 471786 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B1065941 : Blo 471786 1065941 := bbase (se 7 (by rfl) ⟨12491, by rfl⟩ : syracuseStep 1065941 = 24983) (by norm_num)
theorem B3589109 : Blo 471786 3589109 := bbase (se 5 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 3589109 = 336479) (by norm_num)
theorem B1066013 : Blo 471786 1066013 := bbase (se 3 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 1066013 = 399755) (by norm_num)
theorem B607333 : Blo 471786 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B1066085 : Blo 471786 1066085 := bbase (se 4 (by rfl) ⟨99945, by rfl⟩ : syracuseStep 1066085 = 199891) (by norm_num)
theorem B1066157 : Blo 471786 1066157 := bbase (se 3 (by rfl) ⟨199904, by rfl⟩ : syracuseStep 1066157 = 399809) (by norm_num)
theorem B2802869 : Blo 471786 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1197301 : Blo 471786 1197301 := bbase (se 5 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 1197301 = 112247) (by norm_num)
theorem B1066229 : Blo 471786 1066229 := bbase (se 5 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 1066229 = 99959) (by norm_num)
theorem B1066301 : Blo 471786 1066301 := bbase (se 3 (by rfl) ⟨199931, by rfl⟩ : syracuseStep 1066301 = 399863) (by norm_num)
theorem B1197413 : Blo 471786 1197413 := bbase (se 4 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 1197413 = 224515) (by norm_num)
theorem B1066373 : Blo 471786 1066373 := bbase (se 4 (by rfl) ⟨99972, by rfl⟩ : syracuseStep 1066373 = 199945) (by norm_num)
theorem B1623493 : Blo 471786 1623493 := bbase (se 4 (by rfl) ⟨152202, by rfl⟩ : syracuseStep 1623493 = 304405) (by norm_num)
theorem B1066445 : Blo 471786 1066445 := bbase (se 3 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 1066445 = 399917) (by norm_num)
theorem B673277 : Blo 471786 673277 := bbase (se 3 (by rfl) ⟨126239, by rfl⟩ : syracuseStep 673277 = 252479) (by norm_num)
theorem B1066517 : Blo 471786 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B902677 : Blo 471786 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B1197605 : Blo 471786 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1066589 : Blo 471786 1066589 := bbase (se 3 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 1066589 = 399971) (by norm_num)
theorem B1066661 : Blo 471786 1066661 := bbase (se 4 (by rfl) ⟨99999, by rfl⟩ : syracuseStep 1066661 = 199999) (by norm_num)
theorem B902821 : Blo 471786 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B1066733 : Blo 471786 1066733 := bbase (se 3 (by rfl) ⟨200012, by rfl⟩ : syracuseStep 1066733 = 400025) (by norm_num)
theorem B640813 : Blo 471786 640813 := bbase (se 3 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 640813 = 240305) (by norm_num)
theorem B1066805 : Blo 471786 1066805 := bbase (se 5 (by rfl) ⟨50006, by rfl⟩ : syracuseStep 1066805 = 100013) (by norm_num)
theorem B902981 : Blo 471786 902981 := bbase (se 4 (by rfl) ⟨84654, by rfl⟩ : syracuseStep 902981 = 169309) (by norm_num)
theorem B1197949 : Blo 471786 1197949 := bbase (se 3 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 1197949 = 449231) (by norm_num)
theorem B1066877 : Blo 471786 1066877 := bbase (se 3 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 1066877 = 400079) (by norm_num)
theorem B1066949 : Blo 471786 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B903125 : Blo 471786 903125 := bbase (se 7 (by rfl) ⟨10583, by rfl⟩ : syracuseStep 903125 = 21167) (by norm_num)
theorem B1198061 : Blo 471786 1198061 := bbase (se 3 (by rfl) ⟨224636, by rfl⟩ : syracuseStep 1198061 = 449273) (by norm_num)
theorem B1067021 : Blo 471786 1067021 := bbase (se 3 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 1067021 = 400133) (by norm_num)
theorem B1067093 : Blo 471786 1067093 := bbase (se 8 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 1067093 = 12505) (by norm_num)
theorem B1067165 : Blo 471786 1067165 := bbase (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) (by norm_num)
theorem B1198253 : Blo 471786 1198253 := bbase (se 3 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 1198253 = 449345) (by norm_num)
theorem B2017493 : Blo 471786 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B1067237 : Blo 471786 1067237 := bbase (se 4 (by rfl) ⟨100053, by rfl⟩ : syracuseStep 1067237 = 200107) (by norm_num)
theorem B674029 : Blo 471786 674029 := bbase (se 3 (by rfl) ⟨126380, by rfl⟩ : syracuseStep 674029 = 252761) (by norm_num)
theorem B641261 : Blo 471786 641261 := bbase (se 3 (by rfl) ⟨120236, by rfl⟩ : syracuseStep 641261 = 240473) (by norm_num)
theorem B1067309 : Blo 471786 1067309 := bbase (se 3 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 1067309 = 400241) (by norm_num)
theorem B1067381 : Blo 471786 1067381 := bbase (se 5 (by rfl) ⟨50033, by rfl⟩ : syracuseStep 1067381 = 100067) (by norm_num)
theorem B1067453 : Blo 471786 1067453 := bbase (se 3 (by rfl) ⟨200147, by rfl⟩ : syracuseStep 1067453 = 400295) (by norm_num)
theorem B2017781 : Blo 471786 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B1198597 : Blo 471786 1198597 := bbase (se 4 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 1198597 = 224737) (by norm_num)
theorem B1067525 : Blo 471786 1067525 := bbase (se 4 (by rfl) ⟨100080, by rfl⟩ : syracuseStep 1067525 = 200161) (by norm_num)
theorem B1067597 : Blo 471786 1067597 := bbase (se 3 (by rfl) ⟨200174, by rfl⟩ : syracuseStep 1067597 = 400349) (by norm_num)
theorem B1198709 : Blo 471786 1198709 := bbase (se 5 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 1198709 = 112379) (by norm_num)
theorem B1067669 : Blo 471786 1067669 := bbase (se 6 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 1067669 = 50047) (by norm_num)
theorem B1067741 : Blo 471786 1067741 := bbase (se 3 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 1067741 = 400403) (by norm_num)
theorem B969509 : Blo 471786 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B1067813 : Blo 471786 1067813 := bbase (se 4 (by rfl) ⟨100107, by rfl⟩ : syracuseStep 1067813 = 200215) (by norm_num)
theorem B1198901 : Blo 471786 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B1067885 : Blo 471786 1067885 := bbase (se 3 (by rfl) ⟨200228, by rfl⟩ : syracuseStep 1067885 = 400457) (by norm_num)
theorem B1067957 : Blo 471786 1067957 := bbase (se 5 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 1067957 = 100121) (by norm_num)
theorem B1068029 : Blo 471786 1068029 := bbase (se 3 (by rfl) ⟨200255, by rfl⟩ : syracuseStep 1068029 = 400511) (by norm_num)
theorem B674821 : Blo 471786 674821 := bbase (se 4 (by rfl) ⟨63264, by rfl⟩ : syracuseStep 674821 = 126529) (by norm_num)
theorem B1068101 : Blo 471786 1068101 := bbase (se 4 (by rfl) ⟨100134, by rfl⟩ : syracuseStep 1068101 = 200269) (by norm_num)
theorem B1592405 : Blo 471786 1592405 := bbase (se 8 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 1592405 = 18661) (by norm_num)
theorem B707693 : Blo 471786 707693 := bbase (se 3 (by rfl) ⟨132692, by rfl⟩ : syracuseStep 707693 = 265385) (by norm_num)
theorem B707717 : Blo 471786 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B1199245 : Blo 471786 1199245 := bbase (se 3 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 1199245 = 449717) (by norm_num)
theorem B1068173 : Blo 471786 1068173 := bbase (se 3 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 1068173 = 400565) (by norm_num)
theorem B707741 : Blo 471786 707741 := bbase (se 3 (by rfl) ⟨132701, by rfl⟩ : syracuseStep 707741 = 265403) (by norm_num)
theorem B707765 : Blo 471786 707765 := bbase (se 5 (by rfl) ⟨33176, by rfl⟩ : syracuseStep 707765 = 66353) (by norm_num)
theorem B707789 : Blo 471786 707789 := bbase (se 3 (by rfl) ⟨132710, by rfl⟩ : syracuseStep 707789 = 265421) (by norm_num)
theorem B1068245 : Blo 471786 1068245 := bbase (se 7 (by rfl) ⟨12518, by rfl⟩ : syracuseStep 1068245 = 25037) (by norm_num)
theorem B707813 : Blo 471786 707813 := bbase (se 4 (by rfl) ⟨66357, by rfl⟩ : syracuseStep 707813 = 132715) (by norm_num)
theorem B2018533 : Blo 471786 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B707837 : Blo 471786 707837 := bbase (se 3 (by rfl) ⟨132719, by rfl⟩ : syracuseStep 707837 = 265439) (by norm_num)
theorem B1199357 : Blo 471786 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B707861 : Blo 471786 707861 := bbase (se 6 (by rfl) ⟨16590, by rfl⟩ : syracuseStep 707861 = 33181) (by norm_num)
theorem B1068317 : Blo 471786 1068317 := bbase (se 3 (by rfl) ⟨200309, by rfl⟩ : syracuseStep 1068317 = 400619) (by norm_num)
theorem B707885 : Blo 471786 707885 := bbase (se 3 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 707885 = 265457) (by norm_num)
theorem B707909 : Blo 471786 707909 := bbase (se 4 (by rfl) ⟨66366, by rfl⟩ : syracuseStep 707909 = 132733) (by norm_num)
theorem B675157 : Blo 471786 675157 := bbase (se 11 (by rfl) ⟨494, by rfl⟩ : syracuseStep 675157 = 989) (by norm_num)
theorem B707933 : Blo 471786 707933 := bbase (se 3 (by rfl) ⟨132737, by rfl⟩ : syracuseStep 707933 = 265475) (by norm_num)
theorem B1068389 : Blo 471786 1068389 := bbase (se 4 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 1068389 = 200323) (by norm_num)
theorem B707957 : Blo 471786 707957 := bbase (se 5 (by rfl) ⟨33185, by rfl⟩ : syracuseStep 707957 = 66371) (by norm_num)
theorem B707981 : Blo 471786 707981 := bbase (se 3 (by rfl) ⟨132746, by rfl⟩ : syracuseStep 707981 = 265493) (by norm_num)
theorem B708005 : Blo 471786 708005 := bbase (se 4 (by rfl) ⟨66375, by rfl⟩ : syracuseStep 708005 = 132751) (by norm_num)
theorem B1068461 : Blo 471786 1068461 := bbase (se 3 (by rfl) ⟨200336, by rfl⟩ : syracuseStep 1068461 = 400673) (by norm_num)
theorem B708029 : Blo 471786 708029 := bbase (se 3 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 708029 = 265511) (by norm_num)
theorem B1199549 : Blo 471786 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B708053 : Blo 471786 708053 := bbase (se 7 (by rfl) ⟨8297, by rfl⟩ : syracuseStep 708053 = 16595) (by norm_num)
theorem B708077 : Blo 471786 708077 := bbase (se 3 (by rfl) ⟨132764, by rfl⟩ : syracuseStep 708077 = 265529) (by norm_num)
theorem B1068533 : Blo 471786 1068533 := bbase (se 5 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 1068533 = 100175) (by norm_num)
theorem B1592837 : Blo 471786 1592837 := bbase (se 4 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 1592837 = 298657) (by norm_num)
theorem B708101 : Blo 471786 708101 := bbase (se 4 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 708101 = 132769) (by norm_num)
theorem B708125 : Blo 471786 708125 := bbase (se 3 (by rfl) ⟨132773, by rfl⟩ : syracuseStep 708125 = 265547) (by norm_num)
theorem B675373 : Blo 471786 675373 := bbase (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) (by norm_num)
theorem B708149 : Blo 471786 708149 := bbase (se 5 (by rfl) ⟨33194, by rfl⟩ : syracuseStep 708149 = 66389) (by norm_num)
theorem B1068605 : Blo 471786 1068605 := bbase (se 3 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 1068605 = 400727) (by norm_num)
theorem B478793 : Blo 471786 478793 := bbase (se 2 (by rfl) ⟨179547, by rfl⟩ : syracuseStep 478793 = 359095) (by norm_num)
theorem B1134157 : Blo 471786 1134157 := bbase (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) (by norm_num)
theorem B708173 : Blo 471786 708173 := bbase (se 3 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 708173 = 265565) (by norm_num)
theorem B708197 : Blo 471786 708197 := bbase (se 4 (by rfl) ⟨66393, by rfl⟩ : syracuseStep 708197 = 132787) (by norm_num)
theorem B708221 : Blo 471786 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B1068677 : Blo 471786 1068677 := bbase (se 4 (by rfl) ⟨100188, by rfl⟩ : syracuseStep 1068677 = 200377) (by norm_num)
theorem B708245 : Blo 471786 708245 := bbase (se 6 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 708245 = 33199) (by norm_num)
theorem B1068701 : Blo 471786 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B708269 : Blo 471786 708269 := bbase (se 3 (by rfl) ⟨132800, by rfl⟩ : syracuseStep 708269 = 265601) (by norm_num)
theorem B708293 : Blo 471786 708293 := bbase (se 4 (by rfl) ⟨66402, by rfl⟩ : syracuseStep 708293 = 132805) (by norm_num)
theorem B1068749 : Blo 471786 1068749 := bbase (se 3 (by rfl) ⟨200390, by rfl⟩ : syracuseStep 1068749 = 400781) (by norm_num)
theorem B708317 : Blo 471786 708317 := bbase (se 3 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 708317 = 265619) (by norm_num)
theorem B511709 : Blo 471786 511709 := bbase (se 3 (by rfl) ⟨95945, by rfl⟩ : syracuseStep 511709 = 191891) (by norm_num)
theorem B708341 : Blo 471786 708341 := bbase (se 5 (by rfl) ⟨33203, by rfl⟩ : syracuseStep 708341 = 66407) (by norm_num)
theorem B708365 : Blo 471786 708365 := bbase (se 3 (by rfl) ⟨132818, by rfl⟩ : syracuseStep 708365 = 265637) (by norm_num)
theorem B1199893 : Blo 471786 1199893 := bbase (se 6 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 1199893 = 56245) (by norm_num)
theorem B1068821 : Blo 471786 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B708389 : Blo 471786 708389 := bbase (se 4 (by rfl) ⟨66411, by rfl⟩ : syracuseStep 708389 = 132823) (by norm_num)
theorem B708413 : Blo 471786 708413 := bbase (se 3 (by rfl) ⟨132827, by rfl⟩ : syracuseStep 708413 = 265655) (by norm_num)
theorem B708437 : Blo 471786 708437 := bbase (se 9 (by rfl) ⟨2075, by rfl⟩ : syracuseStep 708437 = 4151) (by norm_num)
theorem B1068893 : Blo 471786 1068893 := bbase (se 3 (by rfl) ⟨200417, by rfl⟩ : syracuseStep 1068893 = 400835) (by norm_num)
theorem B708461 : Blo 471786 708461 := bbase (se 3 (by rfl) ⟨132836, by rfl⟩ : syracuseStep 708461 = 265673) (by norm_num)
theorem B708485 : Blo 471786 708485 := bbase (se 4 (by rfl) ⟨66420, by rfl⟩ : syracuseStep 708485 = 132841) (by norm_num)
theorem B1200005 : Blo 471786 1200005 := bbase (se 4 (by rfl) ⟨112500, by rfl⟩ : syracuseStep 1200005 = 225001) (by norm_num)
theorem B708509 : Blo 471786 708509 := bbase (se 3 (by rfl) ⟨132845, by rfl⟩ : syracuseStep 708509 = 265691) (by norm_num)
theorem B675749 : Blo 471786 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B1068965 : Blo 471786 1068965 := bbase (se 4 (by rfl) ⟨100215, by rfl⟩ : syracuseStep 1068965 = 200431) (by norm_num)
theorem B1593269 : Blo 471786 1593269 := bbase (se 5 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 1593269 = 149369) (by norm_num)
theorem B708533 : Blo 471786 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B2019269 : Blo 471786 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B708557 : Blo 471786 708557 := bbase (se 3 (by rfl) ⟨132854, by rfl⟩ : syracuseStep 708557 = 265709) (by norm_num)
theorem B708581 : Blo 471786 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B1069037 : Blo 471786 1069037 := bbase (se 3 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 1069037 = 400889) (by norm_num)
theorem B708605 : Blo 471786 708605 := bbase (se 3 (by rfl) ⟨132863, by rfl⟩ : syracuseStep 708605 = 265727) (by norm_num)
theorem B708629 : Blo 471786 708629 := bbase (se 6 (by rfl) ⟨16608, by rfl⟩ : syracuseStep 708629 = 33217) (by norm_num)
theorem B708653 : Blo 471786 708653 := bbase (se 3 (by rfl) ⟨132872, by rfl⟩ : syracuseStep 708653 = 265745) (by norm_num)
theorem B1069109 : Blo 471786 1069109 := bbase (se 5 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 1069109 = 100229) (by norm_num)
theorem B708677 : Blo 471786 708677 := bbase (se 4 (by rfl) ⟨66438, by rfl⟩ : syracuseStep 708677 = 132877) (by norm_num)
theorem B1200197 : Blo 471786 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B708701 : Blo 471786 708701 := bbase (se 3 (by rfl) ⟨132881, by rfl⟩ : syracuseStep 708701 = 265763) (by norm_num)
theorem B708725 : Blo 471786 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B1069181 : Blo 471786 1069181 := bbase (se 3 (by rfl) ⟨200471, by rfl⟩ : syracuseStep 1069181 = 400943) (by norm_num)
theorem B708749 : Blo 471786 708749 := bbase (se 3 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 708749 = 265781) (by norm_num)
theorem B479389 : Blo 471786 479389 := bbase (se 3 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 479389 = 179771) (by norm_num)
theorem B708773 : Blo 471786 708773 := bbase (se 4 (by rfl) ⟨66447, by rfl⟩ : syracuseStep 708773 = 132895) (by norm_num)
theorem B1134773 : Blo 471786 1134773 := bbase (se 5 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 1134773 = 106385) (by norm_num)
theorem B708797 : Blo 471786 708797 := bbase (se 3 (by rfl) ⟨132899, by rfl⟩ : syracuseStep 708797 = 265799) (by norm_num)
theorem B1069253 : Blo 471786 1069253 := bbase (se 4 (by rfl) ⟨100242, by rfl⟩ : syracuseStep 1069253 = 200485) (by norm_num)
theorem B708821 : Blo 471786 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B708845 : Blo 471786 708845 := bbase (se 3 (by rfl) ⟨132908, by rfl⟩ : syracuseStep 708845 = 265817) (by norm_num)
theorem B708869 : Blo 471786 708869 := bbase (se 4 (by rfl) ⟨66456, by rfl⟩ : syracuseStep 708869 = 132913) (by norm_num)
theorem B1069325 : Blo 471786 1069325 := bbase (se 3 (by rfl) ⟨200498, by rfl⟩ : syracuseStep 1069325 = 400997) (by norm_num)
theorem B708893 : Blo 471786 708893 := bbase (se 3 (by rfl) ⟨132917, by rfl⟩ : syracuseStep 708893 = 265835) (by norm_num)
theorem B708917 : Blo 471786 708917 := bbase (se 5 (by rfl) ⟨33230, by rfl⟩ : syracuseStep 708917 = 66461) (by norm_num)
theorem B708941 : Blo 471786 708941 := bbase (se 3 (by rfl) ⟨132926, by rfl⟩ : syracuseStep 708941 = 265853) (by norm_num)
theorem B1069397 : Blo 471786 1069397 := bbase (se 10 (by rfl) ⟨1566, by rfl⟩ : syracuseStep 1069397 = 3133) (by norm_num)
theorem B1593701 : Blo 471786 1593701 := bbase (se 4 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 1593701 = 298819) (by norm_num)
theorem B708965 : Blo 471786 708965 := bbase (se 4 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 708965 = 132931) (by norm_num)
theorem B1134965 : Blo 471786 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B708989 : Blo 471786 708989 := bbase (se 3 (by rfl) ⟨132935, by rfl⟩ : syracuseStep 708989 = 265871) (by norm_num)
theorem B709013 : Blo 471786 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B1200541 : Blo 471786 1200541 := bbase (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) (by norm_num)
theorem B1069469 : Blo 471786 1069469 := bbase (se 3 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 1069469 = 401051) (by norm_num)
theorem B709037 : Blo 471786 709037 := bbase (se 3 (by rfl) ⟨132944, by rfl⟩ : syracuseStep 709037 = 265889) (by norm_num)
theorem B709061 : Blo 471786 709061 := bbase (se 4 (by rfl) ⟨66474, by rfl⟩ : syracuseStep 709061 = 132949) (by norm_num)
theorem B709085 : Blo 471786 709085 := bbase (se 3 (by rfl) ⟨132953, by rfl⟩ : syracuseStep 709085 = 265907) (by norm_num)
theorem B1069541 : Blo 471786 1069541 := bbase (se 4 (by rfl) ⟨100269, by rfl⟩ : syracuseStep 1069541 = 200539) (by norm_num)
theorem B709109 : Blo 471786 709109 := bbase (se 5 (by rfl) ⟨33239, by rfl⟩ : syracuseStep 709109 = 66479) (by norm_num)
theorem B709133 : Blo 471786 709133 := bbase (se 3 (by rfl) ⟨132962, by rfl⟩ : syracuseStep 709133 = 265925) (by norm_num)
theorem B1200653 : Blo 471786 1200653 := bbase (se 3 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 1200653 = 450245) (by norm_num)
theorem B709157 : Blo 471786 709157 := bbase (se 4 (by rfl) ⟨66483, by rfl⟩ : syracuseStep 709157 = 132967) (by norm_num)
theorem B1069613 : Blo 471786 1069613 := bbase (se 3 (by rfl) ⟨200552, by rfl⟩ : syracuseStep 1069613 = 401105) (by norm_num)
theorem B709181 : Blo 471786 709181 := bbase (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) (by norm_num)
theorem B1233485 : Blo 471786 1233485 := bbase (se 3 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 1233485 = 462557) (by norm_num)
theorem B709205 : Blo 471786 709205 := bbase (se 8 (by rfl) ⟨4155, by rfl⟩ : syracuseStep 709205 = 8311) (by norm_num)
theorem B709229 : Blo 471786 709229 := bbase (se 3 (by rfl) ⟨132980, by rfl⟩ : syracuseStep 709229 = 265961) (by norm_num)
theorem B1069685 : Blo 471786 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B709253 : Blo 471786 709253 := bbase (se 4 (by rfl) ⟨66492, by rfl⟩ : syracuseStep 709253 = 132985) (by norm_num)
theorem B709277 : Blo 471786 709277 := bbase (se 3 (by rfl) ⟨132989, by rfl⟩ : syracuseStep 709277 = 265979) (by norm_num)
theorem B709301 : Blo 471786 709301 := bbase (se 5 (by rfl) ⟨33248, by rfl⟩ : syracuseStep 709301 = 66497) (by norm_num)
theorem B1069757 : Blo 471786 1069757 := bbase (se 3 (by rfl) ⟨200579, by rfl⟩ : syracuseStep 1069757 = 401159) (by norm_num)
theorem B709325 : Blo 471786 709325 := bbase (se 3 (by rfl) ⟨132998, by rfl⟩ : syracuseStep 709325 = 265997) (by norm_num)
theorem B1200845 : Blo 471786 1200845 := bbase (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) (by norm_num)
theorem B709349 : Blo 471786 709349 := bbase (se 4 (by rfl) ⟨66501, by rfl⟩ : syracuseStep 709349 = 133003) (by norm_num)
theorem B709373 : Blo 471786 709373 := bbase (se 3 (by rfl) ⟨133007, by rfl⟩ : syracuseStep 709373 = 266015) (by norm_num)
theorem B1069829 : Blo 471786 1069829 := bbase (se 4 (by rfl) ⟨100296, by rfl⟩ : syracuseStep 1069829 = 200593) (by norm_num)
theorem B1594133 : Blo 471786 1594133 := bbase (se 6 (by rfl) ⟨37362, by rfl⟩ : syracuseStep 1594133 = 74725) (by norm_num)
theorem B709397 : Blo 471786 709397 := bbase (se 6 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 709397 = 33253) (by norm_num)
theorem B709421 : Blo 471786 709421 := bbase (se 3 (by rfl) ⟨133016, by rfl⟩ : syracuseStep 709421 = 266033) (by norm_num)
theorem B4117301 : Blo 471786 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B709445 : Blo 471786 709445 := bbase (se 4 (by rfl) ⟨66510, by rfl⟩ : syracuseStep 709445 = 133021) (by norm_num)
theorem B1069901 : Blo 471786 1069901 := bbase (se 3 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 1069901 = 401213) (by norm_num)
theorem B709469 : Blo 471786 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B709493 : Blo 471786 709493 := bbase (se 5 (by rfl) ⟨33257, by rfl⟩ : syracuseStep 709493 = 66515) (by norm_num)
theorem B709517 : Blo 471786 709517 := bbase (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) (by norm_num)
theorem B1069973 : Blo 471786 1069973 := bbase (se 6 (by rfl) ⟨25077, by rfl⟩ : syracuseStep 1069973 = 50155) (by norm_num)
theorem B709541 : Blo 471786 709541 := bbase (se 4 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 709541 = 133039) (by norm_num)
theorem B1135541 : Blo 471786 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B709565 : Blo 471786 709565 := bbase (se 3 (by rfl) ⟨133043, by rfl⟩ : syracuseStep 709565 = 266087) (by norm_num)
theorem B709589 : Blo 471786 709589 := bbase (se 7 (by rfl) ⟨8315, by rfl⟩ : syracuseStep 709589 = 16631) (by norm_num)
theorem B1070045 : Blo 471786 1070045 := bbase (se 3 (by rfl) ⟨200633, by rfl⟩ : syracuseStep 1070045 = 401267) (by norm_num)
theorem B709613 : Blo 471786 709613 := bbase (se 3 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 709613 = 266105) (by norm_num)
theorem B709637 : Blo 471786 709637 := bbase (se 4 (by rfl) ⟨66528, by rfl⟩ : syracuseStep 709637 = 133057) (by norm_num)
theorem B709661 : Blo 471786 709661 := bbase (se 3 (by rfl) ⟨133061, by rfl⟩ : syracuseStep 709661 = 266123) (by norm_num)
theorem B1201189 : Blo 471786 1201189 := bbase (se 4 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 1201189 = 225223) (by norm_num)
theorem B1070117 : Blo 471786 1070117 := bbase (se 4 (by rfl) ⟨100323, by rfl⟩ : syracuseStep 1070117 = 200647) (by norm_num)
theorem B709685 : Blo 471786 709685 := bbase (se 5 (by rfl) ⟨33266, by rfl⟩ : syracuseStep 709685 = 66533) (by norm_num)
theorem B709709 : Blo 471786 709709 := bbase (se 3 (by rfl) ⟨133070, by rfl⟩ : syracuseStep 709709 = 266141) (by norm_num)
theorem B709733 : Blo 471786 709733 := bbase (se 4 (by rfl) ⟨66537, by rfl⟩ : syracuseStep 709733 = 133075) (by norm_num)
theorem B1070189 : Blo 471786 1070189 := bbase (se 3 (by rfl) ⟨200660, by rfl⟩ : syracuseStep 1070189 = 401321) (by norm_num)
theorem B709757 : Blo 471786 709757 := bbase (se 3 (by rfl) ⟨133079, by rfl⟩ : syracuseStep 709757 = 266159) (by norm_num)
theorem B709781 : Blo 471786 709781 := bbase (se 6 (by rfl) ⟨16635, by rfl⟩ : syracuseStep 709781 = 33271) (by norm_num)
theorem B1201301 : Blo 471786 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B709805 : Blo 471786 709805 := bbase (se 3 (by rfl) ⟨133088, by rfl⟩ : syracuseStep 709805 = 266177) (by norm_num)
theorem B1070261 : Blo 471786 1070261 := bbase (se 5 (by rfl) ⟨50168, by rfl⟩ : syracuseStep 1070261 = 100337) (by norm_num)
theorem B1594565 : Blo 471786 1594565 := bbase (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) (by norm_num)
theorem B709829 : Blo 471786 709829 := bbase (se 4 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 709829 = 133093) (by norm_num)
theorem B709853 : Blo 471786 709853 := bbase (se 3 (by rfl) ⟨133097, by rfl⟩ : syracuseStep 709853 = 266195) (by norm_num)
theorem B709877 : Blo 471786 709877 := bbase (se 5 (by rfl) ⟨33275, by rfl⟩ : syracuseStep 709877 = 66551) (by norm_num)
theorem B1627381 : Blo 471786 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B1070333 : Blo 471786 1070333 := bbase (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) (by norm_num)
theorem B709901 : Blo 471786 709901 := bbase (se 3 (by rfl) ⟨133106, by rfl⟩ : syracuseStep 709901 = 266213) (by norm_num)
theorem B709925 : Blo 471786 709925 := bbase (se 4 (by rfl) ⟨66555, by rfl⟩ : syracuseStep 709925 = 133111) (by norm_num)
theorem B1135925 : Blo 471786 1135925 := bbase (se 5 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 1135925 = 106493) (by norm_num)
theorem B677173 : Blo 471786 677173 := bbase (se 5 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 677173 = 63485) (by norm_num)
theorem B709949 : Blo 471786 709949 := bbase (se 3 (by rfl) ⟨133115, by rfl⟩ : syracuseStep 709949 = 266231) (by norm_num)
theorem B1070405 : Blo 471786 1070405 := bbase (se 4 (by rfl) ⟨100350, by rfl⟩ : syracuseStep 1070405 = 200701) (by norm_num)
theorem B709973 : Blo 471786 709973 := bbase (se 15 (by rfl) ⟨32, by rfl⟩ : syracuseStep 709973 = 65) (by norm_num)
theorem B1201493 : Blo 471786 1201493 := bbase (se 16 (by rfl) ⟨27, by rfl⟩ : syracuseStep 1201493 = 55) (by norm_num)
theorem B709997 : Blo 471786 709997 := bbase (se 3 (by rfl) ⟨133124, by rfl⟩ : syracuseStep 709997 = 266249) (by norm_num)
theorem B710021 : Blo 471786 710021 := bbase (se 4 (by rfl) ⟨66564, by rfl⟩ : syracuseStep 710021 = 133129) (by norm_num)
theorem B1070477 : Blo 471786 1070477 := bbase (se 3 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 1070477 = 401429) (by norm_num)
theorem B710045 : Blo 471786 710045 := bbase (se 3 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 710045 = 266267) (by norm_num)
theorem B710069 : Blo 471786 710069 := bbase (se 5 (by rfl) ⟨33284, by rfl⟩ : syracuseStep 710069 = 66569) (by norm_num)
theorem B710093 : Blo 471786 710093 := bbase (se 3 (by rfl) ⟨133142, by rfl⟩ : syracuseStep 710093 = 266285) (by norm_num)
theorem B710117 : Blo 471786 710117 := bbase (se 4 (by rfl) ⟨66573, by rfl⟩ : syracuseStep 710117 = 133147) (by norm_num)
theorem B710141 : Blo 471786 710141 := bbase (se 3 (by rfl) ⟨133151, by rfl⟩ : syracuseStep 710141 = 266303) (by norm_num)
theorem B710165 : Blo 471786 710165 := bbase (se 6 (by rfl) ⟨16644, by rfl⟩ : syracuseStep 710165 = 33289) (by norm_num)
theorem B710189 : Blo 471786 710189 := bbase (se 3 (by rfl) ⟨133160, by rfl⟩ : syracuseStep 710189 = 266321) (by norm_num)
theorem B710213 : Blo 471786 710213 := bbase (se 4 (by rfl) ⟨66582, by rfl⟩ : syracuseStep 710213 = 133165) (by norm_num)
theorem B710237 : Blo 471786 710237 := bbase (se 3 (by rfl) ⟨133169, by rfl⟩ : syracuseStep 710237 = 266339) (by norm_num)
theorem B1594997 : Blo 471786 1594997 := bbase (se 5 (by rfl) ⟨74765, by rfl⟩ : syracuseStep 1594997 = 149531) (by norm_num)
theorem B710261 : Blo 471786 710261 := bbase (se 5 (by rfl) ⟨33293, by rfl⟩ : syracuseStep 710261 = 66587) (by norm_num)
theorem B710285 : Blo 471786 710285 := bbase (se 3 (by rfl) ⟨133178, by rfl⟩ : syracuseStep 710285 = 266357) (by norm_num)
theorem B710309 : Blo 471786 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B1201837 : Blo 471786 1201837 := bbase (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) (by norm_num)
theorem B710333 : Blo 471786 710333 := bbase (se 3 (by rfl) ⟨133187, by rfl⟩ : syracuseStep 710333 = 266375) (by norm_num)
theorem B710357 : Blo 471786 710357 := bbase (se 7 (by rfl) ⟨8324, by rfl⟩ : syracuseStep 710357 = 16649) (by norm_num)
theorem B710381 : Blo 471786 710381 := bbase (se 3 (by rfl) ⟨133196, by rfl⟩ : syracuseStep 710381 = 266393) (by norm_num)
theorem B710405 : Blo 471786 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B710429 : Blo 471786 710429 := bbase (se 3 (by rfl) ⟨133205, by rfl⟩ : syracuseStep 710429 = 266411) (by norm_num)
theorem B1201949 : Blo 471786 1201949 := bbase (se 3 (by rfl) ⟨225365, by rfl⟩ : syracuseStep 1201949 = 450731) (by norm_num)
theorem B710453 : Blo 471786 710453 := bbase (se 5 (by rfl) ⟨33302, by rfl⟩ : syracuseStep 710453 = 66605) (by norm_num)
theorem B710477 : Blo 471786 710477 := bbase (se 3 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 710477 = 266429) (by norm_num)
theorem B710501 : Blo 471786 710501 := bbase (se 4 (by rfl) ⟨66609, by rfl⟩ : syracuseStep 710501 = 133219) (by norm_num)
theorem B2283365 : Blo 471786 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B710525 : Blo 471786 710525 := bbase (se 3 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 710525 = 266447) (by norm_num)
theorem B6805397 : Blo 471786 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B710549 : Blo 471786 710549 := bbase (se 6 (by rfl) ⟨16653, by rfl⟩ : syracuseStep 710549 = 33307) (by norm_num)
theorem B710573 : Blo 471786 710573 := bbase (se 3 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 710573 = 266465) (by norm_num)
theorem B710597 : Blo 471786 710597 := bbase (se 4 (by rfl) ⟨66618, by rfl⟩ : syracuseStep 710597 = 133237) (by norm_num)
theorem B2283461 : Blo 471786 2283461 := bbase (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) (by norm_num)
theorem B710621 : Blo 471786 710621 := bbase (se 3 (by rfl) ⟨133241, by rfl⟩ : syracuseStep 710621 = 266483) (by norm_num)
theorem B1202141 : Blo 471786 1202141 := bbase (se 3 (by rfl) ⟨225401, by rfl⟩ : syracuseStep 1202141 = 450803) (by norm_num)
theorem B1791989 : Blo 471786 1791989 := bbase (se 5 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 1791989 = 167999) (by norm_num)
theorem B710645 : Blo 471786 710645 := bbase (se 5 (by rfl) ⟨33311, by rfl⟩ : syracuseStep 710645 = 66623) (by norm_num)
theorem B710669 : Blo 471786 710669 := bbase (se 3 (by rfl) ⟨133250, by rfl⟩ : syracuseStep 710669 = 266501) (by norm_num)
theorem B1595429 : Blo 471786 1595429 := bbase (se 4 (by rfl) ⟨149571, by rfl⟩ : syracuseStep 1595429 = 299143) (by norm_num)
theorem B710693 : Blo 471786 710693 := bbase (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) (by norm_num)
theorem B2709557 : Blo 471786 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B710717 : Blo 471786 710717 := bbase (se 3 (by rfl) ⟨133259, by rfl⟩ : syracuseStep 710717 = 266519) (by norm_num)
theorem B710741 : Blo 471786 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B710765 : Blo 471786 710765 := bbase (se 3 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 710765 = 266537) (by norm_num)
theorem B710789 : Blo 471786 710789 := bbase (se 4 (by rfl) ⟨66636, by rfl⟩ : syracuseStep 710789 = 133273) (by norm_num)
theorem B3037333 : Blo 471786 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B710813 : Blo 471786 710813 := bbase (se 3 (by rfl) ⟨133277, by rfl⟩ : syracuseStep 710813 = 266555) (by norm_num)
theorem B710837 : Blo 471786 710837 := bbase (se 5 (by rfl) ⟨33320, by rfl⟩ : syracuseStep 710837 = 66641) (by norm_num)
theorem B710861 : Blo 471786 710861 := bbase (se 3 (by rfl) ⟨133286, by rfl⟩ : syracuseStep 710861 = 266573) (by norm_num)
theorem B710885 : Blo 471786 710885 := bbase (se 4 (by rfl) ⟨66645, by rfl⟩ : syracuseStep 710885 = 133291) (by norm_num)
theorem B710909 : Blo 471786 710909 := bbase (se 3 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 710909 = 266591) (by norm_num)
theorem B1792277 : Blo 471786 1792277 := bbase (se 6 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 1792277 = 84013) (by norm_num)
theorem B710933 : Blo 471786 710933 := bbase (se 6 (by rfl) ⟨16662, by rfl⟩ : syracuseStep 710933 = 33325) (by norm_num)
theorem B710957 : Blo 471786 710957 := bbase (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) (by norm_num)
theorem B1202485 : Blo 471786 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B710981 : Blo 471786 710981 := bbase (se 4 (by rfl) ⟨66654, by rfl⟩ : syracuseStep 710981 = 133309) (by norm_num)
theorem B6838613 : Blo 471786 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B711005 : Blo 471786 711005 := bbase (se 3 (by rfl) ⟨133313, by rfl⟩ : syracuseStep 711005 = 266627) (by norm_num)
theorem B711029 : Blo 471786 711029 := bbase (se 5 (by rfl) ⟨33329, by rfl⟩ : syracuseStep 711029 = 66659) (by norm_num)
theorem B711053 : Blo 471786 711053 := bbase (se 3 (by rfl) ⟨133322, by rfl⟩ : syracuseStep 711053 = 266645) (by norm_num)
theorem B711077 : Blo 471786 711077 := bbase (se 4 (by rfl) ⟨66663, by rfl⟩ : syracuseStep 711077 = 133327) (by norm_num)
theorem B1202597 : Blo 471786 1202597 := bbase (se 4 (by rfl) ⟨112743, by rfl⟩ : syracuseStep 1202597 = 225487) (by norm_num)
theorem B514477 : Blo 471786 514477 := bbase (se 3 (by rfl) ⟨96464, by rfl⟩ : syracuseStep 514477 = 192929) (by norm_num)
theorem B711101 : Blo 471786 711101 := bbase (se 3 (by rfl) ⟨133331, by rfl⟩ : syracuseStep 711101 = 266663) (by norm_num)
theorem B1595861 : Blo 471786 1595861 := bbase (se 7 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 1595861 = 37403) (by norm_num)
theorem B711125 : Blo 471786 711125 := bbase (se 7 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 711125 = 16667) (by norm_num)
theorem B711149 : Blo 471786 711149 := bbase (se 3 (by rfl) ⟨133340, by rfl⟩ : syracuseStep 711149 = 266681) (by norm_num)
theorem B481781 : Blo 471786 481781 := bbase (se 5 (by rfl) ⟨22583, by rfl⟩ : syracuseStep 481781 = 45167) (by norm_num)
theorem B711173 : Blo 471786 711173 := bbase (se 4 (by rfl) ⟨66672, by rfl⟩ : syracuseStep 711173 = 133345) (by norm_num)
theorem B711197 : Blo 471786 711197 := bbase (se 3 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 711197 = 266699) (by norm_num)
theorem B711221 : Blo 471786 711221 := bbase (se 5 (by rfl) ⟨33338, by rfl⟩ : syracuseStep 711221 = 66677) (by norm_num)
theorem B711245 : Blo 471786 711245 := bbase (se 3 (by rfl) ⟨133358, by rfl⟩ : syracuseStep 711245 = 266717) (by norm_num)
theorem B711269 : Blo 471786 711269 := bbase (se 4 (by rfl) ⟨66681, by rfl⟩ : syracuseStep 711269 = 133363) (by norm_num)
theorem B1202789 : Blo 471786 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B711293 : Blo 471786 711293 := bbase (se 3 (by rfl) ⟨133367, by rfl⟩ : syracuseStep 711293 = 266735) (by norm_num)
theorem B711317 : Blo 471786 711317 := bbase (se 6 (by rfl) ⟨16671, by rfl⟩ : syracuseStep 711317 = 33343) (by norm_num)
theorem B1825445 : Blo 471786 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B940709 : Blo 471786 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B711341 : Blo 471786 711341 := bbase (se 3 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 711341 = 266753) (by norm_num)
theorem B711365 : Blo 471786 711365 := bbase (se 4 (by rfl) ⟨66690, by rfl⟩ : syracuseStep 711365 = 133381) (by norm_num)
theorem B711389 : Blo 471786 711389 := bbase (se 3 (by rfl) ⟨133385, by rfl⟩ : syracuseStep 711389 = 266771) (by norm_num)
theorem B711413 : Blo 471786 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B482041 : Blo 471786 482041 := bbase (se 2 (by rfl) ⟨180765, by rfl⟩ : syracuseStep 482041 = 361531) (by norm_num)
theorem B711437 : Blo 471786 711437 := bbase (se 3 (by rfl) ⟨133394, by rfl⟩ : syracuseStep 711437 = 266789) (by norm_num)
theorem B711461 : Blo 471786 711461 := bbase (se 4 (by rfl) ⟨66699, by rfl⟩ : syracuseStep 711461 = 133399) (by norm_num)
theorem B711485 : Blo 471786 711485 := bbase (se 3 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 711485 = 266807) (by norm_num)
theorem B711509 : Blo 471786 711509 := bbase (se 9 (by rfl) ⟨2084, by rfl⟩ : syracuseStep 711509 = 4169) (by norm_num)
theorem B711533 : Blo 471786 711533 := bbase (se 3 (by rfl) ⟨133412, by rfl⟩ : syracuseStep 711533 = 266825) (by norm_num)
theorem B1596293 : Blo 471786 1596293 := bbase (se 4 (by rfl) ⟨149652, by rfl⟩ : syracuseStep 1596293 = 299305) (by norm_num)
theorem B547717 : Blo 471786 547717 := bbase (se 4 (by rfl) ⟨51348, by rfl⟩ : syracuseStep 547717 = 102697) (by norm_num)
theorem B711557 : Blo 471786 711557 := bbase (se 4 (by rfl) ⟨66708, by rfl⟩ : syracuseStep 711557 = 133417) (by norm_num)
theorem B711581 : Blo 471786 711581 := bbase (se 3 (by rfl) ⟨133421, by rfl⟩ : syracuseStep 711581 = 266843) (by norm_num)
theorem B711605 : Blo 471786 711605 := bbase (se 5 (by rfl) ⟨33356, by rfl⟩ : syracuseStep 711605 = 66713) (by norm_num)
theorem B1203133 : Blo 471786 1203133 := bbase (se 3 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 1203133 = 451175) (by norm_num)
theorem B711629 : Blo 471786 711629 := bbase (se 3 (by rfl) ⟨133430, by rfl⟩ : syracuseStep 711629 = 266861) (by norm_num)
theorem B711653 : Blo 471786 711653 := bbase (se 4 (by rfl) ⟨66717, by rfl⟩ : syracuseStep 711653 = 133435) (by norm_num)
theorem B711677 : Blo 471786 711677 := bbase (se 3 (by rfl) ⟨133439, by rfl⟩ : syracuseStep 711677 = 266879) (by norm_num)
theorem B1137685 : Blo 471786 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B711701 : Blo 471786 711701 := bbase (se 6 (by rfl) ⟨16680, by rfl⟩ : syracuseStep 711701 = 33361) (by norm_num)
theorem B711725 : Blo 471786 711725 := bbase (se 3 (by rfl) ⟨133448, by rfl⟩ : syracuseStep 711725 = 266897) (by norm_num)
theorem B1203245 : Blo 471786 1203245 := bbase (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) (by norm_num)
theorem B711749 : Blo 471786 711749 := bbase (se 4 (by rfl) ⟨66726, by rfl⟩ : syracuseStep 711749 = 133453) (by norm_num)
theorem B711773 : Blo 471786 711773 := bbase (se 3 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 711773 = 266915) (by norm_num)
theorem B777325 : Blo 471786 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B711797 : Blo 471786 711797 := bbase (se 5 (by rfl) ⟨33365, by rfl⟩ : syracuseStep 711797 = 66731) (by norm_num)
theorem B711821 : Blo 471786 711821 := bbase (se 3 (by rfl) ⟨133466, by rfl⟩ : syracuseStep 711821 = 266933) (by norm_num)
theorem B2022565 : Blo 471786 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B711845 : Blo 471786 711845 := bbase (se 4 (by rfl) ⟨66735, by rfl⟩ : syracuseStep 711845 = 133471) (by norm_num)
theorem B711869 : Blo 471786 711869 := bbase (se 3 (by rfl) ⟨133475, by rfl⟩ : syracuseStep 711869 = 266951) (by norm_num)
theorem B711893 : Blo 471786 711893 := bbase (se 7 (by rfl) ⟨8342, by rfl⟩ : syracuseStep 711893 = 16685) (by norm_num)
theorem B711917 : Blo 471786 711917 := bbase (se 3 (by rfl) ⟨133484, by rfl⟩ : syracuseStep 711917 = 266969) (by norm_num)
theorem B1203437 : Blo 471786 1203437 := bbase (se 3 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 1203437 = 451289) (by norm_num)
theorem B711941 : Blo 471786 711941 := bbase (se 4 (by rfl) ⟨66744, by rfl⟩ : syracuseStep 711941 = 133489) (by norm_num)
theorem B711965 : Blo 471786 711965 := bbase (se 3 (by rfl) ⟨133493, by rfl⟩ : syracuseStep 711965 = 266987) (by norm_num)
theorem B1596725 : Blo 471786 1596725 := bbase (se 5 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 1596725 = 149693) (by norm_num)
theorem B711989 : Blo 471786 711989 := bbase (se 5 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 711989 = 66749) (by norm_num)
theorem B712013 : Blo 471786 712013 := bbase (se 3 (by rfl) ⟨133502, by rfl⟩ : syracuseStep 712013 = 267005) (by norm_num)
theorem B712037 : Blo 471786 712037 := bbase (se 4 (by rfl) ⟨66753, by rfl⟩ : syracuseStep 712037 = 133507) (by norm_num)
theorem B712061 : Blo 471786 712061 := bbase (se 3 (by rfl) ⟨133511, by rfl⟩ : syracuseStep 712061 = 267023) (by norm_num)
theorem B712085 : Blo 471786 712085 := bbase (se 6 (by rfl) ⟨16689, by rfl⟩ : syracuseStep 712085 = 33379) (by norm_num)
theorem B712109 : Blo 471786 712109 := bbase (se 3 (by rfl) ⟨133520, by rfl⟩ : syracuseStep 712109 = 267041) (by norm_num)
theorem B1793461 : Blo 471786 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B712133 : Blo 471786 712133 := bbase (se 4 (by rfl) ⟨66762, by rfl⟩ : syracuseStep 712133 = 133525) (by norm_num)
theorem B712157 : Blo 471786 712157 := bbase (se 3 (by rfl) ⟨133529, by rfl⟩ : syracuseStep 712157 = 267059) (by norm_num)
theorem B712181 : Blo 471786 712181 := bbase (se 5 (by rfl) ⟨33383, by rfl⟩ : syracuseStep 712181 = 66767) (by norm_num)
theorem B712205 : Blo 471786 712205 := bbase (se 3 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 712205 = 267077) (by norm_num)
theorem B712229 : Blo 471786 712229 := bbase (se 4 (by rfl) ⟨66771, by rfl⟩ : syracuseStep 712229 = 133543) (by norm_num)
theorem B712253 : Blo 471786 712253 := bbase (se 3 (by rfl) ⟨133547, by rfl⟩ : syracuseStep 712253 = 267095) (by norm_num)
theorem B1203781 : Blo 471786 1203781 := bbase (se 4 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 1203781 = 225709) (by norm_num)
theorem B712277 : Blo 471786 712277 := bbase (se 8 (by rfl) ⟨4173, by rfl⟩ : syracuseStep 712277 = 8347) (by norm_num)
theorem B712301 : Blo 471786 712301 := bbase (se 3 (by rfl) ⟨133556, by rfl⟩ : syracuseStep 712301 = 267113) (by norm_num)
theorem B712325 : Blo 471786 712325 := bbase (se 4 (by rfl) ⟨66780, by rfl⟩ : syracuseStep 712325 = 133561) (by norm_num)
theorem B712349 : Blo 471786 712349 := bbase (se 3 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 712349 = 267131) (by norm_num)
theorem B712373 : Blo 471786 712373 := bbase (se 5 (by rfl) ⟨33392, by rfl⟩ : syracuseStep 712373 = 66785) (by norm_num)
theorem B1203893 : Blo 471786 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B712397 : Blo 471786 712397 := bbase (se 3 (by rfl) ⟨133574, by rfl⟩ : syracuseStep 712397 = 267149) (by norm_num)
theorem B1793765 : Blo 471786 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B1597157 : Blo 471786 1597157 := bbase (se 4 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 1597157 = 299467) (by norm_num)
theorem B712421 : Blo 471786 712421 := bbase (se 4 (by rfl) ⟨66789, by rfl⟩ : syracuseStep 712421 = 133579) (by norm_num)
theorem B712445 : Blo 471786 712445 := bbase (se 3 (by rfl) ⟨133583, by rfl⟩ : syracuseStep 712445 = 267167) (by norm_num)
theorem B712469 : Blo 471786 712469 := bbase (se 6 (by rfl) ⟨16698, by rfl⟩ : syracuseStep 712469 = 33397) (by norm_num)
theorem B712493 : Blo 471786 712493 := bbase (se 3 (by rfl) ⟨133592, by rfl⟩ : syracuseStep 712493 = 267185) (by norm_num)
theorem B712517 : Blo 471786 712517 := bbase (se 4 (by rfl) ⟨66798, by rfl⟩ : syracuseStep 712517 = 133597) (by norm_num)
theorem B2285381 : Blo 471786 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B712541 : Blo 471786 712541 := bbase (se 3 (by rfl) ⟨133601, by rfl⟩ : syracuseStep 712541 = 267203) (by norm_num)
theorem B712565 : Blo 471786 712565 := bbase (se 5 (by rfl) ⟨33401, by rfl⟩ : syracuseStep 712565 = 66803) (by norm_num)
theorem B1204085 : Blo 471786 1204085 := bbase (se 5 (by rfl) ⟨56441, by rfl⟩ : syracuseStep 1204085 = 112883) (by norm_num)
theorem B712589 : Blo 471786 712589 := bbase (se 3 (by rfl) ⟨133610, by rfl⟩ : syracuseStep 712589 = 267221) (by norm_num)
theorem B712613 : Blo 471786 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B712637 : Blo 471786 712637 := bbase (se 3 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 712637 = 267239) (by norm_num)
theorem B712661 : Blo 471786 712661 := bbase (se 7 (by rfl) ⟨8351, by rfl⟩ : syracuseStep 712661 = 16703) (by norm_num)
theorem B712685 : Blo 471786 712685 := bbase (se 3 (by rfl) ⟨133628, by rfl⟩ : syracuseStep 712685 = 267257) (by norm_num)
theorem B1138693 : Blo 471786 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B712709 : Blo 471786 712709 := bbase (se 4 (by rfl) ⟨66816, by rfl⟩ : syracuseStep 712709 = 133633) (by norm_num)
theorem B712733 : Blo 471786 712733 := bbase (se 3 (by rfl) ⟨133637, by rfl⟩ : syracuseStep 712733 = 267275) (by norm_num)
theorem B1007653 : Blo 471786 1007653 := bbase (se 4 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 1007653 = 188935) (by norm_num)
theorem B712757 : Blo 471786 712757 := bbase (se 5 (by rfl) ⟨33410, by rfl⟩ : syracuseStep 712757 = 66821) (by norm_num)
theorem B712781 : Blo 471786 712781 := bbase (se 3 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 712781 = 267293) (by norm_num)
theorem B1138789 : Blo 471786 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B712805 : Blo 471786 712805 := bbase (se 4 (by rfl) ⟨66825, by rfl⟩ : syracuseStep 712805 = 133651) (by norm_num)
theorem B712829 : Blo 471786 712829 := bbase (se 3 (by rfl) ⟨133655, by rfl⟩ : syracuseStep 712829 = 267311) (by norm_num)
theorem B1597589 : Blo 471786 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B712853 : Blo 471786 712853 := bbase (se 6 (by rfl) ⟨16707, by rfl⟩ : syracuseStep 712853 = 33415) (by norm_num)
theorem B712877 : Blo 471786 712877 := bbase (se 3 (by rfl) ⟨133664, by rfl⟩ : syracuseStep 712877 = 267329) (by norm_num)
theorem B1007797 : Blo 471786 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B712901 : Blo 471786 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B712925 : Blo 471786 712925 := bbase (se 3 (by rfl) ⟨133673, by rfl⟩ : syracuseStep 712925 = 267347) (by norm_num)
theorem B712949 : Blo 471786 712949 := bbase (se 5 (by rfl) ⟨33419, by rfl⟩ : syracuseStep 712949 = 66839) (by norm_num)
theorem B712973 : Blo 471786 712973 := bbase (se 3 (by rfl) ⟨133682, by rfl⟩ : syracuseStep 712973 = 267365) (by norm_num)
theorem B712997 : Blo 471786 712997 := bbase (se 4 (by rfl) ⟨66843, by rfl⟩ : syracuseStep 712997 = 133687) (by norm_num)
theorem B713021 : Blo 471786 713021 := bbase (se 3 (by rfl) ⟨133691, by rfl⟩ : syracuseStep 713021 = 267383) (by norm_num)
theorem B713045 : Blo 471786 713045 := bbase (se 10 (by rfl) ⟨1044, by rfl⟩ : syracuseStep 713045 = 2089) (by norm_num)
theorem B713069 : Blo 471786 713069 := bbase (se 3 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 713069 = 267401) (by norm_num)
theorem B713093 : Blo 471786 713093 := bbase (se 4 (by rfl) ⟨66852, by rfl⟩ : syracuseStep 713093 = 133705) (by norm_num)
theorem B713117 : Blo 471786 713117 := bbase (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) (by norm_num)
theorem B713141 : Blo 471786 713141 := bbase (se 5 (by rfl) ⟨33428, by rfl⟩ : syracuseStep 713141 = 66857) (by norm_num)
theorem B713165 : Blo 471786 713165 := bbase (se 3 (by rfl) ⟨133718, by rfl⟩ : syracuseStep 713165 = 267437) (by norm_num)
theorem B713189 : Blo 471786 713189 := bbase (se 4 (by rfl) ⟨66861, by rfl⟩ : syracuseStep 713189 = 133723) (by norm_num)
theorem B811501 : Blo 471786 811501 := bbase (se 3 (by rfl) ⟨152156, by rfl⟩ : syracuseStep 811501 = 304313) (by norm_num)
theorem B713213 : Blo 471786 713213 := bbase (se 3 (by rfl) ⟨133727, by rfl⟩ : syracuseStep 713213 = 267455) (by norm_num)
theorem B713237 : Blo 471786 713237 := bbase (se 6 (by rfl) ⟨16716, by rfl⟩ : syracuseStep 713237 = 33433) (by norm_num)
theorem B1008173 : Blo 471786 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B713261 : Blo 471786 713261 := bbase (se 3 (by rfl) ⟨133736, by rfl⟩ : syracuseStep 713261 = 267473) (by norm_num)
theorem B1598021 : Blo 471786 1598021 := bbase (se 4 (by rfl) ⟨149814, by rfl⟩ : syracuseStep 1598021 = 299629) (by norm_num)
theorem B713285 : Blo 471786 713285 := bbase (se 4 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 713285 = 133741) (by norm_num)
theorem B3596885 : Blo 471786 3596885 := bbase (se 8 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 3596885 = 42151) (by norm_num)
theorem B713309 : Blo 471786 713309 := bbase (se 3 (by rfl) ⟨133745, by rfl⟩ : syracuseStep 713309 = 267491) (by norm_num)
theorem B1139309 : Blo 471786 1139309 := bbase (se 3 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 1139309 = 427241) (by norm_num)
theorem B1532533 : Blo 471786 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B713333 : Blo 471786 713333 := bbase (se 5 (by rfl) ⟨33437, by rfl⟩ : syracuseStep 713333 = 66875) (by norm_num)
theorem B713357 : Blo 471786 713357 := bbase (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) (by norm_num)
theorem B713381 : Blo 471786 713381 := bbase (se 4 (by rfl) ⟨66879, by rfl⟩ : syracuseStep 713381 = 133759) (by norm_num)
theorem B713405 : Blo 471786 713405 := bbase (se 3 (by rfl) ⟨133763, by rfl⟩ : syracuseStep 713405 = 267527) (by norm_num)
theorem B713429 : Blo 471786 713429 := bbase (se 7 (by rfl) ⟨8360, by rfl⟩ : syracuseStep 713429 = 16721) (by norm_num)
theorem B713453 : Blo 471786 713453 := bbase (se 3 (by rfl) ⟨133772, by rfl⟩ : syracuseStep 713453 = 267545) (by norm_num)
theorem B713477 : Blo 471786 713477 := bbase (se 4 (by rfl) ⟨66888, by rfl⟩ : syracuseStep 713477 = 133777) (by norm_num)
theorem B713501 : Blo 471786 713501 := bbase (se 3 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 713501 = 267563) (by norm_num)
theorem B713525 : Blo 471786 713525 := bbase (se 5 (by rfl) ⟨33446, by rfl⟩ : syracuseStep 713525 = 66893) (by norm_num)
theorem B1729349 : Blo 471786 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B1925957 : Blo 471786 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B713549 : Blo 471786 713549 := bbase (se 3 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 713549 = 267581) (by norm_num)
theorem B713573 : Blo 471786 713573 := bbase (se 4 (by rfl) ⟨66897, by rfl⟩ : syracuseStep 713573 = 133795) (by norm_num)
theorem B713597 : Blo 471786 713597 := bbase (se 3 (by rfl) ⟨133799, by rfl⟩ : syracuseStep 713597 = 267599) (by norm_num)
theorem B713621 : Blo 471786 713621 := bbase (se 6 (by rfl) ⟨16725, by rfl⟩ : syracuseStep 713621 = 33451) (by norm_num)
theorem B1008541 : Blo 471786 1008541 := bbase (se 3 (by rfl) ⟨189101, by rfl⟩ : syracuseStep 1008541 = 378203) (by norm_num)
theorem B615325 : Blo 471786 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B713645 : Blo 471786 713645 := bbase (se 3 (by rfl) ⟨133808, by rfl⟩ : syracuseStep 713645 = 267617) (by norm_num)
theorem B713669 : Blo 471786 713669 := bbase (se 4 (by rfl) ⟨66906, by rfl⟩ : syracuseStep 713669 = 133813) (by norm_num)
theorem B1598453 : Blo 471786 1598453 := bbase (se 5 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 1598453 = 149855) (by norm_num)
theorem B1139837 : Blo 471786 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B2876725 : Blo 471786 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B1140077 : Blo 471786 1140077 := bbase (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) (by norm_num)
theorem B1598885 : Blo 471786 1598885 := bbase (se 4 (by rfl) ⟨149895, by rfl⟩ : syracuseStep 1598885 = 299791) (by norm_num)
theorem B976573 : Blo 471786 976573 := bbase (se 3 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 976573 = 366215) (by norm_num)
theorem B485141 : Blo 471786 485141 := bbase (se 6 (by rfl) ⟨11370, by rfl⟩ : syracuseStep 485141 = 22741) (by norm_num)
theorem B1795877 : Blo 471786 1795877 := bbase (se 4 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 1795877 = 336727) (by norm_num)
theorem B1828645 : Blo 471786 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B1599317 : Blo 471786 1599317 := bbase (se 9 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 1599317 = 9371) (by norm_num)
theorem B1927157 : Blo 471786 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B3041333 : Blo 471786 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B1796165 : Blo 471786 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B2025557 : Blo 471786 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1599749 : Blo 471786 1599749 := bbase (se 4 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 1599749 = 299953) (by norm_num)
theorem B1010045 : Blo 471786 1010045 := bbase (se 3 (by rfl) ⟨189383, by rfl⟩ : syracuseStep 1010045 = 378767) (by norm_num)
theorem B1010189 : Blo 471786 1010189 := bbase (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) (by norm_num)
theorem B813581 : Blo 471786 813581 := bbase (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) (by norm_num)
theorem B2878037 : Blo 471786 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B1600181 : Blo 471786 1600181 := bbase (se 5 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 1600181 = 150017) (by norm_num)
theorem B1829573 : Blo 471786 1829573 := bbase (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) (by norm_num)
theorem B1010549 : Blo 471786 1010549 := bbase (se 5 (by rfl) ⟨47369, by rfl⟩ : syracuseStep 1010549 = 94739) (by norm_num)
theorem B584593 : Blo 471786 584593 := bbase (se 2 (by rfl) ⟨219222, by rfl⟩ : syracuseStep 584593 = 438445) (by norm_num)
theorem B1141789 : Blo 471786 1141789 := bbase (se 3 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 1141789 = 428171) (by norm_num)
theorem B2026565 : Blo 471786 2026565 := bbase (se 4 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 2026565 = 379981) (by norm_num)
theorem B1600613 : Blo 471786 1600613 := bbase (se 4 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 1600613 = 300115) (by norm_num)
theorem B2059445 : Blo 471786 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B1797349 : Blo 471786 1797349 := bbase (se 4 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 1797349 = 337003) (by norm_num)
theorem B1535365 : Blo 471786 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B1797653 : Blo 471786 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B1601045 : Blo 471786 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B1011437 : Blo 471786 1011437 := bbase (se 3 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 1011437 = 379289) (by norm_num)
theorem B683861 : Blo 471786 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B487253 : Blo 471786 487253 := bbase (se 9 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 487253 = 2855) (by norm_num)
theorem B1601477 : Blo 471786 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B1011685 : Blo 471786 1011685 := bbase (se 4 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 1011685 = 189691) (by norm_num)
theorem B8122517 : Blo 471786 8122517 := bbase (se 6 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 8122517 = 380743) (by norm_num)
theorem B782669 : Blo 471786 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1601909 : Blo 471786 1601909 := bbase (se 5 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 1601909 = 150179) (by norm_num)
theorem B1012189 : Blo 471786 1012189 := bbase (se 3 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 1012189 = 379571) (by norm_num)
theorem B913885 : Blo 471786 913885 := bbase (se 3 (by rfl) ⟨171353, by rfl⟩ : syracuseStep 913885 = 342707) (by norm_num)
theorem B1602341 : Blo 471786 1602341 := bbase (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) (by norm_num)
theorem B2028341 : Blo 471786 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B2389013 : Blo 471786 2389013 := bbase (se 6 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 2389013 = 111985) (by norm_num)
theorem B521321 : Blo 471786 521321 := bbase (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) (by norm_num)
theorem B1602773 : Blo 471786 1602773 := bbase (se 7 (by rfl) ⟨18782, by rfl⟩ : syracuseStep 1602773 = 37565) (by norm_num)
theorem B4846837 : Blo 471786 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B1013077 : Blo 471786 1013077 := bbase (se 13 (by rfl) ⟨185, by rfl⟩ : syracuseStep 1013077 = 371) (by norm_num)
theorem B521677 : Blo 471786 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B1799765 : Blo 471786 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B1603205 : Blo 471786 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B685837 : Blo 471786 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B1013573 : Blo 471786 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B1800053 : Blo 471786 1800053 := bbase (se 5 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 1800053 = 168755) (by norm_num)
theorem B1603637 : Blo 471786 1603637 := bbase (se 5 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 1603637 = 150341) (by norm_num)
theorem B2390309 : Blo 471786 2390309 := bbase (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) (by norm_num)
theorem B1604069 : Blo 471786 1604069 := bbase (se 4 (by rfl) ⟨150381, by rfl⟩ : syracuseStep 1604069 = 300763) (by norm_num)
theorem B1276469 : Blo 471786 1276469 := bbase (se 5 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 1276469 = 119669) (by norm_num)
theorem B1014461 : Blo 471786 1014461 := bbase (se 3 (by rfl) ⟨190211, by rfl⟩ : syracuseStep 1014461 = 380423) (by norm_num)
theorem B1014581 : Blo 471786 1014581 := bbase (se 5 (by rfl) ⟨47558, by rfl⟩ : syracuseStep 1014581 = 95117) (by norm_num)
theorem B1440661 : Blo 471786 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1604501 : Blo 471786 1604501 := bbase (se 6 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 1604501 = 75211) (by norm_num)
theorem B1276901 : Blo 471786 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B1801237 : Blo 471786 1801237 := bbase (se 6 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 1801237 = 84433) (by norm_num)
theorem B1801541 : Blo 471786 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B1604933 : Blo 471786 1604933 := bbase (se 4 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 1604933 = 300925) (by norm_num)
theorem B1211813 : Blo 471786 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B1015213 : Blo 471786 1015213 := bbase (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) (by norm_num)
theorem B8224213 : Blo 471786 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B2391605 : Blo 471786 2391605 := bbase (se 5 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 2391605 = 224213) (by norm_num)
theorem B1605365 : Blo 471786 1605365 := bbase (se 5 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 1605365 = 150503) (by norm_num)
theorem B3047381 : Blo 471786 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1015811 : Blo 471786 1015811 := bstep (se 1 (by rfl) ⟨761858, by rfl⟩ : syracuseStep 1015811 = 1523717) B1523717
theorem B1605635 : Blo 471786 1605635 := bstep (se 1 (by rfl) ⟨1204226, by rfl⟩ : syracuseStep 1605635 = 2408453) B2408453
theorem B1343537 : Blo 471786 1343537 := bstep (se 2 (by rfl) ⟨503826, by rfl⟩ : syracuseStep 1343537 = 1007653) B1007653
theorem B52396145 : Blo 471786 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1343729 : Blo 471786 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B852515 : Blo 471786 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B2392739 : Blo 471786 2392739 := bstep (se 1 (by rfl) ⟨1794554, by rfl⟩ : syracuseStep 2392739 = 3589109) B3589109
theorem B1868579 : Blo 471786 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B6128453 : Blo 471786 6128453 := bstep (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) B1149085
theorem B2556785 : Blo 471786 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B2688005 : Blo 471786 2688005 := bstep (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) B504001
theorem B1344721 : Blo 471786 1344721 := bstep (se 2 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 1344721 = 1008541) B1008541
theorem B820433 : Blo 471786 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B16647565 : Blo 471786 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B2688461 : Blo 471786 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B2393549 : Blo 471786 2393549 := bstep (se 3 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 2393549 = 897581) B897581
theorem B1344995 : Blo 471786 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B1345187 : Blo 471786 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B3835633 : Blo 471786 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B2164657 : Blo 471786 2164657 := bstep (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) B1623493
theorem B1149265 : Blo 471786 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B1706339 : Blo 471786 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B854417 : Blo 471786 854417 := bstep (se 2 (by rfl) ⟨320406, by rfl⟩ : syracuseStep 854417 = 640813) B640813
theorem B1345997 : Blo 471786 1345997 := bstep (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) B504749
theorem B4328005 : Blo 471786 4328005 := bstep (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) B811501
theorem B1149553 : Blo 471786 1149553 := bstep (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) B862165
theorem B1804913 : Blo 471786 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B1346179 : Blo 471786 1346179 := bstep (se 1 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 1346179 = 2019269) B2019269
theorem B756515 : Blo 471786 756515 := bstep (se 1 (by rfl) ⟨567386, by rfl⟩ : syracuseStep 756515 = 1134773) B1134773
theorem B756643 : Blo 471786 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B822323 : Blo 471786 822323 := bstep (se 1 (by rfl) ⟨616742, by rfl⟩ : syracuseStep 822323 = 1233485) B1233485
theorem B1346669 : Blo 471786 1346669 := bstep (se 3 (by rfl) ⟨252500, by rfl⟩ : syracuseStep 1346669 = 505001) B505001
theorem B757027 : Blo 471786 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B757283 : Blo 471786 757283 := bstep (se 1 (by rfl) ⟨567962, by rfl⟩ : syracuseStep 757283 = 1135925) B1135925
theorem B1445539 : Blo 471786 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B3411811 : Blo 471786 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B757745 : Blo 471786 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B1806371 : Blo 471786 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B757841 : Blo 471786 757841 := bstep (se 2 (by rfl) ⟨284190, by rfl⟩ : syracuseStep 757841 = 568381) B568381
theorem B757873 : Blo 471786 757873 := bstep (se 2 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 757873 = 568405) B568405
theorem B528563 : Blo 471786 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B4559075 : Blo 471786 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B1347853 : Blo 471786 1347853 := bstep (se 3 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 1347853 = 505445) B505445
theorem B2691377 : Blo 471786 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B2396465 : Blo 471786 2396465 := bstep (se 2 (by rfl) ⟨898674, by rfl⟩ : syracuseStep 2396465 = 1797349) B1797349
theorem B1216963 : Blo 471786 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B627139 : Blo 471786 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B1282673 : Blo 471786 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B1708721 : Blo 471786 1708721 := bstep (se 2 (by rfl) ⟨640770, by rfl⟩ : syracuseStep 1708721 = 1281541) B1281541
theorem B1512209 : Blo 471786 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B1348913 : Blo 471786 1348913 := bstep (se 2 (by rfl) ⟨505842, by rfl⟩ : syracuseStep 1348913 = 1011685) B1011685
theorem B2692835 : Blo 471786 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B2397923 : Blo 471786 2397923 := bstep (se 1 (by rfl) ⟨1798442, by rfl⟩ : syracuseStep 2397923 = 3596885) B3596885
theorem B759539 : Blo 471786 759539 := bstep (se 1 (by rfl) ⟨569654, by rfl⟩ : syracuseStep 759539 = 1139309) B1139309
theorem B1283971 : Blo 471786 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B1152899 : Blo 471786 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B1710029 : Blo 471786 1710029 := bstep (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) B641261
theorem B1349585 : Blo 471786 1349585 := bstep (se 2 (by rfl) ⟨506094, by rfl⟩ : syracuseStep 1349585 = 1012189) B1012189
theorem B760051 : Blo 471786 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B4921613 : Blo 471786 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B760097 : Blo 471786 760097 := bstep (se 2 (by rfl) ⟨285036, by rfl⟩ : syracuseStep 760097 = 570073) B570073
theorem B3610979 : Blo 471786 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B530851 : Blo 471786 530851 := bstep (se 1 (by rfl) ⟨398138, by rfl⟩ : syracuseStep 530851 = 796277) B796277
theorem B2398733 : Blo 471786 2398733 := bstep (se 3 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 2398733 = 899525) B899525
theorem B530995 : Blo 471786 530995 := bstep (se 1 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 530995 = 796493) B796493
theorem B1284749 : Blo 471786 1284749 := bstep (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) B481781
theorem B531139 : Blo 471786 531139 := bstep (se 1 (by rfl) ⟨398354, by rfl⟩ : syracuseStep 531139 = 796709) B796709
theorem B2693837 : Blo 471786 2693837 := bstep (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) B1010189
theorem B1350371 : Blo 471786 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B1514285 : Blo 471786 1514285 := bstep (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) B567857
theorem B531283 : Blo 471786 531283 := bstep (se 1 (by rfl) ⟨398462, by rfl⟩ : syracuseStep 531283 = 796925) B796925
theorem B760769 : Blo 471786 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B531427 : Blo 471786 531427 := bstep (se 1 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 531427 = 797141) B797141
theorem B6462449 : Blo 471786 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B2169841 : Blo 471786 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B1350701 : Blo 471786 1350701 := bstep (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) B506513
theorem B1711153 : Blo 471786 1711153 := bstep (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) B1283365
theorem B1350769 : Blo 471786 1350769 := bstep (se 2 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 1350769 = 1013077) B1013077
theorem B531571 : Blo 471786 531571 := bstep (se 1 (by rfl) ⟨398678, by rfl⟩ : syracuseStep 531571 = 797357) B797357
theorem B1219715 : Blo 471786 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B531715 : Blo 471786 531715 := bstep (se 1 (by rfl) ⟨398786, by rfl⟩ : syracuseStep 531715 = 797573) B797573
theorem B695569 : Blo 471786 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B1351043 : Blo 471786 1351043 := bstep (se 1 (by rfl) ⟨1013282, by rfl⟩ : syracuseStep 1351043 = 2026565) B2026565
theorem B597395 : Blo 471786 597395 := bstep (se 1 (by rfl) ⟨448046, by rfl⟩ : syracuseStep 597395 = 896093) B896093
theorem B531859 : Blo 471786 531859 := bstep (se 1 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 531859 = 797789) B797789
theorem B761281 : Blo 471786 761281 := bstep (se 2 (by rfl) ⟨285480, by rfl⟩ : syracuseStep 761281 = 570961) B570961
theorem B532003 : Blo 471786 532003 := bstep (se 1 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 532003 = 798005) B798005
theorem B1515181 : Blo 471786 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B532147 : Blo 471786 532147 := bstep (se 1 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 532147 = 798221) B798221
theorem B532291 : Blo 471786 532291 := bstep (se 1 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 532291 = 798437) B798437
theorem B532435 : Blo 471786 532435 := bstep (se 1 (by rfl) ⟨399326, by rfl⟩ : syracuseStep 532435 = 798653) B798653
theorem B598099 : Blo 471786 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B532579 : Blo 471786 532579 := bstep (se 1 (by rfl) ⟨399434, by rfl⟩ : syracuseStep 532579 = 798869) B798869
theorem B5415011 : Blo 471786 5415011 := bstep (se 1 (by rfl) ⟨4061258, by rfl⟩ : syracuseStep 5415011 = 8122517) B8122517
theorem B598195 : Blo 471786 598195 := bstep (se 1 (by rfl) ⟨448646, by rfl⟩ : syracuseStep 598195 = 897293) B897293
theorem B1351885 : Blo 471786 1351885 := bstep (se 3 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 1351885 = 506957) B506957
theorem B532723 : Blo 471786 532723 := bstep (se 1 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 532723 = 799085) B799085
theorem B1352045 : Blo 471786 1352045 := bstep (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) B507017
theorem B532867 : Blo 471786 532867 := bstep (se 1 (by rfl) ⟨399650, by rfl⟩ : syracuseStep 532867 = 799301) B799301
theorem B533011 : Blo 471786 533011 := bstep (se 1 (by rfl) ⟨399758, by rfl⟩ : syracuseStep 533011 = 799517) B799517
theorem B1352227 : Blo 471786 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B598691 : Blo 471786 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B533155 : Blo 471786 533155 := bstep (se 1 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 533155 = 799733) B799733
theorem B1516259 : Blo 471786 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B533299 : Blo 471786 533299 := bstep (se 1 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 533299 = 799949) B799949
theorem B8070029 : Blo 471786 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B533443 : Blo 471786 533443 := bstep (se 1 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 533443 = 800165) B800165
theorem B533587 : Blo 471786 533587 := bstep (se 1 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 533587 = 800381) B800381
theorem B730289 : Blo 471786 730289 := bstep (se 2 (by rfl) ⟨273858, by rfl⟩ : syracuseStep 730289 = 547717) B547717
theorem B533731 : Blo 471786 533731 := bstep (se 1 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 533731 = 800597) B800597
theorem B599395 : Blo 471786 599395 := bstep (se 1 (by rfl) ⟨449546, by rfl⟩ : syracuseStep 599395 = 899093) B899093
theorem B1516913 : Blo 471786 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B2401649 : Blo 471786 2401649 := bstep (se 2 (by rfl) ⟨900618, by rfl⟩ : syracuseStep 2401649 = 1801237) B1801237
theorem B533875 : Blo 471786 533875 := bstep (se 1 (by rfl) ⟨400406, by rfl⟩ : syracuseStep 533875 = 800813) B800813
theorem B12166541 : Blo 471786 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B599491 : Blo 471786 599491 := bstep (se 1 (by rfl) ⟨449618, by rfl⟩ : syracuseStep 599491 = 899237) B899237
theorem B534019 : Blo 471786 534019 := bstep (se 1 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 534019 = 801029) B801029
theorem B2696753 : Blo 471786 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B796243 : Blo 471786 796243 := bstep (se 1 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 796243 = 1194365) B1194365
theorem B534163 : Blo 471786 534163 := bstep (se 1 (by rfl) ⟨400622, by rfl⟩ : syracuseStep 534163 = 801245) B801245
theorem B796385 : Blo 471786 796385 := bstep (se 2 (by rfl) ⟨298644, by rfl⟩ : syracuseStep 796385 = 597289) B597289
theorem B534307 : Blo 471786 534307 := bstep (se 1 (by rfl) ⟨400730, by rfl⟩ : syracuseStep 534307 = 801461) B801461
theorem B796513 : Blo 471786 796513 := bstep (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) B597385
theorem B1025905 : Blo 471786 1025905 := bstep (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) B769429
theorem B796547 : Blo 471786 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B6072205 : Blo 471786 6072205 := bstep (se 3 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 6072205 = 2277077) B2277077
theorem B1353617 : Blo 471786 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B3024803 : Blo 471786 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B599987 : Blo 471786 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B534451 : Blo 471786 534451 := bstep (se 1 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 534451 = 801677) B801677
theorem B796675 : Blo 471786 796675 := bstep (se 1 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 796675 = 1195013) B1195013
theorem B534595 : Blo 471786 534595 := bstep (se 1 (by rfl) ⟨400946, by rfl⟩ : syracuseStep 534595 = 801893) B801893
theorem B5187725 : Blo 471786 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B796817 : Blo 471786 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B534739 : Blo 471786 534739 := bstep (se 1 (by rfl) ⟨401054, by rfl⟩ : syracuseStep 534739 = 802109) B802109
theorem B7416035 : Blo 471786 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B796945 : Blo 471786 796945 := bstep (se 2 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 796945 = 597709) B597709
theorem B796979 : Blo 471786 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B4041029 : Blo 471786 4041029 := bstep (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) B757693
theorem B534883 : Blo 471786 534883 := bstep (se 1 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 534883 = 802325) B802325
theorem B797107 : Blo 471786 797107 := bstep (se 1 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 797107 = 1195661) B1195661
theorem B535027 : Blo 471786 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B797249 : Blo 471786 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B600691 : Blo 471786 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B535171 : Blo 471786 535171 := bstep (se 1 (by rfl) ⟨401378, by rfl⟩ : syracuseStep 535171 = 802757) B802757
theorem B1518257 : Blo 471786 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B797377 : Blo 471786 797377 := bstep (se 2 (by rfl) ⟨299016, by rfl⟩ : syracuseStep 797377 = 598033) B598033
theorem B600787 : Blo 471786 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B797411 : Blo 471786 797411 := bstep (se 1 (by rfl) ⟨598058, by rfl⟩ : syracuseStep 797411 = 1196117) B1196117
theorem B2403107 : Blo 471786 2403107 := bstep (se 1 (by rfl) ⟨1802330, by rfl⟩ : syracuseStep 2403107 = 3604661) B3604661
theorem B1354573 : Blo 471786 1354573 := bstep (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) B507965
theorem B797539 : Blo 471786 797539 := bstep (se 1 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 797539 = 1196309) B1196309
theorem B2698211 : Blo 471786 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B797681 : Blo 471786 797681 := bstep (se 2 (by rfl) ⟨299130, by rfl⟩ : syracuseStep 797681 = 598261) B598261
theorem B896017 : Blo 471786 896017 := bstep (se 2 (by rfl) ⟨336006, by rfl⟩ : syracuseStep 896017 = 672013) B672013
theorem B1354801 : Blo 471786 1354801 := bstep (se 2 (by rfl) ⟨508050, by rfl⟩ : syracuseStep 1354801 = 1016101) B1016101
theorem B797809 : Blo 471786 797809 := bstep (se 2 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 797809 = 598357) B598357
theorem B797843 : Blo 471786 797843 := bstep (se 1 (by rfl) ⟨598382, by rfl⟩ : syracuseStep 797843 = 1196765) B1196765
theorem B896177 : Blo 471786 896177 := bstep (se 2 (by rfl) ⟨336066, by rfl⟩ : syracuseStep 896177 = 672133) B672133
theorem B601283 : Blo 471786 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B6073541 : Blo 471786 6073541 := bstep (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) B1138789
theorem B797971 : Blo 471786 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B798113 : Blo 471786 798113 := bstep (se 2 (by rfl) ⟨299292, by rfl⟩ : syracuseStep 798113 = 598585) B598585
theorem B1027505 : Blo 471786 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B2043377 : Blo 471786 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B798241 : Blo 471786 798241 := bstep (se 2 (by rfl) ⟨299340, by rfl⟩ : syracuseStep 798241 = 598681) B598681
theorem B896579 : Blo 471786 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B798275 : Blo 471786 798275 := bstep (se 1 (by rfl) ⟨598706, by rfl⟩ : syracuseStep 798275 = 1197413) B1197413
theorem B2403917 : Blo 471786 2403917 := bstep (se 3 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 2403917 = 901469) B901469
theorem B9088625 : Blo 471786 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B798403 : Blo 471786 798403 := bstep (se 1 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 798403 = 1197605) B1197605
theorem B1519373 : Blo 471786 1519373 := bstep (se 3 (by rfl) ⟨284882, by rfl⟩ : syracuseStep 1519373 = 569765) B569765
theorem B798545 : Blo 471786 798545 := bstep (se 2 (by rfl) ⟨299454, by rfl⟩ : syracuseStep 798545 = 598909) B598909
theorem B601987 : Blo 471786 601987 := bstep (se 1 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 601987 = 902981) B902981
theorem B798673 : Blo 471786 798673 := bstep (se 2 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 798673 = 599005) B599005
theorem B602083 : Blo 471786 602083 := bstep (se 1 (by rfl) ⟨451562, by rfl⟩ : syracuseStep 602083 = 903125) B903125
theorem B3026929 : Blo 471786 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B798707 : Blo 471786 798707 := bstep (se 1 (by rfl) ⟨599030, by rfl⟩ : syracuseStep 798707 = 1198061) B1198061
theorem B798835 : Blo 471786 798835 := bstep (se 1 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 798835 = 1198253) B1198253
theorem B569539 : Blo 471786 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B798977 : Blo 471786 798977 := bstep (se 2 (by rfl) ⟨299616, by rfl⟩ : syracuseStep 798977 = 599233) B599233
theorem B799105 : Blo 471786 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B799139 : Blo 471786 799139 := bstep (se 1 (by rfl) ⟨599354, by rfl⟩ : syracuseStep 799139 = 1198709) B1198709
theorem B897475 : Blo 471786 897475 := bstep (se 1 (by rfl) ⟨673106, by rfl⟩ : syracuseStep 897475 = 1346213) B1346213
theorem B13152709 : Blo 471786 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B799267 : Blo 471786 799267 := bstep (se 1 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 799267 = 1198901) B1198901
theorem B897635 : Blo 471786 897635 := bstep (se 1 (by rfl) ⟨673226, by rfl⟩ : syracuseStep 897635 = 1346453) B1346453
theorem B799409 : Blo 471786 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B1061585 : Blo 471786 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B1061603 : Blo 471786 1061603 := bstep (se 1 (by rfl) ⟨796202, by rfl⟩ : syracuseStep 1061603 = 1592405) B1592405
theorem B471795 : Blo 471786 471795 := bstep (se 1 (by rfl) ⟨353846, by rfl⟩ : syracuseStep 471795 = 707693) B707693
theorem B471811 : Blo 471786 471811 := bstep (se 1 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 471811 = 707717) B707717
theorem B471827 : Blo 471786 471827 := bstep (se 1 (by rfl) ⟨353870, by rfl⟩ : syracuseStep 471827 = 707741) B707741
theorem B471843 : Blo 471786 471843 := bstep (se 1 (by rfl) ⟨353882, by rfl⟩ : syracuseStep 471843 = 707765) B707765
theorem B799537 : Blo 471786 799537 := bstep (se 2 (by rfl) ⟨299826, by rfl⟩ : syracuseStep 799537 = 599653) B599653
theorem B471859 : Blo 471786 471859 := bstep (se 1 (by rfl) ⟨353894, by rfl⟩ : syracuseStep 471859 = 707789) B707789
theorem B471875 : Blo 471786 471875 := bstep (se 1 (by rfl) ⟨353906, by rfl⟩ : syracuseStep 471875 = 707813) B707813
theorem B1520461 : Blo 471786 1520461 := bstep (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) B570173
theorem B471891 : Blo 471786 471891 := bstep (se 1 (by rfl) ⟨353918, by rfl⟩ : syracuseStep 471891 = 707837) B707837
theorem B799571 : Blo 471786 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B471907 : Blo 471786 471907 := bstep (se 1 (by rfl) ⟨353930, by rfl⟩ : syracuseStep 471907 = 707861) B707861
theorem B471923 : Blo 471786 471923 := bstep (se 1 (by rfl) ⟨353942, by rfl⟩ : syracuseStep 471923 = 707885) B707885
theorem B471939 : Blo 471786 471939 := bstep (se 1 (by rfl) ⟨353954, by rfl⟩ : syracuseStep 471939 = 707909) B707909
theorem B471955 : Blo 471786 471955 := bstep (se 1 (by rfl) ⟨353966, by rfl⟩ : syracuseStep 471955 = 707933) B707933
theorem B471971 : Blo 471786 471971 := bstep (se 1 (by rfl) ⟨353978, by rfl⟩ : syracuseStep 471971 = 707957) B707957
theorem B471987 : Blo 471786 471987 := bstep (se 1 (by rfl) ⟨353990, by rfl⟩ : syracuseStep 471987 = 707981) B707981
theorem B472003 : Blo 471786 472003 := bstep (se 1 (by rfl) ⟨354002, by rfl⟩ : syracuseStep 472003 = 708005) B708005
theorem B472019 : Blo 471786 472019 := bstep (se 1 (by rfl) ⟨354014, by rfl⟩ : syracuseStep 472019 = 708029) B708029
theorem B799699 : Blo 471786 799699 := bstep (se 1 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 799699 = 1199549) B1199549
theorem B472035 : Blo 471786 472035 := bstep (se 1 (by rfl) ⟨354026, by rfl⟩ : syracuseStep 472035 = 708053) B708053
theorem B1061873 : Blo 471786 1061873 := bstep (se 2 (by rfl) ⟨398202, by rfl⟩ : syracuseStep 1061873 = 796405) B796405
theorem B472051 : Blo 471786 472051 := bstep (se 1 (by rfl) ⟨354038, by rfl⟩ : syracuseStep 472051 = 708077) B708077
theorem B1061891 : Blo 471786 1061891 := bstep (se 1 (by rfl) ⟨796418, by rfl⟩ : syracuseStep 1061891 = 1592837) B1592837
theorem B472067 : Blo 471786 472067 := bstep (se 1 (by rfl) ⟨354050, by rfl⟩ : syracuseStep 472067 = 708101) B708101
theorem B472083 : Blo 471786 472083 := bstep (se 1 (by rfl) ⟨354062, by rfl⟩ : syracuseStep 472083 = 708125) B708125
theorem B472099 : Blo 471786 472099 := bstep (se 1 (by rfl) ⟨354074, by rfl⟩ : syracuseStep 472099 = 708149) B708149
theorem B832547 : Blo 471786 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B472115 : Blo 471786 472115 := bstep (se 1 (by rfl) ⟨354086, by rfl⟩ : syracuseStep 472115 = 708173) B708173
theorem B472131 : Blo 471786 472131 := bstep (se 1 (by rfl) ⟨354098, by rfl⟩ : syracuseStep 472131 = 708197) B708197
theorem B472147 : Blo 471786 472147 := bstep (se 1 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 472147 = 708221) B708221
theorem B799841 : Blo 471786 799841 := bstep (se 2 (by rfl) ⟨299940, by rfl⟩ : syracuseStep 799841 = 599881) B599881
theorem B472163 : Blo 471786 472163 := bstep (se 1 (by rfl) ⟨354122, by rfl⟩ : syracuseStep 472163 = 708245) B708245
theorem B472179 : Blo 471786 472179 := bstep (se 1 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 472179 = 708269) B708269
theorem B472195 : Blo 471786 472195 := bstep (se 1 (by rfl) ⟨354146, by rfl⟩ : syracuseStep 472195 = 708293) B708293
theorem B472211 : Blo 471786 472211 := bstep (se 1 (by rfl) ⟨354158, by rfl⟩ : syracuseStep 472211 = 708317) B708317
theorem B472227 : Blo 471786 472227 := bstep (se 1 (by rfl) ⟨354170, by rfl⟩ : syracuseStep 472227 = 708341) B708341
theorem B472243 : Blo 471786 472243 := bstep (se 1 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 472243 = 708365) B708365
theorem B472259 : Blo 471786 472259 := bstep (se 1 (by rfl) ⟨354194, by rfl⟩ : syracuseStep 472259 = 708389) B708389
theorem B3585221 : Blo 471786 3585221 := bstep (se 4 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 3585221 = 672229) B672229
theorem B472275 : Blo 471786 472275 := bstep (se 1 (by rfl) ⟨354206, by rfl⟩ : syracuseStep 472275 = 708413) B708413
theorem B799969 : Blo 471786 799969 := bstep (se 2 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 799969 = 599977) B599977
theorem B472291 : Blo 471786 472291 := bstep (se 1 (by rfl) ⟨354218, by rfl⟩ : syracuseStep 472291 = 708437) B708437
theorem B472307 : Blo 471786 472307 := bstep (se 1 (by rfl) ⟨354230, by rfl⟩ : syracuseStep 472307 = 708461) B708461
theorem B570611 : Blo 471786 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B472323 : Blo 471786 472323 := bstep (se 1 (by rfl) ⟨354242, by rfl⟩ : syracuseStep 472323 = 708485) B708485
theorem B800003 : Blo 471786 800003 := bstep (se 1 (by rfl) ⟨600002, by rfl⟩ : syracuseStep 800003 = 1200005) B1200005
theorem B1062161 : Blo 471786 1062161 := bstep (se 2 (by rfl) ⟨398310, by rfl⟩ : syracuseStep 1062161 = 796621) B796621
theorem B472339 : Blo 471786 472339 := bstep (se 1 (by rfl) ⟨354254, by rfl⟩ : syracuseStep 472339 = 708509) B708509
theorem B1062179 : Blo 471786 1062179 := bstep (se 1 (by rfl) ⟨796634, by rfl⟩ : syracuseStep 1062179 = 1593269) B1593269
theorem B472355 : Blo 471786 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B472371 : Blo 471786 472371 := bstep (se 1 (by rfl) ⟨354278, by rfl⟩ : syracuseStep 472371 = 708557) B708557
theorem B472387 : Blo 471786 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B472403 : Blo 471786 472403 := bstep (se 1 (by rfl) ⟨354302, by rfl⟩ : syracuseStep 472403 = 708605) B708605
theorem B472419 : Blo 471786 472419 := bstep (se 1 (by rfl) ⟨354314, by rfl⟩ : syracuseStep 472419 = 708629) B708629
theorem B472435 : Blo 471786 472435 := bstep (se 1 (by rfl) ⟨354326, by rfl⟩ : syracuseStep 472435 = 708653) B708653
theorem B472451 : Blo 471786 472451 := bstep (se 1 (by rfl) ⟨354338, by rfl⟩ : syracuseStep 472451 = 708677) B708677
theorem B800131 : Blo 471786 800131 := bstep (se 1 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 800131 = 1200197) B1200197
theorem B472467 : Blo 471786 472467 := bstep (se 1 (by rfl) ⟨354350, by rfl⟩ : syracuseStep 472467 = 708701) B708701
theorem B472483 : Blo 471786 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B472499 : Blo 471786 472499 := bstep (se 1 (by rfl) ⟨354374, by rfl⟩ : syracuseStep 472499 = 708749) B708749
theorem B472515 : Blo 471786 472515 := bstep (se 1 (by rfl) ⟨354386, by rfl⟩ : syracuseStep 472515 = 708773) B708773
theorem B472531 : Blo 471786 472531 := bstep (se 1 (by rfl) ⟨354398, by rfl⟩ : syracuseStep 472531 = 708797) B708797
theorem B472547 : Blo 471786 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B472563 : Blo 471786 472563 := bstep (se 1 (by rfl) ⟨354422, by rfl⟩ : syracuseStep 472563 = 708845) B708845
theorem B472579 : Blo 471786 472579 := bstep (se 1 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 472579 = 708869) B708869
theorem B800273 : Blo 471786 800273 := bstep (se 2 (by rfl) ⟨300102, by rfl⟩ : syracuseStep 800273 = 600205) B600205
theorem B472595 : Blo 471786 472595 := bstep (se 1 (by rfl) ⟨354446, by rfl⟩ : syracuseStep 472595 = 708893) B708893
theorem B472611 : Blo 471786 472611 := bstep (se 1 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 472611 = 708917) B708917
theorem B1062449 : Blo 471786 1062449 := bstep (se 2 (by rfl) ⟨398418, by rfl⟩ : syracuseStep 1062449 = 796837) B796837
theorem B472627 : Blo 471786 472627 := bstep (se 1 (by rfl) ⟨354470, by rfl⟩ : syracuseStep 472627 = 708941) B708941
theorem B1062467 : Blo 471786 1062467 := bstep (se 1 (by rfl) ⟨796850, by rfl⟩ : syracuseStep 1062467 = 1593701) B1593701
theorem B472643 : Blo 471786 472643 := bstep (se 1 (by rfl) ⟨354482, by rfl⟩ : syracuseStep 472643 = 708965) B708965
theorem B472659 : Blo 471786 472659 := bstep (se 1 (by rfl) ⟨354494, by rfl⟩ : syracuseStep 472659 = 708989) B708989
theorem B472675 : Blo 471786 472675 := bstep (se 1 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 472675 = 709013) B709013
theorem B1390189 : Blo 471786 1390189 := bstep (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) B521321
theorem B472691 : Blo 471786 472691 := bstep (se 1 (by rfl) ⟨354518, by rfl⟩ : syracuseStep 472691 = 709037) B709037
theorem B472707 : Blo 471786 472707 := bstep (se 1 (by rfl) ⟨354530, by rfl⟩ : syracuseStep 472707 = 709061) B709061
theorem B898705 : Blo 471786 898705 := bstep (se 2 (by rfl) ⟨337014, by rfl⟩ : syracuseStep 898705 = 674029) B674029
theorem B800401 : Blo 471786 800401 := bstep (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) B600301
theorem B472723 : Blo 471786 472723 := bstep (se 1 (by rfl) ⟨354542, by rfl⟩ : syracuseStep 472723 = 709085) B709085
theorem B472739 : Blo 471786 472739 := bstep (se 1 (by rfl) ⟨354554, by rfl⟩ : syracuseStep 472739 = 709109) B709109
theorem B472755 : Blo 471786 472755 := bstep (se 1 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 472755 = 709133) B709133
theorem B800435 : Blo 471786 800435 := bstep (se 1 (by rfl) ⟨600326, by rfl⟩ : syracuseStep 800435 = 1200653) B1200653
theorem B472771 : Blo 471786 472771 := bstep (se 1 (by rfl) ⟨354578, by rfl⟩ : syracuseStep 472771 = 709157) B709157
theorem B472787 : Blo 471786 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B472803 : Blo 471786 472803 := bstep (se 1 (by rfl) ⟨354602, by rfl⟩ : syracuseStep 472803 = 709205) B709205
theorem B472819 : Blo 471786 472819 := bstep (se 1 (by rfl) ⟨354614, by rfl⟩ : syracuseStep 472819 = 709229) B709229
theorem B472835 : Blo 471786 472835 := bstep (se 1 (by rfl) ⟨354626, by rfl⟩ : syracuseStep 472835 = 709253) B709253
theorem B472851 : Blo 471786 472851 := bstep (se 1 (by rfl) ⟨354638, by rfl⟩ : syracuseStep 472851 = 709277) B709277
theorem B27997973 : Blo 471786 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B472867 : Blo 471786 472867 := bstep (se 1 (by rfl) ⟨354650, by rfl⟩ : syracuseStep 472867 = 709301) B709301
theorem B472883 : Blo 471786 472883 := bstep (se 1 (by rfl) ⟨354662, by rfl⟩ : syracuseStep 472883 = 709325) B709325
theorem B800563 : Blo 471786 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B472899 : Blo 471786 472899 := bstep (se 1 (by rfl) ⟨354674, by rfl⟩ : syracuseStep 472899 = 709349) B709349
theorem B1062737 : Blo 471786 1062737 := bstep (se 2 (by rfl) ⟨398526, by rfl⟩ : syracuseStep 1062737 = 797053) B797053
theorem B472915 : Blo 471786 472915 := bstep (se 1 (by rfl) ⟨354686, by rfl⟩ : syracuseStep 472915 = 709373) B709373
theorem B1062755 : Blo 471786 1062755 := bstep (se 1 (by rfl) ⟨797066, by rfl⟩ : syracuseStep 1062755 = 1594133) B1594133
theorem B472931 : Blo 471786 472931 := bstep (se 1 (by rfl) ⟨354698, by rfl⟩ : syracuseStep 472931 = 709397) B709397
theorem B472947 : Blo 471786 472947 := bstep (se 1 (by rfl) ⟨354710, by rfl⟩ : syracuseStep 472947 = 709421) B709421
theorem B472963 : Blo 471786 472963 := bstep (se 1 (by rfl) ⟨354722, by rfl⟩ : syracuseStep 472963 = 709445) B709445
theorem B472979 : Blo 471786 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B472995 : Blo 471786 472995 := bstep (se 1 (by rfl) ⟨354746, by rfl⟩ : syracuseStep 472995 = 709493) B709493
theorem B473011 : Blo 471786 473011 := bstep (se 1 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 473011 = 709517) B709517
theorem B800705 : Blo 471786 800705 := bstep (se 2 (by rfl) ⟨300264, by rfl⟩ : syracuseStep 800705 = 600529) B600529
theorem B473027 : Blo 471786 473027 := bstep (se 1 (by rfl) ⟨354770, by rfl⟩ : syracuseStep 473027 = 709541) B709541
theorem B473043 : Blo 471786 473043 := bstep (se 1 (by rfl) ⟨354782, by rfl⟩ : syracuseStep 473043 = 709565) B709565
theorem B473059 : Blo 471786 473059 := bstep (se 1 (by rfl) ⟨354794, by rfl⟩ : syracuseStep 473059 = 709589) B709589
theorem B473075 : Blo 471786 473075 := bstep (se 1 (by rfl) ⟨354806, by rfl⟩ : syracuseStep 473075 = 709613) B709613
theorem B473091 : Blo 471786 473091 := bstep (se 1 (by rfl) ⟨354818, by rfl⟩ : syracuseStep 473091 = 709637) B709637
theorem B473107 : Blo 471786 473107 := bstep (se 1 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 473107 = 709661) B709661
theorem B473123 : Blo 471786 473123 := bstep (se 1 (by rfl) ⟨354842, by rfl⟩ : syracuseStep 473123 = 709685) B709685
theorem B473139 : Blo 471786 473139 := bstep (se 1 (by rfl) ⟨354854, by rfl⟩ : syracuseStep 473139 = 709709) B709709
theorem B800833 : Blo 471786 800833 := bstep (se 2 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 800833 = 600625) B600625
theorem B473155 : Blo 471786 473155 := bstep (se 1 (by rfl) ⟨354866, by rfl⟩ : syracuseStep 473155 = 709733) B709733
theorem B3881029 : Blo 471786 3881029 := bstep (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) B727693
theorem B473171 : Blo 471786 473171 := bstep (se 1 (by rfl) ⟨354878, by rfl⟩ : syracuseStep 473171 = 709757) B709757
theorem B473187 : Blo 471786 473187 := bstep (se 1 (by rfl) ⟨354890, by rfl⟩ : syracuseStep 473187 = 709781) B709781
theorem B800867 : Blo 471786 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B1063025 : Blo 471786 1063025 := bstep (se 2 (by rfl) ⟨398634, by rfl⟩ : syracuseStep 1063025 = 797269) B797269
theorem B473203 : Blo 471786 473203 := bstep (se 1 (by rfl) ⟨354902, by rfl⟩ : syracuseStep 473203 = 709805) B709805
theorem B1063043 : Blo 471786 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B473219 : Blo 471786 473219 := bstep (se 1 (by rfl) ⟨354914, by rfl⟩ : syracuseStep 473219 = 709829) B709829
theorem B473235 : Blo 471786 473235 := bstep (se 1 (by rfl) ⟨354926, by rfl⟩ : syracuseStep 473235 = 709853) B709853
theorem B473251 : Blo 471786 473251 := bstep (se 1 (by rfl) ⟨354938, by rfl⟩ : syracuseStep 473251 = 709877) B709877
theorem B473267 : Blo 471786 473267 := bstep (se 1 (by rfl) ⟨354950, by rfl⟩ : syracuseStep 473267 = 709901) B709901
theorem B473283 : Blo 471786 473283 := bstep (se 1 (by rfl) ⟨354962, by rfl⟩ : syracuseStep 473283 = 709925) B709925
theorem B473299 : Blo 471786 473299 := bstep (se 1 (by rfl) ⟨354974, by rfl⟩ : syracuseStep 473299 = 709949) B709949
theorem B473315 : Blo 471786 473315 := bstep (se 1 (by rfl) ⟨354986, by rfl⟩ : syracuseStep 473315 = 709973) B709973
theorem B800995 : Blo 471786 800995 := bstep (se 1 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 800995 = 1201493) B1201493
theorem B473331 : Blo 471786 473331 := bstep (se 1 (by rfl) ⟨354998, by rfl⟩ : syracuseStep 473331 = 709997) B709997
theorem B473347 : Blo 471786 473347 := bstep (se 1 (by rfl) ⟨355010, by rfl⟩ : syracuseStep 473347 = 710021) B710021
theorem B473363 : Blo 471786 473363 := bstep (se 1 (by rfl) ⟨355022, by rfl⟩ : syracuseStep 473363 = 710045) B710045
theorem B473379 : Blo 471786 473379 := bstep (se 1 (by rfl) ⟨355034, by rfl⟩ : syracuseStep 473379 = 710069) B710069
theorem B473395 : Blo 471786 473395 := bstep (se 1 (by rfl) ⟨355046, by rfl⟩ : syracuseStep 473395 = 710093) B710093
theorem B473411 : Blo 471786 473411 := bstep (se 1 (by rfl) ⟨355058, by rfl⟩ : syracuseStep 473411 = 710117) B710117
theorem B473427 : Blo 471786 473427 := bstep (se 1 (by rfl) ⟨355070, by rfl⟩ : syracuseStep 473427 = 710141) B710141
theorem B473443 : Blo 471786 473443 := bstep (se 1 (by rfl) ⟨355082, by rfl⟩ : syracuseStep 473443 = 710165) B710165
theorem B801137 : Blo 471786 801137 := bstep (se 2 (by rfl) ⟨300426, by rfl⟩ : syracuseStep 801137 = 600853) B600853
theorem B473459 : Blo 471786 473459 := bstep (se 1 (by rfl) ⟨355094, by rfl⟩ : syracuseStep 473459 = 710189) B710189
theorem B473475 : Blo 471786 473475 := bstep (se 1 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 473475 = 710213) B710213
theorem B1194385 : Blo 471786 1194385 := bstep (se 2 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 1194385 = 895789) B895789
theorem B1063313 : Blo 471786 1063313 := bstep (se 2 (by rfl) ⟨398742, by rfl⟩ : syracuseStep 1063313 = 797485) B797485
theorem B473491 : Blo 471786 473491 := bstep (se 1 (by rfl) ⟨355118, by rfl⟩ : syracuseStep 473491 = 710237) B710237
theorem B1063331 : Blo 471786 1063331 := bstep (se 1 (by rfl) ⟨797498, by rfl⟩ : syracuseStep 1063331 = 1594997) B1594997
theorem B473507 : Blo 471786 473507 := bstep (se 1 (by rfl) ⟨355130, by rfl⟩ : syracuseStep 473507 = 710261) B710261
theorem B2406833 : Blo 471786 2406833 := bstep (se 2 (by rfl) ⟨902562, by rfl⟩ : syracuseStep 2406833 = 1805125) B1805125
theorem B473523 : Blo 471786 473523 := bstep (se 1 (by rfl) ⟨355142, by rfl⟩ : syracuseStep 473523 = 710285) B710285
theorem B473539 : Blo 471786 473539 := bstep (se 1 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 473539 = 710309) B710309
theorem B473555 : Blo 471786 473555 := bstep (se 1 (by rfl) ⟨355166, by rfl⟩ : syracuseStep 473555 = 710333) B710333
theorem B473571 : Blo 471786 473571 := bstep (se 1 (by rfl) ⟨355178, by rfl⟩ : syracuseStep 473571 = 710357) B710357
theorem B801265 : Blo 471786 801265 := bstep (se 2 (by rfl) ⟨300474, by rfl⟩ : syracuseStep 801265 = 600949) B600949
theorem B473587 : Blo 471786 473587 := bstep (se 1 (by rfl) ⟨355190, by rfl⟩ : syracuseStep 473587 = 710381) B710381
theorem B473603 : Blo 471786 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B473619 : Blo 471786 473619 := bstep (se 1 (by rfl) ⟨355214, by rfl⟩ : syracuseStep 473619 = 710429) B710429
theorem B801299 : Blo 471786 801299 := bstep (se 1 (by rfl) ⟨600974, by rfl⟩ : syracuseStep 801299 = 1201949) B1201949
theorem B473635 : Blo 471786 473635 := bstep (se 1 (by rfl) ⟨355226, by rfl⟩ : syracuseStep 473635 = 710453) B710453
theorem B473651 : Blo 471786 473651 := bstep (se 1 (by rfl) ⟨355238, by rfl⟩ : syracuseStep 473651 = 710477) B710477
theorem B473667 : Blo 471786 473667 := bstep (se 1 (by rfl) ⟨355250, by rfl⟩ : syracuseStep 473667 = 710501) B710501
theorem B1522243 : Blo 471786 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B473683 : Blo 471786 473683 := bstep (se 1 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 473683 = 710525) B710525
theorem B473699 : Blo 471786 473699 := bstep (se 1 (by rfl) ⟨355274, by rfl⟩ : syracuseStep 473699 = 710549) B710549
theorem B473715 : Blo 471786 473715 := bstep (se 1 (by rfl) ⟨355286, by rfl⟩ : syracuseStep 473715 = 710573) B710573
theorem B473731 : Blo 471786 473731 := bstep (se 1 (by rfl) ⟨355298, by rfl⟩ : syracuseStep 473731 = 710597) B710597
theorem B1522307 : Blo 471786 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B473747 : Blo 471786 473747 := bstep (se 1 (by rfl) ⟨355310, by rfl⟩ : syracuseStep 473747 = 710621) B710621
theorem B801427 : Blo 471786 801427 := bstep (se 1 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 801427 = 1202141) B1202141
theorem B1194659 : Blo 471786 1194659 := bstep (se 1 (by rfl) ⟨895994, by rfl⟩ : syracuseStep 1194659 = 1791989) B1791989
theorem B473763 : Blo 471786 473763 := bstep (se 1 (by rfl) ⟨355322, by rfl⟩ : syracuseStep 473763 = 710645) B710645
theorem B1063601 : Blo 471786 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B899761 : Blo 471786 899761 := bstep (se 2 (by rfl) ⟨337410, by rfl⟩ : syracuseStep 899761 = 674821) B674821
theorem B473779 : Blo 471786 473779 := bstep (se 1 (by rfl) ⟨355334, by rfl⟩ : syracuseStep 473779 = 710669) B710669
theorem B1063619 : Blo 471786 1063619 := bstep (se 1 (by rfl) ⟨797714, by rfl⟩ : syracuseStep 1063619 = 1595429) B1595429
theorem B473795 : Blo 471786 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B1522385 : Blo 471786 1522385 := bstep (se 2 (by rfl) ⟨570894, by rfl⟩ : syracuseStep 1522385 = 1141789) B1141789
theorem B473811 : Blo 471786 473811 := bstep (se 1 (by rfl) ⟨355358, by rfl⟩ : syracuseStep 473811 = 710717) B710717
theorem B473827 : Blo 471786 473827 := bstep (se 1 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 473827 = 710741) B710741
theorem B473843 : Blo 471786 473843 := bstep (se 1 (by rfl) ⟨355382, by rfl⟩ : syracuseStep 473843 = 710765) B710765
theorem B637699 : Blo 471786 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B473859 : Blo 471786 473859 := bstep (se 1 (by rfl) ⟨355394, by rfl⟩ : syracuseStep 473859 = 710789) B710789
theorem B473875 : Blo 471786 473875 := bstep (se 1 (by rfl) ⟨355406, by rfl⟩ : syracuseStep 473875 = 710813) B710813
theorem B801569 : Blo 471786 801569 := bstep (se 2 (by rfl) ⟨300588, by rfl⟩ : syracuseStep 801569 = 601177) B601177
theorem B473891 : Blo 471786 473891 := bstep (se 1 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 473891 = 710837) B710837
theorem B473907 : Blo 471786 473907 := bstep (se 1 (by rfl) ⟨355430, by rfl⟩ : syracuseStep 473907 = 710861) B710861
theorem B473923 : Blo 471786 473923 := bstep (se 1 (by rfl) ⟨355442, by rfl⟩ : syracuseStep 473923 = 710885) B710885
theorem B3849029 : Blo 471786 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B473939 : Blo 471786 473939 := bstep (se 1 (by rfl) ⟨355454, by rfl⟩ : syracuseStep 473939 = 710909) B710909
theorem B1194851 : Blo 471786 1194851 := bstep (se 1 (by rfl) ⟨896138, by rfl⟩ : syracuseStep 1194851 = 1792277) B1792277
theorem B473955 : Blo 471786 473955 := bstep (se 1 (by rfl) ⟨355466, by rfl⟩ : syracuseStep 473955 = 710933) B710933
theorem B3849059 : Blo 471786 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B473971 : Blo 471786 473971 := bstep (se 1 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 473971 = 710957) B710957
theorem B473987 : Blo 471786 473987 := bstep (se 1 (by rfl) ⟨355490, by rfl⟩ : syracuseStep 473987 = 710981) B710981
theorem B474003 : Blo 471786 474003 := bstep (se 1 (by rfl) ⟨355502, by rfl⟩ : syracuseStep 474003 = 711005) B711005
theorem B801697 : Blo 471786 801697 := bstep (se 2 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 801697 = 601273) B601273
theorem B474019 : Blo 471786 474019 := bstep (se 1 (by rfl) ⟨355514, by rfl⟩ : syracuseStep 474019 = 711029) B711029
theorem B474035 : Blo 471786 474035 := bstep (se 1 (by rfl) ⟨355526, by rfl⟩ : syracuseStep 474035 = 711053) B711053
theorem B474051 : Blo 471786 474051 := bstep (se 1 (by rfl) ⟨355538, by rfl⟩ : syracuseStep 474051 = 711077) B711077
theorem B801731 : Blo 471786 801731 := bstep (se 1 (by rfl) ⟨601298, by rfl⟩ : syracuseStep 801731 = 1202597) B1202597
theorem B1063889 : Blo 471786 1063889 := bstep (se 2 (by rfl) ⟨398958, by rfl⟩ : syracuseStep 1063889 = 797917) B797917
theorem B474067 : Blo 471786 474067 := bstep (se 1 (by rfl) ⟨355550, by rfl⟩ : syracuseStep 474067 = 711101) B711101
theorem B1063907 : Blo 471786 1063907 := bstep (se 1 (by rfl) ⟨797930, by rfl⟩ : syracuseStep 1063907 = 1595861) B1595861
theorem B474083 : Blo 471786 474083 := bstep (se 1 (by rfl) ⟨355562, by rfl⟩ : syracuseStep 474083 = 711125) B711125
theorem B474099 : Blo 471786 474099 := bstep (se 1 (by rfl) ⟨355574, by rfl⟩ : syracuseStep 474099 = 711149) B711149
theorem B474115 : Blo 471786 474115 := bstep (se 1 (by rfl) ⟨355586, by rfl⟩ : syracuseStep 474115 = 711173) B711173
theorem B474131 : Blo 471786 474131 := bstep (se 1 (by rfl) ⟨355598, by rfl⟩ : syracuseStep 474131 = 711197) B711197
theorem B2276387 : Blo 471786 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B474147 : Blo 471786 474147 := bstep (se 1 (by rfl) ⟨355610, by rfl⟩ : syracuseStep 474147 = 711221) B711221
theorem B474163 : Blo 471786 474163 := bstep (se 1 (by rfl) ⟨355622, by rfl⟩ : syracuseStep 474163 = 711245) B711245
theorem B900163 : Blo 471786 900163 := bstep (se 1 (by rfl) ⟨675122, by rfl⟩ : syracuseStep 900163 = 1350245) B1350245
theorem B474179 : Blo 471786 474179 := bstep (se 1 (by rfl) ⟨355634, by rfl⟩ : syracuseStep 474179 = 711269) B711269
theorem B801859 : Blo 471786 801859 := bstep (se 1 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 801859 = 1202789) B1202789
theorem B474195 : Blo 471786 474195 := bstep (se 1 (by rfl) ⟨355646, by rfl⟩ : syracuseStep 474195 = 711293) B711293
theorem B474211 : Blo 471786 474211 := bstep (se 1 (by rfl) ⟨355658, by rfl⟩ : syracuseStep 474211 = 711317) B711317
theorem B900209 : Blo 471786 900209 := bstep (se 2 (by rfl) ⟨337578, by rfl⟩ : syracuseStep 900209 = 675157) B675157
theorem B474227 : Blo 471786 474227 := bstep (se 1 (by rfl) ⟨355670, by rfl⟩ : syracuseStep 474227 = 711341) B711341
theorem B474243 : Blo 471786 474243 := bstep (se 1 (by rfl) ⟨355682, by rfl⟩ : syracuseStep 474243 = 711365) B711365
theorem B474259 : Blo 471786 474259 := bstep (se 1 (by rfl) ⟨355694, by rfl⟩ : syracuseStep 474259 = 711389) B711389
theorem B474275 : Blo 471786 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B2047153 : Blo 471786 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B474291 : Blo 471786 474291 := bstep (se 1 (by rfl) ⟨355718, by rfl⟩ : syracuseStep 474291 = 711437) B711437
theorem B474307 : Blo 471786 474307 := bstep (se 1 (by rfl) ⟨355730, by rfl⟩ : syracuseStep 474307 = 711461) B711461
theorem B802001 : Blo 471786 802001 := bstep (se 2 (by rfl) ⟨300750, by rfl⟩ : syracuseStep 802001 = 601501) B601501
theorem B474323 : Blo 471786 474323 := bstep (se 1 (by rfl) ⟨355742, by rfl⟩ : syracuseStep 474323 = 711485) B711485
theorem B474339 : Blo 471786 474339 := bstep (se 1 (by rfl) ⟨355754, by rfl⟩ : syracuseStep 474339 = 711509) B711509
theorem B507107 : Blo 471786 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B1064177 : Blo 471786 1064177 := bstep (se 2 (by rfl) ⟨399066, by rfl⟩ : syracuseStep 1064177 = 798133) B798133
theorem B474355 : Blo 471786 474355 := bstep (se 1 (by rfl) ⟨355766, by rfl⟩ : syracuseStep 474355 = 711533) B711533
theorem B1064195 : Blo 471786 1064195 := bstep (se 1 (by rfl) ⟨798146, by rfl⟩ : syracuseStep 1064195 = 1596293) B1596293
theorem B474371 : Blo 471786 474371 := bstep (se 1 (by rfl) ⟨355778, by rfl⟩ : syracuseStep 474371 = 711557) B711557
theorem B474387 : Blo 471786 474387 := bstep (se 1 (by rfl) ⟨355790, by rfl⟩ : syracuseStep 474387 = 711581) B711581
theorem B474403 : Blo 471786 474403 := bstep (se 1 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 474403 = 711605) B711605
theorem B2276657 : Blo 471786 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B474419 : Blo 471786 474419 := bstep (se 1 (by rfl) ⟨355814, by rfl⟩ : syracuseStep 474419 = 711629) B711629
theorem B474435 : Blo 471786 474435 := bstep (se 1 (by rfl) ⟨355826, by rfl⟩ : syracuseStep 474435 = 711653) B711653
theorem B802129 : Blo 471786 802129 := bstep (se 2 (by rfl) ⟨300798, by rfl⟩ : syracuseStep 802129 = 601597) B601597
theorem B474451 : Blo 471786 474451 := bstep (se 1 (by rfl) ⟨355838, by rfl⟩ : syracuseStep 474451 = 711677) B711677
theorem B474467 : Blo 471786 474467 := bstep (se 1 (by rfl) ⟨355850, by rfl⟩ : syracuseStep 474467 = 711701) B711701
theorem B474483 : Blo 471786 474483 := bstep (se 1 (by rfl) ⟨355862, by rfl⟩ : syracuseStep 474483 = 711725) B711725
theorem B802163 : Blo 471786 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B474499 : Blo 471786 474499 := bstep (se 1 (by rfl) ⟨355874, by rfl⟩ : syracuseStep 474499 = 711749) B711749
theorem B900497 : Blo 471786 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B474515 : Blo 471786 474515 := bstep (se 1 (by rfl) ⟨355886, by rfl⟩ : syracuseStep 474515 = 711773) B711773
theorem B474531 : Blo 471786 474531 := bstep (se 1 (by rfl) ⟨355898, by rfl⟩ : syracuseStep 474531 = 711797) B711797
theorem B474547 : Blo 471786 474547 := bstep (se 1 (by rfl) ⟨355910, by rfl⟩ : syracuseStep 474547 = 711821) B711821
theorem B474563 : Blo 471786 474563 := bstep (se 1 (by rfl) ⟨355922, by rfl⟩ : syracuseStep 474563 = 711845) B711845
theorem B474579 : Blo 471786 474579 := bstep (se 1 (by rfl) ⟨355934, by rfl⟩ : syracuseStep 474579 = 711869) B711869
theorem B474595 : Blo 471786 474595 := bstep (se 1 (by rfl) ⟨355946, by rfl⟩ : syracuseStep 474595 = 711893) B711893
theorem B2276849 : Blo 471786 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B474611 : Blo 471786 474611 := bstep (se 1 (by rfl) ⟨355958, by rfl⟩ : syracuseStep 474611 = 711917) B711917
theorem B802291 : Blo 471786 802291 := bstep (se 1 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 802291 = 1203437) B1203437
theorem B474627 : Blo 471786 474627 := bstep (se 1 (by rfl) ⟨355970, by rfl⟩ : syracuseStep 474627 = 711941) B711941
theorem B1064465 : Blo 471786 1064465 := bstep (se 2 (by rfl) ⟨399174, by rfl⟩ : syracuseStep 1064465 = 798349) B798349
theorem B474643 : Blo 471786 474643 := bstep (se 1 (by rfl) ⟨355982, by rfl⟩ : syracuseStep 474643 = 711965) B711965
theorem B1064483 : Blo 471786 1064483 := bstep (se 1 (by rfl) ⟨798362, by rfl⟩ : syracuseStep 1064483 = 1596725) B1596725
theorem B474659 : Blo 471786 474659 := bstep (se 1 (by rfl) ⟨355994, by rfl⟩ : syracuseStep 474659 = 711989) B711989
theorem B474675 : Blo 471786 474675 := bstep (se 1 (by rfl) ⟨356006, by rfl⟩ : syracuseStep 474675 = 712013) B712013
theorem B474691 : Blo 471786 474691 := bstep (se 1 (by rfl) ⟨356018, by rfl⟩ : syracuseStep 474691 = 712037) B712037
theorem B474707 : Blo 471786 474707 := bstep (se 1 (by rfl) ⟨356030, by rfl⟩ : syracuseStep 474707 = 712061) B712061
theorem B474723 : Blo 471786 474723 := bstep (se 1 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 474723 = 712085) B712085
theorem B474739 : Blo 471786 474739 := bstep (se 1 (by rfl) ⟨356054, by rfl⟩ : syracuseStep 474739 = 712109) B712109
theorem B802433 : Blo 471786 802433 := bstep (se 2 (by rfl) ⟨300912, by rfl⟩ : syracuseStep 802433 = 601825) B601825
theorem B474755 : Blo 471786 474755 := bstep (se 1 (by rfl) ⟨356066, by rfl⟩ : syracuseStep 474755 = 712133) B712133
theorem B474771 : Blo 471786 474771 := bstep (se 1 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 474771 = 712157) B712157
theorem B474787 : Blo 471786 474787 := bstep (se 1 (by rfl) ⟨356090, by rfl⟩ : syracuseStep 474787 = 712181) B712181
theorem B474803 : Blo 471786 474803 := bstep (se 1 (by rfl) ⟨356102, by rfl⟩ : syracuseStep 474803 = 712205) B712205
theorem B474819 : Blo 471786 474819 := bstep (se 1 (by rfl) ⟨356114, by rfl⟩ : syracuseStep 474819 = 712229) B712229
theorem B474835 : Blo 471786 474835 := bstep (se 1 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 474835 = 712253) B712253
theorem B474851 : Blo 471786 474851 := bstep (se 1 (by rfl) ⟨356138, by rfl⟩ : syracuseStep 474851 = 712277) B712277
theorem B474867 : Blo 471786 474867 := bstep (se 1 (by rfl) ⟨356150, by rfl⟩ : syracuseStep 474867 = 712301) B712301
theorem B802561 : Blo 471786 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B474883 : Blo 471786 474883 := bstep (se 1 (by rfl) ⟨356162, by rfl⟩ : syracuseStep 474883 = 712325) B712325
theorem B1195793 : Blo 471786 1195793 := bstep (se 2 (by rfl) ⟨448422, by rfl⟩ : syracuseStep 1195793 = 896845) B896845
theorem B474899 : Blo 471786 474899 := bstep (se 1 (by rfl) ⟨356174, by rfl⟩ : syracuseStep 474899 = 712349) B712349
theorem B474915 : Blo 471786 474915 := bstep (se 1 (by rfl) ⟨356186, by rfl⟩ : syracuseStep 474915 = 712373) B712373
theorem B802595 : Blo 471786 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B1064753 : Blo 471786 1064753 := bstep (se 2 (by rfl) ⟨399282, by rfl⟩ : syracuseStep 1064753 = 798565) B798565
theorem B474931 : Blo 471786 474931 := bstep (se 1 (by rfl) ⟨356198, by rfl⟩ : syracuseStep 474931 = 712397) B712397
theorem B1195843 : Blo 471786 1195843 := bstep (se 1 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 1195843 = 1793765) B1793765
theorem B1064771 : Blo 471786 1064771 := bstep (se 1 (by rfl) ⟨798578, by rfl⟩ : syracuseStep 1064771 = 1597157) B1597157
theorem B474947 : Blo 471786 474947 := bstep (se 1 (by rfl) ⟨356210, by rfl⟩ : syracuseStep 474947 = 712421) B712421
theorem B474963 : Blo 471786 474963 := bstep (se 1 (by rfl) ⟨356222, by rfl⟩ : syracuseStep 474963 = 712445) B712445
theorem B474979 : Blo 471786 474979 := bstep (se 1 (by rfl) ⟨356234, by rfl⟩ : syracuseStep 474979 = 712469) B712469
theorem B2408291 : Blo 471786 2408291 := bstep (se 1 (by rfl) ⟨1806218, by rfl⟩ : syracuseStep 2408291 = 3612437) B3612437
theorem B2277233 : Blo 471786 2277233 := bstep (se 2 (by rfl) ⟨853962, by rfl⟩ : syracuseStep 2277233 = 1707925) B1707925
theorem B474995 : Blo 471786 474995 := bstep (se 1 (by rfl) ⟨356246, by rfl⟩ : syracuseStep 474995 = 712493) B712493
theorem B475011 : Blo 471786 475011 := bstep (se 1 (by rfl) ⟨356258, by rfl⟩ : syracuseStep 475011 = 712517) B712517
theorem B475027 : Blo 471786 475027 := bstep (se 1 (by rfl) ⟨356270, by rfl⟩ : syracuseStep 475027 = 712541) B712541
theorem B475043 : Blo 471786 475043 := bstep (se 1 (by rfl) ⟨356282, by rfl⟩ : syracuseStep 475043 = 712565) B712565
theorem B802723 : Blo 471786 802723 := bstep (se 1 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 802723 = 1204085) B1204085
theorem B475059 : Blo 471786 475059 := bstep (se 1 (by rfl) ⟨356294, by rfl⟩ : syracuseStep 475059 = 712589) B712589
theorem B475075 : Blo 471786 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B1195985 : Blo 471786 1195985 := bstep (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) B896989
theorem B475091 : Blo 471786 475091 := bstep (se 1 (by rfl) ⟨356318, by rfl⟩ : syracuseStep 475091 = 712637) B712637
theorem B475107 : Blo 471786 475107 := bstep (se 1 (by rfl) ⟨356330, by rfl⟩ : syracuseStep 475107 = 712661) B712661
theorem B475123 : Blo 471786 475123 := bstep (se 1 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 475123 = 712685) B712685
theorem B475139 : Blo 471786 475139 := bstep (se 1 (by rfl) ⟨356354, by rfl⟩ : syracuseStep 475139 = 712709) B712709
theorem B475155 : Blo 471786 475155 := bstep (se 1 (by rfl) ⟨356366, by rfl⟩ : syracuseStep 475155 = 712733) B712733
theorem B475171 : Blo 471786 475171 := bstep (se 1 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 475171 = 712757) B712757
theorem B802865 : Blo 471786 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B475187 : Blo 471786 475187 := bstep (se 1 (by rfl) ⟨356390, by rfl⟩ : syracuseStep 475187 = 712781) B712781
theorem B475203 : Blo 471786 475203 := bstep (se 1 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 475203 = 712805) B712805
theorem B1065041 : Blo 471786 1065041 := bstep (se 2 (by rfl) ⟨399390, by rfl⟩ : syracuseStep 1065041 = 798781) B798781
theorem B475219 : Blo 471786 475219 := bstep (se 1 (by rfl) ⟨356414, by rfl⟩ : syracuseStep 475219 = 712829) B712829
theorem B1065059 : Blo 471786 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B6078563 : Blo 471786 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B901219 : Blo 471786 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B475235 : Blo 471786 475235 := bstep (se 1 (by rfl) ⟨356426, by rfl⟩ : syracuseStep 475235 = 712853) B712853
theorem B475251 : Blo 471786 475251 := bstep (se 1 (by rfl) ⟨356438, by rfl⟩ : syracuseStep 475251 = 712877) B712877
theorem B475267 : Blo 471786 475267 := bstep (se 1 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 475267 = 712901) B712901
theorem B475283 : Blo 471786 475283 := bstep (se 1 (by rfl) ⟨356462, by rfl⟩ : syracuseStep 475283 = 712925) B712925
theorem B671905 : Blo 471786 671905 := bstep (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) B503929
theorem B475299 : Blo 471786 475299 := bstep (se 1 (by rfl) ⟨356474, by rfl⟩ : syracuseStep 475299 = 712949) B712949
theorem B475315 : Blo 471786 475315 := bstep (se 1 (by rfl) ⟨356486, by rfl⟩ : syracuseStep 475315 = 712973) B712973
theorem B475331 : Blo 471786 475331 := bstep (se 1 (by rfl) ⟨356498, by rfl⟩ : syracuseStep 475331 = 712997) B712997
theorem B639185 : Blo 471786 639185 := bstep (se 2 (by rfl) ⟨239694, by rfl⟩ : syracuseStep 639185 = 479389) B479389
theorem B475347 : Blo 471786 475347 := bstep (se 1 (by rfl) ⟨356510, by rfl⟩ : syracuseStep 475347 = 713021) B713021
theorem B475363 : Blo 471786 475363 := bstep (se 1 (by rfl) ⟨356522, by rfl⟩ : syracuseStep 475363 = 713045) B713045
theorem B475379 : Blo 471786 475379 := bstep (se 1 (by rfl) ⟨356534, by rfl⟩ : syracuseStep 475379 = 713069) B713069
theorem B475395 : Blo 471786 475395 := bstep (se 1 (by rfl) ⟨356546, by rfl⟩ : syracuseStep 475395 = 713093) B713093
theorem B475411 : Blo 471786 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B475427 : Blo 471786 475427 := bstep (se 1 (by rfl) ⟨356570, by rfl⟩ : syracuseStep 475427 = 713141) B713141
theorem B475443 : Blo 471786 475443 := bstep (se 1 (by rfl) ⟨356582, by rfl⟩ : syracuseStep 475443 = 713165) B713165
theorem B475459 : Blo 471786 475459 := bstep (se 1 (by rfl) ⟨356594, by rfl⟩ : syracuseStep 475459 = 713189) B713189
theorem B475475 : Blo 471786 475475 := bstep (se 1 (by rfl) ⟨356606, by rfl⟩ : syracuseStep 475475 = 713213) B713213
theorem B475491 : Blo 471786 475491 := bstep (se 1 (by rfl) ⟨356618, by rfl⟩ : syracuseStep 475491 = 713237) B713237
theorem B1065329 : Blo 471786 1065329 := bstep (se 2 (by rfl) ⟨399498, by rfl⟩ : syracuseStep 1065329 = 798997) B798997
theorem B475507 : Blo 471786 475507 := bstep (se 1 (by rfl) ⟨356630, by rfl⟩ : syracuseStep 475507 = 713261) B713261
theorem B1065347 : Blo 471786 1065347 := bstep (se 1 (by rfl) ⟨799010, by rfl⟩ : syracuseStep 1065347 = 1598021) B1598021
theorem B475523 : Blo 471786 475523 := bstep (se 1 (by rfl) ⟨356642, by rfl⟩ : syracuseStep 475523 = 713285) B713285
theorem B475539 : Blo 471786 475539 := bstep (se 1 (by rfl) ⟨356654, by rfl⟩ : syracuseStep 475539 = 713309) B713309
theorem B475555 : Blo 471786 475555 := bstep (se 1 (by rfl) ⟨356666, by rfl⟩ : syracuseStep 475555 = 713333) B713333
theorem B475571 : Blo 471786 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B475587 : Blo 471786 475587 := bstep (se 1 (by rfl) ⟨356690, by rfl⟩ : syracuseStep 475587 = 713381) B713381
theorem B475603 : Blo 471786 475603 := bstep (se 1 (by rfl) ⟨356702, by rfl⟩ : syracuseStep 475603 = 713405) B713405
theorem B475619 : Blo 471786 475619 := bstep (se 1 (by rfl) ⟨356714, by rfl⟩ : syracuseStep 475619 = 713429) B713429
theorem B672241 : Blo 471786 672241 := bstep (se 2 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 672241 = 504181) B504181
theorem B475635 : Blo 471786 475635 := bstep (se 1 (by rfl) ⟨356726, by rfl⟩ : syracuseStep 475635 = 713453) B713453
theorem B475651 : Blo 471786 475651 := bstep (se 1 (by rfl) ⟨356738, by rfl⟩ : syracuseStep 475651 = 713477) B713477
theorem B475667 : Blo 471786 475667 := bstep (se 1 (by rfl) ⟨356750, by rfl⟩ : syracuseStep 475667 = 713501) B713501
theorem B901667 : Blo 471786 901667 := bstep (se 1 (by rfl) ⟨676250, by rfl⟩ : syracuseStep 901667 = 1352501) B1352501
theorem B475683 : Blo 471786 475683 := bstep (se 1 (by rfl) ⟨356762, by rfl⟩ : syracuseStep 475683 = 713525) B713525
theorem B475699 : Blo 471786 475699 := bstep (se 1 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 475699 = 713549) B713549
theorem B475715 : Blo 471786 475715 := bstep (se 1 (by rfl) ⟨356786, by rfl⟩ : syracuseStep 475715 = 713573) B713573
theorem B475731 : Blo 471786 475731 := bstep (se 1 (by rfl) ⟨356798, by rfl⟩ : syracuseStep 475731 = 713597) B713597
theorem B475747 : Blo 471786 475747 := bstep (se 1 (by rfl) ⟨356810, by rfl⟩ : syracuseStep 475747 = 713621) B713621
theorem B475763 : Blo 471786 475763 := bstep (se 1 (by rfl) ⟨356822, by rfl⟩ : syracuseStep 475763 = 713645) B713645
theorem B475779 : Blo 471786 475779 := bstep (se 1 (by rfl) ⟨356834, by rfl⟩ : syracuseStep 475779 = 713669) B713669
theorem B1065617 : Blo 471786 1065617 := bstep (se 2 (by rfl) ⟨399606, by rfl⟩ : syracuseStep 1065617 = 799213) B799213
theorem B1065635 : Blo 471786 1065635 := bstep (se 1 (by rfl) ⟨799226, by rfl⟩ : syracuseStep 1065635 = 1598453) B1598453
theorem B901955 : Blo 471786 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B1196977 : Blo 471786 1196977 := bstep (se 2 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 1196977 = 897733) B897733
theorem B1065905 : Blo 471786 1065905 := bstep (se 2 (by rfl) ⟨399714, by rfl⟩ : syracuseStep 1065905 = 799429) B799429
theorem B1065923 : Blo 471786 1065923 := bstep (se 1 (by rfl) ⟨799442, by rfl⟩ : syracuseStep 1065923 = 1598885) B1598885
theorem B672833 : Blo 471786 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B1197251 : Blo 471786 1197251 := bstep (se 1 (by rfl) ⟨897938, by rfl⟩ : syracuseStep 1197251 = 1795877) B1795877
theorem B3032261 : Blo 471786 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B1066193 : Blo 471786 1066193 := bstep (se 2 (by rfl) ⟨399822, by rfl⟩ : syracuseStep 1066193 = 799645) B799645
theorem B46613717 : Blo 471786 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1066211 : Blo 471786 1066211 := bstep (se 1 (by rfl) ⟨799658, by rfl⟩ : syracuseStep 1066211 = 1599317) B1599317
theorem B1197443 : Blo 471786 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B3851717 : Blo 471786 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1951181 : Blo 471786 1951181 := bstep (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) B731693
theorem B1066481 : Blo 471786 1066481 := bstep (se 2 (by rfl) ⟨399930, by rfl⟩ : syracuseStep 1066481 = 799861) B799861
theorem B1066499 : Blo 471786 1066499 := bstep (se 1 (by rfl) ⟨799874, by rfl⟩ : syracuseStep 1066499 = 1599749) B1599749
theorem B673363 : Blo 471786 673363 := bstep (se 1 (by rfl) ⟨505022, by rfl⟩ : syracuseStep 673363 = 1010045) B1010045
theorem B542387 : Blo 471786 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B2279117 : Blo 471786 2279117 := bstep (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) B854669
theorem B1918691 : Blo 471786 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B902897 : Blo 471786 902897 := bstep (se 2 (by rfl) ⟨338586, by rfl⟩ : syracuseStep 902897 = 677173) B677173
theorem B1066769 : Blo 471786 1066769 := bstep (se 2 (by rfl) ⟨400038, by rfl⟩ : syracuseStep 1066769 = 800077) B800077
theorem B1066787 : Blo 471786 1066787 := bstep (se 1 (by rfl) ⟨800090, by rfl⟩ : syracuseStep 1066787 = 1600181) B1600181
theorem B640915 : Blo 471786 640915 := bstep (se 1 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 640915 = 961373) B961373
theorem B673699 : Blo 471786 673699 := bstep (se 1 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 673699 = 1010549) B1010549
theorem B1067057 : Blo 471786 1067057 := bstep (se 2 (by rfl) ⟨400146, by rfl⟩ : syracuseStep 1067057 = 800293) B800293
theorem B1067075 : Blo 471786 1067075 := bstep (se 1 (by rfl) ⟨800306, by rfl⟩ : syracuseStep 1067075 = 1600613) B1600613
theorem B1198385 : Blo 471786 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B1624369 : Blo 471786 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B1067345 : Blo 471786 1067345 := bstep (se 2 (by rfl) ⟨400254, by rfl⟩ : syracuseStep 1067345 = 800509) B800509
theorem B1198435 : Blo 471786 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B1067363 : Blo 471786 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B674257 : Blo 471786 674257 := bstep (se 2 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 674257 = 505693) B505693
theorem B1198577 : Blo 471786 1198577 := bstep (se 2 (by rfl) ⟨449466, by rfl⟩ : syracuseStep 1198577 = 898933) B898933
theorem B674291 : Blo 471786 674291 := bstep (se 1 (by rfl) ⟨505718, by rfl⟩ : syracuseStep 674291 = 1011437) B1011437
theorem B1067633 : Blo 471786 1067633 := bstep (se 2 (by rfl) ⟨400362, by rfl⟩ : syracuseStep 1067633 = 800725) B800725
theorem B1067651 : Blo 471786 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B1231697 : Blo 471786 1231697 := bstep (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) B923773
theorem B4049777 : Blo 471786 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B3591053 : Blo 471786 3591053 := bstep (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) B1346645
theorem B1067921 : Blo 471786 1067921 := bstep (se 2 (by rfl) ⟨400470, by rfl⟩ : syracuseStep 1067921 = 800941) B800941
theorem B1067939 : Blo 471786 1067939 := bstep (se 1 (by rfl) ⟨800954, by rfl⟩ : syracuseStep 1067939 = 1601909) B1601909
theorem B12471317 : Blo 471786 12471317 := bstep (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) B584593
theorem B674849 : Blo 471786 674849 := bstep (se 2 (by rfl) ⟨253068, by rfl⟩ : syracuseStep 674849 = 506137) B506137
theorem B707681 : Blo 471786 707681 := bstep (se 2 (by rfl) ⟨265380, by rfl⟩ : syracuseStep 707681 = 530761) B530761
theorem B674929 : Blo 471786 674929 := bstep (se 2 (by rfl) ⟨253098, by rfl⟩ : syracuseStep 674929 = 506197) B506197
theorem B707699 : Blo 471786 707699 := bstep (se 1 (by rfl) ⟨530774, by rfl⟩ : syracuseStep 707699 = 1061549) B1061549
theorem B707729 : Blo 471786 707729 := bstep (se 2 (by rfl) ⟨265398, by rfl⟩ : syracuseStep 707729 = 530797) B530797
theorem B707747 : Blo 471786 707747 := bstep (se 1 (by rfl) ⟨530810, by rfl⟩ : syracuseStep 707747 = 1061621) B1061621
theorem B1068209 : Blo 471786 1068209 := bstep (se 2 (by rfl) ⟨400578, by rfl⟩ : syracuseStep 1068209 = 801157) B801157
theorem B707777 : Blo 471786 707777 := bstep (se 2 (by rfl) ⟨265416, by rfl⟩ : syracuseStep 707777 = 530833) B530833
theorem B1068227 : Blo 471786 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B707795 : Blo 471786 707795 := bstep (se 1 (by rfl) ⟨530846, by rfl⟩ : syracuseStep 707795 = 1061693) B1061693
theorem B707825 : Blo 471786 707825 := bstep (se 2 (by rfl) ⟨265434, by rfl⟩ : syracuseStep 707825 = 530869) B530869
theorem B707843 : Blo 471786 707843 := bstep (se 1 (by rfl) ⟨530882, by rfl⟩ : syracuseStep 707843 = 1061765) B1061765
theorem B707873 : Blo 471786 707873 := bstep (se 2 (by rfl) ⟨265452, by rfl⟩ : syracuseStep 707873 = 530905) B530905
theorem B1592621 : Blo 471786 1592621 := bstep (se 3 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 1592621 = 597233) B597233
theorem B707891 : Blo 471786 707891 := bstep (se 1 (by rfl) ⟨530918, by rfl⟩ : syracuseStep 707891 = 1061837) B1061837
theorem B707921 : Blo 471786 707921 := bstep (se 2 (by rfl) ⟨265470, by rfl⟩ : syracuseStep 707921 = 530941) B530941
theorem B1592675 : Blo 471786 1592675 := bstep (se 1 (by rfl) ⟨1194506, by rfl⟩ : syracuseStep 1592675 = 2389013) B2389013
theorem B707939 : Blo 471786 707939 := bstep (se 1 (by rfl) ⟨530954, by rfl⟩ : syracuseStep 707939 = 1061909) B1061909
theorem B707969 : Blo 471786 707969 := bstep (se 2 (by rfl) ⟨265488, by rfl⟩ : syracuseStep 707969 = 530977) B530977
theorem B707987 : Blo 471786 707987 := bstep (se 1 (by rfl) ⟨530990, by rfl⟩ : syracuseStep 707987 = 1061981) B1061981
theorem B708017 : Blo 471786 708017 := bstep (se 2 (by rfl) ⟨265506, by rfl⟩ : syracuseStep 708017 = 531013) B531013
theorem B708035 : Blo 471786 708035 := bstep (se 1 (by rfl) ⟨531026, by rfl⟩ : syracuseStep 708035 = 1062053) B1062053
theorem B1199569 : Blo 471786 1199569 := bstep (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) B899677
theorem B1068497 : Blo 471786 1068497 := bstep (se 2 (by rfl) ⟨400686, by rfl⟩ : syracuseStep 1068497 = 801373) B801373
theorem B708065 : Blo 471786 708065 := bstep (se 2 (by rfl) ⟨265524, by rfl⟩ : syracuseStep 708065 = 531049) B531049
theorem B1068515 : Blo 471786 1068515 := bstep (se 1 (by rfl) ⟨801386, by rfl⟩ : syracuseStep 1068515 = 1602773) B1602773
theorem B708083 : Blo 471786 708083 := bstep (se 1 (by rfl) ⟨531062, by rfl⟩ : syracuseStep 708083 = 1062125) B1062125
theorem B708113 : Blo 471786 708113 := bstep (se 2 (by rfl) ⟨265542, by rfl⟩ : syracuseStep 708113 = 531085) B531085
theorem B708131 : Blo 471786 708131 := bstep (se 1 (by rfl) ⟨531098, by rfl⟩ : syracuseStep 708131 = 1062197) B1062197
theorem B708161 : Blo 471786 708161 := bstep (se 2 (by rfl) ⟨265560, by rfl⟩ : syracuseStep 708161 = 531121) B531121
theorem B708179 : Blo 471786 708179 := bstep (se 1 (by rfl) ⟨531134, by rfl⟩ : syracuseStep 708179 = 1062269) B1062269
theorem B1592945 : Blo 471786 1592945 := bstep (se 2 (by rfl) ⟨597354, by rfl⟩ : syracuseStep 1592945 = 1194709) B1194709
theorem B708209 : Blo 471786 708209 := bstep (se 2 (by rfl) ⟨265578, by rfl⟩ : syracuseStep 708209 = 531157) B531157
theorem B708227 : Blo 471786 708227 := bstep (se 1 (by rfl) ⟨531170, by rfl⟩ : syracuseStep 708227 = 1062341) B1062341
theorem B708257 : Blo 471786 708257 := bstep (se 2 (by rfl) ⟨265596, by rfl⟩ : syracuseStep 708257 = 531193) B531193
theorem B642721 : Blo 471786 642721 := bstep (se 2 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 642721 = 482041) B482041
theorem B708275 : Blo 471786 708275 := bstep (se 1 (by rfl) ⟨531206, by rfl⟩ : syracuseStep 708275 = 1062413) B1062413
theorem B2707141 : Blo 471786 2707141 := bstep (se 4 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 2707141 = 507589) B507589
theorem B708305 : Blo 471786 708305 := bstep (se 2 (by rfl) ⟨265614, by rfl⟩ : syracuseStep 708305 = 531229) B531229
theorem B708323 : Blo 471786 708323 := bstep (se 1 (by rfl) ⟨531242, by rfl⟩ : syracuseStep 708323 = 1062485) B1062485
theorem B1199843 : Blo 471786 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B1068785 : Blo 471786 1068785 := bstep (se 2 (by rfl) ⟨400794, by rfl⟩ : syracuseStep 1068785 = 801589) B801589
theorem B708353 : Blo 471786 708353 := bstep (se 2 (by rfl) ⟨265632, by rfl⟩ : syracuseStep 708353 = 531265) B531265
theorem B1068803 : Blo 471786 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B708371 : Blo 471786 708371 := bstep (se 1 (by rfl) ⟨531278, by rfl⟩ : syracuseStep 708371 = 1062557) B1062557
theorem B708401 : Blo 471786 708401 := bstep (se 2 (by rfl) ⟨265650, by rfl⟩ : syracuseStep 708401 = 531301) B531301
theorem B708419 : Blo 471786 708419 := bstep (se 1 (by rfl) ⟨531314, by rfl⟩ : syracuseStep 708419 = 1062629) B1062629
theorem B708449 : Blo 471786 708449 := bstep (se 2 (by rfl) ⟨265668, by rfl⟩ : syracuseStep 708449 = 531337) B531337
theorem B1920881 : Blo 471786 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B708467 : Blo 471786 708467 := bstep (se 1 (by rfl) ⟨531350, by rfl⟩ : syracuseStep 708467 = 1062701) B1062701
theorem B675715 : Blo 471786 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B708497 : Blo 471786 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B708515 : Blo 471786 708515 := bstep (se 1 (by rfl) ⟨531386, by rfl⟩ : syracuseStep 708515 = 1062773) B1062773
theorem B1200035 : Blo 471786 1200035 := bstep (se 1 (by rfl) ⟨900026, by rfl⟩ : syracuseStep 1200035 = 1800053) B1800053
theorem B708545 : Blo 471786 708545 := bstep (se 2 (by rfl) ⟨265704, by rfl⟩ : syracuseStep 708545 = 531409) B531409
theorem B708563 : Blo 471786 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B708593 : Blo 471786 708593 := bstep (se 2 (by rfl) ⟨265722, by rfl⟩ : syracuseStep 708593 = 531445) B531445
theorem B708611 : Blo 471786 708611 := bstep (se 1 (by rfl) ⟨531458, by rfl⟩ : syracuseStep 708611 = 1062917) B1062917
theorem B1069073 : Blo 471786 1069073 := bstep (se 2 (by rfl) ⟨400902, by rfl⟩ : syracuseStep 1069073 = 801805) B801805
theorem B708641 : Blo 471786 708641 := bstep (se 2 (by rfl) ⟨265740, by rfl⟩ : syracuseStep 708641 = 531481) B531481
theorem B1069091 : Blo 471786 1069091 := bstep (se 1 (by rfl) ⟨801818, by rfl⟩ : syracuseStep 1069091 = 1603637) B1603637
theorem B708659 : Blo 471786 708659 := bstep (se 1 (by rfl) ⟨531494, by rfl⟩ : syracuseStep 708659 = 1062989) B1062989
theorem B708689 : Blo 471786 708689 := bstep (se 2 (by rfl) ⟨265758, by rfl⟩ : syracuseStep 708689 = 531517) B531517
theorem B708707 : Blo 471786 708707 := bstep (se 1 (by rfl) ⟨531530, by rfl⟩ : syracuseStep 708707 = 1063061) B1063061
theorem B708737 : Blo 471786 708737 := bstep (se 2 (by rfl) ⟨265776, by rfl⟩ : syracuseStep 708737 = 531553) B531553
theorem B1593485 : Blo 471786 1593485 := bstep (se 3 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 1593485 = 597557) B597557
theorem B1036433 : Blo 471786 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B708755 : Blo 471786 708755 := bstep (se 1 (by rfl) ⟨531566, by rfl⟩ : syracuseStep 708755 = 1063133) B1063133
theorem B2019491 : Blo 471786 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B708785 : Blo 471786 708785 := bstep (se 2 (by rfl) ⟨265794, by rfl⟩ : syracuseStep 708785 = 531589) B531589
theorem B1593539 : Blo 471786 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B708803 : Blo 471786 708803 := bstep (se 1 (by rfl) ⟨531602, by rfl⟩ : syracuseStep 708803 = 1063205) B1063205
theorem B9752773 : Blo 471786 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B708833 : Blo 471786 708833 := bstep (se 2 (by rfl) ⟨265812, by rfl⟩ : syracuseStep 708833 = 531625) B531625
theorem B708851 : Blo 471786 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B708881 : Blo 471786 708881 := bstep (se 2 (by rfl) ⟨265830, by rfl⟩ : syracuseStep 708881 = 531661) B531661
theorem B708899 : Blo 471786 708899 := bstep (se 1 (by rfl) ⟨531674, by rfl⟩ : syracuseStep 708899 = 1063349) B1063349
theorem B1069361 : Blo 471786 1069361 := bstep (se 2 (by rfl) ⟨401010, by rfl⟩ : syracuseStep 1069361 = 802021) B802021
theorem B708929 : Blo 471786 708929 := bstep (se 2 (by rfl) ⟨265848, by rfl⟩ : syracuseStep 708929 = 531697) B531697
theorem B1069379 : Blo 471786 1069379 := bstep (se 1 (by rfl) ⟨802034, by rfl⟩ : syracuseStep 1069379 = 1604069) B1604069
theorem B708947 : Blo 471786 708947 := bstep (se 1 (by rfl) ⟨531710, by rfl⟩ : syracuseStep 708947 = 1063421) B1063421
theorem B676193 : Blo 471786 676193 := bstep (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) B507145
theorem B708977 : Blo 471786 708977 := bstep (se 2 (by rfl) ⟨265866, by rfl⟩ : syracuseStep 708977 = 531733) B531733
theorem B708995 : Blo 471786 708995 := bstep (se 1 (by rfl) ⟨531746, by rfl⟩ : syracuseStep 708995 = 1063493) B1063493
theorem B709025 : Blo 471786 709025 := bstep (se 2 (by rfl) ⟨265884, by rfl⟩ : syracuseStep 709025 = 531769) B531769
theorem B709043 : Blo 471786 709043 := bstep (se 1 (by rfl) ⟨531782, by rfl⟩ : syracuseStep 709043 = 1063565) B1063565
theorem B1593809 : Blo 471786 1593809 := bstep (se 2 (by rfl) ⟨597678, by rfl⟩ : syracuseStep 1593809 = 1195357) B1195357
theorem B709073 : Blo 471786 709073 := bstep (se 2 (by rfl) ⟨265902, by rfl⟩ : syracuseStep 709073 = 531805) B531805
theorem B676307 : Blo 471786 676307 := bstep (se 1 (by rfl) ⟨507230, by rfl⟩ : syracuseStep 676307 = 1014461) B1014461
theorem B709091 : Blo 471786 709091 := bstep (se 1 (by rfl) ⟨531818, by rfl⟩ : syracuseStep 709091 = 1063637) B1063637
theorem B709121 : Blo 471786 709121 := bstep (se 2 (by rfl) ⟨265920, by rfl⟩ : syracuseStep 709121 = 531841) B531841
theorem B709139 : Blo 471786 709139 := bstep (se 1 (by rfl) ⟨531854, by rfl⟩ : syracuseStep 709139 = 1063709) B1063709
theorem B676387 : Blo 471786 676387 := bstep (se 1 (by rfl) ⟨507290, by rfl⟩ : syracuseStep 676387 = 1014581) B1014581
theorem B709169 : Blo 471786 709169 := bstep (se 2 (by rfl) ⟨265938, by rfl⟩ : syracuseStep 709169 = 531877) B531877
theorem B709187 : Blo 471786 709187 := bstep (se 1 (by rfl) ⟨531890, by rfl⟩ : syracuseStep 709187 = 1063781) B1063781
theorem B1364557 : Blo 471786 1364557 := bstep (se 3 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 1364557 = 511709) B511709
theorem B1069649 : Blo 471786 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B709217 : Blo 471786 709217 := bstep (se 2 (by rfl) ⟨265956, by rfl⟩ : syracuseStep 709217 = 531913) B531913
theorem B1069667 : Blo 471786 1069667 := bstep (se 1 (by rfl) ⟨802250, by rfl⟩ : syracuseStep 1069667 = 1604501) B1604501
theorem B10965617 : Blo 471786 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B709235 : Blo 471786 709235 := bstep (se 1 (by rfl) ⟨531926, by rfl⟩ : syracuseStep 709235 = 1063853) B1063853
theorem B709265 : Blo 471786 709265 := bstep (se 2 (by rfl) ⟨265974, by rfl⟩ : syracuseStep 709265 = 531949) B531949
theorem B709283 : Blo 471786 709283 := bstep (se 1 (by rfl) ⟨531962, by rfl⟩ : syracuseStep 709283 = 1063925) B1063925
theorem B709313 : Blo 471786 709313 := bstep (se 2 (by rfl) ⟨265992, by rfl⟩ : syracuseStep 709313 = 531985) B531985
theorem B709331 : Blo 471786 709331 := bstep (se 1 (by rfl) ⟨531998, by rfl⟩ : syracuseStep 709331 = 1063997) B1063997
theorem B709361 : Blo 471786 709361 := bstep (se 2 (by rfl) ⟨266010, by rfl⟩ : syracuseStep 709361 = 532021) B532021
theorem B709379 : Blo 471786 709379 := bstep (se 1 (by rfl) ⟨532034, by rfl⟩ : syracuseStep 709379 = 1064069) B1064069
theorem B709409 : Blo 471786 709409 := bstep (se 2 (by rfl) ⟨266028, by rfl⟩ : syracuseStep 709409 = 532057) B532057
theorem B709427 : Blo 471786 709427 := bstep (se 1 (by rfl) ⟨532070, by rfl⟩ : syracuseStep 709427 = 1064141) B1064141
theorem B709457 : Blo 471786 709457 := bstep (se 2 (by rfl) ⟨266046, by rfl⟩ : syracuseStep 709457 = 532093) B532093
theorem B1200977 : Blo 471786 1200977 := bstep (se 2 (by rfl) ⟨450366, by rfl⟩ : syracuseStep 1200977 = 900733) B900733
theorem B709475 : Blo 471786 709475 := bstep (se 1 (by rfl) ⟨532106, by rfl⟩ : syracuseStep 709475 = 1064213) B1064213
theorem B1069937 : Blo 471786 1069937 := bstep (se 2 (by rfl) ⟨401226, by rfl⟩ : syracuseStep 1069937 = 802453) B802453
theorem B709505 : Blo 471786 709505 := bstep (se 2 (by rfl) ⟨266064, by rfl⟩ : syracuseStep 709505 = 532129) B532129
theorem B1201027 : Blo 471786 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B1069955 : Blo 471786 1069955 := bstep (se 1 (by rfl) ⟨802466, by rfl⟩ : syracuseStep 1069955 = 1604933) B1604933
theorem B1823629 : Blo 471786 1823629 := bstep (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) B683861
theorem B1299341 : Blo 471786 1299341 := bstep (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) B487253
theorem B709523 : Blo 471786 709523 := bstep (se 1 (by rfl) ⟨532142, by rfl⟩ : syracuseStep 709523 = 1064285) B1064285
theorem B709553 : Blo 471786 709553 := bstep (se 2 (by rfl) ⟨266082, by rfl⟩ : syracuseStep 709553 = 532165) B532165
theorem B807875 : Blo 471786 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B709571 : Blo 471786 709571 := bstep (se 1 (by rfl) ⟨532178, by rfl⟩ : syracuseStep 709571 = 1064357) B1064357
theorem B709601 : Blo 471786 709601 := bstep (se 2 (by rfl) ⟨266100, by rfl⟩ : syracuseStep 709601 = 532201) B532201
theorem B1594349 : Blo 471786 1594349 := bstep (se 3 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 1594349 = 597881) B597881
theorem B709619 : Blo 471786 709619 := bstep (se 1 (by rfl) ⟨532214, by rfl⟩ : syracuseStep 709619 = 1064429) B1064429
theorem B709649 : Blo 471786 709649 := bstep (se 2 (by rfl) ⟨266118, by rfl⟩ : syracuseStep 709649 = 532237) B532237
theorem B1201169 : Blo 471786 1201169 := bstep (se 2 (by rfl) ⟨450438, by rfl⟩ : syracuseStep 1201169 = 900877) B900877
theorem B1594403 : Blo 471786 1594403 := bstep (se 1 (by rfl) ⟨1195802, by rfl⟩ : syracuseStep 1594403 = 2391605) B2391605
theorem B709667 : Blo 471786 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B709697 : Blo 471786 709697 := bstep (se 2 (by rfl) ⟨266136, by rfl⟩ : syracuseStep 709697 = 532273) B532273
theorem B676945 : Blo 471786 676945 := bstep (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) B507709
theorem B709715 : Blo 471786 709715 := bstep (se 1 (by rfl) ⟨532286, by rfl⟩ : syracuseStep 709715 = 1064573) B1064573
theorem B709745 : Blo 471786 709745 := bstep (se 2 (by rfl) ⟨266154, by rfl⟩ : syracuseStep 709745 = 532309) B532309
theorem B709763 : Blo 471786 709763 := bstep (se 1 (by rfl) ⟨532322, by rfl⟩ : syracuseStep 709763 = 1064645) B1064645
theorem B1070225 : Blo 471786 1070225 := bstep (se 2 (by rfl) ⟨401334, by rfl⟩ : syracuseStep 1070225 = 802669) B802669
theorem B709793 : Blo 471786 709793 := bstep (se 2 (by rfl) ⟨266172, by rfl⟩ : syracuseStep 709793 = 532345) B532345
theorem B1070243 : Blo 471786 1070243 := bstep (se 1 (by rfl) ⟨802682, by rfl⟩ : syracuseStep 1070243 = 1605365) B1605365
theorem B709811 : Blo 471786 709811 := bstep (se 1 (by rfl) ⟨532358, by rfl⟩ : syracuseStep 709811 = 1064717) B1064717
theorem B709841 : Blo 471786 709841 := bstep (se 2 (by rfl) ⟨266190, by rfl⟩ : syracuseStep 709841 = 532381) B532381
theorem B709859 : Blo 471786 709859 := bstep (se 1 (by rfl) ⟨532394, by rfl⟩ : syracuseStep 709859 = 1064789) B1064789
theorem B709889 : Blo 471786 709889 := bstep (se 2 (by rfl) ⟨266208, by rfl⟩ : syracuseStep 709889 = 532417) B532417
theorem B709907 : Blo 471786 709907 := bstep (se 1 (by rfl) ⟨532430, by rfl⟩ : syracuseStep 709907 = 1064861) B1064861
theorem B1594673 : Blo 471786 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B709937 : Blo 471786 709937 := bstep (se 2 (by rfl) ⟨266226, by rfl⟩ : syracuseStep 709937 = 532453) B532453
theorem B709955 : Blo 471786 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B709985 : Blo 471786 709985 := bstep (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) B532489
theorem B710003 : Blo 471786 710003 := bstep (se 1 (by rfl) ⟨532502, by rfl⟩ : syracuseStep 710003 = 1065005) B1065005
theorem B710033 : Blo 471786 710033 := bstep (se 2 (by rfl) ⟨266262, by rfl⟩ : syracuseStep 710033 = 532525) B532525
theorem B710051 : Blo 471786 710051 := bstep (se 1 (by rfl) ⟨532538, by rfl⟩ : syracuseStep 710051 = 1065077) B1065077
theorem B1070513 : Blo 471786 1070513 := bstep (se 2 (by rfl) ⟨401442, by rfl⟩ : syracuseStep 1070513 = 802885) B802885
theorem B710081 : Blo 471786 710081 := bstep (se 2 (by rfl) ⟨266280, by rfl⟩ : syracuseStep 710081 = 532561) B532561
theorem B8639941 : Blo 471786 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B710099 : Blo 471786 710099 := bstep (se 1 (by rfl) ⟨532574, by rfl⟩ : syracuseStep 710099 = 1065149) B1065149
theorem B710129 : Blo 471786 710129 := bstep (se 2 (by rfl) ⟨266298, by rfl⟩ : syracuseStep 710129 = 532597) B532597
theorem B710147 : Blo 471786 710147 := bstep (se 1 (by rfl) ⟨532610, by rfl⟩ : syracuseStep 710147 = 1065221) B1065221
theorem B710177 : Blo 471786 710177 := bstep (se 2 (by rfl) ⟨266316, by rfl⟩ : syracuseStep 710177 = 532633) B532633
theorem B710195 : Blo 471786 710195 := bstep (se 1 (by rfl) ⟨532646, by rfl⟩ : syracuseStep 710195 = 1065293) B1065293
theorem B710225 : Blo 471786 710225 := bstep (se 2 (by rfl) ⟨266334, by rfl⟩ : syracuseStep 710225 = 532669) B532669
theorem B710243 : Blo 471786 710243 := bstep (se 1 (by rfl) ⟨532682, by rfl⟩ : syracuseStep 710243 = 1065365) B1065365
theorem B710273 : Blo 471786 710273 := bstep (se 2 (by rfl) ⟨266352, by rfl⟩ : syracuseStep 710273 = 532705) B532705
theorem B2709125 : Blo 471786 2709125 := bstep (se 4 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 2709125 = 507961) B507961
theorem B710291 : Blo 471786 710291 := bstep (se 1 (by rfl) ⟨532718, by rfl⟩ : syracuseStep 710291 = 1065437) B1065437
theorem B710321 : Blo 471786 710321 := bstep (se 2 (by rfl) ⟨266370, by rfl⟩ : syracuseStep 710321 = 532741) B532741
theorem B710339 : Blo 471786 710339 := bstep (se 1 (by rfl) ⟨532754, by rfl⟩ : syracuseStep 710339 = 1065509) B1065509
theorem B710369 : Blo 471786 710369 := bstep (se 2 (by rfl) ⟨266388, by rfl⟩ : syracuseStep 710369 = 532777) B532777
theorem B3593969 : Blo 471786 3593969 := bstep (se 2 (by rfl) ⟨1347738, by rfl⟩ : syracuseStep 3593969 = 2695477) B2695477
theorem B710387 : Blo 471786 710387 := bstep (se 1 (by rfl) ⟨532790, by rfl⟩ : syracuseStep 710387 = 1065581) B1065581
theorem B710417 : Blo 471786 710417 := bstep (se 2 (by rfl) ⟨266406, by rfl⟩ : syracuseStep 710417 = 532813) B532813
theorem B710435 : Blo 471786 710435 := bstep (se 1 (by rfl) ⟨532826, by rfl⟩ : syracuseStep 710435 = 1065653) B1065653
theorem B710465 : Blo 471786 710465 := bstep (se 2 (by rfl) ⟨266424, by rfl⟩ : syracuseStep 710465 = 532849) B532849
theorem B1791821 : Blo 471786 1791821 := bstep (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) B671933
theorem B1595213 : Blo 471786 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B710483 : Blo 471786 710483 := bstep (se 1 (by rfl) ⟨532862, by rfl⟩ : syracuseStep 710483 = 1065725) B1065725
theorem B2021233 : Blo 471786 2021233 := bstep (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) B1515925
theorem B710513 : Blo 471786 710513 := bstep (se 2 (by rfl) ⟨266442, by rfl⟩ : syracuseStep 710513 = 532885) B532885
theorem B710531 : Blo 471786 710531 := bstep (se 1 (by rfl) ⟨532898, by rfl⟩ : syracuseStep 710531 = 1065797) B1065797
theorem B1595267 : Blo 471786 1595267 := bstep (se 1 (by rfl) ⟨1196450, by rfl⟩ : syracuseStep 1595267 = 2392901) B2392901
theorem B22763405 : Blo 471786 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B710561 : Blo 471786 710561 := bstep (se 2 (by rfl) ⟨266460, by rfl⟩ : syracuseStep 710561 = 532921) B532921
theorem B710579 : Blo 471786 710579 := bstep (se 1 (by rfl) ⟨532934, by rfl⟩ : syracuseStep 710579 = 1065869) B1065869
theorem B710609 : Blo 471786 710609 := bstep (se 2 (by rfl) ⟨266478, by rfl⟩ : syracuseStep 710609 = 532957) B532957
theorem B710627 : Blo 471786 710627 := bstep (se 1 (by rfl) ⟨532970, by rfl⟩ : syracuseStep 710627 = 1065941) B1065941
theorem B1202161 : Blo 471786 1202161 := bstep (se 2 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 1202161 = 901621) B901621
theorem B710657 : Blo 471786 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B710675 : Blo 471786 710675 := bstep (se 1 (by rfl) ⟨533006, by rfl⟩ : syracuseStep 710675 = 1066013) B1066013
theorem B710705 : Blo 471786 710705 := bstep (se 2 (by rfl) ⟨266514, by rfl⟩ : syracuseStep 710705 = 533029) B533029
theorem B710723 : Blo 471786 710723 := bstep (se 1 (by rfl) ⟨533042, by rfl⟩ : syracuseStep 710723 = 1066085) B1066085
theorem B710753 : Blo 471786 710753 := bstep (se 2 (by rfl) ⟨266532, by rfl⟩ : syracuseStep 710753 = 533065) B533065
theorem B710771 : Blo 471786 710771 := bstep (se 1 (by rfl) ⟨533078, by rfl⟩ : syracuseStep 710771 = 1066157) B1066157
theorem B1136771 : Blo 471786 1136771 := bstep (se 1 (by rfl) ⟨852578, by rfl⟩ : syracuseStep 1136771 = 1705157) B1705157
theorem B1595537 : Blo 471786 1595537 := bstep (se 2 (by rfl) ⟨598326, by rfl⟩ : syracuseStep 1595537 = 1196653) B1196653
theorem B710801 : Blo 471786 710801 := bstep (se 2 (by rfl) ⟨266550, by rfl⟩ : syracuseStep 710801 = 533101) B533101
theorem B710819 : Blo 471786 710819 := bstep (se 1 (by rfl) ⟨533114, by rfl⟩ : syracuseStep 710819 = 1066229) B1066229
theorem B710849 : Blo 471786 710849 := bstep (se 2 (by rfl) ⟨266568, by rfl⟩ : syracuseStep 710849 = 533137) B533137
theorem B2087117 : Blo 471786 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B710867 : Blo 471786 710867 := bstep (se 1 (by rfl) ⟨533150, by rfl⟩ : syracuseStep 710867 = 1066301) B1066301
theorem B710897 : Blo 471786 710897 := bstep (se 2 (by rfl) ⟨266586, by rfl⟩ : syracuseStep 710897 = 533173) B533173
theorem B710915 : Blo 471786 710915 := bstep (se 1 (by rfl) ⟨533186, by rfl⟩ : syracuseStep 710915 = 1066373) B1066373
theorem B1202435 : Blo 471786 1202435 := bstep (se 1 (by rfl) ⟨901826, by rfl⟩ : syracuseStep 1202435 = 1803653) B1803653
theorem B710945 : Blo 471786 710945 := bstep (se 2 (by rfl) ⟨266604, by rfl⟩ : syracuseStep 710945 = 533209) B533209
theorem B710963 : Blo 471786 710963 := bstep (se 1 (by rfl) ⟨533222, by rfl⟩ : syracuseStep 710963 = 1066445) B1066445
theorem B1136963 : Blo 471786 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B547139 : Blo 471786 547139 := bstep (se 1 (by rfl) ⟨410354, by rfl⟩ : syracuseStep 547139 = 820709) B820709
theorem B710993 : Blo 471786 710993 := bstep (se 2 (by rfl) ⟨266622, by rfl⟩ : syracuseStep 710993 = 533245) B533245
theorem B711011 : Blo 471786 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B711041 : Blo 471786 711041 := bstep (se 2 (by rfl) ⟨266640, by rfl⟩ : syracuseStep 711041 = 533281) B533281
theorem B711059 : Blo 471786 711059 := bstep (se 1 (by rfl) ⟨533294, by rfl⟩ : syracuseStep 711059 = 1066589) B1066589
theorem B711089 : Blo 471786 711089 := bstep (se 2 (by rfl) ⟨266658, by rfl⟩ : syracuseStep 711089 = 533317) B533317
theorem B711107 : Blo 471786 711107 := bstep (se 1 (by rfl) ⟨533330, by rfl⟩ : syracuseStep 711107 = 1066661) B1066661
theorem B1202627 : Blo 471786 1202627 := bstep (se 1 (by rfl) ⟨901970, by rfl⟩ : syracuseStep 1202627 = 1803941) B1803941
theorem B711137 : Blo 471786 711137 := bstep (se 2 (by rfl) ⟨266676, by rfl⟩ : syracuseStep 711137 = 533353) B533353
theorem B711155 : Blo 471786 711155 := bstep (se 1 (by rfl) ⟨533366, by rfl⟩ : syracuseStep 711155 = 1066733) B1066733
theorem B711185 : Blo 471786 711185 := bstep (se 2 (by rfl) ⟨266694, by rfl⟩ : syracuseStep 711185 = 533389) B533389
theorem B711203 : Blo 471786 711203 := bstep (se 1 (by rfl) ⟨533402, by rfl⟩ : syracuseStep 711203 = 1066805) B1066805
theorem B711233 : Blo 471786 711233 := bstep (se 2 (by rfl) ⟨266712, by rfl⟩ : syracuseStep 711233 = 533425) B533425
theorem B1137233 : Blo 471786 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B711251 : Blo 471786 711251 := bstep (se 1 (by rfl) ⟨533438, by rfl⟩ : syracuseStep 711251 = 1066877) B1066877
theorem B711281 : Blo 471786 711281 := bstep (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) B533461
theorem B481907 : Blo 471786 481907 := bstep (se 1 (by rfl) ⟨361430, by rfl⟩ : syracuseStep 481907 = 722861) B722861
theorem B711299 : Blo 471786 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B711329 : Blo 471786 711329 := bstep (se 2 (by rfl) ⟨266748, by rfl⟩ : syracuseStep 711329 = 533497) B533497
theorem B1596077 : Blo 471786 1596077 := bstep (se 3 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 1596077 = 598529) B598529
theorem B711347 : Blo 471786 711347 := bstep (se 1 (by rfl) ⟨533510, by rfl⟩ : syracuseStep 711347 = 1067021) B1067021
theorem B711377 : Blo 471786 711377 := bstep (se 2 (by rfl) ⟨266766, by rfl⟩ : syracuseStep 711377 = 533533) B533533
theorem B1596131 : Blo 471786 1596131 := bstep (se 1 (by rfl) ⟨1197098, by rfl⟩ : syracuseStep 1596131 = 2394197) B2394197
theorem B711395 : Blo 471786 711395 := bstep (se 1 (by rfl) ⟨533546, by rfl⟩ : syracuseStep 711395 = 1067093) B1067093
theorem B711425 : Blo 471786 711425 := bstep (se 2 (by rfl) ⟨266784, by rfl⟩ : syracuseStep 711425 = 533569) B533569
theorem B711443 : Blo 471786 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B809777 : Blo 471786 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B711473 : Blo 471786 711473 := bstep (se 2 (by rfl) ⟨266802, by rfl⟩ : syracuseStep 711473 = 533605) B533605
theorem B711491 : Blo 471786 711491 := bstep (se 1 (by rfl) ⟨533618, by rfl⟩ : syracuseStep 711491 = 1067237) B1067237
theorem B711521 : Blo 471786 711521 := bstep (se 2 (by rfl) ⟨266820, by rfl⟩ : syracuseStep 711521 = 533641) B533641
theorem B711539 : Blo 471786 711539 := bstep (se 1 (by rfl) ⟨533654, by rfl⟩ : syracuseStep 711539 = 1067309) B1067309
theorem B711569 : Blo 471786 711569 := bstep (se 2 (by rfl) ⟨266838, by rfl⟩ : syracuseStep 711569 = 533677) B533677
theorem B711587 : Blo 471786 711587 := bstep (se 1 (by rfl) ⟨533690, by rfl⟩ : syracuseStep 711587 = 1067381) B1067381
theorem B711617 : Blo 471786 711617 := bstep (se 2 (by rfl) ⟨266856, by rfl⟩ : syracuseStep 711617 = 533713) B533713
theorem B1137617 : Blo 471786 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B711635 : Blo 471786 711635 := bstep (se 1 (by rfl) ⟨533726, by rfl⟩ : syracuseStep 711635 = 1067453) B1067453
theorem B1596401 : Blo 471786 1596401 := bstep (se 2 (by rfl) ⟨598650, by rfl⟩ : syracuseStep 1596401 = 1197301) B1197301
theorem B711665 : Blo 471786 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B711683 : Blo 471786 711683 := bstep (se 1 (by rfl) ⟨533762, by rfl⟩ : syracuseStep 711683 = 1067525) B1067525
theorem B711713 : Blo 471786 711713 := bstep (se 2 (by rfl) ⟨266892, by rfl⟩ : syracuseStep 711713 = 533785) B533785
theorem B711731 : Blo 471786 711731 := bstep (se 1 (by rfl) ⟨533798, by rfl⟩ : syracuseStep 711731 = 1067597) B1067597
theorem B2874437 : Blo 471786 2874437 := bstep (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) B538957
theorem B711761 : Blo 471786 711761 := bstep (se 2 (by rfl) ⟨266910, by rfl⟩ : syracuseStep 711761 = 533821) B533821
theorem B711779 : Blo 471786 711779 := bstep (se 1 (by rfl) ⟨533834, by rfl⟩ : syracuseStep 711779 = 1067669) B1067669
theorem B711809 : Blo 471786 711809 := bstep (se 2 (by rfl) ⟨266928, by rfl⟩ : syracuseStep 711809 = 533857) B533857
theorem B711827 : Blo 471786 711827 := bstep (se 1 (by rfl) ⟨533870, by rfl⟩ : syracuseStep 711827 = 1067741) B1067741
theorem B711857 : Blo 471786 711857 := bstep (se 2 (by rfl) ⟨266946, by rfl⟩ : syracuseStep 711857 = 533893) B533893
theorem B711875 : Blo 471786 711875 := bstep (se 1 (by rfl) ⟨533906, by rfl⟩ : syracuseStep 711875 = 1067813) B1067813
theorem B646339 : Blo 471786 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B711905 : Blo 471786 711905 := bstep (se 2 (by rfl) ⟨266964, by rfl⟩ : syracuseStep 711905 = 533929) B533929
theorem B711923 : Blo 471786 711923 := bstep (se 1 (by rfl) ⟨533942, by rfl⟩ : syracuseStep 711923 = 1067885) B1067885
theorem B711953 : Blo 471786 711953 := bstep (se 2 (by rfl) ⟨266982, by rfl⟩ : syracuseStep 711953 = 533965) B533965
theorem B711971 : Blo 471786 711971 := bstep (se 1 (by rfl) ⟨533978, by rfl⟩ : syracuseStep 711971 = 1067957) B1067957
theorem B712001 : Blo 471786 712001 := bstep (se 2 (by rfl) ⟨267000, by rfl⟩ : syracuseStep 712001 = 534001) B534001
theorem B712019 : Blo 471786 712019 := bstep (se 1 (by rfl) ⟨534014, by rfl⟩ : syracuseStep 712019 = 1068029) B1068029
theorem B3038563 : Blo 471786 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B712049 : Blo 471786 712049 := bstep (se 2 (by rfl) ⟨267018, by rfl⟩ : syracuseStep 712049 = 534037) B534037
theorem B1203569 : Blo 471786 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B712067 : Blo 471786 712067 := bstep (se 1 (by rfl) ⟨534050, by rfl⟩ : syracuseStep 712067 = 1068101) B1068101
theorem B712097 : Blo 471786 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B1203619 : Blo 471786 1203619 := bstep (se 1 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 1203619 = 1805429) B1805429
theorem B712115 : Blo 471786 712115 := bstep (se 1 (by rfl) ⟨534086, by rfl⟩ : syracuseStep 712115 = 1068173) B1068173
theorem B712145 : Blo 471786 712145 := bstep (se 2 (by rfl) ⟨267054, by rfl⟩ : syracuseStep 712145 = 534109) B534109
theorem B712163 : Blo 471786 712163 := bstep (se 1 (by rfl) ⟨534122, by rfl⟩ : syracuseStep 712163 = 1068245) B1068245
theorem B712193 : Blo 471786 712193 := bstep (se 2 (by rfl) ⟨267072, by rfl⟩ : syracuseStep 712193 = 534145) B534145
theorem B1596941 : Blo 471786 1596941 := bstep (se 3 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 1596941 = 598853) B598853
theorem B712211 : Blo 471786 712211 := bstep (se 1 (by rfl) ⟨534158, by rfl⟩ : syracuseStep 712211 = 1068317) B1068317
theorem B712241 : Blo 471786 712241 := bstep (se 2 (by rfl) ⟨267090, by rfl⟩ : syracuseStep 712241 = 534181) B534181
theorem B1203761 : Blo 471786 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B1596995 : Blo 471786 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B712259 : Blo 471786 712259 := bstep (se 1 (by rfl) ⟨534194, by rfl⟩ : syracuseStep 712259 = 1068389) B1068389
theorem B2743877 : Blo 471786 2743877 := bstep (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) B514477
theorem B1302097 : Blo 471786 1302097 := bstep (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) B976573
theorem B712289 : Blo 471786 712289 := bstep (se 2 (by rfl) ⟨267108, by rfl⟩ : syracuseStep 712289 = 534217) B534217
theorem B712307 : Blo 471786 712307 := bstep (se 1 (by rfl) ⟨534230, by rfl⟩ : syracuseStep 712307 = 1068461) B1068461
theorem B712337 : Blo 471786 712337 := bstep (se 2 (by rfl) ⟨267126, by rfl⟩ : syracuseStep 712337 = 534253) B534253
theorem B712355 : Blo 471786 712355 := bstep (se 1 (by rfl) ⟨534266, by rfl⟩ : syracuseStep 712355 = 1068533) B1068533
theorem B712385 : Blo 471786 712385 := bstep (se 2 (by rfl) ⟨267144, by rfl⟩ : syracuseStep 712385 = 534289) B534289
theorem B1138385 : Blo 471786 1138385 := bstep (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) B853789
theorem B712403 : Blo 471786 712403 := bstep (se 1 (by rfl) ⟨534302, by rfl⟩ : syracuseStep 712403 = 1068605) B1068605
theorem B712433 : Blo 471786 712433 := bstep (se 2 (by rfl) ⟨267162, by rfl⟩ : syracuseStep 712433 = 534325) B534325
theorem B712451 : Blo 471786 712451 := bstep (se 1 (by rfl) ⟨534338, by rfl⟩ : syracuseStep 712451 = 1068677) B1068677
theorem B2023181 : Blo 471786 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B712481 : Blo 471786 712481 := bstep (se 2 (by rfl) ⟨267180, by rfl⟩ : syracuseStep 712481 = 534361) B534361
theorem B712499 : Blo 471786 712499 := bstep (se 1 (by rfl) ⟨534374, by rfl⟩ : syracuseStep 712499 = 1068749) B1068749
theorem B4874053 : Blo 471786 4874053 := bstep (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) B913885
theorem B1597265 : Blo 471786 1597265 := bstep (se 2 (by rfl) ⟨598974, by rfl⟩ : syracuseStep 1597265 = 1197949) B1197949
theorem B712529 : Blo 471786 712529 := bstep (se 2 (by rfl) ⟨267198, by rfl⟩ : syracuseStep 712529 = 534397) B534397
theorem B1138531 : Blo 471786 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B712547 : Blo 471786 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B712577 : Blo 471786 712577 := bstep (se 2 (by rfl) ⟨267216, by rfl⟩ : syracuseStep 712577 = 534433) B534433
theorem B1793933 : Blo 471786 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B712595 : Blo 471786 712595 := bstep (se 1 (by rfl) ⟨534446, by rfl⟩ : syracuseStep 712595 = 1068893) B1068893
theorem B712625 : Blo 471786 712625 := bstep (se 2 (by rfl) ⟨267234, by rfl⟩ : syracuseStep 712625 = 534469) B534469
theorem B712643 : Blo 471786 712643 := bstep (se 1 (by rfl) ⟨534482, by rfl⟩ : syracuseStep 712643 = 1068965) B1068965
theorem B712673 : Blo 471786 712673 := bstep (se 2 (by rfl) ⟨267252, by rfl⟩ : syracuseStep 712673 = 534505) B534505
theorem B712691 : Blo 471786 712691 := bstep (se 1 (by rfl) ⟨534518, by rfl⟩ : syracuseStep 712691 = 1069037) B1069037
theorem B712721 : Blo 471786 712721 := bstep (se 2 (by rfl) ⟨267270, by rfl⟩ : syracuseStep 712721 = 534541) B534541
theorem B712739 : Blo 471786 712739 := bstep (se 1 (by rfl) ⟨534554, by rfl⟩ : syracuseStep 712739 = 1069109) B1069109
theorem B712769 : Blo 471786 712769 := bstep (se 2 (by rfl) ⟨267288, by rfl⟩ : syracuseStep 712769 = 534577) B534577
theorem B1466435 : Blo 471786 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B712787 : Blo 471786 712787 := bstep (se 1 (by rfl) ⟨534590, by rfl⟩ : syracuseStep 712787 = 1069181) B1069181
theorem B1007729 : Blo 471786 1007729 := bstep (se 2 (by rfl) ⟨377898, by rfl⟩ : syracuseStep 1007729 = 755797) B755797
theorem B712817 : Blo 471786 712817 := bstep (se 2 (by rfl) ⟨267306, by rfl⟩ : syracuseStep 712817 = 534613) B534613
theorem B712835 : Blo 471786 712835 := bstep (se 1 (by rfl) ⟨534626, by rfl⟩ : syracuseStep 712835 = 1069253) B1069253
theorem B712865 : Blo 471786 712865 := bstep (se 2 (by rfl) ⟨267324, by rfl⟩ : syracuseStep 712865 = 534649) B534649
theorem B712883 : Blo 471786 712883 := bstep (se 1 (by rfl) ⟨534662, by rfl⟩ : syracuseStep 712883 = 1069325) B1069325
theorem B712913 : Blo 471786 712913 := bstep (se 2 (by rfl) ⟨267342, by rfl⟩ : syracuseStep 712913 = 534685) B534685
theorem B712931 : Blo 471786 712931 := bstep (se 1 (by rfl) ⟨534698, by rfl⟩ : syracuseStep 712931 = 1069397) B1069397
theorem B712961 : Blo 471786 712961 := bstep (se 2 (by rfl) ⟨267360, by rfl⟩ : syracuseStep 712961 = 534721) B534721
theorem B712979 : Blo 471786 712979 := bstep (se 1 (by rfl) ⟨534734, by rfl⟩ : syracuseStep 712979 = 1069469) B1069469
theorem B713009 : Blo 471786 713009 := bstep (se 2 (by rfl) ⟨267378, by rfl⟩ : syracuseStep 713009 = 534757) B534757
theorem B713027 : Blo 471786 713027 := bstep (se 1 (by rfl) ⟨534770, by rfl⟩ : syracuseStep 713027 = 1069541) B1069541
theorem B3039565 : Blo 471786 3039565 := bstep (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) B1139837
theorem B713057 : Blo 471786 713057 := bstep (se 2 (by rfl) ⟨267396, by rfl⟩ : syracuseStep 713057 = 534793) B534793
theorem B1597805 : Blo 471786 1597805 := bstep (se 3 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 1597805 = 599177) B599177
theorem B713075 : Blo 471786 713075 := bstep (se 1 (by rfl) ⟨534806, by rfl⟩ : syracuseStep 713075 = 1069613) B1069613
theorem B713105 : Blo 471786 713105 := bstep (se 2 (by rfl) ⟨267414, by rfl⟩ : syracuseStep 713105 = 534829) B534829
theorem B1597859 : Blo 471786 1597859 := bstep (se 1 (by rfl) ⟨1198394, by rfl⟩ : syracuseStep 1597859 = 2396789) B2396789
theorem B713123 : Blo 471786 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B713153 : Blo 471786 713153 := bstep (se 2 (by rfl) ⟨267432, by rfl⟩ : syracuseStep 713153 = 534865) B534865
theorem B713171 : Blo 471786 713171 := bstep (se 1 (by rfl) ⟨534878, by rfl⟩ : syracuseStep 713171 = 1069757) B1069757
theorem B713201 : Blo 471786 713201 := bstep (se 2 (by rfl) ⟨267450, by rfl⟩ : syracuseStep 713201 = 534901) B534901
theorem B713219 : Blo 471786 713219 := bstep (se 1 (by rfl) ⟨534914, by rfl⟩ : syracuseStep 713219 = 1069829) B1069829
theorem B713249 : Blo 471786 713249 := bstep (se 2 (by rfl) ⟨267468, by rfl⟩ : syracuseStep 713249 = 534937) B534937
theorem B2744867 : Blo 471786 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B713267 : Blo 471786 713267 := bstep (se 1 (by rfl) ⟨534950, by rfl⟩ : syracuseStep 713267 = 1069901) B1069901
theorem B713297 : Blo 471786 713297 := bstep (se 2 (by rfl) ⟨267486, by rfl⟩ : syracuseStep 713297 = 534973) B534973
theorem B713315 : Blo 471786 713315 := bstep (se 1 (by rfl) ⟨534986, by rfl⟩ : syracuseStep 713315 = 1069973) B1069973
theorem B713345 : Blo 471786 713345 := bstep (se 2 (by rfl) ⟨267504, by rfl⟩ : syracuseStep 713345 = 535009) B535009
theorem B713363 : Blo 471786 713363 := bstep (se 1 (by rfl) ⟨535022, by rfl⟩ : syracuseStep 713363 = 1070045) B1070045
theorem B1794737 : Blo 471786 1794737 := bstep (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) B1346053
theorem B1598129 : Blo 471786 1598129 := bstep (se 2 (by rfl) ⟨599298, by rfl⟩ : syracuseStep 1598129 = 1198597) B1198597
theorem B713393 : Blo 471786 713393 := bstep (se 2 (by rfl) ⟨267522, by rfl⟩ : syracuseStep 713393 = 535045) B535045
theorem B713411 : Blo 471786 713411 := bstep (se 1 (by rfl) ⟨535058, by rfl⟩ : syracuseStep 713411 = 1070117) B1070117
theorem B713441 : Blo 471786 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B713459 : Blo 471786 713459 := bstep (se 1 (by rfl) ⟨535094, by rfl⟩ : syracuseStep 713459 = 1070189) B1070189
theorem B5104397 : Blo 471786 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B713489 : Blo 471786 713489 := bstep (se 2 (by rfl) ⟨267558, by rfl⟩ : syracuseStep 713489 = 535117) B535117
theorem B713507 : Blo 471786 713507 := bstep (se 1 (by rfl) ⟨535130, by rfl⟩ : syracuseStep 713507 = 1070261) B1070261
theorem B713537 : Blo 471786 713537 := bstep (se 2 (by rfl) ⟨267576, by rfl⟩ : syracuseStep 713537 = 535153) B535153
theorem B713555 : Blo 471786 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B713585 : Blo 471786 713585 := bstep (se 2 (by rfl) ⟨267594, by rfl⟩ : syracuseStep 713585 = 535189) B535189
theorem B713603 : Blo 471786 713603 := bstep (se 1 (by rfl) ⟨535202, by rfl⟩ : syracuseStep 713603 = 1070405) B1070405
theorem B713633 : Blo 471786 713633 := bstep (se 2 (by rfl) ⟨267612, by rfl⟩ : syracuseStep 713633 = 535225) B535225
theorem B713651 : Blo 471786 713651 := bstep (se 1 (by rfl) ⟨535238, by rfl⟩ : syracuseStep 713651 = 1070477) B1070477
theorem B1729507 : Blo 471786 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B812035 : Blo 471786 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B1139761 : Blo 471786 1139761 := bstep (se 2 (by rfl) ⟨427410, by rfl⟩ : syracuseStep 1139761 = 854821) B854821
theorem B1598669 : Blo 471786 1598669 := bstep (se 3 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 1598669 = 599501) B599501
theorem B1598723 : Blo 471786 1598723 := bstep (se 1 (by rfl) ⟨1199042, by rfl⟩ : syracuseStep 1598723 = 2398085) B2398085
theorem B1926413 : Blo 471786 1926413 := bstep (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) B722405
theorem B1795405 : Blo 471786 1795405 := bstep (se 3 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 1795405 = 673277) B673277
theorem B1369457 : Blo 471786 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1009027 : Blo 471786 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B1926605 : Blo 471786 1926605 := bstep (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) B722477
theorem B1598993 : Blo 471786 1598993 := bstep (se 2 (by rfl) ⟨599622, by rfl⟩ : syracuseStep 1598993 = 1199245) B1199245
theorem B1009361 : Blo 471786 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B681955 : Blo 471786 681955 := bstep (se 1 (by rfl) ⟨511466, by rfl⟩ : syracuseStep 681955 = 1022933) B1022933
theorem B1599533 : Blo 471786 1599533 := bstep (se 3 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 1599533 = 599825) B599825
theorem B1796195 : Blo 471786 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1599587 : Blo 471786 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B1108081 : Blo 471786 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B1599857 : Blo 471786 1599857 := bstep (se 2 (by rfl) ⟨599946, by rfl⟩ : syracuseStep 1599857 = 1199893) B1199893
theorem B18147725 : Blo 471786 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B1370609 : Blo 471786 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B5139085 : Blo 471786 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B1796849 : Blo 471786 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B1010531 : Blo 471786 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B1600397 : Blo 471786 1600397 := bstep (se 3 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 1600397 = 600149) B600149
theorem B1600451 : Blo 471786 1600451 := bstep (se 1 (by rfl) ⟨1200338, by rfl⟩ : syracuseStep 1600451 = 2400677) B2400677
theorem B1076291 : Blo 471786 1076291 := bstep (se 1 (by rfl) ⟨807218, by rfl⟩ : syracuseStep 1076291 = 1614437) B1614437
theorem B1600721 : Blo 471786 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B6057443 : Blo 471786 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B2027213 : Blo 471786 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B1601261 : Blo 471786 1601261 := bstep (se 3 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 1601261 = 600473) B600473
theorem B1601315 : Blo 471786 1601315 := bstep (se 1 (by rfl) ⟨1200986, by rfl⟩ : syracuseStep 1601315 = 2401973) B2401973
theorem B2027555 : Blo 471786 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B1601585 : Blo 471786 1601585 := bstep (se 2 (by rfl) ⟨600594, by rfl⟩ : syracuseStep 1601585 = 1201189) B1201189
theorem B1798307 : Blo 471786 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B1798321 : Blo 471786 1798321 := bstep (se 2 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 1798321 = 1348741) B1348741
theorem B3338437 : Blo 471786 3338437 := bstep (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) B625957
theorem B2028017 : Blo 471786 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B1602125 : Blo 471786 1602125 := bstep (se 3 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 1602125 = 600797) B600797
theorem B1602179 : Blo 471786 1602179 := bstep (se 1 (by rfl) ⟨1201634, by rfl⟩ : syracuseStep 1602179 = 2403269) B2403269
theorem B1372963 : Blo 471786 1372963 := bstep (se 1 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 1372963 = 2059445) B2059445
theorem B1012547 : Blo 471786 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B2552717 : Blo 471786 2552717 := bstep (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) B957269
theorem B1602449 : Blo 471786 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B914449 : Blo 471786 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B718001 : Blo 471786 718001 := bstep (se 2 (by rfl) ⟨269250, by rfl⟩ : syracuseStep 718001 = 538501) B538501
theorem B1602989 : Blo 471786 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B1603043 : Blo 471786 1603043 := bstep (se 1 (by rfl) ⟨1202282, by rfl⟩ : syracuseStep 1603043 = 2404565) B2404565
theorem B5174837 : Blo 471786 5174837 := bstep (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) B485141
theorem B1799779 : Blo 471786 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B1603313 : Blo 471786 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B1276145 : Blo 471786 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B1603853 : Blo 471786 1603853 := bstep (se 3 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 1603853 = 601445) B601445
theorem B1603907 : Blo 471786 1603907 := bstep (se 1 (by rfl) ⟨1202930, by rfl⟩ : syracuseStep 1603907 = 2405861) B2405861
theorem B3045923 : Blo 471786 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B1604177 : Blo 471786 1604177 := bstep (se 2 (by rfl) ⟨601566, by rfl⟩ : syracuseStep 1604177 = 1203133) B1203133
theorem B1080067 : Blo 471786 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1669901 : Blo 471786 1669901 := bstep (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) B626213
theorem B1014563 : Blo 471786 1014563 := bstep (se 1 (by rfl) ⟨760922, by rfl⟩ : syracuseStep 1014563 = 1521845) B1521845
theorem B1276781 : Blo 471786 1276781 := bstep (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) B478793
theorem B4062149 : Blo 471786 4062149 := bstep (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) B761653
theorem B850979 : Blo 471786 850979 := bstep (se 1 (by rfl) ⟨638234, by rfl⟩ : syracuseStep 850979 = 1276469) B1276469
theorem B2849869 : Blo 471786 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1604717 : Blo 471786 1604717 := bstep (se 3 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 1604717 = 601769) B601769
theorem B1604771 : Blo 471786 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B1277137 : Blo 471786 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B2391281 : Blo 471786 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B851267 : Blo 471786 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B1605041 : Blo 471786 1605041 := bstep (se 2 (by rfl) ⟨601890, by rfl⟩ : syracuseStep 1605041 = 1203781) B1203781
theorem B6094349 : Blo 471786 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B1801997 : Blo 471786 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B1605581 : Blo 471786 1605581 := bstep (se 3 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 1605581 = 602093) B602093
theorem B2031587 : Blo 471786 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B34930763 : Blo 471786 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B1802513 : Blo 471786 1802513 := bstep (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) B1351885
theorem B1409501 : Blo 471786 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B1245719 : Blo 471786 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1704493 : Blo 471786 1704493 := bstep (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) B639185
theorem B1704523 : Blo 471786 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B1802969 : Blo 471786 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B1803181 : Blo 471786 1803181 := bstep (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) B676193
theorem B1279127 : Blo 471786 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B1803485 : Blo 471786 1803485 := bstep (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) B676307
theorem B2393873 : Blo 471786 2393873 := bstep (se 2 (by rfl) ⟨897702, by rfl⟩ : syracuseStep 2393873 = 1795405) B1795405
theorem B2394035 : Blo 471786 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B5114177 : Blo 471786 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B6490469 : Blo 471786 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B8096273 : Blo 471786 8096273 := bstep (se 2 (by rfl) ⟨3036102, by rfl⟩ : syracuseStep 8096273 = 6072205) B6072205
theorem B2886209 : Blo 471786 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B690955 : Blo 471786 690955 := bstep (se 1 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 690955 = 1036433) B1036433
theorem B1346327 : Blo 471786 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1477441 : Blo 471786 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B2165825 : Blo 471786 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B7310411 : Blo 471786 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B5770673 : Blo 471786 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B6852113 : Blo 471786 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B1806083 : Blo 471786 1806083 := bstep (se 1 (by rfl) ⟨1354562, by rfl⟩ : syracuseStep 1806083 = 2709125) B2709125
theorem B1806097 : Blo 471786 1806097 := bstep (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) B1354573
theorem B2395979 : Blo 471786 2395979 := bstep (se 1 (by rfl) ⟨1796984, by rfl⟩ : syracuseStep 2395979 = 3593969) B3593969
theorem B15175603 : Blo 471786 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B1806401 : Blo 471786 1806401 := bstep (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) B1354801
theorem B757847 : Blo 471786 757847 := bstep (se 1 (by rfl) ⟨568385, by rfl⟩ : syracuseStep 757847 = 1136771) B1136771
theorem B3281075 : Blo 471786 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B758155 : Blo 471786 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B856499 : Blo 471786 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B1446365 : Blo 471786 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B2691629 : Blo 471786 2691629 := bstep (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) B1009361
theorem B758411 : Blo 471786 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B856961 : Blo 471786 856961 := bstep (se 2 (by rfl) ⟨321360, by rfl⟩ : syracuseStep 856961 = 642721) B642721
theorem B3609521 : Blo 471786 3609521 := bstep (se 2 (by rfl) ⟨1353570, by rfl⟩ : syracuseStep 3609521 = 2707141) B2707141
theorem B1348787 : Blo 471786 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B4560077 : Blo 471786 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B4035905 : Blo 471786 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B4330853 : Blo 471786 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B3610007 : Blo 471786 3610007 := bstep (se 1 (by rfl) ⟨2707505, by rfl⟩ : syracuseStep 3610007 = 5415011) B5415011
theorem B2397761 : Blo 471786 2397761 := bstep (se 2 (by rfl) ⟨899160, by rfl⟩ : syracuseStep 2397761 = 1798321) B1798321
theorem B759385 : Blo 471786 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B17536945 : Blo 471786 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B5380019 : Blo 471786 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B1284275 : Blo 471786 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B530923 : Blo 471786 530923 := bstep (se 1 (by rfl) ⟨398192, by rfl⟩ : syracuseStep 530923 = 796385) B796385
theorem B2431505 : Blo 471786 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B531031 : Blo 471786 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B1219265 : Blo 471786 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B531211 : Blo 471786 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B531319 : Blo 471786 531319 := bstep (se 1 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 531319 = 796979) B796979
theorem B2694019 : Blo 471786 2694019 := bstep (se 1 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 2694019 = 4041029) B4041029
theorem B12098483 : Blo 471786 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B1285085 : Blo 471786 1285085 := bstep (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) B481907
theorem B531499 : Blo 471786 531499 := bstep (se 1 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 531499 = 797249) B797249
theorem B531607 : Blo 471786 531607 := bstep (se 1 (by rfl) ⟨398705, by rfl⟩ : syracuseStep 531607 = 797411) B797411
theorem B531787 : Blo 471786 531787 := bstep (se 1 (by rfl) ⟨398840, by rfl⟩ : syracuseStep 531787 = 797681) B797681
theorem B5381477 : Blo 471786 5381477 := bstep (se 4 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 5381477 = 1009027) B1009027
theorem B531895 : Blo 471786 531895 := bstep (se 1 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 531895 = 797843) B797843
theorem B597451 : Blo 471786 597451 := bstep (se 1 (by rfl) ⟨448088, by rfl⟩ : syracuseStep 597451 = 896177) B896177
theorem B2399705 : Blo 471786 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B3284525 : Blo 471786 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B532075 : Blo 471786 532075 := bstep (se 1 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 532075 = 798113) B798113
theorem B4038295 : Blo 471786 4038295 := bstep (se 1 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 4038295 = 6057443) B6057443
theorem B597719 : Blo 471786 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B532183 : Blo 471786 532183 := bstep (se 1 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 532183 = 798275) B798275
theorem B1351475 : Blo 471786 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B2694977 : Blo 471786 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B1711961 : Blo 471786 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B532363 : Blo 471786 532363 := bstep (se 1 (by rfl) ⟨399272, by rfl⟩ : syracuseStep 532363 = 798545) B798545
theorem B532471 : Blo 471786 532471 := bstep (se 1 (by rfl) ⟨399353, by rfl⟩ : syracuseStep 532471 = 798707) B798707
theorem B1351703 : Blo 471786 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B532651 : Blo 471786 532651 := bstep (se 1 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 532651 = 798977) B798977
theorem B532759 : Blo 471786 532759 := bstep (se 1 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 532759 = 799139) B799139
theorem B1352011 : Blo 471786 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B598423 : Blo 471786 598423 := bstep (se 1 (by rfl) ⟨448817, by rfl⟩ : syracuseStep 598423 = 897635) B897635
theorem B532939 : Blo 471786 532939 := bstep (se 1 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 532939 = 799409) B799409
theorem B533047 : Blo 471786 533047 := bstep (se 1 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 533047 = 799571) B799571
theorem B1352285 : Blo 471786 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B533227 : Blo 471786 533227 := bstep (se 1 (by rfl) ⟨399920, by rfl⟩ : syracuseStep 533227 = 799841) B799841
theorem B533335 : Blo 471786 533335 := bstep (se 1 (by rfl) ⟨400001, by rfl⟩ : syracuseStep 533335 = 800003) B800003
theorem B2270045 : Blo 471786 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B533515 : Blo 471786 533515 := bstep (se 1 (by rfl) ⟨400136, by rfl⟩ : syracuseStep 533515 = 800273) B800273
theorem B3449891 : Blo 471786 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2401325 : Blo 471786 2401325 := bstep (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) B900497
theorem B533623 : Blo 471786 533623 := bstep (se 1 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 533623 = 800435) B800435
theorem B533803 : Blo 471786 533803 := bstep (se 1 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 533803 = 800705) B800705
theorem B2893121 : Blo 471786 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B533911 : Blo 471786 533911 := bstep (se 1 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 533911 = 800867) B800867
theorem B2729537 : Blo 471786 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B534091 : Blo 471786 534091 := bstep (se 1 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 534091 = 801137) B801137
theorem B861785 : Blo 471786 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B534199 : Blo 471786 534199 := bstep (se 1 (by rfl) ⟨400649, by rfl⟩ : syracuseStep 534199 = 801299) B801299
theorem B927425 : Blo 471786 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B796439 : Blo 471786 796439 := bstep (se 1 (by rfl) ⟨597329, by rfl⟩ : syracuseStep 796439 = 1194659) B1194659
theorem B534379 : Blo 471786 534379 := bstep (se 1 (by rfl) ⟨400784, by rfl⟩ : syracuseStep 534379 = 801569) B801569
theorem B2566019 : Blo 471786 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B796567 : Blo 471786 796567 := bstep (se 1 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 796567 = 1194851) B1194851
theorem B2566039 : Blo 471786 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B534487 : Blo 471786 534487 := bstep (se 1 (by rfl) ⟨400865, by rfl⟩ : syracuseStep 534487 = 801731) B801731
theorem B567319 : Blo 471786 567319 := bstep (se 1 (by rfl) ⟨425489, by rfl⟩ : syracuseStep 567319 = 850979) B850979
theorem B1517591 : Blo 471786 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B600139 : Blo 471786 600139 := bstep (se 1 (by rfl) ⟨450104, by rfl⟩ : syracuseStep 600139 = 900209) B900209
theorem B3418213 : Blo 471786 3418213 := bstep (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) B640915
theorem B534667 : Blo 471786 534667 := bstep (se 1 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 534667 = 802001) B802001
theorem B1517771 : Blo 471786 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B534775 : Blo 471786 534775 := bstep (se 1 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 534775 = 802163) B802163
theorem B5122349 : Blo 471786 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B1517899 : Blo 471786 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B534955 : Blo 471786 534955 := bstep (se 1 (by rfl) ⟨401216, by rfl⟩ : syracuseStep 534955 = 802433) B802433
theorem B6498737 : Blo 471786 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B1518041 : Blo 471786 1518041 := bstep (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) B1138531
theorem B797195 : Blo 471786 797195 := bstep (se 1 (by rfl) ⟨597896, by rfl⟩ : syracuseStep 797195 = 1195793) B1195793
theorem B535063 : Blo 471786 535063 := bstep (se 1 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 535063 = 802595) B802595
theorem B1518155 : Blo 471786 1518155 := bstep (se 1 (by rfl) ⟨1138616, by rfl⟩ : syracuseStep 1518155 = 2277233) B2277233
theorem B797323 : Blo 471786 797323 := bstep (se 1 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 797323 = 1195985) B1195985
theorem B1354391 : Blo 471786 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B895691 : Blo 471786 895691 := bstep (se 1 (by rfl) ⟨671768, by rfl⟩ : syracuseStep 895691 = 1343537) B1343537
theorem B535243 : Blo 471786 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B797465 : Blo 471786 797465 := bstep (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) B598099
theorem B3910493 : Blo 471786 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B895873 : Blo 471786 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B797593 : Blo 471786 797593 := bstep (se 2 (by rfl) ⟨299097, by rfl⟩ : syracuseStep 797593 = 598195) B598195
theorem B568343 : Blo 471786 568343 := bstep (se 1 (by rfl) ⟨426257, by rfl⟩ : syracuseStep 568343 = 852515) B852515
theorem B601111 : Blo 471786 601111 := bstep (se 1 (by rfl) ⟨450833, by rfl⟩ : syracuseStep 601111 = 901667) B901667
theorem B3583277 : Blo 471786 3583277 := bstep (se 3 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 3583277 = 1343729) B1343729
theorem B896321 : Blo 471786 896321 := bstep (se 2 (by rfl) ⟨336120, by rfl⟩ : syracuseStep 896321 = 672241) B672241
theorem B798167 : Blo 471786 798167 := bstep (se 1 (by rfl) ⟨598625, by rfl⟩ : syracuseStep 798167 = 1197251) B1197251
theorem B31075811 : Blo 471786 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B798295 : Blo 471786 798295 := bstep (se 1 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 798295 = 1197443) B1197443
theorem B896663 : Blo 471786 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B1519411 : Blo 471786 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B601931 : Blo 471786 601931 := bstep (se 1 (by rfl) ⟨451448, by rfl⟩ : syracuseStep 601931 = 902897) B902897
theorem B2306009 : Blo 471786 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B1519681 : Blo 471786 1519681 := bstep (se 2 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 1519681 = 1139761) B1139761
theorem B7319645 : Blo 471786 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B798923 : Blo 471786 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B569611 : Blo 471786 569611 := bstep (se 1 (by rfl) ⟨427208, by rfl⟩ : syracuseStep 569611 = 854417) B854417
theorem B3420461 : Blo 471786 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B897331 : Blo 471786 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B799051 : Blo 471786 799051 := bstep (se 1 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 799051 = 1198577) B1198577
theorem B799193 : Blo 471786 799193 := bstep (se 2 (by rfl) ⟨299697, by rfl⟩ : syracuseStep 799193 = 599395) B599395
theorem B22196753 : Blo 471786 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B504343 : Blo 471786 504343 := bstep (se 1 (by rfl) ⟨378257, by rfl⟩ : syracuseStep 504343 = 756515) B756515
theorem B2699851 : Blo 471786 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B799321 : Blo 471786 799321 := bstep (se 2 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 799321 = 599491) B599491
theorem B471787 : Blo 471786 471787 := bstep (se 1 (by rfl) ⟨353840, by rfl⟩ : syracuseStep 471787 = 707681) B707681
theorem B897779 : Blo 471786 897779 := bstep (se 1 (by rfl) ⟨673334, by rfl⟩ : syracuseStep 897779 = 1346669) B1346669
theorem B471799 : Blo 471786 471799 := bstep (se 1 (by rfl) ⟨353849, by rfl⟩ : syracuseStep 471799 = 707699) B707699
theorem B471819 : Blo 471786 471819 := bstep (se 1 (by rfl) ⟨353864, by rfl⟩ : syracuseStep 471819 = 707729) B707729
theorem B471831 : Blo 471786 471831 := bstep (se 1 (by rfl) ⟨353873, by rfl⟩ : syracuseStep 471831 = 707747) B707747
theorem B1061657 : Blo 471786 1061657 := bstep (se 2 (by rfl) ⟨398121, by rfl⟩ : syracuseStep 1061657 = 796243) B796243
theorem B897817 : Blo 471786 897817 := bstep (se 2 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 897817 = 673363) B673363
theorem B471851 : Blo 471786 471851 := bstep (se 1 (by rfl) ⟨353888, by rfl⟩ : syracuseStep 471851 = 707777) B707777
theorem B471863 : Blo 471786 471863 := bstep (se 1 (by rfl) ⟨353897, by rfl⟩ : syracuseStep 471863 = 707795) B707795
theorem B471883 : Blo 471786 471883 := bstep (se 1 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 471883 = 707825) B707825
theorem B471895 : Blo 471786 471895 := bstep (se 1 (by rfl) ⟨353921, by rfl⟩ : syracuseStep 471895 = 707843) B707843
theorem B2700125 : Blo 471786 2700125 := bstep (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) B1012547
theorem B2405213 : Blo 471786 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B471915 : Blo 471786 471915 := bstep (se 1 (by rfl) ⟨353936, by rfl⟩ : syracuseStep 471915 = 707873) B707873
theorem B1061747 : Blo 471786 1061747 := bstep (se 1 (by rfl) ⟨796310, by rfl⟩ : syracuseStep 1061747 = 1592621) B1592621
theorem B471927 : Blo 471786 471927 := bstep (se 1 (by rfl) ⟨353945, by rfl⟩ : syracuseStep 471927 = 707891) B707891
theorem B471947 : Blo 471786 471947 := bstep (se 1 (by rfl) ⟨353960, by rfl⟩ : syracuseStep 471947 = 707921) B707921
theorem B1061783 : Blo 471786 1061783 := bstep (se 1 (by rfl) ⟨796337, by rfl⟩ : syracuseStep 1061783 = 1592675) B1592675
theorem B471959 : Blo 471786 471959 := bstep (se 1 (by rfl) ⟨353969, by rfl⟩ : syracuseStep 471959 = 707939) B707939
theorem B471979 : Blo 471786 471979 := bstep (se 1 (by rfl) ⟨353984, by rfl⟩ : syracuseStep 471979 = 707969) B707969
theorem B471991 : Blo 471786 471991 := bstep (se 1 (by rfl) ⟨353993, by rfl⟩ : syracuseStep 471991 = 707987) B707987
theorem B472011 : Blo 471786 472011 := bstep (se 1 (by rfl) ⟨354008, by rfl⟩ : syracuseStep 472011 = 708017) B708017
theorem B472023 : Blo 471786 472023 := bstep (se 1 (by rfl) ⟨354017, by rfl⟩ : syracuseStep 472023 = 708035) B708035
theorem B472043 : Blo 471786 472043 := bstep (se 1 (by rfl) ⟨354032, by rfl⟩ : syracuseStep 472043 = 708065) B708065
theorem B472055 : Blo 471786 472055 := bstep (se 1 (by rfl) ⟨354041, by rfl⟩ : syracuseStep 472055 = 708083) B708083
theorem B472075 : Blo 471786 472075 := bstep (se 1 (by rfl) ⟨354056, by rfl⟩ : syracuseStep 472075 = 708113) B708113
theorem B472087 : Blo 471786 472087 := bstep (se 1 (by rfl) ⟨354065, by rfl⟩ : syracuseStep 472087 = 708131) B708131
theorem B472107 : Blo 471786 472107 := bstep (se 1 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 472107 = 708161) B708161
theorem B472119 : Blo 471786 472119 := bstep (se 1 (by rfl) ⟨354089, by rfl⟩ : syracuseStep 472119 = 708179) B708179
theorem B1061963 : Blo 471786 1061963 := bstep (se 1 (by rfl) ⟨796472, by rfl⟩ : syracuseStep 1061963 = 1592945) B1592945
theorem B472139 : Blo 471786 472139 := bstep (se 1 (by rfl) ⟨354104, by rfl⟩ : syracuseStep 472139 = 708209) B708209
theorem B472151 : Blo 471786 472151 := bstep (se 1 (by rfl) ⟨354113, by rfl⟩ : syracuseStep 472151 = 708227) B708227
theorem B472171 : Blo 471786 472171 := bstep (se 1 (by rfl) ⟨354128, by rfl⟩ : syracuseStep 472171 = 708257) B708257
theorem B472183 : Blo 471786 472183 := bstep (se 1 (by rfl) ⟨354137, by rfl⟩ : syracuseStep 472183 = 708275) B708275
theorem B1062017 : Blo 471786 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B472203 : Blo 471786 472203 := bstep (se 1 (by rfl) ⟨354152, by rfl⟩ : syracuseStep 472203 = 708305) B708305
theorem B472215 : Blo 471786 472215 := bstep (se 1 (by rfl) ⟨354161, by rfl⟩ : syracuseStep 472215 = 708323) B708323
theorem B799895 : Blo 471786 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B472235 : Blo 471786 472235 := bstep (se 1 (by rfl) ⟨354176, by rfl⟩ : syracuseStep 472235 = 708353) B708353
theorem B472247 : Blo 471786 472247 := bstep (se 1 (by rfl) ⟨354185, by rfl⟩ : syracuseStep 472247 = 708371) B708371
theorem B472267 : Blo 471786 472267 := bstep (se 1 (by rfl) ⟨354200, by rfl⟩ : syracuseStep 472267 = 708401) B708401
theorem B472279 : Blo 471786 472279 := bstep (se 1 (by rfl) ⟨354209, by rfl⟩ : syracuseStep 472279 = 708419) B708419
theorem B898265 : Blo 471786 898265 := bstep (se 2 (by rfl) ⟨336849, by rfl⟩ : syracuseStep 898265 = 673699) B673699
theorem B472299 : Blo 471786 472299 := bstep (se 1 (by rfl) ⟨354224, by rfl⟩ : syracuseStep 472299 = 708449) B708449
theorem B472311 : Blo 471786 472311 := bstep (se 1 (by rfl) ⟨354233, by rfl⟩ : syracuseStep 472311 = 708467) B708467
theorem B472331 : Blo 471786 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B472343 : Blo 471786 472343 := bstep (se 1 (by rfl) ⟨354257, by rfl⟩ : syracuseStep 472343 = 708515) B708515
theorem B800023 : Blo 471786 800023 := bstep (se 1 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 800023 = 1200035) B1200035
theorem B472363 : Blo 471786 472363 := bstep (se 1 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 472363 = 708545) B708545
theorem B472375 : Blo 471786 472375 := bstep (se 1 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 472375 = 708563) B708563
theorem B472395 : Blo 471786 472395 := bstep (se 1 (by rfl) ⟨354296, by rfl⟩ : syracuseStep 472395 = 708593) B708593
theorem B505163 : Blo 471786 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B472407 : Blo 471786 472407 := bstep (se 1 (by rfl) ⟨354305, by rfl⟩ : syracuseStep 472407 = 708611) B708611
theorem B1062233 : Blo 471786 1062233 := bstep (se 2 (by rfl) ⟨398337, by rfl⟩ : syracuseStep 1062233 = 796675) B796675
theorem B472427 : Blo 471786 472427 := bstep (se 1 (by rfl) ⟨354320, by rfl⟩ : syracuseStep 472427 = 708641) B708641
theorem B472439 : Blo 471786 472439 := bstep (se 1 (by rfl) ⟨354329, by rfl⟩ : syracuseStep 472439 = 708659) B708659
theorem B472459 : Blo 471786 472459 := bstep (se 1 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 472459 = 708689) B708689
theorem B472471 : Blo 471786 472471 := bstep (se 1 (by rfl) ⟨354353, by rfl⟩ : syracuseStep 472471 = 708707) B708707
theorem B472491 : Blo 471786 472491 := bstep (se 1 (by rfl) ⟨354368, by rfl⟩ : syracuseStep 472491 = 708737) B708737
theorem B1062323 : Blo 471786 1062323 := bstep (se 1 (by rfl) ⟨796742, by rfl⟩ : syracuseStep 1062323 = 1593485) B1593485
theorem B472503 : Blo 471786 472503 := bstep (se 1 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 472503 = 708755) B708755
theorem B472523 : Blo 471786 472523 := bstep (se 1 (by rfl) ⟨354392, by rfl⟩ : syracuseStep 472523 = 708785) B708785
theorem B1062359 : Blo 471786 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B472535 : Blo 471786 472535 := bstep (se 1 (by rfl) ⟨354401, by rfl⟩ : syracuseStep 472535 = 708803) B708803
theorem B472555 : Blo 471786 472555 := bstep (se 1 (by rfl) ⟨354416, by rfl⟩ : syracuseStep 472555 = 708833) B708833
theorem B472567 : Blo 471786 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B472587 : Blo 471786 472587 := bstep (se 1 (by rfl) ⟨354440, by rfl⟩ : syracuseStep 472587 = 708881) B708881
theorem B472599 : Blo 471786 472599 := bstep (se 1 (by rfl) ⟨354449, by rfl⟩ : syracuseStep 472599 = 708899) B708899
theorem B472619 : Blo 471786 472619 := bstep (se 1 (by rfl) ⟨354464, by rfl⟩ : syracuseStep 472619 = 708929) B708929
theorem B472631 : Blo 471786 472631 := bstep (se 1 (by rfl) ⟨354473, by rfl⟩ : syracuseStep 472631 = 708947) B708947
theorem B472651 : Blo 471786 472651 := bstep (se 1 (by rfl) ⟨354488, by rfl⟩ : syracuseStep 472651 = 708977) B708977
theorem B472663 : Blo 471786 472663 := bstep (se 1 (by rfl) ⟨354497, by rfl⟩ : syracuseStep 472663 = 708995) B708995
theorem B472683 : Blo 471786 472683 := bstep (se 1 (by rfl) ⟨354512, by rfl⟩ : syracuseStep 472683 = 709025) B709025
theorem B472695 : Blo 471786 472695 := bstep (se 1 (by rfl) ⟨354521, by rfl⟩ : syracuseStep 472695 = 709043) B709043
theorem B1062539 : Blo 471786 1062539 := bstep (se 1 (by rfl) ⟨796904, by rfl⟩ : syracuseStep 1062539 = 1593809) B1593809
theorem B472715 : Blo 471786 472715 := bstep (se 1 (by rfl) ⟨354536, by rfl⟩ : syracuseStep 472715 = 709073) B709073
theorem B472727 : Blo 471786 472727 := bstep (se 1 (by rfl) ⟨354545, by rfl⟩ : syracuseStep 472727 = 709091) B709091
theorem B472747 : Blo 471786 472747 := bstep (se 1 (by rfl) ⟨354560, by rfl⟩ : syracuseStep 472747 = 709121) B709121
theorem B472759 : Blo 471786 472759 := bstep (se 1 (by rfl) ⟨354569, by rfl⟩ : syracuseStep 472759 = 709139) B709139
theorem B1062593 : Blo 471786 1062593 := bstep (se 2 (by rfl) ⟨398472, by rfl⟩ : syracuseStep 1062593 = 796945) B796945
theorem B472779 : Blo 471786 472779 := bstep (se 1 (by rfl) ⟨354584, by rfl⟩ : syracuseStep 472779 = 709169) B709169
theorem B472791 : Blo 471786 472791 := bstep (se 1 (by rfl) ⟨354593, by rfl⟩ : syracuseStep 472791 = 709187) B709187
theorem B472811 : Blo 471786 472811 := bstep (se 1 (by rfl) ⟨354608, by rfl⟩ : syracuseStep 472811 = 709217) B709217
theorem B472823 : Blo 471786 472823 := bstep (se 1 (by rfl) ⟨354617, by rfl⟩ : syracuseStep 472823 = 709235) B709235
theorem B472843 : Blo 471786 472843 := bstep (se 1 (by rfl) ⟨354632, by rfl⟩ : syracuseStep 472843 = 709265) B709265
theorem B472855 : Blo 471786 472855 := bstep (se 1 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 472855 = 709283) B709283
theorem B472875 : Blo 471786 472875 := bstep (se 1 (by rfl) ⟨354656, by rfl⟩ : syracuseStep 472875 = 709313) B709313
theorem B472887 : Blo 471786 472887 := bstep (se 1 (by rfl) ⟨354665, by rfl⟩ : syracuseStep 472887 = 709331) B709331
theorem B472907 : Blo 471786 472907 := bstep (se 1 (by rfl) ⟨354680, by rfl⟩ : syracuseStep 472907 = 709361) B709361
theorem B472919 : Blo 471786 472919 := bstep (se 1 (by rfl) ⟨354689, by rfl⟩ : syracuseStep 472919 = 709379) B709379
theorem B472939 : Blo 471786 472939 := bstep (se 1 (by rfl) ⟨354704, by rfl⟩ : syracuseStep 472939 = 709409) B709409
theorem B472951 : Blo 471786 472951 := bstep (se 1 (by rfl) ⟨354713, by rfl⟩ : syracuseStep 472951 = 709427) B709427
theorem B472971 : Blo 471786 472971 := bstep (se 1 (by rfl) ⟨354728, by rfl⟩ : syracuseStep 472971 = 709457) B709457
theorem B800651 : Blo 471786 800651 := bstep (se 1 (by rfl) ⟨600488, by rfl⟩ : syracuseStep 800651 = 1200977) B1200977
theorem B472983 : Blo 471786 472983 := bstep (se 1 (by rfl) ⟨354737, by rfl⟩ : syracuseStep 472983 = 709475) B709475
theorem B1062809 : Blo 471786 1062809 := bstep (se 2 (by rfl) ⟨398553, by rfl⟩ : syracuseStep 1062809 = 797107) B797107
theorem B473003 : Blo 471786 473003 := bstep (se 1 (by rfl) ⟨354752, by rfl⟩ : syracuseStep 473003 = 709505) B709505
theorem B473015 : Blo 471786 473015 := bstep (se 1 (by rfl) ⟨354761, by rfl⟩ : syracuseStep 473015 = 709523) B709523
theorem B899009 : Blo 471786 899009 := bstep (se 2 (by rfl) ⟨337128, by rfl⟩ : syracuseStep 899009 = 674257) B674257
theorem B473035 : Blo 471786 473035 := bstep (se 1 (by rfl) ⟨354776, by rfl⟩ : syracuseStep 473035 = 709553) B709553
theorem B538583 : Blo 471786 538583 := bstep (se 1 (by rfl) ⟨403937, by rfl⟩ : syracuseStep 538583 = 807875) B807875
theorem B473047 : Blo 471786 473047 := bstep (se 1 (by rfl) ⟨354785, by rfl⟩ : syracuseStep 473047 = 709571) B709571
theorem B1521629 : Blo 471786 1521629 := bstep (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) B570611
theorem B473067 : Blo 471786 473067 := bstep (se 1 (by rfl) ⟨354800, by rfl⟩ : syracuseStep 473067 = 709601) B709601
theorem B1062899 : Blo 471786 1062899 := bstep (se 1 (by rfl) ⟨797174, by rfl⟩ : syracuseStep 1062899 = 1594349) B1594349
theorem B473079 : Blo 471786 473079 := bstep (se 1 (by rfl) ⟨354809, by rfl⟩ : syracuseStep 473079 = 709619) B709619
theorem B473099 : Blo 471786 473099 := bstep (se 1 (by rfl) ⟨354824, by rfl⟩ : syracuseStep 473099 = 709649) B709649
theorem B800779 : Blo 471786 800779 := bstep (se 1 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 800779 = 1201169) B1201169
theorem B1062935 : Blo 471786 1062935 := bstep (se 1 (by rfl) ⟨797201, by rfl⟩ : syracuseStep 1062935 = 1594403) B1594403
theorem B473111 : Blo 471786 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B473131 : Blo 471786 473131 := bstep (se 1 (by rfl) ⟨354848, by rfl⟩ : syracuseStep 473131 = 709697) B709697
theorem B473143 : Blo 471786 473143 := bstep (se 1 (by rfl) ⟨354857, by rfl⟩ : syracuseStep 473143 = 709715) B709715
theorem B473163 : Blo 471786 473163 := bstep (se 1 (by rfl) ⟨354872, by rfl⟩ : syracuseStep 473163 = 709745) B709745
theorem B473175 : Blo 471786 473175 := bstep (se 1 (by rfl) ⟨354881, by rfl⟩ : syracuseStep 473175 = 709763) B709763
theorem B473195 : Blo 471786 473195 := bstep (se 1 (by rfl) ⟨354896, by rfl⟩ : syracuseStep 473195 = 709793) B709793
theorem B473207 : Blo 471786 473207 := bstep (se 1 (by rfl) ⟨354905, by rfl⟩ : syracuseStep 473207 = 709811) B709811
theorem B473227 : Blo 471786 473227 := bstep (se 1 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 473227 = 709841) B709841
theorem B473239 : Blo 471786 473239 := bstep (se 1 (by rfl) ⟨354929, by rfl⟩ : syracuseStep 473239 = 709859) B709859
theorem B800921 : Blo 471786 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B473259 : Blo 471786 473259 := bstep (se 1 (by rfl) ⟨354944, by rfl⟩ : syracuseStep 473259 = 709889) B709889
theorem B473271 : Blo 471786 473271 := bstep (se 1 (by rfl) ⟨354953, by rfl⟩ : syracuseStep 473271 = 709907) B709907
theorem B1063115 : Blo 471786 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B473291 : Blo 471786 473291 := bstep (se 1 (by rfl) ⟨354968, by rfl⟩ : syracuseStep 473291 = 709937) B709937
theorem B899275 : Blo 471786 899275 := bstep (se 1 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 899275 = 1348913) B1348913
theorem B473303 : Blo 471786 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B473323 : Blo 471786 473323 := bstep (se 1 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 473323 = 709985) B709985
theorem B473335 : Blo 471786 473335 := bstep (se 1 (by rfl) ⟨355001, by rfl⟩ : syracuseStep 473335 = 710003) B710003
theorem B1063169 : Blo 471786 1063169 := bstep (se 2 (by rfl) ⟨398688, by rfl⟩ : syracuseStep 1063169 = 797377) B797377
theorem B473355 : Blo 471786 473355 := bstep (se 1 (by rfl) ⟨355016, by rfl⟩ : syracuseStep 473355 = 710033) B710033
theorem B473367 : Blo 471786 473367 := bstep (se 1 (by rfl) ⟨355025, by rfl⟩ : syracuseStep 473367 = 710051) B710051
theorem B801049 : Blo 471786 801049 := bstep (se 2 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 801049 = 600787) B600787
theorem B473387 : Blo 471786 473387 := bstep (se 1 (by rfl) ⟨355040, by rfl⟩ : syracuseStep 473387 = 710081) B710081
theorem B473399 : Blo 471786 473399 := bstep (se 1 (by rfl) ⟨355049, by rfl⟩ : syracuseStep 473399 = 710099) B710099
theorem B473419 : Blo 471786 473419 := bstep (se 1 (by rfl) ⟨355064, by rfl⟩ : syracuseStep 473419 = 710129) B710129
theorem B473431 : Blo 471786 473431 := bstep (se 1 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 473431 = 710147) B710147
theorem B473451 : Blo 471786 473451 := bstep (se 1 (by rfl) ⟨355088, by rfl⟩ : syracuseStep 473451 = 710177) B710177
theorem B473463 : Blo 471786 473463 := bstep (se 1 (by rfl) ⟨355097, by rfl⟩ : syracuseStep 473463 = 710195) B710195
theorem B473483 : Blo 471786 473483 := bstep (se 1 (by rfl) ⟨355112, by rfl⟩ : syracuseStep 473483 = 710225) B710225
theorem B473495 : Blo 471786 473495 := bstep (se 1 (by rfl) ⟨355121, by rfl⟩ : syracuseStep 473495 = 710243) B710243
theorem B473515 : Blo 471786 473515 := bstep (se 1 (by rfl) ⟨355136, by rfl⟩ : syracuseStep 473515 = 710273) B710273
theorem B473527 : Blo 471786 473527 := bstep (se 1 (by rfl) ⟨355145, by rfl⟩ : syracuseStep 473527 = 710291) B710291
theorem B473547 : Blo 471786 473547 := bstep (se 1 (by rfl) ⟨355160, by rfl⟩ : syracuseStep 473547 = 710321) B710321
theorem B473559 : Blo 471786 473559 := bstep (se 1 (by rfl) ⟨355169, by rfl⟩ : syracuseStep 473559 = 710339) B710339
theorem B1063385 : Blo 471786 1063385 := bstep (se 2 (by rfl) ⟨398769, by rfl⟩ : syracuseStep 1063385 = 797539) B797539
theorem B473579 : Blo 471786 473579 := bstep (se 1 (by rfl) ⟨355184, by rfl⟩ : syracuseStep 473579 = 710369) B710369
theorem B473591 : Blo 471786 473591 := bstep (se 1 (by rfl) ⟨355193, by rfl⟩ : syracuseStep 473591 = 710387) B710387
theorem B506359 : Blo 471786 506359 := bstep (se 1 (by rfl) ⟨379769, by rfl⟩ : syracuseStep 506359 = 759539) B759539
theorem B473611 : Blo 471786 473611 := bstep (se 1 (by rfl) ⟨355208, by rfl⟩ : syracuseStep 473611 = 710417) B710417
theorem B10271245 : Blo 471786 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B473623 : Blo 471786 473623 := bstep (se 1 (by rfl) ⟨355217, by rfl⟩ : syracuseStep 473623 = 710435) B710435
theorem B473643 : Blo 471786 473643 := bstep (se 1 (by rfl) ⟨355232, by rfl⟩ : syracuseStep 473643 = 710465) B710465
theorem B1194547 : Blo 471786 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1063475 : Blo 471786 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B473655 : Blo 471786 473655 := bstep (se 1 (by rfl) ⟨355241, by rfl⟩ : syracuseStep 473655 = 710483) B710483
theorem B473675 : Blo 471786 473675 := bstep (se 1 (by rfl) ⟨355256, by rfl⟩ : syracuseStep 473675 = 710513) B710513
theorem B1063511 : Blo 471786 1063511 := bstep (se 1 (by rfl) ⟨797633, by rfl⟩ : syracuseStep 1063511 = 1595267) B1595267
theorem B768599 : Blo 471786 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B473687 : Blo 471786 473687 := bstep (se 1 (by rfl) ⟨355265, by rfl⟩ : syracuseStep 473687 = 710531) B710531
theorem B473707 : Blo 471786 473707 := bstep (se 1 (by rfl) ⟨355280, by rfl⟩ : syracuseStep 473707 = 710561) B710561
theorem B473719 : Blo 471786 473719 := bstep (se 1 (by rfl) ⟨355289, by rfl⟩ : syracuseStep 473719 = 710579) B710579
theorem B473739 : Blo 471786 473739 := bstep (se 1 (by rfl) ⟨355304, by rfl⟩ : syracuseStep 473739 = 710609) B710609
theorem B899723 : Blo 471786 899723 := bstep (se 1 (by rfl) ⟨674792, by rfl⟩ : syracuseStep 899723 = 1349585) B1349585
theorem B473751 : Blo 471786 473751 := bstep (se 1 (by rfl) ⟨355313, by rfl⟩ : syracuseStep 473751 = 710627) B710627
theorem B473771 : Blo 471786 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B473783 : Blo 471786 473783 := bstep (se 1 (by rfl) ⟨355337, by rfl⟩ : syracuseStep 473783 = 710675) B710675
theorem B1194689 : Blo 471786 1194689 := bstep (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) B896017
theorem B473803 : Blo 471786 473803 := bstep (se 1 (by rfl) ⟨355352, by rfl⟩ : syracuseStep 473803 = 710705) B710705
theorem B473815 : Blo 471786 473815 := bstep (se 1 (by rfl) ⟨355361, by rfl⟩ : syracuseStep 473815 = 710723) B710723
theorem B473835 : Blo 471786 473835 := bstep (se 1 (by rfl) ⟨355376, by rfl⟩ : syracuseStep 473835 = 710753) B710753
theorem B473847 : Blo 471786 473847 := bstep (se 1 (by rfl) ⟨355385, by rfl⟩ : syracuseStep 473847 = 710771) B710771
theorem B1063691 : Blo 471786 1063691 := bstep (se 1 (by rfl) ⟨797768, by rfl⟩ : syracuseStep 1063691 = 1595537) B1595537
theorem B473867 : Blo 471786 473867 := bstep (se 1 (by rfl) ⟨355400, by rfl⟩ : syracuseStep 473867 = 710801) B710801
theorem B71219989 : Blo 471786 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B473879 : Blo 471786 473879 := bstep (se 1 (by rfl) ⟨355409, by rfl⟩ : syracuseStep 473879 = 710819) B710819
theorem B473899 : Blo 471786 473899 := bstep (se 1 (by rfl) ⟨355424, by rfl⟩ : syracuseStep 473899 = 710849) B710849
theorem B1391411 : Blo 471786 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B473911 : Blo 471786 473911 := bstep (se 1 (by rfl) ⟨355433, by rfl⟩ : syracuseStep 473911 = 710867) B710867
theorem B1063745 : Blo 471786 1063745 := bstep (se 2 (by rfl) ⟨398904, by rfl⟩ : syracuseStep 1063745 = 797809) B797809
theorem B899905 : Blo 471786 899905 := bstep (se 2 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 899905 = 674929) B674929
theorem B473931 : Blo 471786 473931 := bstep (se 1 (by rfl) ⟨355448, by rfl⟩ : syracuseStep 473931 = 710897) B710897
theorem B473943 : Blo 471786 473943 := bstep (se 1 (by rfl) ⟨355457, by rfl⟩ : syracuseStep 473943 = 710915) B710915
theorem B801623 : Blo 471786 801623 := bstep (se 1 (by rfl) ⟨601217, by rfl⟩ : syracuseStep 801623 = 1202435) B1202435
theorem B473963 : Blo 471786 473963 := bstep (se 1 (by rfl) ⟨355472, by rfl⟩ : syracuseStep 473963 = 710945) B710945
theorem B506731 : Blo 471786 506731 := bstep (se 1 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 506731 = 760097) B760097
theorem B473975 : Blo 471786 473975 := bstep (se 1 (by rfl) ⟨355481, by rfl⟩ : syracuseStep 473975 = 710963) B710963
theorem B473995 : Blo 471786 473995 := bstep (se 1 (by rfl) ⟨355496, by rfl⟩ : syracuseStep 473995 = 710993) B710993
theorem B474007 : Blo 471786 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B2407319 : Blo 471786 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B474027 : Blo 471786 474027 := bstep (se 1 (by rfl) ⟨355520, by rfl⟩ : syracuseStep 474027 = 711041) B711041
theorem B474039 : Blo 471786 474039 := bstep (se 1 (by rfl) ⟨355529, by rfl⟩ : syracuseStep 474039 = 711059) B711059
theorem B474059 : Blo 471786 474059 := bstep (se 1 (by rfl) ⟨355544, by rfl⟩ : syracuseStep 474059 = 711089) B711089
theorem B474071 : Blo 471786 474071 := bstep (se 1 (by rfl) ⟨355553, by rfl⟩ : syracuseStep 474071 = 711107) B711107
theorem B801751 : Blo 471786 801751 := bstep (se 1 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 801751 = 1202627) B1202627
theorem B474091 : Blo 471786 474091 := bstep (se 1 (by rfl) ⟨355568, by rfl⟩ : syracuseStep 474091 = 711137) B711137
theorem B474103 : Blo 471786 474103 := bstep (se 1 (by rfl) ⟨355577, by rfl⟩ : syracuseStep 474103 = 711155) B711155
theorem B474123 : Blo 471786 474123 := bstep (se 1 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 474123 = 711185) B711185
theorem B474135 : Blo 471786 474135 := bstep (se 1 (by rfl) ⟨355601, by rfl⟩ : syracuseStep 474135 = 711203) B711203
theorem B1063961 : Blo 471786 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B474155 : Blo 471786 474155 := bstep (se 1 (by rfl) ⟨355616, by rfl⟩ : syracuseStep 474155 = 711233) B711233
theorem B474167 : Blo 471786 474167 := bstep (se 1 (by rfl) ⟨355625, by rfl⟩ : syracuseStep 474167 = 711251) B711251
theorem B474187 : Blo 471786 474187 := bstep (se 1 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 474187 = 711281) B711281
theorem B474199 : Blo 471786 474199 := bstep (se 1 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 474199 = 711299) B711299
theorem B3587165 : Blo 471786 3587165 := bstep (se 3 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 3587165 = 1345187) B1345187
theorem B474219 : Blo 471786 474219 := bstep (se 1 (by rfl) ⟨355664, by rfl⟩ : syracuseStep 474219 = 711329) B711329
theorem B1064051 : Blo 471786 1064051 := bstep (se 1 (by rfl) ⟨798038, by rfl⟩ : syracuseStep 1064051 = 1596077) B1596077
theorem B474231 : Blo 471786 474231 := bstep (se 1 (by rfl) ⟨355673, by rfl⟩ : syracuseStep 474231 = 711347) B711347
theorem B474251 : Blo 471786 474251 := bstep (se 1 (by rfl) ⟨355688, by rfl⟩ : syracuseStep 474251 = 711377) B711377
theorem B1064087 : Blo 471786 1064087 := bstep (se 1 (by rfl) ⟨798065, by rfl⟩ : syracuseStep 1064087 = 1596131) B1596131
theorem B900247 : Blo 471786 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B474263 : Blo 471786 474263 := bstep (se 1 (by rfl) ⟨355697, by rfl⟩ : syracuseStep 474263 = 711395) B711395
theorem B474283 : Blo 471786 474283 := bstep (se 1 (by rfl) ⟨355712, by rfl⟩ : syracuseStep 474283 = 711425) B711425
theorem B474295 : Blo 471786 474295 := bstep (se 1 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 474295 = 711443) B711443
theorem B474315 : Blo 471786 474315 := bstep (se 1 (by rfl) ⟨355736, by rfl⟩ : syracuseStep 474315 = 711473) B711473
theorem B474327 : Blo 471786 474327 := bstep (se 1 (by rfl) ⟨355745, by rfl⟩ : syracuseStep 474327 = 711491) B711491
theorem B474347 : Blo 471786 474347 := bstep (se 1 (by rfl) ⟨355760, by rfl⟩ : syracuseStep 474347 = 711521) B711521
theorem B474359 : Blo 471786 474359 := bstep (se 1 (by rfl) ⟨355769, by rfl⟩ : syracuseStep 474359 = 711539) B711539
theorem B474379 : Blo 471786 474379 := bstep (se 1 (by rfl) ⟨355784, by rfl⟩ : syracuseStep 474379 = 711569) B711569
theorem B474391 : Blo 471786 474391 := bstep (se 1 (by rfl) ⟨355793, by rfl⟩ : syracuseStep 474391 = 711587) B711587
theorem B474411 : Blo 471786 474411 := bstep (se 1 (by rfl) ⟨355808, by rfl⟩ : syracuseStep 474411 = 711617) B711617
theorem B507179 : Blo 471786 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B474423 : Blo 471786 474423 := bstep (se 1 (by rfl) ⟨355817, by rfl⟩ : syracuseStep 474423 = 711635) B711635
theorem B4308299 : Blo 471786 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B1064267 : Blo 471786 1064267 := bstep (se 1 (by rfl) ⟨798200, by rfl⟩ : syracuseStep 1064267 = 1596401) B1596401
theorem B474443 : Blo 471786 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B474455 : Blo 471786 474455 := bstep (se 1 (by rfl) ⟨355841, by rfl⟩ : syracuseStep 474455 = 711683) B711683
theorem B474475 : Blo 471786 474475 := bstep (se 1 (by rfl) ⟨355856, by rfl⟩ : syracuseStep 474475 = 711713) B711713
theorem B900467 : Blo 471786 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B474487 : Blo 471786 474487 := bstep (se 1 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 474487 = 711731) B711731
theorem B1064321 : Blo 471786 1064321 := bstep (se 2 (by rfl) ⟨399120, by rfl⟩ : syracuseStep 1064321 = 798241) B798241
theorem B1916291 : Blo 471786 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B474507 : Blo 471786 474507 := bstep (se 1 (by rfl) ⟨355880, by rfl⟩ : syracuseStep 474507 = 711761) B711761
theorem B474519 : Blo 471786 474519 := bstep (se 1 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 474519 = 711779) B711779
theorem B474539 : Blo 471786 474539 := bstep (se 1 (by rfl) ⟨355904, by rfl⟩ : syracuseStep 474539 = 711809) B711809
theorem B474551 : Blo 471786 474551 := bstep (se 1 (by rfl) ⟨355913, by rfl⟩ : syracuseStep 474551 = 711827) B711827
theorem B474571 : Blo 471786 474571 := bstep (se 1 (by rfl) ⟨355928, by rfl⟩ : syracuseStep 474571 = 711857) B711857
theorem B474583 : Blo 471786 474583 := bstep (se 1 (by rfl) ⟨355937, by rfl⟩ : syracuseStep 474583 = 711875) B711875
theorem B474603 : Blo 471786 474603 := bstep (se 1 (by rfl) ⟨355952, by rfl⟩ : syracuseStep 474603 = 711905) B711905
theorem B474615 : Blo 471786 474615 := bstep (se 1 (by rfl) ⟨355961, by rfl⟩ : syracuseStep 474615 = 711923) B711923
theorem B474635 : Blo 471786 474635 := bstep (se 1 (by rfl) ⟨355976, by rfl⟩ : syracuseStep 474635 = 711953) B711953
theorem B474647 : Blo 471786 474647 := bstep (se 1 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 474647 = 711971) B711971
theorem B474667 : Blo 471786 474667 := bstep (se 1 (by rfl) ⟨356000, by rfl⟩ : syracuseStep 474667 = 712001) B712001
theorem B474679 : Blo 471786 474679 := bstep (se 1 (by rfl) ⟨356009, by rfl⟩ : syracuseStep 474679 = 712019) B712019
theorem B474699 : Blo 471786 474699 := bstep (se 1 (by rfl) ⟨356024, by rfl⟩ : syracuseStep 474699 = 712049) B712049
theorem B802379 : Blo 471786 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B900695 : Blo 471786 900695 := bstep (se 1 (by rfl) ⟨675521, by rfl⟩ : syracuseStep 900695 = 1351043) B1351043
theorem B474711 : Blo 471786 474711 := bstep (se 1 (by rfl) ⟨356033, by rfl⟩ : syracuseStep 474711 = 712067) B712067
theorem B1064537 : Blo 471786 1064537 := bstep (se 2 (by rfl) ⟨399201, by rfl⟩ : syracuseStep 1064537 = 798403) B798403
theorem B474731 : Blo 471786 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B474743 : Blo 471786 474743 := bstep (se 1 (by rfl) ⟨356057, by rfl⟩ : syracuseStep 474743 = 712115) B712115
theorem B474763 : Blo 471786 474763 := bstep (se 1 (by rfl) ⟨356072, by rfl⟩ : syracuseStep 474763 = 712145) B712145
theorem B474775 : Blo 471786 474775 := bstep (se 1 (by rfl) ⟨356081, by rfl⟩ : syracuseStep 474775 = 712163) B712163
theorem B474795 : Blo 471786 474795 := bstep (se 1 (by rfl) ⟨356096, by rfl⟩ : syracuseStep 474795 = 712193) B712193
theorem B1064627 : Blo 471786 1064627 := bstep (se 1 (by rfl) ⟨798470, by rfl⟩ : syracuseStep 1064627 = 1596941) B1596941
theorem B474807 : Blo 471786 474807 := bstep (se 1 (by rfl) ⟨356105, by rfl⟩ : syracuseStep 474807 = 712211) B712211
theorem B474827 : Blo 471786 474827 := bstep (se 1 (by rfl) ⟨356120, by rfl⟩ : syracuseStep 474827 = 712241) B712241
theorem B802507 : Blo 471786 802507 := bstep (se 1 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 802507 = 1203761) B1203761
theorem B1064663 : Blo 471786 1064663 := bstep (se 1 (by rfl) ⟨798497, by rfl⟩ : syracuseStep 1064663 = 1596995) B1596995
theorem B474839 : Blo 471786 474839 := bstep (se 1 (by rfl) ⟨356129, by rfl⟩ : syracuseStep 474839 = 712259) B712259
theorem B474859 : Blo 471786 474859 := bstep (se 1 (by rfl) ⟨356144, by rfl⟩ : syracuseStep 474859 = 712289) B712289
theorem B474871 : Blo 471786 474871 := bstep (se 1 (by rfl) ⟨356153, by rfl⟩ : syracuseStep 474871 = 712307) B712307
theorem B474891 : Blo 471786 474891 := bstep (se 1 (by rfl) ⟨356168, by rfl⟩ : syracuseStep 474891 = 712337) B712337
theorem B474903 : Blo 471786 474903 := bstep (se 1 (by rfl) ⟨356177, by rfl⟩ : syracuseStep 474903 = 712355) B712355
theorem B474923 : Blo 471786 474923 := bstep (se 1 (by rfl) ⟨356192, by rfl⟩ : syracuseStep 474923 = 712385) B712385
theorem B474935 : Blo 471786 474935 := bstep (se 1 (by rfl) ⟨356201, by rfl⟩ : syracuseStep 474935 = 712403) B712403
theorem B474955 : Blo 471786 474955 := bstep (se 1 (by rfl) ⟨356216, by rfl⟩ : syracuseStep 474955 = 712433) B712433
theorem B474967 : Blo 471786 474967 := bstep (se 1 (by rfl) ⟨356225, by rfl⟩ : syracuseStep 474967 = 712451) B712451
theorem B900953 : Blo 471786 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B802649 : Blo 471786 802649 := bstep (se 2 (by rfl) ⟨300993, by rfl⟩ : syracuseStep 802649 = 601987) B601987
theorem B474987 : Blo 471786 474987 := bstep (se 1 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 474987 = 712481) B712481
theorem B474999 : Blo 471786 474999 := bstep (se 1 (by rfl) ⟨356249, by rfl⟩ : syracuseStep 474999 = 712499) B712499
theorem B1064843 : Blo 471786 1064843 := bstep (se 1 (by rfl) ⟨798632, by rfl⟩ : syracuseStep 1064843 = 1597265) B1597265
theorem B475019 : Blo 471786 475019 := bstep (se 1 (by rfl) ⟨356264, by rfl⟩ : syracuseStep 475019 = 712529) B712529
theorem B475031 : Blo 471786 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B475051 : Blo 471786 475051 := bstep (se 1 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 475051 = 712577) B712577
theorem B1195955 : Blo 471786 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B475063 : Blo 471786 475063 := bstep (se 1 (by rfl) ⟨356297, by rfl⟩ : syracuseStep 475063 = 712595) B712595
theorem B1064897 : Blo 471786 1064897 := bstep (se 2 (by rfl) ⟨399336, by rfl⟩ : syracuseStep 1064897 = 798673) B798673
theorem B475083 : Blo 471786 475083 := bstep (se 1 (by rfl) ⟨356312, by rfl⟩ : syracuseStep 475083 = 712625) B712625
theorem B475095 : Blo 471786 475095 := bstep (se 1 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 475095 = 712643) B712643
theorem B802777 : Blo 471786 802777 := bstep (se 2 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 802777 = 602083) B602083
theorem B475115 : Blo 471786 475115 := bstep (se 1 (by rfl) ⟨356336, by rfl⟩ : syracuseStep 475115 = 712673) B712673
theorem B475127 : Blo 471786 475127 := bstep (se 1 (by rfl) ⟨356345, by rfl⟩ : syracuseStep 475127 = 712691) B712691
theorem B475147 : Blo 471786 475147 := bstep (se 1 (by rfl) ⟨356360, by rfl⟩ : syracuseStep 475147 = 712721) B712721
theorem B475159 : Blo 471786 475159 := bstep (se 1 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 475159 = 712739) B712739
theorem B475179 : Blo 471786 475179 := bstep (se 1 (by rfl) ⟨356384, by rfl⟩ : syracuseStep 475179 = 712769) B712769
theorem B475191 : Blo 471786 475191 := bstep (se 1 (by rfl) ⟨356393, by rfl⟩ : syracuseStep 475191 = 712787) B712787
theorem B671819 : Blo 471786 671819 := bstep (se 1 (by rfl) ⟨503864, by rfl⟩ : syracuseStep 671819 = 1007729) B1007729
theorem B475211 : Blo 471786 475211 := bstep (se 1 (by rfl) ⟨356408, by rfl⟩ : syracuseStep 475211 = 712817) B712817
theorem B475223 : Blo 471786 475223 := bstep (se 1 (by rfl) ⟨356417, by rfl⟩ : syracuseStep 475223 = 712835) B712835
theorem B475243 : Blo 471786 475243 := bstep (se 1 (by rfl) ⟨356432, by rfl⟩ : syracuseStep 475243 = 712865) B712865
theorem B475255 : Blo 471786 475255 := bstep (se 1 (by rfl) ⟨356441, by rfl⟩ : syracuseStep 475255 = 712883) B712883
theorem B475275 : Blo 471786 475275 := bstep (se 1 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 475275 = 712913) B712913
theorem B475287 : Blo 471786 475287 := bstep (se 1 (by rfl) ⟨356465, by rfl⟩ : syracuseStep 475287 = 712931) B712931
theorem B1065113 : Blo 471786 1065113 := bstep (se 2 (by rfl) ⟨399417, by rfl⟩ : syracuseStep 1065113 = 798835) B798835
theorem B475307 : Blo 471786 475307 := bstep (se 1 (by rfl) ⟨356480, by rfl⟩ : syracuseStep 475307 = 712961) B712961
theorem B475319 : Blo 471786 475319 := bstep (se 1 (by rfl) ⟨356489, by rfl⟩ : syracuseStep 475319 = 712979) B712979
theorem B475339 : Blo 471786 475339 := bstep (se 1 (by rfl) ⟨356504, by rfl⟩ : syracuseStep 475339 = 713009) B713009
theorem B475351 : Blo 471786 475351 := bstep (se 1 (by rfl) ⟨356513, by rfl⟩ : syracuseStep 475351 = 713027) B713027
theorem B475371 : Blo 471786 475371 := bstep (se 1 (by rfl) ⟨356528, by rfl⟩ : syracuseStep 475371 = 713057) B713057
theorem B1065203 : Blo 471786 1065203 := bstep (se 1 (by rfl) ⟨798902, by rfl⟩ : syracuseStep 1065203 = 1597805) B1597805
theorem B901363 : Blo 471786 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B475383 : Blo 471786 475383 := bstep (se 1 (by rfl) ⟨356537, by rfl⟩ : syracuseStep 475383 = 713075) B713075
theorem B475403 : Blo 471786 475403 := bstep (se 1 (by rfl) ⟨356552, by rfl⟩ : syracuseStep 475403 = 713105) B713105
theorem B1065239 : Blo 471786 1065239 := bstep (se 1 (by rfl) ⟨798929, by rfl⟩ : syracuseStep 1065239 = 1597859) B1597859
theorem B475415 : Blo 471786 475415 := bstep (se 1 (by rfl) ⟨356561, by rfl⟩ : syracuseStep 475415 = 713123) B713123
theorem B475435 : Blo 471786 475435 := bstep (se 1 (by rfl) ⟨356576, by rfl⟩ : syracuseStep 475435 = 713153) B713153
theorem B475447 : Blo 471786 475447 := bstep (se 1 (by rfl) ⟨356585, by rfl⟩ : syracuseStep 475447 = 713171) B713171
theorem B475467 : Blo 471786 475467 := bstep (se 1 (by rfl) ⟨356600, by rfl⟩ : syracuseStep 475467 = 713201) B713201
theorem B475479 : Blo 471786 475479 := bstep (se 1 (by rfl) ⟨356609, by rfl⟩ : syracuseStep 475479 = 713219) B713219
theorem B475499 : Blo 471786 475499 := bstep (se 1 (by rfl) ⟨356624, by rfl⟩ : syracuseStep 475499 = 713249) B713249
theorem B475511 : Blo 471786 475511 := bstep (se 1 (by rfl) ⟨356633, by rfl⟩ : syracuseStep 475511 = 713267) B713267
theorem B475531 : Blo 471786 475531 := bstep (se 1 (by rfl) ⟨356648, by rfl⟩ : syracuseStep 475531 = 713297) B713297
theorem B475543 : Blo 471786 475543 := bstep (se 1 (by rfl) ⟨356657, by rfl⟩ : syracuseStep 475543 = 713315) B713315
theorem B475563 : Blo 471786 475563 := bstep (se 1 (by rfl) ⟨356672, by rfl⟩ : syracuseStep 475563 = 713345) B713345
theorem B475575 : Blo 471786 475575 := bstep (se 1 (by rfl) ⟨356681, by rfl⟩ : syracuseStep 475575 = 713363) B713363
theorem B1196491 : Blo 471786 1196491 := bstep (se 1 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 1196491 = 1794737) B1794737
theorem B1065419 : Blo 471786 1065419 := bstep (se 1 (by rfl) ⟨799064, by rfl⟩ : syracuseStep 1065419 = 1598129) B1598129
theorem B475595 : Blo 471786 475595 := bstep (se 1 (by rfl) ⟨356696, by rfl⟩ : syracuseStep 475595 = 713393) B713393
theorem B475607 : Blo 471786 475607 := bstep (se 1 (by rfl) ⟨356705, by rfl⟩ : syracuseStep 475607 = 713411) B713411
theorem B475627 : Blo 471786 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B475639 : Blo 471786 475639 := bstep (se 1 (by rfl) ⟨356729, by rfl⟩ : syracuseStep 475639 = 713459) B713459
theorem B1065473 : Blo 471786 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B475659 : Blo 471786 475659 := bstep (se 1 (by rfl) ⟨356744, by rfl⟩ : syracuseStep 475659 = 713489) B713489
theorem B475671 : Blo 471786 475671 := bstep (se 1 (by rfl) ⟨356753, by rfl⟩ : syracuseStep 475671 = 713507) B713507
theorem B475691 : Blo 471786 475691 := bstep (se 1 (by rfl) ⟨356768, by rfl⟩ : syracuseStep 475691 = 713537) B713537
theorem B475703 : Blo 471786 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B475723 : Blo 471786 475723 := bstep (se 1 (by rfl) ⟨356792, by rfl⟩ : syracuseStep 475723 = 713585) B713585
theorem B475735 : Blo 471786 475735 := bstep (se 1 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 475735 = 713603) B713603
theorem B1196633 : Blo 471786 1196633 := bstep (se 2 (by rfl) ⟨448737, by rfl⟩ : syracuseStep 1196633 = 897475) B897475
theorem B836185 : Blo 471786 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B475755 : Blo 471786 475755 := bstep (se 1 (by rfl) ⟨356816, by rfl⟩ : syracuseStep 475755 = 713633) B713633
theorem B475767 : Blo 471786 475767 := bstep (se 1 (by rfl) ⟨356825, by rfl⟩ : syracuseStep 475767 = 713651) B713651
theorem B1065689 : Blo 471786 1065689 := bstep (se 2 (by rfl) ⟨399633, by rfl⟩ : syracuseStep 1065689 = 799267) B799267
theorem B901849 : Blo 471786 901849 := bstep (se 2 (by rfl) ⟨338193, by rfl⟩ : syracuseStep 901849 = 676387) B676387
theorem B1819409 : Blo 471786 1819409 := bstep (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) B1364557
theorem B1065779 : Blo 471786 1065779 := bstep (se 1 (by rfl) ⟨799334, by rfl⟩ : syracuseStep 1065779 = 1598669) B1598669
theorem B1065815 : Blo 471786 1065815 := bstep (se 1 (by rfl) ⟨799361, by rfl⟩ : syracuseStep 1065815 = 1598723) B1598723
theorem B3031901 : Blo 471786 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B1459037 : Blo 471786 1459037 := bstep (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) B547139
theorem B8111027 : Blo 471786 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B1065995 : Blo 471786 1065995 := bstep (se 1 (by rfl) ⟨799496, by rfl⟩ : syracuseStep 1065995 = 1598993) B1598993
theorem B1066049 : Blo 471786 1066049 := bstep (se 2 (by rfl) ⟨399768, by rfl⟩ : syracuseStep 1066049 = 799537) B799537
theorem B902411 : Blo 471786 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B2016535 : Blo 471786 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B1066265 : Blo 471786 1066265 := bstep (se 2 (by rfl) ⟨399849, by rfl⟩ : syracuseStep 1066265 = 799699) B799699
theorem B1066355 : Blo 471786 1066355 := bstep (se 1 (by rfl) ⟨799766, by rfl⟩ : syracuseStep 1066355 = 1599533) B1599533
theorem B1197463 : Blo 471786 1197463 := bstep (se 1 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 1197463 = 1796195) B1796195
theorem B1066391 : Blo 471786 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B3458483 : Blo 471786 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B902593 : Blo 471786 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B1066571 : Blo 471786 1066571 := bstep (se 1 (by rfl) ⟨799928, by rfl⟩ : syracuseStep 1066571 = 1599857) B1599857
theorem B1066625 : Blo 471786 1066625 := bstep (se 2 (by rfl) ⟨399984, by rfl⟩ : syracuseStep 1066625 = 799969) B799969
theorem B1197899 : Blo 471786 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B1066841 : Blo 471786 1066841 := bstep (se 2 (by rfl) ⟨400065, by rfl⟩ : syracuseStep 1066841 = 800131) B800131
theorem B673687 : Blo 471786 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B11519921 : Blo 471786 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B1066931 : Blo 471786 1066931 := bstep (se 1 (by rfl) ⟨800198, by rfl⟩ : syracuseStep 1066931 = 1600397) B1600397
theorem B1066967 : Blo 471786 1066967 := bstep (se 1 (by rfl) ⟨800225, by rfl⟩ : syracuseStep 1066967 = 1600451) B1600451
theorem B2705501 : Blo 471786 2705501 := bstep (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) B1014563
theorem B4049027 : Blo 471786 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B1067147 : Blo 471786 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B1853585 : Blo 471786 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1198273 : Blo 471786 1198273 := bstep (se 2 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 1198273 = 898705) B898705
theorem B1067201 : Blo 471786 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B1362251 : Blo 471786 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B1067417 : Blo 471786 1067417 := bstep (se 2 (by rfl) ⟨400281, by rfl⟩ : syracuseStep 1067417 = 800563) B800563
theorem B1067507 : Blo 471786 1067507 := bstep (se 1 (by rfl) ⟨800630, by rfl⟩ : syracuseStep 1067507 = 1601261) B1601261
theorem B1067543 : Blo 471786 1067543 := bstep (se 1 (by rfl) ⟨800657, by rfl⟩ : syracuseStep 1067543 = 1601315) B1601315
theorem B1067723 : Blo 471786 1067723 := bstep (se 1 (by rfl) ⟨800792, by rfl⟩ : syracuseStep 1067723 = 1601585) B1601585
theorem B1067777 : Blo 471786 1067777 := bstep (se 2 (by rfl) ⟨400416, by rfl⟩ : syracuseStep 1067777 = 800833) B800833
theorem B1198871 : Blo 471786 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B1067993 : Blo 471786 1067993 := bstep (se 2 (by rfl) ⟨400497, by rfl⟩ : syracuseStep 1067993 = 800995) B800995
theorem B1068083 : Blo 471786 1068083 := bstep (se 1 (by rfl) ⟨801062, by rfl⟩ : syracuseStep 1068083 = 1602125) B1602125
theorem B1068119 : Blo 471786 1068119 := bstep (se 1 (by rfl) ⟨801089, by rfl⟩ : syracuseStep 1068119 = 1602179) B1602179
theorem B707723 : Blo 471786 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B707735 : Blo 471786 707735 := bstep (se 1 (by rfl) ⟨530801, by rfl⟩ : syracuseStep 707735 = 1061603) B1061603
theorem B1592513 : Blo 471786 1592513 := bstep (se 2 (by rfl) ⟨597192, by rfl⟩ : syracuseStep 1592513 = 1194385) B1194385
theorem B707801 : Blo 471786 707801 := bstep (se 2 (by rfl) ⟨265425, by rfl⟩ : syracuseStep 707801 = 530851) B530851
theorem B1068299 : Blo 471786 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B1068353 : Blo 471786 1068353 := bstep (se 2 (by rfl) ⟨400632, by rfl⟩ : syracuseStep 1068353 = 801265) B801265
theorem B707915 : Blo 471786 707915 := bstep (se 1 (by rfl) ⟨530936, by rfl⟩ : syracuseStep 707915 = 1061873) B1061873
theorem B707927 : Blo 471786 707927 := bstep (se 1 (by rfl) ⟨530945, by rfl⟩ : syracuseStep 707927 = 1061891) B1061891
theorem B707993 : Blo 471786 707993 := bstep (se 2 (by rfl) ⟨265497, by rfl⟩ : syracuseStep 707993 = 530995) B530995
theorem B478667 : Blo 471786 478667 := bstep (se 1 (by rfl) ⟨359000, by rfl⟩ : syracuseStep 478667 = 718001) B718001
theorem B708107 : Blo 471786 708107 := bstep (se 1 (by rfl) ⟨531080, by rfl⟩ : syracuseStep 708107 = 1062161) B1062161
theorem B708119 : Blo 471786 708119 := bstep (se 1 (by rfl) ⟨531089, by rfl⟩ : syracuseStep 708119 = 1062179) B1062179
theorem B1068569 : Blo 471786 1068569 := bstep (se 2 (by rfl) ⟨400713, by rfl⟩ : syracuseStep 1068569 = 801427) B801427
theorem B1199681 : Blo 471786 1199681 := bstep (se 2 (by rfl) ⟨449880, by rfl⟩ : syracuseStep 1199681 = 899761) B899761
theorem B708185 : Blo 471786 708185 := bstep (se 2 (by rfl) ⟨265569, by rfl⟩ : syracuseStep 708185 = 531139) B531139
theorem B1068659 : Blo 471786 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B1068695 : Blo 471786 1068695 := bstep (se 1 (by rfl) ⟨801521, by rfl⟩ : syracuseStep 1068695 = 1603043) B1603043
theorem B708299 : Blo 471786 708299 := bstep (se 1 (by rfl) ⟨531224, by rfl⟩ : syracuseStep 708299 = 1062449) B1062449
theorem B708311 : Blo 471786 708311 := bstep (se 1 (by rfl) ⟨531233, by rfl⟩ : syracuseStep 708311 = 1062467) B1062467
theorem B1593053 : Blo 471786 1593053 := bstep (se 3 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 1593053 = 597395) B597395
theorem B708377 : Blo 471786 708377 := bstep (se 2 (by rfl) ⟨265641, by rfl⟩ : syracuseStep 708377 = 531283) B531283
theorem B1068875 : Blo 471786 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B18665315 : Blo 471786 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B1068929 : Blo 471786 1068929 := bstep (se 2 (by rfl) ⟨400848, by rfl⟩ : syracuseStep 1068929 = 801697) B801697
theorem B708491 : Blo 471786 708491 := bstep (se 1 (by rfl) ⟨531368, by rfl⟩ : syracuseStep 708491 = 1062737) B1062737
theorem B708503 : Blo 471786 708503 := bstep (se 1 (by rfl) ⟨531377, by rfl⟩ : syracuseStep 708503 = 1062755) B1062755
theorem B708569 : Blo 471786 708569 := bstep (se 2 (by rfl) ⟨265713, by rfl⟩ : syracuseStep 708569 = 531427) B531427
theorem B2281537 : Blo 471786 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B708683 : Blo 471786 708683 := bstep (se 1 (by rfl) ⟨531512, by rfl⟩ : syracuseStep 708683 = 1063025) B1063025
theorem B708695 : Blo 471786 708695 := bstep (se 1 (by rfl) ⟨531521, by rfl⟩ : syracuseStep 708695 = 1063043) B1063043
theorem B1200217 : Blo 471786 1200217 := bstep (se 2 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 1200217 = 900163) B900163
theorem B1069145 : Blo 471786 1069145 := bstep (se 2 (by rfl) ⟨400929, by rfl⟩ : syracuseStep 1069145 = 801859) B801859
theorem B2019421 : Blo 471786 2019421 := bstep (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) B757283
theorem B708761 : Blo 471786 708761 := bstep (se 2 (by rfl) ⟨265785, by rfl⟩ : syracuseStep 708761 = 531571) B531571
theorem B1069235 : Blo 471786 1069235 := bstep (se 1 (by rfl) ⟨801926, by rfl⟩ : syracuseStep 1069235 = 1603853) B1603853
theorem B1069271 : Blo 471786 1069271 := bstep (se 1 (by rfl) ⟨801953, by rfl⟩ : syracuseStep 1069271 = 1603907) B1603907
theorem B708875 : Blo 471786 708875 := bstep (se 1 (by rfl) ⟨531656, by rfl⟩ : syracuseStep 708875 = 1063313) B1063313
theorem B708887 : Blo 471786 708887 := bstep (se 1 (by rfl) ⟨531665, by rfl⟩ : syracuseStep 708887 = 1063331) B1063331
theorem B708953 : Blo 471786 708953 := bstep (se 2 (by rfl) ⟨265857, by rfl⟩ : syracuseStep 708953 = 531715) B531715
theorem B1069451 : Blo 471786 1069451 := bstep (se 1 (by rfl) ⟨802088, by rfl⟩ : syracuseStep 1069451 = 1604177) B1604177
theorem B1069505 : Blo 471786 1069505 := bstep (se 2 (by rfl) ⟨401064, by rfl⟩ : syracuseStep 1069505 = 802129) B802129
theorem B709067 : Blo 471786 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B709079 : Blo 471786 709079 := bstep (se 1 (by rfl) ⟨531809, by rfl⟩ : syracuseStep 709079 = 1063619) B1063619
theorem B4051417 : Blo 471786 4051417 := bstep (se 2 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 4051417 = 3038563) B3038563
theorem B709145 : Blo 471786 709145 := bstep (se 2 (by rfl) ⟨265929, by rfl⟩ : syracuseStep 709145 = 531859) B531859
theorem B3035693 : Blo 471786 3035693 := bstep (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) B1138385
theorem B2708099 : Blo 471786 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B709259 : Blo 471786 709259 := bstep (se 1 (by rfl) ⟨531944, by rfl⟩ : syracuseStep 709259 = 1063889) B1063889
theorem B709271 : Blo 471786 709271 := bstep (se 1 (by rfl) ⟨531953, by rfl⟩ : syracuseStep 709271 = 1063907) B1063907
theorem B1069721 : Blo 471786 1069721 := bstep (se 2 (by rfl) ⟨401145, by rfl⟩ : syracuseStep 1069721 = 802291) B802291
theorem B709337 : Blo 471786 709337 := bstep (se 2 (by rfl) ⟨266001, by rfl⟩ : syracuseStep 709337 = 532003) B532003
theorem B1069811 : Blo 471786 1069811 := bstep (se 1 (by rfl) ⟨802358, by rfl⟩ : syracuseStep 1069811 = 1604717) B1604717
theorem B1069847 : Blo 471786 1069847 := bstep (se 1 (by rfl) ⟨802385, by rfl⟩ : syracuseStep 1069847 = 1604771) B1604771
theorem B1594187 : Blo 471786 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B709451 : Blo 471786 709451 := bstep (se 1 (by rfl) ⟨532088, by rfl⟩ : syracuseStep 709451 = 1064177) B1064177
theorem B709463 : Blo 471786 709463 := bstep (se 1 (by rfl) ⟨532097, by rfl⟩ : syracuseStep 709463 = 1064195) B1064195
theorem B2020241 : Blo 471786 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B709529 : Blo 471786 709529 := bstep (se 2 (by rfl) ⟨266073, by rfl⟩ : syracuseStep 709529 = 532147) B532147
theorem B1070027 : Blo 471786 1070027 := bstep (se 1 (by rfl) ⟨802520, by rfl⟩ : syracuseStep 1070027 = 1605041) B1605041
theorem B1070081 : Blo 471786 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B709643 : Blo 471786 709643 := bstep (se 1 (by rfl) ⟨532232, by rfl⟩ : syracuseStep 709643 = 1064465) B1064465
theorem B709655 : Blo 471786 709655 := bstep (se 1 (by rfl) ⟨532241, by rfl⟩ : syracuseStep 709655 = 1064483) B1064483
theorem B1594457 : Blo 471786 1594457 := bstep (se 2 (by rfl) ⟨597921, by rfl⟩ : syracuseStep 1594457 = 1195843) B1195843
theorem B709721 : Blo 471786 709721 := bstep (se 2 (by rfl) ⟨266145, by rfl⟩ : syracuseStep 709721 = 532291) B532291
theorem B1201331 : Blo 471786 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B709835 : Blo 471786 709835 := bstep (se 1 (by rfl) ⟨532376, by rfl⟩ : syracuseStep 709835 = 1064753) B1064753
theorem B709847 : Blo 471786 709847 := bstep (se 1 (by rfl) ⟨532385, by rfl⟩ : syracuseStep 709847 = 1064771) B1064771
theorem B1070297 : Blo 471786 1070297 := bstep (se 2 (by rfl) ⟨401361, by rfl⟩ : syracuseStep 1070297 = 802723) B802723
theorem B709913 : Blo 471786 709913 := bstep (se 2 (by rfl) ⟨266217, by rfl⟩ : syracuseStep 709913 = 532435) B532435
theorem B1070387 : Blo 471786 1070387 := bstep (se 1 (by rfl) ⟨802790, by rfl⟩ : syracuseStep 1070387 = 1605581) B1605581
theorem B677207 : Blo 471786 677207 := bstep (se 1 (by rfl) ⟨507905, by rfl⟩ : syracuseStep 677207 = 1015811) B1015811
theorem B1070423 : Blo 471786 1070423 := bstep (se 1 (by rfl) ⟨802817, by rfl⟩ : syracuseStep 1070423 = 1605635) B1605635
theorem B710027 : Blo 471786 710027 := bstep (se 1 (by rfl) ⟨532520, by rfl⟩ : syracuseStep 710027 = 1065041) B1065041
theorem B710039 : Blo 471786 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B4052375 : Blo 471786 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B710105 : Blo 471786 710105 := bstep (se 2 (by rfl) ⟨266289, by rfl⟩ : syracuseStep 710105 = 532579) B532579
theorem B1201625 : Blo 471786 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B2020909 : Blo 471786 2020909 := bstep (se 3 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 2020909 = 757841) B757841
theorem B710219 : Blo 471786 710219 := bstep (se 1 (by rfl) ⟨532664, by rfl⟩ : syracuseStep 710219 = 1065329) B1065329
theorem B710231 : Blo 471786 710231 := bstep (se 1 (by rfl) ⟨532673, by rfl⟩ : syracuseStep 710231 = 1065347) B1065347
theorem B710297 : Blo 471786 710297 := bstep (se 2 (by rfl) ⟨266361, by rfl⟩ : syracuseStep 710297 = 532723) B532723
theorem B710411 : Blo 471786 710411 := bstep (se 1 (by rfl) ⟨532808, by rfl⟩ : syracuseStep 710411 = 1065617) B1065617
theorem B4052753 : Blo 471786 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B1595159 : Blo 471786 1595159 := bstep (se 1 (by rfl) ⟨1196369, by rfl⟩ : syracuseStep 1595159 = 2392739) B2392739
theorem B710423 : Blo 471786 710423 := bstep (se 1 (by rfl) ⟨532817, by rfl⟩ : syracuseStep 710423 = 1065635) B1065635
theorem B710489 : Blo 471786 710489 := bstep (se 2 (by rfl) ⟨266433, by rfl⟩ : syracuseStep 710489 = 532867) B532867
theorem B4085635 : Blo 471786 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B710603 : Blo 471786 710603 := bstep (se 1 (by rfl) ⟨532952, by rfl⟩ : syracuseStep 710603 = 1065905) B1065905
theorem B710615 : Blo 471786 710615 := bstep (se 1 (by rfl) ⟨532961, by rfl⟩ : syracuseStep 710615 = 1065923) B1065923
theorem B1792003 : Blo 471786 1792003 := bstep (se 1 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 1792003 = 2688005) B2688005
theorem B710681 : Blo 471786 710681 := bstep (se 2 (by rfl) ⟨266505, by rfl⟩ : syracuseStep 710681 = 533011) B533011
theorem B2021507 : Blo 471786 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B546955 : Blo 471786 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B710795 : Blo 471786 710795 := bstep (se 1 (by rfl) ⟨533096, by rfl⟩ : syracuseStep 710795 = 1066193) B1066193
theorem B710807 : Blo 471786 710807 := bstep (se 1 (by rfl) ⟨533105, by rfl⟩ : syracuseStep 710807 = 1066211) B1066211
theorem B710873 : Blo 471786 710873 := bstep (se 2 (by rfl) ⟨266577, by rfl⟩ : syracuseStep 710873 = 533155) B533155
theorem B1792307 : Blo 471786 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1595699 : Blo 471786 1595699 := bstep (se 1 (by rfl) ⟨1196774, by rfl⟩ : syracuseStep 1595699 = 2393549) B2393549
theorem B1300787 : Blo 471786 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B710987 : Blo 471786 710987 := bstep (se 1 (by rfl) ⟨533240, by rfl⟩ : syracuseStep 710987 = 1066481) B1066481
theorem B710999 : Blo 471786 710999 := bstep (se 1 (by rfl) ⟨533249, by rfl⟩ : syracuseStep 710999 = 1066499) B1066499
theorem B711065 : Blo 471786 711065 := bstep (se 2 (by rfl) ⟨266649, by rfl⟩ : syracuseStep 711065 = 533299) B533299
theorem B711179 : Blo 471786 711179 := bstep (se 1 (by rfl) ⟨533384, by rfl⟩ : syracuseStep 711179 = 1066769) B1066769
theorem B711191 : Blo 471786 711191 := bstep (se 1 (by rfl) ⟨533393, by rfl⟩ : syracuseStep 711191 = 1066787) B1066787
theorem B1595969 : Blo 471786 1595969 := bstep (se 2 (by rfl) ⟨598488, by rfl⟩ : syracuseStep 1595969 = 1196977) B1196977
theorem B711257 : Blo 471786 711257 := bstep (se 2 (by rfl) ⟨266721, by rfl⟩ : syracuseStep 711257 = 533443) B533443
theorem B711371 : Blo 471786 711371 := bstep (se 1 (by rfl) ⟨533528, by rfl⟩ : syracuseStep 711371 = 1067057) B1067057
theorem B711383 : Blo 471786 711383 := bstep (se 1 (by rfl) ⟨533537, by rfl⟩ : syracuseStep 711383 = 1067075) B1067075
theorem B711449 : Blo 471786 711449 := bstep (se 2 (by rfl) ⟨266793, by rfl⟩ : syracuseStep 711449 = 533587) B533587
theorem B711563 : Blo 471786 711563 := bstep (se 1 (by rfl) ⟨533672, by rfl⟩ : syracuseStep 711563 = 1067345) B1067345
theorem B1137559 : Blo 471786 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B711575 : Blo 471786 711575 := bstep (se 1 (by rfl) ⟨533681, by rfl⟩ : syracuseStep 711575 = 1067363) B1067363
theorem B1792961 : Blo 471786 1792961 := bstep (se 2 (by rfl) ⟨672360, by rfl⟩ : syracuseStep 1792961 = 1344721) B1344721
theorem B711641 : Blo 471786 711641 := bstep (se 2 (by rfl) ⟨266865, by rfl⟩ : syracuseStep 711641 = 533731) B533731
theorem B711755 : Blo 471786 711755 := bstep (se 1 (by rfl) ⟨533816, by rfl⟩ : syracuseStep 711755 = 1067633) B1067633
theorem B1203275 : Blo 471786 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B711767 : Blo 471786 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B1596509 : Blo 471786 1596509 := bstep (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) B598691
theorem B711833 : Blo 471786 711833 := bstep (se 2 (by rfl) ⟨266937, by rfl⟩ : syracuseStep 711833 = 533875) B533875
theorem B711947 : Blo 471786 711947 := bstep (se 1 (by rfl) ⟨533960, by rfl⟩ : syracuseStep 711947 = 1067921) B1067921
theorem B711959 : Blo 471786 711959 := bstep (se 1 (by rfl) ⟨533969, by rfl⟩ : syracuseStep 711959 = 1067939) B1067939
theorem B712025 : Blo 471786 712025 := bstep (se 2 (by rfl) ⟨267009, by rfl⟩ : syracuseStep 712025 = 534019) B534019
theorem B8314211 : Blo 471786 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B712139 : Blo 471786 712139 := bstep (se 1 (by rfl) ⟨534104, by rfl⟩ : syracuseStep 712139 = 1068209) B1068209
theorem B712151 : Blo 471786 712151 := bstep (se 1 (by rfl) ⟨534113, by rfl⟩ : syracuseStep 712151 = 1068227) B1068227
theorem B712217 : Blo 471786 712217 := bstep (se 2 (by rfl) ⟨267081, by rfl⟩ : syracuseStep 712217 = 534163) B534163
theorem B712331 : Blo 471786 712331 := bstep (se 1 (by rfl) ⟨534248, by rfl⟩ : syracuseStep 712331 = 1068497) B1068497
theorem B712343 : Blo 471786 712343 := bstep (se 1 (by rfl) ⟨534257, by rfl⟩ : syracuseStep 712343 = 1068515) B1068515
theorem B3464909 : Blo 471786 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B712409 : Blo 471786 712409 := bstep (se 2 (by rfl) ⟨267153, by rfl⟩ : syracuseStep 712409 = 534307) B534307
theorem B1367873 : Blo 471786 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B712523 : Blo 471786 712523 := bstep (se 1 (by rfl) ⟨534392, by rfl⟩ : syracuseStep 712523 = 1068785) B1068785
theorem B712535 : Blo 471786 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B712601 : Blo 471786 712601 := bstep (se 2 (by rfl) ⟨267225, by rfl⟩ : syracuseStep 712601 = 534451) B534451
theorem B712715 : Blo 471786 712715 := bstep (se 1 (by rfl) ⟨534536, by rfl⟩ : syracuseStep 712715 = 1069073) B1069073
theorem B712727 : Blo 471786 712727 := bstep (se 1 (by rfl) ⟨534545, by rfl⟩ : syracuseStep 712727 = 1069091) B1069091
theorem B1204247 : Blo 471786 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B712793 : Blo 471786 712793 := bstep (se 2 (by rfl) ⟨267297, by rfl⟩ : syracuseStep 712793 = 534595) B534595
theorem B3039383 : Blo 471786 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B1794221 : Blo 471786 1794221 := bstep (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) B672833
theorem B1794251 : Blo 471786 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B1597643 : Blo 471786 1597643 := bstep (se 1 (by rfl) ⟨1198232, by rfl⟩ : syracuseStep 1597643 = 2396465) B2396465
theorem B712907 : Blo 471786 712907 := bstep (se 1 (by rfl) ⟨534680, by rfl⟩ : syracuseStep 712907 = 1069361) B1069361
theorem B712919 : Blo 471786 712919 := bstep (se 1 (by rfl) ⟨534689, by rfl⟩ : syracuseStep 712919 = 1069379) B1069379
theorem B712985 : Blo 471786 712985 := bstep (se 2 (by rfl) ⟨267369, by rfl⟩ : syracuseStep 712985 = 534739) B534739
theorem B713099 : Blo 471786 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B713111 : Blo 471786 713111 := bstep (se 1 (by rfl) ⟨534833, by rfl⟩ : syracuseStep 713111 = 1069667) B1069667
theorem B1532353 : Blo 471786 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B1139147 : Blo 471786 1139147 := bstep (se 1 (by rfl) ⟨854360, by rfl⟩ : syracuseStep 1139147 = 1708721) B1708721
theorem B1597913 : Blo 471786 1597913 := bstep (se 2 (by rfl) ⟨599217, by rfl⟩ : syracuseStep 1597913 = 1198435) B1198435
theorem B713177 : Blo 471786 713177 := bstep (se 2 (by rfl) ⟨267441, by rfl⟩ : syracuseStep 713177 = 534883) B534883
theorem B1008139 : Blo 471786 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B713291 : Blo 471786 713291 := bstep (se 1 (by rfl) ⟨534968, by rfl⟩ : syracuseStep 713291 = 1069937) B1069937
theorem B713303 : Blo 471786 713303 := bstep (se 1 (by rfl) ⟨534977, by rfl⟩ : syracuseStep 713303 = 1069955) B1069955
theorem B713369 : Blo 471786 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B713483 : Blo 471786 713483 := bstep (se 1 (by rfl) ⟨535112, by rfl⟩ : syracuseStep 713483 = 1070225) B1070225
theorem B713495 : Blo 471786 713495 := bstep (se 1 (by rfl) ⟨535121, by rfl⟩ : syracuseStep 713495 = 1070243) B1070243
theorem B1532737 : Blo 471786 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B1794905 : Blo 471786 1794905 := bstep (se 2 (by rfl) ⟨673089, by rfl⟩ : syracuseStep 1794905 = 1346179) B1346179
theorem B713561 : Blo 471786 713561 := bstep (se 2 (by rfl) ⟨267585, by rfl⟩ : syracuseStep 713561 = 535171) B535171
theorem B713675 : Blo 471786 713675 := bstep (se 1 (by rfl) ⟨535256, by rfl⟩ : syracuseStep 713675 = 1070513) B1070513
theorem B1795223 : Blo 471786 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B1598615 : Blo 471786 1598615 := bstep (se 1 (by rfl) ⟨1198961, by rfl⟩ : syracuseStep 1598615 = 2397923) B2397923
theorem B5137613 : Blo 471786 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B1008857 : Blo 471786 1008857 := bstep (se 2 (by rfl) ⟨378321, by rfl⟩ : syracuseStep 1008857 = 756643) B756643
theorem B1599155 : Blo 471786 1599155 := bstep (se 1 (by rfl) ⟨1199366, by rfl⟩ : syracuseStep 1599155 = 2398733) B2398733
theorem B1009369 : Blo 471786 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B1795891 : Blo 471786 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B1009523 : Blo 471786 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1599425 : Blo 471786 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B813143 : Blo 471786 813143 := bstep (se 1 (by rfl) ⟨609857, by rfl⟩ : syracuseStep 813143 = 1219715) B1219715
theorem B1927385 : Blo 471786 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1829251 : Blo 471786 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B4549081 : Blo 471786 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B1599965 : Blo 471786 1599965 := bstep (se 3 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 1599965 = 599987) B599987
theorem B1010497 : Blo 471786 1010497 := bstep (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) B757873
theorem B13003697 : Blo 471786 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1797137 : Blo 471786 1797137 := bstep (se 2 (by rfl) ⟨673926, by rfl⟩ : syracuseStep 1797137 = 1347853) B1347853
theorem B15199301 : Blo 471786 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1010839 : Blo 471786 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B3402931 : Blo 471786 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B486859 : Blo 471786 486859 := bstep (se 1 (by rfl) ⟨365144, by rfl⟩ : syracuseStep 486859 = 730289) B730289
theorem B1011275 : Blo 471786 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1601099 : Blo 471786 1601099 := bstep (se 1 (by rfl) ⟨1200824, by rfl⟩ : syracuseStep 1601099 = 2401649) B2401649
theorem B912971 : Blo 471786 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B1797835 : Blo 471786 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B1830617 : Blo 471786 1830617 := bstep (se 2 (by rfl) ⟨686481, by rfl⟩ : syracuseStep 1830617 = 1372963) B1372963
theorem B6811397 : Blo 471786 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B2027281 : Blo 471786 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B1601369 : Blo 471786 1601369 := bstep (se 2 (by rfl) ⟨600513, by rfl⟩ : syracuseStep 1601369 = 1201027) B1201027
theorem B1798109 : Blo 471786 1798109 := bstep (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) B674291
theorem B4944023 : Blo 471786 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B913739 : Blo 471786 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B1012171 : Blo 471786 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B1602071 : Blo 471786 1602071 := bstep (se 1 (by rfl) ⟨1201553, by rfl⟩ : syracuseStep 1602071 = 2403107) B2403107
theorem B1798807 : Blo 471786 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B4453069 : Blo 471786 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B717527 : Blo 471786 717527 := bstep (se 1 (by rfl) ⟨538145, by rfl⟩ : syracuseStep 717527 = 1076291) B1076291
theorem B2159405 : Blo 471786 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B685003 : Blo 471786 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B3404749 : Blo 471786 3404749 := bstep (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) B1276781
theorem B4060165 : Blo 471786 4060165 := bstep (se 4 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 4060165 = 761281) B761281
theorem B1602611 : Blo 471786 1602611 := bstep (se 1 (by rfl) ⟨1201958, by rfl⟩ : syracuseStep 1602611 = 2403917) B2403917
theorem B6059083 : Blo 471786 6059083 := bstep (se 1 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 6059083 = 9088625) B9088625
theorem B1012915 : Blo 471786 1012915 := bstep (se 1 (by rfl) ⟨759686, by rfl⟩ : syracuseStep 1012915 = 1519373) B1519373
theorem B1602881 : Blo 471786 1602881 := bstep (se 2 (by rfl) ⟨601080, by rfl⟩ : syracuseStep 1602881 = 1202161) B1202161
theorem B1799597 : Blo 471786 1799597 := bstep (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) B674849
theorem B5174705 : Blo 471786 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B2192861 : Blo 471786 2192861 := bstep (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) B822323
theorem B1013401 : Blo 471786 1013401 := bstep (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) B760051
theorem B1603421 : Blo 471786 1603421 := bstep (se 3 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 1603421 = 601283) B601283
theorem B1701811 : Blo 471786 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B555031 : Blo 471786 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B2029657 : Blo 471786 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B2390147 : Blo 471786 2390147 := bstep (se 1 (by rfl) ⟨1792610, by rfl⟩ : syracuseStep 2390147 = 3585221) B3585221
theorem B850265 : Blo 471786 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B1440089 : Blo 471786 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B1801025 : Blo 471786 1801025 := bstep (se 2 (by rfl) ⟨675384, by rfl⟩ : syracuseStep 1801025 = 1350769) B1350769
theorem B850763 : Blo 471786 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B1604555 : Blo 471786 1604555 := bstep (se 1 (by rfl) ⟨1203416, by rfl⟩ : syracuseStep 1604555 = 2406833) B2406833
theorem B2030615 : Blo 471786 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B1014871 : Blo 471786 1014871 := bstep (se 1 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 1014871 = 1522307) B1522307
theorem B1014923 : Blo 471786 1014923 := bstep (se 1 (by rfl) ⟨761192, by rfl⟩ : syracuseStep 1014923 = 1522385) B1522385
theorem B1604825 : Blo 471786 1604825 := bstep (se 2 (by rfl) ⟨601809, by rfl⟩ : syracuseStep 1604825 = 1203619) B1203619
theorem B14548373 : Blo 471786 14548373 := bstep (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) B681955
theorem B1736129 : Blo 471786 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B4062899 : Blo 471786 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B1605527 : Blo 471786 1605527 := bstep (se 1 (by rfl) ⟨1204145, by rfl⟩ : syracuseStep 1605527 = 2408291) B2408291
theorem B1802681 : Blo 471786 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B1344185 : Blo 471786 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B2917093 : Blo 471786 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B852751 : Blo 471786 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B1114913 : Blo 471786 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1803667 : Blo 471786 1803667 := bstep (se 1 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 1803667 = 2705501) B2705501
theorem B3409451 : Blo 471786 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B2688713 : Blo 471786 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B4851757 : Blo 471786 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B1345825 : Blo 471786 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B2394521 : Blo 471786 2394521 := bstep (se 2 (by rfl) ⟨897945, by rfl⟩ : syracuseStep 2394521 = 1795891) B1795891
theorem B21629405 : Blo 471786 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B756425 : Blo 471786 756425 := bstep (se 2 (by rfl) ⟨283659, by rfl⟩ : syracuseStep 756425 = 567319) B567319
theorem B4557617 : Blo 471786 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B1805399 : Blo 471786 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B6065441 : Blo 471786 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B1347101 : Blo 471786 1347101 := bstep (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) B505163
theorem B2690603 : Blo 471786 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B1805885 : Blo 471786 1805885 := bstep (se 3 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 1805885 = 677207) B677207
theorem B2887235 : Blo 471786 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1969921 : Blo 471786 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347329 : Blo 471786 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B1347671 : Blo 471786 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B856183 : Blo 471786 856183 := bstep (se 1 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 856183 = 1284275) B1284275
theorem B1347785 : Blo 471786 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B8065655 : Blo 471786 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B2397113 : Blo 471786 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B2692061 : Blo 471786 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B2692561 : Blo 471786 2692561 := bstep (se 2 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 2692561 = 2019421) B2019421
theorem B759431 : Blo 471786 759431 := bstep (se 1 (by rfl) ⟨569573, by rfl⟩ : syracuseStep 759431 = 1139147) B1139147
theorem B1513363 : Blo 471786 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B1349561 : Blo 471786 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B2299927 : Blo 471786 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B2398409 : Blo 471786 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B17307917 : Blo 471786 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B5937425 : Blo 471786 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B530959 : Blo 471786 530959 := bstep (se 1 (by rfl) ⟨398219, by rfl⟩ : syracuseStep 530959 = 796439) B796439
theorem B1710679 : Blo 471786 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B5413553 : Blo 471786 5413553 := bstep (se 2 (by rfl) ⟨2030082, by rfl⟩ : syracuseStep 5413553 = 4060165) B4060165
theorem B1284923 : Blo 471786 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B3414899 : Blo 471786 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B1350553 : Blo 471786 1350553 := bstep (se 2 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 1350553 = 1012915) B1012915
theorem B4332491 : Blo 471786 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B531463 : Blo 471786 531463 := bstep (se 1 (by rfl) ⟨398597, by rfl⟩ : syracuseStep 531463 = 797195) B797195
theorem B597127 : Blo 471786 597127 := bstep (se 1 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 597127 = 895691) B895691
theorem B531643 : Blo 471786 531643 := bstep (se 1 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 531643 = 797465) B797465
theorem B10132867 : Blo 471786 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2694545 : Blo 471786 2694545 := bstep (se 2 (by rfl) ⟨1010454, by rfl⟩ : syracuseStep 2694545 = 2020909) B2020909
theorem B597547 : Blo 471786 597547 := bstep (se 1 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 597547 = 896321) B896321
theorem B532111 : Blo 471786 532111 := bstep (se 1 (by rfl) ⟨399083, by rfl⟩ : syracuseStep 532111 = 798167) B798167
theorem B20717207 : Blo 471786 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B597775 : Blo 471786 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B34676525 : Blo 471786 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B1220411 : Blo 471786 1220411 := bstep (se 1 (by rfl) ⟨915308, by rfl⟩ : syracuseStep 1220411 = 1830617) B1830617
theorem B5447513 : Blo 471786 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B2269081 : Blo 471786 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B1515581 : Blo 471786 1515581 := bstep (se 3 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 1515581 = 568343) B568343
theorem B532615 : Blo 471786 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B5775533 : Blo 471786 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B532795 : Blo 471786 532795 := bstep (se 1 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 532795 = 799193) B799193
theorem B598519 : Blo 471786 598519 := bstep (se 1 (by rfl) ⟨448889, by rfl⟩ : syracuseStep 598519 = 897779) B897779
theorem B533263 : Blo 471786 533263 := bstep (se 1 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 533263 = 799895) B799895
theorem B1352477 : Blo 471786 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B598843 : Blo 471786 598843 := bstep (se 1 (by rfl) ⟨449132, by rfl⟩ : syracuseStep 598843 = 898265) B898265
theorem B3449803 : Blo 471786 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B1516745 : Blo 471786 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B533767 : Blo 471786 533767 := bstep (se 1 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 533767 = 800651) B800651
theorem B599339 : Blo 471786 599339 := bstep (se 1 (by rfl) ⟨449504, by rfl⟩ : syracuseStep 599339 = 899009) B899009
theorem B533947 : Blo 471786 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B1353161 : Blo 471786 1353161 := bstep (se 2 (by rfl) ⟨507435, by rfl⟩ : syracuseStep 1353161 = 1014871) B1014871
theorem B566843 : Blo 471786 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B960059 : Blo 471786 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599815 : Blo 471786 599815 := bstep (se 1 (by rfl) ⟨449861, by rfl⟩ : syracuseStep 599815 = 899723) B899723
theorem B796459 : Blo 471786 796459 := bstep (se 1 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 796459 = 1194689) B1194689
theorem B927607 : Blo 471786 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B567175 : Blo 471786 567175 := bstep (se 1 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 567175 = 850763) B850763
theorem B534415 : Blo 471786 534415 := bstep (se 1 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 534415 = 801623) B801623
theorem B796601 : Blo 471786 796601 := bstep (se 2 (by rfl) ⟨298725, by rfl⟩ : syracuseStep 796601 = 597451) B597451
theorem B1353743 : Blo 471786 1353743 := bstep (se 1 (by rfl) ⟨1015307, by rfl⟩ : syracuseStep 1353743 = 2030615) B2030615
theorem B5384393 : Blo 471786 5384393 := bstep (se 2 (by rfl) ⟨2019147, by rfl⟩ : syracuseStep 5384393 = 4038295) B4038295
theorem B600311 : Blo 471786 600311 := bstep (se 1 (by rfl) ⟨450233, by rfl⟩ : syracuseStep 600311 = 900467) B900467
theorem B1157419 : Blo 471786 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B534919 : Blo 471786 534919 := bstep (se 1 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 534919 = 802379) B802379
theorem B600463 : Blo 471786 600463 := bstep (se 1 (by rfl) ⟨450347, by rfl⟩ : syracuseStep 600463 = 900695) B900695
theorem B600635 : Blo 471786 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B535099 : Blo 471786 535099 := bstep (se 1 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 535099 = 802649) B802649
theorem B797303 : Blo 471786 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B2960165 : Blo 471786 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B797755 : Blo 471786 797755 := bstep (se 1 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 797755 = 1196633) B1196633
theorem B8105021 : Blo 471786 8105021 := bstep (se 3 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 8105021 = 3039383) B3039383
theorem B797897 : Blo 471786 797897 := bstep (se 2 (by rfl) ⟨299211, by rfl⟩ : syracuseStep 797897 = 598423) B598423
theorem B2043137 : Blo 471786 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B2272697 : Blo 471786 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B601607 : Blo 471786 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B2436637 : Blo 471786 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B2305655 : Blo 471786 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B2043649 : Blo 471786 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B798599 : Blo 471786 798599 := bstep (se 1 (by rfl) ⟨598949, by rfl⟩ : syracuseStep 798599 = 1197899) B1197899
theorem B2404241 : Blo 471786 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B7679947 : Blo 471786 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B3321917 : Blo 471786 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B2699351 : Blo 471786 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B897551 : Blo 471786 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B799247 : Blo 471786 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B471815 : Blo 471786 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B471823 : Blo 471786 471823 := bstep (se 1 (by rfl) ⟨353867, by rfl⟩ : syracuseStep 471823 = 707735) B707735
theorem B1061675 : Blo 471786 1061675 := bstep (se 1 (by rfl) ⟨796256, by rfl⟩ : syracuseStep 1061675 = 1592513) B1592513
theorem B471867 : Blo 471786 471867 := bstep (se 1 (by rfl) ⟨353900, by rfl⟩ : syracuseStep 471867 = 707801) B707801
theorem B471943 : Blo 471786 471943 := bstep (se 1 (by rfl) ⟨353957, by rfl⟩ : syracuseStep 471943 = 707915) B707915
theorem B471951 : Blo 471786 471951 := bstep (se 1 (by rfl) ⟨353963, by rfl⟩ : syracuseStep 471951 = 707927) B707927
theorem B471995 : Blo 471786 471995 := bstep (se 1 (by rfl) ⟨353996, by rfl⟩ : syracuseStep 471995 = 707993) B707993
theorem B3847115 : Blo 471786 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B472071 : Blo 471786 472071 := bstep (se 1 (by rfl) ⟨354053, by rfl⟩ : syracuseStep 472071 = 708107) B708107
theorem B4568075 : Blo 471786 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B472079 : Blo 471786 472079 := bstep (se 1 (by rfl) ⟨354059, by rfl⟩ : syracuseStep 472079 = 708119) B708119
theorem B799787 : Blo 471786 799787 := bstep (se 1 (by rfl) ⟨599840, by rfl⟩ : syracuseStep 799787 = 1199681) B1199681
theorem B5387309 : Blo 471786 5387309 := bstep (se 3 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 5387309 = 2020241) B2020241
theorem B472123 : Blo 471786 472123 := bstep (se 1 (by rfl) ⟨354092, by rfl⟩ : syracuseStep 472123 = 708185) B708185
theorem B472199 : Blo 471786 472199 := bstep (se 1 (by rfl) ⟨354149, by rfl⟩ : syracuseStep 472199 = 708299) B708299
theorem B472207 : Blo 471786 472207 := bstep (se 1 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 472207 = 708311) B708311
theorem B1062035 : Blo 471786 1062035 := bstep (se 1 (by rfl) ⟨796526, by rfl⟩ : syracuseStep 1062035 = 1593053) B1593053
theorem B472251 : Blo 471786 472251 := bstep (se 1 (by rfl) ⟨354188, by rfl⟩ : syracuseStep 472251 = 708377) B708377
theorem B1062089 : Blo 471786 1062089 := bstep (se 2 (by rfl) ⟨398283, by rfl⟩ : syracuseStep 1062089 = 796567) B796567
theorem B3421385 : Blo 471786 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B472327 : Blo 471786 472327 := bstep (se 1 (by rfl) ⟨354245, by rfl⟩ : syracuseStep 472327 = 708491) B708491
theorem B472335 : Blo 471786 472335 := bstep (se 1 (by rfl) ⟨354251, by rfl⟩ : syracuseStep 472335 = 708503) B708503
theorem B472379 : Blo 471786 472379 := bstep (se 1 (by rfl) ⟨354284, by rfl⟩ : syracuseStep 472379 = 708569) B708569
theorem B472455 : Blo 471786 472455 := bstep (se 1 (by rfl) ⟨354341, by rfl⟩ : syracuseStep 472455 = 708683) B708683
theorem B472463 : Blo 471786 472463 := bstep (se 1 (by rfl) ⟨354347, by rfl⟩ : syracuseStep 472463 = 708695) B708695
theorem B800185 : Blo 471786 800185 := bstep (se 2 (by rfl) ⟨300069, by rfl⟩ : syracuseStep 800185 = 600139) B600139
theorem B472507 : Blo 471786 472507 := bstep (se 1 (by rfl) ⟨354380, by rfl⟩ : syracuseStep 472507 = 708761) B708761
theorem B472583 : Blo 471786 472583 := bstep (se 1 (by rfl) ⟨354437, by rfl⟩ : syracuseStep 472583 = 708875) B708875
theorem B472591 : Blo 471786 472591 := bstep (se 1 (by rfl) ⟨354443, by rfl⟩ : syracuseStep 472591 = 708887) B708887
theorem B472635 : Blo 471786 472635 := bstep (se 1 (by rfl) ⟨354476, by rfl⟩ : syracuseStep 472635 = 708953) B708953
theorem B9090629 : Blo 471786 9090629 := bstep (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) B1704493
theorem B472711 : Blo 471786 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B472719 : Blo 471786 472719 := bstep (se 1 (by rfl) ⟨354539, by rfl⟩ : syracuseStep 472719 = 709079) B709079
theorem B964243 : Blo 471786 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B472763 : Blo 471786 472763 := bstep (se 1 (by rfl) ⟨354572, by rfl⟩ : syracuseStep 472763 = 709145) B709145
theorem B472839 : Blo 471786 472839 := bstep (se 1 (by rfl) ⟨354629, by rfl⟩ : syracuseStep 472839 = 709259) B709259
theorem B505607 : Blo 471786 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B472847 : Blo 471786 472847 := bstep (se 1 (by rfl) ⟨354635, by rfl⟩ : syracuseStep 472847 = 709271) B709271
theorem B472891 : Blo 471786 472891 := bstep (se 1 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 472891 = 709337) B709337
theorem B2439001 : Blo 471786 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B1062791 : Blo 471786 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B472967 : Blo 471786 472967 := bstep (se 1 (by rfl) ⟨354725, by rfl⟩ : syracuseStep 472967 = 709451) B709451
theorem B472975 : Blo 471786 472975 := bstep (se 1 (by rfl) ⟨354731, by rfl⟩ : syracuseStep 472975 = 709463) B709463
theorem B571307 : Blo 471786 571307 := bstep (se 1 (by rfl) ⟨428480, by rfl⟩ : syracuseStep 571307 = 856961) B856961
theorem B473019 : Blo 471786 473019 := bstep (se 1 (by rfl) ⟨354764, by rfl⟩ : syracuseStep 473019 = 709529) B709529
theorem B2406347 : Blo 471786 2406347 := bstep (se 1 (by rfl) ⟨1804760, by rfl⟩ : syracuseStep 2406347 = 3609521) B3609521
theorem B473095 : Blo 471786 473095 := bstep (se 1 (by rfl) ⟨354821, by rfl⟩ : syracuseStep 473095 = 709643) B709643
theorem B473103 : Blo 471786 473103 := bstep (se 1 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 473103 = 709655) B709655
theorem B1062971 : Blo 471786 1062971 := bstep (se 1 (by rfl) ⟨797228, by rfl⟩ : syracuseStep 1062971 = 1594457) B1594457
theorem B473147 : Blo 471786 473147 := bstep (se 1 (by rfl) ⟨354860, by rfl⟩ : syracuseStep 473147 = 709721) B709721
theorem B899191 : Blo 471786 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B800887 : Blo 471786 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B473223 : Blo 471786 473223 := bstep (se 1 (by rfl) ⟨354917, by rfl⟩ : syracuseStep 473223 = 709835) B709835
theorem B473231 : Blo 471786 473231 := bstep (se 1 (by rfl) ⟨354923, by rfl⟩ : syracuseStep 473231 = 709847) B709847
theorem B1063097 : Blo 471786 1063097 := bstep (se 2 (by rfl) ⟨398661, by rfl⟩ : syracuseStep 1063097 = 797323) B797323
theorem B473275 : Blo 471786 473275 := bstep (se 1 (by rfl) ⟨354956, by rfl⟩ : syracuseStep 473275 = 709913) B709913
theorem B473351 : Blo 471786 473351 := bstep (se 1 (by rfl) ⟨355013, by rfl⟩ : syracuseStep 473351 = 710027) B710027
theorem B473359 : Blo 471786 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B2701583 : Blo 471786 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B2406671 : Blo 471786 2406671 := bstep (se 1 (by rfl) ⟨1805003, by rfl⟩ : syracuseStep 2406671 = 3610007) B3610007
theorem B473403 : Blo 471786 473403 := bstep (se 1 (by rfl) ⟨355052, by rfl⟩ : syracuseStep 473403 = 710105) B710105
theorem B801083 : Blo 471786 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B473479 : Blo 471786 473479 := bstep (se 1 (by rfl) ⟨355109, by rfl⟩ : syracuseStep 473479 = 710219) B710219
theorem B473487 : Blo 471786 473487 := bstep (se 1 (by rfl) ⟨355115, by rfl⟩ : syracuseStep 473487 = 710231) B710231
theorem B473531 : Blo 471786 473531 := bstep (se 1 (by rfl) ⟨355148, by rfl⟩ : syracuseStep 473531 = 710297) B710297
theorem B1194497 : Blo 471786 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B473607 : Blo 471786 473607 := bstep (se 1 (by rfl) ⟨355205, by rfl⟩ : syracuseStep 473607 = 710411) B710411
theorem B2701835 : Blo 471786 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B1063439 : Blo 471786 1063439 := bstep (se 1 (by rfl) ⟨797579, by rfl⟩ : syracuseStep 1063439 = 1595159) B1595159
theorem B473615 : Blo 471786 473615 := bstep (se 1 (by rfl) ⟨355211, by rfl⟩ : syracuseStep 473615 = 710423) B710423
theorem B1063457 : Blo 471786 1063457 := bstep (se 2 (by rfl) ⟨398796, by rfl⟩ : syracuseStep 1063457 = 797593) B797593
theorem B473659 : Blo 471786 473659 := bstep (se 1 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 473659 = 710489) B710489
theorem B3586679 : Blo 471786 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B473735 : Blo 471786 473735 := bstep (se 1 (by rfl) ⟨355301, by rfl⟩ : syracuseStep 473735 = 710603) B710603
theorem B473743 : Blo 471786 473743 := bstep (se 1 (by rfl) ⟨355307, by rfl⟩ : syracuseStep 473743 = 710615) B710615
theorem B473787 : Blo 471786 473787 := bstep (se 1 (by rfl) ⟨355340, by rfl⟩ : syracuseStep 473787 = 710681) B710681
theorem B801481 : Blo 471786 801481 := bstep (se 2 (by rfl) ⟨300555, by rfl⟩ : syracuseStep 801481 = 601111) B601111
theorem B473863 : Blo 471786 473863 := bstep (se 1 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 473863 = 710795) B710795
theorem B473871 : Blo 471786 473871 := bstep (se 1 (by rfl) ⟨355403, by rfl⟩ : syracuseStep 473871 = 710807) B710807
theorem B473915 : Blo 471786 473915 := bstep (se 1 (by rfl) ⟨355436, by rfl⟩ : syracuseStep 473915 = 710873) B710873
theorem B1194871 : Blo 471786 1194871 := bstep (se 1 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 1194871 = 1792307) B1792307
theorem B1063799 : Blo 471786 1063799 := bstep (se 1 (by rfl) ⟨797849, by rfl⟩ : syracuseStep 1063799 = 1595699) B1595699
theorem B867191 : Blo 471786 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B473991 : Blo 471786 473991 := bstep (se 1 (by rfl) ⟨355493, by rfl⟩ : syracuseStep 473991 = 710987) B710987
theorem B473999 : Blo 471786 473999 := bstep (se 1 (by rfl) ⟨355499, by rfl⟩ : syracuseStep 473999 = 710999) B710999
theorem B4537241 : Blo 471786 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B474043 : Blo 471786 474043 := bstep (se 1 (by rfl) ⟨355532, by rfl⟩ : syracuseStep 474043 = 711065) B711065
theorem B474119 : Blo 471786 474119 := bstep (se 1 (by rfl) ⟨355589, by rfl⟩ : syracuseStep 474119 = 711179) B711179
theorem B1621003 : Blo 471786 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B474127 : Blo 471786 474127 := bstep (se 1 (by rfl) ⟨355595, by rfl⟩ : syracuseStep 474127 = 711191) B711191
theorem B1063979 : Blo 471786 1063979 := bstep (se 1 (by rfl) ⟨797984, by rfl⟩ : syracuseStep 1063979 = 1595969) B1595969
theorem B474171 : Blo 471786 474171 := bstep (se 1 (by rfl) ⟨355628, by rfl⟩ : syracuseStep 474171 = 711257) B711257
theorem B474247 : Blo 471786 474247 := bstep (se 1 (by rfl) ⟨355685, by rfl⟩ : syracuseStep 474247 = 711371) B711371
theorem B474255 : Blo 471786 474255 := bstep (se 1 (by rfl) ⟨355691, by rfl⟩ : syracuseStep 474255 = 711383) B711383
theorem B474299 : Blo 471786 474299 := bstep (se 1 (by rfl) ⟨355724, by rfl⟩ : syracuseStep 474299 = 711449) B711449
theorem B474375 : Blo 471786 474375 := bstep (se 1 (by rfl) ⟨355781, by rfl⟩ : syracuseStep 474375 = 711563) B711563
theorem B474383 : Blo 471786 474383 := bstep (se 1 (by rfl) ⟨355787, by rfl⟩ : syracuseStep 474383 = 711575) B711575
theorem B1195307 : Blo 471786 1195307 := bstep (se 1 (by rfl) ⟨896480, by rfl⟩ : syracuseStep 1195307 = 1792961) B1792961
theorem B474427 : Blo 471786 474427 := bstep (se 1 (by rfl) ⟨355820, by rfl⟩ : syracuseStep 474427 = 711641) B711641
theorem B474503 : Blo 471786 474503 := bstep (se 1 (by rfl) ⟨355877, by rfl⟩ : syracuseStep 474503 = 711755) B711755
theorem B802183 : Blo 471786 802183 := bstep (se 1 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 802183 = 1203275) B1203275
theorem B474511 : Blo 471786 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B1064339 : Blo 471786 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B474555 : Blo 471786 474555 := bstep (se 1 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 474555 = 711833) B711833
theorem B1064393 : Blo 471786 1064393 := bstep (se 2 (by rfl) ⟨399147, by rfl⟩ : syracuseStep 1064393 = 798295) B798295
theorem B474631 : Blo 471786 474631 := bstep (se 1 (by rfl) ⟨355973, by rfl⟩ : syracuseStep 474631 = 711947) B711947
theorem B474639 : Blo 471786 474639 := bstep (se 1 (by rfl) ⟨355979, by rfl⟩ : syracuseStep 474639 = 711959) B711959
theorem B474683 : Blo 471786 474683 := bstep (se 1 (by rfl) ⟨356012, by rfl⟩ : syracuseStep 474683 = 712025) B712025
theorem B3587651 : Blo 471786 3587651 := bstep (se 1 (by rfl) ⟨2690738, by rfl⟩ : syracuseStep 3587651 = 5381477) B5381477
theorem B474759 : Blo 471786 474759 := bstep (se 1 (by rfl) ⟨356069, by rfl⟩ : syracuseStep 474759 = 712139) B712139
theorem B474767 : Blo 471786 474767 := bstep (se 1 (by rfl) ⟨356075, by rfl⟩ : syracuseStep 474767 = 712151) B712151
theorem B474811 : Blo 471786 474811 := bstep (se 1 (by rfl) ⟨356108, by rfl⟩ : syracuseStep 474811 = 712217) B712217
theorem B2703041 : Blo 471786 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B2408129 : Blo 471786 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B474887 : Blo 471786 474887 := bstep (se 1 (by rfl) ⟨356165, by rfl⟩ : syracuseStep 474887 = 712331) B712331
theorem B474895 : Blo 471786 474895 := bstep (se 1 (by rfl) ⟨356171, by rfl⟩ : syracuseStep 474895 = 712343) B712343
theorem B2309939 : Blo 471786 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B474939 : Blo 471786 474939 := bstep (se 1 (by rfl) ⟨356204, by rfl⟩ : syracuseStep 474939 = 712409) B712409
theorem B900983 : Blo 471786 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B475015 : Blo 471786 475015 := bstep (se 1 (by rfl) ⟨356261, by rfl⟩ : syracuseStep 475015 = 712523) B712523
theorem B475023 : Blo 471786 475023 := bstep (se 1 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 475023 = 712535) B712535
theorem B20234137 : Blo 471786 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B475067 : Blo 471786 475067 := bstep (se 1 (by rfl) ⟨356300, by rfl⟩ : syracuseStep 475067 = 712601) B712601
theorem B475143 : Blo 471786 475143 := bstep (se 1 (by rfl) ⟨356357, by rfl⟩ : syracuseStep 475143 = 712715) B712715
theorem B901135 : Blo 471786 901135 := bstep (se 1 (by rfl) ⟨675851, by rfl⟩ : syracuseStep 901135 = 1351703) B1351703
theorem B475151 : Blo 471786 475151 := bstep (se 1 (by rfl) ⟨356363, by rfl⟩ : syracuseStep 475151 = 712727) B712727
theorem B802831 : Blo 471786 802831 := bstep (se 1 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 802831 = 1204247) B1204247
theorem B475195 : Blo 471786 475195 := bstep (se 1 (by rfl) ⟨356396, by rfl⟩ : syracuseStep 475195 = 712793) B712793
theorem B1196147 : Blo 471786 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1196167 : Blo 471786 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1065095 : Blo 471786 1065095 := bstep (se 1 (by rfl) ⟨798821, by rfl⟩ : syracuseStep 1065095 = 1597643) B1597643
theorem B475271 : Blo 471786 475271 := bstep (se 1 (by rfl) ⟨356453, by rfl⟩ : syracuseStep 475271 = 712907) B712907
theorem B475279 : Blo 471786 475279 := bstep (se 1 (by rfl) ⟨356459, by rfl⟩ : syracuseStep 475279 = 712919) B712919
theorem B475323 : Blo 471786 475323 := bstep (se 1 (by rfl) ⟨356492, by rfl⟩ : syracuseStep 475323 = 712985) B712985
theorem B475399 : Blo 471786 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B475407 : Blo 471786 475407 := bstep (se 1 (by rfl) ⟨356555, by rfl⟩ : syracuseStep 475407 = 713111) B713111
theorem B1065275 : Blo 471786 1065275 := bstep (se 1 (by rfl) ⟨798956, by rfl⟩ : syracuseStep 1065275 = 1597913) B1597913
theorem B475451 : Blo 471786 475451 := bstep (se 1 (by rfl) ⟨356588, by rfl⟩ : syracuseStep 475451 = 713177) B713177
theorem B475527 : Blo 471786 475527 := bstep (se 1 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 475527 = 713291) B713291
theorem B475535 : Blo 471786 475535 := bstep (se 1 (by rfl) ⟨356651, by rfl⟩ : syracuseStep 475535 = 713303) B713303
theorem B901523 : Blo 471786 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B1196441 : Blo 471786 1196441 := bstep (se 2 (by rfl) ⟨448665, by rfl⟩ : syracuseStep 1196441 = 897331) B897331
theorem B1065401 : Blo 471786 1065401 := bstep (se 2 (by rfl) ⟨399525, by rfl⟩ : syracuseStep 1065401 = 799051) B799051
theorem B475579 : Blo 471786 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B475655 : Blo 471786 475655 := bstep (se 1 (by rfl) ⟨356741, by rfl⟩ : syracuseStep 475655 = 713483) B713483
theorem B475663 : Blo 471786 475663 := bstep (se 1 (by rfl) ⟨356747, by rfl⟩ : syracuseStep 475663 = 713495) B713495
theorem B1196603 : Blo 471786 1196603 := bstep (se 1 (by rfl) ⟨897452, by rfl⟩ : syracuseStep 1196603 = 1794905) B1794905
theorem B475707 : Blo 471786 475707 := bstep (se 1 (by rfl) ⟨356780, by rfl⟩ : syracuseStep 475707 = 713561) B713561
theorem B475783 : Blo 471786 475783 := bstep (se 1 (by rfl) ⟨356837, by rfl⟩ : syracuseStep 475783 = 713675) B713675
theorem B672457 : Blo 471786 672457 := bstep (se 2 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 672457 = 504343) B504343
theorem B79086293 : Blo 471786 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B1196815 : Blo 471786 1196815 := bstep (se 1 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 1196815 = 1795223) B1795223
theorem B1065743 : Blo 471786 1065743 := bstep (se 1 (by rfl) ⟨799307, by rfl⟩ : syracuseStep 1065743 = 1598615) B1598615
theorem B1065761 : Blo 471786 1065761 := bstep (se 2 (by rfl) ⟨399660, by rfl⟩ : syracuseStep 1065761 = 799321) B799321
theorem B3425075 : Blo 471786 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B672571 : Blo 471786 672571 := bstep (se 1 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 672571 = 1008857) B1008857
theorem B1197089 : Blo 471786 1197089 := bstep (se 2 (by rfl) ⟨448908, by rfl⟩ : syracuseStep 1197089 = 897817) B897817
theorem B1819691 : Blo 471786 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B574523 : Blo 471786 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B1066103 : Blo 471786 1066103 := bstep (se 1 (by rfl) ⟨799577, by rfl⟩ : syracuseStep 1066103 = 1599155) B1599155
theorem B4539665 : Blo 471786 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B1066283 : Blo 471786 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B542095 : Blo 471786 542095 := bstep (se 1 (by rfl) ⟨406571, by rfl⟩ : syracuseStep 542095 = 813143) B813143
theorem B8078777 : Blo 471786 8078777 := bstep (se 2 (by rfl) ⟨3029541, by rfl⟩ : syracuseStep 8078777 = 6059083) B6059083
theorem B1066643 : Blo 471786 1066643 := bstep (se 1 (by rfl) ⟨799982, by rfl⟩ : syracuseStep 1066643 = 1599965) B1599965
theorem B1066697 : Blo 471786 1066697 := bstep (se 2 (by rfl) ⟨400011, by rfl⟩ : syracuseStep 1066697 = 800023) B800023
theorem B902927 : Blo 471786 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B2606995 : Blo 471786 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B1198091 : Blo 471786 1198091 := bstep (se 1 (by rfl) ⟨898568, by rfl⟩ : syracuseStep 1198091 = 1797137) B1797137
theorem B674183 : Blo 471786 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B1067399 : Blo 471786 1067399 := bstep (se 1 (by rfl) ⟨800549, by rfl⟩ : syracuseStep 1067399 = 1601099) B1601099
theorem B608647 : Blo 471786 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B4540931 : Blo 471786 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B1067579 : Blo 471786 1067579 := bstep (se 1 (by rfl) ⟨800684, by rfl⟩ : syracuseStep 1067579 = 1601369) B1601369
theorem B23382593 : Blo 471786 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B3426893 : Blo 471786 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B1198739 : Blo 471786 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B1067705 : Blo 471786 1067705 := bstep (se 2 (by rfl) ⟨400389, by rfl⟩ : syracuseStep 1067705 = 800779) B800779
theorem B3296015 : Blo 471786 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B2706209 : Blo 471786 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B2280307 : Blo 471786 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B1199033 : Blo 471786 1199033 := bstep (se 2 (by rfl) ⟨449637, by rfl⟩ : syracuseStep 1199033 = 899275) B899275
theorem B14797835 : Blo 471786 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B1068047 : Blo 471786 1068047 := bstep (se 1 (by rfl) ⟨801035, by rfl⟩ : syracuseStep 1068047 = 1602071) B1602071
theorem B1068065 : Blo 471786 1068065 := bstep (se 2 (by rfl) ⟨400524, by rfl⟩ : syracuseStep 1068065 = 801049) B801049
theorem B478351 : Blo 471786 478351 := bstep (se 1 (by rfl) ⟨358763, by rfl⟩ : syracuseStep 478351 = 717527) B717527
theorem B707771 : Blo 471786 707771 := bstep (se 1 (by rfl) ⟨530828, by rfl⟩ : syracuseStep 707771 = 1061657) B1061657
theorem B707831 : Blo 471786 707831 := bstep (se 1 (by rfl) ⟨530873, by rfl⟩ : syracuseStep 707831 = 1061747) B1061747
theorem B707855 : Blo 471786 707855 := bstep (se 1 (by rfl) ⟨530891, by rfl⟩ : syracuseStep 707855 = 1061783) B1061783
theorem B707897 : Blo 471786 707897 := bstep (se 2 (by rfl) ⟨265461, by rfl⟩ : syracuseStep 707897 = 530923) B530923
theorem B675145 : Blo 471786 675145 := bstep (se 2 (by rfl) ⟨253179, by rfl⟩ : syracuseStep 675145 = 506359) B506359
theorem B1068407 : Blo 471786 1068407 := bstep (se 1 (by rfl) ⟨801305, by rfl⟩ : syracuseStep 1068407 = 1602611) B1602611
theorem B707975 : Blo 471786 707975 := bstep (se 1 (by rfl) ⟨530981, by rfl⟩ : syracuseStep 707975 = 1061963) B1061963
theorem B1592729 : Blo 471786 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B708011 : Blo 471786 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B708041 : Blo 471786 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B1068587 : Blo 471786 1068587 := bstep (se 1 (by rfl) ⟨801440, by rfl⟩ : syracuseStep 1068587 = 1602881) B1602881
theorem B708155 : Blo 471786 708155 := bstep (se 1 (by rfl) ⟨531116, by rfl⟩ : syracuseStep 708155 = 1062233) B1062233
theorem B22171229 : Blo 471786 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1199731 : Blo 471786 1199731 := bstep (se 1 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 1199731 = 1799597) B1799597
theorem B708215 : Blo 471786 708215 := bstep (se 1 (by rfl) ⟨531161, by rfl⟩ : syracuseStep 708215 = 1062323) B1062323
theorem B708239 : Blo 471786 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B1461907 : Blo 471786 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B708281 : Blo 471786 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B1199873 : Blo 471786 1199873 := bstep (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) B899905
theorem B708359 : Blo 471786 708359 := bstep (se 1 (by rfl) ⟨531269, by rfl⟩ : syracuseStep 708359 = 1062539) B1062539
theorem B708395 : Blo 471786 708395 := bstep (se 1 (by rfl) ⟨531296, by rfl⟩ : syracuseStep 708395 = 1062593) B1062593
theorem B675641 : Blo 471786 675641 := bstep (se 2 (by rfl) ⟨253365, by rfl⟩ : syracuseStep 675641 = 506731) B506731
theorem B708425 : Blo 471786 708425 := bstep (se 2 (by rfl) ⟨265659, by rfl⟩ : syracuseStep 708425 = 531319) B531319
theorem B3592025 : Blo 471786 3592025 := bstep (se 2 (by rfl) ⟨1347009, by rfl⟩ : syracuseStep 3592025 = 2694019) B2694019
theorem B1068947 : Blo 471786 1068947 := bstep (se 1 (by rfl) ⟨801710, by rfl⟩ : syracuseStep 1068947 = 1603421) B1603421
theorem B708539 : Blo 471786 708539 := bstep (se 1 (by rfl) ⟨531404, by rfl⟩ : syracuseStep 708539 = 1062809) B1062809
theorem B1069001 : Blo 471786 1069001 := bstep (se 2 (by rfl) ⟨400875, by rfl⟩ : syracuseStep 1069001 = 801751) B801751
theorem B708599 : Blo 471786 708599 := bstep (se 1 (by rfl) ⟨531449, by rfl⟩ : syracuseStep 708599 = 1062899) B1062899
theorem B708623 : Blo 471786 708623 := bstep (se 1 (by rfl) ⟨531467, by rfl⟩ : syracuseStep 708623 = 1062935) B1062935
theorem B708665 : Blo 471786 708665 := bstep (se 2 (by rfl) ⟨265749, by rfl⟩ : syracuseStep 708665 = 531499) B531499
theorem B1593431 : Blo 471786 1593431 := bstep (se 1 (by rfl) ⟨1195073, by rfl⟩ : syracuseStep 1593431 = 2390147) B2390147
theorem B708743 : Blo 471786 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B708779 : Blo 471786 708779 := bstep (se 1 (by rfl) ⟨531584, by rfl⟩ : syracuseStep 708779 = 1063169) B1063169
theorem B708809 : Blo 471786 708809 := bstep (se 2 (by rfl) ⟨265803, by rfl⟩ : syracuseStep 708809 = 531607) B531607
theorem B1200329 : Blo 471786 1200329 := bstep (se 2 (by rfl) ⟨450123, by rfl⟩ : syracuseStep 1200329 = 900247) B900247
theorem B708923 : Blo 471786 708923 := bstep (se 1 (by rfl) ⟨531692, by rfl⟩ : syracuseStep 708923 = 1063385) B1063385
theorem B708983 : Blo 471786 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B709007 : Blo 471786 709007 := bstep (se 1 (by rfl) ⟨531755, by rfl⟩ : syracuseStep 709007 = 1063511) B1063511
theorem B512399 : Blo 471786 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B709049 : Blo 471786 709049 := bstep (se 2 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 709049 = 531787) B531787
theorem B709127 : Blo 471786 709127 := bstep (se 1 (by rfl) ⟨531845, by rfl⟩ : syracuseStep 709127 = 1063691) B1063691
theorem B709163 : Blo 471786 709163 := bstep (se 1 (by rfl) ⟨531872, by rfl⟩ : syracuseStep 709163 = 1063745) B1063745
theorem B1200683 : Blo 471786 1200683 := bstep (se 1 (by rfl) ⟨900512, by rfl⟩ : syracuseStep 1200683 = 1801025) B1801025
theorem B1593917 : Blo 471786 1593917 := bstep (se 3 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 1593917 = 597719) B597719
theorem B709193 : Blo 471786 709193 := bstep (se 2 (by rfl) ⟨265947, by rfl⟩ : syracuseStep 709193 = 531895) B531895
theorem B1069703 : Blo 471786 1069703 := bstep (se 1 (by rfl) ⟨802277, by rfl⟩ : syracuseStep 1069703 = 1604555) B1604555
theorem B709307 : Blo 471786 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B709367 : Blo 471786 709367 := bstep (se 1 (by rfl) ⟨532025, by rfl⟩ : syracuseStep 709367 = 1064051) B1064051
theorem B676615 : Blo 471786 676615 := bstep (se 1 (by rfl) ⟨507461, by rfl⟩ : syracuseStep 676615 = 1014923) B1014923
theorem B709391 : Blo 471786 709391 := bstep (se 1 (by rfl) ⟨532043, by rfl⟩ : syracuseStep 709391 = 1064087) B1064087
theorem B3592997 : Blo 471786 3592997 := bstep (se 4 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 3592997 = 673687) B673687
theorem B709433 : Blo 471786 709433 := bstep (se 2 (by rfl) ⟨266037, by rfl⟩ : syracuseStep 709433 = 532075) B532075
theorem B1069883 : Blo 471786 1069883 := bstep (se 1 (by rfl) ⟨802412, by rfl⟩ : syracuseStep 1069883 = 1604825) B1604825
theorem B2872199 : Blo 471786 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B709511 : Blo 471786 709511 := bstep (se 1 (by rfl) ⟨532133, by rfl⟩ : syracuseStep 709511 = 1064267) B1064267
theorem B709547 : Blo 471786 709547 := bstep (se 1 (by rfl) ⟨532160, by rfl⟩ : syracuseStep 709547 = 1064321) B1064321
theorem B1070009 : Blo 471786 1070009 := bstep (se 2 (by rfl) ⟨401253, by rfl⟩ : syracuseStep 1070009 = 802507) B802507
theorem B709577 : Blo 471786 709577 := bstep (se 2 (by rfl) ⟨266091, by rfl⟩ : syracuseStep 709577 = 532183) B532183
theorem B709691 : Blo 471786 709691 := bstep (se 1 (by rfl) ⟨532268, by rfl⟩ : syracuseStep 709691 = 1064537) B1064537
theorem B709751 : Blo 471786 709751 := bstep (se 1 (by rfl) ⟨532313, by rfl⟩ : syracuseStep 709751 = 1064627) B1064627
theorem B2708599 : Blo 471786 2708599 := bstep (se 1 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 2708599 = 4062899) B4062899
theorem B709775 : Blo 471786 709775 := bstep (se 1 (by rfl) ⟨532331, by rfl⟩ : syracuseStep 709775 = 1064663) B1064663
theorem B709817 : Blo 471786 709817 := bstep (se 2 (by rfl) ⟨266181, by rfl⟩ : syracuseStep 709817 = 532363) B532363
theorem B709895 : Blo 471786 709895 := bstep (se 1 (by rfl) ⟨532421, by rfl⟩ : syracuseStep 709895 = 1064843) B1064843
theorem B1070351 : Blo 471786 1070351 := bstep (se 1 (by rfl) ⟨802763, by rfl⟩ : syracuseStep 1070351 = 1605527) B1605527
theorem B1070369 : Blo 471786 1070369 := bstep (se 2 (by rfl) ⟨401388, by rfl⟩ : syracuseStep 1070369 = 802777) B802777
theorem B709931 : Blo 471786 709931 := bstep (se 1 (by rfl) ⟨532448, by rfl⟩ : syracuseStep 709931 = 1064897) B1064897
theorem B709961 : Blo 471786 709961 := bstep (se 2 (by rfl) ⟨266235, by rfl⟩ : syracuseStep 709961 = 532471) B532471
theorem B23287175 : Blo 471786 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B710075 : Blo 471786 710075 := bstep (se 1 (by rfl) ⟨532556, by rfl⟩ : syracuseStep 710075 = 1065113) B1065113
theorem B710135 : Blo 471786 710135 := bstep (se 1 (by rfl) ⟨532601, by rfl⟩ : syracuseStep 710135 = 1065203) B1065203
theorem B1201675 : Blo 471786 1201675 := bstep (se 1 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 1201675 = 1802513) B1802513
theorem B710159 : Blo 471786 710159 := bstep (se 1 (by rfl) ⟨532619, by rfl⟩ : syracuseStep 710159 = 1065239) B1065239
theorem B1791517 : Blo 471786 1791517 := bstep (se 3 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 1791517 = 671819) B671819
theorem B710201 : Blo 471786 710201 := bstep (se 2 (by rfl) ⟨266325, by rfl⟩ : syracuseStep 710201 = 532651) B532651
theorem B2020925 : Blo 471786 2020925 := bstep (se 3 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 2020925 = 757847) B757847
theorem B710279 : Blo 471786 710279 := bstep (se 1 (by rfl) ⟨532709, by rfl⟩ : syracuseStep 710279 = 1065419) B1065419
theorem B1201817 : Blo 471786 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B710315 : Blo 471786 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B710345 : Blo 471786 710345 := bstep (se 2 (by rfl) ⟨266379, by rfl⟩ : syracuseStep 710345 = 532759) B532759
theorem B710459 : Blo 471786 710459 := bstep (se 1 (by rfl) ⟨532844, by rfl⟩ : syracuseStep 710459 = 1065689) B1065689
theorem B1201979 : Blo 471786 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B710519 : Blo 471786 710519 := bstep (se 1 (by rfl) ⟨532889, by rfl⟩ : syracuseStep 710519 = 1065779) B1065779
theorem B710543 : Blo 471786 710543 := bstep (se 1 (by rfl) ⟨532907, by rfl⟩ : syracuseStep 710543 = 1065815) B1065815
theorem B2021267 : Blo 471786 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B972691 : Blo 471786 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B1595321 : Blo 471786 1595321 := bstep (se 2 (by rfl) ⟨598245, by rfl⟩ : syracuseStep 1595321 = 1196491) B1196491
theorem B710585 : Blo 471786 710585 := bstep (se 2 (by rfl) ⟨266469, by rfl⟩ : syracuseStep 710585 = 532939) B532939
theorem B710663 : Blo 471786 710663 := bstep (se 1 (by rfl) ⟨532997, by rfl⟩ : syracuseStep 710663 = 1065995) B1065995
theorem B710699 : Blo 471786 710699 := bstep (se 1 (by rfl) ⟨533024, by rfl⟩ : syracuseStep 710699 = 1066049) B1066049
theorem B710729 : Blo 471786 710729 := bstep (se 2 (by rfl) ⟨266523, by rfl⟩ : syracuseStep 710729 = 533047) B533047
theorem B1202323 : Blo 471786 1202323 := bstep (se 1 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 1202323 = 1803485) B1803485
theorem B710843 : Blo 471786 710843 := bstep (se 1 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 710843 = 1066265) B1066265
theorem B710903 : Blo 471786 710903 := bstep (se 1 (by rfl) ⟨533177, by rfl⟩ : syracuseStep 710903 = 1066355) B1066355
theorem B710927 : Blo 471786 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B1202465 : Blo 471786 1202465 := bstep (se 2 (by rfl) ⟨450924, by rfl⟩ : syracuseStep 1202465 = 901849) B901849
theorem B710969 : Blo 471786 710969 := bstep (se 2 (by rfl) ⟨266613, by rfl⟩ : syracuseStep 710969 = 533227) B533227
theorem B711047 : Blo 471786 711047 := bstep (se 1 (by rfl) ⟨533285, by rfl⟩ : syracuseStep 711047 = 1066571) B1066571
theorem B711083 : Blo 471786 711083 := bstep (se 1 (by rfl) ⟨533312, by rfl⟩ : syracuseStep 711083 = 1066625) B1066625
theorem B711113 : Blo 471786 711113 := bstep (se 2 (by rfl) ⟨266667, by rfl⟩ : syracuseStep 711113 = 533335) B533335
theorem B1595915 : Blo 471786 1595915 := bstep (se 1 (by rfl) ⟨1196936, by rfl⟩ : syracuseStep 1595915 = 2393873) B2393873
theorem B711227 : Blo 471786 711227 := bstep (se 1 (by rfl) ⟨533420, by rfl⟩ : syracuseStep 711227 = 1066841) B1066841
theorem B3758669 : Blo 471786 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1596023 : Blo 471786 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B711287 : Blo 471786 711287 := bstep (se 1 (by rfl) ⟨533465, by rfl⟩ : syracuseStep 711287 = 1066931) B1066931
theorem B711311 : Blo 471786 711311 := bstep (se 1 (by rfl) ⟨533483, by rfl⟩ : syracuseStep 711311 = 1066967) B1066967
theorem B711353 : Blo 471786 711353 := bstep (se 2 (by rfl) ⟨266757, by rfl⟩ : syracuseStep 711353 = 533515) B533515
theorem B3037925 : Blo 471786 3037925 := bstep (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) B569611
theorem B711431 : Blo 471786 711431 := bstep (se 1 (by rfl) ⟨533573, by rfl⟩ : syracuseStep 711431 = 1067147) B1067147
theorem B711467 : Blo 471786 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B711497 : Blo 471786 711497 := bstep (se 2 (by rfl) ⟨266811, by rfl⟩ : syracuseStep 711497 = 533623) B533623
theorem B908167 : Blo 471786 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B711611 : Blo 471786 711611 := bstep (se 1 (by rfl) ⟨533708, by rfl⟩ : syracuseStep 711611 = 1067417) B1067417
theorem B711671 : Blo 471786 711671 := bstep (se 1 (by rfl) ⟨533753, by rfl⟩ : syracuseStep 711671 = 1067507) B1067507
theorem B5397515 : Blo 471786 5397515 := bstep (se 1 (by rfl) ⟨4048136, by rfl⟩ : syracuseStep 5397515 = 8096273) B8096273
theorem B711695 : Blo 471786 711695 := bstep (se 1 (by rfl) ⟨533771, by rfl⟩ : syracuseStep 711695 = 1067543) B1067543
theorem B1924139 : Blo 471786 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B711737 : Blo 471786 711737 := bstep (se 2 (by rfl) ⟨266901, by rfl⟩ : syracuseStep 711737 = 533803) B533803
theorem B711815 : Blo 471786 711815 := bstep (se 1 (by rfl) ⟨533861, by rfl⟩ : syracuseStep 711815 = 1067723) B1067723
theorem B711851 : Blo 471786 711851 := bstep (se 1 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 711851 = 1067777) B1067777
theorem B711881 : Blo 471786 711881 := bstep (se 2 (by rfl) ⟨266955, by rfl⟩ : syracuseStep 711881 = 533911) B533911
theorem B1596617 : Blo 471786 1596617 := bstep (se 2 (by rfl) ⟨598731, by rfl⟩ : syracuseStep 1596617 = 1197463) B1197463
theorem B1203457 : Blo 471786 1203457 := bstep (se 2 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 1203457 = 902593) B902593
theorem B711995 : Blo 471786 711995 := bstep (se 1 (by rfl) ⟨533996, by rfl⟩ : syracuseStep 711995 = 1067993) B1067993
theorem B712055 : Blo 471786 712055 := bstep (se 1 (by rfl) ⟨534041, by rfl⟩ : syracuseStep 712055 = 1068083) B1068083
theorem B4873607 : Blo 471786 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B712079 : Blo 471786 712079 := bstep (se 1 (by rfl) ⟨534059, by rfl⟩ : syracuseStep 712079 = 1068119) B1068119
theorem B712121 : Blo 471786 712121 := bstep (se 2 (by rfl) ⟨267045, by rfl⟩ : syracuseStep 712121 = 534091) B534091
theorem B712199 : Blo 471786 712199 := bstep (se 1 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 712199 = 1068299) B1068299
theorem B712235 : Blo 471786 712235 := bstep (se 1 (by rfl) ⟨534176, by rfl⟩ : syracuseStep 712235 = 1068353) B1068353
theorem B712265 : Blo 471786 712265 := bstep (se 2 (by rfl) ⟨267099, by rfl⟩ : syracuseStep 712265 = 534199) B534199
theorem B712379 : Blo 471786 712379 := bstep (se 1 (by rfl) ⟨534284, by rfl⟩ : syracuseStep 712379 = 1068569) B1068569
theorem B712439 : Blo 471786 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B712463 : Blo 471786 712463 := bstep (se 1 (by rfl) ⟨534347, by rfl⟩ : syracuseStep 712463 = 1068695) B1068695
theorem B712505 : Blo 471786 712505 := bstep (se 2 (by rfl) ⟨267189, by rfl⟩ : syracuseStep 712505 = 534379) B534379
theorem B1204055 : Blo 471786 1204055 := bstep (se 1 (by rfl) ⟨903041, by rfl⟩ : syracuseStep 1204055 = 1806083) B1806083
theorem B1597319 : Blo 471786 1597319 := bstep (se 1 (by rfl) ⟨1197989, by rfl⟩ : syracuseStep 1597319 = 2395979) B2395979
theorem B712583 : Blo 471786 712583 := bstep (se 1 (by rfl) ⟨534437, by rfl⟩ : syracuseStep 712583 = 1068875) B1068875
theorem B12443543 : Blo 471786 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B712619 : Blo 471786 712619 := bstep (se 1 (by rfl) ⟨534464, by rfl⟩ : syracuseStep 712619 = 1068929) B1068929
theorem B712649 : Blo 471786 712649 := bstep (se 2 (by rfl) ⟨267243, by rfl⟩ : syracuseStep 712649 = 534487) B534487
theorem B1204267 : Blo 471786 1204267 := bstep (se 1 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 1204267 = 1806401) B1806401
theorem B712763 : Blo 471786 712763 := bstep (se 1 (by rfl) ⟨534572, by rfl⟩ : syracuseStep 712763 = 1069145) B1069145
theorem B2187383 : Blo 471786 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B712823 : Blo 471786 712823 := bstep (se 1 (by rfl) ⟨534617, by rfl⟩ : syracuseStep 712823 = 1069235) B1069235
theorem B712847 : Blo 471786 712847 := bstep (se 1 (by rfl) ⟨534635, by rfl⟩ : syracuseStep 712847 = 1069271) B1069271
theorem B712889 : Blo 471786 712889 := bstep (se 2 (by rfl) ⟨267333, by rfl⟩ : syracuseStep 712889 = 534667) B534667
theorem B1597697 : Blo 471786 1597697 := bstep (se 2 (by rfl) ⟨599136, by rfl⟩ : syracuseStep 1597697 = 1198273) B1198273
theorem B712967 : Blo 471786 712967 := bstep (se 1 (by rfl) ⟨534725, by rfl⟩ : syracuseStep 712967 = 1069451) B1069451
theorem B713003 : Blo 471786 713003 := bstep (se 1 (by rfl) ⟨534752, by rfl⟩ : syracuseStep 713003 = 1069505) B1069505
theorem B713033 : Blo 471786 713033 := bstep (se 2 (by rfl) ⟨267387, by rfl⟩ : syracuseStep 713033 = 534775) B534775
theorem B1794419 : Blo 471786 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B2023795 : Blo 471786 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B2023865 : Blo 471786 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B713147 : Blo 471786 713147 := bstep (se 1 (by rfl) ⟨534860, by rfl⟩ : syracuseStep 713147 = 1069721) B1069721
theorem B713207 : Blo 471786 713207 := bstep (se 1 (by rfl) ⟨534905, by rfl⟩ : syracuseStep 713207 = 1069811) B1069811
theorem B713231 : Blo 471786 713231 := bstep (se 1 (by rfl) ⟨534923, by rfl⟩ : syracuseStep 713231 = 1069847) B1069847
theorem B713273 : Blo 471786 713273 := bstep (se 2 (by rfl) ⟨267477, by rfl⟩ : syracuseStep 713273 = 534955) B534955
theorem B713351 : Blo 471786 713351 := bstep (se 1 (by rfl) ⟨535013, by rfl⟩ : syracuseStep 713351 = 1070027) B1070027
theorem B713387 : Blo 471786 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B713417 : Blo 471786 713417 := bstep (se 2 (by rfl) ⟨267531, by rfl⟩ : syracuseStep 713417 = 535063) B535063
theorem B3040051 : Blo 471786 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B713531 : Blo 471786 713531 := bstep (se 1 (by rfl) ⟨535148, by rfl⟩ : syracuseStep 713531 = 1070297) B1070297
theorem B713591 : Blo 471786 713591 := bstep (se 1 (by rfl) ⟨535193, by rfl⟩ : syracuseStep 713591 = 1070387) B1070387
theorem B713615 : Blo 471786 713615 := bstep (se 1 (by rfl) ⟨535211, by rfl⟩ : syracuseStep 713615 = 1070423) B1070423
theorem B713657 : Blo 471786 713657 := bstep (se 2 (by rfl) ⟨267621, by rfl⟩ : syracuseStep 713657 = 535243) B535243
theorem B1598507 : Blo 471786 1598507 := bstep (se 1 (by rfl) ⟨1198880, by rfl⟩ : syracuseStep 1598507 = 2397761) B2397761
theorem B812843 : Blo 471786 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B9135989 : Blo 471786 9135989 := bstep (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) B856499
theorem B649145 : Blo 471786 649145 := bstep (se 2 (by rfl) ⟨243429, by rfl⟩ : syracuseStep 649145 = 486859) B486859
theorem B1599803 : Blo 471786 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B2189683 : Blo 471786 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B2025881 : Blo 471786 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B1796651 : Blo 471786 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B911915 : Blo 471786 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B1141307 : Blo 471786 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B1436221 : Blo 471786 1436221 := bstep (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) B538583
theorem B2026241 : Blo 471786 2026241 := bstep (se 2 (by rfl) ⟨759840, by rfl⟩ : syracuseStep 2026241 = 1519681) B1519681
theorem B3042049 : Blo 471786 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B1600289 : Blo 471786 1600289 := bstep (se 2 (by rfl) ⟨600108, by rfl⟩ : syracuseStep 1600289 = 1200217) B1200217
theorem B14740373 : Blo 471786 14740373 := bstep (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) B690955
theorem B1010873 : Blo 471786 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B5401889 : Blo 471786 5401889 := bstep (se 2 (by rfl) ⟨2025708, by rfl⟩ : syracuseStep 5401889 = 4051417) B4051417
theorem B1600883 : Blo 471786 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B3599801 : Blo 471786 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B1928747 : Blo 471786 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B58453589 : Blo 471786 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B618283 : Blo 471786 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B1011727 : Blo 471786 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B1011847 : Blo 471786 1011847 := bstep (se 1 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 1011847 = 1517771) B1517771
theorem B1012027 : Blo 471786 1012027 := bstep (se 1 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 1012027 = 1518041) B1518041
theorem B1012103 : Blo 471786 1012103 := bstep (se 1 (by rfl) ⟨759077, by rfl⟩ : syracuseStep 1012103 = 1518155) B1518155
theorem B1012513 : Blo 471786 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B2388851 : Blo 471786 2388851 := bstep (se 1 (by rfl) ⟨1791638, by rfl⟩ : syracuseStep 2388851 = 3583277) B3583277
theorem B1537339 : Blo 471786 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B2389337 : Blo 471786 2389337 := bstep (se 2 (by rfl) ⟨896001, by rfl⟩ : syracuseStep 2389337 = 1792003) B1792003
theorem B4879763 : Blo 471786 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B1439603 : Blo 471786 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1800083 : Blo 471786 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B1603475 : Blo 471786 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B13694993 : Blo 471786 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B5404805 : Blo 471786 5404805 := bstep (se 4 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 5404805 = 1013401) B1013401
theorem B94959985 : Blo 471786 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B1276445 : Blo 471786 1276445 := bstep (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) B478667
theorem B1014419 : Blo 471786 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B1604879 : Blo 471786 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B2391443 : Blo 471786 2391443 := bstep (se 1 (by rfl) ⟨1793582, by rfl⟩ : syracuseStep 2391443 = 3587165) B3587165
theorem B1605149 : Blo 471786 1605149 := bstep (se 3 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 1605149 = 601931) B601931
theorem B1277527 : Blo 471786 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B9698915 : Blo 471786 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B1605689 : Blo 471786 1605689 := bstep (se 2 (by rfl) ⟨602133, by rfl⟩ : syracuseStep 1605689 = 1204267) B1204267
theorem B5833021 : Blo 471786 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B52724195 : Blo 471786 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B6128245 : Blo 471786 6128245 := bstep (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) B574523
theorem B1213127 : Blo 471786 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B14419603 : Blo 471786 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B2197343 : Blo 471786 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B1804139 : Blo 471786 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B9865223 : Blo 471786 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B3606605 : Blo 471786 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B14780819 : Blo 471786 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B756233 : Blo 471786 756233 := bstep (se 2 (by rfl) ⟨283587, by rfl⟩ : syracuseStep 756233 = 567175) B567175
theorem B3475993 : Blo 471786 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2394683 : Blo 471786 2394683 := bstep (se 1 (by rfl) ⟨1796012, by rfl⟩ : syracuseStep 2394683 = 3592025) B3592025
theorem B1543225 : Blo 471786 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B5377103 : Blo 471786 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B2919577 : Blo 471786 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B2395331 : Blo 471786 2395331 := bstep (se 1 (by rfl) ⟨1796498, by rfl⟩ : syracuseStep 2395331 = 3592997) B3592997
theorem B1347283 : Blo 471786 1347283 := bstep (se 1 (by rfl) ⟨1010462, by rfl⟩ : syracuseStep 1347283 = 2020925) B2020925
theorem B1347511 : Blo 471786 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2560157 : Blo 471786 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B11538611 : Blo 471786 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B3609035 : Blo 471786 3609035 := bstep (se 1 (by rfl) ⟨2706776, by rfl⟩ : syracuseStep 3609035 = 5413553) B5413553
theorem B2888327 : Blo 471786 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B1282759 : Blo 471786 1282759 := bstep (se 1 (by rfl) ⟨962069, by rfl⟩ : syracuseStep 1282759 = 1924139) B1924139
theorem B3248849 : Blo 471786 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B3249071 : Blo 471786 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B2626561 : Blo 471786 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B8295695 : Blo 471786 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B1348969 : Blo 471786 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B1349129 : Blo 471786 1349129 := bstep (se 2 (by rfl) ⟨505923, by rfl⟩ : syracuseStep 1349129 = 1011847) B1011847
theorem B1349243 : Blo 471786 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B1349369 : Blo 471786 1349369 := bstep (se 2 (by rfl) ⟨506013, by rfl⟩ : syracuseStep 1349369 = 1012027) B1012027
theorem B1350017 : Blo 471786 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B531067 : Blo 471786 531067 := bstep (se 1 (by rfl) ⟨398300, by rfl⟩ : syracuseStep 531067 = 796601) B796601
theorem B3611465 : Blo 471786 3611465 := bstep (se 2 (by rfl) ⟨1354299, by rfl⟩ : syracuseStep 3611465 = 2708599) B2708599
theorem B1350587 : Blo 471786 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B760871 : Blo 471786 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B531535 : Blo 471786 531535 := bstep (se 1 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 531535 = 797303) B797303
theorem B1350827 : Blo 471786 1350827 := bstep (se 1 (by rfl) ⟨1013120, by rfl⟩ : syracuseStep 1350827 = 2026241) B2026241
theorem B1973443 : Blo 471786 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B2891173 : Blo 471786 2891173 := bstep (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) B542095
theorem B531931 : Blo 471786 531931 := bstep (se 1 (by rfl) ⟨398948, by rfl⟩ : syracuseStep 531931 = 797897) B797897
theorem B1515131 : Blo 471786 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B2399867 : Blo 471786 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B1285831 : Blo 471786 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B38969059 : Blo 471786 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B3252001 : Blo 471786 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B532399 : Blo 471786 532399 := bstep (se 1 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 532399 = 798599) B798599
theorem B598367 : Blo 471786 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B532831 : Blo 471786 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B2564743 : Blo 471786 2564743 := bstep (se 1 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 2564743 = 3847115) B3847115
theorem B533191 : Blo 471786 533191 := bstep (se 1 (by rfl) ⟨399893, by rfl⟩ : syracuseStep 533191 = 799787) B799787
theorem B3253175 : Blo 471786 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B9250037 : Blo 471786 9250037 := bstep (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) B867191
theorem B959735 : Blo 471786 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B796169 : Blo 471786 796169 := bstep (se 2 (by rfl) ⟨298563, by rfl⟩ : syracuseStep 796169 = 597127) B597127
theorem B534055 : Blo 471786 534055 := bstep (se 1 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 534055 = 801083) B801083
theorem B796331 : Blo 471786 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B13510489 : Blo 471786 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B3024827 : Blo 471786 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B796729 : Blo 471786 796729 := bstep (se 2 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 796729 = 597547) B597547
theorem B5187685 : Blo 471786 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B796871 : Blo 471786 796871 := bstep (se 1 (by rfl) ⟨597653, by rfl⟩ : syracuseStep 796871 = 1195307) B1195307
theorem B2402621 : Blo 471786 2402621 := bstep (se 3 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 2402621 = 900983) B900983
theorem B797033 : Blo 471786 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B6465943 : Blo 471786 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B3025441 : Blo 471786 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B26978849 : Blo 471786 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B797431 : Blo 471786 797431 := bstep (se 1 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 797431 = 1196147) B1196147
theorem B601015 : Blo 471786 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B797627 : Blo 471786 797627 := bstep (se 1 (by rfl) ⟨598220, by rfl⟩ : syracuseStep 797627 = 1196441) B1196441
theorem B797735 : Blo 471786 797735 := bstep (se 1 (by rfl) ⟨598301, by rfl⟩ : syracuseStep 797735 = 1196603) B1196603
theorem B896123 : Blo 471786 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B2698393 : Blo 471786 2698393 := bstep (se 2 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 2698393 = 2023795) B2023795
theorem B798025 : Blo 471786 798025 := bstep (se 2 (by rfl) ⟨299259, by rfl⟩ : syracuseStep 798025 = 598519) B598519
theorem B798059 : Blo 471786 798059 := bstep (se 1 (by rfl) ⟨598544, by rfl⟩ : syracuseStep 798059 = 1197089) B1197089
theorem B3026443 : Blo 471786 3026443 := bstep (se 1 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 3026443 = 4539665) B4539665
theorem B896609 : Blo 471786 896609 := bstep (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) B672457
theorem B5385851 : Blo 471786 5385851 := bstep (se 1 (by rfl) ⟨4039388, by rfl⟩ : syracuseStep 5385851 = 8078777) B8078777
theorem B2272967 : Blo 471786 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B896761 : Blo 471786 896761 := bstep (se 2 (by rfl) ⟨336285, by rfl⟩ : syracuseStep 896761 = 672571) B672571
theorem B798457 : Blo 471786 798457 := bstep (se 2 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 798457 = 598843) B598843
theorem B4599737 : Blo 471786 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B798727 : Blo 471786 798727 := bstep (se 1 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 798727 = 1198091) B1198091
theorem B3027287 : Blo 471786 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B799159 : Blo 471786 799159 := bstep (se 1 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 799159 = 1198739) B1198739
theorem B2404889 : Blo 471786 2404889 := bstep (se 2 (by rfl) ⟨901833, by rfl⟩ : syracuseStep 2404889 = 1803667) B1803667
theorem B799355 : Blo 471786 799355 := bstep (se 1 (by rfl) ⟨599516, by rfl⟩ : syracuseStep 799355 = 1199033) B1199033
theorem B471847 : Blo 471786 471847 := bstep (se 1 (by rfl) ⟨353885, by rfl⟩ : syracuseStep 471847 = 707771) B707771
theorem B471887 : Blo 471786 471887 := bstep (se 1 (by rfl) ⟨353915, by rfl⟩ : syracuseStep 471887 = 707831) B707831
theorem B471903 : Blo 471786 471903 := bstep (se 1 (by rfl) ⟨353927, by rfl⟩ : syracuseStep 471903 = 707855) B707855
theorem B4043627 : Blo 471786 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B471931 : Blo 471786 471931 := bstep (se 1 (by rfl) ⟨353948, by rfl⟩ : syracuseStep 471931 = 707897) B707897
theorem B471983 : Blo 471786 471983 := bstep (se 1 (by rfl) ⟨353987, by rfl⟩ : syracuseStep 471983 = 707975) B707975
theorem B1061819 : Blo 471786 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B472007 : Blo 471786 472007 := bstep (se 1 (by rfl) ⟨354005, by rfl⟩ : syracuseStep 472007 = 708011) B708011
theorem B472027 : Blo 471786 472027 := bstep (se 1 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 472027 = 708041) B708041
theorem B799753 : Blo 471786 799753 := bstep (se 2 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 799753 = 599815) B599815
theorem B898067 : Blo 471786 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B472103 : Blo 471786 472103 := bstep (se 1 (by rfl) ⟨354077, by rfl⟩ : syracuseStep 472103 = 708155) B708155
theorem B1061945 : Blo 471786 1061945 := bstep (se 2 (by rfl) ⟨398229, by rfl⟩ : syracuseStep 1061945 = 796459) B796459
theorem B472143 : Blo 471786 472143 := bstep (se 1 (by rfl) ⟨354107, by rfl⟩ : syracuseStep 472143 = 708215) B708215
theorem B472159 : Blo 471786 472159 := bstep (se 1 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 472159 = 708239) B708239
theorem B472187 : Blo 471786 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B898219 : Blo 471786 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B799915 : Blo 471786 799915 := bstep (se 1 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 799915 = 1199873) B1199873
theorem B472239 : Blo 471786 472239 := bstep (se 1 (by rfl) ⟨354179, by rfl⟩ : syracuseStep 472239 = 708359) B708359
theorem B472263 : Blo 471786 472263 := bstep (se 1 (by rfl) ⟨354197, by rfl⟩ : syracuseStep 472263 = 708395) B708395
theorem B472283 : Blo 471786 472283 := bstep (se 1 (by rfl) ⟨354212, by rfl⟩ : syracuseStep 472283 = 708425) B708425
theorem B472359 : Blo 471786 472359 := bstep (se 1 (by rfl) ⟨354269, by rfl⟩ : syracuseStep 472359 = 708539) B708539
theorem B472399 : Blo 471786 472399 := bstep (se 1 (by rfl) ⟨354299, by rfl⟩ : syracuseStep 472399 = 708599) B708599
theorem B472415 : Blo 471786 472415 := bstep (se 1 (by rfl) ⟨354311, by rfl⟩ : syracuseStep 472415 = 708623) B708623
theorem B472443 : Blo 471786 472443 := bstep (se 1 (by rfl) ⟨354332, by rfl⟩ : syracuseStep 472443 = 708665) B708665
theorem B1062287 : Blo 471786 1062287 := bstep (se 1 (by rfl) ⟨796715, by rfl⟩ : syracuseStep 1062287 = 1593431) B1593431
theorem B898447 : Blo 471786 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B472495 : Blo 471786 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B472519 : Blo 471786 472519 := bstep (se 1 (by rfl) ⟨354389, by rfl⟩ : syracuseStep 472519 = 708779) B708779
theorem B472539 : Blo 471786 472539 := bstep (se 1 (by rfl) ⟨354404, by rfl⟩ : syracuseStep 472539 = 708809) B708809
theorem B898523 : Blo 471786 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B800219 : Blo 471786 800219 := bstep (se 1 (by rfl) ⟨600164, by rfl⟩ : syracuseStep 800219 = 1200329) B1200329
theorem B472615 : Blo 471786 472615 := bstep (se 1 (by rfl) ⟨354461, by rfl⟩ : syracuseStep 472615 = 708923) B708923
theorem B472655 : Blo 471786 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B472671 : Blo 471786 472671 := bstep (se 1 (by rfl) ⟨354503, by rfl⟩ : syracuseStep 472671 = 709007) B709007
theorem B472699 : Blo 471786 472699 := bstep (se 1 (by rfl) ⟨354524, by rfl⟩ : syracuseStep 472699 = 709049) B709049
theorem B472751 : Blo 471786 472751 := bstep (se 1 (by rfl) ⟨354563, by rfl⟩ : syracuseStep 472751 = 709127) B709127
theorem B472775 : Blo 471786 472775 := bstep (se 1 (by rfl) ⟨354581, by rfl⟩ : syracuseStep 472775 = 709163) B709163
theorem B800455 : Blo 471786 800455 := bstep (se 1 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 800455 = 1200683) B1200683
theorem B1062611 : Blo 471786 1062611 := bstep (se 1 (by rfl) ⟨796958, by rfl⟩ : syracuseStep 1062611 = 1593917) B1593917
theorem B472795 : Blo 471786 472795 := bstep (se 1 (by rfl) ⟨354596, by rfl⟩ : syracuseStep 472795 = 709193) B709193
theorem B472871 : Blo 471786 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B472911 : Blo 471786 472911 := bstep (se 1 (by rfl) ⟨354683, by rfl⟩ : syracuseStep 472911 = 709367) B709367
theorem B472927 : Blo 471786 472927 := bstep (se 1 (by rfl) ⟨354695, by rfl⟩ : syracuseStep 472927 = 709391) B709391
theorem B800617 : Blo 471786 800617 := bstep (se 2 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 800617 = 600463) B600463
theorem B4044653 : Blo 471786 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B472955 : Blo 471786 472955 := bstep (se 1 (by rfl) ⟨354716, by rfl⟩ : syracuseStep 472955 = 709433) B709433
theorem B1914799 : Blo 471786 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B473007 : Blo 471786 473007 := bstep (se 1 (by rfl) ⟨354755, by rfl⟩ : syracuseStep 473007 = 709511) B709511
theorem B473031 : Blo 471786 473031 := bstep (se 1 (by rfl) ⟨354773, by rfl⟩ : syracuseStep 473031 = 709547) B709547
theorem B473051 : Blo 471786 473051 := bstep (se 1 (by rfl) ⟨354788, by rfl⟩ : syracuseStep 473051 = 709577) B709577
theorem B473127 : Blo 471786 473127 := bstep (se 1 (by rfl) ⟨354845, by rfl⟩ : syracuseStep 473127 = 709691) B709691
theorem B473167 : Blo 471786 473167 := bstep (se 1 (by rfl) ⟨354875, by rfl⟩ : syracuseStep 473167 = 709751) B709751
theorem B473183 : Blo 471786 473183 := bstep (se 1 (by rfl) ⟨354887, by rfl⟩ : syracuseStep 473183 = 709775) B709775
theorem B473211 : Blo 471786 473211 := bstep (se 1 (by rfl) ⟨354908, by rfl⟩ : syracuseStep 473211 = 709817) B709817
theorem B473263 : Blo 471786 473263 := bstep (se 1 (by rfl) ⟨354947, by rfl⟩ : syracuseStep 473263 = 709895) B709895
theorem B473287 : Blo 471786 473287 := bstep (se 1 (by rfl) ⟨354965, by rfl⟩ : syracuseStep 473287 = 709931) B709931
theorem B473307 : Blo 471786 473307 := bstep (se 1 (by rfl) ⟨354980, by rfl⟩ : syracuseStep 473307 = 709961) B709961
theorem B473383 : Blo 471786 473383 := bstep (se 1 (by rfl) ⟨355037, by rfl⟩ : syracuseStep 473383 = 710075) B710075
theorem B473423 : Blo 471786 473423 := bstep (se 1 (by rfl) ⟨355067, by rfl⟩ : syracuseStep 473423 = 710135) B710135
theorem B473439 : Blo 471786 473439 := bstep (se 1 (by rfl) ⟨355079, by rfl⟩ : syracuseStep 473439 = 710159) B710159
theorem B473467 : Blo 471786 473467 := bstep (se 1 (by rfl) ⟨355100, by rfl⟩ : syracuseStep 473467 = 710201) B710201
theorem B473519 : Blo 471786 473519 := bstep (se 1 (by rfl) ⟨355139, by rfl⟩ : syracuseStep 473519 = 710279) B710279
theorem B506287 : Blo 471786 506287 := bstep (se 1 (by rfl) ⟨379715, by rfl⟩ : syracuseStep 506287 = 759431) B759431
theorem B801211 : Blo 471786 801211 := bstep (se 1 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 801211 = 1201817) B1201817
theorem B473543 : Blo 471786 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B473563 : Blo 471786 473563 := bstep (se 1 (by rfl) ⟨355172, by rfl⟩ : syracuseStep 473563 = 710345) B710345
theorem B473639 : Blo 471786 473639 := bstep (se 1 (by rfl) ⟨355229, by rfl⟩ : syracuseStep 473639 = 710459) B710459
theorem B801319 : Blo 471786 801319 := bstep (se 1 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 801319 = 1201979) B1201979
theorem B473679 : Blo 471786 473679 := bstep (se 1 (by rfl) ⟨355259, by rfl⟩ : syracuseStep 473679 = 710519) B710519
theorem B473695 : Blo 471786 473695 := bstep (se 1 (by rfl) ⟨355271, by rfl⟩ : syracuseStep 473695 = 710543) B710543
theorem B1063547 : Blo 471786 1063547 := bstep (se 1 (by rfl) ⟨797660, by rfl⟩ : syracuseStep 1063547 = 1595321) B1595321
theorem B473723 : Blo 471786 473723 := bstep (se 1 (by rfl) ⟨355292, by rfl⟩ : syracuseStep 473723 = 710585) B710585
theorem B473775 : Blo 471786 473775 := bstep (se 1 (by rfl) ⟨355331, by rfl⟩ : syracuseStep 473775 = 710663) B710663
theorem B473799 : Blo 471786 473799 := bstep (se 1 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 473799 = 710699) B710699
theorem B473819 : Blo 471786 473819 := bstep (se 1 (by rfl) ⟨355364, by rfl⟩ : syracuseStep 473819 = 710729) B710729
theorem B1063673 : Blo 471786 1063673 := bstep (se 2 (by rfl) ⟨398877, by rfl⟩ : syracuseStep 1063673 = 797755) B797755
theorem B473895 : Blo 471786 473895 := bstep (se 1 (by rfl) ⟨355421, by rfl⟩ : syracuseStep 473895 = 710843) B710843
theorem B473935 : Blo 471786 473935 := bstep (se 1 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 473935 = 710903) B710903
theorem B473951 : Blo 471786 473951 := bstep (se 1 (by rfl) ⟨355463, by rfl⟩ : syracuseStep 473951 = 710927) B710927
theorem B637801 : Blo 471786 637801 := bstep (se 2 (by rfl) ⟨239175, by rfl⟩ : syracuseStep 637801 = 478351) B478351
theorem B801643 : Blo 471786 801643 := bstep (se 1 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 801643 = 1202465) B1202465
theorem B473979 : Blo 471786 473979 := bstep (se 1 (by rfl) ⟨355484, by rfl⟩ : syracuseStep 473979 = 710969) B710969
theorem B474031 : Blo 471786 474031 := bstep (se 1 (by rfl) ⟨355523, by rfl⟩ : syracuseStep 474031 = 711047) B711047
theorem B474055 : Blo 471786 474055 := bstep (se 1 (by rfl) ⟨355541, by rfl⟩ : syracuseStep 474055 = 711083) B711083
theorem B474075 : Blo 471786 474075 := bstep (se 1 (by rfl) ⟨355556, by rfl⟩ : syracuseStep 474075 = 711113) B711113
theorem B1063943 : Blo 471786 1063943 := bstep (se 1 (by rfl) ⟨797957, by rfl⟩ : syracuseStep 1063943 = 1595915) B1595915
theorem B474151 : Blo 471786 474151 := bstep (se 1 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 474151 = 711227) B711227
theorem B2505779 : Blo 471786 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1064015 : Blo 471786 1064015 := bstep (se 1 (by rfl) ⟨798011, by rfl⟩ : syracuseStep 1064015 = 1596023) B1596023
theorem B474191 : Blo 471786 474191 := bstep (se 1 (by rfl) ⟨355643, by rfl⟩ : syracuseStep 474191 = 711287) B711287
theorem B474207 : Blo 471786 474207 := bstep (se 1 (by rfl) ⟨355655, by rfl⟩ : syracuseStep 474207 = 711311) B711311
theorem B474235 : Blo 471786 474235 := bstep (se 1 (by rfl) ⟨355676, by rfl⟩ : syracuseStep 474235 = 711353) B711353
theorem B474287 : Blo 471786 474287 := bstep (se 1 (by rfl) ⟨355715, by rfl⟩ : syracuseStep 474287 = 711431) B711431
theorem B474311 : Blo 471786 474311 := bstep (se 1 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 474311 = 711467) B711467
theorem B474331 : Blo 471786 474331 := bstep (se 1 (by rfl) ⟨355748, by rfl⟩ : syracuseStep 474331 = 711497) B711497
theorem B2276599 : Blo 471786 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B474407 : Blo 471786 474407 := bstep (se 1 (by rfl) ⟨355805, by rfl⟩ : syracuseStep 474407 = 711611) B711611
theorem B474447 : Blo 471786 474447 := bstep (se 1 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 474447 = 711671) B711671
theorem B474463 : Blo 471786 474463 := bstep (se 1 (by rfl) ⟨355847, by rfl⟩ : syracuseStep 474463 = 711695) B711695
theorem B474491 : Blo 471786 474491 := bstep (se 1 (by rfl) ⟨355868, by rfl⟩ : syracuseStep 474491 = 711737) B711737
theorem B2407805 : Blo 471786 2407805 := bstep (se 3 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 2407805 = 902927) B902927
theorem B474543 : Blo 471786 474543 := bstep (se 1 (by rfl) ⟨355907, by rfl⟩ : syracuseStep 474543 = 711815) B711815
theorem B474567 : Blo 471786 474567 := bstep (se 1 (by rfl) ⟨355925, by rfl⟩ : syracuseStep 474567 = 711851) B711851
theorem B1064411 : Blo 471786 1064411 := bstep (se 1 (by rfl) ⟨798308, by rfl⟩ : syracuseStep 1064411 = 1596617) B1596617
theorem B474587 : Blo 471786 474587 := bstep (se 1 (by rfl) ⟨355940, by rfl⟩ : syracuseStep 474587 = 711881) B711881
theorem B474663 : Blo 471786 474663 := bstep (se 1 (by rfl) ⟨355997, by rfl⟩ : syracuseStep 474663 = 711995) B711995
theorem B474703 : Blo 471786 474703 := bstep (se 1 (by rfl) ⟨356027, by rfl⟩ : syracuseStep 474703 = 712055) B712055
theorem B474719 : Blo 471786 474719 := bstep (se 1 (by rfl) ⟨356039, by rfl⟩ : syracuseStep 474719 = 712079) B712079
theorem B474747 : Blo 471786 474747 := bstep (se 1 (by rfl) ⟨356060, by rfl⟩ : syracuseStep 474747 = 712121) B712121
theorem B474799 : Blo 471786 474799 := bstep (se 1 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 474799 = 712199) B712199
theorem B474823 : Blo 471786 474823 := bstep (se 1 (by rfl) ⟨356117, by rfl⟩ : syracuseStep 474823 = 712235) B712235
theorem B474843 : Blo 471786 474843 := bstep (se 1 (by rfl) ⟨356132, by rfl⟩ : syracuseStep 474843 = 712265) B712265
theorem B13811471 : Blo 471786 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B1523485 : Blo 471786 1523485 := bstep (se 3 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 1523485 = 571307) B571307
theorem B474919 : Blo 471786 474919 := bstep (se 1 (by rfl) ⟨356189, by rfl⟩ : syracuseStep 474919 = 712379) B712379
theorem B474959 : Blo 471786 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B474975 : Blo 471786 474975 := bstep (se 1 (by rfl) ⟨356231, by rfl⟩ : syracuseStep 474975 = 712463) B712463
theorem B475003 : Blo 471786 475003 := bstep (se 1 (by rfl) ⟨356252, by rfl⟩ : syracuseStep 475003 = 712505) B712505
theorem B802703 : Blo 471786 802703 := bstep (se 1 (by rfl) ⟨602027, by rfl⟩ : syracuseStep 802703 = 1204055) B1204055
theorem B1064879 : Blo 471786 1064879 := bstep (se 1 (by rfl) ⟨798659, by rfl⟩ : syracuseStep 1064879 = 1597319) B1597319
theorem B475055 : Blo 471786 475055 := bstep (se 1 (by rfl) ⟨356291, by rfl⟩ : syracuseStep 475055 = 712583) B712583
theorem B10239929 : Blo 471786 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B475079 : Blo 471786 475079 := bstep (se 1 (by rfl) ⟨356309, by rfl⟩ : syracuseStep 475079 = 712619) B712619
theorem B475099 : Blo 471786 475099 := bstep (se 1 (by rfl) ⟨356324, by rfl⟩ : syracuseStep 475099 = 712649) B712649
theorem B475175 : Blo 471786 475175 := bstep (se 1 (by rfl) ⟨356381, by rfl⟩ : syracuseStep 475175 = 712763) B712763
theorem B475215 : Blo 471786 475215 := bstep (se 1 (by rfl) ⟨356411, by rfl⟩ : syracuseStep 475215 = 712823) B712823
theorem B475231 : Blo 471786 475231 := bstep (se 1 (by rfl) ⟨356423, by rfl⟩ : syracuseStep 475231 = 712847) B712847
theorem B3850355 : Blo 471786 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B475259 : Blo 471786 475259 := bstep (se 1 (by rfl) ⟨356444, by rfl⟩ : syracuseStep 475259 = 712889) B712889
theorem B1065131 : Blo 471786 1065131 := bstep (se 1 (by rfl) ⟨798848, by rfl⟩ : syracuseStep 1065131 = 1597697) B1597697
theorem B475311 : Blo 471786 475311 := bstep (se 1 (by rfl) ⟨356483, by rfl⟩ : syracuseStep 475311 = 712967) B712967
theorem B475335 : Blo 471786 475335 := bstep (se 1 (by rfl) ⟨356501, by rfl⟩ : syracuseStep 475335 = 713003) B713003
theorem B475355 : Blo 471786 475355 := bstep (se 1 (by rfl) ⟨356516, by rfl⟩ : syracuseStep 475355 = 713033) B713033
theorem B1196279 : Blo 471786 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B475431 : Blo 471786 475431 := bstep (se 1 (by rfl) ⟨356573, by rfl⟩ : syracuseStep 475431 = 713147) B713147
theorem B475471 : Blo 471786 475471 := bstep (se 1 (by rfl) ⟨356603, by rfl⟩ : syracuseStep 475471 = 713207) B713207
theorem B475487 : Blo 471786 475487 := bstep (se 1 (by rfl) ⟨356615, by rfl⟩ : syracuseStep 475487 = 713231) B713231
theorem B475515 : Blo 471786 475515 := bstep (se 1 (by rfl) ⟨356636, by rfl⟩ : syracuseStep 475515 = 713273) B713273
theorem B475567 : Blo 471786 475567 := bstep (se 1 (by rfl) ⟨356675, by rfl⟩ : syracuseStep 475567 = 713351) B713351
theorem B475591 : Blo 471786 475591 := bstep (se 1 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 475591 = 713387) B713387
theorem B475611 : Blo 471786 475611 := bstep (se 1 (by rfl) ⟨356708, by rfl⟩ : syracuseStep 475611 = 713417) B713417
theorem B475687 : Blo 471786 475687 := bstep (se 1 (by rfl) ⟨356765, by rfl⟩ : syracuseStep 475687 = 713531) B713531
theorem B475727 : Blo 471786 475727 := bstep (se 1 (by rfl) ⟨356795, by rfl⟩ : syracuseStep 475727 = 713591) B713591
theorem B475743 : Blo 471786 475743 := bstep (se 1 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 475743 = 713615) B713615
theorem B6046325 : Blo 471786 6046325 := bstep (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) B566843
theorem B475771 : Blo 471786 475771 := bstep (se 1 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 475771 = 713657) B713657
theorem B1065671 : Blo 471786 1065671 := bstep (se 1 (by rfl) ⟨799253, by rfl⟩ : syracuseStep 1065671 = 1598507) B1598507
theorem B902107 : Blo 471786 902107 := bstep (se 1 (by rfl) ⟨676580, by rfl⟩ : syracuseStep 902107 = 1353161) B1353161
theorem B902153 : Blo 471786 902153 := bstep (se 2 (by rfl) ⟨338307, by rfl⟩ : syracuseStep 902153 = 676615) B676615
theorem B541895 : Blo 471786 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B902495 : Blo 471786 902495 := bstep (se 1 (by rfl) ⟨676871, by rfl⟩ : syracuseStep 902495 = 1353743) B1353743
theorem B3589595 : Blo 471786 3589595 := bstep (se 1 (by rfl) ⟨2692196, by rfl⟩ : syracuseStep 3589595 = 5384393) B5384393
theorem B1066535 : Blo 471786 1066535 := bstep (se 1 (by rfl) ⟨799901, by rfl⟩ : syracuseStep 1066535 = 1599803) B1599803
theorem B1197767 : Blo 471786 1197767 := bstep (se 1 (by rfl) ⟨898325, by rfl⟩ : syracuseStep 1197767 = 1796651) B1796651
theorem B607943 : Blo 471786 607943 := bstep (se 1 (by rfl) ⟨455957, by rfl⟩ : syracuseStep 607943 = 911915) B911915
theorem B2049785 : Blo 471786 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B1066859 : Blo 471786 1066859 := bstep (se 1 (by rfl) ⟨800144, by rfl⟩ : syracuseStep 1066859 = 1600289) B1600289
theorem B2017133 : Blo 471786 2017133 := bstep (se 3 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 2017133 = 756425) B756425
theorem B1066913 : Blo 471786 1066913 := bstep (se 2 (by rfl) ⟨400092, by rfl⟩ : syracuseStep 1066913 = 800185) B800185
theorem B3590081 : Blo 471786 3590081 := bstep (se 2 (by rfl) ⟨1346280, by rfl⟩ : syracuseStep 3590081 = 2692561) B2692561
theorem B673915 : Blo 471786 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B3426461 : Blo 471786 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B1362091 : Blo 471786 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B1067255 : Blo 471786 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B2017817 : Blo 471786 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B3066569 : Blo 471786 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B2214611 : Blo 471786 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B5393141 : Blo 471786 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B1198921 : Blo 471786 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1067849 : Blo 471786 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B674735 : Blo 471786 674735 := bstep (se 1 (by rfl) ⟨506051, by rfl⟩ : syracuseStep 674735 = 1012103) B1012103
theorem B707783 : Blo 471786 707783 := bstep (se 1 (by rfl) ⟨530837, by rfl⟩ : syracuseStep 707783 = 1061675) B1061675
theorem B1592567 : Blo 471786 1592567 := bstep (se 1 (by rfl) ⟨1194425, by rfl⟩ : syracuseStep 1592567 = 2388851) B2388851
theorem B707945 : Blo 471786 707945 := bstep (se 2 (by rfl) ⟨265479, by rfl⟩ : syracuseStep 707945 = 530959) B530959
theorem B3591539 : Blo 471786 3591539 := bstep (se 1 (by rfl) ⟨2693654, by rfl⟩ : syracuseStep 3591539 = 5387309) B5387309
theorem B708023 : Blo 471786 708023 := bstep (se 1 (by rfl) ⟨531017, by rfl⟩ : syracuseStep 708023 = 1062035) B1062035
theorem B2280905 : Blo 471786 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B708059 : Blo 471786 708059 := bstep (se 1 (by rfl) ⟨531044, by rfl⟩ : syracuseStep 708059 = 1062089) B1062089
theorem B2280923 : Blo 471786 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B1592891 : Blo 471786 1592891 := bstep (se 1 (by rfl) ⟨1194668, by rfl⟩ : syracuseStep 1592891 = 2389337) B2389337
theorem B1068641 : Blo 471786 1068641 := bstep (se 2 (by rfl) ⟨400740, by rfl⟩ : syracuseStep 1068641 = 801481) B801481
theorem B1593161 : Blo 471786 1593161 := bstep (se 2 (by rfl) ⟨597435, by rfl⟩ : syracuseStep 1593161 = 1194871) B1194871
theorem B708527 : Blo 471786 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B1200055 : Blo 471786 1200055 := bstep (se 1 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 1200055 = 1800083) B1800083
theorem B1068983 : Blo 471786 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B10899461 : Blo 471786 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B708617 : Blo 471786 708617 := bstep (se 2 (by rfl) ⟨265731, by rfl⟩ : syracuseStep 708617 = 531463) B531463
theorem B9129995 : Blo 471786 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B708647 : Blo 471786 708647 := bstep (se 1 (by rfl) ⟨531485, by rfl⟩ : syracuseStep 708647 = 1062971) B1062971
theorem B708731 : Blo 471786 708731 := bstep (se 1 (by rfl) ⟨531548, by rfl⟩ : syracuseStep 708731 = 1063097) B1063097
theorem B3297509 : Blo 471786 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B708857 : Blo 471786 708857 := bstep (se 2 (by rfl) ⟨265821, by rfl⟩ : syracuseStep 708857 = 531643) B531643
theorem B708959 : Blo 471786 708959 := bstep (se 1 (by rfl) ⟨531719, by rfl⟩ : syracuseStep 708959 = 1063439) B1063439
theorem B708971 : Blo 471786 708971 := bstep (se 1 (by rfl) ⟨531728, by rfl⟩ : syracuseStep 708971 = 1063457) B1063457
theorem B676279 : Blo 471786 676279 := bstep (se 1 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 676279 = 1014419) B1014419
theorem B1069577 : Blo 471786 1069577 := bstep (se 2 (by rfl) ⟨401091, by rfl⟩ : syracuseStep 1069577 = 802183) B802183
theorem B709199 : Blo 471786 709199 := bstep (se 1 (by rfl) ⟨531899, by rfl⟩ : syracuseStep 709199 = 1063799) B1063799
theorem B709319 : Blo 471786 709319 := bstep (se 1 (by rfl) ⟨531989, by rfl⟩ : syracuseStep 709319 = 1063979) B1063979
theorem B1069919 : Blo 471786 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B709481 : Blo 471786 709481 := bstep (se 2 (by rfl) ⟨266055, by rfl⟩ : syracuseStep 709481 = 532111) B532111
theorem B1594295 : Blo 471786 1594295 := bstep (se 1 (by rfl) ⟨1195721, by rfl⟩ : syracuseStep 1594295 = 2391443) B2391443
theorem B709559 : Blo 471786 709559 := bstep (se 1 (by rfl) ⟨532169, by rfl⟩ : syracuseStep 709559 = 1064339) B1064339
theorem B709595 : Blo 471786 709595 := bstep (se 1 (by rfl) ⟨532196, by rfl⟩ : syracuseStep 709595 = 1064393) B1064393
theorem B1070099 : Blo 471786 1070099 := bstep (se 1 (by rfl) ⟨802574, by rfl⟩ : syracuseStep 1070099 = 1605149) B1605149
theorem B1201513 : Blo 471786 1201513 := bstep (se 2 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 1201513 = 901135) B901135
theorem B1070441 : Blo 471786 1070441 := bstep (se 2 (by rfl) ⟨401415, by rfl⟩ : syracuseStep 1070441 = 802831) B802831
theorem B710063 : Blo 471786 710063 := bstep (se 1 (by rfl) ⟨532547, by rfl⟩ : syracuseStep 710063 = 1065095) B1065095
theorem B1594889 : Blo 471786 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B710153 : Blo 471786 710153 := bstep (se 2 (by rfl) ⟨266307, by rfl⟩ : syracuseStep 710153 = 532615) B532615
theorem B710183 : Blo 471786 710183 := bstep (se 1 (by rfl) ⟨532637, by rfl⟩ : syracuseStep 710183 = 1065275) B1065275
theorem B25876037 : Blo 471786 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B1201787 : Blo 471786 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B710267 : Blo 471786 710267 := bstep (se 1 (by rfl) ⟨532700, by rfl⟩ : syracuseStep 710267 = 1065401) B1065401
theorem B710393 : Blo 471786 710393 := bstep (se 2 (by rfl) ⟨266397, by rfl⟩ : syracuseStep 710393 = 532795) B532795
theorem B710495 : Blo 471786 710495 := bstep (se 1 (by rfl) ⟨532871, by rfl⟩ : syracuseStep 710495 = 1065743) B1065743
theorem B710507 : Blo 471786 710507 := bstep (se 1 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 710507 = 1065761) B1065761
theorem B743275 : Blo 471786 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B2283383 : Blo 471786 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B710735 : Blo 471786 710735 := bstep (se 1 (by rfl) ⟨533051, by rfl⟩ : syracuseStep 710735 = 1066103) B1066103
theorem B710855 : Blo 471786 710855 := bstep (se 1 (by rfl) ⟨533141, by rfl⟩ : syracuseStep 710855 = 1066283) B1066283
theorem B3889457 : Blo 471786 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1595753 : Blo 471786 1595753 := bstep (se 2 (by rfl) ⟨598407, by rfl⟩ : syracuseStep 1595753 = 1196815) B1196815
theorem B1137001 : Blo 471786 1137001 := bstep (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) B852751
theorem B711017 : Blo 471786 711017 := bstep (se 2 (by rfl) ⟨266631, by rfl⟩ : syracuseStep 711017 = 533263) B533263
theorem B1366397 : Blo 471786 1366397 := bstep (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) B512399
theorem B4053401 : Blo 471786 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B711095 : Blo 471786 711095 := bstep (se 1 (by rfl) ⟨533321, by rfl⟩ : syracuseStep 711095 = 1066643) B1066643
theorem B1792475 : Blo 471786 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B711131 : Blo 471786 711131 := bstep (se 1 (by rfl) ⟨533348, by rfl⟩ : syracuseStep 711131 = 1066697) B1066697
theorem B711599 : Blo 471786 711599 := bstep (se 1 (by rfl) ⟨533699, by rfl⟩ : syracuseStep 711599 = 1067399) B1067399
theorem B1596347 : Blo 471786 1596347 := bstep (se 1 (by rfl) ⟨1197260, by rfl⟩ : syracuseStep 1596347 = 2394521) B2394521
theorem B711689 : Blo 471786 711689 := bstep (se 2 (by rfl) ⟨266883, by rfl⟩ : syracuseStep 711689 = 533767) B533767
theorem B711719 : Blo 471786 711719 := bstep (se 1 (by rfl) ⟨533789, by rfl⟩ : syracuseStep 711719 = 1067579) B1067579
theorem B15588395 : Blo 471786 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B2284595 : Blo 471786 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B711803 : Blo 471786 711803 := bstep (se 1 (by rfl) ⟨533852, by rfl⟩ : syracuseStep 711803 = 1067705) B1067705
theorem B3038411 : Blo 471786 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B711929 : Blo 471786 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B712031 : Blo 471786 712031 := bstep (se 1 (by rfl) ⟨534023, by rfl⟩ : syracuseStep 712031 = 1068047) B1068047
theorem B712043 : Blo 471786 712043 := bstep (se 1 (by rfl) ⟨534032, by rfl⟩ : syracuseStep 712043 = 1068065) B1068065
theorem B1203599 : Blo 471786 1203599 := bstep (se 1 (by rfl) ⟨902699, by rfl⟩ : syracuseStep 1203599 = 1805399) B1805399
theorem B98557397 : Blo 471786 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B712271 : Blo 471786 712271 := bstep (se 1 (by rfl) ⟨534203, by rfl⟩ : syracuseStep 712271 = 1068407) B1068407
theorem B1793735 : Blo 471786 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B712391 : Blo 471786 712391 := bstep (se 1 (by rfl) ⟨534293, by rfl⟩ : syracuseStep 712391 = 1068587) B1068587
theorem B1203923 : Blo 471786 1203923 := bstep (se 1 (by rfl) ⟨902942, by rfl⟩ : syracuseStep 1203923 = 1805885) B1805885
theorem B1924823 : Blo 471786 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1236809 : Blo 471786 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B712553 : Blo 471786 712553 := bstep (se 2 (by rfl) ⟨267207, by rfl⟩ : syracuseStep 712553 = 534415) B534415
theorem B712631 : Blo 471786 712631 := bstep (se 1 (by rfl) ⟨534473, by rfl⟩ : syracuseStep 712631 = 1068947) B1068947
theorem B712667 : Blo 471786 712667 := bstep (se 1 (by rfl) ⟨534500, by rfl⟩ : syracuseStep 712667 = 1069001) B1069001
theorem B7659845 : Blo 471786 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B1794433 : Blo 471786 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B713135 : Blo 471786 713135 := bstep (se 1 (by rfl) ⟨534851, by rfl⟩ : syracuseStep 713135 = 1069703) B1069703
theorem B811529 : Blo 471786 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B713225 : Blo 471786 713225 := bstep (se 2 (by rfl) ⟨267459, by rfl⟩ : syracuseStep 713225 = 534919) B534919
theorem B713255 : Blo 471786 713255 := bstep (se 1 (by rfl) ⟨534941, by rfl⟩ : syracuseStep 713255 = 1069883) B1069883
theorem B1598075 : Blo 471786 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B713339 : Blo 471786 713339 := bstep (se 1 (by rfl) ⟨535004, by rfl⟩ : syracuseStep 713339 = 1070009) B1070009
theorem B1794707 : Blo 471786 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B713465 : Blo 471786 713465 := bstep (se 2 (by rfl) ⟨267549, by rfl⟩ : syracuseStep 713465 = 535099) B535099
theorem B1598237 : Blo 471786 1598237 := bstep (se 3 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 1598237 = 599339) B599339
theorem B713567 : Blo 471786 713567 := bstep (se 1 (by rfl) ⟨535175, by rfl⟩ : syracuseStep 713567 = 1070351) B1070351
theorem B713579 : Blo 471786 713579 := bstep (se 1 (by rfl) ⟨535184, by rfl⟩ : syracuseStep 713579 = 1070369) B1070369
theorem B15524783 : Blo 471786 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B4056065 : Blo 471786 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B3040409 : Blo 471786 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B1598939 : Blo 471786 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B3958283 : Blo 471786 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B2025283 : Blo 471786 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B3598343 : Blo 471786 3598343 := bstep (se 1 (by rfl) ⟨2698757, by rfl⟩ : syracuseStep 3598343 = 5397515) B5397515
theorem B1599641 : Blo 471786 1599641 := bstep (se 2 (by rfl) ⟨599865, by rfl⟩ : syracuseStep 1599641 = 1199731) B1199731
theorem B1796363 : Blo 471786 1796363 := bstep (se 1 (by rfl) ⟨1347272, by rfl⟩ : syracuseStep 1796363 = 2694545) B2694545
theorem B1731053 : Blo 471786 1731053 := bstep (se 3 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 1731053 = 649145) B649145
theorem B3598829 : Blo 471786 3598829 := bstep (se 3 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 3598829 = 1349561) B1349561
theorem B813607 : Blo 471786 813607 := bstep (se 1 (by rfl) ⟨610205, by rfl⟩ : syracuseStep 813607 = 1220411) B1220411
theorem B3631675 : Blo 471786 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B1010387 : Blo 471786 1010387 := bstep (se 1 (by rfl) ⟨757790, by rfl⟩ : syracuseStep 1010387 = 1515581) B1515581
theorem B1141577 : Blo 471786 1141577 := bstep (se 2 (by rfl) ⟨428091, by rfl⟩ : syracuseStep 1141577 = 856183) B856183
theorem B1600829 : Blo 471786 1600829 := bstep (se 3 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 1600829 = 600311) B600311
theorem B1797821 : Blo 471786 1797821 := bstep (se 3 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 1797821 = 674183) B674183
theorem B6090659 : Blo 471786 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B3403853 : Blo 471786 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B1601693 : Blo 471786 1601693 := bstep (se 3 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 1601693 = 600635) B600635
theorem B3600773 : Blo 471786 3600773 := bstep (se 4 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 3600773 = 675145) B675145
theorem B9826915 : Blo 471786 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1602233 : Blo 471786 1602233 := bstep (se 2 (by rfl) ⟨600837, by rfl⟩ : syracuseStep 1602233 = 1201675) B1201675
theorem B2388689 : Blo 471786 2388689 := bstep (se 2 (by rfl) ⟨895758, by rfl⟩ : syracuseStep 2388689 = 1791517) B1791517
theorem B5403347 : Blo 471786 5403347 := bstep (se 1 (by rfl) ⟨4052510, by rfl⟩ : syracuseStep 5403347 = 8105021) B8105021
theorem B3601259 : Blo 471786 3601259 := bstep (se 1 (by rfl) ⟨2700944, by rfl⟩ : syracuseStep 3601259 = 5401889) B5401889
theorem B1537103 : Blo 471786 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B1602827 : Blo 471786 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B1799567 : Blo 471786 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B1603097 : Blo 471786 1603097 := bstep (se 2 (by rfl) ⟨601161, by rfl⟩ : syracuseStep 1603097 = 1202323) B1202323
theorem B126613313 : Blo 471786 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B3045383 : Blo 471786 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B7796837 : Blo 471786 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B5142629 : Blo 471786 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B6060419 : Blo 471786 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B1210889 : Blo 471786 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B1800737 : Blo 471786 1800737 := bstep (se 2 (by rfl) ⟨675276, by rfl⟩ : syracuseStep 1800737 = 1350553) B1350553
theorem B1604231 : Blo 471786 1604231 := bstep (se 1 (by rfl) ⟨1203173, by rfl⟩ : syracuseStep 1604231 = 2406347) B2406347
theorem B2161337 : Blo 471786 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1604285 : Blo 471786 1604285 := bstep (se 3 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 1604285 = 601607) B601607
theorem B3603203 : Blo 471786 3603203 := bstep (se 1 (by rfl) ⟨2702402, by rfl⟩ : syracuseStep 3603203 = 5404805) B5404805
theorem B1801055 : Blo 471786 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B1604447 : Blo 471786 1604447 := bstep (se 1 (by rfl) ⟨1203335, by rfl⟩ : syracuseStep 1604447 = 2406671) B2406671
theorem B1604609 : Blo 471786 1604609 := bstep (se 2 (by rfl) ⟨601728, by rfl⟩ : syracuseStep 1604609 = 1203457) B1203457
theorem B1801223 : Blo 471786 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B2391119 : Blo 471786 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B1703369 : Blo 471786 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B92470733 : Blo 471786 92470733 := bstep (se 3 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 92470733 = 34676525) B34676525
theorem B1801709 : Blo 471786 1801709 := bstep (se 3 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 1801709 = 675641) B675641
theorem B2391767 : Blo 471786 2391767 := bstep (se 1 (by rfl) ⟨1793825, by rfl⟩ : syracuseStep 2391767 = 3587651) B3587651
theorem B1802027 : Blo 471786 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B1605419 : Blo 471786 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B29065229 : Blo 471786 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B4030883 : Blo 471786 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B2392577 : Blo 471786 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B2393063 : Blo 471786 2393063 := bstep (se 1 (by rfl) ⟨1794797, by rfl⟩ : syracuseStep 2393063 = 3589595) B3589595
theorem B1344755 : Blo 471786 1344755 := bstep (se 1 (by rfl) ⟨1008566, by rfl⟩ : syracuseStep 1344755 = 2017133) B2017133
theorem B2393387 : Blo 471786 2393387 := bstep (se 1 (by rfl) ⟨1795040, by rfl⟩ : syracuseStep 2393387 = 3590081) B3590081
theorem B1345211 : Blo 471786 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B1476407 : Blo 471786 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2394359 : Blo 471786 2394359 := bstep (se 1 (by rfl) ⟨1795769, by rfl⟩ : syracuseStep 2394359 = 3591539) B3591539
theorem B2394845 : Blo 471786 2394845 := bstep (se 3 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 2394845 = 898067) B898067
theorem B1706771 : Blo 471786 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B6916913 : Blo 471786 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B2198339 : Blo 471786 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B1445053 : Blo 471786 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B8621257 : Blo 471786 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B2166047 : Blo 471786 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B4033921 : Blo 471786 4033921 := bstep (se 2 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 4033921 = 3025441) B3025441
theorem B2592971 : Blo 471786 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B4035257 : Blo 471786 4035257 := bstep (se 2 (by rfl) ⟨1513221, by rfl⟩ : syracuseStep 4035257 = 3026443) B3026443
theorem B10392263 : Blo 471786 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B65704931 : Blo 471786 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B1283215 : Blo 471786 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B2168783 : Blo 471786 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B6166691 : Blo 471786 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B530779 : Blo 471786 530779 := bstep (se 1 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 530779 = 796169) B796169
theorem B530887 : Blo 471786 530887 := bstep (se 1 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 530887 = 796331) B796331
theorem B2398895 : Blo 471786 2398895 := bstep (se 1 (by rfl) ⟨1799171, by rfl⟩ : syracuseStep 2398895 = 3598343) B3598343
theorem B531247 : Blo 471786 531247 := bstep (se 1 (by rfl) ⟨398435, by rfl⟩ : syracuseStep 531247 = 796871) B796871
theorem B531355 : Blo 471786 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B1154035 : Blo 471786 1154035 := bstep (se 1 (by rfl) ⟨865526, by rfl⟩ : syracuseStep 1154035 = 1731053) B1731053
theorem B2399219 : Blo 471786 2399219 := bstep (se 1 (by rfl) ⟨1799414, by rfl⟩ : syracuseStep 2399219 = 3598829) B3598829
theorem B761051 : Blo 471786 761051 := bstep (se 1 (by rfl) ⟨570788, by rfl⟩ : syracuseStep 761051 = 1141577) B1141577
theorem B531751 : Blo 471786 531751 := bstep (se 1 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 531751 = 797627) B797627
theorem B531823 : Blo 471786 531823 := bstep (se 1 (by rfl) ⟨398867, by rfl⟩ : syracuseStep 531823 = 797735) B797735
theorem B532039 : Blo 471786 532039 := bstep (se 1 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 532039 = 798059) B798059
theorem B1515311 : Blo 471786 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B991033 : Blo 471786 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B2269235 : Blo 471786 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B2400515 : Blo 471786 2400515 := bstep (se 1 (by rfl) ⟨1800386, by rfl⟩ : syracuseStep 2400515 = 3600773) B3600773
theorem B532903 : Blo 471786 532903 := bstep (se 1 (by rfl) ⟨399677, by rfl⟩ : syracuseStep 532903 = 799355) B799355
theorem B1516001 : Blo 471786 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B2695751 : Blo 471786 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B2400839 : Blo 471786 2400839 := bstep (se 1 (by rfl) ⟨1800629, by rfl⟩ : syracuseStep 2400839 = 3601259) B3601259
theorem B1024735 : Blo 471786 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B599015 : Blo 471786 599015 := bstep (se 1 (by rfl) ⟨449261, by rfl⟩ : syracuseStep 599015 = 898523) B898523
theorem B533479 : Blo 471786 533479 := bstep (se 1 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 533479 = 800219) B800219
theorem B2696435 : Blo 471786 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B4040279 : Blo 471786 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B2631257 : Blo 471786 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B2402135 : Blo 471786 2402135 := bstep (se 1 (by rfl) ⟨1801601, by rfl⟩ : syracuseStep 2402135 = 3603203) B3603203
theorem B1714441 : Blo 471786 1714441 := bstep (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) B1285831
theorem B61647155 : Blo 471786 61647155 := bstep (se 1 (by rfl) ⟨46235366, by rfl⟩ : syracuseStep 61647155 = 92470733) B92470733
theorem B4336001 : Blo 471786 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B535135 : Blo 471786 535135 := bstep (se 1 (by rfl) ⟨401351, by rfl⟩ : syracuseStep 535135 = 802703) B802703
theorem B6826619 : Blo 471786 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B2566903 : Blo 471786 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B797519 : Blo 471786 797519 := bstep (se 1 (by rfl) ⟨598139, by rfl⟩ : syracuseStep 797519 = 1196279) B1196279
theorem B7777361 : Blo 471786 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B601435 : Blo 471786 601435 := bstep (se 1 (by rfl) ⟨451076, by rfl⟩ : syracuseStep 601435 = 902153) B902153
theorem B8170993 : Blo 471786 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B3419657 : Blo 471786 3419657 := bstep (se 2 (by rfl) ⟨1282371, by rfl⟩ : syracuseStep 3419657 = 2564743) B2564743
theorem B601663 : Blo 471786 601663 := bstep (se 1 (by rfl) ⟨451247, by rfl⟩ : syracuseStep 601663 = 902495) B902495
theorem B798511 : Blo 471786 798511 := bstep (se 1 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 798511 = 1197767) B1197767
theorem B2404403 : Blo 471786 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B504155 : Blo 471786 504155 := bstep (se 1 (by rfl) ⟨378116, by rfl⟩ : syracuseStep 504155 = 756233) B756233
theorem B2044379 : Blo 471786 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B8663597 : Blo 471786 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B3584735 : Blo 471786 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B471855 : Blo 471786 471855 := bstep (se 1 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 471855 = 707783) B707783
theorem B1061711 : Blo 471786 1061711 := bstep (se 1 (by rfl) ⟨796283, by rfl⟩ : syracuseStep 1061711 = 1592567) B1592567
theorem B471963 : Blo 471786 471963 := bstep (se 1 (by rfl) ⟨353972, by rfl⟩ : syracuseStep 471963 = 707945) B707945
theorem B472015 : Blo 471786 472015 := bstep (se 1 (by rfl) ⟨354011, by rfl⟩ : syracuseStep 472015 = 708023) B708023
theorem B1520603 : Blo 471786 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B472039 : Blo 471786 472039 := bstep (se 1 (by rfl) ⟨354029, by rfl⟩ : syracuseStep 472039 = 708059) B708059
theorem B1520615 : Blo 471786 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B1061927 : Blo 471786 1061927 := bstep (se 1 (by rfl) ⟨796445, by rfl⟩ : syracuseStep 1061927 = 1592891) B1592891
theorem B2700377 : Blo 471786 2700377 := bstep (se 2 (by rfl) ⟨1012641, by rfl⟩ : syracuseStep 2700377 = 2025283) B2025283
theorem B1062107 : Blo 471786 1062107 := bstep (se 1 (by rfl) ⟨796580, by rfl⟩ : syracuseStep 1062107 = 1593161) B1593161
theorem B472351 : Blo 471786 472351 := bstep (se 1 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 472351 = 708527) B708527
theorem B472411 : Blo 471786 472411 := bstep (se 1 (by rfl) ⟨354308, by rfl⟩ : syracuseStep 472411 = 708617) B708617
theorem B472431 : Blo 471786 472431 := bstep (se 1 (by rfl) ⟨354323, by rfl⟩ : syracuseStep 472431 = 708647) B708647
theorem B1062305 : Blo 471786 1062305 := bstep (se 2 (by rfl) ⟨398364, by rfl⟩ : syracuseStep 1062305 = 796729) B796729
theorem B472487 : Blo 471786 472487 := bstep (se 1 (by rfl) ⟨354365, by rfl⟩ : syracuseStep 472487 = 708731) B708731
theorem B898553 : Blo 471786 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B472571 : Blo 471786 472571 := bstep (se 1 (by rfl) ⟨354428, by rfl⟩ : syracuseStep 472571 = 708857) B708857
theorem B1816121 : Blo 471786 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B472639 : Blo 471786 472639 := bstep (se 1 (by rfl) ⟨354479, by rfl⟩ : syracuseStep 472639 = 708959) B708959
theorem B472647 : Blo 471786 472647 := bstep (se 1 (by rfl) ⟨354485, by rfl⟩ : syracuseStep 472647 = 708971) B708971
theorem B2406023 : Blo 471786 2406023 := bstep (se 1 (by rfl) ⟨1804517, by rfl⟩ : syracuseStep 2406023 = 3609035) B3609035
theorem B472799 : Blo 471786 472799 := bstep (se 1 (by rfl) ⟨354599, by rfl⟩ : syracuseStep 472799 = 709199) B709199
theorem B472879 : Blo 471786 472879 := bstep (se 1 (by rfl) ⟨354659, by rfl⟩ : syracuseStep 472879 = 709319) B709319
theorem B472987 : Blo 471786 472987 := bstep (se 1 (by rfl) ⟨354740, by rfl⟩ : syracuseStep 472987 = 709481) B709481
theorem B1062863 : Blo 471786 1062863 := bstep (se 1 (by rfl) ⟨797147, by rfl⟩ : syracuseStep 1062863 = 1594295) B1594295
theorem B473039 : Blo 471786 473039 := bstep (se 1 (by rfl) ⟨354779, by rfl⟩ : syracuseStep 473039 = 709559) B709559
theorem B473063 : Blo 471786 473063 := bstep (se 1 (by rfl) ⟨354797, by rfl⟩ : syracuseStep 473063 = 709595) B709595
theorem B4634657 : Blo 471786 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B473375 : Blo 471786 473375 := bstep (se 1 (by rfl) ⟨355031, by rfl⟩ : syracuseStep 473375 = 710063) B710063
theorem B1063241 : Blo 471786 1063241 := bstep (se 2 (by rfl) ⟨398715, by rfl⟩ : syracuseStep 1063241 = 797431) B797431
theorem B1063259 : Blo 471786 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B473435 : Blo 471786 473435 := bstep (se 1 (by rfl) ⟨355076, by rfl⟩ : syracuseStep 473435 = 710153) B710153
theorem B899419 : Blo 471786 899419 := bstep (se 1 (by rfl) ⟨674564, by rfl⟩ : syracuseStep 899419 = 1349129) B1349129
theorem B473455 : Blo 471786 473455 := bstep (se 1 (by rfl) ⟨355091, by rfl⟩ : syracuseStep 473455 = 710183) B710183
theorem B17250691 : Blo 471786 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B473511 : Blo 471786 473511 := bstep (se 1 (by rfl) ⟨355133, by rfl⟩ : syracuseStep 473511 = 710267) B710267
theorem B899495 : Blo 471786 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B801191 : Blo 471786 801191 := bstep (se 1 (by rfl) ⟨600893, by rfl⟩ : syracuseStep 801191 = 1201787) B1201787
theorem B473595 : Blo 471786 473595 := bstep (se 1 (by rfl) ⟨355196, by rfl⟩ : syracuseStep 473595 = 710393) B710393
theorem B899579 : Blo 471786 899579 := bstep (se 1 (by rfl) ⟨674684, by rfl⟩ : syracuseStep 899579 = 1349369) B1349369
theorem B473663 : Blo 471786 473663 := bstep (se 1 (by rfl) ⟨355247, by rfl⟩ : syracuseStep 473663 = 710495) B710495
theorem B473671 : Blo 471786 473671 := bstep (se 1 (by rfl) ⟨355253, by rfl⟩ : syracuseStep 473671 = 710507) B710507
theorem B801353 : Blo 471786 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B1522255 : Blo 471786 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B473823 : Blo 471786 473823 := bstep (se 1 (by rfl) ⟨355367, by rfl⟩ : syracuseStep 473823 = 710735) B710735
theorem B473903 : Blo 471786 473903 := bstep (se 1 (by rfl) ⟨355427, by rfl⟩ : syracuseStep 473903 = 710855) B710855
theorem B1063835 : Blo 471786 1063835 := bstep (se 1 (by rfl) ⟨797876, by rfl⟩ : syracuseStep 1063835 = 1595753) B1595753
theorem B474011 : Blo 471786 474011 := bstep (se 1 (by rfl) ⟨355508, by rfl⟩ : syracuseStep 474011 = 711017) B711017
theorem B900011 : Blo 471786 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B2702267 : Blo 471786 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B474063 : Blo 471786 474063 := bstep (se 1 (by rfl) ⟨355547, by rfl⟩ : syracuseStep 474063 = 711095) B711095
theorem B1194983 : Blo 471786 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B474087 : Blo 471786 474087 := bstep (se 1 (by rfl) ⟨355565, by rfl⟩ : syracuseStep 474087 = 711131) B711131
theorem B1064033 : Blo 471786 1064033 := bstep (se 2 (by rfl) ⟨399012, by rfl⟩ : syracuseStep 1064033 = 798025) B798025
theorem B1621181 : Blo 471786 1621181 := bstep (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) B607943
theorem B2407643 : Blo 471786 2407643 := bstep (se 1 (by rfl) ⟨1805732, by rfl⟩ : syracuseStep 2407643 = 3611465) B3611465
theorem B474399 : Blo 471786 474399 := bstep (se 1 (by rfl) ⟨355799, by rfl⟩ : syracuseStep 474399 = 711599) B711599
theorem B1064231 : Blo 471786 1064231 := bstep (se 1 (by rfl) ⟨798173, by rfl⟩ : syracuseStep 1064231 = 1596347) B1596347
theorem B900391 : Blo 471786 900391 := bstep (se 1 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 900391 = 1350587) B1350587
theorem B474459 : Blo 471786 474459 := bstep (se 1 (by rfl) ⟨355844, by rfl⟩ : syracuseStep 474459 = 711689) B711689
theorem B474479 : Blo 471786 474479 := bstep (se 1 (by rfl) ⟨355859, by rfl⟩ : syracuseStep 474479 = 711719) B711719
theorem B1523063 : Blo 471786 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B474535 : Blo 471786 474535 := bstep (se 1 (by rfl) ⟨355901, by rfl⟩ : syracuseStep 474535 = 711803) B711803
theorem B900551 : Blo 471786 900551 := bstep (se 1 (by rfl) ⟨675413, by rfl⟩ : syracuseStep 900551 = 1350827) B1350827
theorem B474619 : Blo 471786 474619 := bstep (se 1 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 474619 = 711929) B711929
theorem B474687 : Blo 471786 474687 := bstep (se 1 (by rfl) ⟨356015, by rfl⟩ : syracuseStep 474687 = 712031) B712031
theorem B474695 : Blo 471786 474695 := bstep (se 1 (by rfl) ⟨356021, by rfl⟩ : syracuseStep 474695 = 712043) B712043
theorem B802399 : Blo 471786 802399 := bstep (se 1 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 802399 = 1203599) B1203599
theorem B1195681 : Blo 471786 1195681 := bstep (se 2 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 1195681 = 896761) B896761
theorem B1064609 : Blo 471786 1064609 := bstep (se 2 (by rfl) ⟨399228, by rfl⟩ : syracuseStep 1064609 = 798457) B798457
theorem B474847 : Blo 471786 474847 := bstep (se 1 (by rfl) ⟨356135, by rfl⟩ : syracuseStep 474847 = 712271) B712271
theorem B1195823 : Blo 471786 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B474927 : Blo 471786 474927 := bstep (se 1 (by rfl) ⟨356195, by rfl⟩ : syracuseStep 474927 = 712391) B712391
theorem B802615 : Blo 471786 802615 := bstep (se 1 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 802615 = 1203923) B1203923
theorem B475035 : Blo 471786 475035 := bstep (se 1 (by rfl) ⟨356276, by rfl⟩ : syracuseStep 475035 = 712553) B712553
theorem B475087 : Blo 471786 475087 := bstep (se 1 (by rfl) ⟨356315, by rfl⟩ : syracuseStep 475087 = 712631) B712631
theorem B475111 : Blo 471786 475111 := bstep (se 1 (by rfl) ⟨356333, by rfl⟩ : syracuseStep 475111 = 712667) B712667
theorem B1064969 : Blo 471786 1064969 := bstep (se 2 (by rfl) ⟨399363, by rfl⟩ : syracuseStep 1064969 = 798727) B798727
theorem B475423 : Blo 471786 475423 := bstep (se 1 (by rfl) ⟨356567, by rfl⟩ : syracuseStep 475423 = 713135) B713135
theorem B541019 : Blo 471786 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B475483 : Blo 471786 475483 := bstep (se 1 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 475483 = 713225) B713225
theorem B475503 : Blo 471786 475503 := bstep (se 1 (by rfl) ⟨356627, by rfl⟩ : syracuseStep 475503 = 713255) B713255
theorem B1065383 : Blo 471786 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B475559 : Blo 471786 475559 := bstep (se 1 (by rfl) ⟨356669, by rfl⟩ : syracuseStep 475559 = 713339) B713339
theorem B1196471 : Blo 471786 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B475643 : Blo 471786 475643 := bstep (se 1 (by rfl) ⟨356732, by rfl⟩ : syracuseStep 475643 = 713465) B713465
theorem B1065491 : Blo 471786 1065491 := bstep (se 1 (by rfl) ⟨799118, by rfl⟩ : syracuseStep 1065491 = 1598237) B1598237
theorem B475711 : Blo 471786 475711 := bstep (se 1 (by rfl) ⟨356783, by rfl⟩ : syracuseStep 475711 = 713567) B713567
theorem B475719 : Blo 471786 475719 := bstep (se 1 (by rfl) ⟨356789, by rfl⟩ : syracuseStep 475719 = 713579) B713579
theorem B1065545 : Blo 471786 1065545 := bstep (se 2 (by rfl) ⟨399579, by rfl⟩ : syracuseStep 1065545 = 799159) B799159
theorem B901705 : Blo 471786 901705 := bstep (se 2 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 901705 = 676279) B676279
theorem B2704043 : Blo 471786 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B639823 : Blo 471786 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B1065959 : Blo 471786 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B2638855 : Blo 471786 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B2016551 : Blo 471786 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B1066337 : Blo 471786 1066337 := bstep (se 2 (by rfl) ⟨399876, by rfl⟩ : syracuseStep 1066337 = 799753) B799753
theorem B1066427 : Blo 471786 1066427 := bstep (se 1 (by rfl) ⟨799820, by rfl⟩ : syracuseStep 1066427 = 1599641) B1599641
theorem B1197575 : Blo 471786 1197575 := bstep (se 1 (by rfl) ⟨898181, by rfl⟩ : syracuseStep 1197575 = 1796363) B1796363
theorem B1197625 : Blo 471786 1197625 := bstep (se 2 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 1197625 = 898219) B898219
theorem B1066553 : Blo 471786 1066553 := bstep (se 2 (by rfl) ⟨399957, by rfl⟩ : syracuseStep 1066553 = 799915) B799915
theorem B673591 : Blo 471786 673591 := bstep (se 1 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 673591 = 1010387) B1010387
theorem B1197929 : Blo 471786 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B1067219 : Blo 471786 1067219 := bstep (se 1 (by rfl) ⟨800414, by rfl⟩ : syracuseStep 1067219 = 1600829) B1600829
theorem B1067273 : Blo 471786 1067273 := bstep (se 2 (by rfl) ⟨400227, by rfl⟩ : syracuseStep 1067273 = 800455) B800455
theorem B3590567 : Blo 471786 3590567 := bstep (se 1 (by rfl) ⟨2692925, by rfl⟩ : syracuseStep 3590567 = 5385851) B5385851
theorem B1198547 : Blo 471786 1198547 := bstep (se 1 (by rfl) ⟨898910, by rfl⟩ : syracuseStep 1198547 = 1797821) B1797821
theorem B1067489 : Blo 471786 1067489 := bstep (se 2 (by rfl) ⟨400308, by rfl⟩ : syracuseStep 1067489 = 800617) B800617
theorem B3066491 : Blo 471786 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B1067795 : Blo 471786 1067795 := bstep (se 1 (by rfl) ⟨800846, by rfl⟩ : syracuseStep 1067795 = 1601693) B1601693
theorem B2018191 : Blo 471786 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1068155 : Blo 471786 1068155 := bstep (se 1 (by rfl) ⟨801116, by rfl⟩ : syracuseStep 1068155 = 1602233) B1602233
theorem B1592459 : Blo 471786 1592459 := bstep (se 1 (by rfl) ⟨1194344, by rfl⟩ : syracuseStep 1592459 = 2388689) B2388689
theorem B675049 : Blo 471786 675049 := bstep (se 2 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 675049 = 506287) B506287
theorem B1068281 : Blo 471786 1068281 := bstep (se 2 (by rfl) ⟨400605, by rfl⟩ : syracuseStep 1068281 = 801211) B801211
theorem B707879 : Blo 471786 707879 := bstep (se 1 (by rfl) ⟨530909, by rfl⟩ : syracuseStep 707879 = 1061819) B1061819
theorem B707963 : Blo 471786 707963 := bstep (se 1 (by rfl) ⟨530972, by rfl⟩ : syracuseStep 707963 = 1061945) B1061945
theorem B1068425 : Blo 471786 1068425 := bstep (se 2 (by rfl) ⟨400659, by rfl⟩ : syracuseStep 1068425 = 801319) B801319
theorem B708089 : Blo 471786 708089 := bstep (se 2 (by rfl) ⟨265533, by rfl⟩ : syracuseStep 708089 = 531067) B531067
theorem B1068551 : Blo 471786 1068551 := bstep (se 1 (by rfl) ⟨801413, by rfl⟩ : syracuseStep 1068551 = 1602827) B1602827
theorem B708191 : Blo 471786 708191 := bstep (se 1 (by rfl) ⟨531143, by rfl⟩ : syracuseStep 708191 = 1062287) B1062287
theorem B1199711 : Blo 471786 1199711 := bstep (se 1 (by rfl) ⟨899783, by rfl⟩ : syracuseStep 1199711 = 1799567) B1799567
theorem B1068731 : Blo 471786 1068731 := bstep (se 1 (by rfl) ⟨801548, by rfl⟩ : syracuseStep 1068731 = 1603097) B1603097
theorem B708407 : Blo 471786 708407 := bstep (se 1 (by rfl) ⟨531305, by rfl⟩ : syracuseStep 708407 = 1062611) B1062611
theorem B1068857 : Blo 471786 1068857 := bstep (se 2 (by rfl) ⟨400821, by rfl⟩ : syracuseStep 1068857 = 801643) B801643
theorem B4542317 : Blo 471786 4542317 := bstep (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) B1703369
theorem B5197891 : Blo 471786 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B3428419 : Blo 471786 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B708713 : Blo 471786 708713 := bstep (se 2 (by rfl) ⟨265767, by rfl⟩ : syracuseStep 708713 = 531535) B531535
theorem B3035465 : Blo 471786 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B807259 : Blo 471786 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B1200491 : Blo 471786 1200491 := bstep (se 1 (by rfl) ⟨900368, by rfl⟩ : syracuseStep 1200491 = 1800737) B1800737
theorem B709031 : Blo 471786 709031 := bstep (se 1 (by rfl) ⟨531773, by rfl⟩ : syracuseStep 709031 = 1063547) B1063547
theorem B1069487 : Blo 471786 1069487 := bstep (se 1 (by rfl) ⟨802115, by rfl⟩ : syracuseStep 1069487 = 1604231) B1604231
theorem B1069523 : Blo 471786 1069523 := bstep (se 1 (by rfl) ⟨802142, by rfl⟩ : syracuseStep 1069523 = 1604285) B1604285
theorem B709115 : Blo 471786 709115 := bstep (se 1 (by rfl) ⟨531836, by rfl⟩ : syracuseStep 709115 = 1063673) B1063673
theorem B3854897 : Blo 471786 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B1200703 : Blo 471786 1200703 := bstep (se 1 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 1200703 = 1801055) B1801055
theorem B1069631 : Blo 471786 1069631 := bstep (se 1 (by rfl) ⟨802223, by rfl⟩ : syracuseStep 1069631 = 1604447) B1604447
theorem B709241 : Blo 471786 709241 := bstep (se 2 (by rfl) ⟨265965, by rfl⟩ : syracuseStep 709241 = 531931) B531931
theorem B1069739 : Blo 471786 1069739 := bstep (se 1 (by rfl) ⟨802304, by rfl⟩ : syracuseStep 1069739 = 1604609) B1604609
theorem B709295 : Blo 471786 709295 := bstep (se 1 (by rfl) ⟨531971, by rfl⟩ : syracuseStep 709295 = 1063943) B1063943
theorem B1200815 : Blo 471786 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B1594079 : Blo 471786 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B709343 : Blo 471786 709343 := bstep (se 1 (by rfl) ⟨532007, by rfl⟩ : syracuseStep 709343 = 1064015) B1064015
theorem B3298157 : Blo 471786 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B51958745 : Blo 471786 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B709607 : Blo 471786 709607 := bstep (se 1 (by rfl) ⟨532205, by rfl⟩ : syracuseStep 709607 = 1064411) B1064411
theorem B1201139 : Blo 471786 1201139 := bstep (se 1 (by rfl) ⟨900854, by rfl⟩ : syracuseStep 1201139 = 1801709) B1801709
theorem B1594511 : Blo 471786 1594511 := bstep (se 1 (by rfl) ⟨1195883, by rfl⟩ : syracuseStep 1594511 = 2391767) B2391767
theorem B1201351 : Blo 471786 1201351 := bstep (se 1 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 1201351 = 1802027) B1802027
theorem B1070279 : Blo 471786 1070279 := bstep (se 1 (by rfl) ⟨802709, by rfl⟩ : syracuseStep 1070279 = 1605419) B1605419
theorem B709865 : Blo 471786 709865 := bstep (se 2 (by rfl) ⟨266199, by rfl⟩ : syracuseStep 709865 = 532399) B532399
theorem B709919 : Blo 471786 709919 := bstep (se 1 (by rfl) ⟨532439, by rfl⟩ : syracuseStep 709919 = 1064879) B1064879
theorem B1070459 : Blo 471786 1070459 := bstep (se 1 (by rfl) ⟨802844, by rfl⟩ : syracuseStep 1070459 = 1605689) B1605689
theorem B710087 : Blo 471786 710087 := bstep (se 1 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 710087 = 1065131) B1065131
theorem B35149463 : Blo 471786 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B710441 : Blo 471786 710441 := bstep (se 2 (by rfl) ⟨266415, by rfl⟩ : syracuseStep 710441 = 532831) B532831
theorem B808751 : Blo 471786 808751 := bstep (se 1 (by rfl) ⟨606563, by rfl⟩ : syracuseStep 808751 = 1213127) B1213127
theorem B710447 : Blo 471786 710447 := bstep (se 1 (by rfl) ⟨532835, by rfl⟩ : syracuseStep 710447 = 1065671) B1065671
theorem B17356949 : Blo 471786 17356949 := bstep (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) B813607
theorem B1595645 : Blo 471786 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B710921 : Blo 471786 710921 := bstep (se 2 (by rfl) ⟨266595, by rfl⟩ : syracuseStep 710921 = 533191) B533191
theorem B711023 : Blo 471786 711023 := bstep (se 1 (by rfl) ⟨533267, by rfl⟩ : syracuseStep 711023 = 1066535) B1066535
theorem B1366523 : Blo 471786 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B1464895 : Blo 471786 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B711239 : Blo 471786 711239 := bstep (se 1 (by rfl) ⟨533429, by rfl⟩ : syracuseStep 711239 = 1066859) B1066859
theorem B1202759 : Blo 471786 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B711275 : Blo 471786 711275 := bstep (se 1 (by rfl) ⟨533456, by rfl⟩ : syracuseStep 711275 = 1066913) B1066913
theorem B1202809 : Blo 471786 1202809 := bstep (se 2 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 1202809 = 902107) B902107
theorem B6576815 : Blo 471786 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B2284307 : Blo 471786 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B711503 : Blo 471786 711503 := bstep (se 1 (by rfl) ⟨533627, by rfl⟩ : syracuseStep 711503 = 1067255) B1067255
theorem B1596455 : Blo 471786 1596455 := bstep (se 1 (by rfl) ⟨1197341, by rfl⟩ : syracuseStep 1596455 = 2394683) B2394683
theorem B3595427 : Blo 471786 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B711899 : Blo 471786 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B712073 : Blo 471786 712073 := bstep (se 2 (by rfl) ⟨267027, by rfl⟩ : syracuseStep 712073 = 534055) B534055
theorem B1596887 : Blo 471786 1596887 := bstep (se 1 (by rfl) ⟨1197665, by rfl⟩ : syracuseStep 1596887 = 2395331) B2395331
theorem B712427 : Blo 471786 712427 := bstep (se 1 (by rfl) ⟨534320, by rfl⟩ : syracuseStep 712427 = 1068641) B1068641
theorem B18013985 : Blo 471786 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B712655 : Blo 471786 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B6086663 : Blo 471786 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B7692407 : Blo 471786 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B713051 : Blo 471786 713051 := bstep (se 1 (by rfl) ⟨534788, by rfl⟩ : syracuseStep 713051 = 1069577) B1069577
theorem B1925551 : Blo 471786 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B713279 : Blo 471786 713279 := bstep (se 1 (by rfl) ⟨534959, by rfl⟩ : syracuseStep 713279 = 1069919) B1069919
theorem B713399 : Blo 471786 713399 := bstep (se 1 (by rfl) ⟨535049, by rfl⟩ : syracuseStep 713399 = 1070099) B1070099
theorem B4842233 : Blo 471786 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B5530463 : Blo 471786 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B713627 : Blo 471786 713627 := bstep (se 1 (by rfl) ⟨535220, by rfl⟩ : syracuseStep 713627 = 1070441) B1070441
theorem B6841381 : Blo 471786 6841381 := bstep (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) B1282759
theorem B1598561 : Blo 471786 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B2057633 : Blo 471786 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B3892769 : Blo 471786 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B3597857 : Blo 471786 3597857 := bstep (se 2 (by rfl) ⟨1349196, by rfl⟩ : syracuseStep 3597857 = 2698393) B2698393
theorem B910931 : Blo 471786 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B3401605 : Blo 471786 3401605 := bstep (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) B637801
theorem B2025607 : Blo 471786 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B1796377 : Blo 471786 1796377 := bstep (se 2 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 1796377 = 1347283) B1347283
theorem B1010087 : Blo 471786 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B1599911 : Blo 471786 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B1796681 : Blo 471786 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1600073 : Blo 471786 1600073 := bstep (se 2 (by rfl) ⟨600027, by rfl⟩ : syracuseStep 1600073 = 1200055) B1200055
theorem B5106563 : Blo 471786 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B10349855 : Blo 471786 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B2026939 : Blo 471786 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B13102553 : Blo 471786 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B39415517 : Blo 471786 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B3502081 : Blo 471786 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B1601747 : Blo 471786 1601747 := bstep (se 1 (by rfl) ⟨1201310, by rfl⟩ : syracuseStep 1601747 = 2402621) B2402621
theorem B17985899 : Blo 471786 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B1798625 : Blo 471786 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B1602017 : Blo 471786 1602017 := bstep (se 2 (by rfl) ⟨600756, by rfl⟩ : syracuseStep 1602017 = 1201513) B1201513
theorem B5763565 : Blo 471786 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B1799293 : Blo 471786 1799293 := bstep (se 3 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 1799293 = 674735) B674735
theorem B2553065 : Blo 471786 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B4060439 : Blo 471786 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B2028989 : Blo 471786 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B2389661 : Blo 471786 2389661 := bstep (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) B896123
theorem B1603259 : Blo 471786 1603259 := bstep (se 1 (by rfl) ⟨1202444, by rfl⟩ : syracuseStep 1603259 = 2404889) B2404889
theorem B3602231 : Blo 471786 3602231 := bstep (se 1 (by rfl) ⟨2701673, by rfl⟩ : syracuseStep 3602231 = 5403347) B5403347
theorem B76904549 : Blo 471786 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B84408875 : Blo 471786 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B2030255 : Blo 471786 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B2390957 : Blo 471786 2390957 := bstep (se 3 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 2390957 = 896609) B896609
theorem B1670519 : Blo 471786 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B1605203 : Blo 471786 1605203 := bstep (se 1 (by rfl) ⟨1203902, by rfl⟩ : syracuseStep 1605203 = 2407805) B2407805
theorem B2031313 : Blo 471786 2031313 := bstep (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) B1523485
theorem B9207647 : Blo 471786 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B18677765 : Blo 471786 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2687255 : Blo 471786 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B1802695 : Blo 471786 1802695 := bstep (se 1 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 1802695 = 2704043) B2704043
theorem B1344367 : Blo 471786 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B1344413 : Blo 471786 1344413 := bstep (se 3 (by rfl) ⟨252077, by rfl⟩ : syracuseStep 1344413 = 504155) B504155
theorem B1442717 : Blo 471786 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B853097 : Blo 471786 853097 := bstep (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) B639823
theorem B2393711 : Blo 471786 2393711 := bstep (se 1 (by rfl) ⟨1795283, by rfl⟩ : syracuseStep 2393711 = 3590567) B3590567
theorem B1444031 : Blo 471786 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B2395169 : Blo 471786 2395169 := bstep (se 2 (by rfl) ⟨898188, by rfl⟩ : syracuseStep 2395169 = 1796377) B1796377
theorem B2690171 : Blo 471786 2690171 := bstep (se 1 (by rfl) ⟨2017628, by rfl⟩ : syracuseStep 2690171 = 4035257) B4035257
theorem B2198771 : Blo 471786 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B34639163 : Blo 471786 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B23432975 : Blo 471786 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B5410637 : Blo 471786 5410637 := bstep (se 3 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 5410637 = 2028989) B2028989
theorem B2690921 : Blo 471786 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B1445855 : Blo 471786 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B2396141 : Blo 471786 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B11571299 : Blo 471786 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B2429149 : Blo 471786 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B5378561 : Blo 471786 5378561 := bstep (se 2 (by rfl) ⟨2016960, by rfl⟩ : syracuseStep 5378561 = 4033921) B4033921
theorem B2396951 : Blo 471786 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B3937085 : Blo 471786 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B2595179 : Blo 471786 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B2398571 : Blo 471786 2398571 := bstep (se 1 (by rfl) ⟨1798928, by rfl⟩ : syracuseStep 2398571 = 3597857) B3597857
theorem B2693519 : Blo 471786 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B21142037 : Blo 471786 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B2399057 : Blo 471786 2399057 := bstep (se 2 (by rfl) ⟨899646, by rfl⟩ : syracuseStep 2399057 = 1799293) B1799293
theorem B1710953 : Blo 471786 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B41098103 : Blo 471786 41098103 := bstep (se 1 (by rfl) ⟨30823577, by rfl⟩ : syracuseStep 41098103 = 61647155) B61647155
theorem B2890667 : Blo 471786 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B531679 : Blo 471786 531679 := bstep (se 1 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 531679 = 797519) B797519
theorem B2400029 : Blo 471786 2400029 := bstep (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) B900011
theorem B5775731 : Blo 471786 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B2401487 : Blo 471786 2401487 := bstep (se 1 (by rfl) ⟨1801115, by rfl⟩ : syracuseStep 2401487 = 3602231) B3602231
theorem B3089771 : Blo 471786 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B599663 : Blo 471786 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B534127 : Blo 471786 534127 := bstep (se 1 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 534127 = 801191) B801191
theorem B599719 : Blo 471786 599719 := bstep (se 1 (by rfl) ⟨449789, by rfl⟩ : syracuseStep 599719 = 899579) B899579
theorem B56272583 : Blo 471786 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B534235 : Blo 471786 534235 := bstep (se 1 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 534235 = 801353) B801353
theorem B1353503 : Blo 471786 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B796655 : Blo 471786 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B600367 : Blo 471786 600367 := bstep (se 1 (by rfl) ⟨450275, by rfl⟩ : syracuseStep 600367 = 900551) B900551
theorem B797215 : Blo 471786 797215 := bstep (se 1 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 797215 = 1195823) B1195823
theorem B6138431 : Blo 471786 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B19376819 : Blo 471786 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B797647 : Blo 471786 797647 := bstep (se 1 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 797647 = 1196471) B1196471
theorem B896503 : Blo 471786 896503 := bstep (se 1 (by rfl) ⟨672377, by rfl⟩ : syracuseStep 896503 = 1344755) B1344755
theorem B798383 : Blo 471786 798383 := bstep (se 1 (by rfl) ⟨598787, by rfl⟩ : syracuseStep 798383 = 1197575) B1197575
theorem B896807 : Blo 471786 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B798619 : Blo 471786 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B4042669 : Blo 471786 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B3518473 : Blo 471786 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B9121841 : Blo 471786 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B799031 : Blo 471786 799031 := bstep (se 1 (by rfl) ⟨599273, by rfl⟩ : syracuseStep 799031 = 1198547) B1198547
theorem B2044327 : Blo 471786 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B1061639 : Blo 471786 1061639 := bstep (se 1 (by rfl) ⟨796229, by rfl⟩ : syracuseStep 1061639 = 1592459) B1592459
theorem B471919 : Blo 471786 471919 := bstep (se 1 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 471919 = 707879) B707879
theorem B10269605 : Blo 471786 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B471975 : Blo 471786 471975 := bstep (se 1 (by rfl) ⟨353981, by rfl⟩ : syracuseStep 471975 = 707963) B707963
theorem B472059 : Blo 471786 472059 := bstep (se 1 (by rfl) ⟨354044, by rfl⟩ : syracuseStep 472059 = 708089) B708089
theorem B472127 : Blo 471786 472127 := bstep (se 1 (by rfl) ⟨354095, by rfl⟩ : syracuseStep 472127 = 708191) B708191
theorem B799807 : Blo 471786 799807 := bstep (se 1 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 799807 = 1199711) B1199711
theorem B898121 : Blo 471786 898121 := bstep (se 2 (by rfl) ⟨336795, by rfl⟩ : syracuseStep 898121 = 673591) B673591
theorem B4535473 : Blo 471786 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B472271 : Blo 471786 472271 := bstep (se 1 (by rfl) ⟨354203, by rfl⟩ : syracuseStep 472271 = 708407) B708407
theorem B3028211 : Blo 471786 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B472475 : Blo 471786 472475 := bstep (se 1 (by rfl) ⟨354356, by rfl⟩ : syracuseStep 472475 = 708713) B708713
theorem B2700809 : Blo 471786 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B800327 : Blo 471786 800327 := bstep (se 1 (by rfl) ⟨600245, by rfl⟩ : syracuseStep 800327 = 1200491) B1200491
theorem B472687 : Blo 471786 472687 := bstep (se 1 (by rfl) ⟨354515, by rfl⟩ : syracuseStep 472687 = 709031) B709031
theorem B472743 : Blo 471786 472743 := bstep (se 1 (by rfl) ⟨354557, by rfl⟩ : syracuseStep 472743 = 709115) B709115
theorem B2569931 : Blo 471786 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B472827 : Blo 471786 472827 := bstep (se 1 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 472827 = 709241) B709241
theorem B472863 : Blo 471786 472863 := bstep (se 1 (by rfl) ⟨354647, by rfl⟩ : syracuseStep 472863 = 709295) B709295
theorem B800543 : Blo 471786 800543 := bstep (se 1 (by rfl) ⟨600407, by rfl⟩ : syracuseStep 800543 = 1200815) B1200815
theorem B6928175 : Blo 471786 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B1062719 : Blo 471786 1062719 := bstep (se 1 (by rfl) ⟨797039, by rfl⟩ : syracuseStep 1062719 = 1594079) B1594079
theorem B472895 : Blo 471786 472895 := bstep (se 1 (by rfl) ⟨354671, by rfl⟩ : syracuseStep 472895 = 709343) B709343
theorem B473071 : Blo 471786 473071 := bstep (se 1 (by rfl) ⟨354803, by rfl⟩ : syracuseStep 473071 = 709607) B709607
theorem B800759 : Blo 471786 800759 := bstep (se 1 (by rfl) ⟨600569, by rfl⟩ : syracuseStep 800759 = 1201139) B1201139
theorem B1063007 : Blo 471786 1063007 := bstep (se 1 (by rfl) ⟨797255, by rfl⟩ : syracuseStep 1063007 = 1594511) B1594511
theorem B473243 : Blo 471786 473243 := bstep (se 1 (by rfl) ⟨354932, by rfl⟩ : syracuseStep 473243 = 709865) B709865
theorem B473279 : Blo 471786 473279 := bstep (se 1 (by rfl) ⟨354959, by rfl⟩ : syracuseStep 473279 = 709919) B709919
theorem B473391 : Blo 471786 473391 := bstep (se 1 (by rfl) ⟨355043, by rfl⟩ : syracuseStep 473391 = 710087) B710087
theorem B3422537 : Blo 471786 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B473627 : Blo 471786 473627 := bstep (se 1 (by rfl) ⟨355220, by rfl⟩ : syracuseStep 473627 = 710441) B710441
theorem B539167 : Blo 471786 539167 := bstep (se 1 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 539167 = 808751) B808751
theorem B473631 : Blo 471786 473631 := bstep (se 1 (by rfl) ⟨355223, by rfl⟩ : syracuseStep 473631 = 710447) B710447
theorem B4111127 : Blo 471786 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B1063763 : Blo 471786 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B473947 : Blo 471786 473947 := bstep (se 1 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 473947 = 710921) B710921
theorem B474015 : Blo 471786 474015 := bstep (se 1 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 474015 = 711023) B711023
theorem B900065 : Blo 471786 900065 := bstep (se 2 (by rfl) ⟨337524, by rfl⟩ : syracuseStep 900065 = 675049) B675049
theorem B474159 : Blo 471786 474159 := bstep (se 1 (by rfl) ⟨355619, by rfl⟩ : syracuseStep 474159 = 711239) B711239
theorem B801839 : Blo 471786 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B474183 : Blo 471786 474183 := bstep (se 1 (by rfl) ⟨355637, by rfl⟩ : syracuseStep 474183 = 711275) B711275
theorem B801913 : Blo 471786 801913 := bstep (se 2 (by rfl) ⟨300717, by rfl⟩ : syracuseStep 801913 = 601435) B601435
theorem B1522871 : Blo 471786 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B474335 : Blo 471786 474335 := bstep (se 1 (by rfl) ⟨355751, by rfl⟩ : syracuseStep 474335 = 711503) B711503
theorem B2702585 : Blo 471786 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B10894657 : Blo 471786 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B1064303 : Blo 471786 1064303 := bstep (se 1 (by rfl) ⟨798227, by rfl⟩ : syracuseStep 1064303 = 1596455) B1596455
theorem B802217 : Blo 471786 802217 := bstep (se 2 (by rfl) ⟨300831, by rfl⟩ : syracuseStep 802217 = 601663) B601663
theorem B474599 : Blo 471786 474599 := bstep (se 1 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 474599 = 711899) B711899
theorem B507367 : Blo 471786 507367 := bstep (se 1 (by rfl) ⟨380525, by rfl⟩ : syracuseStep 507367 = 761051) B761051
theorem B474715 : Blo 471786 474715 := bstep (se 1 (by rfl) ⟨356036, by rfl⟩ : syracuseStep 474715 = 712073) B712073
theorem B1064591 : Blo 471786 1064591 := bstep (se 1 (by rfl) ⟨798443, by rfl⟩ : syracuseStep 1064591 = 1596887) B1596887
theorem B1064681 : Blo 471786 1064681 := bstep (se 2 (by rfl) ⟨399255, by rfl⟩ : syracuseStep 1064681 = 798511) B798511
theorem B474951 : Blo 471786 474951 := bstep (se 1 (by rfl) ⟨356213, by rfl⟩ : syracuseStep 474951 = 712427) B712427
theorem B12009323 : Blo 471786 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B475103 : Blo 471786 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B5128271 : Blo 471786 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B6930521 : Blo 471786 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B4571225 : Blo 471786 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B475367 : Blo 471786 475367 := bstep (se 1 (by rfl) ⟨356525, by rfl⟩ : syracuseStep 475367 = 713051) B713051
theorem B475519 : Blo 471786 475519 := bstep (se 1 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 475519 = 713279) B713279
theorem B475599 : Blo 471786 475599 := bstep (se 1 (by rfl) ⟨356699, by rfl⟩ : syracuseStep 475599 = 713399) B713399
theorem B3228155 : Blo 471786 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B3686975 : Blo 471786 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B475751 : Blo 471786 475751 := bstep (se 1 (by rfl) ⟨356813, by rfl⟩ : syracuseStep 475751 = 713627) B713627
theorem B7684753 : Blo 471786 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B1065707 : Blo 471786 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1754171 : Blo 471786 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B673391 : Blo 471786 673391 := bstep (se 1 (by rfl) ⟨505043, by rfl⟩ : syracuseStep 673391 = 1010087) B1010087
theorem B1066607 : Blo 471786 1066607 := bstep (se 1 (by rfl) ⟨799955, by rfl⟩ : syracuseStep 1066607 = 1599911) B1599911
theorem B1197787 : Blo 471786 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B1066715 : Blo 471786 1066715 := bstep (se 1 (by rfl) ⟨800036, by rfl⟩ : syracuseStep 1066715 = 1600073) B1600073
theorem B6899903 : Blo 471786 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B8735035 : Blo 471786 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B2279771 : Blo 471786 2279771 := bstep (se 1 (by rfl) ⟨1709828, by rfl⟩ : syracuseStep 2279771 = 3419657) B3419657
theorem B1067831 : Blo 471786 1067831 := bstep (se 1 (by rfl) ⟨800873, by rfl⟩ : syracuseStep 1067831 = 1601747) B1601747
theorem B1362919 : Blo 471786 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B1199083 : Blo 471786 1199083 := bstep (se 1 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 1199083 = 1798625) B1798625
theorem B1068011 : Blo 471786 1068011 := bstep (se 1 (by rfl) ⟨801008, by rfl⟩ : syracuseStep 1068011 = 1602017) B1602017
theorem B707705 : Blo 471786 707705 := bstep (se 2 (by rfl) ⟨265389, by rfl⟩ : syracuseStep 707705 = 530779) B530779
theorem B1199225 : Blo 471786 1199225 := bstep (se 2 (by rfl) ⟨449709, by rfl⟩ : syracuseStep 1199225 = 899419) B899419
theorem B707807 : Blo 471786 707807 := bstep (se 1 (by rfl) ⟨530855, by rfl⟩ : syracuseStep 707807 = 1061711) B1061711
theorem B707849 : Blo 471786 707849 := bstep (se 2 (by rfl) ⟨265443, by rfl⟩ : syracuseStep 707849 = 530887) B530887
theorem B707951 : Blo 471786 707951 := bstep (se 1 (by rfl) ⟨530963, by rfl⟩ : syracuseStep 707951 = 1061927) B1061927
theorem B1953193 : Blo 471786 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B708071 : Blo 471786 708071 := bstep (se 1 (by rfl) ⟨531053, by rfl⟩ : syracuseStep 708071 = 1062107) B1062107
theorem B2706959 : Blo 471786 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B708203 : Blo 471786 708203 := bstep (se 1 (by rfl) ⟨531152, by rfl⟩ : syracuseStep 708203 = 1062305) B1062305
theorem B708329 : Blo 471786 708329 := bstep (se 2 (by rfl) ⟨265623, by rfl⟩ : syracuseStep 708329 = 531247) B531247
theorem B1593107 : Blo 471786 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B1068839 : Blo 471786 1068839 := bstep (se 1 (by rfl) ⟨801629, by rfl⟩ : syracuseStep 1068839 = 1603259) B1603259
theorem B708473 : Blo 471786 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B708575 : Blo 471786 708575 := bstep (se 1 (by rfl) ⟨531431, by rfl⟩ : syracuseStep 708575 = 1062863) B1062863
theorem B51269699 : Blo 471786 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B708827 : Blo 471786 708827 := bstep (se 1 (by rfl) ⟨531620, by rfl⟩ : syracuseStep 708827 = 1063241) B1063241
theorem B708839 : Blo 471786 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B709001 : Blo 471786 709001 := bstep (se 2 (by rfl) ⟨265875, by rfl⟩ : syracuseStep 709001 = 531751) B531751
theorem B1200521 : Blo 471786 1200521 := bstep (se 2 (by rfl) ⟨450195, by rfl⟩ : syracuseStep 1200521 = 900391) B900391
theorem B709097 : Blo 471786 709097 := bstep (se 2 (by rfl) ⟨265911, by rfl⟩ : syracuseStep 709097 = 531823) B531823
theorem B709223 : Blo 471786 709223 := bstep (se 1 (by rfl) ⟨531917, by rfl⟩ : syracuseStep 709223 = 1063835) B1063835
theorem B1593971 : Blo 471786 1593971 := bstep (se 1 (by rfl) ⟨1195478, by rfl⟩ : syracuseStep 1593971 = 2390957) B2390957
theorem B709355 : Blo 471786 709355 := bstep (se 1 (by rfl) ⟨532016, by rfl⟩ : syracuseStep 709355 = 1064033) B1064033
theorem B709385 : Blo 471786 709385 := bstep (se 2 (by rfl) ⟨266019, by rfl⟩ : syracuseStep 709385 = 532039) B532039
theorem B1069865 : Blo 471786 1069865 := bstep (se 2 (by rfl) ⟨401199, by rfl⟩ : syracuseStep 1069865 = 802399) B802399
theorem B709487 : Blo 471786 709487 := bstep (se 1 (by rfl) ⟨532115, by rfl⟩ : syracuseStep 709487 = 1064231) B1064231
theorem B1594241 : Blo 471786 1594241 := bstep (se 2 (by rfl) ⟨597840, by rfl⟩ : syracuseStep 1594241 = 1195681) B1195681
theorem B2708417 : Blo 471786 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B1070135 : Blo 471786 1070135 := bstep (se 1 (by rfl) ⟨802601, by rfl⟩ : syracuseStep 1070135 = 1605203) B1605203
theorem B1070153 : Blo 471786 1070153 := bstep (se 2 (by rfl) ⟨401307, by rfl⟩ : syracuseStep 1070153 = 802615) B802615
theorem B709739 : Blo 471786 709739 := bstep (se 1 (by rfl) ⟨532304, by rfl⟩ : syracuseStep 709739 = 1064609) B1064609
theorem B709979 : Blo 471786 709979 := bstep (se 1 (by rfl) ⟨532484, by rfl⟩ : syracuseStep 709979 = 1064969) B1064969
theorem B6051293 : Blo 471786 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B710255 : Blo 471786 710255 := bstep (se 1 (by rfl) ⟨532691, by rfl⟩ : syracuseStep 710255 = 1065383) B1065383
theorem B1595051 : Blo 471786 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B710327 : Blo 471786 710327 := bstep (se 1 (by rfl) ⟨532745, by rfl⟩ : syracuseStep 710327 = 1065491) B1065491
theorem B710363 : Blo 471786 710363 := bstep (se 1 (by rfl) ⟨532772, by rfl⟩ : syracuseStep 710363 = 1065545) B1065545
theorem B710537 : Blo 471786 710537 := bstep (se 2 (by rfl) ⟨266451, by rfl⟩ : syracuseStep 710537 = 532903) B532903
theorem B1595375 : Blo 471786 1595375 := bstep (se 1 (by rfl) ⟨1196531, by rfl⟩ : syracuseStep 1595375 = 2393063) B2393063
theorem B710639 : Blo 471786 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B1202273 : Blo 471786 1202273 := bstep (se 2 (by rfl) ⟨450852, by rfl⟩ : syracuseStep 1202273 = 901705) B901705
theorem B1595591 : Blo 471786 1595591 := bstep (se 1 (by rfl) ⟨1196693, by rfl⟩ : syracuseStep 1595591 = 2393387) B2393387
theorem B710891 : Blo 471786 710891 := bstep (se 1 (by rfl) ⟨533168, by rfl⟩ : syracuseStep 710891 = 1066337) B1066337
theorem B47962397 : Blo 471786 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B710951 : Blo 471786 710951 := bstep (se 1 (by rfl) ⟨533213, by rfl⟩ : syracuseStep 710951 = 1066427) B1066427
theorem B1366313 : Blo 471786 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B711035 : Blo 471786 711035 := bstep (se 1 (by rfl) ⟨533276, by rfl⟩ : syracuseStep 711035 = 1066553) B1066553
theorem B711305 : Blo 471786 711305 := bstep (se 2 (by rfl) ⟨266739, by rfl⟩ : syracuseStep 711305 = 533479) B533479
theorem B711479 : Blo 471786 711479 := bstep (se 1 (by rfl) ⟨533609, by rfl⟩ : syracuseStep 711479 = 1067219) B1067219
theorem B1596239 : Blo 471786 1596239 := bstep (se 1 (by rfl) ⟨1197179, by rfl⟩ : syracuseStep 1596239 = 2394359) B2394359
theorem B711515 : Blo 471786 711515 := bstep (se 1 (by rfl) ⟨533636, by rfl⟩ : syracuseStep 711515 = 1067273) B1067273
theorem B711659 : Blo 471786 711659 := bstep (se 1 (by rfl) ⟨533744, by rfl⟩ : syracuseStep 711659 = 1067489) B1067489
theorem B1596563 : Blo 471786 1596563 := bstep (se 1 (by rfl) ⟨1197422, by rfl⟩ : syracuseStep 1596563 = 2394845) B2394845
theorem B711863 : Blo 471786 711863 := bstep (se 1 (by rfl) ⟨533897, by rfl⟩ : syracuseStep 711863 = 1067795) B1067795
theorem B4611275 : Blo 471786 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B1465559 : Blo 471786 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B1596833 : Blo 471786 1596833 := bstep (se 2 (by rfl) ⟨598812, by rfl⟩ : syracuseStep 1596833 = 1197625) B1197625
theorem B712103 : Blo 471786 712103 := bstep (se 1 (by rfl) ⟨534077, by rfl⟩ : syracuseStep 712103 = 1068155) B1068155
theorem B712187 : Blo 471786 712187 := bstep (se 1 (by rfl) ⟨534140, by rfl⟩ : syracuseStep 712187 = 1068281) B1068281
theorem B712283 : Blo 471786 712283 := bstep (se 1 (by rfl) ⟨534212, by rfl⟩ : syracuseStep 712283 = 1068425) B1068425
theorem B712367 : Blo 471786 712367 := bstep (se 1 (by rfl) ⟨534275, by rfl⟩ : syracuseStep 712367 = 1068551) B1068551
theorem B712487 : Blo 471786 712487 := bstep (se 1 (by rfl) ⟨534365, by rfl⟩ : syracuseStep 712487 = 1068731) B1068731
theorem B712571 : Blo 471786 712571 := bstep (se 1 (by rfl) ⟨534428, by rfl⟩ : syracuseStep 712571 = 1068857) B1068857
theorem B1597373 : Blo 471786 1597373 := bstep (se 3 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 1597373 = 599015) B599015
theorem B1728647 : Blo 471786 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B2023643 : Blo 471786 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B712991 : Blo 471786 712991 := bstep (se 1 (by rfl) ⟨534743, by rfl⟩ : syracuseStep 712991 = 1069487) B1069487
theorem B713015 : Blo 471786 713015 := bstep (se 1 (by rfl) ⟨534761, by rfl⟩ : syracuseStep 713015 = 1069523) B1069523
theorem B2285921 : Blo 471786 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B713087 : Blo 471786 713087 := bstep (se 1 (by rfl) ⟨534815, by rfl⟩ : syracuseStep 713087 = 1069631) B1069631
theorem B713159 : Blo 471786 713159 := bstep (se 1 (by rfl) ⟨534869, by rfl⟩ : syracuseStep 713159 = 1069739) B1069739
theorem B43803287 : Blo 471786 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B713513 : Blo 471786 713513 := bstep (se 2 (by rfl) ⟨267567, by rfl⟩ : syracuseStep 713513 = 535135) B535135
theorem B713519 : Blo 471786 713519 := bstep (se 1 (by rfl) ⟨535139, by rfl⟩ : syracuseStep 713519 = 1070279) B1070279
theorem B713639 : Blo 471786 713639 := bstep (se 1 (by rfl) ⟨535229, by rfl⟩ : syracuseStep 713639 = 1070459) B1070459
theorem B1926737 : Blo 471786 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B11495009 : Blo 471786 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B911015 : Blo 471786 911015 := bstep (se 1 (by rfl) ⟨683261, by rfl⟩ : syracuseStep 911015 = 1366523) B1366523
theorem B1599263 : Blo 471786 1599263 := bstep (se 1 (by rfl) ⟨1199447, by rfl⟩ : syracuseStep 1599263 = 2398895) B2398895
theorem B4384543 : Blo 471786 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B1599479 : Blo 471786 1599479 := bstep (se 1 (by rfl) ⟨1199609, by rfl⟩ : syracuseStep 1599479 = 2399219) B2399219
theorem B1010207 : Blo 471786 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B4057775 : Blo 471786 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1600343 : Blo 471786 1600343 := bstep (se 1 (by rfl) ⟨1200257, by rfl⟩ : syracuseStep 1600343 = 2400515) B2400515
theorem B1797167 : Blo 471786 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1600559 : Blo 471786 1600559 := bstep (se 1 (by rfl) ⟨1200419, by rfl⟩ : syracuseStep 1600559 = 2400839) B2400839
theorem B1076345 : Blo 471786 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B1600937 : Blo 471786 1600937 := bstep (se 2 (by rfl) ⟨600351, by rfl⟩ : syracuseStep 1600937 = 1200703) B1200703
theorem B1797623 : Blo 471786 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B1371755 : Blo 471786 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B1601423 : Blo 471786 1601423 := bstep (se 1 (by rfl) ⟨1201067, by rfl⟩ : syracuseStep 1601423 = 2402135) B2402135
theorem B1601801 : Blo 471786 1601801 := bstep (se 2 (by rfl) ⟨600675, by rfl⟩ : syracuseStep 1601801 = 1201351) B1201351
theorem B4551079 : Blo 471786 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B3404375 : Blo 471786 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B4551389 : Blo 471786 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B26277011 : Blo 471786 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B1602935 : Blo 471786 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B20739629 : Blo 471786 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B2389823 : Blo 471786 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B4323149 : Blo 471786 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B23000921 : Blo 471786 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B1013735 : Blo 471786 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1013743 : Blo 471786 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B1800251 : Blo 471786 1800251 := bstep (se 1 (by rfl) ⟨1350188, by rfl⟩ : syracuseStep 1800251 = 2700377) B2700377
theorem B2029673 : Blo 471786 2029673 := bstep (se 2 (by rfl) ⟨761127, by rfl⟩ : syracuseStep 2029673 = 1522255) B1522255
theorem B1702043 : Blo 471786 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B1603745 : Blo 471786 1603745 := bstep (se 2 (by rfl) ⟨601404, by rfl⟩ : syracuseStep 1603745 = 1202809) B1202809
theorem B4061501 : Blo 471786 4061501 := bstep (se 3 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 4061501 = 1523063) B1523063
theorem B1210747 : Blo 471786 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B1604015 : Blo 471786 1604015 := bstep (se 1 (by rfl) ⟨1203011, by rfl⟩ : syracuseStep 1604015 = 2406023) B2406023
theorem B1538713 : Blo 471786 1538713 := bstep (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) B1154035
theorem B1801511 : Blo 471786 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B1605095 : Blo 471786 1605095 := bstep (se 1 (by rfl) ⟨1203821, by rfl⟩ : syracuseStep 1605095 = 2407643) B2407643
theorem B1113679 : Blo 471786 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B12451843 : Blo 471786 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B4620347 : Blo 471786 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B3047483 : Blo 471786 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2457983 : Blo 471786 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B1804639 : Blo 471786 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B3607091 : Blo 471786 3607091 := bstep (se 1 (by rfl) ⟨2705318, by rfl⟩ : syracuseStep 3607091 = 5410637) B5410637
theorem B2624723 : Blo 471786 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B1805611 : Blo 471786 1805611 := bstep (se 1 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 1805611 = 2708417) B2708417
theorem B4034195 : Blo 471786 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B14094691 : Blo 471786 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B27398735 : Blo 471786 27398735 := bstep (se 1 (by rfl) ⟨20549051, by rfl⟩ : syracuseStep 27398735 = 41098103) B41098103
theorem B4691297 : Blo 471786 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B1152431 : Blo 471786 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1349095 : Blo 471786 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B29202191 : Blo 471786 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B2725769 : Blo 471786 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B6068105 : Blo 471786 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B3643501 : Blo 471786 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B1284491 : Blo 471786 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B531103 : Blo 471786 531103 := bstep (se 1 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 531103 = 796655) B796655
theorem B12917879 : Blo 471786 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B532255 : Blo 471786 532255 := bstep (se 1 (by rfl) ⟨399191, by rfl⟩ : syracuseStep 532255 = 798383) B798383
theorem B597871 : Blo 471786 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B1351657 : Blo 471786 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B532687 : Blo 471786 532687 := bstep (se 1 (by rfl) ⟨399515, by rfl⟩ : syracuseStep 532687 = 799031) B799031
theorem B2269583 : Blo 471786 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B1614329 : Blo 471786 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B598747 : Blo 471786 598747 := bstep (se 1 (by rfl) ⟨449060, by rfl⟩ : syracuseStep 598747 = 898121) B898121
theorem B533551 : Blo 471786 533551 := bstep (se 1 (by rfl) ⟨400163, by rfl⟩ : syracuseStep 533551 = 800327) B800327
theorem B1713287 : Blo 471786 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B533695 : Blo 471786 533695 := bstep (se 1 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 533695 = 800543) B800543
theorem B533839 : Blo 471786 533839 := bstep (se 1 (by rfl) ⟨400379, by rfl⟩ : syracuseStep 533839 = 800759) B800759
theorem B1353115 : Blo 471786 1353115 := bstep (se 1 (by rfl) ⟨1014836, by rfl⟩ : syracuseStep 1353115 = 2029673) B2029673
theorem B14526209 : Blo 471786 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B600043 : Blo 471786 600043 := bstep (se 1 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 600043 = 900065) B900065
theorem B534559 : Blo 471786 534559 := bstep (se 1 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 534559 = 801839) B801839
theorem B1484905 : Blo 471786 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B534811 : Blo 471786 534811 := bstep (se 1 (by rfl) ⟨401108, by rfl⟩ : syracuseStep 534811 = 802217) B802217
theorem B8006215 : Blo 471786 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B3418847 : Blo 471786 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B136719197 : Blo 471786 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B2403593 : Blo 471786 2403593 := bstep (se 2 (by rfl) ⟨901347, by rfl⟩ : syracuseStep 2403593 = 1802695) B1802695
theorem B896275 : Blo 471786 896275 := bstep (se 1 (by rfl) ⟨672206, by rfl⟩ : syracuseStep 896275 = 1344413) B1344413
theorem B961811 : Blo 471786 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B4599935 : Blo 471786 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B962687 : Blo 471786 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B1519847 : Blo 471786 1519847 := bstep (se 1 (by rfl) ⟨1139885, by rfl⟩ : syracuseStep 1519847 = 2279771) B2279771
theorem B471803 : Blo 471786 471803 := bstep (se 1 (by rfl) ⟨353852, by rfl⟩ : syracuseStep 471803 = 707705) B707705
theorem B799483 : Blo 471786 799483 := bstep (se 1 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 799483 = 1199225) B1199225
theorem B471871 : Blo 471786 471871 := bstep (se 1 (by rfl) ⟨353903, by rfl⟩ : syracuseStep 471871 = 707807) B707807
theorem B471899 : Blo 471786 471899 := bstep (se 1 (by rfl) ⟨353924, by rfl⟩ : syracuseStep 471899 = 707849) B707849
theorem B799625 : Blo 471786 799625 := bstep (se 2 (by rfl) ⟨299859, by rfl⟩ : syracuseStep 799625 = 599719) B599719
theorem B471967 : Blo 471786 471967 := bstep (se 1 (by rfl) ⟨353975, by rfl⟩ : syracuseStep 471967 = 707951) B707951
theorem B472047 : Blo 471786 472047 := bstep (se 1 (by rfl) ⟨354035, by rfl⟩ : syracuseStep 472047 = 708071) B708071
theorem B5846057 : Blo 471786 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B472135 : Blo 471786 472135 := bstep (se 1 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 472135 = 708203) B708203
theorem B472219 : Blo 471786 472219 := bstep (se 1 (by rfl) ⟨354164, by rfl⟩ : syracuseStep 472219 = 708329) B708329
theorem B1062071 : Blo 471786 1062071 := bstep (se 1 (by rfl) ⟨796553, by rfl⟩ : syracuseStep 1062071 = 1593107) B1593107
theorem B472315 : Blo 471786 472315 := bstep (se 1 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 472315 = 708473) B708473
theorem B472383 : Blo 471786 472383 := bstep (se 1 (by rfl) ⟨354287, by rfl⟩ : syracuseStep 472383 = 708575) B708575
theorem B7714199 : Blo 471786 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B472551 : Blo 471786 472551 := bstep (se 1 (by rfl) ⟨354413, by rfl⟩ : syracuseStep 472551 = 708827) B708827
theorem B472559 : Blo 471786 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B472667 : Blo 471786 472667 := bstep (se 1 (by rfl) ⟨354500, by rfl⟩ : syracuseStep 472667 = 709001) B709001
theorem B800347 : Blo 471786 800347 := bstep (se 1 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 800347 = 1200521) B1200521
theorem B2274925 : Blo 471786 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B472731 : Blo 471786 472731 := bstep (se 1 (by rfl) ⟨354548, by rfl⟩ : syracuseStep 472731 = 709097) B709097
theorem B3585707 : Blo 471786 3585707 := bstep (se 1 (by rfl) ⟨2689280, by rfl⟩ : syracuseStep 3585707 = 5378561) B5378561
theorem B800489 : Blo 471786 800489 := bstep (se 2 (by rfl) ⟨300183, by rfl⟩ : syracuseStep 800489 = 600367) B600367
theorem B472815 : Blo 471786 472815 := bstep (se 1 (by rfl) ⟨354611, by rfl⟩ : syracuseStep 472815 = 709223) B709223
theorem B1062647 : Blo 471786 1062647 := bstep (se 1 (by rfl) ⟨796985, by rfl⟩ : syracuseStep 1062647 = 1593971) B1593971
theorem B11646713 : Blo 471786 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B472903 : Blo 471786 472903 := bstep (se 1 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 472903 = 709355) B709355
theorem B472923 : Blo 471786 472923 := bstep (se 1 (by rfl) ⟨354692, by rfl⟩ : syracuseStep 472923 = 709385) B709385
theorem B472991 : Blo 471786 472991 := bstep (se 1 (by rfl) ⟨354743, by rfl⟩ : syracuseStep 472991 = 709487) B709487
theorem B1062827 : Blo 471786 1062827 := bstep (se 1 (by rfl) ⟨797120, by rfl⟩ : syracuseStep 1062827 = 1594241) B1594241
theorem B1062953 : Blo 471786 1062953 := bstep (se 2 (by rfl) ⟨398607, by rfl⟩ : syracuseStep 1062953 = 797215) B797215
theorem B473159 : Blo 471786 473159 := bstep (se 1 (by rfl) ⟨354869, by rfl⟩ : syracuseStep 473159 = 709739) B709739
theorem B473319 : Blo 471786 473319 := bstep (se 1 (by rfl) ⟨354989, by rfl⟩ : syracuseStep 473319 = 709979) B709979
theorem B473503 : Blo 471786 473503 := bstep (se 1 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 473503 = 710255) B710255
theorem B1063367 : Blo 471786 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B473551 : Blo 471786 473551 := bstep (se 1 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 473551 = 710327) B710327
theorem B473575 : Blo 471786 473575 := bstep (se 1 (by rfl) ⟨355181, by rfl⟩ : syracuseStep 473575 = 710363) B710363
theorem B473691 : Blo 471786 473691 := bstep (se 1 (by rfl) ⟨355268, by rfl⟩ : syracuseStep 473691 = 710537) B710537
theorem B1063529 : Blo 471786 1063529 := bstep (se 2 (by rfl) ⟨398823, by rfl⟩ : syracuseStep 1063529 = 797647) B797647
theorem B1817225 : Blo 471786 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B1063583 : Blo 471786 1063583 := bstep (se 1 (by rfl) ⟨797687, by rfl⟩ : syracuseStep 1063583 = 1595375) B1595375
theorem B473759 : Blo 471786 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B801515 : Blo 471786 801515 := bstep (se 1 (by rfl) ⟨601136, by rfl⟩ : syracuseStep 801515 = 1202273) B1202273
theorem B1063727 : Blo 471786 1063727 := bstep (se 1 (by rfl) ⟨797795, by rfl⟩ : syracuseStep 1063727 = 1595591) B1595591
theorem B473927 : Blo 471786 473927 := bstep (se 1 (by rfl) ⟨355445, by rfl⟩ : syracuseStep 473927 = 710891) B710891
theorem B473967 : Blo 471786 473967 := bstep (se 1 (by rfl) ⟨355475, by rfl⟩ : syracuseStep 473967 = 710951) B710951
theorem B474023 : Blo 471786 474023 := bstep (se 1 (by rfl) ⟨355517, by rfl⟩ : syracuseStep 474023 = 711035) B711035
theorem B474203 : Blo 471786 474203 := bstep (se 1 (by rfl) ⟨355652, by rfl⟩ : syracuseStep 474203 = 711305) B711305
theorem B150060221 : Blo 471786 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B474319 : Blo 471786 474319 := bstep (se 1 (by rfl) ⟨355739, by rfl⟩ : syracuseStep 474319 = 711479) B711479
theorem B1064159 : Blo 471786 1064159 := bstep (se 1 (by rfl) ⟨798119, by rfl⟩ : syracuseStep 1064159 = 1596239) B1596239
theorem B2604257 : Blo 471786 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B474343 : Blo 471786 474343 := bstep (se 1 (by rfl) ⟨355757, by rfl⟩ : syracuseStep 474343 = 711515) B711515
theorem B474439 : Blo 471786 474439 := bstep (se 1 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 474439 = 711659) B711659
theorem B1195337 : Blo 471786 1195337 := bstep (se 2 (by rfl) ⟨448251, by rfl⟩ : syracuseStep 1195337 = 896503) B896503
theorem B1064375 : Blo 471786 1064375 := bstep (se 1 (by rfl) ⟨798281, by rfl⟩ : syracuseStep 1064375 = 1596563) B1596563
theorem B474575 : Blo 471786 474575 := bstep (se 1 (by rfl) ⟨355931, by rfl⟩ : syracuseStep 474575 = 711863) B711863
theorem B1064555 : Blo 471786 1064555 := bstep (se 1 (by rfl) ⟨798416, by rfl⟩ : syracuseStep 1064555 = 1596833) B1596833
theorem B474735 : Blo 471786 474735 := bstep (se 1 (by rfl) ⟨356051, by rfl⟩ : syracuseStep 474735 = 712103) B712103
theorem B474791 : Blo 471786 474791 := bstep (se 1 (by rfl) ⟨356093, by rfl⟩ : syracuseStep 474791 = 712187) B712187
theorem B474855 : Blo 471786 474855 := bstep (se 1 (by rfl) ⟨356141, by rfl⟩ : syracuseStep 474855 = 712283) B712283
theorem B474911 : Blo 471786 474911 := bstep (se 1 (by rfl) ⟨356183, by rfl⟩ : syracuseStep 474911 = 712367) B712367
theorem B474991 : Blo 471786 474991 := bstep (se 1 (by rfl) ⟨356243, by rfl⟩ : syracuseStep 474991 = 712487) B712487
theorem B1064825 : Blo 471786 1064825 := bstep (se 2 (by rfl) ⟨399309, by rfl⟩ : syracuseStep 1064825 = 798619) B798619
theorem B5390225 : Blo 471786 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B475047 : Blo 471786 475047 := bstep (se 1 (by rfl) ⟨356285, by rfl⟩ : syracuseStep 475047 = 712571) B712571
theorem B2703293 : Blo 471786 2703293 := bstep (se 3 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 2703293 = 1013735) B1013735
theorem B1064915 : Blo 471786 1064915 := bstep (se 1 (by rfl) ⟨798686, by rfl⟩ : syracuseStep 1064915 = 1597373) B1597373
theorem B475327 : Blo 471786 475327 := bstep (se 1 (by rfl) ⟨356495, by rfl⟩ : syracuseStep 475327 = 712991) B712991
theorem B475343 : Blo 471786 475343 := bstep (se 1 (by rfl) ⟨356507, by rfl⟩ : syracuseStep 475343 = 713015) B713015
theorem B1523947 : Blo 471786 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B3850487 : Blo 471786 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B475391 : Blo 471786 475391 := bstep (se 1 (by rfl) ⟨356543, by rfl⟩ : syracuseStep 475391 = 713087) B713087
theorem B475439 : Blo 471786 475439 := bstep (se 1 (by rfl) ⟨356579, by rfl⟩ : syracuseStep 475439 = 713159) B713159
theorem B475675 : Blo 471786 475675 := bstep (se 1 (by rfl) ⟨356756, by rfl⟩ : syracuseStep 475675 = 713513) B713513
theorem B475679 : Blo 471786 475679 := bstep (se 1 (by rfl) ⟨356759, by rfl⟩ : syracuseStep 475679 = 713519) B713519
theorem B475759 : Blo 471786 475759 := bstep (se 1 (by rfl) ⟨356819, by rfl⟩ : syracuseStep 475759 = 713639) B713639
theorem B607343 : Blo 471786 607343 := bstep (se 1 (by rfl) ⟨455507, by rfl⟩ : syracuseStep 607343 = 911015) B911015
theorem B1066175 : Blo 471786 1066175 := bstep (se 1 (by rfl) ⟨799631, by rfl⟩ : syracuseStep 1066175 = 1599263) B1599263
theorem B902335 : Blo 471786 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B1066319 : Blo 471786 1066319 := bstep (se 1 (by rfl) ⟨799739, by rfl⟩ : syracuseStep 1066319 = 1599479) B1599479
theorem B1066409 : Blo 471786 1066409 := bstep (se 2 (by rfl) ⟨399903, by rfl⟩ : syracuseStep 1066409 = 799807) B799807
theorem B6047297 : Blo 471786 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B673471 : Blo 471786 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B2705183 : Blo 471786 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B1066895 : Blo 471786 1066895 := bstep (se 1 (by rfl) ⟨800171, by rfl⟩ : syracuseStep 1066895 = 1600343) B1600343
theorem B1198111 : Blo 471786 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B1067039 : Blo 471786 1067039 := bstep (se 1 (by rfl) ⟨800279, by rfl⟩ : syracuseStep 1067039 = 1600559) B1600559
theorem B1067291 : Blo 471786 1067291 := bstep (se 1 (by rfl) ⟨800468, by rfl⟩ : syracuseStep 1067291 = 1600937) B1600937
theorem B1198415 : Blo 471786 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B2705957 : Blo 471786 2705957 := bstep (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) B507367
theorem B1067615 : Blo 471786 1067615 := bstep (se 1 (by rfl) ⟨800711, by rfl⟩ : syracuseStep 1067615 = 1601423) B1601423
theorem B6081227 : Blo 471786 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B1067867 : Blo 471786 1067867 := bstep (se 1 (by rfl) ⟨800900, by rfl⟩ : syracuseStep 1067867 = 1601801) B1601801
theorem B3034259 : Blo 471786 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B707759 : Blo 471786 707759 := bstep (se 1 (by rfl) ⟨530819, by rfl⟩ : syracuseStep 707759 = 1061639) B1061639
theorem B17518007 : Blo 471786 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B2018807 : Blo 471786 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B2051617 : Blo 471786 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B1068623 : Blo 471786 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1593215 : Blo 471786 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B708479 : Blo 471786 708479 := bstep (se 1 (by rfl) ⟨531359, by rfl⟩ : syracuseStep 708479 = 1062719) B1062719
theorem B1200167 : Blo 471786 1200167 := bstep (se 1 (by rfl) ⟨900125, by rfl⟩ : syracuseStep 1200167 = 1800251) B1800251
theorem B708671 : Blo 471786 708671 := bstep (se 1 (by rfl) ⟨531503, by rfl⟩ : syracuseStep 708671 = 1063007) B1063007
theorem B1134695 : Blo 471786 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1069163 : Blo 471786 1069163 := bstep (se 1 (by rfl) ⟨801872, by rfl⟩ : syracuseStep 1069163 = 1603745) B1603745
theorem B1069217 : Blo 471786 1069217 := bstep (se 2 (by rfl) ⟨400956, by rfl⟩ : syracuseStep 1069217 = 801913) B801913
theorem B2707667 : Blo 471786 2707667 := bstep (se 1 (by rfl) ⟨2030750, by rfl⟩ : syracuseStep 2707667 = 4061501) B4061501
theorem B2281691 : Blo 471786 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B1069343 : Blo 471786 1069343 := bstep (se 1 (by rfl) ⟨802007, by rfl⟩ : syracuseStep 1069343 = 1604015) B1604015
theorem B708905 : Blo 471786 708905 := bstep (se 2 (by rfl) ⟨265839, by rfl⟩ : syracuseStep 708905 = 531679) B531679
theorem B2740751 : Blo 471786 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B709175 : Blo 471786 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B1201007 : Blo 471786 1201007 := bstep (se 1 (by rfl) ⟨900755, by rfl⟩ : syracuseStep 1201007 = 1801511) B1801511
theorem B709535 : Blo 471786 709535 := bstep (se 1 (by rfl) ⟨532151, by rfl⟩ : syracuseStep 709535 = 1064303) B1064303
theorem B1070063 : Blo 471786 1070063 := bstep (se 1 (by rfl) ⟨802547, by rfl⟩ : syracuseStep 1070063 = 1605095) B1605095
theorem B709727 : Blo 471786 709727 := bstep (se 1 (by rfl) ⟨532295, by rfl⟩ : syracuseStep 709727 = 1064591) B1064591
theorem B709787 : Blo 471786 709787 := bstep (se 1 (by rfl) ⟨532340, by rfl⟩ : syracuseStep 709787 = 1064681) B1064681
theorem B3855613 : Blo 471786 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B1791503 : Blo 471786 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B2152103 : Blo 471786 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B710471 : Blo 471786 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B1169447 : Blo 471786 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B10246337 : Blo 471786 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B1595807 : Blo 471786 1595807 := bstep (se 1 (by rfl) ⟨1196855, by rfl⟩ : syracuseStep 1595807 = 2393711) B2393711
theorem B711071 : Blo 471786 711071 := bstep (se 1 (by rfl) ⟨533303, by rfl⟩ : syracuseStep 711071 = 1066607) B1066607
theorem B711143 : Blo 471786 711143 := bstep (se 1 (by rfl) ⟨533357, by rfl⟩ : syracuseStep 711143 = 1066715) B1066715
theorem B1792489 : Blo 471786 1792489 := bstep (se 2 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 1792489 = 1344367) B1344367
theorem B711887 : Blo 471786 711887 := bstep (se 1 (by rfl) ⟨533915, by rfl⟩ : syracuseStep 711887 = 1067831) B1067831
theorem B712007 : Blo 471786 712007 := bstep (se 1 (by rfl) ⟨534005, by rfl⟩ : syracuseStep 712007 = 1068011) B1068011
theorem B1596779 : Blo 471786 1596779 := bstep (se 1 (by rfl) ⟨1197584, by rfl⟩ : syracuseStep 1596779 = 2395169) B2395169
theorem B1793447 : Blo 471786 1793447 := bstep (se 1 (by rfl) ⟨1345085, by rfl⟩ : syracuseStep 1793447 = 2690171) B2690171
theorem B712169 : Blo 471786 712169 := bstep (se 2 (by rfl) ⟨267063, by rfl⟩ : syracuseStep 712169 = 534127) B534127
theorem B1465847 : Blo 471786 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B23092775 : Blo 471786 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B1597049 : Blo 471786 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B712313 : Blo 471786 712313 := bstep (se 2 (by rfl) ⟨267117, by rfl⟩ : syracuseStep 712313 = 534235) B534235
theorem B15621983 : Blo 471786 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B712559 : Blo 471786 712559 := bstep (se 1 (by rfl) ⟨534419, by rfl⟩ : syracuseStep 712559 = 1068839) B1068839
theorem B1793947 : Blo 471786 1793947 := bstep (se 1 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 1793947 = 2690921) B2690921
theorem B1597427 : Blo 471786 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1597967 : Blo 471786 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B713243 : Blo 471786 713243 := bstep (se 1 (by rfl) ⟨534932, by rfl⟩ : syracuseStep 713243 = 1069865) B1069865
theorem B713423 : Blo 471786 713423 := bstep (se 1 (by rfl) ⟨535067, by rfl⟩ : syracuseStep 713423 = 1070135) B1070135
theorem B713435 : Blo 471786 713435 := bstep (se 1 (by rfl) ⟨535076, by rfl⟩ : syracuseStep 713435 = 1070153) B1070153
theorem B1598777 : Blo 471786 1598777 := bstep (se 2 (by rfl) ⟨599541, by rfl⟩ : syracuseStep 1598777 = 1199083) B1199083
theorem B31974931 : Blo 471786 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B1730119 : Blo 471786 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B1599047 : Blo 471786 1599047 := bstep (se 1 (by rfl) ⟨1199285, by rfl⟩ : syracuseStep 1599047 = 2398571) B2398571
theorem B1795679 : Blo 471786 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B1795709 : Blo 471786 1795709 := bstep (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) B673391
theorem B1599101 : Blo 471786 1599101 := bstep (se 3 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 1599101 = 599663) B599663
theorem B1599371 : Blo 471786 1599371 := bstep (se 1 (by rfl) ⟨1199528, by rfl⟩ : syracuseStep 1599371 = 2399057) B2399057
theorem B1140635 : Blo 471786 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1927111 : Blo 471786 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B3074183 : Blo 471786 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B977039 : Blo 471786 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B1600019 : Blo 471786 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B3238865 : Blo 471786 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B1600991 : Blo 471786 1600991 := bstep (se 1 (by rfl) ⟨1200743, by rfl⟩ : syracuseStep 1600991 = 2401487) B2401487
theorem B2059847 : Blo 471786 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B7663339 : Blo 471786 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B4092287 : Blo 471786 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B717563 : Blo 471786 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B914503 : Blo 471786 914503 := bstep (se 1 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 914503 = 1371755) B1371755
theorem B6846403 : Blo 471786 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B718889 : Blo 471786 718889 := bstep (se 2 (by rfl) ⟨269583, by rfl⟩ : syracuseStep 718889 = 539167) B539167
theorem B1800539 : Blo 471786 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B13826419 : Blo 471786 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B4618783 : Blo 471786 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B2882099 : Blo 471786 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B15333947 : Blo 471786 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B1015247 : Blo 471786 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B1801723 : Blo 471786 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B3080231 : Blo 471786 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B2031655 : Blo 471786 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B2031929 : Blo 471786 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B6554621 : Blo 471786 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B10912765 : Blo 471786 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B4031531 : Blo 471786 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B1803455 : Blo 471786 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B1803971 : Blo 471786 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B75171685 : Blo 471786 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B1804153 : Blo 471786 1804153 := bstep (se 2 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 1804153 = 1353115) B1353115
theorem B1345871 : Blo 471786 1345871 := bstep (se 1 (by rfl) ⟨1009403, by rfl⟩ : syracuseStep 1345871 = 2018807) B2018807
theorem B2689463 : Blo 471786 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B756463 : Blo 471786 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B1805111 : Blo 471786 1805111 := bstep (se 1 (by rfl) ⟨1353833, by rfl⟩ : syracuseStep 1805111 = 2707667) B2707667
theorem B19468127 : Blo 471786 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B856327 : Blo 471786 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B5738941 : Blo 471786 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B29234677 : Blo 471786 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B1513055 : Blo 471786 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B760423 : Blo 471786 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B1219337 : Blo 471786 1219337 := bstep (se 2 (by rfl) ⟨457251, by rfl⟩ : syracuseStep 1219337 = 914503) B914503
theorem B170532965 : Blo 471786 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B4858001 : Blo 471786 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B533083 : Blo 471786 533083 := bstep (se 1 (by rfl) ⟨399812, by rfl⟩ : syracuseStep 533083 = 799625) B799625
theorem B533659 : Blo 471786 533659 := bstep (se 1 (by rfl) ⟨400244, by rfl⟩ : syracuseStep 533659 = 800489) B800489
theorem B534343 : Blo 471786 534343 := bstep (se 1 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 534343 = 801515) B801515
theorem B2402297 : Blo 471786 2402297 := bstep (se 2 (by rfl) ⟨900861, by rfl⟩ : syracuseStep 2402297 = 1801723) B1801723
theorem B796891 : Blo 471786 796891 := bstep (se 1 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 796891 = 1195337) B1195337
theorem B797161 : Blo 471786 797161 := bstep (se 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) B597871
theorem B2566991 : Blo 471786 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B798329 : Blo 471786 798329 := bstep (se 2 (by rfl) ⟨299373, by rfl⟩ : syracuseStep 798329 = 598747) B598747
theorem B798943 : Blo 471786 798943 := bstep (se 1 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 798943 = 1198415) B1198415
theorem B2404727 : Blo 471786 2404727 := bstep (se 1 (by rfl) ⟨1803545, by rfl⟩ : syracuseStep 2404727 = 3607091) B3607091
theorem B73740901 : Blo 471786 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B2306825 : Blo 471786 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B471839 : Blo 471786 471839 := bstep (se 1 (by rfl) ⟨353879, by rfl⟩ : syracuseStep 471839 = 707759) B707759
theorem B1749815 : Blo 471786 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B897961 : Blo 471786 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B11678671 : Blo 471786 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B1062143 : Blo 471786 1062143 := bstep (se 1 (by rfl) ⟨796607, by rfl⟩ : syracuseStep 1062143 = 1593215) B1593215
theorem B472319 : Blo 471786 472319 := bstep (se 1 (by rfl) ⟨354239, by rfl⟩ : syracuseStep 472319 = 708479) B708479
theorem B2569481 : Blo 471786 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B800057 : Blo 471786 800057 := bstep (se 2 (by rfl) ⟨300021, by rfl⟩ : syracuseStep 800057 = 600043) B600043
theorem B800111 : Blo 471786 800111 := bstep (se 1 (by rfl) ⟨600083, by rfl⟩ : syracuseStep 800111 = 1200167) B1200167
theorem B472447 : Blo 471786 472447 := bstep (se 1 (by rfl) ⟨354335, by rfl⟩ : syracuseStep 472447 = 708671) B708671
theorem B1979873 : Blo 471786 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B1521127 : Blo 471786 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B472603 : Blo 471786 472603 := bstep (se 1 (by rfl) ⟨354452, by rfl⟩ : syracuseStep 472603 = 708905) B708905
theorem B1619581 : Blo 471786 1619581 := bstep (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) B607343
theorem B472783 : Blo 471786 472783 := bstep (se 1 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 472783 = 709175) B709175
theorem B18265823 : Blo 471786 18265823 := bstep (se 1 (by rfl) ⟨13699367, by rfl⟩ : syracuseStep 18265823 = 27398735) B27398735
theorem B2406185 : Blo 471786 2406185 := bstep (se 2 (by rfl) ⟨902319, by rfl⟩ : syracuseStep 2406185 = 1804639) B1804639
theorem B800671 : Blo 471786 800671 := bstep (se 1 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 800671 = 1201007) B1201007
theorem B473023 : Blo 471786 473023 := bstep (se 1 (by rfl) ⟨354767, by rfl⟩ : syracuseStep 473023 = 709535) B709535
theorem B473151 : Blo 471786 473151 := bstep (se 1 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 473151 = 709727) B709727
theorem B473191 : Blo 471786 473191 := bstep (se 1 (by rfl) ⟨354893, by rfl⟩ : syracuseStep 473191 = 709787) B709787
theorem B3127531 : Blo 471786 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B768287 : Blo 471786 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B1194335 : Blo 471786 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B473647 : Blo 471786 473647 := bstep (se 1 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 473647 = 710471) B710471
theorem B4045403 : Blo 471786 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B6830891 : Blo 471786 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B1063871 : Blo 471786 1063871 := bstep (se 1 (by rfl) ⟨797903, by rfl⟩ : syracuseStep 1063871 = 1595807) B1595807
theorem B474047 : Blo 471786 474047 := bstep (se 1 (by rfl) ⟨355535, by rfl⟩ : syracuseStep 474047 = 711071) B711071
theorem B474095 : Blo 471786 474095 := bstep (se 1 (by rfl) ⟨355571, by rfl⟩ : syracuseStep 474095 = 711143) B711143
theorem B1195033 : Blo 471786 1195033 := bstep (se 2 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 1195033 = 896275) B896275
theorem B2407481 : Blo 471786 2407481 := bstep (se 2 (by rfl) ⟨902805, by rfl⟩ : syracuseStep 2407481 = 1805611) B1805611
theorem B2735489 : Blo 471786 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B474591 : Blo 471786 474591 := bstep (se 1 (by rfl) ⟨355943, by rfl⟩ : syracuseStep 474591 = 711887) B711887
theorem B474671 : Blo 471786 474671 := bstep (se 1 (by rfl) ⟨356003, by rfl⟩ : syracuseStep 474671 = 712007) B712007
theorem B1064519 : Blo 471786 1064519 := bstep (se 1 (by rfl) ⟨798389, by rfl⟩ : syracuseStep 1064519 = 1596779) B1596779
theorem B1195631 : Blo 471786 1195631 := bstep (se 1 (by rfl) ⟨896723, by rfl⟩ : syracuseStep 1195631 = 1793447) B1793447
theorem B474779 : Blo 471786 474779 := bstep (se 1 (by rfl) ⟨356084, by rfl⟩ : syracuseStep 474779 = 712169) B712169
theorem B1064699 : Blo 471786 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B474875 : Blo 471786 474875 := bstep (se 1 (by rfl) ⟨356156, by rfl⟩ : syracuseStep 474875 = 712313) B712313
theorem B475039 : Blo 471786 475039 := bstep (se 1 (by rfl) ⟨356279, by rfl⟩ : syracuseStep 475039 = 712559) B712559
theorem B1064951 : Blo 471786 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B1917037 : Blo 471786 1917037 := bstep (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) B718889
theorem B1065311 : Blo 471786 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B475495 : Blo 471786 475495 := bstep (se 1 (by rfl) ⟨356621, by rfl⟩ : syracuseStep 475495 = 713243) B713243
theorem B475615 : Blo 471786 475615 := bstep (se 1 (by rfl) ⟨356711, by rfl⟩ : syracuseStep 475615 = 713423) B713423
theorem B475623 : Blo 471786 475623 := bstep (se 1 (by rfl) ⟨356717, by rfl⟩ : syracuseStep 475623 = 713435) B713435
theorem B1065851 : Blo 471786 1065851 := bstep (se 1 (by rfl) ⟨799388, by rfl⟩ : syracuseStep 1065851 = 1598777) B1598777
theorem B1065977 : Blo 471786 1065977 := bstep (se 2 (by rfl) ⟨399741, by rfl⟩ : syracuseStep 1065977 = 799483) B799483
theorem B1066031 : Blo 471786 1066031 := bstep (se 1 (by rfl) ⟨799523, by rfl⟩ : syracuseStep 1066031 = 1599047) B1599047
theorem B1197119 : Blo 471786 1197119 := bstep (se 1 (by rfl) ⟨897839, by rfl⟩ : syracuseStep 1197119 = 1795679) B1795679
theorem B1197139 : Blo 471786 1197139 := bstep (se 1 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 1197139 = 1795709) B1795709
theorem B1066067 : Blo 471786 1066067 := bstep (se 1 (by rfl) ⟨799550, by rfl⟩ : syracuseStep 1066067 = 1599101) B1599101
theorem B9684139 : Blo 471786 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B1066247 : Blo 471786 1066247 := bstep (se 1 (by rfl) ⟨799685, by rfl⟩ : syracuseStep 1066247 = 1599371) B1599371
theorem B2049455 : Blo 471786 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B7685597 : Blo 471786 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B1066679 : Blo 471786 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B2279231 : Blo 471786 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B91146131 : Blo 471786 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B1067129 : Blo 471786 1067129 := bstep (se 2 (by rfl) ⟨400173, by rfl⟩ : syracuseStep 1067129 = 800347) B800347
theorem B3033233 : Blo 471786 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B641207 : Blo 471786 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B1067327 : Blo 471786 1067327 := bstep (se 1 (by rfl) ⟨800495, by rfl⟩ : syracuseStep 1067327 = 1600991) B1600991
theorem B9128537 : Blo 471786 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B3066623 : Blo 471786 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B641791 : Blo 471786 641791 := bstep (se 1 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 641791 = 962687) B962687
theorem B478375 : Blo 471786 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B708047 : Blo 471786 708047 := bstep (se 1 (by rfl) ⟨531035, by rfl⟩ : syracuseStep 708047 = 1062071) B1062071
theorem B708137 : Blo 471786 708137 := bstep (se 2 (by rfl) ⟨265551, by rfl⟩ : syracuseStep 708137 = 531103) B531103
theorem B708431 : Blo 471786 708431 := bstep (se 1 (by rfl) ⟨531323, by rfl⟩ : syracuseStep 708431 = 1062647) B1062647
theorem B708551 : Blo 471786 708551 := bstep (se 1 (by rfl) ⟨531413, by rfl⟩ : syracuseStep 708551 = 1062827) B1062827
theorem B708635 : Blo 471786 708635 := bstep (se 1 (by rfl) ⟨531476, by rfl⟩ : syracuseStep 708635 = 1062953) B1062953
theorem B1200359 : Blo 471786 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B708911 : Blo 471786 708911 := bstep (se 1 (by rfl) ⟨531683, by rfl⟩ : syracuseStep 708911 = 1063367) B1063367
theorem B709019 : Blo 471786 709019 := bstep (se 1 (by rfl) ⟨531764, by rfl⟩ : syracuseStep 709019 = 1063529) B1063529
theorem B709055 : Blo 471786 709055 := bstep (se 1 (by rfl) ⟨531791, by rfl⟩ : syracuseStep 709055 = 1063583) B1063583
theorem B709151 : Blo 471786 709151 := bstep (se 1 (by rfl) ⟨531863, by rfl⟩ : syracuseStep 709151 = 1063727) B1063727
theorem B709439 : Blo 471786 709439 := bstep (se 1 (by rfl) ⟨532079, by rfl⟩ : syracuseStep 709439 = 1064159) B1064159
theorem B709583 : Blo 471786 709583 := bstep (se 1 (by rfl) ⟨532187, by rfl⟩ : syracuseStep 709583 = 1064375) B1064375
theorem B676831 : Blo 471786 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B709673 : Blo 471786 709673 := bstep (se 2 (by rfl) ⟨266127, by rfl⟩ : syracuseStep 709673 = 532255) B532255
theorem B709703 : Blo 471786 709703 := bstep (se 1 (by rfl) ⟨532277, by rfl⟩ : syracuseStep 709703 = 1064555) B1064555
theorem B709883 : Blo 471786 709883 := bstep (se 1 (by rfl) ⟨532412, by rfl⟩ : syracuseStep 709883 = 1064825) B1064825
theorem B3593483 : Blo 471786 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B709943 : Blo 471786 709943 := bstep (se 1 (by rfl) ⟨532457, by rfl⟩ : syracuseStep 709943 = 1064915) B1064915
theorem B16602457 : Blo 471786 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B710249 : Blo 471786 710249 := bstep (se 2 (by rfl) ⟨266343, by rfl⟩ : syracuseStep 710249 = 532687) B532687
theorem B12474101 : Blo 471786 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B710783 : Blo 471786 710783 := bstep (se 1 (by rfl) ⟨533087, by rfl⟩ : syracuseStep 710783 = 1066175) B1066175
theorem B710879 : Blo 471786 710879 := bstep (se 1 (by rfl) ⟨533159, by rfl⟩ : syracuseStep 710879 = 1066319) B1066319
theorem B710939 : Blo 471786 710939 := bstep (se 1 (by rfl) ⟨533204, by rfl⟩ : syracuseStep 710939 = 1066409) B1066409
theorem B711263 : Blo 471786 711263 := bstep (se 1 (by rfl) ⟨533447, by rfl⟩ : syracuseStep 711263 = 1066895) B1066895
theorem B711359 : Blo 471786 711359 := bstep (se 1 (by rfl) ⟨533519, by rfl⟩ : syracuseStep 711359 = 1067039) B1067039
theorem B711401 : Blo 471786 711401 := bstep (se 2 (by rfl) ⟨266775, by rfl⟩ : syracuseStep 711401 = 533551) B533551
theorem B711527 : Blo 471786 711527 := bstep (se 1 (by rfl) ⟨533645, by rfl⟩ : syracuseStep 711527 = 1067291) B1067291
theorem B711593 : Blo 471786 711593 := bstep (se 2 (by rfl) ⟨266847, by rfl⟩ : syracuseStep 711593 = 533695) B533695
theorem B1203113 : Blo 471786 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B711743 : Blo 471786 711743 := bstep (se 1 (by rfl) ⟨533807, by rfl⟩ : syracuseStep 711743 = 1067615) B1067615
theorem B711785 : Blo 471786 711785 := bstep (se 2 (by rfl) ⟨266919, by rfl⟩ : syracuseStep 711785 = 533839) B533839
theorem B4054151 : Blo 471786 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B711911 : Blo 471786 711911 := bstep (se 1 (by rfl) ⟨533933, by rfl⟩ : syracuseStep 711911 = 1067867) B1067867
theorem B2022839 : Blo 471786 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B712415 : Blo 471786 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1597481 : Blo 471786 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B712745 : Blo 471786 712745 := bstep (se 2 (by rfl) ⟨267279, by rfl⟩ : syracuseStep 712745 = 534559) B534559
theorem B712775 : Blo 471786 712775 := bstep (se 1 (by rfl) ⟨534581, by rfl⟩ : syracuseStep 712775 = 1069163) B1069163
theorem B712811 : Blo 471786 712811 := bstep (se 1 (by rfl) ⟨534608, by rfl⟩ : syracuseStep 712811 = 1069217) B1069217
theorem B712895 : Blo 471786 712895 := bstep (se 1 (by rfl) ⟨534671, by rfl⟩ : syracuseStep 712895 = 1069343) B1069343
theorem B713081 : Blo 471786 713081 := bstep (se 2 (by rfl) ⟨267405, by rfl⟩ : syracuseStep 713081 = 534811) B534811
theorem B713375 : Blo 471786 713375 := bstep (se 1 (by rfl) ⟨535031, by rfl⟩ : syracuseStep 713375 = 1070063) B1070063
theorem B10674953 : Blo 471786 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B31057901 : Blo 471786 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B8611919 : Blo 471786 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B10217785 : Blo 471786 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B977231 : Blo 471786 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B7268717 : Blo 471786 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B15395183 : Blo 471786 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B10414655 : Blo 471786 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B1076219 : Blo 471786 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B1142191 : Blo 471786 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B651359 : Blo 471786 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B5140817 : Blo 471786 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B1798793 : Blo 471786 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B2159243 : Blo 471786 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1602395 : Blo 471786 1602395 := bstep (se 1 (by rfl) ⟨1201796, by rfl⟩ : syracuseStep 1602395 = 2403593) B2403593
theorem B1373231 : Blo 471786 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B1013231 : Blo 471786 1013231 := bstep (se 1 (by rfl) ⟨759923, by rfl⟩ : syracuseStep 1013231 = 1519847) B1519847
theorem B2389985 : Blo 471786 2389985 := bstep (se 2 (by rfl) ⟨896244, by rfl⟩ : syracuseStep 2389985 = 1792489) B1792489
theorem B3897371 : Blo 471786 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B6158377 : Blo 471786 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B5142799 : Blo 471786 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B2390471 : Blo 471786 2390471 := bstep (se 1 (by rfl) ⟨1792853, by rfl⟩ : syracuseStep 2390471 = 3585707) B3585707
theorem B10222631 : Blo 471786 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B1211483 : Blo 471786 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B100040147 : Blo 471786 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B1736171 : Blo 471786 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B2391929 : Blo 471786 2391929 := bstep (se 2 (by rfl) ⟨896973, by rfl⟩ : syracuseStep 2391929 = 1793947) B1793947
theorem B1802195 : Blo 471786 1802195 := bstep (se 1 (by rfl) ⟨1351646, by rfl⟩ : syracuseStep 1802195 = 2703293) B2703293
theorem B1802209 : Blo 471786 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B2556049 : Blo 471786 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B1736957 : Blo 471786 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B2687687 : Blo 471786 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B14550353 : Blo 471786 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B12912185 : Blo 471786 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B12978751 : Blo 471786 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B2395655 : Blo 471786 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B855721 : Blo 471786 855721 := bstep (se 2 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 855721 = 641791) B641791
theorem B1348559 : Blo 471786 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1709885 : Blo 471786 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B7116635 : Blo 471786 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B15571561 : Blo 471786 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B5741279 : Blo 471786 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B10263455 : Blo 471786 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B532219 : Blo 471786 532219 := bstep (se 1 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 532219 = 798329) B798329
theorem B4170041 : Blo 471786 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B6857065 : Blo 471786 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B1712987 : Blo 471786 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B533371 : Blo 471786 533371 := bstep (se 1 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 533371 = 800057) B800057
theorem B533407 : Blo 471786 533407 := bstep (se 1 (by rfl) ⟨400055, by rfl⟩ : syracuseStep 533407 = 800111) B800111
theorem B1319915 : Blo 471786 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B2598247 : Blo 471786 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B796223 : Blo 471786 796223 := bstep (se 1 (by rfl) ⟨597167, by rfl⟩ : syracuseStep 796223 = 1194335) B1194335
theorem B2696935 : Blo 471786 2696935 := bstep (se 1 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 2696935 = 4045403) B4045403
theorem B66693431 : Blo 471786 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B1157447 : Blo 471786 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B797087 : Blo 471786 797087 := bstep (se 1 (by rfl) ⟨597815, by rfl⟩ : syracuseStep 797087 = 1195631) B1195631
theorem B2402945 : Blo 471786 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B1354619 : Blo 471786 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B4369747 : Blo 471786 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B798079 : Blo 471786 798079 := bstep (se 1 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 798079 = 1197119) B1197119
theorem B5123731 : Blo 471786 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B1519487 : Blo 471786 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B60764087 : Blo 471786 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B897247 : Blo 471786 897247 := bstep (se 1 (by rfl) ⟨672935, by rfl⟩ : syracuseStep 897247 = 1345871) B1345871
theorem B2044415 : Blo 471786 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B472031 : Blo 471786 472031 := bstep (se 1 (by rfl) ⟨354023, by rfl⟩ : syracuseStep 472031 = 708047) B708047
theorem B472091 : Blo 471786 472091 := bstep (se 1 (by rfl) ⟨354068, by rfl⟩ : syracuseStep 472091 = 708137) B708137
theorem B2405537 : Blo 471786 2405537 := bstep (se 2 (by rfl) ⟨902076, by rfl⟩ : syracuseStep 2405537 = 1804153) B1804153
theorem B472287 : Blo 471786 472287 := bstep (se 1 (by rfl) ⟨354215, by rfl⟩ : syracuseStep 472287 = 708431) B708431
theorem B472367 : Blo 471786 472367 := bstep (se 1 (by rfl) ⟨354275, by rfl⟩ : syracuseStep 472367 = 708551) B708551
theorem B472423 : Blo 471786 472423 := bstep (se 1 (by rfl) ⟨354317, by rfl⟩ : syracuseStep 472423 = 708635) B708635
theorem B800239 : Blo 471786 800239 := bstep (se 1 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 800239 = 1200359) B1200359
theorem B472607 : Blo 471786 472607 := bstep (se 1 (by rfl) ⟨354455, by rfl⟩ : syracuseStep 472607 = 708911) B708911
theorem B472679 : Blo 471786 472679 := bstep (se 1 (by rfl) ⟨354509, by rfl⟩ : syracuseStep 472679 = 709019) B709019
theorem B1062521 : Blo 471786 1062521 := bstep (se 2 (by rfl) ⟨398445, by rfl⟩ : syracuseStep 1062521 = 796891) B796891
theorem B472703 : Blo 471786 472703 := bstep (se 1 (by rfl) ⟨354527, by rfl⟩ : syracuseStep 472703 = 709055) B709055
theorem B472767 : Blo 471786 472767 := bstep (se 1 (by rfl) ⟨354575, by rfl⟩ : syracuseStep 472767 = 709151) B709151
theorem B472959 : Blo 471786 472959 := bstep (se 1 (by rfl) ⟨354719, by rfl⟩ : syracuseStep 472959 = 709439) B709439
theorem B473055 : Blo 471786 473055 := bstep (se 1 (by rfl) ⟨354791, by rfl⟩ : syracuseStep 473055 = 709583) B709583
theorem B1062881 : Blo 471786 1062881 := bstep (se 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) B797161
theorem B473115 : Blo 471786 473115 := bstep (se 1 (by rfl) ⟨354836, by rfl⟩ : syracuseStep 473115 = 709673) B709673
theorem B473135 : Blo 471786 473135 := bstep (se 1 (by rfl) ⟨354851, by rfl⟩ : syracuseStep 473135 = 709703) B709703
theorem B473255 : Blo 471786 473255 := bstep (se 1 (by rfl) ⟨354941, by rfl⟩ : syracuseStep 473255 = 709883) B709883
theorem B473295 : Blo 471786 473295 := bstep (se 1 (by rfl) ⟨354971, by rfl⟩ : syracuseStep 473295 = 709943) B709943
theorem B473499 : Blo 471786 473499 := bstep (se 1 (by rfl) ⟨355124, by rfl⟩ : syracuseStep 473499 = 710249) B710249
theorem B473855 : Blo 471786 473855 := bstep (se 1 (by rfl) ⟨355391, by rfl⟩ : syracuseStep 473855 = 710783) B710783
theorem B473919 : Blo 471786 473919 := bstep (se 1 (by rfl) ⟨355439, by rfl⟩ : syracuseStep 473919 = 710879) B710879
theorem B473959 : Blo 471786 473959 := bstep (se 1 (by rfl) ⟨355469, by rfl⟩ : syracuseStep 473959 = 710939) B710939
theorem B474175 : Blo 471786 474175 := bstep (se 1 (by rfl) ⟨355631, by rfl⟩ : syracuseStep 474175 = 711263) B711263
theorem B474239 : Blo 471786 474239 := bstep (se 1 (by rfl) ⟨355679, by rfl⟩ : syracuseStep 474239 = 711359) B711359
theorem B474267 : Blo 471786 474267 := bstep (se 1 (by rfl) ⟨355700, by rfl⟩ : syracuseStep 474267 = 711401) B711401
theorem B474351 : Blo 471786 474351 := bstep (se 1 (by rfl) ⟨355763, by rfl⟩ : syracuseStep 474351 = 711527) B711527
theorem B474395 : Blo 471786 474395 := bstep (se 1 (by rfl) ⟨355796, by rfl⟩ : syracuseStep 474395 = 711593) B711593
theorem B802075 : Blo 471786 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B474495 : Blo 471786 474495 := bstep (se 1 (by rfl) ⟨355871, by rfl⟩ : syracuseStep 474495 = 711743) B711743
theorem B474523 : Blo 471786 474523 := bstep (se 1 (by rfl) ⟨355892, by rfl⟩ : syracuseStep 474523 = 711785) B711785
theorem B2702767 : Blo 471786 2702767 := bstep (se 1 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 2702767 = 4054151) B4054151
theorem B474607 : Blo 471786 474607 := bstep (se 1 (by rfl) ⟨355955, by rfl⟩ : syracuseStep 474607 = 711911) B711911
theorem B474943 : Blo 471786 474943 := bstep (se 1 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 474943 = 712415) B712415
theorem B1064987 : Blo 471786 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B475163 : Blo 471786 475163 := bstep (se 1 (by rfl) ⟨356372, by rfl⟩ : syracuseStep 475163 = 712745) B712745
theorem B475183 : Blo 471786 475183 := bstep (se 1 (by rfl) ⟨356387, by rfl⟩ : syracuseStep 475183 = 712775) B712775
theorem B113688643 : Blo 471786 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B475207 : Blo 471786 475207 := bstep (se 1 (by rfl) ⟨356405, by rfl⟩ : syracuseStep 475207 = 712811) B712811
theorem B475263 : Blo 471786 475263 := bstep (se 1 (by rfl) ⟨356447, by rfl⟩ : syracuseStep 475263 = 712895) B712895
theorem B475387 : Blo 471786 475387 := bstep (se 1 (by rfl) ⟨356540, by rfl⟩ : syracuseStep 475387 = 713081) B713081
theorem B1065257 : Blo 471786 1065257 := bstep (se 2 (by rfl) ⟨399471, by rfl⟩ : syracuseStep 1065257 = 798943) B798943
theorem B475583 : Blo 471786 475583 := bstep (se 1 (by rfl) ⟨356687, by rfl⟩ : syracuseStep 475583 = 713375) B713375
theorem B7651921 : Blo 471786 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B98321201 : Blo 471786 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B19383245 : Blo 471786 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B1197281 : Blo 471786 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B902441 : Blo 471786 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B22136609 : Blo 471786 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B38979569 : Blo 471786 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B1067561 : Blo 471786 1067561 := bstep (se 2 (by rfl) ⟨400335, by rfl⟩ : syracuseStep 1067561 = 800671) B800671
theorem B8211169 : Blo 471786 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B3427211 : Blo 471786 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B3230621 : Blo 471786 3230621 := bstep (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) B1211483
theorem B1199195 : Blo 471786 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B1166543 : Blo 471786 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B1068263 : Blo 471786 1068263 := bstep (se 1 (by rfl) ⟨801197, by rfl⟩ : syracuseStep 1068263 = 1602395) B1602395
theorem B708095 : Blo 471786 708095 := bstep (se 1 (by rfl) ⟨531071, by rfl⟩ : syracuseStep 708095 = 1062143) B1062143
theorem B675487 : Blo 471786 675487 := bstep (se 1 (by rfl) ⟨506615, by rfl⟩ : syracuseStep 675487 = 1013231) B1013231
theorem B7294637 : Blo 471786 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B12177215 : Blo 471786 12177215 := bstep (se 1 (by rfl) ⟨9132911, by rfl⟩ : syracuseStep 12177215 = 18265823) B18265823
theorem B1593323 : Blo 471786 1593323 := bstep (se 1 (by rfl) ⟨1194992, by rfl⟩ : syracuseStep 1593323 = 2389985) B2389985
theorem B1593377 : Blo 471786 1593377 := bstep (se 2 (by rfl) ⟨597516, by rfl⟩ : syracuseStep 1593377 = 1195033) B1195033
theorem B512191 : Blo 471786 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B1593647 : Blo 471786 1593647 := bstep (se 1 (by rfl) ⟨1195235, by rfl⟩ : syracuseStep 1593647 = 2390471) B2390471
theorem B709247 : Blo 471786 709247 := bstep (se 1 (by rfl) ⟨531935, by rfl⟩ : syracuseStep 709247 = 1063871) B1063871
theorem B709679 : Blo 471786 709679 := bstep (se 1 (by rfl) ⟨532259, by rfl⟩ : syracuseStep 709679 = 1064519) B1064519
theorem B709799 : Blo 471786 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B1594619 : Blo 471786 1594619 := bstep (se 1 (by rfl) ⟨1195964, by rfl⟩ : syracuseStep 1594619 = 2391929) B2391929
theorem B1201463 : Blo 471786 1201463 := bstep (se 1 (by rfl) ⟨901097, by rfl⟩ : syracuseStep 1201463 = 1802195) B1802195
theorem B709967 : Blo 471786 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B2053487 : Blo 471786 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B2708873 : Blo 471786 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B710207 : Blo 471786 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B710567 : Blo 471786 710567 := bstep (se 1 (by rfl) ⟨532925, by rfl⟩ : syracuseStep 710567 = 1065851) B1065851
theorem B710651 : Blo 471786 710651 := bstep (se 1 (by rfl) ⟨532988, by rfl⟩ : syracuseStep 710651 = 1065977) B1065977
theorem B710687 : Blo 471786 710687 := bstep (se 1 (by rfl) ⟨533015, by rfl⟩ : syracuseStep 710687 = 1066031) B1066031
theorem B710711 : Blo 471786 710711 := bstep (se 1 (by rfl) ⟨533033, by rfl⟩ : syracuseStep 710711 = 1066067) B1066067
theorem B710777 : Blo 471786 710777 := bstep (se 2 (by rfl) ⟨266541, by rfl⟩ : syracuseStep 710777 = 533083) B533083
theorem B1202303 : Blo 471786 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B710831 : Blo 471786 710831 := bstep (se 1 (by rfl) ⟨533123, by rfl⟩ : syracuseStep 710831 = 1066247) B1066247
theorem B1366303 : Blo 471786 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B711119 : Blo 471786 711119 := bstep (se 1 (by rfl) ⟨533339, by rfl⟩ : syracuseStep 711119 = 1066679) B1066679
theorem B1202647 : Blo 471786 1202647 := bstep (se 1 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 1202647 = 1803971) B1803971
theorem B711419 : Blo 471786 711419 := bstep (se 1 (by rfl) ⟨533564, by rfl⟩ : syracuseStep 711419 = 1067129) B1067129
theorem B2022155 : Blo 471786 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B1596185 : Blo 471786 1596185 := bstep (se 2 (by rfl) ⟨598569, by rfl⟩ : syracuseStep 1596185 = 1197139) B1197139
theorem B711545 : Blo 471786 711545 := bstep (se 2 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 711545 = 533659) B533659
theorem B711551 : Blo 471786 711551 := bstep (se 1 (by rfl) ⟨533663, by rfl⟩ : syracuseStep 711551 = 1067327) B1067327
theorem B1792975 : Blo 471786 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B6085691 : Blo 471786 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B1203407 : Blo 471786 1203407 := bstep (se 1 (by rfl) ⟨902555, by rfl⟩ : syracuseStep 1203407 = 1805111) B1805111
theorem B712457 : Blo 471786 712457 := bstep (se 2 (by rfl) ⟨267171, by rfl⟩ : syracuseStep 712457 = 534343) B534343
theorem B100228913 : Blo 471786 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B3661949 : Blo 471786 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B13623713 : Blo 471786 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B1008617 : Blo 471786 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B1008703 : Blo 471786 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B8316067 : Blo 471786 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B812891 : Blo 471786 812891 := bstep (se 1 (by rfl) ⟨609668, by rfl⟩ : syracuseStep 812891 = 1219337) B1219337
theorem B3238667 : Blo 471786 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B1141769 : Blo 471786 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B2551333 : Blo 471786 2551333 := bstep (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) B478375
theorem B20705267 : Blo 471786 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B1601531 : Blo 471786 1601531 := bstep (se 1 (by rfl) ⟨1201148, by rfl⟩ : syracuseStep 1601531 = 2402297) B2402297
theorem B651487 : Blo 471786 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B6943103 : Blo 471786 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B2028169 : Blo 471786 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B717479 : Blo 471786 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B2159441 : Blo 471786 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B6845309 : Blo 471786 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B6091685 : Blo 471786 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B1603151 : Blo 471786 1603151 := bstep (se 1 (by rfl) ⟨1202363, by rfl⟩ : syracuseStep 1603151 = 2404727) B2404727
theorem B1439495 : Blo 471786 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B1537883 : Blo 471786 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B1013897 : Blo 471786 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1604123 : Blo 471786 1604123 := bstep (se 1 (by rfl) ⟨1203092, by rfl⟩ : syracuseStep 1604123 = 2406185) B2406185
theorem B4553927 : Blo 471786 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B6815087 : Blo 471786 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B1604987 : Blo 471786 1604987 := bstep (se 1 (by rfl) ⟨1203740, by rfl⟩ : syracuseStep 1604987 = 2407481) B2407481
theorem B151584857 : Blo 471786 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B3408065 : Blo 471786 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B9765197 : Blo 471786 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B9142753 : Blo 471786 9142753 := bstep (se 2 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 9142753 = 6857065) B6857065
theorem B9700235 : Blo 471786 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B25986379 : Blo 471786 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B1344937 : Blo 471786 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B2689645 : Blo 471786 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B17305001 : Blo 471786 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B1805915 : Blo 471786 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B10948225 : Blo 471786 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B1348103 : Blo 471786 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B66819275 : Blo 471786 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B9082475 : Blo 471786 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B3086525 : Blo 471786 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B530815 : Blo 471786 530815 := bstep (se 1 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 530815 = 796223) B796223
theorem B531391 : Blo 471786 531391 := bstep (se 1 (by rfl) ⟨398543, by rfl⟩ : syracuseStep 531391 = 797087) B797087
theorem B761179 : Blo 471786 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B40509391 : Blo 471786 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B4628735 : Blo 471786 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B4563539 : Blo 471786 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B959663 : Blo 471786 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B1025255 : Blo 471786 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B1157971 : Blo 471786 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B65547467 : Blo 471786 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B12922163 : Blo 471786 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B10202561 : Blo 471786 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B798187 : Blo 471786 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B11088089 : Blo 471786 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B799463 : Blo 471786 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B472063 : Blo 471786 472063 := bstep (se 1 (by rfl) ⟨354047, by rfl⟩ : syracuseStep 472063 = 708095) B708095
theorem B4863091 : Blo 471786 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B3519773 : Blo 471786 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1062215 : Blo 471786 1062215 := bstep (se 1 (by rfl) ⟨796661, by rfl⟩ : syracuseStep 1062215 = 1593323) B1593323
theorem B1062251 : Blo 471786 1062251 := bstep (se 1 (by rfl) ⟨796688, by rfl⟩ : syracuseStep 1062251 = 1593377) B1593377
theorem B1062431 : Blo 471786 1062431 := bstep (se 1 (by rfl) ⟨796823, by rfl⟩ : syracuseStep 1062431 = 1593647) B1593647
theorem B472831 : Blo 471786 472831 := bstep (se 1 (by rfl) ⟨354623, by rfl⟩ : syracuseStep 472831 = 709247) B709247
theorem B899039 : Blo 471786 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B473119 : Blo 471786 473119 := bstep (se 1 (by rfl) ⟨354839, by rfl⟩ : syracuseStep 473119 = 709679) B709679
theorem B2406509 : Blo 471786 2406509 := bstep (se 3 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 2406509 = 902441) B902441
theorem B473199 : Blo 471786 473199 := bstep (se 1 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 473199 = 709799) B709799
theorem B1063079 : Blo 471786 1063079 := bstep (se 1 (by rfl) ⟨797309, by rfl⟩ : syracuseStep 1063079 = 1594619) B1594619
theorem B800975 : Blo 471786 800975 := bstep (se 1 (by rfl) ⟨600731, by rfl⟩ : syracuseStep 800975 = 1201463) B1201463
theorem B473311 : Blo 471786 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B473471 : Blo 471786 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B473711 : Blo 471786 473711 := bstep (se 1 (by rfl) ⟨355283, by rfl⟩ : syracuseStep 473711 = 710567) B710567
theorem B473767 : Blo 471786 473767 := bstep (se 1 (by rfl) ⟨355325, by rfl⟩ : syracuseStep 473767 = 710651) B710651
theorem B473791 : Blo 471786 473791 := bstep (se 1 (by rfl) ⟨355343, by rfl⟩ : syracuseStep 473791 = 710687) B710687
theorem B473807 : Blo 471786 473807 := bstep (se 1 (by rfl) ⟨355355, by rfl⟩ : syracuseStep 473807 = 710711) B710711
theorem B473851 : Blo 471786 473851 := bstep (se 1 (by rfl) ⟨355388, by rfl⟩ : syracuseStep 473851 = 710777) B710777
theorem B801535 : Blo 471786 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B473887 : Blo 471786 473887 := bstep (se 1 (by rfl) ⟨355415, by rfl⟩ : syracuseStep 473887 = 710831) B710831
theorem B474079 : Blo 471786 474079 := bstep (se 1 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 474079 = 711119) B711119
theorem B474279 : Blo 471786 474279 := bstep (se 1 (by rfl) ⟨355709, by rfl⟩ : syracuseStep 474279 = 711419) B711419
theorem B1064105 : Blo 471786 1064105 := bstep (se 2 (by rfl) ⟨399039, by rfl⟩ : syracuseStep 1064105 = 798079) B798079
theorem B1064123 : Blo 471786 1064123 := bstep (se 1 (by rfl) ⟨798092, by rfl⟩ : syracuseStep 1064123 = 1596185) B1596185
theorem B474363 : Blo 471786 474363 := bstep (se 1 (by rfl) ⟨355772, by rfl⟩ : syracuseStep 474363 = 711545) B711545
theorem B474367 : Blo 471786 474367 := bstep (se 1 (by rfl) ⟨355775, by rfl⟩ : syracuseStep 474367 = 711551) B711551
theorem B59030957 : Blo 471786 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B802271 : Blo 471786 802271 := bstep (se 1 (by rfl) ⟨601703, by rfl⟩ : syracuseStep 802271 = 1203407) B1203407
theorem B6831641 : Blo 471786 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B900649 : Blo 471786 900649 := bstep (se 2 (by rfl) ⟨337743, by rfl⟩ : syracuseStep 900649 = 675487) B675487
theorem B474971 : Blo 471786 474971 := bstep (se 1 (by rfl) ⟨356228, by rfl⟩ : syracuseStep 474971 = 712457) B712457
theorem B1196329 : Blo 471786 1196329 := bstep (se 2 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 1196329 = 897247) B897247
theorem B868649 : Blo 471786 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B2703725 : Blo 471786 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B2704225 : Blo 471786 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B541927 : Blo 471786 541927 := bstep (se 1 (by rfl) ⟨406445, by rfl⟩ : syracuseStep 541927 = 812891) B812891
theorem B903079 : Blo 471786 903079 := bstep (se 1 (by rfl) ⟨677309, by rfl⟩ : syracuseStep 903079 = 1354619) B1354619
theorem B1066985 : Blo 471786 1066985 := bstep (se 2 (by rfl) ⟨400119, by rfl⟩ : syracuseStep 1066985 = 800239) B800239
theorem B1067687 : Blo 471786 1067687 := bstep (se 1 (by rfl) ⟨800765, by rfl⟩ : syracuseStep 1067687 = 1601531) B1601531
theorem B1362943 : Blo 471786 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B1821737 : Blo 471786 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B478319 : Blo 471786 478319 := bstep (se 1 (by rfl) ⟨358739, by rfl⟩ : syracuseStep 478319 = 717479) B717479
theorem B20762081 : Blo 471786 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B1068767 : Blo 471786 1068767 := bstep (se 1 (by rfl) ⟨801575, by rfl⟩ : syracuseStep 1068767 = 1603151) B1603151
theorem B708347 : Blo 471786 708347 := bstep (se 1 (by rfl) ⟨531260, by rfl⟩ : syracuseStep 708347 = 1062521) B1062521
theorem B708587 : Blo 471786 708587 := bstep (se 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) B1062881
theorem B1069415 : Blo 471786 1069415 := bstep (se 1 (by rfl) ⟨802061, by rfl⟩ : syracuseStep 1069415 = 1604123) B1604123
theorem B1069433 : Blo 471786 1069433 := bstep (se 2 (by rfl) ⟨401037, by rfl⟩ : syracuseStep 1069433 = 802075) B802075
theorem B3035951 : Blo 471786 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B4543391 : Blo 471786 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B1069991 : Blo 471786 1069991 := bstep (se 1 (by rfl) ⟨802493, by rfl⟩ : syracuseStep 1069991 = 1604987) B1604987
theorem B709625 : Blo 471786 709625 := bstep (se 2 (by rfl) ⟨266109, by rfl⟩ : syracuseStep 709625 = 532219) B532219
theorem B709991 : Blo 471786 709991 := bstep (se 1 (by rfl) ⟨532493, by rfl⟩ : syracuseStep 709991 = 1064987) B1064987
theorem B710171 : Blo 471786 710171 := bstep (se 1 (by rfl) ⟨532628, by rfl⟩ : syracuseStep 710171 = 1065257) B1065257
theorem B1791791 : Blo 471786 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B8608123 : Blo 471786 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B711161 : Blo 471786 711161 := bstep (se 2 (by rfl) ⟨266685, by rfl⟩ : syracuseStep 711161 = 533371) B533371
theorem B711209 : Blo 471786 711209 := bstep (se 2 (by rfl) ⟨266703, by rfl⟩ : syracuseStep 711209 = 533407) B533407
theorem B711707 : Blo 471786 711707 := bstep (se 1 (by rfl) ⟨533780, by rfl⟩ : syracuseStep 711707 = 1067561) B1067561
theorem B3464329 : Blo 471786 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B2284807 : Blo 471786 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B2153747 : Blo 471786 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B777695 : Blo 471786 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B712175 : Blo 471786 712175 := bstep (se 1 (by rfl) ⟨534131, by rfl⟩ : syracuseStep 712175 = 1068263) B1068263
theorem B3595913 : Blo 471786 3595913 := bstep (se 2 (by rfl) ⟨1348467, by rfl⟩ : syracuseStep 3595913 = 2696935) B2696935
theorem B1597103 : Blo 471786 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B8118143 : Blo 471786 8118143 := bstep (se 1 (by rfl) ⟨6088607, by rfl⟩ : syracuseStep 8118143 = 12177215) B12177215
theorem B1368991 : Blo 471786 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B1139923 : Blo 471786 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B4744423 : Blo 471786 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B5826329 : Blo 471786 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B3827519 : Blo 471786 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B6842303 : Blo 471786 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B4057127 : Blo 471786 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B3401777 : Blo 471786 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B1140961 : Blo 471786 1140961 := bstep (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) B855721
theorem B2780027 : Blo 471786 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B682921 : Blo 471786 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B1141991 : Blo 471786 1141991 := bstep (se 1 (by rfl) ⟨856493, by rfl⟩ : syracuseStep 1141991 = 1712987) B1712987
theorem B44462287 : Blo 471786 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B1601963 : Blo 471786 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B2159111 : Blo 471786 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B1012991 : Blo 471786 1012991 := bstep (se 1 (by rfl) ⟨759743, by rfl⟩ : syracuseStep 1012991 = 1519487) B1519487
theorem B1439627 : Blo 471786 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B4061123 : Blo 471786 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B1603529 : Blo 471786 1603529 := bstep (se 2 (by rfl) ⟨601323, by rfl⟩ : syracuseStep 1603529 = 1202647) B1202647
theorem B1603691 : Blo 471786 1603691 := bstep (se 1 (by rfl) ⟨1202768, by rfl⟩ : syracuseStep 1603691 = 2405537) B2405537
theorem B2390633 : Blo 471786 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B3603689 : Blo 471786 3603689 := bstep (se 2 (by rfl) ⟨1351383, by rfl⟩ : syracuseStep 3603689 = 2702767) B2702767
theorem B55214045 : Blo 471786 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B101056571 : Blo 471786 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B1802483 : Blo 471786 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B12190337 : Blo 471786 12190337 := bstep (se 2 (by rfl) ⟨4571376, by rfl⟩ : syracuseStep 12190337 = 9142753) B9142753
theorem B3605633 : Blo 471786 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B6325897 : Blo 471786 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B722569 : Blo 471786 722569 := bstep (se 2 (by rfl) ⟨270963, by rfl⟩ : syracuseStep 722569 = 541927) B541927
theorem B11536667 : Blo 471786 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B1543961 : Blo 471786 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B3839005 : Blo 471786 3839005 := bstep (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) B1439627
theorem B2397275 : Blo 471786 2397275 := bstep (se 1 (by rfl) ⟨1797956, by rfl⟩ : syracuseStep 2397275 = 3595913) B3595913
theorem B2397437 : Blo 471786 2397437 := bstep (se 3 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 2397437 = 899039) B899039
theorem B5412095 : Blo 471786 5412095 := bstep (se 1 (by rfl) ⟨4059071, by rfl⟩ : syracuseStep 5412095 = 8118143) B8118143
theorem B3085823 : Blo 471786 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B4561535 : Blo 471786 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B2267851 : Blo 471786 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B761327 : Blo 471786 761327 := bstep (se 1 (by rfl) ⟨570995, by rfl⟩ : syracuseStep 761327 = 1141991) B1141991
theorem B4857965 : Blo 471786 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B532975 : Blo 471786 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B11477497 : Blo 471786 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B5743325 : Blo 471786 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B2073853 : Blo 471786 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B533983 : Blo 471786 533983 := bstep (se 1 (by rfl) ⟨400487, by rfl⟩ : syracuseStep 533983 = 800975) B800975
theorem B2402459 : Blo 471786 2402459 := bstep (se 1 (by rfl) ⟨1801844, by rfl⟩ : syracuseStep 2402459 = 3603689) B3603689
theorem B534847 : Blo 471786 534847 := bstep (se 1 (by rfl) ⟨401135, by rfl⟩ : syracuseStep 534847 = 802271) B802271
theorem B54012521 : Blo 471786 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B36809363 : Blo 471786 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B2272043 : Blo 471786 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B6466823 : Blo 471786 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B1519897 : Blo 471786 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B34648505 : Blo 471786 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B13841387 : Blo 471786 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B472231 : Blo 471786 472231 := bstep (se 1 (by rfl) ⟨354173, by rfl⟩ : syracuseStep 472231 = 708347) B708347
theorem B472391 : Blo 471786 472391 := bstep (se 1 (by rfl) ⟨354293, by rfl⟩ : syracuseStep 472391 = 708587) B708587
theorem B1521281 : Blo 471786 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B2734013 : Blo 471786 2734013 := bstep (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) B1025255
theorem B3028927 : Blo 471786 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B473083 : Blo 471786 473083 := bstep (se 1 (by rfl) ⟨354812, by rfl⟩ : syracuseStep 473083 = 709625) B709625
theorem B2701309 : Blo 471786 2701309 := bstep (se 3 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 2701309 = 1012991) B1012991
theorem B44546183 : Blo 471786 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B3586193 : Blo 471786 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B473327 : Blo 471786 473327 := bstep (se 1 (by rfl) ⟨354995, by rfl⟩ : syracuseStep 473327 = 709991) B709991
theorem B473447 : Blo 471786 473447 := bstep (se 1 (by rfl) ⟨355085, by rfl⟩ : syracuseStep 473447 = 710171) B710171
theorem B1194527 : Blo 471786 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B1817257 : Blo 471786 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B474107 : Blo 471786 474107 := bstep (se 1 (by rfl) ⟨355580, by rfl⟩ : syracuseStep 474107 = 711161) B711161
theorem B474139 : Blo 471786 474139 := bstep (se 1 (by rfl) ⟨355604, by rfl⟩ : syracuseStep 474139 = 711209) B711209
theorem B1064249 : Blo 471786 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B474471 : Blo 471786 474471 := bstep (se 1 (by rfl) ⟨355853, by rfl⟩ : syracuseStep 474471 = 711707) B711707
theorem B14597633 : Blo 471786 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B474783 : Blo 471786 474783 := bstep (se 1 (by rfl) ⟨356087, by rfl⟩ : syracuseStep 474783 = 712175) B712175
theorem B1064735 : Blo 471786 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B639775 : Blo 471786 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B3884219 : Blo 471786 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B2704751 : Blo 471786 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B1853351 : Blo 471786 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B43698311 : Blo 471786 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B6801707 : Blo 471786 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B7392059 : Blo 471786 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B1067975 : Blo 471786 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B707753 : Blo 471786 707753 := bstep (se 2 (by rfl) ⟨265407, by rfl⟩ : syracuseStep 707753 = 530815) B530815
theorem B2346515 : Blo 471786 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B708143 : Blo 471786 708143 := bstep (se 1 (by rfl) ⟨531107, by rfl⟩ : syracuseStep 708143 = 1062215) B1062215
theorem B708167 : Blo 471786 708167 := bstep (se 1 (by rfl) ⟨531125, by rfl⟩ : syracuseStep 708167 = 1062251) B1062251
theorem B1068713 : Blo 471786 1068713 := bstep (se 2 (by rfl) ⟨400767, by rfl⟩ : syracuseStep 1068713 = 801535) B801535
theorem B708287 : Blo 471786 708287 := bstep (se 1 (by rfl) ⟨531215, by rfl⟩ : syracuseStep 708287 = 1062431) B1062431
theorem B708521 : Blo 471786 708521 := bstep (se 2 (by rfl) ⟨265695, by rfl⟩ : syracuseStep 708521 = 531391) B531391
theorem B2707415 : Blo 471786 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B1069019 : Blo 471786 1069019 := bstep (se 1 (by rfl) ⟨801764, by rfl⟩ : syracuseStep 1069019 = 1603529) B1603529
theorem B1069127 : Blo 471786 1069127 := bstep (se 1 (by rfl) ⟨801845, by rfl⟩ : syracuseStep 1069127 = 1603691) B1603691
theorem B708719 : Blo 471786 708719 := bstep (se 1 (by rfl) ⟨531539, by rfl⟩ : syracuseStep 708719 = 1063079) B1063079
theorem B1593755 : Blo 471786 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B1200865 : Blo 471786 1200865 := bstep (se 2 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 1200865 = 900649) B900649
theorem B709403 : Blo 471786 709403 := bstep (se 1 (by rfl) ⟨532052, by rfl⟩ : syracuseStep 709403 = 1064105) B1064105
theorem B709415 : Blo 471786 709415 := bstep (se 1 (by rfl) ⟨532061, by rfl⟩ : syracuseStep 709415 = 1064123) B1064123
theorem B6510131 : Blo 471786 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B1595105 : Blo 471786 1595105 := bstep (se 2 (by rfl) ⟨598164, by rfl⟩ : syracuseStep 1595105 = 1196329) B1196329
theorem B237132197 : Blo 471786 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B711323 : Blo 471786 711323 := bstep (se 1 (by rfl) ⟨533492, by rfl⟩ : syracuseStep 711323 = 1066985) B1066985
theorem B3594941 : Blo 471786 3594941 := bstep (se 3 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 3594941 = 1348103) B1348103
theorem B711791 : Blo 471786 711791 := bstep (se 1 (by rfl) ⟨533843, by rfl⟩ : syracuseStep 711791 = 1067687) B1067687
theorem B1793249 : Blo 471786 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B1203943 : Blo 471786 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B712511 : Blo 471786 712511 := bstep (se 1 (by rfl) ⟨534383, by rfl⟩ : syracuseStep 712511 = 1068767) B1068767
theorem B1204105 : Blo 471786 1204105 := bstep (se 2 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 1204105 = 903079) B903079
theorem B712943 : Blo 471786 712943 := bstep (se 1 (by rfl) ⟨534707, by rfl⟩ : syracuseStep 712943 = 1069415) B1069415
theorem B712955 : Blo 471786 712955 := bstep (se 1 (by rfl) ⟨534716, by rfl⟩ : syracuseStep 712955 = 1069433) B1069433
theorem B9265589 : Blo 471786 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B2023967 : Blo 471786 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B713327 : Blo 471786 713327 := bstep (se 1 (by rfl) ⟨534995, by rfl⟩ : syracuseStep 713327 = 1069991) B1069991
theorem B6054983 : Blo 471786 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B910561 : Blo 471786 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B2057683 : Blo 471786 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B7301285 : Blo 471786 7301285 := bstep (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) B1368991
theorem B3042359 : Blo 471786 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B2551679 : Blo 471786 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B6484121 : Blo 471786 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B8614775 : Blo 471786 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B1275517 : Blo 471786 1275517 := bstep (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) B478319
theorem B1439407 : Blo 471786 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B1604339 : Blo 471786 1604339 := bstep (se 1 (by rfl) ⟨1203254, by rfl⟩ : syracuseStep 1604339 = 2406509) B2406509
theorem B4619105 : Blo 471786 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B3046409 : Blo 471786 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B1014905 : Blo 471786 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B39353971 : Blo 471786 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B4554427 : Blo 471786 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B67371047 : Blo 471786 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B8126891 : Blo 471786 8126891 := bstep (se 1 (by rfl) ⟨6095168, by rfl⟩ : syracuseStep 8126891 = 12190337) B12190337
theorem B15303329 : Blo 471786 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B2589479 : Blo 471786 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B1803167 : Blo 471786 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B853033 : Blo 471786 853033 := bstep (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) B639775
theorem B29132207 : Blo 471786 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1214081 : Blo 471786 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B1804943 : Blo 471786 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B3608063 : Blo 471786 3608063 := bstep (se 1 (by rfl) ⟨2706047, by rfl⟩ : syracuseStep 3608063 = 5412095) B5412095
theorem B8228861 : Blo 471786 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B2396627 : Blo 471786 2396627 := bstep (se 1 (by rfl) ⟨1797470, by rfl⟩ : syracuseStep 2396627 = 3594941) B3594941
theorem B1349311 : Blo 471786 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B4036655 : Blo 471786 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B5118673 : Blo 471786 5118673 := bstep (se 2 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 5118673 = 3839005) B3839005
theorem B12164093 : Blo 471786 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B1514695 : Blo 471786 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B4038569 : Blo 471786 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B5743183 : Blo 471786 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B3023801 : Blo 471786 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B29697455 : Blo 471786 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B796351 : Blo 471786 796351 := bstep (se 1 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 796351 = 1194527) B1194527
theorem B52471961 : Blo 471786 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B6072569 : Blo 471786 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B2403755 : Blo 471786 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B4534471 : Blo 471786 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B2765137 : Blo 471786 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B4928039 : Blo 471786 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B471835 : Blo 471786 471835 := bstep (se 1 (by rfl) ⟨353876, by rfl⟩ : syracuseStep 471835 = 707753) B707753
theorem B8434529 : Blo 471786 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B963425 : Blo 471786 963425 := bstep (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) B722569
theorem B472095 : Blo 471786 472095 := bstep (se 1 (by rfl) ⟨354071, by rfl⟩ : syracuseStep 472095 = 708143) B708143
theorem B472111 : Blo 471786 472111 := bstep (se 1 (by rfl) ⟨354083, by rfl⟩ : syracuseStep 472111 = 708167) B708167
theorem B472191 : Blo 471786 472191 := bstep (se 1 (by rfl) ⟨354143, by rfl⟩ : syracuseStep 472191 = 708287) B708287
theorem B472347 : Blo 471786 472347 := bstep (se 1 (by rfl) ⟨354260, by rfl⟩ : syracuseStep 472347 = 708521) B708521
theorem B472479 : Blo 471786 472479 := bstep (se 1 (by rfl) ⟨354359, by rfl⟩ : syracuseStep 472479 = 708719) B708719
theorem B1062503 : Blo 471786 1062503 := bstep (se 1 (by rfl) ⟨796877, by rfl⟩ : syracuseStep 1062503 = 1593755) B1593755
theorem B472935 : Blo 471786 472935 := bstep (se 1 (by rfl) ⟨354701, by rfl⟩ : syracuseStep 472935 = 709403) B709403
theorem B472943 : Blo 471786 472943 := bstep (se 1 (by rfl) ⟨354707, by rfl⟩ : syracuseStep 472943 = 709415) B709415
theorem B4340087 : Blo 471786 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B1063403 : Blo 471786 1063403 := bstep (se 1 (by rfl) ⟨797552, by rfl⟩ : syracuseStep 1063403 = 1595105) B1595105
theorem B158088131 : Blo 471786 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B474215 : Blo 471786 474215 := bstep (se 1 (by rfl) ⟨355661, by rfl⟩ : syracuseStep 474215 = 711323) B711323
theorem B474527 : Blo 471786 474527 := bstep (se 1 (by rfl) ⟨355895, by rfl⟩ : syracuseStep 474527 = 711791) B711791
theorem B1195499 : Blo 471786 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B507551 : Blo 471786 507551 := bstep (se 1 (by rfl) ⟨380663, by rfl⟩ : syracuseStep 507551 = 761327) B761327
theorem B475007 : Blo 471786 475007 := bstep (se 1 (by rfl) ⟨356255, by rfl⟩ : syracuseStep 475007 = 712511) B712511
theorem B475295 : Blo 471786 475295 := bstep (se 1 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 475295 = 712943) B712943
theorem B475303 : Blo 471786 475303 := bstep (se 1 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 475303 = 712955) B712955
theorem B6177059 : Blo 471786 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B475551 : Blo 471786 475551 := bstep (se 1 (by rfl) ⟨356663, by rfl⟩ : syracuseStep 475551 = 713327) B713327
theorem B4867523 : Blo 471786 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B98158301 : Blo 471786 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B4311215 : Blo 471786 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1919209 : Blo 471786 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B9227591 : Blo 471786 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B1822675 : Blo 471786 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B1069559 : Blo 471786 1069559 := bstep (se 1 (by rfl) ⟨802169, by rfl⟩ : syracuseStep 1069559 = 1604339) B1604339
theorem B4117229 : Blo 471786 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B676603 : Blo 471786 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B709499 : Blo 471786 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B709823 : Blo 471786 709823 := bstep (se 1 (by rfl) ⟨532367, by rfl⟩ : syracuseStep 709823 = 1064735) B1064735
theorem B1201655 : Blo 471786 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B710633 : Blo 471786 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B1235567 : Blo 471786 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B7691111 : Blo 471786 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B2743577 : Blo 471786 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B711977 : Blo 471786 711977 := bstep (se 2 (by rfl) ⟨266991, by rfl⟩ : syracuseStep 711977 = 533983) B533983
theorem B711983 : Blo 471786 711983 := bstep (se 1 (by rfl) ⟨533987, by rfl⟩ : syracuseStep 711983 = 1067975) B1067975
theorem B1564343 : Blo 471786 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B712475 : Blo 471786 712475 := bstep (se 1 (by rfl) ⟨534356, by rfl⟩ : syracuseStep 712475 = 1068713) B1068713
theorem B712679 : Blo 471786 712679 := bstep (se 1 (by rfl) ⟨534509, by rfl⟩ : syracuseStep 712679 = 1069019) B1069019
theorem B712751 : Blo 471786 712751 := bstep (se 1 (by rfl) ⟨534563, by rfl⟩ : syracuseStep 712751 = 1069127) B1069127
theorem B713129 : Blo 471786 713129 := bstep (se 2 (by rfl) ⟨267423, by rfl⟩ : syracuseStep 713129 = 534847) B534847
theorem B1598183 : Blo 471786 1598183 := bstep (se 1 (by rfl) ⟨1198637, by rfl⟩ : syracuseStep 1598183 = 2397275) B2397275
theorem B1598291 : Blo 471786 1598291 := bstep (se 1 (by rfl) ⟨1198718, by rfl⟩ : syracuseStep 1598291 = 2397437) B2397437
theorem B4056749 : Blo 471786 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B3238643 : Blo 471786 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B2026529 : Blo 471786 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B3828883 : Blo 471786 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B1601153 : Blo 471786 1601153 := bstep (se 2 (by rfl) ⟨600432, by rfl⟩ : syracuseStep 1601153 = 1200865) B1200865
theorem B1601639 : Blo 471786 1601639 := bstep (se 1 (by rfl) ⟨1201229, by rfl⟩ : syracuseStep 1601639 = 2402459) B2402459
theorem B36008347 : Blo 471786 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B2028239 : Blo 471786 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B1700689 : Blo 471786 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B1701119 : Blo 471786 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B3601745 : Blo 471786 3601745 := bstep (se 2 (by rfl) ⟨1350654, by rfl⟩ : syracuseStep 3601745 = 2701309) B2701309
theorem B4322747 : Blo 471786 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B23099003 : Blo 471786 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B2423009 : Blo 471786 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2390795 : Blo 471786 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B3079403 : Blo 471786 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B2030939 : Blo 471786 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B1605257 : Blo 471786 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B9731755 : Blo 471786 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B1605473 : Blo 471786 1605473 := bstep (se 2 (by rfl) ⟨602052, by rfl⟩ : syracuseStep 1605473 = 1204105) B1204105
theorem B3245015 : Blo 471786 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B65438867 : Blo 471786 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B2558945 : Blo 471786 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B3608549 : Blo 471786 3608549 := bstep (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) B676603
theorem B2691103 : Blo 471786 2691103 := bstep (se 1 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 2691103 = 4036655) B4036655
theorem B823711 : Blo 471786 823711 := bstep (se 1 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 823711 = 1235567) B1235567
theorem B2430233 : Blo 471786 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B2692379 : Blo 471786 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B48011129 : Blo 471786 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B2267585 : Blo 471786 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B1351019 : Blo 471786 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B3285359 : Blo 471786 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B1352159 : Blo 471786 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B2401163 : Blo 471786 2401163 := bstep (se 1 (by rfl) ⟨1800872, by rfl⟩ : syracuseStep 2401163 = 3601745) B3601745
theorem B6824897 : Blo 471786 6824897 := bstep (se 2 (by rfl) ⟨2559336, by rfl⟩ : syracuseStep 6824897 = 5118673) B5118673
theorem B1615339 : Blo 471786 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B2893391 : Blo 471786 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B1353469 : Blo 471786 1353469 := bstep (se 3 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 1353469 = 507551) B507551
theorem B105392087 : Blo 471786 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B1353959 : Blo 471786 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B796999 : Blo 471786 796999 := bstep (se 1 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 796999 = 1195499) B1195499
theorem B5417927 : Blo 471786 5417927 := bstep (se 1 (by rfl) ⟨4063445, by rfl⟩ : syracuseStep 5417927 = 8126891) B8126891
theorem B10202219 : Blo 471786 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B1061801 : Blo 471786 1061801 := bstep (se 2 (by rfl) ⟨398175, by rfl⟩ : syracuseStep 1061801 = 796351) B796351
theorem B2569133 : Blo 471786 2569133 := bstep (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) B963425
theorem B2405375 : Blo 471786 2405375 := bstep (se 1 (by rfl) ⟨1804031, by rfl⟩ : syracuseStep 2405375 = 3608063) B3608063
theorem B5485907 : Blo 471786 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B472999 : Blo 471786 472999 := bstep (se 1 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 472999 = 709499) B709499
theorem B4536317 : Blo 471786 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B473215 : Blo 471786 473215 := bstep (se 1 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 473215 = 709823) B709823
theorem B801103 : Blo 471786 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B473755 : Blo 471786 473755 := bstep (se 1 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 473755 = 710633) B710633
theorem B5127407 : Blo 471786 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B8109395 : Blo 471786 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B474651 : Blo 471786 474651 := bstep (se 1 (by rfl) ⟨355988, by rfl⟩ : syracuseStep 474651 = 711977) B711977
theorem B474655 : Blo 471786 474655 := bstep (se 1 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 474655 = 711983) B711983
theorem B474983 : Blo 471786 474983 := bstep (se 1 (by rfl) ⟨356237, by rfl⟩ : syracuseStep 474983 = 712475) B712475
theorem B475119 : Blo 471786 475119 := bstep (se 1 (by rfl) ⟨356339, by rfl⟩ : syracuseStep 475119 = 712679) B712679
theorem B475167 : Blo 471786 475167 := bstep (se 1 (by rfl) ⟨356375, by rfl⟩ : syracuseStep 475167 = 712751) B712751
theorem B6045961 : Blo 471786 6045961 := bstep (se 2 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 6045961 = 4534471) B4534471
theorem B475419 : Blo 471786 475419 := bstep (se 1 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 475419 = 713129) B713129
theorem B3686849 : Blo 471786 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B1065455 : Blo 471786 1065455 := bstep (se 1 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 1065455 = 1598183) B1598183
theorem B1065527 : Blo 471786 1065527 := bstep (se 1 (by rfl) ⟨799145, by rfl⟩ : syracuseStep 1065527 = 1598291) B1598291
theorem B2015867 : Blo 471786 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B2704499 : Blo 471786 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B34981307 : Blo 471786 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B4048379 : Blo 471786 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B8636381 : Blo 471786 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B1067435 : Blo 471786 1067435 := bstep (se 1 (by rfl) ⟨800576, by rfl⟩ : syracuseStep 1067435 = 1601153) B1601153
theorem B1067759 : Blo 471786 1067759 := bstep (se 1 (by rfl) ⟨800819, by rfl⟩ : syracuseStep 1067759 = 1601639) B1601639
theorem B5623019 : Blo 471786 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B708335 : Blo 471786 708335 := bstep (se 1 (by rfl) ⟨531251, by rfl⟩ : syracuseStep 708335 = 1062503) B1062503
theorem B2019593 : Blo 471786 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B708935 : Blo 471786 708935 := bstep (se 1 (by rfl) ⟨531701, by rfl⟩ : syracuseStep 708935 = 1063403) B1063403
theorem B1593863 : Blo 471786 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B2052935 : Blo 471786 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1070171 : Blo 471786 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B1070315 : Blo 471786 1070315 := bstep (se 1 (by rfl) ⟨802736, by rfl⟩ : syracuseStep 1070315 = 1605473) B1605473
theorem B44914031 : Blo 471786 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B4118039 : Blo 471786 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B1726319 : Blo 471786 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B1202111 : Blo 471786 1202111 := bstep (se 1 (by rfl) ⟨901583, by rfl⟩ : syracuseStep 1202111 = 1803167) B1803167
theorem B7657577 : Blo 471786 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B19421471 : Blo 471786 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B809387 : Blo 471786 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B1137377 : Blo 471786 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B2874143 : Blo 471786 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1203295 : Blo 471786 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B6151727 : Blo 471786 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B1597751 : Blo 471786 1597751 := bstep (se 1 (by rfl) ⟨1198313, by rfl⟩ : syracuseStep 1597751 = 2396627) B2396627
theorem B713039 : Blo 471786 713039 := bstep (se 1 (by rfl) ⟨534779, by rfl⟩ : syracuseStep 713039 = 1069559) B1069559
theorem B2744819 : Blo 471786 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B79193213 : Blo 471786 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B5105177 : Blo 471786 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B1829051 : Blo 471786 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B1042895 : Blo 471786 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B1799081 : Blo 471786 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B1602503 : Blo 471786 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B2881831 : Blo 471786 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B15399335 : Blo 471786 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B12975673 : Blo 471786 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B2457899 : Blo 471786 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B8061281 : Blo 471786 8061281 := bstep (se 2 (by rfl) ⟨3022980, by rfl⟩ : syracuseStep 8061281 = 6045961) B6045961
theorem B2163343 : Blo 471786 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B1802999 : Blo 471786 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B5375645 : Blo 471786 5375645 := bstep (se 3 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 5375645 = 2015867) B2015867
theorem B1705963 : Blo 471786 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B1804625 : Blo 471786 1804625 := bstep (se 2 (by rfl) ⟨676734, by rfl⟩ : syracuseStep 1804625 = 1353469) B1353469
theorem B1346395 : Blo 471786 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B1511723 : Blo 471786 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B758251 : Blo 471786 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B4101151 : Blo 471786 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B52795475 : Blo 471786 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B70261391 : Blo 471786 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B1219367 : Blo 471786 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B3611951 : Blo 471786 3611951 := bstep (se 1 (by rfl) ⟨2708963, by rfl⟩ : syracuseStep 3611951 = 5417927) B5417927
theorem B3842441 : Blo 471786 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B1712755 : Blo 471786 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B3024211 : Blo 471786 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B10266223 : Blo 471786 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B3418271 : Blo 471786 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B43625911 : Blo 471786 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B2698919 : Blo 471786 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B3748679 : Blo 471786 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B472223 : Blo 471786 472223 := bstep (se 1 (by rfl) ⟨354167, by rfl⟩ : syracuseStep 472223 = 708335) B708335
theorem B2405699 : Blo 471786 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B472623 : Blo 471786 472623 := bstep (se 1 (by rfl) ⟨354467, by rfl⟩ : syracuseStep 472623 = 708935) B708935
theorem B1062575 : Blo 471786 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B1062665 : Blo 471786 1062665 := bstep (se 2 (by rfl) ⟨398499, by rfl⟩ : syracuseStep 1062665 = 796999) B796999
theorem B1620155 : Blo 471786 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B14629085 : Blo 471786 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B801407 : Blo 471786 801407 := bstep (se 1 (by rfl) ⟨601055, by rfl⟩ : syracuseStep 801407 = 1202111) B1202111
theorem B539591 : Blo 471786 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B1916095 : Blo 471786 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B4603517 : Blo 471786 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B3588137 : Blo 471786 3588137 := bstep (se 2 (by rfl) ⟨1345551, by rfl⟩ : syracuseStep 3588137 = 2691103) B2691103
theorem B1065167 : Blo 471786 1065167 := bstep (se 1 (by rfl) ⟨798875, by rfl⟩ : syracuseStep 1065167 = 1597751) B1597751
theorem B475359 : Blo 471786 475359 := bstep (se 1 (by rfl) ⟨356519, by rfl⟩ : syracuseStep 475359 = 713039) B713039
theorem B901439 : Blo 471786 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B1098281 : Blo 471786 1098281 := bstep (se 2 (by rfl) ⟨411855, by rfl⟩ : syracuseStep 1098281 = 823711) B823711
theorem B51790589 : Blo 471786 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B902639 : Blo 471786 902639 := bstep (se 1 (by rfl) ⟨676979, by rfl⟩ : syracuseStep 902639 = 1353959) B1353959
theorem B6801479 : Blo 471786 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B1068137 : Blo 471786 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B707867 : Blo 471786 707867 := bstep (se 1 (by rfl) ⟨530900, by rfl⟩ : syracuseStep 707867 = 1061801) B1061801
theorem B1199387 : Blo 471786 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B1068335 : Blo 471786 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B710303 : Blo 471786 710303 := bstep (se 1 (by rfl) ⟨532727, by rfl⟩ : syracuseStep 710303 = 1065455) B1065455
theorem B710351 : Blo 471786 710351 := bstep (se 1 (by rfl) ⟨532763, by rfl⟩ : syracuseStep 710351 = 1065527) B1065527
theorem B23320871 : Blo 471786 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B5757587 : Blo 471786 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B711623 : Blo 471786 711623 := bstep (se 1 (by rfl) ⟨533717, by rfl⟩ : syracuseStep 711623 = 1067435) B1067435
theorem B711839 : Blo 471786 711839 := bstep (se 1 (by rfl) ⟨533879, by rfl⟩ : syracuseStep 711839 = 1067759) B1067759
theorem B2153785 : Blo 471786 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B1368623 : Blo 471786 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B713447 : Blo 471786 713447 := bstep (se 1 (by rfl) ⟨535085, by rfl⟩ : syracuseStep 713447 = 1070171) B1070171
theorem B713543 : Blo 471786 713543 := bstep (se 1 (by rfl) ⟨535157, by rfl⟩ : syracuseStep 713543 = 1070315) B1070315
theorem B1794919 : Blo 471786 1794919 := bstep (se 1 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 1794919 = 2692379) B2692379
theorem B29942687 : Blo 471786 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B2745359 : Blo 471786 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B32007419 : Blo 471786 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B5105051 : Blo 471786 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B2190239 : Blo 471786 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B1829879 : Blo 471786 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1600775 : Blo 471786 1600775 := bstep (se 1 (by rfl) ⟨1200581, by rfl⟩ : syracuseStep 1600775 = 2401163) B2401163
theorem B4549931 : Blo 471786 4549931 := bstep (se 1 (by rfl) ⟨3412448, by rfl⟩ : syracuseStep 4549931 = 6824897) B6824897
theorem B3403451 : Blo 471786 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B1928927 : Blo 471786 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B2781053 : Blo 471786 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B1603583 : Blo 471786 1603583 := bstep (se 1 (by rfl) ⟨1202687, by rfl⟩ : syracuseStep 1603583 = 2405375) B2405375
theorem B3602717 : Blo 471786 3602717 := bstep (se 3 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 3602717 = 1351019) B1351019
theorem B1604393 : Blo 471786 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B17300897 : Blo 471786 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B5406263 : Blo 471786 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B2392091 : Blo 471786 2392091 := bstep (se 1 (by rfl) ⟨1794068, by rfl⟩ : syracuseStep 2392091 = 3588137) B3588137
theorem B1638599 : Blo 471786 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B5374187 : Blo 471786 5374187 := bstep (se 1 (by rfl) ⟨4030640, by rfl⟩ : syracuseStep 5374187 = 8061281) B8061281
theorem B2884457 : Blo 471786 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B2393225 : Blo 471786 2393225 := bstep (se 2 (by rfl) ⟨897459, by rfl⟩ : syracuseStep 2393225 = 1794919) B1794919
theorem B4032281 : Blo 471786 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B35196983 : Blo 471786 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B3838391 : Blo 471786 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B58167881 : Blo 471786 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B2561627 : Blo 471786 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B21338279 : Blo 471786 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B1219919 : Blo 471786 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B2268967 : Blo 471786 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B1285951 : Blo 471786 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B2499119 : Blo 471786 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B2401811 : Blo 471786 2401811 := bstep (se 1 (by rfl) ⟨1801358, by rfl⟩ : syracuseStep 2401811 = 3602717) B3602717
theorem B534271 : Blo 471786 534271 := bstep (se 1 (by rfl) ⟨400703, by rfl⟩ : syracuseStep 534271 = 801407) B801407
theorem B600959 : Blo 471786 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B732187 : Blo 471786 732187 := bstep (se 1 (by rfl) ⟨549140, by rfl⟩ : syracuseStep 732187 = 1098281) B1098281
theorem B601759 : Blo 471786 601759 := bstep (se 1 (by rfl) ⟨451319, by rfl⟩ : syracuseStep 601759 = 902639) B902639
theorem B3583763 : Blo 471786 3583763 := bstep (se 1 (by rfl) ⟨2687822, by rfl⟩ : syracuseStep 3583763 = 5375645) B5375645
theorem B4534319 : Blo 471786 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B471911 : Blo 471786 471911 := bstep (se 1 (by rfl) ⟨353933, by rfl⟩ : syracuseStep 471911 = 707867) B707867
theorem B799591 : Blo 471786 799591 := bstep (se 1 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 799591 = 1199387) B1199387
theorem B4044005 : Blo 471786 4044005 := bstep (se 4 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 4044005 = 758251) B758251
theorem B2274617 : Blo 471786 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B473535 : Blo 471786 473535 := bstep (se 1 (by rfl) ⟨355151, by rfl⟩ : syracuseStep 473535 = 710303) B710303
theorem B473567 : Blo 471786 473567 := bstep (se 1 (by rfl) ⟨355175, by rfl⟩ : syracuseStep 473567 = 710351) B710351
theorem B15547247 : Blo 471786 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B46840927 : Blo 471786 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B474415 : Blo 471786 474415 := bstep (se 1 (by rfl) ⟨355811, by rfl⟩ : syracuseStep 474415 = 711623) B711623
theorem B474559 : Blo 471786 474559 := bstep (se 1 (by rfl) ⟨355919, by rfl⟩ : syracuseStep 474559 = 711839) B711839
theorem B2407967 : Blo 471786 2407967 := bstep (se 1 (by rfl) ⟨1805975, by rfl⟩ : syracuseStep 2407967 = 3611951) B3611951
theorem B475631 : Blo 471786 475631 := bstep (se 1 (by rfl) ⟨356723, by rfl⟩ : syracuseStep 475631 = 713447) B713447
theorem B475695 : Blo 471786 475695 := bstep (se 1 (by rfl) ⟨356771, by rfl⟩ : syracuseStep 475695 = 713543) B713543
theorem B2278847 : Blo 471786 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B1460159 : Blo 471786 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B1067183 : Blo 471786 1067183 := bstep (se 1 (by rfl) ⟨800387, by rfl⟩ : syracuseStep 1067183 = 1600775) B1600775
theorem B3033287 : Blo 471786 3033287 := bstep (se 1 (by rfl) ⟨2274965, by rfl⟩ : syracuseStep 3033287 = 4549931) B4549931
theorem B1854035 : Blo 471786 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B708383 : Blo 471786 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B708443 : Blo 471786 708443 := bstep (se 1 (by rfl) ⟨531332, by rfl⟩ : syracuseStep 708443 = 1062665) B1062665
theorem B1069055 : Blo 471786 1069055 := bstep (se 1 (by rfl) ⟨801791, by rfl⟩ : syracuseStep 1069055 = 1603583) B1603583
theorem B9752723 : Blo 471786 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B2871713 : Blo 471786 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1069595 : Blo 471786 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B5755637 : Blo 471786 5755637 := bstep (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) B539591
theorem B3069011 : Blo 471786 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B710111 : Blo 471786 710111 := bstep (se 1 (by rfl) ⟨532583, by rfl⟩ : syracuseStep 710111 = 1065167) B1065167
theorem B1201999 : Blo 471786 1201999 := bstep (se 1 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 1201999 = 1802999) B1802999
theorem B34527059 : Blo 471786 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B2283673 : Blo 471786 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B1203083 : Blo 471786 1203083 := bstep (se 1 (by rfl) ⟨902312, by rfl⟩ : syracuseStep 1203083 = 1804625) B1804625
theorem B712091 : Blo 471786 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B13688297 : Blo 471786 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B712223 : Blo 471786 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B79847165 : Blo 471786 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B1007815 : Blo 471786 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B1795193 : Blo 471786 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B812911 : Blo 471786 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B912415 : Blo 471786 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1830239 : Blo 471786 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B3403367 : Blo 471786 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B5468201 : Blo 471786 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B1799279 : Blo 471786 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B1603799 : Blo 471786 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B1080103 : Blo 471786 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B2554793 : Blo 471786 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B11533931 : Blo 471786 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B3604175 : Blo 471786 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B1343753 : Blo 471786 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B2688187 : Blo 471786 2688187 := bstep (se 1 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 2688187 = 4032281) B4032281
theorem B1083881 : Blo 471786 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B23464655 : Blo 471786 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B2558927 : Blo 471786 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B1707751 : Blo 471786 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B1216553 : Blo 471786 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B14225519 : Blo 471786 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B1220159 : Blo 471786 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B2268911 : Blo 471786 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B3645467 : Blo 471786 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B3022879 : Blo 471786 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2696003 : Blo 471786 2696003 := bstep (se 1 (by rfl) ⟨2022002, by rfl⟩ : syracuseStep 2696003 = 4044005) B4044005
theorem B1516411 : Blo 471786 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B3253117 : Blo 471786 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B10364831 : Blo 471786 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B3025289 : Blo 471786 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B1714601 : Blo 471786 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B2402783 : Blo 471786 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B3582791 : Blo 471786 3582791 := bstep (se 1 (by rfl) ⟨2687093, by rfl⟩ : syracuseStep 3582791 = 5374187) B5374187
theorem B1519231 : Blo 471786 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B15348365 : Blo 471786 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B17478389 : Blo 471786 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B472255 : Blo 471786 472255 := bstep (se 1 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 472255 = 708383) B708383
theorem B472295 : Blo 471786 472295 := bstep (se 1 (by rfl) ⟨354221, by rfl⟩ : syracuseStep 472295 = 708443) B708443
theorem B6501815 : Blo 471786 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B1914475 : Blo 471786 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B38778587 : Blo 471786 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B2046007 : Blo 471786 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B473407 : Blo 471786 473407 := bstep (se 1 (by rfl) ⟨355055, by rfl⟩ : syracuseStep 473407 = 710111) B710111
theorem B23018039 : Blo 471786 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B802055 : Blo 471786 802055 := bstep (se 1 (by rfl) ⟨601541, by rfl⟩ : syracuseStep 802055 = 1203083) B1203083
theorem B802345 : Blo 471786 802345 := bstep (se 2 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 802345 = 601759) B601759
theorem B474727 : Blo 471786 474727 := bstep (se 1 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 474727 = 712091) B712091
theorem B9125531 : Blo 471786 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B474815 : Blo 471786 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B1196795 : Blo 471786 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B1066121 : Blo 471786 1066121 := bstep (se 2 (by rfl) ⟨399795, by rfl⟩ : syracuseStep 1066121 = 799591) B799591
theorem B1199519 : Blo 471786 1199519 := bstep (se 1 (by rfl) ⟨899639, by rfl⟩ : syracuseStep 1199519 = 1799279) B1799279
theorem B1069199 : Blo 471786 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B7689287 : Blo 471786 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B1594727 : Blo 471786 1594727 := bstep (se 1 (by rfl) ⟨1196045, by rfl⟩ : syracuseStep 1594727 = 2392091) B2392091
theorem B1595483 : Blo 471786 1595483 := bstep (se 1 (by rfl) ⟨1196612, by rfl⟩ : syracuseStep 1595483 = 2393225) B2393225
theorem B973439 : Blo 471786 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B711455 : Blo 471786 711455 := bstep (se 1 (by rfl) ⟨533591, by rfl⟩ : syracuseStep 711455 = 1067183) B1067183
theorem B2022191 : Blo 471786 2022191 := bstep (se 1 (by rfl) ⟨1516643, by rfl⟩ : syracuseStep 2022191 = 3033287) B3033287
theorem B1236023 : Blo 471786 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B7691885 : Blo 471786 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B712361 : Blo 471786 712361 := bstep (se 2 (by rfl) ⟨267135, by rfl⟩ : syracuseStep 712361 = 534271) B534271
theorem B712703 : Blo 471786 712703 := bstep (se 1 (by rfl) ⟨534527, by rfl⟩ : syracuseStep 712703 = 1069055) B1069055
theorem B713063 : Blo 471786 713063 := bstep (se 1 (by rfl) ⟨534797, by rfl⟩ : syracuseStep 713063 = 1069595) B1069595
theorem B976249 : Blo 471786 976249 := bstep (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) B732187
theorem B1666079 : Blo 471786 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B1601207 : Blo 471786 1601207 := bstep (se 1 (by rfl) ⟨1200905, by rfl⟩ : syracuseStep 1601207 = 2401811) B2401811
theorem B1602557 : Blo 471786 1602557 := bstep (se 3 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 1602557 = 600959) B600959
theorem B1602665 : Blo 471786 1602665 := bstep (se 2 (by rfl) ⟨600999, by rfl⟩ : syracuseStep 1602665 = 1201999) B1201999
theorem B2389175 : Blo 471786 2389175 := bstep (se 1 (by rfl) ⟨1791881, by rfl⟩ : syracuseStep 2389175 = 3583763) B3583763
theorem B3044897 : Blo 471786 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B1440137 : Blo 471786 1440137 := bstep (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) B1080103
theorem B62454569 : Blo 471786 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B1703195 : Blo 471786 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B212925773 : Blo 471786 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B1605311 : Blo 471786 1605311 := bstep (se 1 (by rfl) ⟨1203983, by rfl⟩ : syracuseStep 1605311 = 2407967) B2407967
theorem B4030505 : Blo 471786 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B3244141 : Blo 471786 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B1705951 : Blo 471786 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B1348127 : Blo 471786 1348127 := bstep (se 1 (by rfl) ⟨1011095, by rfl⟩ : syracuseStep 1348127 = 2022191) B2022191
theorem B824015 : Blo 471786 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B1512607 : Blo 471786 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B3840365 : Blo 471786 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B2890349 : Blo 471786 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B2728009 : Blo 471786 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B10232243 : Blo 471786 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B4334543 : Blo 471786 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B15345359 : Blo 471786 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B534703 : Blo 471786 534703 := bstep (se 1 (by rfl) ⟨401027, by rfl⟩ : syracuseStep 534703 = 802055) B802055
theorem B895835 : Blo 471786 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B797863 : Blo 471786 797863 := bstep (se 1 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 797863 = 1196795) B1196795
theorem B4337489 : Blo 471786 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B3584249 : Blo 471786 3584249 := bstep (se 2 (by rfl) ⟨1344093, by rfl⟩ : syracuseStep 3584249 = 2688187) B2688187
theorem B15643103 : Blo 471786 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B46609037 : Blo 471786 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B799679 : Blo 471786 799679 := bstep (se 1 (by rfl) ⟨599759, by rfl⟩ : syracuseStep 799679 = 1199519) B1199519
theorem B9483679 : Blo 471786 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B1063151 : Blo 471786 1063151 := bstep (se 1 (by rfl) ⟨797363, by rfl⟩ : syracuseStep 1063151 = 1594727) B1594727
theorem B1063655 : Blo 471786 1063655 := bstep (se 1 (by rfl) ⟨797741, by rfl⟩ : syracuseStep 1063655 = 1595483) B1595483
theorem B474303 : Blo 471786 474303 := bstep (se 1 (by rfl) ⟨355727, by rfl⟩ : syracuseStep 474303 = 711455) B711455
theorem B2277001 : Blo 471786 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B5127923 : Blo 471786 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B474907 : Blo 471786 474907 := bstep (se 1 (by rfl) ⟨356180, by rfl⟩ : syracuseStep 474907 = 712361) B712361
theorem B475135 : Blo 471786 475135 := bstep (se 1 (by rfl) ⟨356351, by rfl⟩ : syracuseStep 475135 = 712703) B712703
theorem B475375 : Blo 471786 475375 := bstep (se 1 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 475375 = 713063) B713063
theorem B2016859 : Blo 471786 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B166545517 : Blo 471786 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B1067471 : Blo 471786 1067471 := bstep (se 1 (by rfl) ⟨800603, by rfl⟩ : syracuseStep 1067471 = 1601207) B1601207
theorem B1068371 : Blo 471786 1068371 := bstep (se 1 (by rfl) ⟨801278, by rfl⟩ : syracuseStep 1068371 = 1602557) B1602557
theorem B1068443 : Blo 471786 1068443 := bstep (se 1 (by rfl) ⟨801332, by rfl⟩ : syracuseStep 1068443 = 1602665) B1602665
theorem B1592783 : Blo 471786 1592783 := bstep (se 1 (by rfl) ⟨1194587, by rfl⟩ : syracuseStep 1592783 = 2389175) B2389175
theorem B1069793 : Blo 471786 1069793 := bstep (se 2 (by rfl) ⟨401172, by rfl⟩ : syracuseStep 1069793 = 802345) B802345
theorem B1135463 : Blo 471786 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B6083687 : Blo 471786 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B1070207 : Blo 471786 1070207 := bstep (se 1 (by rfl) ⟨802655, by rfl⟩ : syracuseStep 1070207 = 1605311) B1605311
theorem B38884981 : Blo 471786 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B710747 : Blo 471786 710747 := bstep (se 1 (by rfl) ⟨533060, by rfl⟩ : syracuseStep 710747 = 1066121) B1066121
theorem B1301665 : Blo 471786 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B712799 : Blo 471786 712799 := bstep (se 1 (by rfl) ⟨534599, by rfl⟩ : syracuseStep 712799 = 1069199) B1069199
theorem B20504765 : Blo 471786 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B648959 : Blo 471786 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B8087525 : Blo 471786 8087525 := bstep (se 4 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 8087525 = 1516411) B1516411
theorem B2025641 : Blo 471786 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B813439 : Blo 471786 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B1797335 : Blo 471786 1797335 := bstep (se 1 (by rfl) ⟨1348001, by rfl⟩ : syracuseStep 1797335 = 2696003) B2696003
theorem B6909887 : Blo 471786 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B1143067 : Blo 471786 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B1601855 : Blo 471786 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B2388527 : Blo 471786 2388527 := bstep (se 1 (by rfl) ⟨1791395, by rfl⟩ : syracuseStep 2388527 = 3582791) B3582791
theorem B1110719 : Blo 471786 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2552633 : Blo 471786 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B2029931 : Blo 471786 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B25852391 : Blo 471786 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B141950515 : Blo 471786 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B2687003 : Blo 471786 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B4325521 : Blo 471786 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B14549381 : Blo 471786 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B41714941 : Blo 471786 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B2689145 : Blo 471786 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B1084585 : Blo 471786 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B2560243 : Blo 471786 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B13669843 : Blo 471786 13669843 := bstep (se 1 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 13669843 = 20504765) B20504765
theorem B6821495 : Blo 471786 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B2889695 : Blo 471786 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B10230239 : Blo 471786 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B1350427 : Blo 471786 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B597223 : Blo 471786 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B51846641 : Blo 471786 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B2891659 : Blo 471786 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B31072691 : Blo 471786 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B533119 : Blo 471786 533119 := bstep (se 1 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 533119 = 799679) B799679
theorem B1353287 : Blo 471786 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B3418615 : Blo 471786 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B18426365 : Blo 471786 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B2961917 : Blo 471786 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B1061855 : Blo 471786 1061855 := bstep (se 1 (by rfl) ⟨796391, by rfl⟩ : syracuseStep 1061855 = 1592783) B1592783
theorem B2274601 : Blo 471786 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B898751 : Blo 471786 898751 := bstep (se 1 (by rfl) ⟨674063, by rfl⟩ : syracuseStep 898751 = 1348127) B1348127
theorem B473831 : Blo 471786 473831 := bstep (se 1 (by rfl) ⟨355373, by rfl⟩ : syracuseStep 473831 = 710747) B710747
theorem B1063817 : Blo 471786 1063817 := bstep (se 2 (by rfl) ⟨398931, by rfl⟩ : syracuseStep 1063817 = 797863) B797863
theorem B475199 : Blo 471786 475199 := bstep (se 1 (by rfl) ⟨356399, by rfl⟩ : syracuseStep 475199 = 712799) B712799
theorem B1524089 : Blo 471786 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B5391683 : Blo 471786 5391683 := bstep (se 1 (by rfl) ⟨4043762, by rfl⟩ : syracuseStep 5391683 = 8087525) B8087525
theorem B2016809 : Blo 471786 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B1198223 : Blo 471786 1198223 := bstep (se 1 (by rfl) ⟨898667, by rfl⟩ : syracuseStep 1198223 = 1797335) B1797335
theorem B50579621 : Blo 471786 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B1067903 : Blo 471786 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B1592351 : Blo 471786 1592351 := bstep (se 1 (by rfl) ⟨1194263, by rfl⟩ : syracuseStep 1592351 = 2388527) B2388527
theorem B12111605 : Blo 471786 12111605 := bstep (se 5 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 12111605 = 1135463) B1135463
theorem B708767 : Blo 471786 708767 := bstep (se 1 (by rfl) ⟨531575, by rfl⟩ : syracuseStep 708767 = 1063151) B1063151
theorem B709103 : Blo 471786 709103 := bstep (se 1 (by rfl) ⟨531827, by rfl⟩ : syracuseStep 709103 = 1063655) B1063655
theorem B3036001 : Blo 471786 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B711647 : Blo 471786 711647 := bstep (se 1 (by rfl) ⟨533735, by rfl⟩ : syracuseStep 711647 = 1067471) B1067471
theorem B712247 : Blo 471786 712247 := bstep (se 1 (by rfl) ⟨534185, by rfl⟩ : syracuseStep 712247 = 1068371) B1068371
theorem B712295 : Blo 471786 712295 := bstep (se 1 (by rfl) ⟨534221, by rfl⟩ : syracuseStep 712295 = 1068443) B1068443
theorem B222060689 : Blo 471786 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B712937 : Blo 471786 712937 := bstep (se 2 (by rfl) ⟨267351, by rfl⟩ : syracuseStep 712937 = 534703) B534703
theorem B549343 : Blo 471786 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B713195 : Blo 471786 713195 := bstep (se 1 (by rfl) ⟨534896, by rfl⟩ : syracuseStep 713195 = 1069793) B1069793
theorem B4055791 : Blo 471786 4055791 := bstep (se 1 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 4055791 = 6083687) B6083687
theorem B713471 : Blo 471786 713471 := bstep (se 1 (by rfl) ⟨535103, by rfl⟩ : syracuseStep 713471 = 1070207) B1070207
theorem B1926899 : Blo 471786 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B1730557 : Blo 471786 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B2389499 : Blo 471786 2389499 := bstep (se 1 (by rfl) ⟨1792124, by rfl⟩ : syracuseStep 2389499 = 3584249) B3584249
theorem B1701755 : Blo 471786 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1735553 : Blo 471786 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B17234927 : Blo 471786 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B189267353 : Blo 471786 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B5767361 : Blo 471786 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B1016059 : Blo 471786 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B9699587 : Blo 471786 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B5407721 : Blo 471786 5407721 := bstep (se 2 (by rfl) ⟨2027895, by rfl⟩ : syracuseStep 5407721 = 4055791) B4055791
theorem B1344539 : Blo 471786 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B33719747 : Blo 471786 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B4558153 : Blo 471786 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B1446113 : Blo 471786 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B3413657 : Blo 471786 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B1284599 : Blo 471786 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B18226457 : Blo 471786 18226457 := bstep (se 2 (by rfl) ⟨6834921, by rfl⟩ : syracuseStep 18226457 = 13669843) B13669843
theorem B4628141 : Blo 471786 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B1974611 : Blo 471786 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B599167 : Blo 471786 599167 := bstep (se 1 (by rfl) ⟨449375, by rfl⟩ : syracuseStep 599167 = 898751) B898751
theorem B796297 : Blo 471786 796297 := bstep (se 2 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 796297 = 597223) B597223
theorem B798815 : Blo 471786 798815 := bstep (se 1 (by rfl) ⟨599111, by rfl⟩ : syracuseStep 798815 = 1198223) B1198223
theorem B55619921 : Blo 471786 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1061567 : Blo 471786 1061567 := bstep (se 1 (by rfl) ⟨796175, by rfl⟩ : syracuseStep 1061567 = 1592351) B1592351
theorem B8074403 : Blo 471786 8074403 := bstep (se 1 (by rfl) ⟨6055802, by rfl⟩ : syracuseStep 8074403 = 12111605) B12111605
theorem B2929829 : Blo 471786 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B2307409 : Blo 471786 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B472511 : Blo 471786 472511 := bstep (se 1 (by rfl) ⟨354383, by rfl⟩ : syracuseStep 472511 = 708767) B708767
theorem B472735 : Blo 471786 472735 := bstep (se 1 (by rfl) ⟨354551, by rfl⟩ : syracuseStep 472735 = 709103) B709103
theorem B474431 : Blo 471786 474431 := bstep (se 1 (by rfl) ⟨355823, by rfl⟩ : syracuseStep 474431 = 711647) B711647
theorem B474831 : Blo 471786 474831 := bstep (se 1 (by rfl) ⟨356123, by rfl⟩ : syracuseStep 474831 = 712247) B712247
theorem B474863 : Blo 471786 474863 := bstep (se 1 (by rfl) ⟨356147, by rfl⟩ : syracuseStep 474863 = 712295) B712295
theorem B475291 : Blo 471786 475291 := bstep (se 1 (by rfl) ⟨356468, by rfl⟩ : syracuseStep 475291 = 712937) B712937
theorem B475463 : Blo 471786 475463 := bstep (se 1 (by rfl) ⟨356597, by rfl⟩ : syracuseStep 475463 = 713195) B713195
theorem B475647 : Blo 471786 475647 := bstep (se 1 (by rfl) ⟨356735, by rfl⟩ : syracuseStep 475647 = 713471) B713471
theorem B902191 : Blo 471786 902191 := bstep (se 1 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 902191 = 1353287) B1353287
theorem B4048001 : Blo 471786 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B27280637 : Blo 471786 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B3032801 : Blo 471786 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B707903 : Blo 471786 707903 := bstep (se 1 (by rfl) ⟨530927, by rfl⟩ : syracuseStep 707903 = 1061855) B1061855
theorem B1592999 : Blo 471786 1592999 := bstep (se 1 (by rfl) ⟨1194749, by rfl⟩ : syracuseStep 1592999 = 2389499) B2389499
theorem B1134503 : Blo 471786 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B709211 : Blo 471786 709211 := bstep (se 1 (by rfl) ⟨531908, by rfl⟩ : syracuseStep 709211 = 1063817) B1063817
theorem B11489951 : Blo 471786 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B126178235 : Blo 471786 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B3855545 : Blo 471786 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B1791335 : Blo 471786 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B710825 : Blo 471786 710825 := bstep (se 2 (by rfl) ⟨266559, by rfl⟩ : syracuseStep 710825 = 533119) B533119
theorem B3594455 : Blo 471786 3594455 := bstep (se 1 (by rfl) ⟨2695841, by rfl⟩ : syracuseStep 3594455 = 5391683) B5391683
theorem B82860509 : Blo 471786 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B1792763 : Blo 471786 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B711935 : Blo 471786 711935 := bstep (se 1 (by rfl) ⟨533951, by rfl⟩ : syracuseStep 711935 = 1067903) B1067903
theorem B4547663 : Blo 471786 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B1926463 : Blo 471786 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B34564427 : Blo 471786 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B148040459 : Blo 471786 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B12284243 : Blo 471786 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B1800569 : Blo 471786 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B3605147 : Blo 471786 3605147 := bstep (se 1 (by rfl) ⟨2703860, by rfl⟩ : syracuseStep 3605147 = 5407721) B5407721
theorem B18187091 : Blo 471786 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B30639869 : Blo 471786 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B756335 : Blo 471786 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B84118823 : Blo 471786 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B89919325 : Blo 471786 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B2396303 : Blo 471786 2396303 := bstep (se 1 (by rfl) ⟨1797227, by rfl⟩ : syracuseStep 2396303 = 3594455) B3594455
theorem B856399 : Blo 471786 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B3085427 : Blo 471786 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1316407 : Blo 471786 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B23042951 : Blo 471786 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B532543 : Blo 471786 532543 := bstep (se 1 (by rfl) ⟨399407, by rfl⟩ : syracuseStep 532543 = 798815) B798815
theorem B5382935 : Blo 471786 5382935 := bstep (se 1 (by rfl) ⟨4037201, by rfl⟩ : syracuseStep 5382935 = 8074403) B8074403
theorem B3844907 : Blo 471786 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B6466391 : Blo 471786 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B1354745 : Blo 471786 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B896359 : Blo 471786 896359 := bstep (se 1 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 896359 = 1344539) B1344539
theorem B2698667 : Blo 471786 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B798889 : Blo 471786 798889 := bstep (se 2 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 798889 = 599167) B599167
theorem B2568617 : Blo 471786 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B1061729 : Blo 471786 1061729 := bstep (se 2 (by rfl) ⟨398148, by rfl⟩ : syracuseStep 1061729 = 796297) B796297
theorem B471935 : Blo 471786 471935 := bstep (se 1 (by rfl) ⟨353951, by rfl⟩ : syracuseStep 471935 = 707903) B707903
theorem B1061999 : Blo 471786 1061999 := bstep (se 1 (by rfl) ⟨796499, by rfl⟩ : syracuseStep 1061999 = 1592999) B1592999
theorem B964075 : Blo 471786 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B472807 : Blo 471786 472807 := bstep (se 1 (by rfl) ⟨354605, by rfl⟩ : syracuseStep 472807 = 709211) B709211
theorem B7812877 : Blo 471786 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B2570363 : Blo 471786 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B1194223 : Blo 471786 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B2275771 : Blo 471786 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B473883 : Blo 471786 473883 := bstep (se 1 (by rfl) ⟨355412, by rfl⟩ : syracuseStep 473883 = 710825) B710825
theorem B6077537 : Blo 471786 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B1195175 : Blo 471786 1195175 := bstep (se 1 (by rfl) ⟨896381, by rfl⟩ : syracuseStep 1195175 = 1792763) B1792763
theorem B474623 : Blo 471786 474623 := bstep (se 1 (by rfl) ⟨355967, by rfl⟩ : syracuseStep 474623 = 711935) B711935
theorem B3031775 : Blo 471786 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B12306181 : Blo 471786 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B37079947 : Blo 471786 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B707711 : Blo 471786 707711 := bstep (se 1 (by rfl) ⟨530783, by rfl⟩ : syracuseStep 707711 = 1061567) B1061567
theorem B1200379 : Blo 471786 1200379 := bstep (se 1 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 1200379 = 1800569) B1800569
theorem B2021867 : Blo 471786 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B1202921 : Blo 471786 1202921 := bstep (se 2 (by rfl) ⟨451095, by rfl⟩ : syracuseStep 1202921 = 902191) B902191
theorem B55240339 : Blo 471786 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B12150971 : Blo 471786 12150971 := bstep (se 1 (by rfl) ⟨9113228, by rfl⟩ : syracuseStep 12150971 = 18226457) B18226457
theorem B98693639 : Blo 471786 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B8189495 : Blo 471786 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B12124727 : Blo 471786 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B1347911 : Blo 471786 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B197759717 : Blo 471786 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B8100647 : Blo 471786 8100647 := bstep (se 1 (by rfl) ⟨6075485, by rfl⟩ : syracuseStep 8100647 = 12150971) B12150971
theorem B2563271 : Blo 471786 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B1285433 : Blo 471786 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B1712411 : Blo 471786 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B1713575 : Blo 471786 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B479569733 : Blo 471786 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B796783 : Blo 471786 796783 := bstep (se 1 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 796783 = 1195175) B1195175
theorem B2403431 : Blo 471786 2403431 := bstep (se 1 (by rfl) ⟨1802573, by rfl⟩ : syracuseStep 2403431 = 3605147) B3605147
theorem B20426579 : Blo 471786 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B471807 : Blo 471786 471807 := bstep (se 1 (by rfl) ⟨353855, by rfl⟩ : syracuseStep 471807 = 707711) B707711
theorem B56079215 : Blo 471786 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B1195145 : Blo 471786 1195145 := bstep (se 2 (by rfl) ⟨448179, by rfl⟩ : syracuseStep 1195145 = 896359) B896359
theorem B801947 : Blo 471786 801947 := bstep (se 1 (by rfl) ⟨601460, by rfl⟩ : syracuseStep 801947 = 1202921) B1202921
theorem B1065185 : Blo 471786 1065185 := bstep (se 2 (by rfl) ⟨399444, by rfl⟩ : syracuseStep 1065185 = 798889) B798889
theorem B3588623 : Blo 471786 3588623 := bstep (se 1 (by rfl) ⟨2691467, by rfl⟩ : syracuseStep 3588623 = 5382935) B5382935
theorem B2016893 : Blo 471786 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B4310927 : Blo 471786 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B903163 : Blo 471786 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B1755209 : Blo 471786 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B1592297 : Blo 471786 1592297 := bstep (se 2 (by rfl) ⟨597111, by rfl⟩ : syracuseStep 1592297 = 1194223) B1194223
theorem B707819 : Blo 471786 707819 := bstep (se 1 (by rfl) ⟨530864, by rfl⟩ : syracuseStep 707819 = 1061729) B1061729
theorem B3034361 : Blo 471786 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B707999 : Blo 471786 707999 := bstep (se 1 (by rfl) ⟨530999, by rfl⟩ : syracuseStep 707999 = 1061999) B1061999
theorem B5459663 : Blo 471786 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B4051691 : Blo 471786 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B710057 : Blo 471786 710057 := bstep (se 2 (by rfl) ⟨266271, by rfl⟩ : syracuseStep 710057 = 532543) B532543
theorem B2021183 : Blo 471786 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B73653785 : Blo 471786 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B16408241 : Blo 471786 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B1597535 : Blo 471786 1597535 := bstep (se 1 (by rfl) ⟨1198151, by rfl⟩ : syracuseStep 1597535 = 2396303) B2396303
theorem B2056951 : Blo 471786 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B15361967 : Blo 471786 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B1600505 : Blo 471786 1600505 := bstep (se 2 (by rfl) ⟨600189, by rfl⟩ : syracuseStep 1600505 = 1200379) B1200379
theorem B1141865 : Blo 471786 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B1799111 : Blo 471786 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B10417169 : Blo 471786 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B65795759 : Blo 471786 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B2392415 : Blo 471786 2392415 := bstep (se 1 (by rfl) ⟨1794311, by rfl⟩ : syracuseStep 2392415 = 3588623) B3588623
theorem B1344595 : Blo 471786 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B1347455 : Blo 471786 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B1708847 : Blo 471786 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B856955 : Blo 471786 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B761243 : Blo 471786 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B14559101 : Blo 471786 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B796763 : Blo 471786 796763 := bstep (se 1 (by rfl) ⟨597572, by rfl⟩ : syracuseStep 796763 = 1195145) B1195145
theorem B534631 : Blo 471786 534631 := bstep (se 1 (by rfl) ⟨400973, by rfl⟩ : syracuseStep 534631 = 801947) B801947
theorem B1061531 : Blo 471786 1061531 := bstep (se 1 (by rfl) ⟨796148, by rfl⟩ : syracuseStep 1061531 = 1592297) B1592297
theorem B471879 : Blo 471786 471879 := bstep (se 1 (by rfl) ⟨353909, by rfl⟩ : syracuseStep 471879 = 707819) B707819
theorem B471999 : Blo 471786 471999 := bstep (se 1 (by rfl) ⟨353999, by rfl⟩ : syracuseStep 471999 = 707999) B707999
theorem B1062377 : Blo 471786 1062377 := bstep (se 2 (by rfl) ⟨398391, by rfl⟩ : syracuseStep 1062377 = 796783) B796783
theorem B898607 : Blo 471786 898607 := bstep (se 1 (by rfl) ⟨673955, by rfl⟩ : syracuseStep 898607 = 1347911) B1347911
theorem B131839811 : Blo 471786 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B2701127 : Blo 471786 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B473371 : Blo 471786 473371 := bstep (se 1 (by rfl) ⟨355028, by rfl⟩ : syracuseStep 473371 = 710057) B710057
theorem B4569533 : Blo 471786 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B49102523 : Blo 471786 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B1065023 : Blo 471786 1065023 := bstep (se 1 (by rfl) ⟨798767, by rfl⟩ : syracuseStep 1065023 = 1597535) B1597535
theorem B10241311 : Blo 471786 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B1067003 : Blo 471786 1067003 := bstep (se 1 (by rfl) ⟨800252, by rfl⟩ : syracuseStep 1067003 = 1600505) B1600505
theorem B13617719 : Blo 471786 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B1199407 : Blo 471786 1199407 := bstep (se 1 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 1199407 = 1799111) B1799111
theorem B43863839 : Blo 471786 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B710123 : Blo 471786 710123 := bstep (se 1 (by rfl) ⟨532592, by rfl⟩ : syracuseStep 710123 = 1065185) B1065185
theorem B8083151 : Blo 471786 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B2742601 : Blo 471786 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B2873951 : Blo 471786 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B2022907 : Blo 471786 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B1204217 : Blo 471786 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B5400431 : Blo 471786 5400431 := bstep (se 1 (by rfl) ⟨4050323, by rfl⟩ : syracuseStep 5400431 = 8100647) B8100647
theorem B10938827 : Blo 471786 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1141607 : Blo 471786 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B4680557 : Blo 471786 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B319713155 : Blo 471786 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B1602287 : Blo 471786 1602287 := bstep (se 1 (by rfl) ⟨1201715, by rfl⟩ : syracuseStep 1602287 = 2403431) B2403431
theorem B37386143 : Blo 471786 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B6944779 : Blo 471786 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B9078479 : Blo 471786 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B29170205 : Blo 471786 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B9706067 : Blo 471786 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B531175 : Blo 471786 531175 := bstep (se 1 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 531175 = 796763) B796763
theorem B761071 : Blo 471786 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B3120371 : Blo 471786 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B599071 : Blo 471786 599071 := bstep (se 1 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 599071 = 898607) B898607
theorem B87893207 : Blo 471786 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B2697209 : Blo 471786 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B29242559 : Blo 471786 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B898303 : Blo 471786 898303 := bstep (se 1 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 898303 = 1347455) B1347455
theorem B571303 : Blo 471786 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B473415 : Blo 471786 473415 := bstep (se 1 (by rfl) ⟨355061, by rfl⟩ : syracuseStep 473415 = 710123) B710123
theorem B5388767 : Blo 471786 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B1915967 : Blo 471786 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B802811 : Blo 471786 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B213142103 : Blo 471786 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B9259705 : Blo 471786 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B3656801 : Blo 471786 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B707687 : Blo 471786 707687 := bstep (se 1 (by rfl) ⟨530765, by rfl⟩ : syracuseStep 707687 = 1061531) B1061531
theorem B1068191 : Blo 471786 1068191 := bstep (se 1 (by rfl) ⟨801143, by rfl⟩ : syracuseStep 1068191 = 1602287) B1602287
theorem B708251 : Blo 471786 708251 := bstep (se 1 (by rfl) ⟨531188, by rfl⟩ : syracuseStep 708251 = 1062377) B1062377
theorem B24924095 : Blo 471786 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B710015 : Blo 471786 710015 := bstep (se 1 (by rfl) ⟨532511, by rfl⟩ : syracuseStep 710015 = 1065023) B1065023
theorem B1594943 : Blo 471786 1594943 := bstep (se 1 (by rfl) ⟨1196207, by rfl⟩ : syracuseStep 1594943 = 2392415) B2392415
theorem B711335 : Blo 471786 711335 := bstep (se 1 (by rfl) ⟨533501, by rfl⟩ : syracuseStep 711335 = 1067003) B1067003
theorem B1792793 : Blo 471786 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B13655081 : Blo 471786 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B712841 : Blo 471786 712841 := bstep (se 2 (by rfl) ⟨267315, by rfl⟩ : syracuseStep 712841 = 534631) B534631
theorem B1139231 : Blo 471786 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B1599209 : Blo 471786 1599209 := bstep (se 2 (by rfl) ⟨599703, by rfl⟩ : syracuseStep 1599209 = 1199407) B1199407
theorem B3600287 : Blo 471786 3600287 := bstep (se 1 (by rfl) ⟨2700215, by rfl⟩ : syracuseStep 3600287 = 5400431) B5400431
theorem B2029981 : Blo 471786 2029981 := bstep (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) B761243
theorem B1800751 : Blo 471786 1800751 := bstep (se 1 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 1800751 = 2701127) B2701127
theorem B3046355 : Blo 471786 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B32735015 : Blo 471786 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B16616063 : Blo 471786 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B58595471 : Blo 471786 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B761737 : Blo 471786 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B2400191 : Blo 471786 2400191 := bstep (se 1 (by rfl) ⟨1800143, by rfl⟩ : syracuseStep 2400191 = 3600287) B3600287
theorem B2401001 : Blo 471786 2401001 := bstep (se 2 (by rfl) ⟨900375, by rfl⟩ : syracuseStep 2401001 = 1800751) B1800751
theorem B535207 : Blo 471786 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B798761 : Blo 471786 798761 := bstep (se 2 (by rfl) ⟨299535, by rfl⟩ : syracuseStep 798761 = 599071) B599071
theorem B142094735 : Blo 471786 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B2437867 : Blo 471786 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B471791 : Blo 471786 471791 := bstep (se 1 (by rfl) ⟨353843, by rfl⟩ : syracuseStep 471791 = 707687) B707687
theorem B472167 : Blo 471786 472167 := bstep (se 1 (by rfl) ⟨354125, by rfl⟩ : syracuseStep 472167 = 708251) B708251
theorem B473343 : Blo 471786 473343 := bstep (se 1 (by rfl) ⟨355007, by rfl⟩ : syracuseStep 473343 = 710015) B710015
theorem B1063295 : Blo 471786 1063295 := bstep (se 1 (by rfl) ⟨797471, by rfl⟩ : syracuseStep 1063295 = 1594943) B1594943
theorem B19446803 : Blo 471786 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B6470711 : Blo 471786 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B474223 : Blo 471786 474223 := bstep (se 1 (by rfl) ⟨355667, by rfl⟩ : syracuseStep 474223 = 711335) B711335
theorem B1195195 : Blo 471786 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B2080247 : Blo 471786 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B475227 : Blo 471786 475227 := bstep (se 1 (by rfl) ⟨356420, by rfl⟩ : syracuseStep 475227 = 712841) B712841
theorem B1066139 : Blo 471786 1066139 := bstep (se 1 (by rfl) ⟨799604, by rfl⟩ : syracuseStep 1066139 = 1599209) B1599209
theorem B1197737 : Blo 471786 1197737 := bstep (se 2 (by rfl) ⟨449151, by rfl⟩ : syracuseStep 1197737 = 898303) B898303
theorem B2706641 : Blo 471786 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B708233 : Blo 471786 708233 := bstep (se 2 (by rfl) ⟨265587, by rfl⟩ : syracuseStep 708233 = 531175) B531175
theorem B3592511 : Blo 471786 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B6052319 : Blo 471786 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B3037949 : Blo 471786 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B712127 : Blo 471786 712127 := bstep (se 1 (by rfl) ⟨534095, by rfl⟩ : syracuseStep 712127 = 1068191) B1068191
theorem B12346273 : Blo 471786 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B9103387 : Blo 471786 9103387 := bstep (se 1 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 9103387 = 13655081) B13655081
theorem B1798139 : Blo 471786 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B19495039 : Blo 471786 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B1014761 : Blo 471786 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B2030903 : Blo 471786 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B1277311 : Blo 471786 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B21823343 : Blo 471786 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B1804427 : Blo 471786 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B2395007 : Blo 471786 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B39063647 : Blo 471786 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B4034879 : Blo 471786 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B44309501 : Blo 471786 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B532507 : Blo 471786 532507 := bstep (se 1 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 532507 = 798761) B798761
theorem B25993385 : Blo 471786 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B5547325 : Blo 471786 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B1353935 : Blo 471786 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B798491 : Blo 471786 798491 := bstep (se 1 (by rfl) ⟨598868, by rfl⟩ : syracuseStep 798491 = 1197737) B1197737
theorem B472155 : Blo 471786 472155 := bstep (se 1 (by rfl) ⟨354116, by rfl⟩ : syracuseStep 472155 = 708233) B708233
theorem B12137849 : Blo 471786 12137849 := bstep (se 2 (by rfl) ⟨4551693, by rfl⟩ : syracuseStep 12137849 = 9103387) B9103387
theorem B65846789 : Blo 471786 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B474751 : Blo 471786 474751 := bstep (se 1 (by rfl) ⟨356063, by rfl⟩ : syracuseStep 474751 = 712127) B712127
theorem B1198759 : Blo 471786 1198759 := bstep (se 1 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 1198759 = 1798139) B1798139
theorem B1593593 : Blo 471786 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B708863 : Blo 471786 708863 := bstep (se 1 (by rfl) ⟨531647, by rfl⟩ : syracuseStep 708863 = 1063295) B1063295
theorem B676507 : Blo 471786 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B12964535 : Blo 471786 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B4313807 : Blo 471786 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B710759 : Blo 471786 710759 := bstep (se 1 (by rfl) ⟨533069, by rfl⟩ : syracuseStep 710759 = 1066139) B1066139
theorem B713609 : Blo 471786 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B13001957 : Blo 471786 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B2025299 : Blo 471786 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B1600127 : Blo 471786 1600127 := bstep (se 1 (by rfl) ⟨1200095, by rfl⟩ : syracuseStep 1600127 = 2400191) B2400191
theorem B1600667 : Blo 471786 1600667 := bstep (se 1 (by rfl) ⟨1200500, by rfl⟩ : syracuseStep 1600667 = 2401001) B2401001
theorem B94729823 : Blo 471786 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1703081 : Blo 471786 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B1015649 : Blo 471786 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B14548895 : Blo 471786 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B2689919 : Blo 471786 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B3610493 : Blo 471786 3610493 := bstep (se 3 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 3610493 = 1353935) B1353935
theorem B1350199 : Blo 471786 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B532327 : Blo 471786 532327 := bstep (se 1 (by rfl) ⟨399245, by rfl⟩ : syracuseStep 532327 = 798491) B798491
theorem B63153215 : Blo 471786 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B1062395 : Blo 471786 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B472575 : Blo 471786 472575 := bstep (se 1 (by rfl) ⟨354431, by rfl⟩ : syracuseStep 472575 = 708863) B708863
theorem B473839 : Blo 471786 473839 := bstep (se 1 (by rfl) ⟨355379, by rfl⟩ : syracuseStep 473839 = 710759) B710759
theorem B29539667 : Blo 471786 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B475739 : Blo 471786 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B8667971 : Blo 471786 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B902009 : Blo 471786 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B1066751 : Blo 471786 1066751 := bstep (se 1 (by rfl) ⟨800063, by rfl⟩ : syracuseStep 1066751 = 1600127) B1600127
theorem B1067111 : Blo 471786 1067111 := bstep (se 1 (by rfl) ⟨800333, by rfl⟩ : syracuseStep 1067111 = 1600667) B1600667
theorem B1135387 : Blo 471786 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B43897859 : Blo 471786 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B677099 : Blo 471786 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B710009 : Blo 471786 710009 := bstep (se 2 (by rfl) ⟨266253, by rfl⟩ : syracuseStep 710009 = 532507) B532507
theorem B1202951 : Blo 471786 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B7396433 : Blo 471786 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B1596671 : Blo 471786 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B26042431 : Blo 471786 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B8643023 : Blo 471786 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B2875871 : Blo 471786 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B1598345 : Blo 471786 1598345 := bstep (se 2 (by rfl) ⟨599379, by rfl⟩ : syracuseStep 1598345 = 1198759) B1198759
theorem B17328923 : Blo 471786 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B8091899 : Blo 471786 8091899 := bstep (se 1 (by rfl) ⟨6068924, by rfl⟩ : syracuseStep 8091899 = 12137849) B12137849
theorem B9699263 : Blo 471786 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B7668989 : Blo 471786 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B1805597 : Blo 471786 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B29265239 : Blo 471786 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B1513849 : Blo 471786 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B6466175 : Blo 471786 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B5778647 : Blo 471786 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B601339 : Blo 471786 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B473339 : Blo 471786 473339 := bstep (se 1 (by rfl) ⟨355004, by rfl⟩ : syracuseStep 473339 = 710009) B710009
theorem B2406995 : Blo 471786 2406995 := bstep (se 1 (by rfl) ⟨1805246, by rfl⟩ : syracuseStep 2406995 = 3610493) B3610493
theorem B801967 : Blo 471786 801967 := bstep (se 1 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 801967 = 1202951) B1202951
theorem B4930955 : Blo 471786 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B1064447 : Blo 471786 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B1065563 : Blo 471786 1065563 := bstep (se 1 (by rfl) ⟨799172, by rfl⟩ : syracuseStep 1065563 = 1598345) B1598345
theorem B11552615 : Blo 471786 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B708263 : Blo 471786 708263 := bstep (se 1 (by rfl) ⟨531197, by rfl⟩ : syracuseStep 708263 = 1062395) B1062395
theorem B5394599 : Blo 471786 5394599 := bstep (se 1 (by rfl) ⟨4045949, by rfl⟩ : syracuseStep 5394599 = 8091899) B8091899
theorem B709769 : Blo 471786 709769 := bstep (se 2 (by rfl) ⟨266163, by rfl⟩ : syracuseStep 709769 = 532327) B532327
theorem B34723241 : Blo 471786 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B711167 : Blo 471786 711167 := bstep (se 1 (by rfl) ⟨533375, by rfl⟩ : syracuseStep 711167 = 1066751) B1066751
theorem B711407 : Blo 471786 711407 := bstep (se 1 (by rfl) ⟨533555, by rfl⟩ : syracuseStep 711407 = 1067111) B1067111
theorem B1793279 : Blo 471786 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B5762015 : Blo 471786 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B42102143 : Blo 471786 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B1800265 : Blo 471786 1800265 := bstep (se 2 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 1800265 = 1350199) B1350199
theorem B78772445 : Blo 471786 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B5112659 : Blo 471786 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B7701743 : Blo 471786 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B3841343 : Blo 471786 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B2400353 : Blo 471786 2400353 := bstep (se 2 (by rfl) ⟨900132, by rfl⟩ : syracuseStep 2400353 = 1800265) B1800265
theorem B3287303 : Blo 471786 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B19510159 : Blo 471786 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B472175 : Blo 471786 472175 := bstep (se 1 (by rfl) ⟨354131, by rfl⟩ : syracuseStep 472175 = 708263) B708263
theorem B473179 : Blo 471786 473179 := bstep (se 1 (by rfl) ⟨354884, by rfl⟩ : syracuseStep 473179 = 709769) B709769
theorem B23148827 : Blo 471786 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B801785 : Blo 471786 801785 := bstep (se 2 (by rfl) ⟨300669, by rfl⟩ : syracuseStep 801785 = 601339) B601339
theorem B474111 : Blo 471786 474111 := bstep (se 1 (by rfl) ⟨355583, by rfl⟩ : syracuseStep 474111 = 711167) B711167
theorem B474271 : Blo 471786 474271 := bstep (se 1 (by rfl) ⟨355703, by rfl⟩ : syracuseStep 474271 = 711407) B711407
theorem B1195519 : Blo 471786 1195519 := bstep (se 1 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 1195519 = 1793279) B1793279
theorem B4310783 : Blo 471786 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B3852431 : Blo 471786 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B28068095 : Blo 471786 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B2018465 : Blo 471786 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B52514963 : Blo 471786 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B1069289 : Blo 471786 1069289 := bstep (se 2 (by rfl) ⟨400983, by rfl⟩ : syracuseStep 1069289 = 801967) B801967
theorem B709631 : Blo 471786 709631 := bstep (se 1 (by rfl) ⟨532223, by rfl⟩ : syracuseStep 709631 = 1064447) B1064447
theorem B710375 : Blo 471786 710375 := bstep (se 1 (by rfl) ⟨532781, by rfl⟩ : syracuseStep 710375 = 1065563) B1065563
theorem B1203731 : Blo 471786 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B3596399 : Blo 471786 3596399 := bstep (se 1 (by rfl) ⟨2697299, by rfl⟩ : syracuseStep 3596399 = 5394599) B5394599
theorem B1604663 : Blo 471786 1604663 := bstep (se 1 (by rfl) ⟨1203497, by rfl⟩ : syracuseStep 1604663 = 2406995) B2406995
theorem B18712063 : Blo 471786 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B1345643 : Blo 471786 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B13633757 : Blo 471786 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B2560895 : Blo 471786 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B2397599 : Blo 471786 2397599 := bstep (se 1 (by rfl) ⟨1798199, by rfl⟩ : syracuseStep 2397599 = 3596399) B3596399
theorem B534523 : Blo 471786 534523 := bstep (se 1 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 534523 = 801785) B801785
theorem B2568287 : Blo 471786 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B35009975 : Blo 471786 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B473087 : Blo 471786 473087 := bstep (se 1 (by rfl) ⟨354815, by rfl⟩ : syracuseStep 473087 = 709631) B709631
theorem B473583 : Blo 471786 473583 := bstep (se 1 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 473583 = 710375) B710375
theorem B802487 : Blo 471786 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B1594025 : Blo 471786 1594025 := bstep (se 2 (by rfl) ⟨597759, by rfl⟩ : syracuseStep 1594025 = 1195519) B1195519
theorem B1069775 : Blo 471786 1069775 := bstep (se 1 (by rfl) ⟨802331, by rfl⟩ : syracuseStep 1069775 = 1604663) B1604663
theorem B2873855 : Blo 471786 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B712859 : Blo 471786 712859 := bstep (se 1 (by rfl) ⟨534644, by rfl⟩ : syracuseStep 712859 = 1069289) B1069289
theorem B20537981 : Blo 471786 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B1600235 : Blo 471786 1600235 := bstep (se 1 (by rfl) ⟨1200176, by rfl⟩ : syracuseStep 1600235 = 2400353) B2400353
theorem B26013545 : Blo 471786 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B2191535 : Blo 471786 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B15432551 : Blo 471786 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B1707263 : Blo 471786 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B17342363 : Blo 471786 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B1712191 : Blo 471786 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B23339983 : Blo 471786 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B534991 : Blo 471786 534991 := bstep (se 1 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 534991 = 802487) B802487
theorem B897095 : Blo 471786 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B9089171 : Blo 471786 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B24949417 : Blo 471786 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B1062683 : Blo 471786 1062683 := bstep (se 1 (by rfl) ⟨797012, by rfl⟩ : syracuseStep 1062683 = 1594025) B1594025
theorem B1915903 : Blo 471786 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B475239 : Blo 471786 475239 := bstep (se 1 (by rfl) ⟨356429, by rfl⟩ : syracuseStep 475239 = 712859) B712859
theorem B1066823 : Blo 471786 1066823 := bstep (se 1 (by rfl) ⟨800117, by rfl⟩ : syracuseStep 1066823 = 1600235) B1600235
theorem B1461023 : Blo 471786 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B712697 : Blo 471786 712697 := bstep (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) B534523
theorem B713183 : Blo 471786 713183 := bstep (se 1 (by rfl) ⟨534887, by rfl⟩ : syracuseStep 713183 = 1069775) B1069775
theorem B1598399 : Blo 471786 1598399 := bstep (se 1 (by rfl) ⟨1198799, by rfl⟩ : syracuseStep 1598399 = 2397599) B2397599
theorem B13691987 : Blo 471786 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B10288367 : Blo 471786 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B2392253 : Blo 471786 2392253 := bstep (se 3 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 2392253 = 897095) B897095
theorem B33265889 : Blo 471786 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B6858911 : Blo 471786 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B475131 : Blo 471786 475131 := bstep (se 1 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 475131 = 712697) B712697
theorem B475455 : Blo 471786 475455 := bstep (se 1 (by rfl) ⟨356591, by rfl⟩ : syracuseStep 475455 = 713183) B713183
theorem B1065599 : Blo 471786 1065599 := bstep (se 1 (by rfl) ⟨799199, by rfl⟩ : syracuseStep 1065599 = 1598399) B1598399
theorem B9127991 : Blo 471786 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B708455 : Blo 471786 708455 := bstep (se 1 (by rfl) ⟨531341, by rfl⟩ : syracuseStep 708455 = 1062683) B1062683
theorem B2282921 : Blo 471786 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B711215 : Blo 471786 711215 := bstep (se 1 (by rfl) ⟨533411, by rfl⟩ : syracuseStep 711215 = 1066823) B1066823
theorem B31119977 : Blo 471786 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B974015 : Blo 471786 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B1138175 : Blo 471786 1138175 := bstep (se 1 (by rfl) ⟨853631, by rfl⟩ : syracuseStep 1138175 = 1707263) B1707263
theorem B713321 : Blo 471786 713321 := bstep (se 2 (by rfl) ⟨267495, by rfl⟩ : syracuseStep 713321 = 534991) B534991
theorem B11561575 : Blo 471786 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B6059447 : Blo 471786 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B2554537 : Blo 471786 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B758783 : Blo 471786 758783 := bstep (se 1 (by rfl) ⟨569087, by rfl⟩ : syracuseStep 758783 = 1138175) B1138175
theorem B4039631 : Blo 471786 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B472303 : Blo 471786 472303 := bstep (se 1 (by rfl) ⟨354227, by rfl⟩ : syracuseStep 472303 = 708455) B708455
theorem B15415433 : Blo 471786 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B1521947 : Blo 471786 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B474143 : Blo 471786 474143 := bstep (se 1 (by rfl) ⟨355607, by rfl⟩ : syracuseStep 474143 = 711215) B711215
theorem B475547 : Blo 471786 475547 := bstep (se 1 (by rfl) ⟨356660, by rfl⟩ : syracuseStep 475547 = 713321) B713321
theorem B4572607 : Blo 471786 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B82986605 : Blo 471786 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B1594835 : Blo 471786 1594835 := bstep (se 1 (by rfl) ⟨1196126, by rfl⟩ : syracuseStep 1594835 = 2392253) B2392253
theorem B710399 : Blo 471786 710399 := bstep (se 1 (by rfl) ⟨532799, by rfl⟩ : syracuseStep 710399 = 1065599) B1065599
theorem B6085327 : Blo 471786 6085327 := bstep (se 1 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 6085327 = 9127991) B9127991
theorem B22177259 : Blo 471786 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B649343 : Blo 471786 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B3406049 : Blo 471786 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B6096809 : Blo 471786 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B2693087 : Blo 471786 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B14784839 : Blo 471786 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B2270699 : Blo 471786 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B55324403 : Blo 471786 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B505855 : Blo 471786 505855 := bstep (se 1 (by rfl) ⟨379391, by rfl⟩ : syracuseStep 505855 = 758783) B758783
theorem B1063223 : Blo 471786 1063223 := bstep (se 1 (by rfl) ⟨797417, by rfl⟩ : syracuseStep 1063223 = 1594835) B1594835
theorem B473599 : Blo 471786 473599 := bstep (se 1 (by rfl) ⟨355199, by rfl⟩ : syracuseStep 473599 = 710399) B710399
theorem B8113769 : Blo 471786 8113769 := bstep (se 2 (by rfl) ⟨3042663, by rfl⟩ : syracuseStep 8113769 = 6085327) B6085327
theorem B10276955 : Blo 471786 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B1731581 : Blo 471786 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B4058525 : Blo 471786 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B4064539 : Blo 471786 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B5409179 : Blo 471786 5409179 := bstep (se 1 (by rfl) ⟨4056884, by rfl⟩ : syracuseStep 5409179 = 8113769) B8113769
theorem B6851303 : Blo 471786 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B1513799 : Blo 471786 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B1154387 : Blo 471786 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B2697893 : Blo 471786 2697893 := bstep (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) B505855
theorem B2705683 : Blo 471786 2705683 := bstep (se 1 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 2705683 = 4058525) B4058525
theorem B36882935 : Blo 471786 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B708815 : Blo 471786 708815 := bstep (se 1 (by rfl) ⟨531611, by rfl⟩ : syracuseStep 708815 = 1063223) B1063223
theorem B1795391 : Blo 471786 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B9856559 : Blo 471786 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B3606119 : Blo 471786 3606119 := bstep (se 1 (by rfl) ⟨2704589, by rfl⟩ : syracuseStep 3606119 = 5409179) B5409179
theorem B3607577 : Blo 471786 3607577 := bstep (se 2 (by rfl) ⟨1352841, by rfl⟩ : syracuseStep 3607577 = 2705683) B2705683
theorem B24588623 : Blo 471786 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B5419385 : Blo 471786 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B4567535 : Blo 471786 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B472543 : Blo 471786 472543 := bstep (se 1 (by rfl) ⟨354407, by rfl⟩ : syracuseStep 472543 = 708815) B708815
theorem B769591 : Blo 471786 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B1196927 : Blo 471786 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B6571039 : Blo 471786 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B1009199 : Blo 471786 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1798595 : Blo 471786 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B16392415 : Blo 471786 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B3612923 : Blo 471786 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B1026121 : Blo 471786 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B797951 : Blo 471786 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B2404079 : Blo 471786 2404079 := bstep (se 1 (by rfl) ⟨1803059, by rfl⟩ : syracuseStep 2404079 = 3606119) B3606119
theorem B8761385 : Blo 471786 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B2405051 : Blo 471786 2405051 := bstep (se 1 (by rfl) ⟨1803788, by rfl⟩ : syracuseStep 2405051 = 3607577) B3607577
theorem B672799 : Blo 471786 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B1199063 : Blo 471786 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B3045023 : Blo 471786 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B21856553 : Blo 471786 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B531967 : Blo 471786 531967 := bstep (se 1 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 531967 = 797951) B797951
theorem B5840923 : Blo 471786 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B897065 : Blo 471786 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B799375 : Blo 471786 799375 := bstep (se 1 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 799375 = 1199063) B1199063
theorem B2408615 : Blo 471786 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B1368161 : Blo 471786 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B1602719 : Blo 471786 1602719 := bstep (se 1 (by rfl) ⟨1202039, by rfl⟩ : syracuseStep 1602719 = 2404079) B2404079
theorem B1603367 : Blo 471786 1603367 := bstep (se 1 (by rfl) ⟨1202525, by rfl⟩ : syracuseStep 1603367 = 2405051) B2405051
theorem B2030015 : Blo 471786 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B1605743 : Blo 471786 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B598043 : Blo 471786 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B1353343 : Blo 471786 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B1065833 : Blo 471786 1065833 := bstep (se 2 (by rfl) ⟨399687, by rfl⟩ : syracuseStep 1065833 = 799375) B799375
theorem B1068479 : Blo 471786 1068479 := bstep (se 1 (by rfl) ⟨801359, by rfl⟩ : syracuseStep 1068479 = 1602719) B1602719
theorem B1068911 : Blo 471786 1068911 := bstep (se 1 (by rfl) ⟨801683, by rfl⟩ : syracuseStep 1068911 = 1603367) B1603367
theorem B709289 : Blo 471786 709289 := bstep (se 2 (by rfl) ⟨265983, by rfl⟩ : syracuseStep 709289 = 531967) B531967
theorem B7787897 : Blo 471786 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B14571035 : Blo 471786 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B912107 : Blo 471786 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B1804457 : Blo 471786 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B472859 : Blo 471786 472859 := bstep (se 1 (by rfl) ⟨354644, by rfl⟩ : syracuseStep 472859 = 709289) B709289
theorem B5191931 : Blo 471786 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B9714023 : Blo 471786 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B608071 : Blo 471786 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B1594781 : Blo 471786 1594781 := bstep (se 3 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 1594781 = 598043) B598043
theorem B1070495 : Blo 471786 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B710555 : Blo 471786 710555 := bstep (se 1 (by rfl) ⟨532916, by rfl⟩ : syracuseStep 710555 = 1065833) B1065833
theorem B712319 : Blo 471786 712319 := bstep (se 1 (by rfl) ⟨534239, by rfl⟩ : syracuseStep 712319 = 1068479) B1068479
theorem B712607 : Blo 471786 712607 := bstep (se 1 (by rfl) ⟨534455, by rfl⟩ : syracuseStep 712607 = 1068911) B1068911
theorem B1063187 : Blo 471786 1063187 := bstep (se 1 (by rfl) ⟨797390, by rfl⟩ : syracuseStep 1063187 = 1594781) B1594781
theorem B473703 : Blo 471786 473703 := bstep (se 1 (by rfl) ⟨355277, by rfl⟩ : syracuseStep 473703 = 710555) B710555
theorem B474879 : Blo 471786 474879 := bstep (se 1 (by rfl) ⟨356159, by rfl⟩ : syracuseStep 474879 = 712319) B712319
theorem B475071 : Blo 471786 475071 := bstep (se 1 (by rfl) ⟨356303, by rfl⟩ : syracuseStep 475071 = 712607) B712607
theorem B3461287 : Blo 471786 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B6476015 : Blo 471786 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B1202971 : Blo 471786 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B810761 : Blo 471786 810761 := bstep (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) B608071
theorem B713663 : Blo 471786 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B475775 : Blo 471786 475775 := bstep (se 1 (by rfl) ⟨356831, by rfl⟩ : syracuseStep 475775 = 713663) B713663
theorem B708791 : Blo 471786 708791 := bstep (se 1 (by rfl) ⟨531593, by rfl⟩ : syracuseStep 708791 = 1063187) B1063187
theorem B4317343 : Blo 471786 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B4615049 : Blo 471786 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B8648117 : Blo 471786 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B1603961 : Blo 471786 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B472527 : Blo 471786 472527 := bstep (se 1 (by rfl) ⟨354395, by rfl⟩ : syracuseStep 472527 = 708791) B708791
theorem B1069307 : Blo 471786 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B23025829 : Blo 471786 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B3076699 : Blo 471786 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B5765411 : Blo 471786 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B4102265 : Blo 471786 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B3843607 : Blo 471786 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B712871 : Blo 471786 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B30701105 : Blo 471786 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B5124809 : Blo 471786 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B475247 : Blo 471786 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B20467403 : Blo 471786 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B10939373 : Blo 471786 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B3416539 : Blo 471786 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B13644935 : Blo 471786 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B7292915 : Blo 471786 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B4555385 : Blo 471786 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B4861943 : Blo 471786 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B9096623 : Blo 471786 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B6064415 : Blo 471786 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B3036923 : Blo 471786 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B3241295 : Blo 471786 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B4042943 : Blo 471786 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B2024615 : Blo 471786 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B2160863 : Blo 471786 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B2695295 : Blo 471786 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B5398973 : Blo 471786 5398973 := bstep (se 3 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 5398973 = 2024615) B2024615
theorem B1440575 : Blo 471786 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B960383 : Blo 471786 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B1796863 : Blo 471786 1796863 := bstep (se 1 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 1796863 = 2695295) B2695295
theorem B3599315 : Blo 471786 3599315 := bstep (se 1 (by rfl) ⟨2699486, by rfl⟩ : syracuseStep 3599315 = 5398973) B5398973
theorem B2395817 : Blo 471786 2395817 := bstep (se 2 (by rfl) ⟨898431, by rfl⟩ : syracuseStep 2395817 = 1796863) B1796863
theorem B2561021 : Blo 471786 2561021 := bstep (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) B960383
theorem B2399543 : Blo 471786 2399543 := bstep (se 1 (by rfl) ⟨1799657, by rfl⟩ : syracuseStep 2399543 = 3599315) B3599315
theorem B1707347 : Blo 471786 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B1597211 : Blo 471786 1597211 := bstep (se 1 (by rfl) ⟨1197908, by rfl⟩ : syracuseStep 1597211 = 2395817) B2395817
theorem B1599695 : Blo 471786 1599695 := bstep (se 1 (by rfl) ⟨1199771, by rfl⟩ : syracuseStep 1599695 = 2399543) B2399543
theorem B1064807 : Blo 471786 1064807 := bstep (se 1 (by rfl) ⟨798605, by rfl⟩ : syracuseStep 1064807 = 1597211) B1597211
theorem B1066463 : Blo 471786 1066463 := bstep (se 1 (by rfl) ⟨799847, by rfl⟩ : syracuseStep 1066463 = 1599695) B1599695
theorem B1138231 : Blo 471786 1138231 := bstep (se 1 (by rfl) ⟨853673, by rfl⟩ : syracuseStep 1138231 = 1707347) B1707347
theorem B6070565 : Blo 471786 6070565 := bstep (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) B1138231
theorem B709871 : Blo 471786 709871 := bstep (se 1 (by rfl) ⟨532403, by rfl⟩ : syracuseStep 709871 = 1064807) B1064807
theorem B710975 : Blo 471786 710975 := bstep (se 1 (by rfl) ⟨533231, by rfl⟩ : syracuseStep 710975 = 1066463) B1066463
theorem B473247 : Blo 471786 473247 := bstep (se 1 (by rfl) ⟨354935, by rfl⟩ : syracuseStep 473247 = 709871) B709871
theorem B473983 : Blo 471786 473983 := bstep (se 1 (by rfl) ⟨355487, by rfl⟩ : syracuseStep 473983 = 710975) B710975
theorem B4047043 : Blo 471786 4047043 := bstep (se 1 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 4047043 = 6070565) B6070565
theorem B5396057 : Blo 471786 5396057 := bstep (se 2 (by rfl) ⟨2023521, by rfl⟩ : syracuseStep 5396057 = 4047043) B4047043
theorem B3597371 : Blo 471786 3597371 := bstep (se 1 (by rfl) ⟨2698028, by rfl⟩ : syracuseStep 3597371 = 5396057) B5396057
theorem B2398247 : Blo 471786 2398247 := bstep (se 1 (by rfl) ⟨1798685, by rfl⟩ : syracuseStep 2398247 = 3597371) B3597371
theorem B1598831 : Blo 471786 1598831 := bstep (se 1 (by rfl) ⟨1199123, by rfl⟩ : syracuseStep 1598831 = 2398247) B2398247
theorem B1065887 : Blo 471786 1065887 := bstep (se 1 (by rfl) ⟨799415, by rfl⟩ : syracuseStep 1065887 = 1598831) B1598831
theorem B710591 : Blo 471786 710591 := bstep (se 1 (by rfl) ⟨532943, by rfl⟩ : syracuseStep 710591 = 1065887) B1065887
theorem B473727 : Blo 471786 473727 := bstep (se 1 (by rfl) ⟨355295, by rfl⟩ : syracuseStep 473727 = 710591) B710591

theorem C0 (j : ℕ) (h1 : 117946 ≤ j) (h2 : j ≤ 118645) : Blo 471786 (4 * j + 3) := by
  interval_cases j
  · exact B471787
  · exact B471791
  · exact B471795
  · exact B471799
  · exact B471803
  · exact B471807
  · exact B471811
  · exact B471815
  · exact B471819
  · exact B471823
  · exact B471827
  · exact B471831
  · exact B471835
  · exact B471839
  · exact B471843
  · exact B471847
  · exact B471851
  · exact B471855
  · exact B471859
  · exact B471863
  · exact B471867
  · exact B471871
  · exact B471875
  · exact B471879
  · exact B471883
  · exact B471887
  · exact B471891
  · exact B471895
  · exact B471899
  · exact B471903
  · exact B471907
  · exact B471911
  · exact B471915
  · exact B471919
  · exact B471923
  · exact B471927
  · exact B471931
  · exact B471935
  · exact B471939
  · exact B471943
  · exact B471947
  · exact B471951
  · exact B471955
  · exact B471959
  · exact B471963
  · exact B471967
  · exact B471971
  · exact B471975
  · exact B471979
  · exact B471983
  · exact B471987
  · exact B471991
  · exact B471995
  · exact B471999
  · exact B472003
  · exact B472007
  · exact B472011
  · exact B472015
  · exact B472019
  · exact B472023
  · exact B472027
  · exact B472031
  · exact B472035
  · exact B472039
  · exact B472043
  · exact B472047
  · exact B472051
  · exact B472055
  · exact B472059
  · exact B472063
  · exact B472067
  · exact B472071
  · exact B472075
  · exact B472079
  · exact B472083
  · exact B472087
  · exact B472091
  · exact B472095
  · exact B472099
  · exact B472103
  · exact B472107
  · exact B472111
  · exact B472115
  · exact B472119
  · exact B472123
  · exact B472127
  · exact B472131
  · exact B472135
  · exact B472139
  · exact B472143
  · exact B472147
  · exact B472151
  · exact B472155
  · exact B472159
  · exact B472163
  · exact B472167
  · exact B472171
  · exact B472175
  · exact B472179
  · exact B472183
  · exact B472187
  · exact B472191
  · exact B472195
  · exact B472199
  · exact B472203
  · exact B472207
  · exact B472211
  · exact B472215
  · exact B472219
  · exact B472223
  · exact B472227
  · exact B472231
  · exact B472235
  · exact B472239
  · exact B472243
  · exact B472247
  · exact B472251
  · exact B472255
  · exact B472259
  · exact B472263
  · exact B472267
  · exact B472271
  · exact B472275
  · exact B472279
  · exact B472283
  · exact B472287
  · exact B472291
  · exact B472295
  · exact B472299
  · exact B472303
  · exact B472307
  · exact B472311
  · exact B472315
  · exact B472319
  · exact B472323
  · exact B472327
  · exact B472331
  · exact B472335
  · exact B472339
  · exact B472343
  · exact B472347
  · exact B472351
  · exact B472355
  · exact B472359
  · exact B472363
  · exact B472367
  · exact B472371
  · exact B472375
  · exact B472379
  · exact B472383
  · exact B472387
  · exact B472391
  · exact B472395
  · exact B472399
  · exact B472403
  · exact B472407
  · exact B472411
  · exact B472415
  · exact B472419
  · exact B472423
  · exact B472427
  · exact B472431
  · exact B472435
  · exact B472439
  · exact B472443
  · exact B472447
  · exact B472451
  · exact B472455
  · exact B472459
  · exact B472463
  · exact B472467
  · exact B472471
  · exact B472475
  · exact B472479
  · exact B472483
  · exact B472487
  · exact B472491
  · exact B472495
  · exact B472499
  · exact B472503
  · exact B472507
  · exact B472511
  · exact B472515
  · exact B472519
  · exact B472523
  · exact B472527
  · exact B472531
  · exact B472535
  · exact B472539
  · exact B472543
  · exact B472547
  · exact B472551
  · exact B472555
  · exact B472559
  · exact B472563
  · exact B472567
  · exact B472571
  · exact B472575
  · exact B472579
  · exact B472583
  · exact B472587
  · exact B472591
  · exact B472595
  · exact B472599
  · exact B472603
  · exact B472607
  · exact B472611
  · exact B472615
  · exact B472619
  · exact B472623
  · exact B472627
  · exact B472631
  · exact B472635
  · exact B472639
  · exact B472643
  · exact B472647
  · exact B472651
  · exact B472655
  · exact B472659
  · exact B472663
  · exact B472667
  · exact B472671
  · exact B472675
  · exact B472679
  · exact B472683
  · exact B472687
  · exact B472691
  · exact B472695
  · exact B472699
  · exact B472703
  · exact B472707
  · exact B472711
  · exact B472715
  · exact B472719
  · exact B472723
  · exact B472727
  · exact B472731
  · exact B472735
  · exact B472739
  · exact B472743
  · exact B472747
  · exact B472751
  · exact B472755
  · exact B472759
  · exact B472763
  · exact B472767
  · exact B472771
  · exact B472775
  · exact B472779
  · exact B472783
  · exact B472787
  · exact B472791
  · exact B472795
  · exact B472799
  · exact B472803
  · exact B472807
  · exact B472811
  · exact B472815
  · exact B472819
  · exact B472823
  · exact B472827
  · exact B472831
  · exact B472835
  · exact B472839
  · exact B472843
  · exact B472847
  · exact B472851
  · exact B472855
  · exact B472859
  · exact B472863
  · exact B472867
  · exact B472871
  · exact B472875
  · exact B472879
  · exact B472883
  · exact B472887
  · exact B472891
  · exact B472895
  · exact B472899
  · exact B472903
  · exact B472907
  · exact B472911
  · exact B472915
  · exact B472919
  · exact B472923
  · exact B472927
  · exact B472931
  · exact B472935
  · exact B472939
  · exact B472943
  · exact B472947
  · exact B472951
  · exact B472955
  · exact B472959
  · exact B472963
  · exact B472967
  · exact B472971
  · exact B472975
  · exact B472979
  · exact B472983
  · exact B472987
  · exact B472991
  · exact B472995
  · exact B472999
  · exact B473003
  · exact B473007
  · exact B473011
  · exact B473015
  · exact B473019
  · exact B473023
  · exact B473027
  · exact B473031
  · exact B473035
  · exact B473039
  · exact B473043
  · exact B473047
  · exact B473051
  · exact B473055
  · exact B473059
  · exact B473063
  · exact B473067
  · exact B473071
  · exact B473075
  · exact B473079
  · exact B473083
  · exact B473087
  · exact B473091
  · exact B473095
  · exact B473099
  · exact B473103
  · exact B473107
  · exact B473111
  · exact B473115
  · exact B473119
  · exact B473123
  · exact B473127
  · exact B473131
  · exact B473135
  · exact B473139
  · exact B473143
  · exact B473147
  · exact B473151
  · exact B473155
  · exact B473159
  · exact B473163
  · exact B473167
  · exact B473171
  · exact B473175
  · exact B473179
  · exact B473183
  · exact B473187
  · exact B473191
  · exact B473195
  · exact B473199
  · exact B473203
  · exact B473207
  · exact B473211
  · exact B473215
  · exact B473219
  · exact B473223
  · exact B473227
  · exact B473231
  · exact B473235
  · exact B473239
  · exact B473243
  · exact B473247
  · exact B473251
  · exact B473255
  · exact B473259
  · exact B473263
  · exact B473267
  · exact B473271
  · exact B473275
  · exact B473279
  · exact B473283
  · exact B473287
  · exact B473291
  · exact B473295
  · exact B473299
  · exact B473303
  · exact B473307
  · exact B473311
  · exact B473315
  · exact B473319
  · exact B473323
  · exact B473327
  · exact B473331
  · exact B473335
  · exact B473339
  · exact B473343
  · exact B473347
  · exact B473351
  · exact B473355
  · exact B473359
  · exact B473363
  · exact B473367
  · exact B473371
  · exact B473375
  · exact B473379
  · exact B473383
  · exact B473387
  · exact B473391
  · exact B473395
  · exact B473399
  · exact B473403
  · exact B473407
  · exact B473411
  · exact B473415
  · exact B473419
  · exact B473423
  · exact B473427
  · exact B473431
  · exact B473435
  · exact B473439
  · exact B473443
  · exact B473447
  · exact B473451
  · exact B473455
  · exact B473459
  · exact B473463
  · exact B473467
  · exact B473471
  · exact B473475
  · exact B473479
  · exact B473483
  · exact B473487
  · exact B473491
  · exact B473495
  · exact B473499
  · exact B473503
  · exact B473507
  · exact B473511
  · exact B473515
  · exact B473519
  · exact B473523
  · exact B473527
  · exact B473531
  · exact B473535
  · exact B473539
  · exact B473543
  · exact B473547
  · exact B473551
  · exact B473555
  · exact B473559
  · exact B473563
  · exact B473567
  · exact B473571
  · exact B473575
  · exact B473579
  · exact B473583
  · exact B473587
  · exact B473591
  · exact B473595
  · exact B473599
  · exact B473603
  · exact B473607
  · exact B473611
  · exact B473615
  · exact B473619
  · exact B473623
  · exact B473627
  · exact B473631
  · exact B473635
  · exact B473639
  · exact B473643
  · exact B473647
  · exact B473651
  · exact B473655
  · exact B473659
  · exact B473663
  · exact B473667
  · exact B473671
  · exact B473675
  · exact B473679
  · exact B473683
  · exact B473687
  · exact B473691
  · exact B473695
  · exact B473699
  · exact B473703
  · exact B473707
  · exact B473711
  · exact B473715
  · exact B473719
  · exact B473723
  · exact B473727
  · exact B473731
  · exact B473735
  · exact B473739
  · exact B473743
  · exact B473747
  · exact B473751
  · exact B473755
  · exact B473759
  · exact B473763
  · exact B473767
  · exact B473771
  · exact B473775
  · exact B473779
  · exact B473783
  · exact B473787
  · exact B473791
  · exact B473795
  · exact B473799
  · exact B473803
  · exact B473807
  · exact B473811
  · exact B473815
  · exact B473819
  · exact B473823
  · exact B473827
  · exact B473831
  · exact B473835
  · exact B473839
  · exact B473843
  · exact B473847
  · exact B473851
  · exact B473855
  · exact B473859
  · exact B473863
  · exact B473867
  · exact B473871
  · exact B473875
  · exact B473879
  · exact B473883
  · exact B473887
  · exact B473891
  · exact B473895
  · exact B473899
  · exact B473903
  · exact B473907
  · exact B473911
  · exact B473915
  · exact B473919
  · exact B473923
  · exact B473927
  · exact B473931
  · exact B473935
  · exact B473939
  · exact B473943
  · exact B473947
  · exact B473951
  · exact B473955
  · exact B473959
  · exact B473963
  · exact B473967
  · exact B473971
  · exact B473975
  · exact B473979
  · exact B473983
  · exact B473987
  · exact B473991
  · exact B473995
  · exact B473999
  · exact B474003
  · exact B474007
  · exact B474011
  · exact B474015
  · exact B474019
  · exact B474023
  · exact B474027
  · exact B474031
  · exact B474035
  · exact B474039
  · exact B474043
  · exact B474047
  · exact B474051
  · exact B474055
  · exact B474059
  · exact B474063
  · exact B474067
  · exact B474071
  · exact B474075
  · exact B474079
  · exact B474083
  · exact B474087
  · exact B474091
  · exact B474095
  · exact B474099
  · exact B474103
  · exact B474107
  · exact B474111
  · exact B474115
  · exact B474119
  · exact B474123
  · exact B474127
  · exact B474131
  · exact B474135
  · exact B474139
  · exact B474143
  · exact B474147
  · exact B474151
  · exact B474155
  · exact B474159
  · exact B474163
  · exact B474167
  · exact B474171
  · exact B474175
  · exact B474179
  · exact B474183
  · exact B474187
  · exact B474191
  · exact B474195
  · exact B474199
  · exact B474203
  · exact B474207
  · exact B474211
  · exact B474215
  · exact B474219
  · exact B474223
  · exact B474227
  · exact B474231
  · exact B474235
  · exact B474239
  · exact B474243
  · exact B474247
  · exact B474251
  · exact B474255
  · exact B474259
  · exact B474263
  · exact B474267
  · exact B474271
  · exact B474275
  · exact B474279
  · exact B474283
  · exact B474287
  · exact B474291
  · exact B474295
  · exact B474299
  · exact B474303
  · exact B474307
  · exact B474311
  · exact B474315
  · exact B474319
  · exact B474323
  · exact B474327
  · exact B474331
  · exact B474335
  · exact B474339
  · exact B474343
  · exact B474347
  · exact B474351
  · exact B474355
  · exact B474359
  · exact B474363
  · exact B474367
  · exact B474371
  · exact B474375
  · exact B474379
  · exact B474383
  · exact B474387
  · exact B474391
  · exact B474395
  · exact B474399
  · exact B474403
  · exact B474407
  · exact B474411
  · exact B474415
  · exact B474419
  · exact B474423
  · exact B474427
  · exact B474431
  · exact B474435
  · exact B474439
  · exact B474443
  · exact B474447
  · exact B474451
  · exact B474455
  · exact B474459
  · exact B474463
  · exact B474467
  · exact B474471
  · exact B474475
  · exact B474479
  · exact B474483
  · exact B474487
  · exact B474491
  · exact B474495
  · exact B474499
  · exact B474503
  · exact B474507
  · exact B474511
  · exact B474515
  · exact B474519
  · exact B474523
  · exact B474527
  · exact B474531
  · exact B474535
  · exact B474539
  · exact B474543
  · exact B474547
  · exact B474551
  · exact B474555
  · exact B474559
  · exact B474563
  · exact B474567
  · exact B474571
  · exact B474575
  · exact B474579
  · exact B474583

theorem C1 (j : ℕ) (h1 : 118646 ≤ j) (h2 : j ≤ 118945) : Blo 471786 (4 * j + 3) := by
  interval_cases j
  · exact B474587
  · exact B474591
  · exact B474595
  · exact B474599
  · exact B474603
  · exact B474607
  · exact B474611
  · exact B474615
  · exact B474619
  · exact B474623
  · exact B474627
  · exact B474631
  · exact B474635
  · exact B474639
  · exact B474643
  · exact B474647
  · exact B474651
  · exact B474655
  · exact B474659
  · exact B474663
  · exact B474667
  · exact B474671
  · exact B474675
  · exact B474679
  · exact B474683
  · exact B474687
  · exact B474691
  · exact B474695
  · exact B474699
  · exact B474703
  · exact B474707
  · exact B474711
  · exact B474715
  · exact B474719
  · exact B474723
  · exact B474727
  · exact B474731
  · exact B474735
  · exact B474739
  · exact B474743
  · exact B474747
  · exact B474751
  · exact B474755
  · exact B474759
  · exact B474763
  · exact B474767
  · exact B474771
  · exact B474775
  · exact B474779
  · exact B474783
  · exact B474787
  · exact B474791
  · exact B474795
  · exact B474799
  · exact B474803
  · exact B474807
  · exact B474811
  · exact B474815
  · exact B474819
  · exact B474823
  · exact B474827
  · exact B474831
  · exact B474835
  · exact B474839
  · exact B474843
  · exact B474847
  · exact B474851
  · exact B474855
  · exact B474859
  · exact B474863
  · exact B474867
  · exact B474871
  · exact B474875
  · exact B474879
  · exact B474883
  · exact B474887
  · exact B474891
  · exact B474895
  · exact B474899
  · exact B474903
  · exact B474907
  · exact B474911
  · exact B474915
  · exact B474919
  · exact B474923
  · exact B474927
  · exact B474931
  · exact B474935
  · exact B474939
  · exact B474943
  · exact B474947
  · exact B474951
  · exact B474955
  · exact B474959
  · exact B474963
  · exact B474967
  · exact B474971
  · exact B474975
  · exact B474979
  · exact B474983
  · exact B474987
  · exact B474991
  · exact B474995
  · exact B474999
  · exact B475003
  · exact B475007
  · exact B475011
  · exact B475015
  · exact B475019
  · exact B475023
  · exact B475027
  · exact B475031
  · exact B475035
  · exact B475039
  · exact B475043
  · exact B475047
  · exact B475051
  · exact B475055
  · exact B475059
  · exact B475063
  · exact B475067
  · exact B475071
  · exact B475075
  · exact B475079
  · exact B475083
  · exact B475087
  · exact B475091
  · exact B475095
  · exact B475099
  · exact B475103
  · exact B475107
  · exact B475111
  · exact B475115
  · exact B475119
  · exact B475123
  · exact B475127
  · exact B475131
  · exact B475135
  · exact B475139
  · exact B475143
  · exact B475147
  · exact B475151
  · exact B475155
  · exact B475159
  · exact B475163
  · exact B475167
  · exact B475171
  · exact B475175
  · exact B475179
  · exact B475183
  · exact B475187
  · exact B475191
  · exact B475195
  · exact B475199
  · exact B475203
  · exact B475207
  · exact B475211
  · exact B475215
  · exact B475219
  · exact B475223
  · exact B475227
  · exact B475231
  · exact B475235
  · exact B475239
  · exact B475243
  · exact B475247
  · exact B475251
  · exact B475255
  · exact B475259
  · exact B475263
  · exact B475267
  · exact B475271
  · exact B475275
  · exact B475279
  · exact B475283
  · exact B475287
  · exact B475291
  · exact B475295
  · exact B475299
  · exact B475303
  · exact B475307
  · exact B475311
  · exact B475315
  · exact B475319
  · exact B475323
  · exact B475327
  · exact B475331
  · exact B475335
  · exact B475339
  · exact B475343
  · exact B475347
  · exact B475351
  · exact B475355
  · exact B475359
  · exact B475363
  · exact B475367
  · exact B475371
  · exact B475375
  · exact B475379
  · exact B475383
  · exact B475387
  · exact B475391
  · exact B475395
  · exact B475399
  · exact B475403
  · exact B475407
  · exact B475411
  · exact B475415
  · exact B475419
  · exact B475423
  · exact B475427
  · exact B475431
  · exact B475435
  · exact B475439
  · exact B475443
  · exact B475447
  · exact B475451
  · exact B475455
  · exact B475459
  · exact B475463
  · exact B475467
  · exact B475471
  · exact B475475
  · exact B475479
  · exact B475483
  · exact B475487
  · exact B475491
  · exact B475495
  · exact B475499
  · exact B475503
  · exact B475507
  · exact B475511
  · exact B475515
  · exact B475519
  · exact B475523
  · exact B475527
  · exact B475531
  · exact B475535
  · exact B475539
  · exact B475543
  · exact B475547
  · exact B475551
  · exact B475555
  · exact B475559
  · exact B475563
  · exact B475567
  · exact B475571
  · exact B475575
  · exact B475579
  · exact B475583
  · exact B475587
  · exact B475591
  · exact B475595
  · exact B475599
  · exact B475603
  · exact B475607
  · exact B475611
  · exact B475615
  · exact B475619
  · exact B475623
  · exact B475627
  · exact B475631
  · exact B475635
  · exact B475639
  · exact B475643
  · exact B475647
  · exact B475651
  · exact B475655
  · exact B475659
  · exact B475663
  · exact B475667
  · exact B475671
  · exact B475675
  · exact B475679
  · exact B475683
  · exact B475687
  · exact B475691
  · exact B475695
  · exact B475699
  · exact B475703
  · exact B475707
  · exact B475711
  · exact B475715
  · exact B475719
  · exact B475723
  · exact B475727
  · exact B475731
  · exact B475735
  · exact B475739
  · exact B475743
  · exact B475747
  · exact B475751
  · exact B475755
  · exact B475759
  · exact B475763
  · exact B475767
  · exact B475771
  · exact B475775
  · exact B475779
  · exact B475783

theorem solution (m : ℕ) (hlo : 471786 ≤ m) (hhi : m ≤ 475786) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 117946 ≤ j := by omega
    have hj2 : j ≤ 118945 := by omega
    have hb : Blo 471786 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 118646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
