-- Prove2me | solution 1 for syracuse_descends_range_211809_215809
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:55.226486+00:00
-- url     : https://prove2.me/submissions/031be480-b72f-40b3-b6e3-58e75f197858

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


theorem B1081349 : Blo 211809 1081349 := bbase (se 4 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 1081349 = 202753) (by norm_num)
theorem B360517 : Blo 211809 360517 := bbase (se 4 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 360517 = 67597) (by norm_num)
theorem B360605 : Blo 211809 360605 := bbase (se 3 (by rfl) ⟨67613, by rfl⟩ : syracuseStep 360605 = 135227) (by norm_num)
theorem B721061 : Blo 211809 721061 := bbase (se 4 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 721061 = 135199) (by norm_num)
theorem B557237 : Blo 211809 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B295093 : Blo 211809 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B229601 : Blo 211809 229601 := bbase (se 2 (by rfl) ⟨86100, by rfl⟩ : syracuseStep 229601 = 172201) (by norm_num)
theorem B360733 : Blo 211809 360733 := bbase (se 3 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 360733 = 135275) (by norm_num)
theorem B360821 : Blo 211809 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B360949 : Blo 211809 360949 := bbase (se 5 (by rfl) ⟨16919, by rfl⟩ : syracuseStep 360949 = 33839) (by norm_num)
theorem B262645 : Blo 211809 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B361037 : Blo 211809 361037 := bbase (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) (by norm_num)
theorem B721493 : Blo 211809 721493 := bbase (se 8 (by rfl) ⟨4227, by rfl⟩ : syracuseStep 721493 = 8455) (by norm_num)
theorem B459373 : Blo 211809 459373 := bbase (se 3 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 459373 = 172265) (by norm_num)
theorem B230045 : Blo 211809 230045 := bbase (se 3 (by rfl) ⟨43133, by rfl⟩ : syracuseStep 230045 = 86267) (by norm_num)
theorem B361165 : Blo 211809 361165 := bbase (se 3 (by rfl) ⟨67718, by rfl⟩ : syracuseStep 361165 = 135437) (by norm_num)
theorem B361253 : Blo 211809 361253 := bbase (se 4 (by rfl) ⟨33867, by rfl⟩ : syracuseStep 361253 = 67735) (by norm_num)
theorem B230293 : Blo 211809 230293 := bbase (se 6 (by rfl) ⟨5397, by rfl⟩ : syracuseStep 230293 = 10795) (by norm_num)
theorem B361381 : Blo 211809 361381 := bbase (se 4 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 361381 = 67759) (by norm_num)
theorem B459749 : Blo 211809 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B361469 : Blo 211809 361469 := bbase (se 3 (by rfl) ⟨67775, by rfl⟩ : syracuseStep 361469 = 135551) (by norm_num)
theorem B721925 : Blo 211809 721925 := bbase (se 4 (by rfl) ⟨67680, by rfl⟩ : syracuseStep 721925 = 135361) (by norm_num)
theorem B361597 : Blo 211809 361597 := bbase (se 3 (by rfl) ⟨67799, by rfl⟩ : syracuseStep 361597 = 135599) (by norm_num)
theorem B918661 : Blo 211809 918661 := bbase (se 4 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 918661 = 172249) (by norm_num)
theorem B918677 : Blo 211809 918677 := bbase (se 6 (by rfl) ⟨21531, by rfl⟩ : syracuseStep 918677 = 43063) (by norm_num)
theorem B361685 : Blo 211809 361685 := bbase (se 7 (by rfl) ⟨4238, by rfl⟩ : syracuseStep 361685 = 8477) (by norm_num)
theorem B1082645 : Blo 211809 1082645 := bbase (se 6 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 1082645 = 50749) (by norm_num)
theorem B361813 : Blo 211809 361813 := bbase (se 12 (by rfl) ⟨132, by rfl⟩ : syracuseStep 361813 = 265) (by norm_num)
theorem B689573 : Blo 211809 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B361901 : Blo 211809 361901 := bbase (se 3 (by rfl) ⟨67856, by rfl⟩ : syracuseStep 361901 = 135713) (by norm_num)
theorem B722357 : Blo 211809 722357 := bbase (se 5 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 722357 = 67721) (by norm_num)
theorem B263657 : Blo 211809 263657 := bbase (se 2 (by rfl) ⟨98871, by rfl⟩ : syracuseStep 263657 = 197743) (by norm_num)
theorem B1836533 : Blo 211809 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B362029 : Blo 211809 362029 := bbase (se 3 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 362029 = 135761) (by norm_num)
theorem B362117 : Blo 211809 362117 := bbase (se 4 (by rfl) ⟨33948, by rfl⟩ : syracuseStep 362117 = 67897) (by norm_num)
theorem B362245 : Blo 211809 362245 := bbase (se 4 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 362245 = 67921) (by norm_num)
theorem B362333 : Blo 211809 362333 := bbase (se 3 (by rfl) ⟨67937, by rfl⟩ : syracuseStep 362333 = 135875) (by norm_num)
theorem B722789 : Blo 211809 722789 := bbase (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) (by norm_num)
theorem B362461 : Blo 211809 362461 := bbase (se 3 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 362461 = 135923) (by norm_num)
theorem B264173 : Blo 211809 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B362549 : Blo 211809 362549 := bbase (se 5 (by rfl) ⟨16994, by rfl⟩ : syracuseStep 362549 = 33989) (by norm_num)
theorem B362573 : Blo 211809 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B362677 : Blo 211809 362677 := bbase (se 5 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 362677 = 34001) (by norm_num)
theorem B362765 : Blo 211809 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B723221 : Blo 211809 723221 := bbase (se 6 (by rfl) ⟨16950, by rfl⟩ : syracuseStep 723221 = 33901) (by norm_num)
theorem B559445 : Blo 211809 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B362893 : Blo 211809 362893 := bbase (se 3 (by rfl) ⟨68042, by rfl⟩ : syracuseStep 362893 = 136085) (by norm_num)
theorem B362981 : Blo 211809 362981 := bbase (se 4 (by rfl) ⟨34029, by rfl⟩ : syracuseStep 362981 = 68059) (by norm_num)
theorem B1083941 : Blo 211809 1083941 := bbase (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) (by norm_num)
theorem B363109 : Blo 211809 363109 := bbase (se 4 (by rfl) ⟨34041, by rfl⟩ : syracuseStep 363109 = 68083) (by norm_num)
theorem B363197 : Blo 211809 363197 := bbase (se 3 (by rfl) ⟨68099, by rfl⟩ : syracuseStep 363197 = 136199) (by norm_num)
theorem B723653 : Blo 211809 723653 := bbase (se 4 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 723653 = 135685) (by norm_num)
theorem B363325 : Blo 211809 363325 := bbase (se 3 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 363325 = 136247) (by norm_num)
theorem B363413 : Blo 211809 363413 := bbase (se 6 (by rfl) ⟨8517, by rfl⟩ : syracuseStep 363413 = 17035) (by norm_num)
theorem B363541 : Blo 211809 363541 := bbase (se 6 (by rfl) ⟨8520, by rfl⟩ : syracuseStep 363541 = 17041) (by norm_num)
theorem B363629 : Blo 211809 363629 := bbase (se 3 (by rfl) ⟨68180, by rfl⟩ : syracuseStep 363629 = 136361) (by norm_num)
theorem B724085 : Blo 211809 724085 := bbase (se 5 (by rfl) ⟨33941, by rfl⟩ : syracuseStep 724085 = 67883) (by norm_num)
theorem B2067605 : Blo 211809 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B363757 : Blo 211809 363757 := bbase (se 3 (by rfl) ⟨68204, by rfl⟩ : syracuseStep 363757 = 136409) (by norm_num)
theorem B232765 : Blo 211809 232765 := bbase (se 3 (by rfl) ⟨43643, by rfl⟩ : syracuseStep 232765 = 87287) (by norm_num)
theorem B363845 : Blo 211809 363845 := bbase (se 4 (by rfl) ⟨34110, by rfl⟩ : syracuseStep 363845 = 68221) (by norm_num)
theorem B920933 : Blo 211809 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B363973 : Blo 211809 363973 := bbase (se 4 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 363973 = 68245) (by norm_num)
theorem B1379861 : Blo 211809 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B364061 : Blo 211809 364061 := bbase (se 3 (by rfl) ⟨68261, by rfl⟩ : syracuseStep 364061 = 136523) (by norm_num)
theorem B724517 : Blo 211809 724517 := bbase (se 4 (by rfl) ⟨67923, by rfl⟩ : syracuseStep 724517 = 135847) (by norm_num)
theorem B1085237 : Blo 211809 1085237 := bbase (se 5 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 1085237 = 101741) (by norm_num)
theorem B757621 : Blo 211809 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B397181 : Blo 211809 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B724949 : Blo 211809 724949 := bbase (se 7 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 724949 = 16991) (by norm_num)
theorem B1216565 : Blo 211809 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B1544501 : Blo 211809 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B725381 : Blo 211809 725381 := bbase (se 4 (by rfl) ⟨68004, by rfl⟩ : syracuseStep 725381 = 136009) (by norm_num)
theorem B1839509 : Blo 211809 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B725701 : Blo 211809 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B725813 : Blo 211809 725813 := bbase (se 5 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 725813 = 68045) (by norm_num)
theorem B398189 : Blo 211809 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B1151957 : Blo 211809 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B693317 : Blo 211809 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B1086533 : Blo 211809 1086533 := bbase (se 4 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 1086533 = 203725) (by norm_num)
theorem B726245 : Blo 211809 726245 := bbase (se 4 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 726245 = 136171) (by norm_num)
theorem B464221 : Blo 211809 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B2430485 : Blo 211809 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B726677 : Blo 211809 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B530245 : Blo 211809 530245 := bbase (se 4 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 530245 = 99421) (by norm_num)
theorem B268105 : Blo 211809 268105 := bbase (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) (by norm_num)
theorem B268201 : Blo 211809 268201 := bbase (se 2 (by rfl) ⟨100575, by rfl⟩ : syracuseStep 268201 = 201151) (by norm_num)
theorem B464933 : Blo 211809 464933 := bbase (se 4 (by rfl) ⟨43587, by rfl⟩ : syracuseStep 464933 = 87175) (by norm_num)
theorem B727109 : Blo 211809 727109 := bbase (se 4 (by rfl) ⟨68166, by rfl⟩ : syracuseStep 727109 = 136333) (by norm_num)
theorem B268373 : Blo 211809 268373 := bbase (se 8 (by rfl) ⟨1572, by rfl⟩ : syracuseStep 268373 = 3145) (by norm_num)
theorem B268429 : Blo 211809 268429 := bbase (se 3 (by rfl) ⟨50330, by rfl⟩ : syracuseStep 268429 = 100661) (by norm_num)
theorem B3643541 : Blo 211809 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B268525 : Blo 211809 268525 := bbase (se 3 (by rfl) ⟨50348, by rfl⟩ : syracuseStep 268525 = 100697) (by norm_num)
theorem B432373 : Blo 211809 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B1087829 : Blo 211809 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B268697 : Blo 211809 268697 := bbase (se 2 (by rfl) ⟨100761, by rfl⟩ : syracuseStep 268697 = 201523) (by norm_num)
theorem B268753 : Blo 211809 268753 := bbase (se 2 (by rfl) ⟨100782, by rfl⟩ : syracuseStep 268753 = 201565) (by norm_num)
theorem B727541 : Blo 211809 727541 := bbase (se 5 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 727541 = 68207) (by norm_num)
theorem B268849 : Blo 211809 268849 := bbase (se 2 (by rfl) ⟨100818, by rfl⟩ : syracuseStep 268849 = 201637) (by norm_num)
theorem B498317 : Blo 211809 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B2038421 : Blo 211809 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B269021 : Blo 211809 269021 := bbase (se 3 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 269021 = 100883) (by norm_num)
theorem B269077 : Blo 211809 269077 := bbase (se 6 (by rfl) ⟨6306, by rfl⟩ : syracuseStep 269077 = 12613) (by norm_num)
theorem B301909 : Blo 211809 301909 := bbase (se 9 (by rfl) ⟨884, by rfl⟩ : syracuseStep 301909 = 1769) (by norm_num)
theorem B269173 : Blo 211809 269173 := bbase (se 5 (by rfl) ⟨12617, by rfl⟩ : syracuseStep 269173 = 25235) (by norm_num)
theorem B727973 : Blo 211809 727973 := bbase (se 4 (by rfl) ⟨68247, by rfl⟩ : syracuseStep 727973 = 136495) (by norm_num)
theorem B367613 : Blo 211809 367613 := bbase (se 3 (by rfl) ⟨68927, by rfl⟩ : syracuseStep 367613 = 137855) (by norm_num)
theorem B269345 : Blo 211809 269345 := bbase (se 2 (by rfl) ⟨101004, by rfl⟩ : syracuseStep 269345 = 202009) (by norm_num)
theorem B302125 : Blo 211809 302125 := bbase (se 3 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 302125 = 113297) (by norm_num)
theorem B367669 : Blo 211809 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B826453 : Blo 211809 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B269401 : Blo 211809 269401 := bbase (se 2 (by rfl) ⟨101025, by rfl⟩ : syracuseStep 269401 = 202051) (by norm_num)
theorem B2202805 : Blo 211809 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B269497 : Blo 211809 269497 := bbase (se 2 (by rfl) ⟨101061, by rfl⟩ : syracuseStep 269497 = 202123) (by norm_num)
theorem B1252565 : Blo 211809 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B269669 : Blo 211809 269669 := bbase (se 4 (by rfl) ⟨25281, by rfl⟩ : syracuseStep 269669 = 50563) (by norm_num)
theorem B269725 : Blo 211809 269725 := bbase (se 3 (by rfl) ⟨50573, by rfl⟩ : syracuseStep 269725 = 101147) (by norm_num)
theorem B302501 : Blo 211809 302501 := bbase (se 4 (by rfl) ⟨28359, by rfl⟩ : syracuseStep 302501 = 56719) (by norm_num)
theorem B433613 : Blo 211809 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B269821 : Blo 211809 269821 := bbase (se 3 (by rfl) ⟨50591, by rfl⟩ : syracuseStep 269821 = 101183) (by norm_num)
theorem B1089125 : Blo 211809 1089125 := bbase (se 4 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 1089125 = 204211) (by norm_num)
theorem B1023653 : Blo 211809 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B269993 : Blo 211809 269993 := bbase (se 2 (by rfl) ⟨101247, by rfl⟩ : syracuseStep 269993 = 202495) (by norm_num)
theorem B2989781 : Blo 211809 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B270049 : Blo 211809 270049 := bbase (se 2 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 270049 = 202537) (by norm_num)
theorem B1023749 : Blo 211809 1023749 := bbase (se 4 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 1023749 = 191953) (by norm_num)
theorem B270145 : Blo 211809 270145 := bbase (se 2 (by rfl) ⟨101304, by rfl⟩ : syracuseStep 270145 = 202609) (by norm_num)
theorem B270317 : Blo 211809 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B434197 : Blo 211809 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B270373 : Blo 211809 270373 := bbase (se 4 (by rfl) ⟨25347, by rfl⟩ : syracuseStep 270373 = 50695) (by norm_num)
theorem B270469 : Blo 211809 270469 := bbase (se 4 (by rfl) ⟨25356, by rfl⟩ : syracuseStep 270469 = 50713) (by norm_num)
theorem B1614005 : Blo 211809 1614005 := bbase (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) (by norm_num)
theorem B270641 : Blo 211809 270641 := bbase (se 2 (by rfl) ⟨101490, by rfl⟩ : syracuseStep 270641 = 202981) (by norm_num)
theorem B270697 : Blo 211809 270697 := bbase (se 2 (by rfl) ⟨101511, by rfl⟩ : syracuseStep 270697 = 203023) (by norm_num)
theorem B270793 : Blo 211809 270793 := bbase (se 2 (by rfl) ⟨101547, by rfl⟩ : syracuseStep 270793 = 203095) (by norm_num)
theorem B270965 : Blo 211809 270965 := bbase (se 5 (by rfl) ⟨12701, by rfl⟩ : syracuseStep 270965 = 25403) (by norm_num)
theorem B271021 : Blo 211809 271021 := bbase (se 3 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 271021 = 101633) (by norm_num)
theorem B238297 : Blo 211809 238297 := bbase (se 2 (by rfl) ⟨89361, by rfl⟩ : syracuseStep 238297 = 178723) (by norm_num)
theorem B238333 : Blo 211809 238333 := bbase (se 3 (by rfl) ⟨44687, by rfl⟩ : syracuseStep 238333 = 89375) (by norm_num)
theorem B271117 : Blo 211809 271117 := bbase (se 3 (by rfl) ⟨50834, by rfl⟩ : syracuseStep 271117 = 101669) (by norm_num)
theorem B238369 : Blo 211809 238369 := bbase (se 2 (by rfl) ⟨89388, by rfl⟩ : syracuseStep 238369 = 178777) (by norm_num)
theorem B303925 : Blo 211809 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B238405 : Blo 211809 238405 := bbase (se 4 (by rfl) ⟨22350, by rfl⟩ : syracuseStep 238405 = 44701) (by norm_num)
theorem B238441 : Blo 211809 238441 := bbase (se 2 (by rfl) ⟨89415, by rfl⟩ : syracuseStep 238441 = 178831) (by norm_num)
theorem B1090421 : Blo 211809 1090421 := bbase (se 5 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 1090421 = 102227) (by norm_num)
theorem B402317 : Blo 211809 402317 := bbase (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) (by norm_num)
theorem B238477 : Blo 211809 238477 := bbase (se 3 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 238477 = 89429) (by norm_num)
theorem B238513 : Blo 211809 238513 := bbase (se 2 (by rfl) ⟨89442, by rfl⟩ : syracuseStep 238513 = 178885) (by norm_num)
theorem B271289 : Blo 211809 271289 := bbase (se 2 (by rfl) ⟨101733, by rfl⟩ : syracuseStep 271289 = 203467) (by norm_num)
theorem B238549 : Blo 211809 238549 := bbase (se 7 (by rfl) ⟨2795, by rfl⟩ : syracuseStep 238549 = 5591) (by norm_num)
theorem B271345 : Blo 211809 271345 := bbase (se 2 (by rfl) ⟨101754, by rfl⟩ : syracuseStep 271345 = 203509) (by norm_num)
theorem B238585 : Blo 211809 238585 := bbase (se 2 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 238585 = 178939) (by norm_num)
theorem B238621 : Blo 211809 238621 := bbase (se 3 (by rfl) ⟨44741, by rfl⟩ : syracuseStep 238621 = 89483) (by norm_num)
theorem B238657 : Blo 211809 238657 := bbase (se 2 (by rfl) ⟨89496, by rfl⟩ : syracuseStep 238657 = 178993) (by norm_num)
theorem B271441 : Blo 211809 271441 := bbase (se 2 (by rfl) ⟨101790, by rfl⟩ : syracuseStep 271441 = 203581) (by norm_num)
theorem B238693 : Blo 211809 238693 := bbase (se 4 (by rfl) ⟨22377, by rfl⟩ : syracuseStep 238693 = 44755) (by norm_num)
theorem B238729 : Blo 211809 238729 := bbase (se 2 (by rfl) ⟨89523, by rfl⟩ : syracuseStep 238729 = 179047) (by norm_num)
theorem B238765 : Blo 211809 238765 := bbase (se 3 (by rfl) ⟨44768, by rfl⟩ : syracuseStep 238765 = 89537) (by norm_num)
theorem B238801 : Blo 211809 238801 := bbase (se 2 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 238801 = 179101) (by norm_num)
theorem B238837 : Blo 211809 238837 := bbase (se 5 (by rfl) ⟨11195, by rfl⟩ : syracuseStep 238837 = 22391) (by norm_num)
theorem B271613 : Blo 211809 271613 := bbase (se 3 (by rfl) ⟨50927, by rfl⟩ : syracuseStep 271613 = 101855) (by norm_num)
theorem B238873 : Blo 211809 238873 := bbase (se 2 (by rfl) ⟨89577, by rfl⟩ : syracuseStep 238873 = 179155) (by norm_num)
theorem B271669 : Blo 211809 271669 := bbase (se 5 (by rfl) ⟨12734, by rfl⟩ : syracuseStep 271669 = 25469) (by norm_num)
theorem B238909 : Blo 211809 238909 := bbase (se 3 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 238909 = 89591) (by norm_num)
theorem B238945 : Blo 211809 238945 := bbase (se 2 (by rfl) ⟨89604, by rfl⟩ : syracuseStep 238945 = 179209) (by norm_num)
theorem B238981 : Blo 211809 238981 := bbase (se 4 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 238981 = 44809) (by norm_num)
theorem B304517 : Blo 211809 304517 := bbase (se 4 (by rfl) ⟨28548, by rfl⟩ : syracuseStep 304517 = 57097) (by norm_num)
theorem B271765 : Blo 211809 271765 := bbase (se 6 (by rfl) ⟨6369, by rfl⟩ : syracuseStep 271765 = 12739) (by norm_num)
theorem B239017 : Blo 211809 239017 := bbase (se 2 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 239017 = 179263) (by norm_num)
theorem B239053 : Blo 211809 239053 := bbase (se 3 (by rfl) ⟨44822, by rfl⟩ : syracuseStep 239053 = 89645) (by norm_num)
theorem B304597 : Blo 211809 304597 := bbase (se 7 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 304597 = 7139) (by norm_num)
theorem B239089 : Blo 211809 239089 := bbase (se 2 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 239089 = 179317) (by norm_num)
theorem B239125 : Blo 211809 239125 := bbase (se 6 (by rfl) ⟨5604, by rfl⟩ : syracuseStep 239125 = 11209) (by norm_num)
theorem B239161 : Blo 211809 239161 := bbase (se 2 (by rfl) ⟨89685, by rfl⟩ : syracuseStep 239161 = 179371) (by norm_num)
theorem B271937 : Blo 211809 271937 := bbase (se 2 (by rfl) ⟨101976, by rfl⟩ : syracuseStep 271937 = 203953) (by norm_num)
theorem B304717 : Blo 211809 304717 := bbase (se 3 (by rfl) ⟨57134, by rfl⟩ : syracuseStep 304717 = 114269) (by norm_num)
theorem B239197 : Blo 211809 239197 := bbase (se 3 (by rfl) ⟨44849, by rfl⟩ : syracuseStep 239197 = 89699) (by norm_num)
theorem B271993 : Blo 211809 271993 := bbase (se 2 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 271993 = 203995) (by norm_num)
theorem B403069 : Blo 211809 403069 := bbase (se 3 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 403069 = 151151) (by norm_num)
theorem B239233 : Blo 211809 239233 := bbase (se 2 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 239233 = 179425) (by norm_num)
theorem B1025669 : Blo 211809 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B239269 : Blo 211809 239269 := bbase (se 4 (by rfl) ⟨22431, by rfl⟩ : syracuseStep 239269 = 44863) (by norm_num)
theorem B304813 : Blo 211809 304813 := bbase (se 3 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 304813 = 114305) (by norm_num)
theorem B239305 : Blo 211809 239305 := bbase (se 2 (by rfl) ⟨89739, by rfl⟩ : syracuseStep 239305 = 179479) (by norm_num)
theorem B272089 : Blo 211809 272089 := bbase (se 2 (by rfl) ⟨102033, by rfl⟩ : syracuseStep 272089 = 204067) (by norm_num)
theorem B239341 : Blo 211809 239341 := bbase (se 3 (by rfl) ⟨44876, by rfl⟩ : syracuseStep 239341 = 89753) (by norm_num)
theorem B861941 : Blo 211809 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B403213 : Blo 211809 403213 := bbase (se 3 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 403213 = 151205) (by norm_num)
theorem B239377 : Blo 211809 239377 := bbase (se 2 (by rfl) ⟨89766, by rfl⟩ : syracuseStep 239377 = 179533) (by norm_num)
theorem B239413 : Blo 211809 239413 := bbase (se 5 (by rfl) ⟨11222, by rfl⟩ : syracuseStep 239413 = 22445) (by norm_num)
theorem B239449 : Blo 211809 239449 := bbase (se 2 (by rfl) ⟨89793, by rfl⟩ : syracuseStep 239449 = 179587) (by norm_num)
theorem B239485 : Blo 211809 239485 := bbase (se 3 (by rfl) ⟨44903, by rfl⟩ : syracuseStep 239485 = 89807) (by norm_num)
theorem B272261 : Blo 211809 272261 := bbase (se 4 (by rfl) ⟨25524, by rfl⟩ : syracuseStep 272261 = 51049) (by norm_num)
theorem B239521 : Blo 211809 239521 := bbase (se 2 (by rfl) ⟨89820, by rfl⟩ : syracuseStep 239521 = 179641) (by norm_num)
theorem B403373 : Blo 211809 403373 := bbase (se 3 (by rfl) ⟨75632, by rfl⟩ : syracuseStep 403373 = 151265) (by norm_num)
theorem B272317 : Blo 211809 272317 := bbase (se 3 (by rfl) ⟨51059, by rfl⟩ : syracuseStep 272317 = 102119) (by norm_num)
theorem B239557 : Blo 211809 239557 := bbase (se 4 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 239557 = 44917) (by norm_num)
theorem B239593 : Blo 211809 239593 := bbase (se 2 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 239593 = 179695) (by norm_num)
theorem B239629 : Blo 211809 239629 := bbase (se 3 (by rfl) ⟨44930, by rfl⟩ : syracuseStep 239629 = 89861) (by norm_num)
theorem B272413 : Blo 211809 272413 := bbase (se 3 (by rfl) ⟨51077, by rfl⟩ : syracuseStep 272413 = 102155) (by norm_num)
theorem B239665 : Blo 211809 239665 := bbase (se 2 (by rfl) ⟨89874, by rfl⟩ : syracuseStep 239665 = 179749) (by norm_num)
theorem B403517 : Blo 211809 403517 := bbase (se 3 (by rfl) ⟨75659, by rfl⟩ : syracuseStep 403517 = 151319) (by norm_num)
theorem B239701 : Blo 211809 239701 := bbase (se 8 (by rfl) ⟨1404, by rfl⟩ : syracuseStep 239701 = 2809) (by norm_num)
theorem B239737 : Blo 211809 239737 := bbase (se 2 (by rfl) ⟨89901, by rfl⟩ : syracuseStep 239737 = 179803) (by norm_num)
theorem B1091717 : Blo 211809 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B239773 : Blo 211809 239773 := bbase (se 3 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 239773 = 89915) (by norm_num)
theorem B305309 : Blo 211809 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B239809 : Blo 211809 239809 := bbase (se 2 (by rfl) ⟨89928, by rfl⟩ : syracuseStep 239809 = 179857) (by norm_num)
theorem B436421 : Blo 211809 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B272585 : Blo 211809 272585 := bbase (se 2 (by rfl) ⟨102219, by rfl⟩ : syracuseStep 272585 = 204439) (by norm_num)
theorem B239845 : Blo 211809 239845 := bbase (se 4 (by rfl) ⟨22485, by rfl⟩ : syracuseStep 239845 = 44971) (by norm_num)
theorem B272641 : Blo 211809 272641 := bbase (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) (by norm_num)
theorem B239881 : Blo 211809 239881 := bbase (se 2 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 239881 = 179911) (by norm_num)
theorem B3352853 : Blo 211809 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B239917 : Blo 211809 239917 := bbase (se 3 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 239917 = 89969) (by norm_num)
theorem B239953 : Blo 211809 239953 := bbase (se 2 (by rfl) ⟨89982, by rfl⟩ : syracuseStep 239953 = 179965) (by norm_num)
theorem B403805 : Blo 211809 403805 := bbase (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) (by norm_num)
theorem B272737 : Blo 211809 272737 := bbase (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) (by norm_num)
theorem B239989 : Blo 211809 239989 := bbase (se 5 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 239989 = 22499) (by norm_num)
theorem B240025 : Blo 211809 240025 := bbase (se 2 (by rfl) ⟨90009, by rfl⟩ : syracuseStep 240025 = 180019) (by norm_num)
theorem B240061 : Blo 211809 240061 := bbase (se 3 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 240061 = 90023) (by norm_num)
theorem B272857 : Blo 211809 272857 := bbase (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) (by norm_num)
theorem B240097 : Blo 211809 240097 := bbase (se 2 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 240097 = 180073) (by norm_num)
theorem B403957 : Blo 211809 403957 := bbase (se 5 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 403957 = 37871) (by norm_num)
theorem B240133 : Blo 211809 240133 := bbase (se 4 (by rfl) ⟨22512, by rfl⟩ : syracuseStep 240133 = 45025) (by norm_num)
theorem B272909 : Blo 211809 272909 := bbase (se 3 (by rfl) ⟨51170, by rfl⟩ : syracuseStep 272909 = 102341) (by norm_num)
theorem B371237 : Blo 211809 371237 := bbase (se 4 (by rfl) ⟨34803, by rfl⟩ : syracuseStep 371237 = 69607) (by norm_num)
theorem B240169 : Blo 211809 240169 := bbase (se 2 (by rfl) ⟨90063, by rfl⟩ : syracuseStep 240169 = 180127) (by norm_num)
theorem B272965 : Blo 211809 272965 := bbase (se 4 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 272965 = 51181) (by norm_num)
theorem B240205 : Blo 211809 240205 := bbase (se 3 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 240205 = 90077) (by norm_num)
theorem B240241 : Blo 211809 240241 := bbase (se 2 (by rfl) ⟨90090, by rfl⟩ : syracuseStep 240241 = 180181) (by norm_num)
theorem B240277 : Blo 211809 240277 := bbase (se 6 (by rfl) ⟨5631, by rfl⟩ : syracuseStep 240277 = 11263) (by norm_num)
theorem B273061 : Blo 211809 273061 := bbase (se 4 (by rfl) ⟨25599, by rfl⟩ : syracuseStep 273061 = 51199) (by norm_num)
theorem B240313 : Blo 211809 240313 := bbase (se 2 (by rfl) ⟨90117, by rfl⟩ : syracuseStep 240313 = 180235) (by norm_num)
theorem B305861 : Blo 211809 305861 := bbase (se 4 (by rfl) ⟨28674, by rfl⟩ : syracuseStep 305861 = 57349) (by norm_num)
theorem B240349 : Blo 211809 240349 := bbase (se 3 (by rfl) ⟨45065, by rfl⟩ : syracuseStep 240349 = 90131) (by norm_num)
theorem B240385 : Blo 211809 240385 := bbase (se 2 (by rfl) ⟨90144, by rfl⟩ : syracuseStep 240385 = 180289) (by norm_num)
theorem B404261 : Blo 211809 404261 := bbase (se 4 (by rfl) ⟨37899, by rfl⟩ : syracuseStep 404261 = 75799) (by norm_num)
theorem B240421 : Blo 211809 240421 := bbase (se 4 (by rfl) ⟨22539, by rfl⟩ : syracuseStep 240421 = 45079) (by norm_num)
theorem B240457 : Blo 211809 240457 := bbase (se 2 (by rfl) ⟨90171, by rfl⟩ : syracuseStep 240457 = 180343) (by norm_num)
theorem B240493 : Blo 211809 240493 := bbase (se 3 (by rfl) ⟨45092, by rfl⟩ : syracuseStep 240493 = 90185) (by norm_num)
theorem B240529 : Blo 211809 240529 := bbase (se 2 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 240529 = 180397) (by norm_num)
theorem B732053 : Blo 211809 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B240565 : Blo 211809 240565 := bbase (se 5 (by rfl) ⟨11276, by rfl⟩ : syracuseStep 240565 = 22553) (by norm_num)
theorem B240601 : Blo 211809 240601 := bbase (se 2 (by rfl) ⟨90225, by rfl⟩ : syracuseStep 240601 = 180451) (by norm_num)
theorem B240637 : Blo 211809 240637 := bbase (se 3 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 240637 = 90239) (by norm_num)
theorem B1027093 : Blo 211809 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B240673 : Blo 211809 240673 := bbase (se 2 (by rfl) ⟨90252, by rfl⟩ : syracuseStep 240673 = 180505) (by norm_num)
theorem B240709 : Blo 211809 240709 := bbase (se 4 (by rfl) ⟨22566, by rfl⟩ : syracuseStep 240709 = 45133) (by norm_num)
theorem B240745 : Blo 211809 240745 := bbase (se 2 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 240745 = 180559) (by norm_num)
theorem B240781 : Blo 211809 240781 := bbase (se 3 (by rfl) ⟨45146, by rfl⟩ : syracuseStep 240781 = 90293) (by norm_num)
theorem B240817 : Blo 211809 240817 := bbase (se 2 (by rfl) ⟨90306, by rfl⟩ : syracuseStep 240817 = 180613) (by norm_num)
theorem B240853 : Blo 211809 240853 := bbase (se 7 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 240853 = 5645) (by norm_num)
theorem B240889 : Blo 211809 240889 := bbase (se 2 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 240889 = 180667) (by norm_num)
theorem B240925 : Blo 211809 240925 := bbase (se 3 (by rfl) ⟨45173, by rfl⟩ : syracuseStep 240925 = 90347) (by norm_num)
theorem B240961 : Blo 211809 240961 := bbase (se 2 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 240961 = 180721) (by norm_num)
theorem B240997 : Blo 211809 240997 := bbase (se 4 (by rfl) ⟨22593, by rfl⟩ : syracuseStep 240997 = 45187) (by norm_num)
theorem B241033 : Blo 211809 241033 := bbase (se 2 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 241033 = 180775) (by norm_num)
theorem B241069 : Blo 211809 241069 := bbase (se 3 (by rfl) ⟨45200, by rfl⟩ : syracuseStep 241069 = 90401) (by norm_num)
theorem B306613 : Blo 211809 306613 := bbase (se 5 (by rfl) ⟨14372, by rfl⟩ : syracuseStep 306613 = 28745) (by norm_num)
theorem B241105 : Blo 211809 241105 := bbase (se 2 (by rfl) ⟨90414, by rfl⟩ : syracuseStep 241105 = 180829) (by norm_num)
theorem B241141 : Blo 211809 241141 := bbase (se 5 (by rfl) ⟨11303, by rfl⟩ : syracuseStep 241141 = 22607) (by norm_num)
theorem B405013 : Blo 211809 405013 := bbase (se 6 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 405013 = 18985) (by norm_num)
theorem B241177 : Blo 211809 241177 := bbase (se 2 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 241177 = 180883) (by norm_num)
theorem B241213 : Blo 211809 241213 := bbase (se 3 (by rfl) ⟨45227, by rfl⟩ : syracuseStep 241213 = 90455) (by norm_num)
theorem B241249 : Blo 211809 241249 := bbase (se 2 (by rfl) ⟨90468, by rfl⟩ : syracuseStep 241249 = 180937) (by norm_num)
theorem B241285 : Blo 211809 241285 := bbase (se 4 (by rfl) ⟨22620, by rfl⟩ : syracuseStep 241285 = 45241) (by norm_num)
theorem B405157 : Blo 211809 405157 := bbase (se 4 (by rfl) ⟨37983, by rfl⟩ : syracuseStep 405157 = 75967) (by norm_num)
theorem B241321 : Blo 211809 241321 := bbase (se 2 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 241321 = 180991) (by norm_num)
theorem B241357 : Blo 211809 241357 := bbase (se 3 (by rfl) ⟨45254, by rfl⟩ : syracuseStep 241357 = 90509) (by norm_num)
theorem B241393 : Blo 211809 241393 := bbase (se 2 (by rfl) ⟨90522, by rfl⟩ : syracuseStep 241393 = 181045) (by norm_num)
theorem B536341 : Blo 211809 536341 := bbase (se 6 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 536341 = 25141) (by norm_num)
theorem B3059477 : Blo 211809 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B241429 : Blo 211809 241429 := bbase (se 6 (by rfl) ⟨5658, by rfl⟩ : syracuseStep 241429 = 11317) (by norm_num)
theorem B241465 : Blo 211809 241465 := bbase (se 2 (by rfl) ⟨90549, by rfl⟩ : syracuseStep 241465 = 181099) (by norm_num)
theorem B405317 : Blo 211809 405317 := bbase (se 4 (by rfl) ⟨37998, by rfl⟩ : syracuseStep 405317 = 75997) (by norm_num)
theorem B241501 : Blo 211809 241501 := bbase (se 3 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 241501 = 90563) (by norm_num)
theorem B241537 : Blo 211809 241537 := bbase (se 2 (by rfl) ⟨90576, by rfl⟩ : syracuseStep 241537 = 181153) (by norm_num)
theorem B536453 : Blo 211809 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B241573 : Blo 211809 241573 := bbase (se 4 (by rfl) ⟨22647, by rfl⟩ : syracuseStep 241573 = 45295) (by norm_num)
theorem B1224629 : Blo 211809 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B241609 : Blo 211809 241609 := bbase (se 2 (by rfl) ⟨90603, by rfl⟩ : syracuseStep 241609 = 181207) (by norm_num)
theorem B405461 : Blo 211809 405461 := bbase (se 7 (by rfl) ⟨4751, by rfl⟩ : syracuseStep 405461 = 9503) (by norm_num)
theorem B864229 : Blo 211809 864229 := bbase (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) (by norm_num)
theorem B241645 : Blo 211809 241645 := bbase (se 3 (by rfl) ⟨45308, by rfl⟩ : syracuseStep 241645 = 90617) (by norm_num)
theorem B241681 : Blo 211809 241681 := bbase (se 2 (by rfl) ⟨90630, by rfl⟩ : syracuseStep 241681 = 181261) (by norm_num)
theorem B1552405 : Blo 211809 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B241717 : Blo 211809 241717 := bbase (se 5 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 241717 = 22661) (by norm_num)
theorem B536645 : Blo 211809 536645 := bbase (se 4 (by rfl) ⟨50310, by rfl⟩ : syracuseStep 536645 = 100621) (by norm_num)
theorem B241753 : Blo 211809 241753 := bbase (se 2 (by rfl) ⟨90657, by rfl⟩ : syracuseStep 241753 = 181315) (by norm_num)
theorem B438365 : Blo 211809 438365 := bbase (se 3 (by rfl) ⟨82193, by rfl⟩ : syracuseStep 438365 = 164387) (by norm_num)
theorem B241789 : Blo 211809 241789 := bbase (se 3 (by rfl) ⟨45335, by rfl⟩ : syracuseStep 241789 = 90671) (by norm_num)
theorem B241825 : Blo 211809 241825 := bbase (se 2 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 241825 = 181369) (by norm_num)
theorem B307381 : Blo 211809 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B241861 : Blo 211809 241861 := bbase (se 4 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 241861 = 45349) (by norm_num)
theorem B241897 : Blo 211809 241897 := bbase (se 2 (by rfl) ⟨90711, by rfl⟩ : syracuseStep 241897 = 181423) (by norm_num)
theorem B405749 : Blo 211809 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B241933 : Blo 211809 241933 := bbase (se 3 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 241933 = 90725) (by norm_num)
theorem B241969 : Blo 211809 241969 := bbase (se 2 (by rfl) ⟨90738, by rfl⟩ : syracuseStep 241969 = 181477) (by norm_num)
theorem B340301 : Blo 211809 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B242005 : Blo 211809 242005 := bbase (se 10 (by rfl) ⟨354, by rfl⟩ : syracuseStep 242005 = 709) (by norm_num)
theorem B242041 : Blo 211809 242041 := bbase (se 2 (by rfl) ⟨90765, by rfl⟩ : syracuseStep 242041 = 181531) (by norm_num)
theorem B405901 : Blo 211809 405901 := bbase (se 3 (by rfl) ⟨76106, by rfl⟩ : syracuseStep 405901 = 152213) (by norm_num)
theorem B536989 : Blo 211809 536989 := bbase (se 3 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 536989 = 201371) (by norm_num)
theorem B242077 : Blo 211809 242077 := bbase (se 3 (by rfl) ⟨45389, by rfl⟩ : syracuseStep 242077 = 90779) (by norm_num)
theorem B242113 : Blo 211809 242113 := bbase (se 2 (by rfl) ⟨90792, by rfl⟩ : syracuseStep 242113 = 181585) (by norm_num)
theorem B242129 : Blo 211809 242129 := bbase (se 2 (by rfl) ⟨90798, by rfl⟩ : syracuseStep 242129 = 181597) (by norm_num)
theorem B242149 : Blo 211809 242149 := bbase (se 4 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 242149 = 45403) (by norm_num)
theorem B274925 : Blo 211809 274925 := bbase (se 3 (by rfl) ⟨51548, by rfl⟩ : syracuseStep 274925 = 103097) (by norm_num)
theorem B471557 : Blo 211809 471557 := bbase (se 4 (by rfl) ⟨44208, by rfl⟩ : syracuseStep 471557 = 88417) (by norm_num)
theorem B242185 : Blo 211809 242185 := bbase (se 2 (by rfl) ⟨90819, by rfl⟩ : syracuseStep 242185 = 181639) (by norm_num)
theorem B537101 : Blo 211809 537101 := bbase (se 3 (by rfl) ⟨100706, by rfl⟩ : syracuseStep 537101 = 201413) (by norm_num)
theorem B242221 : Blo 211809 242221 := bbase (se 3 (by rfl) ⟨45416, by rfl⟩ : syracuseStep 242221 = 90833) (by norm_num)
theorem B242257 : Blo 211809 242257 := bbase (se 2 (by rfl) ⟨90846, by rfl⟩ : syracuseStep 242257 = 181693) (by norm_num)
theorem B242293 : Blo 211809 242293 := bbase (se 5 (by rfl) ⟨11357, by rfl⟩ : syracuseStep 242293 = 22715) (by norm_num)
theorem B2765461 : Blo 211809 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B242329 : Blo 211809 242329 := bbase (se 2 (by rfl) ⟨90873, by rfl⟩ : syracuseStep 242329 = 181747) (by norm_num)
theorem B406205 : Blo 211809 406205 := bbase (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) (by norm_num)
theorem B242365 : Blo 211809 242365 := bbase (se 3 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 242365 = 90887) (by norm_num)
theorem B537293 : Blo 211809 537293 := bbase (se 3 (by rfl) ⟨100742, by rfl⟩ : syracuseStep 537293 = 201485) (by norm_num)
theorem B242401 : Blo 211809 242401 := bbase (se 2 (by rfl) ⟨90900, by rfl⟩ : syracuseStep 242401 = 181801) (by norm_num)
theorem B275177 : Blo 211809 275177 := bbase (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) (by norm_num)
theorem B242437 : Blo 211809 242437 := bbase (se 4 (by rfl) ⟨22728, by rfl⟩ : syracuseStep 242437 = 45457) (by norm_num)
theorem B340757 : Blo 211809 340757 := bbase (se 6 (by rfl) ⟨7986, by rfl⟩ : syracuseStep 340757 = 15973) (by norm_num)
theorem B242473 : Blo 211809 242473 := bbase (se 2 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 242473 = 181855) (by norm_num)
theorem B242509 : Blo 211809 242509 := bbase (se 3 (by rfl) ⟨45470, by rfl⟩ : syracuseStep 242509 = 90941) (by norm_num)
theorem B1160021 : Blo 211809 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B242545 : Blo 211809 242545 := bbase (se 2 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 242545 = 181909) (by norm_num)
theorem B242581 : Blo 211809 242581 := bbase (se 6 (by rfl) ⟨5685, by rfl⟩ : syracuseStep 242581 = 11371) (by norm_num)
theorem B242617 : Blo 211809 242617 := bbase (se 2 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 242617 = 181963) (by norm_num)
theorem B3683285 : Blo 211809 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B242653 : Blo 211809 242653 := bbase (se 3 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 242653 = 90995) (by norm_num)
theorem B242689 : Blo 211809 242689 := bbase (se 2 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 242689 = 182017) (by norm_num)
theorem B537637 : Blo 211809 537637 := bbase (se 4 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 537637 = 100807) (by norm_num)
theorem B242725 : Blo 211809 242725 := bbase (se 4 (by rfl) ⟨22755, by rfl⟩ : syracuseStep 242725 = 45511) (by norm_num)
theorem B242761 : Blo 211809 242761 := bbase (se 2 (by rfl) ⟨91035, by rfl⟩ : syracuseStep 242761 = 182071) (by norm_num)
theorem B1225813 : Blo 211809 1225813 := bbase (se 8 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 1225813 = 14365) (by norm_num)
theorem B537749 : Blo 211809 537749 := bbase (se 6 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 537749 = 25207) (by norm_num)
theorem B243005 : Blo 211809 243005 := bbase (se 3 (by rfl) ⟨45563, by rfl⟩ : syracuseStep 243005 = 91127) (by norm_num)
theorem B275789 : Blo 211809 275789 := bbase (se 3 (by rfl) ⟨51710, by rfl⟩ : syracuseStep 275789 = 103421) (by norm_num)
theorem B537941 : Blo 211809 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B308605 : Blo 211809 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B406957 : Blo 211809 406957 := bbase (se 3 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 406957 = 152609) (by norm_num)
theorem B407101 : Blo 211809 407101 := bbase (se 3 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 407101 = 152663) (by norm_num)
theorem B603749 : Blo 211809 603749 := bbase (se 4 (by rfl) ⟨56601, by rfl⟩ : syracuseStep 603749 = 113203) (by norm_num)
theorem B243361 : Blo 211809 243361 := bbase (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) (by norm_num)
theorem B538285 : Blo 211809 538285 := bbase (se 3 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 538285 = 201857) (by norm_num)
theorem B407261 : Blo 211809 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B341749 : Blo 211809 341749 := bbase (se 5 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 341749 = 32039) (by norm_num)
theorem B538397 : Blo 211809 538397 := bbase (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) (by norm_num)
theorem B407405 : Blo 211809 407405 := bbase (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) (by norm_num)
theorem B1357717 : Blo 211809 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B538589 : Blo 211809 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B407693 : Blo 211809 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B407845 : Blo 211809 407845 := bbase (se 4 (by rfl) ⟨38235, by rfl⟩ : syracuseStep 407845 = 76471) (by norm_num)
theorem B538933 : Blo 211809 538933 := bbase (se 5 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 538933 = 50525) (by norm_num)
theorem B342397 : Blo 211809 342397 := bbase (se 3 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 342397 = 128399) (by norm_num)
theorem B539045 : Blo 211809 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B440749 : Blo 211809 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B408149 : Blo 211809 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B539237 : Blo 211809 539237 := bbase (se 4 (by rfl) ⟨50553, by rfl⟩ : syracuseStep 539237 = 101107) (by norm_num)
theorem B1096597 : Blo 211809 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B408485 : Blo 211809 408485 := bbase (se 4 (by rfl) ⟨38295, by rfl⟩ : syracuseStep 408485 = 76591) (by norm_num)
theorem B539581 : Blo 211809 539581 := bbase (se 3 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 539581 = 202343) (by norm_num)
theorem B1227797 : Blo 211809 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B539693 : Blo 211809 539693 := bbase (se 3 (by rfl) ⟨101192, by rfl⟩ : syracuseStep 539693 = 202385) (by norm_num)
theorem B605333 : Blo 211809 605333 := bbase (se 6 (by rfl) ⟨14187, by rfl⟩ : syracuseStep 605333 = 28375) (by norm_num)
theorem B277705 : Blo 211809 277705 := bbase (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) (by norm_num)
theorem B539885 : Blo 211809 539885 := bbase (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) (by norm_num)
theorem B343325 : Blo 211809 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B408901 : Blo 211809 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B4078997 : Blo 211809 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B409045 : Blo 211809 409045 := bbase (se 7 (by rfl) ⟨4793, by rfl⟩ : syracuseStep 409045 = 9587) (by norm_num)
theorem B245305 : Blo 211809 245305 := bbase (se 2 (by rfl) ⟨91989, by rfl⟩ : syracuseStep 245305 = 183979) (by norm_num)
theorem B540229 : Blo 211809 540229 := bbase (se 4 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 540229 = 101293) (by norm_num)
theorem B409205 : Blo 211809 409205 := bbase (se 5 (by rfl) ⟨19181, by rfl⟩ : syracuseStep 409205 = 38363) (by norm_num)
theorem B245413 : Blo 211809 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B540341 : Blo 211809 540341 := bbase (se 5 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 540341 = 50657) (by norm_num)
theorem B343781 : Blo 211809 343781 := bbase (se 4 (by rfl) ⟨32229, by rfl⟩ : syracuseStep 343781 = 64459) (by norm_num)
theorem B409349 : Blo 211809 409349 := bbase (se 4 (by rfl) ⟨38376, by rfl⟩ : syracuseStep 409349 = 76753) (by norm_num)
theorem B1621781 : Blo 211809 1621781 := bbase (se 6 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 1621781 = 76021) (by norm_num)
theorem B606005 : Blo 211809 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B540533 : Blo 211809 540533 := bbase (se 5 (by rfl) ⟨25337, by rfl⟩ : syracuseStep 540533 = 50675) (by norm_num)
theorem B409637 : Blo 211809 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B606341 : Blo 211809 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B540877 : Blo 211809 540877 := bbase (se 3 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 540877 = 202829) (by norm_num)
theorem B606437 : Blo 211809 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B246025 : Blo 211809 246025 := bbase (se 2 (by rfl) ⟨92259, by rfl⟩ : syracuseStep 246025 = 184519) (by norm_num)
theorem B1294613 : Blo 211809 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B540989 : Blo 211809 540989 := bbase (se 3 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 540989 = 202871) (by norm_num)
theorem B770405 : Blo 211809 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B311693 : Blo 211809 311693 := bbase (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) (by norm_num)
theorem B541181 : Blo 211809 541181 := bbase (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) (by norm_num)
theorem B574085 : Blo 211809 574085 := bbase (se 4 (by rfl) ⟨53820, by rfl⟩ : syracuseStep 574085 = 107641) (by norm_num)
theorem B770741 : Blo 211809 770741 := bbase (se 5 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 770741 = 72257) (by norm_num)
theorem B344893 : Blo 211809 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B541525 : Blo 211809 541525 := bbase (se 9 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 541525 = 3173) (by norm_num)
theorem B934789 : Blo 211809 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B541637 : Blo 211809 541637 := bbase (se 4 (by rfl) ⟨50778, by rfl⟩ : syracuseStep 541637 = 101557) (by norm_num)
theorem B607189 : Blo 211809 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B508933 : Blo 211809 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B345197 : Blo 211809 345197 := bbase (se 3 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 345197 = 129449) (by norm_num)
theorem B541829 : Blo 211809 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B345421 : Blo 211809 345421 := bbase (se 3 (by rfl) ⟨64766, by rfl⟩ : syracuseStep 345421 = 129533) (by norm_num)
theorem B2049461 : Blo 211809 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B476621 : Blo 211809 476621 := bbase (se 3 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 476621 = 178733) (by norm_num)
theorem B2803157 : Blo 211809 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B411101 : Blo 211809 411101 := bbase (se 3 (by rfl) ⟨77081, by rfl⟩ : syracuseStep 411101 = 154163) (by norm_num)
theorem B542173 : Blo 211809 542173 := bbase (se 3 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 542173 = 203315) (by norm_num)
theorem B509453 : Blo 211809 509453 := bbase (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) (by norm_num)
theorem B476693 : Blo 211809 476693 := bbase (se 6 (by rfl) ⟨11172, by rfl⟩ : syracuseStep 476693 = 22345) (by norm_num)
theorem B542285 : Blo 211809 542285 := bbase (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) (by norm_num)
theorem B804437 : Blo 211809 804437 := bbase (se 8 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 804437 = 9427) (by norm_num)
theorem B476765 : Blo 211809 476765 := bbase (se 3 (by rfl) ⟨89393, by rfl⟩ : syracuseStep 476765 = 178787) (by norm_num)
theorem B345725 : Blo 211809 345725 := bbase (se 3 (by rfl) ⟨64823, by rfl⟩ : syracuseStep 345725 = 129647) (by norm_num)
theorem B476837 : Blo 211809 476837 := bbase (se 4 (by rfl) ⟨44703, by rfl⟩ : syracuseStep 476837 = 89407) (by norm_num)
theorem B476909 : Blo 211809 476909 := bbase (se 3 (by rfl) ⟨89420, by rfl⟩ : syracuseStep 476909 = 178841) (by norm_num)
theorem B1033973 : Blo 211809 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B542477 : Blo 211809 542477 := bbase (se 3 (by rfl) ⟨101714, by rfl⟩ : syracuseStep 542477 = 203429) (by norm_num)
theorem B476981 : Blo 211809 476981 := bbase (se 5 (by rfl) ⟨22358, by rfl⟩ : syracuseStep 476981 = 44717) (by norm_num)
theorem B1361717 : Blo 211809 1361717 := bbase (se 5 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 1361717 = 127661) (by norm_num)
theorem B771893 : Blo 211809 771893 := bbase (se 5 (by rfl) ⟨36182, by rfl⟩ : syracuseStep 771893 = 72365) (by norm_num)
theorem B804725 : Blo 211809 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B477053 : Blo 211809 477053 := bbase (se 3 (by rfl) ⟨89447, by rfl⟩ : syracuseStep 477053 = 178895) (by norm_num)
theorem B477125 : Blo 211809 477125 := bbase (se 4 (by rfl) ⟨44730, by rfl⟩ : syracuseStep 477125 = 89461) (by norm_num)
theorem B477197 : Blo 211809 477197 := bbase (se 3 (by rfl) ⟨89474, by rfl⟩ : syracuseStep 477197 = 178949) (by norm_num)
theorem B509981 : Blo 211809 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B477269 : Blo 211809 477269 := bbase (se 8 (by rfl) ⟨2796, by rfl⟩ : syracuseStep 477269 = 5593) (by norm_num)
theorem B247901 : Blo 211809 247901 := bbase (se 3 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 247901 = 92963) (by norm_num)
theorem B542821 : Blo 211809 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B215185 : Blo 211809 215185 := bbase (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) (by norm_num)
theorem B1230997 : Blo 211809 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B477341 : Blo 211809 477341 := bbase (se 3 (by rfl) ⟨89501, by rfl⟩ : syracuseStep 477341 = 179003) (by norm_num)
theorem B542933 : Blo 211809 542933 := bbase (se 7 (by rfl) ⟨6362, by rfl⟩ : syracuseStep 542933 = 12725) (by norm_num)
theorem B477413 : Blo 211809 477413 := bbase (se 4 (by rfl) ⟨44757, by rfl⟩ : syracuseStep 477413 = 89515) (by norm_num)
theorem B510221 : Blo 211809 510221 := bbase (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) (by norm_num)
theorem B477485 : Blo 211809 477485 := bbase (se 3 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 477485 = 179057) (by norm_num)
theorem B477557 : Blo 211809 477557 := bbase (se 5 (by rfl) ⟨22385, by rfl⟩ : syracuseStep 477557 = 44771) (by norm_num)
theorem B543125 : Blo 211809 543125 := bbase (se 6 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 543125 = 25459) (by norm_num)
theorem B1100213 : Blo 211809 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B477629 : Blo 211809 477629 := bbase (se 3 (by rfl) ⟨89555, by rfl⟩ : syracuseStep 477629 = 179111) (by norm_num)
theorem B477701 : Blo 211809 477701 := bbase (se 4 (by rfl) ⟨44784, by rfl⟩ : syracuseStep 477701 = 89569) (by norm_num)
theorem B477773 : Blo 211809 477773 := bbase (se 3 (by rfl) ⟨89582, by rfl⟩ : syracuseStep 477773 = 179165) (by norm_num)
theorem B477845 : Blo 211809 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B477917 : Blo 211809 477917 := bbase (se 3 (by rfl) ⟨89609, by rfl⟩ : syracuseStep 477917 = 179219) (by norm_num)
theorem B543469 : Blo 211809 543469 := bbase (se 3 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 543469 = 203801) (by norm_num)
theorem B477989 : Blo 211809 477989 := bbase (se 4 (by rfl) ⟨44811, by rfl⟩ : syracuseStep 477989 = 89623) (by norm_num)
theorem B543581 : Blo 211809 543581 := bbase (se 3 (by rfl) ⟨101921, by rfl⟩ : syracuseStep 543581 = 203843) (by norm_num)
theorem B478061 : Blo 211809 478061 := bbase (se 3 (by rfl) ⟨89636, by rfl⟩ : syracuseStep 478061 = 179273) (by norm_num)
theorem B478133 : Blo 211809 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B478205 : Blo 211809 478205 := bbase (se 3 (by rfl) ⟨89663, by rfl⟩ : syracuseStep 478205 = 179327) (by norm_num)
theorem B248845 : Blo 211809 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B805909 : Blo 211809 805909 := bbase (se 6 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 805909 = 37777) (by norm_num)
theorem B543773 : Blo 211809 543773 := bbase (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) (by norm_num)
theorem B773173 : Blo 211809 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B478277 : Blo 211809 478277 := bbase (se 4 (by rfl) ⟨44838, by rfl⟩ : syracuseStep 478277 = 89677) (by norm_num)
theorem B478349 : Blo 211809 478349 := bbase (se 3 (by rfl) ⟨89690, by rfl⟩ : syracuseStep 478349 = 179381) (by norm_num)
theorem B543941 : Blo 211809 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B478421 : Blo 211809 478421 := bbase (se 7 (by rfl) ⟨5606, by rfl⟩ : syracuseStep 478421 = 11213) (by norm_num)
theorem B216317 : Blo 211809 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B642325 : Blo 211809 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B478493 : Blo 211809 478493 := bbase (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) (by norm_num)
theorem B806213 : Blo 211809 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B216401 : Blo 211809 216401 := bbase (se 2 (by rfl) ⟨81150, by rfl⟩ : syracuseStep 216401 = 162301) (by norm_num)
theorem B478565 : Blo 211809 478565 := bbase (se 4 (by rfl) ⟨44865, by rfl⟩ : syracuseStep 478565 = 89731) (by norm_num)
theorem B544117 : Blo 211809 544117 := bbase (se 5 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 544117 = 51011) (by norm_num)
theorem B478637 : Blo 211809 478637 := bbase (se 3 (by rfl) ⟨89744, by rfl⟩ : syracuseStep 478637 = 179489) (by norm_num)
theorem B544229 : Blo 211809 544229 := bbase (se 4 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 544229 = 102043) (by norm_num)
theorem B478709 : Blo 211809 478709 := bbase (se 5 (by rfl) ⟨22439, by rfl⟩ : syracuseStep 478709 = 44879) (by norm_num)
theorem B478781 : Blo 211809 478781 := bbase (se 3 (by rfl) ⟨89771, by rfl⟩ : syracuseStep 478781 = 179543) (by norm_num)
theorem B478853 : Blo 211809 478853 := bbase (se 4 (by rfl) ⟨44892, by rfl⟩ : syracuseStep 478853 = 89785) (by norm_num)
theorem B544421 : Blo 211809 544421 := bbase (se 4 (by rfl) ⟨51039, by rfl⟩ : syracuseStep 544421 = 102079) (by norm_num)
theorem B478925 : Blo 211809 478925 := bbase (se 3 (by rfl) ⟨89798, by rfl⟩ : syracuseStep 478925 = 179597) (by norm_num)
theorem B610037 : Blo 211809 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B478997 : Blo 211809 478997 := bbase (se 6 (by rfl) ⟨11226, by rfl⟩ : syracuseStep 478997 = 22453) (by norm_num)
theorem B479069 : Blo 211809 479069 := bbase (se 3 (by rfl) ⟨89825, by rfl⟩ : syracuseStep 479069 = 179651) (by norm_num)
theorem B479141 : Blo 211809 479141 := bbase (se 4 (by rfl) ⟨44919, by rfl⟩ : syracuseStep 479141 = 89839) (by norm_num)
theorem B511933 : Blo 211809 511933 := bbase (se 3 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 511933 = 191975) (by norm_num)
theorem B479213 : Blo 211809 479213 := bbase (se 3 (by rfl) ⟨89852, by rfl⟩ : syracuseStep 479213 = 179705) (by norm_num)
theorem B544765 : Blo 211809 544765 := bbase (se 3 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 544765 = 204287) (by norm_num)
theorem B479285 : Blo 211809 479285 := bbase (se 5 (by rfl) ⟨22466, by rfl⟩ : syracuseStep 479285 = 44933) (by norm_num)
theorem B544877 : Blo 211809 544877 := bbase (se 3 (by rfl) ⟨102164, by rfl⟩ : syracuseStep 544877 = 204329) (by norm_num)
theorem B479357 : Blo 211809 479357 := bbase (se 3 (by rfl) ⟨89879, by rfl⟩ : syracuseStep 479357 = 179759) (by norm_num)
theorem B479429 : Blo 211809 479429 := bbase (se 4 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 479429 = 89893) (by norm_num)
theorem B479501 : Blo 211809 479501 := bbase (se 3 (by rfl) ⟨89906, by rfl⟩ : syracuseStep 479501 = 179813) (by norm_num)
theorem B545069 : Blo 211809 545069 := bbase (se 3 (by rfl) ⟨102200, by rfl⟩ : syracuseStep 545069 = 204401) (by norm_num)
theorem B479573 : Blo 211809 479573 := bbase (se 10 (by rfl) ⟨702, by rfl⟩ : syracuseStep 479573 = 1405) (by norm_num)
theorem B479645 : Blo 211809 479645 := bbase (se 3 (by rfl) ⟨89933, by rfl⟩ : syracuseStep 479645 = 179867) (by norm_num)
theorem B1036741 : Blo 211809 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B479717 : Blo 211809 479717 := bbase (se 4 (by rfl) ⟨44973, by rfl⟩ : syracuseStep 479717 = 89947) (by norm_num)
theorem B1102325 : Blo 211809 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B479789 : Blo 211809 479789 := bbase (se 3 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 479789 = 179921) (by norm_num)
theorem B905813 : Blo 211809 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B479861 : Blo 211809 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B545413 : Blo 211809 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B479933 : Blo 211809 479933 := bbase (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) (by norm_num)
theorem B217825 : Blo 211809 217825 := bbase (se 2 (by rfl) ⟨81684, by rfl⟩ : syracuseStep 217825 = 163369) (by norm_num)
theorem B217829 : Blo 211809 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B545525 : Blo 211809 545525 := bbase (se 5 (by rfl) ⟨25571, by rfl⟩ : syracuseStep 545525 = 51143) (by norm_num)
theorem B480005 : Blo 211809 480005 := bbase (se 4 (by rfl) ⟨45000, by rfl⟩ : syracuseStep 480005 = 90001) (by norm_num)
theorem B480077 : Blo 211809 480077 := bbase (se 3 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 480077 = 180029) (by norm_num)
theorem B480149 : Blo 211809 480149 := bbase (se 6 (by rfl) ⟨11253, by rfl⟩ : syracuseStep 480149 = 22507) (by norm_num)
theorem B611221 : Blo 211809 611221 := bbase (se 6 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 611221 = 28651) (by norm_num)
theorem B545717 : Blo 211809 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B381917 : Blo 211809 381917 := bbase (se 3 (by rfl) ⟨71609, by rfl⟩ : syracuseStep 381917 = 143219) (by norm_num)
theorem B480221 : Blo 211809 480221 := bbase (se 3 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 480221 = 180083) (by norm_num)
theorem B480293 : Blo 211809 480293 := bbase (se 4 (by rfl) ⟨45027, by rfl⟩ : syracuseStep 480293 = 90055) (by norm_num)
theorem B611381 : Blo 211809 611381 := bbase (se 5 (by rfl) ⟨28658, by rfl⟩ : syracuseStep 611381 = 57317) (by norm_num)
theorem B480365 : Blo 211809 480365 := bbase (se 3 (by rfl) ⟨90068, by rfl⟩ : syracuseStep 480365 = 180137) (by norm_num)
theorem B480437 : Blo 211809 480437 := bbase (se 5 (by rfl) ⟨22520, by rfl⟩ : syracuseStep 480437 = 45041) (by norm_num)
theorem B480509 : Blo 211809 480509 := bbase (se 3 (by rfl) ⟨90095, by rfl⟩ : syracuseStep 480509 = 180191) (by norm_num)
theorem B546061 : Blo 211809 546061 := bbase (se 3 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 546061 = 204773) (by norm_num)
theorem B611621 : Blo 211809 611621 := bbase (se 4 (by rfl) ⟨57339, by rfl⟩ : syracuseStep 611621 = 114679) (by norm_num)
theorem B382277 : Blo 211809 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B480581 : Blo 211809 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B513373 : Blo 211809 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B218461 : Blo 211809 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B546173 : Blo 211809 546173 := bbase (se 3 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 546173 = 204815) (by norm_num)
theorem B808325 : Blo 211809 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B480653 : Blo 211809 480653 := bbase (se 3 (by rfl) ⟨90122, by rfl⟩ : syracuseStep 480653 = 180245) (by norm_num)
theorem B480725 : Blo 211809 480725 := bbase (se 7 (by rfl) ⟨5633, by rfl⟩ : syracuseStep 480725 = 11267) (by norm_num)
theorem B382429 : Blo 211809 382429 := bbase (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) (by norm_num)
theorem B611813 : Blo 211809 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B480797 : Blo 211809 480797 := bbase (se 3 (by rfl) ⟨90149, by rfl⟩ : syracuseStep 480797 = 180299) (by norm_num)
theorem B579125 : Blo 211809 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B906821 : Blo 211809 906821 := bbase (se 4 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 906821 = 170029) (by norm_num)
theorem B480869 : Blo 211809 480869 := bbase (se 4 (by rfl) ⟨45081, by rfl⟩ : syracuseStep 480869 = 90163) (by norm_num)
theorem B218737 : Blo 211809 218737 := bbase (se 2 (by rfl) ⟨82026, by rfl⟩ : syracuseStep 218737 = 164053) (by norm_num)
theorem B808613 : Blo 211809 808613 := bbase (se 4 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 808613 = 151615) (by norm_num)
theorem B480941 : Blo 211809 480941 := bbase (se 3 (by rfl) ⟨90176, by rfl⟩ : syracuseStep 480941 = 180353) (by norm_num)
theorem B481013 : Blo 211809 481013 := bbase (se 5 (by rfl) ⟨22547, by rfl⟩ : syracuseStep 481013 = 45095) (by norm_num)
theorem B481085 : Blo 211809 481085 := bbase (se 3 (by rfl) ⟨90203, by rfl⟩ : syracuseStep 481085 = 180407) (by norm_num)
theorem B481157 : Blo 211809 481157 := bbase (se 4 (by rfl) ⟨45108, by rfl⟩ : syracuseStep 481157 = 90217) (by norm_num)
theorem B350125 : Blo 211809 350125 := bbase (se 3 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 350125 = 131297) (by norm_num)
theorem B513989 : Blo 211809 513989 := bbase (se 4 (by rfl) ⟨48186, by rfl⟩ : syracuseStep 513989 = 96373) (by norm_num)
theorem B481229 : Blo 211809 481229 := bbase (se 3 (by rfl) ⟨90230, by rfl⟩ : syracuseStep 481229 = 180461) (by norm_num)
theorem B481301 : Blo 211809 481301 := bbase (se 6 (by rfl) ⟨11280, by rfl⟩ : syracuseStep 481301 = 22561) (by norm_num)
theorem B481373 : Blo 211809 481373 := bbase (se 3 (by rfl) ⟨90257, by rfl⟩ : syracuseStep 481373 = 180515) (by norm_num)
theorem B546925 : Blo 211809 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B2054261 : Blo 211809 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B514181 : Blo 211809 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B481445 : Blo 211809 481445 := bbase (se 4 (by rfl) ⟨45135, by rfl⟩ : syracuseStep 481445 = 90271) (by norm_num)
theorem B1300693 : Blo 211809 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B481517 : Blo 211809 481517 := bbase (se 3 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 481517 = 180569) (by norm_num)
theorem B547069 : Blo 211809 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B317717 : Blo 211809 317717 := bbase (se 6 (by rfl) ⟨7446, by rfl⟩ : syracuseStep 317717 = 14893) (by norm_num)
theorem B317741 : Blo 211809 317741 := bbase (se 3 (by rfl) ⟨59576, by rfl⟩ : syracuseStep 317741 = 119153) (by norm_num)
theorem B481589 : Blo 211809 481589 := bbase (se 5 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 481589 = 45149) (by norm_num)
theorem B317765 : Blo 211809 317765 := bbase (se 4 (by rfl) ⟨29790, by rfl⟩ : syracuseStep 317765 = 59581) (by norm_num)
theorem B317789 : Blo 211809 317789 := bbase (se 3 (by rfl) ⟨59585, by rfl⟩ : syracuseStep 317789 = 119171) (by norm_num)
theorem B317813 : Blo 211809 317813 := bbase (se 5 (by rfl) ⟨14897, by rfl⟩ : syracuseStep 317813 = 29795) (by norm_num)
theorem B481661 : Blo 211809 481661 := bbase (se 3 (by rfl) ⟨90311, by rfl⟩ : syracuseStep 481661 = 180623) (by norm_num)
theorem B317837 : Blo 211809 317837 := bbase (se 3 (by rfl) ⟨59594, by rfl⟩ : syracuseStep 317837 = 119189) (by norm_num)
theorem B317861 : Blo 211809 317861 := bbase (se 4 (by rfl) ⟨29799, by rfl⟩ : syracuseStep 317861 = 59599) (by norm_num)
theorem B514469 : Blo 211809 514469 := bbase (se 4 (by rfl) ⟨48231, by rfl⟩ : syracuseStep 514469 = 96463) (by norm_num)
theorem B317885 : Blo 211809 317885 := bbase (se 3 (by rfl) ⟨59603, by rfl⟩ : syracuseStep 317885 = 119207) (by norm_num)
theorem B481733 : Blo 211809 481733 := bbase (se 4 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 481733 = 90325) (by norm_num)
theorem B612805 : Blo 211809 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B317909 : Blo 211809 317909 := bbase (se 7 (by rfl) ⟨3725, by rfl⟩ : syracuseStep 317909 = 7451) (by norm_num)
theorem B317933 : Blo 211809 317933 := bbase (se 3 (by rfl) ⟨59612, by rfl⟩ : syracuseStep 317933 = 119225) (by norm_num)
theorem B317957 : Blo 211809 317957 := bbase (se 4 (by rfl) ⟨29808, by rfl⟩ : syracuseStep 317957 = 59617) (by norm_num)
theorem B481805 : Blo 211809 481805 := bbase (se 3 (by rfl) ⟨90338, by rfl⟩ : syracuseStep 481805 = 180677) (by norm_num)
theorem B317981 : Blo 211809 317981 := bbase (se 3 (by rfl) ⟨59621, by rfl⟩ : syracuseStep 317981 = 119243) (by norm_num)
theorem B383525 : Blo 211809 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B318005 : Blo 211809 318005 := bbase (se 5 (by rfl) ⟨14906, by rfl⟩ : syracuseStep 318005 = 29813) (by norm_num)
theorem B318029 : Blo 211809 318029 := bbase (se 3 (by rfl) ⟨59630, by rfl⟩ : syracuseStep 318029 = 119261) (by norm_num)
theorem B481877 : Blo 211809 481877 := bbase (se 8 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 481877 = 5647) (by norm_num)
theorem B318053 : Blo 211809 318053 := bbase (se 4 (by rfl) ⟨29817, by rfl⟩ : syracuseStep 318053 = 59635) (by norm_num)
theorem B318077 : Blo 211809 318077 := bbase (se 3 (by rfl) ⟨59639, by rfl⟩ : syracuseStep 318077 = 119279) (by norm_num)
theorem B318101 : Blo 211809 318101 := bbase (se 6 (by rfl) ⟨7455, by rfl⟩ : syracuseStep 318101 = 14911) (by norm_num)
theorem B481949 : Blo 211809 481949 := bbase (se 3 (by rfl) ⟨90365, by rfl⟩ : syracuseStep 481949 = 180731) (by norm_num)
theorem B318125 : Blo 211809 318125 := bbase (se 3 (by rfl) ⟨59648, by rfl⟩ : syracuseStep 318125 = 119297) (by norm_num)
theorem B318149 : Blo 211809 318149 := bbase (se 4 (by rfl) ⟨29826, by rfl⟩ : syracuseStep 318149 = 59653) (by norm_num)
theorem B318173 : Blo 211809 318173 := bbase (se 3 (by rfl) ⟨59657, by rfl⟩ : syracuseStep 318173 = 119315) (by norm_num)
theorem B482021 : Blo 211809 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B318197 : Blo 211809 318197 := bbase (se 5 (by rfl) ⟨14915, by rfl⟩ : syracuseStep 318197 = 29831) (by norm_num)
theorem B318221 : Blo 211809 318221 := bbase (se 3 (by rfl) ⟨59666, by rfl⟩ : syracuseStep 318221 = 119333) (by norm_num)
theorem B318245 : Blo 211809 318245 := bbase (se 4 (by rfl) ⟨29835, by rfl⟩ : syracuseStep 318245 = 59671) (by norm_num)
theorem B482093 : Blo 211809 482093 := bbase (se 3 (by rfl) ⟨90392, by rfl⟩ : syracuseStep 482093 = 180785) (by norm_num)
theorem B318269 : Blo 211809 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B809797 : Blo 211809 809797 := bbase (se 4 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 809797 = 151837) (by norm_num)
theorem B318293 : Blo 211809 318293 := bbase (se 9 (by rfl) ⟨932, by rfl⟩ : syracuseStep 318293 = 1865) (by norm_num)
theorem B318317 : Blo 211809 318317 := bbase (se 3 (by rfl) ⟨59684, by rfl⟩ : syracuseStep 318317 = 119369) (by norm_num)
theorem B482165 : Blo 211809 482165 := bbase (se 5 (by rfl) ⟨22601, by rfl⟩ : syracuseStep 482165 = 45203) (by norm_num)
theorem B318341 : Blo 211809 318341 := bbase (se 4 (by rfl) ⟨29844, by rfl⟩ : syracuseStep 318341 = 59689) (by norm_num)
theorem B318365 : Blo 211809 318365 := bbase (se 3 (by rfl) ⟨59693, by rfl⟩ : syracuseStep 318365 = 119387) (by norm_num)
theorem B318389 : Blo 211809 318389 := bbase (se 5 (by rfl) ⟨14924, by rfl⟩ : syracuseStep 318389 = 29849) (by norm_num)
theorem B482237 : Blo 211809 482237 := bbase (se 3 (by rfl) ⟨90419, by rfl⟩ : syracuseStep 482237 = 180839) (by norm_num)
theorem B318413 : Blo 211809 318413 := bbase (se 3 (by rfl) ⟨59702, by rfl⟩ : syracuseStep 318413 = 119405) (by norm_num)
theorem B318437 : Blo 211809 318437 := bbase (se 4 (by rfl) ⟨29853, by rfl⟩ : syracuseStep 318437 = 59707) (by norm_num)
theorem B318461 : Blo 211809 318461 := bbase (se 3 (by rfl) ⟨59711, by rfl⟩ : syracuseStep 318461 = 119423) (by norm_num)
theorem B482309 : Blo 211809 482309 := bbase (se 4 (by rfl) ⟨45216, by rfl⟩ : syracuseStep 482309 = 90433) (by norm_num)
theorem B318485 : Blo 211809 318485 := bbase (se 6 (by rfl) ⟨7464, by rfl⟩ : syracuseStep 318485 = 14929) (by norm_num)
theorem B318509 : Blo 211809 318509 := bbase (se 3 (by rfl) ⟨59720, by rfl⟩ : syracuseStep 318509 = 119441) (by norm_num)
theorem B777269 : Blo 211809 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B318533 : Blo 211809 318533 := bbase (se 4 (by rfl) ⟨29862, by rfl⟩ : syracuseStep 318533 = 59725) (by norm_num)
theorem B482381 : Blo 211809 482381 := bbase (se 3 (by rfl) ⟨90446, by rfl⟩ : syracuseStep 482381 = 180893) (by norm_num)
theorem B318557 : Blo 211809 318557 := bbase (se 3 (by rfl) ⟨59729, by rfl⟩ : syracuseStep 318557 = 119459) (by norm_num)
theorem B679013 : Blo 211809 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B318581 : Blo 211809 318581 := bbase (se 5 (by rfl) ⟨14933, by rfl⟩ : syracuseStep 318581 = 29867) (by norm_num)
theorem B810101 : Blo 211809 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B318605 : Blo 211809 318605 := bbase (se 3 (by rfl) ⟨59738, by rfl⟩ : syracuseStep 318605 = 119477) (by norm_num)
theorem B482453 : Blo 211809 482453 := bbase (se 6 (by rfl) ⟨11307, by rfl⟩ : syracuseStep 482453 = 22615) (by norm_num)
theorem B318629 : Blo 211809 318629 := bbase (se 4 (by rfl) ⟨29871, by rfl⟩ : syracuseStep 318629 = 59743) (by norm_num)
theorem B318653 : Blo 211809 318653 := bbase (se 3 (by rfl) ⟨59747, by rfl⟩ : syracuseStep 318653 = 119495) (by norm_num)
theorem B318677 : Blo 211809 318677 := bbase (se 7 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 318677 = 7469) (by norm_num)
theorem B482525 : Blo 211809 482525 := bbase (se 3 (by rfl) ⟨90473, by rfl⟩ : syracuseStep 482525 = 180947) (by norm_num)
theorem B318701 : Blo 211809 318701 := bbase (se 3 (by rfl) ⟨59756, by rfl⟩ : syracuseStep 318701 = 119513) (by norm_num)
theorem B318725 : Blo 211809 318725 := bbase (se 4 (by rfl) ⟨29880, by rfl⟩ : syracuseStep 318725 = 59761) (by norm_num)
theorem B318749 : Blo 211809 318749 := bbase (se 3 (by rfl) ⟨59765, by rfl⟩ : syracuseStep 318749 = 119531) (by norm_num)
theorem B482597 : Blo 211809 482597 := bbase (se 4 (by rfl) ⟨45243, by rfl⟩ : syracuseStep 482597 = 90487) (by norm_num)
theorem B318773 : Blo 211809 318773 := bbase (se 5 (by rfl) ⟨14942, by rfl⟩ : syracuseStep 318773 = 29885) (by norm_num)
theorem B908597 : Blo 211809 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B318797 : Blo 211809 318797 := bbase (se 3 (by rfl) ⟨59774, by rfl⟩ : syracuseStep 318797 = 119549) (by norm_num)
theorem B318821 : Blo 211809 318821 := bbase (se 4 (by rfl) ⟨29889, by rfl⟩ : syracuseStep 318821 = 59779) (by norm_num)
theorem B482669 : Blo 211809 482669 := bbase (se 3 (by rfl) ⟨90500, by rfl⟩ : syracuseStep 482669 = 181001) (by norm_num)
theorem B1629557 : Blo 211809 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B318845 : Blo 211809 318845 := bbase (se 3 (by rfl) ⟨59783, by rfl⟩ : syracuseStep 318845 = 119567) (by norm_num)
theorem B318869 : Blo 211809 318869 := bbase (se 6 (by rfl) ⟨7473, by rfl⟩ : syracuseStep 318869 = 14947) (by norm_num)
theorem B318893 : Blo 211809 318893 := bbase (se 3 (by rfl) ⟨59792, by rfl⟩ : syracuseStep 318893 = 119585) (by norm_num)
theorem B482741 : Blo 211809 482741 := bbase (se 5 (by rfl) ⟨22628, by rfl⟩ : syracuseStep 482741 = 45257) (by norm_num)
theorem B318917 : Blo 211809 318917 := bbase (se 4 (by rfl) ⟨29898, by rfl⟩ : syracuseStep 318917 = 59797) (by norm_num)
theorem B318941 : Blo 211809 318941 := bbase (se 3 (by rfl) ⟨59801, by rfl⟩ : syracuseStep 318941 = 119603) (by norm_num)
theorem B777701 : Blo 211809 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B318965 : Blo 211809 318965 := bbase (se 5 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 318965 = 29903) (by norm_num)
theorem B482813 : Blo 211809 482813 := bbase (se 3 (by rfl) ⟨90527, by rfl⟩ : syracuseStep 482813 = 181055) (by norm_num)
theorem B318989 : Blo 211809 318989 := bbase (se 3 (by rfl) ⟨59810, by rfl⟩ : syracuseStep 318989 = 119621) (by norm_num)
theorem B613909 : Blo 211809 613909 := bbase (se 6 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 613909 = 28777) (by norm_num)
theorem B319013 : Blo 211809 319013 := bbase (se 4 (by rfl) ⟨29907, by rfl⟩ : syracuseStep 319013 = 59815) (by norm_num)
theorem B319037 : Blo 211809 319037 := bbase (se 3 (by rfl) ⟨59819, by rfl⟩ : syracuseStep 319037 = 119639) (by norm_num)
theorem B482885 : Blo 211809 482885 := bbase (se 4 (by rfl) ⟨45270, by rfl⟩ : syracuseStep 482885 = 90541) (by norm_num)
theorem B319061 : Blo 211809 319061 := bbase (se 8 (by rfl) ⟨1869, by rfl⟩ : syracuseStep 319061 = 3739) (by norm_num)
theorem B319085 : Blo 211809 319085 := bbase (se 3 (by rfl) ⟨59828, by rfl⟩ : syracuseStep 319085 = 119657) (by norm_num)
theorem B319109 : Blo 211809 319109 := bbase (se 4 (by rfl) ⟨29916, by rfl⟩ : syracuseStep 319109 = 59833) (by norm_num)
theorem B482957 : Blo 211809 482957 := bbase (se 3 (by rfl) ⟨90554, by rfl⟩ : syracuseStep 482957 = 181109) (by norm_num)
theorem B319133 : Blo 211809 319133 := bbase (se 3 (by rfl) ⟨59837, by rfl⟩ : syracuseStep 319133 = 119675) (by norm_num)
theorem B319157 : Blo 211809 319157 := bbase (se 5 (by rfl) ⟨14960, by rfl⟩ : syracuseStep 319157 = 29921) (by norm_num)
theorem B319181 : Blo 211809 319181 := bbase (se 3 (by rfl) ⟨59846, by rfl⟩ : syracuseStep 319181 = 119693) (by norm_num)
theorem B1367765 : Blo 211809 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B483029 : Blo 211809 483029 := bbase (se 7 (by rfl) ⟨5660, by rfl⟩ : syracuseStep 483029 = 11321) (by norm_num)
theorem B319205 : Blo 211809 319205 := bbase (se 4 (by rfl) ⟨29925, by rfl⟩ : syracuseStep 319205 = 59851) (by norm_num)
theorem B319229 : Blo 211809 319229 := bbase (se 3 (by rfl) ⟨59855, by rfl⟩ : syracuseStep 319229 = 119711) (by norm_num)
theorem B319253 : Blo 211809 319253 := bbase (se 6 (by rfl) ⟨7482, by rfl⟩ : syracuseStep 319253 = 14965) (by norm_num)
theorem B483101 : Blo 211809 483101 := bbase (se 3 (by rfl) ⟨90581, by rfl⟩ : syracuseStep 483101 = 181163) (by norm_num)
theorem B319277 : Blo 211809 319277 := bbase (se 3 (by rfl) ⟨59864, by rfl⟩ : syracuseStep 319277 = 119729) (by norm_num)
theorem B319301 : Blo 211809 319301 := bbase (se 4 (by rfl) ⟨29934, by rfl⟩ : syracuseStep 319301 = 59869) (by norm_num)
theorem B319325 : Blo 211809 319325 := bbase (se 3 (by rfl) ⟨59873, by rfl⟩ : syracuseStep 319325 = 119747) (by norm_num)
theorem B483173 : Blo 211809 483173 := bbase (se 4 (by rfl) ⟨45297, by rfl⟩ : syracuseStep 483173 = 90595) (by norm_num)
theorem B319349 : Blo 211809 319349 := bbase (se 5 (by rfl) ⟨14969, by rfl⟩ : syracuseStep 319349 = 29939) (by norm_num)
theorem B319373 : Blo 211809 319373 := bbase (se 3 (by rfl) ⟨59882, by rfl⟩ : syracuseStep 319373 = 119765) (by norm_num)
theorem B286621 : Blo 211809 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B319397 : Blo 211809 319397 := bbase (se 4 (by rfl) ⟨29943, by rfl⟩ : syracuseStep 319397 = 59887) (by norm_num)
theorem B483245 : Blo 211809 483245 := bbase (se 3 (by rfl) ⟨90608, by rfl⟩ : syracuseStep 483245 = 181217) (by norm_num)
theorem B319421 : Blo 211809 319421 := bbase (se 3 (by rfl) ⟨59891, by rfl⟩ : syracuseStep 319421 = 119783) (by norm_num)
theorem B319445 : Blo 211809 319445 := bbase (se 7 (by rfl) ⟨3743, by rfl⟩ : syracuseStep 319445 = 7487) (by norm_num)
theorem B319469 : Blo 211809 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B483317 : Blo 211809 483317 := bbase (se 5 (by rfl) ⟨22655, by rfl⟩ : syracuseStep 483317 = 45311) (by norm_num)
theorem B319493 : Blo 211809 319493 := bbase (se 4 (by rfl) ⟨29952, by rfl⟩ : syracuseStep 319493 = 59905) (by norm_num)
theorem B319517 : Blo 211809 319517 := bbase (se 3 (by rfl) ⟨59909, by rfl⟩ : syracuseStep 319517 = 119819) (by norm_num)
theorem B319541 : Blo 211809 319541 := bbase (se 5 (by rfl) ⟨14978, by rfl⟩ : syracuseStep 319541 = 29957) (by norm_num)
theorem B483389 : Blo 211809 483389 := bbase (se 3 (by rfl) ⟨90635, by rfl⟩ : syracuseStep 483389 = 181271) (by norm_num)
theorem B319565 : Blo 211809 319565 := bbase (se 3 (by rfl) ⟨59918, by rfl⟩ : syracuseStep 319565 = 119837) (by norm_num)
theorem B548957 : Blo 211809 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B319589 : Blo 211809 319589 := bbase (se 4 (by rfl) ⟨29961, by rfl⟩ : syracuseStep 319589 = 59923) (by norm_num)
theorem B319613 : Blo 211809 319613 := bbase (se 3 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 319613 = 119855) (by norm_num)
theorem B483461 : Blo 211809 483461 := bbase (se 4 (by rfl) ⟨45324, by rfl⟩ : syracuseStep 483461 = 90649) (by norm_num)
theorem B319637 : Blo 211809 319637 := bbase (se 6 (by rfl) ⟨7491, by rfl⟩ : syracuseStep 319637 = 14983) (by norm_num)
theorem B319661 : Blo 211809 319661 := bbase (se 3 (by rfl) ⟨59936, by rfl⟩ : syracuseStep 319661 = 119873) (by norm_num)
theorem B319685 : Blo 211809 319685 := bbase (se 4 (by rfl) ⟨29970, by rfl⟩ : syracuseStep 319685 = 59941) (by norm_num)
theorem B483533 : Blo 211809 483533 := bbase (se 3 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 483533 = 181325) (by norm_num)
theorem B319709 : Blo 211809 319709 := bbase (se 3 (by rfl) ⟨59945, by rfl⟩ : syracuseStep 319709 = 119891) (by norm_num)
theorem B1138933 : Blo 211809 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B319733 : Blo 211809 319733 := bbase (se 5 (by rfl) ⟨14987, by rfl⟩ : syracuseStep 319733 = 29975) (by norm_num)
theorem B319757 : Blo 211809 319757 := bbase (se 3 (by rfl) ⟨59954, by rfl⟩ : syracuseStep 319757 = 119909) (by norm_num)
theorem B483605 : Blo 211809 483605 := bbase (se 6 (by rfl) ⟨11334, by rfl⟩ : syracuseStep 483605 = 22669) (by norm_num)
theorem B319781 : Blo 211809 319781 := bbase (se 4 (by rfl) ⟨29979, by rfl⟩ : syracuseStep 319781 = 59959) (by norm_num)
theorem B319805 : Blo 211809 319805 := bbase (se 3 (by rfl) ⟨59963, by rfl⟩ : syracuseStep 319805 = 119927) (by norm_num)
theorem B581957 : Blo 211809 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B319829 : Blo 211809 319829 := bbase (se 10 (by rfl) ⟨468, by rfl⟩ : syracuseStep 319829 = 937) (by norm_num)
theorem B483677 : Blo 211809 483677 := bbase (se 3 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 483677 = 181379) (by norm_num)
theorem B319853 : Blo 211809 319853 := bbase (se 3 (by rfl) ⟨59972, by rfl⟩ : syracuseStep 319853 = 119945) (by norm_num)
theorem B516469 : Blo 211809 516469 := bbase (se 5 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 516469 = 48419) (by norm_num)
theorem B319877 : Blo 211809 319877 := bbase (se 4 (by rfl) ⟨29988, by rfl⟩ : syracuseStep 319877 = 59977) (by norm_num)
theorem B319901 : Blo 211809 319901 := bbase (se 3 (by rfl) ⟨59981, by rfl⟩ : syracuseStep 319901 = 119963) (by norm_num)
theorem B1073573 : Blo 211809 1073573 := bbase (se 4 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 1073573 = 201295) (by norm_num)
theorem B483749 : Blo 211809 483749 := bbase (se 4 (by rfl) ⟨45351, by rfl⟩ : syracuseStep 483749 = 90703) (by norm_num)
theorem B319925 : Blo 211809 319925 := bbase (se 5 (by rfl) ⟨14996, by rfl⟩ : syracuseStep 319925 = 29993) (by norm_num)
theorem B319949 : Blo 211809 319949 := bbase (se 3 (by rfl) ⟨59990, by rfl⟩ : syracuseStep 319949 = 119981) (by norm_num)
theorem B319973 : Blo 211809 319973 := bbase (se 4 (by rfl) ⟨29997, by rfl⟩ : syracuseStep 319973 = 59995) (by norm_num)
theorem B483821 : Blo 211809 483821 := bbase (se 3 (by rfl) ⟨90716, by rfl⟩ : syracuseStep 483821 = 181433) (by norm_num)
theorem B319997 : Blo 211809 319997 := bbase (se 3 (by rfl) ⟨59999, by rfl⟩ : syracuseStep 319997 = 119999) (by norm_num)
theorem B320021 : Blo 211809 320021 := bbase (se 6 (by rfl) ⟨7500, by rfl⟩ : syracuseStep 320021 = 15001) (by norm_num)
theorem B320045 : Blo 211809 320045 := bbase (se 3 (by rfl) ⟨60008, by rfl⟩ : syracuseStep 320045 = 120017) (by norm_num)
theorem B483893 : Blo 211809 483893 := bbase (se 5 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 483893 = 45365) (by norm_num)
theorem B320069 : Blo 211809 320069 := bbase (se 4 (by rfl) ⟨30006, by rfl⟩ : syracuseStep 320069 = 60013) (by norm_num)
theorem B320093 : Blo 211809 320093 := bbase (se 3 (by rfl) ⟨60017, by rfl⟩ : syracuseStep 320093 = 120035) (by norm_num)
theorem B320117 : Blo 211809 320117 := bbase (se 5 (by rfl) ⟨15005, by rfl⟩ : syracuseStep 320117 = 30011) (by norm_num)
theorem B483965 : Blo 211809 483965 := bbase (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) (by norm_num)
theorem B320141 : Blo 211809 320141 := bbase (se 3 (by rfl) ⟨60026, by rfl⟩ : syracuseStep 320141 = 120053) (by norm_num)
theorem B320165 : Blo 211809 320165 := bbase (se 4 (by rfl) ⟨30015, by rfl⟩ : syracuseStep 320165 = 60031) (by norm_num)
theorem B320189 : Blo 211809 320189 := bbase (se 3 (by rfl) ⟨60035, by rfl⟩ : syracuseStep 320189 = 120071) (by norm_num)
theorem B484037 : Blo 211809 484037 := bbase (se 4 (by rfl) ⟨45378, by rfl⟩ : syracuseStep 484037 = 90757) (by norm_num)
theorem B320213 : Blo 211809 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B320237 : Blo 211809 320237 := bbase (se 3 (by rfl) ⟨60044, by rfl⟩ : syracuseStep 320237 = 120089) (by norm_num)
theorem B320261 : Blo 211809 320261 := bbase (se 4 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 320261 = 60049) (by norm_num)
theorem B484109 : Blo 211809 484109 := bbase (se 3 (by rfl) ⟨90770, by rfl⟩ : syracuseStep 484109 = 181541) (by norm_num)
theorem B320285 : Blo 211809 320285 := bbase (se 3 (by rfl) ⟨60053, by rfl⟩ : syracuseStep 320285 = 120107) (by norm_num)
theorem B320309 : Blo 211809 320309 := bbase (se 5 (by rfl) ⟨15014, by rfl⟩ : syracuseStep 320309 = 30029) (by norm_num)
theorem B320333 : Blo 211809 320333 := bbase (se 3 (by rfl) ⟨60062, by rfl⟩ : syracuseStep 320333 = 120125) (by norm_num)
theorem B484181 : Blo 211809 484181 := bbase (se 9 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 484181 = 2837) (by norm_num)
theorem B615269 : Blo 211809 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B320357 : Blo 211809 320357 := bbase (se 4 (by rfl) ⟨30033, by rfl⟩ : syracuseStep 320357 = 60067) (by norm_num)
theorem B254837 : Blo 211809 254837 := bbase (se 5 (by rfl) ⟨11945, by rfl⟩ : syracuseStep 254837 = 23891) (by norm_num)
theorem B320381 : Blo 211809 320381 := bbase (se 3 (by rfl) ⟨60071, by rfl⟩ : syracuseStep 320381 = 120143) (by norm_num)
theorem B320405 : Blo 211809 320405 := bbase (se 6 (by rfl) ⟨7509, by rfl⟩ : syracuseStep 320405 = 15019) (by norm_num)
theorem B484253 : Blo 211809 484253 := bbase (se 3 (by rfl) ⟨90797, by rfl⟩ : syracuseStep 484253 = 181595) (by norm_num)
theorem B320429 : Blo 211809 320429 := bbase (se 3 (by rfl) ⟨60080, by rfl⟩ : syracuseStep 320429 = 120161) (by norm_num)
theorem B320453 : Blo 211809 320453 := bbase (se 4 (by rfl) ⟨30042, by rfl⟩ : syracuseStep 320453 = 60085) (by norm_num)
theorem B320477 : Blo 211809 320477 := bbase (se 3 (by rfl) ⟨60089, by rfl⟩ : syracuseStep 320477 = 120179) (by norm_num)
theorem B484325 : Blo 211809 484325 := bbase (se 4 (by rfl) ⟨45405, by rfl⟩ : syracuseStep 484325 = 90811) (by norm_num)
theorem B320501 : Blo 211809 320501 := bbase (se 5 (by rfl) ⟨15023, by rfl⟩ : syracuseStep 320501 = 30047) (by norm_num)
theorem B320525 : Blo 211809 320525 := bbase (se 3 (by rfl) ⟨60098, by rfl⟩ : syracuseStep 320525 = 120197) (by norm_num)
theorem B320549 : Blo 211809 320549 := bbase (se 4 (by rfl) ⟨30051, by rfl⟩ : syracuseStep 320549 = 60103) (by norm_num)
theorem B484397 : Blo 211809 484397 := bbase (se 3 (by rfl) ⟨90824, by rfl⟩ : syracuseStep 484397 = 181649) (by norm_num)
theorem B320573 : Blo 211809 320573 := bbase (se 3 (by rfl) ⟨60107, by rfl⟩ : syracuseStep 320573 = 120215) (by norm_num)
theorem B320597 : Blo 211809 320597 := bbase (se 8 (by rfl) ⟨1878, by rfl⟩ : syracuseStep 320597 = 3757) (by norm_num)
theorem B320621 : Blo 211809 320621 := bbase (se 3 (by rfl) ⟨60116, by rfl⟩ : syracuseStep 320621 = 120233) (by norm_num)
theorem B484469 : Blo 211809 484469 := bbase (se 5 (by rfl) ⟨22709, by rfl⟩ : syracuseStep 484469 = 45419) (by norm_num)
theorem B320645 : Blo 211809 320645 := bbase (se 4 (by rfl) ⟨30060, by rfl⟩ : syracuseStep 320645 = 60121) (by norm_num)
theorem B320669 : Blo 211809 320669 := bbase (se 3 (by rfl) ⟨60125, by rfl⟩ : syracuseStep 320669 = 120251) (by norm_num)
theorem B255145 : Blo 211809 255145 := bbase (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) (by norm_num)
theorem B320693 : Blo 211809 320693 := bbase (se 5 (by rfl) ⟨15032, by rfl⟩ : syracuseStep 320693 = 30065) (by norm_num)
theorem B812213 : Blo 211809 812213 := bbase (se 5 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 812213 = 76145) (by norm_num)
theorem B484541 : Blo 211809 484541 := bbase (se 3 (by rfl) ⟨90851, by rfl⟩ : syracuseStep 484541 = 181703) (by norm_num)
theorem B320717 : Blo 211809 320717 := bbase (se 3 (by rfl) ⟨60134, by rfl⟩ : syracuseStep 320717 = 120269) (by norm_num)
theorem B320741 : Blo 211809 320741 := bbase (se 4 (by rfl) ⟨30069, by rfl⟩ : syracuseStep 320741 = 60139) (by norm_num)
theorem B681205 : Blo 211809 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B1729781 : Blo 211809 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B320765 : Blo 211809 320765 := bbase (se 3 (by rfl) ⟨60143, by rfl⟩ : syracuseStep 320765 = 120287) (by norm_num)
theorem B484613 : Blo 211809 484613 := bbase (se 4 (by rfl) ⟨45432, by rfl⟩ : syracuseStep 484613 = 90865) (by norm_num)
theorem B255245 : Blo 211809 255245 := bbase (se 3 (by rfl) ⟨47858, by rfl⟩ : syracuseStep 255245 = 95717) (by norm_num)
theorem B320789 : Blo 211809 320789 := bbase (se 6 (by rfl) ⟨7518, by rfl⟩ : syracuseStep 320789 = 15037) (by norm_num)
theorem B320813 : Blo 211809 320813 := bbase (se 3 (by rfl) ⟨60152, by rfl⟩ : syracuseStep 320813 = 120305) (by norm_num)
theorem B320837 : Blo 211809 320837 := bbase (se 4 (by rfl) ⟨30078, by rfl⟩ : syracuseStep 320837 = 60157) (by norm_num)
theorem B484685 : Blo 211809 484685 := bbase (se 3 (by rfl) ⟨90878, by rfl⟩ : syracuseStep 484685 = 181757) (by norm_num)
theorem B320861 : Blo 211809 320861 := bbase (se 3 (by rfl) ⟨60161, by rfl⟩ : syracuseStep 320861 = 120323) (by norm_num)
theorem B320885 : Blo 211809 320885 := bbase (se 5 (by rfl) ⟨15041, by rfl⟩ : syracuseStep 320885 = 30083) (by norm_num)
theorem B320909 : Blo 211809 320909 := bbase (se 3 (by rfl) ⟨60170, by rfl⟩ : syracuseStep 320909 = 120341) (by norm_num)
theorem B484757 : Blo 211809 484757 := bbase (se 6 (by rfl) ⟨11361, by rfl⟩ : syracuseStep 484757 = 22723) (by norm_num)
theorem B320933 : Blo 211809 320933 := bbase (se 4 (by rfl) ⟨30087, by rfl⟩ : syracuseStep 320933 = 60175) (by norm_num)
theorem B517565 : Blo 211809 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B320957 : Blo 211809 320957 := bbase (se 3 (by rfl) ⟨60179, by rfl⟩ : syracuseStep 320957 = 120359) (by norm_num)
theorem B517573 : Blo 211809 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B320981 : Blo 211809 320981 := bbase (se 7 (by rfl) ⟨3761, by rfl⟩ : syracuseStep 320981 = 7523) (by norm_num)
theorem B812501 : Blo 211809 812501 := bbase (se 7 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 812501 = 19043) (by norm_num)
theorem B484829 : Blo 211809 484829 := bbase (se 3 (by rfl) ⟨90905, by rfl⟩ : syracuseStep 484829 = 181811) (by norm_num)
theorem B321005 : Blo 211809 321005 := bbase (se 3 (by rfl) ⟨60188, by rfl⟩ : syracuseStep 321005 = 120377) (by norm_num)
theorem B321029 : Blo 211809 321029 := bbase (se 4 (by rfl) ⟨30096, by rfl⟩ : syracuseStep 321029 = 60193) (by norm_num)
theorem B321053 : Blo 211809 321053 := bbase (se 3 (by rfl) ⟨60197, by rfl⟩ : syracuseStep 321053 = 120395) (by norm_num)
theorem B484901 : Blo 211809 484901 := bbase (se 4 (by rfl) ⟨45459, by rfl⟩ : syracuseStep 484901 = 90919) (by norm_num)
theorem B321077 : Blo 211809 321077 := bbase (se 5 (by rfl) ⟨15050, by rfl⟩ : syracuseStep 321077 = 30101) (by norm_num)
theorem B321101 : Blo 211809 321101 := bbase (se 3 (by rfl) ⟨60206, by rfl⟩ : syracuseStep 321101 = 120413) (by norm_num)
theorem B321125 : Blo 211809 321125 := bbase (se 4 (by rfl) ⟨30105, by rfl⟩ : syracuseStep 321125 = 60211) (by norm_num)
theorem B484973 : Blo 211809 484973 := bbase (se 3 (by rfl) ⟨90932, by rfl⟩ : syracuseStep 484973 = 181865) (by norm_num)
theorem B321149 : Blo 211809 321149 := bbase (se 3 (by rfl) ⟨60215, by rfl⟩ : syracuseStep 321149 = 120431) (by norm_num)
theorem B321173 : Blo 211809 321173 := bbase (se 6 (by rfl) ⟨7527, by rfl⟩ : syracuseStep 321173 = 15055) (by norm_num)
theorem B255649 : Blo 211809 255649 := bbase (se 2 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 255649 = 191737) (by norm_num)
theorem B321197 : Blo 211809 321197 := bbase (se 3 (by rfl) ⟨60224, by rfl⟩ : syracuseStep 321197 = 120449) (by norm_num)
theorem B1074869 : Blo 211809 1074869 := bbase (se 5 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 1074869 = 100769) (by norm_num)
theorem B485045 : Blo 211809 485045 := bbase (se 5 (by rfl) ⟨22736, by rfl⟩ : syracuseStep 485045 = 45473) (by norm_num)
theorem B321221 : Blo 211809 321221 := bbase (se 4 (by rfl) ⟨30114, by rfl⟩ : syracuseStep 321221 = 60229) (by norm_num)
theorem B321245 : Blo 211809 321245 := bbase (se 3 (by rfl) ⟨60233, by rfl⟩ : syracuseStep 321245 = 120467) (by norm_num)
theorem B517853 : Blo 211809 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B321269 : Blo 211809 321269 := bbase (se 5 (by rfl) ⟨15059, by rfl⟩ : syracuseStep 321269 = 30119) (by norm_num)
theorem B485117 : Blo 211809 485117 := bbase (se 3 (by rfl) ⟨90959, by rfl⟩ : syracuseStep 485117 = 181919) (by norm_num)
theorem B321293 : Blo 211809 321293 := bbase (se 3 (by rfl) ⟨60242, by rfl⟩ : syracuseStep 321293 = 120485) (by norm_num)
theorem B321317 : Blo 211809 321317 := bbase (se 4 (by rfl) ⟨30123, by rfl⟩ : syracuseStep 321317 = 60247) (by norm_num)
theorem B386869 : Blo 211809 386869 := bbase (se 5 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 386869 = 36269) (by norm_num)
theorem B321341 : Blo 211809 321341 := bbase (se 3 (by rfl) ⟨60251, by rfl⟩ : syracuseStep 321341 = 120503) (by norm_num)
theorem B485189 : Blo 211809 485189 := bbase (se 4 (by rfl) ⟨45486, by rfl⟩ : syracuseStep 485189 = 90973) (by norm_num)
theorem B321365 : Blo 211809 321365 := bbase (se 9 (by rfl) ⟨941, by rfl⟩ : syracuseStep 321365 = 1883) (by norm_num)
theorem B321389 : Blo 211809 321389 := bbase (se 3 (by rfl) ⟨60260, by rfl⟩ : syracuseStep 321389 = 120521) (by norm_num)
theorem B321413 : Blo 211809 321413 := bbase (se 4 (by rfl) ⟨30132, by rfl⟩ : syracuseStep 321413 = 60265) (by norm_num)
theorem B485261 : Blo 211809 485261 := bbase (se 3 (by rfl) ⟨90986, by rfl⟩ : syracuseStep 485261 = 181973) (by norm_num)
theorem B321437 : Blo 211809 321437 := bbase (se 3 (by rfl) ⟨60269, by rfl⟩ : syracuseStep 321437 = 120539) (by norm_num)
theorem B321461 : Blo 211809 321461 := bbase (se 5 (by rfl) ⟨15068, by rfl⟩ : syracuseStep 321461 = 30137) (by norm_num)
theorem B321485 : Blo 211809 321485 := bbase (se 3 (by rfl) ⟨60278, by rfl⟩ : syracuseStep 321485 = 120557) (by norm_num)
theorem B485333 : Blo 211809 485333 := bbase (se 7 (by rfl) ⟨5687, by rfl⟩ : syracuseStep 485333 = 11375) (by norm_num)
theorem B321509 : Blo 211809 321509 := bbase (se 4 (by rfl) ⟨30141, by rfl⟩ : syracuseStep 321509 = 60283) (by norm_num)
theorem B321533 : Blo 211809 321533 := bbase (se 3 (by rfl) ⟨60287, by rfl⟩ : syracuseStep 321533 = 120575) (by norm_num)
theorem B3467285 : Blo 211809 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B321557 : Blo 211809 321557 := bbase (se 6 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 321557 = 15073) (by norm_num)
theorem B485405 : Blo 211809 485405 := bbase (se 3 (by rfl) ⟨91013, by rfl⟩ : syracuseStep 485405 = 182027) (by norm_num)
theorem B256033 : Blo 211809 256033 := bbase (se 2 (by rfl) ⟨96012, by rfl⟩ : syracuseStep 256033 = 192025) (by norm_num)
theorem B321581 : Blo 211809 321581 := bbase (se 3 (by rfl) ⟨60296, by rfl⟩ : syracuseStep 321581 = 120593) (by norm_num)
theorem B682037 : Blo 211809 682037 := bbase (se 5 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 682037 = 63941) (by norm_num)
theorem B321605 : Blo 211809 321605 := bbase (se 4 (by rfl) ⟨30150, by rfl⟩ : syracuseStep 321605 = 60301) (by norm_num)
theorem B321629 : Blo 211809 321629 := bbase (se 3 (by rfl) ⟨60305, by rfl⟩ : syracuseStep 321629 = 120611) (by norm_num)
theorem B485477 : Blo 211809 485477 := bbase (se 4 (by rfl) ⟨45513, by rfl⟩ : syracuseStep 485477 = 91027) (by norm_num)
theorem B321653 : Blo 211809 321653 := bbase (se 5 (by rfl) ⟨15077, by rfl⟩ : syracuseStep 321653 = 30155) (by norm_num)
theorem B321677 : Blo 211809 321677 := bbase (se 3 (by rfl) ⟨60314, by rfl⟩ : syracuseStep 321677 = 120629) (by norm_num)
theorem B518285 : Blo 211809 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B321701 : Blo 211809 321701 := bbase (se 4 (by rfl) ⟨30159, by rfl⟩ : syracuseStep 321701 = 60319) (by norm_num)
theorem B485549 : Blo 211809 485549 := bbase (se 3 (by rfl) ⟨91040, by rfl⟩ : syracuseStep 485549 = 182081) (by norm_num)
theorem B321725 : Blo 211809 321725 := bbase (se 3 (by rfl) ⟨60323, by rfl⟩ : syracuseStep 321725 = 120647) (by norm_num)
theorem B321749 : Blo 211809 321749 := bbase (se 7 (by rfl) ⟨3770, by rfl⟩ : syracuseStep 321749 = 7541) (by norm_num)
theorem B321773 : Blo 211809 321773 := bbase (se 3 (by rfl) ⟨60332, by rfl⟩ : syracuseStep 321773 = 120665) (by norm_num)
theorem B715013 : Blo 211809 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B321797 : Blo 211809 321797 := bbase (se 4 (by rfl) ⟨30168, by rfl⟩ : syracuseStep 321797 = 60337) (by norm_num)
theorem B321821 : Blo 211809 321821 := bbase (se 3 (by rfl) ⟨60341, by rfl⟩ : syracuseStep 321821 = 120683) (by norm_num)
theorem B321845 : Blo 211809 321845 := bbase (se 5 (by rfl) ⟨15086, by rfl⟩ : syracuseStep 321845 = 30173) (by norm_num)
theorem B321869 : Blo 211809 321869 := bbase (se 3 (by rfl) ⟨60350, by rfl⟩ : syracuseStep 321869 = 120701) (by norm_num)
theorem B321893 : Blo 211809 321893 := bbase (se 4 (by rfl) ⟨30177, by rfl⟩ : syracuseStep 321893 = 60355) (by norm_num)
theorem B321917 : Blo 211809 321917 := bbase (se 3 (by rfl) ⟨60359, by rfl⟩ : syracuseStep 321917 = 120719) (by norm_num)
theorem B485765 : Blo 211809 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B1206677 : Blo 211809 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B321941 : Blo 211809 321941 := bbase (se 6 (by rfl) ⟨7545, by rfl⟩ : syracuseStep 321941 = 15091) (by norm_num)
theorem B321965 : Blo 211809 321965 := bbase (se 3 (by rfl) ⟨60368, by rfl⟩ : syracuseStep 321965 = 120737) (by norm_num)
theorem B321989 : Blo 211809 321989 := bbase (se 4 (by rfl) ⟨30186, by rfl⟩ : syracuseStep 321989 = 60373) (by norm_num)
theorem B322013 : Blo 211809 322013 := bbase (se 3 (by rfl) ⟨60377, by rfl⟩ : syracuseStep 322013 = 120755) (by norm_num)
theorem B322037 : Blo 211809 322037 := bbase (se 5 (by rfl) ⟨15095, by rfl⟩ : syracuseStep 322037 = 30191) (by norm_num)
theorem B322061 : Blo 211809 322061 := bbase (se 3 (by rfl) ⟨60386, by rfl⟩ : syracuseStep 322061 = 120773) (by norm_num)
theorem B322085 : Blo 211809 322085 := bbase (se 4 (by rfl) ⟨30195, by rfl⟩ : syracuseStep 322085 = 60391) (by norm_num)
theorem B322109 : Blo 211809 322109 := bbase (se 3 (by rfl) ⟨60395, by rfl⟩ : syracuseStep 322109 = 120791) (by norm_num)
theorem B453205 : Blo 211809 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B322133 : Blo 211809 322133 := bbase (se 8 (by rfl) ⟨1887, by rfl⟩ : syracuseStep 322133 = 3775) (by norm_num)
theorem B322157 : Blo 211809 322157 := bbase (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) (by norm_num)
theorem B813685 : Blo 211809 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B322181 : Blo 211809 322181 := bbase (se 4 (by rfl) ⟨30204, by rfl⟩ : syracuseStep 322181 = 60409) (by norm_num)
theorem B322205 : Blo 211809 322205 := bbase (se 3 (by rfl) ⟨60413, by rfl⟩ : syracuseStep 322205 = 120827) (by norm_num)
theorem B715445 : Blo 211809 715445 := bbase (se 5 (by rfl) ⟨33536, by rfl⟩ : syracuseStep 715445 = 67073) (by norm_num)
theorem B322229 : Blo 211809 322229 := bbase (se 5 (by rfl) ⟨15104, by rfl⟩ : syracuseStep 322229 = 30209) (by norm_num)
theorem B322253 : Blo 211809 322253 := bbase (se 3 (by rfl) ⟨60422, by rfl⟩ : syracuseStep 322253 = 120845) (by norm_num)
theorem B322277 : Blo 211809 322277 := bbase (se 4 (by rfl) ⟨30213, by rfl⟩ : syracuseStep 322277 = 60427) (by norm_num)
theorem B322301 : Blo 211809 322301 := bbase (se 3 (by rfl) ⟨60431, by rfl⟩ : syracuseStep 322301 = 120863) (by norm_num)
theorem B322325 : Blo 211809 322325 := bbase (se 6 (by rfl) ⟨7554, by rfl⟩ : syracuseStep 322325 = 15109) (by norm_num)
theorem B322349 : Blo 211809 322349 := bbase (se 3 (by rfl) ⟨60440, by rfl⟩ : syracuseStep 322349 = 120881) (by norm_num)
theorem B322373 : Blo 211809 322373 := bbase (se 4 (by rfl) ⟨30222, by rfl⟩ : syracuseStep 322373 = 60445) (by norm_num)
theorem B322397 : Blo 211809 322397 := bbase (se 3 (by rfl) ⟨60449, by rfl⟩ : syracuseStep 322397 = 120899) (by norm_num)
theorem B322421 : Blo 211809 322421 := bbase (se 5 (by rfl) ⟨15113, by rfl⟩ : syracuseStep 322421 = 30227) (by norm_num)
theorem B256889 : Blo 211809 256889 := bbase (se 2 (by rfl) ⟨96333, by rfl⟩ : syracuseStep 256889 = 192667) (by norm_num)
theorem B387965 : Blo 211809 387965 := bbase (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) (by norm_num)
theorem B322445 : Blo 211809 322445 := bbase (se 3 (by rfl) ⟨60458, by rfl⟩ : syracuseStep 322445 = 120917) (by norm_num)
theorem B813989 : Blo 211809 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B322469 : Blo 211809 322469 := bbase (se 4 (by rfl) ⟨30231, by rfl⟩ : syracuseStep 322469 = 60463) (by norm_num)
theorem B322493 : Blo 211809 322493 := bbase (se 3 (by rfl) ⟨60467, by rfl⟩ : syracuseStep 322493 = 120935) (by norm_num)
theorem B1076165 : Blo 211809 1076165 := bbase (se 4 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 1076165 = 201781) (by norm_num)
theorem B322517 : Blo 211809 322517 := bbase (se 7 (by rfl) ⟨3779, by rfl⟩ : syracuseStep 322517 = 7559) (by norm_num)
theorem B322541 : Blo 211809 322541 := bbase (se 3 (by rfl) ⟨60476, by rfl⟩ : syracuseStep 322541 = 120953) (by norm_num)
theorem B322565 : Blo 211809 322565 := bbase (se 4 (by rfl) ⟨30240, by rfl⟩ : syracuseStep 322565 = 60481) (by norm_num)
theorem B322589 : Blo 211809 322589 := bbase (se 3 (by rfl) ⟨60485, by rfl⟩ : syracuseStep 322589 = 120971) (by norm_num)
theorem B322613 : Blo 211809 322613 := bbase (se 5 (by rfl) ⟨15122, by rfl⟩ : syracuseStep 322613 = 30245) (by norm_num)
theorem B453701 : Blo 211809 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B322637 : Blo 211809 322637 := bbase (se 3 (by rfl) ⟨60494, by rfl⟩ : syracuseStep 322637 = 120989) (by norm_num)
theorem B715877 : Blo 211809 715877 := bbase (se 4 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 715877 = 134227) (by norm_num)
theorem B322661 : Blo 211809 322661 := bbase (se 4 (by rfl) ⟨30249, by rfl⟩ : syracuseStep 322661 = 60499) (by norm_num)
theorem B289909 : Blo 211809 289909 := bbase (se 5 (by rfl) ⟨13589, by rfl⟩ : syracuseStep 289909 = 27179) (by norm_num)
theorem B322685 : Blo 211809 322685 := bbase (se 3 (by rfl) ⟨60503, by rfl⟩ : syracuseStep 322685 = 121007) (by norm_num)
theorem B322709 : Blo 211809 322709 := bbase (se 6 (by rfl) ⟨7563, by rfl⟩ : syracuseStep 322709 = 15127) (by norm_num)
theorem B388253 : Blo 211809 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B257197 : Blo 211809 257197 := bbase (se 3 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 257197 = 96449) (by norm_num)
theorem B322733 : Blo 211809 322733 := bbase (se 3 (by rfl) ⟨60512, by rfl⟩ : syracuseStep 322733 = 121025) (by norm_num)
theorem B322757 : Blo 211809 322757 := bbase (se 4 (by rfl) ⟨30258, by rfl⟩ : syracuseStep 322757 = 60517) (by norm_num)
theorem B322781 : Blo 211809 322781 := bbase (se 3 (by rfl) ⟨60521, by rfl⟩ : syracuseStep 322781 = 121043) (by norm_num)
theorem B322805 : Blo 211809 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B322829 : Blo 211809 322829 := bbase (se 3 (by rfl) ⟨60530, by rfl⟩ : syracuseStep 322829 = 121061) (by norm_num)
theorem B322853 : Blo 211809 322853 := bbase (se 4 (by rfl) ⟨30267, by rfl⟩ : syracuseStep 322853 = 60535) (by norm_num)
theorem B322877 : Blo 211809 322877 := bbase (se 3 (by rfl) ⟨60539, by rfl⟩ : syracuseStep 322877 = 121079) (by norm_num)
theorem B322901 : Blo 211809 322901 := bbase (se 11 (by rfl) ⟨236, by rfl⟩ : syracuseStep 322901 = 473) (by norm_num)
theorem B322925 : Blo 211809 322925 := bbase (se 3 (by rfl) ⟨60548, by rfl⟩ : syracuseStep 322925 = 121097) (by norm_num)
theorem B257413 : Blo 211809 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B322949 : Blo 211809 322949 := bbase (se 4 (by rfl) ⟨30276, by rfl⟩ : syracuseStep 322949 = 60553) (by norm_num)
theorem B322973 : Blo 211809 322973 := bbase (se 3 (by rfl) ⟨60557, by rfl⟩ : syracuseStep 322973 = 121115) (by norm_num)
theorem B322997 : Blo 211809 322997 := bbase (se 5 (by rfl) ⟨15140, by rfl⟩ : syracuseStep 322997 = 30281) (by norm_num)
theorem B945605 : Blo 211809 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B323021 : Blo 211809 323021 := bbase (se 3 (by rfl) ⟨60566, by rfl⟩ : syracuseStep 323021 = 121133) (by norm_num)
theorem B912869 : Blo 211809 912869 := bbase (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) (by norm_num)
theorem B323045 : Blo 211809 323045 := bbase (se 4 (by rfl) ⟨30285, by rfl⟩ : syracuseStep 323045 = 60571) (by norm_num)
theorem B323069 : Blo 211809 323069 := bbase (se 3 (by rfl) ⟨60575, by rfl⟩ : syracuseStep 323069 = 121151) (by norm_num)
theorem B716309 : Blo 211809 716309 := bbase (se 6 (by rfl) ⟨16788, by rfl⟩ : syracuseStep 716309 = 33577) (by norm_num)
theorem B323093 : Blo 211809 323093 := bbase (se 6 (by rfl) ⟨7572, by rfl⟩ : syracuseStep 323093 = 15145) (by norm_num)
theorem B323117 : Blo 211809 323117 := bbase (se 3 (by rfl) ⟨60584, by rfl⟩ : syracuseStep 323117 = 121169) (by norm_num)
theorem B323141 : Blo 211809 323141 := bbase (se 4 (by rfl) ⟨30294, by rfl⟩ : syracuseStep 323141 = 60589) (by norm_num)
theorem B323165 : Blo 211809 323165 := bbase (se 3 (by rfl) ⟨60593, by rfl⟩ : syracuseStep 323165 = 121187) (by norm_num)
theorem B323189 : Blo 211809 323189 := bbase (se 5 (by rfl) ⟨15149, by rfl⟩ : syracuseStep 323189 = 30299) (by norm_num)
theorem B323213 : Blo 211809 323213 := bbase (se 3 (by rfl) ⟨60602, by rfl⟩ : syracuseStep 323213 = 121205) (by norm_num)
theorem B323237 : Blo 211809 323237 := bbase (se 4 (by rfl) ⟨30303, by rfl⟩ : syracuseStep 323237 = 60607) (by norm_num)
theorem B323261 : Blo 211809 323261 := bbase (se 3 (by rfl) ⟨60611, by rfl⟩ : syracuseStep 323261 = 121223) (by norm_num)
theorem B323285 : Blo 211809 323285 := bbase (se 7 (by rfl) ⟨3788, by rfl⟩ : syracuseStep 323285 = 7577) (by norm_num)
theorem B323309 : Blo 211809 323309 := bbase (se 3 (by rfl) ⟨60620, by rfl⟩ : syracuseStep 323309 = 121241) (by norm_num)
theorem B323333 : Blo 211809 323333 := bbase (se 4 (by rfl) ⟨30312, by rfl⟩ : syracuseStep 323333 = 60625) (by norm_num)
theorem B323357 : Blo 211809 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B323381 : Blo 211809 323381 := bbase (se 5 (by rfl) ⟨15158, by rfl⟩ : syracuseStep 323381 = 30317) (by norm_num)
theorem B323405 : Blo 211809 323405 := bbase (se 3 (by rfl) ⟨60638, by rfl⟩ : syracuseStep 323405 = 121277) (by norm_num)
theorem B323429 : Blo 211809 323429 := bbase (se 4 (by rfl) ⟨30321, by rfl⟩ : syracuseStep 323429 = 60643) (by norm_num)
theorem B323453 : Blo 211809 323453 := bbase (se 3 (by rfl) ⟨60647, by rfl⟩ : syracuseStep 323453 = 121295) (by norm_num)
theorem B683909 : Blo 211809 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B323477 : Blo 211809 323477 := bbase (se 6 (by rfl) ⟨7581, by rfl⟩ : syracuseStep 323477 = 15163) (by norm_num)
theorem B323501 : Blo 211809 323501 := bbase (se 3 (by rfl) ⟨60656, by rfl⟩ : syracuseStep 323501 = 121313) (by norm_num)
theorem B454589 : Blo 211809 454589 := bbase (se 3 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 454589 = 170471) (by norm_num)
theorem B716741 : Blo 211809 716741 := bbase (se 4 (by rfl) ⟨67194, by rfl⟩ : syracuseStep 716741 = 134389) (by norm_num)
theorem B323525 : Blo 211809 323525 := bbase (se 4 (by rfl) ⟨30330, by rfl⟩ : syracuseStep 323525 = 60661) (by norm_num)
theorem B3502037 : Blo 211809 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B290773 : Blo 211809 290773 := bbase (se 7 (by rfl) ⟨3407, by rfl⟩ : syracuseStep 290773 = 6815) (by norm_num)
theorem B258013 : Blo 211809 258013 := bbase (se 3 (by rfl) ⟨48377, by rfl⟩ : syracuseStep 258013 = 96755) (by norm_num)
theorem B323549 : Blo 211809 323549 := bbase (se 3 (by rfl) ⟨60665, by rfl⟩ : syracuseStep 323549 = 121331) (by norm_num)
theorem B323573 : Blo 211809 323573 := bbase (se 5 (by rfl) ⟨15167, by rfl⟩ : syracuseStep 323573 = 30335) (by norm_num)
theorem B323597 : Blo 211809 323597 := bbase (se 3 (by rfl) ⟨60674, by rfl⟩ : syracuseStep 323597 = 121349) (by norm_num)
theorem B323621 : Blo 211809 323621 := bbase (se 4 (by rfl) ⟨30339, by rfl⟩ : syracuseStep 323621 = 60679) (by norm_num)
theorem B454709 : Blo 211809 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B323645 : Blo 211809 323645 := bbase (se 3 (by rfl) ⟨60683, by rfl⟩ : syracuseStep 323645 = 121367) (by norm_num)
theorem B2093141 : Blo 211809 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B323669 : Blo 211809 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B323693 : Blo 211809 323693 := bbase (se 3 (by rfl) ⟨60692, by rfl⟩ : syracuseStep 323693 = 121385) (by norm_num)
theorem B1077461 : Blo 211809 1077461 := bbase (se 7 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 1077461 = 25253) (by norm_num)
theorem B717173 : Blo 211809 717173 := bbase (se 5 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 717173 = 67235) (by norm_num)
theorem B455341 : Blo 211809 455341 := bbase (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) (by norm_num)
theorem B291541 : Blo 211809 291541 := bbase (se 7 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 291541 = 6833) (by norm_num)
theorem B717605 : Blo 211809 717605 := bbase (se 4 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 717605 = 134551) (by norm_num)
theorem B5665621 : Blo 211809 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B226201 : Blo 211809 226201 := bbase (se 2 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 226201 = 169651) (by norm_num)
theorem B226261 : Blo 211809 226261 := bbase (se 7 (by rfl) ⟨2651, by rfl⟩ : syracuseStep 226261 = 5303) (by norm_num)
theorem B816101 : Blo 211809 816101 := bbase (se 4 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 816101 = 153019) (by norm_num)
theorem B259157 : Blo 211809 259157 := bbase (se 8 (by rfl) ⟨1518, by rfl⟩ : syracuseStep 259157 = 3037) (by norm_num)
theorem B357493 : Blo 211809 357493 := bbase (se 5 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 357493 = 33515) (by norm_num)
theorem B259205 : Blo 211809 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B357581 : Blo 211809 357581 := bbase (se 3 (by rfl) ⟨67046, by rfl⟩ : syracuseStep 357581 = 134093) (by norm_num)
theorem B718037 : Blo 211809 718037 := bbase (se 7 (by rfl) ⟨8414, by rfl⟩ : syracuseStep 718037 = 16829) (by norm_num)
theorem B914645 : Blo 211809 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B816389 : Blo 211809 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B226577 : Blo 211809 226577 := bbase (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) (by norm_num)
theorem B357709 : Blo 211809 357709 := bbase (se 3 (by rfl) ⟨67070, by rfl⟩ : syracuseStep 357709 = 134141) (by norm_num)
theorem B1373557 : Blo 211809 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B357797 : Blo 211809 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B914885 : Blo 211809 914885 := bbase (se 4 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 914885 = 171541) (by norm_num)
theorem B1078757 : Blo 211809 1078757 := bbase (se 4 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 1078757 = 202267) (by norm_num)
theorem B357925 : Blo 211809 357925 := bbase (se 4 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 357925 = 67111) (by norm_num)
theorem B456229 : Blo 211809 456229 := bbase (se 4 (by rfl) ⟨42771, by rfl⟩ : syracuseStep 456229 = 85543) (by norm_num)
theorem B652853 : Blo 211809 652853 := bbase (se 5 (by rfl) ⟨30602, by rfl⟩ : syracuseStep 652853 = 61205) (by norm_num)
theorem B358013 : Blo 211809 358013 := bbase (se 3 (by rfl) ⟨67127, by rfl⟩ : syracuseStep 358013 = 134255) (by norm_num)
theorem B718469 : Blo 211809 718469 := bbase (se 4 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 718469 = 134713) (by norm_num)
theorem B456349 : Blo 211809 456349 := bbase (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) (by norm_num)
theorem B227021 : Blo 211809 227021 := bbase (se 3 (by rfl) ⟨42566, by rfl⟩ : syracuseStep 227021 = 85133) (by norm_num)
theorem B358141 : Blo 211809 358141 := bbase (se 3 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 358141 = 134303) (by norm_num)
theorem B227081 : Blo 211809 227081 := bbase (se 2 (by rfl) ⟨85155, by rfl⟩ : syracuseStep 227081 = 170311) (by norm_num)
theorem B358229 : Blo 211809 358229 := bbase (se 9 (by rfl) ⟨1049, by rfl⟩ : syracuseStep 358229 = 2099) (by norm_num)
theorem B227209 : Blo 211809 227209 := bbase (se 2 (by rfl) ⟨85203, by rfl⟩ : syracuseStep 227209 = 170407) (by norm_num)
theorem B456605 : Blo 211809 456605 := bbase (se 3 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 456605 = 171227) (by norm_num)
theorem B358357 : Blo 211809 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B358445 : Blo 211809 358445 := bbase (se 3 (by rfl) ⟨67208, by rfl⟩ : syracuseStep 358445 = 134417) (by norm_num)
theorem B718901 : Blo 211809 718901 := bbase (se 5 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 718901 = 67397) (by norm_num)
theorem B358573 : Blo 211809 358573 := bbase (se 3 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 358573 = 134465) (by norm_num)
theorem B358661 : Blo 211809 358661 := bbase (se 4 (by rfl) ⟨33624, by rfl⟩ : syracuseStep 358661 = 67249) (by norm_num)
theorem B227653 : Blo 211809 227653 := bbase (se 4 (by rfl) ⟨21342, by rfl⟩ : syracuseStep 227653 = 42685) (by norm_num)
theorem B358789 : Blo 211809 358789 := bbase (se 4 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 358789 = 67273) (by norm_num)
theorem B817573 : Blo 211809 817573 := bbase (se 4 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 817573 = 153295) (by norm_num)
theorem B227773 : Blo 211809 227773 := bbase (se 3 (by rfl) ⟨42707, by rfl⟩ : syracuseStep 227773 = 85415) (by norm_num)
theorem B358877 : Blo 211809 358877 := bbase (se 3 (by rfl) ⟨67289, by rfl⟩ : syracuseStep 358877 = 134579) (by norm_num)
theorem B719333 : Blo 211809 719333 := bbase (se 4 (by rfl) ⟨67437, by rfl⟩ : syracuseStep 719333 = 134875) (by norm_num)
theorem B260653 : Blo 211809 260653 := bbase (se 3 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 260653 = 97745) (by norm_num)
theorem B686677 : Blo 211809 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B359005 : Blo 211809 359005 := bbase (se 3 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 359005 = 134627) (by norm_num)
theorem B359093 : Blo 211809 359093 := bbase (se 5 (by rfl) ⟨16832, by rfl⟩ : syracuseStep 359093 = 33665) (by norm_num)
theorem B228025 : Blo 211809 228025 := bbase (se 2 (by rfl) ⟨85509, by rfl⟩ : syracuseStep 228025 = 171019) (by norm_num)
theorem B228029 : Blo 211809 228029 := bbase (se 3 (by rfl) ⟨42755, by rfl⟩ : syracuseStep 228029 = 85511) (by norm_num)
theorem B817877 : Blo 211809 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B1080053 : Blo 211809 1080053 := bbase (se 5 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 1080053 = 101255) (by norm_num)
theorem B457493 : Blo 211809 457493 := bbase (se 6 (by rfl) ⟨10722, by rfl⟩ : syracuseStep 457493 = 21445) (by norm_num)
theorem B1178389 : Blo 211809 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B359221 : Blo 211809 359221 := bbase (se 5 (by rfl) ⟨16838, by rfl⟩ : syracuseStep 359221 = 33677) (by norm_num)
theorem B359309 : Blo 211809 359309 := bbase (se 3 (by rfl) ⟨67370, by rfl⟩ : syracuseStep 359309 = 134741) (by norm_num)
theorem B719765 : Blo 211809 719765 := bbase (se 6 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 719765 = 33739) (by norm_num)
theorem B1637333 : Blo 211809 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B457733 : Blo 211809 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B359437 : Blo 211809 359437 := bbase (se 3 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 359437 = 134789) (by norm_num)
theorem B818261 : Blo 211809 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B359525 : Blo 211809 359525 := bbase (se 4 (by rfl) ⟨33705, by rfl⟩ : syracuseStep 359525 = 67411) (by norm_num)
theorem B359653 : Blo 211809 359653 := bbase (se 4 (by rfl) ⟨33717, by rfl⟩ : syracuseStep 359653 = 67435) (by norm_num)
theorem B228593 : Blo 211809 228593 := bbase (se 2 (by rfl) ⟨85722, by rfl⟩ : syracuseStep 228593 = 171445) (by norm_num)
theorem B261397 : Blo 211809 261397 := bbase (se 6 (by rfl) ⟨6126, by rfl⟩ : syracuseStep 261397 = 12253) (by norm_num)
theorem B392501 : Blo 211809 392501 := bbase (se 5 (by rfl) ⟨18398, by rfl⟩ : syracuseStep 392501 = 36797) (by norm_num)
theorem B359741 : Blo 211809 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B720197 : Blo 211809 720197 := bbase (se 4 (by rfl) ⟨67518, by rfl⟩ : syracuseStep 720197 = 135037) (by norm_num)
theorem B228781 : Blo 211809 228781 := bbase (se 3 (by rfl) ⟨42896, by rfl⟩ : syracuseStep 228781 = 85793) (by norm_num)
theorem B359869 : Blo 211809 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B458237 : Blo 211809 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B458245 : Blo 211809 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B359957 : Blo 211809 359957 := bbase (se 6 (by rfl) ⟨8436, by rfl⟩ : syracuseStep 359957 = 16873) (by norm_num)
theorem B1375829 : Blo 211809 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B360085 : Blo 211809 360085 := bbase (se 6 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 360085 = 16879) (by norm_num)
theorem B917173 : Blo 211809 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B360173 : Blo 211809 360173 := bbase (se 3 (by rfl) ⟨67532, by rfl⟩ : syracuseStep 360173 = 135065) (by norm_num)
theorem B720629 : Blo 211809 720629 := bbase (se 5 (by rfl) ⟨33779, by rfl⟩ : syracuseStep 720629 = 67559) (by norm_num)
theorem B786181 : Blo 211809 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B360301 : Blo 211809 360301 := bbase (se 3 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 360301 = 135113) (by norm_num)
theorem B556949 : Blo 211809 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B655285 : Blo 211809 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B360389 : Blo 211809 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B720899 : Blo 211809 720899 := bstep (se 1 (by rfl) ⟨540674, by rfl⟩ : syracuseStep 720899 = 1081349) B1081349
theorem B360497 : Blo 211809 360497 := bstep (se 2 (by rfl) ⟨135186, by rfl⟩ : syracuseStep 360497 = 270373) B270373
theorem B360625 : Blo 211809 360625 := bstep (se 2 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 360625 = 270469) B270469
theorem B360659 : Blo 211809 360659 := bstep (se 1 (by rfl) ⟨270494, by rfl⟩ : syracuseStep 360659 = 540989) B540989
theorem B721169 : Blo 211809 721169 := bstep (se 2 (by rfl) ⟨270438, by rfl⟩ : syracuseStep 721169 = 540877) B540877
theorem B360787 : Blo 211809 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B328033 : Blo 211809 328033 := bstep (se 2 (by rfl) ⟨123012, by rfl⟩ : syracuseStep 328033 = 246025) B246025
theorem B360929 : Blo 211809 360929 := bstep (se 2 (by rfl) ⟨135348, by rfl⟩ : syracuseStep 360929 = 270697) B270697
theorem B688625 : Blo 211809 688625 := bstep (se 2 (by rfl) ⟨258234, by rfl⟩ : syracuseStep 688625 = 516469) B516469
theorem B361057 : Blo 211809 361057 := bstep (se 2 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 361057 = 270793) B270793
theorem B361091 : Blo 211809 361091 := bstep (se 1 (by rfl) ⟨270818, by rfl⟩ : syracuseStep 361091 = 541637) B541637
theorem B1081997 : Blo 211809 1081997 := bstep (se 3 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 1081997 = 405749) B405749
theorem B230131 : Blo 211809 230131 := bstep (se 1 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 230131 = 345197) B345197
theorem B361219 : Blo 211809 361219 := bstep (se 1 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 361219 = 541829) B541829
theorem B721709 : Blo 211809 721709 := bstep (se 3 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 721709 = 270641) B270641
theorem B721763 : Blo 211809 721763 := bstep (se 1 (by rfl) ⟨541322, by rfl⟩ : syracuseStep 721763 = 1082645) B1082645
theorem B361361 : Blo 211809 361361 := bstep (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) B271021
theorem B459715 : Blo 211809 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B1573829 : Blo 211809 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B1868771 : Blo 211809 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B361489 : Blo 211809 361489 := bstep (se 2 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 361489 = 271117) B271117
theorem B361523 : Blo 211809 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B459857 : Blo 211809 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B230483 : Blo 211809 230483 := bstep (se 1 (by rfl) ⟨172862, by rfl⟩ : syracuseStep 230483 = 345725) B345725
theorem B722033 : Blo 211809 722033 := bstep (se 2 (by rfl) ⟨270762, by rfl⟩ : syracuseStep 722033 = 541525) B541525
theorem B689315 : Blo 211809 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B1246385 : Blo 211809 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B361651 : Blo 211809 361651 := bstep (se 1 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 361651 = 542477) B542477
theorem B361793 : Blo 211809 361793 := bstep (se 2 (by rfl) ⟨135672, by rfl⟩ : syracuseStep 361793 = 271345) B271345
theorem B361921 : Blo 211809 361921 := bstep (se 2 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 361921 = 271441) B271441
theorem B361955 : Blo 211809 361955 := bstep (se 1 (by rfl) ⟨271466, by rfl⟩ : syracuseStep 361955 = 542933) B542933
theorem B362083 : Blo 211809 362083 := bstep (se 1 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 362083 = 543125) B543125
theorem B722573 : Blo 211809 722573 := bstep (se 3 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 722573 = 270965) B270965
theorem B722627 : Blo 211809 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B1214149 : Blo 211809 1214149 := bstep (se 4 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 1214149 = 227653) B227653
theorem B362225 : Blo 211809 362225 := bstep (se 2 (by rfl) ⟨135834, by rfl⟩ : syracuseStep 362225 = 271669) B271669
theorem B460561 : Blo 211809 460561 := bstep (se 2 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 460561 = 345421) B345421
theorem B362353 : Blo 211809 362353 := bstep (se 2 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 362353 = 271765) B271765
theorem B362387 : Blo 211809 362387 := bstep (se 1 (by rfl) ⟨271790, by rfl⟩ : syracuseStep 362387 = 543581) B543581
theorem B690097 : Blo 211809 690097 := bstep (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) B517573
theorem B722897 : Blo 211809 722897 := bstep (se 2 (by rfl) ⟨271086, by rfl⟩ : syracuseStep 722897 = 542173) B542173
theorem B362515 : Blo 211809 362515 := bstep (se 1 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 362515 = 543773) B543773
theorem B1378403 : Blo 211809 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B362627 : Blo 211809 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B362657 : Blo 211809 362657 := bstep (se 2 (by rfl) ⟨135996, by rfl⟩ : syracuseStep 362657 = 271993) B271993
theorem B362785 : Blo 211809 362785 := bstep (se 2 (by rfl) ⟨136044, by rfl⟩ : syracuseStep 362785 = 272089) B272089
theorem B362819 : Blo 211809 362819 := bstep (se 1 (by rfl) ⟨272114, by rfl⟩ : syracuseStep 362819 = 544229) B544229
theorem B919907 : Blo 211809 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B362947 : Blo 211809 362947 := bstep (se 1 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 362947 = 544421) B544421
theorem B723437 : Blo 211809 723437 := bstep (se 3 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 723437 = 271289) B271289
theorem B723491 : Blo 211809 723491 := bstep (se 1 (by rfl) ⟨542618, by rfl⟩ : syracuseStep 723491 = 1085237) B1085237
theorem B363089 : Blo 211809 363089 := bstep (se 2 (by rfl) ⟨136158, by rfl⟩ : syracuseStep 363089 = 272317) B272317
theorem B363217 : Blo 211809 363217 := bstep (se 2 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 363217 = 272413) B272413
theorem B363251 : Blo 211809 363251 := bstep (se 1 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 363251 = 544877) B544877
theorem B723761 : Blo 211809 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B1641329 : Blo 211809 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B363379 : Blo 211809 363379 := bstep (se 1 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 363379 = 545069) B545069
theorem B691085 : Blo 211809 691085 := bstep (se 3 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 691085 = 259157) B259157
theorem B363521 : Blo 211809 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B691213 : Blo 211809 691213 := bstep (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) B259205
theorem B363649 : Blo 211809 363649 := bstep (se 2 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 363649 = 272737) B272737
theorem B363683 : Blo 211809 363683 := bstep (se 1 (by rfl) ⟨272762, by rfl⟩ : syracuseStep 363683 = 545525) B545525
theorem B265459 : Blo 211809 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B363809 : Blo 211809 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B363811 : Blo 211809 363811 := bstep (se 1 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 363811 = 545717) B545717
theorem B724301 : Blo 211809 724301 := bstep (se 3 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 724301 = 271613) B271613
theorem B724355 : Blo 211809 724355 := bstep (se 1 (by rfl) ⟨543266, by rfl⟩ : syracuseStep 724355 = 1086533) B1086533
theorem B363953 : Blo 211809 363953 := bstep (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) B272965
theorem B1084913 : Blo 211809 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B1019405 : Blo 211809 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B364081 : Blo 211809 364081 := bstep (se 2 (by rfl) ⟨136530, by rfl⟩ : syracuseStep 364081 = 273061) B273061
theorem B364115 : Blo 211809 364115 := bstep (se 1 (by rfl) ⟨273086, by rfl⟩ : syracuseStep 364115 = 546173) B546173
theorem B1216133 : Blo 211809 1216133 := bstep (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) B228025
theorem B724625 : Blo 211809 724625 := bstep (se 2 (by rfl) ⟨271734, by rfl⟩ : syracuseStep 724625 = 543469) B543469
theorem B331793 : Blo 211809 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B2429027 : Blo 211809 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B725165 : Blo 211809 725165 := bstep (se 3 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 725165 = 271937) B271937
theorem B725219 : Blo 211809 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B856433 : Blo 211809 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B725489 : Blo 211809 725489 := bstep (se 2 (by rfl) ⟨272058, by rfl⟩ : syracuseStep 725489 = 544117) B544117
theorem B1086371 : Blo 211809 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B726029 : Blo 211809 726029 := bstep (se 3 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 726029 = 272261) B272261
theorem B726083 : Blo 211809 726083 := bstep (se 1 (by rfl) ⟨544562, by rfl⟩ : syracuseStep 726083 = 1089125) B1089125
theorem B1152305 : Blo 211809 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B726353 : Blo 211809 726353 := bstep (se 2 (by rfl) ⟨272382, by rfl⟩ : syracuseStep 726353 = 544765) B544765
theorem B2069873 : Blo 211809 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B365971 : Blo 211809 365971 := bstep (se 1 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 365971 = 548957) B548957
theorem B661069 : Blo 211809 661069 := bstep (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) B247901
theorem B1087181 : Blo 211809 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B1382093 : Blo 211809 1382093 := bstep (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) B518285
theorem B726893 : Blo 211809 726893 := bstep (se 3 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 726893 = 272585) B272585
theorem B726947 : Blo 211809 726947 := bstep (se 1 (by rfl) ⟨545210, by rfl⟩ : syracuseStep 726947 = 1090421) B1090421
theorem B1382321 : Blo 211809 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B268211 : Blo 211809 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B1153187 : Blo 211809 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B727217 : Blo 211809 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B301601 : Blo 211809 301601 := bstep (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) B226201
theorem B301681 : Blo 211809 301681 := bstep (se 2 (by rfl) ⟨113130, by rfl⟩ : syracuseStep 301681 = 226261) B226261
theorem B268915 : Blo 211809 268915 := bstep (se 1 (by rfl) ⟨201686, by rfl⟩ : syracuseStep 268915 = 403373) B403373
theorem B727757 : Blo 211809 727757 := bstep (se 3 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 727757 = 272909) B272909
theorem B269011 : Blo 211809 269011 := bstep (se 1 (by rfl) ⟨201758, by rfl⟩ : syracuseStep 269011 = 403517) B403517
theorem B727811 : Blo 211809 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B989965 : Blo 211809 989965 := bstep (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) B371237
theorem B5315381 : Blo 211809 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B2235235 : Blo 211809 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B728081 : Blo 211809 728081 := bstep (se 2 (by rfl) ⟨273030, by rfl⟩ : syracuseStep 728081 = 546061) B546061
theorem B269507 : Blo 211809 269507 := bstep (se 1 (by rfl) ⟨202130, by rfl⟩ : syracuseStep 269507 = 404261) B404261
theorem B302467 : Blo 211809 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B1219981 : Blo 211809 1219981 := bstep (se 3 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 1219981 = 457493) B457493
theorem B1089293 : Blo 211809 1089293 := bstep (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) B408485
theorem B302945 : Blo 211809 302945 := bstep (se 2 (by rfl) ⟨113604, by rfl⟩ : syracuseStep 302945 = 227209) B227209
theorem B2039651 : Blo 211809 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810289 : Blo 211809 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B270211 : Blo 211809 270211 := bstep (se 1 (by rfl) ⟨202658, by rfl⟩ : syracuseStep 270211 = 405317) B405317
theorem B303059 : Blo 211809 303059 := bstep (se 1 (by rfl) ⟨227294, by rfl⟩ : syracuseStep 303059 = 454589) B454589
theorem B2334691 : Blo 211809 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B270307 : Blo 211809 270307 := bstep (se 1 (by rfl) ⟨202730, by rfl⟩ : syracuseStep 270307 = 405461) B405461
theorem B303139 : Blo 211809 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B729233 : Blo 211809 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B729425 : Blo 211809 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B270803 : Blo 211809 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B1090097 : Blo 211809 1090097 := bstep (se 2 (by rfl) ⟨408786, by rfl⟩ : syracuseStep 1090097 = 817573) B817573
theorem B303697 : Blo 211809 303697 := bstep (se 2 (by rfl) ⟨113886, by rfl⟩ : syracuseStep 303697 = 227773) B227773
theorem B238387 : Blo 211809 238387 := bstep (se 1 (by rfl) ⟨178790, by rfl⟩ : syracuseStep 238387 = 357581) B357581
theorem B238531 : Blo 211809 238531 := bstep (se 1 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 238531 = 357797) B357797
theorem B435235 : Blo 211809 435235 := bstep (se 1 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 435235 = 652853) B652853
theorem B402499 : Blo 211809 402499 := bstep (se 1 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 402499 = 603749) B603749
theorem B238675 : Blo 211809 238675 := bstep (se 1 (by rfl) ⟨179006, by rfl⟩ : syracuseStep 238675 = 358013) B358013
theorem B402545 : Blo 211809 402545 := bstep (se 2 (by rfl) ⟨150954, by rfl⟩ : syracuseStep 402545 = 301909) B301909
theorem B271507 : Blo 211809 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B1156301 : Blo 211809 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B238819 : Blo 211809 238819 := bstep (se 1 (by rfl) ⟨179114, by rfl⟩ : syracuseStep 238819 = 358229) B358229
theorem B271603 : Blo 211809 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B2073869 : Blo 211809 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B304403 : Blo 211809 304403 := bstep (se 1 (by rfl) ⟨228302, by rfl⟩ : syracuseStep 304403 = 456605) B456605
theorem B1221965 : Blo 211809 1221965 := bstep (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) B458237
theorem B238963 : Blo 211809 238963 := bstep (se 1 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 238963 = 358445) B358445
theorem B402833 : Blo 211809 402833 := bstep (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) B302125
theorem B239107 : Blo 211809 239107 := bstep (se 1 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 239107 = 358661) B358661
theorem B370273 : Blo 211809 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B239251 : Blo 211809 239251 := bstep (se 1 (by rfl) ⟨179438, by rfl⟩ : syracuseStep 239251 = 358877) B358877
theorem B2827973 : Blo 211809 2827973 := bstep (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) B530245
theorem B272099 : Blo 211809 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B239395 : Blo 211809 239395 := bstep (se 1 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 239395 = 359093) B359093
theorem B305041 : Blo 211809 305041 := bstep (se 2 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 305041 = 228781) B228781
theorem B239539 : Blo 211809 239539 := bstep (se 1 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 239539 = 359309) B359309
theorem B1091555 : Blo 211809 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B305155 : Blo 211809 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B239683 : Blo 211809 239683 := bstep (se 1 (by rfl) ⟨179762, by rfl⟩ : syracuseStep 239683 = 359525) B359525
theorem B403555 : Blo 211809 403555 := bstep (se 1 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 403555 = 605333) B605333
theorem B239827 : Blo 211809 239827 := bstep (se 1 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 239827 = 359741) B359741
theorem B1222897 : Blo 211809 1222897 := bstep (se 2 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 1222897 = 917173) B917173
theorem B1059149 : Blo 211809 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B239971 : Blo 211809 239971 := bstep (se 1 (by rfl) ⟨179978, by rfl⟩ : syracuseStep 239971 = 359957) B359957
theorem B272803 : Blo 211809 272803 := bstep (se 1 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 272803 = 409205) B409205
theorem B1550789 : Blo 211809 1550789 := bstep (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) B290773
theorem B862669 : Blo 211809 862669 := bstep (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) B323501
theorem B240115 : Blo 211809 240115 := bstep (se 1 (by rfl) ⟨180086, by rfl⟩ : syracuseStep 240115 = 360173) B360173
theorem B272899 : Blo 211809 272899 := bstep (se 1 (by rfl) ⟨204674, by rfl⟩ : syracuseStep 272899 = 409349) B409349
theorem B404003 : Blo 211809 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B371299 : Blo 211809 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B240259 : Blo 211809 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B404227 : Blo 211809 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B1092365 : Blo 211809 1092365 := bstep (se 3 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 1092365 = 409637) B409637
theorem B240403 : Blo 211809 240403 := bstep (se 1 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 240403 = 360605) B360605
theorem B371491 : Blo 211809 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B404291 : Blo 211809 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B863075 : Blo 211809 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B240547 : Blo 211809 240547 := bstep (se 1 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 240547 = 360821) B360821
theorem B240691 : Blo 211809 240691 := bstep (se 1 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 240691 = 361037) B361037
theorem B240835 : Blo 211809 240835 := bstep (se 1 (by rfl) ⟨180626, by rfl⟩ : syracuseStep 240835 = 361253) B361253
theorem B306499 : Blo 211809 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B240979 : Blo 211809 240979 := bstep (se 1 (by rfl) ⟨180734, by rfl⟩ : syracuseStep 240979 = 361469) B361469
theorem B241123 : Blo 211809 241123 := bstep (se 1 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 241123 = 361685) B361685
theorem B241267 : Blo 211809 241267 := bstep (se 1 (by rfl) ⟨180950, by rfl⟩ : syracuseStep 241267 = 361901) B361901
theorem B274067 : Blo 211809 274067 := bstep (se 1 (by rfl) ⟨205550, by rfl⟩ : syracuseStep 274067 = 411101) B411101
theorem B1224355 : Blo 211809 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B339635 : Blo 211809 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B831181 : Blo 211809 831181 := bstep (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) B311693
theorem B536291 : Blo 211809 536291 := bstep (se 1 (by rfl) ⟨402218, by rfl⟩ : syracuseStep 536291 = 804437) B804437
theorem B405233 : Blo 211809 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B241411 : Blo 211809 241411 := bstep (se 1 (by rfl) ⟨181058, by rfl⟩ : syracuseStep 241411 = 362117) B362117
theorem B241555 : Blo 211809 241555 := bstep (se 1 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 241555 = 362333) B362333
theorem B536483 : Blo 211809 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B6074309 : Blo 211809 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B733133 : Blo 211809 733133 := bstep (se 3 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 733133 = 274925) B274925
theorem B241699 : Blo 211809 241699 := bstep (se 1 (by rfl) ⟨181274, by rfl⟩ : syracuseStep 241699 = 362549) B362549
theorem B241715 : Blo 211809 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B1224881 : Blo 211809 1224881 := bstep (se 2 (by rfl) ⟨459330, by rfl⟩ : syracuseStep 1224881 = 918661) B918661
theorem B340147 : Blo 211809 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B241843 : Blo 211809 241843 := bstep (se 1 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 241843 = 362765) B362765
theorem B340193 : Blo 211809 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B733475 : Blo 211809 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B241987 : Blo 211809 241987 := bstep (se 1 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 241987 = 362981) B362981
theorem B242131 : Blo 211809 242131 := bstep (se 1 (by rfl) ⟨181598, by rfl⟩ : syracuseStep 242131 = 363197) B363197
theorem B242275 : Blo 211809 242275 := bstep (se 1 (by rfl) ⟨181706, by rfl⟩ : syracuseStep 242275 = 363413) B363413
theorem B733805 : Blo 211809 733805 := bstep (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) B275177
theorem B406129 : Blo 211809 406129 := bstep (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) B304597
theorem B242419 : Blo 211809 242419 := bstep (se 1 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 242419 = 363629) B363629
theorem B406289 : Blo 211809 406289 := bstep (se 2 (by rfl) ⟨152358, by rfl⟩ : syracuseStep 406289 = 304717) B304717
theorem B537425 : Blo 211809 537425 := bstep (se 2 (by rfl) ⟨201534, by rfl⟩ : syracuseStep 537425 = 403069) B403069
theorem B340865 : Blo 211809 340865 := bstep (se 2 (by rfl) ⟨127824, by rfl⟩ : syracuseStep 340865 = 255649) B255649
theorem B537475 : Blo 211809 537475 := bstep (se 1 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 537475 = 806213) B806213
theorem B242563 : Blo 211809 242563 := bstep (se 1 (by rfl) ⟨181922, by rfl⟩ : syracuseStep 242563 = 363845) B363845
theorem B3093389 : Blo 211809 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B537617 : Blo 211809 537617 := bstep (se 2 (by rfl) ⟨201606, by rfl⟩ : syracuseStep 537617 = 403213) B403213
theorem B242707 : Blo 211809 242707 := bstep (se 1 (by rfl) ⟨182030, by rfl⟩ : syracuseStep 242707 = 364061) B364061
theorem B406691 : Blo 211809 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B341377 : Blo 211809 341377 := bstep (se 2 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 341377 = 256033) B256033
theorem B1848845 : Blo 211809 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B1029667 : Blo 211809 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B1226339 : Blo 211809 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B603875 : Blo 211809 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B767971 : Blo 211809 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B538609 : Blo 211809 538609 := bstep (se 2 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 538609 = 403957) B403957
theorem B407587 : Blo 211809 407587 := bstep (se 1 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 407587 = 611381) B611381
theorem B604205 : Blo 211809 604205 := bstep (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) B226577
theorem B604273 : Blo 211809 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B2308277 : Blo 211809 2308277 := bstep (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) B216401
theorem B407747 : Blo 211809 407747 := bstep (se 1 (by rfl) ⟨305810, by rfl⟩ : syracuseStep 407747 = 611621) B611621
theorem B735437 : Blo 211809 735437 := bstep (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) B275789
theorem B538883 : Blo 211809 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B1620323 : Blo 211809 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B604547 : Blo 211809 604547 := bstep (se 1 (by rfl) ⟨453410, by rfl⟩ : syracuseStep 604547 = 906821) B906821
theorem B539075 : Blo 211809 539075 := bstep (se 1 (by rfl) ⟨404306, by rfl⟩ : syracuseStep 539075 = 808613) B808613
theorem B1161733 : Blo 211809 1161733 := bstep (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) B217825
theorem B703085 : Blo 211809 703085 := bstep (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) B263657
theorem B342659 : Blo 211809 342659 := bstep (se 1 (by rfl) ⟨256994, by rfl⟩ : syracuseStep 342659 = 513989) B513989
theorem B309955 : Blo 211809 309955 := bstep (se 1 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 309955 = 464933) B464933
theorem B1030897 : Blo 211809 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B342787 : Blo 211809 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B211811 : Blo 211809 211811 := bstep (se 1 (by rfl) ⟨158858, by rfl⟩ : syracuseStep 211811 = 317717) B317717
theorem B211827 : Blo 211809 211827 := bstep (se 1 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 211827 = 317741) B317741
theorem B211843 : Blo 211809 211843 := bstep (se 1 (by rfl) ⟨158882, by rfl⟩ : syracuseStep 211843 = 317765) B317765
theorem B342929 : Blo 211809 342929 := bstep (se 2 (by rfl) ⟨128598, by rfl⟩ : syracuseStep 342929 = 257197) B257197
theorem B211859 : Blo 211809 211859 := bstep (se 1 (by rfl) ⟨158894, by rfl⟩ : syracuseStep 211859 = 317789) B317789
theorem B211875 : Blo 211809 211875 := bstep (se 1 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 211875 = 317813) B317813
theorem B211891 : Blo 211809 211891 := bstep (se 1 (by rfl) ⟨158918, by rfl⟩ : syracuseStep 211891 = 317837) B317837
theorem B211907 : Blo 211809 211907 := bstep (se 1 (by rfl) ⟨158930, by rfl⟩ : syracuseStep 211907 = 317861) B317861
theorem B211923 : Blo 211809 211923 := bstep (se 1 (by rfl) ⟨158942, by rfl⟩ : syracuseStep 211923 = 317885) B317885
theorem B211939 : Blo 211809 211939 := bstep (se 1 (by rfl) ⟨158954, by rfl⟩ : syracuseStep 211939 = 317909) B317909
theorem B211955 : Blo 211809 211955 := bstep (se 1 (by rfl) ⟨158966, by rfl⟩ : syracuseStep 211955 = 317933) B317933
theorem B211971 : Blo 211809 211971 := bstep (se 1 (by rfl) ⟨158978, by rfl⟩ : syracuseStep 211971 = 317957) B317957
theorem B2735117 : Blo 211809 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B211987 : Blo 211809 211987 := bstep (se 1 (by rfl) ⟨158990, by rfl⟩ : syracuseStep 211987 = 317981) B317981
theorem B212003 : Blo 211809 212003 := bstep (se 1 (by rfl) ⟨159002, by rfl⟩ : syracuseStep 212003 = 318005) B318005
theorem B212019 : Blo 211809 212019 := bstep (se 1 (by rfl) ⟨159014, by rfl⟩ : syracuseStep 212019 = 318029) B318029
theorem B212035 : Blo 211809 212035 := bstep (se 1 (by rfl) ⟨159026, by rfl⟩ : syracuseStep 212035 = 318053) B318053
theorem B212051 : Blo 211809 212051 := bstep (se 1 (by rfl) ⟨159038, by rfl⟩ : syracuseStep 212051 = 318077) B318077
theorem B212067 : Blo 211809 212067 := bstep (se 1 (by rfl) ⟨159050, by rfl⟩ : syracuseStep 212067 = 318101) B318101
theorem B1358947 : Blo 211809 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B212083 : Blo 211809 212083 := bstep (se 1 (by rfl) ⟨159062, by rfl⟩ : syracuseStep 212083 = 318125) B318125
theorem B212099 : Blo 211809 212099 := bstep (se 1 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 212099 = 318149) B318149
theorem B212115 : Blo 211809 212115 := bstep (se 1 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 212115 = 318173) B318173
theorem B212131 : Blo 211809 212131 := bstep (se 1 (by rfl) ⟨159098, by rfl⟩ : syracuseStep 212131 = 318197) B318197
theorem B343217 : Blo 211809 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B212147 : Blo 211809 212147 := bstep (se 1 (by rfl) ⟨159110, by rfl⟩ : syracuseStep 212147 = 318221) B318221
theorem B212163 : Blo 211809 212163 := bstep (se 1 (by rfl) ⟨159122, by rfl⟩ : syracuseStep 212163 = 318245) B318245
theorem B605389 : Blo 211809 605389 := bstep (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) B227021
theorem B212179 : Blo 211809 212179 := bstep (se 1 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 212179 = 318269) B318269
theorem B212195 : Blo 211809 212195 := bstep (se 1 (by rfl) ⟨159146, by rfl⟩ : syracuseStep 212195 = 318293) B318293
theorem B408817 : Blo 211809 408817 := bstep (se 2 (by rfl) ⟨153306, by rfl⟩ : syracuseStep 408817 = 306613) B306613
theorem B212211 : Blo 211809 212211 := bstep (se 1 (by rfl) ⟨159158, by rfl⟩ : syracuseStep 212211 = 318317) B318317
theorem B212227 : Blo 211809 212227 := bstep (se 1 (by rfl) ⟨159170, by rfl⟩ : syracuseStep 212227 = 318341) B318341
theorem B212243 : Blo 211809 212243 := bstep (se 1 (by rfl) ⟨159182, by rfl⟩ : syracuseStep 212243 = 318365) B318365
theorem B212259 : Blo 211809 212259 := bstep (se 1 (by rfl) ⟨159194, by rfl⟩ : syracuseStep 212259 = 318389) B318389
theorem B212275 : Blo 211809 212275 := bstep (se 1 (by rfl) ⟨159206, by rfl⟩ : syracuseStep 212275 = 318413) B318413
theorem B212291 : Blo 211809 212291 := bstep (se 1 (by rfl) ⟨159218, by rfl⟩ : syracuseStep 212291 = 318437) B318437
theorem B212307 : Blo 211809 212307 := bstep (se 1 (by rfl) ⟨159230, by rfl⟩ : syracuseStep 212307 = 318461) B318461
theorem B245075 : Blo 211809 245075 := bstep (se 1 (by rfl) ⟨183806, by rfl⟩ : syracuseStep 245075 = 367613) B367613
theorem B212323 : Blo 211809 212323 := bstep (se 1 (by rfl) ⟨159242, by rfl⟩ : syracuseStep 212323 = 318485) B318485
theorem B605549 : Blo 211809 605549 := bstep (se 3 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 605549 = 227081) B227081
theorem B540017 : Blo 211809 540017 := bstep (se 2 (by rfl) ⟨202506, by rfl⟩ : syracuseStep 540017 = 405013) B405013
theorem B212339 : Blo 211809 212339 := bstep (se 1 (by rfl) ⟨159254, by rfl⟩ : syracuseStep 212339 = 318509) B318509
theorem B212355 : Blo 211809 212355 := bstep (se 1 (by rfl) ⟨159266, by rfl⟩ : syracuseStep 212355 = 318533) B318533
theorem B212371 : Blo 211809 212371 := bstep (se 1 (by rfl) ⟨159278, by rfl⟩ : syracuseStep 212371 = 318557) B318557
theorem B212387 : Blo 211809 212387 := bstep (se 1 (by rfl) ⟨159290, by rfl⟩ : syracuseStep 212387 = 318581) B318581
theorem B540067 : Blo 211809 540067 := bstep (se 1 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 540067 = 810101) B810101
theorem B212403 : Blo 211809 212403 := bstep (se 1 (by rfl) ⟨159302, by rfl⟩ : syracuseStep 212403 = 318605) B318605
theorem B212419 : Blo 211809 212419 := bstep (se 1 (by rfl) ⟨159314, by rfl⟩ : syracuseStep 212419 = 318629) B318629
theorem B5848517 : Blo 211809 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B1228229 : Blo 211809 1228229 := bstep (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) B230293
theorem B212435 : Blo 211809 212435 := bstep (se 1 (by rfl) ⟨159326, by rfl⟩ : syracuseStep 212435 = 318653) B318653
theorem B212451 : Blo 211809 212451 := bstep (se 1 (by rfl) ⟨159338, by rfl⟩ : syracuseStep 212451 = 318677) B318677
theorem B835043 : Blo 211809 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B212467 : Blo 211809 212467 := bstep (se 1 (by rfl) ⟨159350, by rfl⟩ : syracuseStep 212467 = 318701) B318701
theorem B212483 : Blo 211809 212483 := bstep (se 1 (by rfl) ⟨159362, by rfl⟩ : syracuseStep 212483 = 318725) B318725
theorem B212499 : Blo 211809 212499 := bstep (se 1 (by rfl) ⟨159374, by rfl⟩ : syracuseStep 212499 = 318749) B318749
theorem B212515 : Blo 211809 212515 := bstep (se 1 (by rfl) ⟨159386, by rfl⟩ : syracuseStep 212515 = 318773) B318773
theorem B605731 : Blo 211809 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B540209 : Blo 211809 540209 := bstep (se 2 (by rfl) ⟨202578, by rfl⟩ : syracuseStep 540209 = 405157) B405157
theorem B212531 : Blo 211809 212531 := bstep (se 1 (by rfl) ⟨159398, by rfl⟩ : syracuseStep 212531 = 318797) B318797
theorem B212547 : Blo 211809 212547 := bstep (se 1 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 212547 = 318821) B318821
theorem B212563 : Blo 211809 212563 := bstep (se 1 (by rfl) ⟨159422, by rfl⟩ : syracuseStep 212563 = 318845) B318845
theorem B212579 : Blo 211809 212579 := bstep (se 1 (by rfl) ⟨159434, by rfl⟩ : syracuseStep 212579 = 318869) B318869
theorem B212595 : Blo 211809 212595 := bstep (se 1 (by rfl) ⟨159446, by rfl⟩ : syracuseStep 212595 = 318893) B318893
theorem B212611 : Blo 211809 212611 := bstep (se 1 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 212611 = 318917) B318917
theorem B212627 : Blo 211809 212627 := bstep (se 1 (by rfl) ⟨159470, by rfl⟩ : syracuseStep 212627 = 318941) B318941
theorem B212643 : Blo 211809 212643 := bstep (se 1 (by rfl) ⟨159482, by rfl⟩ : syracuseStep 212643 = 318965) B318965
theorem B212659 : Blo 211809 212659 := bstep (se 1 (by rfl) ⟨159494, by rfl⟩ : syracuseStep 212659 = 318989) B318989
theorem B212675 : Blo 211809 212675 := bstep (se 1 (by rfl) ⟨159506, by rfl⟩ : syracuseStep 212675 = 319013) B319013
theorem B212691 : Blo 211809 212691 := bstep (se 1 (by rfl) ⟨159518, by rfl⟩ : syracuseStep 212691 = 319037) B319037
theorem B212707 : Blo 211809 212707 := bstep (se 1 (by rfl) ⟨159530, by rfl⟩ : syracuseStep 212707 = 319061) B319061
theorem B212723 : Blo 211809 212723 := bstep (se 1 (by rfl) ⟨159542, by rfl⟩ : syracuseStep 212723 = 319085) B319085
theorem B212739 : Blo 211809 212739 := bstep (se 1 (by rfl) ⟨159554, by rfl⟩ : syracuseStep 212739 = 319109) B319109
theorem B212755 : Blo 211809 212755 := bstep (se 1 (by rfl) ⟨159566, by rfl⟩ : syracuseStep 212755 = 319133) B319133
theorem B212771 : Blo 211809 212771 := bstep (se 1 (by rfl) ⟨159578, by rfl⟩ : syracuseStep 212771 = 319157) B319157
theorem B212787 : Blo 211809 212787 := bstep (se 1 (by rfl) ⟨159590, by rfl⟩ : syracuseStep 212787 = 319181) B319181
theorem B212803 : Blo 211809 212803 := bstep (se 1 (by rfl) ⟨159602, by rfl⟩ : syracuseStep 212803 = 319205) B319205
theorem B212819 : Blo 211809 212819 := bstep (se 1 (by rfl) ⟨159614, by rfl⟩ : syracuseStep 212819 = 319229) B319229
theorem B212835 : Blo 211809 212835 := bstep (se 1 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 212835 = 319253) B319253
theorem B212851 : Blo 211809 212851 := bstep (se 1 (by rfl) ⟨159638, by rfl⟩ : syracuseStep 212851 = 319277) B319277
theorem B212867 : Blo 211809 212867 := bstep (se 1 (by rfl) ⟨159650, by rfl⟩ : syracuseStep 212867 = 319301) B319301
theorem B212883 : Blo 211809 212883 := bstep (se 1 (by rfl) ⟨159662, by rfl⟩ : syracuseStep 212883 = 319325) B319325
theorem B212899 : Blo 211809 212899 := bstep (se 1 (by rfl) ⟨159674, by rfl⟩ : syracuseStep 212899 = 319349) B319349
theorem B212915 : Blo 211809 212915 := bstep (se 1 (by rfl) ⟨159686, by rfl⟩ : syracuseStep 212915 = 319373) B319373
theorem B212931 : Blo 211809 212931 := bstep (se 1 (by rfl) ⟨159698, by rfl⟩ : syracuseStep 212931 = 319397) B319397
theorem B344017 : Blo 211809 344017 := bstep (se 2 (by rfl) ⟨129006, by rfl⟩ : syracuseStep 344017 = 258013) B258013
theorem B212947 : Blo 211809 212947 := bstep (se 1 (by rfl) ⟨159710, by rfl⟩ : syracuseStep 212947 = 319421) B319421
theorem B212963 : Blo 211809 212963 := bstep (se 1 (by rfl) ⟨159722, by rfl⟩ : syracuseStep 212963 = 319445) B319445
theorem B212979 : Blo 211809 212979 := bstep (se 1 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 212979 = 319469) B319469
theorem B212995 : Blo 211809 212995 := bstep (se 1 (by rfl) ⟨159746, by rfl⟩ : syracuseStep 212995 = 319493) B319493
theorem B213011 : Blo 211809 213011 := bstep (se 1 (by rfl) ⟨159758, by rfl⟩ : syracuseStep 213011 = 319517) B319517
theorem B213027 : Blo 211809 213027 := bstep (se 1 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 213027 = 319541) B319541
theorem B213043 : Blo 211809 213043 := bstep (se 1 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 213043 = 319565) B319565
theorem B213059 : Blo 211809 213059 := bstep (se 1 (by rfl) ⟨159794, by rfl⟩ : syracuseStep 213059 = 319589) B319589
theorem B1359949 : Blo 211809 1359949 := bstep (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) B509981
theorem B213075 : Blo 211809 213075 := bstep (se 1 (by rfl) ⟨159806, by rfl⟩ : syracuseStep 213075 = 319613) B319613
theorem B213091 : Blo 211809 213091 := bstep (se 1 (by rfl) ⟨159818, by rfl⟩ : syracuseStep 213091 = 319637) B319637
theorem B213107 : Blo 211809 213107 := bstep (se 1 (by rfl) ⟨159830, by rfl⟩ : syracuseStep 213107 = 319661) B319661
theorem B213123 : Blo 211809 213123 := bstep (se 1 (by rfl) ⟨159842, by rfl⟩ : syracuseStep 213123 = 319685) B319685
theorem B213139 : Blo 211809 213139 := bstep (se 1 (by rfl) ⟨159854, by rfl⟩ : syracuseStep 213139 = 319709) B319709
theorem B213155 : Blo 211809 213155 := bstep (se 1 (by rfl) ⟨159866, by rfl⟩ : syracuseStep 213155 = 319733) B319733
theorem B213171 : Blo 211809 213171 := bstep (se 1 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 213171 = 319757) B319757
theorem B213187 : Blo 211809 213187 := bstep (se 1 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 213187 = 319781) B319781
theorem B213203 : Blo 211809 213203 := bstep (se 1 (by rfl) ⟨159902, by rfl⟩ : syracuseStep 213203 = 319805) B319805
theorem B213219 : Blo 211809 213219 := bstep (se 1 (by rfl) ⟨159914, by rfl⟩ : syracuseStep 213219 = 319829) B319829
theorem B409841 : Blo 211809 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B213235 : Blo 211809 213235 := bstep (se 1 (by rfl) ⟨159926, by rfl⟩ : syracuseStep 213235 = 319853) B319853
theorem B213251 : Blo 211809 213251 := bstep (se 1 (by rfl) ⟨159938, by rfl⟩ : syracuseStep 213251 = 319877) B319877
theorem B213267 : Blo 211809 213267 := bstep (se 1 (by rfl) ⟨159950, by rfl⟩ : syracuseStep 213267 = 319901) B319901
theorem B213283 : Blo 211809 213283 := bstep (se 1 (by rfl) ⟨159962, by rfl⟩ : syracuseStep 213283 = 319925) B319925
theorem B213299 : Blo 211809 213299 := bstep (se 1 (by rfl) ⟨159974, by rfl⟩ : syracuseStep 213299 = 319949) B319949
theorem B213315 : Blo 211809 213315 := bstep (se 1 (by rfl) ⟨159986, by rfl⟩ : syracuseStep 213315 = 319973) B319973
theorem B213331 : Blo 211809 213331 := bstep (se 1 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 213331 = 319997) B319997
theorem B213347 : Blo 211809 213347 := bstep (se 1 (by rfl) ⟨160010, by rfl⟩ : syracuseStep 213347 = 320021) B320021
theorem B213363 : Blo 211809 213363 := bstep (se 1 (by rfl) ⟨160022, by rfl⟩ : syracuseStep 213363 = 320045) B320045
theorem B213379 : Blo 211809 213379 := bstep (se 1 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 213379 = 320069) B320069
theorem B213395 : Blo 211809 213395 := bstep (se 1 (by rfl) ⟨160046, by rfl⟩ : syracuseStep 213395 = 320093) B320093
theorem B213411 : Blo 211809 213411 := bstep (se 1 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 213411 = 320117) B320117
theorem B213427 : Blo 211809 213427 := bstep (se 1 (by rfl) ⟨160070, by rfl⟩ : syracuseStep 213427 = 320141) B320141
theorem B213443 : Blo 211809 213443 := bstep (se 1 (by rfl) ⟨160082, by rfl⟩ : syracuseStep 213443 = 320165) B320165
theorem B213459 : Blo 211809 213459 := bstep (se 1 (by rfl) ⟨160094, by rfl⟩ : syracuseStep 213459 = 320189) B320189
theorem B213475 : Blo 211809 213475 := bstep (se 1 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 213475 = 320213) B320213
theorem B213491 : Blo 211809 213491 := bstep (se 1 (by rfl) ⟨160118, by rfl⟩ : syracuseStep 213491 = 320237) B320237
theorem B213507 : Blo 211809 213507 := bstep (se 1 (by rfl) ⟨160130, by rfl⟩ : syracuseStep 213507 = 320261) B320261
theorem B541201 : Blo 211809 541201 := bstep (se 2 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 541201 = 405901) B405901
theorem B213523 : Blo 211809 213523 := bstep (se 1 (by rfl) ⟨160142, by rfl⟩ : syracuseStep 213523 = 320285) B320285
theorem B213539 : Blo 211809 213539 := bstep (se 1 (by rfl) ⟨160154, by rfl⟩ : syracuseStep 213539 = 320309) B320309
theorem B213555 : Blo 211809 213555 := bstep (se 1 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 213555 = 320333) B320333
theorem B410179 : Blo 211809 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B213571 : Blo 211809 213571 := bstep (se 1 (by rfl) ⟨160178, by rfl⟩ : syracuseStep 213571 = 320357) B320357
theorem B213587 : Blo 211809 213587 := bstep (se 1 (by rfl) ⟨160190, by rfl⟩ : syracuseStep 213587 = 320381) B320381
theorem B213603 : Blo 211809 213603 := bstep (se 1 (by rfl) ⟨160202, by rfl⟩ : syracuseStep 213603 = 320405) B320405
theorem B213619 : Blo 211809 213619 := bstep (se 1 (by rfl) ⟨160214, by rfl⟩ : syracuseStep 213619 = 320429) B320429
theorem B213635 : Blo 211809 213635 := bstep (se 1 (by rfl) ⟨160226, by rfl⟩ : syracuseStep 213635 = 320453) B320453
theorem B213651 : Blo 211809 213651 := bstep (se 1 (by rfl) ⟨160238, by rfl⟩ : syracuseStep 213651 = 320477) B320477
theorem B213667 : Blo 211809 213667 := bstep (se 1 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 213667 = 320501) B320501
theorem B213683 : Blo 211809 213683 := bstep (se 1 (by rfl) ⟨160262, by rfl⟩ : syracuseStep 213683 = 320525) B320525
theorem B213699 : Blo 211809 213699 := bstep (se 1 (by rfl) ⟨160274, by rfl⟩ : syracuseStep 213699 = 320549) B320549
theorem B213715 : Blo 211809 213715 := bstep (se 1 (by rfl) ⟨160286, by rfl⟩ : syracuseStep 213715 = 320573) B320573
theorem B213731 : Blo 211809 213731 := bstep (se 1 (by rfl) ⟨160298, by rfl⟩ : syracuseStep 213731 = 320597) B320597
theorem B213747 : Blo 211809 213747 := bstep (se 1 (by rfl) ⟨160310, by rfl⟩ : syracuseStep 213747 = 320621) B320621
theorem B213763 : Blo 211809 213763 := bstep (se 1 (by rfl) ⟨160322, by rfl⟩ : syracuseStep 213763 = 320645) B320645
theorem B213779 : Blo 211809 213779 := bstep (se 1 (by rfl) ⟨160334, by rfl⟩ : syracuseStep 213779 = 320669) B320669
theorem B213795 : Blo 211809 213795 := bstep (se 1 (by rfl) ⟨160346, by rfl⟩ : syracuseStep 213795 = 320693) B320693
theorem B541475 : Blo 211809 541475 := bstep (se 1 (by rfl) ⟨406106, by rfl⟩ : syracuseStep 541475 = 812213) B812213
theorem B213811 : Blo 211809 213811 := bstep (se 1 (by rfl) ⟨160358, by rfl⟩ : syracuseStep 213811 = 320717) B320717
theorem B213827 : Blo 211809 213827 := bstep (se 1 (by rfl) ⟨160370, by rfl⟩ : syracuseStep 213827 = 320741) B320741
theorem B213843 : Blo 211809 213843 := bstep (se 1 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 213843 = 320765) B320765
theorem B213859 : Blo 211809 213859 := bstep (se 1 (by rfl) ⟨160394, by rfl⟩ : syracuseStep 213859 = 320789) B320789
theorem B3687281 : Blo 211809 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B213875 : Blo 211809 213875 := bstep (se 1 (by rfl) ⟨160406, by rfl⟩ : syracuseStep 213875 = 320813) B320813
theorem B213891 : Blo 211809 213891 := bstep (se 1 (by rfl) ⟨160418, by rfl⟩ : syracuseStep 213891 = 320837) B320837
theorem B1491853 : Blo 211809 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B607121 : Blo 211809 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B213907 : Blo 211809 213907 := bstep (se 1 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 213907 = 320861) B320861
theorem B213923 : Blo 211809 213923 := bstep (se 1 (by rfl) ⟨160442, by rfl⟩ : syracuseStep 213923 = 320885) B320885
theorem B967601 : Blo 211809 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B213939 : Blo 211809 213939 := bstep (se 1 (by rfl) ⟨160454, by rfl⟩ : syracuseStep 213939 = 320909) B320909
theorem B213955 : Blo 211809 213955 := bstep (se 1 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 213955 = 320933) B320933
theorem B345043 : Blo 211809 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B213971 : Blo 211809 213971 := bstep (se 1 (by rfl) ⟨160478, by rfl⟩ : syracuseStep 213971 = 320957) B320957
theorem B213987 : Blo 211809 213987 := bstep (se 1 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 213987 = 320981) B320981
theorem B541667 : Blo 211809 541667 := bstep (se 1 (by rfl) ⟨406250, by rfl⟩ : syracuseStep 541667 = 812501) B812501
theorem B214003 : Blo 211809 214003 := bstep (se 1 (by rfl) ⟨160502, by rfl⟩ : syracuseStep 214003 = 321005) B321005
theorem B214019 : Blo 211809 214019 := bstep (se 1 (by rfl) ⟨160514, by rfl⟩ : syracuseStep 214019 = 321029) B321029
theorem B214035 : Blo 211809 214035 := bstep (se 1 (by rfl) ⟨160526, by rfl⟩ : syracuseStep 214035 = 321053) B321053
theorem B214051 : Blo 211809 214051 := bstep (se 1 (by rfl) ⟨160538, by rfl⟩ : syracuseStep 214051 = 321077) B321077
theorem B214067 : Blo 211809 214067 := bstep (se 1 (by rfl) ⟨160550, by rfl⟩ : syracuseStep 214067 = 321101) B321101
theorem B214083 : Blo 211809 214083 := bstep (se 1 (by rfl) ⟨160562, by rfl⟩ : syracuseStep 214083 = 321125) B321125
theorem B214099 : Blo 211809 214099 := bstep (se 1 (by rfl) ⟨160574, by rfl⟩ : syracuseStep 214099 = 321149) B321149
theorem B214115 : Blo 211809 214115 := bstep (se 1 (by rfl) ⟨160586, by rfl⟩ : syracuseStep 214115 = 321173) B321173
theorem B7554161 : Blo 211809 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B214131 : Blo 211809 214131 := bstep (se 1 (by rfl) ⟨160598, by rfl⟩ : syracuseStep 214131 = 321197) B321197
theorem B214147 : Blo 211809 214147 := bstep (se 1 (by rfl) ⟨160610, by rfl⟩ : syracuseStep 214147 = 321221) B321221
theorem B214163 : Blo 211809 214163 := bstep (se 1 (by rfl) ⟨160622, by rfl⟩ : syracuseStep 214163 = 321245) B321245
theorem B345235 : Blo 211809 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B574627 : Blo 211809 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B214179 : Blo 211809 214179 := bstep (se 1 (by rfl) ⟨160634, by rfl⟩ : syracuseStep 214179 = 321269) B321269
theorem B214195 : Blo 211809 214195 := bstep (se 1 (by rfl) ⟨160646, by rfl⟩ : syracuseStep 214195 = 321293) B321293
theorem B214211 : Blo 211809 214211 := bstep (se 1 (by rfl) ⟨160658, by rfl⟩ : syracuseStep 214211 = 321317) B321317
theorem B214227 : Blo 211809 214227 := bstep (se 1 (by rfl) ⟨160670, by rfl⟩ : syracuseStep 214227 = 321341) B321341
theorem B214243 : Blo 211809 214243 := bstep (se 1 (by rfl) ⟨160682, by rfl⟩ : syracuseStep 214243 = 321365) B321365
theorem B214259 : Blo 211809 214259 := bstep (se 1 (by rfl) ⟨160694, by rfl⟩ : syracuseStep 214259 = 321389) B321389
theorem B214275 : Blo 211809 214275 := bstep (se 1 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 214275 = 321413) B321413
theorem B214291 : Blo 211809 214291 := bstep (se 1 (by rfl) ⟨160718, by rfl⟩ : syracuseStep 214291 = 321437) B321437
theorem B214307 : Blo 211809 214307 := bstep (se 1 (by rfl) ⟨160730, by rfl⟩ : syracuseStep 214307 = 321461) B321461
theorem B214323 : Blo 211809 214323 := bstep (se 1 (by rfl) ⟨160742, by rfl⟩ : syracuseStep 214323 = 321485) B321485
theorem B214339 : Blo 211809 214339 := bstep (se 1 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 214339 = 321509) B321509
theorem B214355 : Blo 211809 214355 := bstep (se 1 (by rfl) ⟨160766, by rfl⟩ : syracuseStep 214355 = 321533) B321533
theorem B2311523 : Blo 211809 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B214371 : Blo 211809 214371 := bstep (se 1 (by rfl) ⟨160778, by rfl⟩ : syracuseStep 214371 = 321557) B321557
theorem B214387 : Blo 211809 214387 := bstep (se 1 (by rfl) ⟨160790, by rfl⟩ : syracuseStep 214387 = 321581) B321581
theorem B214403 : Blo 211809 214403 := bstep (se 1 (by rfl) ⟨160802, by rfl⟩ : syracuseStep 214403 = 321605) B321605
theorem B214419 : Blo 211809 214419 := bstep (se 1 (by rfl) ⟨160814, by rfl⟩ : syracuseStep 214419 = 321629) B321629
theorem B214435 : Blo 211809 214435 := bstep (se 1 (by rfl) ⟨160826, by rfl⟩ : syracuseStep 214435 = 321653) B321653
theorem B214451 : Blo 211809 214451 := bstep (se 1 (by rfl) ⟨160838, by rfl⟩ : syracuseStep 214451 = 321677) B321677
theorem B214467 : Blo 211809 214467 := bstep (se 1 (by rfl) ⟨160850, by rfl⟩ : syracuseStep 214467 = 321701) B321701
theorem B1394117 : Blo 211809 1394117 := bstep (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) B261397
theorem B214483 : Blo 211809 214483 := bstep (se 1 (by rfl) ⟨160862, by rfl⟩ : syracuseStep 214483 = 321725) B321725
theorem B214499 : Blo 211809 214499 := bstep (se 1 (by rfl) ⟨160874, by rfl⟩ : syracuseStep 214499 = 321749) B321749
theorem B476657 : Blo 211809 476657 := bstep (se 2 (by rfl) ⟨178746, by rfl⟩ : syracuseStep 476657 = 357493) B357493
theorem B214515 : Blo 211809 214515 := bstep (se 1 (by rfl) ⟨160886, by rfl⟩ : syracuseStep 214515 = 321773) B321773
theorem B476675 : Blo 211809 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B214531 : Blo 211809 214531 := bstep (se 1 (by rfl) ⟨160898, by rfl⟩ : syracuseStep 214531 = 321797) B321797
theorem B214547 : Blo 211809 214547 := bstep (se 1 (by rfl) ⟨160910, by rfl⟩ : syracuseStep 214547 = 321821) B321821
theorem B214563 : Blo 211809 214563 := bstep (se 1 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 214563 = 321845) B321845
theorem B214579 : Blo 211809 214579 := bstep (se 1 (by rfl) ⟨160934, by rfl⟩ : syracuseStep 214579 = 321869) B321869
theorem B214595 : Blo 211809 214595 := bstep (se 1 (by rfl) ⟨160946, by rfl⟩ : syracuseStep 214595 = 321893) B321893
theorem B214611 : Blo 211809 214611 := bstep (se 1 (by rfl) ⟨160958, by rfl⟩ : syracuseStep 214611 = 321917) B321917
theorem B804451 : Blo 211809 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B214627 : Blo 211809 214627 := bstep (se 1 (by rfl) ⟨160970, by rfl⟩ : syracuseStep 214627 = 321941) B321941
theorem B214643 : Blo 211809 214643 := bstep (se 1 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 214643 = 321965) B321965
theorem B214659 : Blo 211809 214659 := bstep (se 1 (by rfl) ⟨160994, by rfl⟩ : syracuseStep 214659 = 321989) B321989
theorem B214675 : Blo 211809 214675 := bstep (se 1 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 214675 = 322013) B322013
theorem B214691 : Blo 211809 214691 := bstep (se 1 (by rfl) ⟨161018, by rfl⟩ : syracuseStep 214691 = 322037) B322037
theorem B214707 : Blo 211809 214707 := bstep (se 1 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 214707 = 322061) B322061
theorem B214723 : Blo 211809 214723 := bstep (se 1 (by rfl) ⟨161042, by rfl⟩ : syracuseStep 214723 = 322085) B322085
theorem B214739 : Blo 211809 214739 := bstep (se 1 (by rfl) ⟨161054, by rfl⟩ : syracuseStep 214739 = 322109) B322109
theorem B214755 : Blo 211809 214755 := bstep (se 1 (by rfl) ⟨161066, by rfl⟩ : syracuseStep 214755 = 322133) B322133
theorem B214771 : Blo 211809 214771 := bstep (se 1 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 214771 = 322157) B322157
theorem B214787 : Blo 211809 214787 := bstep (se 1 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 214787 = 322181) B322181
theorem B476945 : Blo 211809 476945 := bstep (se 2 (by rfl) ⟨178854, by rfl⟩ : syracuseStep 476945 = 357709) B357709
theorem B214803 : Blo 211809 214803 := bstep (se 1 (by rfl) ⟨161102, by rfl⟩ : syracuseStep 214803 = 322205) B322205
theorem B476963 : Blo 211809 476963 := bstep (se 1 (by rfl) ⟨357722, by rfl⟩ : syracuseStep 476963 = 715445) B715445
theorem B214819 : Blo 211809 214819 := bstep (se 1 (by rfl) ⟨161114, by rfl⟩ : syracuseStep 214819 = 322229) B322229
theorem B214835 : Blo 211809 214835 := bstep (se 1 (by rfl) ⟨161126, by rfl⟩ : syracuseStep 214835 = 322253) B322253
theorem B214851 : Blo 211809 214851 := bstep (se 1 (by rfl) ⟨161138, by rfl⟩ : syracuseStep 214851 = 322277) B322277
theorem B2475845 : Blo 211809 2475845 := bstep (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) B464221
theorem B608077 : Blo 211809 608077 := bstep (se 3 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 608077 = 228029) B228029
theorem B411473 : Blo 211809 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B214867 : Blo 211809 214867 := bstep (se 1 (by rfl) ⟨161150, by rfl⟩ : syracuseStep 214867 = 322301) B322301
theorem B214883 : Blo 211809 214883 := bstep (se 1 (by rfl) ⟨161162, by rfl⟩ : syracuseStep 214883 = 322325) B322325
theorem B214899 : Blo 211809 214899 := bstep (se 1 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 214899 = 322349) B322349
theorem B214915 : Blo 211809 214915 := bstep (se 1 (by rfl) ⟨161186, by rfl⟩ : syracuseStep 214915 = 322373) B322373
theorem B542609 : Blo 211809 542609 := bstep (se 2 (by rfl) ⟨203478, by rfl⟩ : syracuseStep 542609 = 406957) B406957
theorem B214931 : Blo 211809 214931 := bstep (se 1 (by rfl) ⟨161198, by rfl⟩ : syracuseStep 214931 = 322397) B322397
theorem B214947 : Blo 211809 214947 := bstep (se 1 (by rfl) ⟨161210, by rfl⟩ : syracuseStep 214947 = 322421) B322421
theorem B214963 : Blo 211809 214963 := bstep (se 1 (by rfl) ⟨161222, by rfl⟩ : syracuseStep 214963 = 322445) B322445
theorem B542659 : Blo 211809 542659 := bstep (se 1 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 542659 = 813989) B813989
theorem B214979 : Blo 211809 214979 := bstep (se 1 (by rfl) ⟨161234, by rfl⟩ : syracuseStep 214979 = 322469) B322469
theorem B509905 : Blo 211809 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B214995 : Blo 211809 214995 := bstep (se 1 (by rfl) ⟨161246, by rfl⟩ : syracuseStep 214995 = 322493) B322493
theorem B215011 : Blo 211809 215011 := bstep (se 1 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 215011 = 322517) B322517
theorem B215027 : Blo 211809 215027 := bstep (se 1 (by rfl) ⟨161270, by rfl⟩ : syracuseStep 215027 = 322541) B322541
theorem B215043 : Blo 211809 215043 := bstep (se 1 (by rfl) ⟨161282, by rfl⟩ : syracuseStep 215043 = 322565) B322565
theorem B215059 : Blo 211809 215059 := bstep (se 1 (by rfl) ⟨161294, by rfl⟩ : syracuseStep 215059 = 322589) B322589
theorem B215075 : Blo 211809 215075 := bstep (se 1 (by rfl) ⟨161306, by rfl⟩ : syracuseStep 215075 = 322613) B322613
theorem B477233 : Blo 211809 477233 := bstep (se 2 (by rfl) ⟨178962, by rfl⟩ : syracuseStep 477233 = 357925) B357925
theorem B608305 : Blo 211809 608305 := bstep (se 2 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 608305 = 456229) B456229
theorem B215091 : Blo 211809 215091 := bstep (se 1 (by rfl) ⟨161318, by rfl⟩ : syracuseStep 215091 = 322637) B322637
theorem B477251 : Blo 211809 477251 := bstep (se 1 (by rfl) ⟨357938, by rfl⟩ : syracuseStep 477251 = 715877) B715877
theorem B215107 : Blo 211809 215107 := bstep (se 1 (by rfl) ⟨161330, by rfl⟩ : syracuseStep 215107 = 322661) B322661
theorem B542801 : Blo 211809 542801 := bstep (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) B407101
theorem B215123 : Blo 211809 215123 := bstep (se 1 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 215123 = 322685) B322685
theorem B215139 : Blo 211809 215139 := bstep (se 1 (by rfl) ⟨161354, by rfl⟩ : syracuseStep 215139 = 322709) B322709
theorem B215155 : Blo 211809 215155 := bstep (se 1 (by rfl) ⟨161366, by rfl⟩ : syracuseStep 215155 = 322733) B322733
theorem B215171 : Blo 211809 215171 := bstep (se 1 (by rfl) ⟨161378, by rfl⟩ : syracuseStep 215171 = 322757) B322757
theorem B215187 : Blo 211809 215187 := bstep (se 1 (by rfl) ⟨161390, by rfl⟩ : syracuseStep 215187 = 322781) B322781
theorem B215203 : Blo 211809 215203 := bstep (se 1 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 215203 = 322805) B322805
theorem B215219 : Blo 211809 215219 := bstep (se 1 (by rfl) ⟨161414, by rfl⟩ : syracuseStep 215219 = 322829) B322829
theorem B215235 : Blo 211809 215235 := bstep (se 1 (by rfl) ⟨161426, by rfl⟩ : syracuseStep 215235 = 322853) B322853
theorem B608465 : Blo 211809 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B215251 : Blo 211809 215251 := bstep (se 1 (by rfl) ⟨161438, by rfl⟩ : syracuseStep 215251 = 322877) B322877
theorem B215267 : Blo 211809 215267 := bstep (se 1 (by rfl) ⟨161450, by rfl⟩ : syracuseStep 215267 = 322901) B322901
theorem B215283 : Blo 211809 215283 := bstep (se 1 (by rfl) ⟨161462, by rfl⟩ : syracuseStep 215283 = 322925) B322925
theorem B215299 : Blo 211809 215299 := bstep (se 1 (by rfl) ⟨161474, by rfl⟩ : syracuseStep 215299 = 322949) B322949
theorem B215315 : Blo 211809 215315 := bstep (se 1 (by rfl) ⟨161486, by rfl⟩ : syracuseStep 215315 = 322973) B322973
theorem B215331 : Blo 211809 215331 := bstep (se 1 (by rfl) ⟨161498, by rfl⟩ : syracuseStep 215331 = 322997) B322997
theorem B215347 : Blo 211809 215347 := bstep (se 1 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 215347 = 323021) B323021
theorem B608579 : Blo 211809 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B215363 : Blo 211809 215363 := bstep (se 1 (by rfl) ⟨161522, by rfl⟩ : syracuseStep 215363 = 323045) B323045
theorem B477521 : Blo 211809 477521 := bstep (se 2 (by rfl) ⟨179070, by rfl⟩ : syracuseStep 477521 = 358141) B358141
theorem B215379 : Blo 211809 215379 := bstep (se 1 (by rfl) ⟨161534, by rfl⟩ : syracuseStep 215379 = 323069) B323069
theorem B477539 : Blo 211809 477539 := bstep (se 1 (by rfl) ⟨358154, by rfl⟩ : syracuseStep 477539 = 716309) B716309
theorem B215395 : Blo 211809 215395 := bstep (se 1 (by rfl) ⟨161546, by rfl⟩ : syracuseStep 215395 = 323093) B323093
theorem B215411 : Blo 211809 215411 := bstep (se 1 (by rfl) ⟨161558, by rfl⟩ : syracuseStep 215411 = 323117) B323117
theorem B215427 : Blo 211809 215427 := bstep (se 1 (by rfl) ⟨161570, by rfl⟩ : syracuseStep 215427 = 323141) B323141
theorem B215443 : Blo 211809 215443 := bstep (se 1 (by rfl) ⟨161582, by rfl⟩ : syracuseStep 215443 = 323165) B323165
theorem B215459 : Blo 211809 215459 := bstep (se 1 (by rfl) ⟨161594, by rfl⟩ : syracuseStep 215459 = 323189) B323189
theorem B215475 : Blo 211809 215475 := bstep (se 1 (by rfl) ⟨161606, by rfl⟩ : syracuseStep 215475 = 323213) B323213
theorem B215491 : Blo 211809 215491 := bstep (se 1 (by rfl) ⟨161618, by rfl⟩ : syracuseStep 215491 = 323237) B323237
theorem B215507 : Blo 211809 215507 := bstep (se 1 (by rfl) ⟨161630, by rfl⟩ : syracuseStep 215507 = 323261) B323261
theorem B215523 : Blo 211809 215523 := bstep (se 1 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 215523 = 323285) B323285
theorem B215539 : Blo 211809 215539 := bstep (se 1 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 215539 = 323309) B323309
theorem B215555 : Blo 211809 215555 := bstep (se 1 (by rfl) ⟨161666, by rfl⟩ : syracuseStep 215555 = 323333) B323333
theorem B215571 : Blo 211809 215571 := bstep (se 1 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 215571 = 323357) B323357
theorem B215587 : Blo 211809 215587 := bstep (se 1 (by rfl) ⟨161690, by rfl⟩ : syracuseStep 215587 = 323381) B323381
theorem B215603 : Blo 211809 215603 := bstep (se 1 (by rfl) ⟨161702, by rfl⟩ : syracuseStep 215603 = 323405) B323405
theorem B215619 : Blo 211809 215619 := bstep (se 1 (by rfl) ⟨161714, by rfl⟩ : syracuseStep 215619 = 323429) B323429
theorem B215635 : Blo 211809 215635 := bstep (se 1 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 215635 = 323453) B323453
theorem B215651 : Blo 211809 215651 := bstep (se 1 (by rfl) ⟨161738, by rfl⟩ : syracuseStep 215651 = 323477) B323477
theorem B477809 : Blo 211809 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B215667 : Blo 211809 215667 := bstep (se 1 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 215667 = 323501) B323501
theorem B477827 : Blo 211809 477827 := bstep (se 1 (by rfl) ⟨358370, by rfl⟩ : syracuseStep 477827 = 716741) B716741
theorem B215683 : Blo 211809 215683 := bstep (se 1 (by rfl) ⟨161762, by rfl⟩ : syracuseStep 215683 = 323525) B323525
theorem B215699 : Blo 211809 215699 := bstep (se 1 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 215699 = 323549) B323549
theorem B215715 : Blo 211809 215715 := bstep (se 1 (by rfl) ⟨161786, by rfl⟩ : syracuseStep 215715 = 323573) B323573
theorem B215731 : Blo 211809 215731 := bstep (se 1 (by rfl) ⟨161798, by rfl⟩ : syracuseStep 215731 = 323597) B323597
theorem B215747 : Blo 211809 215747 := bstep (se 1 (by rfl) ⟨161810, by rfl⟩ : syracuseStep 215747 = 323621) B323621
theorem B215763 : Blo 211809 215763 := bstep (se 1 (by rfl) ⟨161822, by rfl⟩ : syracuseStep 215763 = 323645) B323645
theorem B1395427 : Blo 211809 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B215779 : Blo 211809 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B215795 : Blo 211809 215795 := bstep (se 1 (by rfl) ⟨161846, by rfl⟩ : syracuseStep 215795 = 323693) B323693
theorem B478097 : Blo 211809 478097 := bstep (se 2 (by rfl) ⟨179286, by rfl⟩ : syracuseStep 478097 = 358573) B358573
theorem B478115 : Blo 211809 478115 := bstep (se 1 (by rfl) ⟨358586, by rfl⟩ : syracuseStep 478115 = 717173) B717173
theorem B576497 : Blo 211809 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B314371 : Blo 211809 314371 := bstep (se 1 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 314371 = 471557) B471557
theorem B543793 : Blo 211809 543793 := bstep (se 2 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 543793 = 407845) B407845
theorem B1035341 : Blo 211809 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B478385 : Blo 211809 478385 := bstep (se 2 (by rfl) ⟨179394, by rfl⟩ : syracuseStep 478385 = 358789) B358789
theorem B478403 : Blo 211809 478403 := bstep (se 1 (by rfl) ⟨358802, by rfl⟩ : syracuseStep 478403 = 717605) B717605
theorem B609581 : Blo 211809 609581 := bstep (se 3 (by rfl) ⟨114296, by rfl⟩ : syracuseStep 609581 = 228593) B228593
theorem B544067 : Blo 211809 544067 := bstep (se 1 (by rfl) ⟨408050, by rfl⟩ : syracuseStep 544067 = 816101) B816101
theorem B576845 : Blo 211809 576845 := bstep (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) B216317
theorem B347537 : Blo 211809 347537 := bstep (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) B260653
theorem B478673 : Blo 211809 478673 := bstep (se 2 (by rfl) ⟨179502, by rfl⟩ : syracuseStep 478673 = 359005) B359005
theorem B478691 : Blo 211809 478691 := bstep (se 1 (by rfl) ⟨359018, by rfl⟩ : syracuseStep 478691 = 718037) B718037
theorem B609763 : Blo 211809 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B544259 : Blo 211809 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B1625669 : Blo 211809 1625669 := bstep (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) B304813
theorem B609923 : Blo 211809 609923 := bstep (se 1 (by rfl) ⟨457442, by rfl⟩ : syracuseStep 609923 = 914885) B914885
theorem B478961 : Blo 211809 478961 := bstep (se 2 (by rfl) ⟨179610, by rfl⟩ : syracuseStep 478961 = 359221) B359221
theorem B478979 : Blo 211809 478979 := bstep (se 1 (by rfl) ⟨359234, by rfl⟩ : syracuseStep 478979 = 718469) B718469
theorem B806669 : Blo 211809 806669 := bstep (se 3 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 806669 = 302501) B302501
theorem B1822661 : Blo 211809 1822661 := bstep (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) B341749
theorem B479249 : Blo 211809 479249 := bstep (se 2 (by rfl) ⟨179718, by rfl⟩ : syracuseStep 479249 = 359437) B359437
theorem B479267 : Blo 211809 479267 := bstep (se 1 (by rfl) ⟨359450, by rfl⟩ : syracuseStep 479267 = 718901) B718901
theorem B1101937 : Blo 211809 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B2937073 : Blo 211809 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B479537 : Blo 211809 479537 := bstep (se 2 (by rfl) ⟨179826, by rfl⟩ : syracuseStep 479537 = 359653) B359653
theorem B479555 : Blo 211809 479555 := bstep (se 1 (by rfl) ⟨359666, by rfl⟩ : syracuseStep 479555 = 719333) B719333
theorem B545201 : Blo 211809 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B545251 : Blo 211809 545251 := bstep (se 1 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 545251 = 817877) B817877
theorem B479825 : Blo 211809 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B479843 : Blo 211809 479843 := bstep (se 1 (by rfl) ⟨359882, by rfl⟩ : syracuseStep 479843 = 719765) B719765
theorem B545393 : Blo 211809 545393 := bstep (se 2 (by rfl) ⟨204522, by rfl⟩ : syracuseStep 545393 = 409045) B409045
theorem B610993 : Blo 211809 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B545507 : Blo 211809 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B1528645 : Blo 211809 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B480113 : Blo 211809 480113 := bstep (se 2 (by rfl) ⟨180042, by rfl⟩ : syracuseStep 480113 = 360085) B360085
theorem B480131 : Blo 211809 480131 := bstep (se 1 (by rfl) ⟨360098, by rfl⟩ : syracuseStep 480131 = 720197) B720197
theorem B480401 : Blo 211809 480401 := bstep (se 2 (by rfl) ⟨180150, by rfl⟩ : syracuseStep 480401 = 360301) B360301
theorem B480419 : Blo 211809 480419 := bstep (se 1 (by rfl) ⟨360314, by rfl⟩ : syracuseStep 480419 = 720629) B720629
theorem B873713 : Blo 211809 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B578929 : Blo 211809 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B480689 : Blo 211809 480689 := bstep (se 2 (by rfl) ⟨180258, by rfl⟩ : syracuseStep 480689 = 360517) B360517
theorem B480707 : Blo 211809 480707 := bstep (se 1 (by rfl) ⟨360530, by rfl⟩ : syracuseStep 480707 = 721061) B721061
theorem B480977 : Blo 211809 480977 := bstep (se 2 (by rfl) ⟨180366, by rfl⟩ : syracuseStep 480977 = 360733) B360733
theorem B480995 : Blo 211809 480995 := bstep (se 1 (by rfl) ⟨360746, by rfl⟩ : syracuseStep 480995 = 721493) B721493
theorem B513827 : Blo 211809 513827 := bstep (se 1 (by rfl) ⟨385370, by rfl⟩ : syracuseStep 513827 = 770741) B770741
theorem B612269 : Blo 211809 612269 := bstep (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) B229601
theorem B481265 : Blo 211809 481265 := bstep (se 2 (by rfl) ⟨180474, by rfl⟩ : syracuseStep 481265 = 360949) B360949
theorem B481283 : Blo 211809 481283 := bstep (se 1 (by rfl) ⟨360962, by rfl⟩ : syracuseStep 481283 = 721925) B721925
theorem B612451 : Blo 211809 612451 := bstep (se 1 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 612451 = 918677) B918677
theorem B612497 : Blo 211809 612497 := bstep (se 2 (by rfl) ⟨229686, by rfl⟩ : syracuseStep 612497 = 459373) B459373
theorem B907469 : Blo 211809 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B2054413 : Blo 211809 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B481553 : Blo 211809 481553 := bstep (se 2 (by rfl) ⟨180582, by rfl⟩ : syracuseStep 481553 = 361165) B361165
theorem B317729 : Blo 211809 317729 := bstep (se 2 (by rfl) ⟨119148, by rfl⟩ : syracuseStep 317729 = 238297) B238297
theorem B1366307 : Blo 211809 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B481571 : Blo 211809 481571 := bstep (se 1 (by rfl) ⟨361178, by rfl⟩ : syracuseStep 481571 = 722357) B722357
theorem B317747 : Blo 211809 317747 := bstep (se 1 (by rfl) ⟨238310, by rfl⟩ : syracuseStep 317747 = 476621) B476621
theorem B317777 : Blo 211809 317777 := bstep (se 2 (by rfl) ⟨119166, by rfl⟩ : syracuseStep 317777 = 238333) B238333
theorem B317795 : Blo 211809 317795 := bstep (se 1 (by rfl) ⟨238346, by rfl⟩ : syracuseStep 317795 = 476693) B476693
theorem B317825 : Blo 211809 317825 := bstep (se 2 (by rfl) ⟨119184, by rfl⟩ : syracuseStep 317825 = 238369) B238369
theorem B317843 : Blo 211809 317843 := bstep (se 1 (by rfl) ⟨238382, by rfl⟩ : syracuseStep 317843 = 476765) B476765
theorem B317873 : Blo 211809 317873 := bstep (se 2 (by rfl) ⟨119202, by rfl⟩ : syracuseStep 317873 = 238405) B238405
theorem B317891 : Blo 211809 317891 := bstep (se 1 (by rfl) ⟨238418, by rfl⟩ : syracuseStep 317891 = 476837) B476837
theorem B317921 : Blo 211809 317921 := bstep (se 2 (by rfl) ⟨119220, by rfl⟩ : syracuseStep 317921 = 238441) B238441
theorem B317939 : Blo 211809 317939 := bstep (se 1 (by rfl) ⟨238454, by rfl⟩ : syracuseStep 317939 = 476909) B476909
theorem B317969 : Blo 211809 317969 := bstep (se 2 (by rfl) ⟨119238, by rfl⟩ : syracuseStep 317969 = 238477) B238477
theorem B317987 : Blo 211809 317987 := bstep (se 1 (by rfl) ⟨238490, by rfl⟩ : syracuseStep 317987 = 476981) B476981
theorem B907811 : Blo 211809 907811 := bstep (se 1 (by rfl) ⟨680858, by rfl⟩ : syracuseStep 907811 = 1361717) B1361717
theorem B514595 : Blo 211809 514595 := bstep (se 1 (by rfl) ⟨385946, by rfl⟩ : syracuseStep 514595 = 771893) B771893
theorem B645677 : Blo 211809 645677 := bstep (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) B242129
theorem B481841 : Blo 211809 481841 := bstep (se 2 (by rfl) ⟨180690, by rfl⟩ : syracuseStep 481841 = 361381) B361381
theorem B318017 : Blo 211809 318017 := bstep (se 2 (by rfl) ⟨119256, by rfl⟩ : syracuseStep 318017 = 238513) B238513
theorem B481859 : Blo 211809 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B318035 : Blo 211809 318035 := bstep (se 1 (by rfl) ⟨238526, by rfl⟩ : syracuseStep 318035 = 477053) B477053
theorem B318065 : Blo 211809 318065 := bstep (se 2 (by rfl) ⟨119274, by rfl⟩ : syracuseStep 318065 = 238549) B238549
theorem B809585 : Blo 211809 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B318083 : Blo 211809 318083 := bstep (se 1 (by rfl) ⟨238562, by rfl⟩ : syracuseStep 318083 = 477125) B477125
theorem B2939533 : Blo 211809 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B318113 : Blo 211809 318113 := bstep (se 2 (by rfl) ⟨119292, by rfl⟩ : syracuseStep 318113 = 238585) B238585
theorem B318131 : Blo 211809 318131 := bstep (se 1 (by rfl) ⟨238598, by rfl⟩ : syracuseStep 318131 = 477197) B477197
theorem B318161 : Blo 211809 318161 := bstep (se 2 (by rfl) ⟨119310, by rfl⟩ : syracuseStep 318161 = 238621) B238621
theorem B318179 : Blo 211809 318179 := bstep (se 1 (by rfl) ⟨238634, by rfl⟩ : syracuseStep 318179 = 477269) B477269
theorem B318209 : Blo 211809 318209 := bstep (se 2 (by rfl) ⟨119328, by rfl⟩ : syracuseStep 318209 = 238657) B238657
theorem B318227 : Blo 211809 318227 := bstep (se 1 (by rfl) ⟨238670, by rfl⟩ : syracuseStep 318227 = 477341) B477341
theorem B318257 : Blo 211809 318257 := bstep (se 2 (by rfl) ⟨119346, by rfl⟩ : syracuseStep 318257 = 238693) B238693
theorem B318275 : Blo 211809 318275 := bstep (se 1 (by rfl) ⟨238706, by rfl⟩ : syracuseStep 318275 = 477413) B477413
theorem B482129 : Blo 211809 482129 := bstep (se 2 (by rfl) ⟨180798, by rfl⟩ : syracuseStep 482129 = 361597) B361597
theorem B318305 : Blo 211809 318305 := bstep (se 2 (by rfl) ⟨119364, by rfl⟩ : syracuseStep 318305 = 238729) B238729
theorem B482147 : Blo 211809 482147 := bstep (se 1 (by rfl) ⟨361610, by rfl⟩ : syracuseStep 482147 = 723221) B723221
theorem B318323 : Blo 211809 318323 := bstep (se 1 (by rfl) ⟨238742, by rfl⟩ : syracuseStep 318323 = 477485) B477485
theorem B318353 : Blo 211809 318353 := bstep (se 2 (by rfl) ⟨119382, by rfl⟩ : syracuseStep 318353 = 238765) B238765
theorem B318371 : Blo 211809 318371 := bstep (se 1 (by rfl) ⟨238778, by rfl⟩ : syracuseStep 318371 = 477557) B477557
theorem B318401 : Blo 211809 318401 := bstep (se 2 (by rfl) ⟨119400, by rfl⟩ : syracuseStep 318401 = 238801) B238801
theorem B318419 : Blo 211809 318419 := bstep (se 1 (by rfl) ⟨238814, by rfl⟩ : syracuseStep 318419 = 477629) B477629
theorem B318449 : Blo 211809 318449 := bstep (se 2 (by rfl) ⟨119418, by rfl⟩ : syracuseStep 318449 = 238837) B238837
theorem B908273 : Blo 211809 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B318467 : Blo 211809 318467 := bstep (se 1 (by rfl) ⟨238850, by rfl⟩ : syracuseStep 318467 = 477701) B477701
theorem B1530893 : Blo 211809 1530893 := bstep (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) B574085
theorem B318497 : Blo 211809 318497 := bstep (se 2 (by rfl) ⟨119436, by rfl⟩ : syracuseStep 318497 = 238873) B238873
theorem B318515 : Blo 211809 318515 := bstep (se 1 (by rfl) ⟨238886, by rfl⟩ : syracuseStep 318515 = 477773) B477773
theorem B318545 : Blo 211809 318545 := bstep (se 2 (by rfl) ⟨119454, by rfl⟩ : syracuseStep 318545 = 238909) B238909
theorem B318563 : Blo 211809 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B482417 : Blo 211809 482417 := bstep (se 2 (by rfl) ⟨180906, by rfl⟩ : syracuseStep 482417 = 361813) B361813
theorem B318593 : Blo 211809 318593 := bstep (se 2 (by rfl) ⟨119472, by rfl⟩ : syracuseStep 318593 = 238945) B238945
theorem B482435 : Blo 211809 482435 := bstep (se 1 (by rfl) ⟨361826, by rfl⟩ : syracuseStep 482435 = 723653) B723653
theorem B318611 : Blo 211809 318611 := bstep (se 1 (by rfl) ⟨238958, by rfl⟩ : syracuseStep 318611 = 477917) B477917
theorem B318641 : Blo 211809 318641 := bstep (se 2 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 318641 = 238981) B238981
theorem B318659 : Blo 211809 318659 := bstep (se 1 (by rfl) ⟨238994, by rfl⟩ : syracuseStep 318659 = 477989) B477989
theorem B318689 : Blo 211809 318689 := bstep (se 2 (by rfl) ⟨119508, by rfl⟩ : syracuseStep 318689 = 239017) B239017
theorem B318707 : Blo 211809 318707 := bstep (se 1 (by rfl) ⟨239030, by rfl⟩ : syracuseStep 318707 = 478061) B478061
theorem B580877 : Blo 211809 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B318737 : Blo 211809 318737 := bstep (se 2 (by rfl) ⟨119526, by rfl⟩ : syracuseStep 318737 = 239053) B239053
theorem B318755 : Blo 211809 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B318785 : Blo 211809 318785 := bstep (se 2 (by rfl) ⟨119544, by rfl⟩ : syracuseStep 318785 = 239089) B239089
theorem B318803 : Blo 211809 318803 := bstep (se 1 (by rfl) ⟨239102, by rfl⟩ : syracuseStep 318803 = 478205) B478205
theorem B318833 : Blo 211809 318833 := bstep (se 2 (by rfl) ⟨119562, by rfl⟩ : syracuseStep 318833 = 239125) B239125
theorem B318851 : Blo 211809 318851 := bstep (se 1 (by rfl) ⟨239138, by rfl⟩ : syracuseStep 318851 = 478277) B478277
theorem B482705 : Blo 211809 482705 := bstep (se 2 (by rfl) ⟨181014, by rfl⟩ : syracuseStep 482705 = 362029) B362029
theorem B318881 : Blo 211809 318881 := bstep (se 2 (by rfl) ⟨119580, by rfl⟩ : syracuseStep 318881 = 239161) B239161
theorem B482723 : Blo 211809 482723 := bstep (se 1 (by rfl) ⟨362042, by rfl⟩ : syracuseStep 482723 = 724085) B724085
theorem B318899 : Blo 211809 318899 := bstep (se 1 (by rfl) ⟨239174, by rfl⟩ : syracuseStep 318899 = 478349) B478349
theorem B318929 : Blo 211809 318929 := bstep (se 2 (by rfl) ⟨119598, by rfl⟩ : syracuseStep 318929 = 239197) B239197
theorem B318947 : Blo 211809 318947 := bstep (se 1 (by rfl) ⟨239210, by rfl⟩ : syracuseStep 318947 = 478421) B478421
theorem B318977 : Blo 211809 318977 := bstep (se 2 (by rfl) ⟨119616, by rfl⟩ : syracuseStep 318977 = 239233) B239233
theorem B318995 : Blo 211809 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B319025 : Blo 211809 319025 := bstep (se 2 (by rfl) ⟨119634, by rfl⟩ : syracuseStep 319025 = 239269) B239269
theorem B319043 : Blo 211809 319043 := bstep (se 1 (by rfl) ⟨239282, by rfl⟩ : syracuseStep 319043 = 478565) B478565
theorem B613955 : Blo 211809 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B319073 : Blo 211809 319073 := bstep (se 2 (by rfl) ⟨119652, by rfl⟩ : syracuseStep 319073 = 239305) B239305
theorem B319091 : Blo 211809 319091 := bstep (se 1 (by rfl) ⟨239318, by rfl⟩ : syracuseStep 319091 = 478637) B478637
theorem B679565 : Blo 211809 679565 := bstep (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) B254837
theorem B319121 : Blo 211809 319121 := bstep (se 2 (by rfl) ⟨119670, by rfl⟩ : syracuseStep 319121 = 239341) B239341
theorem B319139 : Blo 211809 319139 := bstep (se 1 (by rfl) ⟨239354, by rfl⟩ : syracuseStep 319139 = 478709) B478709
theorem B482993 : Blo 211809 482993 := bstep (se 2 (by rfl) ⟨181122, by rfl⟩ : syracuseStep 482993 = 362245) B362245
theorem B319169 : Blo 211809 319169 := bstep (se 2 (by rfl) ⟨119688, by rfl⟩ : syracuseStep 319169 = 239377) B239377
theorem B483011 : Blo 211809 483011 := bstep (se 1 (by rfl) ⟨362258, by rfl⟩ : syracuseStep 483011 = 724517) B724517
theorem B319187 : Blo 211809 319187 := bstep (se 1 (by rfl) ⟨239390, by rfl⟩ : syracuseStep 319187 = 478781) B478781
theorem B319217 : Blo 211809 319217 := bstep (se 2 (by rfl) ⟨119706, by rfl⟩ : syracuseStep 319217 = 239413) B239413
theorem B515825 : Blo 211809 515825 := bstep (se 2 (by rfl) ⟨193434, by rfl⟩ : syracuseStep 515825 = 386869) B386869
theorem B319235 : Blo 211809 319235 := bstep (se 1 (by rfl) ⟨239426, by rfl⟩ : syracuseStep 319235 = 478853) B478853
theorem B319265 : Blo 211809 319265 := bstep (se 2 (by rfl) ⟨119724, by rfl⟩ : syracuseStep 319265 = 239449) B239449
theorem B319283 : Blo 211809 319283 := bstep (se 1 (by rfl) ⟨239462, by rfl⟩ : syracuseStep 319283 = 478925) B478925
theorem B319313 : Blo 211809 319313 := bstep (se 2 (by rfl) ⟨119742, by rfl⟩ : syracuseStep 319313 = 239485) B239485
theorem B319331 : Blo 211809 319331 := bstep (se 1 (by rfl) ⟨239498, by rfl⟩ : syracuseStep 319331 = 478997) B478997
theorem B319361 : Blo 211809 319361 := bstep (se 2 (by rfl) ⟨119760, by rfl⟩ : syracuseStep 319361 = 239521) B239521
theorem B319379 : Blo 211809 319379 := bstep (se 1 (by rfl) ⟨239534, by rfl⟩ : syracuseStep 319379 = 479069) B479069
theorem B319409 : Blo 211809 319409 := bstep (se 2 (by rfl) ⟨119778, by rfl⟩ : syracuseStep 319409 = 239557) B239557
theorem B319427 : Blo 211809 319427 := bstep (se 1 (by rfl) ⟨239570, by rfl⟩ : syracuseStep 319427 = 479141) B479141
theorem B483281 : Blo 211809 483281 := bstep (se 2 (by rfl) ⟨181230, by rfl⟩ : syracuseStep 483281 = 362461) B362461
theorem B319457 : Blo 211809 319457 := bstep (se 2 (by rfl) ⟨119796, by rfl⟩ : syracuseStep 319457 = 239593) B239593
theorem B483299 : Blo 211809 483299 := bstep (se 1 (by rfl) ⟨362474, by rfl⟩ : syracuseStep 483299 = 724949) B724949
theorem B319475 : Blo 211809 319475 := bstep (se 1 (by rfl) ⟨239606, by rfl⟩ : syracuseStep 319475 = 479213) B479213
theorem B319505 : Blo 211809 319505 := bstep (se 2 (by rfl) ⟨119814, by rfl⟩ : syracuseStep 319505 = 239629) B239629
theorem B319523 : Blo 211809 319523 := bstep (se 1 (by rfl) ⟨239642, by rfl⟩ : syracuseStep 319523 = 479285) B479285
theorem B811043 : Blo 211809 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B319553 : Blo 211809 319553 := bstep (se 2 (by rfl) ⟨119832, by rfl⟩ : syracuseStep 319553 = 239665) B239665
theorem B319571 : Blo 211809 319571 := bstep (se 1 (by rfl) ⟨239678, by rfl⟩ : syracuseStep 319571 = 479357) B479357
theorem B319601 : Blo 211809 319601 := bstep (se 2 (by rfl) ⟨119850, by rfl⟩ : syracuseStep 319601 = 239701) B239701
theorem B319619 : Blo 211809 319619 := bstep (se 1 (by rfl) ⟨239714, by rfl⟩ : syracuseStep 319619 = 479429) B479429
theorem B319649 : Blo 211809 319649 := bstep (se 2 (by rfl) ⟨119868, by rfl⟩ : syracuseStep 319649 = 239737) B239737
theorem B319667 : Blo 211809 319667 := bstep (se 1 (by rfl) ⟨239750, by rfl⟩ : syracuseStep 319667 = 479501) B479501
theorem B286913 : Blo 211809 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B319697 : Blo 211809 319697 := bstep (se 2 (by rfl) ⟨119886, by rfl⟩ : syracuseStep 319697 = 239773) B239773
theorem B319715 : Blo 211809 319715 := bstep (se 1 (by rfl) ⟨239786, by rfl⟩ : syracuseStep 319715 = 479573) B479573
theorem B483569 : Blo 211809 483569 := bstep (se 2 (by rfl) ⟨181338, by rfl⟩ : syracuseStep 483569 = 362677) B362677
theorem B319745 : Blo 211809 319745 := bstep (se 2 (by rfl) ⟨119904, by rfl⟩ : syracuseStep 319745 = 239809) B239809
theorem B483587 : Blo 211809 483587 := bstep (se 1 (by rfl) ⟨362690, by rfl⟩ : syracuseStep 483587 = 725381) B725381
theorem B319763 : Blo 211809 319763 := bstep (se 1 (by rfl) ⟨239822, by rfl⟩ : syracuseStep 319763 = 479645) B479645
theorem B319793 : Blo 211809 319793 := bstep (se 2 (by rfl) ⟨119922, by rfl⟩ : syracuseStep 319793 = 239845) B239845
theorem B319811 : Blo 211809 319811 := bstep (se 1 (by rfl) ⟨239858, by rfl⟩ : syracuseStep 319811 = 479717) B479717
theorem B319841 : Blo 211809 319841 := bstep (se 2 (by rfl) ⟨119940, by rfl⟩ : syracuseStep 319841 = 239881) B239881
theorem B319859 : Blo 211809 319859 := bstep (se 1 (by rfl) ⟨239894, by rfl⟩ : syracuseStep 319859 = 479789) B479789
theorem B319889 : Blo 211809 319889 := bstep (se 2 (by rfl) ⟨119958, by rfl⟩ : syracuseStep 319889 = 239917) B239917
theorem B319907 : Blo 211809 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B319937 : Blo 211809 319937 := bstep (se 2 (by rfl) ⟨119976, by rfl⟩ : syracuseStep 319937 = 239953) B239953
theorem B319955 : Blo 211809 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B319985 : Blo 211809 319985 := bstep (se 2 (by rfl) ⟨119994, by rfl⟩ : syracuseStep 319985 = 239989) B239989
theorem B320003 : Blo 211809 320003 := bstep (se 1 (by rfl) ⟨240002, by rfl⟩ : syracuseStep 320003 = 480005) B480005
theorem B483857 : Blo 211809 483857 := bstep (se 2 (by rfl) ⟨181446, by rfl⟩ : syracuseStep 483857 = 362893) B362893
theorem B320033 : Blo 211809 320033 := bstep (se 2 (by rfl) ⟨120012, by rfl⟩ : syracuseStep 320033 = 240025) B240025
theorem B483875 : Blo 211809 483875 := bstep (se 1 (by rfl) ⟨362906, by rfl⟩ : syracuseStep 483875 = 725813) B725813
theorem B320051 : Blo 211809 320051 := bstep (se 1 (by rfl) ⟨240038, by rfl⟩ : syracuseStep 320051 = 480077) B480077
theorem B320081 : Blo 211809 320081 := bstep (se 2 (by rfl) ⟨120030, by rfl⟩ : syracuseStep 320081 = 240061) B240061
theorem B320099 : Blo 211809 320099 := bstep (se 1 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 320099 = 480149) B480149
theorem B320129 : Blo 211809 320129 := bstep (se 2 (by rfl) ⟨120048, by rfl⟩ : syracuseStep 320129 = 240097) B240097
theorem B254611 : Blo 211809 254611 := bstep (se 1 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 254611 = 381917) B381917
theorem B320147 : Blo 211809 320147 := bstep (se 1 (by rfl) ⟨240110, by rfl⟩ : syracuseStep 320147 = 480221) B480221
theorem B320177 : Blo 211809 320177 := bstep (se 2 (by rfl) ⟨120066, by rfl⟩ : syracuseStep 320177 = 240133) B240133
theorem B320195 : Blo 211809 320195 := bstep (se 1 (by rfl) ⟨240146, by rfl⟩ : syracuseStep 320195 = 480293) B480293
theorem B680653 : Blo 211809 680653 := bstep (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) B255245
theorem B320225 : Blo 211809 320225 := bstep (se 2 (by rfl) ⟨120084, by rfl⟩ : syracuseStep 320225 = 240169) B240169
theorem B320243 : Blo 211809 320243 := bstep (se 1 (by rfl) ⟨240182, by rfl⟩ : syracuseStep 320243 = 480365) B480365
theorem B320273 : Blo 211809 320273 := bstep (se 2 (by rfl) ⟨120102, by rfl⟩ : syracuseStep 320273 = 240205) B240205
theorem B320291 : Blo 211809 320291 := bstep (se 1 (by rfl) ⟨240218, by rfl⟩ : syracuseStep 320291 = 480437) B480437
theorem B484145 : Blo 211809 484145 := bstep (se 2 (by rfl) ⟨181554, by rfl⟩ : syracuseStep 484145 = 363109) B363109
theorem B320321 : Blo 211809 320321 := bstep (se 2 (by rfl) ⟨120120, by rfl⟩ : syracuseStep 320321 = 240241) B240241
theorem B484163 : Blo 211809 484163 := bstep (se 1 (by rfl) ⟨363122, by rfl⟩ : syracuseStep 484163 = 726245) B726245
theorem B648013 : Blo 211809 648013 := bstep (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) B243005
theorem B320339 : Blo 211809 320339 := bstep (se 1 (by rfl) ⟨240254, by rfl⟩ : syracuseStep 320339 = 480509) B480509
theorem B320369 : Blo 211809 320369 := bstep (se 2 (by rfl) ⟨120138, by rfl⟩ : syracuseStep 320369 = 240277) B240277
theorem B320387 : Blo 211809 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B320417 : Blo 211809 320417 := bstep (se 2 (by rfl) ⟨120156, by rfl⟩ : syracuseStep 320417 = 240313) B240313
theorem B320435 : Blo 211809 320435 := bstep (se 1 (by rfl) ⟨240326, by rfl⟩ : syracuseStep 320435 = 480653) B480653
theorem B320465 : Blo 211809 320465 := bstep (se 2 (by rfl) ⟨120174, by rfl⟩ : syracuseStep 320465 = 240349) B240349
theorem B320483 : Blo 211809 320483 := bstep (se 1 (by rfl) ⟨240362, by rfl⟩ : syracuseStep 320483 = 480725) B480725
theorem B320513 : Blo 211809 320513 := bstep (se 2 (by rfl) ⟨120192, by rfl⟩ : syracuseStep 320513 = 240385) B240385
theorem B812045 : Blo 211809 812045 := bstep (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) B304517
theorem B320531 : Blo 211809 320531 := bstep (se 1 (by rfl) ⟨240398, by rfl⟩ : syracuseStep 320531 = 480797) B480797
theorem B386083 : Blo 211809 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B320561 : Blo 211809 320561 := bstep (se 2 (by rfl) ⟨120210, by rfl⟩ : syracuseStep 320561 = 240421) B240421
theorem B320579 : Blo 211809 320579 := bstep (se 1 (by rfl) ⟨240434, by rfl⟩ : syracuseStep 320579 = 480869) B480869
theorem B484433 : Blo 211809 484433 := bstep (se 2 (by rfl) ⟨181662, by rfl⟩ : syracuseStep 484433 = 363325) B363325
theorem B320609 : Blo 211809 320609 := bstep (se 2 (by rfl) ⟨120228, by rfl⟩ : syracuseStep 320609 = 240457) B240457
theorem B484451 : Blo 211809 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B320627 : Blo 211809 320627 := bstep (se 1 (by rfl) ⟨240470, by rfl⟩ : syracuseStep 320627 = 480941) B480941
theorem B320657 : Blo 211809 320657 := bstep (se 2 (by rfl) ⟨120246, by rfl⟩ : syracuseStep 320657 = 240493) B240493
theorem B320675 : Blo 211809 320675 := bstep (se 1 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 320675 = 481013) B481013
theorem B320705 : Blo 211809 320705 := bstep (se 2 (by rfl) ⟨120264, by rfl⟩ : syracuseStep 320705 = 240529) B240529
theorem B320723 : Blo 211809 320723 := bstep (se 1 (by rfl) ⟨240542, by rfl⟩ : syracuseStep 320723 = 481085) B481085
theorem B320753 : Blo 211809 320753 := bstep (se 2 (by rfl) ⟨120282, by rfl⟩ : syracuseStep 320753 = 240565) B240565
theorem B320771 : Blo 211809 320771 := bstep (se 1 (by rfl) ⟨240578, by rfl⟩ : syracuseStep 320771 = 481157) B481157
theorem B1631501 : Blo 211809 1631501 := bstep (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) B611813
theorem B320801 : Blo 211809 320801 := bstep (se 2 (by rfl) ⟨120300, by rfl⟩ : syracuseStep 320801 = 240601) B240601
theorem B320819 : Blo 211809 320819 := bstep (se 1 (by rfl) ⟨240614, by rfl⟩ : syracuseStep 320819 = 481229) B481229
theorem B320849 : Blo 211809 320849 := bstep (se 2 (by rfl) ⟨120318, by rfl⟩ : syracuseStep 320849 = 240637) B240637
theorem B320867 : Blo 211809 320867 := bstep (se 1 (by rfl) ⟨240650, by rfl⟩ : syracuseStep 320867 = 481301) B481301
theorem B1074545 : Blo 211809 1074545 := bstep (se 2 (by rfl) ⟨402954, by rfl⟩ : syracuseStep 1074545 = 805909) B805909
theorem B1369457 : Blo 211809 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B484721 : Blo 211809 484721 := bstep (se 2 (by rfl) ⟨181770, by rfl⟩ : syracuseStep 484721 = 363541) B363541
theorem B320897 : Blo 211809 320897 := bstep (se 2 (by rfl) ⟨120336, by rfl⟩ : syracuseStep 320897 = 240673) B240673
theorem B484739 : Blo 211809 484739 := bstep (se 1 (by rfl) ⟨363554, by rfl⟩ : syracuseStep 484739 = 727109) B727109
theorem B320915 : Blo 211809 320915 := bstep (se 1 (by rfl) ⟨240686, by rfl⟩ : syracuseStep 320915 = 481373) B481373
theorem B1369507 : Blo 211809 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B320945 : Blo 211809 320945 := bstep (se 2 (by rfl) ⟨120354, by rfl⟩ : syracuseStep 320945 = 240709) B240709
theorem B320963 : Blo 211809 320963 := bstep (se 1 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 320963 = 481445) B481445
theorem B320993 : Blo 211809 320993 := bstep (se 2 (by rfl) ⟨120372, by rfl⟩ : syracuseStep 320993 = 240745) B240745
theorem B386545 : Blo 211809 386545 := bstep (se 2 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 386545 = 289909) B289909
theorem B321011 : Blo 211809 321011 := bstep (se 1 (by rfl) ⟨240758, by rfl⟩ : syracuseStep 321011 = 481517) B481517
theorem B321041 : Blo 211809 321041 := bstep (se 2 (by rfl) ⟨120390, by rfl⟩ : syracuseStep 321041 = 240781) B240781
theorem B321059 : Blo 211809 321059 := bstep (se 1 (by rfl) ⟨240794, by rfl⟩ : syracuseStep 321059 = 481589) B481589
theorem B321089 : Blo 211809 321089 := bstep (se 2 (by rfl) ⟨120408, by rfl⟩ : syracuseStep 321089 = 240817) B240817
theorem B321107 : Blo 211809 321107 := bstep (se 1 (by rfl) ⟨240830, by rfl⟩ : syracuseStep 321107 = 481661) B481661
theorem B321137 : Blo 211809 321137 := bstep (se 2 (by rfl) ⟨120426, by rfl⟩ : syracuseStep 321137 = 240853) B240853
theorem B321155 : Blo 211809 321155 := bstep (se 1 (by rfl) ⟨240866, by rfl⟩ : syracuseStep 321155 = 481733) B481733
theorem B485009 : Blo 211809 485009 := bstep (se 2 (by rfl) ⟨181878, by rfl⟩ : syracuseStep 485009 = 363757) B363757
theorem B321185 : Blo 211809 321185 := bstep (se 2 (by rfl) ⟨120444, by rfl⟩ : syracuseStep 321185 = 240889) B240889
theorem B485027 : Blo 211809 485027 := bstep (se 1 (by rfl) ⟨363770, by rfl⟩ : syracuseStep 485027 = 727541) B727541
theorem B321203 : Blo 211809 321203 := bstep (se 1 (by rfl) ⟨240902, by rfl⟩ : syracuseStep 321203 = 481805) B481805
theorem B255683 : Blo 211809 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B321233 : Blo 211809 321233 := bstep (se 2 (by rfl) ⟨120462, by rfl⟩ : syracuseStep 321233 = 240925) B240925
theorem B321251 : Blo 211809 321251 := bstep (se 1 (by rfl) ⟨240938, by rfl⟩ : syracuseStep 321251 = 481877) B481877
theorem B321281 : Blo 211809 321281 := bstep (se 2 (by rfl) ⟨120480, by rfl⟩ : syracuseStep 321281 = 240961) B240961
theorem B321299 : Blo 211809 321299 := bstep (se 1 (by rfl) ⟨240974, by rfl⟩ : syracuseStep 321299 = 481949) B481949
theorem B321329 : Blo 211809 321329 := bstep (se 2 (by rfl) ⟨120498, by rfl⟩ : syracuseStep 321329 = 240997) B240997
theorem B321347 : Blo 211809 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B321377 : Blo 211809 321377 := bstep (se 2 (by rfl) ⟨120516, by rfl⟩ : syracuseStep 321377 = 241033) B241033
theorem B321395 : Blo 211809 321395 := bstep (se 1 (by rfl) ⟨241046, by rfl⟩ : syracuseStep 321395 = 482093) B482093
theorem B321425 : Blo 211809 321425 := bstep (se 2 (by rfl) ⟨120534, by rfl⟩ : syracuseStep 321425 = 241069) B241069
theorem B321443 : Blo 211809 321443 := bstep (se 1 (by rfl) ⟨241082, by rfl⟩ : syracuseStep 321443 = 482165) B482165
theorem B485297 : Blo 211809 485297 := bstep (se 2 (by rfl) ⟨181986, by rfl⟩ : syracuseStep 485297 = 363973) B363973
theorem B321473 : Blo 211809 321473 := bstep (se 2 (by rfl) ⟨120552, by rfl⟩ : syracuseStep 321473 = 241105) B241105
theorem B485315 : Blo 211809 485315 := bstep (se 1 (by rfl) ⟨363986, by rfl⟩ : syracuseStep 485315 = 727973) B727973
theorem B321491 : Blo 211809 321491 := bstep (se 1 (by rfl) ⟨241118, by rfl⟩ : syracuseStep 321491 = 482237) B482237
theorem B321521 : Blo 211809 321521 := bstep (se 2 (by rfl) ⟨120570, by rfl⟩ : syracuseStep 321521 = 241141) B241141
theorem B321539 : Blo 211809 321539 := bstep (se 1 (by rfl) ⟨241154, by rfl⟩ : syracuseStep 321539 = 482309) B482309
theorem B321569 : Blo 211809 321569 := bstep (se 2 (by rfl) ⟨120588, by rfl⟩ : syracuseStep 321569 = 241177) B241177
theorem B518179 : Blo 211809 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B321587 : Blo 211809 321587 := bstep (se 1 (by rfl) ⟨241190, by rfl⟩ : syracuseStep 321587 = 482381) B482381
theorem B452675 : Blo 211809 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B321617 : Blo 211809 321617 := bstep (se 2 (by rfl) ⟨120606, by rfl⟩ : syracuseStep 321617 = 241213) B241213
theorem B321635 : Blo 211809 321635 := bstep (se 1 (by rfl) ⟨241226, by rfl⟩ : syracuseStep 321635 = 482453) B482453
theorem B321665 : Blo 211809 321665 := bstep (se 2 (by rfl) ⟨120624, by rfl⟩ : syracuseStep 321665 = 241249) B241249
theorem B321683 : Blo 211809 321683 := bstep (se 1 (by rfl) ⟨241262, by rfl⟩ : syracuseStep 321683 = 482525) B482525
theorem B321713 : Blo 211809 321713 := bstep (se 2 (by rfl) ⟨120642, by rfl⟩ : syracuseStep 321713 = 241285) B241285
theorem B321731 : Blo 211809 321731 := bstep (se 1 (by rfl) ⟨241298, by rfl⟩ : syracuseStep 321731 = 482597) B482597
theorem B321761 : Blo 211809 321761 := bstep (se 2 (by rfl) ⟨120660, by rfl⟩ : syracuseStep 321761 = 241321) B241321
theorem B321779 : Blo 211809 321779 := bstep (se 1 (by rfl) ⟨241334, by rfl⟩ : syracuseStep 321779 = 482669) B482669
theorem B321809 : Blo 211809 321809 := bstep (se 2 (by rfl) ⟨120678, by rfl⟩ : syracuseStep 321809 = 241357) B241357
theorem B321827 : Blo 211809 321827 := bstep (se 1 (by rfl) ⟨241370, by rfl⟩ : syracuseStep 321827 = 482741) B482741
theorem B321857 : Blo 211809 321857 := bstep (se 2 (by rfl) ⟨120696, by rfl⟩ : syracuseStep 321857 = 241393) B241393
theorem B321875 : Blo 211809 321875 := bstep (se 1 (by rfl) ⟨241406, by rfl⟩ : syracuseStep 321875 = 482813) B482813
theorem B715121 : Blo 211809 715121 := bstep (se 2 (by rfl) ⟨268170, by rfl⟩ : syracuseStep 715121 = 536341) B536341
theorem B321905 : Blo 211809 321905 := bstep (se 2 (by rfl) ⟨120714, by rfl⟩ : syracuseStep 321905 = 241429) B241429
theorem B321923 : Blo 211809 321923 := bstep (se 1 (by rfl) ⟨241442, by rfl⟩ : syracuseStep 321923 = 482885) B482885
theorem B321953 : Blo 211809 321953 := bstep (se 2 (by rfl) ⟨120732, by rfl⟩ : syracuseStep 321953 = 241465) B241465
theorem B321971 : Blo 211809 321971 := bstep (se 1 (by rfl) ⟨241478, by rfl⟩ : syracuseStep 321971 = 482957) B482957
theorem B682435 : Blo 211809 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B322001 : Blo 211809 322001 := bstep (se 2 (by rfl) ⟨120750, by rfl⟩ : syracuseStep 322001 = 241501) B241501
theorem B1993187 : Blo 211809 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B911843 : Blo 211809 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B322019 : Blo 211809 322019 := bstep (se 1 (by rfl) ⟨241514, by rfl⟩ : syracuseStep 322019 = 483029) B483029
theorem B1010161 : Blo 211809 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B322049 : Blo 211809 322049 := bstep (se 2 (by rfl) ⟨120768, by rfl⟩ : syracuseStep 322049 = 241537) B241537
theorem B682499 : Blo 211809 682499 := bstep (se 1 (by rfl) ⟨511874, by rfl⟩ : syracuseStep 682499 = 1023749) B1023749
theorem B322067 : Blo 211809 322067 := bstep (se 1 (by rfl) ⟨241550, by rfl⟩ : syracuseStep 322067 = 483101) B483101
theorem B322097 : Blo 211809 322097 := bstep (se 2 (by rfl) ⟨120786, by rfl⟩ : syracuseStep 322097 = 241573) B241573
theorem B322115 : Blo 211809 322115 := bstep (se 1 (by rfl) ⟨241586, by rfl⟩ : syracuseStep 322115 = 483173) B483173
theorem B682577 : Blo 211809 682577 := bstep (se 2 (by rfl) ⟨255966, by rfl⟩ : syracuseStep 682577 = 511933) B511933
theorem B322145 : Blo 211809 322145 := bstep (se 2 (by rfl) ⟨120804, by rfl⟩ : syracuseStep 322145 = 241609) B241609
theorem B322163 : Blo 211809 322163 := bstep (se 1 (by rfl) ⟨241622, by rfl⟩ : syracuseStep 322163 = 483245) B483245
theorem B322193 : Blo 211809 322193 := bstep (se 2 (by rfl) ⟨120822, by rfl⟩ : syracuseStep 322193 = 241645) B241645
theorem B322211 : Blo 211809 322211 := bstep (se 1 (by rfl) ⟨241658, by rfl⟩ : syracuseStep 322211 = 483317) B483317
theorem B322241 : Blo 211809 322241 := bstep (se 2 (by rfl) ⟨120840, by rfl⟩ : syracuseStep 322241 = 241681) B241681
theorem B2714309 : Blo 211809 2714309 := bstep (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) B508933
theorem B322259 : Blo 211809 322259 := bstep (se 1 (by rfl) ⟨241694, by rfl⟩ : syracuseStep 322259 = 483389) B483389
theorem B322289 : Blo 211809 322289 := bstep (se 2 (by rfl) ⟨120858, by rfl⟩ : syracuseStep 322289 = 241717) B241717
theorem B322307 : Blo 211809 322307 := bstep (se 1 (by rfl) ⟨241730, by rfl⟩ : syracuseStep 322307 = 483461) B483461
theorem B322337 : Blo 211809 322337 := bstep (se 2 (by rfl) ⟨120876, by rfl⟩ : syracuseStep 322337 = 241753) B241753
theorem B1076003 : Blo 211809 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B322355 : Blo 211809 322355 := bstep (se 1 (by rfl) ⟨241766, by rfl⟩ : syracuseStep 322355 = 483533) B483533
theorem B322385 : Blo 211809 322385 := bstep (se 2 (by rfl) ⟨120894, by rfl⟩ : syracuseStep 322385 = 241789) B241789
theorem B322403 : Blo 211809 322403 := bstep (se 1 (by rfl) ⟨241802, by rfl⟩ : syracuseStep 322403 = 483605) B483605
theorem B322433 : Blo 211809 322433 := bstep (se 2 (by rfl) ⟨120912, by rfl⟩ : syracuseStep 322433 = 241825) B241825
theorem B387971 : Blo 211809 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B715661 : Blo 211809 715661 := bstep (se 3 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 715661 = 268373) B268373
theorem B322451 : Blo 211809 322451 := bstep (se 1 (by rfl) ⟨241838, by rfl⟩ : syracuseStep 322451 = 483677) B483677
theorem B322481 : Blo 211809 322481 := bstep (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) B241861
theorem B715715 : Blo 211809 715715 := bstep (se 1 (by rfl) ⟨536786, by rfl⟩ : syracuseStep 715715 = 1073573) B1073573
theorem B322499 : Blo 211809 322499 := bstep (se 1 (by rfl) ⟨241874, by rfl⟩ : syracuseStep 322499 = 483749) B483749
theorem B322529 : Blo 211809 322529 := bstep (se 2 (by rfl) ⟨120948, by rfl⟩ : syracuseStep 322529 = 241897) B241897
theorem B322547 : Blo 211809 322547 := bstep (se 1 (by rfl) ⟨241910, by rfl⟩ : syracuseStep 322547 = 483821) B483821
theorem B322577 : Blo 211809 322577 := bstep (se 2 (by rfl) ⟨120966, by rfl⟩ : syracuseStep 322577 = 241933) B241933
theorem B322595 : Blo 211809 322595 := bstep (se 1 (by rfl) ⟨241946, by rfl⟩ : syracuseStep 322595 = 483893) B483893
theorem B322625 : Blo 211809 322625 := bstep (se 2 (by rfl) ⟨120984, by rfl⟩ : syracuseStep 322625 = 241969) B241969
theorem B814157 : Blo 211809 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B322643 : Blo 211809 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B322673 : Blo 211809 322673 := bstep (se 2 (by rfl) ⟨121002, by rfl⟩ : syracuseStep 322673 = 242005) B242005
theorem B322691 : Blo 211809 322691 := bstep (se 1 (by rfl) ⟨242018, by rfl⟩ : syracuseStep 322691 = 484037) B484037
theorem B322721 : Blo 211809 322721 := bstep (se 2 (by rfl) ⟨121020, by rfl⟩ : syracuseStep 322721 = 242041) B242041
theorem B322739 : Blo 211809 322739 := bstep (se 1 (by rfl) ⟨242054, by rfl⟩ : syracuseStep 322739 = 484109) B484109
theorem B715985 : Blo 211809 715985 := bstep (se 2 (by rfl) ⟨268494, by rfl⟩ : syracuseStep 715985 = 536989) B536989
theorem B322769 : Blo 211809 322769 := bstep (se 2 (by rfl) ⟨121038, by rfl⟩ : syracuseStep 322769 = 242077) B242077
theorem B322787 : Blo 211809 322787 := bstep (se 1 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 322787 = 484181) B484181
theorem B322817 : Blo 211809 322817 := bstep (se 2 (by rfl) ⟨121056, by rfl⟩ : syracuseStep 322817 = 242113) B242113
theorem B322835 : Blo 211809 322835 := bstep (se 1 (by rfl) ⟨242126, by rfl⟩ : syracuseStep 322835 = 484253) B484253
theorem B322865 : Blo 211809 322865 := bstep (se 2 (by rfl) ⟨121074, by rfl⟩ : syracuseStep 322865 = 242149) B242149
theorem B322883 : Blo 211809 322883 := bstep (se 1 (by rfl) ⟨242162, by rfl⟩ : syracuseStep 322883 = 484325) B484325
theorem B322913 : Blo 211809 322913 := bstep (se 2 (by rfl) ⟨121092, by rfl⟩ : syracuseStep 322913 = 242185) B242185
theorem B322931 : Blo 211809 322931 := bstep (se 1 (by rfl) ⟨242198, by rfl⟩ : syracuseStep 322931 = 484397) B484397
theorem B322961 : Blo 211809 322961 := bstep (se 2 (by rfl) ⟨121110, by rfl⟩ : syracuseStep 322961 = 242221) B242221
theorem B322979 : Blo 211809 322979 := bstep (se 1 (by rfl) ⟨242234, by rfl⟩ : syracuseStep 322979 = 484469) B484469
theorem B323009 : Blo 211809 323009 := bstep (se 2 (by rfl) ⟨121128, by rfl⟩ : syracuseStep 323009 = 242257) B242257
theorem B323027 : Blo 211809 323027 := bstep (se 1 (by rfl) ⟨242270, by rfl⟩ : syracuseStep 323027 = 484541) B484541
theorem B323057 : Blo 211809 323057 := bstep (se 2 (by rfl) ⟨121146, by rfl⟩ : syracuseStep 323057 = 242293) B242293
theorem B323075 : Blo 211809 323075 := bstep (se 1 (by rfl) ⟨242306, by rfl⟩ : syracuseStep 323075 = 484613) B484613
theorem B323105 : Blo 211809 323105 := bstep (se 2 (by rfl) ⟨121164, by rfl⟩ : syracuseStep 323105 = 242329) B242329
theorem B323123 : Blo 211809 323123 := bstep (se 1 (by rfl) ⟨242342, by rfl⟩ : syracuseStep 323123 = 484685) B484685
theorem B1076813 : Blo 211809 1076813 := bstep (se 3 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 1076813 = 403805) B403805
theorem B323153 : Blo 211809 323153 := bstep (se 2 (by rfl) ⟨121182, by rfl⟩ : syracuseStep 323153 = 242365) B242365
theorem B323171 : Blo 211809 323171 := bstep (se 1 (by rfl) ⟨242378, by rfl⟩ : syracuseStep 323171 = 484757) B484757
theorem B388721 : Blo 211809 388721 := bstep (se 2 (by rfl) ⟨145770, by rfl⟩ : syracuseStep 388721 = 291541) B291541
theorem B323201 : Blo 211809 323201 := bstep (se 2 (by rfl) ⟨121200, by rfl⟩ : syracuseStep 323201 = 242401) B242401
theorem B323219 : Blo 211809 323219 := bstep (se 1 (by rfl) ⟨242414, by rfl⟩ : syracuseStep 323219 = 484829) B484829
theorem B323249 : Blo 211809 323249 := bstep (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) B242437
theorem B323267 : Blo 211809 323267 := bstep (se 1 (by rfl) ⟨242450, by rfl⟩ : syracuseStep 323267 = 484901) B484901
theorem B323297 : Blo 211809 323297 := bstep (se 2 (by rfl) ⟨121236, by rfl⟩ : syracuseStep 323297 = 242473) B242473
theorem B716525 : Blo 211809 716525 := bstep (se 3 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 716525 = 268697) B268697
theorem B323315 : Blo 211809 323315 := bstep (se 1 (by rfl) ⟨242486, by rfl⟩ : syracuseStep 323315 = 484973) B484973
theorem B1371917 : Blo 211809 1371917 := bstep (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) B514469
theorem B323345 : Blo 211809 323345 := bstep (se 2 (by rfl) ⟨121254, by rfl⟩ : syracuseStep 323345 = 242509) B242509
theorem B716579 : Blo 211809 716579 := bstep (se 1 (by rfl) ⟨537434, by rfl⟩ : syracuseStep 716579 = 1074869) B1074869
theorem B323363 : Blo 211809 323363 := bstep (se 1 (by rfl) ⟨242522, by rfl⟩ : syracuseStep 323363 = 485045) B485045
theorem B323393 : Blo 211809 323393 := bstep (se 2 (by rfl) ⟨121272, by rfl⟩ : syracuseStep 323393 = 242545) B242545
theorem B323411 : Blo 211809 323411 := bstep (se 1 (by rfl) ⟨242558, by rfl⟩ : syracuseStep 323411 = 485117) B485117
theorem B814961 : Blo 211809 814961 := bstep (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) B611221
theorem B323441 : Blo 211809 323441 := bstep (se 2 (by rfl) ⟨121290, by rfl⟩ : syracuseStep 323441 = 242581) B242581
theorem B323459 : Blo 211809 323459 := bstep (se 1 (by rfl) ⟨242594, by rfl⟩ : syracuseStep 323459 = 485189) B485189
theorem B323489 : Blo 211809 323489 := bstep (se 2 (by rfl) ⟨121308, by rfl⟩ : syracuseStep 323489 = 242617) B242617
theorem B323507 : Blo 211809 323507 := bstep (se 1 (by rfl) ⟨242630, by rfl⟩ : syracuseStep 323507 = 485261) B485261
theorem B323537 : Blo 211809 323537 := bstep (se 2 (by rfl) ⟨121326, by rfl⟩ : syracuseStep 323537 = 242653) B242653
theorem B323555 : Blo 211809 323555 := bstep (se 1 (by rfl) ⟨242666, by rfl⟩ : syracuseStep 323555 = 485333) B485333
theorem B323585 : Blo 211809 323585 := bstep (se 2 (by rfl) ⟨121344, by rfl⟩ : syracuseStep 323585 = 242689) B242689
theorem B323603 : Blo 211809 323603 := bstep (se 1 (by rfl) ⟨242702, by rfl⟩ : syracuseStep 323603 = 485405) B485405
theorem B454691 : Blo 211809 454691 := bstep (se 1 (by rfl) ⟨341018, by rfl⟩ : syracuseStep 454691 = 682037) B682037
theorem B716849 : Blo 211809 716849 := bstep (se 2 (by rfl) ⟨268818, by rfl⟩ : syracuseStep 716849 = 537637) B537637
theorem B323633 : Blo 211809 323633 := bstep (se 2 (by rfl) ⟨121362, by rfl⟩ : syracuseStep 323633 = 242725) B242725
theorem B323651 : Blo 211809 323651 := bstep (se 1 (by rfl) ⟨242738, by rfl⟩ : syracuseStep 323651 = 485477) B485477
theorem B323681 : Blo 211809 323681 := bstep (se 2 (by rfl) ⟨121380, by rfl⟩ : syracuseStep 323681 = 242761) B242761
theorem B1634417 : Blo 211809 1634417 := bstep (se 2 (by rfl) ⟨612906, by rfl⟩ : syracuseStep 1634417 = 1225813) B1225813
theorem B323699 : Blo 211809 323699 := bstep (se 1 (by rfl) ⟨242774, by rfl⟩ : syracuseStep 323699 = 485549) B485549
theorem B290947 : Blo 211809 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B323843 : Blo 211809 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B2453813 : Blo 211809 2453813 := bstep (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) B230045
theorem B1241413 : Blo 211809 1241413 := bstep (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) B232765
theorem B684497 : Blo 211809 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B291281 : Blo 211809 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B1831409 : Blo 211809 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B815629 : Blo 211809 815629 := bstep (se 3 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 815629 = 305861) B305861
theorem B717389 : Blo 211809 717389 := bstep (se 3 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 717389 = 269021) B269021
theorem B258643 : Blo 211809 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B488035 : Blo 211809 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B717443 : Blo 211809 717443 := bstep (se 1 (by rfl) ⟨538082, by rfl⟩ : syracuseStep 717443 = 1076165) B1076165
theorem B291649 : Blo 211809 291649 := bstep (se 2 (by rfl) ⟨109368, by rfl⟩ : syracuseStep 291649 = 218737) B218737
theorem B324481 : Blo 211809 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B717713 : Blo 211809 717713 := bstep (se 2 (by rfl) ⟨269142, by rfl⟩ : syracuseStep 717713 = 538285) B538285
theorem B685037 : Blo 211809 685037 := bstep (se 3 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 685037 = 256889) B256889
theorem B357473 : Blo 211809 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B357601 : Blo 211809 357601 := bstep (se 2 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 357601 = 268201) B268201
theorem B357635 : Blo 211809 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B455939 : Blo 211809 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B816419 : Blo 211809 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B357763 : Blo 211809 357763 := bstep (se 1 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 357763 = 536645) B536645
theorem B292243 : Blo 211809 292243 := bstep (se 1 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 292243 = 438365) B438365
theorem B718253 : Blo 211809 718253 := bstep (se 3 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 718253 = 269345) B269345
theorem B718307 : Blo 211809 718307 := bstep (se 1 (by rfl) ⟨538730, by rfl⟩ : syracuseStep 718307 = 1077461) B1077461
theorem B357905 : Blo 211809 357905 := bstep (se 2 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 357905 = 268429) B268429
theorem B1734257 : Blo 211809 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B358033 : Blo 211809 358033 := bstep (se 2 (by rfl) ⟨134262, by rfl⟩ : syracuseStep 358033 = 268525) B268525
theorem B358067 : Blo 211809 358067 := bstep (se 1 (by rfl) ⟨268550, by rfl⟩ : syracuseStep 358067 = 537101) B537101
theorem B718577 : Blo 211809 718577 := bstep (se 2 (by rfl) ⟨269466, by rfl⟩ : syracuseStep 718577 = 538933) B538933
theorem B358195 : Blo 211809 358195 := bstep (se 1 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 358195 = 537293) B537293
theorem B456529 : Blo 211809 456529 := bstep (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) B342397
theorem B227171 : Blo 211809 227171 := bstep (se 1 (by rfl) ⟨170378, by rfl⟩ : syracuseStep 227171 = 340757) B340757
theorem B587665 : Blo 211809 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B817073 : Blo 211809 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B358337 : Blo 211809 358337 := bstep (se 2 (by rfl) ⟨134376, by rfl⟩ : syracuseStep 358337 = 268753) B268753
theorem B2455523 : Blo 211809 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B358465 : Blo 211809 358465 := bstep (se 2 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 358465 = 268849) B268849
theorem B915533 : Blo 211809 915533 := bstep (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) B343325
theorem B358499 : Blo 211809 358499 := bstep (se 1 (by rfl) ⟨268874, by rfl⟩ : syracuseStep 358499 = 537749) B537749
theorem B915569 : Blo 211809 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B1308869 : Blo 211809 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B358627 : Blo 211809 358627 := bstep (se 1 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 358627 = 537941) B537941
theorem B719117 : Blo 211809 719117 := bstep (se 3 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 719117 = 269669) B269669
theorem B719171 : Blo 211809 719171 := bstep (se 1 (by rfl) ⟨539378, by rfl⟩ : syracuseStep 719171 = 1078757) B1078757
theorem B358769 : Blo 211809 358769 := bstep (se 2 (by rfl) ⟨134538, by rfl⟩ : syracuseStep 358769 = 269077) B269077
theorem B1571185 : Blo 211809 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B1079729 : Blo 211809 1079729 := bstep (se 2 (by rfl) ⟨404898, by rfl⟩ : syracuseStep 1079729 = 809797) B809797
theorem B358897 : Blo 211809 358897 := bstep (se 2 (by rfl) ⟨134586, by rfl⟩ : syracuseStep 358897 = 269173) B269173
theorem B2521613 : Blo 211809 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B358931 : Blo 211809 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B719441 : Blo 211809 719441 := bstep (se 2 (by rfl) ⟨269790, by rfl⟩ : syracuseStep 719441 = 539581) B539581
theorem B359059 : Blo 211809 359059 := bstep (se 1 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 359059 = 538589) B538589
theorem B490225 : Blo 211809 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B359201 : Blo 211809 359201 := bstep (se 2 (by rfl) ⟨134700, by rfl⟩ : syracuseStep 359201 = 269401) B269401
theorem B359329 : Blo 211809 359329 := bstep (se 2 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 359329 = 269497) B269497
theorem B359363 : Blo 211809 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B359491 : Blo 211809 359491 := bstep (se 1 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 359491 = 539237) B539237
theorem B719981 : Blo 211809 719981 := bstep (se 3 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 719981 = 269993) B269993
theorem B720035 : Blo 211809 720035 := bstep (se 1 (by rfl) ⟨540026, by rfl⟩ : syracuseStep 720035 = 1080053) B1080053
theorem B359633 : Blo 211809 359633 := bstep (se 2 (by rfl) ⟨134862, by rfl⟩ : syracuseStep 359633 = 269725) B269725
theorem B359761 : Blo 211809 359761 := bstep (se 2 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 359761 = 269821) B269821
theorem B818531 : Blo 211809 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B818545 : Blo 211809 818545 := bstep (se 2 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 818545 = 613909) B613909
theorem B359795 : Blo 211809 359795 := bstep (se 1 (by rfl) ⟨269846, by rfl⟩ : syracuseStep 359795 = 539693) B539693
theorem B327073 : Blo 211809 327073 := bstep (se 2 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 327073 = 245305) B245305
theorem B720305 : Blo 211809 720305 := bstep (se 2 (by rfl) ⟨270114, by rfl⟩ : syracuseStep 720305 = 540229) B540229
theorem B359923 : Blo 211809 359923 := bstep (se 1 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 359923 = 539885) B539885
theorem B261667 : Blo 211809 261667 := bstep (se 1 (by rfl) ⟨196250, by rfl⟩ : syracuseStep 261667 = 392501) B392501
theorem B1867333 : Blo 211809 1867333 := bstep (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) B350125
theorem B2719331 : Blo 211809 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B360065 : Blo 211809 360065 := bstep (se 2 (by rfl) ⟨135024, by rfl⟩ : syracuseStep 360065 = 270049) B270049
theorem B1048241 : Blo 211809 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B917219 : Blo 211809 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B360193 : Blo 211809 360193 := bstep (se 2 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 360193 = 270145) B270145
theorem B5603093 : Blo 211809 5603093 := bstep (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) B262645
theorem B360227 : Blo 211809 360227 := bstep (se 1 (by rfl) ⟨270170, by rfl⟩ : syracuseStep 360227 = 540341) B540341
theorem B2817845 : Blo 211809 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B229187 : Blo 211809 229187 := bstep (se 1 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 229187 = 343781) B343781
theorem B1081187 : Blo 211809 1081187 := bstep (se 1 (by rfl) ⟨810890, by rfl⟩ : syracuseStep 1081187 = 1621781) B1621781
theorem B360355 : Blo 211809 360355 := bstep (se 1 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 360355 = 540533) B540533
theorem B720845 : Blo 211809 720845 := bstep (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) B270317
theorem B1212509 : Blo 211809 1212509 := bstep (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) B454691
theorem B459083 : Blo 211809 459083 := bstep (se 1 (by rfl) ⟨344312, by rfl⟩ : syracuseStep 459083 = 688625) B688625
theorem B721331 : Blo 211809 721331 := bstep (se 1 (by rfl) ⟨540998, by rfl⟩ : syracuseStep 721331 = 1081997) B1081997
theorem B360983 : Blo 211809 360983 := bstep (se 1 (by rfl) ⟨270737, by rfl⟩ : syracuseStep 360983 = 541475) B541475
theorem B2458187 : Blo 211809 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B1049219 : Blo 211809 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B361111 : Blo 211809 361111 := bstep (se 1 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 361111 = 541667) B541667
theorem B721601 : Blo 211809 721601 := bstep (se 2 (by rfl) ⟨270600, by rfl⟩ : syracuseStep 721601 = 541201) B541201
theorem B1541015 : Blo 211809 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B722141 : Blo 211809 722141 := bstep (se 3 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 722141 = 270803) B270803
theorem B361739 : Blo 211809 361739 := bstep (se 1 (by rfl) ⟨271304, by rfl⟩ : syracuseStep 361739 = 542609) B542609
theorem B361867 : Blo 211809 361867 := bstep (se 1 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 361867 = 542801) B542801
theorem B918935 : Blo 211809 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B362009 : Blo 211809 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B460313 : Blo 211809 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B362137 : Blo 211809 362137 := bstep (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) B271603
theorem B6620869 : Blo 211809 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B460723 : Blo 211809 460723 := bstep (se 1 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 460723 = 691085) B691085
theorem B690227 : Blo 211809 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B493697 : Blo 211809 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B362711 : Blo 211809 362711 := bstep (se 1 (by rfl) ⟨272033, by rfl⟩ : syracuseStep 362711 = 544067) B544067
theorem B723275 : Blo 211809 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B362839 : Blo 211809 362839 := bstep (se 1 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 362839 = 544259) B544259
theorem B1083779 : Blo 211809 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B920129 : Blo 211809 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B723545 : Blo 211809 723545 := bstep (se 2 (by rfl) ⟨271329, by rfl⟩ : syracuseStep 723545 = 542659) B542659
theorem B4983389 : Blo 211809 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B1215107 : Blo 211809 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B690905 : Blo 211809 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B363467 : Blo 211809 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B363595 : Blo 211809 363595 := bstep (se 1 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 363595 = 545393) B545393
theorem B1838173 : Blo 211809 1838173 := bstep (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) B689315
theorem B1379429 : Blo 211809 1379429 := bstep (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) B258643
theorem B363671 : Blo 211809 363671 := bstep (se 1 (by rfl) ⟨272753, by rfl⟩ : syracuseStep 363671 = 545507) B545507
theorem B363737 : Blo 211809 363737 := bstep (se 2 (by rfl) ⟨136401, by rfl⟩ : syracuseStep 363737 = 272803) B272803
theorem B724247 : Blo 211809 724247 := bstep (se 1 (by rfl) ⟨543185, by rfl⟩ : syracuseStep 724247 = 1086371) B1086371
theorem B1346881 : Blo 211809 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B363865 : Blo 211809 363865 := bstep (se 2 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 363865 = 272899) B272899
theorem B495065 : Blo 211809 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B1379915 : Blo 211809 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B724787 : Blo 211809 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B921395 : Blo 211809 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B921547 : Blo 211809 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B921617 : Blo 211809 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B725057 : Blo 211809 725057 := bstep (se 2 (by rfl) ⟨271896, by rfl⟩ : syracuseStep 725057 = 543793) B543793
theorem B5279813 : Blo 211809 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B4624685 : Blo 211809 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B430451 : Blo 211809 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B3543587 : Blo 211809 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B725597 : Blo 211809 725597 := bstep (se 3 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 725597 = 272099) B272099
theorem B1020595 : Blo 211809 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B1840229 : Blo 211809 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B726731 : Blo 211809 726731 := bstep (se 1 (by rfl) ⟨545048, by rfl⟩ : syracuseStep 726731 = 1090097) B1090097
theorem B727001 : Blo 211809 727001 := bstep (se 2 (by rfl) ⟨272625, by rfl⟩ : syracuseStep 727001 = 545251) B545251
theorem B1087505 : Blo 211809 1087505 := bstep (se 2 (by rfl) ⟨407814, by rfl⟩ : syracuseStep 1087505 = 815629) B815629
theorem B268363 : Blo 211809 268363 := bstep (se 1 (by rfl) ⟨201272, by rfl⟩ : syracuseStep 268363 = 402545) B402545
theorem B1087667 : Blo 211809 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B1382579 : Blo 211809 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B2038193 : Blo 211809 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B432641 : Blo 211809 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B727703 : Blo 211809 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B2923381 : Blo 211809 2923381 := bstep (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) B274067
theorem B269335 : Blo 211809 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B1809539 : Blo 211809 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B728243 : Blo 211809 728243 := bstep (se 1 (by rfl) ⟨546182, by rfl⟩ : syracuseStep 728243 = 1092365) B1092365
theorem B270155 : Blo 211809 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B1023961 : Blo 211809 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B1089611 : Blo 211809 1089611 := bstep (se 1 (by rfl) ⟨817208, by rfl⟩ : syracuseStep 1089611 = 1634417) B1634417
theorem B1220939 : Blo 211809 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B270859 : Blo 211809 270859 := bstep (se 1 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 270859 = 406289) B406289
theorem B1548977 : Blo 211809 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B238315 : Blo 211809 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B271127 : Blo 211809 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B402241 : Blo 211809 402241 := bstep (se 2 (by rfl) ⟨150840, by rfl⟩ : syracuseStep 402241 = 301681) B301681
theorem B238423 : Blo 211809 238423 := bstep (se 1 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 238423 = 357635) B357635
theorem B303959 : Blo 211809 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B238603 : Blo 211809 238603 := bstep (se 1 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 238603 = 357905) B357905
theorem B926765 : Blo 211809 926765 := bstep (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) B347537
theorem B238711 : Blo 211809 238711 := bstep (se 1 (by rfl) ⟨179033, by rfl⟩ : syracuseStep 238711 = 358067) B358067
theorem B402583 : Blo 211809 402583 := bstep (se 1 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 402583 = 603875) B603875
theorem B238891 : Blo 211809 238891 := bstep (se 1 (by rfl) ⟨179168, by rfl⟩ : syracuseStep 238891 = 358337) B358337
theorem B402803 : Blo 211809 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B238999 : Blo 211809 238999 := bstep (se 1 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 238999 = 358499) B358499
theorem B271831 : Blo 211809 271831 := bstep (se 1 (by rfl) ⟨203873, by rfl⟩ : syracuseStep 271831 = 407747) B407747
theorem B1811929 : Blo 211809 1811929 := bstep (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) B1358947
theorem B239179 : Blo 211809 239179 := bstep (se 1 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 239179 = 358769) B358769
theorem B403031 : Blo 211809 403031 := bstep (se 1 (by rfl) ⟨302273, by rfl⟩ : syracuseStep 403031 = 604547) B604547
theorem B1681075 : Blo 211809 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B239287 : Blo 211809 239287 := bstep (se 1 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 239287 = 358931) B358931
theorem B1091393 : Blo 211809 1091393 := bstep (se 2 (by rfl) ⟨409272, by rfl⟩ : syracuseStep 1091393 = 818545) B818545
theorem B403289 : Blo 211809 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B239467 : Blo 211809 239467 := bstep (se 1 (by rfl) ⟨179600, by rfl⟩ : syracuseStep 239467 = 359201) B359201
theorem B436097 : Blo 211809 436097 := bstep (se 2 (by rfl) ⟨163536, by rfl⟩ : syracuseStep 436097 = 327073) B327073
theorem B239575 : Blo 211809 239575 := bstep (se 1 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 239575 = 359363) B359363
theorem B239755 : Blo 211809 239755 := bstep (se 1 (by rfl) ⟨179816, by rfl⟩ : syracuseStep 239755 = 359633) B359633
theorem B403699 : Blo 211809 403699 := bstep (se 1 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 403699 = 605549) B605549
theorem B239863 : Blo 211809 239863 := bstep (se 1 (by rfl) ⟨179897, by rfl⟩ : syracuseStep 239863 = 359795) B359795
theorem B1812887 : Blo 211809 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B240043 : Blo 211809 240043 := bstep (se 1 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 240043 = 360065) B360065
theorem B698827 : Blo 211809 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B16198157 : Blo 211809 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B240151 : Blo 211809 240151 := bstep (se 1 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 240151 = 360227) B360227
theorem B1878563 : Blo 211809 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B240331 : Blo 211809 240331 := bstep (se 1 (by rfl) ⟨180248, by rfl⟩ : syracuseStep 240331 = 360497) B360497
theorem B404185 : Blo 211809 404185 := bstep (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) B303139
theorem B1813265 : Blo 211809 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B240439 : Blo 211809 240439 := bstep (se 1 (by rfl) ⟨180329, by rfl⟩ : syracuseStep 240439 = 360659) B360659
theorem B273227 : Blo 211809 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B240619 : Blo 211809 240619 := bstep (se 1 (by rfl) ⟨180464, by rfl⟩ : syracuseStep 240619 = 360929) B360929
theorem B240727 : Blo 211809 240727 := bstep (se 1 (by rfl) ⟨180545, by rfl⟩ : syracuseStep 240727 = 361091) B361091
theorem B765101 : Blo 211809 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B404747 : Blo 211809 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B240907 : Blo 211809 240907 := bstep (se 1 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 240907 = 361361) B361361
theorem B863581 : Blo 211809 863581 := bstep (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) B323843
theorem B241015 : Blo 211809 241015 := bstep (se 1 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 241015 = 361523) B361523
theorem B404929 : Blo 211809 404929 := bstep (se 2 (by rfl) ⟨151848, by rfl⟩ : syracuseStep 404929 = 303697) B303697
theorem B339481 : Blo 211809 339481 := bstep (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) B254611
theorem B241195 : Blo 211809 241195 := bstep (se 1 (by rfl) ⟨180896, by rfl⟩ : syracuseStep 241195 = 361793) B361793
theorem B1945133 : Blo 211809 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B929411 : Blo 211809 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B241303 : Blo 211809 241303 := bstep (se 1 (by rfl) ⟨180977, by rfl⟩ : syracuseStep 241303 = 361955) B361955
theorem B306841 : Blo 211809 306841 := bstep (se 2 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 306841 = 230131) B230131
theorem B864017 : Blo 211809 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B241483 : Blo 211809 241483 := bstep (se 1 (by rfl) ⟨181112, by rfl⟩ : syracuseStep 241483 = 362225) B362225
theorem B1650563 : Blo 211809 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B274315 : Blo 211809 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B241591 : Blo 211809 241591 := bstep (se 1 (by rfl) ⟨181193, by rfl⟩ : syracuseStep 241591 = 362387) B362387
theorem B241751 : Blo 211809 241751 := bstep (se 1 (by rfl) ⟨181313, by rfl⟩ : syracuseStep 241751 = 362627) B362627
theorem B536665 : Blo 211809 536665 := bstep (se 2 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 536665 = 402499) B402499
theorem B241771 : Blo 211809 241771 := bstep (se 1 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 241771 = 362657) B362657
theorem B405643 : Blo 211809 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B405719 : Blo 211809 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B241879 : Blo 211809 241879 := bstep (se 1 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 241879 = 362819) B362819
theorem B766169 : Blo 211809 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B242059 : Blo 211809 242059 := bstep (se 1 (by rfl) ⟨181544, by rfl⟩ : syracuseStep 242059 = 363089) B363089
theorem B242167 : Blo 211809 242167 := bstep (se 1 (by rfl) ⟨181625, by rfl⟩ : syracuseStep 242167 = 363251) B363251
theorem B1749509 : Blo 211809 1749509 := bstep (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) B328033
theorem B1094219 : Blo 211809 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B242347 : Blo 211809 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B242455 : Blo 211809 242455 := bstep (se 1 (by rfl) ⟨181841, by rfl⟩ : syracuseStep 242455 = 363683) B363683
theorem B406387 : Blo 211809 406387 := bstep (se 1 (by rfl) ⟨304790, by rfl⟩ : syracuseStep 406387 = 609581) B609581
theorem B1618865 : Blo 211809 1618865 := bstep (se 2 (by rfl) ⟨607074, by rfl⟩ : syracuseStep 1618865 = 1214149) B1214149
theorem B242635 : Blo 211809 242635 := bstep (se 1 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 242635 = 363953) B363953
theorem B242743 : Blo 211809 242743 := bstep (se 1 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 242743 = 364115) B364115
theorem B4600901 : Blo 211809 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B406615 : Blo 211809 406615 := bstep (se 1 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 406615 = 609923) B609923
theorem B537779 : Blo 211809 537779 := bstep (se 1 (by rfl) ⟨403334, by rfl⟩ : syracuseStep 537779 = 806669) B806669
theorem B406721 : Blo 211809 406721 := bstep (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) B305041
theorem B406873 : Blo 211809 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B1619351 : Blo 211809 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B538073 : Blo 211809 538073 := bstep (se 2 (by rfl) ⟨201777, by rfl⟩ : syracuseStep 538073 = 403555) B403555
theorem B1226285 : Blo 211809 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B3323693 : Blo 211809 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B15677509 : Blo 211809 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B768203 : Blo 211809 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B538969 : Blo 211809 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B342551 : Blo 211809 342551 := bstep (se 1 (by rfl) ⟨256913, by rfl⟩ : syracuseStep 342551 = 513827) B513827
theorem B408179 : Blo 211809 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B408331 : Blo 211809 408331 := bstep (se 1 (by rfl) ⟨306248, by rfl⟩ : syracuseStep 408331 = 612497) B612497
theorem B768791 : Blo 211809 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B604979 : Blo 211809 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B211819 : Blo 211809 211819 := bstep (se 1 (by rfl) ⟨158864, by rfl⟩ : syracuseStep 211819 = 317729) B317729
theorem B211831 : Blo 211809 211831 := bstep (se 1 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 211831 = 317747) B317747
theorem B211851 : Blo 211809 211851 := bstep (se 1 (by rfl) ⟨158888, by rfl⟩ : syracuseStep 211851 = 317777) B317777
theorem B211863 : Blo 211809 211863 := bstep (se 1 (by rfl) ⟨158897, by rfl⟩ : syracuseStep 211863 = 317795) B317795
theorem B211883 : Blo 211809 211883 := bstep (se 1 (by rfl) ⟨158912, by rfl⟩ : syracuseStep 211883 = 317825) B317825
theorem B211895 : Blo 211809 211895 := bstep (se 1 (by rfl) ⟨158921, by rfl⟩ : syracuseStep 211895 = 317843) B317843
theorem B211915 : Blo 211809 211915 := bstep (se 1 (by rfl) ⟨158936, by rfl⟩ : syracuseStep 211915 = 317873) B317873
theorem B211927 : Blo 211809 211927 := bstep (se 1 (by rfl) ⟨158945, by rfl⟩ : syracuseStep 211927 = 317891) B317891
theorem B211947 : Blo 211809 211947 := bstep (se 1 (by rfl) ⟨158960, by rfl⟩ : syracuseStep 211947 = 317921) B317921
theorem B211959 : Blo 211809 211959 := bstep (se 1 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 211959 = 317939) B317939
theorem B211979 : Blo 211809 211979 := bstep (se 1 (by rfl) ⟨158984, by rfl⟩ : syracuseStep 211979 = 317969) B317969
theorem B211991 : Blo 211809 211991 := bstep (se 1 (by rfl) ⟨158993, by rfl⟩ : syracuseStep 211991 = 317987) B317987
theorem B605207 : Blo 211809 605207 := bstep (se 1 (by rfl) ⟨453905, by rfl⟩ : syracuseStep 605207 = 907811) B907811
theorem B343063 : Blo 211809 343063 := bstep (se 1 (by rfl) ⟨257297, by rfl⟩ : syracuseStep 343063 = 514595) B514595
theorem B212011 : Blo 211809 212011 := bstep (se 1 (by rfl) ⟨159008, by rfl⟩ : syracuseStep 212011 = 318017) B318017
theorem B212023 : Blo 211809 212023 := bstep (se 1 (by rfl) ⟨159017, by rfl⟩ : syracuseStep 212023 = 318035) B318035
theorem B212043 : Blo 211809 212043 := bstep (se 1 (by rfl) ⟨159032, by rfl⟩ : syracuseStep 212043 = 318065) B318065
theorem B539723 : Blo 211809 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B212055 : Blo 211809 212055 := bstep (se 1 (by rfl) ⟨159041, by rfl⟩ : syracuseStep 212055 = 318083) B318083
theorem B408665 : Blo 211809 408665 := bstep (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) B306499
theorem B212075 : Blo 211809 212075 := bstep (se 1 (by rfl) ⟨159056, by rfl⟩ : syracuseStep 212075 = 318113) B318113
theorem B212087 : Blo 211809 212087 := bstep (se 1 (by rfl) ⟨159065, by rfl⟩ : syracuseStep 212087 = 318131) B318131
theorem B212107 : Blo 211809 212107 := bstep (se 1 (by rfl) ⟨159080, by rfl⟩ : syracuseStep 212107 = 318161) B318161
theorem B212119 : Blo 211809 212119 := bstep (se 1 (by rfl) ⟨159089, by rfl⟩ : syracuseStep 212119 = 318179) B318179
theorem B212139 : Blo 211809 212139 := bstep (se 1 (by rfl) ⟨159104, by rfl⟩ : syracuseStep 212139 = 318209) B318209
theorem B212151 : Blo 211809 212151 := bstep (se 1 (by rfl) ⟨159113, by rfl⟩ : syracuseStep 212151 = 318227) B318227
theorem B212171 : Blo 211809 212171 := bstep (se 1 (by rfl) ⟨159128, by rfl⟩ : syracuseStep 212171 = 318257) B318257
theorem B212183 : Blo 211809 212183 := bstep (se 1 (by rfl) ⟨159137, by rfl⟩ : syracuseStep 212183 = 318275) B318275
theorem B212203 : Blo 211809 212203 := bstep (se 1 (by rfl) ⟨159152, by rfl⟩ : syracuseStep 212203 = 318305) B318305
theorem B212215 : Blo 211809 212215 := bstep (se 1 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 212215 = 318323) B318323
theorem B212235 : Blo 211809 212235 := bstep (se 1 (by rfl) ⟨159176, by rfl⟩ : syracuseStep 212235 = 318353) B318353
theorem B212247 : Blo 211809 212247 := bstep (se 1 (by rfl) ⟨159185, by rfl⟩ : syracuseStep 212247 = 318371) B318371
theorem B212267 : Blo 211809 212267 := bstep (se 1 (by rfl) ⟨159200, by rfl⟩ : syracuseStep 212267 = 318401) B318401
theorem B212279 : Blo 211809 212279 := bstep (se 1 (by rfl) ⟨159209, by rfl⟩ : syracuseStep 212279 = 318419) B318419
theorem B212299 : Blo 211809 212299 := bstep (se 1 (by rfl) ⟨159224, by rfl⟩ : syracuseStep 212299 = 318449) B318449
theorem B605515 : Blo 211809 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B212311 : Blo 211809 212311 := bstep (se 1 (by rfl) ⟨159233, by rfl⟩ : syracuseStep 212311 = 318467) B318467
theorem B212331 : Blo 211809 212331 := bstep (se 1 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 212331 = 318497) B318497
theorem B212343 : Blo 211809 212343 := bstep (se 1 (by rfl) ⟨159257, by rfl⟩ : syracuseStep 212343 = 318515) B318515
theorem B212363 : Blo 211809 212363 := bstep (se 1 (by rfl) ⟨159272, by rfl⟩ : syracuseStep 212363 = 318545) B318545
theorem B212375 : Blo 211809 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B212395 : Blo 211809 212395 := bstep (se 1 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 212395 = 318593) B318593
theorem B212407 : Blo 211809 212407 := bstep (se 1 (by rfl) ⟨159305, by rfl⟩ : syracuseStep 212407 = 318611) B318611
theorem B212427 : Blo 211809 212427 := bstep (se 1 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 212427 = 318641) B318641
theorem B212439 : Blo 211809 212439 := bstep (se 1 (by rfl) ⟨159329, by rfl⟩ : syracuseStep 212439 = 318659) B318659
theorem B212459 : Blo 211809 212459 := bstep (se 1 (by rfl) ⟨159344, by rfl⟩ : syracuseStep 212459 = 318689) B318689
theorem B212471 : Blo 211809 212471 := bstep (se 1 (by rfl) ⟨159353, by rfl⟩ : syracuseStep 212471 = 318707) B318707
theorem B212491 : Blo 211809 212491 := bstep (se 1 (by rfl) ⟨159368, by rfl⟩ : syracuseStep 212491 = 318737) B318737
theorem B212503 : Blo 211809 212503 := bstep (se 1 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 212503 = 318755) B318755
theorem B212523 : Blo 211809 212523 := bstep (se 1 (by rfl) ⟨159392, by rfl⟩ : syracuseStep 212523 = 318785) B318785
theorem B212535 : Blo 211809 212535 := bstep (se 1 (by rfl) ⟨159401, by rfl⟩ : syracuseStep 212535 = 318803) B318803
theorem B212555 : Blo 211809 212555 := bstep (se 1 (by rfl) ⟨159416, by rfl⟩ : syracuseStep 212555 = 318833) B318833
theorem B212567 : Blo 211809 212567 := bstep (se 1 (by rfl) ⟨159425, by rfl⟩ : syracuseStep 212567 = 318851) B318851
theorem B605789 : Blo 211809 605789 := bstep (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) B227171
theorem B212587 : Blo 211809 212587 := bstep (se 1 (by rfl) ⟨159440, by rfl⟩ : syracuseStep 212587 = 318881) B318881
theorem B212599 : Blo 211809 212599 := bstep (se 1 (by rfl) ⟨159449, by rfl⟩ : syracuseStep 212599 = 318899) B318899
theorem B212619 : Blo 211809 212619 := bstep (se 1 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 212619 = 318929) B318929
theorem B212631 : Blo 211809 212631 := bstep (se 1 (by rfl) ⟨159473, by rfl⟩ : syracuseStep 212631 = 318947) B318947
theorem B212651 : Blo 211809 212651 := bstep (se 1 (by rfl) ⟨159488, by rfl⟩ : syracuseStep 212651 = 318977) B318977
theorem B212663 : Blo 211809 212663 := bstep (se 1 (by rfl) ⟨159497, by rfl⟩ : syracuseStep 212663 = 318995) B318995
theorem B212683 : Blo 211809 212683 := bstep (se 1 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 212683 = 319025) B319025
theorem B212695 : Blo 211809 212695 := bstep (se 1 (by rfl) ⟨159521, by rfl⟩ : syracuseStep 212695 = 319043) B319043
theorem B409303 : Blo 211809 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B212715 : Blo 211809 212715 := bstep (se 1 (by rfl) ⟨159536, by rfl⟩ : syracuseStep 212715 = 319073) B319073
theorem B212727 : Blo 211809 212727 := bstep (se 1 (by rfl) ⟨159545, by rfl⟩ : syracuseStep 212727 = 319091) B319091
theorem B212747 : Blo 211809 212747 := bstep (se 1 (by rfl) ⟨159560, by rfl⟩ : syracuseStep 212747 = 319121) B319121
theorem B212759 : Blo 211809 212759 := bstep (se 1 (by rfl) ⟨159569, by rfl⟩ : syracuseStep 212759 = 319139) B319139
theorem B212779 : Blo 211809 212779 := bstep (se 1 (by rfl) ⟨159584, by rfl⟩ : syracuseStep 212779 = 319169) B319169
theorem B212791 : Blo 211809 212791 := bstep (se 1 (by rfl) ⟨159593, by rfl⟩ : syracuseStep 212791 = 319187) B319187
theorem B212811 : Blo 211809 212811 := bstep (se 1 (by rfl) ⟨159608, by rfl⟩ : syracuseStep 212811 = 319217) B319217
theorem B343883 : Blo 211809 343883 := bstep (se 1 (by rfl) ⟨257912, by rfl⟩ : syracuseStep 343883 = 515825) B515825
theorem B212823 : Blo 211809 212823 := bstep (se 1 (by rfl) ⟨159617, by rfl⟩ : syracuseStep 212823 = 319235) B319235
theorem B212843 : Blo 211809 212843 := bstep (se 1 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 212843 = 319265) B319265
theorem B212855 : Blo 211809 212855 := bstep (se 1 (by rfl) ⟨159641, by rfl⟩ : syracuseStep 212855 = 319283) B319283
theorem B212875 : Blo 211809 212875 := bstep (se 1 (by rfl) ⟨159656, by rfl⟩ : syracuseStep 212875 = 319313) B319313
theorem B1359767 : Blo 211809 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B212887 : Blo 211809 212887 := bstep (se 1 (by rfl) ⟨159665, by rfl⟩ : syracuseStep 212887 = 319331) B319331
theorem B212907 : Blo 211809 212907 := bstep (se 1 (by rfl) ⟨159680, by rfl⟩ : syracuseStep 212907 = 319361) B319361
theorem B212919 : Blo 211809 212919 := bstep (se 1 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 212919 = 319379) B319379
theorem B212939 : Blo 211809 212939 := bstep (se 1 (by rfl) ⟨159704, by rfl⟩ : syracuseStep 212939 = 319409) B319409
theorem B212951 : Blo 211809 212951 := bstep (se 1 (by rfl) ⟨159713, by rfl⟩ : syracuseStep 212951 = 319427) B319427
theorem B212971 : Blo 211809 212971 := bstep (se 1 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 212971 = 319457) B319457
theorem B212983 : Blo 211809 212983 := bstep (se 1 (by rfl) ⟨159737, by rfl⟩ : syracuseStep 212983 = 319475) B319475
theorem B213003 : Blo 211809 213003 := bstep (se 1 (by rfl) ⟨159752, by rfl⟩ : syracuseStep 213003 = 319505) B319505
theorem B213015 : Blo 211809 213015 := bstep (se 1 (by rfl) ⟨159761, by rfl⟩ : syracuseStep 213015 = 319523) B319523
theorem B540695 : Blo 211809 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B213035 : Blo 211809 213035 := bstep (se 1 (by rfl) ⟨159776, by rfl⟩ : syracuseStep 213035 = 319553) B319553
theorem B213047 : Blo 211809 213047 := bstep (se 1 (by rfl) ⟨159785, by rfl⟩ : syracuseStep 213047 = 319571) B319571
theorem B213067 : Blo 211809 213067 := bstep (se 1 (by rfl) ⟨159800, by rfl⟩ : syracuseStep 213067 = 319601) B319601
theorem B213079 : Blo 211809 213079 := bstep (se 1 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 213079 = 319619) B319619
theorem B213099 : Blo 211809 213099 := bstep (se 1 (by rfl) ⟨159824, by rfl⟩ : syracuseStep 213099 = 319649) B319649
theorem B213111 : Blo 211809 213111 := bstep (se 1 (by rfl) ⟨159833, by rfl⟩ : syracuseStep 213111 = 319667) B319667
theorem B213131 : Blo 211809 213131 := bstep (se 1 (by rfl) ⟨159848, by rfl⟩ : syracuseStep 213131 = 319697) B319697
theorem B213143 : Blo 211809 213143 := bstep (se 1 (by rfl) ⟨159857, by rfl⟩ : syracuseStep 213143 = 319715) B319715
theorem B213163 : Blo 211809 213163 := bstep (se 1 (by rfl) ⟨159872, by rfl⟩ : syracuseStep 213163 = 319745) B319745
theorem B213175 : Blo 211809 213175 := bstep (se 1 (by rfl) ⟨159881, by rfl⟩ : syracuseStep 213175 = 319763) B319763
theorem B213195 : Blo 211809 213195 := bstep (se 1 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 213195 = 319793) B319793
theorem B213207 : Blo 211809 213207 := bstep (se 1 (by rfl) ⟨159905, by rfl⟩ : syracuseStep 213207 = 319811) B319811
theorem B213227 : Blo 211809 213227 := bstep (se 1 (by rfl) ⟨159920, by rfl⟩ : syracuseStep 213227 = 319841) B319841
theorem B213239 : Blo 211809 213239 := bstep (se 1 (by rfl) ⟨159929, by rfl⟩ : syracuseStep 213239 = 319859) B319859
theorem B213259 : Blo 211809 213259 := bstep (se 1 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 213259 = 319889) B319889
theorem B213271 : Blo 211809 213271 := bstep (se 1 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 213271 = 319907) B319907
theorem B213291 : Blo 211809 213291 := bstep (se 1 (by rfl) ⟨159968, by rfl⟩ : syracuseStep 213291 = 319937) B319937
theorem B213303 : Blo 211809 213303 := bstep (se 1 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 213303 = 319955) B319955
theorem B3916097 : Blo 211809 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B213323 : Blo 211809 213323 := bstep (se 1 (by rfl) ⟨159992, by rfl⟩ : syracuseStep 213323 = 319985) B319985
theorem B213335 : Blo 211809 213335 := bstep (se 1 (by rfl) ⟨160001, by rfl⟩ : syracuseStep 213335 = 320003) B320003
theorem B213355 : Blo 211809 213355 := bstep (se 1 (by rfl) ⟨160016, by rfl⟩ : syracuseStep 213355 = 320033) B320033
theorem B213367 : Blo 211809 213367 := bstep (se 1 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 213367 = 320051) B320051
theorem B213387 : Blo 211809 213387 := bstep (se 1 (by rfl) ⟨160040, by rfl⟩ : syracuseStep 213387 = 320081) B320081
theorem B213399 : Blo 211809 213399 := bstep (se 1 (by rfl) ⟨160049, by rfl⟩ : syracuseStep 213399 = 320099) B320099
theorem B213419 : Blo 211809 213419 := bstep (se 1 (by rfl) ⟨160064, by rfl⟩ : syracuseStep 213419 = 320129) B320129
theorem B213431 : Blo 211809 213431 := bstep (se 1 (by rfl) ⟨160073, by rfl⟩ : syracuseStep 213431 = 320147) B320147
theorem B213451 : Blo 211809 213451 := bstep (se 1 (by rfl) ⟨160088, by rfl⟩ : syracuseStep 213451 = 320177) B320177
theorem B213463 : Blo 211809 213463 := bstep (se 1 (by rfl) ⟨160097, by rfl⟩ : syracuseStep 213463 = 320195) B320195
theorem B213483 : Blo 211809 213483 := bstep (se 1 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 213483 = 320225) B320225
theorem B213495 : Blo 211809 213495 := bstep (se 1 (by rfl) ⟨160121, by rfl⟩ : syracuseStep 213495 = 320243) B320243
theorem B213515 : Blo 211809 213515 := bstep (se 1 (by rfl) ⟨160136, by rfl⟩ : syracuseStep 213515 = 320273) B320273
theorem B213527 : Blo 211809 213527 := bstep (se 1 (by rfl) ⟨160145, by rfl⟩ : syracuseStep 213527 = 320291) B320291
theorem B213547 : Blo 211809 213547 := bstep (se 1 (by rfl) ⟨160160, by rfl⟩ : syracuseStep 213547 = 320321) B320321
theorem B213559 : Blo 211809 213559 := bstep (se 1 (by rfl) ⟨160169, by rfl⟩ : syracuseStep 213559 = 320339) B320339
theorem B213579 : Blo 211809 213579 := bstep (se 1 (by rfl) ⟨160184, by rfl⟩ : syracuseStep 213579 = 320369) B320369
theorem B213591 : Blo 211809 213591 := bstep (se 1 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 213591 = 320387) B320387
theorem B213611 : Blo 211809 213611 := bstep (se 1 (by rfl) ⟨160208, by rfl⟩ : syracuseStep 213611 = 320417) B320417
theorem B213623 : Blo 211809 213623 := bstep (se 1 (by rfl) ⟨160217, by rfl⟩ : syracuseStep 213623 = 320435) B320435
theorem B213643 : Blo 211809 213643 := bstep (se 1 (by rfl) ⟨160232, by rfl⟩ : syracuseStep 213643 = 320465) B320465
theorem B213655 : Blo 211809 213655 := bstep (se 1 (by rfl) ⟨160241, by rfl⟩ : syracuseStep 213655 = 320483) B320483
theorem B213675 : Blo 211809 213675 := bstep (se 1 (by rfl) ⟨160256, by rfl⟩ : syracuseStep 213675 = 320513) B320513
theorem B541363 : Blo 211809 541363 := bstep (se 1 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 541363 = 812045) B812045
theorem B213687 : Blo 211809 213687 := bstep (se 1 (by rfl) ⟨160265, by rfl⟩ : syracuseStep 213687 = 320531) B320531
theorem B213707 : Blo 211809 213707 := bstep (se 1 (by rfl) ⟨160280, by rfl⟩ : syracuseStep 213707 = 320561) B320561
theorem B213719 : Blo 211809 213719 := bstep (se 1 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 213719 = 320579) B320579
theorem B213739 : Blo 211809 213739 := bstep (se 1 (by rfl) ⟨160304, by rfl⟩ : syracuseStep 213739 = 320609) B320609
theorem B213751 : Blo 211809 213751 := bstep (se 1 (by rfl) ⟨160313, by rfl⟩ : syracuseStep 213751 = 320627) B320627
theorem B213771 : Blo 211809 213771 := bstep (se 1 (by rfl) ⟨160328, by rfl⟩ : syracuseStep 213771 = 320657) B320657
theorem B213783 : Blo 211809 213783 := bstep (se 1 (by rfl) ⟨160337, by rfl⟩ : syracuseStep 213783 = 320675) B320675
theorem B213803 : Blo 211809 213803 := bstep (se 1 (by rfl) ⟨160352, by rfl⟩ : syracuseStep 213803 = 320705) B320705
theorem B770867 : Blo 211809 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B213815 : Blo 211809 213815 := bstep (se 1 (by rfl) ⟨160361, by rfl⟩ : syracuseStep 213815 = 320723) B320723
theorem B541505 : Blo 211809 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B213835 : Blo 211809 213835 := bstep (se 1 (by rfl) ⟨160376, by rfl⟩ : syracuseStep 213835 = 320753) B320753
theorem B213847 : Blo 211809 213847 := bstep (se 1 (by rfl) ⟨160385, by rfl⟩ : syracuseStep 213847 = 320771) B320771
theorem B213867 : Blo 211809 213867 := bstep (se 1 (by rfl) ⟨160400, by rfl⟩ : syracuseStep 213867 = 320801) B320801
theorem B213879 : Blo 211809 213879 := bstep (se 1 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 213879 = 320819) B320819
theorem B213899 : Blo 211809 213899 := bstep (se 1 (by rfl) ⟨160424, by rfl⟩ : syracuseStep 213899 = 320849) B320849
theorem B213911 : Blo 211809 213911 := bstep (se 1 (by rfl) ⟨160433, by rfl⟩ : syracuseStep 213911 = 320867) B320867
theorem B213931 : Blo 211809 213931 := bstep (se 1 (by rfl) ⟨160448, by rfl⟩ : syracuseStep 213931 = 320897) B320897
theorem B213943 : Blo 211809 213943 := bstep (se 1 (by rfl) ⟨160457, by rfl⟩ : syracuseStep 213943 = 320915) B320915
theorem B213963 : Blo 211809 213963 := bstep (se 1 (by rfl) ⟨160472, by rfl⟩ : syracuseStep 213963 = 320945) B320945
theorem B213975 : Blo 211809 213975 := bstep (se 1 (by rfl) ⟨160481, by rfl⟩ : syracuseStep 213975 = 320963) B320963
theorem B213995 : Blo 211809 213995 := bstep (se 1 (by rfl) ⟨160496, by rfl⟩ : syracuseStep 213995 = 320993) B320993
theorem B214007 : Blo 211809 214007 := bstep (se 1 (by rfl) ⟨160505, by rfl⟩ : syracuseStep 214007 = 321011) B321011
theorem B214027 : Blo 211809 214027 := bstep (se 1 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 214027 = 321041) B321041
theorem B214039 : Blo 211809 214039 := bstep (se 1 (by rfl) ⟨160529, by rfl⟩ : syracuseStep 214039 = 321059) B321059
theorem B214059 : Blo 211809 214059 := bstep (se 1 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 214059 = 321089) B321089
theorem B214071 : Blo 211809 214071 := bstep (se 1 (by rfl) ⟨160553, by rfl⟩ : syracuseStep 214071 = 321107) B321107
theorem B214091 : Blo 211809 214091 := bstep (se 1 (by rfl) ⟨160568, by rfl⟩ : syracuseStep 214091 = 321137) B321137
theorem B214103 : Blo 211809 214103 := bstep (se 1 (by rfl) ⟨160577, by rfl⟩ : syracuseStep 214103 = 321155) B321155
theorem B214123 : Blo 211809 214123 := bstep (se 1 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 214123 = 321185) B321185
theorem B214135 : Blo 211809 214135 := bstep (se 1 (by rfl) ⟨160601, by rfl⟩ : syracuseStep 214135 = 321203) B321203
theorem B1885315 : Blo 211809 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B214155 : Blo 211809 214155 := bstep (se 1 (by rfl) ⟨160616, by rfl⟩ : syracuseStep 214155 = 321233) B321233
theorem B214167 : Blo 211809 214167 := bstep (se 1 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 214167 = 321251) B321251
theorem B214187 : Blo 211809 214187 := bstep (se 1 (by rfl) ⟨160640, by rfl⟩ : syracuseStep 214187 = 321281) B321281
theorem B214199 : Blo 211809 214199 := bstep (se 1 (by rfl) ⟨160649, by rfl⟩ : syracuseStep 214199 = 321299) B321299
theorem B214219 : Blo 211809 214219 := bstep (se 1 (by rfl) ⟨160664, by rfl⟩ : syracuseStep 214219 = 321329) B321329
theorem B214231 : Blo 211809 214231 := bstep (se 1 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 214231 = 321347) B321347
theorem B214251 : Blo 211809 214251 := bstep (se 1 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 214251 = 321377) B321377
theorem B214263 : Blo 211809 214263 := bstep (se 1 (by rfl) ⟨160697, by rfl⟩ : syracuseStep 214263 = 321395) B321395
theorem B214283 : Blo 211809 214283 := bstep (se 1 (by rfl) ⟨160712, by rfl⟩ : syracuseStep 214283 = 321425) B321425
theorem B214295 : Blo 211809 214295 := bstep (se 1 (by rfl) ⟨160721, by rfl⟩ : syracuseStep 214295 = 321443) B321443
theorem B214315 : Blo 211809 214315 := bstep (se 1 (by rfl) ⟨160736, by rfl⟩ : syracuseStep 214315 = 321473) B321473
theorem B214327 : Blo 211809 214327 := bstep (se 1 (by rfl) ⟨160745, by rfl⟩ : syracuseStep 214327 = 321491) B321491
theorem B214347 : Blo 211809 214347 := bstep (se 1 (by rfl) ⟨160760, by rfl⟩ : syracuseStep 214347 = 321521) B321521
theorem B214359 : Blo 211809 214359 := bstep (se 1 (by rfl) ⟨160769, by rfl⟩ : syracuseStep 214359 = 321539) B321539
theorem B214379 : Blo 211809 214379 := bstep (se 1 (by rfl) ⟨160784, by rfl⟩ : syracuseStep 214379 = 321569) B321569
theorem B214391 : Blo 211809 214391 := bstep (se 1 (by rfl) ⟨160793, by rfl⟩ : syracuseStep 214391 = 321587) B321587
theorem B214411 : Blo 211809 214411 := bstep (se 1 (by rfl) ⟨160808, by rfl⟩ : syracuseStep 214411 = 321617) B321617
theorem B214423 : Blo 211809 214423 := bstep (se 1 (by rfl) ⟨160817, by rfl⟩ : syracuseStep 214423 = 321635) B321635
theorem B214443 : Blo 211809 214443 := bstep (se 1 (by rfl) ⟨160832, by rfl⟩ : syracuseStep 214443 = 321665) B321665
theorem B804269 : Blo 211809 804269 := bstep (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) B301601
theorem B214455 : Blo 211809 214455 := bstep (se 1 (by rfl) ⟨160841, by rfl⟩ : syracuseStep 214455 = 321683) B321683
theorem B214475 : Blo 211809 214475 := bstep (se 1 (by rfl) ⟨160856, by rfl⟩ : syracuseStep 214475 = 321713) B321713
theorem B214487 : Blo 211809 214487 := bstep (se 1 (by rfl) ⟨160865, by rfl⟩ : syracuseStep 214487 = 321731) B321731
theorem B214507 : Blo 211809 214507 := bstep (se 1 (by rfl) ⟨160880, by rfl⟩ : syracuseStep 214507 = 321761) B321761
theorem B214519 : Blo 211809 214519 := bstep (se 1 (by rfl) ⟨160889, by rfl⟩ : syracuseStep 214519 = 321779) B321779
theorem B214539 : Blo 211809 214539 := bstep (se 1 (by rfl) ⟨160904, by rfl⟩ : syracuseStep 214539 = 321809) B321809
theorem B214551 : Blo 211809 214551 := bstep (se 1 (by rfl) ⟨160913, by rfl⟩ : syracuseStep 214551 = 321827) B321827
theorem B214571 : Blo 211809 214571 := bstep (se 1 (by rfl) ⟨160928, by rfl⟩ : syracuseStep 214571 = 321857) B321857
theorem B706099 : Blo 211809 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B214583 : Blo 211809 214583 := bstep (se 1 (by rfl) ⟨160937, by rfl⟩ : syracuseStep 214583 = 321875) B321875
theorem B476747 : Blo 211809 476747 := bstep (se 1 (by rfl) ⟨357560, by rfl⟩ : syracuseStep 476747 = 715121) B715121
theorem B214603 : Blo 211809 214603 := bstep (se 1 (by rfl) ⟨160952, by rfl⟩ : syracuseStep 214603 = 321905) B321905
theorem B214615 : Blo 211809 214615 := bstep (se 1 (by rfl) ⟨160961, by rfl⟩ : syracuseStep 214615 = 321923) B321923
theorem B214635 : Blo 211809 214635 := bstep (se 1 (by rfl) ⟨160976, by rfl⟩ : syracuseStep 214635 = 321953) B321953
theorem B214647 : Blo 211809 214647 := bstep (se 1 (by rfl) ⟨160985, by rfl⟩ : syracuseStep 214647 = 321971) B321971
theorem B476801 : Blo 211809 476801 := bstep (se 2 (by rfl) ⟨178800, by rfl⟩ : syracuseStep 476801 = 357601) B357601
theorem B1033859 : Blo 211809 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B214667 : Blo 211809 214667 := bstep (se 1 (by rfl) ⟨161000, by rfl⟩ : syracuseStep 214667 = 322001) B322001
theorem B1328791 : Blo 211809 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B607895 : Blo 211809 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B214679 : Blo 211809 214679 := bstep (se 1 (by rfl) ⟨161009, by rfl⟩ : syracuseStep 214679 = 322019) B322019
theorem B214699 : Blo 211809 214699 := bstep (se 1 (by rfl) ⟨161024, by rfl⟩ : syracuseStep 214699 = 322049) B322049
theorem B214711 : Blo 211809 214711 := bstep (se 1 (by rfl) ⟨161033, by rfl⟩ : syracuseStep 214711 = 322067) B322067
theorem B214731 : Blo 211809 214731 := bstep (se 1 (by rfl) ⟨161048, by rfl⟩ : syracuseStep 214731 = 322097) B322097
theorem B214743 : Blo 211809 214743 := bstep (se 1 (by rfl) ⟨161057, by rfl⟩ : syracuseStep 214743 = 322115) B322115
theorem B214763 : Blo 211809 214763 := bstep (se 1 (by rfl) ⟨161072, by rfl⟩ : syracuseStep 214763 = 322145) B322145
theorem B214775 : Blo 211809 214775 := bstep (se 1 (by rfl) ⟨161081, by rfl⟩ : syracuseStep 214775 = 322163) B322163
theorem B214795 : Blo 211809 214795 := bstep (se 1 (by rfl) ⟨161096, by rfl⟩ : syracuseStep 214795 = 322193) B322193
theorem B214807 : Blo 211809 214807 := bstep (se 1 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 214807 = 322211) B322211
theorem B214827 : Blo 211809 214827 := bstep (se 1 (by rfl) ⟨161120, by rfl⟩ : syracuseStep 214827 = 322241) B322241
theorem B214839 : Blo 211809 214839 := bstep (se 1 (by rfl) ⟨161129, by rfl⟩ : syracuseStep 214839 = 322259) B322259
theorem B771905 : Blo 211809 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B214859 : Blo 211809 214859 := bstep (se 1 (by rfl) ⟨161144, by rfl⟩ : syracuseStep 214859 = 322289) B322289
theorem B214871 : Blo 211809 214871 := bstep (se 1 (by rfl) ⟨161153, by rfl⟩ : syracuseStep 214871 = 322307) B322307
theorem B477017 : Blo 211809 477017 := bstep (se 2 (by rfl) ⟨178881, by rfl⟩ : syracuseStep 477017 = 357763) B357763
theorem B214891 : Blo 211809 214891 := bstep (se 1 (by rfl) ⟨161168, by rfl⟩ : syracuseStep 214891 = 322337) B322337
theorem B214903 : Blo 211809 214903 := bstep (se 1 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 214903 = 322355) B322355
theorem B214923 : Blo 211809 214923 := bstep (se 1 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 214923 = 322385) B322385
theorem B575383 : Blo 211809 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B214935 : Blo 211809 214935 := bstep (se 1 (by rfl) ⟨161201, by rfl⟩ : syracuseStep 214935 = 322403) B322403
theorem B214955 : Blo 211809 214955 := bstep (se 1 (by rfl) ⟨161216, by rfl⟩ : syracuseStep 214955 = 322433) B322433
theorem B477107 : Blo 211809 477107 := bstep (se 1 (by rfl) ⟨357830, by rfl⟩ : syracuseStep 477107 = 715661) B715661
theorem B214967 : Blo 211809 214967 := bstep (se 1 (by rfl) ⟨161225, by rfl⟩ : syracuseStep 214967 = 322451) B322451
theorem B214987 : Blo 211809 214987 := bstep (se 1 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 214987 = 322481) B322481
theorem B477143 : Blo 211809 477143 := bstep (se 1 (by rfl) ⟨357857, by rfl⟩ : syracuseStep 477143 = 715715) B715715
theorem B214999 : Blo 211809 214999 := bstep (se 1 (by rfl) ⟨161249, by rfl⟩ : syracuseStep 214999 = 322499) B322499
theorem B215019 : Blo 211809 215019 := bstep (se 1 (by rfl) ⟨161264, by rfl⟩ : syracuseStep 215019 = 322529) B322529
theorem B215031 : Blo 211809 215031 := bstep (se 1 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 215031 = 322547) B322547
theorem B1820677 : Blo 211809 1820677 := bstep (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) B341377
theorem B215051 : Blo 211809 215051 := bstep (se 1 (by rfl) ⟨161288, by rfl⟩ : syracuseStep 215051 = 322577) B322577
theorem B215063 : Blo 211809 215063 := bstep (se 1 (by rfl) ⟨161297, by rfl⟩ : syracuseStep 215063 = 322595) B322595
theorem B215083 : Blo 211809 215083 := bstep (se 1 (by rfl) ⟨161312, by rfl⟩ : syracuseStep 215083 = 322625) B322625
theorem B542771 : Blo 211809 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B215095 : Blo 211809 215095 := bstep (se 1 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 215095 = 322643) B322643
theorem B215115 : Blo 211809 215115 := bstep (se 1 (by rfl) ⟨161336, by rfl⟩ : syracuseStep 215115 = 322673) B322673
theorem B215127 : Blo 211809 215127 := bstep (se 1 (by rfl) ⟨161345, by rfl⟩ : syracuseStep 215127 = 322691) B322691
theorem B215147 : Blo 211809 215147 := bstep (se 1 (by rfl) ⟨161360, by rfl⟩ : syracuseStep 215147 = 322721) B322721
theorem B215159 : Blo 211809 215159 := bstep (se 1 (by rfl) ⟨161369, by rfl⟩ : syracuseStep 215159 = 322739) B322739
theorem B477323 : Blo 211809 477323 := bstep (se 1 (by rfl) ⟨357992, by rfl⟩ : syracuseStep 477323 = 715985) B715985
theorem B215179 : Blo 211809 215179 := bstep (se 1 (by rfl) ⟨161384, by rfl⟩ : syracuseStep 215179 = 322769) B322769
theorem B215191 : Blo 211809 215191 := bstep (se 1 (by rfl) ⟨161393, by rfl⟩ : syracuseStep 215191 = 322787) B322787
theorem B215211 : Blo 211809 215211 := bstep (se 1 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 215211 = 322817) B322817
theorem B215223 : Blo 211809 215223 := bstep (se 1 (by rfl) ⟨161417, by rfl⟩ : syracuseStep 215223 = 322835) B322835
theorem B477377 : Blo 211809 477377 := bstep (se 2 (by rfl) ⟨179016, by rfl⟩ : syracuseStep 477377 = 358033) B358033
theorem B215243 : Blo 211809 215243 := bstep (se 1 (by rfl) ⟨161432, by rfl⟩ : syracuseStep 215243 = 322865) B322865
theorem B215255 : Blo 211809 215255 := bstep (se 1 (by rfl) ⟨161441, by rfl⟩ : syracuseStep 215255 = 322883) B322883
theorem B215275 : Blo 211809 215275 := bstep (se 1 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 215275 = 322913) B322913
theorem B215287 : Blo 211809 215287 := bstep (se 1 (by rfl) ⟨161465, by rfl⟩ : syracuseStep 215287 = 322931) B322931
theorem B215307 : Blo 211809 215307 := bstep (se 1 (by rfl) ⟨161480, by rfl⟩ : syracuseStep 215307 = 322961) B322961
theorem B215319 : Blo 211809 215319 := bstep (se 1 (by rfl) ⟨161489, by rfl⟩ : syracuseStep 215319 = 322979) B322979
theorem B215339 : Blo 211809 215339 := bstep (se 1 (by rfl) ⟨161504, by rfl⟩ : syracuseStep 215339 = 323009) B323009
theorem B215351 : Blo 211809 215351 := bstep (se 1 (by rfl) ⟨161513, by rfl⟩ : syracuseStep 215351 = 323027) B323027
theorem B215371 : Blo 211809 215371 := bstep (se 1 (by rfl) ⟨161528, by rfl⟩ : syracuseStep 215371 = 323057) B323057
theorem B215383 : Blo 211809 215383 := bstep (se 1 (by rfl) ⟨161537, by rfl⟩ : syracuseStep 215383 = 323075) B323075
theorem B215403 : Blo 211809 215403 := bstep (se 1 (by rfl) ⟨161552, by rfl⟩ : syracuseStep 215403 = 323105) B323105
theorem B215415 : Blo 211809 215415 := bstep (se 1 (by rfl) ⟨161561, by rfl⟩ : syracuseStep 215415 = 323123) B323123
theorem B215435 : Blo 211809 215435 := bstep (se 1 (by rfl) ⟨161576, by rfl⟩ : syracuseStep 215435 = 323153) B323153
theorem B215447 : Blo 211809 215447 := bstep (se 1 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 215447 = 323171) B323171
theorem B477593 : Blo 211809 477593 := bstep (se 2 (by rfl) ⟨179097, by rfl⟩ : syracuseStep 477593 = 358195) B358195
theorem B215467 : Blo 211809 215467 := bstep (se 1 (by rfl) ⟨161600, by rfl⟩ : syracuseStep 215467 = 323201) B323201
theorem B215479 : Blo 211809 215479 := bstep (se 1 (by rfl) ⟨161609, by rfl⟩ : syracuseStep 215479 = 323219) B323219
theorem B608705 : Blo 211809 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B215499 : Blo 211809 215499 := bstep (se 1 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 215499 = 323249) B323249
theorem B215511 : Blo 211809 215511 := bstep (se 1 (by rfl) ⟨161633, by rfl⟩ : syracuseStep 215511 = 323267) B323267
theorem B215531 : Blo 211809 215531 := bstep (se 1 (by rfl) ⟨161648, by rfl⟩ : syracuseStep 215531 = 323297) B323297
theorem B477683 : Blo 211809 477683 := bstep (se 1 (by rfl) ⟨358262, by rfl⟩ : syracuseStep 477683 = 716525) B716525
theorem B215543 : Blo 211809 215543 := bstep (se 1 (by rfl) ⟨161657, by rfl⟩ : syracuseStep 215543 = 323315) B323315
theorem B215563 : Blo 211809 215563 := bstep (se 1 (by rfl) ⟨161672, by rfl⟩ : syracuseStep 215563 = 323345) B323345
theorem B477719 : Blo 211809 477719 := bstep (se 1 (by rfl) ⟨358289, by rfl⟩ : syracuseStep 477719 = 716579) B716579
theorem B215575 : Blo 211809 215575 := bstep (se 1 (by rfl) ⟨161681, by rfl⟩ : syracuseStep 215575 = 323363) B323363
theorem B215595 : Blo 211809 215595 := bstep (se 1 (by rfl) ⟨161696, by rfl⟩ : syracuseStep 215595 = 323393) B323393
theorem B215607 : Blo 211809 215607 := bstep (se 1 (by rfl) ⟨161705, by rfl⟩ : syracuseStep 215607 = 323411) B323411
theorem B543307 : Blo 211809 543307 := bstep (se 1 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 543307 = 814961) B814961
theorem B215627 : Blo 211809 215627 := bstep (se 1 (by rfl) ⟨161720, by rfl⟩ : syracuseStep 215627 = 323441) B323441
theorem B215639 : Blo 211809 215639 := bstep (se 1 (by rfl) ⟨161729, by rfl⟩ : syracuseStep 215639 = 323459) B323459
theorem B215659 : Blo 211809 215659 := bstep (se 1 (by rfl) ⟨161744, by rfl⟩ : syracuseStep 215659 = 323489) B323489
theorem B215671 : Blo 211809 215671 := bstep (se 1 (by rfl) ⟨161753, by rfl⟩ : syracuseStep 215671 = 323507) B323507
theorem B215691 : Blo 211809 215691 := bstep (se 1 (by rfl) ⟨161768, by rfl⟩ : syracuseStep 215691 = 323537) B323537
theorem B215703 : Blo 211809 215703 := bstep (se 1 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 215703 = 323555) B323555
theorem B215723 : Blo 211809 215723 := bstep (se 1 (by rfl) ⟨161792, by rfl⟩ : syracuseStep 215723 = 323585) B323585
theorem B215735 : Blo 211809 215735 := bstep (se 1 (by rfl) ⟨161801, by rfl⟩ : syracuseStep 215735 = 323603) B323603
theorem B477899 : Blo 211809 477899 := bstep (se 1 (by rfl) ⟨358424, by rfl⟩ : syracuseStep 477899 = 716849) B716849
theorem B215755 : Blo 211809 215755 := bstep (se 1 (by rfl) ⟨161816, by rfl⟩ : syracuseStep 215755 = 323633) B323633
theorem B215767 : Blo 211809 215767 := bstep (se 1 (by rfl) ⟨161825, by rfl⟩ : syracuseStep 215767 = 323651) B323651
theorem B543449 : Blo 211809 543449 := bstep (se 2 (by rfl) ⟨203793, by rfl⟩ : syracuseStep 543449 = 407587) B407587
theorem B215787 : Blo 211809 215787 := bstep (se 1 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 215787 = 323681) B323681
theorem B215799 : Blo 211809 215799 := bstep (se 1 (by rfl) ⟨161849, by rfl⟩ : syracuseStep 215799 = 323699) B323699
theorem B477953 : Blo 211809 477953 := bstep (se 2 (by rfl) ⟨179232, by rfl⟩ : syracuseStep 477953 = 358465) B358465
theorem B805697 : Blo 211809 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B478169 : Blo 211809 478169 := bstep (se 2 (by rfl) ⟨179313, by rfl⟩ : syracuseStep 478169 = 358627) B358627
theorem B2739217 : Blo 211809 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B478259 : Blo 211809 478259 := bstep (se 1 (by rfl) ⟨358694, by rfl⟩ : syracuseStep 478259 = 717389) B717389
theorem B478295 : Blo 211809 478295 := bstep (se 1 (by rfl) ⟨358721, by rfl⟩ : syracuseStep 478295 = 717443) B717443
theorem B478475 : Blo 211809 478475 := bstep (se 1 (by rfl) ⟨358856, by rfl⟩ : syracuseStep 478475 = 717713) B717713
theorem B478529 : Blo 211809 478529 := bstep (se 2 (by rfl) ⟨179448, by rfl⟩ : syracuseStep 478529 = 358897) B358897
theorem B970157 : Blo 211809 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B544279 : Blo 211809 544279 := bstep (se 1 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 544279 = 816419) B816419
theorem B478745 : Blo 211809 478745 := bstep (se 2 (by rfl) ⟨179529, by rfl⟩ : syracuseStep 478745 = 359059) B359059
theorem B413273 : Blo 211809 413273 := bstep (se 2 (by rfl) ⟨154977, by rfl⟩ : syracuseStep 413273 = 309955) B309955
theorem B478835 : Blo 211809 478835 := bstep (se 1 (by rfl) ⟨359126, by rfl⟩ : syracuseStep 478835 = 718253) B718253
theorem B478871 : Blo 211809 478871 := bstep (se 1 (by rfl) ⟨359153, by rfl⟩ : syracuseStep 478871 = 718307) B718307
theorem B1232563 : Blo 211809 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B479051 : Blo 211809 479051 := bstep (se 1 (by rfl) ⟨359288, by rfl⟩ : syracuseStep 479051 = 718577) B718577
theorem B479105 : Blo 211809 479105 := bstep (se 2 (by rfl) ⟨179664, by rfl⟩ : syracuseStep 479105 = 359329) B359329
theorem B544715 : Blo 211809 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B610355 : Blo 211809 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B610379 : Blo 211809 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B479321 : Blo 211809 479321 := bstep (se 2 (by rfl) ⟨179745, by rfl⟩ : syracuseStep 479321 = 359491) B359491
theorem B872579 : Blo 211809 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B479411 : Blo 211809 479411 := bstep (se 1 (by rfl) ⟨359558, by rfl⟩ : syracuseStep 479411 = 719117) B719117
theorem B479447 : Blo 211809 479447 := bstep (se 1 (by rfl) ⟨359585, by rfl⟩ : syracuseStep 479447 = 719171) B719171
theorem B807185 : Blo 211809 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B545089 : Blo 211809 545089 := bstep (se 2 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 545089 = 408817) B408817
theorem B479627 : Blo 211809 479627 := bstep (se 1 (by rfl) ⟨359720, by rfl⟩ : syracuseStep 479627 = 719441) B719441
theorem B479681 : Blo 211809 479681 := bstep (se 2 (by rfl) ⟨179880, by rfl⟩ : syracuseStep 479681 = 359761) B359761
theorem B1626641 : Blo 211809 1626641 := bstep (se 2 (by rfl) ⟨609990, by rfl⟩ : syracuseStep 1626641 = 1219981) B1219981
theorem B479897 : Blo 211809 479897 := bstep (se 2 (by rfl) ⟨179961, by rfl⟩ : syracuseStep 479897 = 359923) B359923
theorem B1823411 : Blo 211809 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B2904781 : Blo 211809 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B807641 : Blo 211809 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B348889 : Blo 211809 348889 := bstep (se 2 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 348889 = 261667) B261667
theorem B479987 : Blo 211809 479987 := bstep (se 1 (by rfl) ⟨359990, by rfl⟩ : syracuseStep 479987 = 719981) B719981
theorem B3134213 : Blo 211809 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B480023 : Blo 211809 480023 := bstep (se 1 (by rfl) ⟨360017, by rfl⟩ : syracuseStep 480023 = 720035) B720035
theorem B611165 : Blo 211809 611165 := bstep (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) B229187
theorem B545687 : Blo 211809 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B807853 : Blo 211809 807853 := bstep (se 3 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 807853 = 302945) B302945
theorem B480203 : Blo 211809 480203 := bstep (se 1 (by rfl) ⟨360152, by rfl⟩ : syracuseStep 480203 = 720305) B720305
theorem B480257 : Blo 211809 480257 := bstep (se 2 (by rfl) ⟨180096, by rfl⟩ : syracuseStep 480257 = 360193) B360193
theorem B611479 : Blo 211809 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B480473 : Blo 211809 480473 := bstep (se 2 (by rfl) ⟨180177, by rfl⟩ : syracuseStep 480473 = 360355) B360355
theorem B808157 : Blo 211809 808157 := bstep (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) B303059
theorem B480563 : Blo 211809 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B480599 : Blo 211809 480599 := bstep (se 1 (by rfl) ⟨360449, by rfl⟩ : syracuseStep 480599 = 720899) B720899
theorem B644573 : Blo 211809 644573 := bstep (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) B241715
theorem B480779 : Blo 211809 480779 := bstep (se 1 (by rfl) ⟨360584, by rfl⟩ : syracuseStep 480779 = 721169) B721169
theorem B480833 : Blo 211809 480833 := bstep (se 2 (by rfl) ⟨180312, by rfl⟩ : syracuseStep 480833 = 360625) B360625
theorem B481049 : Blo 211809 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B481139 : Blo 211809 481139 := bstep (se 1 (by rfl) ⟨360854, by rfl⟩ : syracuseStep 481139 = 721709) B721709
theorem B481175 : Blo 211809 481175 := bstep (se 1 (by rfl) ⟨360881, by rfl⟩ : syracuseStep 481175 = 721763) B721763
theorem B645067 : Blo 211809 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B481355 : Blo 211809 481355 := bstep (se 1 (by rfl) ⟨361016, by rfl⟩ : syracuseStep 481355 = 722033) B722033
theorem B5036107 : Blo 211809 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B546905 : Blo 211809 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B481409 : Blo 211809 481409 := bstep (se 2 (by rfl) ⟨180528, by rfl⟩ : syracuseStep 481409 = 361057) B361057
theorem B907537 : Blo 211809 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B2283821 : Blo 211809 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B317771 : Blo 211809 317771 := bstep (se 1 (by rfl) ⟨238328, by rfl⟩ : syracuseStep 317771 = 476657) B476657
theorem B317783 : Blo 211809 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B481625 : Blo 211809 481625 := bstep (se 2 (by rfl) ⟨180609, by rfl⟩ : syracuseStep 481625 = 361219) B361219
theorem B317849 : Blo 211809 317849 := bstep (se 2 (by rfl) ⟨119193, by rfl⟩ : syracuseStep 317849 = 238387) B238387
theorem B481715 : Blo 211809 481715 := bstep (se 1 (by rfl) ⟨361286, by rfl⟩ : syracuseStep 481715 = 722573) B722573
theorem B481751 : Blo 211809 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B317963 : Blo 211809 317963 := bstep (se 1 (by rfl) ⟨238472, by rfl⟩ : syracuseStep 317963 = 476945) B476945
theorem B1989137 : Blo 211809 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B317975 : Blo 211809 317975 := bstep (se 1 (by rfl) ⟨238481, by rfl⟩ : syracuseStep 317975 = 476963) B476963
theorem B1825325 : Blo 211809 1825325 := bstep (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) B684497
theorem B318041 : Blo 211809 318041 := bstep (se 2 (by rfl) ⟨119265, by rfl⟩ : syracuseStep 318041 = 238531) B238531
theorem B612953 : Blo 211809 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B481931 : Blo 211809 481931 := bstep (se 1 (by rfl) ⟨361448, by rfl⟩ : syracuseStep 481931 = 722897) B722897
theorem B481985 : Blo 211809 481985 := bstep (se 2 (by rfl) ⟨180744, by rfl⟩ : syracuseStep 481985 = 361489) B361489
theorem B318155 : Blo 211809 318155 := bstep (se 1 (by rfl) ⟨238616, by rfl⟩ : syracuseStep 318155 = 477233) B477233
theorem B318167 : Blo 211809 318167 := bstep (se 1 (by rfl) ⟨238625, by rfl⟩ : syracuseStep 318167 = 477251) B477251
theorem B514777 : Blo 211809 514777 := bstep (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) B386083
theorem B580313 : Blo 211809 580313 := bstep (se 2 (by rfl) ⟨217617, by rfl⟩ : syracuseStep 580313 = 435235) B435235
theorem B318233 : Blo 211809 318233 := bstep (se 2 (by rfl) ⟨119337, by rfl⟩ : syracuseStep 318233 = 238675) B238675
theorem B318347 : Blo 211809 318347 := bstep (se 1 (by rfl) ⟨238760, by rfl⟩ : syracuseStep 318347 = 477521) B477521
theorem B318359 : Blo 211809 318359 := bstep (se 1 (by rfl) ⟨238769, by rfl⟩ : syracuseStep 318359 = 477539) B477539
theorem B613271 : Blo 211809 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B482201 : Blo 211809 482201 := bstep (se 2 (by rfl) ⟨180825, by rfl⟩ : syracuseStep 482201 = 361651) B361651
theorem B318425 : Blo 211809 318425 := bstep (se 2 (by rfl) ⟨119409, by rfl⟩ : syracuseStep 318425 = 238819) B238819
theorem B482291 : Blo 211809 482291 := bstep (se 1 (by rfl) ⟨361718, by rfl⟩ : syracuseStep 482291 = 723437) B723437
theorem B482327 : Blo 211809 482327 := bstep (se 1 (by rfl) ⟨361745, by rfl⟩ : syracuseStep 482327 = 723491) B723491
theorem B318539 : Blo 211809 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B318551 : Blo 211809 318551 := bstep (se 1 (by rfl) ⟨238913, by rfl⟩ : syracuseStep 318551 = 477827) B477827
theorem B318617 : Blo 211809 318617 := bstep (se 2 (by rfl) ⟨119481, by rfl⟩ : syracuseStep 318617 = 238963) B238963
theorem B482507 : Blo 211809 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B1826009 : Blo 211809 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B482561 : Blo 211809 482561 := bstep (se 2 (by rfl) ⟨180960, by rfl⟩ : syracuseStep 482561 = 361921) B361921
theorem B318731 : Blo 211809 318731 := bstep (se 1 (by rfl) ⟨239048, by rfl⟩ : syracuseStep 318731 = 478097) B478097
theorem B318743 : Blo 211809 318743 := bstep (se 1 (by rfl) ⟨239057, by rfl⟩ : syracuseStep 318743 = 478115) B478115
theorem B515393 : Blo 211809 515393 := bstep (se 2 (by rfl) ⟨193272, by rfl⟩ : syracuseStep 515393 = 386545) B386545
theorem B318809 : Blo 211809 318809 := bstep (se 2 (by rfl) ⟨119553, by rfl⟩ : syracuseStep 318809 = 239107) B239107
theorem B318923 : Blo 211809 318923 := bstep (se 1 (by rfl) ⟨239192, by rfl⟩ : syracuseStep 318923 = 478385) B478385
theorem B318935 : Blo 211809 318935 := bstep (se 1 (by rfl) ⟨239201, by rfl⟩ : syracuseStep 318935 = 478403) B478403
theorem B1072601 : Blo 211809 1072601 := bstep (se 2 (by rfl) ⟨402225, by rfl⟩ : syracuseStep 1072601 = 804451) B804451
theorem B482777 : Blo 211809 482777 := bstep (se 2 (by rfl) ⟨181041, by rfl⟩ : syracuseStep 482777 = 362083) B362083
theorem B319001 : Blo 211809 319001 := bstep (se 2 (by rfl) ⟨119625, by rfl⟩ : syracuseStep 319001 = 239251) B239251
theorem B384563 : Blo 211809 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B482867 : Blo 211809 482867 := bstep (se 1 (by rfl) ⟨362150, by rfl⟩ : syracuseStep 482867 = 724301) B724301
theorem B482903 : Blo 211809 482903 := bstep (se 1 (by rfl) ⟨362177, by rfl⟩ : syracuseStep 482903 = 724355) B724355
theorem B319115 : Blo 211809 319115 := bstep (se 1 (by rfl) ⟨239336, by rfl⟩ : syracuseStep 319115 = 478673) B478673
theorem B319127 : Blo 211809 319127 := bstep (se 1 (by rfl) ⟨239345, by rfl⟩ : syracuseStep 319127 = 478691) B478691
theorem B679603 : Blo 211809 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B614081 : Blo 211809 614081 := bstep (se 2 (by rfl) ⟨230280, by rfl⟩ : syracuseStep 614081 = 460561) B460561
theorem B319193 : Blo 211809 319193 := bstep (se 2 (by rfl) ⟨119697, by rfl⟩ : syracuseStep 319193 = 239395) B239395
theorem B810755 : Blo 211809 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B483083 : Blo 211809 483083 := bstep (se 1 (by rfl) ⟨362312, by rfl⟩ : syracuseStep 483083 = 724625) B724625
theorem B810769 : Blo 211809 810769 := bstep (se 2 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 810769 = 608077) B608077
theorem B483137 : Blo 211809 483137 := bstep (se 2 (by rfl) ⟨181176, by rfl⟩ : syracuseStep 483137 = 362353) B362353
theorem B319307 : Blo 211809 319307 := bstep (se 1 (by rfl) ⟨239480, by rfl⟩ : syracuseStep 319307 = 478961) B478961
theorem B319319 : Blo 211809 319319 := bstep (se 1 (by rfl) ⟨239489, by rfl⟩ : syracuseStep 319319 = 478979) B478979
theorem B319385 : Blo 211809 319385 := bstep (se 2 (by rfl) ⟨119769, by rfl⟩ : syracuseStep 319385 = 239539) B239539
theorem B679873 : Blo 211809 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B319499 : Blo 211809 319499 := bstep (se 1 (by rfl) ⟨239624, by rfl⟩ : syracuseStep 319499 = 479249) B479249
theorem B221195 : Blo 211809 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B319511 : Blo 211809 319511 := bstep (se 1 (by rfl) ⟨239633, by rfl⟩ : syracuseStep 319511 = 479267) B479267
theorem B483353 : Blo 211809 483353 := bstep (se 2 (by rfl) ⟨181257, by rfl⟩ : syracuseStep 483353 = 362515) B362515
theorem B811073 : Blo 211809 811073 := bstep (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) B608305
theorem B319577 : Blo 211809 319577 := bstep (se 2 (by rfl) ⟨119841, by rfl⟩ : syracuseStep 319577 = 239683) B239683
theorem B483443 : Blo 211809 483443 := bstep (se 1 (by rfl) ⟨362582, by rfl⟩ : syracuseStep 483443 = 725165) B725165
theorem B483479 : Blo 211809 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B319691 : Blo 211809 319691 := bstep (se 1 (by rfl) ⟨239768, by rfl⟩ : syracuseStep 319691 = 479537) B479537
theorem B319703 : Blo 211809 319703 := bstep (se 1 (by rfl) ⟨239777, by rfl⟩ : syracuseStep 319703 = 479555) B479555
theorem B614621 : Blo 211809 614621 := bstep (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) B230483
theorem B319769 : Blo 211809 319769 := bstep (se 2 (by rfl) ⟨119913, by rfl⟩ : syracuseStep 319769 = 239827) B239827
theorem B1630529 : Blo 211809 1630529 := bstep (se 2 (by rfl) ⟨611448, by rfl⟩ : syracuseStep 1630529 = 1222897) B1222897
theorem B483659 : Blo 211809 483659 := bstep (se 1 (by rfl) ⟨362744, by rfl⟩ : syracuseStep 483659 = 725489) B725489
theorem B483713 : Blo 211809 483713 := bstep (se 2 (by rfl) ⟨181392, by rfl⟩ : syracuseStep 483713 = 362785) B362785
theorem B319883 : Blo 211809 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B319895 : Blo 211809 319895 := bstep (se 1 (by rfl) ⟨239921, by rfl⟩ : syracuseStep 319895 = 479843) B479843
theorem B319961 : Blo 211809 319961 := bstep (se 2 (by rfl) ⟨119985, by rfl⟩ : syracuseStep 319961 = 239971) B239971
theorem B320075 : Blo 211809 320075 := bstep (se 1 (by rfl) ⟨240056, by rfl⟩ : syracuseStep 320075 = 480113) B480113
theorem B320087 : Blo 211809 320087 := bstep (se 1 (by rfl) ⟨240065, by rfl⟩ : syracuseStep 320087 = 480131) B480131
theorem B909913 : Blo 211809 909913 := bstep (se 2 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 909913 = 682435) B682435
theorem B483929 : Blo 211809 483929 := bstep (se 2 (by rfl) ⟨181473, by rfl⟩ : syracuseStep 483929 = 362947) B362947
theorem B320153 : Blo 211809 320153 := bstep (se 2 (by rfl) ⟨120057, by rfl⟩ : syracuseStep 320153 = 240115) B240115
theorem B484019 : Blo 211809 484019 := bstep (se 1 (by rfl) ⟨363014, by rfl⟩ : syracuseStep 484019 = 726029) B726029
theorem B484055 : Blo 211809 484055 := bstep (se 1 (by rfl) ⟨363041, by rfl⟩ : syracuseStep 484055 = 726083) B726083
theorem B811741 : Blo 211809 811741 := bstep (se 3 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 811741 = 304403) B304403
theorem B320267 : Blo 211809 320267 := bstep (se 1 (by rfl) ⟨240200, by rfl⟩ : syracuseStep 320267 = 480401) B480401
theorem B320279 : Blo 211809 320279 := bstep (se 1 (by rfl) ⟨240209, by rfl⟩ : syracuseStep 320279 = 480419) B480419
theorem B582475 : Blo 211809 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B320345 : Blo 211809 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B2614133 : Blo 211809 2614133 := bstep (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) B245075
theorem B484235 : Blo 211809 484235 := bstep (se 1 (by rfl) ⟨363176, by rfl⟩ : syracuseStep 484235 = 726353) B726353
theorem B484289 : Blo 211809 484289 := bstep (se 2 (by rfl) ⟨181608, by rfl⟩ : syracuseStep 484289 = 363217) B363217
theorem B320459 : Blo 211809 320459 := bstep (se 1 (by rfl) ⟨240344, by rfl⟩ : syracuseStep 320459 = 480689) B480689
theorem B320471 : Blo 211809 320471 := bstep (se 1 (by rfl) ⟨240353, by rfl⟩ : syracuseStep 320471 = 480707) B480707
theorem B1860569 : Blo 211809 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B320537 : Blo 211809 320537 := bstep (se 2 (by rfl) ⟨120201, by rfl⟩ : syracuseStep 320537 = 240403) B240403
theorem B1074221 : Blo 211809 1074221 := bstep (se 3 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 1074221 = 402833) B402833
theorem B320651 : Blo 211809 320651 := bstep (se 1 (by rfl) ⟨240488, by rfl⟩ : syracuseStep 320651 = 480977) B480977
theorem B320663 : Blo 211809 320663 := bstep (se 1 (by rfl) ⟨240497, by rfl⟩ : syracuseStep 320663 = 480995) B480995
theorem B484505 : Blo 211809 484505 := bstep (se 2 (by rfl) ⟨181689, by rfl⟩ : syracuseStep 484505 = 363379) B363379
theorem B320729 : Blo 211809 320729 := bstep (se 2 (by rfl) ⟨120273, by rfl⟩ : syracuseStep 320729 = 240547) B240547
theorem B484595 : Blo 211809 484595 := bstep (se 1 (by rfl) ⟨363446, by rfl⟩ : syracuseStep 484595 = 726893) B726893
theorem B5498117 : Blo 211809 5498117 := bstep (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) B1030897
theorem B484631 : Blo 211809 484631 := bstep (se 1 (by rfl) ⟨363473, by rfl⟩ : syracuseStep 484631 = 726947) B726947
theorem B320843 : Blo 211809 320843 := bstep (se 1 (by rfl) ⟨240632, by rfl⟩ : syracuseStep 320843 = 481265) B481265
theorem B320855 : Blo 211809 320855 := bstep (se 1 (by rfl) ⟨240641, by rfl⟩ : syracuseStep 320855 = 481283) B481283
theorem B419161 : Blo 211809 419161 := bstep (se 2 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 419161 = 314371) B314371
theorem B320921 : Blo 211809 320921 := bstep (se 2 (by rfl) ⟨120345, by rfl⟩ : syracuseStep 320921 = 240691) B240691
theorem B484811 : Blo 211809 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B484865 : Blo 211809 484865 := bstep (se 2 (by rfl) ⟨181824, by rfl⟩ : syracuseStep 484865 = 363649) B363649
theorem B321035 : Blo 211809 321035 := bstep (se 1 (by rfl) ⟨240776, by rfl⟩ : syracuseStep 321035 = 481553) B481553
theorem B910871 : Blo 211809 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B321047 : Blo 211809 321047 := bstep (se 1 (by rfl) ⟨240785, by rfl⟩ : syracuseStep 321047 = 481571) B481571
theorem B321113 : Blo 211809 321113 := bstep (se 2 (by rfl) ⟨120417, by rfl⟩ : syracuseStep 321113 = 240835) B240835
theorem B353945 : Blo 211809 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B321227 : Blo 211809 321227 := bstep (se 1 (by rfl) ⟨240920, by rfl⟩ : syracuseStep 321227 = 481841) B481841
theorem B321239 : Blo 211809 321239 := bstep (se 1 (by rfl) ⟨240929, by rfl⟩ : syracuseStep 321239 = 481859) B481859
theorem B485081 : Blo 211809 485081 := bstep (se 2 (by rfl) ⟨181905, by rfl⟩ : syracuseStep 485081 = 363811) B363811
theorem B321305 : Blo 211809 321305 := bstep (se 2 (by rfl) ⟨120489, by rfl⟩ : syracuseStep 321305 = 240979) B240979
theorem B485171 : Blo 211809 485171 := bstep (se 1 (by rfl) ⟨363878, by rfl⟩ : syracuseStep 485171 = 727757) B727757
theorem B485207 : Blo 211809 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B681821 : Blo 211809 681821 := bstep (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) B255683
theorem B321419 : Blo 211809 321419 := bstep (se 1 (by rfl) ⟨241064, by rfl⟩ : syracuseStep 321419 = 482129) B482129
theorem B321431 : Blo 211809 321431 := bstep (se 1 (by rfl) ⟨241073, by rfl⟩ : syracuseStep 321431 = 482147) B482147
theorem B813017 : Blo 211809 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B321497 : Blo 211809 321497 := bstep (se 2 (by rfl) ⟨120561, by rfl⟩ : syracuseStep 321497 = 241123) B241123
theorem B485387 : Blo 211809 485387 := bstep (se 1 (by rfl) ⟨364040, by rfl⟩ : syracuseStep 485387 = 728081) B728081
theorem B485441 : Blo 211809 485441 := bstep (se 2 (by rfl) ⟨182040, by rfl⟩ : syracuseStep 485441 = 364081) B364081
theorem B321611 : Blo 211809 321611 := bstep (se 1 (by rfl) ⟨241208, by rfl⟩ : syracuseStep 321611 = 482417) B482417
theorem B321623 : Blo 211809 321623 := bstep (se 1 (by rfl) ⟨241217, by rfl⟩ : syracuseStep 321623 = 482435) B482435
theorem B321689 : Blo 211809 321689 := bstep (se 2 (by rfl) ⟨120633, by rfl⟩ : syracuseStep 321689 = 241267) B241267
theorem B387251 : Blo 211809 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B3106997 : Blo 211809 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B1632473 : Blo 211809 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B321803 : Blo 211809 321803 := bstep (se 1 (by rfl) ⟨241352, by rfl⟩ : syracuseStep 321803 = 482705) B482705
theorem B1108241 : Blo 211809 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B321815 : Blo 211809 321815 := bstep (se 1 (by rfl) ⟨241361, by rfl⟩ : syracuseStep 321815 = 482723) B482723
theorem B321881 : Blo 211809 321881 := bstep (se 2 (by rfl) ⟨120705, by rfl⟩ : syracuseStep 321881 = 241411) B241411
theorem B453043 : Blo 211809 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B321995 : Blo 211809 321995 := bstep (se 1 (by rfl) ⟨241496, by rfl⟩ : syracuseStep 321995 = 482993) B482993
theorem B322007 : Blo 211809 322007 := bstep (se 1 (by rfl) ⟨241505, by rfl⟩ : syracuseStep 322007 = 483011) B483011
theorem B715229 : Blo 211809 715229 := bstep (se 3 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 715229 = 268211) B268211
theorem B322073 : Blo 211809 322073 := bstep (se 2 (by rfl) ⟨120777, by rfl⟩ : syracuseStep 322073 = 241555) B241555
theorem B1206859 : Blo 211809 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B322187 : Blo 211809 322187 := bstep (se 1 (by rfl) ⟨241640, by rfl⟩ : syracuseStep 322187 = 483281) B483281
theorem B322199 : Blo 211809 322199 := bstep (se 1 (by rfl) ⟨241649, by rfl⟩ : syracuseStep 322199 = 483299) B483299
theorem B322265 : Blo 211809 322265 := bstep (se 2 (by rfl) ⟨120849, by rfl⟩ : syracuseStep 322265 = 241699) B241699
theorem B486155 : Blo 211809 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B1469249 : Blo 211809 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B322379 : Blo 211809 322379 := bstep (se 1 (by rfl) ⟨241784, by rfl⟩ : syracuseStep 322379 = 483569) B483569
theorem B322391 : Blo 211809 322391 := bstep (se 1 (by rfl) ⟨241793, by rfl⟩ : syracuseStep 322391 = 483587) B483587
theorem B387929 : Blo 211809 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B1207133 : Blo 211809 1207133 := bstep (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) B452675
theorem B453529 : Blo 211809 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B322457 : Blo 211809 322457 := bstep (se 2 (by rfl) ⟨120921, by rfl⟩ : syracuseStep 322457 = 241843) B241843
theorem B322571 : Blo 211809 322571 := bstep (se 1 (by rfl) ⟨241928, by rfl⟩ : syracuseStep 322571 = 483857) B483857
theorem B322583 : Blo 211809 322583 := bstep (se 1 (by rfl) ⟨241937, by rfl⟩ : syracuseStep 322583 = 483875) B483875
theorem B322649 : Blo 211809 322649 := bstep (se 2 (by rfl) ⟨120993, by rfl⟩ : syracuseStep 322649 = 241987) B241987
theorem B322763 : Blo 211809 322763 := bstep (se 1 (by rfl) ⟨242072, by rfl⟩ : syracuseStep 322763 = 484145) B484145
theorem B1961165 : Blo 211809 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B322775 : Blo 211809 322775 := bstep (se 1 (by rfl) ⟨242081, by rfl⟩ : syracuseStep 322775 = 484163) B484163
theorem B322841 : Blo 211809 322841 := bstep (se 2 (by rfl) ⟨121065, by rfl⟩ : syracuseStep 322841 = 242131) B242131
theorem B322955 : Blo 211809 322955 := bstep (se 1 (by rfl) ⟨242216, by rfl⟩ : syracuseStep 322955 = 484433) B484433
theorem B7925141 : Blo 211809 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B322967 : Blo 211809 322967 := bstep (se 1 (by rfl) ⟨242225, by rfl⟩ : syracuseStep 322967 = 484451) B484451
theorem B650713 : Blo 211809 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B323033 : Blo 211809 323033 := bstep (se 2 (by rfl) ⟨121137, by rfl⟩ : syracuseStep 323033 = 242275) B242275
theorem B814643 : Blo 211809 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B814657 : Blo 211809 814657 := bstep (se 2 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 814657 = 610993) B610993
theorem B716363 : Blo 211809 716363 := bstep (se 1 (by rfl) ⟨537272, by rfl⟩ : syracuseStep 716363 = 1074545) B1074545
theorem B912971 : Blo 211809 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B323147 : Blo 211809 323147 := bstep (se 1 (by rfl) ⟨242360, by rfl⟩ : syracuseStep 323147 = 484721) B484721
theorem B323159 : Blo 211809 323159 := bstep (se 1 (by rfl) ⟨242369, by rfl⟩ : syracuseStep 323159 = 484739) B484739
theorem B323225 : Blo 211809 323225 := bstep (se 2 (by rfl) ⟨121209, by rfl⟩ : syracuseStep 323225 = 242419) B242419
theorem B388865 : Blo 211809 388865 := bstep (se 2 (by rfl) ⟨145824, by rfl⟩ : syracuseStep 388865 = 291649) B291649
theorem B323339 : Blo 211809 323339 := bstep (se 1 (by rfl) ⟨242504, by rfl⟩ : syracuseStep 323339 = 485009) B485009
theorem B323351 : Blo 211809 323351 := bstep (se 1 (by rfl) ⟨242513, by rfl⟩ : syracuseStep 323351 = 485027) B485027
theorem B7499573 : Blo 211809 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B716633 : Blo 211809 716633 := bstep (se 2 (by rfl) ⟨268737, by rfl⟩ : syracuseStep 716633 = 537475) B537475
theorem B323417 : Blo 211809 323417 := bstep (se 2 (by rfl) ⟨121281, by rfl⟩ : syracuseStep 323417 = 242563) B242563
theorem B323531 : Blo 211809 323531 := bstep (se 1 (by rfl) ⟨242648, by rfl⟩ : syracuseStep 323531 = 485297) B485297
theorem B323543 : Blo 211809 323543 := bstep (se 1 (by rfl) ⟨242657, by rfl⟩ : syracuseStep 323543 = 485315) B485315
theorem B323609 : Blo 211809 323609 := bstep (se 2 (by rfl) ⟨121353, by rfl⟩ : syracuseStep 323609 = 242707) B242707
theorem B454999 : Blo 211809 454999 := bstep (se 1 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 454999 = 682499) B682499
theorem B455051 : Blo 211809 455051 := bstep (se 1 (by rfl) ⟨341288, by rfl⟩ : syracuseStep 455051 = 682577) B682577
theorem B717335 : Blo 211809 717335 := bstep (se 1 (by rfl) ⟨538001, by rfl⟩ : syracuseStep 717335 = 1076003) B1076003
theorem B389657 : Blo 211809 389657 := bstep (se 2 (by rfl) ⟨146121, by rfl⟩ : syracuseStep 389657 = 292243) B292243
theorem B487961 : Blo 211809 487961 := bstep (se 2 (by rfl) ⟨182985, by rfl⟩ : syracuseStep 487961 = 365971) B365971
theorem B258647 : Blo 211809 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B1372889 : Blo 211809 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B881425 : Blo 211809 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B1078109 : Blo 211809 1078109 := bstep (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) B404291
theorem B717875 : Blo 211809 717875 := bstep (se 1 (by rfl) ⟨538406, by rfl⟩ : syracuseStep 717875 = 1076813) B1076813
theorem B259147 : Blo 211809 259147 := bstep (se 1 (by rfl) ⟨194360, by rfl⟩ : syracuseStep 259147 = 388721) B388721
theorem B226423 : Blo 211809 226423 := bstep (se 1 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 226423 = 339635) B339635
theorem B357527 : Blo 211809 357527 := bstep (se 1 (by rfl) ⟨268145, by rfl⟩ : syracuseStep 357527 = 536291) B536291
theorem B914611 : Blo 211809 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B357655 : Blo 211809 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B1537325 : Blo 211809 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B488755 : Blo 211809 488755 := bstep (se 1 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 488755 = 733133) B733133
theorem B718145 : Blo 211809 718145 := bstep (se 2 (by rfl) ⟨269304, by rfl⟩ : syracuseStep 718145 = 538609) B538609
theorem B816587 : Blo 211809 816587 := bstep (se 1 (by rfl) ⟨612440, by rfl⟩ : syracuseStep 816587 = 1224881) B1224881
theorem B816601 : Blo 211809 816601 := bstep (se 2 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 816601 = 612451) B612451
theorem B226795 : Blo 211809 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B488983 : Blo 211809 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B1635875 : Blo 211809 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B489203 : Blo 211809 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B915245 : Blo 211809 915245 := bstep (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) B343217
theorem B2094913 : Blo 211809 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B718685 : Blo 211809 718685 := bstep (se 3 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 718685 = 269507) B269507
theorem B358283 : Blo 211809 358283 := bstep (se 1 (by rfl) ⟨268712, by rfl⟩ : syracuseStep 358283 = 537425) B537425
theorem B227243 : Blo 211809 227243 := bstep (se 1 (by rfl) ⟨170432, by rfl⟩ : syracuseStep 227243 = 340865) B340865
theorem B2062259 : Blo 211809 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B456691 : Blo 211809 456691 := bstep (se 1 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 456691 = 685037) B685037
theorem B358411 : Blo 211809 358411 := bstep (se 1 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 358411 = 537617) B537617
theorem B358553 : Blo 211809 358553 := bstep (se 2 (by rfl) ⟨134457, by rfl⟩ : syracuseStep 358553 = 268915) B268915
theorem B358681 : Blo 211809 358681 := bstep (se 2 (by rfl) ⟨134505, by rfl⟩ : syracuseStep 358681 = 269011) B269011
theorem B653633 : Blo 211809 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B457049 : Blo 211809 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B817559 : Blo 211809 817559 := bstep (se 1 (by rfl) ⟨613169, by rfl⟩ : syracuseStep 817559 = 1226339) B1226339
theorem B2980313 : Blo 211809 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B2226781 : Blo 211809 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B1637015 : Blo 211809 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B1538851 : Blo 211809 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B359255 : Blo 211809 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B1080215 : Blo 211809 1080215 := bstep (se 1 (by rfl) ⟨810161, by rfl⟩ : syracuseStep 1080215 = 1620323) B1620323
theorem B719819 : Blo 211809 719819 := bstep (se 1 (by rfl) ⟨539864, by rfl⟩ : syracuseStep 719819 = 1079729) B1079729
theorem B359383 : Blo 211809 359383 := bstep (se 1 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 359383 = 539075) B539075
theorem B228439 : Blo 211809 228439 := bstep (se 1 (by rfl) ⟨171329, by rfl⟩ : syracuseStep 228439 = 342659) B342659
theorem B720089 : Blo 211809 720089 := bstep (se 2 (by rfl) ⟨270033, by rfl⟩ : syracuseStep 720089 = 540067) B540067
theorem B228619 : Blo 211809 228619 := bstep (se 1 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 228619 = 342929) B342929
theorem B2489777 : Blo 211809 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B360011 : Blo 211809 360011 := bstep (se 1 (by rfl) ⟨270008, by rfl⟩ : syracuseStep 360011 = 540017) B540017
theorem B3899011 : Blo 211809 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B818819 : Blo 211809 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B360139 : Blo 211809 360139 := bstep (se 1 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 360139 = 540209) B540209
theorem B1834757 : Blo 211809 1834757 := bstep (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) B344017
theorem B360281 : Blo 211809 360281 := bstep (se 2 (by rfl) ⟨135105, by rfl⟩ : syracuseStep 360281 = 270211) B270211
theorem B3735395 : Blo 211809 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B720791 : Blo 211809 720791 := bstep (se 1 (by rfl) ⟨540593, by rfl⟩ : syracuseStep 720791 = 1081187) B1081187
theorem B3112921 : Blo 211809 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B360409 : Blo 211809 360409 := bstep (se 2 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 360409 = 270307) B270307
theorem B360463 : Blo 211809 360463 := bstep (se 1 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 360463 = 540695) B540695
theorem B589853 : Blo 211809 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B2326877 : Blo 211809 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B1638791 : Blo 211809 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B361003 : Blo 211809 361003 := bstep (se 1 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 361003 = 541505) B541505
theorem B361145 : Blo 211809 361145 := bstep (se 2 (by rfl) ⟨135429, by rfl⟩ : syracuseStep 361145 = 270859) B270859
theorem B1213217 : Blo 211809 1213217 := bstep (se 2 (by rfl) ⟨454956, by rfl⟩ : syracuseStep 1213217 = 909913) B909913
theorem B721817 : Blo 211809 721817 := bstep (se 2 (by rfl) ⟨270681, by rfl⟩ : syracuseStep 721817 = 541363) B541363
theorem B1082321 : Blo 211809 1082321 := bstep (se 2 (by rfl) ⟨405870, by rfl⟩ : syracuseStep 1082321 = 811741) B811741
theorem B689239 : Blo 211809 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B361847 : Blo 211809 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B460151 : Blo 211809 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B329131 : Blo 211809 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B689725 : Blo 211809 689725 := bstep (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) B258647
theorem B722519 : Blo 211809 722519 := bstep (se 1 (by rfl) ⟨541889, by rfl⟩ : syracuseStep 722519 = 1083779) B1083779
theorem B558881 : Blo 211809 558881 := bstep (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) B419161
theorem B4130605 : Blo 211809 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B362299 : Blo 211809 362299 := bstep (se 1 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 362299 = 543449) B543449
theorem B460603 : Blo 211809 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B362441 : Blo 211809 362441 := bstep (se 2 (by rfl) ⟨135915, by rfl⟩ : syracuseStep 362441 = 271831) B271831
theorem B723005 : Blo 211809 723005 := bstep (se 3 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 723005 = 271127) B271127
theorem B919619 : Blo 211809 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B1771721 : Blo 211809 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B330043 : Blo 211809 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B919943 : Blo 211809 919943 := bstep (se 1 (by rfl) ⟨689957, by rfl⟩ : syracuseStep 919943 = 1379915) B1379915
theorem B363143 : Blo 211809 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B2427569 : Blo 211809 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B3083123 : Blo 211809 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B1084427 : Blo 211809 1084427 := bstep (se 1 (by rfl) ⟨813320, by rfl⟩ : syracuseStep 1084427 = 1626641) B1626641
theorem B2362391 : Blo 211809 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B1215607 : Blo 211809 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B1084589 : Blo 211809 1084589 := bstep (se 3 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 1084589 = 406721) B406721
theorem B363791 : Blo 211809 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B1609145 : Blo 211809 1609145 := bstep (se 2 (by rfl) ⟨603429, by rfl⟩ : syracuseStep 1609145 = 1206859) B1206859
theorem B724409 : Blo 211809 724409 := bstep (se 2 (by rfl) ⟨271653, by rfl⟩ : syracuseStep 724409 = 543307) B543307
theorem B429715 : Blo 211809 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B725003 : Blo 211809 725003 := bstep (se 1 (by rfl) ⟨543752, by rfl⟩ : syracuseStep 725003 = 1087505) B1087505
theorem B364603 : Blo 211809 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B725111 : Blo 211809 725111 := bstep (se 1 (by rfl) ⟨543833, by rfl⟩ : syracuseStep 725111 = 1087667) B1087667
theorem B921719 : Blo 211809 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B1216883 : Blo 211809 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1151441 : Blo 211809 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B725705 : Blo 211809 725705 := bstep (se 2 (by rfl) ⟨272139, by rfl⟩ : syracuseStep 725705 = 544279) B544279
theorem B1086209 : Blo 211809 1086209 := bstep (se 2 (by rfl) ⟨407328, by rfl⟩ : syracuseStep 1086209 = 814657) B814657
theorem B1217339 : Blo 211809 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B1643417 : Blo 211809 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B365753 : Blo 211809 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B726407 : Blo 211809 726407 := bstep (se 1 (by rfl) ⟨544805, by rfl⟩ : syracuseStep 726407 = 1089611) B1089611
theorem B1087019 : Blo 211809 1087019 := bstep (se 1 (by rfl) ⟨815264, by rfl⟩ : syracuseStep 1087019 = 1630529) B1630529
theorem B726785 : Blo 211809 726785 := bstep (se 2 (by rfl) ⟨272544, by rfl⟩ : syracuseStep 726785 = 545089) B545089
theorem B1218341 : Blo 211809 1218341 := bstep (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) B228439
theorem B1742755 : Blo 211809 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1218797 : Blo 211809 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B268535 : Blo 211809 268535 := bstep (se 1 (by rfl) ⟨201401, by rfl⟩ : syracuseStep 268535 = 402803) B402803
theorem B3873041 : Blo 211809 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B465185 : Blo 211809 465185 := bstep (se 2 (by rfl) ⟨174444, by rfl⟩ : syracuseStep 465185 = 348889) B348889
theorem B268687 : Blo 211809 268687 := bstep (se 1 (by rfl) ⟨201515, by rfl⟩ : syracuseStep 268687 = 403031) B403031
theorem B235963 : Blo 211809 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B727595 : Blo 211809 727595 := bstep (se 1 (by rfl) ⟨545696, by rfl⟩ : syracuseStep 727595 = 1091393) B1091393
theorem B268859 : Blo 211809 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B2071331 : Blo 211809 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B1088315 : Blo 211809 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B301897 : Blo 211809 301897 := bstep (se 2 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 301897 = 226423) B226423
theorem B1219481 : Blo 211809 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B1088477 : Blo 211809 1088477 := bstep (se 3 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 1088477 = 408179) B408179
theorem B4365373 : Blo 211809 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B1088801 : Blo 211809 1088801 := bstep (se 2 (by rfl) ⟨408300, by rfl⟩ : syracuseStep 1088801 = 816601) B816601
theorem B302393 : Blo 211809 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B269831 : Blo 211809 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B728605 : Blo 211809 728605 := bstep (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) B273227
theorem B5283427 : Blo 211809 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B2793217 : Blo 211809 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B270479 : Blo 211809 270479 := bstep (se 1 (by rfl) ⟨202859, by rfl⟩ : syracuseStep 270479 = 405719) B405719
theorem B1089773 : Blo 211809 1089773 := bstep (se 3 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 1089773 = 408665) B408665
theorem B303367 : Blo 211809 303367 := bstep (se 1 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 303367 = 455051) B455051
theorem B729479 : Blo 211809 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B238351 : Blo 211809 238351 := bstep (se 1 (by rfl) ⟨178763, by rfl⟩ : syracuseStep 238351 = 357527) B357527
theorem B1024883 : Blo 211809 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B1090583 : Blo 211809 1090583 := bstep (se 1 (by rfl) ⟨817937, by rfl⟩ : syracuseStep 1090583 = 1635875) B1635875
theorem B238855 : Blo 211809 238855 := bstep (se 1 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 238855 = 358283) B358283
theorem B239035 : Blo 211809 239035 := bstep (se 1 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 239035 = 358553) B358553
theorem B435755 : Blo 211809 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B304825 : Blo 211809 304825 := bstep (se 2 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 304825 = 228619) B228619
theorem B403319 : Blo 211809 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B239503 : Blo 211809 239503 := bstep (se 1 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 239503 = 359255) B359255
theorem B403471 : Blo 211809 403471 := bstep (se 1 (by rfl) ⟨302603, by rfl⟩ : syracuseStep 403471 = 605207) B605207
theorem B240007 : Blo 211809 240007 := bstep (se 1 (by rfl) ⟨180005, by rfl⟩ : syracuseStep 240007 = 360011) B360011
theorem B403859 : Blo 211809 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B1223171 : Blo 211809 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B240187 : Blo 211809 240187 := bstep (se 1 (by rfl) ⟨180140, by rfl⟩ : syracuseStep 240187 = 360281) B360281
theorem B306055 : Blo 211809 306055 := bstep (se 1 (by rfl) ⟨229541, by rfl⟩ : syracuseStep 306055 = 459083) B459083
theorem B240655 : Blo 211809 240655 := bstep (se 1 (by rfl) ⟨180491, by rfl⟩ : syracuseStep 240655 = 360983) B360983
theorem B699479 : Blo 211809 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B1027343 : Blo 211809 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B241159 : Blo 211809 241159 := bstep (se 1 (by rfl) ⟨180869, by rfl⟩ : syracuseStep 241159 = 361739) B361739
theorem B536179 : Blo 211809 536179 := bstep (se 1 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 536179 = 804269) B804269
theorem B241339 : Blo 211809 241339 := bstep (se 1 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 241339 = 362009) B362009
theorem B306875 : Blo 211809 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B536321 : Blo 211809 536321 := bstep (se 2 (by rfl) ⟨201120, by rfl⟩ : syracuseStep 536321 = 402241) B402241
theorem B405263 : Blo 211809 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B241807 : Blo 211809 241807 := bstep (se 1 (by rfl) ⟨181355, by rfl⟩ : syracuseStep 241807 = 362711) B362711
theorem B536777 : Blo 211809 536777 := bstep (se 2 (by rfl) ⟨201291, by rfl⟩ : syracuseStep 536777 = 402583) B402583
theorem B405803 : Blo 211809 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B3322259 : Blo 211809 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B537131 : Blo 211809 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B242311 : Blo 211809 242311 := bstep (se 1 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 242311 = 363467) B363467
theorem B242491 : Blo 211809 242491 := bstep (se 1 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 242491 = 363737) B363737
theorem B2241433 : Blo 211809 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B8827825 : Blo 211809 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B767177 : Blo 211809 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B3519875 : Blo 211809 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B406919 : Blo 211809 406919 := bstep (se 1 (by rfl) ⟨305189, by rfl⟩ : syracuseStep 406919 = 610379) B610379
theorem B538123 : Blo 211809 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B538265 : Blo 211809 538265 := bstep (se 2 (by rfl) ⟨201849, by rfl⟩ : syracuseStep 538265 = 403699) B403699
theorem B538427 : Blo 211809 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B407443 : Blo 211809 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B604057 : Blo 211809 604057 := bstep (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) B453043
theorem B931769 : Blo 211809 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B1226819 : Blo 211809 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B538771 : Blo 211809 538771 := bstep (se 1 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 538771 = 808157) B808157
theorem B538913 : Blo 211809 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B3652289 : Blo 211809 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B1522547 : Blo 211809 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B211847 : Blo 211809 211847 := bstep (se 1 (by rfl) ⟨158885, by rfl⟩ : syracuseStep 211847 = 317771) B317771
theorem B211855 : Blo 211809 211855 := bstep (se 1 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 211855 = 317783) B317783
theorem B211899 : Blo 211809 211899 := bstep (se 1 (by rfl) ⟨158924, by rfl⟩ : syracuseStep 211899 = 317849) B317849
theorem B1358795 : Blo 211809 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B211975 : Blo 211809 211975 := bstep (se 1 (by rfl) ⟨158981, by rfl⟩ : syracuseStep 211975 = 317963) B317963
theorem B211983 : Blo 211809 211983 := bstep (se 1 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 211983 = 317975) B317975
theorem B212027 : Blo 211809 212027 := bstep (se 1 (by rfl) ⟨159020, by rfl⟩ : syracuseStep 212027 = 318041) B318041
theorem B408635 : Blo 211809 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B212103 : Blo 211809 212103 := bstep (se 1 (by rfl) ⟨159077, by rfl⟩ : syracuseStep 212103 = 318155) B318155
theorem B212111 : Blo 211809 212111 := bstep (se 1 (by rfl) ⟨159083, by rfl⟩ : syracuseStep 212111 = 318167) B318167
theorem B212155 : Blo 211809 212155 := bstep (se 1 (by rfl) ⟨159116, by rfl⟩ : syracuseStep 212155 = 318233) B318233
theorem B539905 : Blo 211809 539905 := bstep (se 2 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 539905 = 404929) B404929
theorem B212231 : Blo 211809 212231 := bstep (se 1 (by rfl) ⟨159173, by rfl⟩ : syracuseStep 212231 = 318347) B318347
theorem B212239 : Blo 211809 212239 := bstep (se 1 (by rfl) ⟨159179, by rfl⟩ : syracuseStep 212239 = 318359) B318359
theorem B867617 : Blo 211809 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B212283 : Blo 211809 212283 := bstep (se 1 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 212283 = 318425) B318425
theorem B212359 : Blo 211809 212359 := bstep (se 1 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 212359 = 318539) B318539
theorem B212367 : Blo 211809 212367 := bstep (se 1 (by rfl) ⟨159275, by rfl⟩ : syracuseStep 212367 = 318551) B318551
theorem B212411 : Blo 211809 212411 := bstep (se 1 (by rfl) ⟨159308, by rfl⟩ : syracuseStep 212411 = 318617) B318617
theorem B212487 : Blo 211809 212487 := bstep (se 1 (by rfl) ⟨159365, by rfl⟩ : syracuseStep 212487 = 318731) B318731
theorem B212495 : Blo 211809 212495 := bstep (se 1 (by rfl) ⟨159371, by rfl⟩ : syracuseStep 212495 = 318743) B318743
theorem B409121 : Blo 211809 409121 := bstep (se 2 (by rfl) ⟨153420, by rfl⟩ : syracuseStep 409121 = 306841) B306841
theorem B343595 : Blo 211809 343595 := bstep (se 1 (by rfl) ⟨257696, by rfl⟩ : syracuseStep 343595 = 515393) B515393
theorem B212539 : Blo 211809 212539 := bstep (se 1 (by rfl) ⟨159404, by rfl⟩ : syracuseStep 212539 = 318809) B318809
theorem B212615 : Blo 211809 212615 := bstep (se 1 (by rfl) ⟨159461, by rfl⟩ : syracuseStep 212615 = 318923) B318923
theorem B212623 : Blo 211809 212623 := bstep (se 1 (by rfl) ⟨159467, by rfl⟩ : syracuseStep 212623 = 318935) B318935
theorem B212667 : Blo 211809 212667 := bstep (se 1 (by rfl) ⟨159500, by rfl⟩ : syracuseStep 212667 = 319001) B319001
theorem B212743 : Blo 211809 212743 := bstep (se 1 (by rfl) ⟨159557, by rfl⟩ : syracuseStep 212743 = 319115) B319115
theorem B212751 : Blo 211809 212751 := bstep (se 1 (by rfl) ⟨159563, by rfl⟩ : syracuseStep 212751 = 319127) B319127
theorem B605981 : Blo 211809 605981 := bstep (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) B227243
theorem B409387 : Blo 211809 409387 := bstep (se 1 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 409387 = 614081) B614081
theorem B212795 : Blo 211809 212795 := bstep (se 1 (by rfl) ⟨159596, by rfl⟩ : syracuseStep 212795 = 319193) B319193
theorem B540503 : Blo 211809 540503 := bstep (se 1 (by rfl) ⟨405377, by rfl⟩ : syracuseStep 540503 = 810755) B810755
theorem B212871 : Blo 211809 212871 := bstep (se 1 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 212871 = 319307) B319307
theorem B212879 : Blo 211809 212879 := bstep (se 1 (by rfl) ⟨159659, by rfl⟩ : syracuseStep 212879 = 319319) B319319
theorem B1228729 : Blo 211809 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B212923 : Blo 211809 212923 := bstep (se 1 (by rfl) ⟨159692, by rfl⟩ : syracuseStep 212923 = 319385) B319385
theorem B212999 : Blo 211809 212999 := bstep (se 1 (by rfl) ⟨159749, by rfl⟩ : syracuseStep 212999 = 319499) B319499
theorem B213007 : Blo 211809 213007 := bstep (se 1 (by rfl) ⟨159755, by rfl⟩ : syracuseStep 213007 = 319511) B319511
theorem B540715 : Blo 211809 540715 := bstep (se 1 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 540715 = 811073) B811073
theorem B213051 : Blo 211809 213051 := bstep (se 1 (by rfl) ⟨159788, by rfl⟩ : syracuseStep 213051 = 319577) B319577
theorem B213127 : Blo 211809 213127 := bstep (se 1 (by rfl) ⟨159845, by rfl⟩ : syracuseStep 213127 = 319691) B319691
theorem B213135 : Blo 211809 213135 := bstep (se 1 (by rfl) ⟨159851, by rfl⟩ : syracuseStep 213135 = 319703) B319703
theorem B409747 : Blo 211809 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B540857 : Blo 211809 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B213179 : Blo 211809 213179 := bstep (se 1 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 213179 = 319769) B319769
theorem B213255 : Blo 211809 213255 := bstep (se 1 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 213255 = 319883) B319883
theorem B213263 : Blo 211809 213263 := bstep (se 1 (by rfl) ⟨159947, by rfl⟩ : syracuseStep 213263 = 319895) B319895
theorem B213307 : Blo 211809 213307 := bstep (se 1 (by rfl) ⟨159980, by rfl⟩ : syracuseStep 213307 = 319961) B319961
theorem B213383 : Blo 211809 213383 := bstep (se 1 (by rfl) ⟨160037, by rfl⟩ : syracuseStep 213383 = 320075) B320075
theorem B213391 : Blo 211809 213391 := bstep (se 1 (by rfl) ⟨160043, by rfl⟩ : syracuseStep 213391 = 320087) B320087
theorem B213435 : Blo 211809 213435 := bstep (se 1 (by rfl) ⟨160076, by rfl⟩ : syracuseStep 213435 = 320153) B320153
theorem B606665 : Blo 211809 606665 := bstep (se 2 (by rfl) ⟨227499, by rfl⟩ : syracuseStep 606665 = 454999) B454999
theorem B213511 : Blo 211809 213511 := bstep (se 1 (by rfl) ⟨160133, by rfl⟩ : syracuseStep 213511 = 320267) B320267
theorem B213519 : Blo 211809 213519 := bstep (se 1 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 213519 = 320279) B320279
theorem B213563 : Blo 211809 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B213639 : Blo 211809 213639 := bstep (se 1 (by rfl) ⟨160229, by rfl⟩ : syracuseStep 213639 = 320459) B320459
theorem B213647 : Blo 211809 213647 := bstep (se 1 (by rfl) ⟨160235, by rfl⟩ : syracuseStep 213647 = 320471) B320471
theorem B9814709 : Blo 211809 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B213691 : Blo 211809 213691 := bstep (se 1 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 213691 = 320537) B320537
theorem B213767 : Blo 211809 213767 := bstep (se 1 (by rfl) ⟨160325, by rfl⟩ : syracuseStep 213767 = 320651) B320651
theorem B213775 : Blo 211809 213775 := bstep (se 1 (by rfl) ⟨160331, by rfl⟩ : syracuseStep 213775 = 320663) B320663
theorem B3261221 : Blo 211809 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B213819 : Blo 211809 213819 := bstep (se 1 (by rfl) ⟨160364, by rfl⟩ : syracuseStep 213819 = 320729) B320729
theorem B213895 : Blo 211809 213895 := bstep (se 1 (by rfl) ⟨160421, by rfl⟩ : syracuseStep 213895 = 320843) B320843
theorem B213903 : Blo 211809 213903 := bstep (se 1 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 213903 = 320855) B320855
theorem B1360793 : Blo 211809 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B213947 : Blo 211809 213947 := bstep (se 1 (by rfl) ⟨160460, by rfl⟩ : syracuseStep 213947 = 320921) B320921
theorem B15516629 : Blo 211809 15516629 := bstep (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) B363671
theorem B214023 : Blo 211809 214023 := bstep (se 1 (by rfl) ⟨160517, by rfl⟩ : syracuseStep 214023 = 321035) B321035
theorem B607247 : Blo 211809 607247 := bstep (se 1 (by rfl) ⟨455435, by rfl⟩ : syracuseStep 607247 = 910871) B910871
theorem B214031 : Blo 211809 214031 := bstep (se 1 (by rfl) ⟨160523, by rfl⟩ : syracuseStep 214031 = 321047) B321047
theorem B214075 : Blo 211809 214075 := bstep (se 1 (by rfl) ⟨160556, by rfl⟩ : syracuseStep 214075 = 321113) B321113
theorem B214151 : Blo 211809 214151 := bstep (se 1 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 214151 = 321227) B321227
theorem B214159 : Blo 211809 214159 := bstep (se 1 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 214159 = 321239) B321239
theorem B541849 : Blo 211809 541849 := bstep (se 2 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 541849 = 406387) B406387
theorem B214203 : Blo 211809 214203 := bstep (se 1 (by rfl) ⟨160652, by rfl⟩ : syracuseStep 214203 = 321305) B321305
theorem B214279 : Blo 211809 214279 := bstep (se 1 (by rfl) ⟨160709, by rfl⟩ : syracuseStep 214279 = 321419) B321419
theorem B214287 : Blo 211809 214287 := bstep (se 1 (by rfl) ⟨160715, by rfl⟩ : syracuseStep 214287 = 321431) B321431
theorem B542011 : Blo 211809 542011 := bstep (se 1 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 542011 = 813017) B813017
theorem B214331 : Blo 211809 214331 := bstep (se 1 (by rfl) ⟨160748, by rfl⟩ : syracuseStep 214331 = 321497) B321497
theorem B214407 : Blo 211809 214407 := bstep (se 1 (by rfl) ⟨160805, by rfl⟩ : syracuseStep 214407 = 321611) B321611
theorem B214415 : Blo 211809 214415 := bstep (se 1 (by rfl) ⟨160811, by rfl⟩ : syracuseStep 214415 = 321623) B321623
theorem B345529 : Blo 211809 345529 := bstep (se 2 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 345529 = 259147) B259147
theorem B214459 : Blo 211809 214459 := bstep (se 1 (by rfl) ⟨160844, by rfl⟩ : syracuseStep 214459 = 321689) B321689
theorem B542153 : Blo 211809 542153 := bstep (se 2 (by rfl) ⟨203307, by rfl⟩ : syracuseStep 542153 = 406615) B406615
theorem B214535 : Blo 211809 214535 := bstep (se 1 (by rfl) ⟨160901, by rfl⟩ : syracuseStep 214535 = 321803) B321803
theorem B738827 : Blo 211809 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B214543 : Blo 211809 214543 := bstep (se 1 (by rfl) ⟨160907, by rfl⟩ : syracuseStep 214543 = 321815) B321815
theorem B214587 : Blo 211809 214587 := bstep (se 1 (by rfl) ⟨160940, by rfl⟩ : syracuseStep 214587 = 321881) B321881
theorem B214663 : Blo 211809 214663 := bstep (se 1 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 214663 = 321995) B321995
theorem B214671 : Blo 211809 214671 := bstep (se 1 (by rfl) ⟨161003, by rfl⟩ : syracuseStep 214671 = 322007) B322007
theorem B476819 : Blo 211809 476819 := bstep (se 1 (by rfl) ⟨357614, by rfl⟩ : syracuseStep 476819 = 715229) B715229
theorem B10798771 : Blo 211809 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B214715 : Blo 211809 214715 := bstep (se 1 (by rfl) ⟨161036, by rfl⟩ : syracuseStep 214715 = 322073) B322073
theorem B476873 : Blo 211809 476873 := bstep (se 2 (by rfl) ⟨178827, by rfl⟩ : syracuseStep 476873 = 357655) B357655
theorem B214791 : Blo 211809 214791 := bstep (se 1 (by rfl) ⟨161093, by rfl⟩ : syracuseStep 214791 = 322187) B322187
theorem B214799 : Blo 211809 214799 := bstep (se 1 (by rfl) ⟨161099, by rfl⟩ : syracuseStep 214799 = 322199) B322199
theorem B542497 : Blo 211809 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B214843 : Blo 211809 214843 := bstep (se 1 (by rfl) ⟨161132, by rfl⟩ : syracuseStep 214843 = 322265) B322265
theorem B214919 : Blo 211809 214919 := bstep (se 1 (by rfl) ⟨161189, by rfl⟩ : syracuseStep 214919 = 322379) B322379
theorem B214927 : Blo 211809 214927 := bstep (se 1 (by rfl) ⟨161195, by rfl⟩ : syracuseStep 214927 = 322391) B322391
theorem B804755 : Blo 211809 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B214971 : Blo 211809 214971 := bstep (se 1 (by rfl) ⟨161228, by rfl⟩ : syracuseStep 214971 = 322457) B322457
theorem B215047 : Blo 211809 215047 := bstep (se 1 (by rfl) ⟨161285, by rfl⟩ : syracuseStep 215047 = 322571) B322571
theorem B215055 : Blo 211809 215055 := bstep (se 1 (by rfl) ⟨161291, by rfl⟩ : syracuseStep 215055 = 322583) B322583
theorem B1296413 : Blo 211809 1296413 := bstep (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) B486155
theorem B215099 : Blo 211809 215099 := bstep (se 1 (by rfl) ⟨161324, by rfl⟩ : syracuseStep 215099 = 322649) B322649
theorem B2050109 : Blo 211809 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B510067 : Blo 211809 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B215175 : Blo 211809 215175 := bstep (se 1 (by rfl) ⟨161381, by rfl⟩ : syracuseStep 215175 = 322763) B322763
theorem B215183 : Blo 211809 215183 := bstep (se 1 (by rfl) ⟨161387, by rfl⟩ : syracuseStep 215183 = 322775) B322775
theorem B215227 : Blo 211809 215227 := bstep (se 1 (by rfl) ⟨161420, by rfl⟩ : syracuseStep 215227 = 322841) B322841
theorem B215303 : Blo 211809 215303 := bstep (se 1 (by rfl) ⟨161477, by rfl⟩ : syracuseStep 215303 = 322955) B322955
theorem B215311 : Blo 211809 215311 := bstep (se 1 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 215311 = 322967) B322967
theorem B215355 : Blo 211809 215355 := bstep (se 1 (by rfl) ⟨161516, by rfl⟩ : syracuseStep 215355 = 323033) B323033
theorem B1296755 : Blo 211809 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B543095 : Blo 211809 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B477575 : Blo 211809 477575 := bstep (se 1 (by rfl) ⟨358181, by rfl⟩ : syracuseStep 477575 = 716363) B716363
theorem B608647 : Blo 211809 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B215431 : Blo 211809 215431 := bstep (se 1 (by rfl) ⟨161573, by rfl⟩ : syracuseStep 215431 = 323147) B323147
theorem B215439 : Blo 211809 215439 := bstep (se 1 (by rfl) ⟨161579, by rfl⟩ : syracuseStep 215439 = 323159) B323159
theorem B215483 : Blo 211809 215483 := bstep (se 1 (by rfl) ⟨161612, by rfl⟩ : syracuseStep 215483 = 323225) B323225
theorem B215559 : Blo 211809 215559 := bstep (se 1 (by rfl) ⟨161669, by rfl⟩ : syracuseStep 215559 = 323339) B323339
theorem B576011 : Blo 211809 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B215567 : Blo 211809 215567 := bstep (se 1 (by rfl) ⟨161675, by rfl⟩ : syracuseStep 215567 = 323351) B323351
theorem B4999715 : Blo 211809 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B477755 : Blo 211809 477755 := bstep (se 1 (by rfl) ⟨358316, by rfl⟩ : syracuseStep 477755 = 716633) B716633
theorem B215611 : Blo 211809 215611 := bstep (se 1 (by rfl) ⟨161708, by rfl⟩ : syracuseStep 215611 = 323417) B323417
theorem B1100375 : Blo 211809 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B215687 : Blo 211809 215687 := bstep (se 1 (by rfl) ⟨161765, by rfl⟩ : syracuseStep 215687 = 323531) B323531
theorem B215695 : Blo 211809 215695 := bstep (se 1 (by rfl) ⟨161771, by rfl⟩ : syracuseStep 215695 = 323543) B323543
theorem B608921 : Blo 211809 608921 := bstep (se 2 (by rfl) ⟨228345, by rfl⟩ : syracuseStep 608921 = 456691) B456691
theorem B477881 : Blo 211809 477881 := bstep (se 2 (by rfl) ⟨179205, by rfl⟩ : syracuseStep 477881 = 358411) B358411
theorem B215739 : Blo 211809 215739 := bstep (se 1 (by rfl) ⟨161804, by rfl⟩ : syracuseStep 215739 = 323609) B323609
theorem B510779 : Blo 211809 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B1166339 : Blo 211809 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B478223 : Blo 211809 478223 := bstep (se 1 (by rfl) ⟨358667, by rfl⟩ : syracuseStep 478223 = 717335) B717335
theorem B478241 : Blo 211809 478241 := bstep (se 2 (by rfl) ⟨179340, by rfl⟩ : syracuseStep 478241 = 358681) B358681
theorem B478583 : Blo 211809 478583 := bstep (se 1 (by rfl) ⟨358937, by rfl⟩ : syracuseStep 478583 = 717875) B717875
theorem B3067267 : Blo 211809 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B2969041 : Blo 211809 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B478763 : Blo 211809 478763 := bstep (se 1 (by rfl) ⟨359072, by rfl⟩ : syracuseStep 478763 = 718145) B718145
theorem B544391 : Blo 211809 544391 := bstep (se 1 (by rfl) ⟨408293, by rfl⟩ : syracuseStep 544391 = 816587) B816587
theorem B544441 : Blo 211809 544441 := bstep (se 2 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 544441 = 408331) B408331
theorem B2051801 : Blo 211809 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B2215795 : Blo 211809 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B610163 : Blo 211809 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B479123 : Blo 211809 479123 := bstep (se 1 (by rfl) ⟨359342, by rfl⟩ : syracuseStep 479123 = 718685) B718685
theorem B479177 : Blo 211809 479177 := bstep (se 2 (by rfl) ⟨179691, by rfl⟩ : syracuseStep 479177 = 359383) B359383
theorem B512135 : Blo 211809 512135 := bstep (se 1 (by rfl) ⟨384101, by rfl⟩ : syracuseStep 512135 = 768203) B768203
theorem B1102061 : Blo 211809 1102061 := bstep (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) B413273
theorem B545039 : Blo 211809 545039 := bstep (se 1 (by rfl) ⟨408779, by rfl⟩ : syracuseStep 545039 = 817559) B817559
theorem B1986875 : Blo 211809 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B807353 : Blo 211809 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B479879 : Blo 211809 479879 := bstep (se 1 (by rfl) ⟨359909, by rfl⟩ : syracuseStep 479879 = 719819) B719819
theorem B480059 : Blo 211809 480059 := bstep (se 1 (by rfl) ⟨360044, by rfl⟩ : syracuseStep 480059 = 720089) B720089
theorem B5198681 : Blo 211809 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B906137 : Blo 211809 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B480185 : Blo 211809 480185 := bstep (se 2 (by rfl) ⟨180069, by rfl⟩ : syracuseStep 480185 = 360139) B360139
theorem B545737 : Blo 211809 545737 := bstep (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) B409303
theorem B1659851 : Blo 211809 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B3626045 : Blo 211809 3626045 := bstep (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) B1359767
theorem B545879 : Blo 211809 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B906497 : Blo 211809 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B480527 : Blo 211809 480527 := bstep (se 1 (by rfl) ⟨360395, by rfl⟩ : syracuseStep 480527 = 720791) B720791
theorem B4150561 : Blo 211809 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 211809 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B480545 : Blo 211809 480545 := bstep (se 2 (by rfl) ⟨180204, by rfl⟩ : syracuseStep 480545 = 360409) B360409
theorem B808339 : Blo 211809 808339 := bstep (se 1 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 808339 = 1212509) B1212509
theorem B1627613 : Blo 211809 1627613 := bstep (se 3 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 1627613 = 610355) B610355
theorem B2610731 : Blo 211809 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B644669 : Blo 211809 644669 := bstep (se 3 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 644669 = 241751) B241751
theorem B480887 : Blo 211809 480887 := bstep (se 1 (by rfl) ⟨360665, by rfl⟩ : syracuseStep 480887 = 721331) B721331
theorem B481067 : Blo 211809 481067 := bstep (se 1 (by rfl) ⟨360800, by rfl⟩ : syracuseStep 481067 = 721601) B721601
theorem B513911 : Blo 211809 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B481427 : Blo 211809 481427 := bstep (se 1 (by rfl) ⟨361070, by rfl⟩ : syracuseStep 481427 = 722141) B722141
theorem B481481 : Blo 211809 481481 := bstep (se 2 (by rfl) ⟨180555, by rfl⟩ : syracuseStep 481481 = 361111) B361111
theorem B612623 : Blo 211809 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B317753 : Blo 211809 317753 := bstep (se 2 (by rfl) ⟨119157, by rfl⟩ : syracuseStep 317753 = 238315) B238315
theorem B317831 : Blo 211809 317831 := bstep (se 1 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 317831 = 476747) B476747
theorem B317867 : Blo 211809 317867 := bstep (se 1 (by rfl) ⟨238400, by rfl⟩ : syracuseStep 317867 = 476801) B476801
theorem B776633 : Blo 211809 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B317897 : Blo 211809 317897 := bstep (se 2 (by rfl) ⟨119211, by rfl⟩ : syracuseStep 317897 = 238423) B238423
theorem B514603 : Blo 211809 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B318011 : Blo 211809 318011 := bstep (se 1 (by rfl) ⟨238508, by rfl⟩ : syracuseStep 318011 = 477017) B477017
theorem B318071 : Blo 211809 318071 := bstep (se 1 (by rfl) ⟨238553, by rfl⟩ : syracuseStep 318071 = 477107) B477107
theorem B318095 : Blo 211809 318095 := bstep (se 1 (by rfl) ⟨238571, by rfl⟩ : syracuseStep 318095 = 477143) B477143
theorem B318137 : Blo 211809 318137 := bstep (se 2 (by rfl) ⟨119301, by rfl⟩ : syracuseStep 318137 = 238603) B238603
theorem B318215 : Blo 211809 318215 := bstep (se 1 (by rfl) ⟨238661, by rfl⟩ : syracuseStep 318215 = 477323) B477323
theorem B318251 : Blo 211809 318251 := bstep (se 1 (by rfl) ⟨238688, by rfl⟩ : syracuseStep 318251 = 477377) B477377
theorem B318281 : Blo 211809 318281 := bstep (se 2 (by rfl) ⟨119355, by rfl⟩ : syracuseStep 318281 = 238711) B238711
theorem B2513753 : Blo 211809 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B482183 : Blo 211809 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B318395 : Blo 211809 318395 := bstep (se 1 (by rfl) ⟨238796, by rfl⟩ : syracuseStep 318395 = 477593) B477593
theorem B318455 : Blo 211809 318455 := bstep (se 1 (by rfl) ⟨238841, by rfl⟩ : syracuseStep 318455 = 477683) B477683
theorem B318479 : Blo 211809 318479 := bstep (se 1 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 318479 = 477719) B477719
theorem B318521 : Blo 211809 318521 := bstep (se 2 (by rfl) ⟨119445, by rfl⟩ : syracuseStep 318521 = 238891) B238891
theorem B482363 : Blo 211809 482363 := bstep (se 1 (by rfl) ⟨361772, by rfl⟩ : syracuseStep 482363 = 723545) B723545
theorem B810071 : Blo 211809 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B318599 : Blo 211809 318599 := bstep (se 1 (by rfl) ⟨238949, by rfl⟩ : syracuseStep 318599 = 477899) B477899
theorem B318635 : Blo 211809 318635 := bstep (se 1 (by rfl) ⟨238976, by rfl⟩ : syracuseStep 318635 = 477953) B477953
theorem B482489 : Blo 211809 482489 := bstep (se 2 (by rfl) ⟨180933, by rfl⟩ : syracuseStep 482489 = 361867) B361867
theorem B318665 : Blo 211809 318665 := bstep (se 2 (by rfl) ⟨119499, by rfl⟩ : syracuseStep 318665 = 238999) B238999
theorem B3661037 : Blo 211809 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B2415905 : Blo 211809 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B318779 : Blo 211809 318779 := bstep (se 1 (by rfl) ⟨239084, by rfl⟩ : syracuseStep 318779 = 478169) B478169
theorem B318839 : Blo 211809 318839 := bstep (se 1 (by rfl) ⟨239129, by rfl⟩ : syracuseStep 318839 = 478259) B478259
theorem B318863 : Blo 211809 318863 := bstep (se 1 (by rfl) ⟨239147, by rfl⟩ : syracuseStep 318863 = 478295) B478295
theorem B941465 : Blo 211809 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B318905 : Blo 211809 318905 := bstep (se 2 (by rfl) ⟨119589, by rfl⟩ : syracuseStep 318905 = 239179) B239179
theorem B318983 : Blo 211809 318983 := bstep (se 1 (by rfl) ⟨239237, by rfl⟩ : syracuseStep 318983 = 478475) B478475
theorem B482831 : Blo 211809 482831 := bstep (se 1 (by rfl) ⟨362123, by rfl⟩ : syracuseStep 482831 = 724247) B724247
theorem B482849 : Blo 211809 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B319019 : Blo 211809 319019 := bstep (se 1 (by rfl) ⟨239264, by rfl⟩ : syracuseStep 319019 = 478529) B478529
theorem B810557 : Blo 211809 810557 := bstep (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) B303959
theorem B319049 : Blo 211809 319049 := bstep (se 2 (by rfl) ⟨119643, by rfl⟩ : syracuseStep 319049 = 239287) B239287
theorem B319163 : Blo 211809 319163 := bstep (se 1 (by rfl) ⟨239372, by rfl⟩ : syracuseStep 319163 = 478745) B478745
theorem B319223 : Blo 211809 319223 := bstep (se 1 (by rfl) ⟨239417, by rfl⟩ : syracuseStep 319223 = 478835) B478835
theorem B319247 : Blo 211809 319247 := bstep (se 1 (by rfl) ⟨239435, by rfl⟩ : syracuseStep 319247 = 478871) B478871
theorem B319289 : Blo 211809 319289 := bstep (se 2 (by rfl) ⟨119733, by rfl⟩ : syracuseStep 319289 = 239467) B239467
theorem B483191 : Blo 211809 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B614263 : Blo 211809 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B319367 : Blo 211809 319367 := bstep (se 1 (by rfl) ⟨239525, by rfl⟩ : syracuseStep 319367 = 479051) B479051
theorem B614297 : Blo 211809 614297 := bstep (se 2 (by rfl) ⟨230361, by rfl⟩ : syracuseStep 614297 = 460723) B460723
theorem B319403 : Blo 211809 319403 := bstep (se 1 (by rfl) ⟨239552, by rfl⟩ : syracuseStep 319403 = 479105) B479105
theorem B319433 : Blo 211809 319433 := bstep (se 2 (by rfl) ⟨119787, by rfl⟩ : syracuseStep 319433 = 239575) B239575
theorem B614411 : Blo 211809 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B483371 : Blo 211809 483371 := bstep (se 1 (by rfl) ⟨362528, by rfl⟩ : syracuseStep 483371 = 725057) B725057
theorem B319547 : Blo 211809 319547 := bstep (se 1 (by rfl) ⟨239660, by rfl⟩ : syracuseStep 319547 = 479321) B479321
theorem B319607 : Blo 211809 319607 := bstep (se 1 (by rfl) ⟨239705, by rfl⟩ : syracuseStep 319607 = 479411) B479411
theorem B319631 : Blo 211809 319631 := bstep (se 1 (by rfl) ⟨239723, by rfl⟩ : syracuseStep 319631 = 479447) B479447
theorem B319673 : Blo 211809 319673 := bstep (se 2 (by rfl) ⟨119877, by rfl⟩ : syracuseStep 319673 = 239755) B239755
theorem B286967 : Blo 211809 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B319751 : Blo 211809 319751 := bstep (se 1 (by rfl) ⟨239813, by rfl⟩ : syracuseStep 319751 = 479627) B479627
theorem B319787 : Blo 211809 319787 := bstep (se 1 (by rfl) ⟨239840, by rfl⟩ : syracuseStep 319787 = 479681) B479681
theorem B319817 : Blo 211809 319817 := bstep (se 2 (by rfl) ⟨119931, by rfl⟩ : syracuseStep 319817 = 239863) B239863
theorem B483731 : Blo 211809 483731 := bstep (se 1 (by rfl) ⟨362798, by rfl⟩ : syracuseStep 483731 = 725597) B725597
theorem B319931 : Blo 211809 319931 := bstep (se 1 (by rfl) ⟨239948, by rfl⟩ : syracuseStep 319931 = 479897) B479897
theorem B483785 : Blo 211809 483785 := bstep (se 2 (by rfl) ⟨181419, by rfl⟩ : syracuseStep 483785 = 362839) B362839
theorem B319991 : Blo 211809 319991 := bstep (se 1 (by rfl) ⟨239993, by rfl⟩ : syracuseStep 319991 = 479987) B479987
theorem B2089475 : Blo 211809 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B320015 : Blo 211809 320015 := bstep (se 1 (by rfl) ⟨240011, by rfl⟩ : syracuseStep 320015 = 480023) B480023
theorem B320057 : Blo 211809 320057 := bstep (se 2 (by rfl) ⟨120021, by rfl⟩ : syracuseStep 320057 = 240043) B240043
theorem B320135 : Blo 211809 320135 := bstep (se 1 (by rfl) ⟨240101, by rfl⟩ : syracuseStep 320135 = 480203) B480203
theorem B320171 : Blo 211809 320171 := bstep (se 1 (by rfl) ⟨240128, by rfl⟩ : syracuseStep 320171 = 480257) B480257
theorem B320201 : Blo 211809 320201 := bstep (se 2 (by rfl) ⟨120075, by rfl⟩ : syracuseStep 320201 = 240151) B240151
theorem B320315 : Blo 211809 320315 := bstep (se 1 (by rfl) ⟨240236, by rfl⟩ : syracuseStep 320315 = 480473) B480473
theorem B320375 : Blo 211809 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B320399 : Blo 211809 320399 := bstep (se 1 (by rfl) ⟨240299, by rfl⟩ : syracuseStep 320399 = 480599) B480599
theorem B320441 : Blo 211809 320441 := bstep (se 2 (by rfl) ⟨120165, by rfl⟩ : syracuseStep 320441 = 240331) B240331
theorem B320519 : Blo 211809 320519 := bstep (se 1 (by rfl) ⟨240389, by rfl⟩ : syracuseStep 320519 = 480779) B480779
theorem B320555 : Blo 211809 320555 := bstep (se 1 (by rfl) ⟨240416, by rfl⟩ : syracuseStep 320555 = 480833) B480833
theorem B320585 : Blo 211809 320585 := bstep (se 2 (by rfl) ⟨120219, by rfl⟩ : syracuseStep 320585 = 240439) B240439
theorem B484487 : Blo 211809 484487 := bstep (se 1 (by rfl) ⟨363365, by rfl⟩ : syracuseStep 484487 = 726731) B726731
theorem B320699 : Blo 211809 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B320759 : Blo 211809 320759 := bstep (se 1 (by rfl) ⟨240569, by rfl⟩ : syracuseStep 320759 = 481139) B481139
theorem B320783 : Blo 211809 320783 := bstep (se 1 (by rfl) ⟨240587, by rfl⟩ : syracuseStep 320783 = 481175) B481175
theorem B320825 : Blo 211809 320825 := bstep (se 2 (by rfl) ⟨120309, by rfl⟩ : syracuseStep 320825 = 240619) B240619
theorem B484667 : Blo 211809 484667 := bstep (se 1 (by rfl) ⟨363500, by rfl⟩ : syracuseStep 484667 = 727001) B727001
theorem B320903 : Blo 211809 320903 := bstep (se 1 (by rfl) ⟨240677, by rfl⟩ : syracuseStep 320903 = 481355) B481355
theorem B320939 : Blo 211809 320939 := bstep (se 1 (by rfl) ⟨240704, by rfl⟩ : syracuseStep 320939 = 481409) B481409
theorem B484793 : Blo 211809 484793 := bstep (se 2 (by rfl) ⟨181797, by rfl⟩ : syracuseStep 484793 = 363595) B363595
theorem B320969 : Blo 211809 320969 := bstep (se 2 (by rfl) ⟨120363, by rfl⟩ : syracuseStep 320969 = 240727) B240727
theorem B2450897 : Blo 211809 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B321083 : Blo 211809 321083 := bstep (se 1 (by rfl) ⟨240812, by rfl⟩ : syracuseStep 321083 = 481625) B481625
theorem B321143 : Blo 211809 321143 := bstep (se 1 (by rfl) ⟨240857, by rfl⟩ : syracuseStep 321143 = 481715) B481715
theorem B321167 : Blo 211809 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B288427 : Blo 211809 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B321209 : Blo 211809 321209 := bstep (se 2 (by rfl) ⟨120453, by rfl⟩ : syracuseStep 321209 = 240907) B240907
theorem B1795841 : Blo 211809 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B321287 : Blo 211809 321287 := bstep (se 1 (by rfl) ⟨240965, by rfl⟩ : syracuseStep 321287 = 481931) B481931
theorem B485135 : Blo 211809 485135 := bstep (se 1 (by rfl) ⟨363851, by rfl⟩ : syracuseStep 485135 = 727703) B727703
theorem B485153 : Blo 211809 485153 := bstep (se 2 (by rfl) ⟨181932, by rfl⟩ : syracuseStep 485153 = 363865) B363865
theorem B321323 : Blo 211809 321323 := bstep (se 1 (by rfl) ⟨240992, by rfl⟩ : syracuseStep 321323 = 481985) B481985
theorem B386875 : Blo 211809 386875 := bstep (se 1 (by rfl) ⟨290156, by rfl⟩ : syracuseStep 386875 = 580313) B580313
theorem B321353 : Blo 211809 321353 := bstep (se 2 (by rfl) ⟨120507, by rfl⟩ : syracuseStep 321353 = 241015) B241015
theorem B321467 : Blo 211809 321467 := bstep (se 1 (by rfl) ⟨241100, by rfl⟩ : syracuseStep 321467 = 482201) B482201
theorem B15591365 : Blo 211809 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B321527 : Blo 211809 321527 := bstep (se 1 (by rfl) ⟨241145, by rfl⟩ : syracuseStep 321527 = 482291) B482291
theorem B321551 : Blo 211809 321551 := bstep (se 1 (by rfl) ⟨241163, by rfl⟩ : syracuseStep 321551 = 482327) B482327
theorem B452641 : Blo 211809 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B321593 : Blo 211809 321593 := bstep (se 2 (by rfl) ⟨120597, by rfl⟩ : syracuseStep 321593 = 241195) B241195
theorem B1206359 : Blo 211809 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B485495 : Blo 211809 485495 := bstep (se 1 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 485495 = 728243) B728243
theorem B2418821 : Blo 211809 2418821 := bstep (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) B453529
theorem B321671 : Blo 211809 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B321707 : Blo 211809 321707 := bstep (se 1 (by rfl) ⟨241280, by rfl⟩ : syracuseStep 321707 = 482561) B482561
theorem B321737 : Blo 211809 321737 := bstep (se 2 (by rfl) ⟨120651, by rfl⟩ : syracuseStep 321737 = 241303) B241303
theorem B715067 : Blo 211809 715067 := bstep (se 1 (by rfl) ⟨536300, by rfl⟩ : syracuseStep 715067 = 1072601) B1072601
theorem B321851 : Blo 211809 321851 := bstep (se 1 (by rfl) ⟨241388, by rfl⟩ : syracuseStep 321851 = 482777) B482777
theorem B256375 : Blo 211809 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B321911 : Blo 211809 321911 := bstep (se 1 (by rfl) ⟨241433, by rfl⟩ : syracuseStep 321911 = 482867) B482867
theorem B321935 : Blo 211809 321935 := bstep (se 1 (by rfl) ⟨241451, by rfl⟩ : syracuseStep 321935 = 482903) B482903
theorem B321977 : Blo 211809 321977 := bstep (se 2 (by rfl) ⟨120741, by rfl⟩ : syracuseStep 321977 = 241483) B241483
theorem B322055 : Blo 211809 322055 := bstep (se 1 (by rfl) ⟨241541, by rfl⟩ : syracuseStep 322055 = 483083) B483083
theorem B322091 : Blo 211809 322091 := bstep (se 1 (by rfl) ⟨241568, by rfl⟩ : syracuseStep 322091 = 483137) B483137
theorem B322121 : Blo 211809 322121 := bstep (se 2 (by rfl) ⟨120795, by rfl⟩ : syracuseStep 322121 = 241591) B241591
theorem B322235 : Blo 211809 322235 := bstep (se 1 (by rfl) ⟨241676, by rfl⟩ : syracuseStep 322235 = 483353) B483353
theorem B322295 : Blo 211809 322295 := bstep (se 1 (by rfl) ⟨241721, by rfl⟩ : syracuseStep 322295 = 483443) B483443
theorem B322319 : Blo 211809 322319 := bstep (se 1 (by rfl) ⟨241739, by rfl⟩ : syracuseStep 322319 = 483479) B483479
theorem B715553 : Blo 211809 715553 := bstep (se 2 (by rfl) ⟨268332, by rfl⟩ : syracuseStep 715553 = 536665) B536665
theorem B322361 : Blo 211809 322361 := bstep (se 2 (by rfl) ⟨120885, by rfl⟩ : syracuseStep 322361 = 241771) B241771
theorem B813959 : Blo 211809 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B322439 : Blo 211809 322439 := bstep (se 1 (by rfl) ⟨241829, by rfl⟩ : syracuseStep 322439 = 483659) B483659
theorem B322475 : Blo 211809 322475 := bstep (se 1 (by rfl) ⟨241856, by rfl⟩ : syracuseStep 322475 = 483713) B483713
theorem B322505 : Blo 211809 322505 := bstep (se 2 (by rfl) ⟨120939, by rfl⟩ : syracuseStep 322505 = 241879) B241879
theorem B322619 : Blo 211809 322619 := bstep (se 1 (by rfl) ⟨241964, by rfl⟩ : syracuseStep 322619 = 483929) B483929
theorem B322679 : Blo 211809 322679 := bstep (se 1 (by rfl) ⟨242009, by rfl⟩ : syracuseStep 322679 = 484019) B484019
theorem B322703 : Blo 211809 322703 := bstep (se 1 (by rfl) ⟨242027, by rfl⟩ : syracuseStep 322703 = 484055) B484055
theorem B322745 : Blo 211809 322745 := bstep (se 2 (by rfl) ⟨121029, by rfl⟩ : syracuseStep 322745 = 242059) B242059
theorem B322823 : Blo 211809 322823 := bstep (se 1 (by rfl) ⟨242117, by rfl⟩ : syracuseStep 322823 = 484235) B484235
theorem B322859 : Blo 211809 322859 := bstep (se 1 (by rfl) ⟨242144, by rfl⟩ : syracuseStep 322859 = 484289) B484289
theorem B1240379 : Blo 211809 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B322889 : Blo 211809 322889 := bstep (se 2 (by rfl) ⟨121083, by rfl⟩ : syracuseStep 322889 = 242167) B242167
theorem B716147 : Blo 211809 716147 := bstep (se 1 (by rfl) ⟨537110, by rfl⟩ : syracuseStep 716147 = 1074221) B1074221
theorem B617843 : Blo 211809 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B323003 : Blo 211809 323003 := bstep (se 1 (by rfl) ⟨242252, by rfl⟩ : syracuseStep 323003 = 484505) B484505
theorem B323063 : Blo 211809 323063 := bstep (se 1 (by rfl) ⟨242297, by rfl⟩ : syracuseStep 323063 = 484595) B484595
theorem B3665411 : Blo 211809 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B323087 : Blo 211809 323087 := bstep (se 1 (by rfl) ⟨242315, by rfl⟩ : syracuseStep 323087 = 484631) B484631
theorem B323129 : Blo 211809 323129 := bstep (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) B242347
theorem B323207 : Blo 211809 323207 := bstep (se 1 (by rfl) ⟨242405, by rfl⟩ : syracuseStep 323207 = 484811) B484811
theorem B323243 : Blo 211809 323243 := bstep (se 1 (by rfl) ⟨242432, by rfl⟩ : syracuseStep 323243 = 484865) B484865
theorem B1175233 : Blo 211809 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B323273 : Blo 211809 323273 := bstep (se 2 (by rfl) ⟨121227, by rfl⟩ : syracuseStep 323273 = 242455) B242455
theorem B323387 : Blo 211809 323387 := bstep (se 1 (by rfl) ⟨242540, by rfl⟩ : syracuseStep 323387 = 485081) B485081
theorem B323447 : Blo 211809 323447 := bstep (se 1 (by rfl) ⟨242585, by rfl⟩ : syracuseStep 323447 = 485171) B485171
theorem B323471 : Blo 211809 323471 := bstep (se 1 (by rfl) ⟨242603, by rfl⟩ : syracuseStep 323471 = 485207) B485207
theorem B1077137 : Blo 211809 1077137 := bstep (se 2 (by rfl) ⟨403926, by rfl⟩ : syracuseStep 1077137 = 807853) B807853
theorem B454547 : Blo 211809 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B290731 : Blo 211809 290731 := bstep (se 1 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 290731 = 436097) B436097
theorem B323513 : Blo 211809 323513 := bstep (se 2 (by rfl) ⟨121317, by rfl⟩ : syracuseStep 323513 = 242635) B242635
theorem B323591 : Blo 211809 323591 := bstep (se 1 (by rfl) ⟨242693, by rfl⟩ : syracuseStep 323591 = 485387) B485387
theorem B323627 : Blo 211809 323627 := bstep (se 1 (by rfl) ⟨242720, by rfl⟩ : syracuseStep 323627 = 485441) B485441
theorem B5304365 : Blo 211809 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B323657 : Blo 211809 323657 := bstep (se 2 (by rfl) ⟨121371, by rfl⟩ : syracuseStep 323657 = 242743) B242743
theorem B5009501 : Blo 211809 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B258167 : Blo 211809 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B1208591 : Blo 211809 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B651673 : Blo 211809 651673 := bstep (se 2 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 651673 = 488755) B488755
theorem B1208843 : Blo 211809 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B979499 : Blo 211809 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B258619 : Blo 211809 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B651977 : Blo 211809 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B1307443 : Blo 211809 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1635389 : Blo 211809 1635389 := bstep (se 3 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 1635389 = 613271) B613271
theorem B619607 : Blo 211809 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B259243 : Blo 211809 259243 := bstep (se 1 (by rfl) ⟨194432, by rfl⟩ : syracuseStep 259243 = 388865) B388865
theorem B20903345 : Blo 211809 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B357817 : Blo 211809 357817 := bstep (se 2 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 357817 = 268363) B268363
theorem B6714809 : Blo 211809 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B259771 : Blo 211809 259771 := bstep (se 1 (by rfl) ⟨194828, by rfl⟩ : syracuseStep 259771 = 389657) B389657
theorem B325307 : Blo 211809 325307 := bstep (se 1 (by rfl) ⟨243980, by rfl⟩ : syracuseStep 325307 = 487961) B487961
theorem B1210049 : Blo 211809 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B718625 : Blo 211809 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B718739 : Blo 211809 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B1079243 : Blo 211809 1079243 := bstep (se 1 (by rfl) ⟨809432, by rfl⟩ : syracuseStep 1079243 = 1618865) B1618865
theorem B358519 : Blo 211809 358519 := bstep (se 1 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 358519 = 537779) B537779
theorem B1079567 : Blo 211809 1079567 := bstep (se 1 (by rfl) ⟨809675, by rfl⟩ : syracuseStep 1079567 = 1619351) B1619351
theorem B686369 : Blo 211809 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B358715 : Blo 211809 358715 := bstep (se 1 (by rfl) ⟨269036, by rfl⟩ : syracuseStep 358715 = 538073) B538073
theorem B817523 : Blo 211809 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B2587085 : Blo 211809 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B326135 : Blo 211809 326135 := bstep (se 1 (by rfl) ⟨244601, by rfl⟩ : syracuseStep 326135 = 489203) B489203
theorem B1374839 : Blo 211809 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B359113 : Blo 211809 359113 := bstep (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) B269335
theorem B457417 : Blo 211809 457417 := bstep (se 2 (by rfl) ⟨171531, by rfl⟩ : syracuseStep 457417 = 343063) B343063
theorem B228367 : Blo 211809 228367 := bstep (se 1 (by rfl) ⟨171275, by rfl⟩ : syracuseStep 228367 = 342551) B342551
theorem B720143 : Blo 211809 720143 := bstep (se 1 (by rfl) ⟨540107, by rfl⟩ : syracuseStep 720143 = 1080215) B1080215
theorem B359815 : Blo 211809 359815 := bstep (se 1 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 359815 = 539723) B539723
theorem B720413 : Blo 211809 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B917021 : Blo 211809 917021 := bstep (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) B343883
theorem B1081025 : Blo 211809 1081025 := bstep (se 2 (by rfl) ⟨405384, by rfl⟩ : syracuseStep 1081025 = 810769) B810769
theorem B3440357 : Blo 211809 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B2490263 : Blo 211809 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B720953 : Blo 211809 720953 := bstep (se 2 (by rfl) ⟨270357, by rfl⟩ : syracuseStep 720953 = 540715) B540715
theorem B1572941 : Blo 211809 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B360571 : Blo 211809 360571 := bstep (se 1 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 360571 = 540857) B540857
theorem B688445 : Blo 211809 688445 := bstep (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) B258167
theorem B721277 : Blo 211809 721277 := bstep (se 3 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 721277 = 270479) B270479
theorem B721547 : Blo 211809 721547 := bstep (se 1 (by rfl) ⟨541160, by rfl⟩ : syracuseStep 721547 = 1082321) B1082321
theorem B361435 : Blo 211809 361435 := bstep (se 1 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 361435 = 542153) B542153
theorem B492551 : Blo 211809 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B918985 : Blo 211809 918985 := bstep (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) B689239
theorem B1181147 : Blo 211809 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B722465 : Blo 211809 722465 := bstep (se 2 (by rfl) ⟨270924, by rfl⟩ : syracuseStep 722465 = 541849) B541849
theorem B362063 : Blo 211809 362063 := bstep (se 1 (by rfl) ⟨271547, by rfl⟩ : syracuseStep 362063 = 543095) B543095
theorem B722681 : Blo 211809 722681 := bstep (se 2 (by rfl) ⟨271005, by rfl⟩ : syracuseStep 722681 = 542011) B542011
theorem B722951 : Blo 211809 722951 := bstep (se 1 (by rfl) ⟨542213, by rfl⟩ : syracuseStep 722951 = 1084427) B1084427
theorem B1574927 : Blo 211809 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B723059 : Blo 211809 723059 := bstep (se 1 (by rfl) ⟨542294, by rfl⟩ : syracuseStep 723059 = 1084589) B1084589
theorem B723329 : Blo 211809 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B362927 : Blo 211809 362927 := bstep (se 1 (by rfl) ⟨272195, by rfl⟩ : syracuseStep 362927 = 544391) B544391
theorem B363359 : Blo 211809 363359 := bstep (se 1 (by rfl) ⟨272519, by rfl⟩ : syracuseStep 363359 = 545039) B545039
theorem B724139 : Blo 211809 724139 := bstep (se 1 (by rfl) ⟨543104, by rfl⟩ : syracuseStep 724139 = 1086209) B1086209
theorem B363919 : Blo 211809 363919 := bstep (se 1 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 363919 = 545879) B545879
theorem B1085075 : Blo 211809 1085075 := bstep (se 1 (by rfl) ⟨813806, by rfl⟩ : syracuseStep 1085075 = 1627613) B1627613
theorem B1740487 : Blo 211809 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B724679 : Blo 211809 724679 := bstep (se 1 (by rfl) ⟨543509, by rfl⟩ : syracuseStep 724679 = 1087019) B1087019
theorem B429779 : Blo 211809 429779 := bstep (se 1 (by rfl) ⟨322334, by rfl⟩ : syracuseStep 429779 = 644669) B644669
theorem B1610117 : Blo 211809 1610117 := bstep (se 4 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 1610117 = 301897) B301897
theorem B1380887 : Blo 211809 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B725543 : Blo 211809 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B1675835 : Blo 211809 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B725651 : Blo 211809 725651 := bstep (se 1 (by rfl) ⟨544238, by rfl⟩ : syracuseStep 725651 = 1088477) B1088477
theorem B1610603 : Blo 211809 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B725867 : Blo 211809 725867 := bstep (se 1 (by rfl) ⟨544400, by rfl⟩ : syracuseStep 725867 = 1088801) B1088801
theorem B725921 : Blo 211809 725921 := bstep (se 2 (by rfl) ⟨272220, by rfl⟩ : syracuseStep 725921 = 544441) B544441
theorem B627643 : Blo 211809 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B2954393 : Blo 211809 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B726515 : Blo 211809 726515 := bstep (se 1 (by rfl) ⟨544886, by rfl⟩ : syracuseStep 726515 = 1089773) B1089773
theorem B727055 : Blo 211809 727055 := bstep (se 1 (by rfl) ⟨545291, by rfl⟩ : syracuseStep 727055 = 1090583) B1090583
theorem B1382629 : Blo 211809 1382629 := bstep (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) B259243
theorem B1743257 : Blo 211809 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B2071021 : Blo 211809 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B11770433 : Blo 211809 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B727649 : Blo 211809 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B10394243 : Blo 211809 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B1612547 : Blo 211809 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B269239 : Blo 211809 269239 := bstep (se 1 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 269239 = 403859) B403859
theorem B466319 : Blo 211809 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B826919 : Blo 211809 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B1842821 : Blo 211809 1842821 := bstep (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) B345529
theorem B303031 : Blo 211809 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B270535 : Blo 211809 270535 := bstep (se 1 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 270535 = 405803) B405803
theorem B3678533 : Blo 211809 3678533 := bstep (se 4 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 3678533 = 689725) B689725
theorem B434651 : Blo 211809 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B1090259 : Blo 211809 1090259 := bstep (se 1 (by rfl) ⟨817694, by rfl⟩ : syracuseStep 1090259 = 1635389) B1635389
theorem B271279 : Blo 211809 271279 := bstep (se 1 (by rfl) ⟨203459, by rfl⟩ : syracuseStep 271279 = 406919) B406919
theorem B13935563 : Blo 211809 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B304489 : Blo 211809 304489 := bstep (se 2 (by rfl) ⟨114183, by rfl⟩ : syracuseStep 304489 = 228367) B228367
theorem B239143 : Blo 211809 239143 := bstep (se 1 (by rfl) ⟨179357, by rfl⟩ : syracuseStep 239143 = 358715) B358715
theorem B22029893 : Blo 211809 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B2434859 : Blo 211809 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B272423 : Blo 211809 272423 := bstep (se 1 (by rfl) ⟨204317, by rfl⟩ : syracuseStep 272423 = 408635) B408635
theorem B1615949 : Blo 211809 1615949 := bstep (se 3 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 1615949 = 605981) B605981
theorem B272747 : Blo 211809 272747 := bstep (se 1 (by rfl) ⟨204560, by rfl⟩ : syracuseStep 272747 = 409121) B409121
theorem B1551251 : Blo 211809 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1092527 : Blo 211809 1092527 := bstep (se 1 (by rfl) ⟨819395, by rfl⟩ : syracuseStep 1092527 = 1638791) B1638791
theorem B404443 : Blo 211809 404443 := bstep (se 1 (by rfl) ⟨303332, by rfl⟩ : syracuseStep 404443 = 606665) B606665
theorem B404489 : Blo 211809 404489 := bstep (se 2 (by rfl) ⟨151683, by rfl⟩ : syracuseStep 404489 = 303367) B303367
theorem B240763 : Blo 211809 240763 := bstep (se 1 (by rfl) ⟨180572, by rfl⟩ : syracuseStep 240763 = 361145) B361145
theorem B2174147 : Blo 211809 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B765245 : Blo 211809 765245 := bstep (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) B286967
theorem B404831 : Blo 211809 404831 := bstep (se 1 (by rfl) ⟨303623, by rfl⟩ : syracuseStep 404831 = 607247) B607247
theorem B241231 : Blo 211809 241231 := bstep (se 1 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 241231 = 361847) B361847
theorem B306767 : Blo 211809 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B536503 : Blo 211809 536503 := bstep (se 1 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 536503 = 804755) B804755
theorem B241627 : Blo 211809 241627 := bstep (se 1 (by rfl) ⟨181220, by rfl⟩ : syracuseStep 241627 = 362441) B362441
theorem B864275 : Blo 211809 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B864503 : Blo 211809 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B733583 : Blo 211809 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B242095 : Blo 211809 242095 := bstep (se 1 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 242095 = 363143) B363143
theorem B405947 : Blo 211809 405947 := bstep (se 1 (by rfl) ⟨304460, by rfl⟩ : syracuseStep 405947 = 608921) B608921
theorem B1618379 : Blo 211809 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B340519 : Blo 211809 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B438841 : Blo 211809 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B242527 : Blo 211809 242527 := bstep (se 1 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 242527 = 363791) B363791
theorem B14398361 : Blo 211809 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B406433 : Blo 211809 406433 := bstep (se 2 (by rfl) ⟨152412, by rfl⟩ : syracuseStep 406433 = 304825) B304825
theorem B406775 : Blo 211809 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B537961 : Blo 211809 537961 := bstep (se 2 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 537961 = 403471) B403471
theorem B603521 : Blo 211809 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B341423 : Blo 211809 341423 := bstep (se 1 (by rfl) ⟨256067, by rfl⟩ : syracuseStep 341423 = 512135) B512135
theorem B734707 : Blo 211809 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B1324583 : Blo 211809 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B1652285 : Blo 211809 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B538235 : Blo 211809 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B767627 : Blo 211809 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B440057 : Blo 211809 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B341833 : Blo 211809 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B604091 : Blo 211809 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B1095611 : Blo 211809 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B604331 : Blo 211809 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B408073 : Blo 211809 408073 := bstep (se 2 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 408073 = 306055) B306055
theorem B1620809 : Blo 211809 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B408415 : Blo 211809 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B310123 : Blo 211809 310123 := bstep (se 1 (by rfl) ⟨232592, by rfl⟩ : syracuseStep 310123 = 465185) B465185
theorem B211835 : Blo 211809 211835 := bstep (se 1 (by rfl) ⟨158876, by rfl⟩ : syracuseStep 211835 = 317753) B317753
theorem B211887 : Blo 211809 211887 := bstep (se 1 (by rfl) ⟨158915, by rfl⟩ : syracuseStep 211887 = 317831) B317831
theorem B211911 : Blo 211809 211911 := bstep (se 1 (by rfl) ⟨158933, by rfl⟩ : syracuseStep 211911 = 317867) B317867
theorem B211931 : Blo 211809 211931 := bstep (se 1 (by rfl) ⟨158948, by rfl⟩ : syracuseStep 211931 = 317897) B317897
theorem B212007 : Blo 211809 212007 := bstep (se 1 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 212007 = 318011) B318011
theorem B212047 : Blo 211809 212047 := bstep (se 1 (by rfl) ⟨159035, by rfl⟩ : syracuseStep 212047 = 318071) B318071
theorem B212063 : Blo 211809 212063 := bstep (se 1 (by rfl) ⟨159047, by rfl⟩ : syracuseStep 212063 = 318095) B318095
theorem B212091 : Blo 211809 212091 := bstep (se 1 (by rfl) ⟨159068, by rfl⟩ : syracuseStep 212091 = 318137) B318137
theorem B867485 : Blo 211809 867485 := bstep (se 3 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 867485 = 325307) B325307
theorem B212143 : Blo 211809 212143 := bstep (se 1 (by rfl) ⟨159107, by rfl⟩ : syracuseStep 212143 = 318215) B318215
theorem B212167 : Blo 211809 212167 := bstep (se 1 (by rfl) ⟨159125, by rfl⟩ : syracuseStep 212167 = 318251) B318251
theorem B212187 : Blo 211809 212187 := bstep (se 1 (by rfl) ⟨159140, by rfl⟩ : syracuseStep 212187 = 318281) B318281
theorem B212263 : Blo 211809 212263 := bstep (se 1 (by rfl) ⟨159197, by rfl⟩ : syracuseStep 212263 = 318395) B318395
theorem B212303 : Blo 211809 212303 := bstep (se 1 (by rfl) ⟨159227, by rfl⟩ : syracuseStep 212303 = 318455) B318455
theorem B212319 : Blo 211809 212319 := bstep (se 1 (by rfl) ⟨159239, by rfl⟩ : syracuseStep 212319 = 318479) B318479
theorem B212347 : Blo 211809 212347 := bstep (se 1 (by rfl) ⟨159260, by rfl⟩ : syracuseStep 212347 = 318521) B318521
theorem B540047 : Blo 211809 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B212399 : Blo 211809 212399 := bstep (se 1 (by rfl) ⟨159299, by rfl⟩ : syracuseStep 212399 = 318599) B318599
theorem B212423 : Blo 211809 212423 := bstep (se 1 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 212423 = 318635) B318635
theorem B212443 : Blo 211809 212443 := bstep (se 1 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 212443 = 318665) B318665
theorem B2440691 : Blo 211809 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B572953 : Blo 211809 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B212519 : Blo 211809 212519 := bstep (se 1 (by rfl) ⟨159389, by rfl⟩ : syracuseStep 212519 = 318779) B318779
theorem B212559 : Blo 211809 212559 := bstep (se 1 (by rfl) ⟨159419, by rfl⟩ : syracuseStep 212559 = 318839) B318839
theorem B212575 : Blo 211809 212575 := bstep (se 1 (by rfl) ⟨159431, by rfl⟩ : syracuseStep 212575 = 318863) B318863
theorem B212603 : Blo 211809 212603 := bstep (se 1 (by rfl) ⟨159452, by rfl⟩ : syracuseStep 212603 = 318905) B318905
theorem B212655 : Blo 211809 212655 := bstep (se 1 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 212655 = 318983) B318983
theorem B212679 : Blo 211809 212679 := bstep (se 1 (by rfl) ⟨159509, by rfl⟩ : syracuseStep 212679 = 319019) B319019
theorem B540371 : Blo 211809 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B212699 : Blo 211809 212699 := bstep (se 1 (by rfl) ⟨159524, by rfl⟩ : syracuseStep 212699 = 319049) B319049
theorem B212775 : Blo 211809 212775 := bstep (se 1 (by rfl) ⟨159581, by rfl⟩ : syracuseStep 212775 = 319163) B319163
theorem B212815 : Blo 211809 212815 := bstep (se 1 (by rfl) ⟨159611, by rfl⟩ : syracuseStep 212815 = 319223) B319223
theorem B212831 : Blo 211809 212831 := bstep (se 1 (by rfl) ⟨159623, by rfl⟩ : syracuseStep 212831 = 319247) B319247
theorem B212859 : Blo 211809 212859 := bstep (se 1 (by rfl) ⟨159644, by rfl⟩ : syracuseStep 212859 = 319289) B319289
theorem B212911 : Blo 211809 212911 := bstep (se 1 (by rfl) ⟨159683, by rfl⟩ : syracuseStep 212911 = 319367) B319367
theorem B409531 : Blo 211809 409531 := bstep (se 1 (by rfl) ⟨307148, by rfl⟩ : syracuseStep 409531 = 614297) B614297
theorem B212935 : Blo 211809 212935 := bstep (se 1 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 212935 = 319403) B319403
theorem B212955 : Blo 211809 212955 := bstep (se 1 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 212955 = 319433) B319433
theorem B409607 : Blo 211809 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B213031 : Blo 211809 213031 := bstep (se 1 (by rfl) ⟨159773, by rfl⟩ : syracuseStep 213031 = 319547) B319547
theorem B213071 : Blo 211809 213071 := bstep (se 1 (by rfl) ⟨159803, by rfl⟩ : syracuseStep 213071 = 319607) B319607
theorem B213087 : Blo 211809 213087 := bstep (se 1 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 213087 = 319631) B319631
theorem B213115 : Blo 211809 213115 := bstep (se 1 (by rfl) ⟨159836, by rfl⟩ : syracuseStep 213115 = 319673) B319673
theorem B213167 : Blo 211809 213167 := bstep (se 1 (by rfl) ⟨159875, by rfl⟩ : syracuseStep 213167 = 319751) B319751
theorem B213191 : Blo 211809 213191 := bstep (se 1 (by rfl) ⟨159893, by rfl⟩ : syracuseStep 213191 = 319787) B319787
theorem B213211 : Blo 211809 213211 := bstep (se 1 (by rfl) ⟨159908, by rfl⟩ : syracuseStep 213211 = 319817) B319817
theorem B213287 : Blo 211809 213287 := bstep (se 1 (by rfl) ⟨159965, by rfl⟩ : syracuseStep 213287 = 319931) B319931
theorem B213327 : Blo 211809 213327 := bstep (se 1 (by rfl) ⟨159995, by rfl⟩ : syracuseStep 213327 = 319991) B319991
theorem B1392983 : Blo 211809 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B213343 : Blo 211809 213343 := bstep (se 1 (by rfl) ⟨160007, by rfl⟩ : syracuseStep 213343 = 320015) B320015
theorem B213371 : Blo 211809 213371 := bstep (se 1 (by rfl) ⟨160028, by rfl⟩ : syracuseStep 213371 = 320057) B320057
theorem B213423 : Blo 211809 213423 := bstep (se 1 (by rfl) ⟨160067, by rfl⟩ : syracuseStep 213423 = 320135) B320135
theorem B213447 : Blo 211809 213447 := bstep (se 1 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 213447 = 320171) B320171
theorem B213467 : Blo 211809 213467 := bstep (se 1 (by rfl) ⟨160100, by rfl⟩ : syracuseStep 213467 = 320201) B320201
theorem B868897 : Blo 211809 868897 := bstep (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) B651673
theorem B213543 : Blo 211809 213543 := bstep (se 1 (by rfl) ⟨160157, by rfl⟩ : syracuseStep 213543 = 320315) B320315
theorem B213583 : Blo 211809 213583 := bstep (se 1 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 213583 = 320375) B320375
theorem B213599 : Blo 211809 213599 := bstep (se 1 (by rfl) ⟨160199, by rfl⟩ : syracuseStep 213599 = 320399) B320399
theorem B213627 : Blo 211809 213627 := bstep (se 1 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 213627 = 320441) B320441
theorem B213679 : Blo 211809 213679 := bstep (se 1 (by rfl) ⟨160259, by rfl⟩ : syracuseStep 213679 = 320519) B320519
theorem B213703 : Blo 211809 213703 := bstep (se 1 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 213703 = 320555) B320555
theorem B213723 : Blo 211809 213723 := bstep (se 1 (by rfl) ⟨160292, by rfl⟩ : syracuseStep 213723 = 320585) B320585
theorem B344825 : Blo 211809 344825 := bstep (se 2 (by rfl) ⟨129309, by rfl⟩ : syracuseStep 344825 = 258619) B258619
theorem B213799 : Blo 211809 213799 := bstep (se 1 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 213799 = 320699) B320699
theorem B213839 : Blo 211809 213839 := bstep (se 1 (by rfl) ⟨160379, by rfl⟩ : syracuseStep 213839 = 320759) B320759
theorem B213855 : Blo 211809 213855 := bstep (se 1 (by rfl) ⟨160391, by rfl⟩ : syracuseStep 213855 = 320783) B320783
theorem B213883 : Blo 211809 213883 := bstep (se 1 (by rfl) ⟨160412, by rfl⟩ : syracuseStep 213883 = 320825) B320825
theorem B213935 : Blo 211809 213935 := bstep (se 1 (by rfl) ⟨160451, by rfl⟩ : syracuseStep 213935 = 320903) B320903
theorem B213959 : Blo 211809 213959 := bstep (se 1 (by rfl) ⟨160469, by rfl⟩ : syracuseStep 213959 = 320939) B320939
theorem B213979 : Blo 211809 213979 := bstep (se 1 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 213979 = 320969) B320969
theorem B214055 : Blo 211809 214055 := bstep (se 1 (by rfl) ⟨160541, by rfl⟩ : syracuseStep 214055 = 321083) B321083
theorem B214095 : Blo 211809 214095 := bstep (se 1 (by rfl) ⟨160571, by rfl⟩ : syracuseStep 214095 = 321143) B321143
theorem B214111 : Blo 211809 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B214139 : Blo 211809 214139 := bstep (se 1 (by rfl) ⟨160604, by rfl⟩ : syracuseStep 214139 = 321209) B321209
theorem B1197227 : Blo 211809 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B214191 : Blo 211809 214191 := bstep (se 1 (by rfl) ⟨160643, by rfl⟩ : syracuseStep 214191 = 321287) B321287
theorem B214215 : Blo 211809 214215 := bstep (se 1 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 214215 = 321323) B321323
theorem B214235 : Blo 211809 214235 := bstep (se 1 (by rfl) ⟨160676, by rfl⟩ : syracuseStep 214235 = 321353) B321353
theorem B214311 : Blo 211809 214311 := bstep (se 1 (by rfl) ⟨160733, by rfl⟩ : syracuseStep 214311 = 321467) B321467
theorem B214351 : Blo 211809 214351 := bstep (se 1 (by rfl) ⟨160763, by rfl⟩ : syracuseStep 214351 = 321527) B321527
theorem B214367 : Blo 211809 214367 := bstep (se 1 (by rfl) ⟨160775, by rfl⟩ : syracuseStep 214367 = 321551) B321551
theorem B214395 : Blo 211809 214395 := bstep (se 1 (by rfl) ⟨160796, by rfl⟩ : syracuseStep 214395 = 321593) B321593
theorem B804239 : Blo 211809 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B214447 : Blo 211809 214447 := bstep (se 1 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 214447 = 321671) B321671
theorem B214471 : Blo 211809 214471 := bstep (se 1 (by rfl) ⟨160853, by rfl⟩ : syracuseStep 214471 = 321707) B321707
theorem B214491 : Blo 211809 214491 := bstep (se 1 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 214491 = 321737) B321737
theorem B476711 : Blo 211809 476711 := bstep (se 1 (by rfl) ⟨357533, by rfl⟩ : syracuseStep 476711 = 715067) B715067
theorem B214567 : Blo 211809 214567 := bstep (se 1 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 214567 = 321851) B321851
theorem B214607 : Blo 211809 214607 := bstep (se 1 (by rfl) ⟨160955, by rfl⟩ : syracuseStep 214607 = 321911) B321911
theorem B214623 : Blo 211809 214623 := bstep (se 1 (by rfl) ⟨160967, by rfl⟩ : syracuseStep 214623 = 321935) B321935
theorem B214651 : Blo 211809 214651 := bstep (se 1 (by rfl) ⟨160988, by rfl⟩ : syracuseStep 214651 = 321977) B321977
theorem B214703 : Blo 211809 214703 := bstep (se 1 (by rfl) ⟨161027, by rfl⟩ : syracuseStep 214703 = 322055) B322055
theorem B214727 : Blo 211809 214727 := bstep (se 1 (by rfl) ⟨161045, by rfl⟩ : syracuseStep 214727 = 322091) B322091
theorem B214747 : Blo 211809 214747 := bstep (se 1 (by rfl) ⟨161060, by rfl⟩ : syracuseStep 214747 = 322121) B322121
theorem B214823 : Blo 211809 214823 := bstep (se 1 (by rfl) ⟨161117, by rfl⟩ : syracuseStep 214823 = 322235) B322235
theorem B214863 : Blo 211809 214863 := bstep (se 1 (by rfl) ⟨161147, by rfl⟩ : syracuseStep 214863 = 322295) B322295
theorem B214879 : Blo 211809 214879 := bstep (se 1 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 214879 = 322319) B322319
theorem B477035 : Blo 211809 477035 := bstep (se 1 (by rfl) ⟨357776, by rfl⟩ : syracuseStep 477035 = 715553) B715553
theorem B214907 : Blo 211809 214907 := bstep (se 1 (by rfl) ⟨161180, by rfl⟩ : syracuseStep 214907 = 322361) B322361
theorem B477089 : Blo 211809 477089 := bstep (se 2 (by rfl) ⟨178908, by rfl⟩ : syracuseStep 477089 = 357817) B357817
theorem B542639 : Blo 211809 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B214959 : Blo 211809 214959 := bstep (se 1 (by rfl) ⟨161219, by rfl⟩ : syracuseStep 214959 = 322439) B322439
theorem B214983 : Blo 211809 214983 := bstep (se 1 (by rfl) ⟨161237, by rfl⟩ : syracuseStep 214983 = 322475) B322475
theorem B215003 : Blo 211809 215003 := bstep (se 1 (by rfl) ⟨161252, by rfl⟩ : syracuseStep 215003 = 322505) B322505
theorem B215079 : Blo 211809 215079 := bstep (se 1 (by rfl) ⟨161309, by rfl⟩ : syracuseStep 215079 = 322619) B322619
theorem B215119 : Blo 211809 215119 := bstep (se 1 (by rfl) ⟨161339, by rfl⟩ : syracuseStep 215119 = 322679) B322679
theorem B215135 : Blo 211809 215135 := bstep (se 1 (by rfl) ⟨161351, by rfl⟩ : syracuseStep 215135 = 322703) B322703
theorem B215163 : Blo 211809 215163 := bstep (se 1 (by rfl) ⟨161372, by rfl⟩ : syracuseStep 215163 = 322745) B322745
theorem B215215 : Blo 211809 215215 := bstep (se 1 (by rfl) ⟨161411, by rfl⟩ : syracuseStep 215215 = 322823) B322823
theorem B215239 : Blo 211809 215239 := bstep (se 1 (by rfl) ⟨161429, by rfl⟩ : syracuseStep 215239 = 322859) B322859
theorem B215259 : Blo 211809 215259 := bstep (se 1 (by rfl) ⟨161444, by rfl⟩ : syracuseStep 215259 = 322889) B322889
theorem B477431 : Blo 211809 477431 := bstep (se 1 (by rfl) ⟨358073, by rfl⟩ : syracuseStep 477431 = 716147) B716147
theorem B411895 : Blo 211809 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B346361 : Blo 211809 346361 := bstep (se 2 (by rfl) ⟨129885, by rfl⟩ : syracuseStep 346361 = 259771) B259771
theorem B215335 : Blo 211809 215335 := bstep (se 1 (by rfl) ⟨161501, by rfl⟩ : syracuseStep 215335 = 323003) B323003
theorem B215375 : Blo 211809 215375 := bstep (se 1 (by rfl) ⟨161531, by rfl⟩ : syracuseStep 215375 = 323063) B323063
theorem B2443607 : Blo 211809 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B215391 : Blo 211809 215391 := bstep (se 1 (by rfl) ⟨161543, by rfl⟩ : syracuseStep 215391 = 323087) B323087
theorem B215419 : Blo 211809 215419 := bstep (se 1 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 215419 = 323129) B323129
theorem B215471 : Blo 211809 215471 := bstep (se 1 (by rfl) ⟨161603, by rfl⟩ : syracuseStep 215471 = 323207) B323207
theorem B215495 : Blo 211809 215495 := bstep (se 1 (by rfl) ⟨161621, by rfl⟩ : syracuseStep 215495 = 323243) B323243
theorem B215515 : Blo 211809 215515 := bstep (se 1 (by rfl) ⟨161636, by rfl⟩ : syracuseStep 215515 = 323273) B323273
theorem B543257 : Blo 211809 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B805409 : Blo 211809 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B215591 : Blo 211809 215591 := bstep (se 1 (by rfl) ⟨161693, by rfl⟩ : syracuseStep 215591 = 323387) B323387
theorem B215631 : Blo 211809 215631 := bstep (se 1 (by rfl) ⟨161723, by rfl⟩ : syracuseStep 215631 = 323447) B323447
theorem B215647 : Blo 211809 215647 := bstep (se 1 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 215647 = 323471) B323471
theorem B215675 : Blo 211809 215675 := bstep (se 1 (by rfl) ⟨161756, by rfl⟩ : syracuseStep 215675 = 323513) B323513
theorem B215727 : Blo 211809 215727 := bstep (se 1 (by rfl) ⟨161795, by rfl⟩ : syracuseStep 215727 = 323591) B323591
theorem B215751 : Blo 211809 215751 := bstep (se 1 (by rfl) ⟨161813, by rfl⟩ : syracuseStep 215751 = 323627) B323627
theorem B215771 : Blo 211809 215771 := bstep (se 1 (by rfl) ⟨161828, by rfl⟩ : syracuseStep 215771 = 323657) B323657
theorem B478025 : Blo 211809 478025 := bstep (se 2 (by rfl) ⟨179259, by rfl⟩ : syracuseStep 478025 = 358519) B358519
theorem B805727 : Blo 211809 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B2214839 : Blo 211809 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B805895 : Blo 211809 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B314617 : Blo 211809 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B2739581 : Blo 211809 2739581 := bstep (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) B1027343
theorem B511451 : Blo 211809 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B806381 : Blo 211809 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B2346583 : Blo 211809 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B478817 : Blo 211809 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B609889 : Blo 211809 609889 := bstep (se 2 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 609889 = 457417) B457417
theorem B4476539 : Blo 211809 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B806699 : Blo 211809 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B479083 : Blo 211809 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B479159 : Blo 211809 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B5820497 : Blo 211809 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B545015 : Blo 211809 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B1724723 : Blo 211809 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B217423 : Blo 211809 217423 := bstep (se 1 (by rfl) ⟨163067, by rfl⟩ : syracuseStep 217423 = 326135) B326135
theorem B479753 : Blo 211809 479753 := bstep (se 2 (by rfl) ⟨179907, by rfl⟩ : syracuseStep 479753 = 359815) B359815
theorem B905863 : Blo 211809 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B971473 : Blo 211809 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B480095 : Blo 211809 480095 := bstep (se 1 (by rfl) ⟨360071, by rfl⟩ : syracuseStep 480095 = 720143) B720143
theorem B578411 : Blo 211809 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B3724289 : Blo 211809 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B480275 : Blo 211809 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B611347 : Blo 211809 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B545849 : Blo 211809 545849 := bstep (se 2 (by rfl) ⟨204693, by rfl⟩ : syracuseStep 545849 = 409387) B409387
theorem B1660175 : Blo 211809 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B480617 : Blo 211809 480617 := bstep (se 2 (by rfl) ⟨180231, by rfl⟩ : syracuseStep 480617 = 360463) B360463
theorem B546329 : Blo 211809 546329 := bstep (se 2 (by rfl) ⟨204873, by rfl⟩ : syracuseStep 546329 = 409747) B409747
theorem B6543139 : Blo 211809 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B808811 : Blo 211809 808811 := bstep (se 1 (by rfl) ⟨606608, by rfl⟩ : syracuseStep 808811 = 1213217) B1213217
theorem B907195 : Blo 211809 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B481211 : Blo 211809 481211 := bstep (se 1 (by rfl) ⟨360908, by rfl⟩ : syracuseStep 481211 = 721817) B721817
theorem B10344419 : Blo 211809 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B481337 : Blo 211809 481337 := bstep (se 2 (by rfl) ⟨180501, by rfl⟩ : syracuseStep 481337 = 361003) B361003
theorem B317801 : Blo 211809 317801 := bstep (se 2 (by rfl) ⟨119175, by rfl⟩ : syracuseStep 317801 = 238351) B238351
theorem B481679 : Blo 211809 481679 := bstep (se 1 (by rfl) ⟨361259, by rfl⟩ : syracuseStep 481679 = 722519) B722519
theorem B317879 : Blo 211809 317879 := bstep (se 1 (by rfl) ⟨238409, by rfl⟩ : syracuseStep 317879 = 476819) B476819
theorem B317915 : Blo 211809 317915 := bstep (se 1 (by rfl) ⟨238436, by rfl⟩ : syracuseStep 317915 = 476873) B476873
theorem B1366739 : Blo 211809 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B482003 : Blo 211809 482003 := bstep (se 1 (by rfl) ⟨361502, by rfl⟩ : syracuseStep 482003 = 723005) B723005
theorem B613079 : Blo 211809 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B2611997 : Blo 211809 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B318383 : Blo 211809 318383 := bstep (se 1 (by rfl) ⟨238787, by rfl⟩ : syracuseStep 318383 = 477575) B477575
theorem B613295 : Blo 211809 613295 := bstep (se 1 (by rfl) ⟨459971, by rfl⟩ : syracuseStep 613295 = 919943) B919943
theorem B384007 : Blo 211809 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B318473 : Blo 211809 318473 := bstep (se 2 (by rfl) ⟨119427, by rfl⟩ : syracuseStep 318473 = 238855) B238855
theorem B3333143 : Blo 211809 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B318503 : Blo 211809 318503 := bstep (se 1 (by rfl) ⟨238877, by rfl⟩ : syracuseStep 318503 = 477755) B477755
theorem B318587 : Blo 211809 318587 := bstep (se 1 (by rfl) ⟨238940, by rfl⟩ : syracuseStep 318587 = 477881) B477881
theorem B2055415 : Blo 211809 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B318713 : Blo 211809 318713 := bstep (se 2 (by rfl) ⟨119517, by rfl⟩ : syracuseStep 318713 = 239035) B239035
theorem B777559 : Blo 211809 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B318815 : Blo 211809 318815 := bstep (se 1 (by rfl) ⟨239111, by rfl⟩ : syracuseStep 318815 = 478223) B478223
theorem B318827 : Blo 211809 318827 := bstep (se 1 (by rfl) ⟨239120, by rfl⟩ : syracuseStep 318827 = 478241) B478241
theorem B384569 : Blo 211809 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B319055 : Blo 211809 319055 := bstep (se 1 (by rfl) ⟨239291, by rfl⟩ : syracuseStep 319055 = 478583) B478583
theorem B1072763 : Blo 211809 1072763 := bstep (se 1 (by rfl) ⟨804572, by rfl⟩ : syracuseStep 1072763 = 1609145) B1609145
theorem B482939 : Blo 211809 482939 := bstep (se 1 (by rfl) ⟨362204, by rfl⟩ : syracuseStep 482939 = 724409) B724409
theorem B319175 : Blo 211809 319175 := bstep (se 1 (by rfl) ⟨239381, by rfl⟩ : syracuseStep 319175 = 478763) B478763
theorem B483065 : Blo 211809 483065 := bstep (se 2 (by rfl) ⟨181149, by rfl⟩ : syracuseStep 483065 = 362299) B362299
theorem B614137 : Blo 211809 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B1367867 : Blo 211809 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B319337 : Blo 211809 319337 := bstep (se 2 (by rfl) ⟨119751, by rfl⟩ : syracuseStep 319337 = 239503) B239503
theorem B319415 : Blo 211809 319415 := bstep (se 1 (by rfl) ⟨239561, by rfl⟩ : syracuseStep 319415 = 479123) B479123
theorem B319451 : Blo 211809 319451 := bstep (se 1 (by rfl) ⟨239588, by rfl⟩ : syracuseStep 319451 = 479177) B479177
theorem B483335 : Blo 211809 483335 := bstep (se 1 (by rfl) ⟨362501, by rfl⟩ : syracuseStep 483335 = 725003) B725003
theorem B483407 : Blo 211809 483407 := bstep (se 1 (by rfl) ⟨362555, by rfl⟩ : syracuseStep 483407 = 725111) B725111
theorem B614479 : Blo 211809 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B680089 : Blo 211809 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B2744549 : Blo 211809 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B811255 : Blo 211809 811255 := bstep (se 1 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 811255 = 1216883) B1216883
theorem B319919 : Blo 211809 319919 := bstep (se 1 (by rfl) ⟨239939, by rfl⟩ : syracuseStep 319919 = 479879) B479879
theorem B483803 : Blo 211809 483803 := bstep (se 1 (by rfl) ⟨362852, by rfl⟩ : syracuseStep 483803 = 725705) B725705
theorem B975341 : Blo 211809 975341 := bstep (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) B365753
theorem B320009 : Blo 211809 320009 := bstep (se 2 (by rfl) ⟨120003, by rfl⟩ : syracuseStep 320009 = 240007) B240007
theorem B811529 : Blo 211809 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B320039 : Blo 211809 320039 := bstep (se 1 (by rfl) ⟨240029, by rfl⟩ : syracuseStep 320039 = 480059) B480059
theorem B811559 : Blo 211809 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B3465787 : Blo 211809 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B320123 : Blo 211809 320123 := bstep (se 1 (by rfl) ⟨240092, by rfl⟩ : syracuseStep 320123 = 480185) B480185
theorem B1106567 : Blo 211809 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B2417363 : Blo 211809 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B320249 : Blo 211809 320249 := bstep (se 2 (by rfl) ⟨120093, by rfl⟩ : syracuseStep 320249 = 240187) B240187
theorem B320351 : Blo 211809 320351 := bstep (se 1 (by rfl) ⟨240263, by rfl⟩ : syracuseStep 320351 = 480527) B480527
theorem B910187 : Blo 211809 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B320363 : Blo 211809 320363 := bstep (se 1 (by rfl) ⟨240272, by rfl⟩ : syracuseStep 320363 = 480545) B480545
theorem B484271 : Blo 211809 484271 := bstep (se 1 (by rfl) ⟨363203, by rfl⟩ : syracuseStep 484271 = 726407) B726407
theorem B320591 : Blo 211809 320591 := bstep (se 1 (by rfl) ⟨240443, by rfl⟩ : syracuseStep 320591 = 480887) B480887
theorem B484523 : Blo 211809 484523 := bstep (se 1 (by rfl) ⟨363392, by rfl⟩ : syracuseStep 484523 = 726785) B726785
theorem B812227 : Blo 211809 812227 := bstep (se 1 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 812227 = 1218341) B1218341
theorem B320711 : Blo 211809 320711 := bstep (se 1 (by rfl) ⟨240533, by rfl⟩ : syracuseStep 320711 = 481067) B481067
theorem B320873 : Blo 211809 320873 := bstep (se 2 (by rfl) ⟨120327, by rfl⟩ : syracuseStep 320873 = 240655) B240655
theorem B320951 : Blo 211809 320951 := bstep (se 1 (by rfl) ⟨240713, by rfl⟩ : syracuseStep 320951 = 481427) B481427
theorem B320987 : Blo 211809 320987 := bstep (se 1 (by rfl) ⟨240740, by rfl⟩ : syracuseStep 320987 = 481481) B481481
theorem B812531 : Blo 211809 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B2582027 : Blo 211809 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B485063 : Blo 211809 485063 := bstep (se 1 (by rfl) ⟨363797, by rfl⟩ : syracuseStep 485063 = 727595) B727595
theorem B4089689 : Blo 211809 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B321455 : Blo 211809 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B812987 : Blo 211809 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B3958721 : Blo 211809 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B321545 : Blo 211809 321545 := bstep (se 2 (by rfl) ⟨120579, by rfl⟩ : syracuseStep 321545 = 241159) B241159
theorem B321575 : Blo 211809 321575 := bstep (se 1 (by rfl) ⟨241181, by rfl⟩ : syracuseStep 321575 = 482363) B482363
theorem B321659 : Blo 211809 321659 := bstep (se 1 (by rfl) ⟨241244, by rfl⟩ : syracuseStep 321659 = 482489) B482489
theorem B11954309 : Blo 211809 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B714905 : Blo 211809 714905 := bstep (se 2 (by rfl) ⟨268089, by rfl⟩ : syracuseStep 714905 = 536179) B536179
theorem B321785 : Blo 211809 321785 := bstep (se 2 (by rfl) ⟨120669, by rfl⟩ : syracuseStep 321785 = 241339) B241339
theorem B1566977 : Blo 211809 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1075517 : Blo 211809 1075517 := bstep (se 3 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 1075517 = 403319) B403319
theorem B1370429 : Blo 211809 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B321887 : Blo 211809 321887 := bstep (se 1 (by rfl) ⟨241415, by rfl⟩ : syracuseStep 321887 = 482831) B482831
theorem B321899 : Blo 211809 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B387641 : Blo 211809 387641 := bstep (se 2 (by rfl) ⟨145365, by rfl⟩ : syracuseStep 387641 = 290731) B290731
theorem B322127 : Blo 211809 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B322247 : Blo 211809 322247 := bstep (se 1 (by rfl) ⟨241685, by rfl⟩ : syracuseStep 322247 = 483371) B483371
theorem B486137 : Blo 211809 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B322409 : Blo 211809 322409 := bstep (se 2 (by rfl) ⟨120903, by rfl⟩ : syracuseStep 322409 = 241807) B241807
theorem B486319 : Blo 211809 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B322487 : Blo 211809 322487 := bstep (se 1 (by rfl) ⟨241865, by rfl⟩ : syracuseStep 322487 = 483731) B483731
theorem B322523 : Blo 211809 322523 := bstep (se 1 (by rfl) ⟨241892, by rfl⟩ : syracuseStep 322523 = 483785) B483785
theorem B683255 : Blo 211809 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B716093 : Blo 211809 716093 := bstep (se 3 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 716093 = 268535) B268535
theorem B322991 : Blo 211809 322991 := bstep (se 1 (by rfl) ⟨242243, by rfl⟩ : syracuseStep 322991 = 484487) B484487
theorem B323081 : Blo 211809 323081 := bstep (se 2 (by rfl) ⟨121155, by rfl⟩ : syracuseStep 323081 = 242311) B242311
theorem B323111 : Blo 211809 323111 := bstep (se 1 (by rfl) ⟨242333, by rfl⟩ : syracuseStep 323111 = 484667) B484667
theorem B323195 : Blo 211809 323195 := bstep (se 1 (by rfl) ⟨242396, by rfl⟩ : syracuseStep 323195 = 484793) B484793
theorem B1633931 : Blo 211809 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B290503 : Blo 211809 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B323321 : Blo 211809 323321 := bstep (se 2 (by rfl) ⟨121245, by rfl⟩ : syracuseStep 323321 = 242491) B242491
theorem B323423 : Blo 211809 323423 := bstep (se 1 (by rfl) ⟨242567, by rfl⟩ : syracuseStep 323423 = 485135) B485135
theorem B323435 : Blo 211809 323435 := bstep (se 1 (by rfl) ⟨242576, by rfl⟩ : syracuseStep 323435 = 485153) B485153
theorem B323663 : Blo 211809 323663 := bstep (se 1 (by rfl) ⟨242747, by rfl⟩ : syracuseStep 323663 = 485495) B485495
theorem B716957 : Blo 211809 716957 := bstep (se 3 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 716957 = 268859) B268859
theorem B815447 : Blo 211809 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B5534081 : Blo 211809 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B1077785 : Blo 211809 1077785 := bstep (se 2 (by rfl) ⟨404169, by rfl⟩ : syracuseStep 1077785 = 808339) B808339
theorem B717497 : Blo 211809 717497 := bstep (se 2 (by rfl) ⟨269061, by rfl⟩ : syracuseStep 717497 = 538123) B538123
theorem B357547 : Blo 211809 357547 := bstep (se 1 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 357547 = 536321) B536321
theorem B2323673 : Blo 211809 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B718091 : Blo 211809 718091 := bstep (se 1 (by rfl) ⟨538568, by rfl⟩ : syracuseStep 718091 = 1077137) B1077137
theorem B3536243 : Blo 211809 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B3339667 : Blo 211809 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B357851 : Blo 211809 357851 := bstep (se 1 (by rfl) ⟨268388, by rfl⟩ : syracuseStep 357851 = 536777) B536777
theorem B718361 : Blo 211809 718361 := bstep (se 2 (by rfl) ⟨269385, by rfl⟩ : syracuseStep 718361 = 538771) B538771
theorem B5961397 : Blo 211809 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B358087 : Blo 211809 358087 := bstep (se 1 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 358087 = 537131) B537131
theorem B358249 : Blo 211809 358249 := bstep (se 2 (by rfl) ⟨134343, by rfl⟩ : syracuseStep 358249 = 268687) B268687
theorem B358843 : Blo 211809 358843 := bstep (se 1 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 358843 = 538265) B538265
theorem B358951 : Blo 211809 358951 := bstep (se 1 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 358951 = 538427) B538427
theorem B621179 : Blo 211809 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B719495 : Blo 211809 719495 := bstep (se 1 (by rfl) ⟨539621, by rfl⟩ : syracuseStep 719495 = 1079243) B1079243
theorem B719549 : Blo 211809 719549 := bstep (se 3 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 719549 = 269831) B269831
theorem B817879 : Blo 211809 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B719711 : Blo 211809 719711 := bstep (se 1 (by rfl) ⟨539783, by rfl⟩ : syracuseStep 719711 = 1079567) B1079567
theorem B359275 : Blo 211809 359275 := bstep (se 1 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 359275 = 538913) B538913
theorem B457579 : Blo 211809 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B2063333 : Blo 211809 2063333 := bstep (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) B386875
theorem B719873 : Blo 211809 719873 := bstep (se 2 (by rfl) ⟨269952, by rfl⟩ : syracuseStep 719873 = 539905) B539905
theorem B916559 : Blo 211809 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B818333 : Blo 211809 818333 := bstep (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) B306875
theorem B1015031 : Blo 211809 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B1080701 : Blo 211809 1080701 := bstep (se 3 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 1080701 = 405263) B405263
theorem B7044569 : Blo 211809 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B229063 : Blo 211809 229063 := bstep (se 1 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 229063 = 343595) B343595
theorem B720683 : Blo 211809 720683 := bstep (se 1 (by rfl) ⟨540512, by rfl⟩ : syracuseStep 720683 = 1081025) B1081025
theorem B2293571 : Blo 211809 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B819017 : Blo 211809 819017 := bstep (se 2 (by rfl) ⟨307131, by rfl⟩ : syracuseStep 819017 = 614263) B614263
theorem B360335 : Blo 211809 360335 := bstep (se 1 (by rfl) ⟨270251, by rfl⟩ : syracuseStep 360335 = 540503) B540503
theorem B1638305 : Blo 211809 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B1048627 : Blo 211809 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B819305 : Blo 211809 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B458963 : Blo 211809 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B360713 : Blo 211809 360713 := bstep (se 2 (by rfl) ⟨135267, by rfl⟩ : syracuseStep 360713 = 270535) B270535
theorem B1081673 : Blo 211809 1081673 := bstep (se 2 (by rfl) ⟨405627, by rfl⟩ : syracuseStep 1081673 = 811255) B811255
theorem B229883 : Blo 211809 229883 := bstep (se 1 (by rfl) ⟨172412, by rfl⟩ : syracuseStep 229883 = 344825) B344825
theorem B328367 : Blo 211809 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B4621049 : Blo 211809 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B361705 : Blo 211809 361705 := bstep (se 2 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 361705 = 271279) B271279
theorem B361759 : Blo 211809 361759 := bstep (se 1 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 361759 = 542639) B542639
theorem B1049951 : Blo 211809 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B1082969 : Blo 211809 1082969 := bstep (se 2 (by rfl) ⟨406113, by rfl⟩ : syracuseStep 1082969 = 812227) B812227
theorem B362171 : Blo 211809 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B1476559 : Blo 211809 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B2984359 : Blo 211809 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B723383 : Blo 211809 723383 := bstep (se 1 (by rfl) ⟨542537, by rfl⟩ : syracuseStep 723383 = 1085075) B1085075
theorem B16714421 : Blo 211809 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1149815 : Blo 211809 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B920591 : Blo 211809 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B1117223 : Blo 211809 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B363899 : Blo 211809 363899 := bstep (se 1 (by rfl) ⟨272924, by rfl⟩ : syracuseStep 363899 = 545849) B545849
theorem B1969595 : Blo 211809 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B364219 : Blo 211809 364219 := bstep (se 1 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 364219 = 546329) B546329
theorem B3149725 : Blo 211809 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B1741331 : Blo 211809 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B726461 : Blo 211809 726461 := bstep (se 3 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 726461 = 272423) B272423
theorem B1611575 : Blo 211809 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B726839 : Blo 211809 726839 := bstep (se 1 (by rfl) ⟨545129, by rfl⟩ : syracuseStep 726839 = 1090259) B1090259
theorem B727325 : Blo 211809 727325 := bstep (se 3 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 727325 = 272747) B272747
theorem B14686595 : Blo 211809 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B2726459 : Blo 211809 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B728351 : Blo 211809 728351 := bstep (se 1 (by rfl) ⟨546263, by rfl⟩ : syracuseStep 728351 = 1092527) B1092527
theorem B269659 : Blo 211809 269659 := bstep (se 1 (by rfl) ⟨202244, by rfl⟩ : syracuseStep 269659 = 404489) B404489
theorem B1449431 : Blo 211809 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B269887 : Blo 211809 269887 := bstep (se 1 (by rfl) ⟨202415, by rfl⟩ : syracuseStep 269887 = 404831) B404831
theorem B8724185 : Blo 211809 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B1089287 : Blo 211809 1089287 := bstep (se 1 (by rfl) ⟨816965, by rfl⟩ : syracuseStep 1089287 = 1633931) B1633931
theorem B270631 : Blo 211809 270631 := bstep (se 1 (by rfl) ⟨202973, by rfl⟩ : syracuseStep 270631 = 405947) B405947
theorem B1843505 : Blo 211809 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B270955 : Blo 211809 270955 := bstep (se 1 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 270955 = 406433) B406433
theorem B2761361 : Blo 211809 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B1549115 : Blo 211809 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B2040653 : Blo 211809 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B271183 : Blo 211809 271183 := bstep (se 1 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 271183 = 406775) B406775
theorem B402347 : Blo 211809 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B1090505 : Blo 211809 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B238567 : Blo 211809 238567 := bstep (se 1 (by rfl) ⟨178925, by rfl⟩ : syracuseStep 238567 = 357851) B357851
theorem B402727 : Blo 211809 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B402887 : Blo 211809 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B763937 : Blo 211809 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B305417 : Blo 211809 305417 := bstep (se 2 (by rfl) ⟨114531, by rfl⟩ : syracuseStep 305417 = 229063) B229063
theorem B4696379 : Blo 211809 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B404041 : Blo 211809 404041 := bstep (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) B303031
theorem B240223 : Blo 211809 240223 := bstep (se 1 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 240223 = 360335) B360335
theorem B1092203 : Blo 211809 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B273071 : Blo 211809 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B2304733 : Blo 211809 2304733 := bstep (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) B864275
theorem B928655 : Blo 211809 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B1453373 : Blo 211809 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B536159 : Blo 211809 536159 := bstep (se 1 (by rfl) ⟨402119, by rfl⟩ : syracuseStep 536159 = 804239) B804239
theorem B241375 : Blo 211809 241375 := bstep (se 1 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 241375 = 362063) B362063
theorem B1159069 : Blo 211809 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B241951 : Blo 211809 241951 := bstep (se 1 (by rfl) ⟨181463, by rfl⟩ : syracuseStep 241951 = 362927) B362927
theorem B536939 : Blo 211809 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B1159589 : Blo 211809 1159589 := bstep (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) B217423
theorem B405985 : Blo 211809 405985 := bstep (se 2 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 405985 = 304489) B304489
theorem B537151 : Blo 211809 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B242239 : Blo 211809 242239 := bstep (se 1 (by rfl) ⟨181679, by rfl⟩ : syracuseStep 242239 = 363359) B363359
theorem B1225313 : Blo 211809 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B537263 : Blo 211809 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B340967 : Blo 211809 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B537587 : Blo 211809 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B537799 : Blo 211809 537799 := bstep (se 1 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 537799 = 806699) B806699
theorem B3880331 : Blo 211809 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B4634117 : Blo 211809 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B2340485 : Blo 211809 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B3192605 : Blo 211809 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B539207 : Blo 211809 539207 := bstep (se 1 (by rfl) ⟨404405, by rfl⟩ : syracuseStep 539207 = 808811) B808811
theorem B539257 : Blo 211809 539257 := bstep (se 2 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 539257 = 404443) B404443
theorem B6896279 : Blo 211809 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B211867 : Blo 211809 211867 := bstep (se 1 (by rfl) ⟨158900, by rfl⟩ : syracuseStep 211867 = 317801) B317801
theorem B1162171 : Blo 211809 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B211919 : Blo 211809 211919 := bstep (se 1 (by rfl) ⟨158939, by rfl⟩ : syracuseStep 211919 = 317879) B317879
theorem B211943 : Blo 211809 211943 := bstep (se 1 (by rfl) ⟨158957, by rfl⟩ : syracuseStep 211943 = 317915) B317915
theorem B7846955 : Blo 211809 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B6929495 : Blo 211809 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B408719 : Blo 211809 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B212255 : Blo 211809 212255 := bstep (se 1 (by rfl) ⟨159191, by rfl⟩ : syracuseStep 212255 = 318383) B318383
theorem B408863 : Blo 211809 408863 := bstep (se 1 (by rfl) ⟨306647, by rfl⟩ : syracuseStep 408863 = 613295) B613295
theorem B212315 : Blo 211809 212315 := bstep (se 1 (by rfl) ⟨159236, by rfl⟩ : syracuseStep 212315 = 318473) B318473
theorem B212335 : Blo 211809 212335 := bstep (se 1 (by rfl) ⟨159251, by rfl⟩ : syracuseStep 212335 = 318503) B318503
theorem B212391 : Blo 211809 212391 := bstep (se 1 (by rfl) ⟨159293, by rfl⟩ : syracuseStep 212391 = 318587) B318587
theorem B3128777 : Blo 211809 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B212475 : Blo 211809 212475 := bstep (se 1 (by rfl) ⟨159356, by rfl⟩ : syracuseStep 212475 = 318713) B318713
theorem B212543 : Blo 211809 212543 := bstep (se 1 (by rfl) ⟨159407, by rfl⟩ : syracuseStep 212543 = 318815) B318815
theorem B212551 : Blo 211809 212551 := bstep (se 1 (by rfl) ⟨159413, by rfl⟩ : syracuseStep 212551 = 318827) B318827
theorem B310879 : Blo 211809 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B212703 : Blo 211809 212703 := bstep (se 1 (by rfl) ⟨159527, by rfl⟩ : syracuseStep 212703 = 319055) B319055
theorem B1228547 : Blo 211809 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B212783 : Blo 211809 212783 := bstep (se 1 (by rfl) ⟨159587, by rfl⟩ : syracuseStep 212783 = 319175) B319175
theorem B638777 : Blo 211809 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B212891 : Blo 211809 212891 := bstep (se 1 (by rfl) ⟨159668, by rfl⟩ : syracuseStep 212891 = 319337) B319337
theorem B212943 : Blo 211809 212943 := bstep (se 1 (by rfl) ⟨159707, by rfl⟩ : syracuseStep 212943 = 319415) B319415
theorem B212967 : Blo 211809 212967 := bstep (se 1 (by rfl) ⟨159725, by rfl⟩ : syracuseStep 212967 = 319451) B319451
theorem B213279 : Blo 211809 213279 := bstep (se 1 (by rfl) ⟨159959, by rfl⟩ : syracuseStep 213279 = 319919) B319919
theorem B213339 : Blo 211809 213339 := bstep (se 1 (by rfl) ⟨160004, by rfl⟩ : syracuseStep 213339 = 320009) B320009
theorem B541019 : Blo 211809 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B213359 : Blo 211809 213359 := bstep (se 1 (by rfl) ⟨160019, by rfl⟩ : syracuseStep 213359 = 320039) B320039
theorem B541039 : Blo 211809 541039 := bstep (se 1 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 541039 = 811559) B811559
theorem B213415 : Blo 211809 213415 := bstep (se 1 (by rfl) ⟨160061, by rfl⟩ : syracuseStep 213415 = 320123) B320123
theorem B737711 : Blo 211809 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B213499 : Blo 211809 213499 := bstep (se 1 (by rfl) ⟨160124, by rfl⟩ : syracuseStep 213499 = 320249) B320249
theorem B213567 : Blo 211809 213567 := bstep (se 1 (by rfl) ⟨160175, by rfl⟩ : syracuseStep 213567 = 320351) B320351
theorem B606791 : Blo 211809 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B213575 : Blo 211809 213575 := bstep (se 1 (by rfl) ⟨160181, by rfl⟩ : syracuseStep 213575 = 320363) B320363
theorem B9290375 : Blo 211809 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B213727 : Blo 211809 213727 := bstep (se 1 (by rfl) ⟨160295, by rfl⟩ : syracuseStep 213727 = 320591) B320591
theorem B213807 : Blo 211809 213807 := bstep (se 1 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 213807 = 320711) B320711
theorem B213915 : Blo 211809 213915 := bstep (se 1 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 213915 = 320873) B320873
theorem B1295297 : Blo 211809 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B213967 : Blo 211809 213967 := bstep (se 1 (by rfl) ⟨160475, by rfl⟩ : syracuseStep 213967 = 320951) B320951
theorem B213991 : Blo 211809 213991 := bstep (se 1 (by rfl) ⟨160493, by rfl⟩ : syracuseStep 213991 = 320987) B320987
theorem B541687 : Blo 211809 541687 := bstep (se 1 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 541687 = 812531) B812531
theorem B1721351 : Blo 211809 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B1623239 : Blo 211809 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B836857 : Blo 211809 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B214303 : Blo 211809 214303 := bstep (se 1 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 214303 = 321455) B321455
theorem B541991 : Blo 211809 541991 := bstep (se 1 (by rfl) ⟨406493, by rfl⟩ : syracuseStep 541991 = 812987) B812987
theorem B2639147 : Blo 211809 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B214363 : Blo 211809 214363 := bstep (se 1 (by rfl) ⟨160772, by rfl⟩ : syracuseStep 214363 = 321545) B321545
theorem B214383 : Blo 211809 214383 := bstep (se 1 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 214383 = 321575) B321575
theorem B214439 : Blo 211809 214439 := bstep (se 1 (by rfl) ⟨160829, by rfl⟩ : syracuseStep 214439 = 321659) B321659
theorem B476603 : Blo 211809 476603 := bstep (se 1 (by rfl) ⟨357452, by rfl⟩ : syracuseStep 476603 = 714905) B714905
theorem B214523 : Blo 211809 214523 := bstep (se 1 (by rfl) ⟨160892, by rfl⟩ : syracuseStep 214523 = 321785) B321785
theorem B476729 : Blo 211809 476729 := bstep (se 2 (by rfl) ⟨178773, by rfl⟩ : syracuseStep 476729 = 357547) B357547
theorem B214591 : Blo 211809 214591 := bstep (se 1 (by rfl) ⟨160943, by rfl⟩ : syracuseStep 214591 = 321887) B321887
theorem B214599 : Blo 211809 214599 := bstep (se 1 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 214599 = 321899) B321899
theorem B214751 : Blo 211809 214751 := bstep (se 1 (by rfl) ⟨161063, by rfl⟩ : syracuseStep 214751 = 322127) B322127
theorem B214831 : Blo 211809 214831 := bstep (se 1 (by rfl) ⟨161123, by rfl⟩ : syracuseStep 214831 = 322247) B322247
theorem B214939 : Blo 211809 214939 := bstep (se 1 (by rfl) ⟨161204, by rfl⟩ : syracuseStep 214939 = 322409) B322409
theorem B1034167 : Blo 211809 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B214991 : Blo 211809 214991 := bstep (se 1 (by rfl) ⟨161243, by rfl⟩ : syracuseStep 214991 = 322487) B322487
theorem B215015 : Blo 211809 215015 := bstep (se 1 (by rfl) ⟨161261, by rfl⟩ : syracuseStep 215015 = 322523) B322523
theorem B477395 : Blo 211809 477395 := bstep (se 1 (by rfl) ⟨358046, by rfl⟩ : syracuseStep 477395 = 716093) B716093
theorem B7948529 : Blo 211809 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B477449 : Blo 211809 477449 := bstep (se 2 (by rfl) ⟨179043, by rfl⟩ : syracuseStep 477449 = 358087) B358087
theorem B215327 : Blo 211809 215327 := bstep (se 1 (by rfl) ⟨161495, by rfl⟩ : syracuseStep 215327 = 322991) B322991
theorem B215387 : Blo 211809 215387 := bstep (se 1 (by rfl) ⟨161540, by rfl⟩ : syracuseStep 215387 = 323081) B323081
theorem B215407 : Blo 211809 215407 := bstep (se 1 (by rfl) ⟨161555, by rfl⟩ : syracuseStep 215407 = 323111) B323111
theorem B215463 : Blo 211809 215463 := bstep (se 1 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 215463 = 323195) B323195
theorem B477665 : Blo 211809 477665 := bstep (se 2 (by rfl) ⟨179124, by rfl⟩ : syracuseStep 477665 = 358249) B358249
theorem B215547 : Blo 211809 215547 := bstep (se 1 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 215547 = 323321) B323321
theorem B215615 : Blo 211809 215615 := bstep (se 1 (by rfl) ⟨161711, by rfl⟩ : syracuseStep 215615 = 323423) B323423
theorem B215623 : Blo 211809 215623 := bstep (se 1 (by rfl) ⟨161717, by rfl⟩ : syracuseStep 215623 = 323435) B323435
theorem B215775 : Blo 211809 215775 := bstep (se 1 (by rfl) ⟨161831, by rfl⟩ : syracuseStep 215775 = 323663) B323663
theorem B477971 : Blo 211809 477971 := bstep (se 1 (by rfl) ⟨358478, by rfl⟩ : syracuseStep 477971 = 716957) B716957
theorem B576335 : Blo 211809 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B543631 : Blo 211809 543631 := bstep (se 1 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 543631 = 815447) B815447
theorem B3689387 : Blo 211809 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B478331 : Blo 211809 478331 := bstep (se 1 (by rfl) ⟨358748, by rfl⟩ : syracuseStep 478331 = 717497) B717497
theorem B478457 : Blo 211809 478457 := bstep (se 2 (by rfl) ⟨179421, by rfl⟩ : syracuseStep 478457 = 358843) B358843
theorem B1822013 : Blo 211809 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B544097 : Blo 211809 544097 := bstep (se 2 (by rfl) ⟨204036, by rfl⟩ : syracuseStep 544097 = 408073) B408073
theorem B478601 : Blo 211809 478601 := bstep (se 2 (by rfl) ⟨179475, by rfl⟩ : syracuseStep 478601 = 358951) B358951
theorem B478727 : Blo 211809 478727 := bstep (se 1 (by rfl) ⟨359045, by rfl⟩ : syracuseStep 478727 = 718091) B718091
theorem B478907 : Blo 211809 478907 := bstep (se 1 (by rfl) ⟨359180, by rfl⟩ : syracuseStep 478907 = 718361) B718361
theorem B1101523 : Blo 211809 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B511751 : Blo 211809 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B544553 : Blo 211809 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B479033 : Blo 211809 479033 := bstep (se 2 (by rfl) ⟨179637, by rfl⟩ : syracuseStep 479033 = 359275) B359275
theorem B610105 : Blo 211809 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B413497 : Blo 211809 413497 := bstep (se 2 (by rfl) ⟨155061, by rfl⟩ : syracuseStep 413497 = 310123) B310123
theorem B512009 : Blo 211809 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B2740553 : Blo 211809 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B414119 : Blo 211809 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B479663 : Blo 211809 479663 := bstep (se 1 (by rfl) ⟨359747, by rfl⟩ : syracuseStep 479663 = 719495) B719495
theorem B1036745 : Blo 211809 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B479699 : Blo 211809 479699 := bstep (se 1 (by rfl) ⟨359774, by rfl⟩ : syracuseStep 479699 = 719549) B719549
theorem B479807 : Blo 211809 479807 := bstep (se 1 (by rfl) ⟨359855, by rfl⟩ : syracuseStep 479807 = 719711) B719711
theorem B11686517 : Blo 211809 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B479915 : Blo 211809 479915 := bstep (se 1 (by rfl) ⟨359936, by rfl⟩ : syracuseStep 479915 = 719873) B719873
theorem B611039 : Blo 211809 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B578323 : Blo 211809 578323 := bstep (se 1 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 578323 = 867485) B867485
theorem B545555 : Blo 211809 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B676687 : Blo 211809 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B1627127 : Blo 211809 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B480455 : Blo 211809 480455 := bstep (se 1 (by rfl) ⟨360341, by rfl⟩ : syracuseStep 480455 = 720683) B720683
theorem B1529047 : Blo 211809 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B546011 : Blo 211809 546011 := bstep (se 1 (by rfl) ⟨409508, by rfl⟩ : syracuseStep 546011 = 819017) B819017
theorem B546041 : Blo 211809 546041 := bstep (se 2 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 546041 = 409531) B409531
theorem B480635 : Blo 211809 480635 := bstep (se 1 (by rfl) ⟨360476, by rfl⟩ : syracuseStep 480635 = 720953) B720953
theorem B480761 : Blo 211809 480761 := bstep (se 2 (by rfl) ⟨180285, by rfl⟩ : syracuseStep 480761 = 360571) B360571
theorem B906785 : Blo 211809 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B480851 : Blo 211809 480851 := bstep (se 1 (by rfl) ⟨360638, by rfl⟩ : syracuseStep 480851 = 721277) B721277
theorem B481031 : Blo 211809 481031 := bstep (se 1 (by rfl) ⟨360773, by rfl⟩ : syracuseStep 481031 = 721547) B721547
theorem B481643 : Blo 211809 481643 := bstep (se 1 (by rfl) ⟨361232, by rfl⟩ : syracuseStep 481643 = 722465) B722465
theorem B317807 : Blo 211809 317807 := bstep (se 1 (by rfl) ⟨238355, by rfl⟩ : syracuseStep 317807 = 476711) B476711
theorem B1956221 : Blo 211809 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B481787 : Blo 211809 481787 := bstep (se 1 (by rfl) ⟨361340, by rfl⟩ : syracuseStep 481787 = 722681) B722681
theorem B318023 : Blo 211809 318023 := bstep (se 1 (by rfl) ⟨238517, by rfl⟩ : syracuseStep 318023 = 477035) B477035
theorem B318059 : Blo 211809 318059 := bstep (se 1 (by rfl) ⟨238544, by rfl⟩ : syracuseStep 318059 = 477089) B477089
theorem B481913 : Blo 211809 481913 := bstep (se 2 (by rfl) ⟨180717, by rfl⟩ : syracuseStep 481913 = 361435) B361435
theorem B481967 : Blo 211809 481967 := bstep (se 1 (by rfl) ⟨361475, by rfl⟩ : syracuseStep 481967 = 722951) B722951
theorem B482039 : Blo 211809 482039 := bstep (se 1 (by rfl) ⟨361529, by rfl⟩ : syracuseStep 482039 = 723059) B723059
theorem B318287 : Blo 211809 318287 := bstep (se 1 (by rfl) ⟨238715, by rfl⟩ : syracuseStep 318287 = 477431) B477431
theorem B1629071 : Blo 211809 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B482219 : Blo 211809 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B318683 : Blo 211809 318683 := bstep (se 1 (by rfl) ⟨239012, by rfl⟩ : syracuseStep 318683 = 478025) B478025
theorem B318857 : Blo 211809 318857 := bstep (se 2 (by rfl) ⟨119571, by rfl⟩ : syracuseStep 318857 = 239143) B239143
theorem B482759 : Blo 211809 482759 := bstep (se 1 (by rfl) ⟨362069, by rfl⟩ : syracuseStep 482759 = 724139) B724139
theorem B1826387 : Blo 211809 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B319211 : Blo 211809 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B483119 : Blo 211809 483119 := bstep (se 1 (by rfl) ⟨362339, by rfl⟩ : syracuseStep 483119 = 724679) B724679
theorem B286519 : Blo 211809 286519 := bstep (se 1 (by rfl) ⟨214889, by rfl⟩ : syracuseStep 286519 = 429779) B429779
theorem B3694517 : Blo 211809 3694517 := bstep (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) B346361
theorem B319439 : Blo 211809 319439 := bstep (se 1 (by rfl) ⟨239579, by rfl⟩ : syracuseStep 319439 = 479159) B479159
theorem B1073411 : Blo 211809 1073411 := bstep (se 1 (by rfl) ⟨805058, by rfl⟩ : syracuseStep 1073411 = 1610117) B1610117
theorem B549193 : Blo 211809 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B319835 : Blo 211809 319835 := bstep (se 1 (by rfl) ⟨239876, by rfl⟩ : syracuseStep 319835 = 479753) B479753
theorem B483695 : Blo 211809 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B483767 : Blo 211809 483767 := bstep (se 1 (by rfl) ⟨362825, by rfl⟩ : syracuseStep 483767 = 725651) B725651
theorem B320063 : Blo 211809 320063 := bstep (se 1 (by rfl) ⟨240047, by rfl⟩ : syracuseStep 320063 = 480095) B480095
theorem B1073735 : Blo 211809 1073735 := bstep (se 1 (by rfl) ⟨805301, by rfl⟩ : syracuseStep 1073735 = 1610603) B1610603
theorem B385607 : Blo 211809 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B483911 : Blo 211809 483911 := bstep (se 1 (by rfl) ⟨362933, by rfl⟩ : syracuseStep 483911 = 725867) B725867
theorem B483947 : Blo 211809 483947 := bstep (se 1 (by rfl) ⟨362960, by rfl⟩ : syracuseStep 483947 = 725921) B725921
theorem B2482859 : Blo 211809 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B320183 : Blo 211809 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B1106783 : Blo 211809 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B320411 : Blo 211809 320411 := bstep (se 1 (by rfl) ⟨240308, by rfl⟩ : syracuseStep 320411 = 480617) B480617
theorem B484343 : Blo 211809 484343 := bstep (se 1 (by rfl) ⟨363257, by rfl⟩ : syracuseStep 484343 = 726515) B726515
theorem B648425 : Blo 211809 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B320807 : Blo 211809 320807 := bstep (se 1 (by rfl) ⟨240605, by rfl⟩ : syracuseStep 320807 = 481211) B481211
theorem B484703 : Blo 211809 484703 := bstep (se 1 (by rfl) ⟨363527, by rfl⟩ : syracuseStep 484703 = 727055) B727055
theorem B320891 : Blo 211809 320891 := bstep (se 1 (by rfl) ⟨240668, by rfl⟩ : syracuseStep 320891 = 481337) B481337
theorem B321017 : Blo 211809 321017 := bstep (se 2 (by rfl) ⟨120381, by rfl⟩ : syracuseStep 321017 = 240763) B240763
theorem B321119 : Blo 211809 321119 := bstep (se 1 (by rfl) ⟨240839, by rfl⟩ : syracuseStep 321119 = 481679) B481679
theorem B419489 : Blo 211809 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B485099 : Blo 211809 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B911159 : Blo 211809 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B321335 : Blo 211809 321335 := bstep (se 1 (by rfl) ⟨241001, by rfl⟩ : syracuseStep 321335 = 482003) B482003
theorem B1075031 : Blo 211809 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B485225 : Blo 211809 485225 := bstep (se 2 (by rfl) ⟨181959, by rfl⟩ : syracuseStep 485225 = 363919) B363919
theorem B2222095 : Blo 211809 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B321641 : Blo 211809 321641 := bstep (se 2 (by rfl) ⟨120615, by rfl⟩ : syracuseStep 321641 = 241231) B241231
theorem B813185 : Blo 211809 813185 := bstep (se 2 (by rfl) ⟨304944, by rfl⟩ : syracuseStep 813185 = 609889) B609889
theorem B2320649 : Blo 211809 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B387337 : Blo 211809 387337 := bstep (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) B290503
theorem B551279 : Blo 211809 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B256379 : Blo 211809 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B715175 : Blo 211809 715175 := bstep (se 1 (by rfl) ⟨536381, by rfl⟩ : syracuseStep 715175 = 1072763) B1072763
theorem B321959 : Blo 211809 321959 := bstep (se 1 (by rfl) ⟨241469, by rfl⟩ : syracuseStep 321959 = 482939) B482939
theorem B322043 : Blo 211809 322043 := bstep (se 1 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 322043 = 483065) B483065
theorem B911911 : Blo 211809 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B715337 : Blo 211809 715337 := bstep (se 2 (by rfl) ⟨268251, by rfl⟩ : syracuseStep 715337 = 536503) B536503
theorem B322169 : Blo 211809 322169 := bstep (se 2 (by rfl) ⟨120813, by rfl⟩ : syracuseStep 322169 = 241627) B241627
theorem B322223 : Blo 211809 322223 := bstep (se 1 (by rfl) ⟨241667, by rfl⟩ : syracuseStep 322223 = 483335) B483335
theorem B322271 : Blo 211809 322271 := bstep (se 1 (by rfl) ⟨241703, by rfl⟩ : syracuseStep 322271 = 483407) B483407
theorem B1829699 : Blo 211809 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B2452355 : Blo 211809 2452355 := bstep (se 1 (by rfl) ⟨1839266, by rfl⟩ : syracuseStep 2452355 = 3678533) B3678533
theorem B322535 : Blo 211809 322535 := bstep (se 1 (by rfl) ⟨241901, by rfl⟩ : syracuseStep 322535 = 483803) B483803
theorem B650227 : Blo 211809 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B31878157 : Blo 211809 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B322793 : Blo 211809 322793 := bstep (se 2 (by rfl) ⟨121047, by rfl⟩ : syracuseStep 322793 = 242095) B242095
theorem B322847 : Blo 211809 322847 := bstep (se 1 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 322847 = 484271) B484271
theorem B454025 : Blo 211809 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B323015 : Blo 211809 323015 := bstep (se 1 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 323015 = 484523) B484523
theorem B1207817 : Blo 211809 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B323369 : Blo 211809 323369 := bstep (se 2 (by rfl) ⟨121263, by rfl⟩ : syracuseStep 323369 = 242527) B242527
theorem B323375 : Blo 211809 323375 := bstep (se 1 (by rfl) ⟨242531, by rfl⟩ : syracuseStep 323375 = 485063) B485063
theorem B815129 : Blo 211809 815129 := bstep (se 2 (by rfl) ⟨305673, by rfl⟩ : syracuseStep 815129 = 611347) B611347
theorem B1077299 : Blo 211809 1077299 := bstep (se 1 (by rfl) ⟨807974, by rfl⟩ : syracuseStep 1077299 = 1615949) B1615949
theorem B717011 : Blo 211809 717011 := bstep (se 1 (by rfl) ⟨537758, by rfl⟩ : syracuseStep 717011 = 1075517) B1075517
theorem B913619 : Blo 211809 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B258427 : Blo 211809 258427 := bstep (se 1 (by rfl) ⟨193820, by rfl⟩ : syracuseStep 258427 = 387641) B387641
theorem B717281 : Blo 211809 717281 := bstep (se 2 (by rfl) ⟨268980, by rfl⟩ : syracuseStep 717281 = 537961) B537961
theorem B324091 : Blo 211809 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B4452889 : Blo 211809 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B979609 : Blo 211809 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B455777 : Blo 211809 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B1209593 : Blo 211809 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B1078919 : Blo 211809 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B718523 : Blo 211809 718523 := bstep (se 1 (by rfl) ⟨538892, by rfl⟩ : syracuseStep 718523 = 1077785) B1077785
theorem B9598907 : Blo 211809 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B2357495 : Blo 211809 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B227615 : Blo 211809 227615 := bstep (se 1 (by rfl) ⟨170711, by rfl⟩ : syracuseStep 227615 = 341423) B341423
theorem B883055 : Blo 211809 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B358823 : Blo 211809 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B293371 : Blo 211809 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B358985 : Blo 211809 358985 := bstep (se 2 (by rfl) ⟨134619, by rfl⟩ : syracuseStep 358985 = 269239) B269239
theorem B818045 : Blo 211809 818045 := bstep (se 3 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 818045 = 306767) B306767
theorem B1080539 : Blo 211809 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B1375555 : Blo 211809 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B720467 : Blo 211809 720467 := bstep (se 1 (by rfl) ⟨540350, by rfl⟩ : syracuseStep 720467 = 1080701) B1080701
theorem B360031 : Blo 211809 360031 := bstep (se 1 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 360031 = 540047) B540047
theorem B818849 : Blo 211809 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B360247 : Blo 211809 360247 := bstep (se 1 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 360247 = 540371) B540371
theorem B721115 : Blo 211809 721115 := bstep (se 1 (by rfl) ⟨540836, by rfl⟩ : syracuseStep 721115 = 1081673) B1081673
theorem B360679 : Blo 211809 360679 := bstep (se 1 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 360679 = 541019) B541019
theorem B491807 : Blo 211809 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B360841 : Blo 211809 360841 := bstep (se 2 (by rfl) ⟨135315, by rfl⟩ : syracuseStep 360841 = 270631) B270631
theorem B6193583 : Blo 211809 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B721385 : Blo 211809 721385 := bstep (se 2 (by rfl) ⟨270519, by rfl⟩ : syracuseStep 721385 = 541039) B541039
theorem B3080699 : Blo 211809 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B1147567 : Blo 211809 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B1082159 : Blo 211809 1082159 := bstep (se 1 (by rfl) ⟨811619, by rfl⟩ : syracuseStep 1082159 = 1623239) B1623239
theorem B361273 : Blo 211809 361273 := bstep (se 2 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 361273 = 270955) B270955
theorem B361327 : Blo 211809 361327 := bstep (se 1 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 361327 = 541991) B541991
theorem B721979 : Blo 211809 721979 := bstep (se 1 (by rfl) ⟨541484, by rfl⟩ : syracuseStep 721979 = 1082969) B1082969
theorem B361577 : Blo 211809 361577 := bstep (se 2 (by rfl) ⟨135591, by rfl⟩ : syracuseStep 361577 = 271183) B271183
theorem B722249 : Blo 211809 722249 := bstep (se 2 (by rfl) ⟨270843, by rfl⟩ : syracuseStep 722249 = 541687) B541687
theorem B6620957 : Blo 211809 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B11142947 : Blo 211809 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B2459591 : Blo 211809 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B1214675 : Blo 211809 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B362731 : Blo 211809 362731 := bstep (se 1 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 362731 = 544097) B544097
theorem B1313063 : Blo 211809 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B363035 : Blo 211809 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B1378889 : Blo 211809 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B1968745 : Blo 211809 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B691163 : Blo 211809 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B363703 : Blo 211809 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B1084751 : Blo 211809 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B1215881 : Blo 211809 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B364007 : Blo 211809 364007 := bstep (se 1 (by rfl) ⟨273005, by rfl⟩ : syracuseStep 364007 = 546011) B546011
theorem B364027 : Blo 211809 364027 := bstep (se 1 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 364027 = 546041) B546041
theorem B724841 : Blo 211809 724841 := bstep (se 2 (by rfl) ⟨271815, by rfl⟩ : syracuseStep 724841 = 543631) B543631
theorem B42504209 : Blo 211809 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B3084389 : Blo 211809 3084389 := bstep (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) B578323
theorem B1086047 : Blo 211809 1086047 := bstep (se 1 (by rfl) ⟨814535, by rfl⟩ : syracuseStep 1086047 = 1629071) B1629071
theorem B1217591 : Blo 211809 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B726191 : Blo 211809 726191 := bstep (se 1 (by rfl) ⟨544643, by rfl⟩ : syracuseStep 726191 = 1089287) B1089287
theorem B4199633 : Blo 211809 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1545425 : Blo 211809 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B2463011 : Blo 211809 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B1840907 : Blo 211809 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B727003 : Blo 211809 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B432121 : Blo 211809 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B5937185 : Blo 211809 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B268591 : Blo 211809 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B4463237 : Blo 211809 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B1547099 : Blo 211809 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B367519 : Blo 211809 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B2038729 : Blo 211809 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B728135 : Blo 211809 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B728189 : Blo 211809 728189 := bstep (se 3 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 728189 = 273071) B273071
theorem B1219799 : Blo 211809 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B303851 : Blo 211809 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B1942501 : Blo 211809 1942501 := bstep (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) B364219
theorem B3089411 : Blo 211809 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B1549561 : Blo 211809 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B6399271 : Blo 211809 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B239215 : Blo 211809 239215 := bstep (se 1 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 239215 = 358823) B358823
theorem B239323 : Blo 211809 239323 := bstep (se 1 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 239323 = 358985) B358985
theorem B4597519 : Blo 211809 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B272479 : Blo 211809 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B272575 : Blo 211809 272575 := bstep (se 1 (by rfl) ⟨204431, by rfl⟩ : syracuseStep 272575 = 408863) B408863
theorem B305975 : Blo 211809 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B240475 : Blo 211809 240475 := bstep (se 1 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 240475 = 360713) B360713
theorem B404527 : Blo 211809 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B732257 : Blo 211809 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B2436317 : Blo 211809 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B863531 : Blo 211809 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B699967 : Blo 211809 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B241447 : Blo 211809 241447 := bstep (se 1 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 241447 = 362171) B362171
theorem B1028285 : Blo 211809 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B536969 : Blo 211809 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B242599 : Blo 211809 242599 := bstep (se 1 (by rfl) ⟨181949, by rfl⟩ : syracuseStep 242599 = 363899) B363899
theorem B341167 : Blo 211809 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B341339 : Blo 211809 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B2962793 : Blo 211809 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B276079 : Blo 211809 276079 := bstep (se 1 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 276079 = 414119) B414119
theorem B1160887 : Blo 211809 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B407359 : Blo 211809 407359 := bstep (se 1 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 407359 = 611039) B611039
theorem B3979145 : Blo 211809 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B538721 : Blo 211809 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B604523 : Blo 211809 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B866969 : Blo 211809 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B211871 : Blo 211809 211871 := bstep (se 1 (by rfl) ⟨158903, by rfl⟩ : syracuseStep 211871 = 317807) B317807
theorem B1817639 : Blo 211809 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B212015 : Blo 211809 212015 := bstep (se 1 (by rfl) ⟨159011, by rfl⟩ : syracuseStep 212015 = 318023) B318023
theorem B212039 : Blo 211809 212039 := bstep (se 1 (by rfl) ⟨159029, by rfl⟩ : syracuseStep 212039 = 318059) B318059
theorem B212191 : Blo 211809 212191 := bstep (se 1 (by rfl) ⟨159143, by rfl⟩ : syracuseStep 212191 = 318287) B318287
theorem B212455 : Blo 211809 212455 := bstep (se 1 (by rfl) ⟨159341, by rfl⟩ : syracuseStep 212455 = 318683) B318683
theorem B212571 : Blo 211809 212571 := bstep (se 1 (by rfl) ⟨159428, by rfl⟩ : syracuseStep 212571 = 318857) B318857
theorem B966287 : Blo 211809 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B5816123 : Blo 211809 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B212807 : Blo 211809 212807 := bstep (se 1 (by rfl) ⟨159605, by rfl⟩ : syracuseStep 212807 = 319211) B319211
theorem B212959 : Blo 211809 212959 := bstep (se 1 (by rfl) ⟨159719, by rfl⟩ : syracuseStep 212959 = 319439) B319439
theorem B1229003 : Blo 211809 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B213223 : Blo 211809 213223 := bstep (se 1 (by rfl) ⟨159917, by rfl⟩ : syracuseStep 213223 = 319835) B319835
theorem B213375 : Blo 211809 213375 := bstep (se 1 (by rfl) ⟨160031, by rfl⟩ : syracuseStep 213375 = 320063) B320063
theorem B213455 : Blo 211809 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B344569 : Blo 211809 344569 := bstep (se 2 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 344569 = 258427) B258427
theorem B1032743 : Blo 211809 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B1360435 : Blo 211809 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B737855 : Blo 211809 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B213607 : Blo 211809 213607 := bstep (se 1 (by rfl) ⟨160205, by rfl⟩ : syracuseStep 213607 = 320411) B320411
theorem B541313 : Blo 211809 541313 := bstep (se 2 (by rfl) ⟨202992, by rfl⟩ : syracuseStep 541313 = 405985) B405985
theorem B606973 : Blo 211809 606973 := bstep (se 3 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 606973 = 227615) B227615
theorem B213871 : Blo 211809 213871 := bstep (se 1 (by rfl) ⟨160403, by rfl⟩ : syracuseStep 213871 = 320807) B320807
theorem B213927 : Blo 211809 213927 := bstep (se 1 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 213927 = 320891) B320891
theorem B214011 : Blo 211809 214011 := bstep (se 1 (by rfl) ⟨160508, by rfl⟩ : syracuseStep 214011 = 321017) B321017
theorem B214079 : Blo 211809 214079 := bstep (se 1 (by rfl) ⟨160559, by rfl⟩ : syracuseStep 214079 = 321119) B321119
theorem B902249 : Blo 211809 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B279659 : Blo 211809 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B607439 : Blo 211809 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B214223 : Blo 211809 214223 := bstep (se 1 (by rfl) ⟨160667, by rfl⟩ : syracuseStep 214223 = 321335) B321335
theorem B509291 : Blo 211809 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B214427 : Blo 211809 214427 := bstep (se 1 (by rfl) ⟨160820, by rfl⟩ : syracuseStep 214427 = 321641) B321641
theorem B542123 : Blo 211809 542123 := bstep (se 1 (by rfl) ⟨406592, by rfl⟩ : syracuseStep 542123 = 813185) B813185
theorem B3130919 : Blo 211809 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B476783 : Blo 211809 476783 := bstep (se 1 (by rfl) ⟨357587, by rfl⟩ : syracuseStep 476783 = 715175) B715175
theorem B214639 : Blo 211809 214639 := bstep (se 1 (by rfl) ⟨160979, by rfl⟩ : syracuseStep 214639 = 321959) B321959
theorem B214695 : Blo 211809 214695 := bstep (se 1 (by rfl) ⟨161021, by rfl⟩ : syracuseStep 214695 = 322043) B322043
theorem B476891 : Blo 211809 476891 := bstep (se 1 (by rfl) ⟨357668, by rfl⟩ : syracuseStep 476891 = 715337) B715337
theorem B214779 : Blo 211809 214779 := bstep (se 1 (by rfl) ⟨161084, by rfl⟩ : syracuseStep 214779 = 322169) B322169
theorem B214815 : Blo 211809 214815 := bstep (se 1 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 214815 = 322223) B322223
theorem B214847 : Blo 211809 214847 := bstep (se 1 (by rfl) ⟨161135, by rfl⟩ : syracuseStep 214847 = 322271) B322271
theorem B215023 : Blo 211809 215023 := bstep (se 1 (by rfl) ⟨161267, by rfl⟩ : syracuseStep 215023 = 322535) B322535
theorem B215195 : Blo 211809 215195 := bstep (se 1 (by rfl) ⟨161396, by rfl⟩ : syracuseStep 215195 = 322793) B322793
theorem B215231 : Blo 211809 215231 := bstep (se 1 (by rfl) ⟨161423, by rfl⟩ : syracuseStep 215231 = 322847) B322847
theorem B968915 : Blo 211809 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B215343 : Blo 211809 215343 := bstep (se 1 (by rfl) ⟨161507, by rfl⟩ : syracuseStep 215343 = 323015) B323015
theorem B3066173 : Blo 211809 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B805211 : Blo 211809 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B215579 : Blo 211809 215579 := bstep (se 1 (by rfl) ⟨161684, by rfl⟩ : syracuseStep 215579 = 323369) B323369
theorem B215583 : Blo 211809 215583 := bstep (se 1 (by rfl) ⟨161687, by rfl⟩ : syracuseStep 215583 = 323375) B323375
theorem B543419 : Blo 211809 543419 := bstep (se 1 (by rfl) ⟨407564, by rfl⟩ : syracuseStep 543419 = 815129) B815129
theorem B478007 : Blo 211809 478007 := bstep (se 1 (by rfl) ⟨358505, by rfl⟩ : syracuseStep 478007 = 717011) B717011
theorem B773059 : Blo 211809 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B478187 : Blo 211809 478187 := bstep (se 1 (by rfl) ⟨358640, by rfl⟩ : syracuseStep 478187 = 717281) B717281
theorem B806395 : Blo 211809 806395 := bstep (se 1 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 806395 = 1209593) B1209593
theorem B1560323 : Blo 211809 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B479015 : Blo 211809 479015 := bstep (se 1 (by rfl) ⟨359261, by rfl⟩ : syracuseStep 479015 = 718523) B718523
theorem B545363 : Blo 211809 545363 := bstep (se 1 (by rfl) ⟨409022, by rfl⟩ : syracuseStep 545363 = 818045) B818045
theorem B5231303 : Blo 211809 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B480041 : Blo 211809 480041 := bstep (se 2 (by rfl) ⟨180015, by rfl⟩ : syracuseStep 480041 = 360031) B360031
theorem B414505 : Blo 211809 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B2085851 : Blo 211809 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B480311 : Blo 211809 480311 := bstep (se 1 (by rfl) ⟨360233, by rfl⟩ : syracuseStep 480311 = 720467) B720467
theorem B382025 : Blo 211809 382025 := bstep (se 2 (by rfl) ⟨143259, by rfl⟩ : syracuseStep 382025 = 286519) B286519
theorem B480329 : Blo 211809 480329 := bstep (se 2 (by rfl) ⟨180123, by rfl⟩ : syracuseStep 480329 = 360247) B360247
theorem B545899 : Blo 211809 545899 := bstep (se 1 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 545899 = 818849) B818849
theorem B1398169 : Blo 211809 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B546203 : Blo 211809 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B218911 : Blo 211809 218911 := bstep (se 1 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 218911 = 328367) B328367
theorem B317735 : Blo 211809 317735 := bstep (se 1 (by rfl) ⟨238301, by rfl⟩ : syracuseStep 317735 = 476603) B476603
theorem B317819 : Blo 211809 317819 := bstep (se 1 (by rfl) ⟨238364, by rfl⟩ : syracuseStep 317819 = 476729) B476729
theorem B318089 : Blo 211809 318089 := bstep (se 2 (by rfl) ⟨119283, by rfl⟩ : syracuseStep 318089 = 238567) B238567
theorem B613021 : Blo 211809 613021 := bstep (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) B229883
theorem B318263 : Blo 211809 318263 := bstep (se 1 (by rfl) ⟨238697, by rfl⟩ : syracuseStep 318263 = 477395) B477395
theorem B5299019 : Blo 211809 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B318299 : Blo 211809 318299 := bstep (se 1 (by rfl) ⟨238724, by rfl⟩ : syracuseStep 318299 = 477449) B477449
theorem B482255 : Blo 211809 482255 := bstep (se 1 (by rfl) ⟨361691, by rfl⟩ : syracuseStep 482255 = 723383) B723383
theorem B482273 : Blo 211809 482273 := bstep (se 2 (by rfl) ⟨180852, by rfl⟩ : syracuseStep 482273 = 361705) B361705
theorem B318443 : Blo 211809 318443 := bstep (se 1 (by rfl) ⟨238832, by rfl⟩ : syracuseStep 318443 = 477665) B477665
theorem B482345 : Blo 211809 482345 := bstep (se 2 (by rfl) ⟨180879, by rfl⟩ : syracuseStep 482345 = 361759) B361759
theorem B318647 : Blo 211809 318647 := bstep (se 1 (by rfl) ⟨238985, by rfl⟩ : syracuseStep 318647 = 477971) B477971
theorem B613727 : Blo 211809 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B744815 : Blo 211809 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B318887 : Blo 211809 318887 := bstep (se 1 (by rfl) ⟨239165, by rfl⟩ : syracuseStep 318887 = 478331) B478331
theorem B318971 : Blo 211809 318971 := bstep (se 1 (by rfl) ⟨239228, by rfl⟩ : syracuseStep 318971 = 478457) B478457
theorem B319067 : Blo 211809 319067 := bstep (se 1 (by rfl) ⟨239300, by rfl⟩ : syracuseStep 319067 = 478601) B478601
theorem B319151 : Blo 211809 319151 := bstep (se 1 (by rfl) ⟨239363, by rfl⟩ : syracuseStep 319151 = 478727) B478727
theorem B1072925 : Blo 211809 1072925 := bstep (se 3 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 1072925 = 402347) B402347
theorem B319271 : Blo 211809 319271 := bstep (se 1 (by rfl) ⟨239453, by rfl⟩ : syracuseStep 319271 = 478907) B478907
theorem B319355 : Blo 211809 319355 := bstep (se 1 (by rfl) ⟨239516, by rfl⟩ : syracuseStep 319355 = 479033) B479033
theorem B909245 : Blo 211809 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B1564645 : Blo 211809 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B1827035 : Blo 211809 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B319775 : Blo 211809 319775 := bstep (se 1 (by rfl) ⟨239831, by rfl⟩ : syracuseStep 319775 = 479663) B479663
theorem B319799 : Blo 211809 319799 := bstep (se 1 (by rfl) ⟨239849, by rfl⟩ : syracuseStep 319799 = 479699) B479699
theorem B516449 : Blo 211809 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B319871 : Blo 211809 319871 := bstep (se 1 (by rfl) ⟨239903, by rfl⟩ : syracuseStep 319871 = 479807) B479807
theorem B7791011 : Blo 211809 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B319943 : Blo 211809 319943 := bstep (se 1 (by rfl) ⟨239957, by rfl⟩ : syracuseStep 319943 = 479915) B479915
theorem B1729133 : Blo 211809 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B287497 : Blo 211809 287497 := bstep (se 2 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 287497 = 215623) B215623
theorem B7037725 : Blo 211809 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B320297 : Blo 211809 320297 := bstep (se 2 (by rfl) ⟨120111, by rfl⟩ : syracuseStep 320297 = 240223) B240223
theorem B320303 : Blo 211809 320303 := bstep (se 1 (by rfl) ⟨240227, by rfl⟩ : syracuseStep 320303 = 480455) B480455
theorem B320423 : Blo 211809 320423 := bstep (se 1 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 320423 = 480635) B480635
theorem B3072977 : Blo 211809 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B484307 : Blo 211809 484307 := bstep (se 1 (by rfl) ⟨363230, by rfl⟩ : syracuseStep 484307 = 726461) B726461
theorem B320507 : Blo 211809 320507 := bstep (se 1 (by rfl) ⟨240380, by rfl⟩ : syracuseStep 320507 = 480761) B480761
theorem B320567 : Blo 211809 320567 := bstep (se 1 (by rfl) ⟨240425, by rfl⟩ : syracuseStep 320567 = 480851) B480851
theorem B320687 : Blo 211809 320687 := bstep (se 1 (by rfl) ⟨240515, by rfl⟩ : syracuseStep 320687 = 481031) B481031
theorem B1074383 : Blo 211809 1074383 := bstep (se 1 (by rfl) ⟨805787, by rfl⟩ : syracuseStep 1074383 = 1611575) B1611575
theorem B484559 : Blo 211809 484559 := bstep (se 1 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 484559 = 726839) B726839
theorem B484883 : Blo 211809 484883 := bstep (se 1 (by rfl) ⟨363662, by rfl⟩ : syracuseStep 484883 = 727325) B727325
theorem B321095 : Blo 211809 321095 := bstep (se 1 (by rfl) ⟨240821, by rfl⟩ : syracuseStep 321095 = 481643) B481643
theorem B1304147 : Blo 211809 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B9791063 : Blo 211809 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B321191 : Blo 211809 321191 := bstep (se 1 (by rfl) ⟨240893, by rfl⟩ : syracuseStep 321191 = 481787) B481787
theorem B321275 : Blo 211809 321275 := bstep (se 1 (by rfl) ⟨240956, by rfl⟩ : syracuseStep 321275 = 481913) B481913
theorem B321311 : Blo 211809 321311 := bstep (se 1 (by rfl) ⟨240983, by rfl⟩ : syracuseStep 321311 = 481967) B481967
theorem B321359 : Blo 211809 321359 := bstep (se 1 (by rfl) ⟨241019, by rfl⟩ : syracuseStep 321359 = 482039) B482039
theorem B321479 : Blo 211809 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B485567 : Blo 211809 485567 := bstep (se 1 (by rfl) ⟨364175, by rfl⟩ : syracuseStep 485567 = 728351) B728351
theorem B1468697 : Blo 211809 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B321833 : Blo 211809 321833 := bstep (se 2 (by rfl) ⟨120687, by rfl⟩ : syracuseStep 321833 = 241375) B241375
theorem B321839 : Blo 211809 321839 := bstep (se 1 (by rfl) ⟨241379, by rfl⟩ : syracuseStep 321839 = 482759) B482759
theorem B813473 : Blo 211809 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B551329 : Blo 211809 551329 := bstep (se 2 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 551329 = 413497) B413497
theorem B322079 : Blo 211809 322079 := bstep (se 1 (by rfl) ⟨241559, by rfl⟩ : syracuseStep 322079 = 483119) B483119
theorem B715607 : Blo 211809 715607 := bstep (se 1 (by rfl) ⟨536705, by rfl⟩ : syracuseStep 715607 = 1073411) B1073411
theorem B322463 : Blo 211809 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B322511 : Blo 211809 322511 := bstep (se 1 (by rfl) ⟨241883, by rfl⟩ : syracuseStep 322511 = 483767) B483767
theorem B322601 : Blo 211809 322601 := bstep (se 2 (by rfl) ⟨120975, by rfl⟩ : syracuseStep 322601 = 241951) B241951
theorem B715823 : Blo 211809 715823 := bstep (se 1 (by rfl) ⟨536867, by rfl⟩ : syracuseStep 715823 = 1073735) B1073735
theorem B322607 : Blo 211809 322607 := bstep (se 1 (by rfl) ⟨241955, by rfl⟩ : syracuseStep 322607 = 483911) B483911
theorem B322631 : Blo 211809 322631 := bstep (se 1 (by rfl) ⟨241973, by rfl⟩ : syracuseStep 322631 = 483947) B483947
theorem B322895 : Blo 211809 322895 := bstep (se 1 (by rfl) ⟨242171, by rfl⟩ : syracuseStep 322895 = 484343) B484343
theorem B814445 : Blo 211809 814445 := bstep (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) B305417
theorem B716201 : Blo 211809 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B322985 : Blo 211809 322985 := bstep (se 2 (by rfl) ⟨121119, by rfl⟩ : syracuseStep 322985 = 242239) B242239
theorem B1306145 : Blo 211809 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B323135 : Blo 211809 323135 := bstep (se 1 (by rfl) ⟨242351, by rfl⟩ : syracuseStep 323135 = 484703) B484703
theorem B683677 : Blo 211809 683677 := bstep (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) B256379
theorem B323399 : Blo 211809 323399 := bstep (se 1 (by rfl) ⟨242549, by rfl⟩ : syracuseStep 323399 = 485099) B485099
theorem B716687 : Blo 211809 716687 := bstep (se 1 (by rfl) ⟨537515, by rfl⟩ : syracuseStep 716687 = 1075031) B1075031
theorem B323483 : Blo 211809 323483 := bstep (se 1 (by rfl) ⟨242612, by rfl⟩ : syracuseStep 323483 = 485225) B485225
theorem B717065 : Blo 211809 717065 := bstep (se 2 (by rfl) ⟨268899, by rfl⟩ : syracuseStep 717065 = 537799) B537799
theorem B1634903 : Blo 211809 1634903 := bstep (se 1 (by rfl) ⟨1226177, by rfl⟩ : syracuseStep 1634903 = 2452355) B2452355
theorem B619103 : Blo 211809 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B1536893 : Blo 211809 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B357439 : Blo 211809 357439 := bstep (se 1 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 357439 = 536159) B536159
theorem B718199 : Blo 211809 718199 := bstep (se 1 (by rfl) ⟨538649, by rfl⟩ : syracuseStep 718199 = 1077299) B1077299
theorem B357959 : Blo 211809 357959 := bstep (se 1 (by rfl) ⟨268469, by rfl⟩ : syracuseStep 357959 = 536939) B536939
theorem B816875 : Blo 211809 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B358175 : Blo 211809 358175 := bstep (se 1 (by rfl) ⟨268631, by rfl⟩ : syracuseStep 358175 = 537263) B537263
theorem B358391 : Blo 211809 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B719009 : Blo 211809 719009 := bstep (se 2 (by rfl) ⟨269628, by rfl⟩ : syracuseStep 719009 = 539257) B539257
theorem B2586887 : Blo 211809 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B1210733 : Blo 211809 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B719279 : Blo 211809 719279 := bstep (se 1 (by rfl) ⟨539459, by rfl⟩ : syracuseStep 719279 = 1078919) B1078919
theorem B2128403 : Blo 211809 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B1571663 : Blo 211809 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B588703 : Blo 211809 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B359471 : Blo 211809 359471 := bstep (se 1 (by rfl) ⟨269603, by rfl⟩ : syracuseStep 359471 = 539207) B539207
theorem B1834073 : Blo 211809 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B359545 : Blo 211809 359545 := bstep (se 2 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 359545 = 269659) B269659
theorem B4619663 : Blo 211809 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B359849 : Blo 211809 359849 := bstep (se 2 (by rfl) ⟨134943, by rfl⟩ : syracuseStep 359849 = 269887) B269887
theorem B720359 : Blo 211809 720359 := bstep (se 1 (by rfl) ⟨540269, by rfl⟩ : syracuseStep 720359 = 1080539) B1080539
theorem B1703405 : Blo 211809 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B819031 : Blo 211809 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B819335 : Blo 211809 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B327871 : Blo 211809 327871 := bstep (se 1 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 327871 = 491807) B491807
theorem B4129055 : Blo 211809 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B688495 : Blo 211809 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B491903 : Blo 211809 491903 := bstep (se 1 (by rfl) ⟨368927, by rfl⟩ : syracuseStep 491903 = 737855) B737855
theorem B360875 : Blo 211809 360875 := bstep (se 1 (by rfl) ⟨270656, by rfl⟩ : syracuseStep 360875 = 541313) B541313
theorem B721439 : Blo 211809 721439 := bstep (se 1 (by rfl) ⟨541079, by rfl⟩ : syracuseStep 721439 = 1082159) B1082159
theorem B459425 : Blo 211809 459425 := bstep (se 2 (by rfl) ⟨172284, by rfl⟩ : syracuseStep 459425 = 344569) B344569
theorem B361415 : Blo 211809 361415 := bstep (se 1 (by rfl) ⟨271061, by rfl⟩ : syracuseStep 361415 = 542123) B542123
theorem B1639727 : Blo 211809 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B2590001 : Blo 211809 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B2066081 : Blo 211809 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B919259 : Blo 211809 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B362279 : Blo 211809 362279 := bstep (se 1 (by rfl) ⟨271709, by rfl⟩ : syracuseStep 362279 = 543419) B543419
theorem B460775 : Blo 211809 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B723167 : Blo 211809 723167 := bstep (se 1 (by rfl) ⟨542375, by rfl⟩ : syracuseStep 723167 = 1084751) B1084751
theorem B6130025 : Blo 211809 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B363305 : Blo 211809 363305 := bstep (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) B272479
theorem B363433 : Blo 211809 363433 := bstep (se 2 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 363433 = 272575) B272575
theorem B363575 : Blo 211809 363575 := bstep (se 1 (by rfl) ⟨272681, by rfl⟩ : syracuseStep 363575 = 545363) B545363
theorem B724031 : Blo 211809 724031 := bstep (se 1 (by rfl) ⟨543023, by rfl⟩ : syracuseStep 724031 = 1086047) B1086047
theorem B2624993 : Blo 211809 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B1642007 : Blo 211809 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B364135 : Blo 211809 364135 := bstep (se 1 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 364135 = 546203) B546203
theorem B3477725 : Blo 211809 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B496543 : Blo 211809 496543 := bstep (se 1 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 496543 = 744815) B744815
theorem B15832493 : Blo 211809 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B1218023 : Blo 211809 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1152755 : Blo 211809 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B1612061 : Blo 211809 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B6527375 : Blo 211809 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B5675741 : Blo 211809 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B727865 : Blo 211809 727865 := bstep (se 2 (by rfl) ⟨272949, by rfl⟩ : syracuseStep 727865 = 545899) B545899
theorem B368105 : Blo 211809 368105 := bstep (se 2 (by rfl) ⟨138039, by rfl⟩ : syracuseStep 368105 = 276079) B276079
theorem B1547849 : Blo 211809 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B1089935 : Blo 211809 1089935 := bstep (se 1 (by rfl) ⟨817451, by rfl⟩ : syracuseStep 1089935 = 1634903) B1634903
theorem B1024595 : Blo 211809 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B1975195 : Blo 211809 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B238639 : Blo 211809 238639 := bstep (se 1 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 238639 = 357959) B357959
theorem B238783 : Blo 211809 238783 := bstep (se 1 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 238783 = 358175) B358175
theorem B238927 : Blo 211809 238927 := bstep (se 1 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 238927 = 358391) B358391
theorem B239647 : Blo 211809 239647 := bstep (se 1 (by rfl) ⟨179735, by rfl⟩ : syracuseStep 239647 = 359471) B359471
theorem B1222715 : Blo 211809 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B239899 : Blo 211809 239899 := bstep (se 1 (by rfl) ⟨179924, by rfl⟩ : syracuseStep 239899 = 359849) B359849
theorem B1092041 : Blo 211809 1092041 := bstep (se 2 (by rfl) ⟨409515, by rfl⟩ : syracuseStep 1092041 = 819031) B819031
theorem B3877415 : Blo 211809 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B1813913 : Blo 211809 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B601499 : Blo 211809 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B241051 : Blo 211809 241051 := bstep (se 1 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 241051 = 361577) B361577
theorem B339527 : Blo 211809 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B9383633 : Blo 211809 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B2044115 : Blo 211809 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B536807 : Blo 211809 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B1650941 : Blo 211809 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B242023 : Blo 211809 242023 := bstep (se 1 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 242023 = 363035) B363035
theorem B8532361 : Blo 211809 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B242671 : Blo 211809 242671 := bstep (se 1 (by rfl) ⟨182003, by rfl⟩ : syracuseStep 242671 = 364007) B364007
theorem B3487535 : Blo 211809 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B1619837 : Blo 211809 1619837 := bstep (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) B607439
theorem B1390567 : Blo 211809 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B2799755 : Blo 211809 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B1030283 : Blo 211809 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B1227271 : Blo 211809 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B1030745 : Blo 211809 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B539369 : Blo 211809 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B211823 : Blo 211809 211823 := bstep (se 1 (by rfl) ⟨158867, by rfl⟩ : syracuseStep 211823 = 317735) B317735
theorem B211879 : Blo 211809 211879 := bstep (se 1 (by rfl) ⟨158909, by rfl⟩ : syracuseStep 211879 = 317819) B317819
theorem B212059 : Blo 211809 212059 := bstep (se 1 (by rfl) ⟨159044, by rfl⟩ : syracuseStep 212059 = 318089) B318089
theorem B212175 : Blo 211809 212175 := bstep (se 1 (by rfl) ⟨159131, by rfl⟩ : syracuseStep 212175 = 318263) B318263
theorem B212199 : Blo 211809 212199 := bstep (se 1 (by rfl) ⟨159149, by rfl⟩ : syracuseStep 212199 = 318299) B318299
theorem B1031399 : Blo 211809 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B212295 : Blo 211809 212295 := bstep (se 1 (by rfl) ⟨159221, by rfl⟩ : syracuseStep 212295 = 318443) B318443
theorem B933289 : Blo 211809 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B212431 : Blo 211809 212431 := bstep (se 1 (by rfl) ⟨159323, by rfl⟩ : syracuseStep 212431 = 318647) B318647
theorem B409151 : Blo 211809 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B212591 : Blo 211809 212591 := bstep (se 1 (by rfl) ⟨159443, by rfl⟩ : syracuseStep 212591 = 318887) B318887
theorem B212647 : Blo 211809 212647 := bstep (se 1 (by rfl) ⟨159485, by rfl⟩ : syracuseStep 212647 = 318971) B318971
theorem B212711 : Blo 211809 212711 := bstep (se 1 (by rfl) ⟨159533, by rfl⟩ : syracuseStep 212711 = 319067) B319067
theorem B212767 : Blo 211809 212767 := bstep (se 1 (by rfl) ⟨159575, by rfl⟩ : syracuseStep 212767 = 319151) B319151
theorem B212847 : Blo 211809 212847 := bstep (se 1 (by rfl) ⟨159635, by rfl⟩ : syracuseStep 212847 = 319271) B319271
theorem B212903 : Blo 211809 212903 := bstep (se 1 (by rfl) ⟨159677, by rfl⟩ : syracuseStep 212903 = 319355) B319355
theorem B213183 : Blo 211809 213183 := bstep (se 1 (by rfl) ⟨159887, by rfl⟩ : syracuseStep 213183 = 319775) B319775
theorem B213199 : Blo 211809 213199 := bstep (se 1 (by rfl) ⟨159899, by rfl⟩ : syracuseStep 213199 = 319799) B319799
theorem B344299 : Blo 211809 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B213247 : Blo 211809 213247 := bstep (se 1 (by rfl) ⟨159935, by rfl⟩ : syracuseStep 213247 = 319871) B319871
theorem B5194007 : Blo 211809 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B213295 : Blo 211809 213295 := bstep (se 1 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 213295 = 319943) B319943
theorem B213531 : Blo 211809 213531 := bstep (se 1 (by rfl) ⟨160148, by rfl⟩ : syracuseStep 213531 = 320297) B320297
theorem B213535 : Blo 211809 213535 := bstep (se 1 (by rfl) ⟨160151, by rfl⟩ : syracuseStep 213535 = 320303) B320303
theorem B213615 : Blo 211809 213615 := bstep (se 1 (by rfl) ⟨160211, by rfl⟩ : syracuseStep 213615 = 320423) B320423
theorem B2048651 : Blo 211809 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B213671 : Blo 211809 213671 := bstep (se 1 (by rfl) ⟨160253, by rfl⟩ : syracuseStep 213671 = 320507) B320507
theorem B213711 : Blo 211809 213711 := bstep (se 1 (by rfl) ⟨160283, by rfl⟩ : syracuseStep 213711 = 320567) B320567
theorem B3916525 : Blo 211809 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B213791 : Blo 211809 213791 := bstep (se 1 (by rfl) ⟨160343, by rfl⟩ : syracuseStep 213791 = 320687) B320687
theorem B214063 : Blo 211809 214063 := bstep (se 1 (by rfl) ⟨160547, by rfl⟩ : syracuseStep 214063 = 321095) B321095
theorem B214127 : Blo 211809 214127 := bstep (se 1 (by rfl) ⟨160595, by rfl⟩ : syracuseStep 214127 = 321191) B321191
theorem B214183 : Blo 211809 214183 := bstep (se 1 (by rfl) ⟨160637, by rfl⟩ : syracuseStep 214183 = 321275) B321275
theorem B214207 : Blo 211809 214207 := bstep (se 1 (by rfl) ⟨160655, by rfl⟩ : syracuseStep 214207 = 321311) B321311
theorem B214239 : Blo 211809 214239 := bstep (se 1 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 214239 = 321359) B321359
theorem B214319 : Blo 211809 214319 := bstep (se 1 (by rfl) ⟨160739, by rfl⟩ : syracuseStep 214319 = 321479) B321479
theorem B476585 : Blo 211809 476585 := bstep (se 2 (by rfl) ⟨178719, by rfl⟩ : syracuseStep 476585 = 357439) B357439
theorem B214555 : Blo 211809 214555 := bstep (se 1 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 214555 = 321833) B321833
theorem B214559 : Blo 211809 214559 := bstep (se 1 (by rfl) ⟨160919, by rfl⟩ : syracuseStep 214559 = 321839) B321839
theorem B542315 : Blo 211809 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B214719 : Blo 211809 214719 := bstep (se 1 (by rfl) ⟨161039, by rfl⟩ : syracuseStep 214719 = 322079) B322079
theorem B477071 : Blo 211809 477071 := bstep (se 1 (by rfl) ⟨357803, by rfl⟩ : syracuseStep 477071 = 715607) B715607
theorem B214975 : Blo 211809 214975 := bstep (se 1 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 214975 = 322463) B322463
theorem B215007 : Blo 211809 215007 := bstep (se 1 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 215007 = 322511) B322511
theorem B215067 : Blo 211809 215067 := bstep (se 1 (by rfl) ⟨161300, by rfl⟩ : syracuseStep 215067 = 322601) B322601
theorem B477215 : Blo 211809 477215 := bstep (se 1 (by rfl) ⟨357911, by rfl⟩ : syracuseStep 477215 = 715823) B715823
theorem B215071 : Blo 211809 215071 := bstep (se 1 (by rfl) ⟨161303, by rfl⟩ : syracuseStep 215071 = 322607) B322607
theorem B215087 : Blo 211809 215087 := bstep (se 1 (by rfl) ⟨161315, by rfl⟩ : syracuseStep 215087 = 322631) B322631
theorem B1624211 : Blo 211809 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B575687 : Blo 211809 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B215263 : Blo 211809 215263 := bstep (se 1 (by rfl) ⟨161447, by rfl⟩ : syracuseStep 215263 = 322895) B322895
theorem B542963 : Blo 211809 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B477467 : Blo 211809 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B215323 : Blo 211809 215323 := bstep (se 1 (by rfl) ⟨161492, by rfl⟩ : syracuseStep 215323 = 322985) B322985
theorem B870763 : Blo 211809 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B215423 : Blo 211809 215423 := bstep (se 1 (by rfl) ⟨161567, by rfl⟩ : syracuseStep 215423 = 323135) B323135
theorem B543145 : Blo 211809 543145 := bstep (se 2 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 543145 = 407359) B407359
theorem B215599 : Blo 211809 215599 := bstep (se 1 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 215599 = 323399) B323399
theorem B477791 : Blo 211809 477791 := bstep (se 1 (by rfl) ⟨358343, by rfl⟩ : syracuseStep 477791 = 716687) B716687
theorem B215655 : Blo 211809 215655 := bstep (se 1 (by rfl) ⟨161741, by rfl⟩ : syracuseStep 215655 = 323483) B323483
theorem B969337 : Blo 211809 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B576161 : Blo 211809 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B478043 : Blo 211809 478043 := bstep (se 1 (by rfl) ⟨358532, by rfl⟩ : syracuseStep 478043 = 717065) B717065
theorem B478799 : Blo 211809 478799 := bstep (se 1 (by rfl) ⟨359099, by rfl⟩ : syracuseStep 478799 = 718199) B718199
theorem B544583 : Blo 211809 544583 := bstep (se 1 (by rfl) ⟨408437, by rfl⟩ : syracuseStep 544583 = 816875) B816875
theorem B479339 : Blo 211809 479339 := bstep (se 1 (by rfl) ⟨359504, by rfl⟩ : syracuseStep 479339 = 719009) B719009
theorem B479393 : Blo 211809 479393 := bstep (se 2 (by rfl) ⟨179772, by rfl⟩ : syracuseStep 479393 = 359545) B359545
theorem B1724591 : Blo 211809 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B807155 : Blo 211809 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B479519 : Blo 211809 479519 := bstep (se 1 (by rfl) ⟨359639, by rfl⟩ : syracuseStep 479519 = 719279) B719279
theorem B2576765 : Blo 211809 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B577979 : Blo 211809 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B480239 : Blo 211809 480239 := bstep (se 1 (by rfl) ⟨360179, by rfl⟩ : syracuseStep 480239 = 720359) B720359
theorem B1135603 : Blo 211809 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B2086193 : Blo 211809 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B480743 : Blo 211809 480743 := bstep (se 1 (by rfl) ⟨360557, by rfl⟩ : syracuseStep 480743 = 721115) B721115
theorem B480905 : Blo 211809 480905 := bstep (se 2 (by rfl) ⟨180339, by rfl⟩ : syracuseStep 480905 = 360679) B360679
theorem B480923 : Blo 211809 480923 := bstep (se 1 (by rfl) ⟨360692, by rfl⟩ : syracuseStep 480923 = 721385) B721385
theorem B2053799 : Blo 211809 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B481121 : Blo 211809 481121 := bstep (se 2 (by rfl) ⟨180420, by rfl⟩ : syracuseStep 481121 = 360841) B360841
theorem B481319 : Blo 211809 481319 := bstep (se 1 (by rfl) ⟨360989, by rfl⟩ : syracuseStep 481319 = 721979) B721979
theorem B481499 : Blo 211809 481499 := bstep (se 1 (by rfl) ⟨361124, by rfl⟩ : syracuseStep 481499 = 722249) B722249
theorem B1530089 : Blo 211809 1530089 := bstep (se 2 (by rfl) ⟨573783, by rfl⟩ : syracuseStep 1530089 = 1147567) B1147567
theorem B809297 : Blo 211809 809297 := bstep (se 2 (by rfl) ⟨303486, by rfl⟩ : syracuseStep 809297 = 606973) B606973
theorem B383329 : Blo 211809 383329 := bstep (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) B287497
theorem B2087279 : Blo 211809 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B317855 : Blo 211809 317855 := bstep (se 1 (by rfl) ⟨238391, by rfl⟩ : syracuseStep 317855 = 476783) B476783
theorem B481697 : Blo 211809 481697 := bstep (se 2 (by rfl) ⟨180636, by rfl⟩ : syracuseStep 481697 = 361273) B361273
theorem B317927 : Blo 211809 317927 := bstep (se 1 (by rfl) ⟨238445, by rfl⟩ : syracuseStep 317927 = 476891) B476891
theorem B481769 : Blo 211809 481769 := bstep (se 2 (by rfl) ⟨180663, by rfl⟩ : syracuseStep 481769 = 361327) B361327
theorem B4413971 : Blo 211809 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B7428631 : Blo 211809 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B645943 : Blo 211809 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B809783 : Blo 211809 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B875375 : Blo 211809 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B318671 : Blo 211809 318671 := bstep (se 1 (by rfl) ⟨239003, by rfl⟩ : syracuseStep 318671 = 478007) B478007
theorem B810269 : Blo 211809 810269 := bstep (se 3 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 810269 = 303851) B303851
theorem B318791 : Blo 211809 318791 := bstep (se 1 (by rfl) ⟨239093, by rfl⟩ : syracuseStep 318791 = 478187) B478187
theorem B318953 : Blo 211809 318953 := bstep (se 2 (by rfl) ⟨119607, by rfl⟩ : syracuseStep 318953 = 239215) B239215
theorem B2940421 : Blo 211809 2940421 := bstep (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) B551329
theorem B810587 : Blo 211809 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B319097 : Blo 211809 319097 := bstep (se 2 (by rfl) ⟨119661, by rfl⟩ : syracuseStep 319097 = 239323) B239323
theorem B1040215 : Blo 211809 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B319343 : Blo 211809 319343 := bstep (se 1 (by rfl) ⟨239507, by rfl⟩ : syracuseStep 319343 = 479015) B479015
theorem B483227 : Blo 211809 483227 := bstep (se 1 (by rfl) ⟨362420, by rfl⟩ : syracuseStep 483227 = 724841) B724841
theorem B28336139 : Blo 211809 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B2056259 : Blo 211809 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B745757 : Blo 211809 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B483641 : Blo 211809 483641 := bstep (se 2 (by rfl) ⟨181365, by rfl⟩ : syracuseStep 483641 = 362731) B362731
theorem B320027 : Blo 211809 320027 := bstep (se 1 (by rfl) ⟨240020, by rfl⟩ : syracuseStep 320027 = 480041) B480041
theorem B320207 : Blo 211809 320207 := bstep (se 1 (by rfl) ⟨240155, by rfl⟩ : syracuseStep 320207 = 480311) B480311
theorem B811727 : Blo 211809 811727 := bstep (se 1 (by rfl) ⟨608795, by rfl⟩ : syracuseStep 811727 = 1217591) B1217591
theorem B254683 : Blo 211809 254683 := bstep (se 1 (by rfl) ⟨191012, by rfl⟩ : syracuseStep 254683 = 382025) B382025
theorem B320219 : Blo 211809 320219 := bstep (se 1 (by rfl) ⟨240164, by rfl⟩ : syracuseStep 320219 = 480329) B480329
theorem B484127 : Blo 211809 484127 := bstep (se 1 (by rfl) ⟨363095, by rfl⟩ : syracuseStep 484127 = 726191) B726191
theorem B910237 : Blo 211809 910237 := bstep (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) B341339
theorem B320633 : Blo 211809 320633 := bstep (se 2 (by rfl) ⟨120237, by rfl⟩ : syracuseStep 320633 = 240475) B240475
theorem B484937 : Blo 211809 484937 := bstep (se 2 (by rfl) ⟨181851, by rfl⟩ : syracuseStep 484937 = 363703) B363703
theorem B2975491 : Blo 211809 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B3532679 : Blo 211809 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B321503 : Blo 211809 321503 := bstep (se 1 (by rfl) ⟨241127, by rfl⟩ : syracuseStep 321503 = 482255) B482255
theorem B321515 : Blo 211809 321515 := bstep (se 1 (by rfl) ⟨241136, by rfl⟩ : syracuseStep 321515 = 482273) B482273
theorem B1075193 : Blo 211809 1075193 := bstep (se 2 (by rfl) ⟨403197, by rfl⟩ : syracuseStep 1075193 = 806395) B806395
theorem B485369 : Blo 211809 485369 := bstep (se 2 (by rfl) ⟨182013, by rfl⟩ : syracuseStep 485369 = 364027) B364027
theorem B321563 : Blo 211809 321563 := bstep (se 1 (by rfl) ⟨241172, by rfl⟩ : syracuseStep 321563 = 482345) B482345
theorem B485423 : Blo 211809 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B485459 : Blo 211809 485459 := bstep (se 1 (by rfl) ⟨364094, by rfl⟩ : syracuseStep 485459 = 728189) B728189
theorem B813199 : Blo 211809 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B911569 : Blo 211809 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B321929 : Blo 211809 321929 := bstep (se 2 (by rfl) ⟨120723, by rfl⟩ : syracuseStep 321929 = 241447) B241447
theorem B715283 : Blo 211809 715283 := bstep (se 1 (by rfl) ⟨536462, by rfl⟩ : syracuseStep 715283 = 1072925) B1072925
theorem B322871 : Blo 211809 322871 := bstep (se 1 (by rfl) ⟨242153, by rfl⟩ : syracuseStep 322871 = 484307) B484307
theorem B2059607 : Blo 211809 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B716255 : Blo 211809 716255 := bstep (se 1 (by rfl) ⟨537191, by rfl⟩ : syracuseStep 716255 = 1074383) B1074383
theorem B323039 : Blo 211809 323039 := bstep (se 1 (by rfl) ⟨242279, by rfl⟩ : syracuseStep 323039 = 484559) B484559
theorem B323255 : Blo 211809 323255 := bstep (se 1 (by rfl) ⟨242441, by rfl⟩ : syracuseStep 323255 = 484883) B484883
theorem B552673 : Blo 211809 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B323465 : Blo 211809 323465 := bstep (se 2 (by rfl) ⟨121299, by rfl⟩ : syracuseStep 323465 = 242599) B242599
theorem B323711 : Blo 211809 323711 := bstep (se 1 (by rfl) ⟨242783, by rfl⟩ : syracuseStep 323711 = 485567) B485567
theorem B454889 : Blo 211809 454889 := bstep (se 2 (by rfl) ⟨170583, by rfl⟩ : syracuseStep 454889 = 341167) B341167
theorem B1864225 : Blo 211809 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B488171 : Blo 211809 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B815933 : Blo 211809 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B291881 : Blo 211809 291881 := bstep (se 2 (by rfl) ⟨109455, by rfl⟩ : syracuseStep 291881 = 218911) B218911
theorem B685523 : Blo 211809 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B357979 : Blo 211809 357979 := bstep (se 1 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 357979 = 536969) B536969
theorem B358121 : Blo 211809 358121 := bstep (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) B268591
theorem B817361 : Blo 211809 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B784937 : Blo 211809 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B490025 : Blo 211809 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B2652763 : Blo 211809 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B2718305 : Blo 211809 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B359147 : Blo 211809 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B1047775 : Blo 211809 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B1211759 : Blo 211809 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B3079775 : Blo 211809 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B2424653 : Blo 211809 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B2752703 : Blo 211809 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B327935 : Blo 211809 327935 := bstep (se 1 (by rfl) ⟨245951, by rfl⟩ : syracuseStep 327935 = 491903) B491903
theorem B459065 : Blo 211809 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B917993 : Blo 211809 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B361543 : Blo 211809 361543 := bstep (se 1 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 361543 = 542315) B542315
theorem B1213649 : Blo 211809 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B1082807 : Blo 211809 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B361975 : Blo 211809 361975 := bstep (se 1 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 361975 = 542963) B542963
theorem B3967321 : Blo 211809 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B363055 : Blo 211809 363055 := bstep (se 1 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 363055 = 544583) B544583
theorem B1149727 : Blo 211809 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B1084265 : Blo 211809 1084265 := bstep (se 2 (by rfl) ⟨406599, by rfl⟩ : syracuseStep 1084265 = 813199) B813199
theorem B1215425 : Blo 211809 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B724193 : Blo 211809 724193 := bstep (se 2 (by rfl) ⟨271572, by rfl⟩ : syracuseStep 724193 = 543145) B543145
theorem B10554995 : Blo 211809 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B1020059 : Blo 211809 1020059 := bstep (se 1 (by rfl) ⟨765044, by rfl⟩ : syracuseStep 1020059 = 1530089) B1530089
theorem B5509549 : Blo 211809 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B497171 : Blo 211809 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B726623 : Blo 211809 726623 := bstep (se 1 (by rfl) ⟨544967, by rfl⟩ : syracuseStep 726623 = 1089935) B1089935
theorem B662057 : Blo 211809 662057 := bstep (se 2 (by rfl) ⟨248271, by rfl⟩ : syracuseStep 662057 = 496543) B496543
theorem B1514137 : Blo 211809 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B11770589 : Blo 211809 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B728027 : Blo 211809 728027 := bstep (se 1 (by rfl) ⟨546020, by rfl⟩ : syracuseStep 728027 = 1092041) B1092041
theorem B303259 : Blo 211809 303259 := bstep (se 1 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 303259 = 454889) B454889
theorem B9904841 : Blo 211809 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B861257 : Blo 211809 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B238747 : Blo 211809 238747 := bstep (se 1 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 238747 = 358121) B358121
theorem B1091069 : Blo 211809 1091069 := bstep (se 3 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 1091069 = 409151) B409151
theorem B1812203 : Blo 211809 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B239431 : Blo 211809 239431 := bstep (se 1 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 239431 = 359147) B359147
theorem B1386953 : Blo 211809 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B1616435 : Blo 211809 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B240583 : Blo 211809 240583 := bstep (se 1 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 240583 = 360875) B360875
theorem B306283 : Blo 211809 306283 := bstep (se 1 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 306283 = 459425) B459425
theorem B240943 : Blo 211809 240943 := bstep (se 1 (by rfl) ⟨180707, by rfl⟩ : syracuseStep 240943 = 361415) B361415
theorem B1093151 : Blo 211809 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B5222033 : Blo 211809 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B1748645 : Blo 211809 1748645 := bstep (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) B327871
theorem B241519 : Blo 211809 241519 := bstep (se 1 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 241519 = 362279) B362279
theorem B2633593 : Blo 211809 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B242203 : Blo 211809 242203 := bstep (se 1 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 242203 = 363305) B363305
theorem B242383 : Blo 211809 242383 := bstep (se 1 (by rfl) ⟨181787, by rfl⟩ : syracuseStep 242383 = 363575) B363575
theorem B1749995 : Blo 211809 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B1094671 : Blo 211809 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B538103 : Blo 211809 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B1717843 : Blo 211809 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1161017 : Blo 211809 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B1292449 : Blo 211809 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B1358309 : Blo 211809 1358309 := bstep (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) B254683
theorem B768503 : Blo 211809 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B539531 : Blo 211809 539531 := bstep (se 1 (by rfl) ⟨404648, by rfl⟩ : syracuseStep 539531 = 809297) B809297
theorem B1391519 : Blo 211809 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B211903 : Blo 211809 211903 := bstep (se 1 (by rfl) ⟨158927, by rfl⟩ : syracuseStep 211903 = 317855) B317855
theorem B211951 : Blo 211809 211951 := bstep (se 1 (by rfl) ⟨158963, by rfl⟩ : syracuseStep 211951 = 317927) B317927
theorem B3783827 : Blo 211809 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B539855 : Blo 211809 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B212447 : Blo 211809 212447 := bstep (se 1 (by rfl) ⟨159335, by rfl⟩ : syracuseStep 212447 = 318671) B318671
theorem B540179 : Blo 211809 540179 := bstep (se 1 (by rfl) ⟨405134, by rfl⟩ : syracuseStep 540179 = 810269) B810269
theorem B212527 : Blo 211809 212527 := bstep (se 1 (by rfl) ⟨159395, by rfl⟩ : syracuseStep 212527 = 318791) B318791
theorem B736897 : Blo 211809 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B212635 : Blo 211809 212635 := bstep (se 1 (by rfl) ⟨159476, by rfl⟩ : syracuseStep 212635 = 318953) B318953
theorem B1031899 : Blo 211809 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B540391 : Blo 211809 540391 := bstep (se 1 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 540391 = 810587) B810587
theorem B212731 : Blo 211809 212731 := bstep (se 1 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 212731 = 319097) B319097
theorem B212895 : Blo 211809 212895 := bstep (se 1 (by rfl) ⟨159671, by rfl⟩ : syracuseStep 212895 = 319343) B319343
theorem B1228733 : Blo 211809 1228733 := bstep (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) B460775
theorem B18890759 : Blo 211809 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B213351 : Blo 211809 213351 := bstep (se 1 (by rfl) ⟨160013, by rfl⟩ : syracuseStep 213351 = 320027) B320027
theorem B213471 : Blo 211809 213471 := bstep (se 1 (by rfl) ⟨160103, by rfl⟩ : syracuseStep 213471 = 320207) B320207
theorem B541151 : Blo 211809 541151 := bstep (se 1 (by rfl) ⟨405863, by rfl⟩ : syracuseStep 541151 = 811727) B811727
theorem B213479 : Blo 211809 213479 := bstep (se 1 (by rfl) ⟨160109, by rfl⟩ : syracuseStep 213479 = 320219) B320219
theorem B213755 : Blo 211809 213755 := bstep (se 1 (by rfl) ⟨160316, by rfl⟩ : syracuseStep 213755 = 320633) B320633
theorem B214335 : Blo 211809 214335 := bstep (se 1 (by rfl) ⟨160751, by rfl⟩ : syracuseStep 214335 = 321503) B321503
theorem B214343 : Blo 211809 214343 := bstep (se 1 (by rfl) ⟨160757, by rfl⟩ : syracuseStep 214343 = 321515) B321515
theorem B214375 : Blo 211809 214375 := bstep (se 1 (by rfl) ⟨160781, by rfl⟩ : syracuseStep 214375 = 321563) B321563
theorem B214619 : Blo 211809 214619 := bstep (se 1 (by rfl) ⟨160964, by rfl⟩ : syracuseStep 214619 = 321929) B321929
theorem B476855 : Blo 211809 476855 := bstep (se 1 (by rfl) ⟨357641, by rfl⟩ : syracuseStep 476855 = 715283) B715283
theorem B477305 : Blo 211809 477305 := bstep (se 2 (by rfl) ⟨178989, by rfl⟩ : syracuseStep 477305 = 357979) B357979
theorem B215247 : Blo 211809 215247 := bstep (se 1 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 215247 = 322871) B322871
theorem B477503 : Blo 211809 477503 := bstep (se 1 (by rfl) ⟨358127, by rfl⟩ : syracuseStep 477503 = 716255) B716255
theorem B215359 : Blo 211809 215359 := bstep (se 1 (by rfl) ⟨161519, by rfl⟩ : syracuseStep 215359 = 323039) B323039
theorem B215503 : Blo 211809 215503 := bstep (se 1 (by rfl) ⟨161627, by rfl⟩ : syracuseStep 215503 = 323255) B323255
theorem B215643 : Blo 211809 215643 := bstep (se 1 (by rfl) ⟨161732, by rfl⟩ : syracuseStep 215643 = 323465) B323465
theorem B1854089 : Blo 211809 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B215807 : Blo 211809 215807 := bstep (se 1 (by rfl) ⟨161855, by rfl⟩ : syracuseStep 215807 = 323711) B323711
theorem B1362743 : Blo 211809 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1100627 : Blo 211809 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B511105 : Blo 211809 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B543955 : Blo 211809 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B544907 : Blo 211809 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B1397033 : Blo 211809 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B3920561 : Blo 211809 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B807839 : Blo 211809 807839 := bstep (se 1 (by rfl) ⟨605879, by rfl⟩ : syracuseStep 807839 = 1211759) B1211759
theorem B2053183 : Blo 211809 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B546223 : Blo 211809 546223 := bstep (se 1 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 546223 = 819335) B819335
theorem B3462671 : Blo 211809 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B480959 : Blo 211809 480959 := bstep (se 1 (by rfl) ⟨360719, by rfl⟩ : syracuseStep 480959 = 721439) B721439
theorem B1365767 : Blo 211809 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B1726667 : Blo 211809 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B317723 : Blo 211809 317723 := bstep (se 1 (by rfl) ⟨238292, by rfl⟩ : syracuseStep 317723 = 476585) B476585
theorem B612839 : Blo 211809 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B318047 : Blo 211809 318047 := bstep (se 1 (by rfl) ⟨238535, by rfl⟩ : syracuseStep 318047 = 477071) B477071
theorem B318143 : Blo 211809 318143 := bstep (se 1 (by rfl) ⟨238607, by rfl⟩ : syracuseStep 318143 = 477215) B477215
theorem B318185 : Blo 211809 318185 := bstep (se 2 (by rfl) ⟨119319, by rfl⟩ : syracuseStep 318185 = 238639) B238639
theorem B383791 : Blo 211809 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B482111 : Blo 211809 482111 := bstep (se 1 (by rfl) ⟨361583, by rfl⟩ : syracuseStep 482111 = 723167) B723167
theorem B318311 : Blo 211809 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B4086683 : Blo 211809 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B318377 : Blo 211809 318377 := bstep (se 2 (by rfl) ⟨119391, by rfl⟩ : syracuseStep 318377 = 238783) B238783
theorem B318527 : Blo 211809 318527 := bstep (se 1 (by rfl) ⟨238895, by rfl⟩ : syracuseStep 318527 = 477791) B477791
theorem B318569 : Blo 211809 318569 := bstep (se 2 (by rfl) ⟨119463, by rfl⟩ : syracuseStep 318569 = 238927) B238927
theorem B384107 : Blo 211809 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B318695 : Blo 211809 318695 := bstep (se 1 (by rfl) ⟨239021, by rfl⟩ : syracuseStep 318695 = 478043) B478043
theorem B1301789 : Blo 211809 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B482687 : Blo 211809 482687 := bstep (se 1 (by rfl) ⟨362015, by rfl⟩ : syracuseStep 482687 = 724031) B724031
theorem B45505925 : Blo 211809 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B319199 : Blo 211809 319199 := bstep (se 1 (by rfl) ⟨239399, by rfl⟩ : syracuseStep 319199 = 478799) B478799
theorem B319529 : Blo 211809 319529 := bstep (se 2 (by rfl) ⟨119823, by rfl⟩ : syracuseStep 319529 = 239647) B239647
theorem B319559 : Blo 211809 319559 := bstep (se 1 (by rfl) ⟨239669, by rfl⟩ : syracuseStep 319559 = 479339) B479339
theorem B319595 : Blo 211809 319595 := bstep (se 1 (by rfl) ⟨239696, by rfl⟩ : syracuseStep 319595 = 479393) B479393
theorem B778349 : Blo 211809 778349 := bstep (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) B291881
theorem B2318483 : Blo 211809 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B319679 : Blo 211809 319679 := bstep (se 1 (by rfl) ⟨239759, by rfl⟩ : syracuseStep 319679 = 479519) B479519
theorem B385319 : Blo 211809 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B319865 : Blo 211809 319865 := bstep (se 2 (by rfl) ⟨119949, by rfl⟩ : syracuseStep 319865 = 239899) B239899
theorem B320159 : Blo 211809 320159 := bstep (se 1 (by rfl) ⟨240119, by rfl⟩ : syracuseStep 320159 = 480239) B480239
theorem B5563181 : Blo 211809 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B320495 : Blo 211809 320495 := bstep (se 1 (by rfl) ⟨240371, by rfl⟩ : syracuseStep 320495 = 480743) B480743
theorem B812015 : Blo 211809 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B320603 : Blo 211809 320603 := bstep (se 1 (by rfl) ⟨240452, by rfl⟩ : syracuseStep 320603 = 480905) B480905
theorem B320615 : Blo 211809 320615 := bstep (se 1 (by rfl) ⟨240461, by rfl⟩ : syracuseStep 320615 = 480923) B480923
theorem B1369199 : Blo 211809 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B484577 : Blo 211809 484577 := bstep (se 2 (by rfl) ⟨181716, by rfl⟩ : syracuseStep 484577 = 363433) B363433
theorem B320747 : Blo 211809 320747 := bstep (se 1 (by rfl) ⟨240560, by rfl⟩ : syracuseStep 320747 = 481121) B481121
theorem B320879 : Blo 211809 320879 := bstep (se 1 (by rfl) ⟨240659, by rfl⟩ : syracuseStep 320879 = 481319) B481319
theorem B320999 : Blo 211809 320999 := bstep (se 1 (by rfl) ⟨240749, by rfl⟩ : syracuseStep 320999 = 481499) B481499
theorem B1074707 : Blo 211809 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B4351583 : Blo 211809 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B321131 : Blo 211809 321131 := bstep (se 1 (by rfl) ⟨240848, by rfl⟩ : syracuseStep 321131 = 481697) B481697
theorem B321179 : Blo 211809 321179 := bstep (se 1 (by rfl) ⟨240884, by rfl⟩ : syracuseStep 321179 = 481769) B481769
theorem B321401 : Blo 211809 321401 := bstep (se 2 (by rfl) ⟨120525, by rfl⟩ : syracuseStep 321401 = 241051) B241051
theorem B485243 : Blo 211809 485243 := bstep (se 1 (by rfl) ⟨363932, by rfl⟩ : syracuseStep 485243 = 727865) B727865
theorem B583583 : Blo 211809 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B485513 : Blo 211809 485513 := bstep (se 2 (by rfl) ⟨182067, by rfl⟩ : syracuseStep 485513 = 364135) B364135
theorem B322151 : Blo 211809 322151 := bstep (se 1 (by rfl) ⟨241613, by rfl⟩ : syracuseStep 322151 = 483227) B483227
theorem B1370839 : Blo 211809 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B322427 : Blo 211809 322427 := bstep (se 1 (by rfl) ⟨241820, by rfl⟩ : syracuseStep 322427 = 483641) B483641
theorem B683063 : Blo 211809 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B322697 : Blo 211809 322697 := bstep (se 2 (by rfl) ⟨121011, by rfl⟩ : syracuseStep 322697 = 242023) B242023
theorem B322751 : Blo 211809 322751 := bstep (se 1 (by rfl) ⟨242063, by rfl⟩ : syracuseStep 322751 = 484127) B484127
theorem B2485633 : Blo 211809 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B323291 : Blo 211809 323291 := bstep (se 1 (by rfl) ⟨242468, by rfl⟩ : syracuseStep 323291 = 484937) B484937
theorem B2355119 : Blo 211809 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B323561 : Blo 211809 323561 := bstep (se 2 (by rfl) ⟨121335, by rfl⟩ : syracuseStep 323561 = 242671) B242671
theorem B716795 : Blo 211809 716795 := bstep (se 1 (by rfl) ⟨537596, by rfl⟩ : syracuseStep 716795 = 1075193) B1075193
theorem B323579 : Blo 211809 323579 := bstep (se 1 (by rfl) ⟨242684, by rfl⟩ : syracuseStep 323579 = 485369) B485369
theorem B323615 : Blo 211809 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B815143 : Blo 211809 815143 := bstep (se 1 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 815143 = 1222715) B1222715
theorem B323639 : Blo 211809 323639 := bstep (se 1 (by rfl) ⟨242729, by rfl⟩ : syracuseStep 323639 = 485459) B485459
theorem B2093165 : Blo 211809 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B2584943 : Blo 211809 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B4977541 : Blo 211809 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B1373071 : Blo 211809 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B1209275 : Blo 211809 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B226351 : Blo 211809 226351 := bstep (se 1 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 226351 = 339527) B339527
theorem B6255755 : Blo 211809 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B357871 : Blo 211809 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B1636361 : Blo 211809 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B3537017 : Blo 211809 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B457015 : Blo 211809 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B1603997 : Blo 211809 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B2325023 : Blo 211809 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B1079891 : Blo 211809 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B981613 : Blo 211809 981613 := bstep (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) B368105
theorem B1866503 : Blo 211809 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B686855 : Blo 211809 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B326683 : Blo 211809 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B687163 : Blo 211809 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B359579 : Blo 211809 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B687599 : Blo 211809 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B1835135 : Blo 211809 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B360767 : Blo 211809 360767 := bstep (se 1 (by rfl) ⟨270575, by rfl⟩ : syracuseStep 360767 = 541151) B541151
theorem B721871 : Blo 211809 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B4097141 : Blo 211809 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B722843 : Blo 211809 722843 := bstep (se 1 (by rfl) ⟨542132, by rfl⟩ : syracuseStep 722843 = 1084265) B1084265
theorem B363271 : Blo 211809 363271 := bstep (se 1 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 363271 = 544907) B544907
theorem B331447 : Blo 211809 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B1151111 : Blo 211809 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B725273 : Blo 211809 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B3314177 : Blo 211809 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2724455 : Blo 211809 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B26546885 : Blo 211809 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B3511457 : Blo 211809 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B1086857 : Blo 211809 1086857 := bstep (se 2 (by rfl) ⟨407571, by rfl⟩ : syracuseStep 1086857 = 815143) B815143
theorem B1545655 : Blo 211809 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1742309 : Blo 211809 1742309 := bstep (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) B326683
theorem B3708787 : Blo 211809 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B7346065 : Blo 211809 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B727379 : Blo 211809 727379 := bstep (se 1 (by rfl) ⟨545534, by rfl⟩ : syracuseStep 727379 = 1091069) B1091069
theorem B301801 : Blo 211809 301801 := bstep (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) B226351
theorem B924635 : Blo 211809 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B728297 : Blo 211809 728297 := bstep (se 2 (by rfl) ⟨273111, by rfl⟩ : syracuseStep 728297 = 546223) B546223
theorem B728767 : Blo 211809 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B3481355 : Blo 211809 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B4170503 : Blo 211809 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1090907 : Blo 211809 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B1550015 : Blo 211809 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B927679 : Blo 211809 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B239719 : Blo 211809 239719 := bstep (se 1 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 239719 = 359579) B359579
theorem B12593839 : Blo 211809 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B404345 : Blo 211809 404345 := bstep (se 2 (by rfl) ⟨151629, by rfl⟩ : syracuseStep 404345 = 303259) B303259
theorem B2075597 : Blo 211809 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B1224173 : Blo 211809 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B733751 : Blo 211809 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B931355 : Blo 211809 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B5289761 : Blo 211809 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B538559 : Blo 211809 538559 := bstep (se 1 (by rfl) ⟨403919, by rfl⟩ : syracuseStep 538559 = 807839) B807839
theorem B2308447 : Blo 211809 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B408377 : Blo 211809 408377 := bstep (se 2 (by rfl) ⟨153141, by rfl⟩ : syracuseStep 408377 = 306283) B306283
theorem B211815 : Blo 211809 211815 := bstep (se 1 (by rfl) ⟨158861, by rfl⟩ : syracuseStep 211815 = 317723) B317723
theorem B408559 : Blo 211809 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B441371 : Blo 211809 441371 := bstep (se 1 (by rfl) ⟨331028, by rfl⟩ : syracuseStep 441371 = 662057) B662057
theorem B212031 : Blo 211809 212031 := bstep (se 1 (by rfl) ⟨159023, by rfl⟩ : syracuseStep 212031 = 318047) B318047
theorem B212095 : Blo 211809 212095 := bstep (se 1 (by rfl) ⟨159071, by rfl⟩ : syracuseStep 212095 = 318143) B318143
theorem B7847059 : Blo 211809 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B212123 : Blo 211809 212123 := bstep (se 1 (by rfl) ⟨159092, by rfl⟩ : syracuseStep 212123 = 318185) B318185
theorem B212207 : Blo 211809 212207 := bstep (se 1 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 212207 = 318311) B318311
theorem B212251 : Blo 211809 212251 := bstep (se 1 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 212251 = 318377) B318377
theorem B212351 : Blo 211809 212351 := bstep (se 1 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 212351 = 318527) B318527
theorem B212379 : Blo 211809 212379 := bstep (se 1 (by rfl) ⟨159284, by rfl⟩ : syracuseStep 212379 = 318569) B318569
theorem B212463 : Blo 211809 212463 := bstep (se 1 (by rfl) ⟨159347, by rfl⟩ : syracuseStep 212463 = 318695) B318695
theorem B1556221 : Blo 211809 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B212799 : Blo 211809 212799 := bstep (se 1 (by rfl) ⟨159599, by rfl⟩ : syracuseStep 212799 = 319199) B319199
theorem B213019 : Blo 211809 213019 := bstep (se 1 (by rfl) ⟨159764, by rfl⟩ : syracuseStep 213019 = 319529) B319529
theorem B213039 : Blo 211809 213039 := bstep (se 1 (by rfl) ⟨159779, by rfl⟩ : syracuseStep 213039 = 319559) B319559
theorem B213063 : Blo 211809 213063 := bstep (se 1 (by rfl) ⟨159797, by rfl⟩ : syracuseStep 213063 = 319595) B319595
theorem B213119 : Blo 211809 213119 := bstep (se 1 (by rfl) ⟨159839, by rfl⟩ : syracuseStep 213119 = 319679) B319679
theorem B213243 : Blo 211809 213243 := bstep (se 1 (by rfl) ⟨159932, by rfl⟩ : syracuseStep 213243 = 319865) B319865
theorem B213439 : Blo 211809 213439 := bstep (se 1 (by rfl) ⟨160079, by rfl⟩ : syracuseStep 213439 = 320159) B320159
theorem B6603227 : Blo 211809 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B213663 : Blo 211809 213663 := bstep (se 1 (by rfl) ⟨160247, by rfl⟩ : syracuseStep 213663 = 320495) B320495
theorem B541343 : Blo 211809 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B574171 : Blo 211809 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B213735 : Blo 211809 213735 := bstep (se 1 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 213735 = 320603) B320603
theorem B213743 : Blo 211809 213743 := bstep (se 1 (by rfl) ⟨160307, by rfl⟩ : syracuseStep 213743 = 320615) B320615
theorem B213831 : Blo 211809 213831 := bstep (se 1 (by rfl) ⟨160373, by rfl⟩ : syracuseStep 213831 = 320747) B320747
theorem B213919 : Blo 211809 213919 := bstep (se 1 (by rfl) ⟨160439, by rfl⟩ : syracuseStep 213919 = 320879) B320879
theorem B213999 : Blo 211809 213999 := bstep (se 1 (by rfl) ⟨160499, by rfl⟩ : syracuseStep 213999 = 320999) B320999
theorem B2901055 : Blo 211809 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B214087 : Blo 211809 214087 := bstep (se 1 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 214087 = 321131) B321131
theorem B214119 : Blo 211809 214119 := bstep (se 1 (by rfl) ⟨160589, by rfl⟩ : syracuseStep 214119 = 321179) B321179
theorem B214267 : Blo 211809 214267 := bstep (se 1 (by rfl) ⟨160700, by rfl⟩ : syracuseStep 214267 = 321401) B321401
theorem B1459561 : Blo 211809 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B2737577 : Blo 211809 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B214767 : Blo 211809 214767 := bstep (se 1 (by rfl) ⟨161075, by rfl⟩ : syracuseStep 214767 = 322151) B322151
theorem B214951 : Blo 211809 214951 := bstep (se 1 (by rfl) ⟨161213, by rfl⟩ : syracuseStep 214951 = 322427) B322427
theorem B477161 : Blo 211809 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B215131 : Blo 211809 215131 := bstep (se 1 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 215131 = 322697) B322697
theorem B215167 : Blo 211809 215167 := bstep (se 1 (by rfl) ⟨161375, by rfl⟩ : syracuseStep 215167 = 322751) B322751
theorem B1165763 : Blo 211809 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B215527 : Blo 211809 215527 := bstep (se 1 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 215527 = 323291) B323291
theorem B215707 : Blo 211809 215707 := bstep (se 1 (by rfl) ⟨161780, by rfl⟩ : syracuseStep 215707 = 323561) B323561
theorem B477863 : Blo 211809 477863 := bstep (se 1 (by rfl) ⟨358397, by rfl⟩ : syracuseStep 477863 = 716795) B716795
theorem B215719 : Blo 211809 215719 := bstep (se 1 (by rfl) ⟨161789, by rfl⟩ : syracuseStep 215719 = 323579) B323579
theorem B215743 : Blo 211809 215743 := bstep (se 1 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 215743 = 323615) B323615
theorem B215759 : Blo 211809 215759 := bstep (se 1 (by rfl) ⟨161819, by rfl⟩ : syracuseStep 215759 = 323639) B323639
theorem B1395443 : Blo 211809 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1723265 : Blo 211809 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1723295 : Blo 211809 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B609353 : Blo 211809 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B806183 : Blo 211809 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B1166663 : Blo 211809 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B2018849 : Blo 211809 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B511721 : Blo 211809 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B774011 : Blo 211809 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B1069331 : Blo 211809 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B905539 : Blo 211809 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B512335 : Blo 211809 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B218623 : Blo 211809 218623 := bstep (se 1 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 218623 = 327935) B327935
theorem B809099 : Blo 211809 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B317903 : Blo 211809 317903 := bstep (se 1 (by rfl) ⟨238427, by rfl⟩ : syracuseStep 317903 = 476855) B476855
theorem B2447981 : Blo 211809 2447981 := bstep (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) B917993
theorem B318203 : Blo 211809 318203 := bstep (se 1 (by rfl) ⟨238652, by rfl⟩ : syracuseStep 318203 = 477305) B477305
theorem B482057 : Blo 211809 482057 := bstep (se 2 (by rfl) ⟨180771, by rfl⟩ : syracuseStep 482057 = 361543) B361543
theorem B318329 : Blo 211809 318329 := bstep (se 2 (by rfl) ⟨119373, by rfl⟩ : syracuseStep 318329 = 238747) B238747
theorem B318335 : Blo 211809 318335 := bstep (se 1 (by rfl) ⟨238751, by rfl⟩ : syracuseStep 318335 = 477503) B477503
theorem B1236059 : Blo 211809 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B908495 : Blo 211809 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B810283 : Blo 211809 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B482633 : Blo 211809 482633 := bstep (se 2 (by rfl) ⟨180987, by rfl⟩ : syracuseStep 482633 = 361975) B361975
theorem B482795 : Blo 211809 482795 := bstep (se 1 (by rfl) ⟨362096, by rfl⟩ : syracuseStep 482795 = 724193) B724193
theorem B319241 : Blo 211809 319241 := bstep (se 2 (by rfl) ⟨119715, by rfl⟩ : syracuseStep 319241 = 239431) B239431
theorem B680039 : Blo 211809 680039 := bstep (se 1 (by rfl) ⟨510029, by rfl⟩ : syracuseStep 680039 = 1020059) B1020059
theorem B2613707 : Blo 211809 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B484073 : Blo 211809 484073 := bstep (se 2 (by rfl) ⟨181527, by rfl⟩ : syracuseStep 484073 = 363055) B363055
theorem B1827785 : Blo 211809 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B1532969 : Blo 211809 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B484415 : Blo 211809 484415 := bstep (se 1 (by rfl) ⟨363311, by rfl⟩ : syracuseStep 484415 = 726623) B726623
theorem B320639 : Blo 211809 320639 := bstep (se 1 (by rfl) ⟨240479, by rfl⟩ : syracuseStep 320639 = 480959) B480959
theorem B910511 : Blo 211809 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B320777 : Blo 211809 320777 := bstep (se 2 (by rfl) ⟨120291, by rfl⟩ : syracuseStep 320777 = 240583) B240583
theorem B681473 : Blo 211809 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B321257 : Blo 211809 321257 := bstep (se 2 (by rfl) ⟨120471, by rfl⟩ : syracuseStep 321257 = 240943) B240943
theorem B321407 : Blo 211809 321407 := bstep (se 1 (by rfl) ⟨241055, by rfl⟩ : syracuseStep 321407 = 482111) B482111
theorem B485351 : Blo 211809 485351 := bstep (se 1 (by rfl) ⟨364013, by rfl⟩ : syracuseStep 485351 = 728027) B728027
theorem B321791 : Blo 211809 321791 := bstep (se 1 (by rfl) ⟨241343, by rfl⟩ : syracuseStep 321791 = 482687) B482687
theorem B30337283 : Blo 211809 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B322025 : Blo 211809 322025 := bstep (se 2 (by rfl) ⟨120759, by rfl⟩ : syracuseStep 322025 = 241519) B241519
theorem B256879 : Blo 211809 256879 := bstep (se 1 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 256879 = 385319) B385319
theorem B322937 : Blo 211809 322937 := bstep (se 2 (by rfl) ⟨121101, by rfl⟩ : syracuseStep 322937 = 242203) B242203
theorem B912799 : Blo 211809 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B323051 : Blo 211809 323051 := bstep (se 1 (by rfl) ⟨242288, by rfl⟩ : syracuseStep 323051 = 484577) B484577
theorem B323177 : Blo 211809 323177 := bstep (se 2 (by rfl) ⟨121191, by rfl⟩ : syracuseStep 323177 = 242383) B242383
theorem B716471 : Blo 211809 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B1208135 : Blo 211809 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B1830761 : Blo 211809 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B323495 : Blo 211809 323495 := bstep (se 1 (by rfl) ⟨242621, by rfl⟩ : syracuseStep 323495 = 485243) B485243
theorem B323675 : Blo 211809 323675 := bstep (se 1 (by rfl) ⟨242756, by rfl⟩ : syracuseStep 323675 = 485513) B485513
theorem B1077623 : Blo 211809 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B455375 : Blo 211809 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B2290457 : Blo 211809 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B1570079 : Blo 211809 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B3471437 : Blo 211809 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B1308817 : Blo 211809 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B358735 : Blo 211809 358735 := bstep (se 1 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 358735 = 538103) B538103
theorem B916217 : Blo 211809 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B2358011 : Blo 211809 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B28146653 : Blo 211809 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B719927 : Blo 211809 719927 := bstep (se 1 (by rfl) ⟨539945, by rfl⟩ : syracuseStep 719927 = 1079891) B1079891
theorem B1244335 : Blo 211809 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B457903 : Blo 211809 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B359687 : Blo 211809 359687 := bstep (se 1 (by rfl) ⟨269765, by rfl⟩ : syracuseStep 359687 = 539531) B539531
theorem B2522551 : Blo 211809 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B359903 : Blo 211809 359903 := bstep (se 1 (by rfl) ⟨269927, by rfl⟩ : syracuseStep 359903 = 539855) B539855
theorem B982529 : Blo 211809 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B1375865 : Blo 211809 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B720521 : Blo 211809 720521 := bstep (se 2 (by rfl) ⟨270195, by rfl⟩ : syracuseStep 720521 = 540391) B540391
theorem B458399 : Blo 211809 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B360119 : Blo 211809 360119 := bstep (se 1 (by rfl) ⟨270089, by rfl⟩ : syracuseStep 360119 = 540179) B540179
theorem B819155 : Blo 211809 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B360895 : Blo 211809 360895 := bstep (se 1 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 360895 = 541343) B541343
theorem B2851549 : Blo 211809 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B6980357 : Blo 211809 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B3868073 : Blo 211809 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B1148843 : Blo 211809 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1148863 : Blo 211809 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B17697923 : Blo 211809 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B724571 : Blo 211809 724571 := bstep (se 1 (by rfl) ⟨543428, by rfl⟩ : syracuseStep 724571 = 1086857) B1086857
theorem B1217065 : Blo 211809 1217065 := bstep (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) B912799
theorem B824039 : Blo 211809 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B1742471 : Blo 211809 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B1218523 : Blo 211809 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B1021979 : Blo 211809 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B727271 : Blo 211809 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B20224855 : Blo 211809 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B269563 : Blo 211809 269563 := bstep (se 1 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 269563 = 404345) B404345
theorem B1383731 : Blo 211809 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B1220507 : Blo 211809 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B303583 : Blo 211809 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B402401 : Blo 211809 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B5383597 : Blo 211809 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B10462745 : Blo 211809 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B1222397 : Blo 211809 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B272251 : Blo 211809 272251 := bstep (se 1 (by rfl) ⟨204188, by rfl⟩ : syracuseStep 272251 = 408377) B408377
theorem B239791 : Blo 211809 239791 := bstep (se 1 (by rfl) ⟨179843, by rfl⟩ : syracuseStep 239791 = 359687) B359687
theorem B239935 : Blo 211809 239935 := bstep (se 1 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 239935 = 359903) B359903
theorem B2074961 : Blo 211809 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B240079 : Blo 211809 240079 := bstep (se 1 (by rfl) ⟨180059, by rfl⟩ : syracuseStep 240079 = 360119) B360119
theorem B1223423 : Blo 211809 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B240511 : Blo 211809 240511 := bstep (se 1 (by rfl) ⟨180383, by rfl⟩ : syracuseStep 240511 = 360767) B360767
theorem B4402151 : Blo 211809 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B2731427 : Blo 211809 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2732453 : Blo 211809 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B1946081 : Blo 211809 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B930295 : Blo 211809 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B406235 : Blo 211809 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B537455 : Blo 211809 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B341147 : Blo 211809 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B767407 : Blo 211809 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B2209451 : Blo 211809 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1816303 : Blo 211809 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B2340971 : Blo 211809 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B16791785 : Blo 211809 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1161539 : Blo 211809 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B3062245 : Blo 211809 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B342505 : Blo 211809 342505 := bstep (se 2 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 342505 = 256879) B256879
theorem B1817261 : Blo 211809 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B539399 : Blo 211809 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B211935 : Blo 211809 211935 := bstep (se 1 (by rfl) ⟨158951, by rfl⟩ : syracuseStep 211935 = 317903) B317903
theorem B212135 : Blo 211809 212135 := bstep (se 1 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 212135 = 318203) B318203
theorem B212219 : Blo 211809 212219 := bstep (se 1 (by rfl) ⟨159164, by rfl⟩ : syracuseStep 212219 = 318329) B318329
theorem B212223 : Blo 211809 212223 := bstep (se 1 (by rfl) ⟨159167, by rfl⟩ : syracuseStep 212223 = 318335) B318335
theorem B605663 : Blo 211809 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B441929 : Blo 211809 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B212827 : Blo 211809 212827 := bstep (se 1 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 212827 = 319241) B319241
theorem B213759 : Blo 211809 213759 := bstep (se 1 (by rfl) ⟨160319, by rfl⟩ : syracuseStep 213759 = 320639) B320639
theorem B607007 : Blo 211809 607007 := bstep (se 1 (by rfl) ⟨455255, by rfl⟩ : syracuseStep 607007 = 910511) B910511
theorem B213851 : Blo 211809 213851 := bstep (se 1 (by rfl) ⟨160388, by rfl⟩ : syracuseStep 213851 = 320777) B320777
theorem B2442149 : Blo 211809 2442149 := bstep (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) B457903
theorem B1033343 : Blo 211809 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B214171 : Blo 211809 214171 := bstep (se 1 (by rfl) ⟨160628, by rfl⟩ : syracuseStep 214171 = 321257) B321257
theorem B214271 : Blo 211809 214271 := bstep (se 1 (by rfl) ⟨160703, by rfl⟩ : syracuseStep 214271 = 321407) B321407
theorem B214527 : Blo 211809 214527 := bstep (se 1 (by rfl) ⟨160895, by rfl⟩ : syracuseStep 214527 = 321791) B321791
theorem B214683 : Blo 211809 214683 := bstep (se 1 (by rfl) ⟨161012, by rfl⟩ : syracuseStep 214683 = 322025) B322025
theorem B215291 : Blo 211809 215291 := bstep (se 1 (by rfl) ⟨161468, by rfl⟩ : syracuseStep 215291 = 322937) B322937
theorem B215367 : Blo 211809 215367 := bstep (se 1 (by rfl) ⟨161525, by rfl⟩ : syracuseStep 215367 = 323051) B323051
theorem B215451 : Blo 211809 215451 := bstep (se 1 (by rfl) ⟨161588, by rfl⟩ : syracuseStep 215451 = 323177) B323177
theorem B477647 : Blo 211809 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B805423 : Blo 211809 805423 := bstep (se 1 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 805423 = 1208135) B1208135
theorem B215663 : Blo 211809 215663 := bstep (se 1 (by rfl) ⟨161747, by rfl⟩ : syracuseStep 215663 = 323495) B323495
theorem B215783 : Blo 211809 215783 := bstep (se 1 (by rfl) ⟨161837, by rfl⟩ : syracuseStep 215783 = 323675) B323675
theorem B478313 : Blo 211809 478313 := bstep (se 2 (by rfl) ⟨179367, by rfl⟩ : syracuseStep 478313 = 358735) B358735
theorem B1526971 : Blo 211809 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B3526507 : Blo 211809 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B544745 : Blo 211809 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B2314291 : Blo 211809 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B1659113 : Blo 211809 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B610811 : Blo 211809 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B3363401 : Blo 211809 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B18764435 : Blo 211809 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B479951 : Blo 211809 479951 := bstep (se 1 (by rfl) ⟨359963, by rfl⟩ : syracuseStep 479951 = 719927) B719927
theorem B971689 : Blo 211809 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B480347 : Blo 211809 480347 := bstep (se 1 (by rfl) ⟨360260, by rfl⟩ : syracuseStep 480347 = 720521) B720521
theorem B546103 : Blo 211809 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B481247 : Blo 211809 481247 := bstep (se 1 (by rfl) ⟨360935, by rfl⟩ : syracuseStep 481247 = 721871) B721871
theorem B1825051 : Blo 211809 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B481895 : Blo 211809 481895 := bstep (se 1 (by rfl) ⟨361421, by rfl⟩ : syracuseStep 481895 = 722843) B722843
theorem B318107 : Blo 211809 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B318575 : Blo 211809 318575 := bstep (se 1 (by rfl) ⟨238931, by rfl⟩ : syracuseStep 318575 = 477863) B477863
theorem B777775 : Blo 211809 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B516007 : Blo 211809 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B1236905 : Blo 211809 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B319625 : Blo 211809 319625 := bstep (se 2 (by rfl) ⟨119859, by rfl⟩ : syracuseStep 319625 = 239719) B239719
theorem B483515 : Blo 211809 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B484361 : Blo 211809 484361 := bstep (se 2 (by rfl) ⟨181635, by rfl⟩ : syracuseStep 484361 = 363271) B363271
theorem B484919 : Blo 211809 484919 := bstep (se 1 (by rfl) ⟨363689, by rfl⟩ : syracuseStep 484919 = 727379) B727379
theorem B1631987 : Blo 211809 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B321371 : Blo 211809 321371 := bstep (se 1 (by rfl) ⟨241028, by rfl⟩ : syracuseStep 321371 = 482057) B482057
theorem B616423 : Blo 211809 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B485531 : Blo 211809 485531 := bstep (se 1 (by rfl) ⟨364148, by rfl⟩ : syracuseStep 485531 = 728297) B728297
theorem B321755 : Blo 211809 321755 := bstep (se 1 (by rfl) ⟨241316, by rfl⟩ : syracuseStep 321755 = 482633) B482633
theorem B321863 : Blo 211809 321863 := bstep (se 1 (by rfl) ⟨241397, by rfl⟩ : syracuseStep 321863 = 482795) B482795
theorem B2320903 : Blo 211809 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B453359 : Blo 211809 453359 := bstep (se 1 (by rfl) ⟨340019, by rfl⟩ : syracuseStep 453359 = 680039) B680039
theorem B1207385 : Blo 211809 1207385 := bstep (se 2 (by rfl) ⟨452769, by rfl⟩ : syracuseStep 1207385 = 905539) B905539
theorem B322715 : Blo 211809 322715 := bstep (se 1 (by rfl) ⟨242036, by rfl⟩ : syracuseStep 322715 = 484073) B484073
theorem B2780335 : Blo 211809 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B322943 : Blo 211809 322943 := bstep (se 1 (by rfl) ⟨242207, by rfl⟩ : syracuseStep 322943 = 484415) B484415
theorem B3108701 : Blo 211809 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B323567 : Blo 211809 323567 := bstep (se 1 (by rfl) ⟨242675, by rfl⟩ : syracuseStep 323567 = 485351) B485351
theorem B2060873 : Blo 211809 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B6288029 : Blo 211809 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B291497 : Blo 211809 291497 := bstep (se 2 (by rfl) ⟨109311, by rfl⟩ : syracuseStep 291497 = 218623) B218623
theorem B816115 : Blo 211809 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B4945049 : Blo 211809 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B9794753 : Blo 211809 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B718415 : Blo 211809 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B489167 : Blo 211809 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B3077929 : Blo 211809 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B1046719 : Blo 211809 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B620903 : Blo 211809 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B359039 : Blo 211809 359039 := bstep (se 1 (by rfl) ⟨269279, by rfl⟩ : syracuseStep 359039 = 538559) B538559
theorem B1080377 : Blo 211809 1080377 := bstep (se 2 (by rfl) ⟨405141, by rfl⟩ : syracuseStep 1080377 = 810283) B810283
theorem B294247 : Blo 211809 294247 := bstep (se 1 (by rfl) ⟨220685, by rfl⟩ : syracuseStep 294247 = 441371) B441371
theorem B655019 : Blo 211809 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B917243 : Blo 211809 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B4653571 : Blo 211809 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B688895 : Blo 211809 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B7178129 : Blo 211809 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1083293 : Blo 211809 1083293 := bstep (se 3 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 1083293 = 406235) B406235
theorem B11798615 : Blo 211809 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B363001 : Blo 211809 363001 := bstep (se 2 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 363001 = 272251) B272251
theorem B821897 : Blo 211809 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B363163 : Blo 211809 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B2035961 : Blo 211809 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B922487 : Blo 211809 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B824603 : Blo 211809 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B3085721 : Blo 211809 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B268267 : Blo 211809 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B1087991 : Blo 211809 1087991 := bstep (se 1 (by rfl) ⟨815993, by rfl⟩ : syracuseStep 1087991 = 1631987) B1631987
theorem B1088153 : Blo 211809 1088153 := bstep (se 2 (by rfl) ⟨408057, by rfl⟩ : syracuseStep 1088153 = 816115) B816115
theorem B1383307 : Blo 211809 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B728137 : Blo 211809 728137 := bstep (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) B546103
theorem B302239 : Blo 211809 302239 := bstep (se 1 (by rfl) ⟨226679, by rfl⟩ : syracuseStep 302239 = 453359) B453359
theorem B1023209 : Blo 211809 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B4103905 : Blo 211809 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B2433401 : Blo 211809 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B6529835 : Blo 211809 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B239359 : Blo 211809 239359 := bstep (se 1 (by rfl) ⟨179519, by rfl⟩ : syracuseStep 239359 = 359039) B359039
theorem B403775 : Blo 211809 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B436679 : Blo 211809 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B404671 : Blo 211809 404671 := bstep (se 1 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 404671 = 607007) B607007
theorem B404777 : Blo 211809 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B765895 : Blo 211809 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B4961573 : Blo 211809 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B407207 : Blo 211809 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B3094537 : Blo 211809 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B1161647 : Blo 211809 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B212071 : Blo 211809 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B60833045 : Blo 211809 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B212383 : Blo 211809 212383 := bstep (se 1 (by rfl) ⟨159287, by rfl⟩ : syracuseStep 212383 = 318575) B318575
theorem B4702009 : Blo 211809 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B213083 : Blo 211809 213083 := bstep (se 1 (by rfl) ⟨159812, by rfl⟩ : syracuseStep 213083 = 319625) B319625
theorem B1622753 : Blo 211809 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B14828453 : Blo 211809 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B1655741 : Blo 211809 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B1295585 : Blo 211809 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B214247 : Blo 211809 214247 := bstep (se 1 (by rfl) ⟨160685, by rfl⟩ : syracuseStep 214247 = 321371) B321371
theorem B214503 : Blo 211809 214503 := bstep (se 1 (by rfl) ⟨160877, by rfl⟩ : syracuseStep 214503 = 321755) B321755
theorem B214575 : Blo 211809 214575 := bstep (se 1 (by rfl) ⟨160931, by rfl⟩ : syracuseStep 214575 = 321863) B321863
theorem B2934767 : Blo 211809 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B804923 : Blo 211809 804923 := bstep (se 1 (by rfl) ⟨603692, by rfl⟩ : syracuseStep 804923 = 1207385) B1207385
theorem B215143 : Blo 211809 215143 := bstep (se 1 (by rfl) ⟨161357, by rfl⟩ : syracuseStep 215143 = 322715) B322715
theorem B215295 : Blo 211809 215295 := bstep (se 1 (by rfl) ⟨161471, by rfl⟩ : syracuseStep 215295 = 322943) B322943
theorem B1820951 : Blo 211809 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B1624697 : Blo 211809 1624697 := bstep (se 2 (by rfl) ⟨609261, by rfl⟩ : syracuseStep 1624697 = 1218523) B1218523
theorem B215711 : Blo 211809 215711 := bstep (se 1 (by rfl) ⟨161783, by rfl⟩ : syracuseStep 215711 = 323567) B323567
theorem B1395625 : Blo 211809 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B1821635 : Blo 211809 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B1297387 : Blo 211809 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B4082993 : Blo 211809 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B3296699 : Blo 211809 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B478943 : Blo 211809 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B1560647 : Blo 211809 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B11194523 : Blo 211809 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B774359 : Blo 211809 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B1037033 : Blo 211809 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B611495 : Blo 211809 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B481193 : Blo 211809 481193 := bstep (se 2 (by rfl) ⟨180447, by rfl⟩ : syracuseStep 481193 = 360895) B360895
theorem B1628099 : Blo 211809 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B2578715 : Blo 211809 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B8969069 : Blo 211809 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B318431 : Blo 211809 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B777325 : Blo 211809 777325 := bstep (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) B291497
theorem B318875 : Blo 211809 318875 := bstep (se 1 (by rfl) ⟨239156, by rfl⟩ : syracuseStep 318875 = 478313) B478313
theorem B483047 : Blo 211809 483047 := bstep (se 1 (by rfl) ⟨362285, by rfl⟩ : syracuseStep 483047 = 724571) B724571
theorem B1531817 : Blo 211809 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B1106075 : Blo 211809 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B319721 : Blo 211809 319721 := bstep (se 2 (by rfl) ⟨119895, by rfl⟩ : syracuseStep 319721 = 239791) B239791
theorem B319913 : Blo 211809 319913 := bstep (se 2 (by rfl) ⟨119967, by rfl⟩ : syracuseStep 319913 = 239935) B239935
theorem B12509623 : Blo 211809 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B319967 : Blo 211809 319967 := bstep (se 1 (by rfl) ⟨239975, by rfl⟩ : syracuseStep 319967 = 479951) B479951
theorem B549359 : Blo 211809 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B320105 : Blo 211809 320105 := bstep (se 2 (by rfl) ⟨120039, by rfl⟩ : syracuseStep 320105 = 240079) B240079
theorem B320231 : Blo 211809 320231 := bstep (se 1 (by rfl) ⟨240173, by rfl⟩ : syracuseStep 320231 = 480347) B480347
theorem B1073897 : Blo 211809 1073897 := bstep (se 2 (by rfl) ⟨402711, by rfl⟩ : syracuseStep 1073897 = 805423) B805423
theorem B320681 : Blo 211809 320681 := bstep (se 2 (by rfl) ⟨120255, by rfl⟩ : syracuseStep 320681 = 240511) B240511
theorem B320831 : Blo 211809 320831 := bstep (se 1 (by rfl) ⟨240623, by rfl⟩ : syracuseStep 320831 = 481247) B481247
theorem B681319 : Blo 211809 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B484847 : Blo 211809 484847 := bstep (se 1 (by rfl) ⟨363635, by rfl⟩ : syracuseStep 484847 = 727271) B727271
theorem B321263 : Blo 211809 321263 := bstep (se 1 (by rfl) ⟨240947, by rfl⟩ : syracuseStep 321263 = 481895) B481895
theorem B5891869 : Blo 211809 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B107865893 : Blo 211809 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B813671 : Blo 211809 813671 := bstep (se 1 (by rfl) ⟨610253, by rfl⟩ : syracuseStep 813671 = 1220507) B1220507
theorem B322343 : Blo 211809 322343 := bstep (se 1 (by rfl) ⟨241757, by rfl⟩ : syracuseStep 322343 = 483515) B483515
theorem B322907 : Blo 211809 322907 := bstep (se 1 (by rfl) ⟨242180, by rfl⟩ : syracuseStep 322907 = 484361) B484361
theorem B6975163 : Blo 211809 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B323279 : Blo 211809 323279 := bstep (se 1 (by rfl) ⟨242459, by rfl⟩ : syracuseStep 323279 = 484919) B484919
theorem B814931 : Blo 211809 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B323687 : Blo 211809 323687 := bstep (se 1 (by rfl) ⟨242765, by rfl⟩ : syracuseStep 323687 = 485531) B485531
theorem B815615 : Blo 211809 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B2421737 : Blo 211809 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B1373915 : Blo 211809 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B4192019 : Blo 211809 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B358303 : Blo 211809 358303 := bstep (se 1 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 358303 = 537455) B537455
theorem B456673 : Blo 211809 456673 := bstep (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) B342505
theorem B227431 : Blo 211809 227431 := bstep (se 1 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 227431 = 341147) B341147
theorem B326111 : Blo 211809 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B359417 : Blo 211809 359417 := bstep (se 2 (by rfl) ⟨134781, by rfl⟩ : syracuseStep 359417 = 269563) B269563
theorem B1211507 : Blo 211809 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B392329 : Blo 211809 392329 := bstep (se 2 (by rfl) ⟨147123, by rfl⟩ : syracuseStep 392329 = 294247) B294247
theorem B359599 : Blo 211809 359599 := bstep (se 1 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 359599 = 539399) B539399
theorem B720251 : Blo 211809 720251 := bstep (se 1 (by rfl) ⟨540188, by rfl⟩ : syracuseStep 720251 = 1080377) B1080377
theorem B8289869 : Blo 211809 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B294619 : Blo 211809 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B688009 : Blo 211809 688009 := bstep (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) B516007
theorem B4161725 : Blo 211809 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B2949533 : Blo 211809 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B1081835 : Blo 211809 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B459263 : Blo 211809 459263 := bstep (se 1 (by rfl) ⟨344447, by rfl⟩ : syracuseStep 459263 = 688895) B688895
theorem B1212965 : Blo 211809 1212965 := bstep (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) B227431
theorem B4785419 : Blo 211809 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B722195 : Blo 211809 722195 := bstep (se 1 (by rfl) ⟨541646, by rfl⟩ : syracuseStep 722195 = 1083293) B1083293
theorem B7865743 : Blo 211809 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B1213967 : Blo 211809 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B1083131 : Blo 211809 1083131 := bstep (se 1 (by rfl) ⟨812348, by rfl⟩ : syracuseStep 1083131 = 1624697) B1624697
theorem B1214423 : Blo 211809 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B2721995 : Blo 211809 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B66717989 : Blo 211809 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B2197799 : Blo 211809 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B2459965 : Blo 211809 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B691355 : Blo 211809 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B1085399 : Blo 211809 1085399 := bstep (se 1 (by rfl) ⟨814049, by rfl⟩ : syracuseStep 1085399 = 1628099) B1628099
theorem B725327 : Blo 211809 725327 := bstep (se 1 (by rfl) ⟨543995, by rfl⟩ : syracuseStep 725327 = 1087991) B1087991
theorem B725435 : Blo 211809 725435 := bstep (se 1 (by rfl) ⟨544076, by rfl⟩ : syracuseStep 725435 = 1088153) B1088153
theorem B1085885 : Blo 211809 1085885 := bstep (se 3 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 1085885 = 407207) B407207
theorem B7377637 : Blo 211809 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B1021193 : Blo 211809 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1021211 : Blo 211809 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B366239 : Blo 211809 366239 := bstep (se 1 (by rfl) ⟨274679, by rfl⟩ : syracuseStep 366239 = 549359) B549359
theorem B269183 : Blo 211809 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B1614491 : Blo 211809 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B2794679 : Blo 211809 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B402985 : Blo 211809 402985 := bstep (se 2 (by rfl) ⟨151119, by rfl⟩ : syracuseStep 402985 = 302239) B302239
theorem B239611 : Blo 211809 239611 := bstep (se 1 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 239611 = 359417) B359417
theorem B6269345 : Blo 211809 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B6204761 : Blo 211809 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B863723 : Blo 211809 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B536615 : Blo 211809 536615 := bstep (se 1 (by rfl) ⟨402461, by rfl⟩ : syracuseStep 536615 = 804923) B804923
theorem B17412893 : Blo 211809 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B1357307 : Blo 211809 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B8795765 : Blo 211809 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B407663 : Blo 211809 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B1719143 : Blo 211809 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B539561 : Blo 211809 539561 := bstep (se 2 (by rfl) ⟨202335, by rfl⟩ : syracuseStep 539561 = 404671) B404671
theorem B5979379 : Blo 211809 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B212287 : Blo 211809 212287 := bstep (se 1 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 212287 = 318431) B318431
theorem B212583 : Blo 211809 212583 := bstep (se 1 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 212583 = 318875) B318875
theorem B213147 : Blo 211809 213147 := bstep (se 1 (by rfl) ⟨159860, by rfl⟩ : syracuseStep 213147 = 319721) B319721
theorem B1622267 : Blo 211809 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B213275 : Blo 211809 213275 := bstep (se 1 (by rfl) ⟨159956, by rfl⟩ : syracuseStep 213275 = 319913) B319913
theorem B213311 : Blo 211809 213311 := bstep (se 1 (by rfl) ⟨159983, by rfl⟩ : syracuseStep 213311 = 319967) B319967
theorem B213403 : Blo 211809 213403 := bstep (se 1 (by rfl) ⟨160052, by rfl⟩ : syracuseStep 213403 = 320105) B320105
theorem B213487 : Blo 211809 213487 := bstep (se 1 (by rfl) ⟨160115, by rfl⟩ : syracuseStep 213487 = 320231) B320231
theorem B213787 : Blo 211809 213787 := bstep (se 1 (by rfl) ⟨160340, by rfl⟩ : syracuseStep 213787 = 320681) B320681
theorem B213887 : Blo 211809 213887 := bstep (se 1 (by rfl) ⟨160415, by rfl⟩ : syracuseStep 213887 = 320831) B320831
theorem B214175 : Blo 211809 214175 := bstep (se 1 (by rfl) ⟨160631, by rfl⟩ : syracuseStep 214175 = 321263) B321263
theorem B71910595 : Blo 211809 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B869629 : Blo 211809 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B542447 : Blo 211809 542447 := bstep (se 1 (by rfl) ⟨406835, by rfl⟩ : syracuseStep 542447 = 813671) B813671
theorem B214895 : Blo 211809 214895 := bstep (se 1 (by rfl) ⟨161171, by rfl⟩ : syracuseStep 214895 = 322343) B322343
theorem B215271 : Blo 211809 215271 := bstep (se 1 (by rfl) ⟨161453, by rfl⟩ : syracuseStep 215271 = 322907) B322907
theorem B215519 : Blo 211809 215519 := bstep (se 1 (by rfl) ⟨161639, by rfl⟩ : syracuseStep 215519 = 323279) B323279
theorem B477737 : Blo 211809 477737 := bstep (se 2 (by rfl) ⟨179151, by rfl⟩ : syracuseStep 477737 = 358303) B358303
theorem B543287 : Blo 211809 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B608897 : Blo 211809 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B215791 : Blo 211809 215791 := bstep (se 1 (by rfl) ⟨161843, by rfl⟩ : syracuseStep 215791 = 323687) B323687
theorem B543743 : Blo 211809 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B970849 : Blo 211809 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B1036433 : Blo 211809 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B22106317 : Blo 211809 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B479465 : Blo 211809 479465 := bstep (se 2 (by rfl) ⟨179799, by rfl⟩ : syracuseStep 479465 = 359599) B359599
theorem B774431 : Blo 211809 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B807671 : Blo 211809 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B40555363 : Blo 211809 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B480167 : Blo 211809 480167 := bstep (se 1 (by rfl) ⟨360125, by rfl⟩ : syracuseStep 480167 = 720251) B720251
theorem B9885635 : Blo 211809 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B1103827 : Blo 211809 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B1956511 : Blo 211809 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B547931 : Blo 211809 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B908425 : Blo 211809 908425 := bstep (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) B681319
theorem B319145 : Blo 211809 319145 := bstep (se 2 (by rfl) ⟨119679, by rfl⟩ : syracuseStep 319145 = 239359) B239359
theorem B7855825 : Blo 211809 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B319295 : Blo 211809 319295 := bstep (se 1 (by rfl) ⟨239471, by rfl⟩ : syracuseStep 319295 = 478943) B478943
theorem B7463015 : Blo 211809 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B516239 : Blo 211809 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B484001 : Blo 211809 484001 := bstep (se 2 (by rfl) ⟨181500, by rfl⟩ : syracuseStep 484001 = 363001) B363001
theorem B484217 : Blo 211809 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B2057147 : Blo 211809 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B1860833 : Blo 211809 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B320795 : Blo 211809 320795 := bstep (se 1 (by rfl) ⟨240596, by rfl⟩ : syracuseStep 320795 = 481193) B481193
theorem B1729849 : Blo 211809 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B682139 : Blo 211809 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B9300217 : Blo 211809 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B322031 : Blo 211809 322031 := bstep (se 1 (by rfl) ⟨241523, by rfl⟩ : syracuseStep 322031 = 483047) B483047
theorem B715931 : Blo 211809 715931 := bstep (se 1 (by rfl) ⟨536948, by rfl⟩ : syracuseStep 715931 = 1073897) B1073897
theorem B323231 : Blo 211809 323231 := bstep (se 1 (by rfl) ⟨242423, by rfl⟩ : syracuseStep 323231 = 484847) B484847
theorem B291119 : Blo 211809 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B357689 : Blo 211809 357689 := bstep (se 2 (by rfl) ⟨134133, by rfl⟩ : syracuseStep 357689 = 268267) B268267
theorem B4126049 : Blo 211809 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B1079405 : Blo 211809 1079405 := bstep (se 3 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 1079405 = 404777) B404777
theorem B3307715 : Blo 211809 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B915943 : Blo 211809 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B523105 : Blo 211809 523105 := bstep (se 2 (by rfl) ⟨196164, by rfl⟩ : syracuseStep 523105 = 392329) B392329
theorem B392825 : Blo 211809 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B5471873 : Blo 211809 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B917345 : Blo 211809 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B1081511 : Blo 211809 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B1966355 : Blo 211809 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B721223 : Blo 211809 721223 := bstep (se 1 (by rfl) ⟨540917, by rfl⟩ : syracuseStep 721223 = 1081835) B1081835
theorem B361631 : Blo 211809 361631 := bstep (se 1 (by rfl) ⟨271223, by rfl⟩ : syracuseStep 361631 = 542447) B542447
theorem B722087 : Blo 211809 722087 := bstep (se 1 (by rfl) ⟨541565, by rfl⟩ : syracuseStep 722087 = 1083131) B1083131
theorem B362191 : Blo 211809 362191 := bstep (se 1 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 362191 = 543287) B543287
theorem B10487657 : Blo 211809 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B362495 : Blo 211809 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B460903 : Blo 211809 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B723599 : Blo 211809 723599 := bstep (se 1 (by rfl) ⟨542699, by rfl⟩ : syracuseStep 723599 = 1085399) B1085399
theorem B723923 : Blo 211809 723923 := bstep (se 1 (by rfl) ⟨542942, by rfl⟩ : syracuseStep 723923 = 1085885) B1085885
theorem B3279953 : Blo 211809 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B6590423 : Blo 211809 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B2789893 : Blo 211809 2789893 := bstep (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) B523105
theorem B9836849 : Blo 211809 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B383523173 : Blo 211809 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B54073817 : Blo 211809 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B4136507 : Blo 211809 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B11608595 : Blo 211809 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B1221257 : Blo 211809 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B238459 : Blo 211809 238459 := bstep (se 1 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 238459 = 357689) B357689
theorem B2303261 : Blo 211809 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B271775 : Blo 211809 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B2205143 : Blo 211809 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B7972505 : Blo 211809 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B3647915 : Blo 211809 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B306175 : Blo 211809 306175 := bstep (se 1 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 306175 = 459263) B459263
theorem B2763821 : Blo 211809 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B3190279 : Blo 211809 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B1814663 : Blo 211809 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B44478659 : Blo 211809 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B1159505 : Blo 211809 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B2306465 : Blo 211809 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B537313 : Blo 211809 537313 := bstep (se 2 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 537313 = 402985) B402985
theorem B12400289 : Blo 211809 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B538447 : Blo 211809 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B4962221 : Blo 211809 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B212763 : Blo 211809 212763 := bstep (se 1 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 212763 = 319145) B319145
theorem B212863 : Blo 211809 212863 := bstep (se 1 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 212863 = 319295) B319295
theorem B344159 : Blo 211809 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B1294465 : Blo 211809 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B29475089 : Blo 211809 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B1819037 : Blo 211809 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B213863 : Blo 211809 213863 := bstep (se 1 (by rfl) ⟨160397, by rfl⟩ : syracuseStep 213863 = 320795) B320795
theorem B4179563 : Blo 211809 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B214687 : Blo 211809 214687 := bstep (se 1 (by rfl) ⟨161015, by rfl⟩ : syracuseStep 214687 = 322031) B322031
theorem B1623725 : Blo 211809 1623725 := bstep (se 3 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 1623725 = 608897) B608897
theorem B477287 : Blo 211809 477287 := bstep (se 1 (by rfl) ⟨357965, by rfl⟩ : syracuseStep 477287 = 715931) B715931
theorem B215487 : Blo 211809 215487 := bstep (se 1 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 215487 = 323231) B323231
theorem B1461149 : Blo 211809 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B2608681 : Blo 211809 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B904871 : Blo 211809 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B10474433 : Blo 211809 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B611563 : Blo 211809 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B2774483 : Blo 211809 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B808643 : Blo 211809 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B776317 : Blo 211809 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B481463 : Blo 211809 481463 := bstep (se 1 (by rfl) ⟨361097, by rfl⟩ : syracuseStep 481463 = 722195) B722195
theorem B809311 : Blo 211809 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B809615 : Blo 211809 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B1465199 : Blo 211809 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B318491 : Blo 211809 318491 := bstep (se 1 (by rfl) ⟨238868, by rfl⟩ : syracuseStep 318491 = 477737) B477737
theorem B319481 : Blo 211809 319481 := bstep (se 2 (by rfl) ⟨119805, by rfl⟩ : syracuseStep 319481 = 239611) B239611
theorem B319643 : Blo 211809 319643 := bstep (se 1 (by rfl) ⟨239732, by rfl⟩ : syracuseStep 319643 = 479465) B479465
theorem B516287 : Blo 211809 516287 := bstep (se 1 (by rfl) ⟨387215, by rfl⟩ : syracuseStep 516287 = 774431) B774431
theorem B483551 : Blo 211809 483551 := bstep (se 1 (by rfl) ⟨362663, by rfl⟩ : syracuseStep 483551 = 725327) B725327
theorem B483623 : Blo 211809 483623 := bstep (se 1 (by rfl) ⟨362717, by rfl⟩ : syracuseStep 483623 = 725435) B725435
theorem B320111 : Blo 211809 320111 := bstep (se 1 (by rfl) ⟨240083, by rfl⟩ : syracuseStep 320111 = 480167) B480167
theorem B680795 : Blo 211809 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B680807 : Blo 211809 680807 := bstep (se 1 (by rfl) ⟨510605, by rfl⟩ : syracuseStep 680807 = 1021211) B1021211
theorem B976637 : Blo 211809 976637 := bstep (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) B366239
theorem B4975343 : Blo 211809 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1076327 : Blo 211809 1076327 := bstep (se 1 (by rfl) ⟨807245, by rfl⟩ : syracuseStep 1076327 = 1614491) B1614491
theorem B322667 : Blo 211809 322667 := bstep (se 1 (by rfl) ⟨242000, by rfl⟩ : syracuseStep 322667 = 484001) B484001
theorem B322811 : Blo 211809 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B1371431 : Blo 211809 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B1863119 : Blo 211809 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B717821 : Blo 211809 717821 := bstep (se 3 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 717821 = 269183) B269183
theorem B1471769 : Blo 211809 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B357743 : Blo 211809 357743 := bstep (se 1 (by rfl) ⟨268307, by rfl⟩ : syracuseStep 357743 = 536615) B536615
theorem B2750699 : Blo 211809 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B5863843 : Blo 211809 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B719603 : Blo 211809 719603 := bstep (se 1 (by rfl) ⟨539702, by rfl⟩ : syracuseStep 719603 = 1079405) B1079405
theorem B1211233 : Blo 211809 1211233 := bstep (se 2 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 1211233 = 908425) B908425
theorem B1146095 : Blo 211809 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B359707 : Blo 211809 359707 := bstep (se 1 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 359707 = 539561) B539561
theorem B261883 : Blo 211809 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B229439 : Blo 211809 229439 := bstep (se 1 (by rfl) ⟨172079, by rfl⟩ : syracuseStep 229439 = 344159) B344159
theorem B721007 : Blo 211809 721007 := bstep (se 1 (by rfl) ⟨540755, by rfl⟩ : syracuseStep 721007 = 1081511) B1081511
theorem B1310903 : Blo 211809 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1212691 : Blo 211809 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B2786375 : Blo 211809 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B1082483 : Blo 211809 1082483 := bstep (se 1 (by rfl) ⟨811862, by rfl⟩ : syracuseStep 1082483 = 1623725) B1623725
theorem B4393615 : Blo 211809 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B6982955 : Blo 211809 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B724733 : Blo 211809 724733 := bstep (se 3 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 724733 = 271775) B271775
theorem B36049211 : Blo 211809 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B3478241 : Blo 211809 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B2757671 : Blo 211809 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B7739063 : Blo 211809 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B5315003 : Blo 211809 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B2431943 : Blo 211809 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B3316895 : Blo 211809 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B1842547 : Blo 211809 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B238495 : Blo 211809 238495 := bstep (se 1 (by rfl) ⟨178871, by rfl⟩ : syracuseStep 238495 = 357743) B357743
theorem B8266859 : Blo 211809 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B1614977 : Blo 211809 1614977 := bstep (se 2 (by rfl) ⟨605616, by rfl⟩ : syracuseStep 1614977 = 1211233) B1211233
theorem B764063 : Blo 211809 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B241087 : Blo 211809 241087 := bstep (se 1 (by rfl) ⟨180815, by rfl⟩ : syracuseStep 241087 = 361631) B361631
theorem B6991771 : Blo 211809 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B241663 : Blo 211809 241663 := bstep (se 1 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 241663 = 362495) B362495
theorem B1849655 : Blo 211809 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B539095 : Blo 211809 539095 := bstep (se 1 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 539095 = 808643) B808643
theorem B408233 : Blo 211809 408233 := bstep (se 2 (by rfl) ⟨153087, by rfl⟩ : syracuseStep 408233 = 306175) B306175
theorem B539743 : Blo 211809 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B212327 : Blo 211809 212327 := bstep (se 1 (by rfl) ⟨159245, by rfl⟩ : syracuseStep 212327 = 318491) B318491
theorem B212987 : Blo 211809 212987 := bstep (se 1 (by rfl) ⟨159740, by rfl⟩ : syracuseStep 212987 = 319481) B319481
theorem B213095 : Blo 211809 213095 := bstep (se 1 (by rfl) ⟨159821, by rfl⟩ : syracuseStep 213095 = 319643) B319643
theorem B344191 : Blo 211809 344191 := bstep (se 1 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 344191 = 516287) B516287
theorem B213407 : Blo 211809 213407 := bstep (se 1 (by rfl) ⟨160055, by rfl⟩ : syracuseStep 213407 = 320111) B320111
theorem B3719857 : Blo 211809 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B26231597 : Blo 211809 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B215111 : Blo 211809 215111 := bstep (se 1 (by rfl) ⟨161333, by rfl⟩ : syracuseStep 215111 = 322667) B322667
theorem B215207 : Blo 211809 215207 := bstep (se 1 (by rfl) ⟨161405, by rfl⟩ : syracuseStep 215207 = 322811) B322811
theorem B1035089 : Blo 211809 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B773003 : Blo 211809 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B7818457 : Blo 211809 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B478547 : Blo 211809 478547 := bstep (se 1 (by rfl) ⟨358910, by rfl⟩ : syracuseStep 478547 = 717821) B717821
theorem B4968317 : Blo 211809 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B479609 : Blo 211809 479609 := bstep (se 2 (by rfl) ⟨179853, by rfl⟩ : syracuseStep 479609 = 359707) B359707
theorem B2412989 : Blo 211809 2412989 := bstep (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) B904871
theorem B479735 : Blo 211809 479735 := bstep (se 1 (by rfl) ⟨359801, by rfl⟩ : syracuseStep 479735 = 719603) B719603
theorem B349177 : Blo 211809 349177 := bstep (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) B261883
theorem B1725953 : Blo 211809 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B19650059 : Blo 211809 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B480815 : Blo 211809 480815 := bstep (se 1 (by rfl) ⟨360611, by rfl⟩ : syracuseStep 480815 = 721223) B721223
theorem B481391 : Blo 211809 481391 := bstep (se 1 (by rfl) ⟨361043, by rfl⟩ : syracuseStep 481391 = 722087) B722087
theorem B317945 : Blo 211809 317945 := bstep (se 2 (by rfl) ⟨119229, by rfl⟩ : syracuseStep 317945 = 238459) B238459
theorem B318191 : Blo 211809 318191 := bstep (se 1 (by rfl) ⟨238643, by rfl⟩ : syracuseStep 318191 = 477287) B477287
theorem B482399 : Blo 211809 482399 := bstep (se 1 (by rfl) ⟨361799, by rfl⟩ : syracuseStep 482399 = 723599) B723599
theorem B974099 : Blo 211809 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B482615 : Blo 211809 482615 := bstep (se 1 (by rfl) ⟨361961, by rfl⟩ : syracuseStep 482615 = 723923) B723923
theorem B2186635 : Blo 211809 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B482921 : Blo 211809 482921 := bstep (se 2 (by rfl) ⟨181095, by rfl⟩ : syracuseStep 482921 = 362191) B362191
theorem B614537 : Blo 211809 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B320975 : Blo 211809 320975 := bstep (se 1 (by rfl) ⟨240731, by rfl⟩ : syracuseStep 320975 = 481463) B481463
theorem B255682115 : Blo 211809 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B976799 : Blo 211809 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B4253705 : Blo 211809 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B322367 : Blo 211809 322367 := bstep (se 1 (by rfl) ⟨241775, by rfl⟩ : syracuseStep 322367 = 483551) B483551
theorem B322415 : Blo 211809 322415 := bstep (se 1 (by rfl) ⟨241811, by rfl⟩ : syracuseStep 322415 = 483623) B483623
theorem B814171 : Blo 211809 814171 := bstep (se 1 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 814171 = 1221257) B1221257
theorem B453863 : Blo 211809 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B453871 : Blo 211809 453871 := bstep (se 1 (by rfl) ⟨340403, by rfl⟩ : syracuseStep 453871 = 680807) B680807
theorem B1535507 : Blo 211809 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B716417 : Blo 211809 716417 := bstep (se 2 (by rfl) ⟨268656, by rfl⟩ : syracuseStep 716417 = 537313) B537313
theorem B1470095 : Blo 211809 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B651091 : Blo 211809 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B815417 : Blo 211809 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B717551 : Blo 211809 717551 := bstep (se 1 (by rfl) ⟨538163, by rfl⟩ : syracuseStep 717551 = 1076327) B1076327
theorem B914287 : Blo 211809 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B717929 : Blo 211809 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B1209775 : Blo 211809 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B29652439 : Blo 211809 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1537643 : Blo 211809 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B1079081 : Blo 211809 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B981179 : Blo 211809 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B3308147 : Blo 211809 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B1833799 : Blo 211809 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B458921 : Blo 211809 458921 := bstep (se 2 (by rfl) ⟨172095, by rfl⟩ : syracuseStep 458921 = 344191) B344191
theorem B721655 : Blo 211809 721655 := bstep (se 1 (by rfl) ⟨541241, by rfl⟩ : syracuseStep 721655 = 1082483) B1082483
theorem B690059 : Blo 211809 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B9275309 : Blo 211809 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B4655303 : Blo 211809 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B1608659 : Blo 211809 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B1838447 : Blo 211809 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B1085561 : Blo 211809 1085561 := bstep (se 2 (by rfl) ⟨407085, by rfl⟩ : syracuseStep 1085561 = 814171) B814171
theorem B10424609 : Blo 211809 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B3543335 : Blo 211809 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B5511239 : Blo 211809 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B1219049 : Blo 211809 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B465569 : Blo 211809 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B1613033 : Blo 211809 1613033 := bstep (se 2 (by rfl) ⟨604887, by rfl⟩ : syracuseStep 1613033 = 1209775) B1209775
theorem B1023671 : Blo 211809 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B1025095 : Blo 211809 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B2205431 : Blo 211809 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B272155 : Blo 211809 272155 := bstep (se 1 (by rfl) ⟨204116, by rfl⟩ : syracuseStep 272155 = 408233) B408233
theorem B13248845 : Blo 211809 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B1616921 : Blo 211809 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B4959809 : Blo 211809 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B24032807 : Blo 211809 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B5159375 : Blo 211809 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B4602541 : Blo 211809 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B605161 : Blo 211809 605161 := bstep (se 2 (by rfl) ⟨226935, by rfl⟩ : syracuseStep 605161 = 453871) B453871
theorem B211963 : Blo 211809 211963 := bstep (se 1 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 211963 = 317945) B317945
theorem B212127 : Blo 211809 212127 := bstep (se 1 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 212127 = 318191) B318191
theorem B1621295 : Blo 211809 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B2211263 : Blo 211809 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B868121 : Blo 211809 868121 := bstep (se 2 (by rfl) ⟨325545, by rfl⟩ : syracuseStep 868121 = 651091) B651091
theorem B9322361 : Blo 211809 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B409691 : Blo 211809 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B213983 : Blo 211809 213983 := bstep (se 1 (by rfl) ⟨160487, by rfl⟩ : syracuseStep 213983 = 320975) B320975
theorem B2835803 : Blo 211809 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B509375 : Blo 211809 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B214911 : Blo 211809 214911 := bstep (se 1 (by rfl) ⟨161183, by rfl⟩ : syracuseStep 214911 = 322367) B322367
theorem B214943 : Blo 211809 214943 := bstep (se 1 (by rfl) ⟨161207, by rfl⟩ : syracuseStep 214943 = 322415) B322415
theorem B39536585 : Blo 211809 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B477611 : Blo 211809 477611 := bstep (se 1 (by rfl) ⟨358208, by rfl⟩ : syracuseStep 477611 = 716417) B716417
theorem B543611 : Blo 211809 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B478367 : Blo 211809 478367 := bstep (se 1 (by rfl) ⟨358775, by rfl⟩ : syracuseStep 478367 = 717551) B717551
theorem B478619 : Blo 211809 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B2445065 : Blo 211809 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B1233103 : Blo 211809 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B480671 : Blo 211809 480671 := bstep (se 1 (by rfl) ⟨360503, by rfl⟩ : syracuseStep 480671 = 721007) B721007
theorem B873935 : Blo 211809 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B611837 : Blo 211809 611837 := bstep (se 3 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 611837 = 229439) B229439
theorem B17487731 : Blo 211809 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1857583 : Blo 211809 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B317993 : Blo 211809 317993 := bstep (se 2 (by rfl) ⟨119247, by rfl⟩ : syracuseStep 317993 = 238495) B238495
theorem B515335 : Blo 211809 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B319031 : Blo 211809 319031 := bstep (se 1 (by rfl) ⟨239273, by rfl⟩ : syracuseStep 319031 = 478547) B478547
theorem B483155 : Blo 211809 483155 := bstep (se 1 (by rfl) ⟨362366, by rfl⟩ : syracuseStep 483155 = 724733) B724733
theorem B319739 : Blo 211809 319739 := bstep (se 1 (by rfl) ⟨239804, by rfl⟩ : syracuseStep 319739 = 479609) B479609
theorem B319823 : Blo 211809 319823 := bstep (se 1 (by rfl) ⟨239867, by rfl⟩ : syracuseStep 319823 = 479735) B479735
theorem B5858153 : Blo 211809 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B13100039 : Blo 211809 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B320543 : Blo 211809 320543 := bstep (se 1 (by rfl) ⟨240407, by rfl⟩ : syracuseStep 320543 = 480815) B480815
theorem B320927 : Blo 211809 320927 := bstep (se 1 (by rfl) ⟨240695, by rfl⟩ : syracuseStep 320927 = 481391) B481391
theorem B321449 : Blo 211809 321449 := bstep (se 2 (by rfl) ⟨120543, by rfl⟩ : syracuseStep 321449 = 241087) B241087
theorem B321599 : Blo 211809 321599 := bstep (se 1 (by rfl) ⟨241199, by rfl⟩ : syracuseStep 321599 = 482399) B482399
theorem B649399 : Blo 211809 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B321743 : Blo 211809 321743 := bstep (se 1 (by rfl) ⟨241307, by rfl⟩ : syracuseStep 321743 = 482615) B482615
theorem B321947 : Blo 211809 321947 := bstep (se 1 (by rfl) ⟨241460, by rfl⟩ : syracuseStep 321947 = 482921) B482921
theorem B322217 : Blo 211809 322217 := bstep (se 2 (by rfl) ⟨120831, by rfl⟩ : syracuseStep 322217 = 241663) B241663
theorem B1076651 : Blo 211809 1076651 := bstep (se 1 (by rfl) ⟨807488, by rfl⟩ : syracuseStep 1076651 = 1614977) B1614977
theorem B170454743 : Blo 211809 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B651199 : Blo 211809 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B980063 : Blo 211809 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B1210301 : Blo 211809 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B718793 : Blo 211809 718793 := bstep (se 2 (by rfl) ⟨269547, by rfl⟩ : syracuseStep 718793 = 539095) B539095
theorem B719387 : Blo 211809 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B654119 : Blo 211809 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B719657 : Blo 211809 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B2456729 : Blo 211809 2456729 := bstep (se 2 (by rfl) ⟨921273, by rfl⟩ : syracuseStep 2456729 = 1842547) B1842547
theorem B2915513 : Blo 211809 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B362407 : Blo 211809 362407 := bstep (se 1 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 362407 = 543611) B543611
theorem B362873 : Blo 211809 362873 := bstep (se 2 (by rfl) ⟨136077, by rfl⟩ : syracuseStep 362873 = 272155) B272155
theorem B723707 : Blo 211809 723707 := bstep (se 1 (by rfl) ⟨542780, by rfl⟩ : syracuseStep 723707 = 1085561) B1085561
theorem B6949739 : Blo 211809 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B2362223 : Blo 211809 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B3674159 : Blo 211809 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B1840157 : Blo 211809 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B1644137 : Blo 211809 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B3905435 : Blo 211809 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B6136721 : Blo 211809 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B436079 : Blo 211809 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B1943675 : Blo 211809 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B273127 : Blo 211809 273127 := bstep (se 1 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 273127 = 409691) B409691
theorem B305947 : Blo 211809 305947 := bstep (se 1 (by rfl) ⟨229460, by rfl⟩ : syracuseStep 305947 = 458921) B458921
theorem B26357723 : Blo 211809 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B1225631 : Blo 211809 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B865865 : Blo 211809 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B407891 : Blo 211809 407891 := bstep (se 1 (by rfl) ⟨305918, by rfl⟩ : syracuseStep 407891 = 611837) B611837
theorem B1358333 : Blo 211809 1358333 := bstep (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) B509375
theorem B211995 : Blo 211809 211995 := bstep (se 1 (by rfl) ⟨158996, by rfl⟩ : syracuseStep 211995 = 317993) B317993
theorem B212687 : Blo 211809 212687 := bstep (se 1 (by rfl) ⟨159515, by rfl⟩ : syracuseStep 212687 = 319031) B319031
theorem B868265 : Blo 211809 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B213159 : Blo 211809 213159 := bstep (se 1 (by rfl) ⟨159869, by rfl⟩ : syracuseStep 213159 = 319739) B319739
theorem B213215 : Blo 211809 213215 := bstep (se 1 (by rfl) ⟨159911, by rfl⟩ : syracuseStep 213215 = 319823) B319823
theorem B8733359 : Blo 211809 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B213695 : Blo 211809 213695 := bstep (se 1 (by rfl) ⟨160271, by rfl⟩ : syracuseStep 213695 = 320543) B320543
theorem B213951 : Blo 211809 213951 := bstep (se 1 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 213951 = 320927) B320927
theorem B214299 : Blo 211809 214299 := bstep (se 1 (by rfl) ⟨160724, by rfl⟩ : syracuseStep 214299 = 321449) B321449
theorem B214399 : Blo 211809 214399 := bstep (se 1 (by rfl) ⟨160799, by rfl⟩ : syracuseStep 214399 = 321599) B321599
theorem B214495 : Blo 211809 214495 := bstep (se 1 (by rfl) ⟨160871, by rfl⟩ : syracuseStep 214495 = 321743) B321743
theorem B8832563 : Blo 211809 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B214631 : Blo 211809 214631 := bstep (se 1 (by rfl) ⟨160973, by rfl⟩ : syracuseStep 214631 = 321947) B321947
theorem B4966069 : Blo 211809 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B214811 : Blo 211809 214811 := bstep (se 1 (by rfl) ⟨161108, by rfl⟩ : syracuseStep 214811 = 322217) B322217
theorem B2476777 : Blo 211809 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B806867 : Blo 211809 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B479195 : Blo 211809 479195 := bstep (se 1 (by rfl) ⟨359396, by rfl⟩ : syracuseStep 479195 = 718793) B718793
theorem B806881 : Blo 211809 806881 := bstep (se 2 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 806881 = 605161) B605161
theorem B479591 : Blo 211809 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B479771 : Blo 211809 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B578747 : Blo 211809 578747 := bstep (se 1 (by rfl) ⟨434060, by rfl⟩ : syracuseStep 578747 = 868121) B868121
theorem B6214907 : Blo 211809 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B481103 : Blo 211809 481103 := bstep (se 1 (by rfl) ⟨360827, by rfl⟩ : syracuseStep 481103 = 721655) B721655
theorem B1890535 : Blo 211809 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B6183539 : Blo 211809 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B1366793 : Blo 211809 1366793 := bstep (se 2 (by rfl) ⟨512547, by rfl⟩ : syracuseStep 1366793 = 1025095) B1025095
theorem B3103535 : Blo 211809 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B318407 : Blo 211809 318407 := bstep (se 1 (by rfl) ⟨238805, by rfl⟩ : syracuseStep 318407 = 477611) B477611
theorem B1072439 : Blo 211809 1072439 := bstep (se 1 (by rfl) ⟨804329, by rfl⟩ : syracuseStep 1072439 = 1608659) B1608659
theorem B318911 : Blo 211809 318911 := bstep (se 1 (by rfl) ⟨239183, by rfl⟩ : syracuseStep 318911 = 478367) B478367
theorem B319079 : Blo 211809 319079 := bstep (se 1 (by rfl) ⟨239309, by rfl⟩ : syracuseStep 319079 = 478619) B478619
theorem B1630043 : Blo 211809 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B320447 : Blo 211809 320447 := bstep (se 1 (by rfl) ⟨240335, by rfl⟩ : syracuseStep 320447 = 480671) B480671
theorem B582623 : Blo 211809 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B11658487 : Blo 211809 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B812699 : Blo 211809 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B1075355 : Blo 211809 1075355 := bstep (se 1 (by rfl) ⟨806516, by rfl⟩ : syracuseStep 1075355 = 1613033) B1613033
theorem B682447 : Blo 211809 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B322103 : Blo 211809 322103 := bstep (se 1 (by rfl) ⟨241577, by rfl⟩ : syracuseStep 322103 = 483155) B483155
theorem B1470287 : Blo 211809 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B1077947 : Blo 211809 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B717767 : Blo 211809 717767 := bstep (se 1 (by rfl) ⟨538325, by rfl⟩ : syracuseStep 717767 = 1076651) B1076651
theorem B3306539 : Blo 211809 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B113636495 : Blo 211809 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B653375 : Blo 211809 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B16021871 : Blo 211809 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B3439583 : Blo 211809 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B687113 : Blo 211809 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B1637819 : Blo 211809 1637819 := bstep (se 1 (by rfl) ⟨1228364, by rfl⟩ : syracuseStep 1637819 = 2456729) B2456729
theorem B1080863 : Blo 211809 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B1474175 : Blo 211809 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B1574815 : Blo 211809 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B6621425 : Blo 211809 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B8817437 : Blo 211809 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B364169 : Blo 211809 364169 := bstep (se 2 (by rfl) ⟨136563, by rfl⟩ : syracuseStep 364169 = 273127) B273127
theorem B2069023 : Blo 211809 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B1086695 : Blo 211809 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B17571815 : Blo 211809 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B435583 : Blo 211809 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B271927 : Blo 211809 271927 := bstep (se 1 (by rfl) ⟨203945, by rfl⟩ : syracuseStep 271927 = 407891) B407891
theorem B1091879 : Blo 211809 1091879 := bstep (se 1 (by rfl) ⟨818909, by rfl⟩ : syracuseStep 1091879 = 1637819) B1637819
theorem B241915 : Blo 211809 241915 := bstep (se 1 (by rfl) ⟨181436, by rfl⟩ : syracuseStep 241915 = 362873) B362873
theorem B15544649 : Blo 211809 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B4633159 : Blo 211809 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B537911 : Blo 211809 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B1226771 : Blo 211809 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B4143271 : Blo 211809 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B407929 : Blo 211809 407929 := bstep (se 2 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 407929 = 305947) B305947
theorem B1096091 : Blo 211809 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B212271 : Blo 211809 212271 := bstep (se 1 (by rfl) ⟨159203, by rfl⟩ : syracuseStep 212271 = 318407) B318407
theorem B212607 : Blo 211809 212607 := bstep (se 1 (by rfl) ⟨159455, by rfl⟩ : syracuseStep 212607 = 318911) B318911
theorem B212719 : Blo 211809 212719 := bstep (se 1 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 212719 = 319079) B319079
theorem B213631 : Blo 211809 213631 := bstep (se 1 (by rfl) ⟨160223, by rfl⟩ : syracuseStep 213631 = 320447) B320447
theorem B541799 : Blo 211809 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B1295783 : Blo 211809 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B214735 : Blo 211809 214735 := bstep (se 1 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 214735 = 322103) B322103
theorem B478511 : Blo 211809 478511 := bstep (se 1 (by rfl) ⟨358883, by rfl⟩ : syracuseStep 478511 = 717767) B717767
theorem B577243 : Blo 211809 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B905555 : Blo 211809 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B578843 : Blo 211809 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B5822239 : Blo 211809 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B5888375 : Blo 211809 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B482471 : Blo 211809 482471 := bstep (se 1 (by rfl) ⟨361853, by rfl⟩ : syracuseStep 482471 = 723707) B723707
theorem B483209 : Blo 211809 483209 := bstep (se 2 (by rfl) ⟨181203, by rfl⟩ : syracuseStep 483209 = 362407) B362407
theorem B319463 : Blo 211809 319463 := bstep (se 1 (by rfl) ⟨239597, by rfl⟩ : syracuseStep 319463 = 479195) B479195
theorem B2449439 : Blo 211809 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B319727 : Blo 211809 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B319847 : Blo 211809 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B909929 : Blo 211809 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B385831 : Blo 211809 385831 := bstep (se 1 (by rfl) ⟨289373, by rfl⟩ : syracuseStep 385831 = 578747) B578747
theorem B3302369 : Blo 211809 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B320735 : Blo 211809 320735 := bstep (se 1 (by rfl) ⟨240551, by rfl⟩ : syracuseStep 320735 = 481103) B481103
theorem B4122359 : Blo 211809 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B911195 : Blo 211809 911195 := bstep (se 1 (by rfl) ⟨683396, by rfl⟩ : syracuseStep 911195 = 1366793) B1366793
theorem B714959 : Blo 211809 714959 := bstep (se 1 (by rfl) ⟨536219, by rfl⟩ : syracuseStep 714959 = 1072439) B1072439
theorem B10414493 : Blo 211809 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1075841 : Blo 211809 1075841 := bstep (se 2 (by rfl) ⟨403440, by rfl⟩ : syracuseStep 1075841 = 806881) B806881
theorem B4091147 : Blo 211809 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B388415 : Blo 211809 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B290719 : Blo 211809 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B716903 : Blo 211809 716903 := bstep (se 1 (by rfl) ⟨537677, by rfl⟩ : syracuseStep 716903 = 1075355) B1075355
theorem B980191 : Blo 211809 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B2520713 : Blo 211809 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B718631 : Blo 211809 718631 := bstep (se 1 (by rfl) ⟨538973, by rfl⟩ : syracuseStep 718631 = 1077947) B1077947
theorem B817087 : Blo 211809 817087 := bstep (se 1 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 817087 = 1225631) B1225631
theorem B75757663 : Blo 211809 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B10681247 : Blo 211809 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B2293055 : Blo 211809 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B458075 : Blo 211809 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B720575 : Blo 211809 720575 := bstep (se 1 (by rfl) ⟨540431, by rfl⟩ : syracuseStep 720575 = 1080863) B1080863
theorem B982783 : Blo 211809 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B361199 : Blo 211809 361199 := bstep (se 1 (by rfl) ⟨270899, by rfl⟩ : syracuseStep 361199 = 541799) B541799
theorem B41452397 : Blo 211809 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B362569 : Blo 211809 362569 := bstep (se 2 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 362569 = 271927) B271927
theorem B2099753 : Blo 211809 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B724463 : Blo 211809 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B2201579 : Blo 211809 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B2758697 : Blo 211809 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B727919 : Blo 211809 727919 := bstep (se 1 (by rfl) ⟨545939, by rfl⟩ : syracuseStep 727919 = 1091879) B1091879
theorem B2727431 : Blo 211809 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B1089449 : Blo 211809 1089449 := bstep (se 2 (by rfl) ⟨408543, by rfl⟩ : syracuseStep 1089449 = 817087) B817087
theorem B1680475 : Blo 211809 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B730727 : Blo 211809 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B7120831 : Blo 211809 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B1550501 : Blo 211809 1550501 := bstep (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) B290719
theorem B305383 : Blo 211809 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B404040869 : Blo 211809 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B863855 : Blo 211809 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B5878291 : Blo 211809 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B242779 : Blo 211809 242779 := bstep (se 1 (by rfl) ⟨182084, by rfl⟩ : syracuseStep 242779 = 364169) B364169
theorem B603703 : Blo 211809 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B769657 : Blo 211809 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B212975 : Blo 211809 212975 := bstep (se 1 (by rfl) ⟨159731, by rfl⟩ : syracuseStep 212975 = 319463) B319463
theorem B11714543 : Blo 211809 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B213151 : Blo 211809 213151 := bstep (se 1 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 213151 = 319727) B319727
theorem B213231 : Blo 211809 213231 := bstep (se 1 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 213231 = 319847) B319847
theorem B606619 : Blo 211809 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B6177545 : Blo 211809 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B213823 : Blo 211809 213823 := bstep (se 1 (by rfl) ⟨160367, by rfl⟩ : syracuseStep 213823 = 320735) B320735
theorem B607463 : Blo 211809 607463 := bstep (se 1 (by rfl) ⟨455597, by rfl⟩ : syracuseStep 607463 = 911195) B911195
theorem B476639 : Blo 211809 476639 := bstep (se 1 (by rfl) ⟨357479, by rfl⟩ : syracuseStep 476639 = 714959) B714959
theorem B477935 : Blo 211809 477935 := bstep (se 1 (by rfl) ⟨358451, by rfl⟩ : syracuseStep 477935 = 716903) B716903
theorem B5524361 : Blo 211809 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B543905 : Blo 211809 543905 := bstep (se 2 (by rfl) ⟨203964, by rfl⟩ : syracuseStep 543905 = 407929) B407929
theorem B1035773 : Blo 211809 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B479087 : Blo 211809 479087 := bstep (se 1 (by rfl) ⟨359315, by rfl⟩ : syracuseStep 479087 = 718631) B718631
theorem B1528703 : Blo 211809 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B480383 : Blo 211809 480383 := bstep (se 1 (by rfl) ⟨360287, by rfl⟩ : syracuseStep 480383 = 720575) B720575
theorem B514441 : Blo 211809 514441 := bstep (se 2 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 514441 = 385831) B385831
theorem B4414283 : Blo 211809 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B319007 : Blo 211809 319007 := bstep (se 1 (by rfl) ⟨239255, by rfl⟩ : syracuseStep 319007 = 478511) B478511
theorem B385895 : Blo 211809 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B3925583 : Blo 211809 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B321647 : Blo 211809 321647 := bstep (se 1 (by rfl) ⟨241235, by rfl⟩ : syracuseStep 321647 = 482471) B482471
theorem B322139 : Blo 211809 322139 := bstep (se 1 (by rfl) ⟨241604, by rfl⟩ : syracuseStep 322139 = 483209) B483209
theorem B1632959 : Blo 211809 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B322553 : Blo 211809 322553 := bstep (se 2 (by rfl) ⟨120957, by rfl⟩ : syracuseStep 322553 = 241915) B241915
theorem B2748239 : Blo 211809 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B6942995 : Blo 211809 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B1306921 : Blo 211809 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B717227 : Blo 211809 717227 := bstep (se 1 (by rfl) ⟨537920, by rfl⟩ : syracuseStep 717227 = 1075841) B1075841
theorem B2323109 : Blo 211809 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B7762985 : Blo 211809 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B358607 : Blo 211809 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B817847 : Blo 211809 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B1310377 : Blo 211809 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B362603 : Blo 211809 362603 := bstep (se 1 (by rfl) ⟨271952, by rfl⟩ : syracuseStep 362603 = 543905) B543905
theorem B690515 : Blo 211809 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B1019135 : Blo 211809 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B1839131 : Blo 211809 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B726299 : Blo 211809 726299 := bstep (se 1 (by rfl) ⟨544724, by rfl⟩ : syracuseStep 726299 = 1089449) B1089449
theorem B1742561 : Blo 211809 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B7837721 : Blo 211809 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1088639 : Blo 211809 1088639 := bstep (se 1 (by rfl) ⟨816479, by rfl⟩ : syracuseStep 1088639 = 1632959) B1632959
theorem B269360579 : Blo 211809 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B4628663 : Blo 211809 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B1548739 : Blo 211809 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B239071 : Blo 211809 239071 := bstep (se 1 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 239071 = 358607) B358607
theorem B1026209 : Blo 211809 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B1747169 : Blo 211809 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B7809695 : Blo 211809 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B240799 : Blo 211809 240799 := bstep (se 1 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 240799 = 361199) B361199
theorem B27634931 : Blo 211809 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B404975 : Blo 211809 404975 := bstep (se 1 (by rfl) ⟨303731, by rfl⟩ : syracuseStep 404975 = 607463) B607463
theorem B2240633 : Blo 211809 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B3682907 : Blo 211809 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B407177 : Blo 211809 407177 := bstep (se 2 (by rfl) ⟨152691, by rfl⟩ : syracuseStep 407177 = 305383) B305383
theorem B1818287 : Blo 211809 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B212671 : Blo 211809 212671 := bstep (se 1 (by rfl) ⟨159503, by rfl⟩ : syracuseStep 212671 = 319007) B319007
theorem B214431 : Blo 211809 214431 := bstep (se 1 (by rfl) ⟨160823, by rfl⟩ : syracuseStep 214431 = 321647) B321647
theorem B1033667 : Blo 211809 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B214759 : Blo 211809 214759 := bstep (se 1 (by rfl) ⟨161069, by rfl⟩ : syracuseStep 214759 = 322139) B322139
theorem B215035 : Blo 211809 215035 := bstep (se 1 (by rfl) ⟨161276, by rfl⟩ : syracuseStep 215035 = 322553) B322553
theorem B804937 : Blo 211809 804937 := bstep (se 2 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 804937 = 603703) B603703
theorem B575903 : Blo 211809 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B478151 : Blo 211809 478151 := bstep (se 1 (by rfl) ⟨358613, by rfl⟩ : syracuseStep 478151 = 717227) B717227
theorem B545231 : Blo 211809 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B4118363 : Blo 211809 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B808825 : Blo 211809 808825 := bstep (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) B606619
theorem B317759 : Blo 211809 317759 := bstep (se 1 (by rfl) ⟨238319, by rfl⟩ : syracuseStep 317759 = 476639) B476639
theorem B1399835 : Blo 211809 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B318623 : Blo 211809 318623 := bstep (se 1 (by rfl) ⟨238967, by rfl⟩ : syracuseStep 318623 = 477935) B477935
theorem B482975 : Blo 211809 482975 := bstep (se 1 (by rfl) ⟨362231, by rfl⟩ : syracuseStep 482975 = 724463) B724463
theorem B319391 : Blo 211809 319391 := bstep (se 1 (by rfl) ⟨239543, by rfl⟩ : syracuseStep 319391 = 479087) B479087
theorem B9494441 : Blo 211809 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B483425 : Blo 211809 483425 := bstep (se 2 (by rfl) ⟨181284, by rfl⟩ : syracuseStep 483425 = 362569) B362569
theorem B320255 : Blo 211809 320255 := bstep (se 1 (by rfl) ⟨240191, by rfl⟩ : syracuseStep 320255 = 480383) B480383
theorem B1467719 : Blo 211809 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B2942855 : Blo 211809 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B485279 : Blo 211809 485279 := bstep (se 1 (by rfl) ⟨363959, by rfl⟩ : syracuseStep 485279 = 727919) B727919
theorem B257263 : Blo 211809 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B2617055 : Blo 211809 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B487151 : Blo 211809 487151 := bstep (se 1 (by rfl) ⟨365363, by rfl⟩ : syracuseStep 487151 = 730727) B730727
theorem B323705 : Blo 211809 323705 := bstep (se 2 (by rfl) ⟨121389, by rfl⟩ : syracuseStep 323705 = 242779) B242779
theorem B1832159 : Blo 211809 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B685921 : Blo 211809 685921 := bstep (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) B514441
theorem B5175323 : Blo 211809 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B689111 : Blo 211809 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B460343 : Blo 211809 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B8259941 : Blo 211809 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B363487 : Blo 211809 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B725759 : Blo 211809 725759 := bstep (se 1 (by rfl) ⟨544319, by rfl⟩ : syracuseStep 725759 = 1088639) B1088639
theorem B6329627 : Blo 211809 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B3085775 : Blo 211809 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B18423287 : Blo 211809 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B269983 : Blo 211809 269983 := bstep (se 1 (by rfl) ⟨202487, by rfl⟩ : syracuseStep 269983 = 404975) B404975
theorem B1744703 : Blo 211809 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B1221439 : Blo 211809 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B271451 : Blo 211809 271451 := bstep (se 1 (by rfl) ⟨203588, by rfl⟩ : syracuseStep 271451 = 407177) B407177
theorem B3450215 : Blo 211809 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B5975021 : Blo 211809 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B241735 : Blo 211809 241735 := bstep (se 1 (by rfl) ⟨181301, by rfl⟩ : syracuseStep 241735 = 362603) B362603
theorem B1226087 : Blo 211809 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B1161707 : Blo 211809 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B5225147 : Blo 211809 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B211839 : Blo 211809 211839 := bstep (se 1 (by rfl) ⟨158879, by rfl⟩ : syracuseStep 211839 = 317759) B317759
theorem B933223 : Blo 211809 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B212415 : Blo 211809 212415 := bstep (se 1 (by rfl) ⟨159311, by rfl⟩ : syracuseStep 212415 = 318623) B318623
theorem B212927 : Blo 211809 212927 := bstep (se 1 (by rfl) ⟨159695, by rfl⟩ : syracuseStep 212927 = 319391) B319391
theorem B213503 : Blo 211809 213503 := bstep (se 1 (by rfl) ⟨160127, by rfl⟩ : syracuseStep 213503 = 320255) B320255
theorem B1164779 : Blo 211809 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B215803 : Blo 211809 215803 := bstep (se 1 (by rfl) ⟨161852, by rfl⟩ : syracuseStep 215803 = 323705) B323705
theorem B718294877 : Blo 211809 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B383935 : Blo 211809 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B318761 : Blo 211809 318761 := bstep (se 2 (by rfl) ⟨119535, by rfl⟩ : syracuseStep 318761 = 239071) B239071
theorem B318767 : Blo 211809 318767 := bstep (se 1 (by rfl) ⟨239075, by rfl⟩ : syracuseStep 318767 = 478151) B478151
theorem B679423 : Blo 211809 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B1073249 : Blo 211809 1073249 := bstep (se 2 (by rfl) ⟨402468, by rfl⟩ : syracuseStep 1073249 = 804937) B804937
theorem B484199 : Blo 211809 484199 := bstep (se 1 (by rfl) ⟨363149, by rfl⟩ : syracuseStep 484199 = 726299) B726299
theorem B2745575 : Blo 211809 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B321065 : Blo 211809 321065 := bstep (se 2 (by rfl) ⟨120399, by rfl⟩ : syracuseStep 321065 = 240799) B240799
theorem B321983 : Blo 211809 321983 := bstep (se 1 (by rfl) ⟨241487, by rfl⟩ : syracuseStep 321983 = 482975) B482975
theorem B322283 : Blo 211809 322283 := bstep (se 1 (by rfl) ⟨241712, by rfl⟩ : syracuseStep 322283 = 483425) B483425
theorem B978479 : Blo 211809 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B1372069 : Blo 211809 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B1961903 : Blo 211809 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B323519 : Blo 211809 323519 := bstep (se 1 (by rfl) ⟨242639, by rfl⟩ : syracuseStep 323519 = 485279) B485279
theorem B684139 : Blo 211809 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B5206463 : Blo 211809 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B914561 : Blo 211809 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B324767 : Blo 211809 324767 := bstep (se 1 (by rfl) ⟨243575, by rfl⟩ : syracuseStep 324767 = 487151) B487151
theorem B1078433 : Blo 211809 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B2455271 : Blo 211809 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B1212191 : Blo 211809 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B459407 : Blo 211809 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B5506627 : Blo 211809 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B723869 : Blo 211809 723869 := bstep (se 3 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 723869 = 271451) B271451
theorem B3483431 : Blo 211809 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B866045 : Blo 211809 866045 := bstep (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) B324767
theorem B1227581 : Blo 211809 1227581 := bstep (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) B460343
theorem B212507 : Blo 211809 212507 := bstep (se 1 (by rfl) ⟨159380, by rfl⟩ : syracuseStep 212507 = 318761) B318761
theorem B212511 : Blo 211809 212511 := bstep (se 1 (by rfl) ⟨159383, by rfl⟩ : syracuseStep 212511 = 318767) B318767
theorem B1163135 : Blo 211809 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B214043 : Blo 211809 214043 := bstep (se 1 (by rfl) ⟨160532, by rfl⟩ : syracuseStep 214043 = 321065) B321065
theorem B3097885 : Blo 211809 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B214655 : Blo 211809 214655 := bstep (se 1 (by rfl) ⟨160991, by rfl⟩ : syracuseStep 214655 = 321983) B321983
theorem B214855 : Blo 211809 214855 := bstep (se 1 (by rfl) ⟨161141, by rfl⟩ : syracuseStep 214855 = 322283) B322283
theorem B3983347 : Blo 211809 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B215679 : Blo 211809 215679 := bstep (se 1 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 215679 = 323519) B323519
theorem B609707 : Blo 211809 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B511913 : Blo 211809 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B905897 : Blo 211809 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B808127 : Blo 211809 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B776519 : Blo 211809 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B1628585 : Blo 211809 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B478863251 : Blo 211809 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B483839 : Blo 211809 483839 := bstep (se 1 (by rfl) ⟨362879, by rfl⟩ : syracuseStep 483839 = 725759) B725759
theorem B4219751 : Blo 211809 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B9200573 : Blo 211809 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B2057183 : Blo 211809 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B484649 : Blo 211809 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B12282191 : Blo 211809 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B1829425 : Blo 211809 1829425 := bstep (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) B1372069
theorem B715499 : Blo 211809 715499 := bstep (se 1 (by rfl) ⟨536624, by rfl⟩ : syracuseStep 715499 = 1073249) B1073249
theorem B322313 : Blo 211809 322313 := bstep (se 2 (by rfl) ⟨120867, by rfl⟩ : syracuseStep 322313 = 241735) B241735
theorem B912185 : Blo 211809 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B322799 : Blo 211809 322799 := bstep (se 1 (by rfl) ⟨242099, by rfl⟩ : syracuseStep 322799 = 484199) B484199
theorem B1830383 : Blo 211809 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B652319 : Blo 211809 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B1307935 : Blo 211809 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B3470975 : Blo 211809 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B718955 : Blo 211809 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B817391 : Blo 211809 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B1636847 : Blo 211809 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B1244297 : Blo 211809 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B359977 : Blo 211809 359977 := bstep (se 2 (by rfl) ⟨134991, by rfl⟩ : syracuseStep 359977 = 269983) B269983
theorem B4130513 : Blo 211809 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B7342169 : Blo 211809 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B5311129 : Blo 211809 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B1085723 : Blo 211809 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B6133715 : Blo 211809 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B1743913 : Blo 211809 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1220255 : Blo 211809 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B434879 : Blo 211809 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B1091231 : Blo 211809 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B829531 : Blo 211809 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B306271 : Blo 211809 306271 := bstep (se 1 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 306271 = 459407) B459407
theorem B406471 : Blo 211809 406471 := bstep (se 1 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 406471 = 609707) B609707
theorem B341275 : Blo 211809 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B603931 : Blo 211809 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B2439233 : Blo 211809 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B538751 : Blo 211809 538751 := bstep (se 1 (by rfl) ⟨404063, by rfl⟩ : syracuseStep 538751 = 808127) B808127
theorem B180042709 : Blo 211809 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B319242167 : Blo 211809 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B476999 : Blo 211809 476999 := bstep (se 1 (by rfl) ⟨357749, by rfl⟩ : syracuseStep 476999 = 715499) B715499
theorem B214875 : Blo 211809 214875 := bstep (se 1 (by rfl) ⟨161156, by rfl⟩ : syracuseStep 214875 = 322313) B322313
theorem B608123 : Blo 211809 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B215199 : Blo 211809 215199 := bstep (se 1 (by rfl) ⟨161399, by rfl⟩ : syracuseStep 215199 = 322799) B322799
theorem B2313983 : Blo 211809 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B577363 : Blo 211809 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B479303 : Blo 211809 479303 := bstep (se 1 (by rfl) ⟨359477, by rfl⟩ : syracuseStep 479303 = 718955) B718955
theorem B544927 : Blo 211809 544927 := bstep (se 1 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 544927 = 817391) B817391
theorem B479969 : Blo 211809 479969 := bstep (se 2 (by rfl) ⟨179988, by rfl⟩ : syracuseStep 479969 = 359977) B359977
theorem B775423 : Blo 211809 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B482579 : Blo 211809 482579 := bstep (se 1 (by rfl) ⟨361934, by rfl⟩ : syracuseStep 482579 = 723869) B723869
theorem B517679 : Blo 211809 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B322559 : Blo 211809 322559 := bstep (se 1 (by rfl) ⟨241919, by rfl⟩ : syracuseStep 322559 = 483839) B483839
theorem B1371455 : Blo 211809 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B323099 : Blo 211809 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B2322287 : Blo 211809 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B8188127 : Blo 211809 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B818387 : Blo 211809 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B4424165 : Blo 211809 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B2753675 : Blo 211809 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B1542655 : Blo 211809 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B723815 : Blo 211809 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B7081505 : Blo 211809 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B726569 : Blo 211809 726569 := bstep (se 2 (by rfl) ⟨272463, by rfl⟩ : syracuseStep 726569 = 544927) B544927
theorem B727487 : Blo 211809 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B1548191 : Blo 211809 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B405415 : Blo 211809 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B769817 : Blo 211809 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B19579117 : Blo 211809 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B345119 : Blo 211809 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B541961 : Blo 211809 541961 := bstep (se 2 (by rfl) ⟨203235, by rfl⟩ : syracuseStep 541961 = 406471) B406471
theorem B1033897 : Blo 211809 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B215039 : Blo 211809 215039 := bstep (se 1 (by rfl) ⟨161279, by rfl⟩ : syracuseStep 215039 = 322559) B322559
theorem B215399 : Blo 211809 215399 := bstep (se 1 (by rfl) ⟨161549, by rfl⟩ : syracuseStep 215399 = 323099) B323099
theorem B805241 : Blo 211809 805241 := bstep (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) B603931
theorem B5458751 : Blo 211809 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B1626155 : Blo 211809 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B545591 : Blo 211809 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B317999 : Blo 211809 317999 := bstep (se 1 (by rfl) ⟨238499, by rfl⟩ : syracuseStep 317999 = 476999) B476999
theorem B319535 : Blo 211809 319535 := bstep (se 1 (by rfl) ⟨239651, by rfl⟩ : syracuseStep 319535 = 479303) B479303
theorem B319979 : Blo 211809 319979 := bstep (se 1 (by rfl) ⟨239984, by rfl⟩ : syracuseStep 319979 = 479969) B479969
theorem B4089143 : Blo 211809 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B321719 : Blo 211809 321719 := bstep (se 1 (by rfl) ⟨241289, by rfl⟩ : syracuseStep 321719 = 482579) B482579
theorem B813503 : Blo 211809 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B289919 : Blo 211809 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B1633445 : Blo 211809 1633445 := bstep (se 4 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 1633445 = 306271) B306271
theorem B455033 : Blo 211809 455033 := bstep (se 2 (by rfl) ⟨170637, by rfl⟩ : syracuseStep 455033 = 341275) B341275
theorem B914303 : Blo 211809 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B240056945 : Blo 211809 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2325217 : Blo 211809 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B359167 : Blo 211809 359167 := bstep (se 1 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 359167 = 538751) B538751
theorem B212828111 : Blo 211809 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B2949443 : Blo 211809 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1835783 : Blo 211809 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B361307 : Blo 211809 361307 := bstep (se 1 (by rfl) ⟨270980, by rfl⟩ : syracuseStep 361307 = 541961) B541961
theorem B3639167 : Blo 211809 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B1378529 : Blo 211809 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B4721003 : Blo 211809 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B8227493 : Blo 211809 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B1084103 : Blo 211809 1084103 := bstep (se 1 (by rfl) ⟨813077, by rfl⟩ : syracuseStep 1084103 = 1626155) B1626155
theorem B920317 : Blo 211809 920317 := bstep (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) B345119
theorem B363727 : Blo 211809 363727 := bstep (se 1 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 363727 = 545591) B545591
theorem B2726095 : Blo 211809 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B1088963 : Blo 211809 1088963 := bstep (se 1 (by rfl) ⟨816722, by rfl⟩ : syracuseStep 1088963 = 1633445) B1633445
theorem B303355 : Blo 211809 303355 := bstep (se 1 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 303355 = 455033) B455033
theorem B536827 : Blo 211809 536827 := bstep (se 1 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 536827 = 805241) B805241
theorem B211999 : Blo 211809 211999 := bstep (se 1 (by rfl) ⟨158999, by rfl⟩ : syracuseStep 211999 = 317999) B317999
theorem B540553 : Blo 211809 540553 := bstep (se 2 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 540553 = 405415) B405415
theorem B213023 : Blo 211809 213023 := bstep (se 1 (by rfl) ⟨159767, by rfl⟩ : syracuseStep 213023 = 319535) B319535
theorem B213319 : Blo 211809 213319 := bstep (se 1 (by rfl) ⟨159989, by rfl⟩ : syracuseStep 213319 = 319979) B319979
theorem B214479 : Blo 211809 214479 := bstep (se 1 (by rfl) ⟨160859, by rfl⟩ : syracuseStep 214479 = 321719) B321719
theorem B542335 : Blo 211809 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B773117 : Blo 211809 773117 := bstep (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) B289919
theorem B609535 : Blo 211809 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B3100289 : Blo 211809 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B478889 : Blo 211809 478889 := bstep (se 2 (by rfl) ⟨179583, by rfl⟩ : syracuseStep 478889 = 359167) B359167
theorem B513211 : Blo 211809 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B26105489 : Blo 211809 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B482543 : Blo 211809 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B484379 : Blo 211809 484379 := bstep (se 1 (by rfl) ⟨363284, by rfl⟩ : syracuseStep 484379 = 726569) B726569
theorem B484991 : Blo 211809 484991 := bstep (se 1 (by rfl) ⟨363743, by rfl⟩ : syracuseStep 484991 = 727487) B727487
theorem B160037963 : Blo 211809 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B4128509 : Blo 211809 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B141885407 : Blo 211809 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B1966295 : Blo 211809 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B2426111 : Blo 211809 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B919019 : Blo 211809 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B3147335 : Blo 211809 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B722735 : Blo 211809 722735 := bstep (se 1 (by rfl) ⟨542051, by rfl⟩ : syracuseStep 722735 = 1084103) B1084103
theorem B723113 : Blo 211809 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B17403659 : Blo 211809 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B725975 : Blo 211809 725975 := bstep (se 1 (by rfl) ⟨544481, by rfl⟩ : syracuseStep 725975 = 1088963) B1088963
theorem B8267437 : Blo 211809 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B1223855 : Blo 211809 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B240871 : Blo 211809 240871 := bstep (se 1 (by rfl) ⟨180653, by rfl⟩ : syracuseStep 240871 = 361307) B361307
theorem B1617893 : Blo 211809 1617893 := bstep (se 4 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 1617893 = 303355) B303355
theorem B5484995 : Blo 211809 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B1227089 : Blo 211809 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B94590271 : Blo 211809 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B515411 : Blo 211809 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B319259 : Blo 211809 319259 := bstep (se 1 (by rfl) ⟨239444, by rfl⟩ : syracuseStep 319259 = 478889) B478889
theorem B484969 : Blo 211809 484969 := bstep (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) B363727
theorem B812713 : Blo 211809 812713 := bstep (se 2 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 812713 = 609535) B609535
theorem B321695 : Blo 211809 321695 := bstep (se 1 (by rfl) ⟨241271, by rfl⟩ : syracuseStep 321695 = 482543) B482543
theorem B715769 : Blo 211809 715769 := bstep (se 2 (by rfl) ⟨268413, by rfl⟩ : syracuseStep 715769 = 536827) B536827
theorem B322919 : Blo 211809 322919 := bstep (se 1 (by rfl) ⟨242189, by rfl⟩ : syracuseStep 322919 = 484379) B484379
theorem B323327 : Blo 211809 323327 := bstep (se 1 (by rfl) ⟨242495, by rfl⟩ : syracuseStep 323327 = 484991) B484991
theorem B684281 : Blo 211809 684281 := bstep (se 2 (by rfl) ⟨256605, by rfl⟩ : syracuseStep 684281 = 513211) B513211
theorem B3634793 : Blo 211809 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B106691975 : Blo 211809 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B2752339 : Blo 211809 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B720737 : Blo 211809 720737 := bstep (se 2 (by rfl) ⟨270276, by rfl⟩ : syracuseStep 720737 = 540553) B540553
theorem B1310863 : Blo 211809 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B2098223 : Blo 211809 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B1083617 : Blo 211809 1083617 := bstep (se 2 (by rfl) ⟨406356, by rfl⟩ : syracuseStep 1083617 = 812713) B812713
theorem B11602439 : Blo 211809 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B1617407 : Blo 211809 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B343607 : Blo 211809 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B212839 : Blo 211809 212839 := bstep (se 1 (by rfl) ⟨159629, by rfl⟩ : syracuseStep 212839 = 319259) B319259
theorem B214463 : Blo 211809 214463 := bstep (se 1 (by rfl) ⟨160847, by rfl⟩ : syracuseStep 214463 = 321695) B321695
theorem B477179 : Blo 211809 477179 := bstep (se 1 (by rfl) ⟨357884, by rfl⟩ : syracuseStep 477179 = 715769) B715769
theorem B215279 : Blo 211809 215279 := bstep (se 1 (by rfl) ⟨161459, by rfl⟩ : syracuseStep 215279 = 322919) B322919
theorem B215551 : Blo 211809 215551 := bstep (se 1 (by rfl) ⟨161663, by rfl⟩ : syracuseStep 215551 = 323327) B323327
theorem B3656663 : Blo 211809 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B44092997 : Blo 211809 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B71127983 : Blo 211809 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B480491 : Blo 211809 480491 := bstep (se 1 (by rfl) ⟨360368, by rfl⟩ : syracuseStep 480491 = 720737) B720737
theorem B612679 : Blo 211809 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B481823 : Blo 211809 481823 := bstep (se 1 (by rfl) ⟨361367, by rfl⟩ : syracuseStep 481823 = 722735) B722735
theorem B482075 : Blo 211809 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B646625 : Blo 211809 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B483983 : Blo 211809 483983 := bstep (se 1 (by rfl) ⟨362987, by rfl⟩ : syracuseStep 483983 = 725975) B725975
theorem B321161 : Blo 211809 321161 := bstep (se 2 (by rfl) ⟨120435, by rfl⟩ : syracuseStep 321161 = 240871) B240871
theorem B126120361 : Blo 211809 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B815903 : Blo 211809 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B1078595 : Blo 211809 1078595 := bstep (se 1 (by rfl) ⟨808946, by rfl⟩ : syracuseStep 1078595 = 1617893) B1617893
theorem B456187 : Blo 211809 456187 := bstep (se 1 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 456187 = 684281) B684281
theorem B2423195 : Blo 211809 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B818059 : Blo 211809 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B3669785 : Blo 211809 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B722411 : Blo 211809 722411 := bstep (se 1 (by rfl) ⟨541808, by rfl⟩ : syracuseStep 722411 = 1083617) B1083617
theorem B7734959 : Blo 211809 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B29395331 : Blo 211809 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B47418655 : Blo 211809 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B431083 : Blo 211809 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B1090745 : Blo 211809 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B1615463 : Blo 211809 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B1747817 : Blo 211809 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B2437775 : Blo 211809 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B214107 : Blo 211809 214107 := bstep (se 1 (by rfl) ⟨160580, by rfl⟩ : syracuseStep 214107 = 321161) B321161
theorem B608249 : Blo 211809 608249 := bstep (se 2 (by rfl) ⟨228093, by rfl⟩ : syracuseStep 608249 = 456187) B456187
theorem B543935 : Blo 211809 543935 := bstep (se 1 (by rfl) ⟨407951, by rfl⟩ : syracuseStep 543935 = 815903) B815903
theorem B2446523 : Blo 211809 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B1398815 : Blo 211809 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B318119 : Blo 211809 318119 := bstep (se 1 (by rfl) ⟨238589, by rfl⟩ : syracuseStep 318119 = 477179) B477179
theorem B320327 : Blo 211809 320327 := bstep (se 1 (by rfl) ⟨240245, by rfl⟩ : syracuseStep 320327 = 480491) B480491
theorem B321215 : Blo 211809 321215 := bstep (se 1 (by rfl) ⟨240911, by rfl⟩ : syracuseStep 321215 = 481823) B481823
theorem B321383 : Blo 211809 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B322655 : Blo 211809 322655 := bstep (se 1 (by rfl) ⟨241991, by rfl⟩ : syracuseStep 322655 = 483983) B483983
theorem B168160481 : Blo 211809 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B1078271 : Blo 211809 1078271 := bstep (se 1 (by rfl) ⟨808703, by rfl⟩ : syracuseStep 1078271 = 1617407) B1617407
theorem B816905 : Blo 211809 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B719063 : Blo 211809 719063 := bstep (se 1 (by rfl) ⟨539297, by rfl⟩ : syracuseStep 719063 = 1078595) B1078595
theorem B916285 : Blo 211809 916285 := bstep (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) B343607
theorem B19596887 : Blo 211809 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B362623 : Blo 211809 362623 := bstep (se 1 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 362623 = 543935) B543935
theorem B727163 : Blo 211809 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B112106987 : Blo 211809 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B1221713 : Blo 211809 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B5156639 : Blo 211809 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B405499 : Blo 211809 405499 := bstep (se 1 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 405499 = 608249) B608249
theorem B932543 : Blo 211809 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B63224873 : Blo 211809 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B212079 : Blo 211809 212079 := bstep (se 1 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 212079 = 318119) B318119
theorem B213551 : Blo 211809 213551 := bstep (se 1 (by rfl) ⟨160163, by rfl⟩ : syracuseStep 213551 = 320327) B320327
theorem B214143 : Blo 211809 214143 := bstep (se 1 (by rfl) ⟨160607, by rfl⟩ : syracuseStep 214143 = 321215) B321215
theorem B214255 : Blo 211809 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B574777 : Blo 211809 574777 := bstep (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) B431083
theorem B1165211 : Blo 211809 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B215103 : Blo 211809 215103 := bstep (se 1 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 215103 = 322655) B322655
theorem B1625183 : Blo 211809 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B544603 : Blo 211809 544603 := bstep (se 1 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 544603 = 816905) B816905
theorem B479375 : Blo 211809 479375 := bstep (se 1 (by rfl) ⟨359531, by rfl⟩ : syracuseStep 479375 = 719063) B719063
theorem B481607 : Blo 211809 481607 := bstep (se 1 (by rfl) ⟨361205, by rfl⟩ : syracuseStep 481607 = 722411) B722411
theorem B1631015 : Blo 211809 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B1076975 : Blo 211809 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B718847 : Blo 211809 718847 := bstep (se 1 (by rfl) ⟨539135, by rfl⟩ : syracuseStep 718847 = 1078271) B1078271
theorem B1083455 : Blo 211809 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B726137 : Blo 211809 726137 := bstep (se 2 (by rfl) ⟨272301, by rfl⟩ : syracuseStep 726137 = 544603) B544603
theorem B1087343 : Blo 211809 1087343 := bstep (se 1 (by rfl) ⟨815507, by rfl⟩ : syracuseStep 1087343 = 1631015) B1631015
theorem B42149915 : Blo 211809 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B766369 : Blo 211809 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B540665 : Blo 211809 540665 := bstep (se 2 (by rfl) ⟨202749, by rfl⟩ : syracuseStep 540665 = 405499) B405499
theorem B479231 : Blo 211809 479231 := bstep (se 1 (by rfl) ⟨359423, by rfl⟩ : syracuseStep 479231 = 718847) B718847
theorem B13064591 : Blo 211809 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B776807 : Blo 211809 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B319583 : Blo 211809 319583 := bstep (se 1 (by rfl) ⟨239687, by rfl⟩ : syracuseStep 319583 = 479375) B479375
theorem B483497 : Blo 211809 483497 := bstep (se 2 (by rfl) ⟨181311, by rfl⟩ : syracuseStep 483497 = 362623) B362623
theorem B484775 : Blo 211809 484775 := bstep (se 1 (by rfl) ⟨363581, by rfl⟩ : syracuseStep 484775 = 727163) B727163
theorem B321071 : Blo 211809 321071 := bstep (se 1 (by rfl) ⟨240803, by rfl⟩ : syracuseStep 321071 = 481607) B481607
theorem B74737991 : Blo 211809 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B814475 : Blo 211809 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B717983 : Blo 211809 717983 := bstep (se 1 (by rfl) ⟨538487, by rfl⟩ : syracuseStep 717983 = 1076975) B1076975
theorem B3437759 : Blo 211809 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B621695 : Blo 211809 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B722303 : Blo 211809 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B724895 : Blo 211809 724895 := bstep (se 1 (by rfl) ⟨543671, by rfl⟩ : syracuseStep 724895 = 1087343) B1087343
theorem B1021825 : Blo 211809 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B213055 : Blo 211809 213055 := bstep (se 1 (by rfl) ⟨159791, by rfl⟩ : syracuseStep 213055 = 319583) B319583
theorem B214047 : Blo 211809 214047 := bstep (se 1 (by rfl) ⟨160535, by rfl⟩ : syracuseStep 214047 = 321071) B321071
theorem B28099943 : Blo 211809 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B49825327 : Blo 211809 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B542983 : Blo 211809 542983 := bstep (se 1 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 542983 = 814475) B814475
theorem B478655 : Blo 211809 478655 := bstep (se 1 (by rfl) ⟨358991, by rfl⟩ : syracuseStep 478655 = 717983) B717983
theorem B414463 : Blo 211809 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B319487 : Blo 211809 319487 := bstep (se 1 (by rfl) ⟨239615, by rfl⟩ : syracuseStep 319487 = 479231) B479231
theorem B9167357 : Blo 211809 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B484091 : Blo 211809 484091 := bstep (se 1 (by rfl) ⟨363068, by rfl⟩ : syracuseStep 484091 = 726137) B726137
theorem B8709727 : Blo 211809 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B517871 : Blo 211809 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B322331 : Blo 211809 322331 := bstep (se 1 (by rfl) ⟨241748, by rfl⟩ : syracuseStep 322331 = 483497) B483497
theorem B323183 : Blo 211809 323183 := bstep (se 1 (by rfl) ⟨242387, by rfl⟩ : syracuseStep 323183 = 484775) B484775
theorem B360443 : Blo 211809 360443 := bstep (se 1 (by rfl) ⟨270332, by rfl⟩ : syracuseStep 360443 = 540665) B540665
theorem B723977 : Blo 211809 723977 := bstep (se 2 (by rfl) ⟨271491, by rfl⟩ : syracuseStep 723977 = 542983) B542983
theorem B1380989 : Blo 211809 1380989 := bstep (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) B517871
theorem B240295 : Blo 211809 240295 := bstep (se 1 (by rfl) ⟨180221, by rfl⟩ : syracuseStep 240295 = 360443) B360443
theorem B66433769 : Blo 211809 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B11612969 : Blo 211809 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B212991 : Blo 211809 212991 := bstep (se 1 (by rfl) ⟨159743, by rfl⟩ : syracuseStep 212991 = 319487) B319487
theorem B6111571 : Blo 211809 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B214887 : Blo 211809 214887 := bstep (se 1 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 214887 = 322331) B322331
theorem B215455 : Blo 211809 215455 := bstep (se 1 (by rfl) ⟨161591, by rfl⟩ : syracuseStep 215455 = 323183) B323183
theorem B1362433 : Blo 211809 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B18733295 : Blo 211809 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B481535 : Blo 211809 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B319103 : Blo 211809 319103 := bstep (se 1 (by rfl) ⟨239327, by rfl⟩ : syracuseStep 319103 = 478655) B478655
theorem B483263 : Blo 211809 483263 := bstep (se 1 (by rfl) ⟨362447, by rfl⟩ : syracuseStep 483263 = 724895) B724895
theorem B322727 : Blo 211809 322727 := bstep (se 1 (by rfl) ⟨242045, by rfl⟩ : syracuseStep 322727 = 484091) B484091
theorem B552617 : Blo 211809 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B920659 : Blo 211809 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B368411 : Blo 211809 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B7741979 : Blo 211809 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1816577 : Blo 211809 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B212735 : Blo 211809 212735 := bstep (se 1 (by rfl) ⟨159551, by rfl⟩ : syracuseStep 212735 = 319103) B319103
theorem B49955453 : Blo 211809 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B215151 : Blo 211809 215151 := bstep (se 1 (by rfl) ⟨161363, by rfl⟩ : syracuseStep 215151 = 322727) B322727
theorem B44289179 : Blo 211809 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B8148761 : Blo 211809 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B482651 : Blo 211809 482651 := bstep (se 1 (by rfl) ⟨361988, by rfl⟩ : syracuseStep 482651 = 723977) B723977
theorem B320393 : Blo 211809 320393 := bstep (se 2 (by rfl) ⟨120147, by rfl⟩ : syracuseStep 320393 = 240295) B240295
theorem B321023 : Blo 211809 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B322175 : Blo 211809 322175 := bstep (se 1 (by rfl) ⟨241631, by rfl⟩ : syracuseStep 322175 = 483263) B483263
theorem B29526119 : Blo 211809 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B33303635 : Blo 211809 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B1227545 : Blo 211809 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B5161319 : Blo 211809 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B213595 : Blo 211809 213595 := bstep (se 1 (by rfl) ⟨160196, by rfl⟩ : syracuseStep 213595 = 320393) B320393
theorem B214015 : Blo 211809 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B214783 : Blo 211809 214783 := bstep (se 1 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 214783 = 322175) B322175
theorem B5432507 : Blo 211809 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B321767 : Blo 211809 321767 := bstep (se 1 (by rfl) ⟨241325, by rfl⟩ : syracuseStep 321767 = 482651) B482651
theorem B3929717 : Blo 211809 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B1211051 : Blo 211809 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B3440879 : Blo 211809 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B3621671 : Blo 211809 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B214511 : Blo 211809 214511 := bstep (se 1 (by rfl) ⟨160883, by rfl⟩ : syracuseStep 214511 = 321767) B321767
theorem B22202423 : Blo 211809 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B807367 : Blo 211809 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B19684079 : Blo 211809 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B2619811 : Blo 211809 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B818363 : Blo 211809 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B2293919 : Blo 211809 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B13122719 : Blo 211809 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B3493081 : Blo 211809 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B545575 : Blo 211809 545575 := bstep (se 1 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 545575 = 818363) B818363
theorem B2414447 : Blo 211809 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B14801615 : Blo 211809 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B1076489 : Blo 211809 1076489 := bstep (se 2 (by rfl) ⟨403683, by rfl⟩ : syracuseStep 1076489 = 807367) B807367
theorem B1609631 : Blo 211809 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B4657441 : Blo 211809 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B9867743 : Blo 211809 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B727433 : Blo 211809 727433 := bstep (se 2 (by rfl) ⟨272787, by rfl⟩ : syracuseStep 727433 = 545575) B545575
theorem B1529279 : Blo 211809 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B717659 : Blo 211809 717659 := bstep (se 1 (by rfl) ⟨538244, by rfl⟩ : syracuseStep 717659 = 1076489) B1076489
theorem B8748479 : Blo 211809 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B1019519 : Blo 211809 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B6209921 : Blo 211809 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B478439 : Blo 211809 478439 := bstep (se 1 (by rfl) ⟨358829, by rfl⟩ : syracuseStep 478439 = 717659) B717659
theorem B1073087 : Blo 211809 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B6578495 : Blo 211809 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B484955 : Blo 211809 484955 := bstep (se 1 (by rfl) ⟨363716, by rfl⟩ : syracuseStep 484955 = 727433) B727433
theorem B5832319 : Blo 211809 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B7776425 : Blo 211809 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B4139947 : Blo 211809 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B318959 : Blo 211809 318959 := bstep (se 1 (by rfl) ⟨239219, by rfl⟩ : syracuseStep 318959 = 478439) B478439
theorem B679679 : Blo 211809 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B715391 : Blo 211809 715391 := bstep (se 1 (by rfl) ⟨536543, by rfl⟩ : syracuseStep 715391 = 1073087) B1073087
theorem B4385663 : Blo 211809 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B323303 : Blo 211809 323303 := bstep (se 1 (by rfl) ⟨242477, by rfl⟩ : syracuseStep 323303 = 484955) B484955
theorem B5184283 : Blo 211809 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B2923775 : Blo 211809 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B5519929 : Blo 211809 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B212639 : Blo 211809 212639 := bstep (se 1 (by rfl) ⟨159479, by rfl⟩ : syracuseStep 212639 = 318959) B318959
theorem B476927 : Blo 211809 476927 := bstep (se 1 (by rfl) ⟨357695, by rfl⟩ : syracuseStep 476927 = 715391) B715391
theorem B215535 : Blo 211809 215535 := bstep (se 1 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 215535 = 323303) B323303
theorem B453119 : Blo 211809 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B1949183 : Blo 211809 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B7359905 : Blo 211809 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B317951 : Blo 211809 317951 := bstep (se 1 (by rfl) ⟨238463, by rfl⟩ : syracuseStep 317951 = 476927) B476927
theorem B1208317 : Blo 211809 1208317 := bstep (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) B453119
theorem B6912377 : Blo 211809 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B1611089 : Blo 211809 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B211967 : Blo 211809 211967 := bstep (se 1 (by rfl) ⟨158975, by rfl⟩ : syracuseStep 211967 = 317951) B317951
theorem B4608251 : Blo 211809 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B1299455 : Blo 211809 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B4906603 : Blo 211809 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B866303 : Blo 211809 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B6542137 : Blo 211809 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B3072167 : Blo 211809 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B1074059 : Blo 211809 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B2048111 : Blo 211809 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B577535 : Blo 211809 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B34891397 : Blo 211809 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B716039 : Blo 211809 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B477359 : Blo 211809 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B1365407 : Blo 211809 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B23260931 : Blo 211809 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B1540093 : Blo 211809 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B15507287 : Blo 211809 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B2053457 : Blo 211809 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B318239 : Blo 211809 318239 := bstep (se 1 (by rfl) ⟨238679, by rfl⟩ : syracuseStep 318239 = 477359) B477359
theorem B910271 : Blo 211809 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B212159 : Blo 211809 212159 := bstep (se 1 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 212159 = 318239) B318239
theorem B10338191 : Blo 211809 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B606847 : Blo 211809 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B1368971 : Blo 211809 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B6892127 : Blo 211809 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B809129 : Blo 211809 809129 := bstep (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) B606847
theorem B912647 : Blo 211809 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B4594751 : Blo 211809 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B539419 : Blo 211809 539419 := bstep (se 1 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 539419 = 809129) B809129
theorem B608431 : Blo 211809 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B3063167 : Blo 211809 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B811241 : Blo 211809 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B719225 : Blo 211809 719225 := bstep (se 2 (by rfl) ⟨269709, by rfl⟩ : syracuseStep 719225 = 539419) B539419
theorem B2042111 : Blo 211809 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B540827 : Blo 211809 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B479483 : Blo 211809 479483 := bstep (se 1 (by rfl) ⟨359612, by rfl⟩ : syracuseStep 479483 = 719225) B719225
theorem B360551 : Blo 211809 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B5445629 : Blo 211809 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B319655 : Blo 211809 319655 := bstep (se 1 (by rfl) ⟨239741, by rfl⟩ : syracuseStep 319655 = 479483) B479483
theorem B240367 : Blo 211809 240367 := bstep (se 1 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 240367 = 360551) B360551
theorem B213103 : Blo 211809 213103 := bstep (se 1 (by rfl) ⟨159827, by rfl⟩ : syracuseStep 213103 = 319655) B319655
theorem B3630419 : Blo 211809 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B320489 : Blo 211809 320489 := bstep (se 2 (by rfl) ⟨120183, by rfl⟩ : syracuseStep 320489 = 240367) B240367
theorem B2420279 : Blo 211809 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B1613519 : Blo 211809 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B213659 : Blo 211809 213659 := bstep (se 1 (by rfl) ⟨160244, by rfl⟩ : syracuseStep 213659 = 320489) B320489
theorem B1075679 : Blo 211809 1075679 := bstep (se 1 (by rfl) ⟨806759, by rfl⟩ : syracuseStep 1075679 = 1613519) B1613519
theorem B717119 : Blo 211809 717119 := bstep (se 1 (by rfl) ⟨537839, by rfl⟩ : syracuseStep 717119 = 1075679) B1075679
theorem B478079 : Blo 211809 478079 := bstep (se 1 (by rfl) ⟨358559, by rfl⟩ : syracuseStep 478079 = 717119) B717119
theorem B318719 : Blo 211809 318719 := bstep (se 1 (by rfl) ⟨239039, by rfl⟩ : syracuseStep 318719 = 478079) B478079
theorem B212479 : Blo 211809 212479 := bstep (se 1 (by rfl) ⟨159359, by rfl⟩ : syracuseStep 212479 = 318719) B318719

theorem C0 (j : ℕ) (h1 : 52952 ≤ j) (h2 : j ≤ 53651) : Blo 211809 (4 * j + 3) := by
  interval_cases j
  · exact B211811
  · exact B211815
  · exact B211819
  · exact B211823
  · exact B211827
  · exact B211831
  · exact B211835
  · exact B211839
  · exact B211843
  · exact B211847
  · exact B211851
  · exact B211855
  · exact B211859
  · exact B211863
  · exact B211867
  · exact B211871
  · exact B211875
  · exact B211879
  · exact B211883
  · exact B211887
  · exact B211891
  · exact B211895
  · exact B211899
  · exact B211903
  · exact B211907
  · exact B211911
  · exact B211915
  · exact B211919
  · exact B211923
  · exact B211927
  · exact B211931
  · exact B211935
  · exact B211939
  · exact B211943
  · exact B211947
  · exact B211951
  · exact B211955
  · exact B211959
  · exact B211963
  · exact B211967
  · exact B211971
  · exact B211975
  · exact B211979
  · exact B211983
  · exact B211987
  · exact B211991
  · exact B211995
  · exact B211999
  · exact B212003
  · exact B212007
  · exact B212011
  · exact B212015
  · exact B212019
  · exact B212023
  · exact B212027
  · exact B212031
  · exact B212035
  · exact B212039
  · exact B212043
  · exact B212047
  · exact B212051
  · exact B212055
  · exact B212059
  · exact B212063
  · exact B212067
  · exact B212071
  · exact B212075
  · exact B212079
  · exact B212083
  · exact B212087
  · exact B212091
  · exact B212095
  · exact B212099
  · exact B212103
  · exact B212107
  · exact B212111
  · exact B212115
  · exact B212119
  · exact B212123
  · exact B212127
  · exact B212131
  · exact B212135
  · exact B212139
  · exact B212143
  · exact B212147
  · exact B212151
  · exact B212155
  · exact B212159
  · exact B212163
  · exact B212167
  · exact B212171
  · exact B212175
  · exact B212179
  · exact B212183
  · exact B212187
  · exact B212191
  · exact B212195
  · exact B212199
  · exact B212203
  · exact B212207
  · exact B212211
  · exact B212215
  · exact B212219
  · exact B212223
  · exact B212227
  · exact B212231
  · exact B212235
  · exact B212239
  · exact B212243
  · exact B212247
  · exact B212251
  · exact B212255
  · exact B212259
  · exact B212263
  · exact B212267
  · exact B212271
  · exact B212275
  · exact B212279
  · exact B212283
  · exact B212287
  · exact B212291
  · exact B212295
  · exact B212299
  · exact B212303
  · exact B212307
  · exact B212311
  · exact B212315
  · exact B212319
  · exact B212323
  · exact B212327
  · exact B212331
  · exact B212335
  · exact B212339
  · exact B212343
  · exact B212347
  · exact B212351
  · exact B212355
  · exact B212359
  · exact B212363
  · exact B212367
  · exact B212371
  · exact B212375
  · exact B212379
  · exact B212383
  · exact B212387
  · exact B212391
  · exact B212395
  · exact B212399
  · exact B212403
  · exact B212407
  · exact B212411
  · exact B212415
  · exact B212419
  · exact B212423
  · exact B212427
  · exact B212431
  · exact B212435
  · exact B212439
  · exact B212443
  · exact B212447
  · exact B212451
  · exact B212455
  · exact B212459
  · exact B212463
  · exact B212467
  · exact B212471
  · exact B212475
  · exact B212479
  · exact B212483
  · exact B212487
  · exact B212491
  · exact B212495
  · exact B212499
  · exact B212503
  · exact B212507
  · exact B212511
  · exact B212515
  · exact B212519
  · exact B212523
  · exact B212527
  · exact B212531
  · exact B212535
  · exact B212539
  · exact B212543
  · exact B212547
  · exact B212551
  · exact B212555
  · exact B212559
  · exact B212563
  · exact B212567
  · exact B212571
  · exact B212575
  · exact B212579
  · exact B212583
  · exact B212587
  · exact B212591
  · exact B212595
  · exact B212599
  · exact B212603
  · exact B212607
  · exact B212611
  · exact B212615
  · exact B212619
  · exact B212623
  · exact B212627
  · exact B212631
  · exact B212635
  · exact B212639
  · exact B212643
  · exact B212647
  · exact B212651
  · exact B212655
  · exact B212659
  · exact B212663
  · exact B212667
  · exact B212671
  · exact B212675
  · exact B212679
  · exact B212683
  · exact B212687
  · exact B212691
  · exact B212695
  · exact B212699
  · exact B212703
  · exact B212707
  · exact B212711
  · exact B212715
  · exact B212719
  · exact B212723
  · exact B212727
  · exact B212731
  · exact B212735
  · exact B212739
  · exact B212743
  · exact B212747
  · exact B212751
  · exact B212755
  · exact B212759
  · exact B212763
  · exact B212767
  · exact B212771
  · exact B212775
  · exact B212779
  · exact B212783
  · exact B212787
  · exact B212791
  · exact B212795
  · exact B212799
  · exact B212803
  · exact B212807
  · exact B212811
  · exact B212815
  · exact B212819
  · exact B212823
  · exact B212827
  · exact B212831
  · exact B212835
  · exact B212839
  · exact B212843
  · exact B212847
  · exact B212851
  · exact B212855
  · exact B212859
  · exact B212863
  · exact B212867
  · exact B212871
  · exact B212875
  · exact B212879
  · exact B212883
  · exact B212887
  · exact B212891
  · exact B212895
  · exact B212899
  · exact B212903
  · exact B212907
  · exact B212911
  · exact B212915
  · exact B212919
  · exact B212923
  · exact B212927
  · exact B212931
  · exact B212935
  · exact B212939
  · exact B212943
  · exact B212947
  · exact B212951
  · exact B212955
  · exact B212959
  · exact B212963
  · exact B212967
  · exact B212971
  · exact B212975
  · exact B212979
  · exact B212983
  · exact B212987
  · exact B212991
  · exact B212995
  · exact B212999
  · exact B213003
  · exact B213007
  · exact B213011
  · exact B213015
  · exact B213019
  · exact B213023
  · exact B213027
  · exact B213031
  · exact B213035
  · exact B213039
  · exact B213043
  · exact B213047
  · exact B213051
  · exact B213055
  · exact B213059
  · exact B213063
  · exact B213067
  · exact B213071
  · exact B213075
  · exact B213079
  · exact B213083
  · exact B213087
  · exact B213091
  · exact B213095
  · exact B213099
  · exact B213103
  · exact B213107
  · exact B213111
  · exact B213115
  · exact B213119
  · exact B213123
  · exact B213127
  · exact B213131
  · exact B213135
  · exact B213139
  · exact B213143
  · exact B213147
  · exact B213151
  · exact B213155
  · exact B213159
  · exact B213163
  · exact B213167
  · exact B213171
  · exact B213175
  · exact B213179
  · exact B213183
  · exact B213187
  · exact B213191
  · exact B213195
  · exact B213199
  · exact B213203
  · exact B213207
  · exact B213211
  · exact B213215
  · exact B213219
  · exact B213223
  · exact B213227
  · exact B213231
  · exact B213235
  · exact B213239
  · exact B213243
  · exact B213247
  · exact B213251
  · exact B213255
  · exact B213259
  · exact B213263
  · exact B213267
  · exact B213271
  · exact B213275
  · exact B213279
  · exact B213283
  · exact B213287
  · exact B213291
  · exact B213295
  · exact B213299
  · exact B213303
  · exact B213307
  · exact B213311
  · exact B213315
  · exact B213319
  · exact B213323
  · exact B213327
  · exact B213331
  · exact B213335
  · exact B213339
  · exact B213343
  · exact B213347
  · exact B213351
  · exact B213355
  · exact B213359
  · exact B213363
  · exact B213367
  · exact B213371
  · exact B213375
  · exact B213379
  · exact B213383
  · exact B213387
  · exact B213391
  · exact B213395
  · exact B213399
  · exact B213403
  · exact B213407
  · exact B213411
  · exact B213415
  · exact B213419
  · exact B213423
  · exact B213427
  · exact B213431
  · exact B213435
  · exact B213439
  · exact B213443
  · exact B213447
  · exact B213451
  · exact B213455
  · exact B213459
  · exact B213463
  · exact B213467
  · exact B213471
  · exact B213475
  · exact B213479
  · exact B213483
  · exact B213487
  · exact B213491
  · exact B213495
  · exact B213499
  · exact B213503
  · exact B213507
  · exact B213511
  · exact B213515
  · exact B213519
  · exact B213523
  · exact B213527
  · exact B213531
  · exact B213535
  · exact B213539
  · exact B213543
  · exact B213547
  · exact B213551
  · exact B213555
  · exact B213559
  · exact B213563
  · exact B213567
  · exact B213571
  · exact B213575
  · exact B213579
  · exact B213583
  · exact B213587
  · exact B213591
  · exact B213595
  · exact B213599
  · exact B213603
  · exact B213607
  · exact B213611
  · exact B213615
  · exact B213619
  · exact B213623
  · exact B213627
  · exact B213631
  · exact B213635
  · exact B213639
  · exact B213643
  · exact B213647
  · exact B213651
  · exact B213655
  · exact B213659
  · exact B213663
  · exact B213667
  · exact B213671
  · exact B213675
  · exact B213679
  · exact B213683
  · exact B213687
  · exact B213691
  · exact B213695
  · exact B213699
  · exact B213703
  · exact B213707
  · exact B213711
  · exact B213715
  · exact B213719
  · exact B213723
  · exact B213727
  · exact B213731
  · exact B213735
  · exact B213739
  · exact B213743
  · exact B213747
  · exact B213751
  · exact B213755
  · exact B213759
  · exact B213763
  · exact B213767
  · exact B213771
  · exact B213775
  · exact B213779
  · exact B213783
  · exact B213787
  · exact B213791
  · exact B213795
  · exact B213799
  · exact B213803
  · exact B213807
  · exact B213811
  · exact B213815
  · exact B213819
  · exact B213823
  · exact B213827
  · exact B213831
  · exact B213835
  · exact B213839
  · exact B213843
  · exact B213847
  · exact B213851
  · exact B213855
  · exact B213859
  · exact B213863
  · exact B213867
  · exact B213871
  · exact B213875
  · exact B213879
  · exact B213883
  · exact B213887
  · exact B213891
  · exact B213895
  · exact B213899
  · exact B213903
  · exact B213907
  · exact B213911
  · exact B213915
  · exact B213919
  · exact B213923
  · exact B213927
  · exact B213931
  · exact B213935
  · exact B213939
  · exact B213943
  · exact B213947
  · exact B213951
  · exact B213955
  · exact B213959
  · exact B213963
  · exact B213967
  · exact B213971
  · exact B213975
  · exact B213979
  · exact B213983
  · exact B213987
  · exact B213991
  · exact B213995
  · exact B213999
  · exact B214003
  · exact B214007
  · exact B214011
  · exact B214015
  · exact B214019
  · exact B214023
  · exact B214027
  · exact B214031
  · exact B214035
  · exact B214039
  · exact B214043
  · exact B214047
  · exact B214051
  · exact B214055
  · exact B214059
  · exact B214063
  · exact B214067
  · exact B214071
  · exact B214075
  · exact B214079
  · exact B214083
  · exact B214087
  · exact B214091
  · exact B214095
  · exact B214099
  · exact B214103
  · exact B214107
  · exact B214111
  · exact B214115
  · exact B214119
  · exact B214123
  · exact B214127
  · exact B214131
  · exact B214135
  · exact B214139
  · exact B214143
  · exact B214147
  · exact B214151
  · exact B214155
  · exact B214159
  · exact B214163
  · exact B214167
  · exact B214171
  · exact B214175
  · exact B214179
  · exact B214183
  · exact B214187
  · exact B214191
  · exact B214195
  · exact B214199
  · exact B214203
  · exact B214207
  · exact B214211
  · exact B214215
  · exact B214219
  · exact B214223
  · exact B214227
  · exact B214231
  · exact B214235
  · exact B214239
  · exact B214243
  · exact B214247
  · exact B214251
  · exact B214255
  · exact B214259
  · exact B214263
  · exact B214267
  · exact B214271
  · exact B214275
  · exact B214279
  · exact B214283
  · exact B214287
  · exact B214291
  · exact B214295
  · exact B214299
  · exact B214303
  · exact B214307
  · exact B214311
  · exact B214315
  · exact B214319
  · exact B214323
  · exact B214327
  · exact B214331
  · exact B214335
  · exact B214339
  · exact B214343
  · exact B214347
  · exact B214351
  · exact B214355
  · exact B214359
  · exact B214363
  · exact B214367
  · exact B214371
  · exact B214375
  · exact B214379
  · exact B214383
  · exact B214387
  · exact B214391
  · exact B214395
  · exact B214399
  · exact B214403
  · exact B214407
  · exact B214411
  · exact B214415
  · exact B214419
  · exact B214423
  · exact B214427
  · exact B214431
  · exact B214435
  · exact B214439
  · exact B214443
  · exact B214447
  · exact B214451
  · exact B214455
  · exact B214459
  · exact B214463
  · exact B214467
  · exact B214471
  · exact B214475
  · exact B214479
  · exact B214483
  · exact B214487
  · exact B214491
  · exact B214495
  · exact B214499
  · exact B214503
  · exact B214507
  · exact B214511
  · exact B214515
  · exact B214519
  · exact B214523
  · exact B214527
  · exact B214531
  · exact B214535
  · exact B214539
  · exact B214543
  · exact B214547
  · exact B214551
  · exact B214555
  · exact B214559
  · exact B214563
  · exact B214567
  · exact B214571
  · exact B214575
  · exact B214579
  · exact B214583
  · exact B214587
  · exact B214591
  · exact B214595
  · exact B214599
  · exact B214603
  · exact B214607

theorem C1 (j : ℕ) (h1 : 53652 ≤ j) (h2 : j ≤ 53951) : Blo 211809 (4 * j + 3) := by
  interval_cases j
  · exact B214611
  · exact B214615
  · exact B214619
  · exact B214623
  · exact B214627
  · exact B214631
  · exact B214635
  · exact B214639
  · exact B214643
  · exact B214647
  · exact B214651
  · exact B214655
  · exact B214659
  · exact B214663
  · exact B214667
  · exact B214671
  · exact B214675
  · exact B214679
  · exact B214683
  · exact B214687
  · exact B214691
  · exact B214695
  · exact B214699
  · exact B214703
  · exact B214707
  · exact B214711
  · exact B214715
  · exact B214719
  · exact B214723
  · exact B214727
  · exact B214731
  · exact B214735
  · exact B214739
  · exact B214743
  · exact B214747
  · exact B214751
  · exact B214755
  · exact B214759
  · exact B214763
  · exact B214767
  · exact B214771
  · exact B214775
  · exact B214779
  · exact B214783
  · exact B214787
  · exact B214791
  · exact B214795
  · exact B214799
  · exact B214803
  · exact B214807
  · exact B214811
  · exact B214815
  · exact B214819
  · exact B214823
  · exact B214827
  · exact B214831
  · exact B214835
  · exact B214839
  · exact B214843
  · exact B214847
  · exact B214851
  · exact B214855
  · exact B214859
  · exact B214863
  · exact B214867
  · exact B214871
  · exact B214875
  · exact B214879
  · exact B214883
  · exact B214887
  · exact B214891
  · exact B214895
  · exact B214899
  · exact B214903
  · exact B214907
  · exact B214911
  · exact B214915
  · exact B214919
  · exact B214923
  · exact B214927
  · exact B214931
  · exact B214935
  · exact B214939
  · exact B214943
  · exact B214947
  · exact B214951
  · exact B214955
  · exact B214959
  · exact B214963
  · exact B214967
  · exact B214971
  · exact B214975
  · exact B214979
  · exact B214983
  · exact B214987
  · exact B214991
  · exact B214995
  · exact B214999
  · exact B215003
  · exact B215007
  · exact B215011
  · exact B215015
  · exact B215019
  · exact B215023
  · exact B215027
  · exact B215031
  · exact B215035
  · exact B215039
  · exact B215043
  · exact B215047
  · exact B215051
  · exact B215055
  · exact B215059
  · exact B215063
  · exact B215067
  · exact B215071
  · exact B215075
  · exact B215079
  · exact B215083
  · exact B215087
  · exact B215091
  · exact B215095
  · exact B215099
  · exact B215103
  · exact B215107
  · exact B215111
  · exact B215115
  · exact B215119
  · exact B215123
  · exact B215127
  · exact B215131
  · exact B215135
  · exact B215139
  · exact B215143
  · exact B215147
  · exact B215151
  · exact B215155
  · exact B215159
  · exact B215163
  · exact B215167
  · exact B215171
  · exact B215175
  · exact B215179
  · exact B215183
  · exact B215187
  · exact B215191
  · exact B215195
  · exact B215199
  · exact B215203
  · exact B215207
  · exact B215211
  · exact B215215
  · exact B215219
  · exact B215223
  · exact B215227
  · exact B215231
  · exact B215235
  · exact B215239
  · exact B215243
  · exact B215247
  · exact B215251
  · exact B215255
  · exact B215259
  · exact B215263
  · exact B215267
  · exact B215271
  · exact B215275
  · exact B215279
  · exact B215283
  · exact B215287
  · exact B215291
  · exact B215295
  · exact B215299
  · exact B215303
  · exact B215307
  · exact B215311
  · exact B215315
  · exact B215319
  · exact B215323
  · exact B215327
  · exact B215331
  · exact B215335
  · exact B215339
  · exact B215343
  · exact B215347
  · exact B215351
  · exact B215355
  · exact B215359
  · exact B215363
  · exact B215367
  · exact B215371
  · exact B215375
  · exact B215379
  · exact B215383
  · exact B215387
  · exact B215391
  · exact B215395
  · exact B215399
  · exact B215403
  · exact B215407
  · exact B215411
  · exact B215415
  · exact B215419
  · exact B215423
  · exact B215427
  · exact B215431
  · exact B215435
  · exact B215439
  · exact B215443
  · exact B215447
  · exact B215451
  · exact B215455
  · exact B215459
  · exact B215463
  · exact B215467
  · exact B215471
  · exact B215475
  · exact B215479
  · exact B215483
  · exact B215487
  · exact B215491
  · exact B215495
  · exact B215499
  · exact B215503
  · exact B215507
  · exact B215511
  · exact B215515
  · exact B215519
  · exact B215523
  · exact B215527
  · exact B215531
  · exact B215535
  · exact B215539
  · exact B215543
  · exact B215547
  · exact B215551
  · exact B215555
  · exact B215559
  · exact B215563
  · exact B215567
  · exact B215571
  · exact B215575
  · exact B215579
  · exact B215583
  · exact B215587
  · exact B215591
  · exact B215595
  · exact B215599
  · exact B215603
  · exact B215607
  · exact B215611
  · exact B215615
  · exact B215619
  · exact B215623
  · exact B215627
  · exact B215631
  · exact B215635
  · exact B215639
  · exact B215643
  · exact B215647
  · exact B215651
  · exact B215655
  · exact B215659
  · exact B215663
  · exact B215667
  · exact B215671
  · exact B215675
  · exact B215679
  · exact B215683
  · exact B215687
  · exact B215691
  · exact B215695
  · exact B215699
  · exact B215703
  · exact B215707
  · exact B215711
  · exact B215715
  · exact B215719
  · exact B215723
  · exact B215727
  · exact B215731
  · exact B215735
  · exact B215739
  · exact B215743
  · exact B215747
  · exact B215751
  · exact B215755
  · exact B215759
  · exact B215763
  · exact B215767
  · exact B215771
  · exact B215775
  · exact B215779
  · exact B215783
  · exact B215787
  · exact B215791
  · exact B215795
  · exact B215799
  · exact B215803
  · exact B215807

theorem solution (m : ℕ) (hlo : 211809 ≤ m) (hhi : m ≤ 215809) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 52952 ≤ j := by omega
    have hj2 : j ≤ 53951 := by omega
    have hb : Blo 211809 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 53652 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
