-- Prove2me | solution 1 for syracuse_descends_range_155795_159795
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:41.14308+00:00
-- url     : https://prove2.me/submissions/dbc6ee25-0611-46d1-af51-6f750aeeb90e

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


theorem B983125 : Blo 155795 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B557237 : Blo 155795 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B197245 : Blo 155795 197245 := bbase (se 3 (by rfl) ⟨36983, by rfl⟩ : syracuseStep 197245 = 73967) (by norm_num)
theorem B361117 : Blo 155795 361117 := bbase (se 3 (by rfl) ⟨67709, by rfl⟩ : syracuseStep 361117 = 135419) (by norm_num)
theorem B197417 : Blo 155795 197417 := bbase (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) (by norm_num)
theorem B262973 : Blo 155795 262973 := bbase (se 3 (by rfl) ⟨49307, by rfl⟩ : syracuseStep 262973 = 98615) (by norm_num)
theorem B197473 : Blo 155795 197473 := bbase (se 2 (by rfl) ⟨74052, by rfl⟩ : syracuseStep 197473 = 148105) (by norm_num)
theorem B1147765 : Blo 155795 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B263101 : Blo 155795 263101 := bbase (se 3 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 263101 = 98663) (by norm_num)
theorem B197569 : Blo 155795 197569 := bbase (se 2 (by rfl) ⟨74088, by rfl⟩ : syracuseStep 197569 = 148177) (by norm_num)
theorem B263189 : Blo 155795 263189 := bbase (se 6 (by rfl) ⟨6168, by rfl⟩ : syracuseStep 263189 = 12337) (by norm_num)
theorem B197741 : Blo 155795 197741 := bbase (se 3 (by rfl) ⟨37076, by rfl⟩ : syracuseStep 197741 = 74153) (by norm_num)
theorem B263317 : Blo 155795 263317 := bbase (se 6 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 263317 = 12343) (by norm_num)
theorem B197797 : Blo 155795 197797 := bbase (se 4 (by rfl) ⟨18543, by rfl⟩ : syracuseStep 197797 = 37087) (by norm_num)
theorem B394429 : Blo 155795 394429 := bbase (se 3 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 394429 = 147911) (by norm_num)
theorem B296149 : Blo 155795 296149 := bbase (se 7 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 296149 = 6941) (by norm_num)
theorem B263405 : Blo 155795 263405 := bbase (se 3 (by rfl) ⟨49388, by rfl⟩ : syracuseStep 263405 = 98777) (by norm_num)
theorem B197893 : Blo 155795 197893 := bbase (se 4 (by rfl) ⟨18552, by rfl⟩ : syracuseStep 197893 = 37105) (by norm_num)
theorem B394541 : Blo 155795 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B296293 : Blo 155795 296293 := bbase (se 4 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 296293 = 55555) (by norm_num)
theorem B263533 : Blo 155795 263533 := bbase (se 3 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 263533 = 98825) (by norm_num)
theorem B198065 : Blo 155795 198065 := bbase (se 2 (by rfl) ⟨74274, by rfl⟩ : syracuseStep 198065 = 148549) (by norm_num)
theorem B263621 : Blo 155795 263621 := bbase (se 4 (by rfl) ⟨24714, by rfl⟩ : syracuseStep 263621 = 49429) (by norm_num)
theorem B198121 : Blo 155795 198121 := bbase (se 2 (by rfl) ⟨74295, by rfl⟩ : syracuseStep 198121 = 148591) (by norm_num)
theorem B394733 : Blo 155795 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B296453 : Blo 155795 296453 := bbase (se 4 (by rfl) ⟨27792, by rfl⟩ : syracuseStep 296453 = 55585) (by norm_num)
theorem B263749 : Blo 155795 263749 := bbase (se 4 (by rfl) ⟨24726, by rfl⟩ : syracuseStep 263749 = 49453) (by norm_num)
theorem B198217 : Blo 155795 198217 := bbase (se 2 (by rfl) ⟨74331, by rfl⟩ : syracuseStep 198217 = 148663) (by norm_num)
theorem B296597 : Blo 155795 296597 := bbase (se 6 (by rfl) ⟨6951, by rfl⟩ : syracuseStep 296597 = 13903) (by norm_num)
theorem B263837 : Blo 155795 263837 := bbase (se 3 (by rfl) ⟨49469, by rfl⟩ : syracuseStep 263837 = 98939) (by norm_num)
theorem B198389 : Blo 155795 198389 := bbase (se 5 (by rfl) ⟨9299, by rfl⟩ : syracuseStep 198389 = 18599) (by norm_num)
theorem B263965 : Blo 155795 263965 := bbase (se 3 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 263965 = 98987) (by norm_num)
theorem B198445 : Blo 155795 198445 := bbase (se 3 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 198445 = 74417) (by norm_num)
theorem B362285 : Blo 155795 362285 := bbase (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) (by norm_num)
theorem B395077 : Blo 155795 395077 := bbase (se 4 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 395077 = 74077) (by norm_num)
theorem B264053 : Blo 155795 264053 := bbase (se 5 (by rfl) ⟨12377, by rfl⟩ : syracuseStep 264053 = 24755) (by norm_num)
theorem B198541 : Blo 155795 198541 := bbase (se 3 (by rfl) ⟨37226, by rfl⟩ : syracuseStep 198541 = 74453) (by norm_num)
theorem B526229 : Blo 155795 526229 := bbase (se 6 (by rfl) ⟨12333, by rfl⟩ : syracuseStep 526229 = 24667) (by norm_num)
theorem B395189 : Blo 155795 395189 := bbase (se 5 (by rfl) ⟨18524, by rfl⟩ : syracuseStep 395189 = 37049) (by norm_num)
theorem B296885 : Blo 155795 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B264181 : Blo 155795 264181 := bbase (se 5 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 264181 = 24767) (by norm_num)
theorem B198713 : Blo 155795 198713 := bbase (se 2 (by rfl) ⟨74517, by rfl⟩ : syracuseStep 198713 = 149035) (by norm_num)
theorem B297037 : Blo 155795 297037 := bbase (se 3 (by rfl) ⟨55694, by rfl⟩ : syracuseStep 297037 = 111389) (by norm_num)
theorem B264269 : Blo 155795 264269 := bbase (se 3 (by rfl) ⟨49550, by rfl⟩ : syracuseStep 264269 = 99101) (by norm_num)
theorem B362573 : Blo 155795 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B198769 : Blo 155795 198769 := bbase (se 2 (by rfl) ⟨74538, by rfl⟩ : syracuseStep 198769 = 149077) (by norm_num)
theorem B395381 : Blo 155795 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B592069 : Blo 155795 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B264397 : Blo 155795 264397 := bbase (se 3 (by rfl) ⟨49574, by rfl⟩ : syracuseStep 264397 = 99149) (by norm_num)
theorem B198865 : Blo 155795 198865 := bbase (se 2 (by rfl) ⟨74574, by rfl⟩ : syracuseStep 198865 = 149149) (by norm_num)
theorem B264485 : Blo 155795 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B526661 : Blo 155795 526661 := bbase (se 4 (by rfl) ⟨49374, by rfl⟩ : syracuseStep 526661 = 98749) (by norm_num)
theorem B1509749 : Blo 155795 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B297341 : Blo 155795 297341 := bbase (se 3 (by rfl) ⟨55751, by rfl⟩ : syracuseStep 297341 = 111503) (by norm_num)
theorem B199037 : Blo 155795 199037 := bbase (se 3 (by rfl) ⟨37319, by rfl⟩ : syracuseStep 199037 = 74639) (by norm_num)
theorem B264613 : Blo 155795 264613 := bbase (se 4 (by rfl) ⟨24807, by rfl⟩ : syracuseStep 264613 = 49615) (by norm_num)
theorem B199093 : Blo 155795 199093 := bbase (se 5 (by rfl) ⟨9332, by rfl⟩ : syracuseStep 199093 = 18665) (by norm_num)
theorem B395725 : Blo 155795 395725 := bbase (se 3 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 395725 = 148397) (by norm_num)
theorem B592373 : Blo 155795 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B264701 : Blo 155795 264701 := bbase (se 3 (by rfl) ⟨49631, by rfl⟩ : syracuseStep 264701 = 99263) (by norm_num)
theorem B166417 : Blo 155795 166417 := bbase (se 2 (by rfl) ⟨62406, by rfl⟩ : syracuseStep 166417 = 124813) (by norm_num)
theorem B199189 : Blo 155795 199189 := bbase (se 6 (by rfl) ⟨4668, by rfl⟩ : syracuseStep 199189 = 9337) (by norm_num)
theorem B395837 : Blo 155795 395837 := bbase (se 3 (by rfl) ⟨74219, by rfl⟩ : syracuseStep 395837 = 148439) (by norm_num)
theorem B264829 : Blo 155795 264829 := bbase (se 3 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 264829 = 99311) (by norm_num)
theorem B166537 : Blo 155795 166537 := bbase (se 2 (by rfl) ⟨62451, by rfl⟩ : syracuseStep 166537 = 124903) (by norm_num)
theorem B199361 : Blo 155795 199361 := bbase (se 2 (by rfl) ⟨74760, by rfl⟩ : syracuseStep 199361 = 149521) (by norm_num)
theorem B264917 : Blo 155795 264917 := bbase (se 7 (by rfl) ⟨3104, by rfl⟩ : syracuseStep 264917 = 6209) (by norm_num)
theorem B527093 : Blo 155795 527093 := bbase (se 5 (by rfl) ⟨24707, by rfl⟩ : syracuseStep 527093 = 49415) (by norm_num)
theorem B199417 : Blo 155795 199417 := bbase (se 2 (by rfl) ⟨74781, by rfl⟩ : syracuseStep 199417 = 149563) (by norm_num)
theorem B396029 : Blo 155795 396029 := bbase (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) (by norm_num)
theorem B265045 : Blo 155795 265045 := bbase (se 9 (by rfl) ⟨776, by rfl⟩ : syracuseStep 265045 = 1553) (by norm_num)
theorem B199513 : Blo 155795 199513 := bbase (se 2 (by rfl) ⟨74817, by rfl⟩ : syracuseStep 199513 = 149635) (by norm_num)
theorem B166789 : Blo 155795 166789 := bbase (se 4 (by rfl) ⟨15636, by rfl⟩ : syracuseStep 166789 = 31273) (by norm_num)
theorem B166793 : Blo 155795 166793 := bbase (se 2 (by rfl) ⟨62547, by rfl⟩ : syracuseStep 166793 = 125095) (by norm_num)
theorem B265133 : Blo 155795 265133 := bbase (se 3 (by rfl) ⟨49712, by rfl⟩ : syracuseStep 265133 = 99425) (by norm_num)
theorem B199685 : Blo 155795 199685 := bbase (se 4 (by rfl) ⟨18720, by rfl⟩ : syracuseStep 199685 = 37441) (by norm_num)
theorem B265261 : Blo 155795 265261 := bbase (se 3 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 265261 = 99473) (by norm_num)
theorem B199741 : Blo 155795 199741 := bbase (se 3 (by rfl) ⟨37451, by rfl⟩ : syracuseStep 199741 = 74903) (by norm_num)
theorem B396373 : Blo 155795 396373 := bbase (se 8 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 396373 = 4645) (by norm_num)
theorem B1346645 : Blo 155795 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B298093 : Blo 155795 298093 := bbase (se 3 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 298093 = 111785) (by norm_num)
theorem B265349 : Blo 155795 265349 := bbase (se 4 (by rfl) ⟨24876, by rfl⟩ : syracuseStep 265349 = 49753) (by norm_num)
theorem B199837 : Blo 155795 199837 := bbase (se 3 (by rfl) ⟨37469, by rfl⟩ : syracuseStep 199837 = 74939) (by norm_num)
theorem B527525 : Blo 155795 527525 := bbase (se 4 (by rfl) ⟨49455, by rfl⟩ : syracuseStep 527525 = 98911) (by norm_num)
theorem B724133 : Blo 155795 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B396485 : Blo 155795 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B789749 : Blo 155795 789749 := bbase (se 5 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 789749 = 74039) (by norm_num)
theorem B298237 : Blo 155795 298237 := bbase (se 3 (by rfl) ⟨55919, by rfl⟩ : syracuseStep 298237 = 111839) (by norm_num)
theorem B265477 : Blo 155795 265477 := bbase (se 4 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 265477 = 49777) (by norm_num)
theorem B200009 : Blo 155795 200009 := bbase (se 2 (by rfl) ⟨75003, by rfl⟩ : syracuseStep 200009 = 150007) (by norm_num)
theorem B265565 : Blo 155795 265565 := bbase (se 3 (by rfl) ⟨49793, by rfl⟩ : syracuseStep 265565 = 99587) (by norm_num)
theorem B200065 : Blo 155795 200065 := bbase (se 2 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 200065 = 150049) (by norm_num)
theorem B396677 : Blo 155795 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B298397 : Blo 155795 298397 := bbase (se 3 (by rfl) ⟨55949, by rfl⟩ : syracuseStep 298397 = 111899) (by norm_num)
theorem B167357 : Blo 155795 167357 := bbase (se 3 (by rfl) ⟨31379, by rfl⟩ : syracuseStep 167357 = 62759) (by norm_num)
theorem B265693 : Blo 155795 265693 := bbase (se 3 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 265693 = 99635) (by norm_num)
theorem B200161 : Blo 155795 200161 := bbase (se 2 (by rfl) ⟨75060, by rfl⟩ : syracuseStep 200161 = 150121) (by norm_num)
theorem B1379861 : Blo 155795 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B298541 : Blo 155795 298541 := bbase (se 3 (by rfl) ⟨55976, by rfl⟩ : syracuseStep 298541 = 111953) (by norm_num)
theorem B265781 : Blo 155795 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B527957 : Blo 155795 527957 := bbase (se 8 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 527957 = 6187) (by norm_num)
theorem B167545 : Blo 155795 167545 := bbase (se 2 (by rfl) ⟨62829, by rfl⟩ : syracuseStep 167545 = 125659) (by norm_num)
theorem B200333 : Blo 155795 200333 := bbase (se 3 (by rfl) ⟨37562, by rfl⟩ : syracuseStep 200333 = 75125) (by norm_num)
theorem B265909 : Blo 155795 265909 := bbase (se 5 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 265909 = 24929) (by norm_num)
theorem B200389 : Blo 155795 200389 := bbase (se 4 (by rfl) ⟨18786, by rfl⟩ : syracuseStep 200389 = 37573) (by norm_num)
theorem B397021 : Blo 155795 397021 := bbase (se 3 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 397021 = 148883) (by norm_num)
theorem B429797 : Blo 155795 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B265997 : Blo 155795 265997 := bbase (se 3 (by rfl) ⟨49874, by rfl⟩ : syracuseStep 265997 = 99749) (by norm_num)
theorem B200485 : Blo 155795 200485 := bbase (se 4 (by rfl) ⟨18795, by rfl⟩ : syracuseStep 200485 = 37591) (by norm_num)
theorem B397133 : Blo 155795 397133 := bbase (se 3 (by rfl) ⟨74462, by rfl⟩ : syracuseStep 397133 = 148925) (by norm_num)
theorem B298829 : Blo 155795 298829 := bbase (se 3 (by rfl) ⟨56030, by rfl⟩ : syracuseStep 298829 = 112061) (by norm_num)
theorem B266069 : Blo 155795 266069 := bbase (se 9 (by rfl) ⟨779, by rfl⟩ : syracuseStep 266069 = 1559) (by norm_num)
theorem B266125 : Blo 155795 266125 := bbase (se 3 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 266125 = 99797) (by norm_num)
theorem B200657 : Blo 155795 200657 := bbase (se 2 (by rfl) ⟨75246, by rfl⟩ : syracuseStep 200657 = 150493) (by norm_num)
theorem B298981 : Blo 155795 298981 := bbase (se 4 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 298981 = 56059) (by norm_num)
theorem B266213 : Blo 155795 266213 := bbase (se 4 (by rfl) ⟨24957, by rfl⟩ : syracuseStep 266213 = 49915) (by norm_num)
theorem B528389 : Blo 155795 528389 := bbase (se 4 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 528389 = 99073) (by norm_num)
theorem B200713 : Blo 155795 200713 := bbase (se 2 (by rfl) ⟨75267, by rfl⟩ : syracuseStep 200713 = 150535) (by norm_num)
theorem B397325 : Blo 155795 397325 := bbase (se 3 (by rfl) ⟨74498, by rfl⟩ : syracuseStep 397325 = 148997) (by norm_num)
theorem B757781 : Blo 155795 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B266341 : Blo 155795 266341 := bbase (se 4 (by rfl) ⟨24969, by rfl⟩ : syracuseStep 266341 = 49939) (by norm_num)
theorem B200809 : Blo 155795 200809 := bbase (se 2 (by rfl) ⟨75303, by rfl⟩ : syracuseStep 200809 = 150607) (by norm_num)
theorem B266429 : Blo 155795 266429 := bbase (se 3 (by rfl) ⟨49955, by rfl⟩ : syracuseStep 266429 = 99911) (by norm_num)
theorem B233693 : Blo 155795 233693 := bbase (se 3 (by rfl) ⟨43817, by rfl⟩ : syracuseStep 233693 = 87635) (by norm_num)
theorem B233717 : Blo 155795 233717 := bbase (se 5 (by rfl) ⟨10955, by rfl⟩ : syracuseStep 233717 = 21911) (by norm_num)
theorem B233741 : Blo 155795 233741 := bbase (se 3 (by rfl) ⟨43826, by rfl⟩ : syracuseStep 233741 = 87653) (by norm_num)
theorem B299285 : Blo 155795 299285 := bbase (se 6 (by rfl) ⟨7014, by rfl⟩ : syracuseStep 299285 = 14029) (by norm_num)
theorem B200981 : Blo 155795 200981 := bbase (se 6 (by rfl) ⟨4710, by rfl⟩ : syracuseStep 200981 = 9421) (by norm_num)
theorem B233765 : Blo 155795 233765 := bbase (se 4 (by rfl) ⟨21915, by rfl⟩ : syracuseStep 233765 = 43831) (by norm_num)
theorem B233789 : Blo 155795 233789 := bbase (se 3 (by rfl) ⟨43835, by rfl⟩ : syracuseStep 233789 = 87671) (by norm_num)
theorem B266557 : Blo 155795 266557 := bbase (se 3 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 266557 = 99959) (by norm_num)
theorem B201037 : Blo 155795 201037 := bbase (se 3 (by rfl) ⟨37694, by rfl⟩ : syracuseStep 201037 = 75389) (by norm_num)
theorem B233813 : Blo 155795 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B397669 : Blo 155795 397669 := bbase (se 4 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 397669 = 74563) (by norm_num)
theorem B233837 : Blo 155795 233837 := bbase (se 3 (by rfl) ⟨43844, by rfl⟩ : syracuseStep 233837 = 87689) (by norm_num)
theorem B233861 : Blo 155795 233861 := bbase (se 4 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 233861 = 43849) (by norm_num)
theorem B266645 : Blo 155795 266645 := bbase (se 6 (by rfl) ⟨6249, by rfl⟩ : syracuseStep 266645 = 12499) (by norm_num)
theorem B233885 : Blo 155795 233885 := bbase (se 3 (by rfl) ⟨43853, by rfl⟩ : syracuseStep 233885 = 87707) (by norm_num)
theorem B168365 : Blo 155795 168365 := bbase (se 3 (by rfl) ⟨31568, by rfl⟩ : syracuseStep 168365 = 63137) (by norm_num)
theorem B201133 : Blo 155795 201133 := bbase (se 3 (by rfl) ⟨37712, by rfl⟩ : syracuseStep 201133 = 75425) (by norm_num)
theorem B233909 : Blo 155795 233909 := bbase (se 5 (by rfl) ⟨10964, by rfl⟩ : syracuseStep 233909 = 21929) (by norm_num)
theorem B528821 : Blo 155795 528821 := bbase (se 5 (by rfl) ⟨24788, by rfl⟩ : syracuseStep 528821 = 49577) (by norm_num)
theorem B233933 : Blo 155795 233933 := bbase (se 3 (by rfl) ⟨43862, by rfl⟩ : syracuseStep 233933 = 87725) (by norm_num)
theorem B397781 : Blo 155795 397781 := bbase (se 7 (by rfl) ⟨4661, by rfl⟩ : syracuseStep 397781 = 9323) (by norm_num)
theorem B233957 : Blo 155795 233957 := bbase (se 4 (by rfl) ⟨21933, by rfl⟩ : syracuseStep 233957 = 43867) (by norm_num)
theorem B233981 : Blo 155795 233981 := bbase (se 3 (by rfl) ⟨43871, by rfl⟩ : syracuseStep 233981 = 87743) (by norm_num)
theorem B791045 : Blo 155795 791045 := bbase (se 4 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 791045 = 148321) (by norm_num)
theorem B234005 : Blo 155795 234005 := bbase (se 6 (by rfl) ⟨5484, by rfl⟩ : syracuseStep 234005 = 10969) (by norm_num)
theorem B266773 : Blo 155795 266773 := bbase (se 6 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 266773 = 12505) (by norm_num)
theorem B234029 : Blo 155795 234029 := bbase (se 3 (by rfl) ⟨43880, by rfl⟩ : syracuseStep 234029 = 87761) (by norm_num)
theorem B594485 : Blo 155795 594485 := bbase (se 5 (by rfl) ⟨27866, by rfl⟩ : syracuseStep 594485 = 55733) (by norm_num)
theorem B234053 : Blo 155795 234053 := bbase (se 4 (by rfl) ⟨21942, by rfl⟩ : syracuseStep 234053 = 43885) (by norm_num)
theorem B201305 : Blo 155795 201305 := bbase (se 2 (by rfl) ⟨75489, by rfl⟩ : syracuseStep 201305 = 150979) (by norm_num)
theorem B234077 : Blo 155795 234077 := bbase (se 3 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 234077 = 87779) (by norm_num)
theorem B266861 : Blo 155795 266861 := bbase (se 3 (by rfl) ⟨50036, by rfl⟩ : syracuseStep 266861 = 100073) (by norm_num)
theorem B234101 : Blo 155795 234101 := bbase (se 5 (by rfl) ⟨10973, by rfl⟩ : syracuseStep 234101 = 21947) (by norm_num)
theorem B234125 : Blo 155795 234125 := bbase (se 3 (by rfl) ⟨43898, by rfl⟩ : syracuseStep 234125 = 87797) (by norm_num)
theorem B332429 : Blo 155795 332429 := bbase (se 3 (by rfl) ⟨62330, by rfl⟩ : syracuseStep 332429 = 124661) (by norm_num)
theorem B201361 : Blo 155795 201361 := bbase (se 2 (by rfl) ⟨75510, by rfl⟩ : syracuseStep 201361 = 151021) (by norm_num)
theorem B397973 : Blo 155795 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B234149 : Blo 155795 234149 := bbase (se 4 (by rfl) ⟨21951, by rfl⟩ : syracuseStep 234149 = 43903) (by norm_num)
theorem B234173 : Blo 155795 234173 := bbase (se 3 (by rfl) ⟨43907, by rfl⟩ : syracuseStep 234173 = 87815) (by norm_num)
theorem B234197 : Blo 155795 234197 := bbase (se 7 (by rfl) ⟨2744, by rfl⟩ : syracuseStep 234197 = 5489) (by norm_num)
theorem B234221 : Blo 155795 234221 := bbase (se 3 (by rfl) ⟨43916, by rfl⟩ : syracuseStep 234221 = 87833) (by norm_num)
theorem B266989 : Blo 155795 266989 := bbase (se 3 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 266989 = 100121) (by norm_num)
theorem B201457 : Blo 155795 201457 := bbase (se 2 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 201457 = 151093) (by norm_num)
theorem B234245 : Blo 155795 234245 := bbase (se 4 (by rfl) ⟨21960, by rfl⟩ : syracuseStep 234245 = 43921) (by norm_num)
theorem B234269 : Blo 155795 234269 := bbase (se 3 (by rfl) ⟨43925, by rfl⟩ : syracuseStep 234269 = 87851) (by norm_num)
theorem B234293 : Blo 155795 234293 := bbase (se 5 (by rfl) ⟨10982, by rfl⟩ : syracuseStep 234293 = 21965) (by norm_num)
theorem B267077 : Blo 155795 267077 := bbase (se 4 (by rfl) ⟨25038, by rfl⟩ : syracuseStep 267077 = 50077) (by norm_num)
theorem B234317 : Blo 155795 234317 := bbase (se 3 (by rfl) ⟨43934, by rfl⟩ : syracuseStep 234317 = 87869) (by norm_num)
theorem B594773 : Blo 155795 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B234341 : Blo 155795 234341 := bbase (se 4 (by rfl) ⟨21969, by rfl⟩ : syracuseStep 234341 = 43939) (by norm_num)
theorem B529253 : Blo 155795 529253 := bbase (se 4 (by rfl) ⟨49617, by rfl⟩ : syracuseStep 529253 = 99235) (by norm_num)
theorem B168809 : Blo 155795 168809 := bbase (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) (by norm_num)
theorem B234365 : Blo 155795 234365 := bbase (se 3 (by rfl) ⟨43943, by rfl⟩ : syracuseStep 234365 = 87887) (by norm_num)
theorem B234389 : Blo 155795 234389 := bbase (se 6 (by rfl) ⟨5493, by rfl⟩ : syracuseStep 234389 = 10987) (by norm_num)
theorem B201629 : Blo 155795 201629 := bbase (se 3 (by rfl) ⟨37805, by rfl⟩ : syracuseStep 201629 = 75611) (by norm_num)
theorem B234413 : Blo 155795 234413 := bbase (se 3 (by rfl) ⟨43952, by rfl⟩ : syracuseStep 234413 = 87905) (by norm_num)
theorem B234437 : Blo 155795 234437 := bbase (se 4 (by rfl) ⟨21978, by rfl⟩ : syracuseStep 234437 = 43957) (by norm_num)
theorem B267205 : Blo 155795 267205 := bbase (se 4 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 267205 = 50101) (by norm_num)
theorem B201685 : Blo 155795 201685 := bbase (se 7 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 201685 = 4727) (by norm_num)
theorem B234461 : Blo 155795 234461 := bbase (se 3 (by rfl) ⟨43961, by rfl⟩ : syracuseStep 234461 = 87923) (by norm_num)
theorem B398317 : Blo 155795 398317 := bbase (se 3 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 398317 = 149369) (by norm_num)
theorem B234485 : Blo 155795 234485 := bbase (se 5 (by rfl) ⟨10991, by rfl⟩ : syracuseStep 234485 = 21983) (by norm_num)
theorem B300037 : Blo 155795 300037 := bbase (se 4 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 300037 = 56257) (by norm_num)
theorem B234509 : Blo 155795 234509 := bbase (se 3 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 234509 = 87941) (by norm_num)
theorem B267293 : Blo 155795 267293 := bbase (se 3 (by rfl) ⟨50117, by rfl⟩ : syracuseStep 267293 = 100235) (by norm_num)
theorem B234533 : Blo 155795 234533 := bbase (se 4 (by rfl) ⟨21987, by rfl⟩ : syracuseStep 234533 = 43975) (by norm_num)
theorem B201781 : Blo 155795 201781 := bbase (se 5 (by rfl) ⟨9458, by rfl⟩ : syracuseStep 201781 = 18917) (by norm_num)
theorem B201785 : Blo 155795 201785 := bbase (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) (by norm_num)
theorem B234557 : Blo 155795 234557 := bbase (se 3 (by rfl) ⟨43979, by rfl⟩ : syracuseStep 234557 = 87959) (by norm_num)
theorem B332869 : Blo 155795 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B234581 : Blo 155795 234581 := bbase (se 8 (by rfl) ⟨1374, by rfl⟩ : syracuseStep 234581 = 2749) (by norm_num)
theorem B398429 : Blo 155795 398429 := bbase (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) (by norm_num)
theorem B169057 : Blo 155795 169057 := bbase (se 2 (by rfl) ⟨63396, by rfl⟩ : syracuseStep 169057 = 126793) (by norm_num)
theorem B234605 : Blo 155795 234605 := bbase (se 3 (by rfl) ⟨43988, by rfl⟩ : syracuseStep 234605 = 87977) (by norm_num)
theorem B889973 : Blo 155795 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B234629 : Blo 155795 234629 := bbase (se 4 (by rfl) ⟨21996, by rfl⟩ : syracuseStep 234629 = 43993) (by norm_num)
theorem B300181 : Blo 155795 300181 := bbase (se 6 (by rfl) ⟨7035, by rfl⟩ : syracuseStep 300181 = 14071) (by norm_num)
theorem B234653 : Blo 155795 234653 := bbase (se 3 (by rfl) ⟨43997, by rfl⟩ : syracuseStep 234653 = 87995) (by norm_num)
theorem B267421 : Blo 155795 267421 := bbase (se 3 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 267421 = 100283) (by norm_num)
theorem B234677 : Blo 155795 234677 := bbase (se 5 (by rfl) ⟨11000, by rfl⟩ : syracuseStep 234677 = 22001) (by norm_num)
theorem B234701 : Blo 155795 234701 := bbase (se 3 (by rfl) ⟨44006, by rfl⟩ : syracuseStep 234701 = 88013) (by norm_num)
theorem B201953 : Blo 155795 201953 := bbase (se 2 (by rfl) ⟨75732, by rfl⟩ : syracuseStep 201953 = 151465) (by norm_num)
theorem B234725 : Blo 155795 234725 := bbase (se 4 (by rfl) ⟨22005, by rfl⟩ : syracuseStep 234725 = 44011) (by norm_num)
theorem B267509 : Blo 155795 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B234749 : Blo 155795 234749 := bbase (se 3 (by rfl) ⟨44015, by rfl⟩ : syracuseStep 234749 = 88031) (by norm_num)
theorem B234773 : Blo 155795 234773 := bbase (se 6 (by rfl) ⟨5502, by rfl⟩ : syracuseStep 234773 = 11005) (by norm_num)
theorem B529685 : Blo 155795 529685 := bbase (se 6 (by rfl) ⟨12414, by rfl⟩ : syracuseStep 529685 = 24829) (by norm_num)
theorem B202009 : Blo 155795 202009 := bbase (se 2 (by rfl) ⟨75753, by rfl⟩ : syracuseStep 202009 = 151507) (by norm_num)
theorem B398621 : Blo 155795 398621 := bbase (se 3 (by rfl) ⟨74741, by rfl⟩ : syracuseStep 398621 = 149483) (by norm_num)
theorem B234797 : Blo 155795 234797 := bbase (se 3 (by rfl) ⟨44024, by rfl⟩ : syracuseStep 234797 = 88049) (by norm_num)
theorem B300341 : Blo 155795 300341 := bbase (se 5 (by rfl) ⟨14078, by rfl⟩ : syracuseStep 300341 = 28157) (by norm_num)
theorem B234821 : Blo 155795 234821 := bbase (se 4 (by rfl) ⟨22014, by rfl⟩ : syracuseStep 234821 = 44029) (by norm_num)
theorem B234845 : Blo 155795 234845 := bbase (se 3 (by rfl) ⟨44033, by rfl⟩ : syracuseStep 234845 = 88067) (by norm_num)
theorem B234869 : Blo 155795 234869 := bbase (se 5 (by rfl) ⟨11009, by rfl⟩ : syracuseStep 234869 = 22019) (by norm_num)
theorem B267637 : Blo 155795 267637 := bbase (se 5 (by rfl) ⟨12545, by rfl⟩ : syracuseStep 267637 = 25091) (by norm_num)
theorem B202105 : Blo 155795 202105 := bbase (se 2 (by rfl) ⟨75789, by rfl⟩ : syracuseStep 202105 = 151579) (by norm_num)
theorem B234893 : Blo 155795 234893 := bbase (se 3 (by rfl) ⟨44042, by rfl⟩ : syracuseStep 234893 = 88085) (by norm_num)
theorem B234917 : Blo 155795 234917 := bbase (se 4 (by rfl) ⟨22023, by rfl⟩ : syracuseStep 234917 = 44047) (by norm_num)
theorem B234941 : Blo 155795 234941 := bbase (se 3 (by rfl) ⟨44051, by rfl⟩ : syracuseStep 234941 = 88103) (by norm_num)
theorem B300485 : Blo 155795 300485 := bbase (se 4 (by rfl) ⟨28170, by rfl⟩ : syracuseStep 300485 = 56341) (by norm_num)
theorem B267725 : Blo 155795 267725 := bbase (se 3 (by rfl) ⟨50198, by rfl⟩ : syracuseStep 267725 = 100397) (by norm_num)
theorem B234965 : Blo 155795 234965 := bbase (se 7 (by rfl) ⟨2753, by rfl⟩ : syracuseStep 234965 = 5507) (by norm_num)
theorem B234989 : Blo 155795 234989 := bbase (se 3 (by rfl) ⟨44060, by rfl⟩ : syracuseStep 234989 = 88121) (by norm_num)
theorem B235013 : Blo 155795 235013 := bbase (se 4 (by rfl) ⟨22032, by rfl⟩ : syracuseStep 235013 = 44065) (by norm_num)
theorem B169489 : Blo 155795 169489 := bbase (se 2 (by rfl) ⟨63558, by rfl⟩ : syracuseStep 169489 = 127117) (by norm_num)
theorem B235037 : Blo 155795 235037 := bbase (se 3 (by rfl) ⟨44069, by rfl⟩ : syracuseStep 235037 = 88139) (by norm_num)
theorem B235061 : Blo 155795 235061 := bbase (se 5 (by rfl) ⟨11018, by rfl⟩ : syracuseStep 235061 = 22037) (by norm_num)
theorem B235085 : Blo 155795 235085 := bbase (se 3 (by rfl) ⟨44078, by rfl⟩ : syracuseStep 235085 = 88157) (by norm_num)
theorem B267853 : Blo 155795 267853 := bbase (se 3 (by rfl) ⟨50222, by rfl⟩ : syracuseStep 267853 = 100445) (by norm_num)
theorem B169561 : Blo 155795 169561 := bbase (se 2 (by rfl) ⟨63585, by rfl⟩ : syracuseStep 169561 = 127171) (by norm_num)
theorem B235109 : Blo 155795 235109 := bbase (se 4 (by rfl) ⟨22041, by rfl⟩ : syracuseStep 235109 = 44083) (by norm_num)
theorem B398965 : Blo 155795 398965 := bbase (se 5 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 398965 = 37403) (by norm_num)
theorem B235133 : Blo 155795 235133 := bbase (se 3 (by rfl) ⟨44087, by rfl⟩ : syracuseStep 235133 = 88175) (by norm_num)
theorem B235157 : Blo 155795 235157 := bbase (se 6 (by rfl) ⟨5511, by rfl⟩ : syracuseStep 235157 = 11023) (by norm_num)
theorem B267941 : Blo 155795 267941 := bbase (se 4 (by rfl) ⟨25119, by rfl⟩ : syracuseStep 267941 = 50239) (by norm_num)
theorem B235181 : Blo 155795 235181 := bbase (se 3 (by rfl) ⟨44096, by rfl⟩ : syracuseStep 235181 = 88193) (by norm_num)
theorem B235205 : Blo 155795 235205 := bbase (se 4 (by rfl) ⟨22050, by rfl⟩ : syracuseStep 235205 = 44101) (by norm_num)
theorem B530117 : Blo 155795 530117 := bbase (se 4 (by rfl) ⟨49698, by rfl⟩ : syracuseStep 530117 = 99397) (by norm_num)
theorem B235229 : Blo 155795 235229 := bbase (se 3 (by rfl) ⟨44105, by rfl⟩ : syracuseStep 235229 = 88211) (by norm_num)
theorem B399077 : Blo 155795 399077 := bbase (se 4 (by rfl) ⟨37413, by rfl⟩ : syracuseStep 399077 = 74827) (by norm_num)
theorem B300773 : Blo 155795 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B235253 : Blo 155795 235253 := bbase (se 5 (by rfl) ⟨11027, by rfl⟩ : syracuseStep 235253 = 22055) (by norm_num)
theorem B235277 : Blo 155795 235277 := bbase (se 3 (by rfl) ⟨44114, by rfl⟩ : syracuseStep 235277 = 88229) (by norm_num)
theorem B792341 : Blo 155795 792341 := bbase (se 6 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 792341 = 37141) (by norm_num)
theorem B235301 : Blo 155795 235301 := bbase (se 4 (by rfl) ⟨22059, by rfl⟩ : syracuseStep 235301 = 44119) (by norm_num)
theorem B268069 : Blo 155795 268069 := bbase (se 4 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 268069 = 50263) (by norm_num)
theorem B235325 : Blo 155795 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B235349 : Blo 155795 235349 := bbase (se 9 (by rfl) ⟨689, by rfl⟩ : syracuseStep 235349 = 1379) (by norm_num)
theorem B235373 : Blo 155795 235373 := bbase (se 3 (by rfl) ⟨44132, by rfl⟩ : syracuseStep 235373 = 88265) (by norm_num)
theorem B300925 : Blo 155795 300925 := bbase (se 3 (by rfl) ⟨56423, by rfl⟩ : syracuseStep 300925 = 112847) (by norm_num)
theorem B268157 : Blo 155795 268157 := bbase (se 3 (by rfl) ⟨50279, by rfl⟩ : syracuseStep 268157 = 100559) (by norm_num)
theorem B235397 : Blo 155795 235397 := bbase (se 4 (by rfl) ⟨22068, by rfl⟩ : syracuseStep 235397 = 44137) (by norm_num)
theorem B235421 : Blo 155795 235421 := bbase (se 3 (by rfl) ⟨44141, by rfl⟩ : syracuseStep 235421 = 88283) (by norm_num)
theorem B399269 : Blo 155795 399269 := bbase (se 4 (by rfl) ⟨37431, by rfl⟩ : syracuseStep 399269 = 74863) (by norm_num)
theorem B235445 : Blo 155795 235445 := bbase (se 5 (by rfl) ⟨11036, by rfl⟩ : syracuseStep 235445 = 22073) (by norm_num)
theorem B333757 : Blo 155795 333757 := bbase (se 3 (by rfl) ⟨62579, by rfl⟩ : syracuseStep 333757 = 125159) (by norm_num)
theorem B235469 : Blo 155795 235469 := bbase (se 3 (by rfl) ⟨44150, by rfl⟩ : syracuseStep 235469 = 88301) (by norm_num)
theorem B169933 : Blo 155795 169933 := bbase (se 3 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 169933 = 63725) (by norm_num)
theorem B235493 : Blo 155795 235493 := bbase (se 4 (by rfl) ⟨22077, by rfl⟩ : syracuseStep 235493 = 44155) (by norm_num)
theorem B595957 : Blo 155795 595957 := bbase (se 5 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 595957 = 55871) (by norm_num)
theorem B1349621 : Blo 155795 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B235517 : Blo 155795 235517 := bbase (se 3 (by rfl) ⟨44159, by rfl⟩ : syracuseStep 235517 = 88319) (by norm_num)
theorem B268285 : Blo 155795 268285 := bbase (se 3 (by rfl) ⟨50303, by rfl⟩ : syracuseStep 268285 = 100607) (by norm_num)
theorem B235541 : Blo 155795 235541 := bbase (se 6 (by rfl) ⟨5520, by rfl⟩ : syracuseStep 235541 = 11041) (by norm_num)
theorem B235565 : Blo 155795 235565 := bbase (se 3 (by rfl) ⟨44168, by rfl⟩ : syracuseStep 235565 = 88337) (by norm_num)
theorem B333877 : Blo 155795 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B235589 : Blo 155795 235589 := bbase (se 4 (by rfl) ⟨22086, by rfl⟩ : syracuseStep 235589 = 44173) (by norm_num)
theorem B268373 : Blo 155795 268373 := bbase (se 8 (by rfl) ⟨1572, by rfl⟩ : syracuseStep 268373 = 3145) (by norm_num)
theorem B235613 : Blo 155795 235613 := bbase (se 3 (by rfl) ⟨44177, by rfl⟩ : syracuseStep 235613 = 88355) (by norm_num)
theorem B235637 : Blo 155795 235637 := bbase (se 5 (by rfl) ⟨11045, by rfl⟩ : syracuseStep 235637 = 22091) (by norm_num)
theorem B530549 : Blo 155795 530549 := bbase (se 5 (by rfl) ⟨24869, by rfl⟩ : syracuseStep 530549 = 49739) (by norm_num)
theorem B235661 : Blo 155795 235661 := bbase (se 3 (by rfl) ⟨44186, by rfl⟩ : syracuseStep 235661 = 88373) (by norm_num)
theorem B235685 : Blo 155795 235685 := bbase (se 4 (by rfl) ⟨22095, by rfl⟩ : syracuseStep 235685 = 44191) (by norm_num)
theorem B301229 : Blo 155795 301229 := bbase (se 3 (by rfl) ⟨56480, by rfl⟩ : syracuseStep 301229 = 112961) (by norm_num)
theorem B235709 : Blo 155795 235709 := bbase (se 3 (by rfl) ⟨44195, by rfl⟩ : syracuseStep 235709 = 88391) (by norm_num)
theorem B235733 : Blo 155795 235733 := bbase (se 7 (by rfl) ⟨2762, by rfl⟩ : syracuseStep 235733 = 5525) (by norm_num)
theorem B268501 : Blo 155795 268501 := bbase (se 7 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 268501 = 6293) (by norm_num)
theorem B235757 : Blo 155795 235757 := bbase (se 3 (by rfl) ⟨44204, by rfl⟩ : syracuseStep 235757 = 88409) (by norm_num)
theorem B399613 : Blo 155795 399613 := bbase (se 3 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 399613 = 149855) (by norm_num)
theorem B235781 : Blo 155795 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B235805 : Blo 155795 235805 := bbase (se 3 (by rfl) ⟨44213, by rfl⟩ : syracuseStep 235805 = 88427) (by norm_num)
theorem B596261 : Blo 155795 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B268589 : Blo 155795 268589 := bbase (se 3 (by rfl) ⟨50360, by rfl⟩ : syracuseStep 268589 = 100721) (by norm_num)
theorem B334133 : Blo 155795 334133 := bbase (se 5 (by rfl) ⟨15662, by rfl⟩ : syracuseStep 334133 = 31325) (by norm_num)
theorem B235829 : Blo 155795 235829 := bbase (se 5 (by rfl) ⟨11054, by rfl⟩ : syracuseStep 235829 = 22109) (by norm_num)
theorem B170309 : Blo 155795 170309 := bbase (se 4 (by rfl) ⟨15966, by rfl⟩ : syracuseStep 170309 = 31933) (by norm_num)
theorem B235853 : Blo 155795 235853 := bbase (se 3 (by rfl) ⟨44222, by rfl⟩ : syracuseStep 235853 = 88445) (by norm_num)
theorem B235877 : Blo 155795 235877 := bbase (se 4 (by rfl) ⟨22113, by rfl⟩ : syracuseStep 235877 = 44227) (by norm_num)
theorem B399725 : Blo 155795 399725 := bbase (se 3 (by rfl) ⟨74948, by rfl⟩ : syracuseStep 399725 = 149897) (by norm_num)
theorem B235901 : Blo 155795 235901 := bbase (se 3 (by rfl) ⟨44231, by rfl⟩ : syracuseStep 235901 = 88463) (by norm_num)
theorem B170381 : Blo 155795 170381 := bbase (se 3 (by rfl) ⟨31946, by rfl⟩ : syracuseStep 170381 = 63893) (by norm_num)
theorem B235925 : Blo 155795 235925 := bbase (se 6 (by rfl) ⟨5529, by rfl⟩ : syracuseStep 235925 = 11059) (by norm_num)
theorem B235949 : Blo 155795 235949 := bbase (se 3 (by rfl) ⟨44240, by rfl⟩ : syracuseStep 235949 = 88481) (by norm_num)
theorem B268717 : Blo 155795 268717 := bbase (se 3 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 268717 = 100769) (by norm_num)
theorem B235973 : Blo 155795 235973 := bbase (se 4 (by rfl) ⟨22122, by rfl⟩ : syracuseStep 235973 = 44245) (by norm_num)
theorem B235997 : Blo 155795 235997 := bbase (se 3 (by rfl) ⟨44249, by rfl⟩ : syracuseStep 235997 = 88499) (by norm_num)
theorem B236021 : Blo 155795 236021 := bbase (se 5 (by rfl) ⟨11063, by rfl⟩ : syracuseStep 236021 = 22127) (by norm_num)
theorem B268805 : Blo 155795 268805 := bbase (se 4 (by rfl) ⟨25200, by rfl⟩ : syracuseStep 268805 = 50401) (by norm_num)
theorem B236045 : Blo 155795 236045 := bbase (se 3 (by rfl) ⟨44258, by rfl⟩ : syracuseStep 236045 = 88517) (by norm_num)
theorem B1186325 : Blo 155795 1186325 := bbase (se 6 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 1186325 = 55609) (by norm_num)
theorem B203293 : Blo 155795 203293 := bbase (se 3 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 203293 = 76235) (by norm_num)
theorem B530981 : Blo 155795 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B236069 : Blo 155795 236069 := bbase (se 4 (by rfl) ⟨22131, by rfl⟩ : syracuseStep 236069 = 44263) (by norm_num)
theorem B399917 : Blo 155795 399917 := bbase (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) (by norm_num)
theorem B236093 : Blo 155795 236093 := bbase (se 3 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 236093 = 88535) (by norm_num)
theorem B170569 : Blo 155795 170569 := bbase (se 2 (by rfl) ⟨63963, by rfl⟩ : syracuseStep 170569 = 127927) (by norm_num)
theorem B236117 : Blo 155795 236117 := bbase (se 8 (by rfl) ⟨1383, by rfl⟩ : syracuseStep 236117 = 2767) (by norm_num)
theorem B236141 : Blo 155795 236141 := bbase (se 3 (by rfl) ⟨44276, by rfl⟩ : syracuseStep 236141 = 88553) (by norm_num)
theorem B236165 : Blo 155795 236165 := bbase (se 4 (by rfl) ⟨22140, by rfl⟩ : syracuseStep 236165 = 44281) (by norm_num)
theorem B268933 : Blo 155795 268933 := bbase (se 4 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 268933 = 50425) (by norm_num)
theorem B236189 : Blo 155795 236189 := bbase (se 3 (by rfl) ⟨44285, by rfl⟩ : syracuseStep 236189 = 88571) (by norm_num)
theorem B236213 : Blo 155795 236213 := bbase (se 5 (by rfl) ⟨11072, by rfl⟩ : syracuseStep 236213 = 22145) (by norm_num)
theorem B236237 : Blo 155795 236237 := bbase (se 3 (by rfl) ⟨44294, by rfl⟩ : syracuseStep 236237 = 88589) (by norm_num)
theorem B269021 : Blo 155795 269021 := bbase (se 3 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 269021 = 100883) (by norm_num)
theorem B236261 : Blo 155795 236261 := bbase (se 4 (by rfl) ⟨22149, by rfl⟩ : syracuseStep 236261 = 44299) (by norm_num)
theorem B236285 : Blo 155795 236285 := bbase (se 3 (by rfl) ⟨44303, by rfl⟩ : syracuseStep 236285 = 88607) (by norm_num)
theorem B236309 : Blo 155795 236309 := bbase (se 6 (by rfl) ⟨5538, by rfl⟩ : syracuseStep 236309 = 11077) (by norm_num)
theorem B236333 : Blo 155795 236333 := bbase (se 3 (by rfl) ⟨44312, by rfl⟩ : syracuseStep 236333 = 88625) (by norm_num)
theorem B236357 : Blo 155795 236357 := bbase (se 4 (by rfl) ⟨22158, by rfl⟩ : syracuseStep 236357 = 44317) (by norm_num)
theorem B236381 : Blo 155795 236381 := bbase (se 3 (by rfl) ⟨44321, by rfl⟩ : syracuseStep 236381 = 88643) (by norm_num)
theorem B269149 : Blo 155795 269149 := bbase (se 3 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 269149 = 100931) (by norm_num)
theorem B236405 : Blo 155795 236405 := bbase (se 5 (by rfl) ⟨11081, by rfl⟩ : syracuseStep 236405 = 22163) (by norm_num)
theorem B400261 : Blo 155795 400261 := bbase (se 4 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 400261 = 75049) (by norm_num)
theorem B236429 : Blo 155795 236429 := bbase (se 3 (by rfl) ⟨44330, by rfl⟩ : syracuseStep 236429 = 88661) (by norm_num)
theorem B301981 : Blo 155795 301981 := bbase (se 3 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 301981 = 113243) (by norm_num)
theorem B236453 : Blo 155795 236453 := bbase (se 4 (by rfl) ⟨22167, by rfl⟩ : syracuseStep 236453 = 44335) (by norm_num)
theorem B269237 : Blo 155795 269237 := bbase (se 5 (by rfl) ⟨12620, by rfl⟩ : syracuseStep 269237 = 25241) (by norm_num)
theorem B236477 : Blo 155795 236477 := bbase (se 3 (by rfl) ⟨44339, by rfl⟩ : syracuseStep 236477 = 88679) (by norm_num)
theorem B531413 : Blo 155795 531413 := bbase (se 7 (by rfl) ⟨6227, by rfl⟩ : syracuseStep 531413 = 12455) (by norm_num)
theorem B236501 : Blo 155795 236501 := bbase (se 7 (by rfl) ⟨2771, by rfl⟩ : syracuseStep 236501 = 5543) (by norm_num)
theorem B236525 : Blo 155795 236525 := bbase (se 3 (by rfl) ⟨44348, by rfl⟩ : syracuseStep 236525 = 88697) (by norm_num)
theorem B400373 : Blo 155795 400373 := bbase (se 5 (by rfl) ⟨18767, by rfl⟩ : syracuseStep 400373 = 37535) (by norm_num)
theorem B236549 : Blo 155795 236549 := bbase (se 4 (by rfl) ⟨22176, by rfl⟩ : syracuseStep 236549 = 44353) (by norm_num)
theorem B236573 : Blo 155795 236573 := bbase (se 3 (by rfl) ⟨44357, by rfl⟩ : syracuseStep 236573 = 88715) (by norm_num)
theorem B793637 : Blo 155795 793637 := bbase (se 4 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 793637 = 148807) (by norm_num)
theorem B302125 : Blo 155795 302125 := bbase (se 3 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 302125 = 113297) (by norm_num)
theorem B236597 : Blo 155795 236597 := bbase (se 5 (by rfl) ⟨11090, by rfl⟩ : syracuseStep 236597 = 22181) (by norm_num)
theorem B269365 : Blo 155795 269365 := bbase (se 5 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 269365 = 25253) (by norm_num)
theorem B236621 : Blo 155795 236621 := bbase (se 3 (by rfl) ⟨44366, by rfl⟩ : syracuseStep 236621 = 88733) (by norm_num)
theorem B236645 : Blo 155795 236645 := bbase (se 4 (by rfl) ⟨22185, by rfl⟩ : syracuseStep 236645 = 44371) (by norm_num)
theorem B1055861 : Blo 155795 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B236669 : Blo 155795 236669 := bbase (se 3 (by rfl) ⟨44375, by rfl⟩ : syracuseStep 236669 = 88751) (by norm_num)
theorem B269453 : Blo 155795 269453 := bbase (se 3 (by rfl) ⟨50522, by rfl⟩ : syracuseStep 269453 = 101045) (by norm_num)
theorem B236693 : Blo 155795 236693 := bbase (se 6 (by rfl) ⟨5547, by rfl⟩ : syracuseStep 236693 = 11095) (by norm_num)
theorem B335021 : Blo 155795 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B236717 : Blo 155795 236717 := bbase (se 3 (by rfl) ⟨44384, by rfl⟩ : syracuseStep 236717 = 88769) (by norm_num)
theorem B400565 : Blo 155795 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B236741 : Blo 155795 236741 := bbase (se 4 (by rfl) ⟨22194, by rfl⟩ : syracuseStep 236741 = 44389) (by norm_num)
theorem B728261 : Blo 155795 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B302285 : Blo 155795 302285 := bbase (se 3 (by rfl) ⟨56678, by rfl⟩ : syracuseStep 302285 = 113357) (by norm_num)
theorem B171217 : Blo 155795 171217 := bbase (se 2 (by rfl) ⟨64206, by rfl⟩ : syracuseStep 171217 = 128413) (by norm_num)
theorem B269525 : Blo 155795 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B236765 : Blo 155795 236765 := bbase (se 3 (by rfl) ⟨44393, by rfl⟩ : syracuseStep 236765 = 88787) (by norm_num)
theorem B236789 : Blo 155795 236789 := bbase (se 5 (by rfl) ⟨11099, by rfl⟩ : syracuseStep 236789 = 22199) (by norm_num)
theorem B236813 : Blo 155795 236813 := bbase (se 3 (by rfl) ⟨44402, by rfl⟩ : syracuseStep 236813 = 88805) (by norm_num)
theorem B269581 : Blo 155795 269581 := bbase (se 3 (by rfl) ⟨50546, by rfl⟩ : syracuseStep 269581 = 101093) (by norm_num)
theorem B236837 : Blo 155795 236837 := bbase (se 4 (by rfl) ⟨22203, by rfl⟩ : syracuseStep 236837 = 44407) (by norm_num)
theorem B236861 : Blo 155795 236861 := bbase (se 3 (by rfl) ⟨44411, by rfl⟩ : syracuseStep 236861 = 88823) (by norm_num)
theorem B236885 : Blo 155795 236885 := bbase (se 11 (by rfl) ⟨173, by rfl⟩ : syracuseStep 236885 = 347) (by norm_num)
theorem B302429 : Blo 155795 302429 := bbase (se 3 (by rfl) ⟨56705, by rfl⟩ : syracuseStep 302429 = 113411) (by norm_num)
theorem B236909 : Blo 155795 236909 := bbase (se 3 (by rfl) ⟨44420, by rfl⟩ : syracuseStep 236909 = 88841) (by norm_num)
theorem B531845 : Blo 155795 531845 := bbase (se 4 (by rfl) ⟨49860, by rfl⟩ : syracuseStep 531845 = 99721) (by norm_num)
theorem B236933 : Blo 155795 236933 := bbase (se 4 (by rfl) ⟨22212, by rfl⟩ : syracuseStep 236933 = 44425) (by norm_num)
theorem B335261 : Blo 155795 335261 := bbase (se 3 (by rfl) ⟨62861, by rfl⟩ : syracuseStep 335261 = 125723) (by norm_num)
theorem B236957 : Blo 155795 236957 := bbase (se 3 (by rfl) ⟨44429, by rfl⟩ : syracuseStep 236957 = 88859) (by norm_num)
theorem B236981 : Blo 155795 236981 := bbase (se 5 (by rfl) ⟨11108, by rfl⟩ : syracuseStep 236981 = 22217) (by norm_num)
theorem B237005 : Blo 155795 237005 := bbase (se 3 (by rfl) ⟨44438, by rfl⟩ : syracuseStep 237005 = 88877) (by norm_num)
theorem B237029 : Blo 155795 237029 := bbase (se 4 (by rfl) ⟨22221, by rfl⟩ : syracuseStep 237029 = 44443) (by norm_num)
theorem B237053 : Blo 155795 237053 := bbase (se 3 (by rfl) ⟨44447, by rfl⟩ : syracuseStep 237053 = 88895) (by norm_num)
theorem B400909 : Blo 155795 400909 := bbase (se 3 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 400909 = 150341) (by norm_num)
theorem B237077 : Blo 155795 237077 := bbase (se 6 (by rfl) ⟨5556, by rfl⟩ : syracuseStep 237077 = 11113) (by norm_num)
theorem B237101 : Blo 155795 237101 := bbase (se 3 (by rfl) ⟨44456, by rfl⟩ : syracuseStep 237101 = 88913) (by norm_num)
theorem B237125 : Blo 155795 237125 := bbase (se 4 (by rfl) ⟨22230, by rfl⟩ : syracuseStep 237125 = 44461) (by norm_num)
theorem B237149 : Blo 155795 237149 := bbase (se 3 (by rfl) ⟨44465, by rfl⟩ : syracuseStep 237149 = 88931) (by norm_num)
theorem B237173 : Blo 155795 237173 := bbase (se 5 (by rfl) ⟨11117, by rfl⟩ : syracuseStep 237173 = 22235) (by norm_num)
theorem B401021 : Blo 155795 401021 := bbase (se 3 (by rfl) ⟨75191, by rfl⟩ : syracuseStep 401021 = 150383) (by norm_num)
theorem B302717 : Blo 155795 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B237197 : Blo 155795 237197 := bbase (se 3 (by rfl) ⟨44474, by rfl⟩ : syracuseStep 237197 = 88949) (by norm_num)
theorem B1777301 : Blo 155795 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B237221 : Blo 155795 237221 := bbase (se 4 (by rfl) ⟨22239, by rfl⟩ : syracuseStep 237221 = 44479) (by norm_num)
theorem B237245 : Blo 155795 237245 := bbase (se 3 (by rfl) ⟨44483, by rfl⟩ : syracuseStep 237245 = 88967) (by norm_num)
theorem B237269 : Blo 155795 237269 := bbase (se 7 (by rfl) ⟨2780, by rfl⟩ : syracuseStep 237269 = 5561) (by norm_num)
theorem B237293 : Blo 155795 237293 := bbase (se 3 (by rfl) ⟨44492, by rfl⟩ : syracuseStep 237293 = 88985) (by norm_num)
theorem B237317 : Blo 155795 237317 := bbase (se 4 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 237317 = 44497) (by norm_num)
theorem B270101 : Blo 155795 270101 := bbase (se 6 (by rfl) ⟨6330, by rfl⟩ : syracuseStep 270101 = 12661) (by norm_num)
theorem B1154837 : Blo 155795 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B302869 : Blo 155795 302869 := bbase (se 6 (by rfl) ⟨7098, by rfl⟩ : syracuseStep 302869 = 14197) (by norm_num)
theorem B237341 : Blo 155795 237341 := bbase (se 3 (by rfl) ⟨44501, by rfl⟩ : syracuseStep 237341 = 89003) (by norm_num)
theorem B171805 : Blo 155795 171805 := bbase (se 3 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 171805 = 64427) (by norm_num)
theorem B532277 : Blo 155795 532277 := bbase (se 5 (by rfl) ⟨24950, by rfl⟩ : syracuseStep 532277 = 49901) (by norm_num)
theorem B237365 : Blo 155795 237365 := bbase (se 5 (by rfl) ⟨11126, by rfl⟩ : syracuseStep 237365 = 22253) (by norm_num)
theorem B401213 : Blo 155795 401213 := bbase (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) (by norm_num)
theorem B237389 : Blo 155795 237389 := bbase (se 3 (by rfl) ⟨44510, by rfl⟩ : syracuseStep 237389 = 89021) (by norm_num)
theorem B237413 : Blo 155795 237413 := bbase (se 4 (by rfl) ⟨22257, by rfl⟩ : syracuseStep 237413 = 44515) (by norm_num)
theorem B237437 : Blo 155795 237437 := bbase (se 3 (by rfl) ⟨44519, by rfl⟩ : syracuseStep 237437 = 89039) (by norm_num)
theorem B434069 : Blo 155795 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B335765 : Blo 155795 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B237461 : Blo 155795 237461 := bbase (se 6 (by rfl) ⟨5565, by rfl⟩ : syracuseStep 237461 = 11131) (by norm_num)
theorem B335773 : Blo 155795 335773 := bbase (se 3 (by rfl) ⟨62957, by rfl⟩ : syracuseStep 335773 = 125915) (by norm_num)
theorem B237485 : Blo 155795 237485 := bbase (se 3 (by rfl) ⟨44528, by rfl⟩ : syracuseStep 237485 = 89057) (by norm_num)
theorem B237509 : Blo 155795 237509 := bbase (se 4 (by rfl) ⟨22266, by rfl⟩ : syracuseStep 237509 = 44533) (by norm_num)
theorem B237533 : Blo 155795 237533 := bbase (se 3 (by rfl) ⟨44537, by rfl⟩ : syracuseStep 237533 = 89075) (by norm_num)
theorem B237557 : Blo 155795 237557 := bbase (se 5 (by rfl) ⟨11135, by rfl⟩ : syracuseStep 237557 = 22271) (by norm_num)
theorem B237581 : Blo 155795 237581 := bbase (se 3 (by rfl) ⟨44546, by rfl⟩ : syracuseStep 237581 = 89093) (by norm_num)
theorem B237605 : Blo 155795 237605 := bbase (se 4 (by rfl) ⟨22275, by rfl⟩ : syracuseStep 237605 = 44551) (by norm_num)
theorem B237629 : Blo 155795 237629 := bbase (se 3 (by rfl) ⟨44555, by rfl⟩ : syracuseStep 237629 = 89111) (by norm_num)
theorem B303173 : Blo 155795 303173 := bbase (se 4 (by rfl) ⟨28422, by rfl⟩ : syracuseStep 303173 = 56845) (by norm_num)
theorem B237653 : Blo 155795 237653 := bbase (se 8 (by rfl) ⟨1392, by rfl⟩ : syracuseStep 237653 = 2785) (by norm_num)
theorem B237677 : Blo 155795 237677 := bbase (se 3 (by rfl) ⟨44564, by rfl⟩ : syracuseStep 237677 = 89129) (by norm_num)
theorem B237701 : Blo 155795 237701 := bbase (se 4 (by rfl) ⟨22284, by rfl⟩ : syracuseStep 237701 = 44569) (by norm_num)
theorem B401557 : Blo 155795 401557 := bbase (se 6 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 401557 = 18823) (by norm_num)
theorem B237725 : Blo 155795 237725 := bbase (se 3 (by rfl) ⟨44573, by rfl⟩ : syracuseStep 237725 = 89147) (by norm_num)
theorem B237749 : Blo 155795 237749 := bbase (se 5 (by rfl) ⟨11144, by rfl⟩ : syracuseStep 237749 = 22289) (by norm_num)
theorem B237773 : Blo 155795 237773 := bbase (se 3 (by rfl) ⟨44582, by rfl⟩ : syracuseStep 237773 = 89165) (by norm_num)
theorem B532709 : Blo 155795 532709 := bbase (se 4 (by rfl) ⟨49941, by rfl⟩ : syracuseStep 532709 = 99883) (by norm_num)
theorem B237797 : Blo 155795 237797 := bbase (se 4 (by rfl) ⟨22293, by rfl⟩ : syracuseStep 237797 = 44587) (by norm_num)
theorem B1646837 : Blo 155795 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B237821 : Blo 155795 237821 := bbase (se 3 (by rfl) ⟨44591, by rfl⟩ : syracuseStep 237821 = 89183) (by norm_num)
theorem B401669 : Blo 155795 401669 := bbase (se 4 (by rfl) ⟨37656, by rfl⟩ : syracuseStep 401669 = 75313) (by norm_num)
theorem B237845 : Blo 155795 237845 := bbase (se 6 (by rfl) ⟨5574, by rfl⟩ : syracuseStep 237845 = 11149) (by norm_num)
theorem B237869 : Blo 155795 237869 := bbase (se 3 (by rfl) ⟨44600, by rfl⟩ : syracuseStep 237869 = 89201) (by norm_num)
theorem B794933 : Blo 155795 794933 := bbase (se 5 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 794933 = 74525) (by norm_num)
theorem B237893 : Blo 155795 237893 := bbase (se 4 (by rfl) ⟨22302, by rfl⟩ : syracuseStep 237893 = 44605) (by norm_num)
theorem B237917 : Blo 155795 237917 := bbase (se 3 (by rfl) ⟨44609, by rfl⟩ : syracuseStep 237917 = 89219) (by norm_num)
theorem B598373 : Blo 155795 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B237941 : Blo 155795 237941 := bbase (se 5 (by rfl) ⟨11153, by rfl⟩ : syracuseStep 237941 = 22307) (by norm_num)
theorem B237965 : Blo 155795 237965 := bbase (se 3 (by rfl) ⟨44618, by rfl⟩ : syracuseStep 237965 = 89237) (by norm_num)
theorem B237989 : Blo 155795 237989 := bbase (se 4 (by rfl) ⟨22311, by rfl⟩ : syracuseStep 237989 = 44623) (by norm_num)
theorem B238013 : Blo 155795 238013 := bbase (se 3 (by rfl) ⟨44627, by rfl⟩ : syracuseStep 238013 = 89255) (by norm_num)
theorem B401861 : Blo 155795 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B238037 : Blo 155795 238037 := bbase (se 7 (by rfl) ⟨2789, by rfl⟩ : syracuseStep 238037 = 5579) (by norm_num)
theorem B238061 : Blo 155795 238061 := bbase (se 3 (by rfl) ⟨44636, by rfl⟩ : syracuseStep 238061 = 89273) (by norm_num)
theorem B238085 : Blo 155795 238085 := bbase (se 4 (by rfl) ⟨22320, by rfl⟩ : syracuseStep 238085 = 44641) (by norm_num)
theorem B238109 : Blo 155795 238109 := bbase (se 3 (by rfl) ⟨44645, by rfl⟩ : syracuseStep 238109 = 89291) (by norm_num)
theorem B238133 : Blo 155795 238133 := bbase (se 5 (by rfl) ⟨11162, by rfl⟩ : syracuseStep 238133 = 22325) (by norm_num)
theorem B238157 : Blo 155795 238157 := bbase (se 3 (by rfl) ⟨44654, by rfl⟩ : syracuseStep 238157 = 89309) (by norm_num)
theorem B303709 : Blo 155795 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B238181 : Blo 155795 238181 := bbase (se 4 (by rfl) ⟨22329, by rfl⟩ : syracuseStep 238181 = 44659) (by norm_num)
theorem B238205 : Blo 155795 238205 := bbase (se 3 (by rfl) ⟨44663, by rfl⟩ : syracuseStep 238205 = 89327) (by norm_num)
theorem B598661 : Blo 155795 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B533141 : Blo 155795 533141 := bbase (se 6 (by rfl) ⟨12495, by rfl⟩ : syracuseStep 533141 = 24991) (by norm_num)
theorem B238229 : Blo 155795 238229 := bbase (se 6 (by rfl) ⟨5583, by rfl⟩ : syracuseStep 238229 = 11167) (by norm_num)
theorem B238253 : Blo 155795 238253 := bbase (se 3 (by rfl) ⟨44672, by rfl⟩ : syracuseStep 238253 = 89345) (by norm_num)
theorem B238277 : Blo 155795 238277 := bbase (se 4 (by rfl) ⟨22338, by rfl⟩ : syracuseStep 238277 = 44677) (by norm_num)
theorem B238301 : Blo 155795 238301 := bbase (se 3 (by rfl) ⟨44681, by rfl⟩ : syracuseStep 238301 = 89363) (by norm_num)
theorem B238325 : Blo 155795 238325 := bbase (se 5 (by rfl) ⟨11171, by rfl⟩ : syracuseStep 238325 = 22343) (by norm_num)
theorem B238349 : Blo 155795 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B402205 : Blo 155795 402205 := bbase (se 3 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 402205 = 150827) (by norm_num)
theorem B238373 : Blo 155795 238373 := bbase (se 4 (by rfl) ⟨22347, by rfl⟩ : syracuseStep 238373 = 44695) (by norm_num)
theorem B303925 : Blo 155795 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B238397 : Blo 155795 238397 := bbase (se 3 (by rfl) ⟨44699, by rfl⟩ : syracuseStep 238397 = 89399) (by norm_num)
theorem B271181 : Blo 155795 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B238421 : Blo 155795 238421 := bbase (se 9 (by rfl) ⟨698, by rfl⟩ : syracuseStep 238421 = 1397) (by norm_num)
theorem B238445 : Blo 155795 238445 := bbase (se 3 (by rfl) ⟨44708, by rfl⟩ : syracuseStep 238445 = 89417) (by norm_num)
theorem B238469 : Blo 155795 238469 := bbase (se 4 (by rfl) ⟨22356, by rfl⟩ : syracuseStep 238469 = 44713) (by norm_num)
theorem B402317 : Blo 155795 402317 := bbase (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) (by norm_num)
theorem B238493 : Blo 155795 238493 := bbase (se 3 (by rfl) ⟨44717, by rfl⟩ : syracuseStep 238493 = 89435) (by norm_num)
theorem B238517 : Blo 155795 238517 := bbase (se 5 (by rfl) ⟨11180, by rfl⟩ : syracuseStep 238517 = 22361) (by norm_num)
theorem B238541 : Blo 155795 238541 := bbase (se 3 (by rfl) ⟨44726, by rfl⟩ : syracuseStep 238541 = 89453) (by norm_num)
theorem B762853 : Blo 155795 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B238565 : Blo 155795 238565 := bbase (se 4 (by rfl) ⟨22365, by rfl⟩ : syracuseStep 238565 = 44731) (by norm_num)
theorem B238589 : Blo 155795 238589 := bbase (se 3 (by rfl) ⟨44735, by rfl⟩ : syracuseStep 238589 = 89471) (by norm_num)
theorem B336901 : Blo 155795 336901 := bbase (se 4 (by rfl) ⟨31584, by rfl⟩ : syracuseStep 336901 = 63169) (by norm_num)
theorem B238613 : Blo 155795 238613 := bbase (se 6 (by rfl) ⟨5592, by rfl⟩ : syracuseStep 238613 = 11185) (by norm_num)
theorem B238637 : Blo 155795 238637 := bbase (se 3 (by rfl) ⟨44744, by rfl⟩ : syracuseStep 238637 = 89489) (by norm_num)
theorem B500789 : Blo 155795 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B533573 : Blo 155795 533573 := bbase (se 4 (by rfl) ⟨50022, by rfl⟩ : syracuseStep 533573 = 100045) (by norm_num)
theorem B238661 : Blo 155795 238661 := bbase (se 4 (by rfl) ⟨22374, by rfl⟩ : syracuseStep 238661 = 44749) (by norm_num)
theorem B402509 : Blo 155795 402509 := bbase (se 3 (by rfl) ⟨75470, by rfl⟩ : syracuseStep 402509 = 150941) (by norm_num)
theorem B238685 : Blo 155795 238685 := bbase (se 3 (by rfl) ⟨44753, by rfl⟩ : syracuseStep 238685 = 89507) (by norm_num)
theorem B238709 : Blo 155795 238709 := bbase (se 5 (by rfl) ⟨11189, by rfl⟩ : syracuseStep 238709 = 22379) (by norm_num)
theorem B238733 : Blo 155795 238733 := bbase (se 3 (by rfl) ⟨44762, by rfl⟩ : syracuseStep 238733 = 89525) (by norm_num)
theorem B238757 : Blo 155795 238757 := bbase (se 4 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 238757 = 44767) (by norm_num)
theorem B238781 : Blo 155795 238781 := bbase (se 3 (by rfl) ⟨44771, by rfl⟩ : syracuseStep 238781 = 89543) (by norm_num)
theorem B238805 : Blo 155795 238805 := bbase (se 7 (by rfl) ⟨2798, by rfl⟩ : syracuseStep 238805 = 5597) (by norm_num)
theorem B238829 : Blo 155795 238829 := bbase (se 3 (by rfl) ⟨44780, by rfl⟩ : syracuseStep 238829 = 89561) (by norm_num)
theorem B238853 : Blo 155795 238853 := bbase (se 4 (by rfl) ⟨22392, by rfl⟩ : syracuseStep 238853 = 44785) (by norm_num)
theorem B238877 : Blo 155795 238877 := bbase (se 3 (by rfl) ⟨44789, by rfl⟩ : syracuseStep 238877 = 89579) (by norm_num)
theorem B238901 : Blo 155795 238901 := bbase (se 5 (by rfl) ⟨11198, by rfl⟩ : syracuseStep 238901 = 22397) (by norm_num)
theorem B238925 : Blo 155795 238925 := bbase (se 3 (by rfl) ⟨44798, by rfl⟩ : syracuseStep 238925 = 89597) (by norm_num)
theorem B2663765 : Blo 155795 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B238949 : Blo 155795 238949 := bbase (se 4 (by rfl) ⟨22401, by rfl⟩ : syracuseStep 238949 = 44803) (by norm_num)
theorem B337277 : Blo 155795 337277 := bbase (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) (by norm_num)
theorem B238973 : Blo 155795 238973 := bbase (se 3 (by rfl) ⟨44807, by rfl⟩ : syracuseStep 238973 = 89615) (by norm_num)
theorem B238997 : Blo 155795 238997 := bbase (se 6 (by rfl) ⟨5601, by rfl⟩ : syracuseStep 238997 = 11203) (by norm_num)
theorem B206233 : Blo 155795 206233 := bbase (se 2 (by rfl) ⟨77337, by rfl⟩ : syracuseStep 206233 = 154675) (by norm_num)
theorem B402853 : Blo 155795 402853 := bbase (se 4 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 402853 = 75535) (by norm_num)
theorem B239021 : Blo 155795 239021 := bbase (se 3 (by rfl) ⟨44816, by rfl⟩ : syracuseStep 239021 = 89633) (by norm_num)
theorem B239045 : Blo 155795 239045 := bbase (se 4 (by rfl) ⟨22410, by rfl⟩ : syracuseStep 239045 = 44821) (by norm_num)
theorem B2041301 : Blo 155795 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B239069 : Blo 155795 239069 := bbase (se 3 (by rfl) ⟨44825, by rfl⟩ : syracuseStep 239069 = 89651) (by norm_num)
theorem B534005 : Blo 155795 534005 := bbase (se 5 (by rfl) ⟨25031, by rfl⟩ : syracuseStep 534005 = 50063) (by norm_num)
theorem B239093 : Blo 155795 239093 := bbase (se 5 (by rfl) ⟨11207, by rfl⟩ : syracuseStep 239093 = 22415) (by norm_num)
theorem B239117 : Blo 155795 239117 := bbase (se 3 (by rfl) ⟨44834, by rfl⟩ : syracuseStep 239117 = 89669) (by norm_num)
theorem B402965 : Blo 155795 402965 := bbase (se 6 (by rfl) ⟨9444, by rfl⟩ : syracuseStep 402965 = 18889) (by norm_num)
theorem B239141 : Blo 155795 239141 := bbase (se 4 (by rfl) ⟨22419, by rfl⟩ : syracuseStep 239141 = 44839) (by norm_num)
theorem B566837 : Blo 155795 566837 := bbase (se 5 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 566837 = 53141) (by norm_num)
theorem B239165 : Blo 155795 239165 := bbase (se 3 (by rfl) ⟨44843, by rfl⟩ : syracuseStep 239165 = 89687) (by norm_num)
theorem B796229 : Blo 155795 796229 := bbase (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) (by norm_num)
theorem B239189 : Blo 155795 239189 := bbase (se 8 (by rfl) ⟨1401, by rfl⟩ : syracuseStep 239189 = 2803) (by norm_num)
theorem B239213 : Blo 155795 239213 := bbase (se 3 (by rfl) ⟨44852, by rfl⟩ : syracuseStep 239213 = 89705) (by norm_num)
theorem B239237 : Blo 155795 239237 := bbase (se 4 (by rfl) ⟨22428, by rfl⟩ : syracuseStep 239237 = 44857) (by norm_num)
theorem B239261 : Blo 155795 239261 := bbase (se 3 (by rfl) ⟨44861, by rfl⟩ : syracuseStep 239261 = 89723) (by norm_num)
theorem B239285 : Blo 155795 239285 := bbase (se 5 (by rfl) ⟨11216, by rfl⟩ : syracuseStep 239285 = 22433) (by norm_num)
theorem B239309 : Blo 155795 239309 := bbase (se 3 (by rfl) ⟨44870, by rfl⟩ : syracuseStep 239309 = 89741) (by norm_num)
theorem B403157 : Blo 155795 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B632549 : Blo 155795 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B239333 : Blo 155795 239333 := bbase (se 4 (by rfl) ⟨22437, by rfl⟩ : syracuseStep 239333 = 44875) (by norm_num)
theorem B239357 : Blo 155795 239357 := bbase (se 3 (by rfl) ⟨44879, by rfl⟩ : syracuseStep 239357 = 89759) (by norm_num)
theorem B239381 : Blo 155795 239381 := bbase (se 6 (by rfl) ⟨5610, by rfl⟩ : syracuseStep 239381 = 11221) (by norm_num)
theorem B599845 : Blo 155795 599845 := bbase (se 4 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 599845 = 112471) (by norm_num)
theorem B239405 : Blo 155795 239405 := bbase (se 3 (by rfl) ⟨44888, by rfl⟩ : syracuseStep 239405 = 89777) (by norm_num)
theorem B239429 : Blo 155795 239429 := bbase (se 4 (by rfl) ⟨22446, by rfl⟩ : syracuseStep 239429 = 44893) (by norm_num)
theorem B239453 : Blo 155795 239453 := bbase (se 3 (by rfl) ⟨44897, by rfl⟩ : syracuseStep 239453 = 89795) (by norm_num)
theorem B239477 : Blo 155795 239477 := bbase (se 5 (by rfl) ⟨11225, by rfl⟩ : syracuseStep 239477 = 22451) (by norm_num)
theorem B239501 : Blo 155795 239501 := bbase (se 3 (by rfl) ⟨44906, by rfl⟩ : syracuseStep 239501 = 89813) (by norm_num)
theorem B534437 : Blo 155795 534437 := bbase (se 4 (by rfl) ⟨50103, by rfl⟩ : syracuseStep 534437 = 100207) (by norm_num)
theorem B239525 : Blo 155795 239525 := bbase (se 4 (by rfl) ⟨22455, by rfl⟩ : syracuseStep 239525 = 44911) (by norm_num)
theorem B239549 : Blo 155795 239549 := bbase (se 3 (by rfl) ⟨44915, by rfl⟩ : syracuseStep 239549 = 89831) (by norm_num)
theorem B567253 : Blo 155795 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B239573 : Blo 155795 239573 := bbase (se 7 (by rfl) ⟨2807, by rfl⟩ : syracuseStep 239573 = 5615) (by norm_num)
theorem B239597 : Blo 155795 239597 := bbase (se 3 (by rfl) ⟨44924, by rfl⟩ : syracuseStep 239597 = 89849) (by norm_num)
theorem B239621 : Blo 155795 239621 := bbase (se 4 (by rfl) ⟨22464, by rfl⟩ : syracuseStep 239621 = 44929) (by norm_num)
theorem B239645 : Blo 155795 239645 := bbase (se 3 (by rfl) ⟨44933, by rfl⟩ : syracuseStep 239645 = 89867) (by norm_num)
theorem B403501 : Blo 155795 403501 := bbase (se 3 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 403501 = 151313) (by norm_num)
theorem B239669 : Blo 155795 239669 := bbase (se 5 (by rfl) ⟨11234, by rfl⟩ : syracuseStep 239669 = 22469) (by norm_num)
theorem B239693 : Blo 155795 239693 := bbase (se 3 (by rfl) ⟨44942, by rfl⟩ : syracuseStep 239693 = 89885) (by norm_num)
theorem B600149 : Blo 155795 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B403613 : Blo 155795 403613 := bbase (se 3 (by rfl) ⟨75677, by rfl⟩ : syracuseStep 403613 = 151355) (by norm_num)
theorem B436421 : Blo 155795 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B534869 : Blo 155795 534869 := bbase (se 10 (by rfl) ⟨783, by rfl⟩ : syracuseStep 534869 = 1567) (by norm_num)
theorem B403805 : Blo 155795 403805 := bbase (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) (by norm_num)
theorem B502213 : Blo 155795 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B305669 : Blo 155795 305669 := bbase (se 4 (by rfl) ⟨28656, by rfl⟩ : syracuseStep 305669 = 57313) (by norm_num)
theorem B338485 : Blo 155795 338485 := bbase (se 5 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 338485 = 31733) (by norm_num)
theorem B338573 : Blo 155795 338573 := bbase (se 3 (by rfl) ⟨63482, by rfl⟩ : syracuseStep 338573 = 126965) (by norm_num)
theorem B404149 : Blo 155795 404149 := bbase (se 5 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 404149 = 37889) (by norm_num)
theorem B535301 : Blo 155795 535301 := bbase (se 4 (by rfl) ⟨50184, by rfl⟩ : syracuseStep 535301 = 100369) (by norm_num)
theorem B404261 : Blo 155795 404261 := bbase (se 4 (by rfl) ⟨37899, by rfl⟩ : syracuseStep 404261 = 75799) (by norm_num)
theorem B797525 : Blo 155795 797525 := bbase (se 9 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 797525 = 4673) (by norm_num)
theorem B502661 : Blo 155795 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B306125 : Blo 155795 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B338917 : Blo 155795 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B404453 : Blo 155795 404453 := bbase (se 4 (by rfl) ⟨37917, by rfl⟩ : syracuseStep 404453 = 75835) (by norm_num)
theorem B1027093 : Blo 155795 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B339109 : Blo 155795 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B175273 : Blo 155795 175273 := bbase (se 2 (by rfl) ⟨65727, by rfl⟩ : syracuseStep 175273 = 131455) (by norm_num)
theorem B535733 : Blo 155795 535733 := bbase (se 5 (by rfl) ⟨25112, by rfl⟩ : syracuseStep 535733 = 50225) (by norm_num)
theorem B175297 : Blo 155795 175297 := bbase (se 2 (by rfl) ⟨65736, by rfl⟩ : syracuseStep 175297 = 131473) (by norm_num)
theorem B175333 : Blo 155795 175333 := bbase (se 4 (by rfl) ⟨16437, by rfl⟩ : syracuseStep 175333 = 32875) (by norm_num)
theorem B175369 : Blo 155795 175369 := bbase (se 2 (by rfl) ⟨65763, by rfl⟩ : syracuseStep 175369 = 131527) (by norm_num)
theorem B175405 : Blo 155795 175405 := bbase (se 3 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 175405 = 65777) (by norm_num)
theorem B175441 : Blo 155795 175441 := bbase (se 2 (by rfl) ⟨65790, by rfl⟩ : syracuseStep 175441 = 131581) (by norm_num)
theorem B3026261 : Blo 155795 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B175477 : Blo 155795 175477 := bbase (se 5 (by rfl) ⟨8225, by rfl⟩ : syracuseStep 175477 = 16451) (by norm_num)
theorem B175513 : Blo 155795 175513 := bbase (se 2 (by rfl) ⟨65817, by rfl⟩ : syracuseStep 175513 = 131635) (by norm_num)
theorem B175549 : Blo 155795 175549 := bbase (se 3 (by rfl) ⟨32915, by rfl⟩ : syracuseStep 175549 = 65831) (by norm_num)
theorem B175585 : Blo 155795 175585 := bbase (se 2 (by rfl) ⟨65844, by rfl⟩ : syracuseStep 175585 = 131689) (by norm_num)
theorem B175621 : Blo 155795 175621 := bbase (se 4 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 175621 = 32929) (by norm_num)
theorem B175657 : Blo 155795 175657 := bbase (se 2 (by rfl) ⟨65871, by rfl⟩ : syracuseStep 175657 = 131743) (by norm_num)
theorem B175693 : Blo 155795 175693 := bbase (se 3 (by rfl) ⟨32942, by rfl⟩ : syracuseStep 175693 = 65885) (by norm_num)
theorem B536165 : Blo 155795 536165 := bbase (se 4 (by rfl) ⟨50265, by rfl⟩ : syracuseStep 536165 = 100531) (by norm_num)
theorem B175729 : Blo 155795 175729 := bbase (se 2 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 175729 = 131797) (by norm_num)
theorem B175765 : Blo 155795 175765 := bbase (se 6 (by rfl) ⟨4119, by rfl⟩ : syracuseStep 175765 = 8239) (by norm_num)
theorem B175801 : Blo 155795 175801 := bbase (se 2 (by rfl) ⟨65925, by rfl⟩ : syracuseStep 175801 = 131851) (by norm_num)
theorem B175837 : Blo 155795 175837 := bbase (se 3 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 175837 = 65939) (by norm_num)
theorem B175873 : Blo 155795 175873 := bbase (se 2 (by rfl) ⟨65952, by rfl⟩ : syracuseStep 175873 = 131905) (by norm_num)
theorem B3059477 : Blo 155795 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B306965 : Blo 155795 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B175909 : Blo 155795 175909 := bbase (se 4 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 175909 = 32983) (by norm_num)
theorem B175945 : Blo 155795 175945 := bbase (se 2 (by rfl) ⟨65979, by rfl⟩ : syracuseStep 175945 = 131959) (by norm_num)
theorem B339805 : Blo 155795 339805 := bbase (se 3 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 339805 = 127427) (by norm_num)
theorem B175981 : Blo 155795 175981 := bbase (se 3 (by rfl) ⟨32996, by rfl⟩ : syracuseStep 175981 = 65993) (by norm_num)
theorem B176017 : Blo 155795 176017 := bbase (se 2 (by rfl) ⟨66006, by rfl⟩ : syracuseStep 176017 = 132013) (by norm_num)
theorem B176053 : Blo 155795 176053 := bbase (se 5 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 176053 = 16505) (by norm_num)
theorem B176089 : Blo 155795 176089 := bbase (se 2 (by rfl) ⟨66033, by rfl⟩ : syracuseStep 176089 = 132067) (by norm_num)
theorem B176125 : Blo 155795 176125 := bbase (se 3 (by rfl) ⟨33023, by rfl⟩ : syracuseStep 176125 = 66047) (by norm_num)
theorem B536597 : Blo 155795 536597 := bbase (se 6 (by rfl) ⟨12576, by rfl⟩ : syracuseStep 536597 = 25153) (by norm_num)
theorem B176161 : Blo 155795 176161 := bbase (se 2 (by rfl) ⟨66060, by rfl⟩ : syracuseStep 176161 = 132121) (by norm_num)
theorem B176197 : Blo 155795 176197 := bbase (se 4 (by rfl) ⟨16518, by rfl⟩ : syracuseStep 176197 = 33037) (by norm_num)
theorem B798821 : Blo 155795 798821 := bbase (se 4 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 798821 = 149779) (by norm_num)
theorem B176233 : Blo 155795 176233 := bbase (se 2 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 176233 = 132175) (by norm_num)
theorem B602245 : Blo 155795 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B176269 : Blo 155795 176269 := bbase (se 3 (by rfl) ⟨33050, by rfl⟩ : syracuseStep 176269 = 66101) (by norm_num)
theorem B602261 : Blo 155795 602261 := bbase (se 6 (by rfl) ⟨14115, by rfl⟩ : syracuseStep 602261 = 28231) (by norm_num)
theorem B176305 : Blo 155795 176305 := bbase (se 2 (by rfl) ⟨66114, by rfl⟩ : syracuseStep 176305 = 132229) (by norm_num)
theorem B176341 : Blo 155795 176341 := bbase (se 7 (by rfl) ⟨2066, by rfl⟩ : syracuseStep 176341 = 4133) (by norm_num)
theorem B176377 : Blo 155795 176377 := bbase (se 2 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 176377 = 132283) (by norm_num)
theorem B667925 : Blo 155795 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B176413 : Blo 155795 176413 := bbase (se 3 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 176413 = 66155) (by norm_num)
theorem B176449 : Blo 155795 176449 := bbase (se 2 (by rfl) ⟨66168, by rfl⟩ : syracuseStep 176449 = 132337) (by norm_num)
theorem B340301 : Blo 155795 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B176485 : Blo 155795 176485 := bbase (se 4 (by rfl) ⟨16545, by rfl⟩ : syracuseStep 176485 = 33091) (by norm_num)
theorem B176521 : Blo 155795 176521 := bbase (se 2 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 176521 = 132391) (by norm_num)
theorem B176557 : Blo 155795 176557 := bbase (se 3 (by rfl) ⟨33104, by rfl⟩ : syracuseStep 176557 = 66209) (by norm_num)
theorem B602549 : Blo 155795 602549 := bbase (se 5 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 602549 = 56489) (by norm_num)
theorem B537029 : Blo 155795 537029 := bbase (se 4 (by rfl) ⟨50346, by rfl⟩ : syracuseStep 537029 = 100693) (by norm_num)
theorem B176593 : Blo 155795 176593 := bbase (se 2 (by rfl) ⟨66222, by rfl⟩ : syracuseStep 176593 = 132445) (by norm_num)
theorem B176629 : Blo 155795 176629 := bbase (se 5 (by rfl) ⟨8279, by rfl⟩ : syracuseStep 176629 = 16559) (by norm_num)
theorem B176665 : Blo 155795 176665 := bbase (se 2 (by rfl) ⟨66249, by rfl⟩ : syracuseStep 176665 = 132499) (by norm_num)
theorem B176701 : Blo 155795 176701 := bbase (se 3 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 176701 = 66263) (by norm_num)
theorem B176737 : Blo 155795 176737 := bbase (se 2 (by rfl) ⟨66276, by rfl⟩ : syracuseStep 176737 = 132553) (by norm_num)
theorem B176773 : Blo 155795 176773 := bbase (se 4 (by rfl) ⟨16572, by rfl⟩ : syracuseStep 176773 = 33145) (by norm_num)
theorem B176809 : Blo 155795 176809 := bbase (se 2 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 176809 = 132607) (by norm_num)
theorem B176845 : Blo 155795 176845 := bbase (se 3 (by rfl) ⟨33158, by rfl⟩ : syracuseStep 176845 = 66317) (by norm_num)
theorem B176881 : Blo 155795 176881 := bbase (se 2 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 176881 = 132661) (by norm_num)
theorem B176917 : Blo 155795 176917 := bbase (se 6 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 176917 = 8293) (by norm_num)
theorem B242461 : Blo 155795 242461 := bbase (se 3 (by rfl) ⟨45461, by rfl⟩ : syracuseStep 242461 = 90923) (by norm_num)
theorem B176953 : Blo 155795 176953 := bbase (se 2 (by rfl) ⟨66357, by rfl⟩ : syracuseStep 176953 = 132715) (by norm_num)
theorem B176989 : Blo 155795 176989 := bbase (se 3 (by rfl) ⟨33185, by rfl⟩ : syracuseStep 176989 = 66371) (by norm_num)
theorem B537461 : Blo 155795 537461 := bbase (se 5 (by rfl) ⟨25193, by rfl⟩ : syracuseStep 537461 = 50387) (by norm_num)
theorem B177025 : Blo 155795 177025 := bbase (se 2 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 177025 = 132769) (by norm_num)
theorem B766853 : Blo 155795 766853 := bbase (se 4 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 766853 = 143785) (by norm_num)
theorem B177061 : Blo 155795 177061 := bbase (se 4 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 177061 = 33199) (by norm_num)
theorem B177097 : Blo 155795 177097 := bbase (se 2 (by rfl) ⟨66411, by rfl⟩ : syracuseStep 177097 = 132823) (by norm_num)
theorem B1029077 : Blo 155795 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B177133 : Blo 155795 177133 := bbase (se 3 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 177133 = 66425) (by norm_num)
theorem B898037 : Blo 155795 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B406525 : Blo 155795 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B177169 : Blo 155795 177169 := bbase (se 2 (by rfl) ⟨66438, by rfl⟩ : syracuseStep 177169 = 132877) (by norm_num)
theorem B177205 : Blo 155795 177205 := bbase (se 5 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 177205 = 16613) (by norm_num)
theorem B504917 : Blo 155795 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B177241 : Blo 155795 177241 := bbase (se 2 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 177241 = 132931) (by norm_num)
theorem B275581 : Blo 155795 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B177277 : Blo 155795 177277 := bbase (se 3 (by rfl) ⟨33239, by rfl⟩ : syracuseStep 177277 = 66479) (by norm_num)
theorem B177313 : Blo 155795 177313 := bbase (se 2 (by rfl) ⟨66492, by rfl⟩ : syracuseStep 177313 = 132985) (by norm_num)
theorem B341165 : Blo 155795 341165 := bbase (se 3 (by rfl) ⟨63968, by rfl⟩ : syracuseStep 341165 = 127937) (by norm_num)
theorem B177349 : Blo 155795 177349 := bbase (se 4 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 177349 = 33253) (by norm_num)
theorem B177385 : Blo 155795 177385 := bbase (se 2 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 177385 = 133039) (by norm_num)
theorem B177421 : Blo 155795 177421 := bbase (se 3 (by rfl) ⟨33266, by rfl⟩ : syracuseStep 177421 = 66533) (by norm_num)
theorem B537893 : Blo 155795 537893 := bbase (se 4 (by rfl) ⟨50427, by rfl⟩ : syracuseStep 537893 = 100855) (by norm_num)
theorem B177457 : Blo 155795 177457 := bbase (se 2 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 177457 = 133093) (by norm_num)
theorem B177493 : Blo 155795 177493 := bbase (se 13 (by rfl) ⟨32, by rfl⟩ : syracuseStep 177493 = 65) (by norm_num)
theorem B636277 : Blo 155795 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B800117 : Blo 155795 800117 := bbase (se 5 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 800117 = 75011) (by norm_num)
theorem B177529 : Blo 155795 177529 := bbase (se 2 (by rfl) ⟨66573, by rfl⟩ : syracuseStep 177529 = 133147) (by norm_num)
theorem B177565 : Blo 155795 177565 := bbase (se 3 (by rfl) ⟨33293, by rfl⟩ : syracuseStep 177565 = 66587) (by norm_num)
theorem B177601 : Blo 155795 177601 := bbase (se 2 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 177601 = 133201) (by norm_num)
theorem B177637 : Blo 155795 177637 := bbase (se 4 (by rfl) ⟨16653, by rfl⟩ : syracuseStep 177637 = 33307) (by norm_num)
theorem B177673 : Blo 155795 177673 := bbase (se 2 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 177673 = 133255) (by norm_num)
theorem B177709 : Blo 155795 177709 := bbase (se 3 (by rfl) ⟨33320, by rfl⟩ : syracuseStep 177709 = 66641) (by norm_num)
theorem B177745 : Blo 155795 177745 := bbase (se 2 (by rfl) ⟨66654, by rfl⟩ : syracuseStep 177745 = 133309) (by norm_num)
theorem B603733 : Blo 155795 603733 := bbase (se 8 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 603733 = 7075) (by norm_num)
theorem B177781 : Blo 155795 177781 := bbase (se 5 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 177781 = 16667) (by norm_num)
theorem B308861 : Blo 155795 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B177817 : Blo 155795 177817 := bbase (se 2 (by rfl) ⟨66681, by rfl⟩ : syracuseStep 177817 = 133363) (by norm_num)
theorem B177853 : Blo 155795 177853 := bbase (se 3 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 177853 = 66695) (by norm_num)
theorem B538325 : Blo 155795 538325 := bbase (se 7 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 538325 = 12617) (by norm_num)
theorem B177889 : Blo 155795 177889 := bbase (se 2 (by rfl) ⟨66708, by rfl⟩ : syracuseStep 177889 = 133417) (by norm_num)
theorem B341741 : Blo 155795 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B177925 : Blo 155795 177925 := bbase (se 4 (by rfl) ⟨16680, by rfl⟩ : syracuseStep 177925 = 33361) (by norm_num)
theorem B177961 : Blo 155795 177961 := bbase (se 2 (by rfl) ⟨66735, by rfl⟩ : syracuseStep 177961 = 133471) (by norm_num)
theorem B177997 : Blo 155795 177997 := bbase (se 3 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 177997 = 66749) (by norm_num)
theorem B178033 : Blo 155795 178033 := bbase (se 2 (by rfl) ⟨66762, by rfl⟩ : syracuseStep 178033 = 133525) (by norm_num)
theorem B604037 : Blo 155795 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B178069 : Blo 155795 178069 := bbase (se 6 (by rfl) ⟨4173, by rfl⟩ : syracuseStep 178069 = 8347) (by norm_num)
theorem B178105 : Blo 155795 178105 := bbase (se 2 (by rfl) ⟨66789, by rfl⟩ : syracuseStep 178105 = 133579) (by norm_num)
theorem B178141 : Blo 155795 178141 := bbase (se 3 (by rfl) ⟨33401, by rfl⟩ : syracuseStep 178141 = 66803) (by norm_num)
theorem B210925 : Blo 155795 210925 := bbase (se 3 (by rfl) ⟨39548, by rfl⟩ : syracuseStep 210925 = 79097) (by norm_num)
theorem B178177 : Blo 155795 178177 := bbase (se 2 (by rfl) ⟨66816, by rfl⟩ : syracuseStep 178177 = 133633) (by norm_num)
theorem B669701 : Blo 155795 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B178213 : Blo 155795 178213 := bbase (se 4 (by rfl) ⟨16707, by rfl⟩ : syracuseStep 178213 = 33415) (by norm_num)
theorem B178249 : Blo 155795 178249 := bbase (se 2 (by rfl) ⟨66843, by rfl⟩ : syracuseStep 178249 = 133687) (by norm_num)
theorem B178285 : Blo 155795 178285 := bbase (se 3 (by rfl) ⟨33428, by rfl⟩ : syracuseStep 178285 = 66857) (by norm_num)
theorem B1194101 : Blo 155795 1194101 := bbase (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) (by norm_num)
theorem B538757 : Blo 155795 538757 := bbase (se 4 (by rfl) ⟨50508, by rfl⟩ : syracuseStep 538757 = 101017) (by norm_num)
theorem B178321 : Blo 155795 178321 := bbase (se 2 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 178321 = 133741) (by norm_num)
theorem B899221 : Blo 155795 899221 := bbase (se 6 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 899221 = 42151) (by norm_num)
theorem B178357 : Blo 155795 178357 := bbase (se 5 (by rfl) ⟨8360, by rfl⟩ : syracuseStep 178357 = 16721) (by norm_num)
theorem B178369 : Blo 155795 178369 := bbase (se 2 (by rfl) ⟨66888, by rfl⟩ : syracuseStep 178369 = 133777) (by norm_num)
theorem B178393 : Blo 155795 178393 := bbase (se 2 (by rfl) ⟨66897, by rfl⟩ : syracuseStep 178393 = 133795) (by norm_num)
theorem B669941 : Blo 155795 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B178429 : Blo 155795 178429 := bbase (se 3 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 178429 = 66911) (by norm_num)
theorem B178465 : Blo 155795 178465 := bbase (se 2 (by rfl) ⟨66924, by rfl⟩ : syracuseStep 178465 = 133849) (by norm_num)
theorem B637253 : Blo 155795 637253 := bbase (se 4 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 637253 = 119485) (by norm_num)
theorem B178501 : Blo 155795 178501 := bbase (se 4 (by rfl) ⟨16734, by rfl⟩ : syracuseStep 178501 = 33469) (by norm_num)
theorem B178537 : Blo 155795 178537 := bbase (se 2 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 178537 = 133903) (by norm_num)
theorem B178573 : Blo 155795 178573 := bbase (se 3 (by rfl) ⟨33482, by rfl⟩ : syracuseStep 178573 = 66965) (by norm_num)
theorem B506261 : Blo 155795 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B178609 : Blo 155795 178609 := bbase (se 2 (by rfl) ⟨66978, by rfl⟩ : syracuseStep 178609 = 133957) (by norm_num)
theorem B178645 : Blo 155795 178645 := bbase (se 7 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 178645 = 4187) (by norm_num)
theorem B178681 : Blo 155795 178681 := bbase (se 2 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 178681 = 134011) (by norm_num)
theorem B178717 : Blo 155795 178717 := bbase (se 3 (by rfl) ⟨33509, by rfl⟩ : syracuseStep 178717 = 67019) (by norm_num)
theorem B539189 : Blo 155795 539189 := bbase (se 5 (by rfl) ⟨25274, by rfl⟩ : syracuseStep 539189 = 50549) (by norm_num)
theorem B178753 : Blo 155795 178753 := bbase (se 2 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 178753 = 134065) (by norm_num)
theorem B211541 : Blo 155795 211541 := bbase (se 8 (by rfl) ⟨1239, by rfl⟩ : syracuseStep 211541 = 2479) (by norm_num)
theorem B178789 : Blo 155795 178789 := bbase (se 4 (by rfl) ⟨16761, by rfl⟩ : syracuseStep 178789 = 33523) (by norm_num)
theorem B801413 : Blo 155795 801413 := bbase (se 4 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 801413 = 150265) (by norm_num)
theorem B178825 : Blo 155795 178825 := bbase (se 2 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 178825 = 134119) (by norm_num)
theorem B178861 : Blo 155795 178861 := bbase (se 3 (by rfl) ⟨33536, by rfl⟩ : syracuseStep 178861 = 67073) (by norm_num)
theorem B178897 : Blo 155795 178897 := bbase (se 2 (by rfl) ⟨67086, by rfl⟩ : syracuseStep 178897 = 134173) (by norm_num)
theorem B178933 : Blo 155795 178933 := bbase (se 5 (by rfl) ⟨8387, by rfl⟩ : syracuseStep 178933 = 16775) (by norm_num)
theorem B178969 : Blo 155795 178969 := bbase (se 2 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 178969 = 134227) (by norm_num)
theorem B179005 : Blo 155795 179005 := bbase (se 3 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 179005 = 67127) (by norm_num)
theorem B179041 : Blo 155795 179041 := bbase (se 2 (by rfl) ⟨67140, by rfl⟩ : syracuseStep 179041 = 134281) (by norm_num)
theorem B179077 : Blo 155795 179077 := bbase (se 4 (by rfl) ⟨16788, by rfl⟩ : syracuseStep 179077 = 33577) (by norm_num)
theorem B179113 : Blo 155795 179113 := bbase (se 2 (by rfl) ⟨67167, by rfl⟩ : syracuseStep 179113 = 134335) (by norm_num)
theorem B179149 : Blo 155795 179149 := bbase (se 3 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 179149 = 67181) (by norm_num)
theorem B179185 : Blo 155795 179185 := bbase (se 2 (by rfl) ⟨67194, by rfl⟩ : syracuseStep 179185 = 134389) (by norm_num)
theorem B1424405 : Blo 155795 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B179221 : Blo 155795 179221 := bbase (se 6 (by rfl) ⟨4200, by rfl⟩ : syracuseStep 179221 = 8401) (by norm_num)
theorem B179245 : Blo 155795 179245 := bbase (se 3 (by rfl) ⟨33608, by rfl⟩ : syracuseStep 179245 = 67217) (by norm_num)
theorem B179257 : Blo 155795 179257 := bbase (se 2 (by rfl) ⟨67221, by rfl⟩ : syracuseStep 179257 = 134443) (by norm_num)
theorem B179293 : Blo 155795 179293 := bbase (se 3 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 179293 = 67235) (by norm_num)
theorem B179329 : Blo 155795 179329 := bbase (se 2 (by rfl) ⟨67248, by rfl⟩ : syracuseStep 179329 = 134497) (by norm_num)
theorem B179365 : Blo 155795 179365 := bbase (se 4 (by rfl) ⟨16815, by rfl⟩ : syracuseStep 179365 = 33631) (by norm_num)
theorem B375997 : Blo 155795 375997 := bbase (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) (by norm_num)
theorem B179401 : Blo 155795 179401 := bbase (se 2 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 179401 = 134551) (by norm_num)
theorem B572645 : Blo 155795 572645 := bbase (se 4 (by rfl) ⟨53685, by rfl⟩ : syracuseStep 572645 = 107371) (by norm_num)
theorem B179437 : Blo 155795 179437 := bbase (se 3 (by rfl) ⟨33644, by rfl⟩ : syracuseStep 179437 = 67289) (by norm_num)
theorem B179473 : Blo 155795 179473 := bbase (se 2 (by rfl) ⟨67302, by rfl⟩ : syracuseStep 179473 = 134605) (by norm_num)
theorem B179509 : Blo 155795 179509 := bbase (se 5 (by rfl) ⟨8414, by rfl⟩ : syracuseStep 179509 = 16829) (by norm_num)
theorem B179545 : Blo 155795 179545 := bbase (se 2 (by rfl) ⟨67329, by rfl⟩ : syracuseStep 179545 = 134659) (by norm_num)
theorem B179569 : Blo 155795 179569 := bbase (se 2 (by rfl) ⟨67338, by rfl⟩ : syracuseStep 179569 = 134677) (by norm_num)
theorem B179581 : Blo 155795 179581 := bbase (se 3 (by rfl) ⟨33671, by rfl⟩ : syracuseStep 179581 = 67343) (by norm_num)
theorem B179617 : Blo 155795 179617 := bbase (se 2 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 179617 = 134713) (by norm_num)
theorem B179653 : Blo 155795 179653 := bbase (se 4 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 179653 = 33685) (by norm_num)
theorem B179689 : Blo 155795 179689 := bbase (se 2 (by rfl) ⟨67383, by rfl⟩ : syracuseStep 179689 = 134767) (by norm_num)
theorem B179725 : Blo 155795 179725 := bbase (se 3 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 179725 = 67397) (by norm_num)
theorem B179761 : Blo 155795 179761 := bbase (se 2 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 179761 = 134821) (by norm_num)
theorem B376613 : Blo 155795 376613 := bbase (se 4 (by rfl) ⟨35307, by rfl⟩ : syracuseStep 376613 = 70615) (by norm_num)
theorem B802709 : Blo 155795 802709 := bbase (se 6 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 802709 = 37627) (by norm_num)
theorem B606149 : Blo 155795 606149 := bbase (se 4 (by rfl) ⟨56826, by rfl⟩ : syracuseStep 606149 = 113653) (by norm_num)
theorem B901205 : Blo 155795 901205 := bbase (se 8 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 901205 = 10561) (by norm_num)
theorem B606341 : Blo 155795 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B377045 : Blo 155795 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B606437 : Blo 155795 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B213229 : Blo 155795 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B1294613 : Blo 155795 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B311693 : Blo 155795 311693 := bbase (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) (by norm_num)
theorem B213445 : Blo 155795 213445 := bbase (se 4 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 213445 = 40021) (by norm_num)
theorem B672229 : Blo 155795 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B770629 : Blo 155795 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B508837 : Blo 155795 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B804005 : Blo 155795 804005 := bbase (se 4 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 804005 = 150751) (by norm_num)
theorem B509093 : Blo 155795 509093 := bbase (se 4 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 509093 = 95455) (by norm_num)
theorem B214309 : Blo 155795 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B378245 : Blo 155795 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B214493 : Blo 155795 214493 := bbase (se 3 (by rfl) ⟨40217, by rfl⟩ : syracuseStep 214493 = 80435) (by norm_num)
theorem B443893 : Blo 155795 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B542213 : Blo 155795 542213 := bbase (se 4 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 542213 = 101665) (by norm_num)
theorem B673717 : Blo 155795 673717 := bbase (se 5 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 673717 = 63161) (by norm_num)
theorem B182197 : Blo 155795 182197 := bbase (se 5 (by rfl) ⟨8540, by rfl⟩ : syracuseStep 182197 = 17081) (by norm_num)
theorem B673733 : Blo 155795 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B215077 : Blo 155795 215077 := bbase (se 4 (by rfl) ⟨20163, by rfl⟩ : syracuseStep 215077 = 40327) (by norm_num)
theorem B247861 : Blo 155795 247861 := bbase (se 5 (by rfl) ⟨11618, by rfl⟩ : syracuseStep 247861 = 23237) (by norm_num)
theorem B215245 : Blo 155795 215245 := bbase (se 3 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 215245 = 80717) (by norm_num)
theorem B903413 : Blo 155795 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B805301 : Blo 155795 805301 := bbase (se 5 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 805301 = 75497) (by norm_num)
theorem B3263125 : Blo 155795 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B281573 : Blo 155795 281573 := bbase (se 4 (by rfl) ⟨26397, by rfl⟩ : syracuseStep 281573 = 52795) (by norm_num)
theorem B544085 : Blo 155795 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B380533 : Blo 155795 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B806597 : Blo 155795 806597 := bbase (se 4 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 806597 = 151237) (by norm_num)
theorem B380629 : Blo 155795 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B511861 : Blo 155795 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B380821 : Blo 155795 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B1527893 : Blo 155795 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B675989 : Blo 155795 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B774293 : Blo 155795 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B381149 : Blo 155795 381149 := bbase (se 3 (by rfl) ⟨71465, by rfl⟩ : syracuseStep 381149 = 142931) (by norm_num)
theorem B446741 : Blo 155795 446741 := bbase (se 6 (by rfl) ⟨10470, by rfl⟩ : syracuseStep 446741 = 20941) (by norm_num)
theorem B479861 : Blo 155795 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B381581 : Blo 155795 381581 := bbase (se 3 (by rfl) ⟨71546, by rfl⟩ : syracuseStep 381581 = 143093) (by norm_num)
theorem B250805 : Blo 155795 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B1004501 : Blo 155795 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B807893 : Blo 155795 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B316381 : Blo 155795 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B381917 : Blo 155795 381917 := bbase (se 3 (by rfl) ⟨71609, by rfl⟩ : syracuseStep 381917 = 143219) (by norm_num)
theorem B250933 : Blo 155795 250933 := bbase (se 5 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 250933 = 23525) (by norm_num)
theorem B447925 : Blo 155795 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B448085 : Blo 155795 448085 := bbase (se 8 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 448085 = 5251) (by norm_num)
theorem B1201877 : Blo 155795 1201877 := bbase (se 7 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 1201877 = 28169) (by norm_num)
theorem B284477 : Blo 155795 284477 := bbase (se 3 (by rfl) ⟨53339, by rfl⟩ : syracuseStep 284477 = 106679) (by norm_num)
theorem B448325 : Blo 155795 448325 := bbase (se 4 (by rfl) ⟨42030, by rfl⟩ : syracuseStep 448325 = 84061) (by norm_num)
theorem B251741 : Blo 155795 251741 := bbase (se 3 (by rfl) ⟨47201, by rfl⟩ : syracuseStep 251741 = 94403) (by norm_num)
theorem B284629 : Blo 155795 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B382973 : Blo 155795 382973 := bbase (se 3 (by rfl) ⟨71807, by rfl⟩ : syracuseStep 382973 = 143615) (by norm_num)
theorem B448517 : Blo 155795 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B710741 : Blo 155795 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B252029 : Blo 155795 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B481589 : Blo 155795 481589 := bbase (se 5 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 481589 = 45149) (by norm_num)
theorem B350549 : Blo 155795 350549 := bbase (se 10 (by rfl) ⟨513, by rfl⟩ : syracuseStep 350549 = 1027) (by norm_num)
theorem B350621 : Blo 155795 350621 := bbase (se 3 (by rfl) ⟨65741, by rfl⟩ : syracuseStep 350621 = 131483) (by norm_num)
theorem B350693 : Blo 155795 350693 := bbase (se 4 (by rfl) ⟨32877, by rfl⟩ : syracuseStep 350693 = 65755) (by norm_num)
theorem B252445 : Blo 155795 252445 := bbase (se 3 (by rfl) ⟨47333, by rfl⟩ : syracuseStep 252445 = 94667) (by norm_num)
theorem B350765 : Blo 155795 350765 := bbase (se 3 (by rfl) ⟨65768, by rfl⟩ : syracuseStep 350765 = 131537) (by norm_num)
theorem B285245 : Blo 155795 285245 := bbase (se 3 (by rfl) ⟨53483, by rfl⟩ : syracuseStep 285245 = 106967) (by norm_num)
theorem B350837 : Blo 155795 350837 := bbase (se 5 (by rfl) ⟨16445, by rfl⟩ : syracuseStep 350837 = 32891) (by norm_num)
theorem B350909 : Blo 155795 350909 := bbase (se 3 (by rfl) ⟨65795, by rfl⟩ : syracuseStep 350909 = 131591) (by norm_num)
theorem B350981 : Blo 155795 350981 := bbase (se 4 (by rfl) ⟨32904, by rfl⟩ : syracuseStep 350981 = 65809) (by norm_num)
theorem B187177 : Blo 155795 187177 := bbase (se 2 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 187177 = 140383) (by norm_num)
theorem B318269 : Blo 155795 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B351053 : Blo 155795 351053 := bbase (se 3 (by rfl) ⟨65822, by rfl⟩ : syracuseStep 351053 = 131645) (by norm_num)
theorem B187277 : Blo 155795 187277 := bbase (se 3 (by rfl) ⟨35114, by rfl⟩ : syracuseStep 187277 = 70229) (by norm_num)
theorem B351125 : Blo 155795 351125 := bbase (se 6 (by rfl) ⟨8229, by rfl⟩ : syracuseStep 351125 = 16459) (by norm_num)
theorem B351197 : Blo 155795 351197 := bbase (se 3 (by rfl) ⟨65849, by rfl⟩ : syracuseStep 351197 = 131699) (by norm_num)
theorem B449509 : Blo 155795 449509 := bbase (se 4 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 449509 = 84283) (by norm_num)
theorem B351269 : Blo 155795 351269 := bbase (se 4 (by rfl) ⟨32931, by rfl⟩ : syracuseStep 351269 = 65863) (by norm_num)
theorem B351341 : Blo 155795 351341 := bbase (se 3 (by rfl) ⟨65876, by rfl⟩ : syracuseStep 351341 = 131753) (by norm_num)
theorem B253085 : Blo 155795 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B351413 : Blo 155795 351413 := bbase (se 5 (by rfl) ⟨16472, by rfl⟩ : syracuseStep 351413 = 32945) (by norm_num)
theorem B351485 : Blo 155795 351485 := bbase (se 3 (by rfl) ⟨65903, by rfl⟩ : syracuseStep 351485 = 131807) (by norm_num)
theorem B351557 : Blo 155795 351557 := bbase (se 4 (by rfl) ⟨32958, by rfl⟩ : syracuseStep 351557 = 65917) (by norm_num)
theorem B351629 : Blo 155795 351629 := bbase (se 3 (by rfl) ⟨65930, by rfl⟩ : syracuseStep 351629 = 131861) (by norm_num)
theorem B253381 : Blo 155795 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B351701 : Blo 155795 351701 := bbase (se 7 (by rfl) ⟨4121, by rfl⟩ : syracuseStep 351701 = 8243) (by norm_num)
theorem B712165 : Blo 155795 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B351773 : Blo 155795 351773 := bbase (se 3 (by rfl) ⟨65957, by rfl⟩ : syracuseStep 351773 = 131915) (by norm_num)
theorem B286301 : Blo 155795 286301 := bbase (se 3 (by rfl) ⟨53681, by rfl⟩ : syracuseStep 286301 = 107363) (by norm_num)
theorem B351845 : Blo 155795 351845 := bbase (se 4 (by rfl) ⟨32985, by rfl⟩ : syracuseStep 351845 = 65971) (by norm_num)
theorem B188065 : Blo 155795 188065 := bbase (se 2 (by rfl) ⟨70524, by rfl⟩ : syracuseStep 188065 = 141049) (by norm_num)
theorem B351917 : Blo 155795 351917 := bbase (se 3 (by rfl) ⟨65984, by rfl⟩ : syracuseStep 351917 = 131969) (by norm_num)
theorem B351989 : Blo 155795 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B352061 : Blo 155795 352061 := bbase (se 3 (by rfl) ⟨66011, by rfl⟩ : syracuseStep 352061 = 132023) (by norm_num)
theorem B352133 : Blo 155795 352133 := bbase (se 4 (by rfl) ⟨33012, by rfl⟩ : syracuseStep 352133 = 66025) (by norm_num)
theorem B810917 : Blo 155795 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B319405 : Blo 155795 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B352205 : Blo 155795 352205 := bbase (se 3 (by rfl) ⟨66038, by rfl⟩ : syracuseStep 352205 = 132077) (by norm_num)
theorem B352277 : Blo 155795 352277 := bbase (se 6 (by rfl) ⟨8256, by rfl⟩ : syracuseStep 352277 = 16513) (by norm_num)
theorem B450613 : Blo 155795 450613 := bbase (se 5 (by rfl) ⟨21122, by rfl⟩ : syracuseStep 450613 = 42245) (by norm_num)
theorem B680021 : Blo 155795 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B352349 : Blo 155795 352349 := bbase (se 3 (by rfl) ⟨66065, by rfl⟩ : syracuseStep 352349 = 132131) (by norm_num)
theorem B352421 : Blo 155795 352421 := bbase (se 4 (by rfl) ⟨33039, by rfl⟩ : syracuseStep 352421 = 66079) (by norm_num)
theorem B352493 : Blo 155795 352493 := bbase (se 3 (by rfl) ⟨66092, by rfl⟩ : syracuseStep 352493 = 132185) (by norm_num)
theorem B352565 : Blo 155795 352565 := bbase (se 5 (by rfl) ⟨16526, by rfl⟩ : syracuseStep 352565 = 33053) (by norm_num)
theorem B680293 : Blo 155795 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B188777 : Blo 155795 188777 := bbase (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) (by norm_num)
theorem B352637 : Blo 155795 352637 := bbase (se 3 (by rfl) ⟨66119, by rfl⟩ : syracuseStep 352637 = 132239) (by norm_num)
theorem B352709 : Blo 155795 352709 := bbase (se 4 (by rfl) ⟨33066, by rfl⟩ : syracuseStep 352709 = 66133) (by norm_num)
theorem B352781 : Blo 155795 352781 := bbase (se 3 (by rfl) ⟨66146, by rfl⟩ : syracuseStep 352781 = 132293) (by norm_num)
theorem B352853 : Blo 155795 352853 := bbase (se 8 (by rfl) ⟨2067, by rfl⟩ : syracuseStep 352853 = 4135) (by norm_num)
theorem B287317 : Blo 155795 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B254573 : Blo 155795 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B1532533 : Blo 155795 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B352925 : Blo 155795 352925 := bbase (se 3 (by rfl) ⟨66173, by rfl⟩ : syracuseStep 352925 = 132347) (by norm_num)
theorem B189113 : Blo 155795 189113 := bbase (se 2 (by rfl) ⟨70917, by rfl⟩ : syracuseStep 189113 = 141835) (by norm_num)
theorem B352997 : Blo 155795 352997 := bbase (se 4 (by rfl) ⟨33093, by rfl⟩ : syracuseStep 352997 = 66187) (by norm_num)
theorem B353069 : Blo 155795 353069 := bbase (se 3 (by rfl) ⟨66200, by rfl⟩ : syracuseStep 353069 = 132401) (by norm_num)
theorem B189229 : Blo 155795 189229 := bbase (se 3 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 189229 = 70961) (by norm_num)
theorem B254765 : Blo 155795 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B189253 : Blo 155795 189253 := bbase (se 4 (by rfl) ⟨17742, by rfl⟩ : syracuseStep 189253 = 35485) (by norm_num)
theorem B353141 : Blo 155795 353141 := bbase (se 5 (by rfl) ⟨16553, by rfl⟩ : syracuseStep 353141 = 33107) (by norm_num)
theorem B353213 : Blo 155795 353213 := bbase (se 3 (by rfl) ⟨66227, by rfl⟩ : syracuseStep 353213 = 132455) (by norm_num)
theorem B1369045 : Blo 155795 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B1139669 : Blo 155795 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B353285 : Blo 155795 353285 := bbase (se 4 (by rfl) ⟨33120, by rfl⟩ : syracuseStep 353285 = 66241) (by norm_num)
theorem B287749 : Blo 155795 287749 := bbase (se 4 (by rfl) ⟨26976, by rfl⟩ : syracuseStep 287749 = 53953) (by norm_num)
theorem B222277 : Blo 155795 222277 := bbase (se 4 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 222277 = 41677) (by norm_num)
theorem B353357 : Blo 155795 353357 := bbase (se 3 (by rfl) ⟨66254, by rfl⟩ : syracuseStep 353357 = 132509) (by norm_num)
theorem B353429 : Blo 155795 353429 := bbase (se 6 (by rfl) ⟨8283, by rfl⟩ : syracuseStep 353429 = 16567) (by norm_num)
theorem B353501 : Blo 155795 353501 := bbase (se 3 (by rfl) ⟨66281, by rfl⟩ : syracuseStep 353501 = 132563) (by norm_num)
theorem B353573 : Blo 155795 353573 := bbase (se 4 (by rfl) ⟨33147, by rfl⟩ : syracuseStep 353573 = 66295) (by norm_num)
theorem B255293 : Blo 155795 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B353645 : Blo 155795 353645 := bbase (se 3 (by rfl) ⟨66308, by rfl⟩ : syracuseStep 353645 = 132617) (by norm_num)
theorem B353717 : Blo 155795 353717 := bbase (se 5 (by rfl) ⟨16580, by rfl⟩ : syracuseStep 353717 = 33161) (by norm_num)
theorem B353789 : Blo 155795 353789 := bbase (se 3 (by rfl) ⟨66335, by rfl⟩ : syracuseStep 353789 = 132671) (by norm_num)
theorem B189949 : Blo 155795 189949 := bbase (se 3 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 189949 = 71231) (by norm_num)
theorem B452117 : Blo 155795 452117 := bbase (se 6 (by rfl) ⟨10596, by rfl⟩ : syracuseStep 452117 = 21193) (by norm_num)
theorem B353861 : Blo 155795 353861 := bbase (se 4 (by rfl) ⟨33174, by rfl⟩ : syracuseStep 353861 = 66349) (by norm_num)
theorem B190045 : Blo 155795 190045 := bbase (se 3 (by rfl) ⟨35633, by rfl⟩ : syracuseStep 190045 = 71267) (by norm_num)
theorem B353933 : Blo 155795 353933 := bbase (se 3 (by rfl) ⟨66362, by rfl⟩ : syracuseStep 353933 = 132725) (by norm_num)
theorem B222869 : Blo 155795 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B321221 : Blo 155795 321221 := bbase (se 4 (by rfl) ⟨30114, by rfl⟩ : syracuseStep 321221 = 60229) (by norm_num)
theorem B354005 : Blo 155795 354005 := bbase (se 7 (by rfl) ⟨4148, by rfl⟩ : syracuseStep 354005 = 8297) (by norm_num)
theorem B222949 : Blo 155795 222949 := bbase (se 4 (by rfl) ⟨20901, by rfl⟩ : syracuseStep 222949 = 41803) (by norm_num)
theorem B354077 : Blo 155795 354077 := bbase (se 3 (by rfl) ⟨66389, by rfl⟩ : syracuseStep 354077 = 132779) (by norm_num)
theorem B681797 : Blo 155795 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B6022997 : Blo 155795 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B223069 : Blo 155795 223069 := bbase (se 3 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 223069 = 83651) (by norm_num)
theorem B354149 : Blo 155795 354149 := bbase (se 4 (by rfl) ⟨33201, by rfl⟩ : syracuseStep 354149 = 66403) (by norm_num)
theorem B157573 : Blo 155795 157573 := bbase (se 4 (by rfl) ⟨14772, by rfl⟩ : syracuseStep 157573 = 29545) (by norm_num)
theorem B354221 : Blo 155795 354221 := bbase (se 3 (by rfl) ⟨66416, by rfl⟩ : syracuseStep 354221 = 132833) (by norm_num)
theorem B223165 : Blo 155795 223165 := bbase (se 3 (by rfl) ⟨41843, by rfl⟩ : syracuseStep 223165 = 83687) (by norm_num)
theorem B354293 : Blo 155795 354293 := bbase (se 5 (by rfl) ⟨16607, by rfl⟩ : syracuseStep 354293 = 33215) (by norm_num)
theorem B354365 : Blo 155795 354365 := bbase (se 3 (by rfl) ⟨66443, by rfl⟩ : syracuseStep 354365 = 132887) (by norm_num)
theorem B354437 : Blo 155795 354437 := bbase (se 4 (by rfl) ⟨33228, by rfl⟩ : syracuseStep 354437 = 66457) (by norm_num)
theorem B354509 : Blo 155795 354509 := bbase (se 3 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 354509 = 132941) (by norm_num)
theorem B190709 : Blo 155795 190709 := bbase (se 5 (by rfl) ⟨8939, by rfl⟩ : syracuseStep 190709 = 17879) (by norm_num)
theorem B485621 : Blo 155795 485621 := bbase (se 5 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 485621 = 45527) (by norm_num)
theorem B354581 : Blo 155795 354581 := bbase (se 6 (by rfl) ⟨8310, by rfl⟩ : syracuseStep 354581 = 16621) (by norm_num)
theorem B190769 : Blo 155795 190769 := bbase (se 2 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 190769 = 143077) (by norm_num)
theorem B354653 : Blo 155795 354653 := bbase (se 3 (by rfl) ⟨66497, by rfl⟩ : syracuseStep 354653 = 132995) (by norm_num)
theorem B158105 : Blo 155795 158105 := bbase (se 2 (by rfl) ⟨59289, by rfl⟩ : syracuseStep 158105 = 118579) (by norm_num)
theorem B354725 : Blo 155795 354725 := bbase (se 4 (by rfl) ⟨33255, by rfl⟩ : syracuseStep 354725 = 66511) (by norm_num)
theorem B223661 : Blo 155795 223661 := bbase (se 3 (by rfl) ⟨41936, by rfl⟩ : syracuseStep 223661 = 83873) (by norm_num)
theorem B354797 : Blo 155795 354797 := bbase (se 3 (by rfl) ⟨66524, by rfl⟩ : syracuseStep 354797 = 133049) (by norm_num)
theorem B354869 : Blo 155795 354869 := bbase (se 5 (by rfl) ⟨16634, by rfl⟩ : syracuseStep 354869 = 33269) (by norm_num)
theorem B191045 : Blo 155795 191045 := bbase (se 4 (by rfl) ⟨17910, by rfl⟩ : syracuseStep 191045 = 35821) (by norm_num)
theorem B354941 : Blo 155795 354941 := bbase (se 3 (by rfl) ⟨66551, by rfl⟩ : syracuseStep 354941 = 133103) (by norm_num)
theorem B355013 : Blo 155795 355013 := bbase (se 4 (by rfl) ⟨33282, by rfl⟩ : syracuseStep 355013 = 66565) (by norm_num)
theorem B355085 : Blo 155795 355085 := bbase (se 3 (by rfl) ⟨66578, by rfl⟩ : syracuseStep 355085 = 133157) (by norm_num)
theorem B355157 : Blo 155795 355157 := bbase (se 9 (by rfl) ⟨1040, by rfl⟩ : syracuseStep 355157 = 2081) (by norm_num)
theorem B191333 : Blo 155795 191333 := bbase (se 4 (by rfl) ⟨17937, by rfl⟩ : syracuseStep 191333 = 35875) (by norm_num)
theorem B355229 : Blo 155795 355229 := bbase (se 3 (by rfl) ⟨66605, by rfl⟩ : syracuseStep 355229 = 133211) (by norm_num)
theorem B519077 : Blo 155795 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B158645 : Blo 155795 158645 := bbase (se 5 (by rfl) ⟨7436, by rfl⟩ : syracuseStep 158645 = 14873) (by norm_num)
theorem B224213 : Blo 155795 224213 := bbase (se 7 (by rfl) ⟨2627, by rfl⟩ : syracuseStep 224213 = 5255) (by norm_num)
theorem B355301 : Blo 155795 355301 := bbase (se 4 (by rfl) ⟨33309, by rfl⟩ : syracuseStep 355301 = 66619) (by norm_num)
theorem B191497 : Blo 155795 191497 := bbase (se 2 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 191497 = 143623) (by norm_num)
theorem B191525 : Blo 155795 191525 := bbase (se 4 (by rfl) ⟨17955, by rfl⟩ : syracuseStep 191525 = 35911) (by norm_num)
theorem B355373 : Blo 155795 355373 := bbase (se 3 (by rfl) ⟨66632, by rfl⟩ : syracuseStep 355373 = 133265) (by norm_num)
theorem B453701 : Blo 155795 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B355445 : Blo 155795 355445 := bbase (se 5 (by rfl) ⟨16661, by rfl⟩ : syracuseStep 355445 = 33323) (by norm_num)
theorem B191641 : Blo 155795 191641 := bbase (se 2 (by rfl) ⟨71865, by rfl⟩ : syracuseStep 191641 = 143731) (by norm_num)
theorem B257189 : Blo 155795 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B355517 : Blo 155795 355517 := bbase (se 3 (by rfl) ⟨66659, by rfl⟩ : syracuseStep 355517 = 133319) (by norm_num)
theorem B158969 : Blo 155795 158969 := bbase (se 2 (by rfl) ⟨59613, by rfl⟩ : syracuseStep 158969 = 119227) (by norm_num)
theorem B191737 : Blo 155795 191737 := bbase (se 2 (by rfl) ⟨71901, by rfl⟩ : syracuseStep 191737 = 143803) (by norm_num)
theorem B355589 : Blo 155795 355589 := bbase (se 4 (by rfl) ⟨33336, by rfl⟩ : syracuseStep 355589 = 66673) (by norm_num)
theorem B421157 : Blo 155795 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B159053 : Blo 155795 159053 := bbase (se 3 (by rfl) ⟨29822, by rfl⟩ : syracuseStep 159053 = 59645) (by norm_num)
theorem B355661 : Blo 155795 355661 := bbase (se 3 (by rfl) ⟨66686, by rfl⟩ : syracuseStep 355661 = 133373) (by norm_num)
theorem B257413 : Blo 155795 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B355733 : Blo 155795 355733 := bbase (se 6 (by rfl) ⟨8337, by rfl⟩ : syracuseStep 355733 = 16675) (by norm_num)
theorem B355805 : Blo 155795 355805 := bbase (se 3 (by rfl) ⟨66713, by rfl⟩ : syracuseStep 355805 = 133427) (by norm_num)
theorem B355877 : Blo 155795 355877 := bbase (se 4 (by rfl) ⟨33363, by rfl⟩ : syracuseStep 355877 = 66727) (by norm_num)
theorem B355949 : Blo 155795 355949 := bbase (se 3 (by rfl) ⟨66740, by rfl⟩ : syracuseStep 355949 = 133481) (by norm_num)
theorem B356021 : Blo 155795 356021 := bbase (se 5 (by rfl) ⟨16688, by rfl⟩ : syracuseStep 356021 = 33377) (by norm_num)
theorem B224965 : Blo 155795 224965 := bbase (se 4 (by rfl) ⟨21090, by rfl⟩ : syracuseStep 224965 = 42181) (by norm_num)
theorem B454373 : Blo 155795 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B356093 : Blo 155795 356093 := bbase (se 3 (by rfl) ⟨66767, by rfl⟩ : syracuseStep 356093 = 133535) (by norm_num)
theorem B356165 : Blo 155795 356165 := bbase (se 4 (by rfl) ⟨33390, by rfl⟩ : syracuseStep 356165 = 66781) (by norm_num)
theorem B356237 : Blo 155795 356237 := bbase (se 3 (by rfl) ⟨66794, by rfl⟩ : syracuseStep 356237 = 133589) (by norm_num)
theorem B356309 : Blo 155795 356309 := bbase (se 7 (by rfl) ⟨4175, by rfl⟩ : syracuseStep 356309 = 8351) (by norm_num)
theorem B815093 : Blo 155795 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B356381 : Blo 155795 356381 := bbase (se 3 (by rfl) ⟨66821, by rfl⟩ : syracuseStep 356381 = 133643) (by norm_num)
theorem B192601 : Blo 155795 192601 := bbase (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) (by norm_num)
theorem B356453 : Blo 155795 356453 := bbase (se 4 (by rfl) ⟨33417, by rfl⟩ : syracuseStep 356453 = 66835) (by norm_num)
theorem B454805 : Blo 155795 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B159913 : Blo 155795 159913 := bbase (se 2 (by rfl) ⟨59967, by rfl⟩ : syracuseStep 159913 = 119935) (by norm_num)
theorem B356525 : Blo 155795 356525 := bbase (se 3 (by rfl) ⟨66848, by rfl⟩ : syracuseStep 356525 = 133697) (by norm_num)
theorem B356597 : Blo 155795 356597 := bbase (se 5 (by rfl) ⟨16715, by rfl⟩ : syracuseStep 356597 = 33431) (by norm_num)
theorem B356669 : Blo 155795 356669 := bbase (se 3 (by rfl) ⟨66875, by rfl⟩ : syracuseStep 356669 = 133751) (by norm_num)
theorem B356741 : Blo 155795 356741 := bbase (se 4 (by rfl) ⟨33444, by rfl⟩ : syracuseStep 356741 = 66889) (by norm_num)
theorem B356813 : Blo 155795 356813 := bbase (se 3 (by rfl) ⟨66902, by rfl⟩ : syracuseStep 356813 = 133805) (by norm_num)
theorem B225757 : Blo 155795 225757 := bbase (se 3 (by rfl) ⟨42329, by rfl⟩ : syracuseStep 225757 = 84659) (by norm_num)
theorem B356885 : Blo 155795 356885 := bbase (se 6 (by rfl) ⟨8364, by rfl⟩ : syracuseStep 356885 = 16729) (by norm_num)
theorem B356957 : Blo 155795 356957 := bbase (se 3 (by rfl) ⟨66929, by rfl⟩ : syracuseStep 356957 = 133859) (by norm_num)
theorem B357029 : Blo 155795 357029 := bbase (se 4 (by rfl) ⟨33471, by rfl⟩ : syracuseStep 357029 = 66943) (by norm_num)
theorem B160481 : Blo 155795 160481 := bbase (se 2 (by rfl) ⟨60180, by rfl⟩ : syracuseStep 160481 = 120361) (by norm_num)
theorem B357101 : Blo 155795 357101 := bbase (se 3 (by rfl) ⟨66956, by rfl⟩ : syracuseStep 357101 = 133913) (by norm_num)
theorem B226093 : Blo 155795 226093 := bbase (se 3 (by rfl) ⟨42392, by rfl⟩ : syracuseStep 226093 = 84785) (by norm_num)
theorem B357173 : Blo 155795 357173 := bbase (se 5 (by rfl) ⟨16742, by rfl⟩ : syracuseStep 357173 = 33485) (by norm_num)
theorem B357245 : Blo 155795 357245 := bbase (se 3 (by rfl) ⟨66983, by rfl⟩ : syracuseStep 357245 = 133967) (by norm_num)
theorem B357317 : Blo 155795 357317 := bbase (se 4 (by rfl) ⟨33498, by rfl⟩ : syracuseStep 357317 = 66997) (by norm_num)
theorem B160741 : Blo 155795 160741 := bbase (se 4 (by rfl) ⟨15069, by rfl⟩ : syracuseStep 160741 = 30139) (by norm_num)
theorem B226309 : Blo 155795 226309 := bbase (se 4 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 226309 = 42433) (by norm_num)
theorem B357389 : Blo 155795 357389 := bbase (se 3 (by rfl) ⟨67010, by rfl⟩ : syracuseStep 357389 = 134021) (by norm_num)
theorem B357461 : Blo 155795 357461 := bbase (se 8 (by rfl) ⟨2094, by rfl⟩ : syracuseStep 357461 = 4189) (by norm_num)
theorem B357533 : Blo 155795 357533 := bbase (se 3 (by rfl) ⟨67037, by rfl⟩ : syracuseStep 357533 = 134075) (by norm_num)
theorem B357605 : Blo 155795 357605 := bbase (se 4 (by rfl) ⟨33525, by rfl⟩ : syracuseStep 357605 = 67051) (by norm_num)
theorem B357677 : Blo 155795 357677 := bbase (se 3 (by rfl) ⟨67064, by rfl⟩ : syracuseStep 357677 = 134129) (by norm_num)
theorem B1209653 : Blo 155795 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B357749 : Blo 155795 357749 := bbase (se 5 (by rfl) ⟨16769, by rfl⟩ : syracuseStep 357749 = 33539) (by norm_num)
theorem B226685 : Blo 155795 226685 := bbase (se 3 (by rfl) ⟨42503, by rfl⟩ : syracuseStep 226685 = 85007) (by norm_num)
theorem B357821 : Blo 155795 357821 := bbase (se 3 (by rfl) ⟨67091, by rfl⟩ : syracuseStep 357821 = 134183) (by norm_num)
theorem B357893 : Blo 155795 357893 := bbase (se 4 (by rfl) ⟨33552, by rfl⟩ : syracuseStep 357893 = 67105) (by norm_num)
theorem B456245 : Blo 155795 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B357965 : Blo 155795 357965 := bbase (se 3 (by rfl) ⟨67118, by rfl⟩ : syracuseStep 357965 = 134237) (by norm_num)
theorem B161357 : Blo 155795 161357 := bbase (se 3 (by rfl) ⟨30254, by rfl⟩ : syracuseStep 161357 = 60509) (by norm_num)
theorem B161389 : Blo 155795 161389 := bbase (se 3 (by rfl) ⟨30260, by rfl⟩ : syracuseStep 161389 = 60521) (by norm_num)
theorem B358037 : Blo 155795 358037 := bbase (se 6 (by rfl) ⟨8391, by rfl⟩ : syracuseStep 358037 = 16783) (by norm_num)
theorem B358109 : Blo 155795 358109 := bbase (se 3 (by rfl) ⟨67145, by rfl⟩ : syracuseStep 358109 = 134291) (by norm_num)
theorem B358181 : Blo 155795 358181 := bbase (se 4 (by rfl) ⟨33579, by rfl⟩ : syracuseStep 358181 = 67159) (by norm_num)
theorem B358253 : Blo 155795 358253 := bbase (se 3 (by rfl) ⟨67172, by rfl⟩ : syracuseStep 358253 = 134345) (by norm_num)
theorem B358325 : Blo 155795 358325 := bbase (se 5 (by rfl) ⟨16796, by rfl⟩ : syracuseStep 358325 = 33593) (by norm_num)
theorem B358397 : Blo 155795 358397 := bbase (se 3 (by rfl) ⟨67199, by rfl⟩ : syracuseStep 358397 = 134399) (by norm_num)
theorem B358469 : Blo 155795 358469 := bbase (se 4 (by rfl) ⟨33606, by rfl⟩ : syracuseStep 358469 = 67213) (by norm_num)
theorem B358541 : Blo 155795 358541 := bbase (se 3 (by rfl) ⟨67226, by rfl⟩ : syracuseStep 358541 = 134453) (by norm_num)
theorem B751781 : Blo 155795 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B358613 : Blo 155795 358613 := bbase (se 7 (by rfl) ⟨4202, by rfl⟩ : syracuseStep 358613 = 8405) (by norm_num)
theorem B358685 : Blo 155795 358685 := bbase (se 3 (by rfl) ⟨67253, by rfl⟩ : syracuseStep 358685 = 134507) (by norm_num)
theorem B424261 : Blo 155795 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B162145 : Blo 155795 162145 := bbase (se 2 (by rfl) ⟨60804, by rfl⟩ : syracuseStep 162145 = 121609) (by norm_num)
theorem B358757 : Blo 155795 358757 := bbase (se 4 (by rfl) ⟨33633, by rfl⟩ : syracuseStep 358757 = 67267) (by norm_num)
theorem B358829 : Blo 155795 358829 := bbase (se 3 (by rfl) ⟨67280, by rfl⟩ : syracuseStep 358829 = 134561) (by norm_num)
theorem B358901 : Blo 155795 358901 := bbase (se 5 (by rfl) ⟨16823, by rfl⟩ : syracuseStep 358901 = 33647) (by norm_num)
theorem B358973 : Blo 155795 358973 := bbase (se 3 (by rfl) ⟨67307, by rfl⟩ : syracuseStep 358973 = 134615) (by norm_num)
theorem B359045 : Blo 155795 359045 := bbase (se 4 (by rfl) ⟨33660, by rfl⟩ : syracuseStep 359045 = 67321) (by norm_num)
theorem B359117 : Blo 155795 359117 := bbase (se 3 (by rfl) ⟨67334, by rfl⟩ : syracuseStep 359117 = 134669) (by norm_num)
theorem B359189 : Blo 155795 359189 := bbase (se 6 (by rfl) ⟨8418, by rfl⟩ : syracuseStep 359189 = 16837) (by norm_num)
theorem B359261 : Blo 155795 359261 := bbase (se 3 (by rfl) ⟨67361, by rfl⟩ : syracuseStep 359261 = 134723) (by norm_num)
theorem B1014677 : Blo 155795 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B359333 : Blo 155795 359333 := bbase (se 4 (by rfl) ⟨33687, by rfl⟩ : syracuseStep 359333 = 67375) (by norm_num)
theorem B359405 : Blo 155795 359405 := bbase (se 3 (by rfl) ⟨67388, by rfl⟩ : syracuseStep 359405 = 134777) (by norm_num)
theorem B359477 : Blo 155795 359477 := bbase (se 5 (by rfl) ⟨16850, by rfl⟩ : syracuseStep 359477 = 33701) (by norm_num)
theorem B261397 : Blo 155795 261397 := bbase (se 6 (by rfl) ⟨6126, by rfl⟩ : syracuseStep 261397 = 12253) (by norm_num)
theorem B359869 : Blo 155795 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B1375829 : Blo 155795 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B720485 : Blo 155795 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B360389 : Blo 155795 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B1310833 : Blo 155795 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B2064781 : Blo 155795 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B3211973 : Blo 155795 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B262993 : Blo 155795 262993 := bstep (se 2 (by rfl) ⟨98622, by rfl⟩ : syracuseStep 262993 = 197245) B197245
theorem B263027 : Blo 155795 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B852869 : Blo 155795 852869 := bstep (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) B159913
theorem B263155 : Blo 155795 263155 := bstep (se 1 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 263155 = 394733) B394733
theorem B197635 : Blo 155795 197635 := bstep (se 1 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 197635 = 296453) B296453
theorem B361475 : Blo 155795 361475 := bstep (se 1 (by rfl) ⟨271106, by rfl⟩ : syracuseStep 361475 = 542213) B542213
theorem B951301 : Blo 155795 951301 := bstep (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) B178369
theorem B197731 : Blo 155795 197731 := bstep (se 1 (by rfl) ⟨148298, by rfl⟩ : syracuseStep 197731 = 296597) B296597
theorem B263297 : Blo 155795 263297 := bstep (se 2 (by rfl) ⟨98736, by rfl⟩ : syracuseStep 263297 = 197473) B197473
theorem B263425 : Blo 155795 263425 := bstep (se 2 (by rfl) ⟨98784, by rfl⟩ : syracuseStep 263425 = 197569) B197569
theorem B263459 : Blo 155795 263459 := bstep (se 1 (by rfl) ⟨197594, by rfl⟩ : syracuseStep 263459 = 395189) B395189
theorem B1017137 : Blo 155795 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B263587 : Blo 155795 263587 := bstep (se 1 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 263587 = 395381) B395381
theorem B296369 : Blo 155795 296369 := bstep (se 2 (by rfl) ⟨111138, by rfl⟩ : syracuseStep 296369 = 222277) B222277
theorem B263729 : Blo 155795 263729 := bstep (se 2 (by rfl) ⟨98898, by rfl⟩ : syracuseStep 263729 = 197797) B197797
theorem B525905 : Blo 155795 525905 := bstep (se 2 (by rfl) ⟨197214, by rfl⟩ : syracuseStep 525905 = 394429) B394429
theorem B198227 : Blo 155795 198227 := bstep (se 1 (by rfl) ⟨148670, by rfl⟩ : syracuseStep 198227 = 297341) B297341
theorem B394865 : Blo 155795 394865 := bstep (se 2 (by rfl) ⟨148074, by rfl⟩ : syracuseStep 394865 = 296149) B296149
theorem B394915 : Blo 155795 394915 := bstep (se 1 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 394915 = 592373) B592373
theorem B263857 : Blo 155795 263857 := bstep (se 2 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 263857 = 197893) B197893
theorem B2262725 : Blo 155795 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B886477 : Blo 155795 886477 := bstep (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) B332429
theorem B263891 : Blo 155795 263891 := bstep (se 1 (by rfl) ⟨197918, by rfl⟩ : syracuseStep 263891 = 395837) B395837
theorem B395057 : Blo 155795 395057 := bstep (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) B296293
theorem B264019 : Blo 155795 264019 := bstep (se 1 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 264019 = 396029) B396029
theorem B427949 : Blo 155795 427949 := bstep (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) B160481
theorem B264161 : Blo 155795 264161 := bstep (se 2 (by rfl) ⟨99060, by rfl⟩ : syracuseStep 264161 = 198121) B198121
theorem B591857 : Blo 155795 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B264289 : Blo 155795 264289 := bstep (se 2 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 264289 = 198217) B198217
theorem B526445 : Blo 155795 526445 := bstep (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) B197417
theorem B264323 : Blo 155795 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B526499 : Blo 155795 526499 := bstep (se 1 (by rfl) ⟨394874, by rfl⟩ : syracuseStep 526499 = 789749) B789749
theorem B362723 : Blo 155795 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B264451 : Blo 155795 264451 := bstep (se 1 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 264451 = 396677) B396677
theorem B198931 : Blo 155795 198931 := bstep (se 1 (by rfl) ⟨149198, by rfl⟩ : syracuseStep 198931 = 298397) B298397
theorem B297265 : Blo 155795 297265 := bstep (se 2 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 297265 = 222949) B222949
theorem B919907 : Blo 155795 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B199027 : Blo 155795 199027 := bstep (se 1 (by rfl) ⟨149270, by rfl⟩ : syracuseStep 199027 = 298541) B298541
theorem B264593 : Blo 155795 264593 := bstep (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) B198445
theorem B526769 : Blo 155795 526769 := bstep (se 2 (by rfl) ⟨197538, by rfl⟩ : syracuseStep 526769 = 395077) B395077
theorem B297425 : Blo 155795 297425 := bstep (se 2 (by rfl) ⟨111534, by rfl⟩ : syracuseStep 297425 = 223069) B223069
theorem B264721 : Blo 155795 264721 := bstep (se 2 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 264721 = 198541) B198541
theorem B264755 : Blo 155795 264755 := bstep (se 1 (by rfl) ⟨198566, by rfl⟩ : syracuseStep 264755 = 397133) B397133
theorem B2034229 : Blo 155795 2034229 := bstep (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) B190709
theorem B756337 : Blo 155795 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B264883 : Blo 155795 264883 := bstep (se 1 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 264883 = 397325) B397325
theorem B1018595 : Blo 155795 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B330481 : Blo 155795 330481 := bstep (se 2 (by rfl) ⟨123930, by rfl⟩ : syracuseStep 330481 = 247861) B247861
theorem B887557 : Blo 155795 887557 := bstep (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) B166417
theorem B396049 : Blo 155795 396049 := bstep (se 2 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 396049 = 297037) B297037
theorem B265025 : Blo 155795 265025 := bstep (se 2 (by rfl) ⟨99384, by rfl⟩ : syracuseStep 265025 = 198769) B198769
theorem B1084229 : Blo 155795 1084229 := bstep (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) B203293
theorem B297827 : Blo 155795 297827 := bstep (se 1 (by rfl) ⟨223370, by rfl⟩ : syracuseStep 297827 = 446741) B446741
theorem B199523 : Blo 155795 199523 := bstep (se 1 (by rfl) ⟨149642, by rfl⟩ : syracuseStep 199523 = 299285) B299285
theorem B789425 : Blo 155795 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B265153 : Blo 155795 265153 := bstep (se 2 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 265153 = 198865) B198865
theorem B527309 : Blo 155795 527309 := bstep (se 3 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 527309 = 197741) B197741
theorem B265187 : Blo 155795 265187 := bstep (se 1 (by rfl) ⟨198890, by rfl⟩ : syracuseStep 265187 = 397781) B397781
theorem B527363 : Blo 155795 527363 := bstep (se 1 (by rfl) ⟨395522, by rfl⟩ : syracuseStep 527363 = 791045) B791045
theorem B396323 : Blo 155795 396323 := bstep (se 1 (by rfl) ⟨297242, by rfl⟩ : syracuseStep 396323 = 594485) B594485
theorem B265315 : Blo 155795 265315 := bstep (se 1 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 265315 = 397973) B397973
theorem B396515 : Blo 155795 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B265457 : Blo 155795 265457 := bstep (se 2 (by rfl) ⟨99546, by rfl⟩ : syracuseStep 265457 = 199093) B199093
theorem B527633 : Blo 155795 527633 := bstep (se 2 (by rfl) ⟨197862, by rfl⟩ : syracuseStep 527633 = 395725) B395725
theorem B167203 : Blo 155795 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B265585 : Blo 155795 265585 := bstep (se 2 (by rfl) ⟨99594, by rfl⟩ : syracuseStep 265585 = 199189) B199189
theorem B265619 : Blo 155795 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B593315 : Blo 155795 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B265747 : Blo 155795 265747 := bstep (se 1 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 265747 = 398621) B398621
theorem B200227 : Blo 155795 200227 := bstep (se 1 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 200227 = 300341) B300341
theorem B200323 : Blo 155795 200323 := bstep (se 1 (by rfl) ⟨150242, by rfl⟩ : syracuseStep 200323 = 300485) B300485
theorem B265889 : Blo 155795 265889 := bstep (se 2 (by rfl) ⟨99708, by rfl⟩ : syracuseStep 265889 = 199417) B199417
theorem B298723 : Blo 155795 298723 := bstep (se 1 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 298723 = 448085) B448085
theorem B266017 : Blo 155795 266017 := bstep (se 2 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 266017 = 199513) B199513
theorem B528173 : Blo 155795 528173 := bstep (se 3 (by rfl) ⟨99032, by rfl⟩ : syracuseStep 528173 = 198065) B198065
theorem B266051 : Blo 155795 266051 := bstep (se 1 (by rfl) ⟨199538, by rfl⟩ : syracuseStep 266051 = 399077) B399077
theorem B528227 : Blo 155795 528227 := bstep (se 1 (by rfl) ⟨396170, by rfl⟩ : syracuseStep 528227 = 792341) B792341
theorem B298883 : Blo 155795 298883 := bstep (se 1 (by rfl) ⟨224162, by rfl⟩ : syracuseStep 298883 = 448325) B448325
theorem B167827 : Blo 155795 167827 := bstep (se 1 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 167827 = 251741) B251741
theorem B266179 : Blo 155795 266179 := bstep (se 1 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 266179 = 399269) B399269
theorem B266321 : Blo 155795 266321 := bstep (se 2 (by rfl) ⟨99870, by rfl⟩ : syracuseStep 266321 = 199741) B199741
theorem B528497 : Blo 155795 528497 := bstep (se 2 (by rfl) ⟨198186, by rfl⟩ : syracuseStep 528497 = 396373) B396373
theorem B200819 : Blo 155795 200819 := bstep (se 1 (by rfl) ⟨150614, by rfl⟩ : syracuseStep 200819 = 301229) B301229
theorem B397457 : Blo 155795 397457 := bstep (se 2 (by rfl) ⟨149046, by rfl⟩ : syracuseStep 397457 = 298093) B298093
theorem B397507 : Blo 155795 397507 := bstep (se 1 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 397507 = 596261) B596261
theorem B430285 : Blo 155795 430285 := bstep (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) B161357
theorem B266449 : Blo 155795 266449 := bstep (se 2 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 266449 = 199837) B199837
theorem B233699 : Blo 155795 233699 := bstep (se 1 (by rfl) ⟨175274, by rfl⟩ : syracuseStep 233699 = 350549) B350549
theorem B266483 : Blo 155795 266483 := bstep (se 1 (by rfl) ⟨199862, by rfl⟩ : syracuseStep 266483 = 399725) B399725
theorem B233729 : Blo 155795 233729 := bstep (se 2 (by rfl) ⟨87648, by rfl⟩ : syracuseStep 233729 = 175297) B175297
theorem B233747 : Blo 155795 233747 := bstep (se 1 (by rfl) ⟨175310, by rfl⟩ : syracuseStep 233747 = 350621) B350621
theorem B233777 : Blo 155795 233777 := bstep (se 2 (by rfl) ⟨87666, by rfl⟩ : syracuseStep 233777 = 175333) B175333
theorem B233795 : Blo 155795 233795 := bstep (se 1 (by rfl) ⟨175346, by rfl⟩ : syracuseStep 233795 = 350693) B350693
theorem B397649 : Blo 155795 397649 := bstep (se 2 (by rfl) ⟨149118, by rfl⟩ : syracuseStep 397649 = 298237) B298237
theorem B233825 : Blo 155795 233825 := bstep (se 2 (by rfl) ⟨87684, by rfl⟩ : syracuseStep 233825 = 175369) B175369
theorem B790883 : Blo 155795 790883 := bstep (se 1 (by rfl) ⟨593162, by rfl⟩ : syracuseStep 790883 = 1186325) B1186325
theorem B233843 : Blo 155795 233843 := bstep (se 1 (by rfl) ⟨175382, by rfl⟩ : syracuseStep 233843 = 350765) B350765
theorem B266611 : Blo 155795 266611 := bstep (se 1 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 266611 = 399917) B399917
theorem B594317 : Blo 155795 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B233873 : Blo 155795 233873 := bstep (se 2 (by rfl) ⟨87702, by rfl⟩ : syracuseStep 233873 = 175405) B175405
theorem B233891 : Blo 155795 233891 := bstep (se 1 (by rfl) ⟨175418, by rfl⟩ : syracuseStep 233891 = 350837) B350837
theorem B233921 : Blo 155795 233921 := bstep (se 2 (by rfl) ⟨87720, by rfl⟩ : syracuseStep 233921 = 175441) B175441
theorem B233939 : Blo 155795 233939 := bstep (se 1 (by rfl) ⟨175454, by rfl⟩ : syracuseStep 233939 = 350909) B350909
theorem B233969 : Blo 155795 233969 := bstep (se 2 (by rfl) ⟨87738, by rfl⟩ : syracuseStep 233969 = 175477) B175477
theorem B266753 : Blo 155795 266753 := bstep (se 2 (by rfl) ⟨100032, by rfl⟩ : syracuseStep 266753 = 200065) B200065
theorem B233987 : Blo 155795 233987 := bstep (se 1 (by rfl) ⟨175490, by rfl⟩ : syracuseStep 233987 = 350981) B350981
theorem B234017 : Blo 155795 234017 := bstep (se 2 (by rfl) ⟨87756, by rfl⟩ : syracuseStep 234017 = 175513) B175513
theorem B234035 : Blo 155795 234035 := bstep (se 1 (by rfl) ⟨175526, by rfl⟩ : syracuseStep 234035 = 351053) B351053
theorem B234065 : Blo 155795 234065 := bstep (se 2 (by rfl) ⟨87774, by rfl⟩ : syracuseStep 234065 = 175549) B175549
theorem B234083 : Blo 155795 234083 := bstep (se 1 (by rfl) ⟨175562, by rfl⟩ : syracuseStep 234083 = 351125) B351125
theorem B234113 : Blo 155795 234113 := bstep (se 2 (by rfl) ⟨87792, by rfl⟩ : syracuseStep 234113 = 175585) B175585
theorem B266881 : Blo 155795 266881 := bstep (se 2 (by rfl) ⟨100080, by rfl⟩ : syracuseStep 266881 = 200161) B200161
theorem B529037 : Blo 155795 529037 := bstep (se 3 (by rfl) ⟨99194, by rfl⟩ : syracuseStep 529037 = 198389) B198389
theorem B234131 : Blo 155795 234131 := bstep (se 1 (by rfl) ⟨175598, by rfl⟩ : syracuseStep 234131 = 351197) B351197
theorem B266915 : Blo 155795 266915 := bstep (se 1 (by rfl) ⟨200186, by rfl⟩ : syracuseStep 266915 = 400373) B400373
theorem B234161 : Blo 155795 234161 := bstep (se 2 (by rfl) ⟨87810, by rfl⟩ : syracuseStep 234161 = 175621) B175621
theorem B234179 : Blo 155795 234179 := bstep (se 1 (by rfl) ⟨175634, by rfl⟩ : syracuseStep 234179 = 351269) B351269
theorem B529091 : Blo 155795 529091 := bstep (se 1 (by rfl) ⟨396818, by rfl⟩ : syracuseStep 529091 = 793637) B793637
theorem B889541 : Blo 155795 889541 := bstep (se 4 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 889541 = 166789) B166789
theorem B234209 : Blo 155795 234209 := bstep (se 2 (by rfl) ⟨87828, by rfl⟩ : syracuseStep 234209 = 175657) B175657
theorem B234227 : Blo 155795 234227 := bstep (se 1 (by rfl) ⟨175670, by rfl⟩ : syracuseStep 234227 = 351341) B351341
theorem B234257 : Blo 155795 234257 := bstep (se 2 (by rfl) ⟨87846, by rfl⟩ : syracuseStep 234257 = 175693) B175693
theorem B234275 : Blo 155795 234275 := bstep (se 1 (by rfl) ⟨175706, by rfl⟩ : syracuseStep 234275 = 351413) B351413
theorem B267043 : Blo 155795 267043 := bstep (se 1 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 267043 = 400565) B400565
theorem B201523 : Blo 155795 201523 := bstep (se 1 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 201523 = 302285) B302285
theorem B234305 : Blo 155795 234305 := bstep (se 2 (by rfl) ⟨87864, by rfl⟩ : syracuseStep 234305 = 175729) B175729
theorem B758605 : Blo 155795 758605 := bstep (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) B284477
theorem B234323 : Blo 155795 234323 := bstep (se 1 (by rfl) ⟨175742, by rfl⟩ : syracuseStep 234323 = 351485) B351485
theorem B234353 : Blo 155795 234353 := bstep (se 2 (by rfl) ⟨87882, by rfl⟩ : syracuseStep 234353 = 175765) B175765
theorem B234371 : Blo 155795 234371 := bstep (se 1 (by rfl) ⟨175778, by rfl⟩ : syracuseStep 234371 = 351557) B351557
theorem B201619 : Blo 155795 201619 := bstep (se 1 (by rfl) ⟨151214, by rfl⟩ : syracuseStep 201619 = 302429) B302429
theorem B234401 : Blo 155795 234401 := bstep (se 2 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 234401 = 175801) B175801
theorem B299953 : Blo 155795 299953 := bstep (se 2 (by rfl) ⟨112482, by rfl⟩ : syracuseStep 299953 = 224965) B224965
theorem B267185 : Blo 155795 267185 := bstep (se 2 (by rfl) ⟨100194, by rfl⟩ : syracuseStep 267185 = 200389) B200389
theorem B234419 : Blo 155795 234419 := bstep (se 1 (by rfl) ⟨175814, by rfl⟩ : syracuseStep 234419 = 351629) B351629
theorem B234449 : Blo 155795 234449 := bstep (se 2 (by rfl) ⟨87918, by rfl⟩ : syracuseStep 234449 = 175837) B175837
theorem B529361 : Blo 155795 529361 := bstep (se 2 (by rfl) ⟨198510, by rfl⟩ : syracuseStep 529361 = 397021) B397021
theorem B234467 : Blo 155795 234467 := bstep (se 1 (by rfl) ⟨175850, by rfl⟩ : syracuseStep 234467 = 351701) B351701
theorem B234497 : Blo 155795 234497 := bstep (se 2 (by rfl) ⟨87936, by rfl⟩ : syracuseStep 234497 = 175873) B175873
theorem B234515 : Blo 155795 234515 := bstep (se 1 (by rfl) ⟨175886, by rfl⟩ : syracuseStep 234515 = 351773) B351773
theorem B234545 : Blo 155795 234545 := bstep (se 2 (by rfl) ⟨87954, by rfl⟩ : syracuseStep 234545 = 175909) B175909
theorem B267313 : Blo 155795 267313 := bstep (se 2 (by rfl) ⟨100242, by rfl⟩ : syracuseStep 267313 = 200485) B200485
theorem B234563 : Blo 155795 234563 := bstep (se 1 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 234563 = 351845) B351845
theorem B267347 : Blo 155795 267347 := bstep (se 1 (by rfl) ⟨200510, by rfl⟩ : syracuseStep 267347 = 401021) B401021
theorem B234593 : Blo 155795 234593 := bstep (se 2 (by rfl) ⟨87972, by rfl⟩ : syracuseStep 234593 = 175945) B175945
theorem B1184867 : Blo 155795 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B234611 : Blo 155795 234611 := bstep (se 1 (by rfl) ⟨175958, by rfl⟩ : syracuseStep 234611 = 351917) B351917
theorem B791693 : Blo 155795 791693 := bstep (se 3 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 791693 = 296885) B296885
theorem B234641 : Blo 155795 234641 := bstep (se 2 (by rfl) ⟨87990, by rfl⟩ : syracuseStep 234641 = 175981) B175981
theorem B234659 : Blo 155795 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B234689 : Blo 155795 234689 := bstep (se 2 (by rfl) ⟨88008, by rfl⟩ : syracuseStep 234689 = 176017) B176017
theorem B234707 : Blo 155795 234707 := bstep (se 1 (by rfl) ⟨176030, by rfl⟩ : syracuseStep 234707 = 352061) B352061
theorem B267475 : Blo 155795 267475 := bstep (se 1 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 267475 = 401213) B401213
theorem B234737 : Blo 155795 234737 := bstep (se 2 (by rfl) ⟨88026, by rfl⟩ : syracuseStep 234737 = 176053) B176053
theorem B234755 : Blo 155795 234755 := bstep (se 1 (by rfl) ⟨176066, by rfl⟩ : syracuseStep 234755 = 352133) B352133
theorem B234785 : Blo 155795 234785 := bstep (se 2 (by rfl) ⟨88044, by rfl⟩ : syracuseStep 234785 = 176089) B176089
theorem B398641 : Blo 155795 398641 := bstep (se 2 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 398641 = 298981) B298981
theorem B234803 : Blo 155795 234803 := bstep (se 1 (by rfl) ⟨176102, by rfl⟩ : syracuseStep 234803 = 352205) B352205
theorem B1021261 : Blo 155795 1021261 := bstep (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) B382973
theorem B234833 : Blo 155795 234833 := bstep (se 2 (by rfl) ⟨88062, by rfl⟩ : syracuseStep 234833 = 176125) B176125
theorem B267617 : Blo 155795 267617 := bstep (se 2 (by rfl) ⟨100356, by rfl⟩ : syracuseStep 267617 = 200713) B200713
theorem B234851 : Blo 155795 234851 := bstep (se 1 (by rfl) ⟨176138, by rfl⟩ : syracuseStep 234851 = 352277) B352277
theorem B234881 : Blo 155795 234881 := bstep (se 2 (by rfl) ⟨88080, by rfl⟩ : syracuseStep 234881 = 176161) B176161
theorem B202115 : Blo 155795 202115 := bstep (se 1 (by rfl) ⟨151586, by rfl⟩ : syracuseStep 202115 = 303173) B303173
theorem B234899 : Blo 155795 234899 := bstep (se 1 (by rfl) ⟨176174, by rfl⟩ : syracuseStep 234899 = 352349) B352349
theorem B234929 : Blo 155795 234929 := bstep (se 2 (by rfl) ⟨88098, by rfl⟩ : syracuseStep 234929 = 176197) B176197
theorem B234947 : Blo 155795 234947 := bstep (se 1 (by rfl) ⟨176210, by rfl⟩ : syracuseStep 234947 = 352421) B352421
theorem B234977 : Blo 155795 234977 := bstep (se 2 (by rfl) ⟨88116, by rfl⟩ : syracuseStep 234977 = 176233) B176233
theorem B267745 : Blo 155795 267745 := bstep (se 2 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 267745 = 200809) B200809
theorem B529901 : Blo 155795 529901 := bstep (se 3 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 529901 = 198713) B198713
theorem B234995 : Blo 155795 234995 := bstep (se 1 (by rfl) ⟨176246, by rfl⟩ : syracuseStep 234995 = 352493) B352493
theorem B267779 : Blo 155795 267779 := bstep (se 1 (by rfl) ⟨200834, by rfl⟩ : syracuseStep 267779 = 401669) B401669
theorem B235025 : Blo 155795 235025 := bstep (se 2 (by rfl) ⟨88134, by rfl⟩ : syracuseStep 235025 = 176269) B176269
theorem B235043 : Blo 155795 235043 := bstep (se 1 (by rfl) ⟨176282, by rfl⟩ : syracuseStep 235043 = 352565) B352565
theorem B529955 : Blo 155795 529955 := bstep (se 1 (by rfl) ⟨397466, by rfl⟩ : syracuseStep 529955 = 794933) B794933
theorem B235073 : Blo 155795 235073 := bstep (se 2 (by rfl) ⟨88152, by rfl⟩ : syracuseStep 235073 = 176305) B176305
theorem B398915 : Blo 155795 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B235091 : Blo 155795 235091 := bstep (se 1 (by rfl) ⟨176318, by rfl⟩ : syracuseStep 235091 = 352637) B352637
theorem B235121 : Blo 155795 235121 := bstep (se 2 (by rfl) ⟨88170, by rfl⟩ : syracuseStep 235121 = 176341) B176341
theorem B235139 : Blo 155795 235139 := bstep (se 1 (by rfl) ⟨176354, by rfl⟩ : syracuseStep 235139 = 352709) B352709
theorem B267907 : Blo 155795 267907 := bstep (se 1 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 267907 = 401861) B401861
theorem B235169 : Blo 155795 235169 := bstep (se 2 (by rfl) ⟨88188, by rfl⟩ : syracuseStep 235169 = 176377) B176377
theorem B235187 : Blo 155795 235187 := bstep (se 1 (by rfl) ⟨176390, by rfl⟩ : syracuseStep 235187 = 352781) B352781
theorem B235217 : Blo 155795 235217 := bstep (se 2 (by rfl) ⟨88206, by rfl⟩ : syracuseStep 235217 = 176413) B176413
theorem B235235 : Blo 155795 235235 := bstep (se 1 (by rfl) ⟨176426, by rfl⟩ : syracuseStep 235235 = 352853) B352853
theorem B169715 : Blo 155795 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B235265 : Blo 155795 235265 := bstep (se 2 (by rfl) ⟨88224, by rfl⟩ : syracuseStep 235265 = 176449) B176449
theorem B399107 : Blo 155795 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B2004749 : Blo 155795 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B268049 : Blo 155795 268049 := bstep (se 2 (by rfl) ⟨100518, by rfl⟩ : syracuseStep 268049 = 201037) B201037
theorem B235283 : Blo 155795 235283 := bstep (se 1 (by rfl) ⟨176462, by rfl⟩ : syracuseStep 235283 = 352925) B352925
theorem B235313 : Blo 155795 235313 := bstep (se 2 (by rfl) ⟨88242, by rfl⟩ : syracuseStep 235313 = 176485) B176485
theorem B530225 : Blo 155795 530225 := bstep (se 2 (by rfl) ⟨198834, by rfl⟩ : syracuseStep 530225 = 397669) B397669
theorem B235331 : Blo 155795 235331 := bstep (se 1 (by rfl) ⟨176498, by rfl⟩ : syracuseStep 235331 = 352997) B352997
theorem B235361 : Blo 155795 235361 := bstep (se 2 (by rfl) ⟨88260, by rfl⟩ : syracuseStep 235361 = 176521) B176521
theorem B235379 : Blo 155795 235379 := bstep (se 1 (by rfl) ⟨176534, by rfl⟩ : syracuseStep 235379 = 353069) B353069
theorem B235409 : Blo 155795 235409 := bstep (se 2 (by rfl) ⟨88278, by rfl⟩ : syracuseStep 235409 = 176557) B176557
theorem B268177 : Blo 155795 268177 := bstep (se 2 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 268177 = 201133) B201133
theorem B235427 : Blo 155795 235427 := bstep (se 1 (by rfl) ⟨176570, by rfl⟩ : syracuseStep 235427 = 353141) B353141
theorem B268211 : Blo 155795 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B235457 : Blo 155795 235457 := bstep (se 2 (by rfl) ⟨88296, by rfl⟩ : syracuseStep 235457 = 176593) B176593
theorem B301009 : Blo 155795 301009 := bstep (se 2 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 301009 = 225757) B225757
theorem B235475 : Blo 155795 235475 := bstep (se 1 (by rfl) ⟨176606, by rfl⟩ : syracuseStep 235475 = 353213) B353213
theorem B759779 : Blo 155795 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B235505 : Blo 155795 235505 := bstep (se 2 (by rfl) ⟨88314, by rfl⟩ : syracuseStep 235505 = 176629) B176629
theorem B235523 : Blo 155795 235523 := bstep (se 1 (by rfl) ⟨176642, by rfl⟩ : syracuseStep 235523 = 353285) B353285
theorem B235553 : Blo 155795 235553 := bstep (se 2 (by rfl) ⟨88332, by rfl⟩ : syracuseStep 235553 = 176665) B176665
theorem B235571 : Blo 155795 235571 := bstep (se 1 (by rfl) ⟨176678, by rfl⟩ : syracuseStep 235571 = 353357) B353357
theorem B268339 : Blo 155795 268339 := bstep (se 1 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 268339 = 402509) B402509
theorem B235601 : Blo 155795 235601 := bstep (se 2 (by rfl) ⟨88350, by rfl⟩ : syracuseStep 235601 = 176701) B176701
theorem B235619 : Blo 155795 235619 := bstep (se 1 (by rfl) ⟨176714, by rfl⟩ : syracuseStep 235619 = 353429) B353429
theorem B235649 : Blo 155795 235649 := bstep (se 2 (by rfl) ⟨88368, by rfl⟩ : syracuseStep 235649 = 176737) B176737
theorem B235667 : Blo 155795 235667 := bstep (se 1 (by rfl) ⟨176750, by rfl⟩ : syracuseStep 235667 = 353501) B353501
theorem B235697 : Blo 155795 235697 := bstep (se 2 (by rfl) ⟨88386, by rfl⟩ : syracuseStep 235697 = 176773) B176773
theorem B268481 : Blo 155795 268481 := bstep (se 2 (by rfl) ⟨100680, by rfl⟩ : syracuseStep 268481 = 201361) B201361
theorem B235715 : Blo 155795 235715 := bstep (se 1 (by rfl) ⟨176786, by rfl⟩ : syracuseStep 235715 = 353573) B353573
theorem B1808581 : Blo 155795 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B170195 : Blo 155795 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B235745 : Blo 155795 235745 := bstep (se 2 (by rfl) ⟨88404, by rfl⟩ : syracuseStep 235745 = 176809) B176809
theorem B1775843 : Blo 155795 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B235763 : Blo 155795 235763 := bstep (se 1 (by rfl) ⟨176822, by rfl⟩ : syracuseStep 235763 = 353645) B353645
theorem B235793 : Blo 155795 235793 := bstep (se 2 (by rfl) ⟨88422, by rfl⟩ : syracuseStep 235793 = 176845) B176845
theorem B235811 : Blo 155795 235811 := bstep (se 1 (by rfl) ⟨176858, by rfl⟩ : syracuseStep 235811 = 353717) B353717
theorem B268609 : Blo 155795 268609 := bstep (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) B201457
theorem B235841 : Blo 155795 235841 := bstep (se 2 (by rfl) ⟨88440, by rfl⟩ : syracuseStep 235841 = 176881) B176881
theorem B530765 : Blo 155795 530765 := bstep (se 3 (by rfl) ⟨99518, by rfl⟩ : syracuseStep 530765 = 199037) B199037
theorem B235859 : Blo 155795 235859 := bstep (se 1 (by rfl) ⟨176894, by rfl⟩ : syracuseStep 235859 = 353789) B353789
theorem B301411 : Blo 155795 301411 := bstep (se 1 (by rfl) ⟨226058, by rfl⟩ : syracuseStep 301411 = 452117) B452117
theorem B268643 : Blo 155795 268643 := bstep (se 1 (by rfl) ⟨201482, by rfl⟩ : syracuseStep 268643 = 402965) B402965
theorem B235889 : Blo 155795 235889 := bstep (se 2 (by rfl) ⟨88458, by rfl⟩ : syracuseStep 235889 = 176917) B176917
theorem B235907 : Blo 155795 235907 := bstep (se 1 (by rfl) ⟨176930, by rfl⟩ : syracuseStep 235907 = 353861) B353861
theorem B530819 : Blo 155795 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B1350029 : Blo 155795 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B301457 : Blo 155795 301457 := bstep (se 2 (by rfl) ⟨113046, by rfl⟩ : syracuseStep 301457 = 226093) B226093
theorem B235937 : Blo 155795 235937 := bstep (se 2 (by rfl) ⟨88476, by rfl⟩ : syracuseStep 235937 = 176953) B176953
theorem B235955 : Blo 155795 235955 := bstep (se 1 (by rfl) ⟨176966, by rfl⟩ : syracuseStep 235955 = 353933) B353933
theorem B596429 : Blo 155795 596429 := bstep (se 3 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 596429 = 223661) B223661
theorem B235985 : Blo 155795 235985 := bstep (se 2 (by rfl) ⟨88494, by rfl⟩ : syracuseStep 235985 = 176989) B176989
theorem B236003 : Blo 155795 236003 := bstep (se 1 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 236003 = 354005) B354005
theorem B268771 : Blo 155795 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B236033 : Blo 155795 236033 := bstep (se 2 (by rfl) ⟨88512, by rfl⟩ : syracuseStep 236033 = 177025) B177025
theorem B236051 : Blo 155795 236051 := bstep (se 1 (by rfl) ⟨177038, by rfl⟩ : syracuseStep 236051 = 354077) B354077
theorem B236081 : Blo 155795 236081 := bstep (se 2 (by rfl) ⟨88530, by rfl⟩ : syracuseStep 236081 = 177061) B177061
theorem B236099 : Blo 155795 236099 := bstep (se 1 (by rfl) ⟨177074, by rfl⟩ : syracuseStep 236099 = 354149) B354149
theorem B236129 : Blo 155795 236129 := bstep (se 2 (by rfl) ⟨88548, by rfl⟩ : syracuseStep 236129 = 177097) B177097
theorem B268913 : Blo 155795 268913 := bstep (se 2 (by rfl) ⟨100842, by rfl⟩ : syracuseStep 268913 = 201685) B201685
theorem B236147 : Blo 155795 236147 := bstep (se 1 (by rfl) ⟨177110, by rfl⟩ : syracuseStep 236147 = 354221) B354221
theorem B531089 : Blo 155795 531089 := bstep (se 2 (by rfl) ⟨199158, by rfl⟩ : syracuseStep 531089 = 398317) B398317
theorem B236177 : Blo 155795 236177 := bstep (se 2 (by rfl) ⟨88566, by rfl⟩ : syracuseStep 236177 = 177133) B177133
theorem B236195 : Blo 155795 236195 := bstep (se 1 (by rfl) ⟨177146, by rfl⟩ : syracuseStep 236195 = 354293) B354293
theorem B400049 : Blo 155795 400049 := bstep (se 2 (by rfl) ⟨150018, by rfl⟩ : syracuseStep 400049 = 300037) B300037
theorem B301745 : Blo 155795 301745 := bstep (se 2 (by rfl) ⟨113154, by rfl⟩ : syracuseStep 301745 = 226309) B226309
theorem B236225 : Blo 155795 236225 := bstep (se 2 (by rfl) ⟨88584, by rfl⟩ : syracuseStep 236225 = 177169) B177169
theorem B236243 : Blo 155795 236243 := bstep (se 1 (by rfl) ⟨177182, by rfl⟩ : syracuseStep 236243 = 354365) B354365
theorem B400099 : Blo 155795 400099 := bstep (se 1 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 400099 = 600149) B600149
theorem B334577 : Blo 155795 334577 := bstep (se 2 (by rfl) ⟨125466, by rfl⟩ : syracuseStep 334577 = 250933) B250933
theorem B236273 : Blo 155795 236273 := bstep (se 2 (by rfl) ⟨88602, by rfl⟩ : syracuseStep 236273 = 177205) B177205
theorem B269041 : Blo 155795 269041 := bstep (se 2 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 269041 = 201781) B201781
theorem B236291 : Blo 155795 236291 := bstep (se 1 (by rfl) ⟨177218, by rfl⟩ : syracuseStep 236291 = 354437) B354437
theorem B269075 : Blo 155795 269075 := bstep (se 1 (by rfl) ⟨201806, by rfl⟩ : syracuseStep 269075 = 403613) B403613
theorem B236321 : Blo 155795 236321 := bstep (se 2 (by rfl) ⟨88620, by rfl⟩ : syracuseStep 236321 = 177241) B177241
theorem B236339 : Blo 155795 236339 := bstep (se 1 (by rfl) ⟨177254, by rfl⟩ : syracuseStep 236339 = 354509) B354509
theorem B236369 : Blo 155795 236369 := bstep (se 2 (by rfl) ⟨88638, by rfl⟩ : syracuseStep 236369 = 177277) B177277
theorem B236387 : Blo 155795 236387 := bstep (se 1 (by rfl) ⟨177290, by rfl⟩ : syracuseStep 236387 = 354581) B354581
theorem B400241 : Blo 155795 400241 := bstep (se 2 (by rfl) ⟨150090, by rfl⟩ : syracuseStep 400241 = 300181) B300181
theorem B236417 : Blo 155795 236417 := bstep (se 2 (by rfl) ⟨88656, by rfl⟩ : syracuseStep 236417 = 177313) B177313
theorem B236435 : Blo 155795 236435 := bstep (se 1 (by rfl) ⟨177326, by rfl⟩ : syracuseStep 236435 = 354653) B354653
theorem B269203 : Blo 155795 269203 := bstep (se 1 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 269203 = 403805) B403805
theorem B236465 : Blo 155795 236465 := bstep (se 2 (by rfl) ⟨88674, by rfl⟩ : syracuseStep 236465 = 177349) B177349
theorem B236483 : Blo 155795 236483 := bstep (se 1 (by rfl) ⟨177362, by rfl⟩ : syracuseStep 236483 = 354725) B354725
theorem B236513 : Blo 155795 236513 := bstep (se 2 (by rfl) ⟨88692, by rfl⟩ : syracuseStep 236513 = 177385) B177385
theorem B236531 : Blo 155795 236531 := bstep (se 1 (by rfl) ⟨177398, by rfl⟩ : syracuseStep 236531 = 354797) B354797
theorem B203779 : Blo 155795 203779 := bstep (se 1 (by rfl) ⟨152834, by rfl⟩ : syracuseStep 203779 = 305669) B305669
theorem B236561 : Blo 155795 236561 := bstep (se 2 (by rfl) ⟨88710, by rfl⟩ : syracuseStep 236561 = 177421) B177421
theorem B269345 : Blo 155795 269345 := bstep (se 2 (by rfl) ⟨101004, by rfl⟩ : syracuseStep 269345 = 202009) B202009
theorem B236579 : Blo 155795 236579 := bstep (se 1 (by rfl) ⟨177434, by rfl⟩ : syracuseStep 236579 = 354869) B354869
theorem B236609 : Blo 155795 236609 := bstep (se 2 (by rfl) ⟨88728, by rfl⟩ : syracuseStep 236609 = 177457) B177457
theorem B236627 : Blo 155795 236627 := bstep (se 1 (by rfl) ⟨177470, by rfl⟩ : syracuseStep 236627 = 354941) B354941
theorem B236657 : Blo 155795 236657 := bstep (se 2 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 236657 = 177493) B177493
theorem B236675 : Blo 155795 236675 := bstep (se 1 (by rfl) ⟨177506, by rfl⟩ : syracuseStep 236675 = 355013) B355013
theorem B236705 : Blo 155795 236705 := bstep (se 2 (by rfl) ⟨88764, by rfl⟩ : syracuseStep 236705 = 177529) B177529
theorem B269473 : Blo 155795 269473 := bstep (se 2 (by rfl) ⟨101052, by rfl⟩ : syracuseStep 269473 = 202105) B202105
theorem B531629 : Blo 155795 531629 := bstep (se 3 (by rfl) ⟨99680, by rfl⟩ : syracuseStep 531629 = 199361) B199361
theorem B236723 : Blo 155795 236723 := bstep (se 1 (by rfl) ⟨177542, by rfl⟩ : syracuseStep 236723 = 355085) B355085
theorem B269507 : Blo 155795 269507 := bstep (se 1 (by rfl) ⟨202130, by rfl⟩ : syracuseStep 269507 = 404261) B404261
theorem B236753 : Blo 155795 236753 := bstep (se 2 (by rfl) ⟨88782, by rfl⟩ : syracuseStep 236753 = 177565) B177565
theorem B531683 : Blo 155795 531683 := bstep (se 1 (by rfl) ⟨398762, by rfl⟩ : syracuseStep 531683 = 797525) B797525
theorem B236771 : Blo 155795 236771 := bstep (se 1 (by rfl) ⟨177578, by rfl⟩ : syracuseStep 236771 = 355157) B355157
theorem B597233 : Blo 155795 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B236801 : Blo 155795 236801 := bstep (se 2 (by rfl) ⟨88800, by rfl⟩ : syracuseStep 236801 = 177601) B177601
theorem B335107 : Blo 155795 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B957701 : Blo 155795 957701 := bstep (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) B179569
theorem B236819 : Blo 155795 236819 := bstep (se 1 (by rfl) ⟨177614, by rfl⟩ : syracuseStep 236819 = 355229) B355229
theorem B236849 : Blo 155795 236849 := bstep (se 2 (by rfl) ⟨88818, by rfl⟩ : syracuseStep 236849 = 177637) B177637
theorem B204083 : Blo 155795 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B236867 : Blo 155795 236867 := bstep (se 1 (by rfl) ⟨177650, by rfl⟩ : syracuseStep 236867 = 355301) B355301
theorem B269635 : Blo 155795 269635 := bstep (se 1 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 269635 = 404453) B404453
theorem B236897 : Blo 155795 236897 := bstep (se 2 (by rfl) ⟨88836, by rfl⟩ : syracuseStep 236897 = 177673) B177673
theorem B236915 : Blo 155795 236915 := bstep (se 1 (by rfl) ⟨177686, by rfl⟩ : syracuseStep 236915 = 355373) B355373
theorem B302467 : Blo 155795 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B236945 : Blo 155795 236945 := bstep (se 2 (by rfl) ⟨88854, by rfl⟩ : syracuseStep 236945 = 177709) B177709
theorem B236963 : Blo 155795 236963 := bstep (se 1 (by rfl) ⟨177722, by rfl⟩ : syracuseStep 236963 = 355445) B355445
theorem B236993 : Blo 155795 236993 := bstep (se 2 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 236993 = 177745) B177745
theorem B237011 : Blo 155795 237011 := bstep (se 1 (by rfl) ⟨177758, by rfl⟩ : syracuseStep 237011 = 355517) B355517
theorem B531953 : Blo 155795 531953 := bstep (se 2 (by rfl) ⟨199482, by rfl⟩ : syracuseStep 531953 = 398965) B398965
theorem B237041 : Blo 155795 237041 := bstep (se 2 (by rfl) ⟨88890, by rfl⟩ : syracuseStep 237041 = 177781) B177781
theorem B237059 : Blo 155795 237059 := bstep (se 1 (by rfl) ⟨177794, by rfl⟩ : syracuseStep 237059 = 355589) B355589
theorem B237089 : Blo 155795 237089 := bstep (se 2 (by rfl) ⟨88908, by rfl⟩ : syracuseStep 237089 = 177817) B177817
theorem B237107 : Blo 155795 237107 := bstep (se 1 (by rfl) ⟨177830, by rfl⟩ : syracuseStep 237107 = 355661) B355661
theorem B237137 : Blo 155795 237137 := bstep (se 2 (by rfl) ⟨88926, by rfl⟩ : syracuseStep 237137 = 177853) B177853
theorem B237155 : Blo 155795 237155 := bstep (se 1 (by rfl) ⟨177866, by rfl⟩ : syracuseStep 237155 = 355733) B355733
theorem B237185 : Blo 155795 237185 := bstep (se 2 (by rfl) ⟨88944, by rfl⟩ : syracuseStep 237185 = 177889) B177889
theorem B237203 : Blo 155795 237203 := bstep (se 1 (by rfl) ⟨177902, by rfl⟩ : syracuseStep 237203 = 355805) B355805
theorem B237233 : Blo 155795 237233 := bstep (se 2 (by rfl) ⟨88962, by rfl⟩ : syracuseStep 237233 = 177925) B177925
theorem B237251 : Blo 155795 237251 := bstep (se 1 (by rfl) ⟨177938, by rfl⟩ : syracuseStep 237251 = 355877) B355877
theorem B237281 : Blo 155795 237281 := bstep (se 2 (by rfl) ⟨88980, by rfl⟩ : syracuseStep 237281 = 177961) B177961
theorem B237299 : Blo 155795 237299 := bstep (se 1 (by rfl) ⟨177974, by rfl⟩ : syracuseStep 237299 = 355949) B355949
theorem B237329 : Blo 155795 237329 := bstep (se 2 (by rfl) ⟨88998, by rfl⟩ : syracuseStep 237329 = 177997) B177997
theorem B237347 : Blo 155795 237347 := bstep (se 1 (by rfl) ⟨178010, by rfl⟩ : syracuseStep 237347 = 356021) B356021
theorem B237377 : Blo 155795 237377 := bstep (se 2 (by rfl) ⟨89016, by rfl⟩ : syracuseStep 237377 = 178033) B178033
theorem B302915 : Blo 155795 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B401233 : Blo 155795 401233 := bstep (se 2 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 401233 = 300925) B300925
theorem B237395 : Blo 155795 237395 := bstep (se 1 (by rfl) ⟨178046, by rfl⟩ : syracuseStep 237395 = 356093) B356093
theorem B2039651 : Blo 155795 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B204643 : Blo 155795 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B237425 : Blo 155795 237425 := bstep (se 2 (by rfl) ⟨89034, by rfl⟩ : syracuseStep 237425 = 178069) B178069
theorem B237443 : Blo 155795 237443 := bstep (se 1 (by rfl) ⟨178082, by rfl⟩ : syracuseStep 237443 = 356165) B356165
theorem B597901 : Blo 155795 597901 := bstep (se 3 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 597901 = 224213) B224213
theorem B237473 : Blo 155795 237473 := bstep (se 2 (by rfl) ⟨89052, by rfl⟩ : syracuseStep 237473 = 178105) B178105
theorem B237491 : Blo 155795 237491 := bstep (se 1 (by rfl) ⟨178118, by rfl⟩ : syracuseStep 237491 = 356237) B356237
theorem B237521 : Blo 155795 237521 := bstep (se 2 (by rfl) ⟨89070, by rfl⟩ : syracuseStep 237521 = 178141) B178141
theorem B237539 : Blo 155795 237539 := bstep (se 1 (by rfl) ⟨178154, by rfl⟩ : syracuseStep 237539 = 356309) B356309
theorem B794609 : Blo 155795 794609 := bstep (se 2 (by rfl) ⟨297978, by rfl⟩ : syracuseStep 794609 = 595957) B595957
theorem B237569 : Blo 155795 237569 := bstep (se 2 (by rfl) ⟨89088, by rfl⟩ : syracuseStep 237569 = 178177) B178177
theorem B532493 : Blo 155795 532493 := bstep (se 3 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 532493 = 199685) B199685
theorem B237587 : Blo 155795 237587 := bstep (se 1 (by rfl) ⟨178190, by rfl⟩ : syracuseStep 237587 = 356381) B356381
theorem B237617 : Blo 155795 237617 := bstep (se 2 (by rfl) ⟨89106, by rfl⟩ : syracuseStep 237617 = 178213) B178213
theorem B532547 : Blo 155795 532547 := bstep (se 1 (by rfl) ⟨399410, by rfl⟩ : syracuseStep 532547 = 798821) B798821
theorem B237635 : Blo 155795 237635 := bstep (se 1 (by rfl) ⟨178226, by rfl⟩ : syracuseStep 237635 = 356453) B356453
theorem B237665 : Blo 155795 237665 := bstep (se 2 (by rfl) ⟨89124, by rfl⟩ : syracuseStep 237665 = 178249) B178249
theorem B401507 : Blo 155795 401507 := bstep (se 1 (by rfl) ⟨301130, by rfl⟩ : syracuseStep 401507 = 602261) B602261
theorem B303203 : Blo 155795 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B237683 : Blo 155795 237683 := bstep (se 1 (by rfl) ⟨178262, by rfl⟩ : syracuseStep 237683 = 356525) B356525
theorem B237713 : Blo 155795 237713 := bstep (se 2 (by rfl) ⟨89142, by rfl⟩ : syracuseStep 237713 = 178285) B178285
theorem B237731 : Blo 155795 237731 := bstep (se 1 (by rfl) ⟨178298, by rfl⟩ : syracuseStep 237731 = 356597) B356597
theorem B237761 : Blo 155795 237761 := bstep (se 2 (by rfl) ⟨89160, by rfl⟩ : syracuseStep 237761 = 178321) B178321
theorem B237779 : Blo 155795 237779 := bstep (se 1 (by rfl) ⟨178334, by rfl⟩ : syracuseStep 237779 = 356669) B356669
theorem B237809 : Blo 155795 237809 := bstep (se 2 (by rfl) ⟨89178, by rfl⟩ : syracuseStep 237809 = 178357) B178357
theorem B237827 : Blo 155795 237827 := bstep (se 1 (by rfl) ⟨178370, by rfl⟩ : syracuseStep 237827 = 356741) B356741
theorem B237857 : Blo 155795 237857 := bstep (se 2 (by rfl) ⟨89196, by rfl⟩ : syracuseStep 237857 = 178393) B178393
theorem B401699 : Blo 155795 401699 := bstep (se 1 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 401699 = 602549) B602549
theorem B237875 : Blo 155795 237875 := bstep (se 1 (by rfl) ⟨178406, by rfl⟩ : syracuseStep 237875 = 356813) B356813
theorem B532817 : Blo 155795 532817 := bstep (se 2 (by rfl) ⟨199806, by rfl⟩ : syracuseStep 532817 = 399613) B399613
theorem B237905 : Blo 155795 237905 := bstep (se 2 (by rfl) ⟨89214, by rfl⟩ : syracuseStep 237905 = 178429) B178429
theorem B237923 : Blo 155795 237923 := bstep (se 1 (by rfl) ⟨178442, by rfl⟩ : syracuseStep 237923 = 356885) B356885
theorem B237953 : Blo 155795 237953 := bstep (se 2 (by rfl) ⟨89232, by rfl⟩ : syracuseStep 237953 = 178465) B178465
theorem B237971 : Blo 155795 237971 := bstep (se 1 (by rfl) ⟨178478, by rfl⟩ : syracuseStep 237971 = 356957) B356957
theorem B238001 : Blo 155795 238001 := bstep (se 2 (by rfl) ⟨89250, by rfl⟩ : syracuseStep 238001 = 178501) B178501
theorem B238019 : Blo 155795 238019 := bstep (se 1 (by rfl) ⟨178514, by rfl⟩ : syracuseStep 238019 = 357029) B357029
theorem B893389 : Blo 155795 893389 := bstep (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) B335021
theorem B238049 : Blo 155795 238049 := bstep (se 2 (by rfl) ⟨89268, by rfl⟩ : syracuseStep 238049 = 178537) B178537
theorem B238067 : Blo 155795 238067 := bstep (se 1 (by rfl) ⟨178550, by rfl⟩ : syracuseStep 238067 = 357101) B357101
theorem B238097 : Blo 155795 238097 := bstep (se 2 (by rfl) ⟨89286, by rfl⟩ : syracuseStep 238097 = 178573) B178573
theorem B238115 : Blo 155795 238115 := bstep (se 1 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 238115 = 357173) B357173
theorem B238145 : Blo 155795 238145 := bstep (se 2 (by rfl) ⟨89304, by rfl⟩ : syracuseStep 238145 = 178609) B178609
theorem B238163 : Blo 155795 238163 := bstep (se 1 (by rfl) ⟨178622, by rfl⟩ : syracuseStep 238163 = 357245) B357245
theorem B238193 : Blo 155795 238193 := bstep (se 2 (by rfl) ⟨89322, by rfl⟩ : syracuseStep 238193 = 178645) B178645
theorem B238211 : Blo 155795 238211 := bstep (se 1 (by rfl) ⟨178658, by rfl⟩ : syracuseStep 238211 = 357317) B357317
theorem B238241 : Blo 155795 238241 := bstep (se 2 (by rfl) ⟨89340, by rfl⟩ : syracuseStep 238241 = 178681) B178681
theorem B598691 : Blo 155795 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B238259 : Blo 155795 238259 := bstep (se 1 (by rfl) ⟨178694, by rfl⟩ : syracuseStep 238259 = 357389) B357389
theorem B336593 : Blo 155795 336593 := bstep (se 2 (by rfl) ⟨126222, by rfl⟩ : syracuseStep 336593 = 252445) B252445
theorem B238289 : Blo 155795 238289 := bstep (se 2 (by rfl) ⟨89358, by rfl⟩ : syracuseStep 238289 = 178717) B178717
theorem B336611 : Blo 155795 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B238307 : Blo 155795 238307 := bstep (se 1 (by rfl) ⟨178730, by rfl⟩ : syracuseStep 238307 = 357461) B357461
theorem B238337 : Blo 155795 238337 := bstep (se 2 (by rfl) ⟨89376, by rfl⟩ : syracuseStep 238337 = 178753) B178753
theorem B1123085 : Blo 155795 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B238355 : Blo 155795 238355 := bstep (se 1 (by rfl) ⟨178766, by rfl⟩ : syracuseStep 238355 = 357533) B357533
theorem B238385 : Blo 155795 238385 := bstep (se 2 (by rfl) ⟨89394, by rfl⟩ : syracuseStep 238385 = 178789) B178789
theorem B238403 : Blo 155795 238403 := bstep (se 1 (by rfl) ⟨178802, by rfl⟩ : syracuseStep 238403 = 357605) B357605
theorem B238433 : Blo 155795 238433 := bstep (se 2 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 238433 = 178825) B178825
theorem B533357 : Blo 155795 533357 := bstep (se 3 (by rfl) ⟨100004, by rfl⟩ : syracuseStep 533357 = 200009) B200009
theorem B238451 : Blo 155795 238451 := bstep (se 1 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 238451 = 357677) B357677
theorem B238481 : Blo 155795 238481 := bstep (se 2 (by rfl) ⟨89430, by rfl⟩ : syracuseStep 238481 = 178861) B178861
theorem B533411 : Blo 155795 533411 := bstep (se 1 (by rfl) ⟨400058, by rfl⟩ : syracuseStep 533411 = 800117) B800117
theorem B238499 : Blo 155795 238499 := bstep (se 1 (by rfl) ⟨178874, by rfl⟩ : syracuseStep 238499 = 357749) B357749
theorem B238529 : Blo 155795 238529 := bstep (se 2 (by rfl) ⟨89448, by rfl⟩ : syracuseStep 238529 = 178897) B178897
theorem B238547 : Blo 155795 238547 := bstep (se 1 (by rfl) ⟨178910, by rfl⟩ : syracuseStep 238547 = 357821) B357821
theorem B238577 : Blo 155795 238577 := bstep (se 2 (by rfl) ⟨89466, by rfl⟩ : syracuseStep 238577 = 178933) B178933
theorem B238595 : Blo 155795 238595 := bstep (se 1 (by rfl) ⟨178946, by rfl⟩ : syracuseStep 238595 = 357893) B357893
theorem B238625 : Blo 155795 238625 := bstep (se 2 (by rfl) ⟨89484, by rfl⟩ : syracuseStep 238625 = 178969) B178969
theorem B304163 : Blo 155795 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B238643 : Blo 155795 238643 := bstep (se 1 (by rfl) ⟨178982, by rfl⟩ : syracuseStep 238643 = 357965) B357965
theorem B238673 : Blo 155795 238673 := bstep (se 2 (by rfl) ⟨89502, by rfl⟩ : syracuseStep 238673 = 179005) B179005
theorem B205907 : Blo 155795 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B238691 : Blo 155795 238691 := bstep (se 1 (by rfl) ⟨179018, by rfl⟩ : syracuseStep 238691 = 358037) B358037
theorem B238721 : Blo 155795 238721 := bstep (se 2 (by rfl) ⟨89520, by rfl⟩ : syracuseStep 238721 = 179041) B179041
theorem B238739 : Blo 155795 238739 := bstep (se 1 (by rfl) ⟨179054, by rfl⟩ : syracuseStep 238739 = 358109) B358109
theorem B533681 : Blo 155795 533681 := bstep (se 2 (by rfl) ⟨200130, by rfl⟩ : syracuseStep 533681 = 400261) B400261
theorem B238769 : Blo 155795 238769 := bstep (se 2 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 238769 = 179077) B179077
theorem B238787 : Blo 155795 238787 := bstep (se 1 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 238787 = 358181) B358181
theorem B402641 : Blo 155795 402641 := bstep (se 2 (by rfl) ⟨150990, by rfl⟩ : syracuseStep 402641 = 301981) B301981
theorem B238817 : Blo 155795 238817 := bstep (se 2 (by rfl) ⟨89556, by rfl⟩ : syracuseStep 238817 = 179113) B179113
theorem B238835 : Blo 155795 238835 := bstep (se 1 (by rfl) ⟨179126, by rfl⟩ : syracuseStep 238835 = 358253) B358253
theorem B402691 : Blo 155795 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B238865 : Blo 155795 238865 := bstep (se 2 (by rfl) ⟨89574, by rfl⟩ : syracuseStep 238865 = 179149) B179149
theorem B238883 : Blo 155795 238883 := bstep (se 1 (by rfl) ⟨179162, by rfl⟩ : syracuseStep 238883 = 358325) B358325
theorem B599345 : Blo 155795 599345 := bstep (se 2 (by rfl) ⟨224754, by rfl⟩ : syracuseStep 599345 = 449509) B449509
theorem B238913 : Blo 155795 238913 := bstep (se 2 (by rfl) ⟨89592, by rfl⟩ : syracuseStep 238913 = 179185) B179185
theorem B238931 : Blo 155795 238931 := bstep (se 1 (by rfl) ⟨179198, by rfl⟩ : syracuseStep 238931 = 358397) B358397
theorem B238961 : Blo 155795 238961 := bstep (se 2 (by rfl) ⟨89610, by rfl⟩ : syracuseStep 238961 = 179221) B179221
theorem B238979 : Blo 155795 238979 := bstep (se 1 (by rfl) ⟨179234, by rfl⟩ : syracuseStep 238979 = 358469) B358469
theorem B402833 : Blo 155795 402833 := bstep (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) B302125
theorem B238993 : Blo 155795 238993 := bstep (se 2 (by rfl) ⟨89622, by rfl⟩ : syracuseStep 238993 = 179245) B179245
theorem B239009 : Blo 155795 239009 := bstep (se 2 (by rfl) ⟨89628, by rfl⟩ : syracuseStep 239009 = 179257) B179257
theorem B796067 : Blo 155795 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B239027 : Blo 155795 239027 := bstep (se 1 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 239027 = 358541) B358541
theorem B239057 : Blo 155795 239057 := bstep (se 2 (by rfl) ⟨89646, by rfl⟩ : syracuseStep 239057 = 179293) B179293
theorem B239075 : Blo 155795 239075 := bstep (se 1 (by rfl) ⟨179306, by rfl⟩ : syracuseStep 239075 = 358613) B358613
theorem B239105 : Blo 155795 239105 := bstep (se 2 (by rfl) ⟨89664, by rfl⟩ : syracuseStep 239105 = 179329) B179329
theorem B239123 : Blo 155795 239123 := bstep (se 1 (by rfl) ⟨179342, by rfl⟩ : syracuseStep 239123 = 358685) B358685
theorem B239153 : Blo 155795 239153 := bstep (se 2 (by rfl) ⟨89682, by rfl⟩ : syracuseStep 239153 = 179365) B179365
theorem B239171 : Blo 155795 239171 := bstep (se 1 (by rfl) ⟨179378, by rfl⟩ : syracuseStep 239171 = 358757) B358757
theorem B763469 : Blo 155795 763469 := bstep (se 3 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 763469 = 286301) B286301
theorem B501329 : Blo 155795 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B239201 : Blo 155795 239201 := bstep (se 2 (by rfl) ⟨89700, by rfl⟩ : syracuseStep 239201 = 179401) B179401
theorem B239219 : Blo 155795 239219 := bstep (se 1 (by rfl) ⟨179414, by rfl⟩ : syracuseStep 239219 = 358829) B358829
theorem B239249 : Blo 155795 239249 := bstep (se 2 (by rfl) ⟨89718, by rfl⟩ : syracuseStep 239249 = 179437) B179437
theorem B239267 : Blo 155795 239267 := bstep (se 1 (by rfl) ⟨179450, by rfl⟩ : syracuseStep 239267 = 358901) B358901
theorem B239297 : Blo 155795 239297 := bstep (se 2 (by rfl) ⟨89736, by rfl⟩ : syracuseStep 239297 = 179473) B179473
theorem B534221 : Blo 155795 534221 := bstep (se 3 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 534221 = 200333) B200333
theorem B239315 : Blo 155795 239315 := bstep (se 1 (by rfl) ⟨179486, by rfl⟩ : syracuseStep 239315 = 358973) B358973
theorem B239345 : Blo 155795 239345 := bstep (se 2 (by rfl) ⟨89754, by rfl⟩ : syracuseStep 239345 = 179509) B179509
theorem B534275 : Blo 155795 534275 := bstep (se 1 (by rfl) ⟨400706, by rfl⟩ : syracuseStep 534275 = 801413) B801413
theorem B239363 : Blo 155795 239363 := bstep (se 1 (by rfl) ⟨179522, by rfl⟩ : syracuseStep 239363 = 359045) B359045
theorem B239393 : Blo 155795 239393 := bstep (se 2 (by rfl) ⟨89772, by rfl⟩ : syracuseStep 239393 = 179545) B179545
theorem B239411 : Blo 155795 239411 := bstep (se 1 (by rfl) ⟨179558, by rfl⟩ : syracuseStep 239411 = 359117) B359117
theorem B1812293 : Blo 155795 1812293 := bstep (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) B339805
theorem B239441 : Blo 155795 239441 := bstep (se 2 (by rfl) ⟨89790, by rfl⟩ : syracuseStep 239441 = 179581) B179581
theorem B239459 : Blo 155795 239459 := bstep (se 1 (by rfl) ⟨179594, by rfl⟩ : syracuseStep 239459 = 359189) B359189
theorem B239489 : Blo 155795 239489 := bstep (se 2 (by rfl) ⟨89808, by rfl⟩ : syracuseStep 239489 = 179617) B179617
theorem B239507 : Blo 155795 239507 := bstep (se 1 (by rfl) ⟨179630, by rfl⟩ : syracuseStep 239507 = 359261) B359261
theorem B337841 : Blo 155795 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B239537 : Blo 155795 239537 := bstep (se 2 (by rfl) ⟨89826, by rfl⟩ : syracuseStep 239537 = 179653) B179653
theorem B239555 : Blo 155795 239555 := bstep (se 1 (by rfl) ⟨179666, by rfl⟩ : syracuseStep 239555 = 359333) B359333
theorem B239585 : Blo 155795 239585 := bstep (se 2 (by rfl) ⟨89844, by rfl⟩ : syracuseStep 239585 = 179689) B179689
theorem B239603 : Blo 155795 239603 := bstep (se 1 (by rfl) ⟨179702, by rfl⟩ : syracuseStep 239603 = 359405) B359405
theorem B534545 : Blo 155795 534545 := bstep (se 2 (by rfl) ⟨200454, by rfl⟩ : syracuseStep 534545 = 400909) B400909
theorem B239633 : Blo 155795 239633 := bstep (se 2 (by rfl) ⟨89862, by rfl⟩ : syracuseStep 239633 = 179725) B179725
theorem B239651 : Blo 155795 239651 := bstep (se 1 (by rfl) ⟨179738, by rfl⟩ : syracuseStep 239651 = 359477) B359477
theorem B239681 : Blo 155795 239681 := bstep (se 2 (by rfl) ⟨89880, by rfl⟩ : syracuseStep 239681 = 179761) B179761
theorem B796877 : Blo 155795 796877 := bstep (se 3 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 796877 = 298829) B298829
theorem B1190213 : Blo 155795 1190213 := bstep (se 4 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 1190213 = 223165) B223165
theorem B403825 : Blo 155795 403825 := bstep (se 2 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 403825 = 302869) B302869
theorem B895373 : Blo 155795 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B535085 : Blo 155795 535085 := bstep (se 3 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 535085 = 200657) B200657
theorem B535139 : Blo 155795 535139 := bstep (se 1 (by rfl) ⟨401354, by rfl⟩ : syracuseStep 535139 = 802709) B802709
theorem B240259 : Blo 155795 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B404099 : Blo 155795 404099 := bstep (se 1 (by rfl) ⟨303074, by rfl⟩ : syracuseStep 404099 = 606149) B606149
theorem B600803 : Blo 155795 600803 := bstep (se 1 (by rfl) ⟨450602, by rfl⟩ : syracuseStep 600803 = 901205) B901205
theorem B600817 : Blo 155795 600817 := bstep (se 2 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 600817 = 450613) B450613
theorem B404227 : Blo 155795 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B371491 : Blo 155795 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B404291 : Blo 155795 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B863075 : Blo 155795 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B535409 : Blo 155795 535409 := bstep (se 2 (by rfl) ⟨200778, by rfl⟩ : syracuseStep 535409 = 401557) B401557
theorem B175315 : Blo 155795 175315 := bstep (se 1 (by rfl) ⟨131486, by rfl⟩ : syracuseStep 175315 = 262973) B262973
theorem B896305 : Blo 155795 896305 := bstep (se 2 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 896305 = 672229) B672229
theorem B634189 : Blo 155795 634189 := bstep (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) B237821
theorem B175459 : Blo 155795 175459 := bstep (se 1 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 175459 = 263189) B263189
theorem B535949 : Blo 155795 535949 := bstep (se 3 (by rfl) ⟨100490, by rfl⟩ : syracuseStep 535949 = 200981) B200981
theorem B1027505 : Blo 155795 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B536003 : Blo 155795 536003 := bstep (se 1 (by rfl) ⟨402002, by rfl⟩ : syracuseStep 536003 = 804005) B804005
theorem B339395 : Blo 155795 339395 := bstep (se 1 (by rfl) ⟨254546, by rfl⟩ : syracuseStep 339395 = 509093) B509093
theorem B404945 : Blo 155795 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B2043377 : Blo 155795 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B175603 : Blo 155795 175603 := bstep (se 1 (by rfl) ⟨131702, by rfl⟩ : syracuseStep 175603 = 263405) B263405
theorem B503405 : Blo 155795 503405 := bstep (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) B188777
theorem B175747 : Blo 155795 175747 := bstep (se 1 (by rfl) ⟨131810, by rfl⟩ : syracuseStep 175747 = 263621) B263621
theorem B831181 : Blo 155795 831181 := bstep (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) B311693
theorem B536273 : Blo 155795 536273 := bstep (se 2 (by rfl) ⟨201102, by rfl⟩ : syracuseStep 536273 = 402205) B402205
theorem B405233 : Blo 155795 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B175891 : Blo 155795 175891 := bstep (se 1 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 175891 = 263837) B263837
theorem B241523 : Blo 155795 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B176035 : Blo 155795 176035 := bstep (se 1 (by rfl) ⟨132026, by rfl⟩ : syracuseStep 176035 = 264053) B264053
theorem B176179 : Blo 155795 176179 := bstep (se 1 (by rfl) ⟨132134, by rfl⟩ : syracuseStep 176179 = 264269) B264269
theorem B241715 : Blo 155795 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B602275 : Blo 155795 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B176323 : Blo 155795 176323 := bstep (se 1 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 176323 = 264485) B264485
theorem B536813 : Blo 155795 536813 := bstep (se 3 (by rfl) ⟨100652, by rfl⟩ : syracuseStep 536813 = 201305) B201305
theorem B536867 : Blo 155795 536867 := bstep (se 1 (by rfl) ⟨402650, by rfl⟩ : syracuseStep 536867 = 805301) B805301
theorem B176467 : Blo 155795 176467 := bstep (se 1 (by rfl) ⟨132350, by rfl⟩ : syracuseStep 176467 = 264701) B264701
theorem B176611 : Blo 155795 176611 := bstep (se 1 (by rfl) ⟨132458, by rfl⟩ : syracuseStep 176611 = 264917) B264917
theorem B504301 : Blo 155795 504301 := bstep (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) B189113
theorem B537137 : Blo 155795 537137 := bstep (se 2 (by rfl) ⟨201426, by rfl⟩ : syracuseStep 537137 = 402853) B402853
theorem B176755 : Blo 155795 176755 := bstep (se 1 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 176755 = 265133) B265133
theorem B897763 : Blo 155795 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B176899 : Blo 155795 176899 := bstep (se 1 (by rfl) ⟨132674, by rfl⟩ : syracuseStep 176899 = 265349) B265349
theorem B177043 : Blo 155795 177043 := bstep (se 1 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 177043 = 265565) B265565
theorem B177187 : Blo 155795 177187 := bstep (se 1 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 177187 = 265781) B265781
theorem B799793 : Blo 155795 799793 := bstep (se 2 (by rfl) ⟨299922, by rfl⟩ : syracuseStep 799793 = 599845) B599845
theorem B537677 : Blo 155795 537677 := bstep (se 3 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 537677 = 201629) B201629
theorem B537731 : Blo 155795 537731 := bstep (se 1 (by rfl) ⟨403298, by rfl⟩ : syracuseStep 537731 = 806597) B806597
theorem B177331 : Blo 155795 177331 := bstep (se 1 (by rfl) ⟨132998, by rfl⟩ : syracuseStep 177331 = 265997) B265997
theorem B898289 : Blo 155795 898289 := bstep (se 2 (by rfl) ⟨336858, by rfl⟩ : syracuseStep 898289 = 673717) B673717
theorem B242929 : Blo 155795 242929 := bstep (se 2 (by rfl) ⟨91098, by rfl⟩ : syracuseStep 242929 = 182197) B182197
theorem B177475 : Blo 155795 177475 := bstep (se 1 (by rfl) ⟨133106, by rfl⟩ : syracuseStep 177475 = 266213) B266213
theorem B505187 : Blo 155795 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B538001 : Blo 155795 538001 := bstep (se 2 (by rfl) ⟨201750, by rfl⟩ : syracuseStep 538001 = 403501) B403501
theorem B177619 : Blo 155795 177619 := bstep (se 1 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 177619 = 266429) B266429
theorem B538093 : Blo 155795 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B177763 : Blo 155795 177763 := bstep (se 1 (by rfl) ⟨133322, by rfl⟩ : syracuseStep 177763 = 266645) B266645
theorem B177907 : Blo 155795 177907 := bstep (se 1 (by rfl) ⟨133430, by rfl⟩ : syracuseStep 177907 = 266861) B266861
theorem B178051 : Blo 155795 178051 := bstep (se 1 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 178051 = 267077) B267077
theorem B538541 : Blo 155795 538541 := bstep (se 3 (by rfl) ⟨100976, by rfl⟩ : syracuseStep 538541 = 201953) B201953
theorem B669617 : Blo 155795 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B669667 : Blo 155795 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B538595 : Blo 155795 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B178195 : Blo 155795 178195 := bstep (se 1 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 178195 = 267293) B267293
theorem B178339 : Blo 155795 178339 := bstep (se 1 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 178339 = 267509) B267509
theorem B538865 : Blo 155795 538865 := bstep (se 2 (by rfl) ⟨202074, by rfl⟩ : syracuseStep 538865 = 404149) B404149
theorem B178483 : Blo 155795 178483 := bstep (se 1 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 178483 = 267725) B267725
theorem B604493 : Blo 155795 604493 := bstep (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) B226685
theorem B178627 : Blo 155795 178627 := bstep (se 1 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 178627 = 267941) B267941
theorem B801251 : Blo 155795 801251 := bstep (se 1 (by rfl) ⟨600938, by rfl⟩ : syracuseStep 801251 = 1201877) B1201877
theorem B571981 : Blo 155795 571981 := bstep (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) B214493
theorem B178771 : Blo 155795 178771 := bstep (se 1 (by rfl) ⟨134078, by rfl⟩ : syracuseStep 178771 = 268157) B268157
theorem B899747 : Blo 155795 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B178915 : Blo 155795 178915 := bstep (se 1 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 178915 = 268373) B268373
theorem B179059 : Blo 155795 179059 := bstep (se 1 (by rfl) ⟨134294, by rfl⟩ : syracuseStep 179059 = 268589) B268589
theorem B179203 : Blo 155795 179203 := bstep (se 1 (by rfl) ⟨134402, by rfl⟩ : syracuseStep 179203 = 268805) B268805
theorem B179347 : Blo 155795 179347 := bstep (se 1 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 179347 = 269021) B269021
theorem B343217 : Blo 155795 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B802061 : Blo 155795 802061 := bstep (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) B300773
theorem B179491 : Blo 155795 179491 := bstep (se 1 (by rfl) ⟨134618, by rfl⟩ : syracuseStep 179491 = 269237) B269237
theorem B703907 : Blo 155795 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B179635 : Blo 155795 179635 := bstep (se 1 (by rfl) ⟨134726, by rfl⟩ : syracuseStep 179635 = 269453) B269453
theorem B507377 : Blo 155795 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B1818125 : Blo 155795 1818125 := bstep (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) B681797
theorem B507505 : Blo 155795 507505 := bstep (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) B380629
theorem B180067 : Blo 155795 180067 := bstep (se 1 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 180067 = 270101) B270101
theorem B507761 : Blo 155795 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B540611 : Blo 155795 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B1196045 : Blo 155795 1196045 := bstep (se 3 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 1196045 = 448517) B448517
theorem B1097891 : Blo 155795 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B672077 : Blo 155795 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B901637 : Blo 155795 901637 := bstep (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) B169057
theorem B180787 : Blo 155795 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B508717 : Blo 155795 508717 := bstep (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) B190769
theorem B934789 : Blo 155795 934789 := bstep (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) B175273
theorem B1360867 : Blo 155795 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B377891 : Blo 155795 377891 := bstep (se 1 (by rfl) ⟨283418, by rfl⟩ : syracuseStep 377891 = 566837) B566837
theorem B214147 : Blo 155795 214147 := bstep (se 1 (by rfl) ⟨160610, by rfl⟩ : syracuseStep 214147 = 321221) B321221
theorem B4015331 : Blo 155795 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B214321 : Blo 155795 214321 := bstep (se 2 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 214321 = 160741) B160741
theorem B542033 : Blo 155795 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B443825 : Blo 155795 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B1394117 : Blo 155795 1394117 := bstep (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) B261397
theorem B509453 : Blo 155795 509453 := bstep (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) B191045
theorem B346051 : Blo 155795 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B804977 : Blo 155795 804977 := bstep (se 2 (by rfl) ⟨301866, by rfl⟩ : syracuseStep 804977 = 603733) B603733
theorem B1099909 : Blo 155795 1099909 := bstep (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) B206233
theorem B215185 : Blo 155795 215185 := bstep (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) B161389
theorem B2017507 : Blo 155795 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B510221 : Blo 155795 510221 := bstep (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) B191333
theorem B444781 : Blo 155795 444781 := bstep (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) B166793
theorem B445009 : Blo 155795 445009 := bstep (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) B333757
theorem B379505 : Blo 155795 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B281233 : Blo 155795 281233 := bstep (se 2 (by rfl) ⟨105462, by rfl⟩ : syracuseStep 281233 = 210925) B210925
theorem B543395 : Blo 155795 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B445169 : Blo 155795 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B510733 : Blo 155795 510733 := bstep (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) B191525
theorem B445283 : Blo 155795 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B1198961 : Blo 155795 1198961 := bstep (se 2 (by rfl) ⟨449610, by rfl⟩ : syracuseStep 1198961 = 899221) B899221
theorem B674893 : Blo 155795 674893 := bstep (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) B253085
theorem B216193 : Blo 155795 216193 := bstep (se 2 (by rfl) ⟨81072, by rfl⟩ : syracuseStep 216193 = 162145) B162145
theorem B511235 : Blo 155795 511235 := bstep (se 1 (by rfl) ⟨383426, by rfl⟩ : syracuseStep 511235 = 766853) B766853
theorem B1003013 : Blo 155795 1003013 := bstep (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) B188065
theorem B806435 : Blo 155795 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B249569 : Blo 155795 249569 := bstep (se 2 (by rfl) ⟨93588, by rfl⟩ : syracuseStep 249569 = 187177) B187177
theorem B446285 : Blo 155795 446285 := bstep (se 3 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 446285 = 167357) B167357
theorem B446467 : Blo 155795 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B446627 : Blo 155795 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B807245 : Blo 155795 807245 := bstep (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) B302717
theorem B479825 : Blo 155795 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B676451 : Blo 155795 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B840389 : Blo 155795 840389 := bstep (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) B157573
theorem B381763 : Blo 155795 381763 := bstep (se 1 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 381763 = 572645) B572645
theorem B709517 : Blo 155795 709517 := bstep (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) B266069
theorem B480323 : Blo 155795 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B251075 : Blo 155795 251075 := bstep (se 1 (by rfl) ⟨188306, by rfl⟩ : syracuseStep 251075 = 376613) B376613
theorem B447697 : Blo 155795 447697 := bstep (se 2 (by rfl) ⟨167886, by rfl⟩ : syracuseStep 447697 = 335773) B335773
theorem B251363 : Blo 155795 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B284305 : Blo 155795 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B907057 : Blo 155795 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B284593 : Blo 155795 284593 := bstep (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) B213445
theorem B907469 : Blo 155795 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B252163 : Blo 155795 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B252305 : Blo 155795 252305 := bstep (se 2 (by rfl) ⟨94614, by rfl⟩ : syracuseStep 252305 = 189229) B189229
theorem B252337 : Blo 155795 252337 := bstep (se 2 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 252337 = 189253) B189253
theorem B448973 : Blo 155795 448973 := bstep (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) B168365
theorem B1530353 : Blo 155795 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B678449 : Blo 155795 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B350801 : Blo 155795 350801 := bstep (se 2 (by rfl) ⟨131550, by rfl⟩ : syracuseStep 350801 = 263101) B263101
theorem B350819 : Blo 155795 350819 := bstep (se 1 (by rfl) ⟨263114, by rfl⟩ : syracuseStep 350819 = 526229) B526229
theorem B449155 : Blo 155795 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B449201 : Blo 155795 449201 := bstep (se 2 (by rfl) ⟨168450, by rfl⟩ : syracuseStep 449201 = 336901) B336901
theorem B383665 : Blo 155795 383665 := bstep (se 2 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 383665 = 287749) B287749
theorem B351089 : Blo 155795 351089 := bstep (se 2 (by rfl) ⟨131658, by rfl⟩ : syracuseStep 351089 = 263317) B263317
theorem B351107 : Blo 155795 351107 := bstep (se 1 (by rfl) ⟨263330, by rfl⟩ : syracuseStep 351107 = 526661) B526661
theorem B1006499 : Blo 155795 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B351377 : Blo 155795 351377 := bstep (se 2 (by rfl) ⟨131766, by rfl⟩ : syracuseStep 351377 = 263533) B263533
theorem B351395 : Blo 155795 351395 := bstep (se 1 (by rfl) ⟨263546, by rfl⟩ : syracuseStep 351395 = 527093) B527093
theorem B187715 : Blo 155795 187715 := bstep (se 1 (by rfl) ⟨140786, by rfl⟩ : syracuseStep 187715 = 281573) B281573
theorem B253265 : Blo 155795 253265 := bstep (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) B189949
theorem B351665 : Blo 155795 351665 := bstep (se 2 (by rfl) ⟨131874, by rfl⟩ : syracuseStep 351665 = 263749) B263749
theorem B351683 : Blo 155795 351683 := bstep (se 1 (by rfl) ⟨263762, by rfl⟩ : syracuseStep 351683 = 527525) B527525
theorem B482755 : Blo 155795 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B679373 : Blo 155795 679373 := bstep (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) B254765
theorem B351953 : Blo 155795 351953 := bstep (se 2 (by rfl) ⟨131982, by rfl⟩ : syracuseStep 351953 = 263965) B263965
theorem B351971 : Blo 155795 351971 := bstep (se 1 (by rfl) ⟨263978, by rfl⟩ : syracuseStep 351971 = 527957) B527957
theorem B352241 : Blo 155795 352241 := bstep (se 2 (by rfl) ⟨132090, by rfl⟩ : syracuseStep 352241 = 264181) B264181
theorem B352259 : Blo 155795 352259 := bstep (se 1 (by rfl) ⟨264194, by rfl⟩ : syracuseStep 352259 = 528389) B528389
theorem B286769 : Blo 155795 286769 := bstep (se 2 (by rfl) ⟨107538, by rfl⟩ : syracuseStep 286769 = 215077) B215077
theorem B450659 : Blo 155795 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B1335437 : Blo 155795 1335437 := bstep (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) B500789
theorem B155795 : Blo 155795 155795 := bstep (se 1 (by rfl) ⟨116846, by rfl⟩ : syracuseStep 155795 = 233693) B233693
theorem B254099 : Blo 155795 254099 := bstep (se 1 (by rfl) ⟨190574, by rfl⟩ : syracuseStep 254099 = 381149) B381149
theorem B155811 : Blo 155795 155811 := bstep (se 1 (by rfl) ⟨116858, by rfl⟩ : syracuseStep 155811 = 233717) B233717
theorem B155827 : Blo 155795 155827 := bstep (se 1 (by rfl) ⟨116870, by rfl⟩ : syracuseStep 155827 = 233741) B233741
theorem B155843 : Blo 155795 155843 := bstep (se 1 (by rfl) ⟨116882, by rfl⟩ : syracuseStep 155843 = 233765) B233765
theorem B155859 : Blo 155795 155859 := bstep (se 1 (by rfl) ⟨116894, by rfl⟩ : syracuseStep 155859 = 233789) B233789
theorem B155875 : Blo 155795 155875 := bstep (se 1 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 155875 = 233813) B233813
theorem B155891 : Blo 155795 155891 := bstep (se 1 (by rfl) ⟨116918, by rfl⟩ : syracuseStep 155891 = 233837) B233837
theorem B155907 : Blo 155795 155907 := bstep (se 1 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 155907 = 233861) B233861
theorem B352529 : Blo 155795 352529 := bstep (se 2 (by rfl) ⟨132198, by rfl⟩ : syracuseStep 352529 = 264397) B264397
theorem B286993 : Blo 155795 286993 := bstep (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) B215245
theorem B155923 : Blo 155795 155923 := bstep (se 1 (by rfl) ⟨116942, by rfl⟩ : syracuseStep 155923 = 233885) B233885
theorem B155939 : Blo 155795 155939 := bstep (se 1 (by rfl) ⟨116954, by rfl⟩ : syracuseStep 155939 = 233909) B233909
theorem B352547 : Blo 155795 352547 := bstep (se 1 (by rfl) ⟨264410, by rfl⟩ : syracuseStep 352547 = 528821) B528821
theorem B155955 : Blo 155795 155955 := bstep (se 1 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 155955 = 233933) B233933
theorem B155971 : Blo 155795 155971 := bstep (se 1 (by rfl) ⟨116978, by rfl⟩ : syracuseStep 155971 = 233957) B233957
theorem B155987 : Blo 155795 155987 := bstep (se 1 (by rfl) ⟨116990, by rfl⟩ : syracuseStep 155987 = 233981) B233981
theorem B156003 : Blo 155795 156003 := bstep (se 1 (by rfl) ⟨117002, by rfl⟩ : syracuseStep 156003 = 234005) B234005
theorem B156019 : Blo 155795 156019 := bstep (se 1 (by rfl) ⟨117014, by rfl⟩ : syracuseStep 156019 = 234029) B234029
theorem B156035 : Blo 155795 156035 := bstep (se 1 (by rfl) ⟨117026, by rfl⟩ : syracuseStep 156035 = 234053) B234053
theorem B909701 : Blo 155795 909701 := bstep (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) B170569
theorem B156051 : Blo 155795 156051 := bstep (se 1 (by rfl) ⟨117038, by rfl⟩ : syracuseStep 156051 = 234077) B234077
theorem B156067 : Blo 155795 156067 := bstep (se 1 (by rfl) ⟨117050, by rfl⟩ : syracuseStep 156067 = 234101) B234101
theorem B319907 : Blo 155795 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B156083 : Blo 155795 156083 := bstep (se 1 (by rfl) ⟨117062, by rfl⟩ : syracuseStep 156083 = 234125) B234125
theorem B254387 : Blo 155795 254387 := bstep (se 1 (by rfl) ⟨190790, by rfl⟩ : syracuseStep 254387 = 381581) B381581
theorem B156099 : Blo 155795 156099 := bstep (se 1 (by rfl) ⟨117074, by rfl⟩ : syracuseStep 156099 = 234149) B234149
theorem B1532357 : Blo 155795 1532357 := bstep (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) B287317
theorem B156115 : Blo 155795 156115 := bstep (se 1 (by rfl) ⟨117086, by rfl⟩ : syracuseStep 156115 = 234173) B234173
theorem B156131 : Blo 155795 156131 := bstep (se 1 (by rfl) ⟨117098, by rfl⟩ : syracuseStep 156131 = 234197) B234197
theorem B156147 : Blo 155795 156147 := bstep (se 1 (by rfl) ⟨117110, by rfl⟩ : syracuseStep 156147 = 234221) B234221
theorem B156163 : Blo 155795 156163 := bstep (se 1 (by rfl) ⟨117122, by rfl⟩ : syracuseStep 156163 = 234245) B234245
theorem B156179 : Blo 155795 156179 := bstep (se 1 (by rfl) ⟨117134, by rfl⟩ : syracuseStep 156179 = 234269) B234269
theorem B156195 : Blo 155795 156195 := bstep (se 1 (by rfl) ⟨117146, by rfl⟩ : syracuseStep 156195 = 234293) B234293
theorem B352817 : Blo 155795 352817 := bstep (se 2 (by rfl) ⟨132306, by rfl⟩ : syracuseStep 352817 = 264613) B264613
theorem B156211 : Blo 155795 156211 := bstep (se 1 (by rfl) ⟨117158, by rfl⟩ : syracuseStep 156211 = 234317) B234317
theorem B156227 : Blo 155795 156227 := bstep (se 1 (by rfl) ⟨117170, by rfl⟩ : syracuseStep 156227 = 234341) B234341
theorem B352835 : Blo 155795 352835 := bstep (se 1 (by rfl) ⟨264626, by rfl⟩ : syracuseStep 352835 = 529253) B529253
theorem B156243 : Blo 155795 156243 := bstep (se 1 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 156243 = 234365) B234365
theorem B156259 : Blo 155795 156259 := bstep (se 1 (by rfl) ⟨117194, by rfl⟩ : syracuseStep 156259 = 234389) B234389
theorem B156275 : Blo 155795 156275 := bstep (se 1 (by rfl) ⟨117206, by rfl⟩ : syracuseStep 156275 = 234413) B234413
theorem B156291 : Blo 155795 156291 := bstep (se 1 (by rfl) ⟨117218, by rfl⟩ : syracuseStep 156291 = 234437) B234437
theorem B156307 : Blo 155795 156307 := bstep (se 1 (by rfl) ⟨117230, by rfl⟩ : syracuseStep 156307 = 234461) B234461
theorem B254611 : Blo 155795 254611 := bstep (se 1 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 254611 = 381917) B381917
theorem B156323 : Blo 155795 156323 := bstep (se 1 (by rfl) ⟨117242, by rfl⟩ : syracuseStep 156323 = 234485) B234485
theorem B156339 : Blo 155795 156339 := bstep (se 1 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 156339 = 234509) B234509
theorem B156355 : Blo 155795 156355 := bstep (se 1 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 156355 = 234533) B234533
theorem B156371 : Blo 155795 156371 := bstep (se 1 (by rfl) ⟨117278, by rfl⟩ : syracuseStep 156371 = 234557) B234557
theorem B156387 : Blo 155795 156387 := bstep (se 1 (by rfl) ⟨117290, by rfl⟩ : syracuseStep 156387 = 234581) B234581
theorem B451313 : Blo 155795 451313 := bstep (se 2 (by rfl) ⟨169242, by rfl⟩ : syracuseStep 451313 = 338485) B338485
theorem B156403 : Blo 155795 156403 := bstep (se 1 (by rfl) ⟨117302, by rfl⟩ : syracuseStep 156403 = 234605) B234605
theorem B156419 : Blo 155795 156419 := bstep (se 1 (by rfl) ⟨117314, by rfl⟩ : syracuseStep 156419 = 234629) B234629
theorem B156435 : Blo 155795 156435 := bstep (se 1 (by rfl) ⟨117326, by rfl⟩ : syracuseStep 156435 = 234653) B234653
theorem B156451 : Blo 155795 156451 := bstep (se 1 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 156451 = 234677) B234677
theorem B156467 : Blo 155795 156467 := bstep (se 1 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 156467 = 234701) B234701
theorem B1696565 : Blo 155795 1696565 := bstep (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) B159053
theorem B156483 : Blo 155795 156483 := bstep (se 1 (by rfl) ⟨117362, by rfl⟩ : syracuseStep 156483 = 234725) B234725
theorem B1925957 : Blo 155795 1925957 := bstep (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) B361117
theorem B353105 : Blo 155795 353105 := bstep (se 2 (by rfl) ⟨132414, by rfl⟩ : syracuseStep 353105 = 264829) B264829
theorem B156499 : Blo 155795 156499 := bstep (se 1 (by rfl) ⟨117374, by rfl⟩ : syracuseStep 156499 = 234749) B234749
theorem B222049 : Blo 155795 222049 := bstep (se 2 (by rfl) ⟨83268, by rfl⟩ : syracuseStep 222049 = 166537) B166537
theorem B156515 : Blo 155795 156515 := bstep (se 1 (by rfl) ⟨117386, by rfl⟩ : syracuseStep 156515 = 234773) B234773
theorem B353123 : Blo 155795 353123 := bstep (se 1 (by rfl) ⟨264842, by rfl⟩ : syracuseStep 353123 = 529685) B529685
theorem B4350833 : Blo 155795 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B156531 : Blo 155795 156531 := bstep (se 1 (by rfl) ⟨117398, by rfl⟩ : syracuseStep 156531 = 234797) B234797
theorem B156547 : Blo 155795 156547 := bstep (se 1 (by rfl) ⟨117410, by rfl⟩ : syracuseStep 156547 = 234821) B234821
theorem B156563 : Blo 155795 156563 := bstep (se 1 (by rfl) ⟨117422, by rfl⟩ : syracuseStep 156563 = 234845) B234845
theorem B156579 : Blo 155795 156579 := bstep (se 1 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 156579 = 234869) B234869
theorem B156595 : Blo 155795 156595 := bstep (se 1 (by rfl) ⟨117446, by rfl⟩ : syracuseStep 156595 = 234893) B234893
theorem B156611 : Blo 155795 156611 := bstep (se 1 (by rfl) ⟨117458, by rfl⟩ : syracuseStep 156611 = 234917) B234917
theorem B156627 : Blo 155795 156627 := bstep (se 1 (by rfl) ⟨117470, by rfl⟩ : syracuseStep 156627 = 234941) B234941
theorem B156643 : Blo 155795 156643 := bstep (se 1 (by rfl) ⟨117482, by rfl⟩ : syracuseStep 156643 = 234965) B234965
theorem B156659 : Blo 155795 156659 := bstep (se 1 (by rfl) ⟨117494, by rfl⟩ : syracuseStep 156659 = 234989) B234989
theorem B156675 : Blo 155795 156675 := bstep (se 1 (by rfl) ⟨117506, by rfl⟩ : syracuseStep 156675 = 235013) B235013
theorem B156691 : Blo 155795 156691 := bstep (se 1 (by rfl) ⟨117518, by rfl⟩ : syracuseStep 156691 = 235037) B235037
theorem B156707 : Blo 155795 156707 := bstep (se 1 (by rfl) ⟨117530, by rfl⟩ : syracuseStep 156707 = 235061) B235061
theorem B156723 : Blo 155795 156723 := bstep (se 1 (by rfl) ⟨117542, by rfl⟩ : syracuseStep 156723 = 235085) B235085
theorem B156739 : Blo 155795 156739 := bstep (se 1 (by rfl) ⟨117554, by rfl⟩ : syracuseStep 156739 = 235109) B235109
theorem B156755 : Blo 155795 156755 := bstep (se 1 (by rfl) ⟨117566, by rfl⟩ : syracuseStep 156755 = 235133) B235133
theorem B156771 : Blo 155795 156771 := bstep (se 1 (by rfl) ⟨117578, by rfl⟩ : syracuseStep 156771 = 235157) B235157
theorem B353393 : Blo 155795 353393 := bstep (se 2 (by rfl) ⟨132522, by rfl⟩ : syracuseStep 353393 = 265045) B265045
theorem B156787 : Blo 155795 156787 := bstep (se 1 (by rfl) ⟨117590, by rfl⟩ : syracuseStep 156787 = 235181) B235181
theorem B156803 : Blo 155795 156803 := bstep (se 1 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 156803 = 235205) B235205
theorem B353411 : Blo 155795 353411 := bstep (se 1 (by rfl) ⟨265058, by rfl⟩ : syracuseStep 353411 = 530117) B530117
theorem B156819 : Blo 155795 156819 := bstep (se 1 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 156819 = 235229) B235229
theorem B156835 : Blo 155795 156835 := bstep (se 1 (by rfl) ⟨117626, by rfl⟩ : syracuseStep 156835 = 235253) B235253
theorem B156851 : Blo 155795 156851 := bstep (se 1 (by rfl) ⟨117638, by rfl⟩ : syracuseStep 156851 = 235277) B235277
theorem B156867 : Blo 155795 156867 := bstep (se 1 (by rfl) ⟨117650, by rfl⟩ : syracuseStep 156867 = 235301) B235301
theorem B156883 : Blo 155795 156883 := bstep (se 1 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 156883 = 235325) B235325
theorem B156899 : Blo 155795 156899 := bstep (se 1 (by rfl) ⟨117674, by rfl⟩ : syracuseStep 156899 = 235349) B235349
theorem B156915 : Blo 155795 156915 := bstep (se 1 (by rfl) ⟨117686, by rfl⟩ : syracuseStep 156915 = 235373) B235373
theorem B156931 : Blo 155795 156931 := bstep (se 1 (by rfl) ⟨117698, by rfl⟩ : syracuseStep 156931 = 235397) B235397
theorem B156947 : Blo 155795 156947 := bstep (se 1 (by rfl) ⟨117710, by rfl⟩ : syracuseStep 156947 = 235421) B235421
theorem B156963 : Blo 155795 156963 := bstep (se 1 (by rfl) ⟨117722, by rfl⟩ : syracuseStep 156963 = 235445) B235445
theorem B451889 : Blo 155795 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B156979 : Blo 155795 156979 := bstep (se 1 (by rfl) ⟨117734, by rfl⟩ : syracuseStep 156979 = 235469) B235469
theorem B156995 : Blo 155795 156995 := bstep (se 1 (by rfl) ⟨117746, by rfl⟩ : syracuseStep 156995 = 235493) B235493
theorem B157011 : Blo 155795 157011 := bstep (se 1 (by rfl) ⟨117758, by rfl⟩ : syracuseStep 157011 = 235517) B235517
theorem B255329 : Blo 155795 255329 := bstep (se 2 (by rfl) ⟨95748, by rfl⟩ : syracuseStep 255329 = 191497) B191497
theorem B157027 : Blo 155795 157027 := bstep (se 1 (by rfl) ⟨117770, by rfl⟩ : syracuseStep 157027 = 235541) B235541
theorem B1369457 : Blo 155795 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B157043 : Blo 155795 157043 := bstep (se 1 (by rfl) ⟨117782, by rfl⟩ : syracuseStep 157043 = 235565) B235565
theorem B157059 : Blo 155795 157059 := bstep (se 1 (by rfl) ⟨117794, by rfl⟩ : syracuseStep 157059 = 235589) B235589
theorem B353681 : Blo 155795 353681 := bstep (se 2 (by rfl) ⟨132630, by rfl⟩ : syracuseStep 353681 = 265261) B265261
theorem B157075 : Blo 155795 157075 := bstep (se 1 (by rfl) ⟨117806, by rfl⟩ : syracuseStep 157075 = 235613) B235613
theorem B157091 : Blo 155795 157091 := bstep (se 1 (by rfl) ⟨117818, by rfl⟩ : syracuseStep 157091 = 235637) B235637
theorem B353699 : Blo 155795 353699 := bstep (se 1 (by rfl) ⟨265274, by rfl⟩ : syracuseStep 353699 = 530549) B530549
theorem B157107 : Blo 155795 157107 := bstep (se 1 (by rfl) ⟨117830, by rfl⟩ : syracuseStep 157107 = 235661) B235661
theorem B157123 : Blo 155795 157123 := bstep (se 1 (by rfl) ⟨117842, by rfl⟩ : syracuseStep 157123 = 235685) B235685
theorem B157139 : Blo 155795 157139 := bstep (se 1 (by rfl) ⟨117854, by rfl⟩ : syracuseStep 157139 = 235709) B235709
theorem B157155 : Blo 155795 157155 := bstep (se 1 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 157155 = 235733) B235733
theorem B157171 : Blo 155795 157171 := bstep (se 1 (by rfl) ⟨117878, by rfl⟩ : syracuseStep 157171 = 235757) B235757
theorem B157187 : Blo 155795 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B157203 : Blo 155795 157203 := bstep (se 1 (by rfl) ⟨117902, by rfl⟩ : syracuseStep 157203 = 235805) B235805
theorem B255521 : Blo 155795 255521 := bstep (se 2 (by rfl) ⟨95820, by rfl⟩ : syracuseStep 255521 = 191641) B191641
theorem B222755 : Blo 155795 222755 := bstep (se 1 (by rfl) ⟨167066, by rfl⟩ : syracuseStep 222755 = 334133) B334133
theorem B157219 : Blo 155795 157219 := bstep (se 1 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 157219 = 235829) B235829
theorem B321059 : Blo 155795 321059 := bstep (se 1 (by rfl) ⟨240794, by rfl⟩ : syracuseStep 321059 = 481589) B481589
theorem B157235 : Blo 155795 157235 := bstep (se 1 (by rfl) ⟨117926, by rfl⟩ : syracuseStep 157235 = 235853) B235853
theorem B157251 : Blo 155795 157251 := bstep (se 1 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 157251 = 235877) B235877
theorem B157267 : Blo 155795 157267 := bstep (se 1 (by rfl) ⟨117950, by rfl⟩ : syracuseStep 157267 = 235901) B235901
theorem B157283 : Blo 155795 157283 := bstep (se 1 (by rfl) ⟨117962, by rfl⟩ : syracuseStep 157283 = 235925) B235925
theorem B157299 : Blo 155795 157299 := bstep (se 1 (by rfl) ⟨117974, by rfl⟩ : syracuseStep 157299 = 235949) B235949
theorem B157315 : Blo 155795 157315 := bstep (se 1 (by rfl) ⟨117986, by rfl⟩ : syracuseStep 157315 = 235973) B235973
theorem B157331 : Blo 155795 157331 := bstep (se 1 (by rfl) ⟨117998, by rfl⟩ : syracuseStep 157331 = 235997) B235997
theorem B255649 : Blo 155795 255649 := bstep (se 2 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 255649 = 191737) B191737
theorem B157347 : Blo 155795 157347 := bstep (se 1 (by rfl) ⟨118010, by rfl⟩ : syracuseStep 157347 = 236021) B236021
theorem B353969 : Blo 155795 353969 := bstep (se 2 (by rfl) ⟨132738, by rfl⟩ : syracuseStep 353969 = 265477) B265477
theorem B157363 : Blo 155795 157363 := bstep (se 1 (by rfl) ⟨118022, by rfl⟩ : syracuseStep 157363 = 236045) B236045
theorem B353987 : Blo 155795 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B157379 : Blo 155795 157379 := bstep (se 1 (by rfl) ⟨118034, by rfl⟩ : syracuseStep 157379 = 236069) B236069
theorem B157395 : Blo 155795 157395 := bstep (se 1 (by rfl) ⟨118046, by rfl⟩ : syracuseStep 157395 = 236093) B236093
theorem B157411 : Blo 155795 157411 := bstep (se 1 (by rfl) ⟨118058, by rfl⟩ : syracuseStep 157411 = 236117) B236117
theorem B157427 : Blo 155795 157427 := bstep (se 1 (by rfl) ⟨118070, by rfl⟩ : syracuseStep 157427 = 236141) B236141
theorem B157443 : Blo 155795 157443 := bstep (se 1 (by rfl) ⟨118082, by rfl⟩ : syracuseStep 157443 = 236165) B236165
theorem B157459 : Blo 155795 157459 := bstep (se 1 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 157459 = 236189) B236189
theorem B157475 : Blo 155795 157475 := bstep (se 1 (by rfl) ⟨118106, by rfl⟩ : syracuseStep 157475 = 236213) B236213
theorem B157491 : Blo 155795 157491 := bstep (se 1 (by rfl) ⟨118118, by rfl⟩ : syracuseStep 157491 = 236237) B236237
theorem B157507 : Blo 155795 157507 := bstep (se 1 (by rfl) ⟨118130, by rfl⟩ : syracuseStep 157507 = 236261) B236261
theorem B157523 : Blo 155795 157523 := bstep (se 1 (by rfl) ⟨118142, by rfl⟩ : syracuseStep 157523 = 236285) B236285
theorem B157539 : Blo 155795 157539 := bstep (se 1 (by rfl) ⟨118154, by rfl⟩ : syracuseStep 157539 = 236309) B236309
theorem B157555 : Blo 155795 157555 := bstep (se 1 (by rfl) ⟨118166, by rfl⟩ : syracuseStep 157555 = 236333) B236333
theorem B157571 : Blo 155795 157571 := bstep (se 1 (by rfl) ⟨118178, by rfl⟩ : syracuseStep 157571 = 236357) B236357
theorem B157587 : Blo 155795 157587 := bstep (se 1 (by rfl) ⟨118190, by rfl⟩ : syracuseStep 157587 = 236381) B236381
theorem B157603 : Blo 155795 157603 := bstep (se 1 (by rfl) ⟨118202, by rfl⟩ : syracuseStep 157603 = 236405) B236405
theorem B157619 : Blo 155795 157619 := bstep (se 1 (by rfl) ⟨118214, by rfl⟩ : syracuseStep 157619 = 236429) B236429
theorem B157635 : Blo 155795 157635 := bstep (se 1 (by rfl) ⟨118226, by rfl⟩ : syracuseStep 157635 = 236453) B236453
theorem B354257 : Blo 155795 354257 := bstep (se 2 (by rfl) ⟨132846, by rfl⟩ : syracuseStep 354257 = 265693) B265693
theorem B157651 : Blo 155795 157651 := bstep (se 1 (by rfl) ⟨118238, by rfl⟩ : syracuseStep 157651 = 236477) B236477
theorem B354275 : Blo 155795 354275 := bstep (se 1 (by rfl) ⟨265706, by rfl⟩ : syracuseStep 354275 = 531413) B531413
theorem B157667 : Blo 155795 157667 := bstep (se 1 (by rfl) ⟨118250, by rfl⟩ : syracuseStep 157667 = 236501) B236501
theorem B157683 : Blo 155795 157683 := bstep (se 1 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 157683 = 236525) B236525
theorem B157699 : Blo 155795 157699 := bstep (se 1 (by rfl) ⟨118274, by rfl⟩ : syracuseStep 157699 = 236549) B236549
theorem B157715 : Blo 155795 157715 := bstep (se 1 (by rfl) ⟨118286, by rfl⟩ : syracuseStep 157715 = 236573) B236573
theorem B157731 : Blo 155795 157731 := bstep (se 1 (by rfl) ⟨118298, by rfl⟩ : syracuseStep 157731 = 236597) B236597
theorem B157747 : Blo 155795 157747 := bstep (se 1 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 157747 = 236621) B236621
theorem B157763 : Blo 155795 157763 := bstep (se 1 (by rfl) ⟨118322, by rfl⟩ : syracuseStep 157763 = 236645) B236645
theorem B157779 : Blo 155795 157779 := bstep (se 1 (by rfl) ⟨118334, by rfl⟩ : syracuseStep 157779 = 236669) B236669
theorem B157795 : Blo 155795 157795 := bstep (se 1 (by rfl) ⟨118346, by rfl⟩ : syracuseStep 157795 = 236693) B236693
theorem B157811 : Blo 155795 157811 := bstep (se 1 (by rfl) ⟨118358, by rfl⟩ : syracuseStep 157811 = 236717) B236717
theorem B157827 : Blo 155795 157827 := bstep (se 1 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 157827 = 236741) B236741
theorem B485507 : Blo 155795 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B157843 : Blo 155795 157843 := bstep (se 1 (by rfl) ⟨118382, by rfl⟩ : syracuseStep 157843 = 236765) B236765
theorem B223393 : Blo 155795 223393 := bstep (se 2 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 223393 = 167545) B167545
theorem B157859 : Blo 155795 157859 := bstep (se 1 (by rfl) ⟨118394, by rfl⟩ : syracuseStep 157859 = 236789) B236789
theorem B157875 : Blo 155795 157875 := bstep (se 1 (by rfl) ⟨118406, by rfl⟩ : syracuseStep 157875 = 236813) B236813
theorem B157891 : Blo 155795 157891 := bstep (se 1 (by rfl) ⟨118418, by rfl⟩ : syracuseStep 157891 = 236837) B236837
theorem B157907 : Blo 155795 157907 := bstep (se 1 (by rfl) ⟨118430, by rfl⟩ : syracuseStep 157907 = 236861) B236861
theorem B157923 : Blo 155795 157923 := bstep (se 1 (by rfl) ⟨118442, by rfl⟩ : syracuseStep 157923 = 236885) B236885
theorem B354545 : Blo 155795 354545 := bstep (se 2 (by rfl) ⟨132954, by rfl⟩ : syracuseStep 354545 = 265909) B265909
theorem B157939 : Blo 155795 157939 := bstep (se 1 (by rfl) ⟨118454, by rfl⟩ : syracuseStep 157939 = 236909) B236909
theorem B354563 : Blo 155795 354563 := bstep (se 1 (by rfl) ⟨265922, by rfl⟩ : syracuseStep 354563 = 531845) B531845
theorem B157955 : Blo 155795 157955 := bstep (se 1 (by rfl) ⟨118466, by rfl⟩ : syracuseStep 157955 = 236933) B236933
theorem B223507 : Blo 155795 223507 := bstep (se 1 (by rfl) ⟨167630, by rfl⟩ : syracuseStep 223507 = 335261) B335261
theorem B157971 : Blo 155795 157971 := bstep (se 1 (by rfl) ⟨118478, by rfl⟩ : syracuseStep 157971 = 236957) B236957
theorem B157987 : Blo 155795 157987 := bstep (se 1 (by rfl) ⟨118490, by rfl⟩ : syracuseStep 157987 = 236981) B236981
theorem B158003 : Blo 155795 158003 := bstep (se 1 (by rfl) ⟨118502, by rfl⟩ : syracuseStep 158003 = 237005) B237005
theorem B158019 : Blo 155795 158019 := bstep (se 1 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 158019 = 237029) B237029
theorem B158035 : Blo 155795 158035 := bstep (se 1 (by rfl) ⟨118526, by rfl⟩ : syracuseStep 158035 = 237053) B237053
theorem B158051 : Blo 155795 158051 := bstep (se 1 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 158051 = 237077) B237077
theorem B158067 : Blo 155795 158067 := bstep (se 1 (by rfl) ⟨118550, by rfl⟩ : syracuseStep 158067 = 237101) B237101
theorem B158083 : Blo 155795 158083 := bstep (se 1 (by rfl) ⟨118562, by rfl⟩ : syracuseStep 158083 = 237125) B237125
theorem B158099 : Blo 155795 158099 := bstep (se 1 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 158099 = 237149) B237149
theorem B158115 : Blo 155795 158115 := bstep (se 1 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 158115 = 237173) B237173
theorem B158131 : Blo 155795 158131 := bstep (se 1 (by rfl) ⟨118598, by rfl⟩ : syracuseStep 158131 = 237197) B237197
theorem B158147 : Blo 155795 158147 := bstep (se 1 (by rfl) ⟨118610, by rfl⟩ : syracuseStep 158147 = 237221) B237221
theorem B7301573 : Blo 155795 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B158163 : Blo 155795 158163 := bstep (se 1 (by rfl) ⟨118622, by rfl⟩ : syracuseStep 158163 = 237245) B237245
theorem B158179 : Blo 155795 158179 := bstep (se 1 (by rfl) ⟨118634, by rfl⟩ : syracuseStep 158179 = 237269) B237269
theorem B682481 : Blo 155795 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B158195 : Blo 155795 158195 := bstep (se 1 (by rfl) ⟨118646, by rfl⟩ : syracuseStep 158195 = 237293) B237293
theorem B158211 : Blo 155795 158211 := bstep (se 1 (by rfl) ⟨118658, by rfl⟩ : syracuseStep 158211 = 237317) B237317
theorem B354833 : Blo 155795 354833 := bstep (se 2 (by rfl) ⟨133062, by rfl⟩ : syracuseStep 354833 = 266125) B266125
theorem B158227 : Blo 155795 158227 := bstep (se 1 (by rfl) ⟨118670, by rfl⟩ : syracuseStep 158227 = 237341) B237341
theorem B354851 : Blo 155795 354851 := bstep (se 1 (by rfl) ⟨266138, by rfl⟩ : syracuseStep 354851 = 532277) B532277
theorem B158243 : Blo 155795 158243 := bstep (se 1 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 158243 = 237365) B237365
theorem B158259 : Blo 155795 158259 := bstep (se 1 (by rfl) ⟨118694, by rfl⟩ : syracuseStep 158259 = 237389) B237389
theorem B158275 : Blo 155795 158275 := bstep (se 1 (by rfl) ⟨118706, by rfl⟩ : syracuseStep 158275 = 237413) B237413
theorem B158291 : Blo 155795 158291 := bstep (se 1 (by rfl) ⟨118718, by rfl⟩ : syracuseStep 158291 = 237437) B237437
theorem B289379 : Blo 155795 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B158307 : Blo 155795 158307 := bstep (se 1 (by rfl) ⟨118730, by rfl⟩ : syracuseStep 158307 = 237461) B237461
theorem B158323 : Blo 155795 158323 := bstep (se 1 (by rfl) ⟨118742, by rfl⟩ : syracuseStep 158323 = 237485) B237485
theorem B158339 : Blo 155795 158339 := bstep (se 1 (by rfl) ⟨118754, by rfl⟩ : syracuseStep 158339 = 237509) B237509
theorem B158355 : Blo 155795 158355 := bstep (se 1 (by rfl) ⟨118766, by rfl⟩ : syracuseStep 158355 = 237533) B237533
theorem B158371 : Blo 155795 158371 := bstep (se 1 (by rfl) ⟨118778, by rfl⟩ : syracuseStep 158371 = 237557) B237557
theorem B158387 : Blo 155795 158387 := bstep (se 1 (by rfl) ⟨118790, by rfl⟩ : syracuseStep 158387 = 237581) B237581
theorem B158403 : Blo 155795 158403 := bstep (se 1 (by rfl) ⟨118802, by rfl⟩ : syracuseStep 158403 = 237605) B237605
theorem B158419 : Blo 155795 158419 := bstep (se 1 (by rfl) ⟨118814, by rfl⟩ : syracuseStep 158419 = 237629) B237629
theorem B453347 : Blo 155795 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B158435 : Blo 155795 158435 := bstep (se 1 (by rfl) ⟨118826, by rfl⟩ : syracuseStep 158435 = 237653) B237653
theorem B158451 : Blo 155795 158451 := bstep (se 1 (by rfl) ⟨118838, by rfl⟩ : syracuseStep 158451 = 237677) B237677
theorem B158467 : Blo 155795 158467 := bstep (se 1 (by rfl) ⟨118850, by rfl⟩ : syracuseStep 158467 = 237701) B237701
theorem B158483 : Blo 155795 158483 := bstep (se 1 (by rfl) ⟨118862, by rfl⟩ : syracuseStep 158483 = 237725) B237725
theorem B256801 : Blo 155795 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B158499 : Blo 155795 158499 := bstep (se 1 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 158499 = 237749) B237749
theorem B355121 : Blo 155795 355121 := bstep (se 2 (by rfl) ⟨133170, by rfl⟩ : syracuseStep 355121 = 266341) B266341
theorem B158515 : Blo 155795 158515 := bstep (se 1 (by rfl) ⟨118886, by rfl⟩ : syracuseStep 158515 = 237773) B237773
theorem B355139 : Blo 155795 355139 := bstep (se 1 (by rfl) ⟨266354, by rfl⟩ : syracuseStep 355139 = 532709) B532709
theorem B158531 : Blo 155795 158531 := bstep (se 1 (by rfl) ⟨118898, by rfl⟩ : syracuseStep 158531 = 237797) B237797
theorem B158547 : Blo 155795 158547 := bstep (se 1 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 158547 = 237821) B237821
theorem B158563 : Blo 155795 158563 := bstep (se 1 (by rfl) ⟨118922, by rfl⟩ : syracuseStep 158563 = 237845) B237845
theorem B158579 : Blo 155795 158579 := bstep (se 1 (by rfl) ⟨118934, by rfl⟩ : syracuseStep 158579 = 237869) B237869
theorem B158595 : Blo 155795 158595 := bstep (se 1 (by rfl) ⟨118946, by rfl⟩ : syracuseStep 158595 = 237893) B237893
theorem B1895309 : Blo 155795 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B158611 : Blo 155795 158611 := bstep (se 1 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 158611 = 237917) B237917
theorem B158627 : Blo 155795 158627 := bstep (se 1 (by rfl) ⟨118970, by rfl⟩ : syracuseStep 158627 = 237941) B237941
theorem B158643 : Blo 155795 158643 := bstep (se 1 (by rfl) ⟨118982, by rfl⟩ : syracuseStep 158643 = 237965) B237965
theorem B158659 : Blo 155795 158659 := bstep (se 1 (by rfl) ⟨118994, by rfl⟩ : syracuseStep 158659 = 237989) B237989
theorem B158675 : Blo 155795 158675 := bstep (se 1 (by rfl) ⟨119006, by rfl⟩ : syracuseStep 158675 = 238013) B238013
theorem B158691 : Blo 155795 158691 := bstep (se 1 (by rfl) ⟨119018, by rfl⟩ : syracuseStep 158691 = 238037) B238037
theorem B158707 : Blo 155795 158707 := bstep (se 1 (by rfl) ⟨119030, by rfl⟩ : syracuseStep 158707 = 238061) B238061
theorem B158723 : Blo 155795 158723 := bstep (se 1 (by rfl) ⟨119042, by rfl⟩ : syracuseStep 158723 = 238085) B238085
theorem B158739 : Blo 155795 158739 := bstep (se 1 (by rfl) ⟨119054, by rfl⟩ : syracuseStep 158739 = 238109) B238109
theorem B158755 : Blo 155795 158755 := bstep (se 1 (by rfl) ⟨119066, by rfl⟩ : syracuseStep 158755 = 238133) B238133
theorem B158771 : Blo 155795 158771 := bstep (se 1 (by rfl) ⟨119078, by rfl⟩ : syracuseStep 158771 = 238157) B238157
theorem B158787 : Blo 155795 158787 := bstep (se 1 (by rfl) ⟨119090, by rfl⟩ : syracuseStep 158787 = 238181) B238181
theorem B355409 : Blo 155795 355409 := bstep (se 2 (by rfl) ⟨133278, by rfl⟩ : syracuseStep 355409 = 266557) B266557
theorem B158803 : Blo 155795 158803 := bstep (se 1 (by rfl) ⟨119102, by rfl⟩ : syracuseStep 158803 = 238205) B238205
theorem B355427 : Blo 155795 355427 := bstep (se 1 (by rfl) ⟨266570, by rfl⟩ : syracuseStep 355427 = 533141) B533141
theorem B158819 : Blo 155795 158819 := bstep (se 1 (by rfl) ⟨119114, by rfl⟩ : syracuseStep 158819 = 238229) B238229
theorem B158835 : Blo 155795 158835 := bstep (se 1 (by rfl) ⟨119126, by rfl⟩ : syracuseStep 158835 = 238253) B238253
theorem B158851 : Blo 155795 158851 := bstep (se 1 (by rfl) ⟨119138, by rfl⟩ : syracuseStep 158851 = 238277) B238277
theorem B158867 : Blo 155795 158867 := bstep (se 1 (by rfl) ⟨119150, by rfl⟩ : syracuseStep 158867 = 238301) B238301
theorem B158883 : Blo 155795 158883 := bstep (se 1 (by rfl) ⟨119162, by rfl⟩ : syracuseStep 158883 = 238325) B238325
theorem B158899 : Blo 155795 158899 := bstep (se 1 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 158899 = 238349) B238349
theorem B158915 : Blo 155795 158915 := bstep (se 1 (by rfl) ⟨119186, by rfl⟩ : syracuseStep 158915 = 238373) B238373
theorem B158931 : Blo 155795 158931 := bstep (se 1 (by rfl) ⟨119198, by rfl⟩ : syracuseStep 158931 = 238397) B238397
theorem B158947 : Blo 155795 158947 := bstep (se 1 (by rfl) ⟨119210, by rfl⟩ : syracuseStep 158947 = 238421) B238421
theorem B158963 : Blo 155795 158963 := bstep (se 1 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 158963 = 238445) B238445
theorem B158979 : Blo 155795 158979 := bstep (se 1 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 158979 = 238469) B238469
theorem B158995 : Blo 155795 158995 := bstep (se 1 (by rfl) ⟨119246, by rfl⟩ : syracuseStep 158995 = 238493) B238493
theorem B3665173 : Blo 155795 3665173 := bstep (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) B171805
theorem B159011 : Blo 155795 159011 := bstep (se 1 (by rfl) ⟨119258, by rfl⟩ : syracuseStep 159011 = 238517) B238517
theorem B159027 : Blo 155795 159027 := bstep (se 1 (by rfl) ⟨119270, by rfl⟩ : syracuseStep 159027 = 238541) B238541
theorem B3042613 : Blo 155795 3042613 := bstep (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) B285245
theorem B159043 : Blo 155795 159043 := bstep (se 1 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 159043 = 238565) B238565
theorem B1469765 : Blo 155795 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B159059 : Blo 155795 159059 := bstep (se 1 (by rfl) ⟨119294, by rfl⟩ : syracuseStep 159059 = 238589) B238589
theorem B159075 : Blo 155795 159075 := bstep (se 1 (by rfl) ⟨119306, by rfl⟩ : syracuseStep 159075 = 238613) B238613
theorem B355697 : Blo 155795 355697 := bstep (se 2 (by rfl) ⟨133386, by rfl⟩ : syracuseStep 355697 = 266773) B266773
theorem B159091 : Blo 155795 159091 := bstep (se 1 (by rfl) ⟨119318, by rfl⟩ : syracuseStep 159091 = 238637) B238637
theorem B355715 : Blo 155795 355715 := bstep (se 1 (by rfl) ⟨266786, by rfl⟩ : syracuseStep 355715 = 533573) B533573
theorem B159107 : Blo 155795 159107 := bstep (se 1 (by rfl) ⟨119330, by rfl⟩ : syracuseStep 159107 = 238661) B238661
theorem B159123 : Blo 155795 159123 := bstep (se 1 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 159123 = 238685) B238685
theorem B159139 : Blo 155795 159139 := bstep (se 1 (by rfl) ⟨119354, by rfl⟩ : syracuseStep 159139 = 238709) B238709
theorem B159155 : Blo 155795 159155 := bstep (se 1 (by rfl) ⟨119366, by rfl⟩ : syracuseStep 159155 = 238733) B238733
theorem B159171 : Blo 155795 159171 := bstep (se 1 (by rfl) ⟨119378, by rfl⟩ : syracuseStep 159171 = 238757) B238757
theorem B159187 : Blo 155795 159187 := bstep (se 1 (by rfl) ⟨119390, by rfl⟩ : syracuseStep 159187 = 238781) B238781
theorem B159203 : Blo 155795 159203 := bstep (se 1 (by rfl) ⟨119402, by rfl⟩ : syracuseStep 159203 = 238805) B238805
theorem B159219 : Blo 155795 159219 := bstep (se 1 (by rfl) ⟨119414, by rfl⟩ : syracuseStep 159219 = 238829) B238829
theorem B159235 : Blo 155795 159235 := bstep (se 1 (by rfl) ⟨119426, by rfl⟩ : syracuseStep 159235 = 238853) B238853
theorem B454157 : Blo 155795 454157 := bstep (se 3 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 454157 = 170309) B170309
theorem B159251 : Blo 155795 159251 := bstep (se 1 (by rfl) ⟨119438, by rfl⟩ : syracuseStep 159251 = 238877) B238877
theorem B159267 : Blo 155795 159267 := bstep (se 1 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 159267 = 238901) B238901
theorem B159283 : Blo 155795 159283 := bstep (se 1 (by rfl) ⟨119462, by rfl⟩ : syracuseStep 159283 = 238925) B238925
theorem B2256437 : Blo 155795 2256437 := bstep (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) B211541
theorem B159299 : Blo 155795 159299 := bstep (se 1 (by rfl) ⟨119474, by rfl⟩ : syracuseStep 159299 = 238949) B238949
theorem B224851 : Blo 155795 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B159315 : Blo 155795 159315 := bstep (se 1 (by rfl) ⟨119486, by rfl⟩ : syracuseStep 159315 = 238973) B238973
theorem B159331 : Blo 155795 159331 := bstep (se 1 (by rfl) ⟨119498, by rfl⟩ : syracuseStep 159331 = 238997) B238997
theorem B159347 : Blo 155795 159347 := bstep (se 1 (by rfl) ⟨119510, by rfl⟩ : syracuseStep 159347 = 239021) B239021
theorem B159363 : Blo 155795 159363 := bstep (se 1 (by rfl) ⟨119522, by rfl⟩ : syracuseStep 159363 = 239045) B239045
theorem B355985 : Blo 155795 355985 := bstep (se 2 (by rfl) ⟨133494, by rfl⟩ : syracuseStep 355985 = 266989) B266989
theorem B159379 : Blo 155795 159379 := bstep (se 1 (by rfl) ⟨119534, by rfl⟩ : syracuseStep 159379 = 239069) B239069
theorem B356003 : Blo 155795 356003 := bstep (se 1 (by rfl) ⟨267002, by rfl⟩ : syracuseStep 356003 = 534005) B534005
theorem B159395 : Blo 155795 159395 := bstep (se 1 (by rfl) ⟨119546, by rfl⟩ : syracuseStep 159395 = 239093) B239093
theorem B159411 : Blo 155795 159411 := bstep (se 1 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 159411 = 239117) B239117
theorem B159427 : Blo 155795 159427 := bstep (se 1 (by rfl) ⟨119570, by rfl⟩ : syracuseStep 159427 = 239141) B239141
theorem B454349 : Blo 155795 454349 := bstep (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) B170381
theorem B323281 : Blo 155795 323281 := bstep (se 2 (by rfl) ⟨121230, by rfl⟩ : syracuseStep 323281 = 242461) B242461
theorem B159443 : Blo 155795 159443 := bstep (se 1 (by rfl) ⟨119582, by rfl⟩ : syracuseStep 159443 = 239165) B239165
theorem B159459 : Blo 155795 159459 := bstep (se 1 (by rfl) ⟨119594, by rfl⟩ : syracuseStep 159459 = 239189) B239189
theorem B421613 : Blo 155795 421613 := bstep (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) B158105
theorem B159475 : Blo 155795 159475 := bstep (se 1 (by rfl) ⟨119606, by rfl⟩ : syracuseStep 159475 = 239213) B239213
theorem B159491 : Blo 155795 159491 := bstep (se 1 (by rfl) ⟨119618, by rfl⟩ : syracuseStep 159491 = 239237) B239237
theorem B913157 : Blo 155795 913157 := bstep (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) B171217
theorem B159507 : Blo 155795 159507 := bstep (se 1 (by rfl) ⟨119630, by rfl⟩ : syracuseStep 159507 = 239261) B239261
theorem B159523 : Blo 155795 159523 := bstep (se 1 (by rfl) ⟨119642, by rfl⟩ : syracuseStep 159523 = 239285) B239285
theorem B159539 : Blo 155795 159539 := bstep (se 1 (by rfl) ⟨119654, by rfl⟩ : syracuseStep 159539 = 239309) B239309
theorem B421699 : Blo 155795 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B159555 : Blo 155795 159555 := bstep (se 1 (by rfl) ⟨119666, by rfl⟩ : syracuseStep 159555 = 239333) B239333
theorem B159571 : Blo 155795 159571 := bstep (se 1 (by rfl) ⟨119678, by rfl⟩ : syracuseStep 159571 = 239357) B239357
theorem B159587 : Blo 155795 159587 := bstep (se 1 (by rfl) ⟨119690, by rfl⟩ : syracuseStep 159587 = 239381) B239381
theorem B159603 : Blo 155795 159603 := bstep (se 1 (by rfl) ⟨119702, by rfl⟩ : syracuseStep 159603 = 239405) B239405
theorem B159619 : Blo 155795 159619 := bstep (se 1 (by rfl) ⟨119714, by rfl⟩ : syracuseStep 159619 = 239429) B239429
theorem B159635 : Blo 155795 159635 := bstep (se 1 (by rfl) ⟨119726, by rfl⟩ : syracuseStep 159635 = 239453) B239453
theorem B159651 : Blo 155795 159651 := bstep (se 1 (by rfl) ⟨119738, by rfl⟩ : syracuseStep 159651 = 239477) B239477
theorem B356273 : Blo 155795 356273 := bstep (se 2 (by rfl) ⟨133602, by rfl⟩ : syracuseStep 356273 = 267205) B267205
theorem B159667 : Blo 155795 159667 := bstep (se 1 (by rfl) ⟨119750, by rfl⟩ : syracuseStep 159667 = 239501) B239501
theorem B356291 : Blo 155795 356291 := bstep (se 1 (by rfl) ⟨267218, by rfl⟩ : syracuseStep 356291 = 534437) B534437
theorem B159683 : Blo 155795 159683 := bstep (se 1 (by rfl) ⟨119762, by rfl⟩ : syracuseStep 159683 = 239525) B239525
theorem B421841 : Blo 155795 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B159699 : Blo 155795 159699 := bstep (se 1 (by rfl) ⟨119774, by rfl⟩ : syracuseStep 159699 = 239549) B239549
theorem B159715 : Blo 155795 159715 := bstep (se 1 (by rfl) ⟨119786, by rfl⟩ : syracuseStep 159715 = 239573) B239573
theorem B159731 : Blo 155795 159731 := bstep (se 1 (by rfl) ⟨119798, by rfl⟩ : syracuseStep 159731 = 239597) B239597
theorem B159747 : Blo 155795 159747 := bstep (se 1 (by rfl) ⟨119810, by rfl⟩ : syracuseStep 159747 = 239621) B239621
theorem B159763 : Blo 155795 159763 := bstep (se 1 (by rfl) ⟨119822, by rfl⟩ : syracuseStep 159763 = 239645) B239645
theorem B159779 : Blo 155795 159779 := bstep (se 1 (by rfl) ⟨119834, by rfl⟩ : syracuseStep 159779 = 239669) B239669
theorem B159795 : Blo 155795 159795 := bstep (se 1 (by rfl) ⟨119846, by rfl⟩ : syracuseStep 159795 = 239693) B239693
theorem B290947 : Blo 155795 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B323747 : Blo 155795 323747 := bstep (se 1 (by rfl) ⟨242810, by rfl⟩ : syracuseStep 323747 = 485621) B485621
theorem B1142981 : Blo 155795 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B356561 : Blo 155795 356561 := bstep (se 2 (by rfl) ⟨133710, by rfl⟩ : syracuseStep 356561 = 267421) B267421
theorem B356579 : Blo 155795 356579 := bstep (se 1 (by rfl) ⟨267434, by rfl⟩ : syracuseStep 356579 = 534869) B534869
theorem B225715 : Blo 155795 225715 := bstep (se 1 (by rfl) ⟨169286, by rfl⟩ : syracuseStep 225715 = 338573) B338573
theorem B848369 : Blo 155795 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B356849 : Blo 155795 356849 := bstep (se 2 (by rfl) ⟨133818, by rfl⟩ : syracuseStep 356849 = 267637) B267637
theorem B356867 : Blo 155795 356867 := bstep (se 1 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 356867 = 535301) B535301
theorem B225985 : Blo 155795 225985 := bstep (se 2 (by rfl) ⟨84744, by rfl⟩ : syracuseStep 225985 = 169489) B169489
theorem B357137 : Blo 155795 357137 := bstep (se 2 (by rfl) ⟨133926, by rfl⟩ : syracuseStep 357137 = 267853) B267853
theorem B226081 : Blo 155795 226081 := bstep (se 2 (by rfl) ⟨84780, by rfl⟩ : syracuseStep 226081 = 169561) B169561
theorem B357155 : Blo 155795 357155 := bstep (se 1 (by rfl) ⟨267866, by rfl⟩ : syracuseStep 357155 = 535733) B535733
theorem B848717 : Blo 155795 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B357425 : Blo 155795 357425 := bstep (se 2 (by rfl) ⟨134034, by rfl⟩ : syracuseStep 357425 = 268069) B268069
theorem B357443 : Blo 155795 357443 := bstep (se 1 (by rfl) ⟨268082, by rfl⟩ : syracuseStep 357443 = 536165) B536165
theorem B423053 : Blo 155795 423053 := bstep (se 3 (by rfl) ⟨79322, by rfl⟩ : syracuseStep 423053 = 158645) B158645
theorem B226577 : Blo 155795 226577 := bstep (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) B169933
theorem B357713 : Blo 155795 357713 := bstep (se 2 (by rfl) ⟨134142, by rfl⟩ : syracuseStep 357713 = 268285) B268285
theorem B357731 : Blo 155795 357731 := bstep (se 1 (by rfl) ⟨268298, by rfl⟩ : syracuseStep 357731 = 536597) B536597
theorem B358001 : Blo 155795 358001 := bstep (se 2 (by rfl) ⟨134250, by rfl⟩ : syracuseStep 358001 = 268501) B268501
theorem B358019 : Blo 155795 358019 := bstep (se 1 (by rfl) ⟨268514, by rfl⟩ : syracuseStep 358019 = 537029) B537029
theorem B685837 : Blo 155795 685837 := bstep (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) B257189
theorem B1013573 : Blo 155795 1013573 := bstep (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) B190045
theorem B718733 : Blo 155795 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B358289 : Blo 155795 358289 := bstep (se 2 (by rfl) ⟨134358, by rfl⟩ : syracuseStep 358289 = 268717) B268717
theorem B358307 : Blo 155795 358307 := bstep (se 1 (by rfl) ⟨268730, by rfl⟩ : syracuseStep 358307 = 537461) B537461
theorem B686051 : Blo 155795 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B423917 : Blo 155795 423917 := bstep (se 3 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 423917 = 158969) B158969
theorem B227443 : Blo 155795 227443 := bstep (se 1 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 227443 = 341165) B341165
theorem B358577 : Blo 155795 358577 := bstep (se 2 (by rfl) ⟨134466, by rfl⟩ : syracuseStep 358577 = 268933) B268933
theorem B358595 : Blo 155795 358595 := bstep (se 1 (by rfl) ⟨268946, by rfl⟩ : syracuseStep 358595 = 537893) B537893
theorem B1800629 : Blo 155795 1800629 := bstep (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) B168809
theorem B358865 : Blo 155795 358865 := bstep (se 2 (by rfl) ⟨134574, by rfl⟩ : syracuseStep 358865 = 269149) B269149
theorem B358883 : Blo 155795 358883 := bstep (se 1 (by rfl) ⟨269162, by rfl⟩ : syracuseStep 358883 = 538325) B538325
theorem B227827 : Blo 155795 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B359153 : Blo 155795 359153 := bstep (se 2 (by rfl) ⟨134682, by rfl⟩ : syracuseStep 359153 = 269365) B269365
theorem B359171 : Blo 155795 359171 := bstep (se 1 (by rfl) ⟨269378, by rfl⟩ : syracuseStep 359171 = 538757) B538757
theorem B1997621 : Blo 155795 1997621 := bstep (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) B187277
theorem B424835 : Blo 155795 424835 := bstep (se 1 (by rfl) ⟨318626, by rfl⟩ : syracuseStep 424835 = 637253) B637253
theorem B359441 : Blo 155795 359441 := bstep (se 2 (by rfl) ⟨134790, by rfl⟩ : syracuseStep 359441 = 269581) B269581
theorem B359459 : Blo 155795 359459 := bstep (se 1 (by rfl) ⟨269594, by rfl⟩ : syracuseStep 359459 = 539189) B539189
theorem B1146125 : Blo 155795 1146125 := bstep (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) B429797
theorem B949553 : Blo 155795 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B949603 : Blo 155795 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B3079565 : Blo 155795 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B917219 : Blo 155795 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B425873 : Blo 155795 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B2753041 : Blo 155795 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B2196341 : Blo 155795 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B361355 : Blo 155795 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B295883 : Blo 155795 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B197579 : Blo 155795 197579 := bstep (se 1 (by rfl) ⟨148184, by rfl⟩ : syracuseStep 197579 = 296369) B296369
theorem B263243 : Blo 155795 263243 := bstep (se 1 (by rfl) ⟨197432, by rfl⟩ : syracuseStep 263243 = 394865) B394865
theorem B853085 : Blo 155795 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B296065 : Blo 155795 296065 := bstep (se 2 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 296065 = 222049) B222049
theorem B1508483 : Blo 155795 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B1246385 : Blo 155795 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B263371 : Blo 155795 263371 := bstep (se 1 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 263371 = 395057) B395057
theorem B394571 : Blo 155795 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B263513 : Blo 155795 263513 := bstep (se 2 (by rfl) ⟨98817, by rfl⟩ : syracuseStep 263513 = 197635) B197635
theorem B1344869 : Blo 155795 1344869 := bstep (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) B252163
theorem B263641 : Blo 155795 263641 := bstep (se 2 (by rfl) ⟨98865, by rfl⟩ : syracuseStep 263641 = 197731) B197731
theorem B198283 : Blo 155795 198283 := bstep (se 1 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 198283 = 297425) B297425
theorem B362263 : Blo 155795 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B296779 : Blo 155795 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B722819 : Blo 155795 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B296855 : Blo 155795 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B198551 : Blo 155795 198551 := bstep (se 1 (by rfl) ⟨148913, by rfl⟩ : syracuseStep 198551 = 297827) B297827
theorem B526283 : Blo 155795 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B264215 : Blo 155795 264215 := bstep (se 1 (by rfl) ⟨198161, by rfl⟩ : syracuseStep 264215 = 396323) B396323
theorem B4524173 : Blo 155795 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B264343 : Blo 155795 264343 := bstep (se 1 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 264343 = 396515) B396515
theorem B526553 : Blo 155795 526553 := bstep (se 2 (by rfl) ⟨197457, by rfl⟩ : syracuseStep 526553 = 394915) B394915
theorem B1181969 : Blo 155795 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B395543 : Blo 155795 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B3869045 : Blo 155795 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B166379 : Blo 155795 166379 := bstep (se 1 (by rfl) ⟨124784, by rfl⟩ : syracuseStep 166379 = 249569) B249569
theorem B297523 : Blo 155795 297523 := bstep (se 1 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 297523 = 446285) B446285
theorem B199255 : Blo 155795 199255 := bstep (se 1 (by rfl) ⟨149441, by rfl⟩ : syracuseStep 199255 = 298883) B298883
theorem B264971 : Blo 155795 264971 := bstep (se 1 (by rfl) ⟨198728, by rfl⟩ : syracuseStep 264971 = 397457) B397457
theorem B297751 : Blo 155795 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B297857 : Blo 155795 297857 := bstep (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) B223393
theorem B265099 : Blo 155795 265099 := bstep (se 1 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 265099 = 397649) B397649
theorem B527255 : Blo 155795 527255 := bstep (se 1 (by rfl) ⟨395441, by rfl⟩ : syracuseStep 527255 = 790883) B790883
theorem B396211 : Blo 155795 396211 := bstep (se 1 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 396211 = 594317) B594317
theorem B2690009 : Blo 155795 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B298009 : Blo 155795 298009 := bstep (se 2 (by rfl) ⟨111753, by rfl⟩ : syracuseStep 298009 = 223507) B223507
theorem B265241 : Blo 155795 265241 := bstep (se 2 (by rfl) ⟨99465, by rfl⟩ : syracuseStep 265241 = 198931) B198931
theorem B396353 : Blo 155795 396353 := bstep (se 2 (by rfl) ⟨148632, by rfl⟩ : syracuseStep 396353 = 297265) B297265
theorem B593027 : Blo 155795 593027 := bstep (se 1 (by rfl) ⟨444770, by rfl⟩ : syracuseStep 593027 = 889541) B889541
theorem B593041 : Blo 155795 593041 := bstep (se 2 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 593041 = 444781) B444781
theorem B265369 : Blo 155795 265369 := bstep (se 2 (by rfl) ⟨99513, by rfl⟩ : syracuseStep 265369 = 199027) B199027
theorem B789911 : Blo 155795 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B527795 : Blo 155795 527795 := bstep (se 1 (by rfl) ⟨395846, by rfl⟩ : syracuseStep 527795 = 791693) B791693
theorem B593345 : Blo 155795 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B167383 : Blo 155795 167383 := bstep (se 1 (by rfl) ⟨125537, by rfl⟩ : syracuseStep 167383 = 251075) B251075
theorem B1183409 : Blo 155795 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B528065 : Blo 155795 528065 := bstep (se 2 (by rfl) ⟨198024, by rfl⟩ : syracuseStep 528065 = 396049) B396049
theorem B265943 : Blo 155795 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B266071 : Blo 155795 266071 := bstep (se 1 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 266071 = 399107) B399107
theorem B594013 : Blo 155795 594013 := bstep (se 3 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 594013 = 222755) B222755
theorem B1183895 : Blo 155795 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B528605 : Blo 155795 528605 := bstep (se 3 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 528605 = 198227) B198227
theorem B168203 : Blo 155795 168203 := bstep (se 1 (by rfl) ⟨126152, by rfl⟩ : syracuseStep 168203 = 252305) B252305
theorem B200971 : Blo 155795 200971 := bstep (se 1 (by rfl) ⟨150728, by rfl⟩ : syracuseStep 200971 = 301457) B301457
theorem B233753 : Blo 155795 233753 := bstep (se 2 (by rfl) ⟨87657, by rfl⟩ : syracuseStep 233753 = 175315) B175315
theorem B397619 : Blo 155795 397619 := bstep (se 1 (by rfl) ⟨298214, by rfl⟩ : syracuseStep 397619 = 596429) B596429
theorem B299315 : Blo 155795 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B4886897 : Blo 155795 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B233867 : Blo 155795 233867 := bstep (se 1 (by rfl) ⟨175400, by rfl⟩ : syracuseStep 233867 = 350801) B350801
theorem B233879 : Blo 155795 233879 := bstep (se 1 (by rfl) ⟨175409, by rfl⟩ : syracuseStep 233879 = 350819) B350819
theorem B299467 : Blo 155795 299467 := bstep (se 1 (by rfl) ⟨224600, by rfl⟩ : syracuseStep 299467 = 449201) B449201
theorem B266699 : Blo 155795 266699 := bstep (se 1 (by rfl) ⟨200024, by rfl⟩ : syracuseStep 266699 = 400049) B400049
theorem B233945 : Blo 155795 233945 := bstep (se 2 (by rfl) ⟨87729, by rfl⟩ : syracuseStep 233945 = 175459) B175459
theorem B234059 : Blo 155795 234059 := bstep (se 1 (by rfl) ⟨175544, by rfl⟩ : syracuseStep 234059 = 351089) B351089
theorem B266827 : Blo 155795 266827 := bstep (se 1 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 266827 = 400241) B400241
theorem B234071 : Blo 155795 234071 := bstep (se 1 (by rfl) ⟨175553, by rfl⟩ : syracuseStep 234071 = 351107) B351107
theorem B234137 : Blo 155795 234137 := bstep (se 2 (by rfl) ⟨87801, by rfl⟩ : syracuseStep 234137 = 175603) B175603
theorem B266969 : Blo 155795 266969 := bstep (se 2 (by rfl) ⟨100113, by rfl⟩ : syracuseStep 266969 = 200227) B200227
theorem B234251 : Blo 155795 234251 := bstep (se 1 (by rfl) ⟨175688, by rfl⟩ : syracuseStep 234251 = 351377) B351377
theorem B234263 : Blo 155795 234263 := bstep (se 1 (by rfl) ⟨175697, by rfl⟩ : syracuseStep 234263 = 351395) B351395
theorem B299801 : Blo 155795 299801 := bstep (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) B224851
theorem B398155 : Blo 155795 398155 := bstep (se 1 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 398155 = 597233) B597233
theorem B234329 : Blo 155795 234329 := bstep (se 2 (by rfl) ⟨87873, by rfl⟩ : syracuseStep 234329 = 175747) B175747
theorem B267097 : Blo 155795 267097 := bstep (se 2 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 267097 = 200323) B200323
theorem B431041 : Blo 155795 431041 := bstep (se 2 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 431041 = 323281) B323281
theorem B234443 : Blo 155795 234443 := bstep (se 1 (by rfl) ⟨175832, by rfl⟩ : syracuseStep 234443 = 351665) B351665
theorem B234455 : Blo 155795 234455 := bstep (se 1 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 234455 = 351683) B351683
theorem B398297 : Blo 155795 398297 := bstep (se 2 (by rfl) ⟨149361, by rfl⟩ : syracuseStep 398297 = 298723) B298723
theorem B234521 : Blo 155795 234521 := bstep (se 2 (by rfl) ⟨87945, by rfl⟩ : syracuseStep 234521 = 175891) B175891
theorem B562265 : Blo 155795 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B234635 : Blo 155795 234635 := bstep (se 1 (by rfl) ⟨175976, by rfl⟩ : syracuseStep 234635 = 351953) B351953
theorem B234647 : Blo 155795 234647 := bstep (se 1 (by rfl) ⟨175985, by rfl⟩ : syracuseStep 234647 = 351971) B351971
theorem B201943 : Blo 155795 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B234713 : Blo 155795 234713 := bstep (se 2 (by rfl) ⟨88017, by rfl⟩ : syracuseStep 234713 = 176035) B176035
theorem B234827 : Blo 155795 234827 := bstep (se 1 (by rfl) ⟨176120, by rfl⟩ : syracuseStep 234827 = 352241) B352241
theorem B529739 : Blo 155795 529739 := bstep (se 1 (by rfl) ⟨397304, by rfl⟩ : syracuseStep 529739 = 794609) B794609
theorem B234839 : Blo 155795 234839 := bstep (se 1 (by rfl) ⟨176129, by rfl⟩ : syracuseStep 234839 = 352259) B352259
theorem B595289 : Blo 155795 595289 := bstep (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) B446467
theorem B1086821 : Blo 155795 1086821 := bstep (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) B203779
theorem B300439 : Blo 155795 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B267671 : Blo 155795 267671 := bstep (se 1 (by rfl) ⟨200753, by rfl⟩ : syracuseStep 267671 = 401507) B401507
theorem B234905 : Blo 155795 234905 := bstep (se 2 (by rfl) ⟨88089, by rfl⟩ : syracuseStep 234905 = 176179) B176179
theorem B890291 : Blo 155795 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B169399 : Blo 155795 169399 := bstep (se 1 (by rfl) ⟨127049, by rfl⟩ : syracuseStep 169399 = 254099) B254099
theorem B235019 : Blo 155795 235019 := bstep (se 1 (by rfl) ⟨176264, by rfl⟩ : syracuseStep 235019 = 352529) B352529
theorem B235031 : Blo 155795 235031 := bstep (se 1 (by rfl) ⟨176273, by rfl⟩ : syracuseStep 235031 = 352547) B352547
theorem B267799 : Blo 155795 267799 := bstep (se 1 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 267799 = 401699) B401699
theorem B235097 : Blo 155795 235097 := bstep (se 2 (by rfl) ⟨88161, by rfl⟩ : syracuseStep 235097 = 176323) B176323
theorem B530009 : Blo 155795 530009 := bstep (se 2 (by rfl) ⟨198753, by rfl⟩ : syracuseStep 530009 = 397507) B397507
theorem B1021571 : Blo 155795 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B235211 : Blo 155795 235211 := bstep (se 1 (by rfl) ⟨176408, by rfl⟩ : syracuseStep 235211 = 352817) B352817
theorem B235223 : Blo 155795 235223 := bstep (se 1 (by rfl) ⟨176417, by rfl⟩ : syracuseStep 235223 = 352835) B352835
theorem B399127 : Blo 155795 399127 := bstep (se 1 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 399127 = 598691) B598691
theorem B235289 : Blo 155795 235289 := bstep (se 2 (by rfl) ⟨88233, by rfl⟩ : syracuseStep 235289 = 176467) B176467
theorem B300875 : Blo 155795 300875 := bstep (se 1 (by rfl) ⟨225656, by rfl⟩ : syracuseStep 300875 = 451313) B451313
theorem B1283971 : Blo 155795 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B235403 : Blo 155795 235403 := bstep (se 1 (by rfl) ⟨176552, by rfl⟩ : syracuseStep 235403 = 353105) B353105
theorem B235415 : Blo 155795 235415 := bstep (se 1 (by rfl) ⟨176561, by rfl⟩ : syracuseStep 235415 = 353123) B353123
theorem B300953 : Blo 155795 300953 := bstep (se 2 (by rfl) ⟨112857, by rfl⟩ : syracuseStep 300953 = 225715) B225715
theorem B235481 : Blo 155795 235481 := bstep (se 2 (by rfl) ⟨88305, by rfl⟩ : syracuseStep 235481 = 176611) B176611
theorem B202775 : Blo 155795 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B235595 : Blo 155795 235595 := bstep (se 1 (by rfl) ⟨176696, by rfl⟩ : syracuseStep 235595 = 353393) B353393
theorem B235607 : Blo 155795 235607 := bstep (se 1 (by rfl) ⟨176705, by rfl⟩ : syracuseStep 235607 = 353411) B353411
theorem B268427 : Blo 155795 268427 := bstep (se 1 (by rfl) ⟨201320, by rfl⟩ : syracuseStep 268427 = 402641) B402641
theorem B235673 : Blo 155795 235673 := bstep (se 2 (by rfl) ⟨88377, by rfl⟩ : syracuseStep 235673 = 176755) B176755
theorem B399563 : Blo 155795 399563 := bstep (se 1 (by rfl) ⟨299672, by rfl⟩ : syracuseStep 399563 = 599345) B599345
theorem B301259 : Blo 155795 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B170219 : Blo 155795 170219 := bstep (se 1 (by rfl) ⟨127664, by rfl⟩ : syracuseStep 170219 = 255329) B255329
theorem B301313 : Blo 155795 301313 := bstep (se 2 (by rfl) ⟨112992, by rfl⟩ : syracuseStep 301313 = 225985) B225985
theorem B268555 : Blo 155795 268555 := bstep (se 1 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 268555 = 402833) B402833
theorem B235787 : Blo 155795 235787 := bstep (se 1 (by rfl) ⟨176840, by rfl⟩ : syracuseStep 235787 = 353681) B353681
theorem B235799 : Blo 155795 235799 := bstep (se 1 (by rfl) ⟨176849, by rfl⟩ : syracuseStep 235799 = 353699) B353699
theorem B530711 : Blo 155795 530711 := bstep (se 1 (by rfl) ⟨398033, by rfl⟩ : syracuseStep 530711 = 796067) B796067
theorem B235865 : Blo 155795 235865 := bstep (se 2 (by rfl) ⟨88449, by rfl⟩ : syracuseStep 235865 = 176899) B176899
theorem B170347 : Blo 155795 170347 := bstep (se 1 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 170347 = 255521) B255521
theorem B334219 : Blo 155795 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B268697 : Blo 155795 268697 := bstep (se 2 (by rfl) ⟨100761, by rfl⟩ : syracuseStep 268697 = 201523) B201523
theorem B235979 : Blo 155795 235979 := bstep (se 1 (by rfl) ⟨176984, by rfl⟩ : syracuseStep 235979 = 353969) B353969
theorem B235991 : Blo 155795 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B236057 : Blo 155795 236057 := bstep (se 2 (by rfl) ⟨88521, by rfl⟩ : syracuseStep 236057 = 177043) B177043
theorem B268825 : Blo 155795 268825 := bstep (se 2 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 268825 = 201619) B201619
theorem B399937 : Blo 155795 399937 := bstep (se 2 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 399937 = 299953) B299953
theorem B236171 : Blo 155795 236171 := bstep (se 1 (by rfl) ⟨177128, by rfl⟩ : syracuseStep 236171 = 354257) B354257
theorem B236183 : Blo 155795 236183 := bstep (se 1 (by rfl) ⟨177137, by rfl⟩ : syracuseStep 236183 = 354275) B354275
theorem B236249 : Blo 155795 236249 := bstep (se 2 (by rfl) ⟨88593, by rfl⟩ : syracuseStep 236249 = 177187) B177187
theorem B531251 : Blo 155795 531251 := bstep (se 1 (by rfl) ⟨398438, by rfl⟩ : syracuseStep 531251 = 796877) B796877
theorem B236363 : Blo 155795 236363 := bstep (se 1 (by rfl) ⟨177272, by rfl⟩ : syracuseStep 236363 = 354545) B354545
theorem B236375 : Blo 155795 236375 := bstep (se 1 (by rfl) ⟨177281, by rfl⟩ : syracuseStep 236375 = 354563) B354563
theorem B891749 : Blo 155795 891749 := bstep (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) B167203
theorem B793475 : Blo 155795 793475 := bstep (se 1 (by rfl) ⟨595106, by rfl⟩ : syracuseStep 793475 = 1190213) B1190213
theorem B236441 : Blo 155795 236441 := bstep (se 2 (by rfl) ⟨88665, by rfl⟩ : syracuseStep 236441 = 177331) B177331
theorem B596915 : Blo 155795 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B596929 : Blo 155795 596929 := bstep (se 2 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 596929 = 447697) B447697
theorem B236555 : Blo 155795 236555 := bstep (se 1 (by rfl) ⟨177416, by rfl⟩ : syracuseStep 236555 = 354833) B354833
theorem B236567 : Blo 155795 236567 := bstep (se 1 (by rfl) ⟨177425, by rfl⟩ : syracuseStep 236567 = 354851) B354851
theorem B531521 : Blo 155795 531521 := bstep (se 2 (by rfl) ⟨199320, by rfl⟩ : syracuseStep 531521 = 398641) B398641
theorem B269399 : Blo 155795 269399 := bstep (se 1 (by rfl) ⟨202049, by rfl⟩ : syracuseStep 269399 = 404099) B404099
theorem B236633 : Blo 155795 236633 := bstep (se 2 (by rfl) ⟨88737, by rfl⟩ : syracuseStep 236633 = 177475) B177475
theorem B302231 : Blo 155795 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B400535 : Blo 155795 400535 := bstep (se 1 (by rfl) ⟨300401, by rfl⟩ : syracuseStep 400535 = 600803) B600803
theorem B236747 : Blo 155795 236747 := bstep (se 1 (by rfl) ⟨177560, by rfl⟩ : syracuseStep 236747 = 355121) B355121
theorem B236759 : Blo 155795 236759 := bstep (se 1 (by rfl) ⟨177569, by rfl⟩ : syracuseStep 236759 = 355139) B355139
theorem B269527 : Blo 155795 269527 := bstep (se 1 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 269527 = 404291) B404291
theorem B236825 : Blo 155795 236825 := bstep (se 2 (by rfl) ⟨88809, by rfl⟩ : syracuseStep 236825 = 177619) B177619
theorem B892205 : Blo 155795 892205 := bstep (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) B334577
theorem B236939 : Blo 155795 236939 := bstep (se 1 (by rfl) ⟨177704, by rfl⟩ : syracuseStep 236939 = 355409) B355409
theorem B236951 : Blo 155795 236951 := bstep (se 1 (by rfl) ⟨177713, by rfl⟩ : syracuseStep 236951 = 355427) B355427
theorem B237017 : Blo 155795 237017 := bstep (se 2 (by rfl) ⟨88881, by rfl⟩ : syracuseStep 237017 = 177763) B177763
theorem B237131 : Blo 155795 237131 := bstep (se 1 (by rfl) ⟨177848, by rfl⟩ : syracuseStep 237131 = 355697) B355697
theorem B237143 : Blo 155795 237143 := bstep (se 1 (by rfl) ⟨177857, by rfl⟩ : syracuseStep 237143 = 355715) B355715
theorem B532061 : Blo 155795 532061 := bstep (se 3 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 532061 = 199523) B199523
theorem B269963 : Blo 155795 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B237209 : Blo 155795 237209 := bstep (se 2 (by rfl) ⟨88953, by rfl⟩ : syracuseStep 237209 = 177907) B177907
theorem B302771 : Blo 155795 302771 := bstep (se 1 (by rfl) ⟨227078, by rfl⟩ : syracuseStep 302771 = 454157) B454157
theorem B335603 : Blo 155795 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B237323 : Blo 155795 237323 := bstep (se 1 (by rfl) ⟨177992, by rfl⟩ : syracuseStep 237323 = 355985) B355985
theorem B237335 : Blo 155795 237335 := bstep (se 1 (by rfl) ⟨178001, by rfl⟩ : syracuseStep 237335 = 356003) B356003
theorem B270155 : Blo 155795 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B237401 : Blo 155795 237401 := bstep (se 2 (by rfl) ⟨89025, by rfl⟩ : syracuseStep 237401 = 178051) B178051
theorem B401345 : Blo 155795 401345 := bstep (se 2 (by rfl) ⟨150504, by rfl⟩ : syracuseStep 401345 = 301009) B301009
theorem B237515 : Blo 155795 237515 := bstep (se 1 (by rfl) ⟨178136, by rfl⟩ : syracuseStep 237515 = 356273) B356273
theorem B237527 : Blo 155795 237527 := bstep (se 1 (by rfl) ⟨178145, by rfl⟩ : syracuseStep 237527 = 356291) B356291
theorem B892889 : Blo 155795 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B237593 : Blo 155795 237593 := bstep (se 2 (by rfl) ⟨89097, by rfl⟩ : syracuseStep 237593 = 178195) B178195
theorem B761987 : Blo 155795 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B237707 : Blo 155795 237707 := bstep (se 1 (by rfl) ⟨178280, by rfl⟩ : syracuseStep 237707 = 356561) B356561
theorem B237719 : Blo 155795 237719 := bstep (se 1 (by rfl) ⟨178289, by rfl⟩ : syracuseStep 237719 = 356579) B356579
theorem B303257 : Blo 155795 303257 := bstep (se 2 (by rfl) ⟨113721, by rfl⟩ : syracuseStep 303257 = 227443) B227443
theorem B237785 : Blo 155795 237785 := bstep (se 2 (by rfl) ⟨89169, by rfl⟩ : syracuseStep 237785 = 178339) B178339
theorem B565579 : Blo 155795 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B237899 : Blo 155795 237899 := bstep (se 1 (by rfl) ⟨178424, by rfl⟩ : syracuseStep 237899 = 356849) B356849
theorem B237911 : Blo 155795 237911 := bstep (se 1 (by rfl) ⟨178433, by rfl⟩ : syracuseStep 237911 = 356867) B356867
theorem B237977 : Blo 155795 237977 := bstep (se 2 (by rfl) ⟨89241, by rfl⟩ : syracuseStep 237977 = 178483) B178483
theorem B401881 : Blo 155795 401881 := bstep (se 2 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 401881 = 301411) B301411
theorem B238091 : Blo 155795 238091 := bstep (se 1 (by rfl) ⟨178568, by rfl⟩ : syracuseStep 238091 = 357137) B357137
theorem B238103 : Blo 155795 238103 := bstep (se 1 (by rfl) ⟨178577, by rfl⟩ : syracuseStep 238103 = 357155) B357155
theorem B565811 : Blo 155795 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B336449 : Blo 155795 336449 := bstep (se 2 (by rfl) ⟨126168, by rfl⟩ : syracuseStep 336449 = 252337) B252337
theorem B238169 : Blo 155795 238169 := bstep (se 2 (by rfl) ⟨89313, by rfl⟩ : syracuseStep 238169 = 178627) B178627
theorem B303769 : Blo 155795 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B533195 : Blo 155795 533195 := bstep (se 1 (by rfl) ⟨399896, by rfl⟩ : syracuseStep 533195 = 799793) B799793
theorem B238283 : Blo 155795 238283 := bstep (se 1 (by rfl) ⟨178712, by rfl⟩ : syracuseStep 238283 = 357425) B357425
theorem B238295 : Blo 155795 238295 := bstep (se 1 (by rfl) ⟨178721, by rfl⟩ : syracuseStep 238295 = 357443) B357443
theorem B762641 : Blo 155795 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B238361 : Blo 155795 238361 := bstep (se 2 (by rfl) ⟨89385, by rfl⟩ : syracuseStep 238361 = 178771) B178771
theorem B598859 : Blo 155795 598859 := bstep (se 1 (by rfl) ⟨449144, by rfl⟩ : syracuseStep 598859 = 898289) B898289
theorem B598873 : Blo 155795 598873 := bstep (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) B449155
theorem B500573 : Blo 155795 500573 := bstep (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) B187715
theorem B238475 : Blo 155795 238475 := bstep (se 1 (by rfl) ⟨178856, by rfl⟩ : syracuseStep 238475 = 357713) B357713
theorem B336791 : Blo 155795 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B238487 : Blo 155795 238487 := bstep (se 1 (by rfl) ⟨178865, by rfl⟩ : syracuseStep 238487 = 357731) B357731
theorem B533465 : Blo 155795 533465 := bstep (se 2 (by rfl) ⟨200049, by rfl⟩ : syracuseStep 533465 = 400099) B400099
theorem B238553 : Blo 155795 238553 := bstep (se 2 (by rfl) ⟨89457, by rfl⟩ : syracuseStep 238553 = 178915) B178915
theorem B238667 : Blo 155795 238667 := bstep (se 1 (by rfl) ⟨179000, by rfl⟩ : syracuseStep 238667 = 358001) B358001
theorem B238679 : Blo 155795 238679 := bstep (se 1 (by rfl) ⟨179009, by rfl⟩ : syracuseStep 238679 = 358019) B358019
theorem B238745 : Blo 155795 238745 := bstep (se 2 (by rfl) ⟨89529, by rfl⟩ : syracuseStep 238745 = 179059) B179059
theorem B238859 : Blo 155795 238859 := bstep (se 1 (by rfl) ⟨179144, by rfl⟩ : syracuseStep 238859 = 358289) B358289
theorem B238871 : Blo 155795 238871 := bstep (se 1 (by rfl) ⟨179153, by rfl⟩ : syracuseStep 238871 = 358307) B358307
theorem B238937 : Blo 155795 238937 := bstep (se 2 (by rfl) ⟨89601, by rfl⟩ : syracuseStep 238937 = 179203) B179203
theorem B239051 : Blo 155795 239051 := bstep (se 1 (by rfl) ⟨179288, by rfl⟩ : syracuseStep 239051 = 358577) B358577
theorem B239063 : Blo 155795 239063 := bstep (se 1 (by rfl) ⟨179297, by rfl⟩ : syracuseStep 239063 = 358595) B358595
theorem B239129 : Blo 155795 239129 := bstep (se 2 (by rfl) ⟨89673, by rfl⟩ : syracuseStep 239129 = 179347) B179347
theorem B402995 : Blo 155795 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B239243 : Blo 155795 239243 := bstep (se 1 (by rfl) ⟨179432, by rfl⟩ : syracuseStep 239243 = 358865) B358865
theorem B534167 : Blo 155795 534167 := bstep (se 1 (by rfl) ⟨400625, by rfl⟩ : syracuseStep 534167 = 801251) B801251
theorem B239255 : Blo 155795 239255 := bstep (se 1 (by rfl) ⟨179441, by rfl⟩ : syracuseStep 239255 = 358883) B358883
theorem B239321 : Blo 155795 239321 := bstep (se 2 (by rfl) ⟨89745, by rfl⟩ : syracuseStep 239321 = 179491) B179491
theorem B599831 : Blo 155795 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B239435 : Blo 155795 239435 := bstep (se 1 (by rfl) ⟨179576, by rfl⟩ : syracuseStep 239435 = 359153) B359153
theorem B239447 : Blo 155795 239447 := bstep (se 1 (by rfl) ⟨179585, by rfl⟩ : syracuseStep 239447 = 359171) B359171
theorem B403289 : Blo 155795 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B239513 : Blo 155795 239513 := bstep (se 2 (by rfl) ⟨89817, by rfl⟩ : syracuseStep 239513 = 179635) B179635
theorem B239627 : Blo 155795 239627 := bstep (se 1 (by rfl) ⟨179720, by rfl⟩ : syracuseStep 239627 = 359441) B359441
theorem B239639 : Blo 155795 239639 := bstep (se 1 (by rfl) ⟨179729, by rfl⟩ : syracuseStep 239639 = 359459) B359459
theorem B534707 : Blo 155795 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B764083 : Blo 155795 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B633035 : Blo 155795 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B469271 : Blo 155795 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B338251 : Blo 155795 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B1845605 : Blo 155795 1845605 := bstep (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) B346051
theorem B534977 : Blo 155795 534977 := bstep (se 2 (by rfl) ⟨200616, by rfl⟩ : syracuseStep 534977 = 401233) B401233
theorem B240089 : Blo 155795 240089 := bstep (se 2 (by rfl) ⟨90033, by rfl⟩ : syracuseStep 240089 = 180067) B180067
theorem B272857 : Blo 155795 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B797201 : Blo 155795 797201 := bstep (se 2 (by rfl) ⟨298950, by rfl⟩ : syracuseStep 797201 = 597901) B597901
theorem B338507 : Blo 155795 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B797363 : Blo 155795 797363 := bstep (se 1 (by rfl) ⟨598022, by rfl⟩ : syracuseStep 797363 = 1196045) B1196045
theorem B731927 : Blo 155795 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B535517 : Blo 155795 535517 := bstep (se 3 (by rfl) ⟨100409, by rfl⟩ : syracuseStep 535517 = 200819) B200819
theorem B601091 : Blo 155795 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B2141315 : Blo 155795 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B175351 : Blo 155795 175351 := bstep (se 1 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 175351 = 263027) B263027
theorem B568579 : Blo 155795 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B6991109 : Blo 155795 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B1191185 : Blo 155795 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B240983 : Blo 155795 240983 := bstep (se 1 (by rfl) ⟨180737, by rfl⟩ : syracuseStep 240983 = 361475) B361475
theorem B241049 : Blo 155795 241049 := bstep (se 2 (by rfl) ⟨90393, by rfl⟩ : syracuseStep 241049 = 180787) B180787
theorem B175531 : Blo 155795 175531 := bstep (se 1 (by rfl) ⟨131648, by rfl⟩ : syracuseStep 175531 = 263297) B263297
theorem B175639 : Blo 155795 175639 := bstep (se 1 (by rfl) ⟨131729, by rfl⟩ : syracuseStep 175639 = 263459) B263459
theorem B339481 : Blo 155795 339481 := bstep (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) B254611
theorem B929411 : Blo 155795 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B339635 : Blo 155795 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B175819 : Blo 155795 175819 := bstep (se 1 (by rfl) ⟨131864, by rfl⟩ : syracuseStep 175819 = 263729) B263729
theorem B175927 : Blo 155795 175927 := bstep (se 1 (by rfl) ⟨131945, by rfl⟩ : syracuseStep 175927 = 263891) B263891
theorem B1814489 : Blo 155795 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B176107 : Blo 155795 176107 := bstep (se 1 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 176107 = 264161) B264161
theorem B536651 : Blo 155795 536651 := bstep (se 1 (by rfl) ⟨402488, by rfl⟩ : syracuseStep 536651 = 804977) B804977
theorem B176215 : Blo 155795 176215 := bstep (se 1 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 176215 = 264323) B264323
theorem B340147 : Blo 155795 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B176395 : Blo 155795 176395 := bstep (se 1 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 176395 = 264593) B264593
theorem B536921 : Blo 155795 536921 := bstep (se 2 (by rfl) ⟨201345, by rfl⟩ : syracuseStep 536921 = 402691) B402691
theorem B176503 : Blo 155795 176503 := bstep (se 1 (by rfl) ⟨132377, by rfl⟩ : syracuseStep 176503 = 264755) B264755
theorem B2241037 : Blo 155795 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B176683 : Blo 155795 176683 := bstep (se 1 (by rfl) ⟨132512, by rfl⟩ : syracuseStep 176683 = 265025) B265025
theorem B897581 : Blo 155795 897581 := bstep (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) B336593
theorem B799307 : Blo 155795 799307 := bstep (se 1 (by rfl) ⟨599480, by rfl⟩ : syracuseStep 799307 = 1198961) B1198961
theorem B176791 : Blo 155795 176791 := bstep (se 1 (by rfl) ⟨132593, by rfl⟩ : syracuseStep 176791 = 265187) B265187
theorem B2994893 : Blo 155795 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B176971 : Blo 155795 176971 := bstep (se 1 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 176971 = 265457) B265457
theorem B340823 : Blo 155795 340823 := bstep (se 1 (by rfl) ⟨255617, by rfl⟩ : syracuseStep 340823 = 511235) B511235
theorem B340865 : Blo 155795 340865 := bstep (se 2 (by rfl) ⟨127824, by rfl⟩ : syracuseStep 340865 = 255649) B255649
theorem B177079 : Blo 155795 177079 := bstep (se 1 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 177079 = 265619) B265619
theorem B668675 : Blo 155795 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B537623 : Blo 155795 537623 := bstep (se 1 (by rfl) ⟨403217, by rfl⟩ : syracuseStep 537623 = 806435) B806435
theorem B177259 : Blo 155795 177259 := bstep (se 1 (by rfl) ⟨132944, by rfl⟩ : syracuseStep 177259 = 265889) B265889
theorem B177367 : Blo 155795 177367 := bstep (se 1 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 177367 = 266051) B266051
theorem B177547 : Blo 155795 177547 := bstep (se 1 (by rfl) ⟨133160, by rfl⟩ : syracuseStep 177547 = 266321) B266321
theorem B177655 : Blo 155795 177655 := bstep (se 1 (by rfl) ⟨133241, by rfl⟩ : syracuseStep 177655 = 266483) B266483
theorem B538163 : Blo 155795 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B177835 : Blo 155795 177835 := bstep (se 1 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 177835 = 266753) B266753
theorem B177943 : Blo 155795 177943 := bstep (se 1 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 177943 = 266915) B266915
theorem B538433 : Blo 155795 538433 := bstep (se 2 (by rfl) ⟨201912, by rfl⟩ : syracuseStep 538433 = 403825) B403825
theorem B2176885 : Blo 155795 2176885 := bstep (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) B204083
theorem B178123 : Blo 155795 178123 := bstep (se 1 (by rfl) ⟨133592, by rfl⟩ : syracuseStep 178123 = 267185) B267185
theorem B604205 : Blo 155795 604205 := bstep (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) B226577
theorem B178231 : Blo 155795 178231 := bstep (se 1 (by rfl) ⟨133673, by rfl⟩ : syracuseStep 178231 = 267347) B267347
theorem B211033 : Blo 155795 211033 := bstep (se 2 (by rfl) ⟨79137, by rfl⟩ : syracuseStep 211033 = 158275) B158275
theorem B374977 : Blo 155795 374977 := bstep (se 2 (by rfl) ⟨140616, by rfl⟩ : syracuseStep 374977 = 281233) B281233
theorem B178411 : Blo 155795 178411 := bstep (se 1 (by rfl) ⟨133808, by rfl⟩ : syracuseStep 178411 = 267617) B267617
theorem B801089 : Blo 155795 801089 := bstep (se 2 (by rfl) ⟨300408, by rfl⟩ : syracuseStep 801089 = 600817) B600817
theorem B440641 : Blo 155795 440641 := bstep (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) B330481
theorem B178519 : Blo 155795 178519 := bstep (se 1 (by rfl) ⟨133889, by rfl⟩ : syracuseStep 178519 = 267779) B267779
theorem B538969 : Blo 155795 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B538973 : Blo 155795 538973 := bstep (se 3 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 538973 = 202115) B202115
theorem B342401 : Blo 155795 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B178699 : Blo 155795 178699 := bstep (se 1 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 178699 = 268049) B268049
theorem B670301 : Blo 155795 670301 := bstep (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) B251363
theorem B178807 : Blo 155795 178807 := bstep (se 1 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 178807 = 268211) B268211
theorem B506519 : Blo 155795 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B899857 : Blo 155795 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B178987 : Blo 155795 178987 := bstep (se 1 (by rfl) ⟨134240, by rfl⟩ : syracuseStep 178987 = 268481) B268481
theorem B604979 : Blo 155795 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B179095 : Blo 155795 179095 := bstep (se 1 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 179095 = 268643) B268643
theorem B900019 : Blo 155795 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B1195073 : Blo 155795 1195073 := bstep (se 2 (by rfl) ⟨448152, by rfl⟩ : syracuseStep 1195073 = 896305) B896305
theorem B179275 : Blo 155795 179275 := bstep (se 1 (by rfl) ⟨134456, by rfl⟩ : syracuseStep 179275 = 268913) B268913
theorem B179383 : Blo 155795 179383 := bstep (se 1 (by rfl) ⟨134537, by rfl⟩ : syracuseStep 179383 = 269075) B269075
theorem B670999 : Blo 155795 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B179563 : Blo 155795 179563 := bstep (se 1 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 179563 = 269345) B269345
theorem B179671 : Blo 155795 179671 := bstep (se 1 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 179671 = 269507) B269507
theorem B1359767 : Blo 155795 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B803033 : Blo 155795 803033 := bstep (se 2 (by rfl) ⟨301137, by rfl⟩ : syracuseStep 803033 = 602275) B602275
theorem B606467 : Blo 155795 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B573713 : Blo 155795 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B2900555 : Blo 155795 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B672401 : Blo 155795 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B1197017 : Blo 155795 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B214039 : Blo 155795 214039 := bstep (se 1 (by rfl) ⟨160529, by rfl⟩ : syracuseStep 214039 = 321059) B321059
theorem B508979 : Blo 155795 508979 := bstep (se 1 (by rfl) ⟨381734, by rfl⟩ : syracuseStep 508979 = 763469) B763469
theorem B509017 : Blo 155795 509017 := bstep (se 2 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 509017 = 381763) B381763
theorem B1295621 : Blo 155795 1295621 := bstep (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) B242929
theorem B4080941 : Blo 155795 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B771677 : Blo 155795 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B4867715 : Blo 155795 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B1361681 : Blo 155795 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B804653 : Blo 155795 804653 := bstep (se 3 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 804653 = 301745) B301745
theorem B575383 : Blo 155795 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B1263539 : Blo 155795 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B379073 : Blo 155795 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B1362251 : Blo 155795 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B281075 : Blo 155795 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B608771 : Blo 155795 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B379457 : Blo 155795 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B281227 : Blo 155795 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B215831 : Blo 155795 215831 := bstep (se 1 (by rfl) ⟨161873, by rfl⟩ : syracuseStep 215831 = 323747) B323747
theorem B2411441 : Blo 155795 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B282035 : Blo 155795 282035 := bstep (se 1 (by rfl) ⟨211526, by rfl⟩ : syracuseStep 282035 = 423053) B423053
theorem B3919373 : Blo 155795 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B675373 : Blo 155795 675373 := bstep (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) B253265
theorem B511553 : Blo 155795 511553 := bstep (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) B383665
theorem B905053 : Blo 155795 905053 := bstep (se 3 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 905053 = 339395) B339395
theorem B2576245 : Blo 155795 2576245 := bstep (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) B241523
theorem B675715 : Blo 155795 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B479155 : Blo 155795 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B446411 : Blo 155795 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B282611 : Blo 155795 282611 := bstep (se 1 (by rfl) ⟨211958, by rfl⟩ : syracuseStep 282611 = 423917) B423917
theorem B4837637 : Blo 155795 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B1200419 : Blo 155795 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B446809 : Blo 155795 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B1266137 : Blo 155795 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B1331747 : Blo 155795 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B283223 : Blo 155795 283223 := bstep (se 1 (by rfl) ⟨212417, by rfl⟩ : syracuseStep 283223 = 424835) B424835
theorem B643673 : Blo 155795 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B676673 : Blo 155795 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B2053043 : Blo 155795 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B611479 : Blo 155795 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B283915 : Blo 155795 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B644573 : Blo 155795 644573 := bstep (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) B241715
theorem B448051 : Blo 155795 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B808541 : Blo 155795 808541 := bstep (se 3 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 808541 = 303203) B303203
theorem B382657 : Blo 155795 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B251927 : Blo 155795 251927 := bstep (se 1 (by rfl) ⟨188945, by rfl⟩ : syracuseStep 251927 = 377891) B377891
theorem B2676887 : Blo 155795 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B678091 : Blo 155795 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B350603 : Blo 155795 350603 := bstep (se 1 (by rfl) ⟨262952, by rfl⟩ : syracuseStep 350603 = 525905) B525905
theorem B678289 : Blo 155795 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B350657 : Blo 155795 350657 := bstep (se 2 (by rfl) ⟨131496, by rfl⟩ : syracuseStep 350657 = 262993) B262993
theorem B678365 : Blo 155795 678365 := bstep (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) B254387
theorem B285299 : Blo 155795 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B350873 : Blo 155795 350873 := bstep (se 2 (by rfl) ⟨131577, by rfl⟩ : syracuseStep 350873 = 263155) B263155
theorem B1268401 : Blo 155795 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B350963 : Blo 155795 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B350999 : Blo 155795 350999 := bstep (se 1 (by rfl) ⟨263249, by rfl⟩ : syracuseStep 350999 = 526499) B526499
theorem B285529 : Blo 155795 285529 := bstep (se 2 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 285529 = 214147) B214147
theorem B613271 : Blo 155795 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B351179 : Blo 155795 351179 := bstep (se 1 (by rfl) ⟨263384, by rfl⟩ : syracuseStep 351179 = 526769) B526769
theorem B351233 : Blo 155795 351233 := bstep (se 2 (by rfl) ⟨131712, by rfl⟩ : syracuseStep 351233 = 263425) B263425
theorem B285761 : Blo 155795 285761 := bstep (se 2 (by rfl) ⟨107160, by rfl⟩ : syracuseStep 285761 = 214321) B214321
theorem B351449 : Blo 155795 351449 := bstep (se 2 (by rfl) ⟨131793, by rfl⟩ : syracuseStep 351449 = 263587) B263587
theorem B351539 : Blo 155795 351539 := bstep (se 1 (by rfl) ⟨263654, by rfl⟩ : syracuseStep 351539 = 527309) B527309
theorem B351575 : Blo 155795 351575 := bstep (se 1 (by rfl) ⟨263681, by rfl⟩ : syracuseStep 351575 = 527363) B527363
theorem B351755 : Blo 155795 351755 := bstep (se 1 (by rfl) ⟨263816, by rfl⟩ : syracuseStep 351755 = 527633) B527633
theorem B351809 : Blo 155795 351809 := bstep (se 2 (by rfl) ⟨131928, by rfl⟩ : syracuseStep 351809 = 263857) B263857
theorem B1892045 : Blo 155795 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B352025 : Blo 155795 352025 := bstep (se 2 (by rfl) ⟨132009, by rfl⟩ : syracuseStep 352025 = 264019) B264019
theorem B352115 : Blo 155795 352115 := bstep (se 1 (by rfl) ⟨264086, by rfl⟩ : syracuseStep 352115 = 528173) B528173
theorem B352151 : Blo 155795 352151 := bstep (se 1 (by rfl) ⟨264113, by rfl⟩ : syracuseStep 352151 = 528227) B528227
theorem B352331 : Blo 155795 352331 := bstep (se 1 (by rfl) ⟨264248, by rfl⟩ : syracuseStep 352331 = 528497) B528497
theorem B352385 : Blo 155795 352385 := bstep (se 2 (by rfl) ⟨132144, by rfl⟩ : syracuseStep 352385 = 264289) B264289
theorem B155799 : Blo 155795 155799 := bstep (se 1 (by rfl) ⟨116849, by rfl⟩ : syracuseStep 155799 = 233699) B233699
theorem B155819 : Blo 155795 155819 := bstep (se 1 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 155819 = 233729) B233729
theorem B1466545 : Blo 155795 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B155831 : Blo 155795 155831 := bstep (se 1 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 155831 = 233747) B233747
theorem B286913 : Blo 155795 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B155851 : Blo 155795 155851 := bstep (se 1 (by rfl) ⟨116888, by rfl⟩ : syracuseStep 155851 = 233777) B233777
theorem B155863 : Blo 155795 155863 := bstep (se 1 (by rfl) ⟨116897, by rfl⟩ : syracuseStep 155863 = 233795) B233795
theorem B155883 : Blo 155795 155883 := bstep (se 1 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 155883 = 233825) B233825
theorem B155895 : Blo 155795 155895 := bstep (se 1 (by rfl) ⟨116921, by rfl⟩ : syracuseStep 155895 = 233843) B233843
theorem B155915 : Blo 155795 155915 := bstep (se 1 (by rfl) ⟨116936, by rfl⟩ : syracuseStep 155915 = 233873) B233873
theorem B155927 : Blo 155795 155927 := bstep (se 1 (by rfl) ⟨116945, by rfl⟩ : syracuseStep 155927 = 233891) B233891
theorem B155947 : Blo 155795 155947 := bstep (se 1 (by rfl) ⟨116960, by rfl⟩ : syracuseStep 155947 = 233921) B233921
theorem B155959 : Blo 155795 155959 := bstep (se 1 (by rfl) ⟨116969, by rfl⟩ : syracuseStep 155959 = 233939) B233939
theorem B155979 : Blo 155795 155979 := bstep (se 1 (by rfl) ⟨116984, by rfl⟩ : syracuseStep 155979 = 233969) B233969
theorem B155991 : Blo 155795 155991 := bstep (se 1 (by rfl) ⟨116993, by rfl⟩ : syracuseStep 155991 = 233987) B233987
theorem B352601 : Blo 155795 352601 := bstep (se 2 (by rfl) ⟨132225, by rfl⟩ : syracuseStep 352601 = 264451) B264451
theorem B156011 : Blo 155795 156011 := bstep (se 1 (by rfl) ⟨117008, by rfl⟩ : syracuseStep 156011 = 234017) B234017
theorem B156023 : Blo 155795 156023 := bstep (se 1 (by rfl) ⟨117017, by rfl⟩ : syracuseStep 156023 = 234035) B234035
theorem B156043 : Blo 155795 156043 := bstep (se 1 (by rfl) ⟨117032, by rfl⟩ : syracuseStep 156043 = 234065) B234065
theorem B319883 : Blo 155795 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B156055 : Blo 155795 156055 := bstep (se 1 (by rfl) ⟨117041, by rfl⟩ : syracuseStep 156055 = 234083) B234083
theorem B450967 : Blo 155795 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B156075 : Blo 155795 156075 := bstep (se 1 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 156075 = 234113) B234113
theorem B352691 : Blo 155795 352691 := bstep (se 1 (by rfl) ⟨264518, by rfl⟩ : syracuseStep 352691 = 529037) B529037
theorem B156087 : Blo 155795 156087 := bstep (se 1 (by rfl) ⟨117065, by rfl⟩ : syracuseStep 156087 = 234131) B234131
theorem B156107 : Blo 155795 156107 := bstep (se 1 (by rfl) ⟨117080, by rfl⟩ : syracuseStep 156107 = 234161) B234161
theorem B156119 : Blo 155795 156119 := bstep (se 1 (by rfl) ⟨117089, by rfl⟩ : syracuseStep 156119 = 234179) B234179
theorem B352727 : Blo 155795 352727 := bstep (se 1 (by rfl) ⟨264545, by rfl⟩ : syracuseStep 352727 = 529091) B529091
theorem B156139 : Blo 155795 156139 := bstep (se 1 (by rfl) ⟨117104, by rfl⟩ : syracuseStep 156139 = 234209) B234209
theorem B156151 : Blo 155795 156151 := bstep (se 1 (by rfl) ⟨117113, by rfl⟩ : syracuseStep 156151 = 234227) B234227
theorem B156171 : Blo 155795 156171 := bstep (se 1 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 156171 = 234257) B234257
theorem B156183 : Blo 155795 156183 := bstep (se 1 (by rfl) ⟨117137, by rfl⟩ : syracuseStep 156183 = 234275) B234275
theorem B156203 : Blo 155795 156203 := bstep (se 1 (by rfl) ⟨117152, by rfl⟩ : syracuseStep 156203 = 234305) B234305
theorem B156215 : Blo 155795 156215 := bstep (se 1 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 156215 = 234323) B234323
theorem B156235 : Blo 155795 156235 := bstep (se 1 (by rfl) ⟨117176, by rfl⟩ : syracuseStep 156235 = 234353) B234353
theorem B156247 : Blo 155795 156247 := bstep (se 1 (by rfl) ⟨117185, by rfl⟩ : syracuseStep 156247 = 234371) B234371
theorem B156267 : Blo 155795 156267 := bstep (se 1 (by rfl) ⟨117200, by rfl⟩ : syracuseStep 156267 = 234401) B234401
theorem B156279 : Blo 155795 156279 := bstep (se 1 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 156279 = 234419) B234419
theorem B156299 : Blo 155795 156299 := bstep (se 1 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 156299 = 234449) B234449
theorem B352907 : Blo 155795 352907 := bstep (se 1 (by rfl) ⟨264680, by rfl⟩ : syracuseStep 352907 = 529361) B529361
theorem B156311 : Blo 155795 156311 := bstep (se 1 (by rfl) ⟨117233, by rfl⟩ : syracuseStep 156311 = 234467) B234467
theorem B156331 : Blo 155795 156331 := bstep (se 1 (by rfl) ⟨117248, by rfl⟩ : syracuseStep 156331 = 234497) B234497
theorem B156343 : Blo 155795 156343 := bstep (se 1 (by rfl) ⟨117257, by rfl⟩ : syracuseStep 156343 = 234515) B234515
theorem B352961 : Blo 155795 352961 := bstep (se 2 (by rfl) ⟨132360, by rfl⟩ : syracuseStep 352961 = 264721) B264721
theorem B156363 : Blo 155795 156363 := bstep (se 1 (by rfl) ⟨117272, by rfl⟩ : syracuseStep 156363 = 234545) B234545
theorem B156375 : Blo 155795 156375 := bstep (se 1 (by rfl) ⟨117281, by rfl⟩ : syracuseStep 156375 = 234563) B234563
theorem B320215 : Blo 155795 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B156395 : Blo 155795 156395 := bstep (se 1 (by rfl) ⟨117296, by rfl⟩ : syracuseStep 156395 = 234593) B234593
theorem B2712305 : Blo 155795 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B156407 : Blo 155795 156407 := bstep (se 1 (by rfl) ⟨117305, by rfl⟩ : syracuseStep 156407 = 234611) B234611
theorem B156427 : Blo 155795 156427 := bstep (se 1 (by rfl) ⟨117320, by rfl⟩ : syracuseStep 156427 = 234641) B234641
theorem B156439 : Blo 155795 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B156459 : Blo 155795 156459 := bstep (se 1 (by rfl) ⟨117344, by rfl⟩ : syracuseStep 156459 = 234689) B234689
theorem B156471 : Blo 155795 156471 := bstep (se 1 (by rfl) ⟨117353, by rfl⟩ : syracuseStep 156471 = 234707) B234707
theorem B1008449 : Blo 155795 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B156491 : Blo 155795 156491 := bstep (se 1 (by rfl) ⟨117368, by rfl⟩ : syracuseStep 156491 = 234737) B234737
theorem B156503 : Blo 155795 156503 := bstep (se 1 (by rfl) ⟨117377, by rfl⟩ : syracuseStep 156503 = 234755) B234755
theorem B320345 : Blo 155795 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B156523 : Blo 155795 156523 := bstep (se 1 (by rfl) ⟨117392, by rfl⟩ : syracuseStep 156523 = 234785) B234785
theorem B156535 : Blo 155795 156535 := bstep (se 1 (by rfl) ⟨117401, by rfl⟩ : syracuseStep 156535 = 234803) B234803
theorem B156555 : Blo 155795 156555 := bstep (se 1 (by rfl) ⟨117416, by rfl⟩ : syracuseStep 156555 = 234833) B234833
theorem B156567 : Blo 155795 156567 := bstep (se 1 (by rfl) ⟨117425, by rfl⟩ : syracuseStep 156567 = 234851) B234851
theorem B353177 : Blo 155795 353177 := bstep (se 2 (by rfl) ⟨132441, by rfl⟩ : syracuseStep 353177 = 264883) B264883
theorem B156587 : Blo 155795 156587 := bstep (se 1 (by rfl) ⟨117440, by rfl⟩ : syracuseStep 156587 = 234881) B234881
theorem B156599 : Blo 155795 156599 := bstep (se 1 (by rfl) ⟨117449, by rfl⟩ : syracuseStep 156599 = 234899) B234899
theorem B156619 : Blo 155795 156619 := bstep (se 1 (by rfl) ⟨117464, by rfl⟩ : syracuseStep 156619 = 234929) B234929
theorem B156631 : Blo 155795 156631 := bstep (se 1 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 156631 = 234947) B234947
theorem B156651 : Blo 155795 156651 := bstep (se 1 (by rfl) ⟨117488, by rfl⟩ : syracuseStep 156651 = 234977) B234977
theorem B353267 : Blo 155795 353267 := bstep (se 1 (by rfl) ⟨264950, by rfl⟩ : syracuseStep 353267 = 529901) B529901
theorem B156663 : Blo 155795 156663 := bstep (se 1 (by rfl) ⟨117497, by rfl⟩ : syracuseStep 156663 = 234995) B234995
theorem B156683 : Blo 155795 156683 := bstep (se 1 (by rfl) ⟨117512, by rfl⟩ : syracuseStep 156683 = 235025) B235025
theorem B680977 : Blo 155795 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B156695 : Blo 155795 156695 := bstep (se 1 (by rfl) ⟨117521, by rfl⟩ : syracuseStep 156695 = 235043) B235043
theorem B353303 : Blo 155795 353303 := bstep (se 1 (by rfl) ⟨264977, by rfl⟩ : syracuseStep 353303 = 529955) B529955
theorem B156715 : Blo 155795 156715 := bstep (se 1 (by rfl) ⟨117536, by rfl⟩ : syracuseStep 156715 = 235073) B235073
theorem B156727 : Blo 155795 156727 := bstep (se 1 (by rfl) ⟨117545, by rfl⟩ : syracuseStep 156727 = 235091) B235091
theorem B156747 : Blo 155795 156747 := bstep (se 1 (by rfl) ⟨117560, by rfl⟩ : syracuseStep 156747 = 235121) B235121
theorem B156759 : Blo 155795 156759 := bstep (se 1 (by rfl) ⟨117569, by rfl⟩ : syracuseStep 156759 = 235139) B235139
theorem B156779 : Blo 155795 156779 := bstep (se 1 (by rfl) ⟨117584, by rfl⟩ : syracuseStep 156779 = 235169) B235169
theorem B156791 : Blo 155795 156791 := bstep (se 1 (by rfl) ⟨117593, by rfl⟩ : syracuseStep 156791 = 235187) B235187
theorem B156811 : Blo 155795 156811 := bstep (se 1 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 156811 = 235217) B235217
theorem B156823 : Blo 155795 156823 := bstep (se 1 (by rfl) ⟨117617, by rfl⟩ : syracuseStep 156823 = 235235) B235235
theorem B156843 : Blo 155795 156843 := bstep (se 1 (by rfl) ⟨117632, by rfl⟩ : syracuseStep 156843 = 235265) B235265
theorem B1336499 : Blo 155795 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B156855 : Blo 155795 156855 := bstep (se 1 (by rfl) ⟨117641, by rfl⟩ : syracuseStep 156855 = 235283) B235283
theorem B156875 : Blo 155795 156875 := bstep (se 1 (by rfl) ⟨117656, by rfl⟩ : syracuseStep 156875 = 235313) B235313
theorem B353483 : Blo 155795 353483 := bstep (se 1 (by rfl) ⟨265112, by rfl⟩ : syracuseStep 353483 = 530225) B530225
theorem B156887 : Blo 155795 156887 := bstep (se 1 (by rfl) ⟨117665, by rfl⟩ : syracuseStep 156887 = 235331) B235331
theorem B156907 : Blo 155795 156907 := bstep (se 1 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 156907 = 235361) B235361
theorem B156919 : Blo 155795 156919 := bstep (se 1 (by rfl) ⟨117689, by rfl⟩ : syracuseStep 156919 = 235379) B235379
theorem B353537 : Blo 155795 353537 := bstep (se 2 (by rfl) ⟨132576, by rfl⟩ : syracuseStep 353537 = 265153) B265153
theorem B156939 : Blo 155795 156939 := bstep (se 1 (by rfl) ⟨117704, by rfl⟩ : syracuseStep 156939 = 235409) B235409
theorem B156951 : Blo 155795 156951 := bstep (se 1 (by rfl) ⟨117713, by rfl⟩ : syracuseStep 156951 = 235427) B235427
theorem B156971 : Blo 155795 156971 := bstep (se 1 (by rfl) ⟨117728, by rfl⟩ : syracuseStep 156971 = 235457) B235457
theorem B156983 : Blo 155795 156983 := bstep (se 1 (by rfl) ⟨117737, by rfl⟩ : syracuseStep 156983 = 235475) B235475
theorem B157003 : Blo 155795 157003 := bstep (se 1 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 157003 = 235505) B235505
theorem B157015 : Blo 155795 157015 := bstep (se 1 (by rfl) ⟨117761, by rfl⟩ : syracuseStep 157015 = 235523) B235523
theorem B157035 : Blo 155795 157035 := bstep (se 1 (by rfl) ⟨117776, by rfl⟩ : syracuseStep 157035 = 235553) B235553
theorem B157047 : Blo 155795 157047 := bstep (se 1 (by rfl) ⟨117785, by rfl⟩ : syracuseStep 157047 = 235571) B235571
theorem B157067 : Blo 155795 157067 := bstep (se 1 (by rfl) ⟨117800, by rfl⟩ : syracuseStep 157067 = 235601) B235601
theorem B157079 : Blo 155795 157079 := bstep (se 1 (by rfl) ⟨117809, by rfl⟩ : syracuseStep 157079 = 235619) B235619
theorem B157099 : Blo 155795 157099 := bstep (se 1 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 157099 = 235649) B235649
theorem B157111 : Blo 155795 157111 := bstep (se 1 (by rfl) ⟨117833, by rfl⟩ : syracuseStep 157111 = 235667) B235667
theorem B157131 : Blo 155795 157131 := bstep (se 1 (by rfl) ⟨117848, by rfl⟩ : syracuseStep 157131 = 235697) B235697
theorem B157143 : Blo 155795 157143 := bstep (se 1 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 157143 = 235715) B235715
theorem B353753 : Blo 155795 353753 := bstep (se 2 (by rfl) ⟨132657, by rfl⟩ : syracuseStep 353753 = 265315) B265315
theorem B157163 : Blo 155795 157163 := bstep (se 1 (by rfl) ⟨117872, by rfl⟩ : syracuseStep 157163 = 235745) B235745
theorem B157175 : Blo 155795 157175 := bstep (se 1 (by rfl) ⟨117881, by rfl⟩ : syracuseStep 157175 = 235763) B235763
theorem B288257 : Blo 155795 288257 := bstep (se 2 (by rfl) ⟨108096, by rfl⟩ : syracuseStep 288257 = 216193) B216193
theorem B1205765 : Blo 155795 1205765 := bstep (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) B226081
theorem B157195 : Blo 155795 157195 := bstep (se 1 (by rfl) ⟨117896, by rfl⟩ : syracuseStep 157195 = 235793) B235793
theorem B157207 : Blo 155795 157207 := bstep (se 1 (by rfl) ⟨117905, by rfl⟩ : syracuseStep 157207 = 235811) B235811
theorem B157227 : Blo 155795 157227 := bstep (se 1 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 157227 = 235841) B235841
theorem B353843 : Blo 155795 353843 := bstep (se 1 (by rfl) ⟨265382, by rfl⟩ : syracuseStep 353843 = 530765) B530765
theorem B157239 : Blo 155795 157239 := bstep (se 1 (by rfl) ⟨117929, by rfl⟩ : syracuseStep 157239 = 235859) B235859
theorem B157259 : Blo 155795 157259 := bstep (se 1 (by rfl) ⟨117944, by rfl⟩ : syracuseStep 157259 = 235889) B235889
theorem B157271 : Blo 155795 157271 := bstep (se 1 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 157271 = 235907) B235907
theorem B353879 : Blo 155795 353879 := bstep (se 1 (by rfl) ⟨265409, by rfl⟩ : syracuseStep 353879 = 530819) B530819
theorem B157291 : Blo 155795 157291 := bstep (se 1 (by rfl) ⟨117968, by rfl⟩ : syracuseStep 157291 = 235937) B235937
theorem B157303 : Blo 155795 157303 := bstep (se 1 (by rfl) ⟨117977, by rfl⟩ : syracuseStep 157303 = 235955) B235955
theorem B157323 : Blo 155795 157323 := bstep (se 1 (by rfl) ⟨117992, by rfl⟩ : syracuseStep 157323 = 235985) B235985
theorem B157335 : Blo 155795 157335 := bstep (se 1 (by rfl) ⟨118001, by rfl⟩ : syracuseStep 157335 = 236003) B236003
theorem B157355 : Blo 155795 157355 := bstep (se 1 (by rfl) ⟨118016, by rfl⟩ : syracuseStep 157355 = 236033) B236033
theorem B157367 : Blo 155795 157367 := bstep (se 1 (by rfl) ⟨118025, by rfl⟩ : syracuseStep 157367 = 236051) B236051
theorem B157387 : Blo 155795 157387 := bstep (se 1 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 157387 = 236081) B236081
theorem B452299 : Blo 155795 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B157399 : Blo 155795 157399 := bstep (se 1 (by rfl) ⟨118049, by rfl⟩ : syracuseStep 157399 = 236099) B236099
theorem B157419 : Blo 155795 157419 := bstep (se 1 (by rfl) ⟨118064, by rfl⟩ : syracuseStep 157419 = 236129) B236129
theorem B4056817 : Blo 155795 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B157431 : Blo 155795 157431 := bstep (se 1 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 157431 = 236147) B236147
theorem B354059 : Blo 155795 354059 := bstep (se 1 (by rfl) ⟨265544, by rfl⟩ : syracuseStep 354059 = 531089) B531089
theorem B157451 : Blo 155795 157451 := bstep (se 1 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 157451 = 236177) B236177
theorem B845585 : Blo 155795 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B157463 : Blo 155795 157463 := bstep (se 1 (by rfl) ⟨118097, by rfl⟩ : syracuseStep 157463 = 236195) B236195
theorem B157483 : Blo 155795 157483 := bstep (se 1 (by rfl) ⟨118112, by rfl⟩ : syracuseStep 157483 = 236225) B236225
theorem B157495 : Blo 155795 157495 := bstep (se 1 (by rfl) ⟨118121, by rfl⟩ : syracuseStep 157495 = 236243) B236243
theorem B354113 : Blo 155795 354113 := bstep (se 2 (by rfl) ⟨132792, by rfl⟩ : syracuseStep 354113 = 265585) B265585
theorem B157515 : Blo 155795 157515 := bstep (se 1 (by rfl) ⟨118136, by rfl⟩ : syracuseStep 157515 = 236273) B236273
theorem B157527 : Blo 155795 157527 := bstep (se 1 (by rfl) ⟨118145, by rfl⟩ : syracuseStep 157527 = 236291) B236291
theorem B157547 : Blo 155795 157547 := bstep (se 1 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 157547 = 236321) B236321
theorem B157559 : Blo 155795 157559 := bstep (se 1 (by rfl) ⟨118169, by rfl⟩ : syracuseStep 157559 = 236339) B236339
theorem B157579 : Blo 155795 157579 := bstep (se 1 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 157579 = 236369) B236369
theorem B157591 : Blo 155795 157591 := bstep (se 1 (by rfl) ⟨118193, by rfl⟩ : syracuseStep 157591 = 236387) B236387
theorem B157611 : Blo 155795 157611 := bstep (se 1 (by rfl) ⟨118208, by rfl⟩ : syracuseStep 157611 = 236417) B236417
theorem B157623 : Blo 155795 157623 := bstep (se 1 (by rfl) ⟨118217, by rfl⟩ : syracuseStep 157623 = 236435) B236435
theorem B157643 : Blo 155795 157643 := bstep (se 1 (by rfl) ⟨118232, by rfl⟩ : syracuseStep 157643 = 236465) B236465
theorem B157655 : Blo 155795 157655 := bstep (se 1 (by rfl) ⟨118241, by rfl⟩ : syracuseStep 157655 = 236483) B236483
theorem B452573 : Blo 155795 452573 := bstep (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) B169715
theorem B157675 : Blo 155795 157675 := bstep (se 1 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 157675 = 236513) B236513
theorem B157687 : Blo 155795 157687 := bstep (se 1 (by rfl) ⟨118265, by rfl⟩ : syracuseStep 157687 = 236531) B236531
theorem B157707 : Blo 155795 157707 := bstep (se 1 (by rfl) ⟨118280, by rfl⟩ : syracuseStep 157707 = 236561) B236561
theorem B157719 : Blo 155795 157719 := bstep (se 1 (by rfl) ⟨118289, by rfl⟩ : syracuseStep 157719 = 236579) B236579
theorem B354329 : Blo 155795 354329 := bstep (se 2 (by rfl) ⟨132873, by rfl⟩ : syracuseStep 354329 = 265747) B265747
theorem B157739 : Blo 155795 157739 := bstep (se 1 (by rfl) ⟨118304, by rfl⟩ : syracuseStep 157739 = 236609) B236609
theorem B157751 : Blo 155795 157751 := bstep (se 1 (by rfl) ⟨118313, by rfl⟩ : syracuseStep 157751 = 236627) B236627
theorem B157771 : Blo 155795 157771 := bstep (se 1 (by rfl) ⟨118328, by rfl⟩ : syracuseStep 157771 = 236657) B236657
theorem B157783 : Blo 155795 157783 := bstep (se 1 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 157783 = 236675) B236675
theorem B157803 : Blo 155795 157803 := bstep (se 1 (by rfl) ⟨118352, by rfl⟩ : syracuseStep 157803 = 236705) B236705
theorem B354419 : Blo 155795 354419 := bstep (se 1 (by rfl) ⟨265814, by rfl⟩ : syracuseStep 354419 = 531629) B531629
theorem B157815 : Blo 155795 157815 := bstep (se 1 (by rfl) ⟨118361, by rfl⟩ : syracuseStep 157815 = 236723) B236723
theorem B157835 : Blo 155795 157835 := bstep (se 1 (by rfl) ⟨118376, by rfl⟩ : syracuseStep 157835 = 236753) B236753
theorem B354455 : Blo 155795 354455 := bstep (se 1 (by rfl) ⟨265841, by rfl⟩ : syracuseStep 354455 = 531683) B531683
theorem B157847 : Blo 155795 157847 := bstep (se 1 (by rfl) ⟨118385, by rfl⟩ : syracuseStep 157847 = 236771) B236771
theorem B157867 : Blo 155795 157867 := bstep (se 1 (by rfl) ⟨118400, by rfl⟩ : syracuseStep 157867 = 236801) B236801
theorem B157879 : Blo 155795 157879 := bstep (se 1 (by rfl) ⟨118409, by rfl⟩ : syracuseStep 157879 = 236819) B236819
theorem B157899 : Blo 155795 157899 := bstep (se 1 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 157899 = 236849) B236849
theorem B157911 : Blo 155795 157911 := bstep (se 1 (by rfl) ⟨118433, by rfl⟩ : syracuseStep 157911 = 236867) B236867
theorem B157931 : Blo 155795 157931 := bstep (se 1 (by rfl) ⟨118448, by rfl⟩ : syracuseStep 157931 = 236897) B236897
theorem B157943 : Blo 155795 157943 := bstep (se 1 (by rfl) ⟨118457, by rfl⟩ : syracuseStep 157943 = 236915) B236915
theorem B157963 : Blo 155795 157963 := bstep (se 1 (by rfl) ⟨118472, by rfl⟩ : syracuseStep 157963 = 236945) B236945
theorem B1108241 : Blo 155795 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B157975 : Blo 155795 157975 := bstep (se 1 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 157975 = 236963) B236963
theorem B157995 : Blo 155795 157995 := bstep (se 1 (by rfl) ⟨118496, by rfl⟩ : syracuseStep 157995 = 236993) B236993
theorem B452915 : Blo 155795 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B158007 : Blo 155795 158007 := bstep (se 1 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 158007 = 237011) B237011
theorem B354635 : Blo 155795 354635 := bstep (se 1 (by rfl) ⟨265976, by rfl⟩ : syracuseStep 354635 = 531953) B531953
theorem B158027 : Blo 155795 158027 := bstep (se 1 (by rfl) ⟨118520, by rfl⟩ : syracuseStep 158027 = 237041) B237041
theorem B158039 : Blo 155795 158039 := bstep (se 1 (by rfl) ⟨118529, by rfl⟩ : syracuseStep 158039 = 237059) B237059
theorem B158059 : Blo 155795 158059 := bstep (se 1 (by rfl) ⟨118544, by rfl⟩ : syracuseStep 158059 = 237089) B237089
theorem B158071 : Blo 155795 158071 := bstep (se 1 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 158071 = 237107) B237107
theorem B354689 : Blo 155795 354689 := bstep (se 2 (by rfl) ⟨133008, by rfl⟩ : syracuseStep 354689 = 266017) B266017
theorem B158091 : Blo 155795 158091 := bstep (se 1 (by rfl) ⟨118568, by rfl⟩ : syracuseStep 158091 = 237137) B237137
theorem B158103 : Blo 155795 158103 := bstep (se 1 (by rfl) ⟨118577, by rfl⟩ : syracuseStep 158103 = 237155) B237155
theorem B158123 : Blo 155795 158123 := bstep (se 1 (by rfl) ⟨118592, by rfl⟩ : syracuseStep 158123 = 237185) B237185
theorem B158135 : Blo 155795 158135 := bstep (se 1 (by rfl) ⟨118601, by rfl⟩ : syracuseStep 158135 = 237203) B237203
theorem B158155 : Blo 155795 158155 := bstep (se 1 (by rfl) ⟨118616, by rfl⟩ : syracuseStep 158155 = 237233) B237233
theorem B158167 : Blo 155795 158167 := bstep (se 1 (by rfl) ⟨118625, by rfl⟩ : syracuseStep 158167 = 237251) B237251
theorem B158187 : Blo 155795 158187 := bstep (se 1 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 158187 = 237281) B237281
theorem B158199 : Blo 155795 158199 := bstep (se 1 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 158199 = 237299) B237299
theorem B158219 : Blo 155795 158219 := bstep (se 1 (by rfl) ⟨118664, by rfl⟩ : syracuseStep 158219 = 237329) B237329
theorem B158231 : Blo 155795 158231 := bstep (se 1 (by rfl) ⟨118673, by rfl⟩ : syracuseStep 158231 = 237347) B237347
theorem B223769 : Blo 155795 223769 := bstep (se 2 (by rfl) ⟨83913, by rfl⟩ : syracuseStep 223769 = 167827) B167827
theorem B158251 : Blo 155795 158251 := bstep (se 1 (by rfl) ⟨118688, by rfl⟩ : syracuseStep 158251 = 237377) B237377
theorem B158263 : Blo 155795 158263 := bstep (se 1 (by rfl) ⟨118697, by rfl⟩ : syracuseStep 158263 = 237395) B237395
theorem B158283 : Blo 155795 158283 := bstep (se 1 (by rfl) ⟨118712, by rfl⟩ : syracuseStep 158283 = 237425) B237425
theorem B158295 : Blo 155795 158295 := bstep (se 1 (by rfl) ⟨118721, by rfl⟩ : syracuseStep 158295 = 237443) B237443
theorem B354905 : Blo 155795 354905 := bstep (se 2 (by rfl) ⟨133089, by rfl⟩ : syracuseStep 354905 = 266179) B266179
theorem B158315 : Blo 155795 158315 := bstep (se 1 (by rfl) ⟨118736, by rfl⟩ : syracuseStep 158315 = 237473) B237473
theorem B158327 : Blo 155795 158327 := bstep (se 1 (by rfl) ⟨118745, by rfl⟩ : syracuseStep 158327 = 237491) B237491
theorem B158347 : Blo 155795 158347 := bstep (se 1 (by rfl) ⟨118760, by rfl⟩ : syracuseStep 158347 = 237521) B237521
theorem B158359 : Blo 155795 158359 := bstep (se 1 (by rfl) ⟨118769, by rfl⟩ : syracuseStep 158359 = 237539) B237539
theorem B158379 : Blo 155795 158379 := bstep (se 1 (by rfl) ⟨118784, by rfl⟩ : syracuseStep 158379 = 237569) B237569
theorem B354995 : Blo 155795 354995 := bstep (se 1 (by rfl) ⟨266246, by rfl⟩ : syracuseStep 354995 = 532493) B532493
theorem B158391 : Blo 155795 158391 := bstep (se 1 (by rfl) ⟨118793, by rfl⟩ : syracuseStep 158391 = 237587) B237587
theorem B158411 : Blo 155795 158411 := bstep (se 1 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 158411 = 237617) B237617
theorem B191179 : Blo 155795 191179 := bstep (se 1 (by rfl) ⟨143384, by rfl⟩ : syracuseStep 191179 = 286769) B286769
theorem B355031 : Blo 155795 355031 := bstep (se 1 (by rfl) ⟨266273, by rfl⟩ : syracuseStep 355031 = 532547) B532547
theorem B158423 : Blo 155795 158423 := bstep (se 1 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 158423 = 237635) B237635
theorem B158443 : Blo 155795 158443 := bstep (se 1 (by rfl) ⟨118832, by rfl⟩ : syracuseStep 158443 = 237665) B237665
theorem B158455 : Blo 155795 158455 := bstep (se 1 (by rfl) ⟨118841, by rfl⟩ : syracuseStep 158455 = 237683) B237683
theorem B158475 : Blo 155795 158475 := bstep (se 1 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 158475 = 237713) B237713
theorem B158487 : Blo 155795 158487 := bstep (se 1 (by rfl) ⟨118865, by rfl⟩ : syracuseStep 158487 = 237731) B237731
theorem B158507 : Blo 155795 158507 := bstep (se 1 (by rfl) ⟨118880, by rfl⟩ : syracuseStep 158507 = 237761) B237761
theorem B158519 : Blo 155795 158519 := bstep (se 1 (by rfl) ⟨118889, by rfl⟩ : syracuseStep 158519 = 237779) B237779
theorem B158539 : Blo 155795 158539 := bstep (se 1 (by rfl) ⟨118904, by rfl⟩ : syracuseStep 158539 = 237809) B237809
theorem B158551 : Blo 155795 158551 := bstep (se 1 (by rfl) ⟨118913, by rfl⟩ : syracuseStep 158551 = 237827) B237827
theorem B387929 : Blo 155795 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B158571 : Blo 155795 158571 := bstep (se 1 (by rfl) ⟨118928, by rfl⟩ : syracuseStep 158571 = 237857) B237857
theorem B158583 : Blo 155795 158583 := bstep (se 1 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 158583 = 237875) B237875
theorem B355211 : Blo 155795 355211 := bstep (se 1 (by rfl) ⟨266408, by rfl⟩ : syracuseStep 355211 = 532817) B532817
theorem B158603 : Blo 155795 158603 := bstep (se 1 (by rfl) ⟨118952, by rfl⟩ : syracuseStep 158603 = 237905) B237905
theorem B158615 : Blo 155795 158615 := bstep (se 1 (by rfl) ⟨118961, by rfl⟩ : syracuseStep 158615 = 237923) B237923
theorem B158635 : Blo 155795 158635 := bstep (se 1 (by rfl) ⟨118976, by rfl⟩ : syracuseStep 158635 = 237953) B237953
theorem B158647 : Blo 155795 158647 := bstep (se 1 (by rfl) ⟨118985, by rfl⟩ : syracuseStep 158647 = 237971) B237971
theorem B355265 : Blo 155795 355265 := bstep (se 2 (by rfl) ⟨133224, by rfl⟩ : syracuseStep 355265 = 266449) B266449
theorem B158667 : Blo 155795 158667 := bstep (se 1 (by rfl) ⟨119000, by rfl⟩ : syracuseStep 158667 = 238001) B238001
theorem B158679 : Blo 155795 158679 := bstep (se 1 (by rfl) ⟨119009, by rfl⟩ : syracuseStep 158679 = 238019) B238019
theorem B158699 : Blo 155795 158699 := bstep (se 1 (by rfl) ⟨119024, by rfl⟩ : syracuseStep 158699 = 238049) B238049
theorem B158711 : Blo 155795 158711 := bstep (se 1 (by rfl) ⟨119033, by rfl⟩ : syracuseStep 158711 = 238067) B238067
theorem B158731 : Blo 155795 158731 := bstep (se 1 (by rfl) ⟨119048, by rfl⟩ : syracuseStep 158731 = 238097) B238097
theorem B158743 : Blo 155795 158743 := bstep (se 1 (by rfl) ⟨119057, by rfl⟩ : syracuseStep 158743 = 238115) B238115
theorem B158763 : Blo 155795 158763 := bstep (se 1 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 158763 = 238145) B238145
theorem B158775 : Blo 155795 158775 := bstep (se 1 (by rfl) ⟨119081, by rfl⟩ : syracuseStep 158775 = 238163) B238163
theorem B158795 : Blo 155795 158795 := bstep (se 1 (by rfl) ⟨119096, by rfl⟩ : syracuseStep 158795 = 238193) B238193
theorem B158807 : Blo 155795 158807 := bstep (se 1 (by rfl) ⟨119105, by rfl⟩ : syracuseStep 158807 = 238211) B238211
theorem B158827 : Blo 155795 158827 := bstep (se 1 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 158827 = 238241) B238241
theorem B158839 : Blo 155795 158839 := bstep (se 1 (by rfl) ⟨119129, by rfl⟩ : syracuseStep 158839 = 238259) B238259
theorem B158859 : Blo 155795 158859 := bstep (se 1 (by rfl) ⟨119144, by rfl⟩ : syracuseStep 158859 = 238289) B238289
theorem B224407 : Blo 155795 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B158871 : Blo 155795 158871 := bstep (se 1 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 158871 = 238307) B238307
theorem B355481 : Blo 155795 355481 := bstep (se 2 (by rfl) ⟨133305, by rfl⟩ : syracuseStep 355481 = 266611) B266611
theorem B158891 : Blo 155795 158891 := bstep (se 1 (by rfl) ⟨119168, by rfl⟩ : syracuseStep 158891 = 238337) B238337
theorem B158903 : Blo 155795 158903 := bstep (se 1 (by rfl) ⟨119177, by rfl⟩ : syracuseStep 158903 = 238355) B238355
theorem B158923 : Blo 155795 158923 := bstep (se 1 (by rfl) ⟨119192, by rfl⟩ : syracuseStep 158923 = 238385) B238385
theorem B158935 : Blo 155795 158935 := bstep (se 1 (by rfl) ⟨119201, by rfl⟩ : syracuseStep 158935 = 238403) B238403
theorem B453853 : Blo 155795 453853 := bstep (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) B170195
theorem B158955 : Blo 155795 158955 := bstep (se 1 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 158955 = 238433) B238433
theorem B355571 : Blo 155795 355571 := bstep (se 1 (by rfl) ⟨266678, by rfl⟩ : syracuseStep 355571 = 533357) B533357
theorem B158967 : Blo 155795 158967 := bstep (se 1 (by rfl) ⟨119225, by rfl⟩ : syracuseStep 158967 = 238451) B238451
theorem B158987 : Blo 155795 158987 := bstep (se 1 (by rfl) ⟨119240, by rfl⟩ : syracuseStep 158987 = 238481) B238481
theorem B355607 : Blo 155795 355607 := bstep (se 1 (by rfl) ⟨266705, by rfl⟩ : syracuseStep 355607 = 533411) B533411
theorem B158999 : Blo 155795 158999 := bstep (se 1 (by rfl) ⟨119249, by rfl⟩ : syracuseStep 158999 = 238499) B238499
theorem B159019 : Blo 155795 159019 := bstep (se 1 (by rfl) ⟨119264, by rfl⟩ : syracuseStep 159019 = 238529) B238529
theorem B159031 : Blo 155795 159031 := bstep (se 1 (by rfl) ⟨119273, by rfl⟩ : syracuseStep 159031 = 238547) B238547
theorem B159051 : Blo 155795 159051 := bstep (se 1 (by rfl) ⟨119288, by rfl⟩ : syracuseStep 159051 = 238577) B238577
theorem B159063 : Blo 155795 159063 := bstep (se 1 (by rfl) ⟨119297, by rfl⟩ : syracuseStep 159063 = 238595) B238595
theorem B159083 : Blo 155795 159083 := bstep (se 1 (by rfl) ⟨119312, by rfl⟩ : syracuseStep 159083 = 238625) B238625
theorem B159095 : Blo 155795 159095 := bstep (se 1 (by rfl) ⟨119321, by rfl⟩ : syracuseStep 159095 = 238643) B238643
theorem B159115 : Blo 155795 159115 := bstep (se 1 (by rfl) ⟨119336, by rfl⟩ : syracuseStep 159115 = 238673) B238673
theorem B7925141 : Blo 155795 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B159127 : Blo 155795 159127 := bstep (se 1 (by rfl) ⟨119345, by rfl⟩ : syracuseStep 159127 = 238691) B238691
theorem B159147 : Blo 155795 159147 := bstep (se 1 (by rfl) ⟨119360, by rfl⟩ : syracuseStep 159147 = 238721) B238721
theorem B159159 : Blo 155795 159159 := bstep (se 1 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 159159 = 238739) B238739
theorem B355787 : Blo 155795 355787 := bstep (se 1 (by rfl) ⟨266840, by rfl⟩ : syracuseStep 355787 = 533681) B533681
theorem B159179 : Blo 155795 159179 := bstep (se 1 (by rfl) ⟨119384, by rfl⟩ : syracuseStep 159179 = 238769) B238769
theorem B159191 : Blo 155795 159191 := bstep (se 1 (by rfl) ⟨119393, by rfl⟩ : syracuseStep 159191 = 238787) B238787
theorem B159211 : Blo 155795 159211 := bstep (se 1 (by rfl) ⟨119408, by rfl⟩ : syracuseStep 159211 = 238817) B238817
theorem B159223 : Blo 155795 159223 := bstep (se 1 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 159223 = 238835) B238835
theorem B355841 : Blo 155795 355841 := bstep (se 2 (by rfl) ⟨133440, by rfl⟩ : syracuseStep 355841 = 266881) B266881
theorem B159243 : Blo 155795 159243 := bstep (se 1 (by rfl) ⟨119432, by rfl⟩ : syracuseStep 159243 = 238865) B238865
theorem B159255 : Blo 155795 159255 := bstep (se 1 (by rfl) ⟨119441, by rfl⟩ : syracuseStep 159255 = 238883) B238883
theorem B159275 : Blo 155795 159275 := bstep (se 1 (by rfl) ⟨119456, by rfl⟩ : syracuseStep 159275 = 238913) B238913
theorem B159287 : Blo 155795 159287 := bstep (se 1 (by rfl) ⟨119465, by rfl⟩ : syracuseStep 159287 = 238931) B238931
theorem B912971 : Blo 155795 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B159307 : Blo 155795 159307 := bstep (se 1 (by rfl) ⟨119480, by rfl⟩ : syracuseStep 159307 = 238961) B238961
theorem B159319 : Blo 155795 159319 := bstep (se 1 (by rfl) ⟨119489, by rfl⟩ : syracuseStep 159319 = 238979) B238979
theorem B159339 : Blo 155795 159339 := bstep (se 1 (by rfl) ⟨119504, by rfl⟩ : syracuseStep 159339 = 239009) B239009
theorem B159351 : Blo 155795 159351 := bstep (se 1 (by rfl) ⟨119513, by rfl⟩ : syracuseStep 159351 = 239027) B239027
theorem B159371 : Blo 155795 159371 := bstep (se 1 (by rfl) ⟨119528, by rfl⟩ : syracuseStep 159371 = 239057) B239057
theorem B159383 : Blo 155795 159383 := bstep (se 1 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 159383 = 239075) B239075
theorem B159403 : Blo 155795 159403 := bstep (se 1 (by rfl) ⟨119552, by rfl⟩ : syracuseStep 159403 = 239105) B239105
theorem B159415 : Blo 155795 159415 := bstep (se 1 (by rfl) ⟨119561, by rfl⟩ : syracuseStep 159415 = 239123) B239123
theorem B159435 : Blo 155795 159435 := bstep (se 1 (by rfl) ⟨119576, by rfl⟩ : syracuseStep 159435 = 239153) B239153
theorem B159447 : Blo 155795 159447 := bstep (se 1 (by rfl) ⟨119585, by rfl⟩ : syracuseStep 159447 = 239171) B239171
theorem B356057 : Blo 155795 356057 := bstep (se 2 (by rfl) ⟨133521, by rfl⟩ : syracuseStep 356057 = 267043) B267043
theorem B159467 : Blo 155795 159467 := bstep (se 1 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 159467 = 239201) B239201
theorem B159479 : Blo 155795 159479 := bstep (se 1 (by rfl) ⟨119609, by rfl⟩ : syracuseStep 159479 = 239219) B239219
theorem B159499 : Blo 155795 159499 := bstep (se 1 (by rfl) ⟨119624, by rfl⟩ : syracuseStep 159499 = 239249) B239249
theorem B1011473 : Blo 155795 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B159511 : Blo 155795 159511 := bstep (se 1 (by rfl) ⟨119633, by rfl⟩ : syracuseStep 159511 = 239267) B239267
theorem B159531 : Blo 155795 159531 := bstep (se 1 (by rfl) ⟨119648, by rfl⟩ : syracuseStep 159531 = 239297) B239297
theorem B356147 : Blo 155795 356147 := bstep (se 1 (by rfl) ⟨267110, by rfl⟩ : syracuseStep 356147 = 534221) B534221
theorem B159543 : Blo 155795 159543 := bstep (se 1 (by rfl) ⟨119657, by rfl⟩ : syracuseStep 159543 = 239315) B239315
theorem B159563 : Blo 155795 159563 := bstep (se 1 (by rfl) ⟨119672, by rfl⟩ : syracuseStep 159563 = 239345) B239345
theorem B356183 : Blo 155795 356183 := bstep (se 1 (by rfl) ⟨267137, by rfl⟩ : syracuseStep 356183 = 534275) B534275
theorem B159575 : Blo 155795 159575 := bstep (se 1 (by rfl) ⟨119681, by rfl⟩ : syracuseStep 159575 = 239363) B239363
theorem B159595 : Blo 155795 159595 := bstep (se 1 (by rfl) ⟨119696, by rfl⟩ : syracuseStep 159595 = 239393) B239393
theorem B159607 : Blo 155795 159607 := bstep (se 1 (by rfl) ⟨119705, by rfl⟩ : syracuseStep 159607 = 239411) B239411
theorem B1208195 : Blo 155795 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B159627 : Blo 155795 159627 := bstep (se 1 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 159627 = 239441) B239441
theorem B159639 : Blo 155795 159639 := bstep (se 1 (by rfl) ⟨119729, by rfl⟩ : syracuseStep 159639 = 239459) B239459
theorem B159659 : Blo 155795 159659 := bstep (se 1 (by rfl) ⟨119744, by rfl⟩ : syracuseStep 159659 = 239489) B239489
theorem B159671 : Blo 155795 159671 := bstep (se 1 (by rfl) ⟨119753, by rfl⟩ : syracuseStep 159671 = 239507) B239507
theorem B225227 : Blo 155795 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B159691 : Blo 155795 159691 := bstep (se 1 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 159691 = 239537) B239537
theorem B159703 : Blo 155795 159703 := bstep (se 1 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 159703 = 239555) B239555
theorem B159723 : Blo 155795 159723 := bstep (se 1 (by rfl) ⟨119792, by rfl⟩ : syracuseStep 159723 = 239585) B239585
theorem B159735 : Blo 155795 159735 := bstep (se 1 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 159735 = 239603) B239603
theorem B356363 : Blo 155795 356363 := bstep (se 1 (by rfl) ⟨267272, by rfl⟩ : syracuseStep 356363 = 534545) B534545
theorem B159755 : Blo 155795 159755 := bstep (se 1 (by rfl) ⟨119816, by rfl⟩ : syracuseStep 159755 = 239633) B239633
theorem B159767 : Blo 155795 159767 := bstep (se 1 (by rfl) ⟨119825, by rfl⟩ : syracuseStep 159767 = 239651) B239651
theorem B159787 : Blo 155795 159787 := bstep (se 1 (by rfl) ⟨119840, by rfl⟩ : syracuseStep 159787 = 239681) B239681
theorem B356417 : Blo 155795 356417 := bstep (se 2 (by rfl) ⟨133656, by rfl⟩ : syracuseStep 356417 = 267313) B267313
theorem B323671 : Blo 155795 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B356633 : Blo 155795 356633 := bstep (se 2 (by rfl) ⟨133737, by rfl⟩ : syracuseStep 356633 = 267475) B267475
theorem B1012013 : Blo 155795 1012013 := bstep (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) B379505
theorem B454987 : Blo 155795 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B356723 : Blo 155795 356723 := bstep (se 1 (by rfl) ⟨267542, by rfl⟩ : syracuseStep 356723 = 535085) B535085
theorem B356759 : Blo 155795 356759 := bstep (se 1 (by rfl) ⟨267569, by rfl⟩ : syracuseStep 356759 = 535139) B535139
theorem B356939 : Blo 155795 356939 := bstep (se 1 (by rfl) ⟨267704, by rfl⟩ : syracuseStep 356939 = 535409) B535409
theorem B2716253 : Blo 155795 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B356993 : Blo 155795 356993 := bstep (se 2 (by rfl) ⟨133872, by rfl⟩ : syracuseStep 356993 = 267745) B267745
theorem B717457 : Blo 155795 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B1274629 : Blo 155795 1274629 := bstep (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) B238993
theorem B357209 : Blo 155795 357209 := bstep (se 2 (by rfl) ⟨133953, by rfl⟩ : syracuseStep 357209 = 267907) B267907
theorem B357299 : Blo 155795 357299 := bstep (se 1 (by rfl) ⟨267974, by rfl⟩ : syracuseStep 357299 = 535949) B535949
theorem B685003 : Blo 155795 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B357335 : Blo 155795 357335 := bstep (se 1 (by rfl) ⟨268001, by rfl⟩ : syracuseStep 357335 = 536003) B536003
theorem B914449 : Blo 155795 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B1504291 : Blo 155795 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B357515 : Blo 155795 357515 := bstep (se 1 (by rfl) ⟨268136, by rfl⟩ : syracuseStep 357515 = 536273) B536273
theorem B357569 : Blo 155795 357569 := bstep (se 2 (by rfl) ⟨134088, by rfl⟩ : syracuseStep 357569 = 268177) B268177
theorem B357785 : Blo 155795 357785 := bstep (se 2 (by rfl) ⟨134169, by rfl⟩ : syracuseStep 357785 = 268339) B268339
theorem B357875 : Blo 155795 357875 := bstep (se 1 (by rfl) ⟨268406, by rfl⟩ : syracuseStep 357875 = 536813) B536813
theorem B357911 : Blo 155795 357911 := bstep (se 1 (by rfl) ⟨268433, by rfl⟩ : syracuseStep 357911 = 536867) B536867
theorem B358091 : Blo 155795 358091 := bstep (se 1 (by rfl) ⟨268568, by rfl⟩ : syracuseStep 358091 = 537137) B537137
theorem B358145 : Blo 155795 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B915245 : Blo 155795 915245 := bstep (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) B343217
theorem B358361 : Blo 155795 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B2553869 : Blo 155795 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B358451 : Blo 155795 358451 := bstep (se 1 (by rfl) ⟨268838, by rfl⟩ : syracuseStep 358451 = 537677) B537677
theorem B358487 : Blo 155795 358487 := bstep (se 1 (by rfl) ⟨268865, by rfl⟩ : syracuseStep 358487 = 537731) B537731
theorem B358667 : Blo 155795 358667 := bstep (se 1 (by rfl) ⟨269000, by rfl⟩ : syracuseStep 358667 = 538001) B538001
theorem B358721 : Blo 155795 358721 := bstep (se 2 (by rfl) ⟨134520, by rfl⟩ : syracuseStep 358721 = 269041) B269041
theorem B358937 : Blo 155795 358937 := bstep (se 2 (by rfl) ⟨134601, by rfl⟩ : syracuseStep 358937 = 269203) B269203
theorem B359027 : Blo 155795 359027 := bstep (se 1 (by rfl) ⟨269270, by rfl⟩ : syracuseStep 359027 = 538541) B538541
theorem B457367 : Blo 155795 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B359063 : Blo 155795 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B359243 : Blo 155795 359243 := bstep (se 1 (by rfl) ⟨269432, by rfl⟩ : syracuseStep 359243 = 538865) B538865
theorem B359297 : Blo 155795 359297 := bstep (se 2 (by rfl) ⟨134736, by rfl⟩ : syracuseStep 359297 = 269473) B269473
theorem B359513 : Blo 155795 359513 := bstep (se 2 (by rfl) ⟨134817, by rfl⟩ : syracuseStep 359513 = 269635) B269635
theorem B1211597 : Blo 155795 1211597 := bstep (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) B454349
theorem B425309 : Blo 155795 425309 := bstep (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) B159491
theorem B1212083 : Blo 155795 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B360407 : Blo 155795 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B2162933 : Blo 155795 2162933 := bstep (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) B202775
theorem B2031965 : Blo 155795 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B1933703 : Blo 155795 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B754105 : Blo 155795 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B197255 : Blo 155795 197255 := bstep (se 1 (by rfl) ⟨147941, by rfl⟩ : syracuseStep 197255 = 295883) B295883
theorem B3670721 : Blo 155795 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B2720627 : Blo 155795 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B263047 : Blo 155795 263047 := bstep (se 1 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 263047 = 394571) B394571
theorem B426953 : Blo 155795 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B853021 : Blo 155795 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B3245143 : Blo 155795 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B197903 : Blo 155795 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B3016115 : Blo 155795 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B394753 : Blo 155795 394753 := bstep (se 2 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 394753 = 296065) B296065
theorem B787979 : Blo 155795 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B263695 : Blo 155795 263695 := bstep (se 1 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 263695 = 395543) B395543
theorem B1607627 : Blo 155795 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B264235 : Blo 155795 264235 := bstep (se 1 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 264235 = 396353) B396353
theorem B395351 : Blo 155795 395351 := bstep (se 1 (by rfl) ⟨296513, by rfl⟩ : syracuseStep 395351 = 593027) B593027
theorem B264377 : Blo 155795 264377 := bstep (se 2 (by rfl) ⟨99141, by rfl⟩ : syracuseStep 264377 = 198283) B198283
theorem B526607 : Blo 155795 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B395563 : Blo 155795 395563 := bstep (se 1 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 395563 = 593345) B593345
theorem B5409089 : Blo 155795 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B395705 : Blo 155795 395705 := bstep (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) B296779
theorem B788939 : Blo 155795 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B526877 : Blo 155795 526877 := bstep (se 3 (by rfl) ⟨98789, by rfl⟩ : syracuseStep 526877 = 197579) B197579
theorem B297607 : Blo 155795 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B789263 : Blo 155795 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B265079 : Blo 155795 265079 := bstep (se 1 (by rfl) ⟨198809, by rfl⟩ : syracuseStep 265079 = 397619) B397619
theorem B1018777 : Blo 155795 1018777 := bstep (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) B764083
theorem B887831 : Blo 155795 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B363809 : Blo 155795 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B265531 : Blo 155795 265531 := bstep (se 1 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 265531 = 398297) B398297
theorem B396697 : Blo 155795 396697 := bstep (se 2 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 396697 = 297523) B297523
theorem B265673 : Blo 155795 265673 := bstep (se 2 (by rfl) ⟨99627, by rfl⟩ : syracuseStep 265673 = 199255) B199255
theorem B396859 : Blo 155795 396859 := bstep (se 1 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 396859 = 595289) B595289
theorem B724547 : Blo 155795 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B593527 : Blo 155795 593527 := bstep (se 1 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 593527 = 890291) B890291
theorem B429715 : Blo 155795 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B397001 : Blo 155795 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B1019621 : Blo 155795 1019621 := bstep (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) B191179
theorem B528281 : Blo 155795 528281 := bstep (se 2 (by rfl) ⟨198105, by rfl⟩ : syracuseStep 528281 = 396211) B396211
theorem B167951 : Blo 155795 167951 := bstep (se 1 (by rfl) ⟨125963, by rfl⟩ : syracuseStep 167951 = 251927) B251927
theorem B397345 : Blo 155795 397345 := bstep (se 2 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 397345 = 298009) B298009
theorem B266375 : Blo 155795 266375 := bstep (se 1 (by rfl) ⟨199781, by rfl⟩ : syracuseStep 266375 = 399563) B399563
theorem B200875 : Blo 155795 200875 := bstep (se 1 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 200875 = 301313) B301313
theorem B790721 : Blo 155795 790721 := bstep (se 2 (by rfl) ⟨296520, by rfl⟩ : syracuseStep 790721 = 593041) B593041
theorem B299209 : Blo 155795 299209 := bstep (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) B224407
theorem B233735 : Blo 155795 233735 := bstep (se 1 (by rfl) ⟨175301, by rfl⟩ : syracuseStep 233735 = 350603) B350603
theorem B233771 : Blo 155795 233771 := bstep (se 1 (by rfl) ⟨175328, by rfl⟩ : syracuseStep 233771 = 350657) B350657
theorem B233801 : Blo 155795 233801 := bstep (se 2 (by rfl) ⟨87675, by rfl⟩ : syracuseStep 233801 = 175351) B175351
theorem B758105 : Blo 155795 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B233915 : Blo 155795 233915 := bstep (se 1 (by rfl) ⟨175436, by rfl⟩ : syracuseStep 233915 = 350873) B350873
theorem B233975 : Blo 155795 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B233999 : Blo 155795 233999 := bstep (se 1 (by rfl) ⟨175499, by rfl⟩ : syracuseStep 233999 = 350999) B350999
theorem B234041 : Blo 155795 234041 := bstep (se 2 (by rfl) ⟨87765, by rfl⟩ : syracuseStep 234041 = 175531) B175531
theorem B594499 : Blo 155795 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B528983 : Blo 155795 528983 := bstep (se 1 (by rfl) ⟨396737, by rfl⟩ : syracuseStep 528983 = 793475) B793475
theorem B397943 : Blo 155795 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B234119 : Blo 155795 234119 := bstep (se 1 (by rfl) ⟨175589, by rfl⟩ : syracuseStep 234119 = 351179) B351179
theorem B234155 : Blo 155795 234155 := bstep (se 1 (by rfl) ⟨175616, by rfl⟩ : syracuseStep 234155 = 351233) B351233
theorem B234185 : Blo 155795 234185 := bstep (se 2 (by rfl) ⟨87819, by rfl⟩ : syracuseStep 234185 = 175639) B175639
theorem B267023 : Blo 155795 267023 := bstep (se 1 (by rfl) ⟨200267, by rfl⟩ : syracuseStep 267023 = 400535) B400535
theorem B234299 : Blo 155795 234299 := bstep (se 1 (by rfl) ⟨175724, by rfl⟩ : syracuseStep 234299 = 351449) B351449
theorem B594803 : Blo 155795 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B234359 : Blo 155795 234359 := bstep (se 1 (by rfl) ⟨175769, by rfl⟩ : syracuseStep 234359 = 351539) B351539
theorem B234383 : Blo 155795 234383 := bstep (se 1 (by rfl) ⟨175787, by rfl⟩ : syracuseStep 234383 = 351575) B351575
theorem B234425 : Blo 155795 234425 := bstep (se 2 (by rfl) ⟨87909, by rfl⟩ : syracuseStep 234425 = 175819) B175819
theorem B234503 : Blo 155795 234503 := bstep (se 1 (by rfl) ⟨175877, by rfl⟩ : syracuseStep 234503 = 351755) B351755
theorem B234539 : Blo 155795 234539 := bstep (se 1 (by rfl) ⟨175904, by rfl⟩ : syracuseStep 234539 = 351809) B351809
theorem B529469 : Blo 155795 529469 := bstep (se 3 (by rfl) ⟨99275, by rfl⟩ : syracuseStep 529469 = 198551) B198551
theorem B234569 : Blo 155795 234569 := bstep (se 2 (by rfl) ⟨87963, by rfl⟩ : syracuseStep 234569 = 175927) B175927
theorem B201847 : Blo 155795 201847 := bstep (se 1 (by rfl) ⟨151385, by rfl⟩ : syracuseStep 201847 = 302771) B302771
theorem B234683 : Blo 155795 234683 := bstep (se 1 (by rfl) ⟨176012, by rfl⟩ : syracuseStep 234683 = 352025) B352025
theorem B234743 : Blo 155795 234743 := bstep (se 1 (by rfl) ⟨176057, by rfl⟩ : syracuseStep 234743 = 352115) B352115
theorem B234767 : Blo 155795 234767 := bstep (se 1 (by rfl) ⟨176075, by rfl⟩ : syracuseStep 234767 = 352151) B352151
theorem B267563 : Blo 155795 267563 := bstep (se 1 (by rfl) ⟨200672, by rfl⟩ : syracuseStep 267563 = 401345) B401345
theorem B234809 : Blo 155795 234809 := bstep (se 2 (by rfl) ⟨88053, by rfl⟩ : syracuseStep 234809 = 176107) B176107
theorem B595259 : Blo 155795 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B234887 : Blo 155795 234887 := bstep (se 1 (by rfl) ⟨176165, by rfl⟩ : syracuseStep 234887 = 352331) B352331
theorem B234923 : Blo 155795 234923 := bstep (se 1 (by rfl) ⟨176192, by rfl⟩ : syracuseStep 234923 = 352385) B352385
theorem B202171 : Blo 155795 202171 := bstep (se 1 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 202171 = 303257) B303257
theorem B234953 : Blo 155795 234953 := bstep (se 2 (by rfl) ⟨88107, by rfl⟩ : syracuseStep 234953 = 176215) B176215
theorem B431561 : Blo 155795 431561 := bstep (se 2 (by rfl) ⟨161835, by rfl⟩ : syracuseStep 431561 = 323671) B323671
theorem B792017 : Blo 155795 792017 := bstep (se 2 (by rfl) ⟨297006, by rfl⟩ : syracuseStep 792017 = 594013) B594013
theorem B235067 : Blo 155795 235067 := bstep (se 1 (by rfl) ⟨176300, by rfl⟩ : syracuseStep 235067 = 352601) B352601
theorem B235127 : Blo 155795 235127 := bstep (se 1 (by rfl) ⟨176345, by rfl⟩ : syracuseStep 235127 = 352691) B352691
theorem B235151 : Blo 155795 235151 := bstep (se 1 (by rfl) ⟨176363, by rfl⟩ : syracuseStep 235151 = 352727) B352727
theorem B235193 : Blo 155795 235193 := bstep (se 2 (by rfl) ⟨88197, by rfl⟩ : syracuseStep 235193 = 176395) B176395
theorem B267961 : Blo 155795 267961 := bstep (se 2 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 267961 = 200971) B200971
theorem B235271 : Blo 155795 235271 := bstep (se 1 (by rfl) ⟨176453, by rfl⟩ : syracuseStep 235271 = 352907) B352907
theorem B595745 : Blo 155795 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B235307 : Blo 155795 235307 := bstep (se 1 (by rfl) ⟨176480, by rfl⟩ : syracuseStep 235307 = 352961) B352961
theorem B235337 : Blo 155795 235337 := bstep (se 2 (by rfl) ⟨88251, by rfl⟩ : syracuseStep 235337 = 176503) B176503
theorem B399239 : Blo 155795 399239 := bstep (se 1 (by rfl) ⟨299429, by rfl⟩ : syracuseStep 399239 = 598859) B598859
theorem B333715 : Blo 155795 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B399289 : Blo 155795 399289 := bstep (se 2 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 399289 = 299467) B299467
theorem B235451 : Blo 155795 235451 := bstep (se 1 (by rfl) ⟨176588, by rfl⟩ : syracuseStep 235451 = 353177) B353177
theorem B235511 : Blo 155795 235511 := bstep (se 1 (by rfl) ⟨176633, by rfl⟩ : syracuseStep 235511 = 353267) B353267
theorem B235535 : Blo 155795 235535 := bstep (se 1 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 235535 = 353303) B353303
theorem B235577 : Blo 155795 235577 := bstep (se 2 (by rfl) ⟨88341, by rfl⟩ : syracuseStep 235577 = 176683) B176683
theorem B1251389 : Blo 155795 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B890999 : Blo 155795 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B235655 : Blo 155795 235655 := bstep (se 1 (by rfl) ⟨176741, by rfl⟩ : syracuseStep 235655 = 353483) B353483
theorem B235691 : Blo 155795 235691 := bstep (se 1 (by rfl) ⟨176768, by rfl⟩ : syracuseStep 235691 = 353537) B353537
theorem B956609 : Blo 155795 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B235721 : Blo 155795 235721 := bstep (se 2 (by rfl) ⟨88395, by rfl⟩ : syracuseStep 235721 = 176791) B176791
theorem B4921613 : Blo 155795 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B235835 : Blo 155795 235835 := bstep (se 1 (by rfl) ⟨176876, by rfl⟩ : syracuseStep 235835 = 353753) B353753
theorem B235895 : Blo 155795 235895 := bstep (se 1 (by rfl) ⟨176921, by rfl⟩ : syracuseStep 235895 = 353843) B353843
theorem B268663 : Blo 155795 268663 := bstep (se 1 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 268663 = 402995) B402995
theorem B235919 : Blo 155795 235919 := bstep (se 1 (by rfl) ⟨176939, by rfl⟩ : syracuseStep 235919 = 353879) B353879
theorem B530873 : Blo 155795 530873 := bstep (se 2 (by rfl) ⟨199077, by rfl⟩ : syracuseStep 530873 = 398155) B398155
theorem B235961 : Blo 155795 235961 := bstep (se 2 (by rfl) ⟨88485, by rfl⟩ : syracuseStep 235961 = 176971) B176971
theorem B236039 : Blo 155795 236039 := bstep (se 1 (by rfl) ⟨177029, by rfl⟩ : syracuseStep 236039 = 354059) B354059
theorem B563723 : Blo 155795 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B399887 : Blo 155795 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B236075 : Blo 155795 236075 := bstep (se 1 (by rfl) ⟨177056, by rfl⟩ : syracuseStep 236075 = 354113) B354113
theorem B268859 : Blo 155795 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B236105 : Blo 155795 236105 := bstep (se 2 (by rfl) ⟨88539, by rfl⟩ : syracuseStep 236105 = 177079) B177079
theorem B301715 : Blo 155795 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B236219 : Blo 155795 236219 := bstep (se 1 (by rfl) ⟨177164, by rfl⟩ : syracuseStep 236219 = 354329) B354329
theorem B1219265 : Blo 155795 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B2005721 : Blo 155795 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B596717 : Blo 155795 596717 := bstep (se 3 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 596717 = 223769) B223769
theorem B236279 : Blo 155795 236279 := bstep (se 1 (by rfl) ⟨177209, by rfl⟩ : syracuseStep 236279 = 354419) B354419
theorem B236303 : Blo 155795 236303 := bstep (se 1 (by rfl) ⟨177227, by rfl⟩ : syracuseStep 236303 = 354455) B354455
theorem B236345 : Blo 155795 236345 := bstep (se 2 (by rfl) ⟨88629, by rfl⟩ : syracuseStep 236345 = 177259) B177259
theorem B301943 : Blo 155795 301943 := bstep (se 1 (by rfl) ⟨226457, by rfl⟩ : syracuseStep 301943 = 452915) B452915
theorem B236423 : Blo 155795 236423 := bstep (se 1 (by rfl) ⟨177317, by rfl⟩ : syracuseStep 236423 = 354635) B354635
theorem B236459 : Blo 155795 236459 := bstep (se 1 (by rfl) ⟨177344, by rfl⟩ : syracuseStep 236459 = 354689) B354689
theorem B236489 : Blo 155795 236489 := bstep (se 2 (by rfl) ⟨88683, by rfl⟩ : syracuseStep 236489 = 177367) B177367
theorem B269257 : Blo 155795 269257 := bstep (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) B201943
theorem B531467 : Blo 155795 531467 := bstep (se 1 (by rfl) ⟨398600, by rfl⟩ : syracuseStep 531467 = 797201) B797201
theorem B236603 : Blo 155795 236603 := bstep (se 1 (by rfl) ⟨177452, by rfl⟩ : syracuseStep 236603 = 354905) B354905
theorem B1219645 : Blo 155795 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B531575 : Blo 155795 531575 := bstep (se 1 (by rfl) ⟨398681, by rfl⟩ : syracuseStep 531575 = 797363) B797363
theorem B236663 : Blo 155795 236663 := bstep (se 1 (by rfl) ⟨177497, by rfl⟩ : syracuseStep 236663 = 354995) B354995
theorem B236687 : Blo 155795 236687 := bstep (se 1 (by rfl) ⟨177515, by rfl⟩ : syracuseStep 236687 = 355031) B355031
theorem B236729 : Blo 155795 236729 := bstep (se 2 (by rfl) ⟨88773, by rfl⟩ : syracuseStep 236729 = 177547) B177547
theorem B400585 : Blo 155795 400585 := bstep (se 2 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 400585 = 300439) B300439
theorem B236807 : Blo 155795 236807 := bstep (se 1 (by rfl) ⟨177605, by rfl⟩ : syracuseStep 236807 = 355211) B355211
theorem B236843 : Blo 155795 236843 := bstep (se 1 (by rfl) ⟨177632, by rfl⟩ : syracuseStep 236843 = 355265) B355265
theorem B236873 : Blo 155795 236873 := bstep (se 2 (by rfl) ⟨88827, by rfl⟩ : syracuseStep 236873 = 177655) B177655
theorem B400727 : Blo 155795 400727 := bstep (se 1 (by rfl) ⟨300545, by rfl⟩ : syracuseStep 400727 = 601091) B601091
theorem B597401 : Blo 155795 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B236987 : Blo 155795 236987 := bstep (se 1 (by rfl) ⟨177740, by rfl⟩ : syracuseStep 236987 = 355481) B355481
theorem B237047 : Blo 155795 237047 := bstep (se 1 (by rfl) ⟨177785, by rfl⟩ : syracuseStep 237047 = 355571) B355571
theorem B4660739 : Blo 155795 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B794123 : Blo 155795 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B237071 : Blo 155795 237071 := bstep (se 1 (by rfl) ⟨177803, by rfl⟩ : syracuseStep 237071 = 355607) B355607
theorem B237113 : Blo 155795 237113 := bstep (se 2 (by rfl) ⟨88917, by rfl⟩ : syracuseStep 237113 = 177835) B177835
theorem B5283427 : Blo 155795 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B237191 : Blo 155795 237191 := bstep (se 1 (by rfl) ⟨177893, by rfl⟩ : syracuseStep 237191 = 355787) B355787
theorem B237227 : Blo 155795 237227 := bstep (se 1 (by rfl) ⟨177920, by rfl⟩ : syracuseStep 237227 = 355841) B355841
theorem B794285 : Blo 155795 794285 := bstep (se 3 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 794285 = 297857) B297857
theorem B532169 : Blo 155795 532169 := bstep (se 2 (by rfl) ⟨199563, by rfl⟩ : syracuseStep 532169 = 399127) B399127
theorem B237257 : Blo 155795 237257 := bstep (se 2 (by rfl) ⟨88971, by rfl⟩ : syracuseStep 237257 = 177943) B177943
theorem B237371 : Blo 155795 237371 := bstep (se 1 (by rfl) ⟨178028, by rfl⟩ : syracuseStep 237371 = 356057) B356057
theorem B1711961 : Blo 155795 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B237431 : Blo 155795 237431 := bstep (se 1 (by rfl) ⟨178073, by rfl⟩ : syracuseStep 237431 = 356147) B356147
theorem B237455 : Blo 155795 237455 := bstep (se 1 (by rfl) ⟨178091, by rfl⟩ : syracuseStep 237455 = 356183) B356183
theorem B237497 : Blo 155795 237497 := bstep (se 2 (by rfl) ⟨89061, by rfl⟩ : syracuseStep 237497 = 178123) B178123
theorem B237575 : Blo 155795 237575 := bstep (se 1 (by rfl) ⟨178181, by rfl⟩ : syracuseStep 237575 = 356363) B356363
theorem B237611 : Blo 155795 237611 := bstep (se 1 (by rfl) ⟨178208, by rfl⟩ : syracuseStep 237611 = 356417) B356417
theorem B237641 : Blo 155795 237641 := bstep (se 2 (by rfl) ⟨89115, by rfl⟩ : syracuseStep 237641 = 178231) B178231
theorem B237755 : Blo 155795 237755 := bstep (se 1 (by rfl) ⟨178316, by rfl⟩ : syracuseStep 237755 = 356633) B356633
theorem B237815 : Blo 155795 237815 := bstep (se 1 (by rfl) ⟨178361, by rfl⟩ : syracuseStep 237815 = 356723) B356723
theorem B499969 : Blo 155795 499969 := bstep (se 2 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 499969 = 374977) B374977
theorem B237839 : Blo 155795 237839 := bstep (se 1 (by rfl) ⟨178379, by rfl⟩ : syracuseStep 237839 = 356759) B356759
theorem B237881 : Blo 155795 237881 := bstep (se 2 (by rfl) ⟨89205, by rfl⟩ : syracuseStep 237881 = 178411) B178411
theorem B598387 : Blo 155795 598387 := bstep (se 1 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 598387 = 897581) B897581
theorem B532871 : Blo 155795 532871 := bstep (se 1 (by rfl) ⟨399653, by rfl⟩ : syracuseStep 532871 = 799307) B799307
theorem B237959 : Blo 155795 237959 := bstep (se 1 (by rfl) ⟨178469, by rfl⟩ : syracuseStep 237959 = 356939) B356939
theorem B1810835 : Blo 155795 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B237995 : Blo 155795 237995 := bstep (se 1 (by rfl) ⟨178496, by rfl⟩ : syracuseStep 237995 = 356993) B356993
theorem B238025 : Blo 155795 238025 := bstep (se 2 (by rfl) ⟨89259, by rfl⟩ : syracuseStep 238025 = 178519) B178519
theorem B238139 : Blo 155795 238139 := bstep (se 1 (by rfl) ⟨178604, by rfl⟩ : syracuseStep 238139 = 357209) B357209
theorem B238199 : Blo 155795 238199 := bstep (se 1 (by rfl) ⟨178649, by rfl⟩ : syracuseStep 238199 = 357299) B357299
theorem B238223 : Blo 155795 238223 := bstep (se 1 (by rfl) ⟨178667, by rfl⟩ : syracuseStep 238223 = 357335) B357335
theorem B238265 : Blo 155795 238265 := bstep (se 2 (by rfl) ⟨89349, by rfl⟩ : syracuseStep 238265 = 178699) B178699
theorem B533249 : Blo 155795 533249 := bstep (se 2 (by rfl) ⟨199968, by rfl⟩ : syracuseStep 533249 = 399937) B399937
theorem B238343 : Blo 155795 238343 := bstep (se 1 (by rfl) ⟨178757, by rfl⟩ : syracuseStep 238343 = 357515) B357515
theorem B238379 : Blo 155795 238379 := bstep (se 1 (by rfl) ⟨178784, by rfl⟩ : syracuseStep 238379 = 357569) B357569
theorem B238409 : Blo 155795 238409 := bstep (se 2 (by rfl) ⟨89403, by rfl⟩ : syracuseStep 238409 = 178807) B178807
theorem B238523 : Blo 155795 238523 := bstep (se 1 (by rfl) ⟨178892, by rfl⟩ : syracuseStep 238523 = 357785) B357785
theorem B238583 : Blo 155795 238583 := bstep (se 1 (by rfl) ⟨178937, by rfl⟩ : syracuseStep 238583 = 357875) B357875
theorem B238607 : Blo 155795 238607 := bstep (se 1 (by rfl) ⟨178955, by rfl⟩ : syracuseStep 238607 = 357911) B357911
theorem B238649 : Blo 155795 238649 := bstep (se 2 (by rfl) ⟨89493, by rfl⟩ : syracuseStep 238649 = 178987) B178987
theorem B238727 : Blo 155795 238727 := bstep (se 1 (by rfl) ⟨179045, by rfl⟩ : syracuseStep 238727 = 358091) B358091
theorem B238763 : Blo 155795 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B238793 : Blo 155795 238793 := bstep (se 2 (by rfl) ⟨89547, by rfl⟩ : syracuseStep 238793 = 179095) B179095
theorem B795905 : Blo 155795 795905 := bstep (se 2 (by rfl) ⟨298464, by rfl⟩ : syracuseStep 795905 = 596929) B596929
theorem B238907 : Blo 155795 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B402803 : Blo 155795 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B238967 : Blo 155795 238967 := bstep (se 1 (by rfl) ⟨179225, by rfl⟩ : syracuseStep 238967 = 358451) B358451
theorem B238991 : Blo 155795 238991 := bstep (se 1 (by rfl) ⟨179243, by rfl⟩ : syracuseStep 238991 = 358487) B358487
theorem B239033 : Blo 155795 239033 := bstep (se 2 (by rfl) ⟨89637, by rfl⟩ : syracuseStep 239033 = 179275) B179275
theorem B239111 : Blo 155795 239111 := bstep (se 1 (by rfl) ⟨179333, by rfl⟩ : syracuseStep 239111 = 358667) B358667
theorem B534059 : Blo 155795 534059 := bstep (se 1 (by rfl) ⟨400544, by rfl⟩ : syracuseStep 534059 = 801089) B801089
theorem B239147 : Blo 155795 239147 := bstep (se 1 (by rfl) ⟨179360, by rfl⟩ : syracuseStep 239147 = 358721) B358721
theorem B239177 : Blo 155795 239177 := bstep (se 2 (by rfl) ⟨89691, by rfl⟩ : syracuseStep 239177 = 179383) B179383
theorem B239291 : Blo 155795 239291 := bstep (se 1 (by rfl) ⟨179468, by rfl⟩ : syracuseStep 239291 = 358937) B358937
theorem B894665 : Blo 155795 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B239351 : Blo 155795 239351 := bstep (se 1 (by rfl) ⟨179513, by rfl⟩ : syracuseStep 239351 = 359027) B359027
theorem B337679 : Blo 155795 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B239375 : Blo 155795 239375 := bstep (se 1 (by rfl) ⟨179531, by rfl⟩ : syracuseStep 239375 = 359063) B359063
theorem B239417 : Blo 155795 239417 := bstep (se 2 (by rfl) ⟨89781, by rfl⟩ : syracuseStep 239417 = 179563) B179563
theorem B403319 : Blo 155795 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B239495 : Blo 155795 239495 := bstep (se 1 (by rfl) ⟨179621, by rfl⟩ : syracuseStep 239495 = 359243) B359243
theorem B239531 : Blo 155795 239531 := bstep (se 1 (by rfl) ⟨179648, by rfl⟩ : syracuseStep 239531 = 359297) B359297
theorem B11610053 : Blo 155795 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B239561 : Blo 155795 239561 := bstep (se 2 (by rfl) ⟨89835, by rfl⟩ : syracuseStep 239561 = 179671) B179671
theorem B796715 : Blo 155795 796715 := bstep (se 1 (by rfl) ⟨597536, by rfl⟩ : syracuseStep 796715 = 1195073) B1195073
theorem B239675 : Blo 155795 239675 := bstep (se 1 (by rfl) ⟨179756, by rfl⟩ : syracuseStep 239675 = 359513) B359513
theorem B600605 : Blo 155795 600605 := bstep (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) B225227
theorem B961085 : Blo 155795 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B535355 : Blo 155795 535355 := bstep (se 1 (by rfl) ⟨401516, by rfl⟩ : syracuseStep 535355 = 803033) B803033
theorem B404311 : Blo 155795 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B765101 : Blo 155795 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B601289 : Blo 155795 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B535841 : Blo 155795 535841 := bstep (se 2 (by rfl) ⟨200940, by rfl⟩ : syracuseStep 535841 = 401881) B401881
theorem B798011 : Blo 155795 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B339319 : Blo 155795 339319 := bstep (se 1 (by rfl) ⟨254489, by rfl⟩ : syracuseStep 339319 = 508979) B508979
theorem B175495 : Blo 155795 175495 := bstep (se 1 (by rfl) ⟨131621, by rfl⟩ : syracuseStep 175495 = 263243) B263243
theorem B568723 : Blo 155795 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B798173 : Blo 155795 798173 := bstep (se 3 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 798173 = 299315) B299315
theorem B863747 : Blo 155795 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B175675 : Blo 155795 175675 := bstep (se 1 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 175675 = 263513) B263513
theorem B896579 : Blo 155795 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B798497 : Blo 155795 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B536435 : Blo 155795 536435 := bstep (se 1 (by rfl) ⟨402326, by rfl⟩ : syracuseStep 536435 = 804653) B804653
theorem B176143 : Blo 155795 176143 := bstep (se 1 (by rfl) ⟨132107, by rfl⟩ : syracuseStep 176143 = 264215) B264215
theorem B1716461 : Blo 155795 1716461 := bstep (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) B643673
theorem B405847 : Blo 155795 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B176647 : Blo 155795 176647 := bstep (se 1 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 176647 = 264971) B264971
theorem B176827 : Blo 155795 176827 := bstep (se 1 (by rfl) ⟨132620, by rfl⟩ : syracuseStep 176827 = 265241) B265241
theorem B799469 : Blo 155795 799469 := bstep (se 3 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 799469 = 299801) B299801
theorem B603065 : Blo 155795 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B963613 : Blo 155795 963613 := bstep (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) B361355
theorem B177295 : Blo 155795 177295 := bstep (se 1 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 177295 = 265943) B265943
theorem B767177 : Blo 155795 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B1783133 : Blo 155795 1783133 := bstep (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) B668675
theorem B3225091 : Blo 155795 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B800279 : Blo 155795 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B177799 : Blo 155795 177799 := bstep (se 1 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 177799 = 266699) B266699
theorem B3323693 : Blo 155795 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B177979 : Blo 155795 177979 := bstep (se 1 (by rfl) ⟨133484, by rfl⟩ : syracuseStep 177979 = 266969) B266969
theorem B374843 : Blo 155795 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B1620101 : Blo 155795 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B374969 : Blo 155795 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B178447 : Blo 155795 178447 := bstep (se 1 (by rfl) ⟨133835, by rfl⟩ : syracuseStep 178447 = 267671) B267671
theorem B539027 : Blo 155795 539027 := bstep (se 1 (by rfl) ⟨404270, by rfl⟩ : syracuseStep 539027 = 808541) B808541
theorem B768685 : Blo 155795 768685 := bstep (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) B288257
theorem B178951 : Blo 155795 178951 := bstep (se 1 (by rfl) ⟨134213, by rfl⟩ : syracuseStep 178951 = 268427) B268427
theorem B1784591 : Blo 155795 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B179131 : Blo 155795 179131 := bstep (se 1 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 179131 = 268697) B268697
theorem B408847 : Blo 155795 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B179599 : Blo 155795 179599 := bstep (se 1 (by rfl) ⟨134699, by rfl⟩ : syracuseStep 179599 = 269399) B269399
theorem B900497 : Blo 155795 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B802333 : Blo 155795 802333 := bstep (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) B300875
theorem B802541 : Blo 155795 802541 := bstep (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) B300953
theorem B179975 : Blo 155795 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B1261363 : Blo 155795 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B900953 : Blo 155795 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B180103 : Blo 155795 180103 := bstep (se 1 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 180103 = 270155) B270155
theorem B638873 : Blo 155795 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B377207 : Blo 155795 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B606649 : Blo 155795 606649 := bstep (se 2 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 606649 = 454987) B454987
theorem B508427 : Blo 155795 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B803357 : Blo 155795 803357 := bstep (se 3 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 803357 = 301259) B301259
theorem B672299 : Blo 155795 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B213563 : Blo 155795 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B3261221 : Blo 155795 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B803843 : Blo 155795 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B640237 : Blo 155795 640237 := bstep (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) B240089
theorem B574721 : Blo 155795 574721 := bstep (se 2 (by rfl) ⟨215520, by rfl⟩ : syracuseStep 574721 = 431041) B431041
theorem B443677 : Blo 155795 443677 := bstep (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) B166379
theorem B738827 : Blo 155795 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B378553 : Blo 155795 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B575549 : Blo 155795 575549 := bstep (se 3 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 575549 = 215831) B215831
theorem B1427543 : Blo 155795 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B510209 : Blo 155795 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B608647 : Blo 155795 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B674315 : Blo 155795 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B805463 : Blo 155795 805463 := bstep (se 1 (by rfl) ⟨604097, by rfl⟩ : syracuseStep 805463 = 1208195) B1208195
theorem B281377 : Blo 155795 281377 := bstep (se 2 (by rfl) ⟨105516, by rfl⟩ : syracuseStep 281377 = 211033) B211033
theorem B674675 : Blo 155795 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B904121 : Blo 155795 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B805949 : Blo 155795 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B445625 : Blo 155795 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B904385 : Blo 155795 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B1691201 : Blo 155795 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B1134157 : Blo 155795 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B1199809 : Blo 155795 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B380705 : Blo 155795 380705 := bstep (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) B285529
theorem B610163 : Blo 155795 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B1200025 : Blo 155795 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B1364141 : Blo 155795 1364141 := bstep (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) B511553
theorem B446867 : Blo 155795 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B807731 : Blo 155795 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B808055 : Blo 155795 808055 := bstep (se 1 (by rfl) ⟨606041, by rfl⟩ : syracuseStep 808055 = 1212083) B1212083
theorem B906511 : Blo 155795 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B382475 : Blo 155795 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B1955393 : Blo 155795 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B448267 : Blo 155795 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B1464227 : Blo 155795 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B448541 : Blo 155795 448541 := bstep (se 3 (by rfl) ⟨84101, by rfl⟩ : syracuseStep 448541 = 168203) B168203
theorem B1005655 : Blo 155795 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B13031725 : Blo 155795 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B514451 : Blo 155795 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B907787 : Blo 155795 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B481879 : Blo 155795 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B350855 : Blo 155795 350855 := bstep (se 1 (by rfl) ⟨263141, by rfl⟩ : syracuseStep 350855 = 526283) B526283
theorem B907969 : Blo 155795 907969 := bstep (se 2 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 907969 = 680977) B680977
theorem B285385 : Blo 155795 285385 := bstep (se 2 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 285385 = 214039) B214039
theorem B678689 : Blo 155795 678689 := bstep (se 2 (by rfl) ⟨254508, by rfl⟩ : syracuseStep 678689 = 509017) B509017
theorem B252715 : Blo 155795 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B351035 : Blo 155795 351035 := bstep (se 1 (by rfl) ⟨263276, by rfl⟩ : syracuseStep 351035 = 526553) B526553
theorem B908167 : Blo 155795 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B2579363 : Blo 155795 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B351161 : Blo 155795 351161 := bstep (se 2 (by rfl) ⟨131685, by rfl⟩ : syracuseStep 351161 = 263371) B263371
theorem B252971 : Blo 155795 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B351503 : Blo 155795 351503 := bstep (se 1 (by rfl) ⟨263627, by rfl⟩ : syracuseStep 351503 = 527255) B527255
theorem B351521 : Blo 155795 351521 := bstep (se 2 (by rfl) ⟨131820, by rfl⟩ : syracuseStep 351521 = 263641) B263641
theorem B7232813 : Blo 155795 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B1793339 : Blo 155795 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B351863 : Blo 155795 351863 := bstep (se 1 (by rfl) ⟨263897, by rfl⟩ : syracuseStep 351863 = 527795) B527795
theorem B188023 : Blo 155795 188023 := bstep (se 1 (by rfl) ⟨141017, by rfl⟩ : syracuseStep 188023 = 282035) B282035
theorem B2612915 : Blo 155795 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B483017 : Blo 155795 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B352043 : Blo 155795 352043 := bstep (se 1 (by rfl) ⟨264032, by rfl⟩ : syracuseStep 352043 = 528065) B528065
theorem B188407 : Blo 155795 188407 := bstep (se 1 (by rfl) ⟨141305, by rfl⟩ : syracuseStep 188407 = 282611) B282611
theorem B11952197 : Blo 155795 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B352403 : Blo 155795 352403 := bstep (se 1 (by rfl) ⟨264302, by rfl⟩ : syracuseStep 352403 = 528605) B528605
theorem B155835 : Blo 155795 155835 := bstep (se 1 (by rfl) ⟨116876, by rfl⟩ : syracuseStep 155835 = 233753) B233753
theorem B352457 : Blo 155795 352457 := bstep (se 2 (by rfl) ⟨132171, by rfl⟩ : syracuseStep 352457 = 264343) B264343
theorem B155911 : Blo 155795 155911 := bstep (se 1 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 155911 = 233867) B233867
theorem B155919 : Blo 155795 155919 := bstep (se 1 (by rfl) ⟨116939, by rfl⟩ : syracuseStep 155919 = 233879) B233879
theorem B155963 : Blo 155795 155963 := bstep (se 1 (by rfl) ⟨116972, by rfl⟩ : syracuseStep 155963 = 233945) B233945
theorem B844091 : Blo 155795 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B156039 : Blo 155795 156039 := bstep (se 1 (by rfl) ⟨117029, by rfl⟩ : syracuseStep 156039 = 234059) B234059
theorem B156047 : Blo 155795 156047 := bstep (se 1 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 156047 = 234071) B234071
theorem B188815 : Blo 155795 188815 := bstep (se 1 (by rfl) ⟨141611, by rfl⟩ : syracuseStep 188815 = 283223) B283223
theorem B451001 : Blo 155795 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B156091 : Blo 155795 156091 := bstep (se 1 (by rfl) ⟨117068, by rfl⟩ : syracuseStep 156091 = 234137) B234137
theorem B156167 : Blo 155795 156167 := bstep (se 1 (by rfl) ⟨117125, by rfl⟩ : syracuseStep 156167 = 234251) B234251
theorem B156175 : Blo 155795 156175 := bstep (se 1 (by rfl) ⟨117131, by rfl⟩ : syracuseStep 156175 = 234263) B234263
theorem B451115 : Blo 155795 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B156219 : Blo 155795 156219 := bstep (se 1 (by rfl) ⟨117164, by rfl⟩ : syracuseStep 156219 = 234329) B234329
theorem B1368695 : Blo 155795 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B156295 : Blo 155795 156295 := bstep (se 1 (by rfl) ⟨117221, by rfl⟩ : syracuseStep 156295 = 234443) B234443
theorem B156303 : Blo 155795 156303 := bstep (se 1 (by rfl) ⟨117227, by rfl⟩ : syracuseStep 156303 = 234455) B234455
theorem B156347 : Blo 155795 156347 := bstep (se 1 (by rfl) ⟨117260, by rfl⟩ : syracuseStep 156347 = 234521) B234521
theorem B156423 : Blo 155795 156423 := bstep (se 1 (by rfl) ⟨117317, by rfl⟩ : syracuseStep 156423 = 234635) B234635
theorem B156431 : Blo 155795 156431 := bstep (se 1 (by rfl) ⟨117323, by rfl⟩ : syracuseStep 156431 = 234647) B234647
theorem B156475 : Blo 155795 156475 := bstep (se 1 (by rfl) ⟨117356, by rfl⟩ : syracuseStep 156475 = 234713) B234713
theorem B156551 : Blo 155795 156551 := bstep (se 1 (by rfl) ⟨117413, by rfl⟩ : syracuseStep 156551 = 234827) B234827
theorem B353159 : Blo 155795 353159 := bstep (se 1 (by rfl) ⟨264869, by rfl⟩ : syracuseStep 353159 = 529739) B529739
theorem B156559 : Blo 155795 156559 := bstep (se 1 (by rfl) ⟨117419, by rfl⟩ : syracuseStep 156559 = 234839) B234839
theorem B156603 : Blo 155795 156603 := bstep (se 1 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 156603 = 234905) B234905
theorem B156679 : Blo 155795 156679 := bstep (se 1 (by rfl) ⟨117509, by rfl⟩ : syracuseStep 156679 = 235019) B235019
theorem B156687 : Blo 155795 156687 := bstep (se 1 (by rfl) ⟨117515, by rfl⟩ : syracuseStep 156687 = 235031) B235031
theorem B156731 : Blo 155795 156731 := bstep (se 1 (by rfl) ⟨117548, by rfl⟩ : syracuseStep 156731 = 235097) B235097
theorem B353339 : Blo 155795 353339 := bstep (se 1 (by rfl) ⟨265004, by rfl⟩ : syracuseStep 353339 = 530009) B530009
theorem B681047 : Blo 155795 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B156807 : Blo 155795 156807 := bstep (se 1 (by rfl) ⟨117605, by rfl⟩ : syracuseStep 156807 = 235211) B235211
theorem B156815 : Blo 155795 156815 := bstep (se 1 (by rfl) ⟨117611, by rfl⟩ : syracuseStep 156815 = 235223) B235223
theorem B353465 : Blo 155795 353465 := bstep (se 2 (by rfl) ⟨132549, by rfl⟩ : syracuseStep 353465 = 265099) B265099
theorem B156859 : Blo 155795 156859 := bstep (se 1 (by rfl) ⟨117644, by rfl⟩ : syracuseStep 156859 = 235289) B235289
theorem B156935 : Blo 155795 156935 := bstep (se 1 (by rfl) ⟨117701, by rfl⟩ : syracuseStep 156935 = 235403) B235403
theorem B156943 : Blo 155795 156943 := bstep (se 1 (by rfl) ⟨117707, by rfl⟩ : syracuseStep 156943 = 235415) B235415
theorem B156987 : Blo 155795 156987 := bstep (se 1 (by rfl) ⟨117740, by rfl⟩ : syracuseStep 156987 = 235481) B235481
theorem B157063 : Blo 155795 157063 := bstep (se 1 (by rfl) ⟨117797, by rfl⟩ : syracuseStep 157063 = 235595) B235595
theorem B157071 : Blo 155795 157071 := bstep (se 1 (by rfl) ⟨117803, by rfl⟩ : syracuseStep 157071 = 235607) B235607
theorem B157115 : Blo 155795 157115 := bstep (se 1 (by rfl) ⟨117836, by rfl⟩ : syracuseStep 157115 = 235673) B235673
theorem B157191 : Blo 155795 157191 := bstep (se 1 (by rfl) ⟨117893, by rfl⟩ : syracuseStep 157191 = 235787) B235787
theorem B157199 : Blo 155795 157199 := bstep (se 1 (by rfl) ⟨117899, by rfl⟩ : syracuseStep 157199 = 235799) B235799
theorem B353807 : Blo 155795 353807 := bstep (se 1 (by rfl) ⟨265355, by rfl⟩ : syracuseStep 353807 = 530711) B530711
theorem B353825 : Blo 155795 353825 := bstep (se 2 (by rfl) ⟨132684, by rfl⟩ : syracuseStep 353825 = 265369) B265369
theorem B157243 : Blo 155795 157243 := bstep (se 1 (by rfl) ⟨117932, by rfl⟩ : syracuseStep 157243 = 235865) B235865
theorem B157319 : Blo 155795 157319 := bstep (se 1 (by rfl) ⟨117989, by rfl⟩ : syracuseStep 157319 = 235979) B235979
theorem B157327 : Blo 155795 157327 := bstep (se 1 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 157327 = 235991) B235991
theorem B452243 : Blo 155795 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B157371 : Blo 155795 157371 := bstep (se 1 (by rfl) ⟨118028, by rfl⟩ : syracuseStep 157371 = 236057) B236057
theorem B190199 : Blo 155795 190199 := bstep (se 1 (by rfl) ⟨142649, by rfl⟩ : syracuseStep 190199 = 285299) B285299
theorem B157447 : Blo 155795 157447 := bstep (se 1 (by rfl) ⟨118085, by rfl⟩ : syracuseStep 157447 = 236171) B236171
theorem B157455 : Blo 155795 157455 := bstep (se 1 (by rfl) ⟨118091, by rfl⟩ : syracuseStep 157455 = 236183) B236183
theorem B157499 : Blo 155795 157499 := bstep (se 1 (by rfl) ⟨118124, by rfl⟩ : syracuseStep 157499 = 236249) B236249
theorem B354167 : Blo 155795 354167 := bstep (se 1 (by rfl) ⟨265625, by rfl⟩ : syracuseStep 354167 = 531251) B531251
theorem B157575 : Blo 155795 157575 := bstep (se 1 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 157575 = 236363) B236363
theorem B157583 : Blo 155795 157583 := bstep (se 1 (by rfl) ⟨118187, by rfl⟩ : syracuseStep 157583 = 236375) B236375
theorem B157627 : Blo 155795 157627 := bstep (se 1 (by rfl) ⟨118220, by rfl⟩ : syracuseStep 157627 = 236441) B236441
theorem B223177 : Blo 155795 223177 := bstep (se 2 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 223177 = 167383) B167383
theorem B157703 : Blo 155795 157703 := bstep (se 1 (by rfl) ⟨118277, by rfl⟩ : syracuseStep 157703 = 236555) B236555
theorem B157711 : Blo 155795 157711 := bstep (se 1 (by rfl) ⟨118283, by rfl⟩ : syracuseStep 157711 = 236567) B236567
theorem B452641 : Blo 155795 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B354347 : Blo 155795 354347 := bstep (se 1 (by rfl) ⟨265760, by rfl⟩ : syracuseStep 354347 = 531521) B531521
theorem B190507 : Blo 155795 190507 := bstep (se 1 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 190507 = 285761) B285761
theorem B157755 : Blo 155795 157755 := bstep (se 1 (by rfl) ⟨118316, by rfl⟩ : syracuseStep 157755 = 236633) B236633
theorem B157831 : Blo 155795 157831 := bstep (se 1 (by rfl) ⟨118373, by rfl⟩ : syracuseStep 157831 = 236747) B236747
theorem B157839 : Blo 155795 157839 := bstep (se 1 (by rfl) ⟨118379, by rfl⟩ : syracuseStep 157839 = 236759) B236759
theorem B157883 : Blo 155795 157883 := bstep (se 1 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 157883 = 236825) B236825
theorem B157959 : Blo 155795 157959 := bstep (se 1 (by rfl) ⟨118469, by rfl⟩ : syracuseStep 157959 = 236939) B236939
theorem B157967 : Blo 155795 157967 := bstep (se 1 (by rfl) ⟨118475, by rfl⟩ : syracuseStep 157967 = 236951) B236951
theorem B158011 : Blo 155795 158011 := bstep (se 1 (by rfl) ⟨118508, by rfl⟩ : syracuseStep 158011 = 237017) B237017
theorem B158087 : Blo 155795 158087 := bstep (se 1 (by rfl) ⟨118565, by rfl⟩ : syracuseStep 158087 = 237131) B237131
theorem B158095 : Blo 155795 158095 := bstep (se 1 (by rfl) ⟨118571, by rfl⟩ : syracuseStep 158095 = 237143) B237143
theorem B354707 : Blo 155795 354707 := bstep (se 1 (by rfl) ⟨266030, by rfl⟩ : syracuseStep 354707 = 532061) B532061
theorem B158139 : Blo 155795 158139 := bstep (se 1 (by rfl) ⟨118604, by rfl⟩ : syracuseStep 158139 = 237209) B237209
theorem B354761 : Blo 155795 354761 := bstep (se 2 (by rfl) ⟨133035, by rfl⟩ : syracuseStep 354761 = 266071) B266071
theorem B1206737 : Blo 155795 1206737 := bstep (se 2 (by rfl) ⟨452526, by rfl⟩ : syracuseStep 1206737 = 905053) B905053
theorem B3369437 : Blo 155795 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B3434993 : Blo 155795 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B223735 : Blo 155795 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B158215 : Blo 155795 158215 := bstep (se 1 (by rfl) ⟨118661, by rfl⟩ : syracuseStep 158215 = 237323) B237323
theorem B158223 : Blo 155795 158223 := bstep (se 1 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 158223 = 237335) B237335
theorem B158267 : Blo 155795 158267 := bstep (se 1 (by rfl) ⟨118700, by rfl⟩ : syracuseStep 158267 = 237401) B237401
theorem B158343 : Blo 155795 158343 := bstep (se 1 (by rfl) ⟨118757, by rfl⟩ : syracuseStep 158343 = 237515) B237515
theorem B158351 : Blo 155795 158351 := bstep (se 1 (by rfl) ⟨118763, by rfl⟩ : syracuseStep 158351 = 237527) B237527
theorem B158395 : Blo 155795 158395 := bstep (se 1 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 158395 = 237593) B237593
theorem B6810317 : Blo 155795 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B158471 : Blo 155795 158471 := bstep (se 1 (by rfl) ⟨118853, by rfl⟩ : syracuseStep 158471 = 237707) B237707
theorem B158479 : Blo 155795 158479 := bstep (se 1 (by rfl) ⟨118859, by rfl⟩ : syracuseStep 158479 = 237719) B237719
theorem B158523 : Blo 155795 158523 := bstep (se 1 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 158523 = 237785) B237785
theorem B158599 : Blo 155795 158599 := bstep (se 1 (by rfl) ⟨118949, by rfl⟩ : syracuseStep 158599 = 237899) B237899
theorem B158607 : Blo 155795 158607 := bstep (se 1 (by rfl) ⟨118955, by rfl⟩ : syracuseStep 158607 = 237911) B237911
theorem B453529 : Blo 155795 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B158651 : Blo 155795 158651 := bstep (se 1 (by rfl) ⟨118988, by rfl⟩ : syracuseStep 158651 = 237977) B237977
theorem B158727 : Blo 155795 158727 := bstep (se 1 (by rfl) ⟨119045, by rfl⟩ : syracuseStep 158727 = 238091) B238091
theorem B158735 : Blo 155795 158735 := bstep (se 1 (by rfl) ⟨119051, by rfl⟩ : syracuseStep 158735 = 238103) B238103
theorem B224299 : Blo 155795 224299 := bstep (se 1 (by rfl) ⟨168224, by rfl⟩ : syracuseStep 224299 = 336449) B336449
theorem B158779 : Blo 155795 158779 := bstep (se 1 (by rfl) ⟨119084, by rfl⟩ : syracuseStep 158779 = 238169) B238169
theorem B355463 : Blo 155795 355463 := bstep (se 1 (by rfl) ⟨266597, by rfl⟩ : syracuseStep 355463 = 533195) B533195
theorem B158855 : Blo 155795 158855 := bstep (se 1 (by rfl) ⟨119141, by rfl⟩ : syracuseStep 158855 = 238283) B238283
theorem B158863 : Blo 155795 158863 := bstep (se 1 (by rfl) ⟨119147, by rfl⟩ : syracuseStep 158863 = 238295) B238295
theorem B158907 : Blo 155795 158907 := bstep (se 1 (by rfl) ⟨119180, by rfl⟩ : syracuseStep 158907 = 238361) B238361
theorem B158983 : Blo 155795 158983 := bstep (se 1 (by rfl) ⟨119237, by rfl⟩ : syracuseStep 158983 = 238475) B238475
theorem B224527 : Blo 155795 224527 := bstep (se 1 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 224527 = 336791) B336791
theorem B158991 : Blo 155795 158991 := bstep (se 1 (by rfl) ⟨119243, by rfl⟩ : syracuseStep 158991 = 238487) B238487
theorem B453917 : Blo 155795 453917 := bstep (se 3 (by rfl) ⟨85109, by rfl⟩ : syracuseStep 453917 = 170219) B170219
theorem B355643 : Blo 155795 355643 := bstep (se 1 (by rfl) ⟨266732, by rfl⟩ : syracuseStep 355643 = 533465) B533465
theorem B159035 : Blo 155795 159035 := bstep (se 1 (by rfl) ⟨119276, by rfl⟩ : syracuseStep 159035 = 238553) B238553
theorem B159111 : Blo 155795 159111 := bstep (se 1 (by rfl) ⟨119333, by rfl⟩ : syracuseStep 159111 = 238667) B238667
theorem B159119 : Blo 155795 159119 := bstep (se 1 (by rfl) ⟨119339, by rfl⟩ : syracuseStep 159119 = 238679) B238679
theorem B355769 : Blo 155795 355769 := bstep (se 2 (by rfl) ⟨133413, by rfl⟩ : syracuseStep 355769 = 266827) B266827
theorem B159163 : Blo 155795 159163 := bstep (se 1 (by rfl) ⟨119372, by rfl⟩ : syracuseStep 159163 = 238745) B238745
theorem B159239 : Blo 155795 159239 := bstep (se 1 (by rfl) ⟨119429, by rfl⟩ : syracuseStep 159239 = 238859) B238859
theorem B159247 : Blo 155795 159247 := bstep (se 1 (by rfl) ⟨119435, by rfl⟩ : syracuseStep 159247 = 238871) B238871
theorem B159291 : Blo 155795 159291 := bstep (se 1 (by rfl) ⟨119468, by rfl⟩ : syracuseStep 159291 = 238937) B238937
theorem B58453589 : Blo 155795 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B159367 : Blo 155795 159367 := bstep (se 1 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 159367 = 239051) B239051
theorem B159375 : Blo 155795 159375 := bstep (se 1 (by rfl) ⟨119531, by rfl⟩ : syracuseStep 159375 = 239063) B239063
theorem B913069 : Blo 155795 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B1699505 : Blo 155795 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B159419 : Blo 155795 159419 := bstep (se 1 (by rfl) ⟨119564, by rfl⟩ : syracuseStep 159419 = 239129) B239129
theorem B159495 : Blo 155795 159495 := bstep (se 1 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 159495 = 239243) B239243
theorem B356111 : Blo 155795 356111 := bstep (se 1 (by rfl) ⟨267083, by rfl⟩ : syracuseStep 356111 = 534167) B534167
theorem B159503 : Blo 155795 159503 := bstep (se 1 (by rfl) ⟨119627, by rfl⟩ : syracuseStep 159503 = 239255) B239255
theorem B356129 : Blo 155795 356129 := bstep (se 2 (by rfl) ⟨133548, by rfl⟩ : syracuseStep 356129 = 267097) B267097
theorem B159547 : Blo 155795 159547 := bstep (se 1 (by rfl) ⟨119660, by rfl⟩ : syracuseStep 159547 = 239321) B239321
theorem B2420549 : Blo 155795 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B159623 : Blo 155795 159623 := bstep (se 1 (by rfl) ⟨119717, by rfl⟩ : syracuseStep 159623 = 239435) B239435
theorem B159631 : Blo 155795 159631 := bstep (se 1 (by rfl) ⟨119723, by rfl⟩ : syracuseStep 159631 = 239447) B239447
theorem B159675 : Blo 155795 159675 := bstep (se 1 (by rfl) ⟨119756, by rfl⟩ : syracuseStep 159675 = 239513) B239513
theorem B749533 : Blo 155795 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B159751 : Blo 155795 159751 := bstep (se 1 (by rfl) ⟨119813, by rfl⟩ : syracuseStep 159751 = 239627) B239627
theorem B159759 : Blo 155795 159759 := bstep (se 1 (by rfl) ⟨119819, by rfl⟩ : syracuseStep 159759 = 239639) B239639
theorem B356471 : Blo 155795 356471 := bstep (se 1 (by rfl) ⟨267353, by rfl⟩ : syracuseStep 356471 = 534707) B534707
theorem B422023 : Blo 155795 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B356651 : Blo 155795 356651 := bstep (se 1 (by rfl) ⟨267488, by rfl⟩ : syracuseStep 356651 = 534977) B534977
theorem B225671 : Blo 155795 225671 := bstep (se 1 (by rfl) ⟨169253, by rfl⟩ : syracuseStep 225671 = 338507) B338507
theorem B487951 : Blo 155795 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B258619 : Blo 155795 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B225865 : Blo 155795 225865 := bstep (se 2 (by rfl) ⟨84699, by rfl⟩ : syracuseStep 225865 = 169399) B169399
theorem B357011 : Blo 155795 357011 := bstep (se 1 (by rfl) ⟨267758, by rfl⟩ : syracuseStep 357011 = 535517) B535517
theorem B357065 : Blo 155795 357065 := bstep (se 2 (by rfl) ⟨133899, by rfl⟩ : syracuseStep 357065 = 267799) B267799
theorem B160655 : Blo 155795 160655 := bstep (se 1 (by rfl) ⟨120491, by rfl⟩ : syracuseStep 160655 = 240983) B240983
theorem B160699 : Blo 155795 160699 := bstep (se 1 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 160699 = 241049) B241049
theorem B619607 : Blo 155795 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B226423 : Blo 155795 226423 := bstep (se 1 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 226423 = 339635) B339635
theorem B1209659 : Blo 155795 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B357767 : Blo 155795 357767 := bstep (se 1 (by rfl) ⟨268325, by rfl⟩ : syracuseStep 357767 = 536651) B536651
theorem B357947 : Blo 155795 357947 := bstep (se 1 (by rfl) ⟨268460, by rfl⟩ : syracuseStep 357947 = 536921) B536921
theorem B358073 : Blo 155795 358073 := bstep (se 2 (by rfl) ⟨134277, by rfl⟩ : syracuseStep 358073 = 268555) B268555
theorem B587521 : Blo 155795 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B718625 : Blo 155795 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B1996595 : Blo 155795 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B227129 : Blo 155795 227129 := bstep (se 2 (by rfl) ⟨85173, by rfl⟩ : syracuseStep 227129 = 170347) B170347
theorem B227215 : Blo 155795 227215 := bstep (se 1 (by rfl) ⟨170411, by rfl⟩ : syracuseStep 227215 = 340823) B340823
theorem B227243 : Blo 155795 227243 := bstep (se 1 (by rfl) ⟨170432, by rfl⟩ : syracuseStep 227243 = 340865) B340865
theorem B358415 : Blo 155795 358415 := bstep (se 1 (by rfl) ⟨268811, by rfl⟩ : syracuseStep 358415 = 537623) B537623
theorem B358433 : Blo 155795 358433 := bstep (se 2 (by rfl) ⟨134412, by rfl⟩ : syracuseStep 358433 = 268825) B268825
theorem B358775 : Blo 155795 358775 := bstep (se 1 (by rfl) ⟨269081, by rfl⟩ : syracuseStep 358775 = 538163) B538163
theorem B358955 : Blo 155795 358955 := bstep (se 1 (by rfl) ⟨269216, by rfl⟩ : syracuseStep 358955 = 538433) B538433
theorem B359315 : Blo 155795 359315 := bstep (se 1 (by rfl) ⟨269486, by rfl⟩ : syracuseStep 359315 = 538973) B538973
theorem B359369 : Blo 155795 359369 := bstep (se 2 (by rfl) ⟨134763, by rfl⟩ : syracuseStep 359369 = 269527) B269527
theorem B1441955 : Blo 155795 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B492551 : Blo 155795 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B263567 : Blo 155795 263567 := bstep (se 1 (by rfl) ⟨197675, by rfl⟩ : syracuseStep 263567 = 395351) B395351
theorem B951695 : Blo 155795 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B4326857 : Blo 155795 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B3606059 : Blo 155795 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B263803 : Blo 155795 263803 := bstep (se 1 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 263803 = 395705) B395705
theorem B525959 : Blo 155795 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B853649 : Blo 155795 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B526013 : Blo 155795 526013 := bstep (se 3 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 526013 = 197255) B197255
theorem B591569 : Blo 155795 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B526175 : Blo 155795 526175 := bstep (se 1 (by rfl) ⟨394631, by rfl⟩ : syracuseStep 526175 = 789263) B789263
theorem B526337 : Blo 155795 526337 := bstep (se 2 (by rfl) ⟨197376, by rfl⟩ : syracuseStep 526337 = 394753) B394753
theorem B591887 : Blo 155795 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B297083 : Blo 155795 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B428413 : Blo 155795 428413 := bstep (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) B160655
theorem B264667 : Blo 155795 264667 := bstep (se 1 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 264667 = 397001) B397001
theorem B297569 : Blo 155795 297569 := bstep (se 2 (by rfl) ⟨111588, by rfl⟩ : syracuseStep 297569 = 223177) B223177
theorem B527147 : Blo 155795 527147 := bstep (se 1 (by rfl) ⟨395360, by rfl⟩ : syracuseStep 527147 = 790721) B790721
theorem B297911 : Blo 155795 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B527417 : Blo 155795 527417 := bstep (se 2 (by rfl) ⟨197781, by rfl⟩ : syracuseStep 527417 = 395563) B395563
theorem B265295 : Blo 155795 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B396535 : Blo 155795 396535 := bstep (se 1 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 396535 = 594803) B594803
theorem B298313 : Blo 155795 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B527741 : Blo 155795 527741 := bstep (se 3 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 527741 = 197903) B197903
theorem B396809 : Blo 155795 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B396839 : Blo 155795 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B528011 : Blo 155795 528011 := bstep (se 1 (by rfl) ⟨396008, by rfl⟩ : syracuseStep 528011 = 792017) B792017
theorem B397163 : Blo 155795 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B266159 : Blo 155795 266159 := bstep (se 1 (by rfl) ⟨199619, by rfl⟩ : syracuseStep 266159 = 399239) B399239
theorem B299027 : Blo 155795 299027 := bstep (se 1 (by rfl) ⟨224270, by rfl⟩ : syracuseStep 299027 = 448541) B448541
theorem B2101277 : Blo 155795 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B299065 : Blo 155795 299065 := bstep (se 2 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 299065 = 224299) B224299
theorem B593999 : Blo 155795 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B3281075 : Blo 155795 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B266591 : Blo 155795 266591 := bstep (se 1 (by rfl) ⟨199943, by rfl⟩ : syracuseStep 266591 = 399887) B399887
theorem B299369 : Blo 155795 299369 := bstep (se 2 (by rfl) ⟨112263, by rfl⟩ : syracuseStep 299369 = 224527) B224527
theorem B233903 : Blo 155795 233903 := bstep (se 1 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 233903 = 350855) B350855
theorem B201143 : Blo 155795 201143 := bstep (se 1 (by rfl) ⟨150857, by rfl⟩ : syracuseStep 201143 = 301715) B301715
theorem B397811 : Blo 155795 397811 := bstep (se 1 (by rfl) ⟨298358, by rfl⟩ : syracuseStep 397811 = 596717) B596717
theorem B233993 : Blo 155795 233993 := bstep (se 2 (by rfl) ⟨87747, by rfl⟩ : syracuseStep 233993 = 175495) B175495
theorem B758297 : Blo 155795 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B528929 : Blo 155795 528929 := bstep (se 2 (by rfl) ⟨198348, by rfl⟩ : syracuseStep 528929 = 396697) B396697
theorem B234023 : Blo 155795 234023 := bstep (se 1 (by rfl) ⟨175517, by rfl⟩ : syracuseStep 234023 = 351035) B351035
theorem B201295 : Blo 155795 201295 := bstep (se 1 (by rfl) ⟨150971, by rfl⟩ : syracuseStep 201295 = 301943) B301943
theorem B234107 : Blo 155795 234107 := bstep (se 1 (by rfl) ⟨175580, by rfl⟩ : syracuseStep 234107 = 351161) B351161
theorem B168647 : Blo 155795 168647 := bstep (se 1 (by rfl) ⟨126485, by rfl⟩ : syracuseStep 168647 = 252971) B252971
theorem B234233 : Blo 155795 234233 := bstep (se 2 (by rfl) ⟨87837, by rfl⟩ : syracuseStep 234233 = 175675) B175675
theorem B529145 : Blo 155795 529145 := bstep (se 2 (by rfl) ⟨198429, by rfl⟩ : syracuseStep 529145 = 396859) B396859
theorem B1512209 : Blo 155795 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B791369 : Blo 155795 791369 := bstep (se 2 (by rfl) ⟨296763, by rfl⟩ : syracuseStep 791369 = 593527) B593527
theorem B234335 : Blo 155795 234335 := bstep (se 1 (by rfl) ⟨175751, by rfl⟩ : syracuseStep 234335 = 351503) B351503
theorem B234347 : Blo 155795 234347 := bstep (se 1 (by rfl) ⟨175760, by rfl⟩ : syracuseStep 234347 = 351521) B351521
theorem B4821875 : Blo 155795 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B267151 : Blo 155795 267151 := bstep (se 1 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 267151 = 400727) B400727
theorem B1217425 : Blo 155795 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B398267 : Blo 155795 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B529415 : Blo 155795 529415 := bstep (se 1 (by rfl) ⟨397061, by rfl⟩ : syracuseStep 529415 = 794123) B794123
theorem B234575 : Blo 155795 234575 := bstep (se 1 (by rfl) ⟨175931, by rfl⟩ : syracuseStep 234575 = 351863) B351863
theorem B529523 : Blo 155795 529523 := bstep (se 1 (by rfl) ⟨397142, by rfl⟩ : syracuseStep 529523 = 794285) B794285
theorem B1741943 : Blo 155795 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B234695 : Blo 155795 234695 := bstep (se 1 (by rfl) ⟨176021, by rfl⟩ : syracuseStep 234695 = 352043) B352043
theorem B234857 : Blo 155795 234857 := bstep (se 2 (by rfl) ⟨88071, by rfl⟩ : syracuseStep 234857 = 176143) B176143
theorem B529793 : Blo 155795 529793 := bstep (se 2 (by rfl) ⟨198672, by rfl⟩ : syracuseStep 529793 = 397345) B397345
theorem B7968131 : Blo 155795 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B234935 : Blo 155795 234935 := bstep (se 1 (by rfl) ⟨176201, by rfl⟩ : syracuseStep 234935 = 352403) B352403
theorem B234971 : Blo 155795 234971 := bstep (se 1 (by rfl) ⟨176228, by rfl⟩ : syracuseStep 234971 = 352457) B352457
theorem B562697 : Blo 155795 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B562727 : Blo 155795 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B267833 : Blo 155795 267833 := bstep (se 2 (by rfl) ⟨100437, by rfl⟩ : syracuseStep 267833 = 200875) B200875
theorem B398945 : Blo 155795 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B300667 : Blo 155795 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B300743 : Blo 155795 300743 := bstep (se 1 (by rfl) ⟨225557, by rfl⟩ : syracuseStep 300743 = 451115) B451115
theorem B235439 : Blo 155795 235439 := bstep (se 1 (by rfl) ⟨176579, by rfl⟩ : syracuseStep 235439 = 353159) B353159
theorem B235529 : Blo 155795 235529 := bstep (se 2 (by rfl) ⟨88323, by rfl⟩ : syracuseStep 235529 = 176647) B176647
theorem B235559 : Blo 155795 235559 := bstep (se 1 (by rfl) ⟨176669, by rfl⟩ : syracuseStep 235559 = 353339) B353339
theorem B792665 : Blo 155795 792665 := bstep (se 2 (by rfl) ⟨297249, by rfl⟩ : syracuseStep 792665 = 594499) B594499
theorem B301153 : Blo 155795 301153 := bstep (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) B225865
theorem B235643 : Blo 155795 235643 := bstep (se 1 (by rfl) ⟨176732, by rfl⟩ : syracuseStep 235643 = 353465) B353465
theorem B530603 : Blo 155795 530603 := bstep (se 1 (by rfl) ⟨397952, by rfl⟩ : syracuseStep 530603 = 795905) B795905
theorem B268535 : Blo 155795 268535 := bstep (se 1 (by rfl) ⟨201401, by rfl⟩ : syracuseStep 268535 = 402803) B402803
theorem B235769 : Blo 155795 235769 := bstep (se 2 (by rfl) ⟨88413, by rfl⟩ : syracuseStep 235769 = 176827) B176827
theorem B235871 : Blo 155795 235871 := bstep (se 1 (by rfl) ⟨176903, by rfl⟩ : syracuseStep 235871 = 353807) B353807
theorem B235883 : Blo 155795 235883 := bstep (se 1 (by rfl) ⟨176912, by rfl⟩ : syracuseStep 235883 = 353825) B353825
theorem B301495 : Blo 155795 301495 := bstep (se 1 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 301495 = 452243) B452243
theorem B596443 : Blo 155795 596443 := bstep (se 1 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 596443 = 894665) B894665
theorem B236111 : Blo 155795 236111 := bstep (se 1 (by rfl) ⟨177083, by rfl⟩ : syracuseStep 236111 = 354167) B354167
theorem B268879 : Blo 155795 268879 := bstep (se 1 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 268879 = 403319) B403319
theorem B7740035 : Blo 155795 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B531143 : Blo 155795 531143 := bstep (se 1 (by rfl) ⟨398357, by rfl⟩ : syracuseStep 531143 = 796715) B796715
theorem B236231 : Blo 155795 236231 := bstep (se 1 (by rfl) ⟨177173, by rfl⟩ : syracuseStep 236231 = 354347) B354347
theorem B1284817 : Blo 155795 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B301897 : Blo 155795 301897 := bstep (se 2 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 301897 = 226423) B226423
theorem B269129 : Blo 155795 269129 := bstep (se 2 (by rfl) ⟨100923, by rfl⟩ : syracuseStep 269129 = 201847) B201847
theorem B236393 : Blo 155795 236393 := bstep (se 2 (by rfl) ⟨88647, by rfl⟩ : syracuseStep 236393 = 177295) B177295
theorem B236471 : Blo 155795 236471 := bstep (se 1 (by rfl) ⟨177353, by rfl⟩ : syracuseStep 236471 = 354707) B354707
theorem B236507 : Blo 155795 236507 := bstep (se 1 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 236507 = 354761) B354761
theorem B400403 : Blo 155795 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B269561 : Blo 155795 269561 := bstep (se 2 (by rfl) ⟨101085, by rfl⟩ : syracuseStep 269561 = 202171) B202171
theorem B4300121 : Blo 155795 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B236975 : Blo 155795 236975 := bstep (se 1 (by rfl) ⟨177731, by rfl⟩ : syracuseStep 236975 = 355463) B355463
theorem B400859 : Blo 155795 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B237065 : Blo 155795 237065 := bstep (se 2 (by rfl) ⟨88899, by rfl⟩ : syracuseStep 237065 = 177799) B177799
theorem B302611 : Blo 155795 302611 := bstep (se 1 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 302611 = 453917) B453917
theorem B532007 : Blo 155795 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B237095 : Blo 155795 237095 := bstep (se 1 (by rfl) ⟨177821, by rfl⟩ : syracuseStep 237095 = 355643) B355643
theorem B237179 : Blo 155795 237179 := bstep (se 1 (by rfl) ⟨177884, by rfl⟩ : syracuseStep 237179 = 355769) B355769
theorem B532115 : Blo 155795 532115 := bstep (se 1 (by rfl) ⟨399086, by rfl⟩ : syracuseStep 532115 = 798173) B798173
theorem B597689 : Blo 155795 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B597719 : Blo 155795 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B38969059 : Blo 155795 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B237305 : Blo 155795 237305 := bstep (se 2 (by rfl) ⟨88989, by rfl⟩ : syracuseStep 237305 = 177979) B177979
theorem B237407 : Blo 155795 237407 := bstep (se 1 (by rfl) ⟨178055, by rfl⟩ : syracuseStep 237407 = 356111) B356111
theorem B302953 : Blo 155795 302953 := bstep (se 2 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 302953 = 227215) B227215
theorem B532331 : Blo 155795 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B237419 : Blo 155795 237419 := bstep (se 1 (by rfl) ⟨178064, by rfl⟩ : syracuseStep 237419 = 356129) B356129
theorem B1613699 : Blo 155795 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B532385 : Blo 155795 532385 := bstep (se 2 (by rfl) ⟨199644, by rfl⟩ : syracuseStep 532385 = 399289) B399289
theorem B237647 : Blo 155795 237647 := bstep (se 1 (by rfl) ⟨178235, by rfl⟩ : syracuseStep 237647 = 356471) B356471
theorem B237767 : Blo 155795 237767 := bstep (se 1 (by rfl) ⟨178325, by rfl⟩ : syracuseStep 237767 = 356651) B356651
theorem B237929 : Blo 155795 237929 := bstep (se 2 (by rfl) ⟨89223, by rfl⟩ : syracuseStep 237929 = 178447) B178447
theorem B17375633 : Blo 155795 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B238007 : Blo 155795 238007 := bstep (se 1 (by rfl) ⟨178505, by rfl⟩ : syracuseStep 238007 = 357011) B357011
theorem B238043 : Blo 155795 238043 := bstep (se 1 (by rfl) ⟨178532, by rfl⟩ : syracuseStep 238043 = 357065) B357065
theorem B532979 : Blo 155795 532979 := bstep (se 1 (by rfl) ⟨399734, by rfl⟩ : syracuseStep 532979 = 799469) B799469
theorem B402043 : Blo 155795 402043 := bstep (se 1 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 402043 = 603065) B603065
theorem B1024913 : Blo 155795 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B1188755 : Blo 155795 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B238511 : Blo 155795 238511 := bstep (se 1 (by rfl) ⟨178883, by rfl⟩ : syracuseStep 238511 = 357767) B357767
theorem B238601 : Blo 155795 238601 := bstep (se 2 (by rfl) ⟨89475, by rfl⟩ : syracuseStep 238601 = 178951) B178951
theorem B533519 : Blo 155795 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B238631 : Blo 155795 238631 := bstep (se 1 (by rfl) ⟨178973, by rfl⟩ : syracuseStep 238631 = 357947) B357947
theorem B336953 : Blo 155795 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B238715 : Blo 155795 238715 := bstep (se 1 (by rfl) ⟨179036, by rfl⟩ : syracuseStep 238715 = 358073) B358073
theorem B238841 : Blo 155795 238841 := bstep (se 2 (by rfl) ⟨89565, by rfl⟩ : syracuseStep 238841 = 179131) B179131
theorem B238943 : Blo 155795 238943 := bstep (se 1 (by rfl) ⟨179207, by rfl⟩ : syracuseStep 238943 = 358415) B358415
theorem B238955 : Blo 155795 238955 := bstep (se 1 (by rfl) ⟨179216, by rfl⟩ : syracuseStep 238955 = 358433) B358433
theorem B239183 : Blo 155795 239183 := bstep (se 1 (by rfl) ⟨179387, by rfl⟩ : syracuseStep 239183 = 358775) B358775
theorem B534113 : Blo 155795 534113 := bstep (se 2 (by rfl) ⟨200292, by rfl⟩ : syracuseStep 534113 = 400585) B400585
theorem B239303 : Blo 155795 239303 := bstep (se 1 (by rfl) ⟨179477, by rfl⟩ : syracuseStep 239303 = 358955) B358955
theorem B1189727 : Blo 155795 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B239465 : Blo 155795 239465 := bstep (se 2 (by rfl) ⟨89799, by rfl⟩ : syracuseStep 239465 = 179599) B179599
theorem B1288045 : Blo 155795 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B239543 : Blo 155795 239543 := bstep (se 1 (by rfl) ⟨179657, by rfl⟩ : syracuseStep 239543 = 359315) B359315
theorem B239579 : Blo 155795 239579 := bstep (se 1 (by rfl) ⟨179684, by rfl⟩ : syracuseStep 239579 = 359369) B359369
theorem B6400133 : Blo 155795 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B600331 : Blo 155795 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B1681817 : Blo 155795 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B535027 : Blo 155795 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B240137 : Blo 155795 240137 := bstep (se 2 (by rfl) ⟨90051, by rfl⟩ : syracuseStep 240137 = 180103) B180103
theorem B600635 : Blo 155795 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B1354643 : Blo 155795 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B1289135 : Blo 155795 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B666625 : Blo 155795 666625 := bstep (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) B499969
theorem B338951 : Blo 155795 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B535571 : Blo 155795 535571 := bstep (se 1 (by rfl) ⟨401678, by rfl⟩ : syracuseStep 535571 = 803357) B803357
theorem B797849 : Blo 155795 797849 := bstep (se 2 (by rfl) ⟨299193, by rfl⟩ : syracuseStep 797849 = 598387) B598387
theorem B2174147 : Blo 155795 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B1813751 : Blo 155795 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B535895 : Blo 155795 535895 := bstep (se 1 (by rfl) ⟨401921, by rfl⟩ : syracuseStep 535895 = 803843) B803843
theorem B2010743 : Blo 155795 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B601789 : Blo 155795 601789 := bstep (se 3 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 601789 = 225671) B225671
theorem B176251 : Blo 155795 176251 := bstep (se 1 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 176251 = 264377) B264377
theorem B569501 : Blo 155795 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B340139 : Blo 155795 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B3649853 : Blo 155795 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B536975 : Blo 155795 536975 := bstep (se 1 (by rfl) ⟨402731, by rfl⟩ : syracuseStep 536975 = 805463) B805463
theorem B176719 : Blo 155795 176719 := bstep (se 1 (by rfl) ⟨132539, by rfl⟩ : syracuseStep 176719 = 265079) B265079
theorem B602747 : Blo 155795 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B537299 : Blo 155795 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B504737 : Blo 155795 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B177115 : Blo 155795 177115 := bstep (se 1 (by rfl) ⟨132836, by rfl⟩ : syracuseStep 177115 = 265673) B265673
theorem B1127467 : Blo 155795 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B406775 : Blo 155795 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B603521 : Blo 155795 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B2602405 : Blo 155795 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B177583 : Blo 155795 177583 := bstep (se 1 (by rfl) ⟨133187, by rfl⟩ : syracuseStep 177583 = 266375) B266375
theorem B505403 : Blo 155795 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B1652285 : Blo 155795 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B178015 : Blo 155795 178015 := bstep (se 1 (by rfl) ⟨133511, by rfl⟩ : syracuseStep 178015 = 267023) B267023
theorem B538487 : Blo 155795 538487 := bstep (se 1 (by rfl) ⟨403865, by rfl⟩ : syracuseStep 538487 = 807731) B807731
theorem B538703 : Blo 155795 538703 := bstep (se 1 (by rfl) ⟨404027, by rfl⟩ : syracuseStep 538703 = 808055) B808055
theorem B3225757 : Blo 155795 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B178375 : Blo 155795 178375 := bstep (se 1 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 178375 = 267563) B267563
theorem B539081 : Blo 155795 539081 := bstep (se 2 (by rfl) ⟨202155, by rfl⟩ : syracuseStep 539081 = 404311) B404311
theorem B1358369 : Blo 155795 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B604705 : Blo 155795 604705 := bstep (se 2 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 604705 = 453529) B453529
theorem B637739 : Blo 155795 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B342967 : Blo 155795 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B375815 : Blo 155795 375815 := bstep (se 1 (by rfl) ⟨281861, by rfl⟩ : syracuseStep 375815 = 563723) B563723
theorem B605191 : Blo 155795 605191 := bstep (se 1 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 605191 = 907787) B907787
theorem B179239 : Blo 155795 179239 := bstep (se 1 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 179239 = 268859) B268859
theorem B1719575 : Blo 155795 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B507197 : Blo 155795 507197 := bstep (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) B190199
theorem B605677 : Blo 155795 605677 := bstep (se 3 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 605677 = 227129) B227129
theorem B572953 : Blo 155795 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B1195559 : Blo 155795 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B605981 : Blo 155795 605981 := bstep (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) B227243
theorem B999377 : Blo 155795 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B541129 : Blo 155795 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B344825 : Blo 155795 344825 := bstep (se 2 (by rfl) ⟨129309, by rfl⟩ : syracuseStep 344825 = 258619) B258619
theorem B214265 : Blo 155795 214265 := bstep (se 2 (by rfl) ⟨80349, by rfl⟩ : syracuseStep 214265 = 160699) B160699
theorem B804491 : Blo 155795 804491 := bstep (se 1 (by rfl) ⟨603368, by rfl⟩ : syracuseStep 804491 = 1206737) B1206737
theorem B2246291 : Blo 155795 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B640723 : Blo 155795 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B4540211 : Blo 155795 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B510067 : Blo 155795 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B575831 : Blo 155795 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B1133003 : Blo 155795 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B444953 : Blo 155795 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B2411693 : Blo 155795 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B970157 : Blo 155795 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B642505 : Blo 155795 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B511451 : Blo 155795 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B380513 : Blo 155795 380513 := bstep (se 2 (by rfl) ⟨142692, by rfl⟩ : syracuseStep 380513 = 285385) B285385
theorem B479083 : Blo 155795 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B2215795 : Blo 155795 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B1331063 : Blo 155795 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B249895 : Blo 155795 249895 := bstep (se 1 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 249895 = 374843) B374843
theorem B1626193 : Blo 155795 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B249979 : Blo 155795 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B545129 : Blo 155795 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B479933 : Blo 155795 479933 := bstep (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) B179975
theorem B1069777 : Blo 155795 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B250697 : Blo 155795 250697 := bstep (se 2 (by rfl) ⟨94011, by rfl⟩ : syracuseStep 250697 = 188023) B188023
theorem B251209 : Blo 155795 251209 := bstep (se 2 (by rfl) ⟨94203, by rfl⟩ : syracuseStep 251209 = 188407) B188407
theorem B447869 : Blo 155795 447869 := bstep (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) B167951
theorem B251471 : Blo 155795 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B448199 : Blo 155795 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B2447147 : Blo 155795 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B251753 : Blo 155795 251753 := bstep (se 2 (by rfl) ⟨94407, by rfl⟩ : syracuseStep 251753 = 188815) B188815
theorem B1005473 : Blo 155795 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B808865 : Blo 155795 808865 := bstep (se 2 (by rfl) ⟨303324, by rfl⟩ : syracuseStep 808865 = 606649) B606649
theorem B284635 : Blo 155795 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B383147 : Blo 155795 383147 := bstep (se 1 (by rfl) ⟨287360, by rfl⟩ : syracuseStep 383147 = 574721) B574721
theorem B350729 : Blo 155795 350729 := bstep (se 2 (by rfl) ⟨131523, by rfl⟩ : syracuseStep 350729 = 263047) B263047
theorem B1071751 : Blo 155795 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1137361 : Blo 155795 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B383699 : Blo 155795 383699 := bstep (se 1 (by rfl) ⟨287774, by rfl⟩ : syracuseStep 383699 = 575549) B575549
theorem B351071 : Blo 155795 351071 := bstep (se 1 (by rfl) ⟨263303, by rfl⟩ : syracuseStep 351071 = 526607) B526607
theorem B449543 : Blo 155795 449543 := bstep (se 1 (by rfl) ⟨337157, by rfl⟩ : syracuseStep 449543 = 674315) B674315
theorem B351251 : Blo 155795 351251 := bstep (se 1 (by rfl) ⟨263438, by rfl⟩ : syracuseStep 351251 = 526877) B526877
theorem B449783 : Blo 155795 449783 := bstep (se 1 (by rfl) ⟨337337, by rfl⟩ : syracuseStep 449783 = 674675) B674675
theorem B351593 : Blo 155795 351593 := bstep (se 2 (by rfl) ⟨131847, by rfl⟩ : syracuseStep 351593 = 263695) B263695
theorem B483031 : Blo 155795 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B679747 : Blo 155795 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B352187 : Blo 155795 352187 := bstep (se 1 (by rfl) ⟨264140, by rfl⟩ : syracuseStep 352187 = 528281) B528281
theorem B352313 : Blo 155795 352313 := bstep (se 2 (by rfl) ⟨132117, by rfl⟩ : syracuseStep 352313 = 264235) B264235
theorem B254009 : Blo 155795 254009 := bstep (se 2 (by rfl) ⟨95253, by rfl⟩ : syracuseStep 254009 = 190507) B190507
theorem B909427 : Blo 155795 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B155823 : Blo 155795 155823 := bstep (se 1 (by rfl) ⟨116867, by rfl⟩ : syracuseStep 155823 = 233735) B233735
theorem B155847 : Blo 155795 155847 := bstep (se 1 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 155847 = 233771) B233771
theorem B155867 : Blo 155795 155867 := bstep (se 1 (by rfl) ⟨116900, by rfl⟩ : syracuseStep 155867 = 233801) B233801
theorem B155943 : Blo 155795 155943 := bstep (se 1 (by rfl) ⟨116957, by rfl⟩ : syracuseStep 155943 = 233915) B233915
theorem B155983 : Blo 155795 155983 := bstep (se 1 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 155983 = 233975) B233975
theorem B155999 : Blo 155795 155999 := bstep (se 1 (by rfl) ⟨116999, by rfl⟩ : syracuseStep 155999 = 233999) B233999
theorem B156027 : Blo 155795 156027 := bstep (se 1 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 156027 = 234041) B234041
theorem B352655 : Blo 155795 352655 := bstep (se 1 (by rfl) ⟨264491, by rfl⟩ : syracuseStep 352655 = 528983) B528983
theorem B156079 : Blo 155795 156079 := bstep (se 1 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 156079 = 234119) B234119
theorem B156103 : Blo 155795 156103 := bstep (se 1 (by rfl) ⟨117077, by rfl⟩ : syracuseStep 156103 = 234155) B234155
theorem B156123 : Blo 155795 156123 := bstep (se 1 (by rfl) ⟨117092, by rfl⟩ : syracuseStep 156123 = 234185) B234185
theorem B811529 : Blo 155795 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B156199 : Blo 155795 156199 := bstep (se 1 (by rfl) ⟨117149, by rfl⟩ : syracuseStep 156199 = 234299) B234299
theorem B156239 : Blo 155795 156239 := bstep (se 1 (by rfl) ⟨117179, by rfl⟩ : syracuseStep 156239 = 234359) B234359
theorem B156255 : Blo 155795 156255 := bstep (se 1 (by rfl) ⟨117191, by rfl⟩ : syracuseStep 156255 = 234383) B234383
theorem B156283 : Blo 155795 156283 := bstep (se 1 (by rfl) ⟨117212, by rfl⟩ : syracuseStep 156283 = 234425) B234425
theorem B156335 : Blo 155795 156335 := bstep (se 1 (by rfl) ⟨117251, by rfl⟩ : syracuseStep 156335 = 234503) B234503
theorem B156359 : Blo 155795 156359 := bstep (se 1 (by rfl) ⟨117269, by rfl⟩ : syracuseStep 156359 = 234539) B234539
theorem B352979 : Blo 155795 352979 := bstep (se 1 (by rfl) ⟨264734, by rfl⟩ : syracuseStep 352979 = 529469) B529469
theorem B156379 : Blo 155795 156379 := bstep (se 1 (by rfl) ⟨117284, by rfl⟩ : syracuseStep 156379 = 234569) B234569
theorem B156455 : Blo 155795 156455 := bstep (se 1 (by rfl) ⟨117341, by rfl⟩ : syracuseStep 156455 = 234683) B234683
theorem B156495 : Blo 155795 156495 := bstep (se 1 (by rfl) ⟨117371, by rfl⟩ : syracuseStep 156495 = 234743) B234743
theorem B156511 : Blo 155795 156511 := bstep (se 1 (by rfl) ⟨117383, by rfl⟩ : syracuseStep 156511 = 234767) B234767
theorem B156539 : Blo 155795 156539 := bstep (se 1 (by rfl) ⟨117404, by rfl⟩ : syracuseStep 156539 = 234809) B234809
theorem B156591 : Blo 155795 156591 := bstep (se 1 (by rfl) ⟨117443, by rfl⟩ : syracuseStep 156591 = 234887) B234887
theorem B156615 : Blo 155795 156615 := bstep (se 1 (by rfl) ⟨117461, by rfl⟩ : syracuseStep 156615 = 234923) B234923
theorem B156635 : Blo 155795 156635 := bstep (se 1 (by rfl) ⟨117476, by rfl⟩ : syracuseStep 156635 = 234953) B234953
theorem B287707 : Blo 155795 287707 := bstep (se 1 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 287707 = 431561) B431561
theorem B254983 : Blo 155795 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B156711 : Blo 155795 156711 := bstep (se 1 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 156711 = 235067) B235067
theorem B1303595 : Blo 155795 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B156751 : Blo 155795 156751 := bstep (se 1 (by rfl) ⟨117563, by rfl⟩ : syracuseStep 156751 = 235127) B235127
theorem B156767 : Blo 155795 156767 := bstep (se 1 (by rfl) ⟨117575, by rfl⟩ : syracuseStep 156767 = 235151) B235151
theorem B156795 : Blo 155795 156795 := bstep (se 1 (by rfl) ⟨117596, by rfl⟩ : syracuseStep 156795 = 235193) B235193
theorem B156847 : Blo 155795 156847 := bstep (se 1 (by rfl) ⟨117635, by rfl⟩ : syracuseStep 156847 = 235271) B235271
theorem B156871 : Blo 155795 156871 := bstep (se 1 (by rfl) ⟨117653, by rfl⟩ : syracuseStep 156871 = 235307) B235307
theorem B156891 : Blo 155795 156891 := bstep (se 1 (by rfl) ⟨117668, by rfl⟩ : syracuseStep 156891 = 235337) B235337
theorem B976151 : Blo 155795 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B156967 : Blo 155795 156967 := bstep (se 1 (by rfl) ⟨117725, by rfl⟩ : syracuseStep 156967 = 235451) B235451
theorem B157007 : Blo 155795 157007 := bstep (se 1 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 157007 = 235511) B235511
theorem B157023 : Blo 155795 157023 := bstep (se 1 (by rfl) ⟨117767, by rfl⟩ : syracuseStep 157023 = 235535) B235535
theorem B157051 : Blo 155795 157051 := bstep (se 1 (by rfl) ⟨117788, by rfl⟩ : syracuseStep 157051 = 235577) B235577
theorem B157103 : Blo 155795 157103 := bstep (se 1 (by rfl) ⟨117827, by rfl⟩ : syracuseStep 157103 = 235655) B235655
theorem B157127 : Blo 155795 157127 := bstep (se 1 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 157127 = 235691) B235691
theorem B157147 : Blo 155795 157147 := bstep (se 1 (by rfl) ⟨117860, by rfl⟩ : syracuseStep 157147 = 235721) B235721
theorem B1500677 : Blo 155795 1500677 := bstep (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) B281377
theorem B157223 : Blo 155795 157223 := bstep (se 1 (by rfl) ⟨117917, by rfl⟩ : syracuseStep 157223 = 235835) B235835
theorem B157263 : Blo 155795 157263 := bstep (se 1 (by rfl) ⟨117947, by rfl⟩ : syracuseStep 157263 = 235895) B235895
theorem B157279 : Blo 155795 157279 := bstep (se 1 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 157279 = 235919) B235919
theorem B353915 : Blo 155795 353915 := bstep (se 1 (by rfl) ⟨265436, by rfl⟩ : syracuseStep 353915 = 530873) B530873
theorem B157307 : Blo 155795 157307 := bstep (se 1 (by rfl) ⟨117980, by rfl⟩ : syracuseStep 157307 = 235961) B235961
theorem B157359 : Blo 155795 157359 := bstep (se 1 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 157359 = 236039) B236039
theorem B157383 : Blo 155795 157383 := bstep (se 1 (by rfl) ⟨118037, by rfl⟩ : syracuseStep 157383 = 236075) B236075
theorem B157403 : Blo 155795 157403 := bstep (se 1 (by rfl) ⟨118052, by rfl⟩ : syracuseStep 157403 = 236105) B236105
theorem B354041 : Blo 155795 354041 := bstep (se 2 (by rfl) ⟨132765, by rfl⟩ : syracuseStep 354041 = 265531) B265531
theorem B157479 : Blo 155795 157479 := bstep (se 1 (by rfl) ⟨118109, by rfl⟩ : syracuseStep 157479 = 236219) B236219
theorem B812843 : Blo 155795 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B1337147 : Blo 155795 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B452425 : Blo 155795 452425 := bstep (se 2 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 452425 = 339319) B339319
theorem B157519 : Blo 155795 157519 := bstep (se 1 (by rfl) ⟨118139, by rfl⟩ : syracuseStep 157519 = 236279) B236279
theorem B157535 : Blo 155795 157535 := bstep (se 1 (by rfl) ⟨118151, by rfl⟩ : syracuseStep 157535 = 236303) B236303
theorem B452459 : Blo 155795 452459 := bstep (se 1 (by rfl) ⟨339344, by rfl⟩ : syracuseStep 452459 = 678689) B678689
theorem B157563 : Blo 155795 157563 := bstep (se 1 (by rfl) ⟨118172, by rfl⟩ : syracuseStep 157563 = 236345) B236345
theorem B157615 : Blo 155795 157615 := bstep (se 1 (by rfl) ⟨118211, by rfl⟩ : syracuseStep 157615 = 236423) B236423
theorem B157639 : Blo 155795 157639 := bstep (se 1 (by rfl) ⟨118229, by rfl⟩ : syracuseStep 157639 = 236459) B236459
theorem B157659 : Blo 155795 157659 := bstep (se 1 (by rfl) ⟨118244, by rfl⟩ : syracuseStep 157659 = 236489) B236489
theorem B354311 : Blo 155795 354311 := bstep (se 1 (by rfl) ⟨265733, by rfl⟩ : syracuseStep 354311 = 531467) B531467
theorem B157735 : Blo 155795 157735 := bstep (se 1 (by rfl) ⟨118301, by rfl⟩ : syracuseStep 157735 = 236603) B236603
theorem B354383 : Blo 155795 354383 := bstep (se 1 (by rfl) ⟨265787, by rfl⟩ : syracuseStep 354383 = 531575) B531575
theorem B157775 : Blo 155795 157775 := bstep (se 1 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 157775 = 236663) B236663
theorem B157791 : Blo 155795 157791 := bstep (se 1 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 157791 = 236687) B236687
theorem B157819 : Blo 155795 157819 := bstep (se 1 (by rfl) ⟨118364, by rfl⟩ : syracuseStep 157819 = 236729) B236729
theorem B157871 : Blo 155795 157871 := bstep (se 1 (by rfl) ⟨118403, by rfl⟩ : syracuseStep 157871 = 236807) B236807
theorem B157895 : Blo 155795 157895 := bstep (se 1 (by rfl) ⟨118421, by rfl⟩ : syracuseStep 157895 = 236843) B236843
theorem B157915 : Blo 155795 157915 := bstep (se 1 (by rfl) ⟨118436, by rfl⟩ : syracuseStep 157915 = 236873) B236873
theorem B1599745 : Blo 155795 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B157991 : Blo 155795 157991 := bstep (se 1 (by rfl) ⟨118493, by rfl⟩ : syracuseStep 157991 = 236987) B236987
theorem B158031 : Blo 155795 158031 := bstep (se 1 (by rfl) ⟨118523, by rfl⟩ : syracuseStep 158031 = 237047) B237047
theorem B3107159 : Blo 155795 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B158047 : Blo 155795 158047 := bstep (se 1 (by rfl) ⟨118535, by rfl⟩ : syracuseStep 158047 = 237071) B237071
theorem B158075 : Blo 155795 158075 := bstep (se 1 (by rfl) ⟨118556, by rfl⟩ : syracuseStep 158075 = 237113) B237113
theorem B158127 : Blo 155795 158127 := bstep (se 1 (by rfl) ⟨118595, by rfl⟩ : syracuseStep 158127 = 237191) B237191
theorem B158151 : Blo 155795 158151 := bstep (se 1 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 158151 = 237227) B237227
theorem B354779 : Blo 155795 354779 := bstep (se 1 (by rfl) ⟨266084, by rfl⟩ : syracuseStep 354779 = 532169) B532169
theorem B158171 : Blo 155795 158171 := bstep (se 1 (by rfl) ⟨118628, by rfl⟩ : syracuseStep 158171 = 237257) B237257
theorem B158247 : Blo 155795 158247 := bstep (se 1 (by rfl) ⟨118685, by rfl⟩ : syracuseStep 158247 = 237371) B237371
theorem B1141307 : Blo 155795 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B158287 : Blo 155795 158287 := bstep (se 1 (by rfl) ⟨118715, by rfl⟩ : syracuseStep 158287 = 237431) B237431
theorem B158303 : Blo 155795 158303 := bstep (se 1 (by rfl) ⟨118727, by rfl⟩ : syracuseStep 158303 = 237455) B237455
theorem B158331 : Blo 155795 158331 := bstep (se 1 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 158331 = 237497) B237497
theorem B158383 : Blo 155795 158383 := bstep (se 1 (by rfl) ⟨118787, by rfl⟩ : syracuseStep 158383 = 237575) B237575
theorem B158407 : Blo 155795 158407 := bstep (se 1 (by rfl) ⟨118805, by rfl⟩ : syracuseStep 158407 = 237611) B237611
theorem B158427 : Blo 155795 158427 := bstep (se 1 (by rfl) ⟨118820, by rfl⟩ : syracuseStep 158427 = 237641) B237641
theorem B158503 : Blo 155795 158503 := bstep (se 1 (by rfl) ⟨118877, by rfl⟩ : syracuseStep 158503 = 237755) B237755
theorem B3337037 : Blo 155795 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B158543 : Blo 155795 158543 := bstep (se 1 (by rfl) ⟨118907, by rfl⟩ : syracuseStep 158543 = 237815) B237815
theorem B158559 : Blo 155795 158559 := bstep (se 1 (by rfl) ⟨118919, by rfl⟩ : syracuseStep 158559 = 237839) B237839
theorem B158587 : Blo 155795 158587 := bstep (se 1 (by rfl) ⟨118940, by rfl⟩ : syracuseStep 158587 = 237881) B237881
theorem B355247 : Blo 155795 355247 := bstep (se 1 (by rfl) ⟨266435, by rfl⟩ : syracuseStep 355247 = 532871) B532871
theorem B158639 : Blo 155795 158639 := bstep (se 1 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 158639 = 237959) B237959
theorem B1207223 : Blo 155795 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B158663 : Blo 155795 158663 := bstep (se 1 (by rfl) ⟨118997, by rfl⟩ : syracuseStep 158663 = 237995) B237995
theorem B158683 : Blo 155795 158683 := bstep (se 1 (by rfl) ⟨119012, by rfl⟩ : syracuseStep 158683 = 238025) B238025
theorem B158759 : Blo 155795 158759 := bstep (se 1 (by rfl) ⟨119069, by rfl⟩ : syracuseStep 158759 = 238139) B238139
theorem B158799 : Blo 155795 158799 := bstep (se 1 (by rfl) ⟨119099, by rfl⟩ : syracuseStep 158799 = 238199) B238199
theorem B158815 : Blo 155795 158815 := bstep (se 1 (by rfl) ⟨119111, by rfl⟩ : syracuseStep 158815 = 238223) B238223
theorem B158843 : Blo 155795 158843 := bstep (se 1 (by rfl) ⟨119132, by rfl⟩ : syracuseStep 158843 = 238265) B238265
theorem B355499 : Blo 155795 355499 := bstep (se 1 (by rfl) ⟨266624, by rfl⟩ : syracuseStep 355499 = 533249) B533249
theorem B158895 : Blo 155795 158895 := bstep (se 1 (by rfl) ⟨119171, by rfl⟩ : syracuseStep 158895 = 238343) B238343
theorem B158919 : Blo 155795 158919 := bstep (se 1 (by rfl) ⟨119189, by rfl⟩ : syracuseStep 158919 = 238379) B238379
theorem B158939 : Blo 155795 158939 := bstep (se 1 (by rfl) ⟨119204, by rfl⟩ : syracuseStep 158939 = 238409) B238409
theorem B159015 : Blo 155795 159015 := bstep (se 1 (by rfl) ⟨119261, by rfl⟩ : syracuseStep 159015 = 238523) B238523
theorem B159055 : Blo 155795 159055 := bstep (se 1 (by rfl) ⟨119291, by rfl⟩ : syracuseStep 159055 = 238583) B238583
theorem B159071 : Blo 155795 159071 := bstep (se 1 (by rfl) ⟨119303, by rfl⟩ : syracuseStep 159071 = 238607) B238607
theorem B159099 : Blo 155795 159099 := bstep (se 1 (by rfl) ⟨119324, by rfl⟩ : syracuseStep 159099 = 238649) B238649
theorem B454031 : Blo 155795 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B159151 : Blo 155795 159151 := bstep (se 1 (by rfl) ⟨119363, by rfl⟩ : syracuseStep 159151 = 238727) B238727
theorem B159175 : Blo 155795 159175 := bstep (se 1 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 159175 = 238763) B238763
theorem B159195 : Blo 155795 159195 := bstep (se 1 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 159195 = 238793) B238793
theorem B159271 : Blo 155795 159271 := bstep (se 1 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 159271 = 238907) B238907
theorem B159311 : Blo 155795 159311 := bstep (se 1 (by rfl) ⟨119483, by rfl⟩ : syracuseStep 159311 = 238967) B238967
theorem B159327 : Blo 155795 159327 := bstep (se 1 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 159327 = 238991) B238991
theorem B159355 : Blo 155795 159355 := bstep (se 1 (by rfl) ⟨119516, by rfl⟩ : syracuseStep 159355 = 239033) B239033
theorem B159407 : Blo 155795 159407 := bstep (se 1 (by rfl) ⟨119555, by rfl⟩ : syracuseStep 159407 = 239111) B239111
theorem B356039 : Blo 155795 356039 := bstep (se 1 (by rfl) ⟨267029, by rfl⟩ : syracuseStep 356039 = 534059) B534059
theorem B159431 : Blo 155795 159431 := bstep (se 1 (by rfl) ⟨119573, by rfl⟩ : syracuseStep 159431 = 239147) B239147
theorem B159451 : Blo 155795 159451 := bstep (se 1 (by rfl) ⟨119588, by rfl⟩ : syracuseStep 159451 = 239177) B239177
theorem B159527 : Blo 155795 159527 := bstep (se 1 (by rfl) ⟨119645, by rfl⟩ : syracuseStep 159527 = 239291) B239291
theorem B159567 : Blo 155795 159567 := bstep (se 1 (by rfl) ⟨119675, by rfl⟩ : syracuseStep 159567 = 239351) B239351
theorem B225119 : Blo 155795 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B159583 : Blo 155795 159583 := bstep (se 1 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 159583 = 239375) B239375
theorem B159611 : Blo 155795 159611 := bstep (se 1 (by rfl) ⟨119708, by rfl⟩ : syracuseStep 159611 = 239417) B239417
theorem B159663 : Blo 155795 159663 := bstep (se 1 (by rfl) ⟨119747, by rfl⟩ : syracuseStep 159663 = 239495) B239495
theorem B159687 : Blo 155795 159687 := bstep (se 1 (by rfl) ⟨119765, by rfl⟩ : syracuseStep 159687 = 239531) B239531
theorem B159707 : Blo 155795 159707 := bstep (se 1 (by rfl) ⟨119780, by rfl⟩ : syracuseStep 159707 = 239561) B239561
theorem B159783 : Blo 155795 159783 := bstep (se 1 (by rfl) ⟨119837, by rfl⟩ : syracuseStep 159783 = 239675) B239675
theorem B2289995 : Blo 155795 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1208681 : Blo 155795 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B356903 : Blo 155795 356903 := bstep (se 1 (by rfl) ⟨267677, by rfl⟩ : syracuseStep 356903 = 535355) B535355
theorem B357227 : Blo 155795 357227 := bstep (se 1 (by rfl) ⟨267920, by rfl⟩ : syracuseStep 357227 = 535841) B535841
theorem B357281 : Blo 155795 357281 := bstep (se 2 (by rfl) ⟨133980, by rfl⟩ : syracuseStep 357281 = 267961) B267961
theorem B783361 : Blo 155795 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B357623 : Blo 155795 357623 := bstep (se 1 (by rfl) ⟨268217, by rfl⟩ : syracuseStep 357623 = 536435) B536435
theorem B1340873 : Blo 155795 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B1144307 : Blo 155795 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B358217 : Blo 155795 358217 := bstep (se 2 (by rfl) ⟨134331, by rfl⟩ : syracuseStep 358217 = 268663) B268663
theorem B1210625 : Blo 155795 1210625 := bstep (se 2 (by rfl) ⟨453984, by rfl⟩ : syracuseStep 1210625 = 907969) B907969
theorem B1210889 : Blo 155795 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B359009 : Blo 155795 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B1080067 : Blo 155795 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B359351 : Blo 155795 359351 := bstep (se 1 (by rfl) ⟨269513, by rfl⟩ : syracuseStep 359351 = 539027) B539027
theorem B1015213 : Blo 155795 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B7044569 : Blo 155795 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B425915 : Blo 155795 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1212569 : Blo 155795 1212569 := bstep (se 2 (by rfl) ⟨454713, by rfl⟩ : syracuseStep 1212569 = 909427) B909427
theorem B229883 : Blo 155795 229883 := bstep (se 1 (by rfl) ⟨172412, by rfl⟩ : syracuseStep 229883 = 344825) B344825
theorem B721505 : Blo 155795 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B328367 : Blo 155795 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B2884571 : Blo 155795 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B394379 : Blo 155795 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B394591 : Blo 155795 394591 := bstep (se 1 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 394591 = 591887) B591887
theorem B198055 : Blo 155795 198055 := bstep (se 1 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 198055 = 297083) B297083
theorem B755335 : Blo 155795 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B296635 : Blo 155795 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B198379 : Blo 155795 198379 := bstep (se 1 (by rfl) ⟨148784, by rfl⟩ : syracuseStep 198379 = 297569) B297569
theorem B198607 : Blo 155795 198607 := bstep (se 1 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 198607 = 297911) B297911
theorem B1607795 : Blo 155795 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B198875 : Blo 155795 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B854297 : Blo 155795 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B264539 : Blo 155795 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B264559 : Blo 155795 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B264775 : Blo 155795 264775 := bstep (se 1 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 264775 = 397163) B397163
theorem B887375 : Blo 155795 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B199351 : Blo 155795 199351 := bstep (se 1 (by rfl) ⟨149513, by rfl⟩ : syracuseStep 199351 = 299027) B299027
theorem B395999 : Blo 155795 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B199579 : Blo 155795 199579 := bstep (se 1 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 199579 = 299369) B299369
theorem B363419 : Blo 155795 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B265207 : Blo 155795 265207 := bstep (se 1 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 265207 = 397811) B397811
theorem B2132993 : Blo 155795 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B527579 : Blo 155795 527579 := bstep (se 1 (by rfl) ⟨395684, by rfl⟩ : syracuseStep 527579 = 791369) B791369
theorem B167131 : Blo 155795 167131 := bstep (se 1 (by rfl) ⟨125348, by rfl⟩ : syracuseStep 167131 = 250697) B250697
theorem B3214583 : Blo 155795 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B265511 : Blo 155795 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B298579 : Blo 155795 298579 := bstep (se 1 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 298579 = 447869) B447869
theorem B5312087 : Blo 155795 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B265963 : Blo 155795 265963 := bstep (se 1 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 265963 = 398945) B398945
theorem B298799 : Blo 155795 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B200495 : Blo 155795 200495 := bstep (se 1 (by rfl) ⟨150371, by rfl⟩ : syracuseStep 200495 = 300743) B300743
theorem B888833 : Blo 155795 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B528443 : Blo 155795 528443 := bstep (se 1 (by rfl) ⟨396332, by rfl⟩ : syracuseStep 528443 = 792665) B792665
theorem B528713 : Blo 155795 528713 := bstep (se 2 (by rfl) ⟨198267, by rfl⟩ : syracuseStep 528713 = 396535) B396535
theorem B233819 : Blo 155795 233819 := bstep (se 1 (by rfl) ⟨175364, by rfl⟩ : syracuseStep 233819 = 350729) B350729
theorem B234047 : Blo 155795 234047 := bstep (se 1 (by rfl) ⟨175535, by rfl⟩ : syracuseStep 234047 = 351071) B351071
theorem B856673 : Blo 155795 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B299695 : Blo 155795 299695 := bstep (se 1 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 299695 = 449543) B449543
theorem B234167 : Blo 155795 234167 := bstep (se 1 (by rfl) ⟨175625, by rfl⟩ : syracuseStep 234167 = 351251) B351251
theorem B266935 : Blo 155795 266935 := bstep (se 1 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 266935 = 400403) B400403
theorem B299855 : Blo 155795 299855 := bstep (se 1 (by rfl) ⟨224891, by rfl⟩ : syracuseStep 299855 = 449783) B449783
theorem B234395 : Blo 155795 234395 := bstep (se 1 (by rfl) ⟨175796, by rfl⟩ : syracuseStep 234395 = 351593) B351593
theorem B267239 : Blo 155795 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B398459 : Blo 155795 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B398479 : Blo 155795 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B2954393 : Blo 155795 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B234791 : Blo 155795 234791 := bstep (se 1 (by rfl) ⟨176093, by rfl⟩ : syracuseStep 234791 = 352187) B352187
theorem B234875 : Blo 155795 234875 := bstep (se 1 (by rfl) ⟨176156, by rfl⟩ : syracuseStep 234875 = 352313) B352313
theorem B169339 : Blo 155795 169339 := bstep (se 1 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 169339 = 254009) B254009
theorem B398753 : Blo 155795 398753 := bstep (se 2 (by rfl) ⟨149532, by rfl⟩ : syracuseStep 398753 = 299065) B299065
theorem B2168257 : Blo 155795 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B333305 : Blo 155795 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B235001 : Blo 155795 235001 := bstep (se 2 (by rfl) ⟨88125, by rfl⟩ : syracuseStep 235001 = 176251) B176251
theorem B235103 : Blo 155795 235103 := bstep (se 1 (by rfl) ⟨176327, by rfl⟩ : syracuseStep 235103 = 352655) B352655
theorem B235319 : Blo 155795 235319 := bstep (se 1 (by rfl) ⟨176489, by rfl⟩ : syracuseStep 235319 = 352979) B352979
theorem B792503 : Blo 155795 792503 := bstep (se 1 (by rfl) ⟨594377, by rfl⟩ : syracuseStep 792503 = 1188755) B1188755
theorem B235625 : Blo 155795 235625 := bstep (se 2 (by rfl) ⟨88359, by rfl⟩ : syracuseStep 235625 = 176719) B176719
theorem B268393 : Blo 155795 268393 := bstep (se 2 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 268393 = 201295) B201295
theorem B235943 : Blo 155795 235943 := bstep (se 1 (by rfl) ⟨176957, by rfl⟩ : syracuseStep 235943 = 353915) B353915
theorem B236027 : Blo 155795 236027 := bstep (se 1 (by rfl) ⟨177020, by rfl⟩ : syracuseStep 236027 = 354041) B354041
theorem B891431 : Blo 155795 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B793151 : Blo 155795 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B301639 : Blo 155795 301639 := bstep (se 1 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 301639 = 452459) B452459
theorem B236153 : Blo 155795 236153 := bstep (se 2 (by rfl) ⟨88557, by rfl⟩ : syracuseStep 236153 = 177115) B177115
theorem B236207 : Blo 155795 236207 := bstep (se 1 (by rfl) ⟨177155, by rfl⟩ : syracuseStep 236207 = 354311) B354311
theorem B236255 : Blo 155795 236255 := bstep (se 1 (by rfl) ⟨177191, by rfl⟩ : syracuseStep 236255 = 354383) B354383
theorem B4266755 : Blo 155795 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B2071439 : Blo 155795 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B236519 : Blo 155795 236519 := bstep (se 1 (by rfl) ⟨177389, by rfl⟩ : syracuseStep 236519 = 354779) B354779
theorem B400423 : Blo 155795 400423 := bstep (se 1 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 400423 = 600635) B600635
theorem B760871 : Blo 155795 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B334945 : Blo 155795 334945 := bstep (se 2 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 334945 = 251209) B251209
theorem B236777 : Blo 155795 236777 := bstep (se 2 (by rfl) ⟨88791, by rfl⟩ : syracuseStep 236777 = 177583) B177583
theorem B236831 : Blo 155795 236831 := bstep (se 1 (by rfl) ⟨177623, by rfl⟩ : syracuseStep 236831 = 355247) B355247
theorem B859423 : Blo 155795 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B531899 : Blo 155795 531899 := bstep (se 1 (by rfl) ⟨398924, by rfl⟩ : syracuseStep 531899 = 797849) B797849
theorem B236999 : Blo 155795 236999 := bstep (se 1 (by rfl) ⟨177749, by rfl⟩ : syracuseStep 236999 = 355499) B355499
theorem B1449431 : Blo 155795 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B400889 : Blo 155795 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B302687 : Blo 155795 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B237353 : Blo 155795 237353 := bstep (se 2 (by rfl) ⟨89007, by rfl⟩ : syracuseStep 237353 = 178015) B178015
theorem B237359 : Blo 155795 237359 := bstep (se 1 (by rfl) ⟨178019, by rfl⟩ : syracuseStep 237359 = 356039) B356039
theorem B401537 : Blo 155795 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B4301009 : Blo 155795 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2433235 : Blo 155795 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B237833 : Blo 155795 237833 := bstep (se 2 (by rfl) ⟨89187, by rfl⟩ : syracuseStep 237833 = 178375) B178375
theorem B237935 : Blo 155795 237935 := bstep (se 1 (by rfl) ⟨178451, by rfl⟩ : syracuseStep 237935 = 356903) B356903
theorem B401831 : Blo 155795 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B238151 : Blo 155795 238151 := bstep (se 1 (by rfl) ⟨178613, by rfl⟩ : syracuseStep 238151 = 357227) B357227
theorem B401993 : Blo 155795 401993 := bstep (se 2 (by rfl) ⟨150747, by rfl⟩ : syracuseStep 401993 = 301495) B301495
theorem B336491 : Blo 155795 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B238187 : Blo 155795 238187 := bstep (se 1 (by rfl) ⟨178640, by rfl⟩ : syracuseStep 238187 = 357281) B357281
theorem B795257 : Blo 155795 795257 := bstep (se 2 (by rfl) ⟨298221, by rfl⟩ : syracuseStep 795257 = 596443) B596443
theorem B271183 : Blo 155795 271183 := bstep (se 1 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 271183 = 406775) B406775
theorem B238415 : Blo 155795 238415 := bstep (se 1 (by rfl) ⟨178811, by rfl⟩ : syracuseStep 238415 = 357623) B357623
theorem B402347 : Blo 155795 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B1516481 : Blo 155795 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1713089 : Blo 155795 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B893915 : Blo 155795 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B762871 : Blo 155795 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B336935 : Blo 155795 336935 := bstep (se 1 (by rfl) ⟨252701, by rfl⟩ : syracuseStep 336935 = 505403) B505403
theorem B402529 : Blo 155795 402529 := bstep (se 2 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 402529 = 301897) B301897
theorem B238811 : Blo 155795 238811 := bstep (se 1 (by rfl) ⟨179108, by rfl⟩ : syracuseStep 238811 = 358217) B358217
theorem B238985 : Blo 155795 238985 := bstep (se 2 (by rfl) ⟨89619, by rfl⟩ : syracuseStep 238985 = 179239) B179239
theorem B239339 : Blo 155795 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B1353617 : Blo 155795 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B239567 : Blo 155795 239567 := bstep (se 1 (by rfl) ⟨179675, by rfl⟩ : syracuseStep 239567 = 359351) B359351
theorem B403481 : Blo 155795 403481 := bstep (se 2 (by rfl) ⟨151305, by rfl⟩ : syracuseStep 403481 = 302611) B302611
theorem B763937 : Blo 155795 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B338131 : Blo 155795 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B600317 : Blo 155795 600317 := bstep (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) B225119
theorem B4696379 : Blo 155795 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B797039 : Blo 155795 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B403937 : Blo 155795 403937 := bstep (se 2 (by rfl) ⟨151476, by rfl⟩ : syracuseStep 403937 = 302953) B302953
theorem B403987 : Blo 155795 403987 := bstep (se 1 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 403987 = 605981) B605981
theorem B666251 : Blo 155795 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B961303 : Blo 155795 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B536057 : Blo 155795 536057 := bstep (se 2 (by rfl) ⟨201021, by rfl⟩ : syracuseStep 536057 = 402043) B402043
theorem B175711 : Blo 155795 175711 := bstep (se 1 (by rfl) ⟨131783, by rfl⟩ : syracuseStep 175711 = 263567) B263567
theorem B634463 : Blo 155795 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B536327 : Blo 155795 536327 := bstep (se 1 (by rfl) ⟨402245, by rfl⟩ : syracuseStep 536327 = 804491) B804491
theorem B569099 : Blo 155795 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B536381 : Blo 155795 536381 := bstep (se 3 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 536381 = 201143) B201143
theorem B3026807 : Blo 155795 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B339977 : Blo 155795 339977 := bstep (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) B254983
theorem B176863 : Blo 155795 176863 := bstep (se 1 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 176863 = 265295) B265295
theorem B340967 : Blo 155795 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B603233 : Blo 155795 603233 := bstep (se 2 (by rfl) ⟨226212, by rfl⟩ : syracuseStep 603233 = 452425) B452425
theorem B1717393 : Blo 155795 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B177439 : Blo 155795 177439 := bstep (se 1 (by rfl) ⟨133079, by rfl⟩ : syracuseStep 177439 = 266159) B266159
theorem B177727 : Blo 155795 177727 := bstep (se 1 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 177727 = 266591) B266591
theorem B800441 : Blo 155795 800441 := bstep (se 2 (by rfl) ⟨300165, by rfl⟩ : syracuseStep 800441 = 600331) B600331
theorem B505531 : Blo 155795 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B571217 : Blo 155795 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B571373 : Blo 155795 571373 := bstep (se 3 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 571373 = 214265) B214265
theorem B375131 : Blo 155795 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B375151 : Blo 155795 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B178555 : Blo 155795 178555 := bstep (se 1 (by rfl) ⟨133916, by rfl⟩ : syracuseStep 178555 = 267833) B267833
theorem B539243 : Blo 155795 539243 := bstep (se 1 (by rfl) ⟨404432, by rfl⟩ : syracuseStep 539243 = 808865) B808865
theorem B9616157 : Blo 155795 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B179023 : Blo 155795 179023 := bstep (se 1 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 179023 = 268535) B268535
theorem B670589 : Blo 155795 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B5160023 : Blo 155795 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B179419 : Blo 155795 179419 := bstep (se 1 (by rfl) ⟨134564, by rfl⟩ : syracuseStep 179419 = 269129) B269129
theorem B179707 : Blo 155795 179707 := bstep (se 1 (by rfl) ⟨134780, by rfl⟩ : syracuseStep 179707 = 269561) B269561
theorem B2866747 : Blo 155795 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B802385 : Blo 155795 802385 := bstep (se 2 (by rfl) ⟨300894, by rfl⟩ : syracuseStep 802385 = 601789) B601789
theorem B671341 : Blo 155795 671341 := bstep (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) B251753
theorem B638777 : Blo 155795 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B11583755 : Blo 155795 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B541019 : Blo 155795 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B869063 : Blo 155795 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B1426369 : Blo 155795 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1000451 : Blo 155795 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B1623233 : Blo 155795 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B541895 : Blo 155795 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B903095 : Blo 155795 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B804815 : Blo 155795 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B379513 : Blo 155795 379513 := bstep (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) B284635
theorem B903869 : Blo 155795 903869 := bstep (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) B338951
theorem B379667 : Blo 155795 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B1526663 : Blo 155795 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B805787 : Blo 155795 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B806273 : Blo 155795 806273 := bstep (se 2 (by rfl) ⟨302352, by rfl⟩ : syracuseStep 806273 = 604705) B604705
theorem B1429001 : Blo 155795 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1101523 : Blo 155795 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B806921 : Blo 155795 806921 := bstep (se 2 (by rfl) ⟨302595, by rfl⟩ : syracuseStep 806921 = 605191) B605191
theorem B807083 : Blo 155795 807083 := bstep (se 1 (by rfl) ⟨605312, by rfl⟩ : syracuseStep 807083 = 1210625) B1210625
theorem B807259 : Blo 155795 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B905579 : Blo 155795 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B807569 : Blo 155795 807569 := bstep (se 2 (by rfl) ⟨302838, by rfl⟩ : syracuseStep 807569 = 605677) B605677
theorem B250543 : Blo 155795 250543 := bstep (se 1 (by rfl) ⟨187907, by rfl⟩ : syracuseStep 250543 = 375815) B375815
theorem B644041 : Blo 155795 644041 := bstep (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) B483031
theorem B51958745 : Blo 155795 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B906329 : Blo 155795 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B283943 : Blo 155795 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B1332773 : Blo 155795 1332773 := bstep (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) B249895
theorem B907037 : Blo 155795 907037 := bstep (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) B340139
theorem B350639 : Blo 155795 350639 := bstep (se 1 (by rfl) ⟨262979, by rfl⟩ : syracuseStep 350639 = 525959) B525959
theorem B1497527 : Blo 155795 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B350675 : Blo 155795 350675 := bstep (se 1 (by rfl) ⟨263006, by rfl⟩ : syracuseStep 350675 = 526013) B526013
theorem B350783 : Blo 155795 350783 := bstep (se 1 (by rfl) ⟨263087, by rfl⟩ : syracuseStep 350783 = 526175) B526175
theorem B383609 : Blo 155795 383609 := bstep (se 2 (by rfl) ⟨143853, by rfl⟩ : syracuseStep 383609 = 287707) B287707
theorem B350891 : Blo 155795 350891 := bstep (se 1 (by rfl) ⟨263168, by rfl⟩ : syracuseStep 350891 = 526337) B526337
theorem B383887 : Blo 155795 383887 := bstep (se 1 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 383887 = 575831) B575831
theorem B449725 : Blo 155795 449725 := bstep (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) B168647
theorem B351431 : Blo 155795 351431 := bstep (se 1 (by rfl) ⟨263573, by rfl⟩ : syracuseStep 351431 = 527147) B527147
theorem B351611 : Blo 155795 351611 := bstep (se 1 (by rfl) ⟨263708, by rfl⟩ : syracuseStep 351611 = 527417) B527417
theorem B351737 : Blo 155795 351737 := bstep (se 2 (by rfl) ⟨131901, by rfl⟩ : syracuseStep 351737 = 263803) B263803
theorem B351827 : Blo 155795 351827 := bstep (se 1 (by rfl) ⟨263870, by rfl⟩ : syracuseStep 351827 = 527741) B527741
theorem B253675 : Blo 155795 253675 := bstep (se 1 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 253675 = 380513) B380513
theorem B352007 : Blo 155795 352007 := bstep (se 1 (by rfl) ⟨264005, by rfl⟩ : syracuseStep 352007 = 528011) B528011
theorem B1400851 : Blo 155795 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B2187383 : Blo 155795 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B680089 : Blo 155795 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B155935 : Blo 155795 155935 := bstep (se 1 (by rfl) ⟨116951, by rfl⟩ : syracuseStep 155935 = 233903) B233903
theorem B4645181 : Blo 155795 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B155995 : Blo 155795 155995 := bstep (se 1 (by rfl) ⟨116996, by rfl⟩ : syracuseStep 155995 = 233993) B233993
theorem B352619 : Blo 155795 352619 := bstep (se 1 (by rfl) ⟨264464, by rfl⟩ : syracuseStep 352619 = 528929) B528929
theorem B156015 : Blo 155795 156015 := bstep (se 1 (by rfl) ⟨117011, by rfl⟩ : syracuseStep 156015 = 234023) B234023
theorem B156071 : Blo 155795 156071 := bstep (se 1 (by rfl) ⟨117053, by rfl⟩ : syracuseStep 156071 = 234107) B234107
theorem B319955 : Blo 155795 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B156155 : Blo 155795 156155 := bstep (se 1 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 156155 = 234233) B234233
theorem B352763 : Blo 155795 352763 := bstep (se 1 (by rfl) ⟨264572, by rfl⟩ : syracuseStep 352763 = 529145) B529145
theorem B1008139 : Blo 155795 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B156223 : Blo 155795 156223 := bstep (se 1 (by rfl) ⟨117167, by rfl⟩ : syracuseStep 156223 = 234335) B234335
theorem B156231 : Blo 155795 156231 := bstep (se 1 (by rfl) ⟨117173, by rfl⟩ : syracuseStep 156231 = 234347) B234347
theorem B352889 : Blo 155795 352889 := bstep (se 2 (by rfl) ⟨132333, by rfl⟩ : syracuseStep 352889 = 264667) B264667
theorem B713369 : Blo 155795 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B352943 : Blo 155795 352943 := bstep (se 1 (by rfl) ⟨264707, by rfl⟩ : syracuseStep 352943 = 529415) B529415
theorem B156383 : Blo 155795 156383 := bstep (se 1 (by rfl) ⟨117287, by rfl⟩ : syracuseStep 156383 = 234575) B234575
theorem B353015 : Blo 155795 353015 := bstep (se 1 (by rfl) ⟨264761, by rfl⟩ : syracuseStep 353015 = 529523) B529523
theorem B156463 : Blo 155795 156463 := bstep (se 1 (by rfl) ⟨117347, by rfl⟩ : syracuseStep 156463 = 234695) B234695
theorem B156571 : Blo 155795 156571 := bstep (se 1 (by rfl) ⟨117428, by rfl⟩ : syracuseStep 156571 = 234857) B234857
theorem B353195 : Blo 155795 353195 := bstep (se 1 (by rfl) ⟨264896, by rfl⟩ : syracuseStep 353195 = 529793) B529793
theorem B156623 : Blo 155795 156623 := bstep (se 1 (by rfl) ⟨117467, by rfl⟩ : syracuseStep 156623 = 234935) B234935
theorem B156647 : Blo 155795 156647 := bstep (se 1 (by rfl) ⟨117485, by rfl⟩ : syracuseStep 156647 = 234971) B234971
theorem B1631431 : Blo 155795 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B156959 : Blo 155795 156959 := bstep (se 1 (by rfl) ⟨117719, by rfl⟩ : syracuseStep 156959 = 235439) B235439
theorem B157019 : Blo 155795 157019 := bstep (se 1 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 157019 = 235529) B235529
theorem B157039 : Blo 155795 157039 := bstep (se 1 (by rfl) ⟨117779, by rfl⟩ : syracuseStep 157039 = 235559) B235559
theorem B157095 : Blo 155795 157095 := bstep (se 1 (by rfl) ⟨117821, by rfl⟩ : syracuseStep 157095 = 235643) B235643
theorem B353735 : Blo 155795 353735 := bstep (se 1 (by rfl) ⟨265301, by rfl⟩ : syracuseStep 353735 = 530603) B530603
theorem B255431 : Blo 155795 255431 := bstep (se 1 (by rfl) ⟨191573, by rfl⟩ : syracuseStep 255431 = 383147) B383147
theorem B157179 : Blo 155795 157179 := bstep (se 1 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 157179 = 235769) B235769
theorem B157247 : Blo 155795 157247 := bstep (se 1 (by rfl) ⟨117935, by rfl⟩ : syracuseStep 157247 = 235871) B235871
theorem B157255 : Blo 155795 157255 := bstep (se 1 (by rfl) ⟨117941, by rfl⟩ : syracuseStep 157255 = 235883) B235883
theorem B157407 : Blo 155795 157407 := bstep (se 1 (by rfl) ⟨118055, by rfl⟩ : syracuseStep 157407 = 236111) B236111
theorem B354095 : Blo 155795 354095 := bstep (se 1 (by rfl) ⟨265571, by rfl⟩ : syracuseStep 354095 = 531143) B531143
theorem B157487 : Blo 155795 157487 := bstep (se 1 (by rfl) ⟨118115, by rfl⟩ : syracuseStep 157487 = 236231) B236231
theorem B255799 : Blo 155795 255799 := bstep (se 1 (by rfl) ⟨191849, by rfl⟩ : syracuseStep 255799 = 383699) B383699
theorem B157595 : Blo 155795 157595 := bstep (se 1 (by rfl) ⟨118196, by rfl⟩ : syracuseStep 157595 = 236393) B236393
theorem B157647 : Blo 155795 157647 := bstep (se 1 (by rfl) ⟨118235, by rfl⟩ : syracuseStep 157647 = 236471) B236471
theorem B157671 : Blo 155795 157671 := bstep (se 1 (by rfl) ⟨118253, by rfl⟩ : syracuseStep 157671 = 236507) B236507
theorem B157983 : Blo 155795 157983 := bstep (se 1 (by rfl) ⟨118487, by rfl⟩ : syracuseStep 157983 = 236975) B236975
theorem B158043 : Blo 155795 158043 := bstep (se 1 (by rfl) ⟨118532, by rfl⟩ : syracuseStep 158043 = 237065) B237065
theorem B354671 : Blo 155795 354671 := bstep (se 1 (by rfl) ⟨266003, by rfl⟩ : syracuseStep 354671 = 532007) B532007
theorem B158063 : Blo 155795 158063 := bstep (se 1 (by rfl) ⟨118547, by rfl⟩ : syracuseStep 158063 = 237095) B237095
theorem B158119 : Blo 155795 158119 := bstep (se 1 (by rfl) ⟨118589, by rfl⟩ : syracuseStep 158119 = 237179) B237179
theorem B2681261 : Blo 155795 2681261 := bstep (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) B1005473
theorem B354743 : Blo 155795 354743 := bstep (se 1 (by rfl) ⟨266057, by rfl⟩ : syracuseStep 354743 = 532115) B532115
theorem B158203 : Blo 155795 158203 := bstep (se 1 (by rfl) ⟨118652, by rfl⟩ : syracuseStep 158203 = 237305) B237305
theorem B158271 : Blo 155795 158271 := bstep (se 1 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 158271 = 237407) B237407
theorem B354887 : Blo 155795 354887 := bstep (se 1 (by rfl) ⟨266165, by rfl⟩ : syracuseStep 354887 = 532331) B532331
theorem B158279 : Blo 155795 158279 := bstep (se 1 (by rfl) ⟨118709, by rfl⟩ : syracuseStep 158279 = 237419) B237419
theorem B1075799 : Blo 155795 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B354923 : Blo 155795 354923 := bstep (se 1 (by rfl) ⟨266192, by rfl⟩ : syracuseStep 354923 = 532385) B532385
theorem B158431 : Blo 155795 158431 := bstep (se 1 (by rfl) ⟨118823, by rfl⟩ : syracuseStep 158431 = 237647) B237647
theorem B158511 : Blo 155795 158511 := bstep (se 1 (by rfl) ⟨118883, by rfl⟩ : syracuseStep 158511 = 237767) B237767
theorem B158619 : Blo 155795 158619 := bstep (se 1 (by rfl) ⟨118964, by rfl⟩ : syracuseStep 158619 = 237929) B237929
theorem B158671 : Blo 155795 158671 := bstep (se 1 (by rfl) ⟨119003, by rfl⟩ : syracuseStep 158671 = 238007) B238007
theorem B158695 : Blo 155795 158695 := bstep (se 1 (by rfl) ⟨119021, by rfl⟩ : syracuseStep 158695 = 238043) B238043
theorem B355319 : Blo 155795 355319 := bstep (se 1 (by rfl) ⟨266489, by rfl⟩ : syracuseStep 355319 = 532979) B532979
theorem B683275 : Blo 155795 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B159007 : Blo 155795 159007 := bstep (se 1 (by rfl) ⟨119255, by rfl⟩ : syracuseStep 159007 = 238511) B238511
theorem B159067 : Blo 155795 159067 := bstep (se 1 (by rfl) ⟨119300, by rfl⟩ : syracuseStep 159067 = 238601) B238601
theorem B355679 : Blo 155795 355679 := bstep (se 1 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 355679 = 533519) B533519
theorem B159087 : Blo 155795 159087 := bstep (se 1 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 159087 = 238631) B238631
theorem B224635 : Blo 155795 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B159143 : Blo 155795 159143 := bstep (se 1 (by rfl) ⟨119357, by rfl⟩ : syracuseStep 159143 = 238715) B238715
theorem B159227 : Blo 155795 159227 := bstep (se 1 (by rfl) ⟨119420, by rfl⟩ : syracuseStep 159227 = 238841) B238841
theorem B650767 : Blo 155795 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B159295 : Blo 155795 159295 := bstep (se 1 (by rfl) ⟨119471, by rfl⟩ : syracuseStep 159295 = 238943) B238943
theorem B159303 : Blo 155795 159303 := bstep (se 1 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 159303 = 238955) B238955
theorem B159455 : Blo 155795 159455 := bstep (se 1 (by rfl) ⟨119591, by rfl⟩ : syracuseStep 159455 = 239183) B239183
theorem B356075 : Blo 155795 356075 := bstep (se 1 (by rfl) ⟨267056, by rfl⟩ : syracuseStep 356075 = 534113) B534113
theorem B4484845 : Blo 155795 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B159535 : Blo 155795 159535 := bstep (se 1 (by rfl) ⟨119651, by rfl⟩ : syracuseStep 159535 = 239303) B239303
theorem B356201 : Blo 155795 356201 := bstep (se 2 (by rfl) ⟨133575, by rfl⟩ : syracuseStep 356201 = 267151) B267151
theorem B159643 : Blo 155795 159643 := bstep (se 1 (by rfl) ⟨119732, by rfl⟩ : syracuseStep 159643 = 239465) B239465
theorem B159695 : Blo 155795 159695 := bstep (se 1 (by rfl) ⟨119771, by rfl⟩ : syracuseStep 159695 = 239543) B239543
theorem B159719 : Blo 155795 159719 := bstep (se 1 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 159719 = 239579) B239579
theorem B1044481 : Blo 155795 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B1503289 : Blo 155795 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B160091 : Blo 155795 160091 := bstep (se 1 (by rfl) ⟨120068, by rfl⟩ : syracuseStep 160091 = 240137) B240137
theorem B3469873 : Blo 155795 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B2224691 : Blo 155795 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B357047 : Blo 155795 357047 := bstep (se 1 (by rfl) ⟨267785, by rfl⟩ : syracuseStep 357047 = 535571) B535571
theorem B1209167 : Blo 155795 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B357263 : Blo 155795 357263 := bstep (se 1 (by rfl) ⟨267947, by rfl⟩ : syracuseStep 357263 = 535895) B535895
theorem B848933 : Blo 155795 848933 := bstep (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) B159175
theorem B1340495 : Blo 155795 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B357983 : Blo 155795 357983 := bstep (se 1 (by rfl) ⟨268487, by rfl⟩ : syracuseStep 357983 = 536975) B536975
theorem B358199 : Blo 155795 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B358505 : Blo 155795 358505 := bstep (se 2 (by rfl) ⟨134439, by rfl⟩ : syracuseStep 358505 = 268879) B268879
theorem B1440089 : Blo 155795 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B2587085 : Blo 155795 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B457289 : Blo 155795 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B358991 : Blo 155795 358991 := bstep (se 1 (by rfl) ⟨269243, by rfl⟩ : syracuseStep 358991 = 538487) B538487
theorem B359135 : Blo 155795 359135 := bstep (se 1 (by rfl) ⟨269351, by rfl⟩ : syracuseStep 359135 = 538703) B538703
theorem B359387 : Blo 155795 359387 := bstep (se 1 (by rfl) ⟨269540, by rfl⟩ : syracuseStep 359387 = 539081) B539081
theorem B425159 : Blo 155795 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B1146383 : Blo 155795 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B1867801 : Blo 155795 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B3244313 : Blo 155795 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B5833021 : Blo 155795 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B1344185 : Blo 155795 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B262919 : Blo 155795 262919 := bstep (se 1 (by rfl) ⟨197189, by rfl⟩ : syracuseStep 262919 = 394379) B394379
theorem B1082155 : Blo 155795 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B1442717 : Blo 155795 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B361577 : Blo 155795 361577 := bstep (se 2 (by rfl) ⟨135591, by rfl⟩ : syracuseStep 361577 = 271183) B271183
theorem B853213 : Blo 155795 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B1901825 : Blo 155795 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B1017161 : Blo 155795 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B591583 : Blo 155795 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B526121 : Blo 155795 526121 := bstep (se 2 (by rfl) ⟨197295, by rfl⟩ : syracuseStep 526121 = 394591) B394591
theorem B263999 : Blo 155795 263999 := bstep (se 1 (by rfl) ⟨197999, by rfl⟩ : syracuseStep 263999 = 395999) B395999
theorem B264073 : Blo 155795 264073 := bstep (se 2 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 264073 = 198055) B198055
theorem B1017775 : Blo 155795 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B395513 : Blo 155795 395513 := bstep (se 2 (by rfl) ⟨148317, by rfl⟩ : syracuseStep 395513 = 296635) B296635
theorem B264505 : Blo 155795 264505 := bstep (se 2 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 264505 = 198379) B198379
theorem B952667 : Blo 155795 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B3541391 : Blo 155795 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B199199 : Blo 155795 199199 := bstep (se 1 (by rfl) ⟨149399, by rfl⟩ : syracuseStep 199199 = 298799) B298799
theorem B264809 : Blo 155795 264809 := bstep (se 2 (by rfl) ⟨99303, by rfl⟩ : syracuseStep 264809 = 198607) B198607
theorem B592555 : Blo 155795 592555 := bstep (se 1 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 592555 = 888833) B888833
theorem B36637717 : Blo 155795 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B1445053 : Blo 155795 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B199903 : Blo 155795 199903 := bstep (se 1 (by rfl) ⟨149927, by rfl⟩ : syracuseStep 199903 = 299855) B299855
theorem B34639163 : Blo 155795 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B265639 : Blo 155795 265639 := bstep (se 1 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 265639 = 398459) B398459
theorem B1969595 : Blo 155795 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B757181 : Blo 155795 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B265801 : Blo 155795 265801 := bstep (se 2 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 265801 = 199351) B199351
theorem B265835 : Blo 155795 265835 := bstep (se 1 (by rfl) ⟨199376, by rfl⟩ : syracuseStep 265835 = 398753) B398753
theorem B1707637 : Blo 155795 1707637 := bstep (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) B160091
theorem B888515 : Blo 155795 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B1281737 : Blo 155795 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B266105 : Blo 155795 266105 := bstep (se 2 (by rfl) ⟨99789, by rfl⟩ : syracuseStep 266105 = 199579) B199579
theorem B528335 : Blo 155795 528335 := bstep (se 1 (by rfl) ⟨396251, by rfl⟩ : syracuseStep 528335 = 792503) B792503
theorem B233759 : Blo 155795 233759 := bstep (se 1 (by rfl) ⟨175319, by rfl⟩ : syracuseStep 233759 = 350639) B350639
theorem B233783 : Blo 155795 233783 := bstep (se 1 (by rfl) ⟨175337, by rfl⟩ : syracuseStep 233783 = 350675) B350675
theorem B594287 : Blo 155795 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B233855 : Blo 155795 233855 := bstep (se 1 (by rfl) ⟨175391, by rfl⟩ : syracuseStep 233855 = 350783) B350783
theorem B528767 : Blo 155795 528767 := bstep (se 1 (by rfl) ⟨396575, by rfl⟩ : syracuseStep 528767 = 793151) B793151
theorem B233927 : Blo 155795 233927 := bstep (se 1 (by rfl) ⟨175445, by rfl⟩ : syracuseStep 233927 = 350891) B350891
theorem B299513 : Blo 155795 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B1380959 : Blo 155795 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B398105 : Blo 155795 398105 := bstep (se 2 (by rfl) ⟨149289, by rfl⟩ : syracuseStep 398105 = 298579) B298579
theorem B234281 : Blo 155795 234281 := bstep (se 2 (by rfl) ⟨87855, by rfl⟩ : syracuseStep 234281 = 175711) B175711
theorem B234287 : Blo 155795 234287 := bstep (se 1 (by rfl) ⟨175715, by rfl⟩ : syracuseStep 234287 = 351431) B351431
theorem B234407 : Blo 155795 234407 := bstep (se 1 (by rfl) ⟨175805, by rfl⟩ : syracuseStep 234407 = 351611) B351611
theorem B234491 : Blo 155795 234491 := bstep (se 1 (by rfl) ⟨175868, by rfl⟩ : syracuseStep 234491 = 351737) B351737
theorem B267259 : Blo 155795 267259 := bstep (se 1 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 267259 = 400889) B400889
theorem B234551 : Blo 155795 234551 := bstep (se 1 (by rfl) ⟨175913, by rfl⟩ : syracuseStep 234551 = 351827) B351827
theorem B201791 : Blo 155795 201791 := bstep (se 1 (by rfl) ⟨151343, by rfl⟩ : syracuseStep 201791 = 302687) B302687
theorem B234671 : Blo 155795 234671 := bstep (se 1 (by rfl) ⟨176003, by rfl⟩ : syracuseStep 234671 = 352007) B352007
theorem B2004385 : Blo 155795 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B267691 : Blo 155795 267691 := bstep (se 1 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 267691 = 401537) B401537
theorem B235079 : Blo 155795 235079 := bstep (se 1 (by rfl) ⟨176309, by rfl⟩ : syracuseStep 235079 = 352619) B352619
theorem B267887 : Blo 155795 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B235175 : Blo 155795 235175 := bstep (se 1 (by rfl) ⟨176381, by rfl⟩ : syracuseStep 235175 = 352763) B352763
theorem B267995 : Blo 155795 267995 := bstep (se 1 (by rfl) ⟨200996, by rfl⟩ : syracuseStep 267995 = 401993) B401993
theorem B235259 : Blo 155795 235259 := bstep (se 1 (by rfl) ⟨176444, by rfl⟩ : syracuseStep 235259 = 352889) B352889
theorem B530171 : Blo 155795 530171 := bstep (se 1 (by rfl) ⟨397628, by rfl⟩ : syracuseStep 530171 = 795257) B795257
theorem B235295 : Blo 155795 235295 := bstep (se 1 (by rfl) ⟨176471, by rfl⟩ : syracuseStep 235295 = 352943) B352943
theorem B235343 : Blo 155795 235343 := bstep (se 1 (by rfl) ⟨176507, by rfl⟩ : syracuseStep 235343 = 353015) B353015
theorem B530333 : Blo 155795 530333 := bstep (se 3 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 530333 = 198875) B198875
theorem B235463 : Blo 155795 235463 := bstep (se 1 (by rfl) ⟨176597, by rfl⟩ : syracuseStep 235463 = 353195) B353195
theorem B268231 : Blo 155795 268231 := bstep (se 1 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 268231 = 402347) B402347
theorem B595943 : Blo 155795 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B4626497 : Blo 155795 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B334057 : Blo 155795 334057 := bstep (se 2 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 334057 = 250543) B250543
theorem B399593 : Blo 155795 399593 := bstep (se 2 (by rfl) ⟨149847, by rfl⟩ : syracuseStep 399593 = 299695) B299695
theorem B235817 : Blo 155795 235817 := bstep (se 2 (by rfl) ⟨88431, by rfl⟩ : syracuseStep 235817 = 176863) B176863
theorem B235823 : Blo 155795 235823 := bstep (se 1 (by rfl) ⟨176867, by rfl⟩ : syracuseStep 235823 = 353735) B353735
theorem B236063 : Blo 155795 236063 := bstep (se 1 (by rfl) ⟨177047, by rfl⟩ : syracuseStep 236063 = 354095) B354095
theorem B858721 : Blo 155795 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B268987 : Blo 155795 268987 := bstep (se 1 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 268987 = 403481) B403481
theorem B400211 : Blo 155795 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B531305 : Blo 155795 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B531359 : Blo 155795 531359 := bstep (se 1 (by rfl) ⟨398519, by rfl⟩ : syracuseStep 531359 = 797039) B797039
theorem B236447 : Blo 155795 236447 := bstep (se 1 (by rfl) ⟨177335, by rfl⟩ : syracuseStep 236447 = 354671) B354671
theorem B236495 : Blo 155795 236495 := bstep (se 1 (by rfl) ⟨177371, by rfl⟩ : syracuseStep 236495 = 354743) B354743
theorem B269291 : Blo 155795 269291 := bstep (se 1 (by rfl) ⟨201968, by rfl⟩ : syracuseStep 269291 = 403937) B403937
theorem B236585 : Blo 155795 236585 := bstep (se 2 (by rfl) ⟨88719, by rfl⟩ : syracuseStep 236585 = 177439) B177439
theorem B236591 : Blo 155795 236591 := bstep (se 1 (by rfl) ⟨177443, by rfl⟩ : syracuseStep 236591 = 354887) B354887
theorem B236615 : Blo 155795 236615 := bstep (se 1 (by rfl) ⟨177461, by rfl⟩ : syracuseStep 236615 = 354923) B354923
theorem B2891009 : Blo 155795 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B236879 : Blo 155795 236879 := bstep (se 1 (by rfl) ⟨177659, by rfl⟩ : syracuseStep 236879 = 355319) B355319
theorem B236969 : Blo 155795 236969 := bstep (se 2 (by rfl) ⟨88863, by rfl⟩ : syracuseStep 236969 = 177727) B177727
theorem B237119 : Blo 155795 237119 := bstep (se 1 (by rfl) ⟨177839, by rfl⟩ : syracuseStep 237119 = 355679) B355679
theorem B237383 : Blo 155795 237383 := bstep (se 1 (by rfl) ⟨178037, by rfl⟩ : syracuseStep 237383 = 356075) B356075
theorem B237467 : Blo 155795 237467 := bstep (se 1 (by rfl) ⟨178100, by rfl⟩ : syracuseStep 237467 = 356201) B356201
theorem B1483127 : Blo 155795 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B238031 : Blo 155795 238031 := bstep (se 1 (by rfl) ⟨178523, by rfl⟩ : syracuseStep 238031 = 357047) B357047
theorem B500201 : Blo 155795 500201 := bstep (se 2 (by rfl) ⟨187575, by rfl⟩ : syracuseStep 500201 = 375151) B375151
theorem B238073 : Blo 155795 238073 := bstep (se 2 (by rfl) ⟨89277, by rfl⟩ : syracuseStep 238073 = 178555) B178555
theorem B238175 : Blo 155795 238175 := bstep (se 1 (by rfl) ⟨178631, by rfl⟩ : syracuseStep 238175 = 357263) B357263
theorem B565955 : Blo 155795 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B893663 : Blo 155795 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B402155 : Blo 155795 402155 := bstep (se 1 (by rfl) ⟨301616, by rfl⟩ : syracuseStep 402155 = 603233) B603233
theorem B402185 : Blo 155795 402185 := bstep (se 2 (by rfl) ⟨150819, by rfl⟩ : syracuseStep 402185 = 301639) B301639
theorem B238655 : Blo 155795 238655 := bstep (se 1 (by rfl) ⟨178991, by rfl⟩ : syracuseStep 238655 = 357983) B357983
theorem B238697 : Blo 155795 238697 := bstep (se 2 (by rfl) ⟨89511, by rfl⟩ : syracuseStep 238697 = 179023) B179023
theorem B533627 : Blo 155795 533627 := bstep (se 1 (by rfl) ⟨400220, by rfl⟩ : syracuseStep 533627 = 800441) B800441
theorem B238799 : Blo 155795 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B1352933 : Blo 155795 1352933 := bstep (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) B253675
theorem B533897 : Blo 155795 533897 := bstep (se 2 (by rfl) ⟨200211, by rfl⟩ : syracuseStep 533897 = 400423) B400423
theorem B239003 : Blo 155795 239003 := bstep (se 1 (by rfl) ⟨179252, by rfl⟩ : syracuseStep 239003 = 358505) B358505
theorem B960059 : Blo 155795 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599633 : Blo 155795 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B239225 : Blo 155795 239225 := bstep (se 2 (by rfl) ⟨89709, by rfl⟩ : syracuseStep 239225 = 179419) B179419
theorem B304859 : Blo 155795 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B239327 : Blo 155795 239327 := bstep (se 1 (by rfl) ⟨179495, by rfl⟩ : syracuseStep 239327 = 358991) B358991
theorem B239423 : Blo 155795 239423 := bstep (se 1 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 239423 = 359135) B359135
theorem B239591 : Blo 155795 239591 := bstep (se 1 (by rfl) ⟨179693, by rfl⟩ : syracuseStep 239591 = 359387) B359387
theorem B239609 : Blo 155795 239609 := bstep (se 2 (by rfl) ⟨89853, by rfl⟩ : syracuseStep 239609 = 179707) B179707
theorem B534653 : Blo 155795 534653 := bstep (se 3 (by rfl) ⟨100247, by rfl⟩ : syracuseStep 534653 = 200495) B200495
theorem B895121 : Blo 155795 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B764255 : Blo 155795 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B534923 : Blo 155795 534923 := bstep (se 1 (by rfl) ⟨401192, by rfl⟩ : syracuseStep 534923 = 802385) B802385
theorem B666967 : Blo 155795 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B602063 : Blo 155795 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B536543 : Blo 155795 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B536705 : Blo 155795 536705 := bstep (se 2 (by rfl) ⟨201264, by rfl⟩ : syracuseStep 536705 = 402529) B402529
theorem B569531 : Blo 155795 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B176359 : Blo 155795 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B602579 : Blo 155795 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B537191 : Blo 155795 537191 := bstep (se 1 (by rfl) ⟨402893, by rfl⟩ : syracuseStep 537191 = 805787) B805787
theorem B242279 : Blo 155795 242279 := bstep (se 1 (by rfl) ⟨181709, by rfl⟩ : syracuseStep 242279 = 363419) B363419
theorem B1421995 : Blo 155795 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B2143055 : Blo 155795 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B177007 : Blo 155795 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B537515 : Blo 155795 537515 := bstep (se 1 (by rfl) ⟨403136, by rfl⟩ : syracuseStep 537515 = 806273) B806273
theorem B341065 : Blo 155795 341065 := bstep (se 2 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 341065 = 255799) B255799
theorem B537947 : Blo 155795 537947 := bstep (se 1 (by rfl) ⟨403460, by rfl⟩ : syracuseStep 537947 = 806921) B806921
theorem B538055 : Blo 155795 538055 := bstep (se 1 (by rfl) ⟨403541, by rfl⟩ : syracuseStep 538055 = 807083) B807083
theorem B603719 : Blo 155795 603719 := bstep (se 1 (by rfl) ⟨452789, by rfl⟩ : syracuseStep 603719 = 905579) B905579
theorem B571115 : Blo 155795 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B538379 : Blo 155795 538379 := bstep (se 1 (by rfl) ⟨403784, by rfl⟩ : syracuseStep 538379 = 807569) B807569
theorem B178159 : Blo 155795 178159 := bstep (se 1 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 178159 = 267239) B267239
theorem B538649 : Blo 155795 538649 := bstep (se 2 (by rfl) ⟨201993, by rfl⟩ : syracuseStep 538649 = 403987) B403987
theorem B604219 : Blo 155795 604219 := bstep (se 1 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 604219 = 906329) B906329
theorem B506017 : Blo 155795 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B604691 : Blo 155795 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B998351 : Blo 155795 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B867689 : Blo 155795 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B1523245 : Blo 155795 1523245 := bstep (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) B571217
theorem B966287 : Blo 155795 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B5979793 : Blo 155795 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B1392641 : Blo 155795 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B2867339 : Blo 155795 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B3096787 : Blo 155795 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B475579 : Blo 155795 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B1000349 : Blo 155795 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B8700965 : Blo 155795 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B902411 : Blo 155795 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B509291 : Blo 155795 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B3130919 : Blo 155795 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2868797 : Blo 155795 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1787507 : Blo 155795 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B444167 : Blo 155795 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B674041 : Blo 155795 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B379399 : Blo 155795 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B2017871 : Blo 155795 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B806111 : Blo 155795 806111 := bstep (se 1 (by rfl) ⟨604583, by rfl⟩ : syracuseStep 806111 = 1209167) B1209167
theorem B511849 : Blo 155795 511849 := bstep (se 2 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 511849 = 383887) B383887
theorem B380915 : Blo 155795 380915 := bstep (se 1 (by rfl) ⟨285686, by rfl⟩ : syracuseStep 380915 = 571373) B571373
theorem B446593 : Blo 155795 446593 := bstep (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) B334945
theorem B1724723 : Blo 155795 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B6410771 : Blo 155795 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B447059 : Blo 155795 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B3822329 : Blo 155795 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B283439 : Blo 155795 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B808379 : Blo 155795 808379 := bstep (se 1 (by rfl) ⟨606284, by rfl⟩ : syracuseStep 808379 = 1212569) B1212569
theorem B7722503 : Blo 155795 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B906785 : Blo 155795 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B218911 : Blo 155795 218911 := bstep (se 1 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 218911 = 328367) B328367
theorem B1923047 : Blo 155795 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B613021 : Blo 155795 613021 := bstep (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) B229883
theorem B1071863 : Blo 155795 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B1924013 : Blo 155795 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B2317501 : Blo 155795 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B351719 : Blo 155795 351719 := bstep (se 1 (by rfl) ⟨263789, by rfl⟩ : syracuseStep 351719 = 527579) B527579
theorem B909245 : Blo 155795 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B352295 : Blo 155795 352295 := bstep (se 1 (by rfl) ⟨264221, by rfl⟩ : syracuseStep 352295 = 528443) B528443
theorem B352475 : Blo 155795 352475 := bstep (se 1 (by rfl) ⟨264356, by rfl⟩ : syracuseStep 352475 = 528713) B528713
theorem B155879 : Blo 155795 155879 := bstep (se 1 (by rfl) ⟨116909, by rfl⟩ : syracuseStep 155879 = 233819) B233819
theorem B450841 : Blo 155795 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B156031 : Blo 155795 156031 := bstep (se 1 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 156031 = 234047) B234047
theorem B156111 : Blo 155795 156111 := bstep (se 1 (by rfl) ⟨117083, by rfl⟩ : syracuseStep 156111 = 234167) B234167
theorem B352745 : Blo 155795 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B156263 : Blo 155795 156263 := bstep (se 1 (by rfl) ⟨117197, by rfl⟩ : syracuseStep 156263 = 234395) B234395
theorem B353033 : Blo 155795 353033 := bstep (se 2 (by rfl) ⟨132387, by rfl⟩ : syracuseStep 353033 = 264775) B264775
theorem B156527 : Blo 155795 156527 := bstep (se 1 (by rfl) ⟨117395, by rfl⟩ : syracuseStep 156527 = 234791) B234791
theorem B156583 : Blo 155795 156583 := bstep (se 1 (by rfl) ⟨117437, by rfl⟩ : syracuseStep 156583 = 234875) B234875
theorem B222203 : Blo 155795 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B156667 : Blo 155795 156667 := bstep (se 1 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 156667 = 235001) B235001
theorem B156735 : Blo 155795 156735 := bstep (se 1 (by rfl) ⟨117551, by rfl⟩ : syracuseStep 156735 = 235103) B235103
theorem B681149 : Blo 155795 681149 := bstep (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) B255431
theorem B156879 : Blo 155795 156879 := bstep (se 1 (by rfl) ⟨117659, by rfl⟩ : syracuseStep 156879 = 235319) B235319
theorem B353609 : Blo 155795 353609 := bstep (se 2 (by rfl) ⟨132603, by rfl⟩ : syracuseStep 353609 = 265207) B265207
theorem B157083 : Blo 155795 157083 := bstep (se 1 (by rfl) ⟨117812, by rfl⟩ : syracuseStep 157083 = 235625) B235625
theorem B157295 : Blo 155795 157295 := bstep (se 1 (by rfl) ⟨117971, by rfl⟩ : syracuseStep 157295 = 235943) B235943
theorem B222841 : Blo 155795 222841 := bstep (se 2 (by rfl) ⟨83565, by rfl⟩ : syracuseStep 222841 = 167131) B167131
theorem B157351 : Blo 155795 157351 := bstep (se 1 (by rfl) ⟨118013, by rfl⟩ : syracuseStep 157351 = 236027) B236027
theorem B911033 : Blo 155795 911033 := bstep (se 2 (by rfl) ⟨341637, by rfl⟩ : syracuseStep 911033 = 683275) B683275
theorem B157435 : Blo 155795 157435 := bstep (se 1 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 157435 = 236153) B236153
theorem B255739 : Blo 155795 255739 := bstep (se 1 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 255739 = 383609) B383609
theorem B157471 : Blo 155795 157471 := bstep (se 1 (by rfl) ⟨118103, by rfl⟩ : syracuseStep 157471 = 236207) B236207
theorem B157503 : Blo 155795 157503 := bstep (se 1 (by rfl) ⟨118127, by rfl⟩ : syracuseStep 157503 = 236255) B236255
theorem B2844503 : Blo 155795 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B157679 : Blo 155795 157679 := bstep (se 1 (by rfl) ⟨118259, by rfl⟩ : syracuseStep 157679 = 236519) B236519
theorem B157851 : Blo 155795 157851 := bstep (se 1 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 157851 = 236777) B236777
theorem B157887 : Blo 155795 157887 := bstep (se 1 (by rfl) ⟨118415, by rfl⟩ : syracuseStep 157887 = 236831) B236831
theorem B1468697 : Blo 155795 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B354599 : Blo 155795 354599 := bstep (se 1 (by rfl) ⟨265949, by rfl⟩ : syracuseStep 354599 = 531899) B531899
theorem B157999 : Blo 155795 157999 := bstep (se 1 (by rfl) ⟨118499, by rfl⟩ : syracuseStep 157999 = 236999) B236999
theorem B354617 : Blo 155795 354617 := bstep (se 2 (by rfl) ⟨132981, by rfl⟩ : syracuseStep 354617 = 265963) B265963
theorem B158235 : Blo 155795 158235 := bstep (se 1 (by rfl) ⟨118676, by rfl⟩ : syracuseStep 158235 = 237353) B237353
theorem B158239 : Blo 155795 158239 := bstep (se 1 (by rfl) ⟨118679, by rfl⟩ : syracuseStep 158239 = 237359) B237359
theorem B158555 : Blo 155795 158555 := bstep (se 1 (by rfl) ⟨118916, by rfl⟩ : syracuseStep 158555 = 237833) B237833
theorem B158623 : Blo 155795 158623 := bstep (se 1 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 158623 = 237935) B237935
theorem B158767 : Blo 155795 158767 := bstep (se 1 (by rfl) ⟨119075, by rfl⟩ : syracuseStep 158767 = 238151) B238151
theorem B224327 : Blo 155795 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B158791 : Blo 155795 158791 := bstep (se 1 (by rfl) ⟨119093, by rfl⟩ : syracuseStep 158791 = 238187) B238187
theorem B1076345 : Blo 155795 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B158943 : Blo 155795 158943 := bstep (se 1 (by rfl) ⟨119207, by rfl⟩ : syracuseStep 158943 = 238415) B238415
theorem B1010987 : Blo 155795 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1142059 : Blo 155795 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B224623 : Blo 155795 224623 := bstep (se 1 (by rfl) ⟨168467, by rfl⟩ : syracuseStep 224623 = 336935) B336935
theorem B159207 : Blo 155795 159207 := bstep (se 1 (by rfl) ⟨119405, by rfl⟩ : syracuseStep 159207 = 238811) B238811
theorem B355913 : Blo 155795 355913 := bstep (se 2 (by rfl) ⟨133467, by rfl⟩ : syracuseStep 355913 = 266935) B266935
theorem B159323 : Blo 155795 159323 := bstep (se 1 (by rfl) ⟨119492, by rfl⟩ : syracuseStep 159323 = 238985) B238985
theorem B159559 : Blo 155795 159559 := bstep (se 1 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 159559 = 239339) B239339
theorem B159711 : Blo 155795 159711 := bstep (se 1 (by rfl) ⟨119783, by rfl⟩ : syracuseStep 159711 = 239567) B239567
theorem B225785 : Blo 155795 225785 := bstep (se 2 (by rfl) ⟨84669, by rfl⟩ : syracuseStep 225785 = 169339) B169339
theorem B1012445 : Blo 155795 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B357371 : Blo 155795 357371 := bstep (se 1 (by rfl) ⟨268028, by rfl⟩ : syracuseStep 357371 = 536057) B536057
theorem B422975 : Blo 155795 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B357551 : Blo 155795 357551 := bstep (se 1 (by rfl) ⟨268163, by rfl⟩ : syracuseStep 357551 = 536327) B536327
theorem B357587 : Blo 155795 357587 := bstep (se 1 (by rfl) ⟨268190, by rfl⟩ : syracuseStep 357587 = 536381) B536381
theorem B226651 : Blo 155795 226651 := bstep (se 1 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 226651 = 339977) B339977
theorem B2028989 : Blo 155795 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B357857 : Blo 155795 357857 := bstep (se 2 (by rfl) ⟨134196, by rfl⟩ : syracuseStep 357857 = 268393) B268393
theorem B4028453 : Blo 155795 4028453 := bstep (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) B755335
theorem B424381 : Blo 155795 424381 := bstep (se 3 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 424381 = 159143) B159143
theorem B1145897 : Blo 155795 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B359495 : Blo 155795 359495 := bstep (se 1 (by rfl) ⟨269621, by rfl⟩ : syracuseStep 359495 = 539243) B539243
theorem B3440015 : Blo 155795 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1703405 : Blo 155795 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B2490401 : Blo 155795 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B2162875 : Blo 155795 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B4129049 : Blo 155795 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B5800643 : Blo 155795 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B1442873 : Blo 155795 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B296111 : Blo 155795 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B263675 : Blo 155795 263675 := bstep (se 1 (by rfl) ⟨197756, by rfl⟩ : syracuseStep 263675 = 395513) B395513
theorem B2360927 : Blo 155795 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B1345247 : Blo 155795 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B10192877 : Blo 155795 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B755837 : Blo 155795 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B297121 : Blo 155795 297121 := bstep (se 2 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 297121 = 222841) B222841
theorem B1313063 : Blo 155795 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B788777 : Blo 155795 788777 := bstep (se 2 (by rfl) ⟨295791, by rfl⟩ : syracuseStep 788777 = 591583) B591583
theorem B592343 : Blo 155795 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B854491 : Blo 155795 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B592541 : Blo 155795 592541 := bstep (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) B222203
theorem B1149815 : Blo 155795 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B396191 : Blo 155795 396191 := bstep (se 1 (by rfl) ⟨297143, by rfl⟩ : syracuseStep 396191 = 594287) B594287
theorem B199675 : Blo 155795 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B920639 : Blo 155795 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B265403 : Blo 155795 265403 := bstep (se 1 (by rfl) ⟨199052, by rfl⟩ : syracuseStep 265403 = 398105) B398105
theorem B790073 : Blo 155795 790073 := bstep (se 2 (by rfl) ⟨296277, by rfl⟩ : syracuseStep 790073 = 592555) B592555
theorem B5148335 : Blo 155795 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B1282031 : Blo 155795 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B397295 : Blo 155795 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B3084331 : Blo 155795 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B266395 : Blo 155795 266395 := bstep (se 1 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 266395 = 399593) B399593
theorem B2560157 : Blo 155795 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B266537 : Blo 155795 266537 := bstep (se 2 (by rfl) ⟨99951, by rfl⟩ : syracuseStep 266537 = 199903) B199903
theorem B889289 : Blo 155795 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B266807 : Blo 155795 266807 := bstep (se 1 (by rfl) ⟨200105, by rfl⟩ : syracuseStep 266807 = 400211) B400211
theorem B234479 : Blo 155795 234479 := bstep (se 1 (by rfl) ⟨175859, by rfl⟩ : syracuseStep 234479 = 351719) B351719
theorem B234863 : Blo 155795 234863 := bstep (se 1 (by rfl) ⟨176147, by rfl⟩ : syracuseStep 234863 = 352295) B352295
theorem B234983 : Blo 155795 234983 := bstep (se 1 (by rfl) ⟨176237, by rfl⟩ : syracuseStep 234983 = 352475) B352475
theorem B595457 : Blo 155795 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B988751 : Blo 155795 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B235145 : Blo 155795 235145 := bstep (se 2 (by rfl) ⟨88179, by rfl⟩ : syracuseStep 235145 = 176359) B176359
theorem B333467 : Blo 155795 333467 := bstep (se 1 (by rfl) ⟨250100, by rfl⟩ : syracuseStep 333467 = 500201) B500201
theorem B235163 : Blo 155795 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B595775 : Blo 155795 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B268103 : Blo 155795 268103 := bstep (se 1 (by rfl) ⟨201077, by rfl⟩ : syracuseStep 268103 = 402155) B402155
theorem B235355 : Blo 155795 235355 := bstep (se 1 (by rfl) ⟨176516, by rfl⟩ : syracuseStep 235355 = 353033) B353033
theorem B268123 : Blo 155795 268123 := bstep (se 1 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 268123 = 402185) B402185
theorem B235739 : Blo 155795 235739 := bstep (se 1 (by rfl) ⟨176804, by rfl⟩ : syracuseStep 235739 = 353609) B353609
theorem B399755 : Blo 155795 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B203239 : Blo 155795 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B236009 : Blo 155795 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B531197 : Blo 155795 531197 := bstep (se 3 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 531197 = 199199) B199199
theorem B596747 : Blo 155795 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B236399 : Blo 155795 236399 := bstep (se 1 (by rfl) ⟨177299, by rfl⟩ : syracuseStep 236399 = 354599) B354599
theorem B236411 : Blo 155795 236411 := bstep (se 1 (by rfl) ⟨177308, by rfl⟩ : syracuseStep 236411 = 354617) B354617
theorem B302201 : Blo 155795 302201 := bstep (se 2 (by rfl) ⟨113325, by rfl⟩ : syracuseStep 302201 = 226651) B226651
theorem B237275 : Blo 155795 237275 := bstep (se 1 (by rfl) ⟨177956, by rfl⟩ : syracuseStep 237275 = 355913) B355913
theorem B401375 : Blo 155795 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B237545 : Blo 155795 237545 := bstep (se 2 (by rfl) ⟨89079, by rfl⟩ : syracuseStep 237545 = 178159) B178159
theorem B598205 : Blo 155795 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B401719 : Blo 155795 401719 := bstep (se 1 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 401719 = 602579) B602579
theorem B565841 : Blo 155795 565841 := bstep (se 2 (by rfl) ⟨212190, by rfl⟩ : syracuseStep 565841 = 424381) B424381
theorem B238247 : Blo 155795 238247 := bstep (se 1 (by rfl) ⟨178685, by rfl⟩ : syracuseStep 238247 = 357371) B357371
theorem B7709357 : Blo 155795 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B238367 : Blo 155795 238367 := bstep (se 1 (by rfl) ⟨178775, by rfl⟩ : syracuseStep 238367 = 357551) B357551
theorem B238391 : Blo 155795 238391 := bstep (se 1 (by rfl) ⟨178793, by rfl⟩ : syracuseStep 238391 = 357587) B357587
theorem B1352659 : Blo 155795 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B238571 : Blo 155795 238571 := bstep (se 1 (by rfl) ⟨178928, by rfl⟩ : syracuseStep 238571 = 357857) B357857
theorem B402479 : Blo 155795 402479 := bstep (se 1 (by rfl) ⟨301859, by rfl⟩ : syracuseStep 402479 = 603719) B603719
theorem B3090001 : Blo 155795 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B403127 : Blo 155795 403127 := bstep (se 1 (by rfl) ⟨302345, by rfl⟩ : syracuseStep 403127 = 604691) B604691
theorem B665567 : Blo 155795 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B763931 : Blo 155795 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B239663 : Blo 155795 239663 := bstep (se 1 (by rfl) ⟨179747, by rfl⟩ : syracuseStep 239663 = 359495) B359495
theorem B7973057 : Blo 155795 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B928427 : Blo 155795 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B1911559 : Blo 155795 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B601121 : Blo 155795 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B7777361 : Blo 155795 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B896123 : Blo 155795 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B1518749 : Blo 155795 1518749 := bstep (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) B569531
theorem B175279 : Blo 155795 175279 := bstep (se 1 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 175279 = 262919) B262919
theorem B634105 : Blo 155795 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B666899 : Blo 155795 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B961811 : Blo 155795 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B241051 : Blo 155795 241051 := bstep (se 1 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 241051 = 361577) B361577
theorem B2698757 : Blo 155795 2698757 := bstep (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) B506017
theorem B601607 : Blo 155795 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B339527 : Blo 155795 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B1191671 : Blo 155795 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B175999 : Blo 155795 175999 := bstep (se 1 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 175999 = 263999) B263999
theorem B602093 : Blo 155795 602093 := bstep (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) B225785
theorem B1192157 : Blo 155795 1192157 := bstep (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) B447059
theorem B635111 : Blo 155795 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B176539 : Blo 155795 176539 := bstep (se 1 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 176539 = 264809) B264809
theorem B537407 : Blo 155795 537407 := bstep (se 1 (by rfl) ⟨403055, by rfl⟩ : syracuseStep 537407 = 806111) B806111
theorem B5714813 : Blo 155795 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B504787 : Blo 155795 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B340985 : Blo 155795 340985 := bstep (se 2 (by rfl) ⟨127869, by rfl⟩ : syracuseStep 340985 = 255739) B255739
theorem B177223 : Blo 155795 177223 := bstep (se 1 (by rfl) ⟨132917, by rfl⟩ : syracuseStep 177223 = 265835) B265835
theorem B1357033 : Blo 155795 1357033 := bstep (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) B1017775
theorem B177403 : Blo 155795 177403 := bstep (se 1 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 177403 = 266105) B266105
theorem B538109 : Blo 155795 538109 := bstep (se 3 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 538109 = 201791) B201791
theorem B898721 : Blo 155795 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B4273847 : Blo 155795 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B636797 : Blo 155795 636797 := bstep (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) B238799
theorem B505865 : Blo 155795 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B538919 : Blo 155795 538919 := bstep (se 1 (by rfl) ⟨404189, by rfl⟩ : syracuseStep 538919 = 808379) B808379
theorem B604523 : Blo 155795 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B178591 : Blo 155795 178591 := bstep (se 1 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 178591 = 267887) B267887
theorem B178663 : Blo 155795 178663 := bstep (se 1 (by rfl) ⟨133997, by rfl⟩ : syracuseStep 178663 = 267995) B267995
theorem B7650125 : Blo 155795 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B1522745 : Blo 155795 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B179527 : Blo 155795 179527 := bstep (se 1 (by rfl) ⟨134645, by rfl⟩ : syracuseStep 179527 = 269291) B269291
theorem B2276849 : Blo 155795 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B606163 : Blo 155795 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B377303 : Blo 155795 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B3916525 : Blo 155795 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B901955 : Blo 155795 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B607355 : Blo 155795 607355 := bstep (se 1 (by rfl) ⟨455516, by rfl⟩ : syracuseStep 607355 = 911033) B911033
theorem B509503 : Blo 155795 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B2672513 : Blo 155795 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B1197989 : Blo 155795 1197989 := bstep (se 4 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 1197989 = 224623) B224623
theorem B673991 : Blo 155795 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B5130701 : Blo 155795 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B805625 : Blo 155795 805625 := bstep (se 2 (by rfl) ⟨302109, by rfl⟩ : syracuseStep 805625 = 604219) B604219
theorem B445409 : Blo 155795 445409 := bstep (se 2 (by rfl) ⟨167028, by rfl⟩ : syracuseStep 445409 = 334057) B334057
theorem B674963 : Blo 155795 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B281983 : Blo 155795 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B380743 : Blo 155795 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B2576765 : Blo 155795 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B578459 : Blo 155795 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B1135603 : Blo 155795 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1267883 : Blo 155795 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B678107 : Blo 155795 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B2087279 : Blo 155795 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B350747 : Blo 155795 350747 := bstep (se 1 (by rfl) ⟨263060, by rfl⟩ : syracuseStep 350747 = 526121) B526121
theorem B1137617 : Blo 155795 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B23092775 : Blo 155795 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B352097 : Blo 155795 352097 := bstep (se 2 (by rfl) ⟨132036, by rfl⟩ : syracuseStep 352097 = 264073) B264073
theorem B352223 : Blo 155795 352223 := bstep (se 1 (by rfl) ⟨264167, by rfl⟩ : syracuseStep 352223 = 528335) B528335
theorem B253943 : Blo 155795 253943 := bstep (se 1 (by rfl) ⟨190457, by rfl⟩ : syracuseStep 253943 = 380915) B380915
theorem B155839 : Blo 155795 155839 := bstep (se 1 (by rfl) ⟨116879, by rfl⟩ : syracuseStep 155839 = 233759) B233759
theorem B155855 : Blo 155795 155855 := bstep (se 1 (by rfl) ⟨116891, by rfl⟩ : syracuseStep 155855 = 233783) B233783
theorem B155903 : Blo 155795 155903 := bstep (se 1 (by rfl) ⟨116927, by rfl⟩ : syracuseStep 155903 = 233855) B233855
theorem B352511 : Blo 155795 352511 := bstep (se 1 (by rfl) ⟨264383, by rfl⟩ : syracuseStep 352511 = 528767) B528767
theorem B155951 : Blo 155795 155951 := bstep (se 1 (by rfl) ⟨116963, by rfl⟩ : syracuseStep 155951 = 233927) B233927
theorem B352673 : Blo 155795 352673 := bstep (se 2 (by rfl) ⟨132252, by rfl⟩ : syracuseStep 352673 = 264505) B264505
theorem B156187 : Blo 155795 156187 := bstep (se 1 (by rfl) ⟨117140, by rfl⟩ : syracuseStep 156187 = 234281) B234281
theorem B156191 : Blo 155795 156191 := bstep (se 1 (by rfl) ⟨117143, by rfl⟩ : syracuseStep 156191 = 234287) B234287
theorem B156271 : Blo 155795 156271 := bstep (se 1 (by rfl) ⟨117203, by rfl⟩ : syracuseStep 156271 = 234407) B234407
theorem B156327 : Blo 155795 156327 := bstep (se 1 (by rfl) ⟨117245, by rfl⟩ : syracuseStep 156327 = 234491) B234491
theorem B156367 : Blo 155795 156367 := bstep (se 1 (by rfl) ⟨117275, by rfl⟩ : syracuseStep 156367 = 234551) B234551
theorem B156447 : Blo 155795 156447 := bstep (se 1 (by rfl) ⟨117335, by rfl⟩ : syracuseStep 156447 = 234671) B234671
theorem B156719 : Blo 155795 156719 := bstep (se 1 (by rfl) ⟨117539, by rfl⟩ : syracuseStep 156719 = 235079) B235079
theorem B156783 : Blo 155795 156783 := bstep (se 1 (by rfl) ⟨117587, by rfl⟩ : syracuseStep 156783 = 235175) B235175
theorem B156839 : Blo 155795 156839 := bstep (se 1 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 156839 = 235259) B235259
theorem B353447 : Blo 155795 353447 := bstep (se 1 (by rfl) ⟨265085, by rfl⟩ : syracuseStep 353447 = 530171) B530171
theorem B156863 : Blo 155795 156863 := bstep (se 1 (by rfl) ⟨117647, by rfl⟩ : syracuseStep 156863 = 235295) B235295
theorem B156895 : Blo 155795 156895 := bstep (se 1 (by rfl) ⟨117671, by rfl⟩ : syracuseStep 156895 = 235343) B235343
theorem B353555 : Blo 155795 353555 := bstep (se 1 (by rfl) ⟨265166, by rfl⟩ : syracuseStep 353555 = 530333) B530333
theorem B156975 : Blo 155795 156975 := bstep (se 1 (by rfl) ⟨117731, by rfl⟩ : syracuseStep 156975 = 235463) B235463
theorem B48850289 : Blo 155795 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B157211 : Blo 155795 157211 := bstep (se 1 (by rfl) ⟨117908, by rfl⟩ : syracuseStep 157211 = 235817) B235817
theorem B157215 : Blo 155795 157215 := bstep (se 1 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 157215 = 235823) B235823
theorem B1926737 : Blo 155795 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B157375 : Blo 155795 157375 := bstep (se 1 (by rfl) ⟨118031, by rfl⟩ : syracuseStep 157375 = 236063) B236063
theorem B714575 : Blo 155795 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B354185 : Blo 155795 354185 := bstep (se 2 (by rfl) ⟨132819, by rfl⟩ : syracuseStep 354185 = 265639) B265639
theorem B354203 : Blo 155795 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B354239 : Blo 155795 354239 := bstep (se 1 (by rfl) ⟨265679, by rfl⟩ : syracuseStep 354239 = 531359) B531359
theorem B157631 : Blo 155795 157631 := bstep (se 1 (by rfl) ⟨118223, by rfl⟩ : syracuseStep 157631 = 236447) B236447
theorem B157663 : Blo 155795 157663 := bstep (se 1 (by rfl) ⟨118247, by rfl⟩ : syracuseStep 157663 = 236495) B236495
theorem B157723 : Blo 155795 157723 := bstep (se 1 (by rfl) ⟨118292, by rfl⟩ : syracuseStep 157723 = 236585) B236585
theorem B157727 : Blo 155795 157727 := bstep (se 1 (by rfl) ⟨118295, by rfl⟩ : syracuseStep 157727 = 236591) B236591
theorem B157743 : Blo 155795 157743 := bstep (se 1 (by rfl) ⟨118307, by rfl⟩ : syracuseStep 157743 = 236615) B236615
theorem B354401 : Blo 155795 354401 := bstep (se 2 (by rfl) ⟨132900, by rfl⟩ : syracuseStep 354401 = 265801) B265801
theorem B157919 : Blo 155795 157919 := bstep (se 1 (by rfl) ⟨118439, by rfl⟩ : syracuseStep 157919 = 236879) B236879
theorem B157979 : Blo 155795 157979 := bstep (se 1 (by rfl) ⟨118484, by rfl⟩ : syracuseStep 157979 = 236969) B236969
theorem B158079 : Blo 155795 158079 := bstep (se 1 (by rfl) ⟨118559, by rfl⟩ : syracuseStep 158079 = 237119) B237119
theorem B682465 : Blo 155795 682465 := bstep (se 2 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 682465 = 511849) B511849
theorem B158255 : Blo 155795 158255 := bstep (se 1 (by rfl) ⟨118691, by rfl⟩ : syracuseStep 158255 = 237383) B237383
theorem B158311 : Blo 155795 158311 := bstep (se 1 (by rfl) ⟨118733, by rfl⟩ : syracuseStep 158311 = 237467) B237467
theorem B158687 : Blo 155795 158687 := bstep (se 1 (by rfl) ⟨119015, by rfl⟩ : syracuseStep 158687 = 238031) B238031
theorem B158715 : Blo 155795 158715 := bstep (se 1 (by rfl) ⟨119036, by rfl⟩ : syracuseStep 158715 = 238073) B238073
theorem B158783 : Blo 155795 158783 := bstep (se 1 (by rfl) ⟨119087, by rfl⟩ : syracuseStep 158783 = 238175) B238175
theorem B159103 : Blo 155795 159103 := bstep (se 1 (by rfl) ⟨119327, by rfl⟩ : syracuseStep 159103 = 238655) B238655
theorem B159131 : Blo 155795 159131 := bstep (se 1 (by rfl) ⟨119348, by rfl⟩ : syracuseStep 159131 = 238697) B238697
theorem B355751 : Blo 155795 355751 := bstep (se 1 (by rfl) ⟨266813, by rfl⟩ : syracuseStep 355751 = 533627) B533627
theorem B454099 : Blo 155795 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B159199 : Blo 155795 159199 := bstep (se 1 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 159199 = 238799) B238799
theorem B1895993 : Blo 155795 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B355931 : Blo 155795 355931 := bstep (se 1 (by rfl) ⟨266948, by rfl⟩ : syracuseStep 355931 = 533897) B533897
theorem B159335 : Blo 155795 159335 := bstep (se 1 (by rfl) ⟨119501, by rfl⟩ : syracuseStep 159335 = 239003) B239003
theorem B159483 : Blo 155795 159483 := bstep (se 1 (by rfl) ⟨119612, by rfl⟩ : syracuseStep 159483 = 239225) B239225
theorem B159551 : Blo 155795 159551 := bstep (se 1 (by rfl) ⟨119663, by rfl⟩ : syracuseStep 159551 = 239327) B239327
theorem B159615 : Blo 155795 159615 := bstep (se 1 (by rfl) ⟨119711, by rfl⟩ : syracuseStep 159615 = 239423) B239423
theorem B1896335 : Blo 155795 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B159727 : Blo 155795 159727 := bstep (se 1 (by rfl) ⟨119795, by rfl⟩ : syracuseStep 159727 = 239591) B239591
theorem B356345 : Blo 155795 356345 := bstep (se 2 (by rfl) ⟨133629, by rfl⟩ : syracuseStep 356345 = 267259) B267259
theorem B159739 : Blo 155795 159739 := bstep (se 1 (by rfl) ⟨119804, by rfl⟩ : syracuseStep 159739 = 239609) B239609
theorem B356435 : Blo 155795 356435 := bstep (se 1 (by rfl) ⟨267326, by rfl⟩ : syracuseStep 356435 = 534653) B534653
theorem B454753 : Blo 155795 454753 := bstep (se 2 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 454753 = 341065) B341065
theorem B356615 : Blo 155795 356615 := bstep (se 1 (by rfl) ⟨267461, by rfl⟩ : syracuseStep 356615 = 534923) B534923
theorem B356921 : Blo 155795 356921 := bstep (se 2 (by rfl) ⟨133845, by rfl⟩ : syracuseStep 356921 = 267691) B267691
theorem B717563 : Blo 155795 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B291881 : Blo 155795 291881 := bstep (se 2 (by rfl) ⟨109455, by rfl⟩ : syracuseStep 291881 = 218911) B218911
theorem B357641 : Blo 155795 357641 := bstep (se 2 (by rfl) ⟨134115, by rfl⟩ : syracuseStep 357641 = 268231) B268231
theorem B357695 : Blo 155795 357695 := bstep (se 1 (by rfl) ⟨268271, by rfl⟩ : syracuseStep 357695 = 536543) B536543
theorem B357803 : Blo 155795 357803 := bstep (se 1 (by rfl) ⟨268352, by rfl⟩ : syracuseStep 357803 = 536705) B536705
theorem B358127 : Blo 155795 358127 := bstep (se 1 (by rfl) ⟨268595, by rfl⟩ : syracuseStep 358127 = 537191) B537191
theorem B161519 : Blo 155795 161519 := bstep (se 1 (by rfl) ⟨121139, by rfl⟩ : syracuseStep 161519 = 242279) B242279
theorem B358343 : Blo 155795 358343 := bstep (se 1 (by rfl) ⟨268757, by rfl⟩ : syracuseStep 358343 = 537515) B537515
theorem B1144961 : Blo 155795 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B817361 : Blo 155795 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B358631 : Blo 155795 358631 := bstep (se 1 (by rfl) ⟨268973, by rfl⟩ : syracuseStep 358631 = 537947) B537947
theorem B358649 : Blo 155795 358649 := bstep (se 2 (by rfl) ⟨134493, by rfl⟩ : syracuseStep 358649 = 268987) B268987
theorem B358703 : Blo 155795 358703 := bstep (se 1 (by rfl) ⟨269027, by rfl⟩ : syracuseStep 358703 = 538055) B538055
theorem B358919 : Blo 155795 358919 := bstep (se 1 (by rfl) ⟨269189, by rfl⟩ : syracuseStep 358919 = 538379) B538379
theorem B359099 : Blo 155795 359099 := bstep (se 1 (by rfl) ⟨269324, by rfl⟩ : syracuseStep 359099 = 538649) B538649
theorem B2685635 : Blo 155795 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B2030993 : Blo 155795 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B2293343 : Blo 155795 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B2752699 : Blo 155795 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B2883833 : Blo 155795 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B3867095 : Blo 155795 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2425349 : Blo 155795 2425349 := bstep (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) B454753
theorem B197407 : Blo 155795 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B1803545 : Blo 155795 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B525851 : Blo 155795 525851 := bstep (se 1 (by rfl) ⟨394388, by rfl⟩ : syracuseStep 525851 = 788777) B788777
theorem B394895 : Blo 155795 394895 := bstep (se 1 (by rfl) ⟨296171, by rfl⟩ : syracuseStep 394895 = 592343) B592343
theorem B395027 : Blo 155795 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B264127 : Blo 155795 264127 := bstep (se 1 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 264127 = 396191) B396191
theorem B296939 : Blo 155795 296939 := bstep (se 1 (by rfl) ⟨222704, by rfl⟩ : syracuseStep 296939 = 445409) B445409
theorem B526715 : Blo 155795 526715 := bstep (se 1 (by rfl) ⟨395036, by rfl⟩ : syracuseStep 526715 = 790073) B790073
theorem B1542557 : Blo 155795 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1083941 : Blo 155795 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B854687 : Blo 155795 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B264863 : Blo 155795 264863 := bstep (se 1 (by rfl) ⟨198647, by rfl⟩ : syracuseStep 264863 = 397295) B397295
theorem B1706771 : Blo 155795 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B396161 : Blo 155795 396161 := bstep (se 2 (by rfl) ⟨148560, by rfl⟩ : syracuseStep 396161 = 297121) B297121
theorem B592859 : Blo 155795 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B396971 : Blo 155795 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B659167 : Blo 155795 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B397183 : Blo 155795 397183 := bstep (se 1 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 397183 = 595775) B595775
theorem B266233 : Blo 155795 266233 := bstep (se 2 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 266233 = 199675) B199675
theorem B233705 : Blo 155795 233705 := bstep (se 2 (by rfl) ⟨87639, by rfl⟩ : syracuseStep 233705 = 175279) B175279
theorem B6295805 : Blo 155795 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B266503 : Blo 155795 266503 := bstep (se 1 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 266503 = 399755) B399755
theorem B233831 : Blo 155795 233831 := bstep (se 1 (by rfl) ⟨175373, by rfl⟩ : syracuseStep 233831 = 350747) B350747
theorem B397831 : Blo 155795 397831 := bstep (se 1 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 397831 = 596747) B596747
theorem B430717 : Blo 155795 430717 := bstep (se 3 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 430717 = 161519) B161519
theorem B758411 : Blo 155795 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B201467 : Blo 155795 201467 := bstep (se 1 (by rfl) ⟨151100, by rfl⟩ : syracuseStep 201467 = 302201) B302201
theorem B234665 : Blo 155795 234665 := bstep (se 2 (by rfl) ⟨87999, by rfl⟩ : syracuseStep 234665 = 175999) B175999
theorem B234731 : Blo 155795 234731 := bstep (se 1 (by rfl) ⟨176048, by rfl⟩ : syracuseStep 234731 = 352097) B352097
theorem B234815 : Blo 155795 234815 := bstep (se 1 (by rfl) ⟨176111, by rfl⟩ : syracuseStep 234815 = 352223) B352223
theorem B267583 : Blo 155795 267583 := bstep (se 1 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 267583 = 401375) B401375
theorem B169295 : Blo 155795 169295 := bstep (se 1 (by rfl) ⟨126971, by rfl⟩ : syracuseStep 169295 = 253943) B253943
theorem B398803 : Blo 155795 398803 := bstep (se 1 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 398803 = 598205) B598205
theorem B235007 : Blo 155795 235007 := bstep (se 1 (by rfl) ⟨176255, by rfl⟩ : syracuseStep 235007 = 352511) B352511
theorem B235115 : Blo 155795 235115 := bstep (se 1 (by rfl) ⟨176336, by rfl⟩ : syracuseStep 235115 = 352673) B352673
theorem B235385 : Blo 155795 235385 := bstep (se 2 (by rfl) ⟨88269, by rfl⟩ : syracuseStep 235385 = 176539) B176539
theorem B268319 : Blo 155795 268319 := bstep (se 1 (by rfl) ⟨201239, by rfl⟩ : syracuseStep 268319 = 402479) B402479
theorem B235631 : Blo 155795 235631 := bstep (se 1 (by rfl) ⟨176723, by rfl⟩ : syracuseStep 235631 = 353447) B353447
theorem B235703 : Blo 155795 235703 := bstep (se 1 (by rfl) ⟨176777, by rfl⟩ : syracuseStep 235703 = 353555) B353555
theorem B1284491 : Blo 155795 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B268751 : Blo 155795 268751 := bstep (se 1 (by rfl) ⟨201563, by rfl⟩ : syracuseStep 268751 = 403127) B403127
theorem B236123 : Blo 155795 236123 := bstep (se 1 (by rfl) ⟨177092, by rfl⟩ : syracuseStep 236123 = 354185) B354185
theorem B236135 : Blo 155795 236135 := bstep (se 1 (by rfl) ⟨177101, by rfl⟩ : syracuseStep 236135 = 354203) B354203
theorem B236159 : Blo 155795 236159 := bstep (se 1 (by rfl) ⟨177119, by rfl⟩ : syracuseStep 236159 = 354239) B354239
theorem B1514137 : Blo 155795 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B236267 : Blo 155795 236267 := bstep (se 1 (by rfl) ⟨177200, by rfl⟩ : syracuseStep 236267 = 354401) B354401
theorem B236297 : Blo 155795 236297 := bstep (se 2 (by rfl) ⟨88611, by rfl⟩ : syracuseStep 236297 = 177223) B177223
theorem B5315371 : Blo 155795 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B1809377 : Blo 155795 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B236537 : Blo 155795 236537 := bstep (se 2 (by rfl) ⟨88701, by rfl⟩ : syracuseStep 236537 = 177403) B177403
theorem B400747 : Blo 155795 400747 := bstep (se 1 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 400747 = 601121) B601121
theorem B597415 : Blo 155795 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B237167 : Blo 155795 237167 := bstep (se 1 (by rfl) ⟨177875, by rfl⟩ : syracuseStep 237167 = 355751) B355751
theorem B401071 : Blo 155795 401071 := bstep (se 1 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 401071 = 601607) B601607
theorem B237287 : Blo 155795 237287 := bstep (se 1 (by rfl) ⟨177965, by rfl⟩ : syracuseStep 237287 = 355931) B355931
theorem B794447 : Blo 155795 794447 := bstep (se 1 (by rfl) ⟨595835, by rfl⟩ : syracuseStep 794447 = 1191671) B1191671
theorem B401395 : Blo 155795 401395 := bstep (se 1 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 401395 = 602093) B602093
theorem B237563 : Blo 155795 237563 := bstep (se 1 (by rfl) ⟨178172, by rfl⟩ : syracuseStep 237563 = 356345) B356345
theorem B237623 : Blo 155795 237623 := bstep (se 1 (by rfl) ⟨178217, by rfl⟩ : syracuseStep 237623 = 356435) B356435
theorem B794771 : Blo 155795 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B237743 : Blo 155795 237743 := bstep (se 1 (by rfl) ⟨178307, by rfl⟩ : syracuseStep 237743 = 356615) B356615
theorem B237947 : Blo 155795 237947 := bstep (se 1 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 237947 = 356921) B356921
theorem B238121 : Blo 155795 238121 := bstep (se 2 (by rfl) ⟨89295, by rfl⟩ : syracuseStep 238121 = 178591) B178591
theorem B3809875 : Blo 155795 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B238217 : Blo 155795 238217 := bstep (se 2 (by rfl) ⟨89331, by rfl⟩ : syracuseStep 238217 = 178663) B178663
theorem B238427 : Blo 155795 238427 := bstep (se 1 (by rfl) ⟨178820, by rfl⟩ : syracuseStep 238427 = 357641) B357641
theorem B238463 : Blo 155795 238463 := bstep (se 1 (by rfl) ⟨178847, by rfl⟩ : syracuseStep 238463 = 357695) B357695
theorem B238535 : Blo 155795 238535 := bstep (se 1 (by rfl) ⟨178901, by rfl⟩ : syracuseStep 238535 = 357803) B357803
theorem B599147 : Blo 155795 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B238751 : Blo 155795 238751 := bstep (se 1 (by rfl) ⟨179063, by rfl⟩ : syracuseStep 238751 = 358127) B358127
theorem B238895 : Blo 155795 238895 := bstep (se 1 (by rfl) ⟨179171, by rfl⟩ : syracuseStep 238895 = 358343) B358343
theorem B337243 : Blo 155795 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B763307 : Blo 155795 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B239087 : Blo 155795 239087 := bstep (se 1 (by rfl) ⟨179315, by rfl⟩ : syracuseStep 239087 = 358631) B358631
theorem B239099 : Blo 155795 239099 := bstep (se 1 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 239099 = 358649) B358649
theorem B239135 : Blo 155795 239135 := bstep (se 1 (by rfl) ⟨179351, by rfl⟩ : syracuseStep 239135 = 358703) B358703
theorem B403015 : Blo 155795 403015 := bstep (se 1 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 403015 = 604523) B604523
theorem B239279 : Blo 155795 239279 := bstep (se 1 (by rfl) ⟨179459, by rfl⟩ : syracuseStep 239279 = 358919) B358919
theorem B239369 : Blo 155795 239369 := bstep (se 2 (by rfl) ⟨89763, by rfl⟩ : syracuseStep 239369 = 179527) B179527
theorem B239399 : Blo 155795 239399 := bstep (se 1 (by rfl) ⟨179549, by rfl⟩ : syracuseStep 239399 = 359099) B359099
theorem B1353995 : Blo 155795 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B1517899 : Blo 155795 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B535625 : Blo 155795 535625 := bstep (se 2 (by rfl) ⟨200859, by rfl⟩ : syracuseStep 535625 = 401719) B401719
theorem B601303 : Blo 155795 601303 := bstep (se 1 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 601303 = 901955) B901955
theorem B961915 : Blo 155795 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B404903 : Blo 155795 404903 := bstep (se 1 (by rfl) ⟨303677, by rfl⟩ : syracuseStep 404903 = 607355) B607355
theorem B5222033 : Blo 155795 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B175783 : Blo 155795 175783 := bstep (se 1 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 175783 = 263675) B263675
theorem B896831 : Blo 155795 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B1781675 : Blo 155795 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B798659 : Blo 155795 798659 := bstep (se 1 (by rfl) ⟨598994, by rfl⟩ : syracuseStep 798659 = 1197989) B1197989
theorem B6795251 : Blo 155795 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B503891 : Blo 155795 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B3420467 : Blo 155795 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B537083 : Blo 155795 537083 := bstep (se 1 (by rfl) ⟨402812, by rfl⟩ : syracuseStep 537083 = 805625) B805625
theorem B176935 : Blo 155795 176935 := bstep (se 1 (by rfl) ⟨132701, by rfl⟩ : syracuseStep 176935 = 265403) B265403
theorem B177691 : Blo 155795 177691 := bstep (se 1 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 177691 = 266537) B266537
theorem B1717843 : Blo 155795 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B177871 : Blo 155795 177871 := bstep (se 1 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 177871 = 266807) B266807
theorem B178735 : Blo 155795 178735 := bstep (se 1 (by rfl) ⟨134051, by rfl⟩ : syracuseStep 178735 = 268103) B268103
theorem B1391519 : Blo 155795 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B375977 : Blo 155795 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B605465 : Blo 155795 605465 := bstep (se 2 (by rfl) ⟨227049, by rfl⟩ : syracuseStep 605465 = 454099) B454099
theorem B4112441 : Blo 155795 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B377227 : Blo 155795 377227 := bstep (se 1 (by rfl) ⟨282920, by rfl⟩ : syracuseStep 377227 = 565841) B565841
theorem B476383 : Blo 155795 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B673049 : Blo 155795 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B443711 : Blo 155795 443711 := bstep (se 1 (by rfl) ⟨332783, by rfl⟩ : syracuseStep 443711 = 665567) B665567
theorem B509287 : Blo 155795 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B2475805 : Blo 155795 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B444599 : Blo 155795 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B641207 : Blo 155795 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B3066173 : Blo 155795 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B1263995 : Blo 155795 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B1264223 : Blo 155795 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B478375 : Blo 155795 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B544907 : Blo 155795 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B1790423 : Blo 155795 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B5100083 : Blo 155795 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B1528895 : Blo 155795 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B808217 : Blo 155795 808217 := bstep (se 2 (by rfl) ⟨303081, by rfl⟩ : syracuseStep 808217 = 606163) B606163
theorem B1660267 : Blo 155795 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B1006141 : Blo 155795 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B449327 : Blo 155795 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B875375 : Blo 155795 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B613759 : Blo 155795 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B679337 : Blo 155795 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B449975 : Blo 155795 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B4120001 : Blo 155795 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B3432223 : Blo 155795 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B778349 : Blo 155795 778349 := bstep (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) B291881
theorem B1139321 : Blo 155795 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B909953 : Blo 155795 909953 := bstep (se 2 (by rfl) ⟨341232, by rfl⟩ : syracuseStep 909953 = 682465) B682465
theorem B156319 : Blo 155795 156319 := bstep (se 1 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 156319 = 234479) B234479
theorem B156575 : Blo 155795 156575 := bstep (se 1 (by rfl) ⟨117431, by rfl⟩ : syracuseStep 156575 = 234863) B234863
theorem B156655 : Blo 155795 156655 := bstep (se 1 (by rfl) ⟨117491, by rfl⟩ : syracuseStep 156655 = 234983) B234983
theorem B2548745 : Blo 155795 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B156763 : Blo 155795 156763 := bstep (se 1 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 156763 = 235145) B235145
theorem B222311 : Blo 155795 222311 := bstep (se 1 (by rfl) ⟨166733, by rfl⟩ : syracuseStep 222311 = 333467) B333467
theorem B156775 : Blo 155795 156775 := bstep (se 1 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 156775 = 235163) B235163
theorem B156903 : Blo 155795 156903 := bstep (se 1 (by rfl) ⟨117677, by rfl⟩ : syracuseStep 156903 = 235355) B235355
theorem B845255 : Blo 155795 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B157159 : Blo 155795 157159 := bstep (se 1 (by rfl) ⟨117869, by rfl⟩ : syracuseStep 157159 = 235739) B235739
theorem B452071 : Blo 155795 452071 := bstep (se 1 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 452071 = 678107) B678107
theorem B157339 : Blo 155795 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B845473 : Blo 155795 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B354131 : Blo 155795 354131 := bstep (se 1 (by rfl) ⟨265598, by rfl⟩ : syracuseStep 354131 = 531197) B531197
theorem B321401 : Blo 155795 321401 := bstep (se 2 (by rfl) ⟨120525, by rfl⟩ : syracuseStep 321401 = 241051) B241051
theorem B157599 : Blo 155795 157599 := bstep (se 1 (by rfl) ⟨118199, by rfl⟩ : syracuseStep 157599 = 236399) B236399
theorem B157607 : Blo 155795 157607 := bstep (se 1 (by rfl) ⟨118205, by rfl⟩ : syracuseStep 157607 = 236411) B236411
theorem B15395183 : Blo 155795 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B158183 : Blo 155795 158183 := bstep (se 1 (by rfl) ⟨118637, by rfl⟩ : syracuseStep 158183 = 237275) B237275
theorem B158363 : Blo 155795 158363 := bstep (se 1 (by rfl) ⟨118772, by rfl⟩ : syracuseStep 158363 = 237545) B237545
theorem B355193 : Blo 155795 355193 := bstep (se 2 (by rfl) ⟨133197, by rfl⟩ : syracuseStep 355193 = 266395) B266395
theorem B158831 : Blo 155795 158831 := bstep (se 1 (by rfl) ⟨119123, by rfl⟩ : syracuseStep 158831 = 238247) B238247
theorem B5139571 : Blo 155795 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B158911 : Blo 155795 158911 := bstep (se 1 (by rfl) ⟨119183, by rfl⟩ : syracuseStep 158911 = 238367) B238367
theorem B158927 : Blo 155795 158927 := bstep (se 1 (by rfl) ⟨119195, by rfl⟩ : syracuseStep 158927 = 238391) B238391
theorem B159047 : Blo 155795 159047 := bstep (se 1 (by rfl) ⟨119285, by rfl⟩ : syracuseStep 159047 = 238571) B238571
theorem B32566859 : Blo 155795 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B159775 : Blo 155795 159775 := bstep (se 1 (by rfl) ⟨119831, by rfl⟩ : syracuseStep 159775 = 239663) B239663
theorem B1012499 : Blo 155795 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B1799171 : Blo 155795 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B226351 : Blo 155795 226351 := bstep (se 1 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 226351 = 339527) B339527
theorem B357497 : Blo 155795 357497 := bstep (se 2 (by rfl) ⟨134061, by rfl⟩ : syracuseStep 357497 = 268123) B268123
theorem B423407 : Blo 155795 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B20739629 : Blo 155795 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B358271 : Blo 155795 358271 := bstep (se 1 (by rfl) ⟨268703, by rfl⟩ : syracuseStep 358271 = 537407) B537407
theorem B227323 : Blo 155795 227323 := bstep (se 1 (by rfl) ⟨170492, by rfl⟩ : syracuseStep 227323 = 340985) B340985
theorem B358739 : Blo 155795 358739 := bstep (se 1 (by rfl) ⟨269054, by rfl⟩ : syracuseStep 358739 = 538109) B538109
theorem B2849231 : Blo 155795 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B424531 : Blo 155795 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B359279 : Blo 155795 359279 := bstep (se 1 (by rfl) ⟨269459, by rfl⟩ : syracuseStep 359279 = 538919) B538919
theorem B2030629 : Blo 155795 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B1015163 : Blo 155795 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B3670265 : Blo 155795 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B5079833 : Blo 155795 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B295807 : Blo 155795 295807 := bstep (se 1 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 295807 = 443711) B443711
theorem B263209 : Blo 155795 263209 := bstep (se 2 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 263209 = 197407) B197407
theorem B263263 : Blo 155795 263263 := bstep (se 1 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 263263 = 394895) B394895
theorem B263351 : Blo 155795 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B197959 : Blo 155795 197959 := bstep (se 1 (by rfl) ⟨148469, by rfl⟩ : syracuseStep 197959 = 296939) B296939
theorem B296399 : Blo 155795 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B722627 : Blo 155795 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B264107 : Blo 155795 264107 := bstep (se 1 (by rfl) ⟨198080, by rfl⟩ : syracuseStep 264107 = 396161) B396161
theorem B395239 : Blo 155795 395239 := bstep (se 1 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 395239 = 592859) B592859
theorem B264647 : Blo 155795 264647 := bstep (se 1 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 264647 = 396971) B396971
theorem B4197203 : Blo 155795 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B592829 : Blo 155795 592829 := bstep (se 3 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 592829 = 222311) B222311
theorem B1019263 : Blo 155795 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B6852761 : Blo 155795 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B28348645 : Blo 155795 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B856327 : Blo 155795 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1282553 : Blo 155795 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B299551 : Blo 155795 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B234377 : Blo 155795 234377 := bstep (se 2 (by rfl) ⟨87891, by rfl⟩ : syracuseStep 234377 = 175783) B175783
theorem B529577 : Blo 155795 529577 := bstep (se 2 (by rfl) ⟨198591, by rfl⟩ : syracuseStep 529577 = 397183) B397183
theorem B529631 : Blo 155795 529631 := bstep (se 1 (by rfl) ⟨397223, by rfl⟩ : syracuseStep 529631 = 794447) B794447
theorem B529847 : Blo 155795 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B759547 : Blo 155795 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B1709885 : Blo 155795 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B530441 : Blo 155795 530441 := bstep (se 2 (by rfl) ⟨198915, by rfl⟩ : syracuseStep 530441 = 397831) B397831
theorem B399431 : Blo 155795 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B235913 : Blo 155795 235913 := bstep (se 2 (by rfl) ⟨88467, by rfl⟩ : syracuseStep 235913 = 176935) B176935
theorem B236087 : Blo 155795 236087 := bstep (se 1 (by rfl) ⟨177065, by rfl⟩ : syracuseStep 236087 = 354131) B354131
theorem B301801 : Blo 155795 301801 := bstep (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) B226351
theorem B10263455 : Blo 155795 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B236795 : Blo 155795 236795 := bstep (se 1 (by rfl) ⟨177596, by rfl⟩ : syracuseStep 236795 = 355193) B355193
theorem B531737 : Blo 155795 531737 := bstep (se 2 (by rfl) ⟨199401, by rfl⟩ : syracuseStep 531737 = 398803) B398803
theorem B236921 : Blo 155795 236921 := bstep (se 2 (by rfl) ⟨88845, by rfl⟩ : syracuseStep 236921 = 177691) B177691
theorem B237161 : Blo 155795 237161 := bstep (se 2 (by rfl) ⟨88935, by rfl⟩ : syracuseStep 237161 = 177871) B177871
theorem B269935 : Blo 155795 269935 := bstep (se 1 (by rfl) ⟨202451, by rfl⟩ : syracuseStep 269935 = 404903) B404903
theorem B3481355 : Blo 155795 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B597887 : Blo 155795 597887 := bstep (se 1 (by rfl) ⟨448415, by rfl⟩ : syracuseStep 597887 = 896831) B896831
theorem B1187783 : Blo 155795 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B532439 : Blo 155795 532439 := bstep (se 1 (by rfl) ⟨399329, by rfl⟩ : syracuseStep 532439 = 798659) B798659
theorem B4530167 : Blo 155795 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B303097 : Blo 155795 303097 := bstep (se 2 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 303097 = 227323) B227323
theorem B335927 : Blo 155795 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B238313 : Blo 155795 238313 := bstep (se 2 (by rfl) ⟨89367, by rfl⟩ : syracuseStep 238313 = 178735) B178735
theorem B238331 : Blo 155795 238331 := bstep (se 1 (by rfl) ⟨178748, by rfl⟩ : syracuseStep 238331 = 357497) B357497
theorem B566041 : Blo 155795 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B3515557 : Blo 155795 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B238847 : Blo 155795 238847 := bstep (se 1 (by rfl) ⟨179135, by rfl⟩ : syracuseStep 238847 = 358271) B358271
theorem B239159 : Blo 155795 239159 := bstep (se 1 (by rfl) ⟨179369, by rfl⟩ : syracuseStep 239159 = 358739) B358739
theorem B534329 : Blo 155795 534329 := bstep (se 2 (by rfl) ⟨200373, by rfl⟩ : syracuseStep 534329 = 400747) B400747
theorem B796553 : Blo 155795 796553 := bstep (se 2 (by rfl) ⟨298707, by rfl⟩ : syracuseStep 796553 = 597415) B597415
theorem B239519 : Blo 155795 239519 := bstep (se 1 (by rfl) ⟨179639, by rfl⟩ : syracuseStep 239519 = 359279) B359279
theorem B927679 : Blo 155795 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B403643 : Blo 155795 403643 := bstep (se 1 (by rfl) ⟨302732, by rfl⟩ : syracuseStep 403643 = 605465) B605465
theorem B534761 : Blo 155795 534761 := bstep (se 2 (by rfl) ⟨200535, by rfl⟩ : syracuseStep 534761 = 401071) B401071
theorem B535193 : Blo 155795 535193 := bstep (se 2 (by rfl) ⟨200697, by rfl⟩ : syracuseStep 535193 = 401395) B401395
theorem B2075597 : Blo 155795 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B1453085 : Blo 155795 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B502969 : Blo 155795 502969 := bstep (se 2 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 502969 = 377227) B377227
theorem B6467597 : Blo 155795 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B2044115 : Blo 155795 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B1028371 : Blo 155795 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B635177 : Blo 155795 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B569791 : Blo 155795 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B176575 : Blo 155795 176575 := bstep (se 1 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 176575 = 264863) B264863
theorem B602761 : Blo 155795 602761 := bstep (se 2 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 602761 = 452071) B452071
theorem B537245 : Blo 155795 537245 := bstep (se 3 (by rfl) ⟨100733, by rfl⟩ : syracuseStep 537245 = 201467) B201467
theorem B537353 : Blo 155795 537353 := bstep (se 2 (by rfl) ⟨201507, by rfl⟩ : syracuseStep 537353 = 403015) B403015
theorem B1127297 : Blo 155795 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B1193615 : Blo 155795 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B505607 : Blo 155795 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B538811 : Blo 155795 538811 := bstep (se 1 (by rfl) ⟨404108, by rfl⟩ : syracuseStep 538811 = 808217) B808217
theorem B1129085 : Blo 155795 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B178879 : Blo 155795 178879 := bstep (se 1 (by rfl) ⟨134159, by rfl⟩ : syracuseStep 178879 = 268319) B268319
theorem B801737 : Blo 155795 801737 := bstep (se 2 (by rfl) ⟨300651, by rfl⟩ : syracuseStep 801737 = 601303) B601303
theorem B179167 : Blo 155795 179167 := bstep (se 1 (by rfl) ⟨134375, by rfl⟩ : syracuseStep 179167 = 268751) B268751
theorem B606635 : Blo 155795 606635 := bstep (se 1 (by rfl) ⟨454976, by rfl⟩ : syracuseStep 606635 = 909953) B909953
theorem B574289 : Blo 155795 574289 := bstep (se 2 (by rfl) ⟨215358, by rfl⟩ : syracuseStep 574289 = 430717) B430717
theorem B508871 : Blo 155795 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B214267 : Blo 155795 214267 := bstep (se 1 (by rfl) ⟨160700, by rfl⟩ : syracuseStep 214267 = 321401) B321401
theorem B902663 : Blo 155795 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B2213689 : Blo 155795 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B21711239 : Blo 155795 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B2280311 : Blo 155795 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B674999 : Blo 155795 674999 := bstep (se 1 (by rfl) ⟨506249, by rfl⟩ : syracuseStep 674999 = 1012499) B1012499
theorem B1199447 : Blo 155795 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B2018849 : Blo 155795 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B1199933 : Blo 155795 1199933 := bstep (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) B449975
theorem B2707505 : Blo 155795 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B250651 : Blo 155795 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B676775 : Blo 155795 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B4576297 : Blo 155795 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B2741627 : Blo 155795 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B1922555 : Blo 155795 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B2578063 : Blo 155795 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B1202363 : Blo 155795 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B350567 : Blo 155795 350567 := bstep (se 1 (by rfl) ⟨262925, by rfl⟩ : syracuseStep 350567 = 525851) B525851
theorem B842663 : Blo 155795 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B351143 : Blo 155795 351143 := bstep (se 1 (by rfl) ⟨263357, by rfl⟩ : syracuseStep 351143 = 526715) B526715
theorem B842815 : Blo 155795 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B449657 : Blo 155795 449657 := bstep (se 2 (by rfl) ⟨168621, by rfl⟩ : syracuseStep 449657 = 337243) B337243
theorem B679049 : Blo 155795 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B3301073 : Blo 155795 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B352169 : Blo 155795 352169 := bstep (se 2 (by rfl) ⟨132063, by rfl⟩ : syracuseStep 352169 = 264127) B264127
theorem B155803 : Blo 155795 155803 := bstep (se 1 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 155803 = 233705) B233705
theorem B155887 : Blo 155795 155887 := bstep (se 1 (by rfl) ⟨116915, by rfl⟩ : syracuseStep 155887 = 233831) B233831
theorem B3400055 : Blo 155795 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B2023865 : Blo 155795 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B1794797 : Blo 155795 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B156443 : Blo 155795 156443 := bstep (se 1 (by rfl) ⟨117332, by rfl⟩ : syracuseStep 156443 = 234665) B234665
theorem B156487 : Blo 155795 156487 := bstep (se 1 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 156487 = 234731) B234731
theorem B451453 : Blo 155795 451453 := bstep (se 3 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 451453 = 169295) B169295
theorem B156543 : Blo 155795 156543 := bstep (se 1 (by rfl) ⟨117407, by rfl⟩ : syracuseStep 156543 = 234815) B234815
theorem B156671 : Blo 155795 156671 := bstep (se 1 (by rfl) ⟨117503, by rfl⟩ : syracuseStep 156671 = 235007) B235007
theorem B156743 : Blo 155795 156743 := bstep (se 1 (by rfl) ⟨117557, by rfl⟩ : syracuseStep 156743 = 235115) B235115
theorem B2254013 : Blo 155795 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B156923 : Blo 155795 156923 := bstep (se 1 (by rfl) ⟨117692, by rfl⟩ : syracuseStep 156923 = 235385) B235385
theorem B157087 : Blo 155795 157087 := bstep (se 1 (by rfl) ⟨117815, by rfl⟩ : syracuseStep 157087 = 235631) B235631
theorem B157135 : Blo 155795 157135 := bstep (se 1 (by rfl) ⟨117851, by rfl⟩ : syracuseStep 157135 = 235703) B235703
theorem B157415 : Blo 155795 157415 := bstep (se 1 (by rfl) ⟨118061, by rfl⟩ : syracuseStep 157415 = 236123) B236123
theorem B157423 : Blo 155795 157423 := bstep (se 1 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 157423 = 236135) B236135
theorem B157439 : Blo 155795 157439 := bstep (se 1 (by rfl) ⟨118079, by rfl⟩ : syracuseStep 157439 = 236159) B236159
theorem B157511 : Blo 155795 157511 := bstep (se 1 (by rfl) ⟨118133, by rfl⟩ : syracuseStep 157511 = 236267) B236267
theorem B157531 : Blo 155795 157531 := bstep (se 1 (by rfl) ⟨118148, by rfl⟩ : syracuseStep 157531 = 236297) B236297
theorem B583583 : Blo 155795 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B1206251 : Blo 155795 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B157691 : Blo 155795 157691 := bstep (se 1 (by rfl) ⟨118268, by rfl⟩ : syracuseStep 157691 = 236537) B236537
theorem B452891 : Blo 155795 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B2746667 : Blo 155795 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B158111 : Blo 155795 158111 := bstep (se 1 (by rfl) ⟨118583, by rfl⟩ : syracuseStep 158111 = 237167) B237167
theorem B158191 : Blo 155795 158191 := bstep (se 1 (by rfl) ⟨118643, by rfl⟩ : syracuseStep 158191 = 237287) B237287
theorem B354977 : Blo 155795 354977 := bstep (se 2 (by rfl) ⟨133116, by rfl⟩ : syracuseStep 354977 = 266233) B266233
theorem B158375 : Blo 155795 158375 := bstep (se 1 (by rfl) ⟨118781, by rfl⟩ : syracuseStep 158375 = 237563) B237563
theorem B158415 : Blo 155795 158415 := bstep (se 1 (by rfl) ⟨118811, by rfl⟩ : syracuseStep 158415 = 237623) B237623
theorem B158495 : Blo 155795 158495 := bstep (se 1 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 158495 = 237743) B237743
theorem B158631 : Blo 155795 158631 := bstep (se 1 (by rfl) ⟨118973, by rfl⟩ : syracuseStep 158631 = 237947) B237947
theorem B355337 : Blo 155795 355337 := bstep (se 2 (by rfl) ⟨133251, by rfl⟩ : syracuseStep 355337 = 266503) B266503
theorem B158747 : Blo 155795 158747 := bstep (se 1 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 158747 = 238121) B238121
theorem B158811 : Blo 155795 158811 := bstep (se 1 (by rfl) ⟨119108, by rfl⟩ : syracuseStep 158811 = 238217) B238217
theorem B158951 : Blo 155795 158951 := bstep (se 1 (by rfl) ⟨119213, by rfl⟩ : syracuseStep 158951 = 238427) B238427
theorem B158975 : Blo 155795 158975 := bstep (se 1 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 158975 = 238463) B238463
theorem B159023 : Blo 155795 159023 := bstep (se 1 (by rfl) ⟨119267, by rfl⟩ : syracuseStep 159023 = 238535) B238535
theorem B1699163 : Blo 155795 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B159167 : Blo 155795 159167 := bstep (se 1 (by rfl) ⟨119375, by rfl⟩ : syracuseStep 159167 = 238751) B238751
theorem B159263 : Blo 155795 159263 := bstep (se 1 (by rfl) ⟨119447, by rfl⟩ : syracuseStep 159263 = 238895) B238895
theorem B2551333 : Blo 155795 2551333 := bstep (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) B478375
theorem B159391 : Blo 155795 159391 := bstep (se 1 (by rfl) ⟨119543, by rfl⟩ : syracuseStep 159391 = 239087) B239087
theorem B159399 : Blo 155795 159399 := bstep (se 1 (by rfl) ⟨119549, by rfl⟩ : syracuseStep 159399 = 239099) B239099
theorem B159423 : Blo 155795 159423 := bstep (se 1 (by rfl) ⟨119567, by rfl⟩ : syracuseStep 159423 = 239135) B239135
theorem B159519 : Blo 155795 159519 := bstep (se 1 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 159519 = 239279) B239279
theorem B159579 : Blo 155795 159579 := bstep (se 1 (by rfl) ⟨119684, by rfl⟩ : syracuseStep 159579 = 239369) B239369
theorem B159599 : Blo 155795 159599 := bstep (se 1 (by rfl) ⟨119699, by rfl⟩ : syracuseStep 159599 = 239399) B239399
theorem B356777 : Blo 155795 356777 := bstep (se 2 (by rfl) ⟨133791, by rfl⟩ : syracuseStep 356777 = 267583) B267583
theorem B357083 : Blo 155795 357083 := bstep (se 1 (by rfl) ⟨267812, by rfl⟩ : syracuseStep 357083 = 535625) B535625
theorem B4551389 : Blo 155795 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B2290457 : Blo 155795 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B358055 : Blo 155795 358055 := bstep (se 1 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 358055 = 537083) B537083
theorem B1341521 : Blo 155795 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B13826419 : Blo 155795 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B1899487 : Blo 155795 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B818345 : Blo 155795 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B754721 : Blo 155795 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B394409 : Blo 155795 394409 := bstep (se 2 (by rfl) ⟨147903, by rfl⟩ : syracuseStep 394409 = 295807) B295807
theorem B4687409 : Blo 155795 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B263945 : Blo 155795 263945 := bstep (se 2 (by rfl) ⟨98979, by rfl⟩ : syracuseStep 263945 = 197959) B197959
theorem B395219 : Blo 155795 395219 := bstep (se 1 (by rfl) ⟨296414, by rfl⟩ : syracuseStep 395219 = 592829) B592829
theorem B2951585 : Blo 155795 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B526985 : Blo 155795 526985 := bstep (se 2 (by rfl) ⟨197619, by rfl⟩ : syracuseStep 526985 = 395239) B395239
theorem B1805003 : Blo 155795 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B855035 : Blo 155795 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B7311005 : Blo 155795 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1281703 : Blo 155795 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B790397 : Blo 155795 790397 := bstep (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) B296399
theorem B266287 : Blo 155795 266287 := bstep (se 1 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 266287 = 399431) B399431
theorem B233711 : Blo 155795 233711 := bstep (se 1 (by rfl) ⟨175283, by rfl⟩ : syracuseStep 233711 = 350567) B350567
theorem B561775 : Blo 155795 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B234095 : Blo 155795 234095 := bstep (se 1 (by rfl) ⟨175571, by rfl⟩ : syracuseStep 234095 = 351143) B351143
theorem B1348285 : Blo 155795 1348285 := bstep (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) B505607
theorem B299771 : Blo 155795 299771 := bstep (se 1 (by rfl) ⟨224828, by rfl⟩ : syracuseStep 299771 = 449657) B449657
theorem B604771093 : Blo 155795 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B2200715 : Blo 155795 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B398591 : Blo 155795 398591 := bstep (se 1 (by rfl) ⟨298943, by rfl⟩ : syracuseStep 398591 = 597887) B597887
theorem B234779 : Blo 155795 234779 := bstep (se 1 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 234779 = 352169) B352169
theorem B791855 : Blo 155795 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B3020111 : Blo 155795 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2266703 : Blo 155795 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B1349243 : Blo 155795 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B759721 : Blo 155795 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B235433 : Blo 155795 235433 := bstep (se 2 (by rfl) ⟨88287, by rfl⟩ : syracuseStep 235433 = 176575) B176575
theorem B399401 : Blo 155795 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B334201 : Blo 155795 334201 := bstep (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) B250651
theorem B531035 : Blo 155795 531035 := bstep (se 1 (by rfl) ⟨398276, by rfl⟩ : syracuseStep 531035 = 796553) B796553
theorem B6101729 : Blo 155795 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B269095 : Blo 155795 269095 := bstep (se 1 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 269095 = 403643) B403643
theorem B236651 : Blo 155795 236651 := bstep (se 1 (by rfl) ⟨177488, by rfl⟩ : syracuseStep 236651 = 354977) B354977
theorem B1383731 : Blo 155795 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B236891 : Blo 155795 236891 := bstep (se 1 (by rfl) ⟨177668, by rfl⟩ : syracuseStep 236891 = 355337) B355337
theorem B237851 : Blo 155795 237851 := bstep (se 1 (by rfl) ⟨178388, by rfl⟩ : syracuseStep 237851 = 356777) B356777
theorem B238055 : Blo 155795 238055 := bstep (se 1 (by rfl) ⟨178541, by rfl⟩ : syracuseStep 238055 = 357083) B357083
theorem B238505 : Blo 155795 238505 := bstep (se 2 (by rfl) ⟨89439, by rfl⟩ : syracuseStep 238505 = 178879) B178879
theorem B402401 : Blo 155795 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B795743 : Blo 155795 795743 := bstep (se 1 (by rfl) ⟨596807, by rfl⟩ : syracuseStep 795743 = 1193615) B1193615
theorem B238703 : Blo 155795 238703 := bstep (se 1 (by rfl) ⟨179027, by rfl⟩ : syracuseStep 238703 = 358055) B358055
theorem B2532649 : Blo 155795 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B238889 : Blo 155795 238889 := bstep (se 2 (by rfl) ⟨89583, by rfl⟩ : syracuseStep 238889 = 179167) B179167
theorem B894347 : Blo 155795 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B1123753 : Blo 155795 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B5383597 : Blo 155795 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B534491 : Blo 155795 534491 := bstep (se 1 (by rfl) ⟨400868, by rfl⟩ : syracuseStep 534491 = 801737) B801737
theorem B404129 : Blo 155795 404129 := bstep (se 2 (by rfl) ⟨151548, by rfl⟩ : syracuseStep 404129 = 303097) B303097
theorem B895805 : Blo 155795 895805 := bstep (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) B335927
theorem B404423 : Blo 155795 404423 := bstep (se 1 (by rfl) ⟨303317, by rfl⟩ : syracuseStep 404423 = 606635) B606635
theorem B3386555 : Blo 155795 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B339247 : Blo 155795 339247 := bstep (se 1 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 339247 = 508871) B508871
theorem B175567 : Blo 155795 175567 := bstep (se 1 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 175567 = 263351) B263351
theorem B601775 : Blo 155795 601775 := bstep (se 1 (by rfl) ⟨451331, by rfl⟩ : syracuseStep 601775 = 902663) B902663
theorem B601937 : Blo 155795 601937 := bstep (se 2 (by rfl) ⟨225726, by rfl⟩ : syracuseStep 601937 = 451453) B451453
theorem B176071 : Blo 155795 176071 := bstep (se 1 (by rfl) ⟨132053, by rfl⟩ : syracuseStep 176071 = 264107) B264107
theorem B176431 : Blo 155795 176431 := bstep (se 1 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 176431 = 264647) B264647
theorem B2798135 : Blo 155795 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B1520207 : Blo 155795 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B73740901 : Blo 155795 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B799631 : Blo 155795 799631 := bstep (se 1 (by rfl) ⟨599723, by rfl⟩ : syracuseStep 799631 = 1199447) B1199447
theorem B799955 : Blo 155795 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B4568507 : Blo 155795 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B801575 : Blo 155795 801575 := bstep (se 1 (by rfl) ⟨601181, by rfl⟩ : syracuseStep 801575 = 1202363) B1202363
theorem B670625 : Blo 155795 670625 := bstep (se 2 (by rfl) ⟨251484, by rfl⟩ : syracuseStep 670625 = 502969) B502969
theorem B1359017 : Blo 155795 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B1556221 : Blo 155795 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B1196531 : Blo 155795 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B7324445 : Blo 155795 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B803681 : Blo 155795 803681 := bstep (se 2 (by rfl) ⟨301380, by rfl⟩ : syracuseStep 803681 = 602761) B602761
theorem B804167 : Blo 155795 804167 := bstep (se 1 (by rfl) ⟨603125, by rfl⟩ : syracuseStep 804167 = 1206251) B1206251
theorem B968723 : Blo 155795 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B1132775 : Blo 155795 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B4311731 : Blo 155795 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1362743 : Blo 155795 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B3034259 : Blo 155795 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B1526971 : Blo 155795 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B4050917 : Blo 155795 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B545563 : Blo 155795 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B2446843 : Blo 155795 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B382859 : Blo 155795 382859 := bstep (se 1 (by rfl) ⟨287144, by rfl⟩ : syracuseStep 382859 = 574289) B574289
theorem B481751 : Blo 155795 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B350945 : Blo 155795 350945 := bstep (se 2 (by rfl) ⟨131604, by rfl⟩ : syracuseStep 350945 = 263209) B263209
theorem B351017 : Blo 155795 351017 := bstep (se 2 (by rfl) ⟨131631, by rfl⟩ : syracuseStep 351017 = 263263) B263263
theorem B14474159 : Blo 155795 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B285689 : Blo 155795 285689 := bstep (se 2 (by rfl) ⟨107133, by rfl⟩ : syracuseStep 285689 = 214267) B214267
theorem B449999 : Blo 155795 449999 := bstep (se 1 (by rfl) ⟨337499, by rfl⟩ : syracuseStep 449999 = 674999) B674999
theorem B5758613 : Blo 155795 5758613 := bstep (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) B269935
theorem B1236905 : Blo 155795 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B156251 : Blo 155795 156251 := bstep (se 1 (by rfl) ⟨117188, by rfl⟩ : syracuseStep 156251 = 234377) B234377
theorem B451183 : Blo 155795 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B353051 : Blo 155795 353051 := bstep (se 1 (by rfl) ⟨264788, by rfl⟩ : syracuseStep 353051 = 529577) B529577
theorem B353087 : Blo 155795 353087 := bstep (se 1 (by rfl) ⟨264815, by rfl⟩ : syracuseStep 353087 = 529631) B529631
theorem B353231 : Blo 155795 353231 := bstep (se 1 (by rfl) ⟨264923, by rfl⟩ : syracuseStep 353231 = 529847) B529847
theorem B1139923 : Blo 155795 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B353627 : Blo 155795 353627 := bstep (se 1 (by rfl) ⟨265220, by rfl⟩ : syracuseStep 353627 = 530441) B530441
theorem B157275 : Blo 155795 157275 := bstep (se 1 (by rfl) ⟨117956, by rfl⟩ : syracuseStep 157275 = 235913) B235913
theorem B157391 : Blo 155795 157391 := bstep (se 1 (by rfl) ⟨118043, by rfl⟩ : syracuseStep 157391 = 236087) B236087
theorem B6842303 : Blo 155795 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B3401777 : Blo 155795 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B452699 : Blo 155795 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B157863 : Blo 155795 157863 := bstep (se 1 (by rfl) ⟨118397, by rfl⟩ : syracuseStep 157863 = 236795) B236795
theorem B354491 : Blo 155795 354491 := bstep (se 1 (by rfl) ⟨265868, by rfl⟩ : syracuseStep 354491 = 531737) B531737
theorem B157947 : Blo 155795 157947 := bstep (se 1 (by rfl) ⟨118460, by rfl⟩ : syracuseStep 157947 = 236921) B236921
theorem B158107 : Blo 155795 158107 := bstep (se 1 (by rfl) ⟨118580, by rfl⟩ : syracuseStep 158107 = 237161) B237161
theorem B2320903 : Blo 155795 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B354959 : Blo 155795 354959 := bstep (se 1 (by rfl) ⟨266219, by rfl⟩ : syracuseStep 354959 = 532439) B532439
theorem B1141769 : Blo 155795 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B1371161 : Blo 155795 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B158875 : Blo 155795 158875 := bstep (se 1 (by rfl) ⟨119156, by rfl⟩ : syracuseStep 158875 = 238313) B238313
theorem B158887 : Blo 155795 158887 := bstep (se 1 (by rfl) ⟨119165, by rfl⟩ : syracuseStep 158887 = 238331) B238331
theorem B1207709 : Blo 155795 1207709 := bstep (se 3 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 1207709 = 452891) B452891
theorem B1502675 : Blo 155795 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B159231 : Blo 155795 159231 := bstep (se 1 (by rfl) ⟨119423, by rfl⟩ : syracuseStep 159231 = 238847) B238847
theorem B159439 : Blo 155795 159439 := bstep (se 1 (by rfl) ⟨119579, by rfl⟩ : syracuseStep 159439 = 239159) B239159
theorem B356219 : Blo 155795 356219 := bstep (se 1 (by rfl) ⟨267164, by rfl⟩ : syracuseStep 356219 = 534329) B534329
theorem B159679 : Blo 155795 159679 := bstep (se 1 (by rfl) ⟨119759, by rfl⟩ : syracuseStep 159679 = 239519) B239519
theorem B356507 : Blo 155795 356507 := bstep (se 1 (by rfl) ⟨267380, by rfl⟩ : syracuseStep 356507 = 534761) B534761
theorem B356795 : Blo 155795 356795 := bstep (se 1 (by rfl) ⟨267596, by rfl⟩ : syracuseStep 356795 = 535193) B535193
theorem B3437417 : Blo 155795 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B423451 : Blo 155795 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B358163 : Blo 155795 358163 := bstep (se 1 (by rfl) ⟨268622, by rfl⟩ : syracuseStep 358163 = 537245) B537245
theorem B358235 : Blo 155795 358235 := bstep (se 1 (by rfl) ⟨268676, by rfl⟩ : syracuseStep 358235 = 537353) B537353
theorem B751531 : Blo 155795 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B359207 : Blo 155795 359207 := bstep (se 1 (by rfl) ⟨269405, by rfl⟩ : syracuseStep 359207 = 538811) B538811
theorem B752723 : Blo 155795 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B4882963 : Blo 155795 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B262939 : Blo 155795 262939 := bstep (se 1 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 262939 = 394409) B394409
theorem B263479 : Blo 155795 263479 := bstep (se 1 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 263479 = 395219) B395219
theorem B755183 : Blo 155795 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B1967723 : Blo 155795 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B3376865 : Blo 155795 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B7178129 : Blo 155795 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B526931 : Blo 155795 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B199847 : Blo 155795 199847 := bstep (se 1 (by rfl) ⟨149885, by rfl⟩ : syracuseStep 199847 = 299771) B299771
theorem B265727 : Blo 155795 265727 := bstep (se 1 (by rfl) ⟨199295, by rfl⟩ : syracuseStep 265727 = 398591) B398591
theorem B527903 : Blo 155795 527903 := bstep (se 1 (by rfl) ⟨395927, by rfl⟩ : syracuseStep 527903 = 791855) B791855
theorem B1511135 : Blo 155795 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B266267 : Blo 155795 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B2035961 : Blo 155795 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B233963 : Blo 155795 233963 := bstep (se 1 (by rfl) ⟨175472, by rfl⟩ : syracuseStep 233963 = 350945) B350945
theorem B4067819 : Blo 155795 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B234011 : Blo 155795 234011 := bstep (se 1 (by rfl) ⟨175508, by rfl⟩ : syracuseStep 234011 = 351017) B351017
theorem B234089 : Blo 155795 234089 := bstep (se 2 (by rfl) ⟨87783, by rfl⟩ : syracuseStep 234089 = 175567) B175567
theorem B922487 : Blo 155795 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1708937 : Blo 155795 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B299999 : Blo 155795 299999 := bstep (se 1 (by rfl) ⟨224999, by rfl⟩ : syracuseStep 299999 = 449999) B449999
theorem B3839075 : Blo 155795 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B234761 : Blo 155795 234761 := bstep (se 2 (by rfl) ⟨88035, by rfl⟩ : syracuseStep 234761 = 176071) B176071
theorem B824603 : Blo 155795 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B235241 : Blo 155795 235241 := bstep (se 2 (by rfl) ⟨88215, by rfl⟩ : syracuseStep 235241 = 176431) B176431
theorem B235367 : Blo 155795 235367 := bstep (se 1 (by rfl) ⟨176525, by rfl⟩ : syracuseStep 235367 = 353051) B353051
theorem B235391 : Blo 155795 235391 := bstep (se 1 (by rfl) ⟨176543, by rfl⟩ : syracuseStep 235391 = 353087) B353087
theorem B235487 : Blo 155795 235487 := bstep (se 1 (by rfl) ⟨176615, by rfl⟩ : syracuseStep 235487 = 353231) B353231
theorem B268267 : Blo 155795 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B530495 : Blo 155795 530495 := bstep (se 1 (by rfl) ⟨397871, by rfl⟩ : syracuseStep 530495 = 795743) B795743
theorem B235751 : Blo 155795 235751 := bstep (se 1 (by rfl) ⟨176813, by rfl⟩ : syracuseStep 235751 = 353627) B353627
theorem B596231 : Blo 155795 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B727417 : Blo 155795 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B4561535 : Blo 155795 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B2267851 : Blo 155795 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B301799 : Blo 155795 301799 := bstep (se 1 (by rfl) ⟨226349, by rfl⟩ : syracuseStep 301799 = 452699) B452699
theorem B236327 : Blo 155795 236327 := bstep (se 1 (by rfl) ⟨177245, by rfl⟩ : syracuseStep 236327 = 354491) B354491
theorem B1809317 : Blo 155795 1809317 := bstep (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) B339247
theorem B236639 : Blo 155795 236639 := bstep (se 1 (by rfl) ⟨177479, by rfl⟩ : syracuseStep 236639 = 354959) B354959
theorem B269419 : Blo 155795 269419 := bstep (se 1 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 269419 = 404129) B404129
theorem B597203 : Blo 155795 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B269615 : Blo 155795 269615 := bstep (se 1 (by rfl) ⟨202211, by rfl⟩ : syracuseStep 269615 = 404423) B404423
theorem B761179 : Blo 155795 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B401183 : Blo 155795 401183 := bstep (se 1 (by rfl) ⟨300887, by rfl⟩ : syracuseStep 401183 = 601775) B601775
theorem B401291 : Blo 155795 401291 := bstep (se 1 (by rfl) ⟨300968, by rfl⟩ : syracuseStep 401291 = 601937) B601937
theorem B237479 : Blo 155795 237479 := bstep (se 1 (by rfl) ⟨178109, by rfl⟩ : syracuseStep 237479 = 356219) B356219
theorem B237671 : Blo 155795 237671 := bstep (se 1 (by rfl) ⟨178253, by rfl⟩ : syracuseStep 237671 = 356507) B356507
theorem B237863 : Blo 155795 237863 := bstep (se 1 (by rfl) ⟨178397, by rfl⟩ : syracuseStep 237863 = 356795) B356795
theorem B533087 : Blo 155795 533087 := bstep (se 1 (by rfl) ⟨399815, by rfl⟩ : syracuseStep 533087 = 799631) B799631
theorem B533303 : Blo 155795 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B238775 : Blo 155795 238775 := bstep (se 1 (by rfl) ⟨179081, by rfl⟩ : syracuseStep 238775 = 358163) B358163
theorem B238823 : Blo 155795 238823 := bstep (se 1 (by rfl) ⟨179117, by rfl⟩ : syracuseStep 238823 = 358235) B358235
theorem B534383 : Blo 155795 534383 := bstep (se 1 (by rfl) ⟨400787, by rfl⟩ : syracuseStep 534383 = 801575) B801575
theorem B239471 : Blo 155795 239471 := bstep (se 1 (by rfl) ⟨179603, by rfl⟩ : syracuseStep 239471 = 359207) B359207
theorem B501815 : Blo 155795 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B2074961 : Blo 155795 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B797687 : Blo 155795 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B535787 : Blo 155795 535787 := bstep (se 1 (by rfl) ⟨401840, by rfl⟩ : syracuseStep 535787 = 803681) B803681
theorem B503147 : Blo 155795 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B601577 : Blo 155795 601577 := bstep (se 2 (by rfl) ⟨225591, by rfl⟩ : syracuseStep 601577 = 451183) B451183
theorem B536111 : Blo 155795 536111 := bstep (se 1 (by rfl) ⟨402083, by rfl⟩ : syracuseStep 536111 = 804167) B804167
theorem B3124939 : Blo 155795 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B175963 : Blo 155795 175963 := bstep (se 1 (by rfl) ⟨131972, by rfl⟩ : syracuseStep 175963 = 263945) B263945
theorem B1519897 : Blo 155795 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B570023 : Blo 155795 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B2700611 : Blo 155795 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B3094537 : Blo 155795 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2013407 : Blo 155795 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B899495 : Blo 155795 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B9649439 : Blo 155795 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B98321201 : Blo 155795 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B3262457 : Blo 155795 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B805139 : Blo 155795 805139 := bstep (se 1 (by rfl) ⟨603854, by rfl⟩ : syracuseStep 805139 = 1207709) B1207709
theorem B1001783 : Blo 155795 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B1002041 : Blo 155795 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B445601 : Blo 155795 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B447083 : Blo 155795 447083 := bstep (se 1 (by rfl) ⟨335312, by rfl⟩ : syracuseStep 447083 = 670625) B670625
theorem B906011 : Blo 155795 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B645815 : Blo 155795 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B351323 : Blo 155795 351323 := bstep (se 1 (by rfl) ⟨263492, by rfl⟩ : syracuseStep 351323 = 526985) B526985
theorem B1203335 : Blo 155795 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B908495 : Blo 155795 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B1498337 : Blo 155795 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B2022839 : Blo 155795 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B4874003 : Blo 155795 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B155807 : Blo 155795 155807 := bstep (se 1 (by rfl) ⟨116855, by rfl⟩ : syracuseStep 155807 = 233711) B233711
theorem B156063 : Blo 155795 156063 := bstep (se 1 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 156063 = 234095) B234095
theorem B1467143 : Blo 155795 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B156519 : Blo 155795 156519 := bstep (se 1 (by rfl) ⟨117389, by rfl⟩ : syracuseStep 156519 = 234779) B234779
theorem B255239 : Blo 155795 255239 := bstep (se 1 (by rfl) ⟨191429, by rfl⟩ : syracuseStep 255239 = 382859) B382859
theorem B156955 : Blo 155795 156955 := bstep (se 1 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 156955 = 235433) B235433
theorem B3225445829 : Blo 155795 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B321167 : Blo 155795 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B354023 : Blo 155795 354023 := bstep (se 1 (by rfl) ⟨265517, by rfl⟩ : syracuseStep 354023 = 531035) B531035
theorem B190459 : Blo 155795 190459 := bstep (se 1 (by rfl) ⟨142844, by rfl⟩ : syracuseStep 190459 = 285689) B285689
theorem B157767 : Blo 155795 157767 := bstep (se 1 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 157767 = 236651) B236651
theorem B157927 : Blo 155795 157927 := bstep (se 1 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 157927 = 236891) B236891
theorem B355049 : Blo 155795 355049 := bstep (se 2 (by rfl) ⟨133143, by rfl⟩ : syracuseStep 355049 = 266287) B266287
theorem B158567 : Blo 155795 158567 := bstep (se 1 (by rfl) ⟨118925, by rfl⟩ : syracuseStep 158567 = 237851) B237851
theorem B158703 : Blo 155795 158703 := bstep (se 1 (by rfl) ⟨119027, by rfl⟩ : syracuseStep 158703 = 238055) B238055
theorem B159003 : Blo 155795 159003 := bstep (se 1 (by rfl) ⟨119252, by rfl⟩ : syracuseStep 159003 = 238505) B238505
theorem B159135 : Blo 155795 159135 := bstep (se 1 (by rfl) ⟨119351, by rfl⟩ : syracuseStep 159135 = 238703) B238703
theorem B749033 : Blo 155795 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B159259 : Blo 155795 159259 := bstep (se 1 (by rfl) ⟨119444, by rfl⟩ : syracuseStep 159259 = 238889) B238889
theorem B1797713 : Blo 155795 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B356327 : Blo 155795 356327 := bstep (se 1 (by rfl) ⟨267245, by rfl⟩ : syracuseStep 356327 = 534491) B534491
theorem B11497949 : Blo 155795 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B914107 : Blo 155795 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B2257703 : Blo 155795 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B1012961 : Blo 155795 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B2258405 : Blo 155795 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B1865423 : Blo 155795 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1013471 : Blo 155795 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B2291611 : Blo 155795 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B3045671 : Blo 155795 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B358793 : Blo 155795 358793 := bstep (se 2 (by rfl) ⟨134547, by rfl⟩ : syracuseStep 358793 = 269095) B269095
theorem B1311815 : Blo 155795 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B4785419 : Blo 155795 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B2459965 : Blo 155795 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B298055 : Blo 155795 298055 := bstep (se 1 (by rfl) ⟨223541, by rfl⟩ : syracuseStep 298055 = 447083) B447083
theorem B199999 : Blo 155795 199999 := bstep (se 1 (by rfl) ⟨149999, by rfl⟩ : syracuseStep 199999 = 299999) B299999
theorem B2559383 : Blo 155795 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B397487 : Blo 155795 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B430543 : Blo 155795 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B201199 : Blo 155795 201199 := bstep (se 1 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 201199 = 301799) B301799
theorem B234215 : Blo 155795 234215 := bstep (se 1 (by rfl) ⟨175661, by rfl⟩ : syracuseStep 234215 = 351323) B351323
theorem B398135 : Blo 155795 398135 := bstep (se 1 (by rfl) ⟨298601, by rfl⟩ : syracuseStep 398135 = 597203) B597203
theorem B4166585 : Blo 155795 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1348559 : Blo 155795 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B234617 : Blo 155795 234617 := bstep (se 2 (by rfl) ⟨87981, by rfl⟩ : syracuseStep 234617 = 175963) B175963
theorem B3249335 : Blo 155795 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B267455 : Blo 155795 267455 := bstep (se 1 (by rfl) ⟨200591, by rfl⟩ : syracuseStep 267455 = 401183) B401183
theorem B267527 : Blo 155795 267527 := bstep (se 1 (by rfl) ⟨200645, by rfl⟩ : syracuseStep 267527 = 401291) B401291
theorem B170159 : Blo 155795 170159 := bstep (se 1 (by rfl) ⟨127619, by rfl⟩ : syracuseStep 170159 = 255239) B255239
theorem B1218809 : Blo 155795 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B236015 : Blo 155795 236015 := bstep (se 1 (by rfl) ⟨177011, by rfl⟩ : syracuseStep 236015 = 354023) B354023
theorem B334543 : Blo 155795 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B1383307 : Blo 155795 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B236699 : Blo 155795 236699 := bstep (se 1 (by rfl) ⟨177524, by rfl⟩ : syracuseStep 236699 = 355049) B355049
theorem B531791 : Blo 155795 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B335431 : Blo 155795 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B499355 : Blo 155795 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B401051 : Blo 155795 401051 := bstep (se 1 (by rfl) ⟨300788, by rfl⟩ : syracuseStep 401051 = 601577) B601577
theorem B3055481 : Blo 155795 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B237551 : Blo 155795 237551 := bstep (se 1 (by rfl) ⟨178163, by rfl⟩ : syracuseStep 237551 = 356327) B356327
theorem B1188269 : Blo 155795 1188269 := bstep (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) B445601
theorem B532925 : Blo 155795 532925 := bstep (se 3 (by rfl) ⟨99923, by rfl⟩ : syracuseStep 532925 = 199847) B199847
theorem B3023801 : Blo 155795 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B239195 : Blo 155795 239195 := bstep (se 1 (by rfl) ⟨179396, by rfl⟩ : syracuseStep 239195 = 358793) B358793
theorem B599663 : Blo 155795 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B6432959 : Blo 155795 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B65547467 : Blo 155795 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B503455 : Blo 155795 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B536759 : Blo 155795 536759 := bstep (se 1 (by rfl) ⟨402569, by rfl⟩ : syracuseStep 536759 = 805139) B805139
theorem B667855 : Blo 155795 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B668027 : Blo 155795 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B177151 : Blo 155795 177151 := bstep (se 1 (by rfl) ⟨132863, by rfl⟩ : syracuseStep 177151 = 265727) B265727
theorem B177511 : Blo 155795 177511 := bstep (se 1 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 177511 = 266267) B266267
theorem B1357307 : Blo 155795 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B8795765 : Blo 155795 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B604007 : Blo 155795 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B802223 : Blo 155795 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B605663 : Blo 155795 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B998891 : Blo 155795 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B179743 : Blo 155795 179743 := bstep (se 1 (by rfl) ⟨134807, by rfl⟩ : syracuseStep 179743 = 269615) B269615
theorem B8699885 : Blo 155795 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B214111 : Blo 155795 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B1198475 : Blo 155795 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B380015 : Blo 155795 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B969889 : Blo 155795 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B675307 : Blo 155795 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B675647 : Blo 155795 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B6510617 : Blo 155795 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B350585 : Blo 155795 350585 := bstep (se 2 (by rfl) ⟨131469, by rfl⟩ : syracuseStep 350585 = 262939) B262939
theorem B2251243 : Blo 155795 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B351287 : Blo 155795 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B351305 : Blo 155795 351305 := bstep (se 2 (by rfl) ⟨131739, by rfl⟩ : syracuseStep 351305 = 263479) B263479
theorem B351935 : Blo 155795 351935 := bstep (se 1 (by rfl) ⟨263951, by rfl⟩ : syracuseStep 351935 = 527903) B527903
theorem B1007423 : Blo 155795 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B253945 : Blo 155795 253945 := bstep (se 2 (by rfl) ⟨95229, by rfl⟩ : syracuseStep 253945 = 190459) B190459
theorem B155975 : Blo 155795 155975 := bstep (se 1 (by rfl) ⟨116981, by rfl⟩ : syracuseStep 155975 = 233963) B233963
theorem B2711879 : Blo 155795 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B156007 : Blo 155795 156007 := bstep (se 1 (by rfl) ⟨117005, by rfl⟩ : syracuseStep 156007 = 234011) B234011
theorem B156059 : Blo 155795 156059 := bstep (se 1 (by rfl) ⟨117044, by rfl⟩ : syracuseStep 156059 = 234089) B234089
theorem B1139291 : Blo 155795 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B156507 : Blo 155795 156507 := bstep (se 1 (by rfl) ⟨117380, by rfl⟩ : syracuseStep 156507 = 234761) B234761
theorem B156827 : Blo 155795 156827 := bstep (se 1 (by rfl) ⟨117620, by rfl⟩ : syracuseStep 156827 = 235241) B235241
theorem B156911 : Blo 155795 156911 := bstep (se 1 (by rfl) ⟨117683, by rfl⟩ : syracuseStep 156911 = 235367) B235367
theorem B156927 : Blo 155795 156927 := bstep (se 1 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 156927 = 235391) B235391
theorem B156991 : Blo 155795 156991 := bstep (se 1 (by rfl) ⟨117743, by rfl⟩ : syracuseStep 156991 = 235487) B235487
theorem B353663 : Blo 155795 353663 := bstep (se 1 (by rfl) ⟨265247, by rfl⟩ : syracuseStep 353663 = 530495) B530495
theorem B157167 : Blo 155795 157167 := bstep (se 1 (by rfl) ⟨117875, by rfl⟩ : syracuseStep 157167 = 235751) B235751
theorem B3041023 : Blo 155795 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B157551 : Blo 155795 157551 := bstep (se 1 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 157551 = 236327) B236327
theorem B1206211 : Blo 155795 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B157759 : Blo 155795 157759 := bstep (se 1 (by rfl) ⟨118319, by rfl⟩ : syracuseStep 157759 = 236639) B236639
theorem B158319 : Blo 155795 158319 := bstep (se 1 (by rfl) ⟨118739, by rfl⟩ : syracuseStep 158319 = 237479) B237479
theorem B158447 : Blo 155795 158447 := bstep (se 1 (by rfl) ⟨118835, by rfl⟩ : syracuseStep 158447 = 237671) B237671
theorem B158575 : Blo 155795 158575 := bstep (se 1 (by rfl) ⟨118931, by rfl⟩ : syracuseStep 158575 = 237863) B237863
theorem B2026529 : Blo 155795 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B355391 : Blo 155795 355391 := bstep (se 1 (by rfl) ⟨266543, by rfl⟩ : syracuseStep 355391 = 533087) B533087
theorem B978095 : Blo 155795 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B355535 : Blo 155795 355535 := bstep (se 1 (by rfl) ⟨266651, by rfl⟩ : syracuseStep 355535 = 533303) B533303
theorem B159183 : Blo 155795 159183 := bstep (se 1 (by rfl) ⟨119387, by rfl⟩ : syracuseStep 159183 = 238775) B238775
theorem B159215 : Blo 155795 159215 := bstep (se 1 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 159215 = 238823) B238823
theorem B2150297219 : Blo 155795 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B356255 : Blo 155795 356255 := bstep (se 1 (by rfl) ⟨267191, by rfl⟩ : syracuseStep 356255 = 534383) B534383
theorem B159647 : Blo 155795 159647 := bstep (se 1 (by rfl) ⟨119735, by rfl⟩ : syracuseStep 159647 = 239471) B239471
theorem B357191 : Blo 155795 357191 := bstep (se 1 (by rfl) ⟨267893, by rfl⟩ : syracuseStep 357191 = 535787) B535787
theorem B357407 : Blo 155795 357407 := bstep (se 1 (by rfl) ⟨268055, by rfl⟩ : syracuseStep 357407 = 536111) B536111
theorem B357689 : Blo 155795 357689 := bstep (se 2 (by rfl) ⟨134133, by rfl⟩ : syracuseStep 357689 = 268267) B268267
theorem B4126049 : Blo 155795 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B7665299 : Blo 155795 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B1505135 : Blo 155795 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B1800407 : Blo 155795 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1505603 : Blo 155795 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B1243615 : Blo 155795 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B359225 : Blo 155795 359225 := bstep (se 2 (by rfl) ⟨134709, by rfl⟩ : syracuseStep 359225 = 269419) B269419
theorem B1342271 : Blo 155795 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B2030447 : Blo 155795 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1014905 : Blo 155795 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B198703 : Blo 155795 198703 := bstep (se 1 (by rfl) ⟨149027, by rfl⟩ : syracuseStep 198703 = 298055) B298055
theorem B1706255 : Blo 155795 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1608281 : Blo 155795 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B264991 : Blo 155795 264991 := bstep (se 1 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 264991 = 397487) B397487
theorem B3279953 : Blo 155795 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B265423 : Blo 155795 265423 := bstep (se 1 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 265423 = 398135) B398135
theorem B2166223 : Blo 155795 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B233723 : Blo 155795 233723 := bstep (se 1 (by rfl) ⟨175292, by rfl⟩ : syracuseStep 233723 = 350585) B350585
theorem B266665 : Blo 155795 266665 := bstep (se 2 (by rfl) ⟨99999, by rfl⟩ : syracuseStep 266665 = 199999) B199999
theorem B234191 : Blo 155795 234191 := bstep (se 1 (by rfl) ⟨175643, by rfl⟩ : syracuseStep 234191 = 351287) B351287
theorem B234203 : Blo 155795 234203 := bstep (se 1 (by rfl) ⟨175652, by rfl⟩ : syracuseStep 234203 = 351305) B351305
theorem B7377637 : Blo 155795 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B332903 : Blo 155795 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B267367 : Blo 155795 267367 := bstep (se 1 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 267367 = 401051) B401051
theorem B234623 : Blo 155795 234623 := bstep (se 1 (by rfl) ⟨175967, by rfl⟩ : syracuseStep 234623 = 351935) B351935
theorem B2036987 : Blo 155795 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B1807919 : Blo 155795 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B890473 : Blo 155795 890473 := bstep (se 2 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 890473 = 667855) B667855
theorem B792179 : Blo 155795 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B759527 : Blo 155795 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B268265 : Blo 155795 268265 := bstep (se 2 (by rfl) ⟨100599, by rfl⟩ : syracuseStep 268265 = 201199) B201199
theorem B235775 : Blo 155795 235775 := bstep (se 1 (by rfl) ⟨176831, by rfl⟩ : syracuseStep 235775 = 353663) B353663
theorem B399775 : Blo 155795 399775 := bstep (se 1 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 399775 = 599663) B599663
theorem B236201 : Blo 155795 236201 := bstep (se 2 (by rfl) ⟨88575, by rfl⟩ : syracuseStep 236201 = 177151) B177151
theorem B236681 : Blo 155795 236681 := bstep (se 2 (by rfl) ⟨88755, by rfl⟩ : syracuseStep 236681 = 177511) B177511
theorem B1351019 : Blo 155795 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B236927 : Blo 155795 236927 := bstep (se 1 (by rfl) ⟨177695, by rfl⟩ : syracuseStep 236927 = 355391) B355391
theorem B237023 : Blo 155795 237023 := bstep (se 1 (by rfl) ⟨177767, by rfl⟩ : syracuseStep 237023 = 355535) B355535
theorem B237503 : Blo 155795 237503 := bstep (se 1 (by rfl) ⟨178127, by rfl⟩ : syracuseStep 237503 = 356255) B356255
theorem B238127 : Blo 155795 238127 := bstep (se 1 (by rfl) ⟨178595, by rfl⟩ : syracuseStep 238127 = 357191) B357191
theorem B238271 : Blo 155795 238271 := bstep (se 1 (by rfl) ⟨178703, by rfl⟩ : syracuseStep 238271 = 357407) B357407
theorem B238459 : Blo 155795 238459 := bstep (se 1 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 238459 = 357689) B357689
theorem B402671 : Blo 155795 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B239483 : Blo 155795 239483 := bstep (se 1 (by rfl) ⟨179612, by rfl⟩ : syracuseStep 239483 = 359225) B359225
theorem B894847 : Blo 155795 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B1353631 : Blo 155795 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B239657 : Blo 155795 239657 := bstep (se 2 (by rfl) ⟨89871, by rfl⟩ : syracuseStep 239657 = 179743) B179743
theorem B534815 : Blo 155795 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B403775 : Blo 155795 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B665927 : Blo 155795 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B338593 : Blo 155795 338593 := bstep (se 2 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 338593 = 253945) B253945
theorem B3190279 : Blo 155795 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B798983 : Blo 155795 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B899039 : Blo 155795 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B178303 : Blo 155795 178303 := bstep (se 1 (by rfl) ⟨133727, by rfl⟩ : syracuseStep 178303 = 267455) B267455
theorem B178351 : Blo 155795 178351 := bstep (se 1 (by rfl) ⟨133763, by rfl⟩ : syracuseStep 178351 = 267527) B267527
theorem B4340411 : Blo 155795 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B1293185 : Blo 155795 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B900409 : Blo 155795 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B671273 : Blo 155795 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B671615 : Blo 155795 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B574057 : Blo 155795 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B2015867 : Blo 155795 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B43698311 : Blo 155795 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B445351 : Blo 155795 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B1788965 : Blo 155795 1788965 := bstep (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) B335431
theorem B1658153 : Blo 155795 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B3001657 : Blo 155795 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B446057 : Blo 155795 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B904871 : Blo 155795 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B1003423 : Blo 155795 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B1200271 : Blo 155795 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1003735 : Blo 155795 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B5734125917 : Blo 155795 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B676603 : Blo 155795 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B285481 : Blo 155795 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B253343 : Blo 155795 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B4054697 : Blo 155795 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B450431 : Blo 155795 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B3498173 : Blo 155795 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B156143 : Blo 155795 156143 := bstep (se 1 (by rfl) ⟨117107, by rfl⟩ : syracuseStep 156143 = 234215) B234215
theorem B2777723 : Blo 155795 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B156411 : Blo 155795 156411 := bstep (se 1 (by rfl) ⟨117308, by rfl⟩ : syracuseStep 156411 = 234617) B234617
theorem B812539 : Blo 155795 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B157343 : Blo 155795 157343 := bstep (se 1 (by rfl) ⟨118007, by rfl⟩ : syracuseStep 157343 = 236015) B236015
theorem B157799 : Blo 155795 157799 := bstep (se 1 (by rfl) ⟨118349, by rfl⟩ : syracuseStep 157799 = 236699) B236699
theorem B354527 : Blo 155795 354527 := bstep (se 1 (by rfl) ⟨265895, by rfl⟩ : syracuseStep 354527 = 531791) B531791
theorem B158367 : Blo 155795 158367 := bstep (se 1 (by rfl) ⟨118775, by rfl⟩ : syracuseStep 158367 = 237551) B237551
theorem B355283 : Blo 155795 355283 := bstep (se 1 (by rfl) ⟨266462, by rfl⟩ : syracuseStep 355283 = 532925) B532925
theorem B453757 : Blo 155795 453757 := bstep (se 3 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 453757 = 170159) B170159
theorem B159463 : Blo 155795 159463 := bstep (se 1 (by rfl) ⟨119597, by rfl⟩ : syracuseStep 159463 = 239195) B239195
theorem B4288639 : Blo 155795 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B652063 : Blo 155795 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B357839 : Blo 155795 357839 := bstep (se 1 (by rfl) ⟨268379, by rfl⟩ : syracuseStep 357839 = 536759) B536759
theorem B2750699 : Blo 155795 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B5863843 : Blo 155795 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B5110199 : Blo 155795 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B5799923 : Blo 155795 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B1343911 : Blo 155795 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B951205 : Blo 155795 951205 := bstep (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) B178351
theorem B29132207 : Blo 155795 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1083385 : Blo 155795 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B297371 : Blo 155795 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B1804841 : Blo 155795 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B264937 : Blo 155795 264937 := bstep (se 2 (by rfl) ⟨99351, by rfl⟩ : syracuseStep 264937 = 198703) B198703
theorem B3822750611 : Blo 155795 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B528119 : Blo 155795 528119 := bstep (se 1 (by rfl) ⟨396089, by rfl⟩ : syracuseStep 528119 = 792179) B792179
theorem B593801 : Blo 155795 593801 := bstep (se 2 (by rfl) ⟨222675, by rfl⟩ : syracuseStep 593801 = 445351) B445351
theorem B4002209 : Blo 155795 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B2888297 : Blo 155795 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B168895 : Blo 155795 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B300287 : Blo 155795 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B2332115 : Blo 155795 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B268447 : Blo 155795 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B9836849 : Blo 155795 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B236351 : Blo 155795 236351 := bstep (se 1 (by rfl) ⟨177263, by rfl⟩ : syracuseStep 236351 = 354527) B354527
theorem B269183 : Blo 155795 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B236855 : Blo 155795 236855 := bstep (se 1 (by rfl) ⟨177641, by rfl⟩ : syracuseStep 236855 = 355283) B355283
theorem B1187297 : Blo 155795 1187297 := bstep (se 2 (by rfl) ⟨445236, by rfl⟩ : syracuseStep 1187297 = 890473) B890473
theorem B237737 : Blo 155795 237737 := bstep (se 2 (by rfl) ⟨89151, by rfl⟩ : syracuseStep 237737 = 178303) B178303
theorem B532655 : Blo 155795 532655 := bstep (se 1 (by rfl) ⟨399491, by rfl⟩ : syracuseStep 532655 = 798983) B798983
theorem B533033 : Blo 155795 533033 := bstep (se 2 (by rfl) ⟨199887, by rfl⟩ : syracuseStep 533033 = 399775) B399775
theorem B238559 : Blo 155795 238559 := bstep (se 1 (by rfl) ⟨178919, by rfl⟩ : syracuseStep 238559 = 357839) B357839
theorem B599359 : Blo 155795 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B2893607 : Blo 155795 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B862123 : Blo 155795 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B765409 : Blo 155795 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B5353253 : Blo 155795 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B1192643 : Blo 155795 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B603247 : Blo 155795 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B1193129 : Blo 155795 1193129 := bstep (se 2 (by rfl) ⟨447423, by rfl⟩ : syracuseStep 1193129 = 894847) B894847
theorem B1357991 : Blo 155795 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B506351 : Blo 155795 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B178843 : Blo 155795 178843 := bstep (se 1 (by rfl) ⟨134132, by rfl⟩ : syracuseStep 178843 = 268265) B268265
theorem B605009 : Blo 155795 605009 := bstep (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) B453757
theorem B900679 : Blo 155795 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B2703131 : Blo 155795 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B5718185 : Blo 155795 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B1851815 : Blo 155795 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B902137 : Blo 155795 902137 := bstep (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) B676603
theorem B869417 : Blo 155795 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B443951 : Blo 155795 443951 := bstep (se 1 (by rfl) ⟨332963, by rfl⟩ : syracuseStep 443951 = 665927) B665927
theorem B7818457 : Blo 155795 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B380641 : Blo 155795 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B1200545 : Blo 155795 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B447515 : Blo 155795 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B447743 : Blo 155795 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B317945 : Blo 155795 317945 := bstep (se 2 (by rfl) ⟨119229, by rfl⟩ : syracuseStep 317945 = 238459) B238459
theorem B1137503 : Blo 155795 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B1072187 : Blo 155795 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B2186635 : Blo 155795 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B1105435 : Blo 155795 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B155815 : Blo 155795 155815 := bstep (se 1 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 155815 = 233723) B233723
theorem B156127 : Blo 155795 156127 := bstep (se 1 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 156127 = 234191) B234191
theorem B156135 : Blo 155795 156135 := bstep (se 1 (by rfl) ⟨117101, by rfl⟩ : syracuseStep 156135 = 234203) B234203
theorem B221935 : Blo 155795 221935 := bstep (se 1 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 221935 = 332903) B332903
theorem B156415 : Blo 155795 156415 := bstep (se 1 (by rfl) ⟨117311, by rfl⟩ : syracuseStep 156415 = 234623) B234623
theorem B451457 : Blo 155795 451457 := bstep (se 2 (by rfl) ⟨169296, by rfl⟩ : syracuseStep 451457 = 338593) B338593
theorem B1205279 : Blo 155795 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B353321 : Blo 155795 353321 := bstep (se 2 (by rfl) ⟨132495, by rfl⟩ : syracuseStep 353321 = 264991) B264991
theorem B157183 : Blo 155795 157183 := bstep (se 1 (by rfl) ⟨117887, by rfl⟩ : syracuseStep 157183 = 235775) B235775
theorem B353897 : Blo 155795 353897 := bstep (se 2 (by rfl) ⟨132711, by rfl⟩ : syracuseStep 353897 = 265423) B265423
theorem B157467 : Blo 155795 157467 := bstep (se 1 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 157467 = 236201) B236201
theorem B4253705 : Blo 155795 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B157787 : Blo 155795 157787 := bstep (se 1 (by rfl) ⟨118340, by rfl⟩ : syracuseStep 157787 = 236681) B236681
theorem B157951 : Blo 155795 157951 := bstep (se 1 (by rfl) ⟨118463, by rfl⟩ : syracuseStep 157951 = 236927) B236927
theorem B158015 : Blo 155795 158015 := bstep (se 1 (by rfl) ⟨118511, by rfl⟩ : syracuseStep 158015 = 237023) B237023
theorem B1337897 : Blo 155795 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B158335 : Blo 155795 158335 := bstep (se 1 (by rfl) ⟨118751, by rfl⟩ : syracuseStep 158335 = 237503) B237503
theorem B1600361 : Blo 155795 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B158751 : Blo 155795 158751 := bstep (se 1 (by rfl) ⟨119063, by rfl⟩ : syracuseStep 158751 = 238127) B238127
theorem B158847 : Blo 155795 158847 := bstep (se 1 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 158847 = 238271) B238271
theorem B355553 : Blo 155795 355553 := bstep (se 2 (by rfl) ⟨133332, by rfl⟩ : syracuseStep 355553 = 266665) B266665
theorem B159655 : Blo 155795 159655 := bstep (se 1 (by rfl) ⟨119741, by rfl⟩ : syracuseStep 159655 = 239483) B239483
theorem B159771 : Blo 155795 159771 := bstep (se 1 (by rfl) ⟨119828, by rfl⟩ : syracuseStep 159771 = 239657) B239657
theorem B356489 : Blo 155795 356489 := bstep (se 2 (by rfl) ⟨133683, by rfl⟩ : syracuseStep 356489 = 267367) B267367
theorem B356543 : Blo 155795 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B1833799 : Blo 155795 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B3406799 : Blo 155795 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B3866615 : Blo 155795 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B295913 : Blo 155795 295913 := bstep (se 2 (by rfl) ⟨110967, by rfl⟩ : syracuseStep 295913 = 221935) B221935
theorem B295967 : Blo 155795 295967 := bstep (se 1 (by rfl) ⟨221975, by rfl⟩ : syracuseStep 295967 = 443951) B443951
theorem B2548500407 : Blo 155795 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1149497 : Blo 155795 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B395867 : Blo 155795 395867 := bstep (se 1 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 395867 = 593801) B593801
theorem B1444513 : Blo 155795 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B298343 : Blo 155795 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B298495 : Blo 155795 298495 := bstep (se 1 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 298495 = 447743) B447743
theorem B10424609 : Blo 155795 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B758335 : Blo 155795 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B1020545 : Blo 155795 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B791531 : Blo 155795 791531 := bstep (se 1 (by rfl) ⟨593648, by rfl⟩ : syracuseStep 791531 = 1187297) B1187297
theorem B300971 : Blo 155795 300971 := bstep (se 1 (by rfl) ⟨225728, by rfl⟩ : syracuseStep 300971 = 451457) B451457
theorem B235547 : Blo 155795 235547 := bstep (se 1 (by rfl) ⟨176660, by rfl⟩ : syracuseStep 235547 = 353321) B353321
theorem B235931 : Blo 155795 235931 := bstep (se 1 (by rfl) ⟨176948, by rfl⟩ : syracuseStep 235931 = 353897) B353897
theorem B792989 : Blo 155795 792989 := bstep (se 3 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 792989 = 297371) B297371
theorem B1350269 : Blo 155795 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B891931 : Blo 155795 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B237035 : Blo 155795 237035 := bstep (se 1 (by rfl) ⟨177776, by rfl⟩ : syracuseStep 237035 = 355553) B355553
theorem B237659 : Blo 155795 237659 := bstep (se 1 (by rfl) ⟨178244, by rfl⟩ : syracuseStep 237659 = 356489) B356489
theorem B237695 : Blo 155795 237695 := bstep (se 1 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 237695 = 356543) B356543
theorem B795095 : Blo 155795 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B795419 : Blo 155795 795419 := bstep (se 1 (by rfl) ⟨596564, by rfl⟩ : syracuseStep 795419 = 1193129) B1193129
theorem B238457 : Blo 155795 238457 := bstep (se 2 (by rfl) ⟨89421, by rfl⟩ : syracuseStep 238457 = 178843) B178843
theorem B403339 : Blo 155795 403339 := bstep (se 1 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 403339 = 605009) B605009
theorem B2271199 : Blo 155795 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B3812123 : Blo 155795 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B799145 : Blo 155795 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B800363 : Blo 155795 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B2668139 : Blo 155795 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B800765 : Blo 155795 800765 := bstep (se 3 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 800765 = 300287) B300287
theorem B1554743 : Blo 155795 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B211963 : Blo 155795 211963 := bstep (se 1 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 211963 = 317945) B317945
theorem B179455 : Blo 155795 179455 := bstep (se 1 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 179455 = 269183) B269183
theorem B507521 : Blo 155795 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B803519 : Blo 155795 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B26231597 : Blo 155795 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B2835803 : Blo 155795 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B804329 : Blo 155795 804329 := bstep (se 2 (by rfl) ⟨301623, by rfl⟩ : syracuseStep 804329 = 603247) B603247
theorem B1066907 : Blo 155795 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B2445065 : Blo 155795 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B905327 : Blo 155795 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B1200905 : Blo 155795 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B2577743 : Blo 155795 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B1234543 : Blo 155795 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B1791881 : Blo 155795 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B579611 : Blo 155795 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B19421471 : Blo 155795 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B1268273 : Blo 155795 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B1202849 : Blo 155795 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B1203227 : Blo 155795 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B352079 : Blo 155795 352079 := bstep (se 1 (by rfl) ⟨264059, by rfl⟩ : syracuseStep 352079 = 528119) B528119
theorem B1925531 : Blo 155795 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B353249 : Blo 155795 353249 := bstep (se 2 (by rfl) ⟨132468, by rfl⟩ : syracuseStep 353249 = 264937) B264937
theorem B157567 : Blo 155795 157567 := bstep (se 1 (by rfl) ⟨118175, by rfl⟩ : syracuseStep 157567 = 236351) B236351
theorem B714791 : Blo 155795 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B157903 : Blo 155795 157903 := bstep (se 1 (by rfl) ⟨118427, by rfl⟩ : syracuseStep 157903 = 236855) B236855
theorem B158491 : Blo 155795 158491 := bstep (se 1 (by rfl) ⟨118868, by rfl⟩ : syracuseStep 158491 = 237737) B237737
theorem B355103 : Blo 155795 355103 := bstep (se 1 (by rfl) ⟨266327, by rfl⟩ : syracuseStep 355103 = 532655) B532655
theorem B355355 : Blo 155795 355355 := bstep (se 1 (by rfl) ⟨266516, by rfl⟩ : syracuseStep 355355 = 533033) B533033
theorem B159039 : Blo 155795 159039 := bstep (se 1 (by rfl) ⟨119279, by rfl⟩ : syracuseStep 159039 = 238559) B238559
theorem B1929071 : Blo 155795 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B225193 : Blo 155795 225193 := bstep (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) B168895
theorem B3568835 : Blo 155795 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B357929 : Blo 155795 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B2915513 : Blo 155795 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B1473913 : Blo 155795 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1802087 : Blo 155795 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B197311 : Blo 155795 197311 := bstep (se 1 (by rfl) ⟨147983, by rfl⟩ : syracuseStep 197311 = 295967) B295967
theorem B263911 : Blo 155795 263911 := bstep (se 1 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 263911 = 395867) B395867
theorem B789101 : Blo 155795 789101 := bstep (se 3 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 789101 = 295913) B295913
theorem B6949739 : Blo 155795 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B527687 : Blo 155795 527687 := bstep (se 1 (by rfl) ⟨395765, by rfl⟩ : syracuseStep 527687 = 791531) B791531
theorem B200647 : Blo 155795 200647 := bstep (se 1 (by rfl) ⟨150485, by rfl⟩ : syracuseStep 200647 = 300971) B300971
theorem B528659 : Blo 155795 528659 := bstep (se 1 (by rfl) ⟨396494, by rfl⟩ : syracuseStep 528659 = 792989) B792989
theorem B397993 : Blo 155795 397993 := bstep (se 2 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 397993 = 298495) B298495
theorem B234719 : Blo 155795 234719 := bstep (se 1 (by rfl) ⟨176039, by rfl⟩ : syracuseStep 234719 = 352079) B352079
theorem B300257 : Blo 155795 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B1283687 : Blo 155795 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B530063 : Blo 155795 530063 := bstep (se 1 (by rfl) ⟨397547, by rfl⟩ : syracuseStep 530063 = 795095) B795095
theorem B530279 : Blo 155795 530279 := bstep (se 1 (by rfl) ⟨397709, by rfl⟩ : syracuseStep 530279 = 795419) B795419
theorem B235499 : Blo 155795 235499 := bstep (se 1 (by rfl) ⟨176624, by rfl⟩ : syracuseStep 235499 = 353249) B353249
theorem B236735 : Blo 155795 236735 := bstep (se 1 (by rfl) ⟨177551, by rfl⟩ : syracuseStep 236735 = 355103) B355103
theorem B236903 : Blo 155795 236903 := bstep (se 1 (by rfl) ⟨177677, by rfl⟩ : syracuseStep 236903 = 355355) B355355
theorem B1646057 : Blo 155795 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1286047 : Blo 155795 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B532763 : Blo 155795 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B795581 : Blo 155795 795581 := bstep (se 3 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 795581 = 298343) B298343
theorem B238619 : Blo 155795 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B533575 : Blo 155795 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B1778759 : Blo 155795 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B533843 : Blo 155795 533843 := bstep (se 1 (by rfl) ⟨400382, by rfl⟩ : syracuseStep 533843 = 800765) B800765
theorem B1189241 : Blo 155795 1189241 := bstep (se 2 (by rfl) ⟨445965, by rfl⟩ : syracuseStep 1189241 = 891931) B891931
theorem B239273 : Blo 155795 239273 := bstep (se 2 (by rfl) ⟨89727, by rfl⟩ : syracuseStep 239273 = 179455) B179455
theorem B1943675 : Blo 155795 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B338347 : Blo 155795 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B535679 : Blo 155795 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B536219 : Blo 155795 536219 := bstep (se 1 (by rfl) ⟨402164, by rfl⟩ : syracuseStep 536219 = 804329) B804329
theorem B1699000271 : Blo 155795 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B766331 : Blo 155795 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B537785 : Blo 155795 537785 := bstep (se 2 (by rfl) ⟨201669, by rfl⟩ : syracuseStep 537785 = 403339) B403339
theorem B3028265 : Blo 155795 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B603551 : Blo 155795 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B800603 : Blo 155795 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B1718495 : Blo 155795 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B1194587 : Blo 155795 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B900179 : Blo 155795 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B801899 : Blo 155795 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B802151 : Blo 155795 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B51790589 : Blo 155795 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B476527 : Blo 155795 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B2541415 : Blo 155795 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B2379223 : Blo 155795 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B282617 : Blo 155795 282617 := bstep (se 2 (by rfl) ⟨105981, by rfl⟩ : syracuseStep 282617 = 211963) B211963
theorem B1036495 : Blo 155795 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B1201391 : Blo 155795 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B17487731 : Blo 155795 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1890535 : Blo 155795 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B711271 : Blo 155795 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1630043 : Blo 155795 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B680363 : Blo 155795 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B1926017 : Blo 155795 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B157031 : Blo 155795 157031 := bstep (se 1 (by rfl) ⟨117773, by rfl⟩ : syracuseStep 157031 = 235547) B235547
theorem B386407 : Blo 155795 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B157287 : Blo 155795 157287 := bstep (se 1 (by rfl) ⟨117965, by rfl⟩ : syracuseStep 157287 = 235931) B235931
theorem B845515 : Blo 155795 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B158023 : Blo 155795 158023 := bstep (se 1 (by rfl) ⟨118517, by rfl⟩ : syracuseStep 158023 = 237035) B237035
theorem B158439 : Blo 155795 158439 := bstep (se 1 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 158439 = 237659) B237659
theorem B158463 : Blo 155795 158463 := bstep (se 1 (by rfl) ⟨118847, by rfl⟩ : syracuseStep 158463 = 237695) B237695
theorem B158971 : Blo 155795 158971 := bstep (se 1 (by rfl) ⟨119228, by rfl⟩ : syracuseStep 158971 = 238457) B238457
theorem B1011113 : Blo 155795 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B1965217 : Blo 155795 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B263081 : Blo 155795 263081 := bstep (se 2 (by rfl) ⟨98655, by rfl⟩ : syracuseStep 263081 = 197311) B197311
theorem B526067 : Blo 155795 526067 := bstep (se 1 (by rfl) ⟨394550, by rfl⟩ : syracuseStep 526067 = 789101) B789101
theorem B200171 : Blo 155795 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B855791 : Blo 155795 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B1086695 : Blo 155795 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B267529 : Blo 155795 267529 := bstep (se 2 (by rfl) ⟨100323, by rfl⟩ : syracuseStep 267529 = 200647) B200647
theorem B1284011 : Blo 155795 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B530387 : Blo 155795 530387 := bstep (se 1 (by rfl) ⟨397790, by rfl⟩ : syracuseStep 530387 = 795581) B795581
theorem B1185839 : Blo 155795 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B530657 : Blo 155795 530657 := bstep (se 2 (by rfl) ⟨198996, by rfl⟩ : syracuseStep 530657 = 397993) B397993
theorem B792827 : Blo 155795 792827 := bstep (se 1 (by rfl) ⟨594620, by rfl⟩ : syracuseStep 792827 = 1189241) B1189241
theorem B1132666847 : Blo 155795 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B402367 : Blo 155795 402367 := bstep (se 1 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 402367 = 603551) B603551
theorem B533735 : Blo 155795 533735 := bstep (se 1 (by rfl) ⟨400301, by rfl⟩ : syracuseStep 533735 = 800603) B800603
theorem B796391 : Blo 155795 796391 := bstep (se 1 (by rfl) ⟨597293, by rfl⟩ : syracuseStep 796391 = 1194587) B1194587
theorem B600119 : Blo 155795 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B534599 : Blo 155795 534599 := bstep (se 1 (by rfl) ⟨400949, by rfl⟩ : syracuseStep 534599 = 801899) B801899
theorem B534767 : Blo 155795 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B1714729 : Blo 155795 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B635369 : Blo 155795 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B4633159 : Blo 155795 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B1127353 : Blo 155795 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B3388553 : Blo 155795 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B800927 : Blo 155795 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B1097371 : Blo 155795 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B1295783 : Blo 155795 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B674075 : Blo 155795 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B510887 : Blo 155795 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B2018843 : Blo 155795 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B34527059 : Blo 155795 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B5527973 : Blo 155795 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B711433 : Blo 155795 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B515209 : Blo 155795 515209 := bstep (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) B386407
theorem B351791 : Blo 155795 351791 := bstep (se 1 (by rfl) ⟨263843, by rfl⟩ : syracuseStep 351791 = 527687) B527687
theorem B351881 : Blo 155795 351881 := bstep (se 2 (by rfl) ⟨131955, by rfl⟩ : syracuseStep 351881 = 263911) B263911
theorem B188411 : Blo 155795 188411 := bstep (se 1 (by rfl) ⟨141308, by rfl⟩ : syracuseStep 188411 = 282617) B282617
theorem B352439 : Blo 155795 352439 := bstep (se 1 (by rfl) ⟨264329, by rfl⟩ : syracuseStep 352439 = 528659) B528659
theorem B451129 : Blo 155795 451129 := bstep (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) B338347
theorem B156479 : Blo 155795 156479 := bstep (se 1 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 156479 = 234719) B234719
theorem B353375 : Blo 155795 353375 := bstep (se 1 (by rfl) ⟨265031, by rfl⟩ : syracuseStep 353375 = 530063) B530063
theorem B353519 : Blo 155795 353519 := bstep (se 1 (by rfl) ⟨265139, by rfl⟩ : syracuseStep 353519 = 530279) B530279
theorem B11658487 : Blo 155795 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B156999 : Blo 155795 156999 := bstep (se 1 (by rfl) ⟨117749, by rfl⟩ : syracuseStep 156999 = 235499) B235499
theorem B3172297 : Blo 155795 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B157823 : Blo 155795 157823 := bstep (se 1 (by rfl) ⟨118367, by rfl⟩ : syracuseStep 157823 = 236735) B236735
theorem B157935 : Blo 155795 157935 := bstep (se 1 (by rfl) ⟨118451, by rfl⟩ : syracuseStep 157935 = 236903) B236903
theorem B355175 : Blo 155795 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B453575 : Blo 155795 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B159079 : Blo 155795 159079 := bstep (se 1 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 159079 = 238619) B238619
theorem B355895 : Blo 155795 355895 := bstep (se 1 (by rfl) ⟨266921, by rfl⟩ : syracuseStep 355895 = 533843) B533843
theorem B159515 : Blo 155795 159515 := bstep (se 1 (by rfl) ⟨119636, by rfl⟩ : syracuseStep 159515 = 239273) B239273
theorem B357119 : Blo 155795 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B357479 : Blo 155795 357479 := bstep (se 1 (by rfl) ⟨268109, by rfl⟩ : syracuseStep 357479 = 536219) B536219
theorem B2520713 : Blo 155795 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B358523 : Blo 155795 358523 := bstep (se 1 (by rfl) ⟨268892, by rfl⟩ : syracuseStep 358523 = 537785) B537785
theorem B948361 : Blo 155795 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B1145663 : Blo 155795 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B2620289 : Blo 155795 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1345895 : Blo 155795 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B4229729 : Blo 155795 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B724463 : Blo 155795 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B856007 : Blo 155795 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B790559 : Blo 155795 790559 := bstep (se 1 (by rfl) ⟨592919, by rfl⟩ : syracuseStep 790559 = 1185839) B1185839
theorem B528551 : Blo 155795 528551 := bstep (se 1 (by rfl) ⟨396413, by rfl⟩ : syracuseStep 528551 = 792827) B792827
theorem B234527 : Blo 155795 234527 := bstep (se 1 (by rfl) ⟨175895, by rfl⟩ : syracuseStep 234527 = 351791) B351791
theorem B234587 : Blo 155795 234587 := bstep (se 1 (by rfl) ⟨175940, by rfl⟩ : syracuseStep 234587 = 351881) B351881
theorem B755111231 : Blo 155795 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B234959 : Blo 155795 234959 := bstep (se 1 (by rfl) ⟨176219, by rfl⟩ : syracuseStep 234959 = 352439) B352439
theorem B235583 : Blo 155795 235583 := bstep (se 1 (by rfl) ⟨176687, by rfl⟩ : syracuseStep 235583 = 353375) B353375
theorem B235679 : Blo 155795 235679 := bstep (se 1 (by rfl) ⟨176759, by rfl⟩ : syracuseStep 235679 = 353519) B353519
theorem B530927 : Blo 155795 530927 := bstep (se 1 (by rfl) ⟨398195, by rfl⟩ : syracuseStep 530927 = 796391) B796391
theorem B400079 : Blo 155795 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B236783 : Blo 155795 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B302383 : Blo 155795 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B237263 : Blo 155795 237263 := bstep (se 1 (by rfl) ⟨177947, by rfl⟩ : syracuseStep 237263 = 355895) B355895
theorem B238079 : Blo 155795 238079 := bstep (se 1 (by rfl) ⟨178559, by rfl⟩ : syracuseStep 238079 = 357119) B357119
theorem B238319 : Blo 155795 238319 := bstep (se 1 (by rfl) ⟨178739, by rfl⟩ : syracuseStep 238319 = 357479) B357479
theorem B1680475 : Blo 155795 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B533789 : Blo 155795 533789 := bstep (se 3 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 533789 = 200171) B200171
theorem B239015 : Blo 155795 239015 := bstep (se 1 (by rfl) ⟨179261, by rfl⟩ : syracuseStep 239015 = 358523) B358523
theorem B533951 : Blo 155795 533951 := bstep (se 1 (by rfl) ⟨400463, by rfl⟩ : syracuseStep 533951 = 800927) B800927
theorem B763775 : Blo 155795 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B1746859 : Blo 155795 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B2009717 : Blo 155795 2009717 := bstep (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) B188411
theorem B175387 : Blo 155795 175387 := bstep (se 1 (by rfl) ⟨131540, by rfl⟩ : syracuseStep 175387 = 263081) B263081
theorem B601505 : Blo 155795 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B863855 : Blo 155795 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B536489 : Blo 155795 536489 := bstep (se 2 (by rfl) ⟨201183, by rfl⟩ : syracuseStep 536489 = 402367) B402367
theorem B15544649 : Blo 155795 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B570527 : Blo 155795 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B23018039 : Blo 155795 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B1426045 : Blo 155795 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B6177545 : Blo 155795 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B1362365 : Blo 155795 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B1264481 : Blo 155795 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B5852645 : Blo 155795 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B350711 : Blo 155795 350711 := bstep (se 1 (by rfl) ⟨263033, by rfl⟩ : syracuseStep 350711 = 526067) B526067
theorem B1694317 : Blo 155795 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B449383 : Blo 155795 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B2286305 : Blo 155795 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B353591 : Blo 155795 353591 := bstep (se 1 (by rfl) ⟨265193, by rfl⟩ : syracuseStep 353591 = 530387) B530387
theorem B3794309 : Blo 155795 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B353771 : Blo 155795 353771 := bstep (se 1 (by rfl) ⟨265328, by rfl⟩ : syracuseStep 353771 = 530657) B530657
theorem B355823 : Blo 155795 355823 := bstep (se 1 (by rfl) ⟨266867, by rfl⟩ : syracuseStep 355823 = 533735) B533735
theorem B14741261 : Blo 155795 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B1503137 : Blo 155795 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B356399 : Blo 155795 356399 := bstep (se 1 (by rfl) ⟨267299, by rfl⟩ : syracuseStep 356399 = 534599) B534599
theorem B356705 : Blo 155795 356705 := bstep (se 2 (by rfl) ⟨133764, by rfl⟩ : syracuseStep 356705 = 267529) B267529
theorem B2259035 : Blo 155795 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B686945 : Blo 155795 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B1901393 : Blo 155795 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B2819819 : Blo 155795 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B3901763 : Blo 155795 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2329145 : Blo 155795 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B527039 : Blo 155795 527039 := bstep (se 1 (by rfl) ⟨395279, by rfl⟩ : syracuseStep 527039 = 790559) B790559
theorem B233807 : Blo 155795 233807 := bstep (se 1 (by rfl) ⟨175355, by rfl⟩ : syracuseStep 233807 = 350711) B350711
theorem B233849 : Blo 155795 233849 := bstep (se 2 (by rfl) ⟨87693, by rfl⟩ : syracuseStep 233849 = 175387) B175387
theorem B266719 : Blo 155795 266719 := bstep (se 1 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 266719 = 400079) B400079
theorem B235727 : Blo 155795 235727 := bstep (se 1 (by rfl) ⟨176795, by rfl⟩ : syracuseStep 235727 = 353591) B353591
theorem B2529539 : Blo 155795 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B235847 : Blo 155795 235847 := bstep (se 1 (by rfl) ⟨176885, by rfl⟩ : syracuseStep 235847 = 353771) B353771
theorem B401003 : Blo 155795 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B237215 : Blo 155795 237215 := bstep (se 1 (by rfl) ⟨177911, by rfl⟩ : syracuseStep 237215 = 355823) B355823
theorem B237599 : Blo 155795 237599 := bstep (se 1 (by rfl) ⟨178199, by rfl⟩ : syracuseStep 237599 = 356399) B356399
theorem B10363099 : Blo 155795 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B237803 : Blo 155795 237803 := bstep (se 1 (by rfl) ⟨178352, by rfl⟩ : syracuseStep 237803 = 356705) B356705
theorem B599177 : Blo 155795 599177 := bstep (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) B449383
theorem B15345359 : Blo 155795 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B403177 : Blo 155795 403177 := bstep (se 2 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 403177 = 302383) B302383
theorem B2240633 : Blo 155795 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B897263 : Blo 155795 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B570671 : Blo 155795 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B1524203 : Blo 155795 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B509183 : Blo 155795 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B575903 : Blo 155795 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B1002091 : Blo 155795 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B380351 : Blo 155795 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B4118363 : Blo 155795 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B908243 : Blo 155795 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B842987 : Blo 155795 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B482975 : Blo 155795 482975 := bstep (se 1 (by rfl) ⟨362231, by rfl⟩ : syracuseStep 482975 = 724463) B724463
theorem B352367 : Blo 155795 352367 := bstep (se 1 (by rfl) ⟨264275, by rfl⟩ : syracuseStep 352367 = 528551) B528551
theorem B156351 : Blo 155795 156351 := bstep (se 1 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 156351 = 234527) B234527
theorem B156391 : Blo 155795 156391 := bstep (se 1 (by rfl) ⟨117293, by rfl⟩ : syracuseStep 156391 = 234587) B234587
theorem B503407487 : Blo 155795 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B156639 : Blo 155795 156639 := bstep (se 1 (by rfl) ⟨117479, by rfl⟩ : syracuseStep 156639 = 234959) B234959
theorem B157055 : Blo 155795 157055 := bstep (se 1 (by rfl) ⟨117791, by rfl⟩ : syracuseStep 157055 = 235583) B235583
theorem B157119 : Blo 155795 157119 := bstep (se 1 (by rfl) ⟨117839, by rfl⟩ : syracuseStep 157119 = 235679) B235679
theorem B353951 : Blo 155795 353951 := bstep (se 1 (by rfl) ⟨265463, by rfl⟩ : syracuseStep 353951 = 530927) B530927
theorem B157855 : Blo 155795 157855 := bstep (se 1 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 157855 = 236783) B236783
theorem B158175 : Blo 155795 158175 := bstep (se 1 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 158175 = 237263) B237263
theorem B158719 : Blo 155795 158719 := bstep (se 1 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 158719 = 238079) B238079
theorem B158879 : Blo 155795 158879 := bstep (se 1 (by rfl) ⟨119159, by rfl⟩ : syracuseStep 158879 = 238319) B238319
theorem B355859 : Blo 155795 355859 := bstep (se 1 (by rfl) ⟨266894, by rfl⟩ : syracuseStep 355859 = 533789) B533789
theorem B159343 : Blo 155795 159343 := bstep (se 1 (by rfl) ⟨119507, by rfl⟩ : syracuseStep 159343 = 239015) B239015
theorem B355967 : Blo 155795 355967 := bstep (se 1 (by rfl) ⟨266975, by rfl⟩ : syracuseStep 355967 = 533951) B533951
theorem B1339811 : Blo 155795 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B9827507 : Blo 155795 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B357659 : Blo 155795 357659 := bstep (se 1 (by rfl) ⟨268244, by rfl⟩ : syracuseStep 357659 = 536489) B536489
theorem B2259089 : Blo 155795 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B1506023 : Blo 155795 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B457963 : Blo 155795 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B1016135 : Blo 155795 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B561991 : Blo 155795 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B267335 : Blo 155795 267335 := bstep (se 1 (by rfl) ⟨200501, by rfl⟩ : syracuseStep 267335 = 401003) B401003
theorem B234911 : Blo 155795 234911 := bstep (se 1 (by rfl) ⟨176183, by rfl⟩ : syracuseStep 234911 = 352367) B352367
theorem B399451 : Blo 155795 399451 := bstep (se 1 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 399451 = 599177) B599177
theorem B235967 : Blo 155795 235967 := bstep (se 1 (by rfl) ⟨176975, by rfl⟩ : syracuseStep 235967 = 353951) B353951
theorem B10230239 : Blo 155795 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B237239 : Blo 155795 237239 := bstep (se 1 (by rfl) ⟨177929, by rfl⟩ : syracuseStep 237239 = 355859) B355859
theorem B237311 : Blo 155795 237311 := bstep (se 1 (by rfl) ⟨177983, by rfl⟩ : syracuseStep 237311 = 355967) B355967
theorem B598175 : Blo 155795 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B893207 : Blo 155795 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B238439 : Blo 155795 238439 := bstep (se 1 (by rfl) ⟨178829, by rfl⟩ : syracuseStep 238439 = 357659) B357659
theorem B5975021 : Blo 155795 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B339455 : Blo 155795 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B2601175 : Blo 155795 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1552763 : Blo 155795 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B537569 : Blo 155795 537569 := bstep (se 2 (by rfl) ⟨201588, by rfl⟩ : syracuseStep 537569 = 403177) B403177
theorem B1686359 : Blo 155795 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B7519517 : Blo 155795 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B605495 : Blo 155795 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B2442469 : Blo 155795 2442469 := bstep (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) B457963
theorem B380447 : Blo 155795 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B1004015 : Blo 155795 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B13817465 : Blo 155795 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B1267595 : Blo 155795 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B383935 : Blo 155795 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B351359 : Blo 155795 351359 := bstep (se 1 (by rfl) ⟨263519, by rfl⟩ : syracuseStep 351359 = 527039) B527039
theorem B253567 : Blo 155795 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B155871 : Blo 155795 155871 := bstep (se 1 (by rfl) ⟨116903, by rfl⟩ : syracuseStep 155871 = 233807) B233807
theorem B155899 : Blo 155795 155899 := bstep (se 1 (by rfl) ⟨116924, by rfl⟩ : syracuseStep 155899 = 233849) B233849
theorem B26206685 : Blo 155795 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B1336121 : Blo 155795 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B2745575 : Blo 155795 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B157151 : Blo 155795 157151 := bstep (se 1 (by rfl) ⟨117863, by rfl⟩ : syracuseStep 157151 = 235727) B235727
theorem B157231 : Blo 155795 157231 := bstep (se 1 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 157231 = 235847) B235847
theorem B158143 : Blo 155795 158143 := bstep (se 1 (by rfl) ⟨118607, by rfl⟩ : syracuseStep 158143 = 237215) B237215
theorem B321983 : Blo 155795 321983 := bstep (se 1 (by rfl) ⟨241487, by rfl⟩ : syracuseStep 321983 = 482975) B482975
theorem B158399 : Blo 155795 158399 := bstep (se 1 (by rfl) ⟨118799, by rfl⟩ : syracuseStep 158399 = 237599) B237599
theorem B158535 : Blo 155795 158535 := bstep (se 1 (by rfl) ⟨118901, by rfl⟩ : syracuseStep 158535 = 237803) B237803
theorem B335604991 : Blo 155795 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B355625 : Blo 155795 355625 := bstep (se 2 (by rfl) ⟨133359, by rfl⟩ : syracuseStep 355625 = 266719) B266719
theorem B1506059 : Blo 155795 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B9211643 : Blo 155795 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B6820159 : Blo 155795 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B234239 : Blo 155795 234239 := bstep (se 1 (by rfl) ⟨175679, by rfl⟩ : syracuseStep 234239 = 351359) B351359
theorem B398783 : Blo 155795 398783 := bstep (se 1 (by rfl) ⟨299087, by rfl⟩ : syracuseStep 398783 = 598175) B598175
theorem B595471 : Blo 155795 595471 := bstep (se 1 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 595471 = 893207) B893207
theorem B17471123 : Blo 155795 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B890747 : Blo 155795 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B237083 : Blo 155795 237083 := bstep (se 1 (by rfl) ⟨177812, by rfl⟩ : syracuseStep 237083 = 355625) B355625
theorem B532601 : Blo 155795 532601 := bstep (se 2 (by rfl) ⟨199725, by rfl⟩ : syracuseStep 532601 = 399451) B399451
theorem B1124239 : Blo 155795 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B338089 : Blo 155795 338089 := bstep (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) B253567
theorem B403663 : Blo 155795 403663 := bstep (se 1 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 403663 = 605495) B605495
theorem B3256625 : Blo 155795 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B669343 : Blo 155795 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B178223 : Blo 155795 178223 := bstep (se 1 (by rfl) ⟨133667, by rfl⟩ : syracuseStep 178223 = 267335) B267335
theorem B214655 : Blo 155795 214655 := bstep (se 1 (by rfl) ⟨160991, by rfl⟩ : syracuseStep 214655 = 321983) B321983
theorem B3983347 : Blo 155795 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B1035175 : Blo 155795 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B511913 : Blo 155795 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B905213 : Blo 155795 905213 := bstep (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) B339455
theorem B1004039 : Blo 155795 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B677423 : Blo 155795 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B253631 : Blo 155795 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B156607 : Blo 155795 156607 := bstep (se 1 (by rfl) ⟨117455, by rfl⟩ : syracuseStep 156607 = 234911) B234911
theorem B845063 : Blo 155795 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B157311 : Blo 155795 157311 := bstep (se 1 (by rfl) ⟨117983, by rfl⟩ : syracuseStep 157311 = 235967) B235967
theorem B447473321 : Blo 155795 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B158159 : Blo 155795 158159 := bstep (se 1 (by rfl) ⟨118619, by rfl⟩ : syracuseStep 158159 = 237239) B237239
theorem B158207 : Blo 155795 158207 := bstep (se 1 (by rfl) ⟨118655, by rfl⟩ : syracuseStep 158207 = 237311) B237311
theorem B3468233 : Blo 155795 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B158959 : Blo 155795 158959 := bstep (se 1 (by rfl) ⟨119219, by rfl⟩ : syracuseStep 158959 = 238439) B238439
theorem B1830383 : Blo 155795 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B749321 : Blo 155795 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B358379 : Blo 155795 358379 := bstep (se 1 (by rfl) ⟨268784, by rfl⟩ : syracuseStep 358379 = 537569) B537569
theorem B5013011 : Blo 155795 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B1901045 : Blo 155795 1901045 := bstep (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) B178223
theorem B5311129 : Blo 155795 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B265855 : Blo 155795 265855 := bstep (se 1 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 265855 = 398783) B398783
theorem B1380233 : Blo 155795 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B593831 : Blo 155795 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B1806461 : Blo 155795 1806461 := bstep (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) B677423
theorem B563375 : Blo 155795 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B793961 : Blo 155795 793961 := bstep (se 2 (by rfl) ⟨297735, by rfl⟩ : syracuseStep 793961 = 595471) B595471
theorem B892457 : Blo 155795 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B1220255 : Blo 155795 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B499547 : Blo 155795 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B2171083 : Blo 155795 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B238919 : Blo 155795 238919 := bstep (se 1 (by rfl) ⟨179189, by rfl⟩ : syracuseStep 238919 = 358379) B358379
theorem B6141095 : Blo 155795 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B341275 : Blo 155795 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B538217 : Blo 155795 538217 := bstep (se 2 (by rfl) ⟨201831, by rfl⟩ : syracuseStep 538217 = 403663) B403663
theorem B669359 : Blo 155795 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B11647415 : Blo 155795 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B9093545 : Blo 155795 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B2312155 : Blo 155795 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B676349 : Blo 155795 676349 := bstep (se 3 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 676349 = 253631) B253631
theorem B2413901 : Blo 155795 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B1498985 : Blo 155795 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B450785 : Blo 155795 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B156159 : Blo 155795 156159 := bstep (se 1 (by rfl) ⟨117119, by rfl⟩ : syracuseStep 156159 = 234239) B234239
theorem B158055 : Blo 155795 158055 := bstep (se 1 (by rfl) ⟨118541, by rfl⟩ : syracuseStep 158055 = 237083) B237083
theorem B355067 : Blo 155795 355067 := bstep (se 1 (by rfl) ⟨266300, by rfl⟩ : syracuseStep 355067 = 532601) B532601
theorem B298315547 : Blo 155795 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B2289653 : Blo 155795 2289653 := bstep (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) B214655
theorem B3342007 : Blo 155795 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B6062363 : Blo 155795 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B920155 : Blo 155795 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B395887 : Blo 155795 395887 := bstep (se 1 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 395887 = 593831) B593831
theorem B3082873 : Blo 155795 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B7081505 : Blo 155795 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B1609267 : Blo 155795 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B529307 : Blo 155795 529307 := bstep (se 1 (by rfl) ⟨396980, by rfl⟩ : syracuseStep 529307 = 793961) B793961
theorem B594971 : Blo 155795 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B300523 : Blo 155795 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B236711 : Blo 155795 236711 := bstep (se 1 (by rfl) ⟨177533, by rfl⟩ : syracuseStep 236711 = 355067) B355067
theorem B198877031 : Blo 155795 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B2894777 : Blo 155795 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B999323 : Blo 155795 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B1526435 : Blo 155795 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B446239 : Blo 155795 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B1332125 : Blo 155795 1332125 := bstep (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) B499547
theorem B1267363 : Blo 155795 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B1204307 : Blo 155795 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B450899 : Blo 155795 450899 := bstep (se 1 (by rfl) ⟨338174, by rfl⟩ : syracuseStep 450899 = 676349) B676349
theorem B354473 : Blo 155795 354473 := bstep (se 2 (by rfl) ⟨132927, by rfl⟩ : syracuseStep 354473 = 265855) B265855
theorem B813503 : Blo 155795 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B1502333 : Blo 155795 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B159279 : Blo 155795 159279 := bstep (se 1 (by rfl) ⟨119459, by rfl⟩ : syracuseStep 159279 = 238919) B238919
theorem B455033 : Blo 155795 455033 := bstep (se 2 (by rfl) ⟨170637, by rfl⟩ : syracuseStep 455033 = 341275) B341275
theorem B4094063 : Blo 155795 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B358811 : Blo 155795 358811 := bstep (se 1 (by rfl) ⟨269108, by rfl⟩ : syracuseStep 358811 = 538217) B538217
theorem B7764943 : Blo 155795 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B4456009 : Blo 155795 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B1017623 : Blo 155795 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B4721003 : Blo 155795 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B888083 : Blo 155795 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B396647 : Blo 155795 396647 := bstep (se 1 (by rfl) ⟨297485, by rfl⟩ : syracuseStep 396647 = 594971) B594971
theorem B527849 : Blo 155795 527849 := bstep (se 2 (by rfl) ⟨197943, by rfl⟩ : syracuseStep 527849 = 395887) B395887
theorem B594985 : Blo 155795 594985 := bstep (se 2 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 594985 = 446239) B446239
theorem B132584687 : Blo 155795 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B300599 : Blo 155795 300599 := bstep (se 1 (by rfl) ⟨225449, by rfl⟩ : syracuseStep 300599 = 450899) B450899
theorem B236315 : Blo 155795 236315 := bstep (se 1 (by rfl) ⟨177236, by rfl⟩ : syracuseStep 236315 = 354473) B354473
theorem B400697 : Blo 155795 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B303355 : Blo 155795 303355 := bstep (se 1 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 303355 = 455033) B455033
theorem B2729375 : Blo 155795 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B239207 : Blo 155795 239207 := bstep (se 1 (by rfl) ⟨179405, by rfl⟩ : syracuseStep 239207 = 358811) B358811
theorem B5941345 : Blo 155795 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B666215 : Blo 155795 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B4041575 : Blo 155795 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B1226873 : Blo 155795 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B4110497 : Blo 155795 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2145689 : Blo 155795 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B802871 : Blo 155795 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B542335 : Blo 155795 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B1001555 : Blo 155795 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B1689817 : Blo 155795 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B352871 : Blo 155795 352871 := bstep (se 1 (by rfl) ⟨264653, by rfl⟩ : syracuseStep 352871 = 529307) B529307
theorem B157807 : Blo 155795 157807 := bstep (se 1 (by rfl) ⟨118355, by rfl⟩ : syracuseStep 157807 = 236711) B236711
theorem B1929851 : Blo 155795 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B10353257 : Blo 155795 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B3147335 : Blo 155795 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B723113 : Blo 155795 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B592055 : Blo 155795 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B264431 : Blo 155795 264431 := bstep (se 1 (by rfl) ⟨198323, by rfl⟩ : syracuseStep 264431 = 396647) B396647
theorem B200399 : Blo 155795 200399 := bstep (se 1 (by rfl) ⟨150299, by rfl⟩ : syracuseStep 200399 = 300599) B300599
theorem B267131 : Blo 155795 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B235247 : Blo 155795 235247 := bstep (se 1 (by rfl) ⟨176435, by rfl⟩ : syracuseStep 235247 = 352871) B352871
theorem B793313 : Blo 155795 793313 := bstep (se 2 (by rfl) ⟨297492, by rfl⟩ : syracuseStep 793313 = 594985) B594985
theorem B2694383 : Blo 155795 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B1286567 : Blo 155795 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B535247 : Blo 155795 535247 := bstep (se 1 (by rfl) ⟨401435, by rfl⟩ : syracuseStep 535247 = 802871) B802871
theorem B404473 : Blo 155795 404473 := bstep (se 2 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 404473 = 303355) B303355
theorem B667703 : Blo 155795 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B88389791 : Blo 155795 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B1819583 : Blo 155795 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B444143 : Blo 155795 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B2740331 : Blo 155795 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B6902171 : Blo 155795 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B1430459 : Blo 155795 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B678415 : Blo 155795 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B351899 : Blo 155795 351899 := bstep (se 1 (by rfl) ⟨263924, by rfl⟩ : syracuseStep 351899 = 527849) B527849
theorem B7921793 : Blo 155795 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B2253089 : Blo 155795 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B157543 : Blo 155795 157543 := bstep (se 1 (by rfl) ⟨118157, by rfl⟩ : syracuseStep 157543 = 236315) B236315
theorem B3271661 : Blo 155795 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B159471 : Blo 155795 159471 := bstep (se 1 (by rfl) ⟨119603, by rfl⟩ : syracuseStep 159471 = 239207) B239207
theorem B1213055 : Blo 155795 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B2098223 : Blo 155795 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B394703 : Blo 155795 394703 := bstep (se 1 (by rfl) ⟨296027, by rfl⟩ : syracuseStep 394703 = 592055) B592055
theorem B953639 : Blo 155795 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B528875 : Blo 155795 528875 := bstep (se 1 (by rfl) ⟨396656, by rfl⟩ : syracuseStep 528875 = 793313) B793313
theorem B1184381 : Blo 155795 1184381 := bstep (se 3 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 1184381 = 444143) B444143
theorem B234599 : Blo 155795 234599 := bstep (se 1 (by rfl) ⟨175949, by rfl⟩ : syracuseStep 234599 = 351899) B351899
theorem B5281195 : Blo 155795 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B857711 : Blo 155795 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B2137589 : Blo 155795 2137589 := bstep (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) B200399
theorem B58926527 : Blo 155795 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B176287 : Blo 155795 176287 := bstep (se 1 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 176287 = 264431) B264431
theorem B4601447 : Blo 155795 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B178087 : Blo 155795 178087 := bstep (se 1 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 178087 = 267131) B267131
theorem B539297 : Blo 155795 539297 := bstep (se 2 (by rfl) ⟨202236, by rfl⟩ : syracuseStep 539297 = 404473) B404473
theorem B2181107 : Blo 155795 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B445135 : Blo 155795 445135 := bstep (se 1 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 445135 = 667703) B667703
theorem B904553 : Blo 155795 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B482075 : Blo 155795 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B1826887 : Blo 155795 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B156831 : Blo 155795 156831 := bstep (se 1 (by rfl) ⟨117623, by rfl⟩ : syracuseStep 156831 = 235247) B235247
theorem B1796255 : Blo 155795 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B1502059 : Blo 155795 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B356831 : Blo 155795 356831 := bstep (se 1 (by rfl) ⟨267623, by rfl⟩ : syracuseStep 356831 = 535247) B535247
theorem B263135 : Blo 155795 263135 := bstep (se 1 (by rfl) ⟨197351, by rfl⟩ : syracuseStep 263135 = 394703) B394703
theorem B789587 : Blo 155795 789587 := bstep (se 1 (by rfl) ⟨592190, by rfl⟩ : syracuseStep 789587 = 1184381) B1184381
theorem B593513 : Blo 155795 593513 := bstep (se 2 (by rfl) ⟨222567, by rfl⟩ : syracuseStep 593513 = 445135) B445135
theorem B2002745 : Blo 155795 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B235049 : Blo 155795 235049 := bstep (se 2 (by rfl) ⟨88143, by rfl⟩ : syracuseStep 235049 = 176287) B176287
theorem B237449 : Blo 155795 237449 := bstep (se 2 (by rfl) ⟨89043, by rfl⟩ : syracuseStep 237449 = 178087) B178087
theorem B237887 : Blo 155795 237887 := bstep (se 1 (by rfl) ⟨178415, by rfl⟩ : syracuseStep 237887 = 356831) B356831
theorem B2435849 : Blo 155795 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B1454071 : Blo 155795 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B635759 : Blo 155795 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B603035 : Blo 155795 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B571807 : Blo 155795 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B1425059 : Blo 155795 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B1197503 : Blo 155795 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B3067631 : Blo 155795 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B808703 : Blo 155795 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B1398815 : Blo 155795 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B352583 : Blo 155795 352583 := bstep (se 1 (by rfl) ⟨264437, by rfl⟩ : syracuseStep 352583 = 528875) B528875
theorem B156399 : Blo 155795 156399 := bstep (se 1 (by rfl) ⟨117299, by rfl⟩ : syracuseStep 156399 = 234599) B234599
theorem B321383 : Blo 155795 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B39284351 : Blo 155795 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B7041593 : Blo 155795 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B359531 : Blo 155795 359531 := bstep (se 1 (by rfl) ⟨269648, by rfl⟩ : syracuseStep 359531 = 539297) B539297
theorem B526391 : Blo 155795 526391 := bstep (se 1 (by rfl) ⟨394793, by rfl⟩ : syracuseStep 526391 = 789587) B789587
theorem B395675 : Blo 155795 395675 := bstep (se 1 (by rfl) ⟨296756, by rfl⟩ : syracuseStep 395675 = 593513) B593513
theorem B1938761 : Blo 155795 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B235055 : Blo 155795 235055 := bstep (se 1 (by rfl) ⟨176291, by rfl⟩ : syracuseStep 235055 = 352583) B352583
theorem B26189567 : Blo 155795 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B4694395 : Blo 155795 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B762409 : Blo 155795 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B402023 : Blo 155795 402023 := bstep (se 1 (by rfl) ⟨301517, by rfl⟩ : syracuseStep 402023 = 603035) B603035
theorem B239687 : Blo 155795 239687 := bstep (se 1 (by rfl) ⟨179765, by rfl⟩ : syracuseStep 239687 = 359531) B359531
theorem B175423 : Blo 155795 175423 := bstep (se 1 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 175423 = 263135) B263135
theorem B798335 : Blo 155795 798335 := bstep (se 1 (by rfl) ⟨598751, by rfl⟩ : syracuseStep 798335 = 1197503) B1197503
theorem B2045087 : Blo 155795 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B539135 : Blo 155795 539135 := bstep (se 1 (by rfl) ⟨404351, by rfl⟩ : syracuseStep 539135 = 808703) B808703
theorem B932543 : Blo 155795 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B214255 : Blo 155795 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B1623899 : Blo 155795 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B1335163 : Blo 155795 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B156699 : Blo 155795 156699 := bstep (se 1 (by rfl) ⟨117524, by rfl⟩ : syracuseStep 156699 = 235049) B235049
theorem B158299 : Blo 155795 158299 := bstep (se 1 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 158299 = 237449) B237449
theorem B158591 : Blo 155795 158591 := bstep (se 1 (by rfl) ⟨118943, by rfl⟩ : syracuseStep 158591 = 237887) B237887
theorem B423839 : Blo 155795 423839 := bstep (se 1 (by rfl) ⟨317879, by rfl⟩ : syracuseStep 423839 = 635759) B635759
theorem B950039 : Blo 155795 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B6259193 : Blo 155795 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B1016545 : Blo 155795 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B263783 : Blo 155795 263783 := bstep (se 1 (by rfl) ⟨197837, by rfl⟩ : syracuseStep 263783 = 395675) B395675
theorem B233897 : Blo 155795 233897 := bstep (se 2 (by rfl) ⟨87711, by rfl⟩ : syracuseStep 233897 = 175423) B175423
theorem B4330397 : Blo 155795 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B268015 : Blo 155795 268015 := bstep (se 1 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 268015 = 402023) B402023
theorem B532223 : Blo 155795 532223 := bstep (se 1 (by rfl) ⟨399167, by rfl⟩ : syracuseStep 532223 = 798335) B798335
theorem B1780217 : Blo 155795 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B633359 : Blo 155795 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B1292507 : Blo 155795 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B1363391 : Blo 155795 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B282559 : Blo 155795 282559 := bstep (se 1 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 282559 = 423839) B423839
theorem B350927 : Blo 155795 350927 := bstep (se 1 (by rfl) ⟨263195, by rfl⟩ : syracuseStep 350927 = 526391) B526391
theorem B156703 : Blo 155795 156703 := bstep (se 1 (by rfl) ⟨117527, by rfl⟩ : syracuseStep 156703 = 235055) B235055
theorem B17459711 : Blo 155795 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B1142693 : Blo 155795 1142693 := bstep (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) B214255
theorem B159791 : Blo 155795 159791 := bstep (se 1 (by rfl) ⟨119843, by rfl⟩ : syracuseStep 159791 = 239687) B239687
theorem B359423 : Blo 155795 359423 := bstep (se 1 (by rfl) ⟨269567, by rfl⟩ : syracuseStep 359423 = 539135) B539135
theorem B621695 : Blo 155795 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B2886931 : Blo 155795 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B233951 : Blo 155795 233951 := bstep (se 1 (by rfl) ⟨175463, by rfl⟩ : syracuseStep 233951 = 350927) B350927
theorem B1186811 : Blo 155795 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B11639807 : Blo 155795 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B761795 : Blo 155795 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B861671 : Blo 155795 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B239615 : Blo 155795 239615 := bstep (se 1 (by rfl) ⟨179711, by rfl⟩ : syracuseStep 239615 = 359423) B359423
theorem B4172795 : Blo 155795 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B1355393 : Blo 155795 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B175855 : Blo 155795 175855 := bstep (se 1 (by rfl) ⟨131891, by rfl⟩ : syracuseStep 175855 = 263783) B263783
theorem B376745 : Blo 155795 376745 := bstep (se 2 (by rfl) ⟨141279, by rfl⟩ : syracuseStep 376745 = 282559) B282559
theorem B1688957 : Blo 155795 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B414463 : Blo 155795 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B908927 : Blo 155795 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B155931 : Blo 155795 155931 := bstep (se 1 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 155931 = 233897) B233897
theorem B354815 : Blo 155795 354815 := bstep (se 1 (by rfl) ⟨266111, by rfl⟩ : syracuseStep 354815 = 532223) B532223
theorem B357353 : Blo 155795 357353 := bstep (se 2 (by rfl) ⟨134007, by rfl⟩ : syracuseStep 357353 = 268015) B268015
theorem B791207 : Blo 155795 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B234473 : Blo 155795 234473 := bstep (se 2 (by rfl) ⟨87927, by rfl⟩ : syracuseStep 234473 = 175855) B175855
theorem B236543 : Blo 155795 236543 := bstep (se 1 (by rfl) ⟨177407, by rfl⟩ : syracuseStep 236543 = 354815) B354815
theorem B238235 : Blo 155795 238235 := bstep (se 1 (by rfl) ⟨178676, by rfl⟩ : syracuseStep 238235 = 357353) B357353
theorem B1125971 : Blo 155795 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B3849241 : Blo 155795 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B605951 : Blo 155795 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B507863 : Blo 155795 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B574447 : Blo 155795 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B903595 : Blo 155795 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B1004653 : Blo 155795 1004653 := bstep (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) B376745
theorem B155967 : Blo 155795 155967 := bstep (se 1 (by rfl) ⟨116975, by rfl⟩ : syracuseStep 155967 = 233951) B233951
theorem B7759871 : Blo 155795 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B552617 : Blo 155795 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B159743 : Blo 155795 159743 := bstep (se 1 (by rfl) ⟨119807, by rfl⟩ : syracuseStep 159743 = 239615) B239615
theorem B2781863 : Blo 155795 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B527471 : Blo 155795 527471 := bstep (se 1 (by rfl) ⟨395603, by rfl⟩ : syracuseStep 527471 = 791207) B791207
theorem B368411 : Blo 155795 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B403967 : Blo 155795 403967 := bstep (se 1 (by rfl) ⟨302975, by rfl⟩ : syracuseStep 403967 = 605951) B605951
theorem B338575 : Blo 155795 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B765929 : Blo 155795 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B1854575 : Blo 155795 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B5132321 : Blo 155795 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B1204793 : Blo 155795 1204793 := bstep (se 2 (by rfl) ⟨451797, by rfl⟩ : syracuseStep 1204793 = 903595) B903595
theorem B156315 : Blo 155795 156315 := bstep (se 1 (by rfl) ⟨117236, by rfl⟩ : syracuseStep 156315 = 234473) B234473
theorem B157695 : Blo 155795 157695 := bstep (se 1 (by rfl) ⟨118271, by rfl⟩ : syracuseStep 157695 = 236543) B236543
theorem B158823 : Blo 155795 158823 := bstep (se 1 (by rfl) ⟨119117, by rfl⟩ : syracuseStep 158823 = 238235) B238235
theorem B5173247 : Blo 155795 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B1339537 : Blo 155795 1339537 := bstep (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) B1004653
theorem B750647 : Blo 155795 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B269311 : Blo 155795 269311 := bstep (se 1 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 269311 = 403967) B403967
theorem B3448831 : Blo 155795 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B500431 : Blo 155795 500431 := bstep (se 1 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 500431 = 750647) B750647
theorem B3421547 : Blo 155795 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1786049 : Blo 155795 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B803195 : Blo 155795 803195 := bstep (se 1 (by rfl) ⟨602396, by rfl⟩ : syracuseStep 803195 = 1204793) B1204793
theorem B510619 : Blo 155795 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B351647 : Blo 155795 351647 := bstep (se 1 (by rfl) ⟨263735, by rfl⟩ : syracuseStep 351647 = 527471) B527471
theorem B1236383 : Blo 155795 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B451433 : Blo 155795 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B3929717 : Blo 155795 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B234431 : Blo 155795 234431 := bstep (se 1 (by rfl) ⟨175823, by rfl⟩ : syracuseStep 234431 = 351647) B351647
theorem B824255 : Blo 155795 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B4598441 : Blo 155795 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B1190699 : Blo 155795 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B535463 : Blo 155795 535463 := bstep (se 1 (by rfl) ⟨401597, by rfl⟩ : syracuseStep 535463 = 803195) B803195
theorem B667241 : Blo 155795 667241 := bstep (se 2 (by rfl) ⟨250215, by rfl⟩ : syracuseStep 667241 = 500431) B500431
theorem B2281031 : Blo 155795 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B1203821 : Blo 155795 1203821 := bstep (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) B451433
theorem B680825 : Blo 155795 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B2619811 : Blo 155795 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B359081 : Blo 155795 359081 := bstep (se 2 (by rfl) ⟨134655, by rfl⟩ : syracuseStep 359081 = 269311) B269311
theorem B793799 : Blo 155795 793799 := bstep (se 1 (by rfl) ⟨595349, by rfl⟩ : syracuseStep 793799 = 1190699) B1190699
theorem B239387 : Blo 155795 239387 := bstep (se 1 (by rfl) ⟨179540, by rfl⟩ : syracuseStep 239387 = 359081) B359081
theorem B1520687 : Blo 155795 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B802547 : Blo 155795 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B3065627 : Blo 155795 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B444827 : Blo 155795 444827 := bstep (se 1 (by rfl) ⟨333620, by rfl⟩ : syracuseStep 444827 = 667241) B667241
theorem B3493081 : Blo 155795 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B156287 : Blo 155795 156287 := bstep (se 1 (by rfl) ⟨117215, by rfl⟩ : syracuseStep 156287 = 234431) B234431
theorem B549503 : Blo 155795 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B453883 : Blo 155795 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B356975 : Blo 155795 356975 := bstep (se 1 (by rfl) ⟨267731, by rfl⟩ : syracuseStep 356975 = 535463) B535463
theorem B296551 : Blo 155795 296551 := bstep (se 1 (by rfl) ⟨222413, by rfl⟩ : syracuseStep 296551 = 444827) B444827
theorem B4657441 : Blo 155795 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B529199 : Blo 155795 529199 := bstep (se 1 (by rfl) ⟨396899, by rfl⟩ : syracuseStep 529199 = 793799) B793799
theorem B366335 : Blo 155795 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B237983 : Blo 155795 237983 := bstep (se 1 (by rfl) ⟨178487, by rfl⟩ : syracuseStep 237983 = 356975) B356975
theorem B535031 : Blo 155795 535031 := bstep (se 1 (by rfl) ⟨401273, by rfl⟩ : syracuseStep 535031 = 802547) B802547
theorem B2043751 : Blo 155795 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B605177 : Blo 155795 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B159591 : Blo 155795 159591 := bstep (se 1 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 159591 = 239387) B239387
theorem B1013791 : Blo 155795 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B395401 : Blo 155795 395401 := bstep (se 2 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 395401 = 296551) B296551
theorem B2725001 : Blo 155795 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B1351721 : Blo 155795 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B403451 : Blo 155795 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B244223 : Blo 155795 244223 := bstep (se 1 (by rfl) ⟨183167, by rfl⟩ : syracuseStep 244223 = 366335) B366335
theorem B6209921 : Blo 155795 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B352799 : Blo 155795 352799 := bstep (se 1 (by rfl) ⟨264599, by rfl⟩ : syracuseStep 352799 = 529199) B529199
theorem B158655 : Blo 155795 158655 := bstep (se 1 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 158655 = 237983) B237983
theorem B356687 : Blo 155795 356687 := bstep (se 1 (by rfl) ⟨267515, by rfl⟩ : syracuseStep 356687 = 535031) B535031
theorem B527201 : Blo 155795 527201 := bstep (se 2 (by rfl) ⟨197700, by rfl⟩ : syracuseStep 527201 = 395401) B395401
theorem B235199 : Blo 155795 235199 := bstep (se 1 (by rfl) ⟨176399, by rfl⟩ : syracuseStep 235199 = 352799) B352799
theorem B268967 : Blo 155795 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B237791 : Blo 155795 237791 := bstep (se 1 (by rfl) ⟨178343, by rfl⟩ : syracuseStep 237791 = 356687) B356687
theorem B4139947 : Blo 155795 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B1816667 : Blo 155795 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B901147 : Blo 155795 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B162815 : Blo 155795 162815 := bstep (se 1 (by rfl) ⟨122111, by rfl⟩ : syracuseStep 162815 = 244223) B244223
theorem B434173 : Blo 155795 434173 := bstep (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) B162815
theorem B5519929 : Blo 155795 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B179311 : Blo 155795 179311 := bstep (se 1 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 179311 = 268967) B268967
theorem B1201529 : Blo 155795 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B351467 : Blo 155795 351467 := bstep (se 1 (by rfl) ⟨263600, by rfl⟩ : syracuseStep 351467 = 527201) B527201
theorem B156799 : Blo 155795 156799 := bstep (se 1 (by rfl) ⟨117599, by rfl⟩ : syracuseStep 156799 = 235199) B235199
theorem B158527 : Blo 155795 158527 := bstep (se 1 (by rfl) ⟨118895, by rfl⟩ : syracuseStep 158527 = 237791) B237791
theorem B1211111 : Blo 155795 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B234311 : Blo 155795 234311 := bstep (se 1 (by rfl) ⟨175733, by rfl⟩ : syracuseStep 234311 = 351467) B351467
theorem B239081 : Blo 155795 239081 := bstep (se 2 (by rfl) ⟨89655, by rfl⟩ : syracuseStep 239081 = 179311) B179311
theorem B801019 : Blo 155795 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B7359905 : Blo 155795 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B807407 : Blo 155795 807407 := bstep (se 1 (by rfl) ⟨605555, by rfl⟩ : syracuseStep 807407 = 1211111) B1211111
theorem B578897 : Blo 155795 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B4272101 : Blo 155795 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B538271 : Blo 155795 538271 := bstep (se 1 (by rfl) ⟨403703, by rfl⟩ : syracuseStep 538271 = 807407) B807407
theorem B4906603 : Blo 155795 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B156207 : Blo 155795 156207 := bstep (se 1 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 156207 = 234311) B234311
theorem B385931 : Blo 155795 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B159387 : Blo 155795 159387 := bstep (se 1 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 159387 = 239081) B239081
theorem B6542137 : Blo 155795 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B257287 : Blo 155795 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B2848067 : Blo 155795 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B358847 : Blo 155795 358847 := bstep (se 1 (by rfl) ⟨269135, by rfl⟩ : syracuseStep 358847 = 538271) B538271
theorem B21955157 : Blo 155795 21955157 := bstep (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) B257287
theorem B239231 : Blo 155795 239231 := bstep (se 1 (by rfl) ⟨179423, by rfl⟩ : syracuseStep 239231 = 358847) B358847
theorem B34891397 : Blo 155795 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B1898711 : Blo 155795 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B1265807 : Blo 155795 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B14636771 : Blo 155795 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B159487 : Blo 155795 159487 := bstep (se 1 (by rfl) ⟨119615, by rfl⟩ : syracuseStep 159487 = 239231) B239231
theorem B23260931 : Blo 155795 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B15507287 : Blo 155795 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B843871 : Blo 155795 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B9757847 : Blo 155795 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B1125161 : Blo 155795 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B10338191 : Blo 155795 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B6505231 : Blo 155795 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B6892127 : Blo 155795 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B8673641 : Blo 155795 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B750107 : Blo 155795 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 155795 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B4594751 : Blo 155795 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B5782427 : Blo 155795 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B3063167 : Blo 155795 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B3854951 : Blo 155795 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B1333523 : Blo 155795 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B889015 : Blo 155795 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B2042111 : Blo 155795 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B2569967 : Blo 155795 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B1185353 : Blo 155795 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B1713311 : Blo 155795 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B1361407 : Blo 155795 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B790235 : Blo 155795 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B1815209 : Blo 155795 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B1142207 : Blo 155795 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B526823 : Blo 155795 526823 := bstep (se 1 (by rfl) ⟨395117, by rfl⟩ : syracuseStep 526823 = 790235) B790235
theorem B761471 : Blo 155795 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B1210139 : Blo 155795 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B507647 : Blo 155795 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B806759 : Blo 155795 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B351215 : Blo 155795 351215 := bstep (se 1 (by rfl) ⟨263411, by rfl⟩ : syracuseStep 351215 = 526823) B526823
theorem B234143 : Blo 155795 234143 := bstep (se 1 (by rfl) ⟨175607, by rfl⟩ : syracuseStep 234143 = 351215) B351215
theorem B338431 : Blo 155795 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B537839 : Blo 155795 537839 := bstep (se 1 (by rfl) ⟨403379, by rfl⟩ : syracuseStep 537839 = 806759) B806759
theorem B156095 : Blo 155795 156095 := bstep (se 1 (by rfl) ⟨117071, by rfl⟩ : syracuseStep 156095 = 234143) B234143
theorem B451241 : Blo 155795 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B358559 : Blo 155795 358559 := bstep (se 1 (by rfl) ⟨268919, by rfl⟩ : syracuseStep 358559 = 537839) B537839
theorem B300827 : Blo 155795 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B239039 : Blo 155795 239039 := bstep (se 1 (by rfl) ⟨179279, by rfl⟩ : syracuseStep 239039 = 358559) B358559
theorem B200551 : Blo 155795 200551 := bstep (se 1 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 200551 = 300827) B300827
theorem B159359 : Blo 155795 159359 := bstep (se 1 (by rfl) ⟨119519, by rfl⟩ : syracuseStep 159359 = 239039) B239039
theorem B267401 : Blo 155795 267401 := bstep (se 2 (by rfl) ⟨100275, by rfl⟩ : syracuseStep 267401 = 200551) B200551
theorem B178267 : Blo 155795 178267 := bstep (se 1 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 178267 = 267401) B267401
theorem B237689 : Blo 155795 237689 := bstep (se 2 (by rfl) ⟨89133, by rfl⟩ : syracuseStep 237689 = 178267) B178267
theorem B158459 : Blo 155795 158459 := bstep (se 1 (by rfl) ⟨118844, by rfl⟩ : syracuseStep 158459 = 237689) B237689

theorem C0 (j : ℕ) (h1 : 38948 ≤ j) (h2 : j ≤ 39647) : Blo 155795 (4 * j + 3) := by
  interval_cases j
  · exact B155795
  · exact B155799
  · exact B155803
  · exact B155807
  · exact B155811
  · exact B155815
  · exact B155819
  · exact B155823
  · exact B155827
  · exact B155831
  · exact B155835
  · exact B155839
  · exact B155843
  · exact B155847
  · exact B155851
  · exact B155855
  · exact B155859
  · exact B155863
  · exact B155867
  · exact B155871
  · exact B155875
  · exact B155879
  · exact B155883
  · exact B155887
  · exact B155891
  · exact B155895
  · exact B155899
  · exact B155903
  · exact B155907
  · exact B155911
  · exact B155915
  · exact B155919
  · exact B155923
  · exact B155927
  · exact B155931
  · exact B155935
  · exact B155939
  · exact B155943
  · exact B155947
  · exact B155951
  · exact B155955
  · exact B155959
  · exact B155963
  · exact B155967
  · exact B155971
  · exact B155975
  · exact B155979
  · exact B155983
  · exact B155987
  · exact B155991
  · exact B155995
  · exact B155999
  · exact B156003
  · exact B156007
  · exact B156011
  · exact B156015
  · exact B156019
  · exact B156023
  · exact B156027
  · exact B156031
  · exact B156035
  · exact B156039
  · exact B156043
  · exact B156047
  · exact B156051
  · exact B156055
  · exact B156059
  · exact B156063
  · exact B156067
  · exact B156071
  · exact B156075
  · exact B156079
  · exact B156083
  · exact B156087
  · exact B156091
  · exact B156095
  · exact B156099
  · exact B156103
  · exact B156107
  · exact B156111
  · exact B156115
  · exact B156119
  · exact B156123
  · exact B156127
  · exact B156131
  · exact B156135
  · exact B156139
  · exact B156143
  · exact B156147
  · exact B156151
  · exact B156155
  · exact B156159
  · exact B156163
  · exact B156167
  · exact B156171
  · exact B156175
  · exact B156179
  · exact B156183
  · exact B156187
  · exact B156191
  · exact B156195
  · exact B156199
  · exact B156203
  · exact B156207
  · exact B156211
  · exact B156215
  · exact B156219
  · exact B156223
  · exact B156227
  · exact B156231
  · exact B156235
  · exact B156239
  · exact B156243
  · exact B156247
  · exact B156251
  · exact B156255
  · exact B156259
  · exact B156263
  · exact B156267
  · exact B156271
  · exact B156275
  · exact B156279
  · exact B156283
  · exact B156287
  · exact B156291
  · exact B156295
  · exact B156299
  · exact B156303
  · exact B156307
  · exact B156311
  · exact B156315
  · exact B156319
  · exact B156323
  · exact B156327
  · exact B156331
  · exact B156335
  · exact B156339
  · exact B156343
  · exact B156347
  · exact B156351
  · exact B156355
  · exact B156359
  · exact B156363
  · exact B156367
  · exact B156371
  · exact B156375
  · exact B156379
  · exact B156383
  · exact B156387
  · exact B156391
  · exact B156395
  · exact B156399
  · exact B156403
  · exact B156407
  · exact B156411
  · exact B156415
  · exact B156419
  · exact B156423
  · exact B156427
  · exact B156431
  · exact B156435
  · exact B156439
  · exact B156443
  · exact B156447
  · exact B156451
  · exact B156455
  · exact B156459
  · exact B156463
  · exact B156467
  · exact B156471
  · exact B156475
  · exact B156479
  · exact B156483
  · exact B156487
  · exact B156491
  · exact B156495
  · exact B156499
  · exact B156503
  · exact B156507
  · exact B156511
  · exact B156515
  · exact B156519
  · exact B156523
  · exact B156527
  · exact B156531
  · exact B156535
  · exact B156539
  · exact B156543
  · exact B156547
  · exact B156551
  · exact B156555
  · exact B156559
  · exact B156563
  · exact B156567
  · exact B156571
  · exact B156575
  · exact B156579
  · exact B156583
  · exact B156587
  · exact B156591
  · exact B156595
  · exact B156599
  · exact B156603
  · exact B156607
  · exact B156611
  · exact B156615
  · exact B156619
  · exact B156623
  · exact B156627
  · exact B156631
  · exact B156635
  · exact B156639
  · exact B156643
  · exact B156647
  · exact B156651
  · exact B156655
  · exact B156659
  · exact B156663
  · exact B156667
  · exact B156671
  · exact B156675
  · exact B156679
  · exact B156683
  · exact B156687
  · exact B156691
  · exact B156695
  · exact B156699
  · exact B156703
  · exact B156707
  · exact B156711
  · exact B156715
  · exact B156719
  · exact B156723
  · exact B156727
  · exact B156731
  · exact B156735
  · exact B156739
  · exact B156743
  · exact B156747
  · exact B156751
  · exact B156755
  · exact B156759
  · exact B156763
  · exact B156767
  · exact B156771
  · exact B156775
  · exact B156779
  · exact B156783
  · exact B156787
  · exact B156791
  · exact B156795
  · exact B156799
  · exact B156803
  · exact B156807
  · exact B156811
  · exact B156815
  · exact B156819
  · exact B156823
  · exact B156827
  · exact B156831
  · exact B156835
  · exact B156839
  · exact B156843
  · exact B156847
  · exact B156851
  · exact B156855
  · exact B156859
  · exact B156863
  · exact B156867
  · exact B156871
  · exact B156875
  · exact B156879
  · exact B156883
  · exact B156887
  · exact B156891
  · exact B156895
  · exact B156899
  · exact B156903
  · exact B156907
  · exact B156911
  · exact B156915
  · exact B156919
  · exact B156923
  · exact B156927
  · exact B156931
  · exact B156935
  · exact B156939
  · exact B156943
  · exact B156947
  · exact B156951
  · exact B156955
  · exact B156959
  · exact B156963
  · exact B156967
  · exact B156971
  · exact B156975
  · exact B156979
  · exact B156983
  · exact B156987
  · exact B156991
  · exact B156995
  · exact B156999
  · exact B157003
  · exact B157007
  · exact B157011
  · exact B157015
  · exact B157019
  · exact B157023
  · exact B157027
  · exact B157031
  · exact B157035
  · exact B157039
  · exact B157043
  · exact B157047
  · exact B157051
  · exact B157055
  · exact B157059
  · exact B157063
  · exact B157067
  · exact B157071
  · exact B157075
  · exact B157079
  · exact B157083
  · exact B157087
  · exact B157091
  · exact B157095
  · exact B157099
  · exact B157103
  · exact B157107
  · exact B157111
  · exact B157115
  · exact B157119
  · exact B157123
  · exact B157127
  · exact B157131
  · exact B157135
  · exact B157139
  · exact B157143
  · exact B157147
  · exact B157151
  · exact B157155
  · exact B157159
  · exact B157163
  · exact B157167
  · exact B157171
  · exact B157175
  · exact B157179
  · exact B157183
  · exact B157187
  · exact B157191
  · exact B157195
  · exact B157199
  · exact B157203
  · exact B157207
  · exact B157211
  · exact B157215
  · exact B157219
  · exact B157223
  · exact B157227
  · exact B157231
  · exact B157235
  · exact B157239
  · exact B157243
  · exact B157247
  · exact B157251
  · exact B157255
  · exact B157259
  · exact B157263
  · exact B157267
  · exact B157271
  · exact B157275
  · exact B157279
  · exact B157283
  · exact B157287
  · exact B157291
  · exact B157295
  · exact B157299
  · exact B157303
  · exact B157307
  · exact B157311
  · exact B157315
  · exact B157319
  · exact B157323
  · exact B157327
  · exact B157331
  · exact B157335
  · exact B157339
  · exact B157343
  · exact B157347
  · exact B157351
  · exact B157355
  · exact B157359
  · exact B157363
  · exact B157367
  · exact B157371
  · exact B157375
  · exact B157379
  · exact B157383
  · exact B157387
  · exact B157391
  · exact B157395
  · exact B157399
  · exact B157403
  · exact B157407
  · exact B157411
  · exact B157415
  · exact B157419
  · exact B157423
  · exact B157427
  · exact B157431
  · exact B157435
  · exact B157439
  · exact B157443
  · exact B157447
  · exact B157451
  · exact B157455
  · exact B157459
  · exact B157463
  · exact B157467
  · exact B157471
  · exact B157475
  · exact B157479
  · exact B157483
  · exact B157487
  · exact B157491
  · exact B157495
  · exact B157499
  · exact B157503
  · exact B157507
  · exact B157511
  · exact B157515
  · exact B157519
  · exact B157523
  · exact B157527
  · exact B157531
  · exact B157535
  · exact B157539
  · exact B157543
  · exact B157547
  · exact B157551
  · exact B157555
  · exact B157559
  · exact B157563
  · exact B157567
  · exact B157571
  · exact B157575
  · exact B157579
  · exact B157583
  · exact B157587
  · exact B157591
  · exact B157595
  · exact B157599
  · exact B157603
  · exact B157607
  · exact B157611
  · exact B157615
  · exact B157619
  · exact B157623
  · exact B157627
  · exact B157631
  · exact B157635
  · exact B157639
  · exact B157643
  · exact B157647
  · exact B157651
  · exact B157655
  · exact B157659
  · exact B157663
  · exact B157667
  · exact B157671
  · exact B157675
  · exact B157679
  · exact B157683
  · exact B157687
  · exact B157691
  · exact B157695
  · exact B157699
  · exact B157703
  · exact B157707
  · exact B157711
  · exact B157715
  · exact B157719
  · exact B157723
  · exact B157727
  · exact B157731
  · exact B157735
  · exact B157739
  · exact B157743
  · exact B157747
  · exact B157751
  · exact B157755
  · exact B157759
  · exact B157763
  · exact B157767
  · exact B157771
  · exact B157775
  · exact B157779
  · exact B157783
  · exact B157787
  · exact B157791
  · exact B157795
  · exact B157799
  · exact B157803
  · exact B157807
  · exact B157811
  · exact B157815
  · exact B157819
  · exact B157823
  · exact B157827
  · exact B157831
  · exact B157835
  · exact B157839
  · exact B157843
  · exact B157847
  · exact B157851
  · exact B157855
  · exact B157859
  · exact B157863
  · exact B157867
  · exact B157871
  · exact B157875
  · exact B157879
  · exact B157883
  · exact B157887
  · exact B157891
  · exact B157895
  · exact B157899
  · exact B157903
  · exact B157907
  · exact B157911
  · exact B157915
  · exact B157919
  · exact B157923
  · exact B157927
  · exact B157931
  · exact B157935
  · exact B157939
  · exact B157943
  · exact B157947
  · exact B157951
  · exact B157955
  · exact B157959
  · exact B157963
  · exact B157967
  · exact B157971
  · exact B157975
  · exact B157979
  · exact B157983
  · exact B157987
  · exact B157991
  · exact B157995
  · exact B157999
  · exact B158003
  · exact B158007
  · exact B158011
  · exact B158015
  · exact B158019
  · exact B158023
  · exact B158027
  · exact B158031
  · exact B158035
  · exact B158039
  · exact B158043
  · exact B158047
  · exact B158051
  · exact B158055
  · exact B158059
  · exact B158063
  · exact B158067
  · exact B158071
  · exact B158075
  · exact B158079
  · exact B158083
  · exact B158087
  · exact B158091
  · exact B158095
  · exact B158099
  · exact B158103
  · exact B158107
  · exact B158111
  · exact B158115
  · exact B158119
  · exact B158123
  · exact B158127
  · exact B158131
  · exact B158135
  · exact B158139
  · exact B158143
  · exact B158147
  · exact B158151
  · exact B158155
  · exact B158159
  · exact B158163
  · exact B158167
  · exact B158171
  · exact B158175
  · exact B158179
  · exact B158183
  · exact B158187
  · exact B158191
  · exact B158195
  · exact B158199
  · exact B158203
  · exact B158207
  · exact B158211
  · exact B158215
  · exact B158219
  · exact B158223
  · exact B158227
  · exact B158231
  · exact B158235
  · exact B158239
  · exact B158243
  · exact B158247
  · exact B158251
  · exact B158255
  · exact B158259
  · exact B158263
  · exact B158267
  · exact B158271
  · exact B158275
  · exact B158279
  · exact B158283
  · exact B158287
  · exact B158291
  · exact B158295
  · exact B158299
  · exact B158303
  · exact B158307
  · exact B158311
  · exact B158315
  · exact B158319
  · exact B158323
  · exact B158327
  · exact B158331
  · exact B158335
  · exact B158339
  · exact B158343
  · exact B158347
  · exact B158351
  · exact B158355
  · exact B158359
  · exact B158363
  · exact B158367
  · exact B158371
  · exact B158375
  · exact B158379
  · exact B158383
  · exact B158387
  · exact B158391
  · exact B158395
  · exact B158399
  · exact B158403
  · exact B158407
  · exact B158411
  · exact B158415
  · exact B158419
  · exact B158423
  · exact B158427
  · exact B158431
  · exact B158435
  · exact B158439
  · exact B158443
  · exact B158447
  · exact B158451
  · exact B158455
  · exact B158459
  · exact B158463
  · exact B158467
  · exact B158471
  · exact B158475
  · exact B158479
  · exact B158483
  · exact B158487
  · exact B158491
  · exact B158495
  · exact B158499
  · exact B158503
  · exact B158507
  · exact B158511
  · exact B158515
  · exact B158519
  · exact B158523
  · exact B158527
  · exact B158531
  · exact B158535
  · exact B158539
  · exact B158543
  · exact B158547
  · exact B158551
  · exact B158555
  · exact B158559
  · exact B158563
  · exact B158567
  · exact B158571
  · exact B158575
  · exact B158579
  · exact B158583
  · exact B158587
  · exact B158591

theorem C1 (j : ℕ) (h1 : 39648 ≤ j) (h2 : j ≤ 39948) : Blo 155795 (4 * j + 3) := by
  interval_cases j
  · exact B158595
  · exact B158599
  · exact B158603
  · exact B158607
  · exact B158611
  · exact B158615
  · exact B158619
  · exact B158623
  · exact B158627
  · exact B158631
  · exact B158635
  · exact B158639
  · exact B158643
  · exact B158647
  · exact B158651
  · exact B158655
  · exact B158659
  · exact B158663
  · exact B158667
  · exact B158671
  · exact B158675
  · exact B158679
  · exact B158683
  · exact B158687
  · exact B158691
  · exact B158695
  · exact B158699
  · exact B158703
  · exact B158707
  · exact B158711
  · exact B158715
  · exact B158719
  · exact B158723
  · exact B158727
  · exact B158731
  · exact B158735
  · exact B158739
  · exact B158743
  · exact B158747
  · exact B158751
  · exact B158755
  · exact B158759
  · exact B158763
  · exact B158767
  · exact B158771
  · exact B158775
  · exact B158779
  · exact B158783
  · exact B158787
  · exact B158791
  · exact B158795
  · exact B158799
  · exact B158803
  · exact B158807
  · exact B158811
  · exact B158815
  · exact B158819
  · exact B158823
  · exact B158827
  · exact B158831
  · exact B158835
  · exact B158839
  · exact B158843
  · exact B158847
  · exact B158851
  · exact B158855
  · exact B158859
  · exact B158863
  · exact B158867
  · exact B158871
  · exact B158875
  · exact B158879
  · exact B158883
  · exact B158887
  · exact B158891
  · exact B158895
  · exact B158899
  · exact B158903
  · exact B158907
  · exact B158911
  · exact B158915
  · exact B158919
  · exact B158923
  · exact B158927
  · exact B158931
  · exact B158935
  · exact B158939
  · exact B158943
  · exact B158947
  · exact B158951
  · exact B158955
  · exact B158959
  · exact B158963
  · exact B158967
  · exact B158971
  · exact B158975
  · exact B158979
  · exact B158983
  · exact B158987
  · exact B158991
  · exact B158995
  · exact B158999
  · exact B159003
  · exact B159007
  · exact B159011
  · exact B159015
  · exact B159019
  · exact B159023
  · exact B159027
  · exact B159031
  · exact B159035
  · exact B159039
  · exact B159043
  · exact B159047
  · exact B159051
  · exact B159055
  · exact B159059
  · exact B159063
  · exact B159067
  · exact B159071
  · exact B159075
  · exact B159079
  · exact B159083
  · exact B159087
  · exact B159091
  · exact B159095
  · exact B159099
  · exact B159103
  · exact B159107
  · exact B159111
  · exact B159115
  · exact B159119
  · exact B159123
  · exact B159127
  · exact B159131
  · exact B159135
  · exact B159139
  · exact B159143
  · exact B159147
  · exact B159151
  · exact B159155
  · exact B159159
  · exact B159163
  · exact B159167
  · exact B159171
  · exact B159175
  · exact B159179
  · exact B159183
  · exact B159187
  · exact B159191
  · exact B159195
  · exact B159199
  · exact B159203
  · exact B159207
  · exact B159211
  · exact B159215
  · exact B159219
  · exact B159223
  · exact B159227
  · exact B159231
  · exact B159235
  · exact B159239
  · exact B159243
  · exact B159247
  · exact B159251
  · exact B159255
  · exact B159259
  · exact B159263
  · exact B159267
  · exact B159271
  · exact B159275
  · exact B159279
  · exact B159283
  · exact B159287
  · exact B159291
  · exact B159295
  · exact B159299
  · exact B159303
  · exact B159307
  · exact B159311
  · exact B159315
  · exact B159319
  · exact B159323
  · exact B159327
  · exact B159331
  · exact B159335
  · exact B159339
  · exact B159343
  · exact B159347
  · exact B159351
  · exact B159355
  · exact B159359
  · exact B159363
  · exact B159367
  · exact B159371
  · exact B159375
  · exact B159379
  · exact B159383
  · exact B159387
  · exact B159391
  · exact B159395
  · exact B159399
  · exact B159403
  · exact B159407
  · exact B159411
  · exact B159415
  · exact B159419
  · exact B159423
  · exact B159427
  · exact B159431
  · exact B159435
  · exact B159439
  · exact B159443
  · exact B159447
  · exact B159451
  · exact B159455
  · exact B159459
  · exact B159463
  · exact B159467
  · exact B159471
  · exact B159475
  · exact B159479
  · exact B159483
  · exact B159487
  · exact B159491
  · exact B159495
  · exact B159499
  · exact B159503
  · exact B159507
  · exact B159511
  · exact B159515
  · exact B159519
  · exact B159523
  · exact B159527
  · exact B159531
  · exact B159535
  · exact B159539
  · exact B159543
  · exact B159547
  · exact B159551
  · exact B159555
  · exact B159559
  · exact B159563
  · exact B159567
  · exact B159571
  · exact B159575
  · exact B159579
  · exact B159583
  · exact B159587
  · exact B159591
  · exact B159595
  · exact B159599
  · exact B159603
  · exact B159607
  · exact B159611
  · exact B159615
  · exact B159619
  · exact B159623
  · exact B159627
  · exact B159631
  · exact B159635
  · exact B159639
  · exact B159643
  · exact B159647
  · exact B159651
  · exact B159655
  · exact B159659
  · exact B159663
  · exact B159667
  · exact B159671
  · exact B159675
  · exact B159679
  · exact B159683
  · exact B159687
  · exact B159691
  · exact B159695
  · exact B159699
  · exact B159703
  · exact B159707
  · exact B159711
  · exact B159715
  · exact B159719
  · exact B159723
  · exact B159727
  · exact B159731
  · exact B159735
  · exact B159739
  · exact B159743
  · exact B159747
  · exact B159751
  · exact B159755
  · exact B159759
  · exact B159763
  · exact B159767
  · exact B159771
  · exact B159775
  · exact B159779
  · exact B159783
  · exact B159787
  · exact B159791
  · exact B159795

theorem solution (m : ℕ) (hlo : 155795 ≤ m) (hhi : m ≤ 159795) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 38948 ≤ j := by omega
    have hj2 : j ≤ 39948 := by omega
    have hb : Blo 155795 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 39648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
