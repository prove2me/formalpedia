-- Prove2me | solution 1 for syracuse_descends_range_1342990_1344990
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:46.159018+00:00
-- url     : https://prove2.me/submissions/1f0fd483-5ce4-4591-8527-ee4212ad955d

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


theorem B2015237 : Blo 1342990 2015237 := bbase (se 4 (by rfl) ⟨188928, by rfl⟩ : syracuseStep 2015237 = 377857) (by norm_num)
theorem B2015261 : Blo 1342990 2015261 := bbase (se 3 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 2015261 = 755723) (by norm_num)
theorem B3825701 : Blo 1342990 3825701 := bbase (se 4 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 3825701 = 717319) (by norm_num)
theorem B3022901 : Blo 1342990 3022901 := bbase (se 5 (by rfl) ⟨141698, by rfl⟩ : syracuseStep 3022901 = 283397) (by norm_num)
theorem B2015285 : Blo 1342990 2015285 := bbase (se 5 (by rfl) ⟨94466, by rfl⟩ : syracuseStep 2015285 = 188933) (by norm_num)
theorem B2015309 : Blo 1342990 2015309 := bbase (se 3 (by rfl) ⟨377870, by rfl⟩ : syracuseStep 2015309 = 755741) (by norm_num)
theorem B2015333 : Blo 1342990 2015333 := bbase (se 4 (by rfl) ⟨188937, by rfl⟩ : syracuseStep 2015333 = 377875) (by norm_num)
theorem B3022973 : Blo 1342990 3022973 := bbase (se 3 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 3022973 = 1133615) (by norm_num)
theorem B2015357 : Blo 1342990 2015357 := bbase (se 3 (by rfl) ⟨377879, by rfl⟩ : syracuseStep 2015357 = 755759) (by norm_num)
theorem B2269309 : Blo 1342990 2269309 := bbase (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) (by norm_num)
theorem B2015381 : Blo 1342990 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B3399853 : Blo 1342990 3399853 := bbase (se 3 (by rfl) ⟨637472, by rfl⟩ : syracuseStep 3399853 = 1274945) (by norm_num)
theorem B2015405 : Blo 1342990 2015405 := bbase (se 3 (by rfl) ⟨377888, by rfl⟩ : syracuseStep 2015405 = 755777) (by norm_num)
theorem B8282293 : Blo 1342990 8282293 := bbase (se 5 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 8282293 = 776465) (by norm_num)
theorem B1532101 : Blo 1342990 1532101 := bbase (se 4 (by rfl) ⟨143634, by rfl⟩ : syracuseStep 1532101 = 287269) (by norm_num)
theorem B3023045 : Blo 1342990 3023045 := bbase (se 4 (by rfl) ⟨283410, by rfl⟩ : syracuseStep 3023045 = 566821) (by norm_num)
theorem B2015429 : Blo 1342990 2015429 := bbase (se 4 (by rfl) ⟨188946, by rfl⟩ : syracuseStep 2015429 = 377893) (by norm_num)
theorem B2269397 : Blo 1342990 2269397 := bbase (se 7 (by rfl) ⟨26594, by rfl⟩ : syracuseStep 2269397 = 53189) (by norm_num)
theorem B2015453 : Blo 1342990 2015453 := bbase (se 3 (by rfl) ⟨377897, by rfl⟩ : syracuseStep 2015453 = 755795) (by norm_num)
theorem B2015477 : Blo 1342990 2015477 := bbase (se 5 (by rfl) ⟨94475, by rfl⟩ : syracuseStep 2015477 = 188951) (by norm_num)
theorem B3023117 : Blo 1342990 3023117 := bbase (se 3 (by rfl) ⟨566834, by rfl⟩ : syracuseStep 3023117 = 1133669) (by norm_num)
theorem B2015501 : Blo 1342990 2015501 := bbase (se 3 (by rfl) ⟨377906, by rfl⟩ : syracuseStep 2015501 = 755813) (by norm_num)
theorem B4538645 : Blo 1342990 4538645 := bbase (se 6 (by rfl) ⟨106374, by rfl⟩ : syracuseStep 4538645 = 212749) (by norm_num)
theorem B3399965 : Blo 1342990 3399965 := bbase (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) (by norm_num)
theorem B2015525 : Blo 1342990 2015525 := bbase (se 4 (by rfl) ⟨188955, by rfl⟩ : syracuseStep 2015525 = 377911) (by norm_num)
theorem B2015549 : Blo 1342990 2015549 := bbase (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) (by norm_num)
theorem B3023189 : Blo 1342990 3023189 := bbase (se 10 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 3023189 = 8857) (by norm_num)
theorem B2015573 : Blo 1342990 2015573 := bbase (se 10 (by rfl) ⟨2952, by rfl⟩ : syracuseStep 2015573 = 5905) (by norm_num)
theorem B2269525 : Blo 1342990 2269525 := bbase (se 10 (by rfl) ⟨3324, by rfl⟩ : syracuseStep 2269525 = 6649) (by norm_num)
theorem B3228005 : Blo 1342990 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B2015597 : Blo 1342990 2015597 := bbase (se 3 (by rfl) ⟨377924, by rfl⟩ : syracuseStep 2015597 = 755849) (by norm_num)
theorem B2015621 : Blo 1342990 2015621 := bbase (se 4 (by rfl) ⟨188964, by rfl⟩ : syracuseStep 2015621 = 377929) (by norm_num)
theorem B3023261 : Blo 1342990 3023261 := bbase (se 3 (by rfl) ⟨566861, by rfl⟩ : syracuseStep 3023261 = 1133723) (by norm_num)
theorem B2015645 : Blo 1342990 2015645 := bbase (se 3 (by rfl) ⟨377933, by rfl⟩ : syracuseStep 2015645 = 755867) (by norm_num)
theorem B6455717 : Blo 1342990 6455717 := bbase (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) (by norm_num)
theorem B2269613 : Blo 1342990 2269613 := bbase (se 3 (by rfl) ⟨425552, by rfl⟩ : syracuseStep 2269613 = 851105) (by norm_num)
theorem B2015669 : Blo 1342990 2015669 := bbase (se 5 (by rfl) ⟨94484, by rfl⟩ : syracuseStep 2015669 = 188969) (by norm_num)
theorem B2015693 : Blo 1342990 2015693 := bbase (se 3 (by rfl) ⟨377942, by rfl⟩ : syracuseStep 2015693 = 755885) (by norm_num)
theorem B3400157 : Blo 1342990 3400157 := bbase (se 3 (by rfl) ⟨637529, by rfl⟩ : syracuseStep 3400157 = 1275059) (by norm_num)
theorem B3023333 : Blo 1342990 3023333 := bbase (se 4 (by rfl) ⟨283437, by rfl⟩ : syracuseStep 3023333 = 566875) (by norm_num)
theorem B2015717 : Blo 1342990 2015717 := bbase (se 4 (by rfl) ⟨188973, by rfl⟩ : syracuseStep 2015717 = 377947) (by norm_num)
theorem B2015741 : Blo 1342990 2015741 := bbase (se 3 (by rfl) ⟨377951, by rfl⟩ : syracuseStep 2015741 = 755903) (by norm_num)
theorem B2015765 : Blo 1342990 2015765 := bbase (se 6 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 2015765 = 94489) (by norm_num)
theorem B3023405 : Blo 1342990 3023405 := bbase (se 3 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 3023405 = 1133777) (by norm_num)
theorem B2015789 : Blo 1342990 2015789 := bbase (se 3 (by rfl) ⟨377960, by rfl⟩ : syracuseStep 2015789 = 755921) (by norm_num)
theorem B2015813 : Blo 1342990 2015813 := bbase (se 4 (by rfl) ⟨188982, by rfl⟩ : syracuseStep 2015813 = 377965) (by norm_num)
theorem B2015837 : Blo 1342990 2015837 := bbase (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) (by norm_num)
theorem B3023477 : Blo 1342990 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B2015861 : Blo 1342990 2015861 := bbase (se 5 (by rfl) ⟨94493, by rfl⟩ : syracuseStep 2015861 = 188987) (by norm_num)
theorem B1434245 : Blo 1342990 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B2015885 : Blo 1342990 2015885 := bbase (se 3 (by rfl) ⟨377978, by rfl⟩ : syracuseStep 2015885 = 755957) (by norm_num)
theorem B2015909 : Blo 1342990 2015909 := bbase (se 4 (by rfl) ⟨188991, by rfl⟩ : syracuseStep 2015909 = 377983) (by norm_num)
theorem B3023549 : Blo 1342990 3023549 := bbase (se 3 (by rfl) ⟨566915, by rfl⟩ : syracuseStep 3023549 = 1133831) (by norm_num)
theorem B2015933 : Blo 1342990 2015933 := bbase (se 3 (by rfl) ⟨377987, by rfl⟩ : syracuseStep 2015933 = 755975) (by norm_num)
theorem B1434305 : Blo 1342990 1434305 := bbase (se 2 (by rfl) ⟨537864, by rfl⟩ : syracuseStep 1434305 = 1075729) (by norm_num)
theorem B4539077 : Blo 1342990 4539077 := bbase (se 4 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 4539077 = 851077) (by norm_num)
theorem B2015957 : Blo 1342990 2015957 := bbase (se 7 (by rfl) ⟨23624, by rfl⟩ : syracuseStep 2015957 = 47249) (by norm_num)
theorem B1532629 : Blo 1342990 1532629 := bbase (se 7 (by rfl) ⟨17960, by rfl⟩ : syracuseStep 1532629 = 35921) (by norm_num)
theorem B3228389 : Blo 1342990 3228389 := bbase (se 4 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 3228389 = 605323) (by norm_num)
theorem B2015981 : Blo 1342990 2015981 := bbase (se 3 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 2015981 = 755993) (by norm_num)
theorem B1614593 : Blo 1342990 1614593 := bbase (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) (by norm_num)
theorem B3023621 : Blo 1342990 3023621 := bbase (se 4 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 3023621 = 566929) (by norm_num)
theorem B2016005 : Blo 1342990 2016005 := bbase (se 4 (by rfl) ⟨189000, by rfl⟩ : syracuseStep 2016005 = 378001) (by norm_num)
theorem B5817109 : Blo 1342990 5817109 := bbase (se 6 (by rfl) ⟨136338, by rfl⟩ : syracuseStep 5817109 = 272677) (by norm_num)
theorem B3826453 : Blo 1342990 3826453 := bbase (se 6 (by rfl) ⟨89682, by rfl⟩ : syracuseStep 3826453 = 179365) (by norm_num)
theorem B2016029 : Blo 1342990 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B3400501 : Blo 1342990 3400501 := bbase (se 5 (by rfl) ⟨159398, by rfl⟩ : syracuseStep 3400501 = 318797) (by norm_num)
theorem B2016053 : Blo 1342990 2016053 := bbase (se 5 (by rfl) ⟨94502, by rfl⟩ : syracuseStep 2016053 = 189005) (by norm_num)
theorem B6808373 : Blo 1342990 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B1434433 : Blo 1342990 1434433 := bbase (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) (by norm_num)
theorem B3023693 : Blo 1342990 3023693 := bbase (se 3 (by rfl) ⟨566942, by rfl⟩ : syracuseStep 3023693 = 1133885) (by norm_num)
theorem B2016077 : Blo 1342990 2016077 := bbase (se 3 (by rfl) ⟨378014, by rfl⟩ : syracuseStep 2016077 = 756029) (by norm_num)
theorem B2016101 : Blo 1342990 2016101 := bbase (se 4 (by rfl) ⟨189009, by rfl⟩ : syracuseStep 2016101 = 378019) (by norm_num)
theorem B2016125 : Blo 1342990 2016125 := bbase (se 3 (by rfl) ⟨378023, by rfl⟩ : syracuseStep 2016125 = 756047) (by norm_num)
theorem B18637717 : Blo 1342990 18637717 := bbase (se 6 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 18637717 = 873643) (by norm_num)
theorem B3023765 : Blo 1342990 3023765 := bbase (se 6 (by rfl) ⟨70869, by rfl⟩ : syracuseStep 3023765 = 141739) (by norm_num)
theorem B2016149 : Blo 1342990 2016149 := bbase (se 6 (by rfl) ⟨47253, by rfl⟩ : syracuseStep 2016149 = 94507) (by norm_num)
theorem B3400613 : Blo 1342990 3400613 := bbase (se 4 (by rfl) ⟨318807, by rfl⟩ : syracuseStep 3400613 = 637615) (by norm_num)
theorem B3228589 : Blo 1342990 3228589 := bbase (se 3 (by rfl) ⟨605360, by rfl⟩ : syracuseStep 3228589 = 1210721) (by norm_num)
theorem B2016173 : Blo 1342990 2016173 := bbase (se 3 (by rfl) ⟨378032, by rfl⟩ : syracuseStep 2016173 = 756065) (by norm_num)
theorem B5104565 : Blo 1342990 5104565 := bbase (se 5 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 5104565 = 478553) (by norm_num)
theorem B5743541 : Blo 1342990 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B2016197 : Blo 1342990 2016197 := bbase (se 4 (by rfl) ⟨189018, by rfl⟩ : syracuseStep 2016197 = 378037) (by norm_num)
theorem B3023837 : Blo 1342990 3023837 := bbase (se 3 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 3023837 = 1133939) (by norm_num)
theorem B2016221 : Blo 1342990 2016221 := bbase (se 3 (by rfl) ⟨378041, by rfl⟩ : syracuseStep 2016221 = 756083) (by norm_num)
theorem B2016245 : Blo 1342990 2016245 := bbase (se 5 (by rfl) ⟨94511, by rfl⟩ : syracuseStep 2016245 = 189023) (by norm_num)
theorem B2016269 : Blo 1342990 2016269 := bbase (se 3 (by rfl) ⟨378050, by rfl⟩ : syracuseStep 2016269 = 756101) (by norm_num)
theorem B3023909 : Blo 1342990 3023909 := bbase (se 4 (by rfl) ⟨283491, by rfl⟩ : syracuseStep 3023909 = 566983) (by norm_num)
theorem B2016293 : Blo 1342990 2016293 := bbase (se 4 (by rfl) ⟨189027, by rfl⟩ : syracuseStep 2016293 = 378055) (by norm_num)
theorem B2016317 : Blo 1342990 2016317 := bbase (se 3 (by rfl) ⟨378059, by rfl⟩ : syracuseStep 2016317 = 756119) (by norm_num)
theorem B1614925 : Blo 1342990 1614925 := bbase (se 3 (by rfl) ⟨302798, by rfl⟩ : syracuseStep 1614925 = 605597) (by norm_num)
theorem B2016341 : Blo 1342990 2016341 := bbase (se 8 (by rfl) ⟨11814, by rfl⟩ : syracuseStep 2016341 = 23629) (by norm_num)
theorem B3400805 : Blo 1342990 3400805 := bbase (se 4 (by rfl) ⟨318825, by rfl⟩ : syracuseStep 3400805 = 637651) (by norm_num)
theorem B3023981 : Blo 1342990 3023981 := bbase (se 3 (by rfl) ⟨566996, by rfl⟩ : syracuseStep 3023981 = 1133993) (by norm_num)
theorem B2016365 : Blo 1342990 2016365 := bbase (se 3 (by rfl) ⟨378068, by rfl⟩ : syracuseStep 2016365 = 756137) (by norm_num)
theorem B2016389 : Blo 1342990 2016389 := bbase (se 4 (by rfl) ⟨189036, by rfl⟩ : syracuseStep 2016389 = 378073) (by norm_num)
theorem B6456469 : Blo 1342990 6456469 := bbase (se 6 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 6456469 = 302647) (by norm_num)
theorem B2016413 : Blo 1342990 2016413 := bbase (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) (by norm_num)
theorem B5743781 : Blo 1342990 5743781 := bbase (se 4 (by rfl) ⟨538479, by rfl⟩ : syracuseStep 5743781 = 1076959) (by norm_num)
theorem B3024053 : Blo 1342990 3024053 := bbase (se 5 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 3024053 = 283505) (by norm_num)
theorem B2016437 : Blo 1342990 2016437 := bbase (se 5 (by rfl) ⟨94520, by rfl⟩ : syracuseStep 2016437 = 189041) (by norm_num)
theorem B2016461 : Blo 1342990 2016461 := bbase (se 3 (by rfl) ⟨378086, by rfl⟩ : syracuseStep 2016461 = 756173) (by norm_num)
theorem B6800597 : Blo 1342990 6800597 := bbase (se 7 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 6800597 = 159389) (by norm_num)
theorem B5104853 : Blo 1342990 5104853 := bbase (se 7 (by rfl) ⟨59822, by rfl⟩ : syracuseStep 5104853 = 119645) (by norm_num)
theorem B2016485 : Blo 1342990 2016485 := bbase (se 4 (by rfl) ⟨189045, by rfl⟩ : syracuseStep 2016485 = 378091) (by norm_num)
theorem B1434877 : Blo 1342990 1434877 := bbase (se 3 (by rfl) ⟨269039, by rfl⟩ : syracuseStep 1434877 = 538079) (by norm_num)
theorem B3024125 : Blo 1342990 3024125 := bbase (se 3 (by rfl) ⟨567023, by rfl⟩ : syracuseStep 3024125 = 1134047) (by norm_num)
theorem B2016509 : Blo 1342990 2016509 := bbase (se 3 (by rfl) ⟨378095, by rfl⟩ : syracuseStep 2016509 = 756191) (by norm_num)
theorem B2016533 : Blo 1342990 2016533 := bbase (se 6 (by rfl) ⟨47262, by rfl⟩ : syracuseStep 2016533 = 94525) (by norm_num)
theorem B8733973 : Blo 1342990 8733973 := bbase (se 6 (by rfl) ⟨204702, by rfl⟩ : syracuseStep 8733973 = 409405) (by norm_num)
theorem B2016557 : Blo 1342990 2016557 := bbase (se 3 (by rfl) ⟨378104, by rfl⟩ : syracuseStep 2016557 = 756209) (by norm_num)
theorem B3024197 : Blo 1342990 3024197 := bbase (se 4 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 3024197 = 567037) (by norm_num)
theorem B2016581 : Blo 1342990 2016581 := bbase (se 4 (by rfl) ⟨189054, by rfl⟩ : syracuseStep 2016581 = 378109) (by norm_num)
theorem B2016605 : Blo 1342990 2016605 := bbase (se 3 (by rfl) ⟨378113, by rfl⟩ : syracuseStep 2016605 = 756227) (by norm_num)
theorem B1434997 : Blo 1342990 1434997 := bbase (se 5 (by rfl) ⟨67265, by rfl⟩ : syracuseStep 1434997 = 134531) (by norm_num)
theorem B2016629 : Blo 1342990 2016629 := bbase (se 5 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 2016629 = 189059) (by norm_num)
theorem B3024269 : Blo 1342990 3024269 := bbase (se 3 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 3024269 = 1134101) (by norm_num)
theorem B2016653 : Blo 1342990 2016653 := bbase (se 3 (by rfl) ⟨378122, by rfl⟩ : syracuseStep 2016653 = 756245) (by norm_num)
theorem B2016677 : Blo 1342990 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B3401149 : Blo 1342990 3401149 := bbase (se 3 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 3401149 = 1275431) (by norm_num)
theorem B2016701 : Blo 1342990 2016701 := bbase (se 3 (by rfl) ⟨378131, by rfl⟩ : syracuseStep 2016701 = 756263) (by norm_num)
theorem B1967557 : Blo 1342990 1967557 := bbase (se 4 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 1967557 = 368917) (by norm_num)
theorem B3024341 : Blo 1342990 3024341 := bbase (se 7 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 3024341 = 70883) (by norm_num)
theorem B2016725 : Blo 1342990 2016725 := bbase (se 7 (by rfl) ⟨23633, by rfl⟩ : syracuseStep 2016725 = 47267) (by norm_num)
theorem B2016749 : Blo 1342990 2016749 := bbase (se 3 (by rfl) ⟨378140, by rfl⟩ : syracuseStep 2016749 = 756281) (by norm_num)
theorem B1361405 : Blo 1342990 1361405 := bbase (se 3 (by rfl) ⟨255263, by rfl⟩ : syracuseStep 1361405 = 510527) (by norm_num)
theorem B2016773 : Blo 1342990 2016773 := bbase (se 4 (by rfl) ⟨189072, by rfl⟩ : syracuseStep 2016773 = 378145) (by norm_num)
theorem B3024413 : Blo 1342990 3024413 := bbase (se 3 (by rfl) ⟨567077, by rfl⟩ : syracuseStep 3024413 = 1134155) (by norm_num)
theorem B2016797 : Blo 1342990 2016797 := bbase (se 3 (by rfl) ⟨378149, by rfl⟩ : syracuseStep 2016797 = 756299) (by norm_num)
theorem B5678629 : Blo 1342990 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B3401261 : Blo 1342990 3401261 := bbase (se 3 (by rfl) ⟨637736, by rfl⟩ : syracuseStep 3401261 = 1275473) (by norm_num)
theorem B2016821 : Blo 1342990 2016821 := bbase (se 5 (by rfl) ⟨94538, by rfl⟩ : syracuseStep 2016821 = 189077) (by norm_num)
theorem B2016845 : Blo 1342990 2016845 := bbase (se 3 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 2016845 = 756317) (by norm_num)
theorem B3024485 : Blo 1342990 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B2016869 : Blo 1342990 2016869 := bbase (se 4 (by rfl) ⟨189081, by rfl⟩ : syracuseStep 2016869 = 378163) (by norm_num)
theorem B1435249 : Blo 1342990 1435249 := bbase (se 2 (by rfl) ⟨538218, by rfl⟩ : syracuseStep 1435249 = 1076437) (by norm_num)
theorem B1435253 : Blo 1342990 1435253 := bbase (se 5 (by rfl) ⟨67277, by rfl⟩ : syracuseStep 1435253 = 134555) (by norm_num)
theorem B2016893 : Blo 1342990 2016893 := bbase (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) (by norm_num)
theorem B2016917 : Blo 1342990 2016917 := bbase (se 6 (by rfl) ⟨47271, by rfl⟩ : syracuseStep 2016917 = 94543) (by norm_num)
theorem B3024557 : Blo 1342990 3024557 := bbase (se 3 (by rfl) ⟨567104, by rfl⟩ : syracuseStep 3024557 = 1134209) (by norm_num)
theorem B2016941 : Blo 1342990 2016941 := bbase (se 3 (by rfl) ⟨378176, by rfl⟩ : syracuseStep 2016941 = 756353) (by norm_num)
theorem B2016965 : Blo 1342990 2016965 := bbase (se 4 (by rfl) ⟨189090, by rfl⟩ : syracuseStep 2016965 = 378181) (by norm_num)
theorem B2016989 : Blo 1342990 2016989 := bbase (se 3 (by rfl) ⟨378185, by rfl⟩ : syracuseStep 2016989 = 756371) (by norm_num)
theorem B3401453 : Blo 1342990 3401453 := bbase (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) (by norm_num)
theorem B3024629 : Blo 1342990 3024629 := bbase (se 5 (by rfl) ⟨141779, by rfl⟩ : syracuseStep 3024629 = 283559) (by norm_num)
theorem B2017013 : Blo 1342990 2017013 := bbase (se 5 (by rfl) ⟨94547, by rfl⟩ : syracuseStep 2017013 = 189095) (by norm_num)
theorem B1615621 : Blo 1342990 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B2017037 : Blo 1342990 2017037 := bbase (se 3 (by rfl) ⟨378194, by rfl⟩ : syracuseStep 2017037 = 756389) (by norm_num)
theorem B2017061 : Blo 1342990 2017061 := bbase (se 4 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 2017061 = 378199) (by norm_num)
theorem B2869037 : Blo 1342990 2869037 := bbase (se 3 (by rfl) ⟨537944, by rfl⟩ : syracuseStep 2869037 = 1075889) (by norm_num)
theorem B1615669 : Blo 1342990 1615669 := bbase (se 5 (by rfl) ⟨75734, by rfl⟩ : syracuseStep 1615669 = 151469) (by norm_num)
theorem B3024701 : Blo 1342990 3024701 := bbase (se 3 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 3024701 = 1134263) (by norm_num)
theorem B2017085 : Blo 1342990 2017085 := bbase (se 3 (by rfl) ⟨378203, by rfl⟩ : syracuseStep 2017085 = 756407) (by norm_num)
theorem B2017109 : Blo 1342990 2017109 := bbase (se 9 (by rfl) ⟨5909, by rfl⟩ : syracuseStep 2017109 = 11819) (by norm_num)
theorem B2017133 : Blo 1342990 2017133 := bbase (se 3 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 2017133 = 756425) (by norm_num)
theorem B3024773 : Blo 1342990 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B2017157 : Blo 1342990 2017157 := bbase (se 4 (by rfl) ⟨189108, by rfl⟩ : syracuseStep 2017157 = 378217) (by norm_num)
theorem B2017181 : Blo 1342990 2017181 := bbase (se 3 (by rfl) ⟨378221, by rfl⟩ : syracuseStep 2017181 = 756443) (by norm_num)
theorem B2869157 : Blo 1342990 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B2017205 : Blo 1342990 2017205 := bbase (se 5 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 2017205 = 189113) (by norm_num)
theorem B2549693 : Blo 1342990 2549693 := bbase (se 3 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 2549693 = 956135) (by norm_num)
theorem B1574845 : Blo 1342990 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B3065789 : Blo 1342990 3065789 := bbase (se 3 (by rfl) ⟨574835, by rfl⟩ : syracuseStep 3065789 = 1149671) (by norm_num)
theorem B3024845 : Blo 1342990 3024845 := bbase (se 3 (by rfl) ⟨567158, by rfl⟩ : syracuseStep 3024845 = 1134317) (by norm_num)
theorem B2017229 : Blo 1342990 2017229 := bbase (se 3 (by rfl) ⟨378230, by rfl⟩ : syracuseStep 2017229 = 756461) (by norm_num)
theorem B21792725 : Blo 1342990 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B2017253 : Blo 1342990 2017253 := bbase (se 4 (by rfl) ⟨189117, by rfl⟩ : syracuseStep 2017253 = 378235) (by norm_num)
theorem B2017277 : Blo 1342990 2017277 := bbase (se 3 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 2017277 = 756479) (by norm_num)
theorem B13273109 : Blo 1342990 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B3024917 : Blo 1342990 3024917 := bbase (se 6 (by rfl) ⟨70896, by rfl⟩ : syracuseStep 3024917 = 141793) (by norm_num)
theorem B2017301 : Blo 1342990 2017301 := bbase (se 6 (by rfl) ⟨47280, by rfl⟩ : syracuseStep 2017301 = 94561) (by norm_num)
theorem B2017325 : Blo 1342990 2017325 := bbase (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) (by norm_num)
theorem B3401797 : Blo 1342990 3401797 := bbase (se 4 (by rfl) ⟨318918, by rfl⟩ : syracuseStep 3401797 = 637837) (by norm_num)
theorem B2017349 : Blo 1342990 2017349 := bbase (se 4 (by rfl) ⟨189126, by rfl⟩ : syracuseStep 2017349 = 378253) (by norm_num)
theorem B3024989 : Blo 1342990 3024989 := bbase (se 3 (by rfl) ⟨567185, by rfl⟩ : syracuseStep 3024989 = 1134371) (by norm_num)
theorem B2017373 : Blo 1342990 2017373 := bbase (se 3 (by rfl) ⟨378257, by rfl⟩ : syracuseStep 2017373 = 756515) (by norm_num)
theorem B2017397 : Blo 1342990 2017397 := bbase (se 5 (by rfl) ⟨94565, by rfl⟩ : syracuseStep 2017397 = 189131) (by norm_num)
theorem B2017421 : Blo 1342990 2017421 := bbase (se 3 (by rfl) ⟨378266, by rfl⟩ : syracuseStep 2017421 = 756533) (by norm_num)
theorem B3025061 : Blo 1342990 3025061 := bbase (se 4 (by rfl) ⟨283599, by rfl⟩ : syracuseStep 3025061 = 567199) (by norm_num)
theorem B2017445 : Blo 1342990 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B1435817 : Blo 1342990 1435817 := bbase (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) (by norm_num)
theorem B3401909 : Blo 1342990 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B2017469 : Blo 1342990 2017469 := bbase (se 3 (by rfl) ⟨378275, by rfl⟩ : syracuseStep 2017469 = 756551) (by norm_num)
theorem B2549981 : Blo 1342990 2549981 := bbase (se 3 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 2549981 = 956243) (by norm_num)
theorem B3025133 : Blo 1342990 3025133 := bbase (se 3 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 3025133 = 1134425) (by norm_num)
theorem B3025205 : Blo 1342990 3025205 := bbase (se 5 (by rfl) ⟨141806, by rfl⟩ : syracuseStep 3025205 = 283613) (by norm_num)
theorem B1436005 : Blo 1342990 1436005 := bbase (se 4 (by rfl) ⟨134625, by rfl⟩ : syracuseStep 1436005 = 269251) (by norm_num)
theorem B4532597 : Blo 1342990 4532597 := bbase (se 5 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 4532597 = 424931) (by norm_num)
theorem B2550133 : Blo 1342990 2550133 := bbase (se 5 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 2550133 = 239075) (by norm_num)
theorem B3402101 : Blo 1342990 3402101 := bbase (se 5 (by rfl) ⟨159473, by rfl⟩ : syracuseStep 3402101 = 318947) (by norm_num)
theorem B5106037 : Blo 1342990 5106037 := bbase (se 5 (by rfl) ⟨239345, by rfl⟩ : syracuseStep 5106037 = 478691) (by norm_num)
theorem B3025277 : Blo 1342990 3025277 := bbase (se 3 (by rfl) ⟨567239, by rfl⟩ : syracuseStep 3025277 = 1134479) (by norm_num)
theorem B1362305 : Blo 1342990 1362305 := bbase (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) (by norm_num)
theorem B3025349 : Blo 1342990 3025349 := bbase (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) (by norm_num)
theorem B3230165 : Blo 1342990 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B6801893 : Blo 1342990 6801893 := bbase (se 4 (by rfl) ⟨637677, by rfl⟩ : syracuseStep 6801893 = 1275355) (by norm_num)
theorem B3025421 : Blo 1342990 3025421 := bbase (se 3 (by rfl) ⟨567266, by rfl⟩ : syracuseStep 3025421 = 1134533) (by norm_num)
theorem B2869789 : Blo 1342990 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B3025493 : Blo 1342990 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B4303493 : Blo 1342990 4303493 := bbase (se 4 (by rfl) ⟨403452, by rfl⟩ : syracuseStep 4303493 = 806905) (by norm_num)
theorem B3148445 : Blo 1342990 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B3025565 : Blo 1342990 3025565 := bbase (se 3 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 3025565 = 1134587) (by norm_num)
theorem B2042533 : Blo 1342990 2042533 := bbase (se 4 (by rfl) ⟨191487, by rfl⟩ : syracuseStep 2042533 = 382975) (by norm_num)
theorem B2550437 : Blo 1342990 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B5106341 : Blo 1342990 5106341 := bbase (se 4 (by rfl) ⟨478719, by rfl⟩ : syracuseStep 5106341 = 957439) (by norm_num)
theorem B1362625 : Blo 1342990 1362625 := bbase (se 2 (by rfl) ⟨510984, by rfl⟩ : syracuseStep 1362625 = 1021969) (by norm_num)
theorem B3402445 : Blo 1342990 3402445 := bbase (se 3 (by rfl) ⟨637958, by rfl⟩ : syracuseStep 3402445 = 1275917) (by norm_num)
theorem B3025637 : Blo 1342990 3025637 := bbase (se 4 (by rfl) ⟨283653, by rfl⟩ : syracuseStep 3025637 = 567307) (by norm_num)
theorem B1723141 : Blo 1342990 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B4533029 : Blo 1342990 4533029 := bbase (se 4 (by rfl) ⟨424971, by rfl⟩ : syracuseStep 4533029 = 849943) (by norm_num)
theorem B3025709 : Blo 1342990 3025709 := bbase (se 3 (by rfl) ⟨567320, by rfl⟩ : syracuseStep 3025709 = 1134641) (by norm_num)
theorem B3402557 : Blo 1342990 3402557 := bbase (se 3 (by rfl) ⟨637979, by rfl⟩ : syracuseStep 3402557 = 1275959) (by norm_num)
theorem B3025781 : Blo 1342990 3025781 := bbase (se 5 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 3025781 = 283667) (by norm_num)
theorem B6548357 : Blo 1342990 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B14740373 : Blo 1342990 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B3025853 : Blo 1342990 3025853 := bbase (se 3 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 3025853 = 1134695) (by norm_num)
theorem B3402749 : Blo 1342990 3402749 := bbase (se 3 (by rfl) ⟨638015, by rfl⟩ : syracuseStep 3402749 = 1276031) (by norm_num)
theorem B3025925 : Blo 1342990 3025925 := bbase (se 4 (by rfl) ⟨283680, by rfl⟩ : syracuseStep 3025925 = 567361) (by norm_num)
theorem B5737493 : Blo 1342990 5737493 := bbase (se 6 (by rfl) ⟨134472, by rfl⟩ : syracuseStep 5737493 = 268945) (by norm_num)
theorem B12266549 : Blo 1342990 12266549 := bbase (se 5 (by rfl) ⟨574994, by rfl⟩ : syracuseStep 12266549 = 1149989) (by norm_num)
theorem B3632197 : Blo 1342990 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B3025997 : Blo 1342990 3025997 := bbase (se 3 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 3025997 = 1134749) (by norm_num)
theorem B3026069 : Blo 1342990 3026069 := bbase (se 6 (by rfl) ⟨70923, by rfl⟩ : syracuseStep 3026069 = 141847) (by norm_num)
theorem B4533461 : Blo 1342990 4533461 := bbase (se 7 (by rfl) ⟨53126, by rfl⟩ : syracuseStep 4533461 = 106253) (by norm_num)
theorem B3026141 : Blo 1342990 3026141 := bbase (se 3 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 3026141 = 1134803) (by norm_num)
theorem B9194741 : Blo 1342990 9194741 := bbase (se 5 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 9194741 = 862007) (by norm_num)
theorem B1723685 : Blo 1342990 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B3026213 : Blo 1342990 3026213 := bbase (se 4 (by rfl) ⟨283707, by rfl⟩ : syracuseStep 3026213 = 567415) (by norm_num)
theorem B113397077 : Blo 1342990 113397077 := bbase (se 11 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 113397077 = 166109) (by norm_num)
theorem B3403093 : Blo 1342990 3403093 := bbase (se 11 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 3403093 = 4985) (by norm_num)
theorem B3272053 : Blo 1342990 3272053 := bbase (se 5 (by rfl) ⟨153377, by rfl⟩ : syracuseStep 3272053 = 306755) (by norm_num)
theorem B2551189 : Blo 1342990 2551189 := bbase (se 6 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 2551189 = 119587) (by norm_num)
theorem B2870677 : Blo 1342990 2870677 := bbase (se 6 (by rfl) ⟨67281, by rfl⟩ : syracuseStep 2870677 = 134563) (by norm_num)
theorem B3403205 : Blo 1342990 3403205 := bbase (se 4 (by rfl) ⟨319050, by rfl⟩ : syracuseStep 3403205 = 638101) (by norm_num)
theorem B1510897 : Blo 1342990 1510897 := bbase (se 2 (by rfl) ⟨566586, by rfl⟩ : syracuseStep 1510897 = 1133173) (by norm_num)
theorem B2870797 : Blo 1342990 2870797 := bbase (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) (by norm_num)
theorem B1510933 : Blo 1342990 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B2551333 : Blo 1342990 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B3829301 : Blo 1342990 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B1510969 : Blo 1342990 1510969 := bbase (se 2 (by rfl) ⟨566613, by rfl⟩ : syracuseStep 1510969 = 1133227) (by norm_num)
theorem B3632725 : Blo 1342990 3632725 := bbase (se 8 (by rfl) ⟨21285, by rfl⟩ : syracuseStep 3632725 = 42571) (by norm_num)
theorem B1511005 : Blo 1342990 1511005 := bbase (se 3 (by rfl) ⟨283313, by rfl⟩ : syracuseStep 1511005 = 566627) (by norm_num)
theorem B1511041 : Blo 1342990 1511041 := bbase (se 2 (by rfl) ⟨566640, by rfl⟩ : syracuseStep 1511041 = 1133281) (by norm_num)
theorem B4533893 : Blo 1342990 4533893 := bbase (se 4 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 4533893 = 850105) (by norm_num)
theorem B3403397 : Blo 1342990 3403397 := bbase (se 4 (by rfl) ⟨319068, by rfl⟩ : syracuseStep 3403397 = 638137) (by norm_num)
theorem B1511077 : Blo 1342990 1511077 := bbase (se 4 (by rfl) ⟨141663, by rfl⟩ : syracuseStep 1511077 = 283327) (by norm_num)
theorem B7655093 : Blo 1342990 7655093 := bbase (se 5 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 7655093 = 717665) (by norm_num)
theorem B2551493 : Blo 1342990 2551493 := bbase (se 4 (by rfl) ⟨239202, by rfl⟩ : syracuseStep 2551493 = 478405) (by norm_num)
theorem B1511113 : Blo 1342990 1511113 := bbase (se 2 (by rfl) ⟨566667, by rfl⟩ : syracuseStep 1511113 = 1133335) (by norm_num)
theorem B1511149 : Blo 1342990 1511149 := bbase (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) (by norm_num)
theorem B6803189 : Blo 1342990 6803189 := bbase (se 5 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 6803189 = 637799) (by norm_num)
theorem B2871053 : Blo 1342990 2871053 := bbase (se 3 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 2871053 = 1076645) (by norm_num)
theorem B1511185 : Blo 1342990 1511185 := bbase (se 2 (by rfl) ⟨566694, by rfl⟩ : syracuseStep 1511185 = 1133389) (by norm_num)
theorem B1511221 : Blo 1342990 1511221 := bbase (se 5 (by rfl) ⟨70838, by rfl⟩ : syracuseStep 1511221 = 141677) (by norm_num)
theorem B4845365 : Blo 1342990 4845365 := bbase (se 5 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 4845365 = 454253) (by norm_num)
theorem B2551637 : Blo 1342990 2551637 := bbase (se 9 (by rfl) ⟨7475, by rfl⟩ : syracuseStep 2551637 = 14951) (by norm_num)
theorem B5820245 : Blo 1342990 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1511257 : Blo 1342990 1511257 := bbase (se 2 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 1511257 = 1133443) (by norm_num)
theorem B2043749 : Blo 1342990 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B3231589 : Blo 1342990 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B2723701 : Blo 1342990 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1511293 : Blo 1342990 1511293 := bbase (se 3 (by rfl) ⟨283367, by rfl⟩ : syracuseStep 1511293 = 566735) (by norm_num)
theorem B3633029 : Blo 1342990 3633029 := bbase (se 4 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 3633029 = 681193) (by norm_num)
theorem B1511329 : Blo 1342990 1511329 := bbase (se 2 (by rfl) ⟨566748, by rfl⟩ : syracuseStep 1511329 = 1133497) (by norm_num)
theorem B1511365 : Blo 1342990 1511365 := bbase (se 4 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 1511365 = 283381) (by norm_num)
theorem B4599749 : Blo 1342990 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B1699805 : Blo 1342990 1699805 := bbase (se 3 (by rfl) ⟨318713, by rfl⟩ : syracuseStep 1699805 = 637427) (by norm_num)
theorem B3403741 : Blo 1342990 3403741 := bbase (se 3 (by rfl) ⟨638201, by rfl⟩ : syracuseStep 3403741 = 1276403) (by norm_num)
theorem B1511401 : Blo 1342990 1511401 := bbase (se 2 (by rfl) ⟨566775, by rfl⟩ : syracuseStep 1511401 = 1133551) (by norm_num)
theorem B1511437 : Blo 1342990 1511437 := bbase (se 3 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 1511437 = 566789) (by norm_num)
theorem B1699861 : Blo 1342990 1699861 := bbase (se 6 (by rfl) ⟨39840, by rfl⟩ : syracuseStep 1699861 = 79681) (by norm_num)
theorem B1511473 : Blo 1342990 1511473 := bbase (se 2 (by rfl) ⟨566802, by rfl⟩ : syracuseStep 1511473 = 1133605) (by norm_num)
theorem B4534325 : Blo 1342990 4534325 := bbase (se 5 (by rfl) ⟨212546, by rfl⟩ : syracuseStep 4534325 = 425093) (by norm_num)
theorem B3403853 : Blo 1342990 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B1511509 : Blo 1342990 1511509 := bbase (se 8 (by rfl) ⟨8856, by rfl⟩ : syracuseStep 1511509 = 17713) (by norm_num)
theorem B4845653 : Blo 1342990 4845653 := bbase (se 8 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 4845653 = 56785) (by norm_num)
theorem B2420837 : Blo 1342990 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B1699957 : Blo 1342990 1699957 := bbase (se 5 (by rfl) ⟨79685, by rfl⟩ : syracuseStep 1699957 = 159371) (by norm_num)
theorem B2551925 : Blo 1342990 2551925 := bbase (se 5 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 2551925 = 239243) (by norm_num)
theorem B1511545 : Blo 1342990 1511545 := bbase (se 2 (by rfl) ⟨566829, by rfl⟩ : syracuseStep 1511545 = 1133659) (by norm_num)
theorem B1724537 : Blo 1342990 1724537 := bbase (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) (by norm_num)
theorem B2044037 : Blo 1342990 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B1511581 : Blo 1342990 1511581 := bbase (se 3 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 1511581 = 566843) (by norm_num)
theorem B1511617 : Blo 1342990 1511617 := bbase (se 2 (by rfl) ⟨566856, by rfl⟩ : syracuseStep 1511617 = 1133713) (by norm_num)
theorem B1511653 : Blo 1342990 1511653 := bbase (se 4 (by rfl) ⟨141717, by rfl⟩ : syracuseStep 1511653 = 283435) (by norm_num)
theorem B2584829 : Blo 1342990 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B1511689 : Blo 1342990 1511689 := bbase (se 2 (by rfl) ⟨566883, by rfl⟩ : syracuseStep 1511689 = 1133767) (by norm_num)
theorem B2552077 : Blo 1342990 2552077 := bbase (se 3 (by rfl) ⟨478514, by rfl⟩ : syracuseStep 2552077 = 957029) (by norm_num)
theorem B3404045 : Blo 1342990 3404045 := bbase (se 3 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 3404045 = 1276517) (by norm_num)
theorem B1700129 : Blo 1342990 1700129 := bbase (se 2 (by rfl) ⟨637548, by rfl⟩ : syracuseStep 1700129 = 1275097) (by norm_num)
theorem B1511725 : Blo 1342990 1511725 := bbase (se 3 (by rfl) ⟨283448, by rfl⟩ : syracuseStep 1511725 = 566897) (by norm_num)
theorem B1511761 : Blo 1342990 1511761 := bbase (se 2 (by rfl) ⟨566910, by rfl⟩ : syracuseStep 1511761 = 1133821) (by norm_num)
theorem B1700185 : Blo 1342990 1700185 := bbase (se 2 (by rfl) ⟨637569, by rfl⟩ : syracuseStep 1700185 = 1275139) (by norm_num)
theorem B1511797 : Blo 1342990 1511797 := bbase (se 5 (by rfl) ⟨70865, by rfl⟩ : syracuseStep 1511797 = 141731) (by norm_num)
theorem B1511833 : Blo 1342990 1511833 := bbase (se 2 (by rfl) ⟨566937, by rfl⟩ : syracuseStep 1511833 = 1133875) (by norm_num)
theorem B12915125 : Blo 1342990 12915125 := bbase (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) (by norm_num)
theorem B1700281 : Blo 1342990 1700281 := bbase (se 2 (by rfl) ⟨637605, by rfl⟩ : syracuseStep 1700281 = 1275211) (by norm_num)
theorem B1511869 : Blo 1342990 1511869 := bbase (se 3 (by rfl) ⟨283475, by rfl⟩ : syracuseStep 1511869 = 566951) (by norm_num)
theorem B4305349 : Blo 1342990 4305349 := bbase (se 4 (by rfl) ⟨403626, by rfl⟩ : syracuseStep 4305349 = 807253) (by norm_num)
theorem B1511905 : Blo 1342990 1511905 := bbase (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) (by norm_num)
theorem B4534757 : Blo 1342990 4534757 := bbase (se 4 (by rfl) ⟨425133, by rfl⟩ : syracuseStep 4534757 = 850267) (by norm_num)
theorem B1511941 : Blo 1342990 1511941 := bbase (se 4 (by rfl) ⟨141744, by rfl⟩ : syracuseStep 1511941 = 283489) (by norm_num)
theorem B4846085 : Blo 1342990 4846085 := bbase (se 4 (by rfl) ⟨454320, by rfl⟩ : syracuseStep 4846085 = 908641) (by norm_num)
theorem B1511977 : Blo 1342990 1511977 := bbase (se 2 (by rfl) ⟨566991, by rfl⟩ : syracuseStep 1511977 = 1133983) (by norm_num)
theorem B2552381 : Blo 1342990 2552381 := bbase (se 3 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 2552381 = 957143) (by norm_num)
theorem B1512013 : Blo 1342990 1512013 := bbase (se 3 (by rfl) ⟨283502, by rfl⟩ : syracuseStep 1512013 = 567005) (by norm_num)
theorem B1700453 : Blo 1342990 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B3404389 : Blo 1342990 3404389 := bbase (se 4 (by rfl) ⟨319161, by rfl⟩ : syracuseStep 3404389 = 638323) (by norm_num)
theorem B1512049 : Blo 1342990 1512049 := bbase (se 2 (by rfl) ⟨567018, by rfl⟩ : syracuseStep 1512049 = 1134037) (by norm_num)
theorem B2871941 : Blo 1342990 2871941 := bbase (se 4 (by rfl) ⟨269244, by rfl⟩ : syracuseStep 2871941 = 538489) (by norm_num)
theorem B1512085 : Blo 1342990 1512085 := bbase (se 6 (by rfl) ⟨35439, by rfl⟩ : syracuseStep 1512085 = 70879) (by norm_num)
theorem B1700509 : Blo 1342990 1700509 := bbase (se 3 (by rfl) ⟨318845, by rfl⟩ : syracuseStep 1700509 = 637691) (by norm_num)
theorem B1512121 : Blo 1342990 1512121 := bbase (se 2 (by rfl) ⟨567045, by rfl⟩ : syracuseStep 1512121 = 1134091) (by norm_num)
theorem B1913557 : Blo 1342990 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B5821141 : Blo 1342990 5821141 := bbase (se 7 (by rfl) ⟨68216, by rfl⟩ : syracuseStep 5821141 = 136433) (by norm_num)
theorem B3404501 : Blo 1342990 3404501 := bbase (se 7 (by rfl) ⟨39896, by rfl⟩ : syracuseStep 3404501 = 79793) (by norm_num)
theorem B1512157 : Blo 1342990 1512157 := bbase (se 3 (by rfl) ⟨283529, by rfl⟩ : syracuseStep 1512157 = 567059) (by norm_num)
theorem B1815277 : Blo 1342990 1815277 := bbase (se 3 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 1815277 = 680729) (by norm_num)
theorem B1700605 : Blo 1342990 1700605 := bbase (se 3 (by rfl) ⟨318863, by rfl⟩ : syracuseStep 1700605 = 637727) (by norm_num)
theorem B1512193 : Blo 1342990 1512193 := bbase (se 2 (by rfl) ⟨567072, by rfl⟩ : syracuseStep 1512193 = 1134145) (by norm_num)
theorem B1725193 : Blo 1342990 1725193 := bbase (se 2 (by rfl) ⟨646947, by rfl⟩ : syracuseStep 1725193 = 1293895) (by norm_num)
theorem B15307541 : Blo 1342990 15307541 := bbase (se 6 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 15307541 = 717541) (by norm_num)
theorem B1512229 : Blo 1342990 1512229 := bbase (se 4 (by rfl) ⟨141771, by rfl⟩ : syracuseStep 1512229 = 283543) (by norm_num)
theorem B1512265 : Blo 1342990 1512265 := bbase (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) (by norm_num)
theorem B1512301 : Blo 1342990 1512301 := bbase (se 3 (by rfl) ⟨283556, by rfl⟩ : syracuseStep 1512301 = 567113) (by norm_num)
theorem B2872181 : Blo 1342990 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B1512337 : Blo 1342990 1512337 := bbase (se 2 (by rfl) ⟨567126, by rfl⟩ : syracuseStep 1512337 = 1134253) (by norm_num)
theorem B4535189 : Blo 1342990 4535189 := bbase (se 6 (by rfl) ⟨106293, by rfl⟩ : syracuseStep 4535189 = 212587) (by norm_num)
theorem B1700777 : Blo 1342990 1700777 := bbase (se 2 (by rfl) ⟨637791, by rfl⟩ : syracuseStep 1700777 = 1275583) (by norm_num)
theorem B1512373 : Blo 1342990 1512373 := bbase (se 5 (by rfl) ⟨70892, by rfl⟩ : syracuseStep 1512373 = 141785) (by norm_num)
theorem B5452757 : Blo 1342990 5452757 := bbase (se 7 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 5452757 = 127799) (by norm_num)
theorem B1512409 : Blo 1342990 1512409 := bbase (se 2 (by rfl) ⟨567153, by rfl⟩ : syracuseStep 1512409 = 1134307) (by norm_num)
theorem B1700833 : Blo 1342990 1700833 := bbase (se 2 (by rfl) ⟨637812, by rfl⟩ : syracuseStep 1700833 = 1275625) (by norm_num)
theorem B1512445 : Blo 1342990 1512445 := bbase (se 3 (by rfl) ⟨283583, by rfl⟩ : syracuseStep 1512445 = 567167) (by norm_num)
theorem B6804485 : Blo 1342990 6804485 := bbase (se 4 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 6804485 = 1275841) (by norm_num)
theorem B22959125 : Blo 1342990 22959125 := bbase (se 6 (by rfl) ⟨538104, by rfl⟩ : syracuseStep 22959125 = 1076209) (by norm_num)
theorem B1512481 : Blo 1342990 1512481 := bbase (se 2 (by rfl) ⟨567180, by rfl⟩ : syracuseStep 1512481 = 1134361) (by norm_num)
theorem B2298917 : Blo 1342990 2298917 := bbase (se 4 (by rfl) ⟨215523, by rfl⟩ : syracuseStep 2298917 = 431047) (by norm_num)
theorem B1700929 : Blo 1342990 1700929 := bbase (se 2 (by rfl) ⟨637848, by rfl⟩ : syracuseStep 1700929 = 1275697) (by norm_num)
theorem B1512517 : Blo 1342990 1512517 := bbase (se 4 (by rfl) ⟨141798, by rfl⟩ : syracuseStep 1512517 = 283597) (by norm_num)
theorem B1512553 : Blo 1342990 1512553 := bbase (se 2 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 1512553 = 1134415) (by norm_num)
theorem B5100677 : Blo 1342990 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B1512589 : Blo 1342990 1512589 := bbase (se 3 (by rfl) ⟨283610, by rfl⟩ : syracuseStep 1512589 = 567221) (by norm_num)
theorem B1512625 : Blo 1342990 1512625 := bbase (se 2 (by rfl) ⟨567234, by rfl⟩ : syracuseStep 1512625 = 1134469) (by norm_num)
theorem B1512661 : Blo 1342990 1512661 := bbase (se 7 (by rfl) ⟨17726, by rfl⟩ : syracuseStep 1512661 = 35453) (by norm_num)
theorem B1701101 : Blo 1342990 1701101 := bbase (se 3 (by rfl) ⟨318956, by rfl⟩ : syracuseStep 1701101 = 637913) (by norm_num)
theorem B1512697 : Blo 1342990 1512697 := bbase (se 2 (by rfl) ⟨567261, by rfl⟩ : syracuseStep 1512697 = 1134523) (by norm_num)
theorem B2266373 : Blo 1342990 2266373 := bbase (se 4 (by rfl) ⟨212472, by rfl⟩ : syracuseStep 2266373 = 424945) (by norm_num)
theorem B2151701 : Blo 1342990 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B1512733 : Blo 1342990 1512733 := bbase (se 3 (by rfl) ⟨283637, by rfl⟩ : syracuseStep 1512733 = 567275) (by norm_num)
theorem B1701157 : Blo 1342990 1701157 := bbase (se 4 (by rfl) ⟨159483, by rfl⟩ : syracuseStep 1701157 = 318967) (by norm_num)
theorem B1914149 : Blo 1342990 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B2553133 : Blo 1342990 2553133 := bbase (se 3 (by rfl) ⟨478712, by rfl⟩ : syracuseStep 2553133 = 957425) (by norm_num)
theorem B1512769 : Blo 1342990 1512769 := bbase (se 2 (by rfl) ⟨567288, by rfl⟩ : syracuseStep 1512769 = 1134577) (by norm_num)
theorem B4535621 : Blo 1342990 4535621 := bbase (se 4 (by rfl) ⟨425214, by rfl⟩ : syracuseStep 4535621 = 850429) (by norm_num)
theorem B3446117 : Blo 1342990 3446117 := bbase (se 4 (by rfl) ⟨323073, by rfl⟩ : syracuseStep 3446117 = 646147) (by norm_num)
theorem B1512805 : Blo 1342990 1512805 := bbase (se 4 (by rfl) ⟨141825, by rfl⟩ : syracuseStep 1512805 = 283651) (by norm_num)
theorem B1914229 : Blo 1342990 1914229 := bbase (se 5 (by rfl) ⟨89729, by rfl⟩ : syracuseStep 1914229 = 179459) (by norm_num)
theorem B2266501 : Blo 1342990 2266501 := bbase (se 4 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 2266501 = 424969) (by norm_num)
theorem B1701253 : Blo 1342990 1701253 := bbase (se 4 (by rfl) ⟨159492, by rfl⟩ : syracuseStep 1701253 = 318985) (by norm_num)
theorem B1512841 : Blo 1342990 1512841 := bbase (se 2 (by rfl) ⟨567315, by rfl⟩ : syracuseStep 1512841 = 1134631) (by norm_num)
theorem B5100965 : Blo 1342990 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B1512877 : Blo 1342990 1512877 := bbase (se 3 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 1512877 = 567329) (by norm_num)
theorem B2553277 : Blo 1342990 2553277 := bbase (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) (by norm_num)
theorem B1512913 : Blo 1342990 1512913 := bbase (se 2 (by rfl) ⟨567342, by rfl⟩ : syracuseStep 1512913 = 1134685) (by norm_num)
theorem B2266589 : Blo 1342990 2266589 := bbase (se 3 (by rfl) ⟨424985, by rfl⟩ : syracuseStep 2266589 = 849971) (by norm_num)
theorem B1914349 : Blo 1342990 1914349 := bbase (se 3 (by rfl) ⟨358940, by rfl⟩ : syracuseStep 1914349 = 717881) (by norm_num)
theorem B8615413 : Blo 1342990 8615413 := bbase (se 5 (by rfl) ⟨403847, by rfl⟩ : syracuseStep 8615413 = 807695) (by norm_num)
theorem B1512949 : Blo 1342990 1512949 := bbase (se 5 (by rfl) ⟨70919, by rfl⟩ : syracuseStep 1512949 = 141839) (by norm_num)
theorem B1512985 : Blo 1342990 1512985 := bbase (se 2 (by rfl) ⟨567369, by rfl⟩ : syracuseStep 1512985 = 1134739) (by norm_num)
theorem B1701425 : Blo 1342990 1701425 := bbase (se 2 (by rfl) ⟨638034, by rfl⟩ : syracuseStep 1701425 = 1276069) (by norm_num)
theorem B1513021 : Blo 1342990 1513021 := bbase (se 3 (by rfl) ⟨283691, by rfl⟩ : syracuseStep 1513021 = 567383) (by norm_num)
theorem B1914445 : Blo 1342990 1914445 := bbase (se 3 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 1914445 = 717917) (by norm_num)
theorem B2266717 : Blo 1342990 2266717 := bbase (se 3 (by rfl) ⟨425009, by rfl⟩ : syracuseStep 2266717 = 850019) (by norm_num)
theorem B1513057 : Blo 1342990 1513057 := bbase (se 2 (by rfl) ⟨567396, by rfl⟩ : syracuseStep 1513057 = 1134793) (by norm_num)
theorem B1701481 : Blo 1342990 1701481 := bbase (se 2 (by rfl) ⟨638055, by rfl⟩ : syracuseStep 1701481 = 1276111) (by norm_num)
theorem B3446405 : Blo 1342990 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B1513093 : Blo 1342990 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B7263893 : Blo 1342990 7263893 := bbase (se 6 (by rfl) ⟨170247, by rfl⟩ : syracuseStep 7263893 = 340495) (by norm_num)
theorem B2266805 : Blo 1342990 2266805 := bbase (se 5 (by rfl) ⟨106256, by rfl⟩ : syracuseStep 2266805 = 212513) (by norm_num)
theorem B1701577 : Blo 1342990 1701577 := bbase (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) (by norm_num)
theorem B4536053 : Blo 1342990 4536053 := bbase (se 5 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 4536053 = 425255) (by norm_num)
theorem B2152213 : Blo 1342990 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B4306709 : Blo 1342990 4306709 := bbase (se 6 (by rfl) ⟨100938, by rfl⟩ : syracuseStep 4306709 = 201877) (by norm_num)
theorem B5601061 : Blo 1342990 5601061 := bbase (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) (by norm_num)
theorem B2266933 : Blo 1342990 2266933 := bbase (se 5 (by rfl) ⟨106262, by rfl⟩ : syracuseStep 2266933 = 212525) (by norm_num)
theorem B1701749 : Blo 1342990 1701749 := bbase (se 5 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 1701749 = 159539) (by norm_num)
theorem B2267021 : Blo 1342990 2267021 := bbase (se 3 (by rfl) ⟨425066, by rfl⟩ : syracuseStep 2267021 = 850133) (by norm_num)
theorem B1701805 : Blo 1342990 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B2267149 : Blo 1342990 2267149 := bbase (se 3 (by rfl) ⟨425090, by rfl⟩ : syracuseStep 2267149 = 850181) (by norm_num)
theorem B1701901 : Blo 1342990 1701901 := bbase (se 3 (by rfl) ⟨319106, by rfl⟩ : syracuseStep 1701901 = 638213) (by norm_num)
theorem B1914941 : Blo 1342990 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B1865797 : Blo 1342990 1865797 := bbase (se 4 (by rfl) ⟨174918, by rfl⟩ : syracuseStep 1865797 = 349837) (by norm_num)
theorem B3881029 : Blo 1342990 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B1636429 : Blo 1342990 1636429 := bbase (se 3 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 1636429 = 613661) (by norm_num)
theorem B2267237 : Blo 1342990 2267237 := bbase (se 4 (by rfl) ⟨212553, by rfl⟩ : syracuseStep 2267237 = 425107) (by norm_num)
theorem B24508565 : Blo 1342990 24508565 := bbase (se 6 (by rfl) ⟨574419, by rfl⟩ : syracuseStep 24508565 = 1148839) (by norm_num)
theorem B4536485 : Blo 1342990 4536485 := bbase (se 4 (by rfl) ⟨425295, by rfl⟩ : syracuseStep 4536485 = 850591) (by norm_num)
theorem B1702073 : Blo 1342990 1702073 := bbase (se 2 (by rfl) ⟨638277, by rfl⟩ : syracuseStep 1702073 = 1276555) (by norm_num)
theorem B5445845 : Blo 1342990 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B2152669 : Blo 1342990 2152669 := bbase (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) (by norm_num)
theorem B2267365 : Blo 1342990 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B1702129 : Blo 1342990 1702129 := bbase (se 2 (by rfl) ⟨638298, by rfl⟩ : syracuseStep 1702129 = 1276597) (by norm_num)
theorem B5519621 : Blo 1342990 5519621 := bbase (se 4 (by rfl) ⟨517464, by rfl⟩ : syracuseStep 5519621 = 1034929) (by norm_num)
theorem B6805781 : Blo 1342990 6805781 := bbase (se 6 (by rfl) ⟨159510, by rfl⟩ : syracuseStep 6805781 = 319021) (by norm_num)
theorem B24254741 : Blo 1342990 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B2267453 : Blo 1342990 2267453 := bbase (se 3 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 2267453 = 850295) (by norm_num)
theorem B1702225 : Blo 1342990 1702225 := bbase (se 2 (by rfl) ⟨638334, by rfl⟩ : syracuseStep 1702225 = 1276669) (by norm_num)
theorem B3275117 : Blo 1342990 3275117 := bbase (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) (by norm_num)
theorem B14522773 : Blo 1342990 14522773 := bbase (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) (by norm_num)
theorem B2267581 : Blo 1342990 2267581 := bbase (se 3 (by rfl) ⟨425171, by rfl⟩ : syracuseStep 2267581 = 850343) (by norm_num)
theorem B6453701 : Blo 1342990 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B3447269 : Blo 1342990 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B2267669 : Blo 1342990 2267669 := bbase (se 6 (by rfl) ⟨53148, by rfl⟩ : syracuseStep 2267669 = 106297) (by norm_num)
theorem B5102149 : Blo 1342990 5102149 := bbase (se 4 (by rfl) ⟨478326, by rfl⟩ : syracuseStep 5102149 = 956653) (by norm_num)
theorem B4536917 : Blo 1342990 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B2267797 : Blo 1342990 2267797 := bbase (se 6 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 2267797 = 106303) (by norm_num)
theorem B27605717 : Blo 1342990 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B2267885 : Blo 1342990 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B6216533 : Blo 1342990 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B2268013 : Blo 1342990 2268013 := bbase (se 3 (by rfl) ⟨425252, by rfl⟩ : syracuseStep 2268013 = 850505) (by norm_num)
theorem B5102453 : Blo 1342990 5102453 := bbase (se 5 (by rfl) ⟨239177, by rfl⟩ : syracuseStep 5102453 = 478355) (by norm_num)
theorem B2153341 : Blo 1342990 2153341 := bbase (se 3 (by rfl) ⟨403751, by rfl⟩ : syracuseStep 2153341 = 807503) (by norm_num)
theorem B3021749 : Blo 1342990 3021749 := bbase (se 5 (by rfl) ⟨141644, by rfl⟩ : syracuseStep 3021749 = 283289) (by norm_num)
theorem B2268101 : Blo 1342990 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B3824597 : Blo 1342990 3824597 := bbase (se 7 (by rfl) ⟨44819, by rfl⟩ : syracuseStep 3824597 = 89639) (by norm_num)
theorem B3021821 : Blo 1342990 3021821 := bbase (se 3 (by rfl) ⟨566591, by rfl⟩ : syracuseStep 3021821 = 1133183) (by norm_num)
theorem B4537349 : Blo 1342990 4537349 := bbase (se 4 (by rfl) ⟨425376, by rfl⟩ : syracuseStep 4537349 = 850753) (by norm_num)
theorem B3021893 : Blo 1342990 3021893 := bbase (se 4 (by rfl) ⟨283302, by rfl⟩ : syracuseStep 3021893 = 566605) (by norm_num)
theorem B2268229 : Blo 1342990 2268229 := bbase (se 4 (by rfl) ⟨212646, by rfl⟩ : syracuseStep 2268229 = 425293) (by norm_num)
theorem B3021965 : Blo 1342990 3021965 := bbase (se 3 (by rfl) ⟨566618, by rfl⟩ : syracuseStep 3021965 = 1133237) (by norm_num)
theorem B2268317 : Blo 1342990 2268317 := bbase (se 3 (by rfl) ⟨425309, by rfl⟩ : syracuseStep 2268317 = 850619) (by norm_num)
theorem B5741765 : Blo 1342990 5741765 := bbase (se 4 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 5741765 = 1076581) (by norm_num)
theorem B3022037 : Blo 1342990 3022037 := bbase (se 7 (by rfl) ⟨35414, by rfl⟩ : syracuseStep 3022037 = 70829) (by norm_num)
theorem B1940701 : Blo 1342990 1940701 := bbase (se 3 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 1940701 = 727763) (by norm_num)
theorem B10206485 : Blo 1342990 10206485 := bbase (se 6 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 10206485 = 478429) (by norm_num)
theorem B2014493 : Blo 1342990 2014493 := bbase (se 3 (by rfl) ⟨377717, by rfl⟩ : syracuseStep 2014493 = 755435) (by norm_num)
theorem B3022109 : Blo 1342990 3022109 := bbase (se 3 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 3022109 = 1133291) (by norm_num)
theorem B2268445 : Blo 1342990 2268445 := bbase (se 3 (by rfl) ⟨425333, by rfl⟩ : syracuseStep 2268445 = 850667) (by norm_num)
theorem B2153765 : Blo 1342990 2153765 := bbase (se 4 (by rfl) ⟨201915, by rfl⟩ : syracuseStep 2153765 = 403831) (by norm_num)
theorem B2014517 : Blo 1342990 2014517 := bbase (se 5 (by rfl) ⟨94430, by rfl⟩ : syracuseStep 2014517 = 188861) (by norm_num)
theorem B2014541 : Blo 1342990 2014541 := bbase (se 3 (by rfl) ⟨377726, by rfl⟩ : syracuseStep 2014541 = 755453) (by norm_num)
theorem B2014565 : Blo 1342990 2014565 := bbase (se 4 (by rfl) ⟨188865, by rfl⟩ : syracuseStep 2014565 = 377731) (by norm_num)
theorem B3022181 : Blo 1342990 3022181 := bbase (se 4 (by rfl) ⟨283329, by rfl⟩ : syracuseStep 3022181 = 566659) (by norm_num)
theorem B2268533 : Blo 1342990 2268533 := bbase (se 5 (by rfl) ⟨106337, by rfl⟩ : syracuseStep 2268533 = 212675) (by norm_num)
theorem B2014589 : Blo 1342990 2014589 := bbase (se 3 (by rfl) ⟨377735, by rfl⟩ : syracuseStep 2014589 = 755471) (by norm_num)
theorem B2014613 : Blo 1342990 2014613 := bbase (se 6 (by rfl) ⟨47217, by rfl⟩ : syracuseStep 2014613 = 94435) (by norm_num)
theorem B2014637 : Blo 1342990 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B3022253 : Blo 1342990 3022253 := bbase (se 3 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 3022253 = 1133345) (by norm_num)
theorem B4537781 : Blo 1342990 4537781 := bbase (se 5 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 4537781 = 425417) (by norm_num)
theorem B2014661 : Blo 1342990 2014661 := bbase (se 4 (by rfl) ⟨188874, by rfl⟩ : syracuseStep 2014661 = 377749) (by norm_num)
theorem B2014685 : Blo 1342990 2014685 := bbase (se 3 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 2014685 = 755507) (by norm_num)
theorem B2014709 : Blo 1342990 2014709 := bbase (se 5 (by rfl) ⟨94439, by rfl⟩ : syracuseStep 2014709 = 188879) (by norm_num)
theorem B3022325 : Blo 1342990 3022325 := bbase (se 5 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 3022325 = 283343) (by norm_num)
theorem B2268661 : Blo 1342990 2268661 := bbase (se 5 (by rfl) ⟨106343, by rfl⟩ : syracuseStep 2268661 = 212687) (by norm_num)
theorem B2014733 : Blo 1342990 2014733 := bbase (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) (by norm_num)
theorem B2014757 : Blo 1342990 2014757 := bbase (se 4 (by rfl) ⟨188883, by rfl⟩ : syracuseStep 2014757 = 377767) (by norm_num)
theorem B6807077 : Blo 1342990 6807077 := bbase (se 4 (by rfl) ⟨638163, by rfl⟩ : syracuseStep 6807077 = 1276327) (by norm_num)
theorem B2014781 : Blo 1342990 2014781 := bbase (se 3 (by rfl) ⟨377771, by rfl⟩ : syracuseStep 2014781 = 755543) (by norm_num)
theorem B3022397 : Blo 1342990 3022397 := bbase (se 3 (by rfl) ⟨566699, by rfl⟩ : syracuseStep 3022397 = 1133399) (by norm_num)
theorem B2154053 : Blo 1342990 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B2760269 : Blo 1342990 2760269 := bbase (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) (by norm_num)
theorem B2268749 : Blo 1342990 2268749 := bbase (se 3 (by rfl) ⟨425390, by rfl⟩ : syracuseStep 2268749 = 850781) (by norm_num)
theorem B2014805 : Blo 1342990 2014805 := bbase (se 8 (by rfl) ⟨11805, by rfl⟩ : syracuseStep 2014805 = 23611) (by norm_num)
theorem B2014829 : Blo 1342990 2014829 := bbase (se 3 (by rfl) ⟨377780, by rfl⟩ : syracuseStep 2014829 = 755561) (by norm_num)
theorem B3825269 : Blo 1342990 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B2014853 : Blo 1342990 2014853 := bbase (se 4 (by rfl) ⟨188892, by rfl⟩ : syracuseStep 2014853 = 377785) (by norm_num)
theorem B3022469 : Blo 1342990 3022469 := bbase (se 4 (by rfl) ⟨283356, by rfl⟩ : syracuseStep 3022469 = 566713) (by norm_num)
theorem B1613449 : Blo 1342990 1613449 := bbase (se 2 (by rfl) ⟨605043, by rfl⟩ : syracuseStep 1613449 = 1210087) (by norm_num)
theorem B2014877 : Blo 1342990 2014877 := bbase (se 3 (by rfl) ⟨377789, by rfl⟩ : syracuseStep 2014877 = 755579) (by norm_num)
theorem B10198709 : Blo 1342990 10198709 := bbase (se 5 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 10198709 = 956129) (by norm_num)
theorem B2014901 : Blo 1342990 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B2014925 : Blo 1342990 2014925 := bbase (se 3 (by rfl) ⟨377798, by rfl⟩ : syracuseStep 2014925 = 755597) (by norm_num)
theorem B3022541 : Blo 1342990 3022541 := bbase (se 3 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 3022541 = 1133453) (by norm_num)
theorem B2268877 : Blo 1342990 2268877 := bbase (se 3 (by rfl) ⟨425414, by rfl⟩ : syracuseStep 2268877 = 850829) (by norm_num)
theorem B2014949 : Blo 1342990 2014949 := bbase (se 4 (by rfl) ⟨188901, by rfl⟩ : syracuseStep 2014949 = 377803) (by norm_num)
theorem B2014973 : Blo 1342990 2014973 := bbase (se 3 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 2014973 = 755615) (by norm_num)
theorem B2014997 : Blo 1342990 2014997 := bbase (se 6 (by rfl) ⟨47226, by rfl⟩ : syracuseStep 2014997 = 94453) (by norm_num)
theorem B3022613 : Blo 1342990 3022613 := bbase (se 6 (by rfl) ⟨70842, by rfl⟩ : syracuseStep 3022613 = 141685) (by norm_num)
theorem B4038437 : Blo 1342990 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B2268965 : Blo 1342990 2268965 := bbase (se 4 (by rfl) ⟨212715, by rfl⟩ : syracuseStep 2268965 = 425431) (by norm_num)
theorem B2015021 : Blo 1342990 2015021 := bbase (se 3 (by rfl) ⟨377816, by rfl⟩ : syracuseStep 2015021 = 755633) (by norm_num)
theorem B7757621 : Blo 1342990 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B2015045 : Blo 1342990 2015045 := bbase (se 4 (by rfl) ⟨188910, by rfl⟩ : syracuseStep 2015045 = 377821) (by norm_num)
theorem B3399509 : Blo 1342990 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B2015069 : Blo 1342990 2015069 := bbase (se 3 (by rfl) ⟨377825, by rfl⟩ : syracuseStep 2015069 = 755651) (by norm_num)
theorem B3022685 : Blo 1342990 3022685 := bbase (se 3 (by rfl) ⟨566753, by rfl⟩ : syracuseStep 3022685 = 1133507) (by norm_num)
theorem B4538213 : Blo 1342990 4538213 := bbase (se 4 (by rfl) ⟨425457, by rfl⟩ : syracuseStep 4538213 = 850915) (by norm_num)
theorem B2015093 : Blo 1342990 2015093 := bbase (se 5 (by rfl) ⟨94457, by rfl⟩ : syracuseStep 2015093 = 188915) (by norm_num)
theorem B2015117 : Blo 1342990 2015117 := bbase (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) (by norm_num)
theorem B2015141 : Blo 1342990 2015141 := bbase (se 4 (by rfl) ⟨188919, by rfl⟩ : syracuseStep 2015141 = 377839) (by norm_num)
theorem B3022757 : Blo 1342990 3022757 := bbase (se 4 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 3022757 = 566767) (by norm_num)
theorem B2269093 : Blo 1342990 2269093 := bbase (se 4 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 2269093 = 425455) (by norm_num)
theorem B2015165 : Blo 1342990 2015165 := bbase (se 3 (by rfl) ⟨377843, by rfl⟩ : syracuseStep 2015165 = 755687) (by norm_num)
theorem B6799301 : Blo 1342990 6799301 := bbase (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) (by norm_num)
theorem B2015189 : Blo 1342990 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B10346453 : Blo 1342990 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B2015213 : Blo 1342990 2015213 := bbase (se 3 (by rfl) ⟨377852, by rfl⟩ : syracuseStep 2015213 = 755705) (by norm_num)
theorem B3022829 : Blo 1342990 3022829 := bbase (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) (by norm_num)
theorem B2269181 : Blo 1342990 2269181 := bbase (se 3 (by rfl) ⟨425471, by rfl⟩ : syracuseStep 2269181 = 850943) (by norm_num)
theorem B1343491 : Blo 1342990 1343491 := bstep (se 1 (by rfl) ⟨1007618, by rfl⟩ : syracuseStep 1343491 = 2015237) B2015237
theorem B3022865 : Blo 1342990 3022865 := bstep (se 2 (by rfl) ⟨1133574, by rfl⟩ : syracuseStep 3022865 = 2267149) B2267149
theorem B2015249 : Blo 1342990 2015249 := bstep (se 2 (by rfl) ⟨755718, by rfl⟩ : syracuseStep 2015249 = 1511437) B1511437
theorem B1343507 : Blo 1342990 1343507 := bstep (se 1 (by rfl) ⟨1007630, by rfl⟩ : syracuseStep 1343507 = 2015261) B2015261
theorem B2269201 : Blo 1342990 2269201 := bstep (se 2 (by rfl) ⟨850950, by rfl⟩ : syracuseStep 2269201 = 1701901) B1701901
theorem B3022883 : Blo 1342990 3022883 := bstep (se 1 (by rfl) ⟨2267162, by rfl⟩ : syracuseStep 3022883 = 4534325) B4534325
theorem B2015267 : Blo 1342990 2015267 := bstep (se 1 (by rfl) ⟨1511450, by rfl⟩ : syracuseStep 2015267 = 3022901) B3022901
theorem B1343523 : Blo 1342990 1343523 := bstep (se 1 (by rfl) ⟨1007642, by rfl⟩ : syracuseStep 1343523 = 2015285) B2015285
theorem B1343539 : Blo 1342990 1343539 := bstep (se 1 (by rfl) ⟨1007654, by rfl⟩ : syracuseStep 1343539 = 2015309) B2015309
theorem B2269235 : Blo 1342990 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B2015297 : Blo 1342990 2015297 := bstep (se 2 (by rfl) ⟨755736, by rfl⟩ : syracuseStep 2015297 = 1511473) B1511473
theorem B1613891 : Blo 1342990 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B1343555 : Blo 1342990 1343555 := bstep (se 1 (by rfl) ⟨1007666, by rfl⟩ : syracuseStep 1343555 = 2015333) B2015333
theorem B2015315 : Blo 1342990 2015315 := bstep (se 1 (by rfl) ⟨1511486, by rfl⟩ : syracuseStep 2015315 = 3022973) B3022973
theorem B1343571 : Blo 1342990 1343571 := bstep (se 1 (by rfl) ⟨1007678, by rfl⟩ : syracuseStep 1343571 = 2015357) B2015357
theorem B1343587 : Blo 1342990 1343587 := bstep (se 1 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 1343587 = 2015381) B2015381
theorem B2015345 : Blo 1342990 2015345 := bstep (se 2 (by rfl) ⟨755754, by rfl⟩ : syracuseStep 2015345 = 1511509) B1511509
theorem B1343603 : Blo 1342990 1343603 := bstep (se 1 (by rfl) ⟨1007702, by rfl⟩ : syracuseStep 1343603 = 2015405) B2015405
theorem B2015363 : Blo 1342990 2015363 := bstep (se 1 (by rfl) ⟨1511522, by rfl⟩ : syracuseStep 2015363 = 3023045) B3023045
theorem B1343619 : Blo 1342990 1343619 := bstep (se 1 (by rfl) ⟨1007714, by rfl⟩ : syracuseStep 1343619 = 2015429) B2015429
theorem B1343635 : Blo 1342990 1343635 := bstep (se 1 (by rfl) ⟨1007726, by rfl⟩ : syracuseStep 1343635 = 2015453) B2015453
theorem B2015393 : Blo 1342990 2015393 := bstep (se 2 (by rfl) ⟨755772, by rfl⟩ : syracuseStep 2015393 = 1511545) B1511545
theorem B1343651 : Blo 1342990 1343651 := bstep (se 1 (by rfl) ⟨1007738, by rfl⟩ : syracuseStep 1343651 = 2015477) B2015477
theorem B2015411 : Blo 1342990 2015411 := bstep (se 1 (by rfl) ⟨1511558, by rfl⟩ : syracuseStep 2015411 = 3023117) B3023117
theorem B1343667 : Blo 1342990 1343667 := bstep (se 1 (by rfl) ⟨1007750, by rfl⟩ : syracuseStep 1343667 = 2015501) B2015501
theorem B2269363 : Blo 1342990 2269363 := bstep (se 1 (by rfl) ⟨1702022, by rfl⟩ : syracuseStep 2269363 = 3404045) B3404045
theorem B1343683 : Blo 1342990 1343683 := bstep (se 1 (by rfl) ⟨1007762, by rfl⟩ : syracuseStep 1343683 = 2015525) B2015525
theorem B30286021 : Blo 1342990 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B2015441 : Blo 1342990 2015441 := bstep (se 2 (by rfl) ⟨755790, by rfl⟩ : syracuseStep 2015441 = 1511581) B1511581
theorem B1343699 : Blo 1342990 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B2015459 : Blo 1342990 2015459 := bstep (se 1 (by rfl) ⟨1511594, by rfl⟩ : syracuseStep 2015459 = 3023189) B3023189
theorem B1343715 : Blo 1342990 1343715 := bstep (se 1 (by rfl) ⟨1007786, by rfl⟩ : syracuseStep 1343715 = 2015573) B2015573
theorem B1343731 : Blo 1342990 1343731 := bstep (se 1 (by rfl) ⟨1007798, by rfl⟩ : syracuseStep 1343731 = 2015597) B2015597
theorem B2015489 : Blo 1342990 2015489 := bstep (se 2 (by rfl) ⟨755808, by rfl⟩ : syracuseStep 2015489 = 1511617) B1511617
theorem B1343747 : Blo 1342990 1343747 := bstep (se 1 (by rfl) ⟨1007810, by rfl⟩ : syracuseStep 1343747 = 2015621) B2015621
theorem B2015507 : Blo 1342990 2015507 := bstep (se 1 (by rfl) ⟨1511630, by rfl⟩ : syracuseStep 2015507 = 3023261) B3023261
theorem B1343763 : Blo 1342990 1343763 := bstep (se 1 (by rfl) ⟨1007822, by rfl⟩ : syracuseStep 1343763 = 2015645) B2015645
theorem B1343779 : Blo 1342990 1343779 := bstep (se 1 (by rfl) ⟨1007834, by rfl⟩ : syracuseStep 1343779 = 2015669) B2015669
theorem B8610083 : Blo 1342990 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B3023153 : Blo 1342990 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B2015537 : Blo 1342990 2015537 := bstep (se 2 (by rfl) ⟨755826, by rfl⟩ : syracuseStep 2015537 = 1511653) B1511653
theorem B1343795 : Blo 1342990 1343795 := bstep (se 1 (by rfl) ⟨1007846, by rfl⟩ : syracuseStep 1343795 = 2015693) B2015693
theorem B2269505 : Blo 1342990 2269505 := bstep (se 2 (by rfl) ⟨851064, by rfl⟩ : syracuseStep 2269505 = 1702129) B1702129
theorem B3023171 : Blo 1342990 3023171 := bstep (se 1 (by rfl) ⟨2267378, by rfl⟩ : syracuseStep 3023171 = 4534757) B4534757
theorem B2015555 : Blo 1342990 2015555 := bstep (se 1 (by rfl) ⟨1511666, by rfl⟩ : syracuseStep 2015555 = 3023333) B3023333
theorem B1343811 : Blo 1342990 1343811 := bstep (se 1 (by rfl) ⟨1007858, by rfl⟩ : syracuseStep 1343811 = 2015717) B2015717
theorem B1343827 : Blo 1342990 1343827 := bstep (se 1 (by rfl) ⟨1007870, by rfl⟩ : syracuseStep 1343827 = 2015741) B2015741
theorem B2015585 : Blo 1342990 2015585 := bstep (se 2 (by rfl) ⟨755844, by rfl⟩ : syracuseStep 2015585 = 1511689) B1511689
theorem B1343843 : Blo 1342990 1343843 := bstep (se 1 (by rfl) ⟨1007882, by rfl⟩ : syracuseStep 1343843 = 2015765) B2015765
theorem B2015603 : Blo 1342990 2015603 := bstep (se 1 (by rfl) ⟨1511702, by rfl⟩ : syracuseStep 2015603 = 3023405) B3023405
theorem B1343859 : Blo 1342990 1343859 := bstep (se 1 (by rfl) ⟨1007894, by rfl⟩ : syracuseStep 1343859 = 2015789) B2015789
theorem B1343875 : Blo 1342990 1343875 := bstep (se 1 (by rfl) ⟨1007906, by rfl⟩ : syracuseStep 1343875 = 2015813) B2015813
theorem B2015633 : Blo 1342990 2015633 := bstep (se 2 (by rfl) ⟨755862, by rfl⟩ : syracuseStep 2015633 = 1511725) B1511725
theorem B1343891 : Blo 1342990 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B2015651 : Blo 1342990 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B1343907 : Blo 1342990 1343907 := bstep (se 1 (by rfl) ⟨1007930, by rfl⟩ : syracuseStep 1343907 = 2015861) B2015861
theorem B1343923 : Blo 1342990 1343923 := bstep (se 1 (by rfl) ⟨1007942, by rfl⟩ : syracuseStep 1343923 = 2015885) B2015885
theorem B2015681 : Blo 1342990 2015681 := bstep (se 2 (by rfl) ⟨755880, by rfl⟩ : syracuseStep 2015681 = 1511761) B1511761
theorem B1343939 : Blo 1342990 1343939 := bstep (se 1 (by rfl) ⟨1007954, by rfl⟩ : syracuseStep 1343939 = 2015909) B2015909
theorem B2269633 : Blo 1342990 2269633 := bstep (se 2 (by rfl) ⟨851112, by rfl⟩ : syracuseStep 2269633 = 1702225) B1702225
theorem B2015699 : Blo 1342990 2015699 := bstep (se 1 (by rfl) ⟨1511774, by rfl⟩ : syracuseStep 2015699 = 3023549) B3023549
theorem B1343955 : Blo 1342990 1343955 := bstep (se 1 (by rfl) ⟨1007966, by rfl⟩ : syracuseStep 1343955 = 2015933) B2015933
theorem B1343971 : Blo 1342990 1343971 := bstep (se 1 (by rfl) ⟨1007978, by rfl⟩ : syracuseStep 1343971 = 2015957) B2015957
theorem B2269667 : Blo 1342990 2269667 := bstep (se 1 (by rfl) ⟨1702250, by rfl⟩ : syracuseStep 2269667 = 3404501) B3404501
theorem B3400177 : Blo 1342990 3400177 := bstep (se 2 (by rfl) ⟨1275066, by rfl⟩ : syracuseStep 3400177 = 2550133) B2550133
theorem B2015729 : Blo 1342990 2015729 := bstep (se 2 (by rfl) ⟨755898, by rfl⟩ : syracuseStep 2015729 = 1511797) B1511797
theorem B1343987 : Blo 1342990 1343987 := bstep (se 1 (by rfl) ⟨1007990, by rfl⟩ : syracuseStep 1343987 = 2015981) B2015981
theorem B6808049 : Blo 1342990 6808049 := bstep (se 2 (by rfl) ⟨2553018, by rfl⟩ : syracuseStep 6808049 = 5106037) B5106037
theorem B4538861 : Blo 1342990 4538861 := bstep (se 3 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 4538861 = 1702073) B1702073
theorem B2015747 : Blo 1342990 2015747 := bstep (se 1 (by rfl) ⟨1511810, by rfl⟩ : syracuseStep 2015747 = 3023621) B3023621
theorem B1344003 : Blo 1342990 1344003 := bstep (se 1 (by rfl) ⟨1008002, by rfl⟩ : syracuseStep 1344003 = 2016005) B2016005
theorem B1344019 : Blo 1342990 1344019 := bstep (se 1 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 1344019 = 2016029) B2016029
theorem B2015777 : Blo 1342990 2015777 := bstep (se 2 (by rfl) ⟨755916, by rfl⟩ : syracuseStep 2015777 = 1511833) B1511833
theorem B1344035 : Blo 1342990 1344035 := bstep (se 1 (by rfl) ⟨1008026, by rfl⟩ : syracuseStep 1344035 = 2016053) B2016053
theorem B4538915 : Blo 1342990 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B2015795 : Blo 1342990 2015795 := bstep (se 1 (by rfl) ⟨1511846, by rfl⟩ : syracuseStep 2015795 = 3023693) B3023693
theorem B1344051 : Blo 1342990 1344051 := bstep (se 1 (by rfl) ⟨1008038, by rfl⟩ : syracuseStep 1344051 = 2016077) B2016077
theorem B1344067 : Blo 1342990 1344067 := bstep (se 1 (by rfl) ⟨1008050, by rfl⟩ : syracuseStep 1344067 = 2016101) B2016101
theorem B6799949 : Blo 1342990 6799949 := bstep (se 3 (by rfl) ⟨1274990, by rfl⟩ : syracuseStep 6799949 = 2549981) B2549981
theorem B3023441 : Blo 1342990 3023441 := bstep (se 2 (by rfl) ⟨1133790, by rfl⟩ : syracuseStep 3023441 = 2267581) B2267581
theorem B2015825 : Blo 1342990 2015825 := bstep (se 2 (by rfl) ⟨755934, by rfl⟩ : syracuseStep 2015825 = 1511869) B1511869
theorem B1344083 : Blo 1342990 1344083 := bstep (se 1 (by rfl) ⟨1008062, by rfl⟩ : syracuseStep 1344083 = 2016125) B2016125
theorem B3023459 : Blo 1342990 3023459 := bstep (se 1 (by rfl) ⟨2267594, by rfl⟩ : syracuseStep 3023459 = 4535189) B4535189
theorem B2015843 : Blo 1342990 2015843 := bstep (se 1 (by rfl) ⟨1511882, by rfl⟩ : syracuseStep 2015843 = 3023765) B3023765
theorem B1344099 : Blo 1342990 1344099 := bstep (se 1 (by rfl) ⟨1008074, by rfl⟩ : syracuseStep 1344099 = 2016149) B2016149
theorem B1344115 : Blo 1342990 1344115 := bstep (se 1 (by rfl) ⟨1008086, by rfl⟩ : syracuseStep 1344115 = 2016173) B2016173
theorem B2015873 : Blo 1342990 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B1344131 : Blo 1342990 1344131 := bstep (se 1 (by rfl) ⟨1008098, by rfl⟩ : syracuseStep 1344131 = 2016197) B2016197
theorem B2015891 : Blo 1342990 2015891 := bstep (se 1 (by rfl) ⟨1511918, by rfl⟩ : syracuseStep 2015891 = 3023837) B3023837
theorem B1344147 : Blo 1342990 1344147 := bstep (se 1 (by rfl) ⟨1008110, by rfl⟩ : syracuseStep 1344147 = 2016221) B2016221
theorem B1344163 : Blo 1342990 1344163 := bstep (se 1 (by rfl) ⟨1008122, by rfl⟩ : syracuseStep 1344163 = 2016245) B2016245
theorem B2015921 : Blo 1342990 2015921 := bstep (se 2 (by rfl) ⟨755970, by rfl⟩ : syracuseStep 2015921 = 1511941) B1511941
theorem B1344179 : Blo 1342990 1344179 := bstep (se 1 (by rfl) ⟨1008134, by rfl⟩ : syracuseStep 1344179 = 2016269) B2016269
theorem B2015939 : Blo 1342990 2015939 := bstep (se 1 (by rfl) ⟨1511954, by rfl⟩ : syracuseStep 2015939 = 3023909) B3023909
theorem B1532611 : Blo 1342990 1532611 := bstep (se 1 (by rfl) ⟨1149458, by rfl⟩ : syracuseStep 1532611 = 2298917) B2298917
theorem B1344195 : Blo 1342990 1344195 := bstep (se 1 (by rfl) ⟨1008146, by rfl⟩ : syracuseStep 1344195 = 2016293) B2016293
theorem B3826385 : Blo 1342990 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B1344211 : Blo 1342990 1344211 := bstep (se 1 (by rfl) ⟨1008158, by rfl⟩ : syracuseStep 1344211 = 2016317) B2016317
theorem B2015969 : Blo 1342990 2015969 := bstep (se 2 (by rfl) ⟨755988, by rfl⟩ : syracuseStep 2015969 = 1511977) B1511977
theorem B1344227 : Blo 1342990 1344227 := bstep (se 1 (by rfl) ⟨1008170, by rfl⟩ : syracuseStep 1344227 = 2016341) B2016341
theorem B2015987 : Blo 1342990 2015987 := bstep (se 1 (by rfl) ⟨1511990, by rfl⟩ : syracuseStep 2015987 = 3023981) B3023981
theorem B1344243 : Blo 1342990 1344243 := bstep (se 1 (by rfl) ⟨1008182, by rfl⟩ : syracuseStep 1344243 = 2016365) B2016365
theorem B3400451 : Blo 1342990 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B1344259 : Blo 1342990 1344259 := bstep (se 1 (by rfl) ⟨1008194, by rfl⟩ : syracuseStep 1344259 = 2016389) B2016389
theorem B5104397 : Blo 1342990 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B2016017 : Blo 1342990 2016017 := bstep (se 2 (by rfl) ⟨756006, by rfl⟩ : syracuseStep 2016017 = 1512013) B1512013
theorem B1344275 : Blo 1342990 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B2016035 : Blo 1342990 2016035 := bstep (se 1 (by rfl) ⟨1512026, by rfl⟩ : syracuseStep 2016035 = 3024053) B3024053
theorem B1344291 : Blo 1342990 1344291 := bstep (se 1 (by rfl) ⟨1008218, by rfl⟩ : syracuseStep 1344291 = 2016437) B2016437
theorem B4539185 : Blo 1342990 4539185 := bstep (se 2 (by rfl) ⟨1702194, by rfl⟩ : syracuseStep 4539185 = 3404389) B3404389
theorem B1344307 : Blo 1342990 1344307 := bstep (se 1 (by rfl) ⟨1008230, by rfl⟩ : syracuseStep 1344307 = 2016461) B2016461
theorem B2016065 : Blo 1342990 2016065 := bstep (se 2 (by rfl) ⟨756024, by rfl⟩ : syracuseStep 2016065 = 1512049) B1512049
theorem B1344323 : Blo 1342990 1344323 := bstep (se 1 (by rfl) ⟨1008242, by rfl⟩ : syracuseStep 1344323 = 2016485) B2016485
theorem B2016083 : Blo 1342990 2016083 := bstep (se 1 (by rfl) ⟨1512062, by rfl⟩ : syracuseStep 2016083 = 3024125) B3024125
theorem B1344339 : Blo 1342990 1344339 := bstep (se 1 (by rfl) ⟨1008254, by rfl⟩ : syracuseStep 1344339 = 2016509) B2016509
theorem B1434467 : Blo 1342990 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B1344355 : Blo 1342990 1344355 := bstep (se 1 (by rfl) ⟨1008266, by rfl⟩ : syracuseStep 1344355 = 2016533) B2016533
theorem B3023729 : Blo 1342990 3023729 := bstep (se 2 (by rfl) ⟨1133898, by rfl⟩ : syracuseStep 3023729 = 2267797) B2267797
theorem B2016113 : Blo 1342990 2016113 := bstep (se 2 (by rfl) ⟨756042, by rfl⟩ : syracuseStep 2016113 = 1512085) B1512085
theorem B1344371 : Blo 1342990 1344371 := bstep (se 1 (by rfl) ⟨1008278, by rfl⟩ : syracuseStep 1344371 = 2016557) B2016557
theorem B3023747 : Blo 1342990 3023747 := bstep (se 1 (by rfl) ⟨2267810, by rfl⟩ : syracuseStep 3023747 = 4535621) B4535621
theorem B2016131 : Blo 1342990 2016131 := bstep (se 1 (by rfl) ⟨1512098, by rfl⟩ : syracuseStep 2016131 = 3024197) B3024197
theorem B1344387 : Blo 1342990 1344387 := bstep (se 1 (by rfl) ⟨1008290, by rfl⟩ : syracuseStep 1344387 = 2016581) B2016581
theorem B1344403 : Blo 1342990 1344403 := bstep (se 1 (by rfl) ⟨1008302, by rfl⟩ : syracuseStep 1344403 = 2016605) B2016605
theorem B2016161 : Blo 1342990 2016161 := bstep (se 2 (by rfl) ⟨756060, by rfl⟩ : syracuseStep 2016161 = 1512121) B1512121
theorem B1344419 : Blo 1342990 1344419 := bstep (se 1 (by rfl) ⟨1008314, by rfl⟩ : syracuseStep 1344419 = 2016629) B2016629
theorem B2016179 : Blo 1342990 2016179 := bstep (se 1 (by rfl) ⟨1512134, by rfl⟩ : syracuseStep 2016179 = 3024269) B3024269
theorem B1344435 : Blo 1342990 1344435 := bstep (se 1 (by rfl) ⟨1008326, by rfl⟩ : syracuseStep 1344435 = 2016653) B2016653
theorem B3400643 : Blo 1342990 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B44172229 : Blo 1342990 44172229 := bstep (se 4 (by rfl) ⟨4141146, by rfl⟩ : syracuseStep 44172229 = 8282293) B8282293
theorem B1344451 : Blo 1342990 1344451 := bstep (se 1 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 1344451 = 2016677) B2016677
theorem B2016209 : Blo 1342990 2016209 := bstep (se 2 (by rfl) ⟨756078, by rfl⟩ : syracuseStep 2016209 = 1512157) B1512157
theorem B1344467 : Blo 1342990 1344467 := bstep (se 1 (by rfl) ⟨1008350, by rfl⟩ : syracuseStep 1344467 = 2016701) B2016701
theorem B2016227 : Blo 1342990 2016227 := bstep (se 1 (by rfl) ⟨1512170, by rfl⟩ : syracuseStep 2016227 = 3024341) B3024341
theorem B1344483 : Blo 1342990 1344483 := bstep (se 1 (by rfl) ⟨1008362, by rfl⟩ : syracuseStep 1344483 = 2016725) B2016725
theorem B1344499 : Blo 1342990 1344499 := bstep (se 1 (by rfl) ⟨1008374, by rfl⟩ : syracuseStep 1344499 = 2016749) B2016749
theorem B2016257 : Blo 1342990 2016257 := bstep (se 2 (by rfl) ⟨756096, by rfl⟩ : syracuseStep 2016257 = 1512193) B1512193
theorem B1344515 : Blo 1342990 1344515 := bstep (se 1 (by rfl) ⟨1008386, by rfl⟩ : syracuseStep 1344515 = 2016773) B2016773
theorem B7267333 : Blo 1342990 7267333 := bstep (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) B1362625
theorem B2016275 : Blo 1342990 2016275 := bstep (se 1 (by rfl) ⟨1512206, by rfl⟩ : syracuseStep 2016275 = 3024413) B3024413
theorem B1344531 : Blo 1342990 1344531 := bstep (se 1 (by rfl) ⟨1008398, by rfl⟩ : syracuseStep 1344531 = 2016797) B2016797
theorem B1344547 : Blo 1342990 1344547 := bstep (se 1 (by rfl) ⟨1008410, by rfl⟩ : syracuseStep 1344547 = 2016821) B2016821
theorem B2016305 : Blo 1342990 2016305 := bstep (se 2 (by rfl) ⟨756114, by rfl⟩ : syracuseStep 2016305 = 1512229) B1512229
theorem B1344563 : Blo 1342990 1344563 := bstep (se 1 (by rfl) ⟨1008422, by rfl⟩ : syracuseStep 1344563 = 2016845) B2016845
theorem B2016323 : Blo 1342990 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B1344579 : Blo 1342990 1344579 := bstep (se 1 (by rfl) ⟨1008434, by rfl⟩ : syracuseStep 1344579 = 2016869) B2016869
theorem B1344595 : Blo 1342990 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B2016353 : Blo 1342990 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B4842595 : Blo 1342990 4842595 := bstep (se 1 (by rfl) ⟨3631946, by rfl⟩ : syracuseStep 4842595 = 7263893) B7263893
theorem B1344611 : Blo 1342990 1344611 := bstep (se 1 (by rfl) ⟨1008458, by rfl⟩ : syracuseStep 1344611 = 2016917) B2016917
theorem B2016371 : Blo 1342990 2016371 := bstep (se 1 (by rfl) ⟨1512278, by rfl⟩ : syracuseStep 2016371 = 3024557) B3024557
theorem B1344627 : Blo 1342990 1344627 := bstep (se 1 (by rfl) ⟨1008470, by rfl⟩ : syracuseStep 1344627 = 2016941) B2016941
theorem B1344643 : Blo 1342990 1344643 := bstep (se 1 (by rfl) ⟨1008482, by rfl⟩ : syracuseStep 1344643 = 2016965) B2016965
theorem B3024017 : Blo 1342990 3024017 := bstep (se 2 (by rfl) ⟨1134006, by rfl⟩ : syracuseStep 3024017 = 2268013) B2268013
theorem B2016401 : Blo 1342990 2016401 := bstep (se 2 (by rfl) ⟨756150, by rfl⟩ : syracuseStep 2016401 = 1512301) B1512301
theorem B1344659 : Blo 1342990 1344659 := bstep (se 1 (by rfl) ⟨1008494, by rfl⟩ : syracuseStep 1344659 = 2016989) B2016989
theorem B3024035 : Blo 1342990 3024035 := bstep (se 1 (by rfl) ⟨2268026, by rfl⟩ : syracuseStep 3024035 = 4536053) B4536053
theorem B2016419 : Blo 1342990 2016419 := bstep (se 1 (by rfl) ⟨1512314, by rfl⟩ : syracuseStep 2016419 = 3024629) B3024629
theorem B1344675 : Blo 1342990 1344675 := bstep (se 1 (by rfl) ⟨1008506, by rfl⟩ : syracuseStep 1344675 = 2017013) B2017013
theorem B1344691 : Blo 1342990 1344691 := bstep (se 1 (by rfl) ⟨1008518, by rfl⟩ : syracuseStep 1344691 = 2017037) B2017037
theorem B2016449 : Blo 1342990 2016449 := bstep (se 2 (by rfl) ⟨756168, by rfl⟩ : syracuseStep 2016449 = 1512337) B1512337
theorem B1344707 : Blo 1342990 1344707 := bstep (se 1 (by rfl) ⟨1008530, by rfl⟩ : syracuseStep 1344707 = 2017061) B2017061
theorem B2016467 : Blo 1342990 2016467 := bstep (se 1 (by rfl) ⟨1512350, by rfl⟩ : syracuseStep 2016467 = 3024701) B3024701
theorem B1344723 : Blo 1342990 1344723 := bstep (se 1 (by rfl) ⟨1008542, by rfl⟩ : syracuseStep 1344723 = 2017085) B2017085
theorem B1344739 : Blo 1342990 1344739 := bstep (se 1 (by rfl) ⟨1008554, by rfl⟩ : syracuseStep 1344739 = 2017109) B2017109
theorem B2016497 : Blo 1342990 2016497 := bstep (se 2 (by rfl) ⟨756186, by rfl⟩ : syracuseStep 2016497 = 1512373) B1512373
theorem B1344755 : Blo 1342990 1344755 := bstep (se 1 (by rfl) ⟨1008566, by rfl⟩ : syracuseStep 1344755 = 2017133) B2017133
theorem B2016515 : Blo 1342990 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B1344771 : Blo 1342990 1344771 := bstep (se 1 (by rfl) ⟨1008578, by rfl⟩ : syracuseStep 1344771 = 2017157) B2017157
theorem B1344787 : Blo 1342990 1344787 := bstep (se 1 (by rfl) ⟨1008590, by rfl⟩ : syracuseStep 1344787 = 2017181) B2017181
theorem B33596693 : Blo 1342990 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B2016545 : Blo 1342990 2016545 := bstep (se 2 (by rfl) ⟨756204, by rfl⟩ : syracuseStep 2016545 = 1512409) B1512409
theorem B1344803 : Blo 1342990 1344803 := bstep (se 1 (by rfl) ⟨1008602, by rfl⟩ : syracuseStep 1344803 = 2017205) B2017205
theorem B2016563 : Blo 1342990 2016563 := bstep (se 1 (by rfl) ⟨1512422, by rfl⟩ : syracuseStep 2016563 = 3024845) B3024845
theorem B1344819 : Blo 1342990 1344819 := bstep (se 1 (by rfl) ⟨1008614, by rfl⟩ : syracuseStep 1344819 = 2017229) B2017229
theorem B1344835 : Blo 1342990 1344835 := bstep (se 1 (by rfl) ⟨1008626, by rfl⟩ : syracuseStep 1344835 = 2017253) B2017253
theorem B7652677 : Blo 1342990 7652677 := bstep (se 4 (by rfl) ⟨717438, by rfl⟩ : syracuseStep 7652677 = 1434877) B1434877
theorem B3630413 : Blo 1342990 3630413 := bstep (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) B1361405
theorem B2016593 : Blo 1342990 2016593 := bstep (se 2 (by rfl) ⟨756222, by rfl⟩ : syracuseStep 2016593 = 1512445) B1512445
theorem B1344851 : Blo 1342990 1344851 := bstep (se 1 (by rfl) ⟨1008638, by rfl⟩ : syracuseStep 1344851 = 2017277) B2017277
theorem B8848739 : Blo 1342990 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B2016611 : Blo 1342990 2016611 := bstep (se 1 (by rfl) ⟨1512458, by rfl⟩ : syracuseStep 2016611 = 3024917) B3024917
theorem B1344867 : Blo 1342990 1344867 := bstep (se 1 (by rfl) ⟨1008650, by rfl⟩ : syracuseStep 1344867 = 2017301) B2017301
theorem B1344883 : Blo 1342990 1344883 := bstep (se 1 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 1344883 = 2017325) B2017325
theorem B2016641 : Blo 1342990 2016641 := bstep (se 2 (by rfl) ⟨756240, by rfl⟩ : syracuseStep 2016641 = 1512481) B1512481
theorem B1344899 : Blo 1342990 1344899 := bstep (se 1 (by rfl) ⟨1008674, by rfl⟩ : syracuseStep 1344899 = 2017349) B2017349
theorem B2016659 : Blo 1342990 2016659 := bstep (se 1 (by rfl) ⟨1512494, by rfl⟩ : syracuseStep 2016659 = 3024989) B3024989
theorem B1344915 : Blo 1342990 1344915 := bstep (se 1 (by rfl) ⟨1008686, by rfl⟩ : syracuseStep 1344915 = 2017373) B2017373
theorem B1344931 : Blo 1342990 1344931 := bstep (se 1 (by rfl) ⟨1008698, by rfl⟩ : syracuseStep 1344931 = 2017397) B2017397
theorem B4842929 : Blo 1342990 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B3024305 : Blo 1342990 3024305 := bstep (se 2 (by rfl) ⟨1134114, by rfl⟩ : syracuseStep 3024305 = 2268229) B2268229
theorem B2016689 : Blo 1342990 2016689 := bstep (se 2 (by rfl) ⟨756258, by rfl⟩ : syracuseStep 2016689 = 1512517) B1512517
theorem B1344947 : Blo 1342990 1344947 := bstep (se 1 (by rfl) ⟨1008710, by rfl⟩ : syracuseStep 1344947 = 2017421) B2017421
theorem B3024323 : Blo 1342990 3024323 := bstep (se 1 (by rfl) ⟨2268242, by rfl⟩ : syracuseStep 3024323 = 4536485) B4536485
theorem B2016707 : Blo 1342990 2016707 := bstep (se 1 (by rfl) ⟨1512530, by rfl⟩ : syracuseStep 2016707 = 3025061) B3025061
theorem B11478469 : Blo 1342990 11478469 := bstep (se 4 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 11478469 = 2152213) B2152213
theorem B1344963 : Blo 1342990 1344963 := bstep (se 1 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 1344963 = 2017445) B2017445
theorem B1344979 : Blo 1342990 1344979 := bstep (se 1 (by rfl) ⟨1008734, by rfl⟩ : syracuseStep 1344979 = 2017469) B2017469
theorem B2016737 : Blo 1342990 2016737 := bstep (se 2 (by rfl) ⟨756276, by rfl⟩ : syracuseStep 2016737 = 1512553) B1512553
theorem B3630563 : Blo 1342990 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B2016755 : Blo 1342990 2016755 := bstep (se 1 (by rfl) ⟨1512566, by rfl⟩ : syracuseStep 2016755 = 3025133) B3025133
theorem B5744141 : Blo 1342990 5744141 := bstep (se 3 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 5744141 = 2154053) B2154053
theorem B2016785 : Blo 1342990 2016785 := bstep (se 2 (by rfl) ⟨756294, by rfl⟩ : syracuseStep 2016785 = 1512589) B1512589
theorem B2016803 : Blo 1342990 2016803 := bstep (se 1 (by rfl) ⟨1512602, by rfl⟩ : syracuseStep 2016803 = 3025205) B3025205
theorem B2016833 : Blo 1342990 2016833 := bstep (se 2 (by rfl) ⟨756312, by rfl⟩ : syracuseStep 2016833 = 1512625) B1512625
theorem B2016851 : Blo 1342990 2016851 := bstep (se 1 (by rfl) ⟨1512638, by rfl⟩ : syracuseStep 2016851 = 3025277) B3025277
theorem B2016881 : Blo 1342990 2016881 := bstep (se 2 (by rfl) ⟨756330, by rfl⟩ : syracuseStep 2016881 = 1512661) B1512661
theorem B4302467 : Blo 1342990 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B2016899 : Blo 1342990 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B3827341 : Blo 1342990 3827341 := bstep (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) B1435253
theorem B2016929 : Blo 1342990 2016929 := bstep (se 2 (by rfl) ⟨756348, by rfl⟩ : syracuseStep 2016929 = 1512697) B1512697
theorem B2016947 : Blo 1342990 2016947 := bstep (se 1 (by rfl) ⟨1512710, by rfl⟩ : syracuseStep 2016947 = 3025421) B3025421
theorem B3024593 : Blo 1342990 3024593 := bstep (se 2 (by rfl) ⟨1134222, by rfl⟩ : syracuseStep 3024593 = 2268445) B2268445
theorem B2016977 : Blo 1342990 2016977 := bstep (se 2 (by rfl) ⟨756366, by rfl⟩ : syracuseStep 2016977 = 1512733) B1512733
theorem B3024611 : Blo 1342990 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B2016995 : Blo 1342990 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B2017025 : Blo 1342990 2017025 := bstep (se 2 (by rfl) ⟨756384, by rfl⟩ : syracuseStep 2017025 = 1512769) B1512769
theorem B2868995 : Blo 1342990 2868995 := bstep (se 1 (by rfl) ⟨2151746, by rfl⟩ : syracuseStep 2868995 = 4303493) B4303493
theorem B2098963 : Blo 1342990 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B2017043 : Blo 1342990 2017043 := bstep (se 1 (by rfl) ⟨1512782, by rfl⟩ : syracuseStep 2017043 = 3025565) B3025565
theorem B2017073 : Blo 1342990 2017073 := bstep (se 2 (by rfl) ⟨756402, by rfl⟩ : syracuseStep 2017073 = 1512805) B1512805
theorem B2017091 : Blo 1342990 2017091 := bstep (se 1 (by rfl) ⟨1512818, by rfl⟩ : syracuseStep 2017091 = 3025637) B3025637
theorem B2017121 : Blo 1342990 2017121 := bstep (se 2 (by rfl) ⟨756420, by rfl⟩ : syracuseStep 2017121 = 1512841) B1512841
theorem B3401585 : Blo 1342990 3401585 := bstep (se 2 (by rfl) ⟨1275594, by rfl⟩ : syracuseStep 3401585 = 2551189) B2551189
theorem B3827569 : Blo 1342990 3827569 := bstep (se 2 (by rfl) ⟨1435338, by rfl⟩ : syracuseStep 3827569 = 2870677) B2870677
theorem B2017139 : Blo 1342990 2017139 := bstep (se 1 (by rfl) ⟨1512854, by rfl⟩ : syracuseStep 2017139 = 3025709) B3025709
theorem B2017169 : Blo 1342990 2017169 := bstep (se 2 (by rfl) ⟨756438, by rfl⟩ : syracuseStep 2017169 = 1512877) B1512877
theorem B3401635 : Blo 1342990 3401635 := bstep (se 1 (by rfl) ⟨2551226, by rfl⟩ : syracuseStep 3401635 = 5102453) B5102453
theorem B2017187 : Blo 1342990 2017187 := bstep (se 1 (by rfl) ⟨1512890, by rfl⟩ : syracuseStep 2017187 = 3025781) B3025781
theorem B2623409 : Blo 1342990 2623409 := bstep (se 2 (by rfl) ⟨983778, by rfl⟩ : syracuseStep 2623409 = 1967557) B1967557
theorem B2017217 : Blo 1342990 2017217 := bstep (se 2 (by rfl) ⟨756456, by rfl⟩ : syracuseStep 2017217 = 1512913) B1512913
theorem B2017235 : Blo 1342990 2017235 := bstep (se 1 (by rfl) ⟨1512926, by rfl⟩ : syracuseStep 2017235 = 3025853) B3025853
theorem B2549731 : Blo 1342990 2549731 := bstep (se 1 (by rfl) ⟨1912298, by rfl⟩ : syracuseStep 2549731 = 3824597) B3824597
theorem B3024881 : Blo 1342990 3024881 := bstep (se 2 (by rfl) ⟨1134330, by rfl⟩ : syracuseStep 3024881 = 2268661) B2268661
theorem B11487217 : Blo 1342990 11487217 := bstep (se 2 (by rfl) ⟨4307706, by rfl⟩ : syracuseStep 11487217 = 8615413) B8615413
theorem B2017265 : Blo 1342990 2017265 := bstep (se 2 (by rfl) ⟨756474, by rfl⟩ : syracuseStep 2017265 = 1512949) B1512949
theorem B3024899 : Blo 1342990 3024899 := bstep (se 1 (by rfl) ⟨2268674, by rfl⟩ : syracuseStep 3024899 = 4537349) B4537349
theorem B2017283 : Blo 1342990 2017283 := bstep (se 1 (by rfl) ⟨1512962, by rfl⟩ : syracuseStep 2017283 = 3025925) B3025925
theorem B3827729 : Blo 1342990 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B2017313 : Blo 1342990 2017313 := bstep (se 2 (by rfl) ⟨756492, by rfl⟩ : syracuseStep 2017313 = 1512985) B1512985
theorem B8177699 : Blo 1342990 8177699 := bstep (se 1 (by rfl) ⟨6133274, by rfl⟩ : syracuseStep 8177699 = 12266549) B12266549
theorem B3401777 : Blo 1342990 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2017331 : Blo 1342990 2017331 := bstep (se 1 (by rfl) ⟨1512998, by rfl⟩ : syracuseStep 2017331 = 3025997) B3025997
theorem B2017361 : Blo 1342990 2017361 := bstep (se 2 (by rfl) ⟨756510, by rfl⟩ : syracuseStep 2017361 = 1513021) B1513021
theorem B2017379 : Blo 1342990 2017379 := bstep (se 1 (by rfl) ⟨1513034, by rfl⟩ : syracuseStep 2017379 = 3026069) B3026069
theorem B4843633 : Blo 1342990 4843633 := bstep (se 2 (by rfl) ⟨1816362, by rfl⟩ : syracuseStep 4843633 = 3632725) B3632725
theorem B2017409 : Blo 1342990 2017409 := bstep (se 2 (by rfl) ⟨756528, by rfl⟩ : syracuseStep 2017409 = 1513057) B1513057
theorem B3827843 : Blo 1342990 3827843 := bstep (se 1 (by rfl) ⟨2870882, by rfl⟩ : syracuseStep 3827843 = 5741765) B5741765
theorem B2017427 : Blo 1342990 2017427 := bstep (se 1 (by rfl) ⟨1513070, by rfl⟩ : syracuseStep 2017427 = 3026141) B3026141
theorem B6129827 : Blo 1342990 6129827 := bstep (se 1 (by rfl) ⟨4597370, by rfl⟩ : syracuseStep 6129827 = 9194741) B9194741
theorem B2017457 : Blo 1342990 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B1435843 : Blo 1342990 1435843 := bstep (se 1 (by rfl) ⟨1076882, by rfl⟩ : syracuseStep 1435843 = 2153765) B2153765
theorem B2017475 : Blo 1342990 2017475 := bstep (se 1 (by rfl) ⟨1513106, by rfl⟩ : syracuseStep 2017475 = 3026213) B3026213
theorem B75598051 : Blo 1342990 75598051 := bstep (se 1 (by rfl) ⟨56698538, by rfl⟩ : syracuseStep 75598051 = 113397077) B113397077
theorem B5449997 : Blo 1342990 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B3025169 : Blo 1342990 3025169 := bstep (se 2 (by rfl) ⟨1134438, by rfl⟩ : syracuseStep 3025169 = 2268877) B2268877
theorem B3025187 : Blo 1342990 3025187 := bstep (se 1 (by rfl) ⟨2268890, by rfl⟩ : syracuseStep 3025187 = 4537781) B4537781
theorem B2550179 : Blo 1342990 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B3631601 : Blo 1342990 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B5171747 : Blo 1342990 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B3230243 : Blo 1342990 3230243 := bstep (se 1 (by rfl) ⟨2422682, by rfl⟩ : syracuseStep 3230243 = 4845365) B4845365
theorem B3025457 : Blo 1342990 3025457 := bstep (se 2 (by rfl) ⟨1134546, by rfl⟩ : syracuseStep 3025457 = 2269093) B2269093
theorem B3025475 : Blo 1342990 3025475 := bstep (se 1 (by rfl) ⟨2269106, by rfl⟩ : syracuseStep 3025475 = 4538213) B4538213
theorem B4532813 : Blo 1342990 4532813 := bstep (se 3 (by rfl) ⟨849902, by rfl⟩ : syracuseStep 4532813 = 1699805) B1699805
theorem B4532867 : Blo 1342990 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B3066499 : Blo 1342990 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B2550467 : Blo 1342990 2550467 := bstep (se 1 (by rfl) ⟨1912850, by rfl⟩ : syracuseStep 2550467 = 3825701) B3825701
theorem B3230435 : Blo 1342990 3230435 := bstep (se 1 (by rfl) ⟨2422826, by rfl⟩ : syracuseStep 3230435 = 4845653) B4845653
theorem B1362691 : Blo 1342990 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B2181905 : Blo 1342990 2181905 := bstep (se 2 (by rfl) ⟨818214, by rfl⟩ : syracuseStep 2181905 = 1636429) B1636429
theorem B5106509 : Blo 1342990 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B3025745 : Blo 1342990 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B3025763 : Blo 1342990 3025763 := bstep (se 1 (by rfl) ⟨2269322, by rfl⟩ : syracuseStep 3025763 = 4538645) B4538645
theorem B4533137 : Blo 1342990 4533137 := bstep (se 2 (by rfl) ⟨1699926, by rfl⟩ : syracuseStep 4533137 = 3399853) B3399853
theorem B2042801 : Blo 1342990 2042801 := bstep (se 2 (by rfl) ⟨766050, by rfl⟩ : syracuseStep 2042801 = 1532101) B1532101
theorem B4303811 : Blo 1342990 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B2870225 : Blo 1342990 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B4598765 : Blo 1342990 4598765 := bstep (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) B1724537
theorem B3230723 : Blo 1342990 3230723 := bstep (se 1 (by rfl) ⟨2423042, by rfl⟩ : syracuseStep 3230723 = 4846085) B4846085
theorem B3402769 : Blo 1342990 3402769 := bstep (se 2 (by rfl) ⟨1276038, by rfl⟩ : syracuseStep 3402769 = 2552077) B2552077
theorem B18385973 : Blo 1342990 18385973 := bstep (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) B1723685
theorem B10210373 : Blo 1342990 10210373 := bstep (se 4 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 10210373 = 1914445) B1914445
theorem B3828845 : Blo 1342990 3828845 := bstep (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) B1435817
theorem B3026033 : Blo 1342990 3026033 := bstep (se 2 (by rfl) ⟨1134762, by rfl⟩ : syracuseStep 3026033 = 2269525) B2269525
theorem B3026051 : Blo 1342990 3026051 := bstep (se 1 (by rfl) ⟨2269538, by rfl⟩ : syracuseStep 3026051 = 4539077) B4539077
theorem B7654661 : Blo 1342990 7654661 := bstep (se 4 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 7654661 = 1435249) B1435249
theorem B3403043 : Blo 1342990 3403043 := bstep (se 1 (by rfl) ⟨2552282, by rfl⟩ : syracuseStep 3403043 = 5104565) B5104565
theorem B3829027 : Blo 1342990 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B6892877 : Blo 1342990 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B15306083 : Blo 1342990 15306083 := bstep (se 1 (by rfl) ⟨11479562, by rfl⟩ : syracuseStep 15306083 = 22959125) B22959125
theorem B8605061 : Blo 1342990 8605061 := bstep (se 4 (by rfl) ⟨806724, by rfl⟩ : syracuseStep 8605061 = 1613449) B1613449
theorem B4533677 : Blo 1342990 4533677 := bstep (se 3 (by rfl) ⟨850064, by rfl⟩ : syracuseStep 4533677 = 1700129) B1700129
theorem B6802865 : Blo 1342990 6802865 := bstep (se 2 (by rfl) ⟨2551074, by rfl⟩ : syracuseStep 6802865 = 5102149) B5102149
theorem B3829187 : Blo 1342990 3829187 := bstep (se 1 (by rfl) ⟨2871890, by rfl⟩ : syracuseStep 3829187 = 5743781) B5743781
theorem B4533731 : Blo 1342990 4533731 := bstep (se 1 (by rfl) ⟨3400298, by rfl⟩ : syracuseStep 4533731 = 6800597) B6800597
theorem B3403235 : Blo 1342990 3403235 := bstep (se 1 (by rfl) ⟨2552426, by rfl⟩ : syracuseStep 3403235 = 5104853) B5104853
theorem B1510915 : Blo 1342990 1510915 := bstep (se 1 (by rfl) ⟨1133186, by rfl⟩ : syracuseStep 1510915 = 2266373) B2266373
theorem B2723377 : Blo 1342990 2723377 := bstep (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) B2042533
theorem B2297411 : Blo 1342990 2297411 := bstep (se 1 (by rfl) ⟨1723058, by rfl⟩ : syracuseStep 2297411 = 3446117) B3446117
theorem B2551409 : Blo 1342990 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B2043505 : Blo 1342990 2043505 := bstep (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) B1532629
theorem B7761521 : Blo 1342990 7761521 := bstep (se 2 (by rfl) ⟨2910570, by rfl⟩ : syracuseStep 7761521 = 5821141) B5821141
theorem B2420369 : Blo 1342990 2420369 := bstep (se 2 (by rfl) ⟨907638, by rfl⟩ : syracuseStep 2420369 = 1815277) B1815277
theorem B1511059 : Blo 1342990 1511059 := bstep (se 1 (by rfl) ⟨1133294, by rfl⟩ : syracuseStep 1511059 = 2266589) B2266589
theorem B3632813 : Blo 1342990 3632813 := bstep (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) B1362305
theorem B2297521 : Blo 1342990 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B4534001 : Blo 1342990 4534001 := bstep (se 2 (by rfl) ⟨1700250, by rfl⟩ : syracuseStep 4534001 = 3400501) B3400501
theorem B1912577 : Blo 1342990 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B2297603 : Blo 1342990 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B1511203 : Blo 1342990 1511203 := bstep (se 1 (by rfl) ⟨1133402, by rfl⟩ : syracuseStep 1511203 = 2266805) B2266805
theorem B2871121 : Blo 1342990 2871121 := bstep (se 2 (by rfl) ⟨1076670, by rfl⟩ : syracuseStep 2871121 = 2153341) B2153341
theorem B2871139 : Blo 1342990 2871139 := bstep (se 1 (by rfl) ⟨2153354, by rfl⟩ : syracuseStep 2871139 = 4306709) B4306709
theorem B24850289 : Blo 1342990 24850289 := bstep (se 2 (by rfl) ⟨9318858, by rfl⟩ : syracuseStep 24850289 = 18637717) B18637717
theorem B1912691 : Blo 1342990 1912691 := bstep (se 1 (by rfl) ⟨1434518, by rfl⟩ : syracuseStep 1912691 = 2869037) B2869037
theorem B8613773 : Blo 1342990 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1511347 : Blo 1342990 1511347 := bstep (se 1 (by rfl) ⟨1133510, by rfl⟩ : syracuseStep 1511347 = 2267021) B2267021
theorem B1912771 : Blo 1342990 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B1699795 : Blo 1342990 1699795 := bstep (se 1 (by rfl) ⟨1274846, by rfl⟩ : syracuseStep 1699795 = 2549693) B2549693
theorem B2043859 : Blo 1342990 2043859 := bstep (se 1 (by rfl) ⟨1532894, by rfl⟩ : syracuseStep 2043859 = 3065789) B3065789
theorem B14528483 : Blo 1342990 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B1511491 : Blo 1342990 1511491 := bstep (se 1 (by rfl) ⟨1133618, by rfl⟩ : syracuseStep 1511491 = 2267237) B2267237
theorem B16339043 : Blo 1342990 16339043 := bstep (se 1 (by rfl) ⟨12254282, by rfl⟩ : syracuseStep 16339043 = 24508565) B24508565
theorem B7360717 : Blo 1342990 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B1511635 : Blo 1342990 1511635 := bstep (se 1 (by rfl) ⟨1133726, by rfl⟩ : syracuseStep 1511635 = 2267453) B2267453
theorem B2183411 : Blo 1342990 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B4534541 : Blo 1342990 4534541 := bstep (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) B1700453
theorem B2298179 : Blo 1342990 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B4534595 : Blo 1342990 4534595 := bstep (se 1 (by rfl) ⟨3400946, by rfl⟩ : syracuseStep 4534595 = 6801893) B6801893
theorem B1511779 : Blo 1342990 1511779 := bstep (se 1 (by rfl) ⟨1133834, by rfl⟩ : syracuseStep 1511779 = 2267669) B2267669
theorem B11645297 : Blo 1342990 11645297 := bstep (se 2 (by rfl) ⟨4366986, by rfl⟩ : syracuseStep 11645297 = 8733973) B8733973
theorem B3404177 : Blo 1342990 3404177 := bstep (se 2 (by rfl) ⟨1276566, by rfl⟩ : syracuseStep 3404177 = 2553133) B2553133
theorem B1700291 : Blo 1342990 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B3404227 : Blo 1342990 3404227 := bstep (se 1 (by rfl) ⟨2553170, by rfl⟩ : syracuseStep 3404227 = 5106341) B5106341
theorem B18403811 : Blo 1342990 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B4362737 : Blo 1342990 4362737 := bstep (se 2 (by rfl) ⟨1636026, by rfl⟩ : syracuseStep 4362737 = 3272053) B3272053
theorem B1913329 : Blo 1342990 1913329 := bstep (se 2 (by rfl) ⟨717498, by rfl⟩ : syracuseStep 1913329 = 1434997) B1434997
theorem B1511923 : Blo 1342990 1511923 := bstep (se 1 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 1511923 = 2267885) B2267885
theorem B2552305 : Blo 1342990 2552305 := bstep (se 2 (by rfl) ⟨957114, by rfl⟩ : syracuseStep 2552305 = 1914229) B1914229
theorem B4534865 : Blo 1342990 4534865 := bstep (se 2 (by rfl) ⟨1700574, by rfl⟩ : syracuseStep 4534865 = 3401149) B3401149
theorem B3404369 : Blo 1342990 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B9826915 : Blo 1342990 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1512067 : Blo 1342990 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B2552465 : Blo 1342990 2552465 := bstep (se 2 (by rfl) ⟨957174, by rfl⟩ : syracuseStep 2552465 = 1914349) B1914349
theorem B4305581 : Blo 1342990 4305581 := bstep (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) B1614593
theorem B1512211 : Blo 1342990 1512211 := bstep (se 1 (by rfl) ⟨1134158, by rfl⟩ : syracuseStep 1512211 = 2268317) B2268317
theorem B6804323 : Blo 1342990 6804323 := bstep (se 1 (by rfl) ⟨5103242, by rfl⟩ : syracuseStep 6804323 = 10206485) B10206485
theorem B1512355 : Blo 1342990 1512355 := bstep (se 1 (by rfl) ⟨1134266, by rfl⟩ : syracuseStep 1512355 = 2268533) B2268533
theorem B2552867 : Blo 1342990 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B7468081 : Blo 1342990 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B1512499 : Blo 1342990 1512499 := bstep (se 1 (by rfl) ⟨1134374, by rfl⟩ : syracuseStep 1512499 = 2268749) B2268749
theorem B4535405 : Blo 1342990 4535405 := bstep (se 3 (by rfl) ⟨850388, by rfl⟩ : syracuseStep 4535405 = 1700777) B1700777
theorem B1700995 : Blo 1342990 1700995 := bstep (se 1 (by rfl) ⟨1275746, by rfl⟩ : syracuseStep 1700995 = 2551493) B2551493
theorem B4535459 : Blo 1342990 4535459 := bstep (se 1 (by rfl) ⟨3401594, by rfl⟩ : syracuseStep 4535459 = 6803189) B6803189
theorem B1914035 : Blo 1342990 1914035 := bstep (se 1 (by rfl) ⟨1435526, by rfl⟩ : syracuseStep 1914035 = 2871053) B2871053
theorem B2692291 : Blo 1342990 2692291 := bstep (se 1 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 2692291 = 4038437) B4038437
theorem B1512643 : Blo 1342990 1512643 := bstep (se 1 (by rfl) ⟨1134482, by rfl⟩ : syracuseStep 1512643 = 2268965) B2268965
theorem B2266339 : Blo 1342990 2266339 := bstep (se 1 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 2266339 = 3399509) B3399509
theorem B1701091 : Blo 1342990 1701091 := bstep (se 1 (by rfl) ⟨1275818, by rfl⟩ : syracuseStep 1701091 = 2551637) B2551637
theorem B3880163 : Blo 1342990 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B2422019 : Blo 1342990 2422019 := bstep (se 1 (by rfl) ⟨1816514, by rfl⟩ : syracuseStep 2422019 = 3633029) B3633029
theorem B1512787 : Blo 1342990 1512787 := bstep (se 1 (by rfl) ⟨1134590, by rfl⟩ : syracuseStep 1512787 = 2269181) B2269181
theorem B2266481 : Blo 1342990 2266481 := bstep (se 2 (by rfl) ⟨849930, by rfl⟩ : syracuseStep 2266481 = 1699861) B1699861
theorem B4535729 : Blo 1342990 4535729 := bstep (se 2 (by rfl) ⟨1700898, by rfl⟩ : syracuseStep 4535729 = 3401797) B3401797
theorem B5174705 : Blo 1342990 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B1512931 : Blo 1342990 1512931 := bstep (se 1 (by rfl) ⟨1134698, by rfl⟩ : syracuseStep 1512931 = 2269397) B2269397
theorem B2266609 : Blo 1342990 2266609 := bstep (se 2 (by rfl) ⟨849978, by rfl⟩ : syracuseStep 2266609 = 1699957) B1699957
theorem B2266643 : Blo 1342990 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B2152003 : Blo 1342990 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B1513075 : Blo 1342990 1513075 := bstep (se 1 (by rfl) ⟨1134806, by rfl⟩ : syracuseStep 1513075 = 2269613) B2269613
theorem B6805133 : Blo 1342990 6805133 := bstep (se 3 (by rfl) ⟨1275962, by rfl⟩ : syracuseStep 6805133 = 2551925) B2551925
theorem B2266771 : Blo 1342990 2266771 := bstep (se 1 (by rfl) ⟨1700078, by rfl⟩ : syracuseStep 2266771 = 3400157) B3400157
theorem B9950917 : Blo 1342990 9950917 := bstep (se 4 (by rfl) ⟨932898, by rfl⟩ : syracuseStep 9950917 = 1865797) B1865797
theorem B1701587 : Blo 1342990 1701587 := bstep (se 1 (by rfl) ⟨1276190, by rfl⟩ : syracuseStep 1701587 = 2552381) B2552381
theorem B2266913 : Blo 1342990 2266913 := bstep (se 2 (by rfl) ⟨850092, by rfl⟩ : syracuseStep 2266913 = 1700185) B1700185
theorem B1914673 : Blo 1342990 1914673 := bstep (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) B1436005
theorem B2152259 : Blo 1342990 2152259 := bstep (se 1 (by rfl) ⟨1614194, by rfl⟩ : syracuseStep 2152259 = 3228389) B3228389
theorem B10205027 : Blo 1342990 10205027 := bstep (se 1 (by rfl) ⟨7653770, by rfl⟩ : syracuseStep 10205027 = 15307541) B15307541
theorem B19363697 : Blo 1342990 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B2267041 : Blo 1342990 2267041 := bstep (se 2 (by rfl) ⟨850140, by rfl⟩ : syracuseStep 2267041 = 1700281) B1700281
theorem B1914787 : Blo 1342990 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B5740465 : Blo 1342990 5740465 := bstep (se 2 (by rfl) ⟨2152674, by rfl⟩ : syracuseStep 5740465 = 4305349) B4305349
theorem B2267075 : Blo 1342990 2267075 := bstep (se 1 (by rfl) ⟨1700306, by rfl⟩ : syracuseStep 2267075 = 3400613) B3400613
theorem B4536269 : Blo 1342990 4536269 := bstep (se 3 (by rfl) ⟨850550, by rfl⟩ : syracuseStep 4536269 = 1701101) B1701101
theorem B3635171 : Blo 1342990 3635171 := bstep (se 1 (by rfl) ⟨2726378, by rfl⟩ : syracuseStep 3635171 = 5452757) B5452757
theorem B4536323 : Blo 1342990 4536323 := bstep (se 1 (by rfl) ⟨3402242, by rfl⟩ : syracuseStep 4536323 = 6804485) B6804485
theorem B14718989 : Blo 1342990 14718989 := bstep (se 3 (by rfl) ⟨2759810, by rfl⟩ : syracuseStep 14718989 = 5519621) B5519621
theorem B2267203 : Blo 1342990 2267203 := bstep (se 1 (by rfl) ⟨1700402, by rfl⟩ : syracuseStep 2267203 = 3400805) B3400805
theorem B2267345 : Blo 1342990 2267345 := bstep (se 2 (by rfl) ⟨850254, by rfl⟩ : syracuseStep 2267345 = 1700509) B1700509
theorem B4536593 : Blo 1342990 4536593 := bstep (se 2 (by rfl) ⟨1701222, by rfl⟩ : syracuseStep 4536593 = 3402445) B3402445
theorem B2267473 : Blo 1342990 2267473 := bstep (se 2 (by rfl) ⟨850302, by rfl⟩ : syracuseStep 2267473 = 1700605) B1700605
theorem B2300257 : Blo 1342990 2300257 := bstep (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) B1725193
theorem B7756145 : Blo 1342990 7756145 := bstep (se 2 (by rfl) ⟨2908554, by rfl⟩ : syracuseStep 7756145 = 5817109) B5817109
theorem B5101937 : Blo 1342990 5101937 := bstep (se 2 (by rfl) ⟨1913226, by rfl⟩ : syracuseStep 5101937 = 3826453) B3826453
theorem B2267507 : Blo 1342990 2267507 := bstep (se 1 (by rfl) ⟨1700630, by rfl⟩ : syracuseStep 2267507 = 3401261) B3401261
theorem B2267635 : Blo 1342990 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B2267777 : Blo 1342990 2267777 := bstep (se 2 (by rfl) ⟨850416, by rfl⟩ : syracuseStep 2267777 = 1700833) B1700833
theorem B2267905 : Blo 1342990 2267905 := bstep (se 2 (by rfl) ⟨850464, by rfl⟩ : syracuseStep 2267905 = 1700929) B1700929
theorem B2153233 : Blo 1342990 2153233 := bstep (se 2 (by rfl) ⟨807462, by rfl⟩ : syracuseStep 2153233 = 1614925) B1614925
theorem B2267939 : Blo 1342990 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B4537133 : Blo 1342990 4537133 := bstep (se 3 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 4537133 = 1701425) B1701425
theorem B4537187 : Blo 1342990 4537187 := bstep (se 1 (by rfl) ⟨3402890, by rfl⟩ : syracuseStep 4537187 = 6805781) B6805781
theorem B16169827 : Blo 1342990 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B8608625 : Blo 1342990 8608625 := bstep (se 2 (by rfl) ⟨3228234, by rfl⟩ : syracuseStep 8608625 = 6456469) B6456469
theorem B3021731 : Blo 1342990 3021731 := bstep (se 1 (by rfl) ⟨2266298, by rfl⟩ : syracuseStep 3021731 = 4532597) B4532597
theorem B2268067 : Blo 1342990 2268067 := bstep (se 1 (by rfl) ⟨1701050, by rfl⟩ : syracuseStep 2268067 = 3402101) B3402101
theorem B8616901 : Blo 1342990 8616901 := bstep (se 4 (by rfl) ⟨807834, by rfl⟩ : syracuseStep 8616901 = 1615669) B1615669
theorem B2587601 : Blo 1342990 2587601 := bstep (se 2 (by rfl) ⟨970350, by rfl⟩ : syracuseStep 2587601 = 1940701) B1940701
theorem B3824653 : Blo 1342990 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B7658509 : Blo 1342990 7658509 := bstep (se 3 (by rfl) ⟨1435970, by rfl⟩ : syracuseStep 7658509 = 2871941) B2871941
theorem B2268209 : Blo 1342990 2268209 := bstep (se 2 (by rfl) ⟨850578, by rfl⟩ : syracuseStep 2268209 = 1701157) B1701157
theorem B4537457 : Blo 1342990 4537457 := bstep (se 2 (by rfl) ⟨1701546, by rfl⟩ : syracuseStep 4537457 = 3403093) B3403093
theorem B3824813 : Blo 1342990 3824813 := bstep (se 3 (by rfl) ⟨717152, by rfl⟩ : syracuseStep 3824813 = 1434305) B1434305
theorem B3022001 : Blo 1342990 3022001 := bstep (se 2 (by rfl) ⟨1133250, by rfl⟩ : syracuseStep 3022001 = 2266501) B2266501
theorem B2268337 : Blo 1342990 2268337 := bstep (se 2 (by rfl) ⟨850626, by rfl⟩ : syracuseStep 2268337 = 1701253) B1701253
theorem B3022019 : Blo 1342990 3022019 := bstep (se 1 (by rfl) ⟨2266514, by rfl⟩ : syracuseStep 3022019 = 4533029) B4533029
theorem B2268371 : Blo 1342990 2268371 := bstep (se 1 (by rfl) ⟨1701278, by rfl⟩ : syracuseStep 2268371 = 3402557) B3402557
theorem B4144355 : Blo 1342990 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B4365571 : Blo 1342990 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B2014499 : Blo 1342990 2014499 := bstep (se 1 (by rfl) ⟨1510874, by rfl⟩ : syracuseStep 2014499 = 3021749) B3021749
theorem B2014529 : Blo 1342990 2014529 := bstep (se 2 (by rfl) ⟨755448, by rfl⟩ : syracuseStep 2014529 = 1510897) B1510897
theorem B2014547 : Blo 1342990 2014547 := bstep (se 1 (by rfl) ⟨1510910, by rfl⟩ : syracuseStep 2014547 = 3021821) B3021821
theorem B2268499 : Blo 1342990 2268499 := bstep (se 1 (by rfl) ⟨1701374, by rfl⟩ : syracuseStep 2268499 = 3402749) B3402749
theorem B3824995 : Blo 1342990 3824995 := bstep (se 1 (by rfl) ⟨2868746, by rfl⟩ : syracuseStep 3824995 = 5737493) B5737493
theorem B2014577 : Blo 1342990 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B2014595 : Blo 1342990 2014595 := bstep (se 1 (by rfl) ⟨1510946, by rfl⟩ : syracuseStep 2014595 = 3021893) B3021893
theorem B2014625 : Blo 1342990 2014625 := bstep (se 2 (by rfl) ⟨755484, by rfl⟩ : syracuseStep 2014625 = 1510969) B1510969
theorem B2014643 : Blo 1342990 2014643 := bstep (se 1 (by rfl) ⟨1510982, by rfl⟩ : syracuseStep 2014643 = 3021965) B3021965
theorem B2014673 : Blo 1342990 2014673 := bstep (se 2 (by rfl) ⟨755502, by rfl⟩ : syracuseStep 2014673 = 1511005) B1511005
theorem B3022289 : Blo 1342990 3022289 := bstep (se 2 (by rfl) ⟨1133358, by rfl⟩ : syracuseStep 3022289 = 2266717) B2266717
theorem B2268641 : Blo 1342990 2268641 := bstep (se 2 (by rfl) ⟨850740, by rfl⟩ : syracuseStep 2268641 = 1701481) B1701481
theorem B2014691 : Blo 1342990 2014691 := bstep (se 1 (by rfl) ⟨1511018, by rfl⟩ : syracuseStep 2014691 = 3022037) B3022037
theorem B3022307 : Blo 1342990 3022307 := bstep (se 1 (by rfl) ⟨2266730, by rfl⟩ : syracuseStep 3022307 = 4533461) B4533461
theorem B2014721 : Blo 1342990 2014721 := bstep (se 2 (by rfl) ⟨755520, by rfl⟩ : syracuseStep 2014721 = 1511041) B1511041
theorem B1342995 : Blo 1342990 1342995 := bstep (se 1 (by rfl) ⟨1007246, by rfl⟩ : syracuseStep 1342995 = 2014493) B2014493
theorem B2014739 : Blo 1342990 2014739 := bstep (se 1 (by rfl) ⟨1511054, by rfl⟩ : syracuseStep 2014739 = 3022109) B3022109
theorem B1343011 : Blo 1342990 1343011 := bstep (se 1 (by rfl) ⟨1007258, by rfl⟩ : syracuseStep 1343011 = 2014517) B2014517
theorem B2014769 : Blo 1342990 2014769 := bstep (se 2 (by rfl) ⟨755538, by rfl⟩ : syracuseStep 2014769 = 1511077) B1511077
theorem B1343027 : Blo 1342990 1343027 := bstep (se 1 (by rfl) ⟨1007270, by rfl⟩ : syracuseStep 1343027 = 2014541) B2014541
theorem B1343043 : Blo 1342990 1343043 := bstep (se 1 (by rfl) ⟨1007282, by rfl⟩ : syracuseStep 1343043 = 2014565) B2014565
theorem B2014787 : Blo 1342990 2014787 := bstep (se 1 (by rfl) ⟨1511090, by rfl⟩ : syracuseStep 2014787 = 3022181) B3022181
theorem B17219141 : Blo 1342990 17219141 := bstep (se 4 (by rfl) ⟨1614294, by rfl⟩ : syracuseStep 17219141 = 3228589) B3228589
theorem B1343059 : Blo 1342990 1343059 := bstep (se 1 (by rfl) ⟨1007294, by rfl⟩ : syracuseStep 1343059 = 2014589) B2014589
theorem B2014817 : Blo 1342990 2014817 := bstep (se 2 (by rfl) ⟨755556, by rfl⟩ : syracuseStep 2014817 = 1511113) B1511113
theorem B1343075 : Blo 1342990 1343075 := bstep (se 1 (by rfl) ⟨1007306, by rfl⟩ : syracuseStep 1343075 = 2014613) B2014613
theorem B2268769 : Blo 1342990 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B1343091 : Blo 1342990 1343091 := bstep (se 1 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 1343091 = 2014637) B2014637
theorem B2014835 : Blo 1342990 2014835 := bstep (se 1 (by rfl) ⟨1511126, by rfl⟩ : syracuseStep 2014835 = 3022253) B3022253
theorem B1343107 : Blo 1342990 1343107 := bstep (se 1 (by rfl) ⟨1007330, by rfl⟩ : syracuseStep 1343107 = 2014661) B2014661
theorem B2268803 : Blo 1342990 2268803 := bstep (se 1 (by rfl) ⟨1701602, by rfl⟩ : syracuseStep 2268803 = 3403205) B3403205
theorem B4537997 : Blo 1342990 4537997 := bstep (se 3 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 4537997 = 1701749) B1701749
theorem B2014865 : Blo 1342990 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1343123 : Blo 1342990 1343123 := bstep (se 1 (by rfl) ⟨1007342, by rfl⟩ : syracuseStep 1343123 = 2014685) B2014685
theorem B1343139 : Blo 1342990 1343139 := bstep (se 1 (by rfl) ⟨1007354, by rfl⟩ : syracuseStep 1343139 = 2014709) B2014709
theorem B2014883 : Blo 1342990 2014883 := bstep (se 1 (by rfl) ⟨1511162, by rfl⟩ : syracuseStep 2014883 = 3022325) B3022325
theorem B2154161 : Blo 1342990 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B1343155 : Blo 1342990 1343155 := bstep (se 1 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 1343155 = 2014733) B2014733
theorem B2014913 : Blo 1342990 2014913 := bstep (se 2 (by rfl) ⟨755592, by rfl⟩ : syracuseStep 2014913 = 1511185) B1511185
theorem B1343171 : Blo 1342990 1343171 := bstep (se 1 (by rfl) ⟨1007378, by rfl⟩ : syracuseStep 1343171 = 2014757) B2014757
theorem B4538051 : Blo 1342990 4538051 := bstep (se 1 (by rfl) ⟨3403538, by rfl⟩ : syracuseStep 4538051 = 6807077) B6807077
theorem B1343187 : Blo 1342990 1343187 := bstep (se 1 (by rfl) ⟨1007390, by rfl⟩ : syracuseStep 1343187 = 2014781) B2014781
theorem B2014931 : Blo 1342990 2014931 := bstep (se 1 (by rfl) ⟨1511198, by rfl⟩ : syracuseStep 2014931 = 3022397) B3022397
theorem B1343203 : Blo 1342990 1343203 := bstep (se 1 (by rfl) ⟨1007402, by rfl⟩ : syracuseStep 1343203 = 2014805) B2014805
theorem B2014961 : Blo 1342990 2014961 := bstep (se 2 (by rfl) ⟨755610, by rfl⟩ : syracuseStep 2014961 = 1511221) B1511221
theorem B3022577 : Blo 1342990 3022577 := bstep (se 2 (by rfl) ⟨1133466, by rfl⟩ : syracuseStep 3022577 = 2266933) B2266933
theorem B1343219 : Blo 1342990 1343219 := bstep (se 1 (by rfl) ⟨1007414, by rfl⟩ : syracuseStep 1343219 = 2014829) B2014829
theorem B1343235 : Blo 1342990 1343235 := bstep (se 1 (by rfl) ⟨1007426, by rfl⟩ : syracuseStep 1343235 = 2014853) B2014853
theorem B2014979 : Blo 1342990 2014979 := bstep (se 1 (by rfl) ⟨1511234, by rfl⟩ : syracuseStep 2014979 = 3022469) B3022469
theorem B3022595 : Blo 1342990 3022595 := bstep (se 1 (by rfl) ⟨2266946, by rfl⟩ : syracuseStep 3022595 = 4533893) B4533893
theorem B2268931 : Blo 1342990 2268931 := bstep (se 1 (by rfl) ⟨1701698, by rfl⟩ : syracuseStep 2268931 = 3403397) B3403397
theorem B1343251 : Blo 1342990 1343251 := bstep (se 1 (by rfl) ⟨1007438, by rfl⟩ : syracuseStep 1343251 = 2014877) B2014877
theorem B2015009 : Blo 1342990 2015009 := bstep (se 2 (by rfl) ⟨755628, by rfl⟩ : syracuseStep 2015009 = 1511257) B1511257
theorem B6799139 : Blo 1342990 6799139 := bstep (se 1 (by rfl) ⟨5099354, by rfl⟩ : syracuseStep 6799139 = 10198709) B10198709
theorem B1343267 : Blo 1342990 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B5103395 : Blo 1342990 5103395 := bstep (se 1 (by rfl) ⟨3827546, by rfl⟩ : syracuseStep 5103395 = 7655093) B7655093
theorem B4308785 : Blo 1342990 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B1343283 : Blo 1342990 1343283 := bstep (se 1 (by rfl) ⟨1007462, by rfl⟩ : syracuseStep 1343283 = 2014925) B2014925
theorem B2015027 : Blo 1342990 2015027 := bstep (se 1 (by rfl) ⟨1511270, by rfl⟩ : syracuseStep 2015027 = 3022541) B3022541
theorem B1343299 : Blo 1342990 1343299 := bstep (se 1 (by rfl) ⟨1007474, by rfl⟩ : syracuseStep 1343299 = 2014949) B2014949
theorem B2015057 : Blo 1342990 2015057 := bstep (se 2 (by rfl) ⟨755646, by rfl⟩ : syracuseStep 2015057 = 1511293) B1511293
theorem B1343315 : Blo 1342990 1343315 := bstep (se 1 (by rfl) ⟨1007486, by rfl⟩ : syracuseStep 1343315 = 2014973) B2014973
theorem B1343331 : Blo 1342990 1343331 := bstep (se 1 (by rfl) ⟨1007498, by rfl⟩ : syracuseStep 1343331 = 2014997) B2014997
theorem B2015075 : Blo 1342990 2015075 := bstep (se 1 (by rfl) ⟨1511306, by rfl⟩ : syracuseStep 2015075 = 3022613) B3022613
theorem B1343347 : Blo 1342990 1343347 := bstep (se 1 (by rfl) ⟨1007510, by rfl⟩ : syracuseStep 1343347 = 2015021) B2015021
theorem B2015105 : Blo 1342990 2015105 := bstep (se 2 (by rfl) ⟨755664, by rfl⟩ : syracuseStep 2015105 = 1511329) B1511329
theorem B1343363 : Blo 1342990 1343363 := bstep (se 1 (by rfl) ⟨1007522, by rfl⟩ : syracuseStep 1343363 = 2015045) B2015045
theorem B2269073 : Blo 1342990 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B1343379 : Blo 1342990 1343379 := bstep (se 1 (by rfl) ⟨1007534, by rfl⟩ : syracuseStep 1343379 = 2015069) B2015069
theorem B2015123 : Blo 1342990 2015123 := bstep (se 1 (by rfl) ⟨1511342, by rfl⟩ : syracuseStep 2015123 = 3022685) B3022685
theorem B1343395 : Blo 1342990 1343395 := bstep (se 1 (by rfl) ⟨1007546, by rfl⟩ : syracuseStep 1343395 = 2015093) B2015093
theorem B2015153 : Blo 1342990 2015153 := bstep (se 2 (by rfl) ⟨755682, by rfl⟩ : syracuseStep 2015153 = 1511365) B1511365
theorem B1343411 : Blo 1342990 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B1343427 : Blo 1342990 1343427 := bstep (se 1 (by rfl) ⟨1007570, by rfl⟩ : syracuseStep 1343427 = 2015141) B2015141
theorem B2015171 : Blo 1342990 2015171 := bstep (se 1 (by rfl) ⟨1511378, by rfl⟩ : syracuseStep 2015171 = 3022757) B3022757
theorem B4538321 : Blo 1342990 4538321 := bstep (se 2 (by rfl) ⟨1701870, by rfl⟩ : syracuseStep 4538321 = 3403741) B3403741
theorem B1343443 : Blo 1342990 1343443 := bstep (se 1 (by rfl) ⟨1007582, by rfl⟩ : syracuseStep 1343443 = 2015165) B2015165
theorem B2015201 : Blo 1342990 2015201 := bstep (se 2 (by rfl) ⟨755700, by rfl⟩ : syracuseStep 2015201 = 1511401) B1511401
theorem B1343459 : Blo 1342990 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B6897635 : Blo 1342990 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B1343475 : Blo 1342990 1343475 := bstep (se 1 (by rfl) ⟨1007606, by rfl⟩ : syracuseStep 1343475 = 2015213) B2015213
theorem B2015219 : Blo 1342990 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B2015243 : Blo 1342990 2015243 := bstep (se 1 (by rfl) ⟨1511432, by rfl⟩ : syracuseStep 2015243 = 3022865) B3022865
theorem B1343499 : Blo 1342990 1343499 := bstep (se 1 (by rfl) ⟨1007624, by rfl⟩ : syracuseStep 1343499 = 2015249) B2015249
theorem B2015255 : Blo 1342990 2015255 := bstep (se 1 (by rfl) ⟨1511441, by rfl⟩ : syracuseStep 2015255 = 3022883) B3022883
theorem B1343511 : Blo 1342990 1343511 := bstep (se 1 (by rfl) ⟨1007633, by rfl⟩ : syracuseStep 1343511 = 2015267) B2015267
theorem B1343531 : Blo 1342990 1343531 := bstep (se 1 (by rfl) ⟨1007648, by rfl⟩ : syracuseStep 1343531 = 2015297) B2015297
theorem B1343543 : Blo 1342990 1343543 := bstep (se 1 (by rfl) ⟨1007657, by rfl⟩ : syracuseStep 1343543 = 2015315) B2015315
theorem B1343563 : Blo 1342990 1343563 := bstep (se 1 (by rfl) ⟨1007672, by rfl⟩ : syracuseStep 1343563 = 2015345) B2015345
theorem B1343575 : Blo 1342990 1343575 := bstep (se 1 (by rfl) ⟨1007681, by rfl⟩ : syracuseStep 1343575 = 2015363) B2015363
theorem B3022937 : Blo 1342990 3022937 := bstep (se 2 (by rfl) ⟨1133601, by rfl⟩ : syracuseStep 3022937 = 2267203) B2267203
theorem B2015321 : Blo 1342990 2015321 := bstep (se 2 (by rfl) ⟨755745, by rfl⟩ : syracuseStep 2015321 = 1511491) B1511491
theorem B1343595 : Blo 1342990 1343595 := bstep (se 1 (by rfl) ⟨1007696, by rfl⟩ : syracuseStep 1343595 = 2015393) B2015393
theorem B1343607 : Blo 1342990 1343607 := bstep (se 1 (by rfl) ⟨1007705, by rfl⟩ : syracuseStep 1343607 = 2015411) B2015411
theorem B1343627 : Blo 1342990 1343627 := bstep (se 1 (by rfl) ⟨1007720, by rfl⟩ : syracuseStep 1343627 = 2015441) B2015441
theorem B1343639 : Blo 1342990 1343639 := bstep (se 1 (by rfl) ⟨1007729, by rfl⟩ : syracuseStep 1343639 = 2015459) B2015459
theorem B1343659 : Blo 1342990 1343659 := bstep (se 1 (by rfl) ⟨1007744, by rfl⟩ : syracuseStep 1343659 = 2015489) B2015489
theorem B3023027 : Blo 1342990 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B1343671 : Blo 1342990 1343671 := bstep (se 1 (by rfl) ⟨1007753, by rfl⟩ : syracuseStep 1343671 = 2015507) B2015507
theorem B2015435 : Blo 1342990 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem B1343691 : Blo 1342990 1343691 := bstep (se 1 (by rfl) ⟨1007768, by rfl⟩ : syracuseStep 1343691 = 2015537) B2015537
theorem B1532119 : Blo 1342990 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B3023063 : Blo 1342990 3023063 := bstep (se 1 (by rfl) ⟨2267297, by rfl⟩ : syracuseStep 3023063 = 4534595) B4534595
theorem B2015447 : Blo 1342990 2015447 := bstep (se 1 (by rfl) ⟨1511585, by rfl⟩ : syracuseStep 2015447 = 3023171) B3023171
theorem B1343703 : Blo 1342990 1343703 := bstep (se 1 (by rfl) ⟨1007777, by rfl⟩ : syracuseStep 1343703 = 2015555) B2015555
theorem B1343723 : Blo 1342990 1343723 := bstep (se 1 (by rfl) ⟨1007792, by rfl⟩ : syracuseStep 1343723 = 2015585) B2015585
theorem B1343735 : Blo 1342990 1343735 := bstep (se 1 (by rfl) ⟨1007801, by rfl⟩ : syracuseStep 1343735 = 2015603) B2015603
theorem B39829765 : Blo 1342990 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B1343755 : Blo 1342990 1343755 := bstep (se 1 (by rfl) ⟨1007816, by rfl⟩ : syracuseStep 1343755 = 2015633) B2015633
theorem B2269451 : Blo 1342990 2269451 := bstep (se 1 (by rfl) ⟨1702088, by rfl⟩ : syracuseStep 2269451 = 3404177) B3404177
theorem B9814289 : Blo 1342990 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B1343767 : Blo 1342990 1343767 := bstep (se 1 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 1343767 = 2015651) B2015651
theorem B2015513 : Blo 1342990 2015513 := bstep (se 2 (by rfl) ⟨755817, by rfl⟩ : syracuseStep 2015513 = 1511635) B1511635
theorem B1343787 : Blo 1342990 1343787 := bstep (se 1 (by rfl) ⟨1007840, by rfl⟩ : syracuseStep 1343787 = 2015681) B2015681
theorem B1343799 : Blo 1342990 1343799 := bstep (se 1 (by rfl) ⟨1007849, by rfl⟩ : syracuseStep 1343799 = 2015699) B2015699
theorem B1343819 : Blo 1342990 1343819 := bstep (se 1 (by rfl) ⟨1007864, by rfl⟩ : syracuseStep 1343819 = 2015729) B2015729
theorem B4538699 : Blo 1342990 4538699 := bstep (se 1 (by rfl) ⟨3404024, by rfl⟩ : syracuseStep 4538699 = 6808049) B6808049
theorem B1343831 : Blo 1342990 1343831 := bstep (se 1 (by rfl) ⟨1007873, by rfl⟩ : syracuseStep 1343831 = 2015747) B2015747
theorem B1343851 : Blo 1342990 1343851 := bstep (se 1 (by rfl) ⟨1007888, by rfl⟩ : syracuseStep 1343851 = 2015777) B2015777
theorem B1343863 : Blo 1342990 1343863 := bstep (se 1 (by rfl) ⟨1007897, by rfl⟩ : syracuseStep 1343863 = 2015795) B2015795
theorem B3023243 : Blo 1342990 3023243 := bstep (se 1 (by rfl) ⟨2267432, by rfl⟩ : syracuseStep 3023243 = 4534865) B4534865
theorem B2015627 : Blo 1342990 2015627 := bstep (se 1 (by rfl) ⟨1511720, by rfl⟩ : syracuseStep 2015627 = 3023441) B3023441
theorem B1343883 : Blo 1342990 1343883 := bstep (se 1 (by rfl) ⟨1007912, by rfl⟩ : syracuseStep 1343883 = 2015825) B2015825
theorem B2269579 : Blo 1342990 2269579 := bstep (se 1 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 2269579 = 3404369) B3404369
theorem B2015639 : Blo 1342990 2015639 := bstep (se 1 (by rfl) ⟨1511729, by rfl⟩ : syracuseStep 2015639 = 3023459) B3023459
theorem B1343895 : Blo 1342990 1343895 := bstep (se 1 (by rfl) ⟨1007921, by rfl⟩ : syracuseStep 1343895 = 2015843) B2015843
theorem B1343915 : Blo 1342990 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B1343927 : Blo 1342990 1343927 := bstep (se 1 (by rfl) ⟨1007945, by rfl⟩ : syracuseStep 1343927 = 2015891) B2015891
theorem B3023297 : Blo 1342990 3023297 := bstep (se 2 (by rfl) ⟨1133736, by rfl⟩ : syracuseStep 3023297 = 2267473) B2267473
theorem B1343947 : Blo 1342990 1343947 := bstep (se 1 (by rfl) ⟨1007960, by rfl⟩ : syracuseStep 1343947 = 2015921) B2015921
theorem B1343959 : Blo 1342990 1343959 := bstep (se 1 (by rfl) ⟨1007969, by rfl⟩ : syracuseStep 1343959 = 2015939) B2015939
theorem B2015705 : Blo 1342990 2015705 := bstep (se 2 (by rfl) ⟨755889, by rfl⟩ : syracuseStep 2015705 = 1511779) B1511779
theorem B5104093 : Blo 1342990 5104093 := bstep (se 3 (by rfl) ⟨957017, by rfl⟩ : syracuseStep 5104093 = 1914035) B1914035
theorem B1343979 : Blo 1342990 1343979 := bstep (se 1 (by rfl) ⟨1007984, by rfl⟩ : syracuseStep 1343979 = 2015969) B2015969
theorem B1343991 : Blo 1342990 1343991 := bstep (se 1 (by rfl) ⟨1007993, by rfl⟩ : syracuseStep 1343991 = 2015987) B2015987
theorem B1344011 : Blo 1342990 1344011 := bstep (se 1 (by rfl) ⟨1008008, by rfl⟩ : syracuseStep 1344011 = 2016017) B2016017
theorem B1344023 : Blo 1342990 1344023 := bstep (se 1 (by rfl) ⟨1008017, by rfl⟩ : syracuseStep 1344023 = 2016035) B2016035
theorem B1344043 : Blo 1342990 1344043 := bstep (se 1 (by rfl) ⟨1008032, by rfl⟩ : syracuseStep 1344043 = 2016065) B2016065
theorem B1344055 : Blo 1342990 1344055 := bstep (se 1 (by rfl) ⟨1008041, by rfl⟩ : syracuseStep 1344055 = 2016083) B2016083
theorem B2015819 : Blo 1342990 2015819 := bstep (se 1 (by rfl) ⟨1511864, by rfl⟩ : syracuseStep 2015819 = 3023729) B3023729
theorem B1344075 : Blo 1342990 1344075 := bstep (se 1 (by rfl) ⟨1008056, by rfl⟩ : syracuseStep 1344075 = 2016113) B2016113
theorem B2015831 : Blo 1342990 2015831 := bstep (se 1 (by rfl) ⟨1511873, by rfl⟩ : syracuseStep 2015831 = 3023747) B3023747
theorem B1344087 : Blo 1342990 1344087 := bstep (se 1 (by rfl) ⟨1008065, by rfl⟩ : syracuseStep 1344087 = 2016131) B2016131
theorem B4538969 : Blo 1342990 4538969 := bstep (se 2 (by rfl) ⟨1702113, by rfl⟩ : syracuseStep 4538969 = 3404227) B3404227
theorem B1344107 : Blo 1342990 1344107 := bstep (se 1 (by rfl) ⟨1008080, by rfl⟩ : syracuseStep 1344107 = 2016161) B2016161
theorem B1344119 : Blo 1342990 1344119 := bstep (se 1 (by rfl) ⟨1008089, by rfl⟩ : syracuseStep 1344119 = 2016179) B2016179
theorem B1344139 : Blo 1342990 1344139 := bstep (se 1 (by rfl) ⟨1008104, by rfl⟩ : syracuseStep 1344139 = 2016209) B2016209
theorem B1344151 : Blo 1342990 1344151 := bstep (se 1 (by rfl) ⟨1008113, by rfl⟩ : syracuseStep 1344151 = 2016227) B2016227
theorem B3023513 : Blo 1342990 3023513 := bstep (se 2 (by rfl) ⟨1133817, by rfl⟩ : syracuseStep 3023513 = 2267635) B2267635
theorem B2015897 : Blo 1342990 2015897 := bstep (se 2 (by rfl) ⟨755961, by rfl⟩ : syracuseStep 2015897 = 1511923) B1511923
theorem B1344171 : Blo 1342990 1344171 := bstep (se 1 (by rfl) ⟨1008128, by rfl⟩ : syracuseStep 1344171 = 2016257) B2016257
theorem B1344183 : Blo 1342990 1344183 := bstep (se 1 (by rfl) ⟨1008137, by rfl⟩ : syracuseStep 1344183 = 2016275) B2016275
theorem B1344203 : Blo 1342990 1344203 := bstep (se 1 (by rfl) ⟨1008152, by rfl⟩ : syracuseStep 1344203 = 2016305) B2016305
theorem B1344215 : Blo 1342990 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B1344235 : Blo 1342990 1344235 := bstep (se 1 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 1344235 = 2016353) B2016353
theorem B3023603 : Blo 1342990 3023603 := bstep (se 1 (by rfl) ⟨2267702, by rfl⟩ : syracuseStep 3023603 = 4535405) B4535405
theorem B1344247 : Blo 1342990 1344247 := bstep (se 1 (by rfl) ⟨1008185, by rfl⟩ : syracuseStep 1344247 = 2016371) B2016371
theorem B2016011 : Blo 1342990 2016011 := bstep (se 1 (by rfl) ⟨1512008, by rfl⟩ : syracuseStep 2016011 = 3024017) B3024017
theorem B1344267 : Blo 1342990 1344267 := bstep (se 1 (by rfl) ⟨1008200, by rfl⟩ : syracuseStep 1344267 = 2016401) B2016401
theorem B3023639 : Blo 1342990 3023639 := bstep (se 1 (by rfl) ⟨2267729, by rfl⟩ : syracuseStep 3023639 = 4535459) B4535459
theorem B2016023 : Blo 1342990 2016023 := bstep (se 1 (by rfl) ⟨1512017, by rfl⟩ : syracuseStep 2016023 = 3024035) B3024035
theorem B1344279 : Blo 1342990 1344279 := bstep (se 1 (by rfl) ⟨1008209, by rfl⟩ : syracuseStep 1344279 = 2016419) B2016419
theorem B1344299 : Blo 1342990 1344299 := bstep (se 1 (by rfl) ⟨1008224, by rfl⟩ : syracuseStep 1344299 = 2016449) B2016449
theorem B1344311 : Blo 1342990 1344311 := bstep (se 1 (by rfl) ⟨1008233, by rfl⟩ : syracuseStep 1344311 = 2016467) B2016467
theorem B1344331 : Blo 1342990 1344331 := bstep (se 1 (by rfl) ⟨1008248, by rfl⟩ : syracuseStep 1344331 = 2016497) B2016497
theorem B1344343 : Blo 1342990 1344343 := bstep (se 1 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 1344343 = 2016515) B2016515
theorem B2016089 : Blo 1342990 2016089 := bstep (se 2 (by rfl) ⟨756033, by rfl⟩ : syracuseStep 2016089 = 1512067) B1512067
theorem B4088665 : Blo 1342990 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B22397795 : Blo 1342990 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B1344363 : Blo 1342990 1344363 := bstep (se 1 (by rfl) ⟨1008272, by rfl⟩ : syracuseStep 1344363 = 2016545) B2016545
theorem B1344375 : Blo 1342990 1344375 := bstep (se 1 (by rfl) ⟨1008281, by rfl⟩ : syracuseStep 1344375 = 2016563) B2016563
theorem B1344395 : Blo 1342990 1344395 := bstep (se 1 (by rfl) ⟨1008296, by rfl⟩ : syracuseStep 1344395 = 2016593) B2016593
theorem B5899159 : Blo 1342990 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B1344407 : Blo 1342990 1344407 := bstep (se 1 (by rfl) ⟨1008305, by rfl⟩ : syracuseStep 1344407 = 2016611) B2016611
theorem B1344427 : Blo 1342990 1344427 := bstep (se 1 (by rfl) ⟨1008320, by rfl⟩ : syracuseStep 1344427 = 2016641) B2016641
theorem B1344439 : Blo 1342990 1344439 := bstep (se 1 (by rfl) ⟨1008329, by rfl⟩ : syracuseStep 1344439 = 2016659) B2016659
theorem B3023819 : Blo 1342990 3023819 := bstep (se 1 (by rfl) ⟨2267864, by rfl⟩ : syracuseStep 3023819 = 4535729) B4535729
theorem B2016203 : Blo 1342990 2016203 := bstep (se 1 (by rfl) ⟨1512152, by rfl⟩ : syracuseStep 2016203 = 3024305) B3024305
theorem B1344459 : Blo 1342990 1344459 := bstep (se 1 (by rfl) ⟨1008344, by rfl⟩ : syracuseStep 1344459 = 2016689) B2016689
theorem B3449803 : Blo 1342990 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B2016215 : Blo 1342990 2016215 := bstep (se 1 (by rfl) ⟨1512161, by rfl⟩ : syracuseStep 2016215 = 3024323) B3024323
theorem B1344471 : Blo 1342990 1344471 := bstep (se 1 (by rfl) ⟨1008353, by rfl⟩ : syracuseStep 1344471 = 2016707) B2016707
theorem B1344491 : Blo 1342990 1344491 := bstep (se 1 (by rfl) ⟨1008368, by rfl⟩ : syracuseStep 1344491 = 2016737) B2016737
theorem B1344503 : Blo 1342990 1344503 := bstep (se 1 (by rfl) ⟨1008377, by rfl⟩ : syracuseStep 1344503 = 2016755) B2016755
theorem B3023873 : Blo 1342990 3023873 := bstep (se 2 (by rfl) ⟨1133952, by rfl⟩ : syracuseStep 3023873 = 2267905) B2267905
theorem B1344523 : Blo 1342990 1344523 := bstep (se 1 (by rfl) ⟨1008392, by rfl⟩ : syracuseStep 1344523 = 2016785) B2016785
theorem B1344535 : Blo 1342990 1344535 := bstep (se 1 (by rfl) ⟨1008401, by rfl⟩ : syracuseStep 1344535 = 2016803) B2016803
theorem B2016281 : Blo 1342990 2016281 := bstep (se 2 (by rfl) ⟨756105, by rfl⟩ : syracuseStep 2016281 = 1512211) B1512211
theorem B1344555 : Blo 1342990 1344555 := bstep (se 1 (by rfl) ⟨1008416, by rfl⟩ : syracuseStep 1344555 = 2016833) B2016833
theorem B1344567 : Blo 1342990 1344567 := bstep (se 1 (by rfl) ⟨1008425, by rfl⟩ : syracuseStep 1344567 = 2016851) B2016851
theorem B1344587 : Blo 1342990 1344587 := bstep (se 1 (by rfl) ⟨1008440, by rfl⟩ : syracuseStep 1344587 = 2016881) B2016881
theorem B2868311 : Blo 1342990 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B1344599 : Blo 1342990 1344599 := bstep (se 1 (by rfl) ⟨1008449, by rfl⟩ : syracuseStep 1344599 = 2016899) B2016899
theorem B1344619 : Blo 1342990 1344619 := bstep (se 1 (by rfl) ⟨1008464, by rfl⟩ : syracuseStep 1344619 = 2016929) B2016929
theorem B1344631 : Blo 1342990 1344631 := bstep (se 1 (by rfl) ⟨1008473, by rfl⟩ : syracuseStep 1344631 = 2016947) B2016947
theorem B2016395 : Blo 1342990 2016395 := bstep (se 1 (by rfl) ⟨1512296, by rfl⟩ : syracuseStep 2016395 = 3024593) B3024593
theorem B1344651 : Blo 1342990 1344651 := bstep (se 1 (by rfl) ⟨1008488, by rfl⟩ : syracuseStep 1344651 = 2016977) B2016977
theorem B2016407 : Blo 1342990 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B1344663 : Blo 1342990 1344663 := bstep (se 1 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 1344663 = 2016995) B2016995
theorem B1344683 : Blo 1342990 1344683 := bstep (se 1 (by rfl) ⟨1008512, by rfl⟩ : syracuseStep 1344683 = 2017025) B2017025
theorem B1344695 : Blo 1342990 1344695 := bstep (se 1 (by rfl) ⟨1008521, by rfl⟩ : syracuseStep 1344695 = 2017043) B2017043
theorem B1344715 : Blo 1342990 1344715 := bstep (se 1 (by rfl) ⟨1008536, by rfl⟩ : syracuseStep 1344715 = 2017073) B2017073
theorem B1434839 : Blo 1342990 1434839 := bstep (se 1 (by rfl) ⟨1076129, by rfl⟩ : syracuseStep 1434839 = 2152259) B2152259
theorem B1344727 : Blo 1342990 1344727 := bstep (se 1 (by rfl) ⟨1008545, by rfl⟩ : syracuseStep 1344727 = 2017091) B2017091
theorem B3024089 : Blo 1342990 3024089 := bstep (se 2 (by rfl) ⟨1134033, by rfl⟩ : syracuseStep 3024089 = 2268067) B2268067
theorem B2016473 : Blo 1342990 2016473 := bstep (se 2 (by rfl) ⟨756177, by rfl⟩ : syracuseStep 2016473 = 1512355) B1512355
theorem B1344747 : Blo 1342990 1344747 := bstep (se 1 (by rfl) ⟨1008560, by rfl⟩ : syracuseStep 1344747 = 2017121) B2017121
theorem B1344759 : Blo 1342990 1344759 := bstep (se 1 (by rfl) ⟨1008569, by rfl⟩ : syracuseStep 1344759 = 2017139) B2017139
theorem B1344779 : Blo 1342990 1344779 := bstep (se 1 (by rfl) ⟨1008584, by rfl⟩ : syracuseStep 1344779 = 2017169) B2017169
theorem B1344791 : Blo 1342990 1344791 := bstep (se 1 (by rfl) ⟨1008593, by rfl⟩ : syracuseStep 1344791 = 2017187) B2017187
theorem B1344811 : Blo 1342990 1344811 := bstep (se 1 (by rfl) ⟨1008608, by rfl⟩ : syracuseStep 1344811 = 2017217) B2017217
theorem B11633965 : Blo 1342990 11633965 := bstep (se 3 (by rfl) ⟨2181368, by rfl⟩ : syracuseStep 11633965 = 4362737) B4362737
theorem B9684269 : Blo 1342990 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B3024179 : Blo 1342990 3024179 := bstep (se 1 (by rfl) ⟨2268134, by rfl⟩ : syracuseStep 3024179 = 4536269) B4536269
theorem B1344823 : Blo 1342990 1344823 := bstep (se 1 (by rfl) ⟨1008617, by rfl⟩ : syracuseStep 1344823 = 2017235) B2017235
theorem B2016587 : Blo 1342990 2016587 := bstep (se 1 (by rfl) ⟨1512440, by rfl⟩ : syracuseStep 2016587 = 3024881) B3024881
theorem B1344843 : Blo 1342990 1344843 := bstep (se 1 (by rfl) ⟨1008632, by rfl⟩ : syracuseStep 1344843 = 2017265) B2017265
theorem B3024215 : Blo 1342990 3024215 := bstep (se 1 (by rfl) ⟨2268161, by rfl⟩ : syracuseStep 3024215 = 4536323) B4536323
theorem B2016599 : Blo 1342990 2016599 := bstep (se 1 (by rfl) ⟨1512449, by rfl⟩ : syracuseStep 2016599 = 3024899) B3024899
theorem B1344855 : Blo 1342990 1344855 := bstep (se 1 (by rfl) ⟨1008641, by rfl⟩ : syracuseStep 1344855 = 2017283) B2017283
theorem B1344875 : Blo 1342990 1344875 := bstep (se 1 (by rfl) ⟨1008656, by rfl⟩ : syracuseStep 1344875 = 2017313) B2017313
theorem B1344887 : Blo 1342990 1344887 := bstep (se 1 (by rfl) ⟨1008665, by rfl⟩ : syracuseStep 1344887 = 2017331) B2017331
theorem B1344907 : Blo 1342990 1344907 := bstep (se 1 (by rfl) ⟨1008680, by rfl⟩ : syracuseStep 1344907 = 2017361) B2017361
theorem B1344919 : Blo 1342990 1344919 := bstep (se 1 (by rfl) ⟨1008689, by rfl⟩ : syracuseStep 1344919 = 2017379) B2017379
theorem B2016665 : Blo 1342990 2016665 := bstep (se 2 (by rfl) ⟨756249, by rfl⟩ : syracuseStep 2016665 = 1512499) B1512499
theorem B1344939 : Blo 1342990 1344939 := bstep (se 1 (by rfl) ⟨1008704, by rfl⟩ : syracuseStep 1344939 = 2017409) B2017409
theorem B1344951 : Blo 1342990 1344951 := bstep (se 1 (by rfl) ⟨1008713, by rfl⟩ : syracuseStep 1344951 = 2017427) B2017427
theorem B1344971 : Blo 1342990 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B1344983 : Blo 1342990 1344983 := bstep (se 1 (by rfl) ⟨1008737, by rfl⟩ : syracuseStep 1344983 = 2017475) B2017475
theorem B3024395 : Blo 1342990 3024395 := bstep (se 1 (by rfl) ⟨2268296, by rfl⟩ : syracuseStep 3024395 = 4536593) B4536593
theorem B2016779 : Blo 1342990 2016779 := bstep (se 1 (by rfl) ⟨1512584, by rfl⟩ : syracuseStep 2016779 = 3025169) B3025169
theorem B2016791 : Blo 1342990 2016791 := bstep (se 1 (by rfl) ⟨1512593, by rfl⟩ : syracuseStep 2016791 = 3025187) B3025187
theorem B3024449 : Blo 1342990 3024449 := bstep (se 2 (by rfl) ⟨1134168, by rfl⟩ : syracuseStep 3024449 = 2268337) B2268337
theorem B5170763 : Blo 1342990 5170763 := bstep (se 1 (by rfl) ⟨3878072, by rfl⟩ : syracuseStep 5170763 = 7756145) B7756145
theorem B3401291 : Blo 1342990 3401291 := bstep (se 1 (by rfl) ⟨2550968, by rfl⟩ : syracuseStep 3401291 = 5101937) B5101937
theorem B3589721 : Blo 1342990 3589721 := bstep (se 2 (by rfl) ⟨1346145, by rfl⟩ : syracuseStep 3589721 = 2692291) B2692291
theorem B2016857 : Blo 1342990 2016857 := bstep (se 2 (by rfl) ⟨756321, by rfl⟩ : syracuseStep 2016857 = 1512643) B1512643
theorem B2016971 : Blo 1342990 2016971 := bstep (se 1 (by rfl) ⟨1512728, by rfl⟩ : syracuseStep 2016971 = 3025457) B3025457
theorem B2016983 : Blo 1342990 2016983 := bstep (se 1 (by rfl) ⟨1512737, by rfl⟩ : syracuseStep 2016983 = 3025475) B3025475
theorem B5105369 : Blo 1342990 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B3024665 : Blo 1342990 3024665 := bstep (se 2 (by rfl) ⟨1134249, by rfl⟩ : syracuseStep 3024665 = 2268499) B2268499
theorem B2017049 : Blo 1342990 2017049 := bstep (se 2 (by rfl) ⟨756393, by rfl⟩ : syracuseStep 2017049 = 1512787) B1512787
theorem B5744429 : Blo 1342990 5744429 := bstep (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) B2154161
theorem B6801245 : Blo 1342990 6801245 := bstep (se 3 (by rfl) ⟨1275233, by rfl⟩ : syracuseStep 6801245 = 2550467) B2550467
theorem B3024755 : Blo 1342990 3024755 := bstep (se 1 (by rfl) ⟨2268566, by rfl⟩ : syracuseStep 3024755 = 4537133) B4537133
theorem B2017163 : Blo 1342990 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B3024791 : Blo 1342990 3024791 := bstep (se 1 (by rfl) ⟨2268593, by rfl⟩ : syracuseStep 3024791 = 4537187) B4537187
theorem B2017175 : Blo 1342990 2017175 := bstep (se 1 (by rfl) ⟨1512881, by rfl⟩ : syracuseStep 2017175 = 3025763) B3025763
theorem B15304625 : Blo 1342990 15304625 := bstep (se 2 (by rfl) ⟨5739234, by rfl⟩ : syracuseStep 15304625 = 11478469) B11478469
theorem B1361867 : Blo 1342990 1361867 := bstep (se 1 (by rfl) ⟨1021400, by rfl⟩ : syracuseStep 1361867 = 2042801) B2042801
theorem B2017241 : Blo 1342990 2017241 := bstep (se 2 (by rfl) ⟨756465, by rfl⟩ : syracuseStep 2017241 = 1512931) B1512931
theorem B3065843 : Blo 1342990 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B12257315 : Blo 1342990 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B3631169 : Blo 1342990 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B3024971 : Blo 1342990 3024971 := bstep (se 1 (by rfl) ⟨2268728, by rfl⟩ : syracuseStep 3024971 = 4537457) B4537457
theorem B2017355 : Blo 1342990 2017355 := bstep (se 1 (by rfl) ⟨1513016, by rfl⟩ : syracuseStep 2017355 = 3026033) B3026033
theorem B2017367 : Blo 1342990 2017367 := bstep (se 1 (by rfl) ⟨1513025, by rfl⟩ : syracuseStep 2017367 = 3026051) B3026051
theorem B2869337 : Blo 1342990 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B2549875 : Blo 1342990 2549875 := bstep (se 1 (by rfl) ⟨1912406, by rfl⟩ : syracuseStep 2549875 = 3824813) B3824813
theorem B3025025 : Blo 1342990 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B2762903 : Blo 1342990 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B2017433 : Blo 1342990 2017433 := bstep (se 2 (by rfl) ⟨756537, by rfl⟩ : syracuseStep 2017433 = 1513075) B1513075
theorem B5736707 : Blo 1342990 5736707 := bstep (se 1 (by rfl) ⟨4302530, by rfl⟩ : syracuseStep 5736707 = 8605061) B8605061
theorem B3025241 : Blo 1342990 3025241 := bstep (se 2 (by rfl) ⟨1134465, by rfl⟩ : syracuseStep 3025241 = 2268931) B2268931
theorem B11479427 : Blo 1342990 11479427 := bstep (se 1 (by rfl) ⟨8609570, by rfl⟩ : syracuseStep 11479427 = 17219141) B17219141
theorem B3025331 : Blo 1342990 3025331 := bstep (se 1 (by rfl) ⟨2268998, by rfl⟩ : syracuseStep 3025331 = 4537997) B4537997
theorem B3828161 : Blo 1342990 3828161 := bstep (se 2 (by rfl) ⟨1435560, by rfl⟩ : syracuseStep 3828161 = 2871121) B2871121
theorem B3025367 : Blo 1342990 3025367 := bstep (se 1 (by rfl) ⟨2269025, by rfl⟩ : syracuseStep 3025367 = 4538051) B4538051
theorem B3828185 : Blo 1342990 3828185 := bstep (se 2 (by rfl) ⟨1435569, by rfl⟩ : syracuseStep 3828185 = 2871139) B2871139
theorem B4532759 : Blo 1342990 4532759 := bstep (se 1 (by rfl) ⟨3399569, by rfl⟩ : syracuseStep 4532759 = 6799139) B6799139
theorem B3402263 : Blo 1342990 3402263 := bstep (se 1 (by rfl) ⟨2551697, by rfl⟩ : syracuseStep 3402263 = 5103395) B5103395
theorem B7653953 : Blo 1342990 7653953 := bstep (se 2 (by rfl) ⟨2870232, by rfl⟩ : syracuseStep 7653953 = 5740465) B5740465
theorem B16566859 : Blo 1342990 16566859 := bstep (se 1 (by rfl) ⟨12425144, by rfl⟩ : syracuseStep 16566859 = 24850289) B24850289
theorem B2550361 : Blo 1342990 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B3025547 : Blo 1342990 3025547 := bstep (se 1 (by rfl) ⟨2269160, by rfl⟩ : syracuseStep 3025547 = 4538321) B4538321
theorem B9685655 : Blo 1342990 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B4598423 : Blo 1342990 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B3025601 : Blo 1342990 3025601 := bstep (se 2 (by rfl) ⟨1134600, by rfl⟩ : syracuseStep 3025601 = 2269201) B2269201
theorem B6458177 : Blo 1342990 6458177 := bstep (se 2 (by rfl) ⟨2421816, by rfl⟩ : syracuseStep 6458177 = 4843633) B4843633
theorem B4303709 : Blo 1342990 4303709 := bstep (se 3 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 4303709 = 1613891) B1613891
theorem B3025817 : Blo 1342990 3025817 := bstep (se 2 (by rfl) ⟨1134681, by rfl⟩ : syracuseStep 3025817 = 2269363) B2269363
theorem B40381361 : Blo 1342990 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B100797401 : Blo 1342990 100797401 := bstep (se 2 (by rfl) ⟨37799025, by rfl⟩ : syracuseStep 100797401 = 75598051) B75598051
theorem B3025907 : Blo 1342990 3025907 := bstep (se 1 (by rfl) ⟨2269430, by rfl⟩ : syracuseStep 3025907 = 4538861) B4538861
theorem B3025943 : Blo 1342990 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B4533299 : Blo 1342990 4533299 := bstep (se 1 (by rfl) ⟨3399974, by rfl⟩ : syracuseStep 4533299 = 6799949) B6799949
theorem B2870387 : Blo 1342990 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B2550923 : Blo 1342990 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B3402931 : Blo 1342990 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B3026123 : Blo 1342990 3026123 := bstep (se 1 (by rfl) ⟨2269592, by rfl⟩ : syracuseStep 3026123 = 4539185) B4539185
theorem B3026177 : Blo 1342990 3026177 := bstep (se 2 (by rfl) ⟨1134816, by rfl⟩ : syracuseStep 3026177 = 2269633) B2269633
theorem B10898693 : Blo 1342990 10898693 := bstep (se 4 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 10898693 = 2043505) B2043505
theorem B4533569 : Blo 1342990 4533569 := bstep (se 2 (by rfl) ⟨1700088, by rfl⟩ : syracuseStep 4533569 = 3400177) B3400177
theorem B2551105 : Blo 1342990 2551105 := bstep (se 2 (by rfl) ⟨956664, by rfl⟩ : syracuseStep 2551105 = 1913329) B1913329
theorem B3403073 : Blo 1342990 3403073 := bstep (se 2 (by rfl) ⟨1276152, by rfl⟩ : syracuseStep 3403073 = 2552305) B2552305
theorem B6458717 : Blo 1342990 6458717 := bstep (se 3 (by rfl) ⟨1211009, by rfl⟩ : syracuseStep 6458717 = 2422019) B2422019
theorem B13102553 : Blo 1342990 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B2420275 : Blo 1342990 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B1510987 : Blo 1342990 1510987 := bstep (se 1 (by rfl) ⟨1133240, by rfl⟩ : syracuseStep 1510987 = 2266481) B2266481
theorem B2420375 : Blo 1342990 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B3829427 : Blo 1342990 3829427 := bstep (se 1 (by rfl) ⟨2872070, by rfl⟩ : syracuseStep 3829427 = 5744141) B5744141
theorem B1511095 : Blo 1342990 1511095 := bstep (se 1 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 1511095 = 2266643) B2266643
theorem B2870977 : Blo 1342990 2870977 := bstep (se 2 (by rfl) ⟨1076616, by rfl⟩ : syracuseStep 2870977 = 2153233) B2153233
theorem B12914477 : Blo 1342990 12914477 := bstep (se 3 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 12914477 = 4842929) B4842929
theorem B1912663 : Blo 1342990 1912663 := bstep (se 1 (by rfl) ⟨1434497, by rfl⟩ : syracuseStep 1912663 = 2868995) B2868995
theorem B4534109 : Blo 1342990 4534109 := bstep (se 3 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 4534109 = 1700291) B1700291
theorem B1511275 : Blo 1342990 1511275 := bstep (se 1 (by rfl) ⟨1133456, by rfl⟩ : syracuseStep 1511275 = 2266913) B2266913
theorem B6803351 : Blo 1342990 6803351 := bstep (se 1 (by rfl) ⟨5102513, by rfl⟩ : syracuseStep 6803351 = 10205027) B10205027
theorem B58896305 : Blo 1342990 58896305 := bstep (se 2 (by rfl) ⟨22086114, by rfl⟩ : syracuseStep 58896305 = 44172229) B44172229
theorem B11489201 : Blo 1342990 11489201 := bstep (se 2 (by rfl) ⟨4308450, by rfl⟩ : syracuseStep 11489201 = 8616901) B8616901
theorem B1511383 : Blo 1342990 1511383 := bstep (se 1 (by rfl) ⟨1133537, by rfl⟩ : syracuseStep 1511383 = 2267075) B2267075
theorem B2551819 : Blo 1342990 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B5099537 : Blo 1342990 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B10211345 : Blo 1342990 10211345 := bstep (se 2 (by rfl) ⟨3829254, by rfl⟩ : syracuseStep 10211345 = 7658509) B7658509
theorem B5451799 : Blo 1342990 5451799 := bstep (se 1 (by rfl) ⟨4088849, by rfl⟩ : syracuseStep 5451799 = 8177699) B8177699
theorem B2551895 : Blo 1342990 2551895 := bstep (se 1 (by rfl) ⟨1913921, by rfl⟩ : syracuseStep 2551895 = 3827843) B3827843
theorem B13791325 : Blo 1342990 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B11194469 : Blo 1342990 11194469 := bstep (se 4 (by rfl) ⟨1049481, by rfl⟩ : syracuseStep 11194469 = 2098963) B2098963
theorem B1511563 : Blo 1342990 1511563 := bstep (se 1 (by rfl) ⟨1133672, by rfl⟩ : syracuseStep 1511563 = 2267345) B2267345
theorem B3633331 : Blo 1342990 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B1511671 : Blo 1342990 1511671 := bstep (se 1 (by rfl) ⟨1133753, by rfl⟩ : syracuseStep 1511671 = 2267507) B2267507
theorem B1700119 : Blo 1342990 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B20697389 : Blo 1342990 20697389 := bstep (se 3 (by rfl) ⟨3880760, by rfl⟩ : syracuseStep 20697389 = 7761521) B7761521
theorem B5820761 : Blo 1342990 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B1511851 : Blo 1342990 1511851 := bstep (se 1 (by rfl) ⟨1133888, by rfl⟩ : syracuseStep 1511851 = 2267777) B2267777
theorem B10203569 : Blo 1342990 10203569 := bstep (se 2 (by rfl) ⟨3826338, by rfl⟩ : syracuseStep 10203569 = 7652677) B7652677
theorem B5099993 : Blo 1342990 5099993 := bstep (se 2 (by rfl) ⟨1912497, by rfl⟩ : syracuseStep 5099993 = 3824995) B3824995
theorem B12268037 : Blo 1342990 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B1454603 : Blo 1342990 1454603 := bstep (se 1 (by rfl) ⟨1090952, by rfl⟩ : syracuseStep 1454603 = 2181905) B2181905
theorem B1511959 : Blo 1342990 1511959 := bstep (se 1 (by rfl) ⟨1133969, by rfl⟩ : syracuseStep 1511959 = 2267939) B2267939
theorem B3404339 : Blo 1342990 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B5739083 : Blo 1342990 5739083 := bstep (se 1 (by rfl) ⟨4304312, by rfl⟩ : syracuseStep 5739083 = 8608625) B8608625
theorem B1913483 : Blo 1342990 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B1725067 : Blo 1342990 1725067 := bstep (se 1 (by rfl) ⟨1293800, by rfl⟩ : syracuseStep 1725067 = 2587601) B2587601
theorem B5100205 : Blo 1342990 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B1512139 : Blo 1342990 1512139 := bstep (se 1 (by rfl) ⟨1134104, by rfl⟩ : syracuseStep 1512139 = 2268209) B2268209
theorem B111932117 : Blo 1342990 111932117 := bstep (se 7 (by rfl) ⟨1311704, by rfl⟩ : syracuseStep 111932117 = 2623409) B2623409
theorem B2552563 : Blo 1342990 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B1512247 : Blo 1342990 1512247 := bstep (se 1 (by rfl) ⟨1134185, by rfl⟩ : syracuseStep 1512247 = 2268371) B2268371
theorem B10204055 : Blo 1342990 10204055 := bstep (se 1 (by rfl) ⟨7653041, by rfl⟩ : syracuseStep 10204055 = 15306083) B15306083
theorem B13267889 : Blo 1342990 13267889 := bstep (se 2 (by rfl) ⟨4975458, by rfl⟩ : syracuseStep 13267889 = 9950917) B9950917
theorem B4535243 : Blo 1342990 4535243 := bstep (se 1 (by rfl) ⟨3401432, by rfl⟩ : syracuseStep 4535243 = 6802865) B6802865
theorem B2552791 : Blo 1342990 2552791 := bstep (se 1 (by rfl) ⟨1914593, by rfl⟩ : syracuseStep 2552791 = 3829187) B3829187
theorem B5100509 : Blo 1342990 5100509 := bstep (se 3 (by rfl) ⟨956345, by rfl⟩ : syracuseStep 5100509 = 1912691) B1912691
theorem B1512427 : Blo 1342990 1512427 := bstep (se 1 (by rfl) ⟨1134320, by rfl⟩ : syracuseStep 1512427 = 2268641) B2268641
theorem B2552897 : Blo 1342990 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B1700939 : Blo 1342990 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1512535 : Blo 1342990 1512535 := bstep (se 1 (by rfl) ⟨1134401, by rfl⟩ : syracuseStep 1512535 = 2268803) B2268803
theorem B2421875 : Blo 1342990 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B2872523 : Blo 1342990 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B4535513 : Blo 1342990 4535513 := bstep (se 2 (by rfl) ⟨1700817, by rfl⟩ : syracuseStep 4535513 = 3401635) B3401635
theorem B2553049 : Blo 1342990 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B1512715 : Blo 1342990 1512715 := bstep (se 1 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 1512715 = 2269073) B2269073
theorem B2266393 : Blo 1342990 2266393 := bstep (se 2 (by rfl) ⟨849897, by rfl⟩ : syracuseStep 2266393 = 1699795) B1699795
theorem B2725145 : Blo 1342990 2725145 := bstep (se 2 (by rfl) ⟨1021929, by rfl⟩ : syracuseStep 2725145 = 2043859) B2043859
theorem B15316289 : Blo 1342990 15316289 := bstep (se 2 (by rfl) ⟨5743608, by rfl⟩ : syracuseStep 15316289 = 11487217) B11487217
theorem B8615261 : Blo 1342990 8615261 := bstep (se 3 (by rfl) ⟨1615361, by rfl⟩ : syracuseStep 8615261 = 3230723) B3230723
theorem B1512823 : Blo 1342990 1512823 := bstep (se 1 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 1512823 = 2269235) B2269235
theorem B1455607 : Blo 1342990 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B5740055 : Blo 1342990 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B1513003 : Blo 1342990 1513003 := bstep (se 1 (by rfl) ⟨1134752, by rfl⟩ : syracuseStep 1513003 = 2269505) B2269505
theorem B7763531 : Blo 1342990 7763531 := bstep (se 1 (by rfl) ⟨5822648, by rfl⟩ : syracuseStep 7763531 = 11645297) B11645297
theorem B1914457 : Blo 1342990 1914457 := bstep (se 2 (by rfl) ⟨717921, by rfl⟩ : syracuseStep 1914457 = 1435843) B1435843
theorem B43570781 : Blo 1342990 43570781 := bstep (se 3 (by rfl) ⟨8169521, by rfl⟩ : syracuseStep 43570781 = 16339043) B16339043
theorem B12269207 : Blo 1342990 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B1513111 : Blo 1342990 1513111 := bstep (se 1 (by rfl) ⟨1134833, by rfl⟩ : syracuseStep 1513111 = 2269667) B2269667
theorem B1701643 : Blo 1342990 1701643 := bstep (se 1 (by rfl) ⟨1276232, by rfl⟩ : syracuseStep 1701643 = 2552465) B2552465
theorem B2266967 : Blo 1342990 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B25827173 : Blo 1342990 25827173 := bstep (se 4 (by rfl) ⟨2421297, by rfl⟩ : syracuseStep 25827173 = 4842595) B4842595
theorem B4536215 : Blo 1342990 4536215 := bstep (se 1 (by rfl) ⟨3402161, by rfl⟩ : syracuseStep 4536215 = 6804323) B6804323
theorem B2267095 : Blo 1342990 2267095 := bstep (se 1 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 2267095 = 3400643) B3400643
theorem B1701911 : Blo 1342990 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B2586775 : Blo 1342990 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B18381005 : Blo 1342990 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B1816921 : Blo 1342990 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B8173925 : Blo 1342990 8173925 := bstep (se 4 (by rfl) ⟨766305, by rfl⟩ : syracuseStep 8173925 = 1532611) B1532611
theorem B4536755 : Blo 1342990 4536755 := bstep (se 1 (by rfl) ⟨3402566, by rfl⟩ : syracuseStep 4536755 = 6805133) B6805133
theorem B21559769 : Blo 1342990 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B12909131 : Blo 1342990 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B2267723 : Blo 1342990 2267723 := bstep (se 1 (by rfl) ⟨1700792, by rfl⟩ : syracuseStep 2267723 = 3401585) B3401585
theorem B2423447 : Blo 1342990 2423447 := bstep (se 1 (by rfl) ⟨1817585, by rfl⟩ : syracuseStep 2423447 = 3635171) B3635171
theorem B9689777 : Blo 1342990 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B9812659 : Blo 1342990 9812659 := bstep (se 1 (by rfl) ⟨7359494, by rfl⟩ : syracuseStep 9812659 = 14718989) B14718989
theorem B4537025 : Blo 1342990 4537025 := bstep (se 2 (by rfl) ⟨1701384, by rfl⟩ : syracuseStep 4537025 = 3402769) B3402769
theorem B2267851 : Blo 1342990 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B4086551 : Blo 1342990 4086551 := bstep (se 1 (by rfl) ⟨3064913, by rfl⟩ : syracuseStep 4086551 = 6129827) B6129827
theorem B2267993 : Blo 1342990 2267993 := bstep (se 2 (by rfl) ⟨850497, by rfl⟩ : syracuseStep 2267993 = 1700995) B1700995
theorem B3021785 : Blo 1342990 3021785 := bstep (se 2 (by rfl) ⟨1133169, by rfl⟩ : syracuseStep 3021785 = 2266339) B2266339
theorem B2268121 : Blo 1342990 2268121 := bstep (se 2 (by rfl) ⟨850545, by rfl⟩ : syracuseStep 2268121 = 1701091) B1701091
theorem B2153495 : Blo 1342990 2153495 := bstep (se 1 (by rfl) ⟨1615121, by rfl⟩ : syracuseStep 2153495 = 3230243) B3230243
theorem B3021875 : Blo 1342990 3021875 := bstep (se 1 (by rfl) ⟨2266406, by rfl⟩ : syracuseStep 3021875 = 4532813) B4532813
theorem B3021911 : Blo 1342990 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B2153623 : Blo 1342990 2153623 := bstep (se 1 (by rfl) ⟨1615217, by rfl⟩ : syracuseStep 2153623 = 3230435) B3230435
theorem B4537565 : Blo 1342990 4537565 := bstep (se 3 (by rfl) ⟨850793, by rfl⟩ : syracuseStep 4537565 = 1701587) B1701587
theorem B3022091 : Blo 1342990 3022091 := bstep (se 1 (by rfl) ⟨2266568, by rfl⟩ : syracuseStep 3022091 = 4533137) B4533137
theorem B2014487 : Blo 1342990 2014487 := bstep (se 1 (by rfl) ⟨1510865, by rfl⟩ : syracuseStep 2014487 = 3021731) B3021731
theorem B3022145 : Blo 1342990 3022145 := bstep (se 2 (by rfl) ⟨1133304, by rfl⟩ : syracuseStep 3022145 = 2266609) B2266609
theorem B2014553 : Blo 1342990 2014553 := bstep (se 2 (by rfl) ⟨755457, by rfl⟩ : syracuseStep 2014553 = 1510915) B1510915
theorem B6126941 : Blo 1342990 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B6806915 : Blo 1342990 6806915 := bstep (se 1 (by rfl) ⟨5105186, by rfl⟩ : syracuseStep 6806915 = 10210373) B10210373
theorem B2014667 : Blo 1342990 2014667 := bstep (se 1 (by rfl) ⟨1511000, by rfl⟩ : syracuseStep 2014667 = 3022001) B3022001
theorem B2014679 : Blo 1342990 2014679 := bstep (se 1 (by rfl) ⟨1511009, by rfl⟩ : syracuseStep 2014679 = 3022019) B3022019
theorem B5103107 : Blo 1342990 5103107 := bstep (se 1 (by rfl) ⟨3827330, by rfl⟩ : syracuseStep 5103107 = 7654661) B7654661
theorem B5103121 : Blo 1342990 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B1342999 : Blo 1342990 1342999 := bstep (se 1 (by rfl) ⟨1007249, by rfl⟩ : syracuseStep 1342999 = 2014499) B2014499
theorem B2268695 : Blo 1342990 2268695 := bstep (se 1 (by rfl) ⟨1701521, by rfl⟩ : syracuseStep 2268695 = 3403043) B3403043
theorem B2014745 : Blo 1342990 2014745 := bstep (se 2 (by rfl) ⟨755529, by rfl⟩ : syracuseStep 2014745 = 1511059) B1511059
theorem B3022361 : Blo 1342990 3022361 := bstep (se 2 (by rfl) ⟨1133385, by rfl⟩ : syracuseStep 3022361 = 2266771) B2266771
theorem B1343019 : Blo 1342990 1343019 := bstep (se 1 (by rfl) ⟨1007264, by rfl⟩ : syracuseStep 1343019 = 2014529) B2014529
theorem B1343031 : Blo 1342990 1343031 := bstep (se 1 (by rfl) ⟨1007273, by rfl⟩ : syracuseStep 1343031 = 2014547) B2014547
theorem B3063361 : Blo 1342990 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B1343051 : Blo 1342990 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B1343063 : Blo 1342990 1343063 := bstep (se 1 (by rfl) ⟨1007297, by rfl⟩ : syracuseStep 1343063 = 2014595) B2014595
theorem B3825245 : Blo 1342990 3825245 := bstep (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) B1434467
theorem B1343083 : Blo 1342990 1343083 := bstep (se 1 (by rfl) ⟨1007312, by rfl⟩ : syracuseStep 1343083 = 2014625) B2014625
theorem B3022451 : Blo 1342990 3022451 := bstep (se 1 (by rfl) ⟨2266838, by rfl⟩ : syracuseStep 3022451 = 4533677) B4533677
theorem B1343095 : Blo 1342990 1343095 := bstep (se 1 (by rfl) ⟨1007321, by rfl⟩ : syracuseStep 1343095 = 2014643) B2014643
theorem B1343115 : Blo 1342990 1343115 := bstep (se 1 (by rfl) ⟨1007336, by rfl⟩ : syracuseStep 1343115 = 2014673) B2014673
theorem B2014859 : Blo 1342990 2014859 := bstep (se 1 (by rfl) ⟨1511144, by rfl⟩ : syracuseStep 2014859 = 3022289) B3022289
theorem B1343127 : Blo 1342990 1343127 := bstep (se 1 (by rfl) ⟨1007345, by rfl⟩ : syracuseStep 1343127 = 2014691) B2014691
theorem B2014871 : Blo 1342990 2014871 := bstep (se 1 (by rfl) ⟨1511153, by rfl⟩ : syracuseStep 2014871 = 3022307) B3022307
theorem B3022487 : Blo 1342990 3022487 := bstep (se 1 (by rfl) ⟨2266865, by rfl⟩ : syracuseStep 3022487 = 4533731) B4533731
theorem B2268823 : Blo 1342990 2268823 := bstep (se 1 (by rfl) ⟨1701617, by rfl⟩ : syracuseStep 2268823 = 3403235) B3403235
theorem B1343147 : Blo 1342990 1343147 := bstep (se 1 (by rfl) ⟨1007360, by rfl⟩ : syracuseStep 1343147 = 2014721) B2014721
theorem B1343159 : Blo 1342990 1343159 := bstep (se 1 (by rfl) ⟨1007369, by rfl⟩ : syracuseStep 1343159 = 2014739) B2014739
theorem B1343179 : Blo 1342990 1343179 := bstep (se 1 (by rfl) ⟨1007384, by rfl⟩ : syracuseStep 1343179 = 2014769) B2014769
theorem B1531607 : Blo 1342990 1531607 := bstep (se 1 (by rfl) ⟨1148705, by rfl⟩ : syracuseStep 1531607 = 2297411) B2297411
theorem B1343191 : Blo 1342990 1343191 := bstep (se 1 (by rfl) ⟨1007393, by rfl⟩ : syracuseStep 1343191 = 2014787) B2014787
theorem B2014937 : Blo 1342990 2014937 := bstep (se 2 (by rfl) ⟨755601, by rfl⟩ : syracuseStep 2014937 = 1511203) B1511203
theorem B1343211 : Blo 1342990 1343211 := bstep (se 1 (by rfl) ⟨1007408, by rfl⟩ : syracuseStep 1343211 = 2014817) B2014817
theorem B1343223 : Blo 1342990 1343223 := bstep (se 1 (by rfl) ⟨1007417, by rfl⟩ : syracuseStep 1343223 = 2014835) B2014835
theorem B1613579 : Blo 1342990 1613579 := bstep (se 1 (by rfl) ⟨1210184, by rfl⟩ : syracuseStep 1613579 = 2420369) B2420369
theorem B1343243 : Blo 1342990 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B1343255 : Blo 1342990 1343255 := bstep (se 1 (by rfl) ⟨1007441, by rfl⟩ : syracuseStep 1343255 = 2014883) B2014883
theorem B1343275 : Blo 1342990 1343275 := bstep (se 1 (by rfl) ⟨1007456, by rfl⟩ : syracuseStep 1343275 = 2014913) B2014913
theorem B1343287 : Blo 1342990 1343287 := bstep (se 1 (by rfl) ⟨1007465, by rfl⟩ : syracuseStep 1343287 = 2014931) B2014931
theorem B5103425 : Blo 1342990 5103425 := bstep (se 2 (by rfl) ⟨1913784, by rfl⟩ : syracuseStep 5103425 = 3827569) B3827569
theorem B1343307 : Blo 1342990 1343307 := bstep (se 1 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 1343307 = 2014961) B2014961
theorem B2015051 : Blo 1342990 2015051 := bstep (se 1 (by rfl) ⟨1511288, by rfl⟩ : syracuseStep 2015051 = 3022577) B3022577
theorem B3022667 : Blo 1342990 3022667 := bstep (se 1 (by rfl) ⟨2267000, by rfl⟩ : syracuseStep 3022667 = 4534001) B4534001
theorem B1343319 : Blo 1342990 1343319 := bstep (se 1 (by rfl) ⟨1007489, by rfl⟩ : syracuseStep 1343319 = 2014979) B2014979
theorem B2015063 : Blo 1342990 2015063 := bstep (se 1 (by rfl) ⟨1511297, by rfl⟩ : syracuseStep 2015063 = 3022595) B3022595
theorem B11476829 : Blo 1342990 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B1343339 : Blo 1342990 1343339 := bstep (se 1 (by rfl) ⟨1007504, by rfl⟩ : syracuseStep 1343339 = 2015009) B2015009
theorem B1343351 : Blo 1342990 1343351 := bstep (se 1 (by rfl) ⟨1007513, by rfl⟩ : syracuseStep 1343351 = 2015027) B2015027
theorem B3022721 : Blo 1342990 3022721 := bstep (se 2 (by rfl) ⟨1133520, by rfl⟩ : syracuseStep 3022721 = 2267041) B2267041
theorem B1343371 : Blo 1342990 1343371 := bstep (se 1 (by rfl) ⟨1007528, by rfl⟩ : syracuseStep 1343371 = 2015057) B2015057
theorem B1343383 : Blo 1342990 1343383 := bstep (se 1 (by rfl) ⟨1007537, by rfl⟩ : syracuseStep 1343383 = 2015075) B2015075
theorem B2015129 : Blo 1342990 2015129 := bstep (se 2 (by rfl) ⟨755673, by rfl⟩ : syracuseStep 2015129 = 1511347) B1511347
theorem B1343403 : Blo 1342990 1343403 := bstep (se 1 (by rfl) ⟨1007552, by rfl⟩ : syracuseStep 1343403 = 2015105) B2015105
theorem B5742515 : Blo 1342990 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B1343415 : Blo 1342990 1343415 := bstep (se 1 (by rfl) ⟨1007561, by rfl⟩ : syracuseStep 1343415 = 2015123) B2015123
theorem B1343435 : Blo 1342990 1343435 := bstep (se 1 (by rfl) ⟨1007576, by rfl⟩ : syracuseStep 1343435 = 2015153) B2015153
theorem B1343447 : Blo 1342990 1343447 := bstep (se 1 (by rfl) ⟨1007585, by rfl⟩ : syracuseStep 1343447 = 2015171) B2015171
theorem B3399641 : Blo 1342990 3399641 := bstep (se 2 (by rfl) ⟨1274865, by rfl⟩ : syracuseStep 3399641 = 2549731) B2549731
theorem B1343467 : Blo 1342990 1343467 := bstep (se 1 (by rfl) ⟨1007600, by rfl⟩ : syracuseStep 1343467 = 2015201) B2015201
theorem B1343479 : Blo 1342990 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B1343495 : Blo 1342990 1343495 := bstep (se 1 (by rfl) ⟨1007621, by rfl⟩ : syracuseStep 1343495 = 2015243) B2015243
theorem B3399691 : Blo 1342990 3399691 := bstep (se 1 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 3399691 = 5099537) B5099537
theorem B6807563 : Blo 1342990 6807563 := bstep (se 1 (by rfl) ⟨5105672, by rfl⟩ : syracuseStep 6807563 = 10211345) B10211345
theorem B1343503 : Blo 1342990 1343503 := bstep (se 1 (by rfl) ⟨1007627, by rfl⟩ : syracuseStep 1343503 = 2015255) B2015255
theorem B2015291 : Blo 1342990 2015291 := bstep (se 1 (by rfl) ⟨1511468, by rfl⟩ : syracuseStep 2015291 = 3022937) B3022937
theorem B1343547 : Blo 1342990 1343547 := bstep (se 1 (by rfl) ⟨1007660, by rfl⟩ : syracuseStep 1343547 = 2015321) B2015321
theorem B4538429 : Blo 1342990 4538429 := bstep (se 3 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 4538429 = 1701911) B1701911
theorem B7462979 : Blo 1342990 7462979 := bstep (se 1 (by rfl) ⟨5597234, by rfl⟩ : syracuseStep 7462979 = 11194469) B11194469
theorem B2015351 : Blo 1342990 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B1343623 : Blo 1342990 1343623 := bstep (se 1 (by rfl) ⟨1007717, by rfl⟩ : syracuseStep 1343623 = 2015435) B2015435
theorem B2015375 : Blo 1342990 2015375 := bstep (se 1 (by rfl) ⟨1511531, by rfl⟩ : syracuseStep 2015375 = 3023063) B3023063
theorem B1343631 : Blo 1342990 1343631 := bstep (se 1 (by rfl) ⟨1007723, by rfl⟩ : syracuseStep 1343631 = 2015447) B2015447
theorem B3399833 : Blo 1342990 3399833 := bstep (se 2 (by rfl) ⟨1274937, by rfl⟩ : syracuseStep 3399833 = 2549875) B2549875
theorem B6807725 : Blo 1342990 6807725 := bstep (se 3 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 6807725 = 2552897) B2552897
theorem B2015417 : Blo 1342990 2015417 := bstep (se 2 (by rfl) ⟨755781, by rfl⟩ : syracuseStep 2015417 = 1511563) B1511563
theorem B1343675 : Blo 1342990 1343675 := bstep (se 1 (by rfl) ⟨1007756, by rfl⟩ : syracuseStep 1343675 = 2015513) B2015513
theorem B3449033 : Blo 1342990 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B2015495 : Blo 1342990 2015495 := bstep (se 1 (by rfl) ⟨1511621, by rfl⟩ : syracuseStep 2015495 = 3023243) B3023243
theorem B1343751 : Blo 1342990 1343751 := bstep (se 1 (by rfl) ⟨1007813, by rfl⟩ : syracuseStep 1343751 = 2015627) B2015627
theorem B1343759 : Blo 1342990 1343759 := bstep (se 1 (by rfl) ⟨1007819, by rfl⟩ : syracuseStep 1343759 = 2015639) B2015639
theorem B2015531 : Blo 1342990 2015531 := bstep (se 1 (by rfl) ⟨1511648, by rfl⟩ : syracuseStep 2015531 = 3023297) B3023297
theorem B3399995 : Blo 1342990 3399995 := bstep (se 1 (by rfl) ⟨2549996, by rfl⟩ : syracuseStep 3399995 = 5099993) B5099993
theorem B1343803 : Blo 1342990 1343803 := bstep (se 1 (by rfl) ⟨1007852, by rfl⟩ : syracuseStep 1343803 = 2015705) B2015705
theorem B2015561 : Blo 1342990 2015561 := bstep (se 2 (by rfl) ⟨755835, by rfl⟩ : syracuseStep 2015561 = 1511671) B1511671
theorem B2269559 : Blo 1342990 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B3826055 : Blo 1342990 3826055 := bstep (se 1 (by rfl) ⟨2869541, by rfl⟩ : syracuseStep 3826055 = 5739083) B5739083
theorem B1343879 : Blo 1342990 1343879 := bstep (se 1 (by rfl) ⟨1007909, by rfl⟩ : syracuseStep 1343879 = 2015819) B2015819
theorem B1343887 : Blo 1342990 1343887 := bstep (se 1 (by rfl) ⟨1007915, by rfl⟩ : syracuseStep 1343887 = 2015831) B2015831
theorem B2015675 : Blo 1342990 2015675 := bstep (se 1 (by rfl) ⟨1511756, by rfl⟩ : syracuseStep 2015675 = 3023513) B3023513
theorem B1343931 : Blo 1342990 1343931 := bstep (se 1 (by rfl) ⟨1007948, by rfl⟩ : syracuseStep 1343931 = 2015897) B2015897
theorem B74621411 : Blo 1342990 74621411 := bstep (se 1 (by rfl) ⟨55966058, by rfl⟩ : syracuseStep 74621411 = 111932117) B111932117
theorem B2015735 : Blo 1342990 2015735 := bstep (se 1 (by rfl) ⟨1511801, by rfl⟩ : syracuseStep 2015735 = 3023603) B3023603
theorem B1344007 : Blo 1342990 1344007 := bstep (se 1 (by rfl) ⟨1008005, by rfl⟩ : syracuseStep 1344007 = 2016011) B2016011
theorem B2015759 : Blo 1342990 2015759 := bstep (se 1 (by rfl) ⟨1511819, by rfl⟩ : syracuseStep 2015759 = 3023639) B3023639
theorem B1344015 : Blo 1342990 1344015 := bstep (se 1 (by rfl) ⟨1008011, by rfl⟩ : syracuseStep 1344015 = 2016023) B2016023
theorem B2015801 : Blo 1342990 2015801 := bstep (se 2 (by rfl) ⟨755925, by rfl⟩ : syracuseStep 2015801 = 1511851) B1511851
theorem B1344059 : Blo 1342990 1344059 := bstep (se 1 (by rfl) ⟨1008044, by rfl⟩ : syracuseStep 1344059 = 2016089) B2016089
theorem B3826237 : Blo 1342990 3826237 := bstep (se 3 (by rfl) ⟨717419, by rfl⟩ : syracuseStep 3826237 = 1434839) B1434839
theorem B3023495 : Blo 1342990 3023495 := bstep (se 1 (by rfl) ⟨2267621, by rfl⟩ : syracuseStep 3023495 = 4535243) B4535243
theorem B2015879 : Blo 1342990 2015879 := bstep (se 1 (by rfl) ⟨1511909, by rfl⟩ : syracuseStep 2015879 = 3023819) B3023819
theorem B1344135 : Blo 1342990 1344135 := bstep (se 1 (by rfl) ⟨1008101, by rfl⟩ : syracuseStep 1344135 = 2016203) B2016203
theorem B1344143 : Blo 1342990 1344143 := bstep (se 1 (by rfl) ⟨1008107, by rfl⟩ : syracuseStep 1344143 = 2016215) B2016215
theorem B3400339 : Blo 1342990 3400339 := bstep (se 1 (by rfl) ⟨2550254, by rfl⟩ : syracuseStep 3400339 = 5100509) B5100509
theorem B2015915 : Blo 1342990 2015915 := bstep (se 1 (by rfl) ⟨1511936, by rfl⟩ : syracuseStep 2015915 = 3023873) B3023873
theorem B1344187 : Blo 1342990 1344187 := bstep (se 1 (by rfl) ⟨1008140, by rfl⟩ : syracuseStep 1344187 = 2016281) B2016281
theorem B2015945 : Blo 1342990 2015945 := bstep (se 2 (by rfl) ⟨755979, by rfl⟩ : syracuseStep 2015945 = 1511959) B1511959
theorem B1614583 : Blo 1342990 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B1344263 : Blo 1342990 1344263 := bstep (se 1 (by rfl) ⟨1008197, by rfl⟩ : syracuseStep 1344263 = 2016395) B2016395
theorem B1344271 : Blo 1342990 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B3400481 : Blo 1342990 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B3023675 : Blo 1342990 3023675 := bstep (se 1 (by rfl) ⟨2267756, by rfl⟩ : syracuseStep 3023675 = 4535513) B4535513
theorem B2016059 : Blo 1342990 2016059 := bstep (se 1 (by rfl) ⟨1512044, by rfl⟩ : syracuseStep 2016059 = 3024089) B3024089
theorem B1344315 : Blo 1342990 1344315 := bstep (se 1 (by rfl) ⟨1008236, by rfl⟩ : syracuseStep 1344315 = 2016473) B2016473
theorem B6456179 : Blo 1342990 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B2016119 : Blo 1342990 2016119 := bstep (se 1 (by rfl) ⟨1512089, by rfl⟩ : syracuseStep 2016119 = 3024179) B3024179
theorem B1344391 : Blo 1342990 1344391 := bstep (se 1 (by rfl) ⟨1008293, by rfl⟩ : syracuseStep 1344391 = 2016587) B2016587
theorem B2016143 : Blo 1342990 2016143 := bstep (se 1 (by rfl) ⟨1512107, by rfl⟩ : syracuseStep 2016143 = 3024215) B3024215
theorem B1344399 : Blo 1342990 1344399 := bstep (se 1 (by rfl) ⟨1008299, by rfl⟩ : syracuseStep 1344399 = 2016599) B2016599
theorem B6800273 : Blo 1342990 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B5743507 : Blo 1342990 5743507 := bstep (se 1 (by rfl) ⟨4307630, by rfl⟩ : syracuseStep 5743507 = 8615261) B8615261
theorem B13083545 : Blo 1342990 13083545 := bstep (se 2 (by rfl) ⟨4906329, by rfl⟩ : syracuseStep 13083545 = 9812659) B9812659
theorem B3023801 : Blo 1342990 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B2016185 : Blo 1342990 2016185 := bstep (se 2 (by rfl) ⟨756069, by rfl⟩ : syracuseStep 2016185 = 1512139) B1512139
theorem B1344443 : Blo 1342990 1344443 := bstep (se 1 (by rfl) ⟨1008332, by rfl⟩ : syracuseStep 1344443 = 2016665) B2016665
theorem B2016263 : Blo 1342990 2016263 := bstep (se 1 (by rfl) ⟨1512197, by rfl⟩ : syracuseStep 2016263 = 3024395) B3024395
theorem B1344519 : Blo 1342990 1344519 := bstep (se 1 (by rfl) ⟨1008389, by rfl⟩ : syracuseStep 1344519 = 2016779) B2016779
theorem B3826703 : Blo 1342990 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B1344527 : Blo 1342990 1344527 := bstep (se 1 (by rfl) ⟨1008395, by rfl⟩ : syracuseStep 1344527 = 2016791) B2016791
theorem B2016299 : Blo 1342990 2016299 := bstep (se 1 (by rfl) ⟨1512224, by rfl⟩ : syracuseStep 2016299 = 3024449) B3024449
theorem B2393147 : Blo 1342990 2393147 := bstep (se 1 (by rfl) ⟨1794860, by rfl⟩ : syracuseStep 2393147 = 3589721) B3589721
theorem B1344571 : Blo 1342990 1344571 := bstep (se 1 (by rfl) ⟨1008428, by rfl⟩ : syracuseStep 1344571 = 2016857) B2016857
theorem B2016329 : Blo 1342990 2016329 := bstep (se 2 (by rfl) ⟨756123, by rfl⟩ : syracuseStep 2016329 = 1512247) B1512247
theorem B1344647 : Blo 1342990 1344647 := bstep (se 1 (by rfl) ⟨1008485, by rfl⟩ : syracuseStep 1344647 = 2016971) B2016971
theorem B1344655 : Blo 1342990 1344655 := bstep (se 1 (by rfl) ⟨1008491, by rfl⟩ : syracuseStep 1344655 = 2016983) B2016983
theorem B10208429 : Blo 1342990 10208429 := bstep (se 3 (by rfl) ⟨1914080, by rfl⟩ : syracuseStep 10208429 = 3828161) B3828161
theorem B2016443 : Blo 1342990 2016443 := bstep (se 1 (by rfl) ⟨1512332, by rfl⟩ : syracuseStep 2016443 = 3024665) B3024665
theorem B1344699 : Blo 1342990 1344699 := bstep (se 1 (by rfl) ⟨1008524, by rfl⟩ : syracuseStep 1344699 = 2017049) B2017049
theorem B2016503 : Blo 1342990 2016503 := bstep (se 1 (by rfl) ⟨1512377, by rfl⟩ : syracuseStep 2016503 = 3024755) B3024755
theorem B1344775 : Blo 1342990 1344775 := bstep (se 1 (by rfl) ⟨1008581, by rfl⟩ : syracuseStep 1344775 = 2017163) B2017163
theorem B3024143 : Blo 1342990 3024143 := bstep (se 1 (by rfl) ⟨2268107, by rfl⟩ : syracuseStep 3024143 = 4536215) B4536215
theorem B2016527 : Blo 1342990 2016527 := bstep (se 1 (by rfl) ⟨1512395, by rfl⟩ : syracuseStep 2016527 = 3024791) B3024791
theorem B1344783 : Blo 1342990 1344783 := bstep (se 1 (by rfl) ⟨1008587, by rfl⟩ : syracuseStep 1344783 = 2017175) B2017175
theorem B3024161 : Blo 1342990 3024161 := bstep (se 2 (by rfl) ⟨1134060, by rfl⟩ : syracuseStep 3024161 = 2268121) B2268121
theorem B2016569 : Blo 1342990 2016569 := bstep (se 2 (by rfl) ⟨756213, by rfl⟩ : syracuseStep 2016569 = 1512427) B1512427
theorem B1344827 : Blo 1342990 1344827 := bstep (se 1 (by rfl) ⟨1008620, by rfl⟩ : syracuseStep 1344827 = 2017241) B2017241
theorem B2016647 : Blo 1342990 2016647 := bstep (se 1 (by rfl) ⟨1512485, by rfl⟩ : syracuseStep 2016647 = 3024971) B3024971
theorem B1344903 : Blo 1342990 1344903 := bstep (se 1 (by rfl) ⟨1008677, by rfl⟩ : syracuseStep 1344903 = 2017355) B2017355
theorem B1344911 : Blo 1342990 1344911 := bstep (se 1 (by rfl) ⟨1008683, by rfl⟩ : syracuseStep 1344911 = 2017367) B2017367
theorem B2016683 : Blo 1342990 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B1344955 : Blo 1342990 1344955 := bstep (se 1 (by rfl) ⟨1008716, by rfl⟩ : syracuseStep 1344955 = 2017433) B2017433
theorem B2016713 : Blo 1342990 2016713 := bstep (se 2 (by rfl) ⟨756267, by rfl⟩ : syracuseStep 2016713 = 1512535) B1512535
theorem B13788701 : Blo 1342990 13788701 := bstep (se 3 (by rfl) ⟨2585381, by rfl⟩ : syracuseStep 13788701 = 5170763) B5170763
theorem B2016827 : Blo 1342990 2016827 := bstep (se 1 (by rfl) ⟨1512620, by rfl⟩ : syracuseStep 2016827 = 3025241) B3025241
theorem B5449283 : Blo 1342990 5449283 := bstep (se 1 (by rfl) ⟨4086962, by rfl⟩ : syracuseStep 5449283 = 8173925) B8173925
theorem B62047813 : Blo 1342990 62047813 := bstep (se 4 (by rfl) ⟨5816982, by rfl⟩ : syracuseStep 62047813 = 11633965) B11633965
theorem B10200653 : Blo 1342990 10200653 := bstep (se 3 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 10200653 = 3825245) B3825245
theorem B7652951 : Blo 1342990 7652951 := bstep (se 1 (by rfl) ⟨5739713, by rfl⟩ : syracuseStep 7652951 = 11479427) B11479427
theorem B3024503 : Blo 1342990 3024503 := bstep (se 1 (by rfl) ⟨2268377, by rfl⟩ : syracuseStep 3024503 = 4536755) B4536755
theorem B2016887 : Blo 1342990 2016887 := bstep (se 1 (by rfl) ⟨1512665, by rfl⟩ : syracuseStep 2016887 = 3025331) B3025331
theorem B2016911 : Blo 1342990 2016911 := bstep (se 1 (by rfl) ⟨1512683, by rfl⟩ : syracuseStep 2016911 = 3025367) B3025367
theorem B2016953 : Blo 1342990 2016953 := bstep (se 2 (by rfl) ⟨756357, by rfl⟩ : syracuseStep 2016953 = 1512715) B1512715
theorem B3401473 : Blo 1342990 3401473 := bstep (se 2 (by rfl) ⟨1275552, by rfl⟩ : syracuseStep 3401473 = 2551105) B2551105
theorem B2017031 : Blo 1342990 2017031 := bstep (se 1 (by rfl) ⟨1512773, by rfl⟩ : syracuseStep 2017031 = 3025547) B3025547
theorem B6457103 : Blo 1342990 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B3065615 : Blo 1342990 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B1615631 : Blo 1342990 1615631 := bstep (se 1 (by rfl) ⟨1211723, by rfl⟩ : syracuseStep 1615631 = 2423447) B2423447
theorem B3024683 : Blo 1342990 3024683 := bstep (se 1 (by rfl) ⟨2268512, by rfl⟩ : syracuseStep 3024683 = 4537025) B4537025
theorem B2017067 : Blo 1342990 2017067 := bstep (se 1 (by rfl) ⟨1512800, by rfl⟩ : syracuseStep 2017067 = 3025601) B3025601
theorem B2017097 : Blo 1342990 2017097 := bstep (se 2 (by rfl) ⟨756411, by rfl⟩ : syracuseStep 2017097 = 1512823) B1512823
theorem B2869139 : Blo 1342990 2869139 := bstep (se 1 (by rfl) ⟨2151854, by rfl⟩ : syracuseStep 2869139 = 4303709) B4303709
theorem B2017211 : Blo 1342990 2017211 := bstep (se 1 (by rfl) ⟨1512908, by rfl⟩ : syracuseStep 2017211 = 3025817) B3025817
theorem B26920907 : Blo 1342990 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B2017271 : Blo 1342990 2017271 := bstep (se 1 (by rfl) ⟨1512953, by rfl⟩ : syracuseStep 2017271 = 3025907) B3025907
theorem B1435663 : Blo 1342990 1435663 := bstep (se 1 (by rfl) ⟨1076747, by rfl⟩ : syracuseStep 1435663 = 2153495) B2153495
theorem B2017295 : Blo 1342990 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B4302877 : Blo 1342990 4302877 := bstep (se 3 (by rfl) ⟨806789, by rfl⟩ : syracuseStep 4302877 = 1613579) B1613579
theorem B2017337 : Blo 1342990 2017337 := bstep (se 2 (by rfl) ⟨756501, by rfl⟩ : syracuseStep 2017337 = 1513003) B1513003
theorem B2017415 : Blo 1342990 2017415 := bstep (se 1 (by rfl) ⟨1513061, by rfl⟩ : syracuseStep 2017415 = 3026123) B3026123
theorem B3025043 : Blo 1342990 3025043 := bstep (se 1 (by rfl) ⟨2268782, by rfl⟩ : syracuseStep 3025043 = 4537565) B4537565
theorem B2017451 : Blo 1342990 2017451 := bstep (se 1 (by rfl) ⟨1513088, by rfl⟩ : syracuseStep 2017451 = 3026177) B3026177
theorem B17221805 : Blo 1342990 17221805 := bstep (se 3 (by rfl) ⟨3229088, by rfl⟩ : syracuseStep 17221805 = 6458177) B6458177
theorem B3025097 : Blo 1342990 3025097 := bstep (se 2 (by rfl) ⟨1134411, by rfl⟩ : syracuseStep 3025097 = 2268823) B2268823
theorem B2017481 : Blo 1342990 2017481 := bstep (se 2 (by rfl) ⟨756555, by rfl⟩ : syracuseStep 2017481 = 1513111) B1513111
theorem B16337141 : Blo 1342990 16337141 := bstep (se 5 (by rfl) ⟨765803, by rfl⟩ : syracuseStep 16337141 = 1531607) B1531607
theorem B3827969 : Blo 1342990 3827969 := bstep (se 2 (by rfl) ⟨1435488, by rfl⟩ : syracuseStep 3827969 = 2870977) B2870977
theorem B8735035 : Blo 1342990 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B3402071 : Blo 1342990 3402071 := bstep (se 1 (by rfl) ⟨2551553, by rfl⟩ : syracuseStep 3402071 = 5103107) B5103107
theorem B2550217 : Blo 1342990 2550217 := bstep (se 2 (by rfl) ⟨956331, by rfl⟩ : syracuseStep 2550217 = 1912663) B1912663
theorem B15313373 : Blo 1342990 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B3631645 : Blo 1342990 3631645 := bstep (se 3 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 3631645 = 1361867) B1361867
theorem B3402283 : Blo 1342990 3402283 := bstep (se 1 (by rfl) ⟨2551712, by rfl⟩ : syracuseStep 3402283 = 5103425) B5103425
theorem B3402425 : Blo 1342990 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B7269065 : Blo 1342990 7269065 := bstep (se 2 (by rfl) ⟨2725899, by rfl⟩ : syracuseStep 7269065 = 5451799) B5451799
theorem B13798259 : Blo 1342990 13798259 := bstep (se 1 (by rfl) ⟨10348694, by rfl⟩ : syracuseStep 13798259 = 20697389) B20697389
theorem B3025799 : Blo 1342990 3025799 := bstep (se 1 (by rfl) ⟨2269349, by rfl⟩ : syracuseStep 3025799 = 4538699) B4538699
theorem B4844441 : Blo 1342990 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B2042825 : Blo 1342990 2042825 := bstep (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) B1532119
theorem B6802379 : Blo 1342990 6802379 := bstep (se 1 (by rfl) ⟨5101784, by rfl⟩ : syracuseStep 6802379 = 10203569) B10203569
theorem B3025979 : Blo 1342990 3025979 := bstep (se 1 (by rfl) ⟨2269484, by rfl⟩ : syracuseStep 3025979 = 4538969) B4538969
theorem B3026105 : Blo 1342990 3026105 := bstep (se 2 (by rfl) ⟨1134789, by rfl⟩ : syracuseStep 3026105 = 2269579) B2269579
theorem B6802703 : Blo 1342990 6802703 := bstep (se 1 (by rfl) ⟨5102027, by rfl⟩ : syracuseStep 6802703 = 10204055) B10204055
theorem B22089145 : Blo 1342990 22089145 := bstep (se 2 (by rfl) ⟨8283429, by rfl⟩ : syracuseStep 22089145 = 16566859) B16566859
theorem B10210859 : Blo 1342990 10210859 := bstep (se 1 (by rfl) ⟨7658144, by rfl⟩ : syracuseStep 10210859 = 15316289) B15316289
theorem B16338509 : Blo 1342990 16338509 := bstep (se 3 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 16338509 = 6126941) B6126941
theorem B3403417 : Blo 1342990 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B8179471 : Blo 1342990 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B5451553 : Blo 1342990 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B3403579 : Blo 1342990 3403579 := bstep (se 1 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 3403579 = 5105369) B5105369
theorem B3829619 : Blo 1342990 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B1511311 : Blo 1342990 1511311 := bstep (se 1 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 1511311 = 2266967) B2266967
theorem B4534163 : Blo 1342990 4534163 := bstep (se 1 (by rfl) ⟨3400622, by rfl⟩ : syracuseStep 4534163 = 6801245) B6801245
theorem B4599737 : Blo 1342990 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B3403721 : Blo 1342990 3403721 := bstep (se 2 (by rfl) ⟨1276395, by rfl⟩ : syracuseStep 3403721 = 2552791) B2552791
theorem B10203083 : Blo 1342990 10203083 := bstep (se 1 (by rfl) ⟨7652312, by rfl⟩ : syracuseStep 10203083 = 15304625) B15304625
theorem B2043895 : Blo 1342990 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B32714765 : Blo 1342990 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B8171543 : Blo 1342990 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B3878941 : Blo 1342990 3878941 := bstep (se 3 (by rfl) ⟨727301, by rfl⟩ : syracuseStep 3878941 = 1454603) B1454603
theorem B2420779 : Blo 1342990 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B1912891 : Blo 1342990 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B2871497 : Blo 1342990 2871497 := bstep (se 2 (by rfl) ⟨1076811, by rfl⟩ : syracuseStep 2871497 = 2153623) B2153623
theorem B3404065 : Blo 1342990 3404065 := bstep (se 2 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 3404065 = 2553049) B2553049
theorem B2552123 : Blo 1342990 2552123 := bstep (se 1 (by rfl) ⟨1914092, by rfl⟩ : syracuseStep 2552123 = 3828185) B3828185
theorem B14373179 : Blo 1342990 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B8606087 : Blo 1342990 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B1511815 : Blo 1342990 1511815 := bstep (se 1 (by rfl) ⟨1133861, by rfl⟩ : syracuseStep 1511815 = 2267723) B2267723
theorem B6459851 : Blo 1342990 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B2724367 : Blo 1342990 2724367 := bstep (se 1 (by rfl) ⟨2043275, by rfl⟩ : syracuseStep 2724367 = 4086551) B4086551
theorem B1511995 : Blo 1342990 1511995 := bstep (se 1 (by rfl) ⟨1133996, by rfl⟩ : syracuseStep 1511995 = 2267993) B2267993
theorem B6804161 : Blo 1342990 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B1913591 : Blo 1342990 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B4084481 : Blo 1342990 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1700615 : Blo 1342990 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B2552609 : Blo 1342990 2552609 := bstep (se 2 (by rfl) ⟨957228, by rfl⟩ : syracuseStep 2552609 = 1914457) B1914457
theorem B31462181 : Blo 1342990 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B4305811 : Blo 1342990 4305811 := bstep (se 1 (by rfl) ⟨3229358, by rfl⟩ : syracuseStep 4305811 = 6458717) B6458717
theorem B1512463 : Blo 1342990 1512463 := bstep (se 1 (by rfl) ⟨1134347, by rfl⟩ : syracuseStep 1512463 = 2268695) B2268695
theorem B2552951 : Blo 1342990 2552951 := bstep (se 1 (by rfl) ⟨1914713, by rfl⟩ : syracuseStep 2552951 = 3829427) B3829427
theorem B4535567 : Blo 1342990 4535567 := bstep (se 1 (by rfl) ⟨3401675, by rfl⟩ : syracuseStep 4535567 = 6803351) B6803351
theorem B2266427 : Blo 1342990 2266427 := bstep (se 1 (by rfl) ⟨1699820, by rfl⟩ : syracuseStep 2266427 = 3399641) B3399641
theorem B1701263 : Blo 1342990 1701263 := bstep (se 1 (by rfl) ⟨1275947, by rfl⟩ : syracuseStep 1701263 = 2551895) B2551895
theorem B18388433 : Blo 1342990 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B1512967 : Blo 1342990 1512967 := bstep (se 1 (by rfl) ⟨1134725, by rfl⟩ : syracuseStep 1512967 = 2269451) B2269451
theorem B4535837 : Blo 1342990 4535837 := bstep (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) B1700939
theorem B7648829 : Blo 1342990 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B3880507 : Blo 1342990 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B53106353 : Blo 1342990 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B2266825 : Blo 1342990 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B2422561 : Blo 1342990 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B14931863 : Blo 1342990 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B8845259 : Blo 1342990 8845259 := bstep (se 1 (by rfl) ⟨6633944, by rfl⟩ : syracuseStep 8845259 = 13267889) B13267889
theorem B6805457 : Blo 1342990 6805457 := bstep (se 2 (by rfl) ⟨2552046, by rfl⟩ : syracuseStep 6805457 = 5104093) B5104093
theorem B26171437 : Blo 1342990 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B82810997 : Blo 1342990 82810997 := bstep (se 5 (by rfl) ⟨3881765, by rfl⟩ : syracuseStep 82810997 = 7763531) B7763531
theorem B1915015 : Blo 1342990 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B2300089 : Blo 1342990 2300089 := bstep (se 2 (by rfl) ⟨862533, by rfl⟩ : syracuseStep 2300089 = 1725067) B1725067
theorem B1816763 : Blo 1342990 1816763 := bstep (se 1 (by rfl) ⟨1362572, by rfl⟩ : syracuseStep 1816763 = 2725145) B2725145
theorem B2267527 : Blo 1342990 2267527 := bstep (se 1 (by rfl) ⟨1700645, by rfl⟩ : syracuseStep 2267527 = 3401291) B3401291
theorem B29047187 : Blo 1342990 29047187 := bstep (se 1 (by rfl) ⟨21785390, by rfl⟩ : syracuseStep 29047187 = 43570781) B43570781
theorem B17218115 : Blo 1342990 17218115 := bstep (se 1 (by rfl) ⟨12913586, by rfl⟩ : syracuseStep 17218115 = 25827173) B25827173
theorem B1841935 : Blo 1342990 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B12254003 : Blo 1342990 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B3824471 : Blo 1342990 3824471 := bstep (se 1 (by rfl) ⟨2868353, by rfl⟩ : syracuseStep 3824471 = 5736707) B5736707
theorem B4537241 : Blo 1342990 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B3021839 : Blo 1342990 3021839 := bstep (se 1 (by rfl) ⟨2266379, by rfl⟩ : syracuseStep 3021839 = 4532759) B4532759
theorem B2268175 : Blo 1342990 2268175 := bstep (se 1 (by rfl) ⟨1701131, by rfl⟩ : syracuseStep 2268175 = 3402263) B3402263
theorem B5102621 : Blo 1342990 5102621 := bstep (se 3 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 5102621 = 1913483) B1913483
theorem B3021857 : Blo 1342990 3021857 := bstep (se 2 (by rfl) ⟨1133196, by rfl⟩ : syracuseStep 3021857 = 2266393) B2266393
theorem B5102635 : Blo 1342990 5102635 := bstep (se 1 (by rfl) ⟨3826976, by rfl⟩ : syracuseStep 5102635 = 7653953) B7653953
theorem B6454333 : Blo 1342990 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B2014523 : Blo 1342990 2014523 := bstep (se 1 (by rfl) ⟨1510892, by rfl⟩ : syracuseStep 2014523 = 3021785) B3021785
theorem B67198267 : Blo 1342990 67198267 := bstep (se 1 (by rfl) ⟨50398700, by rfl⟩ : syracuseStep 67198267 = 100797401) B100797401
theorem B1940809 : Blo 1342990 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B2014583 : Blo 1342990 2014583 := bstep (se 1 (by rfl) ⟨1510937, by rfl⟩ : syracuseStep 2014583 = 3021875) B3021875
theorem B3022199 : Blo 1342990 3022199 := bstep (se 1 (by rfl) ⟨2266649, by rfl⟩ : syracuseStep 3022199 = 4533299) B4533299
theorem B2014607 : Blo 1342990 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B3227033 : Blo 1342990 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B2014649 : Blo 1342990 2014649 := bstep (se 2 (by rfl) ⟨755493, by rfl⟩ : syracuseStep 2014649 = 1510987) B1510987
theorem B7265795 : Blo 1342990 7265795 := bstep (se 1 (by rfl) ⟨5449346, by rfl⟩ : syracuseStep 7265795 = 10898693) B10898693
theorem B2014727 : Blo 1342990 2014727 := bstep (se 1 (by rfl) ⟨1511045, by rfl⟩ : syracuseStep 2014727 = 3022091) B3022091
theorem B1342991 : Blo 1342990 1342991 := bstep (se 1 (by rfl) ⟨1007243, by rfl⟩ : syracuseStep 1342991 = 2014487) B2014487
theorem B2014763 : Blo 1342990 2014763 := bstep (se 1 (by rfl) ⟨1511072, by rfl⟩ : syracuseStep 2014763 = 3022145) B3022145
theorem B3022379 : Blo 1342990 3022379 := bstep (se 1 (by rfl) ⟨2266784, by rfl⟩ : syracuseStep 3022379 = 4533569) B4533569
theorem B2268715 : Blo 1342990 2268715 := bstep (se 1 (by rfl) ⟨1701536, by rfl⟩ : syracuseStep 2268715 = 3403073) B3403073
theorem B1343035 : Blo 1342990 1343035 := bstep (se 1 (by rfl) ⟨1007276, by rfl⟩ : syracuseStep 1343035 = 2014553) B2014553
theorem B2014793 : Blo 1342990 2014793 := bstep (se 2 (by rfl) ⟨755547, by rfl⟩ : syracuseStep 2014793 = 1511095) B1511095
theorem B4537943 : Blo 1342990 4537943 := bstep (se 1 (by rfl) ⟨3403457, by rfl⟩ : syracuseStep 4537943 = 6806915) B6806915
theorem B1343111 : Blo 1342990 1343111 := bstep (se 1 (by rfl) ⟨1007333, by rfl⟩ : syracuseStep 1343111 = 2014667) B2014667
theorem B1343119 : Blo 1342990 1343119 := bstep (se 1 (by rfl) ⟨1007339, by rfl⟩ : syracuseStep 1343119 = 2014679) B2014679
theorem B2268857 : Blo 1342990 2268857 := bstep (se 2 (by rfl) ⟨850821, by rfl⟩ : syracuseStep 2268857 = 1701643) B1701643
theorem B1343163 : Blo 1342990 1343163 := bstep (se 1 (by rfl) ⟨1007372, by rfl⟩ : syracuseStep 1343163 = 2014745) B2014745
theorem B2014907 : Blo 1342990 2014907 := bstep (se 1 (by rfl) ⟨1511180, by rfl⟩ : syracuseStep 2014907 = 3022361) B3022361
theorem B2014967 : Blo 1342990 2014967 := bstep (se 1 (by rfl) ⟨1511225, by rfl⟩ : syracuseStep 2014967 = 3022451) B3022451
theorem B1343239 : Blo 1342990 1343239 := bstep (se 1 (by rfl) ⟨1007429, by rfl⟩ : syracuseStep 1343239 = 2014859) B2014859
theorem B1343247 : Blo 1342990 1343247 := bstep (se 1 (by rfl) ⟨1007435, by rfl⟩ : syracuseStep 1343247 = 2014871) B2014871
theorem B2014991 : Blo 1342990 2014991 := bstep (se 1 (by rfl) ⟨1511243, by rfl⟩ : syracuseStep 2014991 = 3022487) B3022487
theorem B2015033 : Blo 1342990 2015033 := bstep (se 2 (by rfl) ⟨755637, by rfl⟩ : syracuseStep 2015033 = 1511275) B1511275
theorem B1343291 : Blo 1342990 1343291 := bstep (se 1 (by rfl) ⟨1007468, by rfl⟩ : syracuseStep 1343291 = 2014937) B2014937
theorem B8609651 : Blo 1342990 8609651 := bstep (se 1 (by rfl) ⟨6457238, by rfl⟩ : syracuseStep 8609651 = 12914477) B12914477
theorem B1343367 : Blo 1342990 1343367 := bstep (se 1 (by rfl) ⟨1007525, by rfl⟩ : syracuseStep 1343367 = 2015051) B2015051
theorem B2015111 : Blo 1342990 2015111 := bstep (se 1 (by rfl) ⟨1511333, by rfl⟩ : syracuseStep 2015111 = 3022667) B3022667
theorem B1343375 : Blo 1342990 1343375 := bstep (se 1 (by rfl) ⟨1007531, by rfl⟩ : syracuseStep 1343375 = 2015063) B2015063
theorem B7651219 : Blo 1342990 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B3022739 : Blo 1342990 3022739 := bstep (se 1 (by rfl) ⟨2267054, by rfl⟩ : syracuseStep 3022739 = 4534109) B4534109
theorem B2015147 : Blo 1342990 2015147 := bstep (se 1 (by rfl) ⟨1511360, by rfl⟩ : syracuseStep 2015147 = 3022721) B3022721
theorem B1343419 : Blo 1342990 1343419 := bstep (se 1 (by rfl) ⟨1007564, by rfl⟩ : syracuseStep 1343419 = 2015129) B2015129
theorem B2015177 : Blo 1342990 2015177 := bstep (se 2 (by rfl) ⟨755691, by rfl⟩ : syracuseStep 2015177 = 1511383) B1511383
theorem B3022793 : Blo 1342990 3022793 := bstep (se 2 (by rfl) ⟨1133547, by rfl⟩ : syracuseStep 3022793 = 2267095) B2267095
theorem B39264203 : Blo 1342990 39264203 := bstep (se 1 (by rfl) ⟨29448152, by rfl⟩ : syracuseStep 39264203 = 58896305) B58896305
theorem B7659467 : Blo 1342990 7659467 := bstep (se 1 (by rfl) ⟨5744600, by rfl⟩ : syracuseStep 7659467 = 11489201) B11489201
theorem B4538375 : Blo 1342990 4538375 := bstep (se 1 (by rfl) ⟨3403781, by rfl⟩ : syracuseStep 4538375 = 6807563) B6807563
theorem B5447695 : Blo 1342990 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B1343527 : Blo 1342990 1343527 := bstep (se 1 (by rfl) ⟨1007645, by rfl⟩ : syracuseStep 1343527 = 2015291) B2015291
theorem B3227705 : Blo 1342990 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B1343567 : Blo 1342990 1343567 := bstep (se 1 (by rfl) ⟨1007675, by rfl⟩ : syracuseStep 1343567 = 2015351) B2015351
theorem B1343583 : Blo 1342990 1343583 := bstep (se 1 (by rfl) ⟨1007687, by rfl⟩ : syracuseStep 1343583 = 2015375) B2015375
theorem B4538483 : Blo 1342990 4538483 := bstep (se 1 (by rfl) ⟨3403862, by rfl⟩ : syracuseStep 4538483 = 6807725) B6807725
theorem B1343611 : Blo 1342990 1343611 := bstep (se 1 (by rfl) ⟨1007708, by rfl⟩ : syracuseStep 1343611 = 2015417) B2015417
theorem B1343663 : Blo 1342990 1343663 := bstep (se 1 (by rfl) ⟨1007747, by rfl⟩ : syracuseStep 1343663 = 2015495) B2015495
theorem B1343687 : Blo 1342990 1343687 := bstep (se 1 (by rfl) ⟨1007765, by rfl⟩ : syracuseStep 1343687 = 2015531) B2015531
theorem B1343707 : Blo 1342990 1343707 := bstep (se 1 (by rfl) ⟨1007780, by rfl⟩ : syracuseStep 1343707 = 2015561) B2015561
theorem B1343783 : Blo 1342990 1343783 := bstep (se 1 (by rfl) ⟨1007837, by rfl⟩ : syracuseStep 1343783 = 2015675) B2015675
theorem B1343823 : Blo 1342990 1343823 := bstep (se 1 (by rfl) ⟨1007867, by rfl⟩ : syracuseStep 1343823 = 2015735) B2015735
theorem B1343839 : Blo 1342990 1343839 := bstep (se 1 (by rfl) ⟨1007879, by rfl⟩ : syracuseStep 1343839 = 2015759) B2015759
theorem B1343867 : Blo 1342990 1343867 := bstep (se 1 (by rfl) ⟨1007900, by rfl⟩ : syracuseStep 1343867 = 2015801) B2015801
theorem B4538753 : Blo 1342990 4538753 := bstep (se 2 (by rfl) ⟨1702032, by rfl⟩ : syracuseStep 4538753 = 3404065) B3404065
theorem B2015663 : Blo 1342990 2015663 := bstep (se 1 (by rfl) ⟨1511747, by rfl⟩ : syracuseStep 2015663 = 3023495) B3023495
theorem B1343919 : Blo 1342990 1343919 := bstep (se 1 (by rfl) ⟨1007939, by rfl⟩ : syracuseStep 1343919 = 2015879) B2015879
theorem B1343943 : Blo 1342990 1343943 := bstep (se 1 (by rfl) ⟨1007957, by rfl⟩ : syracuseStep 1343943 = 2015915) B2015915
theorem B1343963 : Blo 1342990 1343963 := bstep (se 1 (by rfl) ⟨1007972, by rfl⟩ : syracuseStep 1343963 = 2015945) B2015945
theorem B3023369 : Blo 1342990 3023369 := bstep (se 2 (by rfl) ⟨1133763, by rfl⟩ : syracuseStep 3023369 = 2267527) B2267527
theorem B2015753 : Blo 1342990 2015753 := bstep (se 2 (by rfl) ⟨755907, by rfl⟩ : syracuseStep 2015753 = 1511815) B1511815
theorem B2015783 : Blo 1342990 2015783 := bstep (se 1 (by rfl) ⟨1511837, by rfl⟩ : syracuseStep 2015783 = 3023675) B3023675
theorem B1344039 : Blo 1342990 1344039 := bstep (se 1 (by rfl) ⟨1008029, by rfl⟩ : syracuseStep 1344039 = 2016059) B2016059
theorem B1344079 : Blo 1342990 1344079 := bstep (se 1 (by rfl) ⟨1008059, by rfl⟩ : syracuseStep 1344079 = 2016119) B2016119
theorem B1344095 : Blo 1342990 1344095 := bstep (se 1 (by rfl) ⟨1008071, by rfl⟩ : syracuseStep 1344095 = 2016143) B2016143
theorem B3400289 : Blo 1342990 3400289 := bstep (se 2 (by rfl) ⟨1275108, by rfl⟩ : syracuseStep 3400289 = 2550217) B2550217
theorem B2015867 : Blo 1342990 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B1344123 : Blo 1342990 1344123 := bstep (se 1 (by rfl) ⟨1008092, by rfl⟩ : syracuseStep 1344123 = 2016185) B2016185
theorem B1344175 : Blo 1342990 1344175 := bstep (se 1 (by rfl) ⟨1008131, by rfl⟩ : syracuseStep 1344175 = 2016263) B2016263
theorem B1344199 : Blo 1342990 1344199 := bstep (se 1 (by rfl) ⟨1008149, by rfl⟩ : syracuseStep 1344199 = 2016299) B2016299
theorem B4842193 : Blo 1342990 4842193 := bstep (se 2 (by rfl) ⟨1815822, by rfl⟩ : syracuseStep 4842193 = 3631645) B3631645
theorem B1344219 : Blo 1342990 1344219 := bstep (se 1 (by rfl) ⟨1008164, by rfl⟩ : syracuseStep 1344219 = 2016329) B2016329
theorem B2015993 : Blo 1342990 2015993 := bstep (se 2 (by rfl) ⟨755997, by rfl⟩ : syracuseStep 2015993 = 1511995) B1511995
theorem B1344295 : Blo 1342990 1344295 := bstep (se 1 (by rfl) ⟨1008221, by rfl⟩ : syracuseStep 1344295 = 2016443) B2016443
theorem B1344335 : Blo 1342990 1344335 := bstep (se 1 (by rfl) ⟨1008251, by rfl⟩ : syracuseStep 1344335 = 2016503) B2016503
theorem B3023711 : Blo 1342990 3023711 := bstep (se 1 (by rfl) ⟨2267783, by rfl⟩ : syracuseStep 3023711 = 4535567) B4535567
theorem B2016095 : Blo 1342990 2016095 := bstep (se 1 (by rfl) ⟨1512071, by rfl⟩ : syracuseStep 2016095 = 3024143) B3024143
theorem B1344351 : Blo 1342990 1344351 := bstep (se 1 (by rfl) ⟨1008263, by rfl⟩ : syracuseStep 1344351 = 2016527) B2016527
theorem B2016107 : Blo 1342990 2016107 := bstep (se 1 (by rfl) ⟨1512080, by rfl⟩ : syracuseStep 2016107 = 3024161) B3024161
theorem B1344379 : Blo 1342990 1344379 := bstep (se 1 (by rfl) ⟨1008284, by rfl⟩ : syracuseStep 1344379 = 2016569) B2016569
theorem B1344431 : Blo 1342990 1344431 := bstep (se 1 (by rfl) ⟨1008323, by rfl⟩ : syracuseStep 1344431 = 2016647) B2016647
theorem B1344455 : Blo 1342990 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B1344475 : Blo 1342990 1344475 := bstep (se 1 (by rfl) ⟨1008356, by rfl⟩ : syracuseStep 1344475 = 2016713) B2016713
theorem B9192467 : Blo 1342990 9192467 := bstep (se 1 (by rfl) ⟨6894350, by rfl⟩ : syracuseStep 9192467 = 13788701) B13788701
theorem B3023891 : Blo 1342990 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B1344551 : Blo 1342990 1344551 := bstep (se 1 (by rfl) ⟨1008413, by rfl⟩ : syracuseStep 1344551 = 2016827) B2016827
theorem B6800435 : Blo 1342990 6800435 := bstep (se 1 (by rfl) ⟨5100326, by rfl⟩ : syracuseStep 6800435 = 10200653) B10200653
theorem B2016335 : Blo 1342990 2016335 := bstep (se 1 (by rfl) ⟨1512251, by rfl⟩ : syracuseStep 2016335 = 3024503) B3024503
theorem B1344591 : Blo 1342990 1344591 := bstep (se 1 (by rfl) ⟨1008443, by rfl⟩ : syracuseStep 1344591 = 2016887) B2016887
theorem B1344607 : Blo 1342990 1344607 := bstep (se 1 (by rfl) ⟨1008455, by rfl⟩ : syracuseStep 1344607 = 2016911) B2016911
theorem B1344635 : Blo 1342990 1344635 := bstep (se 1 (by rfl) ⟨1008476, by rfl⟩ : syracuseStep 1344635 = 2016953) B2016953
theorem B1344687 : Blo 1342990 1344687 := bstep (se 1 (by rfl) ⟨1008515, by rfl⟩ : syracuseStep 1344687 = 2017031) B2017031
theorem B2016455 : Blo 1342990 2016455 := bstep (se 1 (by rfl) ⟨1512341, by rfl⟩ : syracuseStep 2016455 = 3024683) B3024683
theorem B1344711 : Blo 1342990 1344711 := bstep (se 1 (by rfl) ⟨1008533, by rfl⟩ : syracuseStep 1344711 = 2017067) B2017067
theorem B1344731 : Blo 1342990 1344731 := bstep (se 1 (by rfl) ⟨1008548, by rfl⟩ : syracuseStep 1344731 = 2017097) B2017097
theorem B9954575 : Blo 1342990 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B8611109 : Blo 1342990 8611109 := bstep (se 4 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 8611109 = 1614583) B1614583
theorem B1344807 : Blo 1342990 1344807 := bstep (se 1 (by rfl) ⟨1008605, by rfl⟩ : syracuseStep 1344807 = 2017211) B2017211
theorem B1344847 : Blo 1342990 1344847 := bstep (se 1 (by rfl) ⟨1008635, by rfl⟩ : syracuseStep 1344847 = 2017271) B2017271
theorem B19375453 : Blo 1342990 19375453 := bstep (se 3 (by rfl) ⟨3632897, by rfl⟩ : syracuseStep 19375453 = 7265795) B7265795
theorem B1344863 : Blo 1342990 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B3024233 : Blo 1342990 3024233 := bstep (se 2 (by rfl) ⟨1134087, by rfl⟩ : syracuseStep 3024233 = 2268175) B2268175
theorem B2016617 : Blo 1342990 2016617 := bstep (se 2 (by rfl) ⟨756231, by rfl⟩ : syracuseStep 2016617 = 1512463) B1512463
theorem B1344891 : Blo 1342990 1344891 := bstep (se 1 (by rfl) ⟨1008668, by rfl⟩ : syracuseStep 1344891 = 2017337) B2017337
theorem B55207331 : Blo 1342990 55207331 := bstep (se 1 (by rfl) ⟨41405498, by rfl⟩ : syracuseStep 55207331 = 82810997) B82810997
theorem B1344943 : Blo 1342990 1344943 := bstep (se 1 (by rfl) ⟨1008707, by rfl⟩ : syracuseStep 1344943 = 2017415) B2017415
theorem B2016695 : Blo 1342990 2016695 := bstep (se 1 (by rfl) ⟨1512521, by rfl⟩ : syracuseStep 2016695 = 3025043) B3025043
theorem B1344967 : Blo 1342990 1344967 := bstep (se 1 (by rfl) ⟨1008725, by rfl⟩ : syracuseStep 1344967 = 2017451) B2017451
theorem B2016731 : Blo 1342990 2016731 := bstep (se 1 (by rfl) ⟨1512548, by rfl⟩ : syracuseStep 2016731 = 3025097) B3025097
theorem B1344987 : Blo 1342990 1344987 := bstep (se 1 (by rfl) ⟨1008740, by rfl⟩ : syracuseStep 1344987 = 2017481) B2017481
theorem B29074949 : Blo 1342990 29074949 := bstep (se 4 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 29074949 = 5451553) B5451553
theorem B10208915 : Blo 1342990 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B11478743 : Blo 1342990 11478743 := bstep (se 1 (by rfl) ⟨8609057, by rfl⟩ : syracuseStep 11478743 = 17218115) B17218115
theorem B8169335 : Blo 1342990 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B2549647 : Blo 1342990 2549647 := bstep (se 1 (by rfl) ⟨1912235, by rfl⟩ : syracuseStep 2549647 = 3824471) B3824471
theorem B29452193 : Blo 1342990 29452193 := bstep (se 2 (by rfl) ⟨11044572, by rfl⟩ : syracuseStep 29452193 = 22089145) B22089145
theorem B2017199 : Blo 1342990 2017199 := bstep (se 1 (by rfl) ⟨1512899, by rfl⟩ : syracuseStep 2017199 = 3025799) B3025799
theorem B3229627 : Blo 1342990 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B3024827 : Blo 1342990 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B2017289 : Blo 1342990 2017289 := bstep (se 2 (by rfl) ⟨756483, by rfl⟩ : syracuseStep 2017289 = 1512967) B1512967
theorem B3401747 : Blo 1342990 3401747 := bstep (se 1 (by rfl) ⟨2551310, by rfl⟩ : syracuseStep 3401747 = 5102621) B5102621
theorem B2017319 : Blo 1342990 2017319 := bstep (se 1 (by rfl) ⟨1512989, by rfl⟩ : syracuseStep 2017319 = 3025979) B3025979
theorem B3024953 : Blo 1342990 3024953 := bstep (se 2 (by rfl) ⟨1134357, by rfl⟩ : syracuseStep 3024953 = 2268715) B2268715
theorem B2017403 : Blo 1342990 2017403 := bstep (se 1 (by rfl) ⟨1513052, by rfl⟩ : syracuseStep 2017403 = 3026105) B3026105
theorem B10905961 : Blo 1342990 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B3230081 : Blo 1342990 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B3025295 : Blo 1342990 3025295 := bstep (se 1 (by rfl) ⟨2268971, by rfl⟩ : syracuseStep 3025295 = 4537943) B4537943
theorem B10201625 : Blo 1342990 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B23587357 : Blo 1342990 23587357 := bstep (se 3 (by rfl) ⟨4422629, by rfl⟩ : syracuseStep 23587357 = 8845259) B8845259
theorem B3066491 : Blo 1342990 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B26176135 : Blo 1342990 26176135 := bstep (se 1 (by rfl) ⟨19632101, by rfl⟩ : syracuseStep 26176135 = 39264203) B39264203
theorem B6802055 : Blo 1342990 6802055 := bstep (se 1 (by rfl) ⟨5101541, by rfl⟩ : syracuseStep 6802055 = 10203083) B10203083
theorem B5106311 : Blo 1342990 5106311 := bstep (se 1 (by rfl) ⟨3829733, by rfl⟩ : syracuseStep 5106311 = 7659467) B7659467
theorem B21809843 : Blo 1342990 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B4532921 : Blo 1342990 4532921 := bstep (se 2 (by rfl) ⟨1699845, by rfl⟩ : syracuseStep 4532921 = 3399691) B3399691
theorem B5737169 : Blo 1342990 5737169 := bstep (se 2 (by rfl) ⟨2151438, by rfl⟩ : syracuseStep 5737169 = 4302877) B4302877
theorem B5171921 : Blo 1342990 5171921 := bstep (se 2 (by rfl) ⟨1939470, by rfl⟩ : syracuseStep 5171921 = 3878941) B3878941
theorem B3025619 : Blo 1342990 3025619 := bstep (se 1 (by rfl) ⟨2269214, by rfl⟩ : syracuseStep 3025619 = 4538429) B4538429
theorem B4975319 : Blo 1342990 4975319 := bstep (se 1 (by rfl) ⟨3731489, by rfl⟩ : syracuseStep 4975319 = 7462979) B7462979
theorem B2550521 : Blo 1342990 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B3066785 : Blo 1342990 3066785 := bstep (se 2 (by rfl) ⟨1150044, by rfl⟩ : syracuseStep 3066785 = 2300089) B2300089
theorem B5737391 : Blo 1342990 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B2550703 : Blo 1342990 2550703 := bstep (se 1 (by rfl) ⟨1913027, by rfl⟩ : syracuseStep 2550703 = 3826055) B3826055
theorem B4844701 : Blo 1342990 4844701 := bstep (se 3 (by rfl) ⟨908381, by rfl⟩ : syracuseStep 4844701 = 1816763) B1816763
theorem B2722987 : Blo 1342990 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B20974787 : Blo 1342990 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B4304119 : Blo 1342990 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B4533515 : Blo 1342990 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3632489 : Blo 1342990 3632489 := bstep (se 2 (by rfl) ⟨1362183, by rfl⟩ : syracuseStep 3632489 = 2724367) B2724367
theorem B4533785 : Blo 1342990 4533785 := bstep (se 2 (by rfl) ⟨1700169, by rfl⟩ : syracuseStep 4533785 = 3400339) B3400339
theorem B1510951 : Blo 1342990 1510951 := bstep (se 1 (by rfl) ⟨1133213, by rfl⟩ : syracuseStep 1510951 = 2266427) B2266427
theorem B12258955 : Blo 1342990 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B5099219 : Blo 1342990 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B3632855 : Blo 1342990 3632855 := bstep (se 1 (by rfl) ⟨2724641, by rfl⟩ : syracuseStep 3632855 = 5449283) B5449283
theorem B4304735 : Blo 1342990 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B2043743 : Blo 1342990 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B6803513 : Blo 1342990 6803513 := bstep (se 2 (by rfl) ⟨2551317, by rfl⟩ : syracuseStep 6803513 = 5102635) B5102635
theorem B8605777 : Blo 1342990 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B11481203 : Blo 1342990 11481203 := bstep (se 1 (by rfl) ⟨8610902, by rfl⟩ : syracuseStep 11481203 = 17221805) B17221805
theorem B10891427 : Blo 1342990 10891427 := bstep (se 1 (by rfl) ⟨8168570, by rfl⟩ : syracuseStep 10891427 = 16337141) B16337141
theorem B2551979 : Blo 1342990 2551979 := bstep (se 1 (by rfl) ⟨1913984, by rfl⟩ : syracuseStep 2551979 = 3827969) B3827969
theorem B4846043 : Blo 1342990 4846043 := bstep (se 1 (by rfl) ⟨3634532, by rfl⟩ : syracuseStep 4846043 = 7269065) B7269065
theorem B4534919 : Blo 1342990 4534919 := bstep (se 1 (by rfl) ⟨3401189, by rfl⟩ : syracuseStep 4534919 = 6802379) B6802379
theorem B4534973 : Blo 1342990 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B5174009 : Blo 1342990 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B4535135 : Blo 1342990 4535135 := bstep (se 1 (by rfl) ⟨3401351, by rfl⟩ : syracuseStep 4535135 = 6802703) B6802703
theorem B2151355 : Blo 1342990 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B10212317 : Blo 1342990 10212317 := bstep (se 3 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 10212317 = 3829619) B3829619
theorem B4535297 : Blo 1342990 4535297 := bstep (se 2 (by rfl) ⟨1700736, by rfl⟩ : syracuseStep 4535297 = 3401473) B3401473
theorem B10892339 : Blo 1342990 10892339 := bstep (se 1 (by rfl) ⟨8169254, by rfl⟩ : syracuseStep 10892339 = 16338509) B16338509
theorem B1512571 : Blo 1342990 1512571 := bstep (se 1 (by rfl) ⟨1134428, by rfl⟩ : syracuseStep 1512571 = 2268857) B2268857
theorem B5739767 : Blo 1342990 5739767 := bstep (se 1 (by rfl) ⟨4304825, by rfl⟩ : syracuseStep 5739767 = 8609651) B8609651
theorem B2725193 : Blo 1342990 2725193 := bstep (se 2 (by rfl) ⟨1021947, by rfl⟩ : syracuseStep 2725193 = 2043895) B2043895
theorem B10204541 : Blo 1342990 10204541 := bstep (se 3 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 10204541 = 3826703) B3826703
theorem B34895249 : Blo 1342990 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B7656869 : Blo 1342990 7656869 := bstep (se 4 (by rfl) ⟨717831, by rfl⟩ : syracuseStep 7656869 = 1435663) B1435663
theorem B2266555 : Blo 1342990 2266555 := bstep (se 1 (by rfl) ⟨1699916, by rfl⟩ : syracuseStep 2266555 = 3399833) B3399833
theorem B2299355 : Blo 1342990 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B2553353 : Blo 1342990 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B2266663 : Blo 1342990 2266663 := bstep (se 1 (by rfl) ⟨1699997, by rfl⟩ : syracuseStep 2266663 = 3399995) B3399995
theorem B1701415 : Blo 1342990 1701415 := bstep (se 1 (by rfl) ⟨1276061, by rfl⟩ : syracuseStep 1701415 = 2552123) B2552123
theorem B9582119 : Blo 1342990 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1513039 : Blo 1342990 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B49747607 : Blo 1342990 49747607 := bstep (se 1 (by rfl) ⟨37310705, by rfl⟩ : syracuseStep 49747607 = 74621411) B74621411
theorem B11646713 : Blo 1342990 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B4536107 : Blo 1342990 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B2266987 : Blo 1342990 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B1701739 : Blo 1342990 1701739 := bstep (se 1 (by rfl) ⟨1276304, by rfl⟩ : syracuseStep 1701739 = 2552609) B2552609
theorem B7657325 : Blo 1342990 7657325 := bstep (se 3 (by rfl) ⟨1435748, by rfl⟩ : syracuseStep 7657325 = 2871497) B2871497
theorem B1595431 : Blo 1342990 1595431 := bstep (se 1 (by rfl) ⟨1196573, by rfl⟩ : syracuseStep 1595431 = 2393147) B2393147
theorem B4536377 : Blo 1342990 4536377 := bstep (se 2 (by rfl) ⟨1701141, by rfl⟩ : syracuseStep 4536377 = 3402283) B3402283
theorem B1701967 : Blo 1342990 1701967 := bstep (se 1 (by rfl) ⟨1276475, by rfl⟩ : syracuseStep 1701967 = 2552951) B2552951
theorem B5101649 : Blo 1342990 5101649 := bstep (se 2 (by rfl) ⟨1913118, by rfl⟩ : syracuseStep 5101649 = 3826237) B3826237
theorem B6805619 : Blo 1342990 6805619 := bstep (se 1 (by rfl) ⟨5104214, by rfl⟩ : syracuseStep 6805619 = 10208429) B10208429
theorem B2455913 : Blo 1342990 2455913 := bstep (se 2 (by rfl) ⟨920967, by rfl⟩ : syracuseStep 2455913 = 1841935) B1841935
theorem B4536701 : Blo 1342990 4536701 := bstep (se 3 (by rfl) ⟨850631, by rfl⟩ : syracuseStep 4536701 = 1701263) B1701263
theorem B5101967 : Blo 1342990 5101967 := bstep (se 1 (by rfl) ⟨3826475, by rfl⟩ : syracuseStep 5101967 = 7652951) B7652951
theorem B35404235 : Blo 1342990 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B5741081 : Blo 1342990 5741081 := bstep (se 2 (by rfl) ⟨2152905, by rfl⟩ : syracuseStep 5741081 = 4305811) B4305811
theorem B7658009 : Blo 1342990 7658009 := bstep (se 2 (by rfl) ⟨2871753, by rfl⟩ : syracuseStep 7658009 = 5743507) B5743507
theorem B17226269 : Blo 1342990 17226269 := bstep (se 3 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 17226269 = 6459851) B6459851
theorem B17947271 : Blo 1342990 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B4536971 : Blo 1342990 4536971 := bstep (se 1 (by rfl) ⟨3402728, by rfl⟩ : syracuseStep 4536971 = 6805457) B6805457
theorem B2268047 : Blo 1342990 2268047 := bstep (se 1 (by rfl) ⟨1701035, by rfl⟩ : syracuseStep 2268047 = 3402071) B3402071
theorem B19364791 : Blo 1342990 19364791 := bstep (se 1 (by rfl) ⟨14523593, by rfl⟩ : syracuseStep 19364791 = 29047187) B29047187
theorem B358390757 : Blo 1342990 358390757 := bstep (se 4 (by rfl) ⟨33599133, by rfl⟩ : syracuseStep 358390757 = 67198267) B67198267
theorem B2587745 : Blo 1342990 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B2268283 : Blo 1342990 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B9198839 : Blo 1342990 9198839 := bstep (se 1 (by rfl) ⟨6899129, by rfl⟩ : syracuseStep 9198839 = 13798259) B13798259
theorem B5102909 : Blo 1342990 5102909 := bstep (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) B1913591
theorem B2014559 : Blo 1342990 2014559 := bstep (se 1 (by rfl) ⟨1510919, by rfl⟩ : syracuseStep 2014559 = 3021839) B3021839
theorem B2014571 : Blo 1342990 2014571 := bstep (se 1 (by rfl) ⟨1510928, by rfl⟩ : syracuseStep 2014571 = 3021857) B3021857
theorem B4308349 : Blo 1342990 4308349 := bstep (se 3 (by rfl) ⟨807815, by rfl⟩ : syracuseStep 4308349 = 1615631) B1615631
theorem B82730417 : Blo 1342990 82730417 := bstep (se 2 (by rfl) ⟨31023906, by rfl⟩ : syracuseStep 82730417 = 62047813) B62047813
theorem B4537889 : Blo 1342990 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B1343015 : Blo 1342990 1343015 := bstep (se 1 (by rfl) ⟨1007261, by rfl⟩ : syracuseStep 1343015 = 2014523) B2014523
theorem B1343055 : Blo 1342990 1343055 := bstep (se 1 (by rfl) ⟨1007291, by rfl⟩ : syracuseStep 1343055 = 2014583) B2014583
theorem B2014799 : Blo 1342990 2014799 := bstep (se 1 (by rfl) ⟨1511099, by rfl⟩ : syracuseStep 2014799 = 3022199) B3022199
theorem B1343071 : Blo 1342990 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B3022433 : Blo 1342990 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B1343099 : Blo 1342990 1343099 := bstep (se 1 (by rfl) ⟨1007324, by rfl⟩ : syracuseStep 1343099 = 2014649) B2014649
theorem B1343151 : Blo 1342990 1343151 := bstep (se 1 (by rfl) ⟨1007363, by rfl⟩ : syracuseStep 1343151 = 2014727) B2014727
theorem B1343175 : Blo 1342990 1343175 := bstep (se 1 (by rfl) ⟨1007381, by rfl⟩ : syracuseStep 1343175 = 2014763) B2014763
theorem B2014919 : Blo 1342990 2014919 := bstep (se 1 (by rfl) ⟨1511189, by rfl⟩ : syracuseStep 2014919 = 3022379) B3022379
theorem B6807239 : Blo 1342990 6807239 := bstep (se 1 (by rfl) ⟨5105429, by rfl⟩ : syracuseStep 6807239 = 10210859) B10210859
theorem B1343195 : Blo 1342990 1343195 := bstep (se 1 (by rfl) ⟨1007396, by rfl⟩ : syracuseStep 1343195 = 2014793) B2014793
theorem B7651037 : Blo 1342990 7651037 := bstep (se 3 (by rfl) ⟨1434569, by rfl⟩ : syracuseStep 7651037 = 2869139) B2869139
theorem B34889453 : Blo 1342990 34889453 := bstep (se 3 (by rfl) ⟨6541772, by rfl⟩ : syracuseStep 34889453 = 13083545) B13083545
theorem B4538105 : Blo 1342990 4538105 := bstep (se 2 (by rfl) ⟨1701789, by rfl⟩ : syracuseStep 4538105 = 3403579) B3403579
theorem B1343271 : Blo 1342990 1343271 := bstep (se 1 (by rfl) ⟨1007453, by rfl⟩ : syracuseStep 1343271 = 2014907) B2014907
theorem B1343311 : Blo 1342990 1343311 := bstep (se 1 (by rfl) ⟨1007483, by rfl⟩ : syracuseStep 1343311 = 2014967) B2014967
theorem B1343327 : Blo 1342990 1343327 := bstep (se 1 (by rfl) ⟨1007495, by rfl⟩ : syracuseStep 1343327 = 2014991) B2014991
theorem B2015081 : Blo 1342990 2015081 := bstep (se 2 (by rfl) ⟨755655, by rfl⟩ : syracuseStep 2015081 = 1511311) B1511311
theorem B5447533 : Blo 1342990 5447533 := bstep (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) B2042825
theorem B1343355 : Blo 1342990 1343355 := bstep (se 1 (by rfl) ⟨1007516, by rfl⟩ : syracuseStep 1343355 = 2015033) B2015033
theorem B1343407 : Blo 1342990 1343407 := bstep (se 1 (by rfl) ⟨1007555, by rfl⟩ : syracuseStep 1343407 = 2015111) B2015111
theorem B2015159 : Blo 1342990 2015159 := bstep (se 1 (by rfl) ⟨1511369, by rfl⟩ : syracuseStep 2015159 = 3022739) B3022739
theorem B3022775 : Blo 1342990 3022775 := bstep (se 1 (by rfl) ⟨2267081, by rfl⟩ : syracuseStep 3022775 = 4534163) B4534163
theorem B1343431 : Blo 1342990 1343431 := bstep (se 1 (by rfl) ⟨1007573, by rfl⟩ : syracuseStep 1343431 = 2015147) B2015147
theorem B1343451 : Blo 1342990 1343451 := bstep (se 1 (by rfl) ⟨1007588, by rfl⟩ : syracuseStep 1343451 = 2015177) B2015177
theorem B2015195 : Blo 1342990 2015195 := bstep (se 1 (by rfl) ⟨1511396, by rfl⟩ : syracuseStep 2015195 = 3022793) B3022793
theorem B2269147 : Blo 1342990 2269147 := bstep (se 1 (by rfl) ⟨1701860, by rfl⟩ : syracuseStep 2269147 = 3403721) B3403721
theorem B2269289 : Blo 1342990 2269289 := bstep (se 2 (by rfl) ⟨850983, by rfl⟩ : syracuseStep 2269289 = 1701967) B1701967
theorem B1343775 : Blo 1342990 1343775 := bstep (se 1 (by rfl) ⟨1007831, by rfl⟩ : syracuseStep 1343775 = 2015663) B2015663
theorem B2015579 : Blo 1342990 2015579 := bstep (se 1 (by rfl) ⟨1511684, by rfl⟩ : syracuseStep 2015579 = 3023369) B3023369
theorem B1343835 : Blo 1342990 1343835 := bstep (se 1 (by rfl) ⟨1007876, by rfl⟩ : syracuseStep 1343835 = 2015753) B2015753
theorem B1343855 : Blo 1342990 1343855 := bstep (se 1 (by rfl) ⟨1007891, by rfl⟩ : syracuseStep 1343855 = 2015783) B2015783
theorem B1343911 : Blo 1342990 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B3023279 : Blo 1342990 3023279 := bstep (se 1 (by rfl) ⟨2267459, by rfl⟩ : syracuseStep 3023279 = 4534919) B4534919
theorem B3023315 : Blo 1342990 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B14541281 : Blo 1342990 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B1343995 : Blo 1342990 1343995 := bstep (se 1 (by rfl) ⟨1007996, by rfl⟩ : syracuseStep 1343995 = 2015993) B2015993
theorem B3449339 : Blo 1342990 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B3023423 : Blo 1342990 3023423 := bstep (se 1 (by rfl) ⟨2267567, by rfl⟩ : syracuseStep 3023423 = 4535135) B4535135
theorem B2015807 : Blo 1342990 2015807 := bstep (se 1 (by rfl) ⟨1511855, by rfl⟩ : syracuseStep 2015807 = 3023711) B3023711
theorem B1344063 : Blo 1342990 1344063 := bstep (se 1 (by rfl) ⟨1008047, by rfl⟩ : syracuseStep 1344063 = 2016095) B2016095
theorem B1344071 : Blo 1342990 1344071 := bstep (se 1 (by rfl) ⟨1008053, by rfl⟩ : syracuseStep 1344071 = 2016107) B2016107
theorem B6808211 : Blo 1342990 6808211 := bstep (se 1 (by rfl) ⟨5106158, by rfl⟩ : syracuseStep 6808211 = 10212317) B10212317
theorem B3023531 : Blo 1342990 3023531 := bstep (se 1 (by rfl) ⟨2267648, by rfl⟩ : syracuseStep 3023531 = 4535297) B4535297
theorem B6128311 : Blo 1342990 6128311 := bstep (se 1 (by rfl) ⟨4596233, by rfl⟩ : syracuseStep 6128311 = 9192467) B9192467
theorem B2015927 : Blo 1342990 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B31449809 : Blo 1342990 31449809 := bstep (se 2 (by rfl) ⟨11793678, by rfl⟩ : syracuseStep 31449809 = 23587357) B23587357
theorem B1344223 : Blo 1342990 1344223 := bstep (se 1 (by rfl) ⟨1008167, by rfl⟩ : syracuseStep 1344223 = 2016335) B2016335
theorem B1344303 : Blo 1342990 1344303 := bstep (se 1 (by rfl) ⟨1008227, by rfl⟩ : syracuseStep 1344303 = 2016455) B2016455
theorem B3826511 : Blo 1342990 3826511 := bstep (se 1 (by rfl) ⟨2869883, by rfl⟩ : syracuseStep 3826511 = 5739767) B5739767
theorem B6636383 : Blo 1342990 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B2016155 : Blo 1342990 2016155 := bstep (se 1 (by rfl) ⟨1512116, by rfl⟩ : syracuseStep 2016155 = 3024233) B3024233
theorem B1344411 : Blo 1342990 1344411 := bstep (se 1 (by rfl) ⟨1008308, by rfl⟩ : syracuseStep 1344411 = 2016617) B2016617
theorem B6456257 : Blo 1342990 6456257 := bstep (se 2 (by rfl) ⟨2421096, by rfl⟩ : syracuseStep 6456257 = 4842193) B4842193
theorem B5104579 : Blo 1342990 5104579 := bstep (se 1 (by rfl) ⟨3828434, by rfl⟩ : syracuseStep 5104579 = 7656869) B7656869
theorem B1344463 : Blo 1342990 1344463 := bstep (se 1 (by rfl) ⟨1008347, by rfl⟩ : syracuseStep 1344463 = 2016695) B2016695
theorem B1532903 : Blo 1342990 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1344487 : Blo 1342990 1344487 := bstep (se 1 (by rfl) ⟨1008365, by rfl⟩ : syracuseStep 1344487 = 2016731) B2016731
theorem B21799925 : Blo 1342990 21799925 := bstep (se 5 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 21799925 = 2043743) B2043743
theorem B19383299 : Blo 1342990 19383299 := bstep (se 1 (by rfl) ⟨14537474, by rfl⟩ : syracuseStep 19383299 = 29074949) B29074949
theorem B7652495 : Blo 1342990 7652495 := bstep (se 1 (by rfl) ⟨5739371, by rfl⟩ : syracuseStep 7652495 = 11478743) B11478743
theorem B3024071 : Blo 1342990 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B3400937 : Blo 1342990 3400937 := bstep (se 2 (by rfl) ⟨1275351, by rfl⟩ : syracuseStep 3400937 = 2550703) B2550703
theorem B5104883 : Blo 1342990 5104883 := bstep (se 1 (by rfl) ⟨3828662, by rfl⟩ : syracuseStep 5104883 = 7657325) B7657325
theorem B2868473 : Blo 1342990 2868473 := bstep (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) B2151355
theorem B1344799 : Blo 1342990 1344799 := bstep (se 1 (by rfl) ⟨1008599, by rfl⟩ : syracuseStep 1344799 = 2017199) B2017199
theorem B2016551 : Blo 1342990 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B1344859 : Blo 1342990 1344859 := bstep (se 1 (by rfl) ⟨1008644, by rfl⟩ : syracuseStep 1344859 = 2017289) B2017289
theorem B1344879 : Blo 1342990 1344879 := bstep (se 1 (by rfl) ⟨1008659, by rfl⟩ : syracuseStep 1344879 = 2017319) B2017319
theorem B3024251 : Blo 1342990 3024251 := bstep (se 1 (by rfl) ⟨2268188, by rfl⟩ : syracuseStep 3024251 = 4536377) B4536377
theorem B2016635 : Blo 1342990 2016635 := bstep (se 1 (by rfl) ⟨1512476, by rfl⟩ : syracuseStep 2016635 = 3024953) B3024953
theorem B3401099 : Blo 1342990 3401099 := bstep (se 1 (by rfl) ⟨2550824, by rfl⟩ : syracuseStep 3401099 = 5101649) B5101649
theorem B1344935 : Blo 1342990 1344935 := bstep (se 1 (by rfl) ⟨1008701, by rfl⟩ : syracuseStep 1344935 = 2017403) B2017403
theorem B3024377 : Blo 1342990 3024377 := bstep (se 2 (by rfl) ⟨1134141, by rfl⟩ : syracuseStep 3024377 = 2268283) B2268283
theorem B2016761 : Blo 1342990 2016761 := bstep (se 2 (by rfl) ⟨756285, by rfl⟩ : syracuseStep 2016761 = 1512571) B1512571
theorem B3024467 : Blo 1342990 3024467 := bstep (se 1 (by rfl) ⟨2268350, by rfl⟩ : syracuseStep 3024467 = 4536701) B4536701
theorem B3401311 : Blo 1342990 3401311 := bstep (se 1 (by rfl) ⟨2550983, by rfl⟩ : syracuseStep 3401311 = 5101967) B5101967
theorem B2016863 : Blo 1342990 2016863 := bstep (se 1 (by rfl) ⟨1512647, by rfl⟩ : syracuseStep 2016863 = 3025295) B3025295
theorem B23602823 : Blo 1342990 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B6801083 : Blo 1342990 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B3827387 : Blo 1342990 3827387 := bstep (se 1 (by rfl) ⟨2870540, by rfl⟩ : syracuseStep 3827387 = 5741081) B5741081
theorem B5105339 : Blo 1342990 5105339 := bstep (se 1 (by rfl) ⟨3829004, by rfl⟩ : syracuseStep 5105339 = 7658009) B7658009
theorem B3024647 : Blo 1342990 3024647 := bstep (se 1 (by rfl) ⟨2268485, by rfl⟩ : syracuseStep 3024647 = 4536971) B4536971
theorem B2017079 : Blo 1342990 2017079 := bstep (se 1 (by rfl) ⟨1512809, by rfl⟩ : syracuseStep 2017079 = 3025619) B3025619
theorem B5744465 : Blo 1342990 5744465 := bstep (se 2 (by rfl) ⟨2154174, by rfl⟩ : syracuseStep 5744465 = 4308349) B4308349
theorem B31057901 : Blo 1342990 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B2017385 : Blo 1342990 2017385 := bstep (se 2 (by rfl) ⟨756519, by rfl⟩ : syracuseStep 2017385 = 1513039) B1513039
theorem B16345273 : Blo 1342990 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B3401939 : Blo 1342990 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B3025259 : Blo 1342990 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B23259635 : Blo 1342990 23259635 := bstep (se 1 (by rfl) ⟨17444726, by rfl⟩ : syracuseStep 23259635 = 34889453) B34889453
theorem B3025403 : Blo 1342990 3025403 := bstep (se 1 (by rfl) ⟨2269052, by rfl⟩ : syracuseStep 3025403 = 4538105) B4538105
theorem B2869823 : Blo 1342990 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B3025529 : Blo 1342990 3025529 := bstep (se 2 (by rfl) ⟨1134573, by rfl⟩ : syracuseStep 3025529 = 2269147) B2269147
theorem B3025583 : Blo 1342990 3025583 := bstep (se 1 (by rfl) ⟨2269187, by rfl⟩ : syracuseStep 3025583 = 4538375) B4538375
theorem B7654135 : Blo 1342990 7654135 := bstep (se 1 (by rfl) ⟨5740601, by rfl⟩ : syracuseStep 7654135 = 11481203) B11481203
theorem B3025655 : Blo 1342990 3025655 := bstep (se 1 (by rfl) ⟨2269241, by rfl⟩ : syracuseStep 3025655 = 4538483) B4538483
theorem B3025835 : Blo 1342990 3025835 := bstep (se 1 (by rfl) ⟨2269376, by rfl⟩ : syracuseStep 3025835 = 4538753) B4538753
theorem B6900653 : Blo 1342990 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B3230695 : Blo 1342990 3230695 := bstep (se 1 (by rfl) ⟨2423021, by rfl⟩ : syracuseStep 3230695 = 4846043) B4846043
theorem B29043805 : Blo 1342990 29043805 := bstep (se 3 (by rfl) ⟨5445713, by rfl⟩ : syracuseStep 29043805 = 10891427) B10891427
theorem B7261559 : Blo 1342990 7261559 := bstep (se 1 (by rfl) ⟨5446169, by rfl⟩ : syracuseStep 7261559 = 10892339) B10892339
theorem B4533623 : Blo 1342990 4533623 := bstep (se 1 (by rfl) ⟨3400217, by rfl⟩ : syracuseStep 4533623 = 6800435) B6800435
theorem B34901513 : Blo 1342990 34901513 := bstep (se 2 (by rfl) ⟨13088067, by rfl⟩ : syracuseStep 34901513 = 26176135) B26176135
theorem B6803027 : Blo 1342990 6803027 := bstep (se 1 (by rfl) ⟨5102270, by rfl⟩ : syracuseStep 6803027 = 10204541) B10204541
theorem B33165071 : Blo 1342990 33165071 := bstep (se 1 (by rfl) ⟨24873803, by rfl⟩ : syracuseStep 33165071 = 49747607) B49747607
theorem B220614445 : Blo 1342990 220614445 := bstep (se 3 (by rfl) ⟨41365208, by rfl⟩ : syracuseStep 220614445 = 82730417) B82730417
theorem B6459601 : Blo 1342990 6459601 := bstep (se 2 (by rfl) ⟨2422350, by rfl⟩ : syracuseStep 6459601 = 4844701) B4844701
theorem B5738825 : Blo 1342990 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B2044327 : Blo 1342990 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B4534703 : Blo 1342990 4534703 := bstep (se 1 (by rfl) ⟨3401027, by rfl⟩ : syracuseStep 4534703 = 6802055) B6802055
theorem B11964847 : Blo 1342990 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B3404207 : Blo 1342990 3404207 := bstep (se 1 (by rfl) ⟨2553155, by rfl⟩ : syracuseStep 3404207 = 5106311) B5106311
theorem B25833937 : Blo 1342990 25833937 := bstep (se 2 (by rfl) ⟨9687726, by rfl⟩ : syracuseStep 25833937 = 19375453) B19375453
theorem B1700347 : Blo 1342990 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B9687613 : Blo 1342990 9687613 := bstep (se 3 (by rfl) ⟨1816427, by rfl⟩ : syracuseStep 9687613 = 3632855) B3632855
theorem B1512031 : Blo 1342990 1512031 := bstep (se 1 (by rfl) ⟨1134023, by rfl⟩ : syracuseStep 1512031 = 2268047) B2268047
theorem B2044523 : Blo 1342990 2044523 := bstep (se 1 (by rfl) ⟨1533392, by rfl⟩ : syracuseStep 2044523 = 3066785) B3066785
theorem B6132559 : Blo 1342990 6132559 := bstep (se 1 (by rfl) ⟨4599419, by rfl⟩ : syracuseStep 6132559 = 9198839) B9198839
theorem B2421659 : Blo 1342990 2421659 := bstep (se 1 (by rfl) ⟨1816244, by rfl⟩ : syracuseStep 2421659 = 3632489) B3632489
theorem B7263377 : Blo 1342990 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B5100691 : Blo 1342990 5100691 := bstep (se 1 (by rfl) ⟨3825518, by rfl⟩ : syracuseStep 5100691 = 7651037) B7651037
theorem B4306169 : Blo 1342990 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B7263593 : Blo 1342990 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B2151803 : Blo 1342990 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B4535675 : Blo 1342990 4535675 := bstep (se 1 (by rfl) ⟨3401756, by rfl⟩ : syracuseStep 4535675 = 6803513) B6803513
theorem B2127241 : Blo 1342990 2127241 := bstep (se 2 (by rfl) ⟨797715, by rfl⟩ : syracuseStep 2127241 = 1595431) B1595431
theorem B11474369 : Blo 1342990 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B1701319 : Blo 1342990 1701319 := bstep (se 1 (by rfl) ⟨1275989, by rfl⟩ : syracuseStep 1701319 = 2551979) B2551979
theorem B2266859 : Blo 1342990 2266859 := bstep (se 1 (by rfl) ⟨1700144, by rfl⟩ : syracuseStep 2266859 = 3400289) B3400289
theorem B5740739 : Blo 1342990 5740739 := bstep (se 1 (by rfl) ⟨4305554, by rfl⟩ : syracuseStep 5740739 = 8611109) B8611109
theorem B1816795 : Blo 1342990 1816795 := bstep (se 1 (by rfl) ⟨1362596, by rfl⟩ : syracuseStep 1816795 = 2725193) B2725193
theorem B14522597 : Blo 1342990 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B23263499 : Blo 1342990 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B36804887 : Blo 1342990 36804887 := bstep (se 1 (by rfl) ⟨27603665, by rfl⟩ : syracuseStep 36804887 = 55207331) B55207331
theorem B1702235 : Blo 1342990 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B6388079 : Blo 1342990 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B6805943 : Blo 1342990 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B25819721 : Blo 1342990 25819721 := bstep (se 2 (by rfl) ⟨9682395, by rfl⟩ : syracuseStep 25819721 = 19364791) B19364791
theorem B5446223 : Blo 1342990 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B19634795 : Blo 1342990 19634795 := bstep (se 1 (by rfl) ⟨14726096, by rfl⟩ : syracuseStep 19634795 = 29452193) B29452193
theorem B2267831 : Blo 1342990 2267831 := bstep (se 1 (by rfl) ⟨1700873, by rfl⟩ : syracuseStep 2267831 = 3401747) B3401747
theorem B4537079 : Blo 1342990 4537079 := bstep (se 1 (by rfl) ⟨3402809, by rfl⟩ : syracuseStep 4537079 = 6805619) B6805619
theorem B1637275 : Blo 1342990 1637275 := bstep (se 1 (by rfl) ⟨1227956, by rfl⟩ : syracuseStep 1637275 = 2455913) B2455913
theorem B2153387 : Blo 1342990 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B11484179 : Blo 1342990 11484179 := bstep (se 1 (by rfl) ⟨8613134, by rfl⟩ : syracuseStep 11484179 = 17226269) B17226269
theorem B14539895 : Blo 1342990 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B3021947 : Blo 1342990 3021947 := bstep (se 1 (by rfl) ⟨2266460, by rfl⟩ : syracuseStep 3021947 = 4532921) B4532921
theorem B3824779 : Blo 1342990 3824779 := bstep (se 1 (by rfl) ⟨2868584, by rfl⟩ : syracuseStep 3824779 = 5737169) B5737169
theorem B3447947 : Blo 1342990 3447947 := bstep (se 1 (by rfl) ⟨2585960, by rfl⟩ : syracuseStep 3447947 = 5171921) B5171921
theorem B3316879 : Blo 1342990 3316879 := bstep (se 1 (by rfl) ⟨2487659, by rfl⟩ : syracuseStep 3316879 = 4975319) B4975319
theorem B3022073 : Blo 1342990 3022073 := bstep (se 2 (by rfl) ⟨1133277, by rfl⟩ : syracuseStep 3022073 = 2266555) B2266555
theorem B3824927 : Blo 1342990 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B238927171 : Blo 1342990 238927171 := bstep (se 1 (by rfl) ⟨179195378, by rfl⟩ : syracuseStep 238927171 = 358390757) B358390757
theorem B2014601 : Blo 1342990 2014601 := bstep (se 2 (by rfl) ⟨755475, by rfl⟩ : syracuseStep 2014601 = 1510951) B1510951
theorem B3022217 : Blo 1342990 3022217 := bstep (se 2 (by rfl) ⟨1133331, by rfl⟩ : syracuseStep 3022217 = 2266663) B2266663
theorem B2268553 : Blo 1342990 2268553 := bstep (se 2 (by rfl) ⟨850707, by rfl⟩ : syracuseStep 2268553 = 1701415) B1701415
theorem B13983191 : Blo 1342990 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B3022343 : Blo 1342990 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B1343039 : Blo 1342990 1343039 := bstep (se 1 (by rfl) ⟨1007279, by rfl⟩ : syracuseStep 1343039 = 2014559) B2014559
theorem B1343047 : Blo 1342990 1343047 := bstep (se 1 (by rfl) ⟨1007285, by rfl⟩ : syracuseStep 1343047 = 2014571) B2014571
theorem B3022523 : Blo 1342990 3022523 := bstep (se 1 (by rfl) ⟨2266892, by rfl⟩ : syracuseStep 3022523 = 4533785) B4533785
theorem B1343199 : Blo 1342990 1343199 := bstep (se 1 (by rfl) ⟨1007399, by rfl⟩ : syracuseStep 1343199 = 2014799) B2014799
theorem B2014955 : Blo 1342990 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B1343279 : Blo 1342990 1343279 := bstep (se 1 (by rfl) ⟨1007459, by rfl⟩ : syracuseStep 1343279 = 2014919) B2014919
theorem B4538159 : Blo 1342990 4538159 := bstep (se 1 (by rfl) ⟨3403619, by rfl⟩ : syracuseStep 4538159 = 6807239) B6807239
theorem B3399479 : Blo 1342990 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B3022649 : Blo 1342990 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B2268985 : Blo 1342990 2268985 := bstep (se 2 (by rfl) ⟨850869, by rfl⟩ : syracuseStep 2268985 = 1701739) B1701739
theorem B3399529 : Blo 1342990 3399529 := bstep (se 2 (by rfl) ⟨1274823, by rfl⟩ : syracuseStep 3399529 = 2549647) B2549647
theorem B1343387 : Blo 1342990 1343387 := bstep (se 1 (by rfl) ⟨1007540, by rfl⟩ : syracuseStep 1343387 = 2015081) B2015081
theorem B1343439 : Blo 1342990 1343439 := bstep (se 1 (by rfl) ⟨1007579, by rfl⟩ : syracuseStep 1343439 = 2015159) B2015159
theorem B2015183 : Blo 1342990 2015183 := bstep (se 1 (by rfl) ⟨1511387, by rfl⟩ : syracuseStep 2015183 = 3022775) B3022775
theorem B1343463 : Blo 1342990 1343463 := bstep (se 1 (by rfl) ⟨1007597, by rfl⟩ : syracuseStep 1343463 = 2015195) B2015195
theorem B3825883 : Blo 1342990 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B1343719 : Blo 1342990 1343719 := bstep (se 1 (by rfl) ⟨1007789, by rfl⟩ : syracuseStep 1343719 = 2015579) B2015579
theorem B3023135 : Blo 1342990 3023135 := bstep (se 1 (by rfl) ⟨2267351, by rfl⟩ : syracuseStep 3023135 = 4534703) B4534703
theorem B2015519 : Blo 1342990 2015519 := bstep (se 1 (by rfl) ⟨1511639, by rfl⟩ : syracuseStep 2015519 = 3023279) B3023279
theorem B2269471 : Blo 1342990 2269471 := bstep (se 1 (by rfl) ⟨1702103, by rfl⟩ : syracuseStep 2269471 = 3404207) B3404207
theorem B2015543 : Blo 1342990 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B2015615 : Blo 1342990 2015615 := bstep (se 1 (by rfl) ⟨1511711, by rfl⟩ : syracuseStep 2015615 = 3023423) B3023423
theorem B1343871 : Blo 1342990 1343871 := bstep (se 1 (by rfl) ⟨1007903, by rfl⟩ : syracuseStep 1343871 = 2015807) B2015807
theorem B4538807 : Blo 1342990 4538807 := bstep (se 1 (by rfl) ⟨3404105, by rfl⟩ : syracuseStep 4538807 = 6808211) B6808211
theorem B2015687 : Blo 1342990 2015687 := bstep (se 1 (by rfl) ⟨1511765, by rfl⟩ : syracuseStep 2015687 = 3023531) B3023531
theorem B1343951 : Blo 1342990 1343951 := bstep (se 1 (by rfl) ⟨1007963, by rfl⟩ : syracuseStep 1343951 = 2015927) B2015927
theorem B4424255 : Blo 1342990 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B1614439 : Blo 1342990 1614439 := bstep (se 1 (by rfl) ⟨1210829, by rfl⟩ : syracuseStep 1614439 = 2421659) B2421659
theorem B1344103 : Blo 1342990 1344103 := bstep (se 1 (by rfl) ⟨1008077, by rfl⟩ : syracuseStep 1344103 = 2016155) B2016155
theorem B14533283 : Blo 1342990 14533283 := bstep (se 1 (by rfl) ⟨10899962, by rfl⟩ : syracuseStep 14533283 = 21799925) B21799925
theorem B4842251 : Blo 1342990 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B2016041 : Blo 1342990 2016041 := bstep (se 2 (by rfl) ⟨756015, by rfl⟩ : syracuseStep 2016041 = 1512031) B1512031
theorem B2016047 : Blo 1342990 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B1344367 : Blo 1342990 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B4842395 : Blo 1342990 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B4539293 : Blo 1342990 4539293 := bstep (se 3 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 4539293 = 1702235) B1702235
theorem B3023783 : Blo 1342990 3023783 := bstep (se 1 (by rfl) ⟨2267837, by rfl⟩ : syracuseStep 3023783 = 4535675) B4535675
theorem B2016167 : Blo 1342990 2016167 := bstep (se 1 (by rfl) ⟨1512125, by rfl⟩ : syracuseStep 2016167 = 3024251) B3024251
theorem B1344423 : Blo 1342990 1344423 := bstep (se 1 (by rfl) ⟨1008317, by rfl⟩ : syracuseStep 1344423 = 2016635) B2016635
theorem B2016251 : Blo 1342990 2016251 := bstep (se 1 (by rfl) ⟨1512188, by rfl⟩ : syracuseStep 2016251 = 3024377) B3024377
theorem B1344507 : Blo 1342990 1344507 := bstep (se 1 (by rfl) ⟨1008380, by rfl⟩ : syracuseStep 1344507 = 2016761) B2016761
theorem B2016311 : Blo 1342990 2016311 := bstep (se 1 (by rfl) ⟨1512233, by rfl⟩ : syracuseStep 2016311 = 3024467) B3024467
theorem B1344575 : Blo 1342990 1344575 := bstep (se 1 (by rfl) ⟨1008431, by rfl⟩ : syracuseStep 1344575 = 2016863) B2016863
theorem B8176745 : Blo 1342990 8176745 := bstep (se 2 (by rfl) ⟨3066279, by rfl⟩ : syracuseStep 8176745 = 6132559) B6132559
theorem B2016431 : Blo 1342990 2016431 := bstep (se 1 (by rfl) ⟨1512323, by rfl⟩ : syracuseStep 2016431 = 3024647) B3024647
theorem B1344719 : Blo 1342990 1344719 := bstep (se 1 (by rfl) ⟨1008539, by rfl⟩ : syracuseStep 1344719 = 2017079) B2017079
theorem B1344923 : Blo 1342990 1344923 := bstep (se 1 (by rfl) ⟨1008692, by rfl⟩ : syracuseStep 1344923 = 2017385) B2017385
theorem B38725073 : Blo 1342990 38725073 := bstep (se 2 (by rfl) ⟨14521902, by rfl⟩ : syracuseStep 38725073 = 29043805) B29043805
theorem B3827159 : Blo 1342990 3827159 := bstep (se 1 (by rfl) ⟨2870369, by rfl⟩ : syracuseStep 3827159 = 5740739) B5740739
theorem B15508999 : Blo 1342990 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B24536591 : Blo 1342990 24536591 := bstep (se 1 (by rfl) ⟨18402443, by rfl⟩ : syracuseStep 24536591 = 36804887) B36804887
theorem B6800921 : Blo 1342990 6800921 := bstep (se 2 (by rfl) ⟨2550345, by rfl⟩ : syracuseStep 6800921 = 5100691) B5100691
theorem B2016839 : Blo 1342990 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B2016935 : Blo 1342990 2016935 := bstep (se 1 (by rfl) ⟨1512701, by rfl⟩ : syracuseStep 2016935 = 3025403) B3025403
theorem B17213147 : Blo 1342990 17213147 := bstep (se 1 (by rfl) ⟨12909860, by rfl⟩ : syracuseStep 17213147 = 25819721) B25819721
theorem B3630815 : Blo 1342990 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B2017019 : Blo 1342990 2017019 := bstep (se 1 (by rfl) ⟨1512764, by rfl⟩ : syracuseStep 2017019 = 3025529) B3025529
theorem B2017055 : Blo 1342990 2017055 := bstep (se 1 (by rfl) ⟨1512791, by rfl⟩ : syracuseStep 2017055 = 3025583) B3025583
theorem B3024719 : Blo 1342990 3024719 := bstep (se 1 (by rfl) ⟨2268539, by rfl⟩ : syracuseStep 3024719 = 4537079) B4537079
theorem B2017103 : Blo 1342990 2017103 := bstep (se 1 (by rfl) ⟨1512827, by rfl⟩ : syracuseStep 2017103 = 3025655) B3025655
theorem B3024737 : Blo 1342990 3024737 := bstep (se 2 (by rfl) ⟨1134276, by rfl⟩ : syracuseStep 3024737 = 2268553) B2268553
theorem B1435591 : Blo 1342990 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B2017223 : Blo 1342990 2017223 := bstep (se 1 (by rfl) ⟨1512917, by rfl⟩ : syracuseStep 2017223 = 3025835) B3025835
theorem B9693263 : Blo 1342990 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B2549951 : Blo 1342990 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B23267675 : Blo 1342990 23267675 := bstep (se 1 (by rfl) ⟨17450756, by rfl⟩ : syracuseStep 23267675 = 34901513) B34901513
theorem B294152593 : Blo 1342990 294152593 := bstep (se 2 (by rfl) ⟨110307222, by rfl⟩ : syracuseStep 294152593 = 220614445) B220614445
theorem B3025313 : Blo 1342990 3025313 := bstep (se 2 (by rfl) ⟨1134492, by rfl⟩ : syracuseStep 3025313 = 2268985) B2268985
theorem B4532705 : Blo 1342990 4532705 := bstep (se 2 (by rfl) ⟨1699764, by rfl⟩ : syracuseStep 4532705 = 3399529) B3399529
theorem B3025439 : Blo 1342990 3025439 := bstep (se 1 (by rfl) ⟨2269079, by rfl⟩ : syracuseStep 3025439 = 4538159) B4538159
theorem B36792949 : Blo 1342990 36792949 := bstep (se 5 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 36792949 = 3449339) B3449339
theorem B21793697 : Blo 1342990 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B8612801 : Blo 1342990 8612801 := bstep (se 2 (by rfl) ⟨3229800, by rfl⟩ : syracuseStep 8612801 = 6459601) B6459601
theorem B9694187 : Blo 1342990 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B1363015 : Blo 1342990 1363015 := bstep (se 1 (by rfl) ⟨1022261, by rfl⟩ : syracuseStep 1363015 = 2044523) B2044523
theorem B20966539 : Blo 1342990 20966539 := bstep (se 1 (by rfl) ⟨15724904, by rfl⟩ : syracuseStep 20966539 = 31449809) B31449809
theorem B2551007 : Blo 1342990 2551007 := bstep (se 1 (by rfl) ⟨1913255, by rfl⟩ : syracuseStep 2551007 = 3826511) B3826511
theorem B15953129 : Blo 1342990 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B4304171 : Blo 1342990 4304171 := bstep (se 1 (by rfl) ⟨3228128, by rfl⟩ : syracuseStep 4304171 = 6456257) B6456257
theorem B12922199 : Blo 1342990 12922199 := bstep (se 1 (by rfl) ⟨9691649, by rfl⟩ : syracuseStep 12922199 = 19383299) B19383299
theorem B17690021 : Blo 1342990 17690021 := bstep (se 4 (by rfl) ⟨1658439, by rfl⟩ : syracuseStep 17690021 = 3316879) B3316879
theorem B3403255 : Blo 1342990 3403255 := bstep (se 1 (by rfl) ⟨2552441, by rfl⟩ : syracuseStep 3403255 = 5104883) B5104883
theorem B8171081 : Blo 1342990 8171081 := bstep (se 2 (by rfl) ⟨3064155, by rfl⟩ : syracuseStep 8171081 = 6128311) B6128311
theorem B17034877 : Blo 1342990 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B5738141 : Blo 1342990 5738141 := bstep (se 3 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 5738141 = 2151803) B2151803
theorem B4534055 : Blo 1342990 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B2551591 : Blo 1342990 2551591 := bstep (se 1 (by rfl) ⟨1913693, by rfl⟩ : syracuseStep 2551591 = 3827387) B3827387
theorem B3403559 : Blo 1342990 3403559 := bstep (se 1 (by rfl) ⟨2552669, by rfl⟩ : syracuseStep 3403559 = 5105339) B5105339
theorem B1511239 : Blo 1342990 1511239 := bstep (se 1 (by rfl) ⟨1133429, by rfl⟩ : syracuseStep 1511239 = 2266859) B2266859
theorem B2183033 : Blo 1342990 2183033 := bstep (se 2 (by rfl) ⟨818637, by rfl⟩ : syracuseStep 2183033 = 1637275) B1637275
theorem B3829643 : Blo 1342990 3829643 := bstep (se 1 (by rfl) ⟨2872232, by rfl⟩ : syracuseStep 3829643 = 5744465) B5744465
theorem B20705267 : Blo 1342990 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B5099705 : Blo 1342990 5099705 := bstep (se 2 (by rfl) ⟨1912389, by rfl⟩ : syracuseStep 5099705 = 3824779) B3824779
theorem B1913215 : Blo 1342990 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B1511887 : Blo 1342990 1511887 := bstep (se 1 (by rfl) ⟨1133915, by rfl⟩ : syracuseStep 1511887 = 2267831) B2267831
theorem B4600435 : Blo 1342990 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B7656119 : Blo 1342990 7656119 := bstep (se 1 (by rfl) ⟨5742089, by rfl⟩ : syracuseStep 7656119 = 11484179) B11484179
theorem B2298631 : Blo 1342990 2298631 := bstep (se 1 (by rfl) ⟨1723973, by rfl⟩ : syracuseStep 2298631 = 3447947) B3447947
theorem B4535081 : Blo 1342990 4535081 := bstep (se 2 (by rfl) ⟨1700655, by rfl⟩ : syracuseStep 4535081 = 3401311) B3401311
theorem B4535351 : Blo 1342990 4535351 := bstep (se 1 (by rfl) ⟨3401513, by rfl⟩ : syracuseStep 4535351 = 6803027) B6803027
theorem B2266319 : Blo 1342990 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B1512859 : Blo 1342990 1512859 := bstep (se 1 (by rfl) ⟨1134644, by rfl⟩ : syracuseStep 1512859 = 2269289) B2269289
theorem B2422393 : Blo 1342990 2422393 := bstep (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) B1816795
theorem B2725769 : Blo 1342990 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B34445249 : Blo 1342990 34445249 := bstep (se 2 (by rfl) ⟨12916968, by rfl⟩ : syracuseStep 34445249 = 25833937) B25833937
theorem B7649261 : Blo 1342990 7649261 := bstep (se 3 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 7649261 = 2868473) B2868473
theorem B11483117 : Blo 1342990 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B2267129 : Blo 1342990 2267129 := bstep (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) B1700347
theorem B12916817 : Blo 1342990 12916817 := bstep (se 2 (by rfl) ⟨4843806, by rfl⟩ : syracuseStep 12916817 = 9687613) B9687613
theorem B5101663 : Blo 1342990 5101663 := bstep (se 1 (by rfl) ⟨3826247, by rfl⟩ : syracuseStep 5101663 = 7652495) B7652495
theorem B2267291 : Blo 1342990 2267291 := bstep (se 1 (by rfl) ⟨1700468, by rfl⟩ : syracuseStep 2267291 = 3400937) B3400937
theorem B2267399 : Blo 1342990 2267399 := bstep (se 1 (by rfl) ⟨1700549, by rfl⟩ : syracuseStep 2267399 = 3401099) B3401099
theorem B7649579 : Blo 1342990 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B10205513 : Blo 1342990 10205513 := bstep (se 2 (by rfl) ⟨3827067, by rfl⟩ : syracuseStep 10205513 = 7654135) B7654135
theorem B15735215 : Blo 1342990 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B6806105 : Blo 1342990 6806105 := bstep (se 2 (by rfl) ⟨2552289, by rfl⟩ : syracuseStep 6806105 = 5104579) B5104579
theorem B4307593 : Blo 1342990 4307593 := bstep (se 2 (by rfl) ⟨1615347, by rfl⟩ : syracuseStep 4307593 = 3230695) B3230695
theorem B2267959 : Blo 1342990 2267959 := bstep (se 1 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 2267959 = 3401939) B3401939
theorem B9681731 : Blo 1342990 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B4537295 : Blo 1342990 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B15506423 : Blo 1342990 15506423 := bstep (se 1 (by rfl) ⟨11629817, by rfl⟩ : syracuseStep 15506423 = 23259635) B23259635
theorem B13089863 : Blo 1342990 13089863 := bstep (se 1 (by rfl) ⟨9817397, by rfl⟩ : syracuseStep 13089863 = 19634795) B19634795
theorem B318569561 : Blo 1342990 318569561 := bstep (se 2 (by rfl) ⟨119463585, by rfl⟩ : syracuseStep 318569561 = 238927171) B238927171
theorem B2268425 : Blo 1342990 2268425 := bstep (se 2 (by rfl) ⟨850659, by rfl⟩ : syracuseStep 2268425 = 1701319) B1701319
theorem B11345285 : Blo 1342990 11345285 := bstep (se 4 (by rfl) ⟨1063620, by rfl⟩ : syracuseStep 11345285 = 2127241) B2127241
theorem B2014631 : Blo 1342990 2014631 := bstep (se 1 (by rfl) ⟨1510973, by rfl⟩ : syracuseStep 2014631 = 3021947) B3021947
theorem B2014715 : Blo 1342990 2014715 := bstep (se 1 (by rfl) ⟨1511036, by rfl⟩ : syracuseStep 2014715 = 3022073) B3022073
theorem B4841039 : Blo 1342990 4841039 := bstep (se 1 (by rfl) ⟨3630779, by rfl⟩ : syracuseStep 4841039 = 7261559) B7261559
theorem B3022415 : Blo 1342990 3022415 := bstep (se 1 (by rfl) ⟨2266811, by rfl⟩ : syracuseStep 3022415 = 4533623) B4533623
theorem B1343067 : Blo 1342990 1343067 := bstep (se 1 (by rfl) ⟨1007300, by rfl⟩ : syracuseStep 1343067 = 2014601) B2014601
theorem B2014811 : Blo 1342990 2014811 := bstep (se 1 (by rfl) ⟨1511108, by rfl⟩ : syracuseStep 2014811 = 3022217) B3022217
theorem B9322127 : Blo 1342990 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B2014895 : Blo 1342990 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B2015015 : Blo 1342990 2015015 := bstep (se 1 (by rfl) ⟨1511261, by rfl⟩ : syracuseStep 2015015 = 3022523) B3022523
theorem B1343303 : Blo 1342990 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B22110047 : Blo 1342990 22110047 := bstep (se 1 (by rfl) ⟨16582535, by rfl⟩ : syracuseStep 22110047 = 33165071) B33165071
theorem B2015099 : Blo 1342990 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B4087741 : Blo 1342990 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B1343455 : Blo 1342990 1343455 := bstep (se 1 (by rfl) ⟨1007591, by rfl⟩ : syracuseStep 1343455 = 2015183) B2015183
theorem B3399803 : Blo 1342990 3399803 := bstep (se 1 (by rfl) ⟨2549852, by rfl⟩ : syracuseStep 3399803 = 5099705) B5099705
theorem B2015423 : Blo 1342990 2015423 := bstep (se 1 (by rfl) ⟨1511567, by rfl⟩ : syracuseStep 2015423 = 3023135) B3023135
theorem B1343679 : Blo 1342990 1343679 := bstep (se 1 (by rfl) ⟨1007759, by rfl⟩ : syracuseStep 1343679 = 2015519) B2015519
theorem B1343695 : Blo 1342990 1343695 := bstep (se 1 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 1343695 = 2015543) B2015543
theorem B1343743 : Blo 1342990 1343743 := bstep (se 1 (by rfl) ⟨1007807, by rfl⟩ : syracuseStep 1343743 = 2015615) B2015615
theorem B1343791 : Blo 1342990 1343791 := bstep (se 1 (by rfl) ⟨1007843, by rfl⟩ : syracuseStep 1343791 = 2015687) B2015687
theorem B2949503 : Blo 1342990 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B5104079 : Blo 1342990 5104079 := bstep (se 1 (by rfl) ⟨3828059, by rfl⟩ : syracuseStep 5104079 = 7656119) B7656119
theorem B3228167 : Blo 1342990 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B3023387 : Blo 1342990 3023387 := bstep (se 1 (by rfl) ⟨2267540, by rfl⟩ : syracuseStep 3023387 = 4535081) B4535081
theorem B1344027 : Blo 1342990 1344027 := bstep (se 1 (by rfl) ⟨1008020, by rfl⟩ : syracuseStep 1344027 = 2016041) B2016041
theorem B1344031 : Blo 1342990 1344031 := bstep (se 1 (by rfl) ⟨1008023, by rfl⟩ : syracuseStep 1344031 = 2016047) B2016047
theorem B3228263 : Blo 1342990 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B2015849 : Blo 1342990 2015849 := bstep (se 2 (by rfl) ⟨755943, by rfl⟩ : syracuseStep 2015849 = 1511887) B1511887
theorem B2015855 : Blo 1342990 2015855 := bstep (se 1 (by rfl) ⟨1511891, by rfl⟩ : syracuseStep 2015855 = 3023783) B3023783
theorem B1344111 : Blo 1342990 1344111 := bstep (se 1 (by rfl) ⟨1008083, by rfl⟩ : syracuseStep 1344111 = 2016167) B2016167
theorem B12919429 : Blo 1342990 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B1344167 : Blo 1342990 1344167 := bstep (se 1 (by rfl) ⟨1008125, by rfl⟩ : syracuseStep 1344167 = 2016251) B2016251
theorem B3023567 : Blo 1342990 3023567 := bstep (se 1 (by rfl) ⟨2267675, by rfl⟩ : syracuseStep 3023567 = 4535351) B4535351
theorem B1344207 : Blo 1342990 1344207 := bstep (se 1 (by rfl) ⟨1008155, by rfl⟩ : syracuseStep 1344207 = 2016311) B2016311
theorem B1344287 : Blo 1342990 1344287 := bstep (se 1 (by rfl) ⟨1008215, by rfl⟩ : syracuseStep 1344287 = 2016431) B2016431
theorem B5743457 : Blo 1342990 5743457 := bstep (se 2 (by rfl) ⟨2153796, by rfl⟩ : syracuseStep 5743457 = 4307593) B4307593
theorem B3064841 : Blo 1342990 3064841 := bstep (se 2 (by rfl) ⟨1149315, by rfl⟩ : syracuseStep 3064841 = 2298631) B2298631
theorem B1344559 : Blo 1342990 1344559 := bstep (se 1 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 1344559 = 2016839) B2016839
theorem B3023945 : Blo 1342990 3023945 := bstep (se 2 (by rfl) ⟨1133979, by rfl⟩ : syracuseStep 3023945 = 2267959) B2267959
theorem B1344623 : Blo 1342990 1344623 := bstep (se 1 (by rfl) ⟨1008467, by rfl⟩ : syracuseStep 1344623 = 2016935) B2016935
theorem B1344679 : Blo 1342990 1344679 := bstep (se 1 (by rfl) ⟨1008509, by rfl⟩ : syracuseStep 1344679 = 2017019) B2017019
theorem B1344703 : Blo 1342990 1344703 := bstep (se 1 (by rfl) ⟨1008527, by rfl⟩ : syracuseStep 1344703 = 2017055) B2017055
theorem B2016479 : Blo 1342990 2016479 := bstep (se 1 (by rfl) ⟨1512359, by rfl⟩ : syracuseStep 2016479 = 3024719) B3024719
theorem B1344735 : Blo 1342990 1344735 := bstep (se 1 (by rfl) ⟨1008551, by rfl⟩ : syracuseStep 1344735 = 2017103) B2017103
theorem B2016491 : Blo 1342990 2016491 := bstep (se 1 (by rfl) ⟨1512368, by rfl⟩ : syracuseStep 2016491 = 3024737) B3024737
theorem B22963499 : Blo 1342990 22963499 := bstep (se 1 (by rfl) ⟨17222624, by rfl⟩ : syracuseStep 22963499 = 34445249) B34445249
theorem B1344815 : Blo 1342990 1344815 := bstep (se 1 (by rfl) ⟨1008611, by rfl⟩ : syracuseStep 1344815 = 2017223) B2017223
theorem B8611211 : Blo 1342990 8611211 := bstep (se 1 (by rfl) ⟨6458408, by rfl⟩ : syracuseStep 8611211 = 12916817) B12916817
theorem B2016875 : Blo 1342990 2016875 := bstep (se 1 (by rfl) ⟨1512656, by rfl⟩ : syracuseStep 2016875 = 3025313) B3025313
theorem B2016959 : Blo 1342990 2016959 := bstep (se 1 (by rfl) ⟨1512719, by rfl⟩ : syracuseStep 2016959 = 3025439) B3025439
theorem B2017145 : Blo 1342990 2017145 := bstep (se 2 (by rfl) ⟨756429, by rfl⟩ : syracuseStep 2017145 = 1512859) B1512859
theorem B3024863 : Blo 1342990 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B20678665 : Blo 1342990 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B8726575 : Blo 1342990 8726575 := bstep (se 1 (by rfl) ⟨6544931, by rfl⟩ : syracuseStep 8726575 = 13089863) B13089863
theorem B212379707 : Blo 1342990 212379707 := bstep (se 1 (by rfl) ⟨159284780, by rfl⟩ : syracuseStep 212379707 = 318569561) B318569561
theorem B10635419 : Blo 1342990 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B2869447 : Blo 1342990 2869447 := bstep (se 1 (by rfl) ⟨2152085, by rfl⟩ : syracuseStep 2869447 = 4304171) B4304171
theorem B7563523 : Blo 1342990 7563523 := bstep (se 1 (by rfl) ⟨5672642, by rfl⟩ : syracuseStep 7563523 = 11345285) B11345285
theorem B7268717 : Blo 1342990 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B3402121 : Blo 1342990 3402121 := bstep (se 2 (by rfl) ⟨1275795, by rfl⟩ : syracuseStep 3402121 = 2551591) B2551591
theorem B14740031 : Blo 1342990 14740031 := bstep (se 1 (by rfl) ⟨11055023, by rfl⟩ : syracuseStep 14740031 = 22110047) B22110047
theorem B5450321 : Blo 1342990 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B6802217 : Blo 1342990 6802217 := bstep (se 2 (by rfl) ⟨2550831, by rfl⟩ : syracuseStep 6802217 = 5101663) B5101663
theorem B3025871 : Blo 1342990 3025871 := bstep (se 1 (by rfl) ⟨2269403, by rfl⟩ : syracuseStep 3025871 = 4538807) B4538807
theorem B3025961 : Blo 1342990 3025961 := bstep (se 2 (by rfl) ⟨1134735, by rfl⟩ : syracuseStep 3025961 = 2269471) B2269471
theorem B2550953 : Blo 1342990 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B392203457 : Blo 1342990 392203457 := bstep (se 2 (by rfl) ⟨147076296, by rfl⟩ : syracuseStep 392203457 = 294152593) B294152593
theorem B3026195 : Blo 1342990 3026195 := bstep (se 1 (by rfl) ⟨2269646, by rfl⟩ : syracuseStep 3026195 = 4539293) B4539293
theorem B1510879 : Blo 1342990 1510879 := bstep (se 1 (by rfl) ⟨1133159, by rfl⟩ : syracuseStep 1510879 = 2266319) B2266319
theorem B49057265 : Blo 1342990 49057265 := bstep (se 2 (by rfl) ⟨18396474, by rfl⟩ : syracuseStep 49057265 = 36792949) B36792949
theorem B25816715 : Blo 1342990 25816715 := bstep (se 1 (by rfl) ⟨19362536, by rfl⟩ : syracuseStep 25816715 = 38725073) B38725073
theorem B2551439 : Blo 1342990 2551439 := bstep (se 1 (by rfl) ⟨1913579, by rfl⟩ : syracuseStep 2551439 = 3827159) B3827159
theorem B4533947 : Blo 1342990 4533947 := bstep (se 1 (by rfl) ⟨3400460, by rfl⟩ : syracuseStep 4533947 = 6800921) B6800921
theorem B2420543 : Blo 1342990 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B5099507 : Blo 1342990 5099507 := bstep (se 1 (by rfl) ⟨3824630, by rfl⟩ : syracuseStep 5099507 = 7649261) B7649261
theorem B7655411 : Blo 1342990 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B1511419 : Blo 1342990 1511419 := bstep (se 1 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 1511419 = 2267129) B2267129
theorem B1511527 : Blo 1342990 1511527 := bstep (se 1 (by rfl) ⟨1133645, by rfl⟩ : syracuseStep 1511527 = 2267291) B2267291
theorem B1699967 : Blo 1342990 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1511599 : Blo 1342990 1511599 := bstep (se 1 (by rfl) ⟨1133699, by rfl⟩ : syracuseStep 1511599 = 2267399) B2267399
theorem B27955385 : Blo 1342990 27955385 := bstep (se 2 (by rfl) ⟨10483269, by rfl⟩ : syracuseStep 27955385 = 20966539) B20966539
theorem B5099719 : Blo 1342990 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B6803675 : Blo 1342990 6803675 := bstep (se 1 (by rfl) ⟨5102756, by rfl⟩ : syracuseStep 6803675 = 10205513) B10205513
theorem B15511783 : Blo 1342990 15511783 := bstep (se 1 (by rfl) ⟨11633837, by rfl⟩ : syracuseStep 15511783 = 23267675) B23267675
theorem B10490143 : Blo 1342990 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B14529131 : Blo 1342990 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B1700671 : Blo 1342990 1700671 := bstep (se 1 (by rfl) ⟨1275503, by rfl⟩ : syracuseStep 1700671 = 2551007) B2551007
theorem B22713169 : Blo 1342990 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B1512283 : Blo 1342990 1512283 := bstep (se 1 (by rfl) ⟨1134212, by rfl⟩ : syracuseStep 1512283 = 2268425) B2268425
theorem B8614799 : Blo 1342990 8614799 := bstep (se 1 (by rfl) ⟨6461099, by rfl⟩ : syracuseStep 8614799 = 12922199) B12922199
theorem B11793347 : Blo 1342990 11793347 := bstep (se 1 (by rfl) ⟨8845010, by rfl⟩ : syracuseStep 11793347 = 17690021) B17690021
theorem B6214751 : Blo 1342990 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B1455355 : Blo 1342990 1455355 := bstep (se 1 (by rfl) ⟨1091516, by rfl⟩ : syracuseStep 1455355 = 2183033) B2183033
theorem B2553095 : Blo 1342990 2553095 := bstep (se 1 (by rfl) ⟨1914821, by rfl⟩ : syracuseStep 2553095 = 3829643) B3829643
theorem B1914121 : Blo 1342990 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B21804653 : Blo 1342990 21804653 := bstep (se 3 (by rfl) ⟨4088372, by rfl⟩ : syracuseStep 21804653 = 8176745) B8176745
theorem B5101177 : Blo 1342990 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B9688855 : Blo 1342990 9688855 := bstep (se 1 (by rfl) ⟨7266641, by rfl⟩ : syracuseStep 9688855 = 14533283) B14533283
theorem B2152585 : Blo 1342990 2152585 := bstep (se 2 (by rfl) ⟨807219, by rfl⟩ : syracuseStep 2152585 = 1614439) B1614439
theorem B6133913 : Blo 1342990 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B16357727 : Blo 1342990 16357727 := bstep (se 1 (by rfl) ⟨12268295, by rfl⟩ : syracuseStep 16357727 = 24536591) B24536591
theorem B11475431 : Blo 1342990 11475431 := bstep (se 1 (by rfl) ⟨8606573, by rfl⟩ : syracuseStep 11475431 = 17213147) B17213147
theorem B6462175 : Blo 1342990 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B1817353 : Blo 1342990 1817353 := bstep (se 2 (by rfl) ⟨681507, by rfl⟩ : syracuseStep 1817353 = 1363015) B1363015
theorem B3021803 : Blo 1342990 3021803 := bstep (se 1 (by rfl) ⟨2266352, by rfl⟩ : syracuseStep 3021803 = 4532705) B4532705
theorem B4537403 : Blo 1342990 4537403 := bstep (se 1 (by rfl) ⟨3403052, by rfl⟩ : syracuseStep 4537403 = 6806105) B6806105
theorem B15301709 : Blo 1342990 15301709 := bstep (se 3 (by rfl) ⟨2869070, by rfl⟩ : syracuseStep 15301709 = 5738141) B5738141
theorem B6454487 : Blo 1342990 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B5741867 : Blo 1342990 5741867 := bstep (se 1 (by rfl) ⟨4306400, by rfl⟩ : syracuseStep 5741867 = 8612801) B8612801
theorem B4537673 : Blo 1342990 4537673 := bstep (se 2 (by rfl) ⟨1701627, by rfl⟩ : syracuseStep 4537673 = 3403255) B3403255
theorem B6462791 : Blo 1342990 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B10337615 : Blo 1342990 10337615 := bstep (se 1 (by rfl) ⟨7753211, by rfl⟩ : syracuseStep 10337615 = 15506423) B15506423
theorem B1343087 : Blo 1342990 1343087 := bstep (se 1 (by rfl) ⟨1007315, by rfl⟩ : syracuseStep 1343087 = 2014631) B2014631
theorem B1343143 : Blo 1342990 1343143 := bstep (se 1 (by rfl) ⟨1007357, by rfl⟩ : syracuseStep 1343143 = 2014715) B2014715
theorem B5447387 : Blo 1342990 5447387 := bstep (se 1 (by rfl) ⟨4085540, by rfl⟩ : syracuseStep 5447387 = 8171081) B8171081
theorem B3227359 : Blo 1342990 3227359 := bstep (se 1 (by rfl) ⟨2420519, by rfl⟩ : syracuseStep 3227359 = 4841039) B4841039
theorem B2014943 : Blo 1342990 2014943 := bstep (se 1 (by rfl) ⟨1511207, by rfl⟩ : syracuseStep 2014943 = 3022415) B3022415
theorem B1343207 : Blo 1342990 1343207 := bstep (se 1 (by rfl) ⟨1007405, by rfl⟩ : syracuseStep 1343207 = 2014811) B2014811
theorem B2014985 : Blo 1342990 2014985 := bstep (se 2 (by rfl) ⟨755619, by rfl⟩ : syracuseStep 2014985 = 1511239) B1511239
theorem B1343263 : Blo 1342990 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B1343343 : Blo 1342990 1343343 := bstep (se 1 (by rfl) ⟨1007507, by rfl⟩ : syracuseStep 1343343 = 2015015) B2015015
theorem B3022703 : Blo 1342990 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B2269039 : Blo 1342990 2269039 := bstep (se 1 (by rfl) ⟨1701779, by rfl⟩ : syracuseStep 2269039 = 3403559) B3403559
theorem B1343399 : Blo 1342990 1343399 := bstep (se 1 (by rfl) ⟨1007549, by rfl⟩ : syracuseStep 1343399 = 2015099) B2015099
theorem B55214045 : Blo 1342990 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B18636923 : Blo 1342990 18636923 := bstep (se 1 (by rfl) ⟨13977692, by rfl⟩ : syracuseStep 18636923 = 27955385) B27955385
theorem B1343615 : Blo 1342990 1343615 := bstep (se 1 (by rfl) ⟨1007711, by rfl⟩ : syracuseStep 1343615 = 2015423) B2015423
theorem B2015369 : Blo 1342990 2015369 := bstep (se 2 (by rfl) ⟨755763, by rfl⟩ : syracuseStep 2015369 = 1511527) B1511527
theorem B2015465 : Blo 1342990 2015465 := bstep (se 2 (by rfl) ⟨755799, by rfl⟩ : syracuseStep 2015465 = 1511599) B1511599
theorem B6799625 : Blo 1342990 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B3825929 : Blo 1342990 3825929 := bstep (se 2 (by rfl) ⟨1434723, by rfl⟩ : syracuseStep 3825929 = 2869447) B2869447
theorem B10084697 : Blo 1342990 10084697 := bstep (se 2 (by rfl) ⟨3781761, by rfl⟩ : syracuseStep 10084697 = 7563523) B7563523
theorem B2015591 : Blo 1342990 2015591 := bstep (se 1 (by rfl) ⟨1511693, by rfl⟩ : syracuseStep 2015591 = 3023387) B3023387
theorem B1343899 : Blo 1342990 1343899 := bstep (se 1 (by rfl) ⟨1007924, by rfl⟩ : syracuseStep 1343899 = 2015849) B2015849
theorem B1343903 : Blo 1342990 1343903 := bstep (se 1 (by rfl) ⟨1007927, by rfl⟩ : syracuseStep 1343903 = 2015855) B2015855
theorem B28361117 : Blo 1342990 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B2015711 : Blo 1342990 2015711 := bstep (se 1 (by rfl) ⟨1511783, by rfl⟩ : syracuseStep 2015711 = 3023567) B3023567
theorem B5743199 : Blo 1342990 5743199 := bstep (se 1 (by rfl) ⟨4307399, by rfl⟩ : syracuseStep 5743199 = 8614799) B8614799
theorem B2015963 : Blo 1342990 2015963 := bstep (se 1 (by rfl) ⟨1511972, by rfl⟩ : syracuseStep 2015963 = 3023945) B3023945
theorem B1344319 : Blo 1342990 1344319 := bstep (se 1 (by rfl) ⟨1008239, by rfl⟩ : syracuseStep 1344319 = 2016479) B2016479
theorem B1344327 : Blo 1342990 1344327 := bstep (se 1 (by rfl) ⟨1008245, by rfl⟩ : syracuseStep 1344327 = 2016491) B2016491
theorem B19383245 : Blo 1342990 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B1344583 : Blo 1342990 1344583 := bstep (se 1 (by rfl) ⟨1008437, by rfl⟩ : syracuseStep 1344583 = 2016875) B2016875
theorem B2016377 : Blo 1342990 2016377 := bstep (se 2 (by rfl) ⟨756141, by rfl⟩ : syracuseStep 2016377 = 1512283) B1512283
theorem B1344639 : Blo 1342990 1344639 := bstep (se 1 (by rfl) ⟨1008479, by rfl⟩ : syracuseStep 1344639 = 2016959) B2016959
theorem B1344763 : Blo 1342990 1344763 := bstep (se 1 (by rfl) ⟨1008572, by rfl⟩ : syracuseStep 1344763 = 2017145) B2017145
theorem B2016575 : Blo 1342990 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B4089275 : Blo 1342990 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B2017247 : Blo 1342990 2017247 := bstep (se 1 (by rfl) ⟨1512935, by rfl⟩ : syracuseStep 2017247 = 3025871) B3025871
theorem B2017307 : Blo 1342990 2017307 := bstep (se 1 (by rfl) ⟨1512980, by rfl⟩ : syracuseStep 2017307 = 3025961) B3025961
theorem B3024935 : Blo 1342990 3024935 := bstep (se 1 (by rfl) ⟨2268701, by rfl⟩ : syracuseStep 3024935 = 4537403) B4537403
theorem B10201139 : Blo 1342990 10201139 := bstep (se 1 (by rfl) ⟨7650854, by rfl⟩ : syracuseStep 10201139 = 15301709) B15301709
theorem B4302991 : Blo 1342990 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B6801569 : Blo 1342990 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B2017463 : Blo 1342990 2017463 := bstep (se 1 (by rfl) ⟨1513097, by rfl⟩ : syracuseStep 2017463 = 3026195) B3026195
theorem B3827911 : Blo 1342990 3827911 := bstep (se 1 (by rfl) ⟨2870933, by rfl⟩ : syracuseStep 3827911 = 5741867) B5741867
theorem B3025115 : Blo 1342990 3025115 := bstep (se 1 (by rfl) ⟨2268836, by rfl⟩ : syracuseStep 3025115 = 4537673) B4537673
theorem B6891743 : Blo 1342990 6891743 := bstep (se 1 (by rfl) ⟨5168807, by rfl⟩ : syracuseStep 6891743 = 10337615) B10337615
theorem B4303145 : Blo 1342990 4303145 := bstep (se 2 (by rfl) ⟨1613679, by rfl⟩ : syracuseStep 4303145 = 3227359) B3227359
theorem B32704843 : Blo 1342990 32704843 := bstep (se 1 (by rfl) ⟨24528632, by rfl⟩ : syracuseStep 32704843 = 49057265) B49057265
theorem B3631591 : Blo 1342990 3631591 := bstep (se 1 (by rfl) ⟨2723693, by rfl⟩ : syracuseStep 3631591 = 5447387) B5447387
theorem B3025385 : Blo 1342990 3025385 := bstep (se 2 (by rfl) ⟨1134519, by rfl⟩ : syracuseStep 3025385 = 2269039) B2269039
theorem B36809363 : Blo 1342990 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B11635433 : Blo 1342990 11635433 := bstep (se 2 (by rfl) ⟨4363287, by rfl⟩ : syracuseStep 11635433 = 8726575) B8726575
theorem B3402719 : Blo 1342990 3402719 := bstep (se 1 (by rfl) ⟨2552039, by rfl⟩ : syracuseStep 3402719 = 5104079) B5104079
theorem B4533245 : Blo 1342990 4533245 := bstep (se 3 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 4533245 = 1699967) B1699967
theorem B13986857 : Blo 1342990 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B9686087 : Blo 1342990 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B6802541 : Blo 1342990 6802541 := bstep (se 3 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 6802541 = 2550953) B2550953
theorem B3828971 : Blo 1342990 3828971 := bstep (se 1 (by rfl) ⟨2871728, by rfl⟩ : syracuseStep 3828971 = 5743457) B5743457
theorem B2043227 : Blo 1342990 2043227 := bstep (se 1 (by rfl) ⟨1532420, by rfl⟩ : syracuseStep 2043227 = 3064841) B3064841
theorem B11480453 : Blo 1342990 11480453 := bstep (se 4 (by rfl) ⟨1076292, by rfl⟩ : syracuseStep 11480453 = 2152585) B2152585
theorem B5103607 : Blo 1342990 5103607 := bstep (se 1 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 5103607 = 7655411) B7655411
theorem B14536435 : Blo 1342990 14536435 := bstep (se 1 (by rfl) ⟨10902326, by rfl⟩ : syracuseStep 14536435 = 21804653) B21804653
theorem B31461365 : Blo 1342990 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B141586471 : Blo 1342990 141586471 := bstep (se 1 (by rfl) ⟨106189853, by rfl⟩ : syracuseStep 141586471 = 212379707) B212379707
theorem B2552161 : Blo 1342990 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B6803837 : Blo 1342990 6803837 := bstep (se 3 (by rfl) ⟨1275719, by rfl⟩ : syracuseStep 6803837 = 2551439) B2551439
theorem B9826687 : Blo 1342990 9826687 := bstep (se 1 (by rfl) ⟨7370015, by rfl⟩ : syracuseStep 9826687 = 14740031) B14740031
theorem B3633547 : Blo 1342990 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B4534811 : Blo 1342990 4534811 := bstep (se 1 (by rfl) ⟨3401108, by rfl⟩ : syracuseStep 4534811 = 6802217) B6802217
theorem B261468971 : Blo 1342990 261468971 := bstep (se 1 (by rfl) ⟨196101728, by rfl⟩ : syracuseStep 261468971 = 392203457) B392203457
theorem B27571553 : Blo 1342990 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B2266535 : Blo 1342990 2266535 := bstep (se 1 (by rfl) ⟨1699901, by rfl⟩ : syracuseStep 2266535 = 3399803) B3399803
theorem B4535783 : Blo 1342990 4535783 := bstep (se 1 (by rfl) ⟨3401837, by rfl⟩ : syracuseStep 4535783 = 6803675) B6803675
theorem B20682377 : Blo 1342990 20682377 := bstep (se 2 (by rfl) ⟨7755891, by rfl⟩ : syracuseStep 20682377 = 15511783) B15511783
theorem B2152111 : Blo 1342990 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B2152175 : Blo 1342990 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B4536161 : Blo 1342990 4536161 := bstep (se 2 (by rfl) ⟨1701060, by rfl⟩ : syracuseStep 4536161 = 3402121) B3402121
theorem B7862231 : Blo 1342990 7862231 := bstep (se 1 (by rfl) ⟨5896673, by rfl⟩ : syracuseStep 7862231 = 11793347) B11793347
theorem B4143167 : Blo 1342990 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B1702063 : Blo 1342990 1702063 := bstep (se 1 (by rfl) ⟨1276547, by rfl⟩ : syracuseStep 1702063 = 2553095) B2553095
theorem B17225905 : Blo 1342990 17225905 := bstep (se 2 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 17225905 = 12919429) B12919429
theorem B15308999 : Blo 1342990 15308999 := bstep (se 1 (by rfl) ⟨11481749, by rfl⟩ : syracuseStep 15308999 = 22963499) B22963499
theorem B43620605 : Blo 1342990 43620605 := bstep (se 3 (by rfl) ⟨8178863, by rfl⟩ : syracuseStep 43620605 = 16357727) B16357727
theorem B5740807 : Blo 1342990 5740807 := bstep (se 1 (by rfl) ⟨4305605, by rfl⟩ : syracuseStep 5740807 = 8611211) B8611211
theorem B8616233 : Blo 1342990 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B2423137 : Blo 1342990 2423137 := bstep (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) B1817353
theorem B2267561 : Blo 1342990 2267561 := bstep (se 2 (by rfl) ⟨850335, by rfl⟩ : syracuseStep 2267561 = 1700671) B1700671
theorem B30284225 : Blo 1342990 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B7650287 : Blo 1342990 7650287 := bstep (se 1 (by rfl) ⟨5737715, by rfl⟩ : syracuseStep 7650287 = 11475431) B11475431
theorem B1940473 : Blo 1342990 1940473 := bstep (se 2 (by rfl) ⟨727677, by rfl⟩ : syracuseStep 1940473 = 1455355) B1455355
theorem B2014505 : Blo 1342990 2014505 := bstep (se 2 (by rfl) ⟨755439, by rfl⟩ : syracuseStep 2014505 = 1510879) B1510879
theorem B2014535 : Blo 1342990 2014535 := bstep (se 1 (by rfl) ⟨1510901, by rfl⟩ : syracuseStep 2014535 = 3021803) B3021803
theorem B4308527 : Blo 1342990 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B12918473 : Blo 1342990 12918473 := bstep (se 2 (by rfl) ⟨4844427, by rfl⟩ : syracuseStep 12918473 = 9688855) B9688855
theorem B3399671 : Blo 1342990 3399671 := bstep (se 1 (by rfl) ⟨2549753, by rfl⟩ : syracuseStep 3399671 = 5099507) B5099507
theorem B17211143 : Blo 1342990 17211143 := bstep (se 1 (by rfl) ⟨12908357, by rfl⟩ : syracuseStep 17211143 = 25816715) B25816715
theorem B3022631 : Blo 1342990 3022631 := bstep (se 1 (by rfl) ⟨2266973, by rfl⟩ : syracuseStep 3022631 = 4533947) B4533947
theorem B1343295 : Blo 1342990 1343295 := bstep (se 1 (by rfl) ⟨1007471, by rfl⟩ : syracuseStep 1343295 = 2014943) B2014943
theorem B1343323 : Blo 1342990 1343323 := bstep (se 1 (by rfl) ⟨1007492, by rfl⟩ : syracuseStep 1343323 = 2014985) B2014985
theorem B1613695 : Blo 1342990 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B2015135 : Blo 1342990 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B2015225 : Blo 1342990 2015225 := bstep (se 2 (by rfl) ⟨755709, by rfl⟩ : syracuseStep 2015225 = 1511419) B1511419
theorem B1343579 : Blo 1342990 1343579 := bstep (se 1 (by rfl) ⟨1007684, by rfl⟩ : syracuseStep 1343579 = 2015369) B2015369
theorem B1343643 : Blo 1342990 1343643 := bstep (se 1 (by rfl) ⟨1007732, by rfl⟩ : syracuseStep 1343643 = 2015465) B2015465
theorem B2269417 : Blo 1342990 2269417 := bstep (se 2 (by rfl) ⟨851031, by rfl⟩ : syracuseStep 2269417 = 1702063) B1702063
theorem B1343727 : Blo 1342990 1343727 := bstep (se 1 (by rfl) ⟨1007795, by rfl⟩ : syracuseStep 1343727 = 2015591) B2015591
theorem B5103881 : Blo 1342990 5103881 := bstep (se 2 (by rfl) ⟨1913955, by rfl⟩ : syracuseStep 5103881 = 3827911) B3827911
theorem B18907411 : Blo 1342990 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B1343807 : Blo 1342990 1343807 := bstep (se 1 (by rfl) ⟨1007855, by rfl⟩ : syracuseStep 1343807 = 2015711) B2015711
theorem B3023207 : Blo 1342990 3023207 := bstep (se 1 (by rfl) ⟨2267405, by rfl⟩ : syracuseStep 3023207 = 4534811) B4534811
theorem B43606457 : Blo 1342990 43606457 := bstep (se 2 (by rfl) ⟨16352421, by rfl⟩ : syracuseStep 43606457 = 32704843) B32704843
theorem B1343975 : Blo 1342990 1343975 := bstep (se 1 (by rfl) ⟨1007981, by rfl⟩ : syracuseStep 1343975 = 2015963) B2015963
theorem B4842121 : Blo 1342990 4842121 := bstep (se 2 (by rfl) ⟨1815795, by rfl⟩ : syracuseStep 4842121 = 3631591) B3631591
theorem B1344251 : Blo 1342990 1344251 := bstep (se 1 (by rfl) ⟨1008188, by rfl⟩ : syracuseStep 1344251 = 2016377) B2016377
theorem B1344383 : Blo 1342990 1344383 := bstep (se 1 (by rfl) ⟨1008287, by rfl⟩ : syracuseStep 1344383 = 2016575) B2016575
theorem B1343483 : Blo 1342990 1343483 := bstep (se 1 (by rfl) ⟨1007612, by rfl⟩ : syracuseStep 1343483 = 2015225) B2015225
theorem B3023855 : Blo 1342990 3023855 := bstep (se 1 (by rfl) ⟨2267891, by rfl⟩ : syracuseStep 3023855 = 4535783) B4535783
theorem B13788251 : Blo 1342990 13788251 := bstep (se 1 (by rfl) ⟨10341188, by rfl⟩ : syracuseStep 13788251 = 20682377) B20682377
theorem B3024107 : Blo 1342990 3024107 := bstep (se 1 (by rfl) ⟨2268080, by rfl⟩ : syracuseStep 3024107 = 4536161) B4536161
theorem B1344831 : Blo 1342990 1344831 := bstep (se 1 (by rfl) ⟨1008623, by rfl⟩ : syracuseStep 1344831 = 2017247) B2017247
theorem B1344871 : Blo 1342990 1344871 := bstep (se 1 (by rfl) ⟨1008653, by rfl⟩ : syracuseStep 1344871 = 2017307) B2017307
theorem B2016623 : Blo 1342990 2016623 := bstep (se 1 (by rfl) ⟨1512467, by rfl⟩ : syracuseStep 2016623 = 3024935) B3024935
theorem B6800759 : Blo 1342990 6800759 := bstep (se 1 (by rfl) ⟨5100569, by rfl⟩ : syracuseStep 6800759 = 10201139) B10201139
theorem B2762111 : Blo 1342990 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B1344975 : Blo 1342990 1344975 := bstep (se 1 (by rfl) ⟨1008731, by rfl⟩ : syracuseStep 1344975 = 2017463) B2017463
theorem B2016743 : Blo 1342990 2016743 := bstep (se 1 (by rfl) ⟨1512557, by rfl⟩ : syracuseStep 2016743 = 3025115) B3025115
theorem B2016923 : Blo 1342990 2016923 := bstep (se 1 (by rfl) ⟨1512692, by rfl⟩ : syracuseStep 2016923 = 3025385) B3025385
theorem B98158301 : Blo 1342990 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B9324571 : Blo 1342990 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B6457391 : Blo 1342990 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B1362151 : Blo 1342990 1362151 := bstep (se 1 (by rfl) ⟨1021613, by rfl⟩ : syracuseStep 1362151 = 2043227) B2043227
theorem B2869481 : Blo 1342990 2869481 := bstep (se 2 (by rfl) ⟨1076055, by rfl⟩ : syracuseStep 2869481 = 2152111) B2152111
theorem B7653635 : Blo 1342990 7653635 := bstep (se 1 (by rfl) ⟨5740226, by rfl⟩ : syracuseStep 7653635 = 11480453) B11480453
theorem B8612315 : Blo 1342990 8612315 := bstep (se 1 (by rfl) ⟨6459236, by rfl⟩ : syracuseStep 8612315 = 12918473) B12918473
theorem B20965949 : Blo 1342990 20965949 := bstep (se 3 (by rfl) ⟨3931115, by rfl⟩ : syracuseStep 20965949 = 7862231) B7862231
theorem B20974243 : Blo 1342990 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B4533083 : Blo 1342990 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B2550619 : Blo 1342990 2550619 := bstep (se 1 (by rfl) ⟨1912964, by rfl⟩ : syracuseStep 2550619 = 3825929) B3825929
theorem B5737321 : Blo 1342990 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B7654409 : Blo 1342990 7654409 := bstep (se 2 (by rfl) ⟨2870403, by rfl⟩ : syracuseStep 7654409 = 5740807) B5740807
theorem B3828799 : Blo 1342990 3828799 := bstep (se 1 (by rfl) ⟨2871599, by rfl⟩ : syracuseStep 3828799 = 5743199) B5743199
theorem B3402881 : Blo 1342990 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B3230849 : Blo 1342990 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B13102249 : Blo 1342990 13102249 := bstep (se 2 (by rfl) ⟨4913343, by rfl⟩ : syracuseStep 13102249 = 9826687) B9826687
theorem B4844729 : Blo 1342990 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B174312647 : Blo 1342990 174312647 := bstep (se 1 (by rfl) ⟨130734485, by rfl⟩ : syracuseStep 174312647 = 261468971) B261468971
theorem B12922163 : Blo 1342990 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B1511023 : Blo 1342990 1511023 := bstep (se 1 (by rfl) ⟨1133267, by rfl⟩ : syracuseStep 1511023 = 2266535) B2266535
theorem B4534379 : Blo 1342990 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B1511707 : Blo 1342990 1511707 := bstep (se 1 (by rfl) ⟨1133780, by rfl⟩ : syracuseStep 1511707 = 2267561) B2267561
theorem B20189483 : Blo 1342990 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B5739133 : Blo 1342990 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B5100191 : Blo 1342990 5100191 := bstep (se 1 (by rfl) ⟨3825143, by rfl⟩ : syracuseStep 5100191 = 7650287) B7650287
theorem B4535027 : Blo 1342990 4535027 := bstep (se 1 (by rfl) ⟨3401270, by rfl⟩ : syracuseStep 4535027 = 6802541) B6802541
theorem B2552647 : Blo 1342990 2552647 := bstep (se 1 (by rfl) ⟨1914485, by rfl⟩ : syracuseStep 2552647 = 3828971) B3828971
theorem B2872351 : Blo 1342990 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B2151593 : Blo 1342990 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B11474095 : Blo 1342990 11474095 := bstep (se 1 (by rfl) ⟨8605571, by rfl⟩ : syracuseStep 11474095 = 17211143) B17211143
theorem B6804809 : Blo 1342990 6804809 := bstep (se 2 (by rfl) ⟨2551803, by rfl⟩ : syracuseStep 6804809 = 5103607) B5103607
theorem B2266447 : Blo 1342990 2266447 := bstep (se 1 (by rfl) ⟨1699835, by rfl⟩ : syracuseStep 2266447 = 3399671) B3399671
theorem B188781961 : Blo 1342990 188781961 := bstep (se 2 (by rfl) ⟨70793235, by rfl⟩ : syracuseStep 188781961 = 141586471) B141586471
theorem B6723131 : Blo 1342990 6723131 := bstep (se 1 (by rfl) ⟨5042348, by rfl⟩ : syracuseStep 6723131 = 10084697) B10084697
theorem B22967873 : Blo 1342990 22967873 := bstep (se 2 (by rfl) ⟨8612952, by rfl⟩ : syracuseStep 22967873 = 17225905) B17225905
theorem B4535891 : Blo 1342990 4535891 := bstep (se 1 (by rfl) ⟨3401918, by rfl⟩ : syracuseStep 4535891 = 6803837) B6803837
theorem B49698461 : Blo 1342990 49698461 := bstep (se 3 (by rfl) ⟨9318461, by rfl⟩ : syracuseStep 49698461 = 18636923) B18636923
theorem B11475053 : Blo 1342990 11475053 := bstep (se 3 (by rfl) ⟨2151572, by rfl⟩ : syracuseStep 11475053 = 4303145) B4303145
theorem B22976621 : Blo 1342990 22976621 := bstep (se 3 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 22976621 = 8616233) B8616233
theorem B18381035 : Blo 1342990 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B2726183 : Blo 1342990 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B2587297 : Blo 1342990 2587297 := bstep (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) B1940473
theorem B10205999 : Blo 1342990 10205999 := bstep (se 1 (by rfl) ⟨7654499, by rfl⟩ : syracuseStep 10205999 = 15308999) B15308999
theorem B4594495 : Blo 1342990 4594495 := bstep (se 1 (by rfl) ⟨3445871, by rfl⟩ : syracuseStep 4594495 = 6891743) B6891743
theorem B29080403 : Blo 1342990 29080403 := bstep (se 1 (by rfl) ⟨21810302, by rfl⟩ : syracuseStep 29080403 = 43620605) B43620605
theorem B7756955 : Blo 1342990 7756955 := bstep (se 1 (by rfl) ⟨5817716, by rfl⟩ : syracuseStep 7756955 = 11635433) B11635433
theorem B2268479 : Blo 1342990 2268479 := bstep (se 1 (by rfl) ⟨1701359, by rfl⟩ : syracuseStep 2268479 = 3402719) B3402719
theorem B3022163 : Blo 1342990 3022163 := bstep (se 1 (by rfl) ⟨2266622, by rfl⟩ : syracuseStep 3022163 = 4533245) B4533245
theorem B1343003 : Blo 1342990 1343003 := bstep (se 1 (by rfl) ⟨1007252, by rfl⟩ : syracuseStep 1343003 = 2014505) B2014505
theorem B1343023 : Blo 1342990 1343023 := bstep (se 1 (by rfl) ⟨1007267, by rfl⟩ : syracuseStep 1343023 = 2014535) B2014535
theorem B19381913 : Blo 1342990 19381913 := bstep (se 2 (by rfl) ⟨7268217, by rfl⟩ : syracuseStep 19381913 = 14536435) B14536435
theorem B2015087 : Blo 1342990 2015087 := bstep (se 1 (by rfl) ⟨1511315, by rfl⟩ : syracuseStep 2015087 = 3022631) B3022631
theorem B1343423 : Blo 1342990 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B3022919 : Blo 1342990 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B15319205 : Blo 1342990 15319205 := bstep (se 4 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 15319205 = 2872351) B2872351
theorem B13459655 : Blo 1342990 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B2015471 : Blo 1342990 2015471 := bstep (se 1 (by rfl) ⟨1511603, by rfl⟩ : syracuseStep 2015471 = 3023207) B3023207
theorem B2015609 : Blo 1342990 2015609 := bstep (se 2 (by rfl) ⟨755853, by rfl⟩ : syracuseStep 2015609 = 1511707) B1511707
theorem B3400127 : Blo 1342990 3400127 := bstep (se 1 (by rfl) ⟨2550095, by rfl⟩ : syracuseStep 3400127 = 5100191) B5100191
theorem B12919277 : Blo 1342990 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B3023351 : Blo 1342990 3023351 := bstep (se 1 (by rfl) ⟨2267513, by rfl⟩ : syracuseStep 3023351 = 4535027) B4535027
theorem B2015903 : Blo 1342990 2015903 := bstep (se 1 (by rfl) ⟨1511927, by rfl⟩ : syracuseStep 2015903 = 3023855) B3023855
theorem B9192167 : Blo 1342990 9192167 := bstep (se 1 (by rfl) ⟨6894125, by rfl⟩ : syracuseStep 9192167 = 13788251) B13788251
theorem B1434395 : Blo 1342990 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B2016071 : Blo 1342990 2016071 := bstep (se 1 (by rfl) ⟨1512053, by rfl⟩ : syracuseStep 2016071 = 3024107) B3024107
theorem B7652177 : Blo 1342990 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B6456161 : Blo 1342990 6456161 := bstep (se 2 (by rfl) ⟨2421060, by rfl⟩ : syracuseStep 6456161 = 4842121) B4842121
theorem B3449729 : Blo 1342990 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B1344415 : Blo 1342990 1344415 := bstep (se 1 (by rfl) ⟨1008311, by rfl⟩ : syracuseStep 1344415 = 2016623) B2016623
theorem B1344495 : Blo 1342990 1344495 := bstep (se 1 (by rfl) ⟨1008371, by rfl⟩ : syracuseStep 1344495 = 2016743) B2016743
theorem B7365629 : Blo 1342990 7365629 := bstep (se 3 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 7365629 = 2762111) B2762111
theorem B15311915 : Blo 1342990 15311915 := bstep (se 1 (by rfl) ⟨11483936, by rfl⟩ : syracuseStep 15311915 = 22967873) B22967873
theorem B3023927 : Blo 1342990 3023927 := bstep (se 1 (by rfl) ⟨2267945, by rfl⟩ : syracuseStep 3023927 = 4535891) B4535891
theorem B1344615 : Blo 1342990 1344615 := bstep (se 1 (by rfl) ⟨1008461, by rfl⟩ : syracuseStep 1344615 = 2016923) B2016923
theorem B3400825 : Blo 1342990 3400825 := bstep (se 2 (by rfl) ⟨1275309, by rfl⟩ : syracuseStep 3400825 = 2550619) B2550619
theorem B65438867 : Blo 1342990 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B5105065 : Blo 1342990 5105065 := bstep (se 2 (by rfl) ⟨1914399, by rfl⟩ : syracuseStep 5105065 = 3828799) B3828799
theorem B13977299 : Blo 1342990 13977299 := bstep (se 1 (by rfl) ⟨10482974, by rfl⟩ : syracuseStep 13977299 = 20965949) B20965949
theorem B251709281 : Blo 1342990 251709281 := bstep (se 2 (by rfl) ⟨94390980, by rfl⟩ : syracuseStep 251709281 = 188781961) B188781961
theorem B5171303 : Blo 1342990 5171303 := bstep (se 1 (by rfl) ⟨3878477, by rfl⟩ : syracuseStep 5171303 = 7756955) B7756955
theorem B12921275 : Blo 1342990 12921275 := bstep (se 1 (by rfl) ⟨9690956, by rfl⟩ : syracuseStep 12921275 = 19381913) B19381913
theorem B3402587 : Blo 1342990 3402587 := bstep (se 1 (by rfl) ⟨2551940, by rfl⟩ : syracuseStep 3402587 = 5103881) B5103881
theorem B3025889 : Blo 1342990 3025889 := bstep (se 2 (by rfl) ⟨1134708, by rfl⟩ : syracuseStep 3025889 = 2269417) B2269417
theorem B25209881 : Blo 1342990 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B7269821 : Blo 1342990 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B4533839 : Blo 1342990 4533839 := bstep (se 1 (by rfl) ⟨3400379, by rfl⟩ : syracuseStep 4533839 = 6800759) B6800759
theorem B3403529 : Blo 1342990 3403529 := bstep (se 2 (by rfl) ⟨1276323, by rfl⟩ : syracuseStep 3403529 = 2552647) B2552647
theorem B4304927 : Blo 1342990 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B1912987 : Blo 1342990 1912987 := bstep (se 1 (by rfl) ⟨1434740, by rfl⟩ : syracuseStep 1912987 = 2869481) B2869481
theorem B17928349 : Blo 1342990 17928349 := bstep (se 3 (by rfl) ⟨3361565, by rfl⟩ : syracuseStep 17928349 = 6723131) B6723131
theorem B17469665 : Blo 1342990 17469665 := bstep (se 2 (by rfl) ⟨6551124, by rfl⟩ : syracuseStep 17469665 = 13102249) B13102249
theorem B15298793 : Blo 1342990 15298793 := bstep (se 2 (by rfl) ⟨5737047, by rfl⟩ : syracuseStep 15298793 = 11474095) B11474095
theorem B6803999 : Blo 1342990 6803999 := bstep (se 1 (by rfl) ⟨5102999, by rfl⟩ : syracuseStep 6803999 = 10205999) B10205999
theorem B19386935 : Blo 1342990 19386935 := bstep (se 1 (by rfl) ⟨14540201, by rfl⟩ : syracuseStep 19386935 = 29080403) B29080403
theorem B116208431 : Blo 1342990 116208431 := bstep (se 1 (by rfl) ⟨87156323, by rfl⟩ : syracuseStep 116208431 = 174312647) B174312647
theorem B8614775 : Blo 1342990 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B1512319 : Blo 1342990 1512319 := bstep (se 1 (by rfl) ⟨1134239, by rfl⟩ : syracuseStep 1512319 = 2268479) B2268479
theorem B12432761 : Blo 1342990 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B29070971 : Blo 1342990 29070971 := bstep (se 1 (by rfl) ⟨21803228, by rfl⟩ : syracuseStep 29070971 = 43606457) B43606457
theorem B1816201 : Blo 1342990 1816201 := bstep (se 2 (by rfl) ⟨681075, by rfl⟩ : syracuseStep 1816201 = 1362151) B1362151
theorem B27965657 : Blo 1342990 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B4536539 : Blo 1342990 4536539 := bstep (se 1 (by rfl) ⟨3402404, by rfl⟩ : syracuseStep 4536539 = 6804809) B6804809
theorem B6125993 : Blo 1342990 6125993 := bstep (se 2 (by rfl) ⟨2297247, by rfl⟩ : syracuseStep 6125993 = 4594495) B4594495
theorem B7649761 : Blo 1342990 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B7650035 : Blo 1342990 7650035 := bstep (se 1 (by rfl) ⟨5737526, by rfl⟩ : syracuseStep 7650035 = 11475053) B11475053
theorem B15317747 : Blo 1342990 15317747 := bstep (se 1 (by rfl) ⟨11488310, by rfl⟩ : syracuseStep 15317747 = 22976621) B22976621
theorem B12254023 : Blo 1342990 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B5102423 : Blo 1342990 5102423 := bstep (se 1 (by rfl) ⟨3826817, by rfl⟩ : syracuseStep 5102423 = 7653635) B7653635
theorem B5741543 : Blo 1342990 5741543 := bstep (se 1 (by rfl) ⟨4306157, by rfl⟩ : syracuseStep 5741543 = 8612315) B8612315
theorem B132529229 : Blo 1342990 132529229 := bstep (se 3 (by rfl) ⟨24849230, by rfl⟩ : syracuseStep 132529229 = 49698461) B49698461
theorem B3021929 : Blo 1342990 3021929 := bstep (se 2 (by rfl) ⟨1133223, by rfl⟩ : syracuseStep 3021929 = 2266447) B2266447
theorem B3022055 : Blo 1342990 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B5102939 : Blo 1342990 5102939 := bstep (se 1 (by rfl) ⟨3827204, by rfl⟩ : syracuseStep 5102939 = 7654409) B7654409
theorem B2268587 : Blo 1342990 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B2153899 : Blo 1342990 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B2014697 : Blo 1342990 2014697 := bstep (se 2 (by rfl) ⟨755511, by rfl⟩ : syracuseStep 2014697 = 1511023) B1511023
theorem B2014775 : Blo 1342990 2014775 := bstep (se 1 (by rfl) ⟨1511081, by rfl⟩ : syracuseStep 2014775 = 3022163) B3022163
theorem B1343391 : Blo 1342990 1343391 := bstep (se 1 (by rfl) ⟨1007543, by rfl⟩ : syracuseStep 1343391 = 2015087) B2015087
theorem B2015279 : Blo 1342990 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B10199195 : Blo 1342990 10199195 := bstep (se 1 (by rfl) ⟨7649396, by rfl⟩ : syracuseStep 10199195 = 15298793) B15298793
theorem B1343647 : Blo 1342990 1343647 := bstep (se 1 (by rfl) ⟨1007735, by rfl⟩ : syracuseStep 1343647 = 2015471) B2015471
theorem B1343739 : Blo 1342990 1343739 := bstep (se 1 (by rfl) ⟨1007804, by rfl⟩ : syracuseStep 1343739 = 2015609) B2015609
theorem B2015567 : Blo 1342990 2015567 := bstep (se 1 (by rfl) ⟨1511675, by rfl⟩ : syracuseStep 2015567 = 3023351) B3023351
theorem B1343935 : Blo 1342990 1343935 := bstep (se 1 (by rfl) ⟨1007951, by rfl⟩ : syracuseStep 1343935 = 2015903) B2015903
theorem B6128111 : Blo 1342990 6128111 := bstep (se 1 (by rfl) ⟨4596083, by rfl⟩ : syracuseStep 6128111 = 9192167) B9192167
theorem B77472287 : Blo 1342990 77472287 := bstep (se 1 (by rfl) ⟨58104215, by rfl⟩ : syracuseStep 77472287 = 116208431) B116208431
theorem B1344047 : Blo 1342990 1344047 := bstep (se 1 (by rfl) ⟨1008035, by rfl⟩ : syracuseStep 1344047 = 2016071) B2016071
theorem B5743183 : Blo 1342990 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B10199681 : Blo 1342990 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B10207943 : Blo 1342990 10207943 := bstep (se 1 (by rfl) ⟨7655957, by rfl⟩ : syracuseStep 10207943 = 15311915) B15311915
theorem B2015951 : Blo 1342990 2015951 := bstep (se 1 (by rfl) ⟨1511963, by rfl⟩ : syracuseStep 2015951 = 3023927) B3023927
theorem B2016425 : Blo 1342990 2016425 := bstep (se 2 (by rfl) ⟨756159, by rfl⟩ : syracuseStep 2016425 = 1512319) B1512319
theorem B167806187 : Blo 1342990 167806187 := bstep (se 1 (by rfl) ⟨125854640, by rfl⟩ : syracuseStep 167806187 = 251709281) B251709281
theorem B3024359 : Blo 1342990 3024359 := bstep (se 1 (by rfl) ⟨2268269, by rfl⟩ : syracuseStep 3024359 = 4536539) B4536539
theorem B3401615 : Blo 1342990 3401615 := bstep (se 1 (by rfl) ⟨2551211, by rfl⟩ : syracuseStep 3401615 = 5102423) B5102423
theorem B2017259 : Blo 1342990 2017259 := bstep (se 1 (by rfl) ⟨1512944, by rfl⟩ : syracuseStep 2017259 = 3025889) B3025889
theorem B3827695 : Blo 1342990 3827695 := bstep (se 1 (by rfl) ⟨2870771, by rfl⟩ : syracuseStep 3827695 = 5741543) B5741543
theorem B88352819 : Blo 1342990 88352819 := bstep (se 1 (by rfl) ⟨66264614, by rfl⟩ : syracuseStep 88352819 = 132529229) B132529229
theorem B3401959 : Blo 1342990 3401959 := bstep (se 1 (by rfl) ⟨2551469, by rfl⟩ : syracuseStep 3401959 = 5102939) B5102939
theorem B11479805 : Blo 1342990 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B8612851 : Blo 1342990 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B35892413 : Blo 1342990 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B4304107 : Blo 1342990 4304107 := bstep (se 1 (by rfl) ⟨3228080, by rfl⟩ : syracuseStep 4304107 = 6456161) B6456161
theorem B382471445 : Blo 1342990 382471445 := bstep (se 6 (by rfl) ⟨8964174, by rfl⟩ : syracuseStep 382471445 = 17928349) B17928349
theorem B4910419 : Blo 1342990 4910419 := bstep (se 1 (by rfl) ⟨3682814, by rfl⟩ : syracuseStep 4910419 = 7365629) B7365629
theorem B9686405 : Blo 1342990 9686405 := bstep (se 4 (by rfl) ⟨908100, by rfl⟩ : syracuseStep 9686405 = 1816201) B1816201
theorem B43625911 : Blo 1342990 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B10202597 : Blo 1342990 10202597 := bstep (se 4 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 10202597 = 1912987) B1912987
theorem B9318199 : Blo 1342990 9318199 := bstep (se 1 (by rfl) ⟨6988649, by rfl⟩ : syracuseStep 9318199 = 13977299) B13977299
theorem B4534433 : Blo 1342990 4534433 := bstep (se 2 (by rfl) ⟨1700412, by rfl⟩ : syracuseStep 4534433 = 3400825) B3400825
theorem B4083995 : Blo 1342990 4083995 := bstep (se 1 (by rfl) ⟨3062996, by rfl⟩ : syracuseStep 4083995 = 6125993) B6125993
theorem B8614183 : Blo 1342990 8614183 := bstep (se 1 (by rfl) ⟨6460637, by rfl⟩ : syracuseStep 8614183 = 12921275) B12921275
theorem B5100023 : Blo 1342990 5100023 := bstep (se 1 (by rfl) ⟨3825017, by rfl⟩ : syracuseStep 5100023 = 7650035) B7650035
theorem B10211831 : Blo 1342990 10211831 := bstep (se 1 (by rfl) ⟨7658873, by rfl⟩ : syracuseStep 10211831 = 15317747) B15317747
theorem B2871865 : Blo 1342990 2871865 := bstep (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) B2153899
theorem B16806587 : Blo 1342990 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B1512391 : Blo 1342990 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B4846547 : Blo 1342990 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B10212803 : Blo 1342990 10212803 := bstep (se 1 (by rfl) ⟨7659602, by rfl⟩ : syracuseStep 10212803 = 15319205) B15319205
theorem B11646443 : Blo 1342990 11646443 := bstep (se 1 (by rfl) ⟨8734832, by rfl⟩ : syracuseStep 11646443 = 17469665) B17469665
theorem B2266751 : Blo 1342990 2266751 := bstep (se 1 (by rfl) ⟨1700063, by rfl⟩ : syracuseStep 2266751 = 3400127) B3400127
theorem B4535999 : Blo 1342990 4535999 := bstep (se 1 (by rfl) ⟨3401999, by rfl⟩ : syracuseStep 4535999 = 6803999) B6803999
theorem B12924623 : Blo 1342990 12924623 := bstep (se 1 (by rfl) ⟨9693467, by rfl⟩ : syracuseStep 12924623 = 19386935) B19386935
theorem B5101451 : Blo 1342990 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B8288507 : Blo 1342990 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B19380647 : Blo 1342990 19380647 := bstep (se 1 (by rfl) ⟨14535485, by rfl⟩ : syracuseStep 19380647 = 29070971) B29070971
theorem B3447535 : Blo 1342990 3447535 := bstep (se 1 (by rfl) ⟨2585651, by rfl⟩ : syracuseStep 3447535 = 5171303) B5171303
theorem B18643771 : Blo 1342990 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B65354789 : Blo 1342990 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B6806753 : Blo 1342990 6806753 := bstep (se 2 (by rfl) ⟨2552532, by rfl⟩ : syracuseStep 6806753 = 5105065) B5105065
theorem B2268391 : Blo 1342990 2268391 := bstep (se 1 (by rfl) ⟨1701293, by rfl⟩ : syracuseStep 2268391 = 3402587) B3402587
theorem B2014619 : Blo 1342990 2014619 := bstep (se 1 (by rfl) ⟨1510964, by rfl⟩ : syracuseStep 2014619 = 3021929) B3021929
theorem B3825053 : Blo 1342990 3825053 := bstep (se 3 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 3825053 = 1434395) B1434395
theorem B2014703 : Blo 1342990 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1343131 : Blo 1342990 1343131 := bstep (se 1 (by rfl) ⟨1007348, by rfl⟩ : syracuseStep 1343131 = 2014697) B2014697
theorem B9199277 : Blo 1342990 9199277 := bstep (se 3 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 9199277 = 3449729) B3449729
theorem B1343183 : Blo 1342990 1343183 := bstep (se 1 (by rfl) ⟨1007387, by rfl⟩ : syracuseStep 1343183 = 2014775) B2014775
theorem B3022559 : Blo 1342990 3022559 := bstep (se 1 (by rfl) ⟨2266919, by rfl⟩ : syracuseStep 3022559 = 4533839) B4533839
theorem B2269019 : Blo 1342990 2269019 := bstep (se 1 (by rfl) ⟨1701764, by rfl⟩ : syracuseStep 2269019 = 3403529) B3403529
theorem B1343519 : Blo 1342990 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B6799463 : Blo 1342990 6799463 := bstep (se 1 (by rfl) ⟨5099597, by rfl⟩ : syracuseStep 6799463 = 10199195) B10199195
theorem B3022955 : Blo 1342990 3022955 := bstep (se 1 (by rfl) ⟨2267216, by rfl⟩ : syracuseStep 3022955 = 4534433) B4534433
theorem B1343711 : Blo 1342990 1343711 := bstep (se 1 (by rfl) ⟨1007783, by rfl⟩ : syracuseStep 1343711 = 2015567) B2015567
theorem B3400015 : Blo 1342990 3400015 := bstep (se 1 (by rfl) ⟨2550011, by rfl⟩ : syracuseStep 3400015 = 5100023) B5100023
theorem B6807887 : Blo 1342990 6807887 := bstep (se 1 (by rfl) ⟨5105915, by rfl⟩ : syracuseStep 6807887 = 10211831) B10211831
theorem B11485577 : Blo 1342990 11485577 := bstep (se 2 (by rfl) ⟨4307091, by rfl⟩ : syracuseStep 11485577 = 8614183) B8614183
theorem B6799787 : Blo 1342990 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B1343967 : Blo 1342990 1343967 := bstep (se 1 (by rfl) ⟨1007975, by rfl⟩ : syracuseStep 1343967 = 2015951) B2015951
theorem B1344283 : Blo 1342990 1344283 := bstep (se 1 (by rfl) ⟨1008212, by rfl⟩ : syracuseStep 1344283 = 2016425) B2016425
theorem B111870791 : Blo 1342990 111870791 := bstep (se 1 (by rfl) ⟨83903093, by rfl⟩ : syracuseStep 111870791 = 167806187) B167806187
theorem B6808535 : Blo 1342990 6808535 := bstep (se 1 (by rfl) ⟨5106401, by rfl⟩ : syracuseStep 6808535 = 10212803) B10212803
theorem B4596713 : Blo 1342990 4596713 := bstep (se 2 (by rfl) ⟨1723767, by rfl⟩ : syracuseStep 4596713 = 3447535) B3447535
theorem B2016239 : Blo 1342990 2016239 := bstep (se 1 (by rfl) ⟨1512179, by rfl⟩ : syracuseStep 2016239 = 3024359) B3024359
theorem B3023999 : Blo 1342990 3023999 := bstep (se 1 (by rfl) ⟨2267999, by rfl⟩ : syracuseStep 3023999 = 4535999) B4535999
theorem B3400967 : Blo 1342990 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B2016521 : Blo 1342990 2016521 := bstep (se 2 (by rfl) ⟨756195, by rfl⟩ : syracuseStep 2016521 = 1512391) B1512391
theorem B1344839 : Blo 1342990 1344839 := bstep (se 1 (by rfl) ⟨1008629, by rfl⟩ : syracuseStep 1344839 = 2017259) B2017259
theorem B58901879 : Blo 1342990 58901879 := bstep (se 1 (by rfl) ⟨44176409, by rfl⟩ : syracuseStep 58901879 = 88352819) B88352819
theorem B12920431 : Blo 1342990 12920431 := bstep (se 1 (by rfl) ⟨9690323, by rfl⟩ : syracuseStep 12920431 = 19380647) B19380647
theorem B3024521 : Blo 1342990 3024521 := bstep (se 2 (by rfl) ⟨1134195, by rfl⟩ : syracuseStep 3024521 = 2268391) B2268391
theorem B6547225 : Blo 1342990 6547225 := bstep (se 2 (by rfl) ⟨2455209, by rfl⟩ : syracuseStep 6547225 = 4910419) B4910419
theorem B7653203 : Blo 1342990 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B6457603 : Blo 1342990 6457603 := bstep (se 1 (by rfl) ⟨4843202, by rfl⟩ : syracuseStep 6457603 = 9686405) B9686405
theorem B2550035 : Blo 1342990 2550035 := bstep (se 1 (by rfl) ⟨1912526, by rfl⟩ : syracuseStep 2550035 = 3825053) B3825053
theorem B6801731 : Blo 1342990 6801731 := bstep (se 1 (by rfl) ⟨5101298, by rfl⟩ : syracuseStep 6801731 = 10202597) B10202597
theorem B2722663 : Blo 1342990 2722663 := bstep (se 1 (by rfl) ⟨2041997, by rfl⟩ : syracuseStep 2722663 = 4083995) B4083995
theorem B3231031 : Blo 1342990 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B3829153 : Blo 1342990 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B24858361 : Blo 1342990 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B1511167 : Blo 1342990 1511167 := bstep (se 1 (by rfl) ⟨1133375, by rfl⟩ : syracuseStep 1511167 = 2266751) B2266751
theorem B5525671 : Blo 1342990 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B5738809 : Blo 1342990 5738809 := bstep (se 2 (by rfl) ⟨2152053, by rfl⟩ : syracuseStep 5738809 = 4304107) B4304107
theorem B58167881 : Blo 1342990 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B43569859 : Blo 1342990 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B254980963 : Blo 1342990 254980963 := bstep (se 1 (by rfl) ⟨191235722, by rfl⟩ : syracuseStep 254980963 = 382471445) B382471445
theorem B12424265 : Blo 1342990 12424265 := bstep (se 2 (by rfl) ⟨4659099, by rfl⟩ : syracuseStep 12424265 = 9318199) B9318199
theorem B6132851 : Blo 1342990 6132851 := bstep (se 1 (by rfl) ⟨4599638, by rfl⟩ : syracuseStep 6132851 = 9199277) B9199277
theorem B1512679 : Blo 1342990 1512679 := bstep (se 1 (by rfl) ⟨1134509, by rfl⟩ : syracuseStep 1512679 = 2269019) B2269019
theorem B4535945 : Blo 1342990 4535945 := bstep (se 2 (by rfl) ⟨1700979, by rfl⟩ : syracuseStep 4535945 = 3401959) B3401959
theorem B4085407 : Blo 1342990 4085407 := bstep (se 1 (by rfl) ⟨3064055, by rfl⟩ : syracuseStep 4085407 = 6128111) B6128111
theorem B51648191 : Blo 1342990 51648191 := bstep (se 1 (by rfl) ⟨38736143, by rfl⟩ : syracuseStep 51648191 = 77472287) B77472287
theorem B6805295 : Blo 1342990 6805295 := bstep (se 1 (by rfl) ⟨5103971, by rfl⟩ : syracuseStep 6805295 = 10207943) B10207943
theorem B7657577 : Blo 1342990 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B7764295 : Blo 1342990 7764295 := bstep (se 1 (by rfl) ⟨5823221, by rfl⟩ : syracuseStep 7764295 = 11646443) B11646443
theorem B8616415 : Blo 1342990 8616415 := bstep (se 1 (by rfl) ⟨6462311, by rfl⟩ : syracuseStep 8616415 = 12924623) B12924623
theorem B2267743 : Blo 1342990 2267743 := bstep (se 1 (by rfl) ⟨1700807, by rfl⟩ : syracuseStep 2267743 = 3401615) B3401615
theorem B11483801 : Blo 1342990 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B44817565 : Blo 1342990 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B23928275 : Blo 1342990 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B4537835 : Blo 1342990 4537835 := bstep (se 1 (by rfl) ⟨3403376, by rfl⟩ : syracuseStep 4537835 = 6806753) B6806753
theorem B1343079 : Blo 1342990 1343079 := bstep (se 1 (by rfl) ⟨1007309, by rfl⟩ : syracuseStep 1343079 = 2014619) B2014619
theorem B1343135 : Blo 1342990 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B2015039 : Blo 1342990 2015039 := bstep (se 1 (by rfl) ⟨1511279, by rfl⟩ : syracuseStep 2015039 = 3022559) B3022559
theorem B5103593 : Blo 1342990 5103593 := bstep (se 2 (by rfl) ⟨1913847, by rfl⟩ : syracuseStep 5103593 = 3827695) B3827695
theorem B2015303 : Blo 1342990 2015303 := bstep (se 1 (by rfl) ⟨1511477, by rfl⟩ : syracuseStep 2015303 = 3022955) B3022955
theorem B4538591 : Blo 1342990 4538591 := bstep (se 1 (by rfl) ⟨3403943, by rfl⟩ : syracuseStep 4538591 = 6807887) B6807887
theorem B8610137 : Blo 1342990 8610137 := bstep (se 2 (by rfl) ⟨3228801, by rfl⟩ : syracuseStep 8610137 = 6457603) B6457603
theorem B7651745 : Blo 1342990 7651745 := bstep (se 2 (by rfl) ⟨2869404, by rfl⟩ : syracuseStep 7651745 = 5738809) B5738809
theorem B74580527 : Blo 1342990 74580527 := bstep (se 1 (by rfl) ⟨55935395, by rfl⟩ : syracuseStep 74580527 = 111870791) B111870791
theorem B4539023 : Blo 1342990 4539023 := bstep (se 1 (by rfl) ⟨3404267, by rfl⟩ : syracuseStep 4539023 = 6808535) B6808535
theorem B3064475 : Blo 1342990 3064475 := bstep (se 1 (by rfl) ⟨2298356, by rfl⟩ : syracuseStep 3064475 = 4596713) B4596713
theorem B1344159 : Blo 1342990 1344159 := bstep (se 1 (by rfl) ⟨1008119, by rfl⟩ : syracuseStep 1344159 = 2016239) B2016239
theorem B8282843 : Blo 1342990 8282843 := bstep (se 1 (by rfl) ⟨6212132, by rfl⟩ : syracuseStep 8282843 = 12424265) B12424265
theorem B4088567 : Blo 1342990 4088567 := bstep (se 1 (by rfl) ⟨3066425, by rfl⟩ : syracuseStep 4088567 = 6132851) B6132851
theorem B2015999 : Blo 1342990 2015999 := bstep (se 1 (by rfl) ⟨1511999, by rfl⟩ : syracuseStep 2015999 = 3023999) B3023999
theorem B3023657 : Blo 1342990 3023657 := bstep (se 2 (by rfl) ⟨1133871, by rfl⟩ : syracuseStep 3023657 = 2267743) B2267743
theorem B1344347 : Blo 1342990 1344347 := bstep (se 1 (by rfl) ⟨1008260, by rfl⟩ : syracuseStep 1344347 = 2016521) B2016521
theorem B3023963 : Blo 1342990 3023963 := bstep (se 1 (by rfl) ⟨2267972, by rfl⟩ : syracuseStep 3023963 = 4535945) B4535945
theorem B2016347 : Blo 1342990 2016347 := bstep (se 1 (by rfl) ⟨1512260, by rfl⟩ : syracuseStep 2016347 = 3024521) B3024521
theorem B34432127 : Blo 1342990 34432127 := bstep (se 1 (by rfl) ⟨25824095, by rfl⟩ : syracuseStep 34432127 = 51648191) B51648191
theorem B5105051 : Blo 1342990 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B2016905 : Blo 1342990 2016905 := bstep (se 2 (by rfl) ⟨756339, by rfl⟩ : syracuseStep 2016905 = 1512679) B1512679
theorem B5105537 : Blo 1342990 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B15952183 : Blo 1342990 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B3025223 : Blo 1342990 3025223 := bstep (se 1 (by rfl) ⟨2268917, by rfl⟩ : syracuseStep 3025223 = 4537835) B4537835
theorem B3402395 : Blo 1342990 3402395 := bstep (se 1 (by rfl) ⟨2551796, by rfl⟩ : syracuseStep 3402395 = 5103593) B5103593
theorem B4532975 : Blo 1342990 4532975 := bstep (se 1 (by rfl) ⟨3399731, by rfl⟩ : syracuseStep 4532975 = 6799463) B6799463
theorem B7367561 : Blo 1342990 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B4533191 : Blo 1342990 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B4533353 : Blo 1342990 4533353 := bstep (se 2 (by rfl) ⟨1700007, by rfl⟩ : syracuseStep 4533353 = 3400015) B3400015
theorem B11488553 : Blo 1342990 11488553 := bstep (se 2 (by rfl) ⟨4308207, by rfl⟩ : syracuseStep 11488553 = 8616415) B8616415
theorem B39267919 : Blo 1342990 39267919 := bstep (se 1 (by rfl) ⟨29450939, by rfl⟩ : syracuseStep 39267919 = 58901879) B58901879
theorem B58093145 : Blo 1342990 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B1700023 : Blo 1342990 1700023 := bstep (se 1 (by rfl) ⟨1275017, by rfl⟩ : syracuseStep 1700023 = 2550035) B2550035
theorem B59756753 : Blo 1342990 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B4534487 : Blo 1342990 4534487 := bstep (se 1 (by rfl) ⟨3400865, by rfl⟩ : syracuseStep 4534487 = 6801731) B6801731
theorem B7655867 : Blo 1342990 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B14520869 : Blo 1342990 14520869 := bstep (se 4 (by rfl) ⟨1361331, by rfl⟩ : syracuseStep 14520869 = 2722663) B2722663
theorem B8729633 : Blo 1342990 8729633 := bstep (se 2 (by rfl) ⟨3273612, by rfl⟩ : syracuseStep 8729633 = 6547225) B6547225
theorem B7657051 : Blo 1342990 7657051 := bstep (se 1 (by rfl) ⟨5742788, by rfl⟩ : syracuseStep 7657051 = 11485577) B11485577
theorem B38778587 : Blo 1342990 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B10352393 : Blo 1342990 10352393 := bstep (se 2 (by rfl) ⟨3882147, by rfl⟩ : syracuseStep 10352393 = 7764295) B7764295
theorem B2267311 : Blo 1342990 2267311 := bstep (se 1 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 2267311 = 3400967) B3400967
theorem B339974617 : Blo 1342990 339974617 := bstep (se 2 (by rfl) ⟨127490481, by rfl⟩ : syracuseStep 339974617 = 254980963) B254980963
theorem B4536863 : Blo 1342990 4536863 := bstep (se 1 (by rfl) ⟨3402647, by rfl⟩ : syracuseStep 4536863 = 6805295) B6805295
theorem B5102135 : Blo 1342990 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B4308041 : Blo 1342990 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B17227241 : Blo 1342990 17227241 := bstep (se 2 (by rfl) ⟨6460215, by rfl⟩ : syracuseStep 17227241 = 12920431) B12920431
theorem B5447209 : Blo 1342990 5447209 := bstep (se 2 (by rfl) ⟨2042703, by rfl⟩ : syracuseStep 5447209 = 4085407) B4085407
theorem B33144481 : Blo 1342990 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B2014889 : Blo 1342990 2014889 := bstep (se 2 (by rfl) ⟨755583, by rfl⟩ : syracuseStep 2014889 = 1511167) B1511167
theorem B1343359 : Blo 1342990 1343359 := bstep (se 1 (by rfl) ⟨1007519, by rfl⟩ : syracuseStep 1343359 = 2015039) B2015039
theorem B1343535 : Blo 1342990 1343535 := bstep (se 1 (by rfl) ⟨1007651, by rfl⟩ : syracuseStep 1343535 = 2015303) B2015303
theorem B39837835 : Blo 1342990 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B3022991 : Blo 1342990 3022991 := bstep (se 1 (by rfl) ⟨2267243, by rfl⟩ : syracuseStep 3022991 = 4534487) B4534487
theorem B3023081 : Blo 1342990 3023081 := bstep (se 2 (by rfl) ⟨1133655, by rfl⟩ : syracuseStep 3023081 = 2267311) B2267311
theorem B5103911 : Blo 1342990 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B5521895 : Blo 1342990 5521895 := bstep (se 1 (by rfl) ⟨4141421, by rfl⟩ : syracuseStep 5521895 = 8282843) B8282843
theorem B1343999 : Blo 1342990 1343999 := bstep (se 1 (by rfl) ⟨1007999, by rfl⟩ : syracuseStep 1343999 = 2015999) B2015999
theorem B2015771 : Blo 1342990 2015771 := bstep (se 1 (by rfl) ⟨1511828, by rfl⟩ : syracuseStep 2015771 = 3023657) B3023657
theorem B2015975 : Blo 1342990 2015975 := bstep (se 1 (by rfl) ⟨1511981, by rfl⟩ : syracuseStep 2015975 = 3023963) B3023963
theorem B1344231 : Blo 1342990 1344231 := bstep (se 1 (by rfl) ⟨1008173, by rfl⟩ : syracuseStep 1344231 = 2016347) B2016347
theorem B22954751 : Blo 1342990 22954751 := bstep (se 1 (by rfl) ⟨17216063, by rfl⟩ : syracuseStep 22954751 = 34432127) B34432127
theorem B1344603 : Blo 1342990 1344603 := bstep (se 1 (by rfl) ⟨1008452, by rfl⟩ : syracuseStep 1344603 = 2016905) B2016905
theorem B2016815 : Blo 1342990 2016815 := bstep (se 1 (by rfl) ⟨1512611, by rfl⟩ : syracuseStep 2016815 = 3025223) B3025223
theorem B3024575 : Blo 1342990 3024575 := bstep (se 1 (by rfl) ⟨2268431, by rfl⟩ : syracuseStep 3024575 = 4536863) B4536863
theorem B3401423 : Blo 1342990 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B52357225 : Blo 1342990 52357225 := bstep (se 2 (by rfl) ⟨19633959, by rfl⟩ : syracuseStep 52357225 = 39267919) B39267919
theorem B10209401 : Blo 1342990 10209401 := bstep (se 2 (by rfl) ⟨3828525, by rfl⟩ : syracuseStep 10209401 = 7657051) B7657051
theorem B3025727 : Blo 1342990 3025727 := bstep (se 1 (by rfl) ⟨2269295, by rfl⟩ : syracuseStep 3025727 = 4538591) B4538591
theorem B3026015 : Blo 1342990 3026015 := bstep (se 1 (by rfl) ⟨2269511, by rfl⟩ : syracuseStep 3026015 = 4539023) B4539023
theorem B2042983 : Blo 1342990 2042983 := bstep (se 1 (by rfl) ⟨1532237, by rfl⟩ : syracuseStep 2042983 = 3064475) B3064475
theorem B453299489 : Blo 1342990 453299489 := bstep (se 2 (by rfl) ⟨169987308, by rfl⟩ : syracuseStep 453299489 = 339974617) B339974617
theorem B3403367 : Blo 1342990 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B6901595 : Blo 1342990 6901595 := bstep (se 1 (by rfl) ⟨5176196, by rfl⟩ : syracuseStep 6901595 = 10352393) B10352393
theorem B3403691 : Blo 1342990 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B198881405 : Blo 1342990 198881405 := bstep (se 3 (by rfl) ⟨37290263, by rfl⟩ : syracuseStep 198881405 = 74580527) B74580527
theorem B85078309 : Blo 1342990 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B4911707 : Blo 1342990 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B2872027 : Blo 1342990 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B7262945 : Blo 1342990 7262945 := bstep (se 2 (by rfl) ⟨2723604, by rfl⟩ : syracuseStep 7262945 = 5447209) B5447209
theorem B44192641 : Blo 1342990 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B38728763 : Blo 1342990 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B23279021 : Blo 1342990 23279021 := bstep (se 3 (by rfl) ⟨4364816, by rfl⟩ : syracuseStep 23279021 = 8729633) B8729633
theorem B5740091 : Blo 1342990 5740091 := bstep (se 1 (by rfl) ⟨4305068, by rfl⟩ : syracuseStep 5740091 = 8610137) B8610137
theorem B2266697 : Blo 1342990 2266697 := bstep (se 2 (by rfl) ⟨850011, by rfl⟩ : syracuseStep 2266697 = 1700023) B1700023
theorem B5101163 : Blo 1342990 5101163 := bstep (se 1 (by rfl) ⟨3825872, by rfl⟩ : syracuseStep 5101163 = 7651745) B7651745
theorem B9680579 : Blo 1342990 9680579 := bstep (se 1 (by rfl) ⟨7260434, by rfl⟩ : syracuseStep 9680579 = 14520869) B14520869
theorem B25852391 : Blo 1342990 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B2268263 : Blo 1342990 2268263 := bstep (se 1 (by rfl) ⟨1701197, by rfl⟩ : syracuseStep 2268263 = 3402395) B3402395
theorem B3021983 : Blo 1342990 3021983 := bstep (se 1 (by rfl) ⟨2266487, by rfl⟩ : syracuseStep 3021983 = 4532975) B4532975
theorem B3022127 : Blo 1342990 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B10902845 : Blo 1342990 10902845 := bstep (se 3 (by rfl) ⟨2044283, by rfl⟩ : syracuseStep 10902845 = 4088567) B4088567
theorem B3022235 : Blo 1342990 3022235 := bstep (se 1 (by rfl) ⟨2266676, by rfl⟩ : syracuseStep 3022235 = 4533353) B4533353
theorem B7659035 : Blo 1342990 7659035 := bstep (se 1 (by rfl) ⟨5744276, by rfl⟩ : syracuseStep 7659035 = 11488553) B11488553
theorem B11484827 : Blo 1342990 11484827 := bstep (se 1 (by rfl) ⟨8613620, by rfl⟩ : syracuseStep 11484827 = 17227241) B17227241
theorem B1343259 : Blo 1342990 1343259 := bstep (se 1 (by rfl) ⟨1007444, by rfl⟩ : syracuseStep 1343259 = 2014889) B2014889
theorem B132587603 : Blo 1342990 132587603 := bstep (se 1 (by rfl) ⟨99440702, by rfl⟩ : syracuseStep 132587603 = 198881405) B198881405
theorem B2015327 : Blo 1342990 2015327 := bstep (se 1 (by rfl) ⟨1511495, by rfl⟩ : syracuseStep 2015327 = 3022991) B3022991
theorem B2015387 : Blo 1342990 2015387 := bstep (se 1 (by rfl) ⟨1511540, by rfl⟩ : syracuseStep 2015387 = 3023081) B3023081
theorem B1343847 : Blo 1342990 1343847 := bstep (se 1 (by rfl) ⟨1007885, by rfl⟩ : syracuseStep 1343847 = 2015771) B2015771
theorem B4841963 : Blo 1342990 4841963 := bstep (se 1 (by rfl) ⟨3631472, by rfl⟩ : syracuseStep 4841963 = 7262945) B7262945
theorem B1343983 : Blo 1342990 1343983 := bstep (se 1 (by rfl) ⟨1007987, by rfl⟩ : syracuseStep 1343983 = 2015975) B2015975
theorem B15303167 : Blo 1342990 15303167 := bstep (se 1 (by rfl) ⟨11477375, by rfl⟩ : syracuseStep 15303167 = 22954751) B22954751
theorem B212468453 : Blo 1342990 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B1344543 : Blo 1342990 1344543 := bstep (se 1 (by rfl) ⟨1008407, by rfl⟩ : syracuseStep 1344543 = 2016815) B2016815
theorem B3826727 : Blo 1342990 3826727 := bstep (se 1 (by rfl) ⟨2870045, by rfl⟩ : syracuseStep 3826727 = 5740091) B5740091
theorem B3400775 : Blo 1342990 3400775 := bstep (se 1 (by rfl) ⟨2550581, by rfl⟩ : syracuseStep 3400775 = 5101163) B5101163
theorem B2016383 : Blo 1342990 2016383 := bstep (se 1 (by rfl) ⟨1512287, by rfl⟩ : syracuseStep 2016383 = 3024575) B3024575
theorem B2017151 : Blo 1342990 2017151 := bstep (se 1 (by rfl) ⟨1512863, by rfl⟩ : syracuseStep 2017151 = 3025727) B3025727
theorem B2017343 : Blo 1342990 2017343 := bstep (se 1 (by rfl) ⟨1513007, by rfl⟩ : syracuseStep 2017343 = 3026015) B3026015
theorem B7268563 : Blo 1342990 7268563 := bstep (se 1 (by rfl) ⟨5451422, by rfl⟩ : syracuseStep 7268563 = 10902845) B10902845
theorem B5106023 : Blo 1342990 5106023 := bstep (se 1 (by rfl) ⟨3829517, by rfl⟩ : syracuseStep 5106023 = 7659035) B7659035
theorem B3402607 : Blo 1342990 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B3681263 : Blo 1342990 3681263 := bstep (se 1 (by rfl) ⟨2760947, by rfl⟩ : syracuseStep 3681263 = 5521895) B5521895
theorem B113437745 : Blo 1342990 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B15519347 : Blo 1342990 15519347 := bstep (se 1 (by rfl) ⟨11639510, by rfl⟩ : syracuseStep 15519347 = 23279021) B23279021
theorem B3829369 : Blo 1342990 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B1511131 : Blo 1342990 1511131 := bstep (se 1 (by rfl) ⟨1133348, by rfl⟩ : syracuseStep 1511131 = 2266697) B2266697
theorem B2723977 : Blo 1342990 2723977 := bstep (se 2 (by rfl) ⟨1021491, by rfl⟩ : syracuseStep 2723977 = 2042983) B2042983
theorem B1512175 : Blo 1342990 1512175 := bstep (se 1 (by rfl) ⟨1134131, by rfl⟩ : syracuseStep 1512175 = 2268263) B2268263
theorem B302199659 : Blo 1342990 302199659 := bstep (se 1 (by rfl) ⟨226649744, by rfl⟩ : syracuseStep 302199659 = 453299489) B453299489
theorem B7656551 : Blo 1342990 7656551 := bstep (se 1 (by rfl) ⟨5742413, by rfl⟩ : syracuseStep 7656551 = 11484827) B11484827
theorem B4601063 : Blo 1342990 4601063 := bstep (se 1 (by rfl) ⟨3450797, by rfl⟩ : syracuseStep 4601063 = 6901595) B6901595
theorem B69809633 : Blo 1342990 69809633 := bstep (se 2 (by rfl) ⟨26178612, by rfl⟩ : syracuseStep 69809633 = 52357225) B52357225
theorem B3274471 : Blo 1342990 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B25819175 : Blo 1342990 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B6453719 : Blo 1342990 6453719 := bstep (se 1 (by rfl) ⟨4840289, by rfl⟩ : syracuseStep 6453719 = 9680579) B9680579
theorem B2267615 : Blo 1342990 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B58923521 : Blo 1342990 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B6806267 : Blo 1342990 6806267 := bstep (se 1 (by rfl) ⟨5104700, by rfl⟩ : syracuseStep 6806267 = 10209401) B10209401
theorem B17234927 : Blo 1342990 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B2014655 : Blo 1342990 2014655 := bstep (se 1 (by rfl) ⟨1510991, by rfl⟩ : syracuseStep 2014655 = 3021983) B3021983
theorem B2014751 : Blo 1342990 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B2014823 : Blo 1342990 2014823 := bstep (se 1 (by rfl) ⟨1511117, by rfl⟩ : syracuseStep 2014823 = 3022235) B3022235
theorem B2268911 : Blo 1342990 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B2269127 : Blo 1342990 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B88391735 : Blo 1342990 88391735 := bstep (se 1 (by rfl) ⟨66293801, by rfl⟩ : syracuseStep 88391735 = 132587603) B132587603
theorem B1343551 : Blo 1342990 1343551 := bstep (se 1 (by rfl) ⟨1007663, by rfl⟩ : syracuseStep 1343551 = 2015327) B2015327
theorem B1343591 : Blo 1342990 1343591 := bstep (se 1 (by rfl) ⟨1007693, by rfl⟩ : syracuseStep 1343591 = 2015387) B2015387
theorem B9691417 : Blo 1342990 9691417 := bstep (se 2 (by rfl) ⟨3634281, by rfl⟩ : syracuseStep 9691417 = 7268563) B7268563
theorem B3227975 : Blo 1342990 3227975 := bstep (se 1 (by rfl) ⟨2420981, by rfl⟩ : syracuseStep 3227975 = 4841963) B4841963
theorem B201466439 : Blo 1342990 201466439 := bstep (se 1 (by rfl) ⟨151099829, by rfl⟩ : syracuseStep 201466439 = 302199659) B302199659
theorem B5104367 : Blo 1342990 5104367 := bstep (se 1 (by rfl) ⟨3828275, by rfl⟩ : syracuseStep 5104367 = 7656551) B7656551
theorem B1344255 : Blo 1342990 1344255 := bstep (se 1 (by rfl) ⟨1008191, by rfl⟩ : syracuseStep 1344255 = 2016383) B2016383
theorem B2016233 : Blo 1342990 2016233 := bstep (se 2 (by rfl) ⟨756087, by rfl⟩ : syracuseStep 2016233 = 1512175) B1512175
theorem B46539755 : Blo 1342990 46539755 := bstep (se 1 (by rfl) ⟨34904816, by rfl⟩ : syracuseStep 46539755 = 69809633) B69809633
theorem B1344767 : Blo 1342990 1344767 := bstep (se 1 (by rfl) ⟨1008575, by rfl⟩ : syracuseStep 1344767 = 2017151) B2017151
theorem B17212783 : Blo 1342990 17212783 := bstep (se 1 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 17212783 = 25819175) B25819175
theorem B1344895 : Blo 1342990 1344895 := bstep (se 1 (by rfl) ⟨1008671, by rfl⟩ : syracuseStep 1344895 = 2017343) B2017343
theorem B4302479 : Blo 1342990 4302479 := bstep (se 1 (by rfl) ⟨3226859, by rfl⟩ : syracuseStep 4302479 = 6453719) B6453719
theorem B39282347 : Blo 1342990 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B5105825 : Blo 1342990 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B3631969 : Blo 1342990 3631969 := bstep (se 2 (by rfl) ⟨1361988, by rfl⟩ : syracuseStep 3631969 = 2723977) B2723977
theorem B10202111 : Blo 1342990 10202111 := bstep (se 1 (by rfl) ⟨7651583, by rfl⟩ : syracuseStep 10202111 = 15303167) B15303167
theorem B2551151 : Blo 1342990 2551151 := bstep (se 1 (by rfl) ⟨1913363, by rfl⟩ : syracuseStep 2551151 = 3826727) B3826727
theorem B3067375 : Blo 1342990 3067375 := bstep (se 1 (by rfl) ⟨2300531, by rfl⟩ : syracuseStep 3067375 = 4601063) B4601063
theorem B3404015 : Blo 1342990 3404015 := bstep (se 1 (by rfl) ⟨2553011, by rfl⟩ : syracuseStep 3404015 = 5106023) B5106023
theorem B1511743 : Blo 1342990 1511743 := bstep (se 1 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 1511743 = 2267615) B2267615
theorem B2454175 : Blo 1342990 2454175 := bstep (se 1 (by rfl) ⟨1840631, by rfl⟩ : syracuseStep 2454175 = 3681263) B3681263
theorem B11489951 : Blo 1342990 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B75625163 : Blo 1342990 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B1512607 : Blo 1342990 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B1512751 : Blo 1342990 1512751 := bstep (se 1 (by rfl) ⟨1134563, by rfl⟩ : syracuseStep 1512751 = 2269127) B2269127
theorem B141645635 : Blo 1342990 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B2267183 : Blo 1342990 2267183 := bstep (se 1 (by rfl) ⟨1700387, by rfl⟩ : syracuseStep 2267183 = 3400775) B3400775
theorem B4536809 : Blo 1342990 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B17463845 : Blo 1342990 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B4537511 : Blo 1342990 4537511 := bstep (se 1 (by rfl) ⟨3403133, by rfl⟩ : syracuseStep 4537511 = 6806267) B6806267
theorem B2014841 : Blo 1342990 2014841 := bstep (se 2 (by rfl) ⟨755565, by rfl⟩ : syracuseStep 2014841 = 1511131) B1511131
theorem B1343103 : Blo 1342990 1343103 := bstep (se 1 (by rfl) ⟨1007327, by rfl⟩ : syracuseStep 1343103 = 2014655) B2014655
theorem B1343167 : Blo 1342990 1343167 := bstep (se 1 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 1343167 = 2014751) B2014751
theorem B1343215 : Blo 1342990 1343215 := bstep (se 1 (by rfl) ⟨1007411, by rfl⟩ : syracuseStep 1343215 = 2014823) B2014823
theorem B10346231 : Blo 1342990 10346231 := bstep (se 1 (by rfl) ⟨7759673, by rfl⟩ : syracuseStep 10346231 = 15519347) B15519347
theorem B2269343 : Blo 1342990 2269343 := bstep (se 1 (by rfl) ⟨1702007, by rfl⟩ : syracuseStep 2269343 = 3404015) B3404015
theorem B2015657 : Blo 1342990 2015657 := bstep (se 2 (by rfl) ⟨755871, by rfl⟩ : syracuseStep 2015657 = 1511743) B1511743
theorem B7659967 : Blo 1342990 7659967 := bstep (se 1 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 7659967 = 11489951) B11489951
theorem B1344155 : Blo 1342990 1344155 := bstep (se 1 (by rfl) ⟨1008116, by rfl⟩ : syracuseStep 1344155 = 2016233) B2016233
theorem B2868319 : Blo 1342990 2868319 := bstep (se 1 (by rfl) ⟨2151239, by rfl⟩ : syracuseStep 2868319 = 4302479) B4302479
theorem B94430423 : Blo 1342990 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B2016809 : Blo 1342990 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B3024539 : Blo 1342990 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B11642563 : Blo 1342990 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B2017001 : Blo 1342990 2017001 := bstep (se 2 (by rfl) ⟨756375, by rfl⟩ : syracuseStep 2017001 = 1512751) B1512751
theorem B4089833 : Blo 1342990 4089833 := bstep (se 2 (by rfl) ⟨1533687, by rfl⟩ : syracuseStep 4089833 = 3067375) B3067375
theorem B6801407 : Blo 1342990 6801407 := bstep (se 1 (by rfl) ⟨5101055, by rfl⟩ : syracuseStep 6801407 = 10202111) B10202111
theorem B3025007 : Blo 1342990 3025007 := bstep (se 1 (by rfl) ⟨2268755, by rfl⟩ : syracuseStep 3025007 = 4537511) B4537511
theorem B58927823 : Blo 1342990 58927823 := bstep (se 1 (by rfl) ⟨44195867, by rfl⟩ : syracuseStep 58927823 = 88391735) B88391735
theorem B134310959 : Blo 1342990 134310959 := bstep (se 1 (by rfl) ⟨100733219, by rfl⟩ : syracuseStep 134310959 = 201466439) B201466439
theorem B50416775 : Blo 1342990 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B3402911 : Blo 1342990 3402911 := bstep (se 1 (by rfl) ⟨2552183, by rfl⟩ : syracuseStep 3402911 = 5104367) B5104367
theorem B31026503 : Blo 1342990 31026503 := bstep (se 1 (by rfl) ⟨23269877, by rfl⟩ : syracuseStep 31026503 = 46539755) B46539755
theorem B3272233 : Blo 1342990 3272233 := bstep (se 2 (by rfl) ⟨1227087, by rfl⟩ : syracuseStep 3272233 = 2454175) B2454175
theorem B1511455 : Blo 1342990 1511455 := bstep (se 1 (by rfl) ⟨1133591, by rfl⟩ : syracuseStep 1511455 = 2267183) B2267183
theorem B3403883 : Blo 1342990 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B51687557 : Blo 1342990 51687557 := bstep (se 4 (by rfl) ⟨4845708, by rfl⟩ : syracuseStep 51687557 = 9691417) B9691417
theorem B22950377 : Blo 1342990 22950377 := bstep (se 2 (by rfl) ⟨8606391, by rfl⟩ : syracuseStep 22950377 = 17212783) B17212783
theorem B19370501 : Blo 1342990 19370501 := bstep (se 4 (by rfl) ⟨1815984, by rfl⟩ : syracuseStep 19370501 = 3631969) B3631969
theorem B1700767 : Blo 1342990 1700767 := bstep (se 1 (by rfl) ⟨1275575, by rfl⟩ : syracuseStep 1700767 = 2551151) B2551151
theorem B2151983 : Blo 1342990 2151983 := bstep (se 1 (by rfl) ⟨1613987, by rfl⟩ : syracuseStep 2151983 = 3227975) B3227975
theorem B26188231 : Blo 1342990 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B1343227 : Blo 1342990 1343227 := bstep (se 1 (by rfl) ⟨1007420, by rfl⟩ : syracuseStep 1343227 = 2014841) B2014841
theorem B6897487 : Blo 1342990 6897487 := bstep (se 1 (by rfl) ⟨5173115, by rfl⟩ : syracuseStep 6897487 = 10346231) B10346231
theorem B2015273 : Blo 1342990 2015273 := bstep (se 2 (by rfl) ⟨755727, by rfl⟩ : syracuseStep 2015273 = 1511455) B1511455
theorem B2269255 : Blo 1342990 2269255 := bstep (se 1 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 2269255 = 3403883) B3403883
theorem B1343771 : Blo 1342990 1343771 := bstep (se 1 (by rfl) ⟨1007828, by rfl⟩ : syracuseStep 1343771 = 2015657) B2015657
theorem B1344539 : Blo 1342990 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B1434655 : Blo 1342990 1434655 := bstep (se 1 (by rfl) ⟨1075991, by rfl⟩ : syracuseStep 1434655 = 2151983) B2151983
theorem B2016359 : Blo 1342990 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B1344667 : Blo 1342990 1344667 := bstep (se 1 (by rfl) ⟨1008500, by rfl⟩ : syracuseStep 1344667 = 2017001) B2017001
theorem B2016671 : Blo 1342990 2016671 := bstep (se 1 (by rfl) ⟨1512503, by rfl⟩ : syracuseStep 2016671 = 3025007) B3025007
theorem B89540639 : Blo 1342990 89540639 := bstep (se 1 (by rfl) ⟨67155479, by rfl⟩ : syracuseStep 89540639 = 134310959) B134310959
theorem B34458371 : Blo 1342990 34458371 := bstep (se 1 (by rfl) ⟨25843778, by rfl⟩ : syracuseStep 34458371 = 51687557) B51687557
theorem B12913667 : Blo 1342990 12913667 := bstep (se 1 (by rfl) ⟨9685250, by rfl⟩ : syracuseStep 12913667 = 19370501) B19370501
theorem B34917641 : Blo 1342990 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B4534271 : Blo 1342990 4534271 := bstep (se 1 (by rfl) ⟨3400703, by rfl⟩ : syracuseStep 4534271 = 6801407) B6801407
theorem B39285215 : Blo 1342990 39285215 := bstep (se 1 (by rfl) ⟨29463911, by rfl⟩ : syracuseStep 39285215 = 58927823) B58927823
theorem B4362977 : Blo 1342990 4362977 := bstep (se 2 (by rfl) ⟨1636116, by rfl⟩ : syracuseStep 4362977 = 3272233) B3272233
theorem B9196649 : Blo 1342990 9196649 := bstep (se 2 (by rfl) ⟨3448743, by rfl⟩ : syracuseStep 9196649 = 6897487) B6897487
theorem B1512895 : Blo 1342990 1512895 := bstep (se 1 (by rfl) ⟨1134671, by rfl⟩ : syracuseStep 1512895 = 2269343) B2269343
theorem B15300251 : Blo 1342990 15300251 := bstep (se 1 (by rfl) ⟨11475188, by rfl⟩ : syracuseStep 15300251 = 22950377) B22950377
theorem B10213289 : Blo 1342990 10213289 := bstep (se 2 (by rfl) ⟨3829983, by rfl⟩ : syracuseStep 10213289 = 7659967) B7659967
theorem B62953615 : Blo 1342990 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B2267689 : Blo 1342990 2267689 := bstep (se 2 (by rfl) ⟨850383, by rfl⟩ : syracuseStep 2267689 = 1700767) B1700767
theorem B2726555 : Blo 1342990 2726555 := bstep (se 1 (by rfl) ⟨2044916, by rfl⟩ : syracuseStep 2726555 = 4089833) B4089833
theorem B3824425 : Blo 1342990 3824425 := bstep (se 2 (by rfl) ⟨1434159, by rfl⟩ : syracuseStep 3824425 = 2868319) B2868319
theorem B33611183 : Blo 1342990 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B2268607 : Blo 1342990 2268607 := bstep (se 1 (by rfl) ⟨1701455, by rfl⟩ : syracuseStep 2268607 = 3402911) B3402911
theorem B20684335 : Blo 1342990 20684335 := bstep (se 1 (by rfl) ⟨15513251, by rfl⟩ : syracuseStep 20684335 = 31026503) B31026503
theorem B15523417 : Blo 1342990 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B1343515 : Blo 1342990 1343515 := bstep (se 1 (by rfl) ⟨1007636, by rfl⟩ : syracuseStep 1343515 = 2015273) B2015273
theorem B7651493 : Blo 1342990 7651493 := bstep (se 4 (by rfl) ⟨717327, by rfl⟩ : syracuseStep 7651493 = 1434655) B1434655
theorem B26190143 : Blo 1342990 26190143 := bstep (se 1 (by rfl) ⟨19642607, by rfl⟩ : syracuseStep 26190143 = 39285215) B39285215
theorem B2908651 : Blo 1342990 2908651 := bstep (se 1 (by rfl) ⟨2181488, by rfl⟩ : syracuseStep 2908651 = 4362977) B4362977
theorem B3023585 : Blo 1342990 3023585 := bstep (se 2 (by rfl) ⟨1133844, by rfl⟩ : syracuseStep 3023585 = 2267689) B2267689
theorem B1344239 : Blo 1342990 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B1344447 : Blo 1342990 1344447 := bstep (se 1 (by rfl) ⟨1008335, by rfl⟩ : syracuseStep 1344447 = 2016671) B2016671
theorem B10200167 : Blo 1342990 10200167 := bstep (se 1 (by rfl) ⟨7650125, by rfl⟩ : syracuseStep 10200167 = 15300251) B15300251
theorem B6808859 : Blo 1342990 6808859 := bstep (se 1 (by rfl) ⟨5106644, by rfl⟩ : syracuseStep 6808859 = 10213289) B10213289
theorem B22972247 : Blo 1342990 22972247 := bstep (se 1 (by rfl) ⟨17229185, by rfl⟩ : syracuseStep 22972247 = 34458371) B34458371
theorem B3024809 : Blo 1342990 3024809 := bstep (se 2 (by rfl) ⟨1134303, by rfl⟩ : syracuseStep 3024809 = 2268607) B2268607
theorem B2017193 : Blo 1342990 2017193 := bstep (se 2 (by rfl) ⟨756447, by rfl⟩ : syracuseStep 2017193 = 1512895) B1512895
theorem B22407455 : Blo 1342990 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B3025673 : Blo 1342990 3025673 := bstep (se 2 (by rfl) ⟨1134627, by rfl⟩ : syracuseStep 3025673 = 2269255) B2269255
theorem B83938153 : Blo 1342990 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B6131099 : Blo 1342990 6131099 := bstep (se 1 (by rfl) ⟨4598324, by rfl⟩ : syracuseStep 6131099 = 9196649) B9196649
theorem B5099233 : Blo 1342990 5099233 := bstep (se 2 (by rfl) ⟨1912212, by rfl⟩ : syracuseStep 5099233 = 3824425) B3824425
theorem B7270813 : Blo 1342990 7270813 := bstep (se 3 (by rfl) ⟨1363277, by rfl⟩ : syracuseStep 7270813 = 2726555) B2726555
theorem B27579113 : Blo 1342990 27579113 := bstep (se 2 (by rfl) ⟨10342167, by rfl⟩ : syracuseStep 27579113 = 20684335) B20684335
theorem B20697889 : Blo 1342990 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B23278427 : Blo 1342990 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B59693759 : Blo 1342990 59693759 := bstep (se 1 (by rfl) ⟨44770319, by rfl⟩ : syracuseStep 59693759 = 89540639) B89540639
theorem B8609111 : Blo 1342990 8609111 := bstep (se 1 (by rfl) ⟨6456833, by rfl⟩ : syracuseStep 8609111 = 12913667) B12913667
theorem B3022847 : Blo 1342990 3022847 := bstep (se 1 (by rfl) ⟨2267135, by rfl⟩ : syracuseStep 3022847 = 4534271) B4534271
theorem B2015723 : Blo 1342990 2015723 := bstep (se 1 (by rfl) ⟨1511792, by rfl⟩ : syracuseStep 2015723 = 3023585) B3023585
theorem B6800111 : Blo 1342990 6800111 := bstep (se 1 (by rfl) ⟨5100083, by rfl⟩ : syracuseStep 6800111 = 10200167) B10200167
theorem B59753213 : Blo 1342990 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B4539239 : Blo 1342990 4539239 := bstep (se 1 (by rfl) ⟨3404429, by rfl⟩ : syracuseStep 4539239 = 6808859) B6808859
theorem B2016539 : Blo 1342990 2016539 := bstep (se 1 (by rfl) ⟨1512404, by rfl⟩ : syracuseStep 2016539 = 3024809) B3024809
theorem B1344795 : Blo 1342990 1344795 := bstep (se 1 (by rfl) ⟨1008596, by rfl⟩ : syracuseStep 1344795 = 2017193) B2017193
theorem B2017115 : Blo 1342990 2017115 := bstep (se 1 (by rfl) ⟨1512836, by rfl⟩ : syracuseStep 2017115 = 3025673) B3025673
theorem B17460095 : Blo 1342990 17460095 := bstep (se 1 (by rfl) ⟨13095071, by rfl⟩ : syracuseStep 17460095 = 26190143) B26190143
theorem B18386075 : Blo 1342990 18386075 := bstep (se 1 (by rfl) ⟨13789556, by rfl⟩ : syracuseStep 18386075 = 27579113) B27579113
theorem B9694417 : Blo 1342990 9694417 := bstep (se 2 (by rfl) ⟨3635406, by rfl⟩ : syracuseStep 9694417 = 7270813) B7270813
theorem B15518951 : Blo 1342990 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B3878201 : Blo 1342990 3878201 := bstep (se 2 (by rfl) ⟨1454325, by rfl⟩ : syracuseStep 3878201 = 2908651) B2908651
theorem B15314831 : Blo 1342990 15314831 := bstep (se 1 (by rfl) ⟨11486123, by rfl⟩ : syracuseStep 15314831 = 22972247) B22972247
theorem B5739407 : Blo 1342990 5739407 := bstep (se 1 (by rfl) ⟨4304555, by rfl⟩ : syracuseStep 5739407 = 8609111) B8609111
theorem B5100995 : Blo 1342990 5100995 := bstep (se 1 (by rfl) ⟨3825746, by rfl⟩ : syracuseStep 5100995 = 7651493) B7651493
theorem B2015231 : Blo 1342990 2015231 := bstep (se 1 (by rfl) ⟨1511423, by rfl⟩ : syracuseStep 2015231 = 3022847) B3022847
theorem B27597185 : Blo 1342990 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B16349597 : Blo 1342990 16349597 := bstep (se 3 (by rfl) ⟨3065549, by rfl⟩ : syracuseStep 16349597 = 6131099) B6131099
theorem B111917537 : Blo 1342990 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B39795839 : Blo 1342990 39795839 := bstep (se 1 (by rfl) ⟨29846879, by rfl⟩ : syracuseStep 39795839 = 59693759) B59693759
theorem B6798977 : Blo 1342990 6798977 := bstep (se 2 (by rfl) ⟨2549616, by rfl⟩ : syracuseStep 6798977 = 5099233) B5099233
theorem B1343815 : Blo 1342990 1343815 := bstep (se 1 (by rfl) ⟨1007861, by rfl⟩ : syracuseStep 1343815 = 2015723) B2015723
theorem B49029533 : Blo 1342990 49029533 := bstep (se 3 (by rfl) ⟨9193037, by rfl⟩ : syracuseStep 49029533 = 18386075) B18386075
theorem B3826271 : Blo 1342990 3826271 := bstep (se 1 (by rfl) ⟨2869703, by rfl⟩ : syracuseStep 3826271 = 5739407) B5739407
theorem B1344359 : Blo 1342990 1344359 := bstep (se 1 (by rfl) ⟨1008269, by rfl⟩ : syracuseStep 1344359 = 2016539) B2016539
theorem B3400663 : Blo 1342990 3400663 := bstep (se 1 (by rfl) ⟨2550497, by rfl⟩ : syracuseStep 3400663 = 5100995) B5100995
theorem B1343487 : Blo 1342990 1343487 := bstep (se 1 (by rfl) ⟨1007615, by rfl⟩ : syracuseStep 1343487 = 2015231) B2015231
theorem B1344743 : Blo 1342990 1344743 := bstep (se 1 (by rfl) ⟨1008557, by rfl⟩ : syracuseStep 1344743 = 2017115) B2017115
theorem B4532651 : Blo 1342990 4532651 := bstep (se 1 (by rfl) ⟨3399488, by rfl⟩ : syracuseStep 4532651 = 6798977) B6798977
theorem B10209887 : Blo 1342990 10209887 := bstep (se 1 (by rfl) ⟨7657415, by rfl⟩ : syracuseStep 10209887 = 15314831) B15314831
theorem B4533407 : Blo 1342990 4533407 := bstep (se 1 (by rfl) ⟨3400055, by rfl⟩ : syracuseStep 4533407 = 6800111) B6800111
theorem B3026159 : Blo 1342990 3026159 := bstep (se 1 (by rfl) ⟨2269619, by rfl⟩ : syracuseStep 3026159 = 4539239) B4539239
theorem B10899731 : Blo 1342990 10899731 := bstep (se 1 (by rfl) ⟨8174798, by rfl⟩ : syracuseStep 10899731 = 16349597) B16349597
theorem B26530559 : Blo 1342990 26530559 := bstep (se 1 (by rfl) ⟨19897919, by rfl⟩ : syracuseStep 26530559 = 39795839) B39795839
theorem B2585467 : Blo 1342990 2585467 := bstep (se 1 (by rfl) ⟨1939100, by rfl⟩ : syracuseStep 2585467 = 3878201) B3878201
theorem B46560253 : Blo 1342990 46560253 := bstep (se 3 (by rfl) ⟨8730047, by rfl⟩ : syracuseStep 46560253 = 17460095) B17460095
theorem B39835475 : Blo 1342990 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B18398123 : Blo 1342990 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B12925889 : Blo 1342990 12925889 := bstep (se 2 (by rfl) ⟨4847208, by rfl⟩ : syracuseStep 12925889 = 9694417) B9694417
theorem B74611691 : Blo 1342990 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B10345967 : Blo 1342990 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B32686355 : Blo 1342990 32686355 := bstep (se 1 (by rfl) ⟨24514766, by rfl⟩ : syracuseStep 32686355 = 49029533) B49029533
theorem B29065949 : Blo 1342990 29065949 := bstep (se 3 (by rfl) ⟨5449865, by rfl⟩ : syracuseStep 29065949 = 10899731) B10899731
theorem B62080337 : Blo 1342990 62080337 := bstep (se 2 (by rfl) ⟨23280126, by rfl⟩ : syracuseStep 62080337 = 46560253) B46560253
theorem B12265415 : Blo 1342990 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B2017439 : Blo 1342990 2017439 := bstep (se 1 (by rfl) ⟨1513079, by rfl⟩ : syracuseStep 2017439 = 3026159) B3026159
theorem B2550847 : Blo 1342990 2550847 := bstep (se 1 (by rfl) ⟨1913135, by rfl⟩ : syracuseStep 2550847 = 3826271) B3826271
theorem B4534217 : Blo 1342990 4534217 := bstep (se 2 (by rfl) ⟨1700331, by rfl⟩ : syracuseStep 4534217 = 3400663) B3400663
theorem B3447289 : Blo 1342990 3447289 := bstep (se 2 (by rfl) ⟨1292733, by rfl⟩ : syracuseStep 3447289 = 2585467) B2585467
theorem B26556983 : Blo 1342990 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B3021767 : Blo 1342990 3021767 := bstep (se 1 (by rfl) ⟨2266325, by rfl⟩ : syracuseStep 3021767 = 4532651) B4532651
theorem B6806591 : Blo 1342990 6806591 := bstep (se 1 (by rfl) ⟨5104943, by rfl⟩ : syracuseStep 6806591 = 10209887) B10209887
theorem B8617259 : Blo 1342990 8617259 := bstep (se 1 (by rfl) ⟨6462944, by rfl⟩ : syracuseStep 8617259 = 12925889) B12925889
theorem B49741127 : Blo 1342990 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B3022271 : Blo 1342990 3022271 := bstep (se 1 (by rfl) ⟨2266703, by rfl⟩ : syracuseStep 3022271 = 4533407) B4533407
theorem B6897311 : Blo 1342990 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B282992629 : Blo 1342990 282992629 := bstep (se 5 (by rfl) ⟨13265279, by rfl⟩ : syracuseStep 282992629 = 26530559) B26530559
theorem B21790903 : Blo 1342990 21790903 := bstep (se 1 (by rfl) ⟨16343177, by rfl⟩ : syracuseStep 21790903 = 32686355) B32686355
theorem B41386891 : Blo 1342990 41386891 := bstep (se 1 (by rfl) ⟨31040168, by rfl⟩ : syracuseStep 41386891 = 62080337) B62080337
theorem B8176943 : Blo 1342990 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B3401129 : Blo 1342990 3401129 := bstep (se 2 (by rfl) ⟨1275423, by rfl⟩ : syracuseStep 3401129 = 2550847) B2550847
theorem B1344959 : Blo 1342990 1344959 := bstep (se 1 (by rfl) ⟨1008719, by rfl⟩ : syracuseStep 1344959 = 2017439) B2017439
theorem B17704655 : Blo 1342990 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B5744839 : Blo 1342990 5744839 := bstep (se 1 (by rfl) ⟨4308629, by rfl⟩ : syracuseStep 5744839 = 8617259) B8617259
theorem B4598207 : Blo 1342990 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B18385541 : Blo 1342990 18385541 := bstep (se 4 (by rfl) ⟨1723644, by rfl⟩ : syracuseStep 18385541 = 3447289) B3447289
theorem B19377299 : Blo 1342990 19377299 := bstep (se 1 (by rfl) ⟨14532974, by rfl⟩ : syracuseStep 19377299 = 29065949) B29065949
theorem B2014511 : Blo 1342990 2014511 := bstep (se 1 (by rfl) ⟨1510883, by rfl⟩ : syracuseStep 2014511 = 3021767) B3021767
theorem B4537727 : Blo 1342990 4537727 := bstep (se 1 (by rfl) ⟨3403295, by rfl⟩ : syracuseStep 4537727 = 6806591) B6806591
theorem B33160751 : Blo 1342990 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B2014847 : Blo 1342990 2014847 := bstep (se 1 (by rfl) ⟨1511135, by rfl⟩ : syracuseStep 2014847 = 3022271) B3022271
theorem B3022811 : Blo 1342990 3022811 := bstep (se 1 (by rfl) ⟨2267108, by rfl⟩ : syracuseStep 3022811 = 4534217) B4534217
theorem B377323505 : Blo 1342990 377323505 := bstep (se 2 (by rfl) ⟨141496314, by rfl⟩ : syracuseStep 377323505 = 282992629) B282992629
theorem B7659785 : Blo 1342990 7659785 := bstep (se 2 (by rfl) ⟨2872419, by rfl⟩ : syracuseStep 7659785 = 5744839) B5744839
theorem B55182521 : Blo 1342990 55182521 := bstep (se 2 (by rfl) ⟨20693445, by rfl⟩ : syracuseStep 55182521 = 41386891) B41386891
theorem B3065471 : Blo 1342990 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B12257027 : Blo 1342990 12257027 := bstep (se 1 (by rfl) ⟨9192770, by rfl⟩ : syracuseStep 12257027 = 18385541) B18385541
theorem B3025151 : Blo 1342990 3025151 := bstep (se 1 (by rfl) ⟨2268863, by rfl⟩ : syracuseStep 3025151 = 4537727) B4537727
theorem B5451295 : Blo 1342990 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B22107167 : Blo 1342990 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B251549003 : Blo 1342990 251549003 := bstep (se 1 (by rfl) ⟨188661752, by rfl⟩ : syracuseStep 251549003 = 377323505) B377323505
theorem B29054537 : Blo 1342990 29054537 := bstep (se 2 (by rfl) ⟨10895451, by rfl⟩ : syracuseStep 29054537 = 21790903) B21790903
theorem B2267419 : Blo 1342990 2267419 := bstep (se 1 (by rfl) ⟨1700564, by rfl⟩ : syracuseStep 2267419 = 3401129) B3401129
theorem B11803103 : Blo 1342990 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B12918199 : Blo 1342990 12918199 := bstep (se 1 (by rfl) ⟨9688649, by rfl⟩ : syracuseStep 12918199 = 19377299) B19377299
theorem B1343007 : Blo 1342990 1343007 := bstep (se 1 (by rfl) ⟨1007255, by rfl⟩ : syracuseStep 1343007 = 2014511) B2014511
theorem B1343231 : Blo 1342990 1343231 := bstep (se 1 (by rfl) ⟨1007423, by rfl⟩ : syracuseStep 1343231 = 2014847) B2014847
theorem B2015207 : Blo 1342990 2015207 := bstep (se 1 (by rfl) ⟨1511405, by rfl⟩ : syracuseStep 2015207 = 3022811) B3022811
theorem B3023225 : Blo 1342990 3023225 := bstep (se 2 (by rfl) ⟨1133709, by rfl⟩ : syracuseStep 3023225 = 2267419) B2267419
theorem B14738111 : Blo 1342990 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B167699335 : Blo 1342990 167699335 := bstep (se 1 (by rfl) ⟨125774501, by rfl⟩ : syracuseStep 167699335 = 251549003) B251549003
theorem B2016767 : Blo 1342990 2016767 := bstep (se 1 (by rfl) ⟨1512575, by rfl⟩ : syracuseStep 2016767 = 3025151) B3025151
theorem B7268393 : Blo 1342990 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B5106523 : Blo 1342990 5106523 := bstep (se 1 (by rfl) ⟨3829892, by rfl⟩ : syracuseStep 5106523 = 7659785) B7659785
theorem B19369691 : Blo 1342990 19369691 := bstep (se 1 (by rfl) ⟨14527268, by rfl⟩ : syracuseStep 19369691 = 29054537) B29054537
theorem B2043647 : Blo 1342990 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B8171351 : Blo 1342990 8171351 := bstep (se 1 (by rfl) ⟨6128513, by rfl⟩ : syracuseStep 8171351 = 12257027) B12257027
theorem B7868735 : Blo 1342990 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B17224265 : Blo 1342990 17224265 := bstep (se 2 (by rfl) ⟨6459099, by rfl⟩ : syracuseStep 17224265 = 12918199) B12918199
theorem B36788347 : Blo 1342990 36788347 := bstep (se 1 (by rfl) ⟨27591260, by rfl⟩ : syracuseStep 36788347 = 55182521) B55182521
theorem B1343471 : Blo 1342990 1343471 := bstep (se 1 (by rfl) ⟨1007603, by rfl⟩ : syracuseStep 1343471 = 2015207) B2015207
theorem B2015483 : Blo 1342990 2015483 := bstep (se 1 (by rfl) ⟨1511612, by rfl⟩ : syracuseStep 2015483 = 3023225) B3023225
theorem B1344511 : Blo 1342990 1344511 := bstep (se 1 (by rfl) ⟨1008383, by rfl⟩ : syracuseStep 1344511 = 2016767) B2016767
theorem B6808697 : Blo 1342990 6808697 := bstep (se 2 (by rfl) ⟨2553261, by rfl⟩ : syracuseStep 6808697 = 5106523) B5106523
theorem B12913127 : Blo 1342990 12913127 := bstep (se 1 (by rfl) ⟨9684845, by rfl⟩ : syracuseStep 12913127 = 19369691) B19369691
theorem B1362431 : Blo 1342990 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B5245823 : Blo 1342990 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B9825407 : Blo 1342990 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B4845595 : Blo 1342990 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B49051129 : Blo 1342990 49051129 := bstep (se 2 (by rfl) ⟨18394173, by rfl⟩ : syracuseStep 49051129 = 36788347) B36788347
theorem B11482843 : Blo 1342990 11482843 := bstep (se 1 (by rfl) ⟨8612132, by rfl⟩ : syracuseStep 11482843 = 17224265) B17224265
theorem B223599113 : Blo 1342990 223599113 := bstep (se 2 (by rfl) ⟨83849667, by rfl⟩ : syracuseStep 223599113 = 167699335) B167699335
theorem B5447567 : Blo 1342990 5447567 := bstep (se 1 (by rfl) ⟨4085675, by rfl⟩ : syracuseStep 5447567 = 8171351) B8171351
theorem B1343655 : Blo 1342990 1343655 := bstep (se 1 (by rfl) ⟨1007741, by rfl⟩ : syracuseStep 1343655 = 2015483) B2015483
theorem B4539131 : Blo 1342990 4539131 := bstep (se 1 (by rfl) ⟨3404348, by rfl⟩ : syracuseStep 4539131 = 6808697) B6808697
theorem B3631711 : Blo 1342990 3631711 := bstep (se 1 (by rfl) ⟨2723783, by rfl⟩ : syracuseStep 3631711 = 5447567) B5447567
theorem B3633149 : Blo 1342990 3633149 := bstep (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) B1362431
theorem B149066075 : Blo 1342990 149066075 := bstep (se 1 (by rfl) ⟨111799556, by rfl⟩ : syracuseStep 149066075 = 223599113) B223599113
theorem B65401505 : Blo 1342990 65401505 := bstep (se 2 (by rfl) ⟨24525564, by rfl⟩ : syracuseStep 65401505 = 49051129) B49051129
theorem B6550271 : Blo 1342990 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B6460793 : Blo 1342990 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B8608751 : Blo 1342990 8608751 := bstep (se 1 (by rfl) ⟨6456563, by rfl⟩ : syracuseStep 8608751 = 12913127) B12913127
theorem B3497215 : Blo 1342990 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B15310457 : Blo 1342990 15310457 := bstep (se 2 (by rfl) ⟨5741421, by rfl⟩ : syracuseStep 15310457 = 11482843) B11482843
theorem B99377383 : Blo 1342990 99377383 := bstep (se 1 (by rfl) ⟨74533037, by rfl⟩ : syracuseStep 99377383 = 149066075) B149066075
theorem B4366847 : Blo 1342990 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B4842281 : Blo 1342990 4842281 := bstep (se 2 (by rfl) ⟨1815855, by rfl⟩ : syracuseStep 4842281 = 3631711) B3631711
theorem B4662953 : Blo 1342990 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B43601003 : Blo 1342990 43601003 := bstep (se 1 (by rfl) ⟨32700752, by rfl⟩ : syracuseStep 43601003 = 65401505) B65401505
theorem B3026087 : Blo 1342990 3026087 := bstep (se 1 (by rfl) ⟨2269565, by rfl⟩ : syracuseStep 3026087 = 4539131) B4539131
theorem B5739167 : Blo 1342990 5739167 := bstep (se 1 (by rfl) ⟨4304375, by rfl⟩ : syracuseStep 5739167 = 8608751) B8608751
theorem B2422099 : Blo 1342990 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B4307195 : Blo 1342990 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B10206971 : Blo 1342990 10206971 := bstep (se 1 (by rfl) ⟨7655228, by rfl⟩ : syracuseStep 10206971 = 15310457) B15310457
theorem B3826111 : Blo 1342990 3826111 := bstep (se 1 (by rfl) ⟨2869583, by rfl⟩ : syracuseStep 3826111 = 5739167) B5739167
theorem B3228187 : Blo 1342990 3228187 := bstep (se 1 (by rfl) ⟨2421140, by rfl⟩ : syracuseStep 3228187 = 4842281) B4842281
theorem B3229465 : Blo 1342990 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B29067335 : Blo 1342990 29067335 := bstep (se 1 (by rfl) ⟨21800501, by rfl⟩ : syracuseStep 29067335 = 43601003) B43601003
theorem B2017391 : Blo 1342990 2017391 := bstep (se 1 (by rfl) ⟨1513043, by rfl⟩ : syracuseStep 2017391 = 3026087) B3026087
theorem B2911231 : Blo 1342990 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B3108635 : Blo 1342990 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2871463 : Blo 1342990 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B6804647 : Blo 1342990 6804647 := bstep (se 1 (by rfl) ⟨5103485, by rfl⟩ : syracuseStep 6804647 = 10206971) B10206971
theorem B132503177 : Blo 1342990 132503177 := bstep (se 2 (by rfl) ⟨49688691, by rfl⟩ : syracuseStep 132503177 = 99377383) B99377383
theorem B88335451 : Blo 1342990 88335451 := bstep (se 1 (by rfl) ⟨66251588, by rfl⟩ : syracuseStep 88335451 = 132503177) B132503177
theorem B1344927 : Blo 1342990 1344927 := bstep (se 1 (by rfl) ⟨1008695, by rfl⟩ : syracuseStep 1344927 = 2017391) B2017391
theorem B3828617 : Blo 1342990 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B4304249 : Blo 1342990 4304249 := bstep (se 2 (by rfl) ⟨1614093, by rfl⟩ : syracuseStep 4304249 = 3228187) B3228187
theorem B19378223 : Blo 1342990 19378223 := bstep (se 1 (by rfl) ⟨14533667, by rfl⟩ : syracuseStep 19378223 = 29067335) B29067335
theorem B4305953 : Blo 1342990 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B5101481 : Blo 1342990 5101481 := bstep (se 2 (by rfl) ⟨1913055, by rfl⟩ : syracuseStep 5101481 = 3826111) B3826111
theorem B4536431 : Blo 1342990 4536431 := bstep (se 1 (by rfl) ⟨3402323, by rfl⟩ : syracuseStep 4536431 = 6804647) B6804647
theorem B3881641 : Blo 1342990 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B2072423 : Blo 1342990 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B12918815 : Blo 1342990 12918815 := bstep (se 1 (by rfl) ⟨9689111, by rfl⟩ : syracuseStep 12918815 = 19378223) B19378223
theorem B3400987 : Blo 1342990 3400987 := bstep (se 1 (by rfl) ⟨2550740, by rfl⟩ : syracuseStep 3400987 = 5101481) B5101481
theorem B3024287 : Blo 1342990 3024287 := bstep (se 1 (by rfl) ⟨2268215, by rfl⟩ : syracuseStep 3024287 = 4536431) B4536431
theorem B2869499 : Blo 1342990 2869499 := bstep (se 1 (by rfl) ⟨2152124, by rfl⟩ : syracuseStep 2869499 = 4304249) B4304249
theorem B2870635 : Blo 1342990 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B117780601 : Blo 1342990 117780601 := bstep (se 2 (by rfl) ⟨44167725, by rfl⟩ : syracuseStep 117780601 = 88335451) B88335451
theorem B2552411 : Blo 1342990 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B5526461 : Blo 1342990 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B5175521 : Blo 1342990 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B157040801 : Blo 1342990 157040801 := bstep (se 2 (by rfl) ⟨58890300, by rfl⟩ : syracuseStep 157040801 = 117780601) B117780601
theorem B2016191 : Blo 1342990 2016191 := bstep (se 1 (by rfl) ⟨1512143, by rfl⟩ : syracuseStep 2016191 = 3024287) B3024287
theorem B3450347 : Blo 1342990 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B3827513 : Blo 1342990 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B8612543 : Blo 1342990 8612543 := bstep (se 1 (by rfl) ⟨6459407, by rfl⟩ : syracuseStep 8612543 = 12918815) B12918815
theorem B1912999 : Blo 1342990 1912999 := bstep (se 1 (by rfl) ⟨1434749, by rfl⟩ : syracuseStep 1912999 = 2869499) B2869499
theorem B4534649 : Blo 1342990 4534649 := bstep (se 2 (by rfl) ⟨1700493, by rfl⟩ : syracuseStep 4534649 = 3400987) B3400987
theorem B3684307 : Blo 1342990 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B6806429 : Blo 1342990 6806429 := bstep (se 3 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 6806429 = 2552411) B2552411
theorem B104693867 : Blo 1342990 104693867 := bstep (se 1 (by rfl) ⟨78520400, by rfl⟩ : syracuseStep 104693867 = 157040801) B157040801
theorem B3023099 : Blo 1342990 3023099 := bstep (se 1 (by rfl) ⟨2267324, by rfl⟩ : syracuseStep 3023099 = 4534649) B4534649
theorem B1344127 : Blo 1342990 1344127 := bstep (se 1 (by rfl) ⟨1008095, by rfl⟩ : syracuseStep 1344127 = 2016191) B2016191
theorem B2550665 : Blo 1342990 2550665 := bstep (se 2 (by rfl) ⟨956499, by rfl⟩ : syracuseStep 2550665 = 1912999) B1912999
theorem B2551675 : Blo 1342990 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B4912409 : Blo 1342990 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B2300231 : Blo 1342990 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B5741695 : Blo 1342990 5741695 := bstep (se 1 (by rfl) ⟨4306271, by rfl⟩ : syracuseStep 5741695 = 8612543) B8612543
theorem B4537619 : Blo 1342990 4537619 := bstep (se 1 (by rfl) ⟨3403214, by rfl⟩ : syracuseStep 4537619 = 6806429) B6806429
theorem B69795911 : Blo 1342990 69795911 := bstep (se 1 (by rfl) ⟨52346933, by rfl⟩ : syracuseStep 69795911 = 104693867) B104693867
theorem B2015399 : Blo 1342990 2015399 := bstep (se 1 (by rfl) ⟨1511549, by rfl⟩ : syracuseStep 2015399 = 3023099) B3023099
theorem B1533487 : Blo 1342990 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B3025079 : Blo 1342990 3025079 := bstep (se 1 (by rfl) ⟨2268809, by rfl⟩ : syracuseStep 3025079 = 4537619) B4537619
theorem B3402233 : Blo 1342990 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B7655593 : Blo 1342990 7655593 := bstep (se 2 (by rfl) ⟨2870847, by rfl⟩ : syracuseStep 7655593 = 5741695) B5741695
theorem B1700443 : Blo 1342990 1700443 := bstep (se 1 (by rfl) ⟨1275332, by rfl⟩ : syracuseStep 1700443 = 2550665) B2550665
theorem B3274939 : Blo 1342990 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B46530607 : Blo 1342990 46530607 := bstep (se 1 (by rfl) ⟨34897955, by rfl⟩ : syracuseStep 46530607 = 69795911) B69795911
theorem B1343599 : Blo 1342990 1343599 := bstep (se 1 (by rfl) ⟨1007699, by rfl⟩ : syracuseStep 1343599 = 2015399) B2015399
theorem B10207457 : Blo 1342990 10207457 := bstep (se 2 (by rfl) ⟨3827796, by rfl⟩ : syracuseStep 10207457 = 7655593) B7655593
theorem B4366585 : Blo 1342990 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B2016719 : Blo 1342990 2016719 := bstep (se 1 (by rfl) ⟨1512539, by rfl⟩ : syracuseStep 2016719 = 3025079) B3025079
theorem B2044649 : Blo 1342990 2044649 := bstep (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) B1533487
theorem B2267257 : Blo 1342990 2267257 := bstep (se 2 (by rfl) ⟨850221, by rfl⟩ : syracuseStep 2267257 = 1700443) B1700443
theorem B2268155 : Blo 1342990 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B3023009 : Blo 1342990 3023009 := bstep (se 2 (by rfl) ⟨1133628, by rfl⟩ : syracuseStep 3023009 = 2267257) B2267257
theorem B1344479 : Blo 1342990 1344479 := bstep (se 1 (by rfl) ⟨1008359, by rfl⟩ : syracuseStep 1344479 = 2016719) B2016719
theorem B62040809 : Blo 1342990 62040809 := bstep (se 2 (by rfl) ⟨23265303, by rfl⟩ : syracuseStep 62040809 = 46530607) B46530607
theorem B1363099 : Blo 1342990 1363099 := bstep (se 1 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 1363099 = 2044649) B2044649
theorem B1512103 : Blo 1342990 1512103 := bstep (se 1 (by rfl) ⟨1134077, by rfl⟩ : syracuseStep 1512103 = 2268155) B2268155
theorem B6804971 : Blo 1342990 6804971 := bstep (se 1 (by rfl) ⟨5103728, by rfl⟩ : syracuseStep 6804971 = 10207457) B10207457
theorem B5822113 : Blo 1342990 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B2015339 : Blo 1342990 2015339 := bstep (se 1 (by rfl) ⟨1511504, by rfl⟩ : syracuseStep 2015339 = 3023009) B3023009
theorem B2016137 : Blo 1342990 2016137 := bstep (se 2 (by rfl) ⟨756051, by rfl⟩ : syracuseStep 2016137 = 1512103) B1512103
theorem B7762817 : Blo 1342990 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B29079445 : Blo 1342990 29079445 := bstep (se 6 (by rfl) ⟨681549, by rfl⟩ : syracuseStep 29079445 = 1363099) B1363099
theorem B4536647 : Blo 1342990 4536647 := bstep (se 1 (by rfl) ⟨3402485, by rfl⟩ : syracuseStep 4536647 = 6804971) B6804971
theorem B41360539 : Blo 1342990 41360539 := bstep (se 1 (by rfl) ⟨31020404, by rfl⟩ : syracuseStep 41360539 = 62040809) B62040809
theorem B1343559 : Blo 1342990 1343559 := bstep (se 1 (by rfl) ⟨1007669, by rfl⟩ : syracuseStep 1343559 = 2015339) B2015339
theorem B1344091 : Blo 1342990 1344091 := bstep (se 1 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 1344091 = 2016137) B2016137
theorem B3024431 : Blo 1342990 3024431 := bstep (se 1 (by rfl) ⟨2268323, by rfl⟩ : syracuseStep 3024431 = 4536647) B4536647
theorem B55147385 : Blo 1342990 55147385 := bstep (se 2 (by rfl) ⟨20680269, by rfl⟩ : syracuseStep 55147385 = 41360539) B41360539
theorem B20700845 : Blo 1342990 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B38772593 : Blo 1342990 38772593 := bstep (se 2 (by rfl) ⟨14539722, by rfl⟩ : syracuseStep 38772593 = 29079445) B29079445
theorem B2016287 : Blo 1342990 2016287 := bstep (se 1 (by rfl) ⟨1512215, by rfl⟩ : syracuseStep 2016287 = 3024431) B3024431
theorem B25848395 : Blo 1342990 25848395 := bstep (se 1 (by rfl) ⟨19386296, by rfl⟩ : syracuseStep 25848395 = 38772593) B38772593
theorem B13800563 : Blo 1342990 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B36764923 : Blo 1342990 36764923 := bstep (se 1 (by rfl) ⟨27573692, by rfl⟩ : syracuseStep 36764923 = 55147385) B55147385
theorem B1344191 : Blo 1342990 1344191 := bstep (se 1 (by rfl) ⟨1008143, by rfl⟩ : syracuseStep 1344191 = 2016287) B2016287
theorem B9200375 : Blo 1342990 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B17232263 : Blo 1342990 17232263 := bstep (se 1 (by rfl) ⟨12924197, by rfl⟩ : syracuseStep 17232263 = 25848395) B25848395
theorem B49019897 : Blo 1342990 49019897 := bstep (se 2 (by rfl) ⟨18382461, by rfl⟩ : syracuseStep 49019897 = 36764923) B36764923
theorem B32679931 : Blo 1342990 32679931 := bstep (se 1 (by rfl) ⟨24509948, by rfl⟩ : syracuseStep 32679931 = 49019897) B49019897
theorem B11488175 : Blo 1342990 11488175 := bstep (se 1 (by rfl) ⟨8616131, by rfl⟩ : syracuseStep 11488175 = 17232263) B17232263
theorem B6133583 : Blo 1342990 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B4089055 : Blo 1342990 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B43573241 : Blo 1342990 43573241 := bstep (se 2 (by rfl) ⟨16339965, by rfl⟩ : syracuseStep 43573241 = 32679931) B32679931
theorem B7658783 : Blo 1342990 7658783 := bstep (se 1 (by rfl) ⟨5744087, by rfl⟩ : syracuseStep 7658783 = 11488175) B11488175
theorem B5105855 : Blo 1342990 5105855 := bstep (se 1 (by rfl) ⟨3829391, by rfl⟩ : syracuseStep 5105855 = 7658783) B7658783
theorem B5452073 : Blo 1342990 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B29048827 : Blo 1342990 29048827 := bstep (se 1 (by rfl) ⟨21786620, by rfl⟩ : syracuseStep 29048827 = 43573241) B43573241
theorem B3403903 : Blo 1342990 3403903 := bstep (se 1 (by rfl) ⟨2552927, by rfl⟩ : syracuseStep 3403903 = 5105855) B5105855
theorem B3634715 : Blo 1342990 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B38731769 : Blo 1342990 38731769 := bstep (se 2 (by rfl) ⟨14524413, by rfl⟩ : syracuseStep 38731769 = 29048827) B29048827
theorem B4538537 : Blo 1342990 4538537 := bstep (se 2 (by rfl) ⟨1701951, by rfl⟩ : syracuseStep 4538537 = 3403903) B3403903
theorem B25821179 : Blo 1342990 25821179 := bstep (se 1 (by rfl) ⟨19365884, by rfl⟩ : syracuseStep 25821179 = 38731769) B38731769
theorem B2423143 : Blo 1342990 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B17214119 : Blo 1342990 17214119 := bstep (se 1 (by rfl) ⟨12910589, by rfl⟩ : syracuseStep 17214119 = 25821179) B25821179
theorem B3025691 : Blo 1342990 3025691 := bstep (se 1 (by rfl) ⟨2269268, by rfl⟩ : syracuseStep 3025691 = 4538537) B4538537
theorem B3230857 : Blo 1342990 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B2017127 : Blo 1342990 2017127 := bstep (se 1 (by rfl) ⟨1512845, by rfl⟩ : syracuseStep 2017127 = 3025691) B3025691
theorem B17231237 : Blo 1342990 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B11476079 : Blo 1342990 11476079 := bstep (se 1 (by rfl) ⟨8607059, by rfl⟩ : syracuseStep 11476079 = 17214119) B17214119
theorem B1344751 : Blo 1342990 1344751 := bstep (se 1 (by rfl) ⟨1008563, by rfl⟩ : syracuseStep 1344751 = 2017127) B2017127
theorem B11487491 : Blo 1342990 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B7650719 : Blo 1342990 7650719 := bstep (se 1 (by rfl) ⟨5738039, by rfl⟩ : syracuseStep 7650719 = 11476079) B11476079
theorem B5100479 : Blo 1342990 5100479 := bstep (se 1 (by rfl) ⟨3825359, by rfl⟩ : syracuseStep 5100479 = 7650719) B7650719
theorem B7658327 : Blo 1342990 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B3400319 : Blo 1342990 3400319 := bstep (se 1 (by rfl) ⟨2550239, by rfl⟩ : syracuseStep 3400319 = 5100479) B5100479
theorem B5105551 : Blo 1342990 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B2266879 : Blo 1342990 2266879 := bstep (se 1 (by rfl) ⟨1700159, by rfl⟩ : syracuseStep 2266879 = 3400319) B3400319
theorem B6807401 : Blo 1342990 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B3022505 : Blo 1342990 3022505 := bstep (se 2 (by rfl) ⟨1133439, by rfl⟩ : syracuseStep 3022505 = 2266879) B2266879
theorem B4538267 : Blo 1342990 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B3025511 : Blo 1342990 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B2015003 : Blo 1342990 2015003 := bstep (se 1 (by rfl) ⟨1511252, by rfl⟩ : syracuseStep 2015003 = 3022505) B3022505
theorem B2017007 : Blo 1342990 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B1343335 : Blo 1342990 1343335 := bstep (se 1 (by rfl) ⟨1007501, by rfl⟩ : syracuseStep 1343335 = 2015003) B2015003
theorem B1344671 : Blo 1342990 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007

theorem C0 (j : ℕ) (h1 : 335747 ≤ j) (h2 : j ≤ 336246) : Blo 1342990 (4 * j + 3) := by
  interval_cases j
  · exact B1342991
  · exact B1342995
  · exact B1342999
  · exact B1343003
  · exact B1343007
  · exact B1343011
  · exact B1343015
  · exact B1343019
  · exact B1343023
  · exact B1343027
  · exact B1343031
  · exact B1343035
  · exact B1343039
  · exact B1343043
  · exact B1343047
  · exact B1343051
  · exact B1343055
  · exact B1343059
  · exact B1343063
  · exact B1343067
  · exact B1343071
  · exact B1343075
  · exact B1343079
  · exact B1343083
  · exact B1343087
  · exact B1343091
  · exact B1343095
  · exact B1343099
  · exact B1343103
  · exact B1343107
  · exact B1343111
  · exact B1343115
  · exact B1343119
  · exact B1343123
  · exact B1343127
  · exact B1343131
  · exact B1343135
  · exact B1343139
  · exact B1343143
  · exact B1343147
  · exact B1343151
  · exact B1343155
  · exact B1343159
  · exact B1343163
  · exact B1343167
  · exact B1343171
  · exact B1343175
  · exact B1343179
  · exact B1343183
  · exact B1343187
  · exact B1343191
  · exact B1343195
  · exact B1343199
  · exact B1343203
  · exact B1343207
  · exact B1343211
  · exact B1343215
  · exact B1343219
  · exact B1343223
  · exact B1343227
  · exact B1343231
  · exact B1343235
  · exact B1343239
  · exact B1343243
  · exact B1343247
  · exact B1343251
  · exact B1343255
  · exact B1343259
  · exact B1343263
  · exact B1343267
  · exact B1343271
  · exact B1343275
  · exact B1343279
  · exact B1343283
  · exact B1343287
  · exact B1343291
  · exact B1343295
  · exact B1343299
  · exact B1343303
  · exact B1343307
  · exact B1343311
  · exact B1343315
  · exact B1343319
  · exact B1343323
  · exact B1343327
  · exact B1343331
  · exact B1343335
  · exact B1343339
  · exact B1343343
  · exact B1343347
  · exact B1343351
  · exact B1343355
  · exact B1343359
  · exact B1343363
  · exact B1343367
  · exact B1343371
  · exact B1343375
  · exact B1343379
  · exact B1343383
  · exact B1343387
  · exact B1343391
  · exact B1343395
  · exact B1343399
  · exact B1343403
  · exact B1343407
  · exact B1343411
  · exact B1343415
  · exact B1343419
  · exact B1343423
  · exact B1343427
  · exact B1343431
  · exact B1343435
  · exact B1343439
  · exact B1343443
  · exact B1343447
  · exact B1343451
  · exact B1343455
  · exact B1343459
  · exact B1343463
  · exact B1343467
  · exact B1343471
  · exact B1343475
  · exact B1343479
  · exact B1343483
  · exact B1343487
  · exact B1343491
  · exact B1343495
  · exact B1343499
  · exact B1343503
  · exact B1343507
  · exact B1343511
  · exact B1343515
  · exact B1343519
  · exact B1343523
  · exact B1343527
  · exact B1343531
  · exact B1343535
  · exact B1343539
  · exact B1343543
  · exact B1343547
  · exact B1343551
  · exact B1343555
  · exact B1343559
  · exact B1343563
  · exact B1343567
  · exact B1343571
  · exact B1343575
  · exact B1343579
  · exact B1343583
  · exact B1343587
  · exact B1343591
  · exact B1343595
  · exact B1343599
  · exact B1343603
  · exact B1343607
  · exact B1343611
  · exact B1343615
  · exact B1343619
  · exact B1343623
  · exact B1343627
  · exact B1343631
  · exact B1343635
  · exact B1343639
  · exact B1343643
  · exact B1343647
  · exact B1343651
  · exact B1343655
  · exact B1343659
  · exact B1343663
  · exact B1343667
  · exact B1343671
  · exact B1343675
  · exact B1343679
  · exact B1343683
  · exact B1343687
  · exact B1343691
  · exact B1343695
  · exact B1343699
  · exact B1343703
  · exact B1343707
  · exact B1343711
  · exact B1343715
  · exact B1343719
  · exact B1343723
  · exact B1343727
  · exact B1343731
  · exact B1343735
  · exact B1343739
  · exact B1343743
  · exact B1343747
  · exact B1343751
  · exact B1343755
  · exact B1343759
  · exact B1343763
  · exact B1343767
  · exact B1343771
  · exact B1343775
  · exact B1343779
  · exact B1343783
  · exact B1343787
  · exact B1343791
  · exact B1343795
  · exact B1343799
  · exact B1343803
  · exact B1343807
  · exact B1343811
  · exact B1343815
  · exact B1343819
  · exact B1343823
  · exact B1343827
  · exact B1343831
  · exact B1343835
  · exact B1343839
  · exact B1343843
  · exact B1343847
  · exact B1343851
  · exact B1343855
  · exact B1343859
  · exact B1343863
  · exact B1343867
  · exact B1343871
  · exact B1343875
  · exact B1343879
  · exact B1343883
  · exact B1343887
  · exact B1343891
  · exact B1343895
  · exact B1343899
  · exact B1343903
  · exact B1343907
  · exact B1343911
  · exact B1343915
  · exact B1343919
  · exact B1343923
  · exact B1343927
  · exact B1343931
  · exact B1343935
  · exact B1343939
  · exact B1343943
  · exact B1343947
  · exact B1343951
  · exact B1343955
  · exact B1343959
  · exact B1343963
  · exact B1343967
  · exact B1343971
  · exact B1343975
  · exact B1343979
  · exact B1343983
  · exact B1343987
  · exact B1343991
  · exact B1343995
  · exact B1343999
  · exact B1344003
  · exact B1344007
  · exact B1344011
  · exact B1344015
  · exact B1344019
  · exact B1344023
  · exact B1344027
  · exact B1344031
  · exact B1344035
  · exact B1344039
  · exact B1344043
  · exact B1344047
  · exact B1344051
  · exact B1344055
  · exact B1344059
  · exact B1344063
  · exact B1344067
  · exact B1344071
  · exact B1344075
  · exact B1344079
  · exact B1344083
  · exact B1344087
  · exact B1344091
  · exact B1344095
  · exact B1344099
  · exact B1344103
  · exact B1344107
  · exact B1344111
  · exact B1344115
  · exact B1344119
  · exact B1344123
  · exact B1344127
  · exact B1344131
  · exact B1344135
  · exact B1344139
  · exact B1344143
  · exact B1344147
  · exact B1344151
  · exact B1344155
  · exact B1344159
  · exact B1344163
  · exact B1344167
  · exact B1344171
  · exact B1344175
  · exact B1344179
  · exact B1344183
  · exact B1344187
  · exact B1344191
  · exact B1344195
  · exact B1344199
  · exact B1344203
  · exact B1344207
  · exact B1344211
  · exact B1344215
  · exact B1344219
  · exact B1344223
  · exact B1344227
  · exact B1344231
  · exact B1344235
  · exact B1344239
  · exact B1344243
  · exact B1344247
  · exact B1344251
  · exact B1344255
  · exact B1344259
  · exact B1344263
  · exact B1344267
  · exact B1344271
  · exact B1344275
  · exact B1344279
  · exact B1344283
  · exact B1344287
  · exact B1344291
  · exact B1344295
  · exact B1344299
  · exact B1344303
  · exact B1344307
  · exact B1344311
  · exact B1344315
  · exact B1344319
  · exact B1344323
  · exact B1344327
  · exact B1344331
  · exact B1344335
  · exact B1344339
  · exact B1344343
  · exact B1344347
  · exact B1344351
  · exact B1344355
  · exact B1344359
  · exact B1344363
  · exact B1344367
  · exact B1344371
  · exact B1344375
  · exact B1344379
  · exact B1344383
  · exact B1344387
  · exact B1344391
  · exact B1344395
  · exact B1344399
  · exact B1344403
  · exact B1344407
  · exact B1344411
  · exact B1344415
  · exact B1344419
  · exact B1344423
  · exact B1344427
  · exact B1344431
  · exact B1344435
  · exact B1344439
  · exact B1344443
  · exact B1344447
  · exact B1344451
  · exact B1344455
  · exact B1344459
  · exact B1344463
  · exact B1344467
  · exact B1344471
  · exact B1344475
  · exact B1344479
  · exact B1344483
  · exact B1344487
  · exact B1344491
  · exact B1344495
  · exact B1344499
  · exact B1344503
  · exact B1344507
  · exact B1344511
  · exact B1344515
  · exact B1344519
  · exact B1344523
  · exact B1344527
  · exact B1344531
  · exact B1344535
  · exact B1344539
  · exact B1344543
  · exact B1344547
  · exact B1344551
  · exact B1344555
  · exact B1344559
  · exact B1344563
  · exact B1344567
  · exact B1344571
  · exact B1344575
  · exact B1344579
  · exact B1344583
  · exact B1344587
  · exact B1344591
  · exact B1344595
  · exact B1344599
  · exact B1344603
  · exact B1344607
  · exact B1344611
  · exact B1344615
  · exact B1344619
  · exact B1344623
  · exact B1344627
  · exact B1344631
  · exact B1344635
  · exact B1344639
  · exact B1344643
  · exact B1344647
  · exact B1344651
  · exact B1344655
  · exact B1344659
  · exact B1344663
  · exact B1344667
  · exact B1344671
  · exact B1344675
  · exact B1344679
  · exact B1344683
  · exact B1344687
  · exact B1344691
  · exact B1344695
  · exact B1344699
  · exact B1344703
  · exact B1344707
  · exact B1344711
  · exact B1344715
  · exact B1344719
  · exact B1344723
  · exact B1344727
  · exact B1344731
  · exact B1344735
  · exact B1344739
  · exact B1344743
  · exact B1344747
  · exact B1344751
  · exact B1344755
  · exact B1344759
  · exact B1344763
  · exact B1344767
  · exact B1344771
  · exact B1344775
  · exact B1344779
  · exact B1344783
  · exact B1344787
  · exact B1344791
  · exact B1344795
  · exact B1344799
  · exact B1344803
  · exact B1344807
  · exact B1344811
  · exact B1344815
  · exact B1344819
  · exact B1344823
  · exact B1344827
  · exact B1344831
  · exact B1344835
  · exact B1344839
  · exact B1344843
  · exact B1344847
  · exact B1344851
  · exact B1344855
  · exact B1344859
  · exact B1344863
  · exact B1344867
  · exact B1344871
  · exact B1344875
  · exact B1344879
  · exact B1344883
  · exact B1344887
  · exact B1344891
  · exact B1344895
  · exact B1344899
  · exact B1344903
  · exact B1344907
  · exact B1344911
  · exact B1344915
  · exact B1344919
  · exact B1344923
  · exact B1344927
  · exact B1344931
  · exact B1344935
  · exact B1344939
  · exact B1344943
  · exact B1344947
  · exact B1344951
  · exact B1344955
  · exact B1344959
  · exact B1344963
  · exact B1344967
  · exact B1344971
  · exact B1344975
  · exact B1344979
  · exact B1344983
  · exact B1344987

theorem solution (m : ℕ) (hlo : 1342990 ≤ m) (hhi : m ≤ 1344990) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 335747 ≤ j := by omega
    have hj2 : j ≤ 336246 := by omega
    have hb : Blo 1342990 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
