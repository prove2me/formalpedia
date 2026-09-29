-- Prove2me | solution 1 for syracuse_descends_range_315835_319835
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:23.727931+00:00
-- url     : https://prove2.me/submissions/b613da5b-57b3-4430-b0ab-ffc9bd475844

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


theorem B983125 : Blo 315835 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B1212677 : Blo 315835 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B328033 : Blo 315835 328033 := bbase (se 2 (by rfl) ⟨123012, by rfl⟩ : syracuseStep 328033 = 246025) (by norm_num)
theorem B819733 : Blo 315835 819733 := bbase (se 6 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 819733 = 38425) (by norm_num)
theorem B1212965 : Blo 315835 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B361045 : Blo 315835 361045 := bbase (se 8 (by rfl) ⟨2115, by rfl⟩ : syracuseStep 361045 = 4231) (by norm_num)
theorem B1606229 : Blo 315835 1606229 := bbase (se 8 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 1606229 = 18823) (by norm_num)
theorem B1081957 : Blo 315835 1081957 := bbase (se 4 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 1081957 = 202867) (by norm_num)
theorem B361117 : Blo 315835 361117 := bbase (se 3 (by rfl) ⟨67709, by rfl⟩ : syracuseStep 361117 = 135419) (by norm_num)
theorem B394177 : Blo 315835 394177 := bbase (se 2 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 394177 = 295633) (by norm_num)
theorem B820469 : Blo 315835 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B361733 : Blo 315835 361733 := bbase (se 4 (by rfl) ⟨33912, by rfl⟩ : syracuseStep 361733 = 67825) (by norm_num)
theorem B722197 : Blo 315835 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B361829 : Blo 315835 361829 := bbase (se 4 (by rfl) ⟨33921, by rfl⟩ : syracuseStep 361829 = 67843) (by norm_num)
theorem B1017365 : Blo 315835 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B1214149 : Blo 315835 1214149 := bbase (se 4 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 1214149 = 227653) (by norm_num)
theorem B362281 : Blo 315835 362281 := bbase (se 2 (by rfl) ⟨135855, by rfl⟩ : syracuseStep 362281 = 271711) (by norm_num)
theorem B1607525 : Blo 315835 1607525 := bbase (se 4 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 1607525 = 301411) (by norm_num)
theorem B460733 : Blo 315835 460733 := bbase (se 3 (by rfl) ⟨86387, by rfl⟩ : syracuseStep 460733 = 172775) (by norm_num)
theorem B1018277 : Blo 315835 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B428509 : Blo 315835 428509 := bbase (se 3 (by rfl) ⟨80345, by rfl⟩ : syracuseStep 428509 = 160691) (by norm_num)
theorem B330481 : Blo 315835 330481 := bbase (se 2 (by rfl) ⟨123930, by rfl⟩ : syracuseStep 330481 = 247861) (by norm_num)
theorem B1084229 : Blo 315835 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B4557845 : Blo 315835 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B1608821 : Blo 315835 1608821 := bbase (se 5 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 1608821 = 150827) (by norm_num)
theorem B724133 : Blo 315835 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B691517 : Blo 315835 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B855365 : Blo 315835 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B364033 : Blo 315835 364033 := bbase (se 2 (by rfl) ⟨136512, by rfl⟩ : syracuseStep 364033 = 273025) (by norm_num)
theorem B1281541 : Blo 315835 1281541 := bbase (se 4 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 1281541 = 240289) (by norm_num)
theorem B1707637 : Blo 315835 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1019621 : Blo 315835 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B725117 : Blo 315835 725117 := bbase (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) (by norm_num)
theorem B1610117 : Blo 315835 1610117 := bbase (se 4 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 1610117 = 301897) (by norm_num)
theorem B332429 : Blo 315835 332429 := bbase (se 3 (by rfl) ⟨62330, by rfl⟩ : syracuseStep 332429 = 124661) (by norm_num)
theorem B725701 : Blo 315835 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B1021045 : Blo 315835 1021045 := bbase (se 5 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 1021045 = 95723) (by norm_num)
theorem B1807829 : Blo 315835 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B3053173 : Blo 315835 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B1611413 : Blo 315835 1611413 := bbase (se 6 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 1611413 = 75535) (by norm_num)
theorem B1218277 : Blo 315835 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B726869 : Blo 315835 726869 := bbase (se 9 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 726869 = 4259) (by norm_num)
theorem B759709 : Blo 315835 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B792845 : Blo 315835 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B399745 : Blo 315835 399745 := bbase (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) (by norm_num)
theorem B399917 : Blo 315835 399917 := bbase (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) (by norm_num)
theorem B760373 : Blo 315835 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B399973 : Blo 315835 399973 := bbase (se 4 (by rfl) ⟨37497, by rfl⟩ : syracuseStep 399973 = 74995) (by norm_num)
theorem B1809013 : Blo 315835 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B2038421 : Blo 315835 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B1022645 : Blo 315835 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B400069 : Blo 315835 400069 := bbase (se 4 (by rfl) ⟨37506, by rfl⟩ : syracuseStep 400069 = 75013) (by norm_num)
theorem B760661 : Blo 315835 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B400241 : Blo 315835 400241 := bbase (se 2 (by rfl) ⟨150090, by rfl⟩ : syracuseStep 400241 = 300181) (by norm_num)
theorem B1612709 : Blo 315835 1612709 := bbase (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) (by norm_num)
theorem B400297 : Blo 315835 400297 := bbase (se 2 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 400297 = 300223) (by norm_num)
theorem B400393 : Blo 315835 400393 := bbase (se 2 (by rfl) ⟨150147, by rfl⟩ : syracuseStep 400393 = 300295) (by norm_num)
theorem B2399381 : Blo 315835 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B400565 : Blo 315835 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B400621 : Blo 315835 400621 := bbase (se 3 (by rfl) ⟨75116, by rfl⟩ : syracuseStep 400621 = 150233) (by norm_num)
theorem B400717 : Blo 315835 400717 := bbase (se 3 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 400717 = 150269) (by norm_num)
theorem B400889 : Blo 315835 400889 := bbase (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) (by norm_num)
theorem B400945 : Blo 315835 400945 := bbase (se 2 (by rfl) ⟨150354, by rfl⟩ : syracuseStep 400945 = 300709) (by norm_num)
theorem B401041 : Blo 315835 401041 := bbase (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) (by norm_num)
theorem B2989781 : Blo 315835 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B1023749 : Blo 315835 1023749 := bbase (se 4 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 1023749 = 191953) (by norm_num)
theorem B499469 : Blo 315835 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B1154837 : Blo 315835 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B401213 : Blo 315835 401213 := bbase (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) (by norm_num)
theorem B401269 : Blo 315835 401269 := bbase (se 5 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 401269 = 37619) (by norm_num)
theorem B401365 : Blo 315835 401365 := bbase (se 7 (by rfl) ⟨4703, by rfl⟩ : syracuseStep 401365 = 9407) (by norm_num)
theorem B401537 : Blo 315835 401537 := bbase (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) (by norm_num)
theorem B1614005 : Blo 315835 1614005 := bbase (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) (by norm_num)
theorem B401593 : Blo 315835 401593 := bbase (se 2 (by rfl) ⟨150597, by rfl⟩ : syracuseStep 401593 = 301195) (by norm_num)
theorem B401689 : Blo 315835 401689 := bbase (se 2 (by rfl) ⟨150633, by rfl⟩ : syracuseStep 401689 = 301267) (by norm_num)
theorem B2662741 : Blo 315835 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B401861 : Blo 315835 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B532973 : Blo 315835 532973 := bbase (se 3 (by rfl) ⟨99932, by rfl⟩ : syracuseStep 532973 = 199865) (by norm_num)
theorem B401917 : Blo 315835 401917 := bbase (se 3 (by rfl) ⟨75359, by rfl⟩ : syracuseStep 401917 = 150719) (by norm_num)
theorem B1810997 : Blo 315835 1810997 := bbase (se 5 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 1810997 = 169781) (by norm_num)
theorem B402013 : Blo 315835 402013 := bbase (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) (by norm_num)
theorem B533101 : Blo 315835 533101 := bbase (se 3 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 533101 = 199913) (by norm_num)
theorem B533189 : Blo 315835 533189 := bbase (se 4 (by rfl) ⟨49986, by rfl⟩ : syracuseStep 533189 = 99973) (by norm_num)
theorem B402185 : Blo 315835 402185 := bbase (se 2 (by rfl) ⟨150819, by rfl⟩ : syracuseStep 402185 = 301639) (by norm_num)
theorem B402241 : Blo 315835 402241 := bbase (se 2 (by rfl) ⟨150840, by rfl⟩ : syracuseStep 402241 = 301681) (by norm_num)
theorem B533317 : Blo 315835 533317 := bbase (se 4 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 533317 = 99997) (by norm_num)
theorem B762709 : Blo 315835 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B533405 : Blo 315835 533405 := bbase (se 3 (by rfl) ⟨100013, by rfl⟩ : syracuseStep 533405 = 200027) (by norm_num)
theorem B402337 : Blo 315835 402337 := bbase (se 2 (by rfl) ⟨150876, by rfl⟩ : syracuseStep 402337 = 301753) (by norm_num)
theorem B1352645 : Blo 315835 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B533533 : Blo 315835 533533 := bbase (se 3 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 533533 = 200075) (by norm_num)
theorem B402509 : Blo 315835 402509 := bbase (se 3 (by rfl) ⟨75470, by rfl⟩ : syracuseStep 402509 = 150941) (by norm_num)
theorem B533621 : Blo 315835 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B402565 : Blo 315835 402565 := bbase (se 4 (by rfl) ⟨37740, by rfl⟩ : syracuseStep 402565 = 75481) (by norm_num)
theorem B1352933 : Blo 315835 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B402661 : Blo 315835 402661 := bbase (se 4 (by rfl) ⟨37749, by rfl⟩ : syracuseStep 402661 = 75499) (by norm_num)
theorem B533749 : Blo 315835 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B533837 : Blo 315835 533837 := bbase (se 3 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 533837 = 200189) (by norm_num)
theorem B402833 : Blo 315835 402833 := bbase (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) (by norm_num)
theorem B1615301 : Blo 315835 1615301 := bbase (se 4 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 1615301 = 302869) (by norm_num)
theorem B402889 : Blo 315835 402889 := bbase (se 2 (by rfl) ⟨151083, by rfl⟩ : syracuseStep 402889 = 302167) (by norm_num)
theorem B533965 : Blo 315835 533965 := bbase (se 3 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 533965 = 200237) (by norm_num)
theorem B534053 : Blo 315835 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B402985 : Blo 315835 402985 := bbase (se 2 (by rfl) ⟨151119, by rfl⟩ : syracuseStep 402985 = 302239) (by norm_num)
theorem B599717 : Blo 315835 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B534181 : Blo 315835 534181 := bbase (se 4 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 534181 = 100159) (by norm_num)
theorem B403157 : Blo 315835 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B861941 : Blo 315835 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B534269 : Blo 315835 534269 := bbase (se 3 (by rfl) ⟨100175, by rfl⟩ : syracuseStep 534269 = 200351) (by norm_num)
theorem B403213 : Blo 315835 403213 := bbase (se 3 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 403213 = 151205) (by norm_num)
theorem B599861 : Blo 315835 599861 := bbase (se 5 (by rfl) ⟨28118, by rfl⟩ : syracuseStep 599861 = 56237) (by norm_num)
theorem B337717 : Blo 315835 337717 := bbase (se 5 (by rfl) ⟨15830, by rfl⟩ : syracuseStep 337717 = 31661) (by norm_num)
theorem B403309 : Blo 315835 403309 := bbase (se 3 (by rfl) ⟨75620, by rfl⟩ : syracuseStep 403309 = 151241) (by norm_num)
theorem B337789 : Blo 315835 337789 := bbase (se 3 (by rfl) ⟨63335, by rfl⟩ : syracuseStep 337789 = 126671) (by norm_num)
theorem B534397 : Blo 315835 534397 := bbase (se 3 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 534397 = 200399) (by norm_num)
theorem B534485 : Blo 315835 534485 := bbase (se 7 (by rfl) ⟨6263, by rfl⟩ : syracuseStep 534485 = 12527) (by norm_num)
theorem B1353685 : Blo 315835 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B403481 : Blo 315835 403481 := bbase (se 2 (by rfl) ⟨151305, by rfl⟩ : syracuseStep 403481 = 302611) (by norm_num)
theorem B337969 : Blo 315835 337969 := bbase (se 2 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 337969 = 253477) (by norm_num)
theorem B403537 : Blo 315835 403537 := bbase (se 2 (by rfl) ⟨151326, by rfl⟩ : syracuseStep 403537 = 302653) (by norm_num)
theorem B600149 : Blo 315835 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B534613 : Blo 315835 534613 := bbase (se 8 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 534613 = 6265) (by norm_num)
theorem B534701 : Blo 315835 534701 := bbase (se 3 (by rfl) ⟨100256, by rfl⟩ : syracuseStep 534701 = 200513) (by norm_num)
theorem B403633 : Blo 315835 403633 := bbase (se 2 (by rfl) ⟨151362, by rfl⟩ : syracuseStep 403633 = 302725) (by norm_num)
theorem B1943765 : Blo 315835 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B600301 : Blo 315835 600301 := bbase (se 3 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 600301 = 225113) (by norm_num)
theorem B3352853 : Blo 315835 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B534829 : Blo 315835 534829 := bbase (se 3 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 534829 = 200561) (by norm_num)
theorem B403805 : Blo 315835 403805 := bbase (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) (by norm_num)
theorem B534917 : Blo 315835 534917 := bbase (se 4 (by rfl) ⟨50148, by rfl⟩ : syracuseStep 534917 = 100297) (by norm_num)
theorem B403861 : Blo 315835 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B2042293 : Blo 315835 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B338413 : Blo 315835 338413 := bbase (se 3 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 338413 = 126905) (by norm_num)
theorem B403957 : Blo 315835 403957 := bbase (se 5 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 403957 = 37871) (by norm_num)
theorem B535045 : Blo 315835 535045 := bbase (se 4 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 535045 = 100321) (by norm_num)
theorem B600605 : Blo 315835 600605 := bbase (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) (by norm_num)
theorem B535133 : Blo 315835 535133 := bbase (se 3 (by rfl) ⟨100337, by rfl⟩ : syracuseStep 535133 = 200675) (by norm_num)
theorem B338537 : Blo 315835 338537 := bbase (se 2 (by rfl) ⟨126951, by rfl⟩ : syracuseStep 338537 = 253903) (by norm_num)
theorem B404129 : Blo 315835 404129 := bbase (se 2 (by rfl) ⟨151548, by rfl⟩ : syracuseStep 404129 = 303097) (by norm_num)
theorem B1354421 : Blo 315835 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B1288901 : Blo 315835 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B1813205 : Blo 315835 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B1616597 : Blo 315835 1616597 := bbase (se 7 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 1616597 = 37889) (by norm_num)
theorem B404185 : Blo 315835 404185 := bbase (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) (by norm_num)
theorem B535261 : Blo 315835 535261 := bbase (se 3 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 535261 = 200723) (by norm_num)
theorem B535349 : Blo 315835 535349 := bbase (se 5 (by rfl) ⟨25094, by rfl⟩ : syracuseStep 535349 = 50189) (by norm_num)
theorem B404281 : Blo 315835 404281 := bbase (se 2 (by rfl) ⟨151605, by rfl⟩ : syracuseStep 404281 = 303211) (by norm_num)
theorem B338789 : Blo 315835 338789 := bbase (se 4 (by rfl) ⟨31761, by rfl⟩ : syracuseStep 338789 = 63523) (by norm_num)
theorem B535477 : Blo 315835 535477 := bbase (se 5 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 535477 = 50201) (by norm_num)
theorem B404453 : Blo 315835 404453 := bbase (se 4 (by rfl) ⟨37917, by rfl⟩ : syracuseStep 404453 = 75835) (by norm_num)
theorem B535565 : Blo 315835 535565 := bbase (se 3 (by rfl) ⟨100418, by rfl⟩ : syracuseStep 535565 = 200837) (by norm_num)
theorem B1027093 : Blo 315835 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B404509 : Blo 315835 404509 := bbase (se 3 (by rfl) ⟨75845, by rfl⟩ : syracuseStep 404509 = 151691) (by norm_num)
theorem B404605 : Blo 315835 404605 := bbase (se 3 (by rfl) ⟨75863, by rfl⟩ : syracuseStep 404605 = 151727) (by norm_num)
theorem B535693 : Blo 315835 535693 := bbase (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) (by norm_num)
theorem B765101 : Blo 315835 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B1518821 : Blo 315835 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B535781 : Blo 315835 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B601357 : Blo 315835 601357 := bbase (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) (by norm_num)
theorem B339233 : Blo 315835 339233 := bbase (se 2 (by rfl) ⟨127212, by rfl⟩ : syracuseStep 339233 = 254425) (by norm_num)
theorem B404777 : Blo 315835 404777 := bbase (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) (by norm_num)
theorem B765245 : Blo 315835 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B535909 : Blo 315835 535909 := bbase (se 4 (by rfl) ⟨50241, by rfl⟩ : syracuseStep 535909 = 100483) (by norm_num)
theorem B601501 : Blo 315835 601501 := bbase (se 3 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 601501 = 225563) (by norm_num)
theorem B863669 : Blo 315835 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B535997 : Blo 315835 535997 := bbase (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) (by norm_num)
theorem B962005 : Blo 315835 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B339481 : Blo 315835 339481 := bbase (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) (by norm_num)
theorem B601661 : Blo 315835 601661 := bbase (se 3 (by rfl) ⟨112811, by rfl⟩ : syracuseStep 601661 = 225623) (by norm_num)
theorem B536125 : Blo 315835 536125 := bbase (se 3 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 536125 = 201047) (by norm_num)
theorem B536213 : Blo 315835 536213 := bbase (se 6 (by rfl) ⟨12567, by rfl⟩ : syracuseStep 536213 = 25135) (by norm_num)
theorem B601805 : Blo 315835 601805 := bbase (se 3 (by rfl) ⟨112838, by rfl⟩ : syracuseStep 601805 = 225677) (by norm_num)
theorem B536341 : Blo 315835 536341 := bbase (se 6 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 536341 = 25141) (by norm_num)
theorem B3059477 : Blo 315835 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B536429 : Blo 315835 536429 := bbase (se 3 (by rfl) ⟨100580, by rfl⟩ : syracuseStep 536429 = 201161) (by norm_num)
theorem B339925 : Blo 315835 339925 := bbase (se 7 (by rfl) ⟨3983, by rfl⟩ : syracuseStep 339925 = 7967) (by norm_num)
theorem B1617893 : Blo 315835 1617893 := bbase (se 4 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 1617893 = 303355) (by norm_num)
theorem B602093 : Blo 315835 602093 := bbase (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) (by norm_num)
theorem B536557 : Blo 315835 536557 := bbase (se 3 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 536557 = 201209) (by norm_num)
theorem B569357 : Blo 315835 569357 := bbase (se 3 (by rfl) ⟨106754, by rfl⟩ : syracuseStep 569357 = 213509) (by norm_num)
theorem B339985 : Blo 315835 339985 := bbase (se 2 (by rfl) ⟨127494, by rfl⟩ : syracuseStep 339985 = 254989) (by norm_num)
theorem B536645 : Blo 315835 536645 := bbase (se 4 (by rfl) ⟨50310, by rfl⟩ : syracuseStep 536645 = 100621) (by norm_num)
theorem B602245 : Blo 315835 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B536773 : Blo 315835 536773 := bbase (se 4 (by rfl) ⟨50322, by rfl⟩ : syracuseStep 536773 = 100645) (by norm_num)
theorem B536861 : Blo 315835 536861 := bbase (se 3 (by rfl) ⟨100661, by rfl⟩ : syracuseStep 536861 = 201323) (by norm_num)
theorem B340301 : Blo 315835 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B536989 : Blo 315835 536989 := bbase (se 3 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 536989 = 201371) (by norm_num)
theorem B602549 : Blo 315835 602549 := bbase (se 5 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 602549 = 56489) (by norm_num)
theorem B537077 : Blo 315835 537077 := bbase (se 5 (by rfl) ⟨25175, by rfl⟩ : syracuseStep 537077 = 50351) (by norm_num)
theorem B9810517 : Blo 315835 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B537205 : Blo 315835 537205 := bbase (se 5 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 537205 = 50363) (by norm_num)
theorem B537293 : Blo 315835 537293 := bbase (se 3 (by rfl) ⟨100742, by rfl⟩ : syracuseStep 537293 = 201485) (by norm_num)
theorem B340745 : Blo 315835 340745 := bbase (se 2 (by rfl) ⟨127779, by rfl⟩ : syracuseStep 340745 = 255559) (by norm_num)
theorem B799541 : Blo 315835 799541 := bbase (se 5 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 799541 = 74957) (by norm_num)
theorem B340805 : Blo 315835 340805 := bbase (se 4 (by rfl) ⟨31950, by rfl⟩ : syracuseStep 340805 = 63901) (by norm_num)
theorem B537421 : Blo 315835 537421 := bbase (se 3 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 537421 = 201533) (by norm_num)
theorem B537509 : Blo 315835 537509 := bbase (se 4 (by rfl) ⟨50391, by rfl⟩ : syracuseStep 537509 = 100783) (by norm_num)
theorem B340933 : Blo 315835 340933 := bbase (se 4 (by rfl) ⟨31962, by rfl⟩ : syracuseStep 340933 = 63925) (by norm_num)
theorem B3683285 : Blo 315835 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B799733 : Blo 315835 799733 := bbase (se 5 (by rfl) ⟨37487, by rfl⟩ : syracuseStep 799733 = 74975) (by norm_num)
theorem B406525 : Blo 315835 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B537637 : Blo 315835 537637 := bbase (se 4 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 537637 = 100807) (by norm_num)
theorem B537725 : Blo 315835 537725 := bbase (se 3 (by rfl) ⟨100823, by rfl⟩ : syracuseStep 537725 = 201647) (by norm_num)
theorem B603301 : Blo 315835 603301 := bbase (se 4 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 603301 = 113119) (by norm_num)
theorem B537853 : Blo 315835 537853 := bbase (se 3 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 537853 = 201695) (by norm_num)
theorem B963845 : Blo 315835 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B767245 : Blo 315835 767245 := bbase (se 3 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 767245 = 287717) (by norm_num)
theorem B603445 : Blo 315835 603445 := bbase (se 5 (by rfl) ⟨28286, by rfl⟩ : syracuseStep 603445 = 56573) (by norm_num)
theorem B800077 : Blo 315835 800077 := bbase (se 3 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 800077 = 300029) (by norm_num)
theorem B537941 : Blo 315835 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B865637 : Blo 315835 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B1521013 : Blo 315835 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B341377 : Blo 315835 341377 := bbase (se 2 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 341377 = 256033) (by norm_num)
theorem B800189 : Blo 315835 800189 := bbase (se 3 (by rfl) ⟨150035, by rfl⟩ : syracuseStep 800189 = 300071) (by norm_num)
theorem B603605 : Blo 315835 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B538069 : Blo 315835 538069 := bbase (se 7 (by rfl) ⟨6305, by rfl⟩ : syracuseStep 538069 = 12611) (by norm_num)
theorem B341497 : Blo 315835 341497 := bbase (se 2 (by rfl) ⟨128061, by rfl⟩ : syracuseStep 341497 = 256123) (by norm_num)
theorem B538157 : Blo 315835 538157 := bbase (se 3 (by rfl) ⟨100904, by rfl⟩ : syracuseStep 538157 = 201809) (by norm_num)
theorem B603749 : Blo 315835 603749 := bbase (se 4 (by rfl) ⟨56601, by rfl⟩ : syracuseStep 603749 = 113203) (by norm_num)
theorem B800381 : Blo 315835 800381 := bbase (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) (by norm_num)
theorem B538285 : Blo 315835 538285 := bbase (se 3 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 538285 = 201857) (by norm_num)
theorem B538373 : Blo 315835 538373 := bbase (se 4 (by rfl) ⟨50472, by rfl⟩ : syracuseStep 538373 = 100945) (by norm_num)
theorem B2176885 : Blo 315835 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B538501 : Blo 315835 538501 := bbase (se 4 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 538501 = 100969) (by norm_num)
theorem B604037 : Blo 315835 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B1357717 : Blo 315835 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B800725 : Blo 315835 800725 := bbase (se 7 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 800725 = 18767) (by norm_num)
theorem B538589 : Blo 315835 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B604189 : Blo 315835 604189 := bbase (se 3 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 604189 = 226571) (by norm_num)
theorem B800837 : Blo 315835 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B538717 : Blo 315835 538717 := bbase (se 3 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 538717 = 202019) (by norm_num)
theorem B538805 : Blo 315835 538805 := bbase (se 5 (by rfl) ⟨25256, by rfl⟩ : syracuseStep 538805 = 50513) (by norm_num)
theorem B735437 : Blo 315835 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B506069 : Blo 315835 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B801029 : Blo 315835 801029 := bbase (se 4 (by rfl) ⟨75096, by rfl⟩ : syracuseStep 801029 = 150193) (by norm_num)
theorem B538933 : Blo 315835 538933 := bbase (se 5 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 538933 = 50525) (by norm_num)
theorem B604493 : Blo 315835 604493 := bbase (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) (by norm_num)
theorem B506197 : Blo 315835 506197 := bbase (se 10 (by rfl) ⟨741, by rfl⟩ : syracuseStep 506197 = 1483) (by norm_num)
theorem B539021 : Blo 315835 539021 := bbase (se 3 (by rfl) ⟨101066, by rfl⟩ : syracuseStep 539021 = 202133) (by norm_num)
theorem B1161733 : Blo 315835 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B539149 : Blo 315835 539149 := bbase (se 3 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 539149 = 202181) (by norm_num)
theorem B571981 : Blo 315835 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B801373 : Blo 315835 801373 := bbase (se 3 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 801373 = 300515) (by norm_num)
theorem B539237 : Blo 315835 539237 := bbase (se 4 (by rfl) ⟨50553, by rfl⟩ : syracuseStep 539237 = 101107) (by norm_num)
theorem B473765 : Blo 315835 473765 := bbase (se 4 (by rfl) ⟨44415, by rfl⟩ : syracuseStep 473765 = 88831) (by norm_num)
theorem B473789 : Blo 315835 473789 := bbase (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) (by norm_num)
theorem B801485 : Blo 315835 801485 := bbase (se 3 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 801485 = 300557) (by norm_num)
theorem B473813 : Blo 315835 473813 := bbase (se 7 (by rfl) ⟨5552, by rfl⟩ : syracuseStep 473813 = 11105) (by norm_num)
theorem B572125 : Blo 315835 572125 := bbase (se 3 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 572125 = 214547) (by norm_num)
theorem B539365 : Blo 315835 539365 := bbase (se 4 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 539365 = 101131) (by norm_num)
theorem B473837 : Blo 315835 473837 := bbase (se 3 (by rfl) ⟨88844, by rfl⟩ : syracuseStep 473837 = 177689) (by norm_num)
theorem B2407157 : Blo 315835 2407157 := bbase (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) (by norm_num)
theorem B473861 : Blo 315835 473861 := bbase (se 4 (by rfl) ⟨44424, by rfl⟩ : syracuseStep 473861 = 88849) (by norm_num)
theorem B473885 : Blo 315835 473885 := bbase (se 3 (by rfl) ⟨88853, by rfl⟩ : syracuseStep 473885 = 177707) (by norm_num)
theorem B473909 : Blo 315835 473909 := bbase (se 5 (by rfl) ⟨22214, by rfl⟩ : syracuseStep 473909 = 44429) (by norm_num)
theorem B539453 : Blo 315835 539453 := bbase (se 3 (by rfl) ⟨101147, by rfl⟩ : syracuseStep 539453 = 202295) (by norm_num)
theorem B473933 : Blo 315835 473933 := bbase (se 3 (by rfl) ⟨88862, by rfl⟩ : syracuseStep 473933 = 177725) (by norm_num)
theorem B473957 : Blo 315835 473957 := bbase (se 4 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 473957 = 88867) (by norm_num)
theorem B473981 : Blo 315835 473981 := bbase (se 3 (by rfl) ⟨88871, by rfl⟩ : syracuseStep 473981 = 177743) (by norm_num)
theorem B801677 : Blo 315835 801677 := bbase (se 3 (by rfl) ⟨150314, by rfl⟩ : syracuseStep 801677 = 300629) (by norm_num)
theorem B474005 : Blo 315835 474005 := bbase (se 6 (by rfl) ⟨11109, by rfl⟩ : syracuseStep 474005 = 22219) (by norm_num)
theorem B474029 : Blo 315835 474029 := bbase (se 3 (by rfl) ⟨88880, by rfl⟩ : syracuseStep 474029 = 177761) (by norm_num)
theorem B572341 : Blo 315835 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B539581 : Blo 315835 539581 := bbase (se 3 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 539581 = 202343) (by norm_num)
theorem B474053 : Blo 315835 474053 := bbase (se 4 (by rfl) ⟨44442, by rfl⟩ : syracuseStep 474053 = 88885) (by norm_num)
theorem B867269 : Blo 315835 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B474077 : Blo 315835 474077 := bbase (se 3 (by rfl) ⟨88889, by rfl⟩ : syracuseStep 474077 = 177779) (by norm_num)
theorem B474101 : Blo 315835 474101 := bbase (se 5 (by rfl) ⟨22223, by rfl⟩ : syracuseStep 474101 = 44447) (by norm_num)
theorem B474125 : Blo 315835 474125 := bbase (se 3 (by rfl) ⟨88898, by rfl⟩ : syracuseStep 474125 = 177797) (by norm_num)
theorem B539669 : Blo 315835 539669 := bbase (se 6 (by rfl) ⟨12648, by rfl⟩ : syracuseStep 539669 = 25297) (by norm_num)
theorem B474149 : Blo 315835 474149 := bbase (se 4 (by rfl) ⟨44451, by rfl⟩ : syracuseStep 474149 = 88903) (by norm_num)
theorem B474173 : Blo 315835 474173 := bbase (se 3 (by rfl) ⟨88907, by rfl⟩ : syracuseStep 474173 = 177815) (by norm_num)
theorem B605245 : Blo 315835 605245 := bbase (se 3 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 605245 = 226967) (by norm_num)
theorem B474197 : Blo 315835 474197 := bbase (se 8 (by rfl) ⟨2778, by rfl⟩ : syracuseStep 474197 = 5557) (by norm_num)
theorem B474221 : Blo 315835 474221 := bbase (se 3 (by rfl) ⟨88916, by rfl⟩ : syracuseStep 474221 = 177833) (by norm_num)
theorem B474245 : Blo 315835 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B408721 : Blo 315835 408721 := bbase (se 2 (by rfl) ⟨153270, by rfl⟩ : syracuseStep 408721 = 306541) (by norm_num)
theorem B474269 : Blo 315835 474269 := bbase (se 3 (by rfl) ⟨88925, by rfl⟩ : syracuseStep 474269 = 177851) (by norm_num)
theorem B474293 : Blo 315835 474293 := bbase (se 5 (by rfl) ⟨22232, by rfl⟩ : syracuseStep 474293 = 44465) (by norm_num)
theorem B1293509 : Blo 315835 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B474317 : Blo 315835 474317 := bbase (se 3 (by rfl) ⟨88934, by rfl⟩ : syracuseStep 474317 = 177869) (by norm_num)
theorem B605389 : Blo 315835 605389 := bbase (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) (by norm_num)
theorem B474341 : Blo 315835 474341 := bbase (se 4 (by rfl) ⟨44469, by rfl⟩ : syracuseStep 474341 = 88939) (by norm_num)
theorem B802021 : Blo 315835 802021 := bbase (se 4 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 802021 = 150379) (by norm_num)
theorem B474365 : Blo 315835 474365 := bbase (se 3 (by rfl) ⟨88943, by rfl⟩ : syracuseStep 474365 = 177887) (by norm_num)
theorem B474389 : Blo 315835 474389 := bbase (se 6 (by rfl) ⟨11118, by rfl⟩ : syracuseStep 474389 = 22237) (by norm_num)
theorem B474413 : Blo 315835 474413 := bbase (se 3 (by rfl) ⟨88952, by rfl⟩ : syracuseStep 474413 = 177905) (by norm_num)
theorem B507197 : Blo 315835 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B474437 : Blo 315835 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B802133 : Blo 315835 802133 := bbase (se 11 (by rfl) ⟨587, by rfl⟩ : syracuseStep 802133 = 1175) (by norm_num)
theorem B474461 : Blo 315835 474461 := bbase (se 3 (by rfl) ⟨88961, by rfl⟩ : syracuseStep 474461 = 177923) (by norm_num)
theorem B605549 : Blo 315835 605549 := bbase (se 3 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 605549 = 227081) (by norm_num)
theorem B474485 : Blo 315835 474485 := bbase (se 5 (by rfl) ⟨22241, by rfl⟩ : syracuseStep 474485 = 44483) (by norm_num)
theorem B474509 : Blo 315835 474509 := bbase (se 3 (by rfl) ⟨88970, by rfl⟩ : syracuseStep 474509 = 177941) (by norm_num)
theorem B4078997 : Blo 315835 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B474533 : Blo 315835 474533 := bbase (se 4 (by rfl) ⟨44487, by rfl⟩ : syracuseStep 474533 = 88975) (by norm_num)
theorem B474557 : Blo 315835 474557 := bbase (se 3 (by rfl) ⟨88979, by rfl⟩ : syracuseStep 474557 = 177959) (by norm_num)
theorem B507325 : Blo 315835 507325 := bbase (se 3 (by rfl) ⟨95123, by rfl⟩ : syracuseStep 507325 = 190247) (by norm_num)
theorem B474581 : Blo 315835 474581 := bbase (se 7 (by rfl) ⟨5561, by rfl⟩ : syracuseStep 474581 = 11123) (by norm_num)
theorem B474605 : Blo 315835 474605 := bbase (se 3 (by rfl) ⟨88988, by rfl⟩ : syracuseStep 474605 = 177977) (by norm_num)
theorem B605693 : Blo 315835 605693 := bbase (se 3 (by rfl) ⟨113567, by rfl⟩ : syracuseStep 605693 = 227135) (by norm_num)
theorem B474629 : Blo 315835 474629 := bbase (se 4 (by rfl) ⟨44496, by rfl⟩ : syracuseStep 474629 = 88993) (by norm_num)
theorem B802325 : Blo 315835 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B474653 : Blo 315835 474653 := bbase (se 3 (by rfl) ⟨88997, by rfl⟩ : syracuseStep 474653 = 177995) (by norm_num)
theorem B474677 : Blo 315835 474677 := bbase (se 5 (by rfl) ⟨22250, by rfl⟩ : syracuseStep 474677 = 44501) (by norm_num)
theorem B474701 : Blo 315835 474701 := bbase (se 3 (by rfl) ⟨89006, by rfl⟩ : syracuseStep 474701 = 178013) (by norm_num)
theorem B474725 : Blo 315835 474725 := bbase (se 4 (by rfl) ⟨44505, by rfl⟩ : syracuseStep 474725 = 89011) (by norm_num)
theorem B474749 : Blo 315835 474749 := bbase (se 3 (by rfl) ⟨89015, by rfl⟩ : syracuseStep 474749 = 178031) (by norm_num)
theorem B474773 : Blo 315835 474773 := bbase (se 6 (by rfl) ⟨11127, by rfl⟩ : syracuseStep 474773 = 22255) (by norm_num)
theorem B474797 : Blo 315835 474797 := bbase (se 3 (by rfl) ⟨89024, by rfl⟩ : syracuseStep 474797 = 178049) (by norm_num)
theorem B474821 : Blo 315835 474821 := bbase (se 4 (by rfl) ⟨44514, by rfl⟩ : syracuseStep 474821 = 89029) (by norm_num)
theorem B2277077 : Blo 315835 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B474845 : Blo 315835 474845 := bbase (se 3 (by rfl) ⟨89033, by rfl⟩ : syracuseStep 474845 = 178067) (by norm_num)
theorem B573149 : Blo 315835 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B474869 : Blo 315835 474869 := bbase (se 5 (by rfl) ⟨22259, by rfl⟩ : syracuseStep 474869 = 44519) (by norm_num)
theorem B474893 : Blo 315835 474893 := bbase (se 3 (by rfl) ⟨89042, by rfl⟩ : syracuseStep 474893 = 178085) (by norm_num)
theorem B605981 : Blo 315835 605981 := bbase (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) (by norm_num)
theorem B474917 : Blo 315835 474917 := bbase (se 4 (by rfl) ⟨44523, by rfl⟩ : syracuseStep 474917 = 89047) (by norm_num)
theorem B474941 : Blo 315835 474941 := bbase (se 3 (by rfl) ⟨89051, by rfl⟩ : syracuseStep 474941 = 178103) (by norm_num)
theorem B507709 : Blo 315835 507709 := bbase (se 3 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 507709 = 190391) (by norm_num)
theorem B474965 : Blo 315835 474965 := bbase (se 9 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 474965 = 2783) (by norm_num)
theorem B474989 : Blo 315835 474989 := bbase (se 3 (by rfl) ⟨89060, by rfl⟩ : syracuseStep 474989 = 178121) (by norm_num)
theorem B802669 : Blo 315835 802669 := bbase (se 3 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 802669 = 301001) (by norm_num)
theorem B475013 : Blo 315835 475013 := bbase (se 4 (by rfl) ⟨44532, by rfl⟩ : syracuseStep 475013 = 89065) (by norm_num)
theorem B475037 : Blo 315835 475037 := bbase (se 3 (by rfl) ⟨89069, by rfl⟩ : syracuseStep 475037 = 178139) (by norm_num)
theorem B475061 : Blo 315835 475061 := bbase (se 5 (by rfl) ⟨22268, by rfl⟩ : syracuseStep 475061 = 44537) (by norm_num)
theorem B606133 : Blo 315835 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B475085 : Blo 315835 475085 := bbase (se 3 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 475085 = 178157) (by norm_num)
theorem B540629 : Blo 315835 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B802781 : Blo 315835 802781 := bbase (se 3 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 802781 = 301043) (by norm_num)
theorem B475109 : Blo 315835 475109 := bbase (se 4 (by rfl) ⟨44541, by rfl⟩ : syracuseStep 475109 = 89083) (by norm_num)
theorem B475133 : Blo 315835 475133 := bbase (se 3 (by rfl) ⟨89087, by rfl⟩ : syracuseStep 475133 = 178175) (by norm_num)
theorem B475157 : Blo 315835 475157 := bbase (se 6 (by rfl) ⟨11136, by rfl⟩ : syracuseStep 475157 = 22273) (by norm_num)
theorem B475181 : Blo 315835 475181 := bbase (se 3 (by rfl) ⟨89096, by rfl⟩ : syracuseStep 475181 = 178193) (by norm_num)
theorem B507965 : Blo 315835 507965 := bbase (se 3 (by rfl) ⟨95243, by rfl⟩ : syracuseStep 507965 = 190487) (by norm_num)
theorem B475205 : Blo 315835 475205 := bbase (se 4 (by rfl) ⟨44550, by rfl⟩ : syracuseStep 475205 = 89101) (by norm_num)
theorem B475229 : Blo 315835 475229 := bbase (se 3 (by rfl) ⟨89105, by rfl⟩ : syracuseStep 475229 = 178211) (by norm_num)
theorem B540773 : Blo 315835 540773 := bbase (se 4 (by rfl) ⟨50697, by rfl⟩ : syracuseStep 540773 = 101395) (by norm_num)
theorem B475253 : Blo 315835 475253 := bbase (se 5 (by rfl) ⟨22277, by rfl⟩ : syracuseStep 475253 = 44555) (by norm_num)
theorem B606341 : Blo 315835 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B475277 : Blo 315835 475277 := bbase (se 3 (by rfl) ⟨89114, by rfl⟩ : syracuseStep 475277 = 178229) (by norm_num)
theorem B802973 : Blo 315835 802973 := bbase (se 3 (by rfl) ⟨150557, by rfl⟩ : syracuseStep 802973 = 301115) (by norm_num)
theorem B475301 : Blo 315835 475301 := bbase (se 4 (by rfl) ⟨44559, by rfl⟩ : syracuseStep 475301 = 89119) (by norm_num)
theorem B475325 : Blo 315835 475325 := bbase (se 3 (by rfl) ⟨89123, by rfl⟩ : syracuseStep 475325 = 178247) (by norm_num)
theorem B475349 : Blo 315835 475349 := bbase (se 7 (by rfl) ⟨5570, by rfl⟩ : syracuseStep 475349 = 11141) (by norm_num)
theorem B606437 : Blo 315835 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B475373 : Blo 315835 475373 := bbase (se 3 (by rfl) ⟨89132, by rfl⟩ : syracuseStep 475373 = 178265) (by norm_num)
theorem B475397 : Blo 315835 475397 := bbase (se 4 (by rfl) ⟨44568, by rfl⟩ : syracuseStep 475397 = 89137) (by norm_num)
theorem B1294613 : Blo 315835 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B475421 : Blo 315835 475421 := bbase (se 3 (by rfl) ⟨89141, by rfl⟩ : syracuseStep 475421 = 178283) (by norm_num)
theorem B475445 : Blo 315835 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B475469 : Blo 315835 475469 := bbase (se 3 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 475469 = 178301) (by norm_num)
theorem B475493 : Blo 315835 475493 := bbase (se 4 (by rfl) ⟨44577, by rfl⟩ : syracuseStep 475493 = 89155) (by norm_num)
theorem B475517 : Blo 315835 475517 := bbase (se 3 (by rfl) ⟨89159, by rfl⟩ : syracuseStep 475517 = 178319) (by norm_num)
theorem B475541 : Blo 315835 475541 := bbase (se 6 (by rfl) ⟨11145, by rfl⟩ : syracuseStep 475541 = 22291) (by norm_num)
theorem B475565 : Blo 315835 475565 := bbase (se 3 (by rfl) ⟨89168, by rfl⟩ : syracuseStep 475565 = 178337) (by norm_num)
theorem B475589 : Blo 315835 475589 := bbase (se 4 (by rfl) ⟨44586, by rfl⟩ : syracuseStep 475589 = 89173) (by norm_num)
theorem B4047317 : Blo 315835 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B475613 : Blo 315835 475613 := bbase (se 3 (by rfl) ⟨89177, by rfl⟩ : syracuseStep 475613 = 178355) (by norm_num)
theorem B475637 : Blo 315835 475637 := bbase (se 5 (by rfl) ⟨22295, by rfl⟩ : syracuseStep 475637 = 44591) (by norm_num)
theorem B803317 : Blo 315835 803317 := bbase (se 5 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 803317 = 75311) (by norm_num)
theorem B573941 : Blo 315835 573941 := bbase (se 5 (by rfl) ⟨26903, by rfl⟩ : syracuseStep 573941 = 53807) (by norm_num)
theorem B901637 : Blo 315835 901637 := bbase (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) (by norm_num)
theorem B475661 : Blo 315835 475661 := bbase (se 3 (by rfl) ⟨89186, by rfl⟩ : syracuseStep 475661 = 178373) (by norm_num)
theorem B6242837 : Blo 315835 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B475685 : Blo 315835 475685 := bbase (se 4 (by rfl) ⟨44595, by rfl⟩ : syracuseStep 475685 = 89191) (by norm_num)
theorem B475709 : Blo 315835 475709 := bbase (se 3 (by rfl) ⟨89195, by rfl⟩ : syracuseStep 475709 = 178391) (by norm_num)
theorem B770629 : Blo 315835 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B475733 : Blo 315835 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B1458773 : Blo 315835 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B803429 : Blo 315835 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B475757 : Blo 315835 475757 := bbase (se 3 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 475757 = 178409) (by norm_num)
theorem B475781 : Blo 315835 475781 := bbase (se 4 (by rfl) ⟨44604, by rfl⟩ : syracuseStep 475781 = 89209) (by norm_num)
theorem B574085 : Blo 315835 574085 := bbase (se 4 (by rfl) ⟨53820, by rfl⟩ : syracuseStep 574085 = 107641) (by norm_num)
theorem B475805 : Blo 315835 475805 := bbase (se 3 (by rfl) ⟨89213, by rfl⟩ : syracuseStep 475805 = 178427) (by norm_num)
theorem B475829 : Blo 315835 475829 := bbase (se 5 (by rfl) ⟨22304, by rfl⟩ : syracuseStep 475829 = 44609) (by norm_num)
theorem B475853 : Blo 315835 475853 := bbase (se 3 (by rfl) ⟨89222, by rfl⟩ : syracuseStep 475853 = 178445) (by norm_num)
theorem B541397 : Blo 315835 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B574165 : Blo 315835 574165 := bbase (se 7 (by rfl) ⟨6728, by rfl⟩ : syracuseStep 574165 = 13457) (by norm_num)
theorem B475877 : Blo 315835 475877 := bbase (se 4 (by rfl) ⟨44613, by rfl⟩ : syracuseStep 475877 = 89227) (by norm_num)
theorem B475901 : Blo 315835 475901 := bbase (se 3 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 475901 = 178463) (by norm_num)
theorem B475925 : Blo 315835 475925 := bbase (se 6 (by rfl) ⟨11154, by rfl⟩ : syracuseStep 475925 = 22309) (by norm_num)
theorem B574229 : Blo 315835 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B803621 : Blo 315835 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B475949 : Blo 315835 475949 := bbase (se 3 (by rfl) ⟨89240, by rfl⟩ : syracuseStep 475949 = 178481) (by norm_num)
theorem B344893 : Blo 315835 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B475973 : Blo 315835 475973 := bbase (se 4 (by rfl) ⟨44622, by rfl⟩ : syracuseStep 475973 = 89245) (by norm_num)
theorem B1360709 : Blo 315835 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B475997 : Blo 315835 475997 := bbase (se 3 (by rfl) ⟨89249, by rfl⟩ : syracuseStep 475997 = 178499) (by norm_num)
theorem B476021 : Blo 315835 476021 := bbase (se 5 (by rfl) ⟨22313, by rfl⟩ : syracuseStep 476021 = 44627) (by norm_num)
theorem B934789 : Blo 315835 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B476045 : Blo 315835 476045 := bbase (se 3 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 476045 = 178517) (by norm_num)
theorem B476069 : Blo 315835 476069 := bbase (se 4 (by rfl) ⟨44631, by rfl⟩ : syracuseStep 476069 = 89263) (by norm_num)
theorem B508837 : Blo 315835 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B476093 : Blo 315835 476093 := bbase (se 3 (by rfl) ⟨89267, by rfl⟩ : syracuseStep 476093 = 178535) (by norm_num)
theorem B476117 : Blo 315835 476117 := bbase (se 7 (by rfl) ⟨5579, by rfl⟩ : syracuseStep 476117 = 11159) (by norm_num)
theorem B607189 : Blo 315835 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B476141 : Blo 315835 476141 := bbase (se 3 (by rfl) ⟨89276, by rfl⟩ : syracuseStep 476141 = 178553) (by norm_num)
theorem B476165 : Blo 315835 476165 := bbase (se 4 (by rfl) ⟨44640, by rfl⟩ : syracuseStep 476165 = 89281) (by norm_num)
theorem B508933 : Blo 315835 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B476189 : Blo 315835 476189 := bbase (se 3 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 476189 = 178571) (by norm_num)
theorem B476213 : Blo 315835 476213 := bbase (se 5 (by rfl) ⟨22322, by rfl⟩ : syracuseStep 476213 = 44645) (by norm_num)
theorem B476237 : Blo 315835 476237 := bbase (se 3 (by rfl) ⟨89294, by rfl⟩ : syracuseStep 476237 = 178589) (by norm_num)
theorem B476261 : Blo 315835 476261 := bbase (se 4 (by rfl) ⟨44649, by rfl⟩ : syracuseStep 476261 = 89299) (by norm_num)
theorem B476285 : Blo 315835 476285 := bbase (se 3 (by rfl) ⟨89303, by rfl⟩ : syracuseStep 476285 = 178607) (by norm_num)
theorem B803965 : Blo 315835 803965 := bbase (se 3 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 803965 = 301487) (by norm_num)
theorem B476309 : Blo 315835 476309 := bbase (se 6 (by rfl) ⟨11163, by rfl⟩ : syracuseStep 476309 = 22327) (by norm_num)
theorem B509093 : Blo 315835 509093 := bbase (se 4 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 509093 = 95455) (by norm_num)
theorem B476333 : Blo 315835 476333 := bbase (se 3 (by rfl) ⟨89312, by rfl⟩ : syracuseStep 476333 = 178625) (by norm_num)
theorem B476357 : Blo 315835 476357 := bbase (se 4 (by rfl) ⟨44658, by rfl⟩ : syracuseStep 476357 = 89317) (by norm_num)
theorem B476381 : Blo 315835 476381 := bbase (se 3 (by rfl) ⟨89321, by rfl⟩ : syracuseStep 476381 = 178643) (by norm_num)
theorem B804077 : Blo 315835 804077 := bbase (se 3 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 804077 = 301529) (by norm_num)
theorem B1066229 : Blo 315835 1066229 := bbase (se 5 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 1066229 = 99959) (by norm_num)
theorem B476405 : Blo 315835 476405 := bbase (se 5 (by rfl) ⟨22331, by rfl⟩ : syracuseStep 476405 = 44663) (by norm_num)
theorem B476429 : Blo 315835 476429 := bbase (se 3 (by rfl) ⟨89330, by rfl⟩ : syracuseStep 476429 = 178661) (by norm_num)
theorem B1525013 : Blo 315835 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B476453 : Blo 315835 476453 := bbase (se 4 (by rfl) ⟨44667, by rfl⟩ : syracuseStep 476453 = 89335) (by norm_num)
theorem B476477 : Blo 315835 476477 := bbase (se 3 (by rfl) ⟨89339, by rfl⟩ : syracuseStep 476477 = 178679) (by norm_num)
theorem B476501 : Blo 315835 476501 := bbase (se 12 (by rfl) ⟨174, by rfl⟩ : syracuseStep 476501 = 349) (by norm_num)
theorem B476525 : Blo 315835 476525 := bbase (se 3 (by rfl) ⟨89348, by rfl⟩ : syracuseStep 476525 = 178697) (by norm_num)
theorem B640381 : Blo 315835 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B476549 : Blo 315835 476549 := bbase (se 4 (by rfl) ⟨44676, by rfl⟩ : syracuseStep 476549 = 89353) (by norm_num)
theorem B476573 : Blo 315835 476573 := bbase (se 3 (by rfl) ⟨89357, by rfl⟩ : syracuseStep 476573 = 178715) (by norm_num)
theorem B804269 : Blo 315835 804269 := bbase (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) (by norm_num)
theorem B476597 : Blo 315835 476597 := bbase (se 5 (by rfl) ⟨22340, by rfl⟩ : syracuseStep 476597 = 44681) (by norm_num)
theorem B476621 : Blo 315835 476621 := bbase (se 3 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 476621 = 178733) (by norm_num)
theorem B476645 : Blo 315835 476645 := bbase (se 4 (by rfl) ⟨44685, by rfl⟩ : syracuseStep 476645 = 89371) (by norm_num)
theorem B476669 : Blo 315835 476669 := bbase (se 3 (by rfl) ⟨89375, by rfl⟩ : syracuseStep 476669 = 178751) (by norm_num)
theorem B476693 : Blo 315835 476693 := bbase (se 6 (by rfl) ⟨11172, by rfl⟩ : syracuseStep 476693 = 22345) (by norm_num)
theorem B1295909 : Blo 315835 1295909 := bbase (se 4 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 1295909 = 242983) (by norm_num)
theorem B476717 : Blo 315835 476717 := bbase (se 3 (by rfl) ⟨89384, by rfl⟩ : syracuseStep 476717 = 178769) (by norm_num)
theorem B476741 : Blo 315835 476741 := bbase (se 4 (by rfl) ⟨44694, by rfl⟩ : syracuseStep 476741 = 89389) (by norm_num)
theorem B2475605 : Blo 315835 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B476765 : Blo 315835 476765 := bbase (se 3 (by rfl) ⟨89393, by rfl⟩ : syracuseStep 476765 = 178787) (by norm_num)
theorem B476789 : Blo 315835 476789 := bbase (se 5 (by rfl) ⟨22349, by rfl⟩ : syracuseStep 476789 = 44699) (by norm_num)
theorem B476813 : Blo 315835 476813 := bbase (se 3 (by rfl) ⟨89402, by rfl⟩ : syracuseStep 476813 = 178805) (by norm_num)
theorem B1066661 : Blo 315835 1066661 := bbase (se 4 (by rfl) ⟨99999, by rfl⟩ : syracuseStep 1066661 = 199999) (by norm_num)
theorem B902821 : Blo 315835 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B476837 : Blo 315835 476837 := bbase (se 4 (by rfl) ⟨44703, by rfl⟩ : syracuseStep 476837 = 89407) (by norm_num)
theorem B1296037 : Blo 315835 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B476861 : Blo 315835 476861 := bbase (se 3 (by rfl) ⟨89411, by rfl⟩ : syracuseStep 476861 = 178823) (by norm_num)
theorem B476885 : Blo 315835 476885 := bbase (se 7 (by rfl) ⟨5588, by rfl⟩ : syracuseStep 476885 = 11177) (by norm_num)
theorem B476909 : Blo 315835 476909 := bbase (se 3 (by rfl) ⟨89420, by rfl⟩ : syracuseStep 476909 = 178841) (by norm_num)
theorem B804613 : Blo 315835 804613 := bbase (se 4 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 804613 = 150865) (by norm_num)
theorem B476933 : Blo 315835 476933 := bbase (se 4 (by rfl) ⟨44712, by rfl⟩ : syracuseStep 476933 = 89425) (by norm_num)
theorem B476957 : Blo 315835 476957 := bbase (se 3 (by rfl) ⟨89429, by rfl⟩ : syracuseStep 476957 = 178859) (by norm_num)
theorem B476981 : Blo 315835 476981 := bbase (se 5 (by rfl) ⟨22358, by rfl⟩ : syracuseStep 476981 = 44717) (by norm_num)
theorem B1361717 : Blo 315835 1361717 := bbase (se 5 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 1361717 = 127661) (by norm_num)
theorem B902981 : Blo 315835 902981 := bbase (se 4 (by rfl) ⟨84654, by rfl⟩ : syracuseStep 902981 = 169309) (by norm_num)
theorem B477005 : Blo 315835 477005 := bbase (se 3 (by rfl) ⟨89438, by rfl⟩ : syracuseStep 477005 = 178877) (by norm_num)
theorem B477029 : Blo 315835 477029 := bbase (se 4 (by rfl) ⟨44721, by rfl⟩ : syracuseStep 477029 = 89443) (by norm_num)
theorem B804725 : Blo 315835 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B477053 : Blo 315835 477053 := bbase (se 3 (by rfl) ⟨89447, by rfl⟩ : syracuseStep 477053 = 178895) (by norm_num)
theorem B477077 : Blo 315835 477077 := bbase (se 6 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 477077 = 22363) (by norm_num)
theorem B477101 : Blo 315835 477101 := bbase (se 3 (by rfl) ⟨89456, by rfl⟩ : syracuseStep 477101 = 178913) (by norm_num)
theorem B477125 : Blo 315835 477125 := bbase (se 4 (by rfl) ⟨44730, by rfl⟩ : syracuseStep 477125 = 89461) (by norm_num)
theorem B477149 : Blo 315835 477149 := bbase (se 3 (by rfl) ⟨89465, by rfl⟩ : syracuseStep 477149 = 178931) (by norm_num)
theorem B477173 : Blo 315835 477173 := bbase (se 5 (by rfl) ⟨22367, by rfl⟩ : syracuseStep 477173 = 44735) (by norm_num)
theorem B477197 : Blo 315835 477197 := bbase (se 3 (by rfl) ⟨89474, by rfl⟩ : syracuseStep 477197 = 178949) (by norm_num)
theorem B477221 : Blo 315835 477221 := bbase (se 4 (by rfl) ⟨44739, by rfl⟩ : syracuseStep 477221 = 89479) (by norm_num)
theorem B903221 : Blo 315835 903221 := bbase (se 5 (by rfl) ⟨42338, by rfl⟩ : syracuseStep 903221 = 84677) (by norm_num)
theorem B804917 : Blo 315835 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B477245 : Blo 315835 477245 := bbase (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) (by norm_num)
theorem B1067093 : Blo 315835 1067093 := bbase (se 8 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 1067093 = 12505) (by norm_num)
theorem B477269 : Blo 315835 477269 := bbase (se 8 (by rfl) ⟨2796, by rfl⟩ : syracuseStep 477269 = 5593) (by norm_num)
theorem B477293 : Blo 315835 477293 := bbase (se 3 (by rfl) ⟨89492, by rfl⟩ : syracuseStep 477293 = 178985) (by norm_num)
theorem B477317 : Blo 315835 477317 := bbase (se 4 (by rfl) ⟨44748, by rfl⟩ : syracuseStep 477317 = 89497) (by norm_num)
theorem B477341 : Blo 315835 477341 := bbase (se 3 (by rfl) ⟨89501, by rfl⟩ : syracuseStep 477341 = 179003) (by norm_num)
theorem B477365 : Blo 315835 477365 := bbase (se 5 (by rfl) ⟨22376, by rfl⟩ : syracuseStep 477365 = 44753) (by norm_num)
theorem B477389 : Blo 315835 477389 := bbase (se 3 (by rfl) ⟨89510, by rfl⟩ : syracuseStep 477389 = 179021) (by norm_num)
theorem B477413 : Blo 315835 477413 := bbase (se 4 (by rfl) ⟨44757, by rfl⟩ : syracuseStep 477413 = 89515) (by norm_num)
theorem B903413 : Blo 315835 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B477437 : Blo 315835 477437 := bbase (se 3 (by rfl) ⟨89519, by rfl⟩ : syracuseStep 477437 = 179039) (by norm_num)
theorem B510221 : Blo 315835 510221 := bbase (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) (by norm_num)
theorem B477461 : Blo 315835 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B477485 : Blo 315835 477485 := bbase (se 3 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 477485 = 179057) (by norm_num)
theorem B477509 : Blo 315835 477509 := bbase (se 4 (by rfl) ⟨44766, by rfl⟩ : syracuseStep 477509 = 89533) (by norm_num)
theorem B477533 : Blo 315835 477533 := bbase (se 3 (by rfl) ⟨89537, by rfl⟩ : syracuseStep 477533 = 179075) (by norm_num)
theorem B477557 : Blo 315835 477557 := bbase (se 5 (by rfl) ⟨22385, by rfl⟩ : syracuseStep 477557 = 44771) (by norm_num)
theorem B805261 : Blo 315835 805261 := bbase (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) (by norm_num)
theorem B477581 : Blo 315835 477581 := bbase (se 3 (by rfl) ⟨89546, by rfl⟩ : syracuseStep 477581 = 179093) (by norm_num)
theorem B477605 : Blo 315835 477605 := bbase (se 4 (by rfl) ⟨44775, by rfl⟩ : syracuseStep 477605 = 89551) (by norm_num)
theorem B477629 : Blo 315835 477629 := bbase (se 3 (by rfl) ⟨89555, by rfl⟩ : syracuseStep 477629 = 179111) (by norm_num)
theorem B477653 : Blo 315835 477653 := bbase (se 7 (by rfl) ⟨5597, by rfl⟩ : syracuseStep 477653 = 11195) (by norm_num)
theorem B477677 : Blo 315835 477677 := bbase (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) (by norm_num)
theorem B805373 : Blo 315835 805373 := bbase (se 3 (by rfl) ⟨151007, by rfl⟩ : syracuseStep 805373 = 302015) (by norm_num)
theorem B1067525 : Blo 315835 1067525 := bbase (se 4 (by rfl) ⟨100080, by rfl⟩ : syracuseStep 1067525 = 200161) (by norm_num)
theorem B477701 : Blo 315835 477701 := bbase (se 4 (by rfl) ⟨44784, by rfl⟩ : syracuseStep 477701 = 89569) (by norm_num)
theorem B477725 : Blo 315835 477725 := bbase (se 3 (by rfl) ⟨89573, by rfl⟩ : syracuseStep 477725 = 179147) (by norm_num)
theorem B477749 : Blo 315835 477749 := bbase (se 5 (by rfl) ⟨22394, by rfl⟩ : syracuseStep 477749 = 44789) (by norm_num)
theorem B477773 : Blo 315835 477773 := bbase (se 3 (by rfl) ⟨89582, by rfl⟩ : syracuseStep 477773 = 179165) (by norm_num)
theorem B477797 : Blo 315835 477797 := bbase (se 4 (by rfl) ⟨44793, by rfl⟩ : syracuseStep 477797 = 89587) (by norm_num)
theorem B477821 : Blo 315835 477821 := bbase (se 3 (by rfl) ⟨89591, by rfl⟩ : syracuseStep 477821 = 179183) (by norm_num)
theorem B477845 : Blo 315835 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B477869 : Blo 315835 477869 := bbase (se 3 (by rfl) ⟨89600, by rfl⟩ : syracuseStep 477869 = 179201) (by norm_num)
theorem B805565 : Blo 315835 805565 := bbase (se 3 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 805565 = 302087) (by norm_num)
theorem B477893 : Blo 315835 477893 := bbase (se 4 (by rfl) ⟨44802, by rfl⟩ : syracuseStep 477893 = 89605) (by norm_num)
theorem B477917 : Blo 315835 477917 := bbase (se 3 (by rfl) ⟨89609, by rfl⟩ : syracuseStep 477917 = 179219) (by norm_num)
theorem B477941 : Blo 315835 477941 := bbase (se 5 (by rfl) ⟨22403, by rfl⟩ : syracuseStep 477941 = 44807) (by norm_num)
theorem B477965 : Blo 315835 477965 := bbase (se 3 (by rfl) ⟨89618, by rfl⟩ : syracuseStep 477965 = 179237) (by norm_num)
theorem B510733 : Blo 315835 510733 := bbase (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) (by norm_num)
theorem B477989 : Blo 315835 477989 := bbase (se 4 (by rfl) ⟨44811, by rfl⟩ : syracuseStep 477989 = 89623) (by norm_num)
theorem B478013 : Blo 315835 478013 := bbase (se 3 (by rfl) ⟨89627, by rfl⟩ : syracuseStep 478013 = 179255) (by norm_num)
theorem B478037 : Blo 315835 478037 := bbase (se 9 (by rfl) ⟨1400, by rfl⟩ : syracuseStep 478037 = 2801) (by norm_num)
theorem B478061 : Blo 315835 478061 := bbase (se 3 (by rfl) ⟨89636, by rfl⟩ : syracuseStep 478061 = 179273) (by norm_num)
theorem B478085 : Blo 315835 478085 := bbase (se 4 (by rfl) ⟨44820, by rfl⟩ : syracuseStep 478085 = 89641) (by norm_num)
theorem B478109 : Blo 315835 478109 := bbase (se 3 (by rfl) ⟨89645, by rfl⟩ : syracuseStep 478109 = 179291) (by norm_num)
theorem B1067957 : Blo 315835 1067957 := bbase (se 5 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 1067957 = 100121) (by norm_num)
theorem B478133 : Blo 315835 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B478157 : Blo 315835 478157 := bbase (se 3 (by rfl) ⟨89654, by rfl⟩ : syracuseStep 478157 = 179309) (by norm_num)
theorem B478181 : Blo 315835 478181 := bbase (se 4 (by rfl) ⟨44829, by rfl⟩ : syracuseStep 478181 = 89659) (by norm_num)
theorem B478205 : Blo 315835 478205 := bbase (se 3 (by rfl) ⟨89663, by rfl⟩ : syracuseStep 478205 = 179327) (by norm_num)
theorem B805909 : Blo 315835 805909 := bbase (se 6 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 805909 = 37777) (by norm_num)
theorem B478229 : Blo 315835 478229 := bbase (se 6 (by rfl) ⟨11208, by rfl⟩ : syracuseStep 478229 = 22417) (by norm_num)
theorem B478253 : Blo 315835 478253 := bbase (se 3 (by rfl) ⟨89672, by rfl⟩ : syracuseStep 478253 = 179345) (by norm_num)
theorem B478277 : Blo 315835 478277 := bbase (se 4 (by rfl) ⟨44838, by rfl⟩ : syracuseStep 478277 = 89677) (by norm_num)
theorem B478301 : Blo 315835 478301 := bbase (se 3 (by rfl) ⟨89681, by rfl⟩ : syracuseStep 478301 = 179363) (by norm_num)
theorem B478325 : Blo 315835 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B806021 : Blo 315835 806021 := bbase (se 4 (by rfl) ⟨75564, by rfl⟩ : syracuseStep 806021 = 151129) (by norm_num)
theorem B478349 : Blo 315835 478349 := bbase (se 3 (by rfl) ⟨89690, by rfl⟩ : syracuseStep 478349 = 179381) (by norm_num)
theorem B642197 : Blo 315835 642197 := bbase (se 6 (by rfl) ⟨15051, by rfl⟩ : syracuseStep 642197 = 30103) (by norm_num)
theorem B478373 : Blo 315835 478373 := bbase (se 4 (by rfl) ⟨44847, by rfl⟩ : syracuseStep 478373 = 89695) (by norm_num)
theorem B478397 : Blo 315835 478397 := bbase (se 3 (by rfl) ⟨89699, by rfl⟩ : syracuseStep 478397 = 179399) (by norm_num)
theorem B904405 : Blo 315835 904405 := bbase (se 7 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 904405 = 21197) (by norm_num)
theorem B478421 : Blo 315835 478421 := bbase (se 7 (by rfl) ⟨5606, by rfl⟩ : syracuseStep 478421 = 11213) (by norm_num)
theorem B478445 : Blo 315835 478445 := bbase (se 3 (by rfl) ⟨89708, by rfl⟩ : syracuseStep 478445 = 179417) (by norm_num)
theorem B478469 : Blo 315835 478469 := bbase (se 4 (by rfl) ⟨44856, by rfl⟩ : syracuseStep 478469 = 89713) (by norm_num)
theorem B478493 : Blo 315835 478493 := bbase (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) (by norm_num)
theorem B478517 : Blo 315835 478517 := bbase (se 5 (by rfl) ⟨22430, by rfl⟩ : syracuseStep 478517 = 44861) (by norm_num)
theorem B806213 : Blo 315835 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B478541 : Blo 315835 478541 := bbase (se 3 (by rfl) ⟨89726, by rfl⟩ : syracuseStep 478541 = 179453) (by norm_num)
theorem B544085 : Blo 315835 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B1068389 : Blo 315835 1068389 := bbase (se 4 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 1068389 = 200323) (by norm_num)
theorem B478565 : Blo 315835 478565 := bbase (se 4 (by rfl) ⟨44865, by rfl⟩ : syracuseStep 478565 = 89731) (by norm_num)
theorem B478589 : Blo 315835 478589 := bbase (se 3 (by rfl) ⟨89735, by rfl⟩ : syracuseStep 478589 = 179471) (by norm_num)
theorem B478613 : Blo 315835 478613 := bbase (se 6 (by rfl) ⟨11217, by rfl⟩ : syracuseStep 478613 = 22435) (by norm_num)
theorem B675229 : Blo 315835 675229 := bbase (se 3 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 675229 = 253211) (by norm_num)
theorem B478637 : Blo 315835 478637 := bbase (se 3 (by rfl) ⟨89744, by rfl⟩ : syracuseStep 478637 = 179489) (by norm_num)
theorem B478661 : Blo 315835 478661 := bbase (se 4 (by rfl) ⟨44874, by rfl⟩ : syracuseStep 478661 = 89749) (by norm_num)
theorem B478685 : Blo 315835 478685 := bbase (se 3 (by rfl) ⟨89753, by rfl⟩ : syracuseStep 478685 = 179507) (by norm_num)
theorem B478709 : Blo 315835 478709 := bbase (se 5 (by rfl) ⟨22439, by rfl⟩ : syracuseStep 478709 = 44879) (by norm_num)
theorem B478733 : Blo 315835 478733 := bbase (se 3 (by rfl) ⟨89762, by rfl⟩ : syracuseStep 478733 = 179525) (by norm_num)
theorem B478757 : Blo 315835 478757 := bbase (se 4 (by rfl) ⟨44883, by rfl⟩ : syracuseStep 478757 = 89767) (by norm_num)
theorem B1363493 : Blo 315835 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B675373 : Blo 315835 675373 := bbase (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) (by norm_num)
theorem B478781 : Blo 315835 478781 := bbase (se 3 (by rfl) ⟨89771, by rfl⟩ : syracuseStep 478781 = 179543) (by norm_num)
theorem B478805 : Blo 315835 478805 := bbase (se 8 (by rfl) ⟨2805, by rfl⟩ : syracuseStep 478805 = 5611) (by norm_num)
theorem B478829 : Blo 315835 478829 := bbase (se 3 (by rfl) ⟨89780, by rfl⟩ : syracuseStep 478829 = 179561) (by norm_num)
theorem B478853 : Blo 315835 478853 := bbase (se 4 (by rfl) ⟨44892, by rfl⟩ : syracuseStep 478853 = 89785) (by norm_num)
theorem B806557 : Blo 315835 806557 := bbase (se 3 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 806557 = 302459) (by norm_num)
theorem B478877 : Blo 315835 478877 := bbase (se 3 (by rfl) ⟨89789, by rfl⟩ : syracuseStep 478877 = 179579) (by norm_num)
theorem B478901 : Blo 315835 478901 := bbase (se 5 (by rfl) ⟨22448, by rfl⟩ : syracuseStep 478901 = 44897) (by norm_num)
theorem B478925 : Blo 315835 478925 := bbase (se 3 (by rfl) ⟨89798, by rfl⟩ : syracuseStep 478925 = 179597) (by norm_num)
theorem B478949 : Blo 315835 478949 := bbase (se 4 (by rfl) ⟨44901, by rfl⟩ : syracuseStep 478949 = 89803) (by norm_num)
theorem B511733 : Blo 315835 511733 := bbase (se 5 (by rfl) ⟨23987, by rfl⟩ : syracuseStep 511733 = 47975) (by norm_num)
theorem B478973 : Blo 315835 478973 := bbase (se 3 (by rfl) ⟨89807, by rfl⟩ : syracuseStep 478973 = 179615) (by norm_num)
theorem B806669 : Blo 315835 806669 := bbase (se 3 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 806669 = 302501) (by norm_num)
theorem B1068821 : Blo 315835 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B478997 : Blo 315835 478997 := bbase (se 6 (by rfl) ⟨11226, by rfl⟩ : syracuseStep 478997 = 22453) (by norm_num)
theorem B380705 : Blo 315835 380705 := bbase (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) (by norm_num)
theorem B479021 : Blo 315835 479021 := bbase (se 3 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 479021 = 179633) (by norm_num)
theorem B479045 : Blo 315835 479045 := bbase (se 4 (by rfl) ⟨44910, by rfl⟩ : syracuseStep 479045 = 89821) (by norm_num)
theorem B479069 : Blo 315835 479069 := bbase (se 3 (by rfl) ⟨89825, by rfl⟩ : syracuseStep 479069 = 179651) (by norm_num)
theorem B2576245 : Blo 315835 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B479093 : Blo 315835 479093 := bbase (se 5 (by rfl) ⟨22457, by rfl⟩ : syracuseStep 479093 = 44915) (by norm_num)
theorem B511861 : Blo 315835 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B479117 : Blo 315835 479117 := bbase (se 3 (by rfl) ⟨89834, by rfl⟩ : syracuseStep 479117 = 179669) (by norm_num)
theorem B675749 : Blo 315835 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B479141 : Blo 315835 479141 := bbase (se 4 (by rfl) ⟨44919, by rfl⟩ : syracuseStep 479141 = 89839) (by norm_num)
theorem B511925 : Blo 315835 511925 := bbase (se 5 (by rfl) ⟨23996, by rfl⟩ : syracuseStep 511925 = 47993) (by norm_num)
theorem B479165 : Blo 315835 479165 := bbase (se 3 (by rfl) ⟨89843, by rfl⟩ : syracuseStep 479165 = 179687) (by norm_num)
theorem B806861 : Blo 315835 806861 := bbase (se 3 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 806861 = 302573) (by norm_num)
theorem B479189 : Blo 315835 479189 := bbase (se 7 (by rfl) ⟨5615, by rfl⟩ : syracuseStep 479189 = 11231) (by norm_num)
theorem B479213 : Blo 315835 479213 := bbase (se 3 (by rfl) ⟨89852, by rfl⟩ : syracuseStep 479213 = 179705) (by norm_num)
theorem B479237 : Blo 315835 479237 := bbase (se 4 (by rfl) ⟨44928, by rfl⟩ : syracuseStep 479237 = 89857) (by norm_num)
theorem B577565 : Blo 315835 577565 := bbase (se 3 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 577565 = 216587) (by norm_num)
theorem B479261 : Blo 315835 479261 := bbase (se 3 (by rfl) ⟨89861, by rfl⟩ : syracuseStep 479261 = 179723) (by norm_num)
theorem B479285 : Blo 315835 479285 := bbase (se 5 (by rfl) ⟨22466, by rfl⟩ : syracuseStep 479285 = 44933) (by norm_num)
theorem B479309 : Blo 315835 479309 := bbase (se 3 (by rfl) ⟨89870, by rfl⟩ : syracuseStep 479309 = 179741) (by norm_num)
theorem B479333 : Blo 315835 479333 := bbase (se 4 (by rfl) ⟨44937, by rfl⟩ : syracuseStep 479333 = 89875) (by norm_num)
theorem B479357 : Blo 315835 479357 := bbase (se 3 (by rfl) ⟨89879, by rfl⟩ : syracuseStep 479357 = 179759) (by norm_num)
theorem B774293 : Blo 315835 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B479381 : Blo 315835 479381 := bbase (se 6 (by rfl) ⟨11235, by rfl⟩ : syracuseStep 479381 = 22471) (by norm_num)
theorem B479405 : Blo 315835 479405 := bbase (se 3 (by rfl) ⟨89888, by rfl⟩ : syracuseStep 479405 = 179777) (by norm_num)
theorem B1069253 : Blo 315835 1069253 := bbase (se 4 (by rfl) ⟨100242, by rfl⟩ : syracuseStep 1069253 = 200485) (by norm_num)
theorem B479429 : Blo 315835 479429 := bbase (se 4 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 479429 = 89893) (by norm_num)
theorem B479453 : Blo 315835 479453 := bbase (se 3 (by rfl) ⟨89897, by rfl⟩ : syracuseStep 479453 = 179795) (by norm_num)
theorem B479477 : Blo 315835 479477 := bbase (se 5 (by rfl) ⟨22475, by rfl⟩ : syracuseStep 479477 = 44951) (by norm_num)
theorem B479501 : Blo 315835 479501 := bbase (se 3 (by rfl) ⟨89906, by rfl⟩ : syracuseStep 479501 = 179813) (by norm_num)
theorem B676117 : Blo 315835 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B905509 : Blo 315835 905509 := bbase (se 4 (by rfl) ⟨84891, by rfl⟩ : syracuseStep 905509 = 169783) (by norm_num)
theorem B807205 : Blo 315835 807205 := bbase (se 4 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 807205 = 151351) (by norm_num)
theorem B479525 : Blo 315835 479525 := bbase (se 4 (by rfl) ⟨44955, by rfl⟩ : syracuseStep 479525 = 89911) (by norm_num)
theorem B479549 : Blo 315835 479549 := bbase (se 3 (by rfl) ⟨89915, by rfl⟩ : syracuseStep 479549 = 179831) (by norm_num)
theorem B479573 : Blo 315835 479573 := bbase (se 10 (by rfl) ⟨702, by rfl⟩ : syracuseStep 479573 = 1405) (by norm_num)
theorem B479597 : Blo 315835 479597 := bbase (se 3 (by rfl) ⟨89924, by rfl⟩ : syracuseStep 479597 = 179849) (by norm_num)
theorem B479621 : Blo 315835 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B807317 : Blo 315835 807317 := bbase (se 6 (by rfl) ⟨18921, by rfl⟩ : syracuseStep 807317 = 37843) (by norm_num)
theorem B479645 : Blo 315835 479645 := bbase (se 3 (by rfl) ⟨89933, by rfl⟩ : syracuseStep 479645 = 179867) (by norm_num)
theorem B479669 : Blo 315835 479669 := bbase (se 5 (by rfl) ⟨22484, by rfl⟩ : syracuseStep 479669 = 44969) (by norm_num)
theorem B479693 : Blo 315835 479693 := bbase (se 3 (by rfl) ⟨89942, by rfl⟩ : syracuseStep 479693 = 179885) (by norm_num)
theorem B381397 : Blo 315835 381397 := bbase (se 7 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 381397 = 8939) (by norm_num)
theorem B479717 : Blo 315835 479717 := bbase (se 4 (by rfl) ⟨44973, by rfl⟩ : syracuseStep 479717 = 89947) (by norm_num)
theorem B479741 : Blo 315835 479741 := bbase (se 3 (by rfl) ⟨89951, by rfl⟩ : syracuseStep 479741 = 179903) (by norm_num)
theorem B381493 : Blo 315835 381493 := bbase (se 5 (by rfl) ⟨17882, by rfl⟩ : syracuseStep 381493 = 35765) (by norm_num)
theorem B545357 : Blo 315835 545357 := bbase (se 3 (by rfl) ⟨102254, by rfl⟩ : syracuseStep 545357 = 204509) (by norm_num)
theorem B807509 : Blo 315835 807509 := bbase (se 8 (by rfl) ⟨4731, by rfl⟩ : syracuseStep 807509 = 9463) (by norm_num)
theorem B1069685 : Blo 315835 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B447293 : Blo 315835 447293 := bbase (se 3 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 447293 = 167735) (by norm_num)
theorem B1528645 : Blo 315835 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B1201013 : Blo 315835 1201013 := bbase (se 5 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 1201013 = 112595) (by norm_num)
theorem B709517 : Blo 315835 709517 := bbase (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) (by norm_num)
theorem B807853 : Blo 315835 807853 := bbase (se 3 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 807853 = 302945) (by norm_num)
theorem B349177 : Blo 315835 349177 := bbase (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) (by norm_num)
theorem B807965 : Blo 315835 807965 := bbase (se 3 (by rfl) ⟨151493, by rfl⟩ : syracuseStep 807965 = 302987) (by norm_num)
theorem B1070117 : Blo 315835 1070117 := bbase (se 4 (by rfl) ⟨100323, by rfl⟩ : syracuseStep 1070117 = 200647) (by norm_num)
theorem B1201301 : Blo 315835 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B808157 : Blo 315835 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B382277 : Blo 315835 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B1070549 : Blo 315835 1070549 := bbase (se 7 (by rfl) ⟨12545, by rfl⟩ : syracuseStep 1070549 = 25091) (by norm_num)
theorem B480821 : Blo 315835 480821 := bbase (se 5 (by rfl) ⟨22538, by rfl⟩ : syracuseStep 480821 = 45077) (by norm_num)
theorem B808501 : Blo 315835 808501 := bbase (se 5 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 808501 = 75797) (by norm_num)
theorem B382585 : Blo 315835 382585 := bbase (se 2 (by rfl) ⟨143469, by rfl⟩ : syracuseStep 382585 = 286939) (by norm_num)
theorem B808613 : Blo 315835 808613 := bbase (se 4 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 808613 = 151615) (by norm_num)
theorem B677621 : Blo 315835 677621 := bbase (se 5 (by rfl) ⟨31763, by rfl⟩ : syracuseStep 677621 = 63527) (by norm_num)
theorem B907013 : Blo 315835 907013 := bbase (se 4 (by rfl) ⟨85032, by rfl⟩ : syracuseStep 907013 = 170065) (by norm_num)
theorem B808805 : Blo 315835 808805 := bbase (se 4 (by rfl) ⟨75825, by rfl⟩ : syracuseStep 808805 = 151651) (by norm_num)
theorem B1070981 : Blo 315835 1070981 := bbase (se 4 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 1070981 = 200809) (by norm_num)
theorem B677765 : Blo 315835 677765 := bbase (se 4 (by rfl) ⟨63540, by rfl⟩ : syracuseStep 677765 = 127081) (by norm_num)
theorem B350125 : Blo 315835 350125 := bbase (se 3 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 350125 = 131297) (by norm_num)
theorem B382973 : Blo 315835 382973 := bbase (se 3 (by rfl) ⟨71807, by rfl⟩ : syracuseStep 382973 = 143615) (by norm_num)
theorem B710693 : Blo 315835 710693 := bbase (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) (by norm_num)
theorem B2709557 : Blo 315835 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B710765 : Blo 315835 710765 := bbase (se 3 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 710765 = 266537) (by norm_num)
theorem B546925 : Blo 315835 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B3037333 : Blo 315835 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B710837 : Blo 315835 710837 := bbase (se 5 (by rfl) ⟨33320, by rfl⟩ : syracuseStep 710837 = 66641) (by norm_num)
theorem B809149 : Blo 315835 809149 := bbase (se 3 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 809149 = 303431) (by norm_num)
theorem B678125 : Blo 315835 678125 := bbase (se 3 (by rfl) ⟨127148, by rfl⟩ : syracuseStep 678125 = 254297) (by norm_num)
theorem B710909 : Blo 315835 710909 := bbase (se 3 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 710909 = 266591) (by norm_num)
theorem B809261 : Blo 315835 809261 := bbase (se 3 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 809261 = 303473) (by norm_num)
theorem B1202485 : Blo 315835 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B1071413 : Blo 315835 1071413 := bbase (se 5 (by rfl) ⟨50222, by rfl⟩ : syracuseStep 1071413 = 100445) (by norm_num)
theorem B710981 : Blo 315835 710981 := bbase (se 4 (by rfl) ⟨66654, by rfl⟩ : syracuseStep 710981 = 133309) (by norm_num)
theorem B2414933 : Blo 315835 2414933 := bbase (se 10 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 2414933 = 7075) (by norm_num)
theorem B383329 : Blo 315835 383329 := bbase (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) (by norm_num)
theorem B711053 : Blo 315835 711053 := bbase (se 3 (by rfl) ⟨133322, by rfl⟩ : syracuseStep 711053 = 266645) (by norm_num)
theorem B612805 : Blo 315835 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B711125 : Blo 315835 711125 := bbase (se 7 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 711125 = 16667) (by norm_num)
theorem B809453 : Blo 315835 809453 := bbase (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) (by norm_num)
theorem B481781 : Blo 315835 481781 := bbase (se 5 (by rfl) ⟨22583, by rfl⟩ : syracuseStep 481781 = 45167) (by norm_num)
theorem B711197 : Blo 315835 711197 := bbase (se 3 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 711197 = 266699) (by norm_num)
theorem B711269 : Blo 315835 711269 := bbase (se 4 (by rfl) ⟨66681, by rfl⟩ : syracuseStep 711269 = 133363) (by norm_num)
theorem B1202789 : Blo 315835 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B940709 : Blo 315835 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B711341 : Blo 315835 711341 := bbase (se 3 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 711341 = 266753) (by norm_num)
theorem B383665 : Blo 315835 383665 := bbase (se 2 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 383665 = 287749) (by norm_num)
theorem B1071845 : Blo 315835 1071845 := bbase (se 4 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 1071845 = 200971) (by norm_num)
theorem B711413 : Blo 315835 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B711485 : Blo 315835 711485 := bbase (se 3 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 711485 = 266807) (by norm_num)
theorem B711557 : Blo 315835 711557 := bbase (se 4 (by rfl) ⟨66708, by rfl⟩ : syracuseStep 711557 = 133417) (by norm_num)
theorem B711629 : Blo 315835 711629 := bbase (se 3 (by rfl) ⟨133430, by rfl⟩ : syracuseStep 711629 = 266861) (by norm_num)
theorem B711701 : Blo 315835 711701 := bbase (se 6 (by rfl) ⟨16680, by rfl⟩ : syracuseStep 711701 = 33361) (by norm_num)
theorem B5463125 : Blo 315835 5463125 := bbase (se 8 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 5463125 = 64021) (by norm_num)
theorem B711773 : Blo 315835 711773 := bbase (se 3 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 711773 = 266915) (by norm_num)
theorem B679013 : Blo 315835 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B1072277 : Blo 315835 1072277 := bbase (se 6 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 1072277 = 50263) (by norm_num)
theorem B711845 : Blo 315835 711845 := bbase (se 4 (by rfl) ⟨66735, by rfl⟩ : syracuseStep 711845 = 133471) (by norm_num)
theorem B449725 : Blo 315835 449725 := bbase (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) (by norm_num)
theorem B711917 : Blo 315835 711917 := bbase (se 3 (by rfl) ⟨133484, by rfl⟩ : syracuseStep 711917 = 266969) (by norm_num)
theorem B711989 : Blo 315835 711989 := bbase (se 5 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 711989 = 66749) (by norm_num)
theorem B908597 : Blo 315835 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B15621461 : Blo 315835 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B679261 : Blo 315835 679261 := bbase (se 3 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 679261 = 254723) (by norm_num)
theorem B712061 : Blo 315835 712061 := bbase (se 3 (by rfl) ⟨133511, by rfl⟩ : syracuseStep 712061 = 267023) (by norm_num)
theorem B482701 : Blo 315835 482701 := bbase (se 3 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 482701 = 181013) (by norm_num)
theorem B712133 : Blo 315835 712133 := bbase (se 4 (by rfl) ⟨66762, by rfl⟩ : syracuseStep 712133 = 133525) (by norm_num)
theorem B712205 : Blo 315835 712205 := bbase (se 3 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 712205 = 267077) (by norm_num)
theorem B1072709 : Blo 315835 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B712277 : Blo 315835 712277 := bbase (se 8 (by rfl) ⟨4173, by rfl⟩ : syracuseStep 712277 = 8347) (by norm_num)
theorem B712349 : Blo 315835 712349 := bbase (se 3 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 712349 = 267131) (by norm_num)
theorem B712421 : Blo 315835 712421 := bbase (se 4 (by rfl) ⟨66789, by rfl⟩ : syracuseStep 712421 = 133579) (by norm_num)
theorem B450317 : Blo 315835 450317 := bbase (se 3 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 450317 = 168869) (by norm_num)
theorem B712493 : Blo 315835 712493 := bbase (se 3 (by rfl) ⟨133592, by rfl⟩ : syracuseStep 712493 = 267185) (by norm_num)
theorem B614189 : Blo 315835 614189 := bbase (se 3 (by rfl) ⟨115160, by rfl⟩ : syracuseStep 614189 = 230321) (by norm_num)
theorem B679765 : Blo 315835 679765 := bbase (se 9 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 679765 = 3983) (by norm_num)
theorem B450397 : Blo 315835 450397 := bbase (se 3 (by rfl) ⟨84449, by rfl⟩ : syracuseStep 450397 = 168899) (by norm_num)
theorem B712565 : Blo 315835 712565 := bbase (se 5 (by rfl) ⟨33401, by rfl⟩ : syracuseStep 712565 = 66803) (by norm_num)
theorem B712637 : Blo 315835 712637 := bbase (se 3 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 712637 = 267239) (by norm_num)
theorem B450517 : Blo 315835 450517 := bbase (se 7 (by rfl) ⟨5279, by rfl⟩ : syracuseStep 450517 = 10559) (by norm_num)
theorem B909269 : Blo 315835 909269 := bbase (se 7 (by rfl) ⟨10655, by rfl⟩ : syracuseStep 909269 = 21311) (by norm_num)
theorem B1073141 : Blo 315835 1073141 := bbase (se 5 (by rfl) ⟨50303, by rfl⟩ : syracuseStep 1073141 = 100607) (by norm_num)
theorem B712709 : Blo 315835 712709 := bbase (se 4 (by rfl) ⟨66816, by rfl⟩ : syracuseStep 712709 = 133633) (by norm_num)
theorem B450613 : Blo 315835 450613 := bbase (se 5 (by rfl) ⟨21122, by rfl⟩ : syracuseStep 450613 = 42245) (by norm_num)
theorem B712781 : Blo 315835 712781 := bbase (se 3 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 712781 = 267293) (by norm_num)
theorem B1368197 : Blo 315835 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B712853 : Blo 315835 712853 := bbase (se 6 (by rfl) ⟨16707, by rfl⟩ : syracuseStep 712853 = 33415) (by norm_num)
theorem B712925 : Blo 315835 712925 := bbase (se 3 (by rfl) ⟨133673, by rfl⟩ : syracuseStep 712925 = 267347) (by norm_num)
theorem B614621 : Blo 315835 614621 := bbase (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) (by norm_num)
theorem B1138933 : Blo 315835 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B712997 : Blo 315835 712997 := bbase (se 4 (by rfl) ⟨66843, by rfl⟩ : syracuseStep 712997 = 133687) (by norm_num)
theorem B713069 : Blo 315835 713069 := bbase (se 3 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 713069 = 267401) (by norm_num)
theorem B909701 : Blo 315835 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B1073573 : Blo 315835 1073573 := bbase (se 4 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 1073573 = 201295) (by norm_num)
theorem B713141 : Blo 315835 713141 := bbase (se 5 (by rfl) ⟨33428, by rfl⟩ : syracuseStep 713141 = 66857) (by norm_num)
theorem B713213 : Blo 315835 713213 := bbase (se 3 (by rfl) ⟨133727, by rfl⟩ : syracuseStep 713213 = 267455) (by norm_num)
theorem B451109 : Blo 315835 451109 := bbase (se 4 (by rfl) ⟨42291, by rfl⟩ : syracuseStep 451109 = 84583) (by norm_num)
theorem B713285 : Blo 315835 713285 := bbase (se 4 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 713285 = 133741) (by norm_num)
theorem B516709 : Blo 315835 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B713357 : Blo 315835 713357 := bbase (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) (by norm_num)
theorem B1204901 : Blo 315835 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B680653 : Blo 315835 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B713429 : Blo 315835 713429 := bbase (se 7 (by rfl) ⟨8360, by rfl⟩ : syracuseStep 713429 = 16721) (by norm_num)
theorem B713501 : Blo 315835 713501 := bbase (se 3 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 713501 = 267563) (by norm_num)
theorem B648013 : Blo 315835 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B1074005 : Blo 315835 1074005 := bbase (se 9 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 1074005 = 6293) (by norm_num)
theorem B713573 : Blo 315835 713573 := bbase (se 4 (by rfl) ⟨66897, by rfl⟩ : syracuseStep 713573 = 133795) (by norm_num)
theorem B615269 : Blo 315835 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B713645 : Blo 315835 713645 := bbase (se 3 (by rfl) ⟨133808, by rfl⟩ : syracuseStep 713645 = 267617) (by norm_num)
theorem B1205189 : Blo 315835 1205189 := bbase (se 4 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 1205189 = 225973) (by norm_num)
theorem B385997 : Blo 315835 385997 := bbase (se 3 (by rfl) ⟨72374, by rfl⟩ : syracuseStep 385997 = 144749) (by norm_num)
theorem B713717 : Blo 315835 713717 := bbase (se 5 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 713717 = 66911) (by norm_num)
theorem B484373 : Blo 315835 484373 := bbase (se 6 (by rfl) ⟨11352, by rfl⟩ : syracuseStep 484373 = 22705) (by norm_num)
theorem B713789 : Blo 315835 713789 := bbase (se 3 (by rfl) ⟨133835, by rfl⟩ : syracuseStep 713789 = 267671) (by norm_num)
theorem B451661 : Blo 315835 451661 := bbase (se 3 (by rfl) ⟨84686, by rfl⟩ : syracuseStep 451661 = 169373) (by norm_num)
theorem B910453 : Blo 315835 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B713861 : Blo 315835 713861 := bbase (se 4 (by rfl) ⟨66924, by rfl⟩ : syracuseStep 713861 = 133849) (by norm_num)
theorem B681149 : Blo 315835 681149 := bbase (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) (by norm_num)
theorem B713933 : Blo 315835 713933 := bbase (se 3 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 713933 = 267725) (by norm_num)
theorem B1074437 : Blo 315835 1074437 := bbase (se 4 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 1074437 = 201457) (by norm_num)
theorem B714005 : Blo 315835 714005 := bbase (se 6 (by rfl) ⟨16734, by rfl⟩ : syracuseStep 714005 = 33469) (by norm_num)
theorem B582941 : Blo 315835 582941 := bbase (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) (by norm_num)
theorem B714077 : Blo 315835 714077 := bbase (se 3 (by rfl) ⟨133889, by rfl⟩ : syracuseStep 714077 = 267779) (by norm_num)
theorem B714149 : Blo 315835 714149 := bbase (se 4 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 714149 = 133903) (by norm_num)
theorem B517573 : Blo 315835 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B320969 : Blo 315835 320969 := bbase (se 2 (by rfl) ⟨120363, by rfl⟩ : syracuseStep 320969 = 240727) (by norm_num)
theorem B714221 : Blo 315835 714221 := bbase (se 3 (by rfl) ⟨133916, by rfl⟩ : syracuseStep 714221 = 267833) (by norm_num)
theorem B714293 : Blo 315835 714293 := bbase (se 5 (by rfl) ⟨33482, by rfl⟩ : syracuseStep 714293 = 66965) (by norm_num)
theorem B714365 : Blo 315835 714365 := bbase (se 3 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 714365 = 267887) (by norm_num)
theorem B1074869 : Blo 315835 1074869 := bbase (se 5 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 1074869 = 100769) (by norm_num)
theorem B714437 : Blo 315835 714437 := bbase (se 4 (by rfl) ⟨66978, by rfl⟩ : syracuseStep 714437 = 133957) (by norm_num)
theorem B714509 : Blo 315835 714509 := bbase (se 3 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 714509 = 267941) (by norm_num)
theorem B452413 : Blo 315835 452413 := bbase (se 3 (by rfl) ⟨84827, by rfl⟩ : syracuseStep 452413 = 169655) (by norm_num)
theorem B714581 : Blo 315835 714581 := bbase (se 9 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 714581 = 4187) (by norm_num)
theorem B714653 : Blo 315835 714653 := bbase (se 3 (by rfl) ⟨133997, by rfl⟩ : syracuseStep 714653 = 267995) (by norm_num)
theorem B714725 : Blo 315835 714725 := bbase (se 4 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 714725 = 134011) (by norm_num)
theorem B714797 : Blo 315835 714797 := bbase (se 3 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 714797 = 268049) (by norm_num)
theorem B3041333 : Blo 315835 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B1468469 : Blo 315835 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B682037 : Blo 315835 682037 := bbase (se 5 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 682037 = 63941) (by norm_num)
theorem B2025557 : Blo 315835 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1206373 : Blo 315835 1206373 := bbase (se 4 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 1206373 = 226195) (by norm_num)
theorem B1075301 : Blo 315835 1075301 := bbase (se 4 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 1075301 = 201619) (by norm_num)
theorem B714869 : Blo 315835 714869 := bbase (se 5 (by rfl) ⟨33509, by rfl⟩ : syracuseStep 714869 = 67019) (by norm_num)
theorem B682157 : Blo 315835 682157 := bbase (se 3 (by rfl) ⟨127904, by rfl⟩ : syracuseStep 682157 = 255809) (by norm_num)
theorem B714941 : Blo 315835 714941 := bbase (se 3 (by rfl) ⟨134051, by rfl⟩ : syracuseStep 714941 = 268103) (by norm_num)
theorem B1599749 : Blo 315835 1599749 := bbase (se 4 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 1599749 = 299953) (by norm_num)
theorem B715013 : Blo 315835 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B715085 : Blo 315835 715085 := bbase (se 3 (by rfl) ⟨134078, by rfl⟩ : syracuseStep 715085 = 268157) (by norm_num)
theorem B321877 : Blo 315835 321877 := bbase (se 10 (by rfl) ⟨471, by rfl⟩ : syracuseStep 321877 = 943) (by norm_num)
theorem B1206677 : Blo 315835 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B715157 : Blo 315835 715157 := bbase (se 6 (by rfl) ⟨16761, by rfl⟩ : syracuseStep 715157 = 33523) (by norm_num)
theorem B715229 : Blo 315835 715229 := bbase (se 3 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 715229 = 268211) (by norm_num)
theorem B813581 : Blo 315835 813581 := bbase (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) (by norm_num)
theorem B1075733 : Blo 315835 1075733 := bbase (se 6 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 1075733 = 50425) (by norm_num)
theorem B715301 : Blo 315835 715301 := bbase (se 4 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 715301 = 134119) (by norm_num)
theorem B453205 : Blo 315835 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B715373 : Blo 315835 715373 := bbase (se 3 (by rfl) ⟨134132, by rfl⟩ : syracuseStep 715373 = 268265) (by norm_num)
theorem B715445 : Blo 315835 715445 := bbase (se 5 (by rfl) ⟨33536, by rfl⟩ : syracuseStep 715445 = 67073) (by norm_num)
theorem B715517 : Blo 315835 715517 := bbase (se 3 (by rfl) ⟨134159, by rfl⟩ : syracuseStep 715517 = 268319) (by norm_num)
theorem B682789 : Blo 315835 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B715589 : Blo 315835 715589 := bbase (se 4 (by rfl) ⟨67086, by rfl⟩ : syracuseStep 715589 = 134173) (by norm_num)
theorem B715661 : Blo 315835 715661 := bbase (se 3 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 715661 = 268373) (by norm_num)
theorem B453541 : Blo 315835 453541 := bbase (se 4 (by rfl) ⟨42519, by rfl⟩ : syracuseStep 453541 = 85039) (by norm_num)
theorem B1076165 : Blo 315835 1076165 := bbase (se 4 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 1076165 = 201781) (by norm_num)
theorem B715733 : Blo 315835 715733 := bbase (se 7 (by rfl) ⟨8387, by rfl⟩ : syracuseStep 715733 = 16775) (by norm_num)
theorem B355333 : Blo 315835 355333 := bbase (se 4 (by rfl) ⟨33312, by rfl⟩ : syracuseStep 355333 = 66625) (by norm_num)
theorem B715805 : Blo 315835 715805 := bbase (se 3 (by rfl) ⟨134213, by rfl⟩ : syracuseStep 715805 = 268427) (by norm_num)
theorem B355369 : Blo 315835 355369 := bbase (se 2 (by rfl) ⟨133263, by rfl⟩ : syracuseStep 355369 = 266527) (by norm_num)
theorem B355405 : Blo 315835 355405 := bbase (se 3 (by rfl) ⟨66638, by rfl⟩ : syracuseStep 355405 = 133277) (by norm_num)
theorem B715877 : Blo 315835 715877 := bbase (se 4 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 715877 = 134227) (by norm_num)
theorem B355441 : Blo 315835 355441 := bbase (se 2 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 355441 = 266581) (by norm_num)
theorem B453757 : Blo 315835 453757 := bbase (se 3 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 453757 = 170159) (by norm_num)
theorem B355477 : Blo 315835 355477 := bbase (se 6 (by rfl) ⟨8331, by rfl⟩ : syracuseStep 355477 = 16663) (by norm_num)
theorem B715949 : Blo 315835 715949 := bbase (se 3 (by rfl) ⟨134240, by rfl⟩ : syracuseStep 715949 = 268481) (by norm_num)
theorem B355513 : Blo 315835 355513 := bbase (se 2 (by rfl) ⟨133317, by rfl⟩ : syracuseStep 355513 = 266635) (by norm_num)
theorem B355549 : Blo 315835 355549 := bbase (se 3 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 355549 = 133331) (by norm_num)
theorem B716021 : Blo 315835 716021 := bbase (se 5 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 716021 = 67127) (by norm_num)
theorem B355585 : Blo 315835 355585 := bbase (se 2 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 355585 = 266689) (by norm_num)
theorem B3665173 : Blo 315835 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B355621 : Blo 315835 355621 := bbase (se 4 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 355621 = 66679) (by norm_num)
theorem B716093 : Blo 315835 716093 := bbase (se 3 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 716093 = 268535) (by norm_num)
theorem B355657 : Blo 315835 355657 := bbase (se 2 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 355657 = 266743) (by norm_num)
theorem B355693 : Blo 315835 355693 := bbase (se 3 (by rfl) ⟨66692, by rfl⟩ : syracuseStep 355693 = 133385) (by norm_num)
theorem B1076597 : Blo 315835 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B716165 : Blo 315835 716165 := bbase (se 4 (by rfl) ⟨67140, by rfl⟩ : syracuseStep 716165 = 134281) (by norm_num)
theorem B355729 : Blo 315835 355729 := bbase (se 2 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 355729 = 266797) (by norm_num)
theorem B355765 : Blo 315835 355765 := bbase (se 5 (by rfl) ⟨16676, by rfl⟩ : syracuseStep 355765 = 33353) (by norm_num)
theorem B1535429 : Blo 315835 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B716237 : Blo 315835 716237 := bbase (se 3 (by rfl) ⟨134294, by rfl⟩ : syracuseStep 716237 = 268589) (by norm_num)
theorem B355801 : Blo 315835 355801 := bbase (se 2 (by rfl) ⟨133425, by rfl⟩ : syracuseStep 355801 = 266851) (by norm_num)
theorem B454133 : Blo 315835 454133 := bbase (se 5 (by rfl) ⟨21287, by rfl⟩ : syracuseStep 454133 = 42575) (by norm_num)
theorem B355837 : Blo 315835 355837 := bbase (se 3 (by rfl) ⟨66719, by rfl⟩ : syracuseStep 355837 = 133439) (by norm_num)
theorem B1601045 : Blo 315835 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B716309 : Blo 315835 716309 := bbase (se 6 (by rfl) ⟨16788, by rfl⟩ : syracuseStep 716309 = 33577) (by norm_num)
theorem B355873 : Blo 315835 355873 := bbase (se 2 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 355873 = 266905) (by norm_num)
theorem B355909 : Blo 315835 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B716381 : Blo 315835 716381 := bbase (se 3 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 716381 = 268643) (by norm_num)
theorem B355945 : Blo 315835 355945 := bbase (se 2 (by rfl) ⟨133479, by rfl⟩ : syracuseStep 355945 = 266959) (by norm_num)
theorem B355981 : Blo 315835 355981 := bbase (se 3 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 355981 = 133493) (by norm_num)
theorem B716453 : Blo 315835 716453 := bbase (se 4 (by rfl) ⟨67167, by rfl⟩ : syracuseStep 716453 = 134335) (by norm_num)
theorem B356017 : Blo 315835 356017 := bbase (se 2 (by rfl) ⟨133506, by rfl⟩ : syracuseStep 356017 = 267013) (by norm_num)
theorem B356053 : Blo 315835 356053 := bbase (se 7 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 356053 = 8345) (by norm_num)
theorem B716525 : Blo 315835 716525 := bbase (se 3 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 716525 = 268697) (by norm_num)
theorem B356089 : Blo 315835 356089 := bbase (se 2 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 356089 = 267067) (by norm_num)
theorem B356125 : Blo 315835 356125 := bbase (se 3 (by rfl) ⟨66773, by rfl⟩ : syracuseStep 356125 = 133547) (by norm_num)
theorem B323357 : Blo 315835 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B1077029 : Blo 315835 1077029 := bbase (se 4 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 1077029 = 201943) (by norm_num)
theorem B716597 : Blo 315835 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B356161 : Blo 315835 356161 := bbase (se 2 (by rfl) ⟨133560, by rfl⟩ : syracuseStep 356161 = 267121) (by norm_num)
theorem B683861 : Blo 315835 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B356197 : Blo 315835 356197 := bbase (se 4 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 356197 = 66787) (by norm_num)
theorem B716669 : Blo 315835 716669 := bbase (se 3 (by rfl) ⟨134375, by rfl⟩ : syracuseStep 716669 = 268751) (by norm_num)
theorem B356233 : Blo 315835 356233 := bbase (se 2 (by rfl) ⟨133587, by rfl⟩ : syracuseStep 356233 = 267175) (by norm_num)
theorem B356269 : Blo 315835 356269 := bbase (se 3 (by rfl) ⟨66800, by rfl⟩ : syracuseStep 356269 = 133601) (by norm_num)
theorem B716741 : Blo 315835 716741 := bbase (se 4 (by rfl) ⟨67194, by rfl⟩ : syracuseStep 716741 = 134389) (by norm_num)
theorem B356305 : Blo 315835 356305 := bbase (se 2 (by rfl) ⟨133614, by rfl⟩ : syracuseStep 356305 = 267229) (by norm_num)
theorem B3502037 : Blo 315835 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B356341 : Blo 315835 356341 := bbase (se 5 (by rfl) ⟨16703, by rfl⟩ : syracuseStep 356341 = 33407) (by norm_num)
theorem B2289653 : Blo 315835 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B716813 : Blo 315835 716813 := bbase (se 3 (by rfl) ⟨134402, by rfl⟩ : syracuseStep 716813 = 268805) (by norm_num)
theorem B356377 : Blo 315835 356377 := bbase (se 2 (by rfl) ⟨133641, by rfl⟩ : syracuseStep 356377 = 267283) (by norm_num)
theorem B356413 : Blo 315835 356413 := bbase (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) (by norm_num)
theorem B716885 : Blo 315835 716885 := bbase (se 8 (by rfl) ⟨4200, by rfl⟩ : syracuseStep 716885 = 8401) (by norm_num)
theorem B356449 : Blo 315835 356449 := bbase (se 2 (by rfl) ⟨133668, by rfl⟩ : syracuseStep 356449 = 267337) (by norm_num)
theorem B356485 : Blo 315835 356485 := bbase (se 4 (by rfl) ⟨33420, by rfl⟩ : syracuseStep 356485 = 66841) (by norm_num)
theorem B618653 : Blo 315835 618653 := bbase (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) (by norm_num)
theorem B716957 : Blo 315835 716957 := bbase (se 3 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 716957 = 268859) (by norm_num)
theorem B356521 : Blo 315835 356521 := bbase (se 2 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 356521 = 267391) (by norm_num)
theorem B1142981 : Blo 315835 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B356557 : Blo 315835 356557 := bbase (se 3 (by rfl) ⟨66854, by rfl⟩ : syracuseStep 356557 = 133709) (by norm_num)
theorem B1077461 : Blo 315835 1077461 := bbase (se 7 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 1077461 = 25253) (by norm_num)
theorem B717029 : Blo 315835 717029 := bbase (se 4 (by rfl) ⟨67221, by rfl⟩ : syracuseStep 717029 = 134443) (by norm_num)
theorem B356593 : Blo 315835 356593 := bbase (se 2 (by rfl) ⟨133722, by rfl⟩ : syracuseStep 356593 = 267445) (by norm_num)
theorem B356629 : Blo 315835 356629 := bbase (se 6 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 356629 = 16717) (by norm_num)
theorem B717101 : Blo 315835 717101 := bbase (se 3 (by rfl) ⟨134456, by rfl⟩ : syracuseStep 717101 = 268913) (by norm_num)
theorem B356665 : Blo 315835 356665 := bbase (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) (by norm_num)
theorem B782669 : Blo 315835 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B356701 : Blo 315835 356701 := bbase (se 3 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 356701 = 133763) (by norm_num)
theorem B717173 : Blo 315835 717173 := bbase (se 5 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 717173 = 67235) (by norm_num)
theorem B356737 : Blo 315835 356737 := bbase (se 2 (by rfl) ⟨133776, by rfl⟩ : syracuseStep 356737 = 267553) (by norm_num)
theorem B356773 : Blo 315835 356773 := bbase (se 4 (by rfl) ⟨33447, by rfl⟩ : syracuseStep 356773 = 66895) (by norm_num)
theorem B717245 : Blo 315835 717245 := bbase (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) (by norm_num)
theorem B356809 : Blo 315835 356809 := bbase (se 2 (by rfl) ⟨133803, by rfl⟩ : syracuseStep 356809 = 267607) (by norm_num)
theorem B1208789 : Blo 315835 1208789 := bbase (se 7 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 1208789 = 28331) (by norm_num)
theorem B356845 : Blo 315835 356845 := bbase (se 3 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 356845 = 133817) (by norm_num)
theorem B717317 : Blo 315835 717317 := bbase (se 4 (by rfl) ⟨67248, by rfl⟩ : syracuseStep 717317 = 134497) (by norm_num)
theorem B356881 : Blo 315835 356881 := bbase (se 2 (by rfl) ⟨133830, by rfl⟩ : syracuseStep 356881 = 267661) (by norm_num)
theorem B356917 : Blo 315835 356917 := bbase (se 5 (by rfl) ⟨16730, by rfl⟩ : syracuseStep 356917 = 33461) (by norm_num)
theorem B717389 : Blo 315835 717389 := bbase (se 3 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 717389 = 269021) (by norm_num)
theorem B356953 : Blo 315835 356953 := bbase (se 2 (by rfl) ⟨133857, by rfl⟩ : syracuseStep 356953 = 267715) (by norm_num)
theorem B356989 : Blo 315835 356989 := bbase (se 3 (by rfl) ⟨66935, by rfl⟩ : syracuseStep 356989 = 133871) (by norm_num)
theorem B1077893 : Blo 315835 1077893 := bbase (se 4 (by rfl) ⟨101052, by rfl⟩ : syracuseStep 1077893 = 202105) (by norm_num)
theorem B717461 : Blo 315835 717461 := bbase (se 6 (by rfl) ⟨16815, by rfl⟩ : syracuseStep 717461 = 33631) (by norm_num)
theorem B357025 : Blo 315835 357025 := bbase (se 2 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 357025 = 267769) (by norm_num)
theorem B357061 : Blo 315835 357061 := bbase (se 4 (by rfl) ⟨33474, by rfl⟩ : syracuseStep 357061 = 66949) (by norm_num)
theorem B717533 : Blo 315835 717533 := bbase (se 3 (by rfl) ⟨134537, by rfl⟩ : syracuseStep 717533 = 269075) (by norm_num)
theorem B357097 : Blo 315835 357097 := bbase (se 2 (by rfl) ⟨133911, by rfl⟩ : syracuseStep 357097 = 267823) (by norm_num)
theorem B1209077 : Blo 315835 1209077 := bbase (se 5 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 1209077 = 113351) (by norm_num)
theorem B357133 : Blo 315835 357133 := bbase (se 3 (by rfl) ⟨66962, by rfl⟩ : syracuseStep 357133 = 133925) (by norm_num)
theorem B1602341 : Blo 315835 1602341 := bbase (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) (by norm_num)
theorem B717605 : Blo 315835 717605 := bbase (se 4 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 717605 = 134551) (by norm_num)
theorem B357169 : Blo 315835 357169 := bbase (se 2 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 357169 = 267877) (by norm_num)
theorem B357205 : Blo 315835 357205 := bbase (se 9 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 357205 = 2093) (by norm_num)
theorem B1536853 : Blo 315835 1536853 := bbase (se 9 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 1536853 = 9005) (by norm_num)
theorem B717677 : Blo 315835 717677 := bbase (se 3 (by rfl) ⟨134564, by rfl⟩ : syracuseStep 717677 = 269129) (by norm_num)
theorem B357241 : Blo 315835 357241 := bbase (se 2 (by rfl) ⟨133965, by rfl⟩ : syracuseStep 357241 = 267931) (by norm_num)
theorem B357277 : Blo 315835 357277 := bbase (se 3 (by rfl) ⟨66989, by rfl⟩ : syracuseStep 357277 = 133979) (by norm_num)
theorem B717749 : Blo 315835 717749 := bbase (se 5 (by rfl) ⟨33644, by rfl⟩ : syracuseStep 717749 = 67289) (by norm_num)
theorem B357313 : Blo 315835 357313 := bbase (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) (by norm_num)
theorem B357349 : Blo 315835 357349 := bbase (se 4 (by rfl) ⟨33501, by rfl⟩ : syracuseStep 357349 = 67003) (by norm_num)
theorem B717821 : Blo 315835 717821 := bbase (se 3 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 717821 = 269183) (by norm_num)
theorem B357385 : Blo 315835 357385 := bbase (se 2 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 357385 = 268039) (by norm_num)
theorem B1143845 : Blo 315835 1143845 := bbase (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) (by norm_num)
theorem B357421 : Blo 315835 357421 := bbase (se 3 (by rfl) ⟨67016, by rfl⟩ : syracuseStep 357421 = 134033) (by norm_num)
theorem B1078325 : Blo 315835 1078325 := bbase (se 5 (by rfl) ⟨50546, by rfl⟩ : syracuseStep 1078325 = 101093) (by norm_num)
theorem B717893 : Blo 315835 717893 := bbase (se 4 (by rfl) ⟨67302, by rfl⟩ : syracuseStep 717893 = 134605) (by norm_num)
theorem B357457 : Blo 315835 357457 := bbase (se 2 (by rfl) ⟨134046, by rfl⟩ : syracuseStep 357457 = 268093) (by norm_num)
theorem B357493 : Blo 315835 357493 := bbase (se 5 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 357493 = 33515) (by norm_num)
theorem B717965 : Blo 315835 717965 := bbase (se 3 (by rfl) ⟨134618, by rfl⟩ : syracuseStep 717965 = 269237) (by norm_num)
theorem B357529 : Blo 315835 357529 := bbase (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) (by norm_num)
theorem B357565 : Blo 315835 357565 := bbase (se 3 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 357565 = 134087) (by norm_num)
theorem B718037 : Blo 315835 718037 := bbase (se 7 (by rfl) ⟨8414, by rfl⟩ : syracuseStep 718037 = 16829) (by norm_num)
theorem B357601 : Blo 315835 357601 := bbase (se 2 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 357601 = 268201) (by norm_num)
theorem B357637 : Blo 315835 357637 := bbase (se 4 (by rfl) ⟨33528, by rfl⟩ : syracuseStep 357637 = 67057) (by norm_num)
theorem B718109 : Blo 315835 718109 := bbase (se 3 (by rfl) ⟨134645, by rfl⟩ : syracuseStep 718109 = 269291) (by norm_num)
theorem B357673 : Blo 315835 357673 := bbase (se 2 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 357673 = 268255) (by norm_num)
theorem B357709 : Blo 315835 357709 := bbase (se 3 (by rfl) ⟨67070, by rfl⟩ : syracuseStep 357709 = 134141) (by norm_num)
theorem B718181 : Blo 315835 718181 := bbase (se 4 (by rfl) ⟨67329, by rfl⟩ : syracuseStep 718181 = 134659) (by norm_num)
theorem B357745 : Blo 315835 357745 := bbase (se 2 (by rfl) ⟨134154, by rfl⟩ : syracuseStep 357745 = 268309) (by norm_num)
theorem B357781 : Blo 315835 357781 := bbase (se 6 (by rfl) ⟨8385, by rfl⟩ : syracuseStep 357781 = 16771) (by norm_num)
theorem B718253 : Blo 315835 718253 := bbase (se 3 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 718253 = 269345) (by norm_num)
theorem B357817 : Blo 315835 357817 := bbase (se 2 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 357817 = 268363) (by norm_num)
theorem B357853 : Blo 315835 357853 := bbase (se 3 (by rfl) ⟨67097, by rfl⟩ : syracuseStep 357853 = 134195) (by norm_num)
theorem B1078757 : Blo 315835 1078757 := bbase (se 4 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 1078757 = 202267) (by norm_num)
theorem B718325 : Blo 315835 718325 := bbase (se 5 (by rfl) ⟨33671, by rfl⟩ : syracuseStep 718325 = 67343) (by norm_num)
theorem B357889 : Blo 315835 357889 := bbase (se 2 (by rfl) ⟨134208, by rfl⟩ : syracuseStep 357889 = 268417) (by norm_num)
theorem B357925 : Blo 315835 357925 := bbase (se 4 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 357925 = 67111) (by norm_num)
theorem B685621 : Blo 315835 685621 := bbase (se 5 (by rfl) ⟨32138, by rfl⟩ : syracuseStep 685621 = 64277) (by norm_num)
theorem B718397 : Blo 315835 718397 := bbase (se 3 (by rfl) ⟨134699, by rfl⟩ : syracuseStep 718397 = 269399) (by norm_num)
theorem B357961 : Blo 315835 357961 := bbase (se 2 (by rfl) ⟨134235, by rfl⟩ : syracuseStep 357961 = 268471) (by norm_num)
theorem B1799765 : Blo 315835 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B357997 : Blo 315835 357997 := bbase (se 3 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 357997 = 134249) (by norm_num)
theorem B718469 : Blo 315835 718469 := bbase (se 4 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 718469 = 134713) (by norm_num)
theorem B358033 : Blo 315835 358033 := bbase (se 2 (by rfl) ⟨134262, by rfl⟩ : syracuseStep 358033 = 268525) (by norm_num)
theorem B358069 : Blo 315835 358069 := bbase (se 5 (by rfl) ⟨16784, by rfl⟩ : syracuseStep 358069 = 33569) (by norm_num)
theorem B718541 : Blo 315835 718541 := bbase (se 3 (by rfl) ⟨134726, by rfl⟩ : syracuseStep 718541 = 269453) (by norm_num)
theorem B358105 : Blo 315835 358105 := bbase (se 2 (by rfl) ⟨134289, by rfl⟩ : syracuseStep 358105 = 268579) (by norm_num)
theorem B358141 : Blo 315835 358141 := bbase (se 3 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 358141 = 134303) (by norm_num)
theorem B685837 : Blo 315835 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B718613 : Blo 315835 718613 := bbase (se 6 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 718613 = 33685) (by norm_num)
theorem B358177 : Blo 315835 358177 := bbase (se 2 (by rfl) ⟨134316, by rfl⟩ : syracuseStep 358177 = 268633) (by norm_num)
theorem B1013573 : Blo 315835 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B358213 : Blo 315835 358213 := bbase (se 4 (by rfl) ⟨33582, by rfl⟩ : syracuseStep 358213 = 67165) (by norm_num)
theorem B718685 : Blo 315835 718685 := bbase (se 3 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 718685 = 269507) (by norm_num)
theorem B358249 : Blo 315835 358249 := bbase (se 2 (by rfl) ⟨134343, by rfl⟩ : syracuseStep 358249 = 268687) (by norm_num)
theorem B358285 : Blo 315835 358285 := bbase (se 3 (by rfl) ⟨67178, by rfl⟩ : syracuseStep 358285 = 134357) (by norm_num)
theorem B1210261 : Blo 315835 1210261 := bbase (se 6 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 1210261 = 56731) (by norm_num)
theorem B1079189 : Blo 315835 1079189 := bbase (se 6 (by rfl) ⟨25293, by rfl⟩ : syracuseStep 1079189 = 50587) (by norm_num)
theorem B718757 : Blo 315835 718757 := bbase (se 4 (by rfl) ⟨67383, by rfl⟩ : syracuseStep 718757 = 134767) (by norm_num)
theorem B358321 : Blo 315835 358321 := bbase (se 2 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 358321 = 268741) (by norm_num)
theorem B2717621 : Blo 315835 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B2422709 : Blo 315835 2422709 := bbase (se 5 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 2422709 = 227129) (by norm_num)
theorem B358357 : Blo 315835 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B718829 : Blo 315835 718829 := bbase (se 3 (by rfl) ⟨134780, by rfl⟩ : syracuseStep 718829 = 269561) (by norm_num)
theorem B358393 : Blo 315835 358393 := bbase (se 2 (by rfl) ⟨134397, by rfl⟩ : syracuseStep 358393 = 268795) (by norm_num)
theorem B358429 : Blo 315835 358429 := bbase (se 3 (by rfl) ⟨67205, by rfl⟩ : syracuseStep 358429 = 134411) (by norm_num)
theorem B1603637 : Blo 315835 1603637 := bbase (se 5 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 1603637 = 150341) (by norm_num)
theorem B718901 : Blo 315835 718901 := bbase (se 5 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 718901 = 67397) (by norm_num)
theorem B358465 : Blo 315835 358465 := bbase (se 2 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 358465 = 268849) (by norm_num)
theorem B358501 : Blo 315835 358501 := bbase (se 4 (by rfl) ⟨33609, by rfl⟩ : syracuseStep 358501 = 67219) (by norm_num)
theorem B718973 : Blo 315835 718973 := bbase (se 3 (by rfl) ⟨134807, by rfl⟩ : syracuseStep 718973 = 269615) (by norm_num)
theorem B358537 : Blo 315835 358537 := bbase (se 2 (by rfl) ⟨134451, by rfl⟩ : syracuseStep 358537 = 268903) (by norm_num)
theorem B358573 : Blo 315835 358573 := bbase (se 3 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 358573 = 134465) (by norm_num)
theorem B1308853 : Blo 315835 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1210565 : Blo 315835 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B719045 : Blo 315835 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B358609 : Blo 315835 358609 := bbase (se 2 (by rfl) ⟨134478, by rfl⟩ : syracuseStep 358609 = 268957) (by norm_num)
theorem B358645 : Blo 315835 358645 := bbase (se 5 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 358645 = 33623) (by norm_num)
theorem B719117 : Blo 315835 719117 := bbase (se 3 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 719117 = 269669) (by norm_num)
theorem B358681 : Blo 315835 358681 := bbase (se 2 (by rfl) ⟨134505, by rfl⟩ : syracuseStep 358681 = 269011) (by norm_num)
theorem B358717 : Blo 315835 358717 := bbase (se 3 (by rfl) ⟨67259, by rfl⟩ : syracuseStep 358717 = 134519) (by norm_num)
theorem B719189 : Blo 315835 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B358753 : Blo 315835 358753 := bbase (se 2 (by rfl) ⟨134532, by rfl⟩ : syracuseStep 358753 = 269065) (by norm_num)
theorem B358789 : Blo 315835 358789 := bbase (se 4 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 358789 = 67273) (by norm_num)
theorem B719261 : Blo 315835 719261 := bbase (se 3 (by rfl) ⟨134861, by rfl⟩ : syracuseStep 719261 = 269723) (by norm_num)
theorem B358825 : Blo 315835 358825 := bbase (se 2 (by rfl) ⟨134559, by rfl⟩ : syracuseStep 358825 = 269119) (by norm_num)
theorem B981445 : Blo 315835 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B358861 : Blo 315835 358861 := bbase (se 3 (by rfl) ⟨67286, by rfl⟩ : syracuseStep 358861 = 134573) (by norm_num)
theorem B719333 : Blo 315835 719333 := bbase (se 4 (by rfl) ⟨67437, by rfl⟩ : syracuseStep 719333 = 134875) (by norm_num)
theorem B358897 : Blo 315835 358897 := bbase (se 2 (by rfl) ⟨134586, by rfl⟩ : syracuseStep 358897 = 269173) (by norm_num)
theorem B358933 : Blo 315835 358933 := bbase (se 6 (by rfl) ⟨8412, by rfl⟩ : syracuseStep 358933 = 16825) (by norm_num)
theorem B719405 : Blo 315835 719405 := bbase (se 3 (by rfl) ⟨134888, by rfl⟩ : syracuseStep 719405 = 269777) (by norm_num)
theorem B358969 : Blo 315835 358969 := bbase (se 2 (by rfl) ⟨134613, by rfl⟩ : syracuseStep 358969 = 269227) (by norm_num)
theorem B359005 : Blo 315835 359005 := bbase (se 3 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 359005 = 134627) (by norm_num)
theorem B719477 : Blo 315835 719477 := bbase (se 5 (by rfl) ⟨33725, by rfl⟩ : syracuseStep 719477 = 67451) (by norm_num)
theorem B359041 : Blo 315835 359041 := bbase (se 2 (by rfl) ⟨134640, by rfl⟩ : syracuseStep 359041 = 269281) (by norm_num)
theorem B359077 : Blo 315835 359077 := bbase (se 4 (by rfl) ⟨33663, by rfl⟩ : syracuseStep 359077 = 67327) (by norm_num)
theorem B719549 : Blo 315835 719549 := bbase (se 3 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 719549 = 269831) (by norm_num)
theorem B359113 : Blo 315835 359113 := bbase (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) (by norm_num)
theorem B359149 : Blo 315835 359149 := bbase (se 3 (by rfl) ⟨67340, by rfl⟩ : syracuseStep 359149 = 134681) (by norm_num)
theorem B719621 : Blo 315835 719621 := bbase (se 4 (by rfl) ⟨67464, by rfl⟩ : syracuseStep 719621 = 134929) (by norm_num)
theorem B359185 : Blo 315835 359185 := bbase (se 2 (by rfl) ⟨134694, by rfl⟩ : syracuseStep 359185 = 269389) (by norm_num)
theorem B359221 : Blo 315835 359221 := bbase (se 5 (by rfl) ⟨16838, by rfl⟩ : syracuseStep 359221 = 33677) (by norm_num)
theorem B359257 : Blo 315835 359257 := bbase (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) (by norm_num)
theorem B359293 : Blo 315835 359293 := bbase (se 3 (by rfl) ⟨67367, by rfl⟩ : syracuseStep 359293 = 134735) (by norm_num)
theorem B359329 : Blo 315835 359329 := bbase (se 2 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 359329 = 269497) (by norm_num)
theorem B359365 : Blo 315835 359365 := bbase (se 4 (by rfl) ⟨33690, by rfl⟩ : syracuseStep 359365 = 67381) (by norm_num)
theorem B359401 : Blo 315835 359401 := bbase (se 2 (by rfl) ⟨134775, by rfl⟩ : syracuseStep 359401 = 269551) (by norm_num)
theorem B359437 : Blo 315835 359437 := bbase (se 3 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 359437 = 134789) (by norm_num)
theorem B359473 : Blo 315835 359473 := bbase (se 2 (by rfl) ⟨134802, by rfl⟩ : syracuseStep 359473 = 269605) (by norm_num)
theorem B818261 : Blo 315835 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B359509 : Blo 315835 359509 := bbase (se 8 (by rfl) ⟨2106, by rfl⟩ : syracuseStep 359509 = 4213) (by norm_num)
theorem B359545 : Blo 315835 359545 := bbase (se 2 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 359545 = 269659) (by norm_num)
theorem B359581 : Blo 315835 359581 := bbase (se 3 (by rfl) ⟨67421, by rfl⟩ : syracuseStep 359581 = 134843) (by norm_num)
theorem B359617 : Blo 315835 359617 := bbase (se 2 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 359617 = 269713) (by norm_num)
theorem B359653 : Blo 315835 359653 := bbase (se 4 (by rfl) ⟨33717, by rfl⟩ : syracuseStep 359653 = 67435) (by norm_num)
theorem B359689 : Blo 315835 359689 := bbase (se 2 (by rfl) ⟨134883, by rfl⟩ : syracuseStep 359689 = 269767) (by norm_num)
theorem B1637653 : Blo 315835 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B359725 : Blo 315835 359725 := bbase (se 3 (by rfl) ⟨67448, by rfl⟩ : syracuseStep 359725 = 134897) (by norm_num)
theorem B687421 : Blo 315835 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B1604933 : Blo 315835 1604933 := bbase (se 4 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 1604933 = 300925) (by norm_num)
theorem B359761 : Blo 315835 359761 := bbase (se 2 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 359761 = 269821) (by norm_num)
theorem B359797 : Blo 315835 359797 := bbase (se 5 (by rfl) ⟨16865, by rfl⟩ : syracuseStep 359797 = 33731) (by norm_num)
theorem B8224213 : Blo 315835 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B1146325 : Blo 315835 1146325 := bbase (se 7 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 1146325 = 26867) (by norm_num)
theorem B1932821 : Blo 315835 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B4587029 : Blo 315835 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1375829 : Blo 315835 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B2293685 : Blo 315835 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B655285 : Blo 315835 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B360515 : Blo 315835 360515 := bstep (se 1 (by rfl) ⟨270386, by rfl⟩ : syracuseStep 360515 = 540773) B540773
theorem B1310833 : Blo 315835 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B1933645 : Blo 315835 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B2064781 : Blo 315835 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B360931 : Blo 315835 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B1442609 : Blo 315835 1442609 := bstep (se 2 (by rfl) ⟨540978, by rfl⟩ : syracuseStep 1442609 = 1081957) B1081957
theorem B1016675 : Blo 315835 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B459857 : Blo 315835 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B1016945 : Blo 315835 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B1246385 : Blo 315835 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B525569 : Blo 315835 525569 := bstep (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) B394177
theorem B16647565 : Blo 315835 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B1213937 : Blo 315835 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B886477 : Blo 315835 886477 := bstep (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) B332429
theorem B853841 : Blo 315835 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B722819 : Blo 315835 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B690097 : Blo 315835 690097 := bstep (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) B517573
theorem B428131 : Blo 315835 428131 := bstep (se 1 (by rfl) ⟨321098, by rfl⟩ : syracuseStep 428131 = 642197) B642197
theorem B362723 : Blo 315835 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B1804913 : Blo 315835 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B1608497 : Blo 315835 1608497 := bstep (se 2 (by rfl) ⟨603186, by rfl⟩ : syracuseStep 1608497 = 1206373) B1206373
theorem B2034629 : Blo 315835 2034629 := bstep (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) B381493
theorem B363571 : Blo 315835 363571 := bstep (se 1 (by rfl) ⟨272678, by rfl⟩ : syracuseStep 363571 = 545357) B545357
theorem B2755781 : Blo 315835 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B2723057 : Blo 315835 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B1019405 : Blo 315835 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B855917 : Blo 315835 855917 := bstep (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) B320969
theorem B1806371 : Blo 315835 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B528563 : Blo 315835 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B1609955 : Blo 315835 1609955 := bstep (se 1 (by rfl) ⟨1207466, by rfl⟩ : syracuseStep 1609955 = 2414933) B2414933
theorem B4886897 : Blo 315835 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B627139 : Blo 315835 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B1282673 : Blo 315835 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B1708721 : Blo 315835 1708721 := bstep (se 2 (by rfl) ⟨640770, by rfl⟩ : syracuseStep 1708721 = 1281541) B1281541
theorem B3642083 : Blo 315835 3642083 := bstep (se 1 (by rfl) ⟨2731562, by rfl⟩ : syracuseStep 3642083 = 5463125) B5463125
theorem B1807373 : Blo 315835 1807373 := bstep (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) B677765
theorem B1610765 : Blo 315835 1610765 := bstep (se 3 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 1610765 = 604037) B604037
theorem B1021261 : Blo 315835 1021261 := bstep (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) B382973
theorem B13080689 : Blo 315835 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B2038193 : Blo 315835 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B399811 : Blo 315835 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B399907 : Blo 315835 399907 := bstep (se 1 (by rfl) ⟨299930, by rfl⟩ : syracuseStep 399907 = 599861) B599861
theorem B1284749 : Blo 315835 1284749 := bstep (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) B481781
theorem B465569 : Blo 315835 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B1350371 : Blo 315835 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B2235235 : Blo 315835 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B1022993 : Blo 315835 1022993 := bstep (se 2 (by rfl) ⟨383622, by rfl⟩ : syracuseStep 1022993 = 767245) B767245
theorem B400403 : Blo 315835 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B859267 : Blo 315835 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B2727053 : Blo 315835 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B4070897 : Blo 315835 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B1023619 : Blo 315835 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B401107 : Blo 315835 401107 := bstep (se 1 (by rfl) ⟨300830, by rfl⟩ : syracuseStep 401107 = 601661) B601661
theorem B401203 : Blo 315835 401203 := bstep (se 1 (by rfl) ⟨300902, by rfl⟩ : syracuseStep 401203 = 601805) B601805
theorem B2039651 : Blo 315835 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810289 : Blo 315835 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1613681 : Blo 315835 1613681 := bstep (se 2 (by rfl) ⟨605130, by rfl⟩ : syracuseStep 1613681 = 1210261) B1210261
theorem B2334691 : Blo 315835 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B1941509 : Blo 315835 1941509 := bstep (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) B364033
theorem B761987 : Blo 315835 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B729233 : Blo 315835 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B1745137 : Blo 315835 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B401699 : Blo 315835 401699 := bstep (se 1 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 401699 = 602549) B602549
theorem B3449141 : Blo 315835 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B532993 : Blo 315835 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B533027 : Blo 315835 533027 := bstep (se 1 (by rfl) ⟨399770, by rfl⟩ : syracuseStep 533027 = 799541) B799541
theorem B533155 : Blo 315835 533155 := bstep (se 1 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 533155 = 799733) B799733
theorem B1548977 : Blo 315835 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B762563 : Blo 315835 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B762641 : Blo 315835 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B533297 : Blo 315835 533297 := bstep (se 2 (by rfl) ⟨199986, by rfl⟩ : syracuseStep 533297 = 399973) B399973
theorem B2040653 : Blo 315835 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B1844045 : Blo 315835 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B533425 : Blo 315835 533425 := bstep (se 2 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 533425 = 400069) B400069
theorem B762833 : Blo 315835 762833 := bstep (se 2 (by rfl) ⟨286062, by rfl⟩ : syracuseStep 762833 = 572125) B572125
theorem B533459 : Blo 315835 533459 := bstep (se 1 (by rfl) ⟨400094, by rfl⟩ : syracuseStep 533459 = 800189) B800189
theorem B402403 : Blo 315835 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B402499 : Blo 315835 402499 := bstep (se 1 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 402499 = 603749) B603749
theorem B533587 : Blo 315835 533587 := bstep (se 1 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 533587 = 800381) B800381
theorem B2303117 : Blo 315835 2303117 := bstep (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) B863669
theorem B533729 : Blo 315835 533729 := bstep (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) B400297
theorem B763121 : Blo 315835 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B1811747 : Blo 315835 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1615139 : Blo 315835 1615139 := bstep (se 1 (by rfl) ⟨1211354, by rfl⟩ : syracuseStep 1615139 = 2422709) B2422709
theorem B533857 : Blo 315835 533857 := bstep (se 2 (by rfl) ⟨200196, by rfl⟩ : syracuseStep 533857 = 400393) B400393
theorem B533891 : Blo 315835 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B337379 : Blo 315835 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B534019 : Blo 315835 534019 := bstep (se 1 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 534019 = 801029) B801029
theorem B402995 : Blo 315835 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B599633 : Blo 315835 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B534161 : Blo 315835 534161 := bstep (se 2 (by rfl) ⟨200310, by rfl⟩ : syracuseStep 534161 = 400621) B400621
theorem B534289 : Blo 315835 534289 := bstep (se 2 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 534289 = 400717) B400717
theorem B534323 : Blo 315835 534323 := bstep (se 1 (by rfl) ⟨400742, by rfl⟩ : syracuseStep 534323 = 801485) B801485
theorem B6072205 : Blo 315835 6072205 := bstep (se 3 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 6072205 = 2277077) B2277077
theorem B534451 : Blo 315835 534451 := bstep (se 1 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 534451 = 801677) B801677
theorem B11610053 : Blo 315835 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B534593 : Blo 315835 534593 := bstep (se 2 (by rfl) ⟨200472, by rfl⟩ : syracuseStep 534593 = 400945) B400945
theorem B1615949 : Blo 315835 1615949 := bstep (se 3 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 1615949 = 605981) B605981
theorem B862339 : Blo 315835 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B534721 : Blo 315835 534721 := bstep (se 2 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 534721 = 401041) B401041
theorem B338131 : Blo 315835 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B534755 : Blo 315835 534755 := bstep (se 1 (by rfl) ⟨401066, by rfl⟩ : syracuseStep 534755 = 802133) B802133
theorem B403699 : Blo 315835 403699 := bstep (se 1 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 403699 = 605549) B605549
theorem B403795 : Blo 315835 403795 := bstep (se 1 (by rfl) ⟨302846, by rfl⟩ : syracuseStep 403795 = 605693) B605693
theorem B534883 : Blo 315835 534883 := bstep (se 1 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 534883 = 802325) B802325
theorem B1288547 : Blo 315835 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B3058019 : Blo 315835 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B600529 : Blo 315835 600529 := bstep (se 2 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 600529 = 450397) B450397
theorem B535025 : Blo 315835 535025 := bstep (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) B401269
theorem B600689 : Blo 315835 600689 := bstep (se 2 (by rfl) ⟨225258, by rfl⟩ : syracuseStep 600689 = 450517) B450517
theorem B535153 : Blo 315835 535153 := bstep (se 2 (by rfl) ⟨200682, by rfl⟩ : syracuseStep 535153 = 401365) B401365
theorem B535187 : Blo 315835 535187 := bstep (se 1 (by rfl) ⟨401390, by rfl⟩ : syracuseStep 535187 = 802781) B802781
theorem B404227 : Blo 315835 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B535315 : Blo 315835 535315 := bstep (se 1 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 535315 = 802973) B802973
theorem B404291 : Blo 315835 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B1354573 : Blo 315835 1354573 := bstep (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) B507965
theorem B863075 : Blo 315835 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B535457 : Blo 315835 535457 := bstep (se 2 (by rfl) ⟨200796, by rfl⟩ : syracuseStep 535457 = 401593) B401593
theorem B2403269 : Blo 315835 2403269 := bstep (se 4 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 2403269 = 450613) B450613
theorem B2698211 : Blo 315835 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B601091 : Blo 315835 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B535585 : Blo 315835 535585 := bstep (se 2 (by rfl) ⟨200844, by rfl⟩ : syracuseStep 535585 = 401689) B401689
theorem B535619 : Blo 315835 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B3550321 : Blo 315835 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B535747 : Blo 315835 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B535889 : Blo 315835 535889 := bstep (se 2 (by rfl) ⟨200958, by rfl⟩ : syracuseStep 535889 = 401917) B401917
theorem B1092977 : Blo 315835 1092977 := bstep (se 2 (by rfl) ⟨409866, by rfl⟩ : syracuseStep 1092977 = 819733) B819733
theorem B1027505 : Blo 315835 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B339395 : Blo 315835 339395 := bstep (se 1 (by rfl) ⟨254546, by rfl⟩ : syracuseStep 339395 = 509093) B509093
theorem B536017 : Blo 315835 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B536051 : Blo 315835 536051 := bstep (se 1 (by rfl) ⟨402038, by rfl⟩ : syracuseStep 536051 = 804077) B804077
theorem B765553 : Blo 315835 765553 := bstep (se 2 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 765553 = 574165) B574165
theorem B536179 : Blo 315835 536179 := bstep (se 1 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 536179 = 804269) B804269
theorem B863939 : Blo 315835 863939 := bstep (se 1 (by rfl) ⟨647954, by rfl⟩ : syracuseStep 863939 = 1295909) B1295909
theorem B1650403 : Blo 315835 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B536321 : Blo 315835 536321 := bstep (se 2 (by rfl) ⟨201120, by rfl⟩ : syracuseStep 536321 = 402241) B402241
theorem B864017 : Blo 315835 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B536449 : Blo 315835 536449 := bstep (se 2 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 536449 = 402337) B402337
theorem B601987 : Blo 315835 601987 := bstep (se 1 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 601987 = 902981) B902981
theorem B536483 : Blo 315835 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B6074309 : Blo 315835 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B602147 : Blo 315835 602147 := bstep (se 1 (by rfl) ⟨451610, by rfl⟩ : syracuseStep 602147 = 903221) B903221
theorem B536611 : Blo 315835 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B536753 : Blo 315835 536753 := bstep (se 2 (by rfl) ⟨201282, by rfl⟩ : syracuseStep 536753 = 402565) B402565
theorem B340147 : Blo 315835 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B536881 : Blo 315835 536881 := bstep (se 2 (by rfl) ⟨201330, by rfl⟩ : syracuseStep 536881 = 402661) B402661
theorem B536915 : Blo 315835 536915 := bstep (se 1 (by rfl) ⟨402686, by rfl⟩ : syracuseStep 536915 = 805373) B805373
theorem B1716677 : Blo 315835 1716677 := bstep (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) B321877
theorem B537043 : Blo 315835 537043 := bstep (se 1 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 537043 = 805565) B805565
theorem B1749509 : Blo 315835 1749509 := bstep (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) B328033
theorem B537185 : Blo 315835 537185 := bstep (se 2 (by rfl) ⟨201444, by rfl⟩ : syracuseStep 537185 = 402889) B402889
theorem B537313 : Blo 315835 537313 := bstep (se 2 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 537313 = 402985) B402985
theorem B537347 : Blo 315835 537347 := bstep (se 1 (by rfl) ⟨403010, by rfl⟩ : syracuseStep 537347 = 806021) B806021
theorem B1192781 : Blo 315835 1192781 := bstep (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) B447293
theorem B537475 : Blo 315835 537475 := bstep (se 1 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 537475 = 806213) B806213
theorem B1618865 : Blo 315835 1618865 := bstep (se 2 (by rfl) ⟨607074, by rfl⟩ : syracuseStep 1618865 = 1214149) B1214149
theorem B537617 : Blo 315835 537617 := bstep (se 2 (by rfl) ⟨201606, by rfl⟩ : syracuseStep 537617 = 403213) B403213
theorem B603217 : Blo 315835 603217 := bstep (se 2 (by rfl) ⟨226206, by rfl⟩ : syracuseStep 603217 = 452413) B452413
theorem B537745 : Blo 315835 537745 := bstep (se 2 (by rfl) ⟨201654, by rfl⟩ : syracuseStep 537745 = 403309) B403309
theorem B341155 : Blo 315835 341155 := bstep (se 1 (by rfl) ⟨255866, by rfl⟩ : syracuseStep 341155 = 511733) B511733
theorem B537779 : Blo 315835 537779 := bstep (se 1 (by rfl) ⟨403334, by rfl⟩ : syracuseStep 537779 = 806669) B806669
theorem B537907 : Blo 315835 537907 := bstep (se 1 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 537907 = 806861) B806861
theorem B538049 : Blo 315835 538049 := bstep (se 2 (by rfl) ⟨201768, by rfl⟩ : syracuseStep 538049 = 403537) B403537
theorem B538177 : Blo 315835 538177 := bstep (se 2 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 538177 = 403633) B403633
theorem B538211 : Blo 315835 538211 := bstep (se 1 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 538211 = 807317) B807317
theorem B800401 : Blo 315835 800401 := bstep (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) B600301
theorem B538339 : Blo 315835 538339 := bstep (se 1 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 538339 = 807509) B807509
theorem B538481 : Blo 315835 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B800675 : Blo 315835 800675 := bstep (se 1 (by rfl) ⟨600506, by rfl⟩ : syracuseStep 800675 = 1201013) B1201013
theorem B538609 : Blo 315835 538609 := bstep (se 2 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 538609 = 403957) B403957
theorem B964621 : Blo 315835 964621 := bstep (se 3 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 964621 = 361733) B361733
theorem B538643 : Blo 315835 538643 := bstep (se 1 (by rfl) ⟨403982, by rfl⟩ : syracuseStep 538643 = 807965) B807965
theorem B1554509 : Blo 315835 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B800867 : Blo 315835 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B604273 : Blo 315835 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B538771 : Blo 315835 538771 := bstep (se 1 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 538771 = 808157) B808157
theorem B964877 : Blo 315835 964877 := bstep (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) B361829
theorem B538913 : Blo 315835 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B440641 : Blo 315835 440641 := bstep (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) B330481
theorem B539041 : Blo 315835 539041 := bstep (se 2 (by rfl) ⟨202140, by rfl⟩ : syracuseStep 539041 = 404281) B404281
theorem B539075 : Blo 315835 539075 := bstep (se 1 (by rfl) ⟨404306, by rfl⟩ : syracuseStep 539075 = 808613) B808613
theorem B604675 : Blo 315835 604675 := bstep (se 1 (by rfl) ⟨453506, by rfl⟩ : syracuseStep 604675 = 907013) B907013
theorem B604721 : Blo 315835 604721 := bstep (se 2 (by rfl) ⟨226770, by rfl⟩ : syracuseStep 604721 = 453541) B453541
theorem B539203 : Blo 315835 539203 := bstep (se 1 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 539203 = 808805) B808805
theorem B473777 : Blo 315835 473777 := bstep (se 2 (by rfl) ⟨177666, by rfl⟩ : syracuseStep 473777 = 355333) B355333
theorem B473795 : Blo 315835 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B539345 : Blo 315835 539345 := bstep (se 2 (by rfl) ⟨202254, by rfl⟩ : syracuseStep 539345 = 404509) B404509
theorem B473825 : Blo 315835 473825 := bstep (se 2 (by rfl) ⟨177684, by rfl⟩ : syracuseStep 473825 = 355369) B355369
theorem B473843 : Blo 315835 473843 := bstep (se 1 (by rfl) ⟨355382, by rfl⟩ : syracuseStep 473843 = 710765) B710765
theorem B473873 : Blo 315835 473873 := bstep (se 2 (by rfl) ⟨177702, by rfl⟩ : syracuseStep 473873 = 355405) B355405
theorem B473891 : Blo 315835 473891 := bstep (se 1 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 473891 = 710837) B710837
theorem B473921 : Blo 315835 473921 := bstep (se 2 (by rfl) ⟨177720, by rfl⟩ : syracuseStep 473921 = 355441) B355441
theorem B605009 : Blo 315835 605009 := bstep (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) B453757
theorem B539473 : Blo 315835 539473 := bstep (se 2 (by rfl) ⟨202302, by rfl⟩ : syracuseStep 539473 = 404605) B404605
theorem B473939 : Blo 315835 473939 := bstep (se 1 (by rfl) ⟨355454, by rfl⟩ : syracuseStep 473939 = 710909) B710909
theorem B473969 : Blo 315835 473969 := bstep (se 2 (by rfl) ⟨177738, by rfl⟩ : syracuseStep 473969 = 355477) B355477
theorem B539507 : Blo 315835 539507 := bstep (se 1 (by rfl) ⟨404630, by rfl⟩ : syracuseStep 539507 = 809261) B809261
theorem B473987 : Blo 315835 473987 := bstep (se 1 (by rfl) ⟨355490, by rfl⟩ : syracuseStep 473987 = 710981) B710981
theorem B474017 : Blo 315835 474017 := bstep (se 2 (by rfl) ⟨177756, by rfl⟩ : syracuseStep 474017 = 355513) B355513
theorem B474035 : Blo 315835 474035 := bstep (se 1 (by rfl) ⟨355526, by rfl⟩ : syracuseStep 474035 = 711053) B711053
theorem B474065 : Blo 315835 474065 := bstep (se 2 (by rfl) ⟨177774, by rfl⟩ : syracuseStep 474065 = 355549) B355549
theorem B474083 : Blo 315835 474083 := bstep (se 1 (by rfl) ⟨355562, by rfl⟩ : syracuseStep 474083 = 711125) B711125
theorem B539635 : Blo 315835 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B474113 : Blo 315835 474113 := bstep (se 2 (by rfl) ⟨177792, by rfl⟩ : syracuseStep 474113 = 355585) B355585
theorem B801809 : Blo 315835 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B474131 : Blo 315835 474131 := bstep (se 1 (by rfl) ⟨355598, by rfl⟩ : syracuseStep 474131 = 711197) B711197
theorem B506915 : Blo 315835 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B474161 : Blo 315835 474161 := bstep (se 2 (by rfl) ⟨177810, by rfl⟩ : syracuseStep 474161 = 355621) B355621
theorem B474179 : Blo 315835 474179 := bstep (se 1 (by rfl) ⟨355634, by rfl⟩ : syracuseStep 474179 = 711269) B711269
theorem B801859 : Blo 315835 801859 := bstep (se 1 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 801859 = 1202789) B1202789
theorem B474209 : Blo 315835 474209 := bstep (se 2 (by rfl) ⟨177828, by rfl⟩ : syracuseStep 474209 = 355657) B355657
theorem B1358947 : Blo 315835 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B474227 : Blo 315835 474227 := bstep (se 1 (by rfl) ⟨355670, by rfl⟩ : syracuseStep 474227 = 711341) B711341
theorem B474257 : Blo 315835 474257 := bstep (se 2 (by rfl) ⟨177846, by rfl⟩ : syracuseStep 474257 = 355693) B355693
theorem B474275 : Blo 315835 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B474305 : Blo 315835 474305 := bstep (se 2 (by rfl) ⟨177864, by rfl⟩ : syracuseStep 474305 = 355729) B355729
theorem B900305 : Blo 315835 900305 := bstep (se 2 (by rfl) ⟨337614, by rfl⟩ : syracuseStep 900305 = 675229) B675229
theorem B802001 : Blo 315835 802001 := bstep (se 2 (by rfl) ⟨300750, by rfl⟩ : syracuseStep 802001 = 601501) B601501
theorem B474323 : Blo 315835 474323 := bstep (se 1 (by rfl) ⟨355742, by rfl⟩ : syracuseStep 474323 = 711485) B711485
theorem B507107 : Blo 315835 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B474353 : Blo 315835 474353 := bstep (se 2 (by rfl) ⟨177882, by rfl⟩ : syracuseStep 474353 = 355765) B355765
theorem B474371 : Blo 315835 474371 := bstep (se 1 (by rfl) ⟨355778, by rfl⟩ : syracuseStep 474371 = 711557) B711557
theorem B474401 : Blo 315835 474401 := bstep (se 2 (by rfl) ⟨177900, by rfl⟩ : syracuseStep 474401 = 355801) B355801
theorem B474419 : Blo 315835 474419 := bstep (se 1 (by rfl) ⟨355814, by rfl⟩ : syracuseStep 474419 = 711629) B711629
theorem B474449 : Blo 315835 474449 := bstep (se 2 (by rfl) ⟨177918, by rfl⟩ : syracuseStep 474449 = 355837) B355837
theorem B474467 : Blo 315835 474467 := bstep (se 1 (by rfl) ⟨355850, by rfl⟩ : syracuseStep 474467 = 711701) B711701
theorem B474497 : Blo 315835 474497 := bstep (se 2 (by rfl) ⟨177936, by rfl⟩ : syracuseStep 474497 = 355873) B355873
theorem B900497 : Blo 315835 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B474515 : Blo 315835 474515 := bstep (se 1 (by rfl) ⟨355886, by rfl⟩ : syracuseStep 474515 = 711773) B711773
theorem B474545 : Blo 315835 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B474563 : Blo 315835 474563 := bstep (se 1 (by rfl) ⟨355922, by rfl⟩ : syracuseStep 474563 = 711845) B711845
theorem B474593 : Blo 315835 474593 := bstep (se 2 (by rfl) ⟨177972, by rfl⟩ : syracuseStep 474593 = 355945) B355945
theorem B2276849 : Blo 315835 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B474611 : Blo 315835 474611 := bstep (se 1 (by rfl) ⟨355958, by rfl⟩ : syracuseStep 474611 = 711917) B711917
theorem B474641 : Blo 315835 474641 := bstep (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) B355981
theorem B474659 : Blo 315835 474659 := bstep (se 1 (by rfl) ⟨355994, by rfl⟩ : syracuseStep 474659 = 711989) B711989
theorem B605731 : Blo 315835 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B474689 : Blo 315835 474689 := bstep (se 2 (by rfl) ⟨178008, by rfl⟩ : syracuseStep 474689 = 356017) B356017
theorem B474707 : Blo 315835 474707 := bstep (se 1 (by rfl) ⟨356030, by rfl⟩ : syracuseStep 474707 = 712061) B712061
theorem B474737 : Blo 315835 474737 := bstep (se 2 (by rfl) ⟨178026, by rfl⟩ : syracuseStep 474737 = 356053) B356053
theorem B474755 : Blo 315835 474755 := bstep (se 1 (by rfl) ⟨356066, by rfl⟩ : syracuseStep 474755 = 712133) B712133
theorem B474785 : Blo 315835 474785 := bstep (se 2 (by rfl) ⟨178044, by rfl⟩ : syracuseStep 474785 = 356089) B356089
theorem B474803 : Blo 315835 474803 := bstep (se 1 (by rfl) ⟨356102, by rfl⟩ : syracuseStep 474803 = 712205) B712205
theorem B474833 : Blo 315835 474833 := bstep (se 2 (by rfl) ⟨178062, by rfl⟩ : syracuseStep 474833 = 356125) B356125
theorem B474851 : Blo 315835 474851 := bstep (se 1 (by rfl) ⟨356138, by rfl⟩ : syracuseStep 474851 = 712277) B712277
theorem B474881 : Blo 315835 474881 := bstep (se 2 (by rfl) ⟨178080, by rfl⟩ : syracuseStep 474881 = 356161) B356161
theorem B474899 : Blo 315835 474899 := bstep (se 1 (by rfl) ⟨356174, by rfl⟩ : syracuseStep 474899 = 712349) B712349
theorem B474929 : Blo 315835 474929 := bstep (se 2 (by rfl) ⟨178098, by rfl⟩ : syracuseStep 474929 = 356197) B356197
theorem B474947 : Blo 315835 474947 := bstep (se 1 (by rfl) ⟨356210, by rfl⟩ : syracuseStep 474947 = 712421) B712421
theorem B474977 : Blo 315835 474977 := bstep (se 2 (by rfl) ⟨178116, by rfl⟩ : syracuseStep 474977 = 356233) B356233
theorem B474995 : Blo 315835 474995 := bstep (se 1 (by rfl) ⟨356246, by rfl⟩ : syracuseStep 474995 = 712493) B712493
theorem B409459 : Blo 315835 409459 := bstep (se 1 (by rfl) ⟨307094, by rfl⟩ : syracuseStep 409459 = 614189) B614189
theorem B475025 : Blo 315835 475025 := bstep (se 2 (by rfl) ⟨178134, by rfl⟩ : syracuseStep 475025 = 356269) B356269
theorem B475043 : Blo 315835 475043 := bstep (se 1 (by rfl) ⟨356282, by rfl⟩ : syracuseStep 475043 = 712565) B712565
theorem B475073 : Blo 315835 475073 := bstep (se 2 (by rfl) ⟨178152, by rfl⟩ : syracuseStep 475073 = 356305) B356305
theorem B475091 : Blo 315835 475091 := bstep (se 1 (by rfl) ⟨356318, by rfl⟩ : syracuseStep 475091 = 712637) B712637
theorem B606179 : Blo 315835 606179 := bstep (se 1 (by rfl) ⟨454634, by rfl⟩ : syracuseStep 606179 = 909269) B909269
theorem B475121 : Blo 315835 475121 := bstep (se 2 (by rfl) ⟨178170, by rfl⟩ : syracuseStep 475121 = 356341) B356341
theorem B475139 : Blo 315835 475139 := bstep (se 1 (by rfl) ⟨356354, by rfl⟩ : syracuseStep 475139 = 712709) B712709
theorem B475169 : Blo 315835 475169 := bstep (se 2 (by rfl) ⟨178188, by rfl⟩ : syracuseStep 475169 = 356377) B356377
theorem B475187 : Blo 315835 475187 := bstep (se 1 (by rfl) ⟨356390, by rfl⟩ : syracuseStep 475187 = 712781) B712781
theorem B475217 : Blo 315835 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B475235 : Blo 315835 475235 := bstep (se 1 (by rfl) ⟨356426, by rfl⟩ : syracuseStep 475235 = 712853) B712853
theorem B475265 : Blo 315835 475265 := bstep (se 2 (by rfl) ⟨178224, by rfl⟩ : syracuseStep 475265 = 356449) B356449
theorem B475283 : Blo 315835 475283 := bstep (se 1 (by rfl) ⟨356462, by rfl⟩ : syracuseStep 475283 = 712925) B712925
theorem B409747 : Blo 315835 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B475313 : Blo 315835 475313 := bstep (se 2 (by rfl) ⟨178242, by rfl⟩ : syracuseStep 475313 = 356485) B356485
theorem B802993 : Blo 315835 802993 := bstep (se 2 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 802993 = 602245) B602245
theorem B475331 : Blo 315835 475331 := bstep (se 1 (by rfl) ⟨356498, by rfl⟩ : syracuseStep 475331 = 712997) B712997
theorem B475361 : Blo 315835 475361 := bstep (se 2 (by rfl) ⟨178260, by rfl⟩ : syracuseStep 475361 = 356521) B356521
theorem B475379 : Blo 315835 475379 := bstep (se 1 (by rfl) ⟨356534, by rfl⟩ : syracuseStep 475379 = 713069) B713069
theorem B606467 : Blo 315835 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B475409 : Blo 315835 475409 := bstep (se 2 (by rfl) ⟨178278, by rfl⟩ : syracuseStep 475409 = 356557) B356557
theorem B475427 : Blo 315835 475427 := bstep (se 1 (by rfl) ⟨356570, by rfl⟩ : syracuseStep 475427 = 713141) B713141
theorem B475457 : Blo 315835 475457 := bstep (se 2 (by rfl) ⟨178296, by rfl⟩ : syracuseStep 475457 = 356593) B356593
theorem B475475 : Blo 315835 475475 := bstep (se 1 (by rfl) ⟨356606, by rfl⟩ : syracuseStep 475475 = 713213) B713213
theorem B901489 : Blo 315835 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B475505 : Blo 315835 475505 := bstep (se 2 (by rfl) ⟨178314, by rfl⟩ : syracuseStep 475505 = 356629) B356629
theorem B475523 : Blo 315835 475523 := bstep (se 1 (by rfl) ⟨356642, by rfl⟩ : syracuseStep 475523 = 713285) B713285
theorem B475553 : Blo 315835 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B475571 : Blo 315835 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B803267 : Blo 315835 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B475601 : Blo 315835 475601 := bstep (se 2 (by rfl) ⟨178350, by rfl⟩ : syracuseStep 475601 = 356701) B356701
theorem B475619 : Blo 315835 475619 := bstep (se 1 (by rfl) ⟨356714, by rfl⟩ : syracuseStep 475619 = 713429) B713429
theorem B475649 : Blo 315835 475649 := bstep (se 2 (by rfl) ⟨178368, by rfl⟩ : syracuseStep 475649 = 356737) B356737
theorem B475667 : Blo 315835 475667 := bstep (se 1 (by rfl) ⟨356750, by rfl⟩ : syracuseStep 475667 = 713501) B713501
theorem B475697 : Blo 315835 475697 := bstep (se 2 (by rfl) ⟨178386, by rfl⟩ : syracuseStep 475697 = 356773) B356773
theorem B5128757 : Blo 315835 5128757 := bstep (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) B480821
theorem B475715 : Blo 315835 475715 := bstep (se 1 (by rfl) ⟨356786, by rfl⟩ : syracuseStep 475715 = 713573) B713573
theorem B410179 : Blo 315835 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B475745 : Blo 315835 475745 := bstep (se 2 (by rfl) ⟨178404, by rfl⟩ : syracuseStep 475745 = 356809) B356809
theorem B508529 : Blo 315835 508529 := bstep (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) B381397
theorem B475763 : Blo 315835 475763 := bstep (se 1 (by rfl) ⟨356822, by rfl⟩ : syracuseStep 475763 = 713645) B713645
theorem B901763 : Blo 315835 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B803459 : Blo 315835 803459 := bstep (se 1 (by rfl) ⟨602594, by rfl⟩ : syracuseStep 803459 = 1205189) B1205189
theorem B2409101 : Blo 315835 2409101 := bstep (se 3 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 2409101 = 903413) B903413
theorem B475793 : Blo 315835 475793 := bstep (se 2 (by rfl) ⟨178422, by rfl⟩ : syracuseStep 475793 = 356845) B356845
theorem B475811 : Blo 315835 475811 := bstep (se 1 (by rfl) ⟨356858, by rfl⟩ : syracuseStep 475811 = 713717) B713717
theorem B475841 : Blo 315835 475841 := bstep (se 2 (by rfl) ⟨178440, by rfl⟩ : syracuseStep 475841 = 356881) B356881
theorem B475859 : Blo 315835 475859 := bstep (se 1 (by rfl) ⟨356894, by rfl⟩ : syracuseStep 475859 = 713789) B713789
theorem B475889 : Blo 315835 475889 := bstep (se 2 (by rfl) ⟨178458, by rfl⟩ : syracuseStep 475889 = 356917) B356917
theorem B475907 : Blo 315835 475907 := bstep (se 1 (by rfl) ⟨356930, by rfl⟩ : syracuseStep 475907 = 713861) B713861
theorem B475937 : Blo 315835 475937 := bstep (se 2 (by rfl) ⟨178476, by rfl⟩ : syracuseStep 475937 = 356953) B356953
theorem B475955 : Blo 315835 475955 := bstep (se 1 (by rfl) ⟨356966, by rfl⟩ : syracuseStep 475955 = 713933) B713933
theorem B901955 : Blo 315835 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B475985 : Blo 315835 475985 := bstep (se 2 (by rfl) ⟨178494, by rfl⟩ : syracuseStep 475985 = 356989) B356989
theorem B476003 : Blo 315835 476003 := bstep (se 1 (by rfl) ⟨357002, by rfl⟩ : syracuseStep 476003 = 714005) B714005
theorem B476033 : Blo 315835 476033 := bstep (se 2 (by rfl) ⟨178512, by rfl⟩ : syracuseStep 476033 = 357025) B357025
theorem B476051 : Blo 315835 476051 := bstep (se 1 (by rfl) ⟨357038, by rfl⟩ : syracuseStep 476051 = 714077) B714077
theorem B476081 : Blo 315835 476081 := bstep (se 2 (by rfl) ⟨178530, by rfl⟩ : syracuseStep 476081 = 357061) B357061
theorem B967601 : Blo 315835 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B476099 : Blo 315835 476099 := bstep (se 1 (by rfl) ⟨357074, by rfl⟩ : syracuseStep 476099 = 714149) B714149
theorem B476129 : Blo 315835 476129 := bstep (se 2 (by rfl) ⟨178548, by rfl⟩ : syracuseStep 476129 = 357097) B357097
theorem B476147 : Blo 315835 476147 := bstep (se 1 (by rfl) ⟨357110, by rfl⟩ : syracuseStep 476147 = 714221) B714221
theorem B476177 : Blo 315835 476177 := bstep (se 2 (by rfl) ⟨178566, by rfl⟩ : syracuseStep 476177 = 357133) B357133
theorem B476195 : Blo 315835 476195 := bstep (se 1 (by rfl) ⟨357146, by rfl⟩ : syracuseStep 476195 = 714293) B714293
theorem B476225 : Blo 315835 476225 := bstep (se 2 (by rfl) ⟨178584, by rfl⟩ : syracuseStep 476225 = 357169) B357169
theorem B476243 : Blo 315835 476243 := bstep (se 1 (by rfl) ⟨357182, by rfl⟩ : syracuseStep 476243 = 714365) B714365
theorem B476273 : Blo 315835 476273 := bstep (se 2 (by rfl) ⟨178602, by rfl⟩ : syracuseStep 476273 = 357205) B357205
theorem B2049137 : Blo 315835 2049137 := bstep (se 2 (by rfl) ⟨768426, by rfl⟩ : syracuseStep 2049137 = 1536853) B1536853
theorem B476291 : Blo 315835 476291 := bstep (se 1 (by rfl) ⟨357218, by rfl⟩ : syracuseStep 476291 = 714437) B714437
theorem B476321 : Blo 315835 476321 := bstep (se 2 (by rfl) ⟨178620, by rfl⟩ : syracuseStep 476321 = 357241) B357241
theorem B574627 : Blo 315835 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B476339 : Blo 315835 476339 := bstep (se 1 (by rfl) ⟨357254, by rfl⟩ : syracuseStep 476339 = 714509) B714509
theorem B476369 : Blo 315835 476369 := bstep (se 2 (by rfl) ⟨178638, by rfl⟩ : syracuseStep 476369 = 357277) B357277
theorem B476387 : Blo 315835 476387 := bstep (se 1 (by rfl) ⟨357290, by rfl⟩ : syracuseStep 476387 = 714581) B714581
theorem B476417 : Blo 315835 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B476435 : Blo 315835 476435 := bstep (se 1 (by rfl) ⟨357326, by rfl⟩ : syracuseStep 476435 = 714653) B714653
theorem B476465 : Blo 315835 476465 := bstep (se 2 (by rfl) ⟨178674, by rfl⟩ : syracuseStep 476465 = 357349) B357349
theorem B476483 : Blo 315835 476483 := bstep (se 1 (by rfl) ⟨357362, by rfl⟩ : syracuseStep 476483 = 714725) B714725
theorem B542033 : Blo 315835 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B476513 : Blo 315835 476513 := bstep (se 2 (by rfl) ⟨178692, by rfl⟩ : syracuseStep 476513 = 357385) B357385
theorem B476531 : Blo 315835 476531 := bstep (se 1 (by rfl) ⟨357398, by rfl⟩ : syracuseStep 476531 = 714797) B714797
theorem B476561 : Blo 315835 476561 := bstep (se 2 (by rfl) ⟨178710, by rfl⟩ : syracuseStep 476561 = 357421) B357421
theorem B476579 : Blo 315835 476579 := bstep (se 1 (by rfl) ⟨357434, by rfl⟩ : syracuseStep 476579 = 714869) B714869
theorem B476609 : Blo 315835 476609 := bstep (se 2 (by rfl) ⟨178728, by rfl⟩ : syracuseStep 476609 = 357457) B357457
theorem B3851717 : Blo 315835 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1066445 : Blo 315835 1066445 := bstep (se 3 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 1066445 = 399917) B399917
theorem B476627 : Blo 315835 476627 := bstep (se 1 (by rfl) ⟨357470, by rfl⟩ : syracuseStep 476627 = 714941) B714941
theorem B1295843 : Blo 315835 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B476657 : Blo 315835 476657 := bstep (se 2 (by rfl) ⟨178746, by rfl⟩ : syracuseStep 476657 = 357493) B357493
theorem B1361393 : Blo 315835 1361393 := bstep (se 2 (by rfl) ⟨510522, by rfl⟩ : syracuseStep 1361393 = 1021045) B1021045
theorem B1066499 : Blo 315835 1066499 := bstep (se 1 (by rfl) ⟨799874, by rfl⟩ : syracuseStep 1066499 = 1599749) B1599749
theorem B476675 : Blo 315835 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B476705 : Blo 315835 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B804401 : Blo 315835 804401 := bstep (se 2 (by rfl) ⟨301650, by rfl⟩ : syracuseStep 804401 = 603301) B603301
theorem B476723 : Blo 315835 476723 := bstep (se 1 (by rfl) ⟨357542, by rfl⟩ : syracuseStep 476723 = 715085) B715085
theorem B476753 : Blo 315835 476753 := bstep (se 2 (by rfl) ⟨178782, by rfl⟩ : syracuseStep 476753 = 357565) B357565
theorem B804451 : Blo 315835 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B476771 : Blo 315835 476771 := bstep (se 1 (by rfl) ⟨357578, by rfl⟩ : syracuseStep 476771 = 715157) B715157
theorem B902765 : Blo 315835 902765 := bstep (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) B338537
theorem B476801 : Blo 315835 476801 := bstep (se 2 (by rfl) ⟨178800, by rfl⟩ : syracuseStep 476801 = 357601) B357601
theorem B476819 : Blo 315835 476819 := bstep (se 1 (by rfl) ⟨357614, by rfl⟩ : syracuseStep 476819 = 715229) B715229
theorem B476849 : Blo 315835 476849 := bstep (se 2 (by rfl) ⟨178818, by rfl⟩ : syracuseStep 476849 = 357637) B357637
theorem B542387 : Blo 315835 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B476867 : Blo 315835 476867 := bstep (se 1 (by rfl) ⟨357650, by rfl⟩ : syracuseStep 476867 = 715301) B715301
theorem B476897 : Blo 315835 476897 := bstep (se 2 (by rfl) ⟨178836, by rfl⟩ : syracuseStep 476897 = 357673) B357673
theorem B804593 : Blo 315835 804593 := bstep (se 2 (by rfl) ⟨301722, by rfl⟩ : syracuseStep 804593 = 603445) B603445
theorem B476915 : Blo 315835 476915 := bstep (se 1 (by rfl) ⟨357686, by rfl⟩ : syracuseStep 476915 = 715373) B715373
theorem B1066769 : Blo 315835 1066769 := bstep (se 2 (by rfl) ⟨400038, by rfl⟩ : syracuseStep 1066769 = 800077) B800077
theorem B476945 : Blo 315835 476945 := bstep (se 2 (by rfl) ⟨178854, by rfl⟩ : syracuseStep 476945 = 357709) B357709
theorem B902947 : Blo 315835 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B476963 : Blo 315835 476963 := bstep (se 1 (by rfl) ⟨357722, by rfl⟩ : syracuseStep 476963 = 715445) B715445
theorem B476993 : Blo 315835 476993 := bstep (se 2 (by rfl) ⟨178872, by rfl⟩ : syracuseStep 476993 = 357745) B357745
theorem B477011 : Blo 315835 477011 := bstep (se 1 (by rfl) ⟨357758, by rfl⟩ : syracuseStep 477011 = 715517) B715517
theorem B477041 : Blo 315835 477041 := bstep (se 2 (by rfl) ⟨178890, by rfl⟩ : syracuseStep 477041 = 357781) B357781
theorem B477059 : Blo 315835 477059 := bstep (se 1 (by rfl) ⟨357794, by rfl⟩ : syracuseStep 477059 = 715589) B715589
theorem B477089 : Blo 315835 477089 := bstep (se 2 (by rfl) ⟨178908, by rfl⟩ : syracuseStep 477089 = 357817) B357817
theorem B477107 : Blo 315835 477107 := bstep (se 1 (by rfl) ⟨357830, by rfl⟩ : syracuseStep 477107 = 715661) B715661
theorem B477137 : Blo 315835 477137 := bstep (se 2 (by rfl) ⟨178926, by rfl⟩ : syracuseStep 477137 = 357853) B357853
theorem B477155 : Blo 315835 477155 := bstep (se 1 (by rfl) ⟨357866, by rfl⟩ : syracuseStep 477155 = 715733) B715733
theorem B477185 : Blo 315835 477185 := bstep (se 2 (by rfl) ⟨178944, by rfl⟩ : syracuseStep 477185 = 357889) B357889
theorem B1820677 : Blo 315835 1820677 := bstep (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) B341377
theorem B477203 : Blo 315835 477203 := bstep (se 1 (by rfl) ⟨357902, by rfl⟩ : syracuseStep 477203 = 715805) B715805
theorem B477233 : Blo 315835 477233 := bstep (se 2 (by rfl) ⟨178962, by rfl⟩ : syracuseStep 477233 = 357925) B357925
theorem B477251 : Blo 315835 477251 := bstep (se 1 (by rfl) ⟨357938, by rfl⟩ : syracuseStep 477251 = 715877) B715877
theorem B477281 : Blo 315835 477281 := bstep (se 2 (by rfl) ⟨178980, by rfl⟩ : syracuseStep 477281 = 357961) B357961
theorem B477299 : Blo 315835 477299 := bstep (se 1 (by rfl) ⟨357974, by rfl⟩ : syracuseStep 477299 = 715949) B715949
theorem B510067 : Blo 315835 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B477329 : Blo 315835 477329 := bstep (se 2 (by rfl) ⟨178998, by rfl⟩ : syracuseStep 477329 = 357997) B357997
theorem B510113 : Blo 315835 510113 := bstep (se 2 (by rfl) ⟨191292, by rfl⟩ : syracuseStep 510113 = 382585) B382585
theorem B477347 : Blo 315835 477347 := bstep (se 1 (by rfl) ⟨358010, by rfl⟩ : syracuseStep 477347 = 716021) B716021
theorem B477377 : Blo 315835 477377 := bstep (se 2 (by rfl) ⟨179016, by rfl⟩ : syracuseStep 477377 = 358033) B358033
theorem B477395 : Blo 315835 477395 := bstep (se 1 (by rfl) ⟨358046, by rfl⟩ : syracuseStep 477395 = 716093) B716093
theorem B477425 : Blo 315835 477425 := bstep (se 2 (by rfl) ⟨179034, by rfl⟩ : syracuseStep 477425 = 358069) B358069
theorem B477443 : Blo 315835 477443 := bstep (se 1 (by rfl) ⟨358082, by rfl⟩ : syracuseStep 477443 = 716165) B716165
theorem B903437 : Blo 315835 903437 := bstep (se 3 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 903437 = 338789) B338789
theorem B477473 : Blo 315835 477473 := bstep (se 2 (by rfl) ⟨179052, by rfl⟩ : syracuseStep 477473 = 358105) B358105
theorem B1067309 : Blo 315835 1067309 := bstep (se 3 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 1067309 = 400241) B400241
theorem B1624369 : Blo 315835 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B477491 : Blo 315835 477491 := bstep (se 1 (by rfl) ⟨358118, by rfl⟩ : syracuseStep 477491 = 716237) B716237
theorem B477521 : Blo 315835 477521 := bstep (se 2 (by rfl) ⟨179070, by rfl⟩ : syracuseStep 477521 = 358141) B358141
theorem B1067363 : Blo 315835 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B477539 : Blo 315835 477539 := bstep (se 1 (by rfl) ⟨358154, by rfl⟩ : syracuseStep 477539 = 716309) B716309
theorem B477569 : Blo 315835 477569 := bstep (se 2 (by rfl) ⟨179088, by rfl⟩ : syracuseStep 477569 = 358177) B358177
theorem B477587 : Blo 315835 477587 := bstep (se 1 (by rfl) ⟨358190, by rfl⟩ : syracuseStep 477587 = 716381) B716381
theorem B477617 : Blo 315835 477617 := bstep (se 2 (by rfl) ⟨179106, by rfl⟩ : syracuseStep 477617 = 358213) B358213
theorem B477635 : Blo 315835 477635 := bstep (se 1 (by rfl) ⟨358226, by rfl⟩ : syracuseStep 477635 = 716453) B716453
theorem B477665 : Blo 315835 477665 := bstep (se 2 (by rfl) ⟨179124, by rfl⟩ : syracuseStep 477665 = 358249) B358249
theorem B477683 : Blo 315835 477683 := bstep (se 1 (by rfl) ⟨358262, by rfl⟩ : syracuseStep 477683 = 716525) B716525
theorem B477713 : Blo 315835 477713 := bstep (se 2 (by rfl) ⟨179142, by rfl⟩ : syracuseStep 477713 = 358285) B358285
theorem B477731 : Blo 315835 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B477761 : Blo 315835 477761 := bstep (se 2 (by rfl) ⟨179160, by rfl⟩ : syracuseStep 477761 = 358321) B358321
theorem B477779 : Blo 315835 477779 := bstep (se 1 (by rfl) ⟨358334, by rfl⟩ : syracuseStep 477779 = 716669) B716669
theorem B1067633 : Blo 315835 1067633 := bstep (se 2 (by rfl) ⟨400362, by rfl⟩ : syracuseStep 1067633 = 800725) B800725
theorem B477809 : Blo 315835 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B477827 : Blo 315835 477827 := bstep (se 1 (by rfl) ⟨358370, by rfl⟩ : syracuseStep 477827 = 716741) B716741
theorem B477857 : Blo 315835 477857 := bstep (se 2 (by rfl) ⟨179196, by rfl⟩ : syracuseStep 477857 = 358393) B358393
theorem B1526435 : Blo 315835 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B379571 : Blo 315835 379571 := bstep (se 1 (by rfl) ⟨284678, by rfl⟩ : syracuseStep 379571 = 569357) B569357
theorem B477875 : Blo 315835 477875 := bstep (se 1 (by rfl) ⟨358406, by rfl⟩ : syracuseStep 477875 = 716813) B716813
theorem B805585 : Blo 315835 805585 := bstep (se 2 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 805585 = 604189) B604189
theorem B477905 : Blo 315835 477905 := bstep (se 2 (by rfl) ⟨179214, by rfl⟩ : syracuseStep 477905 = 358429) B358429
theorem B477923 : Blo 315835 477923 := bstep (se 1 (by rfl) ⟨358442, by rfl⟩ : syracuseStep 477923 = 716885) B716885
theorem B477953 : Blo 315835 477953 := bstep (se 2 (by rfl) ⟨179232, by rfl⟩ : syracuseStep 477953 = 358465) B358465
theorem B412435 : Blo 315835 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B477971 : Blo 315835 477971 := bstep (se 1 (by rfl) ⟨358478, by rfl⟩ : syracuseStep 477971 = 716957) B716957
theorem B478001 : Blo 315835 478001 := bstep (se 2 (by rfl) ⟨179250, by rfl⟩ : syracuseStep 478001 = 358501) B358501
theorem B5327669 : Blo 315835 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B478019 : Blo 315835 478019 := bstep (se 1 (by rfl) ⟨358514, by rfl⟩ : syracuseStep 478019 = 717029) B717029
theorem B478049 : Blo 315835 478049 := bstep (se 2 (by rfl) ⟨179268, by rfl⟩ : syracuseStep 478049 = 358537) B358537
theorem B4049777 : Blo 315835 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B478067 : Blo 315835 478067 := bstep (se 1 (by rfl) ⟨358550, by rfl⟩ : syracuseStep 478067 = 717101) B717101
theorem B478097 : Blo 315835 478097 := bstep (se 2 (by rfl) ⟨179286, by rfl⟩ : syracuseStep 478097 = 358573) B358573
theorem B478115 : Blo 315835 478115 := bstep (se 1 (by rfl) ⟨358586, by rfl⟩ : syracuseStep 478115 = 717173) B717173
theorem B478145 : Blo 315835 478145 := bstep (se 2 (by rfl) ⟨179304, by rfl⟩ : syracuseStep 478145 = 358609) B358609
theorem B478163 : Blo 315835 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B805859 : Blo 315835 805859 := bstep (se 1 (by rfl) ⟨604394, by rfl⟩ : syracuseStep 805859 = 1208789) B1208789
theorem B478193 : Blo 315835 478193 := bstep (se 2 (by rfl) ⟨179322, by rfl⟩ : syracuseStep 478193 = 358645) B358645
theorem B478211 : Blo 315835 478211 := bstep (se 1 (by rfl) ⟨358658, by rfl⟩ : syracuseStep 478211 = 717317) B717317
theorem B478241 : Blo 315835 478241 := bstep (se 2 (by rfl) ⟨179340, by rfl⟩ : syracuseStep 478241 = 358681) B358681
theorem B478259 : Blo 315835 478259 := bstep (se 1 (by rfl) ⟨358694, by rfl⟩ : syracuseStep 478259 = 717389) B717389
theorem B478289 : Blo 315835 478289 := bstep (se 2 (by rfl) ⟨179358, by rfl⟩ : syracuseStep 478289 = 358717) B358717
theorem B478307 : Blo 315835 478307 := bstep (se 1 (by rfl) ⟨358730, by rfl⟩ : syracuseStep 478307 = 717461) B717461
theorem B674929 : Blo 315835 674929 := bstep (se 2 (by rfl) ⟨253098, by rfl⟩ : syracuseStep 674929 = 506197) B506197
theorem B478337 : Blo 315835 478337 := bstep (se 2 (by rfl) ⟨179376, by rfl⟩ : syracuseStep 478337 = 358753) B358753
theorem B511105 : Blo 315835 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B1068173 : Blo 315835 1068173 := bstep (se 3 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 1068173 = 400565) B400565
theorem B478355 : Blo 315835 478355 := bstep (se 1 (by rfl) ⟨358766, by rfl⟩ : syracuseStep 478355 = 717533) B717533
theorem B806051 : Blo 315835 806051 := bstep (se 1 (by rfl) ⟨604538, by rfl⟩ : syracuseStep 806051 = 1209077) B1209077
theorem B478385 : Blo 315835 478385 := bstep (se 2 (by rfl) ⟨179394, by rfl⟩ : syracuseStep 478385 = 358789) B358789
theorem B1068227 : Blo 315835 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B478403 : Blo 315835 478403 := bstep (se 1 (by rfl) ⟨358802, by rfl⟩ : syracuseStep 478403 = 717605) B717605
theorem B478433 : Blo 315835 478433 := bstep (se 2 (by rfl) ⟨179412, by rfl⟩ : syracuseStep 478433 = 358825) B358825
theorem B478451 : Blo 315835 478451 := bstep (se 1 (by rfl) ⟨358838, by rfl⟩ : syracuseStep 478451 = 717677) B717677
theorem B478481 : Blo 315835 478481 := bstep (se 2 (by rfl) ⟨179430, by rfl⟩ : syracuseStep 478481 = 358861) B358861
theorem B478499 : Blo 315835 478499 := bstep (se 1 (by rfl) ⟨358874, by rfl⟩ : syracuseStep 478499 = 717749) B717749
theorem B478529 : Blo 315835 478529 := bstep (se 2 (by rfl) ⟨179448, by rfl⟩ : syracuseStep 478529 = 358897) B358897
theorem B478547 : Blo 315835 478547 := bstep (se 1 (by rfl) ⟨358910, by rfl⟩ : syracuseStep 478547 = 717821) B717821
theorem B478577 : Blo 315835 478577 := bstep (se 2 (by rfl) ⟨179466, by rfl⟩ : syracuseStep 478577 = 358933) B358933
theorem B478595 : Blo 315835 478595 := bstep (se 1 (by rfl) ⟨358946, by rfl⟩ : syracuseStep 478595 = 717893) B717893
theorem B478625 : Blo 315835 478625 := bstep (se 2 (by rfl) ⟨179484, by rfl⟩ : syracuseStep 478625 = 358969) B358969
theorem B904621 : Blo 315835 904621 := bstep (se 3 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 904621 = 339233) B339233
theorem B478643 : Blo 315835 478643 := bstep (se 1 (by rfl) ⟨358982, by rfl⟩ : syracuseStep 478643 = 717965) B717965
theorem B1068497 : Blo 315835 1068497 := bstep (se 2 (by rfl) ⟨400686, by rfl⟩ : syracuseStep 1068497 = 801373) B801373
theorem B478673 : Blo 315835 478673 := bstep (se 2 (by rfl) ⟨179502, by rfl⟩ : syracuseStep 478673 = 359005) B359005
theorem B478691 : Blo 315835 478691 := bstep (se 1 (by rfl) ⟨359018, by rfl⟩ : syracuseStep 478691 = 718037) B718037
theorem B2412017 : Blo 315835 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B478721 : Blo 315835 478721 := bstep (se 2 (by rfl) ⟨179520, by rfl⟩ : syracuseStep 478721 = 359041) B359041
theorem B642563 : Blo 315835 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B2280973 : Blo 315835 2280973 := bstep (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) B855365
theorem B478739 : Blo 315835 478739 := bstep (se 1 (by rfl) ⟨359054, by rfl⟩ : syracuseStep 478739 = 718109) B718109
theorem B478769 : Blo 315835 478769 := bstep (se 2 (by rfl) ⟨179538, by rfl⟩ : syracuseStep 478769 = 359077) B359077
theorem B511553 : Blo 315835 511553 := bstep (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) B383665
theorem B577091 : Blo 315835 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B478787 : Blo 315835 478787 := bstep (se 1 (by rfl) ⟨359090, by rfl⟩ : syracuseStep 478787 = 718181) B718181
theorem B478817 : Blo 315835 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B478835 : Blo 315835 478835 := bstep (se 1 (by rfl) ⟨359126, by rfl⟩ : syracuseStep 478835 = 718253) B718253
theorem B478865 : Blo 315835 478865 := bstep (se 2 (by rfl) ⟨179574, by rfl⟩ : syracuseStep 478865 = 359149) B359149
theorem B478883 : Blo 315835 478883 := bstep (se 1 (by rfl) ⟨359162, by rfl⟩ : syracuseStep 478883 = 718325) B718325
theorem B478913 : Blo 315835 478913 := bstep (se 2 (by rfl) ⟨179592, by rfl⟩ : syracuseStep 478913 = 359185) B359185
theorem B478931 : Blo 315835 478931 := bstep (se 1 (by rfl) ⟨359198, by rfl⟩ : syracuseStep 478931 = 718397) B718397
theorem B1199843 : Blo 315835 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B478961 : Blo 315835 478961 := bstep (se 2 (by rfl) ⟨179610, by rfl⟩ : syracuseStep 478961 = 359221) B359221
theorem B478979 : Blo 315835 478979 := bstep (se 1 (by rfl) ⟨359234, by rfl⟩ : syracuseStep 478979 = 718469) B718469
theorem B479009 : Blo 315835 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B479027 : Blo 315835 479027 := bstep (se 1 (by rfl) ⟨359270, by rfl⟩ : syracuseStep 479027 = 718541) B718541
theorem B479057 : Blo 315835 479057 := bstep (se 2 (by rfl) ⟨179646, by rfl⟩ : syracuseStep 479057 = 359293) B359293
theorem B479075 : Blo 315835 479075 := bstep (se 1 (by rfl) ⟨359306, by rfl⟩ : syracuseStep 479075 = 718613) B718613
theorem B479105 : Blo 315835 479105 := bstep (se 2 (by rfl) ⟨179664, by rfl⟩ : syracuseStep 479105 = 359329) B359329
theorem B675715 : Blo 315835 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B479123 : Blo 315835 479123 := bstep (se 1 (by rfl) ⟨359342, by rfl⟩ : syracuseStep 479123 = 718685) B718685
theorem B479153 : Blo 315835 479153 := bstep (se 2 (by rfl) ⟨179682, by rfl⟩ : syracuseStep 479153 = 359365) B359365
theorem B479171 : Blo 315835 479171 := bstep (se 1 (by rfl) ⟨359378, by rfl⟩ : syracuseStep 479171 = 718757) B718757
theorem B479201 : Blo 315835 479201 := bstep (se 2 (by rfl) ⟨179700, by rfl⟩ : syracuseStep 479201 = 359401) B359401
theorem B1069037 : Blo 315835 1069037 := bstep (se 3 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 1069037 = 400889) B400889
theorem B479219 : Blo 315835 479219 := bstep (se 1 (by rfl) ⟨359414, by rfl⟩ : syracuseStep 479219 = 718829) B718829
theorem B479249 : Blo 315835 479249 := bstep (se 2 (by rfl) ⟨179718, by rfl⟩ : syracuseStep 479249 = 359437) B359437
theorem B1069091 : Blo 315835 1069091 := bstep (se 1 (by rfl) ⟨801818, by rfl⟩ : syracuseStep 1069091 = 1603637) B1603637
theorem B479267 : Blo 315835 479267 := bstep (se 1 (by rfl) ⟨359450, by rfl⟩ : syracuseStep 479267 = 718901) B718901
theorem B479297 : Blo 315835 479297 := bstep (se 2 (by rfl) ⟨179736, by rfl⟩ : syracuseStep 479297 = 359473) B359473
theorem B806993 : Blo 315835 806993 := bstep (se 2 (by rfl) ⟨302622, by rfl⟩ : syracuseStep 806993 = 605245) B605245
theorem B479315 : Blo 315835 479315 := bstep (se 1 (by rfl) ⟨359486, by rfl⟩ : syracuseStep 479315 = 718973) B718973
theorem B479345 : Blo 315835 479345 := bstep (se 2 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 479345 = 359509) B359509
theorem B807043 : Blo 315835 807043 := bstep (se 1 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 807043 = 1210565) B1210565
theorem B479363 : Blo 315835 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B479393 : Blo 315835 479393 := bstep (se 2 (by rfl) ⟨179772, by rfl⟩ : syracuseStep 479393 = 359545) B359545
theorem B479411 : Blo 315835 479411 := bstep (se 1 (by rfl) ⟨359558, by rfl⟩ : syracuseStep 479411 = 719117) B719117
theorem B544961 : Blo 315835 544961 := bstep (se 2 (by rfl) ⟨204360, by rfl⟩ : syracuseStep 544961 = 408721) B408721
theorem B479441 : Blo 315835 479441 := bstep (se 2 (by rfl) ⟨179790, by rfl⟩ : syracuseStep 479441 = 359581) B359581
theorem B479459 : Blo 315835 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B479489 : Blo 315835 479489 := bstep (se 2 (by rfl) ⟨179808, by rfl⟩ : syracuseStep 479489 = 359617) B359617
theorem B807185 : Blo 315835 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B479507 : Blo 315835 479507 := bstep (se 1 (by rfl) ⟨359630, by rfl⟩ : syracuseStep 479507 = 719261) B719261
theorem B1069361 : Blo 315835 1069361 := bstep (se 2 (by rfl) ⟨401010, by rfl⟩ : syracuseStep 1069361 = 802021) B802021
theorem B479537 : Blo 315835 479537 := bstep (se 2 (by rfl) ⟨179826, by rfl⟩ : syracuseStep 479537 = 359653) B359653
theorem B479555 : Blo 315835 479555 := bstep (se 1 (by rfl) ⟨359666, by rfl⟩ : syracuseStep 479555 = 719333) B719333
theorem B479585 : Blo 315835 479585 := bstep (se 2 (by rfl) ⟨179844, by rfl⟩ : syracuseStep 479585 = 359689) B359689
theorem B2183537 : Blo 315835 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B479603 : Blo 315835 479603 := bstep (se 1 (by rfl) ⟨359702, by rfl⟩ : syracuseStep 479603 = 719405) B719405
theorem B479633 : Blo 315835 479633 := bstep (se 2 (by rfl) ⟨179862, by rfl⟩ : syracuseStep 479633 = 359725) B359725
theorem B479651 : Blo 315835 479651 := bstep (se 1 (by rfl) ⟨359738, by rfl⟩ : syracuseStep 479651 = 719477) B719477
theorem B479681 : Blo 315835 479681 := bstep (se 2 (by rfl) ⟨179880, by rfl⟩ : syracuseStep 479681 = 359761) B359761
theorem B315843 : Blo 315835 315843 := bstep (se 1 (by rfl) ⟨236882, by rfl⟩ : syracuseStep 315843 = 473765) B473765
theorem B905681 : Blo 315835 905681 := bstep (se 2 (by rfl) ⟨339630, by rfl⟩ : syracuseStep 905681 = 679261) B679261
theorem B315859 : Blo 315835 315859 := bstep (se 1 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 315859 = 473789) B473789
theorem B479699 : Blo 315835 479699 := bstep (se 1 (by rfl) ⟨359774, by rfl⟩ : syracuseStep 479699 = 719549) B719549
theorem B315875 : Blo 315835 315875 := bstep (se 1 (by rfl) ⟨236906, by rfl⟩ : syracuseStep 315875 = 473813) B473813
theorem B479729 : Blo 315835 479729 := bstep (se 2 (by rfl) ⟨179898, by rfl⟩ : syracuseStep 479729 = 359797) B359797
theorem B315891 : Blo 315835 315891 := bstep (se 1 (by rfl) ⟨236918, by rfl⟩ : syracuseStep 315891 = 473837) B473837
theorem B315907 : Blo 315835 315907 := bstep (se 1 (by rfl) ⟨236930, by rfl⟩ : syracuseStep 315907 = 473861) B473861
theorem B479747 : Blo 315835 479747 := bstep (se 1 (by rfl) ⟨359810, by rfl⟩ : syracuseStep 479747 = 719621) B719621
theorem B643601 : Blo 315835 643601 := bstep (se 2 (by rfl) ⟨241350, by rfl⟩ : syracuseStep 643601 = 482701) B482701
theorem B315923 : Blo 315835 315923 := bstep (se 1 (by rfl) ⟨236942, by rfl⟩ : syracuseStep 315923 = 473885) B473885
theorem B315939 : Blo 315835 315939 := bstep (se 1 (by rfl) ⟨236954, by rfl⟩ : syracuseStep 315939 = 473909) B473909
theorem B315955 : Blo 315835 315955 := bstep (se 1 (by rfl) ⟨236966, by rfl⟩ : syracuseStep 315955 = 473933) B473933
theorem B315971 : Blo 315835 315971 := bstep (se 1 (by rfl) ⟨236978, by rfl⟩ : syracuseStep 315971 = 473957) B473957
theorem B676433 : Blo 315835 676433 := bstep (se 2 (by rfl) ⟨253662, by rfl⟩ : syracuseStep 676433 = 507325) B507325
theorem B315987 : Blo 315835 315987 := bstep (se 1 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 315987 = 473981) B473981
theorem B316003 : Blo 315835 316003 := bstep (se 1 (by rfl) ⟨237002, by rfl⟩ : syracuseStep 316003 = 474005) B474005
theorem B10965617 : Blo 315835 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B1528433 : Blo 315835 1528433 := bstep (se 2 (by rfl) ⟨573162, by rfl⟩ : syracuseStep 1528433 = 1146325) B1146325
theorem B316019 : Blo 315835 316019 := bstep (se 1 (by rfl) ⟨237014, by rfl⟩ : syracuseStep 316019 = 474029) B474029
theorem B316035 : Blo 315835 316035 := bstep (se 1 (by rfl) ⟨237026, by rfl⟩ : syracuseStep 316035 = 474053) B474053
theorem B578179 : Blo 315835 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B316051 : Blo 315835 316051 := bstep (se 1 (by rfl) ⟨237038, by rfl⟩ : syracuseStep 316051 = 474077) B474077
theorem B316067 : Blo 315835 316067 := bstep (se 1 (by rfl) ⟨237050, by rfl⟩ : syracuseStep 316067 = 474101) B474101
theorem B316083 : Blo 315835 316083 := bstep (se 1 (by rfl) ⟨237062, by rfl⟩ : syracuseStep 316083 = 474125) B474125
theorem B316099 : Blo 315835 316099 := bstep (se 1 (by rfl) ⟨237074, by rfl⟩ : syracuseStep 316099 = 474149) B474149
theorem B1200845 : Blo 315835 1200845 := bstep (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) B450317
theorem B316115 : Blo 315835 316115 := bstep (se 1 (by rfl) ⟨237086, by rfl⟩ : syracuseStep 316115 = 474173) B474173
theorem B316131 : Blo 315835 316131 := bstep (se 1 (by rfl) ⟨237098, by rfl⟩ : syracuseStep 316131 = 474197) B474197
theorem B545507 : Blo 315835 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B316147 : Blo 315835 316147 := bstep (se 1 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 316147 = 474221) B474221
theorem B316163 : Blo 315835 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B316179 : Blo 315835 316179 := bstep (se 1 (by rfl) ⟨237134, by rfl⟩ : syracuseStep 316179 = 474269) B474269
theorem B316195 : Blo 315835 316195 := bstep (se 1 (by rfl) ⟨237146, by rfl⟩ : syracuseStep 316195 = 474293) B474293
theorem B316211 : Blo 315835 316211 := bstep (se 1 (by rfl) ⟨237158, by rfl⟩ : syracuseStep 316211 = 474317) B474317
theorem B4117301 : Blo 315835 4117301 := bstep (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) B385997
theorem B316227 : Blo 315835 316227 := bstep (se 1 (by rfl) ⟨237170, by rfl⟩ : syracuseStep 316227 = 474341) B474341
theorem B4051781 : Blo 315835 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B1069901 : Blo 315835 1069901 := bstep (se 3 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 1069901 = 401213) B401213
theorem B316243 : Blo 315835 316243 := bstep (se 1 (by rfl) ⟨237182, by rfl⟩ : syracuseStep 316243 = 474365) B474365
theorem B316259 : Blo 315835 316259 := bstep (se 1 (by rfl) ⟨237194, by rfl⟩ : syracuseStep 316259 = 474389) B474389
theorem B316275 : Blo 315835 316275 := bstep (se 1 (by rfl) ⟨237206, by rfl⟩ : syracuseStep 316275 = 474413) B474413
theorem B316291 : Blo 315835 316291 := bstep (se 1 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 316291 = 474437) B474437
theorem B1069955 : Blo 315835 1069955 := bstep (se 1 (by rfl) ⟨802466, by rfl⟩ : syracuseStep 1069955 = 1604933) B1604933
theorem B1823629 : Blo 315835 1823629 := bstep (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) B683861
theorem B316307 : Blo 315835 316307 := bstep (se 1 (by rfl) ⟨237230, by rfl⟩ : syracuseStep 316307 = 474461) B474461
theorem B316323 : Blo 315835 316323 := bstep (se 1 (by rfl) ⟨237242, by rfl⟩ : syracuseStep 316323 = 474485) B474485
theorem B316339 : Blo 315835 316339 := bstep (se 1 (by rfl) ⟨237254, by rfl⟩ : syracuseStep 316339 = 474509) B474509
theorem B316355 : Blo 315835 316355 := bstep (se 1 (by rfl) ⟨237266, by rfl⟩ : syracuseStep 316355 = 474533) B474533
theorem B316371 : Blo 315835 316371 := bstep (se 1 (by rfl) ⟨237278, by rfl⟩ : syracuseStep 316371 = 474557) B474557
theorem B316387 : Blo 315835 316387 := bstep (se 1 (by rfl) ⟨237290, by rfl⟩ : syracuseStep 316387 = 474581) B474581
theorem B316403 : Blo 315835 316403 := bstep (se 1 (by rfl) ⟨237302, by rfl⟩ : syracuseStep 316403 = 474605) B474605
theorem B316419 : Blo 315835 316419 := bstep (se 1 (by rfl) ⟨237314, by rfl⟩ : syracuseStep 316419 = 474629) B474629
theorem B316435 : Blo 315835 316435 := bstep (se 1 (by rfl) ⟨237326, by rfl⟩ : syracuseStep 316435 = 474653) B474653
theorem B316451 : Blo 315835 316451 := bstep (se 1 (by rfl) ⟨237338, by rfl⟩ : syracuseStep 316451 = 474677) B474677
theorem B316467 : Blo 315835 316467 := bstep (se 1 (by rfl) ⟨237350, by rfl⟩ : syracuseStep 316467 = 474701) B474701
theorem B316483 : Blo 315835 316483 := bstep (se 1 (by rfl) ⟨237362, by rfl⟩ : syracuseStep 316483 = 474725) B474725
theorem B676945 : Blo 315835 676945 := bstep (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) B507709
theorem B316499 : Blo 315835 316499 := bstep (se 1 (by rfl) ⟨237374, by rfl⟩ : syracuseStep 316499 = 474749) B474749
theorem B316515 : Blo 315835 316515 := bstep (se 1 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 316515 = 474773) B474773
theorem B906353 : Blo 315835 906353 := bstep (se 2 (by rfl) ⟨339882, by rfl⟩ : syracuseStep 906353 = 679765) B679765
theorem B316531 : Blo 315835 316531 := bstep (se 1 (by rfl) ⟨237398, by rfl⟩ : syracuseStep 316531 = 474797) B474797
theorem B316547 : Blo 315835 316547 := bstep (se 1 (by rfl) ⟨237410, by rfl⟩ : syracuseStep 316547 = 474821) B474821
theorem B1365133 : Blo 315835 1365133 := bstep (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) B511925
theorem B1070225 : Blo 315835 1070225 := bstep (se 2 (by rfl) ⟨401334, by rfl⟩ : syracuseStep 1070225 = 802669) B802669
theorem B316563 : Blo 315835 316563 := bstep (se 1 (by rfl) ⟨237422, by rfl⟩ : syracuseStep 316563 = 474845) B474845
theorem B382099 : Blo 315835 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B316579 : Blo 315835 316579 := bstep (se 1 (by rfl) ⟨237434, by rfl⟩ : syracuseStep 316579 = 474869) B474869
theorem B316595 : Blo 315835 316595 := bstep (se 1 (by rfl) ⟨237446, by rfl⟩ : syracuseStep 316595 = 474893) B474893
theorem B316611 : Blo 315835 316611 := bstep (se 1 (by rfl) ⟨237458, by rfl⟩ : syracuseStep 316611 = 474917) B474917
theorem B316627 : Blo 315835 316627 := bstep (se 1 (by rfl) ⟨237470, by rfl⟩ : syracuseStep 316627 = 474941) B474941
theorem B316643 : Blo 315835 316643 := bstep (se 1 (by rfl) ⟨237482, by rfl⟩ : syracuseStep 316643 = 474965) B474965
theorem B873713 : Blo 315835 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B808177 : Blo 315835 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B316659 : Blo 315835 316659 := bstep (se 1 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 316659 = 474989) B474989
theorem B316675 : Blo 315835 316675 := bstep (se 1 (by rfl) ⟨237506, by rfl⟩ : syracuseStep 316675 = 475013) B475013
theorem B316691 : Blo 315835 316691 := bstep (se 1 (by rfl) ⟨237518, by rfl⟩ : syracuseStep 316691 = 475037) B475037
theorem B316707 : Blo 315835 316707 := bstep (se 1 (by rfl) ⟨237530, by rfl⟩ : syracuseStep 316707 = 475061) B475061
theorem B1529123 : Blo 315835 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B316723 : Blo 315835 316723 := bstep (se 1 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 316723 = 475085) B475085
theorem B316739 : Blo 315835 316739 := bstep (se 1 (by rfl) ⟨237554, by rfl⟩ : syracuseStep 316739 = 475109) B475109
theorem B316755 : Blo 315835 316755 := bstep (se 1 (by rfl) ⟨237566, by rfl⟩ : syracuseStep 316755 = 475133) B475133
theorem B316771 : Blo 315835 316771 := bstep (se 1 (by rfl) ⟨237578, by rfl⟩ : syracuseStep 316771 = 475157) B475157
theorem B316787 : Blo 315835 316787 := bstep (se 1 (by rfl) ⟨237590, by rfl⟩ : syracuseStep 316787 = 475181) B475181
theorem B316803 : Blo 315835 316803 := bstep (se 1 (by rfl) ⟨237602, by rfl⟩ : syracuseStep 316803 = 475205) B475205
theorem B316819 : Blo 315835 316819 := bstep (se 1 (by rfl) ⟨237614, by rfl⟩ : syracuseStep 316819 = 475229) B475229
theorem B316835 : Blo 315835 316835 := bstep (se 1 (by rfl) ⟨237626, by rfl⟩ : syracuseStep 316835 = 475253) B475253
theorem B316851 : Blo 315835 316851 := bstep (se 1 (by rfl) ⟨237638, by rfl⟩ : syracuseStep 316851 = 475277) B475277
theorem B316867 : Blo 315835 316867 := bstep (se 1 (by rfl) ⟨237650, by rfl⟩ : syracuseStep 316867 = 475301) B475301
theorem B316883 : Blo 315835 316883 := bstep (se 1 (by rfl) ⟨237662, by rfl⟩ : syracuseStep 316883 = 475325) B475325
theorem B316899 : Blo 315835 316899 := bstep (se 1 (by rfl) ⟨237674, by rfl⟩ : syracuseStep 316899 = 475349) B475349
theorem B316915 : Blo 315835 316915 := bstep (se 1 (by rfl) ⟨237686, by rfl⟩ : syracuseStep 316915 = 475373) B475373
theorem B316931 : Blo 315835 316931 := bstep (se 1 (by rfl) ⟨237698, by rfl⟩ : syracuseStep 316931 = 475397) B475397
theorem B808451 : Blo 315835 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B316947 : Blo 315835 316947 := bstep (se 1 (by rfl) ⟨237710, by rfl⟩ : syracuseStep 316947 = 475421) B475421
theorem B316963 : Blo 315835 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B316979 : Blo 315835 316979 := bstep (se 1 (by rfl) ⟨237734, by rfl⟩ : syracuseStep 316979 = 475469) B475469
theorem B316995 : Blo 315835 316995 := bstep (se 1 (by rfl) ⟨237746, by rfl⟩ : syracuseStep 316995 = 475493) B475493
theorem B317011 : Blo 315835 317011 := bstep (se 1 (by rfl) ⟨237758, by rfl⟩ : syracuseStep 317011 = 475517) B475517
theorem B317027 : Blo 315835 317027 := bstep (se 1 (by rfl) ⟨237770, by rfl⟩ : syracuseStep 317027 = 475541) B475541
theorem B317043 : Blo 315835 317043 := bstep (se 1 (by rfl) ⟨237782, by rfl⟩ : syracuseStep 317043 = 475565) B475565
theorem B317059 : Blo 315835 317059 := bstep (se 1 (by rfl) ⟨237794, by rfl⟩ : syracuseStep 317059 = 475589) B475589
theorem B317075 : Blo 315835 317075 := bstep (se 1 (by rfl) ⟨237806, by rfl⟩ : syracuseStep 317075 = 475613) B475613
theorem B317091 : Blo 315835 317091 := bstep (se 1 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 317091 = 475637) B475637
theorem B382627 : Blo 315835 382627 := bstep (se 1 (by rfl) ⟨286970, by rfl⟩ : syracuseStep 382627 = 573941) B573941
theorem B1070765 : Blo 315835 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B317107 : Blo 315835 317107 := bstep (se 1 (by rfl) ⟨237830, by rfl⟩ : syracuseStep 317107 = 475661) B475661
theorem B317123 : Blo 315835 317123 := bstep (se 1 (by rfl) ⟨237842, by rfl⟩ : syracuseStep 317123 = 475685) B475685
theorem B808643 : Blo 315835 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B317139 : Blo 315835 317139 := bstep (se 1 (by rfl) ⟨237854, by rfl⟩ : syracuseStep 317139 = 475709) B475709
theorem B317155 : Blo 315835 317155 := bstep (se 1 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 317155 = 475733) B475733
theorem B1070819 : Blo 315835 1070819 := bstep (se 1 (by rfl) ⟨803114, by rfl⟩ : syracuseStep 1070819 = 1606229) B1606229
theorem B972515 : Blo 315835 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B317171 : Blo 315835 317171 := bstep (se 1 (by rfl) ⟨237878, by rfl⟩ : syracuseStep 317171 = 475757) B475757
theorem B317187 : Blo 315835 317187 := bstep (se 1 (by rfl) ⟨237890, by rfl⟩ : syracuseStep 317187 = 475781) B475781
theorem B317203 : Blo 315835 317203 := bstep (se 1 (by rfl) ⟨237902, by rfl⟩ : syracuseStep 317203 = 475805) B475805
theorem B317219 : Blo 315835 317219 := bstep (se 1 (by rfl) ⟨237914, by rfl⟩ : syracuseStep 317219 = 475829) B475829
theorem B317235 : Blo 315835 317235 := bstep (se 1 (by rfl) ⟨237926, by rfl⟩ : syracuseStep 317235 = 475853) B475853
theorem B317251 : Blo 315835 317251 := bstep (se 1 (by rfl) ⟨237938, by rfl⟩ : syracuseStep 317251 = 475877) B475877
theorem B317267 : Blo 315835 317267 := bstep (se 1 (by rfl) ⟨237950, by rfl⟩ : syracuseStep 317267 = 475901) B475901
theorem B317283 : Blo 315835 317283 := bstep (se 1 (by rfl) ⟨237962, by rfl⟩ : syracuseStep 317283 = 475925) B475925
theorem B317299 : Blo 315835 317299 := bstep (se 1 (by rfl) ⟨237974, by rfl⟩ : syracuseStep 317299 = 475949) B475949
theorem B317315 : Blo 315835 317315 := bstep (se 1 (by rfl) ⟨237986, by rfl⟩ : syracuseStep 317315 = 475973) B475973
theorem B907139 : Blo 315835 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B317331 : Blo 315835 317331 := bstep (se 1 (by rfl) ⟨237998, by rfl⟩ : syracuseStep 317331 = 475997) B475997
theorem B317347 : Blo 315835 317347 := bstep (se 1 (by rfl) ⟨238010, by rfl⟩ : syracuseStep 317347 = 476021) B476021
theorem B317363 : Blo 315835 317363 := bstep (se 1 (by rfl) ⟨238022, by rfl⟩ : syracuseStep 317363 = 476045) B476045
theorem B317379 : Blo 315835 317379 := bstep (se 1 (by rfl) ⟨238034, by rfl⟩ : syracuseStep 317379 = 476069) B476069
theorem B317395 : Blo 315835 317395 := bstep (se 1 (by rfl) ⟨238046, by rfl⟩ : syracuseStep 317395 = 476093) B476093
theorem B317411 : Blo 315835 317411 := bstep (se 1 (by rfl) ⟨238058, by rfl⟩ : syracuseStep 317411 = 476117) B476117
theorem B1071089 : Blo 315835 1071089 := bstep (se 2 (by rfl) ⟨401658, by rfl⟩ : syracuseStep 1071089 = 803317) B803317
theorem B317427 : Blo 315835 317427 := bstep (se 1 (by rfl) ⟨238070, by rfl⟩ : syracuseStep 317427 = 476141) B476141
theorem B317443 : Blo 315835 317443 := bstep (se 1 (by rfl) ⟨238082, by rfl⟩ : syracuseStep 317443 = 476165) B476165
theorem B317459 : Blo 315835 317459 := bstep (se 1 (by rfl) ⟨238094, by rfl⟩ : syracuseStep 317459 = 476189) B476189
theorem B317475 : Blo 315835 317475 := bstep (se 1 (by rfl) ⟨238106, by rfl⟩ : syracuseStep 317475 = 476213) B476213
theorem B317491 : Blo 315835 317491 := bstep (se 1 (by rfl) ⟨238118, by rfl⟩ : syracuseStep 317491 = 476237) B476237
theorem B317507 : Blo 315835 317507 := bstep (se 1 (by rfl) ⟨238130, by rfl⟩ : syracuseStep 317507 = 476261) B476261
theorem B317523 : Blo 315835 317523 := bstep (se 1 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 317523 = 476285) B476285
theorem B317539 : Blo 315835 317539 := bstep (se 1 (by rfl) ⟨238154, by rfl⟩ : syracuseStep 317539 = 476309) B476309
theorem B481393 : Blo 315835 481393 := bstep (se 2 (by rfl) ⟨180522, by rfl⟩ : syracuseStep 481393 = 361045) B361045
theorem B317555 : Blo 315835 317555 := bstep (se 1 (by rfl) ⟨238166, by rfl⟩ : syracuseStep 317555 = 476333) B476333
theorem B317571 : Blo 315835 317571 := bstep (se 1 (by rfl) ⟨238178, by rfl⟩ : syracuseStep 317571 = 476357) B476357
theorem B710801 : Blo 315835 710801 := bstep (se 2 (by rfl) ⟨266550, by rfl⟩ : syracuseStep 710801 = 533101) B533101
theorem B317587 : Blo 315835 317587 := bstep (se 1 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 317587 = 476381) B476381
theorem B710819 : Blo 315835 710819 := bstep (se 1 (by rfl) ⟨533114, by rfl⟩ : syracuseStep 710819 = 1066229) B1066229
theorem B317603 : Blo 315835 317603 := bstep (se 1 (by rfl) ⟨238202, by rfl⟩ : syracuseStep 317603 = 476405) B476405
theorem B317619 : Blo 315835 317619 := bstep (se 1 (by rfl) ⟨238214, by rfl⟩ : syracuseStep 317619 = 476429) B476429
theorem B317635 : Blo 315835 317635 := bstep (se 1 (by rfl) ⟨238226, by rfl⟩ : syracuseStep 317635 = 476453) B476453
theorem B2087117 : Blo 315835 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B907469 : Blo 315835 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B317651 : Blo 315835 317651 := bstep (se 1 (by rfl) ⟨238238, by rfl⟩ : syracuseStep 317651 = 476477) B476477
theorem B317667 : Blo 315835 317667 := bstep (se 1 (by rfl) ⟨238250, by rfl⟩ : syracuseStep 317667 = 476501) B476501
theorem B317683 : Blo 315835 317683 := bstep (se 1 (by rfl) ⟨238262, by rfl⟩ : syracuseStep 317683 = 476525) B476525
theorem B317699 : Blo 315835 317699 := bstep (se 1 (by rfl) ⟨238274, by rfl⟩ : syracuseStep 317699 = 476549) B476549
theorem B907537 : Blo 315835 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B317715 : Blo 315835 317715 := bstep (se 1 (by rfl) ⟨238286, by rfl⟩ : syracuseStep 317715 = 476573) B476573
theorem B317731 : Blo 315835 317731 := bstep (se 1 (by rfl) ⟨238298, by rfl⟩ : syracuseStep 317731 = 476597) B476597
theorem B317747 : Blo 315835 317747 := bstep (se 1 (by rfl) ⟨238310, by rfl⟩ : syracuseStep 317747 = 476621) B476621
theorem B317763 : Blo 315835 317763 := bstep (se 1 (by rfl) ⟨238322, by rfl⟩ : syracuseStep 317763 = 476645) B476645
theorem B317779 : Blo 315835 317779 := bstep (se 1 (by rfl) ⟨238334, by rfl⟩ : syracuseStep 317779 = 476669) B476669
theorem B317795 : Blo 315835 317795 := bstep (se 1 (by rfl) ⟨238346, by rfl⟩ : syracuseStep 317795 = 476693) B476693
theorem B317811 : Blo 315835 317811 := bstep (se 1 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 317811 = 476717) B476717
theorem B317827 : Blo 315835 317827 := bstep (se 1 (by rfl) ⟨238370, by rfl⟩ : syracuseStep 317827 = 476741) B476741
theorem B317843 : Blo 315835 317843 := bstep (se 1 (by rfl) ⟨238382, by rfl⟩ : syracuseStep 317843 = 476765) B476765
theorem B317859 : Blo 315835 317859 := bstep (se 1 (by rfl) ⟨238394, by rfl⟩ : syracuseStep 317859 = 476789) B476789
theorem B711089 : Blo 315835 711089 := bstep (se 2 (by rfl) ⟨266658, by rfl⟩ : syracuseStep 711089 = 533317) B533317
theorem B317875 : Blo 315835 317875 := bstep (se 1 (by rfl) ⟨238406, by rfl⟩ : syracuseStep 317875 = 476813) B476813
theorem B711107 : Blo 315835 711107 := bstep (se 1 (by rfl) ⟨533330, by rfl⟩ : syracuseStep 711107 = 1066661) B1066661
theorem B317891 : Blo 315835 317891 := bstep (se 1 (by rfl) ⟨238418, by rfl⟩ : syracuseStep 317891 = 476837) B476837
theorem B317907 : Blo 315835 317907 := bstep (se 1 (by rfl) ⟨238430, by rfl⟩ : syracuseStep 317907 = 476861) B476861
theorem B317923 : Blo 315835 317923 := bstep (se 1 (by rfl) ⟨238442, by rfl⟩ : syracuseStep 317923 = 476885) B476885
theorem B317939 : Blo 315835 317939 := bstep (se 1 (by rfl) ⟨238454, by rfl⟩ : syracuseStep 317939 = 476909) B476909
theorem B317955 : Blo 315835 317955 := bstep (se 1 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 317955 = 476933) B476933
theorem B1071629 : Blo 315835 1071629 := bstep (se 3 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 1071629 = 401861) B401861
theorem B317971 : Blo 315835 317971 := bstep (se 1 (by rfl) ⟨238478, by rfl⟩ : syracuseStep 317971 = 476957) B476957
theorem B317987 : Blo 315835 317987 := bstep (se 1 (by rfl) ⟨238490, by rfl⟩ : syracuseStep 317987 = 476981) B476981
theorem B907811 : Blo 315835 907811 := bstep (se 1 (by rfl) ⟨680858, by rfl⟩ : syracuseStep 907811 = 1361717) B1361717
theorem B678449 : Blo 315835 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B318003 : Blo 315835 318003 := bstep (se 1 (by rfl) ⟨238502, by rfl⟩ : syracuseStep 318003 = 477005) B477005
theorem B1071683 : Blo 315835 1071683 := bstep (se 1 (by rfl) ⟨803762, by rfl⟩ : syracuseStep 1071683 = 1607525) B1607525
theorem B318019 : Blo 315835 318019 := bstep (se 1 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 318019 = 477029) B477029
theorem B318035 : Blo 315835 318035 := bstep (se 1 (by rfl) ⟨238526, by rfl⟩ : syracuseStep 318035 = 477053) B477053
theorem B318051 : Blo 315835 318051 := bstep (se 1 (by rfl) ⟨238538, by rfl⟩ : syracuseStep 318051 = 477077) B477077
theorem B809585 : Blo 315835 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B318067 : Blo 315835 318067 := bstep (se 1 (by rfl) ⟨238550, by rfl⟩ : syracuseStep 318067 = 477101) B477101
theorem B318083 : Blo 315835 318083 := bstep (se 1 (by rfl) ⟨238562, by rfl⟩ : syracuseStep 318083 = 477125) B477125
theorem B318099 : Blo 315835 318099 := bstep (se 1 (by rfl) ⟨238574, by rfl⟩ : syracuseStep 318099 = 477149) B477149
theorem B318115 : Blo 315835 318115 := bstep (se 1 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 318115 = 477173) B477173
theorem B318131 : Blo 315835 318131 := bstep (se 1 (by rfl) ⟨238598, by rfl⟩ : syracuseStep 318131 = 477197) B477197
theorem B318147 : Blo 315835 318147 := bstep (se 1 (by rfl) ⟨238610, by rfl⟩ : syracuseStep 318147 = 477221) B477221
theorem B711377 : Blo 315835 711377 := bstep (se 2 (by rfl) ⟨266766, by rfl⟩ : syracuseStep 711377 = 533533) B533533
theorem B318163 : Blo 315835 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B711395 : Blo 315835 711395 := bstep (se 1 (by rfl) ⟨533546, by rfl⟩ : syracuseStep 711395 = 1067093) B1067093
theorem B318179 : Blo 315835 318179 := bstep (se 1 (by rfl) ⟨238634, by rfl⟩ : syracuseStep 318179 = 477269) B477269
theorem B318195 : Blo 315835 318195 := bstep (se 1 (by rfl) ⟨238646, by rfl⟩ : syracuseStep 318195 = 477293) B477293
theorem B318211 : Blo 315835 318211 := bstep (se 1 (by rfl) ⟨238658, by rfl⟩ : syracuseStep 318211 = 477317) B477317
theorem B1202957 : Blo 315835 1202957 := bstep (se 3 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 1202957 = 451109) B451109
theorem B318227 : Blo 315835 318227 := bstep (se 1 (by rfl) ⟨238670, by rfl⟩ : syracuseStep 318227 = 477341) B477341
theorem B318243 : Blo 315835 318243 := bstep (se 1 (by rfl) ⟨238682, by rfl⟩ : syracuseStep 318243 = 477365) B477365
theorem B318259 : Blo 315835 318259 := bstep (se 1 (by rfl) ⟨238694, by rfl⟩ : syracuseStep 318259 = 477389) B477389
theorem B318275 : Blo 315835 318275 := bstep (se 1 (by rfl) ⟨238706, by rfl⟩ : syracuseStep 318275 = 477413) B477413
theorem B1071953 : Blo 315835 1071953 := bstep (se 2 (by rfl) ⟨401982, by rfl⟩ : syracuseStep 1071953 = 803965) B803965
theorem B318291 : Blo 315835 318291 := bstep (se 1 (by rfl) ⟨238718, by rfl⟩ : syracuseStep 318291 = 477437) B477437
theorem B318307 : Blo 315835 318307 := bstep (se 1 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 318307 = 477461) B477461
theorem B318323 : Blo 315835 318323 := bstep (se 1 (by rfl) ⟨238742, by rfl⟩ : syracuseStep 318323 = 477485) B477485
theorem B318339 : Blo 315835 318339 := bstep (se 1 (by rfl) ⟨238754, by rfl⟩ : syracuseStep 318339 = 477509) B477509
theorem B318355 : Blo 315835 318355 := bstep (se 1 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 318355 = 477533) B477533
theorem B318371 : Blo 315835 318371 := bstep (se 1 (by rfl) ⟨238778, by rfl⟩ : syracuseStep 318371 = 477557) B477557
theorem B318387 : Blo 315835 318387 := bstep (se 1 (by rfl) ⟨238790, by rfl⟩ : syracuseStep 318387 = 477581) B477581
theorem B678851 : Blo 315835 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B318403 : Blo 315835 318403 := bstep (se 1 (by rfl) ⟨238802, by rfl⟩ : syracuseStep 318403 = 477605) B477605
theorem B318419 : Blo 315835 318419 := bstep (se 1 (by rfl) ⟨238814, by rfl⟩ : syracuseStep 318419 = 477629) B477629
theorem B318435 : Blo 315835 318435 := bstep (se 1 (by rfl) ⟨238826, by rfl⟩ : syracuseStep 318435 = 477653) B477653
theorem B711665 : Blo 315835 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B318451 : Blo 315835 318451 := bstep (se 1 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 318451 = 477677) B477677
theorem B711683 : Blo 315835 711683 := bstep (se 1 (by rfl) ⟨533762, by rfl⟩ : syracuseStep 711683 = 1067525) B1067525
theorem B318467 : Blo 315835 318467 := bstep (se 1 (by rfl) ⟨238850, by rfl⟩ : syracuseStep 318467 = 477701) B477701
theorem B1530893 : Blo 315835 1530893 := bstep (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) B574085
theorem B318483 : Blo 315835 318483 := bstep (se 1 (by rfl) ⟨238862, by rfl⟩ : syracuseStep 318483 = 477725) B477725
theorem B318499 : Blo 315835 318499 := bstep (se 1 (by rfl) ⟨238874, by rfl⟩ : syracuseStep 318499 = 477749) B477749
theorem B318515 : Blo 315835 318515 := bstep (se 1 (by rfl) ⟨238886, by rfl⟩ : syracuseStep 318515 = 477773) B477773
theorem B318531 : Blo 315835 318531 := bstep (se 1 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 318531 = 477797) B477797
theorem B318547 : Blo 315835 318547 := bstep (se 1 (by rfl) ⟨238910, by rfl⟩ : syracuseStep 318547 = 477821) B477821
theorem B318563 : Blo 315835 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B318579 : Blo 315835 318579 := bstep (se 1 (by rfl) ⟨238934, by rfl⟩ : syracuseStep 318579 = 477869) B477869
theorem B318595 : Blo 315835 318595 := bstep (se 1 (by rfl) ⟨238946, by rfl⟩ : syracuseStep 318595 = 477893) B477893
theorem B318611 : Blo 315835 318611 := bstep (se 1 (by rfl) ⟨238958, by rfl⟩ : syracuseStep 318611 = 477917) B477917
theorem B318627 : Blo 315835 318627 := bstep (se 1 (by rfl) ⟨238970, by rfl⟩ : syracuseStep 318627 = 477941) B477941
theorem B318643 : Blo 315835 318643 := bstep (se 1 (by rfl) ⟨238982, by rfl⟩ : syracuseStep 318643 = 477965) B477965
theorem B318659 : Blo 315835 318659 := bstep (se 1 (by rfl) ⟨238994, by rfl⟩ : syracuseStep 318659 = 477989) B477989
theorem B318675 : Blo 315835 318675 := bstep (se 1 (by rfl) ⟨239006, by rfl⟩ : syracuseStep 318675 = 478013) B478013
theorem B318691 : Blo 315835 318691 := bstep (se 1 (by rfl) ⟨239018, by rfl⟩ : syracuseStep 318691 = 478037) B478037
theorem B318707 : Blo 315835 318707 := bstep (se 1 (by rfl) ⟨239030, by rfl⟩ : syracuseStep 318707 = 478061) B478061
theorem B318723 : Blo 315835 318723 := bstep (se 1 (by rfl) ⟨239042, by rfl⟩ : syracuseStep 318723 = 478085) B478085
theorem B711953 : Blo 315835 711953 := bstep (se 2 (by rfl) ⟨266982, by rfl⟩ : syracuseStep 711953 = 533965) B533965
theorem B318739 : Blo 315835 318739 := bstep (se 1 (by rfl) ⟨239054, by rfl⟩ : syracuseStep 318739 = 478109) B478109
theorem B711971 : Blo 315835 711971 := bstep (se 1 (by rfl) ⟨533978, by rfl⟩ : syracuseStep 711971 = 1067957) B1067957
theorem B318755 : Blo 315835 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B318771 : Blo 315835 318771 := bstep (se 1 (by rfl) ⟨239078, by rfl⟩ : syracuseStep 318771 = 478157) B478157
theorem B318787 : Blo 315835 318787 := bstep (se 1 (by rfl) ⟨239090, by rfl⟩ : syracuseStep 318787 = 478181) B478181
theorem B318803 : Blo 315835 318803 := bstep (se 1 (by rfl) ⟨239102, by rfl⟩ : syracuseStep 318803 = 478205) B478205
theorem B3038563 : Blo 315835 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B318819 : Blo 315835 318819 := bstep (se 1 (by rfl) ⟨239114, by rfl⟩ : syracuseStep 318819 = 478229) B478229
theorem B1072493 : Blo 315835 1072493 := bstep (se 3 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 1072493 = 402185) B402185
theorem B908653 : Blo 315835 908653 := bstep (se 3 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 908653 = 340745) B340745
theorem B318835 : Blo 315835 318835 := bstep (se 1 (by rfl) ⟨239126, by rfl⟩ : syracuseStep 318835 = 478253) B478253
theorem B318851 : Blo 315835 318851 := bstep (se 1 (by rfl) ⟨239138, by rfl⟩ : syracuseStep 318851 = 478277) B478277
theorem B1531277 : Blo 315835 1531277 := bstep (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) B574229
theorem B318867 : Blo 315835 318867 := bstep (se 1 (by rfl) ⟨239150, by rfl⟩ : syracuseStep 318867 = 478301) B478301
theorem B1072547 : Blo 315835 1072547 := bstep (se 1 (by rfl) ⟨804410, by rfl⟩ : syracuseStep 1072547 = 1608821) B1608821
theorem B318883 : Blo 315835 318883 := bstep (se 1 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 318883 = 478325) B478325
theorem B318899 : Blo 315835 318899 := bstep (se 1 (by rfl) ⟨239174, by rfl⟩ : syracuseStep 318899 = 478349) B478349
theorem B482755 : Blo 315835 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B318915 : Blo 315835 318915 := bstep (se 1 (by rfl) ⟨239186, by rfl⟩ : syracuseStep 318915 = 478373) B478373
theorem B318931 : Blo 315835 318931 := bstep (se 1 (by rfl) ⟨239198, by rfl⟩ : syracuseStep 318931 = 478397) B478397
theorem B318947 : Blo 315835 318947 := bstep (se 1 (by rfl) ⟨239210, by rfl⟩ : syracuseStep 318947 = 478421) B478421
theorem B318963 : Blo 315835 318963 := bstep (se 1 (by rfl) ⟨239222, by rfl⟩ : syracuseStep 318963 = 478445) B478445
theorem B318979 : Blo 315835 318979 := bstep (se 1 (by rfl) ⟨239234, by rfl⟩ : syracuseStep 318979 = 478469) B478469
theorem B908813 : Blo 315835 908813 := bstep (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) B340805
theorem B318995 : Blo 315835 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B319011 : Blo 315835 319011 := bstep (se 1 (by rfl) ⟨239258, by rfl⟩ : syracuseStep 319011 = 478517) B478517
theorem B712241 : Blo 315835 712241 := bstep (se 2 (by rfl) ⟨267090, by rfl⟩ : syracuseStep 712241 = 534181) B534181
theorem B1203761 : Blo 315835 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B319027 : Blo 315835 319027 := bstep (se 1 (by rfl) ⟨239270, by rfl⟩ : syracuseStep 319027 = 478541) B478541
theorem B1728049 : Blo 315835 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B712259 : Blo 315835 712259 := bstep (se 1 (by rfl) ⟨534194, by rfl⟩ : syracuseStep 712259 = 1068389) B1068389
theorem B319043 : Blo 315835 319043 := bstep (se 1 (by rfl) ⟨239282, by rfl⟩ : syracuseStep 319043 = 478565) B478565
theorem B319059 : Blo 315835 319059 := bstep (se 1 (by rfl) ⟨239294, by rfl⟩ : syracuseStep 319059 = 478589) B478589
theorem B319075 : Blo 315835 319075 := bstep (se 1 (by rfl) ⟨239306, by rfl⟩ : syracuseStep 319075 = 478613) B478613
theorem B319091 : Blo 315835 319091 := bstep (se 1 (by rfl) ⟨239318, by rfl⟩ : syracuseStep 319091 = 478637) B478637
theorem B319107 : Blo 315835 319107 := bstep (se 1 (by rfl) ⟨239330, by rfl⟩ : syracuseStep 319107 = 478661) B478661
theorem B319123 : Blo 315835 319123 := bstep (se 1 (by rfl) ⟨239342, by rfl⟩ : syracuseStep 319123 = 478685) B478685
theorem B319139 : Blo 315835 319139 := bstep (se 1 (by rfl) ⟨239354, by rfl⟩ : syracuseStep 319139 = 478709) B478709
theorem B1072817 : Blo 315835 1072817 := bstep (se 2 (by rfl) ⟨402306, by rfl⟩ : syracuseStep 1072817 = 804613) B804613
theorem B319155 : Blo 315835 319155 := bstep (se 1 (by rfl) ⟨239366, by rfl⟩ : syracuseStep 319155 = 478733) B478733
theorem B319171 : Blo 315835 319171 := bstep (se 1 (by rfl) ⟨239378, by rfl⟩ : syracuseStep 319171 = 478757) B478757
theorem B908995 : Blo 315835 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1892045 : Blo 315835 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B319187 : Blo 315835 319187 := bstep (se 1 (by rfl) ⟨239390, by rfl⟩ : syracuseStep 319187 = 478781) B478781
theorem B483041 : Blo 315835 483041 := bstep (se 2 (by rfl) ⟨181140, by rfl⟩ : syracuseStep 483041 = 362281) B362281
theorem B319203 : Blo 315835 319203 := bstep (se 1 (by rfl) ⟨239402, by rfl⟩ : syracuseStep 319203 = 478805) B478805
theorem B450289 : Blo 315835 450289 := bstep (se 2 (by rfl) ⟨168858, by rfl⟩ : syracuseStep 450289 = 337717) B337717
theorem B319219 : Blo 315835 319219 := bstep (se 1 (by rfl) ⟨239414, by rfl⟩ : syracuseStep 319219 = 478829) B478829
theorem B319235 : Blo 315835 319235 := bstep (se 1 (by rfl) ⟨239426, by rfl⟩ : syracuseStep 319235 = 478853) B478853
theorem B319251 : Blo 315835 319251 := bstep (se 1 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 319251 = 478877) B478877
theorem B319267 : Blo 315835 319267 := bstep (se 1 (by rfl) ⟨239450, by rfl⟩ : syracuseStep 319267 = 478901) B478901
theorem B319283 : Blo 315835 319283 := bstep (se 1 (by rfl) ⟨239462, by rfl⟩ : syracuseStep 319283 = 478925) B478925
theorem B679747 : Blo 315835 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B319299 : Blo 315835 319299 := bstep (se 1 (by rfl) ⟨239474, by rfl⟩ : syracuseStep 319299 = 478949) B478949
theorem B2285381 : Blo 315835 2285381 := bstep (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) B428509
theorem B712529 : Blo 315835 712529 := bstep (se 2 (by rfl) ⟨267198, by rfl⟩ : syracuseStep 712529 = 534397) B534397
theorem B319315 : Blo 315835 319315 := bstep (se 1 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 319315 = 478973) B478973
theorem B712547 : Blo 315835 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B319331 : Blo 315835 319331 := bstep (se 1 (by rfl) ⟨239498, by rfl⟩ : syracuseStep 319331 = 478997) B478997
theorem B319347 : Blo 315835 319347 := bstep (se 1 (by rfl) ⟨239510, by rfl⟩ : syracuseStep 319347 = 479021) B479021
theorem B319363 : Blo 315835 319363 := bstep (se 1 (by rfl) ⟨239522, by rfl⟩ : syracuseStep 319363 = 479045) B479045
theorem B319379 : Blo 315835 319379 := bstep (se 1 (by rfl) ⟨239534, by rfl⟩ : syracuseStep 319379 = 479069) B479069
theorem B319395 : Blo 315835 319395 := bstep (se 1 (by rfl) ⟨239546, by rfl⟩ : syracuseStep 319395 = 479093) B479093
theorem B319411 : Blo 315835 319411 := bstep (se 1 (by rfl) ⟨239558, by rfl⟩ : syracuseStep 319411 = 479117) B479117
theorem B319427 : Blo 315835 319427 := bstep (se 1 (by rfl) ⟨239570, by rfl⟩ : syracuseStep 319427 = 479141) B479141
theorem B319443 : Blo 315835 319443 := bstep (se 1 (by rfl) ⟨239582, by rfl⟩ : syracuseStep 319443 = 479165) B479165
theorem B319459 : Blo 315835 319459 := bstep (se 1 (by rfl) ⟨239594, by rfl⟩ : syracuseStep 319459 = 479189) B479189
theorem B319475 : Blo 315835 319475 := bstep (se 1 (by rfl) ⟨239606, by rfl⟩ : syracuseStep 319475 = 479213) B479213
theorem B319491 : Blo 315835 319491 := bstep (se 1 (by rfl) ⟨239618, by rfl⟩ : syracuseStep 319491 = 479237) B479237
theorem B385043 : Blo 315835 385043 := bstep (se 1 (by rfl) ⟨288782, by rfl⟩ : syracuseStep 385043 = 577565) B577565
theorem B319507 : Blo 315835 319507 := bstep (se 1 (by rfl) ⟨239630, by rfl⟩ : syracuseStep 319507 = 479261) B479261
theorem B319523 : Blo 315835 319523 := bstep (se 1 (by rfl) ⟨239642, by rfl⟩ : syracuseStep 319523 = 479285) B479285
theorem B319539 : Blo 315835 319539 := bstep (se 1 (by rfl) ⟨239654, by rfl⟩ : syracuseStep 319539 = 479309) B479309
theorem B450625 : Blo 315835 450625 := bstep (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) B337969
theorem B319555 : Blo 315835 319555 := bstep (se 1 (by rfl) ⟨239666, by rfl⟩ : syracuseStep 319555 = 479333) B479333
theorem B319571 : Blo 315835 319571 := bstep (se 1 (by rfl) ⟨239678, by rfl⟩ : syracuseStep 319571 = 479357) B479357
theorem B319587 : Blo 315835 319587 := bstep (se 1 (by rfl) ⟨239690, by rfl⟩ : syracuseStep 319587 = 479381) B479381
theorem B712817 : Blo 315835 712817 := bstep (se 2 (by rfl) ⟨267306, by rfl⟩ : syracuseStep 712817 = 534613) B534613
theorem B319603 : Blo 315835 319603 := bstep (se 1 (by rfl) ⟨239702, by rfl⟩ : syracuseStep 319603 = 479405) B479405
theorem B712835 : Blo 315835 712835 := bstep (se 1 (by rfl) ⟨534626, by rfl⟩ : syracuseStep 712835 = 1069253) B1069253
theorem B319619 : Blo 315835 319619 := bstep (se 1 (by rfl) ⟨239714, by rfl⟩ : syracuseStep 319619 = 479429) B479429
theorem B319635 : Blo 315835 319635 := bstep (se 1 (by rfl) ⟨239726, by rfl⟩ : syracuseStep 319635 = 479453) B479453
theorem B319651 : Blo 315835 319651 := bstep (se 1 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 319651 = 479477) B479477
theorem B319667 : Blo 315835 319667 := bstep (se 1 (by rfl) ⟨239750, by rfl⟩ : syracuseStep 319667 = 479501) B479501
theorem B319683 : Blo 315835 319683 := bstep (se 1 (by rfl) ⟨239762, by rfl⟩ : syracuseStep 319683 = 479525) B479525
theorem B1204429 : Blo 315835 1204429 := bstep (se 3 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 1204429 = 451661) B451661
theorem B1073357 : Blo 315835 1073357 := bstep (se 3 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 1073357 = 402509) B402509
theorem B319699 : Blo 315835 319699 := bstep (se 1 (by rfl) ⟨239774, by rfl⟩ : syracuseStep 319699 = 479549) B479549
theorem B319715 : Blo 315835 319715 := bstep (se 1 (by rfl) ⟨239786, by rfl⟩ : syracuseStep 319715 = 479573) B479573
theorem B319731 : Blo 315835 319731 := bstep (se 1 (by rfl) ⟨239798, by rfl⟩ : syracuseStep 319731 = 479597) B479597
theorem B1073411 : Blo 315835 1073411 := bstep (se 1 (by rfl) ⟨805058, by rfl⟩ : syracuseStep 1073411 = 1610117) B1610117
theorem B319747 : Blo 315835 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B319763 : Blo 315835 319763 := bstep (se 1 (by rfl) ⟨239822, by rfl⟩ : syracuseStep 319763 = 479645) B479645
theorem B319779 : Blo 315835 319779 := bstep (se 1 (by rfl) ⟨239834, by rfl⟩ : syracuseStep 319779 = 479669) B479669
theorem B319795 : Blo 315835 319795 := bstep (se 1 (by rfl) ⟨239846, by rfl⟩ : syracuseStep 319795 = 479693) B479693
theorem B319811 : Blo 315835 319811 := bstep (se 1 (by rfl) ⟨239858, by rfl⟩ : syracuseStep 319811 = 479717) B479717
theorem B319827 : Blo 315835 319827 := bstep (se 1 (by rfl) ⟨239870, by rfl⟩ : syracuseStep 319827 = 479741) B479741
theorem B713105 : Blo 315835 713105 := bstep (se 2 (by rfl) ⟨267414, by rfl⟩ : syracuseStep 713105 = 534829) B534829
theorem B713123 : Blo 315835 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B1073681 : Blo 315835 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B2187917 : Blo 315835 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B451217 : Blo 315835 451217 := bstep (se 2 (by rfl) ⟨169206, by rfl⟩ : syracuseStep 451217 = 338413) B338413
theorem B713393 : Blo 315835 713393 := bstep (se 2 (by rfl) ⟨267522, by rfl⟩ : syracuseStep 713393 = 535045) B535045
theorem B713411 : Blo 315835 713411 := bstep (se 1 (by rfl) ⟨535058, by rfl⟩ : syracuseStep 713411 = 1070117) B1070117
theorem B1925957 : Blo 315835 1925957 := bstep (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) B361117
theorem B713681 : Blo 315835 713681 := bstep (se 2 (by rfl) ⟨267630, by rfl⟩ : syracuseStep 713681 = 535261) B535261
theorem B713699 : Blo 315835 713699 := bstep (se 1 (by rfl) ⟨535274, by rfl⟩ : syracuseStep 713699 = 1070549) B1070549
theorem B1205219 : Blo 315835 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B680977 : Blo 315835 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B1074221 : Blo 315835 1074221 := bstep (se 3 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 1074221 = 402833) B402833
theorem B910385 : Blo 315835 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B1074275 : Blo 315835 1074275 := bstep (se 1 (by rfl) ⟨805706, by rfl⟩ : syracuseStep 1074275 = 1611413) B1611413
theorem B451747 : Blo 315835 451747 := bstep (se 1 (by rfl) ⟨338810, by rfl⟩ : syracuseStep 451747 = 677621) B677621
theorem B484579 : Blo 315835 484579 := bstep (se 1 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 484579 = 726869) B726869
theorem B713969 : Blo 315835 713969 := bstep (se 2 (by rfl) ⟨267738, by rfl⟩ : syracuseStep 713969 = 535477) B535477
theorem B713987 : Blo 315835 713987 := bstep (se 1 (by rfl) ⟨535490, by rfl⟩ : syracuseStep 713987 = 1070981) B1070981
theorem B1369457 : Blo 315835 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1074545 : Blo 315835 1074545 := bstep (se 2 (by rfl) ⟨402954, by rfl⟩ : syracuseStep 1074545 = 805909) B805909
theorem B2712973 : Blo 315835 2712973 := bstep (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) B1017365
theorem B452083 : Blo 315835 452083 := bstep (se 1 (by rfl) ⟨339062, by rfl⟩ : syracuseStep 452083 = 678125) B678125
theorem B714257 : Blo 315835 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B714275 : Blo 315835 714275 := bstep (se 1 (by rfl) ⟨535706, by rfl⟩ : syracuseStep 714275 = 1071413) B1071413
theorem B1205873 : Blo 315835 1205873 := bstep (se 2 (by rfl) ⟨452202, by rfl⟩ : syracuseStep 1205873 = 904405) B904405
theorem B714545 : Blo 315835 714545 := bstep (se 2 (by rfl) ⟨267954, by rfl⟩ : syracuseStep 714545 = 535909) B535909
theorem B714563 : Blo 315835 714563 := bstep (se 1 (by rfl) ⟨535922, by rfl⟩ : syracuseStep 714563 = 1071845) B1071845
theorem B1075085 : Blo 315835 1075085 := bstep (se 3 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 1075085 = 403157) B403157
theorem B1075139 : Blo 315835 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B452641 : Blo 315835 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B452675 : Blo 315835 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B714833 : Blo 315835 714833 := bstep (se 2 (by rfl) ⟨268062, by rfl⟩ : syracuseStep 714833 = 536125) B536125
theorem B1599587 : Blo 315835 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B714851 : Blo 315835 714851 := bstep (se 1 (by rfl) ⟨536138, by rfl⟩ : syracuseStep 714851 = 1072277) B1072277
theorem B1075409 : Blo 315835 1075409 := bstep (se 2 (by rfl) ⟨403278, by rfl⟩ : syracuseStep 1075409 = 806557) B806557
theorem B10414307 : Blo 315835 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B715121 : Blo 315835 715121 := bstep (se 2 (by rfl) ⟨268170, by rfl⟩ : syracuseStep 715121 = 536341) B536341
theorem B715139 : Blo 315835 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B1993187 : Blo 315835 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B3434993 : Blo 315835 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B682481 : Blo 315835 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B682499 : Blo 315835 682499 := bstep (se 1 (by rfl) ⟨511874, by rfl⟩ : syracuseStep 682499 = 1023749) B1023749
theorem B453233 : Blo 315835 453233 := bstep (se 2 (by rfl) ⟨169962, by rfl⟩ : syracuseStep 453233 = 339925) B339925
theorem B715409 : Blo 315835 715409 := bstep (se 2 (by rfl) ⟨268278, by rfl⟩ : syracuseStep 715409 = 536557) B536557
theorem B715427 : Blo 315835 715427 := bstep (se 1 (by rfl) ⟨536570, by rfl⟩ : syracuseStep 715427 = 1073141) B1073141
theorem B453313 : Blo 315835 453313 := bstep (se 2 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 453313 = 339985) B339985
theorem B2714309 : Blo 315835 2714309 := bstep (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) B508933
theorem B1075949 : Blo 315835 1075949 := bstep (se 3 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 1075949 = 403481) B403481
theorem B912131 : Blo 315835 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B1076003 : Blo 315835 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B1600397 : Blo 315835 1600397 := bstep (se 3 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 1600397 = 600149) B600149
theorem B715697 : Blo 315835 715697 := bstep (se 2 (by rfl) ⟨268386, by rfl⟩ : syracuseStep 715697 = 536773) B536773
theorem B715715 : Blo 315835 715715 := bstep (se 1 (by rfl) ⟨536786, by rfl⟩ : syracuseStep 715715 = 1073573) B1073573
theorem B355315 : Blo 315835 355315 := bstep (se 1 (by rfl) ⟨266486, by rfl⟩ : syracuseStep 355315 = 532973) B532973
theorem B1207331 : Blo 315835 1207331 := bstep (se 1 (by rfl) ⟨905498, by rfl⟩ : syracuseStep 1207331 = 1810997) B1810997
theorem B1207345 : Blo 315835 1207345 := bstep (se 2 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 1207345 = 905509) B905509
theorem B1076273 : Blo 315835 1076273 := bstep (se 2 (by rfl) ⟨403602, by rfl⟩ : syracuseStep 1076273 = 807205) B807205
theorem B355459 : Blo 315835 355459 := bstep (se 1 (by rfl) ⟨266594, by rfl⟩ : syracuseStep 355459 = 533189) B533189
theorem B1961165 : Blo 315835 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B715985 : Blo 315835 715985 := bstep (se 2 (by rfl) ⟨268494, by rfl⟩ : syracuseStep 715985 = 536989) B536989
theorem B716003 : Blo 315835 716003 := bstep (se 1 (by rfl) ⟨537002, by rfl⟩ : syracuseStep 716003 = 1074005) B1074005
theorem B355603 : Blo 315835 355603 := bstep (se 1 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 355603 = 533405) B533405
theorem B322915 : Blo 315835 322915 := bstep (se 1 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 322915 = 484373) B484373
theorem B355747 : Blo 315835 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B454099 : Blo 315835 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B716273 : Blo 315835 716273 := bstep (se 2 (by rfl) ⟨268602, by rfl⟩ : syracuseStep 716273 = 537205) B537205
theorem B716291 : Blo 315835 716291 := bstep (se 1 (by rfl) ⟨537218, by rfl⟩ : syracuseStep 716291 = 1074437) B1074437
theorem B355891 : Blo 315835 355891 := bstep (se 1 (by rfl) ⟨266918, by rfl⟩ : syracuseStep 355891 = 533837) B533837
theorem B1076813 : Blo 315835 1076813 := bstep (se 3 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 1076813 = 403805) B403805
theorem B1076867 : Blo 315835 1076867 := bstep (se 1 (by rfl) ⟨807650, by rfl⟩ : syracuseStep 1076867 = 1615301) B1615301
theorem B356035 : Blo 315835 356035 := bstep (se 1 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 356035 = 534053) B534053
theorem B716561 : Blo 315835 716561 := bstep (se 2 (by rfl) ⟨268710, by rfl⟩ : syracuseStep 716561 = 537421) B537421
theorem B716579 : Blo 315835 716579 := bstep (se 1 (by rfl) ⟨537434, by rfl⟩ : syracuseStep 716579 = 1074869) B1074869
theorem B356179 : Blo 315835 356179 := bstep (se 1 (by rfl) ⟨267134, by rfl⟩ : syracuseStep 356179 = 534269) B534269
theorem B1077137 : Blo 315835 1077137 := bstep (se 2 (by rfl) ⟨403926, by rfl⟩ : syracuseStep 1077137 = 807853) B807853
theorem B454577 : Blo 315835 454577 := bstep (se 2 (by rfl) ⟨170466, by rfl⟩ : syracuseStep 454577 = 340933) B340933
theorem B356323 : Blo 315835 356323 := bstep (se 1 (by rfl) ⟨267242, by rfl⟩ : syracuseStep 356323 = 534485) B534485
theorem B2027555 : Blo 315835 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B978979 : Blo 315835 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B454691 : Blo 315835 454691 := bstep (se 1 (by rfl) ⟨341018, by rfl⟩ : syracuseStep 454691 = 682037) B682037
theorem B716849 : Blo 315835 716849 := bstep (se 2 (by rfl) ⟨268818, by rfl⟩ : syracuseStep 716849 = 537637) B537637
theorem B716867 : Blo 315835 716867 := bstep (se 1 (by rfl) ⟨537650, by rfl⟩ : syracuseStep 716867 = 1075301) B1075301
theorem B356467 : Blo 315835 356467 := bstep (se 1 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 356467 = 534701) B534701
theorem B454771 : Blo 315835 454771 := bstep (se 1 (by rfl) ⟨341078, by rfl⟩ : syracuseStep 454771 = 682157) B682157
theorem B356611 : Blo 315835 356611 := bstep (se 1 (by rfl) ⟨267458, by rfl⟩ : syracuseStep 356611 = 534917) B534917
theorem B717137 : Blo 315835 717137 := bstep (se 2 (by rfl) ⟨268926, by rfl⟩ : syracuseStep 717137 = 537853) B537853
theorem B717155 : Blo 315835 717155 := bstep (se 1 (by rfl) ⟨537866, by rfl⟩ : syracuseStep 717155 = 1075733) B1075733
theorem B356755 : Blo 315835 356755 := bstep (se 1 (by rfl) ⟨267566, by rfl⟩ : syracuseStep 356755 = 535133) B535133
theorem B1077677 : Blo 315835 1077677 := bstep (se 3 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 1077677 = 404129) B404129
theorem B1208803 : Blo 315835 1208803 := bstep (se 1 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 1208803 = 1813205) B1813205
theorem B1077731 : Blo 315835 1077731 := bstep (se 1 (by rfl) ⟨808298, by rfl⟩ : syracuseStep 1077731 = 1616597) B1616597
theorem B2028017 : Blo 315835 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B356899 : Blo 315835 356899 := bstep (se 1 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 356899 = 535349) B535349
theorem B717425 : Blo 315835 717425 := bstep (se 2 (by rfl) ⟨269034, by rfl⟩ : syracuseStep 717425 = 538069) B538069
theorem B717443 : Blo 315835 717443 := bstep (se 1 (by rfl) ⟨538082, by rfl⟩ : syracuseStep 717443 = 1076165) B1076165
theorem B455329 : Blo 315835 455329 := bstep (se 2 (by rfl) ⟨170748, by rfl⟩ : syracuseStep 455329 = 341497) B341497
theorem B357043 : Blo 315835 357043 := bstep (se 1 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 357043 = 535565) B535565
theorem B914161 : Blo 315835 914161 := bstep (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) B685621
theorem B1078001 : Blo 315835 1078001 := bstep (se 2 (by rfl) ⟨404250, by rfl⟩ : syracuseStep 1078001 = 808501) B808501
theorem B1012547 : Blo 315835 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B357187 : Blo 315835 357187 := bstep (se 1 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 357187 = 535781) B535781
theorem B717713 : Blo 315835 717713 := bstep (se 2 (by rfl) ⟨269142, by rfl⟩ : syracuseStep 717713 = 538285) B538285
theorem B717731 : Blo 315835 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B357331 : Blo 315835 357331 := bstep (se 1 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 357331 = 535997) B535997
theorem B914449 : Blo 315835 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B357475 : Blo 315835 357475 := bstep (se 1 (by rfl) ⟨268106, by rfl⟩ : syracuseStep 357475 = 536213) B536213
theorem B718001 : Blo 315835 718001 := bstep (se 2 (by rfl) ⟨269250, by rfl⟩ : syracuseStep 718001 = 538501) B538501
theorem B718019 : Blo 315835 718019 := bstep (se 1 (by rfl) ⟨538514, by rfl⟩ : syracuseStep 718019 = 1077029) B1077029
theorem B357619 : Blo 315835 357619 := bstep (se 1 (by rfl) ⟨268214, by rfl⟩ : syracuseStep 357619 = 536429) B536429
theorem B1078541 : Blo 315835 1078541 := bstep (se 3 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 1078541 = 404453) B404453
theorem B1078595 : Blo 315835 1078595 := bstep (se 1 (by rfl) ⟨808946, by rfl⟩ : syracuseStep 1078595 = 1617893) B1617893
theorem B357763 : Blo 315835 357763 := bstep (se 1 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 357763 = 536645) B536645
theorem B718289 : Blo 315835 718289 := bstep (se 2 (by rfl) ⟨269358, by rfl⟩ : syracuseStep 718289 = 538717) B538717
theorem B718307 : Blo 315835 718307 := bstep (se 1 (by rfl) ⟨538730, by rfl⟩ : syracuseStep 718307 = 1077461) B1077461
theorem B357907 : Blo 315835 357907 := bstep (se 1 (by rfl) ⟨268430, by rfl⟩ : syracuseStep 357907 = 536861) B536861
theorem B1078865 : Blo 315835 1078865 := bstep (se 2 (by rfl) ⟨404574, by rfl⟩ : syracuseStep 1078865 = 809149) B809149
theorem B358051 : Blo 315835 358051 := bstep (se 1 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 358051 = 537077) B537077
theorem B1603313 : Blo 315835 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B718577 : Blo 315835 718577 := bstep (se 2 (by rfl) ⟨269466, by rfl⟩ : syracuseStep 718577 = 538933) B538933
theorem B718595 : Blo 315835 718595 := bstep (se 1 (by rfl) ⟨538946, by rfl⟩ : syracuseStep 718595 = 1077893) B1077893
theorem B358195 : Blo 315835 358195 := bstep (se 1 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 358195 = 537293) B537293
theorem B1308593 : Blo 315835 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B817073 : Blo 315835 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B358339 : Blo 315835 358339 := bstep (se 1 (by rfl) ⟨268754, by rfl⟩ : syracuseStep 358339 = 537509) B537509
theorem B2455523 : Blo 315835 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B718865 : Blo 315835 718865 := bstep (se 2 (by rfl) ⟨269574, by rfl⟩ : syracuseStep 718865 = 539149) B539149
theorem B718883 : Blo 315835 718883 := bstep (se 1 (by rfl) ⟨539162, by rfl⟩ : syracuseStep 718883 = 1078325) B1078325
theorem B358483 : Blo 315835 358483 := bstep (se 1 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 358483 = 537725) B537725
theorem B1079405 : Blo 315835 1079405 := bstep (se 3 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 1079405 = 404777) B404777
theorem B358627 : Blo 315835 358627 := bstep (se 1 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 358627 = 537941) B537941
theorem B719153 : Blo 315835 719153 := bstep (se 2 (by rfl) ⟨269682, by rfl⟩ : syracuseStep 719153 = 539365) B539365
theorem B719171 : Blo 315835 719171 := bstep (se 1 (by rfl) ⟨539378, by rfl⟩ : syracuseStep 719171 = 1078757) B1078757
theorem B358771 : Blo 315835 358771 := bstep (se 1 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 358771 = 538157) B538157
theorem B358915 : Blo 315835 358915 := bstep (se 1 (by rfl) ⟨269186, by rfl⟩ : syracuseStep 358915 = 538373) B538373
theorem B719441 : Blo 315835 719441 := bstep (se 2 (by rfl) ⟨269790, by rfl⟩ : syracuseStep 719441 = 539581) B539581
theorem B719459 : Blo 315835 719459 := bstep (se 1 (by rfl) ⟨539594, by rfl⟩ : syracuseStep 719459 = 1079189) B1079189
theorem B1211021 : Blo 315835 1211021 := bstep (se 3 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 1211021 = 454133) B454133
theorem B359059 : Blo 315835 359059 := bstep (se 1 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 359059 = 538589) B538589
theorem B359203 : Blo 315835 359203 := bstep (se 1 (by rfl) ⟨269402, by rfl⟩ : syracuseStep 359203 = 538805) B538805
theorem B359347 : Blo 315835 359347 := bstep (se 1 (by rfl) ⟨269510, by rfl⟩ : syracuseStep 359347 = 539021) B539021
theorem B359491 : Blo 315835 359491 := bstep (se 1 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 359491 = 539237) B539237
theorem B916561 : Blo 315835 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B1604771 : Blo 315835 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B359635 : Blo 315835 359635 := bstep (se 1 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 359635 = 539453) B539453
theorem B4914485 : Blo 315835 4914485 := bstep (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) B460733
theorem B1801541 : Blo 315835 1801541 := bstep (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) B337789
theorem B359779 : Blo 315835 359779 := bstep (se 1 (by rfl) ⟨269834, by rfl⟩ : syracuseStep 359779 = 539669) B539669
theorem B3079565 : Blo 315835 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1015213 : Blo 315835 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B5766709 : Blo 315835 5766709 := bstep (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) B540629
theorem B1867333 : Blo 315835 1867333 := bstep (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) B350125
theorem B2719331 : Blo 315835 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B917219 : Blo 315835 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1801997 : Blo 315835 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B1605581 : Blo 315835 1605581 := bstep (se 3 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 1605581 = 602093) B602093
theorem B1212509 : Blo 315835 1212509 := bstep (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) B454691
theorem B1605905 : Blo 315835 1605905 := bstep (se 2 (by rfl) ⟨602214, by rfl⟩ : syracuseStep 1605905 = 1204429) B1204429
theorem B2326849 : Blo 315835 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B2031965 : Blo 315835 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B1606067 : Blo 315835 1606067 := bstep (se 1 (by rfl) ⟨1204550, by rfl⟩ : syracuseStep 1606067 = 2409101) B2409101
theorem B1409501 : Blo 315835 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B2753041 : Blo 315835 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B361355 : Blo 315835 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B1017623 : Blo 315835 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B4130605 : Blo 315835 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B1837187 : Blo 315835 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1181969 : Blo 315835 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B1608011 : Blo 315835 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B428375 : Blo 315835 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B8096273 : Blo 315835 8096273 := bstep (se 2 (by rfl) ⟨3036102, by rfl⟩ : syracuseStep 8096273 = 6072205) B6072205
theorem B920129 : Blo 315835 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B2427569 : Blo 315835 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B363307 : Blo 315835 363307 := bstep (se 1 (by rfl) ⟨272480, by rfl⟩ : syracuseStep 363307 = 544961) B544961
theorem B1149785 : Blo 315835 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B429067 : Blo 315835 429067 := bstep (se 1 (by rfl) ⟨321800, by rfl⟩ : syracuseStep 429067 = 643601) B643601
theorem B2165825 : Blo 315835 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B7310411 : Blo 315835 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B1018955 : Blo 315835 1018955 := bstep (se 1 (by rfl) ⟨764216, by rfl⟩ : syracuseStep 1018955 = 1528433) B1528433
theorem B363671 : Blo 315835 363671 := bstep (se 1 (by rfl) ⟨272753, by rfl⟩ : syracuseStep 363671 = 545507) B545507
theorem B2428055 : Blo 315835 2428055 := bstep (se 1 (by rfl) ⟨1821041, by rfl⟩ : syracuseStep 2428055 = 3642083) B3642083
theorem B2034989 : Blo 315835 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B1806097 : Blo 315835 1806097 := bstep (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) B1354573
theorem B1609793 : Blo 315835 1609793 := bstep (se 2 (by rfl) ⟨603672, by rfl⟩ : syracuseStep 1609793 = 1207345) B1207345
theorem B8720459 : Blo 315835 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B2199653 : Blo 315835 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B856499 : Blo 315835 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B430553 : Blo 315835 430553 := bstep (se 2 (by rfl) ⟨161457, by rfl⟩ : syracuseStep 430553 = 322915) B322915
theorem B1446365 : Blo 315835 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B1020595 : Blo 315835 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B1020737 : Blo 315835 1020737 := bstep (se 2 (by rfl) ⟨382776, by rfl⟩ : syracuseStep 1020737 = 765553) B765553
theorem B1020851 : Blo 315835 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B2200537 : Blo 315835 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B2299427 : Blo 315835 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B4888325 : Blo 315835 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B1283971 : Blo 315835 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B1611737 : Blo 315835 1611737 := bstep (se 2 (by rfl) ⟨604401, by rfl⟩ : syracuseStep 1611737 = 1208803) B1208803
theorem B1218881 : Blo 315835 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B399755 : Blo 315835 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B2431505 : Blo 315835 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B7740035 : Blo 315835 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B1219265 : Blo 315835 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B859031 : Blo 315835 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B2038679 : Blo 315835 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B400459 : Blo 315835 400459 := bstep (se 1 (by rfl) ⟨300344, by rfl⟩ : syracuseStep 400459 = 600689) B600689
theorem B1809539 : Blo 315835 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B400727 : Blo 315835 400727 := bstep (se 1 (by rfl) ⟨300545, by rfl⟩ : syracuseStep 400727 = 601091) B601091
theorem B1613357 : Blo 315835 1613357 := bstep (se 3 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 1613357 = 605009) B605009
theorem B728651 : Blo 315835 728651 := bstep (se 1 (by rfl) ⟨546488, by rfl⟩ : syracuseStep 728651 = 1092977) B1092977
theorem B1286161 : Blo 315835 1286161 := bstep (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) B964621
theorem B1351703 : Blo 315835 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B401431 : Blo 315835 401431 := bstep (se 1 (by rfl) ⟨301073, by rfl⟩ : syracuseStep 401431 = 602147) B602147
theorem B1352011 : Blo 315835 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B795187 : Blo 315835 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B533081 : Blo 315835 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B1352285 : Blo 315835 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B533209 : Blo 315835 533209 := bstep (se 2 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 533209 = 399907) B399907
theorem B2040677 : Blo 315835 2040677 := bstep (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) B382627
theorem B2401325 : Blo 315835 2401325 := bstep (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) B900497
theorem B533783 : Blo 315835 533783 := bstep (se 1 (by rfl) ⟨400337, by rfl⟩ : syracuseStep 533783 = 800675) B800675
theorem B533911 : Blo 315835 533911 := bstep (se 1 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 533911 = 800867) B800867
theorem B1811929 : Blo 315835 1811929 := bstep (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) B1358947
theorem B403147 : Blo 315835 403147 := bstep (se 1 (by rfl) ⟨302360, by rfl⟩ : syracuseStep 403147 = 604721) B604721
theorem B1353617 : Blo 315835 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B1288109 : Blo 315835 1288109 := bstep (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) B483041
theorem B534539 : Blo 315835 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B337943 : Blo 315835 337943 := bstep (se 1 (by rfl) ⟨253457, by rfl⟩ : syracuseStep 337943 = 506915) B506915
theorem B2304065 : Blo 315835 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B600203 : Blo 315835 600203 := bstep (se 1 (by rfl) ⟨450152, by rfl⟩ : syracuseStep 600203 = 900305) B900305
theorem B534667 : Blo 315835 534667 := bstep (se 1 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 534667 = 802001) B802001
theorem B534809 : Blo 315835 534809 := bstep (se 2 (by rfl) ⟨200553, by rfl⟩ : syracuseStep 534809 = 401107) B401107
theorem B600385 : Blo 315835 600385 := bstep (se 2 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 600385 = 450289) B450289
theorem B1517899 : Blo 315835 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B1812887 : Blo 315835 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B534937 : Blo 315835 534937 := bstep (se 2 (by rfl) ⟨200601, by rfl⟩ : syracuseStep 534937 = 401203) B401203
theorem B16198157 : Blo 315835 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B404119 : Blo 315835 404119 := bstep (se 1 (by rfl) ⟨303089, by rfl⟩ : syracuseStep 404119 = 606179) B606179
theorem B600833 : Blo 315835 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B961373 : Blo 315835 961373 := bstep (se 3 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 961373 = 360515) B360515
theorem B4107125 : Blo 315835 4107125 := bstep (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) B385043
theorem B535511 : Blo 315835 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B3419171 : Blo 315835 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B601175 : Blo 315835 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B535639 : Blo 315835 535639 := bstep (se 1 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 535639 = 803459) B803459
theorem B961739 : Blo 315835 961739 := bstep (se 1 (by rfl) ⟨721304, by rfl⟩ : syracuseStep 961739 = 1442609) B1442609
theorem B6991109 : Blo 315835 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B1617245 : Blo 315835 1617245 := bstep (se 3 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 1617245 = 606467) B606467
theorem B536267 : Blo 315835 536267 := bstep (se 1 (by rfl) ⟨402200, by rfl⟩ : syracuseStep 536267 = 804401) B804401
theorem B601843 : Blo 315835 601843 := bstep (se 1 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 601843 = 902765) B902765
theorem B536395 : Blo 315835 536395 := bstep (se 1 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 536395 = 804593) B804593
theorem B536537 : Blo 315835 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B536665 : Blo 315835 536665 := bstep (se 2 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 536665 = 402499) B402499
theorem B340075 : Blo 315835 340075 := bstep (se 1 (by rfl) ⟨255056, by rfl⟩ : syracuseStep 340075 = 510113) B510113
theorem B602291 : Blo 315835 602291 := bstep (se 1 (by rfl) ⟨451718, by rfl⟩ : syracuseStep 602291 = 903437) B903437
theorem B602329 : Blo 315835 602329 := bstep (se 2 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 602329 = 451747) B451747
theorem B766169 : Blo 315835 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B3420461 : Blo 315835 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B1356077 : Blo 315835 1356077 := bstep (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) B508529
theorem B22196753 : Blo 315835 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B3617297 : Blo 315835 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B3551779 : Blo 315835 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B2699851 : Blo 315835 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B1356419 : Blo 315835 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B537239 : Blo 315835 537239 := bstep (se 1 (by rfl) ⟨402929, by rfl⟩ : syracuseStep 537239 = 805859) B805859
theorem B602777 : Blo 315835 602777 := bstep (se 2 (by rfl) ⟨226041, by rfl⟩ : syracuseStep 602777 = 452083) B452083
theorem B537367 : Blo 315835 537367 := bstep (se 1 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 537367 = 806051) B806051
theorem B1815371 : Blo 315835 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B2700125 : Blo 315835 2700125 := bstep (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) B1012547
theorem B2405213 : Blo 315835 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B799895 : Blo 315835 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B570611 : Blo 315835 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B603521 : Blo 315835 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B537995 : Blo 315835 537995 := bstep (se 1 (by rfl) ⟨403496, by rfl⟩ : syracuseStep 537995 = 806993) B806993
theorem B538123 : Blo 315835 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B1226285 : Blo 315835 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B603787 : Blo 315835 603787 := bstep (se 1 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 603787 = 905681) B905681
theorem B538265 : Blo 315835 538265 := bstep (se 2 (by rfl) ⟨201849, by rfl⟩ : syracuseStep 538265 = 403699) B403699
theorem B538393 : Blo 315835 538393 := bstep (se 2 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 538393 = 403795) B403795
theorem B3323693 : Blo 315835 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B800563 : Blo 315835 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B2701187 : Blo 315835 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B800705 : Blo 315835 800705 := bstep (se 2 (by rfl) ⟨300264, by rfl⟩ : syracuseStep 800705 = 600529) B600529
theorem B604235 : Blo 315835 604235 := bstep (se 1 (by rfl) ⟨453176, by rfl⟩ : syracuseStep 604235 = 906353) B906353
theorem B4077661 : Blo 315835 4077661 := bstep (se 3 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 4077661 = 1529123) B1529123
theorem B604417 : Blo 315835 604417 := bstep (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) B453313
theorem B538967 : Blo 315835 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B538969 : Blo 315835 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B539095 : Blo 315835 539095 := bstep (se 1 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 539095 = 808643) B808643
theorem B10271245 : Blo 315835 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B604759 : Blo 315835 604759 := bstep (se 1 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 604759 = 907139) B907139
theorem B899677 : Blo 315835 899677 := bstep (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) B337379
theorem B3455581 : Blo 315835 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B473753 : Blo 315835 473753 := bstep (se 2 (by rfl) ⟨177657, by rfl⟩ : syracuseStep 473753 = 355315) B355315
theorem B473867 : Blo 315835 473867 := bstep (se 1 (by rfl) ⟨355400, by rfl⟩ : syracuseStep 473867 = 710801) B710801
theorem B473879 : Blo 315835 473879 := bstep (se 1 (by rfl) ⟨355409, by rfl⟩ : syracuseStep 473879 = 710819) B710819
theorem B1391411 : Blo 315835 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B604979 : Blo 315835 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B899905 : Blo 315835 899905 := bstep (se 2 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 899905 = 674929) B674929
theorem B4733761 : Blo 315835 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B473945 : Blo 315835 473945 := bstep (se 2 (by rfl) ⟨177729, by rfl⟩ : syracuseStep 473945 = 355459) B355459
theorem B474059 : Blo 315835 474059 := bstep (se 1 (by rfl) ⟨355544, by rfl⟩ : syracuseStep 474059 = 711089) B711089
theorem B1358795 : Blo 315835 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B474071 : Blo 315835 474071 := bstep (se 1 (by rfl) ⟨355553, by rfl⟩ : syracuseStep 474071 = 711107) B711107
theorem B605207 : Blo 315835 605207 := bstep (se 1 (by rfl) ⟨453905, by rfl⟩ : syracuseStep 605207 = 907811) B907811
theorem B474137 : Blo 315835 474137 := bstep (se 2 (by rfl) ⟨177801, by rfl⟩ : syracuseStep 474137 = 355603) B355603
theorem B539723 : Blo 315835 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B474251 : Blo 315835 474251 := bstep (se 1 (by rfl) ⟨355688, by rfl⟩ : syracuseStep 474251 = 711377) B711377
theorem B900247 : Blo 315835 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B474263 : Blo 315835 474263 := bstep (se 1 (by rfl) ⟨355697, by rfl⟩ : syracuseStep 474263 = 711395) B711395
theorem B801971 : Blo 315835 801971 := bstep (se 1 (by rfl) ⟨601478, by rfl⟩ : syracuseStep 801971 = 1202957) B1202957
theorem B474329 : Blo 315835 474329 := bstep (se 2 (by rfl) ⟨177873, by rfl⟩ : syracuseStep 474329 = 355747) B355747
theorem B605465 : Blo 315835 605465 := bstep (se 2 (by rfl) ⟨227049, by rfl⟩ : syracuseStep 605465 = 454099) B454099
theorem B474443 : Blo 315835 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B474455 : Blo 315835 474455 := bstep (se 1 (by rfl) ⟨355841, by rfl⟩ : syracuseStep 474455 = 711683) B711683
theorem B3620213 : Blo 315835 3620213 := bstep (se 5 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 3620213 = 339395) B339395
theorem B474521 : Blo 315835 474521 := bstep (se 2 (by rfl) ⟨177945, by rfl⟩ : syracuseStep 474521 = 355891) B355891
theorem B1818035 : Blo 315835 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B474635 : Blo 315835 474635 := bstep (se 1 (by rfl) ⟨355976, by rfl⟩ : syracuseStep 474635 = 711953) B711953
theorem B474647 : Blo 315835 474647 := bstep (se 1 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 474647 = 711971) B711971
theorem B2276909 : Blo 315835 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B474713 : Blo 315835 474713 := bstep (se 2 (by rfl) ⟨178017, by rfl⟩ : syracuseStep 474713 = 356035) B356035
theorem B605875 : Blo 315835 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B474827 : Blo 315835 474827 := bstep (se 1 (by rfl) ⟨356120, by rfl⟩ : syracuseStep 474827 = 712241) B712241
theorem B802507 : Blo 315835 802507 := bstep (se 1 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 802507 = 1203761) B1203761
theorem B474839 : Blo 315835 474839 := bstep (se 1 (by rfl) ⟨356129, by rfl⟩ : syracuseStep 474839 = 712259) B712259
theorem B474905 : Blo 315835 474905 := bstep (se 2 (by rfl) ⟨178089, by rfl⟩ : syracuseStep 474905 = 356179) B356179
theorem B3489581 : Blo 315835 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1261363 : Blo 315835 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B900953 : Blo 315835 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B802649 : Blo 315835 802649 := bstep (se 2 (by rfl) ⟨300993, by rfl⟩ : syracuseStep 802649 = 601987) B601987
theorem B475019 : Blo 315835 475019 := bstep (se 1 (by rfl) ⟨356264, by rfl⟩ : syracuseStep 475019 = 712529) B712529
theorem B475031 : Blo 315835 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B1359767 : Blo 315835 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B475097 : Blo 315835 475097 := bstep (se 2 (by rfl) ⟨178161, by rfl⟩ : syracuseStep 475097 = 356323) B356323
theorem B1294339 : Blo 315835 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B475211 : Blo 315835 475211 := bstep (se 1 (by rfl) ⟨356408, by rfl⟩ : syracuseStep 475211 = 712817) B712817
theorem B475223 : Blo 315835 475223 := bstep (se 1 (by rfl) ⟨356417, by rfl⟩ : syracuseStep 475223 = 712835) B712835
theorem B475289 : Blo 315835 475289 := bstep (se 2 (by rfl) ⟨178233, by rfl⟩ : syracuseStep 475289 = 356467) B356467
theorem B606361 : Blo 315835 606361 := bstep (se 2 (by rfl) ⟨227385, by rfl⟩ : syracuseStep 606361 = 454771) B454771
theorem B4145357 : Blo 315835 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B475403 : Blo 315835 475403 := bstep (se 1 (by rfl) ⟨356552, by rfl⟩ : syracuseStep 475403 = 713105) B713105
theorem B475415 : Blo 315835 475415 := bstep (se 1 (by rfl) ⟨356561, by rfl⟩ : syracuseStep 475415 = 713123) B713123
theorem B475481 : Blo 315835 475481 := bstep (se 2 (by rfl) ⟨178305, by rfl⟩ : syracuseStep 475481 = 356611) B356611
theorem B1458611 : Blo 315835 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B475595 : Blo 315835 475595 := bstep (se 1 (by rfl) ⟨356696, by rfl⟩ : syracuseStep 475595 = 713393) B713393
theorem B475607 : Blo 315835 475607 := bstep (se 1 (by rfl) ⟨356705, by rfl⟩ : syracuseStep 475607 = 713411) B713411
theorem B508375 : Blo 315835 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B508427 : Blo 315835 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B475673 : Blo 315835 475673 := bstep (se 2 (by rfl) ⟨178377, by rfl⟩ : syracuseStep 475673 = 356755) B356755
theorem B1360435 : Blo 315835 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B1229363 : Blo 315835 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B836185 : Blo 315835 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B967261 : Blo 315835 967261 := bstep (se 3 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 967261 = 362723) B362723
theorem B475787 : Blo 315835 475787 := bstep (se 1 (by rfl) ⟨356840, by rfl⟩ : syracuseStep 475787 = 713681) B713681
theorem B508555 : Blo 315835 508555 := bstep (se 1 (by rfl) ⟨381416, by rfl⟩ : syracuseStep 508555 = 762833) B762833
theorem B475799 : Blo 315835 475799 := bstep (se 1 (by rfl) ⟨356849, by rfl⟩ : syracuseStep 475799 = 713699) B713699
theorem B803479 : Blo 315835 803479 := bstep (se 1 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 803479 = 1205219) B1205219
theorem B606923 : Blo 315835 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B2573005 : Blo 315835 2573005 := bstep (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) B964877
theorem B475865 : Blo 315835 475865 := bstep (se 2 (by rfl) ⟨178449, by rfl⟩ : syracuseStep 475865 = 356899) B356899
theorem B475979 : Blo 315835 475979 := bstep (se 1 (by rfl) ⟨356984, by rfl⟩ : syracuseStep 475979 = 713969) B713969
theorem B475991 : Blo 315835 475991 := bstep (se 1 (by rfl) ⟨356993, by rfl⟩ : syracuseStep 475991 = 713987) B713987
theorem B770905 : Blo 315835 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B1819493 : Blo 315835 1819493 := bstep (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) B341155
theorem B607105 : Blo 315835 607105 := bstep (se 2 (by rfl) ⟨227664, by rfl⟩ : syracuseStep 607105 = 455329) B455329
theorem B476057 : Blo 315835 476057 := bstep (se 2 (by rfl) ⟨178521, by rfl⟩ : syracuseStep 476057 = 357043) B357043
theorem B476171 : Blo 315835 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B476183 : Blo 315835 476183 := bstep (se 1 (by rfl) ⟨357137, by rfl⟩ : syracuseStep 476183 = 714275) B714275
theorem B803915 : Blo 315835 803915 := bstep (se 1 (by rfl) ⟨602936, by rfl⟩ : syracuseStep 803915 = 1205873) B1205873
theorem B476249 : Blo 315835 476249 := bstep (se 2 (by rfl) ⟨178593, by rfl⟩ : syracuseStep 476249 = 357187) B357187
theorem B476363 : Blo 315835 476363 := bstep (se 1 (by rfl) ⟨357272, by rfl⟩ : syracuseStep 476363 = 714545) B714545
theorem B476375 : Blo 315835 476375 := bstep (se 1 (by rfl) ⟨357281, by rfl⟩ : syracuseStep 476375 = 714563) B714563
theorem B476441 : Blo 315835 476441 := bstep (se 2 (by rfl) ⟨178665, by rfl⟩ : syracuseStep 476441 = 357331) B357331
theorem B476555 : Blo 315835 476555 := bstep (se 1 (by rfl) ⟨357416, by rfl⟩ : syracuseStep 476555 = 714833) B714833
theorem B1066391 : Blo 315835 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B476567 : Blo 315835 476567 := bstep (se 1 (by rfl) ⟨357425, by rfl⟩ : syracuseStep 476567 = 714851) B714851
theorem B902593 : Blo 315835 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B804289 : Blo 315835 804289 := bstep (se 2 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 804289 = 603217) B603217
theorem B476633 : Blo 315835 476633 := bstep (se 2 (by rfl) ⟨178737, by rfl⟩ : syracuseStep 476633 = 357475) B357475
theorem B1820177 : Blo 315835 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B509465 : Blo 315835 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B476747 : Blo 315835 476747 := bstep (se 1 (by rfl) ⟨357560, by rfl⟩ : syracuseStep 476747 = 715121) B715121
theorem B476759 : Blo 315835 476759 := bstep (se 1 (by rfl) ⟨357569, by rfl⟩ : syracuseStep 476759 = 715139) B715139
theorem B1328791 : Blo 315835 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B476825 : Blo 315835 476825 := bstep (se 2 (by rfl) ⟨178809, by rfl⟩ : syracuseStep 476825 = 357619) B357619
theorem B4966069 : Blo 315835 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B476939 : Blo 315835 476939 := bstep (se 1 (by rfl) ⟨357704, by rfl⟩ : syracuseStep 476939 = 715409) B715409
theorem B1361681 : Blo 315835 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B476951 : Blo 315835 476951 := bstep (se 1 (by rfl) ⟨357713, by rfl⟩ : syracuseStep 476951 = 715427) B715427
theorem B608087 : Blo 315835 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B477017 : Blo 315835 477017 := bstep (se 2 (by rfl) ⟨178881, by rfl⟩ : syracuseStep 477017 = 357763) B357763
theorem B575383 : Blo 315835 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B1066931 : Blo 315835 1066931 := bstep (se 1 (by rfl) ⟨800198, by rfl⟩ : syracuseStep 1066931 = 1600397) B1600397
theorem B477131 : Blo 315835 477131 := bstep (se 1 (by rfl) ⟨357848, by rfl⟩ : syracuseStep 477131 = 715697) B715697
theorem B477143 : Blo 315835 477143 := bstep (se 1 (by rfl) ⟨357857, by rfl⟩ : syracuseStep 477143 = 715715) B715715
theorem B804887 : Blo 315835 804887 := bstep (se 1 (by rfl) ⟨603665, by rfl⟩ : syracuseStep 804887 = 1207331) B1207331
theorem B477209 : Blo 315835 477209 := bstep (se 2 (by rfl) ⟨178953, by rfl⟩ : syracuseStep 477209 = 357907) B357907
theorem B477323 : Blo 315835 477323 := bstep (se 1 (by rfl) ⟨357992, by rfl⟩ : syracuseStep 477323 = 715985) B715985
theorem B477335 : Blo 315835 477335 := bstep (se 1 (by rfl) ⟨358001, by rfl⟩ : syracuseStep 477335 = 716003) B716003
theorem B1067201 : Blo 315835 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B477401 : Blo 315835 477401 := bstep (se 2 (by rfl) ⟨179025, by rfl⟩ : syracuseStep 477401 = 358051) B358051
theorem B477515 : Blo 315835 477515 := bstep (se 1 (by rfl) ⟨358136, by rfl⟩ : syracuseStep 477515 = 716273) B716273
theorem B477527 : Blo 315835 477527 := bstep (se 1 (by rfl) ⟨358145, by rfl⟩ : syracuseStep 477527 = 716291) B716291
theorem B477593 : Blo 315835 477593 := bstep (se 2 (by rfl) ⟨179097, by rfl⟩ : syracuseStep 477593 = 358195) B358195
theorem B575959 : Blo 315835 575959 := bstep (se 1 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 575959 = 863939) B863939
theorem B477707 : Blo 315835 477707 := bstep (se 1 (by rfl) ⟨358280, by rfl⟩ : syracuseStep 477707 = 716561) B716561
theorem B576011 : Blo 315835 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B477719 : Blo 315835 477719 := bstep (se 1 (by rfl) ⟨358289, by rfl⟩ : syracuseStep 477719 = 716579) B716579
theorem B477785 : Blo 315835 477785 := bstep (se 2 (by rfl) ⟨179169, by rfl⟩ : syracuseStep 477785 = 358339) B358339
theorem B477899 : Blo 315835 477899 := bstep (se 1 (by rfl) ⟨358424, by rfl⟩ : syracuseStep 477899 = 716849) B716849
theorem B477911 : Blo 315835 477911 := bstep (se 1 (by rfl) ⟨358433, by rfl⟩ : syracuseStep 477911 = 716867) B716867
theorem B1067741 : Blo 315835 1067741 := bstep (se 3 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 1067741 = 400403) B400403
theorem B477977 : Blo 315835 477977 := bstep (se 2 (by rfl) ⟨179241, by rfl⟩ : syracuseStep 477977 = 358483) B358483
theorem B641857 : Blo 315835 641857 := bstep (se 2 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 641857 = 481393) B481393
theorem B805697 : Blo 315835 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B478091 : Blo 315835 478091 := bstep (se 1 (by rfl) ⟨358568, by rfl⟩ : syracuseStep 478091 = 717137) B717137
theorem B478103 : Blo 315835 478103 := bstep (se 1 (by rfl) ⟨358577, by rfl⟩ : syracuseStep 478103 = 717155) B717155
theorem B478169 : Blo 315835 478169 := bstep (se 2 (by rfl) ⟨179313, by rfl⟩ : syracuseStep 478169 = 358627) B358627
theorem B1166339 : Blo 315835 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B478283 : Blo 315835 478283 := bstep (se 1 (by rfl) ⟨358712, by rfl⟩ : syracuseStep 478283 = 717425) B717425
theorem B478295 : Blo 315835 478295 := bstep (se 1 (by rfl) ⟨358721, by rfl⟩ : syracuseStep 478295 = 717443) B717443
theorem B478361 : Blo 315835 478361 := bstep (se 2 (by rfl) ⟨179385, by rfl⟩ : syracuseStep 478361 = 358771) B358771
theorem B478475 : Blo 315835 478475 := bstep (se 1 (by rfl) ⟨358856, by rfl⟩ : syracuseStep 478475 = 717713) B717713
theorem B478487 : Blo 315835 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B806233 : Blo 315835 806233 := bstep (se 2 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 806233 = 604675) B604675
theorem B478553 : Blo 315835 478553 := bstep (se 2 (by rfl) ⟨179457, by rfl⟩ : syracuseStep 478553 = 358915) B358915
theorem B478667 : Blo 315835 478667 := bstep (se 1 (by rfl) ⟨359000, by rfl⟩ : syracuseStep 478667 = 718001) B718001
theorem B478679 : Blo 315835 478679 := bstep (se 1 (by rfl) ⟨359009, by rfl⟩ : syracuseStep 478679 = 718019) B718019
theorem B478745 : Blo 315835 478745 := bstep (se 2 (by rfl) ⟨179529, by rfl⟩ : syracuseStep 478745 = 359059) B359059
theorem B478859 : Blo 315835 478859 := bstep (se 1 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 478859 = 718289) B718289
theorem B478871 : Blo 315835 478871 := bstep (se 1 (by rfl) ⟨359153, by rfl⟩ : syracuseStep 478871 = 718307) B718307
theorem B478937 : Blo 315835 478937 := bstep (se 2 (by rfl) ⟨179601, by rfl⟩ : syracuseStep 478937 = 359203) B359203
theorem B1068875 : Blo 315835 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B479051 : Blo 315835 479051 := bstep (se 1 (by rfl) ⟨359288, by rfl⟩ : syracuseStep 479051 = 718577) B718577
theorem B479063 : Blo 315835 479063 := bstep (se 1 (by rfl) ⟨359297, by rfl⟩ : syracuseStep 479063 = 718595) B718595
theorem B479129 : Blo 315835 479129 := bstep (se 2 (by rfl) ⟨179673, by rfl⟩ : syracuseStep 479129 = 359347) B359347
theorem B544715 : Blo 315835 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B479243 : Blo 315835 479243 := bstep (se 1 (by rfl) ⟨359432, by rfl⟩ : syracuseStep 479243 = 718865) B718865
theorem B479255 : Blo 315835 479255 := bstep (se 1 (by rfl) ⟨359441, by rfl⟩ : syracuseStep 479255 = 718883) B718883
theorem B1069145 : Blo 315835 1069145 := bstep (se 2 (by rfl) ⟨400929, by rfl⟩ : syracuseStep 1069145 = 801859) B801859
theorem B479321 : Blo 315835 479321 := bstep (se 2 (by rfl) ⟨179745, by rfl⟩ : syracuseStep 479321 = 359491) B359491
theorem B1364141 : Blo 315835 1364141 := bstep (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) B511553
theorem B479435 : Blo 315835 479435 := bstep (se 1 (by rfl) ⟨359576, by rfl⟩ : syracuseStep 479435 = 719153) B719153
theorem B479447 : Blo 315835 479447 := bstep (se 1 (by rfl) ⟨359585, by rfl⟩ : syracuseStep 479447 = 719171) B719171
theorem B479513 : Blo 315835 479513 := bstep (se 2 (by rfl) ⟨179817, by rfl⟩ : syracuseStep 479513 = 359635) B359635
theorem B479627 : Blo 315835 479627 := bstep (se 1 (by rfl) ⟨359720, by rfl⟩ : syracuseStep 479627 = 719441) B719441
theorem B479639 : Blo 315835 479639 := bstep (se 1 (by rfl) ⟨359729, by rfl⟩ : syracuseStep 479639 = 719459) B719459
theorem B807347 : Blo 315835 807347 := bstep (se 1 (by rfl) ⟨605510, by rfl⟩ : syracuseStep 807347 = 1211021) B1211021
theorem B315851 : Blo 315835 315851 := bstep (se 1 (by rfl) ⟨236888, by rfl⟩ : syracuseStep 315851 = 473777) B473777
theorem B315863 : Blo 315835 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B4051417 : Blo 315835 4051417 := bstep (se 2 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 4051417 = 3038563) B3038563
theorem B479705 : Blo 315835 479705 := bstep (se 2 (by rfl) ⟨179889, by rfl⟩ : syracuseStep 479705 = 359779) B359779
theorem B315883 : Blo 315835 315883 := bstep (se 1 (by rfl) ⟨236912, by rfl⟩ : syracuseStep 315883 = 473825) B473825
theorem B315895 : Blo 315835 315895 := bstep (se 1 (by rfl) ⟨236921, by rfl⟩ : syracuseStep 315895 = 473843) B473843
theorem B315915 : Blo 315835 315915 := bstep (se 1 (by rfl) ⟨236936, by rfl⟩ : syracuseStep 315915 = 473873) B473873
theorem B315927 : Blo 315835 315927 := bstep (se 1 (by rfl) ⟨236945, by rfl⟩ : syracuseStep 315927 = 473891) B473891
theorem B315947 : Blo 315835 315947 := bstep (se 1 (by rfl) ⟨236960, by rfl⟩ : syracuseStep 315947 = 473921) B473921
theorem B315959 : Blo 315835 315959 := bstep (se 1 (by rfl) ⟨236969, by rfl⟩ : syracuseStep 315959 = 473939) B473939
theorem B315979 : Blo 315835 315979 := bstep (se 1 (by rfl) ⟨236984, by rfl⟩ : syracuseStep 315979 = 473969) B473969
theorem B315991 : Blo 315835 315991 := bstep (se 1 (by rfl) ⟨236993, by rfl⟩ : syracuseStep 315991 = 473987) B473987
theorem B643673 : Blo 315835 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B316011 : Blo 315835 316011 := bstep (se 1 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 316011 = 474017) B474017
theorem B316023 : Blo 315835 316023 := bstep (se 1 (by rfl) ⟨237017, by rfl⟩ : syracuseStep 316023 = 474035) B474035
theorem B316043 : Blo 315835 316043 := bstep (se 1 (by rfl) ⟨237032, by rfl⟩ : syracuseStep 316043 = 474065) B474065
theorem B316055 : Blo 315835 316055 := bstep (se 1 (by rfl) ⟨237041, by rfl⟩ : syracuseStep 316055 = 474083) B474083
theorem B316075 : Blo 315835 316075 := bstep (se 1 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 316075 = 474113) B474113
theorem B316087 : Blo 315835 316087 := bstep (se 1 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 316087 = 474131) B474131
theorem B316107 : Blo 315835 316107 := bstep (se 1 (by rfl) ⟨237080, by rfl⟩ : syracuseStep 316107 = 474161) B474161
theorem B316119 : Blo 315835 316119 := bstep (se 1 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 316119 = 474179) B474179
theorem B807641 : Blo 315835 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B316139 : Blo 315835 316139 := bstep (se 1 (by rfl) ⟨237104, by rfl⟩ : syracuseStep 316139 = 474209) B474209
theorem B7688945 : Blo 315835 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B316151 : Blo 315835 316151 := bstep (se 1 (by rfl) ⟨237113, by rfl⟩ : syracuseStep 316151 = 474227) B474227
theorem B316171 : Blo 315835 316171 := bstep (se 1 (by rfl) ⟨237128, by rfl⟩ : syracuseStep 316171 = 474257) B474257
theorem B316183 : Blo 315835 316183 := bstep (se 1 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 316183 = 474275) B474275
theorem B1069847 : Blo 315835 1069847 := bstep (se 1 (by rfl) ⟨802385, by rfl⟩ : syracuseStep 1069847 = 1604771) B1604771
theorem B316203 : Blo 315835 316203 := bstep (se 1 (by rfl) ⟨237152, by rfl⟩ : syracuseStep 316203 = 474305) B474305
theorem B316215 : Blo 315835 316215 := bstep (se 1 (by rfl) ⟨237161, by rfl⟩ : syracuseStep 316215 = 474323) B474323
theorem B316235 : Blo 315835 316235 := bstep (se 1 (by rfl) ⟨237176, by rfl⟩ : syracuseStep 316235 = 474353) B474353
theorem B316247 : Blo 315835 316247 := bstep (se 1 (by rfl) ⟨237185, by rfl⟩ : syracuseStep 316247 = 474371) B474371
theorem B1364825 : Blo 315835 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B316267 : Blo 315835 316267 := bstep (se 1 (by rfl) ⟨237200, by rfl⟩ : syracuseStep 316267 = 474401) B474401
theorem B316279 : Blo 315835 316279 := bstep (se 1 (by rfl) ⟨237209, by rfl⟩ : syracuseStep 316279 = 474419) B474419
theorem B1201027 : Blo 315835 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B316299 : Blo 315835 316299 := bstep (se 1 (by rfl) ⟨237224, by rfl⟩ : syracuseStep 316299 = 474449) B474449
theorem B316311 : Blo 315835 316311 := bstep (se 1 (by rfl) ⟨237233, by rfl⟩ : syracuseStep 316311 = 474467) B474467
theorem B316331 : Blo 315835 316331 := bstep (se 1 (by rfl) ⟨237248, by rfl⟩ : syracuseStep 316331 = 474497) B474497
theorem B2053043 : Blo 315835 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B316343 : Blo 315835 316343 := bstep (se 1 (by rfl) ⟨237257, by rfl⟩ : syracuseStep 316343 = 474515) B474515
theorem B316363 : Blo 315835 316363 := bstep (se 1 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 316363 = 474545) B474545
theorem B316375 : Blo 315835 316375 := bstep (se 1 (by rfl) ⟨237281, by rfl⟩ : syracuseStep 316375 = 474563) B474563
theorem B316395 : Blo 315835 316395 := bstep (se 1 (by rfl) ⟨237296, by rfl⟩ : syracuseStep 316395 = 474593) B474593
theorem B316407 : Blo 315835 316407 := bstep (se 1 (by rfl) ⟨237305, by rfl⟩ : syracuseStep 316407 = 474611) B474611
theorem B316427 : Blo 315835 316427 := bstep (se 1 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 316427 = 474641) B474641
theorem B316439 : Blo 315835 316439 := bstep (se 1 (by rfl) ⟨237329, by rfl⟩ : syracuseStep 316439 = 474659) B474659
theorem B316459 : Blo 315835 316459 := bstep (se 1 (by rfl) ⟨237344, by rfl⟩ : syracuseStep 316459 = 474689) B474689
theorem B316471 : Blo 315835 316471 := bstep (se 1 (by rfl) ⟨237353, by rfl⟩ : syracuseStep 316471 = 474707) B474707
theorem B316491 : Blo 315835 316491 := bstep (se 1 (by rfl) ⟨237368, by rfl⟩ : syracuseStep 316491 = 474737) B474737
theorem B316503 : Blo 315835 316503 := bstep (se 1 (by rfl) ⟨237377, by rfl⟩ : syracuseStep 316503 = 474755) B474755
theorem B906329 : Blo 315835 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B316523 : Blo 315835 316523 := bstep (se 1 (by rfl) ⟨237392, by rfl⟩ : syracuseStep 316523 = 474785) B474785
theorem B316535 : Blo 315835 316535 := bstep (se 1 (by rfl) ⟨237401, by rfl⟩ : syracuseStep 316535 = 474803) B474803
theorem B316555 : Blo 315835 316555 := bstep (se 1 (by rfl) ⟨237416, by rfl⟩ : syracuseStep 316555 = 474833) B474833
theorem B316567 : Blo 315835 316567 := bstep (se 1 (by rfl) ⟨237425, by rfl⟩ : syracuseStep 316567 = 474851) B474851
theorem B611479 : Blo 315835 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B545945 : Blo 315835 545945 := bstep (se 2 (by rfl) ⟨204729, by rfl⟩ : syracuseStep 545945 = 409459) B409459
theorem B316587 : Blo 315835 316587 := bstep (se 1 (by rfl) ⟨237440, by rfl⟩ : syracuseStep 316587 = 474881) B474881
theorem B1201331 : Blo 315835 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B316599 : Blo 315835 316599 := bstep (se 1 (by rfl) ⟨237449, by rfl⟩ : syracuseStep 316599 = 474899) B474899
theorem B316619 : Blo 315835 316619 := bstep (se 1 (by rfl) ⟨237464, by rfl⟩ : syracuseStep 316619 = 474929) B474929
theorem B316631 : Blo 315835 316631 := bstep (se 1 (by rfl) ⟨237473, by rfl⟩ : syracuseStep 316631 = 474947) B474947
theorem B316651 : Blo 315835 316651 := bstep (se 1 (by rfl) ⟨237488, by rfl⟩ : syracuseStep 316651 = 474977) B474977
theorem B316663 : Blo 315835 316663 := bstep (se 1 (by rfl) ⟨237497, by rfl⟩ : syracuseStep 316663 = 474995) B474995
theorem B316683 : Blo 315835 316683 := bstep (se 1 (by rfl) ⟨237512, by rfl⟩ : syracuseStep 316683 = 475025) B475025
theorem B316695 : Blo 315835 316695 := bstep (se 1 (by rfl) ⟨237521, by rfl⟩ : syracuseStep 316695 = 475043) B475043
theorem B316715 : Blo 315835 316715 := bstep (se 1 (by rfl) ⟨237536, by rfl⟩ : syracuseStep 316715 = 475073) B475073
theorem B1070387 : Blo 315835 1070387 := bstep (se 1 (by rfl) ⟨802790, by rfl⟩ : syracuseStep 1070387 = 1605581) B1605581
theorem B316727 : Blo 315835 316727 := bstep (se 1 (by rfl) ⟨237545, by rfl⟩ : syracuseStep 316727 = 475091) B475091
theorem B316747 : Blo 315835 316747 := bstep (se 1 (by rfl) ⟨237560, by rfl⟩ : syracuseStep 316747 = 475121) B475121
theorem B316759 : Blo 315835 316759 := bstep (se 1 (by rfl) ⟨237569, by rfl⟩ : syracuseStep 316759 = 475139) B475139
theorem B316779 : Blo 315835 316779 := bstep (se 1 (by rfl) ⟨237584, by rfl⟩ : syracuseStep 316779 = 475169) B475169
theorem B316791 : Blo 315835 316791 := bstep (se 1 (by rfl) ⟨237593, by rfl⟩ : syracuseStep 316791 = 475187) B475187
theorem B316811 : Blo 315835 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B316823 : Blo 315835 316823 := bstep (se 1 (by rfl) ⟨237617, by rfl⟩ : syracuseStep 316823 = 475235) B475235
theorem B316843 : Blo 315835 316843 := bstep (se 1 (by rfl) ⟨237632, by rfl⟩ : syracuseStep 316843 = 475265) B475265
theorem B316855 : Blo 315835 316855 := bstep (se 1 (by rfl) ⟨237641, by rfl⟩ : syracuseStep 316855 = 475283) B475283
theorem B316875 : Blo 315835 316875 := bstep (se 1 (by rfl) ⟨237656, by rfl⟩ : syracuseStep 316875 = 475313) B475313
theorem B316887 : Blo 315835 316887 := bstep (se 1 (by rfl) ⟨237665, by rfl⟩ : syracuseStep 316887 = 475331) B475331
theorem B316907 : Blo 315835 316907 := bstep (se 1 (by rfl) ⟨237680, by rfl⟩ : syracuseStep 316907 = 475361) B475361
theorem B316919 : Blo 315835 316919 := bstep (se 1 (by rfl) ⟨237689, by rfl⟩ : syracuseStep 316919 = 475379) B475379
theorem B316939 : Blo 315835 316939 := bstep (se 1 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 316939 = 475409) B475409
theorem B316951 : Blo 315835 316951 := bstep (se 1 (by rfl) ⟨237713, by rfl⟩ : syracuseStep 316951 = 475427) B475427
theorem B546329 : Blo 315835 546329 := bstep (se 2 (by rfl) ⟨204873, by rfl⟩ : syracuseStep 546329 = 409747) B409747
theorem B316971 : Blo 315835 316971 := bstep (se 1 (by rfl) ⟨237728, by rfl⟩ : syracuseStep 316971 = 475457) B475457
theorem B316983 : Blo 315835 316983 := bstep (se 1 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 316983 = 475475) B475475
theorem B1070657 : Blo 315835 1070657 := bstep (se 2 (by rfl) ⟨401496, by rfl⟩ : syracuseStep 1070657 = 802993) B802993
theorem B317003 : Blo 315835 317003 := bstep (se 1 (by rfl) ⟨237752, by rfl⟩ : syracuseStep 317003 = 475505) B475505
theorem B317015 : Blo 315835 317015 := bstep (se 1 (by rfl) ⟨237761, by rfl⟩ : syracuseStep 317015 = 475523) B475523
theorem B317035 : Blo 315835 317035 := bstep (se 1 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 317035 = 475553) B475553
theorem B317047 : Blo 315835 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B317067 : Blo 315835 317067 := bstep (se 1 (by rfl) ⟨237800, by rfl⟩ : syracuseStep 317067 = 475601) B475601
theorem B317079 : Blo 315835 317079 := bstep (se 1 (by rfl) ⟨237809, by rfl⟩ : syracuseStep 317079 = 475619) B475619
theorem B317099 : Blo 315835 317099 := bstep (se 1 (by rfl) ⟨237824, by rfl⟩ : syracuseStep 317099 = 475649) B475649
theorem B317111 : Blo 315835 317111 := bstep (se 1 (by rfl) ⟨237833, by rfl⟩ : syracuseStep 317111 = 475667) B475667
theorem B317131 : Blo 315835 317131 := bstep (se 1 (by rfl) ⟨237848, by rfl⟩ : syracuseStep 317131 = 475697) B475697
theorem B317143 : Blo 315835 317143 := bstep (se 1 (by rfl) ⟨237857, by rfl⟩ : syracuseStep 317143 = 475715) B475715
theorem B317163 : Blo 315835 317163 := bstep (se 1 (by rfl) ⟨237872, by rfl⟩ : syracuseStep 317163 = 475745) B475745
theorem B317175 : Blo 315835 317175 := bstep (se 1 (by rfl) ⟨237881, by rfl⟩ : syracuseStep 317175 = 475763) B475763
theorem B317195 : Blo 315835 317195 := bstep (se 1 (by rfl) ⟨237896, by rfl⟩ : syracuseStep 317195 = 475793) B475793
theorem B2578193 : Blo 315835 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B317207 : Blo 315835 317207 := bstep (se 1 (by rfl) ⟨237905, by rfl⟩ : syracuseStep 317207 = 475811) B475811
theorem B317227 : Blo 315835 317227 := bstep (se 1 (by rfl) ⟨237920, by rfl⟩ : syracuseStep 317227 = 475841) B475841
theorem B317239 : Blo 315835 317239 := bstep (se 1 (by rfl) ⟨237929, by rfl⟩ : syracuseStep 317239 = 475859) B475859
theorem B1201985 : Blo 315835 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B317259 : Blo 315835 317259 := bstep (se 1 (by rfl) ⟨237944, by rfl⟩ : syracuseStep 317259 = 475889) B475889
theorem B317271 : Blo 315835 317271 := bstep (se 1 (by rfl) ⟨237953, by rfl⟩ : syracuseStep 317271 = 475907) B475907
theorem B2283365 : Blo 315835 2283365 := bstep (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) B428131
theorem B317291 : Blo 315835 317291 := bstep (se 1 (by rfl) ⟨237968, by rfl⟩ : syracuseStep 317291 = 475937) B475937
theorem B317303 : Blo 315835 317303 := bstep (se 1 (by rfl) ⟨237977, by rfl⟩ : syracuseStep 317303 = 475955) B475955
theorem B317323 : Blo 315835 317323 := bstep (se 1 (by rfl) ⟨237992, by rfl⟩ : syracuseStep 317323 = 475985) B475985
theorem B317335 : Blo 315835 317335 := bstep (se 1 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 317335 = 476003) B476003
theorem B677783 : Blo 315835 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B317355 : Blo 315835 317355 := bstep (se 1 (by rfl) ⟨238016, by rfl⟩ : syracuseStep 317355 = 476033) B476033
theorem B317367 : Blo 315835 317367 := bstep (se 1 (by rfl) ⟨238025, by rfl⟩ : syracuseStep 317367 = 476051) B476051
theorem B317387 : Blo 315835 317387 := bstep (se 1 (by rfl) ⟨238040, by rfl⟩ : syracuseStep 317387 = 476081) B476081
theorem B645067 : Blo 315835 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B317399 : Blo 315835 317399 := bstep (se 1 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 317399 = 476099) B476099
theorem B481241 : Blo 315835 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B317419 : Blo 315835 317419 := bstep (se 1 (by rfl) ⟨238064, by rfl⟩ : syracuseStep 317419 = 476129) B476129
theorem B317431 : Blo 315835 317431 := bstep (se 1 (by rfl) ⟨238073, by rfl⟩ : syracuseStep 317431 = 476147) B476147
theorem B710657 : Blo 315835 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B317451 : Blo 315835 317451 := bstep (se 1 (by rfl) ⟨238088, by rfl⟩ : syracuseStep 317451 = 476177) B476177
theorem B317463 : Blo 315835 317463 := bstep (se 1 (by rfl) ⟨238097, by rfl⟩ : syracuseStep 317463 = 476195) B476195
theorem B317483 : Blo 315835 317483 := bstep (se 1 (by rfl) ⟨238112, by rfl⟩ : syracuseStep 317483 = 476225) B476225
theorem B317495 : Blo 315835 317495 := bstep (se 1 (by rfl) ⟨238121, by rfl⟩ : syracuseStep 317495 = 476243) B476243
theorem B677963 : Blo 315835 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B317515 : Blo 315835 317515 := bstep (se 1 (by rfl) ⟨238136, by rfl⟩ : syracuseStep 317515 = 476273) B476273
theorem B1366091 : Blo 315835 1366091 := bstep (se 1 (by rfl) ⟨1024568, by rfl⟩ : syracuseStep 1366091 = 2049137) B2049137
theorem B317527 : Blo 315835 317527 := bstep (se 1 (by rfl) ⟨238145, by rfl⟩ : syracuseStep 317527 = 476291) B476291
theorem B546905 : Blo 315835 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B1071197 : Blo 315835 1071197 := bstep (se 3 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 1071197 = 401699) B401699
theorem B317547 : Blo 315835 317547 := bstep (se 1 (by rfl) ⟨238160, by rfl⟩ : syracuseStep 317547 = 476321) B476321
theorem B317559 : Blo 315835 317559 := bstep (se 1 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 317559 = 476339) B476339
theorem B317579 : Blo 315835 317579 := bstep (se 1 (by rfl) ⟨238184, by rfl⟩ : syracuseStep 317579 = 476369) B476369
theorem B317591 : Blo 315835 317591 := bstep (se 1 (by rfl) ⟨238193, by rfl⟩ : syracuseStep 317591 = 476387) B476387
theorem B317611 : Blo 315835 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B317623 : Blo 315835 317623 := bstep (se 1 (by rfl) ⟨238217, by rfl⟩ : syracuseStep 317623 = 476435) B476435
theorem B317643 : Blo 315835 317643 := bstep (se 1 (by rfl) ⟨238232, by rfl⟩ : syracuseStep 317643 = 476465) B476465
theorem B317655 : Blo 315835 317655 := bstep (se 1 (by rfl) ⟨238241, by rfl⟩ : syracuseStep 317655 = 476483) B476483
theorem B710873 : Blo 315835 710873 := bstep (se 2 (by rfl) ⟨266577, by rfl⟩ : syracuseStep 710873 = 533155) B533155
theorem B317675 : Blo 315835 317675 := bstep (se 1 (by rfl) ⟨238256, by rfl⟩ : syracuseStep 317675 = 476513) B476513
theorem B317687 : Blo 315835 317687 := bstep (se 1 (by rfl) ⟨238265, by rfl⟩ : syracuseStep 317687 = 476531) B476531
theorem B317707 : Blo 315835 317707 := bstep (se 1 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 317707 = 476561) B476561
theorem B317719 : Blo 315835 317719 := bstep (se 1 (by rfl) ⟨238289, by rfl⟩ : syracuseStep 317719 = 476579) B476579
theorem B317739 : Blo 315835 317739 := bstep (se 1 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 317739 = 476609) B476609
theorem B13031725 : Blo 315835 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B5822765 : Blo 315835 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B710963 : Blo 315835 710963 := bstep (se 1 (by rfl) ⟨533222, by rfl⟩ : syracuseStep 710963 = 1066445) B1066445
theorem B317751 : Blo 315835 317751 := bstep (se 1 (by rfl) ⟨238313, by rfl⟩ : syracuseStep 317751 = 476627) B476627
theorem B317771 : Blo 315835 317771 := bstep (se 1 (by rfl) ⟨238328, by rfl⟩ : syracuseStep 317771 = 476657) B476657
theorem B907595 : Blo 315835 907595 := bstep (se 1 (by rfl) ⟨680696, by rfl⟩ : syracuseStep 907595 = 1361393) B1361393
theorem B809291 : Blo 315835 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B710999 : Blo 315835 710999 := bstep (se 1 (by rfl) ⟨533249, by rfl⟩ : syracuseStep 710999 = 1066499) B1066499
theorem B317783 : Blo 315835 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B317803 : Blo 315835 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B317815 : Blo 315835 317815 := bstep (se 1 (by rfl) ⟨238361, by rfl⟩ : syracuseStep 317815 = 476723) B476723
theorem B317835 : Blo 315835 317835 := bstep (se 1 (by rfl) ⟨238376, by rfl⟩ : syracuseStep 317835 = 476753) B476753
theorem B7756181 : Blo 315835 7756181 := bstep (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) B363571
theorem B317847 : Blo 315835 317847 := bstep (se 1 (by rfl) ⟨238385, by rfl⟩ : syracuseStep 317847 = 476771) B476771
theorem B317867 : Blo 315835 317867 := bstep (se 1 (by rfl) ⟨238400, by rfl⟩ : syracuseStep 317867 = 476801) B476801
theorem B317879 : Blo 315835 317879 := bstep (se 1 (by rfl) ⟨238409, by rfl⟩ : syracuseStep 317879 = 476819) B476819
theorem B317899 : Blo 315835 317899 := bstep (se 1 (by rfl) ⟨238424, by rfl⟩ : syracuseStep 317899 = 476849) B476849
theorem B317911 : Blo 315835 317911 := bstep (se 1 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 317911 = 476867) B476867
theorem B317931 : Blo 315835 317931 := bstep (se 1 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 317931 = 476897) B476897
theorem B317943 : Blo 315835 317943 := bstep (se 1 (by rfl) ⟨238457, by rfl⟩ : syracuseStep 317943 = 476915) B476915
theorem B711179 : Blo 315835 711179 := bstep (se 1 (by rfl) ⟨533384, by rfl⟩ : syracuseStep 711179 = 1066769) B1066769
theorem B317963 : Blo 315835 317963 := bstep (se 1 (by rfl) ⟨238472, by rfl⟩ : syracuseStep 317963 = 476945) B476945
theorem B317975 : Blo 315835 317975 := bstep (se 1 (by rfl) ⟨238481, by rfl⟩ : syracuseStep 317975 = 476963) B476963
theorem B317995 : Blo 315835 317995 := bstep (se 1 (by rfl) ⟨238496, by rfl⟩ : syracuseStep 317995 = 476993) B476993
theorem B318007 : Blo 315835 318007 := bstep (se 1 (by rfl) ⟨238505, by rfl⟩ : syracuseStep 318007 = 477011) B477011
theorem B711233 : Blo 315835 711233 := bstep (se 2 (by rfl) ⟨266712, by rfl⟩ : syracuseStep 711233 = 533425) B533425
theorem B318027 : Blo 315835 318027 := bstep (se 1 (by rfl) ⟨238520, by rfl⟩ : syracuseStep 318027 = 477041) B477041
theorem B481879 : Blo 315835 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B318039 : Blo 315835 318039 := bstep (se 1 (by rfl) ⟨238529, by rfl⟩ : syracuseStep 318039 = 477059) B477059
theorem B318059 : Blo 315835 318059 := bstep (se 1 (by rfl) ⟨238544, by rfl⟩ : syracuseStep 318059 = 477089) B477089
theorem B318071 : Blo 315835 318071 := bstep (se 1 (by rfl) ⟨238553, by rfl⟩ : syracuseStep 318071 = 477107) B477107
theorem B318091 : Blo 315835 318091 := bstep (se 1 (by rfl) ⟨238568, by rfl⟩ : syracuseStep 318091 = 477137) B477137
theorem B318103 : Blo 315835 318103 := bstep (se 1 (by rfl) ⟨238577, by rfl⟩ : syracuseStep 318103 = 477155) B477155
theorem B318123 : Blo 315835 318123 := bstep (se 1 (by rfl) ⟨238592, by rfl⟩ : syracuseStep 318123 = 477185) B477185
theorem B318135 : Blo 315835 318135 := bstep (se 1 (by rfl) ⟨238601, by rfl⟩ : syracuseStep 318135 = 477203) B477203
theorem B318155 : Blo 315835 318155 := bstep (se 1 (by rfl) ⟨238616, by rfl⟩ : syracuseStep 318155 = 477233) B477233
theorem B318167 : Blo 315835 318167 := bstep (se 1 (by rfl) ⟨238625, by rfl⟩ : syracuseStep 318167 = 477251) B477251
theorem B318187 : Blo 315835 318187 := bstep (se 1 (by rfl) ⟨238640, by rfl⟩ : syracuseStep 318187 = 477281) B477281
theorem B318199 : Blo 315835 318199 := bstep (se 1 (by rfl) ⟨238649, by rfl⟩ : syracuseStep 318199 = 477299) B477299
theorem B318219 : Blo 315835 318219 := bstep (se 1 (by rfl) ⟨238664, by rfl⟩ : syracuseStep 318219 = 477329) B477329
theorem B318231 : Blo 315835 318231 := bstep (se 1 (by rfl) ⟨238673, by rfl⟩ : syracuseStep 318231 = 477347) B477347
theorem B711449 : Blo 315835 711449 := bstep (se 2 (by rfl) ⟨266793, by rfl⟩ : syracuseStep 711449 = 533587) B533587
theorem B318251 : Blo 315835 318251 := bstep (se 1 (by rfl) ⟨238688, by rfl⟩ : syracuseStep 318251 = 477377) B477377
theorem B318263 : Blo 315835 318263 := bstep (se 1 (by rfl) ⟨238697, by rfl⟩ : syracuseStep 318263 = 477395) B477395
theorem B318283 : Blo 315835 318283 := bstep (se 1 (by rfl) ⟨238712, by rfl⟩ : syracuseStep 318283 = 477425) B477425
theorem B318295 : Blo 315835 318295 := bstep (se 1 (by rfl) ⟨238721, by rfl⟩ : syracuseStep 318295 = 477443) B477443
theorem B318315 : Blo 315835 318315 := bstep (se 1 (by rfl) ⟨238736, by rfl⟩ : syracuseStep 318315 = 477473) B477473
theorem B711539 : Blo 315835 711539 := bstep (se 1 (by rfl) ⟨533654, by rfl⟩ : syracuseStep 711539 = 1067309) B1067309
theorem B318327 : Blo 315835 318327 := bstep (se 1 (by rfl) ⟨238745, by rfl⟩ : syracuseStep 318327 = 477491) B477491
theorem B318347 : Blo 315835 318347 := bstep (se 1 (by rfl) ⟨238760, by rfl⟩ : syracuseStep 318347 = 477521) B477521
theorem B711575 : Blo 315835 711575 := bstep (se 1 (by rfl) ⟨533681, by rfl⟩ : syracuseStep 711575 = 1067363) B1067363
theorem B318359 : Blo 315835 318359 := bstep (se 1 (by rfl) ⟨238769, by rfl⟩ : syracuseStep 318359 = 477539) B477539
theorem B318379 : Blo 315835 318379 := bstep (se 1 (by rfl) ⟨238784, by rfl⟩ : syracuseStep 318379 = 477569) B477569
theorem B318391 : Blo 315835 318391 := bstep (se 1 (by rfl) ⟨238793, by rfl⟩ : syracuseStep 318391 = 477587) B477587
theorem B318411 : Blo 315835 318411 := bstep (se 1 (by rfl) ⟨238808, by rfl⟩ : syracuseStep 318411 = 477617) B477617
theorem B318423 : Blo 315835 318423 := bstep (se 1 (by rfl) ⟨238817, by rfl⟩ : syracuseStep 318423 = 477635) B477635
theorem B646105 : Blo 315835 646105 := bstep (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) B484579
theorem B318443 : Blo 315835 318443 := bstep (se 1 (by rfl) ⟨238832, by rfl⟩ : syracuseStep 318443 = 477665) B477665
theorem B318455 : Blo 315835 318455 := bstep (se 1 (by rfl) ⟨238841, by rfl⟩ : syracuseStep 318455 = 477683) B477683
theorem B318475 : Blo 315835 318475 := bstep (se 1 (by rfl) ⟨238856, by rfl⟩ : syracuseStep 318475 = 477713) B477713
theorem B318487 : Blo 315835 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B318507 : Blo 315835 318507 := bstep (se 1 (by rfl) ⟨238880, by rfl⟩ : syracuseStep 318507 = 477761) B477761
theorem B1203245 : Blo 315835 1203245 := bstep (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) B451217
theorem B318519 : Blo 315835 318519 := bstep (se 1 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 318519 = 477779) B477779
theorem B711755 : Blo 315835 711755 := bstep (se 1 (by rfl) ⟨533816, by rfl⟩ : syracuseStep 711755 = 1067633) B1067633
theorem B1203275 : Blo 315835 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B318539 : Blo 315835 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B318551 : Blo 315835 318551 := bstep (se 1 (by rfl) ⟨238913, by rfl⟩ : syracuseStep 318551 = 477827) B477827
theorem B318571 : Blo 315835 318571 := bstep (se 1 (by rfl) ⟨238928, by rfl⟩ : syracuseStep 318571 = 477857) B477857
theorem B318583 : Blo 315835 318583 := bstep (se 1 (by rfl) ⟨238937, by rfl⟩ : syracuseStep 318583 = 477875) B477875
theorem B711809 : Blo 315835 711809 := bstep (se 2 (by rfl) ⟨266928, by rfl⟩ : syracuseStep 711809 = 533857) B533857
theorem B318603 : Blo 315835 318603 := bstep (se 1 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 318603 = 477905) B477905
theorem B318615 : Blo 315835 318615 := bstep (se 1 (by rfl) ⟨238961, by rfl⟩ : syracuseStep 318615 = 477923) B477923
theorem B318635 : Blo 315835 318635 := bstep (se 1 (by rfl) ⟨238976, by rfl⟩ : syracuseStep 318635 = 477953) B477953
theorem B318647 : Blo 315835 318647 := bstep (se 1 (by rfl) ⟨238985, by rfl⟩ : syracuseStep 318647 = 477971) B477971
theorem B1072331 : Blo 315835 1072331 := bstep (se 1 (by rfl) ⟨804248, by rfl⟩ : syracuseStep 1072331 = 1608497) B1608497
theorem B318667 : Blo 315835 318667 := bstep (se 1 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 318667 = 478001) B478001
theorem B318679 : Blo 315835 318679 := bstep (se 1 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 318679 = 478019) B478019
theorem B318699 : Blo 315835 318699 := bstep (se 1 (by rfl) ⟨239024, by rfl⟩ : syracuseStep 318699 = 478049) B478049
theorem B318711 : Blo 315835 318711 := bstep (se 1 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 318711 = 478067) B478067
theorem B318731 : Blo 315835 318731 := bstep (se 1 (by rfl) ⟨239048, by rfl⟩ : syracuseStep 318731 = 478097) B478097
theorem B318743 : Blo 315835 318743 := bstep (se 1 (by rfl) ⟨239057, by rfl⟩ : syracuseStep 318743 = 478115) B478115
theorem B318763 : Blo 315835 318763 := bstep (se 1 (by rfl) ⟨239072, by rfl⟩ : syracuseStep 318763 = 478145) B478145
theorem B318775 : Blo 315835 318775 := bstep (se 1 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 318775 = 478163) B478163
theorem B318795 : Blo 315835 318795 := bstep (se 1 (by rfl) ⟨239096, by rfl⟩ : syracuseStep 318795 = 478193) B478193
theorem B318807 : Blo 315835 318807 := bstep (se 1 (by rfl) ⟨239105, by rfl⟩ : syracuseStep 318807 = 478211) B478211
theorem B712025 : Blo 315835 712025 := bstep (se 2 (by rfl) ⟨267009, by rfl⟩ : syracuseStep 712025 = 534019) B534019
theorem B318827 : Blo 315835 318827 := bstep (se 1 (by rfl) ⟨239120, by rfl⟩ : syracuseStep 318827 = 478241) B478241
theorem B318839 : Blo 315835 318839 := bstep (se 1 (by rfl) ⟨239129, by rfl⟩ : syracuseStep 318839 = 478259) B478259
theorem B318859 : Blo 315835 318859 := bstep (se 1 (by rfl) ⟨239144, by rfl⟩ : syracuseStep 318859 = 478289) B478289
theorem B318871 : Blo 315835 318871 := bstep (se 1 (by rfl) ⟨239153, by rfl⟩ : syracuseStep 318871 = 478307) B478307
theorem B318891 : Blo 315835 318891 := bstep (se 1 (by rfl) ⟨239168, by rfl⟩ : syracuseStep 318891 = 478337) B478337
theorem B712115 : Blo 315835 712115 := bstep (se 1 (by rfl) ⟨534086, by rfl⟩ : syracuseStep 712115 = 1068173) B1068173
theorem B318903 : Blo 315835 318903 := bstep (se 1 (by rfl) ⟨239177, by rfl⟩ : syracuseStep 318903 = 478355) B478355
theorem B318923 : Blo 315835 318923 := bstep (se 1 (by rfl) ⟨239192, by rfl⟩ : syracuseStep 318923 = 478385) B478385
theorem B712151 : Blo 315835 712151 := bstep (se 1 (by rfl) ⟨534113, by rfl⟩ : syracuseStep 712151 = 1068227) B1068227
theorem B318935 : Blo 315835 318935 := bstep (se 1 (by rfl) ⟨239201, by rfl⟩ : syracuseStep 318935 = 478403) B478403
theorem B1072601 : Blo 315835 1072601 := bstep (se 2 (by rfl) ⟨402225, by rfl⟩ : syracuseStep 1072601 = 804451) B804451
theorem B318955 : Blo 315835 318955 := bstep (se 1 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 318955 = 478433) B478433
theorem B318967 : Blo 315835 318967 := bstep (se 1 (by rfl) ⟨239225, by rfl⟩ : syracuseStep 318967 = 478451) B478451
theorem B318987 : Blo 315835 318987 := bstep (se 1 (by rfl) ⟨239240, by rfl⟩ : syracuseStep 318987 = 478481) B478481
theorem B318999 : Blo 315835 318999 := bstep (se 1 (by rfl) ⟨239249, by rfl⟩ : syracuseStep 318999 = 478499) B478499
theorem B319019 : Blo 315835 319019 := bstep (se 1 (by rfl) ⟨239264, by rfl⟩ : syracuseStep 319019 = 478529) B478529
theorem B319031 : Blo 315835 319031 := bstep (se 1 (by rfl) ⟨239273, by rfl⟩ : syracuseStep 319031 = 478547) B478547
theorem B319051 : Blo 315835 319051 := bstep (se 1 (by rfl) ⟨239288, by rfl⟩ : syracuseStep 319051 = 478577) B478577
theorem B319063 : Blo 315835 319063 := bstep (se 1 (by rfl) ⟨239297, by rfl⟩ : syracuseStep 319063 = 478595) B478595
theorem B319083 : Blo 315835 319083 := bstep (se 1 (by rfl) ⟨239312, by rfl⟩ : syracuseStep 319083 = 478625) B478625
theorem B319095 : Blo 315835 319095 := bstep (se 1 (by rfl) ⟨239321, by rfl⟩ : syracuseStep 319095 = 478643) B478643
theorem B712331 : Blo 315835 712331 := bstep (se 1 (by rfl) ⟨534248, by rfl⟩ : syracuseStep 712331 = 1068497) B1068497
theorem B319115 : Blo 315835 319115 := bstep (se 1 (by rfl) ⟨239336, by rfl⟩ : syracuseStep 319115 = 478673) B478673
theorem B319127 : Blo 315835 319127 := bstep (se 1 (by rfl) ⟨239345, by rfl⟩ : syracuseStep 319127 = 478691) B478691
theorem B319147 : Blo 315835 319147 := bstep (se 1 (by rfl) ⟨239360, by rfl⟩ : syracuseStep 319147 = 478721) B478721
theorem B679603 : Blo 315835 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B319159 : Blo 315835 319159 := bstep (se 1 (by rfl) ⟨239369, by rfl⟩ : syracuseStep 319159 = 478739) B478739
theorem B712385 : Blo 315835 712385 := bstep (se 2 (by rfl) ⟨267144, by rfl⟩ : syracuseStep 712385 = 534289) B534289
theorem B319179 : Blo 315835 319179 := bstep (se 1 (by rfl) ⟨239384, by rfl⟩ : syracuseStep 319179 = 478769) B478769
theorem B319191 : Blo 315835 319191 := bstep (se 1 (by rfl) ⟨239393, by rfl⟩ : syracuseStep 319191 = 478787) B478787
theorem B1203929 : Blo 315835 1203929 := bstep (se 2 (by rfl) ⟨451473, by rfl⟩ : syracuseStep 1203929 = 902947) B902947
theorem B319211 : Blo 315835 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B319223 : Blo 315835 319223 := bstep (se 1 (by rfl) ⟨239417, by rfl⟩ : syracuseStep 319223 = 478835) B478835
theorem B319243 : Blo 315835 319243 := bstep (se 1 (by rfl) ⟨239432, by rfl⟩ : syracuseStep 319243 = 478865) B478865
theorem B319255 : Blo 315835 319255 := bstep (se 1 (by rfl) ⟨239441, by rfl⟩ : syracuseStep 319255 = 478883) B478883
theorem B319275 : Blo 315835 319275 := bstep (se 1 (by rfl) ⟨239456, by rfl⟩ : syracuseStep 319275 = 478913) B478913
theorem B319287 : Blo 315835 319287 := bstep (se 1 (by rfl) ⟨239465, by rfl⟩ : syracuseStep 319287 = 478931) B478931
theorem B319307 : Blo 315835 319307 := bstep (se 1 (by rfl) ⟨239480, by rfl⟩ : syracuseStep 319307 = 478961) B478961
theorem B319319 : Blo 315835 319319 := bstep (se 1 (by rfl) ⟨239489, by rfl⟩ : syracuseStep 319319 = 478979) B478979
theorem B319339 : Blo 315835 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B319351 : Blo 315835 319351 := bstep (se 1 (by rfl) ⟨239513, by rfl⟩ : syracuseStep 319351 = 479027) B479027
theorem B319371 : Blo 315835 319371 := bstep (se 1 (by rfl) ⟨239528, by rfl⟩ : syracuseStep 319371 = 479057) B479057
theorem B319383 : Blo 315835 319383 := bstep (se 1 (by rfl) ⟨239537, by rfl⟩ : syracuseStep 319383 = 479075) B479075
theorem B712601 : Blo 315835 712601 := bstep (se 2 (by rfl) ⟨267225, by rfl⟩ : syracuseStep 712601 = 534451) B534451
theorem B319403 : Blo 315835 319403 := bstep (se 1 (by rfl) ⟨239552, by rfl⟩ : syracuseStep 319403 = 479105) B479105
theorem B319415 : Blo 315835 319415 := bstep (se 1 (by rfl) ⟨239561, by rfl⟩ : syracuseStep 319415 = 479123) B479123
theorem B319435 : Blo 315835 319435 := bstep (se 1 (by rfl) ⟨239576, by rfl⟩ : syracuseStep 319435 = 479153) B479153
theorem B319447 : Blo 315835 319447 := bstep (se 1 (by rfl) ⟨239585, by rfl⟩ : syracuseStep 319447 = 479171) B479171
theorem B319467 : Blo 315835 319467 := bstep (se 1 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 319467 = 479201) B479201
theorem B712691 : Blo 315835 712691 := bstep (se 1 (by rfl) ⟨534518, by rfl⟩ : syracuseStep 712691 = 1069037) B1069037
theorem B319479 : Blo 315835 319479 := bstep (se 1 (by rfl) ⟨239609, by rfl⟩ : syracuseStep 319479 = 479219) B479219
theorem B319499 : Blo 315835 319499 := bstep (se 1 (by rfl) ⟨239624, by rfl⟩ : syracuseStep 319499 = 479249) B479249
theorem B712727 : Blo 315835 712727 := bstep (se 1 (by rfl) ⟨534545, by rfl⟩ : syracuseStep 712727 = 1069091) B1069091
theorem B1204247 : Blo 315835 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B319511 : Blo 315835 319511 := bstep (se 1 (by rfl) ⟨239633, by rfl⟩ : syracuseStep 319511 = 479267) B479267
theorem B319531 : Blo 315835 319531 := bstep (se 1 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 319531 = 479297) B479297
theorem B319543 : Blo 315835 319543 := bstep (se 1 (by rfl) ⟨239657, by rfl⟩ : syracuseStep 319543 = 479315) B479315
theorem B319563 : Blo 315835 319563 := bstep (se 1 (by rfl) ⟨239672, by rfl⟩ : syracuseStep 319563 = 479345) B479345
theorem B319575 : Blo 315835 319575 := bstep (se 1 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 319575 = 479363) B479363
theorem B319595 : Blo 315835 319595 := bstep (se 1 (by rfl) ⟨239696, by rfl⟩ : syracuseStep 319595 = 479393) B479393
theorem B319607 : Blo 315835 319607 := bstep (se 1 (by rfl) ⟨239705, by rfl⟩ : syracuseStep 319607 = 479411) B479411
theorem B319627 : Blo 315835 319627 := bstep (se 1 (by rfl) ⟨239720, by rfl⟩ : syracuseStep 319627 = 479441) B479441
theorem B1073303 : Blo 315835 1073303 := bstep (se 1 (by rfl) ⟨804977, by rfl⟩ : syracuseStep 1073303 = 1609955) B1609955
theorem B319639 : Blo 315835 319639 := bstep (se 1 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 319639 = 479459) B479459
theorem B680089 : Blo 315835 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B319659 : Blo 315835 319659 := bstep (se 1 (by rfl) ⟨239744, by rfl⟩ : syracuseStep 319659 = 479489) B479489
theorem B319671 : Blo 315835 319671 := bstep (se 1 (by rfl) ⟨239753, by rfl⟩ : syracuseStep 319671 = 479507) B479507
theorem B712907 : Blo 315835 712907 := bstep (se 1 (by rfl) ⟨534680, by rfl⟩ : syracuseStep 712907 = 1069361) B1069361
theorem B319691 : Blo 315835 319691 := bstep (se 1 (by rfl) ⟨239768, by rfl⟩ : syracuseStep 319691 = 479537) B479537
theorem B319703 : Blo 315835 319703 := bstep (se 1 (by rfl) ⟨239777, by rfl⟩ : syracuseStep 319703 = 479555) B479555
theorem B319723 : Blo 315835 319723 := bstep (se 1 (by rfl) ⟨239792, by rfl⟩ : syracuseStep 319723 = 479585) B479585
theorem B319735 : Blo 315835 319735 := bstep (se 1 (by rfl) ⟨239801, by rfl⟩ : syracuseStep 319735 = 479603) B479603
theorem B712961 : Blo 315835 712961 := bstep (se 2 (by rfl) ⟨267360, by rfl⟩ : syracuseStep 712961 = 534721) B534721
theorem B319755 : Blo 315835 319755 := bstep (se 1 (by rfl) ⟨239816, by rfl⟩ : syracuseStep 319755 = 479633) B479633
theorem B319767 : Blo 315835 319767 := bstep (se 1 (by rfl) ⟨239825, by rfl⟩ : syracuseStep 319767 = 479651) B479651
theorem B450841 : Blo 315835 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B319787 : Blo 315835 319787 := bstep (se 1 (by rfl) ⟨239840, by rfl⟩ : syracuseStep 319787 = 479681) B479681
theorem B319799 : Blo 315835 319799 := bstep (se 1 (by rfl) ⟨239849, by rfl⟩ : syracuseStep 319799 = 479699) B479699
theorem B319819 : Blo 315835 319819 := bstep (se 1 (by rfl) ⟨239864, by rfl⟩ : syracuseStep 319819 = 479729) B479729
theorem B319831 : Blo 315835 319831 := bstep (se 1 (by rfl) ⟨239873, by rfl⟩ : syracuseStep 319831 = 479747) B479747
theorem B450955 : Blo 315835 450955 := bstep (se 1 (by rfl) ⟨338216, by rfl⟩ : syracuseStep 450955 = 676433) B676433
theorem B1139147 : Blo 315835 1139147 := bstep (se 1 (by rfl) ⟨854360, by rfl⟩ : syracuseStep 1139147 = 1708721) B1708721
theorem B713177 : Blo 315835 713177 := bstep (se 2 (by rfl) ⟨267441, by rfl⟩ : syracuseStep 713177 = 534883) B534883
theorem B2744867 : Blo 315835 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B713267 : Blo 315835 713267 := bstep (se 1 (by rfl) ⟨534950, by rfl⟩ : syracuseStep 713267 = 1069901) B1069901
theorem B713303 : Blo 315835 713303 := bstep (se 1 (by rfl) ⟨534977, by rfl⟩ : syracuseStep 713303 = 1069955) B1069955
theorem B1401517 : Blo 315835 1401517 := bstep (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) B525569
theorem B1204915 : Blo 315835 1204915 := bstep (se 1 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 1204915 = 1807373) B1807373
theorem B1073843 : Blo 315835 1073843 := bstep (se 1 (by rfl) ⟨805382, by rfl⟩ : syracuseStep 1073843 = 1610765) B1610765
theorem B713483 : Blo 315835 713483 := bstep (se 1 (by rfl) ⟨535112, by rfl⟩ : syracuseStep 713483 = 1070225) B1070225
theorem B713537 : Blo 315835 713537 := bstep (se 2 (by rfl) ⟨267576, by rfl⟩ : syracuseStep 713537 = 535153) B535153
theorem B582475 : Blo 315835 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B1074113 : Blo 315835 1074113 := bstep (se 2 (by rfl) ⟨402792, by rfl⟩ : syracuseStep 1074113 = 805585) B805585
theorem B713753 : Blo 315835 713753 := bstep (se 2 (by rfl) ⟨267657, by rfl⟩ : syracuseStep 713753 = 535315) B535315
theorem B713843 : Blo 315835 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B713879 : Blo 315835 713879 := bstep (se 1 (by rfl) ⟨535409, by rfl⟩ : syracuseStep 713879 = 1070819) B1070819
theorem B648343 : Blo 315835 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B714059 : Blo 315835 714059 := bstep (se 1 (by rfl) ⟨535544, by rfl⟩ : syracuseStep 714059 = 1071089) B1071089
theorem B714113 : Blo 315835 714113 := bstep (se 2 (by rfl) ⟨267792, by rfl⟩ : syracuseStep 714113 = 535585) B535585
theorem B1074653 : Blo 315835 1074653 := bstep (se 3 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 1074653 = 402995) B402995
theorem B681473 : Blo 315835 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B714329 : Blo 315835 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B714419 : Blo 315835 714419 := bstep (se 1 (by rfl) ⟨535814, by rfl⟩ : syracuseStep 714419 = 1071629) B1071629
theorem B452299 : Blo 315835 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B714455 : Blo 315835 714455 := bstep (se 1 (by rfl) ⟨535841, by rfl⟩ : syracuseStep 714455 = 1071683) B1071683
theorem B714635 : Blo 315835 714635 := bstep (se 1 (by rfl) ⟨535976, by rfl⟩ : syracuseStep 714635 = 1071953) B1071953
theorem B1206161 : Blo 315835 1206161 := bstep (se 2 (by rfl) ⟨452310, by rfl⟩ : syracuseStep 1206161 = 904621) B904621
theorem B714689 : Blo 315835 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B452567 : Blo 315835 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B681995 : Blo 315835 681995 := bstep (se 1 (by rfl) ⟨511496, by rfl⟩ : syracuseStep 681995 = 1022993) B1022993
theorem B3041297 : Blo 315835 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B714905 : Blo 315835 714905 := bstep (se 2 (by rfl) ⟨268089, by rfl⟩ : syracuseStep 714905 = 536179) B536179
theorem B714995 : Blo 315835 714995 := bstep (se 1 (by rfl) ⟨536246, by rfl⟩ : syracuseStep 714995 = 1072493) B1072493
theorem B715031 : Blo 315835 715031 := bstep (se 1 (by rfl) ⟨536273, by rfl⟩ : syracuseStep 715031 = 1072547) B1072547
theorem B2713931 : Blo 315835 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B715211 : Blo 315835 715211 := bstep (se 1 (by rfl) ⟨536408, by rfl⟩ : syracuseStep 715211 = 1072817) B1072817
theorem B715265 : Blo 315835 715265 := bstep (se 2 (by rfl) ⟨268224, by rfl⟩ : syracuseStep 715265 = 536449) B536449
theorem B1206859 : Blo 315835 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B1075787 : Blo 315835 1075787 := bstep (se 1 (by rfl) ⟨806840, by rfl⟩ : syracuseStep 1075787 = 1613681) B1613681
theorem B1305305 : Blo 315835 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B715481 : Blo 315835 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B3631877 : Blo 315835 3631877 := bstep (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) B680977
theorem B486155 : Blo 315835 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B715571 : Blo 315835 715571 := bstep (se 1 (by rfl) ⟨536678, by rfl⟩ : syracuseStep 715571 = 1073357) B1073357
theorem B715607 : Blo 315835 715607 := bstep (se 1 (by rfl) ⟨536705, by rfl⟩ : syracuseStep 715607 = 1073411) B1073411
theorem B1076057 : Blo 315835 1076057 := bstep (se 2 (by rfl) ⟨403521, by rfl⟩ : syracuseStep 1076057 = 807043) B807043
theorem B1207133 : Blo 315835 1207133 := bstep (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) B452675
theorem B453529 : Blo 315835 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B715787 : Blo 315835 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B355351 : Blo 315835 355351 := bstep (se 1 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 355351 = 533027) B533027
theorem B715841 : Blo 315835 715841 := bstep (se 2 (by rfl) ⟨268440, by rfl⟩ : syracuseStep 715841 = 536881) B536881
theorem B355531 : Blo 315835 355531 := bstep (se 1 (by rfl) ⟨266648, by rfl⟩ : syracuseStep 355531 = 533297) B533297
theorem B716057 : Blo 315835 716057 := bstep (se 2 (by rfl) ⟨268521, by rfl⟩ : syracuseStep 716057 = 537043) B537043
theorem B355639 : Blo 315835 355639 := bstep (se 1 (by rfl) ⟨266729, by rfl⟩ : syracuseStep 355639 = 533459) B533459
theorem B4582757 : Blo 315835 4582757 := bstep (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) B859267
theorem B716147 : Blo 315835 716147 := bstep (se 1 (by rfl) ⟨537110, by rfl⟩ : syracuseStep 716147 = 1074221) B1074221
theorem B716183 : Blo 315835 716183 := bstep (se 1 (by rfl) ⟨537137, by rfl⟩ : syracuseStep 716183 = 1074275) B1074275
theorem B1535411 : Blo 315835 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B355819 : Blo 315835 355819 := bstep (se 1 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 355819 = 533729) B533729
theorem B1207831 : Blo 315835 1207831 := bstep (se 1 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 1207831 = 1811747) B1811747
theorem B1076759 : Blo 315835 1076759 := bstep (se 1 (by rfl) ⟨807569, by rfl⟩ : syracuseStep 1076759 = 1615139) B1615139
theorem B912971 : Blo 315835 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B716363 : Blo 315835 716363 := bstep (se 1 (by rfl) ⟨537272, by rfl⟩ : syracuseStep 716363 = 1074545) B1074545
theorem B355927 : Blo 315835 355927 := bstep (se 1 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 355927 = 533891) B533891
theorem B716417 : Blo 315835 716417 := bstep (se 2 (by rfl) ⟨268656, by rfl⟩ : syracuseStep 716417 = 537313) B537313
theorem B356107 : Blo 315835 356107 := bstep (se 1 (by rfl) ⟨267080, by rfl⟩ : syracuseStep 356107 = 534161) B534161
theorem B716633 : Blo 315835 716633 := bstep (se 2 (by rfl) ⟨268737, by rfl⟩ : syracuseStep 716633 = 537475) B537475
theorem B356215 : Blo 315835 356215 := bstep (se 1 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 356215 = 534323) B534323
theorem B716723 : Blo 315835 716723 := bstep (se 1 (by rfl) ⟨537542, by rfl⟩ : syracuseStep 716723 = 1075085) B1075085
theorem B716759 : Blo 315835 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B356395 : Blo 315835 356395 := bstep (se 1 (by rfl) ⟨267296, by rfl⟩ : syracuseStep 356395 = 534593) B534593
theorem B1077299 : Blo 315835 1077299 := bstep (se 1 (by rfl) ⟨807974, by rfl⟩ : syracuseStep 1077299 = 1615949) B1615949
theorem B716939 : Blo 315835 716939 := bstep (se 1 (by rfl) ⟨537704, by rfl⟩ : syracuseStep 716939 = 1075409) B1075409
theorem B6942871 : Blo 315835 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B356503 : Blo 315835 356503 := bstep (se 1 (by rfl) ⟨267377, by rfl⟩ : syracuseStep 356503 = 534755) B534755
theorem B716993 : Blo 315835 716993 := bstep (se 2 (by rfl) ⟨268872, by rfl⟩ : syracuseStep 716993 = 537745) B537745
theorem B1208621 : Blo 315835 1208621 := bstep (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) B453233
theorem B1077569 : Blo 315835 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B356683 : Blo 315835 356683 := bstep (se 1 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 356683 = 535025) B535025
theorem B2289995 : Blo 315835 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B454987 : Blo 315835 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B454999 : Blo 315835 454999 := bstep (se 1 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 454999 = 682499) B682499
theorem B717209 : Blo 315835 717209 := bstep (se 2 (by rfl) ⟨268953, by rfl⟩ : syracuseStep 717209 = 537907) B537907
theorem B356791 : Blo 315835 356791 := bstep (se 1 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 356791 = 535187) B535187
theorem B1012189 : Blo 315835 1012189 := bstep (se 3 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 1012189 = 379571) B379571
theorem B717299 : Blo 315835 717299 := bstep (se 1 (by rfl) ⟨537974, by rfl⟩ : syracuseStep 717299 = 1075949) B1075949
theorem B717335 : Blo 315835 717335 := bstep (se 1 (by rfl) ⟨538001, by rfl⟩ : syracuseStep 717335 = 1076003) B1076003
theorem B356971 : Blo 315835 356971 := bstep (se 1 (by rfl) ⟨267728, by rfl⟩ : syracuseStep 356971 = 535457) B535457
theorem B1602179 : Blo 315835 1602179 := bstep (se 1 (by rfl) ⟨1201634, by rfl⟩ : syracuseStep 1602179 = 2403269) B2403269
theorem B1798807 : Blo 315835 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B717515 : Blo 315835 717515 := bstep (se 1 (by rfl) ⟨538136, by rfl⟩ : syracuseStep 717515 = 1076273) B1076273
theorem B357079 : Blo 315835 357079 := bstep (se 1 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 357079 = 535619) B535619
theorem B717569 : Blo 315835 717569 := bstep (se 2 (by rfl) ⟨269088, by rfl⟩ : syracuseStep 717569 = 538177) B538177
theorem B1307443 : Blo 315835 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1078109 : Blo 315835 1078109 := bstep (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) B404291
theorem B357259 : Blo 315835 357259 := bstep (se 1 (by rfl) ⟨267944, by rfl⟩ : syracuseStep 357259 = 535889) B535889
theorem B685003 : Blo 315835 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B717785 : Blo 315835 717785 := bstep (se 2 (by rfl) ⟨269169, by rfl⟩ : syracuseStep 717785 = 538339) B538339
theorem B357367 : Blo 315835 357367 := bstep (se 1 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 357367 = 536051) B536051
theorem B717875 : Blo 315835 717875 := bstep (se 1 (by rfl) ⟨538406, by rfl⟩ : syracuseStep 717875 = 1076813) B1076813
theorem B717911 : Blo 315835 717911 := bstep (se 1 (by rfl) ⟨538433, by rfl⟩ : syracuseStep 717911 = 1076867) B1076867
theorem B357547 : Blo 315835 357547 := bstep (se 1 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 357547 = 536321) B536321
theorem B718091 : Blo 315835 718091 := bstep (se 1 (by rfl) ⟨538568, by rfl⟩ : syracuseStep 718091 = 1077137) B1077137
theorem B357655 : Blo 315835 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B718145 : Blo 315835 718145 := bstep (se 2 (by rfl) ⟨269304, by rfl⟩ : syracuseStep 718145 = 538609) B538609
theorem B357835 : Blo 315835 357835 := bstep (se 1 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 357835 = 536753) B536753
theorem B718361 : Blo 315835 718361 := bstep (se 2 (by rfl) ⟨269385, by rfl⟩ : syracuseStep 718361 = 538771) B538771
theorem B357943 : Blo 315835 357943 := bstep (se 1 (by rfl) ⟨268457, by rfl⟩ : syracuseStep 357943 = 536915) B536915
theorem B718451 : Blo 315835 718451 := bstep (se 1 (by rfl) ⟨538838, by rfl⟩ : syracuseStep 718451 = 1077677) B1077677
theorem B1144451 : Blo 315835 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B718487 : Blo 315835 718487 := bstep (se 1 (by rfl) ⟨538865, by rfl⟩ : syracuseStep 718487 = 1077731) B1077731
theorem B1210049 : Blo 315835 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B358123 : Blo 315835 358123 := bstep (se 1 (by rfl) ⟨268592, by rfl⟩ : syracuseStep 358123 = 537185) B537185
theorem B587521 : Blo 315835 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B718667 : Blo 315835 718667 := bstep (se 1 (by rfl) ⟨539000, by rfl⟩ : syracuseStep 718667 = 1078001) B1078001
theorem B358231 : Blo 315835 358231 := bstep (se 1 (by rfl) ⟨268673, by rfl⟩ : syracuseStep 358231 = 537347) B537347
theorem B718721 : Blo 315835 718721 := bstep (se 2 (by rfl) ⟨269520, by rfl⟩ : syracuseStep 718721 = 539041) B539041
theorem B1079243 : Blo 315835 1079243 := bstep (se 1 (by rfl) ⟨809432, by rfl⟩ : syracuseStep 1079243 = 1618865) B1618865
theorem B358411 : Blo 315835 358411 := bstep (se 1 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 358411 = 537617) B537617
theorem B718937 : Blo 315835 718937 := bstep (se 2 (by rfl) ⟨269601, by rfl⟩ : syracuseStep 718937 = 539203) B539203
theorem B358519 : Blo 315835 358519 := bstep (se 1 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 358519 = 537779) B537779
theorem B719027 : Blo 315835 719027 := bstep (se 1 (by rfl) ⟨539270, by rfl⟩ : syracuseStep 719027 = 1078541) B1078541
theorem B719063 : Blo 315835 719063 := bstep (se 1 (by rfl) ⟨539297, by rfl⟩ : syracuseStep 719063 = 1078595) B1078595
theorem B358699 : Blo 315835 358699 := bstep (se 1 (by rfl) ⟨269024, by rfl⟩ : syracuseStep 358699 = 538049) B538049
theorem B719243 : Blo 315835 719243 := bstep (se 1 (by rfl) ⟨539432, by rfl⟩ : syracuseStep 719243 = 1078865) B1078865
theorem B358807 : Blo 315835 358807 := bstep (se 1 (by rfl) ⟨269105, by rfl⟩ : syracuseStep 358807 = 538211) B538211
theorem B719297 : Blo 315835 719297 := bstep (se 2 (by rfl) ⟨269736, by rfl⟩ : syracuseStep 719297 = 539473) B539473
theorem B2980313 : Blo 315835 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B358987 : Blo 315835 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B1637015 : Blo 315835 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B719513 : Blo 315835 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B359095 : Blo 315835 359095 := bstep (se 1 (by rfl) ⟨269321, by rfl⟩ : syracuseStep 359095 = 538643) B538643
theorem B719603 : Blo 315835 719603 := bstep (se 1 (by rfl) ⟨539702, by rfl⟩ : syracuseStep 719603 = 1079405) B1079405
theorem B1538909 : Blo 315835 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B359275 : Blo 315835 359275 := bstep (se 1 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 359275 = 538913) B538913
theorem B359383 : Blo 315835 359383 := bstep (se 1 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 359383 = 539075) B539075
theorem B359563 : Blo 315835 359563 := bstep (se 1 (by rfl) ⟨269672, by rfl⟩ : syracuseStep 359563 = 539345) B539345
theorem B1211537 : Blo 315835 1211537 := bstep (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) B908653
theorem B359671 : Blo 315835 359671 := bstep (se 1 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 359671 = 539507) B539507
theorem B2489777 : Blo 315835 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B6094349 : Blo 315835 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B3276323 : Blo 315835 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B1211993 : Blo 315835 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B1212205 : Blo 315835 1212205 := bstep (se 3 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 1212205 = 454577) B454577
theorem B3112921 : Blo 315835 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B819575 : Blo 315835 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B1802681 : Blo 315835 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B3637709 : Blo 315835 3637709 := bstep (se 3 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 3637709 = 1364141) B1364141
theorem B1212995 : Blo 315835 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B3670721 : Blo 315835 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1114913 : Blo 315835 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1868689 : Blo 315835 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1606553 : Blo 315835 1606553 := bstep (se 2 (by rfl) ⟨602457, by rfl⟩ : syracuseStep 1606553 = 1204915) B1204915
theorem B1213451 : Blo 315835 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B1148141 : Blo 315835 1148141 := bstep (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) B430553
theorem B787979 : Blo 315835 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B2426597 : Blo 315835 2426597 := bstep (se 4 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 2426597 = 454987) B454987
theorem B1771721 : Blo 315835 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B6621425 : Blo 315835 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B363143 : Blo 315835 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B1609145 : Blo 315835 1609145 := bstep (se 2 (by rfl) ⟨603429, by rfl⟩ : syracuseStep 1609145 = 1206859) B1206859
theorem B364219 : Blo 315835 364219 := bstep (se 1 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 364219 = 546329) B546329
theorem B855809 : Blo 315835 855809 := bstep (se 2 (by rfl) ⟨320928, by rfl⟩ : syracuseStep 855809 = 641857) B641857
theorem B364603 : Blo 315835 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B1610441 : Blo 315835 1610441 := bstep (se 2 (by rfl) ⟨603915, by rfl⟩ : syracuseStep 1610441 = 1207831) B1207831
theorem B1283309 : Blo 315835 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B759431 : Blo 315835 759431 := bstep (se 1 (by rfl) ⟨569573, by rfl⟩ : syracuseStep 759431 = 1139147) B1139147
theorem B1349585 : Blo 315835 1349585 := bstep (se 2 (by rfl) ⟨506094, by rfl⟩ : syracuseStep 1349585 = 1012189) B1012189
theorem B2398409 : Blo 315835 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B1743257 : Blo 315835 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B400135 : Blo 315835 400135 := bstep (se 1 (by rfl) ⟨300101, by rfl⟩ : syracuseStep 400135 = 600203) B600203
theorem B1809287 : Blo 315835 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B4365373 : Blo 315835 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B400555 : Blo 315835 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400783 : Blo 315835 400783 := bstep (se 1 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 400783 = 601175) B601175
theorem B4660739 : Blo 315835 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B3055171 : Blo 315835 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B1023607 : Blo 315835 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B1711961 : Blo 315835 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B401527 : Blo 315835 401527 := bstep (se 1 (by rfl) ⟨301145, by rfl⟩ : syracuseStep 401527 = 602291) B602291
theorem B5775533 : Blo 315835 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B17375633 : Blo 315835 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B401851 : Blo 315835 401851 := bstep (se 1 (by rfl) ⟨301388, by rfl⟩ : syracuseStep 401851 = 602777) B602777
theorem B533263 : Blo 315835 533263 := bstep (se 1 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 533263 = 799895) B799895
theorem B402347 : Blo 315835 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B762967 : Blo 315835 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B861473 : Blo 315835 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B533803 : Blo 315835 533803 := bstep (se 1 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 533803 = 800705) B800705
theorem B402823 : Blo 315835 402823 := bstep (se 1 (by rfl) ⟨302117, by rfl⟩ : syracuseStep 402823 = 604235) B604235
theorem B533945 : Blo 315835 533945 := bstep (se 2 (by rfl) ⟨200229, by rfl⟩ : syracuseStep 533945 = 400459) B400459
theorem B22029893 : Blo 315835 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B927607 : Blo 315835 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B403319 : Blo 315835 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B1025939 : Blo 315835 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B403471 : Blo 315835 403471 := bstep (se 1 (by rfl) ⟨302603, by rfl⟩ : syracuseStep 403471 = 605207) B605207
theorem B534647 : Blo 315835 534647 := bstep (se 1 (by rfl) ⟨400985, by rfl⟩ : syracuseStep 534647 = 801971) B801971
theorem B403643 : Blo 315835 403643 := bstep (se 1 (by rfl) ⟨302732, by rfl⟩ : syracuseStep 403643 = 605465) B605465
theorem B1517939 : Blo 315835 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B1616273 : Blo 315835 1616273 := bstep (se 2 (by rfl) ⟨606102, by rfl⟩ : syracuseStep 1616273 = 1212205) B1212205
theorem B1681817 : Blo 315835 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B600635 : Blo 315835 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B535099 : Blo 315835 535099 := bstep (se 1 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 535099 = 802649) B802649
theorem B535241 : Blo 315835 535241 := bstep (se 2 (by rfl) ⟨200715, by rfl⟩ : syracuseStep 535241 = 401431) B401431
theorem B6859525 : Blo 315835 6859525 := bstep (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) B1286161
theorem B2763571 : Blo 315835 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1354643 : Blo 315835 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B338951 : Blo 315835 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B601121 : Blo 315835 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B404615 : Blo 315835 404615 := bstep (se 1 (by rfl) ⟨303461, by rfl⟩ : syracuseStep 404615 = 606923) B606923
theorem B601273 : Blo 315835 601273 := bstep (se 2 (by rfl) ⟨225477, by rfl⟩ : syracuseStep 601273 = 450955) B450955
theorem B535943 : Blo 315835 535943 := bstep (se 1 (by rfl) ⟨401957, by rfl⟩ : syracuseStep 535943 = 803915) B803915
theorem B1060249 : Blo 315835 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B1813913 : Blo 315835 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B1289681 : Blo 315835 1289681 := bstep (se 2 (by rfl) ⟨483630, by rfl⟩ : syracuseStep 1289681 = 967261) B967261
theorem B339643 : Blo 315835 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B1027873 : Blo 315835 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B405391 : Blo 315835 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B536591 : Blo 315835 536591 := bstep (se 1 (by rfl) ⟨402443, by rfl⟩ : syracuseStep 536591 = 804887) B804887
theorem B1224791 : Blo 315835 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B7319645 : Blo 315835 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B1716461 : Blo 315835 1716461 := bstep (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) B643673
theorem B1618379 : Blo 315835 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B537131 : Blo 315835 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B766523 : Blo 315835 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B1618703 : Blo 315835 1618703 := bstep (se 1 (by rfl) ⟨1214027, by rfl⟩ : syracuseStep 1618703 = 2428055) B2428055
theorem B1356659 : Blo 315835 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B603065 : Blo 315835 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B537529 : Blo 315835 537529 := bstep (se 2 (by rfl) ⟨201573, by rfl⟩ : syracuseStep 537529 = 403147) B403147
theorem B963613 : Blo 315835 963613 := bstep (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) B361355
theorem B767177 : Blo 315835 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B5813639 : Blo 315835 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B538231 : Blo 315835 538231 := bstep (se 1 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 538231 = 807347) B807347
theorem B964243 : Blo 315835 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B800513 : Blo 315835 800513 := bstep (se 2 (by rfl) ⟨300192, by rfl⟩ : syracuseStep 800513 = 600385) B600385
theorem B538427 : Blo 315835 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B5125963 : Blo 315835 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B767945 : Blo 315835 767945 := bstep (se 2 (by rfl) ⟨287979, by rfl⟩ : syracuseStep 767945 = 575959) B575959
theorem B1521629 : Blo 315835 1521629 := bstep (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) B570611
theorem B800887 : Blo 315835 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B538825 : Blo 315835 538825 := bstep (se 2 (by rfl) ⟨202059, by rfl⟩ : syracuseStep 538825 = 404119) B404119
theorem B3258883 : Blo 315835 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B1718795 : Blo 315835 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B801323 : Blo 315835 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B1522243 : Blo 315835 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B473771 : Blo 315835 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B1817261 : Blo 315835 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B572089 : Blo 315835 572089 := bstep (se 2 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 572089 = 429067) B429067
theorem B473801 : Blo 315835 473801 := bstep (se 2 (by rfl) ⟨177675, by rfl⟩ : syracuseStep 473801 = 355351) B355351
theorem B473915 : Blo 315835 473915 := bstep (se 1 (by rfl) ⟨355436, by rfl⟩ : syracuseStep 473915 = 710873) B710873
theorem B3881843 : Blo 315835 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B473975 : Blo 315835 473975 := bstep (se 1 (by rfl) ⟨355481, by rfl⟩ : syracuseStep 473975 = 710963) B710963
theorem B605063 : Blo 315835 605063 := bstep (se 1 (by rfl) ⟨453797, by rfl⟩ : syracuseStep 605063 = 907595) B907595
theorem B539527 : Blo 315835 539527 := bstep (se 1 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 539527 = 809291) B809291
theorem B473999 : Blo 315835 473999 := bstep (se 1 (by rfl) ⟨355499, by rfl⟩ : syracuseStep 473999 = 710999) B710999
theorem B474041 : Blo 315835 474041 := bstep (se 2 (by rfl) ⟨177765, by rfl⟩ : syracuseStep 474041 = 355531) B355531
theorem B474119 : Blo 315835 474119 := bstep (se 1 (by rfl) ⟨355589, by rfl⟩ : syracuseStep 474119 = 711179) B711179
theorem B1621003 : Blo 315835 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B474155 : Blo 315835 474155 := bstep (se 1 (by rfl) ⟨355616, by rfl⟩ : syracuseStep 474155 = 711233) B711233
theorem B474185 : Blo 315835 474185 := bstep (se 2 (by rfl) ⟨177819, by rfl⟩ : syracuseStep 474185 = 355639) B355639
theorem B5160023 : Blo 315835 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B474299 : Blo 315835 474299 := bstep (se 1 (by rfl) ⟨355724, by rfl⟩ : syracuseStep 474299 = 711449) B711449
theorem B474359 : Blo 315835 474359 := bstep (se 1 (by rfl) ⟨355769, by rfl⟩ : syracuseStep 474359 = 711539) B711539
theorem B474383 : Blo 315835 474383 := bstep (se 1 (by rfl) ⟨355787, by rfl⟩ : syracuseStep 474383 = 711575) B711575
theorem B572687 : Blo 315835 572687 := bstep (se 1 (by rfl) ⟨429515, by rfl⟩ : syracuseStep 572687 = 859031) B859031
theorem B1359119 : Blo 315835 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B474425 : Blo 315835 474425 := bstep (se 2 (by rfl) ⟨177909, by rfl⟩ : syracuseStep 474425 = 355819) B355819
theorem B802163 : Blo 315835 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B474503 : Blo 315835 474503 := bstep (se 1 (by rfl) ⟨355877, by rfl⟩ : syracuseStep 474503 = 711755) B711755
theorem B802183 : Blo 315835 802183 := bstep (se 1 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 802183 = 1203275) B1203275
theorem B474539 : Blo 315835 474539 := bstep (se 1 (by rfl) ⟨355904, by rfl⟩ : syracuseStep 474539 = 711809) B711809
theorem B474569 : Blo 315835 474569 := bstep (se 2 (by rfl) ⟨177963, by rfl⟩ : syracuseStep 474569 = 355927) B355927
theorem B474683 : Blo 315835 474683 := bstep (se 1 (by rfl) ⟨356012, by rfl⟩ : syracuseStep 474683 = 712025) B712025
theorem B474743 : Blo 315835 474743 := bstep (se 1 (by rfl) ⟨356057, by rfl⟩ : syracuseStep 474743 = 712115) B712115
theorem B474767 : Blo 315835 474767 := bstep (se 1 (by rfl) ⟨356075, by rfl⟩ : syracuseStep 474767 = 712151) B712151
theorem B802457 : Blo 315835 802457 := bstep (se 2 (by rfl) ⟨300921, by rfl⟩ : syracuseStep 802457 = 601843) B601843
theorem B474809 : Blo 315835 474809 := bstep (se 2 (by rfl) ⟨178053, by rfl⟩ : syracuseStep 474809 = 356107) B356107
theorem B2408129 : Blo 315835 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B474887 : Blo 315835 474887 := bstep (se 1 (by rfl) ⟨356165, by rfl⟩ : syracuseStep 474887 = 712331) B712331
theorem B474923 : Blo 315835 474923 := bstep (se 1 (by rfl) ⟨356192, by rfl⟩ : syracuseStep 474923 = 712385) B712385
theorem B802619 : Blo 315835 802619 := bstep (se 1 (by rfl) ⟨601964, by rfl⟩ : syracuseStep 802619 = 1203929) B1203929
theorem B474953 : Blo 315835 474953 := bstep (se 2 (by rfl) ⟨178107, by rfl⟩ : syracuseStep 474953 = 356215) B356215
theorem B475067 : Blo 315835 475067 := bstep (se 1 (by rfl) ⟨356300, by rfl⟩ : syracuseStep 475067 = 712601) B712601
theorem B475127 : Blo 315835 475127 := bstep (se 1 (by rfl) ⟨356345, by rfl⟩ : syracuseStep 475127 = 712691) B712691
theorem B901135 : Blo 315835 901135 := bstep (se 1 (by rfl) ⟨675851, by rfl⟩ : syracuseStep 901135 = 1351703) B1351703
theorem B475151 : Blo 315835 475151 := bstep (se 1 (by rfl) ⟨356363, by rfl⟩ : syracuseStep 475151 = 712727) B712727
theorem B802831 : Blo 315835 802831 := bstep (se 1 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 802831 = 1204247) B1204247
theorem B475193 : Blo 315835 475193 := bstep (se 2 (by rfl) ⟨178197, by rfl⟩ : syracuseStep 475193 = 356395) B356395
theorem B901181 : Blo 315835 901181 := bstep (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) B337943
theorem B475271 : Blo 315835 475271 := bstep (se 1 (by rfl) ⟨356453, by rfl⟩ : syracuseStep 475271 = 712907) B712907
theorem B475307 : Blo 315835 475307 := bstep (se 1 (by rfl) ⟨356480, by rfl⟩ : syracuseStep 475307 = 712961) B712961
theorem B6144173 : Blo 315835 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B9257161 : Blo 315835 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B475337 : Blo 315835 475337 := bstep (se 2 (by rfl) ⟨178251, by rfl⟩ : syracuseStep 475337 = 356503) B356503
theorem B803105 : Blo 315835 803105 := bstep (se 2 (by rfl) ⟨301164, by rfl⟩ : syracuseStep 803105 = 602329) B602329
theorem B475451 : Blo 315835 475451 := bstep (se 1 (by rfl) ⟨356588, by rfl⟩ : syracuseStep 475451 = 713177) B713177
theorem B475511 : Blo 315835 475511 := bstep (se 1 (by rfl) ⟨356633, by rfl⟩ : syracuseStep 475511 = 713267) B713267
theorem B475535 : Blo 315835 475535 := bstep (se 1 (by rfl) ⟨356651, by rfl⟩ : syracuseStep 475535 = 713303) B713303
theorem B901523 : Blo 315835 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B475577 : Blo 315835 475577 := bstep (se 2 (by rfl) ⟨178341, by rfl⟩ : syracuseStep 475577 = 356683) B356683
theorem B606665 : Blo 315835 606665 := bstep (se 2 (by rfl) ⟨227499, by rfl⟩ : syracuseStep 606665 = 454999) B454999
theorem B475655 : Blo 315835 475655 := bstep (se 1 (by rfl) ⟨356741, by rfl⟩ : syracuseStep 475655 = 713483) B713483
theorem B475691 : Blo 315835 475691 := bstep (se 1 (by rfl) ⟨356768, by rfl⟩ : syracuseStep 475691 = 713537) B713537
theorem B1360451 : Blo 315835 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B475721 : Blo 315835 475721 := bstep (se 2 (by rfl) ⟨178395, by rfl⟩ : syracuseStep 475721 = 356791) B356791
theorem B9814709 : Blo 315835 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B475835 : Blo 315835 475835 := bstep (se 1 (by rfl) ⟨356876, by rfl⟩ : syracuseStep 475835 = 713753) B713753
theorem B4735705 : Blo 315835 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B475895 : Blo 315835 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B475919 : Blo 315835 475919 := bstep (se 1 (by rfl) ⟨356939, by rfl⟩ : syracuseStep 475919 = 713879) B713879
theorem B3261221 : Blo 315835 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B3457829 : Blo 315835 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B475961 : Blo 315835 475961 := bstep (se 2 (by rfl) ⟨178485, by rfl⟩ : syracuseStep 475961 = 356971) B356971
theorem B476039 : Blo 315835 476039 := bstep (se 1 (by rfl) ⟨357029, by rfl⟩ : syracuseStep 476039 = 714059) B714059
theorem B1360793 : Blo 315835 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B476075 : Blo 315835 476075 := bstep (se 1 (by rfl) ⟨357056, by rfl⟩ : syracuseStep 476075 = 714113) B714113
theorem B476105 : Blo 315835 476105 := bstep (se 2 (by rfl) ⟨178539, by rfl⟩ : syracuseStep 476105 = 357079) B357079
theorem B15516629 : Blo 315835 15516629 := bstep (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) B363671
theorem B1066013 : Blo 315835 1066013 := bstep (se 3 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 1066013 = 399755) B399755
theorem B476219 : Blo 315835 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B476279 : Blo 315835 476279 := bstep (se 1 (by rfl) ⟨357209, by rfl⟩ : syracuseStep 476279 = 714419) B714419
theorem B476303 : Blo 315835 476303 := bstep (se 1 (by rfl) ⟨357227, by rfl⟩ : syracuseStep 476303 = 714455) B714455
theorem B476345 : Blo 315835 476345 := bstep (se 2 (by rfl) ⟨178629, by rfl⟩ : syracuseStep 476345 = 357259) B357259
theorem B476423 : Blo 315835 476423 := bstep (se 1 (by rfl) ⟨357317, by rfl⟩ : syracuseStep 476423 = 714635) B714635
theorem B902411 : Blo 315835 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B804107 : Blo 315835 804107 := bstep (se 1 (by rfl) ⟨603080, by rfl⟩ : syracuseStep 804107 = 1206161) B1206161
theorem B2934049 : Blo 315835 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B476459 : Blo 315835 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B476489 : Blo 315835 476489 := bstep (se 2 (by rfl) ⟨178683, by rfl⟩ : syracuseStep 476489 = 357367) B357367
theorem B476603 : Blo 315835 476603 := bstep (se 1 (by rfl) ⟨357452, by rfl⟩ : syracuseStep 476603 = 714905) B714905
theorem B476663 : Blo 315835 476663 := bstep (se 1 (by rfl) ⟨357497, by rfl⟩ : syracuseStep 476663 = 714995) B714995
theorem B476687 : Blo 315835 476687 := bstep (se 1 (by rfl) ⟨357515, by rfl⟩ : syracuseStep 476687 = 715031) B715031
theorem B476729 : Blo 315835 476729 := bstep (se 2 (by rfl) ⟨178773, by rfl⟩ : syracuseStep 476729 = 357547) B357547
theorem B476807 : Blo 315835 476807 := bstep (se 1 (by rfl) ⟨357605, by rfl⟩ : syracuseStep 476807 = 715211) B715211
theorem B476843 : Blo 315835 476843 := bstep (se 1 (by rfl) ⟨357632, by rfl⟩ : syracuseStep 476843 = 715265) B715265
theorem B10798771 : Blo 315835 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B476873 : Blo 315835 476873 := bstep (se 2 (by rfl) ⟨178827, by rfl⟩ : syracuseStep 476873 = 357655) B357655
theorem B870203 : Blo 315835 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B476987 : Blo 315835 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B477047 : Blo 315835 477047 := bstep (se 1 (by rfl) ⟨357785, by rfl⟩ : syracuseStep 477047 = 715571) B715571
theorem B477071 : Blo 315835 477071 := bstep (se 1 (by rfl) ⟨357803, by rfl⟩ : syracuseStep 477071 = 715607) B715607
theorem B640915 : Blo 315835 640915 := bstep (se 1 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 640915 = 961373) B961373
theorem B804755 : Blo 315835 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B2738083 : Blo 315835 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B477113 : Blo 315835 477113 := bstep (se 2 (by rfl) ⟨178917, by rfl⟩ : syracuseStep 477113 = 357835) B357835
theorem B477191 : Blo 315835 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B2279447 : Blo 315835 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B1296413 : Blo 315835 1296413 := bstep (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) B486155
theorem B477227 : Blo 315835 477227 := bstep (se 1 (by rfl) ⟨357920, by rfl⟩ : syracuseStep 477227 = 715841) B715841
theorem B477257 : Blo 315835 477257 := bstep (se 2 (by rfl) ⟨178971, by rfl⟩ : syracuseStep 477257 = 357943) B357943
theorem B641159 : Blo 315835 641159 := bstep (se 1 (by rfl) ⟨480869, by rfl⟩ : syracuseStep 641159 = 961739) B961739
theorem B805049 : Blo 315835 805049 := bstep (se 2 (by rfl) ⟨301893, by rfl⟩ : syracuseStep 805049 = 603787) B603787
theorem B477371 : Blo 315835 477371 := bstep (se 1 (by rfl) ⟨358028, by rfl⟩ : syracuseStep 477371 = 716057) B716057
theorem B477431 : Blo 315835 477431 := bstep (se 1 (by rfl) ⟨358073, by rfl⟩ : syracuseStep 477431 = 716147) B716147
theorem B477455 : Blo 315835 477455 := bstep (se 1 (by rfl) ⟨358091, by rfl⟩ : syracuseStep 477455 = 716183) B716183
theorem B477497 : Blo 315835 477497 := bstep (se 2 (by rfl) ⟨179061, by rfl⟩ : syracuseStep 477497 = 358123) B358123
theorem B608647 : Blo 315835 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B477575 : Blo 315835 477575 := bstep (se 1 (by rfl) ⟨358181, by rfl⟩ : syracuseStep 477575 = 716363) B716363
theorem B1067417 : Blo 315835 1067417 := bstep (se 2 (by rfl) ⟨400281, by rfl⟩ : syracuseStep 1067417 = 800563) B800563
theorem B477611 : Blo 315835 477611 := bstep (se 1 (by rfl) ⟨358208, by rfl⟩ : syracuseStep 477611 = 716417) B716417
theorem B477641 : Blo 315835 477641 := bstep (se 2 (by rfl) ⟨179115, by rfl⟩ : syracuseStep 477641 = 358231) B358231
theorem B477755 : Blo 315835 477755 := bstep (se 1 (by rfl) ⟨358316, by rfl⟩ : syracuseStep 477755 = 716633) B716633
theorem B477815 : Blo 315835 477815 := bstep (se 1 (by rfl) ⟨358361, by rfl⟩ : syracuseStep 477815 = 716723) B716723
theorem B477839 : Blo 315835 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B477881 : Blo 315835 477881 := bstep (se 2 (by rfl) ⟨179205, by rfl⟩ : syracuseStep 477881 = 358411) B358411
theorem B477959 : Blo 315835 477959 := bstep (se 1 (by rfl) ⟨358469, by rfl⟩ : syracuseStep 477959 = 716939) B716939
theorem B477995 : Blo 315835 477995 := bstep (se 1 (by rfl) ⟨358496, by rfl⟩ : syracuseStep 477995 = 716993) B716993
theorem B510779 : Blo 315835 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B478025 : Blo 315835 478025 := bstep (se 2 (by rfl) ⟨179259, by rfl⟩ : syracuseStep 478025 = 358519) B358519
theorem B2280307 : Blo 315835 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B904051 : Blo 315835 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B805747 : Blo 315835 805747 := bstep (se 1 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 805747 = 1208621) B1208621
theorem B1526663 : Blo 315835 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B478139 : Blo 315835 478139 := bstep (se 1 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 478139 = 717209) B717209
theorem B478199 : Blo 315835 478199 := bstep (se 1 (by rfl) ⟨358649, by rfl⟩ : syracuseStep 478199 = 717299) B717299
theorem B805889 : Blo 315835 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B14797835 : Blo 315835 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B2411531 : Blo 315835 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B478223 : Blo 315835 478223 := bstep (se 1 (by rfl) ⟨358667, by rfl⟩ : syracuseStep 478223 = 717335) B717335
theorem B478265 : Blo 315835 478265 := bstep (se 2 (by rfl) ⟨179349, by rfl⟩ : syracuseStep 478265 = 358699) B358699
theorem B1068119 : Blo 315835 1068119 := bstep (se 1 (by rfl) ⟨801089, by rfl⟩ : syracuseStep 1068119 = 1602179) B1602179
theorem B904279 : Blo 315835 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B478343 : Blo 315835 478343 := bstep (se 1 (by rfl) ⟨358757, by rfl⟩ : syracuseStep 478343 = 717515) B717515
theorem B478379 : Blo 315835 478379 := bstep (se 1 (by rfl) ⟨358784, by rfl⟩ : syracuseStep 478379 = 717569) B717569
theorem B478409 : Blo 315835 478409 := bstep (se 2 (by rfl) ⟨179403, by rfl⟩ : syracuseStep 478409 = 358807) B358807
theorem B478523 : Blo 315835 478523 := bstep (se 1 (by rfl) ⟨358892, by rfl⟩ : syracuseStep 478523 = 717785) B717785
theorem B478583 : Blo 315835 478583 := bstep (se 1 (by rfl) ⟨358937, by rfl⟩ : syracuseStep 478583 = 717875) B717875
theorem B478607 : Blo 315835 478607 := bstep (se 1 (by rfl) ⟨358955, by rfl⟩ : syracuseStep 478607 = 717911) B717911
theorem B478649 : Blo 315835 478649 := bstep (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) B358987
theorem B642505 : Blo 315835 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B806345 : Blo 315835 806345 := bstep (se 2 (by rfl) ⟨302379, by rfl⟩ : syracuseStep 806345 = 604759) B604759
theorem B1199569 : Blo 315835 1199569 := bstep (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) B899677
theorem B4607441 : Blo 315835 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B478727 : Blo 315835 478727 := bstep (se 1 (by rfl) ⟨359045, by rfl⟩ : syracuseStep 478727 = 718091) B718091
theorem B478763 : Blo 315835 478763 := bstep (se 1 (by rfl) ⟨359072, by rfl⟩ : syracuseStep 478763 = 718145) B718145
theorem B1068605 : Blo 315835 1068605 := bstep (se 3 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 1068605 = 400727) B400727
theorem B478793 : Blo 315835 478793 := bstep (se 2 (by rfl) ⟨179547, by rfl⟩ : syracuseStep 478793 = 359095) B359095
theorem B478907 : Blo 315835 478907 := bstep (se 1 (by rfl) ⟨359180, by rfl⟩ : syracuseStep 478907 = 718361) B718361
theorem B478967 : Blo 315835 478967 := bstep (se 1 (by rfl) ⟨359225, by rfl⟩ : syracuseStep 478967 = 718451) B718451
theorem B1199873 : Blo 315835 1199873 := bstep (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) B899905
theorem B6311681 : Blo 315835 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B478991 : Blo 315835 478991 := bstep (se 1 (by rfl) ⟨359243, by rfl⟩ : syracuseStep 478991 = 718487) B718487
theorem B806699 : Blo 315835 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B479033 : Blo 315835 479033 := bstep (se 2 (by rfl) ⟨179637, by rfl⟩ : syracuseStep 479033 = 359275) B359275
theorem B2215795 : Blo 315835 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B479111 : Blo 315835 479111 := bstep (se 1 (by rfl) ⟨359333, by rfl⟩ : syracuseStep 479111 = 718667) B718667
theorem B479147 : Blo 315835 479147 := bstep (se 1 (by rfl) ⟨359360, by rfl⟩ : syracuseStep 479147 = 718721) B718721
theorem B479177 : Blo 315835 479177 := bstep (se 2 (by rfl) ⟨179691, by rfl⟩ : syracuseStep 479177 = 359383) B359383
theorem B479291 : Blo 315835 479291 := bstep (se 1 (by rfl) ⟨359468, by rfl⟩ : syracuseStep 479291 = 718937) B718937
theorem B479351 : Blo 315835 479351 := bstep (se 1 (by rfl) ⟨359513, by rfl⟩ : syracuseStep 479351 = 719027) B719027
theorem B479375 : Blo 315835 479375 := bstep (se 1 (by rfl) ⟨359531, by rfl⟩ : syracuseStep 479375 = 719063) B719063
theorem B479417 : Blo 315835 479417 := bstep (se 2 (by rfl) ⟨179781, by rfl⟩ : syracuseStep 479417 = 359563) B359563
theorem B1200329 : Blo 315835 1200329 := bstep (se 2 (by rfl) ⟨450123, by rfl⟩ : syracuseStep 1200329 = 900247) B900247
theorem B479495 : Blo 315835 479495 := bstep (se 1 (by rfl) ⟨359621, by rfl⟩ : syracuseStep 479495 = 719243) B719243
theorem B479531 : Blo 315835 479531 := bstep (se 1 (by rfl) ⟨359648, by rfl⟩ : syracuseStep 479531 = 719297) B719297
theorem B1986875 : Blo 315835 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B479561 : Blo 315835 479561 := bstep (se 2 (by rfl) ⟨179835, by rfl⟩ : syracuseStep 479561 = 359671) B359671
theorem B315835 : Blo 315835 315835 := bstep (se 1 (by rfl) ⟨236876, by rfl⟩ : syracuseStep 315835 = 473753) B473753
theorem B479675 : Blo 315835 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B479735 : Blo 315835 479735 := bstep (se 1 (by rfl) ⟨359801, by rfl⟩ : syracuseStep 479735 = 719603) B719603
theorem B315911 : Blo 315835 315911 := bstep (se 1 (by rfl) ⟨236933, by rfl⟩ : syracuseStep 315911 = 473867) B473867
theorem B315919 : Blo 315835 315919 := bstep (se 1 (by rfl) ⟨236939, by rfl⟩ : syracuseStep 315919 = 473879) B473879
theorem B315963 : Blo 315835 315963 := bstep (se 1 (by rfl) ⟨236972, by rfl⟩ : syracuseStep 315963 = 473945) B473945
theorem B316039 : Blo 315835 316039 := bstep (se 1 (by rfl) ⟨237029, by rfl⟩ : syracuseStep 316039 = 474059) B474059
theorem B905863 : Blo 315835 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B316047 : Blo 315835 316047 := bstep (se 1 (by rfl) ⟨237035, by rfl⟩ : syracuseStep 316047 = 474071) B474071
theorem B316091 : Blo 315835 316091 := bstep (se 1 (by rfl) ⟨237068, by rfl⟩ : syracuseStep 316091 = 474137) B474137
theorem B316167 : Blo 315835 316167 := bstep (se 1 (by rfl) ⟨237125, by rfl⟩ : syracuseStep 316167 = 474251) B474251
theorem B807691 : Blo 315835 807691 := bstep (se 1 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 807691 = 1211537) B1211537
theorem B316175 : Blo 315835 316175 := bstep (se 1 (by rfl) ⟨237131, by rfl⟩ : syracuseStep 316175 = 474263) B474263
theorem B316219 : Blo 315835 316219 := bstep (se 1 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 316219 = 474329) B474329
theorem B316295 : Blo 315835 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B316303 : Blo 315835 316303 := bstep (se 1 (by rfl) ⟨237227, by rfl⟩ : syracuseStep 316303 = 474455) B474455
theorem B906137 : Blo 315835 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B807833 : Blo 315835 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B2413475 : Blo 315835 2413475 := bstep (se 1 (by rfl) ⟨1810106, by rfl⟩ : syracuseStep 2413475 = 3620213) B3620213
theorem B1070009 : Blo 315835 1070009 := bstep (se 2 (by rfl) ⟨401253, by rfl⟩ : syracuseStep 1070009 = 802507) B802507
theorem B316347 : Blo 315835 316347 := bstep (se 1 (by rfl) ⟨237260, by rfl⟩ : syracuseStep 316347 = 474521) B474521
theorem B1659851 : Blo 315835 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B316423 : Blo 315835 316423 := bstep (se 1 (by rfl) ⟨237317, by rfl⟩ : syracuseStep 316423 = 474635) B474635
theorem B316431 : Blo 315835 316431 := bstep (se 1 (by rfl) ⟨237323, by rfl⟩ : syracuseStep 316431 = 474647) B474647
theorem B2184215 : Blo 315835 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B316475 : Blo 315835 316475 := bstep (se 1 (by rfl) ⟨237356, by rfl⟩ : syracuseStep 316475 = 474713) B474713
theorem B807995 : Blo 315835 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B3626045 : Blo 315835 3626045 := bstep (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) B1359767
theorem B316551 : Blo 315835 316551 := bstep (se 1 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 316551 = 474827) B474827
theorem B316559 : Blo 315835 316559 := bstep (se 1 (by rfl) ⟨237419, by rfl⟩ : syracuseStep 316559 = 474839) B474839
theorem B316603 : Blo 315835 316603 := bstep (se 1 (by rfl) ⟨237452, by rfl⟩ : syracuseStep 316603 = 474905) B474905
theorem B316679 : Blo 315835 316679 := bstep (se 1 (by rfl) ⟨237509, by rfl⟩ : syracuseStep 316679 = 475019) B475019
theorem B316687 : Blo 315835 316687 := bstep (se 1 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 316687 = 475031) B475031
theorem B4150561 : Blo 315835 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B316731 : Blo 315835 316731 := bstep (se 1 (by rfl) ⟨237548, by rfl⟩ : syracuseStep 316731 = 475097) B475097
theorem B1725785 : Blo 315835 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B316807 : Blo 315835 316807 := bstep (se 1 (by rfl) ⟨237605, by rfl⟩ : syracuseStep 316807 = 475211) B475211
theorem B316815 : Blo 315835 316815 := bstep (se 1 (by rfl) ⟨237611, by rfl⟩ : syracuseStep 316815 = 475223) B475223
theorem B808339 : Blo 315835 808339 := bstep (se 1 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 808339 = 1212509) B1212509
theorem B316859 : Blo 315835 316859 := bstep (se 1 (by rfl) ⟨237644, by rfl⟩ : syracuseStep 316859 = 475289) B475289
theorem B316935 : Blo 315835 316935 := bstep (se 1 (by rfl) ⟨237701, by rfl⟩ : syracuseStep 316935 = 475403) B475403
theorem B1070603 : Blo 315835 1070603 := bstep (se 1 (by rfl) ⟨802952, by rfl⟩ : syracuseStep 1070603 = 1605905) B1605905
theorem B316943 : Blo 315835 316943 := bstep (se 1 (by rfl) ⟨237707, by rfl⟩ : syracuseStep 316943 = 475415) B475415
theorem B906785 : Blo 315835 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B808481 : Blo 315835 808481 := bstep (se 2 (by rfl) ⟨303180, by rfl⟩ : syracuseStep 808481 = 606361) B606361
theorem B316987 : Blo 315835 316987 := bstep (se 1 (by rfl) ⟨237740, by rfl⟩ : syracuseStep 316987 = 475481) B475481
theorem B1070711 : Blo 315835 1070711 := bstep (se 1 (by rfl) ⟨803033, by rfl⟩ : syracuseStep 1070711 = 1606067) B1606067
theorem B972407 : Blo 315835 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B317063 : Blo 315835 317063 := bstep (se 1 (by rfl) ⟨237797, by rfl⟩ : syracuseStep 317063 = 475595) B475595
theorem B317071 : Blo 315835 317071 := bstep (se 1 (by rfl) ⟨237803, by rfl⟩ : syracuseStep 317071 = 475607) B475607
theorem B317115 : Blo 315835 317115 := bstep (se 1 (by rfl) ⟨237836, by rfl⟩ : syracuseStep 317115 = 475673) B475673
theorem B317191 : Blo 315835 317191 := bstep (se 1 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 317191 = 475787) B475787
theorem B317199 : Blo 315835 317199 := bstep (se 1 (by rfl) ⟨237899, by rfl⟩ : syracuseStep 317199 = 475799) B475799
theorem B317243 : Blo 315835 317243 := bstep (se 1 (by rfl) ⟨237932, by rfl⟩ : syracuseStep 317243 = 475865) B475865
theorem B317319 : Blo 315835 317319 := bstep (se 1 (by rfl) ⟨237989, by rfl⟩ : syracuseStep 317319 = 475979) B475979
theorem B317327 : Blo 315835 317327 := bstep (se 1 (by rfl) ⟨237995, by rfl⟩ : syracuseStep 317327 = 475991) B475991
theorem B317371 : Blo 315835 317371 := bstep (se 1 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 317371 = 476057) B476057
theorem B317447 : Blo 315835 317447 := bstep (se 1 (by rfl) ⟨238085, by rfl⟩ : syracuseStep 317447 = 476171) B476171
theorem B317455 : Blo 315835 317455 := bstep (se 1 (by rfl) ⟨238091, by rfl⟩ : syracuseStep 317455 = 476183) B476183
theorem B317499 : Blo 315835 317499 := bstep (se 1 (by rfl) ⟨238124, by rfl⟩ : syracuseStep 317499 = 476249) B476249
theorem B317575 : Blo 315835 317575 := bstep (se 1 (by rfl) ⟨238181, by rfl⟩ : syracuseStep 317575 = 476363) B476363
theorem B317583 : Blo 315835 317583 := bstep (se 1 (by rfl) ⟨238187, by rfl⟩ : syracuseStep 317583 = 476375) B476375
theorem B678073 : Blo 315835 678073 := bstep (se 2 (by rfl) ⟨254277, by rfl⟩ : syracuseStep 678073 = 508555) B508555
theorem B317627 : Blo 315835 317627 := bstep (se 1 (by rfl) ⟨238220, by rfl⟩ : syracuseStep 317627 = 476441) B476441
theorem B1071305 : Blo 315835 1071305 := bstep (se 2 (by rfl) ⟨401739, by rfl⟩ : syracuseStep 1071305 = 803479) B803479
theorem B317703 : Blo 315835 317703 := bstep (se 1 (by rfl) ⟨238277, by rfl⟩ : syracuseStep 317703 = 476555) B476555
theorem B710927 : Blo 315835 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B317711 : Blo 315835 317711 := bstep (se 1 (by rfl) ⟨238283, by rfl⟩ : syracuseStep 317711 = 476567) B476567
theorem B3430673 : Blo 315835 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B710945 : Blo 315835 710945 := bstep (se 2 (by rfl) ⟨266604, by rfl⟩ : syracuseStep 710945 = 533209) B533209
theorem B317755 : Blo 315835 317755 := bstep (se 1 (by rfl) ⟨238316, by rfl⟩ : syracuseStep 317755 = 476633) B476633
theorem B317831 : Blo 315835 317831 := bstep (se 1 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 317831 = 476747) B476747
theorem B317839 : Blo 315835 317839 := bstep (se 1 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 317839 = 476759) B476759
theorem B776633 : Blo 315835 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B317883 : Blo 315835 317883 := bstep (se 1 (by rfl) ⟨238412, by rfl⟩ : syracuseStep 317883 = 476825) B476825
theorem B809473 : Blo 315835 809473 := bstep (se 2 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 809473 = 607105) B607105
theorem B317959 : Blo 315835 317959 := bstep (se 1 (by rfl) ⟨238469, by rfl⟩ : syracuseStep 317959 = 476939) B476939
theorem B907787 : Blo 315835 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B678415 : Blo 315835 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B317967 : Blo 315835 317967 := bstep (se 1 (by rfl) ⟨238475, by rfl⟩ : syracuseStep 317967 = 476951) B476951
theorem B318011 : Blo 315835 318011 := bstep (se 1 (by rfl) ⟨238508, by rfl⟩ : syracuseStep 318011 = 477017) B477017
theorem B3758669 : Blo 315835 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B711287 : Blo 315835 711287 := bstep (se 1 (by rfl) ⟨533465, by rfl⟩ : syracuseStep 711287 = 1066931) B1066931
theorem B318087 : Blo 315835 318087 := bstep (se 1 (by rfl) ⟨238565, by rfl⟩ : syracuseStep 318087 = 477131) B477131
theorem B318095 : Blo 315835 318095 := bstep (se 1 (by rfl) ⟨238571, by rfl⟩ : syracuseStep 318095 = 477143) B477143
theorem B318139 : Blo 315835 318139 := bstep (se 1 (by rfl) ⟨238604, by rfl⟩ : syracuseStep 318139 = 477209) B477209
theorem B318215 : Blo 315835 318215 := bstep (se 1 (by rfl) ⟨238661, by rfl⟩ : syracuseStep 318215 = 477323) B477323
theorem B318223 : Blo 315835 318223 := bstep (se 1 (by rfl) ⟨238667, by rfl⟩ : syracuseStep 318223 = 477335) B477335
theorem B711467 : Blo 315835 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B318267 : Blo 315835 318267 := bstep (se 1 (by rfl) ⟨238700, by rfl⟩ : syracuseStep 318267 = 477401) B477401
theorem B1072007 : Blo 315835 1072007 := bstep (se 1 (by rfl) ⟨804005, by rfl⟩ : syracuseStep 1072007 = 1608011) B1608011
theorem B318343 : Blo 315835 318343 := bstep (se 1 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 318343 = 477515) B477515
theorem B318351 : Blo 315835 318351 := bstep (se 1 (by rfl) ⟨238763, by rfl⟩ : syracuseStep 318351 = 477527) B477527
theorem B5823413 : Blo 315835 5823413 := bstep (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) B545945
theorem B318395 : Blo 315835 318395 := bstep (se 1 (by rfl) ⟨238796, by rfl⟩ : syracuseStep 318395 = 477593) B477593
theorem B12409861 : Blo 315835 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B318471 : Blo 315835 318471 := bstep (se 1 (by rfl) ⟨238853, by rfl⟩ : syracuseStep 318471 = 477707) B477707
theorem B384007 : Blo 315835 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B5397515 : Blo 315835 5397515 := bstep (se 1 (by rfl) ⟨4048136, by rfl⟩ : syracuseStep 5397515 = 8096273) B8096273
theorem B318479 : Blo 315835 318479 := bstep (se 1 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 318479 = 477719) B477719
theorem B318523 : Blo 315835 318523 := bstep (se 1 (by rfl) ⟨238892, by rfl⟩ : syracuseStep 318523 = 477785) B477785
theorem B318599 : Blo 315835 318599 := bstep (se 1 (by rfl) ⟨238949, by rfl⟩ : syracuseStep 318599 = 477899) B477899
theorem B318607 : Blo 315835 318607 := bstep (se 1 (by rfl) ⟨238955, by rfl⟩ : syracuseStep 318607 = 477911) B477911
theorem B711827 : Blo 315835 711827 := bstep (se 1 (by rfl) ⟨533870, by rfl⟩ : syracuseStep 711827 = 1067741) B1067741
theorem B318651 : Blo 315835 318651 := bstep (se 1 (by rfl) ⟨238988, by rfl⟩ : syracuseStep 318651 = 477977) B477977
theorem B711881 : Blo 315835 711881 := bstep (se 2 (by rfl) ⟨266955, by rfl⟩ : syracuseStep 711881 = 533911) B533911
theorem B1203457 : Blo 315835 1203457 := bstep (se 2 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 1203457 = 902593) B902593
theorem B1072385 : Blo 315835 1072385 := bstep (se 2 (by rfl) ⟨402144, by rfl⟩ : syracuseStep 1072385 = 804289) B804289
theorem B318727 : Blo 315835 318727 := bstep (se 1 (by rfl) ⟨239045, by rfl⟩ : syracuseStep 318727 = 478091) B478091
theorem B318735 : Blo 315835 318735 := bstep (se 1 (by rfl) ⟨239051, by rfl⟩ : syracuseStep 318735 = 478103) B478103
theorem B2415905 : Blo 315835 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B318779 : Blo 315835 318779 := bstep (se 1 (by rfl) ⟨239084, by rfl⟩ : syracuseStep 318779 = 478169) B478169
theorem B777559 : Blo 315835 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B4873607 : Blo 315835 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B679303 : Blo 315835 679303 := bstep (se 1 (by rfl) ⟨509477, by rfl⟩ : syracuseStep 679303 = 1018955) B1018955
theorem B318855 : Blo 315835 318855 := bstep (se 1 (by rfl) ⟨239141, by rfl⟩ : syracuseStep 318855 = 478283) B478283
theorem B318863 : Blo 315835 318863 := bstep (se 1 (by rfl) ⟨239147, by rfl⟩ : syracuseStep 318863 = 478295) B478295
theorem B318907 : Blo 315835 318907 := bstep (se 1 (by rfl) ⟨239180, by rfl⟩ : syracuseStep 318907 = 478361) B478361
theorem B318983 : Blo 315835 318983 := bstep (se 1 (by rfl) ⟨239237, by rfl⟩ : syracuseStep 318983 = 478475) B478475
theorem B318991 : Blo 315835 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B319035 : Blo 315835 319035 := bstep (se 1 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 319035 = 478553) B478553
theorem B319111 : Blo 315835 319111 := bstep (se 1 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 319111 = 478667) B478667
theorem B319119 : Blo 315835 319119 := bstep (se 1 (by rfl) ⟨239339, by rfl⟩ : syracuseStep 319119 = 478679) B478679
theorem B319163 : Blo 315835 319163 := bstep (se 1 (by rfl) ⟨239372, by rfl⟩ : syracuseStep 319163 = 478745) B478745
theorem B319239 : Blo 315835 319239 := bstep (se 1 (by rfl) ⟨239429, by rfl⟩ : syracuseStep 319239 = 478859) B478859
theorem B319247 : Blo 315835 319247 := bstep (se 1 (by rfl) ⟨239435, by rfl⟩ : syracuseStep 319247 = 478871) B478871
theorem B2711333 : Blo 315835 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B319291 : Blo 315835 319291 := bstep (se 1 (by rfl) ⟨239468, by rfl⟩ : syracuseStep 319291 = 478937) B478937
theorem B712583 : Blo 315835 712583 := bstep (se 1 (by rfl) ⟨534437, by rfl⟩ : syracuseStep 712583 = 1068875) B1068875
theorem B319367 : Blo 315835 319367 := bstep (se 1 (by rfl) ⟨239525, by rfl⟩ : syracuseStep 319367 = 479051) B479051
theorem B319375 : Blo 315835 319375 := bstep (se 1 (by rfl) ⟨239531, by rfl⟩ : syracuseStep 319375 = 479063) B479063
theorem B319419 : Blo 315835 319419 := bstep (se 1 (by rfl) ⟨239564, by rfl⟩ : syracuseStep 319419 = 479129) B479129
theorem B319495 : Blo 315835 319495 := bstep (se 1 (by rfl) ⟨239621, by rfl⟩ : syracuseStep 319495 = 479243) B479243
theorem B319503 : Blo 315835 319503 := bstep (se 1 (by rfl) ⟨239627, by rfl⟩ : syracuseStep 319503 = 479255) B479255
theorem B1073195 : Blo 315835 1073195 := bstep (se 1 (by rfl) ⟨804896, by rfl⟩ : syracuseStep 1073195 = 1609793) B1609793
theorem B712763 : Blo 315835 712763 := bstep (se 1 (by rfl) ⟨534572, by rfl⟩ : syracuseStep 712763 = 1069145) B1069145
theorem B319547 : Blo 315835 319547 := bstep (se 1 (by rfl) ⟨239660, by rfl⟩ : syracuseStep 319547 = 479321) B479321
theorem B1466435 : Blo 315835 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B319623 : Blo 315835 319623 := bstep (se 1 (by rfl) ⟨239717, by rfl⟩ : syracuseStep 319623 = 479435) B479435
theorem B319631 : Blo 315835 319631 := bstep (se 1 (by rfl) ⟨239723, by rfl⟩ : syracuseStep 319631 = 479447) B479447
theorem B712889 : Blo 315835 712889 := bstep (se 2 (by rfl) ⟨267333, by rfl⟩ : syracuseStep 712889 = 534667) B534667
theorem B319675 : Blo 315835 319675 := bstep (se 1 (by rfl) ⟨239756, by rfl⟩ : syracuseStep 319675 = 479513) B479513
theorem B2416877 : Blo 315835 2416877 := bstep (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) B906329
theorem B319751 : Blo 315835 319751 := bstep (se 1 (by rfl) ⟨239813, by rfl⟩ : syracuseStep 319751 = 479627) B479627
theorem B319759 : Blo 315835 319759 := bstep (se 1 (by rfl) ⟨239819, by rfl⟩ : syracuseStep 319759 = 479639) B479639
theorem B319803 : Blo 315835 319803 := bstep (se 1 (by rfl) ⟨239852, by rfl⟩ : syracuseStep 319803 = 479705) B479705
theorem B2023865 : Blo 315835 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B713231 : Blo 315835 713231 := bstep (se 1 (by rfl) ⟨534923, by rfl⟩ : syracuseStep 713231 = 1069847) B1069847
theorem B713249 : Blo 315835 713249 := bstep (se 2 (by rfl) ⟨267468, by rfl⟩ : syracuseStep 713249 = 534937) B534937
theorem B680491 : Blo 315835 680491 := bstep (se 1 (by rfl) ⟨510368, by rfl⟩ : syracuseStep 680491 = 1020737) B1020737
theorem B909883 : Blo 315835 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B1368695 : Blo 315835 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B680567 : Blo 315835 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B713591 : Blo 315835 713591 := bstep (se 1 (by rfl) ⟨535193, by rfl⟩ : syracuseStep 713591 = 1070387) B1070387
theorem B1532951 : Blo 315835 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B713771 : Blo 315835 713771 := bstep (se 1 (by rfl) ⟨535328, by rfl⟩ : syracuseStep 713771 = 1070657) B1070657
theorem B484409 : Blo 315835 484409 := bstep (se 2 (by rfl) ⟨181653, by rfl⟩ : syracuseStep 484409 = 363307) B363307
theorem B451855 : Blo 315835 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B1074491 : Blo 315835 1074491 := bstep (se 1 (by rfl) ⟨805868, by rfl⟩ : syracuseStep 1074491 = 1611737) B1611737
theorem B451975 : Blo 315835 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B910727 : Blo 315835 910727 := bstep (se 1 (by rfl) ⟨683045, by rfl⟩ : syracuseStep 910727 = 1366091) B1366091
theorem B714131 : Blo 315835 714131 := bstep (se 1 (by rfl) ⟨535598, by rfl⟩ : syracuseStep 714131 = 1071197) B1071197
theorem B714185 : Blo 315835 714185 := bstep (se 2 (by rfl) ⟨267819, by rfl⟩ : syracuseStep 714185 = 535639) B535639
theorem B812587 : Blo 315835 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B5170787 : Blo 315835 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B1074977 : Blo 315835 1074977 := bstep (se 2 (by rfl) ⟨403116, by rfl⟩ : syracuseStep 1074977 = 806233) B806233
theorem B812843 : Blo 315835 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B9135989 : Blo 315835 9135989 := bstep (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) B856499
theorem B1206359 : Blo 315835 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B2418821 : Blo 315835 2418821 := bstep (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) B453529
theorem B714887 : Blo 315835 714887 := bstep (se 1 (by rfl) ⟨536165, by rfl⟩ : syracuseStep 714887 = 1072331) B1072331
theorem B715067 : Blo 315835 715067 := bstep (se 1 (by rfl) ⟨536300, by rfl⟩ : syracuseStep 715067 = 1072601) B1072601
theorem B1075571 : Blo 315835 1075571 := bstep (se 1 (by rfl) ⟨806678, by rfl⟩ : syracuseStep 1075571 = 1613357) B1613357
theorem B485767 : Blo 315835 485767 := bstep (se 1 (by rfl) ⟨364325, by rfl⟩ : syracuseStep 485767 = 728651) B728651
theorem B715193 : Blo 315835 715193 := bstep (se 2 (by rfl) ⟨268197, by rfl⟩ : syracuseStep 715193 = 536395) B536395
theorem B3434957 : Blo 315835 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B1206845 : Blo 315835 1206845 := bstep (se 3 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 1206845 = 452567) B452567
theorem B715535 : Blo 315835 715535 := bstep (se 1 (by rfl) ⟨536651, by rfl⟩ : syracuseStep 715535 = 1073303) B1073303
theorem B715553 : Blo 315835 715553 := bstep (se 2 (by rfl) ⟨268332, by rfl⟩ : syracuseStep 715553 = 536665) B536665
theorem B453433 : Blo 315835 453433 := bstep (se 2 (by rfl) ⟨170037, by rfl⟩ : syracuseStep 453433 = 340075) B340075
theorem B355387 : Blo 315835 355387 := bstep (se 1 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 355387 = 533081) B533081
theorem B715895 : Blo 315835 715895 := bstep (se 1 (by rfl) ⟨536921, by rfl⟩ : syracuseStep 715895 = 1073843) B1073843
theorem B5401889 : Blo 315835 5401889 := bstep (se 2 (by rfl) ⟨2025708, by rfl⟩ : syracuseStep 5401889 = 4051417) B4051417
theorem B716075 : Blo 315835 716075 := bstep (se 1 (by rfl) ⟨537056, by rfl⟩ : syracuseStep 716075 = 1074113) B1074113
theorem B1600883 : Blo 315835 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B3599801 : Blo 315835 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B355855 : Blo 315835 355855 := bstep (se 1 (by rfl) ⟨266891, by rfl⟩ : syracuseStep 355855 = 533783) B533783
theorem B1142333 : Blo 315835 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B58453589 : Blo 315835 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B716435 : Blo 315835 716435 := bstep (se 1 (by rfl) ⟨537326, by rfl⟩ : syracuseStep 716435 = 1074653) B1074653
theorem B716489 : Blo 315835 716489 := bstep (se 2 (by rfl) ⟨268683, by rfl⟩ : syracuseStep 716489 = 537367) B537367
theorem B1601369 : Blo 315835 1601369 := bstep (se 2 (by rfl) ⟨600513, by rfl⟩ : syracuseStep 1601369 = 1201027) B1201027
theorem B356359 : Blo 315835 356359 := bstep (se 1 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 356359 = 534539) B534539
theorem B454663 : Blo 315835 454663 := bstep (se 1 (by rfl) ⟨340997, by rfl⟩ : syracuseStep 454663 = 681995) B681995
theorem B2027531 : Blo 315835 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B356539 : Blo 315835 356539 := bstep (se 1 (by rfl) ⟨267404, by rfl⟩ : syracuseStep 356539 = 534809) B534809
theorem B1208591 : Blo 315835 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B717191 : Blo 315835 717191 := bstep (se 1 (by rfl) ⟨537893, by rfl⟩ : syracuseStep 717191 = 1075787) B1075787
theorem B2421251 : Blo 315835 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B717371 : Blo 315835 717371 := bstep (se 1 (by rfl) ⟨538028, by rfl⟩ : syracuseStep 717371 = 1076057) B1076057
theorem B357007 : Blo 315835 357007 := bstep (se 1 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 357007 = 535511) B535511
theorem B717497 : Blo 315835 717497 := bstep (se 2 (by rfl) ⟨269061, by rfl⟩ : syracuseStep 717497 = 538123) B538123
theorem B1078163 : Blo 315835 1078163 := bstep (se 1 (by rfl) ⟨808622, by rfl⟩ : syracuseStep 1078163 = 1617245) B1617245
theorem B783361 : Blo 315835 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B717839 : Blo 315835 717839 := bstep (se 1 (by rfl) ⟨538379, by rfl⟩ : syracuseStep 717839 = 1076759) B1076759
theorem B717857 : Blo 315835 717857 := bstep (se 2 (by rfl) ⟨269196, by rfl⟩ : syracuseStep 717857 = 538393) B538393
theorem B357511 : Blo 315835 357511 := bstep (se 1 (by rfl) ⟨268133, by rfl⟩ : syracuseStep 357511 = 536267) B536267
theorem B357691 : Blo 315835 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B718199 : Blo 315835 718199 := bstep (se 1 (by rfl) ⟨538649, by rfl⟩ : syracuseStep 718199 = 1077299) B1077299
theorem B5436881 : Blo 315835 5436881 := bstep (se 2 (by rfl) ⟨2038830, by rfl⟩ : syracuseStep 5436881 = 4077661) B4077661
theorem B718379 : Blo 315835 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B358159 : Blo 315835 358159 := bstep (se 1 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 358159 = 537239) B537239
theorem B718625 : Blo 315835 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B1210247 : Blo 315835 1210247 := bstep (se 1 (by rfl) ⟨907685, by rfl⟩ : syracuseStep 1210247 = 1815371) B1815371
theorem B1800083 : Blo 315835 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B1603475 : Blo 315835 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B718739 : Blo 315835 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B718793 : Blo 315835 718793 := bstep (se 2 (by rfl) ⟨269547, by rfl⟩ : syracuseStep 718793 = 539095) B539095
theorem B13694993 : Blo 315835 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B358663 : Blo 315835 358663 := bstep (se 1 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 358663 = 537995) B537995
theorem B817523 : Blo 315835 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B358843 : Blo 315835 358843 := bstep (se 1 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 358843 = 538265) B538265
theorem B1800791 : Blo 315835 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B719495 : Blo 315835 719495 := bstep (se 1 (by rfl) ⟨539621, by rfl⟩ : syracuseStep 719495 = 1079243) B1079243
theorem B359311 : Blo 315835 359311 := bstep (se 1 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 359311 = 538967) B538967
theorem B359815 : Blo 315835 359815 := bstep (se 1 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 359815 = 539723) B539723
theorem B9305549 : Blo 315835 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B1212023 : Blo 315835 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B4062899 : Blo 315835 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B3440357 : Blo 315835 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B4096115 : Blo 315835 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B23298293 : Blo 315835 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2425139 : Blo 315835 2425139 := bstep (se 1 (by rfl) ⟨1818854, by rfl⟩ : syracuseStep 2425139 = 3637709) B3637709
theorem B1213177 : Blo 315835 1213177 := bstep (se 2 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 1213177 = 909883) B909883
theorem B427439 : Blo 315835 427439 := bstep (se 1 (by rfl) ⟨320579, by rfl⟩ : syracuseStep 427439 = 641159) B641159
theorem B1017289 : Blo 315835 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B1181147 : Blo 315835 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B1017775 : Blo 315835 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B9865223 : Blo 315835 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1607687 : Blo 315835 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B1083449 : Blo 315835 1083449 := bstep (se 2 (by rfl) ⟨406293, by rfl⟩ : syracuseStep 1083449 = 812587) B812587
theorem B1608173 : Blo 315835 1608173 := bstep (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) B603065
theorem B1608983 : Blo 315835 1608983 := bstep (se 1 (by rfl) ⟨1206737, by rfl⟩ : syracuseStep 1608983 = 2413475) B2413475
theorem B2297261 : Blo 315835 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B855539 : Blo 315835 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B1150523 : Blo 315835 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B9146033 : Blo 315835 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B2101277 : Blo 315835 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B1413665 : Blo 315835 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B856673 : Blo 315835 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B9966341 : Blo 315835 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B1610603 : Blo 315835 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B3249071 : Blo 315835 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B2954393 : Blo 315835 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1807555 : Blo 315835 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B1611251 : Blo 315835 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B1349243 : Blo 315835 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B1021967 : Blo 315835 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B14686595 : Blo 315835 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B3447191 : Blo 315835 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B2071021 : Blo 315835 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B1284817 : Blo 315835 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B1612547 : Blo 315835 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B2399867 : Blo 315835 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B859787 : Blo 315835 859787 := bstep (se 1 (by rfl) ⟨644840, by rfl⟩ : syracuseStep 859787 = 1289681) B1289681
theorem B761555 : Blo 315835 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B38969059 : Blo 315835 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B1351687 : Blo 315835 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B1614167 : Blo 315835 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B762785 : Blo 315835 762785 := bstep (se 2 (by rfl) ⟨286044, by rfl⟩ : syracuseStep 762785 = 572089) B572089
theorem B3875759 : Blo 315835 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B1811429 : Blo 315835 1811429 := bstep (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) B339643
theorem B1942501 : Blo 315835 1942501 := bstep (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) B364219
theorem B533513 : Blo 315835 533513 := bstep (se 2 (by rfl) ⟨200067, by rfl⟩ : syracuseStep 533513 = 400135) B400135
theorem B533675 : Blo 315835 533675 := bstep (se 1 (by rfl) ⟨400256, by rfl⟩ : syracuseStep 533675 = 800513) B800513
theorem B5481989 : Blo 315835 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B534073 : Blo 315835 534073 := bstep (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) B400555
theorem B534215 : Blo 315835 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B534377 : Blo 315835 534377 := bstep (se 2 (by rfl) ⟨200391, by rfl⟩ : syracuseStep 534377 = 400783) B400783
theorem B403375 : Blo 315835 403375 := bstep (se 1 (by rfl) ⟨302531, by rfl⟩ : syracuseStep 403375 = 605063) B605063
theorem B4073561 : Blo 315835 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B3418213 : Blo 315835 3418213 := bstep (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) B640915
theorem B534775 : Blo 315835 534775 := bstep (se 1 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 534775 = 802163) B802163
theorem B6203699 : Blo 315835 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B534971 : Blo 315835 534971 := bstep (se 1 (by rfl) ⟨401228, by rfl⟩ : syracuseStep 534971 = 802457) B802457
theorem B535079 : Blo 315835 535079 := bstep (se 1 (by rfl) ⟨401309, by rfl⟩ : syracuseStep 535079 = 802619) B802619
theorem B600787 : Blo 315835 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B535369 : Blo 315835 535369 := bstep (se 2 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 535369 = 401527) B401527
theorem B3910493 : Blo 315835 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B535403 : Blo 315835 535403 := bstep (se 1 (by rfl) ⟨401552, by rfl⟩ : syracuseStep 535403 = 803105) B803105
theorem B601015 : Blo 315835 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B404443 : Blo 315835 404443 := bstep (se 1 (by rfl) ⟨303332, by rfl⟩ : syracuseStep 404443 = 606665) B606665
theorem B2174147 : Blo 315835 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B2305219 : Blo 315835 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B535801 : Blo 315835 535801 := bstep (se 2 (by rfl) ⟨200925, by rfl⟩ : syracuseStep 535801 = 401851) B401851
theorem B601607 : Blo 315835 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B536071 : Blo 315835 536071 := bstep (se 1 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 536071 = 804107) B804107
theorem B1617731 : Blo 315835 1617731 := bstep (se 1 (by rfl) ⟨1213298, by rfl⟩ : syracuseStep 1617731 = 2426597) B2426597
theorem B536503 : Blo 315835 536503 := bstep (se 1 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 536503 = 804755) B804755
theorem B1519631 : Blo 315835 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B864275 : Blo 315835 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B536699 : Blo 315835 536699 := bstep (se 1 (by rfl) ⟨402524, by rfl⟩ : syracuseStep 536699 = 805049) B805049
theorem B2044061 : Blo 315835 2044061 := bstep (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) B766523
theorem B3649853 : Blo 315835 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1814845 : Blo 315835 1814845 := bstep (se 3 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 1814845 = 680567) B680567
theorem B602473 : Blo 315835 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B3912065 : Blo 315835 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B602633 : Blo 315835 602633 := bstep (se 2 (by rfl) ⟨225987, by rfl⟩ : syracuseStep 602633 = 451975) B451975
theorem B537097 : Blo 315835 537097 := bstep (se 2 (by rfl) ⟨201411, by rfl⟩ : syracuseStep 537097 = 402823) B402823
theorem B340519 : Blo 315835 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B537259 : Blo 315835 537259 := bstep (se 1 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 537259 = 805889) B805889
theorem B14398361 : Blo 315835 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B537563 : Blo 315835 537563 := bstep (se 1 (by rfl) ⟨403172, by rfl⟩ : syracuseStep 537563 = 806345) B806345
theorem B799915 : Blo 315835 799915 := bstep (se 1 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 799915 = 1199873) B1199873
theorem B570539 : Blo 315835 570539 := bstep (se 1 (by rfl) ⟨427904, by rfl⟩ : syracuseStep 570539 = 855809) B855809
theorem B4207787 : Blo 315835 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B537799 : Blo 315835 537799 := bstep (se 1 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 537799 = 806699) B806699
theorem B3650777 : Blo 315835 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B537961 : Blo 315835 537961 := bstep (se 2 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 537961 = 403471) B403471
theorem B800219 : Blo 315835 800219 := bstep (se 1 (by rfl) ⟨600164, by rfl⟩ : syracuseStep 800219 = 1200329) B1200329
theorem B1324583 : Blo 315835 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B604091 : Blo 315835 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B538555 : Blo 315835 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B3061709 : Blo 315835 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B538663 : Blo 315835 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B604523 : Blo 315835 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B538987 : Blo 315835 538987 := bstep (se 1 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 538987 = 808481) B808481
theorem B3684761 : Blo 315835 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B604577 : Blo 315835 604577 := bstep (se 2 (by rfl) ⟨226716, by rfl⟩ : syracuseStep 604577 = 453433) B453433
theorem B506287 : Blo 315835 506287 := bstep (se 1 (by rfl) ⟨379715, by rfl⟩ : syracuseStep 506287 = 759431) B759431
theorem B899723 : Blo 315835 899723 := bstep (se 1 (by rfl) ⟨674792, by rfl⟩ : syracuseStep 899723 = 1349585) B1349585
theorem B473849 : Blo 315835 473849 := bstep (se 2 (by rfl) ⟨177693, by rfl⟩ : syracuseStep 473849 = 355387) B355387
theorem B473951 : Blo 315835 473951 := bstep (se 1 (by rfl) ⟨355463, by rfl⟩ : syracuseStep 473951 = 710927) B710927
theorem B473963 : Blo 315835 473963 := bstep (se 1 (by rfl) ⟨355472, by rfl⟩ : syracuseStep 473963 = 710945) B710945
theorem B801697 : Blo 315835 801697 := bstep (se 2 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 801697 = 601273) B601273
theorem B1162171 : Blo 315835 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B2505779 : Blo 315835 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B474191 : Blo 315835 474191 := bstep (se 1 (by rfl) ⟨355643, by rfl⟩ : syracuseStep 474191 = 711287) B711287
theorem B474311 : Blo 315835 474311 := bstep (se 1 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 474311 = 711467) B711467
theorem B3882275 : Blo 315835 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B474473 : Blo 315835 474473 := bstep (se 2 (by rfl) ⟨177927, by rfl⟩ : syracuseStep 474473 = 355855) B355855
theorem B474551 : Blo 315835 474551 := bstep (se 1 (by rfl) ⟨355913, by rfl⟩ : syracuseStep 474551 = 711827) B711827
theorem B474587 : Blo 315835 474587 := bstep (se 1 (by rfl) ⟨355940, by rfl⟩ : syracuseStep 474587 = 711881) B711881
theorem B540521 : Blo 315835 540521 := bstep (se 2 (by rfl) ⟨202695, by rfl⟩ : syracuseStep 540521 = 405391) B405391
theorem B475055 : Blo 315835 475055 := bstep (se 1 (by rfl) ⟨356291, by rfl⟩ : syracuseStep 475055 = 712583) B712583
theorem B475145 : Blo 315835 475145 := bstep (se 2 (by rfl) ⟨178179, by rfl⟩ : syracuseStep 475145 = 356359) B356359
theorem B606217 : Blo 315835 606217 := bstep (se 2 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 606217 = 454663) B454663
theorem B475175 : Blo 315835 475175 := bstep (se 1 (by rfl) ⟨356381, by rfl⟩ : syracuseStep 475175 = 712763) B712763
theorem B3850355 : Blo 315835 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B475259 : Blo 315835 475259 := bstep (se 1 (by rfl) ⟨356444, by rfl⟩ : syracuseStep 475259 = 712889) B712889
theorem B475385 : Blo 315835 475385 := bstep (se 2 (by rfl) ⟨178269, by rfl⟩ : syracuseStep 475385 = 356539) B356539
theorem B11583755 : Blo 315835 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B475487 : Blo 315835 475487 := bstep (se 1 (by rfl) ⟨356615, by rfl⟩ : syracuseStep 475487 = 713231) B713231
theorem B475499 : Blo 315835 475499 := bstep (se 1 (by rfl) ⟨356624, by rfl⟩ : syracuseStep 475499 = 713249) B713249
theorem B475727 : Blo 315835 475727 := bstep (se 1 (by rfl) ⟨356795, by rfl⟩ : syracuseStep 475727 = 713591) B713591
theorem B475847 : Blo 315835 475847 := bstep (se 1 (by rfl) ⟨356885, by rfl⟩ : syracuseStep 475847 = 713771) B713771
theorem B476009 : Blo 315835 476009 := bstep (se 2 (by rfl) ⟨178503, by rfl⟩ : syracuseStep 476009 = 357007) B357007
theorem B607151 : Blo 315835 607151 := bstep (se 1 (by rfl) ⟨455363, by rfl⟩ : syracuseStep 607151 = 910727) B910727
theorem B476087 : Blo 315835 476087 := bstep (se 1 (by rfl) ⟨357065, by rfl⟩ : syracuseStep 476087 = 714131) B714131
theorem B476123 : Blo 315835 476123 := bstep (se 1 (by rfl) ⟨357092, by rfl⟩ : syracuseStep 476123 = 714185) B714185
theorem B541895 : Blo 315835 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B804239 : Blo 315835 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B476591 : Blo 315835 476591 := bstep (se 1 (by rfl) ⟨357443, by rfl⟩ : syracuseStep 476591 = 714887) B714887
theorem B476681 : Blo 315835 476681 := bstep (se 2 (by rfl) ⟨178755, by rfl⟩ : syracuseStep 476681 = 357511) B357511
theorem B476711 : Blo 315835 476711 := bstep (se 1 (by rfl) ⟨357533, by rfl⟩ : syracuseStep 476711 = 715067) B715067
theorem B476795 : Blo 315835 476795 := bstep (se 1 (by rfl) ⟨357596, by rfl⟩ : syracuseStep 476795 = 715193) B715193
theorem B968381 : Blo 315835 968381 := bstep (se 3 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 968381 = 363143) B363143
theorem B804563 : Blo 315835 804563 := bstep (se 1 (by rfl) ⟨603422, by rfl⟩ : syracuseStep 804563 = 1206845) B1206845
theorem B476921 : Blo 315835 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B477023 : Blo 315835 477023 := bstep (se 1 (by rfl) ⟨357767, by rfl⟩ : syracuseStep 477023 = 715535) B715535
theorem B477035 : Blo 315835 477035 := bstep (se 1 (by rfl) ⟨357776, by rfl⟩ : syracuseStep 477035 = 715553) B715553
theorem B903095 : Blo 315835 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B477263 : Blo 315835 477263 := bstep (se 1 (by rfl) ⟨357947, by rfl⟩ : syracuseStep 477263 = 715895) B715895
theorem B477383 : Blo 315835 477383 := bstep (se 1 (by rfl) ⟨358037, by rfl⟩ : syracuseStep 477383 = 716075) B716075
theorem B1067255 : Blo 315835 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B477545 : Blo 315835 477545 := bstep (se 2 (by rfl) ⟨179079, by rfl⟩ : syracuseStep 477545 = 358159) B358159
theorem B477623 : Blo 315835 477623 := bstep (se 1 (by rfl) ⟨358217, by rfl⟩ : syracuseStep 477623 = 716435) B716435
theorem B6834617 : Blo 315835 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B477659 : Blo 315835 477659 := bstep (se 1 (by rfl) ⟨358244, by rfl⟩ : syracuseStep 477659 = 716489) B716489
theorem B1067579 : Blo 315835 1067579 := bstep (se 1 (by rfl) ⟨800684, by rfl⟩ : syracuseStep 1067579 = 1601369) B1601369
theorem B903869 : Blo 315835 903869 := bstep (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) B338951
theorem B1067849 : Blo 315835 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B805727 : Blo 315835 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B904097 : Blo 315835 904097 := bstep (se 2 (by rfl) ⟨339036, by rfl⟩ : syracuseStep 904097 = 678073) B678073
theorem B478127 : Blo 315835 478127 := bstep (se 1 (by rfl) ⟨358595, by rfl⟩ : syracuseStep 478127 = 717191) B717191
theorem B478217 : Blo 315835 478217 := bstep (se 2 (by rfl) ⟨179331, by rfl⟩ : syracuseStep 478217 = 358663) B358663
theorem B478247 : Blo 315835 478247 := bstep (se 1 (by rfl) ⟨358685, by rfl⟩ : syracuseStep 478247 = 717371) B717371
theorem B478331 : Blo 315835 478331 := bstep (se 1 (by rfl) ⟨358748, by rfl⟩ : syracuseStep 478331 = 717497) B717497
theorem B904439 : Blo 315835 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B478457 : Blo 315835 478457 := bstep (se 2 (by rfl) ⟨179421, by rfl⟩ : syracuseStep 478457 = 358843) B358843
theorem B4345177 : Blo 315835 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B478559 : Blo 315835 478559 := bstep (se 1 (by rfl) ⟨358919, by rfl⟩ : syracuseStep 478559 = 717839) B717839
theorem B904553 : Blo 315835 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B478571 : Blo 315835 478571 := bstep (se 1 (by rfl) ⟨358928, by rfl⟩ : syracuseStep 478571 = 717857) B717857
theorem B511451 : Blo 315835 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B478799 : Blo 315835 478799 := bstep (se 1 (by rfl) ⟨359099, by rfl⟩ : syracuseStep 478799 = 718199) B718199
theorem B3624587 : Blo 315835 3624587 := bstep (se 1 (by rfl) ⟨2718440, by rfl⟩ : syracuseStep 3624587 = 5436881) B5436881
theorem B478919 : Blo 315835 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B479081 : Blo 315835 479081 := bstep (se 2 (by rfl) ⟨179655, by rfl⟩ : syracuseStep 479081 = 359311) B359311
theorem B479083 : Blo 315835 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B806831 : Blo 315835 806831 := bstep (se 1 (by rfl) ⟨605123, by rfl⟩ : syracuseStep 806831 = 1210247) B1210247
theorem B1200055 : Blo 315835 1200055 := bstep (se 1 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 1200055 = 1800083) B1800083
theorem B1068983 : Blo 315835 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B479159 : Blo 315835 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B479195 : Blo 315835 479195 := bstep (se 1 (by rfl) ⟨359396, by rfl⟩ : syracuseStep 479195 = 718793) B718793
theorem B511963 : Blo 315835 511963 := bstep (se 1 (by rfl) ⟨383972, by rfl⟩ : syracuseStep 511963 = 767945) B767945
theorem B512009 : Blo 315835 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B9129995 : Blo 315835 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B5820497 : Blo 315835 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B545015 : Blo 315835 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B1200527 : Blo 315835 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B479663 : Blo 315835 479663 := bstep (se 1 (by rfl) ⟨359747, by rfl⟩ : syracuseStep 479663 = 719495) B719495
theorem B315847 : Blo 315835 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B1036745 : Blo 315835 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B315867 : Blo 315835 315867 := bstep (se 1 (by rfl) ⟨236900, by rfl⟩ : syracuseStep 315867 = 473801) B473801
theorem B1069577 : Blo 315835 1069577 := bstep (se 2 (by rfl) ⟨401091, by rfl⟩ : syracuseStep 1069577 = 802183) B802183
theorem B905737 : Blo 315835 905737 := bstep (se 2 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 905737 = 679303) B679303
theorem B479753 : Blo 315835 479753 := bstep (se 2 (by rfl) ⟨179907, by rfl⟩ : syracuseStep 479753 = 359815) B359815
theorem B315943 : Blo 315835 315943 := bstep (se 1 (by rfl) ⟨236957, by rfl⟩ : syracuseStep 315943 = 473915) B473915
theorem B315983 : Blo 315835 315983 := bstep (se 1 (by rfl) ⟨236987, by rfl⟩ : syracuseStep 315983 = 473975) B473975
theorem B315999 : Blo 315835 315999 := bstep (se 1 (by rfl) ⟨236999, by rfl⟩ : syracuseStep 315999 = 473999) B473999
theorem B316027 : Blo 315835 316027 := bstep (se 1 (by rfl) ⟨237020, by rfl⟩ : syracuseStep 316027 = 474041) B474041
theorem B316079 : Blo 315835 316079 := bstep (se 1 (by rfl) ⟨237059, by rfl⟩ : syracuseStep 316079 = 474119) B474119
theorem B316103 : Blo 315835 316103 := bstep (se 1 (by rfl) ⟨237077, by rfl⟩ : syracuseStep 316103 = 474155) B474155
theorem B316123 : Blo 315835 316123 := bstep (se 1 (by rfl) ⟨237092, by rfl⟩ : syracuseStep 316123 = 474185) B474185
theorem B316199 : Blo 315835 316199 := bstep (se 1 (by rfl) ⟨237149, by rfl⟩ : syracuseStep 316199 = 474299) B474299
theorem B1364809 : Blo 315835 1364809 := bstep (se 2 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 1364809 = 1023607) B1023607
theorem B316239 : Blo 315835 316239 := bstep (se 1 (by rfl) ⟨237179, by rfl⟩ : syracuseStep 316239 = 474359) B474359
theorem B316255 : Blo 315835 316255 := bstep (se 1 (by rfl) ⟨237191, by rfl⟩ : syracuseStep 316255 = 474383) B474383
theorem B381791 : Blo 315835 381791 := bstep (se 1 (by rfl) ⟨286343, by rfl⟩ : syracuseStep 381791 = 572687) B572687
theorem B906079 : Blo 315835 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B316283 : Blo 315835 316283 := bstep (se 1 (by rfl) ⟨237212, by rfl⟩ : syracuseStep 316283 = 474425) B474425
theorem B316335 : Blo 315835 316335 := bstep (se 1 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 316335 = 474503) B474503
theorem B316359 : Blo 315835 316359 := bstep (se 1 (by rfl) ⟨237269, by rfl⟩ : syracuseStep 316359 = 474539) B474539
theorem B316379 : Blo 315835 316379 := bstep (se 1 (by rfl) ⟨237284, by rfl⟩ : syracuseStep 316379 = 474569) B474569
theorem B316455 : Blo 315835 316455 := bstep (se 1 (by rfl) ⟨237341, by rfl⟩ : syracuseStep 316455 = 474683) B474683
theorem B316495 : Blo 315835 316495 := bstep (se 1 (by rfl) ⟨237371, by rfl⟩ : syracuseStep 316495 = 474743) B474743
theorem B808015 : Blo 315835 808015 := bstep (se 1 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 808015 = 1212023) B1212023
theorem B316511 : Blo 315835 316511 := bstep (se 1 (by rfl) ⟨237383, by rfl⟩ : syracuseStep 316511 = 474767) B474767
theorem B2708599 : Blo 315835 2708599 := bstep (se 1 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 2708599 = 4062899) B4062899
theorem B316539 : Blo 315835 316539 := bstep (se 1 (by rfl) ⟨237404, by rfl⟩ : syracuseStep 316539 = 474809) B474809
theorem B316591 : Blo 315835 316591 := bstep (se 1 (by rfl) ⟨237443, by rfl⟩ : syracuseStep 316591 = 474887) B474887
theorem B316615 : Blo 315835 316615 := bstep (se 1 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 316615 = 474923) B474923
theorem B316635 : Blo 315835 316635 := bstep (se 1 (by rfl) ⟨237476, by rfl⟩ : syracuseStep 316635 = 474953) B474953
theorem B316711 : Blo 315835 316711 := bstep (se 1 (by rfl) ⟨237533, by rfl⟩ : syracuseStep 316711 = 475067) B475067
theorem B316751 : Blo 315835 316751 := bstep (se 1 (by rfl) ⟨237563, by rfl⟩ : syracuseStep 316751 = 475127) B475127
theorem B316767 : Blo 315835 316767 := bstep (se 1 (by rfl) ⟨237575, by rfl⟩ : syracuseStep 316767 = 475151) B475151
theorem B1201513 : Blo 315835 1201513 := bstep (se 2 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 1201513 = 901135) B901135
theorem B1070441 : Blo 315835 1070441 := bstep (se 2 (by rfl) ⟨401415, by rfl⟩ : syracuseStep 1070441 = 802831) B802831
theorem B316795 : Blo 315835 316795 := bstep (se 1 (by rfl) ⟨237596, by rfl⟩ : syracuseStep 316795 = 475193) B475193
theorem B316847 : Blo 315835 316847 := bstep (se 1 (by rfl) ⟨237635, by rfl⟩ : syracuseStep 316847 = 475271) B475271
theorem B316871 : Blo 315835 316871 := bstep (se 1 (by rfl) ⟨237653, by rfl⟩ : syracuseStep 316871 = 475307) B475307
theorem B316891 : Blo 315835 316891 := bstep (se 1 (by rfl) ⟨237668, by rfl⟩ : syracuseStep 316891 = 475337) B475337
theorem B316967 : Blo 315835 316967 := bstep (se 1 (by rfl) ⟨237725, by rfl⟩ : syracuseStep 316967 = 475451) B475451
theorem B317007 : Blo 315835 317007 := bstep (se 1 (by rfl) ⟨237755, by rfl⟩ : syracuseStep 317007 = 475511) B475511
theorem B546383 : Blo 315835 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B317023 : Blo 315835 317023 := bstep (se 1 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 317023 = 475535) B475535
theorem B12342881 : Blo 315835 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B1201787 : Blo 315835 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B317051 : Blo 315835 317051 := bstep (se 1 (by rfl) ⟨237788, by rfl⟩ : syracuseStep 317051 = 475577) B475577
theorem B317103 : Blo 315835 317103 := bstep (se 1 (by rfl) ⟨237827, by rfl⟩ : syracuseStep 317103 = 475655) B475655
theorem B317127 : Blo 315835 317127 := bstep (se 1 (by rfl) ⟨237845, by rfl⟩ : syracuseStep 317127 = 475691) B475691
theorem B906967 : Blo 315835 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B808663 : Blo 315835 808663 := bstep (se 1 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 808663 = 1212995) B1212995
theorem B317147 : Blo 315835 317147 := bstep (se 1 (by rfl) ⟨237860, by rfl⟩ : syracuseStep 317147 = 475721) B475721
theorem B6543139 : Blo 315835 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B317223 : Blo 315835 317223 := bstep (se 1 (by rfl) ⟨237917, by rfl⟩ : syracuseStep 317223 = 475835) B475835
theorem B2447147 : Blo 315835 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B317263 : Blo 315835 317263 := bstep (se 1 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 317263 = 475895) B475895
theorem B317279 : Blo 315835 317279 := bstep (se 1 (by rfl) ⟨237959, by rfl⟩ : syracuseStep 317279 = 475919) B475919
theorem B743275 : Blo 315835 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B317307 : Blo 315835 317307 := bstep (se 1 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 317307 = 475961) B475961
theorem B317359 : Blo 315835 317359 := bstep (se 1 (by rfl) ⟨238019, by rfl⟩ : syracuseStep 317359 = 476039) B476039
theorem B1071035 : Blo 315835 1071035 := bstep (se 1 (by rfl) ⟨803276, by rfl⟩ : syracuseStep 1071035 = 1606553) B1606553
theorem B907195 : Blo 315835 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B317383 : Blo 315835 317383 := bstep (se 1 (by rfl) ⟨238037, by rfl⟩ : syracuseStep 317383 = 476075) B476075
theorem B317403 : Blo 315835 317403 := bstep (se 1 (by rfl) ⟨238052, by rfl⟩ : syracuseStep 317403 = 476105) B476105
theorem B10344419 : Blo 315835 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B808967 : Blo 315835 808967 := bstep (se 1 (by rfl) ⟨606725, by rfl⟩ : syracuseStep 808967 = 1213451) B1213451
theorem B710675 : Blo 315835 710675 := bstep (se 1 (by rfl) ⟨533006, by rfl⟩ : syracuseStep 710675 = 1066013) B1066013
theorem B317479 : Blo 315835 317479 := bstep (se 1 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 317479 = 476219) B476219
theorem B907321 : Blo 315835 907321 := bstep (se 2 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 907321 = 680491) B680491
theorem B317519 : Blo 315835 317519 := bstep (se 1 (by rfl) ⟨238139, by rfl⟩ : syracuseStep 317519 = 476279) B476279
theorem B317535 : Blo 315835 317535 := bstep (se 1 (by rfl) ⟨238151, by rfl⟩ : syracuseStep 317535 = 476303) B476303
theorem B317563 : Blo 315835 317563 := bstep (se 1 (by rfl) ⟨238172, by rfl⟩ : syracuseStep 317563 = 476345) B476345
theorem B317615 : Blo 315835 317615 := bstep (se 1 (by rfl) ⟨238211, by rfl⟩ : syracuseStep 317615 = 476423) B476423
theorem B317639 : Blo 315835 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B317659 : Blo 315835 317659 := bstep (se 1 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 317659 = 476489) B476489
theorem B6314273 : Blo 315835 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B317735 : Blo 315835 317735 := bstep (se 1 (by rfl) ⟨238301, by rfl⟩ : syracuseStep 317735 = 476603) B476603
theorem B317775 : Blo 315835 317775 := bstep (se 1 (by rfl) ⟨238331, by rfl⟩ : syracuseStep 317775 = 476663) B476663
theorem B317791 : Blo 315835 317791 := bstep (se 1 (by rfl) ⟨238343, by rfl⟩ : syracuseStep 317791 = 476687) B476687
theorem B711017 : Blo 315835 711017 := bstep (se 2 (by rfl) ⟨266631, by rfl⟩ : syracuseStep 711017 = 533263) B533263
theorem B317819 : Blo 315835 317819 := bstep (se 1 (by rfl) ⟨238364, by rfl⟩ : syracuseStep 317819 = 476729) B476729
theorem B317871 : Blo 315835 317871 := bstep (se 1 (by rfl) ⟨238403, by rfl⟩ : syracuseStep 317871 = 476807) B476807
theorem B317895 : Blo 315835 317895 := bstep (se 1 (by rfl) ⟨238421, by rfl⟩ : syracuseStep 317895 = 476843) B476843
theorem B317915 : Blo 315835 317915 := bstep (se 1 (by rfl) ⟨238436, by rfl⟩ : syracuseStep 317915 = 476873) B476873
theorem B580135 : Blo 315835 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B317991 : Blo 315835 317991 := bstep (se 1 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 317991 = 476987) B476987
theorem B318031 : Blo 315835 318031 := bstep (se 1 (by rfl) ⟨238523, by rfl⟩ : syracuseStep 318031 = 477047) B477047
theorem B318047 : Blo 315835 318047 := bstep (se 1 (by rfl) ⟨238535, by rfl⟩ : syracuseStep 318047 = 477071) B477071
theorem B318075 : Blo 315835 318075 := bstep (se 1 (by rfl) ⟨238556, by rfl⟩ : syracuseStep 318075 = 477113) B477113
theorem B318127 : Blo 315835 318127 := bstep (se 1 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 318127 = 477191) B477191
theorem B318151 : Blo 315835 318151 := bstep (se 1 (by rfl) ⟨238613, by rfl⟩ : syracuseStep 318151 = 477227) B477227
theorem B318171 : Blo 315835 318171 := bstep (se 1 (by rfl) ⟨238628, by rfl⟩ : syracuseStep 318171 = 477257) B477257
theorem B318247 : Blo 315835 318247 := bstep (se 1 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 318247 = 477371) B477371
theorem B4414283 : Blo 315835 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B318287 : Blo 315835 318287 := bstep (se 1 (by rfl) ⟨238715, by rfl⟩ : syracuseStep 318287 = 477431) B477431
theorem B318303 : Blo 315835 318303 := bstep (se 1 (by rfl) ⟨238727, by rfl⟩ : syracuseStep 318303 = 477455) B477455
theorem B318331 : Blo 315835 318331 := bstep (se 1 (by rfl) ⟨238748, by rfl⟩ : syracuseStep 318331 = 477497) B477497
theorem B318383 : Blo 315835 318383 := bstep (se 1 (by rfl) ⟨238787, by rfl⟩ : syracuseStep 318383 = 477575) B477575
theorem B711611 : Blo 315835 711611 := bstep (se 1 (by rfl) ⟨533708, by rfl⟩ : syracuseStep 711611 = 1067417) B1067417
theorem B318407 : Blo 315835 318407 := bstep (se 1 (by rfl) ⟨238805, by rfl⟩ : syracuseStep 318407 = 477611) B477611
theorem B318427 : Blo 315835 318427 := bstep (se 1 (by rfl) ⟨238820, by rfl⟩ : syracuseStep 318427 = 477641) B477641
theorem B318503 : Blo 315835 318503 := bstep (se 1 (by rfl) ⟨238877, by rfl⟩ : syracuseStep 318503 = 477755) B477755
theorem B711737 : Blo 315835 711737 := bstep (se 2 (by rfl) ⟨266901, by rfl⟩ : syracuseStep 711737 = 533803) B533803
theorem B318543 : Blo 315835 318543 := bstep (se 1 (by rfl) ⟨238907, by rfl⟩ : syracuseStep 318543 = 477815) B477815
theorem B318559 : Blo 315835 318559 := bstep (se 1 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 318559 = 477839) B477839
theorem B318587 : Blo 315835 318587 := bstep (se 1 (by rfl) ⟨238940, by rfl⟩ : syracuseStep 318587 = 477881) B477881
theorem B318639 : Blo 315835 318639 := bstep (se 1 (by rfl) ⟨238979, by rfl⟩ : syracuseStep 318639 = 477959) B477959
theorem B318663 : Blo 315835 318663 := bstep (se 1 (by rfl) ⟨238997, by rfl⟩ : syracuseStep 318663 = 477995) B477995
theorem B318683 : Blo 315835 318683 := bstep (se 1 (by rfl) ⟨239012, by rfl⟩ : syracuseStep 318683 = 478025) B478025
theorem B318759 : Blo 315835 318759 := bstep (se 1 (by rfl) ⟨239069, by rfl⟩ : syracuseStep 318759 = 478139) B478139
theorem B318799 : Blo 315835 318799 := bstep (se 1 (by rfl) ⟨239099, by rfl⟩ : syracuseStep 318799 = 478199) B478199
theorem B318815 : Blo 315835 318815 := bstep (se 1 (by rfl) ⟨239111, by rfl⟩ : syracuseStep 318815 = 478223) B478223
theorem B318843 : Blo 315835 318843 := bstep (se 1 (by rfl) ⟨239132, by rfl⟩ : syracuseStep 318843 = 478265) B478265
theorem B712079 : Blo 315835 712079 := bstep (se 1 (by rfl) ⟨534059, by rfl⟩ : syracuseStep 712079 = 1068119) B1068119
theorem B318895 : Blo 315835 318895 := bstep (se 1 (by rfl) ⟨239171, by rfl⟩ : syracuseStep 318895 = 478343) B478343
theorem B318919 : Blo 315835 318919 := bstep (se 1 (by rfl) ⟨239189, by rfl⟩ : syracuseStep 318919 = 478379) B478379
theorem B318939 : Blo 315835 318939 := bstep (se 1 (by rfl) ⟨239204, by rfl⟩ : syracuseStep 318939 = 478409) B478409
theorem B319015 : Blo 315835 319015 := bstep (se 1 (by rfl) ⟨239261, by rfl⟩ : syracuseStep 319015 = 478523) B478523
theorem B319055 : Blo 315835 319055 := bstep (se 1 (by rfl) ⟨239291, by rfl⟩ : syracuseStep 319055 = 478583) B478583
theorem B319071 : Blo 315835 319071 := bstep (se 1 (by rfl) ⟨239303, by rfl⟩ : syracuseStep 319071 = 478607) B478607
theorem B1072763 : Blo 315835 1072763 := bstep (se 1 (by rfl) ⟨804572, by rfl⟩ : syracuseStep 1072763 = 1609145) B1609145
theorem B319099 : Blo 315835 319099 := bstep (se 1 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 319099 = 478649) B478649
theorem B3071627 : Blo 315835 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B319151 : Blo 315835 319151 := bstep (se 1 (by rfl) ⟨239363, by rfl⟩ : syracuseStep 319151 = 478727) B478727
theorem B319175 : Blo 315835 319175 := bstep (se 1 (by rfl) ⟨239381, by rfl⟩ : syracuseStep 319175 = 478763) B478763
theorem B712403 : Blo 315835 712403 := bstep (se 1 (by rfl) ⟨534302, by rfl⟩ : syracuseStep 712403 = 1068605) B1068605
theorem B319195 : Blo 315835 319195 := bstep (se 1 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 319195 = 478793) B478793
theorem B1072925 : Blo 315835 1072925 := bstep (se 3 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 1072925 = 402347) B402347
theorem B319271 : Blo 315835 319271 := bstep (se 1 (by rfl) ⟨239453, by rfl⟩ : syracuseStep 319271 = 478907) B478907
theorem B1236809 : Blo 315835 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B319311 : Blo 315835 319311 := bstep (se 1 (by rfl) ⟨239483, by rfl⟩ : syracuseStep 319311 = 478967) B478967
theorem B319327 : Blo 315835 319327 := bstep (se 1 (by rfl) ⟨239495, by rfl⟩ : syracuseStep 319327 = 478991) B478991
theorem B319355 : Blo 315835 319355 := bstep (se 1 (by rfl) ⟨239516, by rfl⟩ : syracuseStep 319355 = 479033) B479033
theorem B319407 : Blo 315835 319407 := bstep (se 1 (by rfl) ⟨239555, by rfl⟩ : syracuseStep 319407 = 479111) B479111
theorem B319431 : Blo 315835 319431 := bstep (se 1 (by rfl) ⟨239573, by rfl⟩ : syracuseStep 319431 = 479147) B479147
theorem B319451 : Blo 315835 319451 := bstep (se 1 (by rfl) ⟨239588, by rfl⟩ : syracuseStep 319451 = 479177) B479177
theorem B319527 : Blo 315835 319527 := bstep (se 1 (by rfl) ⟨239645, by rfl⟩ : syracuseStep 319527 = 479291) B479291
theorem B319567 : Blo 315835 319567 := bstep (se 1 (by rfl) ⟨239675, by rfl⟩ : syracuseStep 319567 = 479351) B479351
theorem B319583 : Blo 315835 319583 := bstep (se 1 (by rfl) ⟨239687, by rfl⟩ : syracuseStep 319583 = 479375) B479375
theorem B319611 : Blo 315835 319611 := bstep (se 1 (by rfl) ⟨239708, by rfl⟩ : syracuseStep 319611 = 479417) B479417
theorem B319663 : Blo 315835 319663 := bstep (se 1 (by rfl) ⟨239747, by rfl⟩ : syracuseStep 319663 = 479495) B479495
theorem B319687 : Blo 315835 319687 := bstep (se 1 (by rfl) ⟨239765, by rfl⟩ : syracuseStep 319687 = 479531) B479531
theorem B319707 : Blo 315835 319707 := bstep (se 1 (by rfl) ⟨239780, by rfl⟩ : syracuseStep 319707 = 479561) B479561
theorem B319783 : Blo 315835 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B319823 : Blo 315835 319823 := bstep (se 1 (by rfl) ⟨239867, by rfl⟩ : syracuseStep 319823 = 479735) B479735
theorem B1073627 : Blo 315835 1073627 := bstep (se 1 (by rfl) ⟨805220, by rfl⟩ : syracuseStep 1073627 = 1610441) B1610441
theorem B811529 : Blo 315835 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B647689 : Blo 315835 647689 := bstep (se 2 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 647689 = 485767) B485767
theorem B713339 : Blo 315835 713339 := bstep (se 1 (by rfl) ⟨535004, by rfl⟩ : syracuseStep 713339 = 1070009) B1070009
theorem B1106567 : Blo 315835 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B2417363 : Blo 315835 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B713465 : Blo 315835 713465 := bstep (se 2 (by rfl) ⟨267549, by rfl⟩ : syracuseStep 713465 = 535099) B535099
theorem B713735 : Blo 315835 713735 := bstep (se 1 (by rfl) ⟨535301, by rfl⟩ : syracuseStep 713735 = 1070603) B1070603
theorem B713807 : Blo 315835 713807 := bstep (se 1 (by rfl) ⟨535355, by rfl⟩ : syracuseStep 713807 = 1070711) B1070711
theorem B648271 : Blo 315835 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B3040409 : Blo 315835 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B1205401 : Blo 315835 1205401 := bstep (se 2 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 1205401 = 904051) B904051
theorem B1074329 : Blo 315835 1074329 := bstep (se 2 (by rfl) ⟨402873, by rfl⟩ : syracuseStep 1074329 = 805747) B805747
theorem B1205705 : Blo 315835 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B1598939 : Blo 315835 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B714203 : Blo 315835 714203 := bstep (se 1 (by rfl) ⟨535652, by rfl⟩ : syracuseStep 714203 = 1071305) B1071305
theorem B2287115 : Blo 315835 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B714671 : Blo 315835 714671 := bstep (se 1 (by rfl) ⟨536003, by rfl⟩ : syracuseStep 714671 = 1072007) B1072007
theorem B1206191 : Blo 315835 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1599425 : Blo 315835 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B3598343 : Blo 315835 3598343 := bstep (se 1 (by rfl) ⟨2698757, by rfl⟩ : syracuseStep 3598343 = 5397515) B5397515
theorem B714923 : Blo 315835 714923 := bstep (se 1 (by rfl) ⟨536192, by rfl⟩ : syracuseStep 714923 = 1072385) B1072385
theorem B1075517 : Blo 315835 1075517 := bstep (se 3 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 1075517 = 403319) B403319
theorem B3107159 : Blo 315835 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B1141307 : Blo 315835 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B715463 : Blo 315835 715463 := bstep (se 1 (by rfl) ⟨536597, by rfl⟩ : syracuseStep 715463 = 1073195) B1073195
theorem B486137 : Blo 315835 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B1076381 : Blo 315835 1076381 := bstep (se 3 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 1076381 = 403643) B403643
theorem B322939 : Blo 315835 322939 := bstep (se 1 (by rfl) ⟨242204, by rfl⟩ : syracuseStep 322939 = 484409) B484409
theorem B1207817 : Blo 315835 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B716327 : Blo 315835 716327 := bstep (se 1 (by rfl) ⟨537245, by rfl⟩ : syracuseStep 716327 = 1074491) B1074491
theorem B355963 : Blo 315835 355963 := bstep (se 1 (by rfl) ⟨266972, by rfl⟩ : syracuseStep 355963 = 533945) B533945
theorem B1076921 : Blo 315835 1076921 := bstep (se 2 (by rfl) ⟨403845, by rfl⟩ : syracuseStep 1076921 = 807691) B807691
theorem B4484845 : Blo 315835 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B716651 : Blo 315835 716651 := bstep (se 1 (by rfl) ⟨537488, by rfl⟩ : syracuseStep 716651 = 1074977) B1074977
theorem B716705 : Blo 315835 716705 := bstep (se 2 (by rfl) ⟨268764, by rfl⟩ : syracuseStep 716705 = 537529) B537529
theorem B6090659 : Blo 315835 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B683959 : Blo 315835 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1044481 : Blo 315835 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B2420765 : Blo 315835 2420765 := bstep (se 3 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 2420765 = 907787) B907787
theorem B356431 : Blo 315835 356431 := bstep (se 1 (by rfl) ⟨267323, by rfl⟩ : syracuseStep 356431 = 534647) B534647
theorem B1601693 : Blo 315835 1601693 := bstep (se 3 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 1601693 = 600635) B600635
theorem B1011959 : Blo 315835 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B717047 : Blo 315835 717047 := bstep (se 1 (by rfl) ⟨537785, by rfl⟩ : syracuseStep 717047 = 1075571) B1075571
theorem B1077515 : Blo 315835 1077515 := bstep (se 1 (by rfl) ⟨808136, by rfl⟩ : syracuseStep 1077515 = 1616273) B1616273
theorem B2289971 : Blo 315835 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B5534081 : Blo 315835 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B356827 : Blo 315835 356827 := bstep (se 1 (by rfl) ⟨267620, by rfl⟩ : syracuseStep 356827 = 535241) B535241
theorem B1077785 : Blo 315835 1077785 := bstep (se 2 (by rfl) ⟨404169, by rfl⟩ : syracuseStep 1077785 = 808339) B808339
theorem B717641 : Blo 315835 717641 := bstep (se 2 (by rfl) ⟨269115, by rfl⟩ : syracuseStep 717641 = 538231) B538231
theorem B3601259 : Blo 315835 3601259 := bstep (se 1 (by rfl) ⟨2700944, by rfl⟩ : syracuseStep 3601259 = 5401889) B5401889
theorem B357295 : Blo 315835 357295 := bstep (se 1 (by rfl) ⟨267971, by rfl⟩ : syracuseStep 357295 = 535943) B535943
theorem B1209275 : Blo 315835 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B357727 : Blo 315835 357727 := bstep (se 1 (by rfl) ⟨268295, by rfl⟩ : syracuseStep 357727 = 536591) B536591
theorem B816527 : Blo 315835 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B4879763 : Blo 315835 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B1602989 : Blo 315835 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B1144307 : Blo 315835 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B718433 : Blo 315835 718433 := bstep (se 2 (by rfl) ⟨269412, by rfl⟩ : syracuseStep 718433 = 538825) B538825
theorem B1078919 : Blo 315835 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B1078973 : Blo 315835 1078973 := bstep (se 3 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 1078973 = 404615) B404615
theorem B358087 : Blo 315835 358087 := bstep (se 1 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 358087 = 537131) B537131
theorem B1079135 : Blo 315835 1079135 := bstep (se 1 (by rfl) ⟨809351, by rfl⟩ : syracuseStep 1079135 = 1618703) B1618703
theorem B718775 : Blo 315835 718775 := bstep (se 1 (by rfl) ⟨539081, by rfl⟩ : syracuseStep 718775 = 1078163) B1078163
theorem B1079297 : Blo 315835 1079297 := bstep (se 2 (by rfl) ⟨404736, by rfl⟩ : syracuseStep 1079297 = 809473) B809473
theorem B2029657 : Blo 315835 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B5142629 : Blo 315835 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B719369 : Blo 315835 719369 := bstep (se 2 (by rfl) ⟨269763, by rfl⟩ : syracuseStep 719369 = 539527) B539527
theorem B358951 : Blo 315835 358951 := bstep (se 1 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 358951 = 538427) B538427
theorem B1014419 : Blo 315835 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B16546481 : Blo 315835 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B2161337 : Blo 315835 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1604609 : Blo 315835 1604609 := bstep (se 2 (by rfl) ⟨601728, by rfl⟩ : syracuseStep 1604609 = 1203457) B1203457
theorem B1145863 : Blo 315835 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B1211507 : Blo 315835 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B2587895 : Blo 315835 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B3440015 : Blo 315835 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1605419 : Blo 315835 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B2293571 : Blo 315835 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B1802249 : Blo 315835 1802249 := bstep (se 2 (by rfl) ⟨675843, by rfl⟩ : syracuseStep 1802249 = 1351687) B1351687
theorem B15532195 : Blo 315835 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B2590001 : Blo 315835 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B722299 : Blo 315835 722299 := bstep (se 1 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 722299 = 1083449) B1083449
theorem B1607201 : Blo 315835 1607201 := bstep (se 2 (by rfl) ⟨602700, by rfl⟩ : syracuseStep 1607201 = 1205401) B1205401
theorem B4556411 : Blo 315835 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B1018109 : Blo 315835 1018109 := bstep (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) B381791
theorem B6097355 : Blo 315835 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B4557617 : Blo 315835 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B691163 : Blo 315835 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B1445053 : Blo 315835 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B2166047 : Blo 315835 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B1969595 : Blo 315835 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B8228587 : Blo 315835 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B3149725 : Blo 315835 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B2298127 : Blo 315835 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B430585 : Blo 315835 430585 := bstep (se 2 (by rfl) ⟨161469, by rfl⟩ : syracuseStep 430585 = 322939) B322939
theorem B1611575 : Blo 315835 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B1612061 : Blo 315835 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B2398895 : Blo 315835 2398895 := bstep (se 1 (by rfl) ⟨1799171, by rfl⟩ : syracuseStep 2398895 = 3598343) B3598343
theorem B3611465 : Blo 315835 3611465 := bstep (se 2 (by rfl) ⟨1354299, by rfl⟩ : syracuseStep 3611465 = 2708599) B2708599
theorem B4135799 : Blo 315835 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B2071439 : Blo 315835 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B760871 : Blo 315835 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B1449431 : Blo 315835 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B8724185 : Blo 315835 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B991033 : Blo 315835 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B1613843 : Blo 315835 1613843 := bstep (se 1 (by rfl) ⟨1210382, by rfl⟩ : syracuseStep 1613843 = 2420765) B2420765
theorem B2433235 : Blo 315835 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B401755 : Blo 315835 401755 := bstep (se 1 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 401755 = 602633) B602633
theorem B2400839 : Blo 315835 2400839 := bstep (se 1 (by rfl) ⟨1800629, by rfl⟩ : syracuseStep 2400839 = 3601259) B3601259
theorem B2761361 : Blo 315835 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B2433851 : Blo 315835 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B3253175 : Blo 315835 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B1713089 : Blo 315835 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B533479 : Blo 315835 533479 := bstep (se 1 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 533479 = 800219) B800219
theorem B762871 : Blo 315835 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B1549561 : Blo 315835 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B402727 : Blo 315835 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B2041139 : Blo 315835 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B403051 : Blo 315835 403051 := bstep (se 1 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 403051 = 604577) B604577
theorem B599815 : Blo 315835 599815 := bstep (se 1 (by rfl) ⟨449861, by rfl⟩ : syracuseStep 599815 = 899723) B899723
theorem B2730469 : Blo 315835 2730469 := bstep (se 4 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 2730469 = 511963) B511963
theorem B2304733 : Blo 315835 2304733 := bstep (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) B864275
theorem B2566903 : Blo 315835 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B2730743 : Blo 315835 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B1616759 : Blo 315835 1616759 := bstep (se 1 (by rfl) ⟨1212569, by rfl⟩ : syracuseStep 1616759 = 2425139) B2425139
theorem B404767 : Blo 315835 404767 := bstep (se 1 (by rfl) ⟨303575, by rfl⟩ : syracuseStep 404767 = 607151) B607151
theorem B1453373 : Blo 315835 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B863585 : Blo 315835 863585 := bstep (se 2 (by rfl) ⟨323844, by rfl⟩ : syracuseStep 863585 = 647689) B647689
theorem B536159 : Blo 315835 536159 := bstep (se 1 (by rfl) ⟨402119, by rfl⟩ : syracuseStep 536159 = 804239) B804239
theorem B1617569 : Blo 315835 1617569 := bstep (se 2 (by rfl) ⟨606588, by rfl⟩ : syracuseStep 1617569 = 1213177) B1213177
theorem B536375 : Blo 315835 536375 := bstep (se 1 (by rfl) ⟨402281, by rfl⟩ : syracuseStep 536375 = 804563) B804563
theorem B602063 : Blo 315835 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B864361 : Blo 315835 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B602579 : Blo 315835 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B537151 : Blo 315835 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B1356385 : Blo 315835 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B602731 : Blo 315835 602731 := bstep (se 1 (by rfl) ⟨452048, by rfl⟩ : syracuseStep 602731 = 904097) B904097
theorem B602959 : Blo 315835 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B603035 : Blo 315835 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B340967 : Blo 315835 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B570359 : Blo 315835 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B767015 : Blo 315835 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B537833 : Blo 315835 537833 := bstep (se 2 (by rfl) ⟨201687, by rfl⟩ : syracuseStep 537833 = 403375) B403375
theorem B537887 : Blo 315835 537887 := bstep (se 1 (by rfl) ⟨403415, by rfl⟩ : syracuseStep 537887 = 806831) B806831
theorem B341339 : Blo 315835 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B3880331 : Blo 315835 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B800351 : Blo 315835 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B571115 : Blo 315835 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B801049 : Blo 315835 801049 := bstep (se 2 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 801049 = 600787) B600787
theorem B2177405 : Blo 315835 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B899495 : Blo 315835 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B801191 : Blo 315835 801191 := bstep (se 1 (by rfl) ⟨600893, by rfl⟩ : syracuseStep 801191 = 1201787) B1201787
theorem B801353 : Blo 315835 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B539257 : Blo 315835 539257 := bstep (se 2 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 539257 = 404443) B404443
theorem B6896279 : Blo 315835 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B539311 : Blo 315835 539311 := bstep (se 1 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 539311 = 808967) B808967
theorem B473783 : Blo 315835 473783 := bstep (se 1 (by rfl) ⟨355337, by rfl⟩ : syracuseStep 473783 = 710675) B710675
theorem B4209515 : Blo 315835 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1457021 : Blo 315835 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B474011 : Blo 315835 474011 := bstep (se 1 (by rfl) ⟨355508, by rfl⟩ : syracuseStep 474011 = 711017) B711017
theorem B474407 : Blo 315835 474407 := bstep (se 1 (by rfl) ⟨355805, by rfl⟩ : syracuseStep 474407 = 711611) B711611
theorem B474491 : Blo 315835 474491 := bstep (se 1 (by rfl) ⟨355868, by rfl⟩ : syracuseStep 474491 = 711737) B711737
theorem B474617 : Blo 315835 474617 := bstep (se 2 (by rfl) ⟨177981, by rfl⟩ : syracuseStep 474617 = 355963) B355963
theorem B474719 : Blo 315835 474719 := bstep (se 1 (by rfl) ⟨356039, by rfl⟩ : syracuseStep 474719 = 712079) B712079
theorem B5979793 : Blo 315835 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B573191 : Blo 315835 573191 := bstep (se 1 (by rfl) ⟨429893, by rfl⟩ : syracuseStep 573191 = 859787) B859787
theorem B2047751 : Blo 315835 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B474935 : Blo 315835 474935 := bstep (se 1 (by rfl) ⟨356201, by rfl⟩ : syracuseStep 474935 = 712403) B712403
theorem B507703 : Blo 315835 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B638777 : Blo 315835 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B1392641 : Blo 315835 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B475241 : Blo 315835 475241 := bstep (se 2 (by rfl) ⟨178215, by rfl⟩ : syracuseStep 475241 = 356431) B356431
theorem B541019 : Blo 315835 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B475559 : Blo 315835 475559 := bstep (se 1 (by rfl) ⟨356669, by rfl⟩ : syracuseStep 475559 = 713339) B713339
theorem B737711 : Blo 315835 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B803297 : Blo 315835 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B475643 : Blo 315835 475643 := bstep (se 1 (by rfl) ⟨356732, by rfl⟩ : syracuseStep 475643 = 713465) B713465
theorem B508523 : Blo 315835 508523 := bstep (se 1 (by rfl) ⟨381392, by rfl⟩ : syracuseStep 508523 = 762785) B762785
theorem B475769 : Blo 315835 475769 := bstep (se 2 (by rfl) ⟨178413, by rfl⟩ : syracuseStep 475769 = 356827) B356827
theorem B475823 : Blo 315835 475823 := bstep (se 1 (by rfl) ⟨356867, by rfl⟩ : syracuseStep 475823 = 713735) B713735
theorem B475871 : Blo 315835 475871 := bstep (se 1 (by rfl) ⟨356903, by rfl⟩ : syracuseStep 475871 = 713807) B713807
theorem B803803 : Blo 315835 803803 := bstep (se 1 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 803803 = 1205705) B1205705
theorem B1065959 : Blo 315835 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B476135 : Blo 315835 476135 := bstep (se 1 (by rfl) ⟨357101, by rfl⟩ : syracuseStep 476135 = 714203) B714203
theorem B3654659 : Blo 315835 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B1524743 : Blo 315835 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B1819745 : Blo 315835 1819745 := bstep (se 2 (by rfl) ⟨682404, by rfl⟩ : syracuseStep 1819745 = 1364809) B1364809
theorem B476393 : Blo 315835 476393 := bstep (se 2 (by rfl) ⟨178647, by rfl⟩ : syracuseStep 476393 = 357295) B357295
theorem B476447 : Blo 315835 476447 := bstep (se 1 (by rfl) ⟨357335, by rfl⟩ : syracuseStep 476447 = 714671) B714671
theorem B804127 : Blo 315835 804127 := bstep (se 1 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 804127 = 1206191) B1206191
theorem B1066283 : Blo 315835 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B476615 : Blo 315835 476615 := bstep (se 1 (by rfl) ⟨357461, by rfl⟩ : syracuseStep 476615 = 714923) B714923
theorem B1066553 : Blo 315835 1066553 := bstep (se 2 (by rfl) ⟨399957, by rfl⟩ : syracuseStep 1066553 = 799915) B799915
theorem B2410073 : Blo 315835 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B476969 : Blo 315835 476969 := bstep (se 2 (by rfl) ⟨178863, by rfl⟩ : syracuseStep 476969 = 357727) B357727
theorem B476975 : Blo 315835 476975 := bstep (se 1 (by rfl) ⟨357731, by rfl⟩ : syracuseStep 476975 = 715463) B715463
theorem B2606995 : Blo 315835 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B477449 : Blo 315835 477449 := bstep (se 2 (by rfl) ⟨179043, by rfl⟩ : syracuseStep 477449 = 358087) B358087
theorem B805211 : Blo 315835 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B477551 : Blo 315835 477551 := bstep (se 1 (by rfl) ⟨358163, by rfl⟩ : syracuseStep 477551 = 716327) B716327
theorem B477767 : Blo 315835 477767 := bstep (se 1 (by rfl) ⟨358325, by rfl⟩ : syracuseStep 477767 = 716651) B716651
theorem B477803 : Blo 315835 477803 := bstep (se 1 (by rfl) ⟨358352, by rfl⟩ : syracuseStep 477803 = 716705) B716705
theorem B1067795 : Blo 315835 1067795 := bstep (se 1 (by rfl) ⟨800846, by rfl⟩ : syracuseStep 1067795 = 1601693) B1601693
theorem B1362707 : Blo 315835 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B2706209 : Blo 315835 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B674639 : Blo 315835 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B478031 : Blo 315835 478031 := bstep (se 1 (by rfl) ⟨358523, by rfl⟩ : syracuseStep 478031 = 717047) B717047
theorem B1526647 : Blo 315835 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B2608043 : Blo 315835 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B3689387 : Blo 315835 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B478427 : Blo 315835 478427 := bstep (se 1 (by rfl) ⟨358820, by rfl⟩ : syracuseStep 478427 = 717641) B717641
theorem B675049 : Blo 315835 675049 := bstep (se 2 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 675049 = 506287) B506287
theorem B806183 : Blo 315835 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B773513 : Blo 315835 773513 := bstep (se 2 (by rfl) ⟨290067, by rfl⟩ : syracuseStep 773513 = 580135) B580135
theorem B478601 : Blo 315835 478601 := bstep (se 2 (by rfl) ⟨179475, by rfl⟩ : syracuseStep 478601 = 358951) B358951
theorem B380359 : Blo 315835 380359 := bstep (se 1 (by rfl) ⟨285269, by rfl⟩ : syracuseStep 380359 = 570539) B570539
theorem B2805191 : Blo 315835 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B1068659 : Blo 315835 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B478955 : Blo 315835 478955 := bstep (se 1 (by rfl) ⟨359216, by rfl⟩ : syracuseStep 478955 = 718433) B718433
theorem B1068929 : Blo 315835 1068929 := bstep (se 2 (by rfl) ⟨400848, by rfl⟩ : syracuseStep 1068929 = 801697) B801697
theorem B479183 : Blo 315835 479183 := bstep (se 1 (by rfl) ⟨359387, by rfl⟩ : syracuseStep 479183 = 718775) B718775
theorem B1527817 : Blo 315835 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B3428419 : Blo 315835 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B479579 : Blo 315835 479579 := bstep (se 1 (by rfl) ⟨359684, by rfl⟩ : syracuseStep 479579 = 719369) B719369
theorem B676279 : Blo 315835 676279 := bstep (se 1 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 676279 = 1014419) B1014419
theorem B11030987 : Blo 315835 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B315899 : Blo 315835 315899 := bstep (se 1 (by rfl) ⟨236924, by rfl⟩ : syracuseStep 315899 = 473849) B473849
theorem B315967 : Blo 315835 315967 := bstep (se 1 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 315967 = 473951) B473951
theorem B315975 : Blo 315835 315975 := bstep (se 1 (by rfl) ⟨236981, by rfl⟩ : syracuseStep 315975 = 473963) B473963
theorem B1069739 : Blo 315835 1069739 := bstep (se 1 (by rfl) ⟨802304, by rfl⟩ : syracuseStep 1069739 = 1604609) B1604609
theorem B316127 : Blo 315835 316127 := bstep (se 1 (by rfl) ⟨237095, by rfl⟩ : syracuseStep 316127 = 474191) B474191
theorem B807671 : Blo 315835 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B316207 : Blo 315835 316207 := bstep (se 1 (by rfl) ⟨237155, by rfl⟩ : syracuseStep 316207 = 474311) B474311
theorem B1725263 : Blo 315835 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B3298157 : Blo 315835 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B316315 : Blo 315835 316315 := bstep (se 1 (by rfl) ⟨237236, by rfl⟩ : syracuseStep 316315 = 474473) B474473
theorem B5428133 : Blo 315835 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B316367 : Blo 315835 316367 := bstep (se 1 (by rfl) ⟨237275, by rfl⟩ : syracuseStep 316367 = 474551) B474551
theorem B51958745 : Blo 315835 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B316391 : Blo 315835 316391 := bstep (se 1 (by rfl) ⟨237293, by rfl⟩ : syracuseStep 316391 = 474587) B474587
theorem B1070279 : Blo 315835 1070279 := bstep (se 1 (by rfl) ⟨802709, by rfl⟩ : syracuseStep 1070279 = 1605419) B1605419
theorem B1529047 : Blo 315835 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B316703 : Blo 315835 316703 := bstep (se 1 (by rfl) ⟨237527, by rfl⟩ : syracuseStep 316703 = 475055) B475055
theorem B316763 : Blo 315835 316763 := bstep (se 1 (by rfl) ⟨237572, by rfl⟩ : syracuseStep 316763 = 475145) B475145
theorem B808289 : Blo 315835 808289 := bstep (se 2 (by rfl) ⟨303108, by rfl⟩ : syracuseStep 808289 = 606217) B606217
theorem B316783 : Blo 315835 316783 := bstep (se 1 (by rfl) ⟨237587, by rfl⟩ : syracuseStep 316783 = 475175) B475175
theorem B316839 : Blo 315835 316839 := bstep (se 1 (by rfl) ⟨237629, by rfl⟩ : syracuseStep 316839 = 475259) B475259
theorem B316923 : Blo 315835 316923 := bstep (se 1 (by rfl) ⟨237692, by rfl⟩ : syracuseStep 316923 = 475385) B475385
theorem B7722503 : Blo 315835 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B316991 : Blo 315835 316991 := bstep (se 1 (by rfl) ⟨237743, by rfl⟩ : syracuseStep 316991 = 475487) B475487
theorem B316999 : Blo 315835 316999 := bstep (se 1 (by rfl) ⟨237749, by rfl⟩ : syracuseStep 316999 = 475499) B475499
theorem B317151 : Blo 315835 317151 := bstep (se 1 (by rfl) ⟨237863, by rfl⟩ : syracuseStep 317151 = 475727) B475727
theorem B317231 : Blo 315835 317231 := bstep (se 1 (by rfl) ⟨237923, by rfl⟩ : syracuseStep 317231 = 475847) B475847
theorem B317339 : Blo 315835 317339 := bstep (se 1 (by rfl) ⟨238004, by rfl⟩ : syracuseStep 317339 = 476009) B476009
theorem B317391 : Blo 315835 317391 := bstep (se 1 (by rfl) ⟨238043, by rfl⟩ : syracuseStep 317391 = 476087) B476087
theorem B317415 : Blo 315835 317415 := bstep (se 1 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 317415 = 476123) B476123
theorem B317727 : Blo 315835 317727 := bstep (se 1 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 317727 = 476591) B476591
theorem B317787 : Blo 315835 317787 := bstep (se 1 (by rfl) ⟨238340, by rfl⟩ : syracuseStep 317787 = 476681) B476681
theorem B317807 : Blo 315835 317807 := bstep (se 1 (by rfl) ⟨238355, by rfl⟩ : syracuseStep 317807 = 476711) B476711
theorem B317863 : Blo 315835 317863 := bstep (se 1 (by rfl) ⟨238397, by rfl⟩ : syracuseStep 317863 = 476795) B476795
theorem B645587 : Blo 315835 645587 := bstep (se 1 (by rfl) ⟨484190, by rfl⟩ : syracuseStep 645587 = 968381) B968381
theorem B317947 : Blo 315835 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B318015 : Blo 315835 318015 := bstep (se 1 (by rfl) ⟨238511, by rfl⟩ : syracuseStep 318015 = 477023) B477023
theorem B318023 : Blo 315835 318023 := bstep (se 1 (by rfl) ⟨238517, by rfl⟩ : syracuseStep 318023 = 477035) B477035
theorem B6576815 : Blo 315835 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B1071791 : Blo 315835 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B318175 : Blo 315835 318175 := bstep (se 1 (by rfl) ⟨238631, by rfl⟩ : syracuseStep 318175 = 477263) B477263
theorem B318255 : Blo 315835 318255 := bstep (se 1 (by rfl) ⟨238691, by rfl⟩ : syracuseStep 318255 = 477383) B477383
theorem B711503 : Blo 315835 711503 := bstep (se 1 (by rfl) ⟨533627, by rfl⟩ : syracuseStep 711503 = 1067255) B1067255
theorem B318363 : Blo 315835 318363 := bstep (se 1 (by rfl) ⟨238772, by rfl⟩ : syracuseStep 318363 = 477545) B477545
theorem B318415 : Blo 315835 318415 := bstep (se 1 (by rfl) ⟨238811, by rfl⟩ : syracuseStep 318415 = 477623) B477623
theorem B318439 : Blo 315835 318439 := bstep (se 1 (by rfl) ⟨238829, by rfl⟩ : syracuseStep 318439 = 477659) B477659
theorem B1072115 : Blo 315835 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B711719 : Blo 315835 711719 := bstep (se 1 (by rfl) ⟨533789, by rfl⟩ : syracuseStep 711719 = 1067579) B1067579
theorem B711899 : Blo 315835 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B318751 : Blo 315835 318751 := bstep (se 1 (by rfl) ⟨239063, by rfl⟩ : syracuseStep 318751 = 478127) B478127
theorem B318811 : Blo 315835 318811 := bstep (se 1 (by rfl) ⟨239108, by rfl⟩ : syracuseStep 318811 = 478217) B478217
theorem B318831 : Blo 315835 318831 := bstep (se 1 (by rfl) ⟨239123, by rfl⟩ : syracuseStep 318831 = 478247) B478247
theorem B712097 : Blo 315835 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B318887 : Blo 315835 318887 := bstep (se 1 (by rfl) ⟨239165, by rfl⟩ : syracuseStep 318887 = 478331) B478331
theorem B318971 : Blo 315835 318971 := bstep (se 1 (by rfl) ⟨239228, by rfl⟩ : syracuseStep 318971 = 478457) B478457
theorem B1072655 : Blo 315835 1072655 := bstep (se 1 (by rfl) ⟨804491, by rfl⟩ : syracuseStep 1072655 = 1608983) B1608983
theorem B319039 : Blo 315835 319039 := bstep (se 1 (by rfl) ⟨239279, by rfl⟩ : syracuseStep 319039 = 478559) B478559
theorem B319047 : Blo 315835 319047 := bstep (se 1 (by rfl) ⟨239285, by rfl⟩ : syracuseStep 319047 = 478571) B478571
theorem B319199 : Blo 315835 319199 := bstep (se 1 (by rfl) ⟨239399, by rfl⟩ : syracuseStep 319199 = 478799) B478799
theorem B2416391 : Blo 315835 2416391 := bstep (se 1 (by rfl) ⟨1812293, by rfl⟩ : syracuseStep 2416391 = 3624587) B3624587
theorem B319279 : Blo 315835 319279 := bstep (se 1 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 319279 = 478919) B478919
theorem B319387 : Blo 315835 319387 := bstep (se 1 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 319387 = 479081) B479081
theorem B712655 : Blo 315835 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B319439 : Blo 315835 319439 := bstep (se 1 (by rfl) ⟨239579, by rfl⟩ : syracuseStep 319439 = 479159) B479159
theorem B319463 : Blo 315835 319463 := bstep (se 1 (by rfl) ⟨239597, by rfl⟩ : syracuseStep 319463 = 479195) B479195
theorem B6086663 : Blo 315835 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1400851 : Blo 315835 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B319775 : Blo 315835 319775 := bstep (se 1 (by rfl) ⟨239831, by rfl⟩ : syracuseStep 319775 = 479663) B479663
theorem B713033 : Blo 315835 713033 := bstep (se 2 (by rfl) ⟨267387, by rfl⟩ : syracuseStep 713033 = 534775) B534775
theorem B713051 : Blo 315835 713051 := bstep (se 1 (by rfl) ⟨534788, by rfl⟩ : syracuseStep 713051 = 1069577) B1069577
theorem B319835 : Blo 315835 319835 := bstep (se 1 (by rfl) ⟨239876, by rfl⟩ : syracuseStep 319835 = 479753) B479753
theorem B942443 : Blo 315835 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B6644227 : Blo 315835 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1073735 : Blo 315835 1073735 := bstep (se 1 (by rfl) ⟨805301, by rfl⟩ : syracuseStep 1073735 = 1610603) B1610603
theorem B713627 : Blo 315835 713627 := bstep (se 1 (by rfl) ⟨535220, by rfl⟩ : syracuseStep 713627 = 1070441) B1070441
theorem B1074167 : Blo 315835 1074167 := bstep (se 1 (by rfl) ⟨805625, by rfl⟩ : syracuseStep 1074167 = 1611251) B1611251
theorem B713825 : Blo 315835 713825 := bstep (se 2 (by rfl) ⟨267684, by rfl⟩ : syracuseStep 713825 = 535369) B535369
theorem B1139837 : Blo 315835 1139837 := bstep (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) B427439
theorem B1631431 : Blo 315835 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B714023 : Blo 315835 714023 := bstep (se 1 (by rfl) ⟨535517, by rfl⟩ : syracuseStep 714023 = 1071035) B1071035
theorem B681311 : Blo 315835 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B9791063 : Blo 315835 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B3073625 : Blo 315835 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B714401 : Blo 315835 714401 := bstep (se 2 (by rfl) ⟨267900, by rfl⟩ : syracuseStep 714401 = 535801) B535801
theorem B5793569 : Blo 315835 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B1075031 : Blo 315835 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B2942855 : Blo 315835 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B714761 : Blo 315835 714761 := bstep (se 2 (by rfl) ⟨268035, by rfl⟩ : syracuseStep 714761 = 536071) B536071
theorem B1599911 : Blo 315835 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B715175 : Blo 315835 715175 := bstep (se 1 (by rfl) ⟨536381, by rfl⟩ : syracuseStep 715175 = 1072763) B1072763
theorem B715283 : Blo 315835 715283 := bstep (se 1 (by rfl) ⟨536462, by rfl⟩ : syracuseStep 715283 = 1072925) B1072925
theorem B911945 : Blo 315835 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1600073 : Blo 315835 1600073 := bstep (se 2 (by rfl) ⟨600027, by rfl⟩ : syracuseStep 1600073 = 1200055) B1200055
theorem B715337 : Blo 315835 715337 := bstep (se 2 (by rfl) ⟨268251, by rfl⟩ : syracuseStep 715337 = 536503) B536503
theorem B1076111 : Blo 315835 1076111 := bstep (se 1 (by rfl) ⟨807083, by rfl⟩ : syracuseStep 1076111 = 1614167) B1614167
theorem B715751 : Blo 315835 715751 := bstep (se 1 (by rfl) ⟨536813, by rfl⟩ : syracuseStep 715751 = 1073627) B1073627
theorem B2419793 : Blo 315835 2419793 := bstep (se 2 (by rfl) ⟨907422, by rfl⟩ : syracuseStep 2419793 = 1814845) B1814845
theorem B2583839 : Blo 315835 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B1207619 : Blo 315835 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B355675 : Blo 315835 355675 := bstep (se 1 (by rfl) ⟨266756, by rfl⟩ : syracuseStep 355675 = 533513) B533513
theorem B1207649 : Blo 315835 1207649 := bstep (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) B905737
theorem B716129 : Blo 315835 716129 := bstep (se 2 (by rfl) ⟨268548, by rfl⟩ : syracuseStep 716129 = 537097) B537097
theorem B454025 : Blo 315835 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B2026939 : Blo 315835 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B716219 : Blo 315835 716219 := bstep (se 1 (by rfl) ⟨537164, by rfl⟩ : syracuseStep 716219 = 1074329) B1074329
theorem B355783 : Blo 315835 355783 := bstep (se 1 (by rfl) ⟨266837, by rfl⟩ : syracuseStep 355783 = 533675) B533675
theorem B716345 : Blo 315835 716345 := bstep (se 2 (by rfl) ⟨268629, by rfl⟩ : syracuseStep 716345 = 537259) B537259
theorem B1208105 : Blo 315835 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B356143 : Blo 315835 356143 := bstep (se 1 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 356143 = 534215) B534215
theorem B356251 : Blo 315835 356251 := bstep (se 1 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 356251 = 534377) B534377
theorem B2715707 : Blo 315835 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1077353 : Blo 315835 1077353 := bstep (se 2 (by rfl) ⟨404007, by rfl⟩ : syracuseStep 1077353 = 808015) B808015
theorem B717011 : Blo 315835 717011 := bstep (se 1 (by rfl) ⟨537758, by rfl⟩ : syracuseStep 717011 = 1075517) B1075517
theorem B717065 : Blo 315835 717065 := bstep (se 2 (by rfl) ⟨268899, by rfl⟩ : syracuseStep 717065 = 537799) B537799
theorem B356647 : Blo 315835 356647 := bstep (se 1 (by rfl) ⟨267485, by rfl⟩ : syracuseStep 356647 = 534971) B534971
theorem B356719 : Blo 315835 356719 := bstep (se 1 (by rfl) ⟨267539, by rfl⟩ : syracuseStep 356719 = 535079) B535079
theorem B1602017 : Blo 315835 1602017 := bstep (se 2 (by rfl) ⟨600756, by rfl⟩ : syracuseStep 1602017 = 1201513) B1201513
theorem B717281 : Blo 315835 717281 := bstep (se 2 (by rfl) ⟨268980, by rfl⟩ : syracuseStep 717281 = 537961) B537961
theorem B5763565 : Blo 315835 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B324091 : Blo 315835 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B356935 : Blo 315835 356935 := bstep (se 1 (by rfl) ⟨267701, by rfl⟩ : syracuseStep 356935 = 535403) B535403
theorem B717587 : Blo 315835 717587 := bstep (se 1 (by rfl) ⟨538190, by rfl⟩ : syracuseStep 717587 = 1076381) B1076381
theorem B1209289 : Blo 315835 1209289 := bstep (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) B906967
theorem B1078217 : Blo 315835 1078217 := bstep (se 2 (by rfl) ⟨404331, by rfl⟩ : syracuseStep 1078217 = 808663) B808663
theorem B717947 : Blo 315835 717947 := bstep (se 1 (by rfl) ⟨538460, by rfl⟩ : syracuseStep 717947 = 1076921) B1076921
theorem B1078487 : Blo 315835 1078487 := bstep (se 1 (by rfl) ⟨808865, by rfl⟩ : syracuseStep 1078487 = 1617731) B1617731
theorem B1209593 : Blo 315835 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B718073 : Blo 315835 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B4060439 : Blo 315835 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B1013087 : Blo 315835 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B718217 : Blo 315835 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B1209761 : Blo 315835 1209761 := bstep (se 2 (by rfl) ⟨453660, by rfl⟩ : syracuseStep 1209761 = 907321) B907321
theorem B357799 : Blo 315835 357799 := bstep (se 1 (by rfl) ⟨268349, by rfl⟩ : syracuseStep 357799 = 536699) B536699
theorem B718343 : Blo 315835 718343 := bstep (se 1 (by rfl) ⟨538757, by rfl⟩ : syracuseStep 718343 = 1077515) B1077515
theorem B718523 : Blo 315835 718523 := bstep (se 1 (by rfl) ⟨538892, by rfl⟩ : syracuseStep 718523 = 1077785) B1077785
theorem B718649 : Blo 315835 718649 := bstep (se 2 (by rfl) ⟨269493, by rfl⟩ : syracuseStep 718649 = 538987) B538987
theorem B9598907 : Blo 315835 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B358375 : Blo 315835 358375 := bstep (se 1 (by rfl) ⟨268781, by rfl⟩ : syracuseStep 358375 = 537563) B537563
theorem B883055 : Blo 315835 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B719279 : Blo 315835 719279 := bstep (se 1 (by rfl) ⟨539459, by rfl⟩ : syracuseStep 719279 = 1078919) B1078919
theorem B6126029 : Blo 315835 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B719315 : Blo 315835 719315 := bstep (se 1 (by rfl) ⟨539486, by rfl⟩ : syracuseStep 719315 = 1078973) B1078973
theorem B719423 : Blo 315835 719423 := bstep (se 1 (by rfl) ⟨539567, by rfl⟩ : syracuseStep 719423 = 1079135) B1079135
theorem B719531 : Blo 315835 719531 := bstep (se 1 (by rfl) ⟨539648, by rfl⟩ : syracuseStep 719531 = 1079297) B1079297
theorem B1604285 : Blo 315835 1604285 := bstep (se 3 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 1604285 = 601607) B601607
theorem B2456507 : Blo 315835 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1670519 : Blo 315835 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B2588183 : Blo 315835 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B2293343 : Blo 315835 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B360347 : Blo 315835 360347 := bstep (se 1 (by rfl) ⟨270260, by rfl⟩ : syracuseStep 360347 = 540521) B540521
theorem B1867801 : Blo 315835 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B20709593 : Blo 315835 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B3244313 : Blo 315835 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B491807 : Blo 315835 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B1016495 : Blo 315835 1016495 := bstep (se 1 (by rfl) ⟨762371, by rfl⟩ : syracuseStep 1016495 = 1524743) B1524743
theorem B1213163 : Blo 315835 1213163 := bstep (se 1 (by rfl) ⟨909872, by rfl⟩ : syracuseStep 1213163 = 1819745) B1819745
theorem B1442717 : Blo 315835 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B1606715 : Blo 315835 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B1606877 : Blo 315835 1606877 := bstep (se 3 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 1606877 = 602579) B602579
theorem B1017161 : Blo 315835 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B4064903 : Blo 315835 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B2066081 : Blo 315835 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1804139 : Blo 315835 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B2459591 : Blo 315835 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B460775 : Blo 315835 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B1444031 : Blo 315835 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B1313063 : Blo 315835 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B1870127 : Blo 315835 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B3475993 : Blo 315835 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2296453 : Blo 315835 2296453 := bstep (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) B430585
theorem B1150175 : Blo 315835 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B2198771 : Blo 315835 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B3640625 : Blo 315835 3640625 := bstep (se 2 (by rfl) ⟨1365234, by rfl⟩ : syracuseStep 3640625 = 2730469) B2730469
theorem B34639163 : Blo 315835 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B5148335 : Blo 315835 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B2035529 : Blo 315835 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B430391 : Blo 315835 430391 := bstep (se 1 (by rfl) ⟨322793, by rfl⟩ : syracuseStep 430391 = 645587) B645587
theorem B2757199 : Blo 315835 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B1380959 : Blo 315835 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B1610927 : Blo 315835 1610927 := bstep (se 1 (by rfl) ⟨1208195, by rfl⟩ : syracuseStep 1610927 = 2416391) B2416391
theorem B4199633 : Blo 315835 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B2037089 : Blo 315835 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B1152481 : Blo 315835 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B628295 : Blo 315835 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B1840907 : Blo 315835 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B2168783 : Blo 315835 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B432121 : Blo 315835 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B1808513 : Blo 315835 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B6527375 : Blo 315835 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B21142037 : Blo 315835 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B1612385 : Blo 315835 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B2431853 : Blo 315835 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2038729 : Blo 315835 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B1613195 : Blo 315835 1613195 := bstep (se 1 (by rfl) ⟨1209896, by rfl⟩ : syracuseStep 1613195 = 2419793) B2419793
theorem B6954781 : Blo 315835 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B401375 : Blo 315835 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B1810471 : Blo 315835 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B402023 : Blo 315835 402023 := bstep (se 1 (by rfl) ⟨301517, by rfl⟩ : syracuseStep 402023 = 603035) B603035
theorem B533567 : Blo 315835 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B6399271 : Blo 315835 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B1451603 : Blo 315835 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B599663 : Blo 315835 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B534127 : Blo 315835 534127 := bstep (se 1 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 534127 = 801191) B801191
theorem B534235 : Blo 315835 534235 := bstep (se 1 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 534235 = 801353) B801353
theorem B4597519 : Blo 315835 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B7973057 : Blo 315835 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B960925 : Blo 315835 960925 := bstep (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) B360347
theorem B928427 : Blo 315835 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B535531 : Blo 315835 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B535673 : Blo 315835 535673 := bstep (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) B401755
theorem B2436439 : Blo 315835 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B8858969 : Blo 315835 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B536807 : Blo 315835 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B1356061 : Blo 315835 1356061 := bstep (se 3 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 1356061 = 508523) B508523
theorem B536969 : Blo 315835 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B963065 : Blo 315835 963065 := bstep (se 2 (by rfl) ⟨361149, by rfl⟩ : syracuseStep 963065 = 722299) B722299
theorem B537401 : Blo 315835 537401 := bstep (se 2 (by rfl) ⟨201525, by rfl⟩ : syracuseStep 537401 = 403051) B403051
theorem B537455 : Blo 315835 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B799753 : Blo 315835 799753 := bstep (se 2 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 799753 = 599815) B599815
theorem B1520957 : Blo 315835 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B7353991 : Blo 315835 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B538447 : Blo 315835 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B3618755 : Blo 315835 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B538859 : Blo 315835 538859 := bstep (se 1 (by rfl) ⟨404144, by rfl⟩ : syracuseStep 538859 = 808289) B808289
theorem B1816829 : Blo 315835 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B3422537 : Blo 315835 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B900065 : Blo 315835 900065 := bstep (se 2 (by rfl) ⟨337524, by rfl⟩ : syracuseStep 900065 = 675049) B675049
theorem B539689 : Blo 315835 539689 := bstep (se 2 (by rfl) ⟨202383, by rfl⟩ : syracuseStep 539689 = 404767) B404767
theorem B474233 : Blo 315835 474233 := bstep (se 2 (by rfl) ⟨177837, by rfl⟩ : syracuseStep 474233 = 355675) B355675
theorem B2407643 : Blo 315835 2407643 := bstep (se 1 (by rfl) ⟨1805732, by rfl⟩ : syracuseStep 2407643 = 3611465) B3611465
theorem B474335 : Blo 315835 474335 := bstep (se 1 (by rfl) ⟨355751, by rfl⟩ : syracuseStep 474335 = 711503) B711503
theorem B2702585 : Blo 315835 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B474377 : Blo 315835 474377 := bstep (se 2 (by rfl) ⟨177891, by rfl⟩ : syracuseStep 474377 = 355783) B355783
theorem B507145 : Blo 315835 507145 := bstep (se 2 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 507145 = 380359) B380359
theorem B474479 : Blo 315835 474479 := bstep (se 1 (by rfl) ⟨355859, by rfl⟩ : syracuseStep 474479 = 711719) B711719
theorem B474599 : Blo 315835 474599 := bstep (se 1 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 474599 = 711899) B711899
theorem B474731 : Blo 315835 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B966287 : Blo 315835 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B474857 : Blo 315835 474857 := bstep (se 2 (by rfl) ⟨178071, by rfl⟩ : syracuseStep 474857 = 356143) B356143
theorem B5816123 : Blo 315835 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B475001 : Blo 315835 475001 := bstep (se 2 (by rfl) ⟨178125, by rfl⟩ : syracuseStep 475001 = 356251) B356251
theorem B475103 : Blo 315835 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B4571225 : Blo 315835 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B475355 : Blo 315835 475355 := bstep (se 1 (by rfl) ⟨356516, by rfl⟩ : syracuseStep 475355 = 713033) B713033
theorem B475367 : Blo 315835 475367 := bstep (se 1 (by rfl) ⟨356525, by rfl⟩ : syracuseStep 475367 = 713051) B713051
theorem B3064169 : Blo 315835 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B475529 : Blo 315835 475529 := bstep (se 2 (by rfl) ⟨178323, by rfl⟩ : syracuseStep 475529 = 356647) B356647
theorem B475625 : Blo 315835 475625 := bstep (se 2 (by rfl) ⟨178359, by rfl⟩ : syracuseStep 475625 = 356719) B356719
theorem B1622567 : Blo 315835 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B901705 : Blo 315835 901705 := bstep (se 2 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 901705 = 676279) B676279
theorem B475751 : Blo 315835 475751 := bstep (se 1 (by rfl) ⟨356813, by rfl⟩ : syracuseStep 475751 = 713627) B713627
theorem B7684753 : Blo 315835 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B475883 : Blo 315835 475883 := bstep (se 1 (by rfl) ⟨356912, by rfl⟩ : syracuseStep 475883 = 713825) B713825
theorem B475913 : Blo 315835 475913 := bstep (se 2 (by rfl) ⟨178467, by rfl⟩ : syracuseStep 475913 = 356935) B356935
theorem B803641 : Blo 315835 803641 := bstep (se 2 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 803641 = 602731) B602731
theorem B476015 : Blo 315835 476015 := bstep (se 1 (by rfl) ⟨357011, by rfl⟩ : syracuseStep 476015 = 714023) B714023
theorem B1360759 : Blo 315835 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B8700965 : Blo 315835 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B2049083 : Blo 315835 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B803945 : Blo 315835 803945 := bstep (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) B602959
theorem B476267 : Blo 315835 476267 := bstep (se 1 (by rfl) ⟨357200, by rfl⟩ : syracuseStep 476267 = 714401) B714401
theorem B476507 : Blo 315835 476507 := bstep (se 1 (by rfl) ⟨357380, by rfl⟩ : syracuseStep 476507 = 714761) B714761
theorem B1066607 : Blo 315835 1066607 := bstep (se 1 (by rfl) ⟨799955, by rfl⟩ : syracuseStep 1066607 = 1599911) B1599911
theorem B476783 : Blo 315835 476783 := bstep (se 1 (by rfl) ⟨357587, by rfl⟩ : syracuseStep 476783 = 715175) B715175
theorem B476855 : Blo 315835 476855 := bstep (se 1 (by rfl) ⟨357641, by rfl⟩ : syracuseStep 476855 = 715283) B715283
theorem B1066715 : Blo 315835 1066715 := bstep (se 1 (by rfl) ⟨800036, by rfl⟩ : syracuseStep 1066715 = 1600073) B1600073
theorem B476891 : Blo 315835 476891 := bstep (se 1 (by rfl) ⟨357668, by rfl⟩ : syracuseStep 476891 = 715337) B715337
theorem B1820495 : Blo 315835 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B477065 : Blo 315835 477065 := bstep (se 2 (by rfl) ⟨178899, by rfl⟩ : syracuseStep 477065 = 357799) B357799
theorem B477167 : Blo 315835 477167 := bstep (se 1 (by rfl) ⟨357875, by rfl⟩ : syracuseStep 477167 = 715751) B715751
theorem B1722559 : Blo 315835 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B968915 : Blo 315835 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B805079 : Blo 315835 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B805099 : Blo 315835 805099 := bstep (se 1 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 805099 = 1207649) B1207649
theorem B477419 : Blo 315835 477419 := bstep (se 1 (by rfl) ⟨358064, by rfl⟩ : syracuseStep 477419 = 716129) B716129
theorem B575723 : Blo 315835 575723 := bstep (se 1 (by rfl) ⟨431792, by rfl⟩ : syracuseStep 575723 = 863585) B863585
theorem B477479 : Blo 315835 477479 := bstep (se 1 (by rfl) ⟨358109, by rfl⟩ : syracuseStep 477479 = 716219) B716219
theorem B477563 : Blo 315835 477563 := bstep (se 1 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 477563 = 716345) B716345
theorem B805403 : Blo 315835 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B477833 : Blo 315835 477833 := bstep (se 2 (by rfl) ⟨179187, by rfl⟩ : syracuseStep 477833 = 358375) B358375
theorem B478007 : Blo 315835 478007 := bstep (se 1 (by rfl) ⟨358505, by rfl⟩ : syracuseStep 478007 = 717011) B717011
theorem B478043 : Blo 315835 478043 := bstep (se 1 (by rfl) ⟨358532, by rfl⟩ : syracuseStep 478043 = 717065) B717065
theorem B1068011 : Blo 315835 1068011 := bstep (se 1 (by rfl) ⟨801008, by rfl⟩ : syracuseStep 1068011 = 1602017) B1602017
theorem B478187 : Blo 315835 478187 := bstep (se 1 (by rfl) ⟨358640, by rfl⟩ : syracuseStep 478187 = 717281) B717281
theorem B1068065 : Blo 315835 1068065 := bstep (se 2 (by rfl) ⟨400524, by rfl⟩ : syracuseStep 1068065 = 801049) B801049
theorem B478391 : Blo 315835 478391 := bstep (se 1 (by rfl) ⟨358793, by rfl⟩ : syracuseStep 478391 = 717587) B717587
theorem B511343 : Blo 315835 511343 := bstep (se 1 (by rfl) ⟨383507, by rfl⟩ : syracuseStep 511343 = 767015) B767015
theorem B478631 : Blo 315835 478631 := bstep (se 1 (by rfl) ⟨358973, by rfl⟩ : syracuseStep 478631 = 717947) B717947
theorem B806395 : Blo 315835 806395 := bstep (se 1 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 806395 = 1209593) B1209593
theorem B478715 : Blo 315835 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B2706959 : Blo 315835 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B675391 : Blo 315835 675391 := bstep (se 1 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 675391 = 1013087) B1013087
theorem B478811 : Blo 315835 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B806507 : Blo 315835 806507 := bstep (se 1 (by rfl) ⟨604880, by rfl⟩ : syracuseStep 806507 = 1209761) B1209761
theorem B478895 : Blo 315835 478895 := bstep (se 1 (by rfl) ⟨359171, by rfl⟩ : syracuseStep 478895 = 718343) B718343
theorem B479015 : Blo 315835 479015 := bstep (se 1 (by rfl) ⟨359261, by rfl⟩ : syracuseStep 479015 = 718523) B718523
theorem B380743 : Blo 315835 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B479099 : Blo 315835 479099 := bstep (se 1 (by rfl) ⟨359324, by rfl⟩ : syracuseStep 479099 = 718649) B718649
theorem B479519 : Blo 315835 479519 := bstep (se 1 (by rfl) ⟨359639, by rfl⟩ : syracuseStep 479519 = 719279) B719279
theorem B4084019 : Blo 315835 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B479543 : Blo 315835 479543 := bstep (se 1 (by rfl) ⟨359657, by rfl⟩ : syracuseStep 479543 = 719315) B719315
theorem B479615 : Blo 315835 479615 := bstep (se 1 (by rfl) ⟨359711, by rfl⟩ : syracuseStep 479615 = 719423) B719423
theorem B479687 : Blo 315835 479687 := bstep (se 1 (by rfl) ⟨359765, by rfl⟩ : syracuseStep 479687 = 719531) B719531
theorem B315855 : Blo 315835 315855 := bstep (se 1 (by rfl) ⟨236891, by rfl⟩ : syracuseStep 315855 = 473783) B473783
theorem B1069523 : Blo 315835 1069523 := bstep (se 1 (by rfl) ⟨802142, by rfl⟩ : syracuseStep 1069523 = 1604285) B1604285
theorem B2806343 : Blo 315835 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B971347 : Blo 315835 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B316007 : Blo 315835 316007 := bstep (se 1 (by rfl) ⟨237005, by rfl⟩ : syracuseStep 316007 = 474011) B474011
theorem B316271 : Blo 315835 316271 := bstep (se 1 (by rfl) ⟨237203, by rfl⟩ : syracuseStep 316271 = 474407) B474407
theorem B316327 : Blo 315835 316327 := bstep (se 1 (by rfl) ⟨237245, by rfl⟩ : syracuseStep 316327 = 474491) B474491
theorem B316411 : Blo 315835 316411 := bstep (se 1 (by rfl) ⟨237308, by rfl⟩ : syracuseStep 316411 = 474617) B474617
theorem B1725455 : Blo 315835 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B316479 : Blo 315835 316479 := bstep (se 1 (by rfl) ⟨237359, by rfl⟩ : syracuseStep 316479 = 474719) B474719
theorem B1528895 : Blo 315835 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B676937 : Blo 315835 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B382127 : Blo 315835 382127 := bstep (se 1 (by rfl) ⟨286595, by rfl⟩ : syracuseStep 382127 = 573191) B573191
theorem B1365167 : Blo 315835 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B316623 : Blo 315835 316623 := bstep (se 1 (by rfl) ⟨237467, by rfl⟩ : syracuseStep 316623 = 474935) B474935
theorem B1201499 : Blo 315835 1201499 := bstep (se 1 (by rfl) ⟨901124, by rfl⟩ : syracuseStep 1201499 = 1802249) B1802249
theorem B316827 : Blo 315835 316827 := bstep (se 1 (by rfl) ⟨237620, by rfl⟩ : syracuseStep 316827 = 475241) B475241
theorem B317039 : Blo 315835 317039 := bstep (se 1 (by rfl) ⟨237779, by rfl⟩ : syracuseStep 317039 = 475559) B475559
theorem B317095 : Blo 315835 317095 := bstep (se 1 (by rfl) ⟨237821, by rfl⟩ : syracuseStep 317095 = 475643) B475643
theorem B317179 : Blo 315835 317179 := bstep (se 1 (by rfl) ⟨237884, by rfl⟩ : syracuseStep 317179 = 475769) B475769
theorem B317215 : Blo 315835 317215 := bstep (se 1 (by rfl) ⟨237911, by rfl⟩ : syracuseStep 317215 = 475823) B475823
theorem B317247 : Blo 315835 317247 := bstep (se 1 (by rfl) ⟨237935, by rfl⟩ : syracuseStep 317247 = 475871) B475871
theorem B710639 : Blo 315835 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B317423 : Blo 315835 317423 := bstep (se 1 (by rfl) ⟨238067, by rfl⟩ : syracuseStep 317423 = 476135) B476135
theorem B317595 : Blo 315835 317595 := bstep (se 1 (by rfl) ⟨238196, by rfl⟩ : syracuseStep 317595 = 476393) B476393
theorem B317631 : Blo 315835 317631 := bstep (se 1 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 317631 = 476447) B476447
theorem B710855 : Blo 315835 710855 := bstep (se 1 (by rfl) ⟨533141, by rfl⟩ : syracuseStep 710855 = 1066283) B1066283
theorem B1726667 : Blo 315835 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B317743 : Blo 315835 317743 := bstep (se 1 (by rfl) ⟨238307, by rfl⟩ : syracuseStep 317743 = 476615) B476615
theorem B1071467 : Blo 315835 1071467 := bstep (se 1 (by rfl) ⟨803600, by rfl⟩ : syracuseStep 1071467 = 1607201) B1607201
theorem B711035 : Blo 315835 711035 := bstep (se 1 (by rfl) ⟨533276, by rfl⟩ : syracuseStep 711035 = 1066553) B1066553
theorem B3037607 : Blo 315835 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B317979 : Blo 315835 317979 := bstep (se 1 (by rfl) ⟨238484, by rfl⟩ : syracuseStep 317979 = 476969) B476969
theorem B317983 : Blo 315835 317983 := bstep (se 1 (by rfl) ⟨238487, by rfl⟩ : syracuseStep 317983 = 476975) B476975
theorem B1071737 : Blo 315835 1071737 := bstep (se 2 (by rfl) ⟨401901, by rfl⟩ : syracuseStep 1071737 = 803803) B803803
theorem B711305 : Blo 315835 711305 := bstep (se 2 (by rfl) ⟨266739, by rfl⟩ : syracuseStep 711305 = 533479) B533479
theorem B318299 : Blo 315835 318299 := bstep (se 1 (by rfl) ⟨238724, by rfl⟩ : syracuseStep 318299 = 477449) B477449
theorem B318367 : Blo 315835 318367 := bstep (se 1 (by rfl) ⟨238775, by rfl⟩ : syracuseStep 318367 = 477551) B477551
theorem B1072169 : Blo 315835 1072169 := bstep (se 2 (by rfl) ⟨402063, by rfl⟩ : syracuseStep 1072169 = 804127) B804127
theorem B318511 : Blo 315835 318511 := bstep (se 1 (by rfl) ⟨238883, by rfl⟩ : syracuseStep 318511 = 477767) B477767
theorem B318535 : Blo 315835 318535 := bstep (se 1 (by rfl) ⟨238901, by rfl⟩ : syracuseStep 318535 = 477803) B477803
theorem B711863 : Blo 315835 711863 := bstep (se 1 (by rfl) ⟨533897, by rfl⟩ : syracuseStep 711863 = 1067795) B1067795
theorem B908471 : Blo 315835 908471 := bstep (se 1 (by rfl) ⟨681353, by rfl⟩ : syracuseStep 908471 = 1362707) B1362707
theorem B3038411 : Blo 315835 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B449759 : Blo 315835 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B318687 : Blo 315835 318687 := bstep (se 1 (by rfl) ⟨239015, by rfl⟩ : syracuseStep 318687 = 478031) B478031
theorem B318951 : Blo 315835 318951 := bstep (se 1 (by rfl) ⟨239213, by rfl⟩ : syracuseStep 318951 = 478427) B478427
theorem B515675 : Blo 315835 515675 := bstep (se 1 (by rfl) ⟨386756, by rfl⟩ : syracuseStep 515675 = 773513) B773513
theorem B319067 : Blo 315835 319067 := bstep (se 1 (by rfl) ⟨239300, by rfl⟩ : syracuseStep 319067 = 478601) B478601
theorem B712439 : Blo 315835 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B319303 : Blo 315835 319303 := bstep (se 1 (by rfl) ⟨239477, by rfl⟩ : syracuseStep 319303 = 478955) B478955
theorem B712619 : Blo 315835 712619 := bstep (se 1 (by rfl) ⟨534464, by rfl⟩ : syracuseStep 712619 = 1068929) B1068929
theorem B909245 : Blo 315835 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B319455 : Blo 315835 319455 := bstep (se 1 (by rfl) ⟨239591, by rfl⟩ : syracuseStep 319455 = 479183) B479183
theorem B319719 : Blo 315835 319719 := bstep (se 1 (by rfl) ⟨239789, by rfl⟩ : syracuseStep 319719 = 479579) B479579
theorem B3039565 : Blo 315835 3039565 := bstep (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) B1139837
theorem B713159 : Blo 315835 713159 := bstep (se 1 (by rfl) ⟨534869, by rfl⟩ : syracuseStep 713159 = 1069739) B1069739
theorem B713519 : Blo 315835 713519 := bstep (se 1 (by rfl) ⟨535139, by rfl⟩ : syracuseStep 713519 = 1070279) B1070279
theorem B910237 : Blo 315835 910237 := bstep (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) B341339
theorem B3072977 : Blo 315835 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B1074383 : Blo 315835 1074383 := bstep (se 1 (by rfl) ⟨805787, by rfl⟩ : syracuseStep 1074383 = 1611575) B1611575
theorem B1074707 : Blo 315835 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B1926737 : Blo 315835 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1599263 : Blo 315835 1599263 := bstep (se 1 (by rfl) ⟨1199447, by rfl⟩ : syracuseStep 1599263 = 2398895) B2398895
theorem B4384543 : Blo 315835 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B714527 : Blo 315835 714527 := bstep (se 1 (by rfl) ⟨535895, by rfl⟩ : syracuseStep 714527 = 1071791) B1071791
theorem B714743 : Blo 315835 714743 := bstep (se 1 (by rfl) ⟨536057, by rfl⟩ : syracuseStep 714743 = 1072115) B1072115
theorem B10971449 : Blo 315835 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B715103 : Blo 315835 715103 := bstep (se 1 (by rfl) ⟨536327, by rfl⟩ : syracuseStep 715103 = 1072655) B1072655
theorem B4057775 : Blo 315835 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1075895 : Blo 315835 1075895 := bstep (se 1 (by rfl) ⟨806921, by rfl⟩ : syracuseStep 1075895 = 1613843) B1613843
theorem B1600559 : Blo 315835 1600559 := bstep (se 1 (by rfl) ⟨1200419, by rfl⟩ : syracuseStep 1600559 = 2400839) B2400839
theorem B715823 : Blo 315835 715823 := bstep (se 1 (by rfl) ⟨536867, by rfl⟩ : syracuseStep 715823 = 1073735) B1073735
theorem B1142059 : Blo 315835 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B2714957 : Blo 315835 2714957 := bstep (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) B1018109
theorem B716111 : Blo 315835 716111 := bstep (se 1 (by rfl) ⟨537083, by rfl⟩ : syracuseStep 716111 = 1074167) B1074167
theorem B716201 : Blo 315835 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B3862379 : Blo 315835 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B716687 : Blo 315835 716687 := bstep (se 1 (by rfl) ⟨537515, by rfl⟩ : syracuseStep 716687 = 1075031) B1075031
theorem B1961903 : Blo 315835 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B1077839 : Blo 315835 1077839 := bstep (se 1 (by rfl) ⟨808379, by rfl⟩ : syracuseStep 1077839 = 1616759) B1616759
theorem B717407 : Blo 315835 717407 := bstep (se 1 (by rfl) ⟨538055, by rfl⟩ : syracuseStep 717407 = 1076111) B1076111
theorem B357439 : Blo 315835 357439 := bstep (se 1 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 357439 = 536159) B536159
theorem B1078379 : Blo 315835 1078379 := bstep (se 1 (by rfl) ⟨808784, by rfl⟩ : syracuseStep 1078379 = 1617569) B1617569
theorem B357583 : Blo 315835 357583 := bstep (se 1 (by rfl) ⟨268187, by rfl⟩ : syracuseStep 357583 = 536375) B536375
theorem B718235 : Blo 315835 718235 := bstep (se 1 (by rfl) ⟨538676, by rfl⟩ : syracuseStep 718235 = 1077353) B1077353
theorem B2028989 : Blo 315835 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B718811 : Blo 315835 718811 := bstep (se 1 (by rfl) ⟨539108, by rfl⟩ : syracuseStep 718811 = 1078217) B1078217
theorem B718991 : Blo 315835 718991 := bstep (se 1 (by rfl) ⟨539243, by rfl⟩ : syracuseStep 718991 = 1078487) B1078487
theorem B358555 : Blo 315835 358555 := bstep (se 1 (by rfl) ⟨268916, by rfl⟩ : syracuseStep 358555 = 537833) B537833
theorem B719009 : Blo 315835 719009 := bstep (se 2 (by rfl) ⟨269628, by rfl⟩ : syracuseStep 719009 = 539257) B539257
theorem B358591 : Blo 315835 358591 := bstep (se 1 (by rfl) ⟨268943, by rfl⟩ : syracuseStep 358591 = 537887) B537887
theorem B719081 : Blo 315835 719081 := bstep (se 2 (by rfl) ⟨269655, by rfl⟩ : syracuseStep 719081 = 539311) B539311
theorem B2586887 : Blo 315835 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B1210733 : Blo 315835 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B588703 : Blo 315835 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B1637671 : Blo 315835 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B1703405 : Blo 315835 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B1113679 : Blo 315835 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B2490401 : Blo 315835 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B3047483 : Blo 315835 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2162875 : Blo 315835 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B327871 : Blo 315835 327871 := bstep (se 1 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 327871 = 491807) B491807
theorem B1081711 : Blo 315835 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B5800643 : Blo 315835 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B1147709 : Blo 315835 1147709 := bstep (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) B430391
theorem B1213649 : Blo 315835 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B1213663 : Blo 315835 1213663 := bstep (se 1 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 1213663 = 1820495) B1820495
theorem B1639727 : Blo 315835 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B1246751 : Blo 315835 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B2427083 : Blo 315835 2427083 := bstep (se 1 (by rfl) ⟨1820312, by rfl⟩ : syracuseStep 2427083 = 3640625) B3640625
theorem B1804639 : Blo 315835 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B6130025 : Blo 315835 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B1805165 : Blo 315835 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B2722679 : Blo 315835 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B2296745 : Blo 315835 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B1870895 : Blo 315835 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B920639 : Blo 315835 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1281233 : Blo 315835 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B1150303 : Blo 315835 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B1019263 : Blo 315835 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B5410637 : Blo 315835 5410637 := bstep (se 3 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 5410637 = 2028989) B2028989
theorem B1445855 : Blo 315835 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B1151111 : Blo 315835 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B1675453 : Blo 315835 1675453 := bstep (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) B628295
theorem B14094691 : Blo 315835 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B5509549 : Blo 315835 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B3248585 : Blo 315835 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B1808081 : Blo 315835 1808081 := bstep (se 2 (by rfl) ⟨678030, by rfl⟩ : syracuseStep 1808081 = 1356061) B1356061
theorem B3676265 : Blo 315835 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B1284491 : Blo 315835 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B5315371 : Blo 315835 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B7314299 : Blo 315835 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B9805321 : Blo 315835 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B1809971 : Blo 315835 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B5905979 : Blo 315835 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B600043 : Blo 315835 600043 := bstep (se 1 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 600043 = 900065) B900065
theorem B1484905 : Blo 315835 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B3877415 : Blo 315835 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B13806395 : Blo 315835 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B2042779 : Blo 315835 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B961811 : Blo 315835 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B535963 : Blo 315835 535963 := bstep (se 1 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 535963 = 803945) B803945
theorem B1814345 : Blo 315835 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B962687 : Blo 315835 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B536719 : Blo 315835 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B536935 : Blo 315835 536935 := bstep (se 1 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 536935 = 805403) B805403
theorem B8532361 : Blo 315835 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B4076021 : Blo 315835 4076021 := bstep (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) B382127
theorem B766783 : Blo 315835 766783 := bstep (se 1 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 766783 = 1150175) B1150175
theorem B340895 : Blo 315835 340895 := bstep (se 1 (by rfl) ⟨255671, by rfl⟩ : syracuseStep 340895 = 511343) B511343
theorem B5846057 : Blo 315835 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B537671 : Blo 315835 537671 := bstep (se 1 (by rfl) ⟨403253, by rfl⟩ : syracuseStep 537671 = 806507) B806507
theorem B1357019 : Blo 315835 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B4634657 : Blo 315835 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B2799755 : Blo 315835 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B3061937 : Blo 315835 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B800999 : Blo 315835 800999 := bstep (se 1 (by rfl) ⟨600749, by rfl⟩ : syracuseStep 800999 = 1201499) B1201499
theorem B1358059 : Blo 315835 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B1227271 : Blo 315835 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B473759 : Blo 315835 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B473903 : Blo 315835 473903 := bstep (se 1 (by rfl) ⟨355427, by rfl⟩ : syracuseStep 473903 = 710855) B710855
theorem B474023 : Blo 315835 474023 := bstep (se 1 (by rfl) ⟨355517, by rfl⟩ : syracuseStep 474023 = 711035) B711035
theorem B1522745 : Blo 315835 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B474203 : Blo 315835 474203 := bstep (se 1 (by rfl) ⟨355652, by rfl⟩ : syracuseStep 474203 = 711305) B711305
theorem B1621235 : Blo 315835 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B900521 : Blo 315835 900521 := bstep (se 2 (by rfl) ⟨337695, by rfl⟩ : syracuseStep 900521 = 675391) B675391
theorem B474575 : Blo 315835 474575 := bstep (se 1 (by rfl) ⟨355931, by rfl⟩ : syracuseStep 474575 = 711863) B711863
theorem B605647 : Blo 315835 605647 := bstep (se 1 (by rfl) ⟨454235, by rfl⟩ : syracuseStep 605647 = 908471) B908471
theorem B474959 : Blo 315835 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B1228733 : Blo 315835 1228733 := bstep (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) B460775
theorem B475079 : Blo 315835 475079 := bstep (se 1 (by rfl) ⟨356309, by rfl⟩ : syracuseStep 475079 = 712619) B712619
theorem B475439 : Blo 315835 475439 := bstep (se 1 (by rfl) ⟨356579, by rfl⟩ : syracuseStep 475439 = 713159) B713159
theorem B475679 : Blo 315835 475679 := bstep (se 1 (by rfl) ⟨356759, by rfl⟩ : syracuseStep 475679 = 713519) B713519
theorem B2048651 : Blo 315835 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B1295129 : Blo 315835 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B967735 : Blo 315835 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B1066175 : Blo 315835 1066175 := bstep (se 1 (by rfl) ⟨799631, by rfl⟩ : syracuseStep 1066175 = 1599263) B1599263
theorem B476351 : Blo 315835 476351 := bstep (se 1 (by rfl) ⟨357263, by rfl⟩ : syracuseStep 476351 = 714527) B714527
theorem B476495 : Blo 315835 476495 := bstep (se 1 (by rfl) ⟨357371, by rfl⟩ : syracuseStep 476495 = 714743) B714743
theorem B1066337 : Blo 315835 1066337 := bstep (se 2 (by rfl) ⟨399876, by rfl⟩ : syracuseStep 1066337 = 799753) B799753
theorem B476585 : Blo 315835 476585 := bstep (se 2 (by rfl) ⟨178719, by rfl⟩ : syracuseStep 476585 = 357439) B357439
theorem B476735 : Blo 315835 476735 := bstep (se 1 (by rfl) ⟨357551, by rfl⟩ : syracuseStep 476735 = 715103) B715103
theorem B476777 : Blo 315835 476777 := bstep (se 2 (by rfl) ⟨178791, by rfl⟩ : syracuseStep 476777 = 357583) B357583
theorem B2475805 : Blo 315835 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B2705183 : Blo 315835 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B1067039 : Blo 315835 1067039 := bstep (se 1 (by rfl) ⟨800279, by rfl⟩ : syracuseStep 1067039 = 1600559) B1600559
theorem B477215 : Blo 315835 477215 := bstep (se 1 (by rfl) ⟨357911, by rfl⟩ : syracuseStep 477215 = 715823) B715823
theorem B477407 : Blo 315835 477407 := bstep (se 1 (by rfl) ⟨358055, by rfl⟩ : syracuseStep 477407 = 716111) B716111
theorem B477467 : Blo 315835 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B2574919 : Blo 315835 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B477791 : Blo 315835 477791 := bstep (se 1 (by rfl) ⟨358343, by rfl⟩ : syracuseStep 477791 = 716687) B716687
theorem B576161 : Blo 315835 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B478073 : Blo 315835 478073 := bstep (se 2 (by rfl) ⟨179277, by rfl⟩ : syracuseStep 478073 = 358555) B358555
theorem B478121 : Blo 315835 478121 := bstep (se 2 (by rfl) ⟨179295, by rfl⟩ : syracuseStep 478121 = 358591) B358591
theorem B642043 : Blo 315835 642043 := bstep (se 1 (by rfl) ⟨481532, by rfl⟩ : syracuseStep 642043 = 963065) B963065
theorem B478271 : Blo 315835 478271 := bstep (se 1 (by rfl) ⟨358703, by rfl⟩ : syracuseStep 478271 = 717407) B717407
theorem B1199357 : Blo 315835 1199357 := bstep (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) B449759
theorem B478823 : Blo 315835 478823 := bstep (se 1 (by rfl) ⟨359117, by rfl⟩ : syracuseStep 478823 = 718235) B718235
theorem B2412503 : Blo 315835 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B479207 : Blo 315835 479207 := bstep (se 1 (by rfl) ⟨359405, by rfl⟩ : syracuseStep 479207 = 718811) B718811
theorem B479327 : Blo 315835 479327 := bstep (se 1 (by rfl) ⟨359495, by rfl⟩ : syracuseStep 479327 = 718991) B718991
theorem B479339 : Blo 315835 479339 := bstep (se 1 (by rfl) ⟨359504, by rfl⟩ : syracuseStep 479339 = 719009) B719009
theorem B479387 : Blo 315835 479387 := bstep (se 1 (by rfl) ⟨359540, by rfl⟩ : syracuseStep 479387 = 719081) B719081
theorem B1724591 : Blo 315835 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B2281691 : Blo 315835 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B807155 : Blo 315835 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B676193 : Blo 315835 676193 := bstep (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) B507145
theorem B2576765 : Blo 315835 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B2183561 : Blo 315835 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B316155 : Blo 315835 316155 := bstep (se 1 (by rfl) ⟨237116, by rfl⟩ : syracuseStep 316155 = 474233) B474233
theorem B316223 : Blo 315835 316223 := bstep (se 1 (by rfl) ⟨237167, by rfl⟩ : syracuseStep 316223 = 474335) B474335
theorem B316251 : Blo 315835 316251 := bstep (se 1 (by rfl) ⟨237188, by rfl⟩ : syracuseStep 316251 = 474377) B474377
theorem B316319 : Blo 315835 316319 := bstep (se 1 (by rfl) ⟨237239, by rfl⟩ : syracuseStep 316319 = 474479) B474479
theorem B316399 : Blo 315835 316399 := bstep (se 1 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 316399 = 474599) B474599
theorem B1135603 : Blo 315835 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B316487 : Blo 315835 316487 := bstep (se 1 (by rfl) ⟨237365, by rfl⟩ : syracuseStep 316487 = 474731) B474731
theorem B316571 : Blo 315835 316571 := bstep (se 1 (by rfl) ⟨237428, by rfl⟩ : syracuseStep 316571 = 474857) B474857
theorem B316667 : Blo 315835 316667 := bstep (se 1 (by rfl) ⟨237500, by rfl⟩ : syracuseStep 316667 = 475001) B475001
theorem B1070333 : Blo 315835 1070333 := bstep (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) B401375
theorem B316735 : Blo 315835 316735 := bstep (se 1 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 316735 = 475103) B475103
theorem B2413961 : Blo 315835 2413961 := bstep (se 2 (by rfl) ⟨905235, by rfl⟩ : syracuseStep 2413961 = 1810471) B1810471
theorem B316903 : Blo 315835 316903 := bstep (se 1 (by rfl) ⟨237677, by rfl⟩ : syracuseStep 316903 = 475355) B475355
theorem B316911 : Blo 315835 316911 := bstep (se 1 (by rfl) ⟨237683, by rfl⟩ : syracuseStep 316911 = 475367) B475367
theorem B317019 : Blo 315835 317019 := bstep (se 1 (by rfl) ⟨237764, by rfl⟩ : syracuseStep 317019 = 475529) B475529
theorem B317083 : Blo 315835 317083 := bstep (se 1 (by rfl) ⟨237812, by rfl⟩ : syracuseStep 317083 = 475625) B475625
theorem B317167 : Blo 315835 317167 := bstep (se 1 (by rfl) ⟨237875, by rfl⟩ : syracuseStep 317167 = 475751) B475751
theorem B4052753 : Blo 315835 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B677663 : Blo 315835 677663 := bstep (se 1 (by rfl) ⟨508247, by rfl⟩ : syracuseStep 677663 = 1016495) B1016495
theorem B317255 : Blo 315835 317255 := bstep (se 1 (by rfl) ⟨237941, by rfl⟩ : syracuseStep 317255 = 475883) B475883
theorem B808775 : Blo 315835 808775 := bstep (se 1 (by rfl) ⟨606581, by rfl⟩ : syracuseStep 808775 = 1213163) B1213163
theorem B317275 : Blo 315835 317275 := bstep (se 1 (by rfl) ⟨237956, by rfl⟩ : syracuseStep 317275 = 475913) B475913
theorem B317343 : Blo 315835 317343 := bstep (se 1 (by rfl) ⟨238007, by rfl⟩ : syracuseStep 317343 = 476015) B476015
theorem B1071143 : Blo 315835 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B1366055 : Blo 315835 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B317511 : Blo 315835 317511 := bstep (se 1 (by rfl) ⟨238133, by rfl⟩ : syracuseStep 317511 = 476267) B476267
theorem B1202273 : Blo 315835 1202273 := bstep (se 2 (by rfl) ⟨450852, by rfl⟩ : syracuseStep 1202273 = 901705) B901705
theorem B1071251 : Blo 315835 1071251 := bstep (se 1 (by rfl) ⟨803438, by rfl⟩ : syracuseStep 1071251 = 1606877) B1606877
theorem B10246337 : Blo 315835 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B678107 : Blo 315835 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B317671 : Blo 315835 317671 := bstep (se 1 (by rfl) ⟨238253, by rfl⟩ : syracuseStep 317671 = 476507) B476507
theorem B711071 : Blo 315835 711071 := bstep (se 1 (by rfl) ⟨533303, by rfl⟩ : syracuseStep 711071 = 1066607) B1066607
theorem B317855 : Blo 315835 317855 := bstep (se 1 (by rfl) ⟨238391, by rfl⟩ : syracuseStep 317855 = 476783) B476783
theorem B1071521 : Blo 315835 1071521 := bstep (se 2 (by rfl) ⟨401820, by rfl⟩ : syracuseStep 1071521 = 803641) B803641
theorem B2709935 : Blo 315835 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B317903 : Blo 315835 317903 := bstep (se 1 (by rfl) ⟨238427, by rfl⟩ : syracuseStep 317903 = 476855) B476855
theorem B711143 : Blo 315835 711143 := bstep (se 1 (by rfl) ⟨533357, by rfl⟩ : syracuseStep 711143 = 1066715) B1066715
theorem B317927 : Blo 315835 317927 := bstep (se 1 (by rfl) ⟨238445, by rfl⟩ : syracuseStep 317927 = 476891) B476891
theorem B1202759 : Blo 315835 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B318043 : Blo 315835 318043 := bstep (se 1 (by rfl) ⟨238532, by rfl⟩ : syracuseStep 318043 = 477065) B477065
theorem B318111 : Blo 315835 318111 := bstep (se 1 (by rfl) ⟨238583, by rfl⟩ : syracuseStep 318111 = 477167) B477167
theorem B645943 : Blo 315835 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B318279 : Blo 315835 318279 := bstep (se 1 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 318279 = 477419) B477419
theorem B383815 : Blo 315835 383815 := bstep (se 1 (by rfl) ⟨287861, by rfl⟩ : syracuseStep 383815 = 575723) B575723
theorem B318319 : Blo 315835 318319 := bstep (se 1 (by rfl) ⟨238739, by rfl⟩ : syracuseStep 318319 = 477479) B477479
theorem B875375 : Blo 315835 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B318375 : Blo 315835 318375 := bstep (se 1 (by rfl) ⟨238781, by rfl⟩ : syracuseStep 318375 = 477563) B477563
theorem B1072061 : Blo 315835 1072061 := bstep (se 3 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 1072061 = 402023) B402023
theorem B318555 : Blo 315835 318555 := bstep (se 1 (by rfl) ⟨238916, by rfl⟩ : syracuseStep 318555 = 477833) B477833
theorem B318671 : Blo 315835 318671 := bstep (se 1 (by rfl) ⟨239003, by rfl⟩ : syracuseStep 318671 = 478007) B478007
theorem B318695 : Blo 315835 318695 := bstep (se 1 (by rfl) ⟨239021, by rfl⟩ : syracuseStep 318695 = 478043) B478043
theorem B712007 : Blo 315835 712007 := bstep (se 1 (by rfl) ⟨534005, by rfl⟩ : syracuseStep 712007 = 1068011) B1068011
theorem B318791 : Blo 315835 318791 := bstep (se 1 (by rfl) ⟨239093, by rfl⟩ : syracuseStep 318791 = 478187) B478187
theorem B712043 : Blo 315835 712043 := bstep (se 1 (by rfl) ⟨534032, by rfl⟩ : syracuseStep 712043 = 1068065) B1068065
theorem B318927 : Blo 315835 318927 := bstep (se 1 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 318927 = 478391) B478391
theorem B712169 : Blo 315835 712169 := bstep (se 2 (by rfl) ⟨267063, by rfl⟩ : syracuseStep 712169 = 534127) B534127
theorem B1465847 : Blo 315835 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B23092775 : Blo 315835 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B319087 : Blo 315835 319087 := bstep (se 1 (by rfl) ⟨239315, by rfl⟩ : syracuseStep 319087 = 478631) B478631
theorem B712313 : Blo 315835 712313 := bstep (se 2 (by rfl) ⟨267117, by rfl⟩ : syracuseStep 712313 = 534235) B534235
theorem B319143 : Blo 315835 319143 := bstep (se 1 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 319143 = 478715) B478715
theorem B319207 : Blo 315835 319207 := bstep (se 1 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 319207 = 478811) B478811
theorem B3432223 : Blo 315835 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B319263 : Blo 315835 319263 := bstep (se 1 (by rfl) ⟨239447, by rfl⟩ : syracuseStep 319263 = 478895) B478895
theorem B319343 : Blo 315835 319343 := bstep (se 1 (by rfl) ⟨239507, by rfl⟩ : syracuseStep 319343 = 479015) B479015
theorem B319399 : Blo 315835 319399 := bstep (se 1 (by rfl) ⟨239549, by rfl⟩ : syracuseStep 319399 = 479099) B479099
theorem B319679 : Blo 315835 319679 := bstep (se 1 (by rfl) ⟨239759, by rfl⟩ : syracuseStep 319679 = 479519) B479519
theorem B319695 : Blo 315835 319695 := bstep (se 1 (by rfl) ⟨239771, by rfl⟩ : syracuseStep 319695 = 479543) B479543
theorem B319743 : Blo 315835 319743 := bstep (se 1 (by rfl) ⟨239807, by rfl⟩ : syracuseStep 319743 = 479615) B479615
theorem B319791 : Blo 315835 319791 := bstep (se 1 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 319791 = 479687) B479687
theorem B713015 : Blo 315835 713015 := bstep (se 1 (by rfl) ⟨534761, by rfl⟩ : syracuseStep 713015 = 1069523) B1069523
theorem B1073465 : Blo 315835 1073465 := bstep (se 2 (by rfl) ⟨402549, by rfl⟩ : syracuseStep 1073465 = 805099) B805099
theorem B1073951 : Blo 315835 1073951 := bstep (se 1 (by rfl) ⟨805463, by rfl⟩ : syracuseStep 1073951 = 1610927) B1610927
theorem B910111 : Blo 315835 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B714041 : Blo 315835 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B1205675 : Blo 315835 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B714311 : Blo 315835 714311 := bstep (se 1 (by rfl) ⟨535733, by rfl⟩ : syracuseStep 714311 = 1071467) B1071467
theorem B4351583 : Blo 315835 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B2025071 : Blo 315835 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B1599101 : Blo 315835 1599101 := bstep (se 3 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 1599101 = 599663) B599663
theorem B1074923 : Blo 315835 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B714491 : Blo 315835 714491 := bstep (se 1 (by rfl) ⟨535868, by rfl⟩ : syracuseStep 714491 = 1071737) B1071737
theorem B1075193 : Blo 315835 1075193 := bstep (se 2 (by rfl) ⟨403197, by rfl⟩ : syracuseStep 1075193 = 806395) B806395
theorem B714779 : Blo 315835 714779 := bstep (se 1 (by rfl) ⟨536084, by rfl⟩ : syracuseStep 714779 = 1072169) B1072169
theorem B2025607 : Blo 315835 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B1075463 : Blo 315835 1075463 := bstep (se 1 (by rfl) ⟨806597, by rfl⟩ : syracuseStep 1075463 = 1613195) B1613195
theorem B355711 : Blo 315835 355711 := bstep (se 1 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 355711 = 533567) B533567
theorem B716255 : Blo 315835 716255 := bstep (se 1 (by rfl) ⟨537191, by rfl⟩ : syracuseStep 716255 = 1074383) B1074383
theorem B716471 : Blo 315835 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B8122517 : Blo 315835 8122517 := bstep (se 6 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 8122517 = 380743) B380743
theorem B717263 : Blo 315835 717263 := bstep (se 1 (by rfl) ⟨537947, by rfl⟩ : syracuseStep 717263 = 1075895) B1075895
theorem B1536641 : Blo 315835 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B357115 : Blo 315835 357115 := bstep (se 1 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 357115 = 535673) B535673
theorem B717929 : Blo 315835 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B1307935 : Blo 315835 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B357871 : Blo 315835 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B357979 : Blo 315835 357979 := bstep (se 1 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 357979 = 536969) B536969
theorem B718559 : Blo 315835 718559 := bstep (se 1 (by rfl) ⟨538919, by rfl⟩ : syracuseStep 718559 = 1077839) B1077839
theorem B358267 : Blo 315835 358267 := bstep (se 1 (by rfl) ⟨268700, by rfl⟩ : syracuseStep 358267 = 537401) B537401
theorem B358303 : Blo 315835 358303 := bstep (se 1 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 358303 = 537455) B537455
theorem B718919 : Blo 315835 718919 := bstep (se 1 (by rfl) ⟨539189, by rfl⟩ : syracuseStep 718919 = 1078379) B1078379
theorem B1013971 : Blo 315835 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B784937 : Blo 315835 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B2718305 : Blo 315835 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B719585 : Blo 315835 719585 := bstep (se 2 (by rfl) ⟨269844, by rfl⟩ : syracuseStep 719585 = 539689) B539689
theorem B359239 : Blo 315835 359239 := bstep (se 1 (by rfl) ⟨269429, by rfl⟩ : syracuseStep 359239 = 538859) B538859
theorem B1211219 : Blo 315835 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B1375133 : Blo 315835 1375133 := bstep (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) B515675
theorem B1605095 : Blo 315835 1605095 := bstep (se 1 (by rfl) ⟨1203821, by rfl⟩ : syracuseStep 1605095 = 2407643) B2407643
theorem B1801723 : Blo 315835 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B9273041 : Blo 315835 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B2424653 : Blo 315835 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B2031655 : Blo 315835 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B2883833 : Blo 315835 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B3867095 : Blo 315835 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B1442281 : Blo 315835 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B1803181 : Blo 315835 1803181 := bstep (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) B676193
theorem B1213481 : Blo 315835 1213481 := bstep (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) B910111
theorem B1803455 : Blo 315835 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B75171685 : Blo 315835 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B854155 : Blo 315835 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B3607091 : Blo 315835 3607091 := bstep (se 1 (by rfl) ⟨2705318, by rfl⟩ : syracuseStep 3607091 = 5410637) B5410637
theorem B1608335 : Blo 315835 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B1149727 : Blo 315835 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B2165723 : Blo 315835 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B1609307 : Blo 315835 1609307 := bstep (se 1 (by rfl) ⟨1206980, by rfl⟩ : syracuseStep 1609307 = 2413961) B2413961
theorem B2723705 : Blo 315835 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B856057 : Blo 315835 856057 := bstep (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) B642043
theorem B28348645 : Blo 315835 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B856327 : Blo 315835 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1806623 : Blo 315835 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B3937319 : Blo 315835 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B2233937 : Blo 315835 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B7346065 : Blo 315835 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B1350047 : Blo 315835 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1022377 : Blo 315835 1022377 := bstep (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) B766783
theorem B1514137 : Blo 315835 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B1743913 : Blo 315835 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B5415011 : Blo 315835 5415011 := bstep (se 1 (by rfl) ⟨4061258, by rfl⟩ : syracuseStep 5415011 = 8122517) B8122517
theorem B4989053 : Blo 315835 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1351961 : Blo 315835 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B1810745 : Blo 315835 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B1024427 : Blo 315835 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B861257 : Blo 315835 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B3089771 : Blo 315835 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B2041291 : Blo 315835 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B533999 : Blo 315835 533999 := bstep (se 1 (by rfl) ⟨400499, by rfl⟩ : syracuseStep 533999 = 800999) B800999
theorem B1812203 : Blo 315835 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B2402297 : Blo 315835 2402297 := bstep (se 2 (by rfl) ⟨900861, by rfl⟩ : syracuseStep 2402297 = 1801723) B1801723
theorem B600347 : Blo 315835 600347 := bstep (se 1 (by rfl) ⟨450260, by rfl⟩ : syracuseStep 600347 = 900521) B900521
theorem B1616435 : Blo 315835 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B765139 : Blo 315835 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B1093151 : Blo 315835 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B1748645 : Blo 315835 1748645 := bstep (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) B327871
theorem B831167 : Blo 315835 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B1290313 : Blo 315835 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B1618055 : Blo 315835 1618055 := bstep (se 1 (by rfl) ⟨1213541, by rfl⟩ : syracuseStep 1618055 = 2427083) B2427083
theorem B1618217 : Blo 315835 1618217 := bstep (se 2 (by rfl) ⟨606831, by rfl⟩ : syracuseStep 1618217 = 1213663) B1213663
theorem B1815119 : Blo 315835 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B3453677 : Blo 315835 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B799571 : Blo 315835 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B800057 : Blo 315835 800057 := bstep (se 2 (by rfl) ⟨300021, by rfl⟩ : syracuseStep 800057 = 600043) B600043
theorem B767407 : Blo 315835 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B1979873 : Blo 315835 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B1521127 : Blo 315835 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B538103 : Blo 315835 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B2700809 : Blo 315835 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B1717843 : Blo 315835 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1455707 : Blo 315835 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B2406185 : Blo 315835 2406185 := bstep (se 2 (by rfl) ⟨902319, by rfl⟩ : syracuseStep 2406185 = 1804639) B1804639
theorem B2701835 : Blo 315835 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B539183 : Blo 315835 539183 := bstep (se 1 (by rfl) ⟨404387, by rfl⟩ : syracuseStep 539183 = 808775) B808775
theorem B801515 : Blo 315835 801515 := bstep (se 1 (by rfl) ⟨601136, by rfl⟩ : syracuseStep 801515 = 1202273) B1202273
theorem B6830891 : Blo 315835 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B474047 : Blo 315835 474047 := bstep (se 1 (by rfl) ⟨355535, by rfl⟩ : syracuseStep 474047 = 711071) B711071
theorem B474095 : Blo 315835 474095 := bstep (se 1 (by rfl) ⟨355571, by rfl⟩ : syracuseStep 474095 = 711143) B711143
theorem B801839 : Blo 315835 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B474281 : Blo 315835 474281 := bstep (se 2 (by rfl) ⟨177855, by rfl⟩ : syracuseStep 474281 = 355711) B355711
theorem B1359017 : Blo 315835 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B474671 : Blo 315835 474671 := bstep (se 1 (by rfl) ⟨356003, by rfl⟩ : syracuseStep 474671 = 712007) B712007
theorem B474695 : Blo 315835 474695 := bstep (se 1 (by rfl) ⟨356021, by rfl⟩ : syracuseStep 474695 = 712043) B712043
theorem B474779 : Blo 315835 474779 := bstep (se 1 (by rfl) ⟨356084, by rfl⟩ : syracuseStep 474779 = 712169) B712169
theorem B474875 : Blo 315835 474875 := bstep (se 1 (by rfl) ⟨356156, by rfl⟩ : syracuseStep 474875 = 712313) B712313
theorem B475343 : Blo 315835 475343 := bstep (se 1 (by rfl) ⟨356507, by rfl⟩ : syracuseStep 475343 = 713015) B713015
theorem B476027 : Blo 315835 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B803783 : Blo 315835 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B476153 : Blo 315835 476153 := bstep (se 2 (by rfl) ⟨178557, by rfl⟩ : syracuseStep 476153 = 357115) B357115
theorem B476207 : Blo 315835 476207 := bstep (se 1 (by rfl) ⟨357155, by rfl⟩ : syracuseStep 476207 = 714311) B714311
theorem B2901055 : Blo 315835 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B1066067 : Blo 315835 1066067 := bstep (se 1 (by rfl) ⟨799550, by rfl⟩ : syracuseStep 1066067 = 1599101) B1599101
theorem B476327 : Blo 315835 476327 := bstep (se 1 (by rfl) ⟨357245, by rfl⟩ : syracuseStep 476327 = 714491) B714491
theorem B476519 : Blo 315835 476519 := bstep (se 1 (by rfl) ⟨357389, by rfl⟩ : syracuseStep 476519 = 714779) B714779
theorem B477161 : Blo 315835 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B477305 : Blo 315835 477305 := bstep (se 2 (by rfl) ⟨178989, by rfl⟩ : syracuseStep 477305 = 357979) B357979
theorem B641207 : Blo 315835 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B477503 : Blo 315835 477503 := bstep (se 1 (by rfl) ⟨358127, by rfl⟩ : syracuseStep 477503 = 716255) B716255
theorem B477647 : Blo 315835 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B477689 : Blo 315835 477689 := bstep (se 2 (by rfl) ⟨179133, by rfl⟩ : syracuseStep 477689 = 358267) B358267
theorem B477737 : Blo 315835 477737 := bstep (se 2 (by rfl) ⟨179151, by rfl⟩ : syracuseStep 477737 = 358303) B358303
theorem B641791 : Blo 315835 641791 := bstep (se 1 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 641791 = 962687) B962687
theorem B478175 : Blo 315835 478175 := bstep (se 1 (by rfl) ⟨358631, by rfl⟩ : syracuseStep 478175 = 717263) B717263
theorem B478619 : Blo 315835 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B904679 : Blo 315835 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B478985 : Blo 315835 478985 := bstep (se 2 (by rfl) ⟨179619, by rfl⟩ : syracuseStep 478985 = 359239) B359239
theorem B511753 : Blo 315835 511753 := bstep (se 2 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 511753 = 383815) B383815
theorem B479039 : Blo 315835 479039 := bstep (se 1 (by rfl) ⟨359279, by rfl⟩ : syracuseStep 479039 = 718559) B718559
theorem B479279 : Blo 315835 479279 := bstep (se 1 (by rfl) ⟨359459, by rfl⟩ : syracuseStep 479279 = 718919) B718919
theorem B18305189 : Blo 315835 18305189 := bstep (se 4 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 18305189 = 3432223) B3432223
theorem B315839 : Blo 315835 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B479723 : Blo 315835 479723 := bstep (se 1 (by rfl) ⟨359792, by rfl⟩ : syracuseStep 479723 = 719585) B719585
theorem B315935 : Blo 315835 315935 := bstep (se 1 (by rfl) ⟨236951, by rfl⟩ : syracuseStep 315935 = 473903) B473903
theorem B807479 : Blo 315835 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B807529 : Blo 315835 807529 := bstep (se 2 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 807529 = 605647) B605647
theorem B316015 : Blo 315835 316015 := bstep (se 1 (by rfl) ⟨237011, by rfl⟩ : syracuseStep 316015 = 474023) B474023
theorem B316135 : Blo 315835 316135 := bstep (se 1 (by rfl) ⟨237101, by rfl⟩ : syracuseStep 316135 = 474203) B474203
theorem B316383 : Blo 315835 316383 := bstep (se 1 (by rfl) ⟨237287, by rfl⟩ : syracuseStep 316383 = 474575) B474575
theorem B1070063 : Blo 315835 1070063 := bstep (se 1 (by rfl) ⟨802547, by rfl⟩ : syracuseStep 1070063 = 1605095) B1605095
theorem B6182027 : Blo 315835 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B316639 : Blo 315835 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B3855613 : Blo 315835 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B316719 : Blo 315835 316719 := bstep (se 1 (by rfl) ⟨237539, by rfl⟩ : syracuseStep 316719 = 475079) B475079
theorem B1660267 : Blo 315835 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B316959 : Blo 315835 316959 := bstep (se 1 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 316959 = 475439) B475439
theorem B317119 : Blo 315835 317119 := bstep (se 1 (by rfl) ⟨237839, by rfl⟩ : syracuseStep 317119 = 475679) B475679
theorem B1365767 : Blo 315835 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B710783 : Blo 315835 710783 := bstep (se 1 (by rfl) ⟨533087, by rfl⟩ : syracuseStep 710783 = 1066175) B1066175
theorem B317567 : Blo 315835 317567 := bstep (se 1 (by rfl) ⟨238175, by rfl⟩ : syracuseStep 317567 = 476351) B476351
theorem B809099 : Blo 315835 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B317663 : Blo 315835 317663 := bstep (se 1 (by rfl) ⟨238247, by rfl⟩ : syracuseStep 317663 = 476495) B476495
theorem B710891 : Blo 315835 710891 := bstep (se 1 (by rfl) ⟨533168, by rfl⟩ : syracuseStep 710891 = 1066337) B1066337
theorem B317723 : Blo 315835 317723 := bstep (se 1 (by rfl) ⟨238292, by rfl⟩ : syracuseStep 317723 = 476585) B476585
theorem B317823 : Blo 315835 317823 := bstep (se 1 (by rfl) ⟨238367, by rfl⟩ : syracuseStep 317823 = 476735) B476735
theorem B317851 : Blo 315835 317851 := bstep (se 1 (by rfl) ⟨238388, by rfl⟩ : syracuseStep 317851 = 476777) B476777
theorem B711359 : Blo 315835 711359 := bstep (se 1 (by rfl) ⟨533519, by rfl⟩ : syracuseStep 711359 = 1067039) B1067039
theorem B318143 : Blo 315835 318143 := bstep (se 1 (by rfl) ⟨238607, by rfl⟩ : syracuseStep 318143 = 477215) B477215
theorem B318271 : Blo 315835 318271 := bstep (se 1 (by rfl) ⟨238703, by rfl⟩ : syracuseStep 318271 = 477407) B477407
theorem B318311 : Blo 315835 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B4086683 : Blo 315835 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B318527 : Blo 315835 318527 := bstep (se 1 (by rfl) ⟨238895, by rfl⟩ : syracuseStep 318527 = 477791) B477791
theorem B384107 : Blo 315835 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B1203443 : Blo 315835 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B318715 : Blo 315835 318715 := bstep (se 1 (by rfl) ⟨239036, by rfl⟩ : syracuseStep 318715 = 478073) B478073
theorem B1531163 : Blo 315835 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B318747 : Blo 315835 318747 := bstep (se 1 (by rfl) ⟨239060, by rfl⟩ : syracuseStep 318747 = 478121) B478121
theorem B318847 : Blo 315835 318847 := bstep (se 1 (by rfl) ⟨239135, by rfl⟩ : syracuseStep 318847 = 478271) B478271
theorem B613759 : Blo 315835 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B45505925 : Blo 315835 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B3301073 : Blo 315835 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B319215 : Blo 315835 319215 := bstep (se 1 (by rfl) ⟨239411, by rfl⟩ : syracuseStep 319215 = 478823) B478823
theorem B909053 : Blo 315835 909053 := bstep (se 3 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 909053 = 340895) B340895
theorem B319471 : Blo 315835 319471 := bstep (se 1 (by rfl) ⟨239603, by rfl⟩ : syracuseStep 319471 = 479207) B479207
theorem B319551 : Blo 315835 319551 := bstep (se 1 (by rfl) ⟨239663, by rfl⟩ : syracuseStep 319551 = 479327) B479327
theorem B319559 : Blo 315835 319559 := bstep (se 1 (by rfl) ⟨239669, by rfl⟩ : syracuseStep 319559 = 479339) B479339
theorem B319591 : Blo 315835 319591 := bstep (se 1 (by rfl) ⟨239693, by rfl⟩ : syracuseStep 319591 = 479387) B479387
theorem B3433225 : Blo 315835 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B713555 : Blo 315835 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B1205387 : Blo 315835 1205387 := bstep (se 1 (by rfl) ⟨904040, by rfl⟩ : syracuseStep 1205387 = 1808081) B1808081
theorem B451775 : Blo 315835 451775 := bstep (se 1 (by rfl) ⟨338831, by rfl⟩ : syracuseStep 451775 = 677663) B677663
theorem B714095 : Blo 315835 714095 := bstep (se 1 (by rfl) ⟨535571, by rfl⟩ : syracuseStep 714095 = 1071143) B1071143
theorem B910703 : Blo 315835 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B2450843 : Blo 315835 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B714167 : Blo 315835 714167 := bstep (se 1 (by rfl) ⟨535625, by rfl⟩ : syracuseStep 714167 = 1071251) B1071251
theorem B452071 : Blo 315835 452071 := bstep (se 1 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 452071 = 678107) B678107
theorem B714347 : Blo 315835 714347 := bstep (se 1 (by rfl) ⟨535760, by rfl⟩ : syracuseStep 714347 = 1071521) B1071521
theorem B1533737 : Blo 315835 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B714617 : Blo 315835 714617 := bstep (se 2 (by rfl) ⟨267981, by rfl⟩ : syracuseStep 714617 = 535963) B535963
theorem B583583 : Blo 315835 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B4876199 : Blo 315835 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B714707 : Blo 315835 714707 := bstep (se 1 (by rfl) ⟨536030, by rfl⟩ : syracuseStep 714707 = 1072061) B1072061
theorem B977231 : Blo 315835 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B15395183 : Blo 315835 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B1206647 : Blo 315835 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B715625 : Blo 315835 715625 := bstep (se 2 (by rfl) ⟨268359, by rfl⟩ : syracuseStep 715625 = 536719) B536719
theorem B715643 : Blo 315835 715643 := bstep (se 1 (by rfl) ⟨536732, by rfl⟩ : syracuseStep 715643 = 1073465) B1073465
theorem B715913 : Blo 315835 715913 := bstep (se 2 (by rfl) ⟨268467, by rfl⟩ : syracuseStep 715913 = 536935) B536935
theorem B715967 : Blo 315835 715967 := bstep (se 1 (by rfl) ⟨536975, by rfl⟩ : syracuseStep 715967 = 1073951) B1073951
theorem B716615 : Blo 315835 716615 := bstep (se 1 (by rfl) ⟨537461, by rfl⟩ : syracuseStep 716615 = 1074923) B1074923
theorem B716795 : Blo 315835 716795 := bstep (se 1 (by rfl) ⟨537596, by rfl⟩ : syracuseStep 716795 = 1075193) B1075193
theorem B2093165 : Blo 315835 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B716975 : Blo 315835 716975 := bstep (se 1 (by rfl) ⟨537731, by rfl⟩ : syracuseStep 716975 = 1075463) B1075463
theorem B2584943 : Blo 315835 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B9204263 : Blo 315835 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B3667021 : Blo 315835 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B1209563 : Blo 315835 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B2717347 : Blo 315835 2717347 := bstep (se 1 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 2717347 = 4076021) B4076021
theorem B1636361 : Blo 315835 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B3897371 : Blo 315835 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B358447 : Blo 315835 358447 := bstep (se 1 (by rfl) ⟨268835, by rfl⟩ : syracuseStep 358447 = 537671) B537671
theorem B1866503 : Blo 315835 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B13073761 : Blo 315835 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B1015163 : Blo 315835 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B1080823 : Blo 315835 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B819155 : Blo 315835 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B6881669 : Blo 315835 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B4097141 : Blo 315835 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B3868073 : Blo 315835 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B2721721 : Blo 315835 2721721 := bstep (se 2 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 2721721 = 2041291) B2041291
theorem B1443815 : Blo 315835 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B2624879 : Blo 315835 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2428541 : Blo 315835 2428541 := bstep (se 3 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 2428541 = 910703) B910703
theorem B855721 : Blo 315835 855721 := bstep (se 2 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 855721 = 641791) B641791
theorem B1020185 : Blo 315835 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B2724455 : Blo 315835 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B604771093 : Blo 315835 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B1020775 : Blo 315835 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B2200715 : Blo 315835 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B3610007 : Blo 315835 3610007 := bstep (se 1 (by rfl) ⟨2707505, by rfl⟩ : syracuseStep 3610007 = 5415011) B5415011
theorem B1709885 : Blo 315835 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B1022491 : Blo 315835 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B3250799 : Blo 315835 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B400231 : Blo 315835 400231 := bstep (se 1 (by rfl) ⟨300173, by rfl⟩ : syracuseStep 400231 = 600347) B600347
theorem B10263455 : Blo 315835 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B1023209 : Blo 315835 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B728767 : Blo 315835 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B6136175 : Blo 315835 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2302451 : Blo 315835 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B533047 : Blo 315835 533047 := bstep (se 1 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 533047 = 799571) B799571
theorem B533371 : Blo 315835 533371 := bstep (se 1 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 533371 = 800057) B800057
theorem B1319915 : Blo 315835 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1090907 : Blo 315835 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B2598247 : Blo 315835 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B534343 : Blo 315835 534343 := bstep (se 1 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 534343 = 801515) B801515
theorem B534559 : Blo 315835 534559 := bstep (se 1 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 534559 = 801839) B801839
theorem B535855 : Blo 315835 535855 := bstep (se 1 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 535855 = 803783) B803783
theorem B2731805 : Blo 315835 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B2404241 : Blo 315835 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B2404727 : Blo 315835 2404727 := bstep (se 1 (by rfl) ⟨1803545, by rfl⟩ : syracuseStep 2404727 = 3607091) B3607091
theorem B603119 : Blo 315835 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B1815803 : Blo 315835 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B12203459 : Blo 315835 12203459 := bstep (se 1 (by rfl) ⟨9152594, by rfl⟩ : syracuseStep 12203459 = 18305189) B18305189
theorem B538319 : Blo 315835 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B1489291 : Blo 315835 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B473855 : Blo 315835 473855 := bstep (se 1 (by rfl) ⟨355391, by rfl⟩ : syracuseStep 473855 = 710783) B710783
theorem B539399 : Blo 315835 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B473927 : Blo 315835 473927 := bstep (se 1 (by rfl) ⟨355445, by rfl⟩ : syracuseStep 473927 = 710891) B710891
theorem B900031 : Blo 315835 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B474239 : Blo 315835 474239 := bstep (se 1 (by rfl) ⟨355679, by rfl⟩ : syracuseStep 474239 = 711359) B711359
theorem B802295 : Blo 315835 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B1556221 : Blo 315835 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B606035 : Blo 315835 606035 := bstep (se 1 (by rfl) ⟨454526, by rfl⟩ : syracuseStep 606035 = 909053) B909053
theorem B3326035 : Blo 315835 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B901307 : Blo 315835 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B475703 : Blo 315835 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B574171 : Blo 315835 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B803591 : Blo 315835 803591 := bstep (se 1 (by rfl) ⟨602693, by rfl⟩ : syracuseStep 803591 = 1205387) B1205387
theorem B476063 : Blo 315835 476063 := bstep (se 1 (by rfl) ⟨357047, by rfl⟩ : syracuseStep 476063 = 714095) B714095
theorem B476111 : Blo 315835 476111 := bstep (se 1 (by rfl) ⟨357083, by rfl⟩ : syracuseStep 476111 = 714167) B714167
theorem B476231 : Blo 315835 476231 := bstep (se 1 (by rfl) ⟨357173, by rfl⟩ : syracuseStep 476231 = 714347) B714347
theorem B476411 : Blo 315835 476411 := bstep (se 1 (by rfl) ⟨357308, by rfl⟩ : syracuseStep 476411 = 714617) B714617
theorem B476471 : Blo 315835 476471 := bstep (se 1 (by rfl) ⟨357353, by rfl⟩ : syracuseStep 476471 = 714707) B714707
theorem B804431 : Blo 315835 804431 := bstep (se 1 (by rfl) ⟨603323, by rfl⟩ : syracuseStep 804431 = 1206647) B1206647
theorem B2213689 : Blo 315835 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B477083 : Blo 315835 477083 := bstep (se 1 (by rfl) ⟨357812, by rfl⟩ : syracuseStep 477083 = 715625) B715625
theorem B477095 : Blo 315835 477095 := bstep (se 1 (by rfl) ⟨357821, by rfl⟩ : syracuseStep 477095 = 715643) B715643
theorem B477275 : Blo 315835 477275 := bstep (se 1 (by rfl) ⟨357956, by rfl⟩ : syracuseStep 477275 = 715913) B715913
theorem B477311 : Blo 315835 477311 := bstep (se 1 (by rfl) ⟨357983, by rfl⟩ : syracuseStep 477311 = 715967) B715967
theorem B3623129 : Blo 315835 3623129 := bstep (se 2 (by rfl) ⟨1358673, by rfl⟩ : syracuseStep 3623129 = 2717347) B2717347
theorem B1165763 : Blo 315835 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B2411045 : Blo 315835 2411045 := bstep (se 4 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 2411045 = 452071) B452071
theorem B477743 : Blo 315835 477743 := bstep (se 1 (by rfl) ⟨358307, by rfl⟩ : syracuseStep 477743 = 716615) B716615
theorem B477863 : Blo 315835 477863 := bstep (se 1 (by rfl) ⟨358397, by rfl⟩ : syracuseStep 477863 = 716795) B716795
theorem B477929 : Blo 315835 477929 := bstep (se 2 (by rfl) ⟨179223, by rfl⟩ : syracuseStep 477929 = 358447) B358447
theorem B1395443 : Blo 315835 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B477983 : Blo 315835 477983 := bstep (se 1 (by rfl) ⟨358487, by rfl⟩ : syracuseStep 477983 = 716975) B716975
theorem B1723295 : Blo 315835 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B1363169 : Blo 315835 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B806375 : Blo 315835 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B2018849 : Blo 315835 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B970471 : Blo 315835 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B316031 : Blo 315835 316031 := bstep (se 1 (by rfl) ⟨237023, by rfl⟩ : syracuseStep 316031 = 474047) B474047
theorem B316063 : Blo 315835 316063 := bstep (se 1 (by rfl) ⟨237047, by rfl⟩ : syracuseStep 316063 = 474095) B474095
theorem B316187 : Blo 315835 316187 := bstep (se 1 (by rfl) ⟨237140, by rfl⟩ : syracuseStep 316187 = 474281) B474281
theorem B906011 : Blo 315835 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B676775 : Blo 315835 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B316447 : Blo 315835 316447 := bstep (se 1 (by rfl) ⟨237335, by rfl⟩ : syracuseStep 316447 = 474671) B474671
theorem B316463 : Blo 315835 316463 := bstep (se 1 (by rfl) ⟨237347, by rfl⟩ : syracuseStep 316463 = 474695) B474695
theorem B316519 : Blo 315835 316519 := bstep (se 1 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 316519 = 474779) B474779
theorem B316583 : Blo 315835 316583 := bstep (se 1 (by rfl) ⟨237437, by rfl⟩ : syracuseStep 316583 = 474875) B474875
theorem B546103 : Blo 315835 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B2708873 : Blo 315835 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B316895 : Blo 315835 316895 := bstep (se 1 (by rfl) ⟨237671, by rfl⟩ : syracuseStep 316895 = 475343) B475343
theorem B1922555 : Blo 315835 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B2578063 : Blo 315835 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B317351 : Blo 315835 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B1923041 : Blo 315835 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B317435 : Blo 315835 317435 := bstep (se 1 (by rfl) ⟨238076, by rfl⟩ : syracuseStep 317435 = 476153) B476153
theorem B808987 : Blo 315835 808987 := bstep (se 1 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 808987 = 1213481) B1213481
theorem B317471 : Blo 315835 317471 := bstep (se 1 (by rfl) ⟨238103, by rfl⟩ : syracuseStep 317471 = 476207) B476207
theorem B710711 : Blo 315835 710711 := bstep (se 1 (by rfl) ⟨533033, by rfl⟩ : syracuseStep 710711 = 1066067) B1066067
theorem B317551 : Blo 315835 317551 := bstep (se 1 (by rfl) ⟨238163, by rfl⟩ : syracuseStep 317551 = 476327) B476327
theorem B1202303 : Blo 315835 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B317679 : Blo 315835 317679 := bstep (se 1 (by rfl) ⟨238259, by rfl⟩ : syracuseStep 317679 = 476519) B476519
theorem B4577633 : Blo 315835 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B318107 : Blo 315835 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B318203 : Blo 315835 318203 := bstep (se 1 (by rfl) ⟨238652, by rfl⟩ : syracuseStep 318203 = 477305) B477305
theorem B318335 : Blo 315835 318335 := bstep (se 1 (by rfl) ⟨238751, by rfl⟩ : syracuseStep 318335 = 477503) B477503
theorem B318431 : Blo 315835 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B318459 : Blo 315835 318459 := bstep (se 1 (by rfl) ⟨238844, by rfl⟩ : syracuseStep 318459 = 477689) B477689
theorem B318491 : Blo 315835 318491 := bstep (se 1 (by rfl) ⟨238868, by rfl⟩ : syracuseStep 318491 = 477737) B477737
theorem B1072223 : Blo 315835 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B318783 : Blo 315835 318783 := bstep (se 1 (by rfl) ⟨239087, by rfl⟩ : syracuseStep 318783 = 478175) B478175
theorem B319079 : Blo 315835 319079 := bstep (se 1 (by rfl) ⟨239309, by rfl⟩ : syracuseStep 319079 = 478619) B478619
theorem B1072871 : Blo 315835 1072871 := bstep (se 1 (by rfl) ⟨804653, by rfl⟩ : syracuseStep 1072871 = 1609307) B1609307
theorem B100228913 : Blo 315835 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B319323 : Blo 315835 319323 := bstep (se 1 (by rfl) ⟨239492, by rfl⟩ : syracuseStep 319323 = 478985) B478985
theorem B319359 : Blo 315835 319359 := bstep (se 1 (by rfl) ⟨239519, by rfl⟩ : syracuseStep 319359 = 479039) B479039
theorem B319519 : Blo 315835 319519 := bstep (se 1 (by rfl) ⟨239639, by rfl⟩ : syracuseStep 319519 = 479279) B479279
theorem B1138873 : Blo 315835 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B1204415 : Blo 315835 1204415 := bstep (se 1 (by rfl) ⟨903311, by rfl⟩ : syracuseStep 1204415 = 1806623) B1806623
theorem B319815 : Blo 315835 319815 := bstep (se 1 (by rfl) ⟨239861, by rfl⟩ : syracuseStep 319815 = 479723) B479723
theorem B1204733 : Blo 315835 1204733 := bstep (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) B451775
theorem B713375 : Blo 315835 713375 := bstep (se 1 (by rfl) ⟨535031, by rfl⟩ : syracuseStep 713375 = 1070063) B1070063
theorem B4121351 : Blo 315835 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1532969 : Blo 315835 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B910511 : Blo 315835 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B30337283 : Blo 315835 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B682337 : Blo 315835 682337 := bstep (se 2 (by rfl) ⟨255876, by rfl⟩ : syracuseStep 682337 = 511753) B511753
theorem B1141409 : Blo 315835 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B1207163 : Blo 315835 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B1141769 : Blo 315835 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B19557445 : Blo 315835 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B1076705 : Blo 315835 1076705 := bstep (se 2 (by rfl) ⟨403764, by rfl⟩ : syracuseStep 1076705 = 807529) B807529
theorem B2059847 : Blo 315835 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1633895 : Blo 315835 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B355999 : Blo 315835 355999 := bstep (se 1 (by rfl) ⟨266999, by rfl⟩ : syracuseStep 355999 = 533999) B533999
theorem B1208135 : Blo 315835 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B1601531 : Blo 315835 1601531 := bstep (se 1 (by rfl) ⟨1201148, by rfl⟩ : syracuseStep 1601531 = 2402297) B2402297
theorem B651487 : Blo 315835 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B5140817 : Blo 315835 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B1077623 : Blo 315835 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B2028169 : Blo 315835 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B2290457 : Blo 315835 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B554111 : Blo 315835 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B9794753 : Blo 315835 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B1078703 : Blo 315835 1078703 := bstep (se 1 (by rfl) ⟨809027, by rfl⟩ : syracuseStep 1078703 = 1618055) B1618055
theorem B1078811 : Blo 315835 1078811 := bstep (se 1 (by rfl) ⟨809108, by rfl⟩ : syracuseStep 1078811 = 1618217) B1618217
theorem B1210079 : Blo 315835 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B358735 : Blo 315835 358735 := bstep (se 1 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 358735 = 538103) B538103
theorem B1800539 : Blo 315835 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B1604123 : Blo 315835 1604123 := bstep (se 1 (by rfl) ⟨1203092, by rfl⟩ : syracuseStep 1604123 = 2406185) B2406185
theorem B2325217 : Blo 315835 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1801223 : Blo 315835 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B359455 : Blo 315835 359455 := bstep (se 1 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 359455 = 539183) B539183
theorem B17431681 : Blo 315835 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B818345 : Blo 315835 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1244335 : Blo 315835 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B4553927 : Blo 315835 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B1441097 : Blo 315835 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B4587779 : Blo 315835 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B1607363 : Blo 315835 1607363 := bstep (se 1 (by rfl) ⟨1205522, by rfl⟩ : syracuseStep 1607363 = 2411045) B2411045
theorem B1148863 : Blo 315835 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B2951585 : Blo 315835 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B1805915 : Blo 315835 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B1281703 : Blo 315835 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B1282027 : Blo 315835 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B3051755 : Blo 315835 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B2167199 : Blo 315835 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B66819275 : Blo 315835 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B1021979 : Blo 315835 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B727271 : Blo 315835 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B20224855 : Blo 315835 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B728137 : Blo 315835 728137 := bstep (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) B546103
theorem B761179 : Blo 315835 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B1089263 : Blo 315835 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B402079 : Blo 315835 402079 := bstep (se 1 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 402079 = 603119) B603119
theorem B369407 : Blo 315835 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B6529835 : Blo 315835 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B8135639 : Blo 315835 8135639 := bstep (se 1 (by rfl) ⟨6101729, by rfl⟩ : syracuseStep 8135639 = 12203459) B12203459
theorem B533641 : Blo 315835 533641 := bstep (se 2 (by rfl) ⟨200115, by rfl⟩ : syracuseStep 533641 = 400231) B400231
theorem B5383597 : Blo 315835 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B23242241 : Blo 315835 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B960731 : Blo 315835 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B534863 : Blo 315835 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B2074961 : Blo 315835 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B404023 : Blo 315835 404023 := bstep (se 1 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 404023 = 606035) B606035
theorem B4434713 : Blo 315835 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B600871 : Blo 315835 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B1518497 : Blo 315835 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B535727 : Blo 315835 535727 := bstep (se 1 (by rfl) ⟨401795, by rfl⟩ : syracuseStep 535727 = 803591) B803591
theorem B2731427 : Blo 315835 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B536287 : Blo 315835 536287 := bstep (se 1 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 536287 = 804431) B804431
theorem B962543 : Blo 315835 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B930295 : Blo 315835 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B1749919 : Blo 315835 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B537583 : Blo 315835 537583 := bstep (se 1 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 537583 = 806375) B806375
theorem B1619027 : Blo 315835 1619027 := bstep (se 1 (by rfl) ⟨1214270, by rfl⟩ : syracuseStep 1619027 = 2428541) B2428541
theorem B3519773 : Blo 315835 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1816303 : Blo 315835 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B604007 : Blo 315835 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B2406671 : Blo 315835 2406671 := bstep (se 1 (by rfl) ⟨1805003, by rfl⟩ : syracuseStep 2406671 = 3610007) B3610007
theorem B3062245 : Blo 315835 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B473807 : Blo 315835 473807 := bstep (se 1 (by rfl) ⟨355355, by rfl⟩ : syracuseStep 473807 = 710711) B710711
theorem B801535 : Blo 315835 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B474665 : Blo 315835 474665 := bstep (se 2 (by rfl) ⟨177999, by rfl⟩ : syracuseStep 474665 = 355999) B355999
theorem B802943 : Blo 315835 802943 := bstep (se 1 (by rfl) ⟨602207, by rfl⟩ : syracuseStep 802943 = 1204415) B1204415
theorem B868649 : Blo 315835 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B803155 : Blo 315835 803155 := bstep (se 1 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 803155 = 1204733) B1204733
theorem B475583 : Blo 315835 475583 := bstep (se 1 (by rfl) ⟨356687, by rfl⟩ : syracuseStep 475583 = 713375) B713375
theorem B607007 : Blo 315835 607007 := bstep (se 1 (by rfl) ⟨455255, by rfl⟩ : syracuseStep 607007 = 910511) B910511
theorem B2704225 : Blo 315835 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B1361033 : Blo 315835 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B804775 : Blo 315835 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B1821203 : Blo 315835 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B805423 : Blo 315835 805423 := bstep (se 1 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 805423 = 1208135) B1208135
theorem B1067687 : Blo 315835 1067687 := bstep (se 1 (by rfl) ⟨800765, by rfl⟩ : syracuseStep 1067687 = 1601531) B1601531
theorem B3427211 : Blo 315835 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B31771541 : Blo 315835 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B478313 : Blo 315835 478313 := bstep (se 2 (by rfl) ⟨179367, by rfl⟩ : syracuseStep 478313 = 358735) B358735
theorem B1526971 : Blo 315835 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B1363321 : Blo 315835 1363321 := bstep (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) B1022491
theorem B3100289 : Blo 315835 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B806719 : Blo 315835 806719 := bstep (se 1 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 806719 = 1210079) B1210079
theorem B1200041 : Blo 315835 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B479273 : Blo 315835 479273 := bstep (se 2 (by rfl) ⟨179727, by rfl⟩ : syracuseStep 479273 = 359455) B359455
theorem B1200359 : Blo 315835 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B1659113 : Blo 315835 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B1069415 : Blo 315835 1069415 := bstep (se 1 (by rfl) ⟨802061, by rfl⟩ : syracuseStep 1069415 = 1604123) B1604123
theorem B315903 : Blo 315835 315903 := bstep (se 1 (by rfl) ⟨236927, by rfl⟩ : syracuseStep 315903 = 473855) B473855
theorem B315951 : Blo 315835 315951 := bstep (se 1 (by rfl) ⟨236963, by rfl⟩ : syracuseStep 315951 = 473927) B473927
theorem B1200815 : Blo 315835 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B316159 : Blo 315835 316159 := bstep (se 1 (by rfl) ⟨237119, by rfl⟩ : syracuseStep 316159 = 474239) B474239
theorem B545563 : Blo 315835 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B3035951 : Blo 315835 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B971689 : Blo 315835 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B317135 : Blo 315835 317135 := bstep (se 1 (by rfl) ⟨237851, by rfl⟩ : syracuseStep 317135 = 475703) B475703
theorem B317375 : Blo 315835 317375 := bstep (se 1 (by rfl) ⟨238031, by rfl⟩ : syracuseStep 317375 = 476063) B476063
theorem B317407 : Blo 315835 317407 := bstep (se 1 (by rfl) ⟨238055, by rfl⟩ : syracuseStep 317407 = 476111) B476111
theorem B317487 : Blo 315835 317487 := bstep (se 1 (by rfl) ⟨238115, by rfl⟩ : syracuseStep 317487 = 476231) B476231
theorem B710729 : Blo 315835 710729 := bstep (se 2 (by rfl) ⟨266523, by rfl⟩ : syracuseStep 710729 = 533047) B533047
theorem B317607 : Blo 315835 317607 := bstep (se 1 (by rfl) ⟨238205, by rfl⟩ : syracuseStep 317607 = 476411) B476411
theorem B317647 : Blo 315835 317647 := bstep (se 1 (by rfl) ⟨238235, by rfl⟩ : syracuseStep 317647 = 476471) B476471
theorem B2578715 : Blo 315835 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B711161 : Blo 315835 711161 := bstep (se 2 (by rfl) ⟨266685, by rfl⟩ : syracuseStep 711161 = 533371) B533371
theorem B318055 : Blo 315835 318055 := bstep (se 1 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 318055 = 477083) B477083
theorem B318063 : Blo 315835 318063 := bstep (se 1 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 318063 = 477095) B477095
theorem B318183 : Blo 315835 318183 := bstep (se 1 (by rfl) ⟨238637, by rfl⟩ : syracuseStep 318183 = 477275) B477275
theorem B318207 : Blo 315835 318207 := bstep (se 1 (by rfl) ⟨238655, by rfl⟩ : syracuseStep 318207 = 477311) B477311
theorem B2415419 : Blo 315835 2415419 := bstep (se 1 (by rfl) ⟨1811564, by rfl⟩ : syracuseStep 2415419 = 3623129) B3623129
theorem B318495 : Blo 315835 318495 := bstep (se 1 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 318495 = 477743) B477743
theorem B318575 : Blo 315835 318575 := bstep (se 1 (by rfl) ⟨238931, by rfl⟩ : syracuseStep 318575 = 477863) B477863
theorem B3464329 : Blo 315835 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B318619 : Blo 315835 318619 := bstep (se 1 (by rfl) ⟨238964, by rfl⟩ : syracuseStep 318619 = 477929) B477929
theorem B318655 : Blo 315835 318655 := bstep (se 1 (by rfl) ⟨238991, by rfl⟩ : syracuseStep 318655 = 477983) B477983
theorem B908779 : Blo 315835 908779 := bstep (se 1 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 908779 = 1363169) B1363169
theorem B712457 : Blo 315835 712457 := bstep (se 2 (by rfl) ⟨267171, by rfl⟩ : syracuseStep 712457 = 534343) B534343
theorem B3628961 : Blo 315835 3628961 := bstep (se 2 (by rfl) ⟨1360860, by rfl⟩ : syracuseStep 3628961 = 2721721) B2721721
theorem B712745 : Blo 315835 712745 := bstep (se 2 (by rfl) ⟨267279, by rfl⟩ : syracuseStep 712745 = 534559) B534559
theorem B680123 : Blo 315835 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B451183 : Blo 315835 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B1467143 : Blo 315835 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1139923 : Blo 315835 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B26076593 : Blo 315835 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B3225445829 : Blo 315835 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B714473 : Blo 315835 714473 := bstep (se 2 (by rfl) ⟨267927, by rfl⟩ : syracuseStep 714473 = 535855) B535855
theorem B6842303 : Blo 315835 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B714815 : Blo 315835 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B682139 : Blo 315835 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B1140961 : Blo 315835 1140961 := bstep (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) B855721
theorem B715247 : Blo 315835 715247 := bstep (se 1 (by rfl) ⟨536435, by rfl⟩ : syracuseStep 715247 = 1072871) B1072871
theorem B4090783 : Blo 315835 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B1534967 : Blo 315835 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B2747567 : Blo 315835 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B3108701 : Blo 315835 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B454891 : Blo 315835 454891 := bstep (se 1 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 454891 = 682337) B682337
theorem B3043757 : Blo 315835 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B3437417 : Blo 315835 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B717803 : Blo 315835 717803 := bstep (se 1 (by rfl) ⟨538352, by rfl⟩ : syracuseStep 717803 = 1076705) B1076705
theorem B1373231 : Blo 315835 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B1602827 : Blo 315835 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B1078649 : Blo 315835 1078649 := bstep (se 2 (by rfl) ⟨404493, by rfl⟩ : syracuseStep 1078649 = 808987) B808987
theorem B1603151 : Blo 315835 1603151 := bstep (se 1 (by rfl) ⟨1202363, by rfl⟩ : syracuseStep 1603151 = 2404727) B2404727
theorem B718415 : Blo 315835 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B1210535 : Blo 315835 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B719135 : Blo 315835 719135 := bstep (se 1 (by rfl) ⟨539351, by rfl⟩ : syracuseStep 719135 = 1078703) B1078703
theorem B719207 : Blo 315835 719207 := bstep (se 1 (by rfl) ⟨539405, by rfl⟩ : syracuseStep 719207 = 1078811) B1078811
theorem B358879 : Blo 315835 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B5175845 : Blo 315835 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B359599 : Blo 315835 359599 := bstep (se 1 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 359599 = 539399) B539399
theorem B3605633 : Blo 315835 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B1967723 : Blo 315835 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B1214135 : Blo 315835 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B7178129 : Blo 315835 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B985085 : Blo 315835 985085 := bstep (se 3 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 985085 = 369407) B369407
theorem B2034503 : Blo 315835 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B1444799 : Blo 315835 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B2035961 : Blo 315835 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B1610279 : Blo 315835 1610279 := bstep (se 1 (by rfl) ⟨1207709, by rfl⟩ : syracuseStep 1610279 = 2415419) B2415419
theorem B1708937 : Blo 315835 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B726175 : Blo 315835 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B1709369 : Blo 315835 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B727417 : Blo 315835 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B2333225 : Blo 315835 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B4561535 : Blo 315835 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B1383307 : Blo 315835 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B2956475 : Blo 315835 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1023311 : Blo 315835 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B402671 : Blo 315835 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B8267437 : Blo 315835 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3450563 : Blo 315835 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B535295 : Blo 315835 535295 := bstep (se 1 (by rfl) ⟨401471, by rfl⟩ : syracuseStep 535295 = 802943) B802943
theorem B3058519 : Blo 315835 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B1813661 : Blo 315835 1813661 := bstep (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) B680123
theorem B404671 : Blo 315835 404671 := bstep (se 1 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 404671 = 607007) B607007
theorem B601577 : Blo 315835 601577 := bstep (se 2 (by rfl) ⟨225591, by rfl⟩ : syracuseStep 601577 = 451183) B451183
theorem B536105 : Blo 315835 536105 := bstep (se 2 (by rfl) ⟨201039, by rfl⟩ : syracuseStep 536105 = 402079) B402079
theorem B1519897 : Blo 315835 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B21181027 : Blo 315835 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B17412893 : Blo 315835 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B800027 : Blo 315835 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B4961573 : Blo 315835 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B800239 : Blo 315835 800239 := bstep (se 1 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 800239 = 1200359) B1200359
theorem B1521281 : Blo 315835 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B800543 : Blo 315835 800543 := bstep (se 1 (by rfl) ⟨600407, by rfl⟩ : syracuseStep 800543 = 1200815) B1200815
theorem B538697 : Blo 315835 538697 := bstep (se 2 (by rfl) ⟨202011, by rfl⟩ : syracuseStep 538697 = 404023) B404023
theorem B44546183 : Blo 315835 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B801161 : Blo 315835 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B5454377 : Blo 315835 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B473819 : Blo 315835 473819 := bstep (se 1 (by rfl) ⟨355364, by rfl⟩ : syracuseStep 473819 = 710729) B710729
theorem B1719143 : Blo 315835 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B474107 : Blo 315835 474107 := bstep (se 1 (by rfl) ⟨355580, by rfl⟩ : syracuseStep 474107 = 711161) B711161
theorem B1817761 : Blo 315835 1817761 := bstep (se 2 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 1817761 = 1363321) B1363321
theorem B474971 : Blo 315835 474971 := bstep (se 1 (by rfl) ⟨356228, by rfl⟩ : syracuseStep 474971 = 712457) B712457
theorem B475163 : Blo 315835 475163 := bstep (se 1 (by rfl) ⟨356372, by rfl⟩ : syracuseStep 475163 = 712745) B712745
theorem B606521 : Blo 315835 606521 := bstep (se 2 (by rfl) ⟨227445, by rfl⟩ : syracuseStep 606521 = 454891) B454891
theorem B1819037 : Blo 315835 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B5423759 : Blo 315835 5423759 := bstep (se 1 (by rfl) ⟨4067819, by rfl⟩ : syracuseStep 5423759 = 8135639) B8135639
theorem B17384395 : Blo 315835 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B476315 : Blo 315835 476315 := bstep (se 1 (by rfl) ⟨357236, by rfl⟩ : syracuseStep 476315 = 714473) B714473
theorem B1295585 : Blo 315835 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B476543 : Blo 315835 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B640487 : Blo 315835 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B476831 : Blo 315835 476831 := bstep (se 1 (by rfl) ⟨357623, by rfl⟩ : syracuseStep 476831 = 715247) B715247
theorem B1820951 : Blo 315835 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B641695 : Blo 315835 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B7326845 : Blo 315835 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B478505 : Blo 315835 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B4082993 : Blo 315835 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B478535 : Blo 315835 478535 := bstep (se 1 (by rfl) ⟨358901, by rfl⟩ : syracuseStep 478535 = 717803) B717803
theorem B1068551 : Blo 315835 1068551 := bstep (se 1 (by rfl) ⟨801413, by rfl⟩ : syracuseStep 1068551 = 1602827) B1602827
theorem B2346515 : Blo 315835 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B1068713 : Blo 315835 1068713 := bstep (se 2 (by rfl) ⟨400767, by rfl⟩ : syracuseStep 1068713 = 801535) B801535
theorem B1068767 : Blo 315835 1068767 := bstep (se 1 (by rfl) ⟨801575, by rfl⟩ : syracuseStep 1068767 = 1603151) B1603151
theorem B478943 : Blo 315835 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B970849 : Blo 315835 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B807023 : Blo 315835 807023 := bstep (se 1 (by rfl) ⟨605267, by rfl⟩ : syracuseStep 807023 = 1210535) B1210535
theorem B479423 : Blo 315835 479423 := bstep (se 1 (by rfl) ⟨359567, by rfl⟩ : syracuseStep 479423 = 719135) B719135
theorem B479465 : Blo 315835 479465 := bstep (se 2 (by rfl) ⟨179799, by rfl⟩ : syracuseStep 479465 = 359599) B359599
theorem B479471 : Blo 315835 479471 := bstep (se 1 (by rfl) ⟨359603, by rfl⟩ : syracuseStep 479471 = 719207) B719207
theorem B315871 : Blo 315835 315871 := bstep (se 1 (by rfl) ⟨236903, by rfl⟩ : syracuseStep 315871 = 473807) B473807
theorem B316443 : Blo 315835 316443 := bstep (se 1 (by rfl) ⟨237332, by rfl⟩ : syracuseStep 316443 = 474665) B474665
theorem B317055 : Blo 315835 317055 := bstep (se 1 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 317055 = 475583) B475583
theorem B1070873 : Blo 315835 1070873 := bstep (se 2 (by rfl) ⟨401577, by rfl⟩ : syracuseStep 1070873 = 803155) B803155
theorem B907355 : Blo 315835 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B1071575 : Blo 315835 1071575 := bstep (se 1 (by rfl) ⟨803681, by rfl⟩ : syracuseStep 1071575 = 1607363) B1607363
theorem B711521 : Blo 315835 711521 := bstep (se 2 (by rfl) ⟨266820, by rfl⟩ : syracuseStep 711521 = 533641) B533641
theorem B711791 : Blo 315835 711791 := bstep (se 1 (by rfl) ⟨533843, by rfl⟩ : syracuseStep 711791 = 1067687) B1067687
theorem B2284807 : Blo 315835 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B318875 : Blo 315835 318875 := bstep (se 1 (by rfl) ⟨239156, by rfl⟩ : syracuseStep 318875 = 478313) B478313
theorem B1203943 : Blo 315835 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B1073033 : Blo 315835 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B1531817 : Blo 315835 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B319515 : Blo 315835 319515 := bstep (se 1 (by rfl) ⟨239636, by rfl⟩ : syracuseStep 319515 = 479273) B479273
theorem B3661949 : Blo 315835 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B1106075 : Blo 315835 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B712943 : Blo 315835 712943 := bstep (se 1 (by rfl) ⟨534707, by rfl⟩ : syracuseStep 712943 = 1069415) B1069415
theorem B9265589 : Blo 315835 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B2023967 : Blo 315835 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B1073897 : Blo 315835 1073897 := bstep (se 2 (by rfl) ⟨402711, by rfl⟩ : syracuseStep 1073897 = 805423) B805423
theorem B681319 : Blo 315835 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B484847 : Blo 315835 484847 := bstep (se 1 (by rfl) ⟨363635, by rfl⟩ : syracuseStep 484847 = 727271) B727271
theorem B107865893 : Blo 315835 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B715049 : Blo 315835 715049 := bstep (se 2 (by rfl) ⟨268143, by rfl⟩ : syracuseStep 715049 = 536287) B536287
theorem B1075625 : Blo 315835 1075625 := bstep (se 2 (by rfl) ⟨403359, by rfl⟩ : syracuseStep 1075625 = 806719) B806719
theorem B2419307 : Blo 315835 2419307 := bstep (se 1 (by rfl) ⟨1814480, by rfl⟩ : syracuseStep 2419307 = 3628961) B3628961
theorem B978095 : Blo 315835 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B2150297219 : Blo 315835 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B15494827 : Blo 315835 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B716777 : Blo 315835 716777 := bstep (se 2 (by rfl) ⟨268791, by rfl⟩ : syracuseStep 716777 = 537583) B537583
theorem B356575 : Blo 315835 356575 := bstep (se 1 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 356575 = 534863) B534863
theorem B1012331 : Blo 315835 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B357151 : Blo 315835 357151 := bstep (se 1 (by rfl) ⟨267863, by rfl⟩ : syracuseStep 357151 = 535727) B535727
theorem B2421737 : Blo 315835 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B2029171 : Blo 315835 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B2291611 : Blo 315835 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B1079351 : Blo 315835 1079351 := bstep (se 1 (by rfl) ⟨809513, by rfl⟩ : syracuseStep 1079351 = 1619027) B1619027
theorem B719099 : Blo 315835 719099 := bstep (se 1 (by rfl) ⟨539324, by rfl⟩ : syracuseStep 719099 = 1078649) B1078649
theorem B1604447 : Blo 315835 1604447 := bstep (se 1 (by rfl) ⟨1203335, by rfl⟩ : syracuseStep 1604447 = 2406671) B2406671
theorem B4619105 : Blo 315835 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B1014905 : Blo 315835 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B1211705 : Blo 315835 1211705 := bstep (se 2 (by rfl) ⟨454389, by rfl⟩ : syracuseStep 1211705 = 908779) B908779
theorem B8289869 : Blo 315835 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1212691 : Blo 315835 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B9765197 : Blo 315835 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B2949533 : Blo 315835 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B1311815 : Blo 315835 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B4785419 : Blo 315835 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B656723 : Blo 315835 656723 := bstep (se 1 (by rfl) ⟨492542, by rfl⟩ : syracuseStep 656723 = 985085) B985085
theorem B1213967 : Blo 315835 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B4884563 : Blo 315835 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B2721995 : Blo 315835 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B855593 : Blo 315835 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B1707965 : Blo 315835 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B7377637 : Blo 315835 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B1970983 : Blo 315835 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B1021211 : Blo 315835 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B1349311 : Blo 315835 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B3872933 : Blo 315835 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B2300375 : Blo 315835 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B12164093 : Blo 315835 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B1612871 : Blo 315835 1612871 := bstep (se 1 (by rfl) ⟨1209653, by rfl⟩ : syracuseStep 1612871 = 2419307) B2419307
theorem B401051 : Blo 315835 401051 := bstep (se 1 (by rfl) ⟨300788, by rfl⟩ : syracuseStep 401051 = 601577) B601577
theorem B3055481 : Blo 315835 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B11608595 : Blo 315835 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B1614491 : Blo 315835 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B533351 : Blo 315835 533351 := bstep (se 1 (by rfl) ⟨400013, by rfl⟩ : syracuseStep 533351 = 800027) B800027
theorem B2728829 : Blo 315835 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B533695 : Blo 315835 533695 := bstep (se 1 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 533695 = 800543) B800543
theorem B29697455 : Blo 315835 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B534107 : Blo 315835 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B404347 : Blo 315835 404347 := bstep (se 1 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 404347 = 606521) B606521
theorem B3615839 : Blo 315835 3615839 := bstep (se 1 (by rfl) ⟨2711879, by rfl⟩ : syracuseStep 3615839 = 5423759) B5423759
theorem B2403755 : Blo 315835 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B863723 : Blo 315835 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B23179193 : Blo 315835 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B1356335 : Blo 315835 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B963199 : Blo 315835 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B538015 : Blo 315835 538015 := bstep (se 1 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 538015 = 807023) B807023
theorem B1357307 : Blo 315835 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B4078025 : Blo 315835 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B604903 : Blo 315835 604903 := bstep (se 1 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 604903 = 907355) B907355
theorem B539561 : Blo 315835 539561 := bstep (se 2 (by rfl) ⟨202335, by rfl⟩ : syracuseStep 539561 = 404671) B404671
theorem B474347 : Blo 315835 474347 := bstep (se 1 (by rfl) ⟨355760, by rfl⟩ : syracuseStep 474347 = 711521) B711521
theorem B474527 : Blo 315835 474527 := bstep (se 1 (by rfl) ⟨355895, by rfl⟩ : syracuseStep 474527 = 711791) B711791
theorem B20659769 : Blo 315835 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B1294465 : Blo 315835 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B475295 : Blo 315835 475295 := bstep (se 1 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 475295 = 712943) B712943
theorem B6177059 : Blo 315835 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B475433 : Blo 315835 475433 := bstep (se 2 (by rfl) ⟨178287, by rfl⟩ : syracuseStep 475433 = 356575) B356575
theorem B476201 : Blo 315835 476201 := bstep (se 2 (by rfl) ⟨178575, by rfl⟩ : syracuseStep 476201 = 357151) B357151
theorem B71910595 : Blo 315835 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B476699 : Blo 315835 476699 := bstep (se 1 (by rfl) ⟨357524, by rfl⟩ : syracuseStep 476699 = 715049) B715049
theorem B1066985 : Blo 315835 1066985 := bstep (se 2 (by rfl) ⟨400119, by rfl⟩ : syracuseStep 1066985 = 800239) B800239
theorem B2705561 : Blo 315835 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B477851 : Blo 315835 477851 := bstep (se 1 (by rfl) ⟨358388, by rfl⟩ : syracuseStep 477851 = 716777) B716777
theorem B674887 : Blo 315835 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B969889 : Blo 315835 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B44092997 : Blo 315835 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B479399 : Blo 315835 479399 := bstep (se 1 (by rfl) ⟨359549, by rfl⟩ : syracuseStep 479399 = 719099) B719099
theorem B22106317 : Blo 315835 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B5734125917 : Blo 315835 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B315879 : Blo 315835 315879 := bstep (se 1 (by rfl) ⟨236909, by rfl⟩ : syracuseStep 315879 = 473819) B473819
theorem B1069631 : Blo 315835 1069631 := bstep (se 1 (by rfl) ⟨802223, by rfl⟩ : syracuseStep 1069631 = 1604447) B1604447
theorem B316071 : Blo 315835 316071 := bstep (se 1 (by rfl) ⟨237053, by rfl⟩ : syracuseStep 316071 = 474107) B474107
theorem B676603 : Blo 315835 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B807803 : Blo 315835 807803 := bstep (se 1 (by rfl) ⟨605852, by rfl⟩ : syracuseStep 807803 = 1211705) B1211705
theorem B316647 : Blo 315835 316647 := bstep (se 1 (by rfl) ⟨237485, by rfl⟩ : syracuseStep 316647 = 474971) B474971
theorem B316775 : Blo 315835 316775 := bstep (se 1 (by rfl) ⟨237581, by rfl⟩ : syracuseStep 316775 = 475163) B475163
theorem B317543 : Blo 315835 317543 := bstep (se 1 (by rfl) ⟨238157, by rfl⟩ : syracuseStep 317543 = 476315) B476315
theorem B317695 : Blo 315835 317695 := bstep (se 1 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 317695 = 476543) B476543
theorem B317887 : Blo 315835 317887 := bstep (se 1 (by rfl) ⟨238415, by rfl⟩ : syracuseStep 317887 = 476831) B476831
theorem B809423 : Blo 315835 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B908425 : Blo 315835 908425 := bstep (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) B681319
theorem B319003 : Blo 315835 319003 := bstep (se 1 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 319003 = 478505) B478505
theorem B319023 : Blo 315835 319023 := bstep (se 1 (by rfl) ⟨239267, by rfl⟩ : syracuseStep 319023 = 478535) B478535
theorem B712367 : Blo 315835 712367 := bstep (se 1 (by rfl) ⟨534275, by rfl⟩ : syracuseStep 712367 = 1068551) B1068551
theorem B1564343 : Blo 315835 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B712475 : Blo 315835 712475 := bstep (se 1 (by rfl) ⟨534356, by rfl⟩ : syracuseStep 712475 = 1068713) B1068713
theorem B712511 : Blo 315835 712511 := bstep (se 1 (by rfl) ⟨534383, by rfl⟩ : syracuseStep 712511 = 1068767) B1068767
theorem B319295 : Blo 315835 319295 := bstep (se 1 (by rfl) ⟨239471, by rfl⟩ : syracuseStep 319295 = 478943) B478943
theorem B319615 : Blo 315835 319615 := bstep (se 1 (by rfl) ⟨239711, by rfl⟩ : syracuseStep 319615 = 479423) B479423
theorem B319643 : Blo 315835 319643 := bstep (se 1 (by rfl) ⟨239732, by rfl⟩ : syracuseStep 319643 = 479465) B479465
theorem B319647 : Blo 315835 319647 := bstep (se 1 (by rfl) ⟨239735, by rfl⟩ : syracuseStep 319647 = 479471) B479471
theorem B1073519 : Blo 315835 1073519 := bstep (se 1 (by rfl) ⟨805139, by rfl⟩ : syracuseStep 1073519 = 1610279) B1610279
theorem B1139291 : Blo 315835 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B1073789 : Blo 315835 1073789 := bstep (se 3 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 1073789 = 402671) B402671
theorem B1139579 : Blo 315835 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B713915 : Blo 315835 713915 := bstep (se 1 (by rfl) ⟨535436, by rfl⟩ : syracuseStep 713915 = 1070873) B1070873
theorem B714383 : Blo 315835 714383 := bstep (se 1 (by rfl) ⟨535787, by rfl⟩ : syracuseStep 714383 = 1071575) B1071575
theorem B4056749 : Blo 315835 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B715355 : Blo 315835 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B2026529 : Blo 315835 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B715931 : Blo 315835 715931 := bstep (se 1 (by rfl) ⟨536948, by rfl⟩ : syracuseStep 715931 = 1073897) B1073897
theorem B28241369 : Blo 315835 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B323231 : Blo 315835 323231 := bstep (se 1 (by rfl) ⟨242423, by rfl⟩ : syracuseStep 323231 = 484847) B484847
theorem B6221933 : Blo 315835 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B717083 : Blo 315835 717083 := bstep (se 1 (by rfl) ⟨537812, by rfl⟩ : syracuseStep 717083 = 1075625) B1075625
theorem B356863 : Blo 315835 356863 := bstep (se 1 (by rfl) ⟨267647, by rfl⟩ : syracuseStep 356863 = 535295) B535295
theorem B1209107 : Blo 315835 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B652063 : Blo 315835 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B357403 : Blo 315835 357403 := bstep (se 1 (by rfl) ⟨268052, by rfl⟩ : syracuseStep 357403 = 536105) B536105
theorem B3307715 : Blo 315835 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B719567 : Blo 315835 719567 := bstep (se 1 (by rfl) ⟨539675, by rfl⟩ : syracuseStep 719567 = 1079351) B1079351
theorem B359131 : Blo 315835 359131 := bstep (se 1 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 359131 = 538697) B538697
theorem B2423681 : Blo 315835 2423681 := bstep (se 2 (by rfl) ⟨908880, by rfl⟩ : syracuseStep 2423681 = 1817761) B1817761
theorem B3046409 : Blo 315835 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B3636251 : Blo 315835 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B3079403 : Blo 315835 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B1146095 : Blo 315835 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B1605257 : Blo 315835 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B1966355 : Blo 315835 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B1803707 : Blo 315835 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B29395331 : Blo 315835 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B3822750611 : Blo 315835 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B3608549 : Blo 315835 3608549 := bstep (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) B676603
theorem B2036987 : Blo 315835 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B7739063 : Blo 315835 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B759527 : Blo 315835 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B759719 : Blo 315835 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B1284265 : Blo 315835 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B9836849 : Blo 315835 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B383523173 : Blo 315835 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B2627977 : Blo 315835 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B1351019 : Blo 315835 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B2303261 : Blo 315835 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B2205143 : Blo 315835 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B861949 : Blo 315835 861949 := bstep (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) B323231
theorem B1615787 : Blo 315835 1615787 := bstep (se 1 (by rfl) ⟨1211840, by rfl⟩ : syracuseStep 1615787 = 2423681) B2423681
theorem B764063 : Blo 315835 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B13773179 : Blo 315835 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B1616921 : Blo 315835 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B3190279 : Blo 315835 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B437815 : Blo 315835 437815 := bstep (se 1 (by rfl) ⟨328361, by rfl⟩ : syracuseStep 437815 = 656723) B656723
theorem B3256375 : Blo 315835 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1814663 : Blo 315835 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B570395 : Blo 315835 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B538535 : Blo 315835 538535 := bstep (se 1 (by rfl) ⟨403901, by rfl⟩ : syracuseStep 538535 = 807803) B807803
theorem B539129 : Blo 315835 539129 := bstep (se 2 (by rfl) ⟨202173, by rfl⟩ : syracuseStep 539129 = 404347) B404347
theorem B899849 : Blo 315835 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B1293185 : Blo 315835 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B539615 : Blo 315835 539615 := bstep (se 1 (by rfl) ⟨404711, by rfl⟩ : syracuseStep 539615 = 809423) B809423
theorem B8109395 : Blo 315835 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B474911 : Blo 315835 474911 := bstep (se 1 (by rfl) ⟨356183, by rfl⟩ : syracuseStep 474911 = 712367) B712367
theorem B474983 : Blo 315835 474983 := bstep (se 1 (by rfl) ⟨356237, by rfl⟩ : syracuseStep 474983 = 712475) B712475
theorem B475007 : Blo 315835 475007 := bstep (se 1 (by rfl) ⟨356255, by rfl⟩ : syracuseStep 475007 = 712511) B712511
theorem B29475089 : Blo 315835 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B1819219 : Blo 315835 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B475817 : Blo 315835 475817 := bstep (se 2 (by rfl) ⟨178431, by rfl⟩ : syracuseStep 475817 = 356863) B356863
theorem B475943 : Blo 315835 475943 := bstep (se 1 (by rfl) ⟨356957, by rfl⟩ : syracuseStep 475943 = 713915) B713915
theorem B869417 : Blo 315835 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B476255 : Blo 315835 476255 := bstep (se 1 (by rfl) ⟨357191, by rfl⟩ : syracuseStep 476255 = 714383) B714383
theorem B2704499 : Blo 315835 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B476537 : Blo 315835 476537 := bstep (se 2 (by rfl) ⟨178701, by rfl⟩ : syracuseStep 476537 = 357403) B357403
theorem B476903 : Blo 315835 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B2410559 : Blo 315835 2410559 := bstep (se 1 (by rfl) ⟨1807919, by rfl⟩ : syracuseStep 2410559 = 3615839) B3615839
theorem B477287 : Blo 315835 477287 := bstep (se 1 (by rfl) ⟨357965, by rfl⟩ : syracuseStep 477287 = 715931) B715931
theorem B18827579 : Blo 315835 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B15452795 : Blo 315835 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B4147955 : Blo 315835 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B478055 : Blo 315835 478055 := bstep (se 1 (by rfl) ⟨358541, by rfl⟩ : syracuseStep 478055 = 717083) B717083
theorem B904223 : Blo 315835 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B806071 : Blo 315835 806071 := bstep (se 1 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 806071 = 1209107) B1209107
theorem B478841 : Blo 315835 478841 := bstep (se 2 (by rfl) ⟨179565, by rfl⟩ : syracuseStep 478841 = 359131) B359131
theorem B806537 : Blo 315835 806537 := bstep (se 2 (by rfl) ⟨302451, by rfl⟩ : syracuseStep 806537 = 604903) B604903
theorem B904871 : Blo 315835 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B1069469 : Blo 315835 1069469 := bstep (se 3 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 1069469 = 401051) B401051
theorem B479711 : Blo 315835 479711 := bstep (se 1 (by rfl) ⟨359783, by rfl⟩ : syracuseStep 479711 = 719567) B719567
theorem B2052935 : Blo 315835 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B316231 : Blo 315835 316231 := bstep (se 1 (by rfl) ⟨237173, by rfl⟩ : syracuseStep 316231 = 474347) B474347
theorem B316351 : Blo 315835 316351 := bstep (se 1 (by rfl) ⟨237263, by rfl⟩ : syracuseStep 316351 = 474527) B474527
theorem B1070171 : Blo 315835 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B316863 : Blo 315835 316863 := bstep (se 1 (by rfl) ⟨237647, by rfl⟩ : syracuseStep 316863 = 475295) B475295
theorem B1725953 : Blo 315835 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B4118039 : Blo 315835 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B316955 : Blo 315835 316955 := bstep (se 1 (by rfl) ⟨237716, by rfl⟩ : syracuseStep 316955 = 475433) B475433
theorem B6510131 : Blo 315835 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B317467 : Blo 315835 317467 := bstep (se 1 (by rfl) ⟨238100, by rfl⟩ : syracuseStep 317467 = 476201) B476201
theorem B809311 : Blo 315835 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B317799 : Blo 315835 317799 := bstep (se 1 (by rfl) ⟨238349, by rfl⟩ : syracuseStep 317799 = 476699) B476699
theorem B711323 : Blo 315835 711323 := bstep (se 1 (by rfl) ⟨533492, by rfl⟩ : syracuseStep 711323 = 1066985) B1066985
theorem B711593 : Blo 315835 711593 := bstep (se 2 (by rfl) ⟨266847, by rfl⟩ : syracuseStep 711593 = 533695) B533695
theorem B318567 : Blo 315835 318567 := bstep (se 1 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 318567 = 477851) B477851
theorem B1138643 : Blo 315835 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B319599 : Blo 315835 319599 := bstep (se 1 (by rfl) ⟨239699, by rfl⟩ : syracuseStep 319599 = 479399) B479399
theorem B3498173 : Blo 315835 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B713087 : Blo 315835 713087 := bstep (se 1 (by rfl) ⟨534815, by rfl⟩ : syracuseStep 713087 = 1069631) B1069631
theorem B680807 : Blo 315835 680807 := bstep (se 1 (by rfl) ⟨510605, by rfl⟩ : syracuseStep 680807 = 1021211) B1021211
theorem B79193213 : Blo 315835 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B2581955 : Blo 315835 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B1533583 : Blo 315835 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B1075247 : Blo 315835 1075247 := bstep (se 1 (by rfl) ⟨806435, by rfl⟩ : syracuseStep 1075247 = 1612871) B1612871
theorem B1042895 : Blo 315835 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B715679 : Blo 315835 715679 := bstep (se 1 (by rfl) ⟨536759, by rfl⟩ : syracuseStep 715679 = 1073519) B1073519
theorem B715859 : Blo 315835 715859 := bstep (se 1 (by rfl) ⟨536894, by rfl⟩ : syracuseStep 715859 = 1073789) B1073789
theorem B1076327 : Blo 315835 1076327 := bstep (se 1 (by rfl) ⟨807245, by rfl⟩ : syracuseStep 1076327 = 1614491) B1614491
theorem B355567 : Blo 315835 355567 := bstep (se 1 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 355567 = 533351) B533351
theorem B356071 : Blo 315835 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B717353 : Blo 315835 717353 := bstep (se 2 (by rfl) ⟨269007, by rfl⟩ : syracuseStep 717353 = 538015) B538015
theorem B1799081 : Blo 315835 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B1602503 : Blo 315835 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B1211233 : Blo 315835 1211233 := bstep (se 2 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 1211233 = 908425) B908425
theorem B2718683 : Blo 315835 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B359707 : Blo 315835 359707 := bstep (se 1 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 359707 = 539561) B539561
theorem B2030939 : Blo 315835 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B2424167 : Blo 315835 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B1310903 : Blo 315835 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1802999 : Blo 315835 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B2425625 : Blo 315835 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B1607039 : Blo 315835 1607039 := bstep (se 1 (by rfl) ⟨1205279, by rfl⟩ : syracuseStep 1607039 = 2410559) B2410559
theorem B19596887 : Blo 315835 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B2548500407 : Blo 315835 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1149265 : Blo 315835 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B759095 : Blo 315835 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B2332115 : Blo 315835 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B52795475 : Blo 315835 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B50206877 : Blo 315835 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B9182119 : Blo 315835 9182119 := bstep (se 1 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 9182119 = 13773179) B13773179
theorem B1712353 : Blo 315835 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B1614977 : Blo 315835 1614977 := bstep (se 2 (by rfl) ⟨605616, by rfl⟩ : syracuseStep 1614977 = 1211233) B1211233
theorem B599899 : Blo 315835 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B862123 : Blo 315835 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B1812455 : Blo 315835 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B1353959 : Blo 315835 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B1616111 : Blo 315835 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B10301863 : Blo 315835 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B2765303 : Blo 315835 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B602815 : Blo 315835 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B2044777 : Blo 315835 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B537691 : Blo 315835 537691 := bstep (se 1 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 537691 = 806537) B806537
theorem B2405699 : Blo 315835 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B1357991 : Blo 315835 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B4340087 : Blo 315835 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B5159375 : Blo 315835 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B506351 : Blo 315835 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B506479 : Blo 315835 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B4602541 : Blo 315835 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B474089 : Blo 315835 474089 := bstep (se 2 (by rfl) ⟨177783, by rfl⟩ : syracuseStep 474089 = 355567) B355567
theorem B474215 : Blo 315835 474215 := bstep (se 1 (by rfl) ⟨355661, by rfl⟩ : syracuseStep 474215 = 711323) B711323
theorem B474395 : Blo 315835 474395 := bstep (se 1 (by rfl) ⟨355796, by rfl⟩ : syracuseStep 474395 = 711593) B711593
theorem B474761 : Blo 315835 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B4341833 : Blo 315835 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B475391 : Blo 315835 475391 := bstep (se 1 (by rfl) ⟨356543, by rfl⟩ : syracuseStep 475391 = 713087) B713087
theorem B26231597 : Blo 315835 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1721303 : Blo 315835 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B509375 : Blo 315835 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B477119 : Blo 315835 477119 := bstep (se 1 (by rfl) ⟨357839, by rfl⟩ : syracuseStep 477119 = 715679) B715679
theorem B477239 : Blo 315835 477239 := bstep (se 1 (by rfl) ⟨357929, by rfl⟩ : syracuseStep 477239 = 715859) B715859
theorem B478235 : Blo 315835 478235 := bstep (se 1 (by rfl) ⟨358676, by rfl⟩ : syracuseStep 478235 = 717353) B717353
theorem B1199387 : Blo 315835 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B1068335 : Blo 315835 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B380263 : Blo 315835 380263 := bstep (se 1 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 380263 = 570395) B570395
theorem B479609 : Blo 315835 479609 := bstep (se 2 (by rfl) ⟨179853, by rfl⟩ : syracuseStep 479609 = 359707) B359707
theorem B2412989 : Blo 315835 2412989 := bstep (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) B904871
theorem B316607 : Blo 315835 316607 := bstep (se 1 (by rfl) ⟨237455, by rfl⟩ : syracuseStep 316607 = 474911) B474911
theorem B316655 : Blo 315835 316655 := bstep (se 1 (by rfl) ⟨237491, by rfl⟩ : syracuseStep 316655 = 474983) B474983
theorem B316671 : Blo 315835 316671 := bstep (se 1 (by rfl) ⟨237503, by rfl⟩ : syracuseStep 316671 = 475007) B475007
theorem B19650059 : Blo 315835 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B317211 : Blo 315835 317211 := bstep (se 1 (by rfl) ⟨237908, by rfl⟩ : syracuseStep 317211 = 475817) B475817
theorem B317295 : Blo 315835 317295 := bstep (se 1 (by rfl) ⟨237971, by rfl⟩ : syracuseStep 317295 = 475943) B475943
theorem B579611 : Blo 315835 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B317503 : Blo 315835 317503 := bstep (se 1 (by rfl) ⟨238127, by rfl⟩ : syracuseStep 317503 = 476255) B476255
theorem B317691 : Blo 315835 317691 := bstep (se 1 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 317691 = 476537) B476537
theorem B1202471 : Blo 315835 1202471 := bstep (se 1 (by rfl) ⟨901853, by rfl⟩ : syracuseStep 1202471 = 1803707) B1803707
theorem B317935 : Blo 315835 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B318191 : Blo 315835 318191 := bstep (se 1 (by rfl) ⟨238643, by rfl⟩ : syracuseStep 318191 = 477287) B477287
theorem B318703 : Blo 315835 318703 := bstep (se 1 (by rfl) ⟨239027, by rfl⟩ : syracuseStep 318703 = 478055) B478055
theorem B319227 : Blo 315835 319227 := bstep (se 1 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 319227 = 478841) B478841
theorem B712979 : Blo 315835 712979 := bstep (se 1 (by rfl) ⟨534734, by rfl⟩ : syracuseStep 712979 = 1069469) B1069469
theorem B319807 : Blo 315835 319807 := bstep (se 1 (by rfl) ⟨239855, by rfl⟩ : syracuseStep 319807 = 479711) B479711
theorem B1368623 : Blo 315835 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B713447 : Blo 315835 713447 := bstep (se 1 (by rfl) ⟨535085, by rfl⟩ : syracuseStep 713447 = 1070171) B1070171
theorem B2745359 : Blo 315835 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B255682115 : Blo 315835 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B1074761 : Blo 315835 1074761 := bstep (se 2 (by rfl) ⟨403035, by rfl⟩ : syracuseStep 1074761 = 806071) B806071
theorem B4253705 : Blo 315835 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B583753 : Blo 315835 583753 := bstep (se 2 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 583753 = 437815) B437815
theorem B453871 : Blo 315835 453871 := bstep (se 1 (by rfl) ⟨340403, by rfl⟩ : syracuseStep 453871 = 680807) B680807
theorem B1535507 : Blo 315835 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B1470095 : Blo 315835 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B2781053 : Blo 315835 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B1077191 : Blo 315835 1077191 := bstep (se 1 (by rfl) ⟨807893, by rfl⟩ : syracuseStep 1077191 = 1615787) B1615787
theorem B716831 : Blo 315835 716831 := bstep (se 1 (by rfl) ⟨537623, by rfl⟩ : syracuseStep 716831 = 1075247) B1075247
theorem B1077947 : Blo 315835 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B717551 : Blo 315835 717551 := bstep (se 1 (by rfl) ⟨538163, by rfl⟩ : syracuseStep 717551 = 1076327) B1076327
theorem B1209775 : Blo 315835 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B1079081 : Blo 315835 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B3503969 : Blo 315835 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B3602717 : Blo 315835 3602717 := bstep (se 3 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 3602717 = 1351019) B1351019
theorem B359023 : Blo 315835 359023 := bstep (se 1 (by rfl) ⟨269267, by rfl⟩ : syracuseStep 359023 = 538535) B538535
theorem B359419 : Blo 315835 359419 := bstep (se 1 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 359419 = 539129) B539129
theorem B359743 : Blo 315835 359743 := bstep (se 1 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 359743 = 539615) B539615
theorem B5406263 : Blo 315835 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B1147535 : Blo 315835 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B1149497 : Blo 315835 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B1608659 : Blo 315835 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B35196983 : Blo 315835 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B13735817 : Blo 315835 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B2726369 : Blo 315835 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B1350269 : Blo 315835 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B1613033 : Blo 315835 1613033 := bstep (se 2 (by rfl) ⟨604887, by rfl⟩ : syracuseStep 1613033 = 1209775) B1209775
theorem B1023671 : Blo 315835 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B1843535 : Blo 315835 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B6136721 : Blo 315835 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B2335979 : Blo 315835 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B2401811 : Blo 315835 2401811 := bstep (se 1 (by rfl) ⟨1801358, by rfl⟩ : syracuseStep 2401811 = 3602717) B3602717
theorem B2893391 : Blo 315835 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B2894555 : Blo 315835 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B1617083 : Blo 315835 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B1699000271 : Blo 315835 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B799591 : Blo 315835 799591 := bstep (se 1 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 799591 = 1199387) B1199387
theorem B799865 : Blo 315835 799865 := bstep (se 2 (by rfl) ⟨299949, by rfl⟩ : syracuseStep 799865 = 599899) B599899
theorem B506063 : Blo 315835 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B1554743 : Blo 315835 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B1358333 : Blo 315835 1358333 := bstep (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) B509375
theorem B33471251 : Blo 315835 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B801647 : Blo 315835 801647 := bstep (se 1 (by rfl) ⟨601235, by rfl⟩ : syracuseStep 801647 = 1202471) B1202471
theorem B605161 : Blo 315835 605161 := bstep (se 2 (by rfl) ⟨226935, by rfl⟩ : syracuseStep 605161 = 453871) B453871
theorem B507017 : Blo 315835 507017 := bstep (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) B380263
theorem B475319 : Blo 315835 475319 := bstep (se 1 (by rfl) ⟨356489, by rfl⟩ : syracuseStep 475319 = 712979) B712979
theorem B475631 : Blo 315835 475631 := bstep (se 1 (by rfl) ⟨356723, by rfl⟩ : syracuseStep 475631 = 713447) B713447
theorem B803753 : Blo 315835 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B2835803 : Blo 315835 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B902639 : Blo 315835 902639 := bstep (se 1 (by rfl) ⟨676979, by rfl⟩ : syracuseStep 902639 = 1353959) B1353959
theorem B1854035 : Blo 315835 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B477887 : Blo 315835 477887 := bstep (se 1 (by rfl) ⟨358415, by rfl⟩ : syracuseStep 477887 = 716831) B716831
theorem B478367 : Blo 315835 478367 := bstep (se 1 (by rfl) ⟨358775, by rfl⟩ : syracuseStep 478367 = 717551) B717551
theorem B675305 : Blo 315835 675305 := bstep (se 2 (by rfl) ⟨253239, by rfl⟩ : syracuseStep 675305 = 506479) B506479
theorem B478697 : Blo 315835 478697 := bstep (se 2 (by rfl) ⟨179511, by rfl⟩ : syracuseStep 478697 = 359023) B359023
theorem B12242825 : Blo 315835 12242825 := bstep (se 2 (by rfl) ⟨4591059, by rfl⟩ : syracuseStep 12242825 = 9182119) B9182119
theorem B479225 : Blo 315835 479225 := bstep (se 2 (by rfl) ⟨179709, by rfl⟩ : syracuseStep 479225 = 359419) B359419
theorem B905327 : Blo 315835 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B479657 : Blo 315835 479657 := bstep (se 2 (by rfl) ⟨179871, by rfl⟩ : syracuseStep 479657 = 359743) B359743
theorem B316059 : Blo 315835 316059 := bstep (se 1 (by rfl) ⟨237044, by rfl⟩ : syracuseStep 316059 = 474089) B474089
theorem B316143 : Blo 315835 316143 := bstep (se 1 (by rfl) ⟨237107, by rfl⟩ : syracuseStep 316143 = 474215) B474215
theorem B316263 : Blo 315835 316263 := bstep (se 1 (by rfl) ⟨237197, by rfl⟩ : syracuseStep 316263 = 474395) B474395
theorem B316507 : Blo 315835 316507 := bstep (se 1 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 316507 = 474761) B474761
theorem B873935 : Blo 315835 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B316927 : Blo 315835 316927 := bstep (se 1 (by rfl) ⟨237695, by rfl⟩ : syracuseStep 316927 = 475391) B475391
theorem B2283137 : Blo 315835 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B1201999 : Blo 315835 1201999 := bstep (se 1 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 1201999 = 1802999) B1802999
theorem B17487731 : Blo 315835 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1071359 : Blo 315835 1071359 := bstep (se 1 (by rfl) ⟨803519, by rfl⟩ : syracuseStep 1071359 = 1607039) B1607039
theorem B13064591 : Blo 315835 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B318079 : Blo 315835 318079 := bstep (se 1 (by rfl) ⟨238559, by rfl⟩ : syracuseStep 318079 = 477119) B477119
theorem B318159 : Blo 315835 318159 := bstep (se 1 (by rfl) ⟨238619, by rfl⟩ : syracuseStep 318159 = 477239) B477239
theorem B318823 : Blo 315835 318823 := bstep (se 1 (by rfl) ⟨239117, by rfl⟩ : syracuseStep 318823 = 478235) B478235
theorem B712223 : Blo 315835 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B778337 : Blo 315835 778337 := bstep (se 2 (by rfl) ⟨291876, by rfl⟩ : syracuseStep 778337 = 583753) B583753
theorem B319739 : Blo 315835 319739 := bstep (se 1 (by rfl) ⟨239804, by rfl⟩ : syracuseStep 319739 = 479609) B479609
theorem B1532353 : Blo 315835 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B13100039 : Blo 315835 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B386407 : Blo 315835 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B912415 : Blo 315835 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1830239 : Blo 315835 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1076651 : Blo 315835 1076651 := bstep (se 1 (by rfl) ⟨807488, by rfl⟩ : syracuseStep 1076651 = 1614977) B1614977
theorem B170454743 : Blo 315835 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B716507 : Blo 315835 716507 := bstep (se 1 (by rfl) ⟨537380, by rfl⟩ : syracuseStep 716507 = 1074761) B1074761
theorem B1208303 : Blo 315835 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B716921 : Blo 315835 716921 := bstep (se 2 (by rfl) ⟨268845, by rfl⟩ : syracuseStep 716921 = 537691) B537691
theorem B1077407 : Blo 315835 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B980063 : Blo 315835 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B718127 : Blo 315835 718127 := bstep (se 1 (by rfl) ⟨538595, by rfl⟩ : syracuseStep 718127 = 1077191) B1077191
theorem B718631 : Blo 315835 718631 := bstep (se 1 (by rfl) ⟨538973, by rfl⟩ : syracuseStep 718631 = 1077947) B1077947
theorem B1603799 : Blo 315835 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B719387 : Blo 315835 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B3439583 : Blo 315835 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B3604175 : Blo 315835 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B8161883 : Blo 315835 8161883 := bstep (se 1 (by rfl) ⟨6121412, by rfl⟩ : syracuseStep 8161883 = 12242825) B12242825
theorem B23464655 : Blo 315835 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B1216553 : Blo 315835 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B1220159 : Blo 315835 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1132666847 : Blo 315835 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B1352045 : Blo 315835 1352045 := bstep (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) B507017
theorem B533243 : Blo 315835 533243 := bstep (se 1 (by rfl) ⟨399932, by rfl⟩ : syracuseStep 533243 = 799865) B799865
theorem B337375 : Blo 315835 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B534431 : Blo 315835 534431 := bstep (se 1 (by rfl) ⟨400823, by rfl⟩ : syracuseStep 534431 = 801647) B801647
theorem B2402783 : Blo 315835 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B765023 : Blo 315835 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B2043137 : Blo 315835 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B535835 : Blo 315835 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B601759 : Blo 315835 601759 := bstep (se 1 (by rfl) ⟨451319, by rfl⟩ : syracuseStep 601759 = 902639) B902639
theorem B766331 : Blo 315835 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B603551 : Blo 315835 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B1522091 : Blo 315835 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B9157211 : Blo 315835 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B1817579 : Blo 315835 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B900179 : Blo 315835 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B474815 : Blo 315835 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B1229023 : Blo 315835 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B8733359 : Blo 315835 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B1557319 : Blo 315835 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1066121 : Blo 315835 1066121 := bstep (se 2 (by rfl) ⟨399795, by rfl⟩ : syracuseStep 1066121 = 799591) B799591
theorem B7718813 : Blo 315835 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B477671 : Blo 315835 477671 := bstep (se 1 (by rfl) ⟨358253, by rfl⟩ : syracuseStep 477671 = 716507) B716507
theorem B805535 : Blo 315835 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B477947 : Blo 315835 477947 := bstep (se 1 (by rfl) ⟨358460, by rfl⟩ : syracuseStep 477947 = 716921) B716921
theorem B478751 : Blo 315835 478751 := bstep (se 1 (by rfl) ⟨359063, by rfl⟩ : syracuseStep 478751 = 718127) B718127
theorem B479087 : Blo 315835 479087 := bstep (se 1 (by rfl) ⟨359315, by rfl⟩ : syracuseStep 479087 = 718631) B718631
theorem B806881 : Blo 315835 806881 := bstep (se 2 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 806881 = 605161) B605161
theorem B1069199 : Blo 315835 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B1036495 : Blo 315835 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B905555 : Blo 315835 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B479591 : Blo 315835 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B316879 : Blo 315835 316879 := bstep (se 1 (by rfl) ⟨237659, by rfl⟩ : syracuseStep 316879 = 475319) B475319
theorem B317087 : Blo 315835 317087 := bstep (se 1 (by rfl) ⟨237815, by rfl⟩ : syracuseStep 317087 = 475631) B475631
theorem B1890535 : Blo 315835 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1236023 : Blo 315835 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B318591 : Blo 315835 318591 := bstep (se 1 (by rfl) ⟨238943, by rfl⟩ : syracuseStep 318591 = 477887) B477887
theorem B515209 : Blo 315835 515209 := bstep (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) B386407
theorem B1072439 : Blo 315835 1072439 := bstep (se 1 (by rfl) ⟨804329, by rfl⟩ : syracuseStep 1072439 = 1608659) B1608659
theorem B318911 : Blo 315835 318911 := bstep (se 1 (by rfl) ⟨239183, by rfl⟩ : syracuseStep 318911 = 478367) B478367
theorem B450203 : Blo 315835 450203 := bstep (se 1 (by rfl) ⟨337652, by rfl⟩ : syracuseStep 450203 = 675305) B675305
theorem B319131 : Blo 315835 319131 := bstep (se 1 (by rfl) ⟨239348, by rfl⟩ : syracuseStep 319131 = 478697) B478697
theorem B319483 : Blo 315835 319483 := bstep (se 1 (by rfl) ⟨239612, by rfl⟩ : syracuseStep 319483 = 479225) B479225
theorem B319771 : Blo 315835 319771 := bstep (se 1 (by rfl) ⟨239828, by rfl⟩ : syracuseStep 319771 = 479657) B479657
theorem B582623 : Blo 315835 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B11658487 : Blo 315835 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B714239 : Blo 315835 714239 := bstep (se 1 (by rfl) ⟨535679, by rfl⟩ : syracuseStep 714239 = 1071359) B1071359
theorem B8709727 : Blo 315835 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B1075355 : Blo 315835 1075355 := bstep (se 1 (by rfl) ⟨806516, by rfl⟩ : syracuseStep 1075355 = 1613033) B1613033
theorem B682447 : Blo 315835 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B518891 : Blo 315835 518891 := bstep (se 1 (by rfl) ⟨389168, by rfl⟩ : syracuseStep 518891 = 778337) B778337
theorem B4091147 : Blo 315835 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B1601207 : Blo 315835 1601207 := bstep (se 1 (by rfl) ⟨1200905, by rfl⟩ : syracuseStep 1601207 = 2401811) B2401811
theorem B1928927 : Blo 315835 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B1078055 : Blo 315835 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B717767 : Blo 315835 717767 := bstep (se 1 (by rfl) ⟨538325, by rfl⟩ : syracuseStep 717767 = 1076651) B1076651
theorem B1602665 : Blo 315835 1602665 := bstep (se 2 (by rfl) ⟨600999, by rfl⟩ : syracuseStep 1602665 = 1201999) B1201999
theorem B113636495 : Blo 315835 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B718271 : Blo 315835 718271 := bstep (se 1 (by rfl) ⟨538703, by rfl⟩ : syracuseStep 718271 = 1077407) B1077407
theorem B653375 : Blo 315835 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B22314167 : Blo 315835 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B2293055 : Blo 315835 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B3244141 : Blo 315835 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B6554789 : Blo 315835 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B5145875 : Blo 315835 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B5441255 : Blo 315835 5441255 := bstep (se 1 (by rfl) ⟨4080941, by rfl⟩ : syracuseStep 5441255 = 8161883) B8161883
theorem B1609469 : Blo 315835 1609469 := bstep (se 3 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 1609469 = 603551) B603551
theorem B824015 : Blo 315835 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B755111231 : Blo 315835 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B2727431 : Blo 315835 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B1285951 : Blo 315835 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B2040061 : Blo 315835 2040061 := bstep (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) B765023
theorem B435583 : Blo 315835 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B6104807 : Blo 315835 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B600119 : Blo 315835 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B2076425 : Blo 315835 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B15544649 : Blo 315835 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B537023 : Blo 315835 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B15643103 : Blo 315835 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B11612969 : Blo 315835 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B603703 : Blo 315835 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B802345 : Blo 315835 802345 := bstep (se 2 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 802345 = 601759) B601759
theorem B901363 : Blo 315835 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B476159 : Blo 315835 476159 := bstep (se 1 (by rfl) ⟨357119, by rfl⟩ : syracuseStep 476159 = 714239) B714239
theorem B1362091 : Blo 315835 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B1067471 : Blo 315835 1067471 := bstep (se 1 (by rfl) ⟨800603, by rfl⟩ : syracuseStep 1067471 = 1601207) B1601207
theorem B510887 : Blo 315835 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B478511 : Blo 315835 478511 := bstep (se 1 (by rfl) ⟨358883, by rfl⟩ : syracuseStep 478511 = 717767) B717767
theorem B1068443 : Blo 315835 1068443 := bstep (se 1 (by rfl) ⟨801332, by rfl⟩ : syracuseStep 1068443 = 1602665) B1602665
theorem B478847 : Blo 315835 478847 := bstep (se 1 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 478847 = 718271) B718271
theorem B1200541 : Blo 315835 1200541 := bstep (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) B450203
theorem B1528703 : Blo 315835 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B316543 : Blo 315835 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B5822239 : Blo 315835 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B710747 : Blo 315835 710747 := bstep (se 1 (by rfl) ⟨533060, by rfl⟩ : syracuseStep 710747 = 1066121) B1066121
theorem B5527973 : Blo 315835 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B318447 : Blo 315835 318447 := bstep (se 1 (by rfl) ⟨238835, by rfl⟩ : syracuseStep 318447 = 477671) B477671
theorem B318631 : Blo 315835 318631 := bstep (se 1 (by rfl) ⟨238973, by rfl⟩ : syracuseStep 318631 = 477947) B477947
theorem B319167 : Blo 315835 319167 := bstep (se 1 (by rfl) ⟨239375, by rfl⟩ : syracuseStep 319167 = 478751) B478751
theorem B319391 : Blo 315835 319391 := bstep (se 1 (by rfl) ⟨239543, by rfl⟩ : syracuseStep 319391 = 479087) B479087
theorem B712799 : Blo 315835 712799 := bstep (se 1 (by rfl) ⟨534599, by rfl⟩ : syracuseStep 712799 = 1069199) B1069199
theorem B319727 : Blo 315835 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B909929 : Blo 315835 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B714959 : Blo 315835 714959 := bstep (se 1 (by rfl) ⟨536219, by rfl⟩ : syracuseStep 714959 = 1072439) B1072439
theorem B813439 : Blo 315835 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B1075841 : Blo 315835 1075841 := bstep (se 2 (by rfl) ⟨403440, by rfl⟩ : syracuseStep 1075841 = 806881) B806881
theorem B355495 : Blo 315835 355495 := bstep (se 1 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 355495 = 533243) B533243
theorem B388415 : Blo 315835 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B356287 : Blo 315835 356287 := bstep (se 1 (by rfl) ⟨267215, by rfl⟩ : syracuseStep 356287 = 534431) B534431
theorem B716903 : Blo 315835 716903 := bstep (se 1 (by rfl) ⟨537677, by rfl⟩ : syracuseStep 716903 = 1075355) B1075355
theorem B1601855 : Blo 315835 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B357223 : Blo 315835 357223 := bstep (se 1 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 357223 = 535835) B535835
theorem B5534837 : Blo 315835 5534837 := bstep (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) B518891
theorem B1799333 : Blo 315835 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B2520713 : Blo 315835 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B718703 : Blo 315835 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B75757663 : Blo 315835 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B686945 : Blo 315835 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B1014727 : Blo 315835 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B1211719 : Blo 315835 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B14876111 : Blo 315835 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B4325521 : Blo 315835 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B2720081 : Blo 315835 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B41452397 : Blo 315835 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B41714941 : Blo 315835 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B1084585 : Blo 315835 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B1019135 : Blo 315835 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B4069871 : Blo 315835 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B400079 : Blo 315835 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B1384283 : Blo 315835 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B7741979 : Blo 315835 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1680475 : Blo 315835 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B1352969 : Blo 315835 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B1615625 : Blo 315835 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B1714601 : Blo 315835 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B404040869 : Blo 315835 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B4369859 : Blo 315835 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B1816121 : Blo 315835 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B473831 : Blo 315835 473831 := bstep (se 1 (by rfl) ⟨355373, by rfl⟩ : syracuseStep 473831 = 710747) B710747
theorem B473993 : Blo 315835 473993 := bstep (se 2 (by rfl) ⟨177747, by rfl⟩ : syracuseStep 473993 = 355495) B355495
theorem B1818287 : Blo 315835 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B475049 : Blo 315835 475049 := bstep (se 2 (by rfl) ⟨178143, by rfl⟩ : syracuseStep 475049 = 356287) B356287
theorem B475199 : Blo 315835 475199 := bstep (se 1 (by rfl) ⟨356399, by rfl⟩ : syracuseStep 475199 = 712799) B712799
theorem B606619 : Blo 315835 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B476297 : Blo 315835 476297 := bstep (se 2 (by rfl) ⟨178611, by rfl⟩ : syracuseStep 476297 = 357223) B357223
theorem B476639 : Blo 315835 476639 := bstep (se 1 (by rfl) ⟨357479, by rfl⟩ : syracuseStep 476639 = 714959) B714959
theorem B804937 : Blo 315835 804937 := bstep (se 2 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 804937 = 603703) B603703
theorem B1362365 : Blo 315835 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B477935 : Blo 315835 477935 := bstep (se 1 (by rfl) ⟨358451, by rfl⟩ : syracuseStep 477935 = 716903) B716903
theorem B1067903 : Blo 315835 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B3689891 : Blo 315835 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B1199555 : Blo 315835 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B1035773 : Blo 315835 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B479135 : Blo 315835 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B1069793 : Blo 315835 1069793 := bstep (se 2 (by rfl) ⟨401172, by rfl⟩ : syracuseStep 1069793 = 802345) B802345
theorem B9917407 : Blo 315835 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B1201817 : Blo 315835 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B317439 : Blo 315835 317439 := bstep (se 1 (by rfl) ⟨238079, by rfl⟩ : syracuseStep 317439 = 476159) B476159
theorem B3430583 : Blo 315835 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3627503 : Blo 315835 3627503 := bstep (se 1 (by rfl) ⟨2720627, by rfl⟩ : syracuseStep 3627503 = 5441255) B5441255
theorem B711647 : Blo 315835 711647 := bstep (se 1 (by rfl) ⟨533735, by rfl⟩ : syracuseStep 711647 = 1067471) B1067471
theorem B319007 : Blo 315835 319007 := bstep (se 1 (by rfl) ⟨239255, by rfl⟩ : syracuseStep 319007 = 478511) B478511
theorem B712295 : Blo 315835 712295 := bstep (se 1 (by rfl) ⟨534221, by rfl⟩ : syracuseStep 712295 = 1068443) B1068443
theorem B319231 : Blo 315835 319231 := bstep (se 1 (by rfl) ⟨239423, by rfl⟩ : syracuseStep 319231 = 478847) B478847
theorem B1072979 : Blo 315835 1072979 := bstep (se 1 (by rfl) ⟨804734, by rfl⟩ : syracuseStep 1072979 = 1609469) B1609469
theorem B549343 : Blo 315835 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B503407487 : Blo 315835 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B1600721 : Blo 315835 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B14741261 : Blo 315835 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B717227 : Blo 315835 717227 := bstep (se 1 (by rfl) ⟨537920, by rfl⟩ : syracuseStep 717227 = 1075841) B1075841
theorem B2323109 : Blo 315835 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B7762985 : Blo 315835 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B358015 : Blo 315835 358015 := bstep (se 1 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 358015 = 537023) B537023
theorem B457963 : Blo 315835 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B5767361 : Blo 315835 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B2459927 : Blo 315835 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B690515 : Blo 315835 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B1446113 : Blo 315835 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B52892837 : Blo 315835 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B922855 : Blo 315835 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B269360579 : Blo 315835 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B1548739 : Blo 315835 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1813387 : Blo 315835 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B27634931 : Blo 315835 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B2240633 : Blo 315835 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B55619921 : Blo 315835 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B799703 : Blo 315835 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B2929829 : Blo 315835 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B801211 : Blo 315835 801211 := bstep (se 1 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 801211 = 1201817) B1201817
theorem B474431 : Blo 315835 474431 := bstep (se 1 (by rfl) ⟨355823, by rfl⟩ : syracuseStep 474431 = 711647) B711647
theorem B474863 : Blo 315835 474863 := bstep (se 1 (by rfl) ⟨356147, by rfl⟩ : syracuseStep 474863 = 712295) B712295
theorem B5161319 : Blo 315835 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B901979 : Blo 315835 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B2442469 : Blo 315835 2442469 := bstep (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) B457963
theorem B1066877 : Blo 315835 1066877 := bstep (se 3 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 1066877 = 400079) B400079
theorem B1067147 : Blo 315835 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B477353 : Blo 315835 477353 := bstep (se 2 (by rfl) ⟨179007, by rfl⟩ : syracuseStep 477353 = 358015) B358015
theorem B478151 : Blo 315835 478151 := bstep (se 1 (by rfl) ⟨358613, by rfl⟩ : syracuseStep 478151 = 717227) B717227
theorem B315887 : Blo 315835 315887 := bstep (se 1 (by rfl) ⟨236915, by rfl⟩ : syracuseStep 315887 = 473831) B473831
theorem B315995 : Blo 315835 315995 := bstep (se 1 (by rfl) ⟨236996, by rfl⟩ : syracuseStep 315995 = 473993) B473993
theorem B316699 : Blo 315835 316699 := bstep (se 1 (by rfl) ⟨237524, by rfl⟩ : syracuseStep 316699 = 475049) B475049
theorem B316799 : Blo 315835 316799 := bstep (se 1 (by rfl) ⟨237599, by rfl⟩ : syracuseStep 316799 = 475199) B475199
theorem B808825 : Blo 315835 808825 := bstep (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) B606619
theorem B317531 : Blo 315835 317531 := bstep (se 1 (by rfl) ⟨238148, by rfl⟩ : syracuseStep 317531 = 476297) B476297
theorem B317759 : Blo 315835 317759 := bstep (se 1 (by rfl) ⟨238319, by rfl⟩ : syracuseStep 317759 = 476639) B476639
theorem B908243 : Blo 315835 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B318623 : Blo 315835 318623 := bstep (se 1 (by rfl) ⟨238967, by rfl⟩ : syracuseStep 318623 = 477935) B477935
theorem B711935 : Blo 315835 711935 := bstep (se 1 (by rfl) ⟨533951, by rfl⟩ : syracuseStep 711935 = 1067903) B1067903
theorem B679423 : Blo 315835 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B319423 : Blo 315835 319423 := bstep (se 1 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 319423 = 479135) B479135
theorem B1073249 : Blo 315835 1073249 := bstep (se 2 (by rfl) ⟨402468, by rfl⟩ : syracuseStep 1073249 = 804937) B804937
theorem B713195 : Blo 315835 713195 := bstep (se 1 (by rfl) ⟨534896, by rfl⟩ : syracuseStep 713195 = 1069793) B1069793
theorem B2287055 : Blo 315835 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B2713247 : Blo 315835 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2418335 : Blo 315835 2418335 := bstep (se 1 (by rfl) ⟨1813751, by rfl⟩ : syracuseStep 2418335 = 3627503) B3627503
theorem B715319 : Blo 315835 715319 := bstep (se 1 (by rfl) ⟨536489, by rfl⟩ : syracuseStep 715319 = 1072979) B1072979
theorem B335604991 : Blo 315835 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B1077083 : Blo 315835 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B1143067 : Blo 315835 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B2913239 : Blo 315835 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B9827507 : Blo 315835 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B5175323 : Blo 315835 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B1210747 : Blo 315835 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B1212191 : Blo 315835 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B3440879 : Blo 315835 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B460343 : Blo 315835 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B8259941 : Blo 315835 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B35261891 : Blo 315835 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B6098813 : Blo 315835 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B6559805 : Blo 315835 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B1808831 : Blo 315835 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B1612223 : Blo 315835 1612223 := bstep (se 1 (by rfl) ⟨1209167, by rfl⟩ : syracuseStep 1612223 = 2418335) B2418335
theorem B18423287 : Blo 315835 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B1614329 : Blo 315835 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B533135 : Blo 315835 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B1942159 : Blo 315835 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B3450215 : Blo 315835 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B3844907 : Blo 315835 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B5975021 : Blo 315835 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B601319 : Blo 315835 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B3256625 : Blo 315835 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B964075 : Blo 315835 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B7812877 : Blo 315835 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B605495 : Blo 315835 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B474623 : Blo 315835 474623 := bstep (se 1 (by rfl) ⟨355967, by rfl⟩ : syracuseStep 474623 = 711935) B711935
theorem B475463 : Blo 315835 475463 := bstep (se 1 (by rfl) ⟨356597, by rfl⟩ : syracuseStep 475463 = 713195) B713195
theorem B1524089 : Blo 315835 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B1230473 : Blo 315835 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B476879 : Blo 315835 476879 := bstep (se 1 (by rfl) ⟨357659, by rfl⟩ : syracuseStep 476879 = 715319) B715319
theorem B37079947 : Blo 315835 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1068281 : Blo 315835 1068281 := bstep (se 2 (by rfl) ⟨400605, by rfl⟩ : syracuseStep 1068281 = 801211) B801211
theorem B718294877 : Blo 315835 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B905897 : Blo 315835 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B316287 : Blo 315835 316287 := bstep (se 1 (by rfl) ⟨237215, by rfl⟩ : syracuseStep 316287 = 474431) B474431
theorem B316575 : Blo 315835 316575 := bstep (se 1 (by rfl) ⟨237431, by rfl⟩ : syracuseStep 316575 = 474863) B474863
theorem B808127 : Blo 315835 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B711251 : Blo 315835 711251 := bstep (se 1 (by rfl) ⟨533438, by rfl⟩ : syracuseStep 711251 = 1066877) B1066877
theorem B711431 : Blo 315835 711431 := bstep (se 1 (by rfl) ⟨533573, by rfl⟩ : syracuseStep 711431 = 1067147) B1067147
theorem B318235 : Blo 315835 318235 := bstep (se 1 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 318235 = 477353) B477353
theorem B318767 : Blo 315835 318767 := bstep (se 1 (by rfl) ⟨239075, by rfl⟩ : syracuseStep 318767 = 478151) B478151
theorem B26206685 : Blo 315835 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B2417849 : Blo 315835 2417849 := bstep (se 2 (by rfl) ⟨906693, by rfl⟩ : syracuseStep 2417849 = 1813387) B1813387
theorem B447473321 : Blo 315835 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B715499 : Blo 315835 715499 := bstep (se 1 (by rfl) ⟨536624, by rfl⟩ : syracuseStep 715499 = 1073249) B1073249
theorem B1078433 : Blo 315835 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B718055 : Blo 315835 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B2293919 : Blo 315835 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B1016059 : Blo 315835 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B2589545 : Blo 315835 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B820315 : Blo 315835 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B5506627 : Blo 315835 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B4065875 : Blo 315835 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B197759717 : Blo 315835 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B17471123 : Blo 315835 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B1611899 : Blo 315835 1611899 := bstep (se 1 (by rfl) ⟨1208924, by rfl⟩ : syracuseStep 1611899 = 2417849) B2417849
theorem B2563271 : Blo 315835 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B1285433 : Blo 315835 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B400879 : Blo 315835 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B2171083 : Blo 315835 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B1614653 : Blo 315835 1614653 := bstep (se 3 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 1614653 = 605495) B605495
theorem B23507927 : Blo 315835 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B603931 : Blo 315835 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B538751 : Blo 315835 538751 := bstep (se 1 (by rfl) ⟨404063, by rfl⟩ : syracuseStep 538751 = 808127) B808127
theorem B4373203 : Blo 315835 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B1227581 : Blo 315835 1227581 := bstep (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) B460343
theorem B474167 : Blo 315835 474167 := bstep (se 1 (by rfl) ⟨355625, by rfl⟩ : syracuseStep 474167 = 711251) B711251
theorem B474287 : Blo 315835 474287 := bstep (se 1 (by rfl) ⟨355715, by rfl⟩ : syracuseStep 474287 = 711431) B711431
theorem B476999 : Blo 315835 476999 := bstep (se 1 (by rfl) ⟨357749, by rfl⟩ : syracuseStep 476999 = 715499) B715499
theorem B3983347 : Blo 315835 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B478703 : Blo 315835 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B316415 : Blo 315835 316415 := bstep (se 1 (by rfl) ⟨237311, by rfl⟩ : syracuseStep 316415 = 474623) B474623
theorem B316975 : Blo 315835 316975 := bstep (se 1 (by rfl) ⟨237731, by rfl⟩ : syracuseStep 316975 = 475463) B475463
theorem B317919 : Blo 315835 317919 := bstep (se 1 (by rfl) ⟨238439, by rfl⟩ : syracuseStep 317919 = 476879) B476879
theorem B712187 : Blo 315835 712187 := bstep (se 1 (by rfl) ⟨534140, by rfl⟩ : syracuseStep 712187 = 1068281) B1068281
theorem B478863251 : Blo 315835 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B9200573 : Blo 315835 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B1205887 : Blo 315835 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B1074815 : Blo 315835 1074815 := bstep (se 1 (by rfl) ⟨806111, by rfl⟩ : syracuseStep 1074815 = 1612223) B1612223
theorem B12282191 : Blo 315835 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B1076219 : Blo 315835 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B355423 : Blo 315835 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B298315547 : Blo 315835 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B10417169 : Blo 315835 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B718955 : Blo 315835 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B7342169 : Blo 315835 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B1607849 : Blo 315835 1607849 := bstep (se 2 (by rfl) ⟨602943, by rfl⟩ : syracuseStep 1607849 = 1205887) B1205887
theorem B5311129 : Blo 315835 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B1708847 : Blo 315835 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B856955 : Blo 315835 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B6133715 : Blo 315835 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B198877031 : Blo 315835 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B15671951 : Blo 315835 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B534505 : Blo 315835 534505 := bstep (se 2 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 534505 = 400879) B400879
theorem B2894777 : Blo 315835 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B1354745 : Blo 315835 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B1093753 : Blo 315835 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B131839811 : Blo 315835 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B11647415 : Blo 315835 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B473897 : Blo 315835 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B474791 : Blo 315835 474791 := bstep (se 1 (by rfl) ⟨356093, by rfl⟩ : syracuseStep 474791 = 712187) B712187
theorem B319242167 : Blo 315835 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B805241 : Blo 315835 805241 := bstep (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) B603931
theorem B479303 : Blo 315835 479303 := bstep (se 1 (by rfl) ⟨359477, by rfl⟩ : syracuseStep 479303 = 718955) B718955
theorem B316111 : Blo 315835 316111 := bstep (se 1 (by rfl) ⟨237083, by rfl⟩ : syracuseStep 316111 = 474167) B474167
theorem B316191 : Blo 315835 316191 := bstep (se 1 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 316191 = 474287) B474287
theorem B1529279 : Blo 315835 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B1726363 : Blo 315835 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B317999 : Blo 315835 317999 := bstep (se 1 (by rfl) ⟨238499, by rfl⟩ : syracuseStep 317999 = 476999) B476999
theorem B2710583 : Blo 315835 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B319135 : Blo 315835 319135 := bstep (se 1 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 319135 = 478703) B478703
theorem B1074599 : Blo 315835 1074599 := bstep (se 1 (by rfl) ⟨805949, by rfl⟩ : syracuseStep 1074599 = 1611899) B1611899
theorem B1076435 : Blo 315835 1076435 := bstep (se 1 (by rfl) ⟨807326, by rfl⟩ : syracuseStep 1076435 = 1614653) B1614653
theorem B716543 : Blo 315835 716543 := bstep (se 1 (by rfl) ⟨537407, by rfl⟩ : syracuseStep 716543 = 1074815) B1074815
theorem B8188127 : Blo 315835 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B717479 : Blo 315835 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B6944779 : Blo 315835 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B5830937 : Blo 315835 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B359167 : Blo 315835 359167 := bstep (se 1 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 359167 = 538751) B538751
theorem B818387 : Blo 315835 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B7081505 : Blo 315835 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B1019519 : Blo 315835 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B1807055 : Blo 315835 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B132584687 : Blo 315835 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B87893207 : Blo 315835 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B536827 : Blo 315835 536827 := bstep (se 1 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 536827 = 805241) B805241
theorem B571303 : Blo 315835 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B1458337 : Blo 315835 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B19579117 : Blo 315835 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B903163 : Blo 315835 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B477695 : Blo 315835 477695 := bstep (se 1 (by rfl) ⟨358271, by rfl⟩ : syracuseStep 477695 = 716543) B716543
theorem B9259705 : Blo 315835 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B5458751 : Blo 315835 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B478319 : Blo 315835 478319 := bstep (se 1 (by rfl) ⟨358739, by rfl⟩ : syracuseStep 478319 = 717479) B717479
theorem B478889 : Blo 315835 478889 := bstep (se 2 (by rfl) ⟨179583, by rfl⟩ : syracuseStep 478889 = 359167) B359167
theorem B3887291 : Blo 315835 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B315931 : Blo 315835 315931 := bstep (se 1 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 315931 = 473897) B473897
theorem B545591 : Blo 315835 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B316527 : Blo 315835 316527 := bstep (se 1 (by rfl) ⟨237395, by rfl⟩ : syracuseStep 316527 = 474791) B474791
theorem B1071899 : Blo 315835 1071899 := bstep (se 1 (by rfl) ⟨803924, by rfl⟩ : syracuseStep 1071899 = 1607849) B1607849
theorem B712673 : Blo 315835 712673 := bstep (se 2 (by rfl) ⟨267252, by rfl⟩ : syracuseStep 712673 = 534505) B534505
theorem B319535 : Blo 315835 319535 := bstep (se 1 (by rfl) ⟨239651, by rfl⟩ : syracuseStep 319535 = 479303) B479303
theorem B1139231 : Blo 315835 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B4089143 : Blo 315835 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B10447967 : Blo 315835 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B716399 : Blo 315835 716399 := bstep (se 1 (by rfl) ⟨537299, by rfl⟩ : syracuseStep 716399 = 1074599) B1074599
theorem B1929851 : Blo 315835 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B717623 : Blo 315835 717623 := bstep (se 1 (by rfl) ⟨538217, by rfl⟩ : syracuseStep 717623 = 1076435) B1076435
theorem B7764943 : Blo 315835 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B9207269 : Blo 315835 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B212828111 : Blo 315835 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B3639167 : Blo 315835 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B4721003 : Blo 315835 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B2591527 : Blo 315835 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B363727 : Blo 315835 363727 := bstep (se 1 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 363727 = 545591) B545591
theorem B58595471 : Blo 315835 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B2726095 : Blo 315835 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B761737 : Blo 315835 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B1286567 : Blo 315835 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B6138179 : Blo 315835 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B1944449 : Blo 315835 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B88389791 : Blo 315835 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B475115 : Blo 315835 475115 := bstep (se 1 (by rfl) ⟨356336, by rfl⟩ : syracuseStep 475115 = 712673) B712673
theorem B6965311 : Blo 315835 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B477599 : Blo 315835 477599 := bstep (se 1 (by rfl) ⟨358199, by rfl⟩ : syracuseStep 477599 = 716399) B716399
theorem B478415 : Blo 315835 478415 := bstep (se 1 (by rfl) ⟨358811, by rfl⟩ : syracuseStep 478415 = 717623) B717623
theorem B26105489 : Blo 315835 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B3037949 : Blo 315835 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B318463 : Blo 315835 318463 := bstep (se 1 (by rfl) ⟨238847, by rfl⟩ : syracuseStep 318463 = 477695) B477695
theorem B318879 : Blo 315835 318879 := bstep (se 1 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 318879 = 478319) B478319
theorem B679679 : Blo 315835 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B319259 : Blo 315835 319259 := bstep (se 1 (by rfl) ⟨239444, by rfl⟩ : syracuseStep 319259 = 478889) B478889
theorem B1204217 : Blo 315835 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B1204703 : Blo 315835 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B12346273 : Blo 315835 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B714599 : Blo 315835 714599 := bstep (se 1 (by rfl) ⟨535949, by rfl⟩ : syracuseStep 714599 = 1071899) B1071899
theorem B715769 : Blo 315835 715769 := bstep (se 2 (by rfl) ⟨268413, by rfl⟩ : syracuseStep 715769 = 536827) B536827
theorem B10353257 : Blo 315835 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B141885407 : Blo 315835 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B2426111 : Blo 315835 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B3147335 : Blo 315835 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B17403659 : Blo 315835 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B39063647 : Blo 315835 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B857711 : Blo 315835 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B58926527 : Blo 315835 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B9287081 : Blo 315835 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B3455369 : Blo 315835 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B65846789 : Blo 315835 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B802811 : Blo 315835 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B803135 : Blo 315835 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B476399 : Blo 315835 476399 := bstep (se 1 (by rfl) ⟨357299, by rfl⟩ : syracuseStep 476399 = 714599) B714599
theorem B1296299 : Blo 315835 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B477179 : Blo 315835 477179 := bstep (se 1 (by rfl) ⟨357884, by rfl⟩ : syracuseStep 477179 = 715769) B715769
theorem B6902171 : Blo 315835 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B94590271 : Blo 315835 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B316743 : Blo 315835 316743 := bstep (se 1 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 316743 = 475115) B475115
theorem B318399 : Blo 315835 318399 := bstep (se 1 (by rfl) ⟨238799, by rfl⟩ : syracuseStep 318399 = 477599) B477599
theorem B318943 : Blo 315835 318943 := bstep (se 1 (by rfl) ⟨239207, by rfl⟩ : syracuseStep 318943 = 478415) B478415
theorem B484969 : Blo 315835 484969 := bstep (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) B363727
theorem B2025299 : Blo 315835 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B453119 : Blo 315835 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B4092119 : Blo 315835 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B3634793 : Blo 315835 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B1015649 : Blo 315835 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B2098223 : Blo 315835 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B11602439 : Blo 315835 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B1350199 : Blo 315835 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B2728079 : Blo 315835 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B2303579 : Blo 315835 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B535207 : Blo 315835 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B535423 : Blo 315835 535423 := bstep (se 1 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 535423 = 803135) B803135
theorem B1617407 : Blo 315835 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B864199 : Blo 315835 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B4601447 : Blo 315835 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B571807 : Blo 315835 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B43897859 : Blo 315835 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B677099 : Blo 315835 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B317599 : Blo 315835 317599 := bstep (se 1 (by rfl) ⟨238199, by rfl⟩ : syracuseStep 317599 = 476399) B476399
theorem B318119 : Blo 315835 318119 := bstep (se 1 (by rfl) ⟨238589, by rfl⟩ : syracuseStep 318119 = 477179) B477179
theorem B646625 : Blo 315835 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B26042431 : Blo 315835 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B39284351 : Blo 315835 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B1208317 : Blo 315835 1208317 := bstep (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) B453119
theorem B126120361 : Blo 315835 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B6191387 : Blo 315835 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B2423195 : Blo 315835 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B7734959 : Blo 315835 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B1805597 : Blo 315835 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B29265239 : Blo 315835 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B431083 : Blo 315835 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B1152265 : Blo 315835 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B1611089 : Blo 315835 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B26189567 : Blo 315835 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B762409 : Blo 315835 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B1615463 : Blo 315835 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B1818719 : Blo 315835 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B3067631 : Blo 315835 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B34723241 : Blo 315835 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1398815 : Blo 315835 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B713609 : Blo 315835 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B713897 : Blo 315835 713897 := bstep (se 2 (by rfl) ⟨267711, by rfl⟩ : syracuseStep 713897 = 535423) B535423
theorem B168160481 : Blo 315835 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B1535719 : Blo 315835 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B1078271 : Blo 315835 1078271 := bstep (se 1 (by rfl) ⟨808703, by rfl⟩ : syracuseStep 1078271 = 1617407) B1617407
theorem B1800265 : Blo 315835 1800265 := bstep (se 2 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 1800265 = 1350199) B1350199
theorem B4127591 : Blo 315835 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B1212479 : Blo 315835 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B1016545 : Blo 315835 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B112106987 : Blo 315835 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B2400353 : Blo 315835 2400353 := bstep (se 2 (by rfl) ⟨900132, by rfl⟩ : syracuseStep 2400353 = 1800265) B1800265
theorem B5156639 : Blo 315835 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B19510159 : Blo 315835 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B2045087 : Blo 315835 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B23148827 : Blo 315835 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B932543 : Blo 315835 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B2047625 : Blo 315835 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B475739 : Blo 315835 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B475931 : Blo 315835 475931 := bstep (se 1 (by rfl) ⟨356948, by rfl⟩ : syracuseStep 475931 = 713897) B713897
theorem B574777 : Blo 315835 574777 := bstep (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) B431083
theorem B1203731 : Blo 315835 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B1074059 : Blo 315835 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B17459711 : Blo 315835 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B1076975 : Blo 315835 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B1536353 : Blo 315835 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B718847 : Blo 315835 718847 := bstep (se 1 (by rfl) ⟨539135, by rfl⟩ : syracuseStep 718847 = 1078271) B1078271
theorem B2751727 : Blo 315835 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B11639807 : Blo 315835 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B1024235 : Blo 315835 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B1355393 : Blo 315835 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B766369 : Blo 315835 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B802487 : Blo 315835 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B1363391 : Blo 315835 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B479231 : Blo 315835 479231 := bstep (se 1 (by rfl) ⟨359423, by rfl⟩ : syracuseStep 479231 = 718847) B718847
theorem B1365083 : Blo 315835 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B808319 : Blo 315835 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B317159 : Blo 315835 317159 := bstep (se 1 (by rfl) ⟨237869, by rfl⟩ : syracuseStep 317159 = 475739) B475739
theorem B317287 : Blo 315835 317287 := bstep (se 1 (by rfl) ⟨237965, by rfl⟩ : syracuseStep 317287 = 475931) B475931
theorem B74737991 : Blo 315835 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B1600235 : Blo 315835 1600235 := bstep (se 1 (by rfl) ⟨1200176, by rfl⟩ : syracuseStep 1600235 = 2400353) B2400353
theorem B716039 : Blo 315835 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B26013545 : Blo 315835 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B717983 : Blo 315835 717983 := bstep (se 1 (by rfl) ⟨538487, by rfl⟩ : syracuseStep 717983 = 1076975) B1076975
theorem B3437759 : Blo 315835 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B15432551 : Blo 315835 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B3668969 : Blo 315835 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B621695 : Blo 315835 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B1021825 : Blo 315835 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B17342363 : Blo 315835 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B3614381 : Blo 315835 3614381 := bstep (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) B1355393
theorem B534991 : Blo 315835 534991 := bstep (se 1 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 534991 = 802487) B802487
theorem B538879 : Blo 315835 538879 := bstep (se 1 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 538879 = 808319) B808319
theorem B49825327 : Blo 315835 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B1066823 : Blo 315835 1066823 := bstep (se 1 (by rfl) ⟨800117, by rfl⟩ : syracuseStep 1066823 = 1600235) B1600235
theorem B477359 : Blo 315835 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B478655 : Blo 315835 478655 := bstep (se 1 (by rfl) ⟨358991, by rfl⟩ : syracuseStep 478655 = 717983) B717983
theorem B2445979 : Blo 315835 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B414463 : Blo 315835 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B908927 : Blo 315835 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B319487 : Blo 315835 319487 := bstep (se 1 (by rfl) ⟨239615, by rfl⟩ : syracuseStep 319487 = 479231) B479231
theorem B9167357 : Blo 315835 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B910055 : Blo 315835 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B7759871 : Blo 315835 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B682823 : Blo 315835 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B10288367 : Blo 315835 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B6858911 : Blo 315835 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B66433769 : Blo 315835 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B605951 : Blo 315835 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B6111571 : Blo 315835 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B606703 : Blo 315835 606703 := bstep (se 1 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 606703 = 910055) B910055
theorem B3261305 : Blo 315835 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B2409587 : Blo 315835 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B1362433 : Blo 315835 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B711215 : Blo 315835 711215 := bstep (se 1 (by rfl) ⟨533411, by rfl⟩ : syracuseStep 711215 = 1066823) B1066823
theorem B318239 : Blo 315835 318239 := bstep (se 1 (by rfl) ⟨238679, by rfl⟩ : syracuseStep 318239 = 477359) B477359
theorem B319103 : Blo 315835 319103 := bstep (se 1 (by rfl) ⟨239327, by rfl⟩ : syracuseStep 319103 = 478655) B478655
theorem B713321 : Blo 315835 713321 := bstep (se 2 (by rfl) ⟨267495, by rfl⟩ : syracuseStep 713321 = 534991) B534991
theorem B11561575 : Blo 315835 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B552617 : Blo 315835 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B5173247 : Blo 315835 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B455215 : Blo 315835 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B718505 : Blo 315835 718505 := bstep (se 2 (by rfl) ⟨269439, by rfl⟩ : syracuseStep 718505 = 538879) B538879
theorem B1606391 : Blo 315835 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B368411 : Blo 315835 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B3448831 : Blo 315835 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B403967 : Blo 315835 403967 := bstep (se 1 (by rfl) ⟨302975, by rfl⟩ : syracuseStep 403967 = 605951) B605951
theorem B2174203 : Blo 315835 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B1816577 : Blo 315835 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B15415433 : Blo 315835 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B474143 : Blo 315835 474143 := bstep (se 1 (by rfl) ⟨355607, by rfl⟩ : syracuseStep 474143 = 711215) B711215
theorem B475547 : Blo 315835 475547 := bstep (se 1 (by rfl) ⟨356660, by rfl⟩ : syracuseStep 475547 = 713321) B713321
theorem B606953 : Blo 315835 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B4572607 : Blo 315835 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B44289179 : Blo 315835 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B479003 : Blo 315835 479003 := bstep (se 1 (by rfl) ⟨359252, by rfl⟩ : syracuseStep 479003 = 718505) B718505
theorem B8148761 : Blo 315835 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B808937 : Blo 315835 808937 := bstep (se 2 (by rfl) ⟨303351, by rfl⟩ : syracuseStep 808937 = 606703) B606703
theorem B6096809 : Blo 315835 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B29526119 : Blo 315835 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B4598441 : Blo 315835 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B1618541 : Blo 315835 1618541 := bstep (se 3 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 1618541 = 606953) B606953
theorem B539291 : Blo 315835 539291 := bstep (se 1 (by rfl) ⟨404468, by rfl⟩ : syracuseStep 539291 = 808937) B808937
theorem B2898937 : Blo 315835 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B10276955 : Blo 315835 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B316095 : Blo 315835 316095 := bstep (se 1 (by rfl) ⟨237071, by rfl⟩ : syracuseStep 316095 = 474143) B474143
theorem B317031 : Blo 315835 317031 := bstep (se 1 (by rfl) ⟨237773, by rfl⟩ : syracuseStep 317031 = 475547) B475547
theorem B1070927 : Blo 315835 1070927 := bstep (se 1 (by rfl) ⟨803195, by rfl⟩ : syracuseStep 1070927 = 1606391) B1606391
theorem B319335 : Blo 315835 319335 := bstep (se 1 (by rfl) ⟨239501, by rfl⟩ : syracuseStep 319335 = 479003) B479003
theorem B5432507 : Blo 315835 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B1077245 : Blo 315835 1077245 := bstep (se 3 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 1077245 = 403967) B403967
theorem B3929717 : Blo 315835 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B1211051 : Blo 315835 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B4064539 : Blo 315835 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B6851303 : Blo 315835 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B3621671 : Blo 315835 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B3065627 : Blo 315835 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B807367 : Blo 315835 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B19684079 : Blo 315835 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B713951 : Blo 315835 713951 := bstep (se 1 (by rfl) ⟨535463, by rfl⟩ : syracuseStep 713951 = 1070927) B1070927
theorem B718163 : Blo 315835 718163 := bstep (se 1 (by rfl) ⟨538622, by rfl⟩ : syracuseStep 718163 = 1077245) B1077245
theorem B1079027 : Blo 315835 1079027 := bstep (se 1 (by rfl) ⟨809270, by rfl⟩ : syracuseStep 1079027 = 1618541) B1618541
theorem B2619811 : Blo 315835 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B3865249 : Blo 315835 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B359527 : Blo 315835 359527 := bstep (se 1 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 359527 = 539291) B539291
theorem B5153665 : Blo 315835 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B5419385 : Blo 315835 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B4567535 : Blo 315835 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B13122719 : Blo 315835 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B8175005 : Blo 315835 8175005 := bstep (se 3 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 8175005 = 3065627) B3065627
theorem B475967 : Blo 315835 475967 := bstep (se 1 (by rfl) ⟨356975, by rfl⟩ : syracuseStep 475967 = 713951) B713951
theorem B3493081 : Blo 315835 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B478775 : Blo 315835 478775 := bstep (se 1 (by rfl) ⟨359081, by rfl⟩ : syracuseStep 478775 = 718163) B718163
theorem B479369 : Blo 315835 479369 := bstep (se 2 (by rfl) ⟨179763, by rfl⟩ : syracuseStep 479369 = 359527) B359527
theorem B2414447 : Blo 315835 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B1076489 : Blo 315835 1076489 := bstep (se 2 (by rfl) ⟨403683, by rfl⟩ : syracuseStep 1076489 = 807367) B807367
theorem B719351 : Blo 315835 719351 := bstep (se 1 (by rfl) ⟨539513, by rfl⟩ : syracuseStep 719351 = 1079027) B1079027
theorem B1609631 : Blo 315835 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B4657441 : Blo 315835 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B3612923 : Blo 315835 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B5450003 : Blo 315835 5450003 := bstep (se 1 (by rfl) ⟨4087502, by rfl⟩ : syracuseStep 5450003 = 8175005) B8175005
theorem B479567 : Blo 315835 479567 := bstep (se 1 (by rfl) ⟨359675, by rfl⟩ : syracuseStep 479567 = 719351) B719351
theorem B317311 : Blo 315835 317311 := bstep (se 1 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 317311 = 475967) B475967
theorem B6871553 : Blo 315835 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B319183 : Blo 315835 319183 := bstep (se 1 (by rfl) ⟨239387, by rfl⟩ : syracuseStep 319183 = 478775) B478775
theorem B319579 : Blo 315835 319579 := bstep (se 1 (by rfl) ⟨239684, by rfl⟩ : syracuseStep 319579 = 479369) B479369
theorem B717659 : Blo 315835 717659 := bstep (se 1 (by rfl) ⟨538244, by rfl⟩ : syracuseStep 717659 = 1076489) B1076489
theorem B3045023 : Blo 315835 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B8748479 : Blo 315835 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B2408615 : Blo 315835 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B6209921 : Blo 315835 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B478439 : Blo 315835 478439 := bstep (se 1 (by rfl) ⟨358829, by rfl⟩ : syracuseStep 478439 = 717659) B717659
theorem B1073087 : Blo 315835 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B319711 : Blo 315835 319711 := bstep (se 1 (by rfl) ⟨239783, by rfl⟩ : syracuseStep 319711 = 479567) B479567
theorem B4581035 : Blo 315835 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B3633335 : Blo 315835 3633335 := bstep (se 1 (by rfl) ⟨2725001, by rfl⟩ : syracuseStep 3633335 = 5450003) B5450003
theorem B2030015 : Blo 315835 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B5832319 : Blo 315835 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B1605743 : Blo 315835 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B3054023 : Blo 315835 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B1353343 : Blo 315835 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B7776425 : Blo 315835 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B4139947 : Blo 315835 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B318959 : Blo 315835 318959 := bstep (se 1 (by rfl) ⟨239219, by rfl⟩ : syracuseStep 318959 = 478439) B478439
theorem B715391 : Blo 315835 715391 := bstep (se 1 (by rfl) ⟨536543, by rfl⟩ : syracuseStep 715391 = 1073087) B1073087
theorem B2422223 : Blo 315835 2422223 := bstep (se 1 (by rfl) ⟨1816667, by rfl⟩ : syracuseStep 2422223 = 3633335) B3633335
theorem B1804457 : Blo 315835 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B2036015 : Blo 315835 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B5184283 : Blo 315835 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B1614815 : Blo 315835 1614815 := bstep (se 1 (by rfl) ⟨1211111, by rfl⟩ : syracuseStep 1614815 = 2422223) B2422223
theorem B5519929 : Blo 315835 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B476927 : Blo 315835 476927 := bstep (se 1 (by rfl) ⟨357695, by rfl⟩ : syracuseStep 476927 = 715391) B715391
theorem B1070495 : Blo 315835 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B1357343 : Blo 315835 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B7359905 : Blo 315835 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B317951 : Blo 315835 317951 := bstep (se 1 (by rfl) ⟨238463, by rfl⟩ : syracuseStep 317951 = 476927) B476927
theorem B1202971 : Blo 315835 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B713663 : Blo 315835 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B1076543 : Blo 315835 1076543 := bstep (se 1 (by rfl) ⟨807407, by rfl⟩ : syracuseStep 1076543 = 1614815) B1614815
theorem B6912377 : Blo 315835 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B475775 : Blo 315835 475775 := bstep (se 1 (by rfl) ⟨356831, by rfl⟩ : syracuseStep 475775 = 713663) B713663
theorem B904895 : Blo 315835 904895 := bstep (se 1 (by rfl) ⟨678671, by rfl⟩ : syracuseStep 904895 = 1357343) B1357343
theorem B4608251 : Blo 315835 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B4906603 : Blo 315835 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B717695 : Blo 315835 717695 := bstep (se 1 (by rfl) ⟨538271, by rfl⟩ : syracuseStep 717695 = 1076543) B1076543
theorem B1603961 : Blo 315835 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B603263 : Blo 315835 603263 := bstep (se 1 (by rfl) ⟨452447, by rfl⟩ : syracuseStep 603263 = 904895) B904895
theorem B478463 : Blo 315835 478463 := bstep (se 1 (by rfl) ⟨358847, by rfl⟩ : syracuseStep 478463 = 717695) B717695
theorem B1069307 : Blo 315835 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B6542137 : Blo 315835 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B317183 : Blo 315835 317183 := bstep (se 1 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 317183 = 475775) B475775
theorem B3072167 : Blo 315835 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B402175 : Blo 315835 402175 := bstep (se 1 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 402175 = 603263) B603263
theorem B2048111 : Blo 315835 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B318975 : Blo 315835 318975 := bstep (se 1 (by rfl) ⟨239231, by rfl⟩ : syracuseStep 318975 = 478463) B478463
theorem B712871 : Blo 315835 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B34891397 : Blo 315835 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B536233 : Blo 315835 536233 := bstep (se 2 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 536233 = 402175) B402175
theorem B475247 : Blo 315835 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B1365407 : Blo 315835 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B23260931 : Blo 315835 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B15507287 : Blo 315835 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B316831 : Blo 315835 316831 := bstep (se 1 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 316831 = 475247) B475247
theorem B910271 : Blo 315835 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B714977 : Blo 315835 714977 := bstep (se 2 (by rfl) ⟨268116, by rfl⟩ : syracuseStep 714977 = 536233) B536233
theorem B10338191 : Blo 315835 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B606847 : Blo 315835 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B476651 : Blo 315835 476651 := bstep (se 1 (by rfl) ⟨357488, by rfl⟩ : syracuseStep 476651 = 714977) B714977
theorem B6892127 : Blo 315835 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B809129 : Blo 315835 809129 := bstep (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) B606847
theorem B317767 : Blo 315835 317767 := bstep (se 1 (by rfl) ⟨238325, by rfl⟩ : syracuseStep 317767 = 476651) B476651
theorem B4594751 : Blo 315835 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B539419 : Blo 315835 539419 := bstep (se 1 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 539419 = 809129) B809129
theorem B3063167 : Blo 315835 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B719225 : Blo 315835 719225 := bstep (se 2 (by rfl) ⟨269709, by rfl⟩ : syracuseStep 719225 = 539419) B539419
theorem B2042111 : Blo 315835 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B479483 : Blo 315835 479483 := bstep (se 1 (by rfl) ⟨359612, by rfl⟩ : syracuseStep 479483 = 719225) B719225
theorem B5445629 : Blo 315835 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B319655 : Blo 315835 319655 := bstep (se 1 (by rfl) ⟨239741, by rfl⟩ : syracuseStep 319655 = 479483) B479483
theorem B3630419 : Blo 315835 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B2420279 : Blo 315835 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B1613519 : Blo 315835 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B1075679 : Blo 315835 1075679 := bstep (se 1 (by rfl) ⟨806759, by rfl⟩ : syracuseStep 1075679 = 1613519) B1613519
theorem B717119 : Blo 315835 717119 := bstep (se 1 (by rfl) ⟨537839, by rfl⟩ : syracuseStep 717119 = 1075679) B1075679
theorem B478079 : Blo 315835 478079 := bstep (se 1 (by rfl) ⟨358559, by rfl⟩ : syracuseStep 478079 = 717119) B717119
theorem B318719 : Blo 315835 318719 := bstep (se 1 (by rfl) ⟨239039, by rfl⟩ : syracuseStep 318719 = 478079) B478079

theorem C0 (j : ℕ) (h1 : 78958 ≤ j) (h2 : j ≤ 79657) : Blo 315835 (4 * j + 3) := by
  interval_cases j
  · exact B315835
  · exact B315839
  · exact B315843
  · exact B315847
  · exact B315851
  · exact B315855
  · exact B315859
  · exact B315863
  · exact B315867
  · exact B315871
  · exact B315875
  · exact B315879
  · exact B315883
  · exact B315887
  · exact B315891
  · exact B315895
  · exact B315899
  · exact B315903
  · exact B315907
  · exact B315911
  · exact B315915
  · exact B315919
  · exact B315923
  · exact B315927
  · exact B315931
  · exact B315935
  · exact B315939
  · exact B315943
  · exact B315947
  · exact B315951
  · exact B315955
  · exact B315959
  · exact B315963
  · exact B315967
  · exact B315971
  · exact B315975
  · exact B315979
  · exact B315983
  · exact B315987
  · exact B315991
  · exact B315995
  · exact B315999
  · exact B316003
  · exact B316007
  · exact B316011
  · exact B316015
  · exact B316019
  · exact B316023
  · exact B316027
  · exact B316031
  · exact B316035
  · exact B316039
  · exact B316043
  · exact B316047
  · exact B316051
  · exact B316055
  · exact B316059
  · exact B316063
  · exact B316067
  · exact B316071
  · exact B316075
  · exact B316079
  · exact B316083
  · exact B316087
  · exact B316091
  · exact B316095
  · exact B316099
  · exact B316103
  · exact B316107
  · exact B316111
  · exact B316115
  · exact B316119
  · exact B316123
  · exact B316127
  · exact B316131
  · exact B316135
  · exact B316139
  · exact B316143
  · exact B316147
  · exact B316151
  · exact B316155
  · exact B316159
  · exact B316163
  · exact B316167
  · exact B316171
  · exact B316175
  · exact B316179
  · exact B316183
  · exact B316187
  · exact B316191
  · exact B316195
  · exact B316199
  · exact B316203
  · exact B316207
  · exact B316211
  · exact B316215
  · exact B316219
  · exact B316223
  · exact B316227
  · exact B316231
  · exact B316235
  · exact B316239
  · exact B316243
  · exact B316247
  · exact B316251
  · exact B316255
  · exact B316259
  · exact B316263
  · exact B316267
  · exact B316271
  · exact B316275
  · exact B316279
  · exact B316283
  · exact B316287
  · exact B316291
  · exact B316295
  · exact B316299
  · exact B316303
  · exact B316307
  · exact B316311
  · exact B316315
  · exact B316319
  · exact B316323
  · exact B316327
  · exact B316331
  · exact B316335
  · exact B316339
  · exact B316343
  · exact B316347
  · exact B316351
  · exact B316355
  · exact B316359
  · exact B316363
  · exact B316367
  · exact B316371
  · exact B316375
  · exact B316379
  · exact B316383
  · exact B316387
  · exact B316391
  · exact B316395
  · exact B316399
  · exact B316403
  · exact B316407
  · exact B316411
  · exact B316415
  · exact B316419
  · exact B316423
  · exact B316427
  · exact B316431
  · exact B316435
  · exact B316439
  · exact B316443
  · exact B316447
  · exact B316451
  · exact B316455
  · exact B316459
  · exact B316463
  · exact B316467
  · exact B316471
  · exact B316475
  · exact B316479
  · exact B316483
  · exact B316487
  · exact B316491
  · exact B316495
  · exact B316499
  · exact B316503
  · exact B316507
  · exact B316511
  · exact B316515
  · exact B316519
  · exact B316523
  · exact B316527
  · exact B316531
  · exact B316535
  · exact B316539
  · exact B316543
  · exact B316547
  · exact B316551
  · exact B316555
  · exact B316559
  · exact B316563
  · exact B316567
  · exact B316571
  · exact B316575
  · exact B316579
  · exact B316583
  · exact B316587
  · exact B316591
  · exact B316595
  · exact B316599
  · exact B316603
  · exact B316607
  · exact B316611
  · exact B316615
  · exact B316619
  · exact B316623
  · exact B316627
  · exact B316631
  · exact B316635
  · exact B316639
  · exact B316643
  · exact B316647
  · exact B316651
  · exact B316655
  · exact B316659
  · exact B316663
  · exact B316667
  · exact B316671
  · exact B316675
  · exact B316679
  · exact B316683
  · exact B316687
  · exact B316691
  · exact B316695
  · exact B316699
  · exact B316703
  · exact B316707
  · exact B316711
  · exact B316715
  · exact B316719
  · exact B316723
  · exact B316727
  · exact B316731
  · exact B316735
  · exact B316739
  · exact B316743
  · exact B316747
  · exact B316751
  · exact B316755
  · exact B316759
  · exact B316763
  · exact B316767
  · exact B316771
  · exact B316775
  · exact B316779
  · exact B316783
  · exact B316787
  · exact B316791
  · exact B316795
  · exact B316799
  · exact B316803
  · exact B316807
  · exact B316811
  · exact B316815
  · exact B316819
  · exact B316823
  · exact B316827
  · exact B316831
  · exact B316835
  · exact B316839
  · exact B316843
  · exact B316847
  · exact B316851
  · exact B316855
  · exact B316859
  · exact B316863
  · exact B316867
  · exact B316871
  · exact B316875
  · exact B316879
  · exact B316883
  · exact B316887
  · exact B316891
  · exact B316895
  · exact B316899
  · exact B316903
  · exact B316907
  · exact B316911
  · exact B316915
  · exact B316919
  · exact B316923
  · exact B316927
  · exact B316931
  · exact B316935
  · exact B316939
  · exact B316943
  · exact B316947
  · exact B316951
  · exact B316955
  · exact B316959
  · exact B316963
  · exact B316967
  · exact B316971
  · exact B316975
  · exact B316979
  · exact B316983
  · exact B316987
  · exact B316991
  · exact B316995
  · exact B316999
  · exact B317003
  · exact B317007
  · exact B317011
  · exact B317015
  · exact B317019
  · exact B317023
  · exact B317027
  · exact B317031
  · exact B317035
  · exact B317039
  · exact B317043
  · exact B317047
  · exact B317051
  · exact B317055
  · exact B317059
  · exact B317063
  · exact B317067
  · exact B317071
  · exact B317075
  · exact B317079
  · exact B317083
  · exact B317087
  · exact B317091
  · exact B317095
  · exact B317099
  · exact B317103
  · exact B317107
  · exact B317111
  · exact B317115
  · exact B317119
  · exact B317123
  · exact B317127
  · exact B317131
  · exact B317135
  · exact B317139
  · exact B317143
  · exact B317147
  · exact B317151
  · exact B317155
  · exact B317159
  · exact B317163
  · exact B317167
  · exact B317171
  · exact B317175
  · exact B317179
  · exact B317183
  · exact B317187
  · exact B317191
  · exact B317195
  · exact B317199
  · exact B317203
  · exact B317207
  · exact B317211
  · exact B317215
  · exact B317219
  · exact B317223
  · exact B317227
  · exact B317231
  · exact B317235
  · exact B317239
  · exact B317243
  · exact B317247
  · exact B317251
  · exact B317255
  · exact B317259
  · exact B317263
  · exact B317267
  · exact B317271
  · exact B317275
  · exact B317279
  · exact B317283
  · exact B317287
  · exact B317291
  · exact B317295
  · exact B317299
  · exact B317303
  · exact B317307
  · exact B317311
  · exact B317315
  · exact B317319
  · exact B317323
  · exact B317327
  · exact B317331
  · exact B317335
  · exact B317339
  · exact B317343
  · exact B317347
  · exact B317351
  · exact B317355
  · exact B317359
  · exact B317363
  · exact B317367
  · exact B317371
  · exact B317375
  · exact B317379
  · exact B317383
  · exact B317387
  · exact B317391
  · exact B317395
  · exact B317399
  · exact B317403
  · exact B317407
  · exact B317411
  · exact B317415
  · exact B317419
  · exact B317423
  · exact B317427
  · exact B317431
  · exact B317435
  · exact B317439
  · exact B317443
  · exact B317447
  · exact B317451
  · exact B317455
  · exact B317459
  · exact B317463
  · exact B317467
  · exact B317471
  · exact B317475
  · exact B317479
  · exact B317483
  · exact B317487
  · exact B317491
  · exact B317495
  · exact B317499
  · exact B317503
  · exact B317507
  · exact B317511
  · exact B317515
  · exact B317519
  · exact B317523
  · exact B317527
  · exact B317531
  · exact B317535
  · exact B317539
  · exact B317543
  · exact B317547
  · exact B317551
  · exact B317555
  · exact B317559
  · exact B317563
  · exact B317567
  · exact B317571
  · exact B317575
  · exact B317579
  · exact B317583
  · exact B317587
  · exact B317591
  · exact B317595
  · exact B317599
  · exact B317603
  · exact B317607
  · exact B317611
  · exact B317615
  · exact B317619
  · exact B317623
  · exact B317627
  · exact B317631
  · exact B317635
  · exact B317639
  · exact B317643
  · exact B317647
  · exact B317651
  · exact B317655
  · exact B317659
  · exact B317663
  · exact B317667
  · exact B317671
  · exact B317675
  · exact B317679
  · exact B317683
  · exact B317687
  · exact B317691
  · exact B317695
  · exact B317699
  · exact B317703
  · exact B317707
  · exact B317711
  · exact B317715
  · exact B317719
  · exact B317723
  · exact B317727
  · exact B317731
  · exact B317735
  · exact B317739
  · exact B317743
  · exact B317747
  · exact B317751
  · exact B317755
  · exact B317759
  · exact B317763
  · exact B317767
  · exact B317771
  · exact B317775
  · exact B317779
  · exact B317783
  · exact B317787
  · exact B317791
  · exact B317795
  · exact B317799
  · exact B317803
  · exact B317807
  · exact B317811
  · exact B317815
  · exact B317819
  · exact B317823
  · exact B317827
  · exact B317831
  · exact B317835
  · exact B317839
  · exact B317843
  · exact B317847
  · exact B317851
  · exact B317855
  · exact B317859
  · exact B317863
  · exact B317867
  · exact B317871
  · exact B317875
  · exact B317879
  · exact B317883
  · exact B317887
  · exact B317891
  · exact B317895
  · exact B317899
  · exact B317903
  · exact B317907
  · exact B317911
  · exact B317915
  · exact B317919
  · exact B317923
  · exact B317927
  · exact B317931
  · exact B317935
  · exact B317939
  · exact B317943
  · exact B317947
  · exact B317951
  · exact B317955
  · exact B317959
  · exact B317963
  · exact B317967
  · exact B317971
  · exact B317975
  · exact B317979
  · exact B317983
  · exact B317987
  · exact B317991
  · exact B317995
  · exact B317999
  · exact B318003
  · exact B318007
  · exact B318011
  · exact B318015
  · exact B318019
  · exact B318023
  · exact B318027
  · exact B318031
  · exact B318035
  · exact B318039
  · exact B318043
  · exact B318047
  · exact B318051
  · exact B318055
  · exact B318059
  · exact B318063
  · exact B318067
  · exact B318071
  · exact B318075
  · exact B318079
  · exact B318083
  · exact B318087
  · exact B318091
  · exact B318095
  · exact B318099
  · exact B318103
  · exact B318107
  · exact B318111
  · exact B318115
  · exact B318119
  · exact B318123
  · exact B318127
  · exact B318131
  · exact B318135
  · exact B318139
  · exact B318143
  · exact B318147
  · exact B318151
  · exact B318155
  · exact B318159
  · exact B318163
  · exact B318167
  · exact B318171
  · exact B318175
  · exact B318179
  · exact B318183
  · exact B318187
  · exact B318191
  · exact B318195
  · exact B318199
  · exact B318203
  · exact B318207
  · exact B318211
  · exact B318215
  · exact B318219
  · exact B318223
  · exact B318227
  · exact B318231
  · exact B318235
  · exact B318239
  · exact B318243
  · exact B318247
  · exact B318251
  · exact B318255
  · exact B318259
  · exact B318263
  · exact B318267
  · exact B318271
  · exact B318275
  · exact B318279
  · exact B318283
  · exact B318287
  · exact B318291
  · exact B318295
  · exact B318299
  · exact B318303
  · exact B318307
  · exact B318311
  · exact B318315
  · exact B318319
  · exact B318323
  · exact B318327
  · exact B318331
  · exact B318335
  · exact B318339
  · exact B318343
  · exact B318347
  · exact B318351
  · exact B318355
  · exact B318359
  · exact B318363
  · exact B318367
  · exact B318371
  · exact B318375
  · exact B318379
  · exact B318383
  · exact B318387
  · exact B318391
  · exact B318395
  · exact B318399
  · exact B318403
  · exact B318407
  · exact B318411
  · exact B318415
  · exact B318419
  · exact B318423
  · exact B318427
  · exact B318431
  · exact B318435
  · exact B318439
  · exact B318443
  · exact B318447
  · exact B318451
  · exact B318455
  · exact B318459
  · exact B318463
  · exact B318467
  · exact B318471
  · exact B318475
  · exact B318479
  · exact B318483
  · exact B318487
  · exact B318491
  · exact B318495
  · exact B318499
  · exact B318503
  · exact B318507
  · exact B318511
  · exact B318515
  · exact B318519
  · exact B318523
  · exact B318527
  · exact B318531
  · exact B318535
  · exact B318539
  · exact B318543
  · exact B318547
  · exact B318551
  · exact B318555
  · exact B318559
  · exact B318563
  · exact B318567
  · exact B318571
  · exact B318575
  · exact B318579
  · exact B318583
  · exact B318587
  · exact B318591
  · exact B318595
  · exact B318599
  · exact B318603
  · exact B318607
  · exact B318611
  · exact B318615
  · exact B318619
  · exact B318623
  · exact B318627
  · exact B318631

theorem C1 (j : ℕ) (h1 : 79658 ≤ j) (h2 : j ≤ 79958) : Blo 315835 (4 * j + 3) := by
  interval_cases j
  · exact B318635
  · exact B318639
  · exact B318643
  · exact B318647
  · exact B318651
  · exact B318655
  · exact B318659
  · exact B318663
  · exact B318667
  · exact B318671
  · exact B318675
  · exact B318679
  · exact B318683
  · exact B318687
  · exact B318691
  · exact B318695
  · exact B318699
  · exact B318703
  · exact B318707
  · exact B318711
  · exact B318715
  · exact B318719
  · exact B318723
  · exact B318727
  · exact B318731
  · exact B318735
  · exact B318739
  · exact B318743
  · exact B318747
  · exact B318751
  · exact B318755
  · exact B318759
  · exact B318763
  · exact B318767
  · exact B318771
  · exact B318775
  · exact B318779
  · exact B318783
  · exact B318787
  · exact B318791
  · exact B318795
  · exact B318799
  · exact B318803
  · exact B318807
  · exact B318811
  · exact B318815
  · exact B318819
  · exact B318823
  · exact B318827
  · exact B318831
  · exact B318835
  · exact B318839
  · exact B318843
  · exact B318847
  · exact B318851
  · exact B318855
  · exact B318859
  · exact B318863
  · exact B318867
  · exact B318871
  · exact B318875
  · exact B318879
  · exact B318883
  · exact B318887
  · exact B318891
  · exact B318895
  · exact B318899
  · exact B318903
  · exact B318907
  · exact B318911
  · exact B318915
  · exact B318919
  · exact B318923
  · exact B318927
  · exact B318931
  · exact B318935
  · exact B318939
  · exact B318943
  · exact B318947
  · exact B318951
  · exact B318955
  · exact B318959
  · exact B318963
  · exact B318967
  · exact B318971
  · exact B318975
  · exact B318979
  · exact B318983
  · exact B318987
  · exact B318991
  · exact B318995
  · exact B318999
  · exact B319003
  · exact B319007
  · exact B319011
  · exact B319015
  · exact B319019
  · exact B319023
  · exact B319027
  · exact B319031
  · exact B319035
  · exact B319039
  · exact B319043
  · exact B319047
  · exact B319051
  · exact B319055
  · exact B319059
  · exact B319063
  · exact B319067
  · exact B319071
  · exact B319075
  · exact B319079
  · exact B319083
  · exact B319087
  · exact B319091
  · exact B319095
  · exact B319099
  · exact B319103
  · exact B319107
  · exact B319111
  · exact B319115
  · exact B319119
  · exact B319123
  · exact B319127
  · exact B319131
  · exact B319135
  · exact B319139
  · exact B319143
  · exact B319147
  · exact B319151
  · exact B319155
  · exact B319159
  · exact B319163
  · exact B319167
  · exact B319171
  · exact B319175
  · exact B319179
  · exact B319183
  · exact B319187
  · exact B319191
  · exact B319195
  · exact B319199
  · exact B319203
  · exact B319207
  · exact B319211
  · exact B319215
  · exact B319219
  · exact B319223
  · exact B319227
  · exact B319231
  · exact B319235
  · exact B319239
  · exact B319243
  · exact B319247
  · exact B319251
  · exact B319255
  · exact B319259
  · exact B319263
  · exact B319267
  · exact B319271
  · exact B319275
  · exact B319279
  · exact B319283
  · exact B319287
  · exact B319291
  · exact B319295
  · exact B319299
  · exact B319303
  · exact B319307
  · exact B319311
  · exact B319315
  · exact B319319
  · exact B319323
  · exact B319327
  · exact B319331
  · exact B319335
  · exact B319339
  · exact B319343
  · exact B319347
  · exact B319351
  · exact B319355
  · exact B319359
  · exact B319363
  · exact B319367
  · exact B319371
  · exact B319375
  · exact B319379
  · exact B319383
  · exact B319387
  · exact B319391
  · exact B319395
  · exact B319399
  · exact B319403
  · exact B319407
  · exact B319411
  · exact B319415
  · exact B319419
  · exact B319423
  · exact B319427
  · exact B319431
  · exact B319435
  · exact B319439
  · exact B319443
  · exact B319447
  · exact B319451
  · exact B319455
  · exact B319459
  · exact B319463
  · exact B319467
  · exact B319471
  · exact B319475
  · exact B319479
  · exact B319483
  · exact B319487
  · exact B319491
  · exact B319495
  · exact B319499
  · exact B319503
  · exact B319507
  · exact B319511
  · exact B319515
  · exact B319519
  · exact B319523
  · exact B319527
  · exact B319531
  · exact B319535
  · exact B319539
  · exact B319543
  · exact B319547
  · exact B319551
  · exact B319555
  · exact B319559
  · exact B319563
  · exact B319567
  · exact B319571
  · exact B319575
  · exact B319579
  · exact B319583
  · exact B319587
  · exact B319591
  · exact B319595
  · exact B319599
  · exact B319603
  · exact B319607
  · exact B319611
  · exact B319615
  · exact B319619
  · exact B319623
  · exact B319627
  · exact B319631
  · exact B319635
  · exact B319639
  · exact B319643
  · exact B319647
  · exact B319651
  · exact B319655
  · exact B319659
  · exact B319663
  · exact B319667
  · exact B319671
  · exact B319675
  · exact B319679
  · exact B319683
  · exact B319687
  · exact B319691
  · exact B319695
  · exact B319699
  · exact B319703
  · exact B319707
  · exact B319711
  · exact B319715
  · exact B319719
  · exact B319723
  · exact B319727
  · exact B319731
  · exact B319735
  · exact B319739
  · exact B319743
  · exact B319747
  · exact B319751
  · exact B319755
  · exact B319759
  · exact B319763
  · exact B319767
  · exact B319771
  · exact B319775
  · exact B319779
  · exact B319783
  · exact B319787
  · exact B319791
  · exact B319795
  · exact B319799
  · exact B319803
  · exact B319807
  · exact B319811
  · exact B319815
  · exact B319819
  · exact B319823
  · exact B319827
  · exact B319831
  · exact B319835

theorem solution (m : ℕ) (hlo : 315835 ≤ m) (hhi : m ≤ 319835) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 78958 ≤ j := by omega
    have hj2 : j ≤ 79958 := by omega
    have hb : Blo 315835 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 79658 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
