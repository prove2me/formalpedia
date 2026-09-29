-- Prove2me | solution 1 for syracuse_descends_range_1676038_1678038
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:21:44.651717+00:00
-- url     : https://prove2.me/submissions/585b141a-8ee5-48c7-a7c2-14f81c8a2b3f

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


theorem B2514965 : Blo 1676038 2514965 := bbase (se 6 (by rfl) ⟨58944, by rfl⟩ : syracuseStep 2514965 = 117889) (by norm_num)
theorem B2514989 : Blo 1676038 2514989 := bbase (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) (by norm_num)
theorem B6045749 : Blo 1676038 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B2515013 : Blo 1676038 2515013 := bbase (se 4 (by rfl) ⟨235782, by rfl⟩ : syracuseStep 2515013 = 471565) (by norm_num)
theorem B2121805 : Blo 1676038 2121805 := bbase (se 3 (by rfl) ⟨397838, by rfl⟩ : syracuseStep 2121805 = 795677) (by norm_num)
theorem B2015317 : Blo 1676038 2015317 := bbase (se 8 (by rfl) ⟨11808, by rfl⟩ : syracuseStep 2015317 = 23617) (by norm_num)
theorem B4243549 : Blo 1676038 4243549 := bbase (se 3 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 4243549 = 1591331) (by norm_num)
theorem B2515037 : Blo 1676038 2515037 := bbase (se 3 (by rfl) ⟨471569, by rfl⟩ : syracuseStep 2515037 = 943139) (by norm_num)
theorem B2515061 : Blo 1676038 2515061 := bbase (se 5 (by rfl) ⟨117893, by rfl⟩ : syracuseStep 2515061 = 235787) (by norm_num)
theorem B2515085 : Blo 1676038 2515085 := bbase (se 3 (by rfl) ⟨471578, by rfl⟩ : syracuseStep 2515085 = 943157) (by norm_num)
theorem B2015389 : Blo 1676038 2015389 := bbase (se 3 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 2015389 = 755771) (by norm_num)
theorem B2515109 : Blo 1676038 2515109 := bbase (se 4 (by rfl) ⟨235791, by rfl⟩ : syracuseStep 2515109 = 471583) (by norm_num)
theorem B3580085 : Blo 1676038 3580085 := bbase (se 5 (by rfl) ⟨167816, by rfl⟩ : syracuseStep 3580085 = 335633) (by norm_num)
theorem B2515133 : Blo 1676038 2515133 := bbase (se 3 (by rfl) ⟨471587, by rfl⟩ : syracuseStep 2515133 = 943175) (by norm_num)
theorem B4243661 : Blo 1676038 4243661 := bbase (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) (by norm_num)
theorem B2515157 : Blo 1676038 2515157 := bbase (se 7 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 2515157 = 58949) (by norm_num)
theorem B2515181 : Blo 1676038 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B2121977 : Blo 1676038 2121977 := bbase (se 2 (by rfl) ⟨795741, by rfl⟩ : syracuseStep 2121977 = 1591483) (by norm_num)
theorem B2515205 : Blo 1676038 2515205 := bbase (se 4 (by rfl) ⟨235800, by rfl⟩ : syracuseStep 2515205 = 471601) (by norm_num)
theorem B2015509 : Blo 1676038 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B2515229 : Blo 1676038 2515229 := bbase (se 3 (by rfl) ⟨471605, by rfl⟩ : syracuseStep 2515229 = 943211) (by norm_num)
theorem B2122033 : Blo 1676038 2122033 := bbase (se 2 (by rfl) ⟨795762, by rfl⟩ : syracuseStep 2122033 = 1591525) (by norm_num)
theorem B4530485 : Blo 1676038 4530485 := bbase (se 5 (by rfl) ⟨212366, by rfl⟩ : syracuseStep 4530485 = 424733) (by norm_num)
theorem B2515253 : Blo 1676038 2515253 := bbase (se 5 (by rfl) ⟨117902, by rfl⟩ : syracuseStep 2515253 = 235805) (by norm_num)
theorem B5660981 : Blo 1676038 5660981 := bbase (se 5 (by rfl) ⟨265358, by rfl⟩ : syracuseStep 5660981 = 530717) (by norm_num)
theorem B2515277 : Blo 1676038 2515277 := bbase (se 3 (by rfl) ⟨471614, by rfl⟩ : syracuseStep 2515277 = 943229) (by norm_num)
theorem B2515301 : Blo 1676038 2515301 := bbase (se 4 (by rfl) ⟨235809, by rfl⟩ : syracuseStep 2515301 = 471619) (by norm_num)
theorem B2515325 : Blo 1676038 2515325 := bbase (se 3 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 2515325 = 943247) (by norm_num)
theorem B4243853 : Blo 1676038 4243853 := bbase (se 3 (by rfl) ⟨795722, by rfl⟩ : syracuseStep 4243853 = 1591445) (by norm_num)
theorem B2122129 : Blo 1676038 2122129 := bbase (se 2 (by rfl) ⟨795798, by rfl⟩ : syracuseStep 2122129 = 1591597) (by norm_num)
theorem B2515349 : Blo 1676038 2515349 := bbase (se 6 (by rfl) ⟨58953, by rfl⟩ : syracuseStep 2515349 = 117907) (by norm_num)
theorem B3400085 : Blo 1676038 3400085 := bbase (se 6 (by rfl) ⟨79689, by rfl⟩ : syracuseStep 3400085 = 159379) (by norm_num)
theorem B2515373 : Blo 1676038 2515373 := bbase (se 3 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 2515373 = 943265) (by norm_num)
theorem B2515397 : Blo 1676038 2515397 := bbase (se 4 (by rfl) ⟨235818, by rfl⟩ : syracuseStep 2515397 = 471637) (by norm_num)
theorem B2515421 : Blo 1676038 2515421 := bbase (se 3 (by rfl) ⟨471641, by rfl⟩ : syracuseStep 2515421 = 943283) (by norm_num)
theorem B2515445 : Blo 1676038 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B9814517 : Blo 1676038 9814517 := bbase (se 5 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 9814517 = 920111) (by norm_num)
theorem B2515469 : Blo 1676038 2515469 := bbase (se 3 (by rfl) ⟨471650, by rfl⟩ : syracuseStep 2515469 = 943301) (by norm_num)
theorem B2867741 : Blo 1676038 2867741 := bbase (se 3 (by rfl) ⟨537701, by rfl⟩ : syracuseStep 2867741 = 1075403) (by norm_num)
theorem B3580453 : Blo 1676038 3580453 := bbase (se 4 (by rfl) ⟨335667, by rfl⟩ : syracuseStep 3580453 = 671335) (by norm_num)
theorem B2515493 : Blo 1676038 2515493 := bbase (se 4 (by rfl) ⟨235827, by rfl⟩ : syracuseStep 2515493 = 471655) (by norm_num)
theorem B3875381 : Blo 1676038 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B6365749 : Blo 1676038 6365749 := bbase (se 5 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 6365749 = 596789) (by norm_num)
theorem B2122301 : Blo 1676038 2122301 := bbase (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) (by norm_num)
theorem B2515517 : Blo 1676038 2515517 := bbase (se 3 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 2515517 = 943319) (by norm_num)
theorem B2515541 : Blo 1676038 2515541 := bbase (se 8 (by rfl) ⟨14739, by rfl⟩ : syracuseStep 2515541 = 29479) (by norm_num)
theorem B2515565 : Blo 1676038 2515565 := bbase (se 3 (by rfl) ⟨471668, by rfl⟩ : syracuseStep 2515565 = 943337) (by norm_num)
theorem B2122357 : Blo 1676038 2122357 := bbase (se 5 (by rfl) ⟨99485, by rfl⟩ : syracuseStep 2122357 = 198971) (by norm_num)
theorem B2515589 : Blo 1676038 2515589 := bbase (se 4 (by rfl) ⟨235836, by rfl⟩ : syracuseStep 2515589 = 471673) (by norm_num)
theorem B5374613 : Blo 1676038 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2015893 : Blo 1676038 2015893 := bbase (se 6 (by rfl) ⟨47247, by rfl⟩ : syracuseStep 2015893 = 94495) (by norm_num)
theorem B2515613 : Blo 1676038 2515613 := bbase (se 3 (by rfl) ⟨471677, by rfl⟩ : syracuseStep 2515613 = 943355) (by norm_num)
theorem B2515637 : Blo 1676038 2515637 := bbase (se 5 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 2515637 = 235841) (by norm_num)
theorem B2515661 : Blo 1676038 2515661 := bbase (se 3 (by rfl) ⟨471686, by rfl⟩ : syracuseStep 2515661 = 943373) (by norm_num)
theorem B2122453 : Blo 1676038 2122453 := bbase (se 7 (by rfl) ⟨24872, by rfl⟩ : syracuseStep 2122453 = 49745) (by norm_num)
theorem B3023581 : Blo 1676038 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B4244197 : Blo 1676038 4244197 := bbase (se 4 (by rfl) ⟨397893, by rfl⟩ : syracuseStep 4244197 = 795787) (by norm_num)
theorem B2515685 : Blo 1676038 2515685 := bbase (se 4 (by rfl) ⟨235845, by rfl⟩ : syracuseStep 2515685 = 471691) (by norm_num)
theorem B5661413 : Blo 1676038 5661413 := bbase (se 4 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 5661413 = 1061515) (by norm_num)
theorem B2687717 : Blo 1676038 2687717 := bbase (se 4 (by rfl) ⟨251973, by rfl⟩ : syracuseStep 2687717 = 503947) (by norm_num)
theorem B2515709 : Blo 1676038 2515709 := bbase (se 3 (by rfl) ⟨471695, by rfl⟩ : syracuseStep 2515709 = 943391) (by norm_num)
theorem B2515733 : Blo 1676038 2515733 := bbase (se 6 (by rfl) ⟨58962, by rfl⟩ : syracuseStep 2515733 = 117925) (by norm_num)
theorem B2515757 : Blo 1676038 2515757 := bbase (se 3 (by rfl) ⟨471704, by rfl⟩ : syracuseStep 2515757 = 943409) (by norm_num)
theorem B2515781 : Blo 1676038 2515781 := bbase (se 4 (by rfl) ⟨235854, by rfl⟩ : syracuseStep 2515781 = 471709) (by norm_num)
theorem B4244309 : Blo 1676038 4244309 := bbase (se 9 (by rfl) ⟨12434, by rfl⟩ : syracuseStep 4244309 = 24869) (by norm_num)
theorem B9552725 : Blo 1676038 9552725 := bbase (se 9 (by rfl) ⟨27986, by rfl⟩ : syracuseStep 9552725 = 55973) (by norm_num)
theorem B2515805 : Blo 1676038 2515805 := bbase (se 3 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 2515805 = 943427) (by norm_num)
theorem B6366053 : Blo 1676038 6366053 := bbase (se 4 (by rfl) ⟨596817, by rfl⟩ : syracuseStep 6366053 = 1193635) (by norm_num)
theorem B2515829 : Blo 1676038 2515829 := bbase (se 5 (by rfl) ⟨117929, by rfl⟩ : syracuseStep 2515829 = 235859) (by norm_num)
theorem B2122625 : Blo 1676038 2122625 := bbase (se 2 (by rfl) ⟨795984, by rfl⟩ : syracuseStep 2122625 = 1591969) (by norm_num)
theorem B2515853 : Blo 1676038 2515853 := bbase (se 3 (by rfl) ⟨471722, by rfl⟩ : syracuseStep 2515853 = 943445) (by norm_num)
theorem B4776853 : Blo 1676038 4776853 := bbase (se 6 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 4776853 = 223915) (by norm_num)
theorem B2515877 : Blo 1676038 2515877 := bbase (se 4 (by rfl) ⟨235863, by rfl⟩ : syracuseStep 2515877 = 471727) (by norm_num)
theorem B2122681 : Blo 1676038 2122681 := bbase (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) (by norm_num)
theorem B2515901 : Blo 1676038 2515901 := bbase (se 3 (by rfl) ⟨471731, by rfl⟩ : syracuseStep 2515901 = 943463) (by norm_num)
theorem B2515925 : Blo 1676038 2515925 := bbase (se 7 (by rfl) ⟨29483, by rfl⟩ : syracuseStep 2515925 = 58967) (by norm_num)
theorem B2515949 : Blo 1676038 2515949 := bbase (se 3 (by rfl) ⟨471740, by rfl⟩ : syracuseStep 2515949 = 943481) (by norm_num)
theorem B2515973 : Blo 1676038 2515973 := bbase (se 4 (by rfl) ⟨235872, by rfl⟩ : syracuseStep 2515973 = 471745) (by norm_num)
theorem B2155529 : Blo 1676038 2155529 := bbase (se 2 (by rfl) ⟨808323, by rfl⟩ : syracuseStep 2155529 = 1616647) (by norm_num)
theorem B4244501 : Blo 1676038 4244501 := bbase (se 6 (by rfl) ⟨99480, by rfl⟩ : syracuseStep 4244501 = 198961) (by norm_num)
theorem B2122777 : Blo 1676038 2122777 := bbase (se 2 (by rfl) ⟨796041, by rfl⟩ : syracuseStep 2122777 = 1592083) (by norm_num)
theorem B2515997 : Blo 1676038 2515997 := bbase (se 3 (by rfl) ⟨471749, by rfl⟩ : syracuseStep 2515997 = 943499) (by norm_num)
theorem B2548781 : Blo 1676038 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B8487989 : Blo 1676038 8487989 := bbase (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) (by norm_num)
theorem B2516021 : Blo 1676038 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B2516045 : Blo 1676038 2516045 := bbase (se 3 (by rfl) ⟨471758, by rfl⟩ : syracuseStep 2516045 = 943517) (by norm_num)
theorem B17204309 : Blo 1676038 17204309 := bbase (se 8 (by rfl) ⟨100806, by rfl⟩ : syracuseStep 17204309 = 201613) (by norm_num)
theorem B2516069 : Blo 1676038 2516069 := bbase (se 4 (by rfl) ⟨235881, by rfl⟩ : syracuseStep 2516069 = 471763) (by norm_num)
theorem B2516093 : Blo 1676038 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B2516117 : Blo 1676038 2516117 := bbase (se 6 (by rfl) ⟨58971, by rfl⟩ : syracuseStep 2516117 = 117943) (by norm_num)
theorem B5661845 : Blo 1676038 5661845 := bbase (se 6 (by rfl) ⟨132699, by rfl⟩ : syracuseStep 5661845 = 265399) (by norm_num)
theorem B2516141 : Blo 1676038 2516141 := bbase (se 3 (by rfl) ⟨471776, by rfl⟩ : syracuseStep 2516141 = 943553) (by norm_num)
theorem B2122949 : Blo 1676038 2122949 := bbase (se 4 (by rfl) ⟨199026, by rfl⟩ : syracuseStep 2122949 = 398053) (by norm_num)
theorem B2516165 : Blo 1676038 2516165 := bbase (se 4 (by rfl) ⟨235890, by rfl⟩ : syracuseStep 2516165 = 471781) (by norm_num)
theorem B2516189 : Blo 1676038 2516189 := bbase (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) (by norm_num)
theorem B2516213 : Blo 1676038 2516213 := bbase (se 5 (by rfl) ⟨117947, by rfl⟩ : syracuseStep 2516213 = 235895) (by norm_num)
theorem B2123005 : Blo 1676038 2123005 := bbase (se 3 (by rfl) ⟨398063, by rfl⟩ : syracuseStep 2123005 = 796127) (by norm_num)
theorem B2516237 : Blo 1676038 2516237 := bbase (se 3 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 2516237 = 943589) (by norm_num)
theorem B2516261 : Blo 1676038 2516261 := bbase (se 4 (by rfl) ⟨235899, by rfl⟩ : syracuseStep 2516261 = 471799) (by norm_num)
theorem B2516285 : Blo 1676038 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B2516309 : Blo 1676038 2516309 := bbase (se 12 (by rfl) ⟨921, by rfl⟩ : syracuseStep 2516309 = 1843) (by norm_num)
theorem B2123101 : Blo 1676038 2123101 := bbase (se 3 (by rfl) ⟨398081, by rfl⟩ : syracuseStep 2123101 = 796163) (by norm_num)
theorem B1885549 : Blo 1676038 1885549 := bbase (se 3 (by rfl) ⟨353540, by rfl⟩ : syracuseStep 1885549 = 707081) (by norm_num)
theorem B4244845 : Blo 1676038 4244845 := bbase (se 3 (by rfl) ⟨795908, by rfl⟩ : syracuseStep 4244845 = 1591817) (by norm_num)
theorem B2516333 : Blo 1676038 2516333 := bbase (se 3 (by rfl) ⟨471812, by rfl⟩ : syracuseStep 2516333 = 943625) (by norm_num)
theorem B6800773 : Blo 1676038 6800773 := bbase (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) (by norm_num)
theorem B2516357 : Blo 1676038 2516357 := bbase (se 4 (by rfl) ⟨235908, by rfl⟩ : syracuseStep 2516357 = 471817) (by norm_num)
theorem B1885585 : Blo 1676038 1885585 := bbase (se 2 (by rfl) ⟨707094, by rfl⟩ : syracuseStep 1885585 = 1414189) (by norm_num)
theorem B2516381 : Blo 1676038 2516381 := bbase (se 3 (by rfl) ⟨471821, by rfl⟩ : syracuseStep 2516381 = 943643) (by norm_num)
theorem B1885621 : Blo 1676038 1885621 := bbase (se 5 (by rfl) ⟨88388, by rfl⟩ : syracuseStep 1885621 = 176777) (by norm_num)
theorem B2516405 : Blo 1676038 2516405 := bbase (se 5 (by rfl) ⟨117956, by rfl⟩ : syracuseStep 2516405 = 235913) (by norm_num)
theorem B2516429 : Blo 1676038 2516429 := bbase (se 3 (by rfl) ⟨471830, by rfl⟩ : syracuseStep 2516429 = 943661) (by norm_num)
theorem B1885657 : Blo 1676038 1885657 := bbase (se 2 (by rfl) ⟨707121, by rfl⟩ : syracuseStep 1885657 = 1414243) (by norm_num)
theorem B4244957 : Blo 1676038 4244957 := bbase (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) (by norm_num)
theorem B7161317 : Blo 1676038 7161317 := bbase (se 4 (by rfl) ⟨671373, by rfl⟩ : syracuseStep 7161317 = 1342747) (by norm_num)
theorem B2516453 : Blo 1676038 2516453 := bbase (se 4 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 2516453 = 471835) (by norm_num)
theorem B2549237 : Blo 1676038 2549237 := bbase (se 5 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 2549237 = 238991) (by norm_num)
theorem B1885693 : Blo 1676038 1885693 := bbase (se 3 (by rfl) ⟨353567, by rfl⟩ : syracuseStep 1885693 = 707135) (by norm_num)
theorem B2516477 : Blo 1676038 2516477 := bbase (se 3 (by rfl) ⟨471839, by rfl⟩ : syracuseStep 2516477 = 943679) (by norm_num)
theorem B4531717 : Blo 1676038 4531717 := bbase (se 4 (by rfl) ⟨424848, by rfl⟩ : syracuseStep 4531717 = 849697) (by norm_num)
theorem B2123273 : Blo 1676038 2123273 := bbase (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) (by norm_num)
theorem B2516501 : Blo 1676038 2516501 := bbase (se 6 (by rfl) ⟨58980, by rfl⟩ : syracuseStep 2516501 = 117961) (by norm_num)
theorem B1885729 : Blo 1676038 1885729 := bbase (se 2 (by rfl) ⟨707148, by rfl⟩ : syracuseStep 1885729 = 1414297) (by norm_num)
theorem B2516525 : Blo 1676038 2516525 := bbase (se 3 (by rfl) ⟨471848, by rfl⟩ : syracuseStep 2516525 = 943697) (by norm_num)
theorem B2123329 : Blo 1676038 2123329 := bbase (se 2 (by rfl) ⟨796248, by rfl⟩ : syracuseStep 2123329 = 1592497) (by norm_num)
theorem B1885765 : Blo 1676038 1885765 := bbase (se 4 (by rfl) ⟨176790, by rfl⟩ : syracuseStep 1885765 = 353581) (by norm_num)
theorem B4531781 : Blo 1676038 4531781 := bbase (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) (by norm_num)
theorem B2516549 : Blo 1676038 2516549 := bbase (se 4 (by rfl) ⟨235926, by rfl⟩ : syracuseStep 2516549 = 471853) (by norm_num)
theorem B5662277 : Blo 1676038 5662277 := bbase (se 4 (by rfl) ⟨530838, by rfl⟩ : syracuseStep 5662277 = 1061677) (by norm_num)
theorem B2516573 : Blo 1676038 2516573 := bbase (se 3 (by rfl) ⟨471857, by rfl⟩ : syracuseStep 2516573 = 943715) (by norm_num)
theorem B1885801 : Blo 1676038 1885801 := bbase (se 2 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 1885801 = 1414351) (by norm_num)
theorem B2516597 : Blo 1676038 2516597 := bbase (se 5 (by rfl) ⟨117965, by rfl⟩ : syracuseStep 2516597 = 235931) (by norm_num)
theorem B1885837 : Blo 1676038 1885837 := bbase (se 3 (by rfl) ⟨353594, by rfl⟩ : syracuseStep 1885837 = 707189) (by norm_num)
theorem B2516621 : Blo 1676038 2516621 := bbase (se 3 (by rfl) ⟨471866, by rfl⟩ : syracuseStep 2516621 = 943733) (by norm_num)
theorem B4245149 : Blo 1676038 4245149 := bbase (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) (by norm_num)
theorem B2123425 : Blo 1676038 2123425 := bbase (se 2 (by rfl) ⟨796284, by rfl⟩ : syracuseStep 2123425 = 1592569) (by norm_num)
theorem B2516645 : Blo 1676038 2516645 := bbase (se 4 (by rfl) ⟨235935, by rfl⟩ : syracuseStep 2516645 = 471871) (by norm_num)
theorem B1885873 : Blo 1676038 1885873 := bbase (se 2 (by rfl) ⟨707202, by rfl⟩ : syracuseStep 1885873 = 1414405) (by norm_num)
theorem B2516669 : Blo 1676038 2516669 := bbase (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) (by norm_num)
theorem B1885909 : Blo 1676038 1885909 := bbase (se 7 (by rfl) ⟨22100, by rfl⟩ : syracuseStep 1885909 = 44201) (by norm_num)
theorem B2516693 : Blo 1676038 2516693 := bbase (se 7 (by rfl) ⟨29492, by rfl⟩ : syracuseStep 2516693 = 58985) (by norm_num)
theorem B2516717 : Blo 1676038 2516717 := bbase (se 3 (by rfl) ⟨471884, by rfl⟩ : syracuseStep 2516717 = 943769) (by norm_num)
theorem B1885945 : Blo 1676038 1885945 := bbase (se 2 (by rfl) ⟨707229, by rfl⟩ : syracuseStep 1885945 = 1414459) (by norm_num)
theorem B7161605 : Blo 1676038 7161605 := bbase (se 4 (by rfl) ⟨671400, by rfl⟩ : syracuseStep 7161605 = 1342801) (by norm_num)
theorem B2516741 : Blo 1676038 2516741 := bbase (se 4 (by rfl) ⟨235944, by rfl⟩ : syracuseStep 2516741 = 471889) (by norm_num)
theorem B1885981 : Blo 1676038 1885981 := bbase (se 3 (by rfl) ⟨353621, by rfl⟩ : syracuseStep 1885981 = 707243) (by norm_num)
theorem B2516765 : Blo 1676038 2516765 := bbase (se 3 (by rfl) ⟨471893, by rfl⟩ : syracuseStep 2516765 = 943787) (by norm_num)
theorem B2516789 : Blo 1676038 2516789 := bbase (se 5 (by rfl) ⟨117974, by rfl⟩ : syracuseStep 2516789 = 235949) (by norm_num)
theorem B1886017 : Blo 1676038 1886017 := bbase (se 2 (by rfl) ⟨707256, by rfl⟩ : syracuseStep 1886017 = 1414513) (by norm_num)
theorem B2516813 : Blo 1676038 2516813 := bbase (se 3 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 2516813 = 943805) (by norm_num)
theorem B2123597 : Blo 1676038 2123597 := bbase (se 3 (by rfl) ⟨398174, by rfl⟩ : syracuseStep 2123597 = 796349) (by norm_num)
theorem B1886053 : Blo 1676038 1886053 := bbase (se 4 (by rfl) ⟨176817, by rfl⟩ : syracuseStep 1886053 = 353635) (by norm_num)
theorem B2516837 : Blo 1676038 2516837 := bbase (se 4 (by rfl) ⟨235953, by rfl⟩ : syracuseStep 2516837 = 471907) (by norm_num)
theorem B2516861 : Blo 1676038 2516861 := bbase (se 3 (by rfl) ⟨471911, by rfl⟩ : syracuseStep 2516861 = 943823) (by norm_num)
theorem B2123653 : Blo 1676038 2123653 := bbase (se 4 (by rfl) ⟨199092, by rfl⟩ : syracuseStep 2123653 = 398185) (by norm_num)
theorem B1886089 : Blo 1676038 1886089 := bbase (se 2 (by rfl) ⟨707283, by rfl⟩ : syracuseStep 1886089 = 1414567) (by norm_num)
theorem B2516885 : Blo 1676038 2516885 := bbase (se 6 (by rfl) ⟨58989, by rfl⟩ : syracuseStep 2516885 = 117979) (by norm_num)
theorem B1886125 : Blo 1676038 1886125 := bbase (se 3 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 1886125 = 707297) (by norm_num)
theorem B2516909 : Blo 1676038 2516909 := bbase (se 3 (by rfl) ⟨471920, by rfl⟩ : syracuseStep 2516909 = 943841) (by norm_num)
theorem B2516933 : Blo 1676038 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B1886161 : Blo 1676038 1886161 := bbase (se 2 (by rfl) ⟨707310, by rfl⟩ : syracuseStep 1886161 = 1414621) (by norm_num)
theorem B2516957 : Blo 1676038 2516957 := bbase (se 3 (by rfl) ⟨471929, by rfl⟩ : syracuseStep 2516957 = 943859) (by norm_num)
theorem B4777957 : Blo 1676038 4777957 := bbase (se 4 (by rfl) ⟨447933, by rfl⟩ : syracuseStep 4777957 = 895867) (by norm_num)
theorem B2123749 : Blo 1676038 2123749 := bbase (se 4 (by rfl) ⟨199101, by rfl⟩ : syracuseStep 2123749 = 398203) (by norm_num)
theorem B1886197 : Blo 1676038 1886197 := bbase (se 5 (by rfl) ⟨88415, by rfl⟩ : syracuseStep 1886197 = 176831) (by norm_num)
theorem B4245493 : Blo 1676038 4245493 := bbase (se 5 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 4245493 = 398015) (by norm_num)
theorem B9553909 : Blo 1676038 9553909 := bbase (se 5 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 9553909 = 895679) (by norm_num)
theorem B5662709 : Blo 1676038 5662709 := bbase (se 5 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 5662709 = 530879) (by norm_num)
theorem B2516981 : Blo 1676038 2516981 := bbase (se 5 (by rfl) ⟨117983, by rfl⟩ : syracuseStep 2516981 = 235967) (by norm_num)
theorem B3581957 : Blo 1676038 3581957 := bbase (se 4 (by rfl) ⟨335808, by rfl⟩ : syracuseStep 3581957 = 671617) (by norm_num)
theorem B2517005 : Blo 1676038 2517005 := bbase (se 3 (by rfl) ⟨471938, by rfl⟩ : syracuseStep 2517005 = 943877) (by norm_num)
theorem B1886233 : Blo 1676038 1886233 := bbase (se 2 (by rfl) ⟨707337, by rfl⟩ : syracuseStep 1886233 = 1414675) (by norm_num)
theorem B2828317 : Blo 1676038 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B2517029 : Blo 1676038 2517029 := bbase (se 4 (by rfl) ⟨235971, by rfl⟩ : syracuseStep 2517029 = 471943) (by norm_num)
theorem B1886269 : Blo 1676038 1886269 := bbase (se 3 (by rfl) ⟨353675, by rfl⟩ : syracuseStep 1886269 = 707351) (by norm_num)
theorem B2517053 : Blo 1676038 2517053 := bbase (se 3 (by rfl) ⟨471947, by rfl⟩ : syracuseStep 2517053 = 943895) (by norm_num)
theorem B48375893 : Blo 1676038 48375893 := bbase (se 8 (by rfl) ⟨283452, by rfl⟩ : syracuseStep 48375893 = 566905) (by norm_num)
theorem B1886305 : Blo 1676038 1886305 := bbase (se 2 (by rfl) ⟨707364, by rfl⟩ : syracuseStep 1886305 = 1414729) (by norm_num)
theorem B4245605 : Blo 1676038 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2828405 : Blo 1676038 2828405 := bbase (se 5 (by rfl) ⟨132581, by rfl⟩ : syracuseStep 2828405 = 265163) (by norm_num)
theorem B1886341 : Blo 1676038 1886341 := bbase (se 4 (by rfl) ⟨176844, by rfl⟩ : syracuseStep 1886341 = 353689) (by norm_num)
theorem B3582101 : Blo 1676038 3582101 := bbase (se 6 (by rfl) ⟨83955, by rfl⟩ : syracuseStep 3582101 = 167911) (by norm_num)
theorem B1886377 : Blo 1676038 1886377 := bbase (se 2 (by rfl) ⟨707391, by rfl⟩ : syracuseStep 1886377 = 1414783) (by norm_num)
theorem B1886413 : Blo 1676038 1886413 := bbase (se 3 (by rfl) ⟨353702, by rfl⟩ : syracuseStep 1886413 = 707405) (by norm_num)
theorem B8063189 : Blo 1676038 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B1886449 : Blo 1676038 1886449 := bbase (se 2 (by rfl) ⟨707418, by rfl⟩ : syracuseStep 1886449 = 1414837) (by norm_num)
theorem B2828533 : Blo 1676038 2828533 := bbase (se 5 (by rfl) ⟨132587, by rfl⟩ : syracuseStep 2828533 = 265175) (by norm_num)
theorem B1886485 : Blo 1676038 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B4245797 : Blo 1676038 4245797 := bbase (se 4 (by rfl) ⟨398043, by rfl⟩ : syracuseStep 4245797 = 796087) (by norm_num)
theorem B1886521 : Blo 1676038 1886521 := bbase (se 2 (by rfl) ⟨707445, by rfl⟩ : syracuseStep 1886521 = 1414891) (by norm_num)
theorem B8489285 : Blo 1676038 8489285 := bbase (se 4 (by rfl) ⟨795870, by rfl⟩ : syracuseStep 8489285 = 1591741) (by norm_num)
theorem B2828621 : Blo 1676038 2828621 := bbase (se 3 (by rfl) ⟨530366, by rfl⟩ : syracuseStep 2828621 = 1060733) (by norm_num)
theorem B9062741 : Blo 1676038 9062741 := bbase (se 10 (by rfl) ⟨13275, by rfl⟩ : syracuseStep 9062741 = 26551) (by norm_num)
theorem B1886557 : Blo 1676038 1886557 := bbase (se 3 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 1886557 = 707459) (by norm_num)
theorem B1886593 : Blo 1676038 1886593 := bbase (se 2 (by rfl) ⟨707472, by rfl⟩ : syracuseStep 1886593 = 1414945) (by norm_num)
theorem B1886629 : Blo 1676038 1886629 := bbase (se 4 (by rfl) ⟨176871, by rfl⟩ : syracuseStep 1886629 = 353743) (by norm_num)
theorem B5663141 : Blo 1676038 5663141 := bbase (se 4 (by rfl) ⟨530919, by rfl⟩ : syracuseStep 5663141 = 1061839) (by norm_num)
theorem B9677237 : Blo 1676038 9677237 := bbase (se 5 (by rfl) ⟨453620, by rfl⟩ : syracuseStep 9677237 = 907241) (by norm_num)
theorem B1886665 : Blo 1676038 1886665 := bbase (se 2 (by rfl) ⟨707499, by rfl⟩ : syracuseStep 1886665 = 1414999) (by norm_num)
theorem B2828749 : Blo 1676038 2828749 := bbase (se 3 (by rfl) ⟨530390, by rfl⟩ : syracuseStep 2828749 = 1060781) (by norm_num)
theorem B9062869 : Blo 1676038 9062869 := bbase (se 7 (by rfl) ⟨106205, by rfl⟩ : syracuseStep 9062869 = 212411) (by norm_num)
theorem B1886701 : Blo 1676038 1886701 := bbase (se 3 (by rfl) ⟨353756, by rfl⟩ : syracuseStep 1886701 = 707513) (by norm_num)
theorem B7162357 : Blo 1676038 7162357 := bbase (se 5 (by rfl) ⟨335735, by rfl⟩ : syracuseStep 7162357 = 671471) (by norm_num)
theorem B3582461 : Blo 1676038 3582461 := bbase (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) (by norm_num)
theorem B1886737 : Blo 1676038 1886737 := bbase (se 2 (by rfl) ⟨707526, by rfl⟩ : syracuseStep 1886737 = 1415053) (by norm_num)
theorem B2869789 : Blo 1676038 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B2828837 : Blo 1676038 2828837 := bbase (se 4 (by rfl) ⟨265203, by rfl⟩ : syracuseStep 2828837 = 530407) (by norm_num)
theorem B1886773 : Blo 1676038 1886773 := bbase (se 5 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 1886773 = 176885) (by norm_num)
theorem B1886809 : Blo 1676038 1886809 := bbase (se 2 (by rfl) ⟨707553, by rfl⟩ : syracuseStep 1886809 = 1415107) (by norm_num)
theorem B2386541 : Blo 1676038 2386541 := bbase (se 3 (by rfl) ⟨447476, by rfl⟩ : syracuseStep 2386541 = 894953) (by norm_num)
theorem B1886845 : Blo 1676038 1886845 := bbase (se 3 (by rfl) ⟨353783, by rfl⟩ : syracuseStep 1886845 = 707567) (by norm_num)
theorem B4246141 : Blo 1676038 4246141 := bbase (se 3 (by rfl) ⟨796151, by rfl⟩ : syracuseStep 4246141 = 1592303) (by norm_num)
theorem B1886881 : Blo 1676038 1886881 := bbase (se 2 (by rfl) ⟨707580, by rfl⟩ : syracuseStep 1886881 = 1415161) (by norm_num)
theorem B2828965 : Blo 1676038 2828965 := bbase (se 4 (by rfl) ⟨265215, by rfl⟩ : syracuseStep 2828965 = 530431) (by norm_num)
theorem B2386621 : Blo 1676038 2386621 := bbase (se 3 (by rfl) ⟨447491, by rfl⟩ : syracuseStep 2386621 = 894983) (by norm_num)
theorem B1886917 : Blo 1676038 1886917 := bbase (se 4 (by rfl) ⟨176898, by rfl⟩ : syracuseStep 1886917 = 353797) (by norm_num)
theorem B1886953 : Blo 1676038 1886953 := bbase (se 2 (by rfl) ⟨707607, by rfl⟩ : syracuseStep 1886953 = 1415215) (by norm_num)
theorem B4246253 : Blo 1676038 4246253 := bbase (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) (by norm_num)
theorem B3771125 : Blo 1676038 3771125 := bbase (se 5 (by rfl) ⟨176771, by rfl⟩ : syracuseStep 3771125 = 353543) (by norm_num)
theorem B2829053 : Blo 1676038 2829053 := bbase (se 3 (by rfl) ⟨530447, by rfl⟩ : syracuseStep 2829053 = 1060895) (by norm_num)
theorem B1886989 : Blo 1676038 1886989 := bbase (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) (by norm_num)
theorem B1887025 : Blo 1676038 1887025 := bbase (se 2 (by rfl) ⟨707634, by rfl⟩ : syracuseStep 1887025 = 1415269) (by norm_num)
theorem B2386741 : Blo 1676038 2386741 := bbase (se 5 (by rfl) ⟨111878, by rfl⟩ : syracuseStep 2386741 = 223757) (by norm_num)
theorem B3771197 : Blo 1676038 3771197 := bbase (se 3 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 3771197 = 1414199) (by norm_num)
theorem B1887061 : Blo 1676038 1887061 := bbase (se 9 (by rfl) ⟨5528, by rfl⟩ : syracuseStep 1887061 = 11057) (by norm_num)
theorem B12741461 : Blo 1676038 12741461 := bbase (se 9 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 12741461 = 74657) (by norm_num)
theorem B1887097 : Blo 1676038 1887097 := bbase (se 2 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 1887097 = 1415323) (by norm_num)
theorem B2829181 : Blo 1676038 2829181 := bbase (se 3 (by rfl) ⟨530471, by rfl⟩ : syracuseStep 2829181 = 1060943) (by norm_num)
theorem B3771269 : Blo 1676038 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B2386837 : Blo 1676038 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B1887133 : Blo 1676038 1887133 := bbase (se 3 (by rfl) ⟨353837, by rfl⟩ : syracuseStep 1887133 = 707675) (by norm_num)
theorem B6368165 : Blo 1676038 6368165 := bbase (se 4 (by rfl) ⟨597015, by rfl⟩ : syracuseStep 6368165 = 1194031) (by norm_num)
theorem B4246445 : Blo 1676038 4246445 := bbase (se 3 (by rfl) ⟨796208, by rfl⟩ : syracuseStep 4246445 = 1592417) (by norm_num)
theorem B1887169 : Blo 1676038 1887169 := bbase (se 2 (by rfl) ⟨707688, by rfl⟩ : syracuseStep 1887169 = 1415377) (by norm_num)
theorem B3771341 : Blo 1676038 3771341 := bbase (se 3 (by rfl) ⟨707126, by rfl⟩ : syracuseStep 3771341 = 1414253) (by norm_num)
theorem B2042833 : Blo 1676038 2042833 := bbase (se 2 (by rfl) ⟨766062, by rfl⟩ : syracuseStep 2042833 = 1532125) (by norm_num)
theorem B2829269 : Blo 1676038 2829269 := bbase (se 7 (by rfl) ⟨33155, by rfl⟩ : syracuseStep 2829269 = 66311) (by norm_num)
theorem B1887205 : Blo 1676038 1887205 := bbase (se 4 (by rfl) ⟨176925, by rfl⟩ : syracuseStep 1887205 = 353851) (by norm_num)
theorem B1887241 : Blo 1676038 1887241 := bbase (se 2 (by rfl) ⟨707715, by rfl⟩ : syracuseStep 1887241 = 1415431) (by norm_num)
theorem B3771413 : Blo 1676038 3771413 := bbase (se 6 (by rfl) ⟨88392, by rfl⟩ : syracuseStep 3771413 = 176785) (by norm_num)
theorem B1887277 : Blo 1676038 1887277 := bbase (se 3 (by rfl) ⟨353864, by rfl⟩ : syracuseStep 1887277 = 707729) (by norm_num)
theorem B1887313 : Blo 1676038 1887313 := bbase (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) (by norm_num)
theorem B2829397 : Blo 1676038 2829397 := bbase (se 8 (by rfl) ⟨16578, by rfl⟩ : syracuseStep 2829397 = 33157) (by norm_num)
theorem B3771485 : Blo 1676038 3771485 := bbase (se 3 (by rfl) ⟨707153, by rfl⟩ : syracuseStep 3771485 = 1414307) (by norm_num)
theorem B1887349 : Blo 1676038 1887349 := bbase (se 5 (by rfl) ⟨88469, by rfl⟩ : syracuseStep 1887349 = 176939) (by norm_num)
theorem B5442709 : Blo 1676038 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B1887385 : Blo 1676038 1887385 := bbase (se 2 (by rfl) ⟨707769, by rfl⟩ : syracuseStep 1887385 = 1415539) (by norm_num)
theorem B3771557 : Blo 1676038 3771557 := bbase (se 4 (by rfl) ⟨353583, by rfl⟩ : syracuseStep 3771557 = 707167) (by norm_num)
theorem B2829485 : Blo 1676038 2829485 := bbase (se 3 (by rfl) ⟨530528, by rfl⟩ : syracuseStep 2829485 = 1061057) (by norm_num)
theorem B1887421 : Blo 1676038 1887421 := bbase (se 3 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 1887421 = 707783) (by norm_num)
theorem B6368453 : Blo 1676038 6368453 := bbase (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) (by norm_num)
theorem B7163093 : Blo 1676038 7163093 := bbase (se 7 (by rfl) ⟨83942, by rfl⟩ : syracuseStep 7163093 = 167885) (by norm_num)
theorem B1887457 : Blo 1676038 1887457 := bbase (se 2 (by rfl) ⟨707796, by rfl⟩ : syracuseStep 1887457 = 1415593) (by norm_num)
theorem B8056037 : Blo 1676038 8056037 := bbase (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) (by norm_num)
theorem B7859429 : Blo 1676038 7859429 := bbase (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) (by norm_num)
theorem B3771629 : Blo 1676038 3771629 := bbase (se 3 (by rfl) ⟨707180, by rfl⟩ : syracuseStep 3771629 = 1414361) (by norm_num)
theorem B12733685 : Blo 1676038 12733685 := bbase (se 5 (by rfl) ⟨596891, by rfl⟩ : syracuseStep 12733685 = 1193783) (by norm_num)
theorem B4246789 : Blo 1676038 4246789 := bbase (se 4 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 4246789 = 796273) (by norm_num)
theorem B1887493 : Blo 1676038 1887493 := bbase (se 4 (by rfl) ⟨176952, by rfl⟩ : syracuseStep 1887493 = 353905) (by norm_num)
theorem B1887529 : Blo 1676038 1887529 := bbase (se 2 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 1887529 = 1415647) (by norm_num)
theorem B2829613 : Blo 1676038 2829613 := bbase (se 3 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 2829613 = 1061105) (by norm_num)
theorem B3771701 : Blo 1676038 3771701 := bbase (se 5 (by rfl) ⟨176798, by rfl⟩ : syracuseStep 3771701 = 353597) (by norm_num)
theorem B1887565 : Blo 1676038 1887565 := bbase (se 3 (by rfl) ⟨353918, by rfl⟩ : syracuseStep 1887565 = 707837) (by norm_num)
theorem B5098837 : Blo 1676038 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B3181933 : Blo 1676038 3181933 := bbase (se 3 (by rfl) ⟨596612, by rfl⟩ : syracuseStep 3181933 = 1193225) (by norm_num)
theorem B1887601 : Blo 1676038 1887601 := bbase (se 2 (by rfl) ⟨707850, by rfl⟩ : syracuseStep 1887601 = 1415701) (by norm_num)
theorem B4246901 : Blo 1676038 4246901 := bbase (se 5 (by rfl) ⟨199073, by rfl⟩ : syracuseStep 4246901 = 398147) (by norm_num)
theorem B3583349 : Blo 1676038 3583349 := bbase (se 5 (by rfl) ⟨167969, by rfl⟩ : syracuseStep 3583349 = 335939) (by norm_num)
theorem B3771773 : Blo 1676038 3771773 := bbase (se 3 (by rfl) ⟨707207, by rfl⟩ : syracuseStep 3771773 = 1414415) (by norm_num)
theorem B2387333 : Blo 1676038 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B2829701 : Blo 1676038 2829701 := bbase (se 4 (by rfl) ⟨265284, by rfl⟩ : syracuseStep 2829701 = 530569) (by norm_num)
theorem B3272069 : Blo 1676038 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B1887637 : Blo 1676038 1887637 := bbase (se 6 (by rfl) ⟨44241, by rfl⟩ : syracuseStep 1887637 = 88483) (by norm_num)
theorem B1887673 : Blo 1676038 1887673 := bbase (se 2 (by rfl) ⟨707877, by rfl⟩ : syracuseStep 1887673 = 1415755) (by norm_num)
theorem B3771845 : Blo 1676038 3771845 := bbase (se 4 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 3771845 = 707221) (by norm_num)
theorem B1887709 : Blo 1676038 1887709 := bbase (se 3 (by rfl) ⟨353945, by rfl⟩ : syracuseStep 1887709 = 707891) (by norm_num)
theorem B3632629 : Blo 1676038 3632629 := bbase (se 5 (by rfl) ⟨170279, by rfl⟩ : syracuseStep 3632629 = 340559) (by norm_num)
theorem B1887745 : Blo 1676038 1887745 := bbase (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) (by norm_num)
theorem B2829829 : Blo 1676038 2829829 := bbase (se 4 (by rfl) ⟨265296, by rfl⟩ : syracuseStep 2829829 = 530593) (by norm_num)
theorem B3771917 : Blo 1676038 3771917 := bbase (se 3 (by rfl) ⟨707234, by rfl⟩ : syracuseStep 3771917 = 1414469) (by norm_num)
theorem B16109077 : Blo 1676038 16109077 := bbase (se 6 (by rfl) ⟨377556, by rfl⟩ : syracuseStep 16109077 = 755113) (by norm_num)
theorem B1912357 : Blo 1676038 1912357 := bbase (se 4 (by rfl) ⟨179283, by rfl⟩ : syracuseStep 1912357 = 358567) (by norm_num)
theorem B1887781 : Blo 1676038 1887781 := bbase (se 4 (by rfl) ⟨176979, by rfl⟩ : syracuseStep 1887781 = 353959) (by norm_num)
theorem B4247093 : Blo 1676038 4247093 := bbase (se 5 (by rfl) ⟨199082, by rfl⟩ : syracuseStep 4247093 = 398165) (by norm_num)
theorem B3771989 : Blo 1676038 3771989 := bbase (se 8 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 3771989 = 44203) (by norm_num)
theorem B8490581 : Blo 1676038 8490581 := bbase (se 8 (by rfl) ⟨49749, by rfl⟩ : syracuseStep 8490581 = 99499) (by norm_num)
theorem B2829917 : Blo 1676038 2829917 := bbase (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) (by norm_num)
theorem B3583597 : Blo 1676038 3583597 := bbase (se 3 (by rfl) ⟨671924, by rfl⟩ : syracuseStep 3583597 = 1343849) (by norm_num)
theorem B3182237 : Blo 1676038 3182237 := bbase (se 3 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 3182237 = 1193339) (by norm_num)
theorem B3772061 : Blo 1676038 3772061 := bbase (se 3 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 3772061 = 1414523) (by norm_num)
theorem B12095189 : Blo 1676038 12095189 := bbase (se 7 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 12095189 = 283481) (by norm_num)
theorem B2830045 : Blo 1676038 2830045 := bbase (se 3 (by rfl) ⟨530633, by rfl⟩ : syracuseStep 2830045 = 1061267) (by norm_num)
theorem B3772133 : Blo 1676038 3772133 := bbase (se 4 (by rfl) ⟨353637, by rfl⟩ : syracuseStep 3772133 = 707275) (by norm_num)
theorem B2723557 : Blo 1676038 2723557 := bbase (se 4 (by rfl) ⟨255333, by rfl⟩ : syracuseStep 2723557 = 510667) (by norm_num)
theorem B1814285 : Blo 1676038 1814285 := bbase (se 3 (by rfl) ⟨340178, by rfl⟩ : syracuseStep 1814285 = 680357) (by norm_num)
theorem B3772205 : Blo 1676038 3772205 := bbase (se 3 (by rfl) ⟨707288, by rfl⟩ : syracuseStep 3772205 = 1414577) (by norm_num)
theorem B2830133 : Blo 1676038 2830133 := bbase (se 5 (by rfl) ⟨132662, by rfl⟩ : syracuseStep 2830133 = 265325) (by norm_num)
theorem B3772277 : Blo 1676038 3772277 := bbase (se 5 (by rfl) ⟨176825, by rfl⟩ : syracuseStep 3772277 = 353651) (by norm_num)
theorem B2723725 : Blo 1676038 2723725 := bbase (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) (by norm_num)
theorem B4247437 : Blo 1676038 4247437 := bbase (se 3 (by rfl) ⟨796394, by rfl⟩ : syracuseStep 4247437 = 1592789) (by norm_num)
theorem B6123413 : Blo 1676038 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2387885 : Blo 1676038 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B2830261 : Blo 1676038 2830261 := bbase (se 5 (by rfl) ⟨132668, by rfl⟩ : syracuseStep 2830261 = 265337) (by norm_num)
theorem B9555893 : Blo 1676038 9555893 := bbase (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) (by norm_num)
theorem B1789885 : Blo 1676038 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B3772349 : Blo 1676038 3772349 := bbase (se 3 (by rfl) ⟨707315, by rfl⟩ : syracuseStep 3772349 = 1414631) (by norm_num)
theorem B12095477 : Blo 1676038 12095477 := bbase (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) (by norm_num)
theorem B1789957 : Blo 1676038 1789957 := bbase (se 4 (by rfl) ⟨167808, by rfl⟩ : syracuseStep 1789957 = 335617) (by norm_num)
theorem B3772421 : Blo 1676038 3772421 := bbase (se 4 (by rfl) ⟨353664, by rfl⟩ : syracuseStep 3772421 = 707329) (by norm_num)
theorem B2830349 : Blo 1676038 2830349 := bbase (se 3 (by rfl) ⟨530690, by rfl⟩ : syracuseStep 2830349 = 1061381) (by norm_num)
theorem B1699913 : Blo 1676038 1699913 := bbase (se 2 (by rfl) ⟨637467, by rfl⟩ : syracuseStep 1699913 = 1274935) (by norm_num)
theorem B3772493 : Blo 1676038 3772493 := bbase (se 3 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 3772493 = 1414685) (by norm_num)
theorem B5656661 : Blo 1676038 5656661 := bbase (se 8 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 5656661 = 66289) (by norm_num)
theorem B2830477 : Blo 1676038 2830477 := bbase (se 3 (by rfl) ⟨530714, by rfl⟩ : syracuseStep 2830477 = 1061429) (by norm_num)
theorem B3772565 : Blo 1676038 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B1913009 : Blo 1676038 1913009 := bbase (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) (by norm_num)
theorem B1790137 : Blo 1676038 1790137 := bbase (se 2 (by rfl) ⟨671301, by rfl⟩ : syracuseStep 1790137 = 1342603) (by norm_num)
theorem B2150617 : Blo 1676038 2150617 := bbase (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) (by norm_num)
theorem B3772637 : Blo 1676038 3772637 := bbase (se 3 (by rfl) ⟨707369, by rfl⟩ : syracuseStep 3772637 = 1414739) (by norm_num)
theorem B2830565 : Blo 1676038 2830565 := bbase (se 4 (by rfl) ⟨265365, by rfl⟩ : syracuseStep 2830565 = 530731) (by norm_num)
theorem B3772709 : Blo 1676038 3772709 := bbase (se 4 (by rfl) ⟨353691, by rfl⟩ : syracuseStep 3772709 = 707383) (by norm_num)
theorem B2830693 : Blo 1676038 2830693 := bbase (se 4 (by rfl) ⟨265377, by rfl⟩ : syracuseStep 2830693 = 530755) (by norm_num)
theorem B6369637 : Blo 1676038 6369637 := bbase (se 4 (by rfl) ⟨597153, by rfl⟩ : syracuseStep 6369637 = 1194307) (by norm_num)
theorem B3772781 : Blo 1676038 3772781 := bbase (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) (by norm_num)
theorem B7647605 : Blo 1676038 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B3182989 : Blo 1676038 3182989 := bbase (se 3 (by rfl) ⟨596810, by rfl⟩ : syracuseStep 3182989 = 1193621) (by norm_num)
theorem B3772853 : Blo 1676038 3772853 := bbase (se 5 (by rfl) ⟨176852, by rfl⟩ : syracuseStep 3772853 = 353705) (by norm_num)
theorem B1913269 : Blo 1676038 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B2830781 : Blo 1676038 2830781 := bbase (se 3 (by rfl) ⟨530771, by rfl⟩ : syracuseStep 2830781 = 1061543) (by norm_num)
theorem B3772925 : Blo 1676038 3772925 := bbase (se 3 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 3772925 = 1414847) (by norm_num)
theorem B5657093 : Blo 1676038 5657093 := bbase (se 4 (by rfl) ⟨530352, by rfl⟩ : syracuseStep 5657093 = 1060705) (by norm_num)
theorem B3183133 : Blo 1676038 3183133 := bbase (se 3 (by rfl) ⟨596837, by rfl⟩ : syracuseStep 3183133 = 1193675) (by norm_num)
theorem B2830909 : Blo 1676038 2830909 := bbase (se 3 (by rfl) ⟨530795, by rfl⟩ : syracuseStep 2830909 = 1061591) (by norm_num)
theorem B3772997 : Blo 1676038 3772997 := bbase (se 4 (by rfl) ⟨353718, by rfl⟩ : syracuseStep 3772997 = 707437) (by norm_num)
theorem B1790581 : Blo 1676038 1790581 := bbase (se 5 (by rfl) ⟨83933, by rfl⟩ : syracuseStep 1790581 = 167867) (by norm_num)
theorem B3773069 : Blo 1676038 3773069 := bbase (se 3 (by rfl) ⟨707450, by rfl⟩ : syracuseStep 3773069 = 1414901) (by norm_num)
theorem B2830997 : Blo 1676038 2830997 := bbase (se 6 (by rfl) ⟨66351, by rfl⟩ : syracuseStep 2830997 = 132703) (by norm_num)
theorem B6369941 : Blo 1676038 6369941 := bbase (se 6 (by rfl) ⟨149295, by rfl⟩ : syracuseStep 6369941 = 298591) (by norm_num)
theorem B2388637 : Blo 1676038 2388637 := bbase (se 3 (by rfl) ⟨447869, by rfl⟩ : syracuseStep 2388637 = 895739) (by norm_num)
theorem B3183293 : Blo 1676038 3183293 := bbase (se 3 (by rfl) ⟨596867, by rfl⟩ : syracuseStep 3183293 = 1193735) (by norm_num)
theorem B3773141 : Blo 1676038 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B1790705 : Blo 1676038 1790705 := bbase (se 2 (by rfl) ⟨671514, by rfl⟩ : syracuseStep 1790705 = 1343029) (by norm_num)
theorem B2831125 : Blo 1676038 2831125 := bbase (se 6 (by rfl) ⟨66354, by rfl⟩ : syracuseStep 2831125 = 132709) (by norm_num)
theorem B3773213 : Blo 1676038 3773213 := bbase (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) (by norm_num)
theorem B8172341 : Blo 1676038 8172341 := bbase (se 5 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 8172341 = 766157) (by norm_num)
theorem B3183437 : Blo 1676038 3183437 := bbase (se 3 (by rfl) ⟨596894, by rfl⟩ : syracuseStep 3183437 = 1193789) (by norm_num)
theorem B3773285 : Blo 1676038 3773285 := bbase (se 4 (by rfl) ⟨353745, by rfl⟩ : syracuseStep 3773285 = 707491) (by norm_num)
theorem B8491877 : Blo 1676038 8491877 := bbase (se 4 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 8491877 = 1592227) (by norm_num)
theorem B2831213 : Blo 1676038 2831213 := bbase (se 3 (by rfl) ⟨530852, by rfl⟩ : syracuseStep 2831213 = 1061705) (by norm_num)
theorem B2151289 : Blo 1676038 2151289 := bbase (se 2 (by rfl) ⟨806733, by rfl⟩ : syracuseStep 2151289 = 1613467) (by norm_num)
theorem B3773357 : Blo 1676038 3773357 := bbase (se 3 (by rfl) ⟨707504, by rfl⟩ : syracuseStep 3773357 = 1415009) (by norm_num)
theorem B5657525 : Blo 1676038 5657525 := bbase (se 5 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 5657525 = 530393) (by norm_num)
theorem B1840081 : Blo 1676038 1840081 := bbase (se 2 (by rfl) ⟨690030, by rfl⟩ : syracuseStep 1840081 = 1380061) (by norm_num)
theorem B1790957 : Blo 1676038 1790957 := bbase (se 3 (by rfl) ⟨335804, by rfl⟩ : syracuseStep 1790957 = 671609) (by norm_num)
theorem B2831341 : Blo 1676038 2831341 := bbase (se 3 (by rfl) ⟨530876, by rfl⟩ : syracuseStep 2831341 = 1061753) (by norm_num)
theorem B3773429 : Blo 1676038 3773429 := bbase (se 5 (by rfl) ⟨176879, by rfl⟩ : syracuseStep 3773429 = 353759) (by norm_num)
theorem B9679925 : Blo 1676038 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B3773501 : Blo 1676038 3773501 := bbase (se 3 (by rfl) ⟨707531, by rfl⟩ : syracuseStep 3773501 = 1415063) (by norm_num)
theorem B2831429 : Blo 1676038 2831429 := bbase (se 4 (by rfl) ⟨265446, by rfl⟩ : syracuseStep 2831429 = 530893) (by norm_num)
theorem B3183725 : Blo 1676038 3183725 := bbase (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) (by norm_num)
theorem B3773573 : Blo 1676038 3773573 := bbase (se 4 (by rfl) ⟨353772, by rfl⟩ : syracuseStep 3773573 = 707545) (by norm_num)
theorem B5100677 : Blo 1676038 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B2831557 : Blo 1676038 2831557 := bbase (se 4 (by rfl) ⟨265458, by rfl⟩ : syracuseStep 2831557 = 530917) (by norm_num)
theorem B3773645 : Blo 1676038 3773645 := bbase (se 3 (by rfl) ⟨707558, by rfl⟩ : syracuseStep 3773645 = 1415117) (by norm_num)
theorem B3183877 : Blo 1676038 3183877 := bbase (se 4 (by rfl) ⟨298488, by rfl⟩ : syracuseStep 3183877 = 596977) (by norm_num)
theorem B3773717 : Blo 1676038 3773717 := bbase (se 6 (by rfl) ⟨88446, by rfl⟩ : syracuseStep 3773717 = 176893) (by norm_num)
theorem B2831645 : Blo 1676038 2831645 := bbase (se 3 (by rfl) ⟨530933, by rfl⟩ : syracuseStep 2831645 = 1061867) (by norm_num)
theorem B3773789 : Blo 1676038 3773789 := bbase (se 3 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 3773789 = 1415171) (by norm_num)
theorem B5657957 : Blo 1676038 5657957 := bbase (se 4 (by rfl) ⟨530433, by rfl⟩ : syracuseStep 5657957 = 1060867) (by norm_num)
theorem B3773861 : Blo 1676038 3773861 := bbase (se 4 (by rfl) ⟨353799, by rfl⟩ : syracuseStep 3773861 = 707599) (by norm_num)
theorem B1791401 : Blo 1676038 1791401 := bbase (se 2 (by rfl) ⟨671775, by rfl⟩ : syracuseStep 1791401 = 1343551) (by norm_num)
theorem B3773933 : Blo 1676038 3773933 := bbase (se 3 (by rfl) ⟨707612, by rfl⟩ : syracuseStep 3773933 = 1415225) (by norm_num)
theorem B7263749 : Blo 1676038 7263749 := bbase (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) (by norm_num)
theorem B5518901 : Blo 1676038 5518901 := bbase (se 5 (by rfl) ⟨258698, by rfl⟩ : syracuseStep 5518901 = 517397) (by norm_num)
theorem B3184181 : Blo 1676038 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B3774005 : Blo 1676038 3774005 := bbase (se 5 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 3774005 = 353813) (by norm_num)
theorem B1816129 : Blo 1676038 1816129 := bbase (se 2 (by rfl) ⟨681048, by rfl⟩ : syracuseStep 1816129 = 1362097) (by norm_num)
theorem B3774077 : Blo 1676038 3774077 := bbase (se 3 (by rfl) ⟨707639, by rfl⟩ : syracuseStep 3774077 = 1415279) (by norm_num)
theorem B5445269 : Blo 1676038 5445269 := bbase (se 6 (by rfl) ⟨127623, by rfl⟩ : syracuseStep 5445269 = 255247) (by norm_num)
theorem B1791649 : Blo 1676038 1791649 := bbase (se 2 (by rfl) ⟨671868, by rfl⟩ : syracuseStep 1791649 = 1343737) (by norm_num)
theorem B3774149 : Blo 1676038 3774149 := bbase (se 4 (by rfl) ⟨353826, by rfl⟩ : syracuseStep 3774149 = 707653) (by norm_num)
theorem B3774221 : Blo 1676038 3774221 := bbase (se 3 (by rfl) ⟨707666, by rfl⟩ : syracuseStep 3774221 = 1415333) (by norm_num)
theorem B5658389 : Blo 1676038 5658389 := bbase (se 6 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 5658389 = 265237) (by norm_num)
theorem B5371717 : Blo 1676038 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B3774293 : Blo 1676038 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B3020669 : Blo 1676038 3020669 := bbase (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) (by norm_num)
theorem B3774365 : Blo 1676038 3774365 := bbase (se 3 (by rfl) ⟨707693, by rfl⟩ : syracuseStep 3774365 = 1415387) (by norm_num)
theorem B3774437 : Blo 1676038 3774437 := bbase (se 4 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 3774437 = 707707) (by norm_num)
theorem B6797317 : Blo 1676038 6797317 := bbase (se 4 (by rfl) ⟨637248, by rfl⟩ : syracuseStep 6797317 = 1274497) (by norm_num)
theorem B3774509 : Blo 1676038 3774509 := bbase (se 3 (by rfl) ⟨707720, by rfl⟩ : syracuseStep 3774509 = 1415441) (by norm_num)
theorem B21502037 : Blo 1676038 21502037 := bbase (se 8 (by rfl) ⟨125988, by rfl⟩ : syracuseStep 21502037 = 251977) (by norm_num)
theorem B3774581 : Blo 1676038 3774581 := bbase (se 5 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 3774581 = 353867) (by norm_num)
theorem B8493173 : Blo 1676038 8493173 := bbase (se 5 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 8493173 = 796235) (by norm_num)
theorem B4028557 : Blo 1676038 4028557 := bbase (se 3 (by rfl) ⟨755354, by rfl⟩ : syracuseStep 4028557 = 1510709) (by norm_num)
theorem B3774653 : Blo 1676038 3774653 := bbase (se 3 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 3774653 = 1415495) (by norm_num)
theorem B4774085 : Blo 1676038 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B5658821 : Blo 1676038 5658821 := bbase (se 4 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 5658821 = 1061029) (by norm_num)
theorem B3315941 : Blo 1676038 3315941 := bbase (se 4 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 3315941 = 621739) (by norm_num)
theorem B3774725 : Blo 1676038 3774725 := bbase (se 4 (by rfl) ⟨353880, by rfl⟩ : syracuseStep 3774725 = 707761) (by norm_num)
theorem B3184933 : Blo 1676038 3184933 := bbase (se 4 (by rfl) ⟨298587, by rfl⟩ : syracuseStep 3184933 = 597175) (by norm_num)
theorem B3774797 : Blo 1676038 3774797 := bbase (se 3 (by rfl) ⟨707774, by rfl⟩ : syracuseStep 3774797 = 1415549) (by norm_num)
theorem B2685269 : Blo 1676038 2685269 := bbase (se 10 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 2685269 = 7867) (by norm_num)
theorem B3774869 : Blo 1676038 3774869 := bbase (se 6 (by rfl) ⟨88473, by rfl⟩ : syracuseStep 3774869 = 176947) (by norm_num)
theorem B7166389 : Blo 1676038 7166389 := bbase (se 5 (by rfl) ⟨335924, by rfl⟩ : syracuseStep 7166389 = 671849) (by norm_num)
theorem B3185077 : Blo 1676038 3185077 := bbase (se 5 (by rfl) ⟨149300, by rfl⟩ : syracuseStep 3185077 = 298601) (by norm_num)
theorem B2685397 : Blo 1676038 2685397 := bbase (se 7 (by rfl) ⟨31469, by rfl⟩ : syracuseStep 2685397 = 62939) (by norm_num)
theorem B3774941 : Blo 1676038 3774941 := bbase (se 3 (by rfl) ⟨707801, by rfl⟩ : syracuseStep 3774941 = 1415603) (by norm_num)
theorem B4028933 : Blo 1676038 4028933 := bbase (se 4 (by rfl) ⟨377712, by rfl⟩ : syracuseStep 4028933 = 755425) (by norm_num)
theorem B5896709 : Blo 1676038 5896709 := bbase (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) (by norm_num)
theorem B8485397 : Blo 1676038 8485397 := bbase (se 6 (by rfl) ⟨198876, by rfl⟩ : syracuseStep 8485397 = 397753) (by norm_num)
theorem B3775013 : Blo 1676038 3775013 := bbase (se 4 (by rfl) ⟨353907, by rfl⟩ : syracuseStep 3775013 = 707815) (by norm_num)
theorem B3185237 : Blo 1676038 3185237 := bbase (se 8 (by rfl) ⟨18663, by rfl⟩ : syracuseStep 3185237 = 37327) (by norm_num)
theorem B3775085 : Blo 1676038 3775085 := bbase (se 3 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 3775085 = 1415657) (by norm_num)
theorem B5659253 : Blo 1676038 5659253 := bbase (se 5 (by rfl) ⟨265277, by rfl⟩ : syracuseStep 5659253 = 530555) (by norm_num)
theorem B3775157 : Blo 1676038 3775157 := bbase (se 5 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 3775157 = 353921) (by norm_num)
theorem B3185381 : Blo 1676038 3185381 := bbase (se 4 (by rfl) ⟨298629, by rfl⟩ : syracuseStep 3185381 = 597259) (by norm_num)
theorem B3775229 : Blo 1676038 3775229 := bbase (se 3 (by rfl) ⟨707855, by rfl⟩ : syracuseStep 3775229 = 1415711) (by norm_num)
theorem B3775301 : Blo 1676038 3775301 := bbase (se 4 (by rfl) ⟨353934, by rfl⟩ : syracuseStep 3775301 = 707869) (by norm_num)
theorem B3775373 : Blo 1676038 3775373 := bbase (se 3 (by rfl) ⟨707882, by rfl⟩ : syracuseStep 3775373 = 1415765) (by norm_num)
theorem B4029365 : Blo 1676038 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B7650229 : Blo 1676038 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B3775445 : Blo 1676038 3775445 := bbase (se 7 (by rfl) ⟨44243, by rfl⟩ : syracuseStep 3775445 = 88487) (by norm_num)
theorem B14334965 : Blo 1676038 14334965 := bbase (se 5 (by rfl) ⟨671951, by rfl⟩ : syracuseStep 14334965 = 1343903) (by norm_num)
theorem B3775517 : Blo 1676038 3775517 := bbase (se 3 (by rfl) ⟨707909, by rfl⟩ : syracuseStep 3775517 = 1415819) (by norm_num)
theorem B5659685 : Blo 1676038 5659685 := bbase (se 4 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 5659685 = 1061191) (by norm_num)
theorem B4422725 : Blo 1676038 4422725 := bbase (se 4 (by rfl) ⟨414630, by rfl⟩ : syracuseStep 4422725 = 829261) (by norm_num)
theorem B6364277 : Blo 1676038 6364277 := bbase (se 5 (by rfl) ⟨298325, by rfl⟩ : syracuseStep 6364277 = 596651) (by norm_num)
theorem B3398773 : Blo 1676038 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B14326901 : Blo 1676038 14326901 := bbase (se 5 (by rfl) ⟨671573, by rfl⟩ : syracuseStep 14326901 = 1343147) (by norm_num)
theorem B4242557 : Blo 1676038 4242557 := bbase (se 3 (by rfl) ⟨795479, by rfl⟩ : syracuseStep 4242557 = 1590959) (by norm_num)
theorem B2514077 : Blo 1676038 2514077 := bbase (se 3 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 2514077 = 942779) (by norm_num)
theorem B2514101 : Blo 1676038 2514101 := bbase (se 5 (by rfl) ⟨117848, by rfl⟩ : syracuseStep 2514101 = 235697) (by norm_num)
theorem B2514125 : Blo 1676038 2514125 := bbase (se 3 (by rfl) ⟨471398, by rfl⟩ : syracuseStep 2514125 = 942797) (by norm_num)
theorem B2514149 : Blo 1676038 2514149 := bbase (se 4 (by rfl) ⟨235701, by rfl⟩ : syracuseStep 2514149 = 471403) (by norm_num)
theorem B2514173 : Blo 1676038 2514173 := bbase (se 3 (by rfl) ⟨471407, by rfl⟩ : syracuseStep 2514173 = 942815) (by norm_num)
theorem B2514197 : Blo 1676038 2514197 := bbase (se 6 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 2514197 = 117853) (by norm_num)
theorem B2514221 : Blo 1676038 2514221 := bbase (se 3 (by rfl) ⟨471416, by rfl⟩ : syracuseStep 2514221 = 942833) (by norm_num)
theorem B2514245 : Blo 1676038 2514245 := bbase (se 4 (by rfl) ⟨235710, by rfl⟩ : syracuseStep 2514245 = 471421) (by norm_num)
theorem B3063109 : Blo 1676038 3063109 := bbase (se 4 (by rfl) ⟨287166, by rfl⟩ : syracuseStep 3063109 = 574333) (by norm_num)
theorem B42974549 : Blo 1676038 42974549 := bbase (se 11 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 42974549 = 62951) (by norm_num)
theorem B96722261 : Blo 1676038 96722261 := bbase (se 11 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 96722261 = 141683) (by norm_num)
theorem B2514269 : Blo 1676038 2514269 := bbase (se 3 (by rfl) ⟨471425, by rfl⟩ : syracuseStep 2514269 = 942851) (by norm_num)
theorem B4775269 : Blo 1676038 4775269 := bbase (se 4 (by rfl) ⟨447681, by rfl⟩ : syracuseStep 4775269 = 895363) (by norm_num)
theorem B6045029 : Blo 1676038 6045029 := bbase (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) (by norm_num)
theorem B2514293 : Blo 1676038 2514293 := bbase (se 5 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 2514293 = 235715) (by norm_num)
theorem B8494469 : Blo 1676038 8494469 := bbase (se 4 (by rfl) ⟨796356, by rfl⟩ : syracuseStep 8494469 = 1592713) (by norm_num)
theorem B2514317 : Blo 1676038 2514317 := bbase (se 3 (by rfl) ⟨471434, by rfl⟩ : syracuseStep 2514317 = 942869) (by norm_num)
theorem B6364565 : Blo 1676038 6364565 := bbase (se 6 (by rfl) ⟨149169, by rfl⟩ : syracuseStep 6364565 = 298339) (by norm_num)
theorem B2514341 : Blo 1676038 2514341 := bbase (se 4 (by rfl) ⟨235719, by rfl⟩ : syracuseStep 2514341 = 471439) (by norm_num)
theorem B2514365 : Blo 1676038 2514365 := bbase (se 3 (by rfl) ⟨471443, by rfl⟩ : syracuseStep 2514365 = 942887) (by norm_num)
theorem B4242901 : Blo 1676038 4242901 := bbase (se 7 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 4242901 = 99443) (by norm_num)
theorem B2514389 : Blo 1676038 2514389 := bbase (se 7 (by rfl) ⟨29465, by rfl⟩ : syracuseStep 2514389 = 58931) (by norm_num)
theorem B5660117 : Blo 1676038 5660117 := bbase (se 7 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 5660117 = 132659) (by norm_num)
theorem B2514413 : Blo 1676038 2514413 := bbase (se 3 (by rfl) ⟨471452, by rfl⟩ : syracuseStep 2514413 = 942905) (by norm_num)
theorem B4029941 : Blo 1676038 4029941 := bbase (se 5 (by rfl) ⟨188903, by rfl⟩ : syracuseStep 4029941 = 377807) (by norm_num)
theorem B2514437 : Blo 1676038 2514437 := bbase (se 4 (by rfl) ⟨235728, by rfl⟩ : syracuseStep 2514437 = 471457) (by norm_num)
theorem B4775429 : Blo 1676038 4775429 := bbase (se 4 (by rfl) ⟨447696, by rfl⟩ : syracuseStep 4775429 = 895393) (by norm_num)
theorem B2514461 : Blo 1676038 2514461 := bbase (se 3 (by rfl) ⟨471461, by rfl⟩ : syracuseStep 2514461 = 942923) (by norm_num)
theorem B7257653 : Blo 1676038 7257653 := bbase (se 5 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 7257653 = 680405) (by norm_num)
theorem B2514485 : Blo 1676038 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B4243013 : Blo 1676038 4243013 := bbase (se 4 (by rfl) ⟨397782, by rfl⟩ : syracuseStep 4243013 = 795565) (by norm_num)
theorem B2514509 : Blo 1676038 2514509 := bbase (se 3 (by rfl) ⟨471470, by rfl⟩ : syracuseStep 2514509 = 942941) (by norm_num)
theorem B2514533 : Blo 1676038 2514533 := bbase (se 4 (by rfl) ⟨235737, by rfl⟩ : syracuseStep 2514533 = 471475) (by norm_num)
theorem B2121329 : Blo 1676038 2121329 := bbase (se 2 (by rfl) ⟨795498, by rfl⟩ : syracuseStep 2121329 = 1590997) (by norm_num)
theorem B16113269 : Blo 1676038 16113269 := bbase (se 5 (by rfl) ⟨755309, by rfl⟩ : syracuseStep 16113269 = 1510619) (by norm_num)
theorem B2514557 : Blo 1676038 2514557 := bbase (se 3 (by rfl) ⟨471479, by rfl⟩ : syracuseStep 2514557 = 942959) (by norm_num)
theorem B6045317 : Blo 1676038 6045317 := bbase (se 4 (by rfl) ⟨566748, by rfl⟩ : syracuseStep 6045317 = 1133497) (by norm_num)
theorem B2514581 : Blo 1676038 2514581 := bbase (se 6 (by rfl) ⟨58935, by rfl⟩ : syracuseStep 2514581 = 117871) (by norm_num)
theorem B2121385 : Blo 1676038 2121385 := bbase (se 2 (by rfl) ⟨795519, by rfl⟩ : syracuseStep 2121385 = 1591039) (by norm_num)
theorem B2514605 : Blo 1676038 2514605 := bbase (se 3 (by rfl) ⟨471488, by rfl⟩ : syracuseStep 2514605 = 942977) (by norm_num)
theorem B9068213 : Blo 1676038 9068213 := bbase (se 5 (by rfl) ⟨425072, by rfl⟩ : syracuseStep 9068213 = 850145) (by norm_num)
theorem B2514629 : Blo 1676038 2514629 := bbase (se 4 (by rfl) ⟨235746, by rfl⟩ : syracuseStep 2514629 = 471493) (by norm_num)
theorem B6127301 : Blo 1676038 6127301 := bbase (se 4 (by rfl) ⟨574434, by rfl⟩ : syracuseStep 6127301 = 1148869) (by norm_num)
theorem B15302357 : Blo 1676038 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B2514653 : Blo 1676038 2514653 := bbase (se 3 (by rfl) ⟨471497, by rfl⟩ : syracuseStep 2514653 = 942995) (by norm_num)
theorem B2514677 : Blo 1676038 2514677 := bbase (se 5 (by rfl) ⟨117875, by rfl⟩ : syracuseStep 2514677 = 235751) (by norm_num)
theorem B4775669 : Blo 1676038 4775669 := bbase (se 5 (by rfl) ⟨223859, by rfl⟩ : syracuseStep 4775669 = 447719) (by norm_num)
theorem B10747637 : Blo 1676038 10747637 := bbase (se 5 (by rfl) ⟨503795, by rfl⟩ : syracuseStep 10747637 = 1007591) (by norm_num)
theorem B3399421 : Blo 1676038 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B4243205 : Blo 1676038 4243205 := bbase (se 4 (by rfl) ⟨397800, by rfl⟩ : syracuseStep 4243205 = 795601) (by norm_num)
theorem B2121481 : Blo 1676038 2121481 := bbase (se 2 (by rfl) ⟨795555, by rfl⟩ : syracuseStep 2121481 = 1591111) (by norm_num)
theorem B2514701 : Blo 1676038 2514701 := bbase (se 3 (by rfl) ⟨471506, by rfl⟩ : syracuseStep 2514701 = 943013) (by norm_num)
theorem B8486693 : Blo 1676038 8486693 := bbase (se 4 (by rfl) ⟨795627, by rfl⟩ : syracuseStep 8486693 = 1591255) (by norm_num)
theorem B2514725 : Blo 1676038 2514725 := bbase (se 4 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 2514725 = 471511) (by norm_num)
theorem B3579709 : Blo 1676038 3579709 := bbase (se 3 (by rfl) ⟨671195, by rfl⟩ : syracuseStep 3579709 = 1342391) (by norm_num)
theorem B2514749 : Blo 1676038 2514749 := bbase (se 3 (by rfl) ⟨471515, by rfl⟩ : syracuseStep 2514749 = 943031) (by norm_num)
theorem B2686781 : Blo 1676038 2686781 := bbase (se 3 (by rfl) ⟨503771, by rfl⟩ : syracuseStep 2686781 = 1007543) (by norm_num)
theorem B2514773 : Blo 1676038 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B2514797 : Blo 1676038 2514797 := bbase (se 3 (by rfl) ⟨471524, by rfl⟩ : syracuseStep 2514797 = 943049) (by norm_num)
theorem B2514821 : Blo 1676038 2514821 := bbase (se 4 (by rfl) ⟨235764, by rfl⟩ : syracuseStep 2514821 = 471529) (by norm_num)
theorem B5660549 : Blo 1676038 5660549 := bbase (se 4 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 5660549 = 1061353) (by norm_num)
theorem B2514845 : Blo 1676038 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B2121653 : Blo 1676038 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B2514869 : Blo 1676038 2514869 := bbase (se 5 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 2514869 = 235769) (by norm_num)
theorem B4775861 : Blo 1676038 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B2514893 : Blo 1676038 2514893 := bbase (se 3 (by rfl) ⟨471542, by rfl⟩ : syracuseStep 2514893 = 943085) (by norm_num)
theorem B2015201 : Blo 1676038 2015201 := bbase (se 2 (by rfl) ⟨755700, by rfl⟩ : syracuseStep 2015201 = 1511401) (by norm_num)
theorem B2514917 : Blo 1676038 2514917 := bbase (se 4 (by rfl) ⟨235773, by rfl⟩ : syracuseStep 2514917 = 471547) (by norm_num)
theorem B2121709 : Blo 1676038 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B2514941 : Blo 1676038 2514941 := bbase (se 3 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 2514941 = 943103) (by norm_num)
theorem B2514947 : Blo 1676038 2514947 := bstep (se 1 (by rfl) ⟨1886210, by rfl⟩ : syracuseStep 2514947 = 3772421) B3772421
theorem B2514977 : Blo 1676038 2514977 := bstep (se 2 (by rfl) ⟨943116, by rfl⟩ : syracuseStep 2514977 = 1886233) B1886233
theorem B4030499 : Blo 1676038 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B2514995 : Blo 1676038 2514995 := bstep (se 1 (by rfl) ⟨1886246, by rfl⟩ : syracuseStep 2514995 = 3772493) B3772493
theorem B2515025 : Blo 1676038 2515025 := bstep (se 2 (by rfl) ⟨943134, by rfl⟩ : syracuseStep 2515025 = 1886269) B1886269
theorem B2515043 : Blo 1676038 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B2687089 : Blo 1676038 2687089 := bstep (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) B2015317
theorem B2515073 : Blo 1676038 2515073 := bstep (se 2 (by rfl) ⟨943152, by rfl⟩ : syracuseStep 2515073 = 1886305) B1886305
theorem B2515091 : Blo 1676038 2515091 := bstep (se 1 (by rfl) ⟨1886318, by rfl⟩ : syracuseStep 2515091 = 3772637) B3772637
theorem B2515121 : Blo 1676038 2515121 := bstep (se 2 (by rfl) ⟨943170, by rfl⟩ : syracuseStep 2515121 = 1886341) B1886341
theorem B2515139 : Blo 1676038 2515139 := bstep (se 1 (by rfl) ⟨1886354, by rfl⟩ : syracuseStep 2515139 = 3772709) B3772709
theorem B2687185 : Blo 1676038 2687185 := bstep (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) B2015389
theorem B2515169 : Blo 1676038 2515169 := bstep (se 2 (by rfl) ⟨943188, by rfl⟩ : syracuseStep 2515169 = 1886377) B1886377
theorem B2515187 : Blo 1676038 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B2515217 : Blo 1676038 2515217 := bstep (se 2 (by rfl) ⟨943206, by rfl⟩ : syracuseStep 2515217 = 1886413) B1886413
theorem B2867489 : Blo 1676038 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B2515235 : Blo 1676038 2515235 := bstep (se 1 (by rfl) ⟨1886426, by rfl⟩ : syracuseStep 2515235 = 3772853) B3772853
theorem B2515265 : Blo 1676038 2515265 := bstep (se 2 (by rfl) ⟨943224, by rfl⟩ : syracuseStep 2515265 = 1886449) B1886449
theorem B2515283 : Blo 1676038 2515283 := bstep (se 1 (by rfl) ⟨1886462, by rfl⟩ : syracuseStep 2515283 = 3772925) B3772925
theorem B2515313 : Blo 1676038 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B2687345 : Blo 1676038 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B2515331 : Blo 1676038 2515331 := bstep (se 1 (by rfl) ⟨1886498, by rfl⟩ : syracuseStep 2515331 = 3772997) B3772997
theorem B9552269 : Blo 1676038 9552269 := bstep (se 3 (by rfl) ⟨1791050, by rfl⟩ : syracuseStep 9552269 = 3582101) B3582101
theorem B2515361 : Blo 1676038 2515361 := bstep (se 2 (by rfl) ⟨943260, by rfl⟩ : syracuseStep 2515361 = 1886521) B1886521
theorem B2515379 : Blo 1676038 2515379 := bstep (se 1 (by rfl) ⟨1886534, by rfl⟩ : syracuseStep 2515379 = 3773069) B3773069
theorem B2515409 : Blo 1676038 2515409 := bstep (se 2 (by rfl) ⟨943278, by rfl⟩ : syracuseStep 2515409 = 1886557) B1886557
theorem B2122195 : Blo 1676038 2122195 := bstep (se 1 (by rfl) ⟨1591646, by rfl⟩ : syracuseStep 2122195 = 3183293) B3183293
theorem B2515427 : Blo 1676038 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B2515457 : Blo 1676038 2515457 := bstep (se 2 (by rfl) ⟨943296, by rfl⟩ : syracuseStep 2515457 = 1886593) B1886593
theorem B5661197 : Blo 1676038 5661197 := bstep (se 3 (by rfl) ⟨1061474, by rfl⟩ : syracuseStep 5661197 = 2122949) B2122949
theorem B4243985 : Blo 1676038 4243985 := bstep (se 2 (by rfl) ⟨1591494, by rfl⟩ : syracuseStep 4243985 = 3182989) B3182989
theorem B2515475 : Blo 1676038 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B5448227 : Blo 1676038 5448227 := bstep (se 1 (by rfl) ⟨4086170, by rfl⟩ : syracuseStep 5448227 = 8172341) B8172341
theorem B2515505 : Blo 1676038 2515505 := bstep (se 2 (by rfl) ⟨943314, by rfl⟩ : syracuseStep 2515505 = 1886629) B1886629
theorem B2122291 : Blo 1676038 2122291 := bstep (se 1 (by rfl) ⟨1591718, by rfl⟩ : syracuseStep 2122291 = 3183437) B3183437
theorem B4244035 : Blo 1676038 4244035 := bstep (se 1 (by rfl) ⟨3183026, by rfl⟩ : syracuseStep 4244035 = 6366053) B6366053
theorem B2515523 : Blo 1676038 2515523 := bstep (se 1 (by rfl) ⟨1886642, by rfl⟩ : syracuseStep 2515523 = 3773285) B3773285
theorem B5661251 : Blo 1676038 5661251 := bstep (se 1 (by rfl) ⟨4245938, by rfl⟩ : syracuseStep 5661251 = 8491877) B8491877
theorem B2515553 : Blo 1676038 2515553 := bstep (se 2 (by rfl) ⟨943332, by rfl⟩ : syracuseStep 2515553 = 1886665) B1886665
theorem B12083825 : Blo 1676038 12083825 := bstep (se 2 (by rfl) ⟨4531434, by rfl⟩ : syracuseStep 12083825 = 9062869) B9062869
theorem B3580529 : Blo 1676038 3580529 := bstep (se 2 (by rfl) ⟨1342698, by rfl⟩ : syracuseStep 3580529 = 2685397) B2685397
theorem B2515571 : Blo 1676038 2515571 := bstep (se 1 (by rfl) ⟨1886678, by rfl⟩ : syracuseStep 2515571 = 3773357) B3773357
theorem B2515601 : Blo 1676038 2515601 := bstep (se 2 (by rfl) ⟨943350, by rfl⟩ : syracuseStep 2515601 = 1886701) B1886701
theorem B2515619 : Blo 1676038 2515619 := bstep (se 1 (by rfl) ⟨1886714, by rfl⟩ : syracuseStep 2515619 = 3773429) B3773429
theorem B2515649 : Blo 1676038 2515649 := bstep (se 2 (by rfl) ⟨943368, by rfl⟩ : syracuseStep 2515649 = 1886737) B1886737
theorem B4244177 : Blo 1676038 4244177 := bstep (se 2 (by rfl) ⟨1591566, by rfl⟩ : syracuseStep 4244177 = 3183133) B3183133
theorem B3826385 : Blo 1676038 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B2515667 : Blo 1676038 2515667 := bstep (se 1 (by rfl) ⟨1886750, by rfl⟩ : syracuseStep 2515667 = 3773501) B3773501
theorem B11469539 : Blo 1676038 11469539 := bstep (se 1 (by rfl) ⟨8602154, by rfl⟩ : syracuseStep 11469539 = 17204309) B17204309
theorem B8487665 : Blo 1676038 8487665 := bstep (se 2 (by rfl) ⟨3182874, by rfl⟩ : syracuseStep 8487665 = 6365749) B6365749
theorem B2515697 : Blo 1676038 2515697 := bstep (se 2 (by rfl) ⟨943386, by rfl⟩ : syracuseStep 2515697 = 1886773) B1886773
theorem B2515715 : Blo 1676038 2515715 := bstep (se 1 (by rfl) ⟨1886786, by rfl⟩ : syracuseStep 2515715 = 3773573) B3773573
theorem B3400451 : Blo 1676038 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B2515745 : Blo 1676038 2515745 := bstep (se 2 (by rfl) ⟨943404, by rfl⟩ : syracuseStep 2515745 = 1886809) B1886809
theorem B2515763 : Blo 1676038 2515763 := bstep (se 1 (by rfl) ⟨1886822, by rfl⟩ : syracuseStep 2515763 = 3773645) B3773645
theorem B2515793 : Blo 1676038 2515793 := bstep (se 2 (by rfl) ⟨943422, by rfl⟩ : syracuseStep 2515793 = 1886845) B1886845
theorem B5661521 : Blo 1676038 5661521 := bstep (se 2 (by rfl) ⟨2123070, by rfl⟩ : syracuseStep 5661521 = 4246141) B4246141
theorem B2515811 : Blo 1676038 2515811 := bstep (se 1 (by rfl) ⟨1886858, by rfl⟩ : syracuseStep 2515811 = 3773717) B3773717
theorem B2515841 : Blo 1676038 2515841 := bstep (se 2 (by rfl) ⟨943440, by rfl⟩ : syracuseStep 2515841 = 1886881) B1886881
theorem B7160717 : Blo 1676038 7160717 := bstep (se 3 (by rfl) ⟨1342634, by rfl⟩ : syracuseStep 7160717 = 2685269) B2685269
theorem B2515859 : Blo 1676038 2515859 := bstep (se 1 (by rfl) ⟨1886894, by rfl⟩ : syracuseStep 2515859 = 3773789) B3773789
theorem B2515889 : Blo 1676038 2515889 := bstep (se 2 (by rfl) ⟨943458, by rfl⟩ : syracuseStep 2515889 = 1886917) B1886917
theorem B2515907 : Blo 1676038 2515907 := bstep (se 1 (by rfl) ⟨1886930, by rfl⟩ : syracuseStep 2515907 = 3773861) B3773861
theorem B4031441 : Blo 1676038 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B2515937 : Blo 1676038 2515937 := bstep (se 2 (by rfl) ⟨943476, by rfl⟩ : syracuseStep 2515937 = 1886953) B1886953
theorem B2515955 : Blo 1676038 2515955 := bstep (se 1 (by rfl) ⟨1886966, by rfl⟩ : syracuseStep 2515955 = 3773933) B3773933
theorem B4842499 : Blo 1676038 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B6366221 : Blo 1676038 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B2515985 : Blo 1676038 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B3679267 : Blo 1676038 3679267 := bstep (se 1 (by rfl) ⟨2759450, by rfl⟩ : syracuseStep 3679267 = 5518901) B5518901
theorem B2122787 : Blo 1676038 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B2516003 : Blo 1676038 2516003 := bstep (se 1 (by rfl) ⟨1887002, by rfl⟩ : syracuseStep 2516003 = 3774005) B3774005
theorem B2516033 : Blo 1676038 2516033 := bstep (se 2 (by rfl) ⟨943512, by rfl⟩ : syracuseStep 2516033 = 1887025) B1887025
theorem B2516051 : Blo 1676038 2516051 := bstep (se 1 (by rfl) ⟨1887038, by rfl⟩ : syracuseStep 2516051 = 3774077) B3774077
theorem B3630179 : Blo 1676038 3630179 := bstep (se 1 (by rfl) ⟨2722634, by rfl⟩ : syracuseStep 3630179 = 5445269) B5445269
theorem B4777069 : Blo 1676038 4777069 := bstep (se 3 (by rfl) ⟨895700, by rfl⟩ : syracuseStep 4777069 = 1791401) B1791401
theorem B2516081 : Blo 1676038 2516081 := bstep (se 2 (by rfl) ⟨943530, by rfl⟩ : syracuseStep 2516081 = 1887061) B1887061
theorem B2516099 : Blo 1676038 2516099 := bstep (se 1 (by rfl) ⟨1887074, by rfl⟩ : syracuseStep 2516099 = 3774149) B3774149
theorem B25805965 : Blo 1676038 25805965 := bstep (se 3 (by rfl) ⟨4838618, by rfl⟩ : syracuseStep 25805965 = 9677237) B9677237
theorem B2868385 : Blo 1676038 2868385 := bstep (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) B2151289
theorem B2516129 : Blo 1676038 2516129 := bstep (se 2 (by rfl) ⟨943548, by rfl⟩ : syracuseStep 2516129 = 1887097) B1887097
theorem B2516147 : Blo 1676038 2516147 := bstep (se 1 (by rfl) ⟨1887110, by rfl⟩ : syracuseStep 2516147 = 3774221) B3774221
theorem B2516177 : Blo 1676038 2516177 := bstep (se 2 (by rfl) ⟨943566, by rfl⟩ : syracuseStep 2516177 = 1887133) B1887133
theorem B2516195 : Blo 1676038 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B10200305 : Blo 1676038 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B2516225 : Blo 1676038 2516225 := bstep (se 2 (by rfl) ⟨943584, by rfl⟩ : syracuseStep 2516225 = 1887169) B1887169
theorem B2516243 : Blo 1676038 2516243 := bstep (se 1 (by rfl) ⟨1887182, by rfl⟩ : syracuseStep 2516243 = 3774365) B3774365
theorem B2516273 : Blo 1676038 2516273 := bstep (se 2 (by rfl) ⟨943602, by rfl⟩ : syracuseStep 2516273 = 1887205) B1887205
theorem B2516291 : Blo 1676038 2516291 := bstep (se 1 (by rfl) ⟨1887218, by rfl⟩ : syracuseStep 2516291 = 3774437) B3774437
theorem B2516321 : Blo 1676038 2516321 := bstep (se 2 (by rfl) ⟨943620, by rfl⟩ : syracuseStep 2516321 = 1887241) B1887241
theorem B5662061 : Blo 1676038 5662061 := bstep (se 3 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 5662061 = 2123273) B2123273
theorem B2516339 : Blo 1676038 2516339 := bstep (se 1 (by rfl) ⟨1887254, by rfl⟩ : syracuseStep 2516339 = 3774509) B3774509
theorem B2516369 : Blo 1676038 2516369 := bstep (se 2 (by rfl) ⟨943638, by rfl⟩ : syracuseStep 2516369 = 1887277) B1887277
theorem B1885603 : Blo 1676038 1885603 := bstep (se 1 (by rfl) ⟨1414202, by rfl⟩ : syracuseStep 1885603 = 2828405) B2828405
theorem B2516387 : Blo 1676038 2516387 := bstep (se 1 (by rfl) ⟨1887290, by rfl⟩ : syracuseStep 2516387 = 3774581) B3774581
theorem B5662115 : Blo 1676038 5662115 := bstep (se 1 (by rfl) ⟨4246586, by rfl⟩ : syracuseStep 5662115 = 8493173) B8493173
theorem B2516417 : Blo 1676038 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B2516435 : Blo 1676038 2516435 := bstep (se 1 (by rfl) ⟨1887326, by rfl⟩ : syracuseStep 2516435 = 3774653) B3774653
theorem B5375459 : Blo 1676038 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B4531697 : Blo 1676038 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B2516465 : Blo 1676038 2516465 := bstep (se 2 (by rfl) ⟨943674, by rfl⟩ : syracuseStep 2516465 = 1887349) B1887349
theorem B2516483 : Blo 1676038 2516483 := bstep (se 1 (by rfl) ⟨1887362, by rfl⟩ : syracuseStep 2516483 = 3774725) B3774725
theorem B2516513 : Blo 1676038 2516513 := bstep (se 2 (by rfl) ⟨943692, by rfl⟩ : syracuseStep 2516513 = 1887385) B1887385
theorem B1885747 : Blo 1676038 1885747 := bstep (se 1 (by rfl) ⟨1414310, by rfl⟩ : syracuseStep 1885747 = 2828621) B2828621
theorem B2516531 : Blo 1676038 2516531 := bstep (se 1 (by rfl) ⟨1887398, by rfl⟩ : syracuseStep 2516531 = 3774797) B3774797
theorem B2516561 : Blo 1676038 2516561 := bstep (se 2 (by rfl) ⟨943710, by rfl⟩ : syracuseStep 2516561 = 1887421) B1887421
theorem B2516579 : Blo 1676038 2516579 := bstep (se 1 (by rfl) ⟨1887434, by rfl⟩ : syracuseStep 2516579 = 3774869) B3774869
theorem B2516609 : Blo 1676038 2516609 := bstep (se 2 (by rfl) ⟨943728, by rfl⟩ : syracuseStep 2516609 = 1887457) B1887457
theorem B2516627 : Blo 1676038 2516627 := bstep (se 1 (by rfl) ⟨1887470, by rfl⟩ : syracuseStep 2516627 = 3774941) B3774941
theorem B4245169 : Blo 1676038 4245169 := bstep (se 2 (by rfl) ⟨1591938, by rfl⟩ : syracuseStep 4245169 = 3183877) B3183877
theorem B5662385 : Blo 1676038 5662385 := bstep (se 2 (by rfl) ⟨2123394, by rfl⟩ : syracuseStep 5662385 = 4246789) B4246789
theorem B2516657 : Blo 1676038 2516657 := bstep (se 2 (by rfl) ⟨943746, by rfl⟩ : syracuseStep 2516657 = 1887493) B1887493
theorem B1885891 : Blo 1676038 1885891 := bstep (se 1 (by rfl) ⟨1414418, by rfl⟩ : syracuseStep 1885891 = 2828837) B2828837
theorem B2516675 : Blo 1676038 2516675 := bstep (se 1 (by rfl) ⟨1887506, by rfl⟩ : syracuseStep 2516675 = 3775013) B3775013
theorem B2516705 : Blo 1676038 2516705 := bstep (se 2 (by rfl) ⟨943764, by rfl⟩ : syracuseStep 2516705 = 1887529) B1887529
theorem B2123491 : Blo 1676038 2123491 := bstep (se 1 (by rfl) ⟨1592618, by rfl⟩ : syracuseStep 2123491 = 3185237) B3185237
theorem B2516723 : Blo 1676038 2516723 := bstep (se 1 (by rfl) ⟨1887542, by rfl⟩ : syracuseStep 2516723 = 3775085) B3775085
theorem B2516753 : Blo 1676038 2516753 := bstep (se 2 (by rfl) ⟨943782, by rfl⟩ : syracuseStep 2516753 = 1887565) B1887565
theorem B2516771 : Blo 1676038 2516771 := bstep (se 1 (by rfl) ⟨1887578, by rfl⟩ : syracuseStep 2516771 = 3775157) B3775157
theorem B6367025 : Blo 1676038 6367025 := bstep (se 2 (by rfl) ⟨2387634, by rfl⟩ : syracuseStep 6367025 = 4775269) B4775269
theorem B2516801 : Blo 1676038 2516801 := bstep (se 2 (by rfl) ⟨943800, by rfl⟩ : syracuseStep 2516801 = 1887601) B1887601
theorem B2123587 : Blo 1676038 2123587 := bstep (se 1 (by rfl) ⟨1592690, by rfl⟩ : syracuseStep 2123587 = 3185381) B3185381
theorem B1886035 : Blo 1676038 1886035 := bstep (se 1 (by rfl) ⟨1414526, by rfl⟩ : syracuseStep 1886035 = 2829053) B2829053
theorem B2516819 : Blo 1676038 2516819 := bstep (se 1 (by rfl) ⟨1887614, by rfl⟩ : syracuseStep 2516819 = 3775229) B3775229
theorem B2516849 : Blo 1676038 2516849 := bstep (se 2 (by rfl) ⟨943818, by rfl⟩ : syracuseStep 2516849 = 1887637) B1887637
theorem B2516867 : Blo 1676038 2516867 := bstep (se 1 (by rfl) ⟨1887650, by rfl⟩ : syracuseStep 2516867 = 3775301) B3775301
theorem B2516897 : Blo 1676038 2516897 := bstep (se 2 (by rfl) ⟨943836, by rfl⟩ : syracuseStep 2516897 = 1887673) B1887673
theorem B2516915 : Blo 1676038 2516915 := bstep (se 1 (by rfl) ⟨1887686, by rfl⟩ : syracuseStep 2516915 = 3775373) B3775373
theorem B4245443 : Blo 1676038 4245443 := bstep (se 1 (by rfl) ⟨3184082, by rfl⟩ : syracuseStep 4245443 = 6368165) B6368165
theorem B2516945 : Blo 1676038 2516945 := bstep (se 2 (by rfl) ⟨943854, by rfl⟩ : syracuseStep 2516945 = 1887709) B1887709
theorem B1886179 : Blo 1676038 1886179 := bstep (se 1 (by rfl) ⟨1414634, by rfl⟩ : syracuseStep 1886179 = 2829269) B2829269
theorem B2516963 : Blo 1676038 2516963 := bstep (se 1 (by rfl) ⟨1887722, by rfl⟩ : syracuseStep 2516963 = 3775445) B3775445
theorem B4843505 : Blo 1676038 4843505 := bstep (se 2 (by rfl) ⟨1816314, by rfl⟩ : syracuseStep 4843505 = 3632629) B3632629
theorem B2516993 : Blo 1676038 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B2517011 : Blo 1676038 2517011 := bstep (se 1 (by rfl) ⟨1887758, by rfl⟩ : syracuseStep 2517011 = 3775517) B3775517
theorem B2549809 : Blo 1676038 2549809 := bstep (se 2 (by rfl) ⟨956178, by rfl⟩ : syracuseStep 2549809 = 1912357) B1912357
theorem B2517041 : Blo 1676038 2517041 := bstep (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) B1887781
theorem B14526533 : Blo 1676038 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B2828371 : Blo 1676038 2828371 := bstep (se 1 (by rfl) ⟨2121278, by rfl⟩ : syracuseStep 2828371 = 4242557) B4242557
theorem B1886323 : Blo 1676038 1886323 := bstep (se 1 (by rfl) ⟨1414742, by rfl⟩ : syracuseStep 1886323 = 2829485) B2829485
theorem B4245635 : Blo 1676038 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B4778129 : Blo 1676038 4778129 := bstep (se 2 (by rfl) ⟨1791798, by rfl⟩ : syracuseStep 4778129 = 3583597) B3583597
theorem B8489123 : Blo 1676038 8489123 := bstep (se 1 (by rfl) ⟨6366842, by rfl⟩ : syracuseStep 8489123 = 12733685) B12733685
theorem B5662925 : Blo 1676038 5662925 := bstep (se 3 (by rfl) ⟨1061798, by rfl⟩ : syracuseStep 5662925 = 2123597) B2123597
theorem B2828513 : Blo 1676038 2828513 := bstep (se 2 (by rfl) ⟨1060692, by rfl⟩ : syracuseStep 2828513 = 2121385) B2121385
theorem B28649699 : Blo 1676038 28649699 := bstep (se 1 (by rfl) ⟨21487274, by rfl⟩ : syracuseStep 28649699 = 42974549) B42974549
theorem B64481507 : Blo 1676038 64481507 := bstep (se 1 (by rfl) ⟨48361130, by rfl⟩ : syracuseStep 64481507 = 96722261) B96722261
theorem B1886467 : Blo 1676038 1886467 := bstep (se 1 (by rfl) ⟨1414850, by rfl⟩ : syracuseStep 1886467 = 2829701) B2829701
theorem B2181379 : Blo 1676038 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B5662979 : Blo 1676038 5662979 := bstep (se 1 (by rfl) ⟨4247234, by rfl⟩ : syracuseStep 5662979 = 8494469) B8494469
theorem B3631409 : Blo 1676038 3631409 := bstep (se 2 (by rfl) ⟨1361778, by rfl⟩ : syracuseStep 3631409 = 2723557) B2723557
theorem B4532561 : Blo 1676038 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B2828641 : Blo 1676038 2828641 := bstep (se 2 (by rfl) ⟨1060740, by rfl⟩ : syracuseStep 2828641 = 2121481) B2121481
theorem B2828675 : Blo 1676038 2828675 := bstep (se 1 (by rfl) ⟨2121506, by rfl⟩ : syracuseStep 2828675 = 4243013) B4243013
theorem B1886611 : Blo 1676038 1886611 := bstep (se 1 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 1886611 = 2829917) B2829917
theorem B10742179 : Blo 1676038 10742179 := bstep (se 1 (by rfl) ⟨8056634, by rfl⟩ : syracuseStep 10742179 = 16113269) B16113269
theorem B7162289 : Blo 1676038 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B6367693 : Blo 1676038 6367693 := bstep (se 3 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 6367693 = 2387885) B2387885
theorem B10201571 : Blo 1676038 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B8063459 : Blo 1676038 8063459 := bstep (se 1 (by rfl) ⟨6047594, by rfl⟩ : syracuseStep 8063459 = 12095189) B12095189
theorem B2828803 : Blo 1676038 2828803 := bstep (se 1 (by rfl) ⟨2121602, by rfl⟩ : syracuseStep 2828803 = 4243205) B4243205
theorem B5663249 : Blo 1676038 5663249 := bstep (se 2 (by rfl) ⟨2123718, by rfl⟩ : syracuseStep 5663249 = 4247437) B4247437
theorem B1886755 : Blo 1676038 1886755 := bstep (se 1 (by rfl) ⟨1415066, by rfl⟩ : syracuseStep 1886755 = 2830133) B2830133
theorem B27191861 : Blo 1676038 27191861 := bstep (se 5 (by rfl) ⟨1274618, by rfl⟩ : syracuseStep 27191861 = 2549237) B2549237
theorem B2386513 : Blo 1676038 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B4082275 : Blo 1676038 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B2828945 : Blo 1676038 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B8063651 : Blo 1676038 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B9063089 : Blo 1676038 9063089 := bstep (se 2 (by rfl) ⟨3398658, by rfl⟩ : syracuseStep 9063089 = 6797317) B6797317
theorem B1886899 : Blo 1676038 1886899 := bstep (se 1 (by rfl) ⟨1415174, by rfl⟩ : syracuseStep 1886899 = 2830349) B2830349
theorem B9546437 : Blo 1676038 9546437 := bstep (se 4 (by rfl) ⟨894978, by rfl⟩ : syracuseStep 9546437 = 1789957) B1789957
theorem B3771089 : Blo 1676038 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B3771107 : Blo 1676038 3771107 := bstep (se 1 (by rfl) ⟨2828330, by rfl⟩ : syracuseStep 3771107 = 5656661) B5656661
theorem B2829073 : Blo 1676038 2829073 := bstep (se 2 (by rfl) ⟨1060902, by rfl⟩ : syracuseStep 2829073 = 2121805) B2121805
theorem B2829107 : Blo 1676038 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B1887043 : Blo 1676038 1887043 := bstep (se 1 (by rfl) ⟨1415282, by rfl⟩ : syracuseStep 1887043 = 2830565) B2830565
theorem B4533101 : Blo 1676038 4533101 := bstep (se 3 (by rfl) ⟨849956, by rfl⟩ : syracuseStep 4533101 = 1699913) B1699913
theorem B2386849 : Blo 1676038 2386849 := bstep (se 2 (by rfl) ⟨895068, by rfl⟩ : syracuseStep 2386849 = 1790137) B1790137
theorem B5098403 : Blo 1676038 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B2829235 : Blo 1676038 2829235 := bstep (se 1 (by rfl) ⟨2121926, by rfl⟩ : syracuseStep 2829235 = 4243853) B4243853
theorem B8489933 : Blo 1676038 8489933 := bstep (se 3 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 8489933 = 3183725) B3183725
theorem B1887187 : Blo 1676038 1887187 := bstep (se 1 (by rfl) ⟨1415390, by rfl⟩ : syracuseStep 1887187 = 2830781) B2830781
theorem B3771377 : Blo 1676038 3771377 := bstep (se 2 (by rfl) ⟨1414266, by rfl⟩ : syracuseStep 3771377 = 2828533) B2828533
theorem B3771395 : Blo 1676038 3771395 := bstep (se 1 (by rfl) ⟨2828546, by rfl⟩ : syracuseStep 3771395 = 5657093) B5657093
theorem B1911827 : Blo 1676038 1911827 := bstep (se 1 (by rfl) ⟨1433870, by rfl⟩ : syracuseStep 1911827 = 2867741) B2867741
theorem B2583587 : Blo 1676038 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B4246577 : Blo 1676038 4246577 := bstep (se 2 (by rfl) ⟨1592466, by rfl⟩ : syracuseStep 4246577 = 3184933) B3184933
theorem B2829377 : Blo 1676038 2829377 := bstep (se 2 (by rfl) ⟨1061016, by rfl⟩ : syracuseStep 2829377 = 2122033) B2122033
theorem B1887331 : Blo 1676038 1887331 := bstep (se 1 (by rfl) ⟨1415498, by rfl⟩ : syracuseStep 1887331 = 2830997) B2830997
theorem B4246627 : Blo 1676038 4246627 := bstep (se 1 (by rfl) ⟨3184970, by rfl⟩ : syracuseStep 4246627 = 6369941) B6369941
theorem B9546893 : Blo 1676038 9546893 := bstep (se 3 (by rfl) ⟨1790042, by rfl⟩ : syracuseStep 9546893 = 3580085) B3580085
theorem B2829505 : Blo 1676038 2829505 := bstep (se 2 (by rfl) ⟨1061064, by rfl⟩ : syracuseStep 2829505 = 2122129) B2122129
theorem B2829539 : Blo 1676038 2829539 := bstep (se 1 (by rfl) ⟨2122154, by rfl⟩ : syracuseStep 2829539 = 4244309) B4244309
theorem B6368483 : Blo 1676038 6368483 := bstep (se 1 (by rfl) ⟨4776362, by rfl⟩ : syracuseStep 6368483 = 9552725) B9552725
theorem B9555185 : Blo 1676038 9555185 := bstep (se 2 (by rfl) ⟨3583194, by rfl⟩ : syracuseStep 9555185 = 7166389) B7166389
theorem B4246769 : Blo 1676038 4246769 := bstep (se 2 (by rfl) ⟨1592538, by rfl⟩ : syracuseStep 4246769 = 3185077) B3185077
theorem B1887475 : Blo 1676038 1887475 := bstep (se 1 (by rfl) ⟨1415606, by rfl⟩ : syracuseStep 1887475 = 2831213) B2831213
theorem B2551025 : Blo 1676038 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B21482765 : Blo 1676038 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B3771665 : Blo 1676038 3771665 := bstep (se 2 (by rfl) ⟨1414374, by rfl⟩ : syracuseStep 3771665 = 2828749) B2828749
theorem B3771683 : Blo 1676038 3771683 := bstep (se 1 (by rfl) ⟨2828762, by rfl⟩ : syracuseStep 3771683 = 5657525) B5657525
theorem B2829667 : Blo 1676038 2829667 := bstep (se 1 (by rfl) ⟨2122250, by rfl⟩ : syracuseStep 2829667 = 4244501) B4244501
theorem B1699187 : Blo 1676038 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B1887619 : Blo 1676038 1887619 := bstep (se 1 (by rfl) ⟨1415714, by rfl⟩ : syracuseStep 1887619 = 2831429) B2831429
theorem B10751429 : Blo 1676038 10751429 := bstep (se 4 (by rfl) ⟨1007946, by rfl⟩ : syracuseStep 10751429 = 2015893) B2015893
theorem B2387441 : Blo 1676038 2387441 := bstep (se 2 (by rfl) ⟨895290, by rfl⟩ : syracuseStep 2387441 = 1790581) B1790581
theorem B2829809 : Blo 1676038 2829809 := bstep (se 2 (by rfl) ⟨1061178, by rfl⟩ : syracuseStep 2829809 = 2122357) B2122357
theorem B1887763 : Blo 1676038 1887763 := bstep (se 1 (by rfl) ⟨1415822, by rfl⟩ : syracuseStep 1887763 = 2831645) B2831645
theorem B3771953 : Blo 1676038 3771953 := bstep (se 2 (by rfl) ⟨1414482, by rfl⟩ : syracuseStep 3771953 = 2828965) B2828965
theorem B3771971 : Blo 1676038 3771971 := bstep (se 1 (by rfl) ⟨2828978, by rfl⟩ : syracuseStep 3771971 = 5657957) B5657957
theorem B3182161 : Blo 1676038 3182161 := bstep (se 2 (by rfl) ⟨1193310, by rfl⟩ : syracuseStep 3182161 = 2386621) B2386621
theorem B2829937 : Blo 1676038 2829937 := bstep (se 2 (by rfl) ⟨1061226, by rfl⟩ : syracuseStep 2829937 = 2122453) B2122453
theorem B2829971 : Blo 1676038 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B3182321 : Blo 1676038 3182321 := bstep (se 2 (by rfl) ⟨1193370, by rfl⟩ : syracuseStep 3182321 = 2386741) B2386741
theorem B2830099 : Blo 1676038 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B3772241 : Blo 1676038 3772241 := bstep (se 2 (by rfl) ⟨1414590, by rfl⟩ : syracuseStep 3772241 = 2829181) B2829181
theorem B3772259 : Blo 1676038 3772259 := bstep (se 1 (by rfl) ⟨2829194, by rfl⟩ : syracuseStep 3772259 = 5658389) B5658389
theorem B6369137 : Blo 1676038 6369137 := bstep (se 2 (by rfl) ⟨2388426, by rfl⟩ : syracuseStep 6369137 = 4776853) B4776853
theorem B2830241 : Blo 1676038 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B2453441 : Blo 1676038 2453441 := bstep (se 2 (by rfl) ⟨920040, by rfl⟩ : syracuseStep 2453441 = 1840081) B1840081
theorem B2723777 : Blo 1676038 2723777 := bstep (se 2 (by rfl) ⟨1021416, by rfl⟩ : syracuseStep 2723777 = 2042833) B2042833
theorem B2387971 : Blo 1676038 2387971 := bstep (se 1 (by rfl) ⟨1790978, by rfl⟩ : syracuseStep 2387971 = 3581957) B3581957
theorem B2830369 : Blo 1676038 2830369 := bstep (se 2 (by rfl) ⟨1061388, by rfl⟩ : syracuseStep 2830369 = 2122777) B2122777
theorem B2830403 : Blo 1676038 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B3772529 : Blo 1676038 3772529 := bstep (se 2 (by rfl) ⟨1414698, by rfl⟩ : syracuseStep 3772529 = 2829397) B2829397
theorem B3182723 : Blo 1676038 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B3772547 : Blo 1676038 3772547 := bstep (se 1 (by rfl) ⟨2829410, by rfl⟩ : syracuseStep 3772547 = 5658821) B5658821
theorem B2830531 : Blo 1676038 2830531 := bstep (se 1 (by rfl) ⟨2122898, by rfl⟩ : syracuseStep 2830531 = 4245797) B4245797
theorem B6041827 : Blo 1676038 6041827 := bstep (se 1 (by rfl) ⟨4531370, by rfl⟩ : syracuseStep 6041827 = 9062741) B9062741
theorem B5656877 : Blo 1676038 5656877 := bstep (se 3 (by rfl) ⟨1060664, by rfl⟩ : syracuseStep 5656877 = 2121329) B2121329
theorem B2830673 : Blo 1676038 2830673 := bstep (se 2 (by rfl) ⟨1061502, by rfl⟩ : syracuseStep 2830673 = 2123005) B2123005
theorem B2388307 : Blo 1676038 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B5656931 : Blo 1676038 5656931 := bstep (se 1 (by rfl) ⟨4242698, by rfl⟩ : syracuseStep 5656931 = 8485397) B8485397
theorem B14332301 : Blo 1676038 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B3772817 : Blo 1676038 3772817 := bstep (se 2 (by rfl) ⟨1414806, by rfl⟩ : syracuseStep 3772817 = 2829613) B2829613
theorem B3772835 : Blo 1676038 3772835 := bstep (se 1 (by rfl) ⟨2829626, by rfl⟩ : syracuseStep 3772835 = 5659253) B5659253
theorem B4084145 : Blo 1676038 4084145 := bstep (se 2 (by rfl) ⟨1531554, by rfl⟩ : syracuseStep 4084145 = 3063109) B3063109
theorem B2830801 : Blo 1676038 2830801 := bstep (se 2 (by rfl) ⟨1061550, by rfl⟩ : syracuseStep 2830801 = 2123101) B2123101
theorem B2830835 : Blo 1676038 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B5657201 : Blo 1676038 5657201 := bstep (se 2 (by rfl) ⟨2121450, by rfl⟩ : syracuseStep 5657201 = 4242901) B4242901
theorem B2830963 : Blo 1676038 2830963 := bstep (se 1 (by rfl) ⟨2123222, by rfl⟩ : syracuseStep 2830963 = 4246445) B4246445
theorem B9556643 : Blo 1676038 9556643 := bstep (se 1 (by rfl) ⟨7167482, by rfl⟩ : syracuseStep 9556643 = 14334965) B14334965
theorem B6042289 : Blo 1676038 6042289 := bstep (se 2 (by rfl) ⟨2265858, by rfl⟩ : syracuseStep 6042289 = 4531717) B4531717
theorem B3773105 : Blo 1676038 3773105 := bstep (se 2 (by rfl) ⟨1414914, by rfl⟩ : syracuseStep 3773105 = 2829829) B2829829
theorem B3773123 : Blo 1676038 3773123 := bstep (se 1 (by rfl) ⟨2829842, by rfl⟩ : syracuseStep 3773123 = 5659685) B5659685
theorem B4838093 : Blo 1676038 4838093 := bstep (se 3 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 4838093 = 1814285) B1814285
theorem B2831105 : Blo 1676038 2831105 := bstep (se 2 (by rfl) ⟨1061664, by rfl⟩ : syracuseStep 2831105 = 2123329) B2123329
theorem B2421505 : Blo 1676038 2421505 := bstep (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) B1816129
theorem B1676051 : Blo 1676038 1676051 := bstep (se 1 (by rfl) ⟨1257038, by rfl⟩ : syracuseStep 1676051 = 2514077) B2514077
theorem B1676067 : Blo 1676038 1676067 := bstep (se 1 (by rfl) ⟨1257050, by rfl⟩ : syracuseStep 1676067 = 2514101) B2514101
theorem B1676083 : Blo 1676038 1676083 := bstep (se 1 (by rfl) ⟨1257062, by rfl⟩ : syracuseStep 1676083 = 2514125) B2514125
theorem B1676099 : Blo 1676038 1676099 := bstep (se 1 (by rfl) ⟨1257074, by rfl⟩ : syracuseStep 1676099 = 2514149) B2514149
theorem B5239619 : Blo 1676038 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B7164749 : Blo 1676038 7164749 := bstep (se 3 (by rfl) ⟨1343390, by rfl⟩ : syracuseStep 7164749 = 2686781) B2686781
theorem B1676115 : Blo 1676038 1676115 := bstep (se 1 (by rfl) ⟨1257086, by rfl⟩ : syracuseStep 1676115 = 2514173) B2514173
theorem B1676131 : Blo 1676038 1676131 := bstep (se 1 (by rfl) ⟨1257098, by rfl⟩ : syracuseStep 1676131 = 2514197) B2514197
theorem B1676147 : Blo 1676038 1676147 := bstep (se 1 (by rfl) ⟨1257110, by rfl⟩ : syracuseStep 1676147 = 2514221) B2514221
theorem B2831233 : Blo 1676038 2831233 := bstep (se 2 (by rfl) ⟨1061712, by rfl⟩ : syracuseStep 2831233 = 2123425) B2123425
theorem B2388865 : Blo 1676038 2388865 := bstep (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) B1791649
theorem B1676163 : Blo 1676038 1676163 := bstep (se 1 (by rfl) ⟨1257122, by rfl⟩ : syracuseStep 1676163 = 2514245) B2514245
theorem B1676179 : Blo 1676038 1676179 := bstep (se 1 (by rfl) ⟨1257134, by rfl⟩ : syracuseStep 1676179 = 2514269) B2514269
theorem B1676195 : Blo 1676038 1676195 := bstep (se 1 (by rfl) ⟨1257146, by rfl⟩ : syracuseStep 1676195 = 2514293) B2514293
theorem B2831267 : Blo 1676038 2831267 := bstep (se 1 (by rfl) ⟨2123450, by rfl⟩ : syracuseStep 2831267 = 4246901) B4246901
theorem B2388899 : Blo 1676038 2388899 := bstep (se 1 (by rfl) ⟨1791674, by rfl⟩ : syracuseStep 2388899 = 3583349) B3583349
theorem B1676211 : Blo 1676038 1676211 := bstep (se 1 (by rfl) ⟨1257158, by rfl⟩ : syracuseStep 1676211 = 2514317) B2514317
theorem B1676227 : Blo 1676038 1676227 := bstep (se 1 (by rfl) ⟨1257170, by rfl⟩ : syracuseStep 1676227 = 2514341) B2514341
theorem B3773393 : Blo 1676038 3773393 := bstep (se 2 (by rfl) ⟨1415022, by rfl⟩ : syracuseStep 3773393 = 2830045) B2830045
theorem B1676243 : Blo 1676038 1676243 := bstep (se 1 (by rfl) ⟨1257182, by rfl⟩ : syracuseStep 1676243 = 2514365) B2514365
theorem B1676259 : Blo 1676038 1676259 := bstep (se 1 (by rfl) ⟨1257194, by rfl⟩ : syracuseStep 1676259 = 2514389) B2514389
theorem B3773411 : Blo 1676038 3773411 := bstep (se 1 (by rfl) ⟨2830058, by rfl⟩ : syracuseStep 3773411 = 5660117) B5660117
theorem B1676275 : Blo 1676038 1676275 := bstep (se 1 (by rfl) ⟨1257206, by rfl⟩ : syracuseStep 1676275 = 2514413) B2514413
theorem B1676291 : Blo 1676038 1676291 := bstep (se 1 (by rfl) ⟨1257218, by rfl⟩ : syracuseStep 1676291 = 2514437) B2514437
theorem B3183619 : Blo 1676038 3183619 := bstep (se 1 (by rfl) ⟨2387714, by rfl⟩ : syracuseStep 3183619 = 4775429) B4775429
theorem B1676307 : Blo 1676038 1676307 := bstep (se 1 (by rfl) ⟨1257230, by rfl⟩ : syracuseStep 1676307 = 2514461) B2514461
theorem B4838435 : Blo 1676038 4838435 := bstep (se 1 (by rfl) ⟨3628826, by rfl⟩ : syracuseStep 4838435 = 7257653) B7257653
theorem B1676323 : Blo 1676038 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B2831395 : Blo 1676038 2831395 := bstep (se 1 (by rfl) ⟨2123546, by rfl⟩ : syracuseStep 2831395 = 4247093) B4247093
theorem B1676339 : Blo 1676038 1676339 := bstep (se 1 (by rfl) ⟨1257254, by rfl⟩ : syracuseStep 1676339 = 2514509) B2514509
theorem B1676355 : Blo 1676038 1676355 := bstep (se 1 (by rfl) ⟨1257266, by rfl⟩ : syracuseStep 1676355 = 2514533) B2514533
theorem B4772945 : Blo 1676038 4772945 := bstep (se 2 (by rfl) ⟨1789854, by rfl⟩ : syracuseStep 4772945 = 3579709) B3579709
theorem B1676371 : Blo 1676038 1676371 := bstep (se 1 (by rfl) ⟨1257278, by rfl⟩ : syracuseStep 1676371 = 2514557) B2514557
theorem B1676387 : Blo 1676038 1676387 := bstep (se 1 (by rfl) ⟨1257290, by rfl⟩ : syracuseStep 1676387 = 2514581) B2514581
theorem B1676403 : Blo 1676038 1676403 := bstep (se 1 (by rfl) ⟨1257302, by rfl⟩ : syracuseStep 1676403 = 2514605) B2514605
theorem B1676419 : Blo 1676038 1676419 := bstep (se 1 (by rfl) ⟨1257314, by rfl⟩ : syracuseStep 1676419 = 2514629) B2514629
theorem B4084867 : Blo 1676038 4084867 := bstep (se 1 (by rfl) ⟨3063650, by rfl⟩ : syracuseStep 4084867 = 6127301) B6127301
theorem B5657741 : Blo 1676038 5657741 := bstep (se 3 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 5657741 = 2121653) B2121653
theorem B10744973 : Blo 1676038 10744973 := bstep (se 3 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 10744973 = 4029365) B4029365
theorem B12735629 : Blo 1676038 12735629 := bstep (se 3 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 12735629 = 4775861) B4775861
theorem B1676435 : Blo 1676038 1676435 := bstep (se 1 (by rfl) ⟨1257326, by rfl⟩ : syracuseStep 1676435 = 2514653) B2514653
theorem B1676451 : Blo 1676038 1676451 := bstep (se 1 (by rfl) ⟨1257338, by rfl⟩ : syracuseStep 1676451 = 2514677) B2514677
theorem B3183779 : Blo 1676038 3183779 := bstep (se 1 (by rfl) ⟨2387834, by rfl⟩ : syracuseStep 3183779 = 4775669) B4775669
theorem B7165091 : Blo 1676038 7165091 := bstep (se 1 (by rfl) ⟨5373818, by rfl⟩ : syracuseStep 7165091 = 10747637) B10747637
theorem B2831537 : Blo 1676038 2831537 := bstep (se 2 (by rfl) ⟨1061826, by rfl⟩ : syracuseStep 2831537 = 2123653) B2123653
theorem B1676467 : Blo 1676038 1676467 := bstep (se 1 (by rfl) ⟨1257350, by rfl⟩ : syracuseStep 1676467 = 2514701) B2514701
theorem B5657795 : Blo 1676038 5657795 := bstep (se 1 (by rfl) ⟨4243346, by rfl⟩ : syracuseStep 5657795 = 8486693) B8486693
theorem B1676483 : Blo 1676038 1676483 := bstep (se 1 (by rfl) ⟨1257362, by rfl⟩ : syracuseStep 1676483 = 2514725) B2514725
theorem B1676499 : Blo 1676038 1676499 := bstep (se 1 (by rfl) ⟨1257374, by rfl⟩ : syracuseStep 1676499 = 2514749) B2514749
theorem B1676515 : Blo 1676038 1676515 := bstep (se 1 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 1676515 = 2514773) B2514773
theorem B3773681 : Blo 1676038 3773681 := bstep (se 2 (by rfl) ⟨1415130, by rfl⟩ : syracuseStep 3773681 = 2830261) B2830261
theorem B1676531 : Blo 1676038 1676531 := bstep (se 1 (by rfl) ⟨1257398, by rfl⟩ : syracuseStep 1676531 = 2514797) B2514797
theorem B1676547 : Blo 1676038 1676547 := bstep (se 1 (by rfl) ⟨1257410, by rfl⟩ : syracuseStep 1676547 = 2514821) B2514821
theorem B3773699 : Blo 1676038 3773699 := bstep (se 1 (by rfl) ⟨2830274, by rfl⟩ : syracuseStep 3773699 = 5660549) B5660549
theorem B1676563 : Blo 1676038 1676563 := bstep (se 1 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 1676563 = 2514845) B2514845
theorem B1676579 : Blo 1676038 1676579 := bstep (se 1 (by rfl) ⟨1257434, by rfl⟩ : syracuseStep 1676579 = 2514869) B2514869
theorem B6370595 : Blo 1676038 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B6370609 : Blo 1676038 6370609 := bstep (se 2 (by rfl) ⟨2388978, by rfl⟩ : syracuseStep 6370609 = 4777957) B4777957
theorem B2831665 : Blo 1676038 2831665 := bstep (se 2 (by rfl) ⟨1061874, by rfl⟩ : syracuseStep 2831665 = 2123749) B2123749
theorem B1676595 : Blo 1676038 1676595 := bstep (se 1 (by rfl) ⟨1257446, by rfl⟩ : syracuseStep 1676595 = 2514893) B2514893
theorem B1676611 : Blo 1676038 1676611 := bstep (se 1 (by rfl) ⟨1257458, by rfl⟩ : syracuseStep 1676611 = 2514917) B2514917
theorem B1676627 : Blo 1676038 1676627 := bstep (se 1 (by rfl) ⟨1257470, by rfl⟩ : syracuseStep 1676627 = 2514941) B2514941
theorem B1676643 : Blo 1676038 1676643 := bstep (se 1 (by rfl) ⟨1257482, by rfl⟩ : syracuseStep 1676643 = 2514965) B2514965
theorem B5748077 : Blo 1676038 5748077 := bstep (se 3 (by rfl) ⟨1077764, by rfl⟩ : syracuseStep 5748077 = 2155529) B2155529
theorem B1676659 : Blo 1676038 1676659 := bstep (se 1 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 1676659 = 2514989) B2514989
theorem B1676675 : Blo 1676038 1676675 := bstep (se 1 (by rfl) ⟨1257506, by rfl⟩ : syracuseStep 1676675 = 2515013) B2515013
theorem B1676691 : Blo 1676038 1676691 := bstep (se 1 (by rfl) ⟨1257518, by rfl⟩ : syracuseStep 1676691 = 2515037) B2515037
theorem B1676707 : Blo 1676038 1676707 := bstep (se 1 (by rfl) ⟨1257530, by rfl⟩ : syracuseStep 1676707 = 2515061) B2515061
theorem B1676723 : Blo 1676038 1676723 := bstep (se 1 (by rfl) ⟨1257542, by rfl⟩ : syracuseStep 1676723 = 2515085) B2515085
theorem B1676739 : Blo 1676038 1676739 := bstep (se 1 (by rfl) ⟨1257554, by rfl⟩ : syracuseStep 1676739 = 2515109) B2515109
theorem B5658065 : Blo 1676038 5658065 := bstep (se 2 (by rfl) ⟨2121774, by rfl⟩ : syracuseStep 5658065 = 4243549) B4243549
theorem B1676755 : Blo 1676038 1676755 := bstep (se 1 (by rfl) ⟨1257566, by rfl⟩ : syracuseStep 1676755 = 2515133) B2515133
theorem B1676771 : Blo 1676038 1676771 := bstep (se 1 (by rfl) ⟨1257578, by rfl⟩ : syracuseStep 1676771 = 2515157) B2515157
theorem B1676787 : Blo 1676038 1676787 := bstep (se 1 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 1676787 = 2515181) B2515181
theorem B1676803 : Blo 1676038 1676803 := bstep (se 1 (by rfl) ⟨1257602, by rfl⟩ : syracuseStep 1676803 = 2515205) B2515205
theorem B5371409 : Blo 1676038 5371409 := bstep (se 2 (by rfl) ⟨2014278, by rfl⟩ : syracuseStep 5371409 = 4028557) B4028557
theorem B3773969 : Blo 1676038 3773969 := bstep (se 2 (by rfl) ⟨1415238, by rfl⟩ : syracuseStep 3773969 = 2830477) B2830477
theorem B1676819 : Blo 1676038 1676819 := bstep (se 1 (by rfl) ⟨1257614, by rfl⟩ : syracuseStep 1676819 = 2515229) B2515229
theorem B3020323 : Blo 1676038 3020323 := bstep (se 1 (by rfl) ⟨2265242, by rfl⟩ : syracuseStep 3020323 = 4530485) B4530485
theorem B1676835 : Blo 1676038 1676835 := bstep (se 1 (by rfl) ⟨1257626, by rfl⟩ : syracuseStep 1676835 = 2515253) B2515253
theorem B3773987 : Blo 1676038 3773987 := bstep (se 1 (by rfl) ⟨2830490, by rfl⟩ : syracuseStep 3773987 = 5660981) B5660981
theorem B1676851 : Blo 1676038 1676851 := bstep (se 1 (by rfl) ⟨1257638, by rfl⟩ : syracuseStep 1676851 = 2515277) B2515277
theorem B1676867 : Blo 1676038 1676867 := bstep (se 1 (by rfl) ⟨1257650, by rfl⟩ : syracuseStep 1676867 = 2515301) B2515301
theorem B1676883 : Blo 1676038 1676883 := bstep (se 1 (by rfl) ⟨1257662, by rfl⟩ : syracuseStep 1676883 = 2515325) B2515325
theorem B1676899 : Blo 1676038 1676899 := bstep (se 1 (by rfl) ⟨1257674, by rfl⟩ : syracuseStep 1676899 = 2515349) B2515349
theorem B2266723 : Blo 1676038 2266723 := bstep (se 1 (by rfl) ⟨1700042, by rfl⟩ : syracuseStep 2266723 = 3400085) B3400085
theorem B1676915 : Blo 1676038 1676915 := bstep (se 1 (by rfl) ⟨1257686, by rfl⟩ : syracuseStep 1676915 = 2515373) B2515373
theorem B1676931 : Blo 1676038 1676931 := bstep (se 1 (by rfl) ⟨1257698, by rfl⟩ : syracuseStep 1676931 = 2515397) B2515397
theorem B1676947 : Blo 1676038 1676947 := bstep (se 1 (by rfl) ⟨1257710, by rfl⟩ : syracuseStep 1676947 = 2515421) B2515421
theorem B1676963 : Blo 1676038 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B6543011 : Blo 1676038 6543011 := bstep (se 1 (by rfl) ⟨4907258, by rfl⟩ : syracuseStep 6543011 = 9814517) B9814517
theorem B1676979 : Blo 1676038 1676979 := bstep (se 1 (by rfl) ⟨1257734, by rfl⟩ : syracuseStep 1676979 = 2515469) B2515469
theorem B1676995 : Blo 1676038 1676995 := bstep (se 1 (by rfl) ⟨1257746, by rfl⟩ : syracuseStep 1676995 = 2515493) B2515493
theorem B1677011 : Blo 1676038 1677011 := bstep (se 1 (by rfl) ⟨1257758, by rfl⟩ : syracuseStep 1677011 = 2515517) B2515517
theorem B1677027 : Blo 1676038 1677027 := bstep (se 1 (by rfl) ⟨1257770, by rfl⟩ : syracuseStep 1677027 = 2515541) B2515541
theorem B1677043 : Blo 1676038 1677043 := bstep (se 1 (by rfl) ⟨1257782, by rfl⟩ : syracuseStep 1677043 = 2515565) B2515565
theorem B1677059 : Blo 1676038 1677059 := bstep (se 1 (by rfl) ⟨1257794, by rfl⟩ : syracuseStep 1677059 = 2515589) B2515589
theorem B1677075 : Blo 1676038 1677075 := bstep (se 1 (by rfl) ⟨1257806, by rfl⟩ : syracuseStep 1677075 = 2515613) B2515613
theorem B1677091 : Blo 1676038 1677091 := bstep (se 1 (by rfl) ⟨1257818, by rfl⟩ : syracuseStep 1677091 = 2515637) B2515637
theorem B3774257 : Blo 1676038 3774257 := bstep (se 2 (by rfl) ⟨1415346, by rfl⟩ : syracuseStep 3774257 = 2830693) B2830693
theorem B8492849 : Blo 1676038 8492849 := bstep (se 2 (by rfl) ⟨3184818, by rfl⟩ : syracuseStep 8492849 = 6369637) B6369637
theorem B1677107 : Blo 1676038 1677107 := bstep (se 1 (by rfl) ⟨1257830, by rfl⟩ : syracuseStep 1677107 = 2515661) B2515661
theorem B1677123 : Blo 1676038 1677123 := bstep (se 1 (by rfl) ⟨1257842, by rfl⟩ : syracuseStep 1677123 = 2515685) B2515685
theorem B3774275 : Blo 1676038 3774275 := bstep (se 1 (by rfl) ⟨2830706, by rfl⟩ : syracuseStep 3774275 = 5661413) B5661413
theorem B1791811 : Blo 1676038 1791811 := bstep (se 1 (by rfl) ⟨1343858, by rfl⟩ : syracuseStep 1791811 = 2687717) B2687717
theorem B1677139 : Blo 1676038 1677139 := bstep (se 1 (by rfl) ⟨1257854, by rfl⟩ : syracuseStep 1677139 = 2515709) B2515709
theorem B1677155 : Blo 1676038 1677155 := bstep (se 1 (by rfl) ⟨1257866, by rfl⟩ : syracuseStep 1677155 = 2515733) B2515733
theorem B1677171 : Blo 1676038 1677171 := bstep (se 1 (by rfl) ⟨1257878, by rfl⟩ : syracuseStep 1677171 = 2515757) B2515757
theorem B1677187 : Blo 1676038 1677187 := bstep (se 1 (by rfl) ⟨1257890, by rfl⟩ : syracuseStep 1677187 = 2515781) B2515781
theorem B1677203 : Blo 1676038 1677203 := bstep (se 1 (by rfl) ⟨1257902, by rfl⟩ : syracuseStep 1677203 = 2515805) B2515805
theorem B1677219 : Blo 1676038 1677219 := bstep (se 1 (by rfl) ⟨1257914, by rfl⟩ : syracuseStep 1677219 = 2515829) B2515829
theorem B1677235 : Blo 1676038 1677235 := bstep (se 1 (by rfl) ⟨1257926, by rfl⟩ : syracuseStep 1677235 = 2515853) B2515853
theorem B1677251 : Blo 1676038 1677251 := bstep (se 1 (by rfl) ⟨1257938, by rfl⟩ : syracuseStep 1677251 = 2515877) B2515877
theorem B1677267 : Blo 1676038 1677267 := bstep (se 1 (by rfl) ⟨1257950, by rfl⟩ : syracuseStep 1677267 = 2515901) B2515901
theorem B1677283 : Blo 1676038 1677283 := bstep (se 1 (by rfl) ⟨1257962, by rfl⟩ : syracuseStep 1677283 = 2515925) B2515925
theorem B5658605 : Blo 1676038 5658605 := bstep (se 3 (by rfl) ⟨1060988, by rfl⟩ : syracuseStep 5658605 = 2121977) B2121977
theorem B9549809 : Blo 1676038 9549809 := bstep (se 2 (by rfl) ⟨3581178, by rfl⟩ : syracuseStep 9549809 = 7162357) B7162357
theorem B1677299 : Blo 1676038 1677299 := bstep (se 1 (by rfl) ⟨1257974, by rfl⟩ : syracuseStep 1677299 = 2515949) B2515949
theorem B1677315 : Blo 1676038 1677315 := bstep (se 1 (by rfl) ⟨1257986, by rfl⟩ : syracuseStep 1677315 = 2515973) B2515973
theorem B1677331 : Blo 1676038 1677331 := bstep (se 1 (by rfl) ⟨1257998, by rfl⟩ : syracuseStep 1677331 = 2515997) B2515997
theorem B5658659 : Blo 1676038 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B6453283 : Blo 1676038 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B1677347 : Blo 1676038 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B4773937 : Blo 1676038 4773937 := bstep (se 2 (by rfl) ⟨1790226, by rfl⟩ : syracuseStep 4773937 = 3580453) B3580453
theorem B1677363 : Blo 1676038 1677363 := bstep (se 1 (by rfl) ⟨1258022, by rfl⟩ : syracuseStep 1677363 = 2516045) B2516045
theorem B1677379 : Blo 1676038 1677379 := bstep (se 1 (by rfl) ⟨1258034, by rfl⟩ : syracuseStep 1677379 = 2516069) B2516069
theorem B3774545 : Blo 1676038 3774545 := bstep (se 2 (by rfl) ⟨1415454, by rfl⟩ : syracuseStep 3774545 = 2830909) B2830909
theorem B1677395 : Blo 1676038 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B1677411 : Blo 1676038 1677411 := bstep (se 1 (by rfl) ⟨1258058, by rfl⟩ : syracuseStep 1677411 = 2516117) B2516117
theorem B3774563 : Blo 1676038 3774563 := bstep (se 1 (by rfl) ⟨2830922, by rfl⟩ : syracuseStep 3774563 = 5661845) B5661845
theorem B1677427 : Blo 1676038 1677427 := bstep (se 1 (by rfl) ⟨1258070, by rfl⟩ : syracuseStep 1677427 = 2516141) B2516141
theorem B1677443 : Blo 1676038 1677443 := bstep (se 1 (by rfl) ⟨1258082, by rfl⟩ : syracuseStep 1677443 = 2516165) B2516165
theorem B1677459 : Blo 1676038 1677459 := bstep (se 1 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 1677459 = 2516189) B2516189
theorem B1677475 : Blo 1676038 1677475 := bstep (se 1 (by rfl) ⟨1258106, by rfl⟩ : syracuseStep 1677475 = 2516213) B2516213
theorem B1677491 : Blo 1676038 1677491 := bstep (se 1 (by rfl) ⟨1258118, by rfl⟩ : syracuseStep 1677491 = 2516237) B2516237
theorem B1677507 : Blo 1676038 1677507 := bstep (se 1 (by rfl) ⟨1258130, by rfl⟩ : syracuseStep 1677507 = 2516261) B2516261
theorem B3184849 : Blo 1676038 3184849 := bstep (se 2 (by rfl) ⟨1194318, by rfl⟩ : syracuseStep 3184849 = 2388637) B2388637
theorem B1677523 : Blo 1676038 1677523 := bstep (se 1 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 1677523 = 2516285) B2516285
theorem B1677539 : Blo 1676038 1677539 := bstep (se 1 (by rfl) ⟨1258154, by rfl⟩ : syracuseStep 1677539 = 2516309) B2516309
theorem B1677555 : Blo 1676038 1677555 := bstep (se 1 (by rfl) ⟨1258166, by rfl⟩ : syracuseStep 1677555 = 2516333) B2516333
theorem B1677571 : Blo 1676038 1677571 := bstep (se 1 (by rfl) ⟨1258178, by rfl⟩ : syracuseStep 1677571 = 2516357) B2516357
theorem B1677587 : Blo 1676038 1677587 := bstep (se 1 (by rfl) ⟨1258190, by rfl⟩ : syracuseStep 1677587 = 2516381) B2516381
theorem B1677603 : Blo 1676038 1677603 := bstep (se 1 (by rfl) ⟨1258202, by rfl⟩ : syracuseStep 1677603 = 2516405) B2516405
theorem B5658929 : Blo 1676038 5658929 := bstep (se 2 (by rfl) ⟨2122098, by rfl⟩ : syracuseStep 5658929 = 4244197) B4244197
theorem B1677619 : Blo 1676038 1677619 := bstep (se 1 (by rfl) ⟨1258214, by rfl⟩ : syracuseStep 1677619 = 2516429) B2516429
theorem B4774211 : Blo 1676038 4774211 := bstep (se 1 (by rfl) ⟨3580658, by rfl⟩ : syracuseStep 4774211 = 7161317) B7161317
theorem B1677635 : Blo 1676038 1677635 := bstep (se 1 (by rfl) ⟨1258226, by rfl⟩ : syracuseStep 1677635 = 2516453) B2516453
theorem B1677651 : Blo 1676038 1677651 := bstep (se 1 (by rfl) ⟨1258238, by rfl⟩ : syracuseStep 1677651 = 2516477) B2516477
theorem B1677667 : Blo 1676038 1677667 := bstep (se 1 (by rfl) ⟨1258250, by rfl⟩ : syracuseStep 1677667 = 2516501) B2516501
theorem B3774833 : Blo 1676038 3774833 := bstep (se 2 (by rfl) ⟨1415562, by rfl⟩ : syracuseStep 3774833 = 2831125) B2831125
theorem B1677683 : Blo 1676038 1677683 := bstep (se 1 (by rfl) ⟨1258262, by rfl⟩ : syracuseStep 1677683 = 2516525) B2516525
theorem B3021187 : Blo 1676038 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B1677699 : Blo 1676038 1677699 := bstep (se 1 (by rfl) ⟨1258274, by rfl⟩ : syracuseStep 1677699 = 2516549) B2516549
theorem B3774851 : Blo 1676038 3774851 := bstep (se 1 (by rfl) ⟨2831138, by rfl⟩ : syracuseStep 3774851 = 5662277) B5662277
theorem B1677715 : Blo 1676038 1677715 := bstep (se 1 (by rfl) ⟨1258286, by rfl⟩ : syracuseStep 1677715 = 2516573) B2516573
theorem B1677731 : Blo 1676038 1677731 := bstep (se 1 (by rfl) ⟨1258298, by rfl⟩ : syracuseStep 1677731 = 2516597) B2516597
theorem B1677747 : Blo 1676038 1677747 := bstep (se 1 (by rfl) ⟨1258310, by rfl⟩ : syracuseStep 1677747 = 2516621) B2516621
theorem B1677763 : Blo 1676038 1677763 := bstep (se 1 (by rfl) ⟨1258322, by rfl⟩ : syracuseStep 1677763 = 2516645) B2516645
theorem B1677779 : Blo 1676038 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B1677795 : Blo 1676038 1677795 := bstep (se 1 (by rfl) ⟨1258346, by rfl⟩ : syracuseStep 1677795 = 2516693) B2516693
theorem B1677811 : Blo 1676038 1677811 := bstep (se 1 (by rfl) ⟨1258358, by rfl⟩ : syracuseStep 1677811 = 2516717) B2516717
theorem B4774403 : Blo 1676038 4774403 := bstep (se 1 (by rfl) ⟨3580802, by rfl⟩ : syracuseStep 4774403 = 7161605) B7161605
theorem B1677827 : Blo 1676038 1677827 := bstep (se 1 (by rfl) ⟨1258370, by rfl⟩ : syracuseStep 1677827 = 2516741) B2516741
theorem B1677843 : Blo 1676038 1677843 := bstep (se 1 (by rfl) ⟨1258382, by rfl⟩ : syracuseStep 1677843 = 2516765) B2516765
theorem B1677859 : Blo 1676038 1677859 := bstep (se 1 (by rfl) ⟨1258394, by rfl⟩ : syracuseStep 1677859 = 2516789) B2516789
theorem B1677875 : Blo 1676038 1677875 := bstep (se 1 (by rfl) ⟨1258406, by rfl⟩ : syracuseStep 1677875 = 2516813) B2516813
theorem B1677891 : Blo 1676038 1677891 := bstep (se 1 (by rfl) ⟨1258418, by rfl⟩ : syracuseStep 1677891 = 2516837) B2516837
theorem B2013779 : Blo 1676038 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B1677907 : Blo 1676038 1677907 := bstep (se 1 (by rfl) ⟨1258430, by rfl⟩ : syracuseStep 1677907 = 2516861) B2516861
theorem B1677923 : Blo 1676038 1677923 := bstep (se 1 (by rfl) ⟨1258442, by rfl⟩ : syracuseStep 1677923 = 2516885) B2516885
theorem B1677939 : Blo 1676038 1677939 := bstep (se 1 (by rfl) ⟨1258454, by rfl⟩ : syracuseStep 1677939 = 2516909) B2516909
theorem B1677955 : Blo 1676038 1677955 := bstep (se 1 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 1677955 = 2516933) B2516933
theorem B3775121 : Blo 1676038 3775121 := bstep (se 2 (by rfl) ⟨1415670, by rfl⟩ : syracuseStep 3775121 = 2831341) B2831341
theorem B1677971 : Blo 1676038 1677971 := bstep (se 1 (by rfl) ⟨1258478, by rfl⟩ : syracuseStep 1677971 = 2516957) B2516957
theorem B3775139 : Blo 1676038 3775139 := bstep (se 1 (by rfl) ⟨2831354, by rfl⟩ : syracuseStep 3775139 = 5662709) B5662709
theorem B1677987 : Blo 1676038 1677987 := bstep (se 1 (by rfl) ⟨1258490, by rfl⟩ : syracuseStep 1677987 = 2516981) B2516981
theorem B1678003 : Blo 1676038 1678003 := bstep (se 1 (by rfl) ⟨1258502, by rfl⟩ : syracuseStep 1678003 = 2517005) B2517005
theorem B1678019 : Blo 1676038 1678019 := bstep (se 1 (by rfl) ⟨1258514, by rfl⟩ : syracuseStep 1678019 = 2517029) B2517029
theorem B1678035 : Blo 1676038 1678035 := bstep (se 1 (by rfl) ⟨1258526, by rfl⟩ : syracuseStep 1678035 = 2517053) B2517053
theorem B32250595 : Blo 1676038 32250595 := bstep (se 1 (by rfl) ⟨24187946, by rfl⟩ : syracuseStep 32250595 = 48375893) B48375893
theorem B14334691 : Blo 1676038 14334691 := bstep (se 1 (by rfl) ⟨10751018, by rfl⟩ : syracuseStep 14334691 = 21502037) B21502037
theorem B2210627 : Blo 1676038 2210627 := bstep (se 1 (by rfl) ⟨1657970, by rfl⟩ : syracuseStep 2210627 = 3315941) B3315941
theorem B5659469 : Blo 1676038 5659469 := bstep (se 3 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 5659469 = 2122301) B2122301
theorem B7256945 : Blo 1676038 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B5659523 : Blo 1676038 5659523 := bstep (se 1 (by rfl) ⟨4244642, by rfl⟩ : syracuseStep 5659523 = 8489285) B8489285
theorem B3775409 : Blo 1676038 3775409 := bstep (se 2 (by rfl) ⟨1415778, by rfl⟩ : syracuseStep 3775409 = 2831557) B2831557
theorem B3775427 : Blo 1676038 3775427 := bstep (se 1 (by rfl) ⟨2831570, by rfl⟩ : syracuseStep 3775427 = 5663141) B5663141
theorem B6364109 : Blo 1676038 6364109 := bstep (se 3 (by rfl) ⟨1193270, by rfl⟩ : syracuseStep 6364109 = 2386541) B2386541
theorem B2685955 : Blo 1676038 2685955 := bstep (se 1 (by rfl) ⟨2014466, by rfl⟩ : syracuseStep 2685955 = 4028933) B4028933
theorem B3931139 : Blo 1676038 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B6798449 : Blo 1676038 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B24181901 : Blo 1676038 24181901 := bstep (se 3 (by rfl) ⟨4534106, by rfl⟩ : syracuseStep 24181901 = 9068213) B9068213
theorem B2514065 : Blo 1676038 2514065 := bstep (se 2 (by rfl) ⟨942774, by rfl⟩ : syracuseStep 2514065 = 1885549) B1885549
theorem B4242577 : Blo 1676038 4242577 := bstep (se 2 (by rfl) ⟨1590966, by rfl⟩ : syracuseStep 4242577 = 3181933) B3181933
theorem B5659793 : Blo 1676038 5659793 := bstep (se 2 (by rfl) ⟨2122422, by rfl⟩ : syracuseStep 5659793 = 4244845) B4244845
theorem B2514083 : Blo 1676038 2514083 := bstep (se 1 (by rfl) ⟨1885562, by rfl⟩ : syracuseStep 2514083 = 3771125) B3771125
theorem B9067697 : Blo 1676038 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B20405429 : Blo 1676038 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B2514113 : Blo 1676038 2514113 := bstep (se 2 (by rfl) ⟨942792, by rfl⟩ : syracuseStep 2514113 = 1885585) B1885585
theorem B2514131 : Blo 1676038 2514131 := bstep (se 1 (by rfl) ⟨1885598, by rfl⟩ : syracuseStep 2514131 = 3771197) B3771197
theorem B8494307 : Blo 1676038 8494307 := bstep (se 1 (by rfl) ⟨6370730, by rfl⟩ : syracuseStep 8494307 = 12741461) B12741461
theorem B2514161 : Blo 1676038 2514161 := bstep (se 2 (by rfl) ⟨942810, by rfl⟩ : syracuseStep 2514161 = 1885621) B1885621
theorem B2514179 : Blo 1676038 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B2514209 : Blo 1676038 2514209 := bstep (se 2 (by rfl) ⟨942828, by rfl⟩ : syracuseStep 2514209 = 1885657) B1885657
theorem B4775213 : Blo 1676038 4775213 := bstep (se 3 (by rfl) ⟨895352, by rfl⟩ : syracuseStep 4775213 = 1790705) B1790705
theorem B2514227 : Blo 1676038 2514227 := bstep (se 1 (by rfl) ⟨1885670, by rfl⟩ : syracuseStep 2514227 = 3771341) B3771341
theorem B2514257 : Blo 1676038 2514257 := bstep (se 2 (by rfl) ⟨942846, by rfl⟩ : syracuseStep 2514257 = 1885693) B1885693
theorem B2514275 : Blo 1676038 2514275 := bstep (se 1 (by rfl) ⟨1885706, by rfl⟩ : syracuseStep 2514275 = 3771413) B3771413
theorem B21478769 : Blo 1676038 21478769 := bstep (se 2 (by rfl) ⟨8054538, by rfl⟩ : syracuseStep 21478769 = 16109077) B16109077
theorem B2514305 : Blo 1676038 2514305 := bstep (se 2 (by rfl) ⟨942864, by rfl⟩ : syracuseStep 2514305 = 1885729) B1885729
theorem B2948483 : Blo 1676038 2948483 := bstep (se 1 (by rfl) ⟨2211362, by rfl⟩ : syracuseStep 2948483 = 4422725) B4422725
theorem B2514323 : Blo 1676038 2514323 := bstep (se 1 (by rfl) ⟨1885742, by rfl⟩ : syracuseStep 2514323 = 3771485) B3771485
theorem B4242851 : Blo 1676038 4242851 := bstep (se 1 (by rfl) ⟨3182138, by rfl⟩ : syracuseStep 4242851 = 6364277) B6364277
theorem B9551267 : Blo 1676038 9551267 := bstep (se 1 (by rfl) ⟨7163450, by rfl⟩ : syracuseStep 9551267 = 14326901) B14326901
theorem B2514353 : Blo 1676038 2514353 := bstep (se 2 (by rfl) ⟨942882, by rfl⟩ : syracuseStep 2514353 = 1885765) B1885765
theorem B2514371 : Blo 1676038 2514371 := bstep (se 1 (by rfl) ⟨1885778, by rfl⟩ : syracuseStep 2514371 = 3771557) B3771557
theorem B12729797 : Blo 1676038 12729797 := bstep (se 4 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 12729797 = 2386837) B2386837
theorem B2514401 : Blo 1676038 2514401 := bstep (se 2 (by rfl) ⟨942900, by rfl⟩ : syracuseStep 2514401 = 1885801) B1885801
theorem B4775395 : Blo 1676038 4775395 := bstep (se 1 (by rfl) ⟨3581546, by rfl⟩ : syracuseStep 4775395 = 7163093) B7163093
theorem B2514419 : Blo 1676038 2514419 := bstep (se 1 (by rfl) ⟨1885814, by rfl⟩ : syracuseStep 2514419 = 3771629) B3771629
theorem B2514449 : Blo 1676038 2514449 := bstep (se 2 (by rfl) ⟨942918, by rfl⟩ : syracuseStep 2514449 = 1885837) B1885837
theorem B2514467 : Blo 1676038 2514467 := bstep (se 1 (by rfl) ⟨1885850, by rfl⟩ : syracuseStep 2514467 = 3771701) B3771701
theorem B2514497 : Blo 1676038 2514497 := bstep (se 2 (by rfl) ⟨942936, by rfl⟩ : syracuseStep 2514497 = 1885873) B1885873
theorem B4030019 : Blo 1676038 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B2514515 : Blo 1676038 2514515 := bstep (se 1 (by rfl) ⟨1885886, by rfl⟩ : syracuseStep 2514515 = 3771773) B3771773
theorem B4243043 : Blo 1676038 4243043 := bstep (se 1 (by rfl) ⟨3182282, by rfl⟩ : syracuseStep 4243043 = 6364565) B6364565
theorem B2514545 : Blo 1676038 2514545 := bstep (se 2 (by rfl) ⟨942954, by rfl⟩ : syracuseStep 2514545 = 1885909) B1885909
theorem B2514563 : Blo 1676038 2514563 := bstep (se 1 (by rfl) ⟨1885922, by rfl⟩ : syracuseStep 2514563 = 3771845) B3771845
theorem B2514593 : Blo 1676038 2514593 := bstep (se 2 (by rfl) ⟨942972, by rfl⟩ : syracuseStep 2514593 = 1885945) B1885945
theorem B2686627 : Blo 1676038 2686627 := bstep (se 1 (by rfl) ⟨2014970, by rfl⟩ : syracuseStep 2686627 = 4029941) B4029941
theorem B5660333 : Blo 1676038 5660333 := bstep (se 3 (by rfl) ⟨1061312, by rfl⟩ : syracuseStep 5660333 = 2122625) B2122625
theorem B2514611 : Blo 1676038 2514611 := bstep (se 1 (by rfl) ⟨1885958, by rfl⟩ : syracuseStep 2514611 = 3771917) B3771917
theorem B2514641 : Blo 1676038 2514641 := bstep (se 2 (by rfl) ⟨942990, by rfl⟩ : syracuseStep 2514641 = 1885981) B1885981
theorem B2514659 : Blo 1676038 2514659 := bstep (se 1 (by rfl) ⟨1885994, by rfl⟩ : syracuseStep 2514659 = 3771989) B3771989
theorem B5660387 : Blo 1676038 5660387 := bstep (se 1 (by rfl) ⟨4245290, by rfl⟩ : syracuseStep 5660387 = 8490581) B8490581
theorem B2514689 : Blo 1676038 2514689 := bstep (se 2 (by rfl) ⟨943008, by rfl⟩ : syracuseStep 2514689 = 1886017) B1886017
theorem B4030211 : Blo 1676038 4030211 := bstep (se 1 (by rfl) ⟨3022658, by rfl⟩ : syracuseStep 4030211 = 6045317) B6045317
theorem B2121491 : Blo 1676038 2121491 := bstep (se 1 (by rfl) ⟨1591118, by rfl⟩ : syracuseStep 2121491 = 3182237) B3182237
theorem B2514707 : Blo 1676038 2514707 := bstep (se 1 (by rfl) ⟨1886030, by rfl⟩ : syracuseStep 2514707 = 3772061) B3772061
theorem B2514737 : Blo 1676038 2514737 := bstep (se 2 (by rfl) ⟨943026, by rfl⟩ : syracuseStep 2514737 = 1886053) B1886053
theorem B2514755 : Blo 1676038 2514755 := bstep (se 1 (by rfl) ⟨1886066, by rfl⟩ : syracuseStep 2514755 = 3772133) B3772133
theorem B2514785 : Blo 1676038 2514785 := bstep (se 2 (by rfl) ⟨943044, by rfl⟩ : syracuseStep 2514785 = 1886089) B1886089
theorem B2514803 : Blo 1676038 2514803 := bstep (se 1 (by rfl) ⟨1886102, by rfl⟩ : syracuseStep 2514803 = 3772205) B3772205
theorem B2514833 : Blo 1676038 2514833 := bstep (se 2 (by rfl) ⟨943062, by rfl⟩ : syracuseStep 2514833 = 1886125) B1886125
theorem B2514851 : Blo 1676038 2514851 := bstep (se 1 (by rfl) ⟨1886138, by rfl⟩ : syracuseStep 2514851 = 3772277) B3772277
theorem B5373869 : Blo 1676038 5373869 := bstep (se 3 (by rfl) ⟨1007600, by rfl⟩ : syracuseStep 5373869 = 2015201) B2015201
theorem B2514881 : Blo 1676038 2514881 := bstep (se 2 (by rfl) ⟨943080, by rfl⟩ : syracuseStep 2514881 = 1886161) B1886161
theorem B4775885 : Blo 1676038 4775885 := bstep (se 3 (by rfl) ⟨895478, by rfl⟩ : syracuseStep 4775885 = 1790957) B1790957
theorem B2514899 : Blo 1676038 2514899 := bstep (se 1 (by rfl) ⟨1886174, by rfl⟩ : syracuseStep 2514899 = 3772349) B3772349
theorem B2514929 : Blo 1676038 2514929 := bstep (se 2 (by rfl) ⟨943098, by rfl⟩ : syracuseStep 2514929 = 1886197) B1886197
theorem B5660657 : Blo 1676038 5660657 := bstep (se 2 (by rfl) ⟨2122746, by rfl⟩ : syracuseStep 5660657 = 4245493) B4245493
theorem B12738545 : Blo 1676038 12738545 := bstep (se 2 (by rfl) ⟨4776954, by rfl⟩ : syracuseStep 12738545 = 9553909) B9553909
theorem B6365249 : Blo 1676038 6365249 := bstep (se 2 (by rfl) ⟨2386968, by rfl⟩ : syracuseStep 6365249 = 4773937) B4773937
theorem B3399745 : Blo 1676038 3399745 := bstep (se 2 (by rfl) ⟨1274904, by rfl⟩ : syracuseStep 3399745 = 2549809) B2549809
theorem B2515019 : Blo 1676038 2515019 := bstep (se 1 (by rfl) ⟨1886264, by rfl⟩ : syracuseStep 2515019 = 3772529) B3772529
theorem B2121815 : Blo 1676038 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B2515031 : Blo 1676038 2515031 := bstep (se 1 (by rfl) ⟨1886273, by rfl⟩ : syracuseStep 2515031 = 3772547) B3772547
theorem B5660765 : Blo 1676038 5660765 := bstep (se 3 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 5660765 = 2122787) B2122787
theorem B10747997 : Blo 1676038 10747997 := bstep (se 3 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 10747997 = 4030499) B4030499
theorem B2515097 : Blo 1676038 2515097 := bstep (se 2 (by rfl) ⟨943161, by rfl⟩ : syracuseStep 2515097 = 1886323) B1886323
theorem B2515211 : Blo 1676038 2515211 := bstep (se 1 (by rfl) ⟨1886408, by rfl⟩ : syracuseStep 2515211 = 3772817) B3772817
theorem B2515223 : Blo 1676038 2515223 := bstep (se 1 (by rfl) ⟨1886417, by rfl⟩ : syracuseStep 2515223 = 3772835) B3772835
theorem B18129197 : Blo 1676038 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B2515289 : Blo 1676038 2515289 := bstep (se 2 (by rfl) ⟨943233, by rfl⟩ : syracuseStep 2515289 = 1886467) B1886467
theorem B2908505 : Blo 1676038 2908505 := bstep (se 2 (by rfl) ⟨1090689, by rfl⟩ : syracuseStep 2908505 = 2181379) B2181379
theorem B58114421 : Blo 1676038 58114421 := bstep (se 5 (by rfl) ⟨2724113, by rfl⟩ : syracuseStep 58114421 = 5448227) B5448227
theorem B2515403 : Blo 1676038 2515403 := bstep (se 1 (by rfl) ⟨1886552, by rfl⟩ : syracuseStep 2515403 = 3773105) B3773105
theorem B2515415 : Blo 1676038 2515415 := bstep (se 1 (by rfl) ⟨1886561, by rfl⟩ : syracuseStep 2515415 = 3773123) B3773123
theorem B2515481 : Blo 1676038 2515481 := bstep (se 2 (by rfl) ⟨943305, by rfl⟩ : syracuseStep 2515481 = 1886611) B1886611
theorem B4776499 : Blo 1676038 4776499 := bstep (se 1 (by rfl) ⟨3582374, by rfl⟩ : syracuseStep 4776499 = 7164749) B7164749
theorem B2515595 : Blo 1676038 2515595 := bstep (se 1 (by rfl) ⟨1886696, by rfl⟩ : syracuseStep 2515595 = 3773393) B3773393
theorem B2687627 : Blo 1676038 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B2515607 : Blo 1676038 2515607 := bstep (se 1 (by rfl) ⟨1886705, by rfl⟩ : syracuseStep 2515607 = 3773411) B3773411
theorem B4244147 : Blo 1676038 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B2515673 : Blo 1676038 2515673 := bstep (se 2 (by rfl) ⟨943377, by rfl⟩ : syracuseStep 2515673 = 1886755) B1886755
theorem B2122519 : Blo 1676038 2122519 := bstep (se 1 (by rfl) ⟨1591889, by rfl⟩ : syracuseStep 2122519 = 3183779) B3183779
theorem B4776727 : Blo 1676038 4776727 := bstep (se 1 (by rfl) ⟨3582545, by rfl⟩ : syracuseStep 4776727 = 7165091) B7165091
theorem B6800203 : Blo 1676038 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B2515787 : Blo 1676038 2515787 := bstep (se 1 (by rfl) ⟨1886840, by rfl⟩ : syracuseStep 2515787 = 3773681) B3773681
theorem B2515799 : Blo 1676038 2515799 := bstep (se 1 (by rfl) ⟨1886849, by rfl⟩ : syracuseStep 2515799 = 3773699) B3773699
theorem B14328677 : Blo 1676038 14328677 := bstep (se 4 (by rfl) ⟨1343313, by rfl⟩ : syracuseStep 14328677 = 2686627) B2686627
theorem B2515865 : Blo 1676038 2515865 := bstep (se 2 (by rfl) ⟨943449, by rfl⟩ : syracuseStep 2515865 = 1886899) B1886899
theorem B15328205 : Blo 1676038 15328205 := bstep (se 3 (by rfl) ⟨2874038, by rfl⟩ : syracuseStep 15328205 = 5748077) B5748077
theorem B43000793 : Blo 1676038 43000793 := bstep (se 2 (by rfl) ⟨16125297, by rfl⟩ : syracuseStep 43000793 = 32250595) B32250595
theorem B19112921 : Blo 1676038 19112921 := bstep (se 2 (by rfl) ⟨7167345, by rfl⟩ : syracuseStep 19112921 = 14334691) B14334691
theorem B3228673 : Blo 1676038 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B3580939 : Blo 1676038 3580939 := bstep (se 1 (by rfl) ⟨2685704, by rfl⟩ : syracuseStep 3580939 = 5371409) B5371409
theorem B2515979 : Blo 1676038 2515979 := bstep (se 1 (by rfl) ⟨1886984, by rfl⟩ : syracuseStep 2515979 = 3773969) B3773969
theorem B2515991 : Blo 1676038 2515991 := bstep (se 1 (by rfl) ⟨1886993, by rfl⟩ : syracuseStep 2515991 = 3773987) B3773987
theorem B2516057 : Blo 1676038 2516057 := bstep (se 2 (by rfl) ⟨943521, by rfl⟩ : syracuseStep 2516057 = 1887043) B1887043
theorem B4244683 : Blo 1676038 4244683 := bstep (se 1 (by rfl) ⟨3183512, by rfl⟩ : syracuseStep 4244683 = 6367025) B6367025
theorem B2516171 : Blo 1676038 2516171 := bstep (se 1 (by rfl) ⟨1887128, by rfl⟩ : syracuseStep 2516171 = 3774257) B3774257
theorem B5661899 : Blo 1676038 5661899 := bstep (se 1 (by rfl) ⟨4246424, by rfl⟩ : syracuseStep 5661899 = 8492849) B8492849
theorem B2516183 : Blo 1676038 2516183 := bstep (se 1 (by rfl) ⟨1887137, by rfl⟩ : syracuseStep 2516183 = 3774275) B3774275
theorem B2516249 : Blo 1676038 2516249 := bstep (se 2 (by rfl) ⟨943593, by rfl⟩ : syracuseStep 2516249 = 1887187) B1887187
theorem B6366509 : Blo 1676038 6366509 := bstep (se 3 (by rfl) ⟨1193720, by rfl⟩ : syracuseStep 6366509 = 2387441) B2387441
theorem B6366539 : Blo 1676038 6366539 := bstep (se 1 (by rfl) ⟨4774904, by rfl⟩ : syracuseStep 6366539 = 9549809) B9549809
theorem B3229003 : Blo 1676038 3229003 := bstep (se 1 (by rfl) ⟨2421752, by rfl⟩ : syracuseStep 3229003 = 4843505) B4843505
theorem B3581273 : Blo 1676038 3581273 := bstep (se 2 (by rfl) ⟨1342977, by rfl⟩ : syracuseStep 3581273 = 2685955) B2685955
theorem B4244825 : Blo 1676038 4244825 := bstep (se 2 (by rfl) ⟨1591809, by rfl⟩ : syracuseStep 4244825 = 3183619) B3183619
theorem B12731741 : Blo 1676038 12731741 := bstep (se 3 (by rfl) ⟨2387201, by rfl⟩ : syracuseStep 12731741 = 4774403) B4774403
theorem B6456665 : Blo 1676038 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B9684355 : Blo 1676038 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B2516363 : Blo 1676038 2516363 := bstep (se 1 (by rfl) ⟨1887272, by rfl⟩ : syracuseStep 2516363 = 3774545) B3774545
theorem B2516375 : Blo 1676038 2516375 := bstep (se 1 (by rfl) ⟨1887281, by rfl⟩ : syracuseStep 2516375 = 3774563) B3774563
theorem B2516441 : Blo 1676038 2516441 := bstep (se 2 (by rfl) ⟨943665, by rfl⟩ : syracuseStep 2516441 = 1887331) B1887331
theorem B5662169 : Blo 1676038 5662169 := bstep (se 2 (by rfl) ⟨2123313, by rfl⟩ : syracuseStep 5662169 = 4246627) B4246627
theorem B1885675 : Blo 1676038 1885675 := bstep (se 1 (by rfl) ⟨1414256, by rfl⟩ : syracuseStep 1885675 = 2828513) B2828513
theorem B34407953 : Blo 1676038 34407953 := bstep (se 2 (by rfl) ⟨12902982, by rfl⟩ : syracuseStep 34407953 = 25805965) B25805965
theorem B2516555 : Blo 1676038 2516555 := bstep (se 1 (by rfl) ⟨1887416, by rfl⟩ : syracuseStep 2516555 = 3774833) B3774833
theorem B1885783 : Blo 1676038 1885783 := bstep (se 1 (by rfl) ⟨1414337, by rfl⟩ : syracuseStep 1885783 = 2828675) B2828675
theorem B2516567 : Blo 1676038 2516567 := bstep (se 1 (by rfl) ⟨1887425, by rfl⟩ : syracuseStep 2516567 = 3774851) B3774851
theorem B6801047 : Blo 1676038 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B5375639 : Blo 1676038 5375639 := bstep (se 1 (by rfl) ⟨4031729, by rfl⟩ : syracuseStep 5375639 = 8063459) B8063459
theorem B2516633 : Blo 1676038 2516633 := bstep (se 2 (by rfl) ⟨943737, by rfl⟩ : syracuseStep 2516633 = 1887475) B1887475
theorem B1885963 : Blo 1676038 1885963 := bstep (se 1 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 1885963 = 2828945) B2828945
theorem B2516747 : Blo 1676038 2516747 := bstep (se 1 (by rfl) ⟨1887560, by rfl⟩ : syracuseStep 2516747 = 3775121) B3775121
theorem B2516759 : Blo 1676038 2516759 := bstep (se 1 (by rfl) ⟨1887569, by rfl⟩ : syracuseStep 2516759 = 3775139) B3775139
theorem B5375767 : Blo 1676038 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B2516825 : Blo 1676038 2516825 := bstep (se 2 (by rfl) ⟨943809, by rfl⟩ : syracuseStep 2516825 = 1887619) B1887619
theorem B1886071 : Blo 1676038 1886071 := bstep (se 1 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 1886071 = 2829107) B2829107
theorem B2516939 : Blo 1676038 2516939 := bstep (se 1 (by rfl) ⟨1887704, by rfl⟩ : syracuseStep 2516939 = 3775409) B3775409
theorem B6367193 : Blo 1676038 6367193 := bstep (se 2 (by rfl) ⟨2387697, by rfl⟩ : syracuseStep 6367193 = 4775395) B4775395
theorem B2516951 : Blo 1676038 2516951 := bstep (se 1 (by rfl) ⟨1887713, by rfl⟩ : syracuseStep 2516951 = 3775427) B3775427
theorem B1722391 : Blo 1676038 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B2517017 : Blo 1676038 2517017 := bstep (se 2 (by rfl) ⟨943881, by rfl⟩ : syracuseStep 2517017 = 1887763) B1887763
theorem B1886251 : Blo 1676038 1886251 := bstep (se 1 (by rfl) ⟨1414688, by rfl⟩ : syracuseStep 1886251 = 2829377) B2829377
theorem B1886359 : Blo 1676038 1886359 := bstep (se 1 (by rfl) ⟨1414769, by rfl⟩ : syracuseStep 1886359 = 2829539) B2829539
theorem B4245655 : Blo 1676038 4245655 := bstep (se 1 (by rfl) ⟨3184241, by rfl⟩ : syracuseStep 4245655 = 6368483) B6368483
theorem B5662871 : Blo 1676038 5662871 := bstep (se 1 (by rfl) ⟨4247153, by rfl⟩ : syracuseStep 5662871 = 8494307) B8494307
theorem B14321843 : Blo 1676038 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B2828567 : Blo 1676038 2828567 := bstep (se 1 (by rfl) ⟨2121425, by rfl⟩ : syracuseStep 2828567 = 4242851) B4242851
theorem B6367511 : Blo 1676038 6367511 := bstep (se 1 (by rfl) ⟨4775633, by rfl⟩ : syracuseStep 6367511 = 9551267) B9551267
theorem B1886539 : Blo 1676038 1886539 := bstep (se 1 (by rfl) ⟨1414904, by rfl⟩ : syracuseStep 1886539 = 2829809) B2829809
theorem B2828695 : Blo 1676038 2828695 := bstep (se 1 (by rfl) ⟨2121521, by rfl⟩ : syracuseStep 2828695 = 4243043) B4243043
theorem B1886647 : Blo 1676038 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B14330317 : Blo 1676038 14330317 := bstep (se 3 (by rfl) ⟨2686934, by rfl⟩ : syracuseStep 14330317 = 5373869) B5373869
theorem B4246091 : Blo 1676038 4246091 := bstep (se 1 (by rfl) ⟨3184568, by rfl⟩ : syracuseStep 4246091 = 6369137) B6369137
theorem B1886827 : Blo 1676038 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B1886935 : Blo 1676038 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B8604377 : Blo 1676038 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B5098205 : Blo 1676038 5098205 := bstep (se 3 (by rfl) ⟨955913, by rfl⟩ : syracuseStep 5098205 = 1911827) B1911827
theorem B3771161 : Blo 1676038 3771161 := bstep (se 2 (by rfl) ⟨1414185, by rfl⟩ : syracuseStep 3771161 = 2828371) B2828371
theorem B3582785 : Blo 1676038 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B1911659 : Blo 1676038 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B3771251 : Blo 1676038 3771251 := bstep (se 1 (by rfl) ⟨2828438, by rfl⟩ : syracuseStep 3771251 = 5656877) B5656877
theorem B1887115 : Blo 1676038 1887115 := bstep (se 1 (by rfl) ⟨1415336, by rfl⟩ : syracuseStep 1887115 = 2830673) B2830673
theorem B3771287 : Blo 1676038 3771287 := bstep (se 1 (by rfl) ⟨2828465, by rfl⟩ : syracuseStep 3771287 = 5656931) B5656931
theorem B6368179 : Blo 1676038 6368179 := bstep (se 1 (by rfl) ⟨4776134, by rfl⟩ : syracuseStep 6368179 = 9552269) B9552269
theorem B9554867 : Blo 1676038 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B4246465 : Blo 1676038 4246465 := bstep (se 2 (by rfl) ⟨1592424, by rfl⟩ : syracuseStep 4246465 = 3184849) B3184849
theorem B2722763 : Blo 1676038 2722763 := bstep (se 1 (by rfl) ⟨2042072, by rfl⟩ : syracuseStep 2722763 = 4084145) B4084145
theorem B8055769 : Blo 1676038 8055769 := bstep (se 2 (by rfl) ⟨3020913, by rfl⟩ : syracuseStep 8055769 = 6041827) B6041827
theorem B1887223 : Blo 1676038 1887223 := bstep (se 1 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 1887223 = 2830835) B2830835
theorem B2829323 : Blo 1676038 2829323 := bstep (se 1 (by rfl) ⟨2121992, by rfl⟩ : syracuseStep 2829323 = 4243985) B4243985
theorem B3771467 : Blo 1676038 3771467 := bstep (se 1 (by rfl) ⟨2828600, by rfl⟩ : syracuseStep 3771467 = 5657201) B5657201
theorem B8055883 : Blo 1676038 8055883 := bstep (se 1 (by rfl) ⟨6041912, by rfl⟩ : syracuseStep 8055883 = 12083825) B12083825
theorem B3771521 : Blo 1676038 3771521 := bstep (se 2 (by rfl) ⟨1414320, by rfl⟩ : syracuseStep 3771521 = 2828641) B2828641
theorem B2829451 : Blo 1676038 2829451 := bstep (se 1 (by rfl) ⟨2122088, by rfl⟩ : syracuseStep 2829451 = 4244177) B4244177
theorem B2550923 : Blo 1676038 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B1887403 : Blo 1676038 1887403 := bstep (se 1 (by rfl) ⟨1415552, by rfl⟩ : syracuseStep 1887403 = 2831105) B2831105
theorem B3493079 : Blo 1676038 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B14322905 : Blo 1676038 14322905 := bstep (se 2 (by rfl) ⟨5371089, by rfl⟩ : syracuseStep 14322905 = 10742179) B10742179
theorem B8490257 : Blo 1676038 8490257 := bstep (se 2 (by rfl) ⟨3183846, by rfl⟩ : syracuseStep 8490257 = 6367693) B6367693
theorem B1887511 : Blo 1676038 1887511 := bstep (se 1 (by rfl) ⟨1415633, by rfl⟩ : syracuseStep 1887511 = 2831267) B2831267
theorem B2829593 : Blo 1676038 2829593 := bstep (se 2 (by rfl) ⟨1061097, by rfl⟩ : syracuseStep 2829593 = 2122195) B2122195
theorem B3771737 : Blo 1676038 3771737 := bstep (se 2 (by rfl) ⟨1414401, by rfl⟩ : syracuseStep 3771737 = 2828803) B2828803
theorem B2420119 : Blo 1676038 2420119 := bstep (se 1 (by rfl) ⟨1815089, by rfl⟩ : syracuseStep 2420119 = 3630179) B3630179
theorem B2829721 : Blo 1676038 2829721 := bstep (se 2 (by rfl) ⟨1061145, by rfl⟩ : syracuseStep 2829721 = 2122291) B2122291
theorem B3771827 : Blo 1676038 3771827 := bstep (se 1 (by rfl) ⟨2828870, by rfl⟩ : syracuseStep 3771827 = 5657741) B5657741
theorem B7163315 : Blo 1676038 7163315 := bstep (se 1 (by rfl) ⟨5372486, by rfl⟩ : syracuseStep 7163315 = 10744973) B10744973
theorem B8490419 : Blo 1676038 8490419 := bstep (se 1 (by rfl) ⟨6367814, by rfl⟩ : syracuseStep 8490419 = 12735629) B12735629
theorem B3182017 : Blo 1676038 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B1887691 : Blo 1676038 1887691 := bstep (se 1 (by rfl) ⟨1415768, by rfl⟩ : syracuseStep 1887691 = 2831537) B2831537
theorem B3771863 : Blo 1676038 3771863 := bstep (se 1 (by rfl) ⟨2828897, by rfl⟩ : syracuseStep 3771863 = 5657795) B5657795
theorem B5443033 : Blo 1676038 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B4247063 : Blo 1676038 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B8056385 : Blo 1676038 8056385 := bstep (se 2 (by rfl) ⟨3021144, by rfl⟩ : syracuseStep 8056385 = 6042289) B6042289
theorem B3772043 : Blo 1676038 3772043 := bstep (se 1 (by rfl) ⟨2829032, by rfl⟩ : syracuseStep 3772043 = 5658065) B5658065
theorem B3583639 : Blo 1676038 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B3772097 : Blo 1676038 3772097 := bstep (se 2 (by rfl) ⟨1414536, by rfl⟩ : syracuseStep 3772097 = 2829073) B2829073
theorem B14331653 : Blo 1676038 14331653 := bstep (se 4 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 14331653 = 2687185) B2687185
theorem B18124661 : Blo 1676038 18124661 := bstep (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) B1699187
theorem B3182465 : Blo 1676038 3182465 := bstep (se 2 (by rfl) ⟨1193424, by rfl⟩ : syracuseStep 3182465 = 2386849) B2386849
theorem B3772313 : Blo 1676038 3772313 := bstep (se 2 (by rfl) ⟨1414617, by rfl⟩ : syracuseStep 3772313 = 2829235) B2829235
theorem B2830295 : Blo 1676038 2830295 := bstep (se 1 (by rfl) ⟨2122721, by rfl⟩ : syracuseStep 2830295 = 4245443) B4245443
theorem B3772403 : Blo 1676038 3772403 := bstep (se 1 (by rfl) ⟨2829302, by rfl⟩ : syracuseStep 3772403 = 5658605) B5658605
theorem B3772439 : Blo 1676038 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B2830423 : Blo 1676038 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B6369425 : Blo 1676038 6369425 := bstep (se 2 (by rfl) ⟨2388534, by rfl⟩ : syracuseStep 6369425 = 4777069) B4777069
theorem B19099799 : Blo 1676038 19099799 := bstep (se 1 (by rfl) ⟨14324849, by rfl⟩ : syracuseStep 19099799 = 28649699) B28649699
theorem B42987671 : Blo 1676038 42987671 := bstep (se 1 (by rfl) ⟨32240753, by rfl⟩ : syracuseStep 42987671 = 64481507) B64481507
theorem B5656769 : Blo 1676038 5656769 := bstep (se 2 (by rfl) ⟨2121288, by rfl⟩ : syracuseStep 5656769 = 4242577) B4242577
theorem B3772619 : Blo 1676038 3772619 := bstep (se 1 (by rfl) ⟨2829464, by rfl⟩ : syracuseStep 3772619 = 5658929) B5658929
theorem B2420939 : Blo 1676038 2420939 := bstep (se 1 (by rfl) ⟨1815704, by rfl⟩ : syracuseStep 2420939 = 3631409) B3631409
theorem B3182807 : Blo 1676038 3182807 := bstep (se 1 (by rfl) ⟨2387105, by rfl⟩ : syracuseStep 3182807 = 4774211) B4774211
theorem B5370077 : Blo 1676038 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B3772673 : Blo 1676038 3772673 := bstep (se 2 (by rfl) ⟨1414752, by rfl⟩ : syracuseStep 3772673 = 2829505) B2829505
theorem B9548077 : Blo 1676038 9548077 := bstep (se 3 (by rfl) ⟨1790264, by rfl⟩ : syracuseStep 9548077 = 3580529) B3580529
theorem B9556325 : Blo 1676038 9556325 := bstep (se 4 (by rfl) ⟨895905, by rfl⟩ : syracuseStep 9556325 = 1791811) B1791811
theorem B6042059 : Blo 1676038 6042059 := bstep (se 1 (by rfl) ⟨4531544, by rfl⟩ : syracuseStep 6042059 = 9063089) B9063089
theorem B3772889 : Blo 1676038 3772889 := bstep (se 2 (by rfl) ⟨1414833, by rfl⟩ : syracuseStep 3772889 = 2829667) B2829667
theorem B3772979 : Blo 1676038 3772979 := bstep (se 1 (by rfl) ⟨2829734, by rfl⟩ : syracuseStep 3772979 = 5659469) B5659469
theorem B4837963 : Blo 1676038 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B3773015 : Blo 1676038 3773015 := bstep (se 1 (by rfl) ⟨2829761, by rfl⟩ : syracuseStep 3773015 = 5659523) B5659523
theorem B30585437 : Blo 1676038 30585437 := bstep (se 3 (by rfl) ⟨5734769, by rfl⟩ : syracuseStep 30585437 = 11469539) B11469539
theorem B26170037 : Blo 1676038 26170037 := bstep (se 5 (by rfl) ⟨1226720, by rfl⟩ : syracuseStep 26170037 = 2453441) B2453441
theorem B2831051 : Blo 1676038 2831051 := bstep (se 1 (by rfl) ⟨2123288, by rfl⟩ : syracuseStep 2831051 = 4246577) B4246577
theorem B4027097 : Blo 1676038 4027097 := bstep (se 2 (by rfl) ⟨1510161, by rfl⟩ : syracuseStep 4027097 = 3020323) B3020323
theorem B5657309 : Blo 1676038 5657309 := bstep (se 3 (by rfl) ⟨1060745, by rfl⟩ : syracuseStep 5657309 = 2121491) B2121491
theorem B1676043 : Blo 1676038 1676043 := bstep (se 1 (by rfl) ⟨1257032, by rfl⟩ : syracuseStep 1676043 = 2514065) B2514065
theorem B3773195 : Blo 1676038 3773195 := bstep (se 1 (by rfl) ⟨2829896, by rfl⟩ : syracuseStep 3773195 = 5659793) B5659793
theorem B1676055 : Blo 1676038 1676055 := bstep (se 1 (by rfl) ⟨1257041, by rfl⟩ : syracuseStep 1676055 = 2514083) B2514083
theorem B13603619 : Blo 1676038 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B1676075 : Blo 1676038 1676075 := bstep (se 1 (by rfl) ⟨1257056, by rfl⟩ : syracuseStep 1676075 = 2514113) B2514113
theorem B1676087 : Blo 1676038 1676087 := bstep (se 1 (by rfl) ⟨1257065, by rfl⟩ : syracuseStep 1676087 = 2514131) B2514131
theorem B3773249 : Blo 1676038 3773249 := bstep (se 2 (by rfl) ⟨1414968, by rfl⟩ : syracuseStep 3773249 = 2829937) B2829937
theorem B1676107 : Blo 1676038 1676107 := bstep (se 1 (by rfl) ⟨1257080, by rfl⟩ : syracuseStep 1676107 = 2514161) B2514161
theorem B6370123 : Blo 1676038 6370123 := bstep (se 1 (by rfl) ⟨4777592, by rfl⟩ : syracuseStep 6370123 = 9555185) B9555185
theorem B2831179 : Blo 1676038 2831179 := bstep (se 1 (by rfl) ⟨2123384, by rfl⟩ : syracuseStep 2831179 = 4246769) B4246769
theorem B1700683 : Blo 1676038 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B1676119 : Blo 1676038 1676119 := bstep (se 1 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 1676119 = 2514179) B2514179
theorem B5895005 : Blo 1676038 5895005 := bstep (se 3 (by rfl) ⟨1105313, by rfl⟩ : syracuseStep 5895005 = 2210627) B2210627
theorem B1676139 : Blo 1676038 1676139 := bstep (se 1 (by rfl) ⟨1257104, by rfl⟩ : syracuseStep 1676139 = 2514209) B2514209
theorem B3183475 : Blo 1676038 3183475 := bstep (se 1 (by rfl) ⟨2387606, by rfl⟩ : syracuseStep 3183475 = 4775213) B4775213
theorem B1676151 : Blo 1676038 1676151 := bstep (se 1 (by rfl) ⟨1257113, by rfl⟩ : syracuseStep 1676151 = 2514227) B2514227
theorem B1676171 : Blo 1676038 1676171 := bstep (se 1 (by rfl) ⟨1257128, by rfl⟩ : syracuseStep 1676171 = 2514257) B2514257
theorem B1676183 : Blo 1676038 1676183 := bstep (se 1 (by rfl) ⟨1257137, by rfl⟩ : syracuseStep 1676183 = 2514275) B2514275
theorem B1676203 : Blo 1676038 1676203 := bstep (se 1 (by rfl) ⟨1257152, by rfl⟩ : syracuseStep 1676203 = 2514305) B2514305
theorem B1676215 : Blo 1676038 1676215 := bstep (se 1 (by rfl) ⟨1257161, by rfl⟩ : syracuseStep 1676215 = 2514323) B2514323
theorem B1676235 : Blo 1676038 1676235 := bstep (se 1 (by rfl) ⟨1257176, by rfl⟩ : syracuseStep 1676235 = 2514353) B2514353
theorem B1676247 : Blo 1676038 1676247 := bstep (se 1 (by rfl) ⟨1257185, by rfl⟩ : syracuseStep 1676247 = 2514371) B2514371
theorem B2831321 : Blo 1676038 2831321 := bstep (se 2 (by rfl) ⟨1061745, by rfl⟩ : syracuseStep 2831321 = 2123491) B2123491
theorem B1676267 : Blo 1676038 1676267 := bstep (se 1 (by rfl) ⟨1257200, by rfl⟩ : syracuseStep 1676267 = 2514401) B2514401
theorem B1676279 : Blo 1676038 1676279 := bstep (se 1 (by rfl) ⟨1257209, by rfl⟩ : syracuseStep 1676279 = 2514419) B2514419
theorem B1676299 : Blo 1676038 1676299 := bstep (se 1 (by rfl) ⟨1257224, by rfl⟩ : syracuseStep 1676299 = 2514449) B2514449
theorem B1676311 : Blo 1676038 1676311 := bstep (se 1 (by rfl) ⟨1257233, by rfl⟩ : syracuseStep 1676311 = 2514467) B2514467
theorem B3773465 : Blo 1676038 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B1676331 : Blo 1676038 1676331 := bstep (se 1 (by rfl) ⟨1257248, by rfl⟩ : syracuseStep 1676331 = 2514497) B2514497
theorem B1676343 : Blo 1676038 1676343 := bstep (se 1 (by rfl) ⟨1257257, by rfl⟩ : syracuseStep 1676343 = 2514515) B2514515
theorem B1676363 : Blo 1676038 1676363 := bstep (se 1 (by rfl) ⟨1257272, by rfl⟩ : syracuseStep 1676363 = 2514545) B2514545
theorem B1676375 : Blo 1676038 1676375 := bstep (se 1 (by rfl) ⟨1257281, by rfl⟩ : syracuseStep 1676375 = 2514563) B2514563
theorem B2831449 : Blo 1676038 2831449 := bstep (se 2 (by rfl) ⟨1061793, by rfl⟩ : syracuseStep 2831449 = 2123587) B2123587
theorem B6370397 : Blo 1676038 6370397 := bstep (se 3 (by rfl) ⟨1194449, by rfl⟩ : syracuseStep 6370397 = 2388899) B2388899
theorem B1676395 : Blo 1676038 1676395 := bstep (se 1 (by rfl) ⟨1257296, by rfl⟩ : syracuseStep 1676395 = 2514593) B2514593
theorem B3773555 : Blo 1676038 3773555 := bstep (se 1 (by rfl) ⟨2830166, by rfl⟩ : syracuseStep 3773555 = 5660333) B5660333
theorem B1676407 : Blo 1676038 1676407 := bstep (se 1 (by rfl) ⟨1257305, by rfl⟩ : syracuseStep 1676407 = 2514611) B2514611
theorem B1676427 : Blo 1676038 1676427 := bstep (se 1 (by rfl) ⟨1257320, by rfl⟩ : syracuseStep 1676427 = 2514641) B2514641
theorem B1676439 : Blo 1676038 1676439 := bstep (se 1 (by rfl) ⟨1257329, by rfl⟩ : syracuseStep 1676439 = 2514659) B2514659
theorem B3773591 : Blo 1676038 3773591 := bstep (se 1 (by rfl) ⟨2830193, by rfl⟩ : syracuseStep 3773591 = 5660387) B5660387
theorem B1676459 : Blo 1676038 1676459 := bstep (se 1 (by rfl) ⟨1257344, by rfl⟩ : syracuseStep 1676459 = 2514689) B2514689
theorem B1676471 : Blo 1676038 1676471 := bstep (se 1 (by rfl) ⟨1257353, by rfl⟩ : syracuseStep 1676471 = 2514707) B2514707
theorem B1676491 : Blo 1676038 1676491 := bstep (se 1 (by rfl) ⟨1257368, by rfl⟩ : syracuseStep 1676491 = 2514737) B2514737
theorem B1676503 : Blo 1676038 1676503 := bstep (se 1 (by rfl) ⟨1257377, by rfl⟩ : syracuseStep 1676503 = 2514755) B2514755
theorem B1676523 : Blo 1676038 1676523 := bstep (se 1 (by rfl) ⟨1257392, by rfl⟩ : syracuseStep 1676523 = 2514785) B2514785
theorem B1676535 : Blo 1676038 1676535 := bstep (se 1 (by rfl) ⟨1257401, by rfl⟩ : syracuseStep 1676535 = 2514803) B2514803
theorem B1676555 : Blo 1676038 1676555 := bstep (se 1 (by rfl) ⟨1257416, by rfl⟩ : syracuseStep 1676555 = 2514833) B2514833
theorem B1676567 : Blo 1676038 1676567 := bstep (se 1 (by rfl) ⟨1257425, by rfl⟩ : syracuseStep 1676567 = 2514851) B2514851
theorem B1676587 : Blo 1676038 1676587 := bstep (se 1 (by rfl) ⟨1257440, by rfl⟩ : syracuseStep 1676587 = 2514881) B2514881
theorem B1815851 : Blo 1676038 1815851 := bstep (se 1 (by rfl) ⟨1361888, by rfl⟩ : syracuseStep 1815851 = 2723777) B2723777
theorem B3183923 : Blo 1676038 3183923 := bstep (se 1 (by rfl) ⟨2387942, by rfl⟩ : syracuseStep 3183923 = 4775885) B4775885
theorem B1676599 : Blo 1676038 1676599 := bstep (se 1 (by rfl) ⟨1257449, by rfl⟩ : syracuseStep 1676599 = 2514899) B2514899
theorem B1676619 : Blo 1676038 1676619 := bstep (se 1 (by rfl) ⟨1257464, by rfl⟩ : syracuseStep 1676619 = 2514929) B2514929
theorem B3773771 : Blo 1676038 3773771 := bstep (se 1 (by rfl) ⟨2830328, by rfl⟩ : syracuseStep 3773771 = 5660657) B5660657
theorem B8492363 : Blo 1676038 8492363 := bstep (se 1 (by rfl) ⟨6369272, by rfl⟩ : syracuseStep 8492363 = 12738545) B12738545
theorem B1676631 : Blo 1676038 1676631 := bstep (se 1 (by rfl) ⟨1257473, by rfl⟩ : syracuseStep 1676631 = 2514947) B2514947
theorem B3183961 : Blo 1676038 3183961 := bstep (se 2 (by rfl) ⟨1193985, by rfl⟩ : syracuseStep 3183961 = 2387971) B2387971
theorem B1676651 : Blo 1676038 1676651 := bstep (se 1 (by rfl) ⟨1257488, by rfl⟩ : syracuseStep 1676651 = 2514977) B2514977
theorem B1676663 : Blo 1676038 1676663 := bstep (se 1 (by rfl) ⟨1257497, by rfl⟩ : syracuseStep 1676663 = 2514995) B2514995
theorem B3773825 : Blo 1676038 3773825 := bstep (se 2 (by rfl) ⟨1415184, by rfl⟩ : syracuseStep 3773825 = 2830369) B2830369
theorem B1676683 : Blo 1676038 1676683 := bstep (se 1 (by rfl) ⟨1257512, by rfl⟩ : syracuseStep 1676683 = 2515025) B2515025
theorem B1676695 : Blo 1676038 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B1676715 : Blo 1676038 1676715 := bstep (se 1 (by rfl) ⟨1257536, by rfl⟩ : syracuseStep 1676715 = 2515073) B2515073
theorem B1676727 : Blo 1676038 1676727 := bstep (se 1 (by rfl) ⟨1257545, by rfl⟩ : syracuseStep 1676727 = 2515091) B2515091
theorem B1676747 : Blo 1676038 1676747 := bstep (se 1 (by rfl) ⟨1257560, by rfl⟩ : syracuseStep 1676747 = 2515121) B2515121
theorem B1676759 : Blo 1676038 1676759 := bstep (se 1 (by rfl) ⟨1257569, by rfl⟩ : syracuseStep 1676759 = 2515139) B2515139
theorem B1676779 : Blo 1676038 1676779 := bstep (se 1 (by rfl) ⟨1257584, by rfl⟩ : syracuseStep 1676779 = 2515169) B2515169
theorem B1676791 : Blo 1676038 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B1676811 : Blo 1676038 1676811 := bstep (se 1 (by rfl) ⟨1257608, by rfl⟩ : syracuseStep 1676811 = 2515217) B2515217
theorem B1676823 : Blo 1676038 1676823 := bstep (se 1 (by rfl) ⟨1257617, by rfl⟩ : syracuseStep 1676823 = 2515235) B2515235
theorem B1676843 : Blo 1676038 1676843 := bstep (se 1 (by rfl) ⟨1257632, by rfl⟩ : syracuseStep 1676843 = 2515265) B2515265
theorem B12727853 : Blo 1676038 12727853 := bstep (se 3 (by rfl) ⟨2386472, by rfl⟩ : syracuseStep 12727853 = 4772945) B4772945
theorem B1676855 : Blo 1676038 1676855 := bstep (se 1 (by rfl) ⟨1257641, by rfl⟩ : syracuseStep 1676855 = 2515283) B2515283
theorem B1676875 : Blo 1676038 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B1791563 : Blo 1676038 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B1676887 : Blo 1676038 1676887 := bstep (se 1 (by rfl) ⟨1257665, by rfl⟩ : syracuseStep 1676887 = 2515331) B2515331
theorem B3774041 : Blo 1676038 3774041 := bstep (se 2 (by rfl) ⟨1415265, by rfl⟩ : syracuseStep 3774041 = 2830531) B2830531
theorem B1676907 : Blo 1676038 1676907 := bstep (se 1 (by rfl) ⟨1257680, by rfl⟩ : syracuseStep 1676907 = 2515361) B2515361
theorem B1676919 : Blo 1676038 1676919 := bstep (se 1 (by rfl) ⟨1257689, by rfl⟩ : syracuseStep 1676919 = 2515379) B2515379
theorem B1676939 : Blo 1676038 1676939 := bstep (se 1 (by rfl) ⟨1257704, by rfl⟩ : syracuseStep 1676939 = 2515409) B2515409
theorem B1676951 : Blo 1676038 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B1676971 : Blo 1676038 1676971 := bstep (se 1 (by rfl) ⟨1257728, by rfl⟩ : syracuseStep 1676971 = 2515457) B2515457
theorem B3774131 : Blo 1676038 3774131 := bstep (se 1 (by rfl) ⟨2830598, by rfl⟩ : syracuseStep 3774131 = 5661197) B5661197
theorem B1676983 : Blo 1676038 1676983 := bstep (se 1 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 1676983 = 2515475) B2515475
theorem B1677003 : Blo 1676038 1677003 := bstep (se 1 (by rfl) ⟨1257752, by rfl⟩ : syracuseStep 1677003 = 2515505) B2515505
theorem B1677015 : Blo 1676038 1677015 := bstep (se 1 (by rfl) ⟨1257761, by rfl⟩ : syracuseStep 1677015 = 2515523) B2515523
theorem B3774167 : Blo 1676038 3774167 := bstep (se 1 (by rfl) ⟨2830625, by rfl⟩ : syracuseStep 3774167 = 5661251) B5661251
theorem B1677035 : Blo 1676038 1677035 := bstep (se 1 (by rfl) ⟨1257776, by rfl⟩ : syracuseStep 1677035 = 2515553) B2515553
theorem B1677047 : Blo 1676038 1677047 := bstep (se 1 (by rfl) ⟨1257785, by rfl⟩ : syracuseStep 1677047 = 2515571) B2515571
theorem B1677067 : Blo 1676038 1677067 := bstep (se 1 (by rfl) ⟨1257800, by rfl⟩ : syracuseStep 1677067 = 2515601) B2515601
theorem B1677079 : Blo 1676038 1677079 := bstep (se 1 (by rfl) ⟨1257809, by rfl⟩ : syracuseStep 1677079 = 2515619) B2515619
theorem B6371095 : Blo 1676038 6371095 := bstep (se 1 (by rfl) ⟨4778321, by rfl⟩ : syracuseStep 6371095 = 9556643) B9556643
theorem B3184409 : Blo 1676038 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B1677099 : Blo 1676038 1677099 := bstep (se 1 (by rfl) ⟨1257824, by rfl⟩ : syracuseStep 1677099 = 2515649) B2515649
theorem B3225395 : Blo 1676038 3225395 := bstep (se 1 (by rfl) ⟨2419046, by rfl⟩ : syracuseStep 3225395 = 4838093) B4838093
theorem B1677111 : Blo 1676038 1677111 := bstep (se 1 (by rfl) ⟨1257833, by rfl⟩ : syracuseStep 1677111 = 2515667) B2515667
theorem B5658443 : Blo 1676038 5658443 := bstep (se 1 (by rfl) ⟨4243832, by rfl⟩ : syracuseStep 5658443 = 8487665) B8487665
theorem B1677131 : Blo 1676038 1677131 := bstep (se 1 (by rfl) ⟨1257848, by rfl⟩ : syracuseStep 1677131 = 2515697) B2515697
theorem B1677143 : Blo 1676038 1677143 := bstep (se 1 (by rfl) ⟨1257857, by rfl⟩ : syracuseStep 1677143 = 2515715) B2515715
theorem B2266967 : Blo 1676038 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B4028249 : Blo 1676038 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B12089189 : Blo 1676038 12089189 := bstep (se 4 (by rfl) ⟨1133361, by rfl⟩ : syracuseStep 12089189 = 2266723) B2266723
theorem B1677163 : Blo 1676038 1677163 := bstep (se 1 (by rfl) ⟨1257872, by rfl⟩ : syracuseStep 1677163 = 2515745) B2515745
theorem B1677175 : Blo 1676038 1677175 := bstep (se 1 (by rfl) ⟨1257881, by rfl⟩ : syracuseStep 1677175 = 2515763) B2515763
theorem B1677195 : Blo 1676038 1677195 := bstep (se 1 (by rfl) ⟨1257896, by rfl⟩ : syracuseStep 1677195 = 2515793) B2515793
theorem B3774347 : Blo 1676038 3774347 := bstep (se 1 (by rfl) ⟨2830760, by rfl⟩ : syracuseStep 3774347 = 5661521) B5661521
theorem B1677207 : Blo 1676038 1677207 := bstep (se 1 (by rfl) ⟨1257905, by rfl⟩ : syracuseStep 1677207 = 2515811) B2515811
theorem B1677227 : Blo 1676038 1677227 := bstep (se 1 (by rfl) ⟨1257920, by rfl⟩ : syracuseStep 1677227 = 2515841) B2515841
theorem B4773811 : Blo 1676038 4773811 := bstep (se 1 (by rfl) ⟨3580358, by rfl⟩ : syracuseStep 4773811 = 7160717) B7160717
theorem B1677239 : Blo 1676038 1677239 := bstep (se 1 (by rfl) ⟨1257929, by rfl⟩ : syracuseStep 1677239 = 2515859) B2515859
theorem B3774401 : Blo 1676038 3774401 := bstep (se 2 (by rfl) ⟨1415400, by rfl⟩ : syracuseStep 3774401 = 2830801) B2830801
theorem B1677259 : Blo 1676038 1677259 := bstep (se 1 (by rfl) ⟨1257944, by rfl⟩ : syracuseStep 1677259 = 2515889) B2515889
theorem B1677271 : Blo 1676038 1677271 := bstep (se 1 (by rfl) ⟨1257953, by rfl⟩ : syracuseStep 1677271 = 2515907) B2515907
theorem B1677291 : Blo 1676038 1677291 := bstep (se 1 (by rfl) ⟨1257968, by rfl⟩ : syracuseStep 1677291 = 2515937) B2515937
theorem B1677303 : Blo 1676038 1677303 := bstep (se 1 (by rfl) ⟨1257977, by rfl⟩ : syracuseStep 1677303 = 2515955) B2515955
theorem B1677323 : Blo 1676038 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B3225623 : Blo 1676038 3225623 := bstep (se 1 (by rfl) ⟨2419217, by rfl⟩ : syracuseStep 3225623 = 4838435) B4838435
theorem B1677335 : Blo 1676038 1677335 := bstep (se 1 (by rfl) ⟨1258001, by rfl⟩ : syracuseStep 1677335 = 2516003) B2516003
theorem B1677355 : Blo 1676038 1677355 := bstep (se 1 (by rfl) ⟨1258016, by rfl⟩ : syracuseStep 1677355 = 2516033) B2516033
theorem B1677367 : Blo 1676038 1677367 := bstep (se 1 (by rfl) ⟨1258025, by rfl⟩ : syracuseStep 1677367 = 2516051) B2516051
theorem B1677387 : Blo 1676038 1677387 := bstep (se 1 (by rfl) ⟨1258040, by rfl⟩ : syracuseStep 1677387 = 2516081) B2516081
theorem B1677399 : Blo 1676038 1677399 := bstep (se 1 (by rfl) ⟨1258049, by rfl⟩ : syracuseStep 1677399 = 2516099) B2516099
theorem B5658713 : Blo 1676038 5658713 := bstep (se 2 (by rfl) ⟨2122017, by rfl⟩ : syracuseStep 5658713 = 4244035) B4244035
theorem B1677419 : Blo 1676038 1677419 := bstep (se 1 (by rfl) ⟨1258064, by rfl⟩ : syracuseStep 1677419 = 2516129) B2516129
theorem B1677431 : Blo 1676038 1677431 := bstep (se 1 (by rfl) ⟨1258073, by rfl⟩ : syracuseStep 1677431 = 2516147) B2516147
theorem B1677451 : Blo 1676038 1677451 := bstep (se 1 (by rfl) ⟨1258088, by rfl⟩ : syracuseStep 1677451 = 2516177) B2516177
theorem B1677463 : Blo 1676038 1677463 := bstep (se 1 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 1677463 = 2516195) B2516195
theorem B3774617 : Blo 1676038 3774617 := bstep (se 2 (by rfl) ⟨1415481, by rfl⟩ : syracuseStep 3774617 = 2830963) B2830963
theorem B1677483 : Blo 1676038 1677483 := bstep (se 1 (by rfl) ⟨1258112, by rfl⟩ : syracuseStep 1677483 = 2516225) B2516225
theorem B1677495 : Blo 1676038 1677495 := bstep (se 1 (by rfl) ⟨1258121, by rfl⟩ : syracuseStep 1677495 = 2516243) B2516243
theorem B1677515 : Blo 1676038 1677515 := bstep (se 1 (by rfl) ⟨1258136, by rfl⟩ : syracuseStep 1677515 = 2516273) B2516273
theorem B1677527 : Blo 1676038 1677527 := bstep (se 1 (by rfl) ⟨1258145, by rfl⟩ : syracuseStep 1677527 = 2516291) B2516291
theorem B1677547 : Blo 1676038 1677547 := bstep (se 1 (by rfl) ⟨1258160, by rfl⟩ : syracuseStep 1677547 = 2516321) B2516321
theorem B3774707 : Blo 1676038 3774707 := bstep (se 1 (by rfl) ⟨2831030, by rfl⟩ : syracuseStep 3774707 = 5662061) B5662061
theorem B1677559 : Blo 1676038 1677559 := bstep (se 1 (by rfl) ⟨1258169, by rfl⟩ : syracuseStep 1677559 = 2516339) B2516339
theorem B1677579 : Blo 1676038 1677579 := bstep (se 1 (by rfl) ⟨1258184, by rfl⟩ : syracuseStep 1677579 = 2516369) B2516369
theorem B1677591 : Blo 1676038 1677591 := bstep (se 1 (by rfl) ⟨1258193, by rfl⟩ : syracuseStep 1677591 = 2516387) B2516387
theorem B3774743 : Blo 1676038 3774743 := bstep (se 1 (by rfl) ⟨2831057, by rfl⟩ : syracuseStep 3774743 = 5662115) B5662115
theorem B1677611 : Blo 1676038 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B1677623 : Blo 1676038 1677623 := bstep (se 1 (by rfl) ⟨1258217, by rfl⟩ : syracuseStep 1677623 = 2516435) B2516435
theorem B3021131 : Blo 1676038 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B1677643 : Blo 1676038 1677643 := bstep (se 1 (by rfl) ⟨1258232, by rfl⟩ : syracuseStep 1677643 = 2516465) B2516465
theorem B1677655 : Blo 1676038 1677655 := bstep (se 1 (by rfl) ⟨1258241, by rfl⟩ : syracuseStep 1677655 = 2516483) B2516483
theorem B1677675 : Blo 1676038 1677675 := bstep (se 1 (by rfl) ⟨1258256, by rfl⟩ : syracuseStep 1677675 = 2516513) B2516513
theorem B1677687 : Blo 1676038 1677687 := bstep (se 1 (by rfl) ⟨1258265, by rfl⟩ : syracuseStep 1677687 = 2516531) B2516531
theorem B1677707 : Blo 1676038 1677707 := bstep (se 1 (by rfl) ⟨1258280, by rfl⟩ : syracuseStep 1677707 = 2516561) B2516561
theorem B1677719 : Blo 1676038 1677719 := bstep (se 1 (by rfl) ⟨1258289, by rfl⟩ : syracuseStep 1677719 = 2516579) B2516579
theorem B1677739 : Blo 1676038 1677739 := bstep (se 1 (by rfl) ⟨1258304, by rfl⟩ : syracuseStep 1677739 = 2516609) B2516609
theorem B1677751 : Blo 1676038 1677751 := bstep (se 1 (by rfl) ⟨1258313, by rfl⟩ : syracuseStep 1677751 = 2516627) B2516627
theorem B3774923 : Blo 1676038 3774923 := bstep (se 1 (by rfl) ⟨2831192, by rfl⟩ : syracuseStep 3774923 = 5662385) B5662385
theorem B1677771 : Blo 1676038 1677771 := bstep (se 1 (by rfl) ⟨1258328, by rfl⟩ : syracuseStep 1677771 = 2516657) B2516657
theorem B1677783 : Blo 1676038 1677783 := bstep (se 1 (by rfl) ⟨1258337, by rfl⟩ : syracuseStep 1677783 = 2516675) B2516675
theorem B1677803 : Blo 1676038 1677803 := bstep (se 1 (by rfl) ⟨1258352, by rfl⟩ : syracuseStep 1677803 = 2516705) B2516705
theorem B1677815 : Blo 1676038 1677815 := bstep (se 1 (by rfl) ⟨1258361, by rfl⟩ : syracuseStep 1677815 = 2516723) B2516723
theorem B3774977 : Blo 1676038 3774977 := bstep (se 2 (by rfl) ⟨1415616, by rfl⟩ : syracuseStep 3774977 = 2831233) B2831233
theorem B3185153 : Blo 1676038 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B1677835 : Blo 1676038 1677835 := bstep (se 1 (by rfl) ⟨1258376, by rfl⟩ : syracuseStep 1677835 = 2516753) B2516753
theorem B1677847 : Blo 1676038 1677847 := bstep (se 1 (by rfl) ⟨1258385, by rfl⟩ : syracuseStep 1677847 = 2516771) B2516771
theorem B1677867 : Blo 1676038 1677867 := bstep (se 1 (by rfl) ⟨1258400, by rfl⟩ : syracuseStep 1677867 = 2516801) B2516801
theorem B1677879 : Blo 1676038 1677879 := bstep (se 1 (by rfl) ⟨1258409, by rfl⟩ : syracuseStep 1677879 = 2516819) B2516819
theorem B1677899 : Blo 1676038 1677899 := bstep (se 1 (by rfl) ⟨1258424, by rfl⟩ : syracuseStep 1677899 = 2516849) B2516849
theorem B1677911 : Blo 1676038 1677911 := bstep (se 1 (by rfl) ⟨1258433, by rfl⟩ : syracuseStep 1677911 = 2516867) B2516867
theorem B1677931 : Blo 1676038 1677931 := bstep (se 1 (by rfl) ⟨1258448, by rfl⟩ : syracuseStep 1677931 = 2516897) B2516897
theorem B1677943 : Blo 1676038 1677943 := bstep (se 1 (by rfl) ⟨1258457, by rfl⟩ : syracuseStep 1677943 = 2516915) B2516915
theorem B1677963 : Blo 1676038 1677963 := bstep (se 1 (by rfl) ⟨1258472, by rfl⟩ : syracuseStep 1677963 = 2516945) B2516945
theorem B1677975 : Blo 1676038 1677975 := bstep (se 1 (by rfl) ⟨1258481, by rfl⟩ : syracuseStep 1677975 = 2516963) B2516963
theorem B1677995 : Blo 1676038 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B1678007 : Blo 1676038 1678007 := bstep (se 1 (by rfl) ⟨1258505, by rfl⟩ : syracuseStep 1678007 = 2517011) B2517011
theorem B1678027 : Blo 1676038 1678027 := bstep (se 1 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 1678027 = 2517041) B2517041
theorem B4905689 : Blo 1676038 4905689 := bstep (se 2 (by rfl) ⟨1839633, by rfl⟩ : syracuseStep 4905689 = 3679267) B3679267
theorem B3775193 : Blo 1676038 3775193 := bstep (se 2 (by rfl) ⟨1415697, by rfl⟩ : syracuseStep 3775193 = 2831395) B2831395
theorem B3185419 : Blo 1676038 3185419 := bstep (se 1 (by rfl) ⟨2389064, by rfl⟩ : syracuseStep 3185419 = 4778129) B4778129
theorem B5659415 : Blo 1676038 5659415 := bstep (se 1 (by rfl) ⟨4244561, by rfl⟩ : syracuseStep 5659415 = 8489123) B8489123
theorem B3775283 : Blo 1676038 3775283 := bstep (se 1 (by rfl) ⟨2831462, by rfl⟩ : syracuseStep 3775283 = 5662925) B5662925
theorem B3775319 : Blo 1676038 3775319 := bstep (se 1 (by rfl) ⟨2831489, by rfl⟩ : syracuseStep 3775319 = 5662979) B5662979
theorem B5446489 : Blo 1676038 5446489 := bstep (se 2 (by rfl) ⟨2042433, by rfl⟩ : syracuseStep 5446489 = 4084867) B4084867
theorem B3824513 : Blo 1676038 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B3021707 : Blo 1676038 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B4774859 : Blo 1676038 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B3775499 : Blo 1676038 3775499 := bstep (se 1 (by rfl) ⟨2831624, by rfl⟩ : syracuseStep 3775499 = 5663249) B5663249
theorem B18127907 : Blo 1676038 18127907 := bstep (se 1 (by rfl) ⟨13595930, by rfl⟩ : syracuseStep 18127907 = 27191861) B27191861
theorem B8494145 : Blo 1676038 8494145 := bstep (se 2 (by rfl) ⟨3185304, by rfl⟩ : syracuseStep 8494145 = 6370609) B6370609
theorem B3775553 : Blo 1676038 3775553 := bstep (se 2 (by rfl) ⟨1415832, by rfl⟩ : syracuseStep 3775553 = 2831665) B2831665
theorem B17448029 : Blo 1676038 17448029 := bstep (se 3 (by rfl) ⟨3271505, by rfl⟩ : syracuseStep 17448029 = 6543011) B6543011
theorem B6364291 : Blo 1676038 6364291 := bstep (se 1 (by rfl) ⟨4773218, by rfl⟩ : syracuseStep 6364291 = 9546437) B9546437
theorem B2514059 : Blo 1676038 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B2514071 : Blo 1676038 2514071 := bstep (se 1 (by rfl) ⟨1885553, by rfl⟩ : syracuseStep 2514071 = 3771107) B3771107
theorem B2514137 : Blo 1676038 2514137 := bstep (se 2 (by rfl) ⟨942801, by rfl⟩ : syracuseStep 2514137 = 1885603) B1885603
theorem B3022067 : Blo 1676038 3022067 := bstep (se 1 (by rfl) ⟨2266550, by rfl⟩ : syracuseStep 3022067 = 4533101) B4533101
theorem B3398935 : Blo 1676038 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B4242739 : Blo 1676038 4242739 := bstep (se 1 (by rfl) ⟨3182054, by rfl⟩ : syracuseStep 4242739 = 6364109) B6364109
theorem B5659955 : Blo 1676038 5659955 := bstep (se 1 (by rfl) ⟨4244966, by rfl⟩ : syracuseStep 5659955 = 8489933) B8489933
theorem B2514251 : Blo 1676038 2514251 := bstep (se 1 (by rfl) ⟨1885688, by rfl⟩ : syracuseStep 2514251 = 3771377) B3771377
theorem B2514263 : Blo 1676038 2514263 := bstep (se 1 (by rfl) ⟨1885697, by rfl⟩ : syracuseStep 2514263 = 3771395) B3771395
theorem B2620759 : Blo 1676038 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B2514329 : Blo 1676038 2514329 := bstep (se 2 (by rfl) ⟨942873, by rfl⟩ : syracuseStep 2514329 = 1885747) B1885747
theorem B6364595 : Blo 1676038 6364595 := bstep (se 1 (by rfl) ⟨4773446, by rfl⟩ : syracuseStep 6364595 = 9546893) B9546893
theorem B16121267 : Blo 1676038 16121267 := bstep (se 1 (by rfl) ⟨12090950, by rfl⟩ : syracuseStep 16121267 = 24181901) B24181901
theorem B4242881 : Blo 1676038 4242881 := bstep (se 2 (by rfl) ⟨1591080, by rfl⟩ : syracuseStep 4242881 = 3182161) B3182161
theorem B6045131 : Blo 1676038 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B2514443 : Blo 1676038 2514443 := bstep (se 1 (by rfl) ⟨1885832, by rfl⟩ : syracuseStep 2514443 = 3771665) B3771665
theorem B2514455 : Blo 1676038 2514455 := bstep (se 1 (by rfl) ⟨1885841, by rfl⟩ : syracuseStep 2514455 = 3771683) B3771683
theorem B5660225 : Blo 1676038 5660225 := bstep (se 2 (by rfl) ⟨2122584, by rfl⟩ : syracuseStep 5660225 = 4245169) B4245169
theorem B14319179 : Blo 1676038 14319179 := bstep (se 1 (by rfl) ⟨10739384, by rfl⟩ : syracuseStep 14319179 = 21478769) B21478769
theorem B1965655 : Blo 1676038 1965655 := bstep (se 1 (by rfl) ⟨1474241, by rfl⟩ : syracuseStep 1965655 = 2948483) B2948483
theorem B2514521 : Blo 1676038 2514521 := bstep (se 2 (by rfl) ⟨942945, by rfl⟩ : syracuseStep 2514521 = 1885891) B1885891
theorem B8486531 : Blo 1676038 8486531 := bstep (se 1 (by rfl) ⟨6364898, by rfl⟩ : syracuseStep 8486531 = 12729797) B12729797
theorem B7167619 : Blo 1676038 7167619 := bstep (se 1 (by rfl) ⟨5375714, by rfl⟩ : syracuseStep 7167619 = 10751429) B10751429
theorem B2514635 : Blo 1676038 2514635 := bstep (se 1 (by rfl) ⟨1885976, by rfl⟩ : syracuseStep 2514635 = 3771953) B3771953
theorem B2514647 : Blo 1676038 2514647 := bstep (se 1 (by rfl) ⟨1885985, by rfl⟩ : syracuseStep 2514647 = 3771971) B3771971
theorem B2686679 : Blo 1676038 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B2514713 : Blo 1676038 2514713 := bstep (se 2 (by rfl) ⟨943017, by rfl⟩ : syracuseStep 2514713 = 1886035) B1886035
theorem B2121547 : Blo 1676038 2121547 := bstep (se 1 (by rfl) ⟨1591160, by rfl⟩ : syracuseStep 2121547 = 3182321) B3182321
theorem B2686807 : Blo 1676038 2686807 := bstep (se 1 (by rfl) ⟨2015105, by rfl⟩ : syracuseStep 2686807 = 4030211) B4030211
theorem B2514827 : Blo 1676038 2514827 := bstep (se 1 (by rfl) ⟨1886120, by rfl⟩ : syracuseStep 2514827 = 3772241) B3772241
theorem B2514839 : Blo 1676038 2514839 := bstep (se 1 (by rfl) ⟨1886129, by rfl⟩ : syracuseStep 2514839 = 3772259) B3772259
theorem B2514905 : Blo 1676038 2514905 := bstep (se 2 (by rfl) ⟨943089, by rfl⟩ : syracuseStep 2514905 = 1886179) B1886179
theorem B2514959 : Blo 1676038 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B4243499 : Blo 1676038 4243499 := bstep (se 1 (by rfl) ⟨3182624, by rfl⟩ : syracuseStep 4243499 = 6365249) B6365249
theorem B2515001 : Blo 1676038 2515001 := bstep (se 2 (by rfl) ⟨943125, by rfl⟩ : syracuseStep 2515001 = 1886251) B1886251
theorem B8601661 : Blo 1676038 8601661 := bstep (se 3 (by rfl) ⟨1612811, by rfl⟩ : syracuseStep 8601661 = 3225623) B3225623
theorem B2515079 : Blo 1676038 2515079 := bstep (se 1 (by rfl) ⟨1886309, by rfl⟩ : syracuseStep 2515079 = 3772619) B3772619
theorem B2121871 : Blo 1676038 2121871 := bstep (se 1 (by rfl) ⟨1591403, by rfl⟩ : syracuseStep 2121871 = 3182807) B3182807
theorem B3580051 : Blo 1676038 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B2515115 : Blo 1676038 2515115 := bstep (se 1 (by rfl) ⟨1886336, by rfl⟩ : syracuseStep 2515115 = 3772673) B3772673
theorem B2515145 : Blo 1676038 2515145 := bstep (se 2 (by rfl) ⟨943179, by rfl⟩ : syracuseStep 2515145 = 1886359) B1886359
theorem B5660873 : Blo 1676038 5660873 := bstep (se 2 (by rfl) ⟨2122827, by rfl⟩ : syracuseStep 5660873 = 4245655) B4245655
theorem B2515259 : Blo 1676038 2515259 := bstep (se 1 (by rfl) ⟨1886444, by rfl⟩ : syracuseStep 2515259 = 3772889) B3772889
theorem B2515319 : Blo 1676038 2515319 := bstep (se 1 (by rfl) ⟨1886489, by rfl⟩ : syracuseStep 2515319 = 3772979) B3772979
theorem B2515343 : Blo 1676038 2515343 := bstep (se 1 (by rfl) ⟨1886507, by rfl⟩ : syracuseStep 2515343 = 3773015) B3773015
theorem B12730769 : Blo 1676038 12730769 := bstep (se 2 (by rfl) ⟨4774038, by rfl⟩ : syracuseStep 12730769 = 9548077) B9548077
theorem B20390291 : Blo 1676038 20390291 := bstep (se 1 (by rfl) ⟨15292718, by rfl⟩ : syracuseStep 20390291 = 30585437) B30585437
theorem B2515385 : Blo 1676038 2515385 := bstep (se 2 (by rfl) ⟨943269, by rfl⟩ : syracuseStep 2515385 = 1886539) B1886539
theorem B2515463 : Blo 1676038 2515463 := bstep (se 1 (by rfl) ⟨1886597, by rfl⟩ : syracuseStep 2515463 = 3773195) B3773195
theorem B9069079 : Blo 1676038 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B6455837 : Blo 1676038 6455837 := bstep (se 3 (by rfl) ⟨1210469, by rfl⟩ : syracuseStep 6455837 = 2420939) B2420939
theorem B2515499 : Blo 1676038 2515499 := bstep (se 1 (by rfl) ⟨1886624, by rfl⟩ : syracuseStep 2515499 = 3773249) B3773249
theorem B9552451 : Blo 1676038 9552451 := bstep (se 1 (by rfl) ⟨7164338, by rfl⟩ : syracuseStep 9552451 = 14328677) B14328677
theorem B2515529 : Blo 1676038 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B2515643 : Blo 1676038 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B2515703 : Blo 1676038 2515703 := bstep (se 1 (by rfl) ⟨1886777, by rfl⟩ : syracuseStep 2515703 = 3773555) B3773555
theorem B2515727 : Blo 1676038 2515727 := bstep (se 1 (by rfl) ⟨1886795, by rfl⟩ : syracuseStep 2515727 = 3773591) B3773591
theorem B4842269 : Blo 1676038 4842269 := bstep (se 3 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 4842269 = 1815851) B1815851
theorem B2515769 : Blo 1676038 2515769 := bstep (se 2 (by rfl) ⟨943413, by rfl⟩ : syracuseStep 2515769 = 1886827) B1886827
theorem B4244339 : Blo 1676038 4244339 := bstep (se 1 (by rfl) ⟨3183254, by rfl⟩ : syracuseStep 4244339 = 6366509) B6366509
theorem B2122615 : Blo 1676038 2122615 := bstep (se 1 (by rfl) ⟨1591961, by rfl⟩ : syracuseStep 2122615 = 3183923) B3183923
theorem B4244359 : Blo 1676038 4244359 := bstep (se 1 (by rfl) ⟨3183269, by rfl⟩ : syracuseStep 4244359 = 6366539) B6366539
theorem B2515847 : Blo 1676038 2515847 := bstep (se 1 (by rfl) ⟨1886885, by rfl⟩ : syracuseStep 2515847 = 3773771) B3773771
theorem B5661575 : Blo 1676038 5661575 := bstep (se 1 (by rfl) ⟨4246181, by rfl⟩ : syracuseStep 5661575 = 8492363) B8492363
theorem B8487827 : Blo 1676038 8487827 := bstep (se 1 (by rfl) ⟨6365870, by rfl⟩ : syracuseStep 8487827 = 12731741) B12731741
theorem B2515883 : Blo 1676038 2515883 := bstep (se 1 (by rfl) ⟨1886912, by rfl⟩ : syracuseStep 2515883 = 3773825) B3773825
theorem B2515913 : Blo 1676038 2515913 := bstep (se 2 (by rfl) ⟨943467, by rfl⟩ : syracuseStep 2515913 = 1886935) B1886935
theorem B22938635 : Blo 1676038 22938635 := bstep (se 1 (by rfl) ⟨17203976, by rfl⟩ : syracuseStep 22938635 = 34407953) B34407953
theorem B2516027 : Blo 1676038 2516027 := bstep (se 1 (by rfl) ⟨1887020, by rfl⟩ : syracuseStep 2516027 = 3774041) B3774041
theorem B2516087 : Blo 1676038 2516087 := bstep (se 1 (by rfl) ⟨1887065, by rfl⟩ : syracuseStep 2516087 = 3774131) B3774131
theorem B2516111 : Blo 1676038 2516111 := bstep (se 1 (by rfl) ⟨1887083, by rfl⟩ : syracuseStep 2516111 = 3774167) B3774167
theorem B4244633 : Blo 1676038 4244633 := bstep (se 2 (by rfl) ⟨1591737, by rfl⟩ : syracuseStep 4244633 = 3183475) B3183475
theorem B2516153 : Blo 1676038 2516153 := bstep (se 2 (by rfl) ⟨943557, by rfl⟩ : syracuseStep 2516153 = 1887115) B1887115
theorem B2122939 : Blo 1676038 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B5661953 : Blo 1676038 5661953 := bstep (se 2 (by rfl) ⟨2123232, by rfl⟩ : syracuseStep 5661953 = 4246465) B4246465
theorem B2516231 : Blo 1676038 2516231 := bstep (se 1 (by rfl) ⟨1887173, by rfl⟩ : syracuseStep 2516231 = 3774347) B3774347
theorem B10741025 : Blo 1676038 10741025 := bstep (se 2 (by rfl) ⟨4027884, by rfl⟩ : syracuseStep 10741025 = 8055769) B8055769
theorem B2516267 : Blo 1676038 2516267 := bstep (se 1 (by rfl) ⟨1887200, by rfl⟩ : syracuseStep 2516267 = 3774401) B3774401
theorem B4244795 : Blo 1676038 4244795 := bstep (se 1 (by rfl) ⟨3183596, by rfl⟩ : syracuseStep 4244795 = 6367193) B6367193
theorem B2516297 : Blo 1676038 2516297 := bstep (se 2 (by rfl) ⟨943611, by rfl⟩ : syracuseStep 2516297 = 1887223) B1887223
theorem B10741177 : Blo 1676038 10741177 := bstep (se 2 (by rfl) ⟨4027941, by rfl⟩ : syracuseStep 10741177 = 8055883) B8055883
theorem B2516411 : Blo 1676038 2516411 := bstep (se 1 (by rfl) ⟨1887308, by rfl⟩ : syracuseStep 2516411 = 3774617) B3774617
theorem B2516471 : Blo 1676038 2516471 := bstep (se 1 (by rfl) ⟨1887353, by rfl⟩ : syracuseStep 2516471 = 3774707) B3774707
theorem B1885711 : Blo 1676038 1885711 := bstep (se 1 (by rfl) ⟨1414283, by rfl⟩ : syracuseStep 1885711 = 2828567) B2828567
theorem B4245007 : Blo 1676038 4245007 := bstep (se 1 (by rfl) ⟨3183755, by rfl⟩ : syracuseStep 4245007 = 6367511) B6367511
theorem B2516495 : Blo 1676038 2516495 := bstep (se 1 (by rfl) ⟨1887371, by rfl⟩ : syracuseStep 2516495 = 3774743) B3774743
theorem B2516537 : Blo 1676038 2516537 := bstep (se 2 (by rfl) ⟨943701, by rfl⟩ : syracuseStep 2516537 = 1887403) B1887403
theorem B2516615 : Blo 1676038 2516615 := bstep (se 1 (by rfl) ⟨1887461, by rfl⟩ : syracuseStep 2516615 = 3774923) B3774923
theorem B2516651 : Blo 1676038 2516651 := bstep (se 1 (by rfl) ⟨1887488, by rfl⟩ : syracuseStep 2516651 = 3774977) B3774977
theorem B2123435 : Blo 1676038 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B4531913 : Blo 1676038 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B2516681 : Blo 1676038 2516681 := bstep (se 2 (by rfl) ⟨943755, by rfl⟩ : syracuseStep 2516681 = 1887511) B1887511
theorem B9070309 : Blo 1676038 9070309 := bstep (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) B1700683
theorem B17221349 : Blo 1676038 17221349 := bstep (se 4 (by rfl) ⟨1614501, by rfl⟩ : syracuseStep 17221349 = 3229003) B3229003
theorem B4245281 : Blo 1676038 4245281 := bstep (se 2 (by rfl) ⟨1591980, by rfl⟩ : syracuseStep 4245281 = 3183961) B3183961
theorem B5736251 : Blo 1676038 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B2516795 : Blo 1676038 2516795 := bstep (se 1 (by rfl) ⟨1887596, by rfl⟩ : syracuseStep 2516795 = 3775193) B3775193
theorem B12912473 : Blo 1676038 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B2516855 : Blo 1676038 2516855 := bstep (se 1 (by rfl) ⟨1887641, by rfl⟩ : syracuseStep 2516855 = 3775283) B3775283
theorem B2516879 : Blo 1676038 2516879 := bstep (se 1 (by rfl) ⟨1887659, by rfl⟩ : syracuseStep 2516879 = 3775319) B3775319
theorem B2549675 : Blo 1676038 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B2516921 : Blo 1676038 2516921 := bstep (se 2 (by rfl) ⟨943845, by rfl⟩ : syracuseStep 2516921 = 1887691) B1887691
theorem B1886215 : Blo 1676038 1886215 := bstep (se 1 (by rfl) ⟨1414661, by rfl⟩ : syracuseStep 1886215 = 2829323) B2829323
theorem B2516999 : Blo 1676038 2516999 := bstep (se 1 (by rfl) ⟨1887749, by rfl⟩ : syracuseStep 2516999 = 3775499) B3775499
theorem B12085271 : Blo 1676038 12085271 := bstep (se 1 (by rfl) ⟨9063953, by rfl⟩ : syracuseStep 12085271 = 18127907) B18127907
theorem B5662763 : Blo 1676038 5662763 := bstep (se 1 (by rfl) ⟨4247072, by rfl⟩ : syracuseStep 5662763 = 8494145) B8494145
theorem B2517035 : Blo 1676038 2517035 := bstep (se 1 (by rfl) ⟨1887776, by rfl⟩ : syracuseStep 2517035 = 3775553) B3775553
theorem B2328719 : Blo 1676038 2328719 := bstep (se 1 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 2328719 = 3493079) B3493079
theorem B1886395 : Blo 1676038 1886395 := bstep (se 1 (by rfl) ⟨1414796, by rfl⟩ : syracuseStep 1886395 = 2829593) B2829593
theorem B4778185 : Blo 1676038 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B10741997 : Blo 1676038 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B32237837 : Blo 1676038 32237837 := bstep (se 3 (by rfl) ⟨6044594, by rfl⟩ : syracuseStep 32237837 = 12089189) B12089189
theorem B5097757 : Blo 1676038 5097757 := bstep (se 3 (by rfl) ⟨955829, by rfl⟩ : syracuseStep 5097757 = 1911659) B1911659
theorem B2828587 : Blo 1676038 2828587 := bstep (se 1 (by rfl) ⟨2121440, by rfl⟩ : syracuseStep 2828587 = 4242881) B4242881
theorem B9546119 : Blo 1676038 9546119 := bstep (se 1 (by rfl) ⟨7159589, by rfl⟩ : syracuseStep 9546119 = 14319179) B14319179
theorem B2828729 : Blo 1676038 2828729 := bstep (se 2 (by rfl) ⟨1060773, by rfl⟩ : syracuseStep 2828729 = 2121547) B2121547
theorem B3582409 : Blo 1676038 3582409 := bstep (se 2 (by rfl) ⟨1343403, by rfl⟩ : syracuseStep 3582409 = 2686807) B2686807
theorem B9554435 : Blo 1676038 9554435 := bstep (se 1 (by rfl) ⟨7165826, by rfl⟩ : syracuseStep 9554435 = 14331653) B14331653
theorem B1886863 : Blo 1676038 1886863 := bstep (se 1 (by rfl) ⟨1415147, by rfl⟩ : syracuseStep 1886863 = 2830295) B2830295
theorem B19098341 : Blo 1676038 19098341 := bstep (se 4 (by rfl) ⟨1790469, by rfl⟩ : syracuseStep 19098341 = 3580939) B3580939
theorem B4532993 : Blo 1676038 4532993 := bstep (se 2 (by rfl) ⟨1699872, by rfl⟩ : syracuseStep 4532993 = 3399745) B3399745
theorem B4246283 : Blo 1676038 4246283 := bstep (se 1 (by rfl) ⟨3184712, by rfl⟩ : syracuseStep 4246283 = 6369425) B6369425
theorem B12733199 : Blo 1676038 12733199 := bstep (se 1 (by rfl) ⟨9549899, by rfl⟩ : syracuseStep 12733199 = 19099799) B19099799
theorem B28658447 : Blo 1676038 28658447 := bstep (se 1 (by rfl) ⟨21493835, by rfl⟩ : syracuseStep 28658447 = 42987671) B42987671
theorem B9186085 : Blo 1676038 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B3771179 : Blo 1676038 3771179 := bstep (se 1 (by rfl) ⟨2828384, by rfl⟩ : syracuseStep 3771179 = 5656769) B5656769
theorem B38742947 : Blo 1676038 38742947 := bstep (se 1 (by rfl) ⟨29057210, by rfl⟩ : syracuseStep 38742947 = 58114421) B58114421
theorem B2829431 : Blo 1676038 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B1887367 : Blo 1676038 1887367 := bstep (se 1 (by rfl) ⟨1415525, by rfl⟩ : syracuseStep 1887367 = 2831051) B2831051
theorem B3771539 : Blo 1676038 3771539 := bstep (se 1 (by rfl) ⟨2828654, by rfl⟩ : syracuseStep 3771539 = 5657309) B5657309
theorem B3771593 : Blo 1676038 3771593 := bstep (se 2 (by rfl) ⟨1414347, by rfl⟩ : syracuseStep 3771593 = 2828695) B2828695
theorem B19107089 : Blo 1676038 19107089 := bstep (se 2 (by rfl) ⟨7165158, by rfl⟩ : syracuseStep 19107089 = 14330317) B14330317
theorem B10218803 : Blo 1676038 10218803 := bstep (se 1 (by rfl) ⟨7664102, by rfl⟩ : syracuseStep 10218803 = 15328205) B15328205
theorem B1887547 : Blo 1676038 1887547 := bstep (se 1 (by rfl) ⟨1415660, by rfl⟩ : syracuseStep 1887547 = 2831321) B2831321
theorem B28667195 : Blo 1676038 28667195 := bstep (se 1 (by rfl) ⟨21500396, by rfl⟩ : syracuseStep 28667195 = 43000793) B43000793
theorem B12741947 : Blo 1676038 12741947 := bstep (se 1 (by rfl) ⟨9556460, by rfl⟩ : syracuseStep 12741947 = 19112921) B19112921
theorem B4246931 : Blo 1676038 4246931 := bstep (se 1 (by rfl) ⟨3185198, by rfl⟩ : syracuseStep 4246931 = 6370397) B6370397
theorem B6368665 : Blo 1676038 6368665 := bstep (se 2 (by rfl) ⟨2388249, by rfl⟩ : syracuseStep 6368665 = 4776499) B4776499
theorem B6450617 : Blo 1676038 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B48344525 : Blo 1676038 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B2829883 : Blo 1676038 2829883 := bstep (se 1 (by rfl) ⟨2122412, by rfl⟩ : syracuseStep 2829883 = 4244825) B4244825
theorem B4247225 : Blo 1676038 4247225 := bstep (se 2 (by rfl) ⟨1592709, by rfl⟩ : syracuseStep 4247225 = 3185419) B3185419
theorem B2830025 : Blo 1676038 2830025 := bstep (se 2 (by rfl) ⟨1061259, by rfl⟩ : syracuseStep 2830025 = 2122519) B2122519
theorem B6368969 : Blo 1676038 6368969 := bstep (se 2 (by rfl) ⟨2388363, by rfl⟩ : syracuseStep 6368969 = 4776727) B4776727
theorem B4534031 : Blo 1676038 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B3583759 : Blo 1676038 3583759 := bstep (se 1 (by rfl) ⟨2687819, by rfl⟩ : syracuseStep 3583759 = 5375639) B5375639
theorem B7261985 : Blo 1676038 7261985 := bstep (se 2 (by rfl) ⟨2723244, by rfl⟩ : syracuseStep 7261985 = 5446489) B5446489
theorem B2150263 : Blo 1676038 2150263 := bstep (se 1 (by rfl) ⟨1612697, by rfl⟩ : syracuseStep 2150263 = 3225395) B3225395
theorem B3772295 : Blo 1676038 3772295 := bstep (se 1 (by rfl) ⟨2829221, by rfl⟩ : syracuseStep 3772295 = 5658443) B5658443
theorem B8490905 : Blo 1676038 8490905 := bstep (se 2 (by rfl) ⟨3184089, by rfl⟩ : syracuseStep 8490905 = 6368179) B6368179
theorem B4304897 : Blo 1676038 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B3772475 : Blo 1676038 3772475 := bstep (se 1 (by rfl) ⟨2829356, by rfl⟩ : syracuseStep 3772475 = 5658713) B5658713
theorem B9547895 : Blo 1676038 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B3772601 : Blo 1676038 3772601 := bstep (se 2 (by rfl) ⟨1414725, by rfl⟩ : syracuseStep 3772601 = 2829451) B2829451
theorem B2830727 : Blo 1676038 2830727 := bstep (se 1 (by rfl) ⟨2123045, by rfl⟩ : syracuseStep 2830727 = 4246091) B4246091
theorem B5656985 : Blo 1676038 5656985 := bstep (se 2 (by rfl) ⟨2121369, by rfl⟩ : syracuseStep 5656985 = 4242739) B4242739
theorem B3494345 : Blo 1676038 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B3772943 : Blo 1676038 3772943 := bstep (se 1 (by rfl) ⟨2829707, by rfl⟩ : syracuseStep 3772943 = 5659415) B5659415
theorem B3772961 : Blo 1676038 3772961 := bstep (se 2 (by rfl) ⟨1414860, by rfl⟩ : syracuseStep 3772961 = 2829721) B2829721
theorem B2388523 : Blo 1676038 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B6369911 : Blo 1676038 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B3183239 : Blo 1676038 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B1815175 : Blo 1676038 1815175 := bstep (se 1 (by rfl) ⟨1361381, by rfl⟩ : syracuseStep 1815175 = 2722763) B2722763
theorem B1676039 : Blo 1676038 1676039 := bstep (se 1 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 1676039 = 2514059) B2514059
theorem B1700615 : Blo 1676038 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B1676047 : Blo 1676038 1676047 := bstep (se 1 (by rfl) ⟨1257035, by rfl⟩ : syracuseStep 1676047 = 2514071) B2514071
theorem B1676091 : Blo 1676038 1676091 := bstep (se 1 (by rfl) ⟨1257068, by rfl⟩ : syracuseStep 1676091 = 2514137) B2514137
theorem B9548603 : Blo 1676038 9548603 := bstep (se 1 (by rfl) ⟨7161452, by rfl⟩ : syracuseStep 9548603 = 14322905) B14322905
theorem B9556825 : Blo 1676038 9556825 := bstep (se 2 (by rfl) ⟨3583809, by rfl⟩ : syracuseStep 9556825 = 7167619) B7167619
theorem B3773303 : Blo 1676038 3773303 := bstep (se 1 (by rfl) ⟨2829977, by rfl⟩ : syracuseStep 3773303 = 5659955) B5659955
theorem B1676167 : Blo 1676038 1676167 := bstep (se 1 (by rfl) ⟨1257125, by rfl⟩ : syracuseStep 1676167 = 2514251) B2514251
theorem B1676175 : Blo 1676038 1676175 := bstep (se 1 (by rfl) ⟨1257131, by rfl⟩ : syracuseStep 1676175 = 2514263) B2514263
theorem B1676219 : Blo 1676038 1676219 := bstep (se 1 (by rfl) ⟨1257164, by rfl⟩ : syracuseStep 1676219 = 2514329) B2514329
theorem B1676295 : Blo 1676038 1676295 := bstep (se 1 (by rfl) ⟨1257221, by rfl⟩ : syracuseStep 1676295 = 2514443) B2514443
theorem B1676303 : Blo 1676038 1676303 := bstep (se 1 (by rfl) ⟨1257227, by rfl⟩ : syracuseStep 1676303 = 2514455) B2514455
theorem B2831375 : Blo 1676038 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B5370923 : Blo 1676038 5370923 := bstep (se 1 (by rfl) ⟨4028192, by rfl⟩ : syracuseStep 5370923 = 8056385) B8056385
theorem B3773483 : Blo 1676038 3773483 := bstep (se 1 (by rfl) ⟨2830112, by rfl⟩ : syracuseStep 3773483 = 5660225) B5660225
theorem B1676347 : Blo 1676038 1676347 := bstep (se 1 (by rfl) ⟨1257260, by rfl⟩ : syracuseStep 1676347 = 2514521) B2514521
theorem B5657687 : Blo 1676038 5657687 := bstep (se 1 (by rfl) ⟨4243265, by rfl⟩ : syracuseStep 5657687 = 8486531) B8486531
theorem B1676423 : Blo 1676038 1676423 := bstep (se 1 (by rfl) ⟨1257317, by rfl⟩ : syracuseStep 1676423 = 2514635) B2514635
theorem B1676431 : Blo 1676038 1676431 := bstep (se 1 (by rfl) ⟨1257323, by rfl⟩ : syracuseStep 1676431 = 2514647) B2514647
theorem B1791119 : Blo 1676038 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B1676475 : Blo 1676038 1676475 := bstep (se 1 (by rfl) ⟨1257356, by rfl⟩ : syracuseStep 1676475 = 2514713) B2514713
theorem B1676551 : Blo 1676038 1676551 := bstep (se 1 (by rfl) ⟨1257413, by rfl⟩ : syracuseStep 1676551 = 2514827) B2514827
theorem B1676559 : Blo 1676038 1676559 := bstep (se 1 (by rfl) ⟨1257419, by rfl⟩ : syracuseStep 1676559 = 2514839) B2514839
theorem B1676603 : Blo 1676038 1676603 := bstep (se 1 (by rfl) ⟨1257452, by rfl⟩ : syracuseStep 1676603 = 2514905) B2514905
theorem B1676679 : Blo 1676038 1676679 := bstep (se 1 (by rfl) ⟨1257509, by rfl⟩ : syracuseStep 1676679 = 2515019) B2515019
theorem B1676687 : Blo 1676038 1676687 := bstep (se 1 (by rfl) ⟨1257515, by rfl⟩ : syracuseStep 1676687 = 2515031) B2515031
theorem B3773843 : Blo 1676038 3773843 := bstep (se 1 (by rfl) ⟨2830382, by rfl⟩ : syracuseStep 3773843 = 5660765) B5660765
theorem B7165331 : Blo 1676038 7165331 := bstep (se 1 (by rfl) ⟨5373998, by rfl⟩ : syracuseStep 7165331 = 10747997) B10747997
theorem B1676731 : Blo 1676038 1676731 := bstep (se 1 (by rfl) ⟨1257548, by rfl⟩ : syracuseStep 1676731 = 2515097) B2515097
theorem B3773897 : Blo 1676038 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B1676807 : Blo 1676038 1676807 := bstep (se 1 (by rfl) ⟨1257605, by rfl⟩ : syracuseStep 1676807 = 2515211) B2515211
theorem B1676815 : Blo 1676038 1676815 := bstep (se 1 (by rfl) ⟨1257611, by rfl⟩ : syracuseStep 1676815 = 2515223) B2515223
theorem B1676859 : Blo 1676038 1676859 := bstep (se 1 (by rfl) ⟨1257644, by rfl⟩ : syracuseStep 1676859 = 2515289) B2515289
theorem B5658173 : Blo 1676038 5658173 := bstep (se 3 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 5658173 = 2121815) B2121815
theorem B6370883 : Blo 1676038 6370883 := bstep (se 1 (by rfl) ⟨4778162, by rfl⟩ : syracuseStep 6370883 = 9556325) B9556325
theorem B4028039 : Blo 1676038 4028039 := bstep (se 1 (by rfl) ⟨3021029, by rfl⟩ : syracuseStep 4028039 = 6042059) B6042059
theorem B1676935 : Blo 1676038 1676935 := bstep (se 1 (by rfl) ⟨1257701, by rfl⟩ : syracuseStep 1676935 = 2515403) B2515403
theorem B1676943 : Blo 1676038 1676943 := bstep (se 1 (by rfl) ⟨1257707, by rfl⟩ : syracuseStep 1676943 = 2515415) B2515415
theorem B1676987 : Blo 1676038 1676987 := bstep (se 1 (by rfl) ⟨1257740, by rfl⟩ : syracuseStep 1676987 = 2515481) B2515481
theorem B1677063 : Blo 1676038 1677063 := bstep (se 1 (by rfl) ⟨1257797, by rfl⟩ : syracuseStep 1677063 = 2515595) B2515595
theorem B1677071 : Blo 1676038 1677071 := bstep (se 1 (by rfl) ⟨1257803, by rfl⟩ : syracuseStep 1677071 = 2515607) B2515607
theorem B17446691 : Blo 1676038 17446691 := bstep (se 1 (by rfl) ⟨13085018, by rfl⟩ : syracuseStep 17446691 = 26170037) B26170037
theorem B2684731 : Blo 1676038 2684731 := bstep (se 1 (by rfl) ⟨2013548, by rfl⟩ : syracuseStep 2684731 = 4027097) B4027097
theorem B1677115 : Blo 1676038 1677115 := bstep (se 1 (by rfl) ⟨1257836, by rfl⟩ : syracuseStep 1677115 = 2515673) B2515673
theorem B1677191 : Blo 1676038 1677191 := bstep (se 1 (by rfl) ⟨1257893, by rfl⟩ : syracuseStep 1677191 = 2515787) B2515787
theorem B1677199 : Blo 1676038 1677199 := bstep (se 1 (by rfl) ⟨1257899, by rfl⟩ : syracuseStep 1677199 = 2515799) B2515799
theorem B1677243 : Blo 1676038 1677243 := bstep (se 1 (by rfl) ⟨1257932, by rfl⟩ : syracuseStep 1677243 = 2515865) B2515865
theorem B8058845 : Blo 1676038 8058845 := bstep (se 3 (by rfl) ⟨1511033, by rfl⟩ : syracuseStep 8058845 = 3022067) B3022067
theorem B1677319 : Blo 1676038 1677319 := bstep (se 1 (by rfl) ⟨1257989, by rfl⟩ : syracuseStep 1677319 = 2515979) B2515979
theorem B1677327 : Blo 1676038 1677327 := bstep (se 1 (by rfl) ⟨1257995, by rfl⟩ : syracuseStep 1677327 = 2515991) B2515991
theorem B1677371 : Blo 1676038 1677371 := bstep (se 1 (by rfl) ⟨1258028, by rfl⟩ : syracuseStep 1677371 = 2516057) B2516057
theorem B19110005 : Blo 1676038 19110005 := bstep (se 5 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 19110005 = 1791563) B1791563
theorem B1677447 : Blo 1676038 1677447 := bstep (se 1 (by rfl) ⟨1258085, by rfl⟩ : syracuseStep 1677447 = 2516171) B2516171
theorem B3774599 : Blo 1676038 3774599 := bstep (se 1 (by rfl) ⟨2830949, by rfl⟩ : syracuseStep 3774599 = 5661899) B5661899
theorem B1677455 : Blo 1676038 1677455 := bstep (se 1 (by rfl) ⟨1258091, by rfl⟩ : syracuseStep 1677455 = 2516183) B2516183
theorem B1677499 : Blo 1676038 1677499 := bstep (se 1 (by rfl) ⟨1258124, by rfl⟩ : syracuseStep 1677499 = 2516249) B2516249
theorem B9550061 : Blo 1676038 9550061 := bstep (se 3 (by rfl) ⟨1790636, by rfl⟩ : syracuseStep 9550061 = 3581273) B3581273
theorem B7756013 : Blo 1676038 7756013 := bstep (se 3 (by rfl) ⟨1454252, by rfl⟩ : syracuseStep 7756013 = 2908505) B2908505
theorem B17217773 : Blo 1676038 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B1677575 : Blo 1676038 1677575 := bstep (se 1 (by rfl) ⟨1258181, by rfl⟩ : syracuseStep 1677575 = 2516363) B2516363
theorem B1677583 : Blo 1676038 1677583 := bstep (se 1 (by rfl) ⟨1258187, by rfl⟩ : syracuseStep 1677583 = 2516375) B2516375
theorem B1677627 : Blo 1676038 1677627 := bstep (se 1 (by rfl) ⟨1258220, by rfl⟩ : syracuseStep 1677627 = 2516441) B2516441
theorem B3774779 : Blo 1676038 3774779 := bstep (se 1 (by rfl) ⟨2831084, by rfl⟩ : syracuseStep 3774779 = 5662169) B5662169
theorem B8485235 : Blo 1676038 8485235 := bstep (se 1 (by rfl) ⟨6363926, by rfl⟩ : syracuseStep 8485235 = 12727853) B12727853
theorem B1677703 : Blo 1676038 1677703 := bstep (se 1 (by rfl) ⟨1258277, by rfl⟩ : syracuseStep 1677703 = 2516555) B2516555
theorem B1677711 : Blo 1676038 1677711 := bstep (se 1 (by rfl) ⟨1258283, by rfl⟩ : syracuseStep 1677711 = 2516567) B2516567
theorem B9066937 : Blo 1676038 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B8493497 : Blo 1676038 8493497 := bstep (se 2 (by rfl) ⟨3185061, by rfl⟩ : syracuseStep 8493497 = 6370123) B6370123
theorem B3774905 : Blo 1676038 3774905 := bstep (se 2 (by rfl) ⟨1415589, by rfl⟩ : syracuseStep 3774905 = 2831179) B2831179
theorem B1677755 : Blo 1676038 1677755 := bstep (se 1 (by rfl) ⟨1258316, by rfl⟩ : syracuseStep 1677755 = 2516633) B2516633
theorem B1677831 : Blo 1676038 1677831 := bstep (se 1 (by rfl) ⟨1258373, by rfl⟩ : syracuseStep 1677831 = 2516747) B2516747
theorem B1677839 : Blo 1676038 1677839 := bstep (se 1 (by rfl) ⟨1258379, by rfl⟩ : syracuseStep 1677839 = 2516759) B2516759
theorem B1677883 : Blo 1676038 1677883 := bstep (se 1 (by rfl) ⟨1258412, by rfl⟩ : syracuseStep 1677883 = 2516825) B2516825
theorem B1677959 : Blo 1676038 1677959 := bstep (se 1 (by rfl) ⟨1258469, by rfl⟩ : syracuseStep 1677959 = 2516939) B2516939
theorem B1677967 : Blo 1676038 1677967 := bstep (se 1 (by rfl) ⟨1258475, by rfl⟩ : syracuseStep 1677967 = 2516951) B2516951
theorem B1678011 : Blo 1676038 1678011 := bstep (se 1 (by rfl) ⟨1258508, by rfl⟩ : syracuseStep 1678011 = 2517017) B2517017
theorem B3775247 : Blo 1676038 3775247 := bstep (se 1 (by rfl) ⟨2831435, by rfl⟩ : syracuseStep 3775247 = 5662871) B5662871
theorem B3775265 : Blo 1676038 3775265 := bstep (se 2 (by rfl) ⟨1415724, by rfl⟩ : syracuseStep 3775265 = 2831449) B2831449
theorem B8485721 : Blo 1676038 8485721 := bstep (se 2 (by rfl) ⟨3182145, by rfl⟩ : syracuseStep 8485721 = 6364291) B6364291
theorem B2014087 : Blo 1676038 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B5659577 : Blo 1676038 5659577 := bstep (se 2 (by rfl) ⟨2122341, by rfl⟩ : syracuseStep 5659577 = 4244683) B4244683
theorem B7167005 : Blo 1676038 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B3398803 : Blo 1676038 3398803 := bstep (se 1 (by rfl) ⟨2549102, by rfl⟩ : syracuseStep 3398803 = 5098205) B5098205
theorem B2514107 : Blo 1676038 2514107 := bstep (se 1 (by rfl) ⟨1885580, by rfl⟩ : syracuseStep 2514107 = 3771161) B3771161
theorem B3226825 : Blo 1676038 3226825 := bstep (se 2 (by rfl) ⟨1210059, by rfl⟩ : syracuseStep 3226825 = 2420119) B2420119
theorem B13081837 : Blo 1676038 13081837 := bstep (se 3 (by rfl) ⟨2452844, by rfl⟩ : syracuseStep 13081837 = 4905689) B4905689
theorem B2514167 : Blo 1676038 2514167 := bstep (se 1 (by rfl) ⟨1885625, by rfl⟩ : syracuseStep 2514167 = 3771251) B3771251
theorem B4242689 : Blo 1676038 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B2014471 : Blo 1676038 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B2514191 : Blo 1676038 2514191 := bstep (se 1 (by rfl) ⟨1885643, by rfl⟩ : syracuseStep 2514191 = 3771287) B3771287
theorem B7257377 : Blo 1676038 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B2514233 : Blo 1676038 2514233 := bstep (se 2 (by rfl) ⟨942837, by rfl⟩ : syracuseStep 2514233 = 1885675) B1885675
theorem B2514311 : Blo 1676038 2514311 := bstep (se 1 (by rfl) ⟨1885733, by rfl⟩ : syracuseStep 2514311 = 3771467) B3771467
theorem B11632019 : Blo 1676038 11632019 := bstep (se 1 (by rfl) ⟨8724014, by rfl⟩ : syracuseStep 11632019 = 17448029) B17448029
theorem B2514347 : Blo 1676038 2514347 := bstep (se 1 (by rfl) ⟨1885760, by rfl⟩ : syracuseStep 2514347 = 3771521) B3771521
theorem B2514377 : Blo 1676038 2514377 := bstep (se 2 (by rfl) ⟨942891, by rfl⟩ : syracuseStep 2514377 = 1885783) B1885783
theorem B2620873 : Blo 1676038 2620873 := bstep (se 2 (by rfl) ⟨982827, by rfl⟩ : syracuseStep 2620873 = 1965655) B1965655
theorem B5660171 : Blo 1676038 5660171 := bstep (se 1 (by rfl) ⟨4245128, by rfl⟩ : syracuseStep 5660171 = 8490257) B8490257
theorem B2514491 : Blo 1676038 2514491 := bstep (se 1 (by rfl) ⟨1885868, by rfl⟩ : syracuseStep 2514491 = 3771737) B3771737
theorem B6045245 : Blo 1676038 6045245 := bstep (se 3 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 6045245 = 2266967) B2266967
theorem B15720013 : Blo 1676038 15720013 := bstep (se 3 (by rfl) ⟨2947502, by rfl⟩ : syracuseStep 15720013 = 5895005) B5895005
theorem B4243063 : Blo 1676038 4243063 := bstep (se 1 (by rfl) ⟨3182297, by rfl⟩ : syracuseStep 4243063 = 6364595) B6364595
theorem B2514551 : Blo 1676038 2514551 := bstep (se 1 (by rfl) ⟨1885913, by rfl⟩ : syracuseStep 2514551 = 3771827) B3771827
theorem B4775543 : Blo 1676038 4775543 := bstep (se 1 (by rfl) ⟨3581657, by rfl⟩ : syracuseStep 4775543 = 7163315) B7163315
theorem B5660279 : Blo 1676038 5660279 := bstep (se 1 (by rfl) ⟨4245209, by rfl⟩ : syracuseStep 5660279 = 8490419) B8490419
theorem B10747511 : Blo 1676038 10747511 := bstep (se 1 (by rfl) ⟨8060633, by rfl⟩ : syracuseStep 10747511 = 16121267) B16121267
theorem B4030087 : Blo 1676038 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B2514575 : Blo 1676038 2514575 := bstep (se 1 (by rfl) ⟨1885931, by rfl⟩ : syracuseStep 2514575 = 3771863) B3771863
theorem B2514617 : Blo 1676038 2514617 := bstep (se 2 (by rfl) ⟨942981, by rfl⟩ : syracuseStep 2514617 = 1885963) B1885963
theorem B8494793 : Blo 1676038 8494793 := bstep (se 2 (by rfl) ⟨3185547, by rfl⟩ : syracuseStep 8494793 = 6371095) B6371095
theorem B7167689 : Blo 1676038 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B2514695 : Blo 1676038 2514695 := bstep (se 1 (by rfl) ⟨1886021, by rfl⟩ : syracuseStep 2514695 = 3772043) B3772043
theorem B2514731 : Blo 1676038 2514731 := bstep (se 1 (by rfl) ⟨1886048, by rfl⟩ : syracuseStep 2514731 = 3772097) B3772097
theorem B2514761 : Blo 1676038 2514761 := bstep (se 2 (by rfl) ⟨943035, by rfl⟩ : syracuseStep 2514761 = 1886071) B1886071
theorem B6365081 : Blo 1676038 6365081 := bstep (se 2 (by rfl) ⟨2386905, by rfl⟩ : syracuseStep 6365081 = 4773811) B4773811
theorem B12083107 : Blo 1676038 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B2121643 : Blo 1676038 2121643 := bstep (se 1 (by rfl) ⟨1591232, by rfl⟩ : syracuseStep 2121643 = 3182465) B3182465
theorem B2514875 : Blo 1676038 2514875 := bstep (se 1 (by rfl) ⟨1886156, by rfl⟩ : syracuseStep 2514875 = 3772313) B3772313
theorem B2514935 : Blo 1676038 2514935 := bstep (se 1 (by rfl) ⟨1886201, by rfl⟩ : syracuseStep 2514935 = 3772403) B3772403
theorem B2514953 : Blo 1676038 2514953 := bstep (se 2 (by rfl) ⟨943107, by rfl⟩ : syracuseStep 2514953 = 1886215) B1886215
theorem B2514983 : Blo 1676038 2514983 := bstep (se 1 (by rfl) ⟨1886237, by rfl⟩ : syracuseStep 2514983 = 3772475) B3772475
theorem B6365263 : Blo 1676038 6365263 := bstep (se 1 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 6365263 = 9547895) B9547895
theorem B11468881 : Blo 1676038 11468881 := bstep (se 2 (by rfl) ⟨4300830, by rfl⟩ : syracuseStep 11468881 = 8601661) B8601661
theorem B2515067 : Blo 1676038 2515067 := bstep (se 1 (by rfl) ⟨1886300, by rfl⟩ : syracuseStep 2515067 = 3772601) B3772601
theorem B2515193 : Blo 1676038 2515193 := bstep (se 2 (by rfl) ⟨943197, by rfl⟩ : syracuseStep 2515193 = 1886395) B1886395
theorem B8487179 : Blo 1676038 8487179 := bstep (se 1 (by rfl) ⟨6365384, by rfl⟩ : syracuseStep 8487179 = 12730769) B12730769
theorem B2515295 : Blo 1676038 2515295 := bstep (se 1 (by rfl) ⟨1886471, by rfl⟩ : syracuseStep 2515295 = 3772943) B3772943
theorem B2515307 : Blo 1676038 2515307 := bstep (se 1 (by rfl) ⟨1886480, by rfl⟩ : syracuseStep 2515307 = 3772961) B3772961
theorem B4776317 : Blo 1676038 4776317 := bstep (se 3 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 4776317 = 1791119) B1791119
theorem B72507797 : Blo 1676038 72507797 := bstep (se 6 (by rfl) ⟨1699401, by rfl⟩ : syracuseStep 72507797 = 3398803) B3398803
theorem B3228179 : Blo 1676038 3228179 := bstep (se 1 (by rfl) ⟨2421134, by rfl⟩ : syracuseStep 3228179 = 4842269) B4842269
theorem B6365735 : Blo 1676038 6365735 := bstep (se 1 (by rfl) ⟨4774301, by rfl⟩ : syracuseStep 6365735 = 9548603) B9548603
theorem B2515535 : Blo 1676038 2515535 := bstep (se 1 (by rfl) ⟨1886651, by rfl⟩ : syracuseStep 2515535 = 3773303) B3773303
theorem B4776545 : Blo 1676038 4776545 := bstep (se 2 (by rfl) ⟨1791204, by rfl⟩ : syracuseStep 4776545 = 3582409) B3582409
theorem B3580615 : Blo 1676038 3580615 := bstep (se 1 (by rfl) ⟨2685461, by rfl⟩ : syracuseStep 3580615 = 5370923) B5370923
theorem B2515655 : Blo 1676038 2515655 := bstep (se 1 (by rfl) ⟨1886741, by rfl⟩ : syracuseStep 2515655 = 3773483) B3773483
theorem B12092105 : Blo 1676038 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B2515817 : Blo 1676038 2515817 := bstep (se 2 (by rfl) ⟨943431, by rfl⟩ : syracuseStep 2515817 = 1886863) B1886863
theorem B7160683 : Blo 1676038 7160683 := bstep (se 1 (by rfl) ⟨5370512, by rfl⟩ : syracuseStep 7160683 = 10741025) B10741025
theorem B2515895 : Blo 1676038 2515895 := bstep (se 1 (by rfl) ⟨1886921, by rfl⟩ : syracuseStep 2515895 = 3773843) B3773843
theorem B4776887 : Blo 1676038 4776887 := bstep (se 1 (by rfl) ⟨3582665, by rfl⟩ : syracuseStep 4776887 = 7165331) B7165331
theorem B2515931 : Blo 1676038 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B12248113 : Blo 1676038 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B12740003 : Blo 1676038 12740003 := bstep (se 1 (by rfl) ⟨9555002, by rfl⟩ : syracuseStep 12740003 = 19110005) B19110005
theorem B2516399 : Blo 1676038 2516399 := bstep (se 1 (by rfl) ⟨1887299, by rfl⟩ : syracuseStep 2516399 = 3774599) B3774599
theorem B6366707 : Blo 1676038 6366707 := bstep (se 1 (by rfl) ⟨4775030, by rfl⟩ : syracuseStep 6366707 = 9550061) B9550061
theorem B11478515 : Blo 1676038 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B24839669 : Blo 1676038 24839669 := bstep (se 5 (by rfl) ⟨1164359, by rfl⟩ : syracuseStep 24839669 = 2328719) B2328719
theorem B2516489 : Blo 1676038 2516489 := bstep (se 2 (by rfl) ⟨943683, by rfl⟩ : syracuseStep 2516489 = 1887367) B1887367
theorem B2516519 : Blo 1676038 2516519 := bstep (se 1 (by rfl) ⟨1887389, by rfl⟩ : syracuseStep 2516519 = 3774779) B3774779
theorem B4302433 : Blo 1676038 4302433 := bstep (se 2 (by rfl) ⟨1613412, by rfl⟩ : syracuseStep 4302433 = 3226825) B3226825
theorem B1885819 : Blo 1676038 1885819 := bstep (se 1 (by rfl) ⟨1414364, by rfl⟩ : syracuseStep 1885819 = 2828729) B2828729
theorem B5662331 : Blo 1676038 5662331 := bstep (se 1 (by rfl) ⟨4246748, by rfl⟩ : syracuseStep 5662331 = 8493497) B8493497
theorem B2516603 : Blo 1676038 2516603 := bstep (se 1 (by rfl) ⟨1887452, by rfl⟩ : syracuseStep 2516603 = 3774905) B3774905
theorem B17442449 : Blo 1676038 17442449 := bstep (se 2 (by rfl) ⟨6540918, by rfl⟩ : syracuseStep 17442449 = 13081837) B13081837
theorem B8488637 : Blo 1676038 8488637 := bstep (se 3 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 8488637 = 3183239) B3183239
theorem B2516729 : Blo 1676038 2516729 := bstep (se 2 (by rfl) ⟨943773, by rfl⟩ : syracuseStep 2516729 = 1887547) B1887547
theorem B5662493 : Blo 1676038 5662493 := bstep (se 3 (by rfl) ⟨1061717, by rfl⟩ : syracuseStep 5662493 = 2123435) B2123435
theorem B12732227 : Blo 1676038 12732227 := bstep (se 1 (by rfl) ⟨9549170, by rfl⟩ : syracuseStep 12732227 = 19098341) B19098341
theorem B8488799 : Blo 1676038 8488799 := bstep (se 1 (by rfl) ⟨6366599, by rfl⟩ : syracuseStep 8488799 = 12733199) B12733199
theorem B19105631 : Blo 1676038 19105631 := bstep (se 1 (by rfl) ⟨14329223, by rfl⟩ : syracuseStep 19105631 = 28658447) B28658447
theorem B2516831 : Blo 1676038 2516831 := bstep (se 1 (by rfl) ⟨1887623, by rfl⟩ : syracuseStep 2516831 = 3775247) B3775247
theorem B2516843 : Blo 1676038 2516843 := bstep (se 1 (by rfl) ⟨1887632, by rfl⟩ : syracuseStep 2516843 = 3775265) B3775265
theorem B14321569 : Blo 1676038 14321569 := bstep (se 2 (by rfl) ⟨5370588, by rfl⟩ : syracuseStep 14321569 = 10741177) B10741177
theorem B4778003 : Blo 1676038 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B1886287 : Blo 1676038 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B2828459 : Blo 1676038 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B12093745 : Blo 1676038 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B32229683 : Blo 1676038 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B4778345 : Blo 1676038 4778345 := bstep (se 2 (by rfl) ⟨1791879, by rfl⟩ : syracuseStep 4778345 = 3583759) B3583759
theorem B1886683 : Blo 1676038 1886683 := bstep (se 1 (by rfl) ⟨1415012, by rfl⟩ : syracuseStep 1886683 = 2830025) B2830025
theorem B4245979 : Blo 1676038 4245979 := bstep (se 1 (by rfl) ⟨3184484, by rfl⟩ : syracuseStep 4245979 = 6368969) B6368969
theorem B5663195 : Blo 1676038 5663195 := bstep (se 1 (by rfl) ⟨4247396, by rfl⟩ : syracuseStep 5663195 = 8494793) B8494793
theorem B4778459 : Blo 1676038 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B2828857 : Blo 1676038 2828857 := bstep (se 2 (by rfl) ⟨1060821, by rfl⟩ : syracuseStep 2828857 = 2121643) B2121643
theorem B2869931 : Blo 1676038 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B2828999 : Blo 1676038 2828999 := bstep (se 1 (by rfl) ⟨2121749, by rfl⟩ : syracuseStep 2828999 = 4243499) B4243499
theorem B2829161 : Blo 1676038 2829161 := bstep (se 2 (by rfl) ⟨1060935, by rfl⟩ : syracuseStep 2829161 = 2121871) B2121871
theorem B1887151 : Blo 1676038 1887151 := bstep (se 1 (by rfl) ⟨1415363, by rfl⟩ : syracuseStep 1887151 = 2830727) B2830727
theorem B13593527 : Blo 1676038 13593527 := bstep (se 1 (by rfl) ⟨10195145, by rfl⟩ : syracuseStep 13593527 = 20390291) B20390291
theorem B3771323 : Blo 1676038 3771323 := bstep (se 1 (by rfl) ⟨2828492, by rfl⟩ : syracuseStep 3771323 = 5656985) B5656985
theorem B4303891 : Blo 1676038 4303891 := bstep (se 1 (by rfl) ⟨3227918, by rfl⟩ : syracuseStep 4303891 = 6455837) B6455837
theorem B3771449 : Blo 1676038 3771449 := bstep (se 2 (by rfl) ⟨1414293, by rfl⟩ : syracuseStep 3771449 = 2828587) B2828587
theorem B4246607 : Blo 1676038 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B2829559 : Blo 1676038 2829559 := bstep (se 1 (by rfl) ⟨2122169, by rfl⟩ : syracuseStep 2829559 = 4244339) B4244339
theorem B1887583 : Blo 1676038 1887583 := bstep (se 1 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 1887583 = 2831375) B2831375
theorem B3771791 : Blo 1676038 3771791 := bstep (se 1 (by rfl) ⟨2828843, by rfl⟩ : syracuseStep 3771791 = 5657687) B5657687
theorem B19353005 : Blo 1676038 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B2829755 : Blo 1676038 2829755 := bstep (se 1 (by rfl) ⟨2122316, by rfl⟩ : syracuseStep 2829755 = 4244633) B4244633
theorem B27250141 : Blo 1676038 27250141 := bstep (se 3 (by rfl) ⟨5109401, by rfl⟩ : syracuseStep 27250141 = 10218803) B10218803
theorem B2829863 : Blo 1676038 2829863 := bstep (se 1 (by rfl) ⟨2122397, by rfl⟩ : syracuseStep 2829863 = 4244795) B4244795
theorem B3772115 : Blo 1676038 3772115 := bstep (se 1 (by rfl) ⟨2829086, by rfl⟩ : syracuseStep 3772115 = 5658173) B5658173
theorem B4247255 : Blo 1676038 4247255 := bstep (se 1 (by rfl) ⟨3185441, by rfl⟩ : syracuseStep 4247255 = 6370883) B6370883
theorem B31018717 : Blo 1676038 31018717 := bstep (se 3 (by rfl) ⟨5816009, by rfl⟩ : syracuseStep 31018717 = 11632019) B11632019
theorem B12742433 : Blo 1676038 12742433 := bstep (se 2 (by rfl) ⟨4778412, by rfl⟩ : syracuseStep 12742433 = 9556825) B9556825
theorem B2830153 : Blo 1676038 2830153 := bstep (se 2 (by rfl) ⟨1061307, by rfl⟩ : syracuseStep 2830153 = 2122615) B2122615
theorem B2830187 : Blo 1676038 2830187 := bstep (se 1 (by rfl) ⟨2122640, by rfl⟩ : syracuseStep 2830187 = 4245281) B4245281
theorem B9318253 : Blo 1676038 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B8056847 : Blo 1676038 8056847 := bstep (se 1 (by rfl) ⟨6042635, by rfl⟩ : syracuseStep 8056847 = 12085271) B12085271
theorem B21491891 : Blo 1676038 21491891 := bstep (se 1 (by rfl) ⟨16118918, by rfl⟩ : syracuseStep 21491891 = 32237837) B32237837
theorem B5656823 : Blo 1676038 5656823 := bstep (se 1 (by rfl) ⟨4242617, by rfl⟩ : syracuseStep 5656823 = 8485235) B8485235
theorem B2830585 : Blo 1676038 2830585 := bstep (se 2 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 2830585 = 2122939) B2122939
theorem B6369623 : Blo 1676038 6369623 := bstep (se 1 (by rfl) ⟨4777217, by rfl⟩ : syracuseStep 6369623 = 9554435) B9554435
theorem B2830855 : Blo 1676038 2830855 := bstep (se 1 (by rfl) ⟨2123141, by rfl⟩ : syracuseStep 2830855 = 4246283) B4246283
theorem B8491553 : Blo 1676038 8491553 := bstep (se 2 (by rfl) ⟨3184332, by rfl⟩ : syracuseStep 8491553 = 6368665) B6368665
theorem B5657147 : Blo 1676038 5657147 := bstep (se 1 (by rfl) ⟨4242860, by rfl⟩ : syracuseStep 5657147 = 8485721) B8485721
theorem B3494497 : Blo 1676038 3494497 := bstep (se 2 (by rfl) ⟨1310436, by rfl⟩ : syracuseStep 3494497 = 2620873) B2620873
theorem B3773051 : Blo 1676038 3773051 := bstep (se 1 (by rfl) ⟨2829788, by rfl⟩ : syracuseStep 3773051 = 5659577) B5659577
theorem B4534973 : Blo 1676038 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B3773177 : Blo 1676038 3773177 := bstep (se 2 (by rfl) ⟨1414941, by rfl⟩ : syracuseStep 3773177 = 2829883) B2829883
theorem B20960017 : Blo 1676038 20960017 := bstep (se 2 (by rfl) ⟨7860006, by rfl⟩ : syracuseStep 20960017 = 15720013) B15720013
theorem B1676071 : Blo 1676038 1676071 := bstep (se 1 (by rfl) ⟨1257053, by rfl⟩ : syracuseStep 1676071 = 2514107) B2514107
theorem B5657417 : Blo 1676038 5657417 := bstep (se 2 (by rfl) ⟨2121531, by rfl⟩ : syracuseStep 5657417 = 4243063) B4243063
theorem B1676111 : Blo 1676038 1676111 := bstep (se 1 (by rfl) ⟨1257083, by rfl⟩ : syracuseStep 1676111 = 2514167) B2514167
theorem B1676127 : Blo 1676038 1676127 := bstep (se 1 (by rfl) ⟨1257095, by rfl⟩ : syracuseStep 1676127 = 2514191) B2514191
theorem B1676155 : Blo 1676038 1676155 := bstep (se 1 (by rfl) ⟨1257116, by rfl⟩ : syracuseStep 1676155 = 2514233) B2514233
theorem B1676207 : Blo 1676038 1676207 := bstep (se 1 (by rfl) ⟨1257155, by rfl⟩ : syracuseStep 1676207 = 2514311) B2514311
theorem B2831287 : Blo 1676038 2831287 := bstep (se 1 (by rfl) ⟨2123465, by rfl⟩ : syracuseStep 2831287 = 4246931) B4246931
theorem B1676231 : Blo 1676038 1676231 := bstep (se 1 (by rfl) ⟨1257173, by rfl⟩ : syracuseStep 1676231 = 2514347) B2514347
theorem B1676251 : Blo 1676038 1676251 := bstep (se 1 (by rfl) ⟨1257188, by rfl⟩ : syracuseStep 1676251 = 2514377) B2514377
theorem B3773447 : Blo 1676038 3773447 := bstep (se 1 (by rfl) ⟨2830085, by rfl⟩ : syracuseStep 3773447 = 5660171) B5660171
theorem B1676327 : Blo 1676038 1676327 := bstep (se 1 (by rfl) ⟨1257245, by rfl⟩ : syracuseStep 1676327 = 2514491) B2514491
theorem B1676367 : Blo 1676038 1676367 := bstep (se 1 (by rfl) ⟨1257275, by rfl⟩ : syracuseStep 1676367 = 2514551) B2514551
theorem B3183695 : Blo 1676038 3183695 := bstep (se 1 (by rfl) ⟨2387771, by rfl⟩ : syracuseStep 3183695 = 4775543) B4775543
theorem B3773519 : Blo 1676038 3773519 := bstep (se 1 (by rfl) ⟨2830139, by rfl⟩ : syracuseStep 3773519 = 5660279) B5660279
theorem B7165007 : Blo 1676038 7165007 := bstep (se 1 (by rfl) ⟨5373755, by rfl⟩ : syracuseStep 7165007 = 10747511) B10747511
theorem B1676383 : Blo 1676038 1676383 := bstep (se 1 (by rfl) ⟨1257287, by rfl⟩ : syracuseStep 1676383 = 2514575) B2514575
theorem B1676411 : Blo 1676038 1676411 := bstep (se 1 (by rfl) ⟨1257308, by rfl⟩ : syracuseStep 1676411 = 2514617) B2514617
theorem B2831483 : Blo 1676038 2831483 := bstep (se 1 (by rfl) ⟨2123612, by rfl⟩ : syracuseStep 2831483 = 4247225) B4247225
theorem B1676463 : Blo 1676038 1676463 := bstep (se 1 (by rfl) ⟨1257347, by rfl⟩ : syracuseStep 1676463 = 2514695) B2514695
theorem B1676487 : Blo 1676038 1676487 := bstep (se 1 (by rfl) ⟨1257365, by rfl⟩ : syracuseStep 1676487 = 2514731) B2514731
theorem B16110809 : Blo 1676038 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B1676507 : Blo 1676038 1676507 := bstep (se 1 (by rfl) ⟨1257380, by rfl⟩ : syracuseStep 1676507 = 2514761) B2514761
theorem B1676583 : Blo 1676038 1676583 := bstep (se 1 (by rfl) ⟨1257437, by rfl⟩ : syracuseStep 1676583 = 2514875) B2514875
theorem B1676623 : Blo 1676038 1676623 := bstep (se 1 (by rfl) ⟨1257467, by rfl⟩ : syracuseStep 1676623 = 2514935) B2514935
theorem B1676639 : Blo 1676038 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B1676667 : Blo 1676038 1676667 := bstep (se 1 (by rfl) ⟨1257500, by rfl⟩ : syracuseStep 1676667 = 2515001) B2515001
theorem B1676719 : Blo 1676038 1676719 := bstep (se 1 (by rfl) ⟨1257539, by rfl⟩ : syracuseStep 1676719 = 2515079) B2515079
theorem B1676743 : Blo 1676038 1676743 := bstep (se 1 (by rfl) ⟨1257557, by rfl⟩ : syracuseStep 1676743 = 2515115) B2515115
theorem B1676763 : Blo 1676038 1676763 := bstep (se 1 (by rfl) ⟨1257572, by rfl⟩ : syracuseStep 1676763 = 2515145) B2515145
theorem B3773915 : Blo 1676038 3773915 := bstep (se 1 (by rfl) ⟨2830436, by rfl⟩ : syracuseStep 3773915 = 5660873) B5660873
theorem B4773401 : Blo 1676038 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B1676839 : Blo 1676038 1676839 := bstep (se 1 (by rfl) ⟨1257629, by rfl⟩ : syracuseStep 1676839 = 2515259) B2515259
theorem B1676879 : Blo 1676038 1676879 := bstep (se 1 (by rfl) ⟨1257659, by rfl⟩ : syracuseStep 1676879 = 2515319) B2515319
theorem B1676895 : Blo 1676038 1676895 := bstep (se 1 (by rfl) ⟨1257671, by rfl⟩ : syracuseStep 1676895 = 2515343) B2515343
theorem B6370913 : Blo 1676038 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B1676923 : Blo 1676038 1676923 := bstep (se 1 (by rfl) ⟨1257692, by rfl⟩ : syracuseStep 1676923 = 2515385) B2515385
theorem B1676975 : Blo 1676038 1676975 := bstep (se 1 (by rfl) ⟨1257731, by rfl⟩ : syracuseStep 1676975 = 2515463) B2515463
theorem B1676999 : Blo 1676038 1676999 := bstep (se 1 (by rfl) ⟨1257749, by rfl⟩ : syracuseStep 1676999 = 2515499) B2515499
theorem B6797009 : Blo 1676038 6797009 := bstep (se 2 (by rfl) ⟨2548878, by rfl⟩ : syracuseStep 6797009 = 5097757) B5097757
theorem B1677019 : Blo 1676038 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B1677095 : Blo 1676038 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B1677135 : Blo 1676038 1677135 := bstep (se 1 (by rfl) ⟨1257851, by rfl⟩ : syracuseStep 1677135 = 2515703) B2515703
theorem B1677151 : Blo 1676038 1677151 := bstep (se 1 (by rfl) ⟨1257863, by rfl⟩ : syracuseStep 1677151 = 2515727) B2515727
theorem B1677179 : Blo 1676038 1677179 := bstep (se 1 (by rfl) ⟨1257884, by rfl⟩ : syracuseStep 1677179 = 2515769) B2515769
theorem B12089249 : Blo 1676038 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1677231 : Blo 1676038 1677231 := bstep (se 1 (by rfl) ⟨1257923, by rfl⟩ : syracuseStep 1677231 = 2515847) B2515847
theorem B3774383 : Blo 1676038 3774383 := bstep (se 1 (by rfl) ⟨2830787, by rfl⟩ : syracuseStep 3774383 = 5661575) B5661575
theorem B5658551 : Blo 1676038 5658551 := bstep (se 1 (by rfl) ⟨4243913, by rfl⟩ : syracuseStep 5658551 = 8487827) B8487827
theorem B1677255 : Blo 1676038 1677255 := bstep (se 1 (by rfl) ⟨1257941, by rfl⟩ : syracuseStep 1677255 = 2515883) B2515883
theorem B28645325 : Blo 1676038 28645325 := bstep (se 3 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 28645325 = 10741997) B10741997
theorem B20682701 : Blo 1676038 20682701 := bstep (se 3 (by rfl) ⟨3878006, by rfl⟩ : syracuseStep 20682701 = 7756013) B7756013
theorem B1677275 : Blo 1676038 1677275 := bstep (se 1 (by rfl) ⟨1257956, by rfl⟩ : syracuseStep 1677275 = 2515913) B2515913
theorem B15292423 : Blo 1676038 15292423 := bstep (se 1 (by rfl) ⟨11469317, by rfl⟩ : syracuseStep 15292423 = 22938635) B22938635
theorem B9680933 : Blo 1676038 9680933 := bstep (se 4 (by rfl) ⟨907587, by rfl⟩ : syracuseStep 9680933 = 1815175) B1815175
theorem B1677351 : Blo 1676038 1677351 := bstep (se 1 (by rfl) ⟨1258013, by rfl⟩ : syracuseStep 1677351 = 2516027) B2516027
theorem B3184697 : Blo 1676038 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B1677391 : Blo 1676038 1677391 := bstep (se 1 (by rfl) ⟨1258043, by rfl⟩ : syracuseStep 1677391 = 2516087) B2516087
theorem B12736601 : Blo 1676038 12736601 := bstep (se 2 (by rfl) ⟨4776225, by rfl⟩ : syracuseStep 12736601 = 9552451) B9552451
theorem B1677407 : Blo 1676038 1677407 := bstep (se 1 (by rfl) ⟨1258055, by rfl⟩ : syracuseStep 1677407 = 2516111) B2516111
theorem B1677435 : Blo 1676038 1677435 := bstep (se 1 (by rfl) ⟨1258076, by rfl⟩ : syracuseStep 1677435 = 2516153) B2516153
theorem B3774635 : Blo 1676038 3774635 := bstep (se 1 (by rfl) ⟨2830976, by rfl⟩ : syracuseStep 3774635 = 5661953) B5661953
theorem B1677487 : Blo 1676038 1677487 := bstep (se 1 (by rfl) ⟨1258115, by rfl⟩ : syracuseStep 1677487 = 2516231) B2516231
theorem B1677511 : Blo 1676038 1677511 := bstep (se 1 (by rfl) ⟨1258133, by rfl⟩ : syracuseStep 1677511 = 2516267) B2516267
theorem B1677531 : Blo 1676038 1677531 := bstep (se 1 (by rfl) ⟨1258148, by rfl⟩ : syracuseStep 1677531 = 2516297) B2516297
theorem B1677607 : Blo 1676038 1677607 := bstep (se 1 (by rfl) ⟨1258205, by rfl⟩ : syracuseStep 1677607 = 2516411) B2516411
theorem B1677647 : Blo 1676038 1677647 := bstep (se 1 (by rfl) ⟨1258235, by rfl⟩ : syracuseStep 1677647 = 2516471) B2516471
theorem B1677663 : Blo 1676038 1677663 := bstep (se 1 (by rfl) ⟨1258247, by rfl⟩ : syracuseStep 1677663 = 2516495) B2516495
theorem B1677691 : Blo 1676038 1677691 := bstep (se 1 (by rfl) ⟨1258268, by rfl⟩ : syracuseStep 1677691 = 2516537) B2516537
theorem B2685359 : Blo 1676038 2685359 := bstep (se 1 (by rfl) ⟨2014019, by rfl⟩ : syracuseStep 2685359 = 4028039) B4028039
theorem B1677743 : Blo 1676038 1677743 := bstep (se 1 (by rfl) ⟨1258307, by rfl⟩ : syracuseStep 1677743 = 2516615) B2516615
theorem B1677767 : Blo 1676038 1677767 := bstep (se 1 (by rfl) ⟨1258325, by rfl⟩ : syracuseStep 1677767 = 2516651) B2516651
theorem B3021275 : Blo 1676038 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B1677787 : Blo 1676038 1677787 := bstep (se 1 (by rfl) ⟨1258340, by rfl⟩ : syracuseStep 1677787 = 2516681) B2516681
theorem B17201645 : Blo 1676038 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B2685449 : Blo 1676038 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B5659145 : Blo 1676038 5659145 := bstep (se 2 (by rfl) ⟨2122179, by rfl⟩ : syracuseStep 5659145 = 4244359) B4244359
theorem B11631127 : Blo 1676038 11631127 := bstep (se 1 (by rfl) ⟨8723345, by rfl⟩ : syracuseStep 11631127 = 17446691) B17446691
theorem B3824167 : Blo 1676038 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B1677863 : Blo 1676038 1677863 := bstep (se 1 (by rfl) ⟨1258397, by rfl⟩ : syracuseStep 1677863 = 2516795) B2516795
theorem B8608315 : Blo 1676038 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B1677903 : Blo 1676038 1677903 := bstep (se 1 (by rfl) ⟨1258427, by rfl⟩ : syracuseStep 1677903 = 2516855) B2516855
theorem B1677919 : Blo 1676038 1677919 := bstep (se 1 (by rfl) ⟨1258439, by rfl⟩ : syracuseStep 1677919 = 2516879) B2516879
theorem B1677947 : Blo 1676038 1677947 := bstep (se 1 (by rfl) ⟨1258460, by rfl⟩ : syracuseStep 1677947 = 2516921) B2516921
theorem B5372563 : Blo 1676038 5372563 := bstep (se 1 (by rfl) ⟨4029422, by rfl⟩ : syracuseStep 5372563 = 8058845) B8058845
theorem B1677999 : Blo 1676038 1677999 := bstep (se 1 (by rfl) ⟨1258499, by rfl⟩ : syracuseStep 1677999 = 2516999) B2516999
theorem B3775175 : Blo 1676038 3775175 := bstep (se 1 (by rfl) ⟨2831381, by rfl⟩ : syracuseStep 3775175 = 5662763) B5662763
theorem B1678023 : Blo 1676038 1678023 := bstep (se 1 (by rfl) ⟨1258517, by rfl⟩ : syracuseStep 1678023 = 2517035) B2517035
theorem B6364079 : Blo 1676038 6364079 := bstep (se 1 (by rfl) ⟨4773059, by rfl⟩ : syracuseStep 6364079 = 9546119) B9546119
theorem B2685961 : Blo 1676038 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B3021995 : Blo 1676038 3021995 := bstep (se 1 (by rfl) ⟨2266496, by rfl⟩ : syracuseStep 3021995 = 4532993) B4532993
theorem B2514119 : Blo 1676038 2514119 := bstep (se 1 (by rfl) ⟨1885589, by rfl⟩ : syracuseStep 2514119 = 3771179) B3771179
theorem B45923597 : Blo 1676038 45923597 := bstep (se 3 (by rfl) ⟨8610674, by rfl⟩ : syracuseStep 45923597 = 17221349) B17221349
theorem B25828631 : Blo 1676038 25828631 := bstep (se 1 (by rfl) ⟨19371473, by rfl⟩ : syracuseStep 25828631 = 38742947) B38742947
theorem B2514281 : Blo 1676038 2514281 := bstep (se 2 (by rfl) ⟨942855, by rfl⟩ : syracuseStep 2514281 = 1885711) B1885711
theorem B5660009 : Blo 1676038 5660009 := bstep (se 2 (by rfl) ⟨2122503, by rfl⟩ : syracuseStep 5660009 = 4245007) B4245007
theorem B19365293 : Blo 1676038 19365293 := bstep (se 3 (by rfl) ⟨3630992, by rfl⟩ : syracuseStep 19365293 = 7261985) B7261985
theorem B2514359 : Blo 1676038 2514359 := bstep (se 1 (by rfl) ⟨1885769, by rfl⟩ : syracuseStep 2514359 = 3771539) B3771539
theorem B2514395 : Blo 1676038 2514395 := bstep (se 1 (by rfl) ⟨1885796, by rfl⟩ : syracuseStep 2514395 = 3771593) B3771593
theorem B5373449 : Blo 1676038 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B12738059 : Blo 1676038 12738059 := bstep (se 1 (by rfl) ⟨9553544, by rfl⟩ : syracuseStep 12738059 = 19107089) B19107089
theorem B19111463 : Blo 1676038 19111463 := bstep (se 1 (by rfl) ⟨14333597, by rfl⟩ : syracuseStep 19111463 = 28667195) B28667195
theorem B8494631 : Blo 1676038 8494631 := bstep (se 1 (by rfl) ⟨6370973, by rfl⟩ : syracuseStep 8494631 = 12741947) B12741947
theorem B4030163 : Blo 1676038 4030163 := bstep (se 1 (by rfl) ⟨3022622, by rfl⟩ : syracuseStep 4030163 = 6045245) B6045245
theorem B3579641 : Blo 1676038 3579641 := bstep (se 2 (by rfl) ⟨1342365, by rfl⟩ : syracuseStep 3579641 = 2684731) B2684731
theorem B6799133 : Blo 1676038 6799133 := bstep (se 3 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 6799133 = 2549675) B2549675
theorem B2867017 : Blo 1676038 2867017 := bstep (se 2 (by rfl) ⟨1075131, by rfl⟩ : syracuseStep 2867017 = 2150263) B2150263
theorem B3022687 : Blo 1676038 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B2514863 : Blo 1676038 2514863 := bstep (se 1 (by rfl) ⟨1886147, by rfl⟩ : syracuseStep 2514863 = 3772295) B3772295
theorem B4243387 : Blo 1676038 4243387 := bstep (se 1 (by rfl) ⟨3182540, by rfl⟩ : syracuseStep 4243387 = 6365081) B6365081
theorem B5660603 : Blo 1676038 5660603 := bstep (se 1 (by rfl) ⟨4245452, by rfl⟩ : syracuseStep 5660603 = 8490905) B8490905
theorem B20389897 : Blo 1676038 20389897 := bstep (se 2 (by rfl) ⟨7646211, by rfl⟩ : syracuseStep 20389897 = 15292423) B15292423
theorem B8487017 : Blo 1676038 8487017 := bstep (se 2 (by rfl) ⟨3182631, by rfl⟩ : syracuseStep 8487017 = 6365263) B6365263
theorem B2515049 : Blo 1676038 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B14327927 : Blo 1676038 14327927 := bstep (se 1 (by rfl) ⟨10745945, by rfl⟩ : syracuseStep 14327927 = 21491891) B21491891
theorem B5661035 : Blo 1676038 5661035 := bstep (se 1 (by rfl) ⟨4245776, by rfl⟩ : syracuseStep 5661035 = 8491553) B8491553
theorem B4243823 : Blo 1676038 4243823 := bstep (se 1 (by rfl) ⟨3182867, by rfl⟩ : syracuseStep 4243823 = 6365735) B6365735
theorem B2515367 : Blo 1676038 2515367 := bstep (se 1 (by rfl) ⟨1886525, by rfl⟩ : syracuseStep 2515367 = 3773051) B3773051
theorem B3023315 : Blo 1676038 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B8061403 : Blo 1676038 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B2515451 : Blo 1676038 2515451 := bstep (se 1 (by rfl) ⟨1886588, by rfl⟩ : syracuseStep 2515451 = 3773177) B3773177
theorem B2515577 : Blo 1676038 2515577 := bstep (se 2 (by rfl) ⟨943341, by rfl⟩ : syracuseStep 2515577 = 1886683) B1886683
theorem B5661305 : Blo 1676038 5661305 := bstep (se 2 (by rfl) ⟨2122989, by rfl⟩ : syracuseStep 5661305 = 4245979) B4245979
theorem B2515631 : Blo 1676038 2515631 := bstep (se 1 (by rfl) ⟨1886723, by rfl⟩ : syracuseStep 2515631 = 3773447) B3773447
theorem B15508169 : Blo 1676038 15508169 := bstep (se 2 (by rfl) ⟨5815563, by rfl⟩ : syracuseStep 15508169 = 11631127) B11631127
theorem B2122463 : Blo 1676038 2122463 := bstep (se 1 (by rfl) ⟨1591847, by rfl⟩ : syracuseStep 2122463 = 3183695) B3183695
theorem B2515679 : Blo 1676038 2515679 := bstep (se 1 (by rfl) ⟨1886759, by rfl⟩ : syracuseStep 2515679 = 3773519) B3773519
theorem B4776671 : Blo 1676038 4776671 := bstep (se 1 (by rfl) ⟨3582503, by rfl⟩ : syracuseStep 4776671 = 7165007) B7165007
theorem B11477753 : Blo 1676038 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B10740539 : Blo 1676038 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B2515943 : Blo 1676038 2515943 := bstep (se 1 (by rfl) ⟨1886957, by rfl⟩ : syracuseStep 2515943 = 3773915) B3773915
theorem B4244471 : Blo 1676038 4244471 := bstep (se 1 (by rfl) ⟨3183353, by rfl⟩ : syracuseStep 4244471 = 6366707) B6366707
theorem B7160957 : Blo 1676038 7160957 := bstep (se 3 (by rfl) ⟨1342679, by rfl⟩ : syracuseStep 7160957 = 2685359) B2685359
theorem B4531339 : Blo 1676038 4531339 := bstep (se 1 (by rfl) ⟨3398504, by rfl⟩ : syracuseStep 4531339 = 6797009) B6797009
theorem B8488151 : Blo 1676038 8488151 := bstep (se 1 (by rfl) ⟨6366113, by rfl⟩ : syracuseStep 8488151 = 12732227) B12732227
theorem B2516201 : Blo 1676038 2516201 := bstep (se 2 (by rfl) ⟨943575, by rfl⟩ : syracuseStep 2516201 = 1887151) B1887151
theorem B2516255 : Blo 1676038 2516255 := bstep (se 1 (by rfl) ⟨1887191, by rfl⟩ : syracuseStep 2516255 = 3774383) B3774383
theorem B19096883 : Blo 1676038 19096883 := bstep (se 1 (by rfl) ⟨14322662, by rfl⟩ : syracuseStep 19096883 = 28645325) B28645325
theorem B13788467 : Blo 1676038 13788467 := bstep (se 1 (by rfl) ⟨10341350, by rfl⟩ : syracuseStep 13788467 = 20682701) B20682701
theorem B3581281 : Blo 1676038 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B1885639 : Blo 1676038 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B2516423 : Blo 1676038 2516423 := bstep (se 1 (by rfl) ⟨1887317, by rfl⟩ : syracuseStep 2516423 = 3774635) B3774635
theorem B7653149 : Blo 1676038 7653149 := bstep (se 3 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 7653149 = 2869931) B2869931
theorem B2516777 : Blo 1676038 2516777 := bstep (se 2 (by rfl) ⟨943791, by rfl⟩ : syracuseStep 2516777 = 1887583) B1887583
theorem B1885999 : Blo 1676038 1885999 := bstep (se 1 (by rfl) ⟨1414499, by rfl⟩ : syracuseStep 1885999 = 2828999) B2828999
theorem B2516783 : Blo 1676038 2516783 := bstep (se 1 (by rfl) ⟨1887587, by rfl⟩ : syracuseStep 2516783 = 3775175) B3775175
theorem B1886107 : Blo 1676038 1886107 := bstep (se 1 (by rfl) ⟨1414580, by rfl⟩ : syracuseStep 1886107 = 2829161) B2829161
theorem B9062351 : Blo 1676038 9062351 := bstep (se 1 (by rfl) ⟨6796763, by rfl⟩ : syracuseStep 9062351 = 13593527) B13593527
theorem B36333521 : Blo 1676038 36333521 := bstep (se 2 (by rfl) ⟨13625070, by rfl⟩ : syracuseStep 36333521 = 27250141) B27250141
theorem B5736577 : Blo 1676038 5736577 := bstep (se 2 (by rfl) ⟨2151216, by rfl⟩ : syracuseStep 5736577 = 4302433) B4302433
theorem B30615731 : Blo 1676038 30615731 := bstep (se 1 (by rfl) ⟨22961798, by rfl⟩ : syracuseStep 30615731 = 45923597) B45923597
theorem B1886503 : Blo 1676038 1886503 := bstep (se 1 (by rfl) ⟨1414877, by rfl⟩ : syracuseStep 1886503 = 2829755) B2829755
theorem B3582299 : Blo 1676038 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B1886575 : Blo 1676038 1886575 := bstep (se 1 (by rfl) ⟨1414931, by rfl⟩ : syracuseStep 1886575 = 2829863) B2829863
theorem B12740975 : Blo 1676038 12740975 := bstep (se 1 (by rfl) ⟨9555731, by rfl⟩ : syracuseStep 12740975 = 19111463) B19111463
theorem B5663087 : Blo 1676038 5663087 := bstep (se 1 (by rfl) ⟨4247315, by rfl⟩ : syracuseStep 5663087 = 8494631) B8494631
theorem B2386427 : Blo 1676038 2386427 := bstep (se 1 (by rfl) ⟨1789820, by rfl⟩ : syracuseStep 2386427 = 3579641) B3579641
theorem B4532755 : Blo 1676038 4532755 := bstep (se 1 (by rfl) ⟨3399566, by rfl⟩ : syracuseStep 4532755 = 6799133) B6799133
theorem B1886791 : Blo 1676038 1886791 := bstep (se 1 (by rfl) ⟨1415093, by rfl⟩ : syracuseStep 1886791 = 2830187) B2830187
theorem B3771215 : Blo 1676038 3771215 := bstep (se 1 (by rfl) ⟨2828411, by rfl⟩ : syracuseStep 3771215 = 5656823) B5656823
theorem B4246415 : Blo 1676038 4246415 := bstep (se 1 (by rfl) ⟨3184811, by rfl⟩ : syracuseStep 4246415 = 6369623) B6369623
theorem B447147029 : Blo 1676038 447147029 := bstep (se 6 (by rfl) ⟨10480008, by rfl⟩ : syracuseStep 447147029 = 20960017) B20960017
theorem B3771431 : Blo 1676038 3771431 := bstep (se 1 (by rfl) ⟨2828573, by rfl⟩ : syracuseStep 3771431 = 5657147) B5657147
theorem B16124993 : Blo 1676038 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B3771611 : Blo 1676038 3771611 := bstep (se 1 (by rfl) ⟨2828708, by rfl⟩ : syracuseStep 3771611 = 5657417) B5657417
theorem B5098889 : Blo 1676038 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B3771809 : Blo 1676038 3771809 := bstep (se 2 (by rfl) ⟨1414428, by rfl⟩ : syracuseStep 3771809 = 2828857) B2828857
theorem B1887655 : Blo 1676038 1887655 := bstep (se 1 (by rfl) ⟨1415741, by rfl⟩ : syracuseStep 1887655 = 2831483) B2831483
theorem B7163417 : Blo 1676038 7163417 := bstep (se 2 (by rfl) ⟨2686281, by rfl⟩ : syracuseStep 7163417 = 5372563) B5372563
theorem B3182267 : Blo 1676038 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B4247275 : Blo 1676038 4247275 := bstep (se 1 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 4247275 = 6370913) B6370913
theorem B11628299 : Blo 1676038 11628299 := bstep (se 1 (by rfl) ⟨8721224, by rfl⟩ : syracuseStep 11628299 = 17442449) B17442449
theorem B9547577 : Blo 1676038 9547577 := bstep (se 2 (by rfl) ⟨3580341, by rfl⟩ : syracuseStep 9547577 = 7160683) B7160683
theorem B3772367 : Blo 1676038 3772367 := bstep (se 1 (by rfl) ⟨2829275, by rfl⟩ : syracuseStep 3772367 = 5658551) B5658551
theorem B30609373 : Blo 1676038 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B5738521 : Blo 1676038 5738521 := bstep (se 2 (by rfl) ⟨2151945, by rfl⟩ : syracuseStep 5738521 = 4303891) B4303891
theorem B8491067 : Blo 1676038 8491067 := bstep (se 1 (by rfl) ⟨6368300, by rfl⟩ : syracuseStep 8491067 = 12736601) B12736601
theorem B16330817 : Blo 1676038 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B3772745 : Blo 1676038 3772745 := bstep (se 2 (by rfl) ⟨1414779, by rfl⟩ : syracuseStep 3772745 = 2829559) B2829559
theorem B1790299 : Blo 1676038 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B3772763 : Blo 1676038 3772763 := bstep (se 1 (by rfl) ⟨2829572, by rfl⟩ : syracuseStep 3772763 = 5659145) B5659145
theorem B2831071 : Blo 1676038 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B1676079 : Blo 1676038 1676079 := bstep (se 1 (by rfl) ⟨1257059, by rfl⟩ : syracuseStep 1676079 = 2514119) B2514119
theorem B1676187 : Blo 1676038 1676187 := bstep (se 1 (by rfl) ⟨1257140, by rfl⟩ : syracuseStep 1676187 = 2514281) B2514281
theorem B3773339 : Blo 1676038 3773339 := bstep (se 1 (by rfl) ⟨2830004, by rfl⟩ : syracuseStep 3773339 = 5660009) B5660009
theorem B1676239 : Blo 1676038 1676239 := bstep (se 1 (by rfl) ⟨1257179, by rfl⟩ : syracuseStep 1676239 = 2514359) B2514359
theorem B41358289 : Blo 1676038 41358289 := bstep (se 2 (by rfl) ⟨15509358, by rfl⟩ : syracuseStep 41358289 = 31018717) B31018717
theorem B1676263 : Blo 1676038 1676263 := bstep (se 1 (by rfl) ⟨1257197, by rfl⟩ : syracuseStep 1676263 = 2514395) B2514395
theorem B8492039 : Blo 1676038 8492039 := bstep (se 1 (by rfl) ⟨6369029, by rfl⟩ : syracuseStep 8492039 = 12738059) B12738059
theorem B3822689 : Blo 1676038 3822689 := bstep (se 2 (by rfl) ⟨1433508, by rfl⟩ : syracuseStep 3822689 = 2867017) B2867017
theorem B3773537 : Blo 1676038 3773537 := bstep (se 2 (by rfl) ⟨1415076, by rfl⟩ : syracuseStep 3773537 = 2830153) B2830153
theorem B12424337 : Blo 1676038 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B2831503 : Blo 1676038 2831503 := bstep (se 1 (by rfl) ⟨2123627, by rfl⟩ : syracuseStep 2831503 = 4247255) B4247255
theorem B5657849 : Blo 1676038 5657849 := bstep (se 2 (by rfl) ⟨2121693, by rfl⟩ : syracuseStep 5657849 = 4243387) B4243387
theorem B1676575 : Blo 1676038 1676575 := bstep (se 1 (by rfl) ⟨1257431, by rfl⟩ : syracuseStep 1676575 = 2514863) B2514863
theorem B3773735 : Blo 1676038 3773735 := bstep (se 1 (by rfl) ⟨2830301, by rfl⟩ : syracuseStep 3773735 = 5660603) B5660603
theorem B1676635 : Blo 1676038 1676635 := bstep (se 1 (by rfl) ⟨1257476, by rfl⟩ : syracuseStep 1676635 = 2514953) B2514953
theorem B5371231 : Blo 1676038 5371231 := bstep (se 1 (by rfl) ⟨4028423, by rfl⟩ : syracuseStep 5371231 = 8056847) B8056847
theorem B1676655 : Blo 1676038 1676655 := bstep (se 1 (by rfl) ⟨1257491, by rfl⟩ : syracuseStep 1676655 = 2514983) B2514983
theorem B1676711 : Blo 1676038 1676711 := bstep (se 1 (by rfl) ⟨1257533, by rfl⟩ : syracuseStep 1676711 = 2515067) B2515067
theorem B15291841 : Blo 1676038 15291841 := bstep (se 2 (by rfl) ⟨5734440, by rfl⟩ : syracuseStep 15291841 = 11468881) B11468881
theorem B8492525 : Blo 1676038 8492525 := bstep (se 3 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 8492525 = 3184697) B3184697
theorem B1676795 : Blo 1676038 1676795 := bstep (se 1 (by rfl) ⟨1257596, by rfl⟩ : syracuseStep 1676795 = 2515193) B2515193
theorem B5658119 : Blo 1676038 5658119 := bstep (se 1 (by rfl) ⟨4243589, by rfl⟩ : syracuseStep 5658119 = 8487179) B8487179
theorem B1676863 : Blo 1676038 1676863 := bstep (se 1 (by rfl) ⟨1257647, by rfl⟩ : syracuseStep 1676863 = 2515295) B2515295
theorem B1676871 : Blo 1676038 1676871 := bstep (se 1 (by rfl) ⟨1257653, by rfl⟩ : syracuseStep 1676871 = 2515307) B2515307
theorem B3184211 : Blo 1676038 3184211 := bstep (se 1 (by rfl) ⟨2388158, by rfl⟩ : syracuseStep 3184211 = 4776317) B4776317
theorem B48338531 : Blo 1676038 48338531 := bstep (se 1 (by rfl) ⟨36253898, by rfl⟩ : syracuseStep 48338531 = 72507797) B72507797
theorem B3774113 : Blo 1676038 3774113 := bstep (se 2 (by rfl) ⟨1415292, by rfl⟩ : syracuseStep 3774113 = 2830585) B2830585
theorem B1677023 : Blo 1676038 1677023 := bstep (se 1 (by rfl) ⟨1257767, by rfl⟩ : syracuseStep 1677023 = 2515535) B2515535
theorem B3184363 : Blo 1676038 3184363 := bstep (se 1 (by rfl) ⟨2388272, by rfl⟩ : syracuseStep 3184363 = 4776545) B4776545
theorem B1677103 : Blo 1676038 1677103 := bstep (se 1 (by rfl) ⟨1257827, by rfl⟩ : syracuseStep 1677103 = 2515655) B2515655
theorem B1677211 : Blo 1676038 1677211 := bstep (se 1 (by rfl) ⟨1257908, by rfl⟩ : syracuseStep 1677211 = 2515817) B2515817
theorem B1677263 : Blo 1676038 1677263 := bstep (se 1 (by rfl) ⟨1257947, by rfl⟩ : syracuseStep 1677263 = 2515895) B2515895
theorem B3184591 : Blo 1676038 3184591 := bstep (se 1 (by rfl) ⟨2388443, by rfl⟩ : syracuseStep 3184591 = 4776887) B4776887
theorem B1677287 : Blo 1676038 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B3774473 : Blo 1676038 3774473 := bstep (se 2 (by rfl) ⟨1415427, by rfl⟩ : syracuseStep 3774473 = 2830855) B2830855
theorem B4659329 : Blo 1676038 4659329 := bstep (se 2 (by rfl) ⟨1747248, by rfl⟩ : syracuseStep 4659329 = 3494497) B3494497
theorem B4774153 : Blo 1676038 4774153 := bstep (se 2 (by rfl) ⟨1790307, by rfl⟩ : syracuseStep 4774153 = 3580615) B3580615
theorem B8493335 : Blo 1676038 8493335 := bstep (se 1 (by rfl) ⟨6370001, by rfl⟩ : syracuseStep 8493335 = 12740003) B12740003
theorem B1677599 : Blo 1676038 1677599 := bstep (se 1 (by rfl) ⟨1258199, by rfl⟩ : syracuseStep 1677599 = 2516399) B2516399
theorem B1677659 : Blo 1676038 1677659 := bstep (se 1 (by rfl) ⟨1258244, by rfl⟩ : syracuseStep 1677659 = 2516489) B2516489
theorem B1677679 : Blo 1676038 1677679 := bstep (se 1 (by rfl) ⟨1258259, by rfl⟩ : syracuseStep 1677679 = 2516519) B2516519
theorem B3774887 : Blo 1676038 3774887 := bstep (se 1 (by rfl) ⟨2831165, by rfl⟩ : syracuseStep 3774887 = 5662331) B5662331
theorem B1677735 : Blo 1676038 1677735 := bstep (se 1 (by rfl) ⟨1258301, by rfl⟩ : syracuseStep 1677735 = 2516603) B2516603
theorem B5659091 : Blo 1676038 5659091 := bstep (se 1 (by rfl) ⟨4244318, by rfl⟩ : syracuseStep 5659091 = 8488637) B8488637
theorem B1677819 : Blo 1676038 1677819 := bstep (se 1 (by rfl) ⟨1258364, by rfl⟩ : syracuseStep 1677819 = 2516729) B2516729
theorem B3774995 : Blo 1676038 3774995 := bstep (se 1 (by rfl) ⟨2831246, by rfl⟩ : syracuseStep 3774995 = 5662493) B5662493
theorem B5659199 : Blo 1676038 5659199 := bstep (se 1 (by rfl) ⟨4244399, by rfl⟩ : syracuseStep 5659199 = 8488799) B8488799
theorem B12737087 : Blo 1676038 12737087 := bstep (se 1 (by rfl) ⟨9552815, by rfl⟩ : syracuseStep 12737087 = 19105631) B19105631
theorem B1677887 : Blo 1676038 1677887 := bstep (se 1 (by rfl) ⟨1258415, by rfl⟩ : syracuseStep 1677887 = 2516831) B2516831
theorem B1677895 : Blo 1676038 1677895 := bstep (se 1 (by rfl) ⟨1258421, by rfl⟩ : syracuseStep 1677895 = 2516843) B2516843
theorem B3775049 : Blo 1676038 3775049 := bstep (se 2 (by rfl) ⟨1415643, by rfl⟩ : syracuseStep 3775049 = 2831287) B2831287
theorem B8059499 : Blo 1676038 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B66239117 : Blo 1676038 66239117 := bstep (se 3 (by rfl) ⟨12419834, by rfl⟩ : syracuseStep 66239117 = 24839669) B24839669
theorem B3185335 : Blo 1676038 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B6453955 : Blo 1676038 6453955 := bstep (se 1 (by rfl) ⟨4840466, by rfl⟩ : syracuseStep 6453955 = 9680933) B9680933
theorem B8608477 : Blo 1676038 8608477 := bstep (se 3 (by rfl) ⟨1614089, by rfl⟩ : syracuseStep 8608477 = 3228179) B3228179
theorem B21486455 : Blo 1676038 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B3185563 : Blo 1676038 3185563 := bstep (se 1 (by rfl) ⟨2389172, by rfl⟩ : syracuseStep 3185563 = 4778345) B4778345
theorem B2014183 : Blo 1676038 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B3775463 : Blo 1676038 3775463 := bstep (se 1 (by rfl) ⟨2831597, by rfl⟩ : syracuseStep 3775463 = 5663195) B5663195
theorem B3185639 : Blo 1676038 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B11467763 : Blo 1676038 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B4242719 : Blo 1676038 4242719 := bstep (se 1 (by rfl) ⟨3182039, by rfl⟩ : syracuseStep 4242719 = 6364079) B6364079
theorem B2514215 : Blo 1676038 2514215 := bstep (se 1 (by rfl) ⟨1885661, by rfl⟩ : syracuseStep 2514215 = 3771323) B3771323
theorem B2514299 : Blo 1676038 2514299 := bstep (se 1 (by rfl) ⟨1885724, by rfl⟩ : syracuseStep 2514299 = 3771449) B3771449
theorem B2014663 : Blo 1676038 2014663 := bstep (se 1 (by rfl) ⟨1510997, by rfl⟩ : syracuseStep 2014663 = 3021995) B3021995
theorem B2514425 : Blo 1676038 2514425 := bstep (se 2 (by rfl) ⟨942909, by rfl⟩ : syracuseStep 2514425 = 1885819) B1885819
theorem B17219087 : Blo 1676038 17219087 := bstep (se 1 (by rfl) ⟨12914315, by rfl⟩ : syracuseStep 17219087 = 25828631) B25828631
theorem B2514527 : Blo 1676038 2514527 := bstep (se 1 (by rfl) ⟨1885895, by rfl⟩ : syracuseStep 2514527 = 3771791) B3771791
theorem B12902003 : Blo 1676038 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B12910195 : Blo 1676038 12910195 := bstep (se 1 (by rfl) ⟨9682646, by rfl⟩ : syracuseStep 12910195 = 19365293) B19365293
theorem B4030249 : Blo 1676038 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B2514743 : Blo 1676038 2514743 := bstep (se 1 (by rfl) ⟨1886057, by rfl⟩ : syracuseStep 2514743 = 3772115) B3772115
theorem B2686775 : Blo 1676038 2686775 := bstep (se 1 (by rfl) ⟨2015081, by rfl⟩ : syracuseStep 2686775 = 4030163) B4030163
theorem B8494955 : Blo 1676038 8494955 := bstep (se 1 (by rfl) ⟨6371216, by rfl⟩ : syracuseStep 8494955 = 12742433) B12742433
theorem B19095425 : Blo 1676038 19095425 := bstep (se 2 (by rfl) ⟨7160784, by rfl⟩ : syracuseStep 19095425 = 14321569) B14321569
theorem B7651361 : Blo 1676038 7651361 := bstep (se 2 (by rfl) ⟨2869260, by rfl⟩ : syracuseStep 7651361 = 5738521) B5738521
theorem B5660711 : Blo 1676038 5660711 := bstep (se 1 (by rfl) ⟨4245533, by rfl⟩ : syracuseStep 5660711 = 8491067) B8491067
theorem B10887211 : Blo 1676038 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B9551951 : Blo 1676038 9551951 := bstep (se 1 (by rfl) ⟨7163963, by rfl⟩ : syracuseStep 9551951 = 14327927) B14327927
theorem B2515163 : Blo 1676038 2515163 := bstep (se 1 (by rfl) ⟨1886372, by rfl⟩ : syracuseStep 2515163 = 3772745) B3772745
theorem B2515175 : Blo 1676038 2515175 := bstep (se 1 (by rfl) ⟨1886381, by rfl⟩ : syracuseStep 2515175 = 3772763) B3772763
theorem B2015543 : Blo 1676038 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B6365537 : Blo 1676038 6365537 := bstep (se 2 (by rfl) ⟨2387076, by rfl⟩ : syracuseStep 6365537 = 4774153) B4774153
theorem B2515337 : Blo 1676038 2515337 := bstep (se 2 (by rfl) ⟨943251, by rfl⟩ : syracuseStep 2515337 = 1886503) B1886503
theorem B10338779 : Blo 1676038 10338779 := bstep (se 1 (by rfl) ⟨7754084, by rfl⟩ : syracuseStep 10338779 = 15508169) B15508169
theorem B2515433 : Blo 1676038 2515433 := bstep (se 2 (by rfl) ⟨943287, by rfl⟩ : syracuseStep 2515433 = 1886575) B1886575
theorem B7651835 : Blo 1676038 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B7160359 : Blo 1676038 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B2515559 : Blo 1676038 2515559 := bstep (se 1 (by rfl) ⟨1886669, by rfl⟩ : syracuseStep 2515559 = 3773339) B3773339
theorem B10748537 : Blo 1676038 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B5661359 : Blo 1676038 5661359 := bstep (se 1 (by rfl) ⟨4246019, by rfl⟩ : syracuseStep 5661359 = 8492039) B8492039
theorem B2548459 : Blo 1676038 2548459 := bstep (se 1 (by rfl) ⟨1911344, by rfl⟩ : syracuseStep 2548459 = 3822689) B3822689
theorem B2515691 : Blo 1676038 2515691 := bstep (se 1 (by rfl) ⟨1886768, by rfl⟩ : syracuseStep 2515691 = 3773537) B3773537
theorem B2515721 : Blo 1676038 2515721 := bstep (se 2 (by rfl) ⟨943395, by rfl⟩ : syracuseStep 2515721 = 1886791) B1886791
theorem B8282891 : Blo 1676038 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B2515823 : Blo 1676038 2515823 := bstep (se 1 (by rfl) ⟨1886867, by rfl⟩ : syracuseStep 2515823 = 3773735) B3773735
theorem B12731255 : Blo 1676038 12731255 := bstep (se 1 (by rfl) ⟨9548441, by rfl⟩ : syracuseStep 12731255 = 19096883) B19096883
theorem B9192311 : Blo 1676038 9192311 := bstep (se 1 (by rfl) ⟨6894233, by rfl⟩ : syracuseStep 9192311 = 13788467) B13788467
theorem B11477969 : Blo 1676038 11477969 := bstep (se 2 (by rfl) ⟨4304238, by rfl⟩ : syracuseStep 11477969 = 8608477) B8608477
theorem B5661683 : Blo 1676038 5661683 := bstep (se 1 (by rfl) ⟨4246262, by rfl⟩ : syracuseStep 5661683 = 8492525) B8492525
theorem B2516075 : Blo 1676038 2516075 := bstep (se 1 (by rfl) ⟨1887056, by rfl⟩ : syracuseStep 2516075 = 3774113) B3774113
theorem B2516315 : Blo 1676038 2516315 := bstep (se 1 (by rfl) ⟨1887236, by rfl⟩ : syracuseStep 2516315 = 3774473) B3774473
theorem B3106219 : Blo 1676038 3106219 := bstep (se 1 (by rfl) ⟨2329664, by rfl⟩ : syracuseStep 3106219 = 4659329) B4659329
theorem B5662223 : Blo 1676038 5662223 := bstep (se 1 (by rfl) ⟨4246667, by rfl⟩ : syracuseStep 5662223 = 8493335) B8493335
theorem B2516591 : Blo 1676038 2516591 := bstep (se 1 (by rfl) ⟨1887443, by rfl⟩ : syracuseStep 2516591 = 3774887) B3774887
theorem B2516663 : Blo 1676038 2516663 := bstep (se 1 (by rfl) ⟨1887497, by rfl⟩ : syracuseStep 2516663 = 3774995) B3774995
theorem B2516699 : Blo 1676038 2516699 := bstep (se 1 (by rfl) ⟨1887524, by rfl⟩ : syracuseStep 2516699 = 3775049) B3775049
theorem B7161641 : Blo 1676038 7161641 := bstep (se 2 (by rfl) ⟨2685615, by rfl⟩ : syracuseStep 7161641 = 5371231) B5371231
theorem B2516873 : Blo 1676038 2516873 := bstep (se 2 (by rfl) ⟨943827, by rfl⟩ : syracuseStep 2516873 = 1887655) B1887655
theorem B2516975 : Blo 1676038 2516975 := bstep (se 1 (by rfl) ⟨1887731, by rfl⟩ : syracuseStep 2516975 = 3775463) B3775463
theorem B2123759 : Blo 1676038 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B7645175 : Blo 1676038 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B10749995 : Blo 1676038 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B17213593 : Blo 1676038 17213593 := bstep (se 2 (by rfl) ⟨6455097, by rfl⟩ : syracuseStep 17213593 = 12910195) B12910195
theorem B2828479 : Blo 1676038 2828479 := bstep (se 1 (by rfl) ⟨2121359, by rfl⟩ : syracuseStep 2828479 = 4242719) B4242719
theorem B4245817 : Blo 1676038 4245817 := bstep (se 2 (by rfl) ⟨1592181, by rfl⟩ : syracuseStep 4245817 = 3184363) B3184363
theorem B5663033 : Blo 1676038 5663033 := bstep (se 2 (by rfl) ⟨2123637, by rfl⟩ : syracuseStep 5663033 = 4247275) B4247275
theorem B11479391 : Blo 1676038 11479391 := bstep (se 1 (by rfl) ⟨8609543, by rfl⟩ : syracuseStep 11479391 = 17219087) B17219087
theorem B7752199 : Blo 1676038 7752199 := bstep (se 1 (by rfl) ⟨5814149, by rfl⟩ : syracuseStep 7752199 = 11628299) B11628299
theorem B5663303 : Blo 1676038 5663303 := bstep (se 1 (by rfl) ⟨4247477, by rfl⟩ : syracuseStep 5663303 = 8494955) B8494955
theorem B4246121 : Blo 1676038 4246121 := bstep (se 2 (by rfl) ⟨1592295, by rfl⟩ : syracuseStep 4246121 = 3184591) B3184591
theorem B2829215 : Blo 1676038 2829215 := bstep (se 1 (by rfl) ⟨2121911, by rfl⟩ : syracuseStep 2829215 = 4243823) B4243823
theorem B2387065 : Blo 1676038 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B2829647 : Blo 1676038 2829647 := bstep (se 1 (by rfl) ⟨2122235, by rfl⟩ : syracuseStep 2829647 = 4244471) B4244471
theorem B3771899 : Blo 1676038 3771899 := bstep (se 1 (by rfl) ⟨2828924, by rfl⟩ : syracuseStep 3771899 = 5657849) B5657849
theorem B4247113 : Blo 1676038 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B8605273 : Blo 1676038 8605273 := bstep (se 2 (by rfl) ⟨3226977, by rfl⟩ : syracuseStep 8605273 = 6453955) B6453955
theorem B3772079 : Blo 1676038 3772079 := bstep (se 1 (by rfl) ⟨2829059, by rfl⟩ : syracuseStep 3772079 = 5658119) B5658119
theorem B4247417 : Blo 1676038 4247417 := bstep (se 2 (by rfl) ⟨1592781, by rfl⟩ : syracuseStep 4247417 = 3185563) B3185563
theorem B55144385 : Blo 1676038 55144385 := bstep (se 2 (by rfl) ⟨20679144, by rfl⟩ : syracuseStep 55144385 = 41358289) B41358289
theorem B6041567 : Blo 1676038 6041567 := bstep (se 1 (by rfl) ⟨4531175, by rfl⟩ : syracuseStep 6041567 = 9062351) B9062351
theorem B20410487 : Blo 1676038 20410487 := bstep (se 1 (by rfl) ⟨15307865, by rfl⟩ : syracuseStep 20410487 = 30615731) B30615731
theorem B6041785 : Blo 1676038 6041785 := bstep (se 2 (by rfl) ⟨2265669, by rfl⟩ : syracuseStep 6041785 = 4531339) B4531339
theorem B8491229 : Blo 1676038 8491229 := bstep (se 3 (by rfl) ⟨1592105, by rfl⟩ : syracuseStep 8491229 = 3184211) B3184211
theorem B2388199 : Blo 1676038 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B3772727 : Blo 1676038 3772727 := bstep (se 1 (by rfl) ⟨2829545, by rfl⟩ : syracuseStep 3772727 = 5659091) B5659091
theorem B3772799 : Blo 1676038 3772799 := bstep (se 1 (by rfl) ⟨2829599, by rfl⟩ : syracuseStep 3772799 = 5659199) B5659199
theorem B8491391 : Blo 1676038 8491391 := bstep (se 1 (by rfl) ⟨6368543, by rfl⟩ : syracuseStep 8491391 = 12737087) B12737087
theorem B44159411 : Blo 1676038 44159411 := bstep (se 1 (by rfl) ⟨33119558, by rfl⟩ : syracuseStep 44159411 = 66239117) B66239117
theorem B14324303 : Blo 1676038 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B2830943 : Blo 1676038 2830943 := bstep (se 1 (by rfl) ⟨2123207, by rfl⟩ : syracuseStep 2830943 = 4246415) B4246415
theorem B7164733 : Blo 1676038 7164733 := bstep (se 3 (by rfl) ⟨1343387, by rfl⟩ : syracuseStep 7164733 = 2686775) B2686775
theorem B1676143 : Blo 1676038 1676143 := bstep (se 1 (by rfl) ⟨1257107, by rfl⟩ : syracuseStep 1676143 = 2514215) B2514215
theorem B1676199 : Blo 1676038 1676199 := bstep (se 1 (by rfl) ⟨1257149, by rfl⟩ : syracuseStep 1676199 = 2514299) B2514299
theorem B1676283 : Blo 1676038 1676283 := bstep (se 1 (by rfl) ⟨1257212, by rfl⟩ : syracuseStep 1676283 = 2514425) B2514425
theorem B1676351 : Blo 1676038 1676351 := bstep (se 1 (by rfl) ⟨1257263, by rfl⟩ : syracuseStep 1676351 = 2514527) B2514527
theorem B1676495 : Blo 1676038 1676495 := bstep (se 1 (by rfl) ⟨1257371, by rfl⟩ : syracuseStep 1676495 = 2514743) B2514743
theorem B27186529 : Blo 1676038 27186529 := bstep (se 2 (by rfl) ⟨10194948, by rfl⟩ : syracuseStep 27186529 = 20389897) B20389897
theorem B5658011 : Blo 1676038 5658011 := bstep (se 1 (by rfl) ⟨4243508, by rfl⟩ : syracuseStep 5658011 = 8487017) B8487017
theorem B1676699 : Blo 1676038 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B7648769 : Blo 1676038 7648769 := bstep (se 2 (by rfl) ⟨2868288, by rfl⟩ : syracuseStep 7648769 = 5736577) B5736577
theorem B3774023 : Blo 1676038 3774023 := bstep (se 1 (by rfl) ⟨2830517, by rfl⟩ : syracuseStep 3774023 = 5661035) B5661035
theorem B1676911 : Blo 1676038 1676911 := bstep (se 1 (by rfl) ⟨1257683, by rfl⟩ : syracuseStep 1676911 = 2515367) B2515367
theorem B1676967 : Blo 1676038 1676967 := bstep (se 1 (by rfl) ⟨1257725, by rfl⟩ : syracuseStep 1676967 = 2515451) B2515451
theorem B1677051 : Blo 1676038 1677051 := bstep (se 1 (by rfl) ⟨1257788, by rfl⟩ : syracuseStep 1677051 = 2515577) B2515577
theorem B3774203 : Blo 1676038 3774203 := bstep (se 1 (by rfl) ⟨2830652, by rfl⟩ : syracuseStep 3774203 = 5661305) B5661305
theorem B1677087 : Blo 1676038 1677087 := bstep (se 1 (by rfl) ⟨1257815, by rfl⟩ : syracuseStep 1677087 = 2515631) B2515631
theorem B1677119 : Blo 1676038 1677119 := bstep (se 1 (by rfl) ⟨1257839, by rfl⟩ : syracuseStep 1677119 = 2515679) B2515679
theorem B3184447 : Blo 1676038 3184447 := bstep (se 1 (by rfl) ⟨2388335, by rfl⟩ : syracuseStep 3184447 = 4776671) B4776671
theorem B1677295 : Blo 1676038 1677295 := bstep (se 1 (by rfl) ⟨1257971, by rfl⟩ : syracuseStep 1677295 = 2515943) B2515943
theorem B6043673 : Blo 1676038 6043673 := bstep (se 2 (by rfl) ⟨2266377, by rfl⟩ : syracuseStep 6043673 = 4532755) B4532755
theorem B4773971 : Blo 1676038 4773971 := bstep (se 1 (by rfl) ⟨3580478, by rfl⟩ : syracuseStep 4773971 = 7160957) B7160957
theorem B5658767 : Blo 1676038 5658767 := bstep (se 1 (by rfl) ⟨4244075, by rfl⟩ : syracuseStep 5658767 = 8488151) B8488151
theorem B1677467 : Blo 1676038 1677467 := bstep (se 1 (by rfl) ⟨1258100, by rfl⟩ : syracuseStep 1677467 = 2516201) B2516201
theorem B1677503 : Blo 1676038 1677503 := bstep (se 1 (by rfl) ⟨1258127, by rfl⟩ : syracuseStep 1677503 = 2516255) B2516255
theorem B3774761 : Blo 1676038 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1677615 : Blo 1676038 1677615 := bstep (se 1 (by rfl) ⟨1258211, by rfl⟩ : syracuseStep 1677615 = 2516423) B2516423
theorem B32225687 : Blo 1676038 32225687 := bstep (se 1 (by rfl) ⟨24169265, by rfl⟩ : syracuseStep 32225687 = 48338531) B48338531
theorem B5102099 : Blo 1676038 5102099 := bstep (se 1 (by rfl) ⟨3826574, by rfl⟩ : syracuseStep 5102099 = 7653149) B7653149
theorem B1677851 : Blo 1676038 1677851 := bstep (se 1 (by rfl) ⟨1258388, by rfl⟩ : syracuseStep 1677851 = 2516777) B2516777
theorem B1677855 : Blo 1676038 1677855 := bstep (se 1 (by rfl) ⟨1258391, by rfl⟩ : syracuseStep 1677855 = 2516783) B2516783
theorem B2685577 : Blo 1676038 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B24222347 : Blo 1676038 24222347 := bstep (se 1 (by rfl) ⟨18166760, by rfl⟩ : syracuseStep 24222347 = 36333521) B36333521
theorem B6363805 : Blo 1676038 6363805 := bstep (se 3 (by rfl) ⟨1193213, by rfl⟩ : syracuseStep 6363805 = 2386427) B2386427
theorem B3775337 : Blo 1676038 3775337 := bstep (se 2 (by rfl) ⟨1415751, by rfl⟩ : syracuseStep 3775337 = 2831503) B2831503
theorem B8493983 : Blo 1676038 8493983 := bstep (se 1 (by rfl) ⟨6370487, by rfl⟩ : syracuseStep 8493983 = 12740975) B12740975
theorem B3775391 : Blo 1676038 3775391 := bstep (se 1 (by rfl) ⟨2831543, by rfl⟩ : syracuseStep 3775391 = 5663087) B5663087
theorem B5372999 : Blo 1676038 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B4775041 : Blo 1676038 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B8486045 : Blo 1676038 8486045 := bstep (se 3 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 8486045 = 3182267) B3182267
theorem B2514143 : Blo 1676038 2514143 := bstep (se 1 (by rfl) ⟨1885607, by rfl⟩ : syracuseStep 2514143 = 3771215) B3771215
theorem B5659901 : Blo 1676038 5659901 := bstep (se 3 (by rfl) ⟨1061231, by rfl⟩ : syracuseStep 5659901 = 2122463) B2122463
theorem B20389121 : Blo 1676038 20389121 := bstep (se 2 (by rfl) ⟨7645920, by rfl⟩ : syracuseStep 20389121 = 15291841) B15291841
theorem B2514185 : Blo 1676038 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B2686217 : Blo 1676038 2686217 := bstep (se 2 (by rfl) ⟨1007331, by rfl⟩ : syracuseStep 2686217 = 2014663) B2014663
theorem B298098019 : Blo 1676038 298098019 := bstep (se 1 (by rfl) ⟨223573514, by rfl⟩ : syracuseStep 298098019 = 447147029) B447147029
theorem B2514287 : Blo 1676038 2514287 := bstep (se 1 (by rfl) ⟨1885715, by rfl⟩ : syracuseStep 2514287 = 3771431) B3771431
theorem B2514407 : Blo 1676038 2514407 := bstep (se 1 (by rfl) ⟨1885805, by rfl⟩ : syracuseStep 2514407 = 3771611) B3771611
theorem B3399259 : Blo 1676038 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B2514539 : Blo 1676038 2514539 := bstep (se 1 (by rfl) ⟨1885904, by rfl⟩ : syracuseStep 2514539 = 3771809) B3771809
theorem B4775611 : Blo 1676038 4775611 := bstep (se 1 (by rfl) ⟨3581708, by rfl⟩ : syracuseStep 4775611 = 7163417) B7163417
theorem B5373665 : Blo 1676038 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B2514665 : Blo 1676038 2514665 := bstep (se 2 (by rfl) ⟨942999, by rfl⟩ : syracuseStep 2514665 = 1885999) B1885999
theorem B8601335 : Blo 1676038 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B2514809 : Blo 1676038 2514809 := bstep (se 2 (by rfl) ⟨943053, by rfl⟩ : syracuseStep 2514809 = 1886107) B1886107
theorem B6365051 : Blo 1676038 6365051 := bstep (se 1 (by rfl) ⟨4773788, by rfl⟩ : syracuseStep 6365051 = 9547577) B9547577
theorem B12730283 : Blo 1676038 12730283 := bstep (se 1 (by rfl) ⟨9547712, by rfl⟩ : syracuseStep 12730283 = 19095425) B19095425
theorem B40812497 : Blo 1676038 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B2514911 : Blo 1676038 2514911 := bstep (se 1 (by rfl) ⟨1886183, by rfl⟩ : syracuseStep 2514911 = 3772367) B3772367
theorem B14516281 : Blo 1676038 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B13606991 : Blo 1676038 13606991 := bstep (se 1 (by rfl) ⟨10205243, by rfl⟩ : syracuseStep 13606991 = 20410487) B20410487
theorem B5660819 : Blo 1676038 5660819 := bstep (se 1 (by rfl) ⟨4245614, by rfl⟩ : syracuseStep 5660819 = 8491229) B8491229
theorem B2515151 : Blo 1676038 2515151 := bstep (se 1 (by rfl) ⟨1886363, by rfl⟩ : syracuseStep 2515151 = 3772727) B3772727
theorem B4243691 : Blo 1676038 4243691 := bstep (se 1 (by rfl) ⟨3182768, by rfl⟩ : syracuseStep 4243691 = 6365537) B6365537
theorem B2515199 : Blo 1676038 2515199 := bstep (se 1 (by rfl) ⟨1886399, by rfl⟩ : syracuseStep 2515199 = 3772799) B3772799
theorem B5660927 : Blo 1676038 5660927 := bstep (se 1 (by rfl) ⟨4245695, by rfl⟩ : syracuseStep 5660927 = 8491391) B8491391
theorem B5661089 : Blo 1676038 5661089 := bstep (se 2 (by rfl) ⟨2122908, by rfl⟩ : syracuseStep 5661089 = 4245817) B4245817
theorem B8487503 : Blo 1676038 8487503 := bstep (se 1 (by rfl) ⟨6365627, by rfl⟩ : syracuseStep 8487503 = 12731255) B12731255
theorem B6128207 : Blo 1676038 6128207 := bstep (se 1 (by rfl) ⟨4596155, by rfl⟩ : syracuseStep 6128207 = 9192311) B9192311
theorem B7651979 : Blo 1676038 7651979 := bstep (se 1 (by rfl) ⟨5738984, by rfl⟩ : syracuseStep 7651979 = 11477969) B11477969
theorem B5374781 : Blo 1676038 5374781 := bstep (se 3 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 5374781 = 2015543) B2015543
theorem B3580769 : Blo 1676038 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B2516015 : Blo 1676038 2516015 := bstep (se 1 (by rfl) ⟨1887011, by rfl⟩ : syracuseStep 2516015 = 3774023) B3774023
theorem B9552977 : Blo 1676038 9552977 := bstep (se 2 (by rfl) ⟨3582366, by rfl⟩ : syracuseStep 9552977 = 7164733) B7164733
theorem B2516135 : Blo 1676038 2516135 := bstep (se 1 (by rfl) ⟨1887101, by rfl⟩ : syracuseStep 2516135 = 3774203) B3774203
theorem B5096783 : Blo 1676038 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B6366721 : Blo 1676038 6366721 := bstep (se 2 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 6366721 = 4775041) B4775041
theorem B2516507 : Blo 1676038 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B7652927 : Blo 1676038 7652927 := bstep (se 1 (by rfl) ⟨5739695, by rfl⟩ : syracuseStep 7652927 = 11479391) B11479391
theorem B3401399 : Blo 1676038 3401399 := bstep (se 1 (by rfl) ⟨2551049, by rfl⟩ : syracuseStep 3401399 = 5102099) B5102099
theorem B16148231 : Blo 1676038 16148231 := bstep (se 1 (by rfl) ⟨12111173, by rfl⟩ : syracuseStep 16148231 = 24222347) B24222347
theorem B2516891 : Blo 1676038 2516891 := bstep (se 1 (by rfl) ⟨1887668, by rfl⟩ : syracuseStep 2516891 = 3775337) B3775337
theorem B1886143 : Blo 1676038 1886143 := bstep (se 1 (by rfl) ⟨1414607, by rfl⟩ : syracuseStep 1886143 = 2829215) B2829215
theorem B5662655 : Blo 1676038 5662655 := bstep (se 1 (by rfl) ⟨4246991, by rfl⟩ : syracuseStep 5662655 = 8493983) B8493983
theorem B2516927 : Blo 1676038 2516927 := bstep (se 1 (by rfl) ⟨1887695, by rfl⟩ : syracuseStep 2516927 = 3775391) B3775391
theorem B22087709 : Blo 1676038 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B3581999 : Blo 1676038 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B5662817 : Blo 1676038 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B4532345 : Blo 1676038 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B13592747 : Blo 1676038 13592747 := bstep (se 1 (by rfl) ⟨10194560, by rfl⟩ : syracuseStep 13592747 = 20389121) B20389121
theorem B1886431 : Blo 1676038 1886431 := bstep (se 1 (by rfl) ⟨1414823, by rfl⟩ : syracuseStep 1886431 = 2829647) B2829647
theorem B6367481 : Blo 1676038 6367481 := bstep (se 2 (by rfl) ⟨2387805, by rfl⟩ : syracuseStep 6367481 = 4775611) B4775611
theorem B4245929 : Blo 1676038 4245929 := bstep (se 2 (by rfl) ⟨1592223, by rfl⟩ : syracuseStep 4245929 = 3184447) B3184447
theorem B3582443 : Blo 1676038 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B5663357 : Blo 1676038 5663357 := bstep (se 3 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 5663357 = 2123759) B2123759
theorem B27208331 : Blo 1676038 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B6367967 : Blo 1676038 6367967 := bstep (se 1 (by rfl) ⟨4775975, by rfl⟩ : syracuseStep 6367967 = 9551951) B9551951
theorem B8055713 : Blo 1676038 8055713 := bstep (se 2 (by rfl) ⟨3020892, by rfl⟩ : syracuseStep 8055713 = 6041785) B6041785
theorem B3771305 : Blo 1676038 3771305 := bstep (se 2 (by rfl) ⟨1414239, by rfl⟩ : syracuseStep 3771305 = 2828479) B2828479
theorem B6892519 : Blo 1676038 6892519 := bstep (se 1 (by rfl) ⟨5169389, by rfl⟩ : syracuseStep 6892519 = 10338779) B10338779
theorem B1887295 : Blo 1676038 1887295 := bstep (se 1 (by rfl) ⟨1415471, by rfl⟩ : syracuseStep 1887295 = 2830943) B2830943
theorem B7163245 : Blo 1676038 7163245 := bstep (se 3 (by rfl) ⟨1343108, by rfl⟩ : syracuseStep 7163245 = 2686217) B2686217
theorem B9547145 : Blo 1676038 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B3772007 : Blo 1676038 3772007 := bstep (se 1 (by rfl) ⟨2829005, by rfl⟩ : syracuseStep 3772007 = 5658011) B5658011
theorem B5099179 : Blo 1676038 5099179 := bstep (se 1 (by rfl) ⟨3824384, by rfl⟩ : syracuseStep 5099179 = 7648769) B7648769
theorem B3182647 : Blo 1676038 3182647 := bstep (se 1 (by rfl) ⟨2386985, by rfl⟩ : syracuseStep 3182647 = 4773971) B4773971
theorem B3772511 : Blo 1676038 3772511 := bstep (se 1 (by rfl) ⟨2829383, by rfl⟩ : syracuseStep 3772511 = 5658767) B5658767
theorem B3182753 : Blo 1676038 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B21483791 : Blo 1676038 21483791 := bstep (se 1 (by rfl) ⟨16112843, by rfl⟩ : syracuseStep 21483791 = 32225687) B32225687
theorem B2830747 : Blo 1676038 2830747 := bstep (se 1 (by rfl) ⟨2123060, by rfl⟩ : syracuseStep 2830747 = 4246121) B4246121
theorem B397464025 : Blo 1676038 397464025 := bstep (se 2 (by rfl) ⟨149049009, by rfl⟩ : syracuseStep 397464025 = 298098019) B298098019
theorem B4141625 : Blo 1676038 4141625 := bstep (se 2 (by rfl) ⟨1553109, by rfl⟩ : syracuseStep 4141625 = 3106219) B3106219
theorem B5657363 : Blo 1676038 5657363 := bstep (se 1 (by rfl) ⟨4243022, by rfl⟩ : syracuseStep 5657363 = 8486045) B8486045
theorem B11473697 : Blo 1676038 11473697 := bstep (se 2 (by rfl) ⟨4302636, by rfl⟩ : syracuseStep 11473697 = 8605273) B8605273
theorem B1676095 : Blo 1676038 1676095 := bstep (se 1 (by rfl) ⟨1257071, by rfl⟩ : syracuseStep 1676095 = 2514143) B2514143
theorem B3773267 : Blo 1676038 3773267 := bstep (se 1 (by rfl) ⟨2829950, by rfl⟩ : syracuseStep 3773267 = 5659901) B5659901
theorem B1676123 : Blo 1676038 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B1676191 : Blo 1676038 1676191 := bstep (se 1 (by rfl) ⟨1257143, by rfl⟩ : syracuseStep 1676191 = 2514287) B2514287
theorem B1676271 : Blo 1676038 1676271 := bstep (se 1 (by rfl) ⟨1257203, by rfl⟩ : syracuseStep 1676271 = 2514407) B2514407
theorem B1676359 : Blo 1676038 1676359 := bstep (se 1 (by rfl) ⟨1257269, by rfl⟩ : syracuseStep 1676359 = 2514539) B2514539
theorem B1676443 : Blo 1676038 1676443 := bstep (se 1 (by rfl) ⟨1257332, by rfl⟩ : syracuseStep 1676443 = 2514665) B2514665
theorem B1676539 : Blo 1676038 1676539 := bstep (se 1 (by rfl) ⟨1257404, by rfl⟩ : syracuseStep 1676539 = 2514809) B2514809
theorem B2831611 : Blo 1676038 2831611 := bstep (se 1 (by rfl) ⟨2123708, by rfl⟩ : syracuseStep 2831611 = 4247417) B4247417
theorem B16110845 : Blo 1676038 16110845 := bstep (se 3 (by rfl) ⟨3020783, by rfl⟩ : syracuseStep 16110845 = 6041567) B6041567
theorem B36762923 : Blo 1676038 36762923 := bstep (se 1 (by rfl) ⟨27572192, by rfl⟩ : syracuseStep 36762923 = 55144385) B55144385
theorem B1676607 : Blo 1676038 1676607 := bstep (se 1 (by rfl) ⟨1257455, by rfl⟩ : syracuseStep 1676607 = 2514911) B2514911
theorem B5100907 : Blo 1676038 5100907 := bstep (se 1 (by rfl) ⟨3825680, by rfl⟩ : syracuseStep 5100907 = 7651361) B7651361
theorem B3773807 : Blo 1676038 3773807 := bstep (se 1 (by rfl) ⟨2830355, by rfl⟩ : syracuseStep 3773807 = 5660711) B5660711
theorem B1676775 : Blo 1676038 1676775 := bstep (se 1 (by rfl) ⟨1257581, by rfl⟩ : syracuseStep 1676775 = 2515163) B2515163
theorem B1676783 : Blo 1676038 1676783 := bstep (se 1 (by rfl) ⟨1257587, by rfl⟩ : syracuseStep 1676783 = 2515175) B2515175
theorem B22951457 : Blo 1676038 22951457 := bstep (se 2 (by rfl) ⟨8606796, by rfl⟩ : syracuseStep 22951457 = 17213593) B17213593
theorem B1676891 : Blo 1676038 1676891 := bstep (se 1 (by rfl) ⟨1257668, by rfl⟩ : syracuseStep 1676891 = 2515337) B2515337
theorem B29439607 : Blo 1676038 29439607 := bstep (se 1 (by rfl) ⟨22079705, by rfl⟩ : syracuseStep 29439607 = 44159411) B44159411
theorem B3184265 : Blo 1676038 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B1676955 : Blo 1676038 1676955 := bstep (se 1 (by rfl) ⟨1257716, by rfl⟩ : syracuseStep 1676955 = 2515433) B2515433
theorem B5101223 : Blo 1676038 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B9549535 : Blo 1676038 9549535 := bstep (se 1 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 9549535 = 14324303) B14324303
theorem B1677039 : Blo 1676038 1677039 := bstep (se 1 (by rfl) ⟨1257779, by rfl⟩ : syracuseStep 1677039 = 2515559) B2515559
theorem B7165691 : Blo 1676038 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B3774239 : Blo 1676038 3774239 := bstep (se 1 (by rfl) ⟨2830679, by rfl⟩ : syracuseStep 3774239 = 5661359) B5661359
theorem B1677127 : Blo 1676038 1677127 := bstep (se 1 (by rfl) ⟨1257845, by rfl⟩ : syracuseStep 1677127 = 2515691) B2515691
theorem B1677147 : Blo 1676038 1677147 := bstep (se 1 (by rfl) ⟨1257860, by rfl⟩ : syracuseStep 1677147 = 2515721) B2515721
theorem B1677215 : Blo 1676038 1677215 := bstep (se 1 (by rfl) ⟨1257911, by rfl⟩ : syracuseStep 1677215 = 2515823) B2515823
theorem B3774455 : Blo 1676038 3774455 := bstep (se 1 (by rfl) ⟨2830841, by rfl⟩ : syracuseStep 3774455 = 5661683) B5661683
theorem B10336265 : Blo 1676038 10336265 := bstep (se 2 (by rfl) ⟨3876099, by rfl⟩ : syracuseStep 10336265 = 7752199) B7752199
theorem B1677383 : Blo 1676038 1677383 := bstep (se 1 (by rfl) ⟨1258037, by rfl⟩ : syracuseStep 1677383 = 2516075) B2516075
theorem B8485073 : Blo 1676038 8485073 := bstep (se 2 (by rfl) ⟨3181902, by rfl⟩ : syracuseStep 8485073 = 6363805) B6363805
theorem B1677543 : Blo 1676038 1677543 := bstep (se 1 (by rfl) ⟨1258157, by rfl⟩ : syracuseStep 1677543 = 2516315) B2516315
theorem B3397945 : Blo 1676038 3397945 := bstep (se 2 (by rfl) ⟨1274229, by rfl⟩ : syracuseStep 3397945 = 2548459) B2548459
theorem B3774815 : Blo 1676038 3774815 := bstep (se 1 (by rfl) ⟨2831111, by rfl⟩ : syracuseStep 3774815 = 5662223) B5662223
theorem B1677727 : Blo 1676038 1677727 := bstep (se 1 (by rfl) ⟨1258295, by rfl⟩ : syracuseStep 1677727 = 2516591) B2516591
theorem B1677775 : Blo 1676038 1677775 := bstep (se 1 (by rfl) ⟨1258331, by rfl⟩ : syracuseStep 1677775 = 2516663) B2516663
theorem B1677799 : Blo 1676038 1677799 := bstep (se 1 (by rfl) ⟨1258349, by rfl⟩ : syracuseStep 1677799 = 2516699) B2516699
theorem B4774427 : Blo 1676038 4774427 := bstep (se 1 (by rfl) ⟨3580820, by rfl⟩ : syracuseStep 4774427 = 7161641) B7161641
theorem B1677915 : Blo 1676038 1677915 := bstep (se 1 (by rfl) ⟨1258436, by rfl⟩ : syracuseStep 1677915 = 2516873) B2516873
theorem B1677983 : Blo 1676038 1677983 := bstep (se 1 (by rfl) ⟨1258487, by rfl⟩ : syracuseStep 1677983 = 2516975) B2516975
theorem B4029115 : Blo 1676038 4029115 := bstep (se 1 (by rfl) ⟨3021836, by rfl⟩ : syracuseStep 4029115 = 6043673) B6043673
theorem B7166663 : Blo 1676038 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B3775355 : Blo 1676038 3775355 := bstep (se 1 (by rfl) ⟨2831516, by rfl⟩ : syracuseStep 3775355 = 5663033) B5663033
theorem B3775535 : Blo 1676038 3775535 := bstep (se 1 (by rfl) ⟨2831651, by rfl⟩ : syracuseStep 3775535 = 5663303) B5663303
theorem B36248705 : Blo 1676038 36248705 := bstep (se 2 (by rfl) ⟨13593264, by rfl⟩ : syracuseStep 36248705 = 27186529) B27186529
theorem B2514599 : Blo 1676038 2514599 := bstep (se 1 (by rfl) ⟨1885949, by rfl⟩ : syracuseStep 2514599 = 3771899) B3771899
theorem B2514719 : Blo 1676038 2514719 := bstep (se 1 (by rfl) ⟨1886039, by rfl⟩ : syracuseStep 2514719 = 3772079) B3772079
theorem B5734223 : Blo 1676038 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B4243367 : Blo 1676038 4243367 := bstep (se 1 (by rfl) ⟨3182525, by rfl⟩ : syracuseStep 4243367 = 6365051) B6365051
theorem B8486855 : Blo 1676038 8486855 := bstep (se 1 (by rfl) ⟨6365141, by rfl⟩ : syracuseStep 8486855 = 12730283) B12730283
theorem B2515007 : Blo 1676038 2515007 := bstep (se 1 (by rfl) ⟨1886255, by rfl⟩ : syracuseStep 2515007 = 3772511) B3772511
theorem B4243529 : Blo 1676038 4243529 := bstep (se 2 (by rfl) ⟨1591323, by rfl⟩ : syracuseStep 4243529 = 3182647) B3182647
theorem B2515241 : Blo 1676038 2515241 := bstep (se 2 (by rfl) ⟨943215, by rfl⟩ : syracuseStep 2515241 = 1886431) B1886431
theorem B235602229 : Blo 1676038 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B4530593 : Blo 1676038 4530593 := bstep (se 2 (by rfl) ⟨1698972, by rfl⟩ : syracuseStep 4530593 = 3397945) B3397945
theorem B8487341 : Blo 1676038 8487341 := bstep (se 3 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 8487341 = 3182753) B3182753
theorem B2515511 : Blo 1676038 2515511 := bstep (se 1 (by rfl) ⟨1886633, by rfl⟩ : syracuseStep 2515511 = 3773267) B3773267
theorem B10740563 : Blo 1676038 10740563 := bstep (se 1 (by rfl) ⟨8055422, by rfl⟩ : syracuseStep 10740563 = 16110845) B16110845
theorem B13591421 : Blo 1676038 13591421 := bstep (se 3 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 13591421 = 5096783) B5096783
theorem B2515871 : Blo 1676038 2515871 := bstep (se 1 (by rfl) ⟨1886903, by rfl⟩ : syracuseStep 2515871 = 3773807) B3773807
theorem B2122843 : Blo 1676038 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B4777127 : Blo 1676038 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B10765487 : Blo 1676038 10765487 := bstep (se 1 (by rfl) ⟨8074115, by rfl⟩ : syracuseStep 10765487 = 16148231) B16148231
theorem B2516159 : Blo 1676038 2516159 := bstep (se 1 (by rfl) ⟨1887119, by rfl⟩ : syracuseStep 2516159 = 3774239) B3774239
theorem B2516303 : Blo 1676038 2516303 := bstep (se 1 (by rfl) ⟨1887227, by rfl⟩ : syracuseStep 2516303 = 3774455) B3774455
theorem B6890843 : Blo 1676038 6890843 := bstep (se 1 (by rfl) ⟨5168132, by rfl⟩ : syracuseStep 6890843 = 10336265) B10336265
theorem B2516393 : Blo 1676038 2516393 := bstep (se 2 (by rfl) ⟨943647, by rfl⟩ : syracuseStep 2516393 = 1887295) B1887295
theorem B9061831 : Blo 1676038 9061831 := bstep (se 1 (by rfl) ⟨6796373, by rfl⟩ : syracuseStep 9061831 = 13592747) B13592747
theorem B11044333 : Blo 1676038 11044333 := bstep (se 3 (by rfl) ⟨2070812, by rfl⟩ : syracuseStep 11044333 = 4141625) B4141625
theorem B4244987 : Blo 1676038 4244987 := bstep (se 1 (by rfl) ⟨3183740, by rfl⟩ : syracuseStep 4244987 = 6367481) B6367481
theorem B2516543 : Blo 1676038 2516543 := bstep (se 1 (by rfl) ⟨1887407, by rfl⟩ : syracuseStep 2516543 = 3774815) B3774815
theorem B18138887 : Blo 1676038 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B4777775 : Blo 1676038 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B6801209 : Blo 1676038 6801209 := bstep (se 2 (by rfl) ⟨2550453, by rfl⟩ : syracuseStep 6801209 = 5100907) B5100907
theorem B4245311 : Blo 1676038 4245311 := bstep (se 1 (by rfl) ⟨3183983, by rfl⟩ : syracuseStep 4245311 = 6367967) B6367967
theorem B2516903 : Blo 1676038 2516903 := bstep (se 1 (by rfl) ⟨1887677, by rfl⟩ : syracuseStep 2516903 = 3775355) B3775355
theorem B8488961 : Blo 1676038 8488961 := bstep (se 2 (by rfl) ⟨3183360, by rfl⟩ : syracuseStep 8488961 = 6366721) B6366721
theorem B2517023 : Blo 1676038 2517023 := bstep (se 1 (by rfl) ⟨1887767, by rfl⟩ : syracuseStep 2517023 = 3775535) B3775535
theorem B12732713 : Blo 1676038 12732713 := bstep (se 2 (by rfl) ⟨4774767, by rfl⟩ : syracuseStep 12732713 = 9549535) B9549535
theorem B2828911 : Blo 1676038 2828911 := bstep (se 1 (by rfl) ⟨2121683, by rfl⟩ : syracuseStep 2828911 = 4243367) B4243367
theorem B9071327 : Blo 1676038 9071327 := bstep (se 1 (by rfl) ⟨6803495, by rfl⟩ : syracuseStep 9071327 = 13606991) B13606991
theorem B2829127 : Blo 1676038 2829127 := bstep (se 1 (by rfl) ⟨2121845, by rfl⟩ : syracuseStep 2829127 = 4243691) B4243691
theorem B14322527 : Blo 1676038 14322527 := bstep (se 1 (by rfl) ⟨10741895, by rfl⟩ : syracuseStep 14322527 = 21483791) B21483791
theorem B3771575 : Blo 1676038 3771575 := bstep (se 1 (by rfl) ⟨2828681, by rfl⟩ : syracuseStep 3771575 = 5657363) B5657363
theorem B3583187 : Blo 1676038 3583187 := bstep (se 1 (by rfl) ⟨2687390, by rfl⟩ : syracuseStep 3583187 = 5374781) B5374781
theorem B2387179 : Blo 1676038 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B529952033 : Blo 1676038 529952033 := bstep (se 2 (by rfl) ⟨198732012, by rfl⟩ : syracuseStep 529952033 = 397464025) B397464025
theorem B6368651 : Blo 1676038 6368651 := bstep (se 1 (by rfl) ⟨4776488, by rfl⟩ : syracuseStep 6368651 = 9552977) B9552977
theorem B2387999 : Blo 1676038 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B5656715 : Blo 1676038 5656715 := bstep (se 1 (by rfl) ⟨4242536, by rfl⟩ : syracuseStep 5656715 = 8485073) B8485073
theorem B2830619 : Blo 1676038 2830619 := bstep (se 1 (by rfl) ⟨2122964, by rfl⟩ : syracuseStep 2830619 = 4245929) B4245929
theorem B2388295 : Blo 1676038 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B3182951 : Blo 1676038 3182951 := bstep (se 1 (by rfl) ⟨2387213, by rfl⟩ : syracuseStep 3182951 = 4774427) B4774427
theorem B13603261 : Blo 1676038 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B5370475 : Blo 1676038 5370475 := bstep (se 1 (by rfl) ⟨4027856, by rfl⟩ : syracuseStep 5370475 = 8055713) B8055713
theorem B39252809 : Blo 1676038 39252809 := bstep (se 2 (by rfl) ⟨14719803, by rfl⟩ : syracuseStep 39252809 = 29439607) B29439607
theorem B1676399 : Blo 1676038 1676399 := bstep (se 1 (by rfl) ⟨1257299, by rfl⟩ : syracuseStep 1676399 = 2514599) B2514599
theorem B1676479 : Blo 1676038 1676479 := bstep (se 1 (by rfl) ⟨1257359, by rfl⟩ : syracuseStep 1676479 = 2514719) B2514719
theorem B3822815 : Blo 1676038 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B5657903 : Blo 1676038 5657903 := bstep (se 1 (by rfl) ⟨4243427, by rfl⟩ : syracuseStep 5657903 = 8486855) B8486855
theorem B19355041 : Blo 1676038 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B3773879 : Blo 1676038 3773879 := bstep (se 1 (by rfl) ⟨2830409, by rfl⟩ : syracuseStep 3773879 = 5660819) B5660819
theorem B1676767 : Blo 1676038 1676767 := bstep (se 1 (by rfl) ⟨1257575, by rfl⟩ : syracuseStep 1676767 = 2515151) B2515151
theorem B1676799 : Blo 1676038 1676799 := bstep (se 1 (by rfl) ⟨1257599, by rfl⟩ : syracuseStep 1676799 = 2515199) B2515199
theorem B3773951 : Blo 1676038 3773951 := bstep (se 1 (by rfl) ⟨2830463, by rfl⟩ : syracuseStep 3773951 = 5660927) B5660927
theorem B3774059 : Blo 1676038 3774059 := bstep (se 1 (by rfl) ⟨2830544, by rfl⟩ : syracuseStep 3774059 = 5661089) B5661089
theorem B5658335 : Blo 1676038 5658335 := bstep (se 1 (by rfl) ⟨4243751, by rfl⟩ : syracuseStep 5658335 = 8487503) B8487503
theorem B4085471 : Blo 1676038 4085471 := bstep (se 1 (by rfl) ⟨3064103, by rfl⟩ : syracuseStep 4085471 = 6128207) B6128207
theorem B5101319 : Blo 1676038 5101319 := bstep (se 1 (by rfl) ⟨3825989, by rfl⟩ : syracuseStep 5101319 = 7651979) B7651979
theorem B3774329 : Blo 1676038 3774329 := bstep (se 2 (by rfl) ⟨1415373, by rfl⟩ : syracuseStep 3774329 = 2830747) B2830747
theorem B1677343 : Blo 1676038 1677343 := bstep (se 1 (by rfl) ⟨1258007, by rfl⟩ : syracuseStep 1677343 = 2516015) B2516015
theorem B1677423 : Blo 1676038 1677423 := bstep (se 1 (by rfl) ⟨1258067, by rfl⟩ : syracuseStep 1677423 = 2516135) B2516135
theorem B24508615 : Blo 1676038 24508615 := bstep (se 1 (by rfl) ⟨18381461, by rfl⟩ : syracuseStep 24508615 = 36762923) B36762923
theorem B5372153 : Blo 1676038 5372153 := bstep (se 2 (by rfl) ⟨2014557, by rfl⟩ : syracuseStep 5372153 = 4029115) B4029115
theorem B1677671 : Blo 1676038 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B15300971 : Blo 1676038 15300971 := bstep (se 1 (by rfl) ⟨11475728, by rfl⟩ : syracuseStep 15300971 = 22951457) B22951457
theorem B5101951 : Blo 1676038 5101951 := bstep (se 1 (by rfl) ⟨3826463, by rfl⟩ : syracuseStep 5101951 = 7652927) B7652927
theorem B2267599 : Blo 1676038 2267599 := bstep (se 1 (by rfl) ⟨1700699, by rfl⟩ : syracuseStep 2267599 = 3401399) B3401399
theorem B1677927 : Blo 1676038 1677927 := bstep (se 1 (by rfl) ⟨1258445, by rfl⟩ : syracuseStep 1677927 = 2516891) B2516891
theorem B3775103 : Blo 1676038 3775103 := bstep (se 1 (by rfl) ⟨2831327, by rfl⟩ : syracuseStep 3775103 = 5662655) B5662655
theorem B1677951 : Blo 1676038 1677951 := bstep (se 1 (by rfl) ⟨1258463, by rfl⟩ : syracuseStep 1677951 = 2516927) B2516927
theorem B9190025 : Blo 1676038 9190025 := bstep (se 2 (by rfl) ⟨3446259, by rfl⟩ : syracuseStep 9190025 = 6892519) B6892519
theorem B3775211 : Blo 1676038 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B3021563 : Blo 1676038 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B3775481 : Blo 1676038 3775481 := bstep (se 2 (by rfl) ⟨1415805, by rfl⟩ : syracuseStep 3775481 = 2831611) B2831611
theorem B3775571 : Blo 1676038 3775571 := bstep (se 1 (by rfl) ⟨2831678, by rfl⟩ : syracuseStep 3775571 = 5663357) B5663357
theorem B9550993 : Blo 1676038 9550993 := bstep (se 2 (by rfl) ⟨3581622, by rfl⟩ : syracuseStep 9550993 = 7163245) B7163245
theorem B2514203 : Blo 1676038 2514203 := bstep (se 1 (by rfl) ⟨1885652, by rfl⟩ : syracuseStep 2514203 = 3771305) B3771305
theorem B24165803 : Blo 1676038 24165803 := bstep (se 1 (by rfl) ⟨18124352, by rfl⟩ : syracuseStep 24165803 = 36248705) B36248705
theorem B30596525 : Blo 1676038 30596525 := bstep (se 3 (by rfl) ⟨5736848, by rfl⟩ : syracuseStep 30596525 = 11473697) B11473697
theorem B6798905 : Blo 1676038 6798905 := bstep (se 2 (by rfl) ⟨2549589, by rfl⟩ : syracuseStep 6798905 = 5099179) B5099179
theorem B6364763 : Blo 1676038 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B2514671 : Blo 1676038 2514671 := bstep (se 1 (by rfl) ⟨1886003, by rfl⟩ : syracuseStep 2514671 = 3772007) B3772007
theorem B2514857 : Blo 1676038 2514857 := bstep (se 2 (by rfl) ⟨943071, by rfl⟩ : syracuseStep 2514857 = 1886143) B1886143
theorem B2121967 : Blo 1676038 2121967 := bstep (se 1 (by rfl) ⟨1591475, by rfl⟩ : syracuseStep 2121967 = 3182951) B3182951
theorem B32678153 : Blo 1676038 32678153 := bstep (se 2 (by rfl) ⟨12254307, by rfl⟩ : syracuseStep 32678153 = 24508615) B24508615
theorem B7160375 : Blo 1676038 7160375 := bstep (se 1 (by rfl) ⟨5370281, by rfl⟩ : syracuseStep 7160375 = 10740563) B10740563
theorem B18137681 : Blo 1676038 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B9060947 : Blo 1676038 9060947 := bstep (se 1 (by rfl) ⟨6795710, by rfl⟩ : syracuseStep 9060947 = 13591421) B13591421
theorem B3023465 : Blo 1676038 3023465 := bstep (se 2 (by rfl) ⟨1133799, by rfl⟩ : syracuseStep 3023465 = 2267599) B2267599
theorem B7160633 : Blo 1676038 7160633 := bstep (se 2 (by rfl) ⟨2685237, by rfl⟩ : syracuseStep 7160633 = 5370475) B5370475
theorem B18375581 : Blo 1676038 18375581 := bstep (se 3 (by rfl) ⟨3445421, by rfl⟩ : syracuseStep 18375581 = 6890843) B6890843
theorem B2515919 : Blo 1676038 2515919 := bstep (se 1 (by rfl) ⟨1886939, by rfl⟩ : syracuseStep 2515919 = 3773879) B3773879
theorem B2515967 : Blo 1676038 2515967 := bstep (se 1 (by rfl) ⟨1886975, by rfl⟩ : syracuseStep 2515967 = 3773951) B3773951
theorem B2516039 : Blo 1676038 2516039 := bstep (se 1 (by rfl) ⟨1887029, by rfl⟩ : syracuseStep 2516039 = 3774059) B3774059
theorem B12092591 : Blo 1676038 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B2516219 : Blo 1676038 2516219 := bstep (se 1 (by rfl) ⟨1887164, by rfl⟩ : syracuseStep 2516219 = 3774329) B3774329
theorem B3581435 : Blo 1676038 3581435 := bstep (se 1 (by rfl) ⟨2686076, by rfl⟩ : syracuseStep 3581435 = 5372153) B5372153
theorem B8488475 : Blo 1676038 8488475 := bstep (se 1 (by rfl) ⟨6366356, by rfl⟩ : syracuseStep 8488475 = 12732713) B12732713
theorem B10200647 : Blo 1676038 10200647 := bstep (se 1 (by rfl) ⟨7650485, by rfl⟩ : syracuseStep 10200647 = 15300971) B15300971
theorem B2516735 : Blo 1676038 2516735 := bstep (se 1 (by rfl) ⟨1887551, by rfl⟩ : syracuseStep 2516735 = 3775103) B3775103
theorem B6047551 : Blo 1676038 6047551 := bstep (se 1 (by rfl) ⟨4535663, by rfl⟩ : syracuseStep 6047551 = 9071327) B9071327
theorem B2516807 : Blo 1676038 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B25806721 : Blo 1676038 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B2516987 : Blo 1676038 2516987 := bstep (se 1 (by rfl) ⟨1887740, by rfl⟩ : syracuseStep 2516987 = 3775481) B3775481
theorem B2517047 : Blo 1676038 2517047 := bstep (se 1 (by rfl) ⟨1887785, by rfl⟩ : syracuseStep 2517047 = 3775571) B3775571
theorem B4245767 : Blo 1676038 4245767 := bstep (se 1 (by rfl) ⟨3184325, by rfl⟩ : syracuseStep 4245767 = 6368651) B6368651
theorem B4532603 : Blo 1676038 4532603 := bstep (se 1 (by rfl) ⟨3399452, by rfl⟩ : syracuseStep 4532603 = 6798905) B6798905
theorem B58903109 : Blo 1676038 58903109 := bstep (se 4 (by rfl) ⟨5522166, by rfl⟩ : syracuseStep 58903109 = 11044333) B11044333
theorem B2829019 : Blo 1676038 2829019 := bstep (se 1 (by rfl) ⟨2121764, by rfl⟩ : syracuseStep 2829019 = 4243529) B4243529
theorem B6367997 : Blo 1676038 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B3771143 : Blo 1676038 3771143 := bstep (se 1 (by rfl) ⟨2828357, by rfl⟩ : syracuseStep 3771143 = 5656715) B5656715
theorem B1887079 : Blo 1676038 1887079 := bstep (se 1 (by rfl) ⟨1415309, by rfl⟩ : syracuseStep 1887079 = 2830619) B2830619
theorem B28707965 : Blo 1676038 28707965 := bstep (se 3 (by rfl) ⟨5382743, by rfl⟩ : syracuseStep 28707965 = 10765487) B10765487
theorem B6802601 : Blo 1676038 6802601 := bstep (se 2 (by rfl) ⟨2550975, by rfl⟩ : syracuseStep 6802601 = 5101951) B5101951
theorem B10194173 : Blo 1676038 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B3771881 : Blo 1676038 3771881 := bstep (se 2 (by rfl) ⟨1414455, by rfl⟩ : syracuseStep 3771881 = 2828911) B2828911
theorem B3771935 : Blo 1676038 3771935 := bstep (se 1 (by rfl) ⟨2828951, by rfl⟩ : syracuseStep 3771935 = 5657903) B5657903
theorem B2829991 : Blo 1676038 2829991 := bstep (se 1 (by rfl) ⟨2122493, by rfl⟩ : syracuseStep 2829991 = 4244987) B4244987
theorem B3772169 : Blo 1676038 3772169 := bstep (se 2 (by rfl) ⟨1414563, by rfl⟩ : syracuseStep 3772169 = 2829127) B2829127
theorem B64442141 : Blo 1676038 64442141 := bstep (se 3 (by rfl) ⟨12082901, by rfl⟩ : syracuseStep 64442141 = 24165803) B24165803
theorem B3772223 : Blo 1676038 3772223 := bstep (se 1 (by rfl) ⟨2829167, by rfl⟩ : syracuseStep 3772223 = 5658335) B5658335
theorem B2723647 : Blo 1676038 2723647 := bstep (se 1 (by rfl) ⟨2042735, by rfl⟩ : syracuseStep 2723647 = 4085471) B4085471
theorem B4534139 : Blo 1676038 4534139 := bstep (se 1 (by rfl) ⟨3400604, by rfl⟩ : syracuseStep 4534139 = 6801209) B6801209
theorem B2830207 : Blo 1676038 2830207 := bstep (se 1 (by rfl) ⟨2122655, by rfl⟩ : syracuseStep 2830207 = 4245311) B4245311
theorem B2830457 : Blo 1676038 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B12734657 : Blo 1676038 12734657 := bstep (se 2 (by rfl) ⟨4775496, by rfl⟩ : syracuseStep 12734657 = 9550993) B9550993
theorem B3182905 : Blo 1676038 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B9548351 : Blo 1676038 9548351 := bstep (se 1 (by rfl) ⟨7161263, by rfl⟩ : syracuseStep 9548351 = 14322527) B14322527
theorem B8057501 : Blo 1676038 8057501 := bstep (se 3 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 8057501 = 3021563) B3021563
theorem B13603517 : Blo 1676038 13603517 := bstep (se 3 (by rfl) ⟨2550659, by rfl⟩ : syracuseStep 13603517 = 5101319) B5101319
theorem B2388791 : Blo 1676038 2388791 := bstep (se 1 (by rfl) ⟨1791593, by rfl⟩ : syracuseStep 2388791 = 3583187) B3583187
theorem B1676135 : Blo 1676038 1676135 := bstep (se 1 (by rfl) ⟨1257101, by rfl⟩ : syracuseStep 1676135 = 2514203) B2514203
theorem B353301355 : Blo 1676038 353301355 := bstep (se 1 (by rfl) ⟨264976016, by rfl⟩ : syracuseStep 353301355 = 529952033) B529952033
theorem B104674157 : Blo 1676038 104674157 := bstep (se 3 (by rfl) ⟨19626404, by rfl⟩ : syracuseStep 104674157 = 39252809) B39252809
theorem B1676447 : Blo 1676038 1676447 := bstep (se 1 (by rfl) ⟨1257335, by rfl⟩ : syracuseStep 1676447 = 2514671) B2514671
theorem B1676571 : Blo 1676038 1676571 := bstep (se 1 (by rfl) ⟨1257428, by rfl⟩ : syracuseStep 1676571 = 2514857) B2514857
theorem B1676671 : Blo 1676038 1676671 := bstep (se 1 (by rfl) ⟨1257503, by rfl⟩ : syracuseStep 1676671 = 2515007) B2515007
theorem B1676827 : Blo 1676038 1676827 := bstep (se 1 (by rfl) ⟨1257620, by rfl⟩ : syracuseStep 1676827 = 2515241) B2515241
theorem B5658227 : Blo 1676038 5658227 := bstep (se 1 (by rfl) ⟨4243670, by rfl⟩ : syracuseStep 5658227 = 8487341) B8487341
theorem B1677007 : Blo 1676038 1677007 := bstep (se 1 (by rfl) ⟨1257755, by rfl⟩ : syracuseStep 1677007 = 2515511) B2515511
theorem B314136305 : Blo 1676038 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B1677247 : Blo 1676038 1677247 := bstep (se 1 (by rfl) ⟨1257935, by rfl⟩ : syracuseStep 1677247 = 2515871) B2515871
theorem B3184751 : Blo 1676038 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B1677439 : Blo 1676038 1677439 := bstep (se 1 (by rfl) ⟨1258079, by rfl⟩ : syracuseStep 1677439 = 2516159) B2516159
theorem B1677535 : Blo 1676038 1677535 := bstep (se 1 (by rfl) ⟨1258151, by rfl⟩ : syracuseStep 1677535 = 2516303) B2516303
theorem B1677595 : Blo 1676038 1677595 := bstep (se 1 (by rfl) ⟨1258196, by rfl⟩ : syracuseStep 1677595 = 2516393) B2516393
theorem B1677695 : Blo 1676038 1677695 := bstep (se 1 (by rfl) ⟨1258271, by rfl⟩ : syracuseStep 1677695 = 2516543) B2516543
theorem B12081581 : Blo 1676038 12081581 := bstep (se 3 (by rfl) ⟨2265296, by rfl⟩ : syracuseStep 12081581 = 4530593) B4530593
theorem B3185183 : Blo 1676038 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B1677935 : Blo 1676038 1677935 := bstep (se 1 (by rfl) ⟨1258451, by rfl⟩ : syracuseStep 1677935 = 2516903) B2516903
theorem B5659307 : Blo 1676038 5659307 := bstep (se 1 (by rfl) ⟨4244480, by rfl⟩ : syracuseStep 5659307 = 8488961) B8488961
theorem B1678015 : Blo 1676038 1678015 := bstep (se 1 (by rfl) ⟨1258511, by rfl⟩ : syracuseStep 1678015 = 2517023) B2517023
theorem B12737573 : Blo 1676038 12737573 := bstep (se 4 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 12737573 = 2388295) B2388295
theorem B6126683 : Blo 1676038 6126683 := bstep (se 1 (by rfl) ⟨4595012, by rfl⟩ : syracuseStep 6126683 = 9190025) B9190025
theorem B12082441 : Blo 1676038 12082441 := bstep (se 2 (by rfl) ⟨4530915, by rfl⟩ : syracuseStep 12082441 = 9061831) B9061831
theorem B2514383 : Blo 1676038 2514383 := bstep (se 1 (by rfl) ⟨1885787, by rfl⟩ : syracuseStep 2514383 = 3771575) B3771575
theorem B20397683 : Blo 1676038 20397683 := bstep (se 1 (by rfl) ⟨15298262, by rfl⟩ : syracuseStep 20397683 = 30596525) B30596525
theorem B4243175 : Blo 1676038 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B6365567 : Blo 1676038 6365567 := bstep (se 1 (by rfl) ⟨4774175, by rfl⟩ : syracuseStep 6365567 = 9548351) B9548351
theorem B12091787 : Blo 1676038 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B4243873 : Blo 1676038 4243873 := bstep (se 2 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 4243873 = 3182905) B3182905
theorem B9069011 : Blo 1676038 9069011 := bstep (se 1 (by rfl) ⟨6801758, by rfl⟩ : syracuseStep 9069011 = 13603517) B13603517
theorem B8061727 : Blo 1676038 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B6800431 : Blo 1676038 6800431 := bstep (se 1 (by rfl) ⟨5100323, by rfl⟩ : syracuseStep 6800431 = 10200647) B10200647
theorem B2516105 : Blo 1676038 2516105 := bstep (se 2 (by rfl) ⟨943539, by rfl⟩ : syracuseStep 2516105 = 1887079) B1887079
theorem B2123167 : Blo 1676038 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B8062573 : Blo 1676038 8062573 := bstep (se 3 (by rfl) ⟨1511732, by rfl⟩ : syracuseStep 8062573 = 3023465) B3023465
theorem B8054387 : Blo 1676038 8054387 := bstep (se 1 (by rfl) ⟨6040790, by rfl⟩ : syracuseStep 8054387 = 12081581) B12081581
theorem B4245331 : Blo 1676038 4245331 := bstep (se 1 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 4245331 = 6367997) B6367997
theorem B19138643 : Blo 1676038 19138643 := bstep (se 1 (by rfl) ⟨14353982, by rfl⟩ : syracuseStep 19138643 = 28707965) B28707965
theorem B3631529 : Blo 1676038 3631529 := bstep (se 2 (by rfl) ⟨1361823, by rfl⟩ : syracuseStep 3631529 = 2723647) B2723647
theorem B8063401 : Blo 1676038 8063401 := bstep (se 2 (by rfl) ⟨3023775, by rfl⟩ : syracuseStep 8063401 = 6047551) B6047551
theorem B2828783 : Blo 1676038 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B34408961 : Blo 1676038 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B42961427 : Blo 1676038 42961427 := bstep (se 1 (by rfl) ⟨32221070, by rfl⟩ : syracuseStep 42961427 = 64442141) B64442141
theorem B1886971 : Blo 1676038 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B8489771 : Blo 1676038 8489771 := bstep (se 1 (by rfl) ⟨6367328, by rfl⟩ : syracuseStep 8489771 = 12734657) B12734657
theorem B21785435 : Blo 1676038 21785435 := bstep (se 1 (by rfl) ⟨16339076, by rfl⟩ : syracuseStep 21785435 = 32678153) B32678153
theorem B16337821 : Blo 1676038 16337821 := bstep (se 3 (by rfl) ⟨3063341, by rfl⟩ : syracuseStep 16337821 = 6126683) B6126683
theorem B2829289 : Blo 1676038 2829289 := bstep (se 2 (by rfl) ⟨1060983, by rfl⟩ : syracuseStep 2829289 = 2121967) B2121967
theorem B6040631 : Blo 1676038 6040631 := bstep (se 1 (by rfl) ⟨4530473, by rfl⟩ : syracuseStep 6040631 = 9060947) B9060947
theorem B18140269 : Blo 1676038 18140269 := bstep (se 3 (by rfl) ⟨3401300, by rfl⟩ : syracuseStep 18140269 = 6802601) B6802601
theorem B69782771 : Blo 1676038 69782771 := bstep (se 1 (by rfl) ⟨52337078, by rfl⟩ : syracuseStep 69782771 = 104674157) B104674157
theorem B12250387 : Blo 1676038 12250387 := bstep (se 1 (by rfl) ⟨9187790, by rfl⟩ : syracuseStep 12250387 = 18375581) B18375581
theorem B3772025 : Blo 1676038 3772025 := bstep (se 2 (by rfl) ⟨1414509, by rfl⟩ : syracuseStep 3772025 = 2829019) B2829019
theorem B12086941 : Blo 1676038 12086941 := bstep (se 3 (by rfl) ⟨2266301, by rfl⟩ : syracuseStep 12086941 = 4532603) B4532603
theorem B3772151 : Blo 1676038 3772151 := bstep (se 1 (by rfl) ⟨2829113, by rfl⟩ : syracuseStep 3772151 = 5658227) B5658227
theorem B471068473 : Blo 1676038 471068473 := bstep (se 2 (by rfl) ⟨176650677, by rfl⟩ : syracuseStep 471068473 = 353301355) B353301355
theorem B209424203 : Blo 1676038 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B2830511 : Blo 1676038 2830511 := bstep (se 1 (by rfl) ⟨2122883, by rfl⟩ : syracuseStep 2830511 = 4245767) B4245767
theorem B16109921 : Blo 1676038 16109921 := bstep (se 2 (by rfl) ⟨6041220, by rfl⟩ : syracuseStep 16109921 = 12082441) B12082441
theorem B39268739 : Blo 1676038 39268739 := bstep (se 1 (by rfl) ⟨29451554, by rfl⟩ : syracuseStep 39268739 = 58903109) B58903109
theorem B3772871 : Blo 1676038 3772871 := bstep (se 1 (by rfl) ⟨2829653, by rfl⟩ : syracuseStep 3772871 = 5659307) B5659307
theorem B8491715 : Blo 1676038 8491715 := bstep (se 1 (by rfl) ⟨6368786, by rfl⟩ : syracuseStep 8491715 = 12737573) B12737573
theorem B6370109 : Blo 1676038 6370109 := bstep (se 3 (by rfl) ⟨1194395, by rfl⟩ : syracuseStep 6370109 = 2388791) B2388791
theorem B6796115 : Blo 1676038 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B3773321 : Blo 1676038 3773321 := bstep (se 2 (by rfl) ⟨1414995, by rfl⟩ : syracuseStep 3773321 = 2829991) B2829991
theorem B1676255 : Blo 1676038 1676255 := bstep (se 1 (by rfl) ⟨1257191, by rfl⟩ : syracuseStep 1676255 = 2514383) B2514383
theorem B3773609 : Blo 1676038 3773609 := bstep (se 2 (by rfl) ⟨1415103, by rfl⟩ : syracuseStep 3773609 = 2830207) B2830207
theorem B4773583 : Blo 1676038 4773583 := bstep (se 1 (by rfl) ⟨3580187, by rfl⟩ : syracuseStep 4773583 = 7160375) B7160375
theorem B5371667 : Blo 1676038 5371667 := bstep (se 1 (by rfl) ⟨4028750, by rfl⟩ : syracuseStep 5371667 = 8057501) B8057501
theorem B4773755 : Blo 1676038 4773755 := bstep (se 1 (by rfl) ⟨3580316, by rfl⟩ : syracuseStep 4773755 = 7160633) B7160633
theorem B1677279 : Blo 1676038 1677279 := bstep (se 1 (by rfl) ⟨1257959, by rfl⟩ : syracuseStep 1677279 = 2515919) B2515919
theorem B1677311 : Blo 1676038 1677311 := bstep (se 1 (by rfl) ⟨1257983, by rfl⟩ : syracuseStep 1677311 = 2515967) B2515967
theorem B1677359 : Blo 1676038 1677359 := bstep (se 1 (by rfl) ⟨1258019, by rfl⟩ : syracuseStep 1677359 = 2516039) B2516039
theorem B1677479 : Blo 1676038 1677479 := bstep (se 1 (by rfl) ⟨1258109, by rfl⟩ : syracuseStep 1677479 = 2516219) B2516219
theorem B5658983 : Blo 1676038 5658983 := bstep (se 1 (by rfl) ⟨4244237, by rfl⟩ : syracuseStep 5658983 = 8488475) B8488475
theorem B1677823 : Blo 1676038 1677823 := bstep (se 1 (by rfl) ⟨1258367, by rfl⟩ : syracuseStep 1677823 = 2516735) B2516735
theorem B1677871 : Blo 1676038 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B9550493 : Blo 1676038 9550493 := bstep (se 3 (by rfl) ⟨1790717, by rfl⟩ : syracuseStep 9550493 = 3581435) B3581435
theorem B1677991 : Blo 1676038 1677991 := bstep (se 1 (by rfl) ⟨1258493, by rfl⟩ : syracuseStep 1677991 = 2516987) B2516987
theorem B1678031 : Blo 1676038 1678031 := bstep (se 1 (by rfl) ⟨1258523, by rfl⟩ : syracuseStep 1678031 = 2517047) B2517047
theorem B8493821 : Blo 1676038 8493821 := bstep (se 3 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 8493821 = 3185183) B3185183
theorem B2514095 : Blo 1676038 2514095 := bstep (se 1 (by rfl) ⟨1885571, by rfl⟩ : syracuseStep 2514095 = 3771143) B3771143
theorem B2514587 : Blo 1676038 2514587 := bstep (se 1 (by rfl) ⟨1885940, by rfl⟩ : syracuseStep 2514587 = 3771881) B3771881
theorem B2514623 : Blo 1676038 2514623 := bstep (se 1 (by rfl) ⟨1885967, by rfl⟩ : syracuseStep 2514623 = 3771935) B3771935
theorem B13598455 : Blo 1676038 13598455 := bstep (se 1 (by rfl) ⟨10198841, by rfl⟩ : syracuseStep 13598455 = 20397683) B20397683
theorem B2514779 : Blo 1676038 2514779 := bstep (se 1 (by rfl) ⟨1886084, by rfl⟩ : syracuseStep 2514779 = 3772169) B3772169
theorem B2514815 : Blo 1676038 2514815 := bstep (se 1 (by rfl) ⟨1886111, by rfl⟩ : syracuseStep 2514815 = 3772223) B3772223
theorem B3022759 : Blo 1676038 3022759 := bstep (se 1 (by rfl) ⟨2267069, by rfl⟩ : syracuseStep 3022759 = 4534139) B4534139
theorem B10739947 : Blo 1676038 10739947 := bstep (se 1 (by rfl) ⟨8054960, by rfl⟩ : syracuseStep 10739947 = 16109921) B16109921
theorem B4243711 : Blo 1676038 4243711 := bstep (se 1 (by rfl) ⟨3182783, by rfl⟩ : syracuseStep 4243711 = 6365567) B6365567
theorem B8061191 : Blo 1676038 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B2515247 : Blo 1676038 2515247 := bstep (se 1 (by rfl) ⟨1886435, by rfl⟩ : syracuseStep 2515247 = 3772871) B3772871
theorem B6046007 : Blo 1676038 6046007 := bstep (se 1 (by rfl) ⟨4534505, by rfl⟩ : syracuseStep 6046007 = 9069011) B9069011
theorem B5661143 : Blo 1676038 5661143 := bstep (se 1 (by rfl) ⟨4245857, by rfl⟩ : syracuseStep 5661143 = 8491715) B8491715
theorem B4530743 : Blo 1676038 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B2515547 : Blo 1676038 2515547 := bstep (se 1 (by rfl) ⟨1886660, by rfl⟩ : syracuseStep 2515547 = 3773321) B3773321
theorem B2515739 : Blo 1676038 2515739 := bstep (se 1 (by rfl) ⟨1886804, by rfl⟩ : syracuseStep 2515739 = 3773609) B3773609
theorem B2515961 : Blo 1676038 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B10748969 : Blo 1676038 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B3581111 : Blo 1676038 3581111 := bstep (se 1 (by rfl) ⟨2685833, by rfl⟩ : syracuseStep 3581111 = 5371667) B5371667
theorem B21783761 : Blo 1676038 21783761 := bstep (se 2 (by rfl) ⟨8168910, by rfl⟩ : syracuseStep 21783761 = 16337821) B16337821
theorem B1885855 : Blo 1676038 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B22939307 : Blo 1676038 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B28640951 : Blo 1676038 28640951 := bstep (se 1 (by rfl) ⟨21480713, by rfl⟩ : syracuseStep 28640951 = 42961427) B42961427
theorem B6366995 : Blo 1676038 6366995 := bstep (se 1 (by rfl) ⟨4775246, by rfl⟩ : syracuseStep 6366995 = 9550493) B9550493
theorem B5662547 : Blo 1676038 5662547 := bstep (se 1 (by rfl) ⟨4246910, by rfl⟩ : syracuseStep 5662547 = 8493821) B8493821
theorem B10750097 : Blo 1676038 10750097 := bstep (se 2 (by rfl) ⟨4031286, by rfl⟩ : syracuseStep 10750097 = 8062573) B8062573
theorem B16115921 : Blo 1676038 16115921 := bstep (se 2 (by rfl) ⟨6043470, by rfl⟩ : syracuseStep 16115921 = 12086941) B12086941
theorem B18131273 : Blo 1676038 18131273 := bstep (se 2 (by rfl) ⟨6799227, by rfl⟩ : syracuseStep 18131273 = 13598455) B13598455
theorem B628091297 : Blo 1676038 628091297 := bstep (se 2 (by rfl) ⟨235534236, by rfl⟩ : syracuseStep 628091297 = 471068473) B471068473
theorem B1887007 : Blo 1676038 1887007 := bstep (se 1 (by rfl) ⟨1415255, by rfl⟩ : syracuseStep 1887007 = 2830511) B2830511
theorem B4246739 : Blo 1676038 4246739 := bstep (se 1 (by rfl) ⟨3185054, by rfl⟩ : syracuseStep 4246739 = 6370109) B6370109
theorem B10751201 : Blo 1676038 10751201 := bstep (se 2 (by rfl) ⟨4031700, by rfl⟩ : syracuseStep 10751201 = 8063401) B8063401
theorem B5369591 : Blo 1676038 5369591 := bstep (se 1 (by rfl) ⟨4027193, by rfl⟩ : syracuseStep 5369591 = 8054387) B8054387
theorem B3182503 : Blo 1676038 3182503 := bstep (se 1 (by rfl) ⟨2386877, by rfl⟩ : syracuseStep 3182503 = 4773755) B4773755
theorem B3772385 : Blo 1676038 3772385 := bstep (se 2 (by rfl) ⟨1414644, by rfl⟩ : syracuseStep 3772385 = 2829289) B2829289
theorem B12759095 : Blo 1676038 12759095 := bstep (se 1 (by rfl) ⟨9569321, by rfl⟩ : syracuseStep 12759095 = 19138643) B19138643
theorem B24187025 : Blo 1676038 24187025 := bstep (se 2 (by rfl) ⟨9070134, by rfl⟩ : syracuseStep 24187025 = 18140269) B18140269
theorem B3772655 : Blo 1676038 3772655 := bstep (se 1 (by rfl) ⟨2829491, by rfl⟩ : syracuseStep 3772655 = 5658983) B5658983
theorem B2421019 : Blo 1676038 2421019 := bstep (se 1 (by rfl) ⟨1815764, by rfl⟩ : syracuseStep 2421019 = 3631529) B3631529
theorem B2830889 : Blo 1676038 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B4027087 : Blo 1676038 4027087 := bstep (se 1 (by rfl) ⟨3020315, by rfl⟩ : syracuseStep 4027087 = 6040631) B6040631
theorem B1676063 : Blo 1676038 1676063 := bstep (se 1 (by rfl) ⟨1257047, by rfl⟩ : syracuseStep 1676063 = 2514095) B2514095
theorem B1676391 : Blo 1676038 1676391 := bstep (se 1 (by rfl) ⟨1257293, by rfl⟩ : syracuseStep 1676391 = 2514587) B2514587
theorem B1676415 : Blo 1676038 1676415 := bstep (se 1 (by rfl) ⟨1257311, by rfl⟩ : syracuseStep 1676415 = 2514623) B2514623
theorem B1676519 : Blo 1676038 1676519 := bstep (se 1 (by rfl) ⟨1257389, by rfl⟩ : syracuseStep 1676519 = 2514779) B2514779
theorem B1676543 : Blo 1676038 1676543 := bstep (se 1 (by rfl) ⟨1257407, by rfl⟩ : syracuseStep 1676543 = 2514815) B2514815
theorem B5658497 : Blo 1676038 5658497 := bstep (se 2 (by rfl) ⟨2121936, by rfl⟩ : syracuseStep 5658497 = 4243873) B4243873
theorem B1677403 : Blo 1676038 1677403 := bstep (se 1 (by rfl) ⟨1258052, by rfl⟩ : syracuseStep 1677403 = 2516105) B2516105
theorem B104716637 : Blo 1676038 104716637 := bstep (se 3 (by rfl) ⟨19634369, by rfl⟩ : syracuseStep 104716637 = 39268739) B39268739
theorem B9067241 : Blo 1676038 9067241 := bstep (se 2 (by rfl) ⟨3400215, by rfl⟩ : syracuseStep 9067241 = 6800431) B6800431
theorem B16333849 : Blo 1676038 16333849 := bstep (se 2 (by rfl) ⟨6125193, by rfl⟩ : syracuseStep 16333849 = 12250387) B12250387
theorem B5659847 : Blo 1676038 5659847 := bstep (se 1 (by rfl) ⟨4244885, by rfl⟩ : syracuseStep 5659847 = 8489771) B8489771
theorem B14523623 : Blo 1676038 14523623 := bstep (se 1 (by rfl) ⟨10892717, by rfl⟩ : syracuseStep 14523623 = 21785435) B21785435
theorem B46521847 : Blo 1676038 46521847 := bstep (se 1 (by rfl) ⟨34891385, by rfl⟩ : syracuseStep 46521847 = 69782771) B69782771
theorem B6364777 : Blo 1676038 6364777 := bstep (se 2 (by rfl) ⟨2386791, by rfl⟩ : syracuseStep 6364777 = 4773583) B4773583
theorem B2514683 : Blo 1676038 2514683 := bstep (se 1 (by rfl) ⟨1886012, by rfl⟩ : syracuseStep 2514683 = 3772025) B3772025
theorem B5660441 : Blo 1676038 5660441 := bstep (se 2 (by rfl) ⟨2122665, by rfl⟩ : syracuseStep 5660441 = 4245331) B4245331
theorem B2514767 : Blo 1676038 2514767 := bstep (se 1 (by rfl) ⟨1886075, by rfl⟩ : syracuseStep 2514767 = 3772151) B3772151
theorem B139616135 : Blo 1676038 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B4030345 : Blo 1676038 4030345 := bstep (se 2 (by rfl) ⟨1511379, by rfl⟩ : syracuseStep 4030345 = 3022759) B3022759
theorem B2515103 : Blo 1676038 2515103 := bstep (se 1 (by rfl) ⟨1886327, by rfl⟩ : syracuseStep 2515103 = 3772655) B3772655
theorem B5374127 : Blo 1676038 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B14319929 : Blo 1676038 14319929 := bstep (se 2 (by rfl) ⟨5369973, by rfl⟩ : syracuseStep 14319929 = 10739947) B10739947
theorem B3228025 : Blo 1676038 3228025 := bstep (se 2 (by rfl) ⟨1210509, by rfl⟩ : syracuseStep 3228025 = 2421019) B2421019
theorem B16122685 : Blo 1676038 16122685 := bstep (se 3 (by rfl) ⟨3023003, by rfl⟩ : syracuseStep 16122685 = 6046007) B6046007
theorem B2516009 : Blo 1676038 2516009 := bstep (se 2 (by rfl) ⟨943503, by rfl⟩ : syracuseStep 2516009 = 1887007) B1887007
theorem B4244663 : Blo 1676038 4244663 := bstep (se 1 (by rfl) ⟨3183497, by rfl⟩ : syracuseStep 4244663 = 6366995) B6366995
theorem B418727531 : Blo 1676038 418727531 := bstep (se 1 (by rfl) ⟨314045648, by rfl⟩ : syracuseStep 418727531 = 628091297) B628091297
theorem B8506063 : Blo 1676038 8506063 := bstep (se 1 (by rfl) ⟨6379547, by rfl⟩ : syracuseStep 8506063 = 12759095) B12759095
theorem B16124683 : Blo 1676038 16124683 := bstep (se 1 (by rfl) ⟨12093512, by rfl⟩ : syracuseStep 16124683 = 24187025) B24187025
theorem B1887259 : Blo 1676038 1887259 := bstep (se 1 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 1887259 = 2830889) B2830889
theorem B2387407 : Blo 1676038 2387407 := bstep (se 1 (by rfl) ⟨1790555, by rfl⟩ : syracuseStep 2387407 = 3581111) B3581111
theorem B3772331 : Blo 1676038 3772331 := bstep (se 1 (by rfl) ⟨2829248, by rfl⟩ : syracuseStep 3772331 = 5658497) B5658497
theorem B21778465 : Blo 1676038 21778465 := bstep (se 2 (by rfl) ⟨8166924, by rfl⟩ : syracuseStep 21778465 = 16333849) B16333849
theorem B10743947 : Blo 1676038 10743947 := bstep (se 1 (by rfl) ⟨8057960, by rfl⟩ : syracuseStep 10743947 = 16115921) B16115921
theorem B12087515 : Blo 1676038 12087515 := bstep (se 1 (by rfl) ⟨9065636, by rfl⟩ : syracuseStep 12087515 = 18131273) B18131273
theorem B3773231 : Blo 1676038 3773231 := bstep (se 1 (by rfl) ⟨2829923, by rfl⟩ : syracuseStep 3773231 = 5659847) B5659847
theorem B2831159 : Blo 1676038 2831159 := bstep (se 1 (by rfl) ⟨2123369, by rfl⟩ : syracuseStep 2831159 = 4246739) B4246739
theorem B1676455 : Blo 1676038 1676455 := bstep (se 1 (by rfl) ⟨1257341, by rfl⟩ : syracuseStep 1676455 = 2514683) B2514683
theorem B3773627 : Blo 1676038 3773627 := bstep (se 1 (by rfl) ⟨2830220, by rfl⟩ : syracuseStep 3773627 = 5660441) B5660441
theorem B1676511 : Blo 1676038 1676511 := bstep (se 1 (by rfl) ⟨1257383, by rfl⟩ : syracuseStep 1676511 = 2514767) B2514767
theorem B248116517 : Blo 1676038 248116517 := bstep (se 4 (by rfl) ⟨23260923, by rfl⟩ : syracuseStep 248116517 = 46521847) B46521847
theorem B1676831 : Blo 1676038 1676831 := bstep (se 1 (by rfl) ⟨1257623, by rfl⟩ : syracuseStep 1676831 = 2515247) B2515247
theorem B3774095 : Blo 1676038 3774095 := bstep (se 1 (by rfl) ⟨2830571, by rfl⟩ : syracuseStep 3774095 = 5661143) B5661143
theorem B5658281 : Blo 1676038 5658281 := bstep (se 2 (by rfl) ⟨2121855, by rfl⟩ : syracuseStep 5658281 = 4243711) B4243711
theorem B3020495 : Blo 1676038 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B1677031 : Blo 1676038 1677031 := bstep (se 1 (by rfl) ⟨1257773, by rfl⟩ : syracuseStep 1677031 = 2515547) B2515547
theorem B1677159 : Blo 1676038 1677159 := bstep (se 1 (by rfl) ⟨1257869, by rfl⟩ : syracuseStep 1677159 = 2515739) B2515739
theorem B1677307 : Blo 1676038 1677307 := bstep (se 1 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 1677307 = 2515961) B2515961
theorem B7165979 : Blo 1676038 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B14522507 : Blo 1676038 14522507 := bstep (se 1 (by rfl) ⟨10891880, by rfl⟩ : syracuseStep 14522507 = 21783761) B21783761
theorem B21477797 : Blo 1676038 21477797 := bstep (se 4 (by rfl) ⟨2013543, by rfl⟩ : syracuseStep 21477797 = 4027087) B4027087
theorem B15292871 : Blo 1676038 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B19093967 : Blo 1676038 19093967 := bstep (se 1 (by rfl) ⟨14320475, by rfl⟩ : syracuseStep 19093967 = 28640951) B28640951
theorem B3775031 : Blo 1676038 3775031 := bstep (se 1 (by rfl) ⟨2831273, by rfl⟩ : syracuseStep 3775031 = 5662547) B5662547
theorem B7166731 : Blo 1676038 7166731 := bstep (se 1 (by rfl) ⟨5375048, by rfl⟩ : syracuseStep 7166731 = 10750097) B10750097
theorem B69811091 : Blo 1676038 69811091 := bstep (se 1 (by rfl) ⟨52358318, by rfl⟩ : syracuseStep 69811091 = 104716637) B104716637
theorem B6044827 : Blo 1676038 6044827 := bstep (se 1 (by rfl) ⟨4533620, by rfl⟩ : syracuseStep 6044827 = 9067241) B9067241
theorem B8486369 : Blo 1676038 8486369 := bstep (se 2 (by rfl) ⟨3182388, by rfl⟩ : syracuseStep 8486369 = 6364777) B6364777
theorem B7167467 : Blo 1676038 7167467 := bstep (se 1 (by rfl) ⟨5375600, by rfl⟩ : syracuseStep 7167467 = 10751201) B10751201
theorem B9682415 : Blo 1676038 9682415 := bstep (se 1 (by rfl) ⟨7261811, by rfl⟩ : syracuseStep 9682415 = 14523623) B14523623
theorem B2514473 : Blo 1676038 2514473 := bstep (se 2 (by rfl) ⟨942927, by rfl⟩ : syracuseStep 2514473 = 1885855) B1885855
theorem B3579727 : Blo 1676038 3579727 := bstep (se 1 (by rfl) ⟨2684795, by rfl⟩ : syracuseStep 3579727 = 5369591) B5369591
theorem B5373793 : Blo 1676038 5373793 := bstep (se 2 (by rfl) ⟨2015172, by rfl⟩ : syracuseStep 5373793 = 4030345) B4030345
theorem B4243337 : Blo 1676038 4243337 := bstep (se 2 (by rfl) ⟨1591251, by rfl⟩ : syracuseStep 4243337 = 3182503) B3182503
theorem B93077423 : Blo 1676038 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B2514923 : Blo 1676038 2514923 := bstep (se 1 (by rfl) ⟨1886192, by rfl⟩ : syracuseStep 2514923 = 3772385) B3772385
theorem B2515487 : Blo 1676038 2515487 := bstep (se 1 (by rfl) ⟨1886615, by rfl⟩ : syracuseStep 2515487 = 3773231) B3773231
theorem B2515751 : Blo 1676038 2515751 := bstep (se 1 (by rfl) ⟨1886813, by rfl⟩ : syracuseStep 2515751 = 3773627) B3773627
theorem B279151687 : Blo 1676038 279151687 := bstep (se 1 (by rfl) ⟨209363765, by rfl⟩ : syracuseStep 279151687 = 418727531) B418727531
theorem B21496913 : Blo 1676038 21496913 := bstep (se 2 (by rfl) ⟨8061342, by rfl⟩ : syracuseStep 21496913 = 16122685) B16122685
theorem B2516063 : Blo 1676038 2516063 := bstep (se 1 (by rfl) ⟨1887047, by rfl⟩ : syracuseStep 2516063 = 3774095) B3774095
theorem B4777319 : Blo 1676038 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B2516345 : Blo 1676038 2516345 := bstep (se 2 (by rfl) ⟨943629, by rfl⟩ : syracuseStep 2516345 = 1887259) B1887259
theorem B2516687 : Blo 1676038 2516687 := bstep (se 1 (by rfl) ⟨1887515, by rfl⟩ : syracuseStep 2516687 = 3775031) B3775031
theorem B8054653 : Blo 1676038 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B46540727 : Blo 1676038 46540727 := bstep (se 1 (by rfl) ⟨34905545, by rfl⟩ : syracuseStep 46540727 = 69811091) B69811091
theorem B4778311 : Blo 1676038 4778311 := bstep (se 1 (by rfl) ⟨3583733, by rfl⟩ : syracuseStep 4778311 = 7167467) B7167467
theorem B2828891 : Blo 1676038 2828891 := bstep (se 1 (by rfl) ⟨2121668, by rfl⟩ : syracuseStep 2828891 = 4243337) B4243337
theorem B7162631 : Blo 1676038 7162631 := bstep (se 1 (by rfl) ⟨5371973, by rfl⟩ : syracuseStep 7162631 = 10743947) B10743947
theorem B3582751 : Blo 1676038 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B9546619 : Blo 1676038 9546619 := bstep (se 1 (by rfl) ⟨7159964, by rfl⟩ : syracuseStep 9546619 = 14319929) B14319929
theorem B4304033 : Blo 1676038 4304033 := bstep (se 2 (by rfl) ⟨1614012, by rfl⟩ : syracuseStep 4304033 = 3228025) B3228025
theorem B1887439 : Blo 1676038 1887439 := bstep (se 1 (by rfl) ⟨1415579, by rfl⟩ : syracuseStep 1887439 = 2831159) B2831159
theorem B2829775 : Blo 1676038 2829775 := bstep (se 1 (by rfl) ⟨2122331, by rfl⟩ : syracuseStep 2829775 = 4244663) B4244663
theorem B21499577 : Blo 1676038 21499577 := bstep (se 2 (by rfl) ⟨8062341, by rfl⟩ : syracuseStep 21499577 = 16124683) B16124683
theorem B9555641 : Blo 1676038 9555641 := bstep (se 2 (by rfl) ⟨3583365, by rfl⟩ : syracuseStep 9555641 = 7166731) B7166731
theorem B3772187 : Blo 1676038 3772187 := bstep (se 1 (by rfl) ⟨2829140, by rfl⟩ : syracuseStep 3772187 = 5658281) B5658281
theorem B10195247 : Blo 1676038 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B3183209 : Blo 1676038 3183209 := bstep (se 2 (by rfl) ⟨1193703, by rfl⟩ : syracuseStep 3183209 = 2387407) B2387407
theorem B5657579 : Blo 1676038 5657579 := bstep (se 1 (by rfl) ⟨4243184, by rfl⟩ : syracuseStep 5657579 = 8486369) B8486369
theorem B1676315 : Blo 1676038 1676315 := bstep (se 1 (by rfl) ⟨1257236, by rfl⟩ : syracuseStep 1676315 = 2514473) B2514473
theorem B4772969 : Blo 1676038 4772969 := bstep (se 2 (by rfl) ⟨1789863, by rfl⟩ : syracuseStep 4772969 = 3579727) B3579727
theorem B7165057 : Blo 1676038 7165057 := bstep (se 2 (by rfl) ⟨2686896, by rfl⟩ : syracuseStep 7165057 = 5373793) B5373793
theorem B62051615 : Blo 1676038 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B1676615 : Blo 1676038 1676615 := bstep (se 1 (by rfl) ⟨1257461, by rfl⟩ : syracuseStep 1676615 = 2514923) B2514923
theorem B29037953 : Blo 1676038 29037953 := bstep (se 2 (by rfl) ⟨10889232, by rfl⟩ : syracuseStep 29037953 = 21778465) B21778465
theorem B1676735 : Blo 1676038 1676735 := bstep (se 1 (by rfl) ⟨1257551, by rfl⟩ : syracuseStep 1676735 = 2515103) B2515103
theorem B32233373 : Blo 1676038 32233373 := bstep (se 3 (by rfl) ⟨6043757, by rfl⟩ : syracuseStep 32233373 = 12087515) B12087515
theorem B1677339 : Blo 1676038 1677339 := bstep (se 1 (by rfl) ⟨1258004, by rfl⟩ : syracuseStep 1677339 = 2516009) B2516009
theorem B165411011 : Blo 1676038 165411011 := bstep (se 1 (by rfl) ⟨124058258, by rfl⟩ : syracuseStep 165411011 = 248116517) B248116517
theorem B45365669 : Blo 1676038 45365669 := bstep (se 4 (by rfl) ⟨4253031, by rfl⟩ : syracuseStep 45365669 = 8506063) B8506063
theorem B9681671 : Blo 1676038 9681671 := bstep (se 1 (by rfl) ⟨7261253, by rfl⟩ : syracuseStep 9681671 = 14522507) B14522507
theorem B8059769 : Blo 1676038 8059769 := bstep (se 2 (by rfl) ⟨3022413, by rfl⟩ : syracuseStep 8059769 = 6044827) B6044827
theorem B14318531 : Blo 1676038 14318531 := bstep (se 1 (by rfl) ⟨10738898, by rfl⟩ : syracuseStep 14318531 = 21477797) B21477797
theorem B12729311 : Blo 1676038 12729311 := bstep (se 1 (by rfl) ⟨9546983, by rfl⟩ : syracuseStep 12729311 = 19093967) B19093967
theorem B6454943 : Blo 1676038 6454943 := bstep (se 1 (by rfl) ⟨4841207, by rfl⟩ : syracuseStep 6454943 = 9682415) B9682415
theorem B2514887 : Blo 1676038 2514887 := bstep (se 1 (by rfl) ⟨1886165, by rfl⟩ : syracuseStep 2514887 = 3772331) B3772331
theorem B2122139 : Blo 1676038 2122139 := bstep (se 1 (by rfl) ⟨1591604, by rfl⟩ : syracuseStep 2122139 = 3183209) B3183209
theorem B12739517 : Blo 1676038 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B4777001 : Blo 1676038 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B21488915 : Blo 1676038 21488915 := bstep (se 1 (by rfl) ⟨16116686, by rfl⟩ : syracuseStep 21488915 = 32233373) B32233373
theorem B9553409 : Blo 1676038 9553409 := bstep (se 2 (by rfl) ⟨3582528, by rfl⟩ : syracuseStep 9553409 = 7165057) B7165057
theorem B2516585 : Blo 1676038 2516585 := bstep (se 2 (by rfl) ⟨943719, by rfl⟩ : syracuseStep 2516585 = 1887439) B1887439
theorem B1885927 : Blo 1676038 1885927 := bstep (se 1 (by rfl) ⟨1414445, by rfl⟩ : syracuseStep 1885927 = 2828891) B2828891
theorem B9545687 : Blo 1676038 9545687 := bstep (se 1 (by rfl) ⟨7159265, by rfl⟩ : syracuseStep 9545687 = 14318531) B14318531
theorem B2869355 : Blo 1676038 2869355 := bstep (se 1 (by rfl) ⟨2152016, by rfl⟩ : syracuseStep 2869355 = 4304033) B4304033
theorem B4303295 : Blo 1676038 4303295 := bstep (se 1 (by rfl) ⟨3227471, by rfl⟩ : syracuseStep 4303295 = 6454943) B6454943
theorem B3771719 : Blo 1676038 3771719 := bstep (se 1 (by rfl) ⟨2828789, by rfl⟩ : syracuseStep 3771719 = 5657579) B5657579
theorem B14331275 : Blo 1676038 14331275 := bstep (se 1 (by rfl) ⟨10748456, by rfl⟩ : syracuseStep 14331275 = 21496913) B21496913
theorem B3181979 : Blo 1676038 3181979 := bstep (se 1 (by rfl) ⟨2386484, by rfl⟩ : syracuseStep 3181979 = 4772969) B4772969
theorem B77434541 : Blo 1676038 77434541 := bstep (se 3 (by rfl) ⟨14518976, by rfl⟩ : syracuseStep 77434541 = 29037953) B29037953
theorem B31027151 : Blo 1676038 31027151 := bstep (se 1 (by rfl) ⟨23270363, by rfl⟩ : syracuseStep 31027151 = 46540727) B46540727
theorem B3773033 : Blo 1676038 3773033 := bstep (se 2 (by rfl) ⟨1414887, by rfl⟩ : syracuseStep 3773033 = 2829775) B2829775
theorem B14333051 : Blo 1676038 14333051 := bstep (se 1 (by rfl) ⟨10749788, by rfl⟩ : syracuseStep 14333051 = 21499577) B21499577
theorem B6370427 : Blo 1676038 6370427 := bstep (se 1 (by rfl) ⟨4777820, by rfl⟩ : syracuseStep 6370427 = 9555641) B9555641
theorem B1676591 : Blo 1676038 1676591 := bstep (se 1 (by rfl) ⟨1257443, by rfl⟩ : syracuseStep 1676591 = 2514887) B2514887
theorem B6796831 : Blo 1676038 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1676991 : Blo 1676038 1676991 := bstep (se 1 (by rfl) ⟨1257743, by rfl⟩ : syracuseStep 1676991 = 2515487) B2515487
theorem B6371081 : Blo 1676038 6371081 := bstep (se 2 (by rfl) ⟨2389155, by rfl⟩ : syracuseStep 6371081 = 4778311) B4778311
theorem B441096029 : Blo 1676038 441096029 := bstep (se 3 (by rfl) ⟨82705505, by rfl⟩ : syracuseStep 441096029 = 165411011) B165411011
theorem B1677167 : Blo 1676038 1677167 := bstep (se 1 (by rfl) ⟨1257875, by rfl⟩ : syracuseStep 1677167 = 2515751) B2515751
theorem B1677375 : Blo 1676038 1677375 := bstep (se 1 (by rfl) ⟨1258031, by rfl⟩ : syracuseStep 1677375 = 2516063) B2516063
theorem B41367743 : Blo 1676038 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B1677563 : Blo 1676038 1677563 := bstep (se 1 (by rfl) ⟨1258172, by rfl⟩ : syracuseStep 1677563 = 2516345) B2516345
theorem B1677791 : Blo 1676038 1677791 := bstep (se 1 (by rfl) ⟨1258343, by rfl⟩ : syracuseStep 1677791 = 2516687) B2516687
theorem B12728825 : Blo 1676038 12728825 := bstep (se 2 (by rfl) ⟨4773309, by rfl⟩ : syracuseStep 12728825 = 9546619) B9546619
theorem B372202249 : Blo 1676038 372202249 := bstep (se 2 (by rfl) ⟨139575843, by rfl⟩ : syracuseStep 372202249 = 279151687) B279151687
theorem B30243779 : Blo 1676038 30243779 := bstep (se 1 (by rfl) ⟨22682834, by rfl⟩ : syracuseStep 30243779 = 45365669) B45365669
theorem B4775087 : Blo 1676038 4775087 := bstep (se 1 (by rfl) ⟨3581315, by rfl⟩ : syracuseStep 4775087 = 7162631) B7162631
theorem B6454447 : Blo 1676038 6454447 := bstep (se 1 (by rfl) ⟨4840835, by rfl⟩ : syracuseStep 6454447 = 9681671) B9681671
theorem B5373179 : Blo 1676038 5373179 := bstep (se 1 (by rfl) ⟨4029884, by rfl⟩ : syracuseStep 5373179 = 8059769) B8059769
theorem B8486207 : Blo 1676038 8486207 := bstep (se 1 (by rfl) ⟨6364655, by rfl⟩ : syracuseStep 8486207 = 12729311) B12729311
theorem B10739537 : Blo 1676038 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B2514791 : Blo 1676038 2514791 := bstep (se 1 (by rfl) ⟨1886093, by rfl⟩ : syracuseStep 2514791 = 3772187) B3772187
theorem B7651613 : Blo 1676038 7651613 := bstep (se 3 (by rfl) ⟨1434677, by rfl⟩ : syracuseStep 7651613 = 2869355) B2869355
theorem B2515355 : Blo 1676038 2515355 := bstep (se 1 (by rfl) ⟨1886516, by rfl⟩ : syracuseStep 2515355 = 3773033) B3773033
theorem B34423717 : Blo 1676038 34423717 := bstep (se 4 (by rfl) ⟨3227223, by rfl⟩ : syracuseStep 34423717 = 6454447) B6454447
theorem B2868863 : Blo 1676038 2868863 := bstep (se 1 (by rfl) ⟨2151647, by rfl⟩ : syracuseStep 2868863 = 4303295) B4303295
theorem B20162519 : Blo 1676038 20162519 := bstep (se 1 (by rfl) ⟨15121889, by rfl⟩ : syracuseStep 20162519 = 30243779) B30243779
theorem B9062441 : Blo 1676038 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B3582119 : Blo 1676038 3582119 := bstep (se 1 (by rfl) ⟨2686589, by rfl⟩ : syracuseStep 3582119 = 5373179) B5373179
theorem B9554183 : Blo 1676038 9554183 := bstep (se 1 (by rfl) ⟨7165637, by rfl⟩ : syracuseStep 9554183 = 14331275) B14331275
theorem B9555367 : Blo 1676038 9555367 := bstep (se 1 (by rfl) ⟨7166525, by rfl⟩ : syracuseStep 9555367 = 14333051) B14333051
theorem B4246951 : Blo 1676038 4246951 := bstep (se 1 (by rfl) ⟨3185213, by rfl⟩ : syracuseStep 4246951 = 6370427) B6370427
theorem B6368939 : Blo 1676038 6368939 := bstep (se 1 (by rfl) ⟨4776704, by rfl⟩ : syracuseStep 6368939 = 9553409) B9553409
theorem B4247387 : Blo 1676038 4247387 := bstep (se 1 (by rfl) ⟨3185540, by rfl⟩ : syracuseStep 4247387 = 6371081) B6371081
theorem B294064019 : Blo 1676038 294064019 := bstep (se 1 (by rfl) ⟨220548014, by rfl⟩ : syracuseStep 294064019 = 441096029) B441096029
theorem B27578495 : Blo 1676038 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B3183391 : Blo 1676038 3183391 := bstep (se 1 (by rfl) ⟨2387543, by rfl⟩ : syracuseStep 3183391 = 4775087) B4775087
theorem B5657471 : Blo 1676038 5657471 := bstep (se 1 (by rfl) ⟨4243103, by rfl⟩ : syracuseStep 5657471 = 8486207) B8486207
theorem B51623027 : Blo 1676038 51623027 := bstep (se 1 (by rfl) ⟨38717270, by rfl⟩ : syracuseStep 51623027 = 77434541) B77434541
theorem B1676527 : Blo 1676038 1676527 := bstep (se 1 (by rfl) ⟨1257395, by rfl⟩ : syracuseStep 1676527 = 2514791) B2514791
theorem B8493011 : Blo 1676038 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B3184667 : Blo 1676038 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B14325943 : Blo 1676038 14325943 := bstep (se 1 (by rfl) ⟨10744457, by rfl⟩ : syracuseStep 14325943 = 21488915) B21488915
theorem B496269665 : Blo 1676038 496269665 := bstep (se 2 (by rfl) ⟨186101124, by rfl⟩ : syracuseStep 496269665 = 372202249) B372202249
theorem B1677723 : Blo 1676038 1677723 := bstep (se 1 (by rfl) ⟨1258292, by rfl⟩ : syracuseStep 1677723 = 2516585) B2516585
theorem B5659037 : Blo 1676038 5659037 := bstep (se 3 (by rfl) ⟨1061069, by rfl⟩ : syracuseStep 5659037 = 2122139) B2122139
theorem B6363791 : Blo 1676038 6363791 := bstep (se 1 (by rfl) ⟨4772843, by rfl⟩ : syracuseStep 6363791 = 9545687) B9545687
theorem B8485883 : Blo 1676038 8485883 := bstep (se 1 (by rfl) ⟨6364412, by rfl⟩ : syracuseStep 8485883 = 12728825) B12728825
theorem B2514479 : Blo 1676038 2514479 := bstep (se 1 (by rfl) ⟨1885859, by rfl⟩ : syracuseStep 2514479 = 3771719) B3771719
theorem B2121319 : Blo 1676038 2121319 := bstep (se 1 (by rfl) ⟨1590989, by rfl⟩ : syracuseStep 2121319 = 3181979) B3181979
theorem B2514569 : Blo 1676038 2514569 := bstep (se 2 (by rfl) ⟨942963, by rfl⟩ : syracuseStep 2514569 = 1885927) B1885927
theorem B7159691 : Blo 1676038 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B20684767 : Blo 1676038 20684767 := bstep (se 1 (by rfl) ⟨15513575, by rfl⟩ : syracuseStep 20684767 = 31027151) B31027151
theorem B34415351 : Blo 1676038 34415351 := bstep (se 1 (by rfl) ⟨25811513, by rfl⟩ : syracuseStep 34415351 = 51623027) B51623027
theorem B4244521 : Blo 1676038 4244521 := bstep (se 2 (by rfl) ⟨1591695, by rfl⟩ : syracuseStep 4244521 = 3183391) B3183391
theorem B5662007 : Blo 1676038 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B2123111 : Blo 1676038 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B12740489 : Blo 1676038 12740489 := bstep (se 2 (by rfl) ⟨4777683, by rfl⟩ : syracuseStep 12740489 = 9555367) B9555367
theorem B5662601 : Blo 1676038 5662601 := bstep (se 2 (by rfl) ⟨2123475, by rfl⟩ : syracuseStep 5662601 = 4246951) B4246951
theorem B2828425 : Blo 1676038 2828425 := bstep (se 2 (by rfl) ⟨1060659, by rfl⟩ : syracuseStep 2828425 = 2121319) B2121319
theorem B4245959 : Blo 1676038 4245959 := bstep (se 1 (by rfl) ⟨3184469, by rfl⟩ : syracuseStep 4245959 = 6368939) B6368939
theorem B18385663 : Blo 1676038 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B3771647 : Blo 1676038 3771647 := bstep (se 1 (by rfl) ⟨2828735, by rfl⟩ : syracuseStep 3771647 = 5657471) B5657471
theorem B6041627 : Blo 1676038 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B2388079 : Blo 1676038 2388079 := bstep (se 1 (by rfl) ⟨1791059, by rfl⟩ : syracuseStep 2388079 = 3582119) B3582119
theorem B6369455 : Blo 1676038 6369455 := bstep (se 1 (by rfl) ⟨4777091, by rfl⟩ : syracuseStep 6369455 = 9554183) B9554183
theorem B330846443 : Blo 1676038 330846443 := bstep (se 1 (by rfl) ⟨248134832, by rfl⟩ : syracuseStep 330846443 = 496269665) B496269665
theorem B3772691 : Blo 1676038 3772691 := bstep (se 1 (by rfl) ⟨2829518, by rfl⟩ : syracuseStep 3772691 = 5659037) B5659037
theorem B5657255 : Blo 1676038 5657255 := bstep (se 1 (by rfl) ⟨4242941, by rfl⟩ : syracuseStep 5657255 = 8485883) B8485883
theorem B19092509 : Blo 1676038 19092509 := bstep (se 3 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 19092509 = 7159691) B7159691
theorem B1676319 : Blo 1676038 1676319 := bstep (se 1 (by rfl) ⟨1257239, by rfl⟩ : syracuseStep 1676319 = 2514479) B2514479
theorem B1676379 : Blo 1676038 1676379 := bstep (se 1 (by rfl) ⟨1257284, by rfl⟩ : syracuseStep 1676379 = 2514569) B2514569
theorem B2831591 : Blo 1676038 2831591 := bstep (se 1 (by rfl) ⟨2123693, by rfl⟩ : syracuseStep 2831591 = 4247387) B4247387
theorem B27579689 : Blo 1676038 27579689 := bstep (se 2 (by rfl) ⟨10342383, by rfl⟩ : syracuseStep 27579689 = 20684767) B20684767
theorem B5101075 : Blo 1676038 5101075 := bstep (se 1 (by rfl) ⟨3825806, by rfl⟩ : syracuseStep 5101075 = 7651613) B7651613
theorem B19101257 : Blo 1676038 19101257 := bstep (se 2 (by rfl) ⟨7162971, by rfl⟩ : syracuseStep 19101257 = 14325943) B14325943
theorem B1676903 : Blo 1676038 1676903 := bstep (se 1 (by rfl) ⟨1257677, by rfl⟩ : syracuseStep 1676903 = 2515355) B2515355
theorem B45898289 : Blo 1676038 45898289 := bstep (se 2 (by rfl) ⟨17211858, by rfl⟩ : syracuseStep 45898289 = 34423717) B34423717
theorem B13441679 : Blo 1676038 13441679 := bstep (se 1 (by rfl) ⟨10081259, by rfl⟩ : syracuseStep 13441679 = 20162519) B20162519
theorem B7650301 : Blo 1676038 7650301 := bstep (se 3 (by rfl) ⟨1434431, by rfl⟩ : syracuseStep 7650301 = 2868863) B2868863
theorem B4242527 : Blo 1676038 4242527 := bstep (se 1 (by rfl) ⟨3181895, by rfl⟩ : syracuseStep 4242527 = 6363791) B6363791
theorem B196042679 : Blo 1676038 196042679 := bstep (se 1 (by rfl) ⟨147032009, by rfl⟩ : syracuseStep 196042679 = 294064019) B294064019
theorem B27205733 : Blo 1676038 27205733 := bstep (se 4 (by rfl) ⟨2550537, by rfl⟩ : syracuseStep 27205733 = 5101075) B5101075
theorem B2515127 : Blo 1676038 2515127 := bstep (se 1 (by rfl) ⟨1886345, by rfl⟩ : syracuseStep 2515127 = 3772691) B3772691
theorem B5661629 : Blo 1676038 5661629 := bstep (se 3 (by rfl) ⟨1061555, by rfl⟩ : syracuseStep 5661629 = 2123111) B2123111
theorem B10200401 : Blo 1676038 10200401 := bstep (se 2 (by rfl) ⟨3825150, by rfl⟩ : syracuseStep 10200401 = 7650301) B7650301
theorem B30598859 : Blo 1676038 30598859 := bstep (se 1 (by rfl) ⟨22949144, by rfl⟩ : syracuseStep 30598859 = 45898289) B45898289
theorem B2828351 : Blo 1676038 2828351 := bstep (se 1 (by rfl) ⟨2121263, by rfl⟩ : syracuseStep 2828351 = 4242527) B4242527
theorem B4246303 : Blo 1676038 4246303 := bstep (se 1 (by rfl) ⟨3184727, by rfl⟩ : syracuseStep 4246303 = 6369455) B6369455
theorem B220564295 : Blo 1676038 220564295 := bstep (se 1 (by rfl) ⟨165423221, by rfl⟩ : syracuseStep 220564295 = 330846443) B330846443
theorem B3771233 : Blo 1676038 3771233 := bstep (se 2 (by rfl) ⟨1414212, by rfl⟩ : syracuseStep 3771233 = 2828425) B2828425
theorem B3771503 : Blo 1676038 3771503 := bstep (se 1 (by rfl) ⟨2828627, by rfl⟩ : syracuseStep 3771503 = 5657255) B5657255
theorem B1887727 : Blo 1676038 1887727 := bstep (se 1 (by rfl) ⟨1415795, by rfl⟩ : syracuseStep 1887727 = 2831591) B2831591
theorem B18386459 : Blo 1676038 18386459 := bstep (se 1 (by rfl) ⟨13789844, by rfl⟩ : syracuseStep 18386459 = 27579689) B27579689
theorem B24514217 : Blo 1676038 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B12734171 : Blo 1676038 12734171 := bstep (se 1 (by rfl) ⟨9550628, by rfl⟩ : syracuseStep 12734171 = 19101257) B19101257
theorem B2830639 : Blo 1676038 2830639 := bstep (se 1 (by rfl) ⟨2122979, by rfl⟩ : syracuseStep 2830639 = 4245959) B4245959
theorem B4027751 : Blo 1676038 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B3184105 : Blo 1676038 3184105 := bstep (se 2 (by rfl) ⟨1194039, by rfl⟩ : syracuseStep 3184105 = 2388079) B2388079
theorem B22943567 : Blo 1676038 22943567 := bstep (se 1 (by rfl) ⟨17207675, by rfl⟩ : syracuseStep 22943567 = 34415351) B34415351
theorem B12728339 : Blo 1676038 12728339 := bstep (se 1 (by rfl) ⟨9546254, by rfl⟩ : syracuseStep 12728339 = 19092509) B19092509
theorem B3774671 : Blo 1676038 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B8493659 : Blo 1676038 8493659 := bstep (se 1 (by rfl) ⟨6370244, by rfl⟩ : syracuseStep 8493659 = 12740489) B12740489
theorem B3775067 : Blo 1676038 3775067 := bstep (se 1 (by rfl) ⟨2831300, by rfl⟩ : syracuseStep 3775067 = 5662601) B5662601
theorem B5659361 : Blo 1676038 5659361 := bstep (se 2 (by rfl) ⟨2122260, by rfl⟩ : syracuseStep 5659361 = 4244521) B4244521
theorem B8961119 : Blo 1676038 8961119 := bstep (se 1 (by rfl) ⟨6720839, by rfl⟩ : syracuseStep 8961119 = 13441679) B13441679
theorem B2514431 : Blo 1676038 2514431 := bstep (se 1 (by rfl) ⟨1885823, by rfl⟩ : syracuseStep 2514431 = 3771647) B3771647
theorem B130695119 : Blo 1676038 130695119 := bstep (se 1 (by rfl) ⟨98021339, by rfl⟩ : syracuseStep 130695119 = 196042679) B196042679
theorem B72548621 : Blo 1676038 72548621 := bstep (se 3 (by rfl) ⟨13602866, by rfl⟩ : syracuseStep 72548621 = 27205733) B27205733
theorem B6800267 : Blo 1676038 6800267 := bstep (se 1 (by rfl) ⟨5100200, by rfl⟩ : syracuseStep 6800267 = 10200401) B10200401
theorem B5661737 : Blo 1676038 5661737 := bstep (se 2 (by rfl) ⟨2123151, by rfl⟩ : syracuseStep 5661737 = 4246303) B4246303
theorem B20399239 : Blo 1676038 20399239 := bstep (se 1 (by rfl) ⟨15299429, by rfl⟩ : syracuseStep 20399239 = 30598859) B30598859
theorem B15295711 : Blo 1676038 15295711 := bstep (se 1 (by rfl) ⟨11471783, by rfl⟩ : syracuseStep 15295711 = 22943567) B22943567
theorem B1885567 : Blo 1676038 1885567 := bstep (se 1 (by rfl) ⟨1414175, by rfl⟩ : syracuseStep 1885567 = 2828351) B2828351
theorem B2516447 : Blo 1676038 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B5662439 : Blo 1676038 5662439 := bstep (se 1 (by rfl) ⟨4246829, by rfl⟩ : syracuseStep 5662439 = 8493659) B8493659
theorem B2516711 : Blo 1676038 2516711 := bstep (se 1 (by rfl) ⟨1887533, by rfl⟩ : syracuseStep 2516711 = 3775067) B3775067
theorem B4245473 : Blo 1676038 4245473 := bstep (se 2 (by rfl) ⟨1592052, by rfl⟩ : syracuseStep 4245473 = 3184105) B3184105
theorem B2516969 : Blo 1676038 2516969 := bstep (se 2 (by rfl) ⟨943863, by rfl⟩ : syracuseStep 2516969 = 1887727) B1887727
theorem B5974079 : Blo 1676038 5974079 := bstep (se 1 (by rfl) ⟨4480559, by rfl⟩ : syracuseStep 5974079 = 8961119) B8961119
theorem B12257639 : Blo 1676038 12257639 := bstep (se 1 (by rfl) ⟨9193229, by rfl⟩ : syracuseStep 12257639 = 18386459) B18386459
theorem B8489447 : Blo 1676038 8489447 := bstep (se 1 (by rfl) ⟨6367085, by rfl⟩ : syracuseStep 8489447 = 12734171) B12734171
theorem B3772907 : Blo 1676038 3772907 := bstep (se 1 (by rfl) ⟨2829680, by rfl⟩ : syracuseStep 3772907 = 5659361) B5659361
theorem B147042863 : Blo 1676038 147042863 := bstep (se 1 (by rfl) ⟨110282147, by rfl⟩ : syracuseStep 147042863 = 220564295) B220564295
theorem B1676287 : Blo 1676038 1676287 := bstep (se 1 (by rfl) ⟨1257215, by rfl⟩ : syracuseStep 1676287 = 2514431) B2514431
theorem B1676751 : Blo 1676038 1676751 := bstep (se 1 (by rfl) ⟨1257563, by rfl⟩ : syracuseStep 1676751 = 2515127) B2515127
theorem B3774185 : Blo 1676038 3774185 := bstep (se 2 (by rfl) ⟨1415319, by rfl⟩ : syracuseStep 3774185 = 2830639) B2830639
theorem B3774419 : Blo 1676038 3774419 := bstep (se 1 (by rfl) ⟨2830814, by rfl⟩ : syracuseStep 3774419 = 5661629) B5661629
theorem B2685167 : Blo 1676038 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B8485559 : Blo 1676038 8485559 := bstep (se 1 (by rfl) ⟨6364169, by rfl⟩ : syracuseStep 8485559 = 12728339) B12728339
theorem B2514155 : Blo 1676038 2514155 := bstep (se 1 (by rfl) ⟨1885616, by rfl⟩ : syracuseStep 2514155 = 3771233) B3771233
theorem B2514335 : Blo 1676038 2514335 := bstep (se 1 (by rfl) ⟨1885751, by rfl⟩ : syracuseStep 2514335 = 3771503) B3771503
theorem B16342811 : Blo 1676038 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B87130079 : Blo 1676038 87130079 := bstep (se 1 (by rfl) ⟨65347559, by rfl⟩ : syracuseStep 87130079 = 130695119) B130695119
theorem B48365747 : Blo 1676038 48365747 := bstep (se 1 (by rfl) ⟨36274310, by rfl⟩ : syracuseStep 48365747 = 72548621) B72548621
theorem B2515271 : Blo 1676038 2515271 := bstep (se 1 (by rfl) ⟨1886453, by rfl⟩ : syracuseStep 2515271 = 3772907) B3772907
theorem B2516123 : Blo 1676038 2516123 := bstep (se 1 (by rfl) ⟨1887092, by rfl⟩ : syracuseStep 2516123 = 3774185) B3774185
theorem B2516279 : Blo 1676038 2516279 := bstep (se 1 (by rfl) ⟨1887209, by rfl⟩ : syracuseStep 2516279 = 3774419) B3774419
theorem B27198985 : Blo 1676038 27198985 := bstep (se 2 (by rfl) ⟨10199619, by rfl⟩ : syracuseStep 27198985 = 20399239) B20399239
theorem B98028575 : Blo 1676038 98028575 := bstep (se 1 (by rfl) ⟨73521431, by rfl⟩ : syracuseStep 98028575 = 147042863) B147042863
theorem B4533511 : Blo 1676038 4533511 := bstep (se 1 (by rfl) ⟨3400133, by rfl⟩ : syracuseStep 4533511 = 6800267) B6800267
theorem B2830315 : Blo 1676038 2830315 := bstep (se 1 (by rfl) ⟨2122736, by rfl⟩ : syracuseStep 2830315 = 4245473) B4245473
theorem B1790111 : Blo 1676038 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B8171759 : Blo 1676038 8171759 := bstep (se 1 (by rfl) ⟨6128819, by rfl⟩ : syracuseStep 8171759 = 12257639) B12257639
theorem B20394281 : Blo 1676038 20394281 := bstep (se 2 (by rfl) ⟨7647855, by rfl⟩ : syracuseStep 20394281 = 15295711) B15295711
theorem B5657039 : Blo 1676038 5657039 := bstep (se 1 (by rfl) ⟨4242779, by rfl⟩ : syracuseStep 5657039 = 8485559) B8485559
theorem B1676103 : Blo 1676038 1676103 := bstep (se 1 (by rfl) ⟨1257077, by rfl⟩ : syracuseStep 1676103 = 2514155) B2514155
theorem B1676223 : Blo 1676038 1676223 := bstep (se 1 (by rfl) ⟨1257167, by rfl⟩ : syracuseStep 1676223 = 2514335) B2514335
theorem B58086719 : Blo 1676038 58086719 := bstep (se 1 (by rfl) ⟨43565039, by rfl⟩ : syracuseStep 58086719 = 87130079) B87130079
theorem B63723509 : Blo 1676038 63723509 := bstep (se 5 (by rfl) ⟨2987039, by rfl⟩ : syracuseStep 63723509 = 5974079) B5974079
theorem B3774491 : Blo 1676038 3774491 := bstep (se 1 (by rfl) ⟨2830868, by rfl⟩ : syracuseStep 3774491 = 5661737) B5661737
theorem B1677631 : Blo 1676038 1677631 := bstep (se 1 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 1677631 = 2516447) B2516447
theorem B3774959 : Blo 1676038 3774959 := bstep (se 1 (by rfl) ⟨2831219, by rfl⟩ : syracuseStep 3774959 = 5662439) B5662439
theorem B1677807 : Blo 1676038 1677807 := bstep (se 1 (by rfl) ⟨1258355, by rfl⟩ : syracuseStep 1677807 = 2516711) B2516711
theorem B1677979 : Blo 1676038 1677979 := bstep (se 1 (by rfl) ⟨1258484, by rfl⟩ : syracuseStep 1677979 = 2516969) B2516969
theorem B5659631 : Blo 1676038 5659631 := bstep (se 1 (by rfl) ⟨4244723, by rfl⟩ : syracuseStep 5659631 = 8489447) B8489447
theorem B2514089 : Blo 1676038 2514089 := bstep (se 2 (by rfl) ⟨942783, by rfl⟩ : syracuseStep 2514089 = 1885567) B1885567
theorem B10895207 : Blo 1676038 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B32243831 : Blo 1676038 32243831 := bstep (se 1 (by rfl) ⟨24182873, by rfl⟩ : syracuseStep 32243831 = 48365747) B48365747
theorem B5447839 : Blo 1676038 5447839 := bstep (se 1 (by rfl) ⟨4085879, by rfl⟩ : syracuseStep 5447839 = 8171759) B8171759
theorem B38724479 : Blo 1676038 38724479 := bstep (se 1 (by rfl) ⟨29043359, by rfl⟩ : syracuseStep 38724479 = 58086719) B58086719
theorem B2516327 : Blo 1676038 2516327 := bstep (se 1 (by rfl) ⟨1887245, by rfl⟩ : syracuseStep 2516327 = 3774491) B3774491
theorem B2516639 : Blo 1676038 2516639 := bstep (se 1 (by rfl) ⟨1887479, by rfl⟩ : syracuseStep 2516639 = 3774959) B3774959
theorem B3771359 : Blo 1676038 3771359 := bstep (se 1 (by rfl) ⟨2828519, by rfl⟩ : syracuseStep 3771359 = 5657039) B5657039
theorem B3773087 : Blo 1676038 3773087 := bstep (se 1 (by rfl) ⟨2829815, by rfl⟩ : syracuseStep 3773087 = 5659631) B5659631
theorem B65352383 : Blo 1676038 65352383 := bstep (se 1 (by rfl) ⟨49014287, by rfl⟩ : syracuseStep 65352383 = 98028575) B98028575
theorem B1676059 : Blo 1676038 1676059 := bstep (se 1 (by rfl) ⟨1257044, by rfl⟩ : syracuseStep 1676059 = 2514089) B2514089
theorem B29053885 : Blo 1676038 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B3773753 : Blo 1676038 3773753 := bstep (se 2 (by rfl) ⟨1415157, by rfl⟩ : syracuseStep 3773753 = 2830315) B2830315
theorem B13596187 : Blo 1676038 13596187 := bstep (se 1 (by rfl) ⟨10197140, by rfl⟩ : syracuseStep 13596187 = 20394281) B20394281
theorem B1676847 : Blo 1676038 1676847 := bstep (se 1 (by rfl) ⟨1257635, by rfl⟩ : syracuseStep 1676847 = 2515271) B2515271
theorem B4773629 : Blo 1676038 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B1677415 : Blo 1676038 1677415 := bstep (se 1 (by rfl) ⟨1258061, by rfl⟩ : syracuseStep 1677415 = 2516123) B2516123
theorem B1677519 : Blo 1676038 1677519 := bstep (se 1 (by rfl) ⟨1258139, by rfl⟩ : syracuseStep 1677519 = 2516279) B2516279
theorem B42482339 : Blo 1676038 42482339 := bstep (se 1 (by rfl) ⟨31861754, by rfl⟩ : syracuseStep 42482339 = 63723509) B63723509
theorem B6044681 : Blo 1676038 6044681 := bstep (se 2 (by rfl) ⟨2266755, by rfl⟩ : syracuseStep 6044681 = 4533511) B4533511
theorem B36265313 : Blo 1676038 36265313 := bstep (se 2 (by rfl) ⟨13599492, by rfl⟩ : syracuseStep 36265313 = 27198985) B27198985
theorem B21495887 : Blo 1676038 21495887 := bstep (se 1 (by rfl) ⟨16121915, by rfl⟩ : syracuseStep 21495887 = 32243831) B32243831
theorem B2515391 : Blo 1676038 2515391 := bstep (se 1 (by rfl) ⟨1886543, by rfl⟩ : syracuseStep 2515391 = 3773087) B3773087
theorem B2515835 : Blo 1676038 2515835 := bstep (se 1 (by rfl) ⟨1886876, by rfl⟩ : syracuseStep 2515835 = 3773753) B3773753
theorem B28321559 : Blo 1676038 28321559 := bstep (se 1 (by rfl) ⟨21241169, by rfl⟩ : syracuseStep 28321559 = 42482339) B42482339
theorem B24176875 : Blo 1676038 24176875 := bstep (se 1 (by rfl) ⟨18132656, by rfl⟩ : syracuseStep 24176875 = 36265313) B36265313
theorem B43568255 : Blo 1676038 43568255 := bstep (se 1 (by rfl) ⟨32676191, by rfl⟩ : syracuseStep 43568255 = 65352383) B65352383
theorem B25816319 : Blo 1676038 25816319 := bstep (se 1 (by rfl) ⟨19362239, by rfl⟩ : syracuseStep 25816319 = 38724479) B38724479
theorem B3182419 : Blo 1676038 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B7263785 : Blo 1676038 7263785 := bstep (se 2 (by rfl) ⟨2723919, by rfl⟩ : syracuseStep 7263785 = 5447839) B5447839
theorem B1677551 : Blo 1676038 1677551 := bstep (se 1 (by rfl) ⟨1258163, by rfl⟩ : syracuseStep 1677551 = 2516327) B2516327
theorem B1677759 : Blo 1676038 1677759 := bstep (se 1 (by rfl) ⟨1258319, by rfl⟩ : syracuseStep 1677759 = 2516639) B2516639
theorem B38738513 : Blo 1676038 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B2514239 : Blo 1676038 2514239 := bstep (se 1 (by rfl) ⟨1885679, by rfl⟩ : syracuseStep 2514239 = 3771359) B3771359
theorem B4029787 : Blo 1676038 4029787 := bstep (se 1 (by rfl) ⟨3022340, by rfl⟩ : syracuseStep 4029787 = 6044681) B6044681
theorem B18128249 : Blo 1676038 18128249 := bstep (se 2 (by rfl) ⟨6798093, by rfl⟩ : syracuseStep 18128249 = 13596187) B13596187
theorem B32235833 : Blo 1676038 32235833 := bstep (se 2 (by rfl) ⟨12088437, by rfl⟩ : syracuseStep 32235833 = 24176875) B24176875
theorem B4842523 : Blo 1676038 4842523 := bstep (se 1 (by rfl) ⟨3631892, by rfl⟩ : syracuseStep 4842523 = 7263785) B7263785
theorem B12085499 : Blo 1676038 12085499 := bstep (se 1 (by rfl) ⟨9064124, by rfl⟩ : syracuseStep 12085499 = 18128249) B18128249
theorem B14330591 : Blo 1676038 14330591 := bstep (se 1 (by rfl) ⟨10747943, by rfl⟩ : syracuseStep 14330591 = 21495887) B21495887
theorem B25825675 : Blo 1676038 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B29045503 : Blo 1676038 29045503 := bstep (se 1 (by rfl) ⟨21784127, by rfl⟩ : syracuseStep 29045503 = 43568255) B43568255
theorem B1676159 : Blo 1676038 1676159 := bstep (se 1 (by rfl) ⟨1257119, by rfl⟩ : syracuseStep 1676159 = 2514239) B2514239
theorem B1676927 : Blo 1676038 1676927 := bstep (se 1 (by rfl) ⟨1257695, by rfl⟩ : syracuseStep 1676927 = 2515391) B2515391
theorem B1677223 : Blo 1676038 1677223 := bstep (se 1 (by rfl) ⟨1257917, by rfl⟩ : syracuseStep 1677223 = 2515835) B2515835
theorem B18881039 : Blo 1676038 18881039 := bstep (se 1 (by rfl) ⟨14160779, by rfl⟩ : syracuseStep 18881039 = 28321559) B28321559
theorem B5373049 : Blo 1676038 5373049 := bstep (se 2 (by rfl) ⟨2014893, by rfl⟩ : syracuseStep 5373049 = 4029787) B4029787
theorem B17210879 : Blo 1676038 17210879 := bstep (se 1 (by rfl) ⟨12908159, by rfl⟩ : syracuseStep 17210879 = 25816319) B25816319
theorem B4243225 : Blo 1676038 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B9553727 : Blo 1676038 9553727 := bstep (se 1 (by rfl) ⟨7165295, by rfl⟩ : syracuseStep 9553727 = 14330591) B14330591
theorem B21490555 : Blo 1676038 21490555 := bstep (se 1 (by rfl) ⟨16117916, by rfl⟩ : syracuseStep 21490555 = 32235833) B32235833
theorem B34434233 : Blo 1676038 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B38727337 : Blo 1676038 38727337 := bstep (se 2 (by rfl) ⟨14522751, by rfl⟩ : syracuseStep 38727337 = 29045503) B29045503
theorem B7164065 : Blo 1676038 7164065 := bstep (se 2 (by rfl) ⟨2686524, by rfl⟩ : syracuseStep 7164065 = 5373049) B5373049
theorem B8056999 : Blo 1676038 8056999 := bstep (se 1 (by rfl) ⟨6042749, by rfl⟩ : syracuseStep 8056999 = 12085499) B12085499
theorem B12587359 : Blo 1676038 12587359 := bstep (se 1 (by rfl) ⟨9440519, by rfl⟩ : syracuseStep 12587359 = 18881039) B18881039
theorem B11473919 : Blo 1676038 11473919 := bstep (se 1 (by rfl) ⟨8605439, by rfl⟩ : syracuseStep 11473919 = 17210879) B17210879
theorem B5657633 : Blo 1676038 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B25826789 : Blo 1676038 25826789 := bstep (se 4 (by rfl) ⟨2421261, by rfl⟩ : syracuseStep 25826789 = 4842523) B4842523
theorem B19104173 : Blo 1676038 19104173 := bstep (se 3 (by rfl) ⟨3582032, by rfl⟩ : syracuseStep 19104173 = 7164065) B7164065
theorem B22956155 : Blo 1676038 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B51636449 : Blo 1676038 51636449 := bstep (se 2 (by rfl) ⟨19363668, by rfl⟩ : syracuseStep 51636449 = 38727337) B38727337
theorem B10742665 : Blo 1676038 10742665 := bstep (se 2 (by rfl) ⟨4028499, by rfl⟩ : syracuseStep 10742665 = 8056999) B8056999
theorem B3771755 : Blo 1676038 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B6369151 : Blo 1676038 6369151 := bstep (se 1 (by rfl) ⟨4776863, by rfl⟩ : syracuseStep 6369151 = 9553727) B9553727
theorem B16783145 : Blo 1676038 16783145 := bstep (se 2 (by rfl) ⟨6293679, by rfl⟩ : syracuseStep 16783145 = 12587359) B12587359
theorem B7649279 : Blo 1676038 7649279 := bstep (se 1 (by rfl) ⟨5736959, by rfl⟩ : syracuseStep 7649279 = 11473919) B11473919
theorem B17217859 : Blo 1676038 17217859 := bstep (se 1 (by rfl) ⟨12913394, by rfl⟩ : syracuseStep 17217859 = 25826789) B25826789
theorem B28654073 : Blo 1676038 28654073 := bstep (se 2 (by rfl) ⟨10745277, by rfl⟩ : syracuseStep 28654073 = 21490555) B21490555
theorem B15304103 : Blo 1676038 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B34424299 : Blo 1676038 34424299 := bstep (se 1 (by rfl) ⟨25818224, by rfl⟩ : syracuseStep 34424299 = 51636449) B51636449
theorem B22957145 : Blo 1676038 22957145 := bstep (se 2 (by rfl) ⟨8608929, by rfl⟩ : syracuseStep 22957145 = 17217859) B17217859
theorem B14323553 : Blo 1676038 14323553 := bstep (se 2 (by rfl) ⟨5371332, by rfl⟩ : syracuseStep 14323553 = 10742665) B10742665
theorem B5099519 : Blo 1676038 5099519 := bstep (se 1 (by rfl) ⟨3824639, by rfl⟩ : syracuseStep 5099519 = 7649279) B7649279
theorem B8492201 : Blo 1676038 8492201 := bstep (se 2 (by rfl) ⟨3184575, by rfl⟩ : syracuseStep 8492201 = 6369151) B6369151
theorem B12736115 : Blo 1676038 12736115 := bstep (se 1 (by rfl) ⟨9552086, by rfl⟩ : syracuseStep 12736115 = 19104173) B19104173
theorem B11188763 : Blo 1676038 11188763 := bstep (se 1 (by rfl) ⟨8391572, by rfl⟩ : syracuseStep 11188763 = 16783145) B16783145
theorem B19102715 : Blo 1676038 19102715 := bstep (se 1 (by rfl) ⟨14327036, by rfl⟩ : syracuseStep 19102715 = 28654073) B28654073
theorem B2514503 : Blo 1676038 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B5661467 : Blo 1676038 5661467 := bstep (se 1 (by rfl) ⟨4246100, by rfl⟩ : syracuseStep 5661467 = 8492201) B8492201
theorem B15304763 : Blo 1676038 15304763 := bstep (se 1 (by rfl) ⟨11478572, by rfl⟩ : syracuseStep 15304763 = 22957145) B22957145
theorem B10202735 : Blo 1676038 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B8490743 : Blo 1676038 8490743 := bstep (se 1 (by rfl) ⟨6368057, by rfl⟩ : syracuseStep 8490743 = 12736115) B12736115
theorem B7459175 : Blo 1676038 7459175 := bstep (se 1 (by rfl) ⟨5594381, by rfl⟩ : syracuseStep 7459175 = 11188763) B11188763
theorem B12735143 : Blo 1676038 12735143 := bstep (se 1 (by rfl) ⟨9551357, by rfl⟩ : syracuseStep 12735143 = 19102715) B19102715
theorem B1676335 : Blo 1676038 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B9549035 : Blo 1676038 9549035 := bstep (se 1 (by rfl) ⟨7161776, by rfl⟩ : syracuseStep 9549035 = 14323553) B14323553
theorem B45899065 : Blo 1676038 45899065 := bstep (se 2 (by rfl) ⟨17212149, by rfl⟩ : syracuseStep 45899065 = 34424299) B34424299
theorem B3399679 : Blo 1676038 3399679 := bstep (se 1 (by rfl) ⟨2549759, by rfl⟩ : syracuseStep 3399679 = 5099519) B5099519
theorem B4972783 : Blo 1676038 4972783 := bstep (se 1 (by rfl) ⟨3729587, by rfl⟩ : syracuseStep 4972783 = 7459175) B7459175
theorem B6366023 : Blo 1676038 6366023 := bstep (se 1 (by rfl) ⟨4774517, by rfl⟩ : syracuseStep 6366023 = 9549035) B9549035
theorem B6801823 : Blo 1676038 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B4532905 : Blo 1676038 4532905 := bstep (se 2 (by rfl) ⟨1699839, by rfl⟩ : syracuseStep 4532905 = 3399679) B3399679
theorem B8490095 : Blo 1676038 8490095 := bstep (se 1 (by rfl) ⟨6367571, by rfl⟩ : syracuseStep 8490095 = 12735143) B12735143
theorem B10203175 : Blo 1676038 10203175 := bstep (se 1 (by rfl) ⟨7652381, by rfl⟩ : syracuseStep 10203175 = 15304763) B15304763
theorem B61198753 : Blo 1676038 61198753 := bstep (se 2 (by rfl) ⟨22949532, by rfl⟩ : syracuseStep 61198753 = 45899065) B45899065
theorem B3774311 : Blo 1676038 3774311 := bstep (se 1 (by rfl) ⟨2830733, by rfl⟩ : syracuseStep 3774311 = 5661467) B5661467
theorem B5660495 : Blo 1676038 5660495 := bstep (se 1 (by rfl) ⟨4245371, by rfl⟩ : syracuseStep 5660495 = 8490743) B8490743
theorem B9069097 : Blo 1676038 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B4244015 : Blo 1676038 4244015 := bstep (se 1 (by rfl) ⟨3183011, by rfl⟩ : syracuseStep 4244015 = 6366023) B6366023
theorem B24175493 : Blo 1676038 24175493 := bstep (se 4 (by rfl) ⟨2266452, by rfl⟩ : syracuseStep 24175493 = 4532905) B4532905
theorem B2516207 : Blo 1676038 2516207 := bstep (se 1 (by rfl) ⟨1887155, by rfl⟩ : syracuseStep 2516207 = 3774311) B3774311
theorem B3773663 : Blo 1676038 3773663 := bstep (se 1 (by rfl) ⟨2830247, by rfl⟩ : syracuseStep 3773663 = 5660495) B5660495
theorem B54416933 : Blo 1676038 54416933 := bstep (se 4 (by rfl) ⟨5101587, by rfl⟩ : syracuseStep 54416933 = 10203175) B10203175
theorem B81598337 : Blo 1676038 81598337 := bstep (se 2 (by rfl) ⟨30599376, by rfl⟩ : syracuseStep 81598337 = 61198753) B61198753
theorem B5660063 : Blo 1676038 5660063 := bstep (se 1 (by rfl) ⟨4245047, by rfl⟩ : syracuseStep 5660063 = 8490095) B8490095
theorem B106086037 : Blo 1676038 106086037 := bstep (se 6 (by rfl) ⟨2486391, by rfl⟩ : syracuseStep 106086037 = 4972783) B4972783
theorem B12092129 : Blo 1676038 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B2515775 : Blo 1676038 2515775 := bstep (se 1 (by rfl) ⟨1886831, by rfl⟩ : syracuseStep 2515775 = 3773663) B3773663
theorem B2829343 : Blo 1676038 2829343 := bstep (se 1 (by rfl) ⟨2122007, by rfl⟩ : syracuseStep 2829343 = 4244015) B4244015
theorem B16116995 : Blo 1676038 16116995 := bstep (se 1 (by rfl) ⟨12087746, by rfl⟩ : syracuseStep 16116995 = 24175493) B24175493
theorem B36277955 : Blo 1676038 36277955 := bstep (se 1 (by rfl) ⟨27208466, by rfl⟩ : syracuseStep 36277955 = 54416933) B54416933
theorem B54398891 : Blo 1676038 54398891 := bstep (se 1 (by rfl) ⟨40799168, by rfl⟩ : syracuseStep 54398891 = 81598337) B81598337
theorem B141448049 : Blo 1676038 141448049 := bstep (se 2 (by rfl) ⟨53043018, by rfl⟩ : syracuseStep 141448049 = 106086037) B106086037
theorem B3773375 : Blo 1676038 3773375 := bstep (se 1 (by rfl) ⟨2830031, by rfl⟩ : syracuseStep 3773375 = 5660063) B5660063
theorem B1677471 : Blo 1676038 1677471 := bstep (se 1 (by rfl) ⟨1258103, by rfl⟩ : syracuseStep 1677471 = 2516207) B2516207
theorem B8061419 : Blo 1676038 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B94298699 : Blo 1676038 94298699 := bstep (se 1 (by rfl) ⟨70724024, by rfl⟩ : syracuseStep 94298699 = 141448049) B141448049
theorem B2515583 : Blo 1676038 2515583 := bstep (se 1 (by rfl) ⟨1886687, by rfl⟩ : syracuseStep 2515583 = 3773375) B3773375
theorem B24185303 : Blo 1676038 24185303 := bstep (se 1 (by rfl) ⟨18138977, by rfl⟩ : syracuseStep 24185303 = 36277955) B36277955
theorem B3772457 : Blo 1676038 3772457 := bstep (se 2 (by rfl) ⟨1414671, by rfl⟩ : syracuseStep 3772457 = 2829343) B2829343
theorem B10744663 : Blo 1676038 10744663 := bstep (se 1 (by rfl) ⟨8058497, by rfl⟩ : syracuseStep 10744663 = 16116995) B16116995
theorem B1677183 : Blo 1676038 1677183 := bstep (se 1 (by rfl) ⟨1257887, by rfl⟩ : syracuseStep 1677183 = 2515775) B2515775
theorem B36265927 : Blo 1676038 36265927 := bstep (se 1 (by rfl) ⟨27199445, by rfl⟩ : syracuseStep 36265927 = 54398891) B54398891
theorem B2514971 : Blo 1676038 2514971 := bstep (se 1 (by rfl) ⟨1886228, by rfl⟩ : syracuseStep 2514971 = 3772457) B3772457
theorem B5374279 : Blo 1676038 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B251463197 : Blo 1676038 251463197 := bstep (se 3 (by rfl) ⟨47149349, by rfl⟩ : syracuseStep 251463197 = 94298699) B94298699
theorem B16123535 : Blo 1676038 16123535 := bstep (se 1 (by rfl) ⟨12092651, by rfl⟩ : syracuseStep 16123535 = 24185303) B24185303
theorem B48354569 : Blo 1676038 48354569 := bstep (se 2 (by rfl) ⟨18132963, by rfl⟩ : syracuseStep 48354569 = 36265927) B36265927
theorem B1677055 : Blo 1676038 1677055 := bstep (se 1 (by rfl) ⟨1257791, by rfl⟩ : syracuseStep 1677055 = 2515583) B2515583
theorem B14326217 : Blo 1676038 14326217 := bstep (se 2 (by rfl) ⟨5372331, by rfl⟩ : syracuseStep 14326217 = 10744663) B10744663
theorem B32236379 : Blo 1676038 32236379 := bstep (se 1 (by rfl) ⟨24177284, by rfl⟩ : syracuseStep 32236379 = 48354569) B48354569
theorem B167642131 : Blo 1676038 167642131 := bstep (se 1 (by rfl) ⟨125731598, by rfl⟩ : syracuseStep 167642131 = 251463197) B251463197
theorem B10749023 : Blo 1676038 10749023 := bstep (se 1 (by rfl) ⟨8061767, by rfl⟩ : syracuseStep 10749023 = 16123535) B16123535
theorem B1676647 : Blo 1676038 1676647 := bstep (se 1 (by rfl) ⟨1257485, by rfl⟩ : syracuseStep 1676647 = 2514971) B2514971
theorem B9550811 : Blo 1676038 9550811 := bstep (se 1 (by rfl) ⟨7163108, by rfl⟩ : syracuseStep 9550811 = 14326217) B14326217
theorem B28662821 : Blo 1676038 28662821 := bstep (se 4 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 28662821 = 5374279) B5374279
theorem B6367207 : Blo 1676038 6367207 := bstep (se 1 (by rfl) ⟨4775405, by rfl⟩ : syracuseStep 6367207 = 9550811) B9550811
theorem B21490919 : Blo 1676038 21490919 := bstep (se 1 (by rfl) ⟨16118189, by rfl⟩ : syracuseStep 21490919 = 32236379) B32236379
theorem B223522841 : Blo 1676038 223522841 := bstep (se 2 (by rfl) ⟨83821065, by rfl⟩ : syracuseStep 223522841 = 167642131) B167642131
theorem B19108547 : Blo 1676038 19108547 := bstep (se 1 (by rfl) ⟨14331410, by rfl⟩ : syracuseStep 19108547 = 28662821) B28662821
theorem B7166015 : Blo 1676038 7166015 := bstep (se 1 (by rfl) ⟨5374511, by rfl⟩ : syracuseStep 7166015 = 10749023) B10749023
theorem B12739031 : Blo 1676038 12739031 := bstep (se 1 (by rfl) ⟨9554273, by rfl⟩ : syracuseStep 12739031 = 19108547) B19108547
theorem B4777343 : Blo 1676038 4777343 := bstep (se 1 (by rfl) ⟨3583007, by rfl⟩ : syracuseStep 4777343 = 7166015) B7166015
theorem B8489609 : Blo 1676038 8489609 := bstep (se 2 (by rfl) ⟨3183603, by rfl⟩ : syracuseStep 8489609 = 6367207) B6367207
theorem B149015227 : Blo 1676038 149015227 := bstep (se 1 (by rfl) ⟨111761420, by rfl⟩ : syracuseStep 149015227 = 223522841) B223522841
theorem B14327279 : Blo 1676038 14327279 := bstep (se 1 (by rfl) ⟨10745459, by rfl⟩ : syracuseStep 14327279 = 21490919) B21490919
theorem B8492687 : Blo 1676038 8492687 := bstep (se 1 (by rfl) ⟨6369515, by rfl⟩ : syracuseStep 8492687 = 12739031) B12739031
theorem B198686969 : Blo 1676038 198686969 := bstep (se 2 (by rfl) ⟨74507613, by rfl⟩ : syracuseStep 198686969 = 149015227) B149015227
theorem B3184895 : Blo 1676038 3184895 := bstep (se 1 (by rfl) ⟨2388671, by rfl⟩ : syracuseStep 3184895 = 4777343) B4777343
theorem B5659739 : Blo 1676038 5659739 := bstep (se 1 (by rfl) ⟨4244804, by rfl⟩ : syracuseStep 5659739 = 8489609) B8489609
theorem B9551519 : Blo 1676038 9551519 := bstep (se 1 (by rfl) ⟨7163639, by rfl⟩ : syracuseStep 9551519 = 14327279) B14327279
theorem B5661791 : Blo 1676038 5661791 := bstep (se 1 (by rfl) ⟨4246343, by rfl⟩ : syracuseStep 5661791 = 8492687) B8492687
theorem B132457979 : Blo 1676038 132457979 := bstep (se 1 (by rfl) ⟨99343484, by rfl⟩ : syracuseStep 132457979 = 198686969) B198686969
theorem B2123263 : Blo 1676038 2123263 := bstep (se 1 (by rfl) ⟨1592447, by rfl⟩ : syracuseStep 2123263 = 3184895) B3184895
theorem B6367679 : Blo 1676038 6367679 := bstep (se 1 (by rfl) ⟨4775759, by rfl⟩ : syracuseStep 6367679 = 9551519) B9551519
theorem B3773159 : Blo 1676038 3773159 := bstep (se 1 (by rfl) ⟨2829869, by rfl⟩ : syracuseStep 3773159 = 5659739) B5659739
theorem B2515439 : Blo 1676038 2515439 := bstep (se 1 (by rfl) ⟨1886579, by rfl⟩ : syracuseStep 2515439 = 3773159) B3773159
theorem B4245119 : Blo 1676038 4245119 := bstep (se 1 (by rfl) ⟨3183839, by rfl⟩ : syracuseStep 4245119 = 6367679) B6367679
theorem B88305319 : Blo 1676038 88305319 := bstep (se 1 (by rfl) ⟨66228989, by rfl⟩ : syracuseStep 88305319 = 132457979) B132457979
theorem B2831017 : Blo 1676038 2831017 := bstep (se 2 (by rfl) ⟨1061631, by rfl⟩ : syracuseStep 2831017 = 2123263) B2123263
theorem B3774527 : Blo 1676038 3774527 := bstep (se 1 (by rfl) ⟨2830895, by rfl⟩ : syracuseStep 3774527 = 5661791) B5661791
theorem B2516351 : Blo 1676038 2516351 := bstep (se 1 (by rfl) ⟨1887263, by rfl⟩ : syracuseStep 2516351 = 3774527) B3774527
theorem B2830079 : Blo 1676038 2830079 := bstep (se 1 (by rfl) ⟨2122559, by rfl⟩ : syracuseStep 2830079 = 4245119) B4245119
theorem B117740425 : Blo 1676038 117740425 := bstep (se 2 (by rfl) ⟨44152659, by rfl⟩ : syracuseStep 117740425 = 88305319) B88305319
theorem B1676959 : Blo 1676038 1676959 := bstep (se 1 (by rfl) ⟨1257719, by rfl⟩ : syracuseStep 1676959 = 2515439) B2515439
theorem B3774689 : Blo 1676038 3774689 := bstep (se 2 (by rfl) ⟨1415508, by rfl⟩ : syracuseStep 3774689 = 2831017) B2831017
theorem B2516459 : Blo 1676038 2516459 := bstep (se 1 (by rfl) ⟨1887344, by rfl⟩ : syracuseStep 2516459 = 3774689) B3774689
theorem B1886719 : Blo 1676038 1886719 := bstep (se 1 (by rfl) ⟨1415039, by rfl⟩ : syracuseStep 1886719 = 2830079) B2830079
theorem B156987233 : Blo 1676038 156987233 := bstep (se 2 (by rfl) ⟨58870212, by rfl⟩ : syracuseStep 156987233 = 117740425) B117740425
theorem B1677567 : Blo 1676038 1677567 := bstep (se 1 (by rfl) ⟨1258175, by rfl⟩ : syracuseStep 1677567 = 2516351) B2516351
theorem B2515625 : Blo 1676038 2515625 := bstep (se 2 (by rfl) ⟨943359, by rfl⟩ : syracuseStep 2515625 = 1886719) B1886719
theorem B104658155 : Blo 1676038 104658155 := bstep (se 1 (by rfl) ⟨78493616, by rfl⟩ : syracuseStep 104658155 = 156987233) B156987233
theorem B1677639 : Blo 1676038 1677639 := bstep (se 1 (by rfl) ⟨1258229, by rfl⟩ : syracuseStep 1677639 = 2516459) B2516459
theorem B69772103 : Blo 1676038 69772103 := bstep (se 1 (by rfl) ⟨52329077, by rfl⟩ : syracuseStep 69772103 = 104658155) B104658155
theorem B1677083 : Blo 1676038 1677083 := bstep (se 1 (by rfl) ⟨1257812, by rfl⟩ : syracuseStep 1677083 = 2515625) B2515625
theorem B46514735 : Blo 1676038 46514735 := bstep (se 1 (by rfl) ⟨34886051, by rfl⟩ : syracuseStep 46514735 = 69772103) B69772103
theorem B31009823 : Blo 1676038 31009823 := bstep (se 1 (by rfl) ⟨23257367, by rfl⟩ : syracuseStep 31009823 = 46514735) B46514735
theorem B20673215 : Blo 1676038 20673215 := bstep (se 1 (by rfl) ⟨15504911, by rfl⟩ : syracuseStep 20673215 = 31009823) B31009823
theorem B13782143 : Blo 1676038 13782143 := bstep (se 1 (by rfl) ⟨10336607, by rfl⟩ : syracuseStep 13782143 = 20673215) B20673215
theorem B36752381 : Blo 1676038 36752381 := bstep (se 3 (by rfl) ⟨6891071, by rfl⟩ : syracuseStep 36752381 = 13782143) B13782143
theorem B24501587 : Blo 1676038 24501587 := bstep (se 1 (by rfl) ⟨18376190, by rfl⟩ : syracuseStep 24501587 = 36752381) B36752381
theorem B65337565 : Blo 1676038 65337565 := bstep (se 3 (by rfl) ⟨12250793, by rfl⟩ : syracuseStep 65337565 = 24501587) B24501587
theorem B87116753 : Blo 1676038 87116753 := bstep (se 2 (by rfl) ⟨32668782, by rfl⟩ : syracuseStep 87116753 = 65337565) B65337565
theorem B232311341 : Blo 1676038 232311341 := bstep (se 3 (by rfl) ⟨43558376, by rfl⟩ : syracuseStep 232311341 = 87116753) B87116753
theorem B154874227 : Blo 1676038 154874227 := bstep (se 1 (by rfl) ⟨116155670, by rfl⟩ : syracuseStep 154874227 = 232311341) B232311341
theorem B206498969 : Blo 1676038 206498969 := bstep (se 2 (by rfl) ⟨77437113, by rfl⟩ : syracuseStep 206498969 = 154874227) B154874227
theorem B137665979 : Blo 1676038 137665979 := bstep (se 1 (by rfl) ⟨103249484, by rfl⟩ : syracuseStep 137665979 = 206498969) B206498969
theorem B91777319 : Blo 1676038 91777319 := bstep (se 1 (by rfl) ⟨68832989, by rfl⟩ : syracuseStep 91777319 = 137665979) B137665979
theorem B61184879 : Blo 1676038 61184879 := bstep (se 1 (by rfl) ⟨45888659, by rfl⟩ : syracuseStep 61184879 = 91777319) B91777319
theorem B40789919 : Blo 1676038 40789919 := bstep (se 1 (by rfl) ⟨30592439, by rfl⟩ : syracuseStep 40789919 = 61184879) B61184879
theorem B27193279 : Blo 1676038 27193279 := bstep (se 1 (by rfl) ⟨20394959, by rfl⟩ : syracuseStep 27193279 = 40789919) B40789919
theorem B36257705 : Blo 1676038 36257705 := bstep (se 2 (by rfl) ⟨13596639, by rfl⟩ : syracuseStep 36257705 = 27193279) B27193279
theorem B24171803 : Blo 1676038 24171803 := bstep (se 1 (by rfl) ⟨18128852, by rfl⟩ : syracuseStep 24171803 = 36257705) B36257705
theorem B16114535 : Blo 1676038 16114535 := bstep (se 1 (by rfl) ⟨12085901, by rfl⟩ : syracuseStep 16114535 = 24171803) B24171803
theorem B10743023 : Blo 1676038 10743023 := bstep (se 1 (by rfl) ⟨8057267, by rfl⟩ : syracuseStep 10743023 = 16114535) B16114535
theorem B7162015 : Blo 1676038 7162015 := bstep (se 1 (by rfl) ⟨5371511, by rfl⟩ : syracuseStep 7162015 = 10743023) B10743023
theorem B9549353 : Blo 1676038 9549353 := bstep (se 2 (by rfl) ⟨3581007, by rfl⟩ : syracuseStep 9549353 = 7162015) B7162015
theorem B6366235 : Blo 1676038 6366235 := bstep (se 1 (by rfl) ⟨4774676, by rfl⟩ : syracuseStep 6366235 = 9549353) B9549353
theorem B8488313 : Blo 1676038 8488313 := bstep (se 2 (by rfl) ⟨3183117, by rfl⟩ : syracuseStep 8488313 = 6366235) B6366235
theorem B5658875 : Blo 1676038 5658875 := bstep (se 1 (by rfl) ⟨4244156, by rfl⟩ : syracuseStep 5658875 = 8488313) B8488313
theorem B3772583 : Blo 1676038 3772583 := bstep (se 1 (by rfl) ⟨2829437, by rfl⟩ : syracuseStep 3772583 = 5658875) B5658875
theorem B2515055 : Blo 1676038 2515055 := bstep (se 1 (by rfl) ⟨1886291, by rfl⟩ : syracuseStep 2515055 = 3772583) B3772583
theorem B1676703 : Blo 1676038 1676703 := bstep (se 1 (by rfl) ⟨1257527, by rfl⟩ : syracuseStep 1676703 = 2515055) B2515055

theorem C0 (j : ℕ) (h1 : 419009 ≤ j) (h2 : j ≤ 419508) : Blo 1676038 (4 * j + 3) := by
  interval_cases j
  · exact B1676039
  · exact B1676043
  · exact B1676047
  · exact B1676051
  · exact B1676055
  · exact B1676059
  · exact B1676063
  · exact B1676067
  · exact B1676071
  · exact B1676075
  · exact B1676079
  · exact B1676083
  · exact B1676087
  · exact B1676091
  · exact B1676095
  · exact B1676099
  · exact B1676103
  · exact B1676107
  · exact B1676111
  · exact B1676115
  · exact B1676119
  · exact B1676123
  · exact B1676127
  · exact B1676131
  · exact B1676135
  · exact B1676139
  · exact B1676143
  · exact B1676147
  · exact B1676151
  · exact B1676155
  · exact B1676159
  · exact B1676163
  · exact B1676167
  · exact B1676171
  · exact B1676175
  · exact B1676179
  · exact B1676183
  · exact B1676187
  · exact B1676191
  · exact B1676195
  · exact B1676199
  · exact B1676203
  · exact B1676207
  · exact B1676211
  · exact B1676215
  · exact B1676219
  · exact B1676223
  · exact B1676227
  · exact B1676231
  · exact B1676235
  · exact B1676239
  · exact B1676243
  · exact B1676247
  · exact B1676251
  · exact B1676255
  · exact B1676259
  · exact B1676263
  · exact B1676267
  · exact B1676271
  · exact B1676275
  · exact B1676279
  · exact B1676283
  · exact B1676287
  · exact B1676291
  · exact B1676295
  · exact B1676299
  · exact B1676303
  · exact B1676307
  · exact B1676311
  · exact B1676315
  · exact B1676319
  · exact B1676323
  · exact B1676327
  · exact B1676331
  · exact B1676335
  · exact B1676339
  · exact B1676343
  · exact B1676347
  · exact B1676351
  · exact B1676355
  · exact B1676359
  · exact B1676363
  · exact B1676367
  · exact B1676371
  · exact B1676375
  · exact B1676379
  · exact B1676383
  · exact B1676387
  · exact B1676391
  · exact B1676395
  · exact B1676399
  · exact B1676403
  · exact B1676407
  · exact B1676411
  · exact B1676415
  · exact B1676419
  · exact B1676423
  · exact B1676427
  · exact B1676431
  · exact B1676435
  · exact B1676439
  · exact B1676443
  · exact B1676447
  · exact B1676451
  · exact B1676455
  · exact B1676459
  · exact B1676463
  · exact B1676467
  · exact B1676471
  · exact B1676475
  · exact B1676479
  · exact B1676483
  · exact B1676487
  · exact B1676491
  · exact B1676495
  · exact B1676499
  · exact B1676503
  · exact B1676507
  · exact B1676511
  · exact B1676515
  · exact B1676519
  · exact B1676523
  · exact B1676527
  · exact B1676531
  · exact B1676535
  · exact B1676539
  · exact B1676543
  · exact B1676547
  · exact B1676551
  · exact B1676555
  · exact B1676559
  · exact B1676563
  · exact B1676567
  · exact B1676571
  · exact B1676575
  · exact B1676579
  · exact B1676583
  · exact B1676587
  · exact B1676591
  · exact B1676595
  · exact B1676599
  · exact B1676603
  · exact B1676607
  · exact B1676611
  · exact B1676615
  · exact B1676619
  · exact B1676623
  · exact B1676627
  · exact B1676631
  · exact B1676635
  · exact B1676639
  · exact B1676643
  · exact B1676647
  · exact B1676651
  · exact B1676655
  · exact B1676659
  · exact B1676663
  · exact B1676667
  · exact B1676671
  · exact B1676675
  · exact B1676679
  · exact B1676683
  · exact B1676687
  · exact B1676691
  · exact B1676695
  · exact B1676699
  · exact B1676703
  · exact B1676707
  · exact B1676711
  · exact B1676715
  · exact B1676719
  · exact B1676723
  · exact B1676727
  · exact B1676731
  · exact B1676735
  · exact B1676739
  · exact B1676743
  · exact B1676747
  · exact B1676751
  · exact B1676755
  · exact B1676759
  · exact B1676763
  · exact B1676767
  · exact B1676771
  · exact B1676775
  · exact B1676779
  · exact B1676783
  · exact B1676787
  · exact B1676791
  · exact B1676795
  · exact B1676799
  · exact B1676803
  · exact B1676807
  · exact B1676811
  · exact B1676815
  · exact B1676819
  · exact B1676823
  · exact B1676827
  · exact B1676831
  · exact B1676835
  · exact B1676839
  · exact B1676843
  · exact B1676847
  · exact B1676851
  · exact B1676855
  · exact B1676859
  · exact B1676863
  · exact B1676867
  · exact B1676871
  · exact B1676875
  · exact B1676879
  · exact B1676883
  · exact B1676887
  · exact B1676891
  · exact B1676895
  · exact B1676899
  · exact B1676903
  · exact B1676907
  · exact B1676911
  · exact B1676915
  · exact B1676919
  · exact B1676923
  · exact B1676927
  · exact B1676931
  · exact B1676935
  · exact B1676939
  · exact B1676943
  · exact B1676947
  · exact B1676951
  · exact B1676955
  · exact B1676959
  · exact B1676963
  · exact B1676967
  · exact B1676971
  · exact B1676975
  · exact B1676979
  · exact B1676983
  · exact B1676987
  · exact B1676991
  · exact B1676995
  · exact B1676999
  · exact B1677003
  · exact B1677007
  · exact B1677011
  · exact B1677015
  · exact B1677019
  · exact B1677023
  · exact B1677027
  · exact B1677031
  · exact B1677035
  · exact B1677039
  · exact B1677043
  · exact B1677047
  · exact B1677051
  · exact B1677055
  · exact B1677059
  · exact B1677063
  · exact B1677067
  · exact B1677071
  · exact B1677075
  · exact B1677079
  · exact B1677083
  · exact B1677087
  · exact B1677091
  · exact B1677095
  · exact B1677099
  · exact B1677103
  · exact B1677107
  · exact B1677111
  · exact B1677115
  · exact B1677119
  · exact B1677123
  · exact B1677127
  · exact B1677131
  · exact B1677135
  · exact B1677139
  · exact B1677143
  · exact B1677147
  · exact B1677151
  · exact B1677155
  · exact B1677159
  · exact B1677163
  · exact B1677167
  · exact B1677171
  · exact B1677175
  · exact B1677179
  · exact B1677183
  · exact B1677187
  · exact B1677191
  · exact B1677195
  · exact B1677199
  · exact B1677203
  · exact B1677207
  · exact B1677211
  · exact B1677215
  · exact B1677219
  · exact B1677223
  · exact B1677227
  · exact B1677231
  · exact B1677235
  · exact B1677239
  · exact B1677243
  · exact B1677247
  · exact B1677251
  · exact B1677255
  · exact B1677259
  · exact B1677263
  · exact B1677267
  · exact B1677271
  · exact B1677275
  · exact B1677279
  · exact B1677283
  · exact B1677287
  · exact B1677291
  · exact B1677295
  · exact B1677299
  · exact B1677303
  · exact B1677307
  · exact B1677311
  · exact B1677315
  · exact B1677319
  · exact B1677323
  · exact B1677327
  · exact B1677331
  · exact B1677335
  · exact B1677339
  · exact B1677343
  · exact B1677347
  · exact B1677351
  · exact B1677355
  · exact B1677359
  · exact B1677363
  · exact B1677367
  · exact B1677371
  · exact B1677375
  · exact B1677379
  · exact B1677383
  · exact B1677387
  · exact B1677391
  · exact B1677395
  · exact B1677399
  · exact B1677403
  · exact B1677407
  · exact B1677411
  · exact B1677415
  · exact B1677419
  · exact B1677423
  · exact B1677427
  · exact B1677431
  · exact B1677435
  · exact B1677439
  · exact B1677443
  · exact B1677447
  · exact B1677451
  · exact B1677455
  · exact B1677459
  · exact B1677463
  · exact B1677467
  · exact B1677471
  · exact B1677475
  · exact B1677479
  · exact B1677483
  · exact B1677487
  · exact B1677491
  · exact B1677495
  · exact B1677499
  · exact B1677503
  · exact B1677507
  · exact B1677511
  · exact B1677515
  · exact B1677519
  · exact B1677523
  · exact B1677527
  · exact B1677531
  · exact B1677535
  · exact B1677539
  · exact B1677543
  · exact B1677547
  · exact B1677551
  · exact B1677555
  · exact B1677559
  · exact B1677563
  · exact B1677567
  · exact B1677571
  · exact B1677575
  · exact B1677579
  · exact B1677583
  · exact B1677587
  · exact B1677591
  · exact B1677595
  · exact B1677599
  · exact B1677603
  · exact B1677607
  · exact B1677611
  · exact B1677615
  · exact B1677619
  · exact B1677623
  · exact B1677627
  · exact B1677631
  · exact B1677635
  · exact B1677639
  · exact B1677643
  · exact B1677647
  · exact B1677651
  · exact B1677655
  · exact B1677659
  · exact B1677663
  · exact B1677667
  · exact B1677671
  · exact B1677675
  · exact B1677679
  · exact B1677683
  · exact B1677687
  · exact B1677691
  · exact B1677695
  · exact B1677699
  · exact B1677703
  · exact B1677707
  · exact B1677711
  · exact B1677715
  · exact B1677719
  · exact B1677723
  · exact B1677727
  · exact B1677731
  · exact B1677735
  · exact B1677739
  · exact B1677743
  · exact B1677747
  · exact B1677751
  · exact B1677755
  · exact B1677759
  · exact B1677763
  · exact B1677767
  · exact B1677771
  · exact B1677775
  · exact B1677779
  · exact B1677783
  · exact B1677787
  · exact B1677791
  · exact B1677795
  · exact B1677799
  · exact B1677803
  · exact B1677807
  · exact B1677811
  · exact B1677815
  · exact B1677819
  · exact B1677823
  · exact B1677827
  · exact B1677831
  · exact B1677835
  · exact B1677839
  · exact B1677843
  · exact B1677847
  · exact B1677851
  · exact B1677855
  · exact B1677859
  · exact B1677863
  · exact B1677867
  · exact B1677871
  · exact B1677875
  · exact B1677879
  · exact B1677883
  · exact B1677887
  · exact B1677891
  · exact B1677895
  · exact B1677899
  · exact B1677903
  · exact B1677907
  · exact B1677911
  · exact B1677915
  · exact B1677919
  · exact B1677923
  · exact B1677927
  · exact B1677931
  · exact B1677935
  · exact B1677939
  · exact B1677943
  · exact B1677947
  · exact B1677951
  · exact B1677955
  · exact B1677959
  · exact B1677963
  · exact B1677967
  · exact B1677971
  · exact B1677975
  · exact B1677979
  · exact B1677983
  · exact B1677987
  · exact B1677991
  · exact B1677995
  · exact B1677999
  · exact B1678003
  · exact B1678007
  · exact B1678011
  · exact B1678015
  · exact B1678019
  · exact B1678023
  · exact B1678027
  · exact B1678031
  · exact B1678035

theorem solution (m : ℕ) (hlo : 1676038 ≤ m) (hhi : m ≤ 1678038) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 419009 ≤ j := by omega
    have hj2 : j ≤ 419508 := by omega
    have hb : Blo 1676038 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
