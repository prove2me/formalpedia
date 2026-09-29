-- Prove2me | solution 1 for syracuse_descends_range_860564_864564
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:39.893986+00:00
-- url     : https://prove2.me/submissions/3306bf03-6fb5-4026-8206-6b6795ce2699

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


theorem B1310813 : Blo 860564 1310813 := bbase (se 3 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 1310813 = 491555) (by norm_num)
theorem B3113093 : Blo 860564 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B2916485 : Blo 860564 2916485 := bbase (se 4 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 2916485 = 546841) (by norm_num)
theorem B1310957 : Blo 860564 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B1638701 : Blo 860564 1638701 := bbase (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) (by norm_num)
theorem B3277205 : Blo 860564 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B1475101 : Blo 860564 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B983593 : Blo 860564 983593 := bbase (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) (by norm_num)
theorem B2916917 : Blo 860564 2916917 := bbase (se 5 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 2916917 = 273461) (by norm_num)
theorem B983629 : Blo 860564 983629 := bbase (se 3 (by rfl) ⟨184430, by rfl⟩ : syracuseStep 983629 = 368861) (by norm_num)
theorem B1966693 : Blo 860564 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B4915829 : Blo 860564 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B983729 : Blo 860564 983729 := bbase (se 2 (by rfl) ⟨368898, by rfl⟩ : syracuseStep 983729 = 737797) (by norm_num)
theorem B3277493 : Blo 860564 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2458325 : Blo 860564 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B4358933 : Blo 860564 4358933 := bbase (se 6 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 4358933 = 204325) (by norm_num)
theorem B1967021 : Blo 860564 1967021 := bbase (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) (by norm_num)
theorem B2917349 : Blo 860564 2917349 := bbase (se 4 (by rfl) ⟨273501, by rfl⟩ : syracuseStep 2917349 = 547003) (by norm_num)
theorem B1639453 : Blo 860564 1639453 := bbase (se 3 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 1639453 = 614795) (by norm_num)
theorem B1639597 : Blo 860564 1639597 := bbase (se 3 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 1639597 = 614849) (by norm_num)
theorem B4654261 : Blo 860564 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B1639757 : Blo 860564 1639757 := bbase (se 3 (by rfl) ⟨307454, by rfl⟩ : syracuseStep 1639757 = 614909) (by norm_num)
theorem B2917781 : Blo 860564 2917781 := bbase (se 6 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 2917781 = 136771) (by norm_num)
theorem B1639901 : Blo 860564 1639901 := bbase (se 3 (by rfl) ⟨307481, by rfl⟩ : syracuseStep 1639901 = 614963) (by norm_num)
theorem B984565 : Blo 860564 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B919117 : Blo 860564 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B919121 : Blo 860564 919121 := bbase (se 2 (by rfl) ⟨344670, by rfl⟩ : syracuseStep 919121 = 689341) (by norm_num)
theorem B1640189 : Blo 860564 1640189 := bbase (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) (by norm_num)
theorem B5605141 : Blo 860564 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B3278677 : Blo 860564 3278677 := bbase (se 9 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 3278677 = 19211) (by norm_num)
theorem B1967989 : Blo 860564 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B1640341 : Blo 860564 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B4360229 : Blo 860564 4360229 := bbase (se 4 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 4360229 = 817543) (by norm_num)
theorem B919685 : Blo 860564 919685 := bbase (se 4 (by rfl) ⟨86220, by rfl⟩ : syracuseStep 919685 = 172441) (by norm_num)
theorem B2492549 : Blo 860564 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B3278981 : Blo 860564 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B1476757 : Blo 860564 1476757 := bbase (se 6 (by rfl) ⟨34611, by rfl⟩ : syracuseStep 1476757 = 69223) (by norm_num)
theorem B1640645 : Blo 860564 1640645 := bbase (se 4 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 1640645 = 307621) (by norm_num)
theorem B2459909 : Blo 860564 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1771789 : Blo 860564 1771789 := bbase (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) (by norm_num)
theorem B919873 : Blo 860564 919873 := bbase (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) (by norm_num)
theorem B887113 : Blo 860564 887113 := bbase (se 2 (by rfl) ⟨332667, by rfl⟩ : syracuseStep 887113 = 665335) (by norm_num)
theorem B2623861 : Blo 860564 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B1051013 : Blo 860564 1051013 := bbase (se 4 (by rfl) ⟨98532, by rfl⟩ : syracuseStep 1051013 = 197065) (by norm_num)
theorem B1968845 : Blo 860564 1968845 := bbase (se 3 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 1968845 = 738317) (by norm_num)
theorem B2394917 : Blo 860564 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1379189 : Blo 860564 1379189 := bbase (se 5 (by rfl) ⟨64649, by rfl⟩ : syracuseStep 1379189 = 129299) (by norm_num)
theorem B1936277 : Blo 860564 1936277 := bbase (se 6 (by rfl) ⟨45381, by rfl⟩ : syracuseStep 1936277 = 90763) (by norm_num)
theorem B2460581 : Blo 860564 2460581 := bbase (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) (by norm_num)
theorem B1182637 : Blo 860564 1182637 := bbase (se 3 (by rfl) ⟨221744, by rfl⟩ : syracuseStep 1182637 = 443489) (by norm_num)
theorem B1936349 : Blo 860564 1936349 := bbase (se 3 (by rfl) ⟨363065, by rfl⟩ : syracuseStep 1936349 = 726131) (by norm_num)
theorem B887833 : Blo 860564 887833 := bbase (se 2 (by rfl) ⟨332937, by rfl⟩ : syracuseStep 887833 = 665875) (by norm_num)
theorem B1870877 : Blo 860564 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B1936421 : Blo 860564 1936421 := bbase (se 4 (by rfl) ⟨181539, by rfl⟩ : syracuseStep 1936421 = 363079) (by norm_num)
theorem B1182773 : Blo 860564 1182773 := bbase (se 5 (by rfl) ⟨55442, by rfl⟩ : syracuseStep 1182773 = 110885) (by norm_num)
theorem B1936493 : Blo 860564 1936493 := bbase (se 3 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 1936493 = 726185) (by norm_num)
theorem B920693 : Blo 860564 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B1936565 : Blo 860564 1936565 := bbase (se 5 (by rfl) ⟨90776, by rfl⟩ : syracuseStep 1936565 = 181553) (by norm_num)
theorem B1936637 : Blo 860564 1936637 := bbase (se 3 (by rfl) ⟨363119, by rfl⟩ : syracuseStep 1936637 = 726239) (by norm_num)
theorem B4361525 : Blo 860564 4361525 := bbase (se 5 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 4361525 = 408893) (by norm_num)
theorem B1936709 : Blo 860564 1936709 := bbase (se 4 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 1936709 = 363133) (by norm_num)
theorem B1838413 : Blo 860564 1838413 := bbase (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) (by norm_num)
theorem B2461013 : Blo 860564 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B1379701 : Blo 860564 1379701 := bbase (se 5 (by rfl) ⟨64673, by rfl⟩ : syracuseStep 1379701 = 129347) (by norm_num)
theorem B1936781 : Blo 860564 1936781 := bbase (se 3 (by rfl) ⟨363146, by rfl⟩ : syracuseStep 1936781 = 726293) (by norm_num)
theorem B2067869 : Blo 860564 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B1838533 : Blo 860564 1838533 := bbase (se 4 (by rfl) ⟨172362, by rfl⟩ : syracuseStep 1838533 = 344725) (by norm_num)
theorem B1936853 : Blo 860564 1936853 := bbase (se 7 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 1936853 = 45395) (by norm_num)
theorem B1936925 : Blo 860564 1936925 := bbase (se 3 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 1936925 = 726347) (by norm_num)
theorem B2428453 : Blo 860564 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B921137 : Blo 860564 921137 := bbase (se 2 (by rfl) ⟨345426, by rfl⟩ : syracuseStep 921137 = 690853) (by norm_num)
theorem B1936997 : Blo 860564 1936997 := bbase (se 4 (by rfl) ⟨181593, by rfl⟩ : syracuseStep 1936997 = 363187) (by norm_num)
theorem B2330245 : Blo 860564 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B1937069 : Blo 860564 1937069 := bbase (se 3 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 1937069 = 726401) (by norm_num)
theorem B1838789 : Blo 860564 1838789 := bbase (se 4 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 1838789 = 344773) (by norm_num)
theorem B1937141 : Blo 860564 1937141 := bbase (se 5 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 1937141 = 181607) (by norm_num)
theorem B921385 : Blo 860564 921385 := bbase (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) (by norm_num)
theorem B8294197 : Blo 860564 8294197 := bbase (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) (by norm_num)
theorem B1937213 : Blo 860564 1937213 := bbase (se 3 (by rfl) ⟨363227, by rfl⟩ : syracuseStep 1937213 = 726455) (by norm_num)
theorem B4657013 : Blo 860564 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B1937285 : Blo 860564 1937285 := bbase (se 4 (by rfl) ⟨181620, by rfl⟩ : syracuseStep 1937285 = 363241) (by norm_num)
theorem B1380245 : Blo 860564 1380245 := bbase (se 6 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 1380245 = 64699) (by norm_num)
theorem B1937357 : Blo 860564 1937357 := bbase (se 3 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 1937357 = 726509) (by norm_num)
theorem B3313685 : Blo 860564 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B1937429 : Blo 860564 1937429 := bbase (se 6 (by rfl) ⟨45408, by rfl⟩ : syracuseStep 1937429 = 90817) (by norm_num)
theorem B2461765 : Blo 860564 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B1478741 : Blo 860564 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B1937501 : Blo 860564 1937501 := bbase (se 3 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 1937501 = 726563) (by norm_num)
theorem B1937573 : Blo 860564 1937573 := bbase (se 4 (by rfl) ⟨181647, by rfl⟩ : syracuseStep 1937573 = 363295) (by norm_num)
theorem B3281093 : Blo 860564 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B921817 : Blo 860564 921817 := bbase (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) (by norm_num)
theorem B1937645 : Blo 860564 1937645 := bbase (se 3 (by rfl) ⟨363308, by rfl⟩ : syracuseStep 1937645 = 726617) (by norm_num)
theorem B921889 : Blo 860564 921889 := bbase (se 2 (by rfl) ⟨345708, by rfl⟩ : syracuseStep 921889 = 691417) (by norm_num)
theorem B1937717 : Blo 860564 1937717 := bbase (se 5 (by rfl) ⟨90830, by rfl⟩ : syracuseStep 1937717 = 181661) (by norm_num)
theorem B1937789 : Blo 860564 1937789 := bbase (se 3 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 1937789 = 726671) (by norm_num)
theorem B1380797 : Blo 860564 1380797 := bbase (se 3 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 1380797 = 517799) (by norm_num)
theorem B1937861 : Blo 860564 1937861 := bbase (se 4 (by rfl) ⟨181674, by rfl⟩ : syracuseStep 1937861 = 363349) (by norm_num)
theorem B1380829 : Blo 860564 1380829 := bbase (se 3 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 1380829 = 517811) (by norm_num)
theorem B3281381 : Blo 860564 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B1937933 : Blo 860564 1937933 := bbase (se 3 (by rfl) ⟨363362, by rfl⟩ : syracuseStep 1937933 = 726725) (by norm_num)
theorem B1839677 : Blo 860564 1839677 := bbase (se 3 (by rfl) ⟨344939, by rfl⟩ : syracuseStep 1839677 = 689879) (by norm_num)
theorem B4362821 : Blo 860564 4362821 := bbase (se 4 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 4362821 = 818029) (by norm_num)
theorem B1938005 : Blo 860564 1938005 := bbase (se 8 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 1938005 = 22711) (by norm_num)
theorem B922261 : Blo 860564 922261 := bbase (se 6 (by rfl) ⟨21615, by rfl⟩ : syracuseStep 922261 = 43231) (by norm_num)
theorem B1938077 : Blo 860564 1938077 := bbase (se 3 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 1938077 = 726779) (by norm_num)
theorem B1970909 : Blo 860564 1970909 := bbase (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) (by norm_num)
theorem B1938149 : Blo 860564 1938149 := bbase (se 4 (by rfl) ⟨181701, by rfl⟩ : syracuseStep 1938149 = 363403) (by norm_num)
theorem B1938221 : Blo 860564 1938221 := bbase (se 3 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 1938221 = 726833) (by norm_num)
theorem B1839917 : Blo 860564 1839917 := bbase (se 3 (by rfl) ⟨344984, by rfl⟩ : syracuseStep 1839917 = 689969) (by norm_num)
theorem B1938293 : Blo 860564 1938293 := bbase (se 5 (by rfl) ⟨90857, by rfl⟩ : syracuseStep 1938293 = 181715) (by norm_num)
theorem B2757557 : Blo 860564 2757557 := bbase (se 5 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 2757557 = 258521) (by norm_num)
theorem B1938365 : Blo 860564 1938365 := bbase (se 3 (by rfl) ⟨363443, by rfl⟩ : syracuseStep 1938365 = 726887) (by norm_num)
theorem B1577965 : Blo 860564 1577965 := bbase (se 3 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 1577965 = 591737) (by norm_num)
theorem B1938437 : Blo 860564 1938437 := bbase (se 4 (by rfl) ⟨181728, by rfl⟩ : syracuseStep 1938437 = 363457) (by norm_num)
theorem B922637 : Blo 860564 922637 := bbase (se 3 (by rfl) ⟨172994, by rfl⟩ : syracuseStep 922637 = 345989) (by norm_num)
theorem B1938509 : Blo 860564 1938509 := bbase (se 3 (by rfl) ⟨363470, by rfl⟩ : syracuseStep 1938509 = 726941) (by norm_num)
theorem B922709 : Blo 860564 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B1938581 : Blo 860564 1938581 := bbase (se 6 (by rfl) ⟨45435, by rfl⟩ : syracuseStep 1938581 = 90871) (by norm_num)
theorem B1938653 : Blo 860564 1938653 := bbase (se 3 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 1938653 = 726995) (by norm_num)
theorem B922897 : Blo 860564 922897 := bbase (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) (by norm_num)
theorem B1938725 : Blo 860564 1938725 := bbase (se 4 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 1938725 = 363511) (by norm_num)
theorem B1840421 : Blo 860564 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1840429 : Blo 860564 1840429 := bbase (se 3 (by rfl) ⟨345080, by rfl⟩ : syracuseStep 1840429 = 690161) (by norm_num)
theorem B1938797 : Blo 860564 1938797 := bbase (se 3 (by rfl) ⟨363524, by rfl⟩ : syracuseStep 1938797 = 727049) (by norm_num)
theorem B1381757 : Blo 860564 1381757 := bbase (se 3 (by rfl) ⟨259079, by rfl⟩ : syracuseStep 1381757 = 518159) (by norm_num)
theorem B1938869 : Blo 860564 1938869 := bbase (se 5 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 1938869 = 181769) (by norm_num)
theorem B923081 : Blo 860564 923081 := bbase (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) (by norm_num)
theorem B2069965 : Blo 860564 2069965 := bbase (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) (by norm_num)
theorem B1938941 : Blo 860564 1938941 := bbase (se 3 (by rfl) ⟨363551, by rfl⟩ : syracuseStep 1938941 = 727103) (by norm_num)
theorem B1939013 : Blo 860564 1939013 := bbase (se 4 (by rfl) ⟨181782, by rfl⟩ : syracuseStep 1939013 = 363565) (by norm_num)
theorem B3282565 : Blo 860564 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B1939085 : Blo 860564 1939085 := bbase (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) (by norm_num)
theorem B1939157 : Blo 860564 1939157 := bbase (se 7 (by rfl) ⟨22724, by rfl⟩ : syracuseStep 1939157 = 45449) (by norm_num)
theorem B1939229 : Blo 860564 1939229 := bbase (se 3 (by rfl) ⟨363605, by rfl⟩ : syracuseStep 1939229 = 727211) (by norm_num)
theorem B6559541 : Blo 860564 6559541 := bbase (se 5 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 6559541 = 614957) (by norm_num)
theorem B4364117 : Blo 860564 4364117 := bbase (se 9 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 4364117 = 25571) (by norm_num)
theorem B1939301 : Blo 860564 1939301 := bbase (se 4 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 1939301 = 363619) (by norm_num)
theorem B1939373 : Blo 860564 1939373 := bbase (se 3 (by rfl) ⟨363632, by rfl⟩ : syracuseStep 1939373 = 727265) (by norm_num)
theorem B13277141 : Blo 860564 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1939445 : Blo 860564 1939445 := bbase (se 5 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 1939445 = 181823) (by norm_num)
theorem B1382437 : Blo 860564 1382437 := bbase (se 4 (by rfl) ⟨129603, by rfl⟩ : syracuseStep 1382437 = 259207) (by norm_num)
theorem B1939517 : Blo 860564 1939517 := bbase (se 3 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 1939517 = 727319) (by norm_num)
theorem B2070629 : Blo 860564 2070629 := bbase (se 4 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 2070629 = 388243) (by norm_num)
theorem B1382501 : Blo 860564 1382501 := bbase (se 4 (by rfl) ⟨129609, by rfl⟩ : syracuseStep 1382501 = 259219) (by norm_num)
theorem B1939589 : Blo 860564 1939589 := bbase (se 4 (by rfl) ⟨181836, by rfl⟩ : syracuseStep 1939589 = 363673) (by norm_num)
theorem B1939661 : Blo 860564 1939661 := bbase (se 3 (by rfl) ⟨363686, by rfl⟩ : syracuseStep 1939661 = 727373) (by norm_num)
theorem B1939733 : Blo 860564 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B1939805 : Blo 860564 1939805 := bbase (se 3 (by rfl) ⟨363713, by rfl⟩ : syracuseStep 1939805 = 727427) (by norm_num)
theorem B1841557 : Blo 860564 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B1939877 : Blo 860564 1939877 := bbase (se 4 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 1939877 = 363727) (by norm_num)
theorem B1939949 : Blo 860564 1939949 := bbase (se 3 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 1939949 = 727481) (by norm_num)
theorem B1940021 : Blo 860564 1940021 := bbase (se 5 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 1940021 = 181877) (by norm_num)
theorem B4659797 : Blo 860564 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B1940093 : Blo 860564 1940093 := bbase (se 3 (by rfl) ⟨363767, by rfl⟩ : syracuseStep 1940093 = 727535) (by norm_num)
theorem B1940165 : Blo 860564 1940165 := bbase (se 4 (by rfl) ⟨181890, by rfl⟩ : syracuseStep 1940165 = 363781) (by norm_num)
theorem B1940237 : Blo 860564 1940237 := bbase (se 3 (by rfl) ⟨363794, by rfl⟩ : syracuseStep 1940237 = 727589) (by norm_num)
theorem B1841933 : Blo 860564 1841933 := bbase (se 3 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 1841933 = 690725) (by norm_num)
theorem B1940309 : Blo 860564 1940309 := bbase (se 9 (by rfl) ⟨5684, by rfl⟩ : syracuseStep 1940309 = 11369) (by norm_num)
theorem B1940381 : Blo 860564 1940381 := bbase (se 3 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 1940381 = 727643) (by norm_num)
theorem B1940453 : Blo 860564 1940453 := bbase (se 4 (by rfl) ⟨181917, by rfl⟩ : syracuseStep 1940453 = 363835) (by norm_num)
theorem B1776629 : Blo 860564 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B1940525 : Blo 860564 1940525 := bbase (se 3 (by rfl) ⟨363848, by rfl⟩ : syracuseStep 1940525 = 727697) (by norm_num)
theorem B3677237 : Blo 860564 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B4365413 : Blo 860564 4365413 := bbase (se 4 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 4365413 = 818515) (by norm_num)
theorem B1940597 : Blo 860564 1940597 := bbase (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) (by norm_num)
theorem B1940669 : Blo 860564 1940669 := bbase (se 3 (by rfl) ⟨363875, by rfl⟩ : syracuseStep 1940669 = 727751) (by norm_num)
theorem B1940741 : Blo 860564 1940741 := bbase (se 4 (by rfl) ⟨181944, by rfl⟩ : syracuseStep 1940741 = 363889) (by norm_num)
theorem B1940813 : Blo 860564 1940813 := bbase (se 3 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 1940813 = 727805) (by norm_num)
theorem B1383821 : Blo 860564 1383821 := bbase (se 3 (by rfl) ⟨259466, by rfl⟩ : syracuseStep 1383821 = 518933) (by norm_num)
theorem B1940885 : Blo 860564 1940885 := bbase (se 6 (by rfl) ⟨45489, by rfl⟩ : syracuseStep 1940885 = 90979) (by norm_num)
theorem B1940957 : Blo 860564 1940957 := bbase (se 3 (by rfl) ⟨363929, by rfl⟩ : syracuseStep 1940957 = 727859) (by norm_num)
theorem B1941029 : Blo 860564 1941029 := bbase (se 4 (by rfl) ⟨181971, by rfl⟩ : syracuseStep 1941029 = 363943) (by norm_num)
theorem B2367029 : Blo 860564 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1384013 : Blo 860564 1384013 := bbase (se 3 (by rfl) ⟨259502, by rfl⟩ : syracuseStep 1384013 = 519005) (by norm_num)
theorem B1941101 : Blo 860564 1941101 := bbase (se 3 (by rfl) ⟨363956, by rfl⟩ : syracuseStep 1941101 = 727913) (by norm_num)
theorem B1941173 : Blo 860564 1941173 := bbase (se 5 (by rfl) ⟨90992, by rfl⟩ : syracuseStep 1941173 = 181985) (by norm_num)
theorem B1089217 : Blo 860564 1089217 := bbase (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) (by norm_num)
theorem B2760389 : Blo 860564 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B1384141 : Blo 860564 1384141 := bbase (se 3 (by rfl) ⟨259526, by rfl⟩ : syracuseStep 1384141 = 519053) (by norm_num)
theorem B1941245 : Blo 860564 1941245 := bbase (se 3 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 1941245 = 727967) (by norm_num)
theorem B1941317 : Blo 860564 1941317 := bbase (se 4 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 1941317 = 363997) (by norm_num)
theorem B2072405 : Blo 860564 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B1679197 : Blo 860564 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B1089389 : Blo 860564 1089389 := bbase (se 3 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 1089389 = 408521) (by norm_num)
theorem B1941389 : Blo 860564 1941389 := bbase (se 3 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 1941389 = 728021) (by norm_num)
theorem B1089445 : Blo 860564 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1941461 : Blo 860564 1941461 := bbase (se 7 (by rfl) ⟨22751, by rfl⟩ : syracuseStep 1941461 = 45503) (by norm_num)
theorem B1089541 : Blo 860564 1089541 := bbase (se 4 (by rfl) ⟨102144, by rfl⟩ : syracuseStep 1089541 = 204289) (by norm_num)
theorem B14000149 : Blo 860564 14000149 := bbase (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) (by norm_num)
theorem B1941533 : Blo 860564 1941533 := bbase (se 3 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 1941533 = 728075) (by norm_num)
theorem B1941605 : Blo 860564 1941605 := bbase (se 4 (by rfl) ⟨182025, by rfl⟩ : syracuseStep 1941605 = 364051) (by norm_num)
theorem B1941677 : Blo 860564 1941677 := bbase (se 3 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 1941677 = 728129) (by norm_num)
theorem B1089713 : Blo 860564 1089713 := bbase (se 2 (by rfl) ⟨408642, by rfl⟩ : syracuseStep 1089713 = 817285) (by norm_num)
theorem B2957525 : Blo 860564 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B1089769 : Blo 860564 1089769 := bbase (se 2 (by rfl) ⟨408663, by rfl⟩ : syracuseStep 1089769 = 817327) (by norm_num)
theorem B1941749 : Blo 860564 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B1941821 : Blo 860564 1941821 := bbase (se 3 (by rfl) ⟨364091, by rfl⟩ : syracuseStep 1941821 = 728183) (by norm_num)
theorem B1089865 : Blo 860564 1089865 := bbase (se 2 (by rfl) ⟨408699, by rfl⟩ : syracuseStep 1089865 = 817399) (by norm_num)
theorem B1384781 : Blo 860564 1384781 := bbase (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) (by norm_num)
theorem B1122665 : Blo 860564 1122665 := bbase (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) (by norm_num)
theorem B4366709 : Blo 860564 4366709 := bbase (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) (by norm_num)
theorem B1843573 : Blo 860564 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B1941893 : Blo 860564 1941893 := bbase (se 4 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 1941893 = 364105) (by norm_num)
theorem B1941965 : Blo 860564 1941965 := bbase (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) (by norm_num)
theorem B1090037 : Blo 860564 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B1942037 : Blo 860564 1942037 := bbase (se 6 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 1942037 = 91033) (by norm_num)
theorem B1090093 : Blo 860564 1090093 := bbase (se 3 (by rfl) ⟨204392, by rfl⟩ : syracuseStep 1090093 = 408785) (by norm_num)
theorem B2761285 : Blo 860564 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B1942109 : Blo 860564 1942109 := bbase (se 3 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 1942109 = 728291) (by norm_num)
theorem B1090189 : Blo 860564 1090189 := bbase (se 3 (by rfl) ⟨204410, by rfl⟩ : syracuseStep 1090189 = 408821) (by norm_num)
theorem B1942181 : Blo 860564 1942181 := bbase (se 4 (by rfl) ⟨182079, by rfl⟩ : syracuseStep 1942181 = 364159) (by norm_num)
theorem B1942253 : Blo 860564 1942253 := bbase (se 3 (by rfl) ⟨364172, by rfl⟩ : syracuseStep 1942253 = 728345) (by norm_num)
theorem B3679013 : Blo 860564 3679013 := bbase (se 4 (by rfl) ⟨344907, by rfl⟩ : syracuseStep 3679013 = 689815) (by norm_num)
theorem B1942325 : Blo 860564 1942325 := bbase (se 5 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 1942325 = 182093) (by norm_num)
theorem B1090361 : Blo 860564 1090361 := bbase (se 2 (by rfl) ⟨408885, by rfl⟩ : syracuseStep 1090361 = 817771) (by norm_num)
theorem B1090417 : Blo 860564 1090417 := bbase (se 2 (by rfl) ⟨408906, by rfl⟩ : syracuseStep 1090417 = 817813) (by norm_num)
theorem B1942397 : Blo 860564 1942397 := bbase (se 3 (by rfl) ⟨364199, by rfl⟩ : syracuseStep 1942397 = 728399) (by norm_num)
theorem B1942469 : Blo 860564 1942469 := bbase (se 4 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 1942469 = 364213) (by norm_num)
theorem B1090513 : Blo 860564 1090513 := bbase (se 2 (by rfl) ⟨408942, by rfl⟩ : syracuseStep 1090513 = 817885) (by norm_num)
theorem B1942541 : Blo 860564 1942541 := bbase (se 3 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 1942541 = 728453) (by norm_num)
theorem B3679253 : Blo 860564 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B1942613 : Blo 860564 1942613 := bbase (se 8 (by rfl) ⟨11382, by rfl⟩ : syracuseStep 1942613 = 22765) (by norm_num)
theorem B1090685 : Blo 860564 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B1942685 : Blo 860564 1942685 := bbase (se 3 (by rfl) ⟨364253, by rfl⟩ : syracuseStep 1942685 = 728507) (by norm_num)
theorem B1090741 : Blo 860564 1090741 := bbase (se 5 (by rfl) ⟨51128, by rfl⟩ : syracuseStep 1090741 = 102257) (by norm_num)
theorem B1942757 : Blo 860564 1942757 := bbase (se 4 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 1942757 = 364267) (by norm_num)
theorem B1844461 : Blo 860564 1844461 := bbase (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) (by norm_num)
theorem B1090837 : Blo 860564 1090837 := bbase (se 6 (by rfl) ⟨25566, by rfl⟩ : syracuseStep 1090837 = 51133) (by norm_num)
theorem B1942829 : Blo 860564 1942829 := bbase (se 3 (by rfl) ⟨364280, by rfl⟩ : syracuseStep 1942829 = 728561) (by norm_num)
theorem B1942901 : Blo 860564 1942901 := bbase (se 5 (by rfl) ⟨91073, by rfl⟩ : syracuseStep 1942901 = 182147) (by norm_num)
theorem B1942973 : Blo 860564 1942973 := bbase (se 3 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 1942973 = 728615) (by norm_num)
theorem B1091009 : Blo 860564 1091009 := bbase (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) (by norm_num)
theorem B1091065 : Blo 860564 1091065 := bbase (se 2 (by rfl) ⟨409149, by rfl⟩ : syracuseStep 1091065 = 818299) (by norm_num)
theorem B1943045 : Blo 860564 1943045 := bbase (se 4 (by rfl) ⟨182160, by rfl⟩ : syracuseStep 1943045 = 364321) (by norm_num)
theorem B1943117 : Blo 860564 1943117 := bbase (se 3 (by rfl) ⟨364334, by rfl⟩ : syracuseStep 1943117 = 728669) (by norm_num)
theorem B1746517 : Blo 860564 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B1091161 : Blo 860564 1091161 := bbase (se 2 (by rfl) ⟨409185, by rfl⟩ : syracuseStep 1091161 = 818371) (by norm_num)
theorem B4368005 : Blo 860564 4368005 := bbase (se 4 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 4368005 = 819001) (by norm_num)
theorem B1943189 : Blo 860564 1943189 := bbase (se 6 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 1943189 = 91087) (by norm_num)
theorem B2238173 : Blo 860564 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B1943261 : Blo 860564 1943261 := bbase (se 3 (by rfl) ⟨364361, by rfl⟩ : syracuseStep 1943261 = 728723) (by norm_num)
theorem B1844957 : Blo 860564 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B7874293 : Blo 860564 7874293 := bbase (se 5 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 7874293 = 738215) (by norm_num)
theorem B1091333 : Blo 860564 1091333 := bbase (se 4 (by rfl) ⟨102312, by rfl⟩ : syracuseStep 1091333 = 204625) (by norm_num)
theorem B1943333 : Blo 860564 1943333 := bbase (se 4 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 1943333 = 364375) (by norm_num)
theorem B1091389 : Blo 860564 1091389 := bbase (se 3 (by rfl) ⟨204635, by rfl⟩ : syracuseStep 1091389 = 409271) (by norm_num)
theorem B1943405 : Blo 860564 1943405 := bbase (se 3 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 1943405 = 728777) (by norm_num)
theorem B2074501 : Blo 860564 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B1091485 : Blo 860564 1091485 := bbase (se 3 (by rfl) ⟨204653, by rfl⟩ : syracuseStep 1091485 = 409307) (by norm_num)
theorem B1943477 : Blo 860564 1943477 := bbase (se 5 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 1943477 = 182201) (by norm_num)
theorem B1943549 : Blo 860564 1943549 := bbase (se 3 (by rfl) ⟨364415, by rfl⟩ : syracuseStep 1943549 = 728831) (by norm_num)
theorem B1943621 : Blo 860564 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B1091657 : Blo 860564 1091657 := bbase (se 2 (by rfl) ⟨409371, by rfl⟩ : syracuseStep 1091657 = 818743) (by norm_num)
theorem B1091713 : Blo 860564 1091713 := bbase (se 2 (by rfl) ⟨409392, by rfl⟩ : syracuseStep 1091713 = 818785) (by norm_num)
theorem B1943693 : Blo 860564 1943693 := bbase (se 3 (by rfl) ⟨364442, by rfl⟩ : syracuseStep 1943693 = 728885) (by norm_num)
theorem B1747117 : Blo 860564 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B1943765 : Blo 860564 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B1091809 : Blo 860564 1091809 := bbase (se 2 (by rfl) ⟨409428, by rfl⟩ : syracuseStep 1091809 = 818857) (by norm_num)
theorem B1452269 : Blo 860564 1452269 := bbase (se 3 (by rfl) ⟨272300, by rfl⟩ : syracuseStep 1452269 = 544601) (by norm_num)
theorem B1943837 : Blo 860564 1943837 := bbase (se 3 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 1943837 = 728939) (by norm_num)
theorem B1943909 : Blo 860564 1943909 := bbase (se 4 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 1943909 = 364483) (by norm_num)
theorem B1452397 : Blo 860564 1452397 := bbase (se 3 (by rfl) ⟨272324, by rfl⟩ : syracuseStep 1452397 = 544649) (by norm_num)
theorem B1091981 : Blo 860564 1091981 := bbase (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) (by norm_num)
theorem B1943981 : Blo 860564 1943981 := bbase (se 3 (by rfl) ⟨364496, by rfl⟩ : syracuseStep 1943981 = 728993) (by norm_num)
theorem B2992565 : Blo 860564 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B1452485 : Blo 860564 1452485 := bbase (se 4 (by rfl) ⟨136170, by rfl⟩ : syracuseStep 1452485 = 272341) (by norm_num)
theorem B1092037 : Blo 860564 1092037 := bbase (se 4 (by rfl) ⟨102378, by rfl⟩ : syracuseStep 1092037 = 204757) (by norm_num)
theorem B1944053 : Blo 860564 1944053 := bbase (se 5 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 1944053 = 182255) (by norm_num)
theorem B1092133 : Blo 860564 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B1944125 : Blo 860564 1944125 := bbase (se 3 (by rfl) ⟨364523, by rfl⟩ : syracuseStep 1944125 = 729047) (by norm_num)
theorem B1845821 : Blo 860564 1845821 := bbase (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) (by norm_num)
theorem B1550917 : Blo 860564 1550917 := bbase (se 4 (by rfl) ⟨145398, by rfl⟩ : syracuseStep 1550917 = 290797) (by norm_num)
theorem B1452613 : Blo 860564 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B2075213 : Blo 860564 2075213 := bbase (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) (by norm_num)
theorem B1944197 : Blo 860564 1944197 := bbase (se 4 (by rfl) ⟨182268, by rfl⟩ : syracuseStep 1944197 = 364537) (by norm_num)
theorem B1452701 : Blo 860564 1452701 := bbase (se 3 (by rfl) ⟨272381, by rfl⟩ : syracuseStep 1452701 = 544763) (by norm_num)
theorem B3943093 : Blo 860564 3943093 := bbase (se 5 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 3943093 = 369665) (by norm_num)
theorem B1944269 : Blo 860564 1944269 := bbase (se 3 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 1944269 = 729101) (by norm_num)
theorem B1845965 : Blo 860564 1845965 := bbase (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) (by norm_num)
theorem B1092305 : Blo 860564 1092305 := bbase (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) (by norm_num)
theorem B1092361 : Blo 860564 1092361 := bbase (se 2 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 1092361 = 819271) (by norm_num)
theorem B1944341 : Blo 860564 1944341 := bbase (se 6 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 1944341 = 91141) (by norm_num)
theorem B1452829 : Blo 860564 1452829 := bbase (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) (by norm_num)
theorem B1944413 : Blo 860564 1944413 := bbase (se 3 (by rfl) ⟨364577, by rfl⟩ : syracuseStep 1944413 = 729155) (by norm_num)
theorem B1092457 : Blo 860564 1092457 := bbase (se 2 (by rfl) ⟨409671, by rfl⟩ : syracuseStep 1092457 = 819343) (by norm_num)
theorem B1452917 : Blo 860564 1452917 := bbase (se 5 (by rfl) ⟨68105, by rfl⟩ : syracuseStep 1452917 = 136211) (by norm_num)
theorem B4369301 : Blo 860564 4369301 := bbase (se 6 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 4369301 = 204811) (by norm_num)
theorem B1944485 : Blo 860564 1944485 := bbase (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) (by norm_num)
theorem B2075597 : Blo 860564 2075597 := bbase (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) (by norm_num)
theorem B1944557 : Blo 860564 1944557 := bbase (se 3 (by rfl) ⟨364604, by rfl⟩ : syracuseStep 1944557 = 729209) (by norm_num)
theorem B1453045 : Blo 860564 1453045 := bbase (se 5 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 1453045 = 136223) (by norm_num)
theorem B1092629 : Blo 860564 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B1944629 : Blo 860564 1944629 := bbase (se 5 (by rfl) ⟨91154, by rfl⟩ : syracuseStep 1944629 = 182309) (by norm_num)
theorem B1453133 : Blo 860564 1453133 := bbase (se 3 (by rfl) ⟨272462, by rfl⟩ : syracuseStep 1453133 = 544925) (by norm_num)
theorem B1092685 : Blo 860564 1092685 := bbase (se 3 (by rfl) ⟨204878, by rfl⟩ : syracuseStep 1092685 = 409757) (by norm_num)
theorem B1944701 : Blo 860564 1944701 := bbase (se 3 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 1944701 = 729263) (by norm_num)
theorem B4140197 : Blo 860564 4140197 := bbase (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) (by norm_num)
theorem B1092781 : Blo 860564 1092781 := bbase (se 3 (by rfl) ⟨204896, by rfl⟩ : syracuseStep 1092781 = 409793) (by norm_num)
theorem B1944773 : Blo 860564 1944773 := bbase (se 4 (by rfl) ⟨182322, by rfl⟩ : syracuseStep 1944773 = 364645) (by norm_num)
theorem B1453261 : Blo 860564 1453261 := bbase (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) (by norm_num)
theorem B2075885 : Blo 860564 2075885 := bbase (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) (by norm_num)
theorem B3681541 : Blo 860564 3681541 := bbase (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) (by norm_num)
theorem B1944845 : Blo 860564 1944845 := bbase (se 3 (by rfl) ⟨364658, by rfl⟩ : syracuseStep 1944845 = 729317) (by norm_num)
theorem B1453349 : Blo 860564 1453349 := bbase (se 4 (by rfl) ⟨136251, by rfl⟩ : syracuseStep 1453349 = 272503) (by norm_num)
theorem B1748285 : Blo 860564 1748285 := bbase (se 3 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 1748285 = 655607) (by norm_num)
theorem B7384405 : Blo 860564 7384405 := bbase (se 11 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 7384405 = 10817) (by norm_num)
theorem B1944917 : Blo 860564 1944917 := bbase (se 11 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 1944917 = 2849) (by norm_num)
theorem B1092953 : Blo 860564 1092953 := bbase (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) (by norm_num)
theorem B1093009 : Blo 860564 1093009 := bbase (se 2 (by rfl) ⟨409878, by rfl⟩ : syracuseStep 1093009 = 819757) (by norm_num)
theorem B2764181 : Blo 860564 2764181 := bbase (se 6 (by rfl) ⟨64785, by rfl⟩ : syracuseStep 2764181 = 129571) (by norm_num)
theorem B1944989 : Blo 860564 1944989 := bbase (se 3 (by rfl) ⟨364685, by rfl⟩ : syracuseStep 1944989 = 729371) (by norm_num)
theorem B1453477 : Blo 860564 1453477 := bbase (se 4 (by rfl) ⟨136263, by rfl⟩ : syracuseStep 1453477 = 272527) (by norm_num)
theorem B5385685 : Blo 860564 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B1945061 : Blo 860564 1945061 := bbase (se 4 (by rfl) ⟨182349, by rfl⟩ : syracuseStep 1945061 = 364699) (by norm_num)
theorem B1093105 : Blo 860564 1093105 := bbase (se 2 (by rfl) ⟨409914, by rfl⟩ : syracuseStep 1093105 = 819829) (by norm_num)
theorem B1453565 : Blo 860564 1453565 := bbase (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) (by norm_num)
theorem B1945133 : Blo 860564 1945133 := bbase (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) (by norm_num)
theorem B3321445 : Blo 860564 3321445 := bbase (se 4 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 3321445 = 622771) (by norm_num)
theorem B1945205 : Blo 860564 1945205 := bbase (se 5 (by rfl) ⟨91181, by rfl⟩ : syracuseStep 1945205 = 182363) (by norm_num)
theorem B1453693 : Blo 860564 1453693 := bbase (se 3 (by rfl) ⟨272567, by rfl⟩ : syracuseStep 1453693 = 545135) (by norm_num)
theorem B1093277 : Blo 860564 1093277 := bbase (se 3 (by rfl) ⟨204989, by rfl⟩ : syracuseStep 1093277 = 409979) (by norm_num)
theorem B5516981 : Blo 860564 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B1453781 : Blo 860564 1453781 := bbase (se 7 (by rfl) ⟨17036, by rfl⟩ : syracuseStep 1453781 = 34073) (by norm_num)
theorem B1093333 : Blo 860564 1093333 := bbase (se 7 (by rfl) ⟨12812, by rfl⟩ : syracuseStep 1093333 = 25625) (by norm_num)
theorem B3550949 : Blo 860564 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B4665077 : Blo 860564 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B5254901 : Blo 860564 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B1093429 : Blo 860564 1093429 := bbase (se 5 (by rfl) ⟨51254, by rfl⟩ : syracuseStep 1093429 = 102509) (by norm_num)
theorem B1453909 : Blo 860564 1453909 := bbase (se 9 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 1453909 = 8519) (by norm_num)
theorem B4665205 : Blo 860564 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B1552301 : Blo 860564 1552301 := bbase (se 3 (by rfl) ⟨291056, by rfl⟩ : syracuseStep 1552301 = 582113) (by norm_num)
theorem B1453997 : Blo 860564 1453997 := bbase (se 3 (by rfl) ⟨272624, by rfl⟩ : syracuseStep 1453997 = 545249) (by norm_num)
theorem B1093601 : Blo 860564 1093601 := bbase (se 2 (by rfl) ⟨410100, by rfl⟩ : syracuseStep 1093601 = 820201) (by norm_num)
theorem B1093657 : Blo 860564 1093657 := bbase (se 2 (by rfl) ⟨410121, by rfl⟩ : syracuseStep 1093657 = 820243) (by norm_num)
theorem B1454125 : Blo 860564 1454125 := bbase (se 3 (by rfl) ⟨272648, by rfl⟩ : syracuseStep 1454125 = 545297) (by norm_num)
theorem B1093753 : Blo 860564 1093753 := bbase (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) (by norm_num)
theorem B1454213 : Blo 860564 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B4370597 : Blo 860564 4370597 := bbase (se 4 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 4370597 = 819487) (by norm_num)
theorem B1454341 : Blo 860564 1454341 := bbase (se 4 (by rfl) ⟨136344, by rfl⟩ : syracuseStep 1454341 = 272689) (by norm_num)
theorem B1093925 : Blo 860564 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B1454429 : Blo 860564 1454429 := bbase (se 3 (by rfl) ⟨272705, by rfl⟩ : syracuseStep 1454429 = 545411) (by norm_num)
theorem B1093981 : Blo 860564 1093981 := bbase (se 3 (by rfl) ⟨205121, by rfl⟩ : syracuseStep 1093981 = 410243) (by norm_num)
theorem B1094077 : Blo 860564 1094077 := bbase (se 3 (by rfl) ⟨205139, by rfl⟩ : syracuseStep 1094077 = 410279) (by norm_num)
theorem B1454557 : Blo 860564 1454557 := bbase (se 3 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 1454557 = 545459) (by norm_num)
theorem B2241037 : Blo 860564 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1454645 : Blo 860564 1454645 := bbase (se 5 (by rfl) ⟨68186, by rfl⟩ : syracuseStep 1454645 = 136373) (by norm_num)
theorem B1290869 : Blo 860564 1290869 := bbase (se 5 (by rfl) ⟨60509, by rfl⟩ : syracuseStep 1290869 = 121019) (by norm_num)
theorem B1290893 : Blo 860564 1290893 := bbase (se 3 (by rfl) ⟨242042, by rfl⟩ : syracuseStep 1290893 = 484085) (by norm_num)
theorem B1290917 : Blo 860564 1290917 := bbase (se 4 (by rfl) ⟨121023, by rfl⟩ : syracuseStep 1290917 = 242047) (by norm_num)
theorem B1225381 : Blo 860564 1225381 := bbase (se 4 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 1225381 = 229759) (by norm_num)
theorem B1454773 : Blo 860564 1454773 := bbase (se 5 (by rfl) ⟨68192, by rfl⟩ : syracuseStep 1454773 = 136385) (by norm_num)
theorem B1290941 : Blo 860564 1290941 := bbase (se 3 (by rfl) ⟨242051, by rfl⟩ : syracuseStep 1290941 = 484103) (by norm_num)
theorem B1290965 : Blo 860564 1290965 := bbase (se 7 (by rfl) ⟨15128, by rfl⟩ : syracuseStep 1290965 = 30257) (by norm_num)
theorem B3683029 : Blo 860564 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B3683045 : Blo 860564 3683045 := bbase (se 4 (by rfl) ⟨345285, by rfl⟩ : syracuseStep 3683045 = 690571) (by norm_num)
theorem B1290989 : Blo 860564 1290989 := bbase (se 3 (by rfl) ⟨242060, by rfl⟩ : syracuseStep 1290989 = 484121) (by norm_num)
theorem B4141813 : Blo 860564 4141813 := bbase (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) (by norm_num)
theorem B1291013 : Blo 860564 1291013 := bbase (se 4 (by rfl) ⟨121032, by rfl⟩ : syracuseStep 1291013 = 242065) (by norm_num)
theorem B1454861 : Blo 860564 1454861 := bbase (se 3 (by rfl) ⟨272786, by rfl⟩ : syracuseStep 1454861 = 545573) (by norm_num)
theorem B1291037 : Blo 860564 1291037 := bbase (se 3 (by rfl) ⟨242069, by rfl⟩ : syracuseStep 1291037 = 484139) (by norm_num)
theorem B1291061 : Blo 860564 1291061 := bbase (se 5 (by rfl) ⟨60518, by rfl⟩ : syracuseStep 1291061 = 121037) (by norm_num)
theorem B1291085 : Blo 860564 1291085 := bbase (se 3 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 1291085 = 484157) (by norm_num)
theorem B1684309 : Blo 860564 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B1291109 : Blo 860564 1291109 := bbase (se 4 (by rfl) ⟨121041, by rfl⟩ : syracuseStep 1291109 = 242083) (by norm_num)
theorem B2208629 : Blo 860564 2208629 := bbase (se 5 (by rfl) ⟨103529, by rfl⟩ : syracuseStep 2208629 = 207059) (by norm_num)
theorem B1291133 : Blo 860564 1291133 := bbase (se 3 (by rfl) ⟨242087, by rfl⟩ : syracuseStep 1291133 = 484175) (by norm_num)
theorem B1454989 : Blo 860564 1454989 := bbase (se 3 (by rfl) ⟨272810, by rfl⟩ : syracuseStep 1454989 = 545621) (by norm_num)
theorem B1291157 : Blo 860564 1291157 := bbase (se 6 (by rfl) ⟨30261, by rfl⟩ : syracuseStep 1291157 = 60523) (by norm_num)
theorem B1291181 : Blo 860564 1291181 := bbase (se 3 (by rfl) ⟨242096, by rfl⟩ : syracuseStep 1291181 = 484193) (by norm_num)
theorem B1291205 : Blo 860564 1291205 := bbase (se 4 (by rfl) ⟨121050, by rfl⟩ : syracuseStep 1291205 = 242101) (by norm_num)
theorem B1291229 : Blo 860564 1291229 := bbase (se 3 (by rfl) ⟨242105, by rfl⟩ : syracuseStep 1291229 = 484211) (by norm_num)
theorem B1455077 : Blo 860564 1455077 := bbase (se 4 (by rfl) ⟨136413, by rfl⟩ : syracuseStep 1455077 = 272827) (by norm_num)
theorem B1291253 : Blo 860564 1291253 := bbase (se 5 (by rfl) ⟨60527, by rfl⟩ : syracuseStep 1291253 = 121055) (by norm_num)
theorem B1291277 : Blo 860564 1291277 := bbase (se 3 (by rfl) ⟨242114, by rfl⟩ : syracuseStep 1291277 = 484229) (by norm_num)
theorem B1291301 : Blo 860564 1291301 := bbase (se 4 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 1291301 = 242119) (by norm_num)
theorem B1291325 : Blo 860564 1291325 := bbase (se 3 (by rfl) ⟨242123, by rfl⟩ : syracuseStep 1291325 = 484247) (by norm_num)
theorem B1291349 : Blo 860564 1291349 := bbase (se 8 (by rfl) ⟨7566, by rfl⟩ : syracuseStep 1291349 = 15133) (by norm_num)
theorem B1455205 : Blo 860564 1455205 := bbase (se 4 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 1455205 = 272851) (by norm_num)
theorem B1291373 : Blo 860564 1291373 := bbase (se 3 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 1291373 = 484265) (by norm_num)
theorem B1291397 : Blo 860564 1291397 := bbase (se 4 (by rfl) ⟨121068, by rfl⟩ : syracuseStep 1291397 = 242137) (by norm_num)
theorem B1291421 : Blo 860564 1291421 := bbase (se 3 (by rfl) ⟨242141, by rfl⟩ : syracuseStep 1291421 = 484283) (by norm_num)
theorem B3323045 : Blo 860564 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B1291445 : Blo 860564 1291445 := bbase (se 5 (by rfl) ⟨60536, by rfl⟩ : syracuseStep 1291445 = 121073) (by norm_num)
theorem B1455293 : Blo 860564 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B1291469 : Blo 860564 1291469 := bbase (se 3 (by rfl) ⟨242150, by rfl⟩ : syracuseStep 1291469 = 484301) (by norm_num)
theorem B1291493 : Blo 860564 1291493 := bbase (se 4 (by rfl) ⟨121077, by rfl⟩ : syracuseStep 1291493 = 242155) (by norm_num)
theorem B1225973 : Blo 860564 1225973 := bbase (se 5 (by rfl) ⟨57467, by rfl⟩ : syracuseStep 1225973 = 114935) (by norm_num)
theorem B1291517 : Blo 860564 1291517 := bbase (se 3 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 1291517 = 484319) (by norm_num)
theorem B1291541 : Blo 860564 1291541 := bbase (se 6 (by rfl) ⟨30270, by rfl⟩ : syracuseStep 1291541 = 60541) (by norm_num)
theorem B1291565 : Blo 860564 1291565 := bbase (se 3 (by rfl) ⟨242168, by rfl⟩ : syracuseStep 1291565 = 484337) (by norm_num)
theorem B1455421 : Blo 860564 1455421 := bbase (se 3 (by rfl) ⟨272891, by rfl⟩ : syracuseStep 1455421 = 545783) (by norm_num)
theorem B1291589 : Blo 860564 1291589 := bbase (se 4 (by rfl) ⟨121086, by rfl⟩ : syracuseStep 1291589 = 242173) (by norm_num)
theorem B1226053 : Blo 860564 1226053 := bbase (se 4 (by rfl) ⟨114942, by rfl⟩ : syracuseStep 1226053 = 229885) (by norm_num)
theorem B1291613 : Blo 860564 1291613 := bbase (se 3 (by rfl) ⟨242177, by rfl⟩ : syracuseStep 1291613 = 484355) (by norm_num)
theorem B1291637 : Blo 860564 1291637 := bbase (se 5 (by rfl) ⟨60545, by rfl⟩ : syracuseStep 1291637 = 121091) (by norm_num)
theorem B1291661 : Blo 860564 1291661 := bbase (se 3 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 1291661 = 484373) (by norm_num)
theorem B1455509 : Blo 860564 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B1291685 : Blo 860564 1291685 := bbase (se 4 (by rfl) ⟨121095, by rfl⟩ : syracuseStep 1291685 = 242191) (by norm_num)
theorem B4371893 : Blo 860564 4371893 := bbase (se 5 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 4371893 = 409865) (by norm_num)
theorem B1291709 : Blo 860564 1291709 := bbase (se 3 (by rfl) ⟨242195, by rfl⟩ : syracuseStep 1291709 = 484391) (by norm_num)
theorem B1226173 : Blo 860564 1226173 := bbase (se 3 (by rfl) ⟨229907, by rfl⟩ : syracuseStep 1226173 = 459815) (by norm_num)
theorem B1291733 : Blo 860564 1291733 := bbase (se 7 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 1291733 = 30275) (by norm_num)
theorem B1291757 : Blo 860564 1291757 := bbase (se 3 (by rfl) ⟨242204, by rfl⟩ : syracuseStep 1291757 = 484409) (by norm_num)
theorem B1291781 : Blo 860564 1291781 := bbase (se 4 (by rfl) ⟨121104, by rfl⟩ : syracuseStep 1291781 = 242209) (by norm_num)
theorem B1455637 : Blo 860564 1455637 := bbase (se 6 (by rfl) ⟨34116, by rfl⟩ : syracuseStep 1455637 = 68233) (by norm_num)
theorem B1291805 : Blo 860564 1291805 := bbase (se 3 (by rfl) ⟨242213, by rfl⟩ : syracuseStep 1291805 = 484427) (by norm_num)
theorem B1226269 : Blo 860564 1226269 := bbase (se 3 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 1226269 = 459851) (by norm_num)
theorem B1291829 : Blo 860564 1291829 := bbase (se 5 (by rfl) ⟨60554, by rfl⟩ : syracuseStep 1291829 = 121109) (by norm_num)
theorem B1291853 : Blo 860564 1291853 := bbase (se 3 (by rfl) ⟨242222, by rfl⟩ : syracuseStep 1291853 = 484445) (by norm_num)
theorem B40416853 : Blo 860564 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B1291877 : Blo 860564 1291877 := bbase (se 4 (by rfl) ⟨121113, by rfl⟩ : syracuseStep 1291877 = 242227) (by norm_num)
theorem B2766437 : Blo 860564 2766437 := bbase (se 4 (by rfl) ⟨259353, by rfl⟩ : syracuseStep 2766437 = 518707) (by norm_num)
theorem B1455725 : Blo 860564 1455725 := bbase (se 3 (by rfl) ⟨272948, by rfl⟩ : syracuseStep 1455725 = 545897) (by norm_num)
theorem B1291901 : Blo 860564 1291901 := bbase (se 3 (by rfl) ⟨242231, by rfl⟩ : syracuseStep 1291901 = 484463) (by norm_num)
theorem B1291925 : Blo 860564 1291925 := bbase (se 6 (by rfl) ⟨30279, by rfl⟩ : syracuseStep 1291925 = 60559) (by norm_num)
theorem B1291949 : Blo 860564 1291949 := bbase (se 3 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 1291949 = 484481) (by norm_num)
theorem B1291973 : Blo 860564 1291973 := bbase (se 4 (by rfl) ⟨121122, by rfl⟩ : syracuseStep 1291973 = 242245) (by norm_num)
theorem B1291997 : Blo 860564 1291997 := bbase (se 3 (by rfl) ⟨242249, by rfl⟩ : syracuseStep 1291997 = 484499) (by norm_num)
theorem B1455853 : Blo 860564 1455853 := bbase (se 3 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 1455853 = 545945) (by norm_num)
theorem B1292021 : Blo 860564 1292021 := bbase (se 5 (by rfl) ⟨60563, by rfl⟩ : syracuseStep 1292021 = 121127) (by norm_num)
theorem B1292045 : Blo 860564 1292045 := bbase (se 3 (by rfl) ⟨242258, by rfl⟩ : syracuseStep 1292045 = 484517) (by norm_num)
theorem B1292069 : Blo 860564 1292069 := bbase (se 4 (by rfl) ⟨121131, by rfl⟩ : syracuseStep 1292069 = 242263) (by norm_num)
theorem B1292093 : Blo 860564 1292093 := bbase (se 3 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 1292093 = 484535) (by norm_num)
theorem B1455941 : Blo 860564 1455941 := bbase (se 4 (by rfl) ⟨136494, by rfl⟩ : syracuseStep 1455941 = 272989) (by norm_num)
theorem B1292117 : Blo 860564 1292117 := bbase (se 9 (by rfl) ⟨3785, by rfl⟩ : syracuseStep 1292117 = 7571) (by norm_num)
theorem B1292141 : Blo 860564 1292141 := bbase (se 3 (by rfl) ⟨242276, by rfl⟩ : syracuseStep 1292141 = 484553) (by norm_num)
theorem B1292165 : Blo 860564 1292165 := bbase (se 4 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 1292165 = 242281) (by norm_num)
theorem B1292189 : Blo 860564 1292189 := bbase (se 3 (by rfl) ⟨242285, by rfl⟩ : syracuseStep 1292189 = 484571) (by norm_num)
theorem B1292213 : Blo 860564 1292213 := bbase (se 5 (by rfl) ⟨60572, by rfl⟩ : syracuseStep 1292213 = 121145) (by norm_num)
theorem B1456069 : Blo 860564 1456069 := bbase (se 4 (by rfl) ⟨136506, by rfl⟩ : syracuseStep 1456069 = 273013) (by norm_num)
theorem B1292237 : Blo 860564 1292237 := bbase (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) (by norm_num)
theorem B1292261 : Blo 860564 1292261 := bbase (se 4 (by rfl) ⟨121149, by rfl⟩ : syracuseStep 1292261 = 242299) (by norm_num)
theorem B1292285 : Blo 860564 1292285 := bbase (se 3 (by rfl) ⟨242303, by rfl⟩ : syracuseStep 1292285 = 484607) (by norm_num)
theorem B1226765 : Blo 860564 1226765 := bbase (se 3 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 1226765 = 460037) (by norm_num)
theorem B1292309 : Blo 860564 1292309 := bbase (se 6 (by rfl) ⟨30288, by rfl⟩ : syracuseStep 1292309 = 60577) (by norm_num)
theorem B1456157 : Blo 860564 1456157 := bbase (se 3 (by rfl) ⟨273029, by rfl⟩ : syracuseStep 1456157 = 546059) (by norm_num)
theorem B1292333 : Blo 860564 1292333 := bbase (se 3 (by rfl) ⟨242312, by rfl⟩ : syracuseStep 1292333 = 484625) (by norm_num)
theorem B1292357 : Blo 860564 1292357 := bbase (se 4 (by rfl) ⟨121158, by rfl⟩ : syracuseStep 1292357 = 242317) (by norm_num)
theorem B1292381 : Blo 860564 1292381 := bbase (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) (by norm_num)
theorem B1292405 : Blo 860564 1292405 := bbase (se 5 (by rfl) ⟨60581, by rfl⟩ : syracuseStep 1292405 = 121163) (by norm_num)
theorem B1554565 : Blo 860564 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B1292429 : Blo 860564 1292429 := bbase (se 3 (by rfl) ⟨242330, by rfl⟩ : syracuseStep 1292429 = 484661) (by norm_num)
theorem B1456285 : Blo 860564 1456285 := bbase (se 3 (by rfl) ⟨273053, by rfl⟩ : syracuseStep 1456285 = 546107) (by norm_num)
theorem B1292453 : Blo 860564 1292453 := bbase (se 4 (by rfl) ⟨121167, by rfl⟩ : syracuseStep 1292453 = 242335) (by norm_num)
theorem B1292477 : Blo 860564 1292477 := bbase (se 3 (by rfl) ⟨242339, by rfl⟩ : syracuseStep 1292477 = 484679) (by norm_num)
theorem B1292501 : Blo 860564 1292501 := bbase (se 7 (by rfl) ⟨15146, by rfl⟩ : syracuseStep 1292501 = 30293) (by norm_num)
theorem B1292525 : Blo 860564 1292525 := bbase (se 3 (by rfl) ⟨242348, by rfl⟩ : syracuseStep 1292525 = 484697) (by norm_num)
theorem B1456373 : Blo 860564 1456373 := bbase (se 5 (by rfl) ⟨68267, by rfl⟩ : syracuseStep 1456373 = 136535) (by norm_num)
theorem B1292549 : Blo 860564 1292549 := bbase (se 4 (by rfl) ⟨121176, by rfl⟩ : syracuseStep 1292549 = 242353) (by norm_num)
theorem B1292573 : Blo 860564 1292573 := bbase (se 3 (by rfl) ⟨242357, by rfl⟩ : syracuseStep 1292573 = 484715) (by norm_num)
theorem B1292597 : Blo 860564 1292597 := bbase (se 5 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 1292597 = 121181) (by norm_num)
theorem B1292621 : Blo 860564 1292621 := bbase (se 3 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 1292621 = 484733) (by norm_num)
theorem B16202069 : Blo 860564 16202069 := bbase (se 10 (by rfl) ⟨23733, by rfl⟩ : syracuseStep 16202069 = 47467) (by norm_num)
theorem B1292645 : Blo 860564 1292645 := bbase (se 4 (by rfl) ⟨121185, by rfl⟩ : syracuseStep 1292645 = 242371) (by norm_num)
theorem B2767205 : Blo 860564 2767205 := bbase (se 4 (by rfl) ⟨259425, by rfl⟩ : syracuseStep 2767205 = 518851) (by norm_num)
theorem B1456501 : Blo 860564 1456501 := bbase (se 5 (by rfl) ⟨68273, by rfl⟩ : syracuseStep 1456501 = 136547) (by norm_num)
theorem B1292669 : Blo 860564 1292669 := bbase (se 3 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 1292669 = 484751) (by norm_num)
theorem B1292693 : Blo 860564 1292693 := bbase (se 6 (by rfl) ⟨30297, by rfl⟩ : syracuseStep 1292693 = 60595) (by norm_num)
theorem B1292717 : Blo 860564 1292717 := bbase (se 3 (by rfl) ⟨242384, by rfl⟩ : syracuseStep 1292717 = 484769) (by norm_num)
theorem B1292741 : Blo 860564 1292741 := bbase (se 4 (by rfl) ⟨121194, by rfl⟩ : syracuseStep 1292741 = 242389) (by norm_num)
theorem B1456589 : Blo 860564 1456589 := bbase (se 3 (by rfl) ⟨273110, by rfl⟩ : syracuseStep 1456589 = 546221) (by norm_num)
theorem B1292765 : Blo 860564 1292765 := bbase (se 3 (by rfl) ⟨242393, by rfl⟩ : syracuseStep 1292765 = 484787) (by norm_num)
theorem B1292789 : Blo 860564 1292789 := bbase (se 5 (by rfl) ⟨60599, by rfl⟩ : syracuseStep 1292789 = 121199) (by norm_num)
theorem B1292813 : Blo 860564 1292813 := bbase (se 3 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 1292813 = 484805) (by norm_num)
theorem B1292837 : Blo 860564 1292837 := bbase (se 4 (by rfl) ⟨121203, by rfl⟩ : syracuseStep 1292837 = 242407) (by norm_num)
theorem B1227317 : Blo 860564 1227317 := bbase (se 5 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 1227317 = 115061) (by norm_num)
theorem B1292861 : Blo 860564 1292861 := bbase (se 3 (by rfl) ⟨242411, by rfl⟩ : syracuseStep 1292861 = 484823) (by norm_num)
theorem B1456717 : Blo 860564 1456717 := bbase (se 3 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 1456717 = 546269) (by norm_num)
theorem B1292885 : Blo 860564 1292885 := bbase (se 8 (by rfl) ⟨7575, by rfl⟩ : syracuseStep 1292885 = 15151) (by norm_num)
theorem B1292909 : Blo 860564 1292909 := bbase (se 3 (by rfl) ⟨242420, by rfl⟩ : syracuseStep 1292909 = 484841) (by norm_num)
theorem B1292933 : Blo 860564 1292933 := bbase (se 4 (by rfl) ⟨121212, by rfl⟩ : syracuseStep 1292933 = 242425) (by norm_num)
theorem B10074773 : Blo 860564 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B1292957 : Blo 860564 1292957 := bbase (se 3 (by rfl) ⟨242429, by rfl⟩ : syracuseStep 1292957 = 484859) (by norm_num)
theorem B1456805 : Blo 860564 1456805 := bbase (se 4 (by rfl) ⟨136575, by rfl⟩ : syracuseStep 1456805 = 273151) (by norm_num)
theorem B1292981 : Blo 860564 1292981 := bbase (se 5 (by rfl) ⟨60608, by rfl⟩ : syracuseStep 1292981 = 121217) (by norm_num)
theorem B4373189 : Blo 860564 4373189 := bbase (se 4 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 4373189 = 819973) (by norm_num)
theorem B1293005 : Blo 860564 1293005 := bbase (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) (by norm_num)
theorem B1293029 : Blo 860564 1293029 := bbase (se 4 (by rfl) ⟨121221, by rfl⟩ : syracuseStep 1293029 = 242443) (by norm_num)
theorem B1293053 : Blo 860564 1293053 := bbase (se 3 (by rfl) ⟨242447, by rfl⟩ : syracuseStep 1293053 = 484895) (by norm_num)
theorem B1293077 : Blo 860564 1293077 := bbase (se 6 (by rfl) ⟨30306, by rfl⟩ : syracuseStep 1293077 = 60613) (by norm_num)
theorem B1456933 : Blo 860564 1456933 := bbase (se 4 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 1456933 = 273175) (by norm_num)
theorem B1293101 : Blo 860564 1293101 := bbase (se 3 (by rfl) ⟨242456, by rfl⟩ : syracuseStep 1293101 = 484913) (by norm_num)
theorem B1293125 : Blo 860564 1293125 := bbase (se 4 (by rfl) ⟨121230, by rfl⟩ : syracuseStep 1293125 = 242461) (by norm_num)
theorem B1293149 : Blo 860564 1293149 := bbase (se 3 (by rfl) ⟨242465, by rfl⟩ : syracuseStep 1293149 = 484931) (by norm_num)
theorem B2767717 : Blo 860564 2767717 := bbase (se 4 (by rfl) ⟨259473, by rfl⟩ : syracuseStep 2767717 = 518947) (by norm_num)
theorem B1293173 : Blo 860564 1293173 := bbase (se 5 (by rfl) ⟨60617, by rfl⟩ : syracuseStep 1293173 = 121235) (by norm_num)
theorem B1457021 : Blo 860564 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B1293197 : Blo 860564 1293197 := bbase (se 3 (by rfl) ⟨242474, by rfl⟩ : syracuseStep 1293197 = 484949) (by norm_num)
theorem B1293221 : Blo 860564 1293221 := bbase (se 4 (by rfl) ⟨121239, by rfl⟩ : syracuseStep 1293221 = 242479) (by norm_num)
theorem B3685301 : Blo 860564 3685301 := bbase (se 5 (by rfl) ⟨172748, by rfl⟩ : syracuseStep 3685301 = 345497) (by norm_num)
theorem B1293245 : Blo 860564 1293245 := bbase (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) (by norm_num)
theorem B1293269 : Blo 860564 1293269 := bbase (se 7 (by rfl) ⟨15155, by rfl⟩ : syracuseStep 1293269 = 30311) (by norm_num)
theorem B1293293 : Blo 860564 1293293 := bbase (se 3 (by rfl) ⟨242492, by rfl⟩ : syracuseStep 1293293 = 484985) (by norm_num)
theorem B1457149 : Blo 860564 1457149 := bbase (se 3 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 1457149 = 546431) (by norm_num)
theorem B1293317 : Blo 860564 1293317 := bbase (se 4 (by rfl) ⟨121248, by rfl⟩ : syracuseStep 1293317 = 242497) (by norm_num)
theorem B6536213 : Blo 860564 6536213 := bbase (se 6 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 6536213 = 306385) (by norm_num)
theorem B1293341 : Blo 860564 1293341 := bbase (se 3 (by rfl) ⟨242501, by rfl⟩ : syracuseStep 1293341 = 485003) (by norm_num)
theorem B1293365 : Blo 860564 1293365 := bbase (se 5 (by rfl) ⟨60626, by rfl⟩ : syracuseStep 1293365 = 121253) (by norm_num)
theorem B1293389 : Blo 860564 1293389 := bbase (se 3 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 1293389 = 485021) (by norm_num)
theorem B1457237 : Blo 860564 1457237 := bbase (se 8 (by rfl) ⟨8538, by rfl⟩ : syracuseStep 1457237 = 17077) (by norm_num)
theorem B1293413 : Blo 860564 1293413 := bbase (se 4 (by rfl) ⟨121257, by rfl⟩ : syracuseStep 1293413 = 242515) (by norm_num)
theorem B1293437 : Blo 860564 1293437 := bbase (se 3 (by rfl) ⟨242519, by rfl⟩ : syracuseStep 1293437 = 485039) (by norm_num)
theorem B1293461 : Blo 860564 1293461 := bbase (se 6 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 1293461 = 60631) (by norm_num)
theorem B1293485 : Blo 860564 1293485 := bbase (se 3 (by rfl) ⟨242528, by rfl⟩ : syracuseStep 1293485 = 485057) (by norm_num)
theorem B1293509 : Blo 860564 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B1457365 : Blo 860564 1457365 := bbase (se 7 (by rfl) ⟨17078, by rfl⟩ : syracuseStep 1457365 = 34157) (by norm_num)
theorem B1293533 : Blo 860564 1293533 := bbase (se 3 (by rfl) ⟨242537, by rfl⟩ : syracuseStep 1293533 = 485075) (by norm_num)
theorem B1293557 : Blo 860564 1293557 := bbase (se 5 (by rfl) ⟨60635, by rfl⟩ : syracuseStep 1293557 = 121271) (by norm_num)
theorem B933125 : Blo 860564 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B1293581 : Blo 860564 1293581 := bbase (se 3 (by rfl) ⟨242546, by rfl⟩ : syracuseStep 1293581 = 485093) (by norm_num)
theorem B1293605 : Blo 860564 1293605 := bbase (se 4 (by rfl) ⟨121275, by rfl⟩ : syracuseStep 1293605 = 242551) (by norm_num)
theorem B1228069 : Blo 860564 1228069 := bbase (se 4 (by rfl) ⟨115131, by rfl⟩ : syracuseStep 1228069 = 230263) (by norm_num)
theorem B1457453 : Blo 860564 1457453 := bbase (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) (by norm_num)
theorem B2997557 : Blo 860564 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1293629 : Blo 860564 1293629 := bbase (se 3 (by rfl) ⟨242555, by rfl⟩ : syracuseStep 1293629 = 485111) (by norm_num)
theorem B2178373 : Blo 860564 2178373 := bbase (se 4 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 2178373 = 408445) (by norm_num)
theorem B1293653 : Blo 860564 1293653 := bbase (se 11 (by rfl) ⟨947, by rfl⟩ : syracuseStep 1293653 = 1895) (by norm_num)
theorem B1293677 : Blo 860564 1293677 := bbase (se 3 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 1293677 = 485129) (by norm_num)
theorem B1752437 : Blo 860564 1752437 := bbase (se 5 (by rfl) ⟨82145, by rfl⟩ : syracuseStep 1752437 = 164291) (by norm_num)
theorem B1293701 : Blo 860564 1293701 := bbase (se 4 (by rfl) ⟨121284, by rfl⟩ : syracuseStep 1293701 = 242569) (by norm_num)
theorem B1293725 : Blo 860564 1293725 := bbase (se 3 (by rfl) ⟨242573, by rfl⟩ : syracuseStep 1293725 = 485147) (by norm_num)
theorem B1457581 : Blo 860564 1457581 := bbase (se 3 (by rfl) ⟨273296, by rfl⟩ : syracuseStep 1457581 = 546593) (by norm_num)
theorem B2178485 : Blo 860564 2178485 := bbase (se 5 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 2178485 = 204233) (by norm_num)
theorem B1293749 : Blo 860564 1293749 := bbase (se 5 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 1293749 = 121289) (by norm_num)
theorem B1293773 : Blo 860564 1293773 := bbase (se 3 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 1293773 = 485165) (by norm_num)
theorem B1293797 : Blo 860564 1293797 := bbase (se 4 (by rfl) ⟨121293, by rfl⟩ : syracuseStep 1293797 = 242587) (by norm_num)
theorem B1555949 : Blo 860564 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B1293821 : Blo 860564 1293821 := bbase (se 3 (by rfl) ⟨242591, by rfl⟩ : syracuseStep 1293821 = 485183) (by norm_num)
theorem B1457669 : Blo 860564 1457669 := bbase (se 4 (by rfl) ⟨136656, by rfl⟩ : syracuseStep 1457669 = 273313) (by norm_num)
theorem B1293845 : Blo 860564 1293845 := bbase (se 6 (by rfl) ⟨30324, by rfl⟩ : syracuseStep 1293845 = 60649) (by norm_num)
theorem B1293869 : Blo 860564 1293869 := bbase (se 3 (by rfl) ⟨242600, by rfl⟩ : syracuseStep 1293869 = 485201) (by norm_num)
theorem B1293893 : Blo 860564 1293893 := bbase (se 4 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 1293893 = 242605) (by norm_num)
theorem B1293917 : Blo 860564 1293917 := bbase (se 3 (by rfl) ⟨242609, by rfl⟩ : syracuseStep 1293917 = 485219) (by norm_num)
theorem B2178677 : Blo 860564 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B1293941 : Blo 860564 1293941 := bbase (se 5 (by rfl) ⟨60653, by rfl⟩ : syracuseStep 1293941 = 121307) (by norm_num)
theorem B1457797 : Blo 860564 1457797 := bbase (se 4 (by rfl) ⟨136668, by rfl⟩ : syracuseStep 1457797 = 273337) (by norm_num)
theorem B1293965 : Blo 860564 1293965 := bbase (se 3 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 1293965 = 485237) (by norm_num)
theorem B4210325 : Blo 860564 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B1293989 : Blo 860564 1293989 := bbase (se 4 (by rfl) ⟨121311, by rfl⟩ : syracuseStep 1293989 = 242623) (by norm_num)
theorem B1294013 : Blo 860564 1294013 := bbase (se 3 (by rfl) ⟨242627, by rfl⟩ : syracuseStep 1294013 = 485255) (by norm_num)
theorem B1556165 : Blo 860564 1556165 := bbase (se 4 (by rfl) ⟨145890, by rfl⟩ : syracuseStep 1556165 = 291781) (by norm_num)
theorem B1294037 : Blo 860564 1294037 := bbase (se 7 (by rfl) ⟨15164, by rfl⟩ : syracuseStep 1294037 = 30329) (by norm_num)
theorem B1457885 : Blo 860564 1457885 := bbase (se 3 (by rfl) ⟨273353, by rfl⟩ : syracuseStep 1457885 = 546707) (by norm_num)
theorem B1294061 : Blo 860564 1294061 := bbase (se 3 (by rfl) ⟨242636, by rfl⟩ : syracuseStep 1294061 = 485273) (by norm_num)
theorem B1294085 : Blo 860564 1294085 := bbase (se 4 (by rfl) ⟨121320, by rfl⟩ : syracuseStep 1294085 = 242641) (by norm_num)
theorem B1326869 : Blo 860564 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B2801429 : Blo 860564 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1294109 : Blo 860564 1294109 := bbase (se 3 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 1294109 = 485291) (by norm_num)
theorem B1294133 : Blo 860564 1294133 := bbase (se 5 (by rfl) ⟨60662, by rfl⟩ : syracuseStep 1294133 = 121325) (by norm_num)
theorem B1294157 : Blo 860564 1294157 := bbase (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) (by norm_num)
theorem B3358549 : Blo 860564 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1458013 : Blo 860564 1458013 := bbase (se 3 (by rfl) ⟨273377, by rfl⟩ : syracuseStep 1458013 = 546755) (by norm_num)
theorem B1294181 : Blo 860564 1294181 := bbase (se 4 (by rfl) ⟨121329, by rfl⟩ : syracuseStep 1294181 = 242659) (by norm_num)
theorem B1294205 : Blo 860564 1294205 := bbase (se 3 (by rfl) ⟨242663, by rfl⟩ : syracuseStep 1294205 = 485327) (by norm_num)
theorem B1294229 : Blo 860564 1294229 := bbase (se 6 (by rfl) ⟨30333, by rfl⟩ : syracuseStep 1294229 = 60667) (by norm_num)
theorem B1294253 : Blo 860564 1294253 := bbase (se 3 (by rfl) ⟨242672, by rfl⟩ : syracuseStep 1294253 = 485345) (by norm_num)
theorem B1458101 : Blo 860564 1458101 := bbase (se 5 (by rfl) ⟨68348, by rfl⟩ : syracuseStep 1458101 = 136697) (by norm_num)
theorem B1294277 : Blo 860564 1294277 := bbase (se 4 (by rfl) ⟨121338, by rfl⟩ : syracuseStep 1294277 = 242677) (by norm_num)
theorem B2179021 : Blo 860564 2179021 := bbase (se 3 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 2179021 = 817133) (by norm_num)
theorem B4374485 : Blo 860564 4374485 := bbase (se 7 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 4374485 = 102527) (by norm_num)
theorem B1294301 : Blo 860564 1294301 := bbase (se 3 (by rfl) ⟨242681, by rfl⟩ : syracuseStep 1294301 = 485363) (by norm_num)
theorem B1294325 : Blo 860564 1294325 := bbase (se 5 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 1294325 = 121343) (by norm_num)
theorem B1294349 : Blo 860564 1294349 := bbase (se 3 (by rfl) ⟨242690, by rfl⟩ : syracuseStep 1294349 = 485381) (by norm_num)
theorem B1294373 : Blo 860564 1294373 := bbase (se 4 (by rfl) ⟨121347, by rfl⟩ : syracuseStep 1294373 = 242695) (by norm_num)
theorem B1458229 : Blo 860564 1458229 := bbase (se 5 (by rfl) ⟨68354, by rfl⟩ : syracuseStep 1458229 = 136709) (by norm_num)
theorem B2179133 : Blo 860564 2179133 := bbase (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) (by norm_num)
theorem B1294397 : Blo 860564 1294397 := bbase (se 3 (by rfl) ⟨242699, by rfl⟩ : syracuseStep 1294397 = 485399) (by norm_num)
theorem B1228861 : Blo 860564 1228861 := bbase (se 3 (by rfl) ⟨230411, by rfl⟩ : syracuseStep 1228861 = 460823) (by norm_num)
theorem B1294421 : Blo 860564 1294421 := bbase (se 8 (by rfl) ⟨7584, by rfl⟩ : syracuseStep 1294421 = 15169) (by norm_num)
theorem B1294445 : Blo 860564 1294445 := bbase (se 3 (by rfl) ⟨242708, by rfl⟩ : syracuseStep 1294445 = 485417) (by norm_num)
theorem B1294469 : Blo 860564 1294469 := bbase (se 4 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 1294469 = 242713) (by norm_num)
theorem B1458317 : Blo 860564 1458317 := bbase (se 3 (by rfl) ⟨273434, by rfl⟩ : syracuseStep 1458317 = 546869) (by norm_num)
theorem B1294493 : Blo 860564 1294493 := bbase (se 3 (by rfl) ⟨242717, by rfl⟩ : syracuseStep 1294493 = 485435) (by norm_num)
theorem B1294517 : Blo 860564 1294517 := bbase (se 5 (by rfl) ⟨60680, by rfl⟩ : syracuseStep 1294517 = 121361) (by norm_num)
theorem B1294541 : Blo 860564 1294541 := bbase (se 3 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 1294541 = 485453) (by norm_num)
theorem B1294565 : Blo 860564 1294565 := bbase (se 4 (by rfl) ⟨121365, by rfl⟩ : syracuseStep 1294565 = 242731) (by norm_num)
theorem B2179325 : Blo 860564 2179325 := bbase (se 3 (by rfl) ⟨408623, by rfl⟩ : syracuseStep 2179325 = 817247) (by norm_num)
theorem B1294589 : Blo 860564 1294589 := bbase (se 3 (by rfl) ⟨242735, by rfl⟩ : syracuseStep 1294589 = 485471) (by norm_num)
theorem B1458445 : Blo 860564 1458445 := bbase (se 3 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 1458445 = 546917) (by norm_num)
theorem B1294613 : Blo 860564 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B1294637 : Blo 860564 1294637 := bbase (se 3 (by rfl) ⟨242744, by rfl⟩ : syracuseStep 1294637 = 485489) (by norm_num)
theorem B1294661 : Blo 860564 1294661 := bbase (se 4 (by rfl) ⟨121374, by rfl⟩ : syracuseStep 1294661 = 242749) (by norm_num)
theorem B1294685 : Blo 860564 1294685 := bbase (se 3 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 1294685 = 485507) (by norm_num)
theorem B1458533 : Blo 860564 1458533 := bbase (se 4 (by rfl) ⟨136737, by rfl⟩ : syracuseStep 1458533 = 273475) (by norm_num)
theorem B1294709 : Blo 860564 1294709 := bbase (se 5 (by rfl) ⟨60689, by rfl⟩ : syracuseStep 1294709 = 121379) (by norm_num)
theorem B1294733 : Blo 860564 1294733 := bbase (se 3 (by rfl) ⟨242762, by rfl⟩ : syracuseStep 1294733 = 485525) (by norm_num)
theorem B1229197 : Blo 860564 1229197 := bbase (se 3 (by rfl) ⟨230474, by rfl⟩ : syracuseStep 1229197 = 460949) (by norm_num)
theorem B1294757 : Blo 860564 1294757 := bbase (se 4 (by rfl) ⟨121383, by rfl⟩ : syracuseStep 1294757 = 242767) (by norm_num)
theorem B1294781 : Blo 860564 1294781 := bbase (se 3 (by rfl) ⟨242771, by rfl⟩ : syracuseStep 1294781 = 485543) (by norm_num)
theorem B1294805 : Blo 860564 1294805 := bbase (se 7 (by rfl) ⟨15173, by rfl⟩ : syracuseStep 1294805 = 30347) (by norm_num)
theorem B1458661 : Blo 860564 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B1294829 : Blo 860564 1294829 := bbase (se 3 (by rfl) ⟨242780, by rfl⟩ : syracuseStep 1294829 = 485561) (by norm_num)
theorem B1294853 : Blo 860564 1294853 := bbase (se 4 (by rfl) ⟨121392, by rfl⟩ : syracuseStep 1294853 = 242785) (by norm_num)
theorem B1294877 : Blo 860564 1294877 := bbase (se 3 (by rfl) ⟨242789, by rfl⟩ : syracuseStep 1294877 = 485579) (by norm_num)
theorem B7979573 : Blo 860564 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B1294901 : Blo 860564 1294901 := bbase (se 5 (by rfl) ⟨60698, by rfl⟩ : syracuseStep 1294901 = 121397) (by norm_num)
theorem B2769461 : Blo 860564 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B1458749 : Blo 860564 1458749 := bbase (se 3 (by rfl) ⟨273515, by rfl⟩ : syracuseStep 1458749 = 547031) (by norm_num)
theorem B1294925 : Blo 860564 1294925 := bbase (se 3 (by rfl) ⟨242798, by rfl⟩ : syracuseStep 1294925 = 485597) (by norm_num)
theorem B2179669 : Blo 860564 2179669 := bbase (se 8 (by rfl) ⟨12771, by rfl⟩ : syracuseStep 2179669 = 25543) (by norm_num)
theorem B1294949 : Blo 860564 1294949 := bbase (se 4 (by rfl) ⟨121401, by rfl⟩ : syracuseStep 1294949 = 242803) (by norm_num)
theorem B1229413 : Blo 860564 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1294973 : Blo 860564 1294973 := bbase (se 3 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 1294973 = 485615) (by norm_num)
theorem B1294997 : Blo 860564 1294997 := bbase (se 6 (by rfl) ⟨30351, by rfl⟩ : syracuseStep 1294997 = 60703) (by norm_num)
theorem B1295021 : Blo 860564 1295021 := bbase (se 3 (by rfl) ⟨242816, by rfl⟩ : syracuseStep 1295021 = 485633) (by norm_num)
theorem B1458877 : Blo 860564 1458877 := bbase (se 3 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 1458877 = 547079) (by norm_num)
theorem B2179781 : Blo 860564 2179781 := bbase (se 4 (by rfl) ⟨204354, by rfl⟩ : syracuseStep 2179781 = 408709) (by norm_num)
theorem B1295045 : Blo 860564 1295045 := bbase (se 4 (by rfl) ⟨121410, by rfl⟩ : syracuseStep 1295045 = 242821) (by norm_num)
theorem B1295069 : Blo 860564 1295069 := bbase (se 3 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 1295069 = 485651) (by norm_num)
theorem B1295093 : Blo 860564 1295093 := bbase (se 5 (by rfl) ⟨60707, by rfl⟩ : syracuseStep 1295093 = 121415) (by norm_num)
theorem B2769653 : Blo 860564 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1557245 : Blo 860564 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B1164037 : Blo 860564 1164037 := bbase (se 4 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 1164037 = 218257) (by norm_num)
theorem B1295117 : Blo 860564 1295117 := bbase (se 3 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 1295117 = 485669) (by norm_num)
theorem B1295141 : Blo 860564 1295141 := bbase (se 4 (by rfl) ⟨121419, by rfl⟩ : syracuseStep 1295141 = 242839) (by norm_num)
theorem B1295165 : Blo 860564 1295165 := bbase (se 3 (by rfl) ⟨242843, by rfl⟩ : syracuseStep 1295165 = 485687) (by norm_num)
theorem B1295189 : Blo 860564 1295189 := bbase (se 9 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 1295189 = 7589) (by norm_num)
theorem B1295213 : Blo 860564 1295213 := bbase (se 3 (by rfl) ⟨242852, by rfl⟩ : syracuseStep 1295213 = 485705) (by norm_num)
theorem B2179973 : Blo 860564 2179973 := bbase (se 4 (by rfl) ⟨204372, by rfl⟩ : syracuseStep 2179973 = 408745) (by norm_num)
theorem B1295237 : Blo 860564 1295237 := bbase (se 4 (by rfl) ⟨121428, by rfl⟩ : syracuseStep 1295237 = 242857) (by norm_num)
theorem B1295261 : Blo 860564 1295261 := bbase (se 3 (by rfl) ⟨242861, by rfl⟩ : syracuseStep 1295261 = 485723) (by norm_num)
theorem B1295285 : Blo 860564 1295285 := bbase (se 5 (by rfl) ⟨60716, by rfl⟩ : syracuseStep 1295285 = 121433) (by norm_num)
theorem B1295309 : Blo 860564 1295309 := bbase (se 3 (by rfl) ⟨242870, by rfl⟩ : syracuseStep 1295309 = 485741) (by norm_num)
theorem B1229789 : Blo 860564 1229789 := bbase (se 3 (by rfl) ⟨230585, by rfl⟩ : syracuseStep 1229789 = 461171) (by norm_num)
theorem B1557469 : Blo 860564 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B1295333 : Blo 860564 1295333 := bbase (se 4 (by rfl) ⟨121437, by rfl⟩ : syracuseStep 1295333 = 242875) (by norm_num)
theorem B1295357 : Blo 860564 1295357 := bbase (se 3 (by rfl) ⟨242879, by rfl⟩ : syracuseStep 1295357 = 485759) (by norm_num)
theorem B1295381 : Blo 860564 1295381 := bbase (se 6 (by rfl) ⟨30360, by rfl⟩ : syracuseStep 1295381 = 60721) (by norm_num)
theorem B1295405 : Blo 860564 1295405 := bbase (se 3 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 1295405 = 485777) (by norm_num)
theorem B1295429 : Blo 860564 1295429 := bbase (se 4 (by rfl) ⟨121446, by rfl⟩ : syracuseStep 1295429 = 242893) (by norm_num)
theorem B1295453 : Blo 860564 1295453 := bbase (se 3 (by rfl) ⟨242897, by rfl⟩ : syracuseStep 1295453 = 485795) (by norm_num)
theorem B1295477 : Blo 860564 1295477 := bbase (se 5 (by rfl) ⟨60725, by rfl⟩ : syracuseStep 1295477 = 121451) (by norm_num)
theorem B1295501 : Blo 860564 1295501 := bbase (se 3 (by rfl) ⟨242906, by rfl⟩ : syracuseStep 1295501 = 485813) (by norm_num)
theorem B1295525 : Blo 860564 1295525 := bbase (se 4 (by rfl) ⟨121455, by rfl⟩ : syracuseStep 1295525 = 242911) (by norm_num)
theorem B1295549 : Blo 860564 1295549 := bbase (se 3 (by rfl) ⟨242915, by rfl⟩ : syracuseStep 1295549 = 485831) (by norm_num)
theorem B1295573 : Blo 860564 1295573 := bbase (se 7 (by rfl) ⟨15182, by rfl⟩ : syracuseStep 1295573 = 30365) (by norm_num)
theorem B2180317 : Blo 860564 2180317 := bbase (se 3 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 2180317 = 817619) (by norm_num)
theorem B4375781 : Blo 860564 4375781 := bbase (se 4 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 4375781 = 820459) (by norm_num)
theorem B1295597 : Blo 860564 1295597 := bbase (se 3 (by rfl) ⟨242924, by rfl⟩ : syracuseStep 1295597 = 485849) (by norm_num)
theorem B1295621 : Blo 860564 1295621 := bbase (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) (by norm_num)
theorem B1295645 : Blo 860564 1295645 := bbase (se 3 (by rfl) ⟨242933, by rfl⟩ : syracuseStep 1295645 = 485867) (by norm_num)
theorem B1295669 : Blo 860564 1295669 := bbase (se 5 (by rfl) ⟨60734, by rfl⟩ : syracuseStep 1295669 = 121469) (by norm_num)
theorem B2180429 : Blo 860564 2180429 := bbase (se 3 (by rfl) ⟨408830, by rfl⟩ : syracuseStep 2180429 = 817661) (by norm_num)
theorem B1295693 : Blo 860564 1295693 := bbase (se 3 (by rfl) ⟨242942, by rfl⟩ : syracuseStep 1295693 = 485885) (by norm_num)
theorem B1295717 : Blo 860564 1295717 := bbase (se 4 (by rfl) ⟨121473, by rfl⟩ : syracuseStep 1295717 = 242947) (by norm_num)
theorem B1295741 : Blo 860564 1295741 := bbase (se 3 (by rfl) ⟨242951, by rfl⟩ : syracuseStep 1295741 = 485903) (by norm_num)
theorem B1295765 : Blo 860564 1295765 := bbase (se 6 (by rfl) ⟨30369, by rfl⟩ : syracuseStep 1295765 = 60739) (by norm_num)
theorem B1295789 : Blo 860564 1295789 := bbase (se 3 (by rfl) ⟨242960, by rfl⟩ : syracuseStep 1295789 = 485921) (by norm_num)
theorem B1295813 : Blo 860564 1295813 := bbase (se 4 (by rfl) ⟨121482, by rfl⟩ : syracuseStep 1295813 = 242965) (by norm_num)
theorem B1295837 : Blo 860564 1295837 := bbase (se 3 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 1295837 = 485939) (by norm_num)
theorem B968161 : Blo 860564 968161 := bbase (se 2 (by rfl) ⟨363060, by rfl⟩ : syracuseStep 968161 = 726121) (by norm_num)
theorem B1295861 : Blo 860564 1295861 := bbase (se 5 (by rfl) ⟨60743, by rfl⟩ : syracuseStep 1295861 = 121487) (by norm_num)
theorem B968197 : Blo 860564 968197 := bbase (se 4 (by rfl) ⟨90768, by rfl⟩ : syracuseStep 968197 = 181537) (by norm_num)
theorem B2180621 : Blo 860564 2180621 := bbase (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) (by norm_num)
theorem B1295885 : Blo 860564 1295885 := bbase (se 3 (by rfl) ⟨242978, by rfl⟩ : syracuseStep 1295885 = 485957) (by norm_num)
theorem B1295909 : Blo 860564 1295909 := bbase (se 4 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 1295909 = 242983) (by norm_num)
theorem B968233 : Blo 860564 968233 := bbase (se 2 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 968233 = 726175) (by norm_num)
theorem B1295933 : Blo 860564 1295933 := bbase (se 3 (by rfl) ⟨242987, by rfl⟩ : syracuseStep 1295933 = 485975) (by norm_num)
theorem B968269 : Blo 860564 968269 := bbase (se 3 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 968269 = 363101) (by norm_num)
theorem B1295957 : Blo 860564 1295957 := bbase (se 8 (by rfl) ⟨7593, by rfl⟩ : syracuseStep 1295957 = 15187) (by norm_num)
theorem B1295981 : Blo 860564 1295981 := bbase (se 3 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 1295981 = 485993) (by norm_num)
theorem B968305 : Blo 860564 968305 := bbase (se 2 (by rfl) ⟨363114, by rfl⟩ : syracuseStep 968305 = 726229) (by norm_num)
theorem B1296005 : Blo 860564 1296005 := bbase (se 4 (by rfl) ⟨121500, by rfl⟩ : syracuseStep 1296005 = 243001) (by norm_num)
theorem B968341 : Blo 860564 968341 := bbase (se 6 (by rfl) ⟨22695, by rfl⟩ : syracuseStep 968341 = 45391) (by norm_num)
theorem B1296029 : Blo 860564 1296029 := bbase (se 3 (by rfl) ⟨243005, by rfl⟩ : syracuseStep 1296029 = 486011) (by norm_num)
theorem B1296053 : Blo 860564 1296053 := bbase (se 5 (by rfl) ⟨60752, by rfl⟩ : syracuseStep 1296053 = 121505) (by norm_num)
theorem B968377 : Blo 860564 968377 := bbase (se 2 (by rfl) ⟨363141, by rfl⟩ : syracuseStep 968377 = 726283) (by norm_num)
theorem B1296077 : Blo 860564 1296077 := bbase (se 3 (by rfl) ⟨243014, by rfl⟩ : syracuseStep 1296077 = 486029) (by norm_num)
theorem B968413 : Blo 860564 968413 := bbase (se 3 (by rfl) ⟨181577, by rfl⟩ : syracuseStep 968413 = 363155) (by norm_num)
theorem B1296101 : Blo 860564 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B1296125 : Blo 860564 1296125 := bbase (se 3 (by rfl) ⟨243023, by rfl⟩ : syracuseStep 1296125 = 486047) (by norm_num)
theorem B968449 : Blo 860564 968449 := bbase (se 2 (by rfl) ⟨363168, by rfl⟩ : syracuseStep 968449 = 726337) (by norm_num)
theorem B1296149 : Blo 860564 1296149 := bbase (se 6 (by rfl) ⟨30378, by rfl⟩ : syracuseStep 1296149 = 60757) (by norm_num)
theorem B968485 : Blo 860564 968485 := bbase (se 4 (by rfl) ⟨90795, by rfl⟩ : syracuseStep 968485 = 181591) (by norm_num)
theorem B1296173 : Blo 860564 1296173 := bbase (se 3 (by rfl) ⟨243032, by rfl⟩ : syracuseStep 1296173 = 486065) (by norm_num)
theorem B1296197 : Blo 860564 1296197 := bbase (se 4 (by rfl) ⟨121518, by rfl⟩ : syracuseStep 1296197 = 243037) (by norm_num)
theorem B968521 : Blo 860564 968521 := bbase (se 2 (by rfl) ⟨363195, by rfl⟩ : syracuseStep 968521 = 726391) (by norm_num)
theorem B1296221 : Blo 860564 1296221 := bbase (se 3 (by rfl) ⟨243041, by rfl⟩ : syracuseStep 1296221 = 486083) (by norm_num)
theorem B2180965 : Blo 860564 2180965 := bbase (se 4 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 2180965 = 408931) (by norm_num)
theorem B968557 : Blo 860564 968557 := bbase (se 3 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 968557 = 363209) (by norm_num)
theorem B1296245 : Blo 860564 1296245 := bbase (se 5 (by rfl) ⟨60761, by rfl⟩ : syracuseStep 1296245 = 121523) (by norm_num)
theorem B1296269 : Blo 860564 1296269 := bbase (se 3 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 1296269 = 486101) (by norm_num)
theorem B968593 : Blo 860564 968593 := bbase (se 2 (by rfl) ⟨363222, by rfl⟩ : syracuseStep 968593 = 726445) (by norm_num)
theorem B1296293 : Blo 860564 1296293 := bbase (se 4 (by rfl) ⟨121527, by rfl⟩ : syracuseStep 1296293 = 243055) (by norm_num)
theorem B1034165 : Blo 860564 1034165 := bbase (se 5 (by rfl) ⟨48476, by rfl⟩ : syracuseStep 1034165 = 96953) (by norm_num)
theorem B968629 : Blo 860564 968629 := bbase (se 5 (by rfl) ⟨45404, by rfl⟩ : syracuseStep 968629 = 90809) (by norm_num)
theorem B1296317 : Blo 860564 1296317 := bbase (se 3 (by rfl) ⟨243059, by rfl⟩ : syracuseStep 1296317 = 486119) (by norm_num)
theorem B2181077 : Blo 860564 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B1296341 : Blo 860564 1296341 := bbase (se 7 (by rfl) ⟨15191, by rfl⟩ : syracuseStep 1296341 = 30383) (by norm_num)
theorem B968665 : Blo 860564 968665 := bbase (se 2 (by rfl) ⟨363249, by rfl⟩ : syracuseStep 968665 = 726499) (by norm_num)
theorem B1296365 : Blo 860564 1296365 := bbase (se 3 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 1296365 = 486137) (by norm_num)
theorem B968701 : Blo 860564 968701 := bbase (se 3 (by rfl) ⟨181631, by rfl⟩ : syracuseStep 968701 = 363263) (by norm_num)
theorem B1296389 : Blo 860564 1296389 := bbase (se 4 (by rfl) ⟨121536, by rfl⟩ : syracuseStep 1296389 = 243073) (by norm_num)
theorem B1296413 : Blo 860564 1296413 := bbase (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) (by norm_num)
theorem B968737 : Blo 860564 968737 := bbase (se 2 (by rfl) ⟨363276, by rfl⟩ : syracuseStep 968737 = 726553) (by norm_num)
theorem B1296437 : Blo 860564 1296437 := bbase (se 5 (by rfl) ⟨60770, by rfl⟩ : syracuseStep 1296437 = 121541) (by norm_num)
theorem B968773 : Blo 860564 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B1296461 : Blo 860564 1296461 := bbase (se 3 (by rfl) ⟨243086, by rfl⟩ : syracuseStep 1296461 = 486173) (by norm_num)
theorem B1296485 : Blo 860564 1296485 := bbase (se 4 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 1296485 = 243091) (by norm_num)
theorem B968809 : Blo 860564 968809 := bbase (se 2 (by rfl) ⟨363303, by rfl⟩ : syracuseStep 968809 = 726607) (by norm_num)
theorem B1296509 : Blo 860564 1296509 := bbase (se 3 (by rfl) ⟨243095, by rfl⟩ : syracuseStep 1296509 = 486191) (by norm_num)
theorem B968845 : Blo 860564 968845 := bbase (se 3 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 968845 = 363317) (by norm_num)
theorem B2181269 : Blo 860564 2181269 := bbase (se 6 (by rfl) ⟨51123, by rfl⟩ : syracuseStep 2181269 = 102247) (by norm_num)
theorem B1296533 : Blo 860564 1296533 := bbase (se 6 (by rfl) ⟨30387, by rfl⟩ : syracuseStep 1296533 = 60775) (by norm_num)
theorem B1296557 : Blo 860564 1296557 := bbase (se 3 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 1296557 = 486209) (by norm_num)
theorem B968881 : Blo 860564 968881 := bbase (se 2 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 968881 = 726661) (by norm_num)
theorem B1296581 : Blo 860564 1296581 := bbase (se 4 (by rfl) ⟨121554, by rfl⟩ : syracuseStep 1296581 = 243109) (by norm_num)
theorem B968917 : Blo 860564 968917 := bbase (se 7 (by rfl) ⟨11354, by rfl⟩ : syracuseStep 968917 = 22709) (by norm_num)
theorem B1296605 : Blo 860564 1296605 := bbase (se 3 (by rfl) ⟨243113, by rfl⟩ : syracuseStep 1296605 = 486227) (by norm_num)
theorem B1034473 : Blo 860564 1034473 := bbase (se 2 (by rfl) ⟨387927, by rfl⟩ : syracuseStep 1034473 = 775855) (by norm_num)
theorem B1296629 : Blo 860564 1296629 := bbase (se 5 (by rfl) ⟨60779, by rfl⟩ : syracuseStep 1296629 = 121559) (by norm_num)
theorem B968953 : Blo 860564 968953 := bbase (se 2 (by rfl) ⟨363357, by rfl⟩ : syracuseStep 968953 = 726715) (by norm_num)
theorem B1296653 : Blo 860564 1296653 := bbase (se 3 (by rfl) ⟨243122, by rfl⟩ : syracuseStep 1296653 = 486245) (by norm_num)
theorem B968989 : Blo 860564 968989 := bbase (se 3 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 968989 = 363371) (by norm_num)
theorem B1296677 : Blo 860564 1296677 := bbase (se 4 (by rfl) ⟨121563, by rfl⟩ : syracuseStep 1296677 = 243127) (by norm_num)
theorem B1296701 : Blo 860564 1296701 := bbase (se 3 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 1296701 = 486263) (by norm_num)
theorem B969025 : Blo 860564 969025 := bbase (se 2 (by rfl) ⟨363384, by rfl⟩ : syracuseStep 969025 = 726769) (by norm_num)
theorem B1165637 : Blo 860564 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B1034569 : Blo 860564 1034569 := bbase (se 2 (by rfl) ⟨387963, by rfl⟩ : syracuseStep 1034569 = 775927) (by norm_num)
theorem B1296725 : Blo 860564 1296725 := bbase (se 10 (by rfl) ⟨1899, by rfl⟩ : syracuseStep 1296725 = 3799) (by norm_num)
theorem B969061 : Blo 860564 969061 := bbase (se 4 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 969061 = 181699) (by norm_num)
theorem B1296749 : Blo 860564 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B1296773 : Blo 860564 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B969097 : Blo 860564 969097 := bbase (se 2 (by rfl) ⟨363411, by rfl⟩ : syracuseStep 969097 = 726823) (by norm_num)
theorem B1296797 : Blo 860564 1296797 := bbase (se 3 (by rfl) ⟨243149, by rfl⟩ : syracuseStep 1296797 = 486299) (by norm_num)
theorem B969133 : Blo 860564 969133 := bbase (se 3 (by rfl) ⟨181712, by rfl⟩ : syracuseStep 969133 = 363425) (by norm_num)
theorem B1296821 : Blo 860564 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B1296845 : Blo 860564 1296845 := bbase (se 3 (by rfl) ⟨243158, by rfl⟩ : syracuseStep 1296845 = 486317) (by norm_num)
theorem B969169 : Blo 860564 969169 := bbase (se 2 (by rfl) ⟨363438, by rfl⟩ : syracuseStep 969169 = 726877) (by norm_num)
theorem B1034713 : Blo 860564 1034713 := bbase (se 2 (by rfl) ⟨388017, by rfl⟩ : syracuseStep 1034713 = 776035) (by norm_num)
theorem B2181613 : Blo 860564 2181613 := bbase (se 3 (by rfl) ⟨409052, by rfl⟩ : syracuseStep 2181613 = 818105) (by norm_num)
theorem B969205 : Blo 860564 969205 := bbase (se 5 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 969205 = 90863) (by norm_num)
theorem B969241 : Blo 860564 969241 := bbase (se 2 (by rfl) ⟨363465, by rfl⟩ : syracuseStep 969241 = 726931) (by norm_num)
theorem B969277 : Blo 860564 969277 := bbase (se 3 (by rfl) ⟨181739, by rfl⟩ : syracuseStep 969277 = 363479) (by norm_num)
theorem B2181725 : Blo 860564 2181725 := bbase (se 3 (by rfl) ⟨409073, by rfl⟩ : syracuseStep 2181725 = 818147) (by norm_num)
theorem B969313 : Blo 860564 969313 := bbase (se 2 (by rfl) ⟨363492, by rfl⟩ : syracuseStep 969313 = 726985) (by norm_num)
theorem B969349 : Blo 860564 969349 := bbase (se 4 (by rfl) ⟨90876, by rfl⟩ : syracuseStep 969349 = 181753) (by norm_num)
theorem B969385 : Blo 860564 969385 := bbase (se 2 (by rfl) ⟨363519, by rfl⟩ : syracuseStep 969385 = 727039) (by norm_num)
theorem B969421 : Blo 860564 969421 := bbase (se 3 (by rfl) ⟨181766, by rfl⟩ : syracuseStep 969421 = 363533) (by norm_num)
theorem B969457 : Blo 860564 969457 := bbase (se 2 (by rfl) ⟨363546, by rfl⟩ : syracuseStep 969457 = 727093) (by norm_num)
theorem B969493 : Blo 860564 969493 := bbase (se 6 (by rfl) ⟨22722, by rfl⟩ : syracuseStep 969493 = 45445) (by norm_num)
theorem B2181917 : Blo 860564 2181917 := bbase (se 3 (by rfl) ⟨409109, by rfl⟩ : syracuseStep 2181917 = 818219) (by norm_num)
theorem B969529 : Blo 860564 969529 := bbase (se 2 (by rfl) ⟨363573, by rfl⟩ : syracuseStep 969529 = 727147) (by norm_num)
theorem B969565 : Blo 860564 969565 := bbase (se 3 (by rfl) ⟨181793, by rfl⟩ : syracuseStep 969565 = 363587) (by norm_num)
theorem B3689333 : Blo 860564 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B969601 : Blo 860564 969601 := bbase (se 2 (by rfl) ⟨363600, by rfl⟩ : syracuseStep 969601 = 727201) (by norm_num)
theorem B4148117 : Blo 860564 4148117 := bbase (se 6 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 4148117 = 194443) (by norm_num)
theorem B3492773 : Blo 860564 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B969637 : Blo 860564 969637 := bbase (se 4 (by rfl) ⟨90903, by rfl⟩ : syracuseStep 969637 = 181807) (by norm_num)
theorem B969673 : Blo 860564 969673 := bbase (se 2 (by rfl) ⟨363627, by rfl⟩ : syracuseStep 969673 = 727255) (by norm_num)
theorem B969709 : Blo 860564 969709 := bbase (se 3 (by rfl) ⟨181820, by rfl⟩ : syracuseStep 969709 = 363641) (by norm_num)
theorem B3984389 : Blo 860564 3984389 := bbase (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) (by norm_num)
theorem B969745 : Blo 860564 969745 := bbase (se 2 (by rfl) ⟨363654, by rfl⟩ : syracuseStep 969745 = 727309) (by norm_num)
theorem B969781 : Blo 860564 969781 := bbase (se 5 (by rfl) ⟨45458, by rfl⟩ : syracuseStep 969781 = 90917) (by norm_num)
theorem B969817 : Blo 860564 969817 := bbase (se 2 (by rfl) ⟨363681, by rfl⟩ : syracuseStep 969817 = 727363) (by norm_num)
theorem B2182261 : Blo 860564 2182261 := bbase (se 5 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 2182261 = 204587) (by norm_num)
theorem B969853 : Blo 860564 969853 := bbase (se 3 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 969853 = 363695) (by norm_num)
theorem B969889 : Blo 860564 969889 := bbase (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) (by norm_num)
theorem B969925 : Blo 860564 969925 := bbase (se 4 (by rfl) ⟨90930, by rfl⟩ : syracuseStep 969925 = 181861) (by norm_num)
theorem B2182373 : Blo 860564 2182373 := bbase (se 4 (by rfl) ⟨204597, by rfl⟩ : syracuseStep 2182373 = 409195) (by norm_num)
theorem B969961 : Blo 860564 969961 := bbase (se 2 (by rfl) ⟨363735, by rfl⟩ : syracuseStep 969961 = 727471) (by norm_num)
theorem B969997 : Blo 860564 969997 := bbase (se 3 (by rfl) ⟨181874, by rfl⟩ : syracuseStep 969997 = 363749) (by norm_num)
theorem B970033 : Blo 860564 970033 := bbase (se 2 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 970033 = 727525) (by norm_num)
theorem B970069 : Blo 860564 970069 := bbase (se 11 (by rfl) ⟨710, by rfl⟩ : syracuseStep 970069 = 1421) (by norm_num)
theorem B970105 : Blo 860564 970105 := bbase (se 2 (by rfl) ⟨363789, by rfl⟩ : syracuseStep 970105 = 727579) (by norm_num)
theorem B970141 : Blo 860564 970141 := bbase (se 3 (by rfl) ⟨181901, by rfl⟩ : syracuseStep 970141 = 363803) (by norm_num)
theorem B2182565 : Blo 860564 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B1035713 : Blo 860564 1035713 := bbase (se 2 (by rfl) ⟨388392, by rfl⟩ : syracuseStep 1035713 = 776785) (by norm_num)
theorem B970177 : Blo 860564 970177 := bbase (se 2 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 970177 = 727633) (by norm_num)
theorem B970213 : Blo 860564 970213 := bbase (se 4 (by rfl) ⟨90957, by rfl⟩ : syracuseStep 970213 = 181915) (by norm_num)
theorem B4902389 : Blo 860564 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B970249 : Blo 860564 970249 := bbase (se 2 (by rfl) ⟨363843, by rfl⟩ : syracuseStep 970249 = 727687) (by norm_num)
theorem B970285 : Blo 860564 970285 := bbase (se 3 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 970285 = 363857) (by norm_num)
theorem B970321 : Blo 860564 970321 := bbase (se 2 (by rfl) ⟨363870, by rfl⟩ : syracuseStep 970321 = 727741) (by norm_num)
theorem B1330781 : Blo 860564 1330781 := bbase (se 3 (by rfl) ⟨249521, by rfl⟩ : syracuseStep 1330781 = 499043) (by norm_num)
theorem B970357 : Blo 860564 970357 := bbase (se 5 (by rfl) ⟨45485, by rfl⟩ : syracuseStep 970357 = 90971) (by norm_num)
theorem B970393 : Blo 860564 970393 := bbase (se 2 (by rfl) ⟨363897, by rfl⟩ : syracuseStep 970393 = 727795) (by norm_num)
theorem B970429 : Blo 860564 970429 := bbase (se 3 (by rfl) ⟨181955, by rfl⟩ : syracuseStep 970429 = 363911) (by norm_num)
theorem B970465 : Blo 860564 970465 := bbase (se 2 (by rfl) ⟨363924, by rfl⟩ : syracuseStep 970465 = 727849) (by norm_num)
theorem B2182909 : Blo 860564 2182909 := bbase (se 3 (by rfl) ⟨409295, by rfl⟩ : syracuseStep 2182909 = 818591) (by norm_num)
theorem B970501 : Blo 860564 970501 := bbase (se 4 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 970501 = 181969) (by norm_num)
theorem B970537 : Blo 860564 970537 := bbase (se 2 (by rfl) ⟨363951, by rfl⟩ : syracuseStep 970537 = 727903) (by norm_num)
theorem B970573 : Blo 860564 970573 := bbase (se 3 (by rfl) ⟨181982, by rfl⟩ : syracuseStep 970573 = 363965) (by norm_num)
theorem B2183021 : Blo 860564 2183021 := bbase (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) (by norm_num)
theorem B970609 : Blo 860564 970609 := bbase (se 2 (by rfl) ⟨363978, by rfl⟩ : syracuseStep 970609 = 727957) (by norm_num)
theorem B970645 : Blo 860564 970645 := bbase (se 6 (by rfl) ⟨22749, by rfl⟩ : syracuseStep 970645 = 45499) (by norm_num)
theorem B970681 : Blo 860564 970681 := bbase (se 2 (by rfl) ⟨364005, by rfl⟩ : syracuseStep 970681 = 728011) (by norm_num)
theorem B970717 : Blo 860564 970717 := bbase (se 3 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 970717 = 364019) (by norm_num)
theorem B970753 : Blo 860564 970753 := bbase (se 2 (by rfl) ⟨364032, by rfl⟩ : syracuseStep 970753 = 728065) (by norm_num)
theorem B970789 : Blo 860564 970789 := bbase (se 4 (by rfl) ⟨91011, by rfl⟩ : syracuseStep 970789 = 182023) (by norm_num)
theorem B2183213 : Blo 860564 2183213 := bbase (se 3 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 2183213 = 818705) (by norm_num)
theorem B970825 : Blo 860564 970825 := bbase (se 2 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 970825 = 728119) (by norm_num)
theorem B970861 : Blo 860564 970861 := bbase (se 3 (by rfl) ⟨182036, by rfl⟩ : syracuseStep 970861 = 364073) (by norm_num)
theorem B1036405 : Blo 860564 1036405 := bbase (se 5 (by rfl) ⟨48581, by rfl⟩ : syracuseStep 1036405 = 97163) (by norm_num)
theorem B970897 : Blo 860564 970897 := bbase (se 2 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 970897 = 728173) (by norm_num)
theorem B970933 : Blo 860564 970933 := bbase (se 5 (by rfl) ⟨45512, by rfl⟩ : syracuseStep 970933 = 91025) (by norm_num)
theorem B970969 : Blo 860564 970969 := bbase (se 2 (by rfl) ⟨364113, by rfl⟩ : syracuseStep 970969 = 728227) (by norm_num)
theorem B971005 : Blo 860564 971005 := bbase (se 3 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 971005 = 364127) (by norm_num)
theorem B971041 : Blo 860564 971041 := bbase (se 2 (by rfl) ⟨364140, by rfl⟩ : syracuseStep 971041 = 728281) (by norm_num)
theorem B1167653 : Blo 860564 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B971077 : Blo 860564 971077 := bbase (se 4 (by rfl) ⟨91038, by rfl⟩ : syracuseStep 971077 = 182077) (by norm_num)
theorem B1036621 : Blo 860564 1036621 := bbase (se 3 (by rfl) ⟨194366, by rfl⟩ : syracuseStep 1036621 = 388733) (by norm_num)
theorem B971113 : Blo 860564 971113 := bbase (se 2 (by rfl) ⟨364167, by rfl⟩ : syracuseStep 971113 = 728335) (by norm_num)
theorem B1331581 : Blo 860564 1331581 := bbase (se 3 (by rfl) ⟨249671, by rfl⟩ : syracuseStep 1331581 = 499343) (by norm_num)
theorem B2183557 : Blo 860564 2183557 := bbase (se 4 (by rfl) ⟨204708, by rfl⟩ : syracuseStep 2183557 = 409417) (by norm_num)
theorem B971149 : Blo 860564 971149 := bbase (se 3 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 971149 = 364181) (by norm_num)
theorem B971185 : Blo 860564 971185 := bbase (se 2 (by rfl) ⟨364194, by rfl⟩ : syracuseStep 971185 = 728389) (by norm_num)
theorem B971221 : Blo 860564 971221 := bbase (se 7 (by rfl) ⟨11381, by rfl⟩ : syracuseStep 971221 = 22763) (by norm_num)
theorem B2183669 : Blo 860564 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B971257 : Blo 860564 971257 := bbase (se 2 (by rfl) ⟨364221, by rfl⟩ : syracuseStep 971257 = 728443) (by norm_num)
theorem B971293 : Blo 860564 971293 := bbase (se 3 (by rfl) ⟨182117, by rfl⟩ : syracuseStep 971293 = 364235) (by norm_num)
theorem B971329 : Blo 860564 971329 := bbase (se 2 (by rfl) ⟨364248, by rfl⟩ : syracuseStep 971329 = 728497) (by norm_num)
theorem B971365 : Blo 860564 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B3691109 : Blo 860564 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B971401 : Blo 860564 971401 := bbase (se 2 (by rfl) ⟨364275, by rfl⟩ : syracuseStep 971401 = 728551) (by norm_num)
theorem B971437 : Blo 860564 971437 := bbase (se 3 (by rfl) ⟨182144, by rfl⟩ : syracuseStep 971437 = 364289) (by norm_num)
theorem B2183861 : Blo 860564 2183861 := bbase (se 5 (by rfl) ⟨102368, by rfl⟩ : syracuseStep 2183861 = 204737) (by norm_num)
theorem B971473 : Blo 860564 971473 := bbase (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) (by norm_num)
theorem B2904821 : Blo 860564 2904821 := bbase (se 5 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 2904821 = 272327) (by norm_num)
theorem B971509 : Blo 860564 971509 := bbase (se 5 (by rfl) ⟨45539, by rfl⟩ : syracuseStep 971509 = 91079) (by norm_num)
theorem B971545 : Blo 860564 971545 := bbase (se 2 (by rfl) ⟨364329, by rfl⟩ : syracuseStep 971545 = 728659) (by norm_num)
theorem B971581 : Blo 860564 971581 := bbase (se 3 (by rfl) ⟨182171, by rfl⟩ : syracuseStep 971581 = 364343) (by norm_num)
theorem B971617 : Blo 860564 971617 := bbase (se 2 (by rfl) ⟨364356, by rfl⟩ : syracuseStep 971617 = 728713) (by norm_num)
theorem B3101573 : Blo 860564 3101573 := bbase (se 4 (by rfl) ⟨290772, by rfl⟩ : syracuseStep 3101573 = 581545) (by norm_num)
theorem B971653 : Blo 860564 971653 := bbase (se 4 (by rfl) ⟨91092, by rfl⟩ : syracuseStep 971653 = 182185) (by norm_num)
theorem B971689 : Blo 860564 971689 := bbase (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) (by norm_num)
theorem B971725 : Blo 860564 971725 := bbase (se 3 (by rfl) ⟨182198, by rfl⟩ : syracuseStep 971725 = 364397) (by norm_num)
theorem B971761 : Blo 860564 971761 := bbase (se 2 (by rfl) ⟨364410, by rfl⟩ : syracuseStep 971761 = 728821) (by norm_num)
theorem B2184205 : Blo 860564 2184205 := bbase (se 3 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 2184205 = 819077) (by norm_num)
theorem B971797 : Blo 860564 971797 := bbase (se 6 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 971797 = 45553) (by norm_num)
theorem B971833 : Blo 860564 971833 := bbase (se 2 (by rfl) ⟨364437, by rfl⟩ : syracuseStep 971833 = 728875) (by norm_num)
theorem B971869 : Blo 860564 971869 := bbase (se 3 (by rfl) ⟨182225, by rfl⟩ : syracuseStep 971869 = 364451) (by norm_num)
theorem B2184317 : Blo 860564 2184317 := bbase (se 3 (by rfl) ⟨409559, by rfl⟩ : syracuseStep 2184317 = 819119) (by norm_num)
theorem B971905 : Blo 860564 971905 := bbase (se 2 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 971905 = 728929) (by norm_num)
theorem B3101861 : Blo 860564 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B2905253 : Blo 860564 2905253 := bbase (se 4 (by rfl) ⟨272367, by rfl⟩ : syracuseStep 2905253 = 544735) (by norm_num)
theorem B971941 : Blo 860564 971941 := bbase (se 4 (by rfl) ⟨91119, by rfl⟩ : syracuseStep 971941 = 182239) (by norm_num)
theorem B971977 : Blo 860564 971977 := bbase (se 2 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 971977 = 728983) (by norm_num)
theorem B972013 : Blo 860564 972013 := bbase (se 3 (by rfl) ⟨182252, by rfl⟩ : syracuseStep 972013 = 364505) (by norm_num)
theorem B972049 : Blo 860564 972049 := bbase (se 2 (by rfl) ⟨364518, by rfl⟩ : syracuseStep 972049 = 729037) (by norm_num)
theorem B972085 : Blo 860564 972085 := bbase (se 5 (by rfl) ⟨45566, by rfl⟩ : syracuseStep 972085 = 91133) (by norm_num)
theorem B2184509 : Blo 860564 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B972121 : Blo 860564 972121 := bbase (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) (by norm_num)
theorem B972157 : Blo 860564 972157 := bbase (se 3 (by rfl) ⟨182279, by rfl⟩ : syracuseStep 972157 = 364559) (by norm_num)
theorem B972193 : Blo 860564 972193 := bbase (se 2 (by rfl) ⟨364572, by rfl⟩ : syracuseStep 972193 = 729145) (by norm_num)
theorem B972229 : Blo 860564 972229 := bbase (se 4 (by rfl) ⟨91146, by rfl⟩ : syracuseStep 972229 = 182293) (by norm_num)
theorem B972265 : Blo 860564 972265 := bbase (se 2 (by rfl) ⟨364599, by rfl⟩ : syracuseStep 972265 = 729199) (by norm_num)
theorem B972301 : Blo 860564 972301 := bbase (se 3 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 972301 = 364613) (by norm_num)
theorem B972337 : Blo 860564 972337 := bbase (se 2 (by rfl) ⟨364626, by rfl⟩ : syracuseStep 972337 = 729253) (by norm_num)
theorem B1398325 : Blo 860564 1398325 := bbase (se 5 (by rfl) ⟨65546, by rfl⟩ : syracuseStep 1398325 = 131093) (by norm_num)
theorem B874037 : Blo 860564 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B3692101 : Blo 860564 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B2905685 : Blo 860564 2905685 := bbase (se 8 (by rfl) ⟨17025, by rfl⟩ : syracuseStep 2905685 = 34051) (by norm_num)
theorem B972373 : Blo 860564 972373 := bbase (se 8 (by rfl) ⟨5697, by rfl⟩ : syracuseStep 972373 = 11395) (by norm_num)
theorem B4150885 : Blo 860564 4150885 := bbase (se 4 (by rfl) ⟨389145, by rfl⟩ : syracuseStep 4150885 = 778291) (by norm_num)
theorem B972409 : Blo 860564 972409 := bbase (se 2 (by rfl) ⟨364653, by rfl⟩ : syracuseStep 972409 = 729307) (by norm_num)
theorem B2184853 : Blo 860564 2184853 := bbase (se 6 (by rfl) ⟨51207, by rfl⟩ : syracuseStep 2184853 = 102415) (by norm_num)
theorem B972445 : Blo 860564 972445 := bbase (se 3 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 972445 = 364667) (by norm_num)
theorem B972481 : Blo 860564 972481 := bbase (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) (by norm_num)
theorem B972517 : Blo 860564 972517 := bbase (se 4 (by rfl) ⟨91173, by rfl⟩ : syracuseStep 972517 = 182347) (by norm_num)
theorem B2184965 : Blo 860564 2184965 := bbase (se 4 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 2184965 = 409681) (by norm_num)
theorem B972553 : Blo 860564 972553 := bbase (se 2 (by rfl) ⟨364707, by rfl⟩ : syracuseStep 972553 = 729415) (by norm_num)
theorem B972589 : Blo 860564 972589 := bbase (se 3 (by rfl) ⟨182360, by rfl⟩ : syracuseStep 972589 = 364721) (by norm_num)
theorem B972625 : Blo 860564 972625 := bbase (se 2 (by rfl) ⟨364734, by rfl⟩ : syracuseStep 972625 = 729469) (by norm_num)
theorem B2185157 : Blo 860564 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B1038317 : Blo 860564 1038317 := bbase (se 3 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 1038317 = 389369) (by norm_num)
theorem B5527541 : Blo 860564 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B2906117 : Blo 860564 2906117 := bbase (se 4 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 2906117 = 544897) (by norm_num)
theorem B874585 : Blo 860564 874585 := bbase (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) (by norm_num)
theorem B1038529 : Blo 860564 1038529 := bbase (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) (by norm_num)
theorem B2185501 : Blo 860564 2185501 := bbase (se 3 (by rfl) ⟨409781, by rfl⟩ : syracuseStep 2185501 = 819563) (by norm_num)
theorem B2185613 : Blo 860564 2185613 := bbase (se 3 (by rfl) ⟨409802, by rfl⟩ : syracuseStep 2185613 = 819605) (by norm_num)
theorem B2906549 : Blo 860564 2906549 := bbase (se 5 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 2906549 = 272489) (by norm_num)
theorem B874945 : Blo 860564 874945 := bbase (se 2 (by rfl) ⟨328104, by rfl⟩ : syracuseStep 874945 = 656209) (by norm_num)
theorem B2185805 : Blo 860564 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B6543989 : Blo 860564 6543989 := bbase (se 5 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 6543989 = 613499) (by norm_num)
theorem B875269 : Blo 860564 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B1104725 : Blo 860564 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B2906981 : Blo 860564 2906981 := bbase (se 4 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 2906981 = 545059) (by norm_num)
theorem B3726229 : Blo 860564 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B2186149 : Blo 860564 2186149 := bbase (se 4 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 2186149 = 409903) (by norm_num)
theorem B2186261 : Blo 860564 2186261 := bbase (se 6 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 2186261 = 102481) (by norm_num)
theorem B2186453 : Blo 860564 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B2907413 : Blo 860564 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B1662445 : Blo 860564 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B2186797 : Blo 860564 2186797 := bbase (se 3 (by rfl) ⟨410024, by rfl⟩ : syracuseStep 2186797 = 820049) (by norm_num)
theorem B876097 : Blo 860564 876097 := bbase (se 2 (by rfl) ⟨328536, by rfl⟩ : syracuseStep 876097 = 657073) (by norm_num)
theorem B2842229 : Blo 860564 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B2186909 : Blo 860564 2186909 := bbase (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) (by norm_num)
theorem B2907845 : Blo 860564 2907845 := bbase (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) (by norm_num)
theorem B3366629 : Blo 860564 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B1105669 : Blo 860564 1105669 := bbase (se 4 (by rfl) ⟨103656, by rfl⟩ : syracuseStep 1105669 = 207313) (by norm_num)
theorem B4972373 : Blo 860564 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2187101 : Blo 860564 2187101 := bbase (se 3 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 2187101 = 820163) (by norm_num)
theorem B1400765 : Blo 860564 1400765 := bbase (se 3 (by rfl) ⟨262643, by rfl⟩ : syracuseStep 1400765 = 525287) (by norm_num)
theorem B2908277 : Blo 860564 2908277 := bbase (se 5 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 2908277 = 272651) (by norm_num)
theorem B2187445 : Blo 860564 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B2187557 : Blo 860564 2187557 := bbase (se 4 (by rfl) ⟨205083, by rfl⟩ : syracuseStep 2187557 = 410167) (by norm_num)
theorem B1663301 : Blo 860564 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1106389 : Blo 860564 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B2187749 : Blo 860564 2187749 := bbase (se 4 (by rfl) ⟨205101, by rfl⟩ : syracuseStep 2187749 = 410203) (by norm_num)
theorem B2908709 : Blo 860564 2908709 := bbase (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) (by norm_num)
theorem B7365269 : Blo 860564 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B3269429 : Blo 860564 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B2188093 : Blo 860564 2188093 := bbase (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) (by norm_num)
theorem B2188205 : Blo 860564 2188205 := bbase (se 3 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 2188205 = 820577) (by norm_num)
theorem B2909141 : Blo 860564 2909141 := bbase (se 7 (by rfl) ⟨34091, by rfl⟩ : syracuseStep 2909141 = 68183) (by norm_num)
theorem B3269717 : Blo 860564 3269717 := bbase (se 8 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 3269717 = 38317) (by norm_num)
theorem B2188397 : Blo 860564 2188397 := bbase (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) (by norm_num)
theorem B1991861 : Blo 860564 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B13985045 : Blo 860564 13985045 := bbase (se 6 (by rfl) ⟨327774, by rfl⟩ : syracuseStep 13985045 = 655549) (by norm_num)
theorem B1402181 : Blo 860564 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B2909573 : Blo 860564 2909573 := bbase (se 4 (by rfl) ⟨272772, by rfl⟩ : syracuseStep 2909573 = 545545) (by norm_num)
theorem B1402429 : Blo 860564 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1894013 : Blo 860564 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B8840917 : Blo 860564 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B2910005 : Blo 860564 2910005 := bbase (se 5 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 2910005 = 272813) (by norm_num)
theorem B13985621 : Blo 860564 13985621 := bbase (se 9 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 13985621 = 81947) (by norm_num)
theorem B1108009 : Blo 860564 1108009 := bbase (se 2 (by rfl) ⟨415503, by rfl⟩ : syracuseStep 1108009 = 831007) (by norm_num)
theorem B2910437 : Blo 860564 2910437 := bbase (se 4 (by rfl) ⟨272853, by rfl⟩ : syracuseStep 2910437 = 545707) (by norm_num)
theorem B3270901 : Blo 860564 3270901 := bbase (se 5 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 3270901 = 306647) (by norm_num)
theorem B1599925 : Blo 860564 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B3271205 : Blo 860564 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B2910869 : Blo 860564 2910869 := bbase (se 6 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 2910869 = 136447) (by norm_num)
theorem B7858997 : Blo 860564 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B3107717 : Blo 860564 3107717 := bbase (se 4 (by rfl) ⟨291348, by rfl⟩ : syracuseStep 3107717 = 582697) (by norm_num)
theorem B11037653 : Blo 860564 11037653 := bbase (se 7 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 11037653 = 258695) (by norm_num)
theorem B2911301 : Blo 860564 2911301 := bbase (se 4 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 2911301 = 545869) (by norm_num)
theorem B4910453 : Blo 860564 4910453 := bbase (se 5 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 4910453 = 460355) (by norm_num)
theorem B3108293 : Blo 860564 3108293 := bbase (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) (by norm_num)
theorem B3927509 : Blo 860564 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2452949 : Blo 860564 2452949 := bbase (se 7 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 2452949 = 57491) (by norm_num)
theorem B1633765 : Blo 860564 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B2911733 : Blo 860564 2911733 := bbase (se 5 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 2911733 = 272975) (by norm_num)
theorem B7368245 : Blo 860564 7368245 := bbase (se 5 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 7368245 = 690773) (by norm_num)
theorem B1863253 : Blo 860564 1863253 := bbase (se 8 (by rfl) ⟨10917, by rfl⟩ : syracuseStep 1863253 = 21835) (by norm_num)
theorem B1633925 : Blo 860564 1633925 := bbase (se 4 (by rfl) ⟨153180, by rfl⟩ : syracuseStep 1633925 = 306361) (by norm_num)
theorem B1634069 : Blo 860564 1634069 := bbase (se 6 (by rfl) ⟨38298, by rfl⟩ : syracuseStep 1634069 = 76597) (by norm_num)
theorem B5533589 : Blo 860564 5533589 := bbase (se 6 (by rfl) ⟨129693, by rfl⟩ : syracuseStep 5533589 = 259387) (by norm_num)
theorem B2912165 : Blo 860564 2912165 := bbase (se 4 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 2912165 = 546031) (by norm_num)
theorem B1634357 : Blo 860564 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B1863773 : Blo 860564 1863773 := bbase (se 3 (by rfl) ⟨349457, by rfl⟩ : syracuseStep 1863773 = 698915) (by norm_num)
theorem B1863869 : Blo 860564 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B1634509 : Blo 860564 1634509 := bbase (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) (by norm_num)
theorem B1863965 : Blo 860564 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B2912597 : Blo 860564 2912597 := bbase (se 10 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 2912597 = 8533) (by norm_num)
theorem B1634813 : Blo 860564 1634813 := bbase (se 3 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 1634813 = 613055) (by norm_num)
theorem B4911637 : Blo 860564 4911637 := bbase (se 6 (by rfl) ⟨115116, by rfl⟩ : syracuseStep 4911637 = 230233) (by norm_num)
theorem B3273317 : Blo 860564 3273317 := bbase (se 4 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 3273317 = 613747) (by norm_num)
theorem B2454133 : Blo 860564 2454133 := bbase (se 5 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 2454133 = 230075) (by norm_num)
theorem B2519813 : Blo 860564 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B2913029 : Blo 860564 2913029 := bbase (se 4 (by rfl) ⟨273096, by rfl⟩ : syracuseStep 2913029 = 546193) (by norm_num)
theorem B2454293 : Blo 860564 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B3273605 : Blo 860564 3273605 := bbase (se 4 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 3273605 = 613801) (by norm_num)
theorem B3109877 : Blo 860564 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2454533 : Blo 860564 2454533 := bbase (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) (by norm_num)
theorem B2913461 : Blo 860564 2913461 := bbase (se 5 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 2913461 = 273137) (by norm_num)
theorem B2454725 : Blo 860564 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B1635565 : Blo 860564 1635565 := bbase (se 3 (by rfl) ⟨306668, by rfl⟩ : syracuseStep 1635565 = 613337) (by norm_num)
theorem B3110165 : Blo 860564 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B1635709 : Blo 860564 1635709 := bbase (se 3 (by rfl) ⟨306695, by rfl⟩ : syracuseStep 1635709 = 613391) (by norm_num)
theorem B1635869 : Blo 860564 1635869 := bbase (se 3 (by rfl) ⟨306725, by rfl⟩ : syracuseStep 1635869 = 613451) (by norm_num)
theorem B2913893 : Blo 860564 2913893 := bbase (se 4 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 2913893 = 546355) (by norm_num)
theorem B1636013 : Blo 860564 1636013 := bbase (se 3 (by rfl) ⟨306752, by rfl⟩ : syracuseStep 1636013 = 613505) (by norm_num)
theorem B2487989 : Blo 860564 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B1636301 : Blo 860564 1636301 := bbase (se 3 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 1636301 = 613613) (by norm_num)
theorem B1964029 : Blo 860564 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2914325 : Blo 860564 2914325 := bbase (se 6 (by rfl) ⟨68304, by rfl⟩ : syracuseStep 2914325 = 136609) (by norm_num)
theorem B3274789 : Blo 860564 3274789 := bbase (se 4 (by rfl) ⟨307011, by rfl⟩ : syracuseStep 3274789 = 614023) (by norm_num)
theorem B1964101 : Blo 860564 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B19888213 : Blo 860564 19888213 := bbase (se 8 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 19888213 = 233065) (by norm_num)
theorem B1636453 : Blo 860564 1636453 := bbase (se 4 (by rfl) ⟨153417, by rfl⟩ : syracuseStep 1636453 = 306835) (by norm_num)
theorem B2455717 : Blo 860564 2455717 := bbase (se 4 (by rfl) ⟨230223, by rfl⟩ : syracuseStep 2455717 = 460447) (by norm_num)
theorem B6551765 : Blo 860564 6551765 := bbase (se 7 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 6551765 = 153557) (by norm_num)
theorem B6715669 : Blo 860564 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B3275093 : Blo 860564 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B3504485 : Blo 860564 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B1636757 : Blo 860564 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B2914757 : Blo 860564 2914757 := bbase (se 4 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 2914757 = 546517) (by norm_num)
theorem B4913621 : Blo 860564 4913621 := bbase (se 7 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 4913621 = 115163) (by norm_num)
theorem B1866269 : Blo 860564 1866269 := bbase (se 3 (by rfl) ⟨349925, by rfl⟩ : syracuseStep 1866269 = 699851) (by norm_num)
theorem B5241493 : Blo 860564 5241493 := bbase (se 6 (by rfl) ⟨122847, by rfl⟩ : syracuseStep 5241493 = 245695) (by norm_num)
theorem B6224597 : Blo 860564 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B2915189 : Blo 860564 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B1637509 : Blo 860564 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B1965197 : Blo 860564 1965197 := bbase (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) (by norm_num)
theorem B1965269 : Blo 860564 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B2456821 : Blo 860564 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B1309949 : Blo 860564 1309949 := bbase (se 3 (by rfl) ⟨245615, by rfl⟩ : syracuseStep 1309949 = 491231) (by norm_num)
theorem B1637653 : Blo 860564 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B2915621 : Blo 860564 2915621 := bbase (se 4 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 2915621 = 546679) (by norm_num)
theorem B1637813 : Blo 860564 1637813 := bbase (se 5 (by rfl) ⟨76772, by rfl⟩ : syracuseStep 1637813 = 153545) (by norm_num)
theorem B4357637 : Blo 860564 4357637 := bbase (se 4 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 4357637 = 817057) (by norm_num)
theorem B982561 : Blo 860564 982561 := bbase (se 2 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 982561 = 736921) (by norm_num)
theorem B1637957 : Blo 860564 1637957 := bbase (se 4 (by rfl) ⟨153558, by rfl⟩ : syracuseStep 1637957 = 307117) (by norm_num)
theorem B2916053 : Blo 860564 2916053 := bbase (se 7 (by rfl) ⟨34172, by rfl⟩ : syracuseStep 2916053 = 68345) (by norm_num)
theorem B1965917 : Blo 860564 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B1638245 : Blo 860564 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B3112933 : Blo 860564 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B1638397 : Blo 860564 1638397 := bbase (se 3 (by rfl) ⟨307199, by rfl⟩ : syracuseStep 1638397 = 614399) (by norm_num)
theorem B1638481 : Blo 860564 1638481 := bstep (se 2 (by rfl) ⟨614430, by rfl⟩ : syracuseStep 1638481 = 1228861) B1228861
theorem B4358285 : Blo 860564 4358285 := bstep (se 3 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 4358285 = 1634357) B1634357
theorem B2916593 : Blo 860564 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B3277219 : Blo 860564 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B1638883 : Blo 860564 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B2458097 : Blo 860564 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B1638929 : Blo 860564 1638929 := bstep (se 2 (by rfl) ⟨614598, by rfl⟩ : syracuseStep 1638929 = 1229197) B1229197
theorem B1475185 : Blo 860564 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B1311347 : Blo 860564 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B3113741 : Blo 860564 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B2917133 : Blo 860564 2917133 := bstep (se 3 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 2917133 = 1093925) B1093925
theorem B2622257 : Blo 860564 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B1639217 : Blo 860564 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B2917187 : Blo 860564 2917187 := bstep (se 1 (by rfl) ⟨2187890, by rfl⟩ : syracuseStep 2917187 = 4375781) B4375781
theorem B2917457 : Blo 860564 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B1639939 : Blo 860564 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B2623277 : Blo 860564 2623277 := bstep (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) B983729
theorem B919459 : Blo 860564 919459 := bstep (se 1 (by rfl) ⟨689594, by rfl⟩ : syracuseStep 919459 = 1379189) B1379189
theorem B2459555 : Blo 860564 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B2328515 : Blo 860564 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B1640387 : Blo 860564 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B1312753 : Blo 860564 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B2656259 : Blo 860564 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B6719501 : Blo 860564 6719501 := bstep (se 3 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 6719501 = 2519813) B2519813
theorem B1247251 : Blo 860564 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B1869905 : Blo 860564 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B2328689 : Blo 860564 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B1640675 : Blo 860564 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B7473521 : Blo 860564 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B2623985 : Blo 860564 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B3279437 : Blo 860564 3279437 := bstep (se 3 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 3279437 = 1229789) B1229789
theorem B2460365 : Blo 860564 2460365 := bstep (se 3 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 2460365 = 922637) B922637
theorem B7867205 : Blo 860564 7867205 := bstep (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) B1475101
theorem B5245829 : Blo 860564 5245829 := bstep (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) B983593
theorem B2460557 : Blo 860564 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B2329489 : Blo 860564 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B920531 : Blo 860564 920531 := bstep (se 1 (by rfl) ⟨690398, by rfl⟩ : syracuseStep 920531 = 1380797) B1380797
theorem B1379297 : Blo 860564 1379297 := bstep (se 2 (by rfl) ⟨517236, by rfl⟩ : syracuseStep 1379297 = 1034473) B1034473
theorem B4361201 : Blo 860564 4361201 := bstep (se 2 (by rfl) ⟨1635450, by rfl⟩ : syracuseStep 4361201 = 3270901) B3270901
theorem B2362385 : Blo 860564 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B5246021 : Blo 860564 5246021 := bstep (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) B983629
theorem B1379425 : Blo 860564 1379425 := bstep (se 2 (by rfl) ⟨517284, by rfl⟩ : syracuseStep 1379425 = 1034569) B1034569
theorem B1182817 : Blo 860564 1182817 := bstep (se 2 (by rfl) ⟨443556, by rfl⟩ : syracuseStep 1182817 = 887113) B887113
theorem B1936529 : Blo 860564 1936529 := bstep (se 2 (by rfl) ⟨726198, by rfl⟩ : syracuseStep 1936529 = 1452397) B1452397
theorem B1313939 : Blo 860564 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B1936547 : Blo 860564 1936547 := bstep (se 1 (by rfl) ⟨1452410, by rfl⟩ : syracuseStep 1936547 = 2904821) B2904821
theorem B2133233 : Blo 860564 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B2067715 : Blo 860564 2067715 := bstep (se 1 (by rfl) ⟨1550786, by rfl⟩ : syracuseStep 2067715 = 3101573) B3101573
theorem B1838371 : Blo 860564 1838371 := bstep (se 1 (by rfl) ⟨1378778, by rfl⟩ : syracuseStep 1838371 = 2757557) B2757557
theorem B2067889 : Blo 860564 2067889 := bstep (se 2 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 2067889 = 1550917) B1550917
theorem B1936817 : Blo 860564 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B1936835 : Blo 860564 1936835 := bstep (se 1 (by rfl) ⟨1452626, by rfl⟩ : syracuseStep 1936835 = 2905253) B2905253
theorem B27954629 : Blo 860564 27954629 := bstep (se 4 (by rfl) ⟨2620746, by rfl⟩ : syracuseStep 27954629 = 5241493) B5241493
theorem B1937105 : Blo 860564 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B1937123 : Blo 860564 1937123 := bstep (se 1 (by rfl) ⟨1452842, by rfl⟩ : syracuseStep 1937123 = 2905685) B2905685
theorem B2461549 : Blo 860564 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1576849 : Blo 860564 1576849 := bstep (se 2 (by rfl) ⟨591318, by rfl⟩ : syracuseStep 1576849 = 1182637) B1182637
theorem B8851427 : Blo 860564 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B1937393 : Blo 860564 1937393 := bstep (se 2 (by rfl) ⟨726522, by rfl⟩ : syracuseStep 1937393 = 1453045) B1453045
theorem B1937411 : Blo 860564 1937411 := bstep (se 1 (by rfl) ⟨1453058, by rfl⟩ : syracuseStep 1937411 = 2906117) B2906117
theorem B1183777 : Blo 860564 1183777 := bstep (se 2 (by rfl) ⟨443916, by rfl⟩ : syracuseStep 1183777 = 887833) B887833
theorem B1380419 : Blo 860564 1380419 := bstep (se 1 (by rfl) ⟨1035314, by rfl⟩ : syracuseStep 1380419 = 2070629) B2070629
theorem B921667 : Blo 860564 921667 := bstep (se 1 (by rfl) ⟨691250, by rfl⟩ : syracuseStep 921667 = 1382501) B1382501
theorem B2330765 : Blo 860564 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B1937681 : Blo 860564 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B1937699 : Blo 860564 1937699 := bstep (se 1 (by rfl) ⟨1453274, by rfl⟩ : syracuseStep 1937699 = 2906549) B2906549
theorem B4362659 : Blo 860564 4362659 := bstep (se 1 (by rfl) ⟨3271994, by rfl⟩ : syracuseStep 4362659 = 6543989) B6543989
theorem B1839601 : Blo 860564 1839601 := bstep (se 2 (by rfl) ⟨689850, by rfl⟩ : syracuseStep 1839601 = 1379701) B1379701
theorem B1937969 : Blo 860564 1937969 := bstep (se 2 (by rfl) ⟨726738, by rfl⟩ : syracuseStep 1937969 = 1453477) B1453477
theorem B1937987 : Blo 860564 1937987 := bstep (se 1 (by rfl) ⟨1453490, by rfl⟩ : syracuseStep 1937987 = 2906981) B2906981
theorem B4919885 : Blo 860564 4919885 := bstep (se 3 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 4919885 = 1844957) B1844957
theorem B7180913 : Blo 860564 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B1184419 : Blo 860564 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B4428593 : Blo 860564 4428593 := bstep (se 2 (by rfl) ⟨1660722, by rfl⟩ : syracuseStep 4428593 = 3321445) B3321445
theorem B1938257 : Blo 860564 1938257 := bstep (se 2 (by rfl) ⟨726846, by rfl⟩ : syracuseStep 1938257 = 1453693) B1453693
theorem B1938275 : Blo 860564 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B922547 : Blo 860564 922547 := bstep (se 1 (by rfl) ⟨691910, by rfl⟩ : syracuseStep 922547 = 1383821) B1383821
theorem B922675 : Blo 860564 922675 := bstep (se 1 (by rfl) ⟨692006, by rfl⟩ : syracuseStep 922675 = 1384013) B1384013
theorem B1938545 : Blo 860564 1938545 := bstep (se 2 (by rfl) ⟨726954, by rfl⟩ : syracuseStep 1938545 = 1453909) B1453909
theorem B1938563 : Blo 860564 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B1840259 : Blo 860564 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B2757773 : Blo 860564 2757773 := bstep (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) B1034165
theorem B4363469 : Blo 860564 4363469 := bstep (se 3 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 4363469 = 1636301) B1636301
theorem B3314915 : Blo 860564 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B1938833 : Blo 860564 1938833 := bstep (se 2 (by rfl) ⟨727062, by rfl⟩ : syracuseStep 1938833 = 1454125) B1454125
theorem B1938851 : Blo 860564 1938851 := bstep (se 1 (by rfl) ⟨1454138, by rfl⟩ : syracuseStep 1938851 = 2908277) B2908277
theorem B3282353 : Blo 860564 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B1971683 : Blo 860564 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B1381873 : Blo 860564 1381873 := bstep (se 2 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 1381873 = 1036405) B1036405
theorem B1939121 : Blo 860564 1939121 := bstep (se 2 (by rfl) ⟨727170, by rfl⟩ : syracuseStep 1939121 = 1454341) B1454341
theorem B1939139 : Blo 860564 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B1775441 : Blo 860564 1775441 := bstep (se 2 (by rfl) ⟨665790, by rfl⟩ : syracuseStep 1775441 = 1331581) B1331581
theorem B1939409 : Blo 860564 1939409 := bstep (se 2 (by rfl) ⟨727278, by rfl⟩ : syracuseStep 1939409 = 1454557) B1454557
theorem B1841105 : Blo 860564 1841105 := bstep (se 2 (by rfl) ⟨690414, by rfl⟩ : syracuseStep 1841105 = 1380829) B1380829
theorem B1939427 : Blo 860564 1939427 := bstep (se 1 (by rfl) ⟨1454570, by rfl⟩ : syracuseStep 1939427 = 2909141) B2909141
theorem B1939697 : Blo 860564 1939697 := bstep (se 2 (by rfl) ⟨727386, by rfl⟩ : syracuseStep 1939697 = 1454773) B1454773
theorem B1939715 : Blo 860564 1939715 := bstep (se 1 (by rfl) ⟨1454786, by rfl⟩ : syracuseStep 1939715 = 2909573) B2909573
theorem B9345293 : Blo 860564 9345293 := bstep (se 3 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 9345293 = 3504485) B3504485
theorem B14194997 : Blo 860564 14194997 := bstep (se 5 (by rfl) ⟨665390, by rfl⟩ : syracuseStep 14194997 = 1330781) B1330781
theorem B1939985 : Blo 860564 1939985 := bstep (se 2 (by rfl) ⟨727494, by rfl⟩ : syracuseStep 1939985 = 1454989) B1454989
theorem B1940003 : Blo 860564 1940003 := bstep (se 1 (by rfl) ⟨1455002, by rfl⟩ : syracuseStep 1940003 = 2910005) B2910005
theorem B9837125 : Blo 860564 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B2103953 : Blo 860564 2103953 := bstep (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) B1577965
theorem B4922117 : Blo 860564 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B1940273 : Blo 860564 1940273 := bstep (se 2 (by rfl) ⟨727602, by rfl⟩ : syracuseStep 1940273 = 1455205) B1455205
theorem B1940291 : Blo 860564 1940291 := bstep (se 1 (by rfl) ⟨1455218, by rfl⟩ : syracuseStep 1940291 = 2910437) B2910437
theorem B1383475 : Blo 860564 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B1940561 : Blo 860564 1940561 := bstep (se 2 (by rfl) ⟨727710, by rfl⟩ : syracuseStep 1940561 = 1455421) B1455421
theorem B1940579 : Blo 860564 1940579 := bstep (se 1 (by rfl) ⟨1455434, by rfl⟩ : syracuseStep 1940579 = 2910869) B2910869
theorem B5250253 : Blo 860564 5250253 := bstep (se 3 (by rfl) ⟨984422, by rfl⟩ : syracuseStep 5250253 = 1968845) B1968845
theorem B2071811 : Blo 860564 2071811 := bstep (se 1 (by rfl) ⟨1553858, by rfl⟩ : syracuseStep 2071811 = 3107717) B3107717
theorem B2759953 : Blo 860564 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B1383731 : Blo 860564 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B1940849 : Blo 860564 1940849 := bstep (se 2 (by rfl) ⟨727818, by rfl⟩ : syracuseStep 1940849 = 1455637) B1455637
theorem B1940867 : Blo 860564 1940867 := bstep (se 1 (by rfl) ⟨1455650, by rfl⟩ : syracuseStep 1940867 = 2911301) B2911301
theorem B4922801 : Blo 860564 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B2760131 : Blo 860564 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B1383923 : Blo 860564 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B1842787 : Blo 860564 1842787 := bstep (se 1 (by rfl) ⟨1382090, by rfl⟩ : syracuseStep 1842787 = 2764181) B2764181
theorem B2072195 : Blo 860564 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B1941137 : Blo 860564 1941137 := bstep (se 2 (by rfl) ⟨727926, by rfl⟩ : syracuseStep 1941137 = 1455853) B1455853
theorem B1941155 : Blo 860564 1941155 := bstep (se 1 (by rfl) ⟨1455866, by rfl⟩ : syracuseStep 1941155 = 2911733) B2911733
theorem B1089283 : Blo 860564 1089283 := bstep (se 1 (by rfl) ⟨816962, by rfl⟩ : syracuseStep 1089283 = 1633925) B1633925
theorem B3677987 : Blo 860564 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B2367299 : Blo 860564 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B1089379 : Blo 860564 1089379 := bstep (se 1 (by rfl) ⟨817034, by rfl⟩ : syracuseStep 1089379 = 1634069) B1634069
theorem B1941425 : Blo 860564 1941425 := bstep (se 2 (by rfl) ⟨728034, by rfl⟩ : syracuseStep 1941425 = 1456069) B1456069
theorem B1941443 : Blo 860564 1941443 := bstep (se 1 (by rfl) ⟨1456082, by rfl⟩ : syracuseStep 1941443 = 2912165) B2912165
theorem B4366385 : Blo 860564 4366385 := bstep (se 2 (by rfl) ⟨1637394, by rfl⟩ : syracuseStep 4366385 = 3274789) B3274789
theorem B1843249 : Blo 860564 1843249 := bstep (se 2 (by rfl) ⟨691218, by rfl⟩ : syracuseStep 1843249 = 1382437) B1382437
theorem B26517617 : Blo 860564 26517617 := bstep (se 2 (by rfl) ⟨9944106, by rfl⟩ : syracuseStep 26517617 = 19888213) B19888213
theorem B3154061 : Blo 860564 3154061 := bstep (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) B1182773
theorem B2072753 : Blo 860564 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B1941713 : Blo 860564 1941713 := bstep (se 2 (by rfl) ⟨728142, by rfl⟩ : syracuseStep 1941713 = 1456285) B1456285
theorem B1941731 : Blo 860564 1941731 := bstep (se 1 (by rfl) ⟨1456298, by rfl⟩ : syracuseStep 1941731 = 2912597) B2912597
theorem B1384705 : Blo 860564 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B1089875 : Blo 860564 1089875 := bstep (se 1 (by rfl) ⟨817406, by rfl⟩ : syracuseStep 1089875 = 1634813) B1634813
theorem B8954225 : Blo 860564 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B860579 : Blo 860564 860579 := bstep (se 1 (by rfl) ⟨645434, by rfl⟩ : syracuseStep 860579 = 1290869) B1290869
theorem B860595 : Blo 860564 860595 := bstep (se 1 (by rfl) ⟨645446, by rfl⟩ : syracuseStep 860595 = 1290893) B1290893
theorem B860611 : Blo 860564 860611 := bstep (se 1 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 860611 = 1290917) B1290917
theorem B9937349 : Blo 860564 9937349 := bstep (se 4 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 9937349 = 1863253) B1863253
theorem B860627 : Blo 860564 860627 := bstep (se 1 (by rfl) ⟨645470, by rfl⟩ : syracuseStep 860627 = 1290941) B1290941
theorem B860643 : Blo 860564 860643 := bstep (se 1 (by rfl) ⟨645482, by rfl⟩ : syracuseStep 860643 = 1290965) B1290965
theorem B1942001 : Blo 860564 1942001 := bstep (se 2 (by rfl) ⟨728250, by rfl⟩ : syracuseStep 1942001 = 1456501) B1456501
theorem B860659 : Blo 860564 860659 := bstep (se 1 (by rfl) ⟨645494, by rfl⟩ : syracuseStep 860659 = 1290989) B1290989
theorem B860675 : Blo 860564 860675 := bstep (se 1 (by rfl) ⟨645506, by rfl⟩ : syracuseStep 860675 = 1291013) B1291013
theorem B1942019 : Blo 860564 1942019 := bstep (se 1 (by rfl) ⟨1456514, by rfl⟩ : syracuseStep 1942019 = 2913029) B2913029
theorem B860691 : Blo 860564 860691 := bstep (se 1 (by rfl) ⟨645518, by rfl⟩ : syracuseStep 860691 = 1291037) B1291037
theorem B860707 : Blo 860564 860707 := bstep (se 1 (by rfl) ⟨645530, by rfl⟩ : syracuseStep 860707 = 1291061) B1291061
theorem B860723 : Blo 860564 860723 := bstep (se 1 (by rfl) ⟨645542, by rfl⟩ : syracuseStep 860723 = 1291085) B1291085
theorem B860739 : Blo 860564 860739 := bstep (se 1 (by rfl) ⟨645554, by rfl⟩ : syracuseStep 860739 = 1291109) B1291109
theorem B860755 : Blo 860564 860755 := bstep (se 1 (by rfl) ⟨645566, by rfl⟩ : syracuseStep 860755 = 1291133) B1291133
theorem B860771 : Blo 860564 860771 := bstep (se 1 (by rfl) ⟨645578, by rfl⟩ : syracuseStep 860771 = 1291157) B1291157
theorem B860787 : Blo 860564 860787 := bstep (se 1 (by rfl) ⟨645590, by rfl⟩ : syracuseStep 860787 = 1291181) B1291181
theorem B860803 : Blo 860564 860803 := bstep (se 1 (by rfl) ⟨645602, by rfl⟩ : syracuseStep 860803 = 1291205) B1291205
theorem B860819 : Blo 860564 860819 := bstep (se 1 (by rfl) ⟨645614, by rfl⟩ : syracuseStep 860819 = 1291229) B1291229
theorem B860835 : Blo 860564 860835 := bstep (se 1 (by rfl) ⟨645626, by rfl⟩ : syracuseStep 860835 = 1291253) B1291253
theorem B2073251 : Blo 860564 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B860851 : Blo 860564 860851 := bstep (se 1 (by rfl) ⟨645638, by rfl⟩ : syracuseStep 860851 = 1291277) B1291277
theorem B860867 : Blo 860564 860867 := bstep (se 1 (by rfl) ⟨645650, by rfl⟩ : syracuseStep 860867 = 1291301) B1291301
theorem B860883 : Blo 860564 860883 := bstep (se 1 (by rfl) ⟨645662, by rfl⟩ : syracuseStep 860883 = 1291325) B1291325
theorem B860899 : Blo 860564 860899 := bstep (se 1 (by rfl) ⟨645674, by rfl⟩ : syracuseStep 860899 = 1291349) B1291349
theorem B860915 : Blo 860564 860915 := bstep (se 1 (by rfl) ⟨645686, by rfl⟩ : syracuseStep 860915 = 1291373) B1291373
theorem B860931 : Blo 860564 860931 := bstep (se 1 (by rfl) ⟨645698, by rfl⟩ : syracuseStep 860931 = 1291397) B1291397
theorem B1942289 : Blo 860564 1942289 := bstep (se 2 (by rfl) ⟨728358, by rfl⟩ : syracuseStep 1942289 = 1456717) B1456717
theorem B860947 : Blo 860564 860947 := bstep (se 1 (by rfl) ⟨645710, by rfl⟩ : syracuseStep 860947 = 1291421) B1291421
theorem B860963 : Blo 860564 860963 := bstep (se 1 (by rfl) ⟨645722, by rfl⟩ : syracuseStep 860963 = 1291445) B1291445
theorem B1942307 : Blo 860564 1942307 := bstep (se 1 (by rfl) ⟨1456730, by rfl⟩ : syracuseStep 1942307 = 2913461) B2913461
theorem B860979 : Blo 860564 860979 := bstep (se 1 (by rfl) ⟨645734, by rfl⟩ : syracuseStep 860979 = 1291469) B1291469
theorem B860995 : Blo 860564 860995 := bstep (se 1 (by rfl) ⟨645746, by rfl⟩ : syracuseStep 860995 = 1291493) B1291493
theorem B861011 : Blo 860564 861011 := bstep (se 1 (by rfl) ⟨645758, by rfl⟩ : syracuseStep 861011 = 1291517) B1291517
theorem B861027 : Blo 860564 861027 := bstep (se 1 (by rfl) ⟨645770, by rfl⟩ : syracuseStep 861027 = 1291541) B1291541
theorem B2073443 : Blo 860564 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B861043 : Blo 860564 861043 := bstep (se 1 (by rfl) ⟨645782, by rfl⟩ : syracuseStep 861043 = 1291565) B1291565
theorem B861059 : Blo 860564 861059 := bstep (se 1 (by rfl) ⟨645794, by rfl⟩ : syracuseStep 861059 = 1291589) B1291589
theorem B861075 : Blo 860564 861075 := bstep (se 1 (by rfl) ⟨645806, by rfl⟩ : syracuseStep 861075 = 1291613) B1291613
theorem B861091 : Blo 860564 861091 := bstep (se 1 (by rfl) ⟨645818, by rfl⟩ : syracuseStep 861091 = 1291637) B1291637
theorem B861107 : Blo 860564 861107 := bstep (se 1 (by rfl) ⟨645830, by rfl⟩ : syracuseStep 861107 = 1291661) B1291661
theorem B861123 : Blo 860564 861123 := bstep (se 1 (by rfl) ⟨645842, by rfl⟩ : syracuseStep 861123 = 1291685) B1291685
theorem B861139 : Blo 860564 861139 := bstep (se 1 (by rfl) ⟨645854, by rfl⟩ : syracuseStep 861139 = 1291709) B1291709
theorem B861155 : Blo 860564 861155 := bstep (se 1 (by rfl) ⟨645866, by rfl⟩ : syracuseStep 861155 = 1291733) B1291733
theorem B861171 : Blo 860564 861171 := bstep (se 1 (by rfl) ⟨645878, by rfl⟩ : syracuseStep 861171 = 1291757) B1291757
theorem B861187 : Blo 860564 861187 := bstep (se 1 (by rfl) ⟨645890, by rfl⟩ : syracuseStep 861187 = 1291781) B1291781
theorem B861203 : Blo 860564 861203 := bstep (se 1 (by rfl) ⟨645902, by rfl⟩ : syracuseStep 861203 = 1291805) B1291805
theorem B1090579 : Blo 860564 1090579 := bstep (se 1 (by rfl) ⟨817934, by rfl⟩ : syracuseStep 1090579 = 1635869) B1635869
theorem B861219 : Blo 860564 861219 := bstep (se 1 (by rfl) ⟨645914, by rfl⟩ : syracuseStep 861219 = 1291829) B1291829
theorem B1942577 : Blo 860564 1942577 := bstep (se 2 (by rfl) ⟨728466, by rfl⟩ : syracuseStep 1942577 = 1456933) B1456933
theorem B861235 : Blo 860564 861235 := bstep (se 1 (by rfl) ⟨645926, by rfl⟩ : syracuseStep 861235 = 1291853) B1291853
theorem B861251 : Blo 860564 861251 := bstep (se 1 (by rfl) ⟨645938, by rfl⟩ : syracuseStep 861251 = 1291877) B1291877
theorem B1942595 : Blo 860564 1942595 := bstep (se 1 (by rfl) ⟨1456946, by rfl⟩ : syracuseStep 1942595 = 2913893) B2913893
theorem B1844291 : Blo 860564 1844291 := bstep (se 1 (by rfl) ⟨1383218, by rfl⟩ : syracuseStep 1844291 = 2766437) B2766437
theorem B5514317 : Blo 860564 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B861267 : Blo 860564 861267 := bstep (se 1 (by rfl) ⟨645950, by rfl⟩ : syracuseStep 861267 = 1291901) B1291901
theorem B861283 : Blo 860564 861283 := bstep (se 1 (by rfl) ⟨645962, by rfl⟩ : syracuseStep 861283 = 1291925) B1291925
theorem B861299 : Blo 860564 861299 := bstep (se 1 (by rfl) ⟨645974, by rfl⟩ : syracuseStep 861299 = 1291949) B1291949
theorem B1090675 : Blo 860564 1090675 := bstep (se 1 (by rfl) ⟨818006, by rfl⟩ : syracuseStep 1090675 = 1636013) B1636013
theorem B861315 : Blo 860564 861315 := bstep (se 1 (by rfl) ⟨645986, by rfl⟩ : syracuseStep 861315 = 1291973) B1291973
theorem B861331 : Blo 860564 861331 := bstep (se 1 (by rfl) ⟨645998, by rfl⟩ : syracuseStep 861331 = 1291997) B1291997
theorem B861347 : Blo 860564 861347 := bstep (se 1 (by rfl) ⟨646010, by rfl⟩ : syracuseStep 861347 = 1292021) B1292021
theorem B2761901 : Blo 860564 2761901 := bstep (se 3 (by rfl) ⟨517856, by rfl⟩ : syracuseStep 2761901 = 1035713) B1035713
theorem B861363 : Blo 860564 861363 := bstep (se 1 (by rfl) ⟨646022, by rfl⟩ : syracuseStep 861363 = 1292045) B1292045
theorem B861379 : Blo 860564 861379 := bstep (se 1 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 861379 = 1292069) B1292069
theorem B861395 : Blo 860564 861395 := bstep (se 1 (by rfl) ⟨646046, by rfl⟩ : syracuseStep 861395 = 1292093) B1292093
theorem B861411 : Blo 860564 861411 := bstep (se 1 (by rfl) ⟨646058, by rfl⟩ : syracuseStep 861411 = 1292117) B1292117
theorem B861427 : Blo 860564 861427 := bstep (se 1 (by rfl) ⟨646070, by rfl⟩ : syracuseStep 861427 = 1292141) B1292141
theorem B861443 : Blo 860564 861443 := bstep (se 1 (by rfl) ⟨646082, by rfl⟩ : syracuseStep 861443 = 1292165) B1292165
theorem B861459 : Blo 860564 861459 := bstep (se 1 (by rfl) ⟨646094, by rfl⟩ : syracuseStep 861459 = 1292189) B1292189
theorem B861475 : Blo 860564 861475 := bstep (se 1 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 861475 = 1292213) B1292213
theorem B861491 : Blo 860564 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B861507 : Blo 860564 861507 := bstep (se 1 (by rfl) ⟨646130, by rfl⟩ : syracuseStep 861507 = 1292261) B1292261
theorem B1942865 : Blo 860564 1942865 := bstep (se 2 (by rfl) ⟨728574, by rfl⟩ : syracuseStep 1942865 = 1457149) B1457149
theorem B861523 : Blo 860564 861523 := bstep (se 1 (by rfl) ⟨646142, by rfl⟩ : syracuseStep 861523 = 1292285) B1292285
theorem B861539 : Blo 860564 861539 := bstep (se 1 (by rfl) ⟨646154, by rfl⟩ : syracuseStep 861539 = 1292309) B1292309
theorem B1942883 : Blo 860564 1942883 := bstep (se 1 (by rfl) ⟨1457162, by rfl⟩ : syracuseStep 1942883 = 2914325) B2914325
theorem B861555 : Blo 860564 861555 := bstep (se 1 (by rfl) ⟨646166, by rfl⟩ : syracuseStep 861555 = 1292333) B1292333
theorem B861571 : Blo 860564 861571 := bstep (se 1 (by rfl) ⟨646178, by rfl⟩ : syracuseStep 861571 = 1292357) B1292357
theorem B861587 : Blo 860564 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B861603 : Blo 860564 861603 := bstep (se 1 (by rfl) ⟨646202, by rfl⟩ : syracuseStep 861603 = 1292405) B1292405
theorem B861619 : Blo 860564 861619 := bstep (se 1 (by rfl) ⟨646214, by rfl⟩ : syracuseStep 861619 = 1292429) B1292429
theorem B861635 : Blo 860564 861635 := bstep (se 1 (by rfl) ⟨646226, by rfl⟩ : syracuseStep 861635 = 1292453) B1292453
theorem B861651 : Blo 860564 861651 := bstep (se 1 (by rfl) ⟨646238, by rfl⟩ : syracuseStep 861651 = 1292477) B1292477
theorem B861667 : Blo 860564 861667 := bstep (se 1 (by rfl) ⟨646250, by rfl⟩ : syracuseStep 861667 = 1292501) B1292501
theorem B4367843 : Blo 860564 4367843 := bstep (se 1 (by rfl) ⟨3275882, by rfl⟩ : syracuseStep 4367843 = 6551765) B6551765
theorem B861683 : Blo 860564 861683 := bstep (se 1 (by rfl) ⟨646262, by rfl⟩ : syracuseStep 861683 = 1292525) B1292525
theorem B861699 : Blo 860564 861699 := bstep (se 1 (by rfl) ⟨646274, by rfl⟩ : syracuseStep 861699 = 1292549) B1292549
theorem B861715 : Blo 860564 861715 := bstep (se 1 (by rfl) ⟨646286, by rfl⟩ : syracuseStep 861715 = 1292573) B1292573
theorem B861731 : Blo 860564 861731 := bstep (se 1 (by rfl) ⟨646298, by rfl⟩ : syracuseStep 861731 = 1292597) B1292597
theorem B861747 : Blo 860564 861747 := bstep (se 1 (by rfl) ⟨646310, by rfl⟩ : syracuseStep 861747 = 1292621) B1292621
theorem B861763 : Blo 860564 861763 := bstep (se 1 (by rfl) ⟨646322, by rfl⟩ : syracuseStep 861763 = 1292645) B1292645
theorem B1844803 : Blo 860564 1844803 := bstep (se 1 (by rfl) ⟨1383602, by rfl⟩ : syracuseStep 1844803 = 2767205) B2767205
theorem B861779 : Blo 860564 861779 := bstep (se 1 (by rfl) ⟨646334, by rfl⟩ : syracuseStep 861779 = 1292669) B1292669
theorem B861795 : Blo 860564 861795 := bstep (se 1 (by rfl) ⟨646346, by rfl⟩ : syracuseStep 861795 = 1292693) B1292693
theorem B1091171 : Blo 860564 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B1943153 : Blo 860564 1943153 := bstep (se 2 (by rfl) ⟨728682, by rfl⟩ : syracuseStep 1943153 = 1457365) B1457365
theorem B861811 : Blo 860564 861811 := bstep (se 1 (by rfl) ⟨646358, by rfl⟩ : syracuseStep 861811 = 1292717) B1292717
theorem B861827 : Blo 860564 861827 := bstep (se 1 (by rfl) ⟨646370, by rfl⟩ : syracuseStep 861827 = 1292741) B1292741
theorem B1943171 : Blo 860564 1943171 := bstep (se 1 (by rfl) ⟨1457378, by rfl⟩ : syracuseStep 1943171 = 2914757) B2914757
theorem B861843 : Blo 860564 861843 := bstep (se 1 (by rfl) ⟨646382, by rfl⟩ : syracuseStep 861843 = 1292765) B1292765
theorem B861859 : Blo 860564 861859 := bstep (se 1 (by rfl) ⟨646394, by rfl⟩ : syracuseStep 861859 = 1292789) B1292789
theorem B861875 : Blo 860564 861875 := bstep (se 1 (by rfl) ⟨646406, by rfl⟩ : syracuseStep 861875 = 1292813) B1292813
theorem B861891 : Blo 860564 861891 := bstep (se 1 (by rfl) ⟨646418, by rfl⟩ : syracuseStep 861891 = 1292837) B1292837
theorem B861907 : Blo 860564 861907 := bstep (se 1 (by rfl) ⟨646430, by rfl⟩ : syracuseStep 861907 = 1292861) B1292861
theorem B861923 : Blo 860564 861923 := bstep (se 1 (by rfl) ⟨646442, by rfl⟩ : syracuseStep 861923 = 1292885) B1292885
theorem B861939 : Blo 860564 861939 := bstep (se 1 (by rfl) ⟨646454, by rfl⟩ : syracuseStep 861939 = 1292909) B1292909
theorem B861955 : Blo 860564 861955 := bstep (se 1 (by rfl) ⟨646466, by rfl⟩ : syracuseStep 861955 = 1292933) B1292933
theorem B861971 : Blo 860564 861971 := bstep (se 1 (by rfl) ⟨646478, by rfl⟩ : syracuseStep 861971 = 1292957) B1292957
theorem B861987 : Blo 860564 861987 := bstep (se 1 (by rfl) ⟨646490, by rfl⟩ : syracuseStep 861987 = 1292981) B1292981
theorem B862003 : Blo 860564 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B862019 : Blo 860564 862019 := bstep (se 1 (by rfl) ⟨646514, by rfl⟩ : syracuseStep 862019 = 1293029) B1293029
theorem B862035 : Blo 860564 862035 := bstep (se 1 (by rfl) ⟨646526, by rfl⟩ : syracuseStep 862035 = 1293053) B1293053
theorem B862051 : Blo 860564 862051 := bstep (se 1 (by rfl) ⟨646538, by rfl⟩ : syracuseStep 862051 = 1293077) B1293077
theorem B862067 : Blo 860564 862067 := bstep (se 1 (by rfl) ⟨646550, by rfl⟩ : syracuseStep 862067 = 1293101) B1293101
theorem B862083 : Blo 860564 862083 := bstep (se 1 (by rfl) ⟨646562, by rfl⟩ : syracuseStep 862083 = 1293125) B1293125
theorem B1943441 : Blo 860564 1943441 := bstep (se 2 (by rfl) ⟨728790, by rfl⟩ : syracuseStep 1943441 = 1457581) B1457581
theorem B862099 : Blo 860564 862099 := bstep (se 1 (by rfl) ⟨646574, by rfl⟩ : syracuseStep 862099 = 1293149) B1293149
theorem B862115 : Blo 860564 862115 := bstep (se 1 (by rfl) ⟨646586, by rfl⟩ : syracuseStep 862115 = 1293173) B1293173
theorem B1943459 : Blo 860564 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B862131 : Blo 860564 862131 := bstep (se 1 (by rfl) ⟨646598, by rfl⟩ : syracuseStep 862131 = 1293197) B1293197
theorem B862147 : Blo 860564 862147 := bstep (se 1 (by rfl) ⟨646610, by rfl⟩ : syracuseStep 862147 = 1293221) B1293221
theorem B862163 : Blo 860564 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B862179 : Blo 860564 862179 := bstep (se 1 (by rfl) ⟨646634, by rfl⟩ : syracuseStep 862179 = 1293269) B1293269
theorem B862195 : Blo 860564 862195 := bstep (se 1 (by rfl) ⟨646646, by rfl⟩ : syracuseStep 862195 = 1293293) B1293293
theorem B862211 : Blo 860564 862211 := bstep (se 1 (by rfl) ⟨646658, by rfl⟩ : syracuseStep 862211 = 1293317) B1293317
theorem B862227 : Blo 860564 862227 := bstep (se 1 (by rfl) ⟨646670, by rfl⟩ : syracuseStep 862227 = 1293341) B1293341
theorem B862243 : Blo 860564 862243 := bstep (se 1 (by rfl) ⟨646682, by rfl⟩ : syracuseStep 862243 = 1293365) B1293365
theorem B862259 : Blo 860564 862259 := bstep (se 1 (by rfl) ⟨646694, by rfl⟩ : syracuseStep 862259 = 1293389) B1293389
theorem B862275 : Blo 860564 862275 := bstep (se 1 (by rfl) ⟨646706, by rfl⟩ : syracuseStep 862275 = 1293413) B1293413
theorem B862291 : Blo 860564 862291 := bstep (se 1 (by rfl) ⟨646718, by rfl⟩ : syracuseStep 862291 = 1293437) B1293437
theorem B862307 : Blo 860564 862307 := bstep (se 1 (by rfl) ⟨646730, by rfl⟩ : syracuseStep 862307 = 1293461) B1293461
theorem B862323 : Blo 860564 862323 := bstep (se 1 (by rfl) ⟨646742, by rfl⟩ : syracuseStep 862323 = 1293485) B1293485
theorem B862339 : Blo 860564 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B862355 : Blo 860564 862355 := bstep (se 1 (by rfl) ⟨646766, by rfl⟩ : syracuseStep 862355 = 1293533) B1293533
theorem B862371 : Blo 860564 862371 := bstep (se 1 (by rfl) ⟨646778, by rfl⟩ : syracuseStep 862371 = 1293557) B1293557
theorem B1943729 : Blo 860564 1943729 := bstep (se 2 (by rfl) ⟨728898, by rfl⟩ : syracuseStep 1943729 = 1457797) B1457797
theorem B862387 : Blo 860564 862387 := bstep (se 1 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 862387 = 1293581) B1293581
theorem B862403 : Blo 860564 862403 := bstep (se 1 (by rfl) ⟨646802, by rfl⟩ : syracuseStep 862403 = 1293605) B1293605
theorem B1943747 : Blo 860564 1943747 := bstep (se 1 (by rfl) ⟨1457810, by rfl⟩ : syracuseStep 1943747 = 2915621) B2915621
theorem B862419 : Blo 860564 862419 := bstep (se 1 (by rfl) ⟨646814, by rfl⟩ : syracuseStep 862419 = 1293629) B1293629
theorem B862435 : Blo 860564 862435 := bstep (se 1 (by rfl) ⟨646826, by rfl⟩ : syracuseStep 862435 = 1293653) B1293653
theorem B862451 : Blo 860564 862451 := bstep (se 1 (by rfl) ⟨646838, by rfl⟩ : syracuseStep 862451 = 1293677) B1293677
theorem B1452289 : Blo 860564 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B862467 : Blo 860564 862467 := bstep (se 1 (by rfl) ⟨646850, by rfl⟩ : syracuseStep 862467 = 1293701) B1293701
theorem B4368653 : Blo 860564 4368653 := bstep (se 3 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 4368653 = 1638245) B1638245
theorem B1845521 : Blo 860564 1845521 := bstep (se 2 (by rfl) ⟨692070, by rfl⟩ : syracuseStep 1845521 = 1384141) B1384141
theorem B862483 : Blo 860564 862483 := bstep (se 1 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 862483 = 1293725) B1293725
theorem B1452323 : Blo 860564 1452323 := bstep (se 1 (by rfl) ⟨1089242, by rfl⟩ : syracuseStep 1452323 = 2178485) B2178485
theorem B862499 : Blo 860564 862499 := bstep (se 1 (by rfl) ⟨646874, by rfl⟩ : syracuseStep 862499 = 1293749) B1293749
theorem B1091875 : Blo 860564 1091875 := bstep (se 1 (by rfl) ⟨818906, by rfl⟩ : syracuseStep 1091875 = 1637813) B1637813
theorem B862515 : Blo 860564 862515 := bstep (se 1 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 862515 = 1293773) B1293773
theorem B862531 : Blo 860564 862531 := bstep (se 1 (by rfl) ⟨646898, by rfl⟩ : syracuseStep 862531 = 1293797) B1293797
theorem B862547 : Blo 860564 862547 := bstep (se 1 (by rfl) ⟨646910, by rfl⟩ : syracuseStep 862547 = 1293821) B1293821
theorem B862563 : Blo 860564 862563 := bstep (se 1 (by rfl) ⟨646922, by rfl⟩ : syracuseStep 862563 = 1293845) B1293845
theorem B862579 : Blo 860564 862579 := bstep (se 1 (by rfl) ⟨646934, by rfl⟩ : syracuseStep 862579 = 1293869) B1293869
theorem B862595 : Blo 860564 862595 := bstep (se 1 (by rfl) ⟨646946, by rfl⟩ : syracuseStep 862595 = 1293893) B1293893
theorem B1091971 : Blo 860564 1091971 := bstep (se 1 (by rfl) ⟨818978, by rfl⟩ : syracuseStep 1091971 = 1637957) B1637957
theorem B3680653 : Blo 860564 3680653 := bstep (se 3 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 3680653 = 1380245) B1380245
theorem B862611 : Blo 860564 862611 := bstep (se 1 (by rfl) ⟨646958, by rfl⟩ : syracuseStep 862611 = 1293917) B1293917
theorem B1452451 : Blo 860564 1452451 := bstep (se 1 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 1452451 = 2178677) B2178677
theorem B862627 : Blo 860564 862627 := bstep (se 1 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 862627 = 1293941) B1293941
theorem B862643 : Blo 860564 862643 := bstep (se 1 (by rfl) ⟨646982, by rfl⟩ : syracuseStep 862643 = 1293965) B1293965
theorem B862659 : Blo 860564 862659 := bstep (se 1 (by rfl) ⟨646994, by rfl⟩ : syracuseStep 862659 = 1293989) B1293989
theorem B2238929 : Blo 860564 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B1944017 : Blo 860564 1944017 := bstep (se 2 (by rfl) ⟨729006, by rfl⟩ : syracuseStep 1944017 = 1458013) B1458013
theorem B862675 : Blo 860564 862675 := bstep (se 1 (by rfl) ⟨647006, by rfl⟩ : syracuseStep 862675 = 1294013) B1294013
theorem B862691 : Blo 860564 862691 := bstep (se 1 (by rfl) ⟨647018, by rfl⟩ : syracuseStep 862691 = 1294037) B1294037
theorem B1944035 : Blo 860564 1944035 := bstep (se 1 (by rfl) ⟨1458026, by rfl⟩ : syracuseStep 1944035 = 2916053) B2916053
theorem B862707 : Blo 860564 862707 := bstep (se 1 (by rfl) ⟨647030, by rfl⟩ : syracuseStep 862707 = 1294061) B1294061
theorem B862723 : Blo 860564 862723 := bstep (se 1 (by rfl) ⟨647042, by rfl⟩ : syracuseStep 862723 = 1294085) B1294085
theorem B862739 : Blo 860564 862739 := bstep (se 1 (by rfl) ⟨647054, by rfl⟩ : syracuseStep 862739 = 1294109) B1294109
theorem B862755 : Blo 860564 862755 := bstep (se 1 (by rfl) ⟨647066, by rfl⟩ : syracuseStep 862755 = 1294133) B1294133
theorem B1452593 : Blo 860564 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B862771 : Blo 860564 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B862787 : Blo 860564 862787 := bstep (se 1 (by rfl) ⟨647090, by rfl⟩ : syracuseStep 862787 = 1294181) B1294181
theorem B862803 : Blo 860564 862803 := bstep (se 1 (by rfl) ⟨647102, by rfl⟩ : syracuseStep 862803 = 1294205) B1294205
theorem B862819 : Blo 860564 862819 := bstep (se 1 (by rfl) ⟨647114, by rfl⟩ : syracuseStep 862819 = 1294229) B1294229
theorem B862835 : Blo 860564 862835 := bstep (se 1 (by rfl) ⟨647126, by rfl⟩ : syracuseStep 862835 = 1294253) B1294253
theorem B862851 : Blo 860564 862851 := bstep (se 1 (by rfl) ⟨647138, by rfl⟩ : syracuseStep 862851 = 1294277) B1294277
theorem B862867 : Blo 860564 862867 := bstep (se 1 (by rfl) ⟨647150, by rfl⟩ : syracuseStep 862867 = 1294301) B1294301
theorem B862883 : Blo 860564 862883 := bstep (se 1 (by rfl) ⟨647162, by rfl⟩ : syracuseStep 862883 = 1294325) B1294325
theorem B1452721 : Blo 860564 1452721 := bstep (se 2 (by rfl) ⟨544770, by rfl⟩ : syracuseStep 1452721 = 1089541) B1089541
theorem B862899 : Blo 860564 862899 := bstep (se 1 (by rfl) ⟨647174, by rfl⟩ : syracuseStep 862899 = 1294349) B1294349
theorem B862915 : Blo 860564 862915 := bstep (se 1 (by rfl) ⟨647186, by rfl⟩ : syracuseStep 862915 = 1294373) B1294373
theorem B1452755 : Blo 860564 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B862931 : Blo 860564 862931 := bstep (se 1 (by rfl) ⟨647198, by rfl⟩ : syracuseStep 862931 = 1294397) B1294397
theorem B862947 : Blo 860564 862947 := bstep (se 1 (by rfl) ⟨647210, by rfl⟩ : syracuseStep 862947 = 1294421) B1294421
theorem B1944305 : Blo 860564 1944305 := bstep (se 2 (by rfl) ⟨729114, by rfl⟩ : syracuseStep 1944305 = 1458229) B1458229
theorem B862963 : Blo 860564 862963 := bstep (se 1 (by rfl) ⟨647222, by rfl⟩ : syracuseStep 862963 = 1294445) B1294445
theorem B862979 : Blo 860564 862979 := bstep (se 1 (by rfl) ⟨647234, by rfl⟩ : syracuseStep 862979 = 1294469) B1294469
theorem B2075395 : Blo 860564 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1944323 : Blo 860564 1944323 := bstep (se 1 (by rfl) ⟨1458242, by rfl⟩ : syracuseStep 1944323 = 2916485) B2916485
theorem B862995 : Blo 860564 862995 := bstep (se 1 (by rfl) ⟨647246, by rfl⟩ : syracuseStep 862995 = 1294493) B1294493
theorem B863011 : Blo 860564 863011 := bstep (se 1 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 863011 = 1294517) B1294517
theorem B863027 : Blo 860564 863027 := bstep (se 1 (by rfl) ⟨647270, by rfl⟩ : syracuseStep 863027 = 1294541) B1294541
theorem B863043 : Blo 860564 863043 := bstep (se 1 (by rfl) ⟨647282, by rfl⟩ : syracuseStep 863043 = 1294565) B1294565
theorem B1452883 : Blo 860564 1452883 := bstep (se 1 (by rfl) ⟨1089662, by rfl⟩ : syracuseStep 1452883 = 2179325) B2179325
theorem B863059 : Blo 860564 863059 := bstep (se 1 (by rfl) ⟨647294, by rfl⟩ : syracuseStep 863059 = 1294589) B1294589
theorem B863075 : Blo 860564 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B863091 : Blo 860564 863091 := bstep (se 1 (by rfl) ⟨647318, by rfl⟩ : syracuseStep 863091 = 1294637) B1294637
theorem B1092467 : Blo 860564 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B863107 : Blo 860564 863107 := bstep (se 1 (by rfl) ⟨647330, by rfl⟩ : syracuseStep 863107 = 1294661) B1294661
theorem B5909381 : Blo 860564 5909381 := bstep (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) B1108009
theorem B863123 : Blo 860564 863123 := bstep (se 1 (by rfl) ⟨647342, by rfl⟩ : syracuseStep 863123 = 1294685) B1294685
theorem B863139 : Blo 860564 863139 := bstep (se 1 (by rfl) ⟨647354, by rfl⟩ : syracuseStep 863139 = 1294709) B1294709
theorem B863155 : Blo 860564 863155 := bstep (se 1 (by rfl) ⟨647366, by rfl⟩ : syracuseStep 863155 = 1294733) B1294733
theorem B863171 : Blo 860564 863171 := bstep (se 1 (by rfl) ⟨647378, by rfl⟩ : syracuseStep 863171 = 1294757) B1294757
theorem B863187 : Blo 860564 863187 := bstep (se 1 (by rfl) ⟨647390, by rfl⟩ : syracuseStep 863187 = 1294781) B1294781
theorem B1453025 : Blo 860564 1453025 := bstep (se 2 (by rfl) ⟨544884, by rfl⟩ : syracuseStep 1453025 = 1089769) B1089769
theorem B863203 : Blo 860564 863203 := bstep (se 1 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 863203 = 1294805) B1294805
theorem B863219 : Blo 860564 863219 := bstep (se 1 (by rfl) ⟨647414, by rfl⟩ : syracuseStep 863219 = 1294829) B1294829
theorem B863235 : Blo 860564 863235 := bstep (se 1 (by rfl) ⟨647426, by rfl⟩ : syracuseStep 863235 = 1294853) B1294853
theorem B1944593 : Blo 860564 1944593 := bstep (se 2 (by rfl) ⟨729222, by rfl⟩ : syracuseStep 1944593 = 1458445) B1458445
theorem B863251 : Blo 860564 863251 := bstep (se 1 (by rfl) ⟨647438, by rfl⟩ : syracuseStep 863251 = 1294877) B1294877
theorem B5319715 : Blo 860564 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B863267 : Blo 860564 863267 := bstep (se 1 (by rfl) ⟨647450, by rfl⟩ : syracuseStep 863267 = 1294901) B1294901
theorem B1944611 : Blo 860564 1944611 := bstep (se 1 (by rfl) ⟨1458458, by rfl⟩ : syracuseStep 1944611 = 2916917) B2916917
theorem B1846307 : Blo 860564 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B863283 : Blo 860564 863283 := bstep (se 1 (by rfl) ⟨647462, by rfl⟩ : syracuseStep 863283 = 1294925) B1294925
theorem B863299 : Blo 860564 863299 := bstep (se 1 (by rfl) ⟨647474, by rfl⟩ : syracuseStep 863299 = 1294949) B1294949
theorem B863315 : Blo 860564 863315 := bstep (se 1 (by rfl) ⟨647486, by rfl⟩ : syracuseStep 863315 = 1294973) B1294973
theorem B1453153 : Blo 860564 1453153 := bstep (se 2 (by rfl) ⟨544932, by rfl⟩ : syracuseStep 1453153 = 1089865) B1089865
theorem B863331 : Blo 860564 863331 := bstep (se 1 (by rfl) ⟨647498, by rfl⟩ : syracuseStep 863331 = 1294997) B1294997
theorem B863347 : Blo 860564 863347 := bstep (se 1 (by rfl) ⟨647510, by rfl⟩ : syracuseStep 863347 = 1295021) B1295021
theorem B1453187 : Blo 860564 1453187 := bstep (se 1 (by rfl) ⟨1089890, by rfl⟩ : syracuseStep 1453187 = 2179781) B2179781
theorem B863363 : Blo 860564 863363 := bstep (se 1 (by rfl) ⟨647522, by rfl⟩ : syracuseStep 863363 = 1295045) B1295045
theorem B863379 : Blo 860564 863379 := bstep (se 1 (by rfl) ⟨647534, by rfl⟩ : syracuseStep 863379 = 1295069) B1295069
theorem B863395 : Blo 860564 863395 := bstep (se 1 (by rfl) ⟨647546, by rfl⟩ : syracuseStep 863395 = 1295093) B1295093
theorem B863411 : Blo 860564 863411 := bstep (se 1 (by rfl) ⟨647558, by rfl⟩ : syracuseStep 863411 = 1295117) B1295117
theorem B863427 : Blo 860564 863427 := bstep (se 1 (by rfl) ⟨647570, by rfl⟩ : syracuseStep 863427 = 1295141) B1295141
theorem B863443 : Blo 860564 863443 := bstep (se 1 (by rfl) ⟨647582, by rfl⟩ : syracuseStep 863443 = 1295165) B1295165
theorem B863459 : Blo 860564 863459 := bstep (se 1 (by rfl) ⟨647594, by rfl⟩ : syracuseStep 863459 = 1295189) B1295189
theorem B863475 : Blo 860564 863475 := bstep (se 1 (by rfl) ⟨647606, by rfl⟩ : syracuseStep 863475 = 1295213) B1295213
theorem B1453315 : Blo 860564 1453315 := bstep (se 1 (by rfl) ⟨1089986, by rfl⟩ : syracuseStep 1453315 = 2179973) B2179973
theorem B863491 : Blo 860564 863491 := bstep (se 1 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 863491 = 1295237) B1295237
theorem B863507 : Blo 860564 863507 := bstep (se 1 (by rfl) ⟨647630, by rfl⟩ : syracuseStep 863507 = 1295261) B1295261
theorem B863523 : Blo 860564 863523 := bstep (se 1 (by rfl) ⟨647642, by rfl⟩ : syracuseStep 863523 = 1295285) B1295285
theorem B1944881 : Blo 860564 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B863539 : Blo 860564 863539 := bstep (se 1 (by rfl) ⟨647654, by rfl⟩ : syracuseStep 863539 = 1295309) B1295309
theorem B863555 : Blo 860564 863555 := bstep (se 1 (by rfl) ⟨647666, by rfl⟩ : syracuseStep 863555 = 1295333) B1295333
theorem B1944899 : Blo 860564 1944899 := bstep (se 1 (by rfl) ⟨1458674, by rfl⟩ : syracuseStep 1944899 = 2917349) B2917349
theorem B863571 : Blo 860564 863571 := bstep (se 1 (by rfl) ⟨647678, by rfl⟩ : syracuseStep 863571 = 1295357) B1295357
theorem B863587 : Blo 860564 863587 := bstep (se 1 (by rfl) ⟨647690, by rfl⟩ : syracuseStep 863587 = 1295381) B1295381
theorem B863603 : Blo 860564 863603 := bstep (se 1 (by rfl) ⟨647702, by rfl⟩ : syracuseStep 863603 = 1295405) B1295405
theorem B863619 : Blo 860564 863619 := bstep (se 1 (by rfl) ⟨647714, by rfl⟩ : syracuseStep 863619 = 1295429) B1295429
theorem B1453457 : Blo 860564 1453457 := bstep (se 2 (by rfl) ⟨545046, by rfl⟩ : syracuseStep 1453457 = 1090093) B1090093
theorem B863635 : Blo 860564 863635 := bstep (se 1 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 863635 = 1295453) B1295453
theorem B863651 : Blo 860564 863651 := bstep (se 1 (by rfl) ⟨647738, by rfl⟩ : syracuseStep 863651 = 1295477) B1295477
theorem B3681713 : Blo 860564 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B863667 : Blo 860564 863667 := bstep (se 1 (by rfl) ⟨647750, by rfl⟩ : syracuseStep 863667 = 1295501) B1295501
theorem B863683 : Blo 860564 863683 := bstep (se 1 (by rfl) ⟨647762, by rfl⟩ : syracuseStep 863683 = 1295525) B1295525
theorem B7876037 : Blo 860564 7876037 := bstep (se 4 (by rfl) ⟨738378, by rfl⟩ : syracuseStep 7876037 = 1476757) B1476757
theorem B863699 : Blo 860564 863699 := bstep (se 1 (by rfl) ⟨647774, by rfl⟩ : syracuseStep 863699 = 1295549) B1295549
theorem B863715 : Blo 860564 863715 := bstep (se 1 (by rfl) ⟨647786, by rfl⟩ : syracuseStep 863715 = 1295573) B1295573
theorem B863731 : Blo 860564 863731 := bstep (se 1 (by rfl) ⟨647798, by rfl⟩ : syracuseStep 863731 = 1295597) B1295597
theorem B863747 : Blo 860564 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B4435469 : Blo 860564 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B1453585 : Blo 860564 1453585 := bstep (se 2 (by rfl) ⟨545094, by rfl⟩ : syracuseStep 1453585 = 1090189) B1090189
theorem B863763 : Blo 860564 863763 := bstep (se 1 (by rfl) ⟨647822, by rfl⟩ : syracuseStep 863763 = 1295645) B1295645
theorem B863779 : Blo 860564 863779 := bstep (se 1 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 863779 = 1295669) B1295669
theorem B1453619 : Blo 860564 1453619 := bstep (se 1 (by rfl) ⟨1090214, by rfl⟩ : syracuseStep 1453619 = 2180429) B2180429
theorem B1093171 : Blo 860564 1093171 := bstep (se 1 (by rfl) ⟨819878, by rfl⟩ : syracuseStep 1093171 = 1639757) B1639757
theorem B863795 : Blo 860564 863795 := bstep (se 1 (by rfl) ⟨647846, by rfl⟩ : syracuseStep 863795 = 1295693) B1295693
theorem B15773237 : Blo 860564 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B863811 : Blo 860564 863811 := bstep (se 1 (by rfl) ⟨647858, by rfl⟩ : syracuseStep 863811 = 1295717) B1295717
theorem B1945169 : Blo 860564 1945169 := bstep (se 2 (by rfl) ⟨729438, by rfl⟩ : syracuseStep 1945169 = 1458877) B1458877
theorem B863827 : Blo 860564 863827 := bstep (se 1 (by rfl) ⟨647870, by rfl⟩ : syracuseStep 863827 = 1295741) B1295741
theorem B863843 : Blo 860564 863843 := bstep (se 1 (by rfl) ⟨647882, by rfl⟩ : syracuseStep 863843 = 1295765) B1295765
theorem B1945187 : Blo 860564 1945187 := bstep (se 1 (by rfl) ⟨1458890, by rfl⟩ : syracuseStep 1945187 = 2917781) B2917781
theorem B2993773 : Blo 860564 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B863859 : Blo 860564 863859 := bstep (se 1 (by rfl) ⟨647894, by rfl⟩ : syracuseStep 863859 = 1295789) B1295789
theorem B863875 : Blo 860564 863875 := bstep (se 1 (by rfl) ⟨647906, by rfl⟩ : syracuseStep 863875 = 1295813) B1295813
theorem B1093267 : Blo 860564 1093267 := bstep (se 1 (by rfl) ⟨819950, by rfl⟩ : syracuseStep 1093267 = 1639901) B1639901
theorem B863891 : Blo 860564 863891 := bstep (se 1 (by rfl) ⟨647918, by rfl⟩ : syracuseStep 863891 = 1295837) B1295837
theorem B863907 : Blo 860564 863907 := bstep (se 1 (by rfl) ⟨647930, by rfl⟩ : syracuseStep 863907 = 1295861) B1295861
theorem B1552049 : Blo 860564 1552049 := bstep (se 2 (by rfl) ⟨582018, by rfl⟩ : syracuseStep 1552049 = 1164037) B1164037
theorem B1453747 : Blo 860564 1453747 := bstep (se 1 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 1453747 = 2180621) B2180621
theorem B863923 : Blo 860564 863923 := bstep (se 1 (by rfl) ⟨647942, by rfl⟩ : syracuseStep 863923 = 1295885) B1295885
theorem B863939 : Blo 860564 863939 := bstep (se 1 (by rfl) ⟨647954, by rfl⟩ : syracuseStep 863939 = 1295909) B1295909
theorem B863955 : Blo 860564 863955 := bstep (se 1 (by rfl) ⟨647966, by rfl⟩ : syracuseStep 863955 = 1295933) B1295933
theorem B863971 : Blo 860564 863971 := bstep (se 1 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 863971 = 1295957) B1295957
theorem B863987 : Blo 860564 863987 := bstep (se 1 (by rfl) ⟨647990, by rfl⟩ : syracuseStep 863987 = 1295981) B1295981
theorem B864003 : Blo 860564 864003 := bstep (se 1 (by rfl) ⟨648002, by rfl⟩ : syracuseStep 864003 = 1296005) B1296005
theorem B864019 : Blo 860564 864019 := bstep (se 1 (by rfl) ⟨648014, by rfl⟩ : syracuseStep 864019 = 1296029) B1296029
theorem B864035 : Blo 860564 864035 := bstep (se 1 (by rfl) ⟨648026, by rfl⟩ : syracuseStep 864035 = 1296053) B1296053
theorem B864051 : Blo 860564 864051 := bstep (se 1 (by rfl) ⟨648038, by rfl⟩ : syracuseStep 864051 = 1296077) B1296077
theorem B1453889 : Blo 860564 1453889 := bstep (se 2 (by rfl) ⟨545208, by rfl⟩ : syracuseStep 1453889 = 1090417) B1090417
theorem B864067 : Blo 860564 864067 := bstep (se 1 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 864067 = 1296101) B1296101
theorem B864083 : Blo 860564 864083 := bstep (se 1 (by rfl) ⟨648062, by rfl⟩ : syracuseStep 864083 = 1296125) B1296125
theorem B864099 : Blo 860564 864099 := bstep (se 1 (by rfl) ⟨648074, by rfl⟩ : syracuseStep 864099 = 1296149) B1296149
theorem B864115 : Blo 860564 864115 := bstep (se 1 (by rfl) ⟨648086, by rfl⟩ : syracuseStep 864115 = 1296173) B1296173
theorem B864131 : Blo 860564 864131 := bstep (se 1 (by rfl) ⟨648098, by rfl⟩ : syracuseStep 864131 = 1296197) B1296197
theorem B864147 : Blo 860564 864147 := bstep (se 1 (by rfl) ⟨648110, by rfl⟩ : syracuseStep 864147 = 1296221) B1296221
theorem B864163 : Blo 860564 864163 := bstep (se 1 (by rfl) ⟨648122, by rfl⟩ : syracuseStep 864163 = 1296245) B1296245
theorem B864179 : Blo 860564 864179 := bstep (se 1 (by rfl) ⟨648134, by rfl⟩ : syracuseStep 864179 = 1296269) B1296269
theorem B1454017 : Blo 860564 1454017 := bstep (se 2 (by rfl) ⟨545256, by rfl⟩ : syracuseStep 1454017 = 1090513) B1090513
theorem B864195 : Blo 860564 864195 := bstep (se 1 (by rfl) ⟨648146, by rfl⟩ : syracuseStep 864195 = 1296293) B1296293
theorem B2076625 : Blo 860564 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B864211 : Blo 860564 864211 := bstep (se 1 (by rfl) ⟨648158, by rfl⟩ : syracuseStep 864211 = 1296317) B1296317
theorem B1454051 : Blo 860564 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B864227 : Blo 860564 864227 := bstep (se 1 (by rfl) ⟨648170, by rfl⟩ : syracuseStep 864227 = 1296341) B1296341
theorem B864243 : Blo 860564 864243 := bstep (se 1 (by rfl) ⟨648182, by rfl⟩ : syracuseStep 864243 = 1296365) B1296365
theorem B864259 : Blo 860564 864259 := bstep (se 1 (by rfl) ⟨648194, by rfl⟩ : syracuseStep 864259 = 1296389) B1296389
theorem B864275 : Blo 860564 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B864291 : Blo 860564 864291 := bstep (se 1 (by rfl) ⟨648218, by rfl⟩ : syracuseStep 864291 = 1296437) B1296437
theorem B864307 : Blo 860564 864307 := bstep (se 1 (by rfl) ⟨648230, by rfl⟩ : syracuseStep 864307 = 1296461) B1296461
theorem B864323 : Blo 860564 864323 := bstep (se 1 (by rfl) ⟨648242, by rfl⟩ : syracuseStep 864323 = 1296485) B1296485
theorem B864339 : Blo 860564 864339 := bstep (se 1 (by rfl) ⟨648254, by rfl⟩ : syracuseStep 864339 = 1296509) B1296509
theorem B1454179 : Blo 860564 1454179 := bstep (se 1 (by rfl) ⟨1090634, by rfl⟩ : syracuseStep 1454179 = 2181269) B2181269
theorem B864355 : Blo 860564 864355 := bstep (se 1 (by rfl) ⟨648266, by rfl⟩ : syracuseStep 864355 = 1296533) B1296533
theorem B864371 : Blo 860564 864371 := bstep (se 1 (by rfl) ⟨648278, by rfl⟩ : syracuseStep 864371 = 1296557) B1296557
theorem B1093763 : Blo 860564 1093763 := bstep (se 1 (by rfl) ⟨820322, by rfl⟩ : syracuseStep 1093763 = 1640645) B1640645
theorem B864387 : Blo 860564 864387 := bstep (se 1 (by rfl) ⟨648290, by rfl⟩ : syracuseStep 864387 = 1296581) B1296581
theorem B864403 : Blo 860564 864403 := bstep (se 1 (by rfl) ⟨648302, by rfl⟩ : syracuseStep 864403 = 1296605) B1296605
theorem B864419 : Blo 860564 864419 := bstep (se 1 (by rfl) ⟨648314, by rfl⟩ : syracuseStep 864419 = 1296629) B1296629
theorem B864435 : Blo 860564 864435 := bstep (se 1 (by rfl) ⟨648326, by rfl⟩ : syracuseStep 864435 = 1296653) B1296653
theorem B864451 : Blo 860564 864451 := bstep (se 1 (by rfl) ⟨648338, by rfl⟩ : syracuseStep 864451 = 1296677) B1296677
theorem B864467 : Blo 860564 864467 := bstep (se 1 (by rfl) ⟨648350, by rfl⟩ : syracuseStep 864467 = 1296701) B1296701
theorem B864483 : Blo 860564 864483 := bstep (se 1 (by rfl) ⟨648362, by rfl⟩ : syracuseStep 864483 = 1296725) B1296725
theorem B6205681 : Blo 860564 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B1454321 : Blo 860564 1454321 := bstep (se 2 (by rfl) ⟨545370, by rfl⟩ : syracuseStep 1454321 = 1090741) B1090741
theorem B864499 : Blo 860564 864499 := bstep (se 1 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 864499 = 1296749) B1296749
theorem B864515 : Blo 860564 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B9842957 : Blo 860564 9842957 := bstep (se 3 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 9842957 = 3691109) B3691109
theorem B864531 : Blo 860564 864531 := bstep (se 1 (by rfl) ⟨648398, by rfl⟩ : syracuseStep 864531 = 1296797) B1296797
theorem B864547 : Blo 860564 864547 := bstep (se 1 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 864547 = 1296821) B1296821
theorem B864563 : Blo 860564 864563 := bstep (se 1 (by rfl) ⟨648422, by rfl⟩ : syracuseStep 864563 = 1296845) B1296845
theorem B1454449 : Blo 860564 1454449 := bstep (se 2 (by rfl) ⟨545418, by rfl⟩ : syracuseStep 1454449 = 1090837) B1090837
theorem B1454483 : Blo 860564 1454483 := bstep (se 1 (by rfl) ⟨1090862, by rfl⟩ : syracuseStep 1454483 = 2181725) B2181725
theorem B1454611 : Blo 860564 1454611 := bstep (se 1 (by rfl) ⟨1090958, by rfl⟩ : syracuseStep 1454611 = 2181917) B2181917
theorem B1290851 : Blo 860564 1290851 := bstep (se 1 (by rfl) ⟨968138, by rfl⟩ : syracuseStep 1290851 = 1936277) B1936277
theorem B2765411 : Blo 860564 2765411 := bstep (se 1 (by rfl) ⟨2074058, by rfl⟩ : syracuseStep 2765411 = 4148117) B4148117
theorem B1290881 : Blo 860564 1290881 := bstep (se 2 (by rfl) ⟨484080, by rfl⟩ : syracuseStep 1290881 = 968161) B968161
theorem B7385741 : Blo 860564 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B1290899 : Blo 860564 1290899 := bstep (se 1 (by rfl) ⟨968174, by rfl⟩ : syracuseStep 1290899 = 1936349) B1936349
theorem B1454753 : Blo 860564 1454753 := bstep (se 2 (by rfl) ⟨545532, by rfl⟩ : syracuseStep 1454753 = 1091065) B1091065
theorem B1290929 : Blo 860564 1290929 := bstep (se 2 (by rfl) ⟨484098, by rfl⟩ : syracuseStep 1290929 = 968197) B968197
theorem B1290947 : Blo 860564 1290947 := bstep (se 1 (by rfl) ⟨968210, by rfl⟩ : syracuseStep 1290947 = 1936421) B1936421
theorem B1290977 : Blo 860564 1290977 := bstep (se 2 (by rfl) ⟨484116, by rfl⟩ : syracuseStep 1290977 = 968233) B968233
theorem B1290995 : Blo 860564 1290995 := bstep (se 1 (by rfl) ⟨968246, by rfl⟩ : syracuseStep 1290995 = 1936493) B1936493
theorem B1291025 : Blo 860564 1291025 := bstep (se 2 (by rfl) ⟨484134, by rfl⟩ : syracuseStep 1291025 = 968269) B968269
theorem B1454881 : Blo 860564 1454881 := bstep (se 2 (by rfl) ⟨545580, by rfl⟩ : syracuseStep 1454881 = 1091161) B1091161
theorem B1291043 : Blo 860564 1291043 := bstep (se 1 (by rfl) ⟨968282, by rfl⟩ : syracuseStep 1291043 = 1936565) B1936565
theorem B1291073 : Blo 860564 1291073 := bstep (se 2 (by rfl) ⟨484152, by rfl⟩ : syracuseStep 1291073 = 968305) B968305
theorem B1454915 : Blo 860564 1454915 := bstep (se 1 (by rfl) ⟨1091186, by rfl⟩ : syracuseStep 1454915 = 2182373) B2182373
theorem B1291091 : Blo 860564 1291091 := bstep (se 1 (by rfl) ⟨968318, by rfl⟩ : syracuseStep 1291091 = 1936637) B1936637
theorem B1291121 : Blo 860564 1291121 := bstep (se 2 (by rfl) ⟨484170, by rfl⟩ : syracuseStep 1291121 = 968341) B968341
theorem B1291139 : Blo 860564 1291139 := bstep (se 1 (by rfl) ⟨968354, by rfl⟩ : syracuseStep 1291139 = 1936709) B1936709
theorem B1291169 : Blo 860564 1291169 := bstep (se 2 (by rfl) ⟨484188, by rfl⟩ : syracuseStep 1291169 = 968377) B968377
theorem B1291187 : Blo 860564 1291187 := bstep (se 1 (by rfl) ⟨968390, by rfl⟩ : syracuseStep 1291187 = 1936781) B1936781
theorem B1455043 : Blo 860564 1455043 := bstep (se 1 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 1455043 = 2182565) B2182565
theorem B1291217 : Blo 860564 1291217 := bstep (se 2 (by rfl) ⟨484206, by rfl⟩ : syracuseStep 1291217 = 968413) B968413
theorem B1291235 : Blo 860564 1291235 := bstep (se 1 (by rfl) ⟨968426, by rfl⟩ : syracuseStep 1291235 = 1936853) B1936853
theorem B10499057 : Blo 860564 10499057 := bstep (se 2 (by rfl) ⟨3937146, by rfl⟩ : syracuseStep 10499057 = 7874293) B7874293
theorem B1291265 : Blo 860564 1291265 := bstep (se 2 (by rfl) ⟨484224, by rfl⟩ : syracuseStep 1291265 = 968449) B968449
theorem B1291283 : Blo 860564 1291283 := bstep (se 1 (by rfl) ⟨968462, by rfl⟩ : syracuseStep 1291283 = 1936925) B1936925
theorem B1291313 : Blo 860564 1291313 := bstep (se 2 (by rfl) ⟨484242, by rfl⟩ : syracuseStep 1291313 = 968485) B968485
theorem B1291331 : Blo 860564 1291331 := bstep (se 1 (by rfl) ⟨968498, by rfl⟩ : syracuseStep 1291331 = 1936997) B1936997
theorem B1455185 : Blo 860564 1455185 := bstep (se 2 (by rfl) ⟨545694, by rfl⟩ : syracuseStep 1455185 = 1091389) B1091389
theorem B1291361 : Blo 860564 1291361 := bstep (se 2 (by rfl) ⟨484260, by rfl⟩ : syracuseStep 1291361 = 968521) B968521
theorem B4371569 : Blo 860564 4371569 := bstep (se 2 (by rfl) ⟨1639338, by rfl⟩ : syracuseStep 4371569 = 3278677) B3278677
theorem B1291379 : Blo 860564 1291379 := bstep (se 1 (by rfl) ⟨968534, by rfl⟩ : syracuseStep 1291379 = 1937069) B1937069
theorem B1225859 : Blo 860564 1225859 := bstep (se 1 (by rfl) ⟨919394, by rfl⟩ : syracuseStep 1225859 = 1838789) B1838789
theorem B5518469 : Blo 860564 5518469 := bstep (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) B1034713
theorem B1291409 : Blo 860564 1291409 := bstep (se 2 (by rfl) ⟨484278, by rfl⟩ : syracuseStep 1291409 = 968557) B968557
theorem B1291427 : Blo 860564 1291427 := bstep (se 1 (by rfl) ⟨968570, by rfl⟩ : syracuseStep 1291427 = 1937141) B1937141
theorem B2766001 : Blo 860564 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B1291457 : Blo 860564 1291457 := bstep (se 2 (by rfl) ⟨484296, by rfl⟩ : syracuseStep 1291457 = 968593) B968593
theorem B1455313 : Blo 860564 1455313 := bstep (se 2 (by rfl) ⟨545742, by rfl⟩ : syracuseStep 1455313 = 1091485) B1091485
theorem B1291475 : Blo 860564 1291475 := bstep (se 1 (by rfl) ⟨968606, by rfl⟩ : syracuseStep 1291475 = 1937213) B1937213
theorem B1291505 : Blo 860564 1291505 := bstep (se 2 (by rfl) ⟨484314, by rfl⟩ : syracuseStep 1291505 = 968629) B968629
theorem B1455347 : Blo 860564 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B1291523 : Blo 860564 1291523 := bstep (se 1 (by rfl) ⟨968642, by rfl⟩ : syracuseStep 1291523 = 1937285) B1937285
theorem B1291553 : Blo 860564 1291553 := bstep (se 2 (by rfl) ⟨484332, by rfl⟩ : syracuseStep 1291553 = 968665) B968665
theorem B1291571 : Blo 860564 1291571 := bstep (se 1 (by rfl) ⟨968678, by rfl⟩ : syracuseStep 1291571 = 1937357) B1937357
theorem B1291601 : Blo 860564 1291601 := bstep (se 2 (by rfl) ⟨484350, by rfl⟩ : syracuseStep 1291601 = 968701) B968701
theorem B2209123 : Blo 860564 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B1291619 : Blo 860564 1291619 := bstep (se 1 (by rfl) ⟨968714, by rfl⟩ : syracuseStep 1291619 = 1937429) B1937429
theorem B1455475 : Blo 860564 1455475 := bstep (se 1 (by rfl) ⟨1091606, by rfl⟩ : syracuseStep 1455475 = 2183213) B2183213
theorem B1291649 : Blo 860564 1291649 := bstep (se 2 (by rfl) ⟨484368, by rfl⟩ : syracuseStep 1291649 = 968737) B968737
theorem B1291667 : Blo 860564 1291667 := bstep (se 1 (by rfl) ⟨968750, by rfl⟩ : syracuseStep 1291667 = 1937501) B1937501
theorem B1291697 : Blo 860564 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B1291715 : Blo 860564 1291715 := bstep (se 1 (by rfl) ⟨968786, by rfl⟩ : syracuseStep 1291715 = 1937573) B1937573
theorem B1291745 : Blo 860564 1291745 := bstep (se 2 (by rfl) ⟨484404, by rfl⟩ : syracuseStep 1291745 = 968809) B968809
theorem B1291763 : Blo 860564 1291763 := bstep (se 1 (by rfl) ⟨968822, by rfl⟩ : syracuseStep 1291763 = 1937645) B1937645
theorem B1455617 : Blo 860564 1455617 := bstep (se 2 (by rfl) ⟨545856, by rfl⟩ : syracuseStep 1455617 = 1091713) B1091713
theorem B1291793 : Blo 860564 1291793 := bstep (se 2 (by rfl) ⟨484422, by rfl⟩ : syracuseStep 1291793 = 968845) B968845
theorem B1291811 : Blo 860564 1291811 := bstep (se 1 (by rfl) ⟨968858, by rfl⟩ : syracuseStep 1291811 = 1937717) B1937717
theorem B1291841 : Blo 860564 1291841 := bstep (se 2 (by rfl) ⟨484440, by rfl⟩ : syracuseStep 1291841 = 968881) B968881
theorem B1291859 : Blo 860564 1291859 := bstep (se 1 (by rfl) ⟨968894, by rfl⟩ : syracuseStep 1291859 = 1937789) B1937789
theorem B1291889 : Blo 860564 1291889 := bstep (se 2 (by rfl) ⟨484458, by rfl⟩ : syracuseStep 1291889 = 968917) B968917
theorem B1455745 : Blo 860564 1455745 := bstep (se 2 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 1455745 = 1091809) B1091809
theorem B1291907 : Blo 860564 1291907 := bstep (se 1 (by rfl) ⟨968930, by rfl⟩ : syracuseStep 1291907 = 1937861) B1937861
theorem B1291937 : Blo 860564 1291937 := bstep (se 2 (by rfl) ⟨484476, by rfl⟩ : syracuseStep 1291937 = 968953) B968953
theorem B1455779 : Blo 860564 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B1291955 : Blo 860564 1291955 := bstep (se 1 (by rfl) ⟨968966, by rfl⟩ : syracuseStep 1291955 = 1937933) B1937933
theorem B1291985 : Blo 860564 1291985 := bstep (se 2 (by rfl) ⟨484494, by rfl⟩ : syracuseStep 1291985 = 968989) B968989
theorem B1292003 : Blo 860564 1292003 := bstep (se 1 (by rfl) ⟨969002, by rfl⟩ : syracuseStep 1292003 = 1938005) B1938005
theorem B1292033 : Blo 860564 1292033 := bstep (se 2 (by rfl) ⟨484512, by rfl⟩ : syracuseStep 1292033 = 969025) B969025
theorem B1226497 : Blo 860564 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B8271629 : Blo 860564 8271629 := bstep (se 3 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 8271629 = 3101861) B3101861
theorem B1292051 : Blo 860564 1292051 := bstep (se 1 (by rfl) ⟨969038, by rfl⟩ : syracuseStep 1292051 = 1938077) B1938077
theorem B1455907 : Blo 860564 1455907 := bstep (se 1 (by rfl) ⟨1091930, by rfl⟩ : syracuseStep 1455907 = 2183861) B2183861
theorem B1292081 : Blo 860564 1292081 := bstep (se 2 (by rfl) ⟨484530, by rfl⟩ : syracuseStep 1292081 = 969061) B969061
theorem B1292099 : Blo 860564 1292099 := bstep (se 1 (by rfl) ⟨969074, by rfl⟩ : syracuseStep 1292099 = 1938149) B1938149
theorem B1292129 : Blo 860564 1292129 := bstep (se 2 (by rfl) ⟨484548, by rfl⟩ : syracuseStep 1292129 = 969097) B969097
theorem B1292147 : Blo 860564 1292147 := bstep (se 1 (by rfl) ⟨969110, by rfl⟩ : syracuseStep 1292147 = 1938221) B1938221
theorem B1226611 : Blo 860564 1226611 := bstep (se 1 (by rfl) ⟨919958, by rfl⟩ : syracuseStep 1226611 = 1839917) B1839917
theorem B1292177 : Blo 860564 1292177 := bstep (se 2 (by rfl) ⟨484566, by rfl⟩ : syracuseStep 1292177 = 969133) B969133
theorem B1292195 : Blo 860564 1292195 := bstep (se 1 (by rfl) ⟨969146, by rfl⟩ : syracuseStep 1292195 = 1938293) B1938293
theorem B1456049 : Blo 860564 1456049 := bstep (se 2 (by rfl) ⟨546018, by rfl⟩ : syracuseStep 1456049 = 1092037) B1092037
theorem B1292225 : Blo 860564 1292225 := bstep (se 2 (by rfl) ⟨484584, by rfl⟩ : syracuseStep 1292225 = 969169) B969169
theorem B1292243 : Blo 860564 1292243 := bstep (se 1 (by rfl) ⟨969182, by rfl⟩ : syracuseStep 1292243 = 1938365) B1938365
theorem B1292273 : Blo 860564 1292273 := bstep (se 2 (by rfl) ⟨484602, by rfl⟩ : syracuseStep 1292273 = 969205) B969205
theorem B1292291 : Blo 860564 1292291 := bstep (se 1 (by rfl) ⟨969218, by rfl⟩ : syracuseStep 1292291 = 1938437) B1938437
theorem B1292321 : Blo 860564 1292321 := bstep (se 2 (by rfl) ⟨484620, by rfl⟩ : syracuseStep 1292321 = 969241) B969241
theorem B1456177 : Blo 860564 1456177 := bstep (se 2 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 1456177 = 1092133) B1092133
theorem B1292339 : Blo 860564 1292339 := bstep (se 1 (by rfl) ⟨969254, by rfl⟩ : syracuseStep 1292339 = 1938509) B1938509
theorem B14956597 : Blo 860564 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B1292369 : Blo 860564 1292369 := bstep (se 2 (by rfl) ⟨484638, by rfl⟩ : syracuseStep 1292369 = 969277) B969277
theorem B1456211 : Blo 860564 1456211 := bstep (se 1 (by rfl) ⟨1092158, by rfl⟩ : syracuseStep 1456211 = 2184317) B2184317
theorem B1292387 : Blo 860564 1292387 := bstep (se 1 (by rfl) ⟨969290, by rfl⟩ : syracuseStep 1292387 = 1938581) B1938581
theorem B1292417 : Blo 860564 1292417 := bstep (se 2 (by rfl) ⟨484656, by rfl⟩ : syracuseStep 1292417 = 969313) B969313
theorem B1292435 : Blo 860564 1292435 := bstep (se 1 (by rfl) ⟨969326, by rfl⟩ : syracuseStep 1292435 = 1938653) B1938653
theorem B1292465 : Blo 860564 1292465 := bstep (se 2 (by rfl) ⟨484674, by rfl⟩ : syracuseStep 1292465 = 969349) B969349
theorem B1292483 : Blo 860564 1292483 := bstep (se 1 (by rfl) ⟨969362, by rfl⟩ : syracuseStep 1292483 = 1938725) B1938725
theorem B1456339 : Blo 860564 1456339 := bstep (se 1 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 1456339 = 2184509) B2184509
theorem B1292513 : Blo 860564 1292513 := bstep (se 2 (by rfl) ⟨484692, by rfl⟩ : syracuseStep 1292513 = 969385) B969385
theorem B5257457 : Blo 860564 5257457 := bstep (se 2 (by rfl) ⟨1971546, by rfl⟩ : syracuseStep 5257457 = 3943093) B3943093
theorem B1292531 : Blo 860564 1292531 := bstep (se 1 (by rfl) ⟨969398, by rfl⟩ : syracuseStep 1292531 = 1938797) B1938797
theorem B1292561 : Blo 860564 1292561 := bstep (se 2 (by rfl) ⟨484710, by rfl⟩ : syracuseStep 1292561 = 969421) B969421
theorem B1292579 : Blo 860564 1292579 := bstep (se 1 (by rfl) ⟨969434, by rfl⟩ : syracuseStep 1292579 = 1938869) B1938869
theorem B1292609 : Blo 860564 1292609 := bstep (se 2 (by rfl) ⟨484728, by rfl⟩ : syracuseStep 1292609 = 969457) B969457
theorem B3684685 : Blo 860564 3684685 := bstep (se 3 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 3684685 = 1381757) B1381757
theorem B1292627 : Blo 860564 1292627 := bstep (se 1 (by rfl) ⟨969470, by rfl⟩ : syracuseStep 1292627 = 1938941) B1938941
theorem B1456481 : Blo 860564 1456481 := bstep (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) B1092361
theorem B1292657 : Blo 860564 1292657 := bstep (se 2 (by rfl) ⟨484746, by rfl⟩ : syracuseStep 1292657 = 969493) B969493
theorem B1292675 : Blo 860564 1292675 := bstep (se 1 (by rfl) ⟨969506, by rfl⟩ : syracuseStep 1292675 = 1939013) B1939013
theorem B1292705 : Blo 860564 1292705 := bstep (se 2 (by rfl) ⟨484764, by rfl⟩ : syracuseStep 1292705 = 969529) B969529
theorem B1292723 : Blo 860564 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B1292753 : Blo 860564 1292753 := bstep (se 2 (by rfl) ⟨484782, by rfl⟩ : syracuseStep 1292753 = 969565) B969565
theorem B1456609 : Blo 860564 1456609 := bstep (se 2 (by rfl) ⟨546228, by rfl⟩ : syracuseStep 1456609 = 1092457) B1092457
theorem B1292771 : Blo 860564 1292771 := bstep (se 1 (by rfl) ⟨969578, by rfl⟩ : syracuseStep 1292771 = 1939157) B1939157
theorem B1292801 : Blo 860564 1292801 := bstep (se 2 (by rfl) ⟨484800, by rfl⟩ : syracuseStep 1292801 = 969601) B969601
theorem B1456643 : Blo 860564 1456643 := bstep (se 1 (by rfl) ⟨1092482, by rfl⟩ : syracuseStep 1456643 = 2184965) B2184965
theorem B1292819 : Blo 860564 1292819 := bstep (se 1 (by rfl) ⟨969614, by rfl⟩ : syracuseStep 1292819 = 1939229) B1939229
theorem B4373027 : Blo 860564 4373027 := bstep (se 1 (by rfl) ⟨3279770, by rfl⟩ : syracuseStep 4373027 = 6559541) B6559541
theorem B1292849 : Blo 860564 1292849 := bstep (se 2 (by rfl) ⟨484818, by rfl⟩ : syracuseStep 1292849 = 969637) B969637
theorem B1292867 : Blo 860564 1292867 := bstep (se 1 (by rfl) ⟨969650, by rfl⟩ : syracuseStep 1292867 = 1939301) B1939301
theorem B1292897 : Blo 860564 1292897 := bstep (se 2 (by rfl) ⟨484836, by rfl⟩ : syracuseStep 1292897 = 969673) B969673
theorem B1292915 : Blo 860564 1292915 := bstep (se 1 (by rfl) ⟨969686, by rfl⟩ : syracuseStep 1292915 = 1939373) B1939373
theorem B1456771 : Blo 860564 1456771 := bstep (se 1 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 1456771 = 2185157) B2185157
theorem B1292945 : Blo 860564 1292945 := bstep (se 2 (by rfl) ⟨484854, by rfl⟩ : syracuseStep 1292945 = 969709) B969709
theorem B1292963 : Blo 860564 1292963 := bstep (se 1 (by rfl) ⟨969722, by rfl⟩ : syracuseStep 1292963 = 1939445) B1939445
theorem B3685027 : Blo 860564 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1292993 : Blo 860564 1292993 := bstep (se 2 (by rfl) ⟨484872, by rfl⟩ : syracuseStep 1292993 = 969745) B969745
theorem B4668101 : Blo 860564 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B1293011 : Blo 860564 1293011 := bstep (se 1 (by rfl) ⟨969758, by rfl⟩ : syracuseStep 1293011 = 1939517) B1939517
theorem B1293041 : Blo 860564 1293041 := bstep (se 2 (by rfl) ⟨484890, by rfl⟩ : syracuseStep 1293041 = 969781) B969781
theorem B1293059 : Blo 860564 1293059 := bstep (se 1 (by rfl) ⟨969794, by rfl⟩ : syracuseStep 1293059 = 1939589) B1939589
theorem B1456913 : Blo 860564 1456913 := bstep (se 2 (by rfl) ⟨546342, by rfl⟩ : syracuseStep 1456913 = 1092685) B1092685
theorem B1293089 : Blo 860564 1293089 := bstep (se 2 (by rfl) ⟨484908, by rfl⟩ : syracuseStep 1293089 = 969817) B969817
theorem B1293107 : Blo 860564 1293107 := bstep (se 1 (by rfl) ⟨969830, by rfl⟩ : syracuseStep 1293107 = 1939661) B1939661
theorem B1293137 : Blo 860564 1293137 := bstep (se 2 (by rfl) ⟨484926, by rfl⟩ : syracuseStep 1293137 = 969853) B969853
theorem B1293155 : Blo 860564 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B1293185 : Blo 860564 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B1457041 : Blo 860564 1457041 := bstep (se 2 (by rfl) ⟨546390, by rfl⟩ : syracuseStep 1457041 = 1092781) B1092781
theorem B1293203 : Blo 860564 1293203 := bstep (se 1 (by rfl) ⟨969902, by rfl⟩ : syracuseStep 1293203 = 1939805) B1939805
theorem B1293233 : Blo 860564 1293233 := bstep (se 2 (by rfl) ⟨484962, by rfl⟩ : syracuseStep 1293233 = 969925) B969925
theorem B1457075 : Blo 860564 1457075 := bstep (se 1 (by rfl) ⟨1092806, by rfl⟩ : syracuseStep 1457075 = 2185613) B2185613
theorem B1293251 : Blo 860564 1293251 := bstep (se 1 (by rfl) ⟨969938, by rfl⟩ : syracuseStep 1293251 = 1939877) B1939877
theorem B1293281 : Blo 860564 1293281 := bstep (se 2 (by rfl) ⟨484980, by rfl⟩ : syracuseStep 1293281 = 969961) B969961
theorem B1293299 : Blo 860564 1293299 := bstep (se 1 (by rfl) ⟨969974, by rfl⟩ : syracuseStep 1293299 = 1939949) B1939949
theorem B1293329 : Blo 860564 1293329 := bstep (se 2 (by rfl) ⟨484998, by rfl⟩ : syracuseStep 1293329 = 969997) B969997
theorem B1293347 : Blo 860564 1293347 := bstep (se 1 (by rfl) ⟨970010, by rfl⟩ : syracuseStep 1293347 = 1940021) B1940021
theorem B1457203 : Blo 860564 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B1293377 : Blo 860564 1293377 := bstep (se 2 (by rfl) ⟨485016, by rfl⟩ : syracuseStep 1293377 = 970033) B970033
theorem B1293395 : Blo 860564 1293395 := bstep (se 1 (by rfl) ⟨970046, by rfl⟩ : syracuseStep 1293395 = 1940093) B1940093
theorem B1293425 : Blo 860564 1293425 := bstep (se 2 (by rfl) ⟨485034, by rfl⟩ : syracuseStep 1293425 = 970069) B970069
theorem B9845873 : Blo 860564 9845873 := bstep (se 2 (by rfl) ⟨3692202, by rfl⟩ : syracuseStep 9845873 = 7384405) B7384405
theorem B1293443 : Blo 860564 1293443 := bstep (se 1 (by rfl) ⟨970082, by rfl⟩ : syracuseStep 1293443 = 1940165) B1940165
theorem B1293473 : Blo 860564 1293473 := bstep (se 2 (by rfl) ⟨485052, by rfl⟩ : syracuseStep 1293473 = 970105) B970105
theorem B1293491 : Blo 860564 1293491 := bstep (se 1 (by rfl) ⟨970118, by rfl⟩ : syracuseStep 1293491 = 1940237) B1940237
theorem B1227955 : Blo 860564 1227955 := bstep (se 1 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 1227955 = 1841933) B1841933
theorem B1457345 : Blo 860564 1457345 := bstep (se 2 (by rfl) ⟨546504, by rfl⟩ : syracuseStep 1457345 = 1093009) B1093009
theorem B1293521 : Blo 860564 1293521 := bstep (se 2 (by rfl) ⟨485070, by rfl⟩ : syracuseStep 1293521 = 970141) B970141
theorem B1293539 : Blo 860564 1293539 := bstep (se 1 (by rfl) ⟨970154, by rfl⟩ : syracuseStep 1293539 = 1940309) B1940309
theorem B1293569 : Blo 860564 1293569 := bstep (se 2 (by rfl) ⟨485088, by rfl⟩ : syracuseStep 1293569 = 970177) B970177
theorem B1293587 : Blo 860564 1293587 := bstep (se 1 (by rfl) ⟨970190, by rfl⟩ : syracuseStep 1293587 = 1940381) B1940381
theorem B2178353 : Blo 860564 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B1293617 : Blo 860564 1293617 := bstep (se 2 (by rfl) ⟨485106, by rfl⟩ : syracuseStep 1293617 = 970213) B970213
theorem B1457473 : Blo 860564 1457473 := bstep (se 2 (by rfl) ⟨546552, by rfl⟩ : syracuseStep 1457473 = 1093105) B1093105
theorem B1293635 : Blo 860564 1293635 := bstep (se 1 (by rfl) ⟨970226, by rfl⟩ : syracuseStep 1293635 = 1940453) B1940453
theorem B4373837 : Blo 860564 4373837 := bstep (se 3 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 4373837 = 1640189) B1640189
theorem B1293665 : Blo 860564 1293665 := bstep (se 2 (by rfl) ⟨485124, by rfl⟩ : syracuseStep 1293665 = 970249) B970249
theorem B1457507 : Blo 860564 1457507 := bstep (se 1 (by rfl) ⟨1093130, by rfl⟩ : syracuseStep 1457507 = 2186261) B2186261
theorem B1293683 : Blo 860564 1293683 := bstep (se 1 (by rfl) ⟨970262, by rfl⟩ : syracuseStep 1293683 = 1940525) B1940525
theorem B1293713 : Blo 860564 1293713 := bstep (se 2 (by rfl) ⟨485142, by rfl⟩ : syracuseStep 1293713 = 970285) B970285
theorem B1293731 : Blo 860564 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B1293761 : Blo 860564 1293761 := bstep (se 2 (by rfl) ⟨485160, by rfl⟩ : syracuseStep 1293761 = 970321) B970321
theorem B1293779 : Blo 860564 1293779 := bstep (se 1 (by rfl) ⟨970334, by rfl⟩ : syracuseStep 1293779 = 1940669) B1940669
theorem B1457635 : Blo 860564 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B1293809 : Blo 860564 1293809 := bstep (se 2 (by rfl) ⟨485178, by rfl⟩ : syracuseStep 1293809 = 970357) B970357
theorem B1293827 : Blo 860564 1293827 := bstep (se 1 (by rfl) ⟨970370, by rfl⟩ : syracuseStep 1293827 = 1940741) B1940741
theorem B1293857 : Blo 860564 1293857 := bstep (se 2 (by rfl) ⟨485196, by rfl⟩ : syracuseStep 1293857 = 970393) B970393
theorem B1293875 : Blo 860564 1293875 := bstep (se 1 (by rfl) ⟨970406, by rfl⟩ : syracuseStep 1293875 = 1940813) B1940813
theorem B1293905 : Blo 860564 1293905 := bstep (se 2 (by rfl) ⟨485214, by rfl⟩ : syracuseStep 1293905 = 970429) B970429
theorem B1293923 : Blo 860564 1293923 := bstep (se 1 (by rfl) ⟨970442, by rfl⟩ : syracuseStep 1293923 = 1940885) B1940885
theorem B1457777 : Blo 860564 1457777 := bstep (se 2 (by rfl) ⟨546666, by rfl⟩ : syracuseStep 1457777 = 1093333) B1093333
theorem B1293953 : Blo 860564 1293953 := bstep (se 2 (by rfl) ⟨485232, by rfl⟩ : syracuseStep 1293953 = 970465) B970465
theorem B1293971 : Blo 860564 1293971 := bstep (se 1 (by rfl) ⟨970478, by rfl⟩ : syracuseStep 1293971 = 1940957) B1940957
theorem B1294001 : Blo 860564 1294001 := bstep (se 2 (by rfl) ⟨485250, by rfl⟩ : syracuseStep 1294001 = 970501) B970501
theorem B1294019 : Blo 860564 1294019 := bstep (se 1 (by rfl) ⟨970514, by rfl⟩ : syracuseStep 1294019 = 1941029) B1941029
theorem B1294049 : Blo 860564 1294049 := bstep (se 2 (by rfl) ⟨485268, by rfl⟩ : syracuseStep 1294049 = 970537) B970537
theorem B11058929 : Blo 860564 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B1457905 : Blo 860564 1457905 := bstep (se 2 (by rfl) ⟨546714, by rfl⟩ : syracuseStep 1457905 = 1093429) B1093429
theorem B1294067 : Blo 860564 1294067 := bstep (se 1 (by rfl) ⟨970550, by rfl⟩ : syracuseStep 1294067 = 1941101) B1941101
theorem B1294097 : Blo 860564 1294097 := bstep (se 2 (by rfl) ⟨485286, by rfl⟩ : syracuseStep 1294097 = 970573) B970573
theorem B1457939 : Blo 860564 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B1294115 : Blo 860564 1294115 := bstep (se 1 (by rfl) ⟨970586, by rfl⟩ : syracuseStep 1294115 = 1941173) B1941173
theorem B1294145 : Blo 860564 1294145 := bstep (se 2 (by rfl) ⟨485304, by rfl⟩ : syracuseStep 1294145 = 970609) B970609
theorem B2244419 : Blo 860564 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B1294163 : Blo 860564 1294163 := bstep (se 1 (by rfl) ⟨970622, by rfl⟩ : syracuseStep 1294163 = 1941245) B1941245
theorem B1294193 : Blo 860564 1294193 := bstep (se 2 (by rfl) ⟨485322, by rfl⟩ : syracuseStep 1294193 = 970645) B970645
theorem B1294211 : Blo 860564 1294211 := bstep (se 1 (by rfl) ⟨970658, by rfl⟩ : syracuseStep 1294211 = 1941317) B1941317
theorem B1458067 : Blo 860564 1458067 := bstep (se 1 (by rfl) ⟨1093550, by rfl⟩ : syracuseStep 1458067 = 2187101) B2187101
theorem B1294241 : Blo 860564 1294241 := bstep (se 2 (by rfl) ⟨485340, by rfl⟩ : syracuseStep 1294241 = 970681) B970681
theorem B1294259 : Blo 860564 1294259 := bstep (se 1 (by rfl) ⟨970694, by rfl⟩ : syracuseStep 1294259 = 1941389) B1941389
theorem B2768845 : Blo 860564 2768845 := bstep (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) B1038317
theorem B1294289 : Blo 860564 1294289 := bstep (se 2 (by rfl) ⟨485358, by rfl⟩ : syracuseStep 1294289 = 970717) B970717
theorem B1294307 : Blo 860564 1294307 := bstep (se 1 (by rfl) ⟨970730, by rfl⟩ : syracuseStep 1294307 = 1941461) B1941461
theorem B1294337 : Blo 860564 1294337 := bstep (se 2 (by rfl) ⟨485376, by rfl⟩ : syracuseStep 1294337 = 970753) B970753
theorem B1294355 : Blo 860564 1294355 := bstep (se 1 (by rfl) ⟨970766, by rfl⟩ : syracuseStep 1294355 = 1941533) B1941533
theorem B1458209 : Blo 860564 1458209 := bstep (se 2 (by rfl) ⟨546828, by rfl⟩ : syracuseStep 1458209 = 1093657) B1093657
theorem B1294385 : Blo 860564 1294385 := bstep (se 2 (by rfl) ⟨485394, by rfl⟩ : syracuseStep 1294385 = 970789) B970789
theorem B1294403 : Blo 860564 1294403 := bstep (se 1 (by rfl) ⟨970802, by rfl⟩ : syracuseStep 1294403 = 1941605) B1941605
theorem B1294433 : Blo 860564 1294433 := bstep (se 2 (by rfl) ⟨485412, by rfl⟩ : syracuseStep 1294433 = 970825) B970825
theorem B1294451 : Blo 860564 1294451 := bstep (se 1 (by rfl) ⟨970838, by rfl⟩ : syracuseStep 1294451 = 1941677) B1941677
theorem B1294481 : Blo 860564 1294481 := bstep (se 2 (by rfl) ⟨485430, by rfl⟩ : syracuseStep 1294481 = 970861) B970861
theorem B1458337 : Blo 860564 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B1294499 : Blo 860564 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B1294529 : Blo 860564 1294529 := bstep (se 2 (by rfl) ⟨485448, by rfl⟩ : syracuseStep 1294529 = 970897) B970897
theorem B1458371 : Blo 860564 1458371 := bstep (se 1 (by rfl) ⟨1093778, by rfl⟩ : syracuseStep 1458371 = 2187557) B2187557
theorem B1294547 : Blo 860564 1294547 := bstep (se 1 (by rfl) ⟨970910, by rfl⟩ : syracuseStep 1294547 = 1941821) B1941821
theorem B1294577 : Blo 860564 1294577 := bstep (se 2 (by rfl) ⟨485466, by rfl⟩ : syracuseStep 1294577 = 970933) B970933
theorem B1294595 : Blo 860564 1294595 := bstep (se 1 (by rfl) ⟨970946, by rfl⟩ : syracuseStep 1294595 = 1941893) B1941893
theorem B2179345 : Blo 860564 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B1294625 : Blo 860564 1294625 := bstep (se 2 (by rfl) ⟨485484, by rfl⟩ : syracuseStep 1294625 = 970969) B970969
theorem B1229089 : Blo 860564 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B1294643 : Blo 860564 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B1458499 : Blo 860564 1458499 := bstep (se 1 (by rfl) ⟨1093874, by rfl⟩ : syracuseStep 1458499 = 2187749) B2187749
theorem B1294673 : Blo 860564 1294673 := bstep (se 2 (by rfl) ⟨485502, by rfl⟩ : syracuseStep 1294673 = 971005) B971005
theorem B1294691 : Blo 860564 1294691 := bstep (se 1 (by rfl) ⟨971018, by rfl⟩ : syracuseStep 1294691 = 1942037) B1942037
theorem B1294721 : Blo 860564 1294721 := bstep (se 2 (by rfl) ⟨485520, by rfl⟩ : syracuseStep 1294721 = 971041) B971041
theorem B1229185 : Blo 860564 1229185 := bstep (se 2 (by rfl) ⟨460944, by rfl⟩ : syracuseStep 1229185 = 921889) B921889
theorem B1294739 : Blo 860564 1294739 := bstep (se 1 (by rfl) ⟨971054, by rfl⟩ : syracuseStep 1294739 = 1942109) B1942109
theorem B1294769 : Blo 860564 1294769 := bstep (se 2 (by rfl) ⟨485538, by rfl⟩ : syracuseStep 1294769 = 971077) B971077
theorem B1294787 : Blo 860564 1294787 := bstep (se 1 (by rfl) ⟨971090, by rfl⟩ : syracuseStep 1294787 = 1942181) B1942181
theorem B1458641 : Blo 860564 1458641 := bstep (se 2 (by rfl) ⟨546990, by rfl⟩ : syracuseStep 1458641 = 1093981) B1093981
theorem B1294817 : Blo 860564 1294817 := bstep (se 2 (by rfl) ⟨485556, by rfl⟩ : syracuseStep 1294817 = 971113) B971113
theorem B1294835 : Blo 860564 1294835 := bstep (se 1 (by rfl) ⟨971126, by rfl⟩ : syracuseStep 1294835 = 1942253) B1942253
theorem B1294865 : Blo 860564 1294865 := bstep (se 2 (by rfl) ⟨485574, by rfl⟩ : syracuseStep 1294865 = 971149) B971149
theorem B2179619 : Blo 860564 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B1294883 : Blo 860564 1294883 := bstep (se 1 (by rfl) ⟨971162, by rfl⟩ : syracuseStep 1294883 = 1942325) B1942325
theorem B1294913 : Blo 860564 1294913 := bstep (se 2 (by rfl) ⟨485592, by rfl⟩ : syracuseStep 1294913 = 971185) B971185
theorem B1458769 : Blo 860564 1458769 := bstep (se 2 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 1458769 = 1094077) B1094077
theorem B1294931 : Blo 860564 1294931 := bstep (se 1 (by rfl) ⟨971198, by rfl⟩ : syracuseStep 1294931 = 1942397) B1942397
theorem B1294961 : Blo 860564 1294961 := bstep (se 2 (by rfl) ⟨485610, by rfl⟩ : syracuseStep 1294961 = 971221) B971221
theorem B1458803 : Blo 860564 1458803 := bstep (se 1 (by rfl) ⟨1094102, by rfl⟩ : syracuseStep 1458803 = 2188205) B2188205
theorem B1294979 : Blo 860564 1294979 := bstep (se 1 (by rfl) ⟨971234, by rfl⟩ : syracuseStep 1294979 = 1942469) B1942469
theorem B1295009 : Blo 860564 1295009 := bstep (se 2 (by rfl) ⟨485628, by rfl⟩ : syracuseStep 1295009 = 971257) B971257
theorem B1295027 : Blo 860564 1295027 := bstep (se 1 (by rfl) ⟨971270, by rfl⟩ : syracuseStep 1295027 = 1942541) B1942541
theorem B1295057 : Blo 860564 1295057 := bstep (se 2 (by rfl) ⟨485646, by rfl⟩ : syracuseStep 1295057 = 971293) B971293
theorem B2179811 : Blo 860564 2179811 := bstep (se 1 (by rfl) ⟨1634858, by rfl⟩ : syracuseStep 2179811 = 3269717) B3269717
theorem B1295075 : Blo 860564 1295075 := bstep (se 1 (by rfl) ⟨971306, by rfl⟩ : syracuseStep 1295075 = 1942613) B1942613
theorem B1458931 : Blo 860564 1458931 := bstep (se 1 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 1458931 = 2188397) B2188397
theorem B1295105 : Blo 860564 1295105 := bstep (se 2 (by rfl) ⟨485664, by rfl⟩ : syracuseStep 1295105 = 971329) B971329
theorem B1295123 : Blo 860564 1295123 := bstep (se 1 (by rfl) ⟨971342, by rfl⟩ : syracuseStep 1295123 = 1942685) B1942685
theorem B1327907 : Blo 860564 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B1295153 : Blo 860564 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B1295171 : Blo 860564 1295171 := bstep (se 1 (by rfl) ⟨971378, by rfl⟩ : syracuseStep 1295171 = 1942757) B1942757
theorem B1295201 : Blo 860564 1295201 := bstep (se 2 (by rfl) ⟨485700, by rfl⟩ : syracuseStep 1295201 = 971401) B971401
theorem B9323363 : Blo 860564 9323363 := bstep (se 1 (by rfl) ⟨6992522, by rfl⟩ : syracuseStep 9323363 = 13985045) B13985045
theorem B1229681 : Blo 860564 1229681 := bstep (se 2 (by rfl) ⟨461130, by rfl⟩ : syracuseStep 1229681 = 922261) B922261
theorem B1295219 : Blo 860564 1295219 := bstep (se 1 (by rfl) ⟨971414, by rfl⟩ : syracuseStep 1295219 = 1942829) B1942829
theorem B1295249 : Blo 860564 1295249 := bstep (se 2 (by rfl) ⟨485718, by rfl⟩ : syracuseStep 1295249 = 971437) B971437
theorem B1295267 : Blo 860564 1295267 := bstep (se 1 (by rfl) ⟨971450, by rfl⟩ : syracuseStep 1295267 = 1942901) B1942901
theorem B1295297 : Blo 860564 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B1295315 : Blo 860564 1295315 := bstep (se 1 (by rfl) ⟨971486, by rfl⟩ : syracuseStep 1295315 = 1942973) B1942973
theorem B5522417 : Blo 860564 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B1295345 : Blo 860564 1295345 := bstep (se 2 (by rfl) ⟨485754, by rfl⟩ : syracuseStep 1295345 = 971509) B971509
theorem B1295363 : Blo 860564 1295363 := bstep (se 1 (by rfl) ⟨971522, by rfl⟩ : syracuseStep 1295363 = 1943045) B1943045
theorem B2802701 : Blo 860564 2802701 := bstep (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) B1051013
theorem B1295393 : Blo 860564 1295393 := bstep (se 2 (by rfl) ⟨485772, by rfl⟩ : syracuseStep 1295393 = 971545) B971545
theorem B1295411 : Blo 860564 1295411 := bstep (se 1 (by rfl) ⟨971558, by rfl⟩ : syracuseStep 1295411 = 1943117) B1943117
theorem B1295441 : Blo 860564 1295441 := bstep (se 2 (by rfl) ⟨485790, by rfl⟩ : syracuseStep 1295441 = 971581) B971581
theorem B1262675 : Blo 860564 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B1295459 : Blo 860564 1295459 := bstep (se 1 (by rfl) ⟨971594, by rfl⟩ : syracuseStep 1295459 = 1943189) B1943189
theorem B2245745 : Blo 860564 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B1295489 : Blo 860564 1295489 := bstep (se 2 (by rfl) ⟨485808, by rfl⟩ : syracuseStep 1295489 = 971617) B971617
theorem B1492115 : Blo 860564 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1295507 : Blo 860564 1295507 := bstep (se 1 (by rfl) ⟨971630, by rfl⟩ : syracuseStep 1295507 = 1943261) B1943261
theorem B1295537 : Blo 860564 1295537 := bstep (se 2 (by rfl) ⟨485826, by rfl⟩ : syracuseStep 1295537 = 971653) B971653
theorem B1295555 : Blo 860564 1295555 := bstep (se 1 (by rfl) ⟨971666, by rfl⟩ : syracuseStep 1295555 = 1943333) B1943333
theorem B1295585 : Blo 860564 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B9323747 : Blo 860564 9323747 := bstep (se 1 (by rfl) ⟨6992810, by rfl⟩ : syracuseStep 9323747 = 13985621) B13985621
theorem B1295603 : Blo 860564 1295603 := bstep (se 1 (by rfl) ⟨971702, by rfl⟩ : syracuseStep 1295603 = 1943405) B1943405
theorem B1295633 : Blo 860564 1295633 := bstep (se 2 (by rfl) ⟨485862, by rfl⟩ : syracuseStep 1295633 = 971725) B971725
theorem B1295651 : Blo 860564 1295651 := bstep (se 1 (by rfl) ⟨971738, by rfl⟩ : syracuseStep 1295651 = 1943477) B1943477
theorem B1295681 : Blo 860564 1295681 := bstep (se 2 (by rfl) ⟨485880, by rfl⟩ : syracuseStep 1295681 = 971761) B971761
theorem B1295699 : Blo 860564 1295699 := bstep (se 1 (by rfl) ⟨971774, by rfl⟩ : syracuseStep 1295699 = 1943549) B1943549
theorem B1295729 : Blo 860564 1295729 := bstep (se 2 (by rfl) ⟨485898, by rfl⟩ : syracuseStep 1295729 = 971797) B971797
theorem B1295747 : Blo 860564 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B1295777 : Blo 860564 1295777 := bstep (se 2 (by rfl) ⟨485916, by rfl⟩ : syracuseStep 1295777 = 971833) B971833
theorem B1295795 : Blo 860564 1295795 := bstep (se 1 (by rfl) ⟨971846, by rfl⟩ : syracuseStep 1295795 = 1943693) B1943693
theorem B1295825 : Blo 860564 1295825 := bstep (se 2 (by rfl) ⟨485934, by rfl⟩ : syracuseStep 1295825 = 971869) B971869
theorem B1295843 : Blo 860564 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B968179 : Blo 860564 968179 := bstep (se 1 (by rfl) ⟨726134, by rfl⟩ : syracuseStep 968179 = 1452269) B1452269
theorem B1295873 : Blo 860564 1295873 := bstep (se 2 (by rfl) ⟨485952, by rfl⟩ : syracuseStep 1295873 = 971905) B971905
theorem B1295891 : Blo 860564 1295891 := bstep (se 1 (by rfl) ⟨971918, by rfl⟩ : syracuseStep 1295891 = 1943837) B1943837
theorem B1295921 : Blo 860564 1295921 := bstep (se 2 (by rfl) ⟨485970, by rfl⟩ : syracuseStep 1295921 = 971941) B971941
theorem B1295939 : Blo 860564 1295939 := bstep (se 1 (by rfl) ⟨971954, by rfl⟩ : syracuseStep 1295939 = 1943909) B1943909
theorem B1295969 : Blo 860564 1295969 := bstep (se 2 (by rfl) ⟨485988, by rfl⟩ : syracuseStep 1295969 = 971977) B971977
theorem B1295987 : Blo 860564 1295987 := bstep (se 1 (by rfl) ⟨971990, by rfl⟩ : syracuseStep 1295987 = 1943981) B1943981
theorem B968323 : Blo 860564 968323 := bstep (se 1 (by rfl) ⟨726242, by rfl⟩ : syracuseStep 968323 = 1452485) B1452485
theorem B2180753 : Blo 860564 2180753 := bstep (se 2 (by rfl) ⟨817782, by rfl⟩ : syracuseStep 2180753 = 1635565) B1635565
theorem B1296017 : Blo 860564 1296017 := bstep (se 2 (by rfl) ⟨486006, by rfl⟩ : syracuseStep 1296017 = 972013) B972013
theorem B1296035 : Blo 860564 1296035 := bstep (se 1 (by rfl) ⟨972026, by rfl⟩ : syracuseStep 1296035 = 1944053) B1944053
theorem B1296065 : Blo 860564 1296065 := bstep (se 2 (by rfl) ⟨486024, by rfl⟩ : syracuseStep 1296065 = 972049) B972049
theorem B2180803 : Blo 860564 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B1296083 : Blo 860564 1296083 := bstep (se 1 (by rfl) ⟨972062, by rfl⟩ : syracuseStep 1296083 = 1944125) B1944125
theorem B1230547 : Blo 860564 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B1296113 : Blo 860564 1296113 := bstep (se 2 (by rfl) ⟨486042, by rfl⟩ : syracuseStep 1296113 = 972085) B972085
theorem B1296131 : Blo 860564 1296131 := bstep (se 1 (by rfl) ⟨972098, by rfl⟩ : syracuseStep 1296131 = 1944197) B1944197
theorem B968467 : Blo 860564 968467 := bstep (se 1 (by rfl) ⟨726350, by rfl⟩ : syracuseStep 968467 = 1452701) B1452701
theorem B1296161 : Blo 860564 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B1296179 : Blo 860564 1296179 := bstep (se 1 (by rfl) ⟨972134, by rfl⟩ : syracuseStep 1296179 = 1944269) B1944269
theorem B1230643 : Blo 860564 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B2180945 : Blo 860564 2180945 := bstep (se 2 (by rfl) ⟨817854, by rfl⟩ : syracuseStep 2180945 = 1635709) B1635709
theorem B1296209 : Blo 860564 1296209 := bstep (se 2 (by rfl) ⟨486078, by rfl⟩ : syracuseStep 1296209 = 972157) B972157
theorem B1296227 : Blo 860564 1296227 := bstep (se 1 (by rfl) ⟨972170, by rfl⟩ : syracuseStep 1296227 = 1944341) B1944341
theorem B1296257 : Blo 860564 1296257 := bstep (se 2 (by rfl) ⟨486096, by rfl⟩ : syracuseStep 1296257 = 972193) B972193
theorem B1296275 : Blo 860564 1296275 := bstep (se 1 (by rfl) ⟨972206, by rfl⟩ : syracuseStep 1296275 = 1944413) B1944413
theorem B968611 : Blo 860564 968611 := bstep (se 1 (by rfl) ⟨726458, by rfl⟩ : syracuseStep 968611 = 1452917) B1452917
theorem B1296305 : Blo 860564 1296305 := bstep (se 2 (by rfl) ⟨486114, by rfl⟩ : syracuseStep 1296305 = 972229) B972229
theorem B1296323 : Blo 860564 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B1296353 : Blo 860564 1296353 := bstep (se 2 (by rfl) ⟨486132, by rfl⟩ : syracuseStep 1296353 = 972265) B972265
theorem B7358435 : Blo 860564 7358435 := bstep (se 1 (by rfl) ⟨5518826, by rfl⟩ : syracuseStep 7358435 = 11037653) B11037653
theorem B1296371 : Blo 860564 1296371 := bstep (se 1 (by rfl) ⟨972278, by rfl⟩ : syracuseStep 1296371 = 1944557) B1944557
theorem B1296401 : Blo 860564 1296401 := bstep (se 2 (by rfl) ⟨486150, by rfl⟩ : syracuseStep 1296401 = 972301) B972301
theorem B1296419 : Blo 860564 1296419 := bstep (se 1 (by rfl) ⟨972314, by rfl⟩ : syracuseStep 1296419 = 1944629) B1944629
theorem B968755 : Blo 860564 968755 := bstep (se 1 (by rfl) ⟨726566, by rfl⟩ : syracuseStep 968755 = 1453133) B1453133
theorem B1296449 : Blo 860564 1296449 := bstep (se 2 (by rfl) ⟨486168, by rfl⟩ : syracuseStep 1296449 = 972337) B972337
theorem B1296467 : Blo 860564 1296467 := bstep (se 1 (by rfl) ⟨972350, by rfl⟩ : syracuseStep 1296467 = 1944701) B1944701
theorem B53889137 : Blo 860564 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B1296497 : Blo 860564 1296497 := bstep (se 2 (by rfl) ⟨486186, by rfl⟩ : syracuseStep 1296497 = 972373) B972373
theorem B1296515 : Blo 860564 1296515 := bstep (se 1 (by rfl) ⟨972386, by rfl⟩ : syracuseStep 1296515 = 1944773) B1944773
theorem B1296545 : Blo 860564 1296545 := bstep (se 2 (by rfl) ⟨486204, by rfl⟩ : syracuseStep 1296545 = 972409) B972409
theorem B4376753 : Blo 860564 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B1296563 : Blo 860564 1296563 := bstep (se 1 (by rfl) ⟨972422, by rfl⟩ : syracuseStep 1296563 = 1944845) B1944845
theorem B968899 : Blo 860564 968899 := bstep (se 1 (by rfl) ⟨726674, by rfl⟩ : syracuseStep 968899 = 1453349) B1453349
theorem B1296593 : Blo 860564 1296593 := bstep (se 2 (by rfl) ⟨486222, by rfl⟩ : syracuseStep 1296593 = 972445) B972445
theorem B1165523 : Blo 860564 1165523 := bstep (se 1 (by rfl) ⟨874142, by rfl⟩ : syracuseStep 1165523 = 1748285) B1748285
theorem B1296611 : Blo 860564 1296611 := bstep (se 1 (by rfl) ⟨972458, by rfl⟩ : syracuseStep 1296611 = 1944917) B1944917
theorem B1296641 : Blo 860564 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B1296659 : Blo 860564 1296659 := bstep (se 1 (by rfl) ⟨972494, by rfl⟩ : syracuseStep 1296659 = 1944989) B1944989
theorem B1296689 : Blo 860564 1296689 := bstep (se 2 (by rfl) ⟨486258, by rfl⟩ : syracuseStep 1296689 = 972517) B972517
theorem B1296707 : Blo 860564 1296707 := bstep (se 1 (by rfl) ⟨972530, by rfl⟩ : syracuseStep 1296707 = 1945061) B1945061
theorem B969043 : Blo 860564 969043 := bstep (se 1 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 969043 = 1453565) B1453565
theorem B1296737 : Blo 860564 1296737 := bstep (se 2 (by rfl) ⟨486276, by rfl⟩ : syracuseStep 1296737 = 972553) B972553
theorem B1296755 : Blo 860564 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B1296785 : Blo 860564 1296785 := bstep (se 2 (by rfl) ⟨486294, by rfl⟩ : syracuseStep 1296785 = 972589) B972589
theorem B1296803 : Blo 860564 1296803 := bstep (se 1 (by rfl) ⟨972602, by rfl⟩ : syracuseStep 1296803 = 1945205) B1945205
theorem B1296833 : Blo 860564 1296833 := bstep (se 2 (by rfl) ⟨486312, by rfl⟩ : syracuseStep 1296833 = 972625) B972625
theorem B969187 : Blo 860564 969187 := bstep (se 1 (by rfl) ⟨726890, by rfl⟩ : syracuseStep 969187 = 1453781) B1453781
theorem B3689059 : Blo 860564 3689059 := bstep (se 1 (by rfl) ⟨2766794, by rfl⟩ : syracuseStep 3689059 = 5533589) B5533589
theorem B1034867 : Blo 860564 1034867 := bstep (se 1 (by rfl) ⟨776150, by rfl⟩ : syracuseStep 1034867 = 1552301) B1552301
theorem B969331 : Blo 860564 969331 := bstep (se 1 (by rfl) ⟨726998, by rfl⟩ : syracuseStep 969331 = 1453997) B1453997
theorem B969475 : Blo 860564 969475 := bstep (se 1 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 969475 = 1454213) B1454213
theorem B1166113 : Blo 860564 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B2181937 : Blo 860564 2181937 := bstep (se 2 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 2181937 = 1636453) B1636453
theorem B6540101 : Blo 860564 6540101 := bstep (se 4 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 6540101 = 1226269) B1226269
theorem B969619 : Blo 860564 969619 := bstep (se 1 (by rfl) ⟨727214, by rfl⟩ : syracuseStep 969619 = 1454429) B1454429
theorem B969763 : Blo 860564 969763 := bstep (se 1 (by rfl) ⟨727322, by rfl⟩ : syracuseStep 969763 = 1454645) B1454645
theorem B2182211 : Blo 860564 2182211 := bstep (se 1 (by rfl) ⟨1636658, by rfl⟩ : syracuseStep 2182211 = 3273317) B3273317
theorem B4901957 : Blo 860564 4901957 := bstep (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) B919117
theorem B969907 : Blo 860564 969907 := bstep (se 1 (by rfl) ⟨727430, by rfl⟩ : syracuseStep 969907 = 1454861) B1454861
theorem B1166593 : Blo 860564 1166593 := bstep (se 2 (by rfl) ⟨437472, by rfl⟩ : syracuseStep 1166593 = 874945) B874945
theorem B2182403 : Blo 860564 2182403 := bstep (se 1 (by rfl) ⟨1636802, by rfl⟩ : syracuseStep 2182403 = 3273605) B3273605
theorem B970051 : Blo 860564 970051 := bstep (se 1 (by rfl) ⟨727538, by rfl⟩ : syracuseStep 970051 = 1455077) B1455077
theorem B2215363 : Blo 860564 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B970195 : Blo 860564 970195 := bstep (se 1 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 970195 = 1455293) B1455293
theorem B970339 : Blo 860564 970339 := bstep (se 1 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 970339 = 1455509) B1455509
theorem B970483 : Blo 860564 970483 := bstep (se 1 (by rfl) ⟨727862, by rfl⟩ : syracuseStep 970483 = 1455725) B1455725
theorem B1658659 : Blo 860564 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B3690289 : Blo 860564 3690289 := bstep (se 2 (by rfl) ⟨1383858, by rfl⟩ : syracuseStep 3690289 = 2767717) B2767717
theorem B4968305 : Blo 860564 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B970627 : Blo 860564 970627 := bstep (se 1 (by rfl) ⟨727970, by rfl⟩ : syracuseStep 970627 = 1455941) B1455941
theorem B970771 : Blo 860564 970771 := bstep (se 1 (by rfl) ⟨728078, by rfl⟩ : syracuseStep 970771 = 1456157) B1456157
theorem B6312077 : Blo 860564 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B970915 : Blo 860564 970915 := bstep (se 1 (by rfl) ⟨728186, by rfl⟩ : syracuseStep 970915 = 1456373) B1456373
theorem B2183345 : Blo 860564 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B2183395 : Blo 860564 2183395 := bstep (se 1 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 2183395 = 3275093) B3275093
theorem B10801379 : Blo 860564 10801379 := bstep (se 1 (by rfl) ⟨8101034, by rfl⟩ : syracuseStep 10801379 = 16202069) B16202069
theorem B971059 : Blo 860564 971059 := bstep (se 1 (by rfl) ⟨728294, by rfl⟩ : syracuseStep 971059 = 1456589) B1456589
theorem B2183537 : Blo 860564 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B2904497 : Blo 860564 2904497 := bstep (se 2 (by rfl) ⟨1089186, by rfl⟩ : syracuseStep 2904497 = 2178373) B2178373
theorem B971203 : Blo 860564 971203 := bstep (se 1 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 971203 = 1456805) B1456805
theorem B17912261 : Blo 860564 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B4149731 : Blo 860564 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B971347 : Blo 860564 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B2216593 : Blo 860564 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B971491 : Blo 860564 971491 := bstep (se 1 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 971491 = 1457237) B1457237
theorem B1168129 : Blo 860564 1168129 := bstep (se 2 (by rfl) ⟨438048, by rfl⟩ : syracuseStep 1168129 = 876097) B876097
theorem B873299 : Blo 860564 873299 := bstep (se 1 (by rfl) ⟨654974, by rfl⟩ : syracuseStep 873299 = 1309949) B1309949
theorem B971635 : Blo 860564 971635 := bstep (se 1 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 971635 = 1457453) B1457453
theorem B5526413 : Blo 860564 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B1168291 : Blo 860564 1168291 := bstep (se 1 (by rfl) ⟨876218, by rfl⟩ : syracuseStep 1168291 = 1752437) B1752437
theorem B2905037 : Blo 860564 2905037 := bstep (se 3 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 2905037 = 1089389) B1089389
theorem B1037299 : Blo 860564 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B2905091 : Blo 860564 2905091 := bstep (se 1 (by rfl) ⟨2178818, by rfl⟩ : syracuseStep 2905091 = 4357637) B4357637
theorem B971779 : Blo 860564 971779 := bstep (se 1 (by rfl) ⟨728834, by rfl⟩ : syracuseStep 971779 = 1457669) B1457669
theorem B2806883 : Blo 860564 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B1037443 : Blo 860564 1037443 := bstep (se 1 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 1037443 = 1556165) B1556165
theorem B971923 : Blo 860564 971923 := bstep (se 1 (by rfl) ⟨728942, by rfl⟩ : syracuseStep 971923 = 1457885) B1457885
theorem B2905361 : Blo 860564 2905361 := bstep (se 2 (by rfl) ⟨1089510, by rfl⟩ : syracuseStep 2905361 = 2179021) B2179021
theorem B972067 : Blo 860564 972067 := bstep (se 1 (by rfl) ⟨729050, by rfl⟩ : syracuseStep 972067 = 1458101) B1458101
theorem B4150577 : Blo 860564 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B2184529 : Blo 860564 2184529 := bstep (se 2 (by rfl) ⟨819198, by rfl⟩ : syracuseStep 2184529 = 1638397) B1638397
theorem B18666865 : Blo 860564 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B873875 : Blo 860564 873875 := bstep (se 1 (by rfl) ⟨655406, by rfl⟩ : syracuseStep 873875 = 1310813) B1310813
theorem B972211 : Blo 860564 972211 := bstep (se 1 (by rfl) ⟨729158, by rfl⟩ : syracuseStep 972211 = 1458317) B1458317
theorem B972355 : Blo 860564 972355 := bstep (se 1 (by rfl) ⟨729266, by rfl⟩ : syracuseStep 972355 = 1458533) B1458533
theorem B2184803 : Blo 860564 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B972499 : Blo 860564 972499 := bstep (se 1 (by rfl) ⟨729374, by rfl⟩ : syracuseStep 972499 = 1458749) B1458749
theorem B2184995 : Blo 860564 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B2905901 : Blo 860564 2905901 := bstep (se 3 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 2905901 = 1089713) B1089713
theorem B4970317 : Blo 860564 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B2905955 : Blo 860564 2905955 := bstep (se 1 (by rfl) ⟨2179466, by rfl⟩ : syracuseStep 2905955 = 4358933) B4358933
theorem B4970573 : Blo 860564 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B2906225 : Blo 860564 2906225 := bstep (se 2 (by rfl) ⟨1089834, by rfl⟩ : syracuseStep 2906225 = 2179669) B2179669
theorem B2906765 : Blo 860564 2906765 := bstep (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) B1090037
theorem B2906819 : Blo 860564 2906819 := bstep (se 1 (by rfl) ⟨2180114, by rfl⟩ : syracuseStep 2906819 = 4360229) B4360229
theorem B2185937 : Blo 860564 2185937 := bstep (se 2 (by rfl) ⟨819726, by rfl⟩ : syracuseStep 2185937 = 1639453) B1639453
theorem B1661699 : Blo 860564 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B2185987 : Blo 860564 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B4905805 : Blo 860564 4905805 := bstep (se 3 (by rfl) ⟨919838, by rfl⟩ : syracuseStep 4905805 = 1839677) B1839677
theorem B2186129 : Blo 860564 2186129 := bstep (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) B1639597
theorem B2907089 : Blo 860564 2907089 := bstep (se 2 (by rfl) ⟨1090158, by rfl⟩ : syracuseStep 2907089 = 2180317) B2180317
theorem B5528645 : Blo 860564 5528645 := bstep (se 4 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 5528645 = 1036621) B1036621
theorem B1596611 : Blo 860564 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B4152653 : Blo 860564 4152653 := bstep (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) B1557245
theorem B2907629 : Blo 860564 2907629 := bstep (se 3 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 2907629 = 1090361) B1090361
theorem B2907683 : Blo 860564 2907683 := bstep (se 1 (by rfl) ⟨2180762, by rfl⟩ : syracuseStep 2907683 = 4361525) B4361525
theorem B11787889 : Blo 860564 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B3268259 : Blo 860564 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2907953 : Blo 860564 2907953 := bstep (se 2 (by rfl) ⟨1090482, by rfl⟩ : syracuseStep 2907953 = 2180965) B2180965
theorem B2187121 : Blo 860564 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B3104675 : Blo 860564 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B11952197 : Blo 860564 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B83845205 : Blo 860564 83845205 := bstep (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) B982561
theorem B2187395 : Blo 860564 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B2187587 : Blo 860564 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B2908493 : Blo 860564 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B2908547 : Blo 860564 2908547 := bstep (se 1 (by rfl) ⟨2181410, by rfl⟩ : syracuseStep 2908547 = 4362821) B4362821
theorem B3498481 : Blo 860564 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B6545933 : Blo 860564 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B3269261 : Blo 860564 3269261 := bstep (se 3 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 3269261 = 1225973) B1225973
theorem B2908817 : Blo 860564 2908817 := bstep (se 2 (by rfl) ⟨1090806, by rfl⟩ : syracuseStep 2908817 = 2181613) B2181613
theorem B4907789 : Blo 860564 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B14770997 : Blo 860564 14770997 := bstep (se 5 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 14770997 = 1384781) B1384781
theorem B2909357 : Blo 860564 2909357 := bstep (se 3 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 2909357 = 1091009) B1091009
theorem B2909411 : Blo 860564 2909411 := bstep (se 1 (by rfl) ⟨2182058, by rfl⟩ : syracuseStep 2909411 = 4364117) B4364117
theorem B2909681 : Blo 860564 2909681 := bstep (se 2 (by rfl) ⟨1091130, by rfl⟩ : syracuseStep 2909681 = 2182261) B2182261
theorem B2450989 : Blo 860564 2450989 := bstep (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) B919121
theorem B4908721 : Blo 860564 4908721 := bstep (se 2 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 4908721 = 3681541) B3681541
theorem B3106531 : Blo 860564 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B2451217 : Blo 860564 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B2451377 : Blo 860564 2451377 := bstep (se 2 (by rfl) ⟨919266, by rfl⟩ : syracuseStep 2451377 = 1838533) B1838533
theorem B2910221 : Blo 860564 2910221 := bstep (se 3 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 2910221 = 1091333) B1091333
theorem B2451491 : Blo 860564 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B3237937 : Blo 860564 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2910275 : Blo 860564 2910275 := bstep (se 1 (by rfl) ⟨2182706, by rfl⟩ : syracuseStep 2910275 = 4365413) B4365413
theorem B3106993 : Blo 860564 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B2910545 : Blo 860564 2910545 := bstep (se 2 (by rfl) ⟨1091454, by rfl⟩ : syracuseStep 2910545 = 2182909) B2182909
theorem B1894819 : Blo 860564 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B6220273 : Blo 860564 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B3271373 : Blo 860564 3271373 := bstep (se 3 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 3271373 = 1226765) B1226765
theorem B2911085 : Blo 860564 2911085 := bstep (se 3 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 2911085 = 1091657) B1091657
theorem B2911139 : Blo 860564 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B2452493 : Blo 860564 2452493 := bstep (se 3 (by rfl) ⟨459842, by rfl⟩ : syracuseStep 2452493 = 919685) B919685
theorem B4910179 : Blo 860564 4910179 := bstep (se 1 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 4910179 = 7365269) B7365269
theorem B2911409 : Blo 860564 2911409 := bstep (se 2 (by rfl) ⟨1091778, by rfl⟩ : syracuseStep 2911409 = 2183557) B2183557
theorem B9825461 : Blo 860564 9825461 := bstep (se 5 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 9825461 = 921137) B921137
theorem B2452675 : Blo 860564 2452675 := bstep (se 1 (by rfl) ⟨1839506, by rfl⟩ : syracuseStep 2452675 = 3679013) B3679013
theorem B2452835 : Blo 860564 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B6548849 : Blo 860564 6548849 := bstep (se 2 (by rfl) ⟨2455818, by rfl⟩ : syracuseStep 6548849 = 4911637) B4911637
theorem B3272177 : Blo 860564 3272177 := bstep (se 2 (by rfl) ⟨1227066, by rfl⟩ : syracuseStep 3272177 = 2454133) B2454133
theorem B3108365 : Blo 860564 3108365 := bstep (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) B1165637
theorem B1633841 : Blo 860564 1633841 := bstep (se 2 (by rfl) ⟨612690, by rfl⟩ : syracuseStep 1633841 = 1225381) B1225381
theorem B4910705 : Blo 860564 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B2911949 : Blo 860564 2911949 := bstep (se 3 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 2911949 = 1091981) B1091981
theorem B2912003 : Blo 860564 2912003 := bstep (se 1 (by rfl) ⟨2184002, by rfl⟩ : syracuseStep 2912003 = 4368005) B4368005
theorem B2912273 : Blo 860564 2912273 := bstep (se 2 (by rfl) ⟨1092102, by rfl⟩ : syracuseStep 2912273 = 2184205) B2184205
theorem B3272845 : Blo 860564 3272845 := bstep (se 3 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 3272845 = 1227317) B1227317
theorem B1995043 : Blo 860564 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2453905 : Blo 860564 2453905 := bstep (se 2 (by rfl) ⟨920214, by rfl⟩ : syracuseStep 2453905 = 1840429) B1840429
theorem B1634737 : Blo 860564 1634737 := bstep (se 2 (by rfl) ⟨613026, by rfl⟩ : syracuseStep 1634737 = 1226053) B1226053
theorem B5239331 : Blo 860564 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B2912813 : Blo 860564 2912813 := bstep (se 3 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 2912813 = 1092305) B1092305
theorem B1634897 : Blo 860564 1634897 := bstep (se 2 (by rfl) ⟨613086, by rfl⟩ : syracuseStep 1634897 = 1226173) B1226173
theorem B2912867 : Blo 860564 2912867 := bstep (se 1 (by rfl) ⟨2184650, by rfl⟩ : syracuseStep 2912867 = 4369301) B4369301
theorem B1864433 : Blo 860564 1864433 := bstep (se 2 (by rfl) ⟨699162, by rfl⟩ : syracuseStep 1864433 = 1398325) B1398325
theorem B5534513 : Blo 860564 5534513 := bstep (se 2 (by rfl) ⟨2075442, by rfl⟩ : syracuseStep 5534513 = 4150885) B4150885
theorem B2913137 : Blo 860564 2913137 := bstep (se 2 (by rfl) ⟨1092426, by rfl⟩ : syracuseStep 2913137 = 2184853) B2184853
theorem B2945933 : Blo 860564 2945933 := bstep (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) B1104725
theorem B3273635 : Blo 860564 3273635 := bstep (se 1 (by rfl) ⟨2455226, by rfl⟩ : syracuseStep 3273635 = 4910453) B4910453
theorem B2618339 : Blo 860564 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B1635299 : Blo 860564 1635299 := bstep (se 1 (by rfl) ⟨1226474, by rfl⟩ : syracuseStep 1635299 = 2452949) B2452949
theorem B4912163 : Blo 860564 4912163 := bstep (se 1 (by rfl) ⟨3684122, by rfl⟩ : syracuseStep 4912163 = 7368245) B7368245
theorem B3110051 : Blo 860564 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B3503267 : Blo 860564 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B2618705 : Blo 860564 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B2913677 : Blo 860564 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B1242515 : Blo 860564 1242515 := bstep (se 1 (by rfl) ⟨931886, by rfl⟩ : syracuseStep 1242515 = 1863773) B1863773
theorem B2618801 : Blo 860564 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B2913731 : Blo 860564 2913731 := bstep (se 1 (by rfl) ⟨2185298, by rfl⟩ : syracuseStep 2913731 = 4370597) B4370597
theorem B3274289 : Blo 860564 3274289 := bstep (se 2 (by rfl) ⟨1227858, by rfl⟩ : syracuseStep 3274289 = 2455717) B2455717
theorem B2455181 : Blo 860564 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B2914001 : Blo 860564 2914001 := bstep (se 2 (by rfl) ⟨1092750, by rfl⟩ : syracuseStep 2914001 = 2185501) B2185501
theorem B2455363 : Blo 860564 2455363 := bstep (se 1 (by rfl) ⟨1841522, by rfl⟩ : syracuseStep 2455363 = 3683045) B3683045
theorem B1636195 : Blo 860564 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B2455409 : Blo 860564 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1472419 : Blo 860564 1472419 := bstep (se 1 (by rfl) ⟨1104314, by rfl⟩ : syracuseStep 1472419 = 2208629) B2208629
theorem B1636355 : Blo 860564 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B2488333 : Blo 860564 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B2914541 : Blo 860564 2914541 := bstep (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) B1092953
theorem B2914595 : Blo 860564 2914595 := bstep (se 1 (by rfl) ⟨2185946, by rfl⟩ : syracuseStep 2914595 = 4371893) B4371893
theorem B2914865 : Blo 860564 2914865 := bstep (se 2 (by rfl) ⟨1093074, by rfl⟩ : syracuseStep 2914865 = 2186149) B2186149
theorem B5896901 : Blo 860564 5896901 := bstep (se 4 (by rfl) ⟨552834, by rfl⟩ : syracuseStep 5896901 = 1105669) B1105669
theorem B4914053 : Blo 860564 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B3275747 : Blo 860564 3275747 := bstep (se 1 (by rfl) ⟨2456810, by rfl⟩ : syracuseStep 3275747 = 4913621) B4913621
theorem B3275761 : Blo 860564 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B1244179 : Blo 860564 1244179 := bstep (se 1 (by rfl) ⟨933134, by rfl⟩ : syracuseStep 1244179 = 1866269) B1866269
theorem B1637425 : Blo 860564 1637425 := bstep (se 2 (by rfl) ⟨614034, by rfl⟩ : syracuseStep 1637425 = 1228069) B1228069
theorem B2915405 : Blo 860564 2915405 := bstep (se 3 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 2915405 = 1093277) B1093277
theorem B6716515 : Blo 860564 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B2915459 : Blo 860564 2915459 := bstep (se 1 (by rfl) ⟨2186594, by rfl⟩ : syracuseStep 2915459 = 4373189) B4373189
theorem B55934165 : Blo 860564 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B2456867 : Blo 860564 2456867 := bstep (se 1 (by rfl) ⟨1842650, by rfl⟩ : syracuseStep 2456867 = 3685301) B3685301
theorem B14941493 : Blo 860564 14941493 := bstep (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) B1400765
theorem B4357475 : Blo 860564 4357475 := bstep (se 1 (by rfl) ⟨3268106, by rfl⟩ : syracuseStep 4357475 = 6536213) B6536213
theorem B2915729 : Blo 860564 2915729 := bstep (se 2 (by rfl) ⟨1093398, by rfl⟩ : syracuseStep 2915729 = 2186797) B2186797
theorem B1310131 : Blo 860564 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B1310179 : Blo 860564 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B1998371 : Blo 860564 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B884579 : Blo 860564 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B1867619 : Blo 860564 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B1310611 : Blo 860564 1310611 := bstep (se 1 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 1310611 = 1965917) B1965917
theorem B2916269 : Blo 860564 2916269 := bstep (se 3 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 2916269 = 1093601) B1093601
theorem B2916323 : Blo 860564 2916323 := bstep (se 1 (by rfl) ⟨2187242, by rfl⟩ : syracuseStep 2916323 = 4374485) B4374485
theorem B2457665 : Blo 860564 2457665 := bstep (se 2 (by rfl) ⟨921624, by rfl⟩ : syracuseStep 2457665 = 1843249) B1843249
theorem B17268997 : Blo 860564 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B1638731 : Blo 860564 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B2916701 : Blo 860564 2916701 := bstep (se 3 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 2916701 = 1093763) B1093763
theorem B1638785 : Blo 860564 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1966913 : Blo 860564 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B1639703 : Blo 860564 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1770839 : Blo 860564 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B1246603 : Blo 860564 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B2917835 : Blo 860564 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B4982347 : Blo 860564 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B1640243 : Blo 860564 1640243 := bstep (se 1 (by rfl) ⟨1230182, by rfl⟩ : syracuseStep 1640243 = 2460365) B2460365
theorem B4360067 : Blo 860564 4360067 := bstep (se 1 (by rfl) ⟨3270050, by rfl⟩ : syracuseStep 4360067 = 6540101) B6540101
theorem B5244803 : Blo 860564 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B919531 : Blo 860564 919531 := bstep (se 1 (by rfl) ⟨689648, by rfl⟩ : syracuseStep 919531 = 1379297) B1379297
theorem B6555653 : Blo 860564 6555653 := bstep (se 4 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 6555653 = 1229185) B1229185
theorem B1574923 : Blo 860564 1574923 := bstep (se 1 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 1574923 = 2362385) B2362385
theorem B2459737 : Blo 860564 2459737 := bstep (se 2 (by rfl) ⟨922401, by rfl⟩ : syracuseStep 2459737 = 1844803) B1844803
theorem B3541085 : Blo 860564 3541085 := bstep (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) B1327907
theorem B2328797 : Blo 860564 2328797 := bstep (se 3 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 2328797 = 873299) B873299
theorem B1640729 : Blo 860564 1640729 := bstep (se 2 (by rfl) ⟨615273, by rfl⟩ : syracuseStep 1640729 = 1230547) B1230547
theorem B3279149 : Blo 860564 3279149 := bstep (se 3 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 3279149 = 1229681) B1229681
theorem B2460125 : Blo 860564 2460125 := bstep (se 3 (by rfl) ⟨461273, by rfl⟩ : syracuseStep 2460125 = 922547) B922547
theorem B3312203 : Blo 860564 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B6982237 : Blo 860564 6982237 := bstep (se 3 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 6982237 = 2618339) B2618339
theorem B5900951 : Blo 860564 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B7473869 : Blo 860564 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B920279 : Blo 860564 920279 := bstep (se 1 (by rfl) ⟨690209, by rfl⟩ : syracuseStep 920279 = 1380419) B1380419
theorem B1936331 : Blo 860564 1936331 := bstep (se 1 (by rfl) ⟨1452248, by rfl⟩ : syracuseStep 1936331 = 2904497) B2904497
theorem B1936385 : Blo 860564 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B3279923 : Blo 860564 3279923 := bstep (se 1 (by rfl) ⟨2459942, by rfl⟩ : syracuseStep 3279923 = 4919885) B4919885
theorem B4787275 : Blo 860564 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B2952395 : Blo 860564 2952395 := bstep (se 1 (by rfl) ⟨2214296, by rfl⟩ : syracuseStep 2952395 = 4428593) B4428593
theorem B1936601 : Blo 860564 1936601 := bstep (se 2 (by rfl) ⟨726225, by rfl⟩ : syracuseStep 1936601 = 1452451) B1452451
theorem B2526425 : Blo 860564 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B1936691 : Blo 860564 1936691 := bstep (se 1 (by rfl) ⟨1452518, by rfl⟩ : syracuseStep 1936691 = 2905037) B2905037
theorem B8293697 : Blo 860564 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B1936727 : Blo 860564 1936727 := bstep (se 1 (by rfl) ⟨1452545, by rfl⟩ : syracuseStep 1936727 = 2905091) B2905091
theorem B1871255 : Blo 860564 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B4918745 : Blo 860564 4918745 := bstep (se 2 (by rfl) ⟨1844529, by rfl⟩ : syracuseStep 4918745 = 3689059) B3689059
theorem B1936907 : Blo 860564 1936907 := bstep (se 1 (by rfl) ⟨1452680, by rfl⟩ : syracuseStep 1936907 = 2905361) B2905361
theorem B1936961 : Blo 860564 1936961 := bstep (se 2 (by rfl) ⟨726360, by rfl⟩ : syracuseStep 1936961 = 1452721) B1452721
theorem B2330333 : Blo 860564 2330333 := bstep (se 3 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 2330333 = 873875) B873875
theorem B1937177 : Blo 860564 1937177 := bstep (se 2 (by rfl) ⟨726441, by rfl⟩ : syracuseStep 1937177 = 1452883) B1452883
theorem B1937267 : Blo 860564 1937267 := bstep (se 1 (by rfl) ⟨1452950, by rfl⟩ : syracuseStep 1937267 = 2905901) B2905901
theorem B1937303 : Blo 860564 1937303 := bstep (se 1 (by rfl) ⟨1452977, by rfl⟩ : syracuseStep 1937303 = 2905955) B2905955
theorem B3313715 : Blo 860564 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B1937483 : Blo 860564 1937483 := bstep (se 1 (by rfl) ⟨1453112, by rfl⟩ : syracuseStep 1937483 = 2906225) B2906225
theorem B1937537 : Blo 860564 1937537 := bstep (se 2 (by rfl) ⟨726576, by rfl⟩ : syracuseStep 1937537 = 1453153) B1453153
theorem B1839233 : Blo 860564 1839233 := bstep (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) B1379425
theorem B1577089 : Blo 860564 1577089 := bstep (se 2 (by rfl) ⟨591408, by rfl⟩ : syracuseStep 1577089 = 1182817) B1182817
theorem B6230195 : Blo 860564 6230195 := bstep (se 1 (by rfl) ⟨4672646, by rfl⟩ : syracuseStep 6230195 = 9345293) B9345293
theorem B2756953 : Blo 860564 2756953 := bstep (se 2 (by rfl) ⟨1033857, by rfl⟩ : syracuseStep 2756953 = 2067715) B2067715
theorem B1937753 : Blo 860564 1937753 := bstep (se 2 (by rfl) ⟨726657, by rfl⟩ : syracuseStep 1937753 = 1453315) B1453315
theorem B6558083 : Blo 860564 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B1937843 : Blo 860564 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B1937879 : Blo 860564 1937879 := bstep (se 1 (by rfl) ⟨1453409, by rfl⟩ : syracuseStep 1937879 = 2906819) B2906819
theorem B3281411 : Blo 860564 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2757185 : Blo 860564 2757185 := bstep (se 2 (by rfl) ⟨1033944, by rfl⟩ : syracuseStep 2757185 = 2067889) B2067889
theorem B2953817 : Blo 860564 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B1938059 : Blo 860564 1938059 := bstep (se 1 (by rfl) ⟨1453544, by rfl⟩ : syracuseStep 1938059 = 2907089) B2907089
theorem B1938113 : Blo 860564 1938113 := bstep (se 2 (by rfl) ⟨726792, by rfl⟩ : syracuseStep 1938113 = 1453585) B1453585
theorem B1381207 : Blo 860564 1381207 := bstep (se 1 (by rfl) ⟨1035905, by rfl⟩ : syracuseStep 1381207 = 2071811) B2071811
theorem B922487 : Blo 860564 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1938329 : Blo 860564 1938329 := bstep (se 2 (by rfl) ⟨726873, by rfl⟩ : syracuseStep 1938329 = 1453747) B1453747
theorem B3281867 : Blo 860564 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B1840087 : Blo 860564 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B1938419 : Blo 860564 1938419 := bstep (se 1 (by rfl) ⟨1453814, by rfl⟩ : syracuseStep 1938419 = 2907629) B2907629
theorem B1938455 : Blo 860564 1938455 := bstep (se 1 (by rfl) ⟨1453841, by rfl⟩ : syracuseStep 1938455 = 2907683) B2907683
theorem B4920385 : Blo 860564 4920385 := bstep (se 2 (by rfl) ⟨1845144, by rfl⟩ : syracuseStep 4920385 = 3690289) B3690289
theorem B1381463 : Blo 860564 1381463 := bstep (se 1 (by rfl) ⟨1036097, by rfl⟩ : syracuseStep 1381463 = 2072195) B2072195
theorem B3282065 : Blo 860564 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B2102465 : Blo 860564 2102465 := bstep (se 2 (by rfl) ⟨788424, by rfl⟩ : syracuseStep 2102465 = 1576849) B1576849
theorem B1938635 : Blo 860564 1938635 := bstep (se 1 (by rfl) ⟨1453976, by rfl⟩ : syracuseStep 1938635 = 2907953) B2907953
theorem B1578199 : Blo 860564 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B1938689 : Blo 860564 1938689 := bstep (se 2 (by rfl) ⟨727008, by rfl⟩ : syracuseStep 1938689 = 1454017) B1454017
theorem B2069783 : Blo 860564 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B7968131 : Blo 860564 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B2102707 : Blo 860564 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B1381835 : Blo 860564 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B1938905 : Blo 860564 1938905 := bstep (se 2 (by rfl) ⟨727089, by rfl⟩ : syracuseStep 1938905 = 1454179) B1454179
theorem B4363793 : Blo 860564 4363793 := bstep (se 2 (by rfl) ⟨1636422, by rfl⟩ : syracuseStep 4363793 = 3272845) B3272845
theorem B1938995 : Blo 860564 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B5969483 : Blo 860564 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B1939031 : Blo 860564 1939031 := bstep (se 1 (by rfl) ⟨1454273, by rfl⟩ : syracuseStep 1939031 = 2908547) B2908547
theorem B6624899 : Blo 860564 6624899 := bstep (se 1 (by rfl) ⟨4968674, by rfl⟩ : syracuseStep 6624899 = 9937349) B9937349
theorem B4363955 : Blo 860564 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B2660057 : Blo 860564 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B1939211 : Blo 860564 1939211 := bstep (se 1 (by rfl) ⟨1454408, by rfl⟩ : syracuseStep 1939211 = 2908817) B2908817
theorem B1382167 : Blo 860564 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B1939265 : Blo 860564 1939265 := bstep (se 2 (by rfl) ⟨727224, by rfl⟩ : syracuseStep 1939265 = 1454449) B1454449
theorem B1939481 : Blo 860564 1939481 := bstep (se 2 (by rfl) ⟨727305, by rfl⟩ : syracuseStep 1939481 = 1454611) B1454611
theorem B3676211 : Blo 860564 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B1939571 : Blo 860564 1939571 := bstep (se 1 (by rfl) ⟨1454678, by rfl⟩ : syracuseStep 1939571 = 2909357) B2909357
theorem B1841267 : Blo 860564 1841267 := bstep (se 1 (by rfl) ⟨1380950, by rfl⟩ : syracuseStep 1841267 = 2761901) B2761901
theorem B1939607 : Blo 860564 1939607 := bstep (se 1 (by rfl) ⟨1454705, by rfl⟩ : syracuseStep 1939607 = 2909411) B2909411
theorem B2955457 : Blo 860564 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B1579225 : Blo 860564 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B1939787 : Blo 860564 1939787 := bstep (se 1 (by rfl) ⟨1454840, by rfl⟩ : syracuseStep 1939787 = 2909681) B2909681
theorem B1939841 : Blo 860564 1939841 := bstep (se 2 (by rfl) ⟨727440, by rfl⟩ : syracuseStep 1939841 = 1454881) B1454881
theorem B1940057 : Blo 860564 1940057 := bstep (se 2 (by rfl) ⟨727521, by rfl⟩ : syracuseStep 1940057 = 1455043) B1455043
theorem B1383065 : Blo 860564 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B1940147 : Blo 860564 1940147 := bstep (se 1 (by rfl) ⟨1455110, by rfl⟩ : syracuseStep 1940147 = 2910221) B2910221
theorem B1940183 : Blo 860564 1940183 := bstep (se 1 (by rfl) ⟨1455137, by rfl⟩ : syracuseStep 1940183 = 2910275) B2910275
theorem B1383257 : Blo 860564 1383257 := bstep (se 2 (by rfl) ⟨518721, by rfl⟩ : syracuseStep 1383257 = 1037443) B1037443
theorem B1940363 : Blo 860564 1940363 := bstep (se 1 (by rfl) ⟨1455272, by rfl⟩ : syracuseStep 1940363 = 2910545) B2910545
theorem B1940417 : Blo 860564 1940417 := bstep (se 2 (by rfl) ⟨727656, by rfl⟩ : syracuseStep 1940417 = 1455313) B1455313
theorem B2759645 : Blo 860564 2759645 := bstep (se 3 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 2759645 = 1034867) B1034867
theorem B5610541 : Blo 860564 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B1940633 : Blo 860564 1940633 := bstep (se 2 (by rfl) ⟨727737, by rfl⟩ : syracuseStep 1940633 = 1455475) B1455475
theorem B1940723 : Blo 860564 1940723 := bstep (se 1 (by rfl) ⟨1455542, by rfl⟩ : syracuseStep 1940723 = 2911085) B2911085
theorem B3939587 : Blo 860564 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B1940759 : Blo 860564 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B1842497 : Blo 860564 1842497 := bstep (se 2 (by rfl) ⟨690936, by rfl⟩ : syracuseStep 1842497 = 1381873) B1381873
theorem B1940939 : Blo 860564 1940939 := bstep (se 1 (by rfl) ⟨1455704, by rfl⟩ : syracuseStep 1940939 = 2911409) B2911409
theorem B1940993 : Blo 860564 1940993 := bstep (se 2 (by rfl) ⟨727872, by rfl⟩ : syracuseStep 1940993 = 1455745) B1455745
theorem B4365899 : Blo 860564 4365899 := bstep (se 1 (by rfl) ⟨3274424, by rfl⟩ : syracuseStep 4365899 = 6548849) B6548849
theorem B5250691 : Blo 860564 5250691 := bstep (se 1 (by rfl) ⟨3938018, by rfl⟩ : syracuseStep 5250691 = 7876037) B7876037
theorem B2072243 : Blo 860564 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B2956979 : Blo 860564 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1089227 : Blo 860564 1089227 := bstep (se 1 (by rfl) ⟨816920, by rfl⟩ : syracuseStep 1089227 = 1633841) B1633841
theorem B6561485 : Blo 860564 6561485 := bstep (se 3 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 6561485 = 2460557) B2460557
theorem B1941209 : Blo 860564 1941209 := bstep (se 2 (by rfl) ⟨727953, by rfl⟩ : syracuseStep 1941209 = 1455907) B1455907
theorem B6627089 : Blo 860564 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B1941299 : Blo 860564 1941299 := bstep (se 1 (by rfl) ⟨1455974, by rfl⟩ : syracuseStep 1941299 = 2911949) B2911949
theorem B1941335 : Blo 860564 1941335 := bstep (se 1 (by rfl) ⟨1456001, by rfl⟩ : syracuseStep 1941335 = 2912003) B2912003
theorem B1941515 : Blo 860564 1941515 := bstep (se 1 (by rfl) ⟨1456136, by rfl⟩ : syracuseStep 1941515 = 2912273) B2912273
theorem B3317777 : Blo 860564 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B1941569 : Blo 860564 1941569 := bstep (se 2 (by rfl) ⟨728088, by rfl⟩ : syracuseStep 1941569 = 1456177) B1456177
theorem B6561971 : Blo 860564 6561971 := bstep (se 1 (by rfl) ⟨4921478, by rfl⟩ : syracuseStep 6561971 = 9842957) B9842957
theorem B1941785 : Blo 860564 1941785 := bstep (se 2 (by rfl) ⟨728169, by rfl⟩ : syracuseStep 1941785 = 1456339) B1456339
theorem B1941875 : Blo 860564 1941875 := bstep (se 1 (by rfl) ⟨1456406, by rfl⟩ : syracuseStep 1941875 = 2912813) B2912813
theorem B1089931 : Blo 860564 1089931 := bstep (se 1 (by rfl) ⟨817448, by rfl⟩ : syracuseStep 1089931 = 1634897) B1634897
theorem B27959701 : Blo 860564 27959701 := bstep (se 6 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 27959701 = 1310611) B1310611
theorem B860567 : Blo 860564 860567 := bstep (se 1 (by rfl) ⟨645425, by rfl⟩ : syracuseStep 860567 = 1290851) B1290851
theorem B1941911 : Blo 860564 1941911 := bstep (se 1 (by rfl) ⟨1456433, by rfl⟩ : syracuseStep 1941911 = 2912867) B2912867
theorem B1843607 : Blo 860564 1843607 := bstep (se 1 (by rfl) ⟨1382705, by rfl⟩ : syracuseStep 1843607 = 2765411) B2765411
theorem B860587 : Blo 860564 860587 := bstep (se 1 (by rfl) ⟨645440, by rfl⟩ : syracuseStep 860587 = 1290881) B1290881
theorem B4923827 : Blo 860564 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B860599 : Blo 860564 860599 := bstep (se 1 (by rfl) ⟨645449, by rfl⟩ : syracuseStep 860599 = 1290899) B1290899
theorem B860619 : Blo 860564 860619 := bstep (se 1 (by rfl) ⟨645464, by rfl⟩ : syracuseStep 860619 = 1290929) B1290929
theorem B860631 : Blo 860564 860631 := bstep (se 1 (by rfl) ⟨645473, by rfl⟩ : syracuseStep 860631 = 1290947) B1290947
theorem B860651 : Blo 860564 860651 := bstep (se 1 (by rfl) ⟨645488, by rfl⟩ : syracuseStep 860651 = 1290977) B1290977
theorem B860663 : Blo 860564 860663 := bstep (se 1 (by rfl) ⟨645497, by rfl⟩ : syracuseStep 860663 = 1290995) B1290995
theorem B860683 : Blo 860564 860683 := bstep (se 1 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 860683 = 1291025) B1291025
theorem B860695 : Blo 860564 860695 := bstep (se 1 (by rfl) ⟨645521, by rfl⟩ : syracuseStep 860695 = 1291043) B1291043
theorem B860715 : Blo 860564 860715 := bstep (se 1 (by rfl) ⟨645536, by rfl⟩ : syracuseStep 860715 = 1291073) B1291073
theorem B860727 : Blo 860564 860727 := bstep (se 1 (by rfl) ⟨645545, by rfl⟩ : syracuseStep 860727 = 1291091) B1291091
theorem B860747 : Blo 860564 860747 := bstep (se 1 (by rfl) ⟨645560, by rfl⟩ : syracuseStep 860747 = 1291121) B1291121
theorem B1942091 : Blo 860564 1942091 := bstep (se 1 (by rfl) ⟨1456568, by rfl⟩ : syracuseStep 1942091 = 2913137) B2913137
theorem B860759 : Blo 860564 860759 := bstep (se 1 (by rfl) ⟨645569, by rfl⟩ : syracuseStep 860759 = 1291139) B1291139
theorem B860779 : Blo 860564 860779 := bstep (se 1 (by rfl) ⟨645584, by rfl⟩ : syracuseStep 860779 = 1291169) B1291169
theorem B860791 : Blo 860564 860791 := bstep (se 1 (by rfl) ⟨645593, by rfl⟩ : syracuseStep 860791 = 1291187) B1291187
theorem B1942145 : Blo 860564 1942145 := bstep (se 2 (by rfl) ⟨728304, by rfl⟩ : syracuseStep 1942145 = 1456609) B1456609
theorem B860811 : Blo 860564 860811 := bstep (se 1 (by rfl) ⟨645608, by rfl⟩ : syracuseStep 860811 = 1291217) B1291217
theorem B860823 : Blo 860564 860823 := bstep (se 1 (by rfl) ⟨645617, by rfl⟩ : syracuseStep 860823 = 1291235) B1291235
theorem B1090199 : Blo 860564 1090199 := bstep (se 1 (by rfl) ⟨817649, by rfl⟩ : syracuseStep 1090199 = 1635299) B1635299
theorem B860843 : Blo 860564 860843 := bstep (se 1 (by rfl) ⟨645632, by rfl⟩ : syracuseStep 860843 = 1291265) B1291265
theorem B860855 : Blo 860564 860855 := bstep (se 1 (by rfl) ⟨645641, by rfl⟩ : syracuseStep 860855 = 1291283) B1291283
theorem B860875 : Blo 860564 860875 := bstep (se 1 (by rfl) ⟨645656, by rfl⟩ : syracuseStep 860875 = 1291313) B1291313
theorem B860887 : Blo 860564 860887 := bstep (se 1 (by rfl) ⟨645665, by rfl⟩ : syracuseStep 860887 = 1291331) B1291331
theorem B860907 : Blo 860564 860907 := bstep (se 1 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 860907 = 1291361) B1291361
theorem B860919 : Blo 860564 860919 := bstep (se 1 (by rfl) ⟨645689, by rfl⟩ : syracuseStep 860919 = 1291379) B1291379
theorem B3678979 : Blo 860564 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B860939 : Blo 860564 860939 := bstep (se 1 (by rfl) ⟨645704, by rfl⟩ : syracuseStep 860939 = 1291409) B1291409
theorem B860951 : Blo 860564 860951 := bstep (se 1 (by rfl) ⟨645713, by rfl⟩ : syracuseStep 860951 = 1291427) B1291427
theorem B2073367 : Blo 860564 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B2335511 : Blo 860564 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B860971 : Blo 860564 860971 := bstep (se 1 (by rfl) ⟨645728, by rfl⟩ : syracuseStep 860971 = 1291457) B1291457
theorem B860983 : Blo 860564 860983 := bstep (se 1 (by rfl) ⟨645737, by rfl⟩ : syracuseStep 860983 = 1291475) B1291475
theorem B861003 : Blo 860564 861003 := bstep (se 1 (by rfl) ⟨645752, by rfl⟩ : syracuseStep 861003 = 1291505) B1291505
theorem B861015 : Blo 860564 861015 := bstep (se 1 (by rfl) ⟨645761, by rfl⟩ : syracuseStep 861015 = 1291523) B1291523
theorem B1942361 : Blo 860564 1942361 := bstep (se 2 (by rfl) ⟨728385, by rfl⟩ : syracuseStep 1942361 = 1456771) B1456771
theorem B861035 : Blo 860564 861035 := bstep (se 1 (by rfl) ⟨645776, by rfl⟩ : syracuseStep 861035 = 1291553) B1291553
theorem B861047 : Blo 860564 861047 := bstep (se 1 (by rfl) ⟨645785, by rfl⟩ : syracuseStep 861047 = 1291571) B1291571
theorem B861067 : Blo 860564 861067 := bstep (se 1 (by rfl) ⟨645800, by rfl⟩ : syracuseStep 861067 = 1291601) B1291601
theorem B1745803 : Blo 860564 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B861079 : Blo 860564 861079 := bstep (se 1 (by rfl) ⟨645809, by rfl⟩ : syracuseStep 861079 = 1291619) B1291619
theorem B861099 : Blo 860564 861099 := bstep (se 1 (by rfl) ⟨645824, by rfl⟩ : syracuseStep 861099 = 1291649) B1291649
theorem B1942451 : Blo 860564 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B861111 : Blo 860564 861111 := bstep (se 1 (by rfl) ⟨645833, by rfl⟩ : syracuseStep 861111 = 1291667) B1291667
theorem B861131 : Blo 860564 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B1745867 : Blo 860564 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B861143 : Blo 860564 861143 := bstep (se 1 (by rfl) ⟨645857, by rfl⟩ : syracuseStep 861143 = 1291715) B1291715
theorem B1942487 : Blo 860564 1942487 := bstep (se 1 (by rfl) ⟨1456865, by rfl⟩ : syracuseStep 1942487 = 2913731) B2913731
theorem B861163 : Blo 860564 861163 := bstep (se 1 (by rfl) ⟨645872, by rfl⟩ : syracuseStep 861163 = 1291745) B1291745
theorem B861175 : Blo 860564 861175 := bstep (se 1 (by rfl) ⟨645881, by rfl⟩ : syracuseStep 861175 = 1291763) B1291763
theorem B861195 : Blo 860564 861195 := bstep (se 1 (by rfl) ⟨645896, by rfl⟩ : syracuseStep 861195 = 1291793) B1291793
theorem B861207 : Blo 860564 861207 := bstep (se 1 (by rfl) ⟨645905, by rfl⟩ : syracuseStep 861207 = 1291811) B1291811
theorem B861227 : Blo 860564 861227 := bstep (se 1 (by rfl) ⟨645920, by rfl⟩ : syracuseStep 861227 = 1291841) B1291841
theorem B861239 : Blo 860564 861239 := bstep (se 1 (by rfl) ⟨645929, by rfl⟩ : syracuseStep 861239 = 1291859) B1291859
theorem B861259 : Blo 860564 861259 := bstep (se 1 (by rfl) ⟨645944, by rfl⟩ : syracuseStep 861259 = 1291889) B1291889
theorem B861271 : Blo 860564 861271 := bstep (se 1 (by rfl) ⟨645953, by rfl⟩ : syracuseStep 861271 = 1291907) B1291907
theorem B861291 : Blo 860564 861291 := bstep (se 1 (by rfl) ⟨645968, by rfl⟩ : syracuseStep 861291 = 1291937) B1291937
theorem B861303 : Blo 860564 861303 := bstep (se 1 (by rfl) ⟨645977, by rfl⟩ : syracuseStep 861303 = 1291955) B1291955
theorem B861323 : Blo 860564 861323 := bstep (se 1 (by rfl) ⟨645992, by rfl⟩ : syracuseStep 861323 = 1291985) B1291985
theorem B1942667 : Blo 860564 1942667 := bstep (se 1 (by rfl) ⟨1457000, by rfl⟩ : syracuseStep 1942667 = 2914001) B2914001
theorem B861335 : Blo 860564 861335 := bstep (se 1 (by rfl) ⟨646001, by rfl⟩ : syracuseStep 861335 = 1292003) B1292003
theorem B861355 : Blo 860564 861355 := bstep (se 1 (by rfl) ⟨646016, by rfl⟩ : syracuseStep 861355 = 1292033) B1292033
theorem B5514419 : Blo 860564 5514419 := bstep (se 1 (by rfl) ⟨4135814, by rfl⟩ : syracuseStep 5514419 = 8271629) B8271629
theorem B861367 : Blo 860564 861367 := bstep (se 1 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 861367 = 1292051) B1292051
theorem B1942721 : Blo 860564 1942721 := bstep (se 2 (by rfl) ⟨728520, by rfl⟩ : syracuseStep 1942721 = 1457041) B1457041
theorem B861387 : Blo 860564 861387 := bstep (se 1 (by rfl) ⟨646040, by rfl⟩ : syracuseStep 861387 = 1292081) B1292081
theorem B861399 : Blo 860564 861399 := bstep (se 1 (by rfl) ⟨646049, by rfl⟩ : syracuseStep 861399 = 1292099) B1292099
theorem B861419 : Blo 860564 861419 := bstep (se 1 (by rfl) ⟨646064, by rfl⟩ : syracuseStep 861419 = 1292129) B1292129
theorem B861431 : Blo 860564 861431 := bstep (se 1 (by rfl) ⟨646073, by rfl⟩ : syracuseStep 861431 = 1292147) B1292147
theorem B861451 : Blo 860564 861451 := bstep (se 1 (by rfl) ⟨646088, by rfl⟩ : syracuseStep 861451 = 1292177) B1292177
theorem B861463 : Blo 860564 861463 := bstep (se 1 (by rfl) ⟨646097, by rfl⟩ : syracuseStep 861463 = 1292195) B1292195
theorem B861483 : Blo 860564 861483 := bstep (se 1 (by rfl) ⟨646112, by rfl⟩ : syracuseStep 861483 = 1292225) B1292225
theorem B861495 : Blo 860564 861495 := bstep (se 1 (by rfl) ⟨646121, by rfl⟩ : syracuseStep 861495 = 1292243) B1292243
theorem B4367681 : Blo 860564 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B861515 : Blo 860564 861515 := bstep (se 1 (by rfl) ⟨646136, by rfl⟩ : syracuseStep 861515 = 1292273) B1292273
theorem B861527 : Blo 860564 861527 := bstep (se 1 (by rfl) ⟨646145, by rfl⟩ : syracuseStep 861527 = 1292291) B1292291
theorem B1090903 : Blo 860564 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B861547 : Blo 860564 861547 := bstep (se 1 (by rfl) ⟨646160, by rfl⟩ : syracuseStep 861547 = 1292321) B1292321
theorem B861559 : Blo 860564 861559 := bstep (se 1 (by rfl) ⟨646169, by rfl⟩ : syracuseStep 861559 = 1292339) B1292339
theorem B861579 : Blo 860564 861579 := bstep (se 1 (by rfl) ⟨646184, by rfl⟩ : syracuseStep 861579 = 1292369) B1292369
theorem B861591 : Blo 860564 861591 := bstep (se 1 (by rfl) ⟨646193, by rfl⟩ : syracuseStep 861591 = 1292387) B1292387
theorem B1942937 : Blo 860564 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1844633 : Blo 860564 1844633 := bstep (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) B1383475
theorem B861611 : Blo 860564 861611 := bstep (se 1 (by rfl) ⟨646208, by rfl⟩ : syracuseStep 861611 = 1292417) B1292417
theorem B861623 : Blo 860564 861623 := bstep (se 1 (by rfl) ⟨646217, by rfl⟩ : syracuseStep 861623 = 1292435) B1292435
theorem B861643 : Blo 860564 861643 := bstep (se 1 (by rfl) ⟨646232, by rfl⟩ : syracuseStep 861643 = 1292465) B1292465
theorem B861655 : Blo 860564 861655 := bstep (se 1 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 861655 = 1292483) B1292483
theorem B8955353 : Blo 860564 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B861675 : Blo 860564 861675 := bstep (se 1 (by rfl) ⟨646256, by rfl⟩ : syracuseStep 861675 = 1292513) B1292513
theorem B1943027 : Blo 860564 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B861687 : Blo 860564 861687 := bstep (se 1 (by rfl) ⟨646265, by rfl⟩ : syracuseStep 861687 = 1292531) B1292531
theorem B861707 : Blo 860564 861707 := bstep (se 1 (by rfl) ⟨646280, by rfl⟩ : syracuseStep 861707 = 1292561) B1292561
theorem B861719 : Blo 860564 861719 := bstep (se 1 (by rfl) ⟨646289, by rfl⟩ : syracuseStep 861719 = 1292579) B1292579
theorem B1943063 : Blo 860564 1943063 := bstep (se 1 (by rfl) ⟨1457297, by rfl⟩ : syracuseStep 1943063 = 2914595) B2914595
theorem B861739 : Blo 860564 861739 := bstep (se 1 (by rfl) ⟨646304, by rfl⟩ : syracuseStep 861739 = 1292609) B1292609
theorem B861751 : Blo 860564 861751 := bstep (se 1 (by rfl) ⟨646313, by rfl⟩ : syracuseStep 861751 = 1292627) B1292627
theorem B861771 : Blo 860564 861771 := bstep (se 1 (by rfl) ⟨646328, by rfl⟩ : syracuseStep 861771 = 1292657) B1292657
theorem B861783 : Blo 860564 861783 := bstep (se 1 (by rfl) ⟨646337, by rfl⟩ : syracuseStep 861783 = 1292675) B1292675
theorem B6563429 : Blo 860564 6563429 := bstep (se 4 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 6563429 = 1230643) B1230643
theorem B861803 : Blo 860564 861803 := bstep (se 1 (by rfl) ⟨646352, by rfl⟩ : syracuseStep 861803 = 1292705) B1292705
theorem B861815 : Blo 860564 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B861835 : Blo 860564 861835 := bstep (se 1 (by rfl) ⟨646376, by rfl⟩ : syracuseStep 861835 = 1292753) B1292753
theorem B861847 : Blo 860564 861847 := bstep (se 1 (by rfl) ⟨646385, by rfl⟩ : syracuseStep 861847 = 1292771) B1292771
theorem B861867 : Blo 860564 861867 := bstep (se 1 (by rfl) ⟨646400, by rfl⟩ : syracuseStep 861867 = 1292801) B1292801
theorem B861879 : Blo 860564 861879 := bstep (se 1 (by rfl) ⟨646409, by rfl⟩ : syracuseStep 861879 = 1292819) B1292819
theorem B3679937 : Blo 860564 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B861899 : Blo 860564 861899 := bstep (se 1 (by rfl) ⟨646424, by rfl⟩ : syracuseStep 861899 = 1292849) B1292849
theorem B1943243 : Blo 860564 1943243 := bstep (se 1 (by rfl) ⟨1457432, by rfl⟩ : syracuseStep 1943243 = 2914865) B2914865
theorem B861911 : Blo 860564 861911 := bstep (se 1 (by rfl) ⟨646433, by rfl⟩ : syracuseStep 861911 = 1292867) B1292867
theorem B861931 : Blo 860564 861931 := bstep (se 1 (by rfl) ⟨646448, by rfl⟩ : syracuseStep 861931 = 1292897) B1292897
theorem B861943 : Blo 860564 861943 := bstep (se 1 (by rfl) ⟨646457, by rfl⟩ : syracuseStep 861943 = 1292915) B1292915
theorem B1943297 : Blo 860564 1943297 := bstep (se 2 (by rfl) ⟨728736, by rfl⟩ : syracuseStep 1943297 = 1457473) B1457473
theorem B861963 : Blo 860564 861963 := bstep (se 1 (by rfl) ⟨646472, by rfl⟩ : syracuseStep 861963 = 1292945) B1292945
theorem B861975 : Blo 860564 861975 := bstep (se 1 (by rfl) ⟨646481, by rfl⟩ : syracuseStep 861975 = 1292963) B1292963
theorem B861995 : Blo 860564 861995 := bstep (se 1 (by rfl) ⟨646496, by rfl⟩ : syracuseStep 861995 = 1292993) B1292993
theorem B862007 : Blo 860564 862007 := bstep (se 1 (by rfl) ⟨646505, by rfl⟩ : syracuseStep 862007 = 1293011) B1293011
theorem B862027 : Blo 860564 862027 := bstep (se 1 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 862027 = 1293041) B1293041
theorem B862039 : Blo 860564 862039 := bstep (se 1 (by rfl) ⟨646529, by rfl⟩ : syracuseStep 862039 = 1293059) B1293059
theorem B862059 : Blo 860564 862059 := bstep (se 1 (by rfl) ⟨646544, by rfl⟩ : syracuseStep 862059 = 1293089) B1293089
theorem B862071 : Blo 860564 862071 := bstep (se 1 (by rfl) ⟨646553, by rfl⟩ : syracuseStep 862071 = 1293107) B1293107
theorem B862091 : Blo 860564 862091 := bstep (se 1 (by rfl) ⟨646568, by rfl⟩ : syracuseStep 862091 = 1293137) B1293137
theorem B862103 : Blo 860564 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B1746841 : Blo 860564 1746841 := bstep (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) B1310131
theorem B862123 : Blo 860564 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B862135 : Blo 860564 862135 := bstep (se 1 (by rfl) ⟨646601, by rfl⟩ : syracuseStep 862135 = 1293203) B1293203
theorem B862155 : Blo 860564 862155 := bstep (se 1 (by rfl) ⟨646616, by rfl⟩ : syracuseStep 862155 = 1293233) B1293233
theorem B862167 : Blo 860564 862167 := bstep (se 1 (by rfl) ⟨646625, by rfl⟩ : syracuseStep 862167 = 1293251) B1293251
theorem B1746905 : Blo 860564 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B1943513 : Blo 860564 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B862187 : Blo 860564 862187 := bstep (se 1 (by rfl) ⟨646640, by rfl⟩ : syracuseStep 862187 = 1293281) B1293281
theorem B862199 : Blo 860564 862199 := bstep (se 1 (by rfl) ⟨646649, by rfl⟩ : syracuseStep 862199 = 1293299) B1293299
theorem B862219 : Blo 860564 862219 := bstep (se 1 (by rfl) ⟨646664, by rfl⟩ : syracuseStep 862219 = 1293329) B1293329
theorem B862231 : Blo 860564 862231 := bstep (se 1 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 862231 = 1293347) B1293347
theorem B862251 : Blo 860564 862251 := bstep (se 1 (by rfl) ⟨646688, by rfl⟩ : syracuseStep 862251 = 1293377) B1293377
theorem B1943603 : Blo 860564 1943603 := bstep (se 1 (by rfl) ⟨1457702, by rfl⟩ : syracuseStep 1943603 = 2915405) B2915405
theorem B862263 : Blo 860564 862263 := bstep (se 1 (by rfl) ⟨646697, by rfl⟩ : syracuseStep 862263 = 1293395) B1293395
theorem B862283 : Blo 860564 862283 := bstep (se 1 (by rfl) ⟨646712, by rfl⟩ : syracuseStep 862283 = 1293425) B1293425
theorem B6563915 : Blo 860564 6563915 := bstep (se 1 (by rfl) ⟨4922936, by rfl⟩ : syracuseStep 6563915 = 9845873) B9845873
theorem B862295 : Blo 860564 862295 := bstep (se 1 (by rfl) ⟨646721, by rfl⟩ : syracuseStep 862295 = 1293443) B1293443
theorem B1943639 : Blo 860564 1943639 := bstep (se 1 (by rfl) ⟨1457729, by rfl⟩ : syracuseStep 1943639 = 2915459) B2915459
theorem B9807965 : Blo 860564 9807965 := bstep (se 3 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 9807965 = 3677987) B3677987
theorem B862315 : Blo 860564 862315 := bstep (se 1 (by rfl) ⟨646736, by rfl⟩ : syracuseStep 862315 = 1293473) B1293473
theorem B862327 : Blo 860564 862327 := bstep (se 1 (by rfl) ⟨646745, by rfl⟩ : syracuseStep 862327 = 1293491) B1293491
theorem B862347 : Blo 860564 862347 := bstep (se 1 (by rfl) ⟨646760, by rfl⟩ : syracuseStep 862347 = 1293521) B1293521
theorem B862359 : Blo 860564 862359 := bstep (se 1 (by rfl) ⟨646769, by rfl⟩ : syracuseStep 862359 = 1293539) B1293539
theorem B862379 : Blo 860564 862379 := bstep (se 1 (by rfl) ⟨646784, by rfl⟩ : syracuseStep 862379 = 1293569) B1293569
theorem B862391 : Blo 860564 862391 := bstep (se 1 (by rfl) ⟨646793, by rfl⟩ : syracuseStep 862391 = 1293587) B1293587
theorem B1452235 : Blo 860564 1452235 := bstep (se 1 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 1452235 = 2178353) B2178353
theorem B862411 : Blo 860564 862411 := bstep (se 1 (by rfl) ⟨646808, by rfl⟩ : syracuseStep 862411 = 1293617) B1293617
theorem B862423 : Blo 860564 862423 := bstep (se 1 (by rfl) ⟨646817, by rfl⟩ : syracuseStep 862423 = 1293635) B1293635
theorem B862443 : Blo 860564 862443 := bstep (se 1 (by rfl) ⟨646832, by rfl⟩ : syracuseStep 862443 = 1293665) B1293665
theorem B862455 : Blo 860564 862455 := bstep (se 1 (by rfl) ⟨646841, by rfl⟩ : syracuseStep 862455 = 1293683) B1293683
theorem B862475 : Blo 860564 862475 := bstep (se 1 (by rfl) ⟨646856, by rfl⟩ : syracuseStep 862475 = 1293713) B1293713
theorem B1943819 : Blo 860564 1943819 := bstep (se 1 (by rfl) ⟨1457864, by rfl⟩ : syracuseStep 1943819 = 2915729) B2915729
theorem B862487 : Blo 860564 862487 := bstep (se 1 (by rfl) ⟨646865, by rfl⟩ : syracuseStep 862487 = 1293731) B1293731
theorem B862507 : Blo 860564 862507 := bstep (se 1 (by rfl) ⟨646880, by rfl⟩ : syracuseStep 862507 = 1293761) B1293761
theorem B862519 : Blo 860564 862519 := bstep (se 1 (by rfl) ⟨646889, by rfl⟩ : syracuseStep 862519 = 1293779) B1293779
theorem B1943873 : Blo 860564 1943873 := bstep (se 2 (by rfl) ⟨728952, by rfl⟩ : syracuseStep 1943873 = 1457905) B1457905
theorem B862539 : Blo 860564 862539 := bstep (se 1 (by rfl) ⟨646904, by rfl⟩ : syracuseStep 862539 = 1293809) B1293809
theorem B862551 : Blo 860564 862551 := bstep (se 1 (by rfl) ⟨646913, by rfl⟩ : syracuseStep 862551 = 1293827) B1293827
theorem B1452377 : Blo 860564 1452377 := bstep (se 2 (by rfl) ⟨544641, by rfl⟩ : syracuseStep 1452377 = 1089283) B1089283
theorem B862571 : Blo 860564 862571 := bstep (se 1 (by rfl) ⟨646928, by rfl⟩ : syracuseStep 862571 = 1293857) B1293857
theorem B862583 : Blo 860564 862583 := bstep (se 1 (by rfl) ⟨646937, by rfl⟩ : syracuseStep 862583 = 1293875) B1293875
theorem B862603 : Blo 860564 862603 := bstep (se 1 (by rfl) ⟨646952, by rfl⟩ : syracuseStep 862603 = 1293905) B1293905
theorem B862615 : Blo 860564 862615 := bstep (se 1 (by rfl) ⟨646961, by rfl⟩ : syracuseStep 862615 = 1293923) B1293923
theorem B862635 : Blo 860564 862635 := bstep (se 1 (by rfl) ⟨646976, by rfl⟩ : syracuseStep 862635 = 1293953) B1293953
theorem B862647 : Blo 860564 862647 := bstep (se 1 (by rfl) ⟨646985, by rfl⟩ : syracuseStep 862647 = 1293971) B1293971
theorem B862667 : Blo 860564 862667 := bstep (se 1 (by rfl) ⟨647000, by rfl⟩ : syracuseStep 862667 = 1294001) B1294001
theorem B862679 : Blo 860564 862679 := bstep (se 1 (by rfl) ⟨647009, by rfl⟩ : syracuseStep 862679 = 1294019) B1294019
theorem B1452505 : Blo 860564 1452505 := bstep (se 2 (by rfl) ⟨544689, by rfl⟩ : syracuseStep 1452505 = 1089379) B1089379
theorem B862699 : Blo 860564 862699 := bstep (se 1 (by rfl) ⟨647024, by rfl⟩ : syracuseStep 862699 = 1294049) B1294049
theorem B862711 : Blo 860564 862711 := bstep (se 1 (by rfl) ⟨647033, by rfl⟩ : syracuseStep 862711 = 1294067) B1294067
theorem B862731 : Blo 860564 862731 := bstep (se 1 (by rfl) ⟨647048, by rfl⟩ : syracuseStep 862731 = 1294097) B1294097
theorem B862743 : Blo 860564 862743 := bstep (se 1 (by rfl) ⟨647057, by rfl⟩ : syracuseStep 862743 = 1294115) B1294115
theorem B1944089 : Blo 860564 1944089 := bstep (se 2 (by rfl) ⟨729033, by rfl⟩ : syracuseStep 1944089 = 1458067) B1458067
theorem B862763 : Blo 860564 862763 := bstep (se 1 (by rfl) ⟨647072, by rfl⟩ : syracuseStep 862763 = 1294145) B1294145
theorem B862775 : Blo 860564 862775 := bstep (se 1 (by rfl) ⟨647081, by rfl⟩ : syracuseStep 862775 = 1294163) B1294163
theorem B862795 : Blo 860564 862795 := bstep (se 1 (by rfl) ⟨647096, by rfl⟩ : syracuseStep 862795 = 1294193) B1294193
theorem B862807 : Blo 860564 862807 := bstep (se 1 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 862807 = 1294211) B1294211
theorem B862827 : Blo 860564 862827 := bstep (se 1 (by rfl) ⟨647120, by rfl⟩ : syracuseStep 862827 = 1294241) B1294241
theorem B1944179 : Blo 860564 1944179 := bstep (se 1 (by rfl) ⟨1458134, by rfl⟩ : syracuseStep 1944179 = 2916269) B2916269
theorem B862839 : Blo 860564 862839 := bstep (se 1 (by rfl) ⟨647129, by rfl⟩ : syracuseStep 862839 = 1294259) B1294259
theorem B862859 : Blo 860564 862859 := bstep (se 1 (by rfl) ⟨647144, by rfl⟩ : syracuseStep 862859 = 1294289) B1294289
theorem B862871 : Blo 860564 862871 := bstep (se 1 (by rfl) ⟨647153, by rfl⟩ : syracuseStep 862871 = 1294307) B1294307
theorem B1944215 : Blo 860564 1944215 := bstep (se 1 (by rfl) ⟨1458161, by rfl⟩ : syracuseStep 1944215 = 2916323) B2916323
theorem B862891 : Blo 860564 862891 := bstep (se 1 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 862891 = 1294337) B1294337
theorem B862903 : Blo 860564 862903 := bstep (se 1 (by rfl) ⟨647177, by rfl⟩ : syracuseStep 862903 = 1294355) B1294355
theorem B862923 : Blo 860564 862923 := bstep (se 1 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 862923 = 1294385) B1294385
theorem B862935 : Blo 860564 862935 := bstep (se 1 (by rfl) ⟨647201, by rfl⟩ : syracuseStep 862935 = 1294403) B1294403
theorem B862955 : Blo 860564 862955 := bstep (se 1 (by rfl) ⟨647216, by rfl⟩ : syracuseStep 862955 = 1294433) B1294433
theorem B862967 : Blo 860564 862967 := bstep (se 1 (by rfl) ⟨647225, by rfl⟩ : syracuseStep 862967 = 1294451) B1294451
theorem B862987 : Blo 860564 862987 := bstep (se 1 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 862987 = 1294481) B1294481
theorem B862999 : Blo 860564 862999 := bstep (se 1 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 862999 = 1294499) B1294499
theorem B863019 : Blo 860564 863019 := bstep (se 1 (by rfl) ⟨647264, by rfl⟩ : syracuseStep 863019 = 1294529) B1294529
theorem B863031 : Blo 860564 863031 := bstep (se 1 (by rfl) ⟨647273, by rfl⟩ : syracuseStep 863031 = 1294547) B1294547
theorem B863051 : Blo 860564 863051 := bstep (se 1 (by rfl) ⟨647288, by rfl⟩ : syracuseStep 863051 = 1294577) B1294577
theorem B1944395 : Blo 860564 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B863063 : Blo 860564 863063 := bstep (se 1 (by rfl) ⟨647297, by rfl⟩ : syracuseStep 863063 = 1294595) B1294595
theorem B863083 : Blo 860564 863083 := bstep (se 1 (by rfl) ⟨647312, by rfl⟩ : syracuseStep 863083 = 1294625) B1294625
theorem B863095 : Blo 860564 863095 := bstep (se 1 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 863095 = 1294643) B1294643
theorem B1944449 : Blo 860564 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B863115 : Blo 860564 863115 := bstep (se 1 (by rfl) ⟨647336, by rfl⟩ : syracuseStep 863115 = 1294673) B1294673
theorem B863127 : Blo 860564 863127 := bstep (se 1 (by rfl) ⟨647345, by rfl⟩ : syracuseStep 863127 = 1294691) B1294691
theorem B863147 : Blo 860564 863147 := bstep (se 1 (by rfl) ⟨647360, by rfl⟩ : syracuseStep 863147 = 1294721) B1294721
theorem B863159 : Blo 860564 863159 := bstep (se 1 (by rfl) ⟨647369, by rfl⟩ : syracuseStep 863159 = 1294739) B1294739
theorem B863179 : Blo 860564 863179 := bstep (se 1 (by rfl) ⟨647384, by rfl⟩ : syracuseStep 863179 = 1294769) B1294769
theorem B863191 : Blo 860564 863191 := bstep (se 1 (by rfl) ⟨647393, by rfl⟩ : syracuseStep 863191 = 1294787) B1294787
theorem B863211 : Blo 860564 863211 := bstep (se 1 (by rfl) ⟨647408, by rfl⟩ : syracuseStep 863211 = 1294817) B1294817
theorem B863223 : Blo 860564 863223 := bstep (se 1 (by rfl) ⟨647417, by rfl⟩ : syracuseStep 863223 = 1294835) B1294835
theorem B1846273 : Blo 860564 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B863243 : Blo 860564 863243 := bstep (se 1 (by rfl) ⟨647432, by rfl⟩ : syracuseStep 863243 = 1294865) B1294865
theorem B1092619 : Blo 860564 1092619 := bstep (se 1 (by rfl) ⟨819464, by rfl⟩ : syracuseStep 1092619 = 1638929) B1638929
theorem B1453079 : Blo 860564 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B863255 : Blo 860564 863255 := bstep (se 1 (by rfl) ⟨647441, by rfl⟩ : syracuseStep 863255 = 1294883) B1294883
theorem B863275 : Blo 860564 863275 := bstep (se 1 (by rfl) ⟨647456, by rfl⟩ : syracuseStep 863275 = 1294913) B1294913
theorem B863287 : Blo 860564 863287 := bstep (se 1 (by rfl) ⟨647465, by rfl⟩ : syracuseStep 863287 = 1294931) B1294931
theorem B863307 : Blo 860564 863307 := bstep (se 1 (by rfl) ⟨647480, by rfl⟩ : syracuseStep 863307 = 1294961) B1294961
theorem B863319 : Blo 860564 863319 := bstep (se 1 (by rfl) ⟨647489, by rfl⟩ : syracuseStep 863319 = 1294979) B1294979
theorem B1944665 : Blo 860564 1944665 := bstep (se 2 (by rfl) ⟨729249, by rfl⟩ : syracuseStep 1944665 = 1458499) B1458499
theorem B863339 : Blo 860564 863339 := bstep (se 1 (by rfl) ⟨647504, by rfl⟩ : syracuseStep 863339 = 1295009) B1295009
theorem B863351 : Blo 860564 863351 := bstep (se 1 (by rfl) ⟨647513, by rfl⟩ : syracuseStep 863351 = 1295027) B1295027
theorem B863371 : Blo 860564 863371 := bstep (se 1 (by rfl) ⟨647528, by rfl⟩ : syracuseStep 863371 = 1295057) B1295057
theorem B1453207 : Blo 860564 1453207 := bstep (se 1 (by rfl) ⟨1089905, by rfl⟩ : syracuseStep 1453207 = 2179811) B2179811
theorem B863383 : Blo 860564 863383 := bstep (se 1 (by rfl) ⟨647537, by rfl⟩ : syracuseStep 863383 = 1295075) B1295075
theorem B863403 : Blo 860564 863403 := bstep (se 1 (by rfl) ⟨647552, by rfl⟩ : syracuseStep 863403 = 1295105) B1295105
theorem B1944755 : Blo 860564 1944755 := bstep (se 1 (by rfl) ⟨1458566, by rfl⟩ : syracuseStep 1944755 = 2917133) B2917133
theorem B863415 : Blo 860564 863415 := bstep (se 1 (by rfl) ⟨647561, by rfl⟩ : syracuseStep 863415 = 1295123) B1295123
theorem B1748171 : Blo 860564 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B863435 : Blo 860564 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B863447 : Blo 860564 863447 := bstep (se 1 (by rfl) ⟨647585, by rfl⟩ : syracuseStep 863447 = 1295171) B1295171
theorem B1944791 : Blo 860564 1944791 := bstep (se 1 (by rfl) ⟨1458593, by rfl⟩ : syracuseStep 1944791 = 2917187) B2917187
theorem B4369625 : Blo 860564 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B863467 : Blo 860564 863467 := bstep (se 1 (by rfl) ⟨647600, by rfl⟩ : syracuseStep 863467 = 1295201) B1295201
theorem B863479 : Blo 860564 863479 := bstep (se 1 (by rfl) ⟨647609, by rfl⟩ : syracuseStep 863479 = 1295219) B1295219
theorem B863499 : Blo 860564 863499 := bstep (se 1 (by rfl) ⟨647624, by rfl⟩ : syracuseStep 863499 = 1295249) B1295249
theorem B863511 : Blo 860564 863511 := bstep (se 1 (by rfl) ⟨647633, by rfl⟩ : syracuseStep 863511 = 1295267) B1295267
theorem B863531 : Blo 860564 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B863543 : Blo 860564 863543 := bstep (se 1 (by rfl) ⟨647657, by rfl⟩ : syracuseStep 863543 = 1295315) B1295315
theorem B4664641 : Blo 860564 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B3681611 : Blo 860564 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B863563 : Blo 860564 863563 := bstep (se 1 (by rfl) ⟨647672, by rfl⟩ : syracuseStep 863563 = 1295345) B1295345
theorem B863575 : Blo 860564 863575 := bstep (se 1 (by rfl) ⟨647681, by rfl⟩ : syracuseStep 863575 = 1295363) B1295363
theorem B863595 : Blo 860564 863595 := bstep (se 1 (by rfl) ⟨647696, by rfl⟩ : syracuseStep 863595 = 1295393) B1295393
theorem B863607 : Blo 860564 863607 := bstep (se 1 (by rfl) ⟨647705, by rfl⟩ : syracuseStep 863607 = 1295411) B1295411
theorem B863627 : Blo 860564 863627 := bstep (se 1 (by rfl) ⟨647720, by rfl⟩ : syracuseStep 863627 = 1295441) B1295441
theorem B1944971 : Blo 860564 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B863639 : Blo 860564 863639 := bstep (se 1 (by rfl) ⟨647729, by rfl⟩ : syracuseStep 863639 = 1295459) B1295459
theorem B863659 : Blo 860564 863659 := bstep (se 1 (by rfl) ⟨647744, by rfl⟩ : syracuseStep 863659 = 1295489) B1295489
theorem B863671 : Blo 860564 863671 := bstep (se 1 (by rfl) ⟨647753, by rfl⟩ : syracuseStep 863671 = 1295507) B1295507
theorem B1945025 : Blo 860564 1945025 := bstep (se 2 (by rfl) ⟨729384, by rfl⟩ : syracuseStep 1945025 = 1458769) B1458769
theorem B863691 : Blo 860564 863691 := bstep (se 1 (by rfl) ⟨647768, by rfl⟩ : syracuseStep 863691 = 1295537) B1295537
theorem B863703 : Blo 860564 863703 := bstep (se 1 (by rfl) ⟨647777, by rfl⟩ : syracuseStep 863703 = 1295555) B1295555
theorem B863723 : Blo 860564 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B863735 : Blo 860564 863735 := bstep (se 1 (by rfl) ⟨647801, by rfl⟩ : syracuseStep 863735 = 1295603) B1295603
theorem B863755 : Blo 860564 863755 := bstep (se 1 (by rfl) ⟨647816, by rfl⟩ : syracuseStep 863755 = 1295633) B1295633
theorem B863767 : Blo 860564 863767 := bstep (se 1 (by rfl) ⟨647825, by rfl⟩ : syracuseStep 863767 = 1295651) B1295651
theorem B863787 : Blo 860564 863787 := bstep (se 1 (by rfl) ⟨647840, by rfl⟩ : syracuseStep 863787 = 1295681) B1295681
theorem B863799 : Blo 860564 863799 := bstep (se 1 (by rfl) ⟨647849, by rfl⟩ : syracuseStep 863799 = 1295699) B1295699
theorem B863819 : Blo 860564 863819 := bstep (se 1 (by rfl) ⟨647864, by rfl⟩ : syracuseStep 863819 = 1295729) B1295729
theorem B863831 : Blo 860564 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B863851 : Blo 860564 863851 := bstep (se 1 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 863851 = 1295777) B1295777
theorem B863863 : Blo 860564 863863 := bstep (se 1 (by rfl) ⟨647897, by rfl⟩ : syracuseStep 863863 = 1295795) B1295795
theorem B863883 : Blo 860564 863883 := bstep (se 1 (by rfl) ⟨647912, by rfl⟩ : syracuseStep 863883 = 1295825) B1295825
theorem B863895 : Blo 860564 863895 := bstep (se 1 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 863895 = 1295843) B1295843
theorem B1945241 : Blo 860564 1945241 := bstep (se 2 (by rfl) ⟨729465, by rfl⟩ : syracuseStep 1945241 = 1458931) B1458931
theorem B863915 : Blo 860564 863915 := bstep (se 1 (by rfl) ⟨647936, by rfl⟩ : syracuseStep 863915 = 1295873) B1295873
theorem B863927 : Blo 860564 863927 := bstep (se 1 (by rfl) ⟨647945, by rfl⟩ : syracuseStep 863927 = 1295891) B1295891
theorem B863947 : Blo 860564 863947 := bstep (se 1 (by rfl) ⟨647960, by rfl⟩ : syracuseStep 863947 = 1295921) B1295921
theorem B863959 : Blo 860564 863959 := bstep (se 1 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 863959 = 1295939) B1295939
theorem B863979 : Blo 860564 863979 := bstep (se 1 (by rfl) ⟨647984, by rfl⟩ : syracuseStep 863979 = 1295969) B1295969
theorem B863991 : Blo 860564 863991 := bstep (se 1 (by rfl) ⟨647993, by rfl⟩ : syracuseStep 863991 = 1295987) B1295987
theorem B1453835 : Blo 860564 1453835 := bstep (se 1 (by rfl) ⟨1090376, by rfl⟩ : syracuseStep 1453835 = 2180753) B2180753
theorem B864011 : Blo 860564 864011 := bstep (se 1 (by rfl) ⟨648008, by rfl⟩ : syracuseStep 864011 = 1296017) B1296017
theorem B864023 : Blo 860564 864023 := bstep (se 1 (by rfl) ⟨648017, by rfl⟩ : syracuseStep 864023 = 1296035) B1296035
theorem B864043 : Blo 860564 864043 := bstep (se 1 (by rfl) ⟨648032, by rfl⟩ : syracuseStep 864043 = 1296065) B1296065
theorem B864055 : Blo 860564 864055 := bstep (se 1 (by rfl) ⟨648041, by rfl⟩ : syracuseStep 864055 = 1296083) B1296083
theorem B864075 : Blo 860564 864075 := bstep (se 1 (by rfl) ⟨648056, by rfl⟩ : syracuseStep 864075 = 1296113) B1296113
theorem B864087 : Blo 860564 864087 := bstep (se 1 (by rfl) ⟨648065, by rfl⟩ : syracuseStep 864087 = 1296131) B1296131
theorem B864107 : Blo 860564 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B864119 : Blo 860564 864119 := bstep (se 1 (by rfl) ⟨648089, by rfl⟩ : syracuseStep 864119 = 1296179) B1296179
theorem B1453963 : Blo 860564 1453963 := bstep (se 1 (by rfl) ⟨1090472, by rfl⟩ : syracuseStep 1453963 = 2180945) B2180945
theorem B864139 : Blo 860564 864139 := bstep (se 1 (by rfl) ⟨648104, by rfl⟩ : syracuseStep 864139 = 1296209) B1296209
theorem B864151 : Blo 860564 864151 := bstep (se 1 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 864151 = 1296227) B1296227
theorem B864171 : Blo 860564 864171 := bstep (se 1 (by rfl) ⟨648128, by rfl⟩ : syracuseStep 864171 = 1296257) B1296257
theorem B864183 : Blo 860564 864183 := bstep (se 1 (by rfl) ⟨648137, by rfl⟩ : syracuseStep 864183 = 1296275) B1296275
theorem B864203 : Blo 860564 864203 := bstep (se 1 (by rfl) ⟨648152, by rfl⟩ : syracuseStep 864203 = 1296305) B1296305
theorem B1552343 : Blo 860564 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1093591 : Blo 860564 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B864215 : Blo 860564 864215 := bstep (se 1 (by rfl) ⟨648161, by rfl⟩ : syracuseStep 864215 = 1296323) B1296323
theorem B864235 : Blo 860564 864235 := bstep (se 1 (by rfl) ⟨648176, by rfl⟩ : syracuseStep 864235 = 1296353) B1296353
theorem B864247 : Blo 860564 864247 := bstep (se 1 (by rfl) ⟨648185, by rfl⟩ : syracuseStep 864247 = 1296371) B1296371
theorem B864267 : Blo 860564 864267 := bstep (se 1 (by rfl) ⟨648200, by rfl⟩ : syracuseStep 864267 = 1296401) B1296401
theorem B864279 : Blo 860564 864279 := bstep (se 1 (by rfl) ⟨648209, by rfl⟩ : syracuseStep 864279 = 1296419) B1296419
theorem B1454105 : Blo 860564 1454105 := bstep (se 2 (by rfl) ⟨545289, by rfl⟩ : syracuseStep 1454105 = 1090579) B1090579
theorem B864299 : Blo 860564 864299 := bstep (se 1 (by rfl) ⟨648224, by rfl⟩ : syracuseStep 864299 = 1296449) B1296449
theorem B864311 : Blo 860564 864311 := bstep (se 1 (by rfl) ⟨648233, by rfl⟩ : syracuseStep 864311 = 1296467) B1296467
theorem B1552459 : Blo 860564 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B35926091 : Blo 860564 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B864331 : Blo 860564 864331 := bstep (se 1 (by rfl) ⟨648248, by rfl⟩ : syracuseStep 864331 = 1296497) B1296497
theorem B864343 : Blo 860564 864343 := bstep (se 1 (by rfl) ⟨648257, by rfl⟩ : syracuseStep 864343 = 1296515) B1296515
theorem B864363 : Blo 860564 864363 := bstep (se 1 (by rfl) ⟨648272, by rfl⟩ : syracuseStep 864363 = 1296545) B1296545
theorem B864375 : Blo 860564 864375 := bstep (se 1 (by rfl) ⟨648281, by rfl⟩ : syracuseStep 864375 = 1296563) B1296563
theorem B864395 : Blo 860564 864395 := bstep (se 1 (by rfl) ⟨648296, by rfl⟩ : syracuseStep 864395 = 1296593) B1296593
theorem B864407 : Blo 860564 864407 := bstep (se 1 (by rfl) ⟨648305, by rfl⟩ : syracuseStep 864407 = 1296611) B1296611
theorem B1454233 : Blo 860564 1454233 := bstep (se 2 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 1454233 = 1090675) B1090675
theorem B864427 : Blo 860564 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B864439 : Blo 860564 864439 := bstep (se 1 (by rfl) ⟨648329, by rfl⟩ : syracuseStep 864439 = 1296659) B1296659
theorem B864459 : Blo 860564 864459 := bstep (se 1 (by rfl) ⟨648344, by rfl⟩ : syracuseStep 864459 = 1296689) B1296689
theorem B864471 : Blo 860564 864471 := bstep (se 1 (by rfl) ⟨648353, by rfl⟩ : syracuseStep 864471 = 1296707) B1296707
theorem B864491 : Blo 860564 864491 := bstep (se 1 (by rfl) ⟨648368, by rfl⟩ : syracuseStep 864491 = 1296737) B1296737
theorem B864503 : Blo 860564 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B864523 : Blo 860564 864523 := bstep (se 1 (by rfl) ⟨648392, by rfl⟩ : syracuseStep 864523 = 1296785) B1296785
theorem B864535 : Blo 860564 864535 := bstep (se 1 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 864535 = 1296803) B1296803
theorem B864555 : Blo 860564 864555 := bstep (se 1 (by rfl) ⟨648416, by rfl⟩ : syracuseStep 864555 = 1296833) B1296833
theorem B1749323 : Blo 860564 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B1290905 : Blo 860564 1290905 := bstep (se 2 (by rfl) ⟨484089, by rfl⟩ : syracuseStep 1290905 = 968179) B968179
theorem B8303309 : Blo 860564 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B1454807 : Blo 860564 1454807 := bstep (se 1 (by rfl) ⟨1091105, by rfl⟩ : syracuseStep 1454807 = 2182211) B2182211
theorem B1291019 : Blo 860564 1291019 := bstep (se 1 (by rfl) ⟨968264, by rfl⟩ : syracuseStep 1291019 = 1936529) B1936529
theorem B1291031 : Blo 860564 1291031 := bstep (se 1 (by rfl) ⟨968273, by rfl⟩ : syracuseStep 1291031 = 1936547) B1936547
theorem B4371245 : Blo 860564 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B1422155 : Blo 860564 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1454935 : Blo 860564 1454935 := bstep (se 1 (by rfl) ⟨1091201, by rfl⟩ : syracuseStep 1454935 = 2182403) B2182403
theorem B1291097 : Blo 860564 1291097 := bstep (se 2 (by rfl) ⟨484161, by rfl⟩ : syracuseStep 1291097 = 968323) B968323
theorem B1291211 : Blo 860564 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1291223 : Blo 860564 1291223 := bstep (se 1 (by rfl) ⟨968417, by rfl⟩ : syracuseStep 1291223 = 1936835) B1936835
theorem B1291289 : Blo 860564 1291289 := bstep (se 2 (by rfl) ⟨484233, by rfl⟩ : syracuseStep 1291289 = 968467) B968467
theorem B1291403 : Blo 860564 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B1291415 : Blo 860564 1291415 := bstep (se 1 (by rfl) ⟨968561, by rfl⟩ : syracuseStep 1291415 = 1937123) B1937123
theorem B1291481 : Blo 860564 1291481 := bstep (se 2 (by rfl) ⟨484305, by rfl⟩ : syracuseStep 1291481 = 968611) B968611
theorem B1225945 : Blo 860564 1225945 := bstep (se 2 (by rfl) ⟨459729, by rfl⟩ : syracuseStep 1225945 = 919459) B919459
theorem B1750337 : Blo 860564 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B1291595 : Blo 860564 1291595 := bstep (se 1 (by rfl) ⟨968696, by rfl⟩ : syracuseStep 1291595 = 1937393) B1937393
theorem B1291607 : Blo 860564 1291607 := bstep (se 1 (by rfl) ⟨968705, by rfl⟩ : syracuseStep 1291607 = 1937411) B1937411
theorem B1291673 : Blo 860564 1291673 := bstep (se 2 (by rfl) ⟨484377, by rfl⟩ : syracuseStep 1291673 = 968755) B968755
theorem B1553843 : Blo 860564 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B4208051 : Blo 860564 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B1455563 : Blo 860564 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B1291787 : Blo 860564 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B1291799 : Blo 860564 1291799 := bstep (se 1 (by rfl) ⟨968849, by rfl⟩ : syracuseStep 1291799 = 1937699) B1937699
theorem B4142657 : Blo 860564 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B1455691 : Blo 860564 1455691 := bstep (se 1 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 1455691 = 2183537) B2183537
theorem B1291865 : Blo 860564 1291865 := bstep (se 2 (by rfl) ⟨484449, by rfl⟩ : syracuseStep 1291865 = 968899) B968899
theorem B11941507 : Blo 860564 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B2766487 : Blo 860564 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1291979 : Blo 860564 1291979 := bstep (se 1 (by rfl) ⟨968984, by rfl⟩ : syracuseStep 1291979 = 1937969) B1937969
theorem B7354061 : Blo 860564 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B1291991 : Blo 860564 1291991 := bstep (se 1 (by rfl) ⟨968993, by rfl⟩ : syracuseStep 1291991 = 1937987) B1937987
theorem B1455833 : Blo 860564 1455833 := bstep (se 2 (by rfl) ⟨545937, by rfl⟩ : syracuseStep 1455833 = 1091875) B1091875
theorem B3978973 : Blo 860564 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B1292057 : Blo 860564 1292057 := bstep (se 2 (by rfl) ⟨484521, by rfl⟩ : syracuseStep 1292057 = 969043) B969043
theorem B1455961 : Blo 860564 1455961 := bstep (se 2 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 1455961 = 1091971) B1091971
theorem B1292171 : Blo 860564 1292171 := bstep (se 1 (by rfl) ⟨969128, by rfl⟩ : syracuseStep 1292171 = 1938257) B1938257
theorem B1292183 : Blo 860564 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B3684275 : Blo 860564 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B1292249 : Blo 860564 1292249 := bstep (se 2 (by rfl) ⟨484593, by rfl⟩ : syracuseStep 1292249 = 969187) B969187
theorem B1292363 : Blo 860564 1292363 := bstep (se 1 (by rfl) ⟨969272, by rfl⟩ : syracuseStep 1292363 = 1938545) B1938545
theorem B1292375 : Blo 860564 1292375 := bstep (se 1 (by rfl) ⟨969281, by rfl⟩ : syracuseStep 1292375 = 1938563) B1938563
theorem B1226839 : Blo 860564 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B2209943 : Blo 860564 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1292441 : Blo 860564 1292441 := bstep (se 2 (by rfl) ⟨484665, by rfl⟩ : syracuseStep 1292441 = 969331) B969331
theorem B2767051 : Blo 860564 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B1292555 : Blo 860564 1292555 := bstep (se 1 (by rfl) ⟨969416, by rfl⟩ : syracuseStep 1292555 = 1938833) B1938833
theorem B1292567 : Blo 860564 1292567 := bstep (se 1 (by rfl) ⟨969425, by rfl⟩ : syracuseStep 1292567 = 1938851) B1938851
theorem B1292633 : Blo 860564 1292633 := bstep (se 2 (by rfl) ⟨484737, by rfl⟩ : syracuseStep 1292633 = 969475) B969475
theorem B2767193 : Blo 860564 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1554817 : Blo 860564 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B1456535 : Blo 860564 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B1292747 : Blo 860564 1292747 := bstep (se 1 (by rfl) ⟨969560, by rfl⟩ : syracuseStep 1292747 = 1939121) B1939121
theorem B1292759 : Blo 860564 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B1456663 : Blo 860564 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B1292825 : Blo 860564 1292825 := bstep (se 2 (by rfl) ⟨484809, by rfl⟩ : syracuseStep 1292825 = 969619) B969619
theorem B1292939 : Blo 860564 1292939 := bstep (se 1 (by rfl) ⟨969704, by rfl⟩ : syracuseStep 1292939 = 1939409) B1939409
theorem B1227403 : Blo 860564 1227403 := bstep (se 1 (by rfl) ⟨920552, by rfl⟩ : syracuseStep 1227403 = 1841105) B1841105
theorem B1292951 : Blo 860564 1292951 := bstep (se 1 (by rfl) ⟨969713, by rfl⟩ : syracuseStep 1292951 = 1939427) B1939427
theorem B1293017 : Blo 860564 1293017 := bstep (se 2 (by rfl) ⟨484881, by rfl⟩ : syracuseStep 1293017 = 969763) B969763
theorem B7092953 : Blo 860564 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B1293131 : Blo 860564 1293131 := bstep (se 1 (by rfl) ⟨969848, by rfl⟩ : syracuseStep 1293131 = 1939697) B1939697
theorem B1293143 : Blo 860564 1293143 := bstep (se 1 (by rfl) ⟨969857, by rfl⟩ : syracuseStep 1293143 = 1939715) B1939715
theorem B1293209 : Blo 860564 1293209 := bstep (se 2 (by rfl) ⟨484953, by rfl⟩ : syracuseStep 1293209 = 969907) B969907
theorem B1555457 : Blo 860564 1555457 := bstep (se 2 (by rfl) ⟨583296, by rfl⟩ : syracuseStep 1555457 = 1166593) B1166593
theorem B1293323 : Blo 860564 1293323 := bstep (se 1 (by rfl) ⟨969992, by rfl⟩ : syracuseStep 1293323 = 1939985) B1939985
theorem B1293335 : Blo 860564 1293335 := bstep (se 1 (by rfl) ⟨970001, by rfl⟩ : syracuseStep 1293335 = 1940003) B1940003
theorem B1293401 : Blo 860564 1293401 := bstep (se 2 (by rfl) ⟨485025, by rfl⟩ : syracuseStep 1293401 = 970051) B970051
theorem B1457291 : Blo 860564 1457291 := bstep (se 1 (by rfl) ⟨1092968, by rfl⟩ : syracuseStep 1457291 = 2185937) B2185937
theorem B1293515 : Blo 860564 1293515 := bstep (se 1 (by rfl) ⟨970136, by rfl⟩ : syracuseStep 1293515 = 1940273) B1940273
theorem B1293527 : Blo 860564 1293527 := bstep (se 1 (by rfl) ⟨970145, by rfl⟩ : syracuseStep 1293527 = 1940291) B1940291
theorem B1457419 : Blo 860564 1457419 := bstep (se 1 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 1457419 = 2186129) B2186129
theorem B1293593 : Blo 860564 1293593 := bstep (se 2 (by rfl) ⟨485097, by rfl⟩ : syracuseStep 1293593 = 970195) B970195
theorem B3685763 : Blo 860564 3685763 := bstep (se 1 (by rfl) ⟨2764322, by rfl⟩ : syracuseStep 3685763 = 5528645) B5528645
theorem B1293707 : Blo 860564 1293707 := bstep (se 1 (by rfl) ⟨970280, by rfl⟩ : syracuseStep 1293707 = 1940561) B1940561
theorem B1293719 : Blo 860564 1293719 := bstep (se 1 (by rfl) ⟨970289, by rfl⟩ : syracuseStep 1293719 = 1940579) B1940579
theorem B1457561 : Blo 860564 1457561 := bstep (se 2 (by rfl) ⟨546585, by rfl⟩ : syracuseStep 1457561 = 1093171) B1093171
theorem B6995405 : Blo 860564 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B1293785 : Blo 860564 1293785 := bstep (se 2 (by rfl) ⟨485169, by rfl⟩ : syracuseStep 1293785 = 970339) B970339
theorem B1457689 : Blo 860564 1457689 := bstep (se 2 (by rfl) ⟨546633, by rfl⟩ : syracuseStep 1457689 = 1093267) B1093267
theorem B4734509 : Blo 860564 4734509 := bstep (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) B1775441
theorem B2768435 : Blo 860564 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B1293899 : Blo 860564 1293899 := bstep (se 1 (by rfl) ⟨970424, by rfl⟩ : syracuseStep 1293899 = 1940849) B1940849
theorem B1293911 : Blo 860564 1293911 := bstep (se 1 (by rfl) ⟨970433, by rfl⟩ : syracuseStep 1293911 = 1940867) B1940867
theorem B1293977 : Blo 860564 1293977 := bstep (se 2 (by rfl) ⟨485241, by rfl⟩ : syracuseStep 1293977 = 970483) B970483
theorem B2211545 : Blo 860564 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B1294091 : Blo 860564 1294091 := bstep (se 1 (by rfl) ⟨970568, by rfl⟩ : syracuseStep 1294091 = 1941137) B1941137
theorem B2178839 : Blo 860564 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B1294103 : Blo 860564 1294103 := bstep (se 1 (by rfl) ⟨970577, by rfl⟩ : syracuseStep 1294103 = 1941155) B1941155
theorem B1294169 : Blo 860564 1294169 := bstep (se 2 (by rfl) ⟨485313, by rfl⟩ : syracuseStep 1294169 = 970627) B970627
theorem B2768833 : Blo 860564 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B1294283 : Blo 860564 1294283 := bstep (se 1 (by rfl) ⟨970712, by rfl⟩ : syracuseStep 1294283 = 1941425) B1941425
theorem B1294295 : Blo 860564 1294295 := bstep (se 1 (by rfl) ⟨970721, by rfl⟩ : syracuseStep 1294295 = 1941443) B1941443
theorem B1294361 : Blo 860564 1294361 := bstep (se 2 (by rfl) ⟨485385, by rfl⟩ : syracuseStep 1294361 = 970771) B970771
theorem B17678411 : Blo 860564 17678411 := bstep (se 1 (by rfl) ⟨13258808, by rfl⟩ : syracuseStep 17678411 = 26517617) B26517617
theorem B1458263 : Blo 860564 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B1228889 : Blo 860564 1228889 := bstep (se 2 (by rfl) ⟨460833, by rfl⟩ : syracuseStep 1228889 = 921667) B921667
theorem B6635621 : Blo 860564 6635621 := bstep (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) B1244179
theorem B1294475 : Blo 860564 1294475 := bstep (se 1 (by rfl) ⟨970856, by rfl⟩ : syracuseStep 1294475 = 1941713) B1941713
theorem B1294487 : Blo 860564 1294487 := bstep (se 1 (by rfl) ⟨970865, by rfl⟩ : syracuseStep 1294487 = 1941731) B1941731
theorem B1458391 : Blo 860564 1458391 := bstep (se 1 (by rfl) ⟨1093793, by rfl⟩ : syracuseStep 1458391 = 2187587) B2187587
theorem B1294553 : Blo 860564 1294553 := bstep (se 2 (by rfl) ⟨485457, by rfl⟩ : syracuseStep 1294553 = 970915) B970915
theorem B8274241 : Blo 860564 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B1294667 : Blo 860564 1294667 := bstep (se 1 (by rfl) ⟨971000, by rfl⟩ : syracuseStep 1294667 = 1942001) B1942001
theorem B1294679 : Blo 860564 1294679 := bstep (se 1 (by rfl) ⟨971009, by rfl⟩ : syracuseStep 1294679 = 1942019) B1942019
theorem B1294745 : Blo 860564 1294745 := bstep (se 2 (by rfl) ⟨485529, by rfl⟩ : syracuseStep 1294745 = 971059) B971059
theorem B2179507 : Blo 860564 2179507 := bstep (se 1 (by rfl) ⟨1634630, by rfl⟩ : syracuseStep 2179507 = 3269261) B3269261
theorem B1294859 : Blo 860564 1294859 := bstep (se 1 (by rfl) ⟨971144, by rfl⟩ : syracuseStep 1294859 = 1942289) B1942289
theorem B1294871 : Blo 860564 1294871 := bstep (se 1 (by rfl) ⟨971153, by rfl⟩ : syracuseStep 1294871 = 1942307) B1942307
theorem B9847331 : Blo 860564 9847331 := bstep (se 1 (by rfl) ⟨7385498, by rfl⟩ : syracuseStep 9847331 = 14770997) B14770997
theorem B2179649 : Blo 860564 2179649 := bstep (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) B1634737
theorem B1294937 : Blo 860564 1294937 := bstep (se 2 (by rfl) ⟨485601, by rfl⟩ : syracuseStep 1294937 = 971203) B971203
theorem B4375133 : Blo 860564 4375133 := bstep (se 3 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 4375133 = 1640675) B1640675
theorem B1295051 : Blo 860564 1295051 := bstep (se 1 (by rfl) ⟨971288, by rfl⟩ : syracuseStep 1295051 = 1942577) B1942577
theorem B1295063 : Blo 860564 1295063 := bstep (se 1 (by rfl) ⟨971297, by rfl⟩ : syracuseStep 1295063 = 1942595) B1942595
theorem B1229527 : Blo 860564 1229527 := bstep (se 1 (by rfl) ⟨922145, by rfl⟩ : syracuseStep 1229527 = 1844291) B1844291
theorem B1295129 : Blo 860564 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B1295243 : Blo 860564 1295243 := bstep (se 1 (by rfl) ⟨971432, by rfl⟩ : syracuseStep 1295243 = 1942865) B1942865
theorem B1295255 : Blo 860564 1295255 := bstep (se 1 (by rfl) ⟨971441, by rfl⟩ : syracuseStep 1295255 = 1942883) B1942883
theorem B1295321 : Blo 860564 1295321 := bstep (se 2 (by rfl) ⟨485745, by rfl⟩ : syracuseStep 1295321 = 971491) B971491
theorem B1557505 : Blo 860564 1557505 := bstep (se 2 (by rfl) ⟨584064, by rfl⟩ : syracuseStep 1557505 = 1168129) B1168129
theorem B1295435 : Blo 860564 1295435 := bstep (se 1 (by rfl) ⟨971576, by rfl⟩ : syracuseStep 1295435 = 1943153) B1943153
theorem B1295447 : Blo 860564 1295447 := bstep (se 1 (by rfl) ⟨971585, by rfl⟩ : syracuseStep 1295447 = 1943171) B1943171
theorem B1295513 : Blo 860564 1295513 := bstep (se 2 (by rfl) ⟨485817, by rfl⟩ : syracuseStep 1295513 = 971635) B971635
theorem B1557721 : Blo 860564 1557721 := bstep (se 2 (by rfl) ⟨584145, by rfl⟩ : syracuseStep 1557721 = 1168291) B1168291
theorem B1295627 : Blo 860564 1295627 := bstep (se 1 (by rfl) ⟨971720, by rfl⟩ : syracuseStep 1295627 = 1943441) B1943441
theorem B1295639 : Blo 860564 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B1295705 : Blo 860564 1295705 := bstep (se 2 (by rfl) ⟨485889, by rfl⟩ : syracuseStep 1295705 = 971779) B971779
theorem B1230233 : Blo 860564 1230233 := bstep (se 2 (by rfl) ⟨461337, by rfl⟩ : syracuseStep 1230233 = 922675) B922675
theorem B1295819 : Blo 860564 1295819 := bstep (se 1 (by rfl) ⟨971864, by rfl⟩ : syracuseStep 1295819 = 1943729) B1943729
theorem B1295831 : Blo 860564 1295831 := bstep (se 1 (by rfl) ⟨971873, by rfl⟩ : syracuseStep 1295831 = 1943747) B1943747
theorem B1230347 : Blo 860564 1230347 := bstep (se 1 (by rfl) ⟨922760, by rfl⟩ : syracuseStep 1230347 = 1845521) B1845521
theorem B968215 : Blo 860564 968215 := bstep (se 1 (by rfl) ⟨726161, by rfl⟩ : syracuseStep 968215 = 1452323) B1452323
theorem B1295897 : Blo 860564 1295897 := bstep (se 2 (by rfl) ⟨485961, by rfl⟩ : syracuseStep 1295897 = 971923) B971923
theorem B3688001 : Blo 860564 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B1492619 : Blo 860564 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B1296011 : Blo 860564 1296011 := bstep (se 1 (by rfl) ⟨972008, by rfl⟩ : syracuseStep 1296011 = 1944017) B1944017
theorem B1296023 : Blo 860564 1296023 := bstep (se 1 (by rfl) ⟨972017, by rfl⟩ : syracuseStep 1296023 = 1944035) B1944035
theorem B968395 : Blo 860564 968395 := bstep (se 1 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 968395 = 1452593) B1452593
theorem B1296089 : Blo 860564 1296089 := bstep (se 2 (by rfl) ⟨486033, by rfl⟩ : syracuseStep 1296089 = 972067) B972067
theorem B2180915 : Blo 860564 2180915 := bstep (se 1 (by rfl) ⟨1635686, by rfl⟩ : syracuseStep 2180915 = 3271373) B3271373
theorem B968503 : Blo 860564 968503 := bstep (se 1 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 968503 = 1452755) B1452755
theorem B24889153 : Blo 860564 24889153 := bstep (se 2 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 24889153 = 18666865) B18666865
theorem B1296203 : Blo 860564 1296203 := bstep (se 1 (by rfl) ⟨972152, by rfl⟩ : syracuseStep 1296203 = 1944305) B1944305
theorem B1296215 : Blo 860564 1296215 := bstep (se 1 (by rfl) ⟨972161, by rfl⟩ : syracuseStep 1296215 = 1944323) B1944323
theorem B1296281 : Blo 860564 1296281 := bstep (se 2 (by rfl) ⟨486105, by rfl⟩ : syracuseStep 1296281 = 972211) B972211
theorem B968683 : Blo 860564 968683 := bstep (se 1 (by rfl) ⟨726512, by rfl⟩ : syracuseStep 968683 = 1453025) B1453025
theorem B1296395 : Blo 860564 1296395 := bstep (se 1 (by rfl) ⟨972296, by rfl⟩ : syracuseStep 1296395 = 1944593) B1944593
theorem B1296407 : Blo 860564 1296407 := bstep (se 1 (by rfl) ⟨972305, by rfl⟩ : syracuseStep 1296407 = 1944611) B1944611
theorem B1230871 : Blo 860564 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B968791 : Blo 860564 968791 := bstep (se 1 (by rfl) ⟨726593, by rfl⟩ : syracuseStep 968791 = 1453187) B1453187
theorem B1296473 : Blo 860564 1296473 := bstep (se 2 (by rfl) ⟨486177, by rfl⟩ : syracuseStep 1296473 = 972355) B972355
theorem B1296587 : Blo 860564 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B1296599 : Blo 860564 1296599 := bstep (se 1 (by rfl) ⟨972449, by rfl⟩ : syracuseStep 1296599 = 1944899) B1944899
theorem B968971 : Blo 860564 968971 := bstep (se 1 (by rfl) ⟨726728, by rfl⟩ : syracuseStep 968971 = 1453457) B1453457
theorem B1296665 : Blo 860564 1296665 := bstep (se 2 (by rfl) ⟨486249, by rfl⟩ : syracuseStep 1296665 = 972499) B972499
theorem B2181451 : Blo 860564 2181451 := bstep (se 1 (by rfl) ⟨1636088, by rfl⟩ : syracuseStep 2181451 = 3272177) B3272177
theorem B969079 : Blo 860564 969079 := bstep (se 1 (by rfl) ⟨726809, by rfl⟩ : syracuseStep 969079 = 1453619) B1453619
theorem B1296779 : Blo 860564 1296779 := bstep (se 1 (by rfl) ⟨972584, by rfl⟩ : syracuseStep 1296779 = 1945169) B1945169
theorem B1296791 : Blo 860564 1296791 := bstep (se 1 (by rfl) ⟨972593, by rfl⟩ : syracuseStep 1296791 = 1945187) B1945187
theorem B1034699 : Blo 860564 1034699 := bstep (se 1 (by rfl) ⟨776024, by rfl⟩ : syracuseStep 1034699 = 1552049) B1552049
theorem B2181593 : Blo 860564 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B969259 : Blo 860564 969259 := bstep (se 1 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 969259 = 1453889) B1453889
theorem B969367 : Blo 860564 969367 := bstep (se 1 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 969367 = 1454051) B1454051
theorem B19942129 : Blo 860564 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B969547 : Blo 860564 969547 := bstep (se 1 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 969547 = 1454321) B1454321
theorem B969655 : Blo 860564 969655 := bstep (se 1 (by rfl) ⟨727241, by rfl⟩ : syracuseStep 969655 = 1454483) B1454483
theorem B3492887 : Blo 860564 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B969835 : Blo 860564 969835 := bstep (se 1 (by rfl) ⟨727376, by rfl⟩ : syracuseStep 969835 = 1454753) B1454753
theorem B3689675 : Blo 860564 3689675 := bstep (se 1 (by rfl) ⟨2767256, by rfl⟩ : syracuseStep 3689675 = 5534513) B5534513
theorem B969943 : Blo 860564 969943 := bstep (se 1 (by rfl) ⟨727457, by rfl⟩ : syracuseStep 969943 = 1454915) B1454915
theorem B2182423 : Blo 860564 2182423 := bstep (se 1 (by rfl) ⟨1636817, by rfl⟩ : syracuseStep 2182423 = 3273635) B3273635
theorem B6999371 : Blo 860564 6999371 := bstep (se 1 (by rfl) ⟨5249528, by rfl⟩ : syracuseStep 6999371 = 10499057) B10499057
theorem B970123 : Blo 860564 970123 := bstep (se 1 (by rfl) ⟨727592, by rfl⟩ : syracuseStep 970123 = 1455185) B1455185
theorem B970231 : Blo 860564 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B970411 : Blo 860564 970411 := bstep (se 1 (by rfl) ⟨727808, by rfl⟩ : syracuseStep 970411 = 1455617) B1455617
theorem B2182859 : Blo 860564 2182859 := bstep (se 1 (by rfl) ⟨1637144, by rfl⟩ : syracuseStep 2182859 = 3274289) B3274289
theorem B6541073 : Blo 860564 6541073 := bstep (se 2 (by rfl) ⟨2452902, by rfl⟩ : syracuseStep 6541073 = 4905805) B4905805
theorem B970519 : Blo 860564 970519 := bstep (se 1 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 970519 = 1455779) B1455779
theorem B16568165 : Blo 860564 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B970699 : Blo 860564 970699 := bstep (se 1 (by rfl) ⟨728024, by rfl⟩ : syracuseStep 970699 = 1456049) B1456049
theorem B3690461 : Blo 860564 3690461 := bstep (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) B1383923
theorem B970807 : Blo 860564 970807 := bstep (se 1 (by rfl) ⟨728105, by rfl⟩ : syracuseStep 970807 = 1456211) B1456211
theorem B2183233 : Blo 860564 2183233 := bstep (se 2 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 2183233 = 1637425) B1637425
theorem B5328989 : Blo 860564 5328989 := bstep (se 3 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 5328989 = 1998371) B1998371
theorem B970987 : Blo 860564 970987 := bstep (se 1 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 970987 = 1456481) B1456481
theorem B7000337 : Blo 860564 7000337 := bstep (se 2 (by rfl) ⟨2625126, by rfl⟩ : syracuseStep 7000337 = 5250253) B5250253
theorem B971095 : Blo 860564 971095 := bstep (se 1 (by rfl) ⟨728321, by rfl⟩ : syracuseStep 971095 = 1456643) B1456643
theorem B971275 : Blo 860564 971275 := bstep (se 1 (by rfl) ⟨728456, by rfl⟩ : syracuseStep 971275 = 1456913) B1456913
theorem B971383 : Blo 860564 971383 := bstep (se 1 (by rfl) ⟨728537, by rfl⟩ : syracuseStep 971383 = 1457075) B1457075
theorem B2183831 : Blo 860564 2183831 := bstep (se 1 (by rfl) ⟨1637873, by rfl⟩ : syracuseStep 2183831 = 3275747) B3275747
theorem B971563 : Blo 860564 971563 := bstep (se 1 (by rfl) ⟨728672, by rfl⟩ : syracuseStep 971563 = 1457345) B1457345
theorem B15717185 : Blo 860564 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B2904983 : Blo 860564 2904983 := bstep (se 1 (by rfl) ⟨2178737, by rfl⟩ : syracuseStep 2904983 = 4357475) B4357475
theorem B971671 : Blo 860564 971671 := bstep (se 1 (by rfl) ⟨728753, by rfl⟩ : syracuseStep 971671 = 1457507) B1457507
theorem B971851 : Blo 860564 971851 := bstep (se 1 (by rfl) ⟨728888, by rfl⟩ : syracuseStep 971851 = 1457777) B1457777
theorem B971959 : Blo 860564 971959 := bstep (se 1 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 971959 = 1457939) B1457939
theorem B1496279 : Blo 860564 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B3691793 : Blo 860564 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B972139 : Blo 860564 972139 := bstep (se 1 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 972139 = 1458209) B1458209
theorem B2905523 : Blo 860564 2905523 := bstep (se 1 (by rfl) ⟨2179142, by rfl⟩ : syracuseStep 2905523 = 4358285) B4358285
theorem B2184641 : Blo 860564 2184641 := bstep (se 2 (by rfl) ⟨819240, by rfl⟩ : syracuseStep 2184641 = 1638481) B1638481
theorem B972247 : Blo 860564 972247 := bstep (se 1 (by rfl) ⟨729185, by rfl⟩ : syracuseStep 972247 = 1458371) B1458371
theorem B6313477 : Blo 860564 6313477 := bstep (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) B1183777
theorem B972427 : Blo 860564 972427 := bstep (se 1 (by rfl) ⟨729320, by rfl⟩ : syracuseStep 972427 = 1458641) B1458641
theorem B2905793 : Blo 860564 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B972535 : Blo 860564 972535 := bstep (se 1 (by rfl) ⟨729401, by rfl⟩ : syracuseStep 972535 = 1458803) B1458803
theorem B6215575 : Blo 860564 6215575 := bstep (se 1 (by rfl) ⟨4661681, by rfl⟩ : syracuseStep 6215575 = 9323363) B9323363
theorem B2185177 : Blo 860564 2185177 := bstep (se 2 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 2185177 = 1638883) B1638883
theorem B1497163 : Blo 860564 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B6215831 : Blo 860564 6215831 := bstep (se 1 (by rfl) ⟨4661873, by rfl⟩ : syracuseStep 6215831 = 9323747) B9323747
theorem B2906333 : Blo 860564 2906333 := bstep (se 3 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 2906333 = 1089875) B1089875
theorem B4905623 : Blo 860564 4905623 := bstep (se 1 (by rfl) ⟨3679217, by rfl⟩ : syracuseStep 4905623 = 7358435) B7358435
theorem B4479667 : Blo 860564 4479667 := bstep (se 1 (by rfl) ⟨3359750, by rfl⟩ : syracuseStep 4479667 = 6719501) B6719501
theorem B3496925 : Blo 860564 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B2186291 : Blo 860564 2186291 := bstep (se 1 (by rfl) ⟨1639718, by rfl⟩ : syracuseStep 2186291 = 3279437) B3279437
theorem B3497219 : Blo 860564 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B2907467 : Blo 860564 2907467 := bstep (se 1 (by rfl) ⟨2180600, by rfl⟩ : syracuseStep 2907467 = 4361201) B4361201
theorem B2186585 : Blo 860564 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B3267971 : Blo 860564 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B3497347 : Blo 860564 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B3267985 : Blo 860564 3267985 := bstep (se 2 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 3267985 = 2450989) B2450989
theorem B6544961 : Blo 860564 6544961 := bstep (se 2 (by rfl) ⟨2454360, by rfl⟩ : syracuseStep 6544961 = 4908721) B4908721
theorem B2907737 : Blo 860564 2907737 := bstep (se 2 (by rfl) ⟨1090401, by rfl⟩ : syracuseStep 2907737 = 2180803) B2180803
theorem B5529181 : Blo 860564 5529181 := bstep (se 3 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 5529181 = 2073443) B2073443
theorem B18636419 : Blo 860564 18636419 := bstep (se 1 (by rfl) ⟨13977314, by rfl⟩ : syracuseStep 18636419 = 27954629) B27954629
theorem B3268289 : Blo 860564 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B1663001 : Blo 860564 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B7200919 : Blo 860564 7200919 := bstep (se 1 (by rfl) ⟨5400689, by rfl⟩ : syracuseStep 7200919 = 10801379) B10801379
theorem B3367133 : Blo 860564 3367133 := bstep (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) B1262675
theorem B2908439 : Blo 860564 2908439 := bstep (se 1 (by rfl) ⟨2181329, by rfl⟩ : syracuseStep 2908439 = 4362659) B4362659
theorem B3268957 : Blo 860564 3268957 := bstep (se 3 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 3268957 = 1225859) B1225859
theorem B4907537 : Blo 860564 4907537 := bstep (se 2 (by rfl) ⟨1840326, by rfl⟩ : syracuseStep 4907537 = 3680653) B3680653
theorem B2908979 : Blo 860564 2908979 := bstep (se 1 (by rfl) ⟨2181734, by rfl⟩ : syracuseStep 2908979 = 4363469) B4363469
theorem B2188235 : Blo 860564 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B2909249 : Blo 860564 2909249 := bstep (se 2 (by rfl) ⟨1090968, by rfl⟩ : syracuseStep 2909249 = 2181937) B2181937
theorem B3105985 : Blo 860564 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B6546905 : Blo 860564 6546905 := bstep (se 2 (by rfl) ⟨2455089, by rfl⟩ : syracuseStep 6546905 = 4910179) B4910179
theorem B9463331 : Blo 860564 9463331 := bstep (se 1 (by rfl) ⟨7097498, by rfl⟩ : syracuseStep 9463331 = 14194997) B14194997
theorem B3270233 : Blo 860564 3270233 := bstep (se 2 (by rfl) ⟨1226337, by rfl⟩ : syracuseStep 3270233 = 2452675) B2452675
theorem B2909789 : Blo 860564 2909789 := bstep (se 3 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 2909789 = 1091171) B1091171
theorem B2451161 : Blo 860564 2451161 := bstep (se 2 (by rfl) ⟨919185, by rfl⟩ : syracuseStep 2451161 = 1838371) B1838371
theorem B1107799 : Blo 860564 1107799 := bstep (se 1 (by rfl) ⟨830849, by rfl⟩ : syracuseStep 1107799 = 1661699) B1661699
theorem B3991697 : Blo 860564 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B21031285 : Blo 860564 21031285 := bstep (se 5 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 21031285 = 1971683) B1971683
theorem B2910923 : Blo 860564 2910923 := bstep (se 1 (by rfl) ⟨2183192, by rfl⟩ : syracuseStep 2910923 = 4366385) B4366385
theorem B55896803 : Blo 860564 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B2911193 : Blo 860564 2911193 := bstep (se 2 (by rfl) ⟨1091697, by rfl⟩ : syracuseStep 2911193 = 2183395) B2183395
theorem B3271859 : Blo 860564 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B3271873 : Blo 860564 3271873 := bstep (se 2 (by rfl) ⟨1226952, by rfl⟩ : syracuseStep 3271873 = 2453905) B2453905
theorem B3108061 : Blo 860564 3108061 := bstep (se 3 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 3108061 = 1165523) B1165523
theorem B2452801 : Blo 860564 2452801 := bstep (se 2 (by rfl) ⟨919800, by rfl⟩ : syracuseStep 2452801 = 1839601) B1839601
theorem B53013973 : Blo 860564 53013973 := bstep (se 7 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 53013973 = 1242515) B1242515
theorem B2911895 : Blo 860564 2911895 := bstep (se 1 (by rfl) ⟨2183921, by rfl⟩ : syracuseStep 2911895 = 4367843) B4367843
theorem B1634251 : Blo 860564 1634251 := bstep (se 1 (by rfl) ⟨1225688, by rfl⟩ : syracuseStep 1634251 = 2451377) B2451377
theorem B1634327 : Blo 860564 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B2912435 : Blo 860564 2912435 := bstep (se 1 (by rfl) ⟨2184326, by rfl⟩ : syracuseStep 2912435 = 4368653) B4368653
theorem B2912705 : Blo 860564 2912705 := bstep (se 2 (by rfl) ⟨1092264, by rfl⟩ : syracuseStep 2912705 = 2184529) B2184529
theorem B2945497 : Blo 860564 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B1634995 : Blo 860564 1634995 := bstep (se 1 (by rfl) ⟨1226246, by rfl⟩ : syracuseStep 1634995 = 2452493) B2452493
theorem B6550307 : Blo 860564 6550307 := bstep (se 1 (by rfl) ⟨4912730, by rfl⟩ : syracuseStep 6550307 = 9825461) B9825461
theorem B1635223 : Blo 860564 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B2454475 : Blo 860564 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B2913245 : Blo 860564 2913245 := bstep (se 3 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 2913245 = 1092467) B1092467
theorem B1635329 : Blo 860564 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B10515491 : Blo 860564 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B3273803 : Blo 860564 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B3273817 : Blo 860564 3273817 := bstep (se 2 (by rfl) ⟨1227681, by rfl⟩ : syracuseStep 3273817 = 2455363) B2455363
theorem B1635481 : Blo 860564 1635481 := bstep (se 2 (by rfl) ⟨613305, by rfl⟩ : syracuseStep 1635481 = 1226611) B1226611
theorem B1963225 : Blo 860564 1963225 := bstep (se 2 (by rfl) ⟨736209, by rfl⟩ : syracuseStep 1963225 = 1472419) B1472419
theorem B2454749 : Blo 860564 2454749 := bstep (se 3 (by rfl) ⟨460265, by rfl⟩ : syracuseStep 2454749 = 920531) B920531
theorem B3503837 : Blo 860564 3503837 := bstep (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) B1313939
theorem B4912913 : Blo 860564 4912913 := bstep (se 2 (by rfl) ⟨1842342, by rfl⟩ : syracuseStep 4912913 = 3684685) B3684685
theorem B1242955 : Blo 860564 1242955 := bstep (se 1 (by rfl) ⟨932216, by rfl⟩ : syracuseStep 1242955 = 1864433) B1864433
theorem B4257629 : Blo 860564 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B1963955 : Blo 860564 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B3274775 : Blo 860564 3274775 := bstep (se 1 (by rfl) ⟨2456081, by rfl⟩ : syracuseStep 3274775 = 4912163) B4912163
theorem B2914379 : Blo 860564 2914379 := bstep (se 1 (by rfl) ⟨2185784, by rfl⟩ : syracuseStep 2914379 = 4371569) B4371569
theorem B4913369 : Blo 860564 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B2914649 : Blo 860564 2914649 := bstep (se 2 (by rfl) ⟨1092993, by rfl⟩ : syracuseStep 2914649 = 2185987) B2185987
theorem B1636787 : Blo 860564 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1636939 : Blo 860564 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B3504971 : Blo 860564 3504971 := bstep (se 1 (by rfl) ⟨2628728, by rfl⟩ : syracuseStep 3504971 = 5257457) B5257457
theorem B1637273 : Blo 860564 1637273 := bstep (se 2 (by rfl) ⟨613977, by rfl⟩ : syracuseStep 1637273 = 1227955) B1227955
theorem B2915351 : Blo 860564 2915351 := bstep (se 1 (by rfl) ⟨2186513, by rfl⟩ : syracuseStep 2915351 = 4373027) B4373027
theorem B3931267 : Blo 860564 3931267 := bstep (se 1 (by rfl) ⟨2948450, by rfl⟩ : syracuseStep 3931267 = 5896901) B5896901
theorem B3112067 : Blo 860564 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B3276035 : Blo 860564 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B2457049 : Blo 860564 2457049 := bstep (se 2 (by rfl) ⟨921393, by rfl⟩ : syracuseStep 2457049 = 1842787) B1842787
theorem B37289443 : Blo 860564 37289443 := bstep (se 1 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 37289443 = 55934165) B55934165
theorem B1637911 : Blo 860564 1637911 := bstep (se 1 (by rfl) ⟨1228433, by rfl⟩ : syracuseStep 1637911 = 2456867) B2456867
theorem B9960995 : Blo 860564 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B2915891 : Blo 860564 2915891 := bstep (se 1 (by rfl) ⟨2186918, by rfl⟩ : syracuseStep 2915891 = 4373837) B4373837
theorem B2358877 : Blo 860564 2358877 := bstep (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) B884579
theorem B2916161 : Blo 860564 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B7372619 : Blo 860564 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B1245079 : Blo 860564 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B1638443 : Blo 860564 1638443 := bstep (se 1 (by rfl) ⟨1228832, by rfl⟩ : syracuseStep 1638443 = 2457665) B2457665
theorem B4423747 : Blo 860564 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B3277037 : Blo 860564 3277037 := bstep (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) B1228889
theorem B2916755 : Blo 860564 2916755 := bstep (se 1 (by rfl) ⟨2187566, by rfl⟩ : syracuseStep 2916755 = 4375133) B4375133
theorem B4358609 : Blo 860564 4358609 := bstep (se 2 (by rfl) ⟨1634478, by rfl⟩ : syracuseStep 4358609 = 3268957) B3268957
theorem B1311275 : Blo 860564 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B38404901 : Blo 860564 38404901 := bstep (se 4 (by rfl) ⟨3600459, by rfl⟩ : syracuseStep 38404901 = 7200919) B7200919
theorem B1180559 : Blo 860564 1180559 := bstep (se 1 (by rfl) ⟨885419, by rfl⟩ : syracuseStep 1180559 = 1770839) B1770839
theorem B1639369 : Blo 860564 1639369 := bstep (se 2 (by rfl) ⟨614763, by rfl⟩ : syracuseStep 1639369 = 1229527) B1229527
theorem B15762437 : Blo 860564 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B2458667 : Blo 860564 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B4916285 : Blo 860564 4916285 := bstep (se 3 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 4916285 = 1843607) B1843607
theorem B2360723 : Blo 860564 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B1640083 : Blo 860564 1640083 := bstep (se 1 (by rfl) ⟨1230062, by rfl⟩ : syracuseStep 1640083 = 2460125) B2460125
theorem B4982579 : Blo 860564 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B6228029 : Blo 860564 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B1968263 : Blo 860564 1968263 := bstep (se 1 (by rfl) ⟨1476197, by rfl⟩ : syracuseStep 1968263 = 2952395) B2952395
theorem B2459783 : Blo 860564 2459783 := bstep (se 1 (by rfl) ⟨1844837, by rfl⟩ : syracuseStep 2459783 = 3689675) B3689675
theorem B3279163 : Blo 860564 3279163 := bstep (se 1 (by rfl) ⟨2459372, by rfl⟩ : syracuseStep 3279163 = 4918745) B4918745
theorem B2459965 : Blo 860564 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B4360715 : Blo 860564 4360715 := bstep (se 1 (by rfl) ⟨3270536, by rfl⟩ : syracuseStep 4360715 = 6541073) B6541073
theorem B4655645 : Blo 860564 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B2329121 : Blo 860564 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B11045443 : Blo 860564 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B2460307 : Blo 860564 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B4360877 : Blo 860564 4360877 := bstep (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) B1635329
theorem B2099897 : Blo 860564 2099897 := bstep (se 2 (by rfl) ⟨787461, by rfl⟩ : syracuseStep 2099897 = 1574923) B1574923
theorem B1641161 : Blo 860564 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B3279649 : Blo 860564 3279649 := bstep (se 2 (by rfl) ⟨1229868, by rfl⟩ : syracuseStep 3279649 = 2459737) B2459737
theorem B1936313 : Blo 860564 1936313 := bstep (se 2 (by rfl) ⟨726117, by rfl⟩ : syracuseStep 1936313 = 1452235) B1452235
theorem B1838123 : Blo 860564 1838123 := bstep (se 1 (by rfl) ⟨1378592, by rfl⟩ : syracuseStep 1838123 = 2757185) B2757185
theorem B1969211 : Blo 860564 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1936655 : Blo 860564 1936655 := bstep (se 1 (by rfl) ⟨1452491, by rfl⟩ : syracuseStep 1936655 = 2904983) B2904983
theorem B1936673 : Blo 860564 1936673 := bstep (se 2 (by rfl) ⟨726252, by rfl⟩ : syracuseStep 1936673 = 1452505) B1452505
theorem B920975 : Blo 860564 920975 := bstep (se 1 (by rfl) ⟨690731, by rfl⟩ : syracuseStep 920975 = 1381463) B1381463
theorem B9309649 : Blo 860564 9309649 := bstep (se 2 (by rfl) ⟨3491118, by rfl⟩ : syracuseStep 9309649 = 6982237) B6982237
theorem B2461195 : Blo 860564 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B1379855 : Blo 860564 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B5312087 : Blo 860564 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B1937015 : Blo 860564 1937015 := bstep (se 1 (by rfl) ⟨1452761, by rfl⟩ : syracuseStep 1937015 = 2905523) B2905523
theorem B921223 : Blo 860564 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B3280621 : Blo 860564 3280621 := bstep (se 3 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 3280621 = 1230233) B1230233
theorem B1937195 : Blo 860564 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B1773371 : Blo 860564 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B2461697 : Blo 860564 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B3280925 : Blo 860564 3280925 := bstep (se 3 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 3280925 = 1230347) B1230347
theorem B1937555 : Blo 860564 1937555 := bstep (se 1 (by rfl) ⟨1453166, by rfl⟩ : syracuseStep 1937555 = 2906333) B2906333
theorem B1937609 : Blo 860564 1937609 := bstep (se 2 (by rfl) ⟨726603, by rfl⟩ : syracuseStep 1937609 = 1453207) B1453207
theorem B4362497 : Blo 860564 4362497 := bstep (se 2 (by rfl) ⟨1635936, by rfl⟩ : syracuseStep 4362497 = 3271873) B3271873
theorem B922043 : Blo 860564 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B70685297 : Blo 860564 70685297 := bstep (se 2 (by rfl) ⟨26506986, by rfl⟩ : syracuseStep 70685297 = 53013973) B53013973
theorem B1839763 : Blo 860564 1839763 := bstep (se 1 (by rfl) ⟨1379822, by rfl⟩ : syracuseStep 1839763 = 2759645) B2759645
theorem B2331283 : Blo 860564 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B9310949 : Blo 860564 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B2331479 : Blo 860564 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B2626391 : Blo 860564 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B1938311 : Blo 860564 1938311 := bstep (se 1 (by rfl) ⟨1453733, by rfl⟩ : syracuseStep 1938311 = 2907467) B2907467
theorem B4363307 : Blo 860564 4363307 := bstep (se 1 (by rfl) ⟨3272480, by rfl⟩ : syracuseStep 4363307 = 6544961) B6544961
theorem B1938491 : Blo 860564 1938491 := bstep (se 1 (by rfl) ⟨1453868, by rfl⟩ : syracuseStep 1938491 = 2907737) B2907737
theorem B12424279 : Blo 860564 12424279 := bstep (se 1 (by rfl) ⟨9318209, by rfl⟩ : syracuseStep 12424279 = 18636419) B18636419
theorem B1971319 : Blo 860564 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B1938617 : Blo 860564 1938617 := bstep (se 2 (by rfl) ⟨726981, by rfl⟩ : syracuseStep 1938617 = 1453963) B1453963
theorem B4658413 : Blo 860564 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B2069945 : Blo 860564 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B1938959 : Blo 860564 1938959 := bstep (se 1 (by rfl) ⟨1454219, by rfl⟩ : syracuseStep 1938959 = 2908439) B2908439
theorem B1938977 : Blo 860564 1938977 := bstep (se 2 (by rfl) ⟨727116, by rfl⟩ : syracuseStep 1938977 = 1454233) B1454233
theorem B3282551 : Blo 860564 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B3675937 : Blo 860564 3675937 := bstep (se 2 (by rfl) ⟨1378476, by rfl⟩ : syracuseStep 3675937 = 2756953) B2756953
theorem B1939319 : Blo 860564 1939319 := bstep (se 1 (by rfl) ⟨1454489, by rfl⟩ : syracuseStep 1939319 = 2908979) B2908979
theorem B1939499 : Blo 860564 1939499 := bstep (se 1 (by rfl) ⟨1454624, by rfl⟩ : syracuseStep 1939499 = 2909249) B2909249
theorem B35330165 : Blo 860564 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B3676279 : Blo 860564 3676279 := bstep (se 1 (by rfl) ⟨2757209, by rfl⟩ : syracuseStep 3676279 = 5514419) B5514419
theorem B5970235 : Blo 860564 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B4364603 : Blo 860564 4364603 := bstep (se 1 (by rfl) ⟨3273452, by rfl⟩ : syracuseStep 4364603 = 6546905) B6546905
theorem B1939859 : Blo 860564 1939859 := bstep (se 1 (by rfl) ⟨1454894, by rfl⟩ : syracuseStep 1939859 = 2909789) B2909789
theorem B1939913 : Blo 860564 1939913 := bstep (se 2 (by rfl) ⟨727467, by rfl⟩ : syracuseStep 1939913 = 1454935) B1454935
theorem B1841609 : Blo 860564 1841609 := bstep (se 2 (by rfl) ⟨690603, by rfl⟩ : syracuseStep 1841609 = 1381207) B1381207
theorem B4364765 : Blo 860564 4364765 := bstep (se 3 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 4364765 = 1636787) B1636787
theorem B2759197 : Blo 860564 2759197 := bstep (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) B1034699
theorem B6560513 : Blo 860564 6560513 := bstep (se 2 (by rfl) ⟨2460192, by rfl⟩ : syracuseStep 6560513 = 4920385) B4920385
theorem B2661131 : Blo 860564 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B4365089 : Blo 860564 4365089 := bstep (se 2 (by rfl) ⟨1636908, by rfl⟩ : syracuseStep 4365089 = 3273817) B3273817
theorem B2104265 : Blo 860564 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B15735869 : Blo 860564 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B1940615 : Blo 860564 1940615 := bstep (se 1 (by rfl) ⟨1455461, by rfl⟩ : syracuseStep 1940615 = 2910923) B2910923
theorem B37264535 : Blo 860564 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B1940795 : Blo 860564 1940795 := bstep (se 1 (by rfl) ⟨1455596, by rfl⟩ : syracuseStep 1940795 = 2911193) B2911193
theorem B1940921 : Blo 860564 1940921 := bstep (se 2 (by rfl) ⟨727845, by rfl⟩ : syracuseStep 1940921 = 1455691) B1455691
theorem B4366061 : Blo 860564 4366061 := bstep (se 3 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 4366061 = 1637273) B1637273
theorem B1941263 : Blo 860564 1941263 := bstep (se 1 (by rfl) ⟨1455947, by rfl⟩ : syracuseStep 1941263 = 2911895) B2911895
theorem B1941281 : Blo 860564 1941281 := bstep (se 2 (by rfl) ⟨727980, by rfl⟩ : syracuseStep 1941281 = 1455961) B1455961
theorem B1089551 : Blo 860564 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B9314365 : Blo 860564 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B1941623 : Blo 860564 1941623 := bstep (se 1 (by rfl) ⟨1456217, by rfl⟩ : syracuseStep 1941623 = 2912435) B2912435
theorem B2105633 : Blo 860564 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1941803 : Blo 860564 1941803 := bstep (se 1 (by rfl) ⟨1456352, by rfl⟩ : syracuseStep 1941803 = 2912705) B2912705
theorem B8298845 : Blo 860564 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B860603 : Blo 860564 860603 := bstep (se 1 (by rfl) ⟨645452, by rfl⟩ : syracuseStep 860603 = 1290905) B1290905
theorem B2073089 : Blo 860564 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B860679 : Blo 860564 860679 := bstep (se 1 (by rfl) ⟨645509, by rfl⟩ : syracuseStep 860679 = 1291019) B1291019
theorem B860687 : Blo 860564 860687 := bstep (se 1 (by rfl) ⟨645515, by rfl⟩ : syracuseStep 860687 = 1291031) B1291031
theorem B4366871 : Blo 860564 4366871 := bstep (se 1 (by rfl) ⟨3275153, by rfl⟩ : syracuseStep 4366871 = 6550307) B6550307
theorem B860731 : Blo 860564 860731 := bstep (se 1 (by rfl) ⟨645548, by rfl⟩ : syracuseStep 860731 = 1291097) B1291097
theorem B860807 : Blo 860564 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B860815 : Blo 860564 860815 := bstep (se 1 (by rfl) ⟨645611, by rfl⟩ : syracuseStep 860815 = 1291223) B1291223
theorem B1942163 : Blo 860564 1942163 := bstep (se 1 (by rfl) ⟨1456622, by rfl⟩ : syracuseStep 1942163 = 2913245) B2913245
theorem B860859 : Blo 860564 860859 := bstep (se 1 (by rfl) ⟨645644, by rfl⟩ : syracuseStep 860859 = 1291289) B1291289
theorem B1942217 : Blo 860564 1942217 := bstep (se 2 (by rfl) ⟨728331, by rfl⟩ : syracuseStep 1942217 = 1456663) B1456663
theorem B860935 : Blo 860564 860935 := bstep (se 1 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 860935 = 1291403) B1291403
theorem B860943 : Blo 860564 860943 := bstep (se 1 (by rfl) ⟨645707, by rfl⟩ : syracuseStep 860943 = 1291415) B1291415
theorem B860987 : Blo 860564 860987 := bstep (se 1 (by rfl) ⟨645740, by rfl⟩ : syracuseStep 860987 = 1291481) B1291481
theorem B861063 : Blo 860564 861063 := bstep (se 1 (by rfl) ⟨645797, by rfl⟩ : syracuseStep 861063 = 1291595) B1291595
theorem B861071 : Blo 860564 861071 := bstep (se 1 (by rfl) ⟨645803, by rfl⟩ : syracuseStep 861071 = 1291607) B1291607
theorem B861115 : Blo 860564 861115 := bstep (se 1 (by rfl) ⟨645836, by rfl⟩ : syracuseStep 861115 = 1291673) B1291673
theorem B861191 : Blo 860564 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B861199 : Blo 860564 861199 := bstep (se 1 (by rfl) ⟨645899, by rfl⟩ : syracuseStep 861199 = 1291799) B1291799
theorem B2761771 : Blo 860564 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B861243 : Blo 860564 861243 := bstep (se 1 (by rfl) ⟨645932, by rfl⟩ : syracuseStep 861243 = 1291865) B1291865
theorem B4990013 : Blo 860564 4990013 := bstep (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) B1871255
theorem B861319 : Blo 860564 861319 := bstep (se 1 (by rfl) ⟨645989, by rfl⟩ : syracuseStep 861319 = 1291979) B1291979
theorem B861327 : Blo 860564 861327 := bstep (se 1 (by rfl) ⟨645995, by rfl⟩ : syracuseStep 861327 = 1291991) B1291991
theorem B2335891 : Blo 860564 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B861371 : Blo 860564 861371 := bstep (se 1 (by rfl) ⟨646028, by rfl⟩ : syracuseStep 861371 = 1292057) B1292057
theorem B861447 : Blo 860564 861447 := bstep (se 1 (by rfl) ⟨646085, by rfl⟩ : syracuseStep 861447 = 1292171) B1292171
theorem B861455 : Blo 860564 861455 := bstep (se 1 (by rfl) ⟨646091, by rfl⟩ : syracuseStep 861455 = 1292183) B1292183
theorem B861499 : Blo 860564 861499 := bstep (se 1 (by rfl) ⟨646124, by rfl⟩ : syracuseStep 861499 = 1292249) B1292249
theorem B861575 : Blo 860564 861575 := bstep (se 1 (by rfl) ⟨646181, by rfl⟩ : syracuseStep 861575 = 1292363) B1292363
theorem B1942919 : Blo 860564 1942919 := bstep (se 1 (by rfl) ⟨1457189, by rfl⟩ : syracuseStep 1942919 = 2914379) B2914379
theorem B861583 : Blo 860564 861583 := bstep (se 1 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 861583 = 1292375) B1292375
theorem B7480721 : Blo 860564 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B861627 : Blo 860564 861627 := bstep (se 1 (by rfl) ⟨646220, by rfl⟩ : syracuseStep 861627 = 1292441) B1292441
theorem B12625357 : Blo 860564 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B861703 : Blo 860564 861703 := bstep (se 1 (by rfl) ⟨646277, by rfl⟩ : syracuseStep 861703 = 1292555) B1292555
theorem B861711 : Blo 860564 861711 := bstep (se 1 (by rfl) ⟨646283, by rfl⟩ : syracuseStep 861711 = 1292567) B1292567
theorem B1844795 : Blo 860564 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B861755 : Blo 860564 861755 := bstep (se 1 (by rfl) ⟨646316, by rfl⟩ : syracuseStep 861755 = 1292633) B1292633
theorem B1943099 : Blo 860564 1943099 := bstep (se 1 (by rfl) ⟨1457324, by rfl⟩ : syracuseStep 1943099 = 2914649) B2914649
theorem B861831 : Blo 860564 861831 := bstep (se 1 (by rfl) ⟨646373, by rfl⟩ : syracuseStep 861831 = 1292747) B1292747
theorem B861839 : Blo 860564 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B1943225 : Blo 860564 1943225 := bstep (se 2 (by rfl) ⟨728709, by rfl⟩ : syracuseStep 1943225 = 1457419) B1457419
theorem B861883 : Blo 860564 861883 := bstep (se 1 (by rfl) ⟨646412, by rfl⟩ : syracuseStep 861883 = 1292825) B1292825
theorem B861959 : Blo 860564 861959 := bstep (se 1 (by rfl) ⟨646469, by rfl⟩ : syracuseStep 861959 = 1292939) B1292939
theorem B861967 : Blo 860564 861967 := bstep (se 1 (by rfl) ⟨646475, by rfl⟩ : syracuseStep 861967 = 1292951) B1292951
theorem B5908261 : Blo 860564 5908261 := bstep (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) B1107799
theorem B862011 : Blo 860564 862011 := bstep (se 1 (by rfl) ⟨646508, by rfl⟩ : syracuseStep 862011 = 1293017) B1293017
theorem B4728635 : Blo 860564 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B4663129 : Blo 860564 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B862087 : Blo 860564 862087 := bstep (se 1 (by rfl) ⟨646565, by rfl⟩ : syracuseStep 862087 = 1293131) B1293131
theorem B2336647 : Blo 860564 2336647 := bstep (se 1 (by rfl) ⟨1752485, by rfl⟩ : syracuseStep 2336647 = 3504971) B3504971
theorem B862095 : Blo 860564 862095 := bstep (se 1 (by rfl) ⟨646571, by rfl⟩ : syracuseStep 862095 = 1293143) B1293143
theorem B862139 : Blo 860564 862139 := bstep (se 1 (by rfl) ⟨646604, by rfl⟩ : syracuseStep 862139 = 1293209) B1293209
theorem B49719257 : Blo 860564 49719257 := bstep (se 2 (by rfl) ⟨18644721, by rfl⟩ : syracuseStep 49719257 = 37289443) B37289443
theorem B862215 : Blo 860564 862215 := bstep (se 1 (by rfl) ⟨646661, by rfl⟩ : syracuseStep 862215 = 1293323) B1293323
theorem B862223 : Blo 860564 862223 := bstep (se 1 (by rfl) ⟨646667, by rfl⟩ : syracuseStep 862223 = 1293335) B1293335
theorem B1943567 : Blo 860564 1943567 := bstep (se 1 (by rfl) ⟨1457675, by rfl⟩ : syracuseStep 1943567 = 2915351) B2915351
theorem B1943585 : Blo 860564 1943585 := bstep (se 2 (by rfl) ⟨728844, by rfl⟩ : syracuseStep 1943585 = 1457689) B1457689
theorem B862267 : Blo 860564 862267 := bstep (se 1 (by rfl) ⟨646700, by rfl⟩ : syracuseStep 862267 = 1293401) B1293401
theorem B862343 : Blo 860564 862343 := bstep (se 1 (by rfl) ⟨646757, by rfl⟩ : syracuseStep 862343 = 1293515) B1293515
theorem B862351 : Blo 860564 862351 := bstep (se 1 (by rfl) ⟨646763, by rfl⟩ : syracuseStep 862351 = 1293527) B1293527
theorem B862395 : Blo 860564 862395 := bstep (se 1 (by rfl) ⟨646796, by rfl⟩ : syracuseStep 862395 = 1293593) B1293593
theorem B862471 : Blo 860564 862471 := bstep (se 1 (by rfl) ⟨646853, by rfl⟩ : syracuseStep 862471 = 1293707) B1293707
theorem B862479 : Blo 860564 862479 := bstep (se 1 (by rfl) ⟨646859, by rfl⟩ : syracuseStep 862479 = 1293719) B1293719
theorem B4663603 : Blo 860564 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B862523 : Blo 860564 862523 := bstep (se 1 (by rfl) ⟨646892, by rfl⟩ : syracuseStep 862523 = 1293785) B1293785
theorem B1943927 : Blo 860564 1943927 := bstep (se 1 (by rfl) ⟨1457945, by rfl⟩ : syracuseStep 1943927 = 2915891) B2915891
theorem B1845623 : Blo 860564 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B862599 : Blo 860564 862599 := bstep (se 1 (by rfl) ⟨646949, by rfl⟩ : syracuseStep 862599 = 1293899) B1293899
theorem B862607 : Blo 860564 862607 := bstep (se 1 (by rfl) ⟨646955, by rfl⟩ : syracuseStep 862607 = 1293911) B1293911
theorem B862651 : Blo 860564 862651 := bstep (se 1 (by rfl) ⟨646988, by rfl⟩ : syracuseStep 862651 = 1293977) B1293977
theorem B862727 : Blo 860564 862727 := bstep (se 1 (by rfl) ⟨647045, by rfl⟩ : syracuseStep 862727 = 1294091) B1294091
theorem B1452559 : Blo 860564 1452559 := bstep (se 1 (by rfl) ⟨1089419, by rfl⟩ : syracuseStep 1452559 = 2178839) B2178839
theorem B862735 : Blo 860564 862735 := bstep (se 1 (by rfl) ⟨647051, by rfl⟩ : syracuseStep 862735 = 1294103) B1294103
theorem B1944107 : Blo 860564 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B862779 : Blo 860564 862779 := bstep (se 1 (by rfl) ⟨647084, by rfl⟩ : syracuseStep 862779 = 1294169) B1294169
theorem B4139581 : Blo 860564 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B862855 : Blo 860564 862855 := bstep (se 1 (by rfl) ⟨647141, by rfl⟩ : syracuseStep 862855 = 1294283) B1294283
theorem B862863 : Blo 860564 862863 := bstep (se 1 (by rfl) ⟨647147, by rfl⟩ : syracuseStep 862863 = 1294295) B1294295
theorem B862907 : Blo 860564 862907 := bstep (se 1 (by rfl) ⟨647180, by rfl⟩ : syracuseStep 862907 = 1294361) B1294361
theorem B862983 : Blo 860564 862983 := bstep (se 1 (by rfl) ⟨647237, by rfl⟩ : syracuseStep 862983 = 1294475) B1294475
theorem B862991 : Blo 860564 862991 := bstep (se 1 (by rfl) ⟨647243, by rfl⟩ : syracuseStep 862991 = 1294487) B1294487
theorem B863035 : Blo 860564 863035 := bstep (se 1 (by rfl) ⟨647276, by rfl⟩ : syracuseStep 863035 = 1294553) B1294553
theorem B863111 : Blo 860564 863111 := bstep (se 1 (by rfl) ⟨647333, by rfl⟩ : syracuseStep 863111 = 1294667) B1294667
theorem B863119 : Blo 860564 863119 := bstep (se 1 (by rfl) ⟨647339, by rfl⟩ : syracuseStep 863119 = 1294679) B1294679
theorem B1944467 : Blo 860564 1944467 := bstep (se 1 (by rfl) ⟨1458350, by rfl⟩ : syracuseStep 1944467 = 2916701) B2916701
theorem B1092523 : Blo 860564 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B863163 : Blo 860564 863163 := bstep (se 1 (by rfl) ⟨647372, by rfl⟩ : syracuseStep 863163 = 1294745) B1294745
theorem B1944521 : Blo 860564 1944521 := bstep (se 2 (by rfl) ⟨729195, by rfl⟩ : syracuseStep 1944521 = 1458391) B1458391
theorem B863239 : Blo 860564 863239 := bstep (se 1 (by rfl) ⟨647429, by rfl⟩ : syracuseStep 863239 = 1294859) B1294859
theorem B863247 : Blo 860564 863247 := bstep (se 1 (by rfl) ⟨647435, by rfl⟩ : syracuseStep 863247 = 1294871) B1294871
theorem B6564887 : Blo 860564 6564887 := bstep (se 1 (by rfl) ⟨4923665, by rfl⟩ : syracuseStep 6564887 = 9847331) B9847331
theorem B1453099 : Blo 860564 1453099 := bstep (se 1 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 1453099 = 2179649) B2179649
theorem B863291 : Blo 860564 863291 := bstep (se 1 (by rfl) ⟨647468, by rfl⟩ : syracuseStep 863291 = 1294937) B1294937
theorem B863367 : Blo 860564 863367 := bstep (se 1 (by rfl) ⟨647525, by rfl⟩ : syracuseStep 863367 = 1295051) B1295051
theorem B863375 : Blo 860564 863375 := bstep (se 1 (by rfl) ⟨647531, by rfl⟩ : syracuseStep 863375 = 1295063) B1295063
theorem B1453241 : Blo 860564 1453241 := bstep (se 2 (by rfl) ⟨544965, by rfl⟩ : syracuseStep 1453241 = 1089931) B1089931
theorem B863419 : Blo 860564 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B863495 : Blo 860564 863495 := bstep (se 1 (by rfl) ⟨647621, by rfl⟩ : syracuseStep 863495 = 1295243) B1295243
theorem B863503 : Blo 860564 863503 := bstep (se 1 (by rfl) ⟨647627, by rfl⟩ : syracuseStep 863503 = 1295255) B1295255
theorem B863547 : Blo 860564 863547 := bstep (se 1 (by rfl) ⟨647660, by rfl⟩ : syracuseStep 863547 = 1295321) B1295321
theorem B863623 : Blo 860564 863623 := bstep (se 1 (by rfl) ⟨647717, by rfl⟩ : syracuseStep 863623 = 1295435) B1295435
theorem B863631 : Blo 860564 863631 := bstep (se 1 (by rfl) ⟨647723, by rfl⟩ : syracuseStep 863631 = 1295447) B1295447
theorem B863675 : Blo 860564 863675 := bstep (se 1 (by rfl) ⟨647756, by rfl⟩ : syracuseStep 863675 = 1295513) B1295513
theorem B863751 : Blo 860564 863751 := bstep (se 1 (by rfl) ⟨647813, by rfl⟩ : syracuseStep 863751 = 1295627) B1295627
theorem B863759 : Blo 860564 863759 := bstep (se 1 (by rfl) ⟨647819, by rfl⟩ : syracuseStep 863759 = 1295639) B1295639
theorem B4664861 : Blo 860564 4664861 := bstep (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) B1749323
theorem B4369949 : Blo 860564 4369949 := bstep (se 3 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 4369949 = 1638731) B1638731
theorem B863803 : Blo 860564 863803 := bstep (se 1 (by rfl) ⟨647852, by rfl⟩ : syracuseStep 863803 = 1295705) B1295705
theorem B863879 : Blo 860564 863879 := bstep (se 1 (by rfl) ⟨647909, by rfl⟩ : syracuseStep 863879 = 1295819) B1295819
theorem B1945223 : Blo 860564 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B863887 : Blo 860564 863887 := bstep (se 1 (by rfl) ⟨647915, by rfl⟩ : syracuseStep 863887 = 1295831) B1295831
theorem B863931 : Blo 860564 863931 := bstep (se 1 (by rfl) ⟨647948, by rfl⟩ : syracuseStep 863931 = 1295897) B1295897
theorem B2764489 : Blo 860564 2764489 := bstep (se 2 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 2764489 = 2073367) B2073367
theorem B864007 : Blo 860564 864007 := bstep (se 1 (by rfl) ⟨648005, by rfl⟩ : syracuseStep 864007 = 1296011) B1296011
theorem B864015 : Blo 860564 864015 := bstep (se 1 (by rfl) ⟨648011, by rfl⟩ : syracuseStep 864015 = 1296023) B1296023
theorem B864059 : Blo 860564 864059 := bstep (se 1 (by rfl) ⟨648044, by rfl⟩ : syracuseStep 864059 = 1296089) B1296089
theorem B1453943 : Blo 860564 1453943 := bstep (se 1 (by rfl) ⟨1090457, by rfl⟩ : syracuseStep 1453943 = 2180915) B2180915
theorem B1093495 : Blo 860564 1093495 := bstep (se 1 (by rfl) ⟨820121, by rfl⟩ : syracuseStep 1093495 = 1640243) B1640243
theorem B864135 : Blo 860564 864135 := bstep (se 1 (by rfl) ⟨648101, by rfl⟩ : syracuseStep 864135 = 1296203) B1296203
theorem B864143 : Blo 860564 864143 := bstep (se 1 (by rfl) ⟨648107, by rfl⟩ : syracuseStep 864143 = 1296215) B1296215
theorem B864187 : Blo 860564 864187 := bstep (se 1 (by rfl) ⟨648140, by rfl⟩ : syracuseStep 864187 = 1296281) B1296281
theorem B2076673 : Blo 860564 2076673 := bstep (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) B1557505
theorem B4370435 : Blo 860564 4370435 := bstep (se 1 (by rfl) ⟨3277826, by rfl⟩ : syracuseStep 4370435 = 6555653) B6555653
theorem B864263 : Blo 860564 864263 := bstep (se 1 (by rfl) ⟨648197, by rfl⟩ : syracuseStep 864263 = 1296395) B1296395
theorem B864271 : Blo 860564 864271 := bstep (se 1 (by rfl) ⟨648203, by rfl⟩ : syracuseStep 864271 = 1296407) B1296407
theorem B864315 : Blo 860564 864315 := bstep (se 1 (by rfl) ⟨648236, by rfl⟩ : syracuseStep 864315 = 1296473) B1296473
theorem B864391 : Blo 860564 864391 := bstep (se 1 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 864391 = 1296587) B1296587
theorem B864399 : Blo 860564 864399 := bstep (se 1 (by rfl) ⟨648299, by rfl⟩ : syracuseStep 864399 = 1296599) B1296599
theorem B1552531 : Blo 860564 1552531 := bstep (se 1 (by rfl) ⟨1164398, by rfl⟩ : syracuseStep 1552531 = 2328797) B2328797
theorem B1093819 : Blo 860564 1093819 := bstep (se 1 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 1093819 = 1640729) B1640729
theorem B864443 : Blo 860564 864443 := bstep (se 1 (by rfl) ⟨648332, by rfl⟩ : syracuseStep 864443 = 1296665) B1296665
theorem B4141313 : Blo 860564 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B864519 : Blo 860564 864519 := bstep (se 1 (by rfl) ⟨648389, by rfl⟩ : syracuseStep 864519 = 1296779) B1296779
theorem B864527 : Blo 860564 864527 := bstep (se 1 (by rfl) ⟨648395, by rfl⟩ : syracuseStep 864527 = 1296791) B1296791
theorem B1454395 : Blo 860564 1454395 := bstep (se 1 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 1454395 = 2181593) B2181593
theorem B1454537 : Blo 860564 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B1290887 : Blo 860564 1290887 := bstep (se 1 (by rfl) ⟨968165, by rfl⟩ : syracuseStep 1290887 = 1936331) B1936331
theorem B1290923 : Blo 860564 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B1290953 : Blo 860564 1290953 := bstep (se 2 (by rfl) ⟨484107, by rfl⟩ : syracuseStep 1290953 = 968215) B968215
theorem B1291067 : Blo 860564 1291067 := bstep (se 1 (by rfl) ⟨968300, by rfl⟩ : syracuseStep 1291067 = 1936601) B1936601
theorem B1684283 : Blo 860564 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B1291127 : Blo 860564 1291127 := bstep (se 1 (by rfl) ⟨968345, by rfl⟩ : syracuseStep 1291127 = 1936691) B1936691
theorem B4666247 : Blo 860564 4666247 := bstep (se 1 (by rfl) ⟨3499685, by rfl⟩ : syracuseStep 4666247 = 6999371) B6999371
theorem B1291151 : Blo 860564 1291151 := bstep (se 1 (by rfl) ⟨968363, by rfl⟩ : syracuseStep 1291151 = 1936727) B1936727
theorem B1291193 : Blo 860564 1291193 := bstep (se 2 (by rfl) ⟨484197, by rfl⟩ : syracuseStep 1291193 = 968395) B968395
theorem B1291271 : Blo 860564 1291271 := bstep (se 1 (by rfl) ⟨968453, by rfl⟩ : syracuseStep 1291271 = 1936907) B1936907
theorem B1291307 : Blo 860564 1291307 := bstep (se 1 (by rfl) ⟨968480, by rfl⟩ : syracuseStep 1291307 = 1936961) B1936961
theorem B1291337 : Blo 860564 1291337 := bstep (se 2 (by rfl) ⟨484251, by rfl⟩ : syracuseStep 1291337 = 968503) B968503
theorem B1455239 : Blo 860564 1455239 := bstep (se 1 (by rfl) ⟨1091429, by rfl⟩ : syracuseStep 1455239 = 2182859) B2182859
theorem B1553555 : Blo 860564 1553555 := bstep (se 1 (by rfl) ⟨1165166, by rfl⟩ : syracuseStep 1553555 = 2330333) B2330333
theorem B1291451 : Blo 860564 1291451 := bstep (se 1 (by rfl) ⟨968588, by rfl⟩ : syracuseStep 1291451 = 1937177) B1937177
theorem B1291511 : Blo 860564 1291511 := bstep (se 1 (by rfl) ⟨968633, by rfl⟩ : syracuseStep 1291511 = 1937267) B1937267
theorem B1291535 : Blo 860564 1291535 := bstep (se 1 (by rfl) ⟨968651, by rfl⟩ : syracuseStep 1291535 = 1937303) B1937303
theorem B1291577 : Blo 860564 1291577 := bstep (se 2 (by rfl) ⟨484341, by rfl⟩ : syracuseStep 1291577 = 968683) B968683
theorem B1291655 : Blo 860564 1291655 := bstep (se 1 (by rfl) ⟨968741, by rfl⟩ : syracuseStep 1291655 = 1937483) B1937483
theorem B3552659 : Blo 860564 3552659 := bstep (se 1 (by rfl) ⟨2664494, by rfl⟩ : syracuseStep 3552659 = 5328989) B5328989
theorem B1291691 : Blo 860564 1291691 := bstep (se 1 (by rfl) ⟨968768, by rfl⟩ : syracuseStep 1291691 = 1937537) B1937537
theorem B1291721 : Blo 860564 1291721 := bstep (se 2 (by rfl) ⟨484395, by rfl⟩ : syracuseStep 1291721 = 968791) B968791
theorem B4666891 : Blo 860564 4666891 := bstep (se 1 (by rfl) ⟨3500168, by rfl⟩ : syracuseStep 4666891 = 7000337) B7000337
theorem B1291835 : Blo 860564 1291835 := bstep (se 1 (by rfl) ⟨968876, by rfl⟩ : syracuseStep 1291835 = 1937753) B1937753
theorem B4372055 : Blo 860564 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B1291895 : Blo 860564 1291895 := bstep (se 1 (by rfl) ⟨968921, by rfl⟩ : syracuseStep 1291895 = 1937843) B1937843
theorem B1291919 : Blo 860564 1291919 := bstep (se 1 (by rfl) ⟨968939, by rfl⟩ : syracuseStep 1291919 = 1937879) B1937879
theorem B1291961 : Blo 860564 1291961 := bstep (se 2 (by rfl) ⟨484485, by rfl⟩ : syracuseStep 1291961 = 968971) B968971
theorem B1292039 : Blo 860564 1292039 := bstep (se 1 (by rfl) ⟨969029, by rfl⟩ : syracuseStep 1292039 = 1938059) B1938059
theorem B1455887 : Blo 860564 1455887 := bstep (se 1 (by rfl) ⟨1091915, by rfl⟩ : syracuseStep 1455887 = 2183831) B2183831
theorem B1292075 : Blo 860564 1292075 := bstep (se 1 (by rfl) ⟨969056, by rfl⟩ : syracuseStep 1292075 = 1938113) B1938113
theorem B1292105 : Blo 860564 1292105 := bstep (se 2 (by rfl) ⟨484539, by rfl⟩ : syracuseStep 1292105 = 969079) B969079
theorem B1292219 : Blo 860564 1292219 := bstep (se 1 (by rfl) ⟨969164, by rfl⟩ : syracuseStep 1292219 = 1938329) B1938329
theorem B1292279 : Blo 860564 1292279 := bstep (se 1 (by rfl) ⟨969209, by rfl⟩ : syracuseStep 1292279 = 1938419) B1938419
theorem B1292303 : Blo 860564 1292303 := bstep (se 1 (by rfl) ⟨969227, by rfl⟩ : syracuseStep 1292303 = 1938455) B1938455
theorem B1292345 : Blo 860564 1292345 := bstep (se 2 (by rfl) ⟨484629, by rfl⟩ : syracuseStep 1292345 = 969259) B969259
theorem B4372541 : Blo 860564 4372541 := bstep (se 3 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 4372541 = 1639703) B1639703
theorem B1292423 : Blo 860564 1292423 := bstep (se 1 (by rfl) ⟨969317, by rfl⟩ : syracuseStep 1292423 = 1938635) B1938635
theorem B997519 : Blo 860564 997519 := bstep (se 1 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 997519 = 1496279) B1496279
theorem B1292459 : Blo 860564 1292459 := bstep (se 1 (by rfl) ⟨969344, by rfl⟩ : syracuseStep 1292459 = 1938689) B1938689
theorem B1292489 : Blo 860564 1292489 := bstep (se 2 (by rfl) ⟨484683, by rfl⟩ : syracuseStep 1292489 = 969367) B969367
theorem B1456427 : Blo 860564 1456427 := bstep (se 1 (by rfl) ⟨1092320, by rfl⟩ : syracuseStep 1456427 = 2184641) B2184641
theorem B1292603 : Blo 860564 1292603 := bstep (se 1 (by rfl) ⟨969452, by rfl⟩ : syracuseStep 1292603 = 1938905) B1938905
theorem B26589505 : Blo 860564 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B1292663 : Blo 860564 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B3979655 : Blo 860564 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B1292687 : Blo 860564 1292687 := bstep (se 1 (by rfl) ⟨969515, by rfl⟩ : syracuseStep 1292687 = 1939031) B1939031
theorem B95566229 : Blo 860564 95566229 := bstep (se 6 (by rfl) ⟨2239833, by rfl⟩ : syracuseStep 95566229 = 4479667) B4479667
theorem B1292729 : Blo 860564 1292729 := bstep (se 2 (by rfl) ⟨484773, by rfl⟩ : syracuseStep 1292729 = 969547) B969547
theorem B4143581 : Blo 860564 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B1292807 : Blo 860564 1292807 := bstep (se 1 (by rfl) ⟨969605, by rfl⟩ : syracuseStep 1292807 = 1939211) B1939211
theorem B1292843 : Blo 860564 1292843 := bstep (se 1 (by rfl) ⟨969632, by rfl⟩ : syracuseStep 1292843 = 1939265) B1939265
theorem B1292873 : Blo 860564 1292873 := bstep (se 2 (by rfl) ⟨484827, by rfl⟩ : syracuseStep 1292873 = 969655) B969655
theorem B1456825 : Blo 860564 1456825 := bstep (se 2 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 1456825 = 1092619) B1092619
theorem B1292987 : Blo 860564 1292987 := bstep (se 1 (by rfl) ⟨969740, by rfl⟩ : syracuseStep 1292987 = 1939481) B1939481
theorem B1293047 : Blo 860564 1293047 := bstep (se 1 (by rfl) ⟨969785, by rfl⟩ : syracuseStep 1293047 = 1939571) B1939571
theorem B1227511 : Blo 860564 1227511 := bstep (se 1 (by rfl) ⟨920633, by rfl⟩ : syracuseStep 1227511 = 1841267) B1841267
theorem B1293071 : Blo 860564 1293071 := bstep (se 1 (by rfl) ⟨969803, by rfl⟩ : syracuseStep 1293071 = 1939607) B1939607
theorem B4143887 : Blo 860564 4143887 := bstep (se 1 (by rfl) ⟨3107915, by rfl⟩ : syracuseStep 4143887 = 6215831) B6215831
theorem B1293113 : Blo 860564 1293113 := bstep (se 2 (by rfl) ⟨484917, by rfl⟩ : syracuseStep 1293113 = 969835) B969835
theorem B1293191 : Blo 860564 1293191 := bstep (se 1 (by rfl) ⟨969893, by rfl⟩ : syracuseStep 1293191 = 1939787) B1939787
theorem B1293227 : Blo 860564 1293227 := bstep (se 1 (by rfl) ⟨969920, by rfl⟩ : syracuseStep 1293227 = 1939841) B1939841
theorem B1293257 : Blo 860564 1293257 := bstep (se 2 (by rfl) ⟨484971, by rfl⟩ : syracuseStep 1293257 = 969943) B969943
theorem B4144081 : Blo 860564 4144081 := bstep (se 2 (by rfl) ⟨1554030, by rfl⟩ : syracuseStep 4144081 = 3108061) B3108061
theorem B1293371 : Blo 860564 1293371 := bstep (se 1 (by rfl) ⟨970028, by rfl⟩ : syracuseStep 1293371 = 1940057) B1940057
theorem B1293431 : Blo 860564 1293431 := bstep (se 1 (by rfl) ⟨970073, by rfl⟩ : syracuseStep 1293431 = 1940147) B1940147
theorem B1293455 : Blo 860564 1293455 := bstep (se 1 (by rfl) ⟨970091, by rfl⟩ : syracuseStep 1293455 = 1940183) B1940183
theorem B1293497 : Blo 860564 1293497 := bstep (se 2 (by rfl) ⟨485061, by rfl⟩ : syracuseStep 1293497 = 970123) B970123
theorem B1293575 : Blo 860564 1293575 := bstep (se 1 (by rfl) ⟨970181, by rfl⟩ : syracuseStep 1293575 = 1940363) B1940363
theorem B1293611 : Blo 860564 1293611 := bstep (se 1 (by rfl) ⟨970208, by rfl⟩ : syracuseStep 1293611 = 1940417) B1940417
theorem B1293641 : Blo 860564 1293641 := bstep (se 2 (by rfl) ⟨485115, by rfl⟩ : syracuseStep 1293641 = 970231) B970231
theorem B1457527 : Blo 860564 1457527 := bstep (se 1 (by rfl) ⟨1093145, by rfl⟩ : syracuseStep 1457527 = 2186291) B2186291
theorem B1293755 : Blo 860564 1293755 := bstep (se 1 (by rfl) ⟨970316, by rfl⟩ : syracuseStep 1293755 = 1940633) B1940633
theorem B1293815 : Blo 860564 1293815 := bstep (se 1 (by rfl) ⟨970361, by rfl⟩ : syracuseStep 1293815 = 1940723) B1940723
theorem B1293839 : Blo 860564 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B1228331 : Blo 860564 1228331 := bstep (se 1 (by rfl) ⟨921248, by rfl⟩ : syracuseStep 1228331 = 1842497) B1842497
theorem B1293881 : Blo 860564 1293881 := bstep (se 2 (by rfl) ⟨485205, by rfl⟩ : syracuseStep 1293881 = 970411) B970411
theorem B1457723 : Blo 860564 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B2178647 : Blo 860564 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B1293959 : Blo 860564 1293959 := bstep (se 1 (by rfl) ⟨970469, by rfl⟩ : syracuseStep 1293959 = 1940939) B1940939
theorem B1293995 : Blo 860564 1293995 := bstep (se 1 (by rfl) ⟨970496, by rfl⟩ : syracuseStep 1293995 = 1940993) B1940993
theorem B1294025 : Blo 860564 1294025 := bstep (se 2 (by rfl) ⟨485259, by rfl⟩ : syracuseStep 1294025 = 970519) B970519
theorem B9813797 : Blo 860564 9813797 := bstep (se 4 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 9813797 = 1840087) B1840087
theorem B2178859 : Blo 860564 2178859 := bstep (se 1 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 2178859 = 3268289) B3268289
theorem B4374323 : Blo 860564 4374323 := bstep (se 1 (by rfl) ⟨3280742, by rfl⟩ : syracuseStep 4374323 = 6561485) B6561485
theorem B1294139 : Blo 860564 1294139 := bstep (se 1 (by rfl) ⟨970604, by rfl⟩ : syracuseStep 1294139 = 1941209) B1941209
theorem B1294199 : Blo 860564 1294199 := bstep (se 1 (by rfl) ⟨970649, by rfl⟩ : syracuseStep 1294199 = 1941299) B1941299
theorem B1294223 : Blo 860564 1294223 := bstep (se 1 (by rfl) ⟨970667, by rfl⟩ : syracuseStep 1294223 = 1941335) B1941335
theorem B2179001 : Blo 860564 2179001 := bstep (se 2 (by rfl) ⟨817125, by rfl⟩ : syracuseStep 2179001 = 1634251) B1634251
theorem B1294265 : Blo 860564 1294265 := bstep (se 2 (by rfl) ⟨485349, by rfl⟩ : syracuseStep 1294265 = 970699) B970699
theorem B1458121 : Blo 860564 1458121 := bstep (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) B1093591
theorem B1294343 : Blo 860564 1294343 := bstep (se 1 (by rfl) ⟨970757, by rfl⟩ : syracuseStep 1294343 = 1941515) B1941515
theorem B2211851 : Blo 860564 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1294379 : Blo 860564 1294379 := bstep (se 1 (by rfl) ⟨970784, by rfl⟩ : syracuseStep 1294379 = 1941569) B1941569
theorem B1294409 : Blo 860564 1294409 := bstep (se 2 (by rfl) ⟨485403, by rfl⟩ : syracuseStep 1294409 = 970807) B970807
theorem B4374647 : Blo 860564 4374647 := bstep (se 1 (by rfl) ⟨3280985, by rfl⟩ : syracuseStep 4374647 = 6561971) B6561971
theorem B2244755 : Blo 860564 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B1294523 : Blo 860564 1294523 := bstep (se 1 (by rfl) ⟨970892, by rfl⟩ : syracuseStep 1294523 = 1941785) B1941785
theorem B1294583 : Blo 860564 1294583 := bstep (se 1 (by rfl) ⟨970937, by rfl⟩ : syracuseStep 1294583 = 1941875) B1941875
theorem B1294607 : Blo 860564 1294607 := bstep (se 1 (by rfl) ⟨970955, by rfl⟩ : syracuseStep 1294607 = 1941911) B1941911
theorem B1294649 : Blo 860564 1294649 := bstep (se 2 (by rfl) ⟨485493, by rfl⟩ : syracuseStep 1294649 = 970987) B970987
theorem B1294727 : Blo 860564 1294727 := bstep (se 1 (by rfl) ⟨971045, by rfl⟩ : syracuseStep 1294727 = 1942091) B1942091
theorem B1294763 : Blo 860564 1294763 := bstep (se 1 (by rfl) ⟨971072, by rfl⟩ : syracuseStep 1294763 = 1942145) B1942145
theorem B1294793 : Blo 860564 1294793 := bstep (se 2 (by rfl) ⟨485547, by rfl⟩ : syracuseStep 1294793 = 971095) B971095
theorem B1294907 : Blo 860564 1294907 := bstep (se 1 (by rfl) ⟨971180, by rfl⟩ : syracuseStep 1294907 = 1942361) B1942361
theorem B1294967 : Blo 860564 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B1458823 : Blo 860564 1458823 := bstep (se 1 (by rfl) ⟨1094117, by rfl⟩ : syracuseStep 1458823 = 2188235) B2188235
theorem B1294991 : Blo 860564 1294991 := bstep (se 1 (by rfl) ⟨971243, by rfl⟩ : syracuseStep 1294991 = 1942487) B1942487
theorem B1295033 : Blo 860564 1295033 := bstep (se 2 (by rfl) ⟨485637, by rfl⟩ : syracuseStep 1295033 = 971275) B971275
theorem B1295111 : Blo 860564 1295111 := bstep (se 1 (by rfl) ⟨971333, by rfl⟩ : syracuseStep 1295111 = 1942667) B1942667
theorem B1295147 : Blo 860564 1295147 := bstep (se 1 (by rfl) ⟨971360, by rfl⟩ : syracuseStep 1295147 = 1942721) B1942721
theorem B1295177 : Blo 860564 1295177 := bstep (se 2 (by rfl) ⟨485691, by rfl⟩ : syracuseStep 1295177 = 971383) B971383
theorem B2179993 : Blo 860564 2179993 := bstep (se 2 (by rfl) ⟨817497, by rfl⟩ : syracuseStep 2179993 = 1634995) B1634995
theorem B1295291 : Blo 860564 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1229755 : Blo 860564 1229755 := bstep (se 1 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 1229755 = 1844633) B1844633
theorem B1295351 : Blo 860564 1295351 := bstep (se 1 (by rfl) ⟨971513, by rfl⟩ : syracuseStep 1295351 = 1943027) B1943027
theorem B1295375 : Blo 860564 1295375 := bstep (se 1 (by rfl) ⟨971531, by rfl⟩ : syracuseStep 1295375 = 1943063) B1943063
theorem B6308887 : Blo 860564 6308887 := bstep (se 1 (by rfl) ⟨4731665, by rfl⟩ : syracuseStep 6308887 = 9463331) B9463331
theorem B1295417 : Blo 860564 1295417 := bstep (se 2 (by rfl) ⟨485781, by rfl⟩ : syracuseStep 1295417 = 971563) B971563
theorem B2180155 : Blo 860564 2180155 := bstep (se 1 (by rfl) ⟨1635116, by rfl⟩ : syracuseStep 2180155 = 3270233) B3270233
theorem B4375619 : Blo 860564 4375619 := bstep (se 1 (by rfl) ⟨3281714, by rfl⟩ : syracuseStep 4375619 = 6563429) B6563429
theorem B8307845 : Blo 860564 8307845 := bstep (se 4 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 8307845 = 1557721) B1557721
theorem B1295495 : Blo 860564 1295495 := bstep (se 1 (by rfl) ⟨971621, by rfl⟩ : syracuseStep 1295495 = 1943243) B1943243
theorem B1295531 : Blo 860564 1295531 := bstep (se 1 (by rfl) ⟨971648, by rfl⟩ : syracuseStep 1295531 = 1943297) B1943297
theorem B2180297 : Blo 860564 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B1295561 : Blo 860564 1295561 := bstep (se 2 (by rfl) ⟨485835, by rfl⟩ : syracuseStep 1295561 = 971671) B971671
theorem B1295675 : Blo 860564 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B1295735 : Blo 860564 1295735 := bstep (se 1 (by rfl) ⟨971801, by rfl⟩ : syracuseStep 1295735 = 1943603) B1943603
theorem B4375943 : Blo 860564 4375943 := bstep (se 1 (by rfl) ⟨3281957, by rfl⟩ : syracuseStep 4375943 = 6563915) B6563915
theorem B1295759 : Blo 860564 1295759 := bstep (se 1 (by rfl) ⟨971819, by rfl⟩ : syracuseStep 1295759 = 1943639) B1943639
theorem B6538643 : Blo 860564 6538643 := bstep (se 1 (by rfl) ⟨4903982, by rfl⟩ : syracuseStep 6538643 = 9807965) B9807965
theorem B1295801 : Blo 860564 1295801 := bstep (se 2 (by rfl) ⟨485925, by rfl⟩ : syracuseStep 1295801 = 971851) B971851
theorem B1295879 : Blo 860564 1295879 := bstep (se 1 (by rfl) ⟨971909, by rfl⟩ : syracuseStep 1295879 = 1943819) B1943819
theorem B2180641 : Blo 860564 2180641 := bstep (se 2 (by rfl) ⟨817740, by rfl⟩ : syracuseStep 2180641 = 1635481) B1635481
theorem B1295915 : Blo 860564 1295915 := bstep (se 1 (by rfl) ⟨971936, by rfl⟩ : syracuseStep 1295915 = 1943873) B1943873
theorem B968251 : Blo 860564 968251 := bstep (se 1 (by rfl) ⟨726188, by rfl⟩ : syracuseStep 968251 = 1452377) B1452377
theorem B1295945 : Blo 860564 1295945 := bstep (se 2 (by rfl) ⟨485979, by rfl⟩ : syracuseStep 1295945 = 971959) B971959
theorem B1296059 : Blo 860564 1296059 := bstep (se 1 (by rfl) ⟨972044, by rfl⟩ : syracuseStep 1296059 = 1944089) B1944089
theorem B1296119 : Blo 860564 1296119 := bstep (se 1 (by rfl) ⟨972089, by rfl⟩ : syracuseStep 1296119 = 1944179) B1944179
theorem B1296143 : Blo 860564 1296143 := bstep (se 1 (by rfl) ⟨972107, by rfl⟩ : syracuseStep 1296143 = 1944215) B1944215
theorem B1296185 : Blo 860564 1296185 := bstep (se 2 (by rfl) ⟨486069, by rfl⟩ : syracuseStep 1296185 = 972139) B972139
theorem B1296263 : Blo 860564 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B2803609 : Blo 860564 2803609 := bstep (se 2 (by rfl) ⟨1051353, by rfl⟩ : syracuseStep 2803609 = 2102707) B2102707
theorem B1296299 : Blo 860564 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B1296329 : Blo 860564 1296329 := bstep (se 2 (by rfl) ⟨486123, by rfl⟩ : syracuseStep 1296329 = 972247) B972247
theorem B968719 : Blo 860564 968719 := bstep (se 1 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 968719 = 1453079) B1453079
theorem B1296443 : Blo 860564 1296443 := bstep (se 1 (by rfl) ⟨972332, by rfl⟩ : syracuseStep 1296443 = 1944665) B1944665
theorem B2181239 : Blo 860564 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B1296503 : Blo 860564 1296503 := bstep (se 1 (by rfl) ⟨972377, by rfl⟩ : syracuseStep 1296503 = 1944755) B1944755
theorem B1165447 : Blo 860564 1165447 := bstep (se 1 (by rfl) ⟨874085, by rfl⟩ : syracuseStep 1165447 = 1748171) B1748171
theorem B1296527 : Blo 860564 1296527 := bstep (se 1 (by rfl) ⟨972395, by rfl⟩ : syracuseStep 1296527 = 1944791) B1944791
theorem B1296569 : Blo 860564 1296569 := bstep (se 2 (by rfl) ⟨486213, by rfl⟩ : syracuseStep 1296569 = 972427) B972427
theorem B3688649 : Blo 860564 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B3688685 : Blo 860564 3688685 := bstep (se 3 (by rfl) ⟨691628, by rfl⟩ : syracuseStep 3688685 = 1383257) B1383257
theorem B1296647 : Blo 860564 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B1296683 : Blo 860564 1296683 := bstep (se 1 (by rfl) ⟨972512, by rfl⟩ : syracuseStep 1296683 = 1945025) B1945025
theorem B1296713 : Blo 860564 1296713 := bstep (se 2 (by rfl) ⟨486267, by rfl⟩ : syracuseStep 1296713 = 972535) B972535
theorem B1657273 : Blo 860564 1657273 := bstep (se 2 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 1657273 = 1242955) B1242955
theorem B1296827 : Blo 860564 1296827 := bstep (se 1 (by rfl) ⟨972620, by rfl⟩ : syracuseStep 1296827 = 1945241) B1945241
theorem B969223 : Blo 860564 969223 := bstep (se 1 (by rfl) ⟨726917, by rfl⟩ : syracuseStep 969223 = 1453835) B1453835
theorem B4147885 : Blo 860564 4147885 := bstep (se 3 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 4147885 = 1555457) B1555457
theorem B969403 : Blo 860564 969403 := bstep (se 1 (by rfl) ⟨727052, by rfl⟩ : syracuseStep 969403 = 1454105) B1454105
theorem B3689401 : Blo 860564 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B969871 : Blo 860564 969871 := bstep (se 1 (by rfl) ⟨727403, by rfl⟩ : syracuseStep 969871 = 1454807) B1454807
theorem B63688037 : Blo 860564 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B2182535 : Blo 860564 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B2182585 : Blo 860564 2182585 := bstep (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) B1636939
theorem B1166891 : Blo 860564 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B2805367 : Blo 860564 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B970375 : Blo 860564 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B4902707 : Blo 860564 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B970555 : Blo 860564 970555 := bstep (se 1 (by rfl) ⟨727916, by rfl⟩ : syracuseStep 970555 = 1455833) B1455833
theorem B21221189 : Blo 860564 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B2838419 : Blo 860564 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B2183183 : Blo 860564 2183183 := bstep (se 1 (by rfl) ⟨1637387, by rfl⟩ : syracuseStep 2183183 = 3274775) B3274775
theorem B971023 : Blo 860564 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B5525981 : Blo 860564 5525981 := bstep (se 3 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 5525981 = 2072243) B2072243
theorem B2904605 : Blo 860564 2904605 := bstep (se 3 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 2904605 = 1089227) B1089227
theorem B2183881 : Blo 860564 2183881 := bstep (se 2 (by rfl) ⟨818955, by rfl⟩ : syracuseStep 2183881 = 1637911) B1637911
theorem B971527 : Blo 860564 971527 := bstep (se 1 (by rfl) ⟨728645, by rfl⟩ : syracuseStep 971527 = 1457291) B1457291
theorem B2184023 : Blo 860564 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B7000921 : Blo 860564 7000921 := bstep (se 2 (by rfl) ⟨2625345, by rfl⟩ : syracuseStep 7000921 = 5250691) B5250691
theorem B971707 : Blo 860564 971707 := bstep (se 1 (by rfl) ⟨728780, by rfl⟩ : syracuseStep 971707 = 1457561) B1457561
theorem B6640663 : Blo 860564 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B1660105 : Blo 860564 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B4904165 : Blo 860564 4904165 := bstep (se 4 (by rfl) ⟨459765, by rfl⟩ : syracuseStep 4904165 = 919531) B919531
theorem B3691777 : Blo 860564 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B11785607 : Blo 860564 11785607 := bstep (se 1 (by rfl) ⟨8839205, by rfl⟩ : syracuseStep 11785607 = 17678411) B17678411
theorem B972175 : Blo 860564 972175 := bstep (se 1 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 972175 = 1458263) B1458263
theorem B4904621 : Blo 860564 4904621 := bstep (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) B1839233
theorem B23025329 : Blo 860564 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B11032321 : Blo 860564 11032321 := bstep (se 2 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 11032321 = 8274241) B8274241
theorem B37279601 : Blo 860564 37279601 := bstep (se 2 (by rfl) ⟨13979850, by rfl⟩ : syracuseStep 37279601 = 27959701) B27959701
theorem B35346293 : Blo 860564 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B2906009 : Blo 860564 2906009 := bstep (se 2 (by rfl) ⟨1089753, by rfl⟩ : syracuseStep 2906009 = 2179507) B2179507
theorem B8411141 : Blo 860564 8411141 := bstep (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) B1577089
theorem B4905305 : Blo 860564 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B2906711 : Blo 860564 2906711 := bstep (se 1 (by rfl) ⟨2180033, by rfl⟩ : syracuseStep 2906711 = 4360067) B4360067
theorem B3496535 : Blo 860564 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B2186099 : Blo 860564 2186099 := bstep (se 1 (by rfl) ⟨1639574, by rfl⟩ : syracuseStep 2186099 = 3279149) B3279149
theorem B2907197 : Blo 860564 2907197 := bstep (se 3 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 2907197 = 1090199) B1090199
theorem B1662137 : Blo 860564 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B2186615 : Blo 860564 2186615 := bstep (se 1 (by rfl) ⟨1639961, by rfl⟩ : syracuseStep 2186615 = 3279923) B3279923
theorem B6643129 : Blo 860564 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B3792413 : Blo 860564 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B5529131 : Blo 860564 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B33185537 : Blo 860564 33185537 := bstep (se 2 (by rfl) ⟨12444576, by rfl⟩ : syracuseStep 33185537 = 24889153) B24889153
theorem B4153463 : Blo 860564 4153463 := bstep (se 1 (by rfl) ⟨3115097, by rfl⟩ : syracuseStep 4153463 = 6230195) B6230195
theorem B2187607 : Blo 860564 2187607 := bstep (se 1 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 2187607 = 3281411) B3281411
theorem B2908601 : Blo 860564 2908601 := bstep (se 2 (by rfl) ⟨1090725, by rfl⟩ : syracuseStep 2908601 = 2181451) B2181451
theorem B28041713 : Blo 860564 28041713 := bstep (se 2 (by rfl) ⟨10515642, by rfl⟩ : syracuseStep 28041713 = 21031285) B21031285
theorem B10478123 : Blo 860564 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B2187911 : Blo 860564 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B2188043 : Blo 860564 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B1401643 : Blo 860564 1401643 := bstep (se 1 (by rfl) ⟨1051232, by rfl⟩ : syracuseStep 1401643 = 2102465) B2102465
theorem B2909195 : Blo 860564 2909195 := bstep (se 1 (by rfl) ⟨2181896, by rfl⟩ : syracuseStep 2909195 = 4363793) B4363793
theorem B4416599 : Blo 860564 4416599 := bstep (se 1 (by rfl) ⟨3312449, by rfl⟩ : syracuseStep 4416599 = 6624899) B6624899
theorem B2909303 : Blo 860564 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B2450807 : Blo 860564 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B6383033 : Blo 860564 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B2909897 : Blo 860564 2909897 := bstep (se 2 (by rfl) ⟨1091211, by rfl⟩ : syracuseStep 2909897 = 2182423) B2182423
theorem B3270401 : Blo 860564 3270401 := bstep (se 2 (by rfl) ⟨1226400, by rfl⟩ : syracuseStep 3270401 = 2452801) B2452801
theorem B6219521 : Blo 860564 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B3270415 : Blo 860564 3270415 := bstep (se 1 (by rfl) ⟨2452811, by rfl⟩ : syracuseStep 3270415 = 4905623) B4905623
theorem B2910599 : Blo 860564 2910599 := bstep (se 1 (by rfl) ⟨2182949, by rfl⟩ : syracuseStep 2910599 = 4365899) B4365899
theorem B4418059 : Blo 860564 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B1108667 : Blo 860564 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B2910977 : Blo 860564 2910977 := bstep (se 2 (by rfl) ⟨1091616, by rfl⟩ : syracuseStep 2910977 = 2183233) B2183233
theorem B3271691 : Blo 860564 3271691 := bstep (se 1 (by rfl) ⟨2453768, by rfl⟩ : syracuseStep 3271691 = 4907537) B4907537
theorem B5893181 : Blo 860564 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B3927329 : Blo 860564 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B2911787 : Blo 860564 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B2453291 : Blo 860564 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B1634107 : Blo 860564 1634107 := bstep (se 1 (by rfl) ⟨1225580, by rfl⟩ : syracuseStep 1634107 = 2451161) B2451161
theorem B3272633 : Blo 860564 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B15921269 : Blo 860564 15921269 := bstep (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) B1492619
theorem B2617633 : Blo 860564 2617633 := bstep (se 2 (by rfl) ⟨981612, by rfl⟩ : syracuseStep 2617633 = 1963225) B1963225
theorem B1634593 : Blo 860564 1634593 := bstep (se 2 (by rfl) ⟨612972, by rfl⟩ : syracuseStep 1634593 = 1225945) B1225945
theorem B2454077 : Blo 860564 2454077 := bstep (se 3 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 2454077 = 920279) B920279
theorem B8417969 : Blo 860564 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B2913083 : Blo 860564 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B2454407 : Blo 860564 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B8287433 : Blo 860564 8287433 := bstep (se 2 (by rfl) ⟨3107787, by rfl⟩ : syracuseStep 8287433 = 6215575) B6215575
theorem B2913569 : Blo 860564 2913569 := bstep (se 2 (by rfl) ⟨1092588, by rfl⟩ : syracuseStep 2913569 = 2185177) B2185177
theorem B23950727 : Blo 860564 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1996217 : Blo 860564 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B1635785 : Blo 860564 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B5535539 : Blo 860564 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B2914163 : Blo 860564 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B7010327 : Blo 860564 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B1636499 : Blo 860564 1636499 := bstep (se 1 (by rfl) ⟨1227374, by rfl⟩ : syracuseStep 1636499 = 2454749) B2454749
theorem B1636537 : Blo 860564 1636537 := bstep (se 2 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 1636537 = 1227403) B1227403
theorem B3275275 : Blo 860564 3275275 := bstep (se 1 (by rfl) ⟨2456456, by rfl⟩ : syracuseStep 3275275 = 4912913) B4912913
theorem B1309303 : Blo 860564 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B2456183 : Blo 860564 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B7371557 : Blo 860564 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B3275579 : Blo 860564 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B5241689 : Blo 860564 5241689 := bstep (se 2 (by rfl) ⟨1965633, by rfl⟩ : syracuseStep 5241689 = 3931267) B3931267
theorem B4357313 : Blo 860564 4357313 := bstep (se 2 (by rfl) ⟨1633992, by rfl⟩ : syracuseStep 4357313 = 3267985) B3267985
theorem B3276065 : Blo 860564 3276065 := bstep (se 2 (by rfl) ⟨1228524, by rfl⟩ : syracuseStep 3276065 = 2457049) B2457049
theorem B3145169 : Blo 860564 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B7372241 : Blo 860564 7372241 := bstep (se 2 (by rfl) ⟨2764590, by rfl⟩ : syracuseStep 7372241 = 5529181) B5529181
theorem B2457175 : Blo 860564 2457175 := bstep (se 1 (by rfl) ⟨1842881, by rfl⟩ : syracuseStep 2457175 = 3685763) B3685763
theorem B1474363 : Blo 860564 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B4915079 : Blo 860564 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B5898269 : Blo 860564 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2916431 : Blo 860564 2916431 := bstep (se 1 (by rfl) ⟨2187323, by rfl⟩ : syracuseStep 2916431 = 4374647) B4374647
theorem B12419153 : Blo 860564 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B5898329 : Blo 860564 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B2916809 : Blo 860564 2916809 := bstep (se 2 (by rfl) ⟨1093803, by rfl⟩ : syracuseStep 2916809 = 2187607) B2187607
theorem B1639111 : Blo 860564 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B3277523 : Blo 860564 3277523 := bstep (se 1 (by rfl) ⟨2458142, by rfl⟩ : syracuseStep 3277523 = 4916285) B4916285
theorem B2917079 : Blo 860564 2917079 := bstep (se 1 (by rfl) ⟨2187809, by rfl⟩ : syracuseStep 2917079 = 4375619) B4375619
theorem B5538563 : Blo 860564 5538563 := bstep (se 1 (by rfl) ⟨4153922, by rfl⟩ : syracuseStep 5538563 = 8307845) B8307845
theorem B2917295 : Blo 860564 2917295 := bstep (se 1 (by rfl) ⟨2187971, by rfl⟩ : syracuseStep 2917295 = 4375943) B4375943
theorem B4359095 : Blo 860564 4359095 := bstep (se 1 (by rfl) ⟨3269321, by rfl⟩ : syracuseStep 4359095 = 6538643) B6538643
theorem B2458781 : Blo 860564 2458781 := bstep (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) B922043
theorem B1639673 : Blo 860564 1639673 := bstep (se 2 (by rfl) ⟨614877, by rfl⟩ : syracuseStep 1639673 = 1229755) B1229755
theorem B1312175 : Blo 860564 1312175 := bstep (se 1 (by rfl) ⟨984131, by rfl⟩ : syracuseStep 1312175 = 1968263) B1968263
theorem B1639855 : Blo 860564 1639855 := bstep (se 1 (by rfl) ⟨1229891, by rfl⟩ : syracuseStep 1639855 = 2459783) B2459783
theorem B2459099 : Blo 860564 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B2459123 : Blo 860564 2459123 := bstep (se 1 (by rfl) ⟨1844342, by rfl⟩ : syracuseStep 2459123 = 3688685) B3688685
theorem B3114521 : Blo 860564 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B4491421 : Blo 860564 4491421 := bstep (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) B1684283
theorem B4360553 : Blo 860564 4360553 := bstep (se 2 (by rfl) ⟨1635207, by rfl⟩ : syracuseStep 4360553 = 3270415) B3270415
theorem B3148157 : Blo 860564 3148157 := bstep (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) B1180559
theorem B3541391 : Blo 860564 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B3115529 : Blo 860564 3115529 := bstep (se 2 (by rfl) ⟨1168323, by rfl⟩ : syracuseStep 3115529 = 2336647) B2336647
theorem B3738145 : Blo 860564 3738145 := bstep (se 2 (by rfl) ⟨1401804, by rfl⟩ : syracuseStep 3738145 = 2803609) B2803609
theorem B1641131 : Blo 860564 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B1936403 : Blo 860564 1936403 := bstep (se 1 (by rfl) ⟨1452302, by rfl⟩ : syracuseStep 1936403 = 2904605) B2904605
theorem B47123531 : Blo 860564 47123531 := bstep (se 1 (by rfl) ⟨35342648, by rfl⟩ : syracuseStep 47123531 = 70685297) B70685297
theorem B3279953 : Blo 860564 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B6982949 : Blo 860564 6982949 := bstep (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) B1309303
theorem B1936745 : Blo 860564 1936745 := bstep (se 2 (by rfl) ⟨726279, by rfl⟩ : syracuseStep 1936745 = 1452559) B1452559
theorem B3280409 : Blo 860564 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B1379963 : Blo 860564 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B6295261 : Blo 860564 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B4919201 : Blo 860564 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B23564195 : Blo 860564 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B1937339 : Blo 860564 1937339 := bstep (se 1 (by rfl) ⟨1453004, by rfl⟩ : syracuseStep 1937339 = 2906009) B2906009
theorem B5607427 : Blo 860564 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B1937465 : Blo 860564 1937465 := bstep (se 2 (by rfl) ⟨726549, by rfl⟩ : syracuseStep 1937465 = 1453099) B1453099
theorem B4919453 : Blo 860564 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B7475429 : Blo 860564 7475429 := bstep (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) B1401643
theorem B1937807 : Blo 860564 1937807 := bstep (se 1 (by rfl) ⟨1453355, by rfl⟩ : syracuseStep 1937807 = 2906711) B2906711
theorem B2331023 : Blo 860564 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B3281593 : Blo 860564 3281593 := bstep (se 2 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 3281593 = 2461195) B2461195
theorem B1938131 : Blo 860564 1938131 := bstep (se 1 (by rfl) ⟨1453598, by rfl⟩ : syracuseStep 1938131 = 2907197) B2907197
theorem B10490579 : Blo 860564 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B24843023 : Blo 860564 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B3740489 : Blo 860564 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B2528275 : Blo 860564 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B22123691 : Blo 860564 22123691 := bstep (se 1 (by rfl) ⟨16592768, by rfl⟩ : syracuseStep 22123691 = 33185537) B33185537
theorem B2070041 : Blo 860564 2070041 := bstep (se 2 (by rfl) ⟨776265, by rfl⟩ : syracuseStep 2070041 = 1552531) B1552531
theorem B1939067 : Blo 860564 1939067 := bstep (se 1 (by rfl) ⟨1454300, by rfl⟩ : syracuseStep 1939067 = 2908601) B2908601
theorem B1382059 : Blo 860564 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B6985415 : Blo 860564 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B1939193 : Blo 860564 1939193 := bstep (se 2 (by rfl) ⟨727197, by rfl⟩ : syracuseStep 1939193 = 1454395) B1454395
theorem B1939463 : Blo 860564 1939463 := bstep (se 1 (by rfl) ⟨1454597, by rfl⟩ : syracuseStep 1939463 = 2909195) B2909195
theorem B1939535 : Blo 860564 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B4921661 : Blo 860564 4921661 := bstep (se 3 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 4921661 = 1845623) B1845623
theorem B8853893 : Blo 860564 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B1939931 : Blo 860564 1939931 := bstep (se 1 (by rfl) ⟨1454948, by rfl⟩ : syracuseStep 1939931 = 2909897) B2909897
theorem B3152423 : Blo 860564 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B8854217 : Blo 860564 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B2628425 : Blo 860564 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B1940399 : Blo 860564 1940399 := bstep (se 1 (by rfl) ⟨1455299, by rfl⟩ : syracuseStep 1940399 = 2910599) B2910599
theorem B4922369 : Blo 860564 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B2956445 : Blo 860564 2956445 := bstep (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) B1108667
theorem B1940651 : Blo 860564 1940651 := bstep (se 1 (by rfl) ⟨1455488, by rfl⟩ : syracuseStep 1940651 = 2910977) B2910977
theorem B1941191 : Blo 860564 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B5611373 : Blo 860564 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B5251229 : Blo 860564 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B2760875 : Blo 860564 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B860591 : Blo 860564 860591 := bstep (se 1 (by rfl) ⟨645443, by rfl⟩ : syracuseStep 860591 = 1290887) B1290887
theorem B860615 : Blo 860564 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B5611979 : Blo 860564 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B860635 : Blo 860564 860635 := bstep (se 1 (by rfl) ⟨645476, by rfl⟩ : syracuseStep 860635 = 1290953) B1290953
theorem B860711 : Blo 860564 860711 := bstep (se 1 (by rfl) ⟨645533, by rfl⟩ : syracuseStep 860711 = 1291067) B1291067
theorem B1942055 : Blo 860564 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B860751 : Blo 860564 860751 := bstep (se 1 (by rfl) ⟨645563, by rfl⟩ : syracuseStep 860751 = 1291127) B1291127
theorem B860767 : Blo 860564 860767 := bstep (se 1 (by rfl) ⟨645575, by rfl⟩ : syracuseStep 860767 = 1291151) B1291151
theorem B860795 : Blo 860564 860795 := bstep (se 1 (by rfl) ⟨645596, by rfl⟩ : syracuseStep 860795 = 1291193) B1291193
theorem B860847 : Blo 860564 860847 := bstep (se 1 (by rfl) ⟨645635, by rfl⟩ : syracuseStep 860847 = 1291271) B1291271
theorem B4367033 : Blo 860564 4367033 := bstep (se 2 (by rfl) ⟨1637637, by rfl⟩ : syracuseStep 4367033 = 3275275) B3275275
theorem B860871 : Blo 860564 860871 := bstep (se 1 (by rfl) ⟨645653, by rfl⟩ : syracuseStep 860871 = 1291307) B1291307
theorem B3678929 : Blo 860564 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B860891 : Blo 860564 860891 := bstep (se 1 (by rfl) ⟨645668, by rfl⟩ : syracuseStep 860891 = 1291337) B1291337
theorem B860967 : Blo 860564 860967 := bstep (se 1 (by rfl) ⟨645725, by rfl⟩ : syracuseStep 860967 = 1291451) B1291451
theorem B861007 : Blo 860564 861007 := bstep (se 1 (by rfl) ⟨645755, by rfl⟩ : syracuseStep 861007 = 1291511) B1291511
theorem B861023 : Blo 860564 861023 := bstep (se 1 (by rfl) ⟨645767, by rfl⟩ : syracuseStep 861023 = 1291535) B1291535
theorem B1942379 : Blo 860564 1942379 := bstep (se 1 (by rfl) ⟨1456784, by rfl⟩ : syracuseStep 1942379 = 2913569) B2913569
theorem B861051 : Blo 860564 861051 := bstep (se 1 (by rfl) ⟨645788, by rfl⟩ : syracuseStep 861051 = 1291577) B1291577
theorem B1942433 : Blo 860564 1942433 := bstep (se 2 (by rfl) ⟨728412, by rfl⟩ : syracuseStep 1942433 = 1456825) B1456825
theorem B861103 : Blo 860564 861103 := bstep (se 1 (by rfl) ⟨645827, by rfl⟩ : syracuseStep 861103 = 1291655) B1291655
theorem B15967151 : Blo 860564 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B2368439 : Blo 860564 2368439 := bstep (se 1 (by rfl) ⟨1776329, by rfl⟩ : syracuseStep 2368439 = 3552659) B3552659
theorem B861127 : Blo 860564 861127 := bstep (se 1 (by rfl) ⟨645845, by rfl⟩ : syracuseStep 861127 = 1291691) B1291691
theorem B861147 : Blo 860564 861147 := bstep (se 1 (by rfl) ⟨645860, by rfl⟩ : syracuseStep 861147 = 1291721) B1291721
theorem B1090523 : Blo 860564 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B861223 : Blo 860564 861223 := bstep (se 1 (by rfl) ⟨645917, by rfl⟩ : syracuseStep 861223 = 1291835) B1291835
theorem B861263 : Blo 860564 861263 := bstep (se 1 (by rfl) ⟨645947, by rfl⟩ : syracuseStep 861263 = 1291895) B1291895
theorem B861279 : Blo 860564 861279 := bstep (se 1 (by rfl) ⟨645959, by rfl⟩ : syracuseStep 861279 = 1291919) B1291919
theorem B861307 : Blo 860564 861307 := bstep (se 1 (by rfl) ⟨645980, by rfl⟩ : syracuseStep 861307 = 1291961) B1291961
theorem B861359 : Blo 860564 861359 := bstep (se 1 (by rfl) ⟨646019, by rfl⟩ : syracuseStep 861359 = 1292039) B1292039
theorem B861383 : Blo 860564 861383 := bstep (se 1 (by rfl) ⟨646037, by rfl⟩ : syracuseStep 861383 = 1292075) B1292075
theorem B861403 : Blo 860564 861403 := bstep (se 1 (by rfl) ⟨646052, by rfl⟩ : syracuseStep 861403 = 1292105) B1292105
theorem B1942775 : Blo 860564 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B861479 : Blo 860564 861479 := bstep (se 1 (by rfl) ⟨646109, by rfl⟩ : syracuseStep 861479 = 1292219) B1292219
theorem B861519 : Blo 860564 861519 := bstep (se 1 (by rfl) ⟨646139, by rfl⟩ : syracuseStep 861519 = 1292279) B1292279
theorem B861535 : Blo 860564 861535 := bstep (se 1 (by rfl) ⟨646151, by rfl⟩ : syracuseStep 861535 = 1292303) B1292303
theorem B861563 : Blo 860564 861563 := bstep (se 1 (by rfl) ⟨646172, by rfl⟩ : syracuseStep 861563 = 1292345) B1292345
theorem B3679613 : Blo 860564 3679613 := bstep (se 3 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 3679613 = 1379855) B1379855
theorem B861615 : Blo 860564 861615 := bstep (se 1 (by rfl) ⟨646211, by rfl⟩ : syracuseStep 861615 = 1292423) B1292423
theorem B1090999 : Blo 860564 1090999 := bstep (se 1 (by rfl) ⟨818249, by rfl⟩ : syracuseStep 1090999 = 1636499) B1636499
theorem B861639 : Blo 860564 861639 := bstep (se 1 (by rfl) ⟨646229, by rfl⟩ : syracuseStep 861639 = 1292459) B1292459
theorem B861659 : Blo 860564 861659 := bstep (se 1 (by rfl) ⟨646244, by rfl⟩ : syracuseStep 861659 = 1292489) B1292489
theorem B861735 : Blo 860564 861735 := bstep (se 1 (by rfl) ⟨646301, by rfl⟩ : syracuseStep 861735 = 1292603) B1292603
theorem B861775 : Blo 860564 861775 := bstep (se 1 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 861775 = 1292663) B1292663
theorem B861791 : Blo 860564 861791 := bstep (se 1 (by rfl) ⟨646343, by rfl⟩ : syracuseStep 861791 = 1292687) B1292687
theorem B63710819 : Blo 860564 63710819 := bstep (se 1 (by rfl) ⟨47783114, by rfl⟩ : syracuseStep 63710819 = 95566229) B95566229
theorem B861819 : Blo 860564 861819 := bstep (se 1 (by rfl) ⟨646364, by rfl⟩ : syracuseStep 861819 = 1292729) B1292729
theorem B2762387 : Blo 860564 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B861871 : Blo 860564 861871 := bstep (se 1 (by rfl) ⟨646403, by rfl⟩ : syracuseStep 861871 = 1292807) B1292807
theorem B861895 : Blo 860564 861895 := bstep (se 1 (by rfl) ⟨646421, by rfl⟩ : syracuseStep 861895 = 1292843) B1292843
theorem B861915 : Blo 860564 861915 := bstep (se 1 (by rfl) ⟨646436, by rfl⟩ : syracuseStep 861915 = 1292873) B1292873
theorem B861991 : Blo 860564 861991 := bstep (se 1 (by rfl) ⟨646493, by rfl⟩ : syracuseStep 861991 = 1292987) B1292987
theorem B1943369 : Blo 860564 1943369 := bstep (se 2 (by rfl) ⟨728763, by rfl⟩ : syracuseStep 1943369 = 1457527) B1457527
theorem B862031 : Blo 860564 862031 := bstep (se 1 (by rfl) ⟨646523, by rfl⟩ : syracuseStep 862031 = 1293047) B1293047
theorem B862047 : Blo 860564 862047 := bstep (se 1 (by rfl) ⟨646535, by rfl⟩ : syracuseStep 862047 = 1293071) B1293071
theorem B2762591 : Blo 860564 2762591 := bstep (se 1 (by rfl) ⟨2071943, by rfl⟩ : syracuseStep 2762591 = 4143887) B4143887
theorem B862075 : Blo 860564 862075 := bstep (se 1 (by rfl) ⟨646556, by rfl⟩ : syracuseStep 862075 = 1293113) B1293113
theorem B8857505 : Blo 860564 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B862127 : Blo 860564 862127 := bstep (se 1 (by rfl) ⟨646595, by rfl⟩ : syracuseStep 862127 = 1293191) B1293191
theorem B862151 : Blo 860564 862151 := bstep (se 1 (by rfl) ⟨646613, by rfl⟩ : syracuseStep 862151 = 1293227) B1293227
theorem B862171 : Blo 860564 862171 := bstep (se 1 (by rfl) ⟨646628, by rfl⟩ : syracuseStep 862171 = 1293257) B1293257
theorem B862247 : Blo 860564 862247 := bstep (se 1 (by rfl) ⟨646685, by rfl⟩ : syracuseStep 862247 = 1293371) B1293371
theorem B862287 : Blo 860564 862287 := bstep (se 1 (by rfl) ⟨646715, by rfl⟩ : syracuseStep 862287 = 1293431) B1293431
theorem B862303 : Blo 860564 862303 := bstep (se 1 (by rfl) ⟨646727, by rfl⟩ : syracuseStep 862303 = 1293455) B1293455
theorem B862331 : Blo 860564 862331 := bstep (se 1 (by rfl) ⟨646748, by rfl⟩ : syracuseStep 862331 = 1293497) B1293497
theorem B4728989 : Blo 860564 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B862383 : Blo 860564 862383 := bstep (se 1 (by rfl) ⟨646787, by rfl⟩ : syracuseStep 862383 = 1293575) B1293575
theorem B862407 : Blo 860564 862407 := bstep (se 1 (by rfl) ⟨646805, by rfl⟩ : syracuseStep 862407 = 1293611) B1293611
theorem B862427 : Blo 860564 862427 := bstep (se 1 (by rfl) ⟨646820, by rfl⟩ : syracuseStep 862427 = 1293641) B1293641
theorem B862503 : Blo 860564 862503 := bstep (se 1 (by rfl) ⟨646877, by rfl⟩ : syracuseStep 862503 = 1293755) B1293755
theorem B862543 : Blo 860564 862543 := bstep (se 1 (by rfl) ⟨646907, by rfl⟩ : syracuseStep 862543 = 1293815) B1293815
theorem B862559 : Blo 860564 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B862587 : Blo 860564 862587 := bstep (se 1 (by rfl) ⟨646940, by rfl⟩ : syracuseStep 862587 = 1293881) B1293881
theorem B1452431 : Blo 860564 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B862639 : Blo 860564 862639 := bstep (se 1 (by rfl) ⟨646979, by rfl⟩ : syracuseStep 862639 = 1293959) B1293959
theorem B862663 : Blo 860564 862663 := bstep (se 1 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 862663 = 1293995) B1293995
theorem B862683 : Blo 860564 862683 := bstep (se 1 (by rfl) ⟨647012, by rfl⟩ : syracuseStep 862683 = 1294025) B1294025
theorem B862759 : Blo 860564 862759 := bstep (se 1 (by rfl) ⟨647069, by rfl⟩ : syracuseStep 862759 = 1294139) B1294139
theorem B862799 : Blo 860564 862799 := bstep (se 1 (by rfl) ⟨647099, by rfl⟩ : syracuseStep 862799 = 1294199) B1294199
theorem B862815 : Blo 860564 862815 := bstep (se 1 (by rfl) ⟨647111, by rfl⟩ : syracuseStep 862815 = 1294223) B1294223
theorem B1944161 : Blo 860564 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B1452667 : Blo 860564 1452667 := bstep (se 1 (by rfl) ⟨1089500, by rfl⟩ : syracuseStep 1452667 = 2179001) B2179001
theorem B862843 : Blo 860564 862843 := bstep (se 1 (by rfl) ⟨647132, by rfl⟩ : syracuseStep 862843 = 1294265) B1294265
theorem B862895 : Blo 860564 862895 := bstep (se 1 (by rfl) ⟨647171, by rfl⟩ : syracuseStep 862895 = 1294343) B1294343
theorem B862919 : Blo 860564 862919 := bstep (se 1 (by rfl) ⟨647189, by rfl⟩ : syracuseStep 862919 = 1294379) B1294379
theorem B1092295 : Blo 860564 1092295 := bstep (se 1 (by rfl) ⟨819221, by rfl⟩ : syracuseStep 1092295 = 1638443) B1638443
theorem B862939 : Blo 860564 862939 := bstep (se 1 (by rfl) ⟨647204, by rfl⟩ : syracuseStep 862939 = 1294409) B1294409
theorem B863015 : Blo 860564 863015 := bstep (se 1 (by rfl) ⟨647261, by rfl⟩ : syracuseStep 863015 = 1294523) B1294523
theorem B863055 : Blo 860564 863055 := bstep (se 1 (by rfl) ⟨647291, by rfl⟩ : syracuseStep 863055 = 1294583) B1294583
theorem B863071 : Blo 860564 863071 := bstep (se 1 (by rfl) ⟨647303, by rfl⟩ : syracuseStep 863071 = 1294607) B1294607
theorem B863099 : Blo 860564 863099 := bstep (se 1 (by rfl) ⟨647324, by rfl⟩ : syracuseStep 863099 = 1294649) B1294649
theorem B863151 : Blo 860564 863151 := bstep (se 1 (by rfl) ⟨647363, by rfl⟩ : syracuseStep 863151 = 1294727) B1294727
theorem B1944503 : Blo 860564 1944503 := bstep (se 1 (by rfl) ⟨1458377, by rfl⟩ : syracuseStep 1944503 = 2916755) B2916755
theorem B863175 : Blo 860564 863175 := bstep (se 1 (by rfl) ⟨647381, by rfl⟩ : syracuseStep 863175 = 1294763) B1294763
theorem B863195 : Blo 860564 863195 := bstep (se 1 (by rfl) ⟨647396, by rfl⟩ : syracuseStep 863195 = 1294793) B1294793
theorem B863271 : Blo 860564 863271 := bstep (se 1 (by rfl) ⟨647453, by rfl⟩ : syracuseStep 863271 = 1294907) B1294907
theorem B863311 : Blo 860564 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B863327 : Blo 860564 863327 := bstep (se 1 (by rfl) ⟨647495, by rfl⟩ : syracuseStep 863327 = 1294991) B1294991
theorem B863355 : Blo 860564 863355 := bstep (se 1 (by rfl) ⟨647516, by rfl⟩ : syracuseStep 863355 = 1295033) B1295033
theorem B863407 : Blo 860564 863407 := bstep (se 1 (by rfl) ⟨647555, by rfl⟩ : syracuseStep 863407 = 1295111) B1295111
theorem B863431 : Blo 860564 863431 := bstep (se 1 (by rfl) ⟨647573, by rfl⟩ : syracuseStep 863431 = 1295147) B1295147
theorem B863451 : Blo 860564 863451 := bstep (se 1 (by rfl) ⟨647588, by rfl⟩ : syracuseStep 863451 = 1295177) B1295177
theorem B863527 : Blo 860564 863527 := bstep (se 1 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 863527 = 1295291) B1295291
theorem B863567 : Blo 860564 863567 := bstep (se 1 (by rfl) ⟨647675, by rfl⟩ : syracuseStep 863567 = 1295351) B1295351
theorem B863583 : Blo 860564 863583 := bstep (se 1 (by rfl) ⟨647687, by rfl⟩ : syracuseStep 863583 = 1295375) B1295375
theorem B863611 : Blo 860564 863611 := bstep (se 1 (by rfl) ⟨647708, by rfl⟩ : syracuseStep 863611 = 1295417) B1295417
theorem B5615021 : Blo 860564 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B863663 : Blo 860564 863663 := bstep (se 1 (by rfl) ⟨647747, by rfl⟩ : syracuseStep 863663 = 1295495) B1295495
theorem B863687 : Blo 860564 863687 := bstep (se 1 (by rfl) ⟨647765, by rfl⟩ : syracuseStep 863687 = 1295531) B1295531
theorem B1453531 : Blo 860564 1453531 := bstep (se 1 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 1453531 = 2180297) B2180297
theorem B863707 : Blo 860564 863707 := bstep (se 1 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 863707 = 1295561) B1295561
theorem B1945097 : Blo 860564 1945097 := bstep (se 2 (by rfl) ⟨729411, by rfl⟩ : syracuseStep 1945097 = 1458823) B1458823
theorem B863783 : Blo 860564 863783 := bstep (se 1 (by rfl) ⟨647837, by rfl⟩ : syracuseStep 863783 = 1295675) B1295675
theorem B863823 : Blo 860564 863823 := bstep (se 1 (by rfl) ⟨647867, by rfl⟩ : syracuseStep 863823 = 1295735) B1295735
theorem B863839 : Blo 860564 863839 := bstep (se 1 (by rfl) ⟨647879, by rfl⟩ : syracuseStep 863839 = 1295759) B1295759
theorem B863867 : Blo 860564 863867 := bstep (se 1 (by rfl) ⟨647900, by rfl⟩ : syracuseStep 863867 = 1295801) B1295801
theorem B863919 : Blo 860564 863919 := bstep (se 1 (by rfl) ⟨647939, by rfl⟩ : syracuseStep 863919 = 1295879) B1295879
theorem B863943 : Blo 860564 863943 := bstep (se 1 (by rfl) ⟨647957, by rfl⟩ : syracuseStep 863943 = 1295915) B1295915
theorem B863963 : Blo 860564 863963 := bstep (se 1 (by rfl) ⟨647972, by rfl⟩ : syracuseStep 863963 = 1295945) B1295945
theorem B864039 : Blo 860564 864039 := bstep (se 1 (by rfl) ⟨648029, by rfl⟩ : syracuseStep 864039 = 1296059) B1296059
theorem B864079 : Blo 860564 864079 := bstep (se 1 (by rfl) ⟨648059, by rfl⟩ : syracuseStep 864079 = 1296119) B1296119
theorem B864095 : Blo 860564 864095 := bstep (se 1 (by rfl) ⟨648071, by rfl⟩ : syracuseStep 864095 = 1296143) B1296143
theorem B3321719 : Blo 860564 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B864123 : Blo 860564 864123 := bstep (se 1 (by rfl) ⟨648092, by rfl⟩ : syracuseStep 864123 = 1296185) B1296185
theorem B864175 : Blo 860564 864175 := bstep (se 1 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 864175 = 1296263) B1296263
theorem B864199 : Blo 860564 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B864219 : Blo 860564 864219 := bstep (se 1 (by rfl) ⟨648164, by rfl⟩ : syracuseStep 864219 = 1296329) B1296329
theorem B864295 : Blo 860564 864295 := bstep (se 1 (by rfl) ⟨648221, by rfl⟩ : syracuseStep 864295 = 1296443) B1296443
theorem B3682361 : Blo 860564 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B1454159 : Blo 860564 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B864335 : Blo 860564 864335 := bstep (se 1 (by rfl) ⟨648251, by rfl⟩ : syracuseStep 864335 = 1296503) B1296503
theorem B864351 : Blo 860564 864351 := bstep (se 1 (by rfl) ⟨648263, by rfl⟩ : syracuseStep 864351 = 1296527) B1296527
theorem B864379 : Blo 860564 864379 := bstep (se 1 (by rfl) ⟨648284, by rfl⟩ : syracuseStep 864379 = 1296569) B1296569
theorem B864431 : Blo 860564 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B864455 : Blo 860564 864455 := bstep (se 1 (by rfl) ⟨648341, by rfl⟩ : syracuseStep 864455 = 1296683) B1296683
theorem B864475 : Blo 860564 864475 := bstep (se 1 (by rfl) ⟨648356, by rfl⟩ : syracuseStep 864475 = 1296713) B1296713
theorem B864551 : Blo 860564 864551 := bstep (se 1 (by rfl) ⟨648413, by rfl⟩ : syracuseStep 864551 = 1296827) B1296827
theorem B1290875 : Blo 860564 1290875 := bstep (se 1 (by rfl) ⟨968156, by rfl⟩ : syracuseStep 1290875 = 1936313) B1936313
theorem B1225415 : Blo 860564 1225415 := bstep (se 1 (by rfl) ⟨919061, by rfl⟩ : syracuseStep 1225415 = 1838123) B1838123
theorem B1291001 : Blo 860564 1291001 := bstep (se 2 (by rfl) ⟨484125, by rfl⟩ : syracuseStep 1291001 = 968251) B968251
theorem B102413069 : Blo 860564 102413069 := bstep (se 3 (by rfl) ⟨19202450, by rfl⟩ : syracuseStep 102413069 = 38404901) B38404901
theorem B1291103 : Blo 860564 1291103 := bstep (se 1 (by rfl) ⟨968327, by rfl⟩ : syracuseStep 1291103 = 1936655) B1936655
theorem B1291115 : Blo 860564 1291115 := bstep (se 1 (by rfl) ⟨968336, by rfl⟩ : syracuseStep 1291115 = 1936673) B1936673
theorem B1455023 : Blo 860564 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B7877681 : Blo 860564 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B1291343 : Blo 860564 1291343 := bstep (se 1 (by rfl) ⟨968507, by rfl⟩ : syracuseStep 1291343 = 1937015) B1937015
theorem B1291463 : Blo 860564 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B1455455 : Blo 860564 1455455 := bstep (se 1 (by rfl) ⟨1091591, by rfl⟩ : syracuseStep 1455455 = 2183183) B2183183
theorem B1291625 : Blo 860564 1291625 := bstep (se 2 (by rfl) ⟨484359, by rfl⟩ : syracuseStep 1291625 = 968719) B968719
theorem B1291703 : Blo 860564 1291703 := bstep (se 1 (by rfl) ⟨968777, by rfl⟩ : syracuseStep 1291703 = 1937555) B1937555
theorem B1291739 : Blo 860564 1291739 := bstep (se 1 (by rfl) ⟨968804, by rfl⟩ : syracuseStep 1291739 = 1937609) B1937609
theorem B3683987 : Blo 860564 3683987 := bstep (se 1 (by rfl) ⟨2762990, by rfl⟩ : syracuseStep 3683987 = 5525981) B5525981
theorem B4372217 : Blo 860564 4372217 := bstep (se 2 (by rfl) ⟨1639581, by rfl⟩ : syracuseStep 4372217 = 3279163) B3279163
theorem B6207299 : Blo 860564 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B1554319 : Blo 860564 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B1456015 : Blo 860564 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B2209697 : Blo 860564 2209697 := bstep (se 2 (by rfl) ⟨828636, by rfl⟩ : syracuseStep 2209697 = 1657273) B1657273
theorem B1292207 : Blo 860564 1292207 := bstep (se 1 (by rfl) ⟨969155, by rfl⟩ : syracuseStep 1292207 = 1938311) B1938311
theorem B1292297 : Blo 860564 1292297 := bstep (se 2 (by rfl) ⟨484611, by rfl⟩ : syracuseStep 1292297 = 969223) B969223
theorem B1292327 : Blo 860564 1292327 := bstep (se 1 (by rfl) ⟨969245, by rfl⟩ : syracuseStep 1292327 = 1938491) B1938491
theorem B5519441 : Blo 860564 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B14727257 : Blo 860564 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B1292411 : Blo 860564 1292411 := bstep (se 1 (by rfl) ⟨969308, by rfl⟩ : syracuseStep 1292411 = 1938617) B1938617
theorem B1292537 : Blo 860564 1292537 := bstep (se 2 (by rfl) ⟨484701, by rfl⟩ : syracuseStep 1292537 = 969403) B969403
theorem B1292639 : Blo 860564 1292639 := bstep (se 1 (by rfl) ⟨969479, by rfl⟩ : syracuseStep 1292639 = 1938959) B1938959
theorem B1292651 : Blo 860564 1292651 := bstep (se 1 (by rfl) ⟨969488, by rfl⟩ : syracuseStep 1292651 = 1938977) B1938977
theorem B4372865 : Blo 860564 4372865 := bstep (se 2 (by rfl) ⟨1639824, by rfl⟩ : syracuseStep 4372865 = 3279649) B3279649
theorem B15350219 : Blo 860564 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1456697 : Blo 860564 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B24853067 : Blo 860564 24853067 := bstep (se 1 (by rfl) ⟨18639800, by rfl⟩ : syracuseStep 24853067 = 37279601) B37279601
theorem B1292879 : Blo 860564 1292879 := bstep (se 1 (by rfl) ⟨969659, by rfl⟩ : syracuseStep 1292879 = 1939319) B1939319
theorem B1292999 : Blo 860564 1292999 := bstep (se 1 (by rfl) ⟨969749, by rfl⟩ : syracuseStep 1292999 = 1939499) B1939499
theorem B1293161 : Blo 860564 1293161 := bstep (se 2 (by rfl) ⟨484935, by rfl⟩ : syracuseStep 1293161 = 969871) B969871
theorem B1293239 : Blo 860564 1293239 := bstep (se 1 (by rfl) ⟨969929, by rfl⟩ : syracuseStep 1293239 = 1939859) B1939859
theorem B1293275 : Blo 860564 1293275 := bstep (se 1 (by rfl) ⟨969956, by rfl⟩ : syracuseStep 1293275 = 1939913) B1939913
theorem B1227739 : Blo 860564 1227739 := bstep (se 1 (by rfl) ⟨920804, by rfl⟩ : syracuseStep 1227739 = 1841609) B1841609
theorem B4373675 : Blo 860564 4373675 := bstep (se 1 (by rfl) ⟨3280256, by rfl⟩ : syracuseStep 4373675 = 6560513) B6560513
theorem B1457399 : Blo 860564 1457399 := bstep (se 1 (by rfl) ⟨1093049, by rfl⟩ : syracuseStep 1457399 = 2186099) B2186099
theorem B1293743 : Blo 860564 1293743 := bstep (se 1 (by rfl) ⟨970307, by rfl⟩ : syracuseStep 1293743 = 1940615) B1940615
theorem B1293833 : Blo 860564 1293833 := bstep (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) B970375
theorem B1228297 : Blo 860564 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B1293863 : Blo 860564 1293863 := bstep (se 1 (by rfl) ⟨970397, by rfl⟩ : syracuseStep 1293863 = 1940795) B1940795
theorem B1457743 : Blo 860564 1457743 := bstep (se 1 (by rfl) ⟨1093307, by rfl⟩ : syracuseStep 1457743 = 2186615) B2186615
theorem B3685985 : Blo 860564 3685985 := bstep (se 2 (by rfl) ⟨1382244, by rfl⟩ : syracuseStep 3685985 = 2764489) B2764489
theorem B1293947 : Blo 860564 1293947 := bstep (se 1 (by rfl) ⟨970460, by rfl⟩ : syracuseStep 1293947 = 1940921) B1940921
theorem B4374161 : Blo 860564 4374161 := bstep (se 2 (by rfl) ⟨1640310, by rfl⟩ : syracuseStep 4374161 = 3280621) B3280621
theorem B3686087 : Blo 860564 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B2178809 : Blo 860564 2178809 := bstep (se 2 (by rfl) ⟨817053, by rfl⟩ : syracuseStep 2178809 = 1634107) B1634107
theorem B1294073 : Blo 860564 1294073 := bstep (se 2 (by rfl) ⟨485277, by rfl⟩ : syracuseStep 1294073 = 970555) B970555
theorem B1457993 : Blo 860564 1457993 := bstep (se 2 (by rfl) ⟨546747, by rfl⟩ : syracuseStep 1457993 = 1093495) B1093495
theorem B1294175 : Blo 860564 1294175 := bstep (se 1 (by rfl) ⟨970631, by rfl⟩ : syracuseStep 1294175 = 1941263) B1941263
theorem B1294187 : Blo 860564 1294187 := bstep (se 1 (by rfl) ⟨970640, by rfl⟩ : syracuseStep 1294187 = 1941281) B1941281
theorem B2768897 : Blo 860564 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B1294415 : Blo 860564 1294415 := bstep (se 1 (by rfl) ⟨970811, by rfl⟩ : syracuseStep 1294415 = 1941623) B1941623
theorem B2768975 : Blo 860564 2768975 := bstep (se 1 (by rfl) ⟨2076731, by rfl⟩ : syracuseStep 2768975 = 4153463) B4153463
theorem B1294535 : Blo 860564 1294535 := bstep (se 1 (by rfl) ⟨970901, by rfl⟩ : syracuseStep 1294535 = 1941803) B1941803
theorem B1458425 : Blo 860564 1458425 := bstep (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) B1093819
theorem B18694475 : Blo 860564 18694475 := bstep (se 1 (by rfl) ⟨14020856, by rfl⟩ : syracuseStep 18694475 = 28041713) B28041713
theorem B1294697 : Blo 860564 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B3490177 : Blo 860564 3490177 := bstep (se 2 (by rfl) ⟨1308816, by rfl⟩ : syracuseStep 3490177 = 2617633) B2617633
theorem B2179457 : Blo 860564 2179457 := bstep (se 2 (by rfl) ⟨817296, by rfl⟩ : syracuseStep 2179457 = 1634593) B1634593
theorem B1458607 : Blo 860564 1458607 := bstep (se 1 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 1458607 = 2187911) B2187911
theorem B1294775 : Blo 860564 1294775 := bstep (se 1 (by rfl) ⟨971081, by rfl⟩ : syracuseStep 1294775 = 1942163) B1942163
theorem B1294811 : Blo 860564 1294811 := bstep (se 1 (by rfl) ⟨971108, by rfl⟩ : syracuseStep 1294811 = 1942217) B1942217
theorem B1458695 : Blo 860564 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B3326675 : Blo 860564 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B1295279 : Blo 860564 1295279 := bstep (se 1 (by rfl) ⟨971459, by rfl⟩ : syracuseStep 1295279 = 1942919) B1942919
theorem B1295369 : Blo 860564 1295369 := bstep (se 2 (by rfl) ⟨485763, by rfl⟩ : syracuseStep 1295369 = 971527) B971527
theorem B1295399 : Blo 860564 1295399 := bstep (se 1 (by rfl) ⟨971549, by rfl⟩ : syracuseStep 1295399 = 1943099) B1943099
theorem B1295483 : Blo 860564 1295483 := bstep (se 1 (by rfl) ⟨971612, by rfl⟩ : syracuseStep 1295483 = 1943225) B1943225
theorem B2180267 : Blo 860564 2180267 := bstep (se 1 (by rfl) ⟨1635200, by rfl⟩ : syracuseStep 2180267 = 3270401) B3270401
theorem B4146347 : Blo 860564 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B1295609 : Blo 860564 1295609 := bstep (se 2 (by rfl) ⟨485853, by rfl⟩ : syracuseStep 1295609 = 971707) B971707
theorem B33146171 : Blo 860564 33146171 := bstep (se 1 (by rfl) ⟨24859628, by rfl⟩ : syracuseStep 33146171 = 49719257) B49719257
theorem B1295711 : Blo 860564 1295711 := bstep (se 1 (by rfl) ⟨971783, by rfl⟩ : syracuseStep 1295711 = 1943567) B1943567
theorem B1295723 : Blo 860564 1295723 := bstep (se 1 (by rfl) ⟨971792, by rfl⟩ : syracuseStep 1295723 = 1943585) B1943585
theorem B6210989 : Blo 860564 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B16565705 : Blo 860564 16565705 := bstep (se 2 (by rfl) ⟨6212139, by rfl⟩ : syracuseStep 16565705 = 12424279) B12424279
theorem B1295951 : Blo 860564 1295951 := bstep (se 1 (by rfl) ⟨971963, by rfl⟩ : syracuseStep 1295951 = 1943927) B1943927
theorem B6211217 : Blo 860564 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B1296071 : Blo 860564 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B1296233 : Blo 860564 1296233 := bstep (se 2 (by rfl) ⟨486087, by rfl⟩ : syracuseStep 1296233 = 972175) B972175
theorem B4376429 : Blo 860564 4376429 := bstep (se 3 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 4376429 = 1641161) B1641161
theorem B1296311 : Blo 860564 1296311 := bstep (se 1 (by rfl) ⟨972233, by rfl⟩ : syracuseStep 1296311 = 1944467) B1944467
theorem B1296347 : Blo 860564 1296347 := bstep (se 1 (by rfl) ⟨972260, by rfl⟩ : syracuseStep 1296347 = 1944521) B1944521
theorem B2181127 : Blo 860564 2181127 := bstep (se 1 (by rfl) ⟨1635845, by rfl⟩ : syracuseStep 2181127 = 3271691) B3271691
theorem B4376591 : Blo 860564 4376591 := bstep (se 1 (by rfl) ⟨3282443, by rfl⟩ : syracuseStep 4376591 = 6564887) B6564887
theorem B7096349 : Blo 860564 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B968827 : Blo 860564 968827 := bstep (se 1 (by rfl) ⟨726620, by rfl⟩ : syracuseStep 968827 = 1453241) B1453241
theorem B4901249 : Blo 860564 4901249 := bstep (se 2 (by rfl) ⟨1837968, by rfl⟩ : syracuseStep 4901249 = 3675937) B3675937
theorem B1296815 : Blo 860564 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B969295 : Blo 860564 969295 := bstep (se 1 (by rfl) ⟨726971, by rfl⟩ : syracuseStep 969295 = 1453943) B1453943
theorem B2181755 : Blo 860564 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B4901705 : Blo 860564 4901705 := bstep (se 2 (by rfl) ⟨1838139, by rfl⟩ : syracuseStep 4901705 = 3676279) B3676279
theorem B1330025 : Blo 860564 1330025 := bstep (se 2 (by rfl) ⟨498759, by rfl⟩ : syracuseStep 1330025 = 997519) B997519
theorem B2182049 : Blo 860564 2182049 := bstep (se 2 (by rfl) ⟨818268, by rfl⟩ : syracuseStep 2182049 = 1636537) B1636537
theorem B969691 : Blo 860564 969691 := bstep (se 1 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 969691 = 1454537) B1454537
theorem B970159 : Blo 860564 970159 := bstep (se 1 (by rfl) ⟨727619, by rfl⟩ : syracuseStep 970159 = 1455239) B1455239
theorem B1035703 : Blo 860564 1035703 := bstep (se 1 (by rfl) ⟨776777, by rfl⟩ : syracuseStep 1035703 = 1553555) B1553555
theorem B5524955 : Blo 860564 5524955 := bstep (se 1 (by rfl) ⟨4143716, by rfl⟩ : syracuseStep 5524955 = 8287433) B8287433
theorem B1330811 : Blo 860564 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B970591 : Blo 860564 970591 := bstep (se 1 (by rfl) ⟨727943, by rfl⟩ : syracuseStep 970591 = 1455887) B1455887
theorem B3690359 : Blo 860564 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B5525441 : Blo 860564 5525441 := bstep (se 2 (by rfl) ⟨2072040, by rfl⟩ : syracuseStep 5525441 = 4144081) B4144081
theorem B4673551 : Blo 860564 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B970951 : Blo 860564 970951 := bstep (se 1 (by rfl) ⟨728213, by rfl⟩ : syracuseStep 970951 = 1456427) B1456427
theorem B2183719 : Blo 860564 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B3494459 : Blo 860564 3494459 := bstep (se 1 (by rfl) ⟨2620844, by rfl⟩ : syracuseStep 3494459 = 5241689) B5241689
theorem B2904875 : Blo 860564 2904875 := bstep (se 1 (by rfl) ⟨2178656, by rfl⟩ : syracuseStep 2904875 = 4357313) B4357313
theorem B2184043 : Blo 860564 2184043 := bstep (se 1 (by rfl) ⟨1638032, by rfl⟩ : syracuseStep 2184043 = 3276065) B3276065
theorem B971815 : Blo 860564 971815 := bstep (se 1 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 971815 = 1457723) B1457723
theorem B2905145 : Blo 860564 2905145 := bstep (se 2 (by rfl) ⟨1089429, by rfl⟩ : syracuseStep 2905145 = 2178859) B2178859
theorem B6542531 : Blo 860564 6542531 := bstep (se 1 (by rfl) ⟨4906898, by rfl⟩ : syracuseStep 6542531 = 9813797) B9813797
theorem B2905469 : Blo 860564 2905469 := bstep (se 3 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 2905469 = 1089551) B1089551
theorem B1496503 : Blo 860564 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B2184691 : Blo 860564 2184691 := bstep (se 1 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 2184691 = 3277037) B3277037
theorem B2905739 : Blo 860564 2905739 := bstep (se 1 (by rfl) ⟨2179304, by rfl⟩ : syracuseStep 2905739 = 4358609) B4358609
theorem B10508291 : Blo 860564 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B6215717 : Blo 860564 6215717 := bstep (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) B1165447
theorem B2906657 : Blo 860564 2906657 := bstep (se 2 (by rfl) ⟨1089996, by rfl⟩ : syracuseStep 2906657 = 2179993) B2179993
theorem B2185825 : Blo 860564 2185825 := bstep (se 2 (by rfl) ⟨819684, by rfl⟩ : syracuseStep 2185825 = 1639369) B1639369
theorem B8411849 : Blo 860564 8411849 := bstep (se 2 (by rfl) ⟨3154443, by rfl⟩ : syracuseStep 8411849 = 6308887) B6308887
theorem B2906873 : Blo 860564 2906873 := bstep (se 2 (by rfl) ⟨1090077, by rfl⟩ : syracuseStep 2906873 = 2180155) B2180155
theorem B3496733 : Blo 860564 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B2907143 : Blo 860564 2907143 := bstep (se 1 (by rfl) ⟨2180357, by rfl⟩ : syracuseStep 2907143 = 4360715) B4360715
theorem B3103763 : Blo 860564 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B2907251 : Blo 860564 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B1399931 : Blo 860564 1399931 := bstep (se 1 (by rfl) ⟨1049948, by rfl⟩ : syracuseStep 1399931 = 2099897) B2099897
theorem B16833809 : Blo 860564 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B2907521 : Blo 860564 2907521 := bstep (se 2 (by rfl) ⟨1090320, by rfl⟩ : syracuseStep 2907521 = 2180641) B2180641
theorem B2186777 : Blo 860564 2186777 := bstep (se 2 (by rfl) ⟨820041, by rfl⟩ : syracuseStep 2186777 = 1640083) B1640083
theorem B7003709 : Blo 860564 7003709 := bstep (se 3 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 7003709 = 2626391) B2626391
theorem B6217505 : Blo 860564 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B3268471 : Blo 860564 3268471 := bstep (se 1 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 3268471 = 4902707) B4902707
theorem B14147459 : Blo 860564 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B1892279 : Blo 860564 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B2187283 : Blo 860564 2187283 := bstep (se 1 (by rfl) ⟨1640462, by rfl⟩ : syracuseStep 2187283 = 3280925) B3280925
theorem B2908331 : Blo 860564 2908331 := bstep (se 1 (by rfl) ⟨2181248, by rfl⟩ : syracuseStep 2908331 = 4362497) B4362497
theorem B6218137 : Blo 860564 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B5890745 : Blo 860564 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B2908871 : Blo 860564 2908871 := bstep (se 1 (by rfl) ⟨2181653, by rfl⟩ : syracuseStep 2908871 = 4363307) B4363307
theorem B3269443 : Blo 860564 3269443 := bstep (se 1 (by rfl) ⟨2452082, by rfl⟩ : syracuseStep 3269443 = 4904165) B4904165
theorem B5530513 : Blo 860564 5530513 := bstep (se 2 (by rfl) ⟨2073942, by rfl⟩ : syracuseStep 5530513 = 4147885) B4147885
theorem B7857071 : Blo 860564 7857071 := bstep (se 1 (by rfl) ⟨5892803, by rfl⟩ : syracuseStep 7857071 = 11785607) B11785607
theorem B19948589 : Blo 860564 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B2188367 : Blo 860564 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B3269747 : Blo 860564 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B23553443 : Blo 860564 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B2909735 : Blo 860564 2909735 := bstep (se 1 (by rfl) ⟨2182301, by rfl⟩ : syracuseStep 2909735 = 4364603) B4364603
theorem B3270203 : Blo 860564 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B2909843 : Blo 860564 2909843 := bstep (se 1 (by rfl) ⟨2182382, by rfl⟩ : syracuseStep 2909843 = 4364765) B4364765
theorem B2910059 : Blo 860564 2910059 := bstep (se 1 (by rfl) ⟨2182544, by rfl⟩ : syracuseStep 2910059 = 4365089) B4365089
theorem B2910113 : Blo 860564 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B12412865 : Blo 860564 12412865 := bstep (se 2 (by rfl) ⟨4654824, by rfl⟩ : syracuseStep 12412865 = 9309649) B9309649
theorem B1108091 : Blo 860564 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B2910707 : Blo 860564 2910707 := bstep (se 1 (by rfl) ⟨2183030, by rfl⟩ : syracuseStep 2910707 = 4366061) B4366061
theorem B16608077 : Blo 860564 16608077 := bstep (se 3 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 16608077 = 6228029) B6228029
theorem B5532563 : Blo 860564 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B2911247 : Blo 860564 2911247 := bstep (se 1 (by rfl) ⟨2183435, by rfl⟩ : syracuseStep 2911247 = 4366871) B4366871
theorem B2944399 : Blo 860564 2944399 := bstep (se 1 (by rfl) ⟨2208299, by rfl⟩ : syracuseStep 2944399 = 4416599) B4416599
theorem B2453017 : Blo 860564 2453017 := bstep (se 2 (by rfl) ⟨919881, by rfl⟩ : syracuseStep 2453017 = 1839763) B1839763
theorem B3108377 : Blo 860564 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B1633871 : Blo 860564 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B2911841 : Blo 860564 2911841 := bstep (se 2 (by rfl) ⟨1091940, by rfl⟩ : syracuseStep 2911841 = 2183881) B2183881
theorem B4255355 : Blo 860564 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B9334561 : Blo 860564 9334561 := bstep (se 2 (by rfl) ⟨3500460, by rfl⟩ : syracuseStep 9334561 = 7000921) B7000921
theorem B6549821 : Blo 860564 6549821 := bstep (se 3 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 6549821 = 2456183) B2456183
theorem B6222521 : Blo 860564 6222521 := bstep (se 2 (by rfl) ⟨2333445, by rfl⟩ : syracuseStep 6222521 = 4666891) B4666891
theorem B3928787 : Blo 860564 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B2618219 : Blo 860564 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B14709761 : Blo 860564 14709761 := bstep (se 2 (by rfl) ⟨5516160, by rfl⟩ : syracuseStep 14709761 = 11032321) B11032321
theorem B3109907 : Blo 860564 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B2913299 : Blo 860564 2913299 := bstep (se 1 (by rfl) ⟨2184974, by rfl⟩ : syracuseStep 2913299 = 4369949) B4369949
theorem B1635527 : Blo 860564 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B2913623 : Blo 860564 2913623 := bstep (se 1 (by rfl) ⟨2185217, by rfl⟩ : syracuseStep 2913623 = 4370435) B4370435
theorem B10614179 : Blo 860564 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B1636051 : Blo 860564 1636051 := bstep (se 1 (by rfl) ⟨1227038, by rfl⟩ : syracuseStep 1636051 = 2454077) B2454077
theorem B7960313 : Blo 860564 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B35452673 : Blo 860564 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1636271 : Blo 860564 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B3110831 : Blo 860564 3110831 := bstep (se 1 (by rfl) ⟨2333123, by rfl⟩ : syracuseStep 3110831 = 4666247) B4666247
theorem B169834765 : Blo 860564 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B1636681 : Blo 860564 1636681 := bstep (se 2 (by rfl) ⟨613755, by rfl⟩ : syracuseStep 1636681 = 1227511) B1227511
theorem B2455933 : Blo 860564 2455933 := bstep (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) B920975
theorem B2914703 : Blo 860564 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B2915027 : Blo 860564 2915027 := bstep (se 1 (by rfl) ⟨2186270, by rfl⟩ : syracuseStep 2915027 = 4372541) B4372541
theorem B3275549 : Blo 860564 3275549 := bstep (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) B1228331
theorem B3111709 : Blo 860564 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B2653103 : Blo 860564 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B4914371 : Blo 860564 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B3276233 : Blo 860564 3276233 := bstep (se 2 (by rfl) ⟨1228587, by rfl⟩ : syracuseStep 3276233 = 2457175) B2457175
theorem B2096779 : Blo 860564 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B4914827 : Blo 860564 4914827 := bstep (se 1 (by rfl) ⟨3686120, by rfl⟩ : syracuseStep 4914827 = 7372241) B7372241
theorem B1965817 : Blo 860564 1965817 := bstep (se 2 (by rfl) ⟨737181, by rfl⟩ : syracuseStep 1965817 = 1474363) B1474363
theorem B2916215 : Blo 860564 2916215 := bstep (se 1 (by rfl) ⟨2187161, by rfl⟩ : syracuseStep 2916215 = 4374323) B4374323
theorem B3276719 : Blo 860564 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B2916377 : Blo 860564 2916377 := bstep (se 2 (by rfl) ⟨1093641, by rfl⟩ : syracuseStep 2916377 = 2187283) B2187283
theorem B3932219 : Blo 860564 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B15728717 : Blo 860564 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B4653569 : Blo 860564 4653569 := bstep (se 2 (by rfl) ⟨1745088, by rfl⟩ : syracuseStep 4653569 = 3490177) B3490177
theorem B8290849 : Blo 860564 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B1639187 : Blo 860564 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B11043803 : Blo 860564 11043803 := bstep (se 1 (by rfl) ⟨8282852, by rfl⟩ : syracuseStep 11043803 = 16565705) B16565705
theorem B1639415 : Blo 860564 1639415 := bstep (se 1 (by rfl) ⟨1229561, by rfl⟩ : syracuseStep 1639415 = 2459123) B2459123
theorem B4359257 : Blo 860564 4359257 := bstep (se 2 (by rfl) ⟨1634721, by rfl⟩ : syracuseStep 4359257 = 3269443) B3269443
theorem B7374017 : Blo 860564 7374017 := bstep (se 2 (by rfl) ⟨2765256, by rfl⟩ : syracuseStep 7374017 = 5530513) B5530513
theorem B2917619 : Blo 860564 2917619 := bstep (se 1 (by rfl) ⟨2188214, by rfl⟩ : syracuseStep 2917619 = 4376429) B4376429
theorem B2917727 : Blo 860564 2917727 := bstep (se 1 (by rfl) ⟨2188295, by rfl⟩ : syracuseStep 2917727 = 4376591) B4376591
theorem B2360927 : Blo 860564 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2460239 : Blo 860564 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B3279467 : Blo 860564 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B3279635 : Blo 860564 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B4983619 : Blo 860564 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B1936583 : Blo 860564 1936583 := bstep (se 1 (by rfl) ⟨1452437, by rfl⟩ : syracuseStep 1936583 = 2904875) B2904875
theorem B2493659 : Blo 860564 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B95816981 : Blo 860564 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B1936763 : Blo 860564 1936763 := bstep (se 1 (by rfl) ⟨1452572, by rfl⟩ : syracuseStep 1936763 = 2905145) B2905145
theorem B4984193 : Blo 860564 4984193 := bstep (se 2 (by rfl) ⟨1869072, by rfl⟩ : syracuseStep 4984193 = 3738145) B3738145
theorem B14749127 : Blo 860564 14749127 := bstep (se 1 (by rfl) ⟨11061845, by rfl⟩ : syracuseStep 14749127 = 22123691) B22123691
theorem B4361687 : Blo 860564 4361687 := bstep (se 1 (by rfl) ⟨3271265, by rfl⟩ : syracuseStep 4361687 = 6542531) B6542531
theorem B1936889 : Blo 860564 1936889 := bstep (se 2 (by rfl) ⟨726333, by rfl⟩ : syracuseStep 1936889 = 1452667) B1452667
theorem B1936979 : Blo 860564 1936979 := bstep (se 1 (by rfl) ⟨1452734, by rfl⟩ : syracuseStep 1936979 = 2905469) B2905469
theorem B1937159 : Blo 860564 1937159 := bstep (se 1 (by rfl) ⟨1452869, by rfl⟩ : syracuseStep 1937159 = 2905739) B2905739
theorem B4656943 : Blo 860564 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B6557597 : Blo 860564 6557597 := bstep (se 3 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 6557597 = 2459099) B2459099
theorem B3281107 : Blo 860564 3281107 := bstep (se 1 (by rfl) ⟨2460830, by rfl⟩ : syracuseStep 3281107 = 4921661) B4921661
theorem B5902595 : Blo 860564 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B1937771 : Blo 860564 1937771 := bstep (se 1 (by rfl) ⟨1453328, by rfl⟩ : syracuseStep 1937771 = 2906657) B2906657
theorem B5902811 : Blo 860564 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B5607899 : Blo 860564 5607899 := bstep (se 1 (by rfl) ⟨4205924, by rfl⟩ : syracuseStep 5607899 = 8411849) B8411849
theorem B1937915 : Blo 860564 1937915 := bstep (se 1 (by rfl) ⟨1453436, by rfl⟩ : syracuseStep 1937915 = 2906873) B2906873
theorem B2331155 : Blo 860564 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B1380937 : Blo 860564 1380937 := bstep (se 2 (by rfl) ⟨517851, by rfl⟩ : syracuseStep 1380937 = 1035703) B1035703
theorem B1938041 : Blo 860564 1938041 := bstep (se 2 (by rfl) ⟨726765, by rfl⟩ : syracuseStep 1938041 = 1453531) B1453531
theorem B3281579 : Blo 860564 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B1938095 : Blo 860564 1938095 := bstep (se 1 (by rfl) ⟨1453571, by rfl⟩ : syracuseStep 1938095 = 2907143) B2907143
theorem B1938167 : Blo 860564 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B1970963 : Blo 860564 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B1938347 : Blo 860564 1938347 := bstep (se 1 (by rfl) ⟨1453760, by rfl⟩ : syracuseStep 1938347 = 2907521) B2907521
theorem B8393681 : Blo 860564 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B3740915 : Blo 860564 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B7476569 : Blo 860564 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B6231401 : Blo 860564 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B1938887 : Blo 860564 1938887 := bstep (se 1 (by rfl) ⟨1454165, by rfl⟩ : syracuseStep 1938887 = 2908331) B2908331
theorem B1840583 : Blo 860564 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B14718509 : Blo 860564 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B3741319 : Blo 860564 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B2954909 : Blo 860564 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B1939247 : Blo 860564 1939247 := bstep (se 1 (by rfl) ⟨1454435, by rfl⟩ : syracuseStep 1939247 = 2908871) B2908871
theorem B1578959 : Blo 860564 1578959 := bstep (se 1 (by rfl) ⟨1184219, by rfl⟩ : syracuseStep 1578959 = 2368439) B2368439
theorem B15702295 : Blo 860564 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B8395085 : Blo 860564 8395085 := bstep (se 3 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 8395085 = 3148157) B3148157
theorem B1939823 : Blo 860564 1939823 := bstep (se 1 (by rfl) ⟨1454867, by rfl⟩ : syracuseStep 1939823 = 2909735) B2909735
theorem B42473879 : Blo 860564 42473879 := bstep (se 1 (by rfl) ⟨31855409, by rfl⟩ : syracuseStep 42473879 = 63710819) B63710819
theorem B1939895 : Blo 860564 1939895 := bstep (se 1 (by rfl) ⟨1454921, by rfl⟩ : syracuseStep 1939895 = 2909843) B2909843
theorem B1841591 : Blo 860564 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1940039 : Blo 860564 1940039 := bstep (se 1 (by rfl) ⟨1455029, by rfl⟩ : syracuseStep 1940039 = 2910059) B2910059
theorem B1940075 : Blo 860564 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B5905003 : Blo 860564 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B14195317 : Blo 860564 14195317 := bstep (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) B1330811
theorem B1940471 : Blo 860564 1940471 := bstep (se 1 (by rfl) ⟨1455353, by rfl⟩ : syracuseStep 1940471 = 2910707) B2910707
theorem B1940831 : Blo 860564 1940831 := bstep (se 1 (by rfl) ⟨1455623, by rfl⟩ : syracuseStep 1940831 = 2911247) B2911247
theorem B1842745 : Blo 860564 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B3743347 : Blo 860564 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2072251 : Blo 860564 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B14753501 : Blo 860564 14753501 := bstep (se 3 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 14753501 = 5532563) B5532563
theorem B1941227 : Blo 860564 1941227 := bstep (se 1 (by rfl) ⟨1455920, by rfl⟩ : syracuseStep 1941227 = 2911841) B2911841
theorem B1941353 : Blo 860564 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B4366547 : Blo 860564 4366547 := bstep (se 1 (by rfl) ⟨3274910, by rfl⟩ : syracuseStep 4366547 = 6549821) B6549821
theorem B860583 : Blo 860564 860583 := bstep (se 1 (by rfl) ⟨645437, by rfl⟩ : syracuseStep 860583 = 1290875) B1290875
theorem B860667 : Blo 860564 860667 := bstep (se 1 (by rfl) ⟨645500, by rfl⟩ : syracuseStep 860667 = 1291001) B1291001
theorem B860735 : Blo 860564 860735 := bstep (se 1 (by rfl) ⟨645551, by rfl⟩ : syracuseStep 860735 = 1291103) B1291103
theorem B860743 : Blo 860564 860743 := bstep (se 1 (by rfl) ⟨645557, by rfl⟩ : syracuseStep 860743 = 1291115) B1291115
theorem B1745479 : Blo 860564 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B9806507 : Blo 860564 9806507 := bstep (se 1 (by rfl) ⟨7354880, by rfl⟩ : syracuseStep 9806507 = 14709761) B14709761
theorem B2073271 : Blo 860564 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B1942199 : Blo 860564 1942199 := bstep (se 1 (by rfl) ⟨1456649, by rfl⟩ : syracuseStep 1942199 = 2913299) B2913299
theorem B5251787 : Blo 860564 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B860895 : Blo 860564 860895 := bstep (se 1 (by rfl) ⟨645671, by rfl⟩ : syracuseStep 860895 = 1291343) B1291343
theorem B18621197 : Blo 860564 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B860975 : Blo 860564 860975 := bstep (se 1 (by rfl) ⟨645731, by rfl⟩ : syracuseStep 860975 = 1291463) B1291463
theorem B1090351 : Blo 860564 1090351 := bstep (se 1 (by rfl) ⟨817763, by rfl⟩ : syracuseStep 1090351 = 1635527) B1635527
theorem B1942415 : Blo 860564 1942415 := bstep (se 1 (by rfl) ⟨1456811, by rfl⟩ : syracuseStep 1942415 = 2913623) B2913623
theorem B861083 : Blo 860564 861083 := bstep (se 1 (by rfl) ⟨645812, by rfl⟩ : syracuseStep 861083 = 1291625) B1291625
theorem B861135 : Blo 860564 861135 := bstep (se 1 (by rfl) ⟨645851, by rfl⟩ : syracuseStep 861135 = 1291703) B1291703
theorem B861159 : Blo 860564 861159 := bstep (se 1 (by rfl) ⟨645869, by rfl⟩ : syracuseStep 861159 = 1291739) B1291739
theorem B23635115 : Blo 860564 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B4138199 : Blo 860564 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B861471 : Blo 860564 861471 := bstep (se 1 (by rfl) ⟨646103, by rfl⟩ : syracuseStep 861471 = 1292207) B1292207
theorem B1090847 : Blo 860564 1090847 := bstep (se 1 (by rfl) ⟨818135, by rfl⟩ : syracuseStep 1090847 = 1636271) B1636271
theorem B2073887 : Blo 860564 2073887 := bstep (se 1 (by rfl) ⟨1555415, by rfl⟩ : syracuseStep 2073887 = 3110831) B3110831
theorem B861531 : Blo 860564 861531 := bstep (se 1 (by rfl) ⟨646148, by rfl⟩ : syracuseStep 861531 = 1292297) B1292297
theorem B861551 : Blo 860564 861551 := bstep (se 1 (by rfl) ⟨646163, by rfl⟩ : syracuseStep 861551 = 1292327) B1292327
theorem B861607 : Blo 860564 861607 := bstep (se 1 (by rfl) ⟨646205, by rfl⟩ : syracuseStep 861607 = 1292411) B1292411
theorem B861691 : Blo 860564 861691 := bstep (se 1 (by rfl) ⟨646268, by rfl⟩ : syracuseStep 861691 = 1292537) B1292537
theorem B861759 : Blo 860564 861759 := bstep (se 1 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 861759 = 1292639) B1292639
theorem B861767 : Blo 860564 861767 := bstep (se 1 (by rfl) ⟨646325, by rfl⟩ : syracuseStep 861767 = 1292651) B1292651
theorem B1943135 : Blo 860564 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B10233479 : Blo 860564 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B3679901 : Blo 860564 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B11347613 : Blo 860564 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B861919 : Blo 860564 861919 := bstep (se 1 (by rfl) ⟨646439, by rfl⟩ : syracuseStep 861919 = 1292879) B1292879
theorem B861999 : Blo 860564 861999 := bstep (se 1 (by rfl) ⟨646499, by rfl⟩ : syracuseStep 861999 = 1292999) B1292999
theorem B1943351 : Blo 860564 1943351 := bstep (se 1 (by rfl) ⟨1457513, by rfl⟩ : syracuseStep 1943351 = 2915027) B2915027
theorem B862107 : Blo 860564 862107 := bstep (se 1 (by rfl) ⟨646580, by rfl⟩ : syracuseStep 862107 = 1293161) B1293161
theorem B862159 : Blo 860564 862159 := bstep (se 1 (by rfl) ⟨646619, by rfl⟩ : syracuseStep 862159 = 1293239) B1293239
theorem B862183 : Blo 860564 862183 := bstep (se 1 (by rfl) ⟨646637, by rfl⟩ : syracuseStep 862183 = 1293275) B1293275
theorem B1943657 : Blo 860564 1943657 := bstep (se 2 (by rfl) ⟨728871, by rfl⟩ : syracuseStep 1943657 = 1457743) B1457743
theorem B2795705 : Blo 860564 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B862495 : Blo 860564 862495 := bstep (se 1 (by rfl) ⟨646871, by rfl⟩ : syracuseStep 862495 = 1293743) B1293743
theorem B862555 : Blo 860564 862555 := bstep (se 1 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 862555 = 1293833) B1293833
theorem B862575 : Blo 860564 862575 := bstep (se 1 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 862575 = 1293863) B1293863
theorem B862631 : Blo 860564 862631 := bstep (se 1 (by rfl) ⟨646973, by rfl⟩ : syracuseStep 862631 = 1293947) B1293947
theorem B1452539 : Blo 860564 1452539 := bstep (se 1 (by rfl) ⟨1089404, by rfl⟩ : syracuseStep 1452539 = 2178809) B2178809
theorem B862715 : Blo 860564 862715 := bstep (se 1 (by rfl) ⟨647036, by rfl⟩ : syracuseStep 862715 = 1294073) B1294073
theorem B862783 : Blo 860564 862783 := bstep (se 1 (by rfl) ⟨647087, by rfl⟩ : syracuseStep 862783 = 1294175) B1294175
theorem B862791 : Blo 860564 862791 := bstep (se 1 (by rfl) ⟨647093, by rfl⟩ : syracuseStep 862791 = 1294187) B1294187
theorem B1944143 : Blo 860564 1944143 := bstep (se 1 (by rfl) ⟨1458107, by rfl⟩ : syracuseStep 1944143 = 2916215) B2916215
theorem B1845931 : Blo 860564 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B862943 : Blo 860564 862943 := bstep (se 1 (by rfl) ⟨647207, by rfl⟩ : syracuseStep 862943 = 1294415) B1294415
theorem B1944287 : Blo 860564 1944287 := bstep (se 1 (by rfl) ⟨1458215, by rfl⟩ : syracuseStep 1944287 = 2916431) B2916431
theorem B1845983 : Blo 860564 1845983 := bstep (se 1 (by rfl) ⟨1384487, by rfl⟩ : syracuseStep 1845983 = 2768975) B2768975
theorem B863023 : Blo 860564 863023 := bstep (se 1 (by rfl) ⟨647267, by rfl⟩ : syracuseStep 863023 = 1294535) B1294535
theorem B33106805 : Blo 860564 33106805 := bstep (se 5 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 33106805 = 3103763) B3103763
theorem B12462983 : Blo 860564 12462983 := bstep (se 1 (by rfl) ⟨9347237, by rfl⟩ : syracuseStep 12462983 = 18694475) B18694475
theorem B863131 : Blo 860564 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B1452971 : Blo 860564 1452971 := bstep (se 1 (by rfl) ⟨1089728, by rfl⟩ : syracuseStep 1452971 = 2179457) B2179457
theorem B863183 : Blo 860564 863183 := bstep (se 1 (by rfl) ⟨647387, by rfl⟩ : syracuseStep 863183 = 1294775) B1294775
theorem B1944539 : Blo 860564 1944539 := bstep (se 1 (by rfl) ⟨1458404, by rfl⟩ : syracuseStep 1944539 = 2916809) B2916809
theorem B863207 : Blo 860564 863207 := bstep (se 1 (by rfl) ⟨647405, by rfl⟩ : syracuseStep 863207 = 1294811) B1294811
theorem B1944719 : Blo 860564 1944719 := bstep (se 1 (by rfl) ⟨1458539, by rfl⟩ : syracuseStep 1944719 = 2917079) B2917079
theorem B1944809 : Blo 860564 1944809 := bstep (se 2 (by rfl) ⟨729303, by rfl⟩ : syracuseStep 1944809 = 1458607) B1458607
theorem B863519 : Blo 860564 863519 := bstep (se 1 (by rfl) ⟨647639, by rfl⟩ : syracuseStep 863519 = 1295279) B1295279
theorem B1944863 : Blo 860564 1944863 := bstep (se 1 (by rfl) ⟨1458647, by rfl⟩ : syracuseStep 1944863 = 2917295) B2917295
theorem B863579 : Blo 860564 863579 := bstep (se 1 (by rfl) ⟨647684, by rfl⟩ : syracuseStep 863579 = 1295369) B1295369
theorem B863599 : Blo 860564 863599 := bstep (se 1 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 863599 = 1295399) B1295399
theorem B863655 : Blo 860564 863655 := bstep (se 1 (by rfl) ⟨647741, by rfl⟩ : syracuseStep 863655 = 1295483) B1295483
theorem B1453511 : Blo 860564 1453511 := bstep (se 1 (by rfl) ⟨1090133, by rfl⟩ : syracuseStep 1453511 = 2180267) B2180267
theorem B1093115 : Blo 860564 1093115 := bstep (se 1 (by rfl) ⟨819836, by rfl⟩ : syracuseStep 1093115 = 1639673) B1639673
theorem B863739 : Blo 860564 863739 := bstep (se 1 (by rfl) ⟨647804, by rfl⟩ : syracuseStep 863739 = 1295609) B1295609
theorem B22097447 : Blo 860564 22097447 := bstep (se 1 (by rfl) ⟨16573085, by rfl⟩ : syracuseStep 22097447 = 33146171) B33146171
theorem B863807 : Blo 860564 863807 := bstep (se 1 (by rfl) ⟨647855, by rfl⟩ : syracuseStep 863807 = 1295711) B1295711
theorem B863815 : Blo 860564 863815 := bstep (se 1 (by rfl) ⟨647861, by rfl⟩ : syracuseStep 863815 = 1295723) B1295723
theorem B4140659 : Blo 860564 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B2076347 : Blo 860564 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B863967 : Blo 860564 863967 := bstep (se 1 (by rfl) ⟨647975, by rfl⟩ : syracuseStep 863967 = 1295951) B1295951
theorem B4140811 : Blo 860564 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B864047 : Blo 860564 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B864155 : Blo 860564 864155 := bstep (se 1 (by rfl) ⟨648116, by rfl⟩ : syracuseStep 864155 = 1296233) B1296233
theorem B864207 : Blo 860564 864207 := bstep (se 1 (by rfl) ⟨648155, by rfl⟩ : syracuseStep 864207 = 1296311) B1296311
theorem B864231 : Blo 860564 864231 := bstep (se 1 (by rfl) ⟨648173, by rfl⟩ : syracuseStep 864231 = 1296347) B1296347
theorem B4730899 : Blo 860564 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B9318557 : Blo 860564 9318557 := bstep (se 3 (by rfl) ⟨1747229, by rfl⟩ : syracuseStep 9318557 = 3494459) B3494459
theorem B864543 : Blo 860564 864543 := bstep (se 1 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 864543 = 1296815) B1296815
theorem B2077019 : Blo 860564 2077019 := bstep (se 1 (by rfl) ⟨1557764, by rfl⟩ : syracuseStep 2077019 = 3115529) B3115529
theorem B1454503 : Blo 860564 1454503 := bstep (se 1 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 1454503 = 2181755) B2181755
theorem B1094087 : Blo 860564 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B15708653 : Blo 860564 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B1454665 : Blo 860564 1454665 := bstep (se 2 (by rfl) ⟨545499, by rfl⟩ : syracuseStep 1454665 = 1090999) B1090999
theorem B1454699 : Blo 860564 1454699 := bstep (se 1 (by rfl) ⟨1091024, by rfl⟩ : syracuseStep 1454699 = 2182049) B2182049
theorem B1290935 : Blo 860564 1290935 := bstep (se 1 (by rfl) ⟨968201, by rfl⟩ : syracuseStep 1290935 = 1936403) B1936403
theorem B1291163 : Blo 860564 1291163 := bstep (se 1 (by rfl) ⟨968372, by rfl⟩ : syracuseStep 1291163 = 1936745) B1936745
theorem B3683303 : Blo 860564 3683303 := bstep (se 1 (by rfl) ⟨2762477, by rfl⟩ : syracuseStep 3683303 = 5524955) B5524955
theorem B15709463 : Blo 860564 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B1291559 : Blo 860564 1291559 := bstep (se 1 (by rfl) ⟨968669, by rfl⟩ : syracuseStep 1291559 = 1937339) B1937339
theorem B3683627 : Blo 860564 3683627 := bstep (se 1 (by rfl) ⟨2762720, by rfl⟩ : syracuseStep 3683627 = 5525441) B5525441
theorem B1291643 : Blo 860564 1291643 := bstep (se 1 (by rfl) ⟨968732, by rfl⟩ : syracuseStep 1291643 = 1937465) B1937465
theorem B1291769 : Blo 860564 1291769 := bstep (se 2 (by rfl) ⟨484413, by rfl⟩ : syracuseStep 1291769 = 968827) B968827
theorem B1291871 : Blo 860564 1291871 := bstep (se 1 (by rfl) ⟨968903, by rfl⟩ : syracuseStep 1291871 = 1937807) B1937807
theorem B11056925 : Blo 860564 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B1292087 : Blo 860564 1292087 := bstep (se 1 (by rfl) ⟨969065, by rfl⟩ : syracuseStep 1292087 = 1938131) B1938131
theorem B6993719 : Blo 860564 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B16562015 : Blo 860564 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B1292393 : Blo 860564 1292393 := bstep (se 2 (by rfl) ⟨484647, by rfl⟩ : syracuseStep 1292393 = 969295) B969295
theorem B1456393 : Blo 860564 1456393 := bstep (se 2 (by rfl) ⟨546147, by rfl⟩ : syracuseStep 1456393 = 1092295) B1092295
theorem B1292711 : Blo 860564 1292711 := bstep (se 1 (by rfl) ⟨969533, by rfl⟩ : syracuseStep 1292711 = 1939067) B1939067
theorem B1292795 : Blo 860564 1292795 := bstep (se 1 (by rfl) ⟨969596, by rfl⟩ : syracuseStep 1292795 = 1939193) B1939193
theorem B1292921 : Blo 860564 1292921 := bstep (se 2 (by rfl) ⟨484845, by rfl⟩ : syracuseStep 1292921 = 969691) B969691
theorem B1292975 : Blo 860564 1292975 := bstep (se 1 (by rfl) ⟨969731, by rfl⟩ : syracuseStep 1292975 = 1939463) B1939463
theorem B4143811 : Blo 860564 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B1293023 : Blo 860564 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B5520109 : Blo 860564 5520109 := bstep (se 3 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 5520109 = 2070041) B2070041
theorem B1293287 : Blo 860564 1293287 := bstep (se 1 (by rfl) ⟨969965, by rfl⟩ : syracuseStep 1293287 = 1939931) B1939931
theorem B1752283 : Blo 860564 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B1293545 : Blo 860564 1293545 := bstep (se 2 (by rfl) ⟨485079, by rfl⟩ : syracuseStep 1293545 = 970159) B970159
theorem B1293599 : Blo 860564 1293599 := bstep (se 1 (by rfl) ⟨970199, by rfl⟩ : syracuseStep 1293599 = 1940399) B1940399
theorem B933287 : Blo 860564 933287 := bstep (se 1 (by rfl) ⟨699965, by rfl⟩ : syracuseStep 933287 = 1399931) B1399931
theorem B1293767 : Blo 860564 1293767 := bstep (se 1 (by rfl) ⟨970325, by rfl⟩ : syracuseStep 1293767 = 1940651) B1940651
theorem B1457851 : Blo 860564 1457851 := bstep (se 1 (by rfl) ⟨1093388, by rfl⟩ : syracuseStep 1457851 = 2186777) B2186777
theorem B4669139 : Blo 860564 4669139 := bstep (se 1 (by rfl) ⟨3501854, by rfl⟩ : syracuseStep 4669139 = 7003709) B7003709
theorem B1294121 : Blo 860564 1294121 := bstep (se 2 (by rfl) ⟨485295, by rfl⟩ : syracuseStep 1294121 = 970591) B970591
theorem B1294127 : Blo 860564 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B4145003 : Blo 860564 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B1294601 : Blo 860564 1294601 := bstep (se 2 (by rfl) ⟨485475, by rfl⟩ : syracuseStep 1294601 = 970951) B970951
theorem B1294703 : Blo 860564 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B1294919 : Blo 860564 1294919 := bstep (se 1 (by rfl) ⟨971189, by rfl⟩ : syracuseStep 1294919 = 1942379) B1942379
theorem B1294955 : Blo 860564 1294955 := bstep (se 1 (by rfl) ⟨971216, by rfl⟩ : syracuseStep 1294955 = 1942433) B1942433
theorem B1458911 : Blo 860564 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B2179831 : Blo 860564 2179831 := bstep (se 1 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 2179831 = 3269747) B3269747
theorem B1295183 : Blo 860564 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B4375457 : Blo 860564 4375457 := bstep (se 2 (by rfl) ⟨1640796, by rfl⟩ : syracuseStep 4375457 = 3281593) B3281593
theorem B2180135 : Blo 860564 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B1295579 : Blo 860564 1295579 := bstep (se 1 (by rfl) ⟨971684, by rfl⟩ : syracuseStep 1295579 = 1943369) B1943369
theorem B8275243 : Blo 860564 8275243 := bstep (se 1 (by rfl) ⟨6206432, by rfl⟩ : syracuseStep 8275243 = 12412865) B12412865
theorem B1295753 : Blo 860564 1295753 := bstep (se 2 (by rfl) ⟨485907, by rfl⟩ : syracuseStep 1295753 = 971815) B971815
theorem B8406461 : Blo 860564 8406461 := bstep (se 3 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 8406461 = 3152423) B3152423
theorem B968287 : Blo 860564 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B1296107 : Blo 860564 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B1296335 : Blo 860564 1296335 := bstep (se 1 (by rfl) ⟨972251, by rfl⟩ : syracuseStep 1296335 = 1944503) B1944503
theorem B2181401 : Blo 860564 2181401 := bstep (se 2 (by rfl) ⟨818025, by rfl⟩ : syracuseStep 2181401 = 1636051) B1636051
theorem B1296731 : Blo 860564 1296731 := bstep (se 1 (by rfl) ⟨972548, by rfl⟩ : syracuseStep 1296731 = 1945097) B1945097
theorem B2214479 : Blo 860564 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B969439 : Blo 860564 969439 := bstep (se 1 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 969439 = 1454159) B1454159
theorem B226446353 : Blo 860564 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B2182241 : Blo 860564 2182241 := bstep (se 2 (by rfl) ⟨818340, by rfl⟩ : syracuseStep 2182241 = 1636681) B1636681
theorem B4148347 : Blo 860564 4148347 := bstep (se 1 (by rfl) ⟨3111260, by rfl⟩ : syracuseStep 4148347 = 6222521) B6222521
theorem B68275379 : Blo 860564 68275379 := bstep (se 1 (by rfl) ⟨51206534, by rfl⟩ : syracuseStep 68275379 = 102413069) B102413069
theorem B970015 : Blo 860564 970015 := bstep (se 1 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 970015 = 1455023) B1455023
theorem B970303 : Blo 860564 970303 := bstep (se 1 (by rfl) ⟨727727, by rfl⟩ : syracuseStep 970303 = 1455455) B1455455
theorem B4148945 : Blo 860564 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B9818171 : Blo 860564 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B971131 : Blo 860564 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B16568711 : Blo 860564 16568711 := bstep (se 1 (by rfl) ⟨12426533, by rfl⟩ : syracuseStep 16568711 = 24853067) B24853067
theorem B2183699 : Blo 860564 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B971599 : Blo 860564 971599 := bstep (se 1 (by rfl) ⟨728699, by rfl⟩ : syracuseStep 971599 = 1457399) B1457399
theorem B2184155 : Blo 860564 2184155 := bstep (se 1 (by rfl) ⟨1638116, by rfl⟩ : syracuseStep 2184155 = 3276233) B3276233
theorem B971995 : Blo 860564 971995 := bstep (se 1 (by rfl) ⟨728996, by rfl⟩ : syracuseStep 971995 = 1457993) B1457993
theorem B2184479 : Blo 860564 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B8279435 : Blo 860564 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B9819629 : Blo 860564 9819629 := bstep (se 3 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 9819629 = 3682361) B3682361
theorem B972283 : Blo 860564 972283 := bstep (se 1 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 972283 = 1458425) B1458425
theorem B972463 : Blo 860564 972463 := bstep (se 1 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 972463 = 1458695) B1458695
theorem B2185015 : Blo 860564 2185015 := bstep (se 1 (by rfl) ⟨1638761, by rfl⟩ : syracuseStep 2185015 = 3277523) B3277523
theorem B3692375 : Blo 860564 3692375 := bstep (se 1 (by rfl) ⟨2769281, by rfl⟩ : syracuseStep 3692375 = 5538563) B5538563
theorem B2906063 : Blo 860564 2906063 := bstep (se 1 (by rfl) ⟨2179547, by rfl⟩ : syracuseStep 2906063 = 4359095) B4359095
theorem B2185481 : Blo 860564 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B874783 : Blo 860564 874783 := bstep (se 1 (by rfl) ⟨656087, by rfl⟩ : syracuseStep 874783 = 1312175) B1312175
theorem B2907035 : Blo 860564 2907035 := bstep (se 1 (by rfl) ⟨2180276, by rfl⟩ : syracuseStep 2907035 = 4360553) B4360553
theorem B3267499 : Blo 860564 3267499 := bstep (se 1 (by rfl) ⟨2450624, by rfl⟩ : syracuseStep 3267499 = 4901249) B4901249
theorem B3267773 : Blo 860564 3267773 := bstep (se 3 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 3267773 = 1225415) B1225415
theorem B3267803 : Blo 860564 3267803 := bstep (se 1 (by rfl) ⟨2450852, by rfl⟩ : syracuseStep 3267803 = 4901705) B4901705
theorem B8871133 : Blo 860564 8871133 := bstep (se 3 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 8871133 = 3326675) B3326675
theorem B2186473 : Blo 860564 2186473 := bstep (se 2 (by rfl) ⟨819927, by rfl⟩ : syracuseStep 2186473 = 1639855) B1639855
theorem B31415687 : Blo 860564 31415687 := bstep (se 1 (by rfl) ⟨23561765, by rfl⟩ : syracuseStep 31415687 = 47123531) B47123531
theorem B2186635 : Blo 860564 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B2186939 : Blo 860564 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B2908061 : Blo 860564 2908061 := bstep (se 3 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 2908061 = 1090523) B1090523
theorem B2908169 : Blo 860564 2908169 := bstep (se 2 (by rfl) ⟨1090563, by rfl⟩ : syracuseStep 2908169 = 2181127) B2181127
theorem B7005527 : Blo 860564 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B24864245 : Blo 860564 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B3925865 : Blo 860564 3925865 := bstep (se 2 (by rfl) ⟨1472199, by rfl⟩ : syracuseStep 3925865 = 2944399) B2944399
theorem B21227501 : Blo 860564 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B3270689 : Blo 860564 3270689 := bstep (se 2 (by rfl) ⟨1226508, by rfl⟩ : syracuseStep 3270689 = 2453017) B2453017
theorem B7366909 : Blo 860564 7366909 := bstep (se 3 (by rfl) ⟨1381295, by rfl⟩ : syracuseStep 7366909 = 2762591) B2762591
theorem B12446081 : Blo 860564 12446081 := bstep (se 2 (by rfl) ⟨4667280, by rfl⟩ : syracuseStep 12446081 = 9334561) B9334561
theorem B9431639 : Blo 860564 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B3500819 : Blo 860564 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B12610637 : Blo 860564 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B2911355 : Blo 860564 2911355 := bstep (se 1 (by rfl) ⟨2183516, by rfl⟩ : syracuseStep 2911355 = 4367033) B4367033
theorem B2452619 : Blo 860564 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B5238047 : Blo 860564 5238047 := bstep (se 1 (by rfl) ⟨3928535, by rfl⟩ : syracuseStep 5238047 = 7857071) B7857071
theorem B10644767 : Blo 860564 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B13299059 : Blo 860564 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B2911625 : Blo 860564 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B2453075 : Blo 860564 2453075 := bstep (se 1 (by rfl) ⟨1839806, by rfl⟩ : syracuseStep 2453075 = 3679613) B3679613
theorem B2912057 : Blo 860564 2912057 := bstep (se 2 (by rfl) ⟨1092021, by rfl⟩ : syracuseStep 2912057 = 2184043) B2184043
theorem B3371033 : Blo 860564 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B11072051 : Blo 860564 11072051 := bstep (se 1 (by rfl) ⟨8304038, by rfl⟩ : syracuseStep 11072051 = 16608077) B16608077
theorem B1995337 : Blo 860564 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B2912921 : Blo 860564 2912921 := bstep (se 2 (by rfl) ⟨1092345, by rfl⟩ : syracuseStep 2912921 = 2184691) B2184691
theorem B2619191 : Blo 860564 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B3274577 : Blo 860564 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B44890157 : Blo 860564 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B2914433 : Blo 860564 2914433 := bstep (se 2 (by rfl) ⟨1092912, by rfl⟩ : syracuseStep 2914433 = 2185825) B2185825
theorem B7076119 : Blo 860564 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B14186933 : Blo 860564 14186933 := bstep (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) B1330025
theorem B2455991 : Blo 860564 2455991 := bstep (se 1 (by rfl) ⟨1841993, by rfl⟩ : syracuseStep 2455991 = 3683987) B3683987
theorem B2914811 : Blo 860564 2914811 := bstep (se 1 (by rfl) ⟨2186108, by rfl⟩ : syracuseStep 2914811 = 4372217) B4372217
theorem B1473131 : Blo 860564 1473131 := bstep (se 1 (by rfl) ⟨1104848, by rfl⟩ : syracuseStep 1473131 = 2209697) B2209697
theorem B1636985 : Blo 860564 1636985 := bstep (se 2 (by rfl) ⟨613869, by rfl⟩ : syracuseStep 1636985 = 1227739) B1227739
theorem B4356989 : Blo 860564 4356989 := bstep (se 3 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 4356989 = 1633871) B1633871
theorem B2915243 : Blo 860564 2915243 := bstep (se 1 (by rfl) ⟨2186432, by rfl⟩ : syracuseStep 2915243 = 4372865) B4372865
theorem B1768735 : Blo 860564 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B1637729 : Blo 860564 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B8289701 : Blo 860564 8289701 := bstep (se 4 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 8289701 = 1554319) B1554319
theorem B2915783 : Blo 860564 2915783 := bstep (se 1 (by rfl) ⟨2186837, by rfl⟩ : syracuseStep 2915783 = 4373675) B4373675
theorem B3276247 : Blo 860564 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B2621089 : Blo 860564 2621089 := bstep (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) B1965817
theorem B2457323 : Blo 860564 2457323 := bstep (se 1 (by rfl) ⟨1842992, by rfl⟩ : syracuseStep 2457323 = 3685985) B3685985
theorem B3276551 : Blo 860564 3276551 := bstep (se 1 (by rfl) ⟨2457413, by rfl⟩ : syracuseStep 3276551 = 4914827) B4914827
theorem B2916107 : Blo 860564 2916107 := bstep (se 1 (by rfl) ⟨2187080, by rfl⟩ : syracuseStep 2916107 = 4374161) B4374161
theorem B2457391 : Blo 860564 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B5046077 : Blo 860564 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B4357961 : Blo 860564 4357961 := bstep (se 2 (by rfl) ⟨1634235, by rfl⟩ : syracuseStep 4357961 = 3268471) B3268471
theorem B2621479 : Blo 860564 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B10485811 : Blo 860564 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B2916971 : Blo 860564 2916971 := bstep (se 1 (by rfl) ⟨2187728, by rfl⟩ : syracuseStep 2916971 = 4375457) B4375457
theorem B2327305 : Blo 860564 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B4916011 : Blo 860564 4916011 := bstep (se 1 (by rfl) ⟨3687008, by rfl⟩ : syracuseStep 4916011 = 7374017) B7374017
theorem B2917565 : Blo 860564 2917565 := bstep (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) B1094087
theorem B1640159 : Blo 860564 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B150964235 : Blo 860564 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B45516919 : Blo 860564 45516919 := bstep (se 1 (by rfl) ⟨34137689, by rfl⟩ : syracuseStep 45516919 = 68275379) B68275379
theorem B9832751 : Blo 860564 9832751 := bstep (se 1 (by rfl) ⟨7374563, by rfl⟩ : syracuseStep 9832751 = 14749127) B14749127
theorem B3935063 : Blo 860564 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B11045807 : Blo 860564 11045807 := bstep (se 1 (by rfl) ⟨8284355, by rfl⟩ : syracuseStep 11045807 = 16568711) B16568711
theorem B3935207 : Blo 860564 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B3738599 : Blo 860564 3738599 := bstep (se 1 (by rfl) ⟨2803949, by rfl⟩ : syracuseStep 3738599 = 5607899) B5607899
theorem B1313975 : Blo 860564 1313975 := bstep (se 1 (by rfl) ⟨985481, by rfl⟩ : syracuseStep 1313975 = 1970963) B1970963
theorem B2461241 : Blo 860564 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B4984379 : Blo 860564 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B1969939 : Blo 860564 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B22417229 : Blo 860564 22417229 := bstep (se 3 (by rfl) ⟨4203230, by rfl⟩ : syracuseStep 22417229 = 8406461) B8406461
theorem B2461583 : Blo 860564 2461583 := bstep (se 1 (by rfl) ⟨1846187, by rfl⟩ : syracuseStep 2461583 = 3692375) B3692375
theorem B1937375 : Blo 860564 1937375 := bstep (se 1 (by rfl) ⟨1453031, by rfl⟩ : syracuseStep 1937375 = 2906063) B2906063
theorem B1052639 : Blo 860564 1052639 := bstep (se 1 (by rfl) ⟨789479, by rfl⟩ : syracuseStep 1052639 = 1578959) B1578959
theorem B6295805 : Blo 860564 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B28315919 : Blo 860564 28315919 := bstep (se 1 (by rfl) ⟨21236939, by rfl⟩ : syracuseStep 28315919 = 42473879) B42473879
theorem B1938023 : Blo 860564 1938023 := bstep (se 1 (by rfl) ⟨1453517, by rfl⟩ : syracuseStep 1938023 = 2907035) B2907035
theorem B20943791 : Blo 860564 20943791 := bstep (se 1 (by rfl) ⟨15707843, by rfl⟩ : syracuseStep 20943791 = 31415687) B31415687
theorem B9835667 : Blo 860564 9835667 := bstep (se 1 (by rfl) ⟨7376750, by rfl⟩ : syracuseStep 9835667 = 14753501) B14753501
theorem B1938707 : Blo 860564 1938707 := bstep (se 1 (by rfl) ⟨1454030, by rfl⟩ : syracuseStep 1938707 = 2908061) B2908061
theorem B1938779 : Blo 860564 1938779 := bstep (se 1 (by rfl) ⟨1454084, by rfl⟩ : syracuseStep 1938779 = 2908169) B2908169
theorem B119707085 : Blo 860564 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B1939337 : Blo 860564 1939337 := bstep (se 2 (by rfl) ⟨727251, by rfl⟩ : syracuseStep 1939337 = 1454503) B1454503
theorem B1939553 : Blo 860564 1939553 := bstep (se 2 (by rfl) ⟨727332, by rfl⟩ : syracuseStep 1939553 = 1454665) B1454665
theorem B1841249 : Blo 860564 1841249 := bstep (se 2 (by rfl) ⟨690468, by rfl⟩ : syracuseStep 1841249 = 1380937) B1380937
theorem B2660449 : Blo 860564 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B2758799 : Blo 860564 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B1382591 : Blo 860564 1382591 := bstep (se 1 (by rfl) ⟨1036943, by rfl⟩ : syracuseStep 1382591 = 2073887) B2073887
theorem B6822319 : Blo 860564 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B5905277 : Blo 860564 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B8297387 : Blo 860564 8297387 := bstep (se 1 (by rfl) ⟨6223040, by rfl⟩ : syracuseStep 8297387 = 12446081) B12446081
theorem B2333879 : Blo 860564 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B1940903 : Blo 860564 1940903 := bstep (se 1 (by rfl) ⟨1455677, by rfl⟩ : syracuseStep 1940903 = 2911355) B2911355
theorem B4988425 : Blo 860564 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B1941083 : Blo 860564 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B2760439 : Blo 860564 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B1384231 : Blo 860564 1384231 := bstep (se 1 (by rfl) ⟨1038173, by rfl⟩ : syracuseStep 1384231 = 2076347) B2076347
theorem B1941371 : Blo 860564 1941371 := bstep (se 1 (by rfl) ⟨1456028, by rfl⟩ : syracuseStep 1941371 = 2912057) B2912057
theorem B1384679 : Blo 860564 1384679 := bstep (se 1 (by rfl) ⟨1038509, by rfl⟩ : syracuseStep 1384679 = 2077019) B2077019
theorem B1941857 : Blo 860564 1941857 := bstep (se 2 (by rfl) ⟨728196, by rfl⟩ : syracuseStep 1941857 = 1456393) B1456393
theorem B7381367 : Blo 860564 7381367 := bstep (se 1 (by rfl) ⟨5536025, by rfl⟩ : syracuseStep 7381367 = 11072051) B11072051
theorem B1941947 : Blo 860564 1941947 := bstep (se 1 (by rfl) ⟨1456460, by rfl⟩ : syracuseStep 1941947 = 2912921) B2912921
theorem B860623 : Blo 860564 860623 := bstep (se 1 (by rfl) ⟨645467, by rfl⟩ : syracuseStep 860623 = 1290935) B1290935
theorem B860775 : Blo 860564 860775 := bstep (se 1 (by rfl) ⟨645581, by rfl⟩ : syracuseStep 860775 = 1291163) B1291163
theorem B7873337 : Blo 860564 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B861039 : Blo 860564 861039 := bstep (se 1 (by rfl) ⟨645779, by rfl⟩ : syracuseStep 861039 = 1291559) B1291559
theorem B861095 : Blo 860564 861095 := bstep (se 1 (by rfl) ⟨645821, by rfl⟩ : syracuseStep 861095 = 1291643) B1291643
theorem B861179 : Blo 860564 861179 := bstep (se 1 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 861179 = 1291769) B1291769
theorem B861247 : Blo 860564 861247 := bstep (se 1 (by rfl) ⟨645935, by rfl⟩ : syracuseStep 861247 = 1291871) B1291871
theorem B1746127 : Blo 860564 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B861391 : Blo 860564 861391 := bstep (se 1 (by rfl) ⟨646043, by rfl⟩ : syracuseStep 861391 = 1292087) B1292087
theorem B4662479 : Blo 860564 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B861595 : Blo 860564 861595 := bstep (se 1 (by rfl) ⟨646196, by rfl⟩ : syracuseStep 861595 = 1292393) B1292393
theorem B1942955 : Blo 860564 1942955 := bstep (se 1 (by rfl) ⟨1457216, by rfl⟩ : syracuseStep 1942955 = 2914433) B2914433
theorem B861807 : Blo 860564 861807 := bstep (se 1 (by rfl) ⟨646355, by rfl⟩ : syracuseStep 861807 = 1292711) B1292711
theorem B2336377 : Blo 860564 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B861863 : Blo 860564 861863 := bstep (se 1 (by rfl) ⟨646397, by rfl⟩ : syracuseStep 861863 = 1292795) B1292795
theorem B1943207 : Blo 860564 1943207 := bstep (se 1 (by rfl) ⟨1457405, by rfl⟩ : syracuseStep 1943207 = 2914811) B2914811
theorem B861947 : Blo 860564 861947 := bstep (se 1 (by rfl) ⟨646460, by rfl⟩ : syracuseStep 861947 = 1292921) B1292921
theorem B1091323 : Blo 860564 1091323 := bstep (se 1 (by rfl) ⟨818492, by rfl⟩ : syracuseStep 1091323 = 1636985) B1636985
theorem B861983 : Blo 860564 861983 := bstep (se 1 (by rfl) ⟨646487, by rfl⟩ : syracuseStep 861983 = 1292975) B1292975
theorem B862015 : Blo 860564 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B1943495 : Blo 860564 1943495 := bstep (se 1 (by rfl) ⟨1457621, by rfl⟩ : syracuseStep 1943495 = 2915243) B2915243
theorem B4368329 : Blo 860564 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B862191 : Blo 860564 862191 := bstep (se 1 (by rfl) ⟨646643, by rfl⟩ : syracuseStep 862191 = 1293287) B1293287
theorem B4991129 : Blo 860564 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B862363 : Blo 860564 862363 := bstep (se 1 (by rfl) ⟨646772, by rfl⟩ : syracuseStep 862363 = 1293545) B1293545
theorem B862399 : Blo 860564 862399 := bstep (se 1 (by rfl) ⟨646799, by rfl⟩ : syracuseStep 862399 = 1293599) B1293599
theorem B1091819 : Blo 860564 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B2763001 : Blo 860564 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B1943801 : Blo 860564 1943801 := bstep (se 2 (by rfl) ⟨728925, by rfl⟩ : syracuseStep 1943801 = 1457851) B1457851
theorem B862511 : Blo 860564 862511 := bstep (se 1 (by rfl) ⟨646883, by rfl⟩ : syracuseStep 862511 = 1293767) B1293767
theorem B1943855 : Blo 860564 1943855 := bstep (se 1 (by rfl) ⟨1457891, by rfl⟩ : syracuseStep 1943855 = 2915783) B2915783
theorem B1944071 : Blo 860564 1944071 := bstep (se 1 (by rfl) ⟨1458053, by rfl⟩ : syracuseStep 1944071 = 2916107) B2916107
theorem B862747 : Blo 860564 862747 := bstep (se 1 (by rfl) ⟨647060, by rfl⟩ : syracuseStep 862747 = 1294121) B1294121
theorem B862751 : Blo 860564 862751 := bstep (se 1 (by rfl) ⟨647063, by rfl⟩ : syracuseStep 862751 = 1294127) B1294127
theorem B2763335 : Blo 860564 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B1944251 : Blo 860564 1944251 := bstep (se 1 (by rfl) ⟨1458188, by rfl⟩ : syracuseStep 1944251 = 2916377) B2916377
theorem B863067 : Blo 860564 863067 := bstep (se 1 (by rfl) ⟨647300, by rfl⟩ : syracuseStep 863067 = 1294601) B1294601
theorem B863135 : Blo 860564 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B863279 : Blo 860564 863279 := bstep (se 1 (by rfl) ⟨647459, by rfl⟩ : syracuseStep 863279 = 1294919) B1294919
theorem B863303 : Blo 860564 863303 := bstep (se 1 (by rfl) ⟨647477, by rfl⟩ : syracuseStep 863303 = 1294955) B1294955
theorem B1092791 : Blo 860564 1092791 := bstep (se 1 (by rfl) ⟨819593, by rfl⟩ : syracuseStep 1092791 = 1639187) B1639187
theorem B863455 : Blo 860564 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B1092943 : Blo 860564 1092943 := bstep (se 1 (by rfl) ⟨819707, by rfl⟩ : syracuseStep 1092943 = 1639415) B1639415
theorem B1453423 : Blo 860564 1453423 := bstep (se 1 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 1453423 = 2180135) B2180135
theorem B11054465 : Blo 860564 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B863719 : Blo 860564 863719 := bstep (se 1 (by rfl) ⟨647789, by rfl⟩ : syracuseStep 863719 = 1295579) B1295579
theorem B1945079 : Blo 860564 1945079 := bstep (se 1 (by rfl) ⟨1458809, by rfl⟩ : syracuseStep 1945079 = 2917619) B2917619
theorem B1945151 : Blo 860564 1945151 := bstep (se 1 (by rfl) ⟨1458863, by rfl⟩ : syracuseStep 1945151 = 2917727) B2917727
theorem B2764361 : Blo 860564 2764361 := bstep (se 2 (by rfl) ⟨1036635, by rfl⟩ : syracuseStep 2764361 = 2073271) B2073271
theorem B863835 : Blo 860564 863835 := bstep (se 1 (by rfl) ⟨647876, by rfl⟩ : syracuseStep 863835 = 1295753) B1295753
theorem B1453801 : Blo 860564 1453801 := bstep (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) B1090351
theorem B864071 : Blo 860564 864071 := bstep (se 1 (by rfl) ⟨648053, by rfl⟩ : syracuseStep 864071 = 1296107) B1296107
theorem B864223 : Blo 860564 864223 := bstep (se 1 (by rfl) ⟨648167, by rfl⟩ : syracuseStep 864223 = 1296335) B1296335
theorem B4665509 : Blo 860564 4665509 := bstep (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) B874783
theorem B1454267 : Blo 860564 1454267 := bstep (se 1 (by rfl) ⟨1090700, by rfl⟩ : syracuseStep 1454267 = 2181401) B2181401
theorem B864487 : Blo 860564 864487 := bstep (se 1 (by rfl) ⟨648365, by rfl⟩ : syracuseStep 864487 = 1296731) B1296731
theorem B1454827 : Blo 860564 1454827 := bstep (se 1 (by rfl) ⟨1091120, by rfl⟩ : syracuseStep 1454827 = 2182241) B2182241
theorem B1291049 : Blo 860564 1291049 := bstep (se 2 (by rfl) ⟨484143, by rfl⟩ : syracuseStep 1291049 = 968287) B968287
theorem B1291055 : Blo 860564 1291055 := bstep (se 1 (by rfl) ⟨968291, by rfl⟩ : syracuseStep 1291055 = 1936583) B1936583
theorem B63877987 : Blo 860564 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B1291175 : Blo 860564 1291175 := bstep (se 1 (by rfl) ⟨968381, by rfl⟩ : syracuseStep 1291175 = 1936763) B1936763
theorem B3322795 : Blo 860564 3322795 := bstep (se 1 (by rfl) ⟨2492096, by rfl⟩ : syracuseStep 3322795 = 4984193) B4984193
theorem B1291259 : Blo 860564 1291259 := bstep (se 1 (by rfl) ⟨968444, by rfl⟩ : syracuseStep 1291259 = 1936889) B1936889
theorem B1291319 : Blo 860564 1291319 := bstep (se 1 (by rfl) ⟨968489, by rfl⟩ : syracuseStep 1291319 = 1936979) B1936979
theorem B2765963 : Blo 860564 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B1291439 : Blo 860564 1291439 := bstep (se 1 (by rfl) ⟨968579, by rfl⟩ : syracuseStep 1291439 = 1937159) B1937159
theorem B4371731 : Blo 860564 4371731 := bstep (se 1 (by rfl) ⟨3278798, by rfl⟩ : syracuseStep 4371731 = 6557597) B6557597
theorem B1291847 : Blo 860564 1291847 := bstep (se 1 (by rfl) ⟨968885, by rfl⟩ : syracuseStep 1291847 = 1937771) B1937771
theorem B1291943 : Blo 860564 1291943 := bstep (se 1 (by rfl) ⟨968957, by rfl⟩ : syracuseStep 1291943 = 1937915) B1937915
theorem B1554103 : Blo 860564 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B1455799 : Blo 860564 1455799 := bstep (se 1 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 1455799 = 2183699) B2183699
theorem B1292027 : Blo 860564 1292027 := bstep (se 1 (by rfl) ⟨969020, by rfl⟩ : syracuseStep 1292027 = 1938041) B1938041
theorem B1292063 : Blo 860564 1292063 := bstep (se 1 (by rfl) ⟨969047, by rfl⟩ : syracuseStep 1292063 = 1938095) B1938095
theorem B1292111 : Blo 860564 1292111 := bstep (se 1 (by rfl) ⟨969083, by rfl⟩ : syracuseStep 1292111 = 1938167) B1938167
theorem B1292231 : Blo 860564 1292231 := bstep (se 1 (by rfl) ⟨969173, by rfl⟩ : syracuseStep 1292231 = 1938347) B1938347
theorem B9975773 : Blo 860564 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B1456103 : Blo 860564 1456103 := bstep (se 1 (by rfl) ⟨1092077, by rfl⟩ : syracuseStep 1456103 = 2184155) B2184155
theorem B1456319 : Blo 860564 1456319 := bstep (se 1 (by rfl) ⟨1092239, by rfl⟩ : syracuseStep 1456319 = 2184479) B2184479
theorem B5519623 : Blo 860564 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B1292585 : Blo 860564 1292585 := bstep (se 2 (by rfl) ⟨484719, by rfl⟩ : syracuseStep 1292585 = 969439) B969439
theorem B1292591 : Blo 860564 1292591 := bstep (se 1 (by rfl) ⟨969443, by rfl⟩ : syracuseStep 1292591 = 1938887) B1938887
theorem B9812339 : Blo 860564 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B1292831 : Blo 860564 1292831 := bstep (se 1 (by rfl) ⟨969623, by rfl⟩ : syracuseStep 1292831 = 1939247) B1939247
theorem B1456987 : Blo 860564 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B1293215 : Blo 860564 1293215 := bstep (se 1 (by rfl) ⟨969911, by rfl⟩ : syracuseStep 1293215 = 1939823) B1939823
theorem B1293263 : Blo 860564 1293263 := bstep (se 1 (by rfl) ⟨969947, by rfl⟩ : syracuseStep 1293263 = 1939895) B1939895
theorem B1227727 : Blo 860564 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B1293353 : Blo 860564 1293353 := bstep (se 2 (by rfl) ⟨485007, by rfl⟩ : syracuseStep 1293353 = 970015) B970015
theorem B1293359 : Blo 860564 1293359 := bstep (se 1 (by rfl) ⟨970019, by rfl⟩ : syracuseStep 1293359 = 1940039) B1940039
theorem B1293383 : Blo 860564 1293383 := bstep (se 1 (by rfl) ⟨970037, by rfl⟩ : syracuseStep 1293383 = 1940075) B1940075
theorem B1293647 : Blo 860564 1293647 := bstep (se 1 (by rfl) ⟨970235, by rfl⟩ : syracuseStep 1293647 = 1940471) B1940471
theorem B1293737 : Blo 860564 1293737 := bstep (se 2 (by rfl) ⟨485151, by rfl⟩ : syracuseStep 1293737 = 970303) B970303
theorem B2178515 : Blo 860564 2178515 := bstep (se 1 (by rfl) ⟨1633886, by rfl⟩ : syracuseStep 2178515 = 3267773) B3267773
theorem B2178535 : Blo 860564 2178535 := bstep (se 1 (by rfl) ⟨1633901, by rfl⟩ : syracuseStep 2178535 = 3267803) B3267803
theorem B1293887 : Blo 860564 1293887 := bstep (se 1 (by rfl) ⟨970415, by rfl⟩ : syracuseStep 1293887 = 1940831) B1940831
theorem B10468973 : Blo 860564 10468973 := bstep (se 3 (by rfl) ⟨1962932, by rfl⟩ : syracuseStep 10468973 = 3925865) B3925865
theorem B1457959 : Blo 860564 1457959 := bstep (se 1 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 1457959 = 2186939) B2186939
theorem B1294151 : Blo 860564 1294151 := bstep (se 1 (by rfl) ⟨970613, by rfl⟩ : syracuseStep 1294151 = 1941227) B1941227
theorem B1294235 : Blo 860564 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B6307865 : Blo 860564 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B4374809 : Blo 860564 4374809 := bstep (se 2 (by rfl) ⟨1640553, by rfl⟩ : syracuseStep 4374809 = 3281107) B3281107
theorem B6537671 : Blo 860564 6537671 := bstep (se 1 (by rfl) ⟨4903253, by rfl⟩ : syracuseStep 6537671 = 9806507) B9806507
theorem B1294799 : Blo 860564 1294799 := bstep (se 1 (by rfl) ⟨971099, by rfl⟩ : syracuseStep 1294799 = 1942199) B1942199
theorem B1294841 : Blo 860564 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B1294943 : Blo 860564 1294943 := bstep (se 1 (by rfl) ⟨971207, by rfl⟩ : syracuseStep 1294943 = 1942415) B1942415
theorem B4670351 : Blo 860564 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B1295423 : Blo 860564 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B1295465 : Blo 860564 1295465 := bstep (se 2 (by rfl) ⟨485799, by rfl⟩ : syracuseStep 1295465 = 971599) B971599
theorem B1295567 : Blo 860564 1295567 := bstep (se 1 (by rfl) ⟨971675, by rfl⟩ : syracuseStep 1295567 = 1943351) B1943351
theorem B2180459 : Blo 860564 2180459 := bstep (se 1 (by rfl) ⟨1635344, by rfl⟩ : syracuseStep 2180459 = 3270689) B3270689
theorem B1295771 : Blo 860564 1295771 := bstep (se 1 (by rfl) ⟨971828, by rfl⟩ : syracuseStep 1295771 = 1943657) B1943657
theorem B1295993 : Blo 860564 1295993 := bstep (se 2 (by rfl) ⟨485997, by rfl⟩ : syracuseStep 1295993 = 971995) B971995
theorem B968359 : Blo 860564 968359 := bstep (se 1 (by rfl) ⟨726269, by rfl⟩ : syracuseStep 968359 = 1452539) B1452539
theorem B1296095 : Blo 860564 1296095 := bstep (se 1 (by rfl) ⟨972071, by rfl⟩ : syracuseStep 1296095 = 1944143) B1944143
theorem B1296191 : Blo 860564 1296191 := bstep (se 1 (by rfl) ⟨972143, by rfl⟩ : syracuseStep 1296191 = 1944287) B1944287
theorem B1230655 : Blo 860564 1230655 := bstep (se 1 (by rfl) ⟨922991, by rfl⟩ : syracuseStep 1230655 = 1845983) B1845983
theorem B22071203 : Blo 860564 22071203 := bstep (se 1 (by rfl) ⟨16553402, by rfl⟩ : syracuseStep 22071203 = 33106805) B33106805
theorem B8308655 : Blo 860564 8308655 := bstep (se 1 (by rfl) ⟨6231491, by rfl⟩ : syracuseStep 8308655 = 12462983) B12462983
theorem B968647 : Blo 860564 968647 := bstep (se 1 (by rfl) ⟨726485, by rfl⟩ : syracuseStep 968647 = 1452971) B1452971
theorem B1296359 : Blo 860564 1296359 := bstep (se 1 (by rfl) ⟨972269, by rfl⟩ : syracuseStep 1296359 = 1944539) B1944539
theorem B1296377 : Blo 860564 1296377 := bstep (se 2 (by rfl) ⟨486141, by rfl⟩ : syracuseStep 1296377 = 972283) B972283
theorem B8407091 : Blo 860564 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B1296479 : Blo 860564 1296479 := bstep (se 1 (by rfl) ⟨972359, by rfl⟩ : syracuseStep 1296479 = 1944719) B1944719
theorem B1296539 : Blo 860564 1296539 := bstep (se 1 (by rfl) ⟨972404, by rfl⟩ : syracuseStep 1296539 = 1944809) B1944809
theorem B3492031 : Blo 860564 3492031 := bstep (se 1 (by rfl) ⟨2619023, by rfl⟩ : syracuseStep 3492031 = 5238047) B5238047
theorem B7096511 : Blo 860564 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B1296575 : Blo 860564 1296575 := bstep (se 1 (by rfl) ⟨972431, by rfl⟩ : syracuseStep 1296575 = 1944863) B1944863
theorem B1296617 : Blo 860564 1296617 := bstep (se 2 (by rfl) ⟨486231, by rfl⟩ : syracuseStep 1296617 = 972463) B972463
theorem B8866039 : Blo 860564 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B969007 : Blo 860564 969007 := bstep (se 1 (by rfl) ⟨726755, by rfl⟩ : syracuseStep 969007 = 1453511) B1453511
theorem B14731631 : Blo 860564 14731631 := bstep (se 1 (by rfl) ⟨11048723, by rfl⟩ : syracuseStep 14731631 = 22097447) B22097447
theorem B2247355 : Blo 860564 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B6212371 : Blo 860564 6212371 := bstep (se 1 (by rfl) ⟨4659278, by rfl⟩ : syracuseStep 6212371 = 9318557) B9318557
theorem B10472435 : Blo 860564 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B969799 : Blo 860564 969799 := bstep (se 1 (by rfl) ⟨727349, by rfl⟩ : syracuseStep 969799 = 1454699) B1454699
theorem B18927089 : Blo 860564 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B10472975 : Blo 860564 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B5525081 : Blo 860564 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B7360145 : Blo 860564 7360145 := bstep (se 2 (by rfl) ⟨2760054, by rfl⟩ : syracuseStep 7360145 = 5520109) B5520109
theorem B2183051 : Blo 860564 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B9457955 : Blo 860564 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B2904659 : Blo 860564 2904659 := bstep (se 1 (by rfl) ⟨2178494, by rfl⟩ : syracuseStep 2904659 = 4356989) B4356989
theorem B3494785 : Blo 860564 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B5526467 : Blo 860564 5526467 := bstep (se 1 (by rfl) ⟨4144850, by rfl⟩ : syracuseStep 5526467 = 8289701) B8289701
theorem B2184367 : Blo 860564 2184367 := bstep (se 1 (by rfl) ⟨1638275, by rfl⟩ : syracuseStep 2184367 = 3276551) B3276551
theorem B3364051 : Blo 860564 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B2905307 : Blo 860564 2905307 := bstep (se 1 (by rfl) ⟨2178980, by rfl⟩ : syracuseStep 2905307 = 4357961) B4357961
theorem B972607 : Blo 860564 972607 := bstep (se 1 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 972607 = 1458911) B1458911
theorem B7362535 : Blo 860564 7362535 := bstep (se 1 (by rfl) ⟨5521901, by rfl⟩ : syracuseStep 7362535 = 11043803) B11043803
theorem B2906171 : Blo 860564 2906171 := bstep (se 1 (by rfl) ⟨2179628, by rfl⟩ : syracuseStep 2906171 = 4359257) B4359257
theorem B2906441 : Blo 860564 2906441 := bstep (se 2 (by rfl) ⟨1089915, by rfl⟩ : syracuseStep 2906441 = 2179831) B2179831
theorem B12409517 : Blo 860564 12409517 := bstep (se 3 (by rfl) ⟨2326784, by rfl⟩ : syracuseStep 12409517 = 4653569) B4653569
theorem B11033657 : Blo 860564 11033657 := bstep (se 2 (by rfl) ⟨4137621, by rfl⟩ : syracuseStep 11033657 = 8275243) B8275243
theorem B2186311 : Blo 860564 2186311 := bstep (se 1 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 2186311 = 3279467) B3279467
theorem B2186423 : Blo 860564 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1662439 : Blo 860564 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B2907791 : Blo 860564 2907791 := bstep (se 1 (by rfl) ⟨2180843, by rfl⟩ : syracuseStep 2907791 = 4361687) B4361687
theorem B6545447 : Blo 860564 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B9822545 : Blo 860564 9822545 := bstep (se 2 (by rfl) ⟨3683454, by rfl⟩ : syracuseStep 9822545 = 7366909) B7366909
theorem B2187719 : Blo 860564 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B5595787 : Blo 860564 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B2908925 : Blo 860564 2908925 := bstep (se 3 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 2908925 = 1090847) B1090847
theorem B4154267 : Blo 860564 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B6546419 : Blo 860564 6546419 := bstep (se 1 (by rfl) ⟨4909814, by rfl⟩ : syracuseStep 6546419 = 9819629) B9819629
theorem B6644825 : Blo 860564 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B4908221 : Blo 860564 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B5531129 : Blo 860564 5531129 := bstep (se 2 (by rfl) ⟨2074173, by rfl⟩ : syracuseStep 5531129 = 4148347) B4148347
theorem B5596723 : Blo 860564 5596723 := bstep (se 1 (by rfl) ⟨4197542, by rfl⟩ : syracuseStep 5596723 = 8395085) B8395085
theorem B2911031 : Blo 860564 2911031 := bstep (se 1 (by rfl) ⟨2183273, by rfl⟩ : syracuseStep 2911031 = 4366547) B4366547
theorem B3501191 : Blo 860564 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B12414131 : Blo 860564 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B15756743 : Blo 860564 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B16576163 : Blo 860564 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B2453267 : Blo 860564 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B7565075 : Blo 860564 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B14151667 : Blo 860564 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B1863803 : Blo 860564 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B9433253 : Blo 860564 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B6287759 : Blo 860564 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B1635079 : Blo 860564 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B1635383 : Blo 860564 1635383 := bstep (se 1 (by rfl) ⟨1226537, by rfl⟩ : syracuseStep 1635383 = 2453075) B2453075
theorem B2913353 : Blo 860564 2913353 := bstep (se 2 (by rfl) ⟨1092507, by rfl⟩ : syracuseStep 2913353 = 2185015) B2185015
theorem B20936393 : Blo 860564 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B9434825 : Blo 860564 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B2455535 : Blo 860564 2455535 := bstep (se 1 (by rfl) ⟨1841651, by rfl⟩ : syracuseStep 2455535 = 3683303) B3683303
theorem B2455751 : Blo 860564 2455751 := bstep (se 1 (by rfl) ⟨1841813, by rfl⟩ : syracuseStep 2455751 = 3683627) B3683627
theorem B2488765 : Blo 860564 2488765 := bstep (se 3 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 2488765 = 933287) B933287
theorem B7371283 : Blo 860564 7371283 := bstep (se 1 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 7371283 = 11056925) B11056925
theorem B4356665 : Blo 860564 4356665 := bstep (se 2 (by rfl) ⟨1633749, by rfl⟩ : syracuseStep 4356665 = 3267499) B3267499
theorem B11041343 : Blo 860564 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B2914973 : Blo 860564 2914973 := bstep (se 3 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 2914973 = 1093115) B1093115
theorem B22084325 : Blo 860564 22084325 := bstep (se 4 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 22084325 = 4140811) B4140811
theorem B24837029 : Blo 860564 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B1637327 : Blo 860564 1637327 := bstep (se 1 (by rfl) ⟨1227995, by rfl⟩ : syracuseStep 1637327 = 2455991) B2455991
theorem B11828177 : Blo 860564 11828177 := bstep (se 2 (by rfl) ⟨4435566, by rfl⟩ : syracuseStep 11828177 = 8871133) B8871133
theorem B2915297 : Blo 860564 2915297 := bstep (se 2 (by rfl) ⟨1093236, by rfl⟩ : syracuseStep 2915297 = 2186473) B2186473
theorem B982087 : Blo 860564 982087 := bstep (se 1 (by rfl) ⟨736565, by rfl⟩ : syracuseStep 982087 = 1473131) B1473131
theorem B2915513 : Blo 860564 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B2456993 : Blo 860564 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B3276521 : Blo 860564 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B3112759 : Blo 860564 3112759 := bstep (se 1 (by rfl) ⟨2334569, by rfl⟩ : syracuseStep 3112759 = 4669139) B4669139
theorem B1638215 : Blo 860564 1638215 := bstep (se 1 (by rfl) ⟨1228661, by rfl⟩ : syracuseStep 1638215 = 2457323) B2457323
theorem B2916539 : Blo 860564 2916539 := bstep (se 1 (by rfl) ⟨2187404, by rfl⟩ : syracuseStep 2916539 = 4374809) B4374809
theorem B4358447 : Blo 860564 4358447 := bstep (se 1 (by rfl) ⟨3268835, by rfl⟩ : syracuseStep 4358447 = 6537671) B6537671
theorem B3113567 : Blo 860564 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B6554681 : Blo 860564 6554681 := bstep (se 2 (by rfl) ⟨2458005, by rfl⟩ : syracuseStep 6554681 = 4916011) B4916011
theorem B14714135 : Blo 860564 14714135 := bstep (se 1 (by rfl) ⟨11035601, by rfl⟩ : syracuseStep 14714135 = 22071203) B22071203
theorem B5539103 : Blo 860564 5539103 := bstep (se 1 (by rfl) ⟨4154327, by rfl⟩ : syracuseStep 5539103 = 8308655) B8308655
theorem B5604727 : Blo 860564 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B6555167 : Blo 860564 6555167 := bstep (se 1 (by rfl) ⟨4916375, by rfl⟩ : syracuseStep 6555167 = 9832751) B9832751
theorem B2328169 : Blo 860564 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B2623375 : Blo 860564 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B2623471 : Blo 860564 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B2492399 : Blo 860564 2492399 := bstep (se 1 (by rfl) ⟨1869299, by rfl⟩ : syracuseStep 2492399 = 3738599) B3738599
theorem B6981623 : Blo 860564 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B3115169 : Blo 860564 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B12618059 : Blo 860564 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B6981983 : Blo 860564 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B1640827 : Blo 860564 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B11078045 : Blo 860564 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B1640873 : Blo 860564 1640873 := bstep (se 2 (by rfl) ⟨615327, by rfl⟩ : syracuseStep 1640873 = 1230655) B1230655
theorem B14944819 : Blo 860564 14944819 := bstep (se 1 (by rfl) ⟨11208614, by rfl⟩ : syracuseStep 14944819 = 22417229) B22417229
theorem B1641055 : Blo 860564 1641055 := bstep (se 1 (by rfl) ⟨1230791, by rfl⟩ : syracuseStep 1641055 = 2461583) B2461583
theorem B60689225 : Blo 860564 60689225 := bstep (se 2 (by rfl) ⟨22758459, by rfl⟩ : syracuseStep 60689225 = 45516919) B45516919
theorem B4197203 : Blo 860564 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B18877279 : Blo 860564 18877279 := bstep (se 1 (by rfl) ⟨14157959, by rfl⟩ : syracuseStep 18877279 = 28315919) B28315919
theorem B4656041 : Blo 860564 4656041 := bstep (se 2 (by rfl) ⟨1746015, by rfl⟩ : syracuseStep 4656041 = 3492031) B3492031
theorem B1936439 : Blo 860564 1936439 := bstep (se 1 (by rfl) ⟨1452329, by rfl⟩ : syracuseStep 1936439 = 2904659) B2904659
theorem B13962527 : Blo 860564 13962527 := bstep (se 1 (by rfl) ⟨10471895, by rfl⟩ : syracuseStep 13962527 = 20943791) B20943791
theorem B6557111 : Blo 860564 6557111 := bstep (se 1 (by rfl) ⟨4917833, by rfl⟩ : syracuseStep 6557111 = 9835667) B9835667
theorem B1936871 : Blo 860564 1936871 := bstep (se 1 (by rfl) ⟨1452653, by rfl⟩ : syracuseStep 1936871 = 2905307) B2905307
theorem B1937447 : Blo 860564 1937447 := bstep (se 1 (by rfl) ⟨1453085, by rfl⟩ : syracuseStep 1937447 = 2906171) B2906171
theorem B1839199 : Blo 860564 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B921727 : Blo 860564 921727 := bstep (se 1 (by rfl) ⟨691295, by rfl⟩ : syracuseStep 921727 = 1382591) B1382591
theorem B1937627 : Blo 860564 1937627 := bstep (se 1 (by rfl) ⟨1453220, by rfl⟩ : syracuseStep 1937627 = 2906441) B2906441
theorem B1937897 : Blo 860564 1937897 := bstep (se 2 (by rfl) ⟨726711, by rfl⟩ : syracuseStep 1937897 = 1453423) B1453423
theorem B3936851 : Blo 860564 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B1938401 : Blo 860564 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B1938527 : Blo 860564 1938527 := bstep (se 1 (by rfl) ⟨1453895, by rfl⟩ : syracuseStep 1938527 = 2907791) B2907791
theorem B4363631 : Blo 860564 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B923119 : Blo 860564 923119 := bstep (se 1 (by rfl) ⟨692339, by rfl⟩ : syracuseStep 923119 = 1384679) B1384679
theorem B4920911 : Blo 860564 4920911 := bstep (se 1 (by rfl) ⟨3690683, by rfl⟩ : syracuseStep 4920911 = 7381367) B7381367
theorem B1939283 : Blo 860564 1939283 := bstep (se 1 (by rfl) ⟨1454462, by rfl⟩ : syracuseStep 1939283 = 2908925) B2908925
theorem B5248891 : Blo 860564 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B4364279 : Blo 860564 4364279 := bstep (se 1 (by rfl) ⟨3273209, by rfl⟩ : syracuseStep 4364279 = 6546419) B6546419
theorem B4429883 : Blo 860564 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B1939769 : Blo 860564 1939769 := bstep (se 2 (by rfl) ⟨727413, by rfl⟩ : syracuseStep 1939769 = 1454827) B1454827
theorem B85170649 : Blo 860564 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B4659713 : Blo 860564 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B4430393 : Blo 860564 4430393 := bstep (se 2 (by rfl) ⟨1661397, by rfl⟩ : syracuseStep 4430393 = 3322795) B3322795
theorem B1940687 : Blo 860564 1940687 := bstep (se 1 (by rfl) ⟨1455515, by rfl⟩ : syracuseStep 1940687 = 2911031) B2911031
theorem B2072137 : Blo 860564 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B1941065 : Blo 860564 1941065 := bstep (se 2 (by rfl) ⟨727899, by rfl⟩ : syracuseStep 1941065 = 1455799) B1455799
theorem B1842907 : Blo 860564 1842907 := bstep (se 1 (by rfl) ⟨1382180, by rfl⟩ : syracuseStep 1842907 = 2764361) B2764361
theorem B11050775 : Blo 860564 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B3547265 : Blo 860564 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B860699 : Blo 860564 860699 := bstep (se 1 (by rfl) ⟨645524, by rfl⟩ : syracuseStep 860699 = 1291049) B1291049
theorem B860703 : Blo 860564 860703 := bstep (se 1 (by rfl) ⟨645527, by rfl⟩ : syracuseStep 860703 = 1291055) B1291055
theorem B3318353 : Blo 860564 3318353 := bstep (se 2 (by rfl) ⟨1244382, by rfl⟩ : syracuseStep 3318353 = 2488765) B2488765
theorem B860783 : Blo 860564 860783 := bstep (se 1 (by rfl) ⟨645587, by rfl⟩ : syracuseStep 860783 = 1291175) B1291175
theorem B860839 : Blo 860564 860839 := bstep (se 1 (by rfl) ⟨645629, by rfl⟩ : syracuseStep 860839 = 1291259) B1291259
theorem B860879 : Blo 860564 860879 := bstep (se 1 (by rfl) ⟨645659, by rfl⟩ : syracuseStep 860879 = 1291319) B1291319
theorem B1090255 : Blo 860564 1090255 := bstep (se 1 (by rfl) ⟨817691, by rfl⟩ : syracuseStep 1090255 = 1635383) B1635383
theorem B1942235 : Blo 860564 1942235 := bstep (se 1 (by rfl) ⟨1456676, by rfl⟩ : syracuseStep 1942235 = 2913353) B2913353
theorem B1843975 : Blo 860564 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B860959 : Blo 860564 860959 := bstep (se 1 (by rfl) ⟨645719, by rfl⟩ : syracuseStep 860959 = 1291439) B1291439
theorem B861231 : Blo 860564 861231 := bstep (se 1 (by rfl) ⟨645923, by rfl⟩ : syracuseStep 861231 = 1291847) B1291847
theorem B861295 : Blo 860564 861295 := bstep (se 1 (by rfl) ⟨645971, by rfl⟩ : syracuseStep 861295 = 1291943) B1291943
theorem B1942649 : Blo 860564 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B861351 : Blo 860564 861351 := bstep (se 1 (by rfl) ⟨646013, by rfl⟩ : syracuseStep 861351 = 1292027) B1292027
theorem B861375 : Blo 860564 861375 := bstep (se 1 (by rfl) ⟨646031, by rfl⟩ : syracuseStep 861375 = 1292063) B1292063
theorem B861407 : Blo 860564 861407 := bstep (se 1 (by rfl) ⟨646055, by rfl⟩ : syracuseStep 861407 = 1292111) B1292111
theorem B861487 : Blo 860564 861487 := bstep (se 1 (by rfl) ⟨646115, by rfl⟩ : syracuseStep 861487 = 1292231) B1292231
theorem B861723 : Blo 860564 861723 := bstep (se 1 (by rfl) ⟨646292, by rfl⟩ : syracuseStep 861723 = 1292585) B1292585
theorem B861727 : Blo 860564 861727 := bstep (se 1 (by rfl) ⟨646295, by rfl⟩ : syracuseStep 861727 = 1292591) B1292591
theorem B861887 : Blo 860564 861887 := bstep (se 1 (by rfl) ⟨646415, by rfl⟩ : syracuseStep 861887 = 1292831) B1292831
theorem B1943315 : Blo 860564 1943315 := bstep (se 1 (by rfl) ⟨1457486, by rfl⟩ : syracuseStep 1943315 = 2914973) B2914973
theorem B14722883 : Blo 860564 14722883 := bstep (se 1 (by rfl) ⟨11042162, by rfl⟩ : syracuseStep 14722883 = 22084325) B22084325
theorem B862143 : Blo 860564 862143 := bstep (se 1 (by rfl) ⟨646607, by rfl⟩ : syracuseStep 862143 = 1293215) B1293215
theorem B16558019 : Blo 860564 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B862175 : Blo 860564 862175 := bstep (se 1 (by rfl) ⟨646631, by rfl⟩ : syracuseStep 862175 = 1293263) B1293263
theorem B1091551 : Blo 860564 1091551 := bstep (se 1 (by rfl) ⟨818663, by rfl⟩ : syracuseStep 1091551 = 1637327) B1637327
theorem B1943531 : Blo 860564 1943531 := bstep (se 1 (by rfl) ⟨1457648, by rfl⟩ : syracuseStep 1943531 = 2915297) B2915297
theorem B862235 : Blo 860564 862235 := bstep (se 1 (by rfl) ⟨646676, by rfl⟩ : syracuseStep 862235 = 1293353) B1293353
theorem B862239 : Blo 860564 862239 := bstep (se 1 (by rfl) ⟨646679, by rfl⟩ : syracuseStep 862239 = 1293359) B1293359
theorem B862255 : Blo 860564 862255 := bstep (se 1 (by rfl) ⟨646691, by rfl⟩ : syracuseStep 862255 = 1293383) B1293383
theorem B1943675 : Blo 860564 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B862431 : Blo 860564 862431 := bstep (se 1 (by rfl) ⟨646823, by rfl⟩ : syracuseStep 862431 = 1293647) B1293647
theorem B862491 : Blo 860564 862491 := bstep (se 1 (by rfl) ⟨646868, by rfl⟩ : syracuseStep 862491 = 1293737) B1293737
theorem B1452343 : Blo 860564 1452343 := bstep (se 1 (by rfl) ⟨1089257, by rfl⟩ : syracuseStep 1452343 = 2178515) B2178515
theorem B3680585 : Blo 860564 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B862591 : Blo 860564 862591 := bstep (se 1 (by rfl) ⟨646943, by rfl⟩ : syracuseStep 862591 = 1293887) B1293887
theorem B1943945 : Blo 860564 1943945 := bstep (se 2 (by rfl) ⟨728979, by rfl⟩ : syracuseStep 1943945 = 1457959) B1457959
theorem B1845641 : Blo 860564 1845641 := bstep (se 2 (by rfl) ⟨692115, by rfl⟩ : syracuseStep 1845641 = 1384231) B1384231
theorem B862767 : Blo 860564 862767 := bstep (se 1 (by rfl) ⟨647075, by rfl⟩ : syracuseStep 862767 = 1294151) B1294151
theorem B1092143 : Blo 860564 1092143 := bstep (se 1 (by rfl) ⟨819107, by rfl⟩ : syracuseStep 1092143 = 1638215) B1638215
theorem B862823 : Blo 860564 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B4205243 : Blo 860564 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B863199 : Blo 860564 863199 := bstep (se 1 (by rfl) ⟨647399, by rfl⟩ : syracuseStep 863199 = 1294799) B1294799
theorem B863227 : Blo 860564 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B863295 : Blo 860564 863295 := bstep (se 1 (by rfl) ⟨647471, by rfl⟩ : syracuseStep 863295 = 1294943) B1294943
theorem B1944647 : Blo 860564 1944647 := bstep (se 1 (by rfl) ⟨1458485, by rfl⟩ : syracuseStep 1944647 = 2916971) B2916971
theorem B863615 : Blo 860564 863615 := bstep (se 1 (by rfl) ⟨647711, by rfl⟩ : syracuseStep 863615 = 1295423) B1295423
theorem B863643 : Blo 860564 863643 := bstep (se 1 (by rfl) ⟨647732, by rfl⟩ : syracuseStep 863643 = 1295465) B1295465
theorem B1945043 : Blo 860564 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B863711 : Blo 860564 863711 := bstep (se 1 (by rfl) ⟨647783, by rfl⟩ : syracuseStep 863711 = 1295567) B1295567
theorem B1453639 : Blo 860564 1453639 := bstep (se 1 (by rfl) ⟨1090229, by rfl⟩ : syracuseStep 1453639 = 2180459) B2180459
theorem B863847 : Blo 860564 863847 := bstep (se 1 (by rfl) ⟨647885, by rfl⟩ : syracuseStep 863847 = 1295771) B1295771
theorem B863995 : Blo 860564 863995 := bstep (se 1 (by rfl) ⟨647996, by rfl⟩ : syracuseStep 863995 = 1295993) B1295993
theorem B1093439 : Blo 860564 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B864063 : Blo 860564 864063 := bstep (se 1 (by rfl) ⟨648047, by rfl⟩ : syracuseStep 864063 = 1296095) B1296095
theorem B864127 : Blo 860564 864127 := bstep (se 1 (by rfl) ⟨648095, by rfl⟩ : syracuseStep 864127 = 1296191) B1296191
theorem B864239 : Blo 860564 864239 := bstep (se 1 (by rfl) ⟨648179, by rfl⟩ : syracuseStep 864239 = 1296359) B1296359
theorem B864251 : Blo 860564 864251 := bstep (se 1 (by rfl) ⟨648188, by rfl⟩ : syracuseStep 864251 = 1296377) B1296377
theorem B100642823 : Blo 860564 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B864319 : Blo 860564 864319 := bstep (se 1 (by rfl) ⟨648239, by rfl⟩ : syracuseStep 864319 = 1296479) B1296479
theorem B864359 : Blo 860564 864359 := bstep (se 1 (by rfl) ⟨648269, by rfl⟩ : syracuseStep 864359 = 1296539) B1296539
theorem B864383 : Blo 860564 864383 := bstep (se 1 (by rfl) ⟨648287, by rfl⟩ : syracuseStep 864383 = 1296575) B1296575
theorem B864411 : Blo 860564 864411 := bstep (se 1 (by rfl) ⟨648308, by rfl⟩ : syracuseStep 864411 = 1296617) B1296617
theorem B1291145 : Blo 860564 1291145 := bstep (se 2 (by rfl) ⟨484179, by rfl⟩ : syracuseStep 1291145 = 968359) B968359
theorem B1455097 : Blo 860564 1455097 := bstep (se 2 (by rfl) ⟨545661, by rfl⟩ : syracuseStep 1455097 = 1091323) B1091323
theorem B3322919 : Blo 860564 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B3683387 : Blo 860564 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B1455367 : Blo 860564 1455367 := bstep (se 1 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 1455367 = 2183051) B2183051
theorem B1291529 : Blo 860564 1291529 := bstep (se 2 (by rfl) ⟨484323, by rfl⟩ : syracuseStep 1291529 = 968647) B968647
theorem B1291583 : Blo 860564 1291583 := bstep (se 1 (by rfl) ⟨968687, by rfl⟩ : syracuseStep 1291583 = 1937375) B1937375
theorem B6305303 : Blo 860564 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B1292009 : Blo 860564 1292009 := bstep (se 2 (by rfl) ⟨484503, by rfl⟩ : syracuseStep 1292009 = 969007) B969007
theorem B1292015 : Blo 860564 1292015 := bstep (se 1 (by rfl) ⟨969011, by rfl⟩ : syracuseStep 1292015 = 1938023) B1938023
theorem B12433277 : Blo 860564 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B3684311 : Blo 860564 3684311 := bstep (se 1 (by rfl) ⟨2763233, by rfl⟩ : syracuseStep 3684311 = 5526467) B5526467
theorem B1292471 : Blo 860564 1292471 := bstep (se 1 (by rfl) ⟨969353, by rfl⟩ : syracuseStep 1292471 = 1938707) B1938707
theorem B1292519 : Blo 860564 1292519 := bstep (se 1 (by rfl) ⟨969389, by rfl⟩ : syracuseStep 1292519 = 1938779) B1938779
theorem B79804723 : Blo 860564 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B1292891 : Blo 860564 1292891 := bstep (se 1 (by rfl) ⟨969668, by rfl⟩ : syracuseStep 1292891 = 1939337) B1939337
theorem B1293035 : Blo 860564 1293035 := bstep (se 1 (by rfl) ⟨969776, by rfl⟩ : syracuseStep 1293035 = 1939553) B1939553
theorem B1293065 : Blo 860564 1293065 := bstep (se 2 (by rfl) ⟨484899, by rfl⟩ : syracuseStep 1293065 = 969799) B969799
theorem B1457257 : Blo 860564 1457257 := bstep (se 2 (by rfl) ⟨546471, by rfl⟩ : syracuseStep 1457257 = 1092943) B1092943
theorem B8273011 : Blo 860564 8273011 := bstep (se 1 (by rfl) ⟨6204758, by rfl⟩ : syracuseStep 8273011 = 12409517) B12409517
theorem B7355771 : Blo 860564 7355771 := bstep (se 1 (by rfl) ⟨5516828, by rfl⟩ : syracuseStep 7355771 = 11033657) B11033657
theorem B1555919 : Blo 860564 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B1457615 : Blo 860564 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B1293935 : Blo 860564 1293935 := bstep (se 1 (by rfl) ⟨970451, by rfl⟩ : syracuseStep 1293935 = 1940903) B1940903
theorem B1294055 : Blo 860564 1294055 := bstep (se 1 (by rfl) ⟨970541, by rfl⟩ : syracuseStep 1294055 = 1941083) B1941083
theorem B1294247 : Blo 860564 1294247 := bstep (se 1 (by rfl) ⟨970685, by rfl⟩ : syracuseStep 1294247 = 1941371) B1941371
theorem B1294571 : Blo 860564 1294571 := bstep (se 1 (by rfl) ⟨970928, by rfl⟩ : syracuseStep 1294571 = 1941857) B1941857
theorem B1294631 : Blo 860564 1294631 := bstep (se 1 (by rfl) ⟨970973, by rfl⟩ : syracuseStep 1294631 = 1941947) B1941947
theorem B1458479 : Blo 860564 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B18924029 : Blo 860564 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1295303 : Blo 860564 1295303 := bstep (se 1 (by rfl) ⟨971477, by rfl⟩ : syracuseStep 1295303 = 1942955) B1942955
theorem B3687419 : Blo 860564 3687419 := bstep (se 1 (by rfl) ⟨2765564, by rfl⟩ : syracuseStep 3687419 = 5531129) B5531129
theorem B2180105 : Blo 860564 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B1295471 : Blo 860564 1295471 := bstep (se 1 (by rfl) ⟨971603, by rfl⟩ : syracuseStep 1295471 = 1943207) B1943207
theorem B1295663 : Blo 860564 1295663 := bstep (se 1 (by rfl) ⟨971747, by rfl⟩ : syracuseStep 1295663 = 1943495) B1943495
theorem B3327419 : Blo 860564 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B1295867 : Blo 860564 1295867 := bstep (se 1 (by rfl) ⟨971900, by rfl⟩ : syracuseStep 1295867 = 1943801) B1943801
theorem B1295903 : Blo 860564 1295903 := bstep (se 1 (by rfl) ⟨971927, by rfl⟩ : syracuseStep 1295903 = 1943855) B1943855
theorem B1296047 : Blo 860564 1296047 := bstep (se 1 (by rfl) ⟨972035, by rfl⟩ : syracuseStep 1296047 = 1944071) B1944071
theorem B1296167 : Blo 860564 1296167 := bstep (se 1 (by rfl) ⟨972125, by rfl⟩ : syracuseStep 1296167 = 1944251) B1944251
theorem B8276087 : Blo 860564 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B10504495 : Blo 860564 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B1296719 : Blo 860564 1296719 := bstep (se 1 (by rfl) ⟨972539, by rfl⟩ : syracuseStep 1296719 = 1945079) B1945079
theorem B1296767 : Blo 860564 1296767 := bstep (se 1 (by rfl) ⟨972575, by rfl⟩ : syracuseStep 1296767 = 1945151) B1945151
theorem B1296809 : Blo 860564 1296809 := bstep (se 2 (by rfl) ⟨486303, by rfl⟩ : syracuseStep 1296809 = 972607) B972607
theorem B9816713 : Blo 860564 9816713 := bstep (se 2 (by rfl) ⟨3681267, by rfl⟩ : syracuseStep 9816713 = 7362535) B7362535
theorem B969511 : Blo 860564 969511 := bstep (se 1 (by rfl) ⟨727133, by rfl⟩ : syracuseStep 969511 = 1454267) B1454267
theorem B7359497 : Blo 860564 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B9096425 : Blo 860564 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B970735 : Blo 860564 970735 := bstep (se 1 (by rfl) ⟨728051, by rfl⟩ : syracuseStep 970735 = 1456103) B1456103
theorem B10506341 : Blo 860564 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B970879 : Blo 860564 970879 := bstep (se 1 (by rfl) ⟨728159, by rfl⟩ : syracuseStep 970879 = 1456319) B1456319
theorem B6541559 : Blo 860564 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B16601381 : Blo 860564 16601381 := bstep (se 4 (by rfl) ⟨1556379, by rfl⟩ : syracuseStep 16601381 = 3112759) B3112759
theorem B2904443 : Blo 860564 2904443 := bstep (se 1 (by rfl) ⟨2178332, by rfl⟩ : syracuseStep 2904443 = 4356665) B4356665
theorem B7360895 : Blo 860564 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B2904713 : Blo 860564 2904713 := bstep (se 2 (by rfl) ⟨1089267, by rfl⟩ : syracuseStep 2904713 = 2178535) B2178535
theorem B2216585 : Blo 860564 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B7885451 : Blo 860564 7885451 := bstep (se 1 (by rfl) ⟨5914088, by rfl⟩ : syracuseStep 7885451 = 11828177) B11828177
theorem B6542045 : Blo 860564 6542045 := bstep (se 3 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 6542045 = 2453267) B2453267
theorem B11228149 : Blo 860564 11228149 := bstep (se 5 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 11228149 = 1052639) B1052639
theorem B2184347 : Blo 860564 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B3495305 : Blo 860564 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B13981081 : Blo 860564 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B3103073 : Blo 860564 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B14736005 : Blo 860564 14736005 := bstep (se 4 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 14736005 = 2763001) B2763001
theorem B9821087 : Blo 860564 9821087 := bstep (se 1 (by rfl) ⟨7365815, by rfl⟩ : syracuseStep 9821087 = 14731631) B14731631
theorem B7363871 : Blo 860564 7363871 := bstep (se 1 (by rfl) ⟨5522903, by rfl⟩ : syracuseStep 7363871 = 11045807) B11045807
theorem B7462297 : Blo 860564 7462297 := bstep (se 2 (by rfl) ⟨2798361, by rfl⟩ : syracuseStep 7462297 = 5596723) B5596723
theorem B875983 : Blo 860564 875983 := bstep (se 1 (by rfl) ⟨656987, by rfl⟩ : syracuseStep 875983 = 1313975) B1313975
theorem B4906763 : Blo 860564 4906763 := bstep (se 1 (by rfl) ⟨3680072, by rfl⟩ : syracuseStep 4906763 = 7360145) B7360145
theorem B11821385 : Blo 860564 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B29844197 : Blo 860564 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B11985893 : Blo 860564 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B8283161 : Blo 860564 8283161 := bstep (se 2 (by rfl) ⟨3106185, by rfl⟩ : syracuseStep 8283161 = 6212371) B6212371
theorem B5531591 : Blo 860564 5531591 := bstep (se 1 (by rfl) ⟨4148693, by rfl⟩ : syracuseStep 5531591 = 8297387) B8297387
theorem B6547877 : Blo 860564 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B18868889 : Blo 860564 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B6548363 : Blo 860564 6548363 := bstep (se 1 (by rfl) ⟨4911272, by rfl⟩ : syracuseStep 6548363 = 9822545) B9822545
theorem B4909997 : Blo 860564 4909997 := bstep (se 3 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 4909997 = 1841249) B1841249
theorem B5237797 : Blo 860564 5237797 := bstep (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) B982087
theorem B2911517 : Blo 860564 2911517 := bstep (se 3 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 2911517 = 1091819) B1091819
theorem B3272147 : Blo 860564 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B2912219 : Blo 860564 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B7368893 : Blo 860564 7368893 := bstep (se 3 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 7368893 = 2763335) B2763335
theorem B2912489 : Blo 860564 2912489 := bstep (se 2 (by rfl) ⟨1092183, by rfl⟩ : syracuseStep 2912489 = 2184367) B2184367
theorem B4485401 : Blo 860564 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B7369643 : Blo 860564 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B5043383 : Blo 860564 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B1242535 : Blo 860564 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B6288835 : Blo 860564 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B3110339 : Blo 860564 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B4191839 : Blo 860564 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B9336509 : Blo 860564 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B2914109 : Blo 860564 2914109 := bstep (se 3 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 2914109 = 1092791) B1092791
theorem B9828377 : Blo 860564 9828377 := bstep (se 2 (by rfl) ⟨3685641, by rfl⟩ : syracuseStep 9828377 = 7371283) B7371283
theorem B2914487 : Blo 860564 2914487 := bstep (se 1 (by rfl) ⟨2185865, by rfl⟩ : syracuseStep 2914487 = 4371731) B4371731
theorem B13957595 : Blo 860564 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B6289883 : Blo 860564 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B6650515 : Blo 860564 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B1637023 : Blo 860564 1637023 := bstep (se 1 (by rfl) ⟨1227767, by rfl⟩ : syracuseStep 1637023 = 2455535) B2455535
theorem B2915081 : Blo 860564 2915081 := bstep (se 2 (by rfl) ⟨1093155, by rfl⟩ : syracuseStep 2915081 = 2186311) B2186311
theorem B1637167 : Blo 860564 1637167 := bstep (se 1 (by rfl) ⟨1227875, by rfl⟩ : syracuseStep 1637167 = 2455751) B2455751
theorem B27917261 : Blo 860564 27917261 := bstep (se 3 (by rfl) ⟨5234486, by rfl⟩ : syracuseStep 27917261 = 10468973) B10468973
theorem B6651233 : Blo 860564 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B1637995 : Blo 860564 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B12616019 : Blo 860564 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B2458279 : Blo 860564 2458279 := bstep (se 1 (by rfl) ⟨1843709, by rfl⟩ : syracuseStep 2458279 = 3687419) B3687419
theorem B2458633 : Blo 860564 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B4654415 : Blo 860564 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B4654655 : Blo 860564 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B7472969 : Blo 860564 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B6064283 : Blo 860564 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B9308351 : Blo 860564 9308351 := bstep (se 1 (by rfl) ⟨6981263, by rfl⟩ : syracuseStep 9308351 = 13962527) B13962527
theorem B4361039 : Blo 860564 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B1936295 : Blo 860564 1936295 := bstep (se 1 (by rfl) ⟨1452221, by rfl⟩ : syracuseStep 1936295 = 2904443) B2904443
theorem B2624567 : Blo 860564 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B1936457 : Blo 860564 1936457 := bstep (se 2 (by rfl) ⟨726171, by rfl⟩ : syracuseStep 1936457 = 1452343) B1452343
theorem B1936475 : Blo 860564 1936475 := bstep (se 1 (by rfl) ⟨1452356, by rfl⟩ : syracuseStep 1936475 = 2904713) B2904713
theorem B4361363 : Blo 860564 4361363 := bstep (se 1 (by rfl) ⟨3271022, by rfl⟩ : syracuseStep 4361363 = 6542045) B6542045
theorem B19926425 : Blo 860564 19926425 := bstep (se 2 (by rfl) ⟨7472409, by rfl⟩ : syracuseStep 19926425 = 14944819) B14944819
theorem B2330203 : Blo 860564 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B3280607 : Blo 860564 3280607 := bstep (se 1 (by rfl) ⟨2460455, by rfl⟩ : syracuseStep 3280607 = 4920911) B4920911
theorem B25169705 : Blo 860564 25169705 := bstep (se 2 (by rfl) ⟨9438639, by rfl⟩ : syracuseStep 25169705 = 18877279) B18877279
theorem B2953255 : Blo 860564 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B6983729 : Blo 860564 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B2068715 : Blo 860564 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B2953595 : Blo 860564 2953595 := bstep (se 1 (by rfl) ⟨2215196, by rfl⟩ : syracuseStep 2953595 = 4430393) B4430393
theorem B1938185 : Blo 860564 1938185 := bstep (se 2 (by rfl) ⟨726819, by rfl⟩ : syracuseStep 1938185 = 1453639) B1453639
theorem B19896131 : Blo 860564 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B1940129 : Blo 860564 1940129 := bstep (se 2 (by rfl) ⟨727548, by rfl⟩ : syracuseStep 1940129 = 1455097) B1455097
theorem B4365251 : Blo 860564 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B1940489 : Blo 860564 1940489 := bstep (se 2 (by rfl) ⟨727683, by rfl⟩ : syracuseStep 1940489 = 1455367) B1455367
theorem B4365575 : Blo 860564 4365575 := bstep (se 1 (by rfl) ⟨3274181, by rfl⟩ : syracuseStep 4365575 = 6548363) B6548363
theorem B1941011 : Blo 860564 1941011 := bstep (se 1 (by rfl) ⟨1455758, by rfl⟩ : syracuseStep 1941011 = 2911517) B2911517
theorem B4923301 : Blo 860564 4923301 := bstep (se 4 (by rfl) ⟨461559, by rfl⟩ : syracuseStep 4923301 = 923119) B923119
theorem B1941479 : Blo 860564 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B1941659 : Blo 860564 1941659 := bstep (se 1 (by rfl) ⟨1456244, by rfl⟩ : syracuseStep 1941659 = 2912489) B2912489
theorem B2990267 : Blo 860564 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B106406297 : Blo 860564 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B860763 : Blo 860564 860763 := bstep (se 1 (by rfl) ⟨645572, by rfl⟩ : syracuseStep 860763 = 1291145) B1291145
theorem B861019 : Blo 860564 861019 := bstep (se 1 (by rfl) ⟨645764, by rfl⟩ : syracuseStep 861019 = 1291529) B1291529
theorem B861055 : Blo 860564 861055 := bstep (se 1 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 861055 = 1291583) B1291583
theorem B2073559 : Blo 860564 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B4203535 : Blo 860564 4203535 := bstep (se 1 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 4203535 = 6305303) B6305303
theorem B2794559 : Blo 860564 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B861339 : Blo 860564 861339 := bstep (se 1 (by rfl) ⟨646004, by rfl⟩ : syracuseStep 861339 = 1292009) B1292009
theorem B861343 : Blo 860564 861343 := bstep (se 1 (by rfl) ⟨646007, by rfl⟩ : syracuseStep 861343 = 1292015) B1292015
theorem B1942739 : Blo 860564 1942739 := bstep (se 1 (by rfl) ⟨1457054, by rfl⟩ : syracuseStep 1942739 = 2914109) B2914109
theorem B861647 : Blo 860564 861647 := bstep (se 1 (by rfl) ⟨646235, by rfl⟩ : syracuseStep 861647 = 1292471) B1292471
theorem B1942991 : Blo 860564 1942991 := bstep (se 1 (by rfl) ⟨1457243, by rfl⟩ : syracuseStep 1942991 = 2914487) B2914487
theorem B1943009 : Blo 860564 1943009 := bstep (se 2 (by rfl) ⟨728628, by rfl⟩ : syracuseStep 1943009 = 1457257) B1457257
theorem B861679 : Blo 860564 861679 := bstep (se 1 (by rfl) ⟨646259, by rfl⟩ : syracuseStep 861679 = 1292519) B1292519
theorem B861927 : Blo 860564 861927 := bstep (se 1 (by rfl) ⟨646445, by rfl⟩ : syracuseStep 861927 = 1292891) B1292891
theorem B862023 : Blo 860564 862023 := bstep (se 1 (by rfl) ⟨646517, by rfl⟩ : syracuseStep 862023 = 1293035) B1293035
theorem B862043 : Blo 860564 862043 := bstep (se 1 (by rfl) ⟨646532, by rfl⟩ : syracuseStep 862043 = 1293065) B1293065
theorem B1943387 : Blo 860564 1943387 := bstep (se 1 (by rfl) ⟨1457540, by rfl⟩ : syracuseStep 1943387 = 2915081) B2915081
theorem B2762849 : Blo 860564 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B4434155 : Blo 860564 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B862623 : Blo 860564 862623 := bstep (se 1 (by rfl) ⟨646967, by rfl⟩ : syracuseStep 862623 = 1293935) B1293935
theorem B862703 : Blo 860564 862703 := bstep (se 1 (by rfl) ⟨647027, by rfl⟩ : syracuseStep 862703 = 1294055) B1294055
theorem B862831 : Blo 860564 862831 := bstep (se 1 (by rfl) ⟨647123, by rfl⟩ : syracuseStep 862831 = 1294247) B1294247
theorem B1944359 : Blo 860564 1944359 := bstep (se 1 (by rfl) ⟨1458269, by rfl⟩ : syracuseStep 1944359 = 2916539) B2916539
theorem B863047 : Blo 860564 863047 := bstep (se 1 (by rfl) ⟨647285, by rfl⟩ : syracuseStep 863047 = 1294571) B1294571
theorem B863087 : Blo 860564 863087 := bstep (se 1 (by rfl) ⟨647315, by rfl⟩ : syracuseStep 863087 = 1294631) B1294631
theorem B2075711 : Blo 860564 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B863535 : Blo 860564 863535 := bstep (se 1 (by rfl) ⟨647651, by rfl⟩ : syracuseStep 863535 = 1295303) B1295303
theorem B1453403 : Blo 860564 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B4369787 : Blo 860564 4369787 := bstep (se 1 (by rfl) ⟨3277340, by rfl⟩ : syracuseStep 4369787 = 6554681) B6554681
theorem B863647 : Blo 860564 863647 := bstep (se 1 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 863647 = 1295471) B1295471
theorem B9809423 : Blo 860564 9809423 := bstep (se 1 (by rfl) ⟨7357067, by rfl⟩ : syracuseStep 9809423 = 14714135) B14714135
theorem B863775 : Blo 860564 863775 := bstep (se 1 (by rfl) ⟨647831, by rfl⟩ : syracuseStep 863775 = 1295663) B1295663
theorem B1453673 : Blo 860564 1453673 := bstep (se 2 (by rfl) ⟨545127, by rfl⟩ : syracuseStep 1453673 = 1090255) B1090255
theorem B863911 : Blo 860564 863911 := bstep (se 1 (by rfl) ⟨647933, by rfl⟩ : syracuseStep 863911 = 1295867) B1295867
theorem B4370111 : Blo 860564 4370111 := bstep (se 1 (by rfl) ⟨3277583, by rfl⟩ : syracuseStep 4370111 = 6555167) B6555167
theorem B863935 : Blo 860564 863935 := bstep (se 1 (by rfl) ⟨647951, by rfl⟩ : syracuseStep 863935 = 1295903) B1295903
theorem B864031 : Blo 860564 864031 := bstep (se 1 (by rfl) ⟨648023, by rfl⟩ : syracuseStep 864031 = 1296047) B1296047
theorem B864111 : Blo 860564 864111 := bstep (se 1 (by rfl) ⟨648083, by rfl⟩ : syracuseStep 864111 = 1296167) B1296167
theorem B5517391 : Blo 860564 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B2076779 : Blo 860564 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B864479 : Blo 860564 864479 := bstep (se 1 (by rfl) ⟨648359, by rfl⟩ : syracuseStep 864479 = 1296719) B1296719
theorem B864511 : Blo 860564 864511 := bstep (se 1 (by rfl) ⟨648383, by rfl⟩ : syracuseStep 864511 = 1296767) B1296767
theorem B7385363 : Blo 860564 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B1093915 : Blo 860564 1093915 := bstep (se 1 (by rfl) ⟨820436, by rfl⟩ : syracuseStep 1093915 = 1640873) B1640873
theorem B864539 : Blo 860564 864539 := bstep (se 1 (by rfl) ⟨648404, by rfl⟩ : syracuseStep 864539 = 1296809) B1296809
theorem B5910893 : Blo 860564 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B2798135 : Blo 860564 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B1290959 : Blo 860564 1290959 := bstep (se 1 (by rfl) ⟨968219, by rfl⟩ : syracuseStep 1290959 = 1936439) B1936439
theorem B4371407 : Blo 860564 4371407 := bstep (se 1 (by rfl) ⟨3278555, by rfl⟩ : syracuseStep 4371407 = 6557111) B6557111
theorem B1291247 : Blo 860564 1291247 := bstep (se 1 (by rfl) ⟨968435, by rfl⟩ : syracuseStep 1291247 = 1936871) B1936871
theorem B1455401 : Blo 860564 1455401 := bstep (se 2 (by rfl) ⟨545775, by rfl⟩ : syracuseStep 1455401 = 1091551) B1091551
theorem B1291631 : Blo 860564 1291631 := bstep (se 1 (by rfl) ⟨968723, by rfl⟩ : syracuseStep 1291631 = 1937447) B1937447
theorem B1291751 : Blo 860564 1291751 := bstep (se 1 (by rfl) ⟨968813, by rfl⟩ : syracuseStep 1291751 = 1937627) B1937627
theorem B1291931 : Blo 860564 1291931 := bstep (se 1 (by rfl) ⟨968948, by rfl⟩ : syracuseStep 1291931 = 1937897) B1937897
theorem B14005993 : Blo 860564 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1292267 : Blo 860564 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B1292351 : Blo 860564 1292351 := bstep (se 1 (by rfl) ⟨969263, by rfl⟩ : syracuseStep 1292351 = 1938527) B1938527
theorem B1456231 : Blo 860564 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B1292681 : Blo 860564 1292681 := bstep (se 2 (by rfl) ⟨484755, by rfl⟩ : syracuseStep 1292681 = 969511) B969511
theorem B1292855 : Blo 860564 1292855 := bstep (se 1 (by rfl) ⟨969641, by rfl⟩ : syracuseStep 1292855 = 1939283) B1939283
theorem B1293179 : Blo 860564 1293179 := bstep (se 1 (by rfl) ⟨969884, by rfl⟩ : syracuseStep 1293179 = 1939769) B1939769
theorem B1293791 : Blo 860564 1293791 := bstep (se 1 (by rfl) ⟨970343, by rfl⟩ : syracuseStep 1293791 = 1940687) B1940687
theorem B1294043 : Blo 860564 1294043 := bstep (se 1 (by rfl) ⟨970532, by rfl⟩ : syracuseStep 1294043 = 1941065) B1941065
theorem B1294313 : Blo 860564 1294313 := bstep (se 2 (by rfl) ⟨485367, by rfl⟩ : syracuseStep 1294313 = 970735) B970735
theorem B1294505 : Blo 860564 1294505 := bstep (se 2 (by rfl) ⟨485439, by rfl⟩ : syracuseStep 1294505 = 970879) B970879
theorem B1228969 : Blo 860564 1228969 := bstep (se 2 (by rfl) ⟨460863, by rfl⟩ : syracuseStep 1228969 = 921727) B921727
theorem B7880923 : Blo 860564 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B2212235 : Blo 860564 2212235 := bstep (se 1 (by rfl) ⟨1659176, by rfl⟩ : syracuseStep 2212235 = 3318353) B3318353
theorem B1294823 : Blo 860564 1294823 := bstep (se 1 (by rfl) ⟨971117, by rfl⟩ : syracuseStep 1294823 = 1942235) B1942235
theorem B5522107 : Blo 860564 5522107 := bstep (se 1 (by rfl) ⟨4141580, by rfl⟩ : syracuseStep 5522107 = 8283161) B8283161
theorem B1295099 : Blo 860564 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B1295543 : Blo 860564 1295543 := bstep (se 1 (by rfl) ⟨971657, by rfl⟩ : syracuseStep 1295543 = 1943315) B1943315
theorem B9815255 : Blo 860564 9815255 := bstep (se 1 (by rfl) ⟨7361441, by rfl⟩ : syracuseStep 9815255 = 14722883) B14722883
theorem B3687727 : Blo 860564 3687727 := bstep (se 1 (by rfl) ⟨2765795, by rfl⟩ : syracuseStep 3687727 = 5531591) B5531591
theorem B1295687 : Blo 860564 1295687 := bstep (se 1 (by rfl) ⟨971765, by rfl⟩ : syracuseStep 1295687 = 1943531) B1943531
theorem B1295783 : Blo 860564 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B1295963 : Blo 860564 1295963 := bstep (se 1 (by rfl) ⟨971972, by rfl⟩ : syracuseStep 1295963 = 1943945) B1943945
theorem B1230427 : Blo 860564 1230427 := bstep (se 1 (by rfl) ⟨922820, by rfl⟩ : syracuseStep 1230427 = 1845641) B1845641
theorem B2803495 : Blo 860564 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1656713 : Blo 860564 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B1296431 : Blo 860564 1296431 := bstep (se 1 (by rfl) ⟨972323, by rfl⟩ : syracuseStep 1296431 = 1944647) B1944647
theorem B2181431 : Blo 860564 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B1296695 : Blo 860564 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B6998521 : Blo 860564 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B67095215 : Blo 860564 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B113560865 : Blo 860564 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B2215279 : Blo 860564 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B3362255 : Blo 860564 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B8867353 : Blo 860564 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B2182697 : Blo 860564 2182697 := bstep (se 2 (by rfl) ⟨818511, by rfl⟩ : syracuseStep 2182697 = 1637023) B1637023
theorem B2182889 : Blo 860564 2182889 := bstep (se 2 (by rfl) ⟨818583, by rfl⟩ : syracuseStep 2182889 = 1637167) B1637167
theorem B11030681 : Blo 860564 11030681 := bstep (se 2 (by rfl) ⟨4136505, by rfl⟩ : syracuseStep 11030681 = 8273011) B8273011
theorem B9949729 : Blo 860564 9949729 := bstep (se 2 (by rfl) ⟨3731148, by rfl⟩ : syracuseStep 9949729 = 7462297) B7462297
theorem B1167977 : Blo 860564 1167977 := bstep (se 2 (by rfl) ⟨437991, by rfl⟩ : syracuseStep 1167977 = 875983) B875983
theorem B2183993 : Blo 860564 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B4903847 : Blo 860564 4903847 := bstep (se 1 (by rfl) ⟨3677885, by rfl⟩ : syracuseStep 4903847 = 7355771) B7355771
theorem B1037279 : Blo 860564 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B971743 : Blo 860564 971743 := bstep (se 1 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 971743 = 1457615) B1457615
theorem B2905631 : Blo 860564 2905631 := bstep (se 1 (by rfl) ⟨2179223, by rfl⟩ : syracuseStep 2905631 = 4358447) B4358447
theorem B972319 : Blo 860564 972319 := bstep (se 1 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 972319 = 1458479) B1458479
theorem B3692735 : Blo 860564 3692735 := bstep (se 1 (by rfl) ⟨2769551, by rfl⟩ : syracuseStep 3692735 = 5539103) B5539103
theorem B2218279 : Blo 860564 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B1661599 : Blo 860564 1661599 := bstep (se 1 (by rfl) ⟨1246199, by rfl⟩ : syracuseStep 1661599 = 2492399) B2492399
theorem B37837493 : Blo 860564 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B21027869 : Blo 860564 21027869 := bstep (se 3 (by rfl) ⟨3942725, by rfl⟩ : syracuseStep 21027869 = 7885451) B7885451
theorem B6544475 : Blo 860564 6544475 := bstep (se 1 (by rfl) ⟨4908356, by rfl⟩ : syracuseStep 6544475 = 9816713) B9816713
theorem B40459483 : Blo 860564 40459483 := bstep (se 1 (by rfl) ⟨30344612, by rfl⟩ : syracuseStep 40459483 = 60689225) B60689225
theorem B3104027 : Blo 860564 3104027 := bstep (se 1 (by rfl) ⟨2328020, by rfl⟩ : syracuseStep 3104027 = 4656041) B4656041
theorem B4906331 : Blo 860564 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B3104225 : Blo 860564 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B3497833 : Blo 860564 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B7004227 : Blo 860564 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B11067587 : Blo 860564 11067587 := bstep (se 1 (by rfl) ⟨8300690, by rfl⟩ : syracuseStep 11067587 = 16601381) B16601381
theorem B4907263 : Blo 860564 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B2187769 : Blo 860564 2187769 := bstep (se 2 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 2187769 = 1640827) B1640827
theorem B2188073 : Blo 860564 2188073 := bstep (se 2 (by rfl) ⟨820527, by rfl⟩ : syracuseStep 2188073 = 1641055) B1641055
theorem B2909087 : Blo 860564 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B2909519 : Blo 860564 2909519 := bstep (se 1 (by rfl) ⟨2182139, by rfl⟩ : syracuseStep 2909519 = 4364279) B4364279
theorem B3106475 : Blo 860564 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B9824003 : Blo 860564 9824003 := bstep (se 1 (by rfl) ⟨7368002, by rfl⟩ : syracuseStep 9824003 = 14736005) B14736005
theorem B6547391 : Blo 860564 6547391 := bstep (se 1 (by rfl) ⟨4910543, by rfl⟩ : syracuseStep 6547391 = 9821087) B9821087
theorem B4909247 : Blo 860564 4909247 := bstep (se 1 (by rfl) ⟨3681935, by rfl⟩ : syracuseStep 4909247 = 7363871) B7363871
theorem B3271175 : Blo 860564 3271175 := bstep (se 1 (by rfl) ⟨2453381, by rfl⟩ : syracuseStep 3271175 = 4906763) B4906763
theorem B7367183 : Blo 860564 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B2452265 : Blo 860564 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B7990595 : Blo 860564 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B33648157 : Blo 860564 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B11038679 : Blo 860564 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B14970865 : Blo 860564 14970865 := bstep (se 2 (by rfl) ⟨5614074, by rfl⟩ : syracuseStep 14970865 = 11228149) B11228149
theorem B2912381 : Blo 860564 2912381 := bstep (se 3 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 2912381 = 1092143) B1092143
theorem B2453723 : Blo 860564 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B12579259 : Blo 860564 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B18641441 : Blo 860564 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B8385113 : Blo 860564 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B3273331 : Blo 860564 3273331 := bstep (se 1 (by rfl) ⟨2454998, by rfl⟩ : syracuseStep 3273331 = 4909997) B4909997
theorem B4912595 : Blo 860564 4912595 := bstep (se 1 (by rfl) ⟨3684446, by rfl⟩ : syracuseStep 4912595 = 7368893) B7368893
theorem B4913095 : Blo 860564 4913095 := bstep (se 1 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 4913095 = 7369643) B7369643
theorem B2455591 : Blo 860564 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B6224339 : Blo 860564 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B8288851 : Blo 860564 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B2456207 : Blo 860564 2456207 := bstep (se 1 (by rfl) ⟨1842155, by rfl⟩ : syracuseStep 2456207 = 3684311) B3684311
theorem B6552251 : Blo 860564 6552251 := bstep (se 1 (by rfl) ⟨4914188, by rfl⟩ : syracuseStep 6552251 = 9828377) B9828377
theorem B9305063 : Blo 860564 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B4193255 : Blo 860564 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B18611507 : Blo 860564 18611507 := bstep (se 1 (by rfl) ⟨13958630, by rfl⟩ : syracuseStep 18611507 = 27917261) B27917261
theorem B2915837 : Blo 860564 2915837 := bstep (se 3 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 2915837 = 1093439) B1093439
theorem B2457209 : Blo 860564 2457209 := bstep (se 2 (by rfl) ⟨921453, by rfl⟩ : syracuseStep 2457209 = 1842907) B1842907
theorem B55967381 : Blo 860564 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B9338969 : Blo 860564 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1638625 : Blo 860564 1638625 := bstep (se 2 (by rfl) ⟨614484, by rfl⟩ : syracuseStep 1638625 = 1228969) B1228969
theorem B1474823 : Blo 860564 1474823 := bstep (se 1 (by rfl) ⟨1106117, by rfl⟩ : syracuseStep 1474823 = 2212235) B2212235
theorem B5538077 : Blo 860564 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B2917025 : Blo 860564 2917025 := bstep (se 2 (by rfl) ⟨1093884, by rfl⟩ : syracuseStep 2917025 = 2187769) B2187769
theorem B3277705 : Blo 860564 3277705 := bstep (se 2 (by rfl) ⟨1229139, by rfl⟩ : syracuseStep 3277705 = 2458279) B2458279
theorem B4981979 : Blo 860564 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B3278177 : Blo 860564 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B5604713 : Blo 860564 5604713 := bstep (se 2 (by rfl) ⟨2101767, by rfl⟩ : syracuseStep 5604713 = 4203535) B4203535
theorem B3114605 : Blo 860564 3114605 := bstep (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) B1167977
theorem B4916969 : Blo 860564 4916969 := bstep (se 2 (by rfl) ⟨1843863, by rfl⟩ : syracuseStep 4916969 = 3687727) B3687727
theorem B44730143 : Blo 860564 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1640569 : Blo 860564 1640569 := bstep (se 2 (by rfl) ⟨615213, by rfl⟩ : syracuseStep 1640569 = 1230427) B1230427
theorem B3737993 : Blo 860564 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B16779803 : Blo 860564 16779803 := bstep (se 1 (by rfl) ⟨12584852, by rfl⟩ : syracuseStep 16779803 = 25169705) B25169705
theorem B4655819 : Blo 860564 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1379143 : Blo 860564 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B1937087 : Blo 860564 1937087 := bstep (se 1 (by rfl) ⟨1452815, by rfl⟩ : syracuseStep 1937087 = 2905631) B2905631
theorem B2461823 : Blo 860564 2461823 := bstep (se 1 (by rfl) ⟨1846367, by rfl⟩ : syracuseStep 2461823 = 3692735) B3692735
theorem B44864209 : Blo 860564 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B4362983 : Blo 860564 4362983 := bstep (se 1 (by rfl) ⟨3272237, by rfl⟩ : syracuseStep 4362983 = 6544475) B6544475
theorem B2069351 : Blo 860564 2069351 := bstep (se 1 (by rfl) ⟨1552013, by rfl⟩ : syracuseStep 2069351 = 3104027) B3104027
theorem B2069483 : Blo 860564 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B19961153 : Blo 860564 19961153 := bstep (se 2 (by rfl) ⟨7485432, by rfl⟩ : syracuseStep 19961153 = 14970865) B14970865
theorem B3937673 : Blo 860564 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B7378391 : Blo 860564 7378391 := bstep (se 1 (by rfl) ⟨5533793, by rfl⟩ : syracuseStep 7378391 = 11067587) B11067587
theorem B1939391 : Blo 860564 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B4364441 : Blo 860564 4364441 := bstep (se 2 (by rfl) ⟨1636665, by rfl⟩ : syracuseStep 4364441 = 3273331) B3273331
theorem B1939679 : Blo 860564 1939679 := bstep (se 1 (by rfl) ⟨1454759, by rfl⟩ : syracuseStep 1939679 = 2909519) B2909519
theorem B2070983 : Blo 860564 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B215783909 : Blo 860564 215783909 := bstep (se 4 (by rfl) ⟨20229741, by rfl⟩ : syracuseStep 215783909 = 40459483) B40459483
theorem B4364927 : Blo 860564 4364927 := bstep (se 1 (by rfl) ⟨3273695, by rfl⟩ : syracuseStep 4364927 = 6547391) B6547391
theorem B1841899 : Blo 860564 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B2956103 : Blo 860564 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B11182013 : Blo 860564 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B1941587 : Blo 860564 1941587 := bstep (se 1 (by rfl) ⟨1456190, by rfl⟩ : syracuseStep 1941587 = 2912381) B2912381
theorem B1941641 : Blo 860564 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B4923575 : Blo 860564 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B3940595 : Blo 860564 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B12427627 : Blo 860564 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B2957705 : Blo 860564 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B860639 : Blo 860564 860639 := bstep (se 1 (by rfl) ⟨645479, by rfl⟩ : syracuseStep 860639 = 1290959) B1290959
theorem B860831 : Blo 860564 860831 := bstep (se 1 (by rfl) ⟨645623, by rfl⟩ : syracuseStep 860831 = 1291247) B1291247
theorem B11051801 : Blo 860564 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B861087 : Blo 860564 861087 := bstep (se 1 (by rfl) ⟨645815, by rfl⟩ : syracuseStep 861087 = 1291631) B1291631
theorem B861167 : Blo 860564 861167 := bstep (se 1 (by rfl) ⟨645875, by rfl⟩ : syracuseStep 861167 = 1291751) B1291751
theorem B861287 : Blo 860564 861287 := bstep (se 1 (by rfl) ⟨645965, by rfl⟩ : syracuseStep 861287 = 1291931) B1291931
theorem B861511 : Blo 860564 861511 := bstep (se 1 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 861511 = 1292267) B1292267
theorem B861567 : Blo 860564 861567 := bstep (se 1 (by rfl) ⟨646175, by rfl⟩ : syracuseStep 861567 = 1292351) B1292351
theorem B861787 : Blo 860564 861787 := bstep (se 1 (by rfl) ⟨646340, by rfl⟩ : syracuseStep 861787 = 1292681) B1292681
theorem B861903 : Blo 860564 861903 := bstep (se 1 (by rfl) ⟨646427, by rfl⟩ : syracuseStep 861903 = 1292855) B1292855
theorem B4368167 : Blo 860564 4368167 := bstep (se 1 (by rfl) ⟨3276125, by rfl⟩ : syracuseStep 4368167 = 6552251) B6552251
theorem B18655109 : Blo 860564 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B862119 : Blo 860564 862119 := bstep (se 1 (by rfl) ⟨646589, by rfl⟩ : syracuseStep 862119 = 1293179) B1293179
theorem B6203375 : Blo 860564 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B862527 : Blo 860564 862527 := bstep (se 1 (by rfl) ⟨646895, by rfl⟩ : syracuseStep 862527 = 1293791) B1293791
theorem B1943891 : Blo 860564 1943891 := bstep (se 1 (by rfl) ⟨1457918, by rfl⟩ : syracuseStep 1943891 = 2915837) B2915837
theorem B862695 : Blo 860564 862695 := bstep (se 1 (by rfl) ⟨647021, by rfl⟩ : syracuseStep 862695 = 1294043) B1294043
theorem B6564401 : Blo 860564 6564401 := bstep (se 2 (by rfl) ⟨2461650, by rfl⟩ : syracuseStep 6564401 = 4923301) B4923301
theorem B862875 : Blo 860564 862875 := bstep (se 1 (by rfl) ⟨647156, by rfl⟩ : syracuseStep 862875 = 1294313) B1294313
theorem B863003 : Blo 860564 863003 := bstep (se 1 (by rfl) ⟨647252, by rfl⟩ : syracuseStep 863003 = 1294505) B1294505
theorem B863215 : Blo 860564 863215 := bstep (se 1 (by rfl) ⟨647411, by rfl⟩ : syracuseStep 863215 = 1294823) B1294823
theorem B863399 : Blo 860564 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B863695 : Blo 860564 863695 := bstep (se 1 (by rfl) ⟨647771, by rfl⟩ : syracuseStep 863695 = 1295543) B1295543
theorem B863791 : Blo 860564 863791 := bstep (se 1 (by rfl) ⟨647843, by rfl⟩ : syracuseStep 863791 = 1295687) B1295687
theorem B863855 : Blo 860564 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B7876253 : Blo 860564 7876253 := bstep (se 3 (by rfl) ⟨1476797, by rfl⟩ : syracuseStep 7876253 = 2953595) B2953595
theorem B863975 : Blo 860564 863975 := bstep (se 1 (by rfl) ⟨647981, by rfl⟩ : syracuseStep 863975 = 1295963) B1295963
theorem B2764745 : Blo 860564 2764745 := bstep (se 2 (by rfl) ⟨1036779, by rfl⟩ : syracuseStep 2764745 = 2073559) B2073559
theorem B864287 : Blo 860564 864287 := bstep (se 1 (by rfl) ⟨648215, by rfl⟩ : syracuseStep 864287 = 1296431) B1296431
theorem B4042855 : Blo 860564 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B6205567 : Blo 860564 6205567 := bstep (se 1 (by rfl) ⟨4654175, by rfl⟩ : syracuseStep 6205567 = 9308351) B9308351
theorem B1454287 : Blo 860564 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B864463 : Blo 860564 864463 := bstep (se 1 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 864463 = 1296695) B1296695
theorem B1290863 : Blo 860564 1290863 := bstep (se 1 (by rfl) ⟨968147, by rfl⟩ : syracuseStep 1290863 = 1936295) B1936295
theorem B1290971 : Blo 860564 1290971 := bstep (se 1 (by rfl) ⟨968228, by rfl⟩ : syracuseStep 1290971 = 1936457) B1936457
theorem B1290983 : Blo 860564 1290983 := bstep (se 1 (by rfl) ⟨968237, by rfl⟩ : syracuseStep 1290983 = 1936475) B1936475
theorem B75707243 : Blo 860564 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B13284283 : Blo 860564 13284283 := bstep (se 1 (by rfl) ⟨9963212, by rfl⟩ : syracuseStep 13284283 = 19926425) B19926425
theorem B2241503 : Blo 860564 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B1455131 : Blo 860564 1455131 := bstep (se 1 (by rfl) ⟨1091348, by rfl⟩ : syracuseStep 1455131 = 2182697) B2182697
theorem B1455259 : Blo 860564 1455259 := bstep (se 1 (by rfl) ⟨1091444, by rfl⟩ : syracuseStep 1455259 = 2182889) B2182889
theorem B2766077 : Blo 860564 2766077 := bstep (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) B1037279
theorem B7353787 : Blo 860564 7353787 := bstep (se 1 (by rfl) ⟨5515340, by rfl⟩ : syracuseStep 7353787 = 11030681) B11030681
theorem B7452157 : Blo 860564 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B1292123 : Blo 860564 1292123 := bstep (se 1 (by rfl) ⟨969092, by rfl⟩ : syracuseStep 1292123 = 1938185) B1938185
theorem B1455995 : Blo 860564 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B8861861 : Blo 860564 8861861 := bstep (se 4 (by rfl) ⟨830799, by rfl⟩ : syracuseStep 8861861 = 1661599) B1661599
theorem B1293419 : Blo 860564 1293419 := bstep (se 1 (by rfl) ⟨970064, by rfl⟩ : syracuseStep 1293419 = 1940129) B1940129
theorem B1293659 : Blo 860564 1293659 := bstep (se 1 (by rfl) ⟨970244, by rfl⟩ : syracuseStep 1293659 = 1940489) B1940489
theorem B1294007 : Blo 860564 1294007 := bstep (se 1 (by rfl) ⟨970505, by rfl⟩ : syracuseStep 1294007 = 1941011) B1941011
theorem B1294319 : Blo 860564 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B1294439 : Blo 860564 1294439 := bstep (se 1 (by rfl) ⟨970829, by rfl⟩ : syracuseStep 1294439 = 1941659) B1941659
theorem B7356521 : Blo 860564 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B1458553 : Blo 860564 1458553 := bstep (se 2 (by rfl) ⟨546957, by rfl⟩ : syracuseStep 1458553 = 1093915) B1093915
theorem B1458715 : Blo 860564 1458715 := bstep (se 1 (by rfl) ⟨1094036, by rfl⟩ : syracuseStep 1458715 = 2188073) B2188073
theorem B1295159 : Blo 860564 1295159 := bstep (se 1 (by rfl) ⟨971369, by rfl⟩ : syracuseStep 1295159 = 1942739) B1942739
theorem B1295327 : Blo 860564 1295327 := bstep (se 1 (by rfl) ⟨971495, by rfl⟩ : syracuseStep 1295327 = 1942991) B1942991
theorem B1295339 : Blo 860564 1295339 := bstep (se 1 (by rfl) ⟨971504, by rfl⟩ : syracuseStep 1295339 = 1943009) B1943009
theorem B1295591 : Blo 860564 1295591 := bstep (se 1 (by rfl) ⟨971693, by rfl⟩ : syracuseStep 1295591 = 1943387) B1943387
theorem B1295657 : Blo 860564 1295657 := bstep (se 2 (by rfl) ⟨485871, by rfl⟩ : syracuseStep 1295657 = 971743) B971743
theorem B2180783 : Blo 860564 2180783 := bstep (se 1 (by rfl) ⟨1635587, by rfl⟩ : syracuseStep 2180783 = 3271175) B3271175
theorem B1296239 : Blo 860564 1296239 := bstep (se 1 (by rfl) ⟨972179, by rfl⟩ : syracuseStep 1296239 = 1944359) B1944359
theorem B11814821 : Blo 860564 11814821 := bstep (se 4 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 11814821 = 2215279) B2215279
theorem B1296425 : Blo 860564 1296425 := bstep (se 2 (by rfl) ⟨486159, by rfl⟩ : syracuseStep 1296425 = 972319) B972319
theorem B5327063 : Blo 860564 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B968935 : Blo 860564 968935 := bstep (se 1 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 968935 = 1453403) B1453403
theorem B6539615 : Blo 860564 6539615 := bstep (se 1 (by rfl) ⟨4904711, by rfl⟩ : syracuseStep 6539615 = 9809423) B9809423
theorem B969115 : Blo 860564 969115 := bstep (se 1 (by rfl) ⟨726836, by rfl⟩ : syracuseStep 969115 = 1453673) B1453673
theorem B7359119 : Blo 860564 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B6998845 : Blo 860564 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B5590075 : Blo 860564 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B970267 : Blo 860564 970267 := bstep (se 1 (by rfl) ⟨727700, by rfl⟩ : syracuseStep 970267 = 1455401) B1455401
theorem B4149559 : Blo 860564 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B12407671 : Blo 860564 12407671 := bstep (se 1 (by rfl) ⟨9305753, by rfl⟩ : syracuseStep 12407671 = 18611507) B18611507
theorem B37311587 : Blo 860564 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B8410679 : Blo 860564 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B10507897 : Blo 860564 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B6543017 : Blo 860564 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B6543503 : Blo 860564 6543503 := bstep (se 1 (by rfl) ⟨4907627, by rfl⟩ : syracuseStep 6543503 = 9815255) B9815255
theorem B3102943 : Blo 860564 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B7362809 : Blo 860564 7362809 := bstep (se 2 (by rfl) ⟨2761053, by rfl⟩ : syracuseStep 7362809 = 5522107) B5522107
theorem B3103103 : Blo 860564 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B2907359 : Blo 860564 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B2907575 : Blo 860564 2907575 := bstep (se 1 (by rfl) ⟨2180681, by rfl⟩ : syracuseStep 2907575 = 4361363) B4361363
theorem B2187071 : Blo 860564 2187071 := bstep (se 1 (by rfl) ⟨1640303, by rfl⟩ : syracuseStep 2187071 = 3280607) B3280607
theorem B3269231 : Blo 860564 3269231 := bstep (se 1 (by rfl) ⟨2451923, by rfl⟩ : syracuseStep 3269231 = 4903847) B4903847
theorem B9331361 : Blo 860564 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B13264087 : Blo 860564 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B25224995 : Blo 860564 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B2910167 : Blo 860564 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B14018579 : Blo 860564 14018579 := bstep (se 1 (by rfl) ⟨10513934, by rfl⟩ : syracuseStep 14018579 = 21027869) B21027869
theorem B11823137 : Blo 860564 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B3106937 : Blo 860564 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B2910383 : Blo 860564 2910383 := bstep (se 1 (by rfl) ⟨2182787, by rfl⟩ : syracuseStep 2910383 = 4365575) B4365575
theorem B3270887 : Blo 860564 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B4417901 : Blo 860564 4417901 := bstep (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) B1656713
theorem B1993511 : Blo 860564 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B70937531 : Blo 860564 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B16772345 : Blo 860564 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B13266305 : Blo 860564 13266305 := bstep (se 2 (by rfl) ⟨4974864, by rfl⟩ : syracuseStep 13266305 = 9949729) B9949729
theorem B6549335 : Blo 860564 6549335 := bstep (se 1 (by rfl) ⟨4912001, by rfl⟩ : syracuseStep 6549335 = 9824003) B9824003
theorem B3272831 : Blo 860564 3272831 := bstep (se 1 (by rfl) ⟨2454623, by rfl⟩ : syracuseStep 3272831 = 4909247) B4909247
theorem B4911455 : Blo 860564 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B1634843 : Blo 860564 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B2913191 : Blo 860564 2913191 := bstep (se 1 (by rfl) ⟨2184893, by rfl⟩ : syracuseStep 2913191 = 4369787) B4369787
theorem B18674657 : Blo 860564 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B2913407 : Blo 860564 2913407 := bstep (se 1 (by rfl) ⟨2185055, by rfl⟩ : syracuseStep 2913407 = 4370111) B4370111
theorem B6550793 : Blo 860564 6550793 := bstep (se 2 (by rfl) ⟨2456547, by rfl⟩ : syracuseStep 6550793 = 4913095) B4913095
theorem B3274121 : Blo 860564 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B1635815 : Blo 860564 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B5535229 : Blo 860564 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B1865423 : Blo 860564 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B2914271 : Blo 860564 2914271 := bstep (se 1 (by rfl) ⟨2185703, by rfl⟩ : syracuseStep 2914271 = 4371407) B4371407
theorem B3275063 : Blo 860564 3275063 := bstep (se 1 (by rfl) ⟨2456297, by rfl⟩ : syracuseStep 3275063 = 4912595) B4912595
theorem B1637471 : Blo 860564 1637471 := bstep (se 1 (by rfl) ⟨1228103, by rfl⟩ : syracuseStep 1637471 = 2456207) B2456207
theorem B1638139 : Blo 860564 1638139 := bstep (se 1 (by rfl) ⟨1228604, by rfl⟩ : syracuseStep 1638139 = 2457209) B2457209
theorem B6225979 : Blo 860564 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B983215 : Blo 860564 983215 := bstep (se 1 (by rfl) ⟨737411, by rfl⟩ : syracuseStep 983215 = 1474823) B1474823
theorem B3736475 : Blo 860564 3736475 := bstep (se 1 (by rfl) ⟨2802356, by rfl⟩ : syracuseStep 3736475 = 5604713) B5604713
theorem B3277979 : Blo 860564 3277979 := bstep (se 1 (by rfl) ⟨2458484, by rfl⟩ : syracuseStep 3277979 = 4916969) B4916969
theorem B29820095 : Blo 860564 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B4359581 : Blo 860564 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B4359743 : Blo 860564 4359743 := bstep (se 1 (by rfl) ⟨3269807, by rfl⟩ : syracuseStep 4359743 = 6539615) B6539615
theorem B1641215 : Blo 860564 1641215 := bstep (se 1 (by rfl) ⟨1230911, by rfl⟩ : syracuseStep 1641215 = 2461823) B2461823
theorem B1379567 : Blo 860564 1379567 := bstep (se 1 (by rfl) ⟨1034675, by rfl⟩ : syracuseStep 1379567 = 2069351) B2069351
theorem B24874391 : Blo 860564 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B13307435 : Blo 860564 13307435 := bstep (se 1 (by rfl) ⟨9980576, by rfl⟩ : syracuseStep 13307435 = 19961153) B19961153
theorem B4918927 : Blo 860564 4918927 := bstep (se 1 (by rfl) ⟨3689195, by rfl⟩ : syracuseStep 4918927 = 7378391) B7378391
theorem B5607119 : Blo 860564 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1838857 : Blo 860564 1838857 := bstep (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) B1379143
theorem B4362011 : Blo 860564 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B4362173 : Blo 860564 4362173 := bstep (se 3 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 4362173 = 1635815) B1635815
theorem B4362335 : Blo 860564 4362335 := bstep (se 1 (by rfl) ⟨3271751, by rfl⟩ : syracuseStep 4362335 = 6543503) B6543503
theorem B2068735 : Blo 860564 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B1380655 : Blo 860564 1380655 := bstep (se 1 (by rfl) ⟨1035491, by rfl⟩ : syracuseStep 1380655 = 2070983) B2070983
theorem B143855939 : Blo 860564 143855939 := bstep (se 1 (by rfl) ⟨107891954, by rfl⟩ : syracuseStep 143855939 = 215783909) B215783909
theorem B1970735 : Blo 860564 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B1938239 : Blo 860564 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B1938383 : Blo 860564 1938383 := bstep (se 1 (by rfl) ⟨1453787, by rfl⟩ : syracuseStep 1938383 = 2907575) B2907575
theorem B3282383 : Blo 860564 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B2627063 : Blo 860564 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B1971803 : Blo 860564 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B1939049 : Blo 860564 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B9967981 : Blo 860564 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B16816663 : Blo 860564 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1940111 : Blo 860564 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B4135583 : Blo 860564 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B9345719 : Blo 860564 9345719 := bstep (se 1 (by rfl) ⟨7009289, by rfl⟩ : syracuseStep 9345719 = 14018579) B14018579
theorem B2071291 : Blo 860564 2071291 := bstep (se 1 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 2071291 = 3106937) B3106937
theorem B1940255 : Blo 860564 1940255 := bstep (se 1 (by rfl) ⟨1455191, by rfl⟩ : syracuseStep 1940255 = 2910383) B2910383
theorem B1940345 : Blo 860564 1940345 := bstep (se 2 (by rfl) ⟨727629, by rfl⟩ : syracuseStep 1940345 = 1455259) B1455259
theorem B9805049 : Blo 860564 9805049 := bstep (se 2 (by rfl) ⟨3676893, by rfl⟩ : syracuseStep 9805049 = 7353787) B7353787
theorem B47291687 : Blo 860564 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B9936209 : Blo 860564 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B7380305 : Blo 860564 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B5316029 : Blo 860564 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B11181563 : Blo 860564 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B5250835 : Blo 860564 5250835 := bstep (se 1 (by rfl) ⟨3938126, by rfl⟩ : syracuseStep 5250835 = 7876253) B7876253
theorem B4366223 : Blo 860564 4366223 := bstep (se 1 (by rfl) ⟨3274667, by rfl⟩ : syracuseStep 4366223 = 6549335) B6549335
theorem B1843163 : Blo 860564 1843163 := bstep (se 1 (by rfl) ⟨1382372, by rfl⟩ : syracuseStep 1843163 = 2764745) B2764745
theorem B4137257 : Blo 860564 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B860575 : Blo 860564 860575 := bstep (se 1 (by rfl) ⟨645431, by rfl⟩ : syracuseStep 860575 = 1290863) B1290863
theorem B860647 : Blo 860564 860647 := bstep (se 1 (by rfl) ⟨645485, by rfl⟩ : syracuseStep 860647 = 1290971) B1290971
theorem B860655 : Blo 860564 860655 := bstep (se 1 (by rfl) ⟨645491, by rfl⟩ : syracuseStep 860655 = 1290983) B1290983
theorem B50471495 : Blo 860564 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B1942127 : Blo 860564 1942127 := bstep (se 1 (by rfl) ⟨1456595, by rfl⟩ : syracuseStep 1942127 = 2913191) B2913191
theorem B56042117 : Blo 860564 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B1942271 : Blo 860564 1942271 := bstep (se 1 (by rfl) ⟨1456703, by rfl⟩ : syracuseStep 1942271 = 2913407) B2913407
theorem B1844051 : Blo 860564 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B4367195 : Blo 860564 4367195 := bstep (se 1 (by rfl) ⟨3275396, by rfl⟩ : syracuseStep 4367195 = 6550793) B6550793
theorem B861415 : Blo 860564 861415 := bstep (se 1 (by rfl) ⟨646061, by rfl⟩ : syracuseStep 861415 = 1292123) B1292123
theorem B1942847 : Blo 860564 1942847 := bstep (se 1 (by rfl) ⟨1457135, by rfl⟩ : syracuseStep 1942847 = 2914271) B2914271
theorem B5907907 : Blo 860564 5907907 := bstep (se 1 (by rfl) ⟨4430930, by rfl⟩ : syracuseStep 5907907 = 8861861) B8861861
theorem B1091647 : Blo 860564 1091647 := bstep (se 1 (by rfl) ⟨818735, by rfl⟩ : syracuseStep 1091647 = 1637471) B1637471
theorem B862279 : Blo 860564 862279 := bstep (se 1 (by rfl) ⟨646709, by rfl⟩ : syracuseStep 862279 = 1293419) B1293419
theorem B862439 : Blo 860564 862439 := bstep (se 1 (by rfl) ⟨646829, by rfl⟩ : syracuseStep 862439 = 1293659) B1293659
theorem B862671 : Blo 860564 862671 := bstep (se 1 (by rfl) ⟨647003, by rfl⟩ : syracuseStep 862671 = 1294007) B1294007
theorem B862879 : Blo 860564 862879 := bstep (se 1 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 862879 = 1294319) B1294319
theorem B862959 : Blo 860564 862959 := bstep (se 1 (by rfl) ⟨647219, by rfl⟩ : syracuseStep 862959 = 1294439) B1294439
theorem B1944683 : Blo 860564 1944683 := bstep (se 1 (by rfl) ⟨1458512, by rfl⟩ : syracuseStep 1944683 = 2917025) B2917025
theorem B1944737 : Blo 860564 1944737 := bstep (se 2 (by rfl) ⟨729276, by rfl⟩ : syracuseStep 1944737 = 1458553) B1458553
theorem B863439 : Blo 860564 863439 := bstep (se 1 (by rfl) ⟨647579, by rfl⟩ : syracuseStep 863439 = 1295159) B1295159
theorem B863551 : Blo 860564 863551 := bstep (se 1 (by rfl) ⟨647663, by rfl⟩ : syracuseStep 863551 = 1295327) B1295327
theorem B863559 : Blo 860564 863559 := bstep (se 1 (by rfl) ⟨647669, by rfl⟩ : syracuseStep 863559 = 1295339) B1295339
theorem B1944953 : Blo 860564 1944953 := bstep (se 2 (by rfl) ⟨729357, by rfl⟩ : syracuseStep 1944953 = 1458715) B1458715
theorem B3321319 : Blo 860564 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B863727 : Blo 860564 863727 := bstep (se 1 (by rfl) ⟨647795, by rfl⟩ : syracuseStep 863727 = 1295591) B1295591
theorem B863771 : Blo 860564 863771 := bstep (se 1 (by rfl) ⟨647828, by rfl⟩ : syracuseStep 863771 = 1295657) B1295657
theorem B2076403 : Blo 860564 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B1453855 : Blo 860564 1453855 := bstep (se 1 (by rfl) ⟨1090391, by rfl⟩ : syracuseStep 1453855 = 2180783) B2180783
theorem B4370273 : Blo 860564 4370273 := bstep (se 2 (by rfl) ⟨1638852, by rfl⟩ : syracuseStep 4370273 = 3277705) B3277705
theorem B864159 : Blo 860564 864159 := bstep (se 1 (by rfl) ⟨648119, by rfl⟩ : syracuseStep 864159 = 1296239) B1296239
theorem B7876547 : Blo 860564 7876547 := bstep (se 1 (by rfl) ⟨5907410, by rfl⟩ : syracuseStep 7876547 = 11814821) B11814821
theorem B864283 : Blo 860564 864283 := bstep (se 1 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 864283 = 1296425) B1296425
theorem B3551375 : Blo 860564 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B1291391 : Blo 860564 1291391 := bstep (se 1 (by rfl) ⟨968543, by rfl⟩ : syracuseStep 1291391 = 1937087) B1937087
theorem B5518621 : Blo 860564 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B1291913 : Blo 860564 1291913 := bstep (se 2 (by rfl) ⟨484467, by rfl⟩ : syracuseStep 1291913 = 968935) B968935
theorem B1292153 : Blo 860564 1292153 := bstep (se 2 (by rfl) ⟨484557, by rfl⟩ : syracuseStep 1292153 = 969115) B969115
theorem B10500461 : Blo 860564 10500461 := bstep (se 3 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 10500461 = 3937673) B3937673
theorem B1292927 : Blo 860564 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B7453433 : Blo 860564 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B1293119 : Blo 860564 1293119 := bstep (se 1 (by rfl) ⟨969839, by rfl⟩ : syracuseStep 1293119 = 1939679) B1939679
theorem B1293689 : Blo 860564 1293689 := bstep (se 2 (by rfl) ⟨485133, by rfl⟩ : syracuseStep 1293689 = 970267) B970267
theorem B1458047 : Blo 860564 1458047 := bstep (se 1 (by rfl) ⟨1093535, by rfl⟩ : syracuseStep 1458047 = 2187071) B2187071
theorem B7454675 : Blo 860564 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B1294391 : Blo 860564 1294391 := bstep (se 1 (by rfl) ⟨970793, by rfl⟩ : syracuseStep 1294391 = 1941587) B1941587
theorem B1294427 : Blo 860564 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B5390473 : Blo 860564 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B8274089 : Blo 860564 8274089 := bstep (se 2 (by rfl) ⟨3102783, by rfl⟩ : syracuseStep 8274089 = 6205567) B6205567
theorem B2179487 : Blo 860564 2179487 := bstep (se 1 (by rfl) ⟨1634615, by rfl⟩ : syracuseStep 2179487 = 3269231) B3269231
theorem B59818945 : Blo 860564 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B17712377 : Blo 860564 17712377 := bstep (se 2 (by rfl) ⟨6642141, by rfl⟩ : syracuseStep 17712377 = 13284283) B13284283
theorem B12436739 : Blo 860564 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B7882091 : Blo 860564 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B44746141 : Blo 860564 44746141 := bstep (se 3 (by rfl) ⟨8389901, by rfl⟩ : syracuseStep 44746141 = 16779803) B16779803
theorem B2180591 : Blo 860564 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B1295927 : Blo 860564 1295927 := bstep (se 1 (by rfl) ⟨971945, by rfl⟩ : syracuseStep 1295927 = 1943891) B1943891
theorem B4376267 : Blo 860564 4376267 := bstep (se 1 (by rfl) ⟨3282200, by rfl⟩ : syracuseStep 4376267 = 6564401) B6564401
theorem B2181887 : Blo 860564 2181887 := bstep (se 1 (by rfl) ⟨1636415, by rfl⟩ : syracuseStep 2181887 = 3272831) B3272831
theorem B1494335 : Blo 860564 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B970087 : Blo 860564 970087 := bstep (se 1 (by rfl) ⟨727565, by rfl⟩ : syracuseStep 970087 = 1455131) B1455131
theorem B2182747 : Blo 860564 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B970663 : Blo 860564 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B2183375 : Blo 860564 2183375 := bstep (se 1 (by rfl) ⟨1637531, by rfl⟩ : syracuseStep 2183375 = 3275063) B3275063
theorem B2184185 : Blo 860564 2184185 := bstep (se 2 (by rfl) ⟨819069, by rfl⟩ : syracuseStep 2184185 = 1638139) B1638139
theorem B4904347 : Blo 860564 4904347 := bstep (se 1 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 4904347 = 7356521) B7356521
theorem B3692051 : Blo 860564 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B2184833 : Blo 860564 2184833 := bstep (se 2 (by rfl) ⟨819312, by rfl⟩ : syracuseStep 2184833 = 1638625) B1638625
theorem B16570169 : Blo 860564 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B2185451 : Blo 860564 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B17685449 : Blo 860564 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B4906079 : Blo 860564 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B2187425 : Blo 860564 2187425 := bstep (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) B1640569
theorem B2908655 : Blo 860564 2908655 := bstep (se 1 (by rfl) ⟨2181491, by rfl⟩ : syracuseStep 2908655 = 4362983) B4362983
theorem B9331793 : Blo 860564 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B2909627 : Blo 860564 2909627 := bstep (se 1 (by rfl) ⟨2182220, by rfl⟩ : syracuseStep 2909627 = 4364441) B4364441
theorem B4908539 : Blo 860564 4908539 := bstep (se 1 (by rfl) ⟨3681404, by rfl⟩ : syracuseStep 4908539 = 7362809) B7362809
theorem B2909951 : Blo 860564 2909951 := bstep (se 1 (by rfl) ⟨2182463, by rfl⟩ : syracuseStep 2909951 = 4364927) B4364927
theorem B5532745 : Blo 860564 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B6220907 : Blo 860564 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B7367867 : Blo 860564 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B16543561 : Blo 860564 16543561 := bstep (se 2 (by rfl) ⟨6203835, by rfl⟩ : syracuseStep 16543561 = 12407671) B12407671
theorem B2912111 : Blo 860564 2912111 := bstep (se 1 (by rfl) ⟨2184083, by rfl⟩ : syracuseStep 2912111 = 4368167) B4368167
theorem B2945267 : Blo 860564 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B12415517 : Blo 860564 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B8844203 : Blo 860564 8844203 := bstep (se 1 (by rfl) ⟨6633152, by rfl⟩ : syracuseStep 8844203 = 13266305) B13266305
theorem B3274303 : Blo 860564 3274303 := bstep (se 1 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 3274303 = 4911455) B4911455
theorem B12449771 : Blo 860564 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B2455865 : Blo 860564 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B1243615 : Blo 860564 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B1310953 : Blo 860564 1310953 := bstep (se 2 (by rfl) ⟨491607, by rfl⟩ : syracuseStep 1310953 = 983215) B983215
theorem B9470333 : Blo 860564 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B2490983 : Blo 860564 2490983 := bstep (se 1 (by rfl) ⟨1868237, by rfl⟩ : syracuseStep 2490983 = 3736475) B3736475
theorem B8291159 : Blo 860564 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B2917511 : Blo 860564 2917511 := bstep (se 1 (by rfl) ⟨2188133, by rfl⟩ : syracuseStep 2917511 = 4376267) B4376267
theorem B79758593 : Blo 860564 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B919711 : Blo 860564 919711 := bstep (se 1 (by rfl) ⟨689783, by rfl⟩ : syracuseStep 919711 = 1379567) B1379567
theorem B4917469 : Blo 860564 4917469 := bstep (se 3 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 4917469 = 1844051) B1844051
theorem B16582927 : Blo 860564 16582927 := bstep (se 1 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 16582927 = 24874391) B24874391
theorem B3738079 : Blo 860564 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B89688869 : Blo 860564 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B2461367 : Blo 860564 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B11046779 : Blo 860564 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B7376993 : Blo 860564 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B6230479 : Blo 860564 6230479 := bstep (se 1 (by rfl) ⟨4672859, by rfl⟩ : syracuseStep 6230479 = 9345719) B9345719
theorem B4428425 : Blo 860564 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B6558569 : Blo 860564 6558569 := bstep (se 2 (by rfl) ⟨2459463, by rfl⟩ : syracuseStep 6558569 = 4918927) B4918927
theorem B31527791 : Blo 860564 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B6624139 : Blo 860564 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B4920203 : Blo 860564 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B3544019 : Blo 860564 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B1938473 : Blo 860564 1938473 := bstep (se 2 (by rfl) ⟨726927, by rfl⟩ : syracuseStep 1938473 = 1453855) B1453855
theorem B22058081 : Blo 860564 22058081 := bstep (se 2 (by rfl) ⟨8271780, by rfl⟩ : syracuseStep 22058081 = 16543561) B16543561
theorem B1939103 : Blo 860564 1939103 := bstep (se 1 (by rfl) ⟨1454327, by rfl⟩ : syracuseStep 1939103 = 2908655) B2908655
theorem B2758313 : Blo 860564 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B37361411 : Blo 860564 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B1939751 : Blo 860564 1939751 := bstep (se 1 (by rfl) ⟨1454813, by rfl⟩ : syracuseStep 1939751 = 2909627) B2909627
theorem B1939967 : Blo 860564 1939967 := bstep (se 1 (by rfl) ⟨1454975, by rfl⟩ : syracuseStep 1939967 = 2909951) B2909951
theorem B4365737 : Blo 860564 4365737 := bstep (se 2 (by rfl) ⟨1637151, by rfl⟩ : syracuseStep 4365737 = 3274303) B3274303
theorem B1941407 : Blo 860564 1941407 := bstep (se 1 (by rfl) ⟨1456055, by rfl⟩ : syracuseStep 1941407 = 2912111) B2912111
theorem B5251031 : Blo 860564 5251031 := bstep (se 1 (by rfl) ⟨3938273, by rfl⟩ : syracuseStep 5251031 = 7876547) B7876547
theorem B860927 : Blo 860564 860927 := bstep (se 1 (by rfl) ⟨645695, by rfl⟩ : syracuseStep 860927 = 1291391) B1291391
theorem B2761721 : Blo 860564 2761721 := bstep (se 2 (by rfl) ⟨1035645, by rfl⟩ : syracuseStep 2761721 = 2071291) B2071291
theorem B861275 : Blo 860564 861275 := bstep (se 1 (by rfl) ⟨645956, by rfl⟩ : syracuseStep 861275 = 1291913) B1291913
theorem B861435 : Blo 860564 861435 := bstep (se 1 (by rfl) ⟨646076, by rfl⟩ : syracuseStep 861435 = 1292153) B1292153
theorem B8299847 : Blo 860564 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B861951 : Blo 860564 861951 := bstep (se 1 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 861951 = 1292927) B1292927
theorem B862079 : Blo 860564 862079 := bstep (se 1 (by rfl) ⟨646559, by rfl⟩ : syracuseStep 862079 = 1293119) B1293119
theorem B862459 : Blo 860564 862459 := bstep (se 1 (by rfl) ⟨646844, by rfl⟩ : syracuseStep 862459 = 1293689) B1293689
theorem B862927 : Blo 860564 862927 := bstep (se 1 (by rfl) ⟨647195, by rfl⟩ : syracuseStep 862927 = 1294391) B1294391
theorem B862951 : Blo 860564 862951 := bstep (se 1 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 862951 = 1294427) B1294427
theorem B8301305 : Blo 860564 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B5516059 : Blo 860564 5516059 := bstep (se 1 (by rfl) ⟨4137044, by rfl⟩ : syracuseStep 5516059 = 8274089) B8274089
theorem B7187297 : Blo 860564 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B1452991 : Blo 860564 1452991 := bstep (se 1 (by rfl) ⟨1089743, by rfl⟩ : syracuseStep 1452991 = 2179487) B2179487
theorem B11808251 : Blo 860564 11808251 := bstep (se 1 (by rfl) ⟨8856188, by rfl⟩ : syracuseStep 11808251 = 17712377) B17712377
theorem B5254727 : Blo 860564 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B1453727 : Blo 860564 1453727 := bstep (se 1 (by rfl) ⟨1090295, by rfl⟩ : syracuseStep 1453727 = 2180591) B2180591
theorem B863951 : Blo 860564 863951 := bstep (se 1 (by rfl) ⟨647963, by rfl⟩ : syracuseStep 863951 = 1295927) B1295927
theorem B5255293 : Blo 860564 5255293 := bstep (se 3 (by rfl) ⟨985367, by rfl⟩ : syracuseStep 5255293 = 1970735) B1970735
theorem B1454591 : Blo 860564 1454591 := bstep (se 1 (by rfl) ⟨1090943, by rfl⟩ : syracuseStep 1454591 = 2181887) B2181887
theorem B1094143 : Blo 860564 1094143 := bstep (se 1 (by rfl) ⟨820607, by rfl⟩ : syracuseStep 1094143 = 1641215) B1641215
theorem B7877209 : Blo 860564 7877209 := bstep (se 2 (by rfl) ⟨2953953, by rfl⟩ : syracuseStep 7877209 = 5907907) B5907907
theorem B996223 : Blo 860564 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B1455529 : Blo 860564 1455529 := bstep (se 2 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 1455529 = 1091647) B1091647
theorem B1455583 : Blo 860564 1455583 := bstep (se 1 (by rfl) ⟨1091687, by rfl⟩ : syracuseStep 1455583 = 2183375) B2183375
theorem B1292159 : Blo 860564 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B1292255 : Blo 860564 1292255 := bstep (se 1 (by rfl) ⟨969191, by rfl⟩ : syracuseStep 1292255 = 1938383) B1938383
theorem B1456123 : Blo 860564 1456123 := bstep (se 1 (by rfl) ⟨1092092, by rfl⟩ : syracuseStep 1456123 = 2184185) B2184185
theorem B1751375 : Blo 860564 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B1292699 : Blo 860564 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B1456555 : Blo 860564 1456555 := bstep (se 1 (by rfl) ⟨1092416, by rfl⟩ : syracuseStep 1456555 = 2184833) B2184833
theorem B1456967 : Blo 860564 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B5258141 : Blo 860564 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B1293407 : Blo 860564 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B1293449 : Blo 860564 1293449 := bstep (se 2 (by rfl) ⟨485043, by rfl⟩ : syracuseStep 1293449 = 970087) B970087
theorem B1293503 : Blo 860564 1293503 := bstep (se 1 (by rfl) ⟨970127, by rfl⟩ : syracuseStep 1293503 = 1940255) B1940255
theorem B1293563 : Blo 860564 1293563 := bstep (se 1 (by rfl) ⟨970172, by rfl⟩ : syracuseStep 1293563 = 1940345) B1940345
theorem B6536699 : Blo 860564 6536699 := bstep (se 1 (by rfl) ⟨4902524, by rfl⟩ : syracuseStep 6536699 = 9805049) B9805049
theorem B2768537 : Blo 860564 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B7454375 : Blo 860564 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B1294217 : Blo 860564 1294217 := bstep (se 2 (by rfl) ⟨485331, by rfl⟩ : syracuseStep 1294217 = 970663) B970663
theorem B1228775 : Blo 860564 1228775 := bstep (se 1 (by rfl) ⟨921581, by rfl⟩ : syracuseStep 1228775 = 1843163) B1843163
theorem B1458283 : Blo 860564 1458283 := bstep (se 1 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 1458283 = 2187425) B2187425
theorem B1294751 : Blo 860564 1294751 := bstep (se 1 (by rfl) ⟨971063, by rfl⟩ : syracuseStep 1294751 = 1942127) B1942127
theorem B1294847 : Blo 860564 1294847 := bstep (se 1 (by rfl) ⟨971135, by rfl⟩ : syracuseStep 1294847 = 1942271) B1942271
theorem B1295231 : Blo 860564 1295231 := bstep (se 1 (by rfl) ⟨971423, by rfl⟩ : syracuseStep 1295231 = 1942847) B1942847
theorem B7358161 : Blo 860564 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B11028221 : Blo 860564 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B6539129 : Blo 860564 6539129 := bstep (se 2 (by rfl) ⟨2452173, by rfl⟩ : syracuseStep 6539129 = 4904347) B4904347
theorem B4147271 : Blo 860564 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B1296455 : Blo 860564 1296455 := bstep (se 1 (by rfl) ⟨972341, by rfl⟩ : syracuseStep 1296455 = 1944683) B1944683
theorem B1296491 : Blo 860564 1296491 := bstep (se 1 (by rfl) ⟨972368, by rfl⟩ : syracuseStep 1296491 = 1944737) B1944737
theorem B1296635 : Blo 860564 1296635 := bstep (se 1 (by rfl) ⟨972476, by rfl⟩ : syracuseStep 1296635 = 1944953) B1944953
theorem B8277011 : Blo 860564 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B13290641 : Blo 860564 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B1658153 : Blo 860564 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B28004453 : Blo 860564 28004453 := bstep (se 4 (by rfl) ⟨2625417, by rfl⟩ : syracuseStep 28004453 = 5250835) B5250835
theorem B7000307 : Blo 860564 7000307 := bstep (se 1 (by rfl) ⟨5250230, by rfl⟩ : syracuseStep 7000307 = 10500461) B10500461
theorem B4968955 : Blo 860564 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B972031 : Blo 860564 972031 := bstep (se 1 (by rfl) ⟨729023, by rfl⟩ : syracuseStep 972031 = 1458047) B1458047
theorem B4969783 : Blo 860564 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B2185319 : Blo 860564 2185319 := bstep (se 1 (by rfl) ⟨1638989, by rfl⟩ : syracuseStep 2185319 = 3277979) B3277979
theorem B11032685 : Blo 860564 11032685 := bstep (se 3 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 11032685 = 4137257) B4137257
theorem B19880063 : Blo 860564 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B2906387 : Blo 860564 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B2906495 : Blo 860564 2906495 := bstep (se 1 (by rfl) ⟨2179871, by rfl⟩ : syracuseStep 2906495 = 4359743) B4359743
theorem B7363493 : Blo 860564 7363493 := bstep (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) B1380655
theorem B59661521 : Blo 860564 59661521 := bstep (se 2 (by rfl) ⟨22373070, by rfl⟩ : syracuseStep 59661521 = 44746141) B44746141
theorem B8871623 : Blo 860564 8871623 := bstep (se 1 (by rfl) ⟨6653717, by rfl⟩ : syracuseStep 8871623 = 13307435) B13307435
theorem B2908007 : Blo 860564 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B2908115 : Blo 860564 2908115 := bstep (se 1 (by rfl) ⟨2181086, by rfl⟩ : syracuseStep 2908115 = 4362173) B4362173
theorem B2908223 : Blo 860564 2908223 := bstep (se 1 (by rfl) ⟨2181167, by rfl⟩ : syracuseStep 2908223 = 4362335) B4362335
theorem B95903959 : Blo 860564 95903959 := bstep (se 1 (by rfl) ⟨71927969, by rfl⟩ : syracuseStep 95903959 = 143855939) B143855939
theorem B2188255 : Blo 860564 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B11790299 : Blo 860564 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B3270719 : Blo 860564 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B2910329 : Blo 860564 2910329 := bstep (se 2 (by rfl) ⟨1091373, by rfl⟩ : syracuseStep 2910329 = 2182747) B2182747
theorem B2451809 : Blo 860564 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B2910815 : Blo 860564 2910815 := bstep (se 1 (by rfl) ⟨2183111, by rfl⟩ : syracuseStep 2910815 = 4366223) B4366223
theorem B33647663 : Blo 860564 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B2911463 : Blo 860564 2911463 := bstep (se 1 (by rfl) ⟨2183597, by rfl⟩ : syracuseStep 2911463 = 4367195) B4367195
theorem B6221195 : Blo 860564 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B3272359 : Blo 860564 3272359 := bstep (se 1 (by rfl) ⟨2454269, by rfl⟩ : syracuseStep 3272359 = 4908539) B4908539
theorem B4911911 : Blo 860564 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B2913515 : Blo 860564 2913515 := bstep (se 1 (by rfl) ⟨2185136, by rfl⟩ : syracuseStep 2913515 = 4370273) B4370273
theorem B1963511 : Blo 860564 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B5896135 : Blo 860564 5896135 := bstep (se 1 (by rfl) ⟨4422101, by rfl⟩ : syracuseStep 5896135 = 8844203) B8844203
theorem B1637243 : Blo 860564 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B4359419 : Blo 860564 4359419 := bstep (se 1 (by rfl) ⟨3269564, by rfl⟩ : syracuseStep 4359419 = 6539129) B6539129
theorem B2917673 : Blo 860564 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B1640911 : Blo 860564 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B4917995 : Blo 860564 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B6556625 : Blo 860564 6556625 := bstep (se 2 (by rfl) ⟨2458734, by rfl⟩ : syracuseStep 6556625 = 4917469) B4917469
theorem B2952283 : Blo 860564 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B3280135 : Blo 860564 3280135 := bstep (se 1 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 3280135 = 4920203) B4920203
theorem B4984105 : Blo 860564 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B2362679 : Blo 860564 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B1838875 : Blo 860564 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B24907607 : Blo 860564 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B1937321 : Blo 860564 1937321 := bstep (se 2 (by rfl) ⟨726495, by rfl⟩ : syracuseStep 1937321 = 1452991) B1452991
theorem B1937591 : Blo 860564 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B1937663 : Blo 860564 1937663 := bstep (se 1 (by rfl) ⟨1453247, by rfl⟩ : syracuseStep 1937663 = 2906495) B2906495
theorem B4363145 : Blo 860564 4363145 := bstep (se 2 (by rfl) ⟨1636179, by rfl⟩ : syracuseStep 4363145 = 3272359) B3272359
theorem B1938671 : Blo 860564 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B1938743 : Blo 860564 1938743 := bstep (se 1 (by rfl) ⟨1454057, by rfl⟩ : syracuseStep 1938743 = 2908115) B2908115
theorem B1938815 : Blo 860564 1938815 := bstep (se 1 (by rfl) ⟨1454111, by rfl⟩ : syracuseStep 1938815 = 2908223) B2908223
theorem B6625273 : Blo 860564 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B1841147 : Blo 860564 1841147 := bstep (se 1 (by rfl) ⟨1380860, by rfl⟩ : syracuseStep 1841147 = 2761721) B2761721
theorem B1940219 : Blo 860564 1940219 := bstep (se 1 (by rfl) ⟨1455164, by rfl⟩ : syracuseStep 1940219 = 2910329) B2910329
theorem B1940543 : Blo 860564 1940543 := bstep (se 1 (by rfl) ⟨1455407, by rfl⟩ : syracuseStep 1940543 = 2910815) B2910815
theorem B6626377 : Blo 860564 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B1940705 : Blo 860564 1940705 := bstep (se 2 (by rfl) ⟨727764, by rfl⟩ : syracuseStep 1940705 = 1455529) B1455529
theorem B1940777 : Blo 860564 1940777 := bstep (se 2 (by rfl) ⟨727791, by rfl⟩ : syracuseStep 1940777 = 1455583) B1455583
theorem B1940975 : Blo 860564 1940975 := bstep (se 1 (by rfl) ⟨1455731, by rfl⟩ : syracuseStep 1940975 = 2911463) B2911463
theorem B7872167 : Blo 860564 7872167 := bstep (se 1 (by rfl) ⟨5904125, by rfl⟩ : syracuseStep 7872167 = 11808251) B11808251
theorem B1941497 : Blo 860564 1941497 := bstep (se 2 (by rfl) ⟨728061, by rfl⟩ : syracuseStep 1941497 = 1456123) B1456123
theorem B1942073 : Blo 860564 1942073 := bstep (se 2 (by rfl) ⟨728277, by rfl⟩ : syracuseStep 1942073 = 1456555) B1456555
theorem B1942343 : Blo 860564 1942343 := bstep (se 1 (by rfl) ⟨1456757, by rfl⟩ : syracuseStep 1942343 = 2913515) B2913515
theorem B861439 : Blo 860564 861439 := bstep (se 1 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 861439 = 1292159) B1292159
theorem B861503 : Blo 860564 861503 := bstep (se 1 (by rfl) ⟨646127, by rfl⟩ : syracuseStep 861503 = 1292255) B1292255
theorem B861799 : Blo 860564 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B7382765 : Blo 860564 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B1091495 : Blo 860564 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B862271 : Blo 860564 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B862299 : Blo 860564 862299 := bstep (se 1 (by rfl) ⟨646724, by rfl⟩ : syracuseStep 862299 = 1293449) B1293449
theorem B862335 : Blo 860564 862335 := bstep (se 1 (by rfl) ⟨646751, by rfl⟩ : syracuseStep 862335 = 1293503) B1293503
theorem B862375 : Blo 860564 862375 := bstep (se 1 (by rfl) ⟨646781, by rfl⟩ : syracuseStep 862375 = 1293563) B1293563
theorem B862811 : Blo 860564 862811 := bstep (se 1 (by rfl) ⟨647108, by rfl⟩ : syracuseStep 862811 = 1294217) B1294217
theorem B1944377 : Blo 860564 1944377 := bstep (se 2 (by rfl) ⟨729141, by rfl⟩ : syracuseStep 1944377 = 1458283) B1458283
theorem B863167 : Blo 860564 863167 := bstep (se 1 (by rfl) ⟨647375, by rfl⟩ : syracuseStep 863167 = 1294751) B1294751
theorem B127871945 : Blo 860564 127871945 := bstep (se 2 (by rfl) ⟨47951979, by rfl⟩ : syracuseStep 127871945 = 95903959) B95903959
theorem B1747937 : Blo 860564 1747937 := bstep (se 2 (by rfl) ⟨655476, by rfl⟩ : syracuseStep 1747937 = 1310953) B1310953
theorem B863231 : Blo 860564 863231 := bstep (se 1 (by rfl) ⟨647423, by rfl⟩ : syracuseStep 863231 = 1294847) B1294847
theorem B863487 : Blo 860564 863487 := bstep (se 1 (by rfl) ⟨647615, by rfl⟩ : syracuseStep 863487 = 1295231) B1295231
theorem B1945007 : Blo 860564 1945007 := bstep (se 1 (by rfl) ⟨1458755, by rfl⟩ : syracuseStep 1945007 = 2917511) B2917511
theorem B7352147 : Blo 860564 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B2764847 : Blo 860564 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B864303 : Blo 860564 864303 := bstep (se 1 (by rfl) ⟨648227, by rfl⟩ : syracuseStep 864303 = 1296455) B1296455
theorem B864327 : Blo 860564 864327 := bstep (se 1 (by rfl) ⟨648245, by rfl⟩ : syracuseStep 864327 = 1296491) B1296491
theorem B864423 : Blo 860564 864423 := bstep (se 1 (by rfl) ⟨648317, by rfl⟩ : syracuseStep 864423 = 1296635) B1296635
theorem B5518007 : Blo 860564 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B8860427 : Blo 860564 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B9810881 : Blo 860564 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B4666871 : Blo 860564 4666871 := bstep (se 1 (by rfl) ⟨3500153, by rfl⟩ : syracuseStep 4666871 = 7000307) B7000307
theorem B1226281 : Blo 860564 1226281 := bstep (se 2 (by rfl) ⟨459855, by rfl⟩ : syracuseStep 1226281 = 919711) B919711
theorem B4372379 : Blo 860564 4372379 := bstep (se 1 (by rfl) ⟨3279284, by rfl⟩ : syracuseStep 4372379 = 6558569) B6558569
theorem B21018527 : Blo 860564 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B1292315 : Blo 860564 1292315 := bstep (se 1 (by rfl) ⟨969236, by rfl⟩ : syracuseStep 1292315 = 1938473) B1938473
theorem B7354745 : Blo 860564 7354745 := bstep (se 2 (by rfl) ⟨2758029, by rfl⟩ : syracuseStep 7354745 = 5516059) B5516059
theorem B1292735 : Blo 860564 1292735 := bstep (se 1 (by rfl) ⟨969551, by rfl⟩ : syracuseStep 1292735 = 1939103) B1939103
theorem B1456879 : Blo 860564 1456879 := bstep (se 1 (by rfl) ⟨1092659, by rfl⟩ : syracuseStep 1456879 = 2185319) B2185319
theorem B7355123 : Blo 860564 7355123 := bstep (se 1 (by rfl) ⟨5516342, by rfl⟩ : syracuseStep 7355123 = 11032685) B11032685
theorem B13253375 : Blo 860564 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B1293167 : Blo 860564 1293167 := bstep (se 1 (by rfl) ⟨969875, by rfl⟩ : syracuseStep 1293167 = 1939751) B1939751
theorem B1293311 : Blo 860564 1293311 := bstep (se 1 (by rfl) ⟨969983, by rfl⟩ : syracuseStep 1293311 = 1939967) B1939967
theorem B5914415 : Blo 860564 5914415 := bstep (se 1 (by rfl) ⟨4435811, by rfl⟩ : syracuseStep 5914415 = 8871623) B8871623
theorem B1294271 : Blo 860564 1294271 := bstep (se 1 (by rfl) ⟨970703, by rfl⟩ : syracuseStep 1294271 = 1941407) B1941407
theorem B8307305 : Blo 860564 8307305 := bstep (se 2 (by rfl) ⟨3115239, by rfl⟩ : syracuseStep 8307305 = 6230479) B6230479
theorem B1458857 : Blo 860564 1458857 := bstep (se 2 (by rfl) ⟨547071, by rfl⟩ : syracuseStep 1458857 = 1094143) B1094143
theorem B10502945 : Blo 860564 10502945 := bstep (se 2 (by rfl) ⟨3938604, by rfl⟩ : syracuseStep 10502945 = 7877209) B7877209
theorem B6538157 : Blo 860564 6538157 := bstep (se 3 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 6538157 = 2451809) B2451809
theorem B1328297 : Blo 860564 1328297 := bstep (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) B996223
theorem B8832185 : Blo 860564 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B2180479 : Blo 860564 2180479 := bstep (se 1 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 2180479 = 3270719) B3270719
theorem B1296041 : Blo 860564 1296041 := bstep (se 2 (by rfl) ⟨486015, by rfl⟩ : syracuseStep 1296041 = 972031) B972031
theorem B22136813 : Blo 860564 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B22431775 : Blo 860564 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B4147463 : Blo 860564 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B969151 : Blo 860564 969151 := bstep (se 1 (by rfl) ⟨726863, by rfl⟩ : syracuseStep 969151 = 1453727) B1453727
theorem B969727 : Blo 860564 969727 := bstep (se 1 (by rfl) ⟨727295, by rfl⟩ : syracuseStep 969727 = 1454591) B1454591
theorem B76664501 : Blo 860564 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B14012605 : Blo 860564 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B1167583 : Blo 860564 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B971311 : Blo 860564 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B31446053 : Blo 860564 31446053 := bstep (se 4 (by rfl) ⟨2948067, by rfl⟩ : syracuseStep 31446053 = 5896135) B5896135
theorem B4969583 : Blo 860564 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B6313555 : Blo 860564 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B1660655 : Blo 860564 1660655 := bstep (se 1 (by rfl) ⟨1245491, by rfl⟩ : syracuseStep 1660655 = 2490983) B2490983
theorem B5527439 : Blo 860564 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B53172395 : Blo 860564 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B59792579 : Blo 860564 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B1105435 : Blo 860564 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B7364519 : Blo 860564 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B18669635 : Blo 860564 18669635 := bstep (se 1 (by rfl) ⟨14002226, by rfl⟩ : syracuseStep 18669635 = 28004453) B28004453
theorem B22110569 : Blo 860564 22110569 := bstep (se 2 (by rfl) ⟨8291463, by rfl⟩ : syracuseStep 22110569 = 16582927) B16582927
theorem B14705387 : Blo 860564 14705387 := bstep (se 1 (by rfl) ⟨11029040, by rfl⟩ : syracuseStep 14705387 = 22058081) B22058081
theorem B4908995 : Blo 860564 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B39774347 : Blo 860564 39774347 := bstep (se 1 (by rfl) ⟨29830760, by rfl⟩ : syracuseStep 39774347 = 59661521) B59661521
theorem B2910491 : Blo 860564 2910491 := bstep (se 1 (by rfl) ⟨2182868, by rfl⟩ : syracuseStep 2910491 = 4365737) B4365737
theorem B3500687 : Blo 860564 3500687 := bstep (se 1 (by rfl) ⟨2625515, by rfl⟩ : syracuseStep 3500687 = 5251031) B5251031
theorem B7007057 : Blo 860564 7007057 := bstep (se 2 (by rfl) ⟨2627646, by rfl⟩ : syracuseStep 7007057 = 5255293) B5255293
theorem B5533231 : Blo 860564 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B7860199 : Blo 860564 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B3274607 : Blo 860564 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B1309007 : Blo 860564 1309007 := bstep (se 1 (by rfl) ⟨981755, by rfl⟩ : syracuseStep 1309007 = 1963511) B1963511
theorem B3505427 : Blo 860564 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B4357799 : Blo 860564 4357799 := bstep (se 1 (by rfl) ⟨3268349, by rfl⟩ : syracuseStep 4357799 = 6536699) B6536699
theorem B3276733 : Blo 860564 3276733 := bstep (se 3 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 3276733 = 1228775) B1228775
theorem B5538203 : Blo 860564 5538203 := bstep (se 1 (by rfl) ⟨4153652, by rfl⟩ : syracuseStep 5538203 = 8307305) B8307305
theorem B4358771 : Blo 860564 4358771 := bstep (se 1 (by rfl) ⟨3269078, by rfl⟩ : syracuseStep 4358771 = 6538157) B6538157
theorem B3278663 : Blo 860564 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B1575119 : Blo 860564 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B3542125 : Blo 860564 3542125 := bstep (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) B1328297
theorem B3313055 : Blo 860564 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B3936377 : Blo 860564 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B7377641 : Blo 860564 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B18683473 : Blo 860564 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B9803591 : Blo 860564 9803591 := bstep (se 1 (by rfl) ⟨7352693, by rfl⟩ : syracuseStep 9803591 = 14705387) B14705387
theorem B4921843 : Blo 860564 4921843 := bstep (se 1 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 4921843 = 7382765) B7382765
theorem B26516231 : Blo 860564 26516231 := bstep (se 1 (by rfl) ⟨19887173, by rfl⟩ : syracuseStep 26516231 = 39774347) B39774347
theorem B1940327 : Blo 860564 1940327 := bstep (se 1 (by rfl) ⟨1455245, by rfl⟩ : syracuseStep 1940327 = 2910491) B2910491
theorem B2333791 : Blo 860564 2333791 := bstep (se 1 (by rfl) ⟨1750343, by rfl⟩ : syracuseStep 2333791 = 3500687) B3500687
theorem B4661165 : Blo 860564 4661165 := bstep (se 3 (by rfl) ⟨873968, by rfl⟩ : syracuseStep 4661165 = 1747937) B1747937
theorem B1843231 : Blo 860564 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B3678671 : Blo 860564 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B5906951 : Blo 860564 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B1942505 : Blo 860564 1942505 := bstep (se 2 (by rfl) ⟨728439, by rfl⟩ : syracuseStep 1942505 = 1456879) B1456879
theorem B861543 : Blo 860564 861543 := bstep (se 1 (by rfl) ⟨646157, by rfl⟩ : syracuseStep 861543 = 1292315) B1292315
theorem B861823 : Blo 860564 861823 := bstep (se 1 (by rfl) ⟨646367, by rfl⟩ : syracuseStep 861823 = 1292735) B1292735
theorem B862111 : Blo 860564 862111 := bstep (se 1 (by rfl) ⟨646583, by rfl⟩ : syracuseStep 862111 = 1293167) B1293167
theorem B862207 : Blo 860564 862207 := bstep (se 1 (by rfl) ⟨646655, by rfl⟩ : syracuseStep 862207 = 1293311) B1293311
theorem B15771773 : Blo 860564 15771773 := bstep (se 3 (by rfl) ⟨2957207, by rfl⟩ : syracuseStep 15771773 = 5914415) B5914415
theorem B2336951 : Blo 860564 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B4368977 : Blo 860564 4368977 := bstep (se 2 (by rfl) ⟨1638366, by rfl⟩ : syracuseStep 4368977 = 3276733) B3276733
theorem B862847 : Blo 860564 862847 := bstep (se 1 (by rfl) ⟨647135, by rfl⟩ : syracuseStep 862847 = 1294271) B1294271
theorem B1945115 : Blo 860564 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B864027 : Blo 860564 864027 := bstep (se 1 (by rfl) ⟨648020, by rfl⟩ : syracuseStep 864027 = 1296041) B1296041
theorem B14757875 : Blo 860564 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B4371083 : Blo 860564 4371083 := bstep (se 1 (by rfl) ⟨3278312, by rfl⟩ : syracuseStep 4371083 = 6556625) B6556625
theorem B1291547 : Blo 860564 1291547 := bstep (se 1 (by rfl) ⟨968660, by rfl⟩ : syracuseStep 1291547 = 1937321) B1937321
theorem B1291727 : Blo 860564 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B1291775 : Blo 860564 1291775 := bstep (se 1 (by rfl) ⟨968831, by rfl⟩ : syracuseStep 1291775 = 1937663) B1937663
theorem B1292201 : Blo 860564 1292201 := bstep (se 2 (by rfl) ⟨484575, by rfl⟩ : syracuseStep 1292201 = 969151) B969151
theorem B1292447 : Blo 860564 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B1292495 : Blo 860564 1292495 := bstep (se 1 (by rfl) ⟨969371, by rfl⟩ : syracuseStep 1292495 = 1938743) B1938743
theorem B1292543 : Blo 860564 1292543 := bstep (se 1 (by rfl) ⟨969407, by rfl⟩ : syracuseStep 1292543 = 1938815) B1938815
theorem B3684959 : Blo 860564 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B1227431 : Blo 860564 1227431 := bstep (se 1 (by rfl) ⟨920573, by rfl⟩ : syracuseStep 1227431 = 1841147) B1841147
theorem B1292969 : Blo 860564 1292969 := bstep (se 2 (by rfl) ⟨484863, by rfl⟩ : syracuseStep 1292969 = 969727) B969727
theorem B4373513 : Blo 860564 4373513 := bstep (se 2 (by rfl) ⟨1640067, by rfl⟩ : syracuseStep 4373513 = 3280135) B3280135
theorem B1293479 : Blo 860564 1293479 := bstep (se 1 (by rfl) ⟨970109, by rfl⟩ : syracuseStep 1293479 = 1940219) B1940219
theorem B1293695 : Blo 860564 1293695 := bstep (se 1 (by rfl) ⟨970271, by rfl⟩ : syracuseStep 1293695 = 1940543) B1940543
theorem B39861719 : Blo 860564 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B1293803 : Blo 860564 1293803 := bstep (se 1 (by rfl) ⟨970352, by rfl⟩ : syracuseStep 1293803 = 1940705) B1940705
theorem B1293851 : Blo 860564 1293851 := bstep (se 1 (by rfl) ⟨970388, by rfl⟩ : syracuseStep 1293851 = 1940777) B1940777
theorem B1293983 : Blo 860564 1293983 := bstep (se 1 (by rfl) ⟨970487, by rfl⟩ : syracuseStep 1293983 = 1940975) B1940975
theorem B1294331 : Blo 860564 1294331 := bstep (se 1 (by rfl) ⟨970748, by rfl⟩ : syracuseStep 1294331 = 1941497) B1941497
theorem B1556777 : Blo 860564 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B1294715 : Blo 860564 1294715 := bstep (se 1 (by rfl) ⟨971036, by rfl⟩ : syracuseStep 1294715 = 1942073) B1942073
theorem B1294895 : Blo 860564 1294895 := bstep (se 1 (by rfl) ⟨971171, by rfl⟩ : syracuseStep 1294895 = 1942343) B1942343
theorem B11059901 : Blo 860564 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B1295081 : Blo 860564 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B3490685 : Blo 860564 3490685 := bstep (se 3 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 3490685 = 1309007) B1309007
theorem B1296251 : Blo 860564 1296251 := bstep (se 1 (by rfl) ⟨972188, by rfl⟩ : syracuseStep 1296251 = 1944377) B1944377
theorem B4671371 : Blo 860564 4671371 := bstep (se 1 (by rfl) ⟨3503528, by rfl⟩ : syracuseStep 4671371 = 7007057) B7007057
theorem B85247963 : Blo 860564 85247963 := bstep (se 1 (by rfl) ⟨63935972, by rfl⟩ : syracuseStep 85247963 = 127871945) B127871945
theorem B1296671 : Blo 860564 1296671 := bstep (se 1 (by rfl) ⟨972503, by rfl⟩ : syracuseStep 1296671 = 1945007) B1945007
theorem B4901431 : Blo 860564 4901431 := bstep (se 1 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 4901431 = 7352147) B7352147
theorem B8833697 : Blo 860564 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B6540587 : Blo 860564 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B2183071 : Blo 860564 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B14012351 : Blo 860564 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B8835169 : Blo 860564 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B4903163 : Blo 860564 4903163 := bstep (se 1 (by rfl) ⟨3677372, by rfl⟩ : syracuseStep 4903163 = 7354745) B7354745
theorem B20992445 : Blo 860564 20992445 := bstep (se 3 (by rfl) ⟨3936083, by rfl⟩ : syracuseStep 20992445 = 7872167) B7872167
theorem B4903415 : Blo 860564 4903415 := bstep (se 1 (by rfl) ⟨3677561, by rfl⟩ : syracuseStep 4903415 = 7355123) B7355123
theorem B8835583 : Blo 860564 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B2905199 : Blo 860564 2905199 := bstep (se 1 (by rfl) ⟨2178899, by rfl⟩ : syracuseStep 2905199 = 4357799) B4357799
theorem B972571 : Blo 860564 972571 := bstep (se 1 (by rfl) ⟨729428, by rfl⟩ : syracuseStep 972571 = 1458857) B1458857
theorem B7001963 : Blo 860564 7001963 := bstep (se 1 (by rfl) ⟨5251472, by rfl⟩ : syracuseStep 7001963 = 10502945) B10502945
theorem B5888123 : Blo 860564 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B2906279 : Blo 860564 2906279 := bstep (se 1 (by rfl) ⟨2179709, by rfl⟩ : syracuseStep 2906279 = 4359419) B4359419
theorem B2907305 : Blo 860564 2907305 := bstep (se 2 (by rfl) ⟨1090239, by rfl⟩ : syracuseStep 2907305 = 2180479) B2180479
theorem B51109667 : Blo 860564 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B16605071 : Blo 860564 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B29909033 : Blo 860564 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B2908763 : Blo 860564 2908763 := bstep (se 1 (by rfl) ⟨2181572, by rfl⟩ : syracuseStep 2908763 = 4363145) B4363145
theorem B2187881 : Blo 860564 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B20964035 : Blo 860564 20964035 := bstep (se 1 (by rfl) ⟨15723026, by rfl⟩ : syracuseStep 20964035 = 31446053) B31446053
theorem B1107103 : Blo 860564 1107103 := bstep (se 1 (by rfl) ⟨830327, by rfl⟩ : syracuseStep 1107103 = 1660655) B1660655
theorem B35448263 : Blo 860564 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B6645473 : Blo 860564 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B2451833 : Blo 860564 2451833 := bstep (se 2 (by rfl) ⟨919437, by rfl⟩ : syracuseStep 2451833 = 1838875) B1838875
theorem B2910653 : Blo 860564 2910653 := bstep (se 3 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 2910653 = 1091495) B1091495
theorem B4909679 : Blo 860564 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B10480265 : Blo 860564 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B12446423 : Blo 860564 12446423 := bstep (se 1 (by rfl) ⟨9334817, by rfl⟩ : syracuseStep 12446423 = 18669635) B18669635
theorem B14740379 : Blo 860564 14740379 := bstep (se 1 (by rfl) ⟨11055284, by rfl⟩ : syracuseStep 14740379 = 22110569) B22110569
theorem B3272663 : Blo 860564 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B1635041 : Blo 860564 1635041 := bstep (se 2 (by rfl) ⟨613140, by rfl⟩ : syracuseStep 1635041 = 1226281) B1226281
theorem B8418073 : Blo 860564 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B3111247 : Blo 860564 3111247 := bstep (se 1 (by rfl) ⟨2333435, by rfl⟩ : syracuseStep 3111247 = 4666871) B4666871
theorem B2914919 : Blo 860564 2914919 := bstep (se 1 (by rfl) ⟨2186189, by rfl⟩ : syracuseStep 2914919 = 4372379) B4372379
theorem B1473913 : Blo 860564 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B2457641 : Blo 860564 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B7373267 : Blo 860564 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B2327123 : Blo 860564 2327123 := bstep (se 1 (by rfl) ⟨1745342, by rfl⟩ : syracuseStep 2327123 = 3490685) B3490685
theorem B3114247 : Blo 860564 3114247 := bstep (se 1 (by rfl) ⟨2335685, by rfl⟩ : syracuseStep 3114247 = 4671371) B4671371
theorem B1050079 : Blo 860564 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B1476137 : Blo 860564 1476137 := bstep (se 2 (by rfl) ⟨553551, by rfl⟩ : syracuseStep 1476137 = 1107103) B1107103
theorem B4360391 : Blo 860564 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B9341567 : Blo 860564 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B2624251 : Blo 860564 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B13994963 : Blo 860564 13994963 := bstep (se 1 (by rfl) ⟨10496222, by rfl⟩ : syracuseStep 13994963 = 20992445) B20992445
theorem B4918427 : Blo 860564 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B1936799 : Blo 860564 1936799 := bstep (se 1 (by rfl) ⟨1452599, by rfl⟩ : syracuseStep 1936799 = 2905199) B2905199
theorem B1937519 : Blo 860564 1937519 := bstep (se 1 (by rfl) ⟨1453139, by rfl⟩ : syracuseStep 1937519 = 2906279) B2906279
theorem B4722833 : Blo 860564 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B1938203 : Blo 860564 1938203 := bstep (se 1 (by rfl) ⟨1453652, by rfl⟩ : syracuseStep 1938203 = 2907305) B2907305
theorem B3937967 : Blo 860564 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B1939175 : Blo 860564 1939175 := bstep (se 1 (by rfl) ⟨1454381, by rfl⟩ : syracuseStep 1939175 = 2908763) B2908763
theorem B23632175 : Blo 860564 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B4430315 : Blo 860564 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B1940435 : Blo 860564 1940435 := bstep (se 1 (by rfl) ⟨1455326, by rfl⟩ : syracuseStep 1940435 = 2910653) B2910653
theorem B6986843 : Blo 860564 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B8297615 : Blo 860564 8297615 := bstep (se 1 (by rfl) ⟨6223211, by rfl⟩ : syracuseStep 8297615 = 12446423) B12446423
theorem B24911297 : Blo 860564 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B9838583 : Blo 860564 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B1090027 : Blo 860564 1090027 := bstep (se 1 (by rfl) ⟨817520, by rfl⟩ : syracuseStep 1090027 = 1635041) B1635041
theorem B6562457 : Blo 860564 6562457 := bstep (se 2 (by rfl) ⟨2460921, by rfl⟩ : syracuseStep 6562457 = 4921843) B4921843
theorem B861031 : Blo 860564 861031 := bstep (se 1 (by rfl) ⟨645773, by rfl⟩ : syracuseStep 861031 = 1291547) B1291547
theorem B861151 : Blo 860564 861151 := bstep (se 1 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 861151 = 1291727) B1291727
theorem B861183 : Blo 860564 861183 := bstep (se 1 (by rfl) ⟨645887, by rfl⟩ : syracuseStep 861183 = 1291775) B1291775
theorem B861467 : Blo 860564 861467 := bstep (se 1 (by rfl) ⟨646100, by rfl⟩ : syracuseStep 861467 = 1292201) B1292201
theorem B861631 : Blo 860564 861631 := bstep (se 1 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 861631 = 1292447) B1292447
theorem B861663 : Blo 860564 861663 := bstep (se 1 (by rfl) ⟨646247, by rfl⟩ : syracuseStep 861663 = 1292495) B1292495
theorem B861695 : Blo 860564 861695 := bstep (se 1 (by rfl) ⟨646271, by rfl⟩ : syracuseStep 861695 = 1292543) B1292543
theorem B1943279 : Blo 860564 1943279 := bstep (se 1 (by rfl) ⟨1457459, by rfl⟩ : syracuseStep 1943279 = 2914919) B2914919
theorem B861979 : Blo 860564 861979 := bstep (se 1 (by rfl) ⟨646484, by rfl⟩ : syracuseStep 861979 = 1292969) B1292969
theorem B862319 : Blo 860564 862319 := bstep (se 1 (by rfl) ⟨646739, by rfl⟩ : syracuseStep 862319 = 1293479) B1293479
theorem B862463 : Blo 860564 862463 := bstep (se 1 (by rfl) ⟨646847, by rfl⟩ : syracuseStep 862463 = 1293695) B1293695
theorem B862535 : Blo 860564 862535 := bstep (se 1 (by rfl) ⟨646901, by rfl⟩ : syracuseStep 862535 = 1293803) B1293803
theorem B862567 : Blo 860564 862567 := bstep (se 1 (by rfl) ⟨646925, by rfl⟩ : syracuseStep 862567 = 1293851) B1293851
theorem B862655 : Blo 860564 862655 := bstep (se 1 (by rfl) ⟨646991, by rfl⟩ : syracuseStep 862655 = 1293983) B1293983
theorem B862887 : Blo 860564 862887 := bstep (se 1 (by rfl) ⟨647165, by rfl⟩ : syracuseStep 862887 = 1294331) B1294331
theorem B863143 : Blo 860564 863143 := bstep (se 1 (by rfl) ⟨647357, by rfl⟩ : syracuseStep 863143 = 1294715) B1294715
theorem B863263 : Blo 860564 863263 := bstep (se 1 (by rfl) ⟨647447, by rfl⟩ : syracuseStep 863263 = 1294895) B1294895
theorem B863387 : Blo 860564 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B864167 : Blo 860564 864167 := bstep (se 1 (by rfl) ⟨648125, by rfl⟩ : syracuseStep 864167 = 1296251) B1296251
theorem B56831975 : Blo 860564 56831975 := bstep (se 1 (by rfl) ⟨42623981, by rfl⟩ : syracuseStep 56831975 = 85247963) B85247963
theorem B864447 : Blo 860564 864447 := bstep (se 1 (by rfl) ⟨648335, by rfl⟩ : syracuseStep 864447 = 1296671) B1296671
theorem B2208703 : Blo 860564 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B6535241 : Blo 860564 6535241 := bstep (se 2 (by rfl) ⟨2450715, by rfl⟩ : syracuseStep 6535241 = 4901431) B4901431
theorem B6535727 : Blo 860564 6535727 := bstep (se 1 (by rfl) ⟨4901795, by rfl⟩ : syracuseStep 6535727 = 9803591) B9803591
theorem B4667975 : Blo 860564 4667975 := bstep (se 1 (by rfl) ⟨3500981, by rfl⟩ : syracuseStep 4667975 = 7001963) B7001963
theorem B17677487 : Blo 860564 17677487 := bstep (se 1 (by rfl) ⟨13258115, by rfl⟩ : syracuseStep 17677487 = 26516231) B26516231
theorem B1293551 : Blo 860564 1293551 := bstep (se 1 (by rfl) ⟨970163, by rfl⟩ : syracuseStep 1293551 = 1940327) B1940327
theorem B19939355 : Blo 860564 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B11780225 : Blo 860564 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B42058061 : Blo 860564 42058061 := bstep (se 3 (by rfl) ⟨7885886, by rfl⟩ : syracuseStep 42058061 = 15771773) B15771773
theorem B1458587 : Blo 860564 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B13976023 : Blo 860564 13976023 := bstep (se 1 (by rfl) ⟨10482017, by rfl⟩ : syracuseStep 13976023 = 20964035) B20964035
theorem B1295003 : Blo 860564 1295003 := bstep (se 1 (by rfl) ⟨971252, by rfl⟩ : syracuseStep 1295003 = 1942505) B1942505
theorem B11780777 : Blo 860564 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B11224097 : Blo 860564 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B1557967 : Blo 860564 1557967 := bstep (se 1 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 1557967 = 2336951) B2336951
theorem B1296743 : Blo 860564 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B1296761 : Blo 860564 1296761 := bstep (se 2 (by rfl) ⟨486285, by rfl⟩ : syracuseStep 1296761 = 972571) B972571
theorem B2181775 : Blo 860564 2181775 := bstep (se 1 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 2181775 = 3272663) B3272663
theorem B4148329 : Blo 860564 4148329 := bstep (se 2 (by rfl) ⟨1555623, by rfl⟩ : syracuseStep 4148329 = 3111247) B3111247
theorem B3692135 : Blo 860564 3692135 := bstep (se 1 (by rfl) ⟨2769101, by rfl⟩ : syracuseStep 3692135 = 5538203) B5538203
theorem B2905847 : Blo 860564 2905847 := bstep (se 1 (by rfl) ⟨2179385, by rfl⟩ : syracuseStep 2905847 = 4358771) B4358771
theorem B4151405 : Blo 860564 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B2185775 : Blo 860564 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B5889131 : Blo 860564 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B3268775 : Blo 860564 3268775 := bstep (se 1 (by rfl) ⟨2451581, by rfl⟩ : syracuseStep 3268775 = 4903163) B4903163
theorem B3268943 : Blo 860564 3268943 := bstep (se 1 (by rfl) ⟨2451707, by rfl⟩ : syracuseStep 3268943 = 4903415) B4903415
theorem B3925415 : Blo 860564 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B34073111 : Blo 860564 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B2910761 : Blo 860564 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B11070047 : Blo 860564 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B3107443 : Blo 860564 3107443 := bstep (se 1 (by rfl) ⟨2330582, by rfl⟩ : syracuseStep 3107443 = 4661165) B4661165
theorem B2452447 : Blo 860564 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B12446885 : Blo 860564 12446885 := bstep (se 4 (by rfl) ⟨1166895, by rfl⟩ : syracuseStep 12446885 = 2333791) B2333791
theorem B1634555 : Blo 860564 1634555 := bstep (se 1 (by rfl) ⟨1225916, by rfl⟩ : syracuseStep 1634555 = 2451833) B2451833
theorem B2912651 : Blo 860564 2912651 := bstep (se 1 (by rfl) ⟨2184488, by rfl⟩ : syracuseStep 2912651 = 4368977) B4368977
theorem B3273119 : Blo 860564 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B3273149 : Blo 860564 3273149 := bstep (se 3 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 3273149 = 1227431) B1227431
theorem B9826919 : Blo 860564 9826919 := bstep (se 1 (by rfl) ⟨7370189, by rfl⟩ : syracuseStep 9826919 = 14740379) B14740379
theorem B2914055 : Blo 860564 2914055 := bstep (se 1 (by rfl) ⟨2185541, by rfl⟩ : syracuseStep 2914055 = 4371083) B4371083
theorem B2456639 : Blo 860564 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B1965217 : Blo 860564 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B2915675 : Blo 860564 2915675 := bstep (se 1 (by rfl) ⟨2186756, by rfl⟩ : syracuseStep 2915675 = 4373513) B4373513
theorem B26574479 : Blo 860564 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B6553709 : Blo 860564 6553709 := bstep (se 3 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 6553709 = 2457641) B2457641
theorem B4915511 : Blo 860564 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B984091 : Blo 860564 984091 := bstep (se 1 (by rfl) ⟨738068, by rfl⟩ : syracuseStep 984091 = 1476137) B1476137
theorem B6227711 : Blo 860564 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B3278951 : Blo 860564 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B3148555 : Blo 860564 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B2461423 : Blo 860564 2461423 := bstep (se 1 (by rfl) ⟨1846067, by rfl⟩ : syracuseStep 2461423 = 3692135) B3692135
theorem B2625311 : Blo 860564 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B1937231 : Blo 860564 1937231 := bstep (se 1 (by rfl) ⟨1452923, by rfl⟩ : syracuseStep 1937231 = 2905847) B2905847
theorem B4657895 : Blo 860564 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B6559055 : Blo 860564 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B22715407 : Blo 860564 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1940507 : Blo 860564 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B7380031 : Blo 860564 7380031 := bstep (se 1 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 7380031 = 11070047) B11070047
theorem B8297923 : Blo 860564 8297923 := bstep (se 1 (by rfl) ⟨6223442, by rfl⟩ : syracuseStep 8297923 = 12446885) B12446885
theorem B37887983 : Blo 860564 37887983 := bstep (se 1 (by rfl) ⟨28415987, by rfl⟩ : syracuseStep 37887983 = 56831975) B56831975
theorem B1089703 : Blo 860564 1089703 := bstep (se 1 (by rfl) ⟨817277, by rfl⟩ : syracuseStep 1089703 = 1634555) B1634555
theorem B1941767 : Blo 860564 1941767 := bstep (se 1 (by rfl) ⟨1456325, by rfl⟩ : syracuseStep 1941767 = 2912651) B2912651
theorem B1942703 : Blo 860564 1942703 := bstep (se 1 (by rfl) ⟨1457027, by rfl⟩ : syracuseStep 1942703 = 2914055) B2914055
theorem B862367 : Blo 860564 862367 := bstep (se 1 (by rfl) ⟨646775, by rfl⟩ : syracuseStep 862367 = 1293551) B1293551
theorem B1943783 : Blo 860564 1943783 := bstep (se 1 (by rfl) ⟨1457837, by rfl⟩ : syracuseStep 1943783 = 2915675) B2915675
theorem B1551415 : Blo 860564 1551415 := bstep (se 1 (by rfl) ⟨1163561, by rfl⟩ : syracuseStep 1551415 = 2327123) B2327123
theorem B863335 : Blo 860564 863335 := bstep (se 1 (by rfl) ⟨647501, by rfl⟩ : syracuseStep 863335 = 1295003) B1295003
theorem B1453369 : Blo 860564 1453369 := bstep (se 2 (by rfl) ⟨545013, by rfl⟩ : syracuseStep 1453369 = 1090027) B1090027
theorem B7482731 : Blo 860564 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B864495 : Blo 860564 864495 := bstep (se 1 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 864495 = 1296743) B1296743
theorem B864507 : Blo 860564 864507 := bstep (se 1 (by rfl) ⟨648380, by rfl⟩ : syracuseStep 864507 = 1296761) B1296761
theorem B2077289 : Blo 860564 2077289 := bstep (se 2 (by rfl) ⟨778983, by rfl⟩ : syracuseStep 2077289 = 1557967) B1557967
theorem B1291199 : Blo 860564 1291199 := bstep (se 1 (by rfl) ⟨968399, by rfl⟩ : syracuseStep 1291199 = 1936799) B1936799
theorem B1291679 : Blo 860564 1291679 := bstep (se 1 (by rfl) ⟨968759, by rfl⟩ : syracuseStep 1291679 = 1937519) B1937519
theorem B1292135 : Blo 860564 1292135 := bstep (se 1 (by rfl) ⟨969101, by rfl⟩ : syracuseStep 1292135 = 1938203) B1938203
theorem B4143257 : Blo 860564 4143257 := bstep (se 2 (by rfl) ⟨1553721, by rfl⟩ : syracuseStep 4143257 = 3107443) B3107443
theorem B1292783 : Blo 860564 1292783 := bstep (se 1 (by rfl) ⟨969587, by rfl⟩ : syracuseStep 1292783 = 1939175) B1939175
theorem B2767603 : Blo 860564 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B1457183 : Blo 860564 1457183 := bstep (se 1 (by rfl) ⟨1092887, by rfl⟩ : syracuseStep 1457183 = 2185775) B2185775
theorem B1293623 : Blo 860564 1293623 := bstep (se 1 (by rfl) ⟨970217, by rfl⟩ : syracuseStep 1293623 = 1940435) B1940435
theorem B2179183 : Blo 860564 2179183 := bstep (se 1 (by rfl) ⟨1634387, by rfl⟩ : syracuseStep 2179183 = 3268775) B3268775
theorem B2179295 : Blo 860564 2179295 := bstep (se 1 (by rfl) ⟨1634471, by rfl⟩ : syracuseStep 2179295 = 3268943) B3268943
theorem B4374971 : Blo 860564 4374971 := bstep (se 1 (by rfl) ⟨3281228, by rfl⟩ : syracuseStep 4374971 = 6562457) B6562457
theorem B1295519 : Blo 860564 1295519 := bstep (se 1 (by rfl) ⟨971639, by rfl⟩ : syracuseStep 1295519 = 1943279) B1943279
theorem B11814173 : Blo 860564 11814173 := bstep (se 3 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 11814173 = 4430315) B4430315
theorem B2182079 : Blo 860564 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B2182099 : Blo 860564 2182099 := bstep (se 1 (by rfl) ⟨1636574, by rfl⟩ : syracuseStep 2182099 = 3273149) B3273149
theorem B47139965 : Blo 860564 47139965 := bstep (se 3 (by rfl) ⟨8838743, by rfl⟩ : syracuseStep 47139965 = 17677487) B17677487
theorem B17716319 : Blo 860564 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B13292903 : Blo 860564 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B7853483 : Blo 860564 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B28038707 : Blo 860564 28038707 := bstep (se 1 (by rfl) ⟨21029030, by rfl⟩ : syracuseStep 28038707 = 42058061) B42058061
theorem B972391 : Blo 860564 972391 := bstep (se 1 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 972391 = 1458587) B1458587
theorem B7853851 : Blo 860564 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B18634697 : Blo 860564 18634697 := bstep (se 2 (by rfl) ⟨6988011, by rfl⟩ : syracuseStep 18634697 = 13976023) B13976023
theorem B2906927 : Blo 860564 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B4152329 : Blo 860564 4152329 := bstep (se 2 (by rfl) ⟨1557123, by rfl⟩ : syracuseStep 4152329 = 3114247) B3114247
theorem B1400105 : Blo 860564 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B9329975 : Blo 860564 9329975 := bstep (se 1 (by rfl) ⟨6997481, by rfl⟩ : syracuseStep 9329975 = 13994963) B13994963
theorem B2909033 : Blo 860564 2909033 := bstep (se 2 (by rfl) ⟨1090887, by rfl⟩ : syracuseStep 2909033 = 2181775) B2181775
theorem B3499001 : Blo 860564 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B3269929 : Blo 860564 3269929 := bstep (se 2 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 3269929 = 2452447) B2452447
theorem B5531105 : Blo 860564 5531105 := bstep (se 2 (by rfl) ⟨2074164, by rfl⟩ : syracuseStep 5531105 = 4148329) B4148329
theorem B15754783 : Blo 860564 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B3926087 : Blo 860564 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B5531743 : Blo 860564 5531743 := bstep (se 1 (by rfl) ⟨4148807, by rfl⟩ : syracuseStep 5531743 = 8297615) B8297615
theorem B16607531 : Blo 860564 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B2616943 : Blo 860564 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B2944937 : Blo 860564 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B6551279 : Blo 860564 6551279 := bstep (se 1 (by rfl) ⟨4913459, by rfl⟩ : syracuseStep 6551279 = 9826919) B9826919
theorem B4356827 : Blo 860564 4356827 := bstep (se 1 (by rfl) ⟨3267620, by rfl⟩ : syracuseStep 4356827 = 6535241) B6535241
theorem B2620289 : Blo 860564 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B4357151 : Blo 860564 4357151 := bstep (se 1 (by rfl) ⟨3267863, by rfl⟩ : syracuseStep 4357151 = 6535727) B6535727
theorem B3111983 : Blo 860564 3111983 := bstep (se 1 (by rfl) ⟨2333987, by rfl⟩ : syracuseStep 3111983 = 4667975) B4667975
theorem B1637759 : Blo 860564 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B3277007 : Blo 860564 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B2916647 : Blo 860564 2916647 := bstep (se 1 (by rfl) ⟨2187485, by rfl⟩ : syracuseStep 2916647 = 4374971) B4374971
theorem B1312121 : Blo 860564 1312121 := bstep (se 2 (by rfl) ⟨492045, by rfl⟩ : syracuseStep 1312121 = 984091) B984091
theorem B4359905 : Blo 860564 4359905 := bstep (se 2 (by rfl) ⟨1634964, by rfl⟩ : syracuseStep 4359905 = 3269929) B3269929
theorem B21006377 : Blo 860564 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B31426643 : Blo 860564 31426643 := bstep (se 1 (by rfl) ⟨23569982, by rfl⟩ : syracuseStep 31426643 = 47139965) B47139965
theorem B7375657 : Blo 860564 7375657 := bstep (se 2 (by rfl) ⟨2765871, by rfl⟩ : syracuseStep 7375657 = 5531743) B5531743
theorem B4198073 : Blo 860564 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B20942621 : Blo 860564 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B12423131 : Blo 860564 12423131 := bstep (se 1 (by rfl) ⟨9317348, by rfl⟩ : syracuseStep 12423131 = 18634697) B18634697
theorem B2068553 : Blo 860564 2068553 := bstep (se 2 (by rfl) ⟨775707, by rfl⟩ : syracuseStep 2068553 = 1551415) B1551415
theorem B1937825 : Blo 860564 1937825 := bstep (se 2 (by rfl) ⟨726684, by rfl⟩ : syracuseStep 1937825 = 1453369) B1453369
theorem B1937951 : Blo 860564 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B3281897 : Blo 860564 3281897 := bstep (se 2 (by rfl) ⟨1230711, by rfl⟩ : syracuseStep 3281897 = 2461423) B2461423
theorem B1939355 : Blo 860564 1939355 := bstep (se 1 (by rfl) ⟨1454516, by rfl⟩ : syracuseStep 1939355 = 2909033) B2909033
theorem B2332667 : Blo 860564 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B1384859 : Blo 860564 1384859 := bstep (se 1 (by rfl) ⟨1038644, by rfl⟩ : syracuseStep 1384859 = 2077289) B2077289
theorem B860799 : Blo 860564 860799 := bstep (se 1 (by rfl) ⟨645599, by rfl⟩ : syracuseStep 860799 = 1291199) B1291199
theorem B861119 : Blo 860564 861119 := bstep (se 1 (by rfl) ⟨645839, by rfl⟩ : syracuseStep 861119 = 1291679) B1291679
theorem B4367357 : Blo 860564 4367357 := bstep (se 3 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 4367357 = 1637759) B1637759
theorem B4367519 : Blo 860564 4367519 := bstep (se 1 (by rfl) ⟨3275639, by rfl⟩ : syracuseStep 4367519 = 6551279) B6551279
theorem B861423 : Blo 860564 861423 := bstep (se 1 (by rfl) ⟨646067, by rfl⟩ : syracuseStep 861423 = 1292135) B1292135
theorem B30287209 : Blo 860564 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B9840041 : Blo 860564 9840041 := bstep (se 2 (by rfl) ⟨3690015, by rfl⟩ : syracuseStep 9840041 = 7380031) B7380031
theorem B2762171 : Blo 860564 2762171 := bstep (se 1 (by rfl) ⟨2071628, by rfl⟩ : syracuseStep 2762171 = 4143257) B4143257
theorem B861855 : Blo 860564 861855 := bstep (se 1 (by rfl) ⟨646391, by rfl⟩ : syracuseStep 861855 = 1292783) B1292783
theorem B1746859 : Blo 860564 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B2074655 : Blo 860564 2074655 := bstep (se 1 (by rfl) ⟨1555991, by rfl⟩ : syracuseStep 2074655 = 3111983) B3111983
theorem B862415 : Blo 860564 862415 := bstep (se 1 (by rfl) ⟨646811, by rfl⟩ : syracuseStep 862415 = 1293623) B1293623
theorem B4369139 : Blo 860564 4369139 := bstep (se 1 (by rfl) ⟨3276854, by rfl⟩ : syracuseStep 4369139 = 6553709) B6553709
theorem B1452863 : Blo 860564 1452863 := bstep (se 1 (by rfl) ⟨1089647, by rfl⟩ : syracuseStep 1452863 = 2179295) B2179295
theorem B1452937 : Blo 860564 1452937 := bstep (se 2 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 1452937 = 1089703) B1089703
theorem B863679 : Blo 860564 863679 := bstep (se 1 (by rfl) ⟨647759, by rfl⟩ : syracuseStep 863679 = 1295519) B1295519
theorem B7876115 : Blo 860564 7876115 := bstep (se 1 (by rfl) ⟨5907086, by rfl⟩ : syracuseStep 7876115 = 11814173) B11814173
theorem B1454719 : Blo 860564 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B1291487 : Blo 860564 1291487 := bstep (se 1 (by rfl) ⟨968615, by rfl⟩ : syracuseStep 1291487 = 1937231) B1937231
theorem B11810879 : Blo 860564 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B4372703 : Blo 860564 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B8861935 : Blo 860564 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B18692471 : Blo 860564 18692471 := bstep (se 1 (by rfl) ⟨14019353, by rfl⟩ : syracuseStep 18692471 = 28038707) B28038707
theorem B2768219 : Blo 860564 2768219 := bstep (se 1 (by rfl) ⟨2076164, by rfl⟩ : syracuseStep 2768219 = 4152329) B4152329
theorem B1293671 : Blo 860564 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B3489257 : Blo 860564 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B1294511 : Blo 860564 1294511 := bstep (se 1 (by rfl) ⟨970883, by rfl⟩ : syracuseStep 1294511 = 1941767) B1941767
theorem B1295135 : Blo 860564 1295135 := bstep (se 1 (by rfl) ⟨971351, by rfl⟩ : syracuseStep 1295135 = 1942703) B1942703
theorem B3687403 : Blo 860564 3687403 := bstep (se 1 (by rfl) ⟨2765552, by rfl⟩ : syracuseStep 3687403 = 5531105) B5531105
theorem B1295855 : Blo 860564 1295855 := bstep (se 1 (by rfl) ⟨971891, by rfl⟩ : syracuseStep 1295855 = 1943783) B1943783
theorem B1296521 : Blo 860564 1296521 := bstep (se 2 (by rfl) ⟨486195, by rfl⟩ : syracuseStep 1296521 = 972391) B972391
theorem B10471801 : Blo 860564 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B3690137 : Blo 860564 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B2904551 : Blo 860564 2904551 := bstep (se 1 (by rfl) ⟨2178413, by rfl⟩ : syracuseStep 2904551 = 4356827) B4356827
theorem B11063897 : Blo 860564 11063897 := bstep (se 2 (by rfl) ⟨4148961, by rfl⟩ : syracuseStep 11063897 = 8297923) B8297923
theorem B2904767 : Blo 860564 2904767 := bstep (se 1 (by rfl) ⟨2178575, by rfl⟩ : syracuseStep 2904767 = 4357151) B4357151
theorem B971455 : Blo 860564 971455 := bstep (se 1 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 971455 = 1457183) B1457183
theorem B7000829 : Blo 860564 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B2905577 : Blo 860564 2905577 := bstep (se 2 (by rfl) ⟨1089591, by rfl⟩ : syracuseStep 2905577 = 2179183) B2179183
theorem B4151807 : Blo 860564 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B2185967 : Blo 860564 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B3105263 : Blo 860564 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B2909465 : Blo 860564 2909465 := bstep (se 2 (by rfl) ⟨1091049, by rfl⟩ : syracuseStep 2909465 = 2182099) B2182099
theorem B6219983 : Blo 860564 6219983 := bstep (se 1 (by rfl) ⟨4664987, by rfl⟩ : syracuseStep 6219983 = 9329975) B9329975
theorem B25258655 : Blo 860564 25258655 := bstep (se 1 (by rfl) ⟨18943991, by rfl⟩ : syracuseStep 25258655 = 37887983) B37887983
theorem B2617391 : Blo 860564 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B11071687 : Blo 860564 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B1963291 : Blo 860564 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B3733613 : Blo 860564 3733613 := bstep (se 3 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 3733613 = 1400105) B1400105
theorem B19953949 : Blo 860564 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B6979709 : Blo 860564 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B4916537 : Blo 860564 4916537 := bstep (se 2 (by rfl) ⟨1843701, by rfl⟩ : syracuseStep 4916537 = 3687403) B3687403
theorem B2460091 : Blo 860564 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B13961747 : Blo 860564 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B2329145 : Blo 860564 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B1379035 : Blo 860564 1379035 := bstep (se 1 (by rfl) ⟨1034276, by rfl⟩ : syracuseStep 1379035 = 2068553) B2068553
theorem B1936367 : Blo 860564 1936367 := bstep (se 1 (by rfl) ⟨1452275, by rfl⟩ : syracuseStep 1936367 = 2904551) B2904551
theorem B7375931 : Blo 860564 7375931 := bstep (se 1 (by rfl) ⟨5531948, by rfl⟩ : syracuseStep 7375931 = 11063897) B11063897
theorem B1936511 : Blo 860564 1936511 := bstep (se 1 (by rfl) ⟨1452383, by rfl⟩ : syracuseStep 1936511 = 2904767) B2904767
theorem B13962401 : Blo 860564 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B1937051 : Blo 860564 1937051 := bstep (se 1 (by rfl) ⟨1452788, by rfl⟩ : syracuseStep 1937051 = 2905577) B2905577
theorem B9834209 : Blo 860564 9834209 := bstep (se 2 (by rfl) ⟨3687828, by rfl⟩ : syracuseStep 9834209 = 7375657) B7375657
theorem B1937249 : Blo 860564 1937249 := bstep (se 2 (by rfl) ⟨726468, by rfl⟩ : syracuseStep 1937249 = 1452937) B1452937
theorem B923239 : Blo 860564 923239 := bstep (se 1 (by rfl) ⟨692429, by rfl⟩ : syracuseStep 923239 = 1384859) B1384859
theorem B1939625 : Blo 860564 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B1939643 : Blo 860564 1939643 := bstep (se 1 (by rfl) ⟨1454732, by rfl⟩ : syracuseStep 1939643 = 2909465) B2909465
theorem B6560027 : Blo 860564 6560027 := bstep (se 1 (by rfl) ⟨4920020, by rfl⟩ : syracuseStep 6560027 = 9840041) B9840041
theorem B1841447 : Blo 860564 1841447 := bstep (se 1 (by rfl) ⟨1381085, by rfl⟩ : syracuseStep 1841447 = 2762171) B2762171
theorem B1383103 : Blo 860564 1383103 := bstep (se 1 (by rfl) ⟨1037327, by rfl⟩ : syracuseStep 1383103 = 2074655) B2074655
theorem B5250743 : Blo 860564 5250743 := bstep (se 1 (by rfl) ⟨3938057, by rfl⟩ : syracuseStep 5250743 = 7876115) B7876115
theorem B860991 : Blo 860564 860991 := bstep (se 1 (by rfl) ⟨645743, by rfl⟩ : syracuseStep 860991 = 1291487) B1291487
theorem B7873919 : Blo 860564 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B12461647 : Blo 860564 12461647 := bstep (se 1 (by rfl) ⟨9346235, by rfl⟩ : syracuseStep 12461647 = 18692471) B18692471
theorem B1845479 : Blo 860564 1845479 := bstep (se 1 (by rfl) ⟨1384109, by rfl⟩ : syracuseStep 1845479 = 2768219) B2768219
theorem B862447 : Blo 860564 862447 := bstep (se 1 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 862447 = 1293671) B1293671
theorem B863007 : Blo 860564 863007 := bstep (se 1 (by rfl) ⟨647255, by rfl⟩ : syracuseStep 863007 = 1294511) B1294511
theorem B1944431 : Blo 860564 1944431 := bstep (se 1 (by rfl) ⟨1458323, by rfl⟩ : syracuseStep 1944431 = 2916647) B2916647
theorem B863423 : Blo 860564 863423 := bstep (se 1 (by rfl) ⟨647567, by rfl⟩ : syracuseStep 863423 = 1295135) B1295135
theorem B863903 : Blo 860564 863903 := bstep (se 1 (by rfl) ⟨647927, by rfl⟩ : syracuseStep 863903 = 1295855) B1295855
theorem B14004251 : Blo 860564 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B20951095 : Blo 860564 20951095 := bstep (se 1 (by rfl) ⟨15713321, by rfl⟩ : syracuseStep 20951095 = 31426643) B31426643
theorem B864347 : Blo 860564 864347 := bstep (se 1 (by rfl) ⟨648260, by rfl⟩ : syracuseStep 864347 = 1296521) B1296521
theorem B40382945 : Blo 860564 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1291883 : Blo 860564 1291883 := bstep (se 1 (by rfl) ⟨968912, by rfl⟩ : syracuseStep 1291883 = 1937825) B1937825
theorem B1291967 : Blo 860564 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B4667219 : Blo 860564 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B1292903 : Blo 860564 1292903 := bstep (se 1 (by rfl) ⟨969677, by rfl⟩ : syracuseStep 1292903 = 1939355) B1939355
theorem B1555111 : Blo 860564 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B2767871 : Blo 860564 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B1457311 : Blo 860564 1457311 := bstep (se 1 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 1457311 = 2185967) B2185967
theorem B14762249 : Blo 860564 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B1295273 : Blo 860564 1295273 := bstep (se 2 (by rfl) ⟨485727, by rfl⟩ : syracuseStep 1295273 = 971455) B971455
theorem B4146655 : Blo 860564 4146655 := bstep (se 1 (by rfl) ⟨3109991, by rfl⟩ : syracuseStep 4146655 = 6219983) B6219983
theorem B968575 : Blo 860564 968575 := bstep (se 1 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 968575 = 1452863) B1452863
theorem B11815913 : Blo 860564 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B11194861 : Blo 860564 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B2184671 : Blo 860564 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B874747 : Blo 860564 874747 := bstep (se 1 (by rfl) ⟨656060, by rfl⟩ : syracuseStep 874747 = 1312121) B1312121
theorem B2906603 : Blo 860564 2906603 := bstep (se 1 (by rfl) ⟨2179952, by rfl⟩ : syracuseStep 2906603 = 4359905) B4359905
theorem B8280701 : Blo 860564 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B8282087 : Blo 860564 8282087 := bstep (se 1 (by rfl) ⟨6211565, by rfl⟩ : syracuseStep 8282087 = 12423131) B12423131
theorem B2187931 : Blo 860564 2187931 := bstep (se 1 (by rfl) ⟨1640948, by rfl⟩ : syracuseStep 2187931 = 3281897) B3281897
theorem B2911571 : Blo 860564 2911571 := bstep (se 1 (by rfl) ⟨2183678, by rfl⟩ : syracuseStep 2911571 = 4367357) B4367357
theorem B2911679 : Blo 860564 2911679 := bstep (se 1 (by rfl) ⟨2183759, by rfl⟩ : syracuseStep 2911679 = 4367519) B4367519
theorem B2617721 : Blo 860564 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B16839103 : Blo 860564 16839103 := bstep (se 1 (by rfl) ⟨12629327, by rfl⟩ : syracuseStep 16839103 = 25258655) B25258655
theorem B2912759 : Blo 860564 2912759 := bstep (se 1 (by rfl) ⟨2184569, by rfl⟩ : syracuseStep 2912759 = 4369139) B4369139
theorem B26605265 : Blo 860564 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B2489075 : Blo 860564 2489075 := bstep (se 1 (by rfl) ⟨1866806, by rfl⟩ : syracuseStep 2489075 = 3733613) B3733613
theorem B2915135 : Blo 860564 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B2326171 : Blo 860564 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B4653139 : Blo 860564 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B2917241 : Blo 860564 2917241 := bstep (se 2 (by rfl) ⟨1093965, by rfl⟩ : syracuseStep 2917241 = 2187931) B2187931
theorem B3277691 : Blo 860564 3277691 := bstep (se 1 (by rfl) ⟨2458268, by rfl⟩ : syracuseStep 3277691 = 4916537) B4916537
theorem B9307831 : Blo 860564 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B4917287 : Blo 860564 4917287 := bstep (se 1 (by rfl) ⟨3687965, by rfl⟩ : syracuseStep 4917287 = 7375931) B7375931
theorem B16615529 : Blo 860564 16615529 := bstep (se 2 (by rfl) ⟨6230823, by rfl⟩ : syracuseStep 16615529 = 12461647) B12461647
theorem B9308267 : Blo 860564 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B6556139 : Blo 860564 6556139 := bstep (se 1 (by rfl) ⟨4917104, by rfl⟩ : syracuseStep 6556139 = 9834209) B9834209
theorem B3280121 : Blo 860564 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B1838713 : Blo 860564 1838713 := bstep (se 2 (by rfl) ⟨689517, by rfl⟩ : syracuseStep 1838713 = 1379035) B1379035
theorem B1937735 : Blo 860564 1937735 := bstep (se 1 (by rfl) ⟨1453301, by rfl⟩ : syracuseStep 1937735 = 2906603) B2906603
theorem B22452137 : Blo 860564 22452137 := bstep (se 2 (by rfl) ⟨8419551, by rfl⟩ : syracuseStep 22452137 = 16839103) B16839103
theorem B5249279 : Blo 860564 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B1941047 : Blo 860564 1941047 := bstep (se 1 (by rfl) ⟨1455785, by rfl⟩ : syracuseStep 1941047 = 2911571) B2911571
theorem B1941119 : Blo 860564 1941119 := bstep (se 1 (by rfl) ⟨1455839, by rfl⟩ : syracuseStep 1941119 = 2911679) B2911679
theorem B7380989 : Blo 860564 7380989 := bstep (se 3 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 7380989 = 2767871) B2767871
theorem B1745147 : Blo 860564 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B1941839 : Blo 860564 1941839 := bstep (se 1 (by rfl) ⟨1456379, by rfl⟩ : syracuseStep 1941839 = 2912759) B2912759
theorem B2073481 : Blo 860564 2073481 := bstep (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) B1555111
theorem B1844137 : Blo 860564 1844137 := bstep (se 2 (by rfl) ⟨691551, by rfl⟩ : syracuseStep 1844137 = 1383103) B1383103
theorem B861255 : Blo 860564 861255 := bstep (se 1 (by rfl) ⟨645941, by rfl⟩ : syracuseStep 861255 = 1291883) B1291883
theorem B861311 : Blo 860564 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B1943081 : Blo 860564 1943081 := bstep (se 2 (by rfl) ⟨728655, by rfl⟩ : syracuseStep 1943081 = 1457311) B1457311
theorem B861935 : Blo 860564 861935 := bstep (se 1 (by rfl) ⟨646451, by rfl⟩ : syracuseStep 861935 = 1292903) B1292903
theorem B1943423 : Blo 860564 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B9841499 : Blo 860564 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B863515 : Blo 860564 863515 := bstep (se 1 (by rfl) ⟨647636, by rfl⟩ : syracuseStep 863515 = 1295273) B1295273
theorem B1552763 : Blo 860564 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B1290911 : Blo 860564 1290911 := bstep (se 1 (by rfl) ⟨968183, by rfl⟩ : syracuseStep 1290911 = 1936367) B1936367
theorem B1291007 : Blo 860564 1291007 := bstep (se 1 (by rfl) ⟨968255, by rfl⟩ : syracuseStep 1291007 = 1936511) B1936511
theorem B1291367 : Blo 860564 1291367 := bstep (se 1 (by rfl) ⟨968525, by rfl⟩ : syracuseStep 1291367 = 1937051) B1937051
theorem B1291433 : Blo 860564 1291433 := bstep (se 2 (by rfl) ⟨484287, by rfl⟩ : syracuseStep 1291433 = 968575) B968575
theorem B1291499 : Blo 860564 1291499 := bstep (se 1 (by rfl) ⟨968624, by rfl⟩ : syracuseStep 1291499 = 1937249) B1937249
theorem B1456447 : Blo 860564 1456447 := bstep (se 1 (by rfl) ⟨1092335, by rfl⟩ : syracuseStep 1456447 = 2184671) B2184671
theorem B1293083 : Blo 860564 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B1293095 : Blo 860564 1293095 := bstep (se 1 (by rfl) ⟨969821, by rfl⟩ : syracuseStep 1293095 = 1939643) B1939643
theorem B4373351 : Blo 860564 4373351 := bstep (se 1 (by rfl) ⟨3280013, by rfl⟩ : syracuseStep 4373351 = 6560027) B6560027
theorem B1227631 : Blo 860564 1227631 := bstep (se 1 (by rfl) ⟨920723, by rfl⟩ : syracuseStep 1227631 = 1841447) B1841447
theorem B5520467 : Blo 860564 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B5521391 : Blo 860564 5521391 := bstep (se 1 (by rfl) ⟨4141043, by rfl⟩ : syracuseStep 5521391 = 8282087) B8282087
theorem B27934793 : Blo 860564 27934793 := bstep (se 2 (by rfl) ⟨10475547, by rfl⟩ : syracuseStep 27934793 = 20951095) B20951095
theorem B14926481 : Blo 860564 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B1230319 : Blo 860564 1230319 := bstep (se 1 (by rfl) ⟨922739, by rfl⟩ : syracuseStep 1230319 = 1845479) B1845479
theorem B1296287 : Blo 860564 1296287 := bstep (se 1 (by rfl) ⟨972215, by rfl⟩ : syracuseStep 1296287 = 1944431) B1944431
theorem B1230985 : Blo 860564 1230985 := bstep (se 2 (by rfl) ⟨461619, by rfl⟩ : syracuseStep 1230985 = 923239) B923239
theorem B283789493 : Blo 860564 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B31509101 : Blo 860564 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B26921963 : Blo 860564 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1166329 : Blo 860564 1166329 := bstep (se 2 (by rfl) ⟨437373, by rfl⟩ : syracuseStep 1166329 = 874747) B874747
theorem B1659383 : Blo 860564 1659383 := bstep (se 1 (by rfl) ⟨1244537, by rfl⟩ : syracuseStep 1659383 = 2489075) B2489075
theorem B3101561 : Blo 860564 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B5528873 : Blo 860564 5528873 := bstep (se 2 (by rfl) ⟨2073327, by rfl⟩ : syracuseStep 5528873 = 4146655) B4146655
theorem B3500495 : Blo 860564 3500495 := bstep (se 1 (by rfl) ⟨2625371, by rfl⟩ : syracuseStep 3500495 = 5250743) B5250743
theorem B9336167 : Blo 860564 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B3111479 : Blo 860564 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B2458849 : Blo 860564 2458849 := bstep (se 2 (by rfl) ⟨922068, by rfl⟩ : syracuseStep 2458849 = 1844137) B1844137
theorem B3278191 : Blo 860564 3278191 := bstep (se 1 (by rfl) ⟨2458643, by rfl⟩ : syracuseStep 3278191 = 4917287) B4917287
theorem B11077019 : Blo 860564 11077019 := bstep (se 1 (by rfl) ⟨8307764, by rfl⟩ : syracuseStep 11077019 = 16615529) B16615529
theorem B21006067 : Blo 860564 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B1640425 : Blo 860564 1640425 := bstep (se 2 (by rfl) ⟨615159, by rfl⟩ : syracuseStep 1640425 = 1230319) B1230319
theorem B1641313 : Blo 860564 1641313 := bstep (se 2 (by rfl) ⟨615492, by rfl⟩ : syracuseStep 1641313 = 1230985) B1230985
theorem B2067707 : Blo 860564 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B4920659 : Blo 860564 4920659 := bstep (se 1 (by rfl) ⟨3690494, by rfl⟩ : syracuseStep 4920659 = 7380989) B7380989
theorem B2333663 : Blo 860564 2333663 := bstep (se 1 (by rfl) ⟨1750247, by rfl⟩ : syracuseStep 2333663 = 3500495) B3500495
theorem B6560999 : Blo 860564 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B1941929 : Blo 860564 1941929 := bstep (se 2 (by rfl) ⟨728223, by rfl⟩ : syracuseStep 1941929 = 1456447) B1456447
theorem B860607 : Blo 860564 860607 := bstep (se 1 (by rfl) ⟨645455, by rfl⟩ : syracuseStep 860607 = 1290911) B1290911
theorem B860671 : Blo 860564 860671 := bstep (se 1 (by rfl) ⟨645503, by rfl⟩ : syracuseStep 860671 = 1291007) B1291007
theorem B860911 : Blo 860564 860911 := bstep (se 1 (by rfl) ⟨645683, by rfl⟩ : syracuseStep 860911 = 1291367) B1291367
theorem B860955 : Blo 860564 860955 := bstep (se 1 (by rfl) ⟨645716, by rfl⟩ : syracuseStep 860955 = 1291433) B1291433
theorem B860999 : Blo 860564 860999 := bstep (se 1 (by rfl) ⟨645749, by rfl⟩ : syracuseStep 860999 = 1291499) B1291499
theorem B2074319 : Blo 860564 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B862055 : Blo 860564 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B862063 : Blo 860564 862063 := bstep (se 1 (by rfl) ⟨646547, by rfl⟩ : syracuseStep 862063 = 1293095) B1293095
theorem B3680311 : Blo 860564 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B3680927 : Blo 860564 3680927 := bstep (se 1 (by rfl) ⟨2760695, by rfl⟩ : syracuseStep 3680927 = 5521391) B5521391
theorem B18623195 : Blo 860564 18623195 := bstep (se 1 (by rfl) ⟨13967396, by rfl⟩ : syracuseStep 18623195 = 27934793) B27934793
theorem B6204185 : Blo 860564 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B1944827 : Blo 860564 1944827 := bstep (se 1 (by rfl) ⟨1458620, by rfl⟩ : syracuseStep 1944827 = 2917241) B2917241
theorem B864191 : Blo 860564 864191 := bstep (se 1 (by rfl) ⟨648143, by rfl⟩ : syracuseStep 864191 = 1296287) B1296287
theorem B6205511 : Blo 860564 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B4370759 : Blo 860564 4370759 := bstep (se 1 (by rfl) ⟨3278069, by rfl⟩ : syracuseStep 4370759 = 6556139) B6556139
theorem B1291823 : Blo 860564 1291823 := bstep (se 1 (by rfl) ⟨968867, by rfl⟩ : syracuseStep 1291823 = 1937735) B1937735
theorem B11058565 : Blo 860564 11058565 := bstep (se 4 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 11058565 = 2073481) B2073481
theorem B3685915 : Blo 860564 3685915 := bstep (se 1 (by rfl) ⟨2764436, by rfl⟩ : syracuseStep 3685915 = 5528873) B5528873
theorem B1294031 : Blo 860564 1294031 := bstep (se 1 (by rfl) ⟨970523, by rfl⟩ : syracuseStep 1294031 = 1941047) B1941047
theorem B1294079 : Blo 860564 1294079 := bstep (se 1 (by rfl) ⟨970559, by rfl⟩ : syracuseStep 1294079 = 1941119) B1941119
theorem B1163431 : Blo 860564 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B1294559 : Blo 860564 1294559 := bstep (se 1 (by rfl) ⟨970919, by rfl⟩ : syracuseStep 1294559 = 1941839) B1941839
theorem B1295387 : Blo 860564 1295387 := bstep (se 1 (by rfl) ⟨971540, by rfl⟩ : syracuseStep 1295387 = 1943081) B1943081
theorem B1295615 : Blo 860564 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B1035175 : Blo 860564 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B9950987 : Blo 860564 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B2185127 : Blo 860564 2185127 := bstep (se 1 (by rfl) ⟨1638845, by rfl⟩ : syracuseStep 2185127 = 3277691) B3277691
theorem B189192995 : Blo 860564 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B17947975 : Blo 860564 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B2186747 : Blo 860564 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B12410441 : Blo 860564 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B1106255 : Blo 860564 1106255 := bstep (se 1 (by rfl) ⟨829691, by rfl⟩ : syracuseStep 1106255 = 1659383) B1659383
theorem B14968091 : Blo 860564 14968091 := bstep (se 1 (by rfl) ⟨11226068, by rfl⟩ : syracuseStep 14968091 = 22452137) B22452137
theorem B3499519 : Blo 860564 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B2451617 : Blo 860564 2451617 := bstep (se 2 (by rfl) ⟨919356, by rfl⟩ : syracuseStep 2451617 = 1838713) B1838713
theorem B6220421 : Blo 860564 6220421 := bstep (se 4 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 6220421 = 1166329) B1166329
theorem B6224111 : Blo 860564 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B1636841 : Blo 860564 1636841 := bstep (se 2 (by rfl) ⟨613815, by rfl⟩ : syracuseStep 1636841 = 1227631) B1227631
theorem B2915567 : Blo 860564 2915567 := bstep (se 1 (by rfl) ⟨2186675, by rfl⟩ : syracuseStep 2915567 = 4373351) B4373351
theorem B2950013 : Blo 860564 2950013 := bstep (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) B1106255
theorem B3278465 : Blo 860564 3278465 := bstep (se 2 (by rfl) ⟨1229424, by rfl⟩ : syracuseStep 3278465 = 2458849) B2458849
theorem B1378471 : Blo 860564 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B3280439 : Blo 860564 3280439 := bstep (se 1 (by rfl) ⟨2460329, by rfl⟩ : syracuseStep 3280439 = 4920659) B4920659
theorem B1380233 : Blo 860564 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B126128663 : Blo 860564 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B1382879 : Blo 860564 1382879 := bstep (se 1 (by rfl) ⟨1037159, by rfl⟩ : syracuseStep 1382879 = 2074319) B2074319
theorem B4136123 : Blo 860564 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B4137007 : Blo 860564 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B861215 : Blo 860564 861215 := bstep (se 1 (by rfl) ⟨645911, by rfl⟩ : syracuseStep 861215 = 1291823) B1291823
theorem B1091227 : Blo 860564 1091227 := bstep (se 1 (by rfl) ⟨818420, by rfl⟩ : syracuseStep 1091227 = 1636841) B1636841
theorem B23930633 : Blo 860564 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B1943711 : Blo 860564 1943711 := bstep (se 1 (by rfl) ⟨1457783, by rfl⟩ : syracuseStep 1943711 = 2915567) B2915567
theorem B862687 : Blo 860564 862687 := bstep (se 1 (by rfl) ⟨647015, by rfl⟩ : syracuseStep 862687 = 1294031) B1294031
theorem B862719 : Blo 860564 862719 := bstep (se 1 (by rfl) ⟨647039, by rfl⟩ : syracuseStep 862719 = 1294079) B1294079
theorem B863039 : Blo 860564 863039 := bstep (se 1 (by rfl) ⟨647279, by rfl⟩ : syracuseStep 863039 = 1294559) B1294559
theorem B1551241 : Blo 860564 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B863591 : Blo 860564 863591 := bstep (se 1 (by rfl) ⟨647693, by rfl⟩ : syracuseStep 863591 = 1295387) B1295387
theorem B863743 : Blo 860564 863743 := bstep (se 1 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 863743 = 1295615) B1295615
theorem B7384679 : Blo 860564 7384679 := bstep (se 1 (by rfl) ⟨5538509, by rfl⟩ : syracuseStep 7384679 = 11077019) B11077019
theorem B4370921 : Blo 860564 4370921 := bstep (se 2 (by rfl) ⟨1639095, by rfl⟩ : syracuseStep 4370921 = 3278191) B3278191
theorem B4666025 : Blo 860564 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B6633991 : Blo 860564 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B1456751 : Blo 860564 1456751 := bstep (se 1 (by rfl) ⟨1092563, by rfl⟩ : syracuseStep 1456751 = 2185127) B2185127
theorem B1555775 : Blo 860564 1555775 := bstep (se 1 (by rfl) ⟨1166831, by rfl⟩ : syracuseStep 1555775 = 2333663) B2333663
theorem B4373999 : Blo 860564 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B1457831 : Blo 860564 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B8273627 : Blo 860564 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B1294619 : Blo 860564 1294619 := bstep (se 1 (by rfl) ⟨970964, by rfl⟩ : syracuseStep 1294619 = 1941929) B1941929
theorem B9978727 : Blo 860564 9978727 := bstep (se 1 (by rfl) ⟨7484045, by rfl⟩ : syracuseStep 9978727 = 14968091) B14968091
theorem B4146947 : Blo 860564 4146947 := bstep (se 1 (by rfl) ⟨3110210, by rfl⟩ : syracuseStep 4146947 = 6220421) B6220421
theorem B1296551 : Blo 860564 1296551 := bstep (se 1 (by rfl) ⟨972413, by rfl⟩ : syracuseStep 1296551 = 1944827) B1944827
theorem B4149407 : Blo 860564 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B28008089 : Blo 860564 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B2187233 : Blo 860564 2187233 := bstep (se 2 (by rfl) ⟨820212, by rfl⟩ : syracuseStep 2187233 = 1640425) B1640425
theorem B4907081 : Blo 860564 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B2188417 : Blo 860564 2188417 := bstep (se 2 (by rfl) ⟨820656, by rfl⟩ : syracuseStep 2188417 = 1641313) B1641313
theorem B1634411 : Blo 860564 1634411 := bstep (se 1 (by rfl) ⟨1225808, by rfl⟩ : syracuseStep 1634411 = 2451617) B2451617
theorem B2453951 : Blo 860564 2453951 := bstep (se 1 (by rfl) ⟨1840463, by rfl⟩ : syracuseStep 2453951 = 3680927) B3680927
theorem B12415463 : Blo 860564 12415463 := bstep (se 1 (by rfl) ⟨9311597, by rfl⟩ : syracuseStep 12415463 = 18623195) B18623195
theorem B2913839 : Blo 860564 2913839 := bstep (se 1 (by rfl) ⟨2185379, by rfl⟩ : syracuseStep 2913839 = 4370759) B4370759
theorem B14744753 : Blo 860564 14744753 := bstep (se 2 (by rfl) ⟨5529282, by rfl⟩ : syracuseStep 14744753 = 11058565) B11058565
theorem B4914553 : Blo 860564 4914553 := bstep (se 2 (by rfl) ⟨1842957, by rfl⟩ : syracuseStep 4914553 = 3685915) B3685915
theorem B1966675 : Blo 860564 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B13304969 : Blo 860564 13304969 := bstep (se 2 (by rfl) ⟨4989363, by rfl⟩ : syracuseStep 13304969 = 9978727) B9978727
theorem B2917889 : Blo 860564 2917889 := bstep (se 2 (by rfl) ⟨1094208, by rfl⟩ : syracuseStep 2917889 = 2188417) B2188417
theorem B920155 : Blo 860564 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B1837961 : Blo 860564 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B84085775 : Blo 860564 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B2757415 : Blo 860564 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B4923119 : Blo 860564 4923119 := bstep (se 1 (by rfl) ⟨3692339, by rfl⟩ : syracuseStep 4923119 = 7384679) B7384679
theorem B1089607 : Blo 860564 1089607 := bstep (se 1 (by rfl) ⟨817205, by rfl⟩ : syracuseStep 1089607 = 1634411) B1634411
theorem B1942559 : Blo 860564 1942559 := bstep (se 1 (by rfl) ⟨1456919, by rfl⟩ : syracuseStep 1942559 = 2913839) B2913839
theorem B5515751 : Blo 860564 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B5516009 : Blo 860564 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B863079 : Blo 860564 863079 := bstep (se 1 (by rfl) ⟨647309, by rfl⟩ : syracuseStep 863079 = 1294619) B1294619
theorem B2764631 : Blo 860564 2764631 := bstep (se 1 (by rfl) ⟨2073473, by rfl⟩ : syracuseStep 2764631 = 4146947) B4146947
theorem B864367 : Blo 860564 864367 := bstep (se 1 (by rfl) ⟨648275, by rfl⟩ : syracuseStep 864367 = 1296551) B1296551
theorem B1454969 : Blo 860564 1454969 := bstep (se 2 (by rfl) ⟨545613, by rfl⟩ : syracuseStep 1454969 = 1091227) B1091227
theorem B2766271 : Blo 860564 2766271 := bstep (se 1 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 2766271 = 4149407) B4149407
theorem B8273285 : Blo 860564 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B1458155 : Blo 860564 1458155 := bstep (se 1 (by rfl) ⟨1093616, by rfl⟩ : syracuseStep 1458155 = 2187233) B2187233
theorem B3687677 : Blo 860564 3687677 := bstep (se 3 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 3687677 = 1382879) B1382879
theorem B1295807 : Blo 860564 1295807 := bstep (se 1 (by rfl) ⟨971855, by rfl⟩ : syracuseStep 1295807 = 1943711) B1943711
theorem B8276975 : Blo 860564 8276975 := bstep (se 1 (by rfl) ⟨6207731, by rfl⟩ : syracuseStep 8276975 = 12415463) B12415463
theorem B971167 : Blo 860564 971167 := bstep (se 1 (by rfl) ⟨728375, by rfl⟩ : syracuseStep 971167 = 1456751) B1456751
theorem B1037183 : Blo 860564 1037183 := bstep (se 1 (by rfl) ⟨777887, by rfl⟩ : syracuseStep 1037183 = 1555775) B1555775
theorem B971887 : Blo 860564 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B2185643 : Blo 860564 2185643 := bstep (se 1 (by rfl) ⟨1639232, by rfl⟩ : syracuseStep 2185643 = 3278465) B3278465
theorem B12442733 : Blo 860564 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B2186959 : Blo 860564 2186959 := bstep (se 1 (by rfl) ⟨1640219, by rfl⟩ : syracuseStep 2186959 = 3280439) B3280439
theorem B18672059 : Blo 860564 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B3271387 : Blo 860564 3271387 := bstep (se 1 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 3271387 = 4907081) B4907081
theorem B15953755 : Blo 860564 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B1635967 : Blo 860564 1635967 := bstep (se 1 (by rfl) ⟨1226975, by rfl⟩ : syracuseStep 1635967 = 2453951) B2453951
theorem B2913947 : Blo 860564 2913947 := bstep (se 1 (by rfl) ⟨2185460, by rfl⟩ : syracuseStep 2913947 = 4370921) B4370921
theorem B8845321 : Blo 860564 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B6552737 : Blo 860564 6552737 := bstep (se 2 (by rfl) ⟨2457276, by rfl⟩ : syracuseStep 6552737 = 4914553) B4914553
theorem B9829835 : Blo 860564 9829835 := bstep (se 1 (by rfl) ⟨7372376, by rfl⟩ : syracuseStep 9829835 = 14744753) B14744753
theorem B2915999 : Blo 860564 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B2622233 : Blo 860564 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B2458451 : Blo 860564 2458451 := bstep (se 1 (by rfl) ⟨1843838, by rfl⟩ : syracuseStep 2458451 = 3687677) B3687677
theorem B4361849 : Blo 860564 4361849 := bstep (se 2 (by rfl) ⟨1635693, by rfl⟩ : syracuseStep 4361849 = 3271387) B3271387
theorem B8295155 : Blo 860564 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B21271673 : Blo 860564 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B3282079 : Blo 860564 3282079 := bstep (se 1 (by rfl) ⟨2461559, by rfl⟩ : syracuseStep 3282079 = 4923119) B4923119
theorem B3676553 : Blo 860564 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B3677167 : Blo 860564 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B3677339 : Blo 860564 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B1843087 : Blo 860564 1843087 := bstep (se 1 (by rfl) ⟨1382315, by rfl⟩ : syracuseStep 1843087 = 2764631) B2764631
theorem B1942631 : Blo 860564 1942631 := bstep (se 1 (by rfl) ⟨1456973, by rfl⟩ : syracuseStep 1942631 = 2913947) B2913947
theorem B4368491 : Blo 860564 4368491 := bstep (se 1 (by rfl) ⟨3276368, by rfl⟩ : syracuseStep 4368491 = 6552737) B6552737
theorem B5515523 : Blo 860564 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B1943999 : Blo 860564 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B1452809 : Blo 860564 1452809 := bstep (se 2 (by rfl) ⟨544803, by rfl⟩ : syracuseStep 1452809 = 1089607) B1089607
theorem B863871 : Blo 860564 863871 := bstep (se 1 (by rfl) ⟨647903, by rfl⟩ : syracuseStep 863871 = 1295807) B1295807
theorem B1945259 : Blo 860564 1945259 := bstep (se 1 (by rfl) ⟨1458944, by rfl⟩ : syracuseStep 1945259 = 2917889) B2917889
theorem B1225307 : Blo 860564 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B5517983 : Blo 860564 5517983 := bstep (se 1 (by rfl) ⟨4138487, by rfl⟩ : syracuseStep 5517983 = 8276975) B8276975
theorem B2765821 : Blo 860564 2765821 := bstep (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) B1037183
theorem B1226873 : Blo 860564 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B1457095 : Blo 860564 1457095 := bstep (se 1 (by rfl) ⟨1092821, by rfl⟩ : syracuseStep 1457095 = 2185643) B2185643
theorem B1294889 : Blo 860564 1294889 := bstep (se 2 (by rfl) ⟨485583, by rfl⟩ : syracuseStep 1294889 = 971167) B971167
theorem B1295039 : Blo 860564 1295039 := bstep (se 1 (by rfl) ⟨971279, by rfl⟩ : syracuseStep 1295039 = 1942559) B1942559
theorem B1295849 : Blo 860564 1295849 := bstep (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) B971887
theorem B3688361 : Blo 860564 3688361 := bstep (se 2 (by rfl) ⟨1383135, by rfl⟩ : syracuseStep 3688361 = 2766271) B2766271
theorem B2181289 : Blo 860564 2181289 := bstep (se 2 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 2181289 = 1635967) B1635967
theorem B969979 : Blo 860564 969979 := bstep (se 1 (by rfl) ⟨727484, by rfl⟩ : syracuseStep 969979 = 1454969) B1454969
theorem B972103 : Blo 860564 972103 := bstep (se 1 (by rfl) ⟨729077, by rfl⟩ : syracuseStep 972103 = 1458155) B1458155
theorem B8869979 : Blo 860564 8869979 := bstep (se 1 (by rfl) ⟨6652484, by rfl⟩ : syracuseStep 8869979 = 13304969) B13304969
theorem B56057183 : Blo 860564 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B12448039 : Blo 860564 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B11793761 : Blo 860564 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B2915945 : Blo 860564 2915945 := bstep (se 2 (by rfl) ⟨1093479, by rfl⟩ : syracuseStep 2915945 = 2186959) B2186959
theorem B6553223 : Blo 860564 6553223 := bstep (se 1 (by rfl) ⟨4914917, by rfl⟩ : syracuseStep 6553223 = 9829835) B9829835
theorem B1638967 : Blo 860564 1638967 := bstep (se 1 (by rfl) ⟨1229225, by rfl⟩ : syracuseStep 1638967 = 2458451) B2458451
theorem B2458907 : Blo 860564 2458907 := bstep (se 1 (by rfl) ⟨1844180, by rfl⟩ : syracuseStep 2458907 = 3688361) B3688361
theorem B56724461 : Blo 860564 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B3677015 : Blo 860564 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B3678655 : Blo 860564 3678655 := bstep (se 1 (by rfl) ⟨2758991, by rfl⟩ : syracuseStep 3678655 = 5517983) B5517983
theorem B1942793 : Blo 860564 1942793 := bstep (se 2 (by rfl) ⟨728547, by rfl⟩ : syracuseStep 1942793 = 1457095) B1457095
theorem B1943963 : Blo 860564 1943963 := bstep (se 1 (by rfl) ⟨1457972, by rfl⟩ : syracuseStep 1943963 = 2915945) B2915945
theorem B4368815 : Blo 860564 4368815 := bstep (se 1 (by rfl) ⟨3276611, by rfl⟩ : syracuseStep 4368815 = 6553223) B6553223
theorem B863259 : Blo 860564 863259 := bstep (se 1 (by rfl) ⟨647444, by rfl⟩ : syracuseStep 863259 = 1294889) B1294889
theorem B863359 : Blo 860564 863359 := bstep (se 1 (by rfl) ⟨647519, by rfl⟩ : syracuseStep 863359 = 1295039) B1295039
theorem B1748155 : Blo 860564 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B863899 : Blo 860564 863899 := bstep (se 1 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 863899 = 1295849) B1295849
theorem B1293305 : Blo 860564 1293305 := bstep (se 2 (by rfl) ⟨484989, by rfl⟩ : syracuseStep 1293305 = 969979) B969979
theorem B37371455 : Blo 860564 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B16597385 : Blo 860564 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B1295087 : Blo 860564 1295087 := bstep (se 1 (by rfl) ⟨971315, by rfl⟩ : syracuseStep 1295087 = 1942631) B1942631
theorem B3687761 : Blo 860564 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B4376105 : Blo 860564 4376105 := bstep (se 2 (by rfl) ⟨1641039, by rfl⟩ : syracuseStep 4376105 = 3282079) B3282079
theorem B1295999 : Blo 860564 1295999 := bstep (se 1 (by rfl) ⟨971999, by rfl⟩ : syracuseStep 1295999 = 1943999) B1943999
theorem B1296137 : Blo 860564 1296137 := bstep (se 2 (by rfl) ⟨486051, by rfl⟩ : syracuseStep 1296137 = 972103) B972103
theorem B968539 : Blo 860564 968539 := bstep (se 1 (by rfl) ⟨726404, by rfl⟩ : syracuseStep 968539 = 1452809) B1452809
theorem B1296839 : Blo 860564 1296839 := bstep (se 1 (by rfl) ⟨972629, by rfl⟩ : syracuseStep 1296839 = 1945259) B1945259
theorem B4902889 : Blo 860564 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B3267485 : Blo 860564 3267485 := bstep (se 3 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 3267485 = 1225307) B1225307
theorem B2907899 : Blo 860564 2907899 := bstep (se 1 (by rfl) ⟨2180924, by rfl⟩ : syracuseStep 2907899 = 4361849) B4361849
theorem B2908385 : Blo 860564 2908385 := bstep (se 2 (by rfl) ⟨1090644, by rfl⟩ : syracuseStep 2908385 = 2181289) B2181289
theorem B5530103 : Blo 860564 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B2451035 : Blo 860564 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B2451559 : Blo 860564 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B23653277 : Blo 860564 23653277 := bstep (se 3 (by rfl) ⟨4434989, by rfl⟩ : syracuseStep 23653277 = 8869979) B8869979
theorem B3271661 : Blo 860564 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B2912327 : Blo 860564 2912327 := bstep (se 1 (by rfl) ⟨2184245, by rfl⟩ : syracuseStep 2912327 = 4368491) B4368491
theorem B7862507 : Blo 860564 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B2457449 : Blo 860564 2457449 := bstep (se 2 (by rfl) ⟨921543, by rfl⟩ : syracuseStep 2457449 = 1843087) B1843087
theorem B1639271 : Blo 860564 1639271 := bstep (se 1 (by rfl) ⟨1229453, by rfl⟩ : syracuseStep 1639271 = 2458907) B2458907
theorem B2458507 : Blo 860564 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B2917403 : Blo 860564 2917403 := bstep (se 1 (by rfl) ⟨2188052, by rfl⟩ : syracuseStep 2917403 = 4376105) B4376105
theorem B37816307 : Blo 860564 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B2330873 : Blo 860564 2330873 := bstep (se 2 (by rfl) ⟨874077, by rfl⟩ : syracuseStep 2330873 = 1748155) B1748155
theorem B1938599 : Blo 860564 1938599 := bstep (se 1 (by rfl) ⟨1453949, by rfl⟩ : syracuseStep 1938599 = 2907899) B2907899
theorem B1938923 : Blo 860564 1938923 := bstep (se 1 (by rfl) ⟨1454192, by rfl⟩ : syracuseStep 1938923 = 2908385) B2908385
theorem B15768851 : Blo 860564 15768851 := bstep (se 1 (by rfl) ⟨11826638, by rfl⟩ : syracuseStep 15768851 = 23653277) B23653277
theorem B1941551 : Blo 860564 1941551 := bstep (se 1 (by rfl) ⟨1456163, by rfl⟩ : syracuseStep 1941551 = 2912327) B2912327
theorem B862203 : Blo 860564 862203 := bstep (se 1 (by rfl) ⟨646652, by rfl⟩ : syracuseStep 862203 = 1293305) B1293305
theorem B24914303 : Blo 860564 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B863391 : Blo 860564 863391 := bstep (se 1 (by rfl) ⟨647543, by rfl⟩ : syracuseStep 863391 = 1295087) B1295087
theorem B863999 : Blo 860564 863999 := bstep (se 1 (by rfl) ⟨647999, by rfl⟩ : syracuseStep 863999 = 1295999) B1295999
theorem B864091 : Blo 860564 864091 := bstep (se 1 (by rfl) ⟨648068, by rfl⟩ : syracuseStep 864091 = 1296137) B1296137
theorem B864559 : Blo 860564 864559 := bstep (se 1 (by rfl) ⟨648419, by rfl⟩ : syracuseStep 864559 = 1296839) B1296839
theorem B1291385 : Blo 860564 1291385 := bstep (se 2 (by rfl) ⟨484269, by rfl⟩ : syracuseStep 1291385 = 968539) B968539
theorem B2178323 : Blo 860564 2178323 := bstep (se 1 (by rfl) ⟨1633742, by rfl⟩ : syracuseStep 2178323 = 3267485) B3267485
theorem B6537185 : Blo 860564 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B3686735 : Blo 860564 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B1295195 : Blo 860564 1295195 := bstep (se 1 (by rfl) ⟨971396, by rfl⟩ : syracuseStep 1295195 = 1942793) B1942793
theorem B1295975 : Blo 860564 1295975 := bstep (se 1 (by rfl) ⟨971981, by rfl⟩ : syracuseStep 1295975 = 1943963) B1943963
theorem B2181107 : Blo 860564 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B11064923 : Blo 860564 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B4904873 : Blo 860564 4904873 := bstep (se 2 (by rfl) ⟨1839327, by rfl⟩ : syracuseStep 4904873 = 3678655) B3678655
theorem B2185289 : Blo 860564 2185289 := bstep (se 2 (by rfl) ⟨819483, by rfl⟩ : syracuseStep 2185289 = 1638967) B1638967
theorem B3268745 : Blo 860564 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B2451343 : Blo 860564 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B1634023 : Blo 860564 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B2912543 : Blo 860564 2912543 := bstep (se 1 (by rfl) ⟨2184407, by rfl⟩ : syracuseStep 2912543 = 4368815) B4368815
theorem B5241671 : Blo 860564 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B1638299 : Blo 860564 1638299 := bstep (se 1 (by rfl) ⟨1228724, by rfl⟩ : syracuseStep 1638299 = 2457449) B2457449
theorem B9831293 : Blo 860564 9831293 := bstep (se 3 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 9831293 = 3686735) B3686735
theorem B3278009 : Blo 860564 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B7376615 : Blo 860564 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B1941695 : Blo 860564 1941695 := bstep (se 1 (by rfl) ⟨1456271, by rfl⟩ : syracuseStep 1941695 = 2912543) B2912543
theorem B42050269 : Blo 860564 42050269 := bstep (se 3 (by rfl) ⟨7884425, by rfl⟩ : syracuseStep 42050269 = 15768851) B15768851
theorem B860923 : Blo 860564 860923 := bstep (se 1 (by rfl) ⟨645692, by rfl⟩ : syracuseStep 860923 = 1291385) B1291385
theorem B1452215 : Blo 860564 1452215 := bstep (se 1 (by rfl) ⟨1089161, by rfl⟩ : syracuseStep 1452215 = 2178323) B2178323
theorem B1092199 : Blo 860564 1092199 := bstep (se 1 (by rfl) ⟨819149, by rfl⟩ : syracuseStep 1092199 = 1638299) B1638299
theorem B863463 : Blo 860564 863463 := bstep (se 1 (by rfl) ⟨647597, by rfl⟩ : syracuseStep 863463 = 1295195) B1295195
theorem B1092847 : Blo 860564 1092847 := bstep (se 1 (by rfl) ⟨819635, by rfl⟩ : syracuseStep 1092847 = 1639271) B1639271
theorem B1944935 : Blo 860564 1944935 := bstep (se 1 (by rfl) ⟨1458701, by rfl⟩ : syracuseStep 1944935 = 2917403) B2917403
theorem B863983 : Blo 860564 863983 := bstep (se 1 (by rfl) ⟨647987, by rfl⟩ : syracuseStep 863983 = 1295975) B1295975
theorem B1454071 : Blo 860564 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B25210871 : Blo 860564 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1553915 : Blo 860564 1553915 := bstep (se 1 (by rfl) ⟨1165436, by rfl⟩ : syracuseStep 1553915 = 2330873) B2330873
theorem B1292399 : Blo 860564 1292399 := bstep (se 1 (by rfl) ⟨969299, by rfl⟩ : syracuseStep 1292399 = 1938599) B1938599
theorem B1292615 : Blo 860564 1292615 := bstep (se 1 (by rfl) ⟨969461, by rfl⟩ : syracuseStep 1292615 = 1938923) B1938923
theorem B1456859 : Blo 860564 1456859 := bstep (se 1 (by rfl) ⟨1092644, by rfl⟩ : syracuseStep 1456859 = 2185289) B2185289
theorem B2178697 : Blo 860564 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B1294367 : Blo 860564 1294367 := bstep (se 1 (by rfl) ⟨970775, by rfl⟩ : syracuseStep 1294367 = 1941551) B1941551
theorem B2179163 : Blo 860564 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B3494447 : Blo 860564 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B3268457 : Blo 860564 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B3269915 : Blo 860564 3269915 := bstep (se 1 (by rfl) ⟨2452436, by rfl⟩ : syracuseStep 3269915 = 4904873) B4904873
theorem B16609535 : Blo 860564 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B4358123 : Blo 860564 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B6554195 : Blo 860564 6554195 := bstep (se 1 (by rfl) ⟨4915646, by rfl⟩ : syracuseStep 6554195 = 9831293) B9831293
theorem B56067025 : Blo 860564 56067025 := bstep (se 2 (by rfl) ⟨21025134, by rfl⟩ : syracuseStep 56067025 = 42050269) B42050269
theorem B4917743 : Blo 860564 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B2329631 : Blo 860564 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B1938761 : Blo 860564 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B861599 : Blo 860564 861599 := bstep (se 1 (by rfl) ⟨646199, by rfl⟩ : syracuseStep 861599 = 1292399) B1292399
theorem B861743 : Blo 860564 861743 := bstep (se 1 (by rfl) ⟨646307, by rfl⟩ : syracuseStep 861743 = 1292615) B1292615
theorem B862911 : Blo 860564 862911 := bstep (se 1 (by rfl) ⟨647183, by rfl⟩ : syracuseStep 862911 = 1294367) B1294367
theorem B1452775 : Blo 860564 1452775 := bstep (se 1 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 1452775 = 2179163) B2179163
theorem B1456265 : Blo 860564 1456265 := bstep (se 2 (by rfl) ⟨546099, by rfl⟩ : syracuseStep 1456265 = 1092199) B1092199
theorem B4143773 : Blo 860564 4143773 := bstep (se 3 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 4143773 = 1553915) B1553915
theorem B1457129 : Blo 860564 1457129 := bstep (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) B1092847
theorem B2178971 : Blo 860564 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B1294463 : Blo 860564 1294463 := bstep (se 1 (by rfl) ⟨970847, by rfl⟩ : syracuseStep 1294463 = 1941695) B1941695
theorem B2179943 : Blo 860564 2179943 := bstep (se 1 (by rfl) ⟨1634957, by rfl⟩ : syracuseStep 2179943 = 3269915) B3269915
theorem B968143 : Blo 860564 968143 := bstep (se 1 (by rfl) ⟨726107, by rfl⟩ : syracuseStep 968143 = 1452215) B1452215
theorem B1296623 : Blo 860564 1296623 := bstep (se 1 (by rfl) ⟨972467, by rfl⟩ : syracuseStep 1296623 = 1944935) B1944935
theorem B971239 : Blo 860564 971239 := bstep (se 1 (by rfl) ⟨728429, by rfl⟩ : syracuseStep 971239 = 1456859) B1456859
theorem B2904929 : Blo 860564 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B2905415 : Blo 860564 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B2185339 : Blo 860564 2185339 := bstep (se 1 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 2185339 = 3278009) B3278009
theorem B16807247 : Blo 860564 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B11073023 : Blo 860564 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B3278495 : Blo 860564 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B1936619 : Blo 860564 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1936943 : Blo 860564 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B1937033 : Blo 860564 1937033 := bstep (se 2 (by rfl) ⟨726387, by rfl⟩ : syracuseStep 1937033 = 1452775) B1452775
theorem B7382015 : Blo 860564 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B2762515 : Blo 860564 2762515 := bstep (se 1 (by rfl) ⟨2071886, by rfl⟩ : syracuseStep 2762515 = 4143773) B4143773
theorem B1452647 : Blo 860564 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B862975 : Blo 860564 862975 := bstep (se 1 (by rfl) ⟨647231, by rfl⟩ : syracuseStep 862975 = 1294463) B1294463
theorem B4369463 : Blo 860564 4369463 := bstep (se 1 (by rfl) ⟨3277097, by rfl⟩ : syracuseStep 4369463 = 6554195) B6554195
theorem B1453295 : Blo 860564 1453295 := bstep (se 1 (by rfl) ⟨1089971, by rfl⟩ : syracuseStep 1453295 = 2179943) B2179943
theorem B74756033 : Blo 860564 74756033 := bstep (se 2 (by rfl) ⟨28033512, by rfl⟩ : syracuseStep 74756033 = 56067025) B56067025
theorem B864415 : Blo 860564 864415 := bstep (se 1 (by rfl) ⟨648311, by rfl⟩ : syracuseStep 864415 = 1296623) B1296623
theorem B1290857 : Blo 860564 1290857 := bstep (se 2 (by rfl) ⟨484071, by rfl⟩ : syracuseStep 1290857 = 968143) B968143
theorem B1553087 : Blo 860564 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B1292507 : Blo 860564 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B1294985 : Blo 860564 1294985 := bstep (se 2 (by rfl) ⟨485619, by rfl⟩ : syracuseStep 1294985 = 971239) B971239
theorem B970843 : Blo 860564 970843 := bstep (se 1 (by rfl) ⟨728132, by rfl⟩ : syracuseStep 970843 = 1456265) B1456265
theorem B971419 : Blo 860564 971419 := bstep (se 1 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 971419 = 1457129) B1457129
theorem B2913785 : Blo 860564 2913785 := bstep (se 2 (by rfl) ⟨1092669, by rfl⟩ : syracuseStep 2913785 = 2185339) B2185339
theorem B11204831 : Blo 860564 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B4921343 : Blo 860564 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B860571 : Blo 860564 860571 := bstep (se 1 (by rfl) ⟨645428, by rfl⟩ : syracuseStep 860571 = 1290857) B1290857
theorem B1942523 : Blo 860564 1942523 := bstep (se 1 (by rfl) ⟨1456892, by rfl⟩ : syracuseStep 1942523 = 2913785) B2913785
theorem B861671 : Blo 860564 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B863323 : Blo 860564 863323 := bstep (se 1 (by rfl) ⟨647492, by rfl⟩ : syracuseStep 863323 = 1294985) B1294985
theorem B1291079 : Blo 860564 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B3683353 : Blo 860564 3683353 := bstep (se 2 (by rfl) ⟨1381257, by rfl⟩ : syracuseStep 3683353 = 2762515) B2762515
theorem B1291295 : Blo 860564 1291295 := bstep (se 1 (by rfl) ⟨968471, by rfl⟩ : syracuseStep 1291295 = 1936943) B1936943
theorem B1291355 : Blo 860564 1291355 := bstep (se 1 (by rfl) ⟨968516, by rfl⟩ : syracuseStep 1291355 = 1937033) B1937033
theorem B1294457 : Blo 860564 1294457 := bstep (se 2 (by rfl) ⟨485421, by rfl⟩ : syracuseStep 1294457 = 970843) B970843
theorem B1295225 : Blo 860564 1295225 := bstep (se 2 (by rfl) ⟨485709, by rfl⟩ : syracuseStep 1295225 = 971419) B971419
theorem B968431 : Blo 860564 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B968863 : Blo 860564 968863 := bstep (se 1 (by rfl) ⟨726647, by rfl⟩ : syracuseStep 968863 = 1453295) B1453295
theorem B1035391 : Blo 860564 1035391 := bstep (se 1 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 1035391 = 1553087) B1553087
theorem B2185663 : Blo 860564 2185663 := bstep (se 1 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 2185663 = 3278495) B3278495
theorem B2912975 : Blo 860564 2912975 := bstep (se 1 (by rfl) ⟨2184731, by rfl⟩ : syracuseStep 2912975 = 4369463) B4369463
theorem B49837355 : Blo 860564 49837355 := bstep (se 1 (by rfl) ⟨37378016, by rfl⟩ : syracuseStep 49837355 = 74756033) B74756033
theorem B7469887 : Blo 860564 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B3280895 : Blo 860564 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B1380521 : Blo 860564 1380521 := bstep (se 2 (by rfl) ⟨517695, by rfl⟩ : syracuseStep 1380521 = 1035391) B1035391
theorem B1941983 : Blo 860564 1941983 := bstep (se 1 (by rfl) ⟨1456487, by rfl⟩ : syracuseStep 1941983 = 2912975) B2912975
theorem B860719 : Blo 860564 860719 := bstep (se 1 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 860719 = 1291079) B1291079
theorem B860863 : Blo 860564 860863 := bstep (se 1 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 860863 = 1291295) B1291295
theorem B860903 : Blo 860564 860903 := bstep (se 1 (by rfl) ⟨645677, by rfl⟩ : syracuseStep 860903 = 1291355) B1291355
theorem B862971 : Blo 860564 862971 := bstep (se 1 (by rfl) ⟨647228, by rfl⟩ : syracuseStep 862971 = 1294457) B1294457
theorem B863483 : Blo 860564 863483 := bstep (se 1 (by rfl) ⟨647612, by rfl⟩ : syracuseStep 863483 = 1295225) B1295225
theorem B1291241 : Blo 860564 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B1291817 : Blo 860564 1291817 := bstep (se 2 (by rfl) ⟨484431, by rfl⟩ : syracuseStep 1291817 = 968863) B968863
theorem B1295015 : Blo 860564 1295015 := bstep (se 1 (by rfl) ⟨971261, by rfl⟩ : syracuseStep 1295015 = 1942523) B1942523
theorem B4911137 : Blo 860564 4911137 := bstep (se 2 (by rfl) ⟨1841676, by rfl⟩ : syracuseStep 4911137 = 3683353) B3683353
theorem B2914217 : Blo 860564 2914217 := bstep (se 2 (by rfl) ⟨1092831, by rfl⟩ : syracuseStep 2914217 = 2185663) B2185663
theorem B33224903 : Blo 860564 33224903 := bstep (se 1 (by rfl) ⟨24918677, by rfl⟩ : syracuseStep 33224903 = 49837355) B49837355
theorem B9959849 : Blo 860564 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B860827 : Blo 860564 860827 := bstep (se 1 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 860827 = 1291241) B1291241
theorem B861211 : Blo 860564 861211 := bstep (se 1 (by rfl) ⟨645908, by rfl⟩ : syracuseStep 861211 = 1291817) B1291817
theorem B1942811 : Blo 860564 1942811 := bstep (se 1 (by rfl) ⟨1457108, by rfl⟩ : syracuseStep 1942811 = 2914217) B2914217
theorem B3681389 : Blo 860564 3681389 := bstep (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) B1380521
theorem B863343 : Blo 860564 863343 := bstep (se 1 (by rfl) ⟨647507, by rfl⟩ : syracuseStep 863343 = 1295015) B1295015
theorem B1294655 : Blo 860564 1294655 := bstep (se 1 (by rfl) ⟨970991, by rfl⟩ : syracuseStep 1294655 = 1941983) B1941983
theorem B6639899 : Blo 860564 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B2187263 : Blo 860564 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B3274091 : Blo 860564 3274091 := bstep (se 1 (by rfl) ⟨2455568, by rfl⟩ : syracuseStep 3274091 = 4911137) B4911137
theorem B22149935 : Blo 860564 22149935 := bstep (se 1 (by rfl) ⟨16612451, by rfl⟩ : syracuseStep 22149935 = 33224903) B33224903
theorem B863103 : Blo 860564 863103 := bstep (se 1 (by rfl) ⟨647327, by rfl⟩ : syracuseStep 863103 = 1294655) B1294655
theorem B17706397 : Blo 860564 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B1458175 : Blo 860564 1458175 := bstep (se 1 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 1458175 = 2187263) B2187263
theorem B1295207 : Blo 860564 1295207 := bstep (se 1 (by rfl) ⟨971405, by rfl⟩ : syracuseStep 1295207 = 1942811) B1942811
theorem B2182727 : Blo 860564 2182727 := bstep (se 1 (by rfl) ⟨1637045, by rfl⟩ : syracuseStep 2182727 = 3274091) B3274091
theorem B14766623 : Blo 860564 14766623 := bstep (se 1 (by rfl) ⟨11074967, by rfl⟩ : syracuseStep 14766623 = 22149935) B22149935
theorem B2454259 : Blo 860564 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B1944233 : Blo 860564 1944233 := bstep (se 2 (by rfl) ⟨729087, by rfl⟩ : syracuseStep 1944233 = 1458175) B1458175
theorem B863471 : Blo 860564 863471 := bstep (se 1 (by rfl) ⟨647603, by rfl⟩ : syracuseStep 863471 = 1295207) B1295207
theorem B1455151 : Blo 860564 1455151 := bstep (se 1 (by rfl) ⟨1091363, by rfl⟩ : syracuseStep 1455151 = 2182727) B2182727
theorem B9844415 : Blo 860564 9844415 := bstep (se 1 (by rfl) ⟨7383311, by rfl⟩ : syracuseStep 9844415 = 14766623) B14766623
theorem B23608529 : Blo 860564 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B3272345 : Blo 860564 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B1940201 : Blo 860564 1940201 := bstep (se 2 (by rfl) ⟨727575, by rfl⟩ : syracuseStep 1940201 = 1455151) B1455151
theorem B6562943 : Blo 860564 6562943 := bstep (se 1 (by rfl) ⟨4922207, by rfl⟩ : syracuseStep 6562943 = 9844415) B9844415
theorem B15739019 : Blo 860564 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B1296155 : Blo 860564 1296155 := bstep (se 1 (by rfl) ⟨972116, by rfl⟩ : syracuseStep 1296155 = 1944233) B1944233
theorem B2181563 : Blo 860564 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B10492679 : Blo 860564 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B864103 : Blo 860564 864103 := bstep (se 1 (by rfl) ⟨648077, by rfl⟩ : syracuseStep 864103 = 1296155) B1296155
theorem B1454375 : Blo 860564 1454375 := bstep (se 1 (by rfl) ⟨1090781, by rfl⟩ : syracuseStep 1454375 = 2181563) B2181563
theorem B1293467 : Blo 860564 1293467 := bstep (se 1 (by rfl) ⟨970100, by rfl⟩ : syracuseStep 1293467 = 1940201) B1940201
theorem B4375295 : Blo 860564 4375295 := bstep (se 1 (by rfl) ⟨3281471, by rfl⟩ : syracuseStep 4375295 = 6562943) B6562943
theorem B2916863 : Blo 860564 2916863 := bstep (se 1 (by rfl) ⟨2187647, by rfl⟩ : syracuseStep 2916863 = 4375295) B4375295
theorem B862311 : Blo 860564 862311 := bstep (se 1 (by rfl) ⟨646733, by rfl⟩ : syracuseStep 862311 = 1293467) B1293467
theorem B6995119 : Blo 860564 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B969583 : Blo 860564 969583 := bstep (se 1 (by rfl) ⟨727187, by rfl⟩ : syracuseStep 969583 = 1454375) B1454375
theorem B1944575 : Blo 860564 1944575 := bstep (se 1 (by rfl) ⟨1458431, by rfl⟩ : syracuseStep 1944575 = 2916863) B2916863
theorem B1292777 : Blo 860564 1292777 := bstep (se 2 (by rfl) ⟨484791, by rfl⟩ : syracuseStep 1292777 = 969583) B969583
theorem B9326825 : Blo 860564 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B861851 : Blo 860564 861851 := bstep (se 1 (by rfl) ⟨646388, by rfl⟩ : syracuseStep 861851 = 1292777) B1292777
theorem B1296383 : Blo 860564 1296383 := bstep (se 1 (by rfl) ⟨972287, by rfl⟩ : syracuseStep 1296383 = 1944575) B1944575
theorem B6217883 : Blo 860564 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B864255 : Blo 860564 864255 := bstep (se 1 (by rfl) ⟨648191, by rfl⟩ : syracuseStep 864255 = 1296383) B1296383
theorem B4145255 : Blo 860564 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B2763503 : Blo 860564 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1842335 : Blo 860564 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1228223 : Blo 860564 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B3275261 : Blo 860564 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2183507 : Blo 860564 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B1455671 : Blo 860564 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B970447 : Blo 860564 970447 := bstep (se 1 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 970447 = 1455671) B1455671
theorem B1293929 : Blo 860564 1293929 := bstep (se 2 (by rfl) ⟨485223, by rfl⟩ : syracuseStep 1293929 = 970447) B970447
theorem B862619 : Blo 860564 862619 := bstep (se 1 (by rfl) ⟨646964, by rfl⟩ : syracuseStep 862619 = 1293929) B1293929

theorem C0 (j : ℕ) (h1 : 215141 ≤ j) (h2 : j ≤ 215840) : Blo 860564 (4 * j + 3) := by
  interval_cases j
  · exact B860567
  · exact B860571
  · exact B860575
  · exact B860579
  · exact B860583
  · exact B860587
  · exact B860591
  · exact B860595
  · exact B860599
  · exact B860603
  · exact B860607
  · exact B860611
  · exact B860615
  · exact B860619
  · exact B860623
  · exact B860627
  · exact B860631
  · exact B860635
  · exact B860639
  · exact B860643
  · exact B860647
  · exact B860651
  · exact B860655
  · exact B860659
  · exact B860663
  · exact B860667
  · exact B860671
  · exact B860675
  · exact B860679
  · exact B860683
  · exact B860687
  · exact B860691
  · exact B860695
  · exact B860699
  · exact B860703
  · exact B860707
  · exact B860711
  · exact B860715
  · exact B860719
  · exact B860723
  · exact B860727
  · exact B860731
  · exact B860735
  · exact B860739
  · exact B860743
  · exact B860747
  · exact B860751
  · exact B860755
  · exact B860759
  · exact B860763
  · exact B860767
  · exact B860771
  · exact B860775
  · exact B860779
  · exact B860783
  · exact B860787
  · exact B860791
  · exact B860795
  · exact B860799
  · exact B860803
  · exact B860807
  · exact B860811
  · exact B860815
  · exact B860819
  · exact B860823
  · exact B860827
  · exact B860831
  · exact B860835
  · exact B860839
  · exact B860843
  · exact B860847
  · exact B860851
  · exact B860855
  · exact B860859
  · exact B860863
  · exact B860867
  · exact B860871
  · exact B860875
  · exact B860879
  · exact B860883
  · exact B860887
  · exact B860891
  · exact B860895
  · exact B860899
  · exact B860903
  · exact B860907
  · exact B860911
  · exact B860915
  · exact B860919
  · exact B860923
  · exact B860927
  · exact B860931
  · exact B860935
  · exact B860939
  · exact B860943
  · exact B860947
  · exact B860951
  · exact B860955
  · exact B860959
  · exact B860963
  · exact B860967
  · exact B860971
  · exact B860975
  · exact B860979
  · exact B860983
  · exact B860987
  · exact B860991
  · exact B860995
  · exact B860999
  · exact B861003
  · exact B861007
  · exact B861011
  · exact B861015
  · exact B861019
  · exact B861023
  · exact B861027
  · exact B861031
  · exact B861035
  · exact B861039
  · exact B861043
  · exact B861047
  · exact B861051
  · exact B861055
  · exact B861059
  · exact B861063
  · exact B861067
  · exact B861071
  · exact B861075
  · exact B861079
  · exact B861083
  · exact B861087
  · exact B861091
  · exact B861095
  · exact B861099
  · exact B861103
  · exact B861107
  · exact B861111
  · exact B861115
  · exact B861119
  · exact B861123
  · exact B861127
  · exact B861131
  · exact B861135
  · exact B861139
  · exact B861143
  · exact B861147
  · exact B861151
  · exact B861155
  · exact B861159
  · exact B861163
  · exact B861167
  · exact B861171
  · exact B861175
  · exact B861179
  · exact B861183
  · exact B861187
  · exact B861191
  · exact B861195
  · exact B861199
  · exact B861203
  · exact B861207
  · exact B861211
  · exact B861215
  · exact B861219
  · exact B861223
  · exact B861227
  · exact B861231
  · exact B861235
  · exact B861239
  · exact B861243
  · exact B861247
  · exact B861251
  · exact B861255
  · exact B861259
  · exact B861263
  · exact B861267
  · exact B861271
  · exact B861275
  · exact B861279
  · exact B861283
  · exact B861287
  · exact B861291
  · exact B861295
  · exact B861299
  · exact B861303
  · exact B861307
  · exact B861311
  · exact B861315
  · exact B861319
  · exact B861323
  · exact B861327
  · exact B861331
  · exact B861335
  · exact B861339
  · exact B861343
  · exact B861347
  · exact B861351
  · exact B861355
  · exact B861359
  · exact B861363
  · exact B861367
  · exact B861371
  · exact B861375
  · exact B861379
  · exact B861383
  · exact B861387
  · exact B861391
  · exact B861395
  · exact B861399
  · exact B861403
  · exact B861407
  · exact B861411
  · exact B861415
  · exact B861419
  · exact B861423
  · exact B861427
  · exact B861431
  · exact B861435
  · exact B861439
  · exact B861443
  · exact B861447
  · exact B861451
  · exact B861455
  · exact B861459
  · exact B861463
  · exact B861467
  · exact B861471
  · exact B861475
  · exact B861479
  · exact B861483
  · exact B861487
  · exact B861491
  · exact B861495
  · exact B861499
  · exact B861503
  · exact B861507
  · exact B861511
  · exact B861515
  · exact B861519
  · exact B861523
  · exact B861527
  · exact B861531
  · exact B861535
  · exact B861539
  · exact B861543
  · exact B861547
  · exact B861551
  · exact B861555
  · exact B861559
  · exact B861563
  · exact B861567
  · exact B861571
  · exact B861575
  · exact B861579
  · exact B861583
  · exact B861587
  · exact B861591
  · exact B861595
  · exact B861599
  · exact B861603
  · exact B861607
  · exact B861611
  · exact B861615
  · exact B861619
  · exact B861623
  · exact B861627
  · exact B861631
  · exact B861635
  · exact B861639
  · exact B861643
  · exact B861647
  · exact B861651
  · exact B861655
  · exact B861659
  · exact B861663
  · exact B861667
  · exact B861671
  · exact B861675
  · exact B861679
  · exact B861683
  · exact B861687
  · exact B861691
  · exact B861695
  · exact B861699
  · exact B861703
  · exact B861707
  · exact B861711
  · exact B861715
  · exact B861719
  · exact B861723
  · exact B861727
  · exact B861731
  · exact B861735
  · exact B861739
  · exact B861743
  · exact B861747
  · exact B861751
  · exact B861755
  · exact B861759
  · exact B861763
  · exact B861767
  · exact B861771
  · exact B861775
  · exact B861779
  · exact B861783
  · exact B861787
  · exact B861791
  · exact B861795
  · exact B861799
  · exact B861803
  · exact B861807
  · exact B861811
  · exact B861815
  · exact B861819
  · exact B861823
  · exact B861827
  · exact B861831
  · exact B861835
  · exact B861839
  · exact B861843
  · exact B861847
  · exact B861851
  · exact B861855
  · exact B861859
  · exact B861863
  · exact B861867
  · exact B861871
  · exact B861875
  · exact B861879
  · exact B861883
  · exact B861887
  · exact B861891
  · exact B861895
  · exact B861899
  · exact B861903
  · exact B861907
  · exact B861911
  · exact B861915
  · exact B861919
  · exact B861923
  · exact B861927
  · exact B861931
  · exact B861935
  · exact B861939
  · exact B861943
  · exact B861947
  · exact B861951
  · exact B861955
  · exact B861959
  · exact B861963
  · exact B861967
  · exact B861971
  · exact B861975
  · exact B861979
  · exact B861983
  · exact B861987
  · exact B861991
  · exact B861995
  · exact B861999
  · exact B862003
  · exact B862007
  · exact B862011
  · exact B862015
  · exact B862019
  · exact B862023
  · exact B862027
  · exact B862031
  · exact B862035
  · exact B862039
  · exact B862043
  · exact B862047
  · exact B862051
  · exact B862055
  · exact B862059
  · exact B862063
  · exact B862067
  · exact B862071
  · exact B862075
  · exact B862079
  · exact B862083
  · exact B862087
  · exact B862091
  · exact B862095
  · exact B862099
  · exact B862103
  · exact B862107
  · exact B862111
  · exact B862115
  · exact B862119
  · exact B862123
  · exact B862127
  · exact B862131
  · exact B862135
  · exact B862139
  · exact B862143
  · exact B862147
  · exact B862151
  · exact B862155
  · exact B862159
  · exact B862163
  · exact B862167
  · exact B862171
  · exact B862175
  · exact B862179
  · exact B862183
  · exact B862187
  · exact B862191
  · exact B862195
  · exact B862199
  · exact B862203
  · exact B862207
  · exact B862211
  · exact B862215
  · exact B862219
  · exact B862223
  · exact B862227
  · exact B862231
  · exact B862235
  · exact B862239
  · exact B862243
  · exact B862247
  · exact B862251
  · exact B862255
  · exact B862259
  · exact B862263
  · exact B862267
  · exact B862271
  · exact B862275
  · exact B862279
  · exact B862283
  · exact B862287
  · exact B862291
  · exact B862295
  · exact B862299
  · exact B862303
  · exact B862307
  · exact B862311
  · exact B862315
  · exact B862319
  · exact B862323
  · exact B862327
  · exact B862331
  · exact B862335
  · exact B862339
  · exact B862343
  · exact B862347
  · exact B862351
  · exact B862355
  · exact B862359
  · exact B862363
  · exact B862367
  · exact B862371
  · exact B862375
  · exact B862379
  · exact B862383
  · exact B862387
  · exact B862391
  · exact B862395
  · exact B862399
  · exact B862403
  · exact B862407
  · exact B862411
  · exact B862415
  · exact B862419
  · exact B862423
  · exact B862427
  · exact B862431
  · exact B862435
  · exact B862439
  · exact B862443
  · exact B862447
  · exact B862451
  · exact B862455
  · exact B862459
  · exact B862463
  · exact B862467
  · exact B862471
  · exact B862475
  · exact B862479
  · exact B862483
  · exact B862487
  · exact B862491
  · exact B862495
  · exact B862499
  · exact B862503
  · exact B862507
  · exact B862511
  · exact B862515
  · exact B862519
  · exact B862523
  · exact B862527
  · exact B862531
  · exact B862535
  · exact B862539
  · exact B862543
  · exact B862547
  · exact B862551
  · exact B862555
  · exact B862559
  · exact B862563
  · exact B862567
  · exact B862571
  · exact B862575
  · exact B862579
  · exact B862583
  · exact B862587
  · exact B862591
  · exact B862595
  · exact B862599
  · exact B862603
  · exact B862607
  · exact B862611
  · exact B862615
  · exact B862619
  · exact B862623
  · exact B862627
  · exact B862631
  · exact B862635
  · exact B862639
  · exact B862643
  · exact B862647
  · exact B862651
  · exact B862655
  · exact B862659
  · exact B862663
  · exact B862667
  · exact B862671
  · exact B862675
  · exact B862679
  · exact B862683
  · exact B862687
  · exact B862691
  · exact B862695
  · exact B862699
  · exact B862703
  · exact B862707
  · exact B862711
  · exact B862715
  · exact B862719
  · exact B862723
  · exact B862727
  · exact B862731
  · exact B862735
  · exact B862739
  · exact B862743
  · exact B862747
  · exact B862751
  · exact B862755
  · exact B862759
  · exact B862763
  · exact B862767
  · exact B862771
  · exact B862775
  · exact B862779
  · exact B862783
  · exact B862787
  · exact B862791
  · exact B862795
  · exact B862799
  · exact B862803
  · exact B862807
  · exact B862811
  · exact B862815
  · exact B862819
  · exact B862823
  · exact B862827
  · exact B862831
  · exact B862835
  · exact B862839
  · exact B862843
  · exact B862847
  · exact B862851
  · exact B862855
  · exact B862859
  · exact B862863
  · exact B862867
  · exact B862871
  · exact B862875
  · exact B862879
  · exact B862883
  · exact B862887
  · exact B862891
  · exact B862895
  · exact B862899
  · exact B862903
  · exact B862907
  · exact B862911
  · exact B862915
  · exact B862919
  · exact B862923
  · exact B862927
  · exact B862931
  · exact B862935
  · exact B862939
  · exact B862943
  · exact B862947
  · exact B862951
  · exact B862955
  · exact B862959
  · exact B862963
  · exact B862967
  · exact B862971
  · exact B862975
  · exact B862979
  · exact B862983
  · exact B862987
  · exact B862991
  · exact B862995
  · exact B862999
  · exact B863003
  · exact B863007
  · exact B863011
  · exact B863015
  · exact B863019
  · exact B863023
  · exact B863027
  · exact B863031
  · exact B863035
  · exact B863039
  · exact B863043
  · exact B863047
  · exact B863051
  · exact B863055
  · exact B863059
  · exact B863063
  · exact B863067
  · exact B863071
  · exact B863075
  · exact B863079
  · exact B863083
  · exact B863087
  · exact B863091
  · exact B863095
  · exact B863099
  · exact B863103
  · exact B863107
  · exact B863111
  · exact B863115
  · exact B863119
  · exact B863123
  · exact B863127
  · exact B863131
  · exact B863135
  · exact B863139
  · exact B863143
  · exact B863147
  · exact B863151
  · exact B863155
  · exact B863159
  · exact B863163
  · exact B863167
  · exact B863171
  · exact B863175
  · exact B863179
  · exact B863183
  · exact B863187
  · exact B863191
  · exact B863195
  · exact B863199
  · exact B863203
  · exact B863207
  · exact B863211
  · exact B863215
  · exact B863219
  · exact B863223
  · exact B863227
  · exact B863231
  · exact B863235
  · exact B863239
  · exact B863243
  · exact B863247
  · exact B863251
  · exact B863255
  · exact B863259
  · exact B863263
  · exact B863267
  · exact B863271
  · exact B863275
  · exact B863279
  · exact B863283
  · exact B863287
  · exact B863291
  · exact B863295
  · exact B863299
  · exact B863303
  · exact B863307
  · exact B863311
  · exact B863315
  · exact B863319
  · exact B863323
  · exact B863327
  · exact B863331
  · exact B863335
  · exact B863339
  · exact B863343
  · exact B863347
  · exact B863351
  · exact B863355
  · exact B863359
  · exact B863363

theorem C1 (j : ℕ) (h1 : 215841 ≤ j) (h2 : j ≤ 216140) : Blo 860564 (4 * j + 3) := by
  interval_cases j
  · exact B863367
  · exact B863371
  · exact B863375
  · exact B863379
  · exact B863383
  · exact B863387
  · exact B863391
  · exact B863395
  · exact B863399
  · exact B863403
  · exact B863407
  · exact B863411
  · exact B863415
  · exact B863419
  · exact B863423
  · exact B863427
  · exact B863431
  · exact B863435
  · exact B863439
  · exact B863443
  · exact B863447
  · exact B863451
  · exact B863455
  · exact B863459
  · exact B863463
  · exact B863467
  · exact B863471
  · exact B863475
  · exact B863479
  · exact B863483
  · exact B863487
  · exact B863491
  · exact B863495
  · exact B863499
  · exact B863503
  · exact B863507
  · exact B863511
  · exact B863515
  · exact B863519
  · exact B863523
  · exact B863527
  · exact B863531
  · exact B863535
  · exact B863539
  · exact B863543
  · exact B863547
  · exact B863551
  · exact B863555
  · exact B863559
  · exact B863563
  · exact B863567
  · exact B863571
  · exact B863575
  · exact B863579
  · exact B863583
  · exact B863587
  · exact B863591
  · exact B863595
  · exact B863599
  · exact B863603
  · exact B863607
  · exact B863611
  · exact B863615
  · exact B863619
  · exact B863623
  · exact B863627
  · exact B863631
  · exact B863635
  · exact B863639
  · exact B863643
  · exact B863647
  · exact B863651
  · exact B863655
  · exact B863659
  · exact B863663
  · exact B863667
  · exact B863671
  · exact B863675
  · exact B863679
  · exact B863683
  · exact B863687
  · exact B863691
  · exact B863695
  · exact B863699
  · exact B863703
  · exact B863707
  · exact B863711
  · exact B863715
  · exact B863719
  · exact B863723
  · exact B863727
  · exact B863731
  · exact B863735
  · exact B863739
  · exact B863743
  · exact B863747
  · exact B863751
  · exact B863755
  · exact B863759
  · exact B863763
  · exact B863767
  · exact B863771
  · exact B863775
  · exact B863779
  · exact B863783
  · exact B863787
  · exact B863791
  · exact B863795
  · exact B863799
  · exact B863803
  · exact B863807
  · exact B863811
  · exact B863815
  · exact B863819
  · exact B863823
  · exact B863827
  · exact B863831
  · exact B863835
  · exact B863839
  · exact B863843
  · exact B863847
  · exact B863851
  · exact B863855
  · exact B863859
  · exact B863863
  · exact B863867
  · exact B863871
  · exact B863875
  · exact B863879
  · exact B863883
  · exact B863887
  · exact B863891
  · exact B863895
  · exact B863899
  · exact B863903
  · exact B863907
  · exact B863911
  · exact B863915
  · exact B863919
  · exact B863923
  · exact B863927
  · exact B863931
  · exact B863935
  · exact B863939
  · exact B863943
  · exact B863947
  · exact B863951
  · exact B863955
  · exact B863959
  · exact B863963
  · exact B863967
  · exact B863971
  · exact B863975
  · exact B863979
  · exact B863983
  · exact B863987
  · exact B863991
  · exact B863995
  · exact B863999
  · exact B864003
  · exact B864007
  · exact B864011
  · exact B864015
  · exact B864019
  · exact B864023
  · exact B864027
  · exact B864031
  · exact B864035
  · exact B864039
  · exact B864043
  · exact B864047
  · exact B864051
  · exact B864055
  · exact B864059
  · exact B864063
  · exact B864067
  · exact B864071
  · exact B864075
  · exact B864079
  · exact B864083
  · exact B864087
  · exact B864091
  · exact B864095
  · exact B864099
  · exact B864103
  · exact B864107
  · exact B864111
  · exact B864115
  · exact B864119
  · exact B864123
  · exact B864127
  · exact B864131
  · exact B864135
  · exact B864139
  · exact B864143
  · exact B864147
  · exact B864151
  · exact B864155
  · exact B864159
  · exact B864163
  · exact B864167
  · exact B864171
  · exact B864175
  · exact B864179
  · exact B864183
  · exact B864187
  · exact B864191
  · exact B864195
  · exact B864199
  · exact B864203
  · exact B864207
  · exact B864211
  · exact B864215
  · exact B864219
  · exact B864223
  · exact B864227
  · exact B864231
  · exact B864235
  · exact B864239
  · exact B864243
  · exact B864247
  · exact B864251
  · exact B864255
  · exact B864259
  · exact B864263
  · exact B864267
  · exact B864271
  · exact B864275
  · exact B864279
  · exact B864283
  · exact B864287
  · exact B864291
  · exact B864295
  · exact B864299
  · exact B864303
  · exact B864307
  · exact B864311
  · exact B864315
  · exact B864319
  · exact B864323
  · exact B864327
  · exact B864331
  · exact B864335
  · exact B864339
  · exact B864343
  · exact B864347
  · exact B864351
  · exact B864355
  · exact B864359
  · exact B864363
  · exact B864367
  · exact B864371
  · exact B864375
  · exact B864379
  · exact B864383
  · exact B864387
  · exact B864391
  · exact B864395
  · exact B864399
  · exact B864403
  · exact B864407
  · exact B864411
  · exact B864415
  · exact B864419
  · exact B864423
  · exact B864427
  · exact B864431
  · exact B864435
  · exact B864439
  · exact B864443
  · exact B864447
  · exact B864451
  · exact B864455
  · exact B864459
  · exact B864463
  · exact B864467
  · exact B864471
  · exact B864475
  · exact B864479
  · exact B864483
  · exact B864487
  · exact B864491
  · exact B864495
  · exact B864499
  · exact B864503
  · exact B864507
  · exact B864511
  · exact B864515
  · exact B864519
  · exact B864523
  · exact B864527
  · exact B864531
  · exact B864535
  · exact B864539
  · exact B864543
  · exact B864547
  · exact B864551
  · exact B864555
  · exact B864559
  · exact B864563

theorem solution (m : ℕ) (hlo : 860564 ≤ m) (hhi : m ≤ 864564) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 215141 ≤ j := by omega
    have hj2 : j ≤ 216140 := by omega
    have hb : Blo 860564 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 215841 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
