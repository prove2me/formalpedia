-- Prove2me | solution 1 for syracuse_descends_range_614296_618296
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:31.746253+00:00
-- url     : https://prove2.me/submissions/6d6527b1-4763-498b-80b9-5069f4b0bbad

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


theorem B9469973 : Blo 614296 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B622945 : Blo 614296 622945 := bbase (se 2 (by rfl) ⟨233604, by rfl⟩ : syracuseStep 622945 = 467209) (by norm_num)
theorem B23658965 : Blo 614296 23658965 := bbase (se 7 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 23658965 = 554507) (by norm_num)
theorem B1409501 : Blo 614296 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B3113477 : Blo 614296 3113477 := bbase (se 4 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 3113477 = 583777) (by norm_num)
theorem B7111253 : Blo 614296 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B1606541 : Blo 614296 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B721829 : Blo 614296 721829 := bbase (se 4 (by rfl) ⟨67671, by rfl⟩ : syracuseStep 721829 = 135343) (by norm_num)
theorem B656305 : Blo 614296 656305 := bbase (se 2 (by rfl) ⟨246114, by rfl⟩ : syracuseStep 656305 = 492229) (by norm_num)
theorem B623545 : Blo 614296 623545 := bbase (se 2 (by rfl) ⟨233829, by rfl⟩ : syracuseStep 623545 = 467659) (by norm_num)
theorem B623561 : Blo 614296 623561 := bbase (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) (by norm_num)
theorem B656425 : Blo 614296 656425 := bbase (se 2 (by rfl) ⟨246159, by rfl⟩ : syracuseStep 656425 = 492319) (by norm_num)
theorem B984125 : Blo 614296 984125 := bbase (se 3 (by rfl) ⟨184523, by rfl⟩ : syracuseStep 984125 = 369047) (by norm_num)
theorem B984253 : Blo 614296 984253 := bbase (se 3 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 984253 = 369095) (by norm_num)
theorem B984317 : Blo 614296 984317 := bbase (se 3 (by rfl) ⟨184559, by rfl⟩ : syracuseStep 984317 = 369119) (by norm_num)
theorem B1312013 : Blo 614296 1312013 := bbase (se 3 (by rfl) ⟨246002, by rfl⟩ : syracuseStep 1312013 = 492005) (by norm_num)
theorem B656677 : Blo 614296 656677 := bbase (se 4 (by rfl) ⟨61563, by rfl⟩ : syracuseStep 656677 = 123127) (by norm_num)
theorem B656681 : Blo 614296 656681 := bbase (se 2 (by rfl) ⟨246255, by rfl⟩ : syracuseStep 656681 = 492511) (by norm_num)
theorem B2491813 : Blo 614296 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B624109 : Blo 614296 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B3114773 : Blo 614296 3114773 := bbase (se 6 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 3114773 = 146005) (by norm_num)
theorem B1869605 : Blo 614296 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B657245 : Blo 614296 657245 := bbase (se 3 (by rfl) ⟨123233, by rfl⟩ : syracuseStep 657245 = 246467) (by norm_num)
theorem B1312645 : Blo 614296 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B1476533 : Blo 614296 1476533 := bbase (se 5 (by rfl) ⟨69212, by rfl⟩ : syracuseStep 1476533 = 138425) (by norm_num)
theorem B657433 : Blo 614296 657433 := bbase (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) (by norm_num)
theorem B952445 : Blo 614296 952445 := bbase (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) (by norm_num)
theorem B1968533 : Blo 614296 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B985637 : Blo 614296 985637 := bbase (se 4 (by rfl) ⟨92403, by rfl⟩ : syracuseStep 985637 = 184807) (by norm_num)
theorem B789113 : Blo 614296 789113 := bbase (se 2 (by rfl) ⟨295917, by rfl⟩ : syracuseStep 789113 = 591835) (by norm_num)
theorem B625277 : Blo 614296 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B985765 : Blo 614296 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B1313533 : Blo 614296 1313533 := bbase (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) (by norm_num)
theorem B658253 : Blo 614296 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B1313653 : Blo 614296 1313653 := bbase (se 5 (by rfl) ⟨61577, by rfl⟩ : syracuseStep 1313653 = 123155) (by norm_num)
theorem B691105 : Blo 614296 691105 := bbase (se 2 (by rfl) ⟨259164, by rfl⟩ : syracuseStep 691105 = 518329) (by norm_num)
theorem B691141 : Blo 614296 691141 := bbase (se 4 (by rfl) ⟨64794, by rfl⟩ : syracuseStep 691141 = 129589) (by norm_num)
theorem B625613 : Blo 614296 625613 := bbase (se 3 (by rfl) ⟨117302, by rfl⟩ : syracuseStep 625613 = 234605) (by norm_num)
theorem B691177 : Blo 614296 691177 := bbase (se 2 (by rfl) ⟨259191, by rfl⟩ : syracuseStep 691177 = 518383) (by norm_num)
theorem B691213 : Blo 614296 691213 := bbase (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) (by norm_num)
theorem B3116069 : Blo 614296 3116069 := bbase (se 4 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 3116069 = 584263) (by norm_num)
theorem B691249 : Blo 614296 691249 := bbase (se 2 (by rfl) ⟨259218, by rfl⟩ : syracuseStep 691249 = 518437) (by norm_num)
theorem B691285 : Blo 614296 691285 := bbase (se 8 (by rfl) ⟨4050, by rfl⟩ : syracuseStep 691285 = 8101) (by norm_num)
theorem B1313909 : Blo 614296 1313909 := bbase (se 5 (by rfl) ⟨61589, by rfl⟩ : syracuseStep 1313909 = 123179) (by norm_num)
theorem B691321 : Blo 614296 691321 := bbase (se 2 (by rfl) ⟨259245, by rfl⟩ : syracuseStep 691321 = 518491) (by norm_num)
theorem B691357 : Blo 614296 691357 := bbase (se 3 (by rfl) ⟨129629, by rfl⟩ : syracuseStep 691357 = 259259) (by norm_num)
theorem B691393 : Blo 614296 691393 := bbase (se 2 (by rfl) ⟨259272, by rfl⟩ : syracuseStep 691393 = 518545) (by norm_num)
theorem B691429 : Blo 614296 691429 := bbase (se 4 (by rfl) ⟨64821, by rfl⟩ : syracuseStep 691429 = 129643) (by norm_num)
theorem B691465 : Blo 614296 691465 := bbase (se 2 (by rfl) ⟨259299, by rfl⟩ : syracuseStep 691465 = 518599) (by norm_num)
theorem B658697 : Blo 614296 658697 := bbase (se 2 (by rfl) ⟨247011, by rfl⟩ : syracuseStep 658697 = 494023) (by norm_num)
theorem B691501 : Blo 614296 691501 := bbase (se 3 (by rfl) ⟨129656, by rfl⟩ : syracuseStep 691501 = 259313) (by norm_num)
theorem B691537 : Blo 614296 691537 := bbase (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) (by norm_num)
theorem B691573 : Blo 614296 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B691609 : Blo 614296 691609 := bbase (se 2 (by rfl) ⟨259353, by rfl⟩ : syracuseStep 691609 = 518707) (by norm_num)
theorem B2035109 : Blo 614296 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B691645 : Blo 614296 691645 := bbase (se 3 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 691645 = 259367) (by norm_num)
theorem B986573 : Blo 614296 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B691681 : Blo 614296 691681 := bbase (se 2 (by rfl) ⟨259380, by rfl⟩ : syracuseStep 691681 = 518761) (by norm_num)
theorem B658945 : Blo 614296 658945 := bbase (se 2 (by rfl) ⟨247104, by rfl⟩ : syracuseStep 658945 = 494209) (by norm_num)
theorem B691717 : Blo 614296 691717 := bbase (se 4 (by rfl) ⟨64848, by rfl⟩ : syracuseStep 691717 = 129697) (by norm_num)
theorem B626185 : Blo 614296 626185 := bbase (se 2 (by rfl) ⟨234819, by rfl⟩ : syracuseStep 626185 = 469639) (by norm_num)
theorem B691753 : Blo 614296 691753 := bbase (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) (by norm_num)
theorem B1576493 : Blo 614296 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B691789 : Blo 614296 691789 := bbase (se 3 (by rfl) ⟨129710, by rfl⟩ : syracuseStep 691789 = 259421) (by norm_num)
theorem B1478245 : Blo 614296 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B691825 : Blo 614296 691825 := bbase (se 2 (by rfl) ⟨259434, by rfl⟩ : syracuseStep 691825 = 518869) (by norm_num)
theorem B691861 : Blo 614296 691861 := bbase (se 6 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 691861 = 32431) (by norm_num)
theorem B691897 : Blo 614296 691897 := bbase (se 2 (by rfl) ⟨259461, by rfl⟩ : syracuseStep 691897 = 518923) (by norm_num)
theorem B691933 : Blo 614296 691933 := bbase (se 3 (by rfl) ⟨129737, by rfl⟩ : syracuseStep 691933 = 259475) (by norm_num)
theorem B986861 : Blo 614296 986861 := bbase (se 3 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 986861 = 370073) (by norm_num)
theorem B691969 : Blo 614296 691969 := bbase (se 2 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 691969 = 518977) (by norm_num)
theorem B692005 : Blo 614296 692005 := bbase (se 4 (by rfl) ⟨64875, by rfl⟩ : syracuseStep 692005 = 129751) (by norm_num)
theorem B692041 : Blo 614296 692041 := bbase (se 2 (by rfl) ⟨259515, by rfl⟩ : syracuseStep 692041 = 519031) (by norm_num)
theorem B692077 : Blo 614296 692077 := bbase (se 3 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 692077 = 259529) (by norm_num)
theorem B921461 : Blo 614296 921461 := bbase (se 5 (by rfl) ⟨43193, by rfl⟩ : syracuseStep 921461 = 86387) (by norm_num)
theorem B921485 : Blo 614296 921485 := bbase (se 3 (by rfl) ⟨172778, by rfl⟩ : syracuseStep 921485 = 345557) (by norm_num)
theorem B692113 : Blo 614296 692113 := bbase (se 2 (by rfl) ⟨259542, by rfl⟩ : syracuseStep 692113 = 519085) (by norm_num)
theorem B921509 : Blo 614296 921509 := bbase (se 4 (by rfl) ⟨86391, by rfl⟩ : syracuseStep 921509 = 172783) (by norm_num)
theorem B659377 : Blo 614296 659377 := bbase (se 2 (by rfl) ⟨247266, by rfl⟩ : syracuseStep 659377 = 494533) (by norm_num)
theorem B692149 : Blo 614296 692149 := bbase (se 5 (by rfl) ⟨32444, by rfl⟩ : syracuseStep 692149 = 64889) (by norm_num)
theorem B921533 : Blo 614296 921533 := bbase (se 3 (by rfl) ⟨172787, by rfl⟩ : syracuseStep 921533 = 345575) (by norm_num)
theorem B921557 : Blo 614296 921557 := bbase (se 7 (by rfl) ⟨10799, by rfl⟩ : syracuseStep 921557 = 21599) (by norm_num)
theorem B692185 : Blo 614296 692185 := bbase (se 2 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 692185 = 519139) (by norm_num)
theorem B921581 : Blo 614296 921581 := bbase (se 3 (by rfl) ⟨172796, by rfl⟩ : syracuseStep 921581 = 345593) (by norm_num)
theorem B1314797 : Blo 614296 1314797 := bbase (se 3 (by rfl) ⟨246524, by rfl⟩ : syracuseStep 1314797 = 493049) (by norm_num)
theorem B659449 : Blo 614296 659449 := bbase (se 2 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 659449 = 494587) (by norm_num)
theorem B692221 : Blo 614296 692221 := bbase (se 3 (by rfl) ⟨129791, by rfl⟩ : syracuseStep 692221 = 259583) (by norm_num)
theorem B921605 : Blo 614296 921605 := bbase (se 4 (by rfl) ⟨86400, by rfl⟩ : syracuseStep 921605 = 172801) (by norm_num)
theorem B921629 : Blo 614296 921629 := bbase (se 3 (by rfl) ⟨172805, by rfl⟩ : syracuseStep 921629 = 345611) (by norm_num)
theorem B692257 : Blo 614296 692257 := bbase (se 2 (by rfl) ⟨259596, by rfl⟩ : syracuseStep 692257 = 519193) (by norm_num)
theorem B921653 : Blo 614296 921653 := bbase (se 5 (by rfl) ⟨43202, by rfl⟩ : syracuseStep 921653 = 86405) (by norm_num)
theorem B692293 : Blo 614296 692293 := bbase (se 4 (by rfl) ⟨64902, by rfl⟩ : syracuseStep 692293 = 129805) (by norm_num)
theorem B921677 : Blo 614296 921677 := bbase (se 3 (by rfl) ⟨172814, by rfl⟩ : syracuseStep 921677 = 345629) (by norm_num)
theorem B921701 : Blo 614296 921701 := bbase (se 4 (by rfl) ⟨86409, by rfl⟩ : syracuseStep 921701 = 172819) (by norm_num)
theorem B692329 : Blo 614296 692329 := bbase (se 2 (by rfl) ⟨259623, by rfl⟩ : syracuseStep 692329 = 519247) (by norm_num)
theorem B921725 : Blo 614296 921725 := bbase (se 3 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 921725 = 345647) (by norm_num)
theorem B692365 : Blo 614296 692365 := bbase (se 3 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 692365 = 259637) (by norm_num)
theorem B987277 : Blo 614296 987277 := bbase (se 3 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 987277 = 370229) (by norm_num)
theorem B921749 : Blo 614296 921749 := bbase (se 6 (by rfl) ⟨21603, by rfl⟩ : syracuseStep 921749 = 43207) (by norm_num)
theorem B921773 : Blo 614296 921773 := bbase (se 3 (by rfl) ⟨172832, by rfl⟩ : syracuseStep 921773 = 345665) (by norm_num)
theorem B692401 : Blo 614296 692401 := bbase (se 2 (by rfl) ⟨259650, by rfl⟩ : syracuseStep 692401 = 519301) (by norm_num)
theorem B921797 : Blo 614296 921797 := bbase (se 4 (by rfl) ⟨86418, by rfl⟩ : syracuseStep 921797 = 172837) (by norm_num)
theorem B1478861 : Blo 614296 1478861 := bbase (se 3 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 1478861 = 554573) (by norm_num)
theorem B692437 : Blo 614296 692437 := bbase (se 7 (by rfl) ⟨8114, by rfl⟩ : syracuseStep 692437 = 16229) (by norm_num)
theorem B921821 : Blo 614296 921821 := bbase (se 3 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 921821 = 345683) (by norm_num)
theorem B1315037 : Blo 614296 1315037 := bbase (se 3 (by rfl) ⟨246569, by rfl⟩ : syracuseStep 1315037 = 493139) (by norm_num)
theorem B921845 : Blo 614296 921845 := bbase (se 5 (by rfl) ⟨43211, by rfl⟩ : syracuseStep 921845 = 86423) (by norm_num)
theorem B692473 : Blo 614296 692473 := bbase (se 2 (by rfl) ⟨259677, by rfl⟩ : syracuseStep 692473 = 519355) (by norm_num)
theorem B921869 : Blo 614296 921869 := bbase (se 3 (by rfl) ⟨172850, by rfl⟩ : syracuseStep 921869 = 345701) (by norm_num)
theorem B1970453 : Blo 614296 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B692509 : Blo 614296 692509 := bbase (se 3 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 692509 = 259691) (by norm_num)
theorem B921893 : Blo 614296 921893 := bbase (se 4 (by rfl) ⟨86427, by rfl⟩ : syracuseStep 921893 = 172855) (by norm_num)
theorem B3117365 : Blo 614296 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B921917 : Blo 614296 921917 := bbase (se 3 (by rfl) ⟨172859, by rfl⟩ : syracuseStep 921917 = 345719) (by norm_num)
theorem B692545 : Blo 614296 692545 := bbase (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) (by norm_num)
theorem B921941 : Blo 614296 921941 := bbase (se 10 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 921941 = 2701) (by norm_num)
theorem B692581 : Blo 614296 692581 := bbase (se 4 (by rfl) ⟨64929, by rfl⟩ : syracuseStep 692581 = 129859) (by norm_num)
theorem B921965 : Blo 614296 921965 := bbase (se 3 (by rfl) ⟨172868, by rfl⟩ : syracuseStep 921965 = 345737) (by norm_num)
theorem B659821 : Blo 614296 659821 := bbase (se 3 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 659821 = 247433) (by norm_num)
theorem B3051893 : Blo 614296 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B921989 : Blo 614296 921989 := bbase (se 4 (by rfl) ⟨86436, by rfl⟩ : syracuseStep 921989 = 172873) (by norm_num)
theorem B692617 : Blo 614296 692617 := bbase (se 2 (by rfl) ⟨259731, by rfl⟩ : syracuseStep 692617 = 519463) (by norm_num)
theorem B922013 : Blo 614296 922013 := bbase (se 3 (by rfl) ⟨172877, by rfl⟩ : syracuseStep 922013 = 345755) (by norm_num)
theorem B692653 : Blo 614296 692653 := bbase (se 3 (by rfl) ⟨129872, by rfl⟩ : syracuseStep 692653 = 259745) (by norm_num)
theorem B922037 : Blo 614296 922037 := bbase (se 5 (by rfl) ⟨43220, by rfl⟩ : syracuseStep 922037 = 86441) (by norm_num)
theorem B922061 : Blo 614296 922061 := bbase (se 3 (by rfl) ⟨172886, by rfl⟩ : syracuseStep 922061 = 345773) (by norm_num)
theorem B692689 : Blo 614296 692689 := bbase (se 2 (by rfl) ⟨259758, by rfl⟩ : syracuseStep 692689 = 519517) (by norm_num)
theorem B922085 : Blo 614296 922085 := bbase (se 4 (by rfl) ⟨86445, by rfl⟩ : syracuseStep 922085 = 172891) (by norm_num)
theorem B692725 : Blo 614296 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B3510773 : Blo 614296 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B922109 : Blo 614296 922109 := bbase (se 3 (by rfl) ⟨172895, by rfl⟩ : syracuseStep 922109 = 345791) (by norm_num)
theorem B922133 : Blo 614296 922133 := bbase (se 6 (by rfl) ⟨21612, by rfl⟩ : syracuseStep 922133 = 43225) (by norm_num)
theorem B692761 : Blo 614296 692761 := bbase (se 2 (by rfl) ⟨259785, by rfl⟩ : syracuseStep 692761 = 519571) (by norm_num)
theorem B922157 : Blo 614296 922157 := bbase (se 3 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 922157 = 345809) (by norm_num)
theorem B692797 : Blo 614296 692797 := bbase (se 3 (by rfl) ⟨129899, by rfl⟩ : syracuseStep 692797 = 259799) (by norm_num)
theorem B922181 : Blo 614296 922181 := bbase (se 4 (by rfl) ⟨86454, by rfl⟩ : syracuseStep 922181 = 172909) (by norm_num)
theorem B922205 : Blo 614296 922205 := bbase (se 3 (by rfl) ⟨172913, by rfl⟩ : syracuseStep 922205 = 345827) (by norm_num)
theorem B692833 : Blo 614296 692833 := bbase (se 2 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 692833 = 519625) (by norm_num)
theorem B922229 : Blo 614296 922229 := bbase (se 5 (by rfl) ⟨43229, by rfl⟩ : syracuseStep 922229 = 86459) (by norm_num)
theorem B5345909 : Blo 614296 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B1479293 : Blo 614296 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B692869 : Blo 614296 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B922253 : Blo 614296 922253 := bbase (se 3 (by rfl) ⟨172922, by rfl⟩ : syracuseStep 922253 = 345845) (by norm_num)
theorem B922277 : Blo 614296 922277 := bbase (se 4 (by rfl) ⟨86463, by rfl⟩ : syracuseStep 922277 = 172927) (by norm_num)
theorem B692905 : Blo 614296 692905 := bbase (se 2 (by rfl) ⟨259839, by rfl⟩ : syracuseStep 692905 = 519679) (by norm_num)
theorem B922301 : Blo 614296 922301 := bbase (se 3 (by rfl) ⟨172931, by rfl⟩ : syracuseStep 922301 = 345863) (by norm_num)
theorem B692941 : Blo 614296 692941 := bbase (se 3 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 692941 = 259853) (by norm_num)
theorem B922325 : Blo 614296 922325 := bbase (se 7 (by rfl) ⟨10808, by rfl⟩ : syracuseStep 922325 = 21617) (by norm_num)
theorem B1315541 : Blo 614296 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B1577693 : Blo 614296 1577693 := bbase (se 3 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 1577693 = 591635) (by norm_num)
theorem B1315549 : Blo 614296 1315549 := bbase (se 3 (by rfl) ⟨246665, by rfl⟩ : syracuseStep 1315549 = 493331) (by norm_num)
theorem B660197 : Blo 614296 660197 := bbase (se 4 (by rfl) ⟨61893, by rfl⟩ : syracuseStep 660197 = 123787) (by norm_num)
theorem B922349 : Blo 614296 922349 := bbase (se 3 (by rfl) ⟨172940, by rfl⟩ : syracuseStep 922349 = 345881) (by norm_num)
theorem B692977 : Blo 614296 692977 := bbase (se 2 (by rfl) ⟨259866, by rfl⟩ : syracuseStep 692977 = 519733) (by norm_num)
theorem B922373 : Blo 614296 922373 := bbase (se 4 (by rfl) ⟨86472, by rfl⟩ : syracuseStep 922373 = 172945) (by norm_num)
theorem B693013 : Blo 614296 693013 := bbase (se 6 (by rfl) ⟨16242, by rfl⟩ : syracuseStep 693013 = 32485) (by norm_num)
theorem B922397 : Blo 614296 922397 := bbase (se 3 (by rfl) ⟨172949, by rfl⟩ : syracuseStep 922397 = 345899) (by norm_num)
theorem B922421 : Blo 614296 922421 := bbase (se 5 (by rfl) ⟨43238, by rfl⟩ : syracuseStep 922421 = 86477) (by norm_num)
theorem B693049 : Blo 614296 693049 := bbase (se 2 (by rfl) ⟨259893, by rfl⟩ : syracuseStep 693049 = 519787) (by norm_num)
theorem B922445 : Blo 614296 922445 := bbase (se 3 (by rfl) ⟨172958, by rfl⟩ : syracuseStep 922445 = 345917) (by norm_num)
theorem B693085 : Blo 614296 693085 := bbase (se 3 (by rfl) ⟨129953, by rfl⟩ : syracuseStep 693085 = 259907) (by norm_num)
theorem B922469 : Blo 614296 922469 := bbase (se 4 (by rfl) ⟨86481, by rfl⟩ : syracuseStep 922469 = 172963) (by norm_num)
theorem B922493 : Blo 614296 922493 := bbase (se 3 (by rfl) ⟨172967, by rfl⟩ : syracuseStep 922493 = 345935) (by norm_num)
theorem B693121 : Blo 614296 693121 := bbase (se 2 (by rfl) ⟨259920, by rfl⟩ : syracuseStep 693121 = 519841) (by norm_num)
theorem B922517 : Blo 614296 922517 := bbase (se 6 (by rfl) ⟨21621, by rfl⟩ : syracuseStep 922517 = 43243) (by norm_num)
theorem B693157 : Blo 614296 693157 := bbase (se 4 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 693157 = 129967) (by norm_num)
theorem B922541 : Blo 614296 922541 := bbase (se 3 (by rfl) ⟨172976, by rfl⟩ : syracuseStep 922541 = 345953) (by norm_num)
theorem B1250237 : Blo 614296 1250237 := bbase (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) (by norm_num)
theorem B922565 : Blo 614296 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B693193 : Blo 614296 693193 := bbase (se 2 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 693193 = 519895) (by norm_num)
theorem B922589 : Blo 614296 922589 := bbase (se 3 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 922589 = 345971) (by norm_num)
theorem B693229 : Blo 614296 693229 := bbase (se 3 (by rfl) ⟨129980, by rfl⟩ : syracuseStep 693229 = 259961) (by norm_num)
theorem B922613 : Blo 614296 922613 := bbase (se 5 (by rfl) ⟨43247, by rfl⟩ : syracuseStep 922613 = 86495) (by norm_num)
theorem B922637 : Blo 614296 922637 := bbase (se 3 (by rfl) ⟨172994, by rfl⟩ : syracuseStep 922637 = 345989) (by norm_num)
theorem B693265 : Blo 614296 693265 := bbase (se 2 (by rfl) ⟨259974, by rfl⟩ : syracuseStep 693265 = 519949) (by norm_num)
theorem B922661 : Blo 614296 922661 := bbase (se 4 (by rfl) ⟨86499, by rfl⟩ : syracuseStep 922661 = 172999) (by norm_num)
theorem B693301 : Blo 614296 693301 := bbase (se 5 (by rfl) ⟨32498, by rfl⟩ : syracuseStep 693301 = 64997) (by norm_num)
theorem B988213 : Blo 614296 988213 := bbase (se 5 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 988213 = 92645) (by norm_num)
theorem B922685 : Blo 614296 922685 := bbase (se 3 (by rfl) ⟨173003, by rfl⟩ : syracuseStep 922685 = 346007) (by norm_num)
theorem B922709 : Blo 614296 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B693337 : Blo 614296 693337 := bbase (se 2 (by rfl) ⟨260001, by rfl⟩ : syracuseStep 693337 = 520003) (by norm_num)
theorem B922733 : Blo 614296 922733 := bbase (se 3 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 922733 = 346025) (by norm_num)
theorem B693373 : Blo 614296 693373 := bbase (se 3 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 693373 = 260015) (by norm_num)
theorem B922757 : Blo 614296 922757 := bbase (se 4 (by rfl) ⟨86508, by rfl⟩ : syracuseStep 922757 = 173017) (by norm_num)
theorem B922781 : Blo 614296 922781 := bbase (se 3 (by rfl) ⟨173021, by rfl⟩ : syracuseStep 922781 = 346043) (by norm_num)
theorem B693409 : Blo 614296 693409 := bbase (se 2 (by rfl) ⟨260028, by rfl⟩ : syracuseStep 693409 = 520057) (by norm_num)
theorem B922805 : Blo 614296 922805 := bbase (se 5 (by rfl) ⟨43256, by rfl⟩ : syracuseStep 922805 = 86513) (by norm_num)
theorem B693445 : Blo 614296 693445 := bbase (se 4 (by rfl) ⟨65010, by rfl⟩ : syracuseStep 693445 = 130021) (by norm_num)
theorem B922829 : Blo 614296 922829 := bbase (se 3 (by rfl) ⟨173030, by rfl⟩ : syracuseStep 922829 = 346061) (by norm_num)
theorem B922853 : Blo 614296 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B693481 : Blo 614296 693481 := bbase (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) (by norm_num)
theorem B922877 : Blo 614296 922877 := bbase (se 3 (by rfl) ⟨173039, by rfl⟩ : syracuseStep 922877 = 346079) (by norm_num)
theorem B693517 : Blo 614296 693517 := bbase (se 3 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 693517 = 260069) (by norm_num)
theorem B922901 : Blo 614296 922901 := bbase (se 6 (by rfl) ⟨21630, by rfl⟩ : syracuseStep 922901 = 43261) (by norm_num)
theorem B922925 : Blo 614296 922925 := bbase (se 3 (by rfl) ⟨173048, by rfl⟩ : syracuseStep 922925 = 346097) (by norm_num)
theorem B693553 : Blo 614296 693553 := bbase (se 2 (by rfl) ⟨260082, by rfl⟩ : syracuseStep 693553 = 520165) (by norm_num)
theorem B922949 : Blo 614296 922949 := bbase (se 4 (by rfl) ⟨86526, by rfl⟩ : syracuseStep 922949 = 173053) (by norm_num)
theorem B693589 : Blo 614296 693589 := bbase (se 14 (by rfl) ⟨63, by rfl⟩ : syracuseStep 693589 = 127) (by norm_num)
theorem B922973 : Blo 614296 922973 := bbase (se 3 (by rfl) ⟨173057, by rfl⟩ : syracuseStep 922973 = 346115) (by norm_num)
theorem B791905 : Blo 614296 791905 := bbase (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) (by norm_num)
theorem B922997 : Blo 614296 922997 := bbase (se 5 (by rfl) ⟨43265, by rfl⟩ : syracuseStep 922997 = 86531) (by norm_num)
theorem B693625 : Blo 614296 693625 := bbase (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) (by norm_num)
theorem B923021 : Blo 614296 923021 := bbase (se 3 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 923021 = 346133) (by norm_num)
theorem B693661 : Blo 614296 693661 := bbase (se 3 (by rfl) ⟨130061, by rfl⟩ : syracuseStep 693661 = 260123) (by norm_num)
theorem B923045 : Blo 614296 923045 := bbase (se 4 (by rfl) ⟨86535, by rfl⟩ : syracuseStep 923045 = 173071) (by norm_num)
theorem B923069 : Blo 614296 923069 := bbase (se 3 (by rfl) ⟨173075, by rfl⟩ : syracuseStep 923069 = 346151) (by norm_num)
theorem B693697 : Blo 614296 693697 := bbase (se 2 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 693697 = 520273) (by norm_num)
theorem B923093 : Blo 614296 923093 := bbase (se 7 (by rfl) ⟨10817, by rfl⟩ : syracuseStep 923093 = 21635) (by norm_num)
theorem B693733 : Blo 614296 693733 := bbase (se 4 (by rfl) ⟨65037, by rfl⟩ : syracuseStep 693733 = 130075) (by norm_num)
theorem B923117 : Blo 614296 923117 := bbase (se 3 (by rfl) ⟨173084, by rfl⟩ : syracuseStep 923117 = 346169) (by norm_num)
theorem B1054205 : Blo 614296 1054205 := bbase (se 3 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 1054205 = 395327) (by norm_num)
theorem B923141 : Blo 614296 923141 := bbase (se 4 (by rfl) ⟨86544, by rfl⟩ : syracuseStep 923141 = 173089) (by norm_num)
theorem B693769 : Blo 614296 693769 := bbase (se 2 (by rfl) ⟨260163, by rfl⟩ : syracuseStep 693769 = 520327) (by norm_num)
theorem B923165 : Blo 614296 923165 := bbase (se 3 (by rfl) ⟨173093, by rfl⟩ : syracuseStep 923165 = 346187) (by norm_num)
theorem B693805 : Blo 614296 693805 := bbase (se 3 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 693805 = 260177) (by norm_num)
theorem B923189 : Blo 614296 923189 := bbase (se 5 (by rfl) ⟨43274, by rfl⟩ : syracuseStep 923189 = 86549) (by norm_num)
theorem B3118661 : Blo 614296 3118661 := bbase (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) (by norm_num)
theorem B923213 : Blo 614296 923213 := bbase (se 3 (by rfl) ⟨173102, by rfl⟩ : syracuseStep 923213 = 346205) (by norm_num)
theorem B693841 : Blo 614296 693841 := bbase (se 2 (by rfl) ⟨260190, by rfl⟩ : syracuseStep 693841 = 520381) (by norm_num)
theorem B923237 : Blo 614296 923237 := bbase (se 4 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 923237 = 173107) (by norm_num)
theorem B693877 : Blo 614296 693877 := bbase (se 5 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 693877 = 65051) (by norm_num)
theorem B923261 : Blo 614296 923261 := bbase (se 3 (by rfl) ⟨173111, by rfl⟩ : syracuseStep 923261 = 346223) (by norm_num)
theorem B923285 : Blo 614296 923285 := bbase (se 6 (by rfl) ⟨21639, by rfl⟩ : syracuseStep 923285 = 43279) (by norm_num)
theorem B3511957 : Blo 614296 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B693913 : Blo 614296 693913 := bbase (se 2 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 693913 = 520435) (by norm_num)
theorem B1971877 : Blo 614296 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B923309 : Blo 614296 923309 := bbase (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) (by norm_num)
theorem B693949 : Blo 614296 693949 := bbase (se 3 (by rfl) ⟨130115, by rfl⟩ : syracuseStep 693949 = 260231) (by norm_num)
theorem B923333 : Blo 614296 923333 := bbase (se 4 (by rfl) ⟨86562, by rfl⟩ : syracuseStep 923333 = 173125) (by norm_num)
theorem B923357 : Blo 614296 923357 := bbase (se 3 (by rfl) ⟨173129, by rfl⟩ : syracuseStep 923357 = 346259) (by norm_num)
theorem B693985 : Blo 614296 693985 := bbase (se 2 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 693985 = 520489) (by norm_num)
theorem B923381 : Blo 614296 923381 := bbase (se 5 (by rfl) ⟨43283, by rfl⟩ : syracuseStep 923381 = 86567) (by norm_num)
theorem B5936885 : Blo 614296 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B2332421 : Blo 614296 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B694021 : Blo 614296 694021 := bbase (se 4 (by rfl) ⟨65064, by rfl⟩ : syracuseStep 694021 = 130129) (by norm_num)
theorem B923405 : Blo 614296 923405 := bbase (se 3 (by rfl) ⟨173138, by rfl⟩ : syracuseStep 923405 = 346277) (by norm_num)
theorem B923429 : Blo 614296 923429 := bbase (se 4 (by rfl) ⟨86571, by rfl⟩ : syracuseStep 923429 = 173143) (by norm_num)
theorem B694057 : Blo 614296 694057 := bbase (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) (by norm_num)
theorem B1480493 : Blo 614296 1480493 := bbase (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) (by norm_num)
theorem B923453 : Blo 614296 923453 := bbase (se 3 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 923453 = 346295) (by norm_num)
theorem B1316677 : Blo 614296 1316677 := bbase (se 4 (by rfl) ⟨123438, by rfl⟩ : syracuseStep 1316677 = 246877) (by norm_num)
theorem B694093 : Blo 614296 694093 := bbase (se 3 (by rfl) ⟨130142, by rfl⟩ : syracuseStep 694093 = 260285) (by norm_num)
theorem B923477 : Blo 614296 923477 := bbase (se 9 (by rfl) ⟨2705, by rfl⟩ : syracuseStep 923477 = 5411) (by norm_num)
theorem B1382237 : Blo 614296 1382237 := bbase (se 3 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 1382237 = 518339) (by norm_num)
theorem B923501 : Blo 614296 923501 := bbase (se 3 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 923501 = 346313) (by norm_num)
theorem B694129 : Blo 614296 694129 := bbase (se 2 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 694129 = 520597) (by norm_num)
theorem B923525 : Blo 614296 923525 := bbase (se 4 (by rfl) ⟨86580, by rfl⟩ : syracuseStep 923525 = 173161) (by norm_num)
theorem B2627477 : Blo 614296 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B694165 : Blo 614296 694165 := bbase (se 6 (by rfl) ⟨16269, by rfl⟩ : syracuseStep 694165 = 32539) (by norm_num)
theorem B923549 : Blo 614296 923549 := bbase (se 3 (by rfl) ⟨173165, by rfl⟩ : syracuseStep 923549 = 346331) (by norm_num)
theorem B1382309 : Blo 614296 1382309 := bbase (se 4 (by rfl) ⟨129591, by rfl⟩ : syracuseStep 1382309 = 259183) (by norm_num)
theorem B4986805 : Blo 614296 4986805 := bbase (se 5 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 4986805 = 467513) (by norm_num)
theorem B923573 : Blo 614296 923573 := bbase (se 5 (by rfl) ⟨43292, by rfl⟩ : syracuseStep 923573 = 86585) (by norm_num)
theorem B694201 : Blo 614296 694201 := bbase (se 2 (by rfl) ⟨260325, by rfl⟩ : syracuseStep 694201 = 520651) (by norm_num)
theorem B923597 : Blo 614296 923597 := bbase (se 3 (by rfl) ⟨173174, by rfl⟩ : syracuseStep 923597 = 346349) (by norm_num)
theorem B694237 : Blo 614296 694237 := bbase (se 3 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 694237 = 260339) (by norm_num)
theorem B923621 : Blo 614296 923621 := bbase (se 4 (by rfl) ⟨86589, by rfl⟩ : syracuseStep 923621 = 173179) (by norm_num)
theorem B1382381 : Blo 614296 1382381 := bbase (se 3 (by rfl) ⟨259196, by rfl⟩ : syracuseStep 1382381 = 518393) (by norm_num)
theorem B923645 : Blo 614296 923645 := bbase (se 3 (by rfl) ⟨173183, by rfl⟩ : syracuseStep 923645 = 346367) (by norm_num)
theorem B694273 : Blo 614296 694273 := bbase (se 2 (by rfl) ⟨260352, by rfl⟩ : syracuseStep 694273 = 520705) (by norm_num)
theorem B2103317 : Blo 614296 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B923669 : Blo 614296 923669 := bbase (se 6 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 923669 = 43297) (by norm_num)
theorem B694309 : Blo 614296 694309 := bbase (se 4 (by rfl) ⟨65091, by rfl⟩ : syracuseStep 694309 = 130183) (by norm_num)
theorem B2332709 : Blo 614296 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B923693 : Blo 614296 923693 := bbase (se 3 (by rfl) ⟨173192, by rfl⟩ : syracuseStep 923693 = 346385) (by norm_num)
theorem B1382453 : Blo 614296 1382453 := bbase (se 5 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 1382453 = 129605) (by norm_num)
theorem B923717 : Blo 614296 923717 := bbase (se 4 (by rfl) ⟨86598, by rfl⟩ : syracuseStep 923717 = 173197) (by norm_num)
theorem B694345 : Blo 614296 694345 := bbase (se 2 (by rfl) ⟨260379, by rfl⟩ : syracuseStep 694345 = 520759) (by norm_num)
theorem B923741 : Blo 614296 923741 := bbase (se 3 (by rfl) ⟨173201, by rfl⟩ : syracuseStep 923741 = 346403) (by norm_num)
theorem B1972325 : Blo 614296 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B694381 : Blo 614296 694381 := bbase (se 3 (by rfl) ⟨130196, by rfl⟩ : syracuseStep 694381 = 260393) (by norm_num)
theorem B792685 : Blo 614296 792685 := bbase (se 3 (by rfl) ⟨148628, by rfl⟩ : syracuseStep 792685 = 297257) (by norm_num)
theorem B923765 : Blo 614296 923765 := bbase (se 5 (by rfl) ⟨43301, by rfl⟩ : syracuseStep 923765 = 86603) (by norm_num)
theorem B1382525 : Blo 614296 1382525 := bbase (se 3 (by rfl) ⟨259223, by rfl⟩ : syracuseStep 1382525 = 518447) (by norm_num)
theorem B923789 : Blo 614296 923789 := bbase (se 3 (by rfl) ⟨173210, by rfl⟩ : syracuseStep 923789 = 346421) (by norm_num)
theorem B694417 : Blo 614296 694417 := bbase (se 2 (by rfl) ⟨260406, by rfl⟩ : syracuseStep 694417 = 520813) (by norm_num)
theorem B923813 : Blo 614296 923813 := bbase (se 4 (by rfl) ⟨86607, by rfl⟩ : syracuseStep 923813 = 173215) (by norm_num)
theorem B694453 : Blo 614296 694453 := bbase (se 5 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 694453 = 65105) (by norm_num)
theorem B923837 : Blo 614296 923837 := bbase (se 3 (by rfl) ⟨173219, by rfl⟩ : syracuseStep 923837 = 346439) (by norm_num)
theorem B1317053 : Blo 614296 1317053 := bbase (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) (by norm_num)
theorem B1382597 : Blo 614296 1382597 := bbase (se 4 (by rfl) ⟨129618, by rfl⟩ : syracuseStep 1382597 = 259237) (by norm_num)
theorem B923861 : Blo 614296 923861 := bbase (se 7 (by rfl) ⟨10826, by rfl⟩ : syracuseStep 923861 = 21653) (by norm_num)
theorem B694489 : Blo 614296 694489 := bbase (se 2 (by rfl) ⟨260433, by rfl⟩ : syracuseStep 694489 = 520867) (by norm_num)
theorem B989405 : Blo 614296 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B923885 : Blo 614296 923885 := bbase (se 3 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 923885 = 346457) (by norm_num)
theorem B694525 : Blo 614296 694525 := bbase (se 3 (by rfl) ⟨130223, by rfl⟩ : syracuseStep 694525 = 260447) (by norm_num)
theorem B923909 : Blo 614296 923909 := bbase (se 4 (by rfl) ⟨86616, by rfl⟩ : syracuseStep 923909 = 173233) (by norm_num)
theorem B1382669 : Blo 614296 1382669 := bbase (se 3 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 1382669 = 518501) (by norm_num)
theorem B923933 : Blo 614296 923933 := bbase (se 3 (by rfl) ⟨173237, by rfl⟩ : syracuseStep 923933 = 346475) (by norm_num)
theorem B694561 : Blo 614296 694561 := bbase (se 2 (by rfl) ⟨260460, by rfl⟩ : syracuseStep 694561 = 520921) (by norm_num)
theorem B923957 : Blo 614296 923957 := bbase (se 5 (by rfl) ⟨43310, by rfl⟩ : syracuseStep 923957 = 86621) (by norm_num)
theorem B694597 : Blo 614296 694597 := bbase (se 4 (by rfl) ⟨65118, by rfl⟩ : syracuseStep 694597 = 130237) (by norm_num)
theorem B923981 : Blo 614296 923981 := bbase (se 3 (by rfl) ⟨173246, by rfl⟩ : syracuseStep 923981 = 346493) (by norm_num)
theorem B1382741 : Blo 614296 1382741 := bbase (se 10 (by rfl) ⟨2025, by rfl⟩ : syracuseStep 1382741 = 4051) (by norm_num)
theorem B924005 : Blo 614296 924005 := bbase (se 4 (by rfl) ⟨86625, by rfl⟩ : syracuseStep 924005 = 173251) (by norm_num)
theorem B694633 : Blo 614296 694633 := bbase (se 2 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 694633 = 520975) (by norm_num)
theorem B924029 : Blo 614296 924029 := bbase (se 3 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 924029 = 346511) (by norm_num)
theorem B694669 : Blo 614296 694669 := bbase (se 3 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 694669 = 260501) (by norm_num)
theorem B924053 : Blo 614296 924053 := bbase (se 6 (by rfl) ⟨21657, by rfl⟩ : syracuseStep 924053 = 43315) (by norm_num)
theorem B1382813 : Blo 614296 1382813 := bbase (se 3 (by rfl) ⟨259277, by rfl⟩ : syracuseStep 1382813 = 518555) (by norm_num)
theorem B989597 : Blo 614296 989597 := bbase (se 3 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 989597 = 371099) (by norm_num)
theorem B2365861 : Blo 614296 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B924077 : Blo 614296 924077 := bbase (se 3 (by rfl) ⟨173264, by rfl⟩ : syracuseStep 924077 = 346529) (by norm_num)
theorem B694705 : Blo 614296 694705 := bbase (se 2 (by rfl) ⟨260514, by rfl⟩ : syracuseStep 694705 = 521029) (by norm_num)
theorem B924101 : Blo 614296 924101 := bbase (se 4 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 924101 = 173269) (by norm_num)
theorem B694741 : Blo 614296 694741 := bbase (se 7 (by rfl) ⟨8141, by rfl⟩ : syracuseStep 694741 = 16283) (by norm_num)
theorem B924125 : Blo 614296 924125 := bbase (se 3 (by rfl) ⟨173273, by rfl⟩ : syracuseStep 924125 = 346547) (by norm_num)
theorem B1382885 : Blo 614296 1382885 := bbase (se 4 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 1382885 = 259291) (by norm_num)
theorem B924149 : Blo 614296 924149 := bbase (se 5 (by rfl) ⟨43319, by rfl⟩ : syracuseStep 924149 = 86639) (by norm_num)
theorem B694777 : Blo 614296 694777 := bbase (se 2 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 694777 = 521083) (by norm_num)
theorem B924173 : Blo 614296 924173 := bbase (se 3 (by rfl) ⟨173282, by rfl⟩ : syracuseStep 924173 = 346565) (by norm_num)
theorem B694813 : Blo 614296 694813 := bbase (se 3 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 694813 = 260555) (by norm_num)
theorem B924197 : Blo 614296 924197 := bbase (se 4 (by rfl) ⟨86643, by rfl⟩ : syracuseStep 924197 = 173287) (by norm_num)
theorem B1382957 : Blo 614296 1382957 := bbase (se 3 (by rfl) ⟨259304, by rfl⟩ : syracuseStep 1382957 = 518609) (by norm_num)
theorem B924221 : Blo 614296 924221 := bbase (se 3 (by rfl) ⟨173291, by rfl⟩ : syracuseStep 924221 = 346583) (by norm_num)
theorem B694849 : Blo 614296 694849 := bbase (se 2 (by rfl) ⟨260568, by rfl⟩ : syracuseStep 694849 = 521137) (by norm_num)
theorem B924245 : Blo 614296 924245 := bbase (se 8 (by rfl) ⟨5415, by rfl⟩ : syracuseStep 924245 = 10831) (by norm_num)
theorem B1186397 : Blo 614296 1186397 := bbase (se 3 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 1186397 = 444899) (by norm_num)
theorem B694885 : Blo 614296 694885 := bbase (se 4 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 694885 = 130291) (by norm_num)
theorem B924269 : Blo 614296 924269 := bbase (se 3 (by rfl) ⟨173300, by rfl⟩ : syracuseStep 924269 = 346601) (by norm_num)
theorem B1383029 : Blo 614296 1383029 := bbase (se 5 (by rfl) ⟨64829, by rfl⟩ : syracuseStep 1383029 = 129659) (by norm_num)
theorem B924293 : Blo 614296 924293 := bbase (se 4 (by rfl) ⟨86652, by rfl⟩ : syracuseStep 924293 = 173305) (by norm_num)
theorem B694921 : Blo 614296 694921 := bbase (se 2 (by rfl) ⟨260595, by rfl⟩ : syracuseStep 694921 = 521191) (by norm_num)
theorem B924317 : Blo 614296 924317 := bbase (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) (by norm_num)
theorem B694957 : Blo 614296 694957 := bbase (se 3 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 694957 = 260609) (by norm_num)
theorem B924341 : Blo 614296 924341 := bbase (se 5 (by rfl) ⟨43328, by rfl⟩ : syracuseStep 924341 = 86657) (by norm_num)
theorem B1383101 : Blo 614296 1383101 := bbase (se 3 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 1383101 = 518663) (by norm_num)
theorem B924365 : Blo 614296 924365 := bbase (se 3 (by rfl) ⟨173318, by rfl⟩ : syracuseStep 924365 = 346637) (by norm_num)
theorem B694993 : Blo 614296 694993 := bbase (se 2 (by rfl) ⟨260622, by rfl⟩ : syracuseStep 694993 = 521245) (by norm_num)
theorem B924389 : Blo 614296 924389 := bbase (se 4 (by rfl) ⟨86661, by rfl⟩ : syracuseStep 924389 = 173323) (by norm_num)
theorem B695029 : Blo 614296 695029 := bbase (se 5 (by rfl) ⟨32579, by rfl⟩ : syracuseStep 695029 = 65159) (by norm_num)
theorem B924413 : Blo 614296 924413 := bbase (se 3 (by rfl) ⟨173327, by rfl⟩ : syracuseStep 924413 = 346655) (by norm_num)
theorem B1383173 : Blo 614296 1383173 := bbase (se 4 (by rfl) ⟨129672, by rfl⟩ : syracuseStep 1383173 = 259345) (by norm_num)
theorem B924437 : Blo 614296 924437 := bbase (se 6 (by rfl) ⟨21666, by rfl⟩ : syracuseStep 924437 = 43333) (by norm_num)
theorem B695065 : Blo 614296 695065 := bbase (se 2 (by rfl) ⟨260649, by rfl⟩ : syracuseStep 695065 = 521299) (by norm_num)
theorem B924461 : Blo 614296 924461 := bbase (se 3 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 924461 = 346673) (by norm_num)
theorem B695101 : Blo 614296 695101 := bbase (se 3 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 695101 = 260663) (by norm_num)
theorem B924485 : Blo 614296 924485 := bbase (se 4 (by rfl) ⟨86670, by rfl⟩ : syracuseStep 924485 = 173341) (by norm_num)
theorem B1383245 : Blo 614296 1383245 := bbase (se 3 (by rfl) ⟨259358, by rfl⟩ : syracuseStep 1383245 = 518717) (by norm_num)
theorem B3119957 : Blo 614296 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B924509 : Blo 614296 924509 := bbase (se 3 (by rfl) ⟨173345, by rfl⟩ : syracuseStep 924509 = 346691) (by norm_num)
theorem B695137 : Blo 614296 695137 := bbase (se 2 (by rfl) ⟨260676, by rfl⟩ : syracuseStep 695137 = 521353) (by norm_num)
theorem B924533 : Blo 614296 924533 := bbase (se 5 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 924533 = 86675) (by norm_num)
theorem B695173 : Blo 614296 695173 := bbase (se 4 (by rfl) ⟨65172, by rfl⟩ : syracuseStep 695173 = 130345) (by norm_num)
theorem B924557 : Blo 614296 924557 := bbase (se 3 (by rfl) ⟨173354, by rfl⟩ : syracuseStep 924557 = 346709) (by norm_num)
theorem B1383317 : Blo 614296 1383317 := bbase (se 6 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 1383317 = 64843) (by norm_num)
theorem B924581 : Blo 614296 924581 := bbase (se 4 (by rfl) ⟨86679, by rfl⟩ : syracuseStep 924581 = 173359) (by norm_num)
theorem B695209 : Blo 614296 695209 := bbase (se 2 (by rfl) ⟨260703, by rfl⟩ : syracuseStep 695209 = 521407) (by norm_num)
theorem B924605 : Blo 614296 924605 := bbase (se 3 (by rfl) ⟨173363, by rfl⟩ : syracuseStep 924605 = 346727) (by norm_num)
theorem B3152837 : Blo 614296 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B695245 : Blo 614296 695245 := bbase (se 3 (by rfl) ⟨130358, by rfl⟩ : syracuseStep 695245 = 260717) (by norm_num)
theorem B924629 : Blo 614296 924629 := bbase (se 7 (by rfl) ⟨10835, by rfl⟩ : syracuseStep 924629 = 21671) (by norm_num)
theorem B1383389 : Blo 614296 1383389 := bbase (se 3 (by rfl) ⟨259385, by rfl⟩ : syracuseStep 1383389 = 518771) (by norm_num)
theorem B1874917 : Blo 614296 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B924653 : Blo 614296 924653 := bbase (se 3 (by rfl) ⟨173372, by rfl⟩ : syracuseStep 924653 = 346745) (by norm_num)
theorem B695281 : Blo 614296 695281 := bbase (se 2 (by rfl) ⟨260730, by rfl⟩ : syracuseStep 695281 = 521461) (by norm_num)
theorem B2956277 : Blo 614296 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B924677 : Blo 614296 924677 := bbase (se 4 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 924677 = 173377) (by norm_num)
theorem B695317 : Blo 614296 695317 := bbase (se 6 (by rfl) ⟨16296, by rfl⟩ : syracuseStep 695317 = 32593) (by norm_num)
theorem B924701 : Blo 614296 924701 := bbase (se 3 (by rfl) ⟨173381, by rfl⟩ : syracuseStep 924701 = 346763) (by norm_num)
theorem B1383461 : Blo 614296 1383461 := bbase (se 4 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 1383461 = 259399) (by norm_num)
theorem B924725 : Blo 614296 924725 := bbase (se 5 (by rfl) ⟨43346, by rfl⟩ : syracuseStep 924725 = 86693) (by norm_num)
theorem B695353 : Blo 614296 695353 := bbase (se 2 (by rfl) ⟨260757, by rfl⟩ : syracuseStep 695353 = 521515) (by norm_num)
theorem B924749 : Blo 614296 924749 := bbase (se 3 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 924749 = 346781) (by norm_num)
theorem B695389 : Blo 614296 695389 := bbase (se 3 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 695389 = 260771) (by norm_num)
theorem B924773 : Blo 614296 924773 := bbase (se 4 (by rfl) ⟨86697, by rfl⟩ : syracuseStep 924773 = 173395) (by norm_num)
theorem B1383533 : Blo 614296 1383533 := bbase (se 3 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 1383533 = 518825) (by norm_num)
theorem B924797 : Blo 614296 924797 := bbase (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) (by norm_num)
theorem B695425 : Blo 614296 695425 := bbase (se 2 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 695425 = 521569) (by norm_num)
theorem B924821 : Blo 614296 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B695461 : Blo 614296 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B924845 : Blo 614296 924845 := bbase (se 3 (by rfl) ⟨173408, by rfl⟩ : syracuseStep 924845 = 346817) (by norm_num)
theorem B1383605 : Blo 614296 1383605 := bbase (se 5 (by rfl) ⟨64856, by rfl⟩ : syracuseStep 1383605 = 129713) (by norm_num)
theorem B2333893 : Blo 614296 2333893 := bbase (se 4 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 2333893 = 437605) (by norm_num)
theorem B924869 : Blo 614296 924869 := bbase (se 4 (by rfl) ⟨86706, by rfl⟩ : syracuseStep 924869 = 173413) (by norm_num)
theorem B695497 : Blo 614296 695497 := bbase (se 2 (by rfl) ⟨260811, by rfl⟩ : syracuseStep 695497 = 521623) (by norm_num)
theorem B924893 : Blo 614296 924893 := bbase (se 3 (by rfl) ⟨173417, by rfl⟩ : syracuseStep 924893 = 346835) (by norm_num)
theorem B695533 : Blo 614296 695533 := bbase (se 3 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 695533 = 260825) (by norm_num)
theorem B924917 : Blo 614296 924917 := bbase (se 5 (by rfl) ⟨43355, by rfl⟩ : syracuseStep 924917 = 86711) (by norm_num)
theorem B1383677 : Blo 614296 1383677 := bbase (se 3 (by rfl) ⟨259439, by rfl⟩ : syracuseStep 1383677 = 518879) (by norm_num)
theorem B924941 : Blo 614296 924941 := bbase (se 3 (by rfl) ⟨173426, by rfl⟩ : syracuseStep 924941 = 346853) (by norm_num)
theorem B695569 : Blo 614296 695569 := bbase (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) (by norm_num)
theorem B924965 : Blo 614296 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B4693301 : Blo 614296 4693301 := bbase (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) (by norm_num)
theorem B924989 : Blo 614296 924989 := bbase (se 3 (by rfl) ⟨173435, by rfl⟩ : syracuseStep 924989 = 346871) (by norm_num)
theorem B1383749 : Blo 614296 1383749 := bbase (se 4 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 1383749 = 259453) (by norm_num)
theorem B925013 : Blo 614296 925013 := bbase (se 11 (by rfl) ⟨677, by rfl⟩ : syracuseStep 925013 = 1355) (by norm_num)
theorem B925037 : Blo 614296 925037 := bbase (se 3 (by rfl) ⟨173444, by rfl⟩ : syracuseStep 925037 = 346889) (by norm_num)
theorem B925061 : Blo 614296 925061 := bbase (se 4 (by rfl) ⟨86724, by rfl⟩ : syracuseStep 925061 = 173449) (by norm_num)
theorem B1383821 : Blo 614296 1383821 := bbase (se 3 (by rfl) ⟨259466, by rfl⟩ : syracuseStep 1383821 = 518933) (by norm_num)
theorem B925085 : Blo 614296 925085 := bbase (se 3 (by rfl) ⟨173453, by rfl⟩ : syracuseStep 925085 = 346907) (by norm_num)
theorem B925109 : Blo 614296 925109 := bbase (se 5 (by rfl) ⟨43364, by rfl⟩ : syracuseStep 925109 = 86729) (by norm_num)
theorem B925133 : Blo 614296 925133 := bbase (se 3 (by rfl) ⟨173462, by rfl⟩ : syracuseStep 925133 = 346925) (by norm_num)
theorem B1383893 : Blo 614296 1383893 := bbase (se 7 (by rfl) ⟨16217, by rfl⟩ : syracuseStep 1383893 = 32435) (by norm_num)
theorem B925157 : Blo 614296 925157 := bbase (se 4 (by rfl) ⟨86733, by rfl⟩ : syracuseStep 925157 = 173467) (by norm_num)
theorem B2334197 : Blo 614296 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B925181 : Blo 614296 925181 := bbase (se 3 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 925181 = 346943) (by norm_num)
theorem B925205 : Blo 614296 925205 := bbase (se 6 (by rfl) ⟨21684, by rfl⟩ : syracuseStep 925205 = 43369) (by norm_num)
theorem B1383965 : Blo 614296 1383965 := bbase (se 3 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 1383965 = 518987) (by norm_num)
theorem B925229 : Blo 614296 925229 := bbase (se 3 (by rfl) ⟨173480, by rfl⟩ : syracuseStep 925229 = 346961) (by norm_num)
theorem B925253 : Blo 614296 925253 := bbase (se 4 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 925253 = 173485) (by norm_num)
theorem B3513941 : Blo 614296 3513941 := bbase (se 8 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 3513941 = 41179) (by norm_num)
theorem B925277 : Blo 614296 925277 := bbase (se 3 (by rfl) ⟨173489, by rfl⟩ : syracuseStep 925277 = 346979) (by norm_num)
theorem B1384037 : Blo 614296 1384037 := bbase (se 4 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 1384037 = 259507) (by norm_num)
theorem B925301 : Blo 614296 925301 := bbase (se 5 (by rfl) ⟨43373, by rfl⟩ : syracuseStep 925301 = 86747) (by norm_num)
theorem B2629253 : Blo 614296 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B925325 : Blo 614296 925325 := bbase (se 3 (by rfl) ⟨173498, by rfl⟩ : syracuseStep 925325 = 346997) (by norm_num)
theorem B925349 : Blo 614296 925349 := bbase (se 4 (by rfl) ⟨86751, by rfl⟩ : syracuseStep 925349 = 173503) (by norm_num)
theorem B1384109 : Blo 614296 1384109 := bbase (se 3 (by rfl) ⟨259520, by rfl⟩ : syracuseStep 1384109 = 519041) (by norm_num)
theorem B925373 : Blo 614296 925373 := bbase (se 3 (by rfl) ⟨173507, by rfl⟩ : syracuseStep 925373 = 347015) (by norm_num)
theorem B925397 : Blo 614296 925397 := bbase (se 7 (by rfl) ⟨10844, by rfl⟩ : syracuseStep 925397 = 21689) (by norm_num)
theorem B925421 : Blo 614296 925421 := bbase (se 3 (by rfl) ⟨173516, by rfl⟩ : syracuseStep 925421 = 347033) (by norm_num)
theorem B1384181 : Blo 614296 1384181 := bbase (se 5 (by rfl) ⟨64883, by rfl⟩ : syracuseStep 1384181 = 129767) (by norm_num)
theorem B925445 : Blo 614296 925445 := bbase (se 4 (by rfl) ⟨86760, by rfl⟩ : syracuseStep 925445 = 173521) (by norm_num)
theorem B925469 : Blo 614296 925469 := bbase (se 3 (by rfl) ⟨173525, by rfl⟩ : syracuseStep 925469 = 347051) (by norm_num)
theorem B1318693 : Blo 614296 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B925493 : Blo 614296 925493 := bbase (se 5 (by rfl) ⟨43382, by rfl⟩ : syracuseStep 925493 = 86765) (by norm_num)
theorem B1384253 : Blo 614296 1384253 := bbase (se 3 (by rfl) ⟨259547, by rfl⟩ : syracuseStep 1384253 = 519095) (by norm_num)
theorem B925517 : Blo 614296 925517 := bbase (se 3 (by rfl) ⟨173534, by rfl⟩ : syracuseStep 925517 = 347069) (by norm_num)
theorem B925541 : Blo 614296 925541 := bbase (se 4 (by rfl) ⟨86769, by rfl⟩ : syracuseStep 925541 = 173539) (by norm_num)
theorem B2629493 : Blo 614296 2629493 := bbase (se 5 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 2629493 = 246515) (by norm_num)
theorem B925565 : Blo 614296 925565 := bbase (se 3 (by rfl) ⟨173543, by rfl⟩ : syracuseStep 925565 = 347087) (by norm_num)
theorem B1384325 : Blo 614296 1384325 := bbase (se 4 (by rfl) ⟨129780, by rfl⟩ : syracuseStep 1384325 = 259561) (by norm_num)
theorem B925589 : Blo 614296 925589 := bbase (se 6 (by rfl) ⟨21693, by rfl⟩ : syracuseStep 925589 = 43387) (by norm_num)
theorem B925613 : Blo 614296 925613 := bbase (se 3 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 925613 = 347105) (by norm_num)
theorem B925637 : Blo 614296 925637 := bbase (se 4 (by rfl) ⟨86778, by rfl⟩ : syracuseStep 925637 = 173557) (by norm_num)
theorem B1384397 : Blo 614296 1384397 := bbase (se 3 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 1384397 = 519149) (by norm_num)
theorem B925661 : Blo 614296 925661 := bbase (se 3 (by rfl) ⟨173561, by rfl⟩ : syracuseStep 925661 = 347123) (by norm_num)
theorem B925685 : Blo 614296 925685 := bbase (se 5 (by rfl) ⟨43391, by rfl⟩ : syracuseStep 925685 = 86783) (by norm_num)
theorem B925709 : Blo 614296 925709 := bbase (se 3 (by rfl) ⟨173570, by rfl⟩ : syracuseStep 925709 = 347141) (by norm_num)
theorem B1384469 : Blo 614296 1384469 := bbase (se 6 (by rfl) ⟨32448, by rfl⟩ : syracuseStep 1384469 = 64897) (by norm_num)
theorem B1482781 : Blo 614296 1482781 := bbase (se 3 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 1482781 = 556043) (by norm_num)
theorem B925733 : Blo 614296 925733 := bbase (se 4 (by rfl) ⟨86787, by rfl⟩ : syracuseStep 925733 = 173575) (by norm_num)
theorem B925757 : Blo 614296 925757 := bbase (se 3 (by rfl) ⟨173579, by rfl⟩ : syracuseStep 925757 = 347159) (by norm_num)
theorem B925781 : Blo 614296 925781 := bbase (se 8 (by rfl) ⟨5424, by rfl⟩ : syracuseStep 925781 = 10849) (by norm_num)
theorem B1384541 : Blo 614296 1384541 := bbase (se 3 (by rfl) ⟨259601, by rfl⟩ : syracuseStep 1384541 = 519203) (by norm_num)
theorem B3121253 : Blo 614296 3121253 := bbase (se 4 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 3121253 = 585235) (by norm_num)
theorem B925805 : Blo 614296 925805 := bbase (se 3 (by rfl) ⟨173588, by rfl⟩ : syracuseStep 925805 = 347177) (by norm_num)
theorem B1482877 : Blo 614296 1482877 := bbase (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) (by norm_num)
theorem B925829 : Blo 614296 925829 := bbase (se 4 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 925829 = 173593) (by norm_num)
theorem B925853 : Blo 614296 925853 := bbase (se 3 (by rfl) ⟨173597, by rfl⟩ : syracuseStep 925853 = 347195) (by norm_num)
theorem B1384613 : Blo 614296 1384613 := bbase (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) (by norm_num)
theorem B925877 : Blo 614296 925877 := bbase (se 5 (by rfl) ⟨43400, by rfl⟩ : syracuseStep 925877 = 86801) (by norm_num)
theorem B925901 : Blo 614296 925901 := bbase (se 3 (by rfl) ⟨173606, by rfl⟩ : syracuseStep 925901 = 347213) (by norm_num)
theorem B925925 : Blo 614296 925925 := bbase (se 4 (by rfl) ⟨86805, by rfl⟩ : syracuseStep 925925 = 173611) (by norm_num)
theorem B1384685 : Blo 614296 1384685 := bbase (se 3 (by rfl) ⟨259628, by rfl⟩ : syracuseStep 1384685 = 519257) (by norm_num)
theorem B925949 : Blo 614296 925949 := bbase (se 3 (by rfl) ⟨173615, by rfl⟩ : syracuseStep 925949 = 347231) (by norm_num)
theorem B925973 : Blo 614296 925973 := bbase (se 6 (by rfl) ⟨21702, by rfl⟩ : syracuseStep 925973 = 43405) (by norm_num)
theorem B925997 : Blo 614296 925997 := bbase (se 3 (by rfl) ⟨173624, by rfl⟩ : syracuseStep 925997 = 347249) (by norm_num)
theorem B1384757 : Blo 614296 1384757 := bbase (se 5 (by rfl) ⟨64910, by rfl⟩ : syracuseStep 1384757 = 129821) (by norm_num)
theorem B1974581 : Blo 614296 1974581 := bbase (se 5 (by rfl) ⟨92558, by rfl⟩ : syracuseStep 1974581 = 185117) (by norm_num)
theorem B1483069 : Blo 614296 1483069 := bbase (se 3 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 1483069 = 556151) (by norm_num)
theorem B926021 : Blo 614296 926021 := bbase (se 4 (by rfl) ⟨86814, by rfl⟩ : syracuseStep 926021 = 173629) (by norm_num)
theorem B926045 : Blo 614296 926045 := bbase (se 3 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 926045 = 347267) (by norm_num)
theorem B926069 : Blo 614296 926069 := bbase (se 5 (by rfl) ⟨43409, by rfl⟩ : syracuseStep 926069 = 86819) (by norm_num)
theorem B1384829 : Blo 614296 1384829 := bbase (se 3 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 1384829 = 519311) (by norm_num)
theorem B926093 : Blo 614296 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B926117 : Blo 614296 926117 := bbase (se 4 (by rfl) ⟨86823, by rfl⟩ : syracuseStep 926117 = 173647) (by norm_num)
theorem B926141 : Blo 614296 926141 := bbase (se 3 (by rfl) ⟨173651, by rfl⟩ : syracuseStep 926141 = 347303) (by norm_num)
theorem B1384901 : Blo 614296 1384901 := bbase (se 4 (by rfl) ⟨129834, by rfl⟩ : syracuseStep 1384901 = 259669) (by norm_num)
theorem B926165 : Blo 614296 926165 := bbase (se 7 (by rfl) ⟨10853, by rfl⟩ : syracuseStep 926165 = 21707) (by norm_num)
theorem B1122797 : Blo 614296 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B926189 : Blo 614296 926189 := bbase (se 3 (by rfl) ⟨173660, by rfl⟩ : syracuseStep 926189 = 347321) (by norm_num)
theorem B926213 : Blo 614296 926213 := bbase (se 4 (by rfl) ⟨86832, by rfl⟩ : syracuseStep 926213 = 173665) (by norm_num)
theorem B1384973 : Blo 614296 1384973 := bbase (se 3 (by rfl) ⟨259682, by rfl⟩ : syracuseStep 1384973 = 519365) (by norm_num)
theorem B926237 : Blo 614296 926237 := bbase (se 3 (by rfl) ⟨173669, by rfl⟩ : syracuseStep 926237 = 347339) (by norm_num)
theorem B926261 : Blo 614296 926261 := bbase (se 5 (by rfl) ⟨43418, by rfl⟩ : syracuseStep 926261 = 86837) (by norm_num)
theorem B926285 : Blo 614296 926285 := bbase (se 3 (by rfl) ⟨173678, by rfl⟩ : syracuseStep 926285 = 347357) (by norm_num)
theorem B1385045 : Blo 614296 1385045 := bbase (se 8 (by rfl) ⟨8115, by rfl⟩ : syracuseStep 1385045 = 16231) (by norm_num)
theorem B926309 : Blo 614296 926309 := bbase (se 4 (by rfl) ⟨86841, by rfl⟩ : syracuseStep 926309 = 173683) (by norm_num)
theorem B926333 : Blo 614296 926333 := bbase (se 3 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 926333 = 347375) (by norm_num)
theorem B1483397 : Blo 614296 1483397 := bbase (se 4 (by rfl) ⟨139068, by rfl⟩ : syracuseStep 1483397 = 278137) (by norm_num)
theorem B926357 : Blo 614296 926357 := bbase (se 6 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 926357 = 43423) (by norm_num)
theorem B1385117 : Blo 614296 1385117 := bbase (se 3 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 1385117 = 519419) (by norm_num)
theorem B1319581 : Blo 614296 1319581 := bbase (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) (by norm_num)
theorem B926381 : Blo 614296 926381 := bbase (se 3 (by rfl) ⟨173696, by rfl⟩ : syracuseStep 926381 = 347393) (by norm_num)
theorem B926405 : Blo 614296 926405 := bbase (se 4 (by rfl) ⟨86850, by rfl⟩ : syracuseStep 926405 = 173701) (by norm_num)
theorem B926429 : Blo 614296 926429 := bbase (se 3 (by rfl) ⟨173705, by rfl⟩ : syracuseStep 926429 = 347411) (by norm_num)
theorem B1385189 : Blo 614296 1385189 := bbase (se 4 (by rfl) ⟨129861, by rfl⟩ : syracuseStep 1385189 = 259723) (by norm_num)
theorem B926453 : Blo 614296 926453 := bbase (se 5 (by rfl) ⟨43427, by rfl⟩ : syracuseStep 926453 = 86855) (by norm_num)
theorem B926477 : Blo 614296 926477 := bbase (se 3 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 926477 = 347429) (by norm_num)
theorem B926501 : Blo 614296 926501 := bbase (se 4 (by rfl) ⟨86859, by rfl⟩ : syracuseStep 926501 = 173719) (by norm_num)
theorem B1385261 : Blo 614296 1385261 := bbase (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) (by norm_num)
theorem B926525 : Blo 614296 926525 := bbase (se 3 (by rfl) ⟨173723, by rfl⟩ : syracuseStep 926525 = 347447) (by norm_num)
theorem B926549 : Blo 614296 926549 := bbase (se 9 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 926549 = 5429) (by norm_num)
theorem B926573 : Blo 614296 926573 := bbase (se 3 (by rfl) ⟨173732, by rfl⟩ : syracuseStep 926573 = 347465) (by norm_num)
theorem B1385333 : Blo 614296 1385333 := bbase (se 5 (by rfl) ⟨64937, by rfl⟩ : syracuseStep 1385333 = 129875) (by norm_num)
theorem B926597 : Blo 614296 926597 := bbase (se 4 (by rfl) ⟨86868, by rfl⟩ : syracuseStep 926597 = 173737) (by norm_num)
theorem B926621 : Blo 614296 926621 := bbase (se 3 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 926621 = 347483) (by norm_num)
theorem B926645 : Blo 614296 926645 := bbase (se 5 (by rfl) ⟨43436, by rfl⟩ : syracuseStep 926645 = 86873) (by norm_num)
theorem B1385405 : Blo 614296 1385405 := bbase (se 3 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 1385405 = 519527) (by norm_num)
theorem B926669 : Blo 614296 926669 := bbase (se 3 (by rfl) ⟨173750, by rfl⟩ : syracuseStep 926669 = 347501) (by norm_num)
theorem B926693 : Blo 614296 926693 := bbase (se 4 (by rfl) ⟨86877, by rfl⟩ : syracuseStep 926693 = 173755) (by norm_num)
theorem B926717 : Blo 614296 926717 := bbase (se 3 (by rfl) ⟨173759, by rfl⟩ : syracuseStep 926717 = 347519) (by norm_num)
theorem B1385477 : Blo 614296 1385477 := bbase (se 4 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 1385477 = 259777) (by norm_num)
theorem B926741 : Blo 614296 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B926765 : Blo 614296 926765 := bbase (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) (by norm_num)
theorem B2073653 : Blo 614296 2073653 := bbase (se 5 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 2073653 = 194405) (by norm_num)
theorem B1483829 : Blo 614296 1483829 := bbase (se 5 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 1483829 = 139109) (by norm_num)
theorem B926789 : Blo 614296 926789 := bbase (se 4 (by rfl) ⟨86886, by rfl⟩ : syracuseStep 926789 = 173773) (by norm_num)
theorem B1385549 : Blo 614296 1385549 := bbase (se 3 (by rfl) ⟨259790, by rfl⟩ : syracuseStep 1385549 = 519581) (by norm_num)
theorem B926813 : Blo 614296 926813 := bbase (se 3 (by rfl) ⟨173777, by rfl⟩ : syracuseStep 926813 = 347555) (by norm_num)
theorem B926837 : Blo 614296 926837 := bbase (se 5 (by rfl) ⟨43445, by rfl⟩ : syracuseStep 926837 = 86891) (by norm_num)
theorem B926861 : Blo 614296 926861 := bbase (se 3 (by rfl) ⟨173786, by rfl⟩ : syracuseStep 926861 = 347573) (by norm_num)
theorem B1320077 : Blo 614296 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B1385621 : Blo 614296 1385621 := bbase (se 6 (by rfl) ⟨32475, by rfl⟩ : syracuseStep 1385621 = 64951) (by norm_num)
theorem B926885 : Blo 614296 926885 := bbase (se 4 (by rfl) ⟨86895, by rfl⟩ : syracuseStep 926885 = 173791) (by norm_num)
theorem B2368693 : Blo 614296 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B926909 : Blo 614296 926909 := bbase (se 3 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 926909 = 347591) (by norm_num)
theorem B926933 : Blo 614296 926933 := bbase (se 7 (by rfl) ⟨10862, by rfl⟩ : syracuseStep 926933 = 21725) (by norm_num)
theorem B1385693 : Blo 614296 1385693 := bbase (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) (by norm_num)
theorem B926957 : Blo 614296 926957 := bbase (se 3 (by rfl) ⟨173804, by rfl⟩ : syracuseStep 926957 = 347609) (by norm_num)
theorem B1582325 : Blo 614296 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B926981 : Blo 614296 926981 := bbase (se 4 (by rfl) ⟨86904, by rfl⟩ : syracuseStep 926981 = 173809) (by norm_num)
theorem B927005 : Blo 614296 927005 := bbase (se 3 (by rfl) ⟨173813, by rfl⟩ : syracuseStep 927005 = 347627) (by norm_num)
theorem B1385765 : Blo 614296 1385765 := bbase (se 4 (by rfl) ⟨129915, by rfl⟩ : syracuseStep 1385765 = 259831) (by norm_num)
theorem B927029 : Blo 614296 927029 := bbase (se 5 (by rfl) ⟨43454, by rfl⟩ : syracuseStep 927029 = 86909) (by norm_num)
theorem B927053 : Blo 614296 927053 := bbase (se 3 (by rfl) ⟨173822, by rfl⟩ : syracuseStep 927053 = 347645) (by norm_num)
theorem B927077 : Blo 614296 927077 := bbase (se 4 (by rfl) ⟨86913, by rfl⟩ : syracuseStep 927077 = 173827) (by norm_num)
theorem B1385837 : Blo 614296 1385837 := bbase (se 3 (by rfl) ⟨259844, by rfl⟩ : syracuseStep 1385837 = 519689) (by norm_num)
theorem B664949 : Blo 614296 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B3122549 : Blo 614296 3122549 := bbase (se 5 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 3122549 = 292739) (by norm_num)
theorem B927101 : Blo 614296 927101 := bbase (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) (by norm_num)
theorem B1484165 : Blo 614296 1484165 := bbase (se 4 (by rfl) ⟨139140, by rfl⟩ : syracuseStep 1484165 = 278281) (by norm_num)
theorem B927125 : Blo 614296 927125 := bbase (se 6 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 927125 = 43459) (by norm_num)
theorem B927149 : Blo 614296 927149 := bbase (se 3 (by rfl) ⟨173840, by rfl⟩ : syracuseStep 927149 = 347681) (by norm_num)
theorem B1385909 : Blo 614296 1385909 := bbase (se 5 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 1385909 = 129929) (by norm_num)
theorem B1582517 : Blo 614296 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B927173 : Blo 614296 927173 := bbase (se 4 (by rfl) ⟨86922, by rfl⟩ : syracuseStep 927173 = 173845) (by norm_num)
theorem B927197 : Blo 614296 927197 := bbase (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) (by norm_num)
theorem B2074085 : Blo 614296 2074085 := bbase (se 4 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 2074085 = 388891) (by norm_num)
theorem B927221 : Blo 614296 927221 := bbase (se 5 (by rfl) ⟨43463, by rfl⟩ : syracuseStep 927221 = 86927) (by norm_num)
theorem B1385981 : Blo 614296 1385981 := bbase (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) (by norm_num)
theorem B927245 : Blo 614296 927245 := bbase (se 3 (by rfl) ⟨173858, by rfl⟩ : syracuseStep 927245 = 347717) (by norm_num)
theorem B927269 : Blo 614296 927269 := bbase (se 4 (by rfl) ⟨86931, by rfl⟩ : syracuseStep 927269 = 173863) (by norm_num)
theorem B2336309 : Blo 614296 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B927293 : Blo 614296 927293 := bbase (se 3 (by rfl) ⟨173867, by rfl⟩ : syracuseStep 927293 = 347735) (by norm_num)
theorem B1386053 : Blo 614296 1386053 := bbase (se 4 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 1386053 = 259885) (by norm_num)
theorem B927317 : Blo 614296 927317 := bbase (se 8 (by rfl) ⟨5433, by rfl⟩ : syracuseStep 927317 = 10867) (by norm_num)
theorem B927341 : Blo 614296 927341 := bbase (se 3 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 927341 = 347753) (by norm_num)
theorem B927365 : Blo 614296 927365 := bbase (se 4 (by rfl) ⟨86940, by rfl⟩ : syracuseStep 927365 = 173881) (by norm_num)
theorem B1386125 : Blo 614296 1386125 := bbase (se 3 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 1386125 = 519797) (by norm_num)
theorem B927389 : Blo 614296 927389 := bbase (se 3 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 927389 = 347771) (by norm_num)
theorem B2369189 : Blo 614296 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B927413 : Blo 614296 927413 := bbase (se 5 (by rfl) ⟨43472, by rfl⟩ : syracuseStep 927413 = 86945) (by norm_num)
theorem B927437 : Blo 614296 927437 := bbase (se 3 (by rfl) ⟨173894, by rfl⟩ : syracuseStep 927437 = 347789) (by norm_num)
theorem B1386197 : Blo 614296 1386197 := bbase (se 7 (by rfl) ⟨16244, by rfl⟩ : syracuseStep 1386197 = 32489) (by norm_num)
theorem B3516149 : Blo 614296 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B1386269 : Blo 614296 1386269 := bbase (se 3 (by rfl) ⟨259925, by rfl⟩ : syracuseStep 1386269 = 519851) (by norm_num)
theorem B2336597 : Blo 614296 2336597 := bbase (se 9 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 2336597 = 13691) (by norm_num)
theorem B1386341 : Blo 614296 1386341 := bbase (se 4 (by rfl) ⟨129969, by rfl⟩ : syracuseStep 1386341 = 259939) (by norm_num)
theorem B2074517 : Blo 614296 2074517 := bbase (se 6 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 2074517 = 97243) (by norm_num)
theorem B1386413 : Blo 614296 1386413 := bbase (se 3 (by rfl) ⟨259952, by rfl⟩ : syracuseStep 1386413 = 519905) (by norm_num)
theorem B1386485 : Blo 614296 1386485 := bbase (se 5 (by rfl) ⟨64991, by rfl⟩ : syracuseStep 1386485 = 129983) (by norm_num)
theorem B1386557 : Blo 614296 1386557 := bbase (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) (by norm_num)
theorem B2631781 : Blo 614296 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B1386629 : Blo 614296 1386629 := bbase (se 4 (by rfl) ⟨129996, by rfl⟩ : syracuseStep 1386629 = 259993) (by norm_num)
theorem B1386701 : Blo 614296 1386701 := bbase (se 3 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 1386701 = 520013) (by norm_num)
theorem B1386773 : Blo 614296 1386773 := bbase (se 6 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 1386773 = 65005) (by norm_num)
theorem B2074949 : Blo 614296 2074949 := bbase (se 4 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 2074949 = 389053) (by norm_num)
theorem B1386845 : Blo 614296 1386845 := bbase (se 3 (by rfl) ⟨260033, by rfl⟩ : syracuseStep 1386845 = 520067) (by norm_num)
theorem B1386917 : Blo 614296 1386917 := bbase (se 4 (by rfl) ⟨130023, by rfl⟩ : syracuseStep 1386917 = 260047) (by norm_num)
theorem B1485221 : Blo 614296 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B1386989 : Blo 614296 1386989 := bbase (se 3 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 1386989 = 520121) (by norm_num)
theorem B1387061 : Blo 614296 1387061 := bbase (se 5 (by rfl) ⟨65018, by rfl⟩ : syracuseStep 1387061 = 130037) (by norm_num)
theorem B1780309 : Blo 614296 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1387133 : Blo 614296 1387133 := bbase (se 3 (by rfl) ⟨260087, by rfl⟩ : syracuseStep 1387133 = 520175) (by norm_num)
theorem B3123845 : Blo 614296 3123845 := bbase (se 4 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 3123845 = 585721) (by norm_num)
theorem B1387205 : Blo 614296 1387205 := bbase (se 4 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 1387205 = 260101) (by norm_num)
theorem B2075381 : Blo 614296 2075381 := bbase (se 5 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 2075381 = 194567) (by norm_num)
theorem B1387277 : Blo 614296 1387277 := bbase (se 3 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 1387277 = 520229) (by norm_num)
theorem B1387349 : Blo 614296 1387349 := bbase (se 9 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 1387349 = 8129) (by norm_num)
theorem B1387421 : Blo 614296 1387421 := bbase (se 3 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 1387421 = 520283) (by norm_num)
theorem B1387493 : Blo 614296 1387493 := bbase (se 4 (by rfl) ⟨130077, by rfl⟩ : syracuseStep 1387493 = 260155) (by norm_num)
theorem B2337781 : Blo 614296 2337781 := bbase (se 5 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 2337781 = 219167) (by norm_num)
theorem B1387565 : Blo 614296 1387565 := bbase (se 3 (by rfl) ⟨260168, by rfl⟩ : syracuseStep 1387565 = 520337) (by norm_num)
theorem B1387637 : Blo 614296 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B3124373 : Blo 614296 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B2075813 : Blo 614296 2075813 := bbase (se 4 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 2075813 = 389215) (by norm_num)
theorem B1387709 : Blo 614296 1387709 := bbase (se 3 (by rfl) ⟨260195, by rfl⟩ : syracuseStep 1387709 = 520391) (by norm_num)
theorem B1387781 : Blo 614296 1387781 := bbase (se 4 (by rfl) ⟨130104, by rfl⟩ : syracuseStep 1387781 = 260209) (by norm_num)
theorem B2338085 : Blo 614296 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B1387853 : Blo 614296 1387853 := bbase (se 3 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 1387853 = 520445) (by norm_num)
theorem B830821 : Blo 614296 830821 := bbase (se 4 (by rfl) ⟨77889, by rfl⟩ : syracuseStep 830821 = 155779) (by norm_num)
theorem B3943829 : Blo 614296 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B1387925 : Blo 614296 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B1387997 : Blo 614296 1387997 := bbase (se 3 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 1387997 = 520499) (by norm_num)
theorem B1388069 : Blo 614296 1388069 := bbase (se 4 (by rfl) ⟨130131, by rfl⟩ : syracuseStep 1388069 = 260263) (by norm_num)
theorem B2633269 : Blo 614296 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B2633285 : Blo 614296 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B2076245 : Blo 614296 2076245 := bbase (se 8 (by rfl) ⟨12165, by rfl⟩ : syracuseStep 2076245 = 24331) (by norm_num)
theorem B1388141 : Blo 614296 1388141 := bbase (se 3 (by rfl) ⟨260276, by rfl⟩ : syracuseStep 1388141 = 520553) (by norm_num)
theorem B1388213 : Blo 614296 1388213 := bbase (se 5 (by rfl) ⟨65072, by rfl⟩ : syracuseStep 1388213 = 130145) (by norm_num)
theorem B634601 : Blo 614296 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B1388285 : Blo 614296 1388285 := bbase (se 3 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 1388285 = 520607) (by norm_num)
theorem B1388357 : Blo 614296 1388357 := bbase (se 4 (by rfl) ⟨130158, by rfl⟩ : syracuseStep 1388357 = 260317) (by norm_num)
theorem B2502485 : Blo 614296 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B4435829 : Blo 614296 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1388429 : Blo 614296 1388429 := bbase (se 3 (by rfl) ⟨260330, by rfl⟩ : syracuseStep 1388429 = 520661) (by norm_num)
theorem B3125141 : Blo 614296 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B1388501 : Blo 614296 1388501 := bbase (se 7 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 1388501 = 32543) (by norm_num)
theorem B2076677 : Blo 614296 2076677 := bbase (se 4 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 2076677 = 389377) (by norm_num)
theorem B2109445 : Blo 614296 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B1388573 : Blo 614296 1388573 := bbase (se 3 (by rfl) ⟨260357, by rfl⟩ : syracuseStep 1388573 = 520715) (by norm_num)
theorem B831541 : Blo 614296 831541 := bbase (se 5 (by rfl) ⟨38978, by rfl⟩ : syracuseStep 831541 = 77957) (by norm_num)
theorem B1781813 : Blo 614296 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B2535509 : Blo 614296 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B1388645 : Blo 614296 1388645 := bbase (se 4 (by rfl) ⟨130185, by rfl⟩ : syracuseStep 1388645 = 260371) (by norm_num)
theorem B1978501 : Blo 614296 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B798881 : Blo 614296 798881 := bbase (se 2 (by rfl) ⟨299580, by rfl⟩ : syracuseStep 798881 = 599161) (by norm_num)
theorem B1388717 : Blo 614296 1388717 := bbase (se 3 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 1388717 = 520769) (by norm_num)
theorem B1388789 : Blo 614296 1388789 := bbase (se 5 (by rfl) ⟨65099, by rfl⟩ : syracuseStep 1388789 = 130199) (by norm_num)
theorem B1388861 : Blo 614296 1388861 := bbase (se 3 (by rfl) ⟨260411, by rfl⟩ : syracuseStep 1388861 = 520823) (by norm_num)
theorem B1388933 : Blo 614296 1388933 := bbase (se 4 (by rfl) ⟨130212, by rfl⟩ : syracuseStep 1388933 = 260425) (by norm_num)
theorem B1978757 : Blo 614296 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B2077109 : Blo 614296 2077109 := bbase (se 5 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 2077109 = 194729) (by norm_num)
theorem B1389005 : Blo 614296 1389005 := bbase (se 3 (by rfl) ⟨260438, by rfl⟩ : syracuseStep 1389005 = 520877) (by norm_num)
theorem B831973 : Blo 614296 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1749509 : Blo 614296 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B1389077 : Blo 614296 1389077 := bbase (se 6 (by rfl) ⟨32556, by rfl⟩ : syracuseStep 1389077 = 65113) (by norm_num)
theorem B1389149 : Blo 614296 1389149 := bbase (se 3 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 1389149 = 520931) (by norm_num)
theorem B1389221 : Blo 614296 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B4207285 : Blo 614296 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B832205 : Blo 614296 832205 := bbase (se 3 (by rfl) ⟨156038, by rfl⟩ : syracuseStep 832205 = 312077) (by norm_num)
theorem B668377 : Blo 614296 668377 := bbase (se 2 (by rfl) ⟨250641, by rfl⟩ : syracuseStep 668377 = 501283) (by norm_num)
theorem B1389293 : Blo 614296 1389293 := bbase (se 3 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 1389293 = 520985) (by norm_num)
theorem B1389365 : Blo 614296 1389365 := bbase (se 5 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 1389365 = 130253) (by norm_num)
theorem B2077541 : Blo 614296 2077541 := bbase (se 4 (by rfl) ⟨194769, by rfl⟩ : syracuseStep 2077541 = 389539) (by norm_num)
theorem B2962277 : Blo 614296 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B1389437 : Blo 614296 1389437 := bbase (se 3 (by rfl) ⟨260519, by rfl⟩ : syracuseStep 1389437 = 521039) (by norm_num)
theorem B1389509 : Blo 614296 1389509 := bbase (se 4 (by rfl) ⟨130266, by rfl⟩ : syracuseStep 1389509 = 260533) (by norm_num)
theorem B701393 : Blo 614296 701393 := bbase (se 2 (by rfl) ⟨263022, by rfl⟩ : syracuseStep 701393 = 526045) (by norm_num)
theorem B12530645 : Blo 614296 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1389581 : Blo 614296 1389581 := bbase (se 3 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 1389581 = 521093) (by norm_num)
theorem B1586213 : Blo 614296 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B3847253 : Blo 614296 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B1389653 : Blo 614296 1389653 := bbase (se 8 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 1389653 = 16285) (by norm_num)
theorem B832669 : Blo 614296 832669 := bbase (se 3 (by rfl) ⟨156125, by rfl⟩ : syracuseStep 832669 = 312251) (by norm_num)
theorem B1389725 : Blo 614296 1389725 := bbase (se 3 (by rfl) ⟨260573, by rfl⟩ : syracuseStep 1389725 = 521147) (by norm_num)
theorem B3126437 : Blo 614296 3126437 := bbase (se 4 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 3126437 = 586207) (by norm_num)
theorem B1389797 : Blo 614296 1389797 := bbase (se 4 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 1389797 = 260587) (by norm_num)
theorem B1750261 : Blo 614296 1750261 := bbase (se 5 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 1750261 = 164087) (by norm_num)
theorem B2077973 : Blo 614296 2077973 := bbase (se 6 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 2077973 = 97405) (by norm_num)
theorem B1389869 : Blo 614296 1389869 := bbase (se 3 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 1389869 = 521201) (by norm_num)
theorem B2340197 : Blo 614296 2340197 := bbase (se 4 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 2340197 = 438787) (by norm_num)
theorem B1389941 : Blo 614296 1389941 := bbase (se 5 (by rfl) ⟨65153, by rfl⟩ : syracuseStep 1389941 = 130307) (by norm_num)
theorem B1390013 : Blo 614296 1390013 := bbase (se 3 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 1390013 = 521255) (by norm_num)
theorem B1390085 : Blo 614296 1390085 := bbase (se 4 (by rfl) ⟨130320, by rfl⟩ : syracuseStep 1390085 = 260641) (by norm_num)
theorem B1390157 : Blo 614296 1390157 := bbase (se 3 (by rfl) ⟨260654, by rfl⟩ : syracuseStep 1390157 = 521309) (by norm_num)
theorem B2340485 : Blo 614296 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B1390229 : Blo 614296 1390229 := bbase (se 6 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 1390229 = 65167) (by norm_num)
theorem B2078405 : Blo 614296 2078405 := bbase (se 4 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 2078405 = 389701) (by norm_num)
theorem B1390301 : Blo 614296 1390301 := bbase (se 3 (by rfl) ⟨260681, by rfl⟩ : syracuseStep 1390301 = 521363) (by norm_num)
theorem B2635541 : Blo 614296 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B1390373 : Blo 614296 1390373 := bbase (se 4 (by rfl) ⟨130347, by rfl⟩ : syracuseStep 1390373 = 260695) (by norm_num)
theorem B1390445 : Blo 614296 1390445 := bbase (se 3 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 1390445 = 521417) (by norm_num)
theorem B1390517 : Blo 614296 1390517 := bbase (se 5 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 1390517 = 130361) (by norm_num)
theorem B1390589 : Blo 614296 1390589 := bbase (se 3 (by rfl) ⟨260735, by rfl⟩ : syracuseStep 1390589 = 521471) (by norm_num)
theorem B1390661 : Blo 614296 1390661 := bbase (se 4 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 1390661 = 260749) (by norm_num)
theorem B2078837 : Blo 614296 2078837 := bbase (se 5 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 2078837 = 194891) (by norm_num)
theorem B1390733 : Blo 614296 1390733 := bbase (se 3 (by rfl) ⟨260762, by rfl⟩ : syracuseStep 1390733 = 521525) (by norm_num)
theorem B1390805 : Blo 614296 1390805 := bbase (se 7 (by rfl) ⟨16298, by rfl⟩ : syracuseStep 1390805 = 32597) (by norm_num)
theorem B3324149 : Blo 614296 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B1390877 : Blo 614296 1390877 := bbase (se 3 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 1390877 = 521579) (by norm_num)
theorem B1390949 : Blo 614296 1390949 := bbase (se 4 (by rfl) ⟨130401, by rfl⟩ : syracuseStep 1390949 = 260803) (by norm_num)
theorem B1391021 : Blo 614296 1391021 := bbase (se 3 (by rfl) ⟨260816, by rfl⟩ : syracuseStep 1391021 = 521633) (by norm_num)
theorem B3127733 : Blo 614296 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B833989 : Blo 614296 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B1391093 : Blo 614296 1391093 := bbase (se 5 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 1391093 = 130415) (by norm_num)
theorem B3750421 : Blo 614296 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B2079269 : Blo 614296 2079269 := bbase (se 4 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 2079269 = 389863) (by norm_num)
theorem B1554997 : Blo 614296 1554997 := bbase (se 5 (by rfl) ⟨72890, by rfl⟩ : syracuseStep 1554997 = 145781) (by norm_num)
theorem B1391165 : Blo 614296 1391165 := bbase (se 3 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 1391165 = 521687) (by norm_num)
theorem B703085 : Blo 614296 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B11844245 : Blo 614296 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B1555109 : Blo 614296 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B834221 : Blo 614296 834221 := bbase (se 3 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 834221 = 312833) (by norm_num)
theorem B2341669 : Blo 614296 2341669 := bbase (se 4 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 2341669 = 439063) (by norm_num)
theorem B1555301 : Blo 614296 1555301 := bbase (se 4 (by rfl) ⟨145809, by rfl⟩ : syracuseStep 1555301 = 291619) (by norm_num)
theorem B2079701 : Blo 614296 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B703477 : Blo 614296 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B2341973 : Blo 614296 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B11877461 : Blo 614296 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B1555645 : Blo 614296 1555645 := bbase (se 3 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 1555645 = 583367) (by norm_num)
theorem B703733 : Blo 614296 703733 := bbase (se 5 (by rfl) ⟨32987, by rfl⟩ : syracuseStep 703733 = 65975) (by norm_num)
theorem B703769 : Blo 614296 703769 := bbase (se 2 (by rfl) ⟨263913, by rfl⟩ : syracuseStep 703769 = 527827) (by norm_num)
theorem B1555757 : Blo 614296 1555757 := bbase (se 3 (by rfl) ⟨291704, by rfl⟩ : syracuseStep 1555757 = 583409) (by norm_num)
theorem B2080133 : Blo 614296 2080133 := bbase (se 4 (by rfl) ⟨195012, by rfl⟩ : syracuseStep 2080133 = 390025) (by norm_num)
theorem B998821 : Blo 614296 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B1555949 : Blo 614296 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B4439573 : Blo 614296 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B835157 : Blo 614296 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B1523333 : Blo 614296 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B3129029 : Blo 614296 3129029 := bbase (se 4 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 3129029 = 586693) (by norm_num)
theorem B4275989 : Blo 614296 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B835373 : Blo 614296 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B2080565 : Blo 614296 2080565 := bbase (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) (by norm_num)
theorem B1556293 : Blo 614296 1556293 := bbase (se 4 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 1556293 = 291805) (by norm_num)
theorem B10501973 : Blo 614296 10501973 := bbase (se 9 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 10501973 = 61535) (by norm_num)
theorem B2703253 : Blo 614296 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B1556405 : Blo 614296 1556405 := bbase (se 5 (by rfl) ⟨72956, by rfl⟩ : syracuseStep 1556405 = 145913) (by norm_num)
theorem B1753109 : Blo 614296 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B1556597 : Blo 614296 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B2080997 : Blo 614296 2080997 := bbase (se 4 (by rfl) ⟨195093, by rfl⟩ : syracuseStep 2080997 = 390187) (by norm_num)
theorem B1556941 : Blo 614296 1556941 := bbase (se 3 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 1556941 = 583853) (by norm_num)
theorem B10961365 : Blo 614296 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B4669973 : Blo 614296 4669973 := bbase (se 6 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 4669973 = 218905) (by norm_num)
theorem B7225877 : Blo 614296 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B1557053 : Blo 614296 1557053 := bbase (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) (by norm_num)
theorem B1688197 : Blo 614296 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B2081429 : Blo 614296 2081429 := bbase (se 6 (by rfl) ⟨48783, by rfl⟩ : syracuseStep 2081429 = 97567) (by norm_num)
theorem B1557245 : Blo 614296 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B738109 : Blo 614296 738109 := bbase (se 3 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 738109 = 276791) (by norm_num)
theorem B738301 : Blo 614296 738301 := bbase (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) (by norm_num)
theorem B2081861 : Blo 614296 2081861 := bbase (se 4 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 2081861 = 390349) (by norm_num)
theorem B1557589 : Blo 614296 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B738401 : Blo 614296 738401 := bbase (se 2 (by rfl) ⟨276900, by rfl⟩ : syracuseStep 738401 = 553801) (by norm_num)
theorem B2344085 : Blo 614296 2344085 := bbase (se 6 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 2344085 = 109879) (by norm_num)
theorem B2999477 : Blo 614296 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1754293 : Blo 614296 1754293 := bbase (se 5 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 1754293 = 164465) (by norm_num)
theorem B1557701 : Blo 614296 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B1754453 : Blo 614296 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B1557893 : Blo 614296 1557893 := bbase (se 4 (by rfl) ⟨146052, by rfl⟩ : syracuseStep 1557893 = 292105) (by norm_num)
theorem B2344373 : Blo 614296 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B2082293 : Blo 614296 2082293 := bbase (se 5 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 2082293 = 195215) (by norm_num)
theorem B1754693 : Blo 614296 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B2639573 : Blo 614296 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B1558237 : Blo 614296 1558237 := bbase (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) (by norm_num)
theorem B1754885 : Blo 614296 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B2967349 : Blo 614296 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B1558349 : Blo 614296 1558349 := bbase (se 3 (by rfl) ⟨292190, by rfl⟩ : syracuseStep 1558349 = 584381) (by norm_num)
theorem B739189 : Blo 614296 739189 := bbase (se 5 (by rfl) ⟨34649, by rfl⟩ : syracuseStep 739189 = 69299) (by norm_num)
theorem B2082725 : Blo 614296 2082725 := bbase (se 4 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 2082725 = 390511) (by norm_num)
theorem B1558541 : Blo 614296 1558541 := bbase (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) (by norm_num)
theorem B2083157 : Blo 614296 2083157 := bbase (se 10 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 2083157 = 6103) (by norm_num)
theorem B1558885 : Blo 614296 1558885 := bbase (se 4 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 1558885 = 292291) (by norm_num)
theorem B1558997 : Blo 614296 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B739901 : Blo 614296 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B2345557 : Blo 614296 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B1559189 : Blo 614296 1559189 := bbase (se 6 (by rfl) ⟨36543, by rfl⟩ : syracuseStep 1559189 = 73087) (by norm_num)
theorem B1755877 : Blo 614296 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B2083589 : Blo 614296 2083589 := bbase (se 4 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 2083589 = 390673) (by norm_num)
theorem B1428317 : Blo 614296 1428317 := bbase (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) (by norm_num)
theorem B2345861 : Blo 614296 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B740237 : Blo 614296 740237 := bbase (se 3 (by rfl) ⟨138794, by rfl⟩ : syracuseStep 740237 = 277589) (by norm_num)
theorem B1166309 : Blo 614296 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B1559533 : Blo 614296 1559533 := bbase (se 3 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 1559533 = 584825) (by norm_num)
theorem B740353 : Blo 614296 740353 := bbase (se 2 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 740353 = 555265) (by norm_num)
theorem B740377 : Blo 614296 740377 := bbase (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) (by norm_num)
theorem B1559645 : Blo 614296 1559645 := bbase (se 3 (by rfl) ⟨292433, by rfl⟩ : syracuseStep 1559645 = 584867) (by norm_num)
theorem B1428629 : Blo 614296 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2084021 : Blo 614296 2084021 := bbase (se 5 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 2084021 = 195377) (by norm_num)
theorem B3755285 : Blo 614296 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B1559837 : Blo 614296 1559837 := bbase (se 3 (by rfl) ⟨292469, by rfl⟩ : syracuseStep 1559837 = 584939) (by norm_num)
theorem B2084453 : Blo 614296 2084453 := bbase (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) (by norm_num)
theorem B1560181 : Blo 614296 1560181 := bbase (se 5 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 1560181 = 146267) (by norm_num)
theorem B9981589 : Blo 614296 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B741073 : Blo 614296 741073 := bbase (se 2 (by rfl) ⟨277902, by rfl⟩ : syracuseStep 741073 = 555805) (by norm_num)
theorem B1167061 : Blo 614296 1167061 := bbase (se 7 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 1167061 = 27353) (by norm_num)
theorem B2215637 : Blo 614296 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B1560293 : Blo 614296 1560293 := bbase (se 4 (by rfl) ⟨146277, by rfl⟩ : syracuseStep 1560293 = 292555) (by norm_num)
theorem B3165973 : Blo 614296 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B741169 : Blo 614296 741169 := bbase (se 2 (by rfl) ⟨277938, by rfl⟩ : syracuseStep 741169 = 555877) (by norm_num)
theorem B1756981 : Blo 614296 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B1167205 : Blo 614296 1167205 := bbase (se 4 (by rfl) ⟨109425, by rfl⟩ : syracuseStep 1167205 = 218851) (by norm_num)
theorem B1560485 : Blo 614296 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1167365 : Blo 614296 1167365 := bbase (se 4 (by rfl) ⟨109440, by rfl⟩ : syracuseStep 1167365 = 218881) (by norm_num)
theorem B5918741 : Blo 614296 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B2084885 : Blo 614296 2084885 := bbase (se 6 (by rfl) ⟨48864, by rfl⟩ : syracuseStep 2084885 = 97729) (by norm_num)
theorem B2216069 : Blo 614296 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1167509 : Blo 614296 1167509 := bbase (se 6 (by rfl) ⟨27363, by rfl⟩ : syracuseStep 1167509 = 54727) (by norm_num)
theorem B1560829 : Blo 614296 1560829 := bbase (se 3 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 1560829 = 585311) (by norm_num)
theorem B938261 : Blo 614296 938261 := bbase (se 6 (by rfl) ⟨21990, by rfl⟩ : syracuseStep 938261 = 43981) (by norm_num)
theorem B1560941 : Blo 614296 1560941 := bbase (se 3 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 1560941 = 585353) (by norm_num)
theorem B1036685 : Blo 614296 1036685 := bbase (se 3 (by rfl) ⟨194378, by rfl⟩ : syracuseStep 1036685 = 388757) (by norm_num)
theorem B1167797 : Blo 614296 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B2085317 : Blo 614296 2085317 := bbase (se 4 (by rfl) ⟨195498, by rfl⟩ : syracuseStep 2085317 = 390997) (by norm_num)
theorem B1036813 : Blo 614296 1036813 := bbase (se 3 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 1036813 = 388805) (by norm_num)
theorem B1692181 : Blo 614296 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B1561133 : Blo 614296 1561133 := bbase (se 3 (by rfl) ⟨292712, by rfl⟩ : syracuseStep 1561133 = 585425) (by norm_num)
theorem B1167949 : Blo 614296 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B1036901 : Blo 614296 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B1037029 : Blo 614296 1037029 := bbase (se 4 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 1037029 = 194443) (by norm_num)
theorem B2806501 : Blo 614296 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B742169 : Blo 614296 742169 := bbase (se 2 (by rfl) ⟨278313, by rfl⟩ : syracuseStep 742169 = 556627) (by norm_num)
theorem B1037117 : Blo 614296 1037117 := bbase (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) (by norm_num)
theorem B3756917 : Blo 614296 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B2085749 : Blo 614296 2085749 := bbase (se 5 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 2085749 = 195539) (by norm_num)
theorem B1168253 : Blo 614296 1168253 := bbase (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) (by norm_num)
theorem B1561477 : Blo 614296 1561477 := bbase (se 4 (by rfl) ⟨146388, by rfl⟩ : syracuseStep 1561477 = 292777) (by norm_num)
theorem B1037245 : Blo 614296 1037245 := bbase (se 3 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 1037245 = 388967) (by norm_num)
theorem B1561589 : Blo 614296 1561589 := bbase (se 5 (by rfl) ⟨73199, by rfl⟩ : syracuseStep 1561589 = 146399) (by norm_num)
theorem B1037333 : Blo 614296 1037333 := bbase (se 6 (by rfl) ⟨24312, by rfl⟩ : syracuseStep 1037333 = 48625) (by norm_num)
theorem B742457 : Blo 614296 742457 := bbase (se 2 (by rfl) ⟨278421, by rfl⟩ : syracuseStep 742457 = 556843) (by norm_num)
theorem B2806901 : Blo 614296 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1037461 : Blo 614296 1037461 := bbase (se 6 (by rfl) ⟨24315, by rfl⟩ : syracuseStep 1037461 = 48631) (by norm_num)
theorem B1561781 : Blo 614296 1561781 := bbase (se 5 (by rfl) ⟨73208, by rfl⟩ : syracuseStep 1561781 = 146417) (by norm_num)
theorem B742621 : Blo 614296 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B1037549 : Blo 614296 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B742649 : Blo 614296 742649 := bbase (se 2 (by rfl) ⟨278493, by rfl⟩ : syracuseStep 742649 = 556987) (by norm_num)
theorem B1758485 : Blo 614296 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B2086181 : Blo 614296 2086181 := bbase (se 4 (by rfl) ⟨195579, by rfl⟩ : syracuseStep 2086181 = 391159) (by norm_num)
theorem B3954005 : Blo 614296 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B1037677 : Blo 614296 1037677 := bbase (se 3 (by rfl) ⟨194564, by rfl⟩ : syracuseStep 1037677 = 389129) (by norm_num)
theorem B742765 : Blo 614296 742765 := bbase (se 3 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 742765 = 278537) (by norm_num)
theorem B1037765 : Blo 614296 1037765 := bbase (se 4 (by rfl) ⟨97290, by rfl⟩ : syracuseStep 1037765 = 194581) (by norm_num)
theorem B1562125 : Blo 614296 1562125 := bbase (se 3 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 1562125 = 585797) (by norm_num)
theorem B1037893 : Blo 614296 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B1169005 : Blo 614296 1169005 := bbase (se 3 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 1169005 = 438377) (by norm_num)
theorem B1562237 : Blo 614296 1562237 := bbase (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) (by norm_num)
theorem B1037981 : Blo 614296 1037981 := bbase (se 3 (by rfl) ⟨194621, by rfl⟩ : syracuseStep 1037981 = 389243) (by norm_num)
theorem B2086613 : Blo 614296 2086613 := bbase (se 7 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 2086613 = 48905) (by norm_num)
theorem B1169149 : Blo 614296 1169149 := bbase (se 3 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 1169149 = 438431) (by norm_num)
theorem B1038109 : Blo 614296 1038109 := bbase (se 3 (by rfl) ⟨194645, by rfl⟩ : syracuseStep 1038109 = 389291) (by norm_num)
theorem B1562429 : Blo 614296 1562429 := bbase (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) (by norm_num)
theorem B1038197 : Blo 614296 1038197 := bbase (se 5 (by rfl) ⟨48665, by rfl⟩ : syracuseStep 1038197 = 97331) (by norm_num)
theorem B1169309 : Blo 614296 1169309 := bbase (se 3 (by rfl) ⟨219245, by rfl⟩ : syracuseStep 1169309 = 438491) (by norm_num)
theorem B939941 : Blo 614296 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B939989 : Blo 614296 939989 := bbase (se 7 (by rfl) ⟨11015, by rfl⟩ : syracuseStep 939989 = 22031) (by norm_num)
theorem B1038325 : Blo 614296 1038325 := bbase (se 5 (by rfl) ⟨48671, by rfl⟩ : syracuseStep 1038325 = 97343) (by norm_num)
theorem B1169453 : Blo 614296 1169453 := bbase (se 3 (by rfl) ⟨219272, by rfl⟩ : syracuseStep 1169453 = 438545) (by norm_num)
theorem B1038413 : Blo 614296 1038413 := bbase (se 3 (by rfl) ⟨194702, by rfl⟩ : syracuseStep 1038413 = 389405) (by norm_num)
theorem B2283653 : Blo 614296 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B1562773 : Blo 614296 1562773 := bbase (se 6 (by rfl) ⟨36627, by rfl⟩ : syracuseStep 1562773 = 73255) (by norm_num)
theorem B1038541 : Blo 614296 1038541 := bbase (se 3 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 1038541 = 389453) (by norm_num)
theorem B1562885 : Blo 614296 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B1038629 : Blo 614296 1038629 := bbase (se 4 (by rfl) ⟨97371, by rfl⟩ : syracuseStep 1038629 = 194743) (by norm_num)
theorem B1169741 : Blo 614296 1169741 := bbase (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) (by norm_num)
theorem B5265749 : Blo 614296 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B1038757 : Blo 614296 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B1563077 : Blo 614296 1563077 := bbase (se 4 (by rfl) ⟨146538, by rfl⟩ : syracuseStep 1563077 = 293077) (by norm_num)
theorem B1169893 : Blo 614296 1169893 := bbase (se 4 (by rfl) ⟨109677, by rfl⟩ : syracuseStep 1169893 = 219355) (by norm_num)
theorem B1038845 : Blo 614296 1038845 := bbase (se 3 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 1038845 = 389567) (by norm_num)
theorem B1038973 : Blo 614296 1038973 := bbase (se 3 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 1038973 = 389615) (by norm_num)
theorem B7002773 : Blo 614296 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B1071773 : Blo 614296 1071773 := bbase (se 3 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 1071773 = 401915) (by norm_num)
theorem B1039061 : Blo 614296 1039061 := bbase (se 7 (by rfl) ⟨12176, by rfl⟩ : syracuseStep 1039061 = 24353) (by norm_num)
theorem B2251477 : Blo 614296 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B1170197 : Blo 614296 1170197 := bbase (se 6 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 1170197 = 54853) (by norm_num)
theorem B1334045 : Blo 614296 1334045 := bbase (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) (by norm_num)
theorem B1563421 : Blo 614296 1563421 := bbase (se 3 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 1563421 = 586283) (by norm_num)
theorem B1760069 : Blo 614296 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1039189 : Blo 614296 1039189 := bbase (se 9 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 1039189 = 6089) (by norm_num)
theorem B1563533 : Blo 614296 1563533 := bbase (se 3 (by rfl) ⟨293162, by rfl⟩ : syracuseStep 1563533 = 586325) (by norm_num)
theorem B1039277 : Blo 614296 1039277 := bbase (se 3 (by rfl) ⟨194864, by rfl⟩ : syracuseStep 1039277 = 389729) (by norm_num)
theorem B875461 : Blo 614296 875461 := bbase (se 4 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 875461 = 164149) (by norm_num)
theorem B1039405 : Blo 614296 1039405 := bbase (se 3 (by rfl) ⟨194888, by rfl⟩ : syracuseStep 1039405 = 389777) (by norm_num)
theorem B1563725 : Blo 614296 1563725 := bbase (se 3 (by rfl) ⟨293198, by rfl⟩ : syracuseStep 1563725 = 586397) (by norm_num)
theorem B1039493 : Blo 614296 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B1039621 : Blo 614296 1039621 := bbase (se 4 (by rfl) ⟨97464, by rfl⟩ : syracuseStep 1039621 = 194929) (by norm_num)
theorem B777529 : Blo 614296 777529 := bbase (se 2 (by rfl) ⟨291573, by rfl⟩ : syracuseStep 777529 = 583147) (by norm_num)
theorem B57105749 : Blo 614296 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B1039709 : Blo 614296 1039709 := bbase (se 3 (by rfl) ⟨194945, by rfl⟩ : syracuseStep 1039709 = 389891) (by norm_num)
theorem B2219413 : Blo 614296 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B1564069 : Blo 614296 1564069 := bbase (se 4 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 1564069 = 293263) (by norm_num)
theorem B1662389 : Blo 614296 1662389 := bbase (se 5 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 1662389 = 155849) (by norm_num)
theorem B1039837 : Blo 614296 1039837 := bbase (se 3 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 1039837 = 389939) (by norm_num)
theorem B777701 : Blo 614296 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B1170949 : Blo 614296 1170949 := bbase (se 4 (by rfl) ⟨109776, by rfl⟩ : syracuseStep 1170949 = 219553) (by norm_num)
theorem B876053 : Blo 614296 876053 := bbase (se 6 (by rfl) ⟨20532, by rfl⟩ : syracuseStep 876053 = 41065) (by norm_num)
theorem B1564181 : Blo 614296 1564181 := bbase (se 6 (by rfl) ⟨36660, by rfl⟩ : syracuseStep 1564181 = 73321) (by norm_num)
theorem B777757 : Blo 614296 777757 := bbase (se 3 (by rfl) ⟨145829, by rfl⟩ : syracuseStep 777757 = 291659) (by norm_num)
theorem B1039925 : Blo 614296 1039925 := bbase (se 5 (by rfl) ⟨48746, by rfl⟩ : syracuseStep 1039925 = 97493) (by norm_num)
theorem B876133 : Blo 614296 876133 := bbase (se 4 (by rfl) ⟨82137, by rfl⟩ : syracuseStep 876133 = 164275) (by norm_num)
theorem B777853 : Blo 614296 777853 := bbase (se 3 (by rfl) ⟨145847, by rfl⟩ : syracuseStep 777853 = 291695) (by norm_num)
theorem B1171093 : Blo 614296 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B1040053 : Blo 614296 1040053 := bbase (se 5 (by rfl) ⟨48752, by rfl⟩ : syracuseStep 1040053 = 97505) (by norm_num)
theorem B1564373 : Blo 614296 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B876253 : Blo 614296 876253 := bbase (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) (by norm_num)
theorem B1040141 : Blo 614296 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B778025 : Blo 614296 778025 := bbase (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) (by norm_num)
theorem B1171253 : Blo 614296 1171253 := bbase (se 5 (by rfl) ⟨54902, by rfl⟩ : syracuseStep 1171253 = 109805) (by norm_num)
theorem B876349 : Blo 614296 876349 := bbase (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) (by norm_num)
theorem B778081 : Blo 614296 778081 := bbase (se 2 (by rfl) ⟨291780, by rfl⟩ : syracuseStep 778081 = 583561) (by norm_num)
theorem B1040269 : Blo 614296 1040269 := bbase (se 3 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 1040269 = 390101) (by norm_num)
theorem B778177 : Blo 614296 778177 := bbase (se 2 (by rfl) ⟨291816, by rfl⟩ : syracuseStep 778177 = 583633) (by norm_num)
theorem B1171397 : Blo 614296 1171397 := bbase (se 4 (by rfl) ⟨109818, by rfl⟩ : syracuseStep 1171397 = 219637) (by norm_num)
theorem B3170245 : Blo 614296 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1040357 : Blo 614296 1040357 := bbase (se 4 (by rfl) ⟨97533, by rfl⟩ : syracuseStep 1040357 = 195067) (by norm_num)
theorem B1564717 : Blo 614296 1564717 := bbase (se 3 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 1564717 = 586769) (by norm_num)
theorem B1040485 : Blo 614296 1040485 := bbase (se 4 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 1040485 = 195091) (by norm_num)
theorem B778349 : Blo 614296 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B4677749 : Blo 614296 4677749 := bbase (se 5 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 4677749 = 438539) (by norm_num)
theorem B1564829 : Blo 614296 1564829 := bbase (se 3 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 1564829 = 586811) (by norm_num)
theorem B778405 : Blo 614296 778405 := bbase (se 4 (by rfl) ⟨72975, by rfl⟩ : syracuseStep 778405 = 145951) (by norm_num)
theorem B1040573 : Blo 614296 1040573 := bbase (se 3 (by rfl) ⟨195107, by rfl⟩ : syracuseStep 1040573 = 390215) (by norm_num)
theorem B1171685 : Blo 614296 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B778501 : Blo 614296 778501 := bbase (se 4 (by rfl) ⟨72984, by rfl⟩ : syracuseStep 778501 = 145969) (by norm_num)
theorem B876845 : Blo 614296 876845 := bbase (se 3 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 876845 = 328817) (by norm_num)
theorem B1040701 : Blo 614296 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B1565021 : Blo 614296 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1171837 : Blo 614296 1171837 := bbase (se 3 (by rfl) ⟨219719, by rfl⟩ : syracuseStep 1171837 = 439439) (by norm_num)
theorem B1040789 : Blo 614296 1040789 := bbase (se 6 (by rfl) ⟨24393, by rfl⟩ : syracuseStep 1040789 = 48787) (by norm_num)
theorem B778673 : Blo 614296 778673 := bbase (se 2 (by rfl) ⟨292002, by rfl⟩ : syracuseStep 778673 = 584005) (by norm_num)
theorem B778729 : Blo 614296 778729 := bbase (se 2 (by rfl) ⟨292023, by rfl⟩ : syracuseStep 778729 = 584047) (by norm_num)
theorem B1040917 : Blo 614296 1040917 := bbase (se 6 (by rfl) ⟨24396, by rfl⟩ : syracuseStep 1040917 = 48793) (by norm_num)
theorem B2253349 : Blo 614296 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B778825 : Blo 614296 778825 := bbase (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) (by norm_num)
theorem B1041005 : Blo 614296 1041005 := bbase (se 3 (by rfl) ⟨195188, by rfl⟩ : syracuseStep 1041005 = 390377) (by norm_num)
theorem B1401517 : Blo 614296 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B1172141 : Blo 614296 1172141 := bbase (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) (by norm_num)
theorem B1041133 : Blo 614296 1041133 := bbase (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) (by norm_num)
theorem B778997 : Blo 614296 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B779053 : Blo 614296 779053 := bbase (se 3 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 779053 = 292145) (by norm_num)
theorem B1041221 : Blo 614296 1041221 := bbase (se 4 (by rfl) ⟨97614, by rfl⟩ : syracuseStep 1041221 = 195229) (by norm_num)
theorem B877397 : Blo 614296 877397 := bbase (se 9 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 877397 = 5141) (by norm_num)
theorem B779149 : Blo 614296 779149 := bbase (se 3 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 779149 = 292181) (by norm_num)
theorem B3335093 : Blo 614296 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B1041349 : Blo 614296 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1041437 : Blo 614296 1041437 := bbase (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) (by norm_num)
theorem B779321 : Blo 614296 779321 := bbase (se 2 (by rfl) ⟨292245, by rfl⟩ : syracuseStep 779321 = 584491) (by norm_num)
theorem B779377 : Blo 614296 779377 := bbase (se 2 (by rfl) ⟨292266, by rfl⟩ : syracuseStep 779377 = 584533) (by norm_num)
theorem B1041565 : Blo 614296 1041565 := bbase (se 3 (by rfl) ⟨195293, by rfl⟩ : syracuseStep 1041565 = 390587) (by norm_num)
theorem B779473 : Blo 614296 779473 := bbase (se 2 (by rfl) ⟨292302, by rfl⟩ : syracuseStep 779473 = 584605) (by norm_num)
theorem B5268725 : Blo 614296 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B1041653 : Blo 614296 1041653 := bbase (se 5 (by rfl) ⟨48827, by rfl⟩ : syracuseStep 1041653 = 97655) (by norm_num)
theorem B3368213 : Blo 614296 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B1041781 : Blo 614296 1041781 := bbase (se 5 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 1041781 = 97667) (by norm_num)
theorem B779645 : Blo 614296 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B1172893 : Blo 614296 1172893 := bbase (se 3 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 1172893 = 439835) (by norm_num)
theorem B779701 : Blo 614296 779701 := bbase (se 5 (by rfl) ⟨36548, by rfl⟩ : syracuseStep 779701 = 73097) (by norm_num)
theorem B1041869 : Blo 614296 1041869 := bbase (se 3 (by rfl) ⟨195350, by rfl⟩ : syracuseStep 1041869 = 390701) (by norm_num)
theorem B779797 : Blo 614296 779797 := bbase (se 6 (by rfl) ⟨18276, by rfl⟩ : syracuseStep 779797 = 36553) (by norm_num)
theorem B1173037 : Blo 614296 1173037 := bbase (se 3 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 1173037 = 439889) (by norm_num)
theorem B878149 : Blo 614296 878149 := bbase (se 4 (by rfl) ⟨82326, by rfl⟩ : syracuseStep 878149 = 164653) (by norm_num)
theorem B1041997 : Blo 614296 1041997 := bbase (se 3 (by rfl) ⟨195374, by rfl⟩ : syracuseStep 1041997 = 390749) (by norm_num)
theorem B1893989 : Blo 614296 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B1926805 : Blo 614296 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1336981 : Blo 614296 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B1042085 : Blo 614296 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B779969 : Blo 614296 779969 := bbase (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) (by norm_num)
theorem B1173197 : Blo 614296 1173197 := bbase (se 3 (by rfl) ⟨219974, by rfl⟩ : syracuseStep 1173197 = 439949) (by norm_num)
theorem B780025 : Blo 614296 780025 := bbase (se 2 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 780025 = 585019) (by norm_num)
theorem B1042213 : Blo 614296 1042213 := bbase (se 4 (by rfl) ⟨97707, by rfl⟩ : syracuseStep 1042213 = 195415) (by norm_num)
theorem B780121 : Blo 614296 780121 := bbase (se 2 (by rfl) ⟨292545, by rfl⟩ : syracuseStep 780121 = 585091) (by norm_num)
theorem B1173341 : Blo 614296 1173341 := bbase (se 3 (by rfl) ⟨220001, by rfl⟩ : syracuseStep 1173341 = 440003) (by norm_num)
theorem B1042301 : Blo 614296 1042301 := bbase (se 3 (by rfl) ⟨195431, by rfl⟩ : syracuseStep 1042301 = 390863) (by norm_num)
theorem B1042429 : Blo 614296 1042429 := bbase (se 3 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 1042429 = 390911) (by norm_num)
theorem B780293 : Blo 614296 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B780349 : Blo 614296 780349 := bbase (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) (by norm_num)
theorem B1042517 : Blo 614296 1042517 := bbase (se 8 (by rfl) ⟨6108, by rfl⟩ : syracuseStep 1042517 = 12217) (by norm_num)
theorem B1173629 : Blo 614296 1173629 := bbase (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) (by norm_num)
theorem B1665157 : Blo 614296 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B780445 : Blo 614296 780445 := bbase (se 3 (by rfl) ⟨146333, by rfl⟩ : syracuseStep 780445 = 292667) (by norm_num)
theorem B1042645 : Blo 614296 1042645 := bbase (se 7 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 1042645 = 24437) (by norm_num)
theorem B1173781 : Blo 614296 1173781 := bbase (se 6 (by rfl) ⟨27510, by rfl⟩ : syracuseStep 1173781 = 55021) (by norm_num)
theorem B1042733 : Blo 614296 1042733 := bbase (se 3 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 1042733 = 391025) (by norm_num)
theorem B780617 : Blo 614296 780617 := bbase (se 2 (by rfl) ⟨292731, by rfl⟩ : syracuseStep 780617 = 585463) (by norm_num)
theorem B878941 : Blo 614296 878941 := bbase (se 3 (by rfl) ⟨164801, by rfl⟩ : syracuseStep 878941 = 329603) (by norm_num)
theorem B780673 : Blo 614296 780673 := bbase (se 2 (by rfl) ⟨292752, by rfl⟩ : syracuseStep 780673 = 585505) (by norm_num)
theorem B1042861 : Blo 614296 1042861 := bbase (se 3 (by rfl) ⟨195536, by rfl⟩ : syracuseStep 1042861 = 391073) (by norm_num)
theorem B780769 : Blo 614296 780769 := bbase (se 2 (by rfl) ⟨292788, by rfl⟩ : syracuseStep 780769 = 585577) (by norm_num)
theorem B1042949 : Blo 614296 1042949 := bbase (se 4 (by rfl) ⟨97776, by rfl⟩ : syracuseStep 1042949 = 195553) (by norm_num)
theorem B1043077 : Blo 614296 1043077 := bbase (se 4 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 1043077 = 195577) (by norm_num)
theorem B780941 : Blo 614296 780941 := bbase (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) (by norm_num)
theorem B879277 : Blo 614296 879277 := bbase (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) (by norm_num)
theorem B1108669 : Blo 614296 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B780997 : Blo 614296 780997 := bbase (se 4 (by rfl) ⟨73218, by rfl⟩ : syracuseStep 780997 = 146437) (by norm_num)
theorem B1043165 : Blo 614296 1043165 := bbase (se 3 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 1043165 = 391187) (by norm_num)
theorem B781093 : Blo 614296 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B1043293 : Blo 614296 1043293 := bbase (se 3 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 1043293 = 391235) (by norm_num)
theorem B879493 : Blo 614296 879493 := bbase (se 4 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 879493 = 164905) (by norm_num)
theorem B781265 : Blo 614296 781265 := bbase (se 2 (by rfl) ⟨292974, by rfl⟩ : syracuseStep 781265 = 585949) (by norm_num)
theorem B781321 : Blo 614296 781321 := bbase (se 2 (by rfl) ⟨292995, by rfl⟩ : syracuseStep 781321 = 585991) (by norm_num)
theorem B781417 : Blo 614296 781417 := bbase (se 2 (by rfl) ⟨293031, by rfl⟩ : syracuseStep 781417 = 586063) (by norm_num)
theorem B1109245 : Blo 614296 1109245 := bbase (se 3 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 1109245 = 415967) (by norm_num)
theorem B879869 : Blo 614296 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B781589 : Blo 614296 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B781645 : Blo 614296 781645 := bbase (se 3 (by rfl) ⟨146558, by rfl⟩ : syracuseStep 781645 = 293117) (by norm_num)
theorem B781741 : Blo 614296 781741 := bbase (se 3 (by rfl) ⟨146576, by rfl⟩ : syracuseStep 781741 = 293153) (by norm_num)
theorem B781913 : Blo 614296 781913 := bbase (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) (by norm_num)
theorem B1011341 : Blo 614296 1011341 := bbase (se 3 (by rfl) ⟨189626, by rfl⟩ : syracuseStep 1011341 = 379253) (by norm_num)
theorem B781969 : Blo 614296 781969 := bbase (se 2 (by rfl) ⟨293238, by rfl⟩ : syracuseStep 781969 = 586477) (by norm_num)
theorem B782065 : Blo 614296 782065 := bbase (se 2 (by rfl) ⟨293274, by rfl⟩ : syracuseStep 782065 = 586549) (by norm_num)
theorem B1109909 : Blo 614296 1109909 := bbase (se 6 (by rfl) ⟨26013, by rfl⟩ : syracuseStep 1109909 = 52027) (by norm_num)
theorem B782237 : Blo 614296 782237 := bbase (se 3 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 782237 = 293339) (by norm_num)
theorem B782293 : Blo 614296 782293 := bbase (se 7 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 782293 = 18335) (by norm_num)
theorem B4223029 : Blo 614296 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B782389 : Blo 614296 782389 := bbase (se 5 (by rfl) ⟨36674, by rfl⟩ : syracuseStep 782389 = 73349) (by norm_num)
theorem B7499861 : Blo 614296 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B1110125 : Blo 614296 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B749821 : Blo 614296 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B1110629 : Blo 614296 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B3502709 : Blo 614296 3502709 := bbase (se 5 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 3502709 = 328379) (by norm_num)
theorem B4223765 : Blo 614296 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B5206837 : Blo 614296 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1504261 : Blo 614296 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B1406317 : Blo 614296 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B1996613 : Blo 614296 1996613 := bbase (se 4 (by rfl) ⟨187182, by rfl⟩ : syracuseStep 1996613 = 374365) (by norm_num)
theorem B3110885 : Blo 614296 3110885 := bbase (se 4 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 3110885 = 583291) (by norm_num)
theorem B1439837 : Blo 614296 1439837 := bbase (se 3 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 1439837 = 539939) (by norm_num)
theorem B19003733 : Blo 614296 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B1997237 : Blo 614296 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B948893 : Blo 614296 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B4225877 : Blo 614296 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B2227429 : Blo 614296 2227429 := bbase (se 4 (by rfl) ⟨208821, by rfl⟩ : syracuseStep 2227429 = 417643) (by norm_num)
theorem B3112181 : Blo 614296 3112181 := bbase (se 5 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 3112181 = 291767) (by norm_num)
theorem B4685525 : Blo 614296 4685525 := bbase (se 7 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 4685525 = 109817) (by norm_num)
theorem B950077 : Blo 614296 950077 := bbase (se 3 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 950077 = 356279) (by norm_num)
theorem B3211093 : Blo 614296 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B3113315 : Blo 614296 3113315 := bstep (se 1 (by rfl) ⟨2334986, by rfl⟩ : syracuseStep 3113315 = 4669973) B4669973
theorem B4817251 : Blo 614296 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B2130349 : Blo 614296 2130349 := bstep (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) B798881
theorem B4227653 : Blo 614296 4227653 := bstep (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) B792685
theorem B14615153 : Blo 614296 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B656083 : Blo 614296 656083 := bstep (se 1 (by rfl) ⟨492062, by rfl⟩ : syracuseStep 656083 = 984125) B984125
theorem B1999651 : Blo 614296 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B1868689 : Blo 614296 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B984145 : Blo 614296 984145 := bstep (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) B738109
theorem B3114125 : Blo 614296 3114125 := bstep (se 3 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 3114125 = 1167797) B1167797
theorem B1246403 : Blo 614296 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B984355 : Blo 614296 984355 := bstep (se 1 (by rfl) ⟨738266, by rfl⟩ : syracuseStep 984355 = 1476533) B1476533
theorem B984401 : Blo 614296 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B33326645 : Blo 614296 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B15238709 : Blo 614296 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B1312337 : Blo 614296 1312337 := bstep (se 2 (by rfl) ⟨492126, by rfl⟩ : syracuseStep 1312337 = 984253) B984253
theorem B1312355 : Blo 614296 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B657091 : Blo 614296 657091 := bstep (se 1 (by rfl) ⟨492818, by rfl⟩ : syracuseStep 657091 = 985637) B985637
theorem B3508109 : Blo 614296 3508109 := bstep (se 3 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 3508109 = 1315541) B1315541
theorem B952211 : Blo 614296 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B657715 : Blo 614296 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B1050995 : Blo 614296 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1477091 : Blo 614296 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B1870381 : Blo 614296 1870381 := bstep (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) B701393
theorem B1477379 : Blo 614296 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B3509041 : Blo 614296 3509041 := bstep (se 2 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 3509041 = 2631781) B2631781
theorem B985907 : Blo 614296 985907 := bstep (se 1 (by rfl) ⟨739430, by rfl⟩ : syracuseStep 985907 = 1478861) B1478861
theorem B10259341 : Blo 614296 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B2034595 : Blo 614296 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B691123 : Blo 614296 691123 := bstep (se 1 (by rfl) ⟨518342, by rfl⟩ : syracuseStep 691123 = 1036685) B1036685
theorem B691267 : Blo 614296 691267 := bstep (se 1 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 691267 = 1036901) B1036901
theorem B986195 : Blo 614296 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B1051795 : Blo 614296 1051795 := bstep (se 1 (by rfl) ⟨788846, by rfl⟩ : syracuseStep 1051795 = 1577693) B1577693
theorem B691411 : Blo 614296 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B2624845 : Blo 614296 2624845 := bstep (se 3 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 2624845 = 984317) B984317
theorem B691555 : Blo 614296 691555 := bstep (se 1 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 691555 = 1037333) B1037333
theorem B1871267 : Blo 614296 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B691699 : Blo 614296 691699 := bstep (se 1 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 691699 = 1037549) B1037549
theorem B1314353 : Blo 614296 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B1478225 : Blo 614296 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B691843 : Blo 614296 691843 := bstep (se 1 (by rfl) ⟨518882, by rfl⟩ : syracuseStep 691843 = 1037765) B1037765
theorem B1773197 : Blo 614296 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B691987 : Blo 614296 691987 := bstep (se 1 (by rfl) ⟨518990, by rfl⟩ : syracuseStep 691987 = 1037981) B1037981
theorem B986995 : Blo 614296 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B921473 : Blo 614296 921473 := bstep (se 2 (by rfl) ⟨345552, by rfl⟩ : syracuseStep 921473 = 691105) B691105
theorem B921491 : Blo 614296 921491 := bstep (se 1 (by rfl) ⟨691118, by rfl⟩ : syracuseStep 921491 = 1382237) B1382237
theorem B692131 : Blo 614296 692131 := bstep (se 1 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 692131 = 1038197) B1038197
theorem B921521 : Blo 614296 921521 := bstep (se 2 (by rfl) ⟨345570, by rfl⟩ : syracuseStep 921521 = 691141) B691141
theorem B921539 : Blo 614296 921539 := bstep (se 1 (by rfl) ⟨691154, by rfl⟩ : syracuseStep 921539 = 1382309) B1382309
theorem B626627 : Blo 614296 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B921569 : Blo 614296 921569 := bstep (se 2 (by rfl) ⟨345588, by rfl⟩ : syracuseStep 921569 = 691177) B691177
theorem B626659 : Blo 614296 626659 := bstep (se 1 (by rfl) ⟨469994, by rfl⟩ : syracuseStep 626659 = 939989) B939989
theorem B3117041 : Blo 614296 3117041 := bstep (se 2 (by rfl) ⟨1168890, by rfl⟩ : syracuseStep 3117041 = 2337781) B2337781
theorem B921587 : Blo 614296 921587 := bstep (se 1 (by rfl) ⟨691190, by rfl⟩ : syracuseStep 921587 = 1382381) B1382381
theorem B987137 : Blo 614296 987137 := bstep (se 2 (by rfl) ⟨370176, by rfl⟩ : syracuseStep 987137 = 740353) B740353
theorem B921617 : Blo 614296 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B987169 : Blo 614296 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B921635 : Blo 614296 921635 := bstep (se 1 (by rfl) ⟨691226, by rfl⟩ : syracuseStep 921635 = 1382453) B1382453
theorem B692275 : Blo 614296 692275 := bstep (se 1 (by rfl) ⟨519206, by rfl⟩ : syracuseStep 692275 = 1038413) B1038413
theorem B921665 : Blo 614296 921665 := bstep (se 2 (by rfl) ⟨345624, by rfl⟩ : syracuseStep 921665 = 691249) B691249
theorem B1314883 : Blo 614296 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B921683 : Blo 614296 921683 := bstep (se 1 (by rfl) ⟨691262, by rfl⟩ : syracuseStep 921683 = 1382525) B1382525
theorem B921713 : Blo 614296 921713 := bstep (se 2 (by rfl) ⟨345642, by rfl⟩ : syracuseStep 921713 = 691285) B691285
theorem B921731 : Blo 614296 921731 := bstep (se 1 (by rfl) ⟨691298, by rfl⟩ : syracuseStep 921731 = 1382597) B1382597
theorem B659603 : Blo 614296 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B921761 : Blo 614296 921761 := bstep (se 2 (by rfl) ⟨345660, by rfl⟩ : syracuseStep 921761 = 691321) B691321
theorem B921779 : Blo 614296 921779 := bstep (se 1 (by rfl) ⟨691334, by rfl⟩ : syracuseStep 921779 = 1382669) B1382669
theorem B692419 : Blo 614296 692419 := bstep (se 1 (by rfl) ⟨519314, by rfl⟩ : syracuseStep 692419 = 1038629) B1038629
theorem B921809 : Blo 614296 921809 := bstep (se 2 (by rfl) ⟨345678, by rfl⟩ : syracuseStep 921809 = 691357) B691357
theorem B921827 : Blo 614296 921827 := bstep (se 1 (by rfl) ⟨691370, by rfl⟩ : syracuseStep 921827 = 1382741) B1382741
theorem B3510499 : Blo 614296 3510499 := bstep (se 1 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 3510499 = 5265749) B5265749
theorem B921857 : Blo 614296 921857 := bstep (se 2 (by rfl) ⟨345696, by rfl⟩ : syracuseStep 921857 = 691393) B691393
theorem B921875 : Blo 614296 921875 := bstep (se 1 (by rfl) ⟨691406, by rfl⟩ : syracuseStep 921875 = 1382813) B1382813
theorem B921905 : Blo 614296 921905 := bstep (se 2 (by rfl) ⟨345714, by rfl⟩ : syracuseStep 921905 = 691429) B691429
theorem B921923 : Blo 614296 921923 := bstep (se 1 (by rfl) ⟨691442, by rfl⟩ : syracuseStep 921923 = 1382885) B1382885
theorem B1478993 : Blo 614296 1478993 := bstep (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) B1109245
theorem B692563 : Blo 614296 692563 := bstep (se 1 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 692563 = 1038845) B1038845
theorem B921953 : Blo 614296 921953 := bstep (se 2 (by rfl) ⟨345732, by rfl⟩ : syracuseStep 921953 = 691465) B691465
theorem B921971 : Blo 614296 921971 := bstep (se 1 (by rfl) ⟨691478, by rfl⟩ : syracuseStep 921971 = 1382957) B1382957
theorem B922001 : Blo 614296 922001 := bstep (se 2 (by rfl) ⟨345750, by rfl⟩ : syracuseStep 922001 = 691501) B691501
theorem B790931 : Blo 614296 790931 := bstep (se 1 (by rfl) ⟨593198, by rfl⟩ : syracuseStep 790931 = 1186397) B1186397
theorem B922019 : Blo 614296 922019 := bstep (se 1 (by rfl) ⟨691514, by rfl⟩ : syracuseStep 922019 = 1383029) B1383029
theorem B922049 : Blo 614296 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B922067 : Blo 614296 922067 := bstep (se 1 (by rfl) ⟨691550, by rfl⟩ : syracuseStep 922067 = 1383101) B1383101
theorem B692707 : Blo 614296 692707 := bstep (se 1 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 692707 = 1039061) B1039061
theorem B922097 : Blo 614296 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B922115 : Blo 614296 922115 := bstep (se 1 (by rfl) ⟨691586, by rfl⟩ : syracuseStep 922115 = 1383173) B1383173
theorem B889363 : Blo 614296 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B922145 : Blo 614296 922145 := bstep (se 2 (by rfl) ⟨345804, by rfl⟩ : syracuseStep 922145 = 691609) B691609
theorem B922163 : Blo 614296 922163 := bstep (se 1 (by rfl) ⟨691622, by rfl⟩ : syracuseStep 922163 = 1383245) B1383245
theorem B922193 : Blo 614296 922193 := bstep (se 2 (by rfl) ⟨345822, by rfl⟩ : syracuseStep 922193 = 691645) B691645
theorem B922211 : Blo 614296 922211 := bstep (se 1 (by rfl) ⟨691658, by rfl⟩ : syracuseStep 922211 = 1383317) B1383317
theorem B692851 : Blo 614296 692851 := bstep (se 1 (by rfl) ⟨519638, by rfl⟩ : syracuseStep 692851 = 1039277) B1039277
theorem B922241 : Blo 614296 922241 := bstep (se 2 (by rfl) ⟨345840, by rfl⟩ : syracuseStep 922241 = 691681) B691681
theorem B2101891 : Blo 614296 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B922259 : Blo 614296 922259 := bstep (se 1 (by rfl) ⟨691694, by rfl⟩ : syracuseStep 922259 = 1383389) B1383389
theorem B922289 : Blo 614296 922289 := bstep (se 2 (by rfl) ⟨345858, by rfl⟩ : syracuseStep 922289 = 691717) B691717
theorem B922307 : Blo 614296 922307 := bstep (se 1 (by rfl) ⟨691730, by rfl⟩ : syracuseStep 922307 = 1383461) B1383461
theorem B922337 : Blo 614296 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B3511025 : Blo 614296 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B922355 : Blo 614296 922355 := bstep (se 1 (by rfl) ⟨691766, by rfl⟩ : syracuseStep 922355 = 1383533) B1383533
theorem B692995 : Blo 614296 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B922385 : Blo 614296 922385 := bstep (se 2 (by rfl) ⟨345894, by rfl⟩ : syracuseStep 922385 = 691789) B691789
theorem B922403 : Blo 614296 922403 := bstep (se 1 (by rfl) ⟨691802, by rfl⟩ : syracuseStep 922403 = 1383605) B1383605
theorem B1970993 : Blo 614296 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B922433 : Blo 614296 922433 := bstep (se 2 (by rfl) ⟨345912, by rfl⟩ : syracuseStep 922433 = 691825) B691825
theorem B922451 : Blo 614296 922451 := bstep (se 1 (by rfl) ⟨691838, by rfl⟩ : syracuseStep 922451 = 1383677) B1383677
theorem B922481 : Blo 614296 922481 := bstep (se 2 (by rfl) ⟨345930, by rfl⟩ : syracuseStep 922481 = 691861) B691861
theorem B13308785 : Blo 614296 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B922499 : Blo 614296 922499 := bstep (se 1 (by rfl) ⟨691874, by rfl⟩ : syracuseStep 922499 = 1383749) B1383749
theorem B693139 : Blo 614296 693139 := bstep (se 1 (by rfl) ⟨519854, by rfl⟩ : syracuseStep 693139 = 1039709) B1039709
theorem B922529 : Blo 614296 922529 := bstep (se 2 (by rfl) ⟨345948, by rfl⟩ : syracuseStep 922529 = 691897) B691897
theorem B922547 : Blo 614296 922547 := bstep (se 1 (by rfl) ⟨691910, by rfl⟩ : syracuseStep 922547 = 1383821) B1383821
theorem B988097 : Blo 614296 988097 := bstep (se 2 (by rfl) ⟨370536, by rfl⟩ : syracuseStep 988097 = 741073) B741073
theorem B922577 : Blo 614296 922577 := bstep (se 2 (by rfl) ⟨345966, by rfl⟩ : syracuseStep 922577 = 691933) B691933
theorem B922595 : Blo 614296 922595 := bstep (se 1 (by rfl) ⟨691946, by rfl⟩ : syracuseStep 922595 = 1383893) B1383893
theorem B922625 : Blo 614296 922625 := bstep (se 2 (by rfl) ⟨345984, by rfl⟩ : syracuseStep 922625 = 691969) B691969
theorem B922643 : Blo 614296 922643 := bstep (se 1 (by rfl) ⟨691982, by rfl⟩ : syracuseStep 922643 = 1383965) B1383965
theorem B693283 : Blo 614296 693283 := bstep (se 1 (by rfl) ⟨519962, by rfl⟩ : syracuseStep 693283 = 1039925) B1039925
theorem B922673 : Blo 614296 922673 := bstep (se 2 (by rfl) ⟨346002, by rfl⟩ : syracuseStep 922673 = 692005) B692005
theorem B922691 : Blo 614296 922691 := bstep (se 1 (by rfl) ⟨692018, by rfl⟩ : syracuseStep 922691 = 1384037) B1384037
theorem B922721 : Blo 614296 922721 := bstep (se 2 (by rfl) ⟨346020, by rfl⟩ : syracuseStep 922721 = 692041) B692041
theorem B922739 : Blo 614296 922739 := bstep (se 1 (by rfl) ⟨692054, by rfl⟩ : syracuseStep 922739 = 1384109) B1384109
theorem B922769 : Blo 614296 922769 := bstep (se 2 (by rfl) ⟨346038, by rfl⟩ : syracuseStep 922769 = 692077) B692077
theorem B922787 : Blo 614296 922787 := bstep (se 1 (by rfl) ⟨692090, by rfl⟩ : syracuseStep 922787 = 1384181) B1384181
theorem B693427 : Blo 614296 693427 := bstep (se 1 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 693427 = 1040141) B1040141
theorem B922817 : Blo 614296 922817 := bstep (se 2 (by rfl) ⟨346056, by rfl⟩ : syracuseStep 922817 = 692113) B692113
theorem B9999557 : Blo 614296 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B922835 : Blo 614296 922835 := bstep (se 1 (by rfl) ⟨692126, by rfl⟩ : syracuseStep 922835 = 1384253) B1384253
theorem B922865 : Blo 614296 922865 := bstep (se 2 (by rfl) ⟨346074, by rfl⟩ : syracuseStep 922865 = 692149) B692149
theorem B922883 : Blo 614296 922883 := bstep (se 1 (by rfl) ⟨692162, by rfl⟩ : syracuseStep 922883 = 1384325) B1384325
theorem B922913 : Blo 614296 922913 := bstep (se 2 (by rfl) ⟨346092, by rfl⟩ : syracuseStep 922913 = 692185) B692185
theorem B922931 : Blo 614296 922931 := bstep (se 1 (by rfl) ⟨692198, by rfl⟩ : syracuseStep 922931 = 1384397) B1384397
theorem B693571 : Blo 614296 693571 := bstep (se 1 (by rfl) ⟨520178, by rfl⟩ : syracuseStep 693571 = 1040357) B1040357
theorem B922961 : Blo 614296 922961 := bstep (se 2 (by rfl) ⟨346110, by rfl⟩ : syracuseStep 922961 = 692221) B692221
theorem B922979 : Blo 614296 922979 := bstep (se 1 (by rfl) ⟨692234, by rfl⟩ : syracuseStep 922979 = 1384469) B1384469
theorem B923009 : Blo 614296 923009 := bstep (se 2 (by rfl) ⟨346128, by rfl⟩ : syracuseStep 923009 = 692257) B692257
theorem B923027 : Blo 614296 923027 := bstep (se 1 (by rfl) ⟨692270, by rfl⟩ : syracuseStep 923027 = 1384541) B1384541
theorem B3118499 : Blo 614296 3118499 := bstep (se 1 (by rfl) ⟨2338874, by rfl⟩ : syracuseStep 3118499 = 4677749) B4677749
theorem B923057 : Blo 614296 923057 := bstep (se 2 (by rfl) ⟨346146, by rfl⟩ : syracuseStep 923057 = 692293) B692293
theorem B923075 : Blo 614296 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B693715 : Blo 614296 693715 := bstep (se 1 (by rfl) ⟨520286, by rfl⟩ : syracuseStep 693715 = 1040573) B1040573
theorem B923105 : Blo 614296 923105 := bstep (se 2 (by rfl) ⟨346164, by rfl⟩ : syracuseStep 923105 = 692329) B692329
theorem B923123 : Blo 614296 923123 := bstep (se 1 (by rfl) ⟨692342, by rfl⟩ : syracuseStep 923123 = 1384685) B1384685
theorem B923153 : Blo 614296 923153 := bstep (se 2 (by rfl) ⟨346182, by rfl⟩ : syracuseStep 923153 = 692365) B692365
theorem B1316369 : Blo 614296 1316369 := bstep (se 2 (by rfl) ⟨493638, by rfl⟩ : syracuseStep 1316369 = 987277) B987277
theorem B923171 : Blo 614296 923171 := bstep (se 1 (by rfl) ⟨692378, by rfl⟩ : syracuseStep 923171 = 1384757) B1384757
theorem B1316387 : Blo 614296 1316387 := bstep (se 1 (by rfl) ⟨987290, by rfl⟩ : syracuseStep 1316387 = 1974581) B1974581
theorem B923201 : Blo 614296 923201 := bstep (se 2 (by rfl) ⟨346200, by rfl⟩ : syracuseStep 923201 = 692401) B692401
theorem B923219 : Blo 614296 923219 := bstep (se 1 (by rfl) ⟨692414, by rfl⟩ : syracuseStep 923219 = 1384829) B1384829
theorem B693859 : Blo 614296 693859 := bstep (se 1 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 693859 = 1040789) B1040789
theorem B923249 : Blo 614296 923249 := bstep (se 2 (by rfl) ⟨346218, by rfl⟩ : syracuseStep 923249 = 692437) B692437
theorem B923267 : Blo 614296 923267 := bstep (se 1 (by rfl) ⟨692450, by rfl⟩ : syracuseStep 923267 = 1384901) B1384901
theorem B923297 : Blo 614296 923297 := bstep (se 2 (by rfl) ⟨346236, by rfl⟩ : syracuseStep 923297 = 692473) B692473
theorem B923315 : Blo 614296 923315 := bstep (se 1 (by rfl) ⟨692486, by rfl⟩ : syracuseStep 923315 = 1384973) B1384973
theorem B923345 : Blo 614296 923345 := bstep (se 2 (by rfl) ⟨346254, by rfl⟩ : syracuseStep 923345 = 692509) B692509
theorem B923363 : Blo 614296 923363 := bstep (se 1 (by rfl) ⟨692522, by rfl⟩ : syracuseStep 923363 = 1385045) B1385045
theorem B694003 : Blo 614296 694003 := bstep (se 1 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 694003 = 1041005) B1041005
theorem B923393 : Blo 614296 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B988931 : Blo 614296 988931 := bstep (se 1 (by rfl) ⟨741698, by rfl⟩ : syracuseStep 988931 = 1483397) B1483397
theorem B923411 : Blo 614296 923411 := bstep (se 1 (by rfl) ⟨692558, by rfl⟩ : syracuseStep 923411 = 1385117) B1385117
theorem B923441 : Blo 614296 923441 := bstep (se 2 (by rfl) ⟨346290, by rfl⟩ : syracuseStep 923441 = 692581) B692581
theorem B923459 : Blo 614296 923459 := bstep (se 1 (by rfl) ⟨692594, by rfl⟩ : syracuseStep 923459 = 1385189) B1385189
theorem B923489 : Blo 614296 923489 := bstep (se 2 (by rfl) ⟨346308, by rfl⟩ : syracuseStep 923489 = 692617) B692617
theorem B923507 : Blo 614296 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B694147 : Blo 614296 694147 := bstep (se 1 (by rfl) ⟨520610, by rfl⟩ : syracuseStep 694147 = 1041221) B1041221
theorem B923537 : Blo 614296 923537 := bstep (se 2 (by rfl) ⟨346326, by rfl⟩ : syracuseStep 923537 = 692653) B692653
theorem B923555 : Blo 614296 923555 := bstep (se 1 (by rfl) ⟨692666, by rfl⟩ : syracuseStep 923555 = 1385333) B1385333
theorem B923585 : Blo 614296 923585 := bstep (se 2 (by rfl) ⟨346344, by rfl⟩ : syracuseStep 923585 = 692689) B692689
theorem B923603 : Blo 614296 923603 := bstep (se 1 (by rfl) ⟨692702, by rfl⟩ : syracuseStep 923603 = 1385405) B1385405
theorem B923633 : Blo 614296 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B923651 : Blo 614296 923651 := bstep (se 1 (by rfl) ⟨692738, by rfl⟩ : syracuseStep 923651 = 1385477) B1385477
theorem B1382417 : Blo 614296 1382417 := bstep (se 2 (by rfl) ⟨518406, by rfl⟩ : syracuseStep 1382417 = 1036813) B1036813
theorem B694291 : Blo 614296 694291 := bstep (se 1 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 694291 = 1041437) B1041437
theorem B923681 : Blo 614296 923681 := bstep (se 2 (by rfl) ⟨346380, by rfl⟩ : syracuseStep 923681 = 692761) B692761
theorem B1382435 : Blo 614296 1382435 := bstep (se 1 (by rfl) ⟨1036826, by rfl⟩ : syracuseStep 1382435 = 2073653) B2073653
theorem B989219 : Blo 614296 989219 := bstep (se 1 (by rfl) ⟨741914, by rfl⟩ : syracuseStep 989219 = 1483829) B1483829
theorem B923699 : Blo 614296 923699 := bstep (se 1 (by rfl) ⟨692774, by rfl⟩ : syracuseStep 923699 = 1385549) B1385549
theorem B923729 : Blo 614296 923729 := bstep (se 2 (by rfl) ⟨346398, by rfl⟩ : syracuseStep 923729 = 692797) B692797
theorem B923747 : Blo 614296 923747 := bstep (se 1 (by rfl) ⟨692810, by rfl⟩ : syracuseStep 923747 = 1385621) B1385621
theorem B923777 : Blo 614296 923777 := bstep (se 2 (by rfl) ⟨346416, by rfl⟩ : syracuseStep 923777 = 692833) B692833
theorem B923795 : Blo 614296 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B1054883 : Blo 614296 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B3512483 : Blo 614296 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B694435 : Blo 614296 694435 := bstep (se 1 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 694435 = 1041653) B1041653
theorem B923825 : Blo 614296 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B923843 : Blo 614296 923843 := bstep (se 1 (by rfl) ⟨692882, by rfl⟩ : syracuseStep 923843 = 1385765) B1385765
theorem B3119309 : Blo 614296 3119309 := bstep (se 3 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 3119309 = 1169741) B1169741
theorem B923873 : Blo 614296 923873 := bstep (se 2 (by rfl) ⟨346452, by rfl⟩ : syracuseStep 923873 = 692905) B692905
theorem B923891 : Blo 614296 923891 := bstep (se 1 (by rfl) ⟨692918, by rfl⟩ : syracuseStep 923891 = 1385837) B1385837
theorem B989443 : Blo 614296 989443 := bstep (se 1 (by rfl) ⟨742082, by rfl⟩ : syracuseStep 989443 = 1484165) B1484165
theorem B923921 : Blo 614296 923921 := bstep (se 2 (by rfl) ⟨346470, by rfl⟩ : syracuseStep 923921 = 692941) B692941
theorem B891169 : Blo 614296 891169 := bstep (se 2 (by rfl) ⟨334188, by rfl⟩ : syracuseStep 891169 = 668377) B668377
theorem B923939 : Blo 614296 923939 := bstep (se 1 (by rfl) ⟨692954, by rfl⟩ : syracuseStep 923939 = 1385909) B1385909
theorem B1382705 : Blo 614296 1382705 := bstep (se 2 (by rfl) ⟨518514, by rfl⟩ : syracuseStep 1382705 = 1037029) B1037029
theorem B3742001 : Blo 614296 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B694579 : Blo 614296 694579 := bstep (se 1 (by rfl) ⟨520934, by rfl⟩ : syracuseStep 694579 = 1041869) B1041869
theorem B923969 : Blo 614296 923969 := bstep (se 2 (by rfl) ⟨346488, by rfl⟩ : syracuseStep 923969 = 692977) B692977
theorem B1382723 : Blo 614296 1382723 := bstep (se 1 (by rfl) ⟨1037042, by rfl⟩ : syracuseStep 1382723 = 2074085) B2074085
theorem B923987 : Blo 614296 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B924017 : Blo 614296 924017 := bstep (se 2 (by rfl) ⟨346506, by rfl⟩ : syracuseStep 924017 = 693013) B693013
theorem B924035 : Blo 614296 924035 := bstep (se 1 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 924035 = 1386053) B1386053
theorem B924065 : Blo 614296 924065 := bstep (se 2 (by rfl) ⟨346524, by rfl⟩ : syracuseStep 924065 = 693049) B693049
theorem B924083 : Blo 614296 924083 := bstep (se 1 (by rfl) ⟨693062, by rfl⟩ : syracuseStep 924083 = 1386125) B1386125
theorem B1579459 : Blo 614296 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B694723 : Blo 614296 694723 := bstep (se 1 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 694723 = 1042085) B1042085
theorem B924113 : Blo 614296 924113 := bstep (se 2 (by rfl) ⟨346542, by rfl⟩ : syracuseStep 924113 = 693085) B693085
theorem B924131 : Blo 614296 924131 := bstep (se 1 (by rfl) ⟨693098, by rfl⟩ : syracuseStep 924131 = 1386197) B1386197
theorem B924161 : Blo 614296 924161 := bstep (se 2 (by rfl) ⟨346560, by rfl⟩ : syracuseStep 924161 = 693121) B693121
theorem B924179 : Blo 614296 924179 := bstep (se 1 (by rfl) ⟨693134, by rfl⟩ : syracuseStep 924179 = 1386269) B1386269
theorem B924209 : Blo 614296 924209 := bstep (se 2 (by rfl) ⟨346578, by rfl⟩ : syracuseStep 924209 = 693157) B693157
theorem B924227 : Blo 614296 924227 := bstep (se 1 (by rfl) ⟨693170, by rfl⟩ : syracuseStep 924227 = 1386341) B1386341
theorem B1382993 : Blo 614296 1382993 := bstep (se 2 (by rfl) ⟨518622, by rfl⟩ : syracuseStep 1382993 = 1037245) B1037245
theorem B694867 : Blo 614296 694867 := bstep (se 1 (by rfl) ⟨521150, by rfl⟩ : syracuseStep 694867 = 1042301) B1042301
theorem B924257 : Blo 614296 924257 := bstep (se 2 (by rfl) ⟨346596, by rfl⟩ : syracuseStep 924257 = 693193) B693193
theorem B1383011 : Blo 614296 1383011 := bstep (se 1 (by rfl) ⟨1037258, by rfl⟩ : syracuseStep 1383011 = 2074517) B2074517
theorem B924275 : Blo 614296 924275 := bstep (se 1 (by rfl) ⟨693206, by rfl⟩ : syracuseStep 924275 = 1386413) B1386413
theorem B924305 : Blo 614296 924305 := bstep (se 2 (by rfl) ⟨346614, by rfl⟩ : syracuseStep 924305 = 693229) B693229
theorem B924323 : Blo 614296 924323 := bstep (se 1 (by rfl) ⟨693242, by rfl⟩ : syracuseStep 924323 = 1386485) B1386485
theorem B2005681 : Blo 614296 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B924353 : Blo 614296 924353 := bstep (se 2 (by rfl) ⟨346632, by rfl⟩ : syracuseStep 924353 = 693265) B693265
theorem B924371 : Blo 614296 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B695011 : Blo 614296 695011 := bstep (se 1 (by rfl) ⟨521258, by rfl⟩ : syracuseStep 695011 = 1042517) B1042517
theorem B924401 : Blo 614296 924401 := bstep (se 2 (by rfl) ⟨346650, by rfl⟩ : syracuseStep 924401 = 693301) B693301
theorem B1317617 : Blo 614296 1317617 := bstep (se 2 (by rfl) ⟨494106, by rfl⟩ : syracuseStep 1317617 = 988213) B988213
theorem B924419 : Blo 614296 924419 := bstep (se 1 (by rfl) ⟨693314, by rfl⟩ : syracuseStep 924419 = 1386629) B1386629
theorem B924449 : Blo 614296 924449 := bstep (se 2 (by rfl) ⟨346668, by rfl⟩ : syracuseStep 924449 = 693337) B693337
theorem B924467 : Blo 614296 924467 := bstep (se 1 (by rfl) ⟨693350, by rfl⟩ : syracuseStep 924467 = 1386701) B1386701
theorem B1973069 : Blo 614296 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B924497 : Blo 614296 924497 := bstep (se 2 (by rfl) ⟨346686, by rfl⟩ : syracuseStep 924497 = 693373) B693373
theorem B924515 : Blo 614296 924515 := bstep (se 1 (by rfl) ⟨693386, by rfl⟩ : syracuseStep 924515 = 1386773) B1386773
theorem B1383281 : Blo 614296 1383281 := bstep (se 2 (by rfl) ⟨518730, by rfl⟩ : syracuseStep 1383281 = 1037461) B1037461
theorem B695155 : Blo 614296 695155 := bstep (se 1 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 695155 = 1042733) B1042733
theorem B924545 : Blo 614296 924545 := bstep (se 2 (by rfl) ⟨346704, by rfl⟩ : syracuseStep 924545 = 693409) B693409
theorem B1383299 : Blo 614296 1383299 := bstep (se 1 (by rfl) ⟨1037474, by rfl⟩ : syracuseStep 1383299 = 2074949) B2074949
theorem B924563 : Blo 614296 924563 := bstep (se 1 (by rfl) ⟨693422, by rfl⟩ : syracuseStep 924563 = 1386845) B1386845
theorem B924593 : Blo 614296 924593 := bstep (se 2 (by rfl) ⟨346722, by rfl⟩ : syracuseStep 924593 = 693445) B693445
theorem B924611 : Blo 614296 924611 := bstep (se 1 (by rfl) ⟨693458, by rfl⟩ : syracuseStep 924611 = 1386917) B1386917
theorem B990161 : Blo 614296 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B924641 : Blo 614296 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B2104301 : Blo 614296 2104301 := bstep (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) B789113
theorem B2333681 : Blo 614296 2333681 := bstep (se 2 (by rfl) ⟨875130, by rfl⟩ : syracuseStep 2333681 = 1750261) B1750261
theorem B924659 : Blo 614296 924659 := bstep (se 1 (by rfl) ⟨693494, by rfl⟩ : syracuseStep 924659 = 1386989) B1386989
theorem B695299 : Blo 614296 695299 := bstep (se 1 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 695299 = 1042949) B1042949
theorem B924689 : Blo 614296 924689 := bstep (se 2 (by rfl) ⟨346758, by rfl⟩ : syracuseStep 924689 = 693517) B693517
theorem B924707 : Blo 614296 924707 := bstep (se 1 (by rfl) ⟨693530, by rfl⟩ : syracuseStep 924707 = 1387061) B1387061
theorem B924737 : Blo 614296 924737 := bstep (se 2 (by rfl) ⟨346776, by rfl⟩ : syracuseStep 924737 = 693553) B693553
theorem B2530381 : Blo 614296 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B924755 : Blo 614296 924755 := bstep (se 1 (by rfl) ⟨693566, by rfl⟩ : syracuseStep 924755 = 1387133) B1387133
theorem B924785 : Blo 614296 924785 := bstep (se 2 (by rfl) ⟨346794, by rfl⟩ : syracuseStep 924785 = 693589) B693589
theorem B1055873 : Blo 614296 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B924803 : Blo 614296 924803 := bstep (se 1 (by rfl) ⟨693602, by rfl⟩ : syracuseStep 924803 = 1387205) B1387205
theorem B1383569 : Blo 614296 1383569 := bstep (se 2 (by rfl) ⟨518838, by rfl⟩ : syracuseStep 1383569 = 1037677) B1037677
theorem B1875089 : Blo 614296 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B695443 : Blo 614296 695443 := bstep (se 1 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 695443 = 1043165) B1043165
theorem B990353 : Blo 614296 990353 := bstep (se 2 (by rfl) ⟨371382, by rfl⟩ : syracuseStep 990353 = 742765) B742765
theorem B924833 : Blo 614296 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B1383587 : Blo 614296 1383587 := bstep (se 1 (by rfl) ⟨1037690, by rfl⟩ : syracuseStep 1383587 = 2075381) B2075381
theorem B924851 : Blo 614296 924851 := bstep (se 1 (by rfl) ⟨693638, by rfl⟩ : syracuseStep 924851 = 1387277) B1387277
theorem B924881 : Blo 614296 924881 := bstep (se 2 (by rfl) ⟨346830, by rfl⟩ : syracuseStep 924881 = 693661) B693661
theorem B924899 : Blo 614296 924899 := bstep (se 1 (by rfl) ⟨693674, by rfl⟩ : syracuseStep 924899 = 1387349) B1387349
theorem B924929 : Blo 614296 924929 := bstep (se 2 (by rfl) ⟨346848, by rfl⟩ : syracuseStep 924929 = 693697) B693697
theorem B924947 : Blo 614296 924947 := bstep (se 1 (by rfl) ⟨693710, by rfl⟩ : syracuseStep 924947 = 1387421) B1387421
theorem B924977 : Blo 614296 924977 := bstep (se 2 (by rfl) ⟨346866, by rfl⟩ : syracuseStep 924977 = 693733) B693733
theorem B924995 : Blo 614296 924995 := bstep (se 1 (by rfl) ⟨693746, by rfl⟩ : syracuseStep 924995 = 1387493) B1387493
theorem B925025 : Blo 614296 925025 := bstep (se 2 (by rfl) ⟨346884, by rfl⟩ : syracuseStep 925025 = 693769) B693769
theorem B925043 : Blo 614296 925043 := bstep (se 1 (by rfl) ⟨693782, by rfl⟩ : syracuseStep 925043 = 1387565) B1387565
theorem B925073 : Blo 614296 925073 := bstep (se 2 (by rfl) ⟨346902, by rfl⟩ : syracuseStep 925073 = 693805) B693805
theorem B925091 : Blo 614296 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B1383857 : Blo 614296 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B925121 : Blo 614296 925121 := bstep (se 2 (by rfl) ⟨346920, by rfl⟩ : syracuseStep 925121 = 693841) B693841
theorem B1383875 : Blo 614296 1383875 := bstep (se 1 (by rfl) ⟨1037906, by rfl⟩ : syracuseStep 1383875 = 2075813) B2075813
theorem B925139 : Blo 614296 925139 := bstep (se 1 (by rfl) ⟨693854, by rfl⟩ : syracuseStep 925139 = 1387709) B1387709
theorem B925169 : Blo 614296 925169 := bstep (se 2 (by rfl) ⟨346938, by rfl⟩ : syracuseStep 925169 = 693877) B693877
theorem B925187 : Blo 614296 925187 := bstep (se 1 (by rfl) ⟨693890, by rfl⟩ : syracuseStep 925187 = 1387781) B1387781
theorem B925217 : Blo 614296 925217 := bstep (se 2 (by rfl) ⟨346956, by rfl⟩ : syracuseStep 925217 = 693913) B693913
theorem B2629169 : Blo 614296 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B925235 : Blo 614296 925235 := bstep (se 1 (by rfl) ⟨693926, by rfl⟩ : syracuseStep 925235 = 1387853) B1387853
theorem B925265 : Blo 614296 925265 := bstep (se 2 (by rfl) ⟨346974, by rfl⟩ : syracuseStep 925265 = 693949) B693949
theorem B2629219 : Blo 614296 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B925283 : Blo 614296 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B925313 : Blo 614296 925313 := bstep (se 2 (by rfl) ⟨346992, by rfl⟩ : syracuseStep 925313 = 693985) B693985
theorem B925331 : Blo 614296 925331 := bstep (se 1 (by rfl) ⟨693998, by rfl⟩ : syracuseStep 925331 = 1387997) B1387997
theorem B925361 : Blo 614296 925361 := bstep (se 2 (by rfl) ⟨347010, by rfl⟩ : syracuseStep 925361 = 694021) B694021
theorem B925379 : Blo 614296 925379 := bstep (se 1 (by rfl) ⟨694034, by rfl⟩ : syracuseStep 925379 = 1388069) B1388069
theorem B1973965 : Blo 614296 1973965 := bstep (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) B740237
theorem B1384145 : Blo 614296 1384145 := bstep (se 2 (by rfl) ⟨519054, by rfl⟩ : syracuseStep 1384145 = 1038109) B1038109
theorem B925409 : Blo 614296 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B1384163 : Blo 614296 1384163 := bstep (se 1 (by rfl) ⟨1038122, by rfl⟩ : syracuseStep 1384163 = 2076245) B2076245
theorem B925427 : Blo 614296 925427 := bstep (se 1 (by rfl) ⟨694070, by rfl⟩ : syracuseStep 925427 = 1388141) B1388141
theorem B925457 : Blo 614296 925457 := bstep (se 2 (by rfl) ⟨347046, by rfl⟩ : syracuseStep 925457 = 694093) B694093
theorem B925475 : Blo 614296 925475 := bstep (se 1 (by rfl) ⟨694106, by rfl⟩ : syracuseStep 925475 = 1388213) B1388213
theorem B925505 : Blo 614296 925505 := bstep (se 2 (by rfl) ⟨347064, by rfl⟩ : syracuseStep 925505 = 694129) B694129
theorem B925523 : Blo 614296 925523 := bstep (se 1 (by rfl) ⟨694142, by rfl⟩ : syracuseStep 925523 = 1388285) B1388285
theorem B925553 : Blo 614296 925553 := bstep (se 2 (by rfl) ⟨347082, by rfl⟩ : syracuseStep 925553 = 694165) B694165
theorem B925571 : Blo 614296 925571 := bstep (se 1 (by rfl) ⟨694178, by rfl⟩ : syracuseStep 925571 = 1388357) B1388357
theorem B925601 : Blo 614296 925601 := bstep (se 2 (by rfl) ⟨347100, by rfl⟩ : syracuseStep 925601 = 694201) B694201
theorem B2957219 : Blo 614296 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B925619 : Blo 614296 925619 := bstep (se 1 (by rfl) ⟨694214, by rfl⟩ : syracuseStep 925619 = 1388429) B1388429
theorem B925649 : Blo 614296 925649 := bstep (se 2 (by rfl) ⟨347118, by rfl⟩ : syracuseStep 925649 = 694237) B694237
theorem B925667 : Blo 614296 925667 := bstep (se 1 (by rfl) ⟨694250, by rfl⟩ : syracuseStep 925667 = 1388501) B1388501
theorem B1384433 : Blo 614296 1384433 := bstep (se 2 (by rfl) ⟨519162, by rfl⟩ : syracuseStep 1384433 = 1038325) B1038325
theorem B925697 : Blo 614296 925697 := bstep (se 2 (by rfl) ⟨347136, by rfl⟩ : syracuseStep 925697 = 694273) B694273
theorem B1384451 : Blo 614296 1384451 := bstep (se 1 (by rfl) ⟨1038338, by rfl⟩ : syracuseStep 1384451 = 2076677) B2076677
theorem B3514373 : Blo 614296 3514373 := bstep (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) B658945
theorem B925715 : Blo 614296 925715 := bstep (se 1 (by rfl) ⟨694286, by rfl⟩ : syracuseStep 925715 = 1388573) B1388573
theorem B1187875 : Blo 614296 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B925745 : Blo 614296 925745 := bstep (se 2 (by rfl) ⟨347154, by rfl⟩ : syracuseStep 925745 = 694309) B694309
theorem B925763 : Blo 614296 925763 := bstep (se 1 (by rfl) ⟨694322, by rfl⟩ : syracuseStep 925763 = 1388645) B1388645
theorem B925793 : Blo 614296 925793 := bstep (se 2 (by rfl) ⟨347172, by rfl⟩ : syracuseStep 925793 = 694345) B694345
theorem B925811 : Blo 614296 925811 := bstep (se 1 (by rfl) ⟨694358, by rfl⟩ : syracuseStep 925811 = 1388717) B1388717
theorem B925841 : Blo 614296 925841 := bstep (se 2 (by rfl) ⟨347190, by rfl⟩ : syracuseStep 925841 = 694381) B694381
theorem B925859 : Blo 614296 925859 := bstep (se 1 (by rfl) ⟨694394, by rfl⟩ : syracuseStep 925859 = 1388789) B1388789
theorem B925889 : Blo 614296 925889 := bstep (se 2 (by rfl) ⟨347208, by rfl⟩ : syracuseStep 925889 = 694417) B694417
theorem B925907 : Blo 614296 925907 := bstep (se 1 (by rfl) ⟨694430, by rfl⟩ : syracuseStep 925907 = 1388861) B1388861
theorem B925937 : Blo 614296 925937 := bstep (se 2 (by rfl) ⟨347226, by rfl⟩ : syracuseStep 925937 = 694453) B694453
theorem B925955 : Blo 614296 925955 := bstep (se 1 (by rfl) ⟨694466, by rfl⟩ : syracuseStep 925955 = 1388933) B1388933
theorem B1319171 : Blo 614296 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B1384721 : Blo 614296 1384721 := bstep (se 2 (by rfl) ⟨519270, by rfl⟩ : syracuseStep 1384721 = 1038541) B1038541
theorem B925985 : Blo 614296 925985 := bstep (se 2 (by rfl) ⟨347244, by rfl⟩ : syracuseStep 925985 = 694489) B694489
theorem B1384739 : Blo 614296 1384739 := bstep (se 1 (by rfl) ⟨1038554, by rfl⟩ : syracuseStep 1384739 = 2077109) B2077109
theorem B926003 : Blo 614296 926003 := bstep (se 1 (by rfl) ⟨694502, by rfl⟩ : syracuseStep 926003 = 1389005) B1389005
theorem B926033 : Blo 614296 926033 := bstep (se 2 (by rfl) ⟨347262, by rfl⟩ : syracuseStep 926033 = 694525) B694525
theorem B926051 : Blo 614296 926051 := bstep (se 1 (by rfl) ⟨694538, by rfl⟩ : syracuseStep 926051 = 1389077) B1389077
theorem B926081 : Blo 614296 926081 := bstep (se 2 (by rfl) ⟨347280, by rfl⟩ : syracuseStep 926081 = 694561) B694561
theorem B926099 : Blo 614296 926099 := bstep (se 1 (by rfl) ⟨694574, by rfl⟩ : syracuseStep 926099 = 1389149) B1389149
theorem B2335139 : Blo 614296 2335139 := bstep (se 1 (by rfl) ⟨1751354, by rfl⟩ : syracuseStep 2335139 = 3502709) B3502709
theorem B926129 : Blo 614296 926129 := bstep (se 2 (by rfl) ⟨347298, by rfl⟩ : syracuseStep 926129 = 694597) B694597
theorem B926147 : Blo 614296 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B926177 : Blo 614296 926177 := bstep (se 2 (by rfl) ⟨347316, by rfl⟩ : syracuseStep 926177 = 694633) B694633
theorem B926195 : Blo 614296 926195 := bstep (se 1 (by rfl) ⟨694646, by rfl⟩ : syracuseStep 926195 = 1389293) B1389293
theorem B926225 : Blo 614296 926225 := bstep (se 2 (by rfl) ⟨347334, by rfl⟩ : syracuseStep 926225 = 694669) B694669
theorem B926243 : Blo 614296 926243 := bstep (se 1 (by rfl) ⟨694682, by rfl⟩ : syracuseStep 926243 = 1389365) B1389365
theorem B3154481 : Blo 614296 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B1385009 : Blo 614296 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B926273 : Blo 614296 926273 := bstep (se 2 (by rfl) ⟨347352, by rfl⟩ : syracuseStep 926273 = 694705) B694705
theorem B1385027 : Blo 614296 1385027 := bstep (se 1 (by rfl) ⟨1038770, by rfl⟩ : syracuseStep 1385027 = 2077541) B2077541
theorem B1974851 : Blo 614296 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B926291 : Blo 614296 926291 := bstep (se 1 (by rfl) ⟨694718, by rfl⟩ : syracuseStep 926291 = 1389437) B1389437
theorem B926321 : Blo 614296 926321 := bstep (se 2 (by rfl) ⟨347370, by rfl⟩ : syracuseStep 926321 = 694741) B694741
theorem B926339 : Blo 614296 926339 := bstep (se 1 (by rfl) ⟨694754, by rfl⟩ : syracuseStep 926339 = 1389509) B1389509
theorem B1876621 : Blo 614296 1876621 := bstep (se 3 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 1876621 = 703733) B703733
theorem B926369 : Blo 614296 926369 := bstep (se 2 (by rfl) ⟨347388, by rfl⟩ : syracuseStep 926369 = 694777) B694777
theorem B926387 : Blo 614296 926387 := bstep (se 1 (by rfl) ⟨694790, by rfl⟩ : syracuseStep 926387 = 1389581) B1389581
theorem B1057475 : Blo 614296 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B926417 : Blo 614296 926417 := bstep (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) B694813
theorem B926435 : Blo 614296 926435 := bstep (se 1 (by rfl) ⟨694826, by rfl⟩ : syracuseStep 926435 = 1389653) B1389653
theorem B1876717 : Blo 614296 1876717 := bstep (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) B703769
theorem B2073329 : Blo 614296 2073329 := bstep (se 2 (by rfl) ⟨777498, by rfl⟩ : syracuseStep 2073329 = 1554997) B1554997
theorem B926465 : Blo 614296 926465 := bstep (se 2 (by rfl) ⟨347424, by rfl⟩ : syracuseStep 926465 = 694849) B694849
theorem B926483 : Blo 614296 926483 := bstep (se 1 (by rfl) ⟨694862, by rfl⟩ : syracuseStep 926483 = 1389725) B1389725
theorem B926513 : Blo 614296 926513 := bstep (se 2 (by rfl) ⟨347442, by rfl⟩ : syracuseStep 926513 = 694885) B694885
theorem B926531 : Blo 614296 926531 := bstep (se 1 (by rfl) ⟨694898, by rfl⟩ : syracuseStep 926531 = 1389797) B1389797
theorem B1385297 : Blo 614296 1385297 := bstep (se 2 (by rfl) ⟨519486, by rfl⟩ : syracuseStep 1385297 = 1038973) B1038973
theorem B926561 : Blo 614296 926561 := bstep (se 2 (by rfl) ⟨347460, by rfl⟩ : syracuseStep 926561 = 694921) B694921
theorem B1385315 : Blo 614296 1385315 := bstep (se 1 (by rfl) ⟨1038986, by rfl⟩ : syracuseStep 1385315 = 2077973) B2077973
theorem B926579 : Blo 614296 926579 := bstep (se 1 (by rfl) ⟨694934, by rfl⟩ : syracuseStep 926579 = 1389869) B1389869
theorem B926609 : Blo 614296 926609 := bstep (se 2 (by rfl) ⟨347478, by rfl⟩ : syracuseStep 926609 = 694957) B694957
theorem B926627 : Blo 614296 926627 := bstep (se 1 (by rfl) ⟨694970, by rfl⟩ : syracuseStep 926627 = 1389941) B1389941
theorem B926657 : Blo 614296 926657 := bstep (se 2 (by rfl) ⟨347496, by rfl⟩ : syracuseStep 926657 = 694993) B694993
theorem B926675 : Blo 614296 926675 := bstep (se 1 (by rfl) ⟨695006, by rfl⟩ : syracuseStep 926675 = 1390013) B1390013
theorem B926705 : Blo 614296 926705 := bstep (se 2 (by rfl) ⟨347514, by rfl⟩ : syracuseStep 926705 = 695029) B695029
theorem B926723 : Blo 614296 926723 := bstep (se 1 (by rfl) ⟨695042, by rfl⟩ : syracuseStep 926723 = 1390085) B1390085
theorem B926753 : Blo 614296 926753 := bstep (se 2 (by rfl) ⟨347532, by rfl⟩ : syracuseStep 926753 = 695065) B695065
theorem B3122225 : Blo 614296 3122225 := bstep (se 2 (by rfl) ⟨1170834, by rfl⟩ : syracuseStep 3122225 = 2341669) B2341669
theorem B926771 : Blo 614296 926771 := bstep (se 1 (by rfl) ⟨695078, by rfl⟩ : syracuseStep 926771 = 1390157) B1390157
theorem B926801 : Blo 614296 926801 := bstep (se 2 (by rfl) ⟨347550, by rfl⟩ : syracuseStep 926801 = 695101) B695101
theorem B926819 : Blo 614296 926819 := bstep (se 1 (by rfl) ⟨695114, by rfl⟩ : syracuseStep 926819 = 1390229) B1390229
theorem B1385585 : Blo 614296 1385585 := bstep (se 2 (by rfl) ⟨519594, by rfl⟩ : syracuseStep 1385585 = 1039189) B1039189
theorem B926849 : Blo 614296 926849 := bstep (se 2 (by rfl) ⟨347568, by rfl⟩ : syracuseStep 926849 = 695137) B695137
theorem B1385603 : Blo 614296 1385603 := bstep (se 1 (by rfl) ⟨1039202, by rfl⟩ : syracuseStep 1385603 = 2078405) B2078405
theorem B926867 : Blo 614296 926867 := bstep (se 1 (by rfl) ⟨695150, by rfl⟩ : syracuseStep 926867 = 1390301) B1390301
theorem B926897 : Blo 614296 926897 := bstep (se 2 (by rfl) ⟨347586, by rfl⟩ : syracuseStep 926897 = 695173) B695173
theorem B926915 : Blo 614296 926915 := bstep (se 1 (by rfl) ⟨695186, by rfl⟩ : syracuseStep 926915 = 1390373) B1390373
theorem B926945 : Blo 614296 926945 := bstep (se 2 (by rfl) ⟨347604, by rfl⟩ : syracuseStep 926945 = 695209) B695209
theorem B926963 : Blo 614296 926963 := bstep (se 1 (by rfl) ⟨695222, by rfl⟩ : syracuseStep 926963 = 1390445) B1390445
theorem B2073869 : Blo 614296 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B926993 : Blo 614296 926993 := bstep (se 2 (by rfl) ⟨347622, by rfl⟩ : syracuseStep 926993 = 695245) B695245
theorem B927011 : Blo 614296 927011 := bstep (se 1 (by rfl) ⟨695258, by rfl⟩ : syracuseStep 927011 = 1390517) B1390517
theorem B927041 : Blo 614296 927041 := bstep (se 2 (by rfl) ⟨347640, by rfl⟩ : syracuseStep 927041 = 695281) B695281
theorem B2073923 : Blo 614296 2073923 := bstep (se 1 (by rfl) ⟨1555442, by rfl⟩ : syracuseStep 2073923 = 3110885) B3110885
theorem B927059 : Blo 614296 927059 := bstep (se 1 (by rfl) ⟨695294, by rfl⟩ : syracuseStep 927059 = 1390589) B1390589
theorem B927089 : Blo 614296 927089 := bstep (se 2 (by rfl) ⟨347658, by rfl⟩ : syracuseStep 927089 = 695317) B695317
theorem B927107 : Blo 614296 927107 := bstep (se 1 (by rfl) ⟨695330, by rfl⟩ : syracuseStep 927107 = 1390661) B1390661
theorem B2336141 : Blo 614296 2336141 := bstep (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) B876053
theorem B1385873 : Blo 614296 1385873 := bstep (se 2 (by rfl) ⟨519702, by rfl⟩ : syracuseStep 1385873 = 1039405) B1039405
theorem B959891 : Blo 614296 959891 := bstep (se 1 (by rfl) ⟨719918, by rfl⟩ : syracuseStep 959891 = 1439837) B1439837
theorem B927137 : Blo 614296 927137 := bstep (se 2 (by rfl) ⟨347676, by rfl⟩ : syracuseStep 927137 = 695353) B695353
theorem B1385891 : Blo 614296 1385891 := bstep (se 1 (by rfl) ⟨1039418, by rfl⟩ : syracuseStep 1385891 = 2078837) B2078837
theorem B927155 : Blo 614296 927155 := bstep (se 1 (by rfl) ⟨695366, by rfl⟩ : syracuseStep 927155 = 1390733) B1390733
theorem B16885189 : Blo 614296 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B927185 : Blo 614296 927185 := bstep (se 2 (by rfl) ⟨347694, by rfl⟩ : syracuseStep 927185 = 695389) B695389
theorem B927203 : Blo 614296 927203 := bstep (se 1 (by rfl) ⟨695402, by rfl⟩ : syracuseStep 927203 = 1390805) B1390805
theorem B927233 : Blo 614296 927233 := bstep (se 2 (by rfl) ⟨347712, by rfl⟩ : syracuseStep 927233 = 695425) B695425
theorem B927251 : Blo 614296 927251 := bstep (se 1 (by rfl) ⟨695438, by rfl⟩ : syracuseStep 927251 = 1390877) B1390877
theorem B927281 : Blo 614296 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B927299 : Blo 614296 927299 := bstep (se 1 (by rfl) ⟨695474, by rfl⟩ : syracuseStep 927299 = 1390949) B1390949
theorem B2074193 : Blo 614296 2074193 := bstep (se 2 (by rfl) ⟨777822, by rfl⟩ : syracuseStep 2074193 = 1555645) B1555645
theorem B927329 : Blo 614296 927329 := bstep (se 2 (by rfl) ⟨347748, by rfl⟩ : syracuseStep 927329 = 695497) B695497
theorem B927347 : Blo 614296 927347 := bstep (se 1 (by rfl) ⟨695510, by rfl⟩ : syracuseStep 927347 = 1391021) B1391021
theorem B927377 : Blo 614296 927377 := bstep (se 2 (by rfl) ⟨347766, by rfl⟩ : syracuseStep 927377 = 695533) B695533
theorem B927395 : Blo 614296 927395 := bstep (se 1 (by rfl) ⟨695546, by rfl⟩ : syracuseStep 927395 = 1391093) B1391093
theorem B1386161 : Blo 614296 1386161 := bstep (se 2 (by rfl) ⟨519810, by rfl⟩ : syracuseStep 1386161 = 1039621) B1039621
theorem B927425 : Blo 614296 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B1386179 : Blo 614296 1386179 := bstep (se 1 (by rfl) ⟨1039634, by rfl⟩ : syracuseStep 1386179 = 2079269) B2079269
theorem B927443 : Blo 614296 927443 := bstep (se 1 (by rfl) ⟨695582, by rfl⟩ : syracuseStep 927443 = 1391165) B1391165
theorem B2959217 : Blo 614296 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B3942341 : Blo 614296 3942341 := bstep (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) B739189
theorem B2631629 : Blo 614296 2631629 := bstep (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) B986861
theorem B1386449 : Blo 614296 1386449 := bstep (se 2 (by rfl) ⟨519918, by rfl⟩ : syracuseStep 1386449 = 1039837) B1039837
theorem B1386467 : Blo 614296 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B2074733 : Blo 614296 2074733 := bstep (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) B778025
theorem B2074787 : Blo 614296 2074787 := bstep (se 1 (by rfl) ⟨1556090, by rfl⟩ : syracuseStep 2074787 = 3112181) B3112181
theorem B1386737 : Blo 614296 1386737 := bstep (se 2 (by rfl) ⟨520026, by rfl⟩ : syracuseStep 1386737 = 1040053) B1040053
theorem B1386755 : Blo 614296 1386755 := bstep (se 1 (by rfl) ⟨1040066, by rfl⟩ : syracuseStep 1386755 = 2080133) B2080133
theorem B2959715 : Blo 614296 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B2075057 : Blo 614296 2075057 := bstep (se 2 (by rfl) ⟨778146, by rfl⟩ : syracuseStep 2075057 = 1556293) B1556293
theorem B3123683 : Blo 614296 3123683 := bstep (se 1 (by rfl) ⟨2342762, by rfl⟩ : syracuseStep 3123683 = 4685525) B4685525
theorem B1387025 : Blo 614296 1387025 := bstep (se 2 (by rfl) ⟨520134, by rfl⟩ : syracuseStep 1387025 = 1040269) B1040269
theorem B1387043 : Blo 614296 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B11250373 : Blo 614296 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1977041 : Blo 614296 1977041 := bstep (se 2 (by rfl) ⟨741390, by rfl⟩ : syracuseStep 1977041 = 1482781) B1482781
theorem B1387313 : Blo 614296 1387313 := bstep (se 2 (by rfl) ⟨520242, by rfl⟩ : syracuseStep 1387313 = 1040485) B1040485
theorem B1387331 : Blo 614296 1387331 := bstep (se 1 (by rfl) ⟨1040498, by rfl⟩ : syracuseStep 1387331 = 2080997) B2080997
theorem B1977169 : Blo 614296 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B6761357 : Blo 614296 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B2075597 : Blo 614296 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B2960333 : Blo 614296 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B15772643 : Blo 614296 15772643 := bstep (se 1 (by rfl) ⟨11829482, by rfl⟩ : syracuseStep 15772643 = 23658965) B23658965
theorem B2075651 : Blo 614296 2075651 := bstep (se 1 (by rfl) ⟨1556738, by rfl⟩ : syracuseStep 2075651 = 3113477) B3113477
theorem B1387601 : Blo 614296 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B1977425 : Blo 614296 1977425 := bstep (se 2 (by rfl) ⟨741534, by rfl⟩ : syracuseStep 1977425 = 1483069) B1483069
theorem B1387619 : Blo 614296 1387619 := bstep (se 1 (by rfl) ⟨1040714, by rfl⟩ : syracuseStep 1387619 = 2081429) B2081429
theorem B830593 : Blo 614296 830593 := bstep (se 2 (by rfl) ⟨311472, by rfl⟩ : syracuseStep 830593 = 622945) B622945
theorem B3124493 : Blo 614296 3124493 := bstep (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) B1171685
theorem B2075921 : Blo 614296 2075921 := bstep (se 2 (by rfl) ⟨778470, by rfl⟩ : syracuseStep 2075921 = 1556941) B1556941
theorem B1387889 : Blo 614296 1387889 := bstep (se 2 (by rfl) ⟨520458, by rfl⟩ : syracuseStep 1387889 = 1040917) B1040917
theorem B1387907 : Blo 614296 1387907 := bstep (se 1 (by rfl) ⟨1040930, by rfl⟩ : syracuseStep 1387907 = 2081861) B2081861
theorem B5254541 : Blo 614296 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B2502029 : Blo 614296 2502029 := bstep (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) B938261
theorem B2338253 : Blo 614296 2338253 := bstep (se 3 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 2338253 = 876845) B876845
theorem B1388177 : Blo 614296 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B1388195 : Blo 614296 1388195 := bstep (se 1 (by rfl) ⟨1041146, by rfl⟩ : syracuseStep 1388195 = 2082293) B2082293
theorem B7876277 : Blo 614296 7876277 := bstep (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) B738401
theorem B2076461 : Blo 614296 2076461 := bstep (se 3 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 2076461 = 778673) B778673
theorem B2076515 : Blo 614296 2076515 := bstep (se 1 (by rfl) ⟨1557386, by rfl⟩ : syracuseStep 2076515 = 3114773) B3114773
theorem B1388465 : Blo 614296 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B1388483 : Blo 614296 1388483 := bstep (se 1 (by rfl) ⟨1041362, by rfl⟩ : syracuseStep 1388483 = 2082725) B2082725
theorem B634963 : Blo 614296 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B2076785 : Blo 614296 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B1388753 : Blo 614296 1388753 := bstep (se 2 (by rfl) ⟨520782, by rfl⟩ : syracuseStep 1388753 = 1041565) B1041565
theorem B1388771 : Blo 614296 1388771 := bstep (se 1 (by rfl) ⟨1041578, by rfl⟩ : syracuseStep 1388771 = 2083157) B2083157
theorem B2339057 : Blo 614296 2339057 := bstep (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) B1754293
theorem B2961677 : Blo 614296 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B1389041 : Blo 614296 1389041 := bstep (se 2 (by rfl) ⟨520890, by rfl⟩ : syracuseStep 1389041 = 1041781) B1041781
theorem B1389059 : Blo 614296 1389059 := bstep (se 1 (by rfl) ⟨1041794, by rfl⟩ : syracuseStep 1389059 = 2083589) B2083589
theorem B2077325 : Blo 614296 2077325 := bstep (se 3 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 2077325 = 778997) B778997
theorem B832145 : Blo 614296 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B2077379 : Blo 614296 2077379 := bstep (se 1 (by rfl) ⟨1558034, by rfl⟩ : syracuseStep 2077379 = 3116069) B3116069
theorem B1979117 : Blo 614296 1979117 := bstep (se 3 (by rfl) ⟨371084, by rfl⟩ : syracuseStep 1979117 = 742169) B742169
theorem B1389329 : Blo 614296 1389329 := bstep (se 2 (by rfl) ⟨520998, by rfl⟩ : syracuseStep 1389329 = 1041997) B1041997
theorem B1389347 : Blo 614296 1389347 := bstep (se 1 (by rfl) ⟨1042010, by rfl⟩ : syracuseStep 1389347 = 2084021) B2084021
theorem B2503523 : Blo 614296 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B2569073 : Blo 614296 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B1782641 : Blo 614296 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B2339725 : Blo 614296 2339725 := bstep (se 3 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 2339725 = 877397) B877397
theorem B2077649 : Blo 614296 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B1389617 : Blo 614296 1389617 := bstep (se 2 (by rfl) ⟨521106, by rfl⟩ : syracuseStep 1389617 = 1042213) B1042213
theorem B1389635 : Blo 614296 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B1750193 : Blo 614296 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B1389905 : Blo 614296 1389905 := bstep (se 2 (by rfl) ⟨521214, by rfl⟩ : syracuseStep 1389905 = 1042429) B1042429
theorem B3945827 : Blo 614296 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B1389923 : Blo 614296 1389923 := bstep (se 1 (by rfl) ⟨1042442, by rfl⟩ : syracuseStep 1389923 = 2084885) B2084885
theorem B7026101 : Blo 614296 7026101 := bstep (se 5 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 7026101 = 658697) B658697
theorem B9024965 : Blo 614296 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B2078189 : Blo 614296 2078189 := bstep (se 3 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 2078189 = 779321) B779321
theorem B1979885 : Blo 614296 1979885 := bstep (se 3 (by rfl) ⟨371228, by rfl⟩ : syracuseStep 1979885 = 742457) B742457
theorem B2078243 : Blo 614296 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B1390193 : Blo 614296 1390193 := bstep (se 2 (by rfl) ⟨521322, by rfl⟩ : syracuseStep 1390193 = 1042645) B1042645
theorem B1390211 : Blo 614296 1390211 := bstep (se 1 (by rfl) ⟨1042658, by rfl⟩ : syracuseStep 1390211 = 2085317) B2085317
theorem B2340515 : Blo 614296 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B3520205 : Blo 614296 3520205 := bstep (se 3 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 3520205 = 1320077) B1320077
theorem B2078513 : Blo 614296 2078513 := bstep (se 2 (by rfl) ⟨779442, by rfl⟩ : syracuseStep 2078513 = 1558885) B1558885
theorem B1390481 : Blo 614296 1390481 := bstep (se 2 (by rfl) ⟨521430, by rfl⟩ : syracuseStep 1390481 = 1042861) B1042861
theorem B2504611 : Blo 614296 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1390499 : Blo 614296 1390499 := bstep (se 1 (by rfl) ⟨1042874, by rfl⟩ : syracuseStep 1390499 = 2085749) B2085749
theorem B833491 : Blo 614296 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B1980397 : Blo 614296 1980397 := bstep (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) B742649
theorem B1751149 : Blo 614296 1751149 := bstep (se 3 (by rfl) ⟨328340, by rfl⟩ : syracuseStep 1751149 = 656681) B656681
theorem B2373745 : Blo 614296 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B3127409 : Blo 614296 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B1390769 : Blo 614296 1390769 := bstep (se 2 (by rfl) ⟨521538, by rfl⟩ : syracuseStep 1390769 = 1043077) B1043077
theorem B1390787 : Blo 614296 1390787 := bstep (se 1 (by rfl) ⟨1043090, by rfl⟩ : syracuseStep 1390787 = 2086181) B2086181
theorem B2636003 : Blo 614296 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B2341169 : Blo 614296 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B2079053 : Blo 614296 2079053 := bstep (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) B779645
theorem B1751377 : Blo 614296 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B702803 : Blo 614296 702803 := bstep (se 1 (by rfl) ⟨527102, by rfl⟩ : syracuseStep 702803 = 1054205) B1054205
theorem B2079107 : Blo 614296 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B1391057 : Blo 614296 1391057 := bstep (se 2 (by rfl) ⟨521646, by rfl⟩ : syracuseStep 1391057 = 1043293) B1043293
theorem B1391075 : Blo 614296 1391075 := bstep (se 1 (by rfl) ⟨1043306, by rfl⟩ : syracuseStep 1391075 = 2086613) B2086613
theorem B1751537 : Blo 614296 1751537 := bstep (se 2 (by rfl) ⟨656826, by rfl⟩ : syracuseStep 1751537 = 1313653) B1313653
theorem B1554947 : Blo 614296 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B1751651 : Blo 614296 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B2079377 : Blo 614296 2079377 := bstep (se 2 (by rfl) ⟨779766, by rfl⟩ : syracuseStep 2079377 = 1559533) B1559533
theorem B1555139 : Blo 614296 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1522435 : Blo 614296 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B4668515 : Blo 614296 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B2079917 : Blo 614296 2079917 := bstep (se 3 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 2079917 = 779969) B779969
theorem B2079971 : Blo 614296 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B834913 : Blo 614296 834913 := bstep (se 2 (by rfl) ⟨313092, by rfl⟩ : syracuseStep 834913 = 626185) B626185
theorem B2080241 : Blo 614296 2080241 := bstep (se 2 (by rfl) ⟨780090, by rfl⟩ : syracuseStep 2080241 = 1560181) B1560181
theorem B3128867 : Blo 614296 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B1752653 : Blo 614296 1752653 := bstep (se 3 (by rfl) ⟨328622, by rfl⟩ : syracuseStep 1752653 = 657245) B657245
theorem B1556081 : Blo 614296 1556081 := bstep (se 2 (by rfl) ⟨583530, by rfl⟩ : syracuseStep 1556081 = 1167061) B1167061
theorem B3325573 : Blo 614296 3325573 := bstep (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) B623545
theorem B1556131 : Blo 614296 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B2342627 : Blo 614296 2342627 := bstep (se 1 (by rfl) ⟨1756970, by rfl⟩ : syracuseStep 2342627 = 3513941) B3513941
theorem B2342641 : Blo 614296 2342641 := bstep (se 2 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 2342641 = 1756981) B1756981
theorem B1752835 : Blo 614296 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B1556273 : Blo 614296 1556273 := bstep (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) B1167205
theorem B1752995 : Blo 614296 1752995 := bstep (se 1 (by rfl) ⟨1314746, by rfl⟩ : syracuseStep 1752995 = 2629493) B2629493
theorem B2080781 : Blo 614296 2080781 := bstep (se 3 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 2080781 = 780293) B780293
theorem B2080835 : Blo 614296 2080835 := bstep (se 1 (by rfl) ⟨1560626, by rfl⟩ : syracuseStep 2080835 = 3121253) B3121253
theorem B2638001 : Blo 614296 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B3129677 : Blo 614296 3129677 := bstep (se 3 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 3129677 = 1173629) B1173629
theorem B999761 : Blo 614296 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B2081105 : Blo 614296 2081105 := bstep (se 2 (by rfl) ⟨780414, by rfl⟩ : syracuseStep 2081105 = 1560829) B1560829
theorem B1557265 : Blo 614296 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B4440901 : Blo 614296 4440901 := bstep (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) B832669
theorem B2245475 : Blo 614296 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B2081645 : Blo 614296 2081645 := bstep (se 3 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 2081645 = 780617) B780617
theorem B2081699 : Blo 614296 2081699 := bstep (se 1 (by rfl) ⟨1561274, by rfl⟩ : syracuseStep 2081699 = 3122549) B3122549
theorem B12633029 : Blo 614296 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B1754065 : Blo 614296 1754065 := bstep (se 2 (by rfl) ⟨657774, by rfl⟩ : syracuseStep 1754065 = 1315549) B1315549
theorem B1557539 : Blo 614296 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1262659 : Blo 614296 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B2638925 : Blo 614296 2638925 := bstep (se 3 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 2638925 = 989597) B989597
theorem B2344099 : Blo 614296 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B2081969 : Blo 614296 2081969 := bstep (se 2 (by rfl) ⟨780738, by rfl⟩ : syracuseStep 2081969 = 1561477) B1561477
theorem B1557731 : Blo 614296 1557731 := bstep (se 1 (by rfl) ⟨1168298, by rfl⟩ : syracuseStep 1557731 = 2336597) B2336597
theorem B2082509 : Blo 614296 2082509 := bstep (se 3 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 2082509 = 780941) B780941
theorem B2082563 : Blo 614296 2082563 := bstep (se 1 (by rfl) ⟨1561922, by rfl⟩ : syracuseStep 2082563 = 3123845) B3123845
theorem B2082833 : Blo 614296 2082833 := bstep (se 2 (by rfl) ⟨781062, by rfl⟩ : syracuseStep 2082833 = 1562125) B1562125
theorem B1558673 : Blo 614296 1558673 := bstep (se 2 (by rfl) ⟨584502, by rfl⟩ : syracuseStep 1558673 = 1169005) B1169005
theorem B1558723 : Blo 614296 1558723 := bstep (se 1 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 1558723 = 2338085) B2338085
theorem B13289669 : Blo 614296 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B5327045 : Blo 614296 5327045 := bstep (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) B998821
theorem B1755341 : Blo 614296 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B1558865 : Blo 614296 1558865 := bstep (se 2 (by rfl) ⟨584574, by rfl⟩ : syracuseStep 1558865 = 1169149) B1169149
theorem B1755523 : Blo 614296 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1755569 : Blo 614296 1755569 := bstep (se 2 (by rfl) ⟨658338, by rfl⟩ : syracuseStep 1755569 = 1316677) B1316677
theorem B674227 : Blo 614296 674227 := bstep (se 1 (by rfl) ⟨505670, by rfl⟩ : syracuseStep 674227 = 1011341) B1011341
theorem B2083373 : Blo 614296 2083373 := bstep (se 3 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 2083373 = 781265) B781265
theorem B739939 : Blo 614296 739939 := bstep (se 1 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 739939 = 1109909) B1109909
theorem B2083427 : Blo 614296 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B7883405 : Blo 614296 7883405 := bstep (se 3 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 7883405 = 2956277) B2956277
theorem B4999907 : Blo 614296 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B2083697 : Blo 614296 2083697 := bstep (se 2 (by rfl) ⟨781386, by rfl⟩ : syracuseStep 2083697 = 1562773) B1562773
theorem B1166339 : Blo 614296 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1559857 : Blo 614296 1559857 := bstep (se 2 (by rfl) ⟨584946, by rfl⟩ : syracuseStep 1559857 = 1169893) B1169893
theorem B2346317 : Blo 614296 2346317 := bstep (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) B879869
theorem B5000561 : Blo 614296 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B2084237 : Blo 614296 2084237 := bstep (se 3 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 2084237 = 781589) B781589
theorem B2084291 : Blo 614296 2084291 := bstep (se 1 (by rfl) ⟨1563218, by rfl⟩ : syracuseStep 2084291 = 3126437) B3126437
theorem B1560131 : Blo 614296 1560131 := bstep (se 1 (by rfl) ⟨1170098, by rfl⟩ : syracuseStep 1560131 = 2340197) B2340197
theorem B3001969 : Blo 614296 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B2084561 : Blo 614296 2084561 := bstep (se 2 (by rfl) ⟨781710, by rfl⟩ : syracuseStep 2084561 = 1563421) B1563421
theorem B1560323 : Blo 614296 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B5426957 : Blo 614296 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B1757027 : Blo 614296 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B1331075 : Blo 614296 1331075 := bstep (se 1 (by rfl) ⟨998306, by rfl⟩ : syracuseStep 1331075 = 1996613) B1996613
theorem B1167281 : Blo 614296 1167281 := bstep (se 2 (by rfl) ⟨437730, by rfl⟩ : syracuseStep 1167281 = 875461) B875461
theorem B937969 : Blo 614296 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B2216099 : Blo 614296 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B12669155 : Blo 614296 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B2085101 : Blo 614296 2085101 := bstep (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) B781913
theorem B3952901 : Blo 614296 3952901 := bstep (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) B741169
theorem B1331491 : Blo 614296 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B2085155 : Blo 614296 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B2969905 : Blo 614296 2969905 := bstep (se 2 (by rfl) ⟨1113714, by rfl⟩ : syracuseStep 2969905 = 2227429) B2227429
theorem B4673861 : Blo 614296 4673861 := bstep (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) B876349
theorem B1036705 : Blo 614296 1036705 := bstep (se 2 (by rfl) ⟨388764, by rfl⟩ : syracuseStep 1036705 = 777529) B777529
theorem B1036739 : Blo 614296 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B17125829 : Blo 614296 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B2085425 : Blo 614296 2085425 := bstep (se 2 (by rfl) ⟨782034, by rfl⟩ : syracuseStep 2085425 = 1564069) B1564069
theorem B1036867 : Blo 614296 1036867 := bstep (se 1 (by rfl) ⟨777650, by rfl⟩ : syracuseStep 1036867 = 1555301) B1555301
theorem B1692269 : Blo 614296 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B1561265 : Blo 614296 1561265 := bstep (se 2 (by rfl) ⟨585474, by rfl⟩ : syracuseStep 1561265 = 1170949) B1170949
theorem B1037009 : Blo 614296 1037009 := bstep (se 2 (by rfl) ⟨388878, by rfl⟩ : syracuseStep 1037009 = 777757) B777757
theorem B1561315 : Blo 614296 1561315 := bstep (se 1 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 1561315 = 2341973) B2341973
theorem B7918307 : Blo 614296 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B1168177 : Blo 614296 1168177 := bstep (se 2 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 1168177 = 876133) B876133
theorem B6673205 : Blo 614296 6673205 := bstep (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) B625613
theorem B1037137 : Blo 614296 1037137 := bstep (se 2 (by rfl) ⟨388926, by rfl⟩ : syracuseStep 1037137 = 777853) B777853
theorem B1561457 : Blo 614296 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B1037171 : Blo 614296 1037171 := bstep (se 1 (by rfl) ⟨777878, by rfl⟩ : syracuseStep 1037171 = 1555757) B1555757
theorem B1168337 : Blo 614296 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B1037299 : Blo 614296 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B1758257 : Blo 614296 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B2085965 : Blo 614296 2085965 := bstep (se 3 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 2085965 = 782237) B782237
theorem B1266769 : Blo 614296 1266769 := bstep (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) B950077
theorem B1037441 : Blo 614296 1037441 := bstep (se 2 (by rfl) ⟨389040, by rfl⟩ : syracuseStep 1037441 = 778081) B778081
theorem B2086019 : Blo 614296 2086019 := bstep (se 1 (by rfl) ⟨1564514, by rfl⟩ : syracuseStep 2086019 = 3129029) B3129029
theorem B7001315 : Blo 614296 7001315 := bstep (se 1 (by rfl) ⟨5250986, by rfl⟩ : syracuseStep 7001315 = 10501973) B10501973
theorem B1037569 : Blo 614296 1037569 := bstep (se 2 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 1037569 = 778177) B778177
theorem B1037603 : Blo 614296 1037603 := bstep (se 1 (by rfl) ⟨778202, by rfl⟩ : syracuseStep 1037603 = 1556405) B1556405
theorem B6313315 : Blo 614296 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1168739 : Blo 614296 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B2086289 : Blo 614296 2086289 := bstep (se 2 (by rfl) ⟨782358, by rfl⟩ : syracuseStep 2086289 = 1564717) B1564717
theorem B1037731 : Blo 614296 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B1037873 : Blo 614296 1037873 := bstep (se 2 (by rfl) ⟨389202, by rfl⟩ : syracuseStep 1037873 = 778405) B778405
theorem B1038001 : Blo 614296 1038001 := bstep (se 2 (by rfl) ⟨389250, by rfl⟩ : syracuseStep 1038001 = 778501) B778501
theorem B1038035 : Blo 614296 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B1562449 : Blo 614296 1562449 := bstep (se 2 (by rfl) ⟨585918, by rfl⟩ : syracuseStep 1562449 = 1171837) B1171837
theorem B1038163 : Blo 614296 1038163 := bstep (se 1 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 1038163 = 1557245) B1557245
theorem B1038305 : Blo 614296 1038305 := bstep (se 2 (by rfl) ⟨389364, by rfl⟩ : syracuseStep 1038305 = 778729) B778729
theorem B3004465 : Blo 614296 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1038433 : Blo 614296 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B1562723 : Blo 614296 1562723 := bstep (se 1 (by rfl) ⟨1172042, by rfl⟩ : syracuseStep 1562723 = 2344085) B2344085
theorem B1038467 : Blo 614296 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B2250929 : Blo 614296 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B874675 : Blo 614296 874675 := bstep (se 1 (by rfl) ⟨656006, by rfl⟩ : syracuseStep 874675 = 1312013) B1312013
theorem B1169635 : Blo 614296 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B1038595 : Blo 614296 1038595 := bstep (se 1 (by rfl) ⟨778946, by rfl⟩ : syracuseStep 1038595 = 1557893) B1557893
theorem B1562915 : Blo 614296 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B1169795 : Blo 614296 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B1038737 : Blo 614296 1038737 := bstep (se 2 (by rfl) ⟨389526, by rfl⟩ : syracuseStep 1038737 = 779053) B779053
theorem B1759715 : Blo 614296 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1038865 : Blo 614296 1038865 := bstep (se 2 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 1038865 = 779149) B779149
theorem B1038899 : Blo 614296 1038899 := bstep (se 1 (by rfl) ⟨779174, by rfl⟩ : syracuseStep 1038899 = 1558349) B1558349
theorem B3758669 : Blo 614296 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1039027 : Blo 614296 1039027 := bstep (se 1 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 1039027 = 1558541) B1558541
theorem B875233 : Blo 614296 875233 := bstep (se 2 (by rfl) ⟨328212, by rfl⟩ : syracuseStep 875233 = 656425) B656425
theorem B1039169 : Blo 614296 1039169 := bstep (se 2 (by rfl) ⟨389688, by rfl⟩ : syracuseStep 1039169 = 779377) B779377
theorem B18963341 : Blo 614296 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1039297 : Blo 614296 1039297 := bstep (se 2 (by rfl) ⟨389736, by rfl⟩ : syracuseStep 1039297 = 779473) B779473
theorem B1039331 : Blo 614296 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B1039459 : Blo 614296 1039459 := bstep (se 1 (by rfl) ⟨779594, by rfl⟩ : syracuseStep 1039459 = 1559189) B1559189
theorem B2219213 : Blo 614296 2219213 := bstep (se 3 (by rfl) ⟨416102, by rfl⟩ : syracuseStep 2219213 = 832205) B832205
theorem B1563857 : Blo 614296 1563857 := bstep (se 2 (by rfl) ⟨586446, by rfl⟩ : syracuseStep 1563857 = 1172893) B1172893
theorem B1039601 : Blo 614296 1039601 := bstep (se 2 (by rfl) ⟨389850, by rfl⟩ : syracuseStep 1039601 = 779701) B779701
theorem B1563907 : Blo 614296 1563907 := bstep (se 1 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 1563907 = 2345861) B2345861
theorem B1760525 : Blo 614296 1760525 := bstep (se 3 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 1760525 = 660197) B660197
theorem B777539 : Blo 614296 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B1039729 : Blo 614296 1039729 := bstep (se 2 (by rfl) ⟨389898, by rfl⟩ : syracuseStep 1039729 = 779797) B779797
theorem B1564049 : Blo 614296 1564049 := bstep (se 2 (by rfl) ⟨586518, by rfl⟩ : syracuseStep 1564049 = 1173037) B1173037
theorem B1039763 : Blo 614296 1039763 := bstep (se 1 (by rfl) ⟨779822, by rfl⟩ : syracuseStep 1039763 = 1559645) B1559645
theorem B875939 : Blo 614296 875939 := bstep (se 1 (by rfl) ⟨656954, by rfl⟩ : syracuseStep 875939 = 1313909) B1313909
theorem B1170865 : Blo 614296 1170865 := bstep (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) B878149
theorem B1039891 : Blo 614296 1039891 := bstep (se 1 (by rfl) ⟨779918, by rfl⟩ : syracuseStep 1039891 = 1559837) B1559837
theorem B1040033 : Blo 614296 1040033 := bstep (se 2 (by rfl) ⟨390012, by rfl⟩ : syracuseStep 1040033 = 780025) B780025
theorem B4284109 : Blo 614296 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B3956465 : Blo 614296 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B1924877 : Blo 614296 1924877 := bstep (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) B721829
theorem B1040161 : Blo 614296 1040161 := bstep (se 2 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 1040161 = 780121) B780121
theorem B1040195 : Blo 614296 1040195 := bstep (se 1 (by rfl) ⟨780146, by rfl⟩ : syracuseStep 1040195 = 1560293) B1560293
theorem B614307 : Blo 614296 614307 := bstep (se 1 (by rfl) ⟨460730, by rfl⟩ : syracuseStep 614307 = 921461) B921461
theorem B614323 : Blo 614296 614323 := bstep (se 1 (by rfl) ⟨460742, by rfl⟩ : syracuseStep 614323 = 921485) B921485
theorem B614339 : Blo 614296 614339 := bstep (se 1 (by rfl) ⟨460754, by rfl⟩ : syracuseStep 614339 = 921509) B921509
theorem B1040323 : Blo 614296 1040323 := bstep (se 1 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 1040323 = 1560485) B1560485
theorem B614355 : Blo 614296 614355 := bstep (se 1 (by rfl) ⟨460766, by rfl⟩ : syracuseStep 614355 = 921533) B921533
theorem B614371 : Blo 614296 614371 := bstep (se 1 (by rfl) ⟨460778, by rfl⟩ : syracuseStep 614371 = 921557) B921557
theorem B614387 : Blo 614296 614387 := bstep (se 1 (by rfl) ⟨460790, by rfl⟩ : syracuseStep 614387 = 921581) B921581
theorem B614403 : Blo 614296 614403 := bstep (se 1 (by rfl) ⟨460802, by rfl⟩ : syracuseStep 614403 = 921605) B921605
theorem B778243 : Blo 614296 778243 := bstep (se 1 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 778243 = 1167365) B1167365
theorem B614419 : Blo 614296 614419 := bstep (se 1 (by rfl) ⟨460814, by rfl⟩ : syracuseStep 614419 = 921629) B921629
theorem B876577 : Blo 614296 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B614435 : Blo 614296 614435 := bstep (se 1 (by rfl) ⟨460826, by rfl⟩ : syracuseStep 614435 = 921653) B921653
theorem B614451 : Blo 614296 614451 := bstep (se 1 (by rfl) ⟨460838, by rfl⟩ : syracuseStep 614451 = 921677) B921677
theorem B614467 : Blo 614296 614467 := bstep (se 1 (by rfl) ⟨460850, by rfl⟩ : syracuseStep 614467 = 921701) B921701
theorem B1040465 : Blo 614296 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B614483 : Blo 614296 614483 := bstep (se 1 (by rfl) ⟨460862, by rfl⟩ : syracuseStep 614483 = 921725) B921725
theorem B614499 : Blo 614296 614499 := bstep (se 1 (by rfl) ⟨460874, by rfl⟩ : syracuseStep 614499 = 921749) B921749
theorem B778339 : Blo 614296 778339 := bstep (se 1 (by rfl) ⟨583754, by rfl⟩ : syracuseStep 778339 = 1167509) B1167509
theorem B614515 : Blo 614296 614515 := bstep (se 1 (by rfl) ⟨460886, by rfl⟩ : syracuseStep 614515 = 921773) B921773
theorem B614531 : Blo 614296 614531 := bstep (se 1 (by rfl) ⟨460898, by rfl⟩ : syracuseStep 614531 = 921797) B921797
theorem B614547 : Blo 614296 614547 := bstep (se 1 (by rfl) ⟨460910, by rfl⟩ : syracuseStep 614547 = 921821) B921821
theorem B876691 : Blo 614296 876691 := bstep (se 1 (by rfl) ⟨657518, by rfl⟩ : syracuseStep 876691 = 1315037) B1315037
theorem B614563 : Blo 614296 614563 := bstep (se 1 (by rfl) ⟨460922, by rfl⟩ : syracuseStep 614563 = 921845) B921845
theorem B2220209 : Blo 614296 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B614579 : Blo 614296 614579 := bstep (se 1 (by rfl) ⟨460934, by rfl⟩ : syracuseStep 614579 = 921869) B921869
theorem B614595 : Blo 614296 614595 := bstep (se 1 (by rfl) ⟨460946, by rfl⟩ : syracuseStep 614595 = 921893) B921893
theorem B1040593 : Blo 614296 1040593 := bstep (se 2 (by rfl) ⟨390222, by rfl⟩ : syracuseStep 1040593 = 780445) B780445
theorem B614611 : Blo 614296 614611 := bstep (se 1 (by rfl) ⟨460958, by rfl⟩ : syracuseStep 614611 = 921917) B921917
theorem B614627 : Blo 614296 614627 := bstep (se 1 (by rfl) ⟨460970, by rfl⟩ : syracuseStep 614627 = 921941) B921941
theorem B614643 : Blo 614296 614643 := bstep (se 1 (by rfl) ⟨460982, by rfl⟩ : syracuseStep 614643 = 921965) B921965
theorem B1040627 : Blo 614296 1040627 := bstep (se 1 (by rfl) ⟨780470, by rfl⟩ : syracuseStep 1040627 = 1560941) B1560941
theorem B614659 : Blo 614296 614659 := bstep (se 1 (by rfl) ⟨460994, by rfl⟩ : syracuseStep 614659 = 921989) B921989
theorem B614675 : Blo 614296 614675 := bstep (se 1 (by rfl) ⟨461006, by rfl⟩ : syracuseStep 614675 = 922013) B922013
theorem B614691 : Blo 614296 614691 := bstep (se 1 (by rfl) ⟨461018, by rfl⟩ : syracuseStep 614691 = 922037) B922037
theorem B614707 : Blo 614296 614707 := bstep (se 1 (by rfl) ⟨461030, by rfl⟩ : syracuseStep 614707 = 922061) B922061
theorem B614723 : Blo 614296 614723 := bstep (se 1 (by rfl) ⟨461042, by rfl⟩ : syracuseStep 614723 = 922085) B922085
theorem B614739 : Blo 614296 614739 := bstep (se 1 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 614739 = 922109) B922109
theorem B614755 : Blo 614296 614755 := bstep (se 1 (by rfl) ⟨461066, by rfl⟩ : syracuseStep 614755 = 922133) B922133
theorem B1565041 : Blo 614296 1565041 := bstep (se 2 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 1565041 = 1173781) B1173781
theorem B614771 : Blo 614296 614771 := bstep (se 1 (by rfl) ⟨461078, by rfl⟩ : syracuseStep 614771 = 922157) B922157
theorem B1040755 : Blo 614296 1040755 := bstep (se 1 (by rfl) ⟨780566, by rfl⟩ : syracuseStep 1040755 = 1561133) B1561133
theorem B614787 : Blo 614296 614787 := bstep (se 1 (by rfl) ⟨461090, by rfl⟩ : syracuseStep 614787 = 922181) B922181
theorem B614803 : Blo 614296 614803 := bstep (se 1 (by rfl) ⟨461102, by rfl⟩ : syracuseStep 614803 = 922205) B922205
theorem B614819 : Blo 614296 614819 := bstep (se 1 (by rfl) ⟨461114, by rfl⟩ : syracuseStep 614819 = 922229) B922229
theorem B3563939 : Blo 614296 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B614835 : Blo 614296 614835 := bstep (se 1 (by rfl) ⟨461126, by rfl⟩ : syracuseStep 614835 = 922253) B922253
theorem B614851 : Blo 614296 614851 := bstep (se 1 (by rfl) ⟨461138, by rfl⟩ : syracuseStep 614851 = 922277) B922277
theorem B1171921 : Blo 614296 1171921 := bstep (se 2 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 1171921 = 878941) B878941
theorem B614867 : Blo 614296 614867 := bstep (se 1 (by rfl) ⟨461150, by rfl⟩ : syracuseStep 614867 = 922301) B922301
theorem B614883 : Blo 614296 614883 := bstep (se 1 (by rfl) ⟨461162, by rfl⟩ : syracuseStep 614883 = 922325) B922325
theorem B614899 : Blo 614296 614899 := bstep (se 1 (by rfl) ⟨461174, by rfl⟩ : syracuseStep 614899 = 922349) B922349
theorem B1040897 : Blo 614296 1040897 := bstep (se 2 (by rfl) ⟨390336, by rfl⟩ : syracuseStep 1040897 = 780673) B780673
theorem B614915 : Blo 614296 614915 := bstep (se 1 (by rfl) ⟨461186, by rfl⟩ : syracuseStep 614915 = 922373) B922373
theorem B614931 : Blo 614296 614931 := bstep (se 1 (by rfl) ⟨461198, by rfl⟩ : syracuseStep 614931 = 922397) B922397
theorem B614947 : Blo 614296 614947 := bstep (se 1 (by rfl) ⟨461210, by rfl⟩ : syracuseStep 614947 = 922421) B922421
theorem B614963 : Blo 614296 614963 := bstep (se 1 (by rfl) ⟨461222, by rfl⟩ : syracuseStep 614963 = 922445) B922445
theorem B614979 : Blo 614296 614979 := bstep (se 1 (by rfl) ⟨461234, by rfl⟩ : syracuseStep 614979 = 922469) B922469
theorem B614995 : Blo 614296 614995 := bstep (se 1 (by rfl) ⟨461246, by rfl⟩ : syracuseStep 614995 = 922493) B922493
theorem B778835 : Blo 614296 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B615011 : Blo 614296 615011 := bstep (se 1 (by rfl) ⟨461258, by rfl⟩ : syracuseStep 615011 = 922517) B922517
theorem B615027 : Blo 614296 615027 := bstep (se 1 (by rfl) ⟨461270, by rfl⟩ : syracuseStep 615027 = 922541) B922541
theorem B1041025 : Blo 614296 1041025 := bstep (se 2 (by rfl) ⟨390384, by rfl⟩ : syracuseStep 1041025 = 780769) B780769
theorem B615043 : Blo 614296 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B615059 : Blo 614296 615059 := bstep (se 1 (by rfl) ⟨461294, by rfl⟩ : syracuseStep 615059 = 922589) B922589
theorem B615075 : Blo 614296 615075 := bstep (se 1 (by rfl) ⟨461306, by rfl⟩ : syracuseStep 615075 = 922613) B922613
theorem B1041059 : Blo 614296 1041059 := bstep (se 1 (by rfl) ⟨780794, by rfl⟩ : syracuseStep 1041059 = 1561589) B1561589
theorem B615091 : Blo 614296 615091 := bstep (se 1 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 615091 = 922637) B922637
theorem B615107 : Blo 614296 615107 := bstep (se 1 (by rfl) ⟨461330, by rfl⟩ : syracuseStep 615107 = 922661) B922661
theorem B615123 : Blo 614296 615123 := bstep (se 1 (by rfl) ⟨461342, by rfl⟩ : syracuseStep 615123 = 922685) B922685
theorem B615139 : Blo 614296 615139 := bstep (se 1 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 615139 = 922709) B922709
theorem B615155 : Blo 614296 615155 := bstep (se 1 (by rfl) ⟨461366, by rfl⟩ : syracuseStep 615155 = 922733) B922733
theorem B615171 : Blo 614296 615171 := bstep (se 1 (by rfl) ⟨461378, by rfl⟩ : syracuseStep 615171 = 922757) B922757
theorem B615187 : Blo 614296 615187 := bstep (se 1 (by rfl) ⟨461390, by rfl⟩ : syracuseStep 615187 = 922781) B922781
theorem B615203 : Blo 614296 615203 := bstep (se 1 (by rfl) ⟨461402, by rfl⟩ : syracuseStep 615203 = 922805) B922805
theorem B1041187 : Blo 614296 1041187 := bstep (se 1 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 1041187 = 1561781) B1561781
theorem B615219 : Blo 614296 615219 := bstep (se 1 (by rfl) ⟨461414, by rfl⟩ : syracuseStep 615219 = 922829) B922829
theorem B615235 : Blo 614296 615235 := bstep (se 1 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 615235 = 922853) B922853
theorem B7037765 : Blo 614296 7037765 := bstep (se 4 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 7037765 = 1319581) B1319581
theorem B615251 : Blo 614296 615251 := bstep (se 1 (by rfl) ⟨461438, by rfl⟩ : syracuseStep 615251 = 922877) B922877
theorem B615267 : Blo 614296 615267 := bstep (se 1 (by rfl) ⟨461450, by rfl⟩ : syracuseStep 615267 = 922901) B922901
theorem B1172323 : Blo 614296 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B615283 : Blo 614296 615283 := bstep (se 1 (by rfl) ⟨461462, by rfl⟩ : syracuseStep 615283 = 922925) B922925
theorem B615299 : Blo 614296 615299 := bstep (se 1 (by rfl) ⟨461474, by rfl⟩ : syracuseStep 615299 = 922949) B922949
theorem B1172369 : Blo 614296 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B615315 : Blo 614296 615315 := bstep (se 1 (by rfl) ⟨461486, by rfl⟩ : syracuseStep 615315 = 922973) B922973
theorem B615331 : Blo 614296 615331 := bstep (se 1 (by rfl) ⟨461498, by rfl⟩ : syracuseStep 615331 = 922997) B922997
theorem B1041329 : Blo 614296 1041329 := bstep (se 2 (by rfl) ⟨390498, by rfl⟩ : syracuseStep 1041329 = 780997) B780997
theorem B615347 : Blo 614296 615347 := bstep (se 1 (by rfl) ⟨461510, by rfl⟩ : syracuseStep 615347 = 923021) B923021
theorem B615363 : Blo 614296 615363 := bstep (se 1 (by rfl) ⟨461522, by rfl⟩ : syracuseStep 615363 = 923045) B923045
theorem B22438853 : Blo 614296 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B615379 : Blo 614296 615379 := bstep (se 1 (by rfl) ⟨461534, by rfl⟩ : syracuseStep 615379 = 923069) B923069
theorem B615395 : Blo 614296 615395 := bstep (se 1 (by rfl) ⟨461546, by rfl⟩ : syracuseStep 615395 = 923093) B923093
theorem B615411 : Blo 614296 615411 := bstep (se 1 (by rfl) ⟨461558, by rfl⟩ : syracuseStep 615411 = 923117) B923117
theorem B615427 : Blo 614296 615427 := bstep (se 1 (by rfl) ⟨461570, by rfl⟩ : syracuseStep 615427 = 923141) B923141
theorem B615443 : Blo 614296 615443 := bstep (se 1 (by rfl) ⟨461582, by rfl⟩ : syracuseStep 615443 = 923165) B923165
theorem B615459 : Blo 614296 615459 := bstep (se 1 (by rfl) ⟨461594, by rfl⟩ : syracuseStep 615459 = 923189) B923189
theorem B1041457 : Blo 614296 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B615475 : Blo 614296 615475 := bstep (se 1 (by rfl) ⟨461606, by rfl⟩ : syracuseStep 615475 = 923213) B923213
theorem B615491 : Blo 614296 615491 := bstep (se 1 (by rfl) ⟨461618, by rfl⟩ : syracuseStep 615491 = 923237) B923237
theorem B615507 : Blo 614296 615507 := bstep (se 1 (by rfl) ⟨461630, by rfl⟩ : syracuseStep 615507 = 923261) B923261
theorem B1041491 : Blo 614296 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B615523 : Blo 614296 615523 := bstep (se 1 (by rfl) ⟨461642, by rfl⟩ : syracuseStep 615523 = 923285) B923285
theorem B615539 : Blo 614296 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B615555 : Blo 614296 615555 := bstep (se 1 (by rfl) ⟨461666, by rfl⟩ : syracuseStep 615555 = 923333) B923333
theorem B4220045 : Blo 614296 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B615571 : Blo 614296 615571 := bstep (se 1 (by rfl) ⟨461678, by rfl⟩ : syracuseStep 615571 = 923357) B923357
theorem B615587 : Blo 614296 615587 := bstep (se 1 (by rfl) ⟨461690, by rfl⟩ : syracuseStep 615587 = 923381) B923381
theorem B3957923 : Blo 614296 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1172657 : Blo 614296 1172657 := bstep (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) B879493
theorem B615603 : Blo 614296 615603 := bstep (se 1 (by rfl) ⟨461702, by rfl⟩ : syracuseStep 615603 = 923405) B923405
theorem B615619 : Blo 614296 615619 := bstep (se 1 (by rfl) ⟨461714, by rfl⟩ : syracuseStep 615619 = 923429) B923429
theorem B615635 : Blo 614296 615635 := bstep (se 1 (by rfl) ⟨461726, by rfl⟩ : syracuseStep 615635 = 923453) B923453
theorem B1041619 : Blo 614296 1041619 := bstep (se 1 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 1041619 = 1562429) B1562429
theorem B615651 : Blo 614296 615651 := bstep (se 1 (by rfl) ⟨461738, by rfl⟩ : syracuseStep 615651 = 923477) B923477
theorem B615667 : Blo 614296 615667 := bstep (se 1 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 615667 = 923501) B923501
theorem B615683 : Blo 614296 615683 := bstep (se 1 (by rfl) ⟨461762, by rfl⟩ : syracuseStep 615683 = 923525) B923525
theorem B615699 : Blo 614296 615699 := bstep (se 1 (by rfl) ⟨461774, by rfl⟩ : syracuseStep 615699 = 923549) B923549
theorem B779539 : Blo 614296 779539 := bstep (se 1 (by rfl) ⟨584654, by rfl⟩ : syracuseStep 779539 = 1169309) B1169309
theorem B615715 : Blo 614296 615715 := bstep (se 1 (by rfl) ⟨461786, by rfl⟩ : syracuseStep 615715 = 923573) B923573
theorem B615731 : Blo 614296 615731 := bstep (se 1 (by rfl) ⟨461798, by rfl⟩ : syracuseStep 615731 = 923597) B923597
theorem B615747 : Blo 614296 615747 := bstep (se 1 (by rfl) ⟨461810, by rfl⟩ : syracuseStep 615747 = 923621) B923621
theorem B615763 : Blo 614296 615763 := bstep (se 1 (by rfl) ⟨461822, by rfl⟩ : syracuseStep 615763 = 923645) B923645
theorem B1041761 : Blo 614296 1041761 := bstep (se 2 (by rfl) ⟨390660, by rfl⟩ : syracuseStep 1041761 = 781321) B781321
theorem B1402211 : Blo 614296 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B615779 : Blo 614296 615779 := bstep (se 1 (by rfl) ⟨461834, by rfl⟩ : syracuseStep 615779 = 923669) B923669
theorem B615795 : Blo 614296 615795 := bstep (se 1 (by rfl) ⟨461846, by rfl⟩ : syracuseStep 615795 = 923693) B923693
theorem B779635 : Blo 614296 779635 := bstep (se 1 (by rfl) ⟨584726, by rfl⟩ : syracuseStep 779635 = 1169453) B1169453
theorem B615811 : Blo 614296 615811 := bstep (se 1 (by rfl) ⟨461858, by rfl⟩ : syracuseStep 615811 = 923717) B923717
theorem B615827 : Blo 614296 615827 := bstep (se 1 (by rfl) ⟨461870, by rfl⟩ : syracuseStep 615827 = 923741) B923741
theorem B615843 : Blo 614296 615843 := bstep (se 1 (by rfl) ⟨461882, by rfl⟩ : syracuseStep 615843 = 923765) B923765
theorem B615859 : Blo 614296 615859 := bstep (se 1 (by rfl) ⟨461894, by rfl⟩ : syracuseStep 615859 = 923789) B923789
theorem B615875 : Blo 614296 615875 := bstep (se 1 (by rfl) ⟨461906, by rfl⟩ : syracuseStep 615875 = 923813) B923813
theorem B615891 : Blo 614296 615891 := bstep (se 1 (by rfl) ⟨461918, by rfl⟩ : syracuseStep 615891 = 923837) B923837
theorem B878035 : Blo 614296 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B1041889 : Blo 614296 1041889 := bstep (se 2 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 1041889 = 781417) B781417
theorem B615907 : Blo 614296 615907 := bstep (se 1 (by rfl) ⟨461930, by rfl⟩ : syracuseStep 615907 = 923861) B923861
theorem B615923 : Blo 614296 615923 := bstep (se 1 (by rfl) ⟨461942, by rfl⟩ : syracuseStep 615923 = 923885) B923885
theorem B615939 : Blo 614296 615939 := bstep (se 1 (by rfl) ⟨461954, by rfl⟩ : syracuseStep 615939 = 923909) B923909
theorem B1041923 : Blo 614296 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B615955 : Blo 614296 615955 := bstep (se 1 (by rfl) ⟨461966, by rfl⟩ : syracuseStep 615955 = 923933) B923933
theorem B615971 : Blo 614296 615971 := bstep (se 1 (by rfl) ⟨461978, by rfl⟩ : syracuseStep 615971 = 923957) B923957
theorem B615987 : Blo 614296 615987 := bstep (se 1 (by rfl) ⟨461990, by rfl⟩ : syracuseStep 615987 = 923981) B923981
theorem B616003 : Blo 614296 616003 := bstep (se 1 (by rfl) ⟨462002, by rfl⟩ : syracuseStep 616003 = 924005) B924005
theorem B616019 : Blo 614296 616019 := bstep (se 1 (by rfl) ⟨462014, by rfl⟩ : syracuseStep 616019 = 924029) B924029
theorem B616035 : Blo 614296 616035 := bstep (se 1 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 616035 = 924053) B924053
theorem B616051 : Blo 614296 616051 := bstep (se 1 (by rfl) ⟨462038, by rfl⟩ : syracuseStep 616051 = 924077) B924077
theorem B616067 : Blo 614296 616067 := bstep (se 1 (by rfl) ⟨462050, by rfl⟩ : syracuseStep 616067 = 924101) B924101
theorem B1042051 : Blo 614296 1042051 := bstep (se 1 (by rfl) ⟨781538, by rfl⟩ : syracuseStep 1042051 = 1563077) B1563077
theorem B616083 : Blo 614296 616083 := bstep (se 1 (by rfl) ⟨462062, by rfl⟩ : syracuseStep 616083 = 924125) B924125
theorem B616099 : Blo 614296 616099 := bstep (se 1 (by rfl) ⟨462074, by rfl⟩ : syracuseStep 616099 = 924149) B924149
theorem B616115 : Blo 614296 616115 := bstep (se 1 (by rfl) ⟨462086, by rfl⟩ : syracuseStep 616115 = 924173) B924173
theorem B616131 : Blo 614296 616131 := bstep (se 1 (by rfl) ⟨462098, by rfl⟩ : syracuseStep 616131 = 924197) B924197
theorem B616147 : Blo 614296 616147 := bstep (se 1 (by rfl) ⟨462110, by rfl⟩ : syracuseStep 616147 = 924221) B924221
theorem B616163 : Blo 614296 616163 := bstep (se 1 (by rfl) ⟨462122, by rfl⟩ : syracuseStep 616163 = 924245) B924245
theorem B616179 : Blo 614296 616179 := bstep (se 1 (by rfl) ⟨462134, by rfl⟩ : syracuseStep 616179 = 924269) B924269
theorem B616195 : Blo 614296 616195 := bstep (se 1 (by rfl) ⟨462146, by rfl⟩ : syracuseStep 616195 = 924293) B924293
theorem B1042193 : Blo 614296 1042193 := bstep (se 2 (by rfl) ⟨390822, by rfl⟩ : syracuseStep 1042193 = 781645) B781645
theorem B616211 : Blo 614296 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B714515 : Blo 614296 714515 := bstep (se 1 (by rfl) ⟨535886, by rfl⟩ : syracuseStep 714515 = 1071773) B1071773
theorem B616227 : Blo 614296 616227 := bstep (se 1 (by rfl) ⟨462170, by rfl⟩ : syracuseStep 616227 = 924341) B924341
theorem B1107761 : Blo 614296 1107761 := bstep (se 2 (by rfl) ⟨415410, by rfl⟩ : syracuseStep 1107761 = 830821) B830821
theorem B616243 : Blo 614296 616243 := bstep (se 1 (by rfl) ⟨462182, by rfl⟩ : syracuseStep 616243 = 924365) B924365
theorem B616259 : Blo 614296 616259 := bstep (se 1 (by rfl) ⟨462194, by rfl⟩ : syracuseStep 616259 = 924389) B924389
theorem B616275 : Blo 614296 616275 := bstep (se 1 (by rfl) ⟨462206, by rfl⟩ : syracuseStep 616275 = 924413) B924413
theorem B616291 : Blo 614296 616291 := bstep (se 1 (by rfl) ⟨462218, by rfl⟩ : syracuseStep 616291 = 924437) B924437
theorem B780131 : Blo 614296 780131 := bstep (se 1 (by rfl) ⟨585098, by rfl⟩ : syracuseStep 780131 = 1170197) B1170197
theorem B616307 : Blo 614296 616307 := bstep (se 1 (by rfl) ⟨462230, by rfl⟩ : syracuseStep 616307 = 924461) B924461
theorem B616323 : Blo 614296 616323 := bstep (se 1 (by rfl) ⟨462242, by rfl⟩ : syracuseStep 616323 = 924485) B924485
theorem B1173379 : Blo 614296 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B1042321 : Blo 614296 1042321 := bstep (se 2 (by rfl) ⟨390870, by rfl⟩ : syracuseStep 1042321 = 781741) B781741
theorem B616339 : Blo 614296 616339 := bstep (se 1 (by rfl) ⟨462254, by rfl⟩ : syracuseStep 616339 = 924509) B924509
theorem B616355 : Blo 614296 616355 := bstep (se 1 (by rfl) ⟨462266, by rfl⟩ : syracuseStep 616355 = 924533) B924533
theorem B616371 : Blo 614296 616371 := bstep (se 1 (by rfl) ⟨462278, by rfl⟩ : syracuseStep 616371 = 924557) B924557
theorem B1042355 : Blo 614296 1042355 := bstep (se 1 (by rfl) ⟨781766, by rfl⟩ : syracuseStep 1042355 = 1563533) B1563533
theorem B616387 : Blo 614296 616387 := bstep (se 1 (by rfl) ⟨462290, by rfl⟩ : syracuseStep 616387 = 924581) B924581
theorem B616403 : Blo 614296 616403 := bstep (se 1 (by rfl) ⟨462302, by rfl⟩ : syracuseStep 616403 = 924605) B924605
theorem B616419 : Blo 614296 616419 := bstep (se 1 (by rfl) ⟨462314, by rfl⟩ : syracuseStep 616419 = 924629) B924629
theorem B616435 : Blo 614296 616435 := bstep (se 1 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 616435 = 924653) B924653
theorem B616451 : Blo 614296 616451 := bstep (se 1 (by rfl) ⟨462338, by rfl⟩ : syracuseStep 616451 = 924677) B924677
theorem B4679693 : Blo 614296 4679693 := bstep (se 3 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 4679693 = 1754885) B1754885
theorem B616467 : Blo 614296 616467 := bstep (se 1 (by rfl) ⟨462350, by rfl⟩ : syracuseStep 616467 = 924701) B924701
theorem B616483 : Blo 614296 616483 := bstep (se 1 (by rfl) ⟨462362, by rfl⟩ : syracuseStep 616483 = 924725) B924725
theorem B616499 : Blo 614296 616499 := bstep (se 1 (by rfl) ⟨462374, by rfl⟩ : syracuseStep 616499 = 924749) B924749
theorem B1042483 : Blo 614296 1042483 := bstep (se 1 (by rfl) ⟨781862, by rfl⟩ : syracuseStep 1042483 = 1563725) B1563725
theorem B616515 : Blo 614296 616515 := bstep (se 1 (by rfl) ⟨462386, by rfl⟩ : syracuseStep 616515 = 924773) B924773
theorem B616531 : Blo 614296 616531 := bstep (se 1 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 616531 = 924797) B924797
theorem B616547 : Blo 614296 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B616563 : Blo 614296 616563 := bstep (se 1 (by rfl) ⟨462422, by rfl⟩ : syracuseStep 616563 = 924845) B924845
theorem B616579 : Blo 614296 616579 := bstep (se 1 (by rfl) ⟨462434, by rfl⟩ : syracuseStep 616579 = 924869) B924869
theorem B616595 : Blo 614296 616595 := bstep (se 1 (by rfl) ⟨462446, by rfl⟩ : syracuseStep 616595 = 924893) B924893
theorem B616611 : Blo 614296 616611 := bstep (se 1 (by rfl) ⟨462458, by rfl⟩ : syracuseStep 616611 = 924917) B924917
theorem B616627 : Blo 614296 616627 := bstep (se 1 (by rfl) ⟨462470, by rfl⟩ : syracuseStep 616627 = 924941) B924941
theorem B616643 : Blo 614296 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B1042625 : Blo 614296 1042625 := bstep (se 2 (by rfl) ⟨390984, by rfl⟩ : syracuseStep 1042625 = 781969) B781969
theorem B616659 : Blo 614296 616659 := bstep (se 1 (by rfl) ⟨462494, by rfl⟩ : syracuseStep 616659 = 924989) B924989
theorem B616675 : Blo 614296 616675 := bstep (se 1 (by rfl) ⟨462506, by rfl⟩ : syracuseStep 616675 = 925013) B925013
theorem B38070499 : Blo 614296 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B616691 : Blo 614296 616691 := bstep (se 1 (by rfl) ⟨462518, by rfl⟩ : syracuseStep 616691 = 925037) B925037
theorem B616707 : Blo 614296 616707 := bstep (se 1 (by rfl) ⟨462530, by rfl⟩ : syracuseStep 616707 = 925061) B925061
theorem B3500293 : Blo 614296 3500293 := bstep (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) B656305
theorem B616723 : Blo 614296 616723 := bstep (se 1 (by rfl) ⟨462542, by rfl⟩ : syracuseStep 616723 = 925085) B925085
theorem B1108259 : Blo 614296 1108259 := bstep (se 1 (by rfl) ⟨831194, by rfl⟩ : syracuseStep 1108259 = 1662389) B1662389
theorem B616739 : Blo 614296 616739 := bstep (se 1 (by rfl) ⟨462554, by rfl⟩ : syracuseStep 616739 = 925109) B925109
theorem B616755 : Blo 614296 616755 := bstep (se 1 (by rfl) ⟨462566, by rfl⟩ : syracuseStep 616755 = 925133) B925133
theorem B1042753 : Blo 614296 1042753 := bstep (se 2 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 1042753 = 782065) B782065
theorem B616771 : Blo 614296 616771 := bstep (se 1 (by rfl) ⟨462578, by rfl⟩ : syracuseStep 616771 = 925157) B925157
theorem B616787 : Blo 614296 616787 := bstep (se 1 (by rfl) ⟨462590, by rfl⟩ : syracuseStep 616787 = 925181) B925181
theorem B616803 : Blo 614296 616803 := bstep (se 1 (by rfl) ⟨462602, by rfl⟩ : syracuseStep 616803 = 925205) B925205
theorem B1042787 : Blo 614296 1042787 := bstep (se 1 (by rfl) ⟨782090, by rfl⟩ : syracuseStep 1042787 = 1564181) B1564181
theorem B616819 : Blo 614296 616819 := bstep (se 1 (by rfl) ⟨462614, by rfl⟩ : syracuseStep 616819 = 925229) B925229
theorem B616835 : Blo 614296 616835 := bstep (se 1 (by rfl) ⟨462626, by rfl⟩ : syracuseStep 616835 = 925253) B925253
theorem B616851 : Blo 614296 616851 := bstep (se 1 (by rfl) ⟨462638, by rfl⟩ : syracuseStep 616851 = 925277) B925277
theorem B616867 : Blo 614296 616867 := bstep (se 1 (by rfl) ⟨462650, by rfl⟩ : syracuseStep 616867 = 925301) B925301
theorem B616883 : Blo 614296 616883 := bstep (se 1 (by rfl) ⟨462662, by rfl⟩ : syracuseStep 616883 = 925325) B925325
theorem B616899 : Blo 614296 616899 := bstep (se 1 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 616899 = 925349) B925349
theorem B616915 : Blo 614296 616915 := bstep (se 1 (by rfl) ⟨462686, by rfl⟩ : syracuseStep 616915 = 925373) B925373
theorem B616931 : Blo 614296 616931 := bstep (se 1 (by rfl) ⟨462698, by rfl⟩ : syracuseStep 616931 = 925397) B925397
theorem B1042915 : Blo 614296 1042915 := bstep (se 1 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 1042915 = 1564373) B1564373
theorem B616947 : Blo 614296 616947 := bstep (se 1 (by rfl) ⟨462710, by rfl⟩ : syracuseStep 616947 = 925421) B925421
theorem B616963 : Blo 614296 616963 := bstep (se 1 (by rfl) ⟨462722, by rfl⟩ : syracuseStep 616963 = 925445) B925445
theorem B616979 : Blo 614296 616979 := bstep (se 1 (by rfl) ⟨462734, by rfl⟩ : syracuseStep 616979 = 925469) B925469
theorem B780835 : Blo 614296 780835 := bstep (se 1 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 780835 = 1171253) B1171253
theorem B616995 : Blo 614296 616995 := bstep (se 1 (by rfl) ⟨462746, by rfl⟩ : syracuseStep 616995 = 925493) B925493
theorem B617011 : Blo 614296 617011 := bstep (se 1 (by rfl) ⟨462758, by rfl⟩ : syracuseStep 617011 = 925517) B925517
theorem B879169 : Blo 614296 879169 := bstep (se 2 (by rfl) ⟨329688, by rfl⟩ : syracuseStep 879169 = 659377) B659377
theorem B617027 : Blo 614296 617027 := bstep (se 1 (by rfl) ⟨462770, by rfl⟩ : syracuseStep 617027 = 925541) B925541
theorem B617043 : Blo 614296 617043 := bstep (se 1 (by rfl) ⟨462782, by rfl⟩ : syracuseStep 617043 = 925565) B925565
theorem B617059 : Blo 614296 617059 := bstep (se 1 (by rfl) ⟨462794, by rfl⟩ : syracuseStep 617059 = 925589) B925589
theorem B1043057 : Blo 614296 1043057 := bstep (se 2 (by rfl) ⟨391146, by rfl⟩ : syracuseStep 1043057 = 782293) B782293
theorem B617075 : Blo 614296 617075 := bstep (se 1 (by rfl) ⟨462806, by rfl⟩ : syracuseStep 617075 = 925613) B925613
theorem B780931 : Blo 614296 780931 := bstep (se 1 (by rfl) ⟨585698, by rfl⟩ : syracuseStep 780931 = 1171397) B1171397
theorem B617091 : Blo 614296 617091 := bstep (se 1 (by rfl) ⟨462818, by rfl⟩ : syracuseStep 617091 = 925637) B925637
theorem B617107 : Blo 614296 617107 := bstep (se 1 (by rfl) ⟨462830, by rfl⟩ : syracuseStep 617107 = 925661) B925661
theorem B879265 : Blo 614296 879265 := bstep (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) B659449
theorem B617123 : Blo 614296 617123 := bstep (se 1 (by rfl) ⟨462842, by rfl⟩ : syracuseStep 617123 = 925685) B925685
theorem B617139 : Blo 614296 617139 := bstep (se 1 (by rfl) ⟨462854, by rfl⟩ : syracuseStep 617139 = 925709) B925709
theorem B617155 : Blo 614296 617155 := bstep (se 1 (by rfl) ⟨462866, by rfl⟩ : syracuseStep 617155 = 925733) B925733
theorem B617171 : Blo 614296 617171 := bstep (se 1 (by rfl) ⟨462878, by rfl⟩ : syracuseStep 617171 = 925757) B925757
theorem B617187 : Blo 614296 617187 := bstep (se 1 (by rfl) ⟨462890, by rfl⟩ : syracuseStep 617187 = 925781) B925781
theorem B1108721 : Blo 614296 1108721 := bstep (se 2 (by rfl) ⟨415770, by rfl⟩ : syracuseStep 1108721 = 831541) B831541
theorem B5630705 : Blo 614296 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B617203 : Blo 614296 617203 := bstep (se 1 (by rfl) ⟨462902, by rfl⟩ : syracuseStep 617203 = 925805) B925805
theorem B1043185 : Blo 614296 1043185 := bstep (se 2 (by rfl) ⟨391194, by rfl⟩ : syracuseStep 1043185 = 782389) B782389
theorem B617219 : Blo 614296 617219 := bstep (se 1 (by rfl) ⟨462914, by rfl⟩ : syracuseStep 617219 = 925829) B925829
theorem B617235 : Blo 614296 617235 := bstep (se 1 (by rfl) ⟨462926, by rfl⟩ : syracuseStep 617235 = 925853) B925853
theorem B1043219 : Blo 614296 1043219 := bstep (se 1 (by rfl) ⟨782414, by rfl⟩ : syracuseStep 1043219 = 1564829) B1564829
theorem B617251 : Blo 614296 617251 := bstep (se 1 (by rfl) ⟨462938, by rfl⟩ : syracuseStep 617251 = 925877) B925877
theorem B617267 : Blo 614296 617267 := bstep (se 1 (by rfl) ⟨462950, by rfl⟩ : syracuseStep 617267 = 925901) B925901
theorem B617283 : Blo 614296 617283 := bstep (se 1 (by rfl) ⟨462962, by rfl⟩ : syracuseStep 617283 = 925925) B925925
theorem B617299 : Blo 614296 617299 := bstep (se 1 (by rfl) ⟨462974, by rfl⟩ : syracuseStep 617299 = 925949) B925949
theorem B617315 : Blo 614296 617315 := bstep (se 1 (by rfl) ⟨462986, by rfl⟩ : syracuseStep 617315 = 925973) B925973
theorem B617331 : Blo 614296 617331 := bstep (se 1 (by rfl) ⟨462998, by rfl⟩ : syracuseStep 617331 = 925997) B925997
theorem B617347 : Blo 614296 617347 := bstep (se 1 (by rfl) ⟨463010, by rfl⟩ : syracuseStep 617347 = 926021) B926021
theorem B617363 : Blo 614296 617363 := bstep (se 1 (by rfl) ⟨463022, by rfl⟩ : syracuseStep 617363 = 926045) B926045
theorem B1043347 : Blo 614296 1043347 := bstep (se 1 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 1043347 = 1565021) B1565021
theorem B617379 : Blo 614296 617379 := bstep (se 1 (by rfl) ⟨463034, by rfl⟩ : syracuseStep 617379 = 926069) B926069
theorem B617395 : Blo 614296 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B617411 : Blo 614296 617411 := bstep (se 1 (by rfl) ⟨463058, by rfl⟩ : syracuseStep 617411 = 926117) B926117
theorem B617427 : Blo 614296 617427 := bstep (se 1 (by rfl) ⟨463070, by rfl⟩ : syracuseStep 617427 = 926141) B926141
theorem B617443 : Blo 614296 617443 := bstep (se 1 (by rfl) ⟨463082, by rfl⟩ : syracuseStep 617443 = 926165) B926165
theorem B748531 : Blo 614296 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B617459 : Blo 614296 617459 := bstep (se 1 (by rfl) ⟨463094, by rfl⟩ : syracuseStep 617459 = 926189) B926189
theorem B617475 : Blo 614296 617475 := bstep (se 1 (by rfl) ⟨463106, by rfl⟩ : syracuseStep 617475 = 926213) B926213
theorem B617491 : Blo 614296 617491 := bstep (se 1 (by rfl) ⟨463118, by rfl⟩ : syracuseStep 617491 = 926237) B926237
theorem B617507 : Blo 614296 617507 := bstep (se 1 (by rfl) ⟨463130, by rfl⟩ : syracuseStep 617507 = 926261) B926261
theorem B617523 : Blo 614296 617523 := bstep (se 1 (by rfl) ⟨463142, by rfl⟩ : syracuseStep 617523 = 926285) B926285
theorem B617539 : Blo 614296 617539 := bstep (se 1 (by rfl) ⟨463154, by rfl⟩ : syracuseStep 617539 = 926309) B926309
theorem B617555 : Blo 614296 617555 := bstep (se 1 (by rfl) ⟨463166, by rfl⟩ : syracuseStep 617555 = 926333) B926333
theorem B617571 : Blo 614296 617571 := bstep (se 1 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 617571 = 926357) B926357
theorem B781427 : Blo 614296 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B617587 : Blo 614296 617587 := bstep (se 1 (by rfl) ⟨463190, by rfl⟩ : syracuseStep 617587 = 926381) B926381
theorem B617603 : Blo 614296 617603 := bstep (se 1 (by rfl) ⟨463202, by rfl⟩ : syracuseStep 617603 = 926405) B926405
theorem B879761 : Blo 614296 879761 := bstep (se 2 (by rfl) ⟨329910, by rfl⟩ : syracuseStep 879761 = 659821) B659821
theorem B617619 : Blo 614296 617619 := bstep (se 1 (by rfl) ⟨463214, by rfl⟩ : syracuseStep 617619 = 926429) B926429
theorem B617635 : Blo 614296 617635 := bstep (se 1 (by rfl) ⟨463226, by rfl⟩ : syracuseStep 617635 = 926453) B926453
theorem B617651 : Blo 614296 617651 := bstep (se 1 (by rfl) ⟨463238, by rfl⟩ : syracuseStep 617651 = 926477) B926477
theorem B617667 : Blo 614296 617667 := bstep (se 1 (by rfl) ⟨463250, by rfl⟩ : syracuseStep 617667 = 926501) B926501
theorem B617683 : Blo 614296 617683 := bstep (se 1 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 617683 = 926525) B926525
theorem B617699 : Blo 614296 617699 := bstep (se 1 (by rfl) ⟨463274, by rfl⟩ : syracuseStep 617699 = 926549) B926549
theorem B617715 : Blo 614296 617715 := bstep (se 1 (by rfl) ⟨463286, by rfl⟩ : syracuseStep 617715 = 926573) B926573
theorem B617731 : Blo 614296 617731 := bstep (se 1 (by rfl) ⟨463298, by rfl⟩ : syracuseStep 617731 = 926597) B926597
theorem B617747 : Blo 614296 617747 := bstep (se 1 (by rfl) ⟨463310, by rfl⟩ : syracuseStep 617747 = 926621) B926621
theorem B2223395 : Blo 614296 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B617763 : Blo 614296 617763 := bstep (se 1 (by rfl) ⟨463322, by rfl⟩ : syracuseStep 617763 = 926645) B926645
theorem B1109297 : Blo 614296 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B617779 : Blo 614296 617779 := bstep (se 1 (by rfl) ⟨463334, by rfl⟩ : syracuseStep 617779 = 926669) B926669
theorem B617795 : Blo 614296 617795 := bstep (se 1 (by rfl) ⟨463346, by rfl⟩ : syracuseStep 617795 = 926693) B926693
theorem B617811 : Blo 614296 617811 := bstep (se 1 (by rfl) ⟨463358, by rfl⟩ : syracuseStep 617811 = 926717) B926717
theorem B617827 : Blo 614296 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B617843 : Blo 614296 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B617859 : Blo 614296 617859 := bstep (se 1 (by rfl) ⟨463394, by rfl⟩ : syracuseStep 617859 = 926789) B926789
theorem B617875 : Blo 614296 617875 := bstep (se 1 (by rfl) ⟨463406, by rfl⟩ : syracuseStep 617875 = 926813) B926813
theorem B617891 : Blo 614296 617891 := bstep (se 1 (by rfl) ⟨463418, by rfl⟩ : syracuseStep 617891 = 926837) B926837
theorem B617907 : Blo 614296 617907 := bstep (se 1 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 617907 = 926861) B926861
theorem B617923 : Blo 614296 617923 := bstep (se 1 (by rfl) ⟨463442, by rfl⟩ : syracuseStep 617923 = 926885) B926885
theorem B617939 : Blo 614296 617939 := bstep (se 1 (by rfl) ⟨463454, by rfl⟩ : syracuseStep 617939 = 926909) B926909
theorem B617955 : Blo 614296 617955 := bstep (se 1 (by rfl) ⟨463466, by rfl⟩ : syracuseStep 617955 = 926933) B926933
theorem B617971 : Blo 614296 617971 := bstep (se 1 (by rfl) ⟨463478, by rfl⟩ : syracuseStep 617971 = 926957) B926957
theorem B617987 : Blo 614296 617987 := bstep (se 1 (by rfl) ⟨463490, by rfl⟩ : syracuseStep 617987 = 926981) B926981
theorem B618003 : Blo 614296 618003 := bstep (se 1 (by rfl) ⟨463502, by rfl⟩ : syracuseStep 618003 = 927005) B927005
theorem B618019 : Blo 614296 618019 := bstep (se 1 (by rfl) ⟨463514, by rfl⟩ : syracuseStep 618019 = 927029) B927029
theorem B618035 : Blo 614296 618035 := bstep (se 1 (by rfl) ⟨463526, by rfl⟩ : syracuseStep 618035 = 927053) B927053
theorem B618051 : Blo 614296 618051 := bstep (se 1 (by rfl) ⟨463538, by rfl⟩ : syracuseStep 618051 = 927077) B927077
theorem B618067 : Blo 614296 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B618083 : Blo 614296 618083 := bstep (se 1 (by rfl) ⟨463562, by rfl⟩ : syracuseStep 618083 = 927125) B927125
theorem B618099 : Blo 614296 618099 := bstep (se 1 (by rfl) ⟨463574, by rfl⟩ : syracuseStep 618099 = 927149) B927149
theorem B618115 : Blo 614296 618115 := bstep (se 1 (by rfl) ⟨463586, by rfl⟩ : syracuseStep 618115 = 927173) B927173
theorem B618131 : Blo 614296 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B618147 : Blo 614296 618147 := bstep (se 1 (by rfl) ⟨463610, by rfl⟩ : syracuseStep 618147 = 927221) B927221
theorem B618163 : Blo 614296 618163 := bstep (se 1 (by rfl) ⟨463622, by rfl⟩ : syracuseStep 618163 = 927245) B927245
theorem B618179 : Blo 614296 618179 := bstep (se 1 (by rfl) ⟨463634, by rfl⟩ : syracuseStep 618179 = 927269) B927269
theorem B618195 : Blo 614296 618195 := bstep (se 1 (by rfl) ⟨463646, by rfl⟩ : syracuseStep 618195 = 927293) B927293
theorem B618211 : Blo 614296 618211 := bstep (se 1 (by rfl) ⟨463658, by rfl⟩ : syracuseStep 618211 = 927317) B927317
theorem B6942449 : Blo 614296 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B618227 : Blo 614296 618227 := bstep (se 1 (by rfl) ⟨463670, by rfl⟩ : syracuseStep 618227 = 927341) B927341
theorem B618243 : Blo 614296 618243 := bstep (se 1 (by rfl) ⟨463682, by rfl⟩ : syracuseStep 618243 = 927365) B927365
theorem B3960589 : Blo 614296 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B618259 : Blo 614296 618259 := bstep (se 1 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 618259 = 927389) B927389
theorem B618275 : Blo 614296 618275 := bstep (se 1 (by rfl) ⟨463706, by rfl⟩ : syracuseStep 618275 = 927413) B927413
theorem B782131 : Blo 614296 782131 := bstep (se 1 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 782131 = 1173197) B1173197
theorem B618291 : Blo 614296 618291 := bstep (se 1 (by rfl) ⟨463718, by rfl⟩ : syracuseStep 618291 = 927437) B927437
theorem B7499573 : Blo 614296 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B782227 : Blo 614296 782227 := bstep (se 1 (by rfl) ⟨586670, by rfl⟩ : syracuseStep 782227 = 1173341) B1173341
theorem B3502277 : Blo 614296 3502277 := bstep (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) B656677
theorem B1667405 : Blo 614296 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B2224589 : Blo 614296 2224589 := bstep (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) B834221
theorem B4682609 : Blo 614296 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B1668323 : Blo 614296 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B6649073 : Blo 614296 6649073 := bstep (se 2 (by rfl) ⟨2493402, by rfl⟩ : syracuseStep 6649073 = 4986805) B4986805
theorem B2815843 : Blo 614296 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1111985 : Blo 614296 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B8353763 : Blo 614296 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B2227085 : Blo 614296 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B3111857 : Blo 614296 3111857 := bstep (se 2 (by rfl) ⟨1166946, by rfl⟩ : syracuseStep 3111857 = 2333893) B2333893
theorem B4062221 : Blo 614296 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B7896163 : Blo 614296 7896163 := bstep (se 1 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 7896163 = 11844245) B11844245
theorem B2817251 : Blo 614296 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B6651317 : Blo 614296 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B2227661 : Blo 614296 2227661 := bstep (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) B835373
theorem B2850659 : Blo 614296 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B3604337 : Blo 614296 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B4226993 : Blo 614296 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B3506125 : Blo 614296 3506125 := bstep (se 3 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 3506125 = 1314797) B1314797
theorem B2818435 : Blo 614296 2818435 := bstep (se 1 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 2818435 = 4227653) B4227653
theorem B8422019 : Blo 614296 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B656267 : Blo 614296 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B10159139 : Blo 614296 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B9503837 : Blo 614296 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B5932237 : Blo 614296 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B26936725 : Blo 614296 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B1312193 : Blo 614296 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B4752901 : Blo 614296 4752901 := bstep (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) B891169
theorem B984727 : Blo 614296 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B2819933 : Blo 614296 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B25692005 : Blo 614296 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B657271 : Blo 614296 657271 := bstep (se 1 (by rfl) ⟨492953, by rfl⟩ : syracuseStep 657271 = 985907) B985907
theorem B6850861 : Blo 614296 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B985483 : Blo 614296 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B1182131 : Blo 614296 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B887383 : Blo 614296 887383 := bstep (se 1 (by rfl) ⟨665537, by rfl⟩ : syracuseStep 887383 = 1331075) B1331075
theorem B658091 : Blo 614296 658091 := bstep (se 1 (by rfl) ⟨493568, by rfl⟩ : syracuseStep 658091 = 987137) B987137
theorem B1477399 : Blo 614296 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B3115907 : Blo 614296 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B691159 : Blo 614296 691159 := bstep (se 1 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 691159 = 1036739) B1036739
theorem B50760665 : Blo 614296 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B10554461 : Blo 614296 10554461 := bstep (se 3 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 10554461 = 3957923) B3957923
theorem B691339 : Blo 614296 691339 := bstep (se 1 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 691339 = 1037009) B1037009
theorem B5278871 : Blo 614296 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B1313995 : Blo 614296 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B691447 : Blo 614296 691447 := bstep (se 1 (by rfl) ⟨518585, by rfl⟩ : syracuseStep 691447 = 1037171) B1037171
theorem B2493841 : Blo 614296 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B691627 : Blo 614296 691627 := bstep (se 1 (by rfl) ⟨518720, by rfl⟩ : syracuseStep 691627 = 1037441) B1037441
theorem B986585 : Blo 614296 986585 := bstep (se 2 (by rfl) ⟨369969, by rfl⟩ : syracuseStep 986585 = 739939) B739939
theorem B4689413 : Blo 614296 4689413 := bstep (se 4 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 4689413 = 879265) B879265
theorem B691735 : Blo 614296 691735 := bstep (se 1 (by rfl) ⟨518801, by rfl⟩ : syracuseStep 691735 = 1037603) B1037603
theorem B3739229 : Blo 614296 3739229 := bstep (se 3 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 3739229 = 1402211) B1402211
theorem B691915 : Blo 614296 691915 := bstep (se 1 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 691915 = 1037873) B1037873
theorem B2559709 : Blo 614296 2559709 := bstep (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) B959891
theorem B692023 : Blo 614296 692023 := bstep (se 1 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 692023 = 1038035) B1038035
theorem B659287 : Blo 614296 659287 := bstep (se 1 (by rfl) ⟨494465, by rfl⟩ : syracuseStep 659287 = 988931) B988931
theorem B921497 : Blo 614296 921497 := bstep (se 2 (by rfl) ⟨345561, by rfl⟩ : syracuseStep 921497 = 691123) B691123
theorem B692203 : Blo 614296 692203 := bstep (se 1 (by rfl) ⟨519152, by rfl⟩ : syracuseStep 692203 = 1038305) B1038305
theorem B921611 : Blo 614296 921611 := bstep (se 1 (by rfl) ⟨691208, by rfl⟩ : syracuseStep 921611 = 1382417) B1382417
theorem B921623 : Blo 614296 921623 := bstep (se 1 (by rfl) ⟨691217, by rfl⟩ : syracuseStep 921623 = 1382435) B1382435
theorem B3510317 : Blo 614296 3510317 := bstep (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) B1316369
theorem B692311 : Blo 614296 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B921689 : Blo 614296 921689 := bstep (se 2 (by rfl) ⟨345633, by rfl⟩ : syracuseStep 921689 = 691267) B691267
theorem B88871053 : Blo 614296 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B921803 : Blo 614296 921803 := bstep (se 1 (by rfl) ⟨691352, by rfl⟩ : syracuseStep 921803 = 1382705) B1382705
theorem B2494667 : Blo 614296 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B921815 : Blo 614296 921815 := bstep (se 1 (by rfl) ⟨691361, by rfl⟩ : syracuseStep 921815 = 1382723) B1382723
theorem B692491 : Blo 614296 692491 := bstep (se 1 (by rfl) ⟨519368, by rfl⟩ : syracuseStep 692491 = 1038737) B1038737
theorem B921881 : Blo 614296 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B19960181 : Blo 614296 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B692599 : Blo 614296 692599 := bstep (se 1 (by rfl) ⟨519449, by rfl⟩ : syracuseStep 692599 = 1038899) B1038899
theorem B921995 : Blo 614296 921995 := bstep (se 1 (by rfl) ⟨691496, by rfl⟩ : syracuseStep 921995 = 1382993) B1382993
theorem B922007 : Blo 614296 922007 := bstep (se 1 (by rfl) ⟨691505, by rfl⟩ : syracuseStep 922007 = 1383011) B1383011
theorem B922073 : Blo 614296 922073 := bstep (se 2 (by rfl) ⟨345777, by rfl⟩ : syracuseStep 922073 = 691555) B691555
theorem B692779 : Blo 614296 692779 := bstep (se 1 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 692779 = 1039169) B1039169
theorem B1315379 : Blo 614296 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B922187 : Blo 614296 922187 := bstep (se 1 (by rfl) ⟨691640, by rfl⟩ : syracuseStep 922187 = 1383281) B1383281
theorem B922199 : Blo 614296 922199 := bstep (se 1 (by rfl) ⟨691649, by rfl⟩ : syracuseStep 922199 = 1383299) B1383299
theorem B660107 : Blo 614296 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B692887 : Blo 614296 692887 := bstep (se 1 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 692887 = 1039331) B1039331
theorem B922265 : Blo 614296 922265 := bstep (se 2 (by rfl) ⟨345849, by rfl⟩ : syracuseStep 922265 = 691699) B691699
theorem B1905373 : Blo 614296 1905373 := bstep (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) B714515
theorem B9966341 : Blo 614296 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B922379 : Blo 614296 922379 := bstep (se 1 (by rfl) ⟨691784, by rfl⟩ : syracuseStep 922379 = 1383569) B1383569
theorem B1250059 : Blo 614296 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B660235 : Blo 614296 660235 := bstep (se 1 (by rfl) ⟨495176, by rfl⟩ : syracuseStep 660235 = 990353) B990353
theorem B922391 : Blo 614296 922391 := bstep (se 1 (by rfl) ⟨691793, by rfl⟩ : syracuseStep 922391 = 1383587) B1383587
theorem B2954029 : Blo 614296 2954029 := bstep (se 3 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 2954029 = 1107761) B1107761
theorem B1479475 : Blo 614296 1479475 := bstep (se 1 (by rfl) ⟨1109606, by rfl⟩ : syracuseStep 1479475 = 2219213) B2219213
theorem B4002625 : Blo 614296 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B693067 : Blo 614296 693067 := bstep (se 1 (by rfl) ⟨519800, by rfl⟩ : syracuseStep 693067 = 1039601) B1039601
theorem B922457 : Blo 614296 922457 := bstep (se 2 (by rfl) ⟨345921, by rfl⟩ : syracuseStep 922457 = 691843) B691843
theorem B693175 : Blo 614296 693175 := bstep (se 1 (by rfl) ⟨519881, by rfl⟩ : syracuseStep 693175 = 1039763) B1039763
theorem B922571 : Blo 614296 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B922583 : Blo 614296 922583 := bstep (se 1 (by rfl) ⟨691937, by rfl⟩ : syracuseStep 922583 = 1383875) B1383875
theorem B5280785 : Blo 614296 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B922649 : Blo 614296 922649 := bstep (se 2 (by rfl) ⟨345993, by rfl⟩ : syracuseStep 922649 = 691987) B691987
theorem B693355 : Blo 614296 693355 := bstep (se 1 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 693355 = 1040033) B1040033
theorem B922763 : Blo 614296 922763 := bstep (se 1 (by rfl) ⟨692072, by rfl⟩ : syracuseStep 922763 = 1384145) B1384145
theorem B922775 : Blo 614296 922775 := bstep (se 1 (by rfl) ⟨692081, by rfl⟩ : syracuseStep 922775 = 1384163) B1384163
theorem B1283251 : Blo 614296 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B693463 : Blo 614296 693463 := bstep (se 1 (by rfl) ⟨520097, by rfl⟩ : syracuseStep 693463 = 1040195) B1040195
theorem B922841 : Blo 614296 922841 := bstep (se 2 (by rfl) ⟨346065, by rfl⟩ : syracuseStep 922841 = 692131) B692131
theorem B1971479 : Blo 614296 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B922955 : Blo 614296 922955 := bstep (se 1 (by rfl) ⟨692216, by rfl⟩ : syracuseStep 922955 = 1384433) B1384433
theorem B922967 : Blo 614296 922967 := bstep (se 1 (by rfl) ⟨692225, by rfl⟩ : syracuseStep 922967 = 1384451) B1384451
theorem B1316225 : Blo 614296 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B693643 : Blo 614296 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B923033 : Blo 614296 923033 := bstep (se 2 (by rfl) ⟨346137, by rfl⟩ : syracuseStep 923033 = 692275) B692275
theorem B1480139 : Blo 614296 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B693751 : Blo 614296 693751 := bstep (se 1 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 693751 = 1040627) B1040627
theorem B923147 : Blo 614296 923147 := bstep (se 1 (by rfl) ⟨692360, by rfl⟩ : syracuseStep 923147 = 1384721) B1384721
theorem B923159 : Blo 614296 923159 := bstep (se 1 (by rfl) ⟨692369, by rfl⟩ : syracuseStep 923159 = 1384739) B1384739
theorem B923225 : Blo 614296 923225 := bstep (se 2 (by rfl) ⟨346209, by rfl⟩ : syracuseStep 923225 = 692419) B692419
theorem B693931 : Blo 614296 693931 := bstep (se 1 (by rfl) ⟨520448, by rfl⟩ : syracuseStep 693931 = 1040897) B1040897
theorem B2102987 : Blo 614296 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B923339 : Blo 614296 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B923351 : Blo 614296 923351 := bstep (se 1 (by rfl) ⟨692513, by rfl⟩ : syracuseStep 923351 = 1385027) B1385027
theorem B1316567 : Blo 614296 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B1775321 : Blo 614296 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B694039 : Blo 614296 694039 := bstep (se 1 (by rfl) ⟨520529, by rfl⟩ : syracuseStep 694039 = 1041059) B1041059
theorem B923417 : Blo 614296 923417 := bstep (se 2 (by rfl) ⟨346281, by rfl⟩ : syracuseStep 923417 = 692563) B692563
theorem B1382219 : Blo 614296 1382219 := bstep (se 1 (by rfl) ⟨1036664, by rfl⟩ : syracuseStep 1382219 = 2073329) B2073329
theorem B1382273 : Blo 614296 1382273 := bstep (se 2 (by rfl) ⟨518352, by rfl⟩ : syracuseStep 1382273 = 1036705) B1036705
theorem B4691843 : Blo 614296 4691843 := bstep (se 1 (by rfl) ⟨3518882, by rfl⟩ : syracuseStep 4691843 = 7037765) B7037765
theorem B923531 : Blo 614296 923531 := bstep (se 1 (by rfl) ⟨692648, by rfl⟩ : syracuseStep 923531 = 1385297) B1385297
theorem B923543 : Blo 614296 923543 := bstep (se 1 (by rfl) ⟨692657, by rfl⟩ : syracuseStep 923543 = 1385315) B1385315
theorem B694219 : Blo 614296 694219 := bstep (se 1 (by rfl) ⟨520664, by rfl⟩ : syracuseStep 694219 = 1041329) B1041329
theorem B923609 : Blo 614296 923609 := bstep (se 2 (by rfl) ⟨346353, by rfl⟩ : syracuseStep 923609 = 692707) B692707
theorem B4429829 : Blo 614296 4429829 := bstep (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) B830593
theorem B1185817 : Blo 614296 1185817 := bstep (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) B889363
theorem B694327 : Blo 614296 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B923723 : Blo 614296 923723 := bstep (se 1 (by rfl) ⟨692792, by rfl⟩ : syracuseStep 923723 = 1385585) B1385585
theorem B923735 : Blo 614296 923735 := bstep (se 1 (by rfl) ⟨692801, by rfl⟩ : syracuseStep 923735 = 1385603) B1385603
theorem B1382489 : Blo 614296 1382489 := bstep (se 2 (by rfl) ⟨518433, by rfl⟩ : syracuseStep 1382489 = 1036867) B1036867
theorem B5609573 : Blo 614296 5609573 := bstep (se 4 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 5609573 = 1051795) B1051795
theorem B923801 : Blo 614296 923801 := bstep (se 2 (by rfl) ⟨346425, by rfl⟩ : syracuseStep 923801 = 692851) B692851
theorem B1382579 : Blo 614296 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B1382615 : Blo 614296 1382615 := bstep (se 1 (by rfl) ⟨1036961, by rfl⟩ : syracuseStep 1382615 = 2073923) B2073923
theorem B1874141 : Blo 614296 1874141 := bstep (se 3 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 1874141 = 702803) B702803
theorem B694507 : Blo 614296 694507 := bstep (se 1 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 694507 = 1041761) B1041761
theorem B923915 : Blo 614296 923915 := bstep (se 1 (by rfl) ⟨692936, by rfl⟩ : syracuseStep 923915 = 1385873) B1385873
theorem B923927 : Blo 614296 923927 := bstep (se 1 (by rfl) ⟨692945, by rfl⟩ : syracuseStep 923927 = 1385891) B1385891
theorem B694615 : Blo 614296 694615 := bstep (se 1 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 694615 = 1041923) B1041923
theorem B923993 : Blo 614296 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B1382795 : Blo 614296 1382795 := bstep (se 1 (by rfl) ⟨1037096, by rfl⟩ : syracuseStep 1382795 = 2074193) B2074193
theorem B1382849 : Blo 614296 1382849 := bstep (se 2 (by rfl) ⟨518568, by rfl⟩ : syracuseStep 1382849 = 1037137) B1037137
theorem B924107 : Blo 614296 924107 := bstep (se 1 (by rfl) ⟨693080, by rfl⟩ : syracuseStep 924107 = 1386161) B1386161
theorem B924119 : Blo 614296 924119 := bstep (se 1 (by rfl) ⟨693089, by rfl⟩ : syracuseStep 924119 = 1386179) B1386179
theorem B694795 : Blo 614296 694795 := bstep (se 1 (by rfl) ⟨521096, by rfl⟩ : syracuseStep 694795 = 1042193) B1042193
theorem B3119633 : Blo 614296 3119633 := bstep (se 2 (by rfl) ⟨1169862, by rfl⟩ : syracuseStep 3119633 = 2339725) B2339725
theorem B924185 : Blo 614296 924185 := bstep (se 2 (by rfl) ⟨346569, by rfl⟩ : syracuseStep 924185 = 693139) B693139
theorem B1972811 : Blo 614296 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B694903 : Blo 614296 694903 := bstep (se 1 (by rfl) ⟨521177, by rfl⟩ : syracuseStep 694903 = 1042355) B1042355
theorem B2628227 : Blo 614296 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B924299 : Blo 614296 924299 := bstep (se 1 (by rfl) ⟨693224, by rfl⟩ : syracuseStep 924299 = 1386449) B1386449
theorem B924311 : Blo 614296 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B1383065 : Blo 614296 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B3119795 : Blo 614296 3119795 := bstep (se 1 (by rfl) ⟨2339846, by rfl⟩ : syracuseStep 3119795 = 4679693) B4679693
theorem B924377 : Blo 614296 924377 := bstep (se 2 (by rfl) ⟨346641, by rfl⟩ : syracuseStep 924377 = 693283) B693283
theorem B1383155 : Blo 614296 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B1383191 : Blo 614296 1383191 := bstep (se 1 (by rfl) ⟨1037393, by rfl⟩ : syracuseStep 1383191 = 2074787) B2074787
theorem B695083 : Blo 614296 695083 := bstep (se 1 (by rfl) ⟨521312, by rfl⟩ : syracuseStep 695083 = 1042625) B1042625
theorem B924491 : Blo 614296 924491 := bstep (se 1 (by rfl) ⟨693368, by rfl⟩ : syracuseStep 924491 = 1386737) B1386737
theorem B924503 : Blo 614296 924503 := bstep (se 1 (by rfl) ⟨693377, by rfl⟩ : syracuseStep 924503 = 1386755) B1386755
theorem B5249893 : Blo 614296 5249893 := bstep (se 4 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 5249893 = 984355) B984355
theorem B1973143 : Blo 614296 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B695191 : Blo 614296 695191 := bstep (se 1 (by rfl) ⟨521393, by rfl⟩ : syracuseStep 695191 = 1042787) B1042787
theorem B924569 : Blo 614296 924569 := bstep (se 2 (by rfl) ⟨346713, by rfl⟩ : syracuseStep 924569 = 693427) B693427
theorem B1383371 : Blo 614296 1383371 := bstep (se 1 (by rfl) ⟨1037528, by rfl⟩ : syracuseStep 1383371 = 2075057) B2075057
theorem B1383425 : Blo 614296 1383425 := bstep (se 2 (by rfl) ⟨518784, by rfl⟩ : syracuseStep 1383425 = 1037569) B1037569
theorem B924683 : Blo 614296 924683 := bstep (se 1 (by rfl) ⟨693512, by rfl⟩ : syracuseStep 924683 = 1387025) B1387025
theorem B924695 : Blo 614296 924695 := bstep (se 1 (by rfl) ⟨693521, by rfl⟩ : syracuseStep 924695 = 1387043) B1387043
theorem B695371 : Blo 614296 695371 := bstep (se 1 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 695371 = 1043057) B1043057
theorem B924761 : Blo 614296 924761 := bstep (se 2 (by rfl) ⟨346785, by rfl⟩ : syracuseStep 924761 = 693571) B693571
theorem B1318027 : Blo 614296 1318027 := bstep (se 1 (by rfl) ⟨988520, by rfl⟩ : syracuseStep 1318027 = 1977041) B1977041
theorem B695479 : Blo 614296 695479 := bstep (se 1 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 695479 = 1043219) B1043219
theorem B924875 : Blo 614296 924875 := bstep (se 1 (by rfl) ⟨693656, by rfl⟩ : syracuseStep 924875 = 1387313) B1387313
theorem B924887 : Blo 614296 924887 := bstep (se 1 (by rfl) ⟨693665, by rfl⟩ : syracuseStep 924887 = 1387331) B1387331
theorem B1383641 : Blo 614296 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B924953 : Blo 614296 924953 := bstep (se 2 (by rfl) ⟨346857, by rfl⟩ : syracuseStep 924953 = 693715) B693715
theorem B1383731 : Blo 614296 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B1973555 : Blo 614296 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B1383767 : Blo 614296 1383767 := bstep (se 1 (by rfl) ⟨1037825, by rfl⟩ : syracuseStep 1383767 = 2075651) B2075651
theorem B3939677 : Blo 614296 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B925067 : Blo 614296 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B1318283 : Blo 614296 1318283 := bstep (se 1 (by rfl) ⟨988712, by rfl⟩ : syracuseStep 1318283 = 1977425) B1977425
theorem B925079 : Blo 614296 925079 := bstep (se 1 (by rfl) ⟨693809, by rfl⟩ : syracuseStep 925079 = 1387619) B1387619
theorem B925145 : Blo 614296 925145 := bstep (se 2 (by rfl) ⟨346929, by rfl⟩ : syracuseStep 925145 = 693859) B693859
theorem B1383947 : Blo 614296 1383947 := bstep (se 1 (by rfl) ⟨1037960, by rfl⟩ : syracuseStep 1383947 = 2075921) B2075921
theorem B1482263 : Blo 614296 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B1384001 : Blo 614296 1384001 := bstep (se 2 (by rfl) ⟨519000, by rfl⟩ : syracuseStep 1384001 = 1038001) B1038001
theorem B925259 : Blo 614296 925259 := bstep (se 1 (by rfl) ⟨693944, by rfl⟩ : syracuseStep 925259 = 1387889) B1387889
theorem B925271 : Blo 614296 925271 := bstep (se 1 (by rfl) ⟨693953, by rfl⟩ : syracuseStep 925271 = 1387907) B1387907
theorem B925337 : Blo 614296 925337 := bstep (se 2 (by rfl) ⟨347001, by rfl⟩ : syracuseStep 925337 = 694003) B694003
theorem B90054341 : Blo 614296 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B925451 : Blo 614296 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B925463 : Blo 614296 925463 := bstep (se 1 (by rfl) ⟨694097, by rfl⟩ : syracuseStep 925463 = 1388195) B1388195
theorem B1384217 : Blo 614296 1384217 := bstep (se 2 (by rfl) ⟨519081, by rfl⟩ : syracuseStep 1384217 = 1038163) B1038163
theorem B5250851 : Blo 614296 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B925529 : Blo 614296 925529 := bstep (se 2 (by rfl) ⟨347073, by rfl⟩ : syracuseStep 925529 = 694147) B694147
theorem B1384307 : Blo 614296 1384307 := bstep (se 1 (by rfl) ⟨1038230, by rfl⟩ : syracuseStep 1384307 = 2076461) B2076461
theorem B1384343 : Blo 614296 1384343 := bstep (se 1 (by rfl) ⟨1038257, by rfl⟩ : syracuseStep 1384343 = 2076515) B2076515
theorem B925643 : Blo 614296 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B925655 : Blo 614296 925655 := bstep (se 1 (by rfl) ⟨694241, by rfl⟩ : syracuseStep 925655 = 1388483) B1388483
theorem B925721 : Blo 614296 925721 := bstep (se 2 (by rfl) ⟨347145, by rfl⟩ : syracuseStep 925721 = 694291) B694291
theorem B4005953 : Blo 614296 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B1384523 : Blo 614296 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B1384577 : Blo 614296 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B2334851 : Blo 614296 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B925835 : Blo 614296 925835 := bstep (se 1 (by rfl) ⟨694376, by rfl⟩ : syracuseStep 925835 = 1388753) B1388753
theorem B2334865 : Blo 614296 2334865 := bstep (se 2 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 2334865 = 1751149) B1751149
theorem B925847 : Blo 614296 925847 := bstep (se 1 (by rfl) ⟨694385, by rfl⟩ : syracuseStep 925847 = 1388771) B1388771
theorem B1974451 : Blo 614296 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B925913 : Blo 614296 925913 := bstep (se 2 (by rfl) ⟨347217, by rfl⟩ : syracuseStep 925913 = 694435) B694435
theorem B2629853 : Blo 614296 2629853 := bstep (se 3 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 2629853 = 986195) B986195
theorem B926027 : Blo 614296 926027 := bstep (se 1 (by rfl) ⟨694520, by rfl⟩ : syracuseStep 926027 = 1389041) B1389041
theorem B926039 : Blo 614296 926039 := bstep (se 1 (by rfl) ⟨694529, by rfl⟩ : syracuseStep 926039 = 1389059) B1389059
theorem B1384793 : Blo 614296 1384793 := bstep (se 2 (by rfl) ⟨519297, by rfl⟩ : syracuseStep 1384793 = 1038595) B1038595
theorem B1319257 : Blo 614296 1319257 := bstep (se 2 (by rfl) ⟨494721, by rfl⟩ : syracuseStep 1319257 = 989443) B989443
theorem B926105 : Blo 614296 926105 := bstep (se 2 (by rfl) ⟨347289, by rfl⟩ : syracuseStep 926105 = 694579) B694579
theorem B1384883 : Blo 614296 1384883 := bstep (se 1 (by rfl) ⟨1038662, by rfl⟩ : syracuseStep 1384883 = 2077325) B2077325
theorem B2335169 : Blo 614296 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1384919 : Blo 614296 1384919 := bstep (se 1 (by rfl) ⟨1038689, by rfl⟩ : syracuseStep 1384919 = 2077379) B2077379
theorem B1319411 : Blo 614296 1319411 := bstep (se 1 (by rfl) ⟨989558, by rfl⟩ : syracuseStep 1319411 = 1979117) B1979117
theorem B926219 : Blo 614296 926219 := bstep (se 1 (by rfl) ⟨694664, by rfl⟩ : syracuseStep 926219 = 1389329) B1389329
theorem B926231 : Blo 614296 926231 := bstep (se 1 (by rfl) ⟨694673, by rfl⟩ : syracuseStep 926231 = 1389347) B1389347
theorem B3121739 : Blo 614296 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B1188427 : Blo 614296 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B2105945 : Blo 614296 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B926297 : Blo 614296 926297 := bstep (se 2 (by rfl) ⟨347361, by rfl⟩ : syracuseStep 926297 = 694723) B694723
theorem B1385099 : Blo 614296 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B1385153 : Blo 614296 1385153 := bstep (se 2 (by rfl) ⟨519432, by rfl⟩ : syracuseStep 1385153 = 1038865) B1038865
theorem B926411 : Blo 614296 926411 := bstep (se 1 (by rfl) ⟨694808, by rfl⟩ : syracuseStep 926411 = 1389617) B1389617
theorem B926423 : Blo 614296 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B926489 : Blo 614296 926489 := bstep (se 2 (by rfl) ⟨347433, by rfl⟩ : syracuseStep 926489 = 694867) B694867
theorem B4432715 : Blo 614296 4432715 := bstep (se 1 (by rfl) ⟨3324536, by rfl⟩ : syracuseStep 4432715 = 6649073) B6649073
theorem B2073437 : Blo 614296 2073437 := bstep (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) B777539
theorem B926603 : Blo 614296 926603 := bstep (se 1 (by rfl) ⟨694952, by rfl⟩ : syracuseStep 926603 = 1389905) B1389905
theorem B2630551 : Blo 614296 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B926615 : Blo 614296 926615 := bstep (se 1 (by rfl) ⟨694961, by rfl⟩ : syracuseStep 926615 = 1389923) B1389923
theorem B1385369 : Blo 614296 1385369 := bstep (se 2 (by rfl) ⟨519513, by rfl⟩ : syracuseStep 1385369 = 1039027) B1039027
theorem B926681 : Blo 614296 926681 := bstep (se 2 (by rfl) ⟨347505, by rfl⟩ : syracuseStep 926681 = 695011) B695011
theorem B1385459 : Blo 614296 1385459 := bstep (se 1 (by rfl) ⟨1039094, by rfl⟩ : syracuseStep 1385459 = 2078189) B2078189
theorem B1319923 : Blo 614296 1319923 := bstep (se 1 (by rfl) ⟨989942, by rfl⟩ : syracuseStep 1319923 = 1979885) B1979885
theorem B1385495 : Blo 614296 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B22848581 : Blo 614296 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B926795 : Blo 614296 926795 := bstep (se 1 (by rfl) ⟨695096, by rfl⟩ : syracuseStep 926795 = 1390193) B1390193
theorem B926807 : Blo 614296 926807 := bstep (se 1 (by rfl) ⟨695105, by rfl⟩ : syracuseStep 926807 = 1390211) B1390211
theorem B2335837 : Blo 614296 2335837 := bstep (se 3 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 2335837 = 875939) B875939
theorem B926873 : Blo 614296 926873 := bstep (se 2 (by rfl) ⟨347577, by rfl⟩ : syracuseStep 926873 = 695155) B695155
theorem B1385675 : Blo 614296 1385675 := bstep (se 1 (by rfl) ⟨1039256, by rfl⟩ : syracuseStep 1385675 = 2078513) B2078513
theorem B1385729 : Blo 614296 1385729 := bstep (se 2 (by rfl) ⟨519648, by rfl⟩ : syracuseStep 1385729 = 1039297) B1039297
theorem B926987 : Blo 614296 926987 := bstep (se 1 (by rfl) ⟨695240, by rfl⟩ : syracuseStep 926987 = 1390481) B1390481
theorem B926999 : Blo 614296 926999 := bstep (se 1 (by rfl) ⟨695249, by rfl⟩ : syracuseStep 926999 = 1390499) B1390499
theorem B927065 : Blo 614296 927065 := bstep (se 2 (by rfl) ⟨347649, by rfl⟩ : syracuseStep 927065 = 695299) B695299
theorem B927179 : Blo 614296 927179 := bstep (se 1 (by rfl) ⟨695384, by rfl⟩ : syracuseStep 927179 = 1390769) B1390769
theorem B927191 : Blo 614296 927191 := bstep (se 1 (by rfl) ⟨695393, by rfl⟩ : syracuseStep 927191 = 1390787) B1390787
theorem B1385945 : Blo 614296 1385945 := bstep (se 2 (by rfl) ⟨519729, by rfl⟩ : syracuseStep 1385945 = 1039459) B1039459
theorem B10528217 : Blo 614296 10528217 := bstep (se 2 (by rfl) ⟨3948081, by rfl⟩ : syracuseStep 10528217 = 7896163) B7896163
theorem B927257 : Blo 614296 927257 := bstep (se 2 (by rfl) ⟨347721, by rfl⟩ : syracuseStep 927257 = 695443) B695443
theorem B1386035 : Blo 614296 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B1386071 : Blo 614296 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B927371 : Blo 614296 927371 := bstep (se 1 (by rfl) ⟨695528, by rfl⟩ : syracuseStep 927371 = 1391057) B1391057
theorem B927383 : Blo 614296 927383 := bstep (se 1 (by rfl) ⟨695537, by rfl⟩ : syracuseStep 927383 = 1391075) B1391075
theorem B1386251 : Blo 614296 1386251 := bstep (se 1 (by rfl) ⟨1039688, by rfl⟩ : syracuseStep 1386251 = 2079377) B2079377
theorem B1386305 : Blo 614296 1386305 := bstep (se 2 (by rfl) ⟨519864, by rfl⟩ : syracuseStep 1386305 = 1039729) B1039729
theorem B1484723 : Blo 614296 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B2074571 : Blo 614296 2074571 := bstep (se 1 (by rfl) ⟨1555928, by rfl⟩ : syracuseStep 2074571 = 3111857) B3111857
theorem B1386521 : Blo 614296 1386521 := bstep (se 2 (by rfl) ⟨519945, by rfl⟩ : syracuseStep 1386521 = 1039891) B1039891
theorem B1386611 : Blo 614296 1386611 := bstep (se 1 (by rfl) ⟨1039958, by rfl⟩ : syracuseStep 1386611 = 2079917) B2079917
theorem B1386647 : Blo 614296 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B1878167 : Blo 614296 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B4434097 : Blo 614296 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B2074841 : Blo 614296 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B2631953 : Blo 614296 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B4434211 : Blo 614296 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1485107 : Blo 614296 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B3123521 : Blo 614296 3123521 := bstep (se 2 (by rfl) ⟨1171320, by rfl⟩ : syracuseStep 3123521 = 2342641) B2342641
theorem B1386827 : Blo 614296 1386827 := bstep (se 1 (by rfl) ⟨1040120, by rfl⟩ : syracuseStep 1386827 = 2080241) B2080241
theorem B2337113 : Blo 614296 2337113 := bstep (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) B1752835
theorem B1386881 : Blo 614296 1386881 := bstep (se 2 (by rfl) ⟨520080, by rfl⟩ : syracuseStep 1386881 = 1040161) B1040161
theorem B2402891 : Blo 614296 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B1387097 : Blo 614296 1387097 := bstep (se 2 (by rfl) ⟨520161, by rfl⟩ : syracuseStep 1387097 = 1040323) B1040323
theorem B1387187 : Blo 614296 1387187 := bstep (se 1 (by rfl) ⟨1040390, by rfl⟩ : syracuseStep 1387187 = 2080781) B2080781
theorem B1387223 : Blo 614296 1387223 := bstep (se 1 (by rfl) ⟨1040417, by rfl⟩ : syracuseStep 1387223 = 2080835) B2080835
theorem B1583833 : Blo 614296 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B1387403 : Blo 614296 1387403 := bstep (se 1 (by rfl) ⟨1040552, by rfl⟩ : syracuseStep 1387403 = 2081105) B2081105
theorem B2075543 : Blo 614296 2075543 := bstep (se 1 (by rfl) ⟨1556657, by rfl⟩ : syracuseStep 2075543 = 3113315) B3113315
theorem B1387457 : Blo 614296 1387457 := bstep (se 2 (by rfl) ⟨520296, by rfl⟩ : syracuseStep 1387457 = 1040593) B1040593
theorem B9743435 : Blo 614296 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B1387673 : Blo 614296 1387673 := bstep (se 2 (by rfl) ⟨520377, by rfl⟩ : syracuseStep 1387673 = 1040755) B1040755
theorem B1387763 : Blo 614296 1387763 := bstep (se 1 (by rfl) ⟨1040822, by rfl⟩ : syracuseStep 1387763 = 2081645) B2081645
theorem B1387799 : Blo 614296 1387799 := bstep (se 1 (by rfl) ⟨1040849, by rfl⟩ : syracuseStep 1387799 = 2081699) B2081699
theorem B3517789 : Blo 614296 3517789 := bstep (se 3 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 3517789 = 1319171) B1319171
theorem B2076083 : Blo 614296 2076083 := bstep (se 1 (by rfl) ⟨1557062, by rfl⟩ : syracuseStep 2076083 = 3114125) B3114125
theorem B1387979 : Blo 614296 1387979 := bstep (se 1 (by rfl) ⟨1040984, by rfl⟩ : syracuseStep 1387979 = 2081969) B2081969
theorem B830935 : Blo 614296 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B1388033 : Blo 614296 1388033 := bstep (se 2 (by rfl) ⟨520512, by rfl⟩ : syracuseStep 1388033 = 1041025) B1041025
theorem B2502161 : Blo 614296 2502161 := bstep (se 2 (by rfl) ⟨938310, by rfl⟩ : syracuseStep 2502161 = 1876621) B1876621
theorem B3943981 : Blo 614296 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B2666029 : Blo 614296 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2502289 : Blo 614296 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B2076353 : Blo 614296 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B2666201 : Blo 614296 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B1388249 : Blo 614296 1388249 := bstep (se 2 (by rfl) ⟨520593, by rfl⟩ : syracuseStep 1388249 = 1041187) B1041187
theorem B2109149 : Blo 614296 2109149 := bstep (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) B790931
theorem B1388339 : Blo 614296 1388339 := bstep (se 1 (by rfl) ⟨1041254, by rfl⟩ : syracuseStep 1388339 = 2082509) B2082509
theorem B1388375 : Blo 614296 1388375 := bstep (se 1 (by rfl) ⟨1041281, by rfl⟩ : syracuseStep 1388375 = 2082563) B2082563
theorem B2338739 : Blo 614296 2338739 := bstep (se 1 (by rfl) ⟨1754054, by rfl⟩ : syracuseStep 2338739 = 3508109) B3508109
theorem B634807 : Blo 614296 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B2338753 : Blo 614296 2338753 := bstep (se 2 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 2338753 = 1754065) B1754065
theorem B1388555 : Blo 614296 1388555 := bstep (se 1 (by rfl) ⟨1041416, by rfl⟩ : syracuseStep 1388555 = 2082833) B2082833
theorem B1388609 : Blo 614296 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B8859779 : Blo 614296 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B3551363 : Blo 614296 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B3125465 : Blo 614296 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B2076893 : Blo 614296 2076893 := bstep (se 3 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 2076893 = 778835) B778835
theorem B1388825 : Blo 614296 1388825 := bstep (se 2 (by rfl) ⟨520809, by rfl⟩ : syracuseStep 1388825 = 1041619) B1041619
theorem B1388915 : Blo 614296 1388915 := bstep (se 1 (by rfl) ⟨1041686, by rfl⟩ : syracuseStep 1388915 = 2083373) B2083373
theorem B1388951 : Blo 614296 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B5255603 : Blo 614296 5255603 := bstep (se 1 (by rfl) ⟨3941702, by rfl⟩ : syracuseStep 5255603 = 7883405) B7883405
theorem B1389131 : Blo 614296 1389131 := bstep (se 1 (by rfl) ⟨1041848, by rfl⟩ : syracuseStep 1389131 = 2083697) B2083697
theorem B1389185 : Blo 614296 1389185 := bstep (se 2 (by rfl) ⟨520944, by rfl⟩ : syracuseStep 1389185 = 1041889) B1041889
theorem B1389401 : Blo 614296 1389401 := bstep (se 2 (by rfl) ⟨521025, by rfl⟩ : syracuseStep 1389401 = 1042051) B1042051
theorem B1389491 : Blo 614296 1389491 := bstep (se 1 (by rfl) ⟨1042118, by rfl⟩ : syracuseStep 1389491 = 2084237) B2084237
theorem B1389527 : Blo 614296 1389527 := bstep (se 1 (by rfl) ⟨1042145, by rfl⟩ : syracuseStep 1389527 = 2084291) B2084291
theorem B1389707 : Blo 614296 1389707 := bstep (se 1 (by rfl) ⟨1042280, by rfl⟩ : syracuseStep 1389707 = 2084561) B2084561
theorem B2634925 : Blo 614296 2634925 := bstep (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) B988097
theorem B1389761 : Blo 614296 1389761 := bstep (se 2 (by rfl) ⟨521160, by rfl⟩ : syracuseStep 1389761 = 1042321) B1042321
theorem B2078027 : Blo 614296 2078027 := bstep (se 1 (by rfl) ⟨1558520, by rfl⟩ : syracuseStep 2078027 = 3117041) B3117041
theorem B1389977 : Blo 614296 1389977 := bstep (se 2 (by rfl) ⟨521241, by rfl⟩ : syracuseStep 1389977 = 1042483) B1042483
theorem B1390067 : Blo 614296 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B2635267 : Blo 614296 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1390103 : Blo 614296 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B2078297 : Blo 614296 2078297 := bstep (se 2 (by rfl) ⟨779361, by rfl⟩ : syracuseStep 2078297 = 1558723) B1558723
theorem B11417219 : Blo 614296 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B4667057 : Blo 614296 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B1390283 : Blo 614296 1390283 := bstep (se 1 (by rfl) ⟨1042712, by rfl⟩ : syracuseStep 1390283 = 2085425) B2085425
theorem B1128179 : Blo 614296 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B1390337 : Blo 614296 1390337 := bstep (se 2 (by rfl) ⟨521376, by rfl⟩ : syracuseStep 1390337 = 1042753) B1042753
theorem B3127085 : Blo 614296 3127085 := bstep (se 3 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 3127085 = 1172657) B1172657
theorem B2340683 : Blo 614296 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B2340697 : Blo 614296 2340697 := bstep (se 2 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 2340697 = 1755523) B1755523
theorem B1390553 : Blo 614296 1390553 := bstep (se 2 (by rfl) ⟨521457, by rfl⟩ : syracuseStep 1390553 = 1042915) B1042915
theorem B1390643 : Blo 614296 1390643 := bstep (se 1 (by rfl) ⟨1042982, by rfl⟩ : syracuseStep 1390643 = 2085965) B2085965
theorem B1390679 : Blo 614296 1390679 := bstep (se 1 (by rfl) ⟨1043009, by rfl⟩ : syracuseStep 1390679 = 2086019) B2086019
theorem B6666371 : Blo 614296 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B4667543 : Blo 614296 4667543 := bstep (se 1 (by rfl) ⟨3500657, by rfl⟩ : syracuseStep 4667543 = 7001315) B7001315
theorem B1390859 : Blo 614296 1390859 := bstep (se 1 (by rfl) ⟨1043144, by rfl⟩ : syracuseStep 1390859 = 2086289) B2086289
theorem B2078999 : Blo 614296 2078999 := bstep (se 1 (by rfl) ⟨1559249, by rfl⟩ : syracuseStep 2078999 = 3118499) B3118499
theorem B1390913 : Blo 614296 1390913 := bstep (se 2 (by rfl) ⟨521592, by rfl⟩ : syracuseStep 1390913 = 1043185) B1043185
theorem B2636225 : Blo 614296 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B1391129 : Blo 614296 1391129 := bstep (se 2 (by rfl) ⟨521673, by rfl⟩ : syracuseStep 1391129 = 1043347) B1043347
theorem B703255 : Blo 614296 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B2341655 : Blo 614296 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B2079539 : Blo 614296 2079539 := bstep (se 1 (by rfl) ⟨1559654, by rfl⟩ : syracuseStep 2079539 = 3119309) B3119309
theorem B2505779 : Blo 614296 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B2079809 : Blo 614296 2079809 := bstep (se 2 (by rfl) ⟨779928, by rfl⟩ : syracuseStep 2079809 = 1559857) B1559857
theorem B1555787 : Blo 614296 1555787 := bstep (se 1 (by rfl) ⟨1166840, by rfl⟩ : syracuseStep 1555787 = 2333681) B2333681
theorem B2080349 : Blo 614296 2080349 := bstep (se 3 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 2080349 = 780131) B780131
theorem B1752779 : Blo 614296 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B2637643 : Blo 614296 2637643 := bstep (se 1 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 2637643 = 3956465) B3956465
theorem B2342915 : Blo 614296 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1753177 : Blo 614296 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B2637917 : Blo 614296 2637917 := bstep (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) B989219
theorem B1556759 : Blo 614296 1556759 := bstep (se 1 (by rfl) ⟨1167569, by rfl⟩ : syracuseStep 1556759 = 2335139) B2335139
theorem B14959235 : Blo 614296 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B2081483 : Blo 614296 2081483 := bstep (se 1 (by rfl) ⟨1561112, by rfl⟩ : syracuseStep 2081483 = 3122225) B3122225
theorem B2802521 : Blo 614296 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1557427 : Blo 614296 1557427 := bstep (se 1 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 1557427 = 2336141) B2336141
theorem B2081753 : Blo 614296 2081753 := bstep (se 2 (by rfl) ⟨780657, by rfl⟩ : syracuseStep 2081753 = 1561315) B1561315
theorem B2802653 : Blo 614296 2802653 := bstep (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) B1050995
theorem B1557569 : Blo 614296 1557569 := bstep (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) B1168177
theorem B1754419 : Blo 614296 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B1689025 : Blo 614296 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B738839 : Blo 614296 738839 := bstep (se 1 (by rfl) ⟨554129, by rfl⟩ : syracuseStep 738839 = 1108259) B1108259
theorem B2082455 : Blo 614296 2082455 := bstep (se 1 (by rfl) ⟨1561841, by rfl⟩ : syracuseStep 2082455 = 3123683) B3123683
theorem B739147 : Blo 614296 739147 := bstep (se 1 (by rfl) ⟨554360, by rfl⟩ : syracuseStep 739147 = 1108721) B1108721
theorem B3753803 : Blo 614296 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B4507571 : Blo 614296 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B2082995 : Blo 614296 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B739531 : Blo 614296 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B1558835 : Blo 614296 1558835 := bstep (se 1 (by rfl) ⟨1169126, by rfl⟩ : syracuseStep 1558835 = 2338253) B2338253
theorem B2083265 : Blo 614296 2083265 := bstep (se 2 (by rfl) ⟨781224, by rfl⟩ : syracuseStep 2083265 = 1562449) B1562449
theorem B3754457 : Blo 614296 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B4999715 : Blo 614296 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B2640529 : Blo 614296 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B3164993 : Blo 614296 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B1559371 : Blo 614296 1559371 := bstep (se 1 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 1559371 = 2339057) B2339057
theorem B1166233 : Blo 614296 1166233 := bstep (se 2 (by rfl) ⟨437337, by rfl⟩ : syracuseStep 1166233 = 874675) B874675
theorem B1559513 : Blo 614296 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B2083805 : Blo 614296 2083805 := bstep (se 3 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 2083805 = 781427) B781427
theorem B2346029 : Blo 614296 2346029 := bstep (se 3 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 2346029 = 879761) B879761
theorem B1166795 : Blo 614296 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B2674241 : Blo 614296 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B1166977 : Blo 614296 1166977 := bstep (se 2 (by rfl) ⟨437616, by rfl⟩ : syracuseStep 1166977 = 875233) B875233
theorem B6016643 : Blo 614296 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B6672077 : Blo 614296 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B1560343 : Blo 614296 1560343 := bstep (se 1 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 1560343 = 2340515) B2340515
theorem B2346803 : Blo 614296 2346803 := bstep (se 1 (by rfl) ⟨1760102, by rfl⟩ : syracuseStep 2346803 = 3520205) B3520205
theorem B741323 : Blo 614296 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B2084939 : Blo 614296 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B1757335 : Blo 614296 1757335 := bstep (se 1 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 1757335 = 2636003) B2636003
theorem B1560779 : Blo 614296 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B1167691 : Blo 614296 1167691 := bstep (se 1 (by rfl) ⟨875768, by rfl⟩ : syracuseStep 1167691 = 1751537) B1751537
theorem B1036631 : Blo 614296 1036631 := bstep (se 1 (by rfl) ⟨777473, by rfl⟩ : syracuseStep 1036631 = 1554947) B1554947
theorem B2085209 : Blo 614296 2085209 := bstep (se 2 (by rfl) ⟨781953, by rfl⟩ : syracuseStep 2085209 = 1563907) B1563907
theorem B1167767 : Blo 614296 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B1036759 : Blo 614296 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B1561153 : Blo 614296 1561153 := bstep (se 2 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 1561153 = 1170865) B1170865
theorem B5263973 : Blo 614296 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B2708147 : Blo 614296 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B14471885 : Blo 614296 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B2085911 : Blo 614296 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B1168435 : Blo 614296 1168435 := bstep (se 1 (by rfl) ⟨876326, by rfl⟩ : syracuseStep 1168435 = 1752653) B1752653
theorem B1037387 : Blo 614296 1037387 := bstep (se 1 (by rfl) ⟨778040, by rfl⟩ : syracuseStep 1037387 = 1556081) B1556081
theorem B1561751 : Blo 614296 1561751 := bstep (se 1 (by rfl) ⟨1171313, by rfl⟩ : syracuseStep 1561751 = 2342627) B2342627
theorem B1037515 : Blo 614296 1037515 := bstep (se 1 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 1037515 = 1556273) B1556273
theorem B5002501 : Blo 614296 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B4674833 : Blo 614296 4674833 := bstep (se 2 (by rfl) ⟨1753062, by rfl⟩ : syracuseStep 4674833 = 3506125) B3506125
theorem B1168663 : Blo 614296 1168663 := bstep (se 1 (by rfl) ⟨876497, by rfl⟩ : syracuseStep 1168663 = 1752995) B1752995
theorem B1037657 : Blo 614296 1037657 := bstep (se 2 (by rfl) ⟨389121, by rfl⟩ : syracuseStep 1037657 = 778243) B778243
theorem B1168769 : Blo 614296 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B1758667 : Blo 614296 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1037785 : Blo 614296 1037785 := bstep (se 2 (by rfl) ⟨389169, by rfl⟩ : syracuseStep 1037785 = 778339) B778339
theorem B1168921 : Blo 614296 1168921 := bstep (se 2 (by rfl) ⟨438345, by rfl⟩ : syracuseStep 1168921 = 876691) B876691
theorem B2086451 : Blo 614296 2086451 := bstep (se 1 (by rfl) ⟨1564838, by rfl⟩ : syracuseStep 2086451 = 3129677) B3129677
theorem B1758941 : Blo 614296 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B2086721 : Blo 614296 2086721 := bstep (se 2 (by rfl) ⟨782520, by rfl⟩ : syracuseStep 2086721 = 1565041) B1565041
theorem B2840465 : Blo 614296 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1496983 : Blo 614296 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B1562561 : Blo 614296 1562561 := bstep (se 2 (by rfl) ⟨585960, by rfl⟩ : syracuseStep 1562561 = 1171921) B1171921
theorem B1038359 : Blo 614296 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B1759283 : Blo 614296 1759283 := bstep (se 1 (by rfl) ⟨1319462, by rfl⟩ : syracuseStep 1759283 = 2638925) B2638925
theorem B1038487 : Blo 614296 1038487 := bstep (se 1 (by rfl) ⟨778865, by rfl⟩ : syracuseStep 1038487 = 1557731) B1557731
theorem B4446413 : Blo 614296 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B874891 : Blo 614296 874891 := bstep (se 1 (by rfl) ⟨656168, by rfl⟩ : syracuseStep 874891 = 1312337) B1312337
theorem B874903 : Blo 614296 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B5921201 : Blo 614296 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B1563097 : Blo 614296 1563097 := bstep (se 2 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 1563097 = 1172323) B1172323
theorem B1039115 : Blo 614296 1039115 := bstep (se 1 (by rfl) ⟨779336, by rfl⟩ : syracuseStep 1039115 = 1558673) B1558673
theorem B1170227 : Blo 614296 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1039243 : Blo 614296 1039243 := bstep (se 1 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 1039243 = 1558865) B1558865
theorem B1170379 : Blo 614296 1170379 := bstep (se 1 (by rfl) ⟨877784, by rfl⟩ : syracuseStep 1170379 = 1755569) B1755569
theorem B1039385 : Blo 614296 1039385 := bstep (se 2 (by rfl) ⟨389769, by rfl⟩ : syracuseStep 1039385 = 779539) B779539
theorem B3333271 : Blo 614296 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B1039513 : Blo 614296 1039513 := bstep (se 2 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 1039513 = 779635) B779635
theorem B1170713 : Blo 614296 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B1564211 : Blo 614296 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B3333707 : Blo 614296 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B3595877 : Blo 614296 3595877 := bstep (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) B674227
theorem B1040087 : Blo 614296 1040087 := bstep (se 1 (by rfl) ⟨780065, by rfl⟩ : syracuseStep 1040087 = 1560131) B1560131
theorem B1040215 : Blo 614296 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B1564505 : Blo 614296 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B1171351 : Blo 614296 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B614315 : Blo 614296 614315 := bstep (se 1 (by rfl) ⟨460736, by rfl⟩ : syracuseStep 614315 = 921473) B921473
theorem B614327 : Blo 614296 614327 := bstep (se 1 (by rfl) ⟨460745, by rfl⟩ : syracuseStep 614327 = 921491) B921491
theorem B614347 : Blo 614296 614347 := bstep (se 1 (by rfl) ⟨460760, by rfl⟩ : syracuseStep 614347 = 921521) B921521
theorem B778187 : Blo 614296 778187 := bstep (se 1 (by rfl) ⟨583640, by rfl⟩ : syracuseStep 778187 = 1167281) B1167281
theorem B614359 : Blo 614296 614359 := bstep (se 1 (by rfl) ⟨460769, by rfl⟩ : syracuseStep 614359 = 921539) B921539
theorem B614379 : Blo 614296 614379 := bstep (se 1 (by rfl) ⟨460784, by rfl⟩ : syracuseStep 614379 = 921569) B921569
theorem B614391 : Blo 614296 614391 := bstep (se 1 (by rfl) ⟨460793, by rfl⟩ : syracuseStep 614391 = 921587) B921587
theorem B614411 : Blo 614296 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B614423 : Blo 614296 614423 := bstep (se 1 (by rfl) ⟨460817, by rfl⟩ : syracuseStep 614423 = 921635) B921635
theorem B614443 : Blo 614296 614443 := bstep (se 1 (by rfl) ⟨460832, by rfl⟩ : syracuseStep 614443 = 921665) B921665
theorem B614455 : Blo 614296 614455 := bstep (se 1 (by rfl) ⟨460841, by rfl⟩ : syracuseStep 614455 = 921683) B921683
theorem B614475 : Blo 614296 614475 := bstep (se 1 (by rfl) ⟨460856, by rfl⟩ : syracuseStep 614475 = 921713) B921713
theorem B614487 : Blo 614296 614487 := bstep (se 1 (by rfl) ⟨460865, by rfl⟩ : syracuseStep 614487 = 921731) B921731
theorem B614507 : Blo 614296 614507 := bstep (se 1 (by rfl) ⟨460880, by rfl⟩ : syracuseStep 614507 = 921761) B921761
theorem B614519 : Blo 614296 614519 := bstep (se 1 (by rfl) ⟨460889, by rfl⟩ : syracuseStep 614519 = 921779) B921779
theorem B614539 : Blo 614296 614539 := bstep (se 1 (by rfl) ⟨460904, by rfl⟩ : syracuseStep 614539 = 921809) B921809
theorem B614551 : Blo 614296 614551 := bstep (se 1 (by rfl) ⟨460913, by rfl⟩ : syracuseStep 614551 = 921827) B921827
theorem B8446103 : Blo 614296 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B614571 : Blo 614296 614571 := bstep (se 1 (by rfl) ⟨460928, by rfl⟩ : syracuseStep 614571 = 921857) B921857
theorem B614583 : Blo 614296 614583 := bstep (se 1 (by rfl) ⟨460937, by rfl⟩ : syracuseStep 614583 = 921875) B921875
theorem B614603 : Blo 614296 614603 := bstep (se 1 (by rfl) ⟨460952, by rfl⟩ : syracuseStep 614603 = 921905) B921905
theorem B614615 : Blo 614296 614615 := bstep (se 1 (by rfl) ⟨460961, by rfl⟩ : syracuseStep 614615 = 921923) B921923
theorem B614635 : Blo 614296 614635 := bstep (se 1 (by rfl) ⟨460976, by rfl⟩ : syracuseStep 614635 = 921953) B921953
theorem B614647 : Blo 614296 614647 := bstep (se 1 (by rfl) ⟨460985, by rfl⟩ : syracuseStep 614647 = 921971) B921971
theorem B614667 : Blo 614296 614667 := bstep (se 1 (by rfl) ⟨461000, by rfl⟩ : syracuseStep 614667 = 922001) B922001
theorem B614679 : Blo 614296 614679 := bstep (se 1 (by rfl) ⟨461009, by rfl⟩ : syracuseStep 614679 = 922019) B922019
theorem B614699 : Blo 614296 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B614711 : Blo 614296 614711 := bstep (se 1 (by rfl) ⟨461033, by rfl⟩ : syracuseStep 614711 = 922067) B922067
theorem B614731 : Blo 614296 614731 := bstep (se 1 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 614731 = 922097) B922097
theorem B614743 : Blo 614296 614743 := bstep (se 1 (by rfl) ⟨461057, by rfl⟩ : syracuseStep 614743 = 922115) B922115
theorem B614763 : Blo 614296 614763 := bstep (se 1 (by rfl) ⟨461072, by rfl⟩ : syracuseStep 614763 = 922145) B922145
theorem B614775 : Blo 614296 614775 := bstep (se 1 (by rfl) ⟨461081, by rfl⟩ : syracuseStep 614775 = 922163) B922163
theorem B614795 : Blo 614296 614795 := bstep (se 1 (by rfl) ⟨461096, by rfl⟩ : syracuseStep 614795 = 922193) B922193
theorem B614807 : Blo 614296 614807 := bstep (se 1 (by rfl) ⟨461105, by rfl⟩ : syracuseStep 614807 = 922211) B922211
theorem B876953 : Blo 614296 876953 := bstep (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) B657715
theorem B614827 : Blo 614296 614827 := bstep (se 1 (by rfl) ⟨461120, by rfl⟩ : syracuseStep 614827 = 922241) B922241
theorem B614839 : Blo 614296 614839 := bstep (se 1 (by rfl) ⟨461129, by rfl⟩ : syracuseStep 614839 = 922259) B922259
theorem B614859 : Blo 614296 614859 := bstep (se 1 (by rfl) ⟨461144, by rfl⟩ : syracuseStep 614859 = 922289) B922289
theorem B1040843 : Blo 614296 1040843 := bstep (se 1 (by rfl) ⟨780632, by rfl⟩ : syracuseStep 1040843 = 1561265) B1561265
theorem B614871 : Blo 614296 614871 := bstep (se 1 (by rfl) ⟨461153, by rfl⟩ : syracuseStep 614871 = 922307) B922307
theorem B614891 : Blo 614296 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B614903 : Blo 614296 614903 := bstep (se 1 (by rfl) ⟨461177, by rfl⟩ : syracuseStep 614903 = 922355) B922355
theorem B614923 : Blo 614296 614923 := bstep (se 1 (by rfl) ⟨461192, by rfl⟩ : syracuseStep 614923 = 922385) B922385
theorem B614935 : Blo 614296 614935 := bstep (se 1 (by rfl) ⟨461201, by rfl⟩ : syracuseStep 614935 = 922403) B922403
theorem B4448803 : Blo 614296 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B614955 : Blo 614296 614955 := bstep (se 1 (by rfl) ⟨461216, by rfl⟩ : syracuseStep 614955 = 922433) B922433
theorem B614967 : Blo 614296 614967 := bstep (se 1 (by rfl) ⟨461225, by rfl⟩ : syracuseStep 614967 = 922451) B922451
theorem B614987 : Blo 614296 614987 := bstep (se 1 (by rfl) ⟨461240, by rfl⟩ : syracuseStep 614987 = 922481) B922481
theorem B8872523 : Blo 614296 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B1040971 : Blo 614296 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B614999 : Blo 614296 614999 := bstep (se 1 (by rfl) ⟨461249, by rfl⟩ : syracuseStep 614999 = 922499) B922499
theorem B615019 : Blo 614296 615019 := bstep (se 1 (by rfl) ⟨461264, by rfl⟩ : syracuseStep 615019 = 922529) B922529
theorem B615031 : Blo 614296 615031 := bstep (se 1 (by rfl) ⟨461273, by rfl⟩ : syracuseStep 615031 = 922547) B922547
theorem B615051 : Blo 614296 615051 := bstep (se 1 (by rfl) ⟨461288, by rfl⟩ : syracuseStep 615051 = 922577) B922577
theorem B778891 : Blo 614296 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B615063 : Blo 614296 615063 := bstep (se 1 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 615063 = 922595) B922595
theorem B615083 : Blo 614296 615083 := bstep (se 1 (by rfl) ⟨461312, by rfl⟩ : syracuseStep 615083 = 922625) B922625
theorem B615095 : Blo 614296 615095 := bstep (se 1 (by rfl) ⟨461321, by rfl⟩ : syracuseStep 615095 = 922643) B922643
theorem B615115 : Blo 614296 615115 := bstep (se 1 (by rfl) ⟨461336, by rfl⟩ : syracuseStep 615115 = 922673) B922673
theorem B1172171 : Blo 614296 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B615127 : Blo 614296 615127 := bstep (se 1 (by rfl) ⟨461345, by rfl⟩ : syracuseStep 615127 = 922691) B922691
theorem B1041113 : Blo 614296 1041113 := bstep (se 2 (by rfl) ⟨390417, by rfl⟩ : syracuseStep 1041113 = 780835) B780835
theorem B615147 : Blo 614296 615147 := bstep (se 1 (by rfl) ⟨461360, by rfl⟩ : syracuseStep 615147 = 922721) B922721
theorem B615159 : Blo 614296 615159 := bstep (se 1 (by rfl) ⟨461369, by rfl⟩ : syracuseStep 615159 = 922739) B922739
theorem B1172225 : Blo 614296 1172225 := bstep (se 2 (by rfl) ⟨439584, by rfl⟩ : syracuseStep 1172225 = 879169) B879169
theorem B615179 : Blo 614296 615179 := bstep (se 1 (by rfl) ⟨461384, by rfl⟩ : syracuseStep 615179 = 922769) B922769
theorem B615191 : Blo 614296 615191 := bstep (se 1 (by rfl) ⟨461393, by rfl⟩ : syracuseStep 615191 = 922787) B922787
theorem B615211 : Blo 614296 615211 := bstep (se 1 (by rfl) ⟨461408, by rfl⟩ : syracuseStep 615211 = 922817) B922817
theorem B615223 : Blo 614296 615223 := bstep (se 1 (by rfl) ⟨461417, by rfl⟩ : syracuseStep 615223 = 922835) B922835
theorem B615243 : Blo 614296 615243 := bstep (se 1 (by rfl) ⟨461432, by rfl⟩ : syracuseStep 615243 = 922865) B922865
theorem B615255 : Blo 614296 615255 := bstep (se 1 (by rfl) ⟨461441, by rfl⟩ : syracuseStep 615255 = 922883) B922883
theorem B1041241 : Blo 614296 1041241 := bstep (se 2 (by rfl) ⟨390465, by rfl⟩ : syracuseStep 1041241 = 780931) B780931
theorem B615275 : Blo 614296 615275 := bstep (se 1 (by rfl) ⟨461456, by rfl⟩ : syracuseStep 615275 = 922913) B922913
theorem B615287 : Blo 614296 615287 := bstep (se 1 (by rfl) ⟨461465, by rfl⟩ : syracuseStep 615287 = 922931) B922931
theorem B615307 : Blo 614296 615307 := bstep (se 1 (by rfl) ⟨461480, by rfl⟩ : syracuseStep 615307 = 922961) B922961
theorem B615319 : Blo 614296 615319 := bstep (se 1 (by rfl) ⟨461489, by rfl⟩ : syracuseStep 615319 = 922979) B922979
theorem B779159 : Blo 614296 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B615339 : Blo 614296 615339 := bstep (se 1 (by rfl) ⟨461504, by rfl⟩ : syracuseStep 615339 = 923009) B923009
theorem B15000497 : Blo 614296 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B615351 : Blo 614296 615351 := bstep (se 1 (by rfl) ⟨461513, by rfl⟩ : syracuseStep 615351 = 923027) B923027
theorem B615371 : Blo 614296 615371 := bstep (se 1 (by rfl) ⟨461528, by rfl⟩ : syracuseStep 615371 = 923057) B923057
theorem B615383 : Blo 614296 615383 := bstep (se 1 (by rfl) ⟨461537, by rfl⟩ : syracuseStep 615383 = 923075) B923075
theorem B615403 : Blo 614296 615403 := bstep (se 1 (by rfl) ⟨461552, by rfl⟩ : syracuseStep 615403 = 923105) B923105
theorem B615415 : Blo 614296 615415 := bstep (se 1 (by rfl) ⟨461561, by rfl⟩ : syracuseStep 615415 = 923123) B923123
theorem B615435 : Blo 614296 615435 := bstep (se 1 (by rfl) ⟨461576, by rfl⟩ : syracuseStep 615435 = 923153) B923153
theorem B615447 : Blo 614296 615447 := bstep (se 1 (by rfl) ⟨461585, by rfl⟩ : syracuseStep 615447 = 923171) B923171
theorem B877591 : Blo 614296 877591 := bstep (se 1 (by rfl) ⟨658193, by rfl⟩ : syracuseStep 877591 = 1316387) B1316387
theorem B615467 : Blo 614296 615467 := bstep (se 1 (by rfl) ⟨461600, by rfl⟩ : syracuseStep 615467 = 923201) B923201
theorem B615479 : Blo 614296 615479 := bstep (se 1 (by rfl) ⟨461609, by rfl⟩ : syracuseStep 615479 = 923219) B923219
theorem B4678721 : Blo 614296 4678721 := bstep (se 2 (by rfl) ⟨1754520, by rfl⟩ : syracuseStep 4678721 = 3509041) B3509041
theorem B615499 : Blo 614296 615499 := bstep (se 1 (by rfl) ⟨461624, by rfl⟩ : syracuseStep 615499 = 923249) B923249
theorem B615511 : Blo 614296 615511 := bstep (se 1 (by rfl) ⟨461633, by rfl⟩ : syracuseStep 615511 = 923267) B923267
theorem B3499109 : Blo 614296 3499109 := bstep (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) B656083
theorem B615531 : Blo 614296 615531 := bstep (se 1 (by rfl) ⟨461648, by rfl⟩ : syracuseStep 615531 = 923297) B923297
theorem B615543 : Blo 614296 615543 := bstep (se 1 (by rfl) ⟨461657, by rfl⟩ : syracuseStep 615543 = 923315) B923315
theorem B615563 : Blo 614296 615563 := bstep (se 1 (by rfl) ⟨461672, by rfl⟩ : syracuseStep 615563 = 923345) B923345
theorem B615575 : Blo 614296 615575 := bstep (se 1 (by rfl) ⟨461681, by rfl⟩ : syracuseStep 615575 = 923363) B923363
theorem B615595 : Blo 614296 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B615607 : Blo 614296 615607 := bstep (se 1 (by rfl) ⟨461705, by rfl⟩ : syracuseStep 615607 = 923411) B923411
theorem B615627 : Blo 614296 615627 := bstep (se 1 (by rfl) ⟨461720, by rfl⟩ : syracuseStep 615627 = 923441) B923441
theorem B615639 : Blo 614296 615639 := bstep (se 1 (by rfl) ⟨461729, by rfl⟩ : syracuseStep 615639 = 923459) B923459
theorem B2712793 : Blo 614296 2712793 := bstep (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) B2034595
theorem B615659 : Blo 614296 615659 := bstep (se 1 (by rfl) ⟨461744, by rfl⟩ : syracuseStep 615659 = 923489) B923489
theorem B615671 : Blo 614296 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B615691 : Blo 614296 615691 := bstep (se 1 (by rfl) ⟨461768, by rfl⟩ : syracuseStep 615691 = 923537) B923537
theorem B615703 : Blo 614296 615703 := bstep (se 1 (by rfl) ⟨461777, by rfl⟩ : syracuseStep 615703 = 923555) B923555
theorem B615723 : Blo 614296 615723 := bstep (se 1 (by rfl) ⟨461792, by rfl⟩ : syracuseStep 615723 = 923585) B923585
theorem B615735 : Blo 614296 615735 := bstep (se 1 (by rfl) ⟨461801, by rfl⟩ : syracuseStep 615735 = 923603) B923603
theorem B615755 : Blo 614296 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B615767 : Blo 614296 615767 := bstep (se 1 (by rfl) ⟨461825, by rfl⟩ : syracuseStep 615767 = 923651) B923651
theorem B615787 : Blo 614296 615787 := bstep (se 1 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 615787 = 923681) B923681
theorem B615799 : Blo 614296 615799 := bstep (se 1 (by rfl) ⟨461849, by rfl⟩ : syracuseStep 615799 = 923699) B923699
theorem B615819 : Blo 614296 615819 := bstep (se 1 (by rfl) ⟨461864, by rfl⟩ : syracuseStep 615819 = 923729) B923729
theorem B615831 : Blo 614296 615831 := bstep (se 1 (by rfl) ⟨461873, by rfl⟩ : syracuseStep 615831 = 923747) B923747
theorem B1041815 : Blo 614296 1041815 := bstep (se 1 (by rfl) ⟨781361, by rfl⟩ : syracuseStep 1041815 = 1562723) B1562723
theorem B615851 : Blo 614296 615851 := bstep (se 1 (by rfl) ⟨461888, by rfl⟩ : syracuseStep 615851 = 923777) B923777
theorem B615863 : Blo 614296 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B615883 : Blo 614296 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B1500619 : Blo 614296 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B615895 : Blo 614296 615895 := bstep (se 1 (by rfl) ⟨461921, by rfl⟩ : syracuseStep 615895 = 923843) B923843
theorem B615915 : Blo 614296 615915 := bstep (se 1 (by rfl) ⟨461936, by rfl⟩ : syracuseStep 615915 = 923873) B923873
theorem B615927 : Blo 614296 615927 := bstep (se 1 (by rfl) ⟨461945, by rfl⟩ : syracuseStep 615927 = 923891) B923891
theorem B615947 : Blo 614296 615947 := bstep (se 1 (by rfl) ⟨461960, by rfl⟩ : syracuseStep 615947 = 923921) B923921
theorem B615959 : Blo 614296 615959 := bstep (se 1 (by rfl) ⟨461969, by rfl⟩ : syracuseStep 615959 = 923939) B923939
theorem B1041943 : Blo 614296 1041943 := bstep (se 1 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 1041943 = 1562915) B1562915
theorem B615979 : Blo 614296 615979 := bstep (se 1 (by rfl) ⟨461984, by rfl⟩ : syracuseStep 615979 = 923969) B923969
theorem B615991 : Blo 614296 615991 := bstep (se 1 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 615991 = 923987) B923987
theorem B616011 : Blo 614296 616011 := bstep (se 1 (by rfl) ⟨462008, by rfl⟩ : syracuseStep 616011 = 924017) B924017
theorem B616023 : Blo 614296 616023 := bstep (se 1 (by rfl) ⟨462017, by rfl⟩ : syracuseStep 616023 = 924035) B924035
theorem B779863 : Blo 614296 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B616043 : Blo 614296 616043 := bstep (se 1 (by rfl) ⟨462032, by rfl⟩ : syracuseStep 616043 = 924065) B924065
theorem B616055 : Blo 614296 616055 := bstep (se 1 (by rfl) ⟨462041, by rfl⟩ : syracuseStep 616055 = 924083) B924083
theorem B616075 : Blo 614296 616075 := bstep (se 1 (by rfl) ⟨462056, by rfl⟩ : syracuseStep 616075 = 924113) B924113
theorem B616087 : Blo 614296 616087 := bstep (se 1 (by rfl) ⟨462065, by rfl⟩ : syracuseStep 616087 = 924131) B924131
theorem B1173143 : Blo 614296 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B616107 : Blo 614296 616107 := bstep (se 1 (by rfl) ⟨462080, by rfl⟩ : syracuseStep 616107 = 924161) B924161
theorem B616119 : Blo 614296 616119 := bstep (se 1 (by rfl) ⟨462089, by rfl⟩ : syracuseStep 616119 = 924179) B924179
theorem B616139 : Blo 614296 616139 := bstep (se 1 (by rfl) ⟨462104, by rfl⟩ : syracuseStep 616139 = 924209) B924209
theorem B616151 : Blo 614296 616151 := bstep (se 1 (by rfl) ⟨462113, by rfl⟩ : syracuseStep 616151 = 924227) B924227
theorem B616171 : Blo 614296 616171 := bstep (se 1 (by rfl) ⟨462128, by rfl⟩ : syracuseStep 616171 = 924257) B924257
theorem B616183 : Blo 614296 616183 := bstep (se 1 (by rfl) ⟨462137, by rfl⟩ : syracuseStep 616183 = 924275) B924275
theorem B616203 : Blo 614296 616203 := bstep (se 1 (by rfl) ⟨462152, by rfl⟩ : syracuseStep 616203 = 924305) B924305
theorem B3499793 : Blo 614296 3499793 := bstep (se 2 (by rfl) ⟨1312422, by rfl⟩ : syracuseStep 3499793 = 2624845) B2624845
theorem B616215 : Blo 614296 616215 := bstep (se 1 (by rfl) ⟨462161, by rfl⟩ : syracuseStep 616215 = 924323) B924323
theorem B616235 : Blo 614296 616235 := bstep (se 1 (by rfl) ⟨462176, by rfl⟩ : syracuseStep 616235 = 924353) B924353
theorem B616247 : Blo 614296 616247 := bstep (se 1 (by rfl) ⟨462185, by rfl⟩ : syracuseStep 616247 = 924371) B924371
theorem B616267 : Blo 614296 616267 := bstep (se 1 (by rfl) ⟨462200, by rfl⟩ : syracuseStep 616267 = 924401) B924401
theorem B878411 : Blo 614296 878411 := bstep (se 1 (by rfl) ⟨658808, by rfl⟩ : syracuseStep 878411 = 1317617) B1317617
theorem B616279 : Blo 614296 616279 := bstep (se 1 (by rfl) ⟨462209, by rfl⟩ : syracuseStep 616279 = 924419) B924419
theorem B616299 : Blo 614296 616299 := bstep (se 1 (by rfl) ⟨462224, by rfl⟩ : syracuseStep 616299 = 924449) B924449
theorem B616311 : Blo 614296 616311 := bstep (se 1 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 616311 = 924467) B924467
theorem B616331 : Blo 614296 616331 := bstep (se 1 (by rfl) ⟨462248, by rfl⟩ : syracuseStep 616331 = 924497) B924497
theorem B616343 : Blo 614296 616343 := bstep (se 1 (by rfl) ⟨462257, by rfl⟩ : syracuseStep 616343 = 924515) B924515
theorem B616363 : Blo 614296 616363 := bstep (se 1 (by rfl) ⟨462272, by rfl⟩ : syracuseStep 616363 = 924545) B924545
theorem B12642227 : Blo 614296 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B616375 : Blo 614296 616375 := bstep (se 1 (by rfl) ⟨462281, by rfl⟩ : syracuseStep 616375 = 924563) B924563
theorem B616395 : Blo 614296 616395 := bstep (se 1 (by rfl) ⟨462296, by rfl⟩ : syracuseStep 616395 = 924593) B924593
theorem B616407 : Blo 614296 616407 := bstep (se 1 (by rfl) ⟨462305, by rfl⟩ : syracuseStep 616407 = 924611) B924611
theorem B616427 : Blo 614296 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B1402867 : Blo 614296 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B616439 : Blo 614296 616439 := bstep (se 1 (by rfl) ⟨462329, by rfl⟩ : syracuseStep 616439 = 924659) B924659
theorem B616459 : Blo 614296 616459 := bstep (se 1 (by rfl) ⟨462344, by rfl⟩ : syracuseStep 616459 = 924689) B924689
theorem B616471 : Blo 614296 616471 := bstep (se 1 (by rfl) ⟨462353, by rfl⟩ : syracuseStep 616471 = 924707) B924707
theorem B616491 : Blo 614296 616491 := bstep (se 1 (by rfl) ⟨462368, by rfl⟩ : syracuseStep 616491 = 924737) B924737
theorem B616503 : Blo 614296 616503 := bstep (se 1 (by rfl) ⟨462377, by rfl⟩ : syracuseStep 616503 = 924755) B924755
theorem B54716485 : Blo 614296 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B616523 : Blo 614296 616523 := bstep (se 1 (by rfl) ⟨462392, by rfl⟩ : syracuseStep 616523 = 924785) B924785
theorem B616535 : Blo 614296 616535 := bstep (se 1 (by rfl) ⟨462401, by rfl⟩ : syracuseStep 616535 = 924803) B924803
theorem B616555 : Blo 614296 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B616567 : Blo 614296 616567 := bstep (se 1 (by rfl) ⟨462425, by rfl⟩ : syracuseStep 616567 = 924851) B924851
theorem B616587 : Blo 614296 616587 := bstep (se 1 (by rfl) ⟨462440, by rfl⟩ : syracuseStep 616587 = 924881) B924881
theorem B1042571 : Blo 614296 1042571 := bstep (se 1 (by rfl) ⟨781928, by rfl⟩ : syracuseStep 1042571 = 1563857) B1563857
theorem B616599 : Blo 614296 616599 := bstep (se 1 (by rfl) ⟨462449, by rfl⟩ : syracuseStep 616599 = 924899) B924899
theorem B616619 : Blo 614296 616619 := bstep (se 1 (by rfl) ⟨462464, by rfl⟩ : syracuseStep 616619 = 924929) B924929
theorem B1173683 : Blo 614296 1173683 := bstep (se 1 (by rfl) ⟨880262, by rfl⟩ : syracuseStep 1173683 = 1760525) B1760525
theorem B616631 : Blo 614296 616631 := bstep (se 1 (by rfl) ⟨462473, by rfl⟩ : syracuseStep 616631 = 924947) B924947
theorem B616651 : Blo 614296 616651 := bstep (se 1 (by rfl) ⟨462488, by rfl⟩ : syracuseStep 616651 = 924977) B924977
theorem B616663 : Blo 614296 616663 := bstep (se 1 (by rfl) ⟨462497, by rfl⟩ : syracuseStep 616663 = 924995) B924995
theorem B616683 : Blo 614296 616683 := bstep (se 1 (by rfl) ⟨462512, by rfl⟩ : syracuseStep 616683 = 925025) B925025
theorem B616695 : Blo 614296 616695 := bstep (se 1 (by rfl) ⟨462521, by rfl⟩ : syracuseStep 616695 = 925043) B925043
theorem B616715 : Blo 614296 616715 := bstep (se 1 (by rfl) ⟨462536, by rfl⟩ : syracuseStep 616715 = 925073) B925073
theorem B1042699 : Blo 614296 1042699 := bstep (se 1 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 1042699 = 1564049) B1564049
theorem B616727 : Blo 614296 616727 := bstep (se 1 (by rfl) ⟨462545, by rfl⟩ : syracuseStep 616727 = 925091) B925091
theorem B616747 : Blo 614296 616747 := bstep (se 1 (by rfl) ⟨462560, by rfl⟩ : syracuseStep 616747 = 925121) B925121
theorem B616759 : Blo 614296 616759 := bstep (se 1 (by rfl) ⟨462569, by rfl⟩ : syracuseStep 616759 = 925139) B925139
theorem B616779 : Blo 614296 616779 := bstep (se 1 (by rfl) ⟨462584, by rfl⟩ : syracuseStep 616779 = 925169) B925169
theorem B616791 : Blo 614296 616791 := bstep (se 1 (by rfl) ⟨462593, by rfl⟩ : syracuseStep 616791 = 925187) B925187
theorem B616811 : Blo 614296 616811 := bstep (se 1 (by rfl) ⟨462608, by rfl⟩ : syracuseStep 616811 = 925217) B925217
theorem B616823 : Blo 614296 616823 := bstep (se 1 (by rfl) ⟨462617, by rfl⟩ : syracuseStep 616823 = 925235) B925235
theorem B616843 : Blo 614296 616843 := bstep (se 1 (by rfl) ⟨462632, by rfl⟩ : syracuseStep 616843 = 925265) B925265
theorem B616855 : Blo 614296 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B1042841 : Blo 614296 1042841 := bstep (se 2 (by rfl) ⟨391065, by rfl⟩ : syracuseStep 1042841 = 782131) B782131
theorem B616875 : Blo 614296 616875 := bstep (se 1 (by rfl) ⟨462656, by rfl⟩ : syracuseStep 616875 = 925313) B925313
theorem B616887 : Blo 614296 616887 := bstep (se 1 (by rfl) ⟨462665, by rfl⟩ : syracuseStep 616887 = 925331) B925331
theorem B616907 : Blo 614296 616907 := bstep (se 1 (by rfl) ⟨462680, by rfl⟩ : syracuseStep 616907 = 925361) B925361
theorem B616919 : Blo 614296 616919 := bstep (se 1 (by rfl) ⟨462689, by rfl⟩ : syracuseStep 616919 = 925379) B925379
theorem B616939 : Blo 614296 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B616951 : Blo 614296 616951 := bstep (se 1 (by rfl) ⟨462713, by rfl⟩ : syracuseStep 616951 = 925427) B925427
theorem B616971 : Blo 614296 616971 := bstep (se 1 (by rfl) ⟨462728, by rfl⟩ : syracuseStep 616971 = 925457) B925457
theorem B616983 : Blo 614296 616983 := bstep (se 1 (by rfl) ⟨462737, by rfl⟩ : syracuseStep 616983 = 925475) B925475
theorem B1042969 : Blo 614296 1042969 := bstep (se 2 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 1042969 = 782227) B782227
theorem B617003 : Blo 614296 617003 := bstep (se 1 (by rfl) ⟨462752, by rfl⟩ : syracuseStep 617003 = 925505) B925505
theorem B617015 : Blo 614296 617015 := bstep (se 1 (by rfl) ⟨462761, by rfl⟩ : syracuseStep 617015 = 925523) B925523
theorem B617035 : Blo 614296 617035 := bstep (se 1 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 617035 = 925553) B925553
theorem B617047 : Blo 614296 617047 := bstep (se 1 (by rfl) ⟨462785, by rfl⟩ : syracuseStep 617047 = 925571) B925571
theorem B3992165 : Blo 614296 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B617067 : Blo 614296 617067 := bstep (se 1 (by rfl) ⟨462800, by rfl⟩ : syracuseStep 617067 = 925601) B925601
theorem B617079 : Blo 614296 617079 := bstep (se 1 (by rfl) ⟨462809, by rfl⟩ : syracuseStep 617079 = 925619) B925619
theorem B617099 : Blo 614296 617099 := bstep (se 1 (by rfl) ⟨462824, by rfl⟩ : syracuseStep 617099 = 925649) B925649
theorem B617111 : Blo 614296 617111 := bstep (se 1 (by rfl) ⟨462833, by rfl⟩ : syracuseStep 617111 = 925667) B925667
theorem B617131 : Blo 614296 617131 := bstep (se 1 (by rfl) ⟨462848, by rfl⟩ : syracuseStep 617131 = 925697) B925697
theorem B617143 : Blo 614296 617143 := bstep (se 1 (by rfl) ⟨462857, by rfl⟩ : syracuseStep 617143 = 925715) B925715
theorem B617163 : Blo 614296 617163 := bstep (se 1 (by rfl) ⟨462872, by rfl⟩ : syracuseStep 617163 = 925745) B925745
theorem B617175 : Blo 614296 617175 := bstep (se 1 (by rfl) ⟨462881, by rfl⟩ : syracuseStep 617175 = 925763) B925763
theorem B617195 : Blo 614296 617195 := bstep (se 1 (by rfl) ⟨462896, by rfl⟩ : syracuseStep 617195 = 925793) B925793
theorem B617207 : Blo 614296 617207 := bstep (se 1 (by rfl) ⟨462905, by rfl⟩ : syracuseStep 617207 = 925811) B925811
theorem B617227 : Blo 614296 617227 := bstep (se 1 (by rfl) ⟨462920, by rfl⟩ : syracuseStep 617227 = 925841) B925841
theorem B617239 : Blo 614296 617239 := bstep (se 1 (by rfl) ⟨462929, by rfl⟩ : syracuseStep 617239 = 925859) B925859
theorem B846617 : Blo 614296 846617 := bstep (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) B634963
theorem B617259 : Blo 614296 617259 := bstep (se 1 (by rfl) ⟨462944, by rfl⟩ : syracuseStep 617259 = 925889) B925889
theorem B617271 : Blo 614296 617271 := bstep (se 1 (by rfl) ⟨462953, by rfl⟩ : syracuseStep 617271 = 925907) B925907
theorem B617291 : Blo 614296 617291 := bstep (se 1 (by rfl) ⟨462968, by rfl⟩ : syracuseStep 617291 = 925937) B925937
theorem B617303 : Blo 614296 617303 := bstep (se 1 (by rfl) ⟨462977, by rfl⟩ : syracuseStep 617303 = 925955) B925955
theorem B617323 : Blo 614296 617323 := bstep (se 1 (by rfl) ⟨462992, by rfl⟩ : syracuseStep 617323 = 925985) B925985
theorem B617335 : Blo 614296 617335 := bstep (se 1 (by rfl) ⟨463001, by rfl⟩ : syracuseStep 617335 = 926003) B926003
theorem B617355 : Blo 614296 617355 := bstep (se 1 (by rfl) ⟨463016, by rfl⟩ : syracuseStep 617355 = 926033) B926033
theorem B617367 : Blo 614296 617367 := bstep (se 1 (by rfl) ⟨463025, by rfl⟩ : syracuseStep 617367 = 926051) B926051
theorem B617387 : Blo 614296 617387 := bstep (se 1 (by rfl) ⟨463040, by rfl⟩ : syracuseStep 617387 = 926081) B926081
theorem B617399 : Blo 614296 617399 := bstep (se 1 (by rfl) ⟨463049, by rfl⟩ : syracuseStep 617399 = 926099) B926099
theorem B617419 : Blo 614296 617419 := bstep (se 1 (by rfl) ⟨463064, by rfl⟩ : syracuseStep 617419 = 926129) B926129
theorem B617431 : Blo 614296 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B4680665 : Blo 614296 4680665 := bstep (se 2 (by rfl) ⟨1755249, by rfl⟩ : syracuseStep 4680665 = 3510499) B3510499
theorem B617451 : Blo 614296 617451 := bstep (se 1 (by rfl) ⟨463088, by rfl⟩ : syracuseStep 617451 = 926177) B926177
theorem B617463 : Blo 614296 617463 := bstep (se 1 (by rfl) ⟨463097, by rfl⟩ : syracuseStep 617463 = 926195) B926195
theorem B617483 : Blo 614296 617483 := bstep (se 1 (by rfl) ⟨463112, by rfl⟩ : syracuseStep 617483 = 926225) B926225
theorem B617495 : Blo 614296 617495 := bstep (se 1 (by rfl) ⟨463121, by rfl⟩ : syracuseStep 617495 = 926243) B926243
theorem B617515 : Blo 614296 617515 := bstep (se 1 (by rfl) ⟨463136, by rfl⟩ : syracuseStep 617515 = 926273) B926273
theorem B617527 : Blo 614296 617527 := bstep (se 1 (by rfl) ⟨463145, by rfl⟩ : syracuseStep 617527 = 926291) B926291
theorem B3959873 : Blo 614296 3959873 := bstep (se 2 (by rfl) ⟨1484952, by rfl⟩ : syracuseStep 3959873 = 2969905) B2969905
theorem B617547 : Blo 614296 617547 := bstep (se 1 (by rfl) ⟨463160, by rfl⟩ : syracuseStep 617547 = 926321) B926321
theorem B617559 : Blo 614296 617559 := bstep (se 1 (by rfl) ⟨463169, by rfl⟩ : syracuseStep 617559 = 926339) B926339
theorem B617579 : Blo 614296 617579 := bstep (se 1 (by rfl) ⟨463184, by rfl⟩ : syracuseStep 617579 = 926369) B926369
theorem B617591 : Blo 614296 617591 := bstep (se 1 (by rfl) ⟨463193, by rfl⟩ : syracuseStep 617591 = 926387) B926387
theorem B617611 : Blo 614296 617611 := bstep (se 1 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 617611 = 926417) B926417
theorem B617623 : Blo 614296 617623 := bstep (se 1 (by rfl) ⟨463217, by rfl⟩ : syracuseStep 617623 = 926435) B926435
theorem B617643 : Blo 614296 617643 := bstep (se 1 (by rfl) ⟨463232, by rfl⟩ : syracuseStep 617643 = 926465) B926465
theorem B617655 : Blo 614296 617655 := bstep (se 1 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 617655 = 926483) B926483
theorem B617675 : Blo 614296 617675 := bstep (se 1 (by rfl) ⟨463256, by rfl⟩ : syracuseStep 617675 = 926513) B926513
theorem B617687 : Blo 614296 617687 := bstep (se 1 (by rfl) ⟨463265, by rfl⟩ : syracuseStep 617687 = 926531) B926531
theorem B617707 : Blo 614296 617707 := bstep (se 1 (by rfl) ⟨463280, by rfl⟩ : syracuseStep 617707 = 926561) B926561
theorem B617719 : Blo 614296 617719 := bstep (se 1 (by rfl) ⟨463289, by rfl⟩ : syracuseStep 617719 = 926579) B926579
theorem B781579 : Blo 614296 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B617739 : Blo 614296 617739 := bstep (se 1 (by rfl) ⟨463304, by rfl⟩ : syracuseStep 617739 = 926609) B926609
theorem B617751 : Blo 614296 617751 := bstep (se 1 (by rfl) ⟨463313, by rfl⟩ : syracuseStep 617751 = 926627) B926627
theorem B617771 : Blo 614296 617771 := bstep (se 1 (by rfl) ⟨463328, by rfl⟩ : syracuseStep 617771 = 926657) B926657
theorem B617783 : Blo 614296 617783 := bstep (se 1 (by rfl) ⟨463337, by rfl⟩ : syracuseStep 617783 = 926675) B926675
theorem B617803 : Blo 614296 617803 := bstep (se 1 (by rfl) ⟨463352, by rfl⟩ : syracuseStep 617803 = 926705) B926705
theorem B617815 : Blo 614296 617815 := bstep (se 1 (by rfl) ⟨463361, by rfl⟩ : syracuseStep 617815 = 926723) B926723
theorem B617835 : Blo 614296 617835 := bstep (se 1 (by rfl) ⟨463376, by rfl⟩ : syracuseStep 617835 = 926753) B926753
theorem B617847 : Blo 614296 617847 := bstep (se 1 (by rfl) ⟨463385, by rfl⟩ : syracuseStep 617847 = 926771) B926771
theorem B617867 : Blo 614296 617867 := bstep (se 1 (by rfl) ⟨463400, by rfl⟩ : syracuseStep 617867 = 926801) B926801
theorem B617879 : Blo 614296 617879 := bstep (se 1 (by rfl) ⟨463409, by rfl⟩ : syracuseStep 617879 = 926819) B926819
theorem B617899 : Blo 614296 617899 := bstep (se 1 (by rfl) ⟨463424, by rfl⟩ : syracuseStep 617899 = 926849) B926849
theorem B2813363 : Blo 614296 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B617911 : Blo 614296 617911 := bstep (se 1 (by rfl) ⟨463433, by rfl⟩ : syracuseStep 617911 = 926867) B926867
theorem B617931 : Blo 614296 617931 := bstep (se 1 (by rfl) ⟨463448, by rfl⟩ : syracuseStep 617931 = 926897) B926897
theorem B617943 : Blo 614296 617943 := bstep (se 1 (by rfl) ⟨463457, by rfl⟩ : syracuseStep 617943 = 926915) B926915
theorem B617963 : Blo 614296 617963 := bstep (se 1 (by rfl) ⟨463472, by rfl⟩ : syracuseStep 617963 = 926945) B926945
theorem B617975 : Blo 614296 617975 := bstep (se 1 (by rfl) ⟨463481, by rfl⟩ : syracuseStep 617975 = 926963) B926963
theorem B617995 : Blo 614296 617995 := bstep (se 1 (by rfl) ⟨463496, by rfl⟩ : syracuseStep 617995 = 926993) B926993
theorem B618007 : Blo 614296 618007 := bstep (se 1 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 618007 = 927011) B927011
theorem B618027 : Blo 614296 618027 := bstep (se 1 (by rfl) ⟨463520, by rfl⟩ : syracuseStep 618027 = 927041) B927041
theorem B618039 : Blo 614296 618039 := bstep (se 1 (by rfl) ⟨463529, by rfl⟩ : syracuseStep 618039 = 927059) B927059
theorem B618059 : Blo 614296 618059 := bstep (se 1 (by rfl) ⟨463544, by rfl⟩ : syracuseStep 618059 = 927089) B927089
theorem B618071 : Blo 614296 618071 := bstep (se 1 (by rfl) ⟨463553, by rfl⟩ : syracuseStep 618071 = 927107) B927107
theorem B618091 : Blo 614296 618091 := bstep (se 1 (by rfl) ⟨463568, by rfl⟩ : syracuseStep 618091 = 927137) B927137
theorem B618103 : Blo 614296 618103 := bstep (se 1 (by rfl) ⟨463577, by rfl⟩ : syracuseStep 618103 = 927155) B927155
theorem B618123 : Blo 614296 618123 := bstep (se 1 (by rfl) ⟨463592, by rfl⟩ : syracuseStep 618123 = 927185) B927185
theorem B618135 : Blo 614296 618135 := bstep (se 1 (by rfl) ⟨463601, by rfl⟩ : syracuseStep 618135 = 927203) B927203
theorem B618155 : Blo 614296 618155 := bstep (se 1 (by rfl) ⟨463616, by rfl⟩ : syracuseStep 618155 = 927233) B927233
theorem B618167 : Blo 614296 618167 := bstep (se 1 (by rfl) ⟨463625, by rfl⟩ : syracuseStep 618167 = 927251) B927251
theorem B618187 : Blo 614296 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B618199 : Blo 614296 618199 := bstep (se 1 (by rfl) ⟨463649, by rfl⟩ : syracuseStep 618199 = 927299) B927299
theorem B618219 : Blo 614296 618219 := bstep (se 1 (by rfl) ⟨463664, by rfl⟩ : syracuseStep 618219 = 927329) B927329
theorem B618231 : Blo 614296 618231 := bstep (se 1 (by rfl) ⟨463673, by rfl⟩ : syracuseStep 618231 = 927347) B927347
theorem B618251 : Blo 614296 618251 := bstep (se 1 (by rfl) ⟨463688, by rfl⟩ : syracuseStep 618251 = 927377) B927377
theorem B618263 : Blo 614296 618263 := bstep (se 1 (by rfl) ⟨463697, by rfl⟩ : syracuseStep 618263 = 927395) B927395
theorem B618283 : Blo 614296 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B618295 : Blo 614296 618295 := bstep (se 1 (by rfl) ⟨463721, by rfl⟩ : syracuseStep 618295 = 927443) B927443
theorem B8876213 : Blo 614296 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B8417753 : Blo 614296 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B4452869 : Blo 614296 4452869 := bstep (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) B834913
theorem B10515095 : Blo 614296 10515095 := bstep (se 1 (by rfl) ⟨7886321, by rfl⟩ : syracuseStep 10515095 = 15772643) B15772643
theorem B3503027 : Blo 614296 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B3339481 : Blo 614296 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B1111321 : Blo 614296 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B3110237 : Blo 614296 3110237 := bstep (se 3 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 3110237 = 1166339) B1166339
theorem B2815661 : Blo 614296 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B1669015 : Blo 614296 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B1112215 : Blo 614296 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B4684067 : Blo 614296 4684067 := bstep (se 1 (by rfl) ⟨3513050, by rfl⟩ : syracuseStep 4684067 = 7026101) B7026101
theorem B2029913 : Blo 614296 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B3504485 : Blo 614296 3504485 := bstep (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) B657091
theorem B5569175 : Blo 614296 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B3373841 : Blo 614296 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B3504941 : Blo 614296 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B18513197 : Blo 614296 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B3112343 : Blo 614296 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B3505625 : Blo 614296 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B1671005 : Blo 614296 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B3342181 : Blo 614296 3342181 := bstep (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) B626659
theorem B1900439 : Blo 614296 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B2817995 : Blo 614296 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B3113153 : Blo 614296 3113153 := bstep (se 2 (by rfl) ⟨1167432, by rfl⟩ : syracuseStep 3113153 = 2334865) B2334865
theorem B1868435 : Blo 614296 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B5931737 : Blo 614296 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B3507401 : Blo 614296 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B3114449 : Blo 614296 3114449 := bstep (se 2 (by rfl) ⟨1167918, by rfl⟩ : syracuseStep 3114449 = 2335837) B2335837
theorem B36537925 : Blo 614296 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B788087 : Blo 614296 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B35915633 : Blo 614296 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B2000825 : Blo 614296 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B7473389 : Blo 614296 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B2492819 : Blo 614296 2492819 := bstep (se 1 (by rfl) ⟨1869614, by rfl⟩ : syracuseStep 2492819 = 3739229) B3739229
theorem B985529 : Blo 614296 985529 := bstep (se 2 (by rfl) ⟨369573, by rfl⟩ : syracuseStep 985529 = 739147) B739147
theorem B1870489 : Blo 614296 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B691087 : Blo 614296 691087 := bstep (se 1 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 691087 = 1036631) B1036631
theorem B13306787 : Blo 614296 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B986041 : Blo 614296 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B3509315 : Blo 614296 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B1805431 : Blo 614296 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B1313977 : Blo 614296 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B691591 : Blo 614296 691591 := bstep (se 1 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 691591 = 1037387) B1037387
theorem B1183177 : Blo 614296 1183177 := bstep (se 2 (by rfl) ⟨443691, by rfl⟩ : syracuseStep 1183177 = 887383) B887383
theorem B3116555 : Blo 614296 3116555 := bstep (se 1 (by rfl) ⟨2337416, by rfl⟩ : syracuseStep 3116555 = 4674833) B4674833
theorem B1314319 : Blo 614296 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B691771 : Blo 614296 691771 := bstep (se 1 (by rfl) ⟨518828, by rfl⟩ : syracuseStep 691771 = 1037657) B1037657
theorem B986759 : Blo 614296 986759 := bstep (se 1 (by rfl) ⟨740069, by rfl⟩ : syracuseStep 986759 = 1480139) B1480139
theorem B3116717 : Blo 614296 3116717 := bstep (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) B1168769
theorem B1969865 : Blo 614296 1969865 := bstep (se 2 (by rfl) ⟨738699, by rfl⟩ : syracuseStep 1969865 = 1477399) B1477399
theorem B1183547 : Blo 614296 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B921479 : Blo 614296 921479 := bstep (se 1 (by rfl) ⟨691109, by rfl⟩ : syracuseStep 921479 = 1382219) B1382219
theorem B921515 : Blo 614296 921515 := bstep (se 1 (by rfl) ⟨691136, by rfl⟩ : syracuseStep 921515 = 1382273) B1382273
theorem B921545 : Blo 614296 921545 := bstep (se 2 (by rfl) ⟨345579, by rfl⟩ : syracuseStep 921545 = 691159) B691159
theorem B692239 : Blo 614296 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B921659 : Blo 614296 921659 := bstep (se 1 (by rfl) ⟨691244, by rfl⟩ : syracuseStep 921659 = 1382489) B1382489
theorem B1970237 : Blo 614296 1970237 := bstep (se 3 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 1970237 = 738839) B738839
theorem B3739715 : Blo 614296 3739715 := bstep (se 1 (by rfl) ⟨2804786, by rfl⟩ : syracuseStep 3739715 = 5609573) B5609573
theorem B921719 : Blo 614296 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B921743 : Blo 614296 921743 := bstep (se 1 (by rfl) ⟨691307, by rfl⟩ : syracuseStep 921743 = 1382615) B1382615
theorem B1249427 : Blo 614296 1249427 := bstep (se 1 (by rfl) ⟨937070, by rfl⟩ : syracuseStep 1249427 = 1874141) B1874141
theorem B921785 : Blo 614296 921785 := bstep (se 2 (by rfl) ⟨345669, by rfl⟩ : syracuseStep 921785 = 691339) B691339
theorem B921863 : Blo 614296 921863 := bstep (se 1 (by rfl) ⟨691397, by rfl⟩ : syracuseStep 921863 = 1382795) B1382795
theorem B921899 : Blo 614296 921899 := bstep (se 1 (by rfl) ⟨691424, by rfl⟩ : syracuseStep 921899 = 1382849) B1382849
theorem B921929 : Blo 614296 921929 := bstep (se 2 (by rfl) ⟨345723, by rfl⟩ : syracuseStep 921929 = 691447) B691447
theorem B1315207 : Blo 614296 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B922043 : Blo 614296 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B4690385 : Blo 614296 4690385 := bstep (se 2 (by rfl) ⟨1758894, by rfl⟩ : syracuseStep 4690385 = 3517789) B3517789
theorem B922103 : Blo 614296 922103 := bstep (se 1 (by rfl) ⟨691577, by rfl⟩ : syracuseStep 922103 = 1383155) B1383155
theorem B692743 : Blo 614296 692743 := bstep (se 1 (by rfl) ⟨519557, by rfl⟩ : syracuseStep 692743 = 1039115) B1039115
theorem B922127 : Blo 614296 922127 := bstep (se 1 (by rfl) ⟨691595, by rfl⟩ : syracuseStep 922127 = 1383191) B1383191
theorem B922169 : Blo 614296 922169 := bstep (se 2 (by rfl) ⟨345813, by rfl⟩ : syracuseStep 922169 = 691627) B691627
theorem B922247 : Blo 614296 922247 := bstep (se 1 (by rfl) ⟨691685, by rfl⟩ : syracuseStep 922247 = 1383371) B1383371
theorem B922283 : Blo 614296 922283 := bstep (se 1 (by rfl) ⟨691712, by rfl⟩ : syracuseStep 922283 = 1383425) B1383425
theorem B692923 : Blo 614296 692923 := bstep (se 1 (by rfl) ⟨519692, by rfl⟩ : syracuseStep 692923 = 1039385) B1039385
theorem B922313 : Blo 614296 922313 := bstep (se 2 (by rfl) ⟨345867, by rfl⟩ : syracuseStep 922313 = 691735) B691735
theorem B10523429 : Blo 614296 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B922427 : Blo 614296 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B922487 : Blo 614296 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1315703 : Blo 614296 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B922511 : Blo 614296 922511 := bstep (se 1 (by rfl) ⟨691883, by rfl⟩ : syracuseStep 922511 = 1383767) B1383767
theorem B2626451 : Blo 614296 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B922553 : Blo 614296 922553 := bstep (se 2 (by rfl) ⟨345957, by rfl⟩ : syracuseStep 922553 = 691915) B691915
theorem B3412945 : Blo 614296 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B922631 : Blo 614296 922631 := bstep (se 1 (by rfl) ⟨691973, by rfl⟩ : syracuseStep 922631 = 1383947) B1383947
theorem B988175 : Blo 614296 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B922667 : Blo 614296 922667 := bstep (se 1 (by rfl) ⟨692000, by rfl⟩ : syracuseStep 922667 = 1384001) B1384001
theorem B7574573 : Blo 614296 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B2397251 : Blo 614296 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B922697 : Blo 614296 922697 := bstep (se 2 (by rfl) ⟨346011, by rfl⟩ : syracuseStep 922697 = 692023) B692023
theorem B60036227 : Blo 614296 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B693391 : Blo 614296 693391 := bstep (se 1 (by rfl) ⟨520043, by rfl⟩ : syracuseStep 693391 = 1040087) B1040087
theorem B922811 : Blo 614296 922811 := bstep (se 1 (by rfl) ⟨692108, by rfl⟩ : syracuseStep 922811 = 1384217) B1384217
theorem B922871 : Blo 614296 922871 := bstep (se 1 (by rfl) ⟨692153, by rfl⟩ : syracuseStep 922871 = 1384307) B1384307
theorem B3118337 : Blo 614296 3118337 := bstep (se 2 (by rfl) ⟨1169376, by rfl⟩ : syracuseStep 3118337 = 2338753) B2338753
theorem B922895 : Blo 614296 922895 := bstep (se 1 (by rfl) ⟨692171, by rfl⟩ : syracuseStep 922895 = 1384343) B1384343
theorem B922937 : Blo 614296 922937 := bstep (se 2 (by rfl) ⟨346101, by rfl⟩ : syracuseStep 922937 = 692203) B692203
theorem B923015 : Blo 614296 923015 := bstep (se 1 (by rfl) ⟨692261, by rfl⟩ : syracuseStep 923015 = 1384523) B1384523
theorem B923051 : Blo 614296 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B923081 : Blo 614296 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B118494737 : Blo 614296 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B923195 : Blo 614296 923195 := bstep (se 1 (by rfl) ⟨692396, by rfl⟩ : syracuseStep 923195 = 1384793) B1384793
theorem B923255 : Blo 614296 923255 := bstep (se 1 (by rfl) ⟨692441, by rfl⟩ : syracuseStep 923255 = 1384883) B1384883
theorem B693895 : Blo 614296 693895 := bstep (se 1 (by rfl) ⟨520421, by rfl⟩ : syracuseStep 693895 = 1040843) B1040843
theorem B923279 : Blo 614296 923279 := bstep (se 1 (by rfl) ⟨692459, by rfl⟩ : syracuseStep 923279 = 1384919) B1384919
theorem B923321 : Blo 614296 923321 := bstep (se 2 (by rfl) ⟨346245, by rfl⟩ : syracuseStep 923321 = 692491) B692491
theorem B923399 : Blo 614296 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B923435 : Blo 614296 923435 := bstep (se 1 (by rfl) ⟨692576, by rfl⟩ : syracuseStep 923435 = 1385153) B1385153
theorem B694075 : Blo 614296 694075 := bstep (se 1 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 694075 = 1041113) B1041113
theorem B923465 : Blo 614296 923465 := bstep (se 2 (by rfl) ⟨346299, by rfl⟩ : syracuseStep 923465 = 692599) B692599
theorem B2955143 : Blo 614296 2955143 := bstep (se 1 (by rfl) ⟨2216357, by rfl⟩ : syracuseStep 2955143 = 4432715) B4432715
theorem B1382291 : Blo 614296 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B923579 : Blo 614296 923579 := bstep (se 1 (by rfl) ⟨692684, by rfl⟩ : syracuseStep 923579 = 1385369) B1385369
theorem B1382345 : Blo 614296 1382345 := bstep (se 2 (by rfl) ⟨518379, by rfl⟩ : syracuseStep 1382345 = 1036759) B1036759
theorem B10000331 : Blo 614296 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B923639 : Blo 614296 923639 := bstep (se 1 (by rfl) ⟨692729, by rfl⟩ : syracuseStep 923639 = 1385459) B1385459
theorem B923663 : Blo 614296 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B3119147 : Blo 614296 3119147 := bstep (se 1 (by rfl) ⟨2339360, by rfl⟩ : syracuseStep 3119147 = 4678721) B4678721
theorem B923705 : Blo 614296 923705 := bstep (se 2 (by rfl) ⟨346389, by rfl⟩ : syracuseStep 923705 = 692779) B692779
theorem B2332739 : Blo 614296 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B923783 : Blo 614296 923783 := bstep (se 1 (by rfl) ⟨692837, by rfl⟩ : syracuseStep 923783 = 1385675) B1385675
theorem B923819 : Blo 614296 923819 := bstep (se 1 (by rfl) ⟨692864, by rfl⟩ : syracuseStep 923819 = 1385729) B1385729
theorem B923849 : Blo 614296 923849 := bstep (se 2 (by rfl) ⟨346443, by rfl⟩ : syracuseStep 923849 = 692887) B692887
theorem B694543 : Blo 614296 694543 := bstep (se 1 (by rfl) ⟨520907, by rfl⟩ : syracuseStep 694543 = 1041815) B1041815
theorem B923963 : Blo 614296 923963 := bstep (se 1 (by rfl) ⟨692972, by rfl⟩ : syracuseStep 923963 = 1385945) B1385945
theorem B7018811 : Blo 614296 7018811 := bstep (se 1 (by rfl) ⟨5264108, by rfl⟩ : syracuseStep 7018811 = 10528217) B10528217
theorem B924023 : Blo 614296 924023 := bstep (se 1 (by rfl) ⟨693017, by rfl⟩ : syracuseStep 924023 = 1386035) B1386035
theorem B924047 : Blo 614296 924047 := bstep (se 1 (by rfl) ⟨693035, by rfl⟩ : syracuseStep 924047 = 1386071) B1386071
theorem B3938705 : Blo 614296 3938705 := bstep (se 2 (by rfl) ⟨1477014, by rfl⟩ : syracuseStep 3938705 = 2954029) B2954029
theorem B1972633 : Blo 614296 1972633 := bstep (se 2 (by rfl) ⟨739737, by rfl⟩ : syracuseStep 1972633 = 1479475) B1479475
theorem B924089 : Blo 614296 924089 := bstep (se 2 (by rfl) ⟨346533, by rfl⟩ : syracuseStep 924089 = 693067) B693067
theorem B924167 : Blo 614296 924167 := bstep (se 1 (by rfl) ⟨693125, by rfl⟩ : syracuseStep 924167 = 1386251) B1386251
theorem B2333195 : Blo 614296 2333195 := bstep (se 1 (by rfl) ⟨1749896, by rfl⟩ : syracuseStep 2333195 = 3499793) B3499793
theorem B924203 : Blo 614296 924203 := bstep (se 1 (by rfl) ⟨693152, by rfl⟩ : syracuseStep 924203 = 1386305) B1386305
theorem B924233 : Blo 614296 924233 := bstep (se 2 (by rfl) ⟨346587, by rfl⟩ : syracuseStep 924233 = 693175) B693175
theorem B8428151 : Blo 614296 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B989815 : Blo 614296 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B1383047 : Blo 614296 1383047 := bstep (se 1 (by rfl) ⟨1037285, by rfl⟩ : syracuseStep 1383047 = 2074571) B2074571
theorem B924347 : Blo 614296 924347 := bstep (se 1 (by rfl) ⟨693260, by rfl⟩ : syracuseStep 924347 = 1386521) B1386521
theorem B924407 : Blo 614296 924407 := bstep (se 1 (by rfl) ⟨693305, by rfl⟩ : syracuseStep 924407 = 1386611) B1386611
theorem B695047 : Blo 614296 695047 := bstep (se 1 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 695047 = 1042571) B1042571
theorem B924431 : Blo 614296 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B1252111 : Blo 614296 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B924473 : Blo 614296 924473 := bstep (se 2 (by rfl) ⟨346677, by rfl⟩ : syracuseStep 924473 = 693355) B693355
theorem B1383227 : Blo 614296 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B990071 : Blo 614296 990071 := bstep (se 1 (by rfl) ⟨742553, by rfl⟩ : syracuseStep 990071 = 1485107) B1485107
theorem B924551 : Blo 614296 924551 := bstep (se 1 (by rfl) ⟨693413, by rfl⟩ : syracuseStep 924551 = 1386827) B1386827
theorem B3513233 : Blo 614296 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B1711001 : Blo 614296 1711001 := bstep (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) B1283251
theorem B924587 : Blo 614296 924587 := bstep (se 1 (by rfl) ⟨693440, by rfl⟩ : syracuseStep 924587 = 1386881) B1386881
theorem B1383353 : Blo 614296 1383353 := bstep (se 2 (by rfl) ⟨518757, by rfl⟩ : syracuseStep 1383353 = 1037515) B1037515
theorem B695227 : Blo 614296 695227 := bstep (se 1 (by rfl) ⟨521420, by rfl⟩ : syracuseStep 695227 = 1042841) B1042841
theorem B924617 : Blo 614296 924617 := bstep (se 2 (by rfl) ⟨346731, by rfl⟩ : syracuseStep 924617 = 693463) B693463
theorem B1481761 : Blo 614296 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B924731 : Blo 614296 924731 := bstep (se 1 (by rfl) ⟨693548, by rfl⟩ : syracuseStep 924731 = 1387097) B1387097
theorem B14851133 : Blo 614296 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B2661443 : Blo 614296 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B924791 : Blo 614296 924791 := bstep (se 1 (by rfl) ⟨693593, by rfl⟩ : syracuseStep 924791 = 1387187) B1387187
theorem B924815 : Blo 614296 924815 := bstep (se 1 (by rfl) ⟨693611, by rfl⟩ : syracuseStep 924815 = 1387223) B1387223
theorem B924857 : Blo 614296 924857 := bstep (se 2 (by rfl) ⟨346821, by rfl⟩ : syracuseStep 924857 = 693643) B693643
theorem B924935 : Blo 614296 924935 := bstep (se 1 (by rfl) ⟨693701, by rfl⟩ : syracuseStep 924935 = 1387403) B1387403
theorem B1383695 : Blo 614296 1383695 := bstep (se 1 (by rfl) ⟨1037771, by rfl⟩ : syracuseStep 1383695 = 2075543) B2075543
theorem B1383713 : Blo 614296 1383713 := bstep (se 2 (by rfl) ⟨518892, by rfl⟩ : syracuseStep 1383713 = 1037785) B1037785
theorem B924971 : Blo 614296 924971 := bstep (se 1 (by rfl) ⟨693728, by rfl⟩ : syracuseStep 924971 = 1387457) B1387457
theorem B3120443 : Blo 614296 3120443 := bstep (se 1 (by rfl) ⟨2340332, by rfl⟩ : syracuseStep 3120443 = 4680665) B4680665
theorem B925001 : Blo 614296 925001 := bstep (se 2 (by rfl) ⟨346875, by rfl⟩ : syracuseStep 925001 = 693751) B693751
theorem B3513689 : Blo 614296 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B6495623 : Blo 614296 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B925115 : Blo 614296 925115 := bstep (se 1 (by rfl) ⟨693836, by rfl⟩ : syracuseStep 925115 = 1387673) B1387673
theorem B3120605 : Blo 614296 3120605 := bstep (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) B1170227
theorem B925175 : Blo 614296 925175 := bstep (se 1 (by rfl) ⟨693881, by rfl⟩ : syracuseStep 925175 = 1387763) B1387763
theorem B925199 : Blo 614296 925199 := bstep (se 1 (by rfl) ⟨693899, by rfl⟩ : syracuseStep 925199 = 1387799) B1387799
theorem B925241 : Blo 614296 925241 := bstep (se 2 (by rfl) ⟨346965, by rfl⟩ : syracuseStep 925241 = 693931) B693931
theorem B1384055 : Blo 614296 1384055 := bstep (se 1 (by rfl) ⟨1038041, by rfl⟩ : syracuseStep 1384055 = 2076083) B2076083
theorem B1875575 : Blo 614296 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B925319 : Blo 614296 925319 := bstep (se 1 (by rfl) ⟨693989, by rfl⟩ : syracuseStep 925319 = 1387979) B1387979
theorem B925355 : Blo 614296 925355 := bstep (se 1 (by rfl) ⟨694016, by rfl⟩ : syracuseStep 925355 = 1388033) B1388033
theorem B925385 : Blo 614296 925385 := bstep (se 2 (by rfl) ⟨347019, by rfl⟩ : syracuseStep 925385 = 694039) B694039
theorem B3120929 : Blo 614296 3120929 := bstep (se 2 (by rfl) ⟨1170348, by rfl⟩ : syracuseStep 3120929 = 2340697) B2340697
theorem B1384235 : Blo 614296 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B925499 : Blo 614296 925499 := bstep (se 1 (by rfl) ⟨694124, by rfl⟩ : syracuseStep 925499 = 1388249) B1388249
theorem B925559 : Blo 614296 925559 := bstep (se 1 (by rfl) ⟨694169, by rfl⟩ : syracuseStep 925559 = 1388339) B1388339
theorem B925583 : Blo 614296 925583 := bstep (se 1 (by rfl) ⟨694187, by rfl⟩ : syracuseStep 925583 = 1388375) B1388375
theorem B925625 : Blo 614296 925625 := bstep (se 2 (by rfl) ⟨347109, by rfl⟩ : syracuseStep 925625 = 694219) B694219
theorem B925703 : Blo 614296 925703 := bstep (se 1 (by rfl) ⟨694277, by rfl⟩ : syracuseStep 925703 = 1388555) B1388555
theorem B1581089 : Blo 614296 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B925739 : Blo 614296 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B925769 : Blo 614296 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B5906519 : Blo 614296 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2367575 : Blo 614296 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B1384595 : Blo 614296 1384595 := bstep (se 1 (by rfl) ⟨1038446, by rfl⟩ : syracuseStep 1384595 = 2076893) B2076893
theorem B925883 : Blo 614296 925883 := bstep (se 1 (by rfl) ⟨694412, by rfl⟩ : syracuseStep 925883 = 1388825) B1388825
theorem B1384649 : Blo 614296 1384649 := bstep (se 2 (by rfl) ⟨519243, by rfl⟩ : syracuseStep 1384649 = 1038487) B1038487
theorem B1482953 : Blo 614296 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B925943 : Blo 614296 925943 := bstep (se 1 (by rfl) ⟨694457, by rfl⟩ : syracuseStep 925943 = 1388915) B1388915
theorem B925967 : Blo 614296 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B926009 : Blo 614296 926009 := bstep (se 2 (by rfl) ⟨347253, by rfl⟩ : syracuseStep 926009 = 694507) B694507
theorem B5611835 : Blo 614296 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B926087 : Blo 614296 926087 := bstep (se 1 (by rfl) ⟨694565, by rfl⟩ : syracuseStep 926087 = 1389131) B1389131
theorem B926123 : Blo 614296 926123 := bstep (se 1 (by rfl) ⟨694592, by rfl⟩ : syracuseStep 926123 = 1389185) B1389185
theorem B926153 : Blo 614296 926153 := bstep (se 2 (by rfl) ⟨347307, by rfl⟩ : syracuseStep 926153 = 694615) B694615
theorem B926267 : Blo 614296 926267 := bstep (se 1 (by rfl) ⟨694700, by rfl⟩ : syracuseStep 926267 = 1389401) B1389401
theorem B2335351 : Blo 614296 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B926327 : Blo 614296 926327 := bstep (se 1 (by rfl) ⟨694745, by rfl⟩ : syracuseStep 926327 = 1389491) B1389491
theorem B926351 : Blo 614296 926351 := bstep (se 1 (by rfl) ⟨694763, by rfl⟩ : syracuseStep 926351 = 1389527) B1389527
theorem B926393 : Blo 614296 926393 := bstep (se 2 (by rfl) ⟨347397, by rfl⟩ : syracuseStep 926393 = 694795) B694795
theorem B3121901 : Blo 614296 3121901 := bstep (se 3 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 3121901 = 1170713) B1170713
theorem B926471 : Blo 614296 926471 := bstep (se 1 (by rfl) ⟨694853, by rfl⟩ : syracuseStep 926471 = 1389707) B1389707
theorem B5251877 : Blo 614296 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B926507 : Blo 614296 926507 := bstep (se 1 (by rfl) ⟨694880, by rfl⟩ : syracuseStep 926507 = 1389761) B1389761
theorem B926537 : Blo 614296 926537 := bstep (se 2 (by rfl) ⟨347451, by rfl⟩ : syracuseStep 926537 = 694903) B694903
theorem B1385351 : Blo 614296 1385351 := bstep (se 1 (by rfl) ⟨1039013, by rfl⟩ : syracuseStep 1385351 = 2078027) B2078027
theorem B2073491 : Blo 614296 2073491 := bstep (se 1 (by rfl) ⟨1555118, by rfl⟩ : syracuseStep 2073491 = 3110237) B3110237
theorem B926651 : Blo 614296 926651 := bstep (se 1 (by rfl) ⟨694988, by rfl⟩ : syracuseStep 926651 = 1389977) B1389977
theorem B926711 : Blo 614296 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B926735 : Blo 614296 926735 := bstep (se 1 (by rfl) ⟨695051, by rfl⟩ : syracuseStep 926735 = 1390103) B1390103
theorem B926777 : Blo 614296 926777 := bstep (se 2 (by rfl) ⟨347541, by rfl⟩ : syracuseStep 926777 = 695083) B695083
theorem B1385531 : Blo 614296 1385531 := bstep (se 1 (by rfl) ⟨1039148, by rfl⟩ : syracuseStep 1385531 = 2078297) B2078297
theorem B7611479 : Blo 614296 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1877107 : Blo 614296 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B926855 : Blo 614296 926855 := bstep (se 1 (by rfl) ⟨695141, by rfl⟩ : syracuseStep 926855 = 1390283) B1390283
theorem B926891 : Blo 614296 926891 := bstep (se 1 (by rfl) ⟨695168, by rfl⟩ : syracuseStep 926891 = 1390337) B1390337
theorem B1385657 : Blo 614296 1385657 := bstep (se 2 (by rfl) ⟨519621, by rfl⟩ : syracuseStep 1385657 = 1039243) B1039243
theorem B926921 : Blo 614296 926921 := bstep (se 2 (by rfl) ⟨347595, by rfl⟩ : syracuseStep 926921 = 695191) B695191
theorem B2630893 : Blo 614296 2630893 := bstep (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) B986585
theorem B927035 : Blo 614296 927035 := bstep (se 1 (by rfl) ⟨695276, by rfl⟩ : syracuseStep 927035 = 1390553) B1390553
theorem B927095 : Blo 614296 927095 := bstep (se 1 (by rfl) ⟨695321, by rfl⟩ : syracuseStep 927095 = 1390643) B1390643
theorem B927119 : Blo 614296 927119 := bstep (se 1 (by rfl) ⟨695339, by rfl⟩ : syracuseStep 927119 = 1390679) B1390679
theorem B927161 : Blo 614296 927161 := bstep (se 2 (by rfl) ⟨347685, by rfl⟩ : syracuseStep 927161 = 695371) B695371
theorem B927239 : Blo 614296 927239 := bstep (se 1 (by rfl) ⟨695429, by rfl⟩ : syracuseStep 927239 = 1390859) B1390859
theorem B1385999 : Blo 614296 1385999 := bstep (se 1 (by rfl) ⟨1039499, by rfl⟩ : syracuseStep 1385999 = 2078999) B2078999
theorem B3122711 : Blo 614296 3122711 := bstep (se 1 (by rfl) ⟨2342033, by rfl⟩ : syracuseStep 3122711 = 4684067) B4684067
theorem B1386017 : Blo 614296 1386017 := bstep (se 2 (by rfl) ⟨519756, by rfl⟩ : syracuseStep 1386017 = 1039513) B1039513
theorem B927275 : Blo 614296 927275 := bstep (se 1 (by rfl) ⟨695456, by rfl⟩ : syracuseStep 927275 = 1390913) B1390913
theorem B1353275 : Blo 614296 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B2336323 : Blo 614296 2336323 := bstep (se 1 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 2336323 = 3504485) B3504485
theorem B927305 : Blo 614296 927305 := bstep (se 2 (by rfl) ⟨347739, by rfl⟩ : syracuseStep 927305 = 695479) B695479
theorem B927419 : Blo 614296 927419 := bstep (se 1 (by rfl) ⟨695564, by rfl⟩ : syracuseStep 927419 = 1391129) B1391129
theorem B2336627 : Blo 614296 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1386359 : Blo 614296 1386359 := bstep (se 1 (by rfl) ⟨1039769, by rfl⟩ : syracuseStep 1386359 = 2079539) B2079539
theorem B1386539 : Blo 614296 1386539 := bstep (se 1 (by rfl) ⟨1039904, by rfl⟩ : syracuseStep 1386539 = 2079809) B2079809
theorem B2074895 : Blo 614296 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B3385637 : Blo 614296 3385637 := bstep (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) B634807
theorem B2337083 : Blo 614296 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B1386899 : Blo 614296 1386899 := bstep (se 1 (by rfl) ⟨1040174, by rfl⟩ : syracuseStep 1386899 = 2080349) B2080349
theorem B3516857 : Blo 614296 3516857 := bstep (se 2 (by rfl) ⟨1318821, by rfl⟩ : syracuseStep 3516857 = 2637643) B2637643
theorem B1386953 : Blo 614296 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B2075165 : Blo 614296 2075165 := bstep (se 3 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 2075165 = 778187) B778187
theorem B1976861 : Blo 614296 1976861 := bstep (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) B741323
theorem B7514653 : Blo 614296 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B2337569 : Blo 614296 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B2632601 : Blo 614296 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B9972823 : Blo 614296 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B5614679 : Blo 614296 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B1387655 : Blo 614296 1387655 := bstep (se 1 (by rfl) ⟨1040741, by rfl⟩ : syracuseStep 1387655 = 2081483) B2081483
theorem B1387835 : Blo 614296 1387835 := bstep (se 1 (by rfl) ⟨1040876, by rfl⟩ : syracuseStep 1387835 = 2081753) B2081753
theorem B6335891 : Blo 614296 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B1387961 : Blo 614296 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B1584569 : Blo 614296 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B2338541 : Blo 614296 2338541 := bstep (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) B876953
theorem B1388303 : Blo 614296 1388303 := bstep (se 1 (by rfl) ⟨1041227, by rfl⟩ : syracuseStep 1388303 = 2082455) B2082455
theorem B1388321 : Blo 614296 1388321 := bstep (se 2 (by rfl) ⟨520620, by rfl⟩ : syracuseStep 1388321 = 1041241) B1041241
theorem B1879955 : Blo 614296 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B2076569 : Blo 614296 2076569 := bstep (se 2 (by rfl) ⟨778713, by rfl⟩ : syracuseStep 2076569 = 1557427) B1557427
theorem B1388663 : Blo 614296 1388663 := bstep (se 1 (by rfl) ⟨1041497, by rfl⟩ : syracuseStep 1388663 = 2082995) B2082995
theorem B7909649 : Blo 614296 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B3617057 : Blo 614296 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B1388843 : Blo 614296 1388843 := bstep (se 1 (by rfl) ⟨1041632, by rfl⟩ : syracuseStep 1388843 = 2083265) B2083265
theorem B2502971 : Blo 614296 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B2339225 : Blo 614296 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B3125789 : Blo 614296 3125789 := bstep (se 3 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 3125789 = 1172171) B1172171
theorem B2109995 : Blo 614296 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B2077271 : Blo 614296 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B1389203 : Blo 614296 1389203 := bstep (se 1 (by rfl) ⟨1041902, by rfl⟩ : syracuseStep 1389203 = 2083805) B2083805
theorem B6337201 : Blo 614296 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1389257 : Blo 614296 1389257 := bstep (se 2 (by rfl) ⟨520971, by rfl⟩ : syracuseStep 1389257 = 1041943) B1041943
theorem B4666085 : Blo 614296 4666085 := bstep (se 4 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 4666085 = 874891) B874891
theorem B3519247 : Blo 614296 3519247 := bstep (se 1 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 3519247 = 5278871) B5278871
theorem B3126275 : Blo 614296 3126275 := bstep (se 1 (by rfl) ⟨2344706, by rfl⟩ : syracuseStep 3126275 = 4689413) B4689413
theorem B1750045 : Blo 614296 1750045 := bstep (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) B656267
theorem B1782827 : Blo 614296 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B2077757 : Blo 614296 2077757 := bstep (se 3 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 2077757 = 779159) B779159
theorem B4011095 : Blo 614296 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2340211 : Blo 614296 2340211 := bstep (se 1 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 2340211 = 3510317) B3510317
theorem B1389959 : Blo 614296 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B72955313 : Blo 614296 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B1390139 : Blo 614296 1390139 := bstep (se 1 (by rfl) ⟨1042604, by rfl⟩ : syracuseStep 1390139 = 2085209) B2085209
theorem B5912129 : Blo 614296 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B1390265 : Blo 614296 1390265 := bstep (se 2 (by rfl) ⟨521349, by rfl⟩ : syracuseStep 1390265 = 1042699) B1042699
theorem B5912281 : Blo 614296 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B9647923 : Blo 614296 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B3520523 : Blo 614296 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B1390607 : Blo 614296 1390607 := bstep (se 1 (by rfl) ⟨1042955, by rfl⟩ : syracuseStep 1390607 = 2085911) B2085911
theorem B1390625 : Blo 614296 1390625 := bstep (se 2 (by rfl) ⟨521484, by rfl⟩ : syracuseStep 1390625 = 1042969) B1042969
theorem B3520705 : Blo 614296 3520705 := bstep (se 2 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 3520705 = 2640529) B2640529
theorem B2111777 : Blo 614296 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B1390967 : Blo 614296 1390967 := bstep (se 1 (by rfl) ⟨1043225, by rfl⟩ : syracuseStep 1390967 = 2086451) B2086451
theorem B2079161 : Blo 614296 2079161 := bstep (se 2 (by rfl) ⟨779685, by rfl⟩ : syracuseStep 2079161 = 1559371) B1559371
theorem B1554977 : Blo 614296 1554977 := bstep (se 2 (by rfl) ⟨583116, by rfl⟩ : syracuseStep 1554977 = 1166233) B1166233
theorem B1391147 : Blo 614296 1391147 := bstep (se 1 (by rfl) ⟨1043360, by rfl⟩ : syracuseStep 1391147 = 2086721) B2086721
theorem B3127895 : Blo 614296 3127895 := bstep (se 1 (by rfl) ⟨2345921, by rfl⟩ : syracuseStep 3127895 = 4691843) B4691843
theorem B2964275 : Blo 614296 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1751993 : Blo 614296 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B3947467 : Blo 614296 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B2079755 : Blo 614296 2079755 := bstep (se 1 (by rfl) ⟨1559816, by rfl⟩ : syracuseStep 2079755 = 3119633) B3119633
theorem B3128381 : Blo 614296 3128381 := bstep (se 3 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 3128381 = 1173143) B1173143
theorem B2079863 : Blo 614296 2079863 := bstep (se 1 (by rfl) ⟨1559897, by rfl⟩ : syracuseStep 2079863 = 3119795) B3119795
theorem B3325121 : Blo 614296 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B5258641 : Blo 614296 5258641 := bstep (se 2 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 5258641 = 3943981) B3943981
theorem B3554705 : Blo 614296 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B1555969 : Blo 614296 1555969 := bstep (se 2 (by rfl) ⟨583488, by rfl⟩ : syracuseStep 1555969 = 1166977) B1166977
theorem B2342429 : Blo 614296 2342429 := bstep (se 3 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 2342429 = 878411) B878411
theorem B10010141 : Blo 614296 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B2080457 : Blo 614296 2080457 := bstep (se 2 (by rfl) ⟨780171, by rfl⟩ : syracuseStep 2080457 = 1560343) B1560343
theorem B11812877 : Blo 614296 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B2670635 : Blo 614296 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1556567 : Blo 614296 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B1753235 : Blo 614296 1753235 := bstep (se 1 (by rfl) ⟨1314926, by rfl⟩ : syracuseStep 1753235 = 2629853) B2629853
theorem B2343113 : Blo 614296 2343113 := bstep (se 2 (by rfl) ⟨878667, by rfl⟩ : syracuseStep 2343113 = 1757335) B1757335
theorem B1556779 : Blo 614296 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B5915015 : Blo 614296 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B2081159 : Blo 614296 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B1556921 : Blo 614296 1556921 := bstep (se 2 (by rfl) ⟨583845, by rfl⟩ : syracuseStep 1556921 = 1167691) B1167691
theorem B2081537 : Blo 614296 2081537 := bstep (se 2 (by rfl) ⟨780576, by rfl⟩ : syracuseStep 2081537 = 1561153) B1561153
theorem B2540497 : Blo 614296 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B1557913 : Blo 614296 1557913 := bstep (se 2 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 1557913 = 1168435) B1168435
theorem B1754635 : Blo 614296 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B2082347 : Blo 614296 2082347 := bstep (se 1 (by rfl) ⟨1561760, by rfl⟩ : syracuseStep 2082347 = 3123521) B3123521
theorem B1558075 : Blo 614296 1558075 := bstep (se 1 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 1558075 = 2337113) B2337113
theorem B6670001 : Blo 614296 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B1558217 : Blo 614296 1558217 := bstep (se 2 (by rfl) ⟨584331, by rfl⟩ : syracuseStep 1558217 = 1168663) B1168663
theorem B1754909 : Blo 614296 1754909 := bstep (se 3 (by rfl) ⟨329045, by rfl⟩ : syracuseStep 1754909 = 658091) B658091
theorem B2344889 : Blo 614296 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B1558561 : Blo 614296 1558561 := bstep (se 2 (by rfl) ⟨584460, by rfl⟩ : syracuseStep 1558561 = 1168921) B1168921
theorem B2639915 : Blo 614296 2639915 := bstep (se 1 (by rfl) ⟨1979936, by rfl⟩ : syracuseStep 2639915 = 3959873) B3959873
theorem B1559159 : Blo 614296 1559159 := bstep (se 1 (by rfl) ⟨1169369, by rfl⟩ : syracuseStep 1559159 = 2338739) B2338739
theorem B5917475 : Blo 614296 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B2083643 : Blo 614296 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B2968579 : Blo 614296 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B1166537 : Blo 614296 1166537 := bstep (se 2 (by rfl) ⟨437451, by rfl⟩ : syracuseStep 1166537 = 874903) B874903
theorem B2084129 : Blo 614296 2084129 := bstep (se 2 (by rfl) ⟨781548, by rfl⟩ : syracuseStep 2084129 = 1563097) B1563097
theorem B937673 : Blo 614296 937673 := bstep (se 2 (by rfl) ⟨351627, by rfl⟩ : syracuseStep 937673 = 703255) B703255
theorem B6999857 : Blo 614296 6999857 := bstep (se 2 (by rfl) ⟨2624946, by rfl⟩ : syracuseStep 6999857 = 5249893) B5249893
theorem B2084723 : Blo 614296 2084723 := bstep (se 1 (by rfl) ⟨1563542, by rfl⟩ : syracuseStep 2084723 = 3127085) B3127085
theorem B1560455 : Blo 614296 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B1560505 : Blo 614296 1560505 := bstep (se 2 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 1560505 = 1170379) B1170379
theorem B4444247 : Blo 614296 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B1757369 : Blo 614296 1757369 := bstep (se 2 (by rfl) ⟨659013, by rfl⟩ : syracuseStep 1757369 = 1318027) B1318027
theorem B4444361 : Blo 614296 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B1757483 : Blo 614296 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B2249227 : Blo 614296 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1561103 : Blo 614296 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B12342131 : Blo 614296 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1037191 : Blo 614296 1037191 := bstep (se 1 (by rfl) ⟨777893, by rfl⟩ : syracuseStep 1037191 = 1555787) B1555787
theorem B1168519 : Blo 614296 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B1561801 : Blo 614296 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B1266959 : Blo 614296 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B1561943 : Blo 614296 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1758611 : Blo 614296 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B1037839 : Blo 614296 1037839 := bstep (se 1 (by rfl) ⟨778379, by rfl⟩ : syracuseStep 1037839 = 1556759) B1556759
theorem B1759009 : Blo 614296 1759009 := bstep (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) B1319257
theorem B3757913 : Blo 614296 3757913 := bstep (se 2 (by rfl) ⟨1409217, by rfl⟩ : syracuseStep 3757913 = 2818435) B2818435
theorem B1038379 : Blo 614296 1038379 := bstep (se 1 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 1038379 = 1557569) B1557569
theorem B1038521 : Blo 614296 1038521 := bstep (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) B778891
theorem B874795 : Blo 614296 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B3005047 : Blo 614296 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1759897 : Blo 614296 1759897 := bstep (se 2 (by rfl) ⟨659961, by rfl⟩ : syracuseStep 1759897 = 1319923) B1319923
theorem B1170121 : Blo 614296 1170121 := bstep (se 2 (by rfl) ⟨438795, by rfl⟩ : syracuseStep 1170121 = 877591) B877591
theorem B1039223 : Blo 614296 1039223 := bstep (se 1 (by rfl) ⟨779417, by rfl⟩ : syracuseStep 1039223 = 1558835) B1558835
theorem B3333143 : Blo 614296 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1760285 : Blo 614296 1760285 := bstep (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) B660107
theorem B2252033 : Blo 614296 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B1039675 : Blo 614296 1039675 := bstep (se 1 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 1039675 = 1559513) B1559513
theorem B33840443 : Blo 614296 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B1564019 : Blo 614296 1564019 := bstep (se 1 (by rfl) ⟨1173014, by rfl⟩ : syracuseStep 1564019 = 2346029) B2346029
theorem B7036307 : Blo 614296 7036307 := bstep (se 1 (by rfl) ⟨5277230, by rfl⟩ : syracuseStep 7036307 = 10554461) B10554461
theorem B1039817 : Blo 614296 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B777863 : Blo 614296 777863 := bstep (se 1 (by rfl) ⟨583397, by rfl⟩ : syracuseStep 777863 = 1166795) B1166795
theorem B4448051 : Blo 614296 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B876361 : Blo 614296 876361 := bstep (se 2 (by rfl) ⟨328635, by rfl⟩ : syracuseStep 876361 = 657271) B657271
theorem B1564535 : Blo 614296 1564535 := bstep (se 1 (by rfl) ⟨1173401, by rfl⟩ : syracuseStep 1564535 = 2346803) B2346803
theorem B614331 : Blo 614296 614331 := bstep (se 1 (by rfl) ⟨460748, by rfl⟩ : syracuseStep 614331 = 921497) B921497
theorem B614407 : Blo 614296 614407 := bstep (se 1 (by rfl) ⟨460805, by rfl⟩ : syracuseStep 614407 = 921611) B921611
theorem B614415 : Blo 614296 614415 := bstep (se 1 (by rfl) ⟨460811, by rfl⟩ : syracuseStep 614415 = 921623) B921623
theorem B614459 : Blo 614296 614459 := bstep (se 1 (by rfl) ⟨460844, by rfl⟩ : syracuseStep 614459 = 921689) B921689
theorem B27091037 : Blo 614296 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B614535 : Blo 614296 614535 := bstep (se 1 (by rfl) ⟨460901, by rfl⟩ : syracuseStep 614535 = 921803) B921803
theorem B1663111 : Blo 614296 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1040519 : Blo 614296 1040519 := bstep (se 1 (by rfl) ⟨780389, by rfl⟩ : syracuseStep 1040519 = 1560779) B1560779
theorem B614543 : Blo 614296 614543 := bstep (se 1 (by rfl) ⟨460907, by rfl⟩ : syracuseStep 614543 = 921815) B921815
theorem B614587 : Blo 614296 614587 := bstep (se 1 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 614587 = 921881) B921881
theorem B614663 : Blo 614296 614663 := bstep (se 1 (by rfl) ⟨460997, by rfl⟩ : syracuseStep 614663 = 921995) B921995
theorem B614671 : Blo 614296 614671 := bstep (se 1 (by rfl) ⟨461003, by rfl⟩ : syracuseStep 614671 = 922007) B922007
theorem B778511 : Blo 614296 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B614715 : Blo 614296 614715 := bstep (se 1 (by rfl) ⟨461036, by rfl⟩ : syracuseStep 614715 = 922073) B922073
theorem B876919 : Blo 614296 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B614791 : Blo 614296 614791 := bstep (se 1 (by rfl) ⟨461093, by rfl⟩ : syracuseStep 614791 = 922187) B922187
theorem B614799 : Blo 614296 614799 := bstep (se 1 (by rfl) ⟨461099, by rfl⟩ : syracuseStep 614799 = 922199) B922199
theorem B614843 : Blo 614296 614843 := bstep (se 1 (by rfl) ⟨461132, by rfl⟩ : syracuseStep 614843 = 922265) B922265
theorem B6644227 : Blo 614296 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B614919 : Blo 614296 614919 := bstep (se 1 (by rfl) ⟨461189, by rfl⟩ : syracuseStep 614919 = 922379) B922379
theorem B614927 : Blo 614296 614927 := bstep (se 1 (by rfl) ⟨461195, by rfl⟩ : syracuseStep 614927 = 922391) B922391
theorem B614971 : Blo 614296 614971 := bstep (se 1 (by rfl) ⟨461228, by rfl⟩ : syracuseStep 614971 = 922457) B922457
theorem B615047 : Blo 614296 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B615055 : Blo 614296 615055 := bstep (se 1 (by rfl) ⟨461291, by rfl⟩ : syracuseStep 615055 = 922583) B922583
theorem B615099 : Blo 614296 615099 := bstep (se 1 (by rfl) ⟨461324, by rfl⟩ : syracuseStep 615099 = 922649) B922649
theorem B615175 : Blo 614296 615175 := bstep (se 1 (by rfl) ⟨461381, by rfl⟩ : syracuseStep 615175 = 922763) B922763
theorem B615183 : Blo 614296 615183 := bstep (se 1 (by rfl) ⟨461387, by rfl⟩ : syracuseStep 615183 = 922775) B922775
theorem B1041167 : Blo 614296 1041167 := bstep (se 1 (by rfl) ⟨780875, by rfl⟩ : syracuseStep 1041167 = 1561751) B1561751
theorem B615227 : Blo 614296 615227 := bstep (se 1 (by rfl) ⟨461420, by rfl⟩ : syracuseStep 615227 = 922841) B922841
theorem B615303 : Blo 614296 615303 := bstep (se 1 (by rfl) ⟨461477, by rfl⟩ : syracuseStep 615303 = 922955) B922955
theorem B615311 : Blo 614296 615311 := bstep (se 1 (by rfl) ⟨461483, by rfl⟩ : syracuseStep 615311 = 922967) B922967
theorem B877483 : Blo 614296 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B615355 : Blo 614296 615355 := bstep (se 1 (by rfl) ⟨461516, by rfl⟩ : syracuseStep 615355 = 923033) B923033
theorem B615431 : Blo 614296 615431 := bstep (se 1 (by rfl) ⟨461573, by rfl⟩ : syracuseStep 615431 = 923147) B923147
theorem B615439 : Blo 614296 615439 := bstep (se 1 (by rfl) ⟨461579, by rfl⟩ : syracuseStep 615439 = 923159) B923159
theorem B615483 : Blo 614296 615483 := bstep (se 1 (by rfl) ⟨461612, by rfl⟩ : syracuseStep 615483 = 923225) B923225
theorem B1401991 : Blo 614296 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B615559 : Blo 614296 615559 := bstep (se 1 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 615559 = 923339) B923339
theorem B615567 : Blo 614296 615567 := bstep (se 1 (by rfl) ⟨461675, by rfl⟩ : syracuseStep 615567 = 923351) B923351
theorem B877711 : Blo 614296 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B1172627 : Blo 614296 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B615611 : Blo 614296 615611 := bstep (se 1 (by rfl) ⟨461708, by rfl⟩ : syracuseStep 615611 = 923417) B923417
theorem B615687 : Blo 614296 615687 := bstep (se 1 (by rfl) ⟨461765, by rfl⟩ : syracuseStep 615687 = 923531) B923531
theorem B615695 : Blo 614296 615695 := bstep (se 1 (by rfl) ⟨461771, by rfl⟩ : syracuseStep 615695 = 923543) B923543
theorem B1041707 : Blo 614296 1041707 := bstep (se 1 (by rfl) ⟨781280, by rfl⟩ : syracuseStep 1041707 = 1562561) B1562561
theorem B615739 : Blo 614296 615739 := bstep (se 1 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 615739 = 923609) B923609
theorem B1172855 : Blo 614296 1172855 := bstep (se 1 (by rfl) ⟨879641, by rfl⟩ : syracuseStep 1172855 = 1759283) B1759283
theorem B615815 : Blo 614296 615815 := bstep (se 1 (by rfl) ⟨461861, by rfl⟩ : syracuseStep 615815 = 923723) B923723
theorem B615823 : Blo 614296 615823 := bstep (se 1 (by rfl) ⟨461867, by rfl⟩ : syracuseStep 615823 = 923735) B923735
theorem B615867 : Blo 614296 615867 := bstep (se 1 (by rfl) ⟨461900, by rfl⟩ : syracuseStep 615867 = 923801) B923801
theorem B615943 : Blo 614296 615943 := bstep (se 1 (by rfl) ⟨461957, by rfl⟩ : syracuseStep 615943 = 923915) B923915
theorem B615951 : Blo 614296 615951 := bstep (se 1 (by rfl) ⟨461963, by rfl⟩ : syracuseStep 615951 = 923927) B923927
theorem B615995 : Blo 614296 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B616071 : Blo 614296 616071 := bstep (se 1 (by rfl) ⟨462053, by rfl⟩ : syracuseStep 616071 = 924107) B924107
theorem B616079 : Blo 614296 616079 := bstep (se 1 (by rfl) ⟨462059, by rfl⟩ : syracuseStep 616079 = 924119) B924119
theorem B1042105 : Blo 614296 1042105 := bstep (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) B781579
theorem B616123 : Blo 614296 616123 := bstep (se 1 (by rfl) ⟨462092, by rfl⟩ : syracuseStep 616123 = 924185) B924185
theorem B616199 : Blo 614296 616199 := bstep (se 1 (by rfl) ⟨462149, by rfl⟩ : syracuseStep 616199 = 924299) B924299
theorem B616207 : Blo 614296 616207 := bstep (se 1 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 616207 = 924311) B924311
theorem B616251 : Blo 614296 616251 := bstep (se 1 (by rfl) ⟨462188, by rfl⟩ : syracuseStep 616251 = 924377) B924377
theorem B616327 : Blo 614296 616327 := bstep (se 1 (by rfl) ⟨462245, by rfl⟩ : syracuseStep 616327 = 924491) B924491
theorem B616335 : Blo 614296 616335 := bstep (se 1 (by rfl) ⟨462251, by rfl⟩ : syracuseStep 616335 = 924503) B924503
theorem B616379 : Blo 614296 616379 := bstep (se 1 (by rfl) ⟨462284, by rfl⟩ : syracuseStep 616379 = 924569) B924569
theorem B1107913 : Blo 614296 1107913 := bstep (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) B830935
theorem B3008477 : Blo 614296 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B616455 : Blo 614296 616455 := bstep (se 1 (by rfl) ⟨462341, by rfl⟩ : syracuseStep 616455 = 924683) B924683
theorem B616463 : Blo 614296 616463 := bstep (se 1 (by rfl) ⟨462347, by rfl⟩ : syracuseStep 616463 = 924695) B924695
theorem B616507 : Blo 614296 616507 := bstep (se 1 (by rfl) ⟨462380, by rfl⟩ : syracuseStep 616507 = 924761) B924761
theorem B616583 : Blo 614296 616583 := bstep (se 1 (by rfl) ⟨462437, by rfl⟩ : syracuseStep 616583 = 924875) B924875
theorem B616591 : Blo 614296 616591 := bstep (se 1 (by rfl) ⟨462443, by rfl⟩ : syracuseStep 616591 = 924887) B924887
theorem B616635 : Blo 614296 616635 := bstep (se 1 (by rfl) ⟨462476, by rfl⟩ : syracuseStep 616635 = 924953) B924953
theorem B3336385 : Blo 614296 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B616711 : Blo 614296 616711 := bstep (se 1 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 616711 = 925067) B925067
theorem B878855 : Blo 614296 878855 := bstep (se 1 (by rfl) ⟨659141, by rfl⟩ : syracuseStep 878855 = 1318283) B1318283
theorem B68512013 : Blo 614296 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B616719 : Blo 614296 616719 := bstep (se 1 (by rfl) ⟨462539, by rfl⟩ : syracuseStep 616719 = 925079) B925079
theorem B616763 : Blo 614296 616763 := bstep (se 1 (by rfl) ⟨462572, by rfl⟩ : syracuseStep 616763 = 925145) B925145
theorem B1042807 : Blo 614296 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B2222471 : Blo 614296 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B616839 : Blo 614296 616839 := bstep (se 1 (by rfl) ⟨462629, by rfl⟩ : syracuseStep 616839 = 925259) B925259
theorem B616847 : Blo 614296 616847 := bstep (se 1 (by rfl) ⟨462635, by rfl⟩ : syracuseStep 616847 = 925271) B925271
theorem B616891 : Blo 614296 616891 := bstep (se 1 (by rfl) ⟨462668, by rfl⟩ : syracuseStep 616891 = 925337) B925337
theorem B879049 : Blo 614296 879049 := bstep (se 2 (by rfl) ⟨329643, by rfl⟩ : syracuseStep 879049 = 659287) B659287
theorem B616967 : Blo 614296 616967 := bstep (se 1 (by rfl) ⟨462725, by rfl⟩ : syracuseStep 616967 = 925451) B925451
theorem B616975 : Blo 614296 616975 := bstep (se 1 (by rfl) ⟨462731, by rfl⟩ : syracuseStep 616975 = 925463) B925463
theorem B3500567 : Blo 614296 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B617019 : Blo 614296 617019 := bstep (se 1 (by rfl) ⟨462764, by rfl⟩ : syracuseStep 617019 = 925529) B925529
theorem B1043003 : Blo 614296 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B617095 : Blo 614296 617095 := bstep (se 1 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 617095 = 925643) B925643
theorem B617103 : Blo 614296 617103 := bstep (se 1 (by rfl) ⟨462827, by rfl⟩ : syracuseStep 617103 = 925655) B925655
theorem B617147 : Blo 614296 617147 := bstep (se 1 (by rfl) ⟨462860, by rfl⟩ : syracuseStep 617147 = 925721) B925721
theorem B617223 : Blo 614296 617223 := bstep (se 1 (by rfl) ⟨462917, by rfl⟩ : syracuseStep 617223 = 925835) B925835
theorem B5630735 : Blo 614296 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B617231 : Blo 614296 617231 := bstep (se 1 (by rfl) ⟨462923, by rfl⟩ : syracuseStep 617231 = 925847) B925847
theorem B617275 : Blo 614296 617275 := bstep (se 1 (by rfl) ⟨462956, by rfl⟩ : syracuseStep 617275 = 925913) B925913
theorem B617351 : Blo 614296 617351 := bstep (se 1 (by rfl) ⟨463013, by rfl⟩ : syracuseStep 617351 = 926027) B926027
theorem B617359 : Blo 614296 617359 := bstep (se 1 (by rfl) ⟨463019, by rfl⟩ : syracuseStep 617359 = 926039) B926039
theorem B617403 : Blo 614296 617403 := bstep (se 1 (by rfl) ⟨463052, by rfl⟩ : syracuseStep 617403 = 926105) B926105
theorem B879607 : Blo 614296 879607 := bstep (se 1 (by rfl) ⟨659705, by rfl⟩ : syracuseStep 879607 = 1319411) B1319411
theorem B617479 : Blo 614296 617479 := bstep (se 1 (by rfl) ⟨463109, by rfl⟩ : syracuseStep 617479 = 926219) B926219
theorem B617487 : Blo 614296 617487 := bstep (se 1 (by rfl) ⟨463115, by rfl⟩ : syracuseStep 617487 = 926231) B926231
theorem B1403963 : Blo 614296 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B617531 : Blo 614296 617531 := bstep (se 1 (by rfl) ⟨463148, by rfl⟩ : syracuseStep 617531 = 926297) B926297
theorem B617607 : Blo 614296 617607 := bstep (se 1 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 617607 = 926411) B926411
theorem B617615 : Blo 614296 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B781483 : Blo 614296 781483 := bstep (se 1 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 781483 = 1172225) B1172225
theorem B617659 : Blo 614296 617659 := bstep (se 1 (by rfl) ⟨463244, by rfl⟩ : syracuseStep 617659 = 926489) B926489
theorem B617735 : Blo 614296 617735 := bstep (se 1 (by rfl) ⟨463301, by rfl⟩ : syracuseStep 617735 = 926603) B926603
theorem B617743 : Blo 614296 617743 := bstep (se 1 (by rfl) ⟨463307, by rfl⟩ : syracuseStep 617743 = 926615) B926615
theorem B617787 : Blo 614296 617787 := bstep (se 1 (by rfl) ⟨463340, by rfl⟩ : syracuseStep 617787 = 926681) B926681
theorem B15232387 : Blo 614296 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B617863 : Blo 614296 617863 := bstep (se 1 (by rfl) ⟨463397, by rfl⟩ : syracuseStep 617863 = 926795) B926795
theorem B617871 : Blo 614296 617871 := bstep (se 1 (by rfl) ⟨463403, by rfl⟩ : syracuseStep 617871 = 926807) B926807
theorem B617915 : Blo 614296 617915 := bstep (se 1 (by rfl) ⟨463436, by rfl⟩ : syracuseStep 617915 = 926873) B926873
theorem B617991 : Blo 614296 617991 := bstep (se 1 (by rfl) ⟨463493, by rfl⟩ : syracuseStep 617991 = 926987) B926987
theorem B617999 : Blo 614296 617999 := bstep (se 1 (by rfl) ⟨463499, by rfl⟩ : syracuseStep 617999 = 926999) B926999
theorem B618043 : Blo 614296 618043 := bstep (se 1 (by rfl) ⟨463532, by rfl⟩ : syracuseStep 618043 = 927065) B927065
theorem B618119 : Blo 614296 618119 := bstep (se 1 (by rfl) ⟨463589, by rfl⟩ : syracuseStep 618119 = 927179) B927179
theorem B618127 : Blo 614296 618127 := bstep (se 1 (by rfl) ⟨463595, by rfl⟩ : syracuseStep 618127 = 927191) B927191
theorem B1666745 : Blo 614296 1666745 := bstep (se 2 (by rfl) ⟨625029, by rfl⟩ : syracuseStep 1666745 = 1250059) B1250059
theorem B880313 : Blo 614296 880313 := bstep (se 2 (by rfl) ⟨330117, by rfl⟩ : syracuseStep 880313 = 660235) B660235
theorem B618171 : Blo 614296 618171 := bstep (se 1 (by rfl) ⟨463628, by rfl⟩ : syracuseStep 618171 = 927257) B927257
theorem B5336833 : Blo 614296 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B618247 : Blo 614296 618247 := bstep (se 1 (by rfl) ⟨463685, by rfl⟩ : syracuseStep 618247 = 927371) B927371
theorem B618255 : Blo 614296 618255 := bstep (se 1 (by rfl) ⟨463691, by rfl⟩ : syracuseStep 618255 = 927383) B927383
theorem B782455 : Blo 614296 782455 := bstep (se 1 (by rfl) ⟨586841, by rfl⟩ : syracuseStep 782455 = 1173683) B1173683
theorem B4452641 : Blo 614296 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B7008605 : Blo 614296 7008605 := bstep (se 3 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 7008605 = 2628227) B2628227
theorem B1601927 : Blo 614296 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B2257645 : Blo 614296 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B1668107 : Blo 614296 1668107 := bstep (se 1 (by rfl) ⟨1251080, by rfl⟩ : syracuseStep 1668107 = 2502161) B2502161
theorem B1406099 : Blo 614296 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B1995977 : Blo 614296 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B2225353 : Blo 614296 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B3503735 : Blo 614296 3503735 := bstep (se 1 (by rfl) ⟨2627801, by rfl⟩ : syracuseStep 3503735 = 5255603) B5255603
theorem B7010063 : Blo 614296 7010063 := bstep (se 1 (by rfl) ⟨5257547, by rfl⟩ : syracuseStep 7010063 = 10515095) B10515095
theorem B3111371 : Blo 614296 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B3111695 : Blo 614296 3111695 := bstep (se 1 (by rfl) ⟨2333771, by rfl⟩ : syracuseStep 3111695 = 4667543) B4667543
theorem B7109869 : Blo 614296 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B1670519 : Blo 614296 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B4456241 : Blo 614296 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1114003 : Blo 614296 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1245623 : Blo 614296 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B3113801 : Blo 614296 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B657019 : Blo 614296 657019 := bstep (se 1 (by rfl) ⟨492764, by rfl⟩ : syracuseStep 657019 = 985529) B985529
theorem B3507857 : Blo 614296 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B7014437 : Blo 614296 7014437 := bstep (se 4 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 7014437 = 1315207) B1315207
theorem B3115097 : Blo 614296 3115097 := bstep (se 2 (by rfl) ⟨1168161, by rfl⟩ : syracuseStep 3115097 = 2336323) B2336323
theorem B3508541 : Blo 614296 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B657839 : Blo 614296 657839 := bstep (se 1 (by rfl) ⟨493379, by rfl⟩ : syracuseStep 657839 = 986759) B986759
theorem B1313243 : Blo 614296 1313243 := bstep (se 1 (by rfl) ⟨984932, by rfl⟩ : syracuseStep 1313243 = 1969865) B1969865
theorem B625115 : Blo 614296 625115 := bstep (se 1 (by rfl) ⟨468836, by rfl⟩ : syracuseStep 625115 = 937673) B937673
theorem B789031 : Blo 614296 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B1477217 : Blo 614296 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B1313491 : Blo 614296 1313491 := bstep (se 1 (by rfl) ⟨985118, by rfl⟩ : syracuseStep 1313491 = 1970237) B1970237
theorem B2493143 : Blo 614296 2493143 := bstep (se 1 (by rfl) ⟨1869857, by rfl⟩ : syracuseStep 2493143 = 3739715) B3739715
theorem B11995877 : Blo 614296 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B7015619 : Blo 614296 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B8228087 : Blo 614296 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B16026917 : Blo 614296 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B658783 : Blo 614296 658783 := bstep (se 1 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 658783 = 988175) B988175
theorem B5049715 : Blo 614296 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B3378557 : Blo 614296 3378557 := bstep (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) B1266959
theorem B2493985 : Blo 614296 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B921449 : Blo 614296 921449 := bstep (se 2 (by rfl) ⟨345543, by rfl⟩ : syracuseStep 921449 = 691087) B691087
theorem B1314721 : Blo 614296 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1970095 : Blo 614296 1970095 := bstep (se 1 (by rfl) ⟨1477571, by rfl⟩ : syracuseStep 1970095 = 2955143) B2955143
theorem B921527 : Blo 614296 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B921563 : Blo 614296 921563 := bstep (se 1 (by rfl) ⟨691172, by rfl⟩ : syracuseStep 921563 = 1382345) B1382345
theorem B692347 : Blo 614296 692347 := bstep (se 1 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 692347 = 1038521) B1038521
theorem B2625803 : Blo 614296 2625803 := bstep (se 1 (by rfl) ⟨1969352, by rfl⟩ : syracuseStep 2625803 = 3938705) B3938705
theorem B2101565 : Blo 614296 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B922031 : Blo 614296 922031 := bstep (se 1 (by rfl) ⟨691523, by rfl⟩ : syracuseStep 922031 = 1383047) B1383047
theorem B922121 : Blo 614296 922121 := bstep (se 2 (by rfl) ⟨345795, by rfl⟩ : syracuseStep 922121 = 691591) B691591
theorem B922151 : Blo 614296 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B692815 : Blo 614296 692815 := bstep (se 1 (by rfl) ⟨519611, by rfl⟩ : syracuseStep 692815 = 1039223) B1039223
theorem B660047 : Blo 614296 660047 := bstep (se 1 (by rfl) ⟨495035, by rfl⟩ : syracuseStep 660047 = 990071) B990071
theorem B1577569 : Blo 614296 1577569 := bstep (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) B1183177
theorem B922235 : Blo 614296 922235 := bstep (se 1 (by rfl) ⟨691676, by rfl⟩ : syracuseStep 922235 = 1383353) B1383353
theorem B9900755 : Blo 614296 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B1774295 : Blo 614296 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B922361 : Blo 614296 922361 := bstep (se 2 (by rfl) ⟨345885, by rfl⟩ : syracuseStep 922361 = 691771) B691771
theorem B922463 : Blo 614296 922463 := bstep (se 1 (by rfl) ⟨691847, by rfl⟩ : syracuseStep 922463 = 1383695) B1383695
theorem B922475 : Blo 614296 922475 := bstep (se 1 (by rfl) ⟨691856, by rfl⟩ : syracuseStep 922475 = 1383713) B1383713
theorem B4330415 : Blo 614296 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B4690871 : Blo 614296 4690871 := bstep (se 1 (by rfl) ⟨3518153, by rfl⟩ : syracuseStep 4690871 = 7036307) B7036307
theorem B693211 : Blo 614296 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B7115777 : Blo 614296 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B922703 : Blo 614296 922703 := bstep (se 1 (by rfl) ⟨692027, by rfl⟩ : syracuseStep 922703 = 1384055) B1384055
theorem B922823 : Blo 614296 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B922985 : Blo 614296 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B3937679 : Blo 614296 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1578383 : Blo 614296 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B18060691 : Blo 614296 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B693679 : Blo 614296 693679 := bstep (se 1 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 693679 = 1040519) B1040519
theorem B923063 : Blo 614296 923063 := bstep (se 1 (by rfl) ⟨692297, by rfl⟩ : syracuseStep 923063 = 1384595) B1384595
theorem B923099 : Blo 614296 923099 := bstep (se 1 (by rfl) ⟨692324, by rfl⟩ : syracuseStep 923099 = 1384649) B1384649
theorem B3741223 : Blo 614296 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B694111 : Blo 614296 694111 := bstep (se 1 (by rfl) ⟨520583, by rfl⟩ : syracuseStep 694111 = 1041167) B1041167
theorem B923567 : Blo 614296 923567 := bstep (se 1 (by rfl) ⟨692675, by rfl⟩ : syracuseStep 923567 = 1385351) B1385351
theorem B1382327 : Blo 614296 1382327 := bstep (se 1 (by rfl) ⟨1036745, by rfl⟩ : syracuseStep 1382327 = 2073491) B2073491
theorem B923657 : Blo 614296 923657 := bstep (se 2 (by rfl) ⟨346371, by rfl⟩ : syracuseStep 923657 = 692743) B692743
theorem B7477285 : Blo 614296 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B923687 : Blo 614296 923687 := bstep (se 1 (by rfl) ⟨692765, by rfl⟩ : syracuseStep 923687 = 1385531) B1385531
theorem B923771 : Blo 614296 923771 := bstep (se 1 (by rfl) ⟨692828, by rfl⟩ : syracuseStep 923771 = 1385657) B1385657
theorem B694471 : Blo 614296 694471 := bstep (se 1 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 694471 = 1041707) B1041707
theorem B923897 : Blo 614296 923897 := bstep (se 2 (by rfl) ⟨346461, by rfl⟩ : syracuseStep 923897 = 692923) B692923
theorem B923999 : Blo 614296 923999 := bstep (se 1 (by rfl) ⟨692999, by rfl⟩ : syracuseStep 923999 = 1385999) B1385999
theorem B4692329 : Blo 614296 4692329 := bstep (se 2 (by rfl) ⟨1759623, by rfl⟩ : syracuseStep 4692329 = 3519247) B3519247
theorem B924011 : Blo 614296 924011 := bstep (se 1 (by rfl) ⟨693008, by rfl⟩ : syracuseStep 924011 = 1386017) B1386017
theorem B1382921 : Blo 614296 1382921 := bstep (se 2 (by rfl) ⟨518595, by rfl⟩ : syracuseStep 1382921 = 1037191) B1037191
theorem B924239 : Blo 614296 924239 := bstep (se 1 (by rfl) ⟨693179, by rfl⟩ : syracuseStep 924239 = 1386359) B1386359
theorem B2005651 : Blo 614296 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B924359 : Blo 614296 924359 := bstep (se 1 (by rfl) ⟨693269, by rfl⟩ : syracuseStep 924359 = 1386539) B1386539
theorem B2333393 : Blo 614296 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B1383263 : Blo 614296 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B924521 : Blo 614296 924521 := bstep (se 2 (by rfl) ⟨346695, by rfl⟩ : syracuseStep 924521 = 693391) B693391
theorem B1481647 : Blo 614296 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B924599 : Blo 614296 924599 := bstep (se 1 (by rfl) ⟨693449, by rfl⟩ : syracuseStep 924599 = 1386899) B1386899
theorem B924635 : Blo 614296 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B2333711 : Blo 614296 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1383443 : Blo 614296 1383443 := bstep (se 1 (by rfl) ⟨1037582, by rfl⟩ : syracuseStep 1383443 = 2075165) B2075165
theorem B1317907 : Blo 614296 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B695335 : Blo 614296 695335 := bstep (se 1 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 695335 = 1043003) B1043003
theorem B3120281 : Blo 614296 3120281 := bstep (se 2 (by rfl) ⟨1170105, by rfl⟩ : syracuseStep 3120281 = 2340211) B2340211
theorem B1383785 : Blo 614296 1383785 := bstep (se 2 (by rfl) ⟨518919, by rfl⟩ : syracuseStep 1383785 = 1037839) B1037839
theorem B3743119 : Blo 614296 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B925103 : Blo 614296 925103 := bstep (se 1 (by rfl) ⟨693827, by rfl⟩ : syracuseStep 925103 = 1387655) B1387655
theorem B925193 : Blo 614296 925193 := bstep (se 2 (by rfl) ⟨346947, by rfl⟩ : syracuseStep 925193 = 693895) B693895
theorem B925223 : Blo 614296 925223 := bstep (se 1 (by rfl) ⟨693917, by rfl⟩ : syracuseStep 925223 = 1387835) B1387835
theorem B925307 : Blo 614296 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B4562669 : Blo 614296 4562669 := bstep (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) B1711001
theorem B7020269 : Blo 614296 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B925433 : Blo 614296 925433 := bstep (se 2 (by rfl) ⟨347037, by rfl⟩ : syracuseStep 925433 = 694075) B694075
theorem B925535 : Blo 614296 925535 := bstep (se 1 (by rfl) ⟨694151, by rfl⟩ : syracuseStep 925535 = 1388303) B1388303
theorem B925547 : Blo 614296 925547 := bstep (se 1 (by rfl) ⟨694160, by rfl⟩ : syracuseStep 925547 = 1388321) B1388321
theorem B1253303 : Blo 614296 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B1384379 : Blo 614296 1384379 := bstep (se 1 (by rfl) ⟨1038284, by rfl⟩ : syracuseStep 1384379 = 2076569) B2076569
theorem B1384505 : Blo 614296 1384505 := bstep (se 2 (by rfl) ⟨519189, by rfl⟩ : syracuseStep 1384505 = 1038379) B1038379
theorem B925775 : Blo 614296 925775 := bstep (se 1 (by rfl) ⟨694331, by rfl⟩ : syracuseStep 925775 = 1388663) B1388663
theorem B925895 : Blo 614296 925895 := bstep (se 1 (by rfl) ⟨694421, by rfl⟩ : syracuseStep 925895 = 1388843) B1388843
theorem B4694273 : Blo 614296 4694273 := bstep (se 2 (by rfl) ⟨1760352, by rfl⟩ : syracuseStep 4694273 = 3520705) B3520705
theorem B926057 : Blo 614296 926057 := bstep (se 2 (by rfl) ⟨347271, by rfl⟩ : syracuseStep 926057 = 694543) B694543
theorem B1384847 : Blo 614296 1384847 := bstep (se 1 (by rfl) ⟨1038635, by rfl⟩ : syracuseStep 1384847 = 2077271) B2077271
theorem B926135 : Blo 614296 926135 := bstep (se 1 (by rfl) ⟨694601, by rfl⟩ : syracuseStep 926135 = 1389203) B1389203
theorem B926171 : Blo 614296 926171 := bstep (se 1 (by rfl) ⟨694628, by rfl⟩ : syracuseStep 926171 = 1389257) B1389257
theorem B2630177 : Blo 614296 2630177 := bstep (se 2 (by rfl) ⟨986316, by rfl⟩ : syracuseStep 2630177 = 1972633) B1972633
theorem B1188551 : Blo 614296 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B1385171 : Blo 614296 1385171 := bstep (se 1 (by rfl) ⟨1038878, by rfl⟩ : syracuseStep 1385171 = 2077757) B2077757
theorem B1319753 : Blo 614296 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B926639 : Blo 614296 926639 := bstep (se 1 (by rfl) ⟨694979, by rfl⟩ : syracuseStep 926639 = 1389959) B1389959
theorem B48636875 : Blo 614296 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B926729 : Blo 614296 926729 := bstep (se 2 (by rfl) ⟨347523, by rfl⟩ : syracuseStep 926729 = 695047) B695047
theorem B926759 : Blo 614296 926759 := bstep (se 1 (by rfl) ⟨695069, by rfl⟩ : syracuseStep 926759 = 1390139) B1390139
theorem B3941419 : Blo 614296 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B2335823 : Blo 614296 2335823 := bstep (se 1 (by rfl) ⟨1751867, by rfl⟩ : syracuseStep 2335823 = 3503735) B3503735
theorem B926843 : Blo 614296 926843 := bstep (se 1 (by rfl) ⟨695132, by rfl⟩ : syracuseStep 926843 = 1390265) B1390265
theorem B926969 : Blo 614296 926969 := bstep (se 2 (by rfl) ⟨347613, by rfl⟩ : syracuseStep 926969 = 695227) B695227
theorem B927071 : Blo 614296 927071 := bstep (se 1 (by rfl) ⟨695303, by rfl⟩ : syracuseStep 927071 = 1390607) B1390607
theorem B927083 : Blo 614296 927083 := bstep (se 1 (by rfl) ⟨695312, by rfl⟩ : syracuseStep 927083 = 1390625) B1390625
theorem B1975681 : Blo 614296 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B927311 : Blo 614296 927311 := bstep (se 1 (by rfl) ⟨695483, by rfl⟩ : syracuseStep 927311 = 1390967) B1390967
theorem B1386107 : Blo 614296 1386107 := bstep (se 1 (by rfl) ⟨1039580, by rfl⟩ : syracuseStep 1386107 = 2079161) B2079161
theorem B2074247 : Blo 614296 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B9479825 : Blo 614296 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B2074301 : Blo 614296 2074301 := bstep (se 3 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 2074301 = 777863) B777863
theorem B927431 : Blo 614296 927431 := bstep (se 1 (by rfl) ⟨695573, by rfl⟩ : syracuseStep 927431 = 1391147) B1391147
theorem B1386233 : Blo 614296 1386233 := bstep (se 2 (by rfl) ⟨519837, by rfl⟩ : syracuseStep 1386233 = 1039675) B1039675
theorem B2074463 : Blo 614296 2074463 := bstep (se 1 (by rfl) ⟨1555847, by rfl⟩ : syracuseStep 2074463 = 3111695) B3111695
theorem B1976183 : Blo 614296 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B2074625 : Blo 614296 2074625 := bstep (se 2 (by rfl) ⟨777984, by rfl⟩ : syracuseStep 2074625 = 1555969) B1555969
theorem B1386503 : Blo 614296 1386503 := bstep (se 1 (by rfl) ⟨1039877, by rfl⟩ : syracuseStep 1386503 = 2079755) B2079755
theorem B1386575 : Blo 614296 1386575 := bstep (se 1 (by rfl) ⟨1039931, by rfl⟩ : syracuseStep 1386575 = 2079863) B2079863
theorem B5941349 : Blo 614296 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B2369803 : Blo 614296 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B1386971 : Blo 614296 1386971 := bstep (se 1 (by rfl) ⟨1040228, by rfl⟩ : syracuseStep 1386971 = 2080457) B2080457
theorem B7875251 : Blo 614296 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B1780423 : Blo 614296 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B2075435 : Blo 614296 2075435 := bstep (se 1 (by rfl) ⟨1556576, by rfl⟩ : syracuseStep 2075435 = 3113153) B3113153
theorem B3943343 : Blo 614296 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B1387439 : Blo 614296 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B2075705 : Blo 614296 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B1387691 : Blo 614296 1387691 := bstep (se 1 (by rfl) ⟨1040768, by rfl⟩ : syracuseStep 1387691 = 2081537) B2081537
theorem B8858969 : Blo 614296 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B2076029 : Blo 614296 2076029 := bstep (se 3 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 2076029 = 778511) B778511
theorem B2338267 : Blo 614296 2338267 := bstep (se 1 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 2338267 = 3507401) B3507401
theorem B2076299 : Blo 614296 2076299 := bstep (se 1 (by rfl) ⟨1557224, by rfl⟩ : syracuseStep 2076299 = 3114449) B3114449
theorem B1388231 : Blo 614296 1388231 := bstep (se 1 (by rfl) ⟨1041173, by rfl⟩ : syracuseStep 1388231 = 2082347) B2082347
theorem B3387329 : Blo 614296 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B2502809 : Blo 614296 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B3944983 : Blo 614296 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B2077217 : Blo 614296 2077217 := bstep (se 2 (by rfl) ⟨778956, by rfl⟩ : syracuseStep 2077217 = 1557913) B1557913
theorem B1389095 : Blo 614296 1389095 := bstep (se 1 (by rfl) ⟨1041821, by rfl⟩ : syracuseStep 1389095 = 2083643) B2083643
theorem B2339513 : Blo 614296 2339513 := bstep (se 2 (by rfl) ⟨877317, by rfl⟩ : syracuseStep 2339513 = 1754635) B1754635
theorem B2339543 : Blo 614296 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B2077433 : Blo 614296 2077433 := bstep (se 2 (by rfl) ⟨779037, by rfl⟩ : syracuseStep 2077433 = 1558075) B1558075
theorem B1389419 : Blo 614296 1389419 := bstep (se 1 (by rfl) ⟨1042064, by rfl⟩ : syracuseStep 1389419 = 2084129) B2084129
theorem B1389473 : Blo 614296 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B2077703 : Blo 614296 2077703 := bstep (se 1 (by rfl) ⟨1558277, by rfl⟩ : syracuseStep 2077703 = 3116555) B3116555
theorem B2077811 : Blo 614296 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B4666571 : Blo 614296 4666571 := bstep (se 1 (by rfl) ⟨3499928, by rfl⟩ : syracuseStep 4666571 = 6999857) B6999857
theorem B1389815 : Blo 614296 1389815 := bstep (se 1 (by rfl) ⟨1042361, by rfl⟩ : syracuseStep 1389815 = 2084723) B2084723
theorem B2078081 : Blo 614296 2078081 := bstep (se 2 (by rfl) ⟨779280, by rfl⟩ : syracuseStep 2078081 = 1558561) B1558561
theorem B2962831 : Blo 614296 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B832951 : Blo 614296 832951 := bstep (se 1 (by rfl) ⟨624713, by rfl⟩ : syracuseStep 832951 = 1249427) B1249427
theorem B102282709 : Blo 614296 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B2962907 : Blo 614296 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B3126923 : Blo 614296 3126923 := bstep (se 1 (by rfl) ⟨2345192, by rfl⟩ : syracuseStep 3126923 = 4690385) B4690385
theorem B3749597 : Blo 614296 3749597 := bstep (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) B1406099
theorem B1390409 : Blo 614296 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B1750967 : Blo 614296 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B40024151 : Blo 614296 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B2078891 : Blo 614296 2078891 := bstep (se 1 (by rfl) ⟨1559168, by rfl⟩ : syracuseStep 2078891 = 3118337) B3118337
theorem B2505275 : Blo 614296 2505275 := bstep (se 1 (by rfl) ⟨1878956, by rfl⟩ : syracuseStep 2505275 = 3757913) B3757913
theorem B6666887 : Blo 614296 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B2079431 : Blo 614296 2079431 := bstep (se 1 (by rfl) ⟨1559573, by rfl⟩ : syracuseStep 2079431 = 3119147) B3119147
theorem B1555159 : Blo 614296 1555159 := bstep (se 1 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 1555159 = 2332739) B2332739
theorem B2407241 : Blo 614296 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B1751969 : Blo 614296 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1555463 : Blo 614296 1555463 := bstep (se 1 (by rfl) ⟨1166597, by rfl⟩ : syracuseStep 1555463 = 2333195) B2333195
theorem B2342155 : Blo 614296 2342155 := bstep (se 1 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 2342155 = 3513233) B3513233
theorem B1752425 : Blo 614296 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B2080295 : Blo 614296 2080295 := bstep (se 1 (by rfl) ⟨1560221, by rfl⟩ : syracuseStep 2080295 = 3120443) B3120443
theorem B22560295 : Blo 614296 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B2342459 : Blo 614296 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B2080403 : Blo 614296 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B2080619 : Blo 614296 2080619 := bstep (se 1 (by rfl) ⟨1560464, by rfl⟩ : syracuseStep 2080619 = 3120929) B3120929
theorem B2965367 : Blo 614296 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B2080673 : Blo 614296 2080673 := bstep (se 2 (by rfl) ⟨780252, by rfl⟩ : syracuseStep 2080673 = 1560505) B1560505
theorem B2081267 : Blo 614296 2081267 := bstep (se 1 (by rfl) ⟨1560950, by rfl⟩ : syracuseStep 2081267 = 3121901) B3121901
theorem B2343613 : Blo 614296 2343613 := bstep (se 3 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 2343613 = 878855) B878855
theorem B2081807 : Blo 614296 2081807 := bstep (se 1 (by rfl) ⟨1561355, by rfl⟩ : syracuseStep 2081807 = 3122711) B3122711
theorem B902183 : Blo 614296 902183 := bstep (se 1 (by rfl) ⟨676637, by rfl⟩ : syracuseStep 902183 = 1353275) B1353275
theorem B1557751 : Blo 614296 1557751 := bstep (se 1 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 1557751 = 2336627) B2336627
theorem B1558025 : Blo 614296 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1558055 : Blo 614296 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B2082401 : Blo 614296 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B2967137 : Blo 614296 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B2344571 : Blo 614296 2344571 := bstep (se 1 (by rfl) ⟨1758428, by rfl⟩ : syracuseStep 2344571 = 3516857) B3516857
theorem B3753823 : Blo 614296 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B1558379 : Blo 614296 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B935975 : Blo 614296 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B7883041 : Blo 614296 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B2345345 : Blo 614296 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B12863897 : Blo 614296 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B1559027 : Blo 614296 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B2968427 : Blo 614296 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B2411371 : Blo 614296 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B4672403 : Blo 614296 4672403 := bstep (se 1 (by rfl) ⟨3504302, by rfl⟩ : syracuseStep 4672403 = 7008605) B7008605
theorem B1067951 : Blo 614296 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B1559483 : Blo 614296 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B2083859 : Blo 614296 2083859 := bstep (se 1 (by rfl) ⟨1562894, by rfl⟩ : syracuseStep 2083859 = 3125789) B3125789
theorem B1166393 : Blo 614296 1166393 := bstep (se 2 (by rfl) ⟨437397, by rfl⟩ : syracuseStep 1166393 = 874795) B874795
theorem B2084183 : Blo 614296 2084183 := bstep (se 1 (by rfl) ⟨1563137, by rfl⟩ : syracuseStep 2084183 = 3126275) B3126275
theorem B2674063 : Blo 614296 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B1330651 : Blo 614296 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B2346529 : Blo 614296 2346529 := bstep (se 2 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 2346529 = 1759897) B1759897
theorem B1560161 : Blo 614296 1560161 := bstep (se 2 (by rfl) ⟨585060, by rfl⟩ : syracuseStep 1560161 = 1170121) B1170121
theorem B4673375 : Blo 614296 4673375 := bstep (se 1 (by rfl) ⟨3505031, by rfl⟩ : syracuseStep 4673375 = 7010063) B7010063
theorem B5263289 : Blo 614296 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B2347015 : Blo 614296 2347015 := bstep (se 1 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 2347015 = 3520523) B3520523
theorem B5001533 : Blo 614296 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B1036651 : Blo 614296 1036651 := bstep (se 1 (by rfl) ⟨777488, by rfl⟩ : syracuseStep 1036651 = 1554977) B1554977
theorem B2085263 : Blo 614296 2085263 := bstep (se 1 (by rfl) ⟨1563947, by rfl⟩ : syracuseStep 2085263 = 3127895) B3127895
theorem B2347501 : Blo 614296 2347501 := bstep (se 3 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 2347501 = 880313) B880313
theorem B1167995 : Blo 614296 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B2085587 : Blo 614296 2085587 := bstep (se 1 (by rfl) ⟨1564190, by rfl⟩ : syracuseStep 2085587 = 3128381) B3128381
theorem B2216747 : Blo 614296 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B1561619 : Blo 614296 1561619 := bstep (se 1 (by rfl) ⟨1171214, by rfl⟩ : syracuseStep 1561619 = 2342429) B2342429
theorem B6673427 : Blo 614296 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B1168481 : Blo 614296 1168481 := bstep (se 2 (by rfl) ⟨438180, by rfl⟩ : syracuseStep 1168481 = 876361) B876361
theorem B2970827 : Blo 614296 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B1037711 : Blo 614296 1037711 := bstep (se 1 (by rfl) ⟨778283, by rfl⟩ : syracuseStep 1037711 = 1556567) B1556567
theorem B1168823 : Blo 614296 1168823 := bstep (se 1 (by rfl) ⟨876617, by rfl⟩ : syracuseStep 1168823 = 1753235) B1753235
theorem B1562075 : Blo 614296 1562075 := bstep (se 1 (by rfl) ⟨1171556, by rfl⟩ : syracuseStep 1562075 = 2343113) B2343113
theorem B1037947 : Blo 614296 1037947 := bstep (se 1 (by rfl) ⟨778460, by rfl⟩ : syracuseStep 1037947 = 1556921) B1556921
theorem B16864949 : Blo 614296 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B3954491 : Blo 614296 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B1169225 : Blo 614296 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B3954541 : Blo 614296 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B8869925 : Blo 614296 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B4446667 : Blo 614296 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B1038811 : Blo 614296 1038811 := bstep (se 1 (by rfl) ⟨779108, by rfl⟩ : syracuseStep 1038811 = 1558217) B1558217
theorem B1169939 : Blo 614296 1169939 := bstep (se 1 (by rfl) ⟨877454, by rfl⟩ : syracuseStep 1169939 = 1754909) B1754909
theorem B1169977 : Blo 614296 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B23943755 : Blo 614296 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B1333883 : Blo 614296 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B1563259 : Blo 614296 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B1759943 : Blo 614296 1759943 := bstep (se 1 (by rfl) ⟨1319957, by rfl⟩ : syracuseStep 1759943 = 2639915) B2639915
theorem B1170281 : Blo 614296 1170281 := bstep (se 2 (by rfl) ⟨438855, by rfl⟩ : syracuseStep 1170281 = 877711) B877711
theorem B1661879 : Blo 614296 1661879 := bstep (se 1 (by rfl) ⟨1246409, by rfl⟩ : syracuseStep 1661879 = 2492819) B2492819
theorem B1039439 : Blo 614296 1039439 := bstep (se 1 (by rfl) ⟨779579, by rfl⟩ : syracuseStep 1039439 = 1559159) B1559159
theorem B8871191 : Blo 614296 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B48717233 : Blo 614296 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B777691 : Blo 614296 777691 := bstep (se 1 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 777691 = 1166537) B1166537
theorem B79716149 : Blo 614296 79716149 := bstep (se 5 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 79716149 = 7473389) B7473389
theorem B614319 : Blo 614296 614319 := bstep (se 1 (by rfl) ⟨460739, by rfl⟩ : syracuseStep 614319 = 921479) B921479
theorem B1040303 : Blo 614296 1040303 := bstep (se 1 (by rfl) ⟨780227, by rfl⟩ : syracuseStep 1040303 = 1560455) B1560455
theorem B614343 : Blo 614296 614343 := bstep (se 1 (by rfl) ⟨460757, by rfl⟩ : syracuseStep 614343 = 921515) B921515
theorem B614363 : Blo 614296 614363 := bstep (se 1 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 614363 = 921545) B921545
theorem B614439 : Blo 614296 614439 := bstep (se 1 (by rfl) ⟨460829, by rfl⟩ : syracuseStep 614439 = 921659) B921659
theorem B614479 : Blo 614296 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B614495 : Blo 614296 614495 := bstep (se 1 (by rfl) ⟨460871, by rfl⟩ : syracuseStep 614495 = 921743) B921743
theorem B614523 : Blo 614296 614523 := bstep (se 1 (by rfl) ⟨460892, by rfl⟩ : syracuseStep 614523 = 921785) B921785
theorem B1171579 : Blo 614296 1171579 := bstep (se 1 (by rfl) ⟨878684, by rfl⟩ : syracuseStep 1171579 = 1757369) B1757369
theorem B614575 : Blo 614296 614575 := bstep (se 1 (by rfl) ⟨460931, by rfl⟩ : syracuseStep 614575 = 921863) B921863
theorem B614599 : Blo 614296 614599 := bstep (se 1 (by rfl) ⟨460949, by rfl⟩ : syracuseStep 614599 = 921899) B921899
theorem B1171655 : Blo 614296 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B614619 : Blo 614296 614619 := bstep (se 1 (by rfl) ⟨460964, by rfl⟩ : syracuseStep 614619 = 921929) B921929
theorem B4448513 : Blo 614296 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B614695 : Blo 614296 614695 := bstep (se 1 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 614695 = 922043) B922043
theorem B614735 : Blo 614296 614735 := bstep (se 1 (by rfl) ⟨461051, by rfl⟩ : syracuseStep 614735 = 922103) B922103
theorem B614751 : Blo 614296 614751 := bstep (se 1 (by rfl) ⟨461063, by rfl⟩ : syracuseStep 614751 = 922127) B922127
theorem B1040735 : Blo 614296 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B614779 : Blo 614296 614779 := bstep (se 1 (by rfl) ⟨461084, by rfl⟩ : syracuseStep 614779 = 922169) B922169
theorem B614831 : Blo 614296 614831 := bstep (se 1 (by rfl) ⟨461123, by rfl⟩ : syracuseStep 614831 = 922247) B922247
theorem B614855 : Blo 614296 614855 := bstep (se 1 (by rfl) ⟨461141, by rfl⟩ : syracuseStep 614855 = 922283) B922283
theorem B614875 : Blo 614296 614875 := bstep (se 1 (by rfl) ⟨461156, by rfl⟩ : syracuseStep 614875 = 922313) B922313
theorem B614951 : Blo 614296 614951 := bstep (se 1 (by rfl) ⟨461213, by rfl⟩ : syracuseStep 614951 = 922427) B922427
theorem B614991 : Blo 614296 614991 := bstep (se 1 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 614991 = 922487) B922487
theorem B615007 : Blo 614296 615007 := bstep (se 1 (by rfl) ⟨461255, by rfl⟩ : syracuseStep 615007 = 922511) B922511
theorem B1172065 : Blo 614296 1172065 := bstep (se 2 (by rfl) ⟨439524, by rfl⟩ : syracuseStep 1172065 = 879049) B879049
theorem B615035 : Blo 614296 615035 := bstep (se 1 (by rfl) ⟨461276, by rfl⟩ : syracuseStep 615035 = 922553) B922553
theorem B615087 : Blo 614296 615087 := bstep (se 1 (by rfl) ⟨461315, by rfl⟩ : syracuseStep 615087 = 922631) B922631
theorem B615111 : Blo 614296 615111 := bstep (se 1 (by rfl) ⟨461333, by rfl⟩ : syracuseStep 615111 = 922667) B922667
theorem B10019537 : Blo 614296 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B615131 : Blo 614296 615131 := bstep (se 1 (by rfl) ⟨461348, by rfl⟩ : syracuseStep 615131 = 922697) B922697
theorem B615207 : Blo 614296 615207 := bstep (se 1 (by rfl) ⟨461405, by rfl⟩ : syracuseStep 615207 = 922811) B922811
theorem B615247 : Blo 614296 615247 := bstep (se 1 (by rfl) ⟨461435, by rfl⟩ : syracuseStep 615247 = 922871) B922871
theorem B615263 : Blo 614296 615263 := bstep (se 1 (by rfl) ⟨461447, by rfl⟩ : syracuseStep 615263 = 922895) B922895
theorem B615291 : Blo 614296 615291 := bstep (se 1 (by rfl) ⟨461468, by rfl⟩ : syracuseStep 615291 = 922937) B922937
theorem B1041295 : Blo 614296 1041295 := bstep (se 1 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 1041295 = 1561943) B1561943
theorem B615343 : Blo 614296 615343 := bstep (se 1 (by rfl) ⟨461507, by rfl⟩ : syracuseStep 615343 = 923015) B923015
theorem B1172407 : Blo 614296 1172407 := bstep (se 1 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 1172407 = 1758611) B1758611
theorem B615367 : Blo 614296 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B615387 : Blo 614296 615387 := bstep (se 1 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 615387 = 923081) B923081
theorem B78996491 : Blo 614296 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B615463 : Blo 614296 615463 := bstep (se 1 (by rfl) ⟨461597, by rfl⟩ : syracuseStep 615463 = 923195) B923195
theorem B615503 : Blo 614296 615503 := bstep (se 1 (by rfl) ⟨461627, by rfl⟩ : syracuseStep 615503 = 923255) B923255
theorem B615519 : Blo 614296 615519 := bstep (se 1 (by rfl) ⟨461639, by rfl⟩ : syracuseStep 615519 = 923279) B923279
theorem B615547 : Blo 614296 615547 := bstep (se 1 (by rfl) ⟨461660, by rfl⟩ : syracuseStep 615547 = 923321) B923321
theorem B615599 : Blo 614296 615599 := bstep (se 1 (by rfl) ⟨461699, by rfl⟩ : syracuseStep 615599 = 923399) B923399
theorem B615623 : Blo 614296 615623 := bstep (se 1 (by rfl) ⟨461717, by rfl⟩ : syracuseStep 615623 = 923435) B923435
theorem B615643 : Blo 614296 615643 := bstep (se 1 (by rfl) ⟨461732, by rfl⟩ : syracuseStep 615643 = 923465) B923465
theorem B615719 : Blo 614296 615719 := bstep (se 1 (by rfl) ⟨461789, by rfl⟩ : syracuseStep 615719 = 923579) B923579
theorem B1172809 : Blo 614296 1172809 := bstep (se 2 (by rfl) ⟨439803, by rfl⟩ : syracuseStep 1172809 = 879607) B879607
theorem B615759 : Blo 614296 615759 := bstep (se 1 (by rfl) ⟨461819, by rfl⟩ : syracuseStep 615759 = 923639) B923639
theorem B3958105 : Blo 614296 3958105 := bstep (se 2 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 3958105 = 2968579) B2968579
theorem B615775 : Blo 614296 615775 := bstep (se 1 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 615775 = 923663) B923663
theorem B615803 : Blo 614296 615803 := bstep (se 1 (by rfl) ⟨461852, by rfl⟩ : syracuseStep 615803 = 923705) B923705
theorem B615855 : Blo 614296 615855 := bstep (se 1 (by rfl) ⟨461891, by rfl⟩ : syracuseStep 615855 = 923783) B923783
theorem B615879 : Blo 614296 615879 := bstep (se 1 (by rfl) ⟨461909, by rfl⟩ : syracuseStep 615879 = 923819) B923819
theorem B13297097 : Blo 614296 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B615899 : Blo 614296 615899 := bstep (se 1 (by rfl) ⟨461924, by rfl⟩ : syracuseStep 615899 = 923849) B923849
theorem B615975 : Blo 614296 615975 := bstep (se 1 (by rfl) ⟨461981, by rfl⟩ : syracuseStep 615975 = 923963) B923963
theorem B4679207 : Blo 614296 4679207 := bstep (se 1 (by rfl) ⟨3509405, by rfl⟩ : syracuseStep 4679207 = 7018811) B7018811
theorem B1041977 : Blo 614296 1041977 := bstep (se 2 (by rfl) ⟨390741, by rfl⟩ : syracuseStep 1041977 = 781483) B781483
theorem B616015 : Blo 614296 616015 := bstep (se 1 (by rfl) ⟨462011, by rfl⟩ : syracuseStep 616015 = 924023) B924023
theorem B616031 : Blo 614296 616031 := bstep (se 1 (by rfl) ⟨462023, by rfl⟩ : syracuseStep 616031 = 924047) B924047
theorem B616059 : Blo 614296 616059 := bstep (se 1 (by rfl) ⟨462044, by rfl⟩ : syracuseStep 616059 = 924089) B924089
theorem B616111 : Blo 614296 616111 := bstep (se 1 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 616111 = 924167) B924167
theorem B616135 : Blo 614296 616135 := bstep (se 1 (by rfl) ⟨462101, by rfl⟩ : syracuseStep 616135 = 924203) B924203
theorem B616155 : Blo 614296 616155 := bstep (se 1 (by rfl) ⟨462116, by rfl⟩ : syracuseStep 616155 = 924233) B924233
theorem B616231 : Blo 614296 616231 := bstep (se 1 (by rfl) ⟨462173, by rfl⟩ : syracuseStep 616231 = 924347) B924347
theorem B616271 : Blo 614296 616271 := bstep (se 1 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 616271 = 924407) B924407
theorem B20309849 : Blo 614296 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B616287 : Blo 614296 616287 := bstep (se 1 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 616287 = 924431) B924431
theorem B616315 : Blo 614296 616315 := bstep (se 1 (by rfl) ⟨462236, by rfl⟩ : syracuseStep 616315 = 924473) B924473
theorem B616367 : Blo 614296 616367 := bstep (se 1 (by rfl) ⟨462275, by rfl⟩ : syracuseStep 616367 = 924551) B924551
theorem B616391 : Blo 614296 616391 := bstep (se 1 (by rfl) ⟨462293, by rfl⟩ : syracuseStep 616391 = 924587) B924587
theorem B616411 : Blo 614296 616411 := bstep (se 1 (by rfl) ⟨462308, by rfl⟩ : syracuseStep 616411 = 924617) B924617
theorem B2222095 : Blo 614296 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B1173523 : Blo 614296 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B616487 : Blo 614296 616487 := bstep (se 1 (by rfl) ⟨462365, by rfl⟩ : syracuseStep 616487 = 924731) B924731
theorem B616527 : Blo 614296 616527 := bstep (se 1 (by rfl) ⟨462395, by rfl⟩ : syracuseStep 616527 = 924791) B924791
theorem B616543 : Blo 614296 616543 := bstep (se 1 (by rfl) ⟨462407, by rfl⟩ : syracuseStep 616543 = 924815) B924815
theorem B616571 : Blo 614296 616571 := bstep (se 1 (by rfl) ⟨462428, by rfl⟩ : syracuseStep 616571 = 924857) B924857
theorem B1501355 : Blo 614296 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B616623 : Blo 614296 616623 := bstep (se 1 (by rfl) ⟨462467, by rfl⟩ : syracuseStep 616623 = 924935) B924935
theorem B616647 : Blo 614296 616647 := bstep (se 1 (by rfl) ⟨462485, by rfl⟩ : syracuseStep 616647 = 924971) B924971
theorem B616667 : Blo 614296 616667 := bstep (se 1 (by rfl) ⟨462500, by rfl⟩ : syracuseStep 616667 = 925001) B925001
theorem B1042679 : Blo 614296 1042679 := bstep (se 1 (by rfl) ⟨782009, by rfl⟩ : syracuseStep 1042679 = 1564019) B1564019
theorem B616743 : Blo 614296 616743 := bstep (se 1 (by rfl) ⟨462557, by rfl⟩ : syracuseStep 616743 = 925115) B925115
theorem B616783 : Blo 614296 616783 := bstep (se 1 (by rfl) ⟨462587, by rfl⟩ : syracuseStep 616783 = 925175) B925175
theorem B616799 : Blo 614296 616799 := bstep (se 1 (by rfl) ⟨462599, by rfl⟩ : syracuseStep 616799 = 925199) B925199
theorem B616827 : Blo 614296 616827 := bstep (se 1 (by rfl) ⟨462620, by rfl⟩ : syracuseStep 616827 = 925241) B925241
theorem B616879 : Blo 614296 616879 := bstep (se 1 (by rfl) ⟨462659, by rfl⟩ : syracuseStep 616879 = 925319) B925319
theorem B616903 : Blo 614296 616903 := bstep (se 1 (by rfl) ⟨462677, by rfl⟩ : syracuseStep 616903 = 925355) B925355
theorem B616923 : Blo 614296 616923 := bstep (se 1 (by rfl) ⟨462692, by rfl⟩ : syracuseStep 616923 = 925385) B925385
theorem B616999 : Blo 614296 616999 := bstep (se 1 (by rfl) ⟨462749, by rfl⟩ : syracuseStep 616999 = 925499) B925499
theorem B617039 : Blo 614296 617039 := bstep (se 1 (by rfl) ⟨462779, by rfl⟩ : syracuseStep 617039 = 925559) B925559
theorem B1043023 : Blo 614296 1043023 := bstep (se 1 (by rfl) ⟨782267, by rfl⟩ : syracuseStep 1043023 = 1564535) B1564535
theorem B617055 : Blo 614296 617055 := bstep (se 1 (by rfl) ⟨462791, by rfl⟩ : syracuseStep 617055 = 925583) B925583
theorem B617083 : Blo 614296 617083 := bstep (se 1 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 617083 = 925625) B925625
theorem B617135 : Blo 614296 617135 := bstep (se 1 (by rfl) ⟨462851, by rfl⟩ : syracuseStep 617135 = 925703) B925703
theorem B617159 : Blo 614296 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B617179 : Blo 614296 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B617255 : Blo 614296 617255 := bstep (se 1 (by rfl) ⟨462941, by rfl⟩ : syracuseStep 617255 = 925883) B925883
theorem B1043273 : Blo 614296 1043273 := bstep (se 2 (by rfl) ⟨391227, by rfl⟩ : syracuseStep 1043273 = 782455) B782455
theorem B617295 : Blo 614296 617295 := bstep (se 1 (by rfl) ⟨462971, by rfl⟩ : syracuseStep 617295 = 925943) B925943
theorem B617311 : Blo 614296 617311 := bstep (se 1 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 617311 = 925967) B925967
theorem B617339 : Blo 614296 617339 := bstep (se 1 (by rfl) ⟨463004, by rfl⟩ : syracuseStep 617339 = 926009) B926009
theorem B617391 : Blo 614296 617391 := bstep (se 1 (by rfl) ⟨463043, by rfl⟩ : syracuseStep 617391 = 926087) B926087
theorem B617415 : Blo 614296 617415 := bstep (se 1 (by rfl) ⟨463061, by rfl⟩ : syracuseStep 617415 = 926123) B926123
theorem B617435 : Blo 614296 617435 := bstep (se 1 (by rfl) ⟨463076, by rfl⟩ : syracuseStep 617435 = 926153) B926153
theorem B617511 : Blo 614296 617511 := bstep (se 1 (by rfl) ⟨463133, by rfl⟩ : syracuseStep 617511 = 926267) B926267
theorem B617551 : Blo 614296 617551 := bstep (se 1 (by rfl) ⟨463163, by rfl⟩ : syracuseStep 617551 = 926327) B926327
theorem B617567 : Blo 614296 617567 := bstep (se 1 (by rfl) ⟨463175, by rfl⟩ : syracuseStep 617567 = 926351) B926351
theorem B617595 : Blo 614296 617595 := bstep (se 1 (by rfl) ⟨463196, by rfl⟩ : syracuseStep 617595 = 926393) B926393
theorem B617647 : Blo 614296 617647 := bstep (se 1 (by rfl) ⟨463235, by rfl⟩ : syracuseStep 617647 = 926471) B926471
theorem B3501251 : Blo 614296 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B617671 : Blo 614296 617671 := bstep (se 1 (by rfl) ⟨463253, by rfl⟩ : syracuseStep 617671 = 926507) B926507
theorem B617691 : Blo 614296 617691 := bstep (se 1 (by rfl) ⟨463268, by rfl⟩ : syracuseStep 617691 = 926537) B926537
theorem B617767 : Blo 614296 617767 := bstep (se 1 (by rfl) ⟨463325, by rfl⟩ : syracuseStep 617767 = 926651) B926651
theorem B617807 : Blo 614296 617807 := bstep (se 1 (by rfl) ⟨463355, by rfl⟩ : syracuseStep 617807 = 926711) B926711
theorem B617823 : Blo 614296 617823 := bstep (se 1 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 617823 = 926735) B926735
theorem B617851 : Blo 614296 617851 := bstep (se 1 (by rfl) ⟨463388, by rfl⟩ : syracuseStep 617851 = 926777) B926777
theorem B5074319 : Blo 614296 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B617903 : Blo 614296 617903 := bstep (se 1 (by rfl) ⟨463427, by rfl⟩ : syracuseStep 617903 = 926855) B926855
theorem B781751 : Blo 614296 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B617927 : Blo 614296 617927 := bstep (se 1 (by rfl) ⟨463445, by rfl⟩ : syracuseStep 617927 = 926891) B926891
theorem B617947 : Blo 614296 617947 := bstep (se 1 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 617947 = 926921) B926921
theorem B618023 : Blo 614296 618023 := bstep (se 1 (by rfl) ⟨463517, by rfl⟩ : syracuseStep 618023 = 927035) B927035
theorem B8449601 : Blo 614296 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B781903 : Blo 614296 781903 := bstep (se 1 (by rfl) ⟨586427, by rfl⟩ : syracuseStep 781903 = 1172855) B1172855
theorem B618063 : Blo 614296 618063 := bstep (se 1 (by rfl) ⟨463547, by rfl⟩ : syracuseStep 618063 = 927095) B927095
theorem B618079 : Blo 614296 618079 := bstep (se 1 (by rfl) ⟨463559, by rfl⟩ : syracuseStep 618079 = 927119) B927119
theorem B618107 : Blo 614296 618107 := bstep (se 1 (by rfl) ⟨463580, by rfl⟩ : syracuseStep 618107 = 927161) B927161
theorem B3010193 : Blo 614296 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B618159 : Blo 614296 618159 := bstep (se 1 (by rfl) ⟨463619, by rfl⟩ : syracuseStep 618159 = 927239) B927239
theorem B618183 : Blo 614296 618183 := bstep (se 1 (by rfl) ⟨463637, by rfl⟩ : syracuseStep 618183 = 927275) B927275
theorem B618203 : Blo 614296 618203 := bstep (se 1 (by rfl) ⟨463652, by rfl⟩ : syracuseStep 618203 = 927305) B927305
theorem B618279 : Blo 614296 618279 := bstep (se 1 (by rfl) ⟨463709, by rfl⟩ : syracuseStep 618279 = 927419) B927419
theorem B4550593 : Blo 614296 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B45674675 : Blo 614296 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B2257091 : Blo 614296 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B22475069 : Blo 614296 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B4223927 : Blo 614296 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B1111163 : Blo 614296 1111163 := bstep (se 1 (by rfl) ⟨833372, by rfl⟩ : syracuseStep 1111163 = 1666745) B1666745
theorem B5273099 : Blo 614296 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B1668647 : Blo 614296 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B1406663 : Blo 614296 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B3110723 : Blo 614296 3110723 := bstep (se 1 (by rfl) ⟨2333042, by rfl⟩ : syracuseStep 3110723 = 4666085) B4666085
theorem B1112071 : Blo 614296 1112071 := bstep (se 1 (by rfl) ⟨834053, by rfl⟩ : syracuseStep 1112071 = 1668107) B1668107
theorem B1669481 : Blo 614296 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B4225517 : Blo 614296 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B1407851 : Blo 614296 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B7011521 : Blo 614296 7011521 := bstep (se 2 (by rfl) ⟨2629320, by rfl⟩ : syracuseStep 7011521 = 5258641) B5258641
theorem B1113679 : Blo 614296 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B5604173 : Blo 614296 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B984811 : Blo 614296 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B5277473 : Blo 614296 5277473 := bstep (se 2 (by rfl) ⟨1979052, by rfl⟩ : syracuseStep 5277473 = 3958105) B3958105
theorem B7997251 : Blo 614296 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B3114935 : Blo 614296 3114935 := bstep (se 1 (by rfl) ⟨2336201, by rfl⟩ : syracuseStep 3114935 = 4672403) B4672403
theorem B3115583 : Blo 614296 3115583 := bstep (se 1 (by rfl) ⟨2336687, by rfl⟩ : syracuseStep 3115583 = 4673375) B4673375
theorem B3508859 : Blo 614296 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B1182863 : Blo 614296 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B2886943 : Blo 614296 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1052041 : Blo 614296 1052041 := bstep (se 2 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 1052041 = 789031) B789031
theorem B2625119 : Blo 614296 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B691807 : Blo 614296 691807 := bstep (se 1 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 691807 = 1037711) B1037711
theorem B1052255 : Blo 614296 1052255 := bstep (se 1 (by rfl) ⟨789191, by rfl⟩ : syracuseStep 1052255 = 1578383) B1578383
theorem B11243299 : Blo 614296 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B3215161 : Blo 614296 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B921551 : Blo 614296 921551 := bstep (se 1 (by rfl) ⟨691163, by rfl⟩ : syracuseStep 921551 = 1382327) B1382327
theorem B921947 : Blo 614296 921947 := bstep (se 1 (by rfl) ⟨691460, by rfl⟩ : syracuseStep 921947 = 1382921) B1382921
theorem B15962503 : Blo 614296 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B889255 : Blo 614296 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B922175 : Blo 614296 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B3117689 : Blo 614296 3117689 := bstep (se 2 (by rfl) ⟨1169133, by rfl⟩ : syracuseStep 3117689 = 2338267) B2338267
theorem B922295 : Blo 614296 922295 := bstep (se 1 (by rfl) ⟨691721, by rfl⟩ : syracuseStep 922295 = 1383443) B1383443
theorem B692959 : Blo 614296 692959 := bstep (se 1 (by rfl) ⟨519719, by rfl⟩ : syracuseStep 692959 = 1039439) B1039439
theorem B922523 : Blo 614296 922523 := bstep (se 1 (by rfl) ⟨691892, by rfl⟩ : syracuseStep 922523 = 1383785) B1383785
theorem B32478155 : Blo 614296 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B2626793 : Blo 614296 2626793 := bstep (se 2 (by rfl) ⟨985047, by rfl⟩ : syracuseStep 2626793 = 1970095) B1970095
theorem B6067457 : Blo 614296 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B693535 : Blo 614296 693535 := bstep (se 1 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 693535 = 1040303) B1040303
theorem B922919 : Blo 614296 922919 := bstep (se 1 (by rfl) ⟨692189, by rfl⟩ : syracuseStep 922919 = 1384379) B1384379
theorem B923003 : Blo 614296 923003 := bstep (se 1 (by rfl) ⟨692252, by rfl⟩ : syracuseStep 923003 = 1384505) B1384505
theorem B2495933 : Blo 614296 2495933 := bstep (se 3 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 2495933 = 935975) B935975
theorem B923129 : Blo 614296 923129 := bstep (se 2 (by rfl) ⟨346173, by rfl⟩ : syracuseStep 923129 = 692347) B692347
theorem B693823 : Blo 614296 693823 := bstep (se 1 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 693823 = 1040735) B1040735
theorem B923231 : Blo 614296 923231 := bstep (se 1 (by rfl) ⟨692423, by rfl⟩ : syracuseStep 923231 = 1384847) B1384847
theorem B4003613 : Blo 614296 4003613 := bstep (se 3 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 4003613 = 1501355) B1501355
theorem B923447 : Blo 614296 923447 := bstep (se 1 (by rfl) ⟨692585, by rfl⟩ : syracuseStep 923447 = 1385171) B1385171
theorem B1382201 : Blo 614296 1382201 := bstep (se 2 (by rfl) ⟨518325, by rfl⟩ : syracuseStep 1382201 = 1036651) B1036651
theorem B52664327 : Blo 614296 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B923753 : Blo 614296 923753 := bstep (se 2 (by rfl) ⟨346407, by rfl⟩ : syracuseStep 923753 = 692815) B692815
theorem B2103425 : Blo 614296 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B3119471 : Blo 614296 3119471 := bstep (se 1 (by rfl) ⟨2339603, by rfl⟩ : syracuseStep 3119471 = 4679207) B4679207
theorem B694651 : Blo 614296 694651 := bstep (se 1 (by rfl) ⟨520988, by rfl⟩ : syracuseStep 694651 = 1041977) B1041977
theorem B924071 : Blo 614296 924071 := bstep (se 1 (by rfl) ⟨693053, by rfl⟩ : syracuseStep 924071 = 1386107) B1386107
theorem B1382831 : Blo 614296 1382831 := bstep (se 1 (by rfl) ⟨1037123, by rfl⟩ : syracuseStep 1382831 = 2074247) B2074247
theorem B1382867 : Blo 614296 1382867 := bstep (se 1 (by rfl) ⟨1037150, by rfl⟩ : syracuseStep 1382867 = 2074301) B2074301
theorem B924155 : Blo 614296 924155 := bstep (se 1 (by rfl) ⟨693116, by rfl⟩ : syracuseStep 924155 = 1386233) B1386233
theorem B13539899 : Blo 614296 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B1382975 : Blo 614296 1382975 := bstep (se 1 (by rfl) ⟨1037231, by rfl⟩ : syracuseStep 1382975 = 2074463) B2074463
theorem B1317455 : Blo 614296 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B924281 : Blo 614296 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B1383083 : Blo 614296 1383083 := bstep (se 1 (by rfl) ⟨1037312, by rfl⟩ : syracuseStep 1383083 = 2074625) B2074625
theorem B924335 : Blo 614296 924335 := bstep (se 1 (by rfl) ⟨693251, by rfl⟩ : syracuseStep 924335 = 1386503) B1386503
theorem B924383 : Blo 614296 924383 := bstep (se 1 (by rfl) ⟨693287, by rfl⟩ : syracuseStep 924383 = 1386575) B1386575
theorem B695119 : Blo 614296 695119 := bstep (se 1 (by rfl) ⟨521339, by rfl⟩ : syracuseStep 695119 = 1042679) B1042679
theorem B924647 : Blo 614296 924647 := bstep (se 1 (by rfl) ⟨693485, by rfl⟩ : syracuseStep 924647 = 1386971) B1386971
theorem B5250167 : Blo 614296 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B1383623 : Blo 614296 1383623 := bstep (se 1 (by rfl) ⟨1037717, by rfl⟩ : syracuseStep 1383623 = 2075435) B2075435
theorem B695515 : Blo 614296 695515 := bstep (se 1 (by rfl) ⟨521636, by rfl⟩ : syracuseStep 695515 = 1043273) B1043273
theorem B924905 : Blo 614296 924905 := bstep (se 2 (by rfl) ⟨346839, by rfl⟩ : syracuseStep 924905 = 693679) B693679
theorem B2628895 : Blo 614296 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B924959 : Blo 614296 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B1383803 : Blo 614296 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B4988297 : Blo 614296 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B925127 : Blo 614296 925127 := bstep (se 1 (by rfl) ⟨693845, by rfl⟩ : syracuseStep 925127 = 1387691) B1387691
theorem B2334167 : Blo 614296 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1383929 : Blo 614296 1383929 := bstep (se 2 (by rfl) ⟨518973, by rfl⟩ : syracuseStep 1383929 = 1037947) B1037947
theorem B5905979 : Blo 614296 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B1384019 : Blo 614296 1384019 := bstep (se 1 (by rfl) ⟨1038014, by rfl⟩ : syracuseStep 1384019 = 2076029) B2076029
theorem B3382879 : Blo 614296 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B1384199 : Blo 614296 1384199 := bstep (se 1 (by rfl) ⟨1038149, by rfl⟩ : syracuseStep 1384199 = 2076299) B2076299
theorem B2006795 : Blo 614296 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B925481 : Blo 614296 925481 := bstep (se 2 (by rfl) ⟨347055, by rfl⟩ : syracuseStep 925481 = 694111) B694111
theorem B925487 : Blo 614296 925487 := bstep (se 1 (by rfl) ⟨694115, by rfl⟩ : syracuseStep 925487 = 1388231) B1388231
theorem B1482761 : Blo 614296 1482761 := bstep (se 2 (by rfl) ⟨556035, by rfl⟩ : syracuseStep 1482761 = 1112071) B1112071
theorem B9969713 : Blo 614296 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B30449783 : Blo 614296 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B14983379 : Blo 614296 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B925961 : Blo 614296 925961 := bstep (se 2 (by rfl) ⟨347235, by rfl⟩ : syracuseStep 925961 = 694471) B694471
theorem B1384811 : Blo 614296 1384811 := bstep (se 1 (by rfl) ⟨1038608, by rfl⟩ : syracuseStep 1384811 = 2077217) B2077217
theorem B926063 : Blo 614296 926063 := bstep (se 1 (by rfl) ⟨694547, by rfl⟩ : syracuseStep 926063 = 1389095) B1389095
theorem B1384955 : Blo 614296 1384955 := bstep (se 1 (by rfl) ⟨1038716, by rfl⟩ : syracuseStep 1384955 = 2077433) B2077433
theorem B926279 : Blo 614296 926279 := bstep (se 1 (by rfl) ⟨694709, by rfl⟩ : syracuseStep 926279 = 1389419) B1389419
theorem B926315 : Blo 614296 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B1385081 : Blo 614296 1385081 := bstep (se 2 (by rfl) ⟨519405, by rfl⟩ : syracuseStep 1385081 = 1038811) B1038811
theorem B1385135 : Blo 614296 1385135 := bstep (se 1 (by rfl) ⟨1038851, by rfl⟩ : syracuseStep 1385135 = 2077703) B2077703
theorem B1385207 : Blo 614296 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B42738445 : Blo 614296 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B926543 : Blo 614296 926543 := bstep (se 1 (by rfl) ⟨694907, by rfl⟩ : syracuseStep 926543 = 1389815) B1389815
theorem B1385387 : Blo 614296 1385387 := bstep (se 1 (by rfl) ⟨1039040, by rfl⟩ : syracuseStep 1385387 = 2078081) B2078081
theorem B2073545 : Blo 614296 2073545 := bstep (se 2 (by rfl) ⟨777579, by rfl⟩ : syracuseStep 2073545 = 1555159) B1555159
theorem B1975271 : Blo 614296 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B3515399 : Blo 614296 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B2499731 : Blo 614296 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B2073815 : Blo 614296 2073815 := bstep (se 1 (by rfl) ⟨1555361, by rfl⟩ : syracuseStep 2073815 = 3110723) B3110723
theorem B926939 : Blo 614296 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B1975529 : Blo 614296 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B927113 : Blo 614296 927113 := bstep (se 2 (by rfl) ⟨347667, by rfl⟩ : syracuseStep 927113 = 695335) B695335
theorem B26682767 : Blo 614296 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B1385927 : Blo 614296 1385927 := bstep (se 1 (by rfl) ⟨1039445, by rfl⟩ : syracuseStep 1385927 = 2078891) B2078891
theorem B3122873 : Blo 614296 3122873 := bstep (se 2 (by rfl) ⟨1171077, by rfl⟩ : syracuseStep 3122873 = 2342155) B2342155
theorem B1386287 : Blo 614296 1386287 := bstep (se 1 (by rfl) ⟨1039715, by rfl⟩ : syracuseStep 1386287 = 2079431) B2079431
theorem B4990825 : Blo 614296 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B12167117 : Blo 614296 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B1484905 : Blo 614296 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B7907645 : Blo 614296 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B1386863 : Blo 614296 1386863 := bstep (se 1 (by rfl) ⟨1040147, by rfl⟩ : syracuseStep 1386863 = 2080295) B2080295
theorem B1386935 : Blo 614296 1386935 := bstep (se 1 (by rfl) ⟨1040201, by rfl⟩ : syracuseStep 1386935 = 2080403) B2080403
theorem B1387079 : Blo 614296 1387079 := bstep (se 1 (by rfl) ⟨1040309, by rfl⟩ : syracuseStep 1387079 = 2080619) B2080619
theorem B1387115 : Blo 614296 1387115 := bstep (se 1 (by rfl) ⟨1040336, by rfl⟩ : syracuseStep 1387115 = 2080673) B2080673
theorem B1387511 : Blo 614296 1387511 := bstep (se 1 (by rfl) ⟨1040633, by rfl⟩ : syracuseStep 1387511 = 2081267) B2081267
theorem B2075867 : Blo 614296 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B1387871 : Blo 614296 1387871 := bstep (se 1 (by rfl) ⟨1040903, by rfl⟩ : syracuseStep 1387871 = 2081807) B2081807
theorem B3124817 : Blo 614296 3124817 := bstep (se 2 (by rfl) ⟨1171806, by rfl⟩ : syracuseStep 3124817 = 2343613) B2343613
theorem B1388267 : Blo 614296 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B1978091 : Blo 614296 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B2338571 : Blo 614296 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B3321661 : Blo 614296 3321661 := bstep (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) B1245623
theorem B1388393 : Blo 614296 1388393 := bstep (se 2 (by rfl) ⟨520647, by rfl⟩ : syracuseStep 1388393 = 1041295) B1041295
theorem B5255225 : Blo 614296 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B2076731 : Blo 614296 2076731 := bstep (se 1 (by rfl) ⟨1557548, by rfl⟩ : syracuseStep 2076731 = 3115097) B3115097
theorem B2339027 : Blo 614296 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B2077001 : Blo 614296 2077001 := bstep (se 2 (by rfl) ⟨778875, by rfl⟩ : syracuseStep 2077001 = 1557751) B1557751
theorem B1978951 : Blo 614296 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B1389239 : Blo 614296 1389239 := bstep (se 1 (by rfl) ⟨1041929, by rfl⟩ : syracuseStep 1389239 = 2083859) B2083859
theorem B5911325 : Blo 614296 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B5485391 : Blo 614296 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1389455 : Blo 614296 1389455 := bstep (se 1 (by rfl) ⟨1042091, by rfl⟩ : syracuseStep 1389455 = 2084183) B2084183
theorem B2962793 : Blo 614296 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B2405821 : Blo 614296 2405821 := bstep (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) B902183
theorem B1750535 : Blo 614296 1750535 := bstep (se 1 (by rfl) ⟨1312901, by rfl⟩ : syracuseStep 1750535 = 2625803) B2625803
theorem B1390175 : Blo 614296 1390175 := bstep (se 1 (by rfl) ⟨1042631, by rfl⟩ : syracuseStep 1390175 = 2085263) B2085263
theorem B2963101 : Blo 614296 2963101 := bstep (se 3 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 2963101 = 1111163) B1111163
theorem B3159737 : Blo 614296 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B6600503 : Blo 614296 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B1390391 : Blo 614296 1390391 := bstep (se 1 (by rfl) ⟨1042793, by rfl⟩ : syracuseStep 1390391 = 2085587) B2085587
theorem B3127247 : Blo 614296 3127247 := bstep (se 1 (by rfl) ⟨2345435, by rfl⟩ : syracuseStep 3127247 = 4690871) B4690871
theorem B1390697 : Blo 614296 1390697 := bstep (se 2 (by rfl) ⟨521511, by rfl⟩ : syracuseStep 1390697 = 1043023) B1043023
theorem B1980551 : Blo 614296 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1751321 : Blo 614296 1751321 := bstep (se 2 (by rfl) ⟨656745, by rfl⟩ : syracuseStep 1751321 = 1313491) B1313491
theorem B2636327 : Blo 614296 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B5913283 : Blo 614296 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B3128219 : Blo 614296 3128219 := bstep (se 1 (by rfl) ⟨2346164, by rfl⟩ : syracuseStep 3128219 = 4692329) B4692329
theorem B1555595 : Blo 614296 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B6732953 : Blo 614296 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B1555807 : Blo 614296 1555807 := bstep (se 1 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 1555807 = 2333711) B2333711
theorem B3325313 : Blo 614296 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B3128705 : Blo 614296 3128705 := bstep (se 2 (by rfl) ⟨1173264, by rfl⟩ : syracuseStep 3128705 = 2346529) B2346529
theorem B2080187 : Blo 614296 2080187 := bstep (se 1 (by rfl) ⟨1560140, by rfl⟩ : syracuseStep 2080187 = 3120281) B3120281
theorem B5914127 : Blo 614296 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B1752961 : Blo 614296 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B835535 : Blo 614296 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B3129353 : Blo 614296 3129353 := bstep (se 2 (by rfl) ⟨1173507, by rfl⟩ : syracuseStep 3129353 = 2347015) B2347015
theorem B2965675 : Blo 614296 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B3129515 : Blo 614296 3129515 := bstep (se 1 (by rfl) ⟨2347136, by rfl⟩ : syracuseStep 3129515 = 4694273) B4694273
theorem B1753451 : Blo 614296 1753451 := bstep (se 1 (by rfl) ⟨1315088, by rfl⟩ : syracuseStep 1753451 = 2630177) B2630177
theorem B32424583 : Blo 614296 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B3130001 : Blo 614296 3130001 := bstep (se 2 (by rfl) ⟨1173750, by rfl⟩ : syracuseStep 3130001 = 2347501) B2347501
theorem B5259977 : Blo 614296 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B1557215 : Blo 614296 1557215 := bstep (se 1 (by rfl) ⟨1167911, by rfl⟩ : syracuseStep 1557215 = 2335823) B2335823
theorem B8864731 : Blo 614296 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1754237 : Blo 614296 1754237 := bstep (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) B657839
theorem B17778365 : Blo 614296 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B3950441 : Blo 614296 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B10536965 : Blo 614296 10536965 := bstep (se 4 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 10536965 = 1975681) B1975681
theorem B4671917 : Blo 614296 4671917 := bstep (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) B1751969
theorem B7096805 : Blo 614296 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B1559675 : Blo 614296 1559675 := bstep (se 1 (by rfl) ⟨1169756, by rfl⟩ : syracuseStep 1559675 = 2339513) B2339513
theorem B1559695 : Blo 614296 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B1559969 : Blo 614296 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B2084345 : Blo 614296 2084345 := bstep (se 2 (by rfl) ⟨781629, by rfl⟩ : syracuseStep 2084345 = 1563259) B1563259
theorem B2674201 : Blo 614296 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B2084615 : Blo 614296 2084615 := bstep (se 1 (by rfl) ⟨1563461, by rfl⟩ : syracuseStep 2084615 = 3126923) B3126923
theorem B937775 : Blo 614296 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B2084669 : Blo 614296 2084669 := bstep (se 3 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 2084669 = 781751) B781751
theorem B1167311 : Blo 614296 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B1757209 : Blo 614296 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B22532269 : Blo 614296 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B938567 : Blo 614296 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B1036921 : Blo 614296 1036921 := bstep (se 2 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 1036921 = 777691) B777691
theorem B1036975 : Blo 614296 1036975 := bstep (se 1 (by rfl) ⟨777731, by rfl⟩ : syracuseStep 1036975 = 1555463) B1555463
theorem B4674347 : Blo 614296 4674347 := bstep (se 1 (by rfl) ⟨3505760, by rfl⟩ : syracuseStep 4674347 = 7011521) B7011521
theorem B1168283 : Blo 614296 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B1561639 : Blo 614296 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B1562105 : Blo 614296 1562105 := bstep (se 2 (by rfl) ⟨585789, by rfl⟩ : syracuseStep 1562105 = 1171579) B1171579
theorem B1562753 : Blo 614296 1562753 := bstep (se 2 (by rfl) ⟨586032, by rfl⟩ : syracuseStep 1562753 = 1172065) B1172065
theorem B1038683 : Blo 614296 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B1038703 : Blo 614296 1038703 := bstep (se 1 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 1038703 = 1558055) B1558055
theorem B1563047 : Blo 614296 1563047 := bstep (se 1 (by rfl) ⟨1172285, by rfl⟩ : syracuseStep 1563047 = 2344571) B2344571
theorem B1038919 : Blo 614296 1038919 := bstep (se 1 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 1038919 = 1558379) B1558379
theorem B1563209 : Blo 614296 1563209 := bstep (se 2 (by rfl) ⟨586203, by rfl⟩ : syracuseStep 1563209 = 1172407) B1172407
theorem B4676291 : Blo 614296 4676291 := bstep (se 1 (by rfl) ⟨3507218, by rfl⟩ : syracuseStep 4676291 = 7014437) B7014437
theorem B1760125 : Blo 614296 1760125 := bstep (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) B660047
theorem B1563563 : Blo 614296 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B8575931 : Blo 614296 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B875495 : Blo 614296 875495 := bstep (se 1 (by rfl) ⟨656621, by rfl⟩ : syracuseStep 875495 = 1313243) B1313243
theorem B1039351 : Blo 614296 1039351 := bstep (se 1 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 1039351 = 1559027) B1559027
theorem B1563745 : Blo 614296 1563745 := bstep (se 2 (by rfl) ⟨586404, by rfl⟩ : syracuseStep 1563745 = 1172809) B1172809
theorem B1662095 : Blo 614296 1662095 := bstep (se 1 (by rfl) ⟨1246571, by rfl⟩ : syracuseStep 1662095 = 2493143) B2493143
theorem B3169469 : Blo 614296 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B1039655 : Blo 614296 1039655 := bstep (se 1 (by rfl) ⟨779741, by rfl⟩ : syracuseStep 1039655 = 1559483) B1559483
theorem B777595 : Blo 614296 777595 := bstep (se 1 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 777595 = 1166393) B1166393
theorem B876025 : Blo 614296 876025 := bstep (se 2 (by rfl) ⟨328509, by rfl⟩ : syracuseStep 876025 = 657019) B657019
theorem B2252371 : Blo 614296 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B1040107 : Blo 614296 1040107 := bstep (se 1 (by rfl) ⟨780080, by rfl⟩ : syracuseStep 1040107 = 1560161) B1560161
theorem B5005097 : Blo 614296 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B614299 : Blo 614296 614299 := bstep (se 1 (by rfl) ⟨460724, by rfl⟩ : syracuseStep 614299 = 921449) B921449
theorem B614351 : Blo 614296 614351 := bstep (se 1 (by rfl) ⟨460763, by rfl⟩ : syracuseStep 614351 = 921527) B921527
theorem B614375 : Blo 614296 614375 := bstep (se 1 (by rfl) ⟨460781, by rfl⟩ : syracuseStep 614375 = 921563) B921563
theorem B1564697 : Blo 614296 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B3334355 : Blo 614296 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B614687 : Blo 614296 614687 := bstep (se 1 (by rfl) ⟨461015, by rfl⟩ : syracuseStep 614687 = 922031) B922031
theorem B614747 : Blo 614296 614747 := bstep (se 1 (by rfl) ⟨461060, by rfl⟩ : syracuseStep 614747 = 922121) B922121
theorem B614767 : Blo 614296 614767 := bstep (se 1 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 614767 = 922151) B922151
theorem B10510721 : Blo 614296 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B614823 : Blo 614296 614823 := bstep (se 1 (by rfl) ⟨461117, by rfl⟩ : syracuseStep 614823 = 922235) B922235
theorem B778663 : Blo 614296 778663 := bstep (se 1 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 778663 = 1167995) B1167995
theorem B614907 : Blo 614296 614907 := bstep (se 1 (by rfl) ⟨461180, by rfl⟩ : syracuseStep 614907 = 922361) B922361
theorem B614975 : Blo 614296 614975 := bstep (se 1 (by rfl) ⟨461231, by rfl⟩ : syracuseStep 614975 = 922463) B922463
theorem B614983 : Blo 614296 614983 := bstep (se 1 (by rfl) ⟨461237, by rfl⟩ : syracuseStep 614983 = 922475) B922475
theorem B4743851 : Blo 614296 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B1041079 : Blo 614296 1041079 := bstep (se 1 (by rfl) ⟨780809, by rfl⟩ : syracuseStep 1041079 = 1561619) B1561619
theorem B4448951 : Blo 614296 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B615135 : Blo 614296 615135 := bstep (se 1 (by rfl) ⟨461351, by rfl⟩ : syracuseStep 615135 = 922703) B922703
theorem B778987 : Blo 614296 778987 := bstep (se 1 (by rfl) ⟨584240, by rfl⟩ : syracuseStep 778987 = 1168481) B1168481
theorem B615215 : Blo 614296 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B615323 : Blo 614296 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B615375 : Blo 614296 615375 := bstep (se 1 (by rfl) ⟨461531, by rfl⟩ : syracuseStep 615375 = 923063) B923063
theorem B779215 : Blo 614296 779215 := bstep (se 1 (by rfl) ⟨584411, by rfl⟩ : syracuseStep 779215 = 1168823) B1168823
theorem B615399 : Blo 614296 615399 := bstep (se 1 (by rfl) ⟨461549, by rfl⟩ : syracuseStep 615399 = 923099) B923099
theorem B1041383 : Blo 614296 1041383 := bstep (se 1 (by rfl) ⟨781037, by rfl⟩ : syracuseStep 1041383 = 1562075) B1562075
theorem B9495589 : Blo 614296 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B779483 : Blo 614296 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B615711 : Blo 614296 615711 := bstep (se 1 (by rfl) ⟨461783, by rfl⟩ : syracuseStep 615711 = 923567) B923567
theorem B615771 : Blo 614296 615771 := bstep (se 1 (by rfl) ⟨461828, by rfl⟩ : syracuseStep 615771 = 923657) B923657
theorem B615791 : Blo 614296 615791 := bstep (se 1 (by rfl) ⟨461843, by rfl⟩ : syracuseStep 615791 = 923687) B923687
theorem B615847 : Blo 614296 615847 := bstep (se 1 (by rfl) ⟨461885, by rfl⟩ : syracuseStep 615847 = 923771) B923771
theorem B4449725 : Blo 614296 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B615931 : Blo 614296 615931 := bstep (se 1 (by rfl) ⟨461948, by rfl⟩ : syracuseStep 615931 = 923897) B923897
theorem B615999 : Blo 614296 615999 := bstep (se 1 (by rfl) ⟨461999, by rfl⟩ : syracuseStep 615999 = 923999) B923999
theorem B616007 : Blo 614296 616007 := bstep (se 1 (by rfl) ⟨462005, by rfl⟩ : syracuseStep 616007 = 924011) B924011
theorem B779959 : Blo 614296 779959 := bstep (se 1 (by rfl) ⟨584969, by rfl⟩ : syracuseStep 779959 = 1169939) B1169939
theorem B616159 : Blo 614296 616159 := bstep (se 1 (by rfl) ⟨462119, by rfl⟩ : syracuseStep 616159 = 924239) B924239
theorem B878377 : Blo 614296 878377 := bstep (se 2 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 878377 = 658783) B658783
theorem B616239 : Blo 614296 616239 := bstep (se 1 (by rfl) ⟨462179, by rfl⟩ : syracuseStep 616239 = 924359) B924359
theorem B1173295 : Blo 614296 1173295 := bstep (se 1 (by rfl) ⟨879971, by rfl⟩ : syracuseStep 1173295 = 1759943) B1759943
theorem B3565417 : Blo 614296 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B616347 : Blo 614296 616347 := bstep (se 1 (by rfl) ⟨462260, by rfl⟩ : syracuseStep 616347 = 924521) B924521
theorem B780187 : Blo 614296 780187 := bstep (se 1 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 780187 = 1170281) B1170281
theorem B1107919 : Blo 614296 1107919 := bstep (se 1 (by rfl) ⟨830939, by rfl⟩ : syracuseStep 1107919 = 1661879) B1661879
theorem B616399 : Blo 614296 616399 := bstep (se 1 (by rfl) ⟨462299, by rfl⟩ : syracuseStep 616399 = 924599) B924599
theorem B616423 : Blo 614296 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B1042537 : Blo 614296 1042537 := bstep (se 2 (by rfl) ⟨390951, by rfl⟩ : syracuseStep 1042537 = 781903) B781903
theorem B616735 : Blo 614296 616735 := bstep (se 1 (by rfl) ⟨462551, by rfl⟩ : syracuseStep 616735 = 925103) B925103
theorem B616795 : Blo 614296 616795 := bstep (se 1 (by rfl) ⟨462596, by rfl⟩ : syracuseStep 616795 = 925193) B925193
theorem B616815 : Blo 614296 616815 := bstep (se 1 (by rfl) ⟨462611, by rfl⟩ : syracuseStep 616815 = 925223) B925223
theorem B616871 : Blo 614296 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B4680179 : Blo 614296 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B616955 : Blo 614296 616955 := bstep (se 1 (by rfl) ⟨462716, by rfl⟩ : syracuseStep 616955 = 925433) B925433
theorem B53144099 : Blo 614296 53144099 := bstep (se 1 (by rfl) ⟨39858074, by rfl⟩ : syracuseStep 53144099 = 79716149) B79716149
theorem B617023 : Blo 614296 617023 := bstep (se 1 (by rfl) ⟨462767, by rfl⟩ : syracuseStep 617023 = 925535) B925535
theorem B617031 : Blo 614296 617031 := bstep (se 1 (by rfl) ⟨462773, by rfl⟩ : syracuseStep 617031 = 925547) B925547
theorem B617183 : Blo 614296 617183 := bstep (se 1 (by rfl) ⟨462887, by rfl⟩ : syracuseStep 617183 = 925775) B925775
theorem B781103 : Blo 614296 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B617263 : Blo 614296 617263 := bstep (se 1 (by rfl) ⟨462947, by rfl⟩ : syracuseStep 617263 = 925895) B925895
theorem B617371 : Blo 614296 617371 := bstep (se 1 (by rfl) ⟨463028, by rfl⟩ : syracuseStep 617371 = 926057) B926057
theorem B617423 : Blo 614296 617423 := bstep (se 1 (by rfl) ⟨463067, by rfl⟩ : syracuseStep 617423 = 926135) B926135
theorem B617447 : Blo 614296 617447 := bstep (se 1 (by rfl) ⟨463085, by rfl⟩ : syracuseStep 617447 = 926171) B926171
theorem B6679691 : Blo 614296 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B879835 : Blo 614296 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B617759 : Blo 614296 617759 := bstep (se 1 (by rfl) ⟨463319, by rfl⟩ : syracuseStep 617759 = 926639) B926639
theorem B617819 : Blo 614296 617819 := bstep (se 1 (by rfl) ⟨463364, by rfl⟩ : syracuseStep 617819 = 926729) B926729
theorem B617839 : Blo 614296 617839 := bstep (se 1 (by rfl) ⟨463379, by rfl⟩ : syracuseStep 617839 = 926759) B926759
theorem B617895 : Blo 614296 617895 := bstep (se 1 (by rfl) ⟨463421, by rfl⟩ : syracuseStep 617895 = 926843) B926843
theorem B617979 : Blo 614296 617979 := bstep (se 1 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 617979 = 926969) B926969
theorem B618047 : Blo 614296 618047 := bstep (se 1 (by rfl) ⟨463535, by rfl⟩ : syracuseStep 618047 = 927071) B927071
theorem B618055 : Blo 614296 618055 := bstep (se 1 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 618055 = 927083) B927083
theorem B618207 : Blo 614296 618207 := bstep (se 1 (by rfl) ⟨463655, by rfl⟩ : syracuseStep 618207 = 927311) B927311
theorem B6319883 : Blo 614296 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B618287 : Blo 614296 618287 := bstep (se 1 (by rfl) ⟨463715, by rfl⟩ : syracuseStep 618287 = 927431) B927431
theorem B1666973 : Blo 614296 1666973 := bstep (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) B625115
theorem B3960899 : Blo 614296 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B24080921 : Blo 614296 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B1110601 : Blo 614296 1110601 := bstep (se 2 (by rfl) ⟨416475, by rfl⟩ : syracuseStep 1110601 = 832951) B832951
theorem B136376945 : Blo 614296 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B2847869 : Blo 614296 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B5272721 : Blo 614296 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B2258219 : Blo 614296 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B1668539 : Blo 614296 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1504727 : Blo 614296 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B18708317 : Blo 614296 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B5928889 : Blo 614296 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B2815951 : Blo 614296 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B3111047 : Blo 614296 3111047 := bstep (se 1 (by rfl) ⟨2333285, by rfl⟩ : syracuseStep 3111047 = 4666571) B4666571
theorem B1112987 : Blo 614296 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B2817011 : Blo 614296 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B1670183 : Blo 614296 1670183 := bstep (se 1 (by rfl) ⟨1252637, by rfl⟩ : syracuseStep 1670183 = 2505275) B2505275
theorem B1604827 : Blo 614296 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B30080393 : Blo 614296 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B3506651 : Blo 614296 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B3736115 : Blo 614296 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B56984593 : Blo 614296 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B3114611 : Blo 614296 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B12650269 : Blo 614296 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B1313081 : Blo 614296 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B3115421 : Blo 614296 3115421 := bstep (se 3 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 3115421 = 1168283) B1168283
theorem B6654433 : Blo 614296 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B4753889 : Blo 614296 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B1477225 : Blo 614296 1477225 := bstep (se 2 (by rfl) ⟨553959, by rfl⟩ : syracuseStep 1477225 = 1107919) B1107919
theorem B3116231 : Blo 614296 3116231 := bstep (se 1 (by rfl) ⟨2337173, by rfl⟩ : syracuseStep 3116231 = 4674347) B4674347
theorem B921467 : Blo 614296 921467 := bstep (se 1 (by rfl) ⟨691100, by rfl⟩ : syracuseStep 921467 = 1382201) B1382201
theorem B692455 : Blo 614296 692455 := bstep (se 1 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 692455 = 1038683) B1038683
theorem B921887 : Blo 614296 921887 := bstep (se 1 (by rfl) ⟨691415, by rfl⟩ : syracuseStep 921887 = 1382831) B1382831
theorem B921911 : Blo 614296 921911 := bstep (se 1 (by rfl) ⟨691433, by rfl⟩ : syracuseStep 921911 = 1382867) B1382867
theorem B921983 : Blo 614296 921983 := bstep (se 1 (by rfl) ⟨691487, by rfl⟩ : syracuseStep 921983 = 1382975) B1382975
theorem B922055 : Blo 614296 922055 := bstep (se 1 (by rfl) ⟨691541, by rfl⟩ : syracuseStep 922055 = 1383083) B1383083
theorem B3117527 : Blo 614296 3117527 := bstep (se 1 (by rfl) ⟨2338145, by rfl⟩ : syracuseStep 3117527 = 4676291) B4676291
theorem B922409 : Blo 614296 922409 := bstep (se 2 (by rfl) ⟨345903, by rfl⟩ : syracuseStep 922409 = 691807) B691807
theorem B922415 : Blo 614296 922415 := bstep (se 1 (by rfl) ⟨691811, by rfl⟩ : syracuseStep 922415 = 1383623) B1383623
theorem B693103 : Blo 614296 693103 := bstep (se 1 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 693103 = 1039655) B1039655
theorem B922535 : Blo 614296 922535 := bstep (se 1 (by rfl) ⟨691901, by rfl⟩ : syracuseStep 922535 = 1383803) B1383803
theorem B922619 : Blo 614296 922619 := bstep (se 1 (by rfl) ⟨691964, by rfl⟩ : syracuseStep 922619 = 1383929) B1383929
theorem B3937319 : Blo 614296 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B922679 : Blo 614296 922679 := bstep (se 1 (by rfl) ⟨692009, by rfl⟩ : syracuseStep 922679 = 1384019) B1384019
theorem B4428881 : Blo 614296 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B922799 : Blo 614296 922799 := bstep (se 1 (by rfl) ⟨692099, by rfl⟩ : syracuseStep 922799 = 1384199) B1384199
theorem B988507 : Blo 614296 988507 := bstep (se 1 (by rfl) ⟨741380, by rfl⟩ : syracuseStep 988507 = 1482761) B1482761
theorem B923207 : Blo 614296 923207 := bstep (se 1 (by rfl) ⟨692405, by rfl⟩ : syracuseStep 923207 = 1384811) B1384811
theorem B923303 : Blo 614296 923303 := bstep (se 1 (by rfl) ⟨692477, by rfl⟩ : syracuseStep 923303 = 1384955) B1384955
theorem B5281469 : Blo 614296 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B923387 : Blo 614296 923387 := bstep (se 1 (by rfl) ⟨692540, by rfl⟩ : syracuseStep 923387 = 1385081) B1385081
theorem B923423 : Blo 614296 923423 := bstep (se 1 (by rfl) ⟨692567, by rfl⟩ : syracuseStep 923423 = 1385135) B1385135
theorem B923471 : Blo 614296 923471 := bstep (se 1 (by rfl) ⟨692603, by rfl⟩ : syracuseStep 923471 = 1385207) B1385207
theorem B1185673 : Blo 614296 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B923591 : Blo 614296 923591 := bstep (se 1 (by rfl) ⟨692693, by rfl⟩ : syracuseStep 923591 = 1385387) B1385387
theorem B1382363 : Blo 614296 1382363 := bstep (se 1 (by rfl) ⟨1036772, by rfl⟩ : syracuseStep 1382363 = 2073545) B2073545
theorem B694255 : Blo 614296 694255 := bstep (se 1 (by rfl) ⟨520691, by rfl⟩ : syracuseStep 694255 = 1041383) B1041383
theorem B1480801 : Blo 614296 1480801 := bstep (se 2 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 1480801 = 1110601) B1110601
theorem B1382543 : Blo 614296 1382543 := bstep (se 1 (by rfl) ⟨1036907, by rfl⟩ : syracuseStep 1382543 = 2073815) B2073815
theorem B1317019 : Blo 614296 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B1382561 : Blo 614296 1382561 := bstep (se 2 (by rfl) ⟨518460, by rfl⟩ : syracuseStep 1382561 = 1036921) B1036921
theorem B1382633 : Blo 614296 1382633 := bstep (se 2 (by rfl) ⟨518487, by rfl⟩ : syracuseStep 1382633 = 1036975) B1036975
theorem B923945 : Blo 614296 923945 := bstep (se 2 (by rfl) ⟨346479, by rfl⟩ : syracuseStep 923945 = 692959) B692959
theorem B923951 : Blo 614296 923951 := bstep (se 1 (by rfl) ⟨692963, by rfl⟩ : syracuseStep 923951 = 1385927) B1385927
theorem B924191 : Blo 614296 924191 := bstep (se 1 (by rfl) ⟨693143, by rfl⟩ : syracuseStep 924191 = 1386287) B1386287
theorem B924575 : Blo 614296 924575 := bstep (se 1 (by rfl) ⟨693431, by rfl⟩ : syracuseStep 924575 = 1386863) B1386863
theorem B924623 : Blo 614296 924623 := bstep (se 1 (by rfl) ⟨693467, by rfl⟩ : syracuseStep 924623 = 1386935) B1386935
theorem B3120119 : Blo 614296 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B35429399 : Blo 614296 35429399 := bstep (se 1 (by rfl) ⟨26572049, by rfl⟩ : syracuseStep 35429399 = 53144099) B53144099
theorem B924713 : Blo 614296 924713 := bstep (se 2 (by rfl) ⟨346767, by rfl⟩ : syracuseStep 924713 = 693535) B693535
theorem B924719 : Blo 614296 924719 := bstep (se 1 (by rfl) ⟨693539, by rfl⟩ : syracuseStep 924719 = 1387079) B1387079
theorem B924743 : Blo 614296 924743 := bstep (se 1 (by rfl) ⟨693557, by rfl⟩ : syracuseStep 924743 = 1387115) B1387115
theorem B925007 : Blo 614296 925007 := bstep (se 1 (by rfl) ⟨693755, by rfl⟩ : syracuseStep 925007 = 1387511) B1387511
theorem B925097 : Blo 614296 925097 := bstep (se 2 (by rfl) ⟨346911, by rfl⟩ : syracuseStep 925097 = 693823) B693823
theorem B1383911 : Blo 614296 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B925247 : Blo 614296 925247 := bstep (se 1 (by rfl) ⟨693935, by rfl⟩ : syracuseStep 925247 = 1387871) B1387871
theorem B925511 : Blo 614296 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B1318727 : Blo 614296 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B925595 : Blo 614296 925595 := bstep (se 1 (by rfl) ⟨694196, by rfl⟩ : syracuseStep 925595 = 1388393) B1388393
theorem B7905185 : Blo 614296 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B2334653 : Blo 614296 2334653 := bstep (se 3 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 2334653 = 875495) B875495
theorem B1384487 : Blo 614296 1384487 := bstep (se 1 (by rfl) ⟨1038365, by rfl⟩ : syracuseStep 1384487 = 2076731) B2076731
theorem B1384667 : Blo 614296 1384667 := bstep (se 1 (by rfl) ⟨1038500, by rfl⟩ : syracuseStep 1384667 = 2077001) B2077001
theorem B3154301 : Blo 614296 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B926159 : Blo 614296 926159 := bstep (se 1 (by rfl) ⟨694619, by rfl⟩ : syracuseStep 926159 = 1389239) B1389239
theorem B1384937 : Blo 614296 1384937 := bstep (se 2 (by rfl) ⟨519351, by rfl⟩ : syracuseStep 1384937 = 1038703) B1038703
theorem B926201 : Blo 614296 926201 := bstep (se 2 (by rfl) ⟨347325, by rfl⟩ : syracuseStep 926201 = 694651) B694651
theorem B3940883 : Blo 614296 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B926303 : Blo 614296 926303 := bstep (se 1 (by rfl) ⟨694727, by rfl⟩ : syracuseStep 926303 = 1389455) B1389455
theorem B1385225 : Blo 614296 1385225 := bstep (se 2 (by rfl) ⟨519459, by rfl⟩ : syracuseStep 1385225 = 1038919) B1038919
theorem B3515147 : Blo 614296 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B1975195 : Blo 614296 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B926783 : Blo 614296 926783 := bstep (se 1 (by rfl) ⟨695087, by rfl⟩ : syracuseStep 926783 = 1390175) B1390175
theorem B926825 : Blo 614296 926825 := bstep (se 2 (by rfl) ⟨347559, by rfl⟩ : syracuseStep 926825 = 695119) B695119
theorem B2106491 : Blo 614296 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B4400335 : Blo 614296 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B926927 : Blo 614296 926927 := bstep (se 1 (by rfl) ⟨695195, by rfl⟩ : syracuseStep 926927 = 1390391) B1390391
theorem B1385801 : Blo 614296 1385801 := bstep (se 2 (by rfl) ⟨519675, by rfl⟩ : syracuseStep 1385801 = 1039351) B1039351
theorem B927131 : Blo 614296 927131 := bstep (se 1 (by rfl) ⟨695348, by rfl⟩ : syracuseStep 927131 = 1390697) B1390697
theorem B2074031 : Blo 614296 2074031 := bstep (se 1 (by rfl) ⟨1555523, by rfl⟩ : syracuseStep 2074031 = 3111047) B3111047
theorem B2139769 : Blo 614296 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B927353 : Blo 614296 927353 := bstep (se 2 (by rfl) ⟨347757, by rfl⟩ : syracuseStep 927353 = 695515) B695515
theorem B2074409 : Blo 614296 2074409 := bstep (se 2 (by rfl) ⟨777903, by rfl⟩ : syracuseStep 2074409 = 1555807) B1555807
theorem B1878007 : Blo 614296 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B16853021 : Blo 614296 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B5351453 : Blo 614296 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B2500733 : Blo 614296 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B1386791 : Blo 614296 1386791 := bstep (se 1 (by rfl) ⟨1040093, by rfl⟩ : syracuseStep 1386791 = 2080187) B2080187
theorem B1386809 : Blo 614296 1386809 := bstep (se 2 (by rfl) ⟨520053, by rfl⟩ : syracuseStep 1386809 = 1040107) B1040107
theorem B3942751 : Blo 614296 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B2337281 : Blo 614296 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B43232777 : Blo 614296 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B1388105 : Blo 614296 1388105 := bstep (se 2 (by rfl) ⟨520539, by rfl⟩ : syracuseStep 1388105 = 1041079) B1041079
theorem B3518315 : Blo 614296 3518315 := bstep (se 1 (by rfl) ⟨2638736, by rfl⟩ : syracuseStep 3518315 = 5277473) B5277473
theorem B2633627 : Blo 614296 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B2076623 : Blo 614296 2076623 := bstep (se 1 (by rfl) ⟨1557467, by rfl⟩ : syracuseStep 2076623 = 3114935) B3114935
theorem B7024643 : Blo 614296 7024643 := bstep (se 1 (by rfl) ⟨5268482, by rfl⟩ : syracuseStep 7024643 = 10536965) B10536965
theorem B12660785 : Blo 614296 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B2502845 : Blo 614296 2502845 := bstep (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) B938567
theorem B4731203 : Blo 614296 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B2077055 : Blo 614296 2077055 := bstep (se 1 (by rfl) ⟨1557791, by rfl⟩ : syracuseStep 2077055 = 3115583) B3115583
theorem B2339239 : Blo 614296 2339239 := bstep (se 1 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 2339239 = 3508859) B3508859
theorem B1389563 : Blo 614296 1389563 := bstep (se 1 (by rfl) ⟨1042172, by rfl⟩ : syracuseStep 1389563 = 2084345) B2084345
theorem B1750079 : Blo 614296 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B701503 : Blo 614296 701503 := bstep (se 1 (by rfl) ⟨526127, by rfl⟩ : syracuseStep 701503 = 1052255) B1052255
theorem B10663001 : Blo 614296 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B1389743 : Blo 614296 1389743 := bstep (se 1 (by rfl) ⟨1042307, by rfl⟩ : syracuseStep 1389743 = 2084615) B2084615
theorem B1389779 : Blo 614296 1389779 := bstep (se 1 (by rfl) ⟨1042334, by rfl⟩ : syracuseStep 1389779 = 2084669) B2084669
theorem B1390049 : Blo 614296 1390049 := bstep (se 2 (by rfl) ⟨521268, by rfl⟩ : syracuseStep 1390049 = 1042537) B1042537
theorem B1979873 : Blo 614296 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B2078459 : Blo 614296 2078459 := bstep (se 1 (by rfl) ⟨1558844, by rfl⟩ : syracuseStep 2078459 = 3117689) B3117689
theorem B2078621 : Blo 614296 2078621 := bstep (se 3 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 2078621 = 779483) B779483
theorem B1751195 : Blo 614296 1751195 := bstep (se 1 (by rfl) ⟨1313396, by rfl⟩ : syracuseStep 1751195 = 2626793) B2626793
theorem B4044971 : Blo 614296 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B2669075 : Blo 614296 2669075 := bstep (se 1 (by rfl) ⟨2001806, by rfl⟩ : syracuseStep 2669075 = 4003613) B4003613
theorem B35109551 : Blo 614296 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B2079593 : Blo 614296 2079593 := bstep (se 2 (by rfl) ⟨779847, by rfl⟩ : syracuseStep 2079593 = 1559695) B1559695
theorem B2079647 : Blo 614296 2079647 := bstep (se 1 (by rfl) ⟨1559735, by rfl⟩ : syracuseStep 2079647 = 3119471) B3119471
theorem B9026599 : Blo 614296 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B3849257 : Blo 614296 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B5717287 : Blo 614296 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B2112979 : Blo 614296 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B3325531 : Blo 614296 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B1556111 : Blo 614296 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B14991065 : Blo 614296 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B2342945 : Blo 614296 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B20299855 : Blo 614296 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B2965967 : Blo 614296 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B21283337 : Blo 614296 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B2343599 : Blo 614296 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B2638601 : Blo 614296 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B2966483 : Blo 614296 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B2081915 : Blo 614296 2081915 := bstep (se 1 (by rfl) ⟨1561436, by rfl⟩ : syracuseStep 2081915 = 3122873) B3122873
theorem B8111411 : Blo 614296 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B2082185 : Blo 614296 2082185 := bstep (se 2 (by rfl) ⟨780819, by rfl⟩ : syracuseStep 2082185 = 1561639) B1561639
theorem B2082941 : Blo 614296 2082941 := bstep (se 3 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 2082941 = 781103) B781103
theorem B3950801 : Blo 614296 3950801 := bstep (se 2 (by rfl) ⟨1481550, by rfl⟩ : syracuseStep 3950801 = 2963101) B2963101
theorem B2083211 : Blo 614296 2083211 := bstep (se 1 (by rfl) ⟨1562408, by rfl⟩ : syracuseStep 2083211 = 3124817) B3124817
theorem B2967965 : Blo 614296 2967965 := bstep (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) B1112987
theorem B1559047 : Blo 614296 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B3754601 : Blo 614296 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B2640599 : Blo 614296 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B1559351 : Blo 614296 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B90917963 : Blo 614296 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B3656927 : Blo 614296 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B7884377 : Blo 614296 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B1003151 : Blo 614296 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B8867501 : Blo 614296 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B1167023 : Blo 614296 1167023 := bstep (se 1 (by rfl) ⟨875267, by rfl⟩ : syracuseStep 1167023 = 1750535) B1750535
theorem B2346833 : Blo 614296 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B12472211 : Blo 614296 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B2084831 : Blo 614296 2084831 := bstep (se 1 (by rfl) ⟨1563623, by rfl⟩ : syracuseStep 2084831 = 3127247) B3127247
theorem B2084993 : Blo 614296 2084993 := bstep (se 2 (by rfl) ⟨781872, by rfl⟩ : syracuseStep 2084993 = 1563745) B1563745
theorem B1167547 : Blo 614296 1167547 := bstep (se 1 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 1167547 = 1751321) B1751321
theorem B1757551 : Blo 614296 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B1036793 : Blo 614296 1036793 := bstep (se 2 (by rfl) ⟨388797, by rfl⟩ : syracuseStep 1036793 = 777595) B777595
theorem B2085479 : Blo 614296 2085479 := bstep (se 1 (by rfl) ⟨1564109, by rfl⟩ : syracuseStep 2085479 = 3128219) B3128219
theorem B1168033 : Blo 614296 1168033 := bstep (se 2 (by rfl) ⟨438012, by rfl⟩ : syracuseStep 1168033 = 876025) B876025
theorem B1037063 : Blo 614296 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B3003161 : Blo 614296 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B4510505 : Blo 614296 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B2085803 : Blo 614296 2085803 := bstep (se 1 (by rfl) ⟨1564352, by rfl⟩ : syracuseStep 2085803 = 3128705) B3128705
theorem B2086235 : Blo 614296 2086235 := bstep (se 1 (by rfl) ⟨1564676, by rfl⟩ : syracuseStep 2086235 = 3129353) B3129353
theorem B2086343 : Blo 614296 2086343 := bstep (se 1 (by rfl) ⟨1564757, by rfl⟩ : syracuseStep 2086343 = 3129515) B3129515
theorem B3954233 : Blo 614296 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B1168967 : Blo 614296 1168967 := bstep (se 1 (by rfl) ⟨876725, by rfl⟩ : syracuseStep 1168967 = 1753451) B1753451
theorem B2086667 : Blo 614296 2086667 := bstep (se 1 (by rfl) ⟨1565000, by rfl⟩ : syracuseStep 2086667 = 3130001) B3130001
theorem B1038143 : Blo 614296 1038143 := bstep (se 1 (by rfl) ⟨778607, by rfl⟩ : syracuseStep 1038143 = 1557215) B1557215
theorem B1038217 : Blo 614296 1038217 := bstep (se 2 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 1038217 = 778663) B778663
theorem B1169491 : Blo 614296 1169491 := bstep (se 1 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 1169491 = 1754237) B1754237
theorem B1038649 : Blo 614296 1038649 := bstep (se 2 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 1038649 = 778987) B778987
theorem B11852243 : Blo 614296 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B1038953 : Blo 614296 1038953 := bstep (se 2 (by rfl) ⟨389607, by rfl⟩ : syracuseStep 1038953 = 779215) B779215
theorem B11819641 : Blo 614296 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B1039783 : Blo 614296 1039783 := bstep (se 1 (by rfl) ⟨779837, by rfl⟩ : syracuseStep 1039783 = 1559675) B1559675
theorem B1039945 : Blo 614296 1039945 := bstep (se 2 (by rfl) ⟨389979, by rfl⟩ : syracuseStep 1039945 = 779959) B779959
theorem B1039979 : Blo 614296 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B1171169 : Blo 614296 1171169 := bstep (se 2 (by rfl) ⟨439188, by rfl⟩ : syracuseStep 1171169 = 878377) B878377
theorem B1564393 : Blo 614296 1564393 := bstep (se 2 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 1564393 = 1173295) B1173295
theorem B1040249 : Blo 614296 1040249 := bstep (se 2 (by rfl) ⟨390093, by rfl⟩ : syracuseStep 1040249 = 780187) B780187
theorem B5267389 : Blo 614296 5267389 := bstep (se 3 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 5267389 = 1975271) B1975271
theorem B614367 : Blo 614296 614367 := bstep (se 1 (by rfl) ⟨460775, by rfl⟩ : syracuseStep 614367 = 921551) B921551
theorem B614631 : Blo 614296 614631 := bstep (se 1 (by rfl) ⟨460973, by rfl⟩ : syracuseStep 614631 = 921947) B921947
theorem B614783 : Blo 614296 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B614863 : Blo 614296 614863 := bstep (se 1 (by rfl) ⟨461147, by rfl⟩ : syracuseStep 614863 = 922295) B922295
theorem B615015 : Blo 614296 615015 := bstep (se 1 (by rfl) ⟨461261, by rfl⟩ : syracuseStep 615015 = 922523) B922523
theorem B21652103 : Blo 614296 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B615279 : Blo 614296 615279 := bstep (se 1 (by rfl) ⟨461459, by rfl⟩ : syracuseStep 615279 = 922919) B922919
theorem B615335 : Blo 614296 615335 := bstep (se 1 (by rfl) ⟨461501, by rfl⟩ : syracuseStep 615335 = 923003) B923003
theorem B1663955 : Blo 614296 1663955 := bstep (se 1 (by rfl) ⟨1247966, by rfl⟩ : syracuseStep 1663955 = 2495933) B2495933
theorem B615419 : Blo 614296 615419 := bstep (se 1 (by rfl) ⟨461564, by rfl⟩ : syracuseStep 615419 = 923129) B923129
theorem B1041403 : Blo 614296 1041403 := bstep (se 1 (by rfl) ⟨781052, by rfl⟩ : syracuseStep 1041403 = 1562105) B1562105
theorem B615487 : Blo 614296 615487 := bstep (se 1 (by rfl) ⟨461615, by rfl⟩ : syracuseStep 615487 = 923231) B923231
theorem B4449437 : Blo 614296 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B615631 : Blo 614296 615631 := bstep (se 1 (by rfl) ⟨461723, by rfl⟩ : syracuseStep 615631 = 923447) B923447
theorem B615835 : Blo 614296 615835 := bstep (se 1 (by rfl) ⟨461876, by rfl⟩ : syracuseStep 615835 = 923753) B923753
theorem B1402283 : Blo 614296 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B1041835 : Blo 614296 1041835 := bstep (se 1 (by rfl) ⟨781376, by rfl⟩ : syracuseStep 1041835 = 1562753) B1562753
theorem B616047 : Blo 614296 616047 := bstep (se 1 (by rfl) ⟨462035, by rfl⟩ : syracuseStep 616047 = 924071) B924071
theorem B1042031 : Blo 614296 1042031 := bstep (se 1 (by rfl) ⟨781523, by rfl⟩ : syracuseStep 1042031 = 1563047) B1563047
theorem B1173113 : Blo 614296 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B616103 : Blo 614296 616103 := bstep (se 1 (by rfl) ⟨462077, by rfl⟩ : syracuseStep 616103 = 924155) B924155
theorem B1042139 : Blo 614296 1042139 := bstep (se 1 (by rfl) ⟨781604, by rfl⟩ : syracuseStep 1042139 = 1563209) B1563209
theorem B878303 : Blo 614296 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B616187 : Blo 614296 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B616223 : Blo 614296 616223 := bstep (se 1 (by rfl) ⟨462167, by rfl⟩ : syracuseStep 616223 = 924335) B924335
theorem B616255 : Blo 614296 616255 := bstep (se 1 (by rfl) ⟨462191, by rfl⟩ : syracuseStep 616255 = 924383) B924383
theorem B1402721 : Blo 614296 1402721 := bstep (se 2 (by rfl) ⟨526020, by rfl⟩ : syracuseStep 1402721 = 1052041) B1052041
theorem B1042375 : Blo 614296 1042375 := bstep (se 1 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 1042375 = 1563563) B1563563
theorem B616431 : Blo 614296 616431 := bstep (se 1 (by rfl) ⟨462323, by rfl⟩ : syracuseStep 616431 = 924647) B924647
theorem B3565601 : Blo 614296 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B3500111 : Blo 614296 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B1108063 : Blo 614296 1108063 := bstep (se 1 (by rfl) ⟨831047, by rfl⟩ : syracuseStep 1108063 = 1662095) B1662095
theorem B616603 : Blo 614296 616603 := bstep (se 1 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 616603 = 924905) B924905
theorem B616639 : Blo 614296 616639 := bstep (se 1 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 616639 = 924959) B924959
theorem B616751 : Blo 614296 616751 := bstep (se 1 (by rfl) ⟨462563, by rfl⟩ : syracuseStep 616751 = 925127) B925127
theorem B4286881 : Blo 614296 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B616987 : Blo 614296 616987 := bstep (se 1 (by rfl) ⟨462740, by rfl⟩ : syracuseStep 616987 = 925481) B925481
theorem B3336731 : Blo 614296 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B616991 : Blo 614296 616991 := bstep (se 1 (by rfl) ⟨462743, by rfl⟩ : syracuseStep 616991 = 925487) B925487
theorem B1043131 : Blo 614296 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B6646475 : Blo 614296 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B9988919 : Blo 614296 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B2222903 : Blo 614296 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B617307 : Blo 614296 617307 := bstep (se 1 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 617307 = 925961) B925961
theorem B30043025 : Blo 614296 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B617375 : Blo 614296 617375 := bstep (se 1 (by rfl) ⟨463031, by rfl⟩ : syracuseStep 617375 = 926063) B926063
theorem B7007147 : Blo 614296 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B617519 : Blo 614296 617519 := bstep (se 1 (by rfl) ⟨463139, by rfl⟩ : syracuseStep 617519 = 926279) B926279
theorem B617543 : Blo 614296 617543 := bstep (se 1 (by rfl) ⟨463157, by rfl⟩ : syracuseStep 617543 = 926315) B926315
theorem B617695 : Blo 614296 617695 := bstep (se 1 (by rfl) ⟨463271, by rfl⟩ : syracuseStep 617695 = 926543) B926543
theorem B1666487 : Blo 614296 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B617959 : Blo 614296 617959 := bstep (se 1 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 617959 = 926939) B926939
theorem B618075 : Blo 614296 618075 := bstep (se 1 (by rfl) ⟨463556, by rfl⟩ : syracuseStep 618075 = 927113) B927113
theorem B17788511 : Blo 614296 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B5271763 : Blo 614296 5271763 := bstep (se 1 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 5271763 = 7907645) B7907645
theorem B3207761 : Blo 614296 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B4453127 : Blo 614296 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B1111315 : Blo 614296 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B3503483 : Blo 614296 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B16053947 : Blo 614296 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B1898579 : Blo 614296 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B1505479 : Blo 614296 1505479 := bstep (se 1 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 1505479 = 2258219) B2258219
theorem B3505193 : Blo 614296 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B1113455 : Blo 614296 1113455 := bstep (se 1 (by rfl) ⟨835091, by rfl⟩ : syracuseStep 1113455 = 1670183) B1670183
theorem B4488635 : Blo 614296 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B20053595 : Blo 614296 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B3112829 : Blo 614296 3112829 := bstep (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) B1167311
theorem B2228093 : Blo 614296 2228093 := bstep (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) B835535
theorem B27066473 : Blo 614296 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B14188891 : Blo 614296 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B2490743 : Blo 614296 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B5407607 : Blo 614296 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B5867113 : Blo 614296 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B2853025 : Blo 614296 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B691195 : Blo 614296 691195 := bstep (se 1 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 691195 = 1036793) B1036793
theorem B691375 : Blo 614296 691375 := bstep (se 1 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 691375 = 1037063) B1037063
theorem B2624879 : Blo 614296 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2952587 : Blo 614296 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B1969633 : Blo 614296 1969633 := bstep (se 2 (by rfl) ⟨738612, by rfl⟩ : syracuseStep 1969633 = 1477225) B1477225
theorem B3739421 : Blo 614296 3739421 := bstep (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) B1402283
theorem B692095 : Blo 614296 692095 := bstep (se 1 (by rfl) ⟨519071, by rfl⟩ : syracuseStep 692095 = 1038143) B1038143
theorem B921575 : Blo 614296 921575 := bstep (se 1 (by rfl) ⟨691181, by rfl⟩ : syracuseStep 921575 = 1382363) B1382363
theorem B921695 : Blo 614296 921695 := bstep (se 1 (by rfl) ⟨691271, by rfl⟩ : syracuseStep 921695 = 1382543) B1382543
theorem B921707 : Blo 614296 921707 := bstep (se 1 (by rfl) ⟨691280, by rfl⟩ : syracuseStep 921707 = 1382561) B1382561
theorem B921755 : Blo 614296 921755 := bstep (se 1 (by rfl) ⟨691316, by rfl⟩ : syracuseStep 921755 = 1382633) B1382633
theorem B7901495 : Blo 614296 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B692635 : Blo 614296 692635 := bstep (se 1 (by rfl) ⟨519476, by rfl⟩ : syracuseStep 692635 = 1038953) B1038953
theorem B922607 : Blo 614296 922607 := bstep (se 1 (by rfl) ⟨691955, by rfl⟩ : syracuseStep 922607 = 1383911) B1383911
theorem B693319 : Blo 614296 693319 := bstep (se 1 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 693319 = 1039979) B1039979
theorem B693499 : Blo 614296 693499 := bstep (se 1 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 693499 = 1040249) B1040249
theorem B922991 : Blo 614296 922991 := bstep (se 1 (by rfl) ⟨692243, by rfl⟩ : syracuseStep 922991 = 1384487) B1384487
theorem B923111 : Blo 614296 923111 := bstep (se 1 (by rfl) ⟨692333, by rfl⟩ : syracuseStep 923111 = 1384667) B1384667
theorem B2102867 : Blo 614296 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B923273 : Blo 614296 923273 := bstep (se 2 (by rfl) ⟨346227, by rfl⟩ : syracuseStep 923273 = 692455) B692455
theorem B923291 : Blo 614296 923291 := bstep (se 1 (by rfl) ⟨692468, by rfl⟩ : syracuseStep 923291 = 1384937) B1384937
theorem B3741349 : Blo 614296 3741349 := bstep (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) B701503
theorem B2627255 : Blo 614296 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B923483 : Blo 614296 923483 := bstep (se 1 (by rfl) ⟨692612, by rfl⟩ : syracuseStep 923483 = 1385225) B1385225
theorem B3118985 : Blo 614296 3118985 := bstep (se 2 (by rfl) ⟨1169619, by rfl⟩ : syracuseStep 3118985 = 2339239) B2339239
theorem B923867 : Blo 614296 923867 := bstep (se 1 (by rfl) ⟨692900, by rfl⟩ : syracuseStep 923867 = 1385801) B1385801
theorem B1382687 : Blo 614296 1382687 := bstep (se 1 (by rfl) ⟨1037015, by rfl⟩ : syracuseStep 1382687 = 2074031) B2074031
theorem B694687 : Blo 614296 694687 := bstep (se 1 (by rfl) ⟨521015, by rfl⟩ : syracuseStep 694687 = 1042031) B1042031
theorem B694759 : Blo 614296 694759 := bstep (se 1 (by rfl) ⟨521069, by rfl⟩ : syracuseStep 694759 = 1042139) B1042139
theorem B924137 : Blo 614296 924137 := bstep (se 2 (by rfl) ⟨346551, by rfl⟩ : syracuseStep 924137 = 693103) B693103
theorem B1382939 : Blo 614296 1382939 := bstep (se 1 (by rfl) ⟨1037204, by rfl⟩ : syracuseStep 1382939 = 2074409) B2074409
theorem B2333407 : Blo 614296 2333407 := bstep (se 1 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 2333407 = 3500111) B3500111
theorem B924527 : Blo 614296 924527 := bstep (se 1 (by rfl) ⟨693395, by rfl⟩ : syracuseStep 924527 = 1386791) B1386791
theorem B924539 : Blo 614296 924539 := bstep (se 1 (by rfl) ⟨693404, by rfl⟩ : syracuseStep 924539 = 1386809) B1386809
theorem B1481753 : Blo 614296 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B4430983 : Blo 614296 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B6659279 : Blo 614296 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B20028683 : Blo 614296 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B925403 : Blo 614296 925403 := bstep (se 1 (by rfl) ⟨694052, by rfl⟩ : syracuseStep 925403 = 1388105) B1388105
theorem B1384289 : Blo 614296 1384289 := bstep (se 2 (by rfl) ⟨519108, by rfl⟩ : syracuseStep 1384289 = 1038217) B1038217
theorem B1580897 : Blo 614296 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B1384415 : Blo 614296 1384415 := bstep (se 1 (by rfl) ⟨1038311, by rfl⟩ : syracuseStep 1384415 = 2076623) B2076623
theorem B925673 : Blo 614296 925673 := bstep (se 2 (by rfl) ⟨347127, by rfl⟩ : syracuseStep 925673 = 694255) B694255
theorem B1974401 : Blo 614296 1974401 := bstep (se 2 (by rfl) ⟨740400, by rfl⟩ : syracuseStep 1974401 = 1480801) B1480801
theorem B3154135 : Blo 614296 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B1384703 : Blo 614296 1384703 := bstep (se 1 (by rfl) ⟨1038527, by rfl⟩ : syracuseStep 1384703 = 2077055) B2077055
theorem B2007305 : Blo 614296 2007305 := bstep (se 2 (by rfl) ⟨752739, by rfl⟩ : syracuseStep 2007305 = 1505479) B1505479
theorem B2138507 : Blo 614296 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B1384865 : Blo 614296 1384865 := bstep (se 2 (by rfl) ⟨519324, by rfl⟩ : syracuseStep 1384865 = 1038649) B1038649
theorem B926375 : Blo 614296 926375 := bstep (se 1 (by rfl) ⟨694781, by rfl⟩ : syracuseStep 926375 = 1389563) B1389563
theorem B926495 : Blo 614296 926495 := bstep (se 1 (by rfl) ⟨694871, by rfl⟩ : syracuseStep 926495 = 1389743) B1389743
theorem B926519 : Blo 614296 926519 := bstep (se 1 (by rfl) ⟨694889, by rfl⟩ : syracuseStep 926519 = 1389779) B1389779
theorem B2335655 : Blo 614296 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B926699 : Blo 614296 926699 := bstep (se 1 (by rfl) ⟨695024, by rfl⟩ : syracuseStep 926699 = 1390049) B1390049
theorem B1319915 : Blo 614296 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B11969693 : Blo 614296 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B1385639 : Blo 614296 1385639 := bstep (se 1 (by rfl) ⟨1039229, by rfl⟩ : syracuseStep 1385639 = 2078459) B2078459
theorem B1385747 : Blo 614296 1385747 := bstep (se 1 (by rfl) ⟨1039310, by rfl⟩ : syracuseStep 1385747 = 2078621) B2078621
theorem B12035465 : Blo 614296 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B2696647 : Blo 614296 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B1779383 : Blo 614296 1779383 := bstep (se 1 (by rfl) ⟨1334537, by rfl⟩ : syracuseStep 1779383 = 2669075) B2669075
theorem B23406367 : Blo 614296 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B1386377 : Blo 614296 1386377 := bstep (se 2 (by rfl) ⟨519891, by rfl⟩ : syracuseStep 1386377 = 1039783) B1039783
theorem B1386395 : Blo 614296 1386395 := bstep (se 1 (by rfl) ⟨1039796, by rfl⟩ : syracuseStep 1386395 = 2079593) B2079593
theorem B1386431 : Blo 614296 1386431 := bstep (se 1 (by rfl) ⟨1039823, by rfl⟩ : syracuseStep 1386431 = 2079647) B2079647
theorem B2336795 : Blo 614296 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B2566171 : Blo 614296 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B1386593 : Blo 614296 1386593 := bstep (se 2 (by rfl) ⟨519972, by rfl⟩ : syracuseStep 1386593 = 1039945) B1039945
theorem B4434041 : Blo 614296 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B3516605 : Blo 614296 3516605 := bstep (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) B1318727
theorem B7023185 : Blo 614296 7023185 := bstep (se 2 (by rfl) ⟨2633694, by rfl⟩ : syracuseStep 7023185 = 5267389) B5267389
theorem B2075219 : Blo 614296 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B1485395 : Blo 614296 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B1977311 : Blo 614296 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B2337767 : Blo 614296 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B5909669 : Blo 614296 5909669 := bstep (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) B1108063
theorem B1387943 : Blo 614296 1387943 := bstep (se 1 (by rfl) ⟨1040957, by rfl⟩ : syracuseStep 1387943 = 2081915) B2081915
theorem B1388123 : Blo 614296 1388123 := bstep (se 1 (by rfl) ⟨1041092, by rfl⟩ : syracuseStep 1388123 = 2082185) B2082185
theorem B2076407 : Blo 614296 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B2633593 : Blo 614296 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B1388537 : Blo 614296 1388537 := bstep (se 2 (by rfl) ⟨520701, by rfl⟩ : syracuseStep 1388537 = 1041403) B1041403
theorem B1388627 : Blo 614296 1388627 := bstep (se 1 (by rfl) ⟨1041470, by rfl⟩ : syracuseStep 1388627 = 2082941) B2082941
theorem B2633867 : Blo 614296 2633867 := bstep (se 1 (by rfl) ⟨1975400, by rfl⟩ : syracuseStep 2633867 = 3950801) B3950801
theorem B1388807 : Blo 614296 1388807 := bstep (se 1 (by rfl) ⟨1041605, by rfl⟩ : syracuseStep 1388807 = 2083211) B2083211
theorem B2076947 : Blo 614296 2076947 := bstep (se 1 (by rfl) ⟨1557710, by rfl⟩ : syracuseStep 2076947 = 3115421) B3115421
theorem B1978643 : Blo 614296 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B2503067 : Blo 614296 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B1389113 : Blo 614296 1389113 := bstep (se 2 (by rfl) ⟨520917, by rfl⟩ : syracuseStep 1389113 = 1041835) B1041835
theorem B8008429 : Blo 614296 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B2077487 : Blo 614296 2077487 := bstep (se 1 (by rfl) ⟨1558115, by rfl⟩ : syracuseStep 2077487 = 3116231) B3116231
theorem B2437951 : Blo 614296 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B5256251 : Blo 614296 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B5911667 : Blo 614296 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B7910621 : Blo 614296 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B1389833 : Blo 614296 1389833 := bstep (se 2 (by rfl) ⟨521187, by rfl⟩ : syracuseStep 1389833 = 1042375) B1042375
theorem B1389887 : Blo 614296 1389887 := bstep (se 1 (by rfl) ⟨1042415, by rfl⟩ : syracuseStep 1389887 = 2084831) B2084831
theorem B2504009 : Blo 614296 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B1389995 : Blo 614296 1389995 := bstep (se 1 (by rfl) ⟨1042496, by rfl⟩ : syracuseStep 1389995 = 2084993) B2084993
theorem B2078351 : Blo 614296 2078351 := bstep (se 1 (by rfl) ⟨1558763, by rfl⟩ : syracuseStep 2078351 = 3117527) B3117527
theorem B5617309 : Blo 614296 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B1390319 : Blo 614296 1390319 := bstep (se 1 (by rfl) ⟨1042739, by rfl⟩ : syracuseStep 1390319 = 2085479) B2085479
theorem B5257001 : Blo 614296 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B5715841 : Blo 614296 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B1390535 : Blo 614296 1390535 := bstep (se 1 (by rfl) ⟨1042901, by rfl⟩ : syracuseStep 1390535 = 2085803) B2085803
theorem B2078729 : Blo 614296 2078729 := bstep (se 2 (by rfl) ⟨779523, by rfl⟩ : syracuseStep 2078729 = 1559047) B1559047
theorem B1390823 : Blo 614296 1390823 := bstep (se 1 (by rfl) ⟨1043117, by rfl⟩ : syracuseStep 1390823 = 2086235) B2086235
theorem B1390841 : Blo 614296 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B1390895 : Blo 614296 1390895 := bstep (se 1 (by rfl) ⟨1043171, by rfl⟩ : syracuseStep 1390895 = 2086343) B2086343
theorem B2636155 : Blo 614296 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B3520979 : Blo 614296 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B1391111 : Blo 614296 1391111 := bstep (se 1 (by rfl) ⟨1043333, by rfl⟩ : syracuseStep 1391111 = 2086667) B2086667
theorem B2342141 : Blo 614296 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B2080079 : Blo 614296 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B1556435 : Blo 614296 1556435 := bstep (se 1 (by rfl) ⟨1167326, by rfl⟩ : syracuseStep 1556435 = 2334653) B2334653
theorem B1556729 : Blo 614296 1556729 := bstep (se 2 (by rfl) ⟨583773, by rfl⟩ : syracuseStep 1556729 = 1167547) B1167547
theorem B7029017 : Blo 614296 7029017 := bstep (se 2 (by rfl) ⟨2635881, by rfl⟩ : syracuseStep 7029017 = 5271763) B5271763
theorem B14434735 : Blo 614296 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B2343401 : Blo 614296 2343401 := bstep (se 2 (by rfl) ⟨878775, by rfl⟩ : syracuseStep 2343401 = 1757551) B1757551
theorem B2343431 : Blo 614296 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B2966291 : Blo 614296 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1557377 : Blo 614296 1557377 := bstep (se 2 (by rfl) ⟨584016, by rfl⟩ : syracuseStep 1557377 = 1168033) B1168033
theorem B935147 : Blo 614296 935147 := bstep (se 1 (by rfl) ⟨701360, by rfl⟩ : syracuseStep 935147 = 1402721) B1402721
theorem B2377067 : Blo 614296 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B30492197 : Blo 614296 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B1558187 : Blo 614296 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B4671431 : Blo 614296 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B28821851 : Blo 614296 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B2345543 : Blo 614296 2345543 := bstep (se 1 (by rfl) ⟨1759157, by rfl⟩ : syracuseStep 2345543 = 3518315) B3518315
theorem B1755751 : Blo 614296 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B8440523 : Blo 614296 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B1559321 : Blo 614296 1559321 := bstep (se 2 (by rfl) ⟨584745, by rfl⟩ : syracuseStep 1559321 = 1169491) B1169491
theorem B1756025 : Blo 614296 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B2968751 : Blo 614296 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B1166719 : Blo 614296 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B10702631 : Blo 614296 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B1265719 : Blo 614296 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B1167463 : Blo 614296 1167463 := bstep (se 1 (by rfl) ⟨875597, by rfl⟩ : syracuseStep 1167463 = 1751195) B1751195
theorem B2675069 : Blo 614296 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B742303 : Blo 614296 742303 := bstep (se 1 (by rfl) ⟨556727, by rfl⟩ : syracuseStep 742303 = 1113455) B1113455
theorem B2085857 : Blo 614296 2085857 := bstep (se 2 (by rfl) ⟨782196, by rfl⟩ : syracuseStep 2085857 = 1564393) B1564393
theorem B1037407 : Blo 614296 1037407 := bstep (se 1 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 1037407 = 1556111) B1556111
theorem B1561963 : Blo 614296 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B1562399 : Blo 614296 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B1759067 : Blo 614296 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B75979457 : Blo 614296 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B875387 : Blo 614296 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B3169259 : Blo 614296 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B1760399 : Blo 614296 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1039567 : Blo 614296 1039567 := bstep (se 1 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 1039567 = 1559351) B1559351
theorem B60611975 : Blo 614296 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B16867025 : Blo 614296 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B778015 : Blo 614296 778015 := bstep (se 1 (by rfl) ⟨583511, by rfl⟩ : syracuseStep 778015 = 1167023) B1167023
theorem B1564555 : Blo 614296 1564555 := bstep (se 1 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 1564555 = 2346833) B2346833
theorem B614311 : Blo 614296 614311 := bstep (se 1 (by rfl) ⟨460733, by rfl⟩ : syracuseStep 614311 = 921467) B921467
theorem B8314807 : Blo 614296 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B614591 : Blo 614296 614591 := bstep (se 1 (by rfl) ⟨460943, by rfl⟩ : syracuseStep 614591 = 921887) B921887
theorem B614607 : Blo 614296 614607 := bstep (se 1 (by rfl) ⟨460955, by rfl⟩ : syracuseStep 614607 = 921911) B921911
theorem B614655 : Blo 614296 614655 := bstep (se 1 (by rfl) ⟨460991, by rfl⟩ : syracuseStep 614655 = 921983) B921983
theorem B614703 : Blo 614296 614703 := bstep (se 1 (by rfl) ⟨461027, by rfl⟩ : syracuseStep 614703 = 922055) B922055
theorem B614939 : Blo 614296 614939 := bstep (se 1 (by rfl) ⟨461204, by rfl⟩ : syracuseStep 614939 = 922409) B922409
theorem B3007003 : Blo 614296 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B614943 : Blo 614296 614943 := bstep (se 1 (by rfl) ⟨461207, by rfl⟩ : syracuseStep 614943 = 922415) B922415
theorem B615023 : Blo 614296 615023 := bstep (se 1 (by rfl) ⟨461267, by rfl⟩ : syracuseStep 615023 = 922535) B922535
theorem B8872577 : Blo 614296 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B615079 : Blo 614296 615079 := bstep (se 1 (by rfl) ⟨461309, by rfl⟩ : syracuseStep 615079 = 922619) B922619
theorem B615119 : Blo 614296 615119 := bstep (se 1 (by rfl) ⟨461339, by rfl⟩ : syracuseStep 615119 = 922679) B922679
theorem B615199 : Blo 614296 615199 := bstep (se 1 (by rfl) ⟨461399, by rfl⟩ : syracuseStep 615199 = 922799) B922799
theorem B615471 : Blo 614296 615471 := bstep (se 1 (by rfl) ⟨461603, by rfl⟩ : syracuseStep 615471 = 923207) B923207
theorem B779311 : Blo 614296 779311 := bstep (se 1 (by rfl) ⟨584483, by rfl⟩ : syracuseStep 779311 = 1168967) B1168967
theorem B615535 : Blo 614296 615535 := bstep (se 1 (by rfl) ⟨461651, by rfl⟩ : syracuseStep 615535 = 923303) B923303
theorem B615591 : Blo 614296 615591 := bstep (se 1 (by rfl) ⟨461693, by rfl⟩ : syracuseStep 615591 = 923387) B923387
theorem B615615 : Blo 614296 615615 := bstep (se 1 (by rfl) ⟨461711, by rfl⟩ : syracuseStep 615615 = 923423) B923423
theorem B615647 : Blo 614296 615647 := bstep (se 1 (by rfl) ⟨461735, by rfl⟩ : syracuseStep 615647 = 923471) B923471
theorem B615727 : Blo 614296 615727 := bstep (se 1 (by rfl) ⟨461795, by rfl⟩ : syracuseStep 615727 = 923591) B923591
theorem B615963 : Blo 614296 615963 := bstep (se 1 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 615963 = 923945) B923945
theorem B615967 : Blo 614296 615967 := bstep (se 1 (by rfl) ⟨461975, by rfl⟩ : syracuseStep 615967 = 923951) B923951
theorem B616127 : Blo 614296 616127 := bstep (se 1 (by rfl) ⟨462095, by rfl⟩ : syracuseStep 616127 = 924191) B924191
theorem B616383 : Blo 614296 616383 := bstep (se 1 (by rfl) ⟨462287, by rfl⟩ : syracuseStep 616383 = 924575) B924575
theorem B616415 : Blo 614296 616415 := bstep (se 1 (by rfl) ⟨462311, by rfl⟩ : syracuseStep 616415 = 924623) B924623
theorem B23619599 : Blo 614296 23619599 := bstep (se 1 (by rfl) ⟨17714699, by rfl⟩ : syracuseStep 23619599 = 35429399) B35429399
theorem B616475 : Blo 614296 616475 := bstep (se 1 (by rfl) ⟨462356, by rfl⟩ : syracuseStep 616475 = 924713) B924713
theorem B616479 : Blo 614296 616479 := bstep (se 1 (by rfl) ⟨462359, by rfl⟩ : syracuseStep 616479 = 924719) B924719
theorem B616495 : Blo 614296 616495 := bstep (se 1 (by rfl) ⟨462371, by rfl⟩ : syracuseStep 616495 = 924743) B924743
theorem B616671 : Blo 614296 616671 := bstep (se 1 (by rfl) ⟨462503, by rfl⟩ : syracuseStep 616671 = 925007) B925007
theorem B616731 : Blo 614296 616731 := bstep (se 1 (by rfl) ⟨462548, by rfl⟩ : syracuseStep 616731 = 925097) B925097
theorem B616831 : Blo 614296 616831 := bstep (se 1 (by rfl) ⟨462623, by rfl⟩ : syracuseStep 616831 = 925247) B925247
theorem B780779 : Blo 614296 780779 := bstep (se 1 (by rfl) ⟨585584, by rfl⟩ : syracuseStep 780779 = 1171169) B1171169
theorem B617007 : Blo 614296 617007 := bstep (se 1 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 617007 = 925511) B925511
theorem B617063 : Blo 614296 617063 := bstep (se 1 (by rfl) ⟨462797, by rfl⟩ : syracuseStep 617063 = 925595) B925595
theorem B5270123 : Blo 614296 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B617439 : Blo 614296 617439 := bstep (se 1 (by rfl) ⟨463079, by rfl⟩ : syracuseStep 617439 = 926159) B926159
theorem B617467 : Blo 614296 617467 := bstep (se 1 (by rfl) ⟨463100, by rfl⟩ : syracuseStep 617467 = 926201) B926201
theorem B617535 : Blo 614296 617535 := bstep (se 1 (by rfl) ⟨463151, by rfl⟩ : syracuseStep 617535 = 926303) B926303
theorem B1109303 : Blo 614296 1109303 := bstep (se 1 (by rfl) ⟨831977, by rfl⟩ : syracuseStep 1109303 = 1663955) B1663955
theorem B617855 : Blo 614296 617855 := bstep (se 1 (by rfl) ⟨463391, by rfl⟩ : syracuseStep 617855 = 926783) B926783
theorem B617883 : Blo 614296 617883 := bstep (se 1 (by rfl) ⟨463412, by rfl⟩ : syracuseStep 617883 = 926825) B926825
theorem B617951 : Blo 614296 617951 := bstep (se 1 (by rfl) ⟨463463, by rfl⟩ : syracuseStep 617951 = 926927) B926927
theorem B618087 : Blo 614296 618087 := bstep (se 1 (by rfl) ⟨463565, by rfl⟩ : syracuseStep 618087 = 927131) B927131
theorem B782075 : Blo 614296 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B618235 : Blo 614296 618235 := bstep (se 1 (by rfl) ⟨463676, by rfl⟩ : syracuseStep 618235 = 927353) B927353
theorem B11235347 : Blo 614296 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B3567635 : Blo 614296 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B1667155 : Blo 614296 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B2224487 : Blo 614296 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B5272037 : Blo 614296 5272037 := bstep (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) B988507
theorem B5927741 : Blo 614296 5927741 := bstep (se 3 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 5927741 = 2222903) B2222903
theorem B1110991 : Blo 614296 1110991 := bstep (se 1 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 1110991 = 1666487) B1666487
theorem B11859007 : Blo 614296 11859007 := bstep (se 1 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 11859007 = 17788511) B17788511
theorem B4683095 : Blo 614296 4683095 := bstep (se 1 (by rfl) ⟨3512321, by rfl⟩ : syracuseStep 4683095 = 7024643) B7024643
theorem B1668563 : Blo 614296 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B7108667 : Blo 614296 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B15759521 : Blo 614296 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B2817305 : Blo 614296 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B13369063 : Blo 614296 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B9994043 : Blo 614296 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B4686011 : Blo 614296 4686011 := bstep (se 1 (by rfl) ⟨3514508, by rfl⟩ : syracuseStep 4686011 = 7029017) B7029017
theorem B3114287 : Blo 614296 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B1968391 : Blo 614296 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B14420285 : Blo 614296 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B2492947 : Blo 614296 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B2493725 : Blo 614296 2493725 := bstep (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) B935147
theorem B921593 : Blo 614296 921593 := bstep (se 2 (by rfl) ⟨345597, by rfl⟩ : syracuseStep 921593 = 691195) B691195
theorem B921791 : Blo 614296 921791 := bstep (se 1 (by rfl) ⟨691343, by rfl⟩ : syracuseStep 921791 = 1382687) B1382687
theorem B921833 : Blo 614296 921833 := bstep (se 2 (by rfl) ⟨345687, by rfl⟩ : syracuseStep 921833 = 691375) B691375
theorem B921959 : Blo 614296 921959 := bstep (se 1 (by rfl) ⟨691469, by rfl⟩ : syracuseStep 921959 = 1382939) B1382939
theorem B2626177 : Blo 614296 2626177 := bstep (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) B1969633
theorem B40407983 : Blo 614296 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B11244683 : Blo 614296 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B3511457 : Blo 614296 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B922793 : Blo 614296 922793 := bstep (se 2 (by rfl) ⟨346047, by rfl⟩ : syracuseStep 922793 = 692095) B692095
theorem B922859 : Blo 614296 922859 := bstep (se 1 (by rfl) ⟨692144, by rfl⟩ : syracuseStep 922859 = 1384289) B1384289
theorem B1053931 : Blo 614296 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B922943 : Blo 614296 922943 := bstep (se 1 (by rfl) ⟨692207, by rfl⟩ : syracuseStep 922943 = 1384415) B1384415
theorem B1316267 : Blo 614296 1316267 := bstep (se 1 (by rfl) ⟨987200, by rfl⟩ : syracuseStep 1316267 = 1974401) B1974401
theorem B923135 : Blo 614296 923135 := bstep (se 1 (by rfl) ⟨692351, by rfl⟩ : syracuseStep 923135 = 1384703) B1384703
theorem B923243 : Blo 614296 923243 := bstep (se 1 (by rfl) ⟨692432, by rfl⟩ : syracuseStep 923243 = 1384865) B1384865
theorem B923513 : Blo 614296 923513 := bstep (se 2 (by rfl) ⟨346317, by rfl⟩ : syracuseStep 923513 = 692635) B692635
theorem B923759 : Blo 614296 923759 := bstep (se 1 (by rfl) ⟨692819, by rfl⟩ : syracuseStep 923759 = 1385639) B1385639
theorem B923831 : Blo 614296 923831 := bstep (se 1 (by rfl) ⟨692873, by rfl⟩ : syracuseStep 923831 = 1385747) B1385747
theorem B3250601 : Blo 614296 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B1186255 : Blo 614296 1186255 := bstep (se 1 (by rfl) ⟨889691, by rfl⟩ : syracuseStep 1186255 = 1779383) B1779383
theorem B924251 : Blo 614296 924251 := bstep (se 1 (by rfl) ⟨693188, by rfl⟩ : syracuseStep 924251 = 1386377) B1386377
theorem B924263 : Blo 614296 924263 := bstep (se 1 (by rfl) ⟨693197, by rfl⟩ : syracuseStep 924263 = 1386395) B1386395
theorem B1481321 : Blo 614296 1481321 := bstep (se 2 (by rfl) ⟨555495, by rfl⟩ : syracuseStep 1481321 = 1110991) B1110991
theorem B924287 : Blo 614296 924287 := bstep (se 1 (by rfl) ⟨693215, by rfl⟩ : syracuseStep 924287 = 1386431) B1386431
theorem B924395 : Blo 614296 924395 := bstep (se 1 (by rfl) ⟨693296, by rfl⟩ : syracuseStep 924395 = 1386593) B1386593
theorem B2956027 : Blo 614296 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B924425 : Blo 614296 924425 := bstep (se 2 (by rfl) ⟨346659, by rfl⟩ : syracuseStep 924425 = 693319) B693319
theorem B1383209 : Blo 614296 1383209 := bstep (se 2 (by rfl) ⟨518703, by rfl⟩ : syracuseStep 1383209 = 1037407) B1037407
theorem B924665 : Blo 614296 924665 := bstep (se 2 (by rfl) ⟨346749, by rfl⟩ : syracuseStep 924665 = 693499) B693499
theorem B1383479 : Blo 614296 1383479 := bstep (se 1 (by rfl) ⟨1037609, by rfl⟩ : syracuseStep 1383479 = 2075219) B2075219
theorem B990263 : Blo 614296 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B3513415 : Blo 614296 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B1318207 : Blo 614296 1318207 := bstep (se 1 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 1318207 = 1977311) B1977311
theorem B3939779 : Blo 614296 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B4988465 : Blo 614296 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B925295 : Blo 614296 925295 := bstep (se 1 (by rfl) ⟨693971, by rfl⟩ : syracuseStep 925295 = 1387943) B1387943
theorem B2334365 : Blo 614296 2334365 := bstep (se 3 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 2334365 = 875387) B875387
theorem B925415 : Blo 614296 925415 := bstep (se 1 (by rfl) ⟨694061, by rfl⟩ : syracuseStep 925415 = 1388123) B1388123
theorem B1384271 : Blo 614296 1384271 := bstep (se 1 (by rfl) ⟨1038203, by rfl⟩ : syracuseStep 1384271 = 2076407) B2076407
theorem B925691 : Blo 614296 925691 := bstep (se 1 (by rfl) ⟨694268, by rfl⟩ : syracuseStep 925691 = 1388537) B1388537
theorem B925751 : Blo 614296 925751 := bstep (se 1 (by rfl) ⟨694313, by rfl⟩ : syracuseStep 925751 = 1388627) B1388627
theorem B925871 : Blo 614296 925871 := bstep (se 1 (by rfl) ⟨694403, by rfl⟩ : syracuseStep 925871 = 1388807) B1388807
theorem B1384631 : Blo 614296 1384631 := bstep (se 1 (by rfl) ⟨1038473, by rfl⟩ : syracuseStep 1384631 = 2076947) B2076947
theorem B1319095 : Blo 614296 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B1482991 : Blo 614296 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B3514691 : Blo 614296 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B926075 : Blo 614296 926075 := bstep (se 1 (by rfl) ⟨694556, by rfl⟩ : syracuseStep 926075 = 1389113) B1389113
theorem B3514873 : Blo 614296 3514873 := bstep (se 2 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 3514873 = 2636155) B2636155
theorem B1384991 : Blo 614296 1384991 := bstep (se 1 (by rfl) ⟨1038743, by rfl⟩ : syracuseStep 1384991 = 2077487) B2077487
theorem B926249 : Blo 614296 926249 := bstep (se 2 (by rfl) ⟨347343, by rfl⟩ : syracuseStep 926249 = 694687) B694687
theorem B926345 : Blo 614296 926345 := bstep (se 2 (by rfl) ⟨347379, by rfl⟩ : syracuseStep 926345 = 694759) B694759
theorem B3941111 : Blo 614296 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B926555 : Blo 614296 926555 := bstep (se 1 (by rfl) ⟨694916, by rfl⟩ : syracuseStep 926555 = 1389833) B1389833
theorem B926591 : Blo 614296 926591 := bstep (se 1 (by rfl) ⟨694943, by rfl⟩ : syracuseStep 926591 = 1389887) B1389887
theorem B3122063 : Blo 614296 3122063 := bstep (se 1 (by rfl) ⟨2341547, by rfl⟩ : syracuseStep 3122063 = 4683095) B4683095
theorem B926663 : Blo 614296 926663 := bstep (se 1 (by rfl) ⟨694997, by rfl⟩ : syracuseStep 926663 = 1389995) B1389995
theorem B1385567 : Blo 614296 1385567 := bstep (se 1 (by rfl) ⟨1039175, by rfl⟩ : syracuseStep 1385567 = 2078351) B2078351
theorem B926879 : Blo 614296 926879 := bstep (se 1 (by rfl) ⟨695159, by rfl⟩ : syracuseStep 926879 = 1390319) B1390319
theorem B927023 : Blo 614296 927023 := bstep (se 1 (by rfl) ⟨695267, by rfl⟩ : syracuseStep 927023 = 1390535) B1390535
theorem B1385819 : Blo 614296 1385819 := bstep (se 1 (by rfl) ⟨1039364, by rfl⟩ : syracuseStep 1385819 = 2078729) B2078729
theorem B927215 : Blo 614296 927215 := bstep (se 1 (by rfl) ⟨695411, by rfl⟩ : syracuseStep 927215 = 1390823) B1390823
theorem B927227 : Blo 614296 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B5907977 : Blo 614296 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B927263 : Blo 614296 927263 := bstep (se 1 (by rfl) ⟨695447, by rfl⟩ : syracuseStep 927263 = 1390895) B1390895
theorem B1386089 : Blo 614296 1386089 := bstep (se 2 (by rfl) ⟨519783, by rfl⟩ : syracuseStep 1386089 = 1039567) B1039567
theorem B927407 : Blo 614296 927407 := bstep (se 1 (by rfl) ⟨695555, by rfl⟩ : syracuseStep 927407 = 1391111) B1391111
theorem B26650781 : Blo 614296 26650781 := bstep (se 3 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 26650781 = 9994043) B9994043
theorem B1878203 : Blo 614296 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B1386719 : Blo 614296 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B11086409 : Blo 614296 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B4205513 : Blo 614296 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B18918521 : Blo 614296 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B1977527 : Blo 614296 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B19246313 : Blo 614296 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B4009337 : Blo 614296 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B15216133 : Blo 614296 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B20328131 : Blo 614296 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B19214567 : Blo 614296 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B1979167 : Blo 614296 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1749919 : Blo 614296 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B31208489 : Blo 614296 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B3519773 : Blo 614296 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1783379 : Blo 614296 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B1390571 : Blo 614296 1390571 := bstep (se 1 (by rfl) ⟨1042928, by rfl⟩ : syracuseStep 1390571 = 2085857) B2085857
theorem B2341001 : Blo 614296 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B6338845 : Blo 614296 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1751503 : Blo 614296 1751503 := bstep (se 1 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 1751503 = 2627255) B2627255
theorem B2079323 : Blo 614296 2079323 := bstep (se 1 (by rfl) ⟨1559492, by rfl⟩ : syracuseStep 2079323 = 3118985) B3118985
theorem B1555625 : Blo 614296 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B2112839 : Blo 614296 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B4439519 : Blo 614296 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B13352455 : Blo 614296 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B1687625 : Blo 614296 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B1556617 : Blo 614296 1556617 := bstep (se 2 (by rfl) ⟨583731, by rfl⟩ : syracuseStep 1556617 = 1167463) B1167463
theorem B1425671 : Blo 614296 1425671 := bstep (se 1 (by rfl) ⟨1069253, by rfl⟩ : syracuseStep 1425671 = 2138507) B2138507
theorem B5915051 : Blo 614296 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B1557103 : Blo 614296 1557103 := bstep (se 1 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 1557103 = 2335655) B2335655
theorem B7979795 : Blo 614296 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B2082077 : Blo 614296 2082077 := bstep (se 3 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 2082077 = 780779) B780779
theorem B15746399 : Blo 614296 15746399 := bstep (se 1 (by rfl) ⟨11809799, by rfl⟩ : syracuseStep 15746399 = 23619599) B23619599
theorem B1557863 : Blo 614296 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B15812009 : Blo 614296 15812009 := bstep (se 2 (by rfl) ⟨5929503, by rfl⟩ : syracuseStep 15812009 = 11859007) B11859007
theorem B2344403 : Blo 614296 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B2082617 : Blo 614296 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B1558511 : Blo 614296 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B739535 : Blo 614296 739535 := bstep (se 1 (by rfl) ⟨554651, by rfl⟩ : syracuseStep 739535 = 1109303) B1109303
theorem B7489745 : Blo 614296 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B7621121 : Blo 614296 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B7490231 : Blo 614296 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B2378423 : Blo 614296 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B3951341 : Blo 614296 3951341 := bstep (se 3 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 3951341 = 1481753) B1481753
theorem B1755911 : Blo 614296 1755911 := bstep (se 1 (by rfl) ⟨1316933, by rfl⟩ : syracuseStep 1755911 = 2633867) B2633867
theorem B3951827 : Blo 614296 3951827 := bstep (se 1 (by rfl) ⟨2963870, by rfl⟩ : syracuseStep 3951827 = 5927741) B5927741
theorem B4739111 : Blo 614296 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B10506347 : Blo 614296 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B2347319 : Blo 614296 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B2085533 : Blo 614296 2085533 := bstep (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) B782075
theorem B1561427 : Blo 614296 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1037353 : Blo 614296 1037353 := bstep (se 2 (by rfl) ⟨389007, by rfl⟩ : syracuseStep 1037353 = 778015) B778015
theorem B2086073 : Blo 614296 2086073 := bstep (se 2 (by rfl) ⟨782277, by rfl⟩ : syracuseStep 2086073 = 1564555) B1564555
theorem B1037623 : Blo 614296 1037623 := bstep (se 1 (by rfl) ⟨778217, by rfl⟩ : syracuseStep 1037623 = 1556435) B1556435
theorem B18044315 : Blo 614296 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B13686245 : Blo 614296 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B1037819 : Blo 614296 1037819 := bstep (se 1 (by rfl) ⟨778364, by rfl⟩ : syracuseStep 1037819 = 1556729) B1556729
theorem B1660495 : Blo 614296 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1562267 : Blo 614296 1562267 := bstep (se 1 (by rfl) ⟨1171700, by rfl⟩ : syracuseStep 1562267 = 2343401) B2343401
theorem B1562287 : Blo 614296 1562287 := bstep (se 1 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 1562287 = 2343431) B2343431
theorem B1038251 : Blo 614296 1038251 := bstep (se 1 (by rfl) ⟨778688, by rfl⟩ : syracuseStep 1038251 = 1557377) B1557377
theorem B6674845 : Blo 614296 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B1038791 : Blo 614296 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B1039081 : Blo 614296 1039081 := bstep (se 2 (by rfl) ⟨389655, by rfl⟩ : syracuseStep 1039081 = 779311) B779311
theorem B1563695 : Blo 614296 1563695 := bstep (se 1 (by rfl) ⟨1172771, by rfl⟩ : syracuseStep 1563695 = 2345543) B2345543
theorem B5627015 : Blo 614296 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B1039547 : Blo 614296 1039547 := bstep (se 1 (by rfl) ⟨779660, by rfl⟩ : syracuseStep 1039547 = 1559321) B1559321
theorem B1170683 : Blo 614296 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B3595529 : Blo 614296 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B7822817 : Blo 614296 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B614383 : Blo 614296 614383 := bstep (se 1 (by rfl) ⟨460787, by rfl⟩ : syracuseStep 614383 = 921575) B921575
theorem B614463 : Blo 614296 614463 := bstep (se 1 (by rfl) ⟨460847, by rfl⟩ : syracuseStep 614463 = 921695) B921695
theorem B614471 : Blo 614296 614471 := bstep (se 1 (by rfl) ⟨460853, by rfl⟩ : syracuseStep 614471 = 921707) B921707
theorem B614503 : Blo 614296 614503 := bstep (se 1 (by rfl) ⟨460877, by rfl⟩ : syracuseStep 614503 = 921755) B921755
theorem B5267663 : Blo 614296 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B615071 : Blo 614296 615071 := bstep (se 1 (by rfl) ⟨461303, by rfl⟩ : syracuseStep 615071 = 922607) B922607
theorem B615327 : Blo 614296 615327 := bstep (se 1 (by rfl) ⟨461495, by rfl⟩ : syracuseStep 615327 = 922991) B922991
theorem B615407 : Blo 614296 615407 := bstep (se 1 (by rfl) ⟨461555, by rfl⟩ : syracuseStep 615407 = 923111) B923111
theorem B1401911 : Blo 614296 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B615515 : Blo 614296 615515 := bstep (se 1 (by rfl) ⟨461636, by rfl⟩ : syracuseStep 615515 = 923273) B923273
theorem B615527 : Blo 614296 615527 := bstep (se 1 (by rfl) ⟨461645, by rfl⟩ : syracuseStep 615527 = 923291) B923291
theorem B1041599 : Blo 614296 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B615655 : Blo 614296 615655 := bstep (se 1 (by rfl) ⟨461741, by rfl⟩ : syracuseStep 615655 = 923483) B923483
theorem B1172711 : Blo 614296 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B615911 : Blo 614296 615911 := bstep (se 1 (by rfl) ⟨461933, by rfl⟩ : syracuseStep 615911 = 923867) B923867
theorem B616091 : Blo 614296 616091 := bstep (se 1 (by rfl) ⟨462068, by rfl⟩ : syracuseStep 616091 = 924137) B924137
theorem B50652971 : Blo 614296 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B616351 : Blo 614296 616351 := bstep (se 1 (by rfl) ⟨462263, by rfl⟩ : syracuseStep 616351 = 924527) B924527
theorem B616359 : Blo 614296 616359 := bstep (se 1 (by rfl) ⟨462269, by rfl⟩ : syracuseStep 616359 = 924539) B924539
theorem B1173599 : Blo 614296 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B3958949 : Blo 614296 3958949 := bstep (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) B742303
theorem B616935 : Blo 614296 616935 := bstep (se 1 (by rfl) ⟨462701, by rfl⟩ : syracuseStep 616935 = 925403) B925403
theorem B617115 : Blo 614296 617115 := bstep (se 1 (by rfl) ⟨462836, by rfl⟩ : syracuseStep 617115 = 925673) B925673
theorem B2222873 : Blo 614296 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B1338203 : Blo 614296 1338203 := bstep (se 1 (by rfl) ⟨1003652, by rfl⟩ : syracuseStep 1338203 = 2007305) B2007305
theorem B617583 : Blo 614296 617583 := bstep (se 1 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 617583 = 926375) B926375
theorem B617663 : Blo 614296 617663 := bstep (se 1 (by rfl) ⟨463247, by rfl⟩ : syracuseStep 617663 = 926495) B926495
theorem B617679 : Blo 614296 617679 := bstep (se 1 (by rfl) ⟨463259, by rfl⟩ : syracuseStep 617679 = 926519) B926519
theorem B617799 : Blo 614296 617799 := bstep (se 1 (by rfl) ⟨463349, by rfl⟩ : syracuseStep 617799 = 926699) B926699
theorem B8023643 : Blo 614296 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B10677905 : Blo 614296 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B4682123 : Blo 614296 4682123 := bstep (se 1 (by rfl) ⟨3511592, by rfl⟩ : syracuseStep 4682123 = 7023185) B7023185
theorem B3504167 : Blo 614296 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B5273747 : Blo 614296 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B1669339 : Blo 614296 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B3111209 : Blo 614296 3111209 := bstep (se 2 (by rfl) ⟨1166703, by rfl⟩ : syracuseStep 3111209 = 2333407) B2333407
theorem B1112375 : Blo 614296 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B3504667 : Blo 614296 3504667 := bstep (se 1 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 3504667 = 5257001) B5257001
theorem B28540349 : Blo 614296 28540349 := bstep (se 3 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 28540349 = 10702631) B10702631
theorem B17825417 : Blo 614296 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B950447 : Blo 614296 950447 := bstep (se 1 (by rfl) ⟨712835, by rfl⟩ : syracuseStep 950447 = 1425671) B1425671
theorem B4686497 : Blo 614296 4686497 := bstep (se 2 (by rfl) ⟨1757436, by rfl⟩ : syracuseStep 4686497 = 3514873) B3514873
theorem B5080747 : Blo 614296 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B2624521 : Blo 614296 2624521 := bstep (se 2 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 2624521 = 1968391) B1968391
theorem B29985821 : Blo 614296 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B26938655 : Blo 614296 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B12029543 : Blo 614296 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B691879 : Blo 614296 691879 := bstep (se 1 (by rfl) ⟨518909, by rfl⟩ : syracuseStep 691879 = 1037819) B1037819
theorem B692167 : Blo 614296 692167 := bstep (se 1 (by rfl) ⟨519125, by rfl⟩ : syracuseStep 692167 = 1038251) B1038251
theorem B2167067 : Blo 614296 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B692527 : Blo 614296 692527 := bstep (se 1 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 692527 = 1038791) B1038791
theorem B987547 : Blo 614296 987547 := bstep (se 1 (by rfl) ⟨740660, by rfl⟩ : syracuseStep 987547 = 1481321) B1481321
theorem B922139 : Blo 614296 922139 := bstep (se 1 (by rfl) ⟨691604, by rfl⟩ : syracuseStep 922139 = 1383209) B1383209
theorem B20288177 : Blo 614296 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B922319 : Blo 614296 922319 := bstep (se 1 (by rfl) ⟨691739, by rfl⟩ : syracuseStep 922319 = 1383479) B1383479
theorem B693031 : Blo 614296 693031 := bstep (se 1 (by rfl) ⟨519773, by rfl⟩ : syracuseStep 693031 = 1039547) B1039547
theorem B2397019 : Blo 614296 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B2626519 : Blo 614296 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B5215211 : Blo 614296 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B922847 : Blo 614296 922847 := bstep (se 1 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 922847 = 1384271) B1384271
theorem B923087 : Blo 614296 923087 := bstep (se 1 (by rfl) ⟨692315, by rfl⟩ : syracuseStep 923087 = 1384631) B1384631
theorem B3511775 : Blo 614296 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B923327 : Blo 614296 923327 := bstep (se 1 (by rfl) ⟨692495, by rfl⟩ : syracuseStep 923327 = 1384991) B1384991
theorem B2627407 : Blo 614296 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B923711 : Blo 614296 923711 := bstep (se 1 (by rfl) ⟨692783, by rfl⟩ : syracuseStep 923711 = 1385567) B1385567
theorem B694399 : Blo 614296 694399 := bstep (se 1 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 694399 = 1041599) B1041599
theorem B923879 : Blo 614296 923879 := bstep (se 1 (by rfl) ⟨692909, by rfl⟩ : syracuseStep 923879 = 1385819) B1385819
theorem B3938651 : Blo 614296 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B924059 : Blo 614296 924059 := bstep (se 1 (by rfl) ⟨693044, by rfl⟩ : syracuseStep 924059 = 1386089) B1386089
theorem B2333225 : Blo 614296 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1383137 : Blo 614296 1383137 := bstep (se 2 (by rfl) ⟨518676, by rfl⟩ : syracuseStep 1383137 = 1037353) B1037353
theorem B17767187 : Blo 614296 17767187 := bstep (se 1 (by rfl) ⟨13325390, by rfl⟩ : syracuseStep 17767187 = 26650781) B26650781
theorem B1252135 : Blo 614296 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B924479 : Blo 614296 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B1383497 : Blo 614296 1383497 := bstep (se 2 (by rfl) ⟨518811, by rfl⟩ : syracuseStep 1383497 = 1037623) B1037623
theorem B1481915 : Blo 614296 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B892135 : Blo 614296 892135 := bstep (se 1 (by rfl) ⟨669101, by rfl⟩ : syracuseStep 892135 = 1338203) B1338203
theorem B1318351 : Blo 614296 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B5349095 : Blo 614296 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B7118603 : Blo 614296 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B3121415 : Blo 614296 3121415 := bstep (se 1 (by rfl) ⟨2341061, by rfl⟩ : syracuseStep 3121415 = 4682123) B4682123
theorem B2335337 : Blo 614296 2335337 := bstep (se 2 (by rfl) ⟨875751, by rfl⟩ : syracuseStep 2335337 = 1751503) B1751503
theorem B1581673 : Blo 614296 1581673 := bstep (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) B1186255
theorem B1385441 : Blo 614296 1385441 := bstep (se 2 (by rfl) ⟨519540, by rfl⟩ : syracuseStep 1385441 = 1039081) B1039081
theorem B3941369 : Blo 614296 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B1188919 : Blo 614296 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B927047 : Blo 614296 927047 := bstep (se 1 (by rfl) ⟨695285, by rfl⟩ : syracuseStep 927047 = 1390571) B1390571
theorem B2336111 : Blo 614296 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B3515831 : Blo 614296 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B2074139 : Blo 614296 2074139 := bstep (se 1 (by rfl) ⟨1555604, by rfl⟩ : syracuseStep 2074139 = 3111209) B3111209
theorem B1386215 : Blo 614296 1386215 := bstep (se 1 (by rfl) ⟨1039661, by rfl⟩ : syracuseStep 1386215 = 2079323) B2079323
theorem B54208349 : Blo 614296 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B17803273 : Blo 614296 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B2959679 : Blo 614296 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B1125083 : Blo 614296 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B3124007 : Blo 614296 3124007 := bstep (se 1 (by rfl) ⟨2343005, by rfl⟩ : syracuseStep 3124007 = 4686011) B4686011
theorem B2075489 : Blo 614296 2075489 := bstep (se 2 (by rfl) ⟨778308, by rfl⟩ : syracuseStep 2075489 = 1556617) B1556617
theorem B3943367 : Blo 614296 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B5319863 : Blo 614296 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B2076137 : Blo 614296 2076137 := bstep (se 2 (by rfl) ⟨778551, by rfl⟩ : syracuseStep 2076137 = 1557103) B1557103
theorem B1388051 : Blo 614296 1388051 := bstep (se 1 (by rfl) ⟨1041038, by rfl⟩ : syracuseStep 1388051 = 2082077) B2082077
theorem B2076191 : Blo 614296 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B10497599 : Blo 614296 10497599 := bstep (se 1 (by rfl) ⟨7873199, by rfl⟩ : syracuseStep 10497599 = 15746399) B15746399
theorem B1388411 : Blo 614296 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B7909285 : Blo 614296 7909285 := bstep (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) B1482991
theorem B4993163 : Blo 614296 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B9613523 : Blo 614296 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B4993487 : Blo 614296 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B2634227 : Blo 614296 2634227 := bstep (se 1 (by rfl) ⟨1975670, by rfl⟩ : syracuseStep 2634227 = 3951341) B3951341
theorem B2634551 : Blo 614296 2634551 := bstep (se 1 (by rfl) ⟨1975913, by rfl⟩ : syracuseStep 2634551 = 3951827) B3951827
theorem B3159407 : Blo 614296 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1390355 : Blo 614296 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B3323929 : Blo 614296 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B2340971 : Blo 614296 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B1390715 : Blo 614296 1390715 := bstep (se 1 (by rfl) ⟨1043036, by rfl⟩ : syracuseStep 1390715 = 2086073) B2086073
theorem B9124163 : Blo 614296 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B3751343 : Blo 614296 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B3325643 : Blo 614296 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B1556243 : Blo 614296 1556243 := bstep (se 1 (by rfl) ⟨1167182, by rfl⟩ : syracuseStep 1556243 = 2334365) B2334365
theorem B2343127 : Blo 614296 2343127 := bstep (se 1 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 2343127 = 3514691) B3514691
theorem B2081375 : Blo 614296 2081375 := bstep (se 1 (by rfl) ⟨1561031, by rfl⟩ : syracuseStep 2081375 = 3122063) B3122063
theorem B934607 : Blo 614296 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B2638889 : Blo 614296 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B33768647 : Blo 614296 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B2639299 : Blo 614296 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B7390939 : Blo 614296 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B6342461 : Blo 614296 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B2803675 : Blo 614296 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B2213993 : Blo 614296 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B12830875 : Blo 614296 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B2083049 : Blo 614296 2083049 := bstep (se 2 (by rfl) ⟨781143, by rfl⟩ : syracuseStep 2083049 = 1562287) B1562287
theorem B2672891 : Blo 614296 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B2640701 : Blo 614296 2640701 := bstep (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) B990263
theorem B8899793 : Blo 614296 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B4672889 : Blo 614296 4672889 := bstep (se 2 (by rfl) ⟨1752333, by rfl⟩ : syracuseStep 4672889 = 3504667) B3504667
theorem B2346515 : Blo 614296 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B1560667 : Blo 614296 1560667 := bstep (se 1 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 1560667 = 2341001) B2341001
theorem B741583 : Blo 614296 741583 := bstep (se 1 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 741583 = 1112375) B1112375
theorem B1757609 : Blo 614296 1757609 := bstep (se 2 (by rfl) ⟨659103, by rfl⟩ : syracuseStep 1757609 = 1318207) B1318207
theorem B1037083 : Blo 614296 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B19026899 : Blo 614296 19026899 := bstep (se 1 (by rfl) ⟨14270174, by rfl⟩ : syracuseStep 19026899 = 28540349) B28540349
theorem B11883611 : Blo 614296 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B1758793 : Blo 614296 1758793 := bstep (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) B1319095
theorem B1038575 : Blo 614296 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B10541339 : Blo 614296 10541339 := bstep (se 1 (by rfl) ⟨7906004, by rfl⟩ : syracuseStep 10541339 = 15812009) B15812009
theorem B1562935 : Blo 614296 1562935 := bstep (se 1 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 1562935 = 2344403) B2344403
theorem B8903141 : Blo 614296 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B1039007 : Blo 614296 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B1170607 : Blo 614296 1170607 := bstep (se 1 (by rfl) ⟨877955, by rfl⟩ : syracuseStep 1170607 = 1755911) B1755911
theorem B7888373 : Blo 614296 7888373 := bstep (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) B739535
theorem B614395 : Blo 614296 614395 := bstep (se 1 (by rfl) ⟨460796, by rfl⟩ : syracuseStep 614395 = 921593) B921593
theorem B7004231 : Blo 614296 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B614527 : Blo 614296 614527 := bstep (se 1 (by rfl) ⟨460895, by rfl⟩ : syracuseStep 614527 = 921791) B921791
theorem B614555 : Blo 614296 614555 := bstep (se 1 (by rfl) ⟨460916, by rfl⟩ : syracuseStep 614555 = 921833) B921833
theorem B1564879 : Blo 614296 1564879 := bstep (se 1 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 1564879 = 2347319) B2347319
theorem B614639 : Blo 614296 614639 := bstep (se 1 (by rfl) ⟨460979, by rfl⟩ : syracuseStep 614639 = 921959) B921959
theorem B1040951 : Blo 614296 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B615195 : Blo 614296 615195 := bstep (se 1 (by rfl) ⟨461396, by rfl⟩ : syracuseStep 615195 = 922793) B922793
theorem B615239 : Blo 614296 615239 := bstep (se 1 (by rfl) ⟨461429, by rfl⟩ : syracuseStep 615239 = 922859) B922859
theorem B615295 : Blo 614296 615295 := bstep (se 1 (by rfl) ⟨461471, by rfl⟩ : syracuseStep 615295 = 922943) B922943
theorem B877511 : Blo 614296 877511 := bstep (se 1 (by rfl) ⟨658133, by rfl⟩ : syracuseStep 877511 = 1316267) B1316267
theorem B615423 : Blo 614296 615423 := bstep (se 1 (by rfl) ⟨461567, by rfl⟩ : syracuseStep 615423 = 923135) B923135
theorem B615495 : Blo 614296 615495 := bstep (se 1 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 615495 = 923243) B923243
theorem B1041511 : Blo 614296 1041511 := bstep (se 1 (by rfl) ⟨781133, by rfl⟩ : syracuseStep 1041511 = 1562267) B1562267
theorem B615675 : Blo 614296 615675 := bstep (se 1 (by rfl) ⟨461756, by rfl⟩ : syracuseStep 615675 = 923513) B923513
theorem B615839 : Blo 614296 615839 := bstep (se 1 (by rfl) ⟨461879, by rfl⟩ : syracuseStep 615839 = 923759) B923759
theorem B615887 : Blo 614296 615887 := bstep (se 1 (by rfl) ⟨461915, by rfl⟩ : syracuseStep 615887 = 923831) B923831
theorem B616167 : Blo 614296 616167 := bstep (se 1 (by rfl) ⟨462125, by rfl⟩ : syracuseStep 616167 = 924251) B924251
theorem B616175 : Blo 614296 616175 := bstep (se 1 (by rfl) ⟨462131, by rfl⟩ : syracuseStep 616175 = 924263) B924263
theorem B616191 : Blo 614296 616191 := bstep (se 1 (by rfl) ⟨462143, by rfl⟩ : syracuseStep 616191 = 924287) B924287
theorem B616263 : Blo 614296 616263 := bstep (se 1 (by rfl) ⟨462197, by rfl⟩ : syracuseStep 616263 = 924395) B924395
theorem B616283 : Blo 614296 616283 := bstep (se 1 (by rfl) ⟨462212, by rfl⟩ : syracuseStep 616283 = 924425) B924425
theorem B616443 : Blo 614296 616443 := bstep (se 1 (by rfl) ⟨462332, by rfl⟩ : syracuseStep 616443 = 924665) B924665
theorem B1042463 : Blo 614296 1042463 := bstep (se 1 (by rfl) ⟨781847, by rfl⟩ : syracuseStep 1042463 = 1563695) B1563695
theorem B780455 : Blo 614296 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B616863 : Blo 614296 616863 := bstep (se 1 (by rfl) ⟨462647, by rfl⟩ : syracuseStep 616863 = 925295) B925295
theorem B616943 : Blo 614296 616943 := bstep (se 1 (by rfl) ⟨462707, by rfl⟩ : syracuseStep 616943 = 925415) B925415
theorem B617127 : Blo 614296 617127 := bstep (se 1 (by rfl) ⟨462845, by rfl⟩ : syracuseStep 617127 = 925691) B925691
theorem B617167 : Blo 614296 617167 := bstep (se 1 (by rfl) ⟨462875, by rfl⟩ : syracuseStep 617167 = 925751) B925751
theorem B617247 : Blo 614296 617247 := bstep (se 1 (by rfl) ⟨462935, by rfl⟩ : syracuseStep 617247 = 925871) B925871
theorem B617383 : Blo 614296 617383 := bstep (se 1 (by rfl) ⟨463037, by rfl⟩ : syracuseStep 617383 = 926075) B926075
theorem B617499 : Blo 614296 617499 := bstep (se 1 (by rfl) ⟨463124, by rfl⟩ : syracuseStep 617499 = 926249) B926249
theorem B617563 : Blo 614296 617563 := bstep (se 1 (by rfl) ⟨463172, by rfl⟩ : syracuseStep 617563 = 926345) B926345
theorem B617703 : Blo 614296 617703 := bstep (se 1 (by rfl) ⟨463277, by rfl⟩ : syracuseStep 617703 = 926555) B926555
theorem B617727 : Blo 614296 617727 := bstep (se 1 (by rfl) ⟨463295, by rfl⟩ : syracuseStep 617727 = 926591) B926591
theorem B617775 : Blo 614296 617775 := bstep (se 1 (by rfl) ⟨463331, by rfl⟩ : syracuseStep 617775 = 926663) B926663
theorem B617919 : Blo 614296 617919 := bstep (se 1 (by rfl) ⟨463439, by rfl⟩ : syracuseStep 617919 = 926879) B926879
theorem B781807 : Blo 614296 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B3501569 : Blo 614296 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B618015 : Blo 614296 618015 := bstep (se 1 (by rfl) ⟨463511, by rfl⟩ : syracuseStep 618015 = 927023) B927023
theorem B618143 : Blo 614296 618143 := bstep (se 1 (by rfl) ⟨463607, by rfl⟩ : syracuseStep 618143 = 927215) B927215
theorem B618151 : Blo 614296 618151 := bstep (se 1 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 618151 = 927227) B927227
theorem B618175 : Blo 614296 618175 := bstep (se 1 (by rfl) ⟨463631, by rfl⟩ : syracuseStep 618175 = 927263) B927263
theorem B618271 : Blo 614296 618271 := bstep (se 1 (by rfl) ⟨463703, by rfl⟩ : syracuseStep 618271 = 927407) B927407
theorem B782399 : Blo 614296 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B1405241 : Blo 614296 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B12612347 : Blo 614296 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B12809711 : Blo 614296 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B8451793 : Blo 614296 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B20805659 : Blo 614296 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B6649933 : Blo 614296 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B4684553 : Blo 614296 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B1408559 : Blo 614296 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B623071 : Blo 614296 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B22512431 : Blo 614296 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B4228307 : Blo 614296 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B1475995 : Blo 614296 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B19990547 : Blo 614296 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B5933195 : Blo 614296 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B17959103 : Blo 614296 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B3115259 : Blo 614296 3115259 := bstep (se 1 (by rfl) ⟨2336444, by rfl⟩ : syracuseStep 3115259 = 4672889) B4672889
theorem B3738233 : Blo 614296 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B1444711 : Blo 614296 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B12684599 : Blo 614296 12684599 := bstep (se 1 (by rfl) ⟨9513449, by rfl⟩ : syracuseStep 12684599 = 19026899) B19026899
theorem B3476807 : Blo 614296 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B692383 : Blo 614296 692383 := bstep (se 1 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 692383 = 1038575) B1038575
theorem B2625767 : Blo 614296 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B5935427 : Blo 614296 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B692671 : Blo 614296 692671 := bstep (se 1 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 692671 = 1039007) B1039007
theorem B922091 : Blo 614296 922091 := bstep (se 1 (by rfl) ⟨691568, by rfl⟩ : syracuseStep 922091 = 1383137) B1383137
theorem B922331 : Blo 614296 922331 := bstep (se 1 (by rfl) ⟨691748, by rfl⟩ : syracuseStep 922331 = 1383497) B1383497
theorem B922505 : Blo 614296 922505 := bstep (se 2 (by rfl) ⟨345939, by rfl⟩ : syracuseStep 922505 = 691879) B691879
theorem B922889 : Blo 614296 922889 := bstep (se 2 (by rfl) ⟨346083, by rfl⟩ : syracuseStep 922889 = 692167) B692167
theorem B988777 : Blo 614296 988777 := bstep (se 2 (by rfl) ⟨370791, by rfl⟩ : syracuseStep 988777 = 741583) B741583
theorem B693967 : Blo 614296 693967 := bstep (se 1 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 693967 = 1040951) B1040951
theorem B923369 : Blo 614296 923369 := bstep (se 2 (by rfl) ⟨346263, by rfl⟩ : syracuseStep 923369 = 692527) B692527
theorem B1316729 : Blo 614296 1316729 := bstep (se 2 (by rfl) ⟨493773, by rfl⟩ : syracuseStep 1316729 = 987547) B987547
theorem B923627 : Blo 614296 923627 := bstep (se 1 (by rfl) ⟨692720, by rfl⟩ : syracuseStep 923627 = 1385441) B1385441
theorem B2627579 : Blo 614296 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B1382759 : Blo 614296 1382759 := bstep (se 1 (by rfl) ⟨1037069, by rfl⟩ : syracuseStep 1382759 = 2074139) B2074139
theorem B1382777 : Blo 614296 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B924041 : Blo 614296 924041 := bstep (se 2 (by rfl) ⟨346515, by rfl⟩ : syracuseStep 924041 = 693031) B693031
theorem B924143 : Blo 614296 924143 := bstep (se 1 (by rfl) ⟨693107, by rfl⟩ : syracuseStep 924143 = 1386215) B1386215
theorem B694975 : Blo 614296 694975 := bstep (se 1 (by rfl) ⟨521231, by rfl⟩ : syracuseStep 694975 = 1042463) B1042463
theorem B1973119 : Blo 614296 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B1383659 : Blo 614296 1383659 := bstep (se 1 (by rfl) ⟨1037744, by rfl⟩ : syracuseStep 1383659 = 2075489) B2075489
theorem B2628911 : Blo 614296 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B3546575 : Blo 614296 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B1384091 : Blo 614296 1384091 := bstep (se 1 (by rfl) ⟨1038068, by rfl⟩ : syracuseStep 1384091 = 2076137) B2076137
theorem B2334379 : Blo 614296 2334379 := bstep (se 1 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 2334379 = 3501569) B3501569
theorem B925367 : Blo 614296 925367 := bstep (se 1 (by rfl) ⟨694025, by rfl⟩ : syracuseStep 925367 = 1388051) B1388051
theorem B1384127 : Blo 614296 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B925607 : Blo 614296 925607 := bstep (se 1 (by rfl) ⟨694205, by rfl⟩ : syracuseStep 925607 = 1388411) B1388411
theorem B4431905 : Blo 614296 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B925865 : Blo 614296 925865 := bstep (se 2 (by rfl) ⟨347199, by rfl⟩ : syracuseStep 925865 = 694399) B694399
theorem B2106271 : Blo 614296 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B926903 : Blo 614296 926903 := bstep (se 1 (by rfl) ⟨695177, by rfl⟩ : syracuseStep 926903 = 1390355) B1390355
theorem B13870439 : Blo 614296 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B927143 : Blo 614296 927143 := bstep (se 1 (by rfl) ⟨695357, by rfl⟩ : syracuseStep 927143 = 1390715) B1390715
theorem B1189513 : Blo 614296 1189513 := bstep (se 2 (by rfl) ⟨446067, by rfl⟩ : syracuseStep 1189513 = 892135) B892135
theorem B3123035 : Blo 614296 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B2500895 : Blo 614296 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B633631 : Blo 614296 633631 := bstep (se 1 (by rfl) ⟨475223, by rfl⟩ : syracuseStep 633631 = 950447) B950447
theorem B3124169 : Blo 614296 3124169 := bstep (se 2 (by rfl) ⟨1171563, by rfl⟩ : syracuseStep 3124169 = 2343127) B2343127
theorem B1387583 : Blo 614296 1387583 := bstep (se 1 (by rfl) ⟨1040687, by rfl⟩ : syracuseStep 1387583 = 2081375) B2081375
theorem B3124331 : Blo 614296 3124331 := bstep (se 1 (by rfl) ⟨2343248, by rfl⟩ : syracuseStep 3124331 = 4686497) B4686497
theorem B25636061 : Blo 614296 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B2108897 : Blo 614296 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B68431333 : Blo 614296 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B1585225 : Blo 614296 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B1388681 : Blo 614296 1388681 := bstep (se 2 (by rfl) ⟨520755, by rfl⟩ : syracuseStep 1388681 = 1041511) B1041511
theorem B1388699 : Blo 614296 1388699 := bstep (se 1 (by rfl) ⟨1041524, by rfl⟩ : syracuseStep 1388699 = 2083049) B2083049
theorem B1781927 : Blo 614296 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B3519065 : Blo 614296 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B2340029 : Blo 614296 2340029 := bstep (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) B877511
theorem B23737697 : Blo 614296 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B2341183 : Blo 614296 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B34159229 : Blo 614296 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B7027559 : Blo 614296 7027559 := bstep (se 1 (by rfl) ⟨5270669, by rfl⟩ : syracuseStep 7027559 = 10541339) B10541339
theorem B1555483 : Blo 614296 1555483 := bstep (se 1 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 1555483 = 2333225) B2333225
theorem B11844791 : Blo 614296 11844791 := bstep (se 1 (by rfl) ⟨8883593, by rfl⟩ : syracuseStep 11844791 = 17767187) B17767187
theorem B5258915 : Blo 614296 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B4669487 : Blo 614296 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B2080889 : Blo 614296 2080889 := bstep (se 2 (by rfl) ⟨780333, by rfl⟩ : syracuseStep 2080889 = 1560667) B1560667
theorem B2080943 : Blo 614296 2080943 := bstep (se 1 (by rfl) ⟨1560707, by rfl⟩ : syracuseStep 2080943 = 3121415) B3121415
theorem B1556891 : Blo 614296 1556891 := bstep (se 1 (by rfl) ⟨1167668, by rfl⟩ : syracuseStep 1556891 = 2335337) B2335337
theorem B2081213 : Blo 614296 2081213 := bstep (se 3 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 2081213 = 780455) B780455
theorem B15024629 : Blo 614296 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B1557407 : Blo 614296 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B2343887 : Blo 614296 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B3196025 : Blo 614296 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B2082671 : Blo 614296 2082671 := bstep (se 1 (by rfl) ⟨1562003, by rfl⟩ : syracuseStep 2082671 = 3124007) B3124007
theorem B2345057 : Blo 614296 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B6998399 : Blo 614296 6998399 := bstep (se 1 (by rfl) ⟨5248799, by rfl⟩ : syracuseStep 6998399 = 10497599) B10497599
theorem B3328775 : Blo 614296 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B8866577 : Blo 614296 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B936827 : Blo 614296 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B3328991 : Blo 614296 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B1756151 : Blo 614296 1756151 := bstep (se 1 (by rfl) ⟨1317113, by rfl⟩ : syracuseStep 1756151 = 2634227) B2634227
theorem B2083913 : Blo 614296 2083913 := bstep (se 2 (by rfl) ⟨781467, by rfl⟩ : syracuseStep 2083913 = 1562935) B1562935
theorem B3951773 : Blo 614296 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B8408231 : Blo 614296 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B1756367 : Blo 614296 1756367 := bstep (se 1 (by rfl) ⟨1317275, by rfl⟩ : syracuseStep 1756367 = 2634551) B2634551
theorem B1560647 : Blo 614296 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B6082775 : Blo 614296 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B1560809 : Blo 614296 1560809 := bstep (se 2 (by rfl) ⟨585303, by rfl⟩ : syracuseStep 1560809 = 1170607) B1170607
theorem B1757801 : Blo 614296 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B2217095 : Blo 614296 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B1037495 : Blo 614296 1037495 := bstep (se 1 (by rfl) ⟨778121, by rfl⟩ : syracuseStep 1037495 = 1556243) B1556243
theorem B2086397 : Blo 614296 2086397 := bstep (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) B782399
theorem B2086505 : Blo 614296 2086505 := bstep (se 2 (by rfl) ⟨782439, by rfl⟩ : syracuseStep 2086505 = 1564879) B1564879
theorem B1759259 : Blo 614296 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1760467 : Blo 614296 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B6774329 : Blo 614296 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B9854585 : Blo 614296 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B1564343 : Blo 614296 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B8019695 : Blo 614296 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B1171739 : Blo 614296 1171739 := bstep (se 1 (by rfl) ⟨878804, by rfl⟩ : syracuseStep 1171739 = 1757609) B1757609
theorem B614759 : Blo 614296 614759 := bstep (se 1 (by rfl) ⟨461069, by rfl⟩ : syracuseStep 614759 = 922139) B922139
theorem B13525451 : Blo 614296 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B614879 : Blo 614296 614879 := bstep (se 1 (by rfl) ⟨461159, by rfl⟩ : syracuseStep 614879 = 922319) B922319
theorem B7922407 : Blo 614296 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B615231 : Blo 614296 615231 := bstep (se 1 (by rfl) ⟨461423, by rfl⟩ : syracuseStep 615231 = 922847) B922847
theorem B615391 : Blo 614296 615391 := bstep (se 1 (by rfl) ⟨461543, by rfl⟩ : syracuseStep 615391 = 923087) B923087
theorem B615551 : Blo 614296 615551 := bstep (se 1 (by rfl) ⟨461663, by rfl⟩ : syracuseStep 615551 = 923327) B923327
theorem B3499361 : Blo 614296 3499361 := bstep (se 2 (by rfl) ⟨1312260, by rfl⟩ : syracuseStep 3499361 = 2624521) B2624521
theorem B615807 : Blo 614296 615807 := bstep (se 1 (by rfl) ⟨461855, by rfl⟩ : syracuseStep 615807 = 923711) B923711
theorem B615919 : Blo 614296 615919 := bstep (se 1 (by rfl) ⟨461939, by rfl⟩ : syracuseStep 615919 = 923879) B923879
theorem B616039 : Blo 614296 616039 := bstep (se 1 (by rfl) ⟨462029, by rfl⟩ : syracuseStep 616039 = 924059) B924059
theorem B616319 : Blo 614296 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B1042409 : Blo 614296 1042409 := bstep (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) B781807
theorem B3566063 : Blo 614296 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B4745735 : Blo 614296 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B10545713 : Blo 614296 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B618031 : Blo 614296 618031 := bstep (se 1 (by rfl) ⟨463523, by rfl⟩ : syracuseStep 618031 = 927047) B927047
theorem B36138899 : Blo 614296 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B3502025 : Blo 614296 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B750055 : Blo 614296 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B11269057 : Blo 614296 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B3503209 : Blo 614296 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B1669513 : Blo 614296 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B3112991 : Blo 614296 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B15008287 : Blo 614296 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B2130683 : Blo 614296 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B2818871 : Blo 614296 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B4687469 : Blo 614296 4687469 := bstep (se 3 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 4687469 = 1757801) B1757801
theorem B2492155 : Blo 614296 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B1967993 : Blo 614296 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B624551 : Blo 614296 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B5605487 : Blo 614296 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B8456399 : Blo 614296 8456399 := bstep (se 1 (by rfl) ⟨6342299, by rfl⟩ : syracuseStep 8456399 = 12684599) B12684599
theorem B1478063 : Blo 614296 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B691663 : Blo 614296 691663 := bstep (se 1 (by rfl) ⟨518747, by rfl⟩ : syracuseStep 691663 = 1037495) B1037495
theorem B921839 : Blo 614296 921839 := bstep (se 1 (by rfl) ⟨691379, by rfl⟩ : syracuseStep 921839 = 1382759) B1382759
theorem B921851 : Blo 614296 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B922439 : Blo 614296 922439 := bstep (se 1 (by rfl) ⟨691829, by rfl⟩ : syracuseStep 922439 = 1383659) B1383659
theorem B2364383 : Blo 614296 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B922727 : Blo 614296 922727 := bstep (se 1 (by rfl) ⟨692045, by rfl⟩ : syracuseStep 922727 = 1384091) B1384091
theorem B922751 : Blo 614296 922751 := bstep (se 1 (by rfl) ⟨692063, by rfl⟩ : syracuseStep 922751 = 1384127) B1384127
theorem B2954603 : Blo 614296 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B4691357 : Blo 614296 4691357 := bstep (se 3 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 4691357 = 1759259) B1759259
theorem B923177 : Blo 614296 923177 := bstep (se 2 (by rfl) ⟨346191, by rfl⟩ : syracuseStep 923177 = 692383) B692383
theorem B9016967 : Blo 614296 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B923561 : Blo 614296 923561 := bstep (se 2 (by rfl) ⟨346335, by rfl⟩ : syracuseStep 923561 = 692671) B692671
theorem B2332907 : Blo 614296 2332907 := bstep (se 1 (by rfl) ⟨1749680, by rfl⟩ : syracuseStep 2332907 = 3499361) B3499361
theorem B9246959 : Blo 614296 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B9509501 : Blo 614296 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B694939 : Blo 614296 694939 := bstep (se 1 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 694939 = 1042409) B1042409
theorem B925055 : Blo 614296 925055 := bstep (se 1 (by rfl) ⟨693791, by rfl⟩ : syracuseStep 925055 = 1387583) B1387583
theorem B1318369 : Blo 614296 1318369 := bstep (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) B988777
theorem B925289 : Blo 614296 925289 := bstep (se 2 (by rfl) ⟨346983, by rfl⟩ : syracuseStep 925289 = 693967) B693967
theorem B2334683 : Blo 614296 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B925787 : Blo 614296 925787 := bstep (se 1 (by rfl) ⟨694340, by rfl⟩ : syracuseStep 925787 = 1388681) B1388681
theorem B925799 : Blo 614296 925799 := bstep (se 1 (by rfl) ⟨694349, by rfl⟩ : syracuseStep 925799 = 1388699) B1388699
theorem B1187951 : Blo 614296 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B3121577 : Blo 614296 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B926633 : Blo 614296 926633 := bstep (se 2 (by rfl) ⟨347487, by rfl⟩ : syracuseStep 926633 = 694975) B694975
theorem B2630825 : Blo 614296 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B2073977 : Blo 614296 2073977 := bstep (se 2 (by rfl) ⟨777741, by rfl⟩ : syracuseStep 2073977 = 1555483) B1555483
theorem B1387259 : Blo 614296 1387259 := bstep (se 1 (by rfl) ⟨1040444, by rfl⟩ : syracuseStep 1387259 = 2080889) B2080889
theorem B1387295 : Blo 614296 1387295 := bstep (se 1 (by rfl) ⟨1040471, by rfl⟩ : syracuseStep 1387295 = 2080943) B2080943
theorem B1387475 : Blo 614296 1387475 := bstep (se 1 (by rfl) ⟨1040606, by rfl⟩ : syracuseStep 1387475 = 2081213) B2081213
theorem B10563209 : Blo 614296 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B1388447 : Blo 614296 1388447 := bstep (se 1 (by rfl) ⟨1041335, by rfl⟩ : syracuseStep 1388447 = 2082671) B2082671
theorem B11972735 : Blo 614296 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B2076839 : Blo 614296 2076839 := bstep (se 1 (by rfl) ⟨1557629, by rfl⟩ : syracuseStep 2076839 = 3115259) B3115259
theorem B4665599 : Blo 614296 4665599 := bstep (se 1 (by rfl) ⟨3499199, by rfl⟩ : syracuseStep 4665599 = 6998399) B6998399
theorem B5911051 : Blo 614296 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B1389275 : Blo 614296 1389275 := bstep (se 1 (by rfl) ⟨1041956, by rfl⟩ : syracuseStep 1389275 = 2083913) B2083913
theorem B2634515 : Blo 614296 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B1586017 : Blo 614296 1586017 := bstep (se 2 (by rfl) ⟨594756, by rfl⟩ : syracuseStep 1586017 = 1189513) B1189513
theorem B3323045 : Blo 614296 3323045 := bstep (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) B623071
theorem B1750511 : Blo 614296 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B1390931 : Blo 614296 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B1391003 : Blo 614296 1391003 := bstep (se 1 (by rfl) ⟨1043252, by rfl⟩ : syracuseStep 1391003 = 2086505) B2086505
theorem B1751719 : Blo 614296 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B91241777 : Blo 614296 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B1752607 : Blo 614296 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B6569723 : Blo 614296 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B2113633 : Blo 614296 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B1000073 : Blo 614296 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B6669053 : Blo 614296 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B2082023 : Blo 614296 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B15025409 : Blo 614296 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B4670945 : Blo 614296 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B3163823 : Blo 614296 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B7030475 : Blo 614296 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B2082779 : Blo 614296 2082779 := bstep (se 1 (by rfl) ⟨1562084, by rfl⟩ : syracuseStep 2082779 = 3124169) B3124169
theorem B2082887 : Blo 614296 2082887 := bstep (se 1 (by rfl) ⟨1562165, by rfl⟩ : syracuseStep 2082887 = 3124331) B3124331
theorem B17090707 : Blo 614296 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B2346043 : Blo 614296 2346043 := bstep (se 1 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 2346043 = 3519065) B3519065
theorem B1560019 : Blo 614296 1560019 := bstep (se 1 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 1560019 = 2340029) B2340029
theorem B2347289 : Blo 614296 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B21385853 : Blo 614296 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B1037927 : Blo 614296 1037927 := bstep (se 1 (by rfl) ⟨778445, by rfl⟩ : syracuseStep 1037927 = 1556891) B1556891
theorem B10016419 : Blo 614296 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B1038271 : Blo 614296 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B1562591 : Blo 614296 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B2808361 : Blo 614296 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B13327031 : Blo 614296 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B1563371 : Blo 614296 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B3955463 : Blo 614296 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2219183 : Blo 614296 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B2219327 : Blo 614296 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B1170767 : Blo 614296 1170767 := bstep (se 1 (by rfl) ⟨878075, by rfl⟩ : syracuseStep 1170767 = 1756151) B1756151
theorem B1170911 : Blo 614296 1170911 := bstep (se 1 (by rfl) ⟨878183, by rfl⟩ : syracuseStep 1170911 = 1756367) B1756367
theorem B2317871 : Blo 614296 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B1040431 : Blo 614296 1040431 := bstep (se 1 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 1040431 = 1560647) B1560647
theorem B4055183 : Blo 614296 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B1040539 : Blo 614296 1040539 := bstep (se 1 (by rfl) ⟨780404, by rfl⟩ : syracuseStep 1040539 = 1560809) B1560809
theorem B3956951 : Blo 614296 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B614727 : Blo 614296 614727 := bstep (se 1 (by rfl) ⟨461045, by rfl⟩ : syracuseStep 614727 = 922091) B922091
theorem B614887 : Blo 614296 614887 := bstep (se 1 (by rfl) ⟨461165, by rfl⟩ : syracuseStep 614887 = 922331) B922331
theorem B615003 : Blo 614296 615003 := bstep (se 1 (by rfl) ⟨461252, by rfl⟩ : syracuseStep 615003 = 922505) B922505
theorem B615259 : Blo 614296 615259 := bstep (se 1 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 615259 = 922889) B922889
theorem B844841 : Blo 614296 844841 := bstep (se 2 (by rfl) ⟨316815, by rfl⟩ : syracuseStep 844841 = 633631) B633631
theorem B1926281 : Blo 614296 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B615579 : Blo 614296 615579 := bstep (se 1 (by rfl) ⟨461684, by rfl⟩ : syracuseStep 615579 = 923369) B923369
theorem B877819 : Blo 614296 877819 := bstep (se 1 (by rfl) ⟨658364, by rfl⟩ : syracuseStep 877819 = 1316729) B1316729
theorem B615751 : Blo 614296 615751 := bstep (se 1 (by rfl) ⟨461813, by rfl⟩ : syracuseStep 615751 = 923627) B923627
theorem B616027 : Blo 614296 616027 := bstep (se 1 (by rfl) ⟨462020, by rfl⟩ : syracuseStep 616027 = 924041) B924041
theorem B616095 : Blo 614296 616095 := bstep (se 1 (by rfl) ⟨462071, by rfl⟩ : syracuseStep 616095 = 924143) B924143
theorem B4516219 : Blo 614296 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B616911 : Blo 614296 616911 := bstep (se 1 (by rfl) ⟨462683, by rfl⟩ : syracuseStep 616911 = 925367) B925367
theorem B1042895 : Blo 614296 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B617071 : Blo 614296 617071 := bstep (se 1 (by rfl) ⟨462803, by rfl⟩ : syracuseStep 617071 = 925607) B925607
theorem B617243 : Blo 614296 617243 := bstep (se 1 (by rfl) ⟨462932, by rfl⟩ : syracuseStep 617243 = 925865) B925865
theorem B781159 : Blo 614296 781159 := bstep (se 1 (by rfl) ⟨585869, by rfl⟩ : syracuseStep 781159 = 1171739) B1171739
theorem B617935 : Blo 614296 617935 := bstep (se 1 (by rfl) ⟨463451, by rfl⟩ : syracuseStep 617935 = 926903) B926903
theorem B618095 : Blo 614296 618095 := bstep (se 1 (by rfl) ⟨463571, by rfl⟩ : syracuseStep 618095 = 927143) B927143
theorem B2226017 : Blo 614296 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B15825131 : Blo 614296 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B89979605 : Blo 614296 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B22772819 : Blo 614296 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B4685039 : Blo 614296 4685039 := bstep (se 1 (by rfl) ⟨3513779, by rfl⟩ : syracuseStep 4685039 = 7027559) B7027559
theorem B7896527 : Blo 614296 7896527 := bstep (se 1 (by rfl) ⟨5922395, by rfl⟩ : syracuseStep 7896527 = 11844791) B11844791
theorem B3112505 : Blo 614296 3112505 := bstep (se 2 (by rfl) ⟨1167189, by rfl⟩ : syracuseStep 3112505 = 2334379) B2334379
theorem B96370397 : Blo 614296 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B3505943 : Blo 614296 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B11272709 : Blo 614296 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B3113963 : Blo 614296 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B4686983 : Blo 614296 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B1311995 : Blo 614296 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B3736991 : Blo 614296 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B5637599 : Blo 614296 5637599 := bstep (se 1 (by rfl) ⟨4228199, by rfl⟩ : syracuseStep 5637599 = 8456399) B8456399
theorem B24086501 : Blo 614296 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B985375 : Blo 614296 985375 := bstep (se 1 (by rfl) ⟨739031, by rfl⟩ : syracuseStep 985375 = 1478063) B1478063
theorem B14257235 : Blo 614296 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B1576255 : Blo 614296 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B691951 : Blo 614296 691951 := bstep (se 1 (by rfl) ⟨518963, by rfl⟩ : syracuseStep 691951 = 1037927) B1037927
theorem B6164639 : Blo 614296 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B8884687 : Blo 614296 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B922217 : Blo 614296 922217 := bstep (se 2 (by rfl) ⟨345831, by rfl⟩ : syracuseStep 922217 = 691663) B691663
theorem B1479455 : Blo 614296 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1479551 : Blo 614296 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B1545247 : Blo 614296 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B1284187 : Blo 614296 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1382651 : Blo 614296 1382651 := bstep (se 1 (by rfl) ⟨1036988, by rfl⟩ : syracuseStep 1382651 = 2073977) B2073977
theorem B695263 : Blo 614296 695263 := bstep (se 1 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 695263 = 1042895) B1042895
theorem B924839 : Blo 614296 924839 := bstep (se 1 (by rfl) ⟨693629, by rfl⟩ : syracuseStep 924839 = 1387259) B1387259
theorem B924863 : Blo 614296 924863 := bstep (se 1 (by rfl) ⟨693647, by rfl⟩ : syracuseStep 924863 = 1387295) B1387295
theorem B924983 : Blo 614296 924983 := bstep (se 1 (by rfl) ⟨693737, by rfl⟩ : syracuseStep 924983 = 1387475) B1387475
theorem B1384361 : Blo 614296 1384361 := bstep (se 2 (by rfl) ⟨519135, by rfl⟩ : syracuseStep 1384361 = 1038271) B1038271
theorem B925631 : Blo 614296 925631 := bstep (se 1 (by rfl) ⟨694223, by rfl⟩ : syracuseStep 925631 = 1388447) B1388447
theorem B1384559 : Blo 614296 1384559 := bstep (se 1 (by rfl) ⟨1038419, by rfl⟩ : syracuseStep 1384559 = 2076839) B2076839
theorem B926183 : Blo 614296 926183 := bstep (se 1 (by rfl) ⟨694637, by rfl⟩ : syracuseStep 926183 = 1389275) B1389275
theorem B3744481 : Blo 614296 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B926585 : Blo 614296 926585 := bstep (se 2 (by rfl) ⟨347469, by rfl⟩ : syracuseStep 926585 = 694939) B694939
theorem B2335625 : Blo 614296 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B1484011 : Blo 614296 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B927287 : Blo 614296 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B927335 : Blo 614296 927335 := bstep (se 1 (by rfl) ⟨695501, by rfl⟩ : syracuseStep 927335 = 1391003) B1391003
theorem B2336809 : Blo 614296 2336809 := bstep (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) B1752607
theorem B15181879 : Blo 614296 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B3123359 : Blo 614296 3123359 := bstep (se 1 (by rfl) ⟨2342519, by rfl⟩ : syracuseStep 3123359 = 4685039) B4685039
theorem B60827851 : Blo 614296 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B2075003 : Blo 614296 2075003 := bstep (se 1 (by rfl) ⟨1556252, by rfl⟩ : syracuseStep 2075003 = 3112505) B3112505
theorem B2337295 : Blo 614296 2337295 := bstep (se 1 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 2337295 = 3505943) B3505943
theorem B2075327 : Blo 614296 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B1387241 : Blo 614296 1387241 := bstep (se 2 (by rfl) ⟨520215, by rfl⟩ : syracuseStep 1387241 = 1040431) B1040431
theorem B1387385 : Blo 614296 1387385 := bstep (se 2 (by rfl) ⟨520269, by rfl⟩ : syracuseStep 1387385 = 1040539) B1040539
theorem B666715 : Blo 614296 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B1879247 : Blo 614296 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B1388015 : Blo 614296 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B3124979 : Blo 614296 3124979 := bstep (se 1 (by rfl) ⟨2343734, by rfl⟩ : syracuseStep 3124979 = 4687469) B4687469
theorem B2109215 : Blo 614296 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B1388519 : Blo 614296 1388519 := bstep (se 1 (by rfl) ⟨1041389, by rfl⟩ : syracuseStep 1388519 = 2082779) B2082779
theorem B1388591 : Blo 614296 1388591 := bstep (se 1 (by rfl) ⟨1041443, by rfl⟩ : syracuseStep 1388591 = 2082887) B2082887
theorem B5681821 : Blo 614296 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B3322873 : Blo 614296 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B22787609 : Blo 614296 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B3127571 : Blo 614296 3127571 := bstep (se 1 (by rfl) ⟨2345678, by rfl⟩ : syracuseStep 3127571 = 4691357) B4691357
theorem B7878941 : Blo 614296 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B4668029 : Blo 614296 4668029 := bstep (se 3 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 4668029 = 1750511) B1750511
theorem B3128057 : Blo 614296 3128057 := bstep (se 2 (by rfl) ⟨1173021, by rfl⟩ : syracuseStep 3128057 = 2346043) B2346043
theorem B1555271 : Blo 614296 1555271 := bstep (se 1 (by rfl) ⟨1166453, by rfl⟩ : syracuseStep 1555271 = 2332907) B2332907
theorem B6339667 : Blo 614296 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B2636975 : Blo 614296 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B2080025 : Blo 614296 2080025 := bstep (se 2 (by rfl) ⟨780009, by rfl⟩ : syracuseStep 2080025 = 1560019) B1560019
theorem B1556455 : Blo 614296 1556455 := bstep (se 1 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 1556455 = 2334683) B2334683
theorem B2703455 : Blo 614296 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B2637967 : Blo 614296 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B2081051 : Blo 614296 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B7881401 : Blo 614296 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B1753883 : Blo 614296 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B2114689 : Blo 614296 2114689 := bstep (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) B1586017
theorem B13355225 : Blo 614296 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B7981823 : Blo 614296 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B1756343 : Blo 614296 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B2215363 : Blo 614296 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B59986403 : Blo 614296 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B1757825 : Blo 614296 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B5264351 : Blo 614296 5264351 := bstep (se 1 (by rfl) ⟨3948263, by rfl⟩ : syracuseStep 5264351 = 7896527) B7896527
theorem B64246931 : Blo 614296 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B4379815 : Blo 614296 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B4446035 : Blo 614296 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B20011049 : Blo 614296 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B10016939 : Blo 614296 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B12671477 : Blo 614296 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B1170425 : Blo 614296 1170425 := bstep (se 2 (by rfl) ⟨438909, by rfl⟩ : syracuseStep 1170425 = 877819) B877819
theorem B2252909 : Blo 614296 2252909 := bstep (se 3 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 2252909 = 844841) B844841
theorem B614559 : Blo 614296 614559 := bstep (se 1 (by rfl) ⟨460919, by rfl⟩ : syracuseStep 614559 = 921839) B921839
theorem B614567 : Blo 614296 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B1564859 : Blo 614296 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B614959 : Blo 614296 614959 := bstep (se 1 (by rfl) ⟨461219, by rfl⟩ : syracuseStep 614959 = 922439) B922439
theorem B615151 : Blo 614296 615151 := bstep (se 1 (by rfl) ⟨461363, by rfl⟩ : syracuseStep 615151 = 922727) B922727
theorem B615167 : Blo 614296 615167 := bstep (se 1 (by rfl) ⟨461375, by rfl⟩ : syracuseStep 615167 = 922751) B922751
theorem B615451 : Blo 614296 615451 := bstep (se 1 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 615451 = 923177) B923177
theorem B1041545 : Blo 614296 1041545 := bstep (se 2 (by rfl) ⟨390579, by rfl⟩ : syracuseStep 1041545 = 781159) B781159
theorem B615707 : Blo 614296 615707 := bstep (se 1 (by rfl) ⟨461780, by rfl⟩ : syracuseStep 615707 = 923561) B923561
theorem B1041727 : Blo 614296 1041727 := bstep (se 1 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 1041727 = 1562591) B1562591
theorem B24045245 : Blo 614296 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B1042247 : Blo 614296 1042247 := bstep (se 1 (by rfl) ⟨781685, by rfl⟩ : syracuseStep 1042247 = 1563371) B1563371
theorem B780511 : Blo 614296 780511 := bstep (se 1 (by rfl) ⟨585383, by rfl⟩ : syracuseStep 780511 = 1170767) B1170767
theorem B616703 : Blo 614296 616703 := bstep (se 1 (by rfl) ⟨462527, by rfl⟩ : syracuseStep 616703 = 925055) B925055
theorem B780607 : Blo 614296 780607 := bstep (se 1 (by rfl) ⟨585455, by rfl⟩ : syracuseStep 780607 = 1170911) B1170911
theorem B616859 : Blo 614296 616859 := bstep (se 1 (by rfl) ⟨462644, by rfl⟩ : syracuseStep 616859 = 925289) B925289
theorem B1665469 : Blo 614296 1665469 := bstep (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) B624551
theorem B617191 : Blo 614296 617191 := bstep (se 1 (by rfl) ⟨462893, by rfl⟩ : syracuseStep 617191 = 925787) B925787
theorem B617199 : Blo 614296 617199 := bstep (se 1 (by rfl) ⟨462899, by rfl⟩ : syracuseStep 617199 = 925799) B925799
theorem B617755 : Blo 614296 617755 := bstep (se 1 (by rfl) ⟨463316, by rfl⟩ : syracuseStep 617755 = 926633) B926633
theorem B7042139 : Blo 614296 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B3110399 : Blo 614296 3110399 := bstep (se 1 (by rfl) ⟨2332799, by rfl⟩ : syracuseStep 3110399 = 4665599) B4665599
theorem B10550087 : Blo 614296 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B1802303 : Blo 614296 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B2491327 : Blo 614296 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B16057667 : Blo 614296 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B2819585 : Blo 614296 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B9504823 : Blo 614296 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B3115745 : Blo 614296 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B81103801 : Blo 614296 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B1313833 : Blo 614296 1313833 := bstep (se 2 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 1313833 = 985375) B985375
theorem B986303 : Blo 614296 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B3509567 : Blo 614296 3509567 := bstep (se 1 (by rfl) ⟨2632175, by rfl⟩ : syracuseStep 3509567 = 5264351) B5264351
theorem B3116393 : Blo 614296 3116393 := bstep (se 2 (by rfl) ⟨1168647, by rfl⟩ : syracuseStep 3116393 = 2337295) B2337295
theorem B42831287 : Blo 614296 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B13340699 : Blo 614296 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B888953 : Blo 614296 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B921767 : Blo 614296 921767 := bstep (se 1 (by rfl) ⟨691325, by rfl⟩ : syracuseStep 921767 = 1382651) B1382651
theorem B2101673 : Blo 614296 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B2953817 : Blo 614296 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B922601 : Blo 614296 922601 := bstep (se 2 (by rfl) ⟨345975, by rfl⟩ : syracuseStep 922601 = 691951) B691951
theorem B922907 : Blo 614296 922907 := bstep (se 1 (by rfl) ⟨692180, by rfl⟩ : syracuseStep 922907 = 1384361) B1384361
theorem B923039 : Blo 614296 923039 := bstep (se 1 (by rfl) ⟨692279, by rfl⟩ : syracuseStep 923039 = 1384559) B1384559
theorem B694363 : Blo 614296 694363 := bstep (se 1 (by rfl) ⟨520772, by rfl⟩ : syracuseStep 694363 = 1041545) B1041545
theorem B7575761 : Blo 614296 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B16030163 : Blo 614296 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B694831 : Blo 614296 694831 := bstep (se 1 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 694831 = 1042247) B1042247
theorem B4430497 : Blo 614296 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B1383335 : Blo 614296 1383335 := bstep (se 1 (by rfl) ⟨1037501, by rfl⟩ : syracuseStep 1383335 = 2075003) B2075003
theorem B1383551 : Blo 614296 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B924827 : Blo 614296 924827 := bstep (se 1 (by rfl) ⟨693620, by rfl⟩ : syracuseStep 924827 = 1387241) B1387241
theorem B924923 : Blo 614296 924923 := bstep (se 1 (by rfl) ⟨693692, by rfl⟩ : syracuseStep 924923 = 1387385) B1387385
theorem B1252831 : Blo 614296 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B925343 : Blo 614296 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B925679 : Blo 614296 925679 := bstep (se 1 (by rfl) ⟨694259, by rfl⟩ : syracuseStep 925679 = 1388519) B1388519
theorem B925727 : Blo 614296 925727 := bstep (se 1 (by rfl) ⟨694295, by rfl⟩ : syracuseStep 925727 = 1388591) B1388591
theorem B1712249 : Blo 614296 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B4694759 : Blo 614296 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B2073599 : Blo 614296 2073599 := bstep (se 1 (by rfl) ⟨1555199, by rfl⟩ : syracuseStep 2073599 = 3110399) B3110399
theorem B927017 : Blo 614296 927017 := bstep (se 2 (by rfl) ⟨347631, by rfl⟩ : syracuseStep 927017 = 695263) B695263
theorem B5252627 : Blo 614296 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B1386683 : Blo 614296 1386683 := bstep (se 1 (by rfl) ⟨1040012, by rfl⟩ : syracuseStep 1386683 = 2080025) B2080025
theorem B2075273 : Blo 614296 2075273 := bstep (se 2 (by rfl) ⟨778227, by rfl⟩ : syracuseStep 2075273 = 1556455) B1556455
theorem B1387367 : Blo 614296 1387367 := bstep (se 1 (by rfl) ⟨1040525, by rfl⟩ : syracuseStep 1387367 = 2081051) B2081051
theorem B3517289 : Blo 614296 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B5254267 : Blo 614296 5254267 := bstep (se 1 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 5254267 = 7881401) B7881401
theorem B2075975 : Blo 614296 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B3124655 : Blo 614296 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B4992641 : Blo 614296 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B30060557 : Blo 614296 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B1978681 : Blo 614296 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B1388969 : Blo 614296 1388969 := bstep (se 2 (by rfl) ⟨520863, by rfl⟩ : syracuseStep 1388969 = 1041727) B1041727
theorem B5321215 : Blo 614296 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B3945469 : Blo 614296 3945469 := bstep (se 3 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 3945469 = 1479551) B1479551
theorem B4109759 : Blo 614296 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B39990935 : Blo 614296 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B2964023 : Blo 614296 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B60766957 : Blo 614296 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B1557083 : Blo 614296 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B11846249 : Blo 614296 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B2082239 : Blo 614296 2082239 := bstep (se 1 (by rfl) ⟨1561679, by rfl⟩ : syracuseStep 2082239 = 3123359) B3123359
theorem B2083319 : Blo 614296 2083319 := bstep (se 1 (by rfl) ⟨1562489, by rfl⟩ : syracuseStep 2083319 = 3124979) B3124979
theorem B7031933 : Blo 614296 7031933 := bstep (se 3 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 7031933 = 2636975) B2636975
theorem B2085047 : Blo 614296 2085047 := bstep (se 1 (by rfl) ⟨1563785, by rfl⟩ : syracuseStep 2085047 = 3127571) B3127571
theorem B2085371 : Blo 614296 2085371 := bstep (se 1 (by rfl) ⟨1564028, by rfl⟩ : syracuseStep 2085371 = 3128057) B3128057
theorem B1036847 : Blo 614296 1036847 := bstep (se 1 (by rfl) ⟨777635, by rfl⟩ : syracuseStep 1036847 = 1555271) B1555271
theorem B7033391 : Blo 614296 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B1169255 : Blo 614296 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B3758399 : Blo 614296 3758399 := bstep (se 1 (by rfl) ⟨2818799, by rfl⟩ : syracuseStep 3758399 = 5637599) B5637599
theorem B8903483 : Blo 614296 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B20242505 : Blo 614296 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B1040681 : Blo 614296 1040681 := bstep (se 2 (by rfl) ⟨390255, by rfl⟩ : syracuseStep 1040681 = 780511) B780511
theorem B614811 : Blo 614296 614811 := bstep (se 1 (by rfl) ⟨461108, by rfl⟩ : syracuseStep 614811 = 922217) B922217
theorem B1040809 : Blo 614296 1040809 := bstep (se 2 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 1040809 = 780607) B780607
theorem B1171883 : Blo 614296 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B2220625 : Blo 614296 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B3498653 : Blo 614296 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B6677959 : Blo 614296 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B8447651 : Blo 614296 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B780283 : Blo 614296 780283 := bstep (se 1 (by rfl) ⟨585212, by rfl⟩ : syracuseStep 780283 = 1170425) B1170425
theorem B616559 : Blo 614296 616559 := bstep (se 1 (by rfl) ⟨462419, by rfl⟩ : syracuseStep 616559 = 924839) B924839
theorem B616575 : Blo 614296 616575 := bstep (se 1 (by rfl) ⟨462431, by rfl⟩ : syracuseStep 616575 = 924863) B924863
theorem B616655 : Blo 614296 616655 := bstep (se 1 (by rfl) ⟨462491, by rfl⟩ : syracuseStep 616655 = 924983) B924983
theorem B617087 : Blo 614296 617087 := bstep (se 1 (by rfl) ⟨462815, by rfl⟩ : syracuseStep 617087 = 925631) B925631
theorem B1501939 : Blo 614296 1501939 := bstep (se 1 (by rfl) ⟨1126454, by rfl⟩ : syracuseStep 1501939 = 2252909) B2252909
theorem B1043239 : Blo 614296 1043239 := bstep (se 1 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 1043239 = 1564859) B1564859
theorem B617455 : Blo 614296 617455 := bstep (se 1 (by rfl) ⟨463091, by rfl⟩ : syracuseStep 617455 = 926183) B926183
theorem B617723 : Blo 614296 617723 := bstep (se 1 (by rfl) ⟨463292, by rfl⟩ : syracuseStep 617723 = 926585) B926585
theorem B23359013 : Blo 614296 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B618191 : Blo 614296 618191 := bstep (se 1 (by rfl) ⟨463643, by rfl⟩ : syracuseStep 618191 = 927287) B927287
theorem B618223 : Blo 614296 618223 := bstep (se 1 (by rfl) ⟨463667, by rfl⟩ : syracuseStep 618223 = 927335) B927335
theorem B2060329 : Blo 614296 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B1406143 : Blo 614296 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B4683581 : Blo 614296 4683581 := bstep (se 3 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 4683581 = 1756343) B1756343
theorem B8452889 : Blo 614296 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B3112019 : Blo 614296 3112019 := bstep (se 1 (by rfl) ⟨2334014, by rfl⟩ : syracuseStep 3112019 = 4668029) B4668029
theorem B7897499 : Blo 614296 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B5604461 : Blo 614296 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B4687955 : Blo 614296 4687955 := bstep (se 1 (by rfl) ⟨3515966, by rfl⟩ : syracuseStep 4687955 = 7031933) B7031933
theorem B691231 : Blo 614296 691231 := bstep (se 1 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 691231 = 1036847) B1036847
theorem B4688927 : Blo 614296 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B1969211 : Blo 614296 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B108138401 : Blo 614296 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B5050507 : Blo 614296 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B5935655 : Blo 614296 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B922223 : Blo 614296 922223 := bstep (se 1 (by rfl) ⟨691667, by rfl⟩ : syracuseStep 922223 = 1383335) B1383335
theorem B922367 : Blo 614296 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B3118013 : Blo 614296 3118013 := bstep (se 3 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 3118013 = 1169255) B1169255
theorem B693787 : Blo 614296 693787 := bstep (se 1 (by rfl) ⟨520340, by rfl⟩ : syracuseStep 693787 = 1040681) B1040681
theorem B2332435 : Blo 614296 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B1382399 : Blo 614296 1382399 := bstep (se 1 (by rfl) ⟨1036799, by rfl⟩ : syracuseStep 1382399 = 2073599) B2073599
theorem B924455 : Blo 614296 924455 := bstep (se 1 (by rfl) ⟨693341, by rfl⟩ : syracuseStep 924455 = 1386683) B1386683
theorem B1383515 : Blo 614296 1383515 := bstep (se 1 (by rfl) ⟨1037636, by rfl⟩ : syracuseStep 1383515 = 2075273) B2075273
theorem B924911 : Blo 614296 924911 := bstep (se 1 (by rfl) ⟨693683, by rfl⟩ : syracuseStep 924911 = 1387367) B1387367
theorem B1383983 : Blo 614296 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B15572675 : Blo 614296 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B925817 : Blo 614296 925817 := bstep (se 2 (by rfl) ⟨347181, by rfl⟩ : syracuseStep 925817 = 694363) B694363
theorem B925979 : Blo 614296 925979 := bstep (se 1 (by rfl) ⟨694484, by rfl⟩ : syracuseStep 925979 = 1388969) B1388969
theorem B2630141 : Blo 614296 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B926441 : Blo 614296 926441 := bstep (se 2 (by rfl) ⟨347415, by rfl⟩ : syracuseStep 926441 = 694831) B694831
theorem B5907329 : Blo 614296 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B3122387 : Blo 614296 3122387 := bstep (se 1 (by rfl) ⟨2341790, by rfl⟩ : syracuseStep 3122387 = 4683581) B4683581
theorem B1976015 : Blo 614296 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B2074679 : Blo 614296 2074679 := bstep (se 1 (by rfl) ⟨1556009, by rfl⟩ : syracuseStep 2074679 = 3112019) B3112019
theorem B53980013 : Blo 614296 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B2370541 : Blo 614296 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B1387745 : Blo 614296 1387745 := bstep (se 2 (by rfl) ⟨520404, by rfl⟩ : syracuseStep 1387745 = 1040809) B1040809
theorem B2960833 : Blo 614296 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B1388159 : Blo 614296 1388159 := bstep (se 1 (by rfl) ⟨1041119, by rfl⟩ : syracuseStep 1388159 = 2082239) B2082239
theorem B1879723 : Blo 614296 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B3321769 : Blo 614296 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B1388879 : Blo 614296 1388879 := bstep (se 1 (by rfl) ⟨1041659, by rfl⟩ : syracuseStep 1388879 = 2083319) B2083319
theorem B2077163 : Blo 614296 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B2339711 : Blo 614296 2339711 := bstep (se 1 (by rfl) ⟨1754783, by rfl⟩ : syracuseStep 2339711 = 3509567) B3509567
theorem B2077595 : Blo 614296 2077595 := bstep (se 1 (by rfl) ⟨1558196, by rfl⟩ : syracuseStep 2077595 = 3116393) B3116393
theorem B28554191 : Blo 614296 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B8893799 : Blo 614296 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B1390031 : Blo 614296 1390031 := bstep (se 1 (by rfl) ⟨1042523, by rfl⟩ : syracuseStep 1390031 = 2085047) B2085047
theorem B1390247 : Blo 614296 1390247 := bstep (se 1 (by rfl) ⟨1042685, by rfl⟩ : syracuseStep 1390247 = 2085371) B2085371
theorem B1390985 : Blo 614296 1390985 := bstep (se 2 (by rfl) ⟨521619, by rfl⟩ : syracuseStep 1390985 = 1043239) B1043239
theorem B8010341 : Blo 614296 8010341 := bstep (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) B1501939
theorem B1751777 : Blo 614296 1751777 := bstep (se 2 (by rfl) ⟨656916, by rfl⟩ : syracuseStep 1751777 = 1313833) B1313833
theorem B2505599 : Blo 614296 2505599 := bstep (se 1 (by rfl) ⟨1879199, by rfl⟩ : syracuseStep 2505599 = 3758399) B3758399
theorem B2638241 : Blo 614296 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B3129839 : Blo 614296 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B7094953 : Blo 614296 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B42747101 : Blo 614296 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B5260625 : Blo 614296 5260625 := bstep (se 2 (by rfl) ⟨1972734, by rfl⟩ : syracuseStep 5260625 = 3945469) B3945469
theorem B2344859 : Blo 614296 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B2083103 : Blo 614296 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B3328427 : Blo 614296 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B20040371 : Blo 614296 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B2739839 : Blo 614296 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B81022609 : Blo 614296 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B26660623 : Blo 614296 26660623 := bstep (se 1 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 26660623 = 39990935) B39990935
theorem B1201535 : Blo 614296 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1038055 : Blo 614296 1038055 := bstep (se 1 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 1038055 = 1557083) B1557083
theorem B10705111 : Blo 614296 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B8903945 : Blo 614296 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B1040377 : Blo 614296 1040377 := bstep (se 2 (by rfl) ⟨390141, by rfl⟩ : syracuseStep 1040377 = 780283) B780283
theorem B12673097 : Blo 614296 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B614511 : Blo 614296 614511 := bstep (se 1 (by rfl) ⟨460883, by rfl⟩ : syracuseStep 614511 = 921767) B921767
theorem B615067 : Blo 614296 615067 := bstep (se 1 (by rfl) ⟨461300, by rfl⟩ : syracuseStep 615067 = 922601) B922601
theorem B615271 : Blo 614296 615271 := bstep (se 1 (by rfl) ⟨461453, by rfl⟩ : syracuseStep 615271 = 922907) B922907
theorem B615359 : Blo 614296 615359 := bstep (se 1 (by rfl) ⟨461519, by rfl⟩ : syracuseStep 615359 = 923039) B923039
theorem B7005689 : Blo 614296 7005689 := bstep (se 2 (by rfl) ⟨2627133, by rfl⟩ : syracuseStep 7005689 = 5254267) B5254267
theorem B616551 : Blo 614296 616551 := bstep (se 1 (by rfl) ⟨462413, by rfl⟩ : syracuseStep 616551 = 924827) B924827
theorem B616615 : Blo 614296 616615 := bstep (se 1 (by rfl) ⟨462461, by rfl⟩ : syracuseStep 616615 = 924923) B924923
theorem B616895 : Blo 614296 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B617119 : Blo 614296 617119 := bstep (se 1 (by rfl) ⟨462839, by rfl⟩ : syracuseStep 617119 = 925679) B925679
theorem B617151 : Blo 614296 617151 := bstep (se 1 (by rfl) ⟨462863, by rfl⟩ : syracuseStep 617151 = 925727) B925727
theorem B2747105 : Blo 614296 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B1141499 : Blo 614296 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B781255 : Blo 614296 781255 := bstep (se 1 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 781255 = 1171883) B1171883
theorem B618011 : Blo 614296 618011 := bstep (se 1 (by rfl) ⟨463508, by rfl⟩ : syracuseStep 618011 = 927017) B927017
theorem B7499429 : Blo 614296 7499429 := bstep (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) B1406143
theorem B3501751 : Blo 614296 3501751 := bstep (se 1 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 3501751 = 5252627) B5252627
theorem B5631767 : Blo 614296 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B5635259 : Blo 614296 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B1670441 : Blo 614296 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B3736307 : Blo 614296 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B3507083 : Blo 614296 3507083 := bstep (se 1 (by rfl) ⟨2630312, by rfl⟩ : syracuseStep 3507083 = 5260625) B5260625
theorem B72092267 : Blo 614296 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B12816373 : Blo 614296 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B921599 : Blo 614296 921599 := bstep (se 1 (by rfl) ⟨691199, by rfl⟩ : syracuseStep 921599 = 1382399) B1382399
theorem B921641 : Blo 614296 921641 := bstep (se 2 (by rfl) ⟨345615, by rfl⟩ : syracuseStep 921641 = 691231) B691231
theorem B922343 : Blo 614296 922343 := bstep (se 1 (by rfl) ⟨691757, by rfl⟩ : syracuseStep 922343 = 1383515) B1383515
theorem B5935963 : Blo 614296 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B922655 : Blo 614296 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B4429025 : Blo 614296 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B3938219 : Blo 614296 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B1383119 : Blo 614296 1383119 := bstep (se 1 (by rfl) ⟨1037339, by rfl⟩ : syracuseStep 1383119 = 2074679) B2074679
theorem B35986675 : Blo 614296 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B925049 : Blo 614296 925049 := bstep (se 2 (by rfl) ⟨346893, by rfl⟩ : syracuseStep 925049 = 693787) B693787
theorem B925163 : Blo 614296 925163 := bstep (se 1 (by rfl) ⟨693872, by rfl⟩ : syracuseStep 925163 = 1387745) B1387745
theorem B1384073 : Blo 614296 1384073 := bstep (se 2 (by rfl) ⟨519027, by rfl⟩ : syracuseStep 1384073 = 1038055) B1038055
theorem B925439 : Blo 614296 925439 := bstep (se 1 (by rfl) ⟨694079, by rfl⟩ : syracuseStep 925439 = 1388159) B1388159
theorem B5251229 : Blo 614296 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B925919 : Blo 614296 925919 := bstep (se 1 (by rfl) ⟨694439, by rfl⟩ : syracuseStep 925919 = 1388879) B1388879
theorem B1384775 : Blo 614296 1384775 := bstep (se 1 (by rfl) ⟨1038581, by rfl⟩ : syracuseStep 1384775 = 2077163) B2077163
theorem B1385063 : Blo 614296 1385063 := bstep (se 1 (by rfl) ⟨1038797, by rfl⟩ : syracuseStep 1385063 = 2077595) B2077595
theorem B926687 : Blo 614296 926687 := bstep (se 1 (by rfl) ⟨695015, by rfl⟩ : syracuseStep 926687 = 1390031) B1390031
theorem B926831 : Blo 614296 926831 := bstep (se 1 (by rfl) ⟨695123, by rfl⟩ : syracuseStep 926831 = 1390247) B1390247
theorem B927323 : Blo 614296 927323 := bstep (se 1 (by rfl) ⟨695492, by rfl⟩ : syracuseStep 927323 = 1390985) B1390985
theorem B41527133 : Blo 614296 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B1387169 : Blo 614296 1387169 := bstep (se 2 (by rfl) ⟨520188, by rfl⟩ : syracuseStep 1387169 = 1040377) B1040377
theorem B57093925 : Blo 614296 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B3125303 : Blo 614296 3125303 := bstep (se 1 (by rfl) ⟨2343977, by rfl⟩ : syracuseStep 3125303 = 4687955) B4687955
theorem B1388735 : Blo 614296 1388735 := bstep (se 1 (by rfl) ⟨1041551, by rfl⟩ : syracuseStep 1388735 = 2083103) B2083103
theorem B3125951 : Blo 614296 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B2078675 : Blo 614296 2078675 := bstep (se 1 (by rfl) ⟨1559006, by rfl⟩ : syracuseStep 2078675 = 3118013) B3118013
theorem B3160721 : Blo 614296 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B3947777 : Blo 614296 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B2506297 : Blo 614296 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B4669001 : Blo 614296 4669001 := bstep (se 2 (by rfl) ⟨1750875, by rfl⟩ : syracuseStep 4669001 = 3501751) B3501751
theorem B6734009 : Blo 614296 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B1753427 : Blo 614296 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B2081591 : Blo 614296 2081591 := bstep (se 1 (by rfl) ⟨1561193, by rfl⟩ : syracuseStep 2081591 = 3122387) B3122387
theorem B4670459 : Blo 614296 4670459 := bstep (se 1 (by rfl) ⟨3502844, by rfl⟩ : syracuseStep 4670459 = 7005689) B7005689
theorem B4999619 : Blo 614296 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B3754511 : Blo 614296 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B1559807 : Blo 614296 1559807 := bstep (se 1 (by rfl) ⟨1169855, by rfl⟩ : syracuseStep 1559807 = 2339711) B2339711
theorem B1167851 : Blo 614296 1167851 := bstep (se 1 (by rfl) ⟨875888, by rfl⟩ : syracuseStep 1167851 = 1751777) B1751777
theorem B3756839 : Blo 614296 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B5264999 : Blo 614296 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B1758827 : Blo 614296 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B2086559 : Blo 614296 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B28498067 : Blo 614296 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B9459937 : Blo 614296 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B1563239 : Blo 614296 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B2218951 : Blo 614296 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B13360247 : Blo 614296 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B3957103 : Blo 614296 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B614815 : Blo 614296 614815 := bstep (se 1 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 614815 = 922223) B922223
theorem B614911 : Blo 614296 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B1041673 : Blo 614296 1041673 := bstep (se 2 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 1041673 = 781255) B781255
theorem B616303 : Blo 614296 616303 := bstep (se 1 (by rfl) ⟨462227, by rfl⟩ : syracuseStep 616303 = 924455) B924455
theorem B5269373 : Blo 614296 5269373 := bstep (se 3 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 5269373 = 1976015) B1976015
theorem B616607 : Blo 614296 616607 := bstep (se 1 (by rfl) ⟨462455, by rfl⟩ : syracuseStep 616607 = 924911) B924911
theorem B108030145 : Blo 614296 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B35547497 : Blo 614296 35547497 := bstep (se 2 (by rfl) ⟨13330311, by rfl⟩ : syracuseStep 35547497 = 26660623) B26660623
theorem B8448731 : Blo 614296 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B617211 : Blo 614296 617211 := bstep (se 1 (by rfl) ⟨462908, by rfl⟩ : syracuseStep 617211 = 925817) B925817
theorem B617319 : Blo 614296 617319 := bstep (se 1 (by rfl) ⟨462989, by rfl⟩ : syracuseStep 617319 = 925979) B925979
theorem B617627 : Blo 614296 617627 := bstep (se 1 (by rfl) ⟨463220, by rfl⟩ : syracuseStep 617627 = 926441) B926441
theorem B1831403 : Blo 614296 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B3043997 : Blo 614296 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B3109913 : Blo 614296 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B19036127 : Blo 614296 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B4454509 : Blo 614296 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B5929199 : Blo 614296 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B7306237 : Blo 614296 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B5340227 : Blo 614296 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B1670399 : Blo 614296 1670399 := bstep (se 1 (by rfl) ⟨1252799, by rfl⟩ : syracuseStep 1670399 = 2505599) B2505599
theorem B4489339 : Blo 614296 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B5276137 : Blo 614296 5276137 := bstep (se 2 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 5276137 = 3957103) B3957103
theorem B3113639 : Blo 614296 3113639 := bstep (se 1 (by rfl) ⟨2335229, by rfl⟩ : syracuseStep 3113639 = 4670459) B4670459
theorem B9963485 : Blo 614296 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B2952683 : Blo 614296 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B3509999 : Blo 614296 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B2625479 : Blo 614296 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B922079 : Blo 614296 922079 := bstep (se 1 (by rfl) ⟨691559, by rfl⟩ : syracuseStep 922079 = 1383119) B1383119
theorem B76125233 : Blo 614296 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B922715 : Blo 614296 922715 := bstep (se 1 (by rfl) ⟨692036, by rfl⟩ : syracuseStep 922715 = 1384073) B1384073
theorem B923183 : Blo 614296 923183 := bstep (se 1 (by rfl) ⟨692387, by rfl⟩ : syracuseStep 923183 = 1384775) B1384775
theorem B923375 : Blo 614296 923375 := bstep (se 1 (by rfl) ⟨692531, by rfl⟩ : syracuseStep 923375 = 1385063) B1385063
theorem B3512915 : Blo 614296 3512915 := bstep (se 1 (by rfl) ⟨2634686, by rfl⟩ : syracuseStep 3512915 = 5269373) B5269373
theorem B23698331 : Blo 614296 23698331 := bstep (se 1 (by rfl) ⟨17773748, by rfl⟩ : syracuseStep 23698331 = 35547497) B35547497
theorem B924779 : Blo 614296 924779 := bstep (se 1 (by rfl) ⟨693584, by rfl⟩ : syracuseStep 924779 = 1387169) B1387169
theorem B925823 : Blo 614296 925823 := bstep (se 1 (by rfl) ⟨694367, by rfl⟩ : syracuseStep 925823 = 1388735) B1388735
theorem B5939345 : Blo 614296 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B1220935 : Blo 614296 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B2073275 : Blo 614296 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B2958601 : Blo 614296 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B1385783 : Blo 614296 1385783 := bstep (se 1 (by rfl) ⟨1039337, by rfl⟩ : syracuseStep 1385783 = 2078675) B2078675
theorem B12690751 : Blo 614296 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B9741649 : Blo 614296 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B47982233 : Blo 614296 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B2107147 : Blo 614296 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B2631851 : Blo 614296 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B1387727 : Blo 614296 1387727 := bstep (se 1 (by rfl) ⟨1040795, by rfl⟩ : syracuseStep 1387727 = 2081591) B2081591
theorem B2338055 : Blo 614296 2338055 := bstep (se 1 (by rfl) ⟨1753541, by rfl⟩ : syracuseStep 2338055 = 3507083) B3507083
theorem B2503007 : Blo 614296 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B1388897 : Blo 614296 1388897 := bstep (se 2 (by rfl) ⟨520836, by rfl⟩ : syracuseStep 1388897 = 1041673) B1041673
theorem B1391039 : Blo 614296 1391039 := bstep (se 1 (by rfl) ⟨1043279, by rfl⟩ : syracuseStep 1391039 = 2086559) B2086559
theorem B17088497 : Blo 614296 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B7914617 : Blo 614296 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B2083535 : Blo 614296 2083535 := bstep (se 1 (by rfl) ⟨1562651, by rfl⟩ : syracuseStep 2083535 = 3125303) B3125303
theorem B14240605 : Blo 614296 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B2083967 : Blo 614296 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B3952799 : Blo 614296 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B4675805 : Blo 614296 4675805 := bstep (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) B1753427
theorem B3333079 : Blo 614296 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B48061511 : Blo 614296 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B10018237 : Blo 614296 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B1039871 : Blo 614296 1039871 := bstep (se 1 (by rfl) ⟨779903, by rfl⟩ : syracuseStep 1039871 = 1559807) B1559807
theorem B614399 : Blo 614296 614399 := bstep (se 1 (by rfl) ⟨460799, by rfl⟩ : syracuseStep 614399 = 921599) B921599
theorem B614427 : Blo 614296 614427 := bstep (se 1 (by rfl) ⟨460820, by rfl⟩ : syracuseStep 614427 = 921641) B921641
theorem B144040193 : Blo 614296 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B778567 : Blo 614296 778567 := bstep (se 1 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 778567 = 1167851) B1167851
theorem B614895 : Blo 614296 614895 := bstep (se 1 (by rfl) ⟨461171, by rfl⟩ : syracuseStep 614895 = 922343) B922343
theorem B615103 : Blo 614296 615103 := bstep (se 1 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 615103 = 922655) B922655
theorem B1172551 : Blo 614296 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B18998711 : Blo 614296 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B1042159 : Blo 614296 1042159 := bstep (se 1 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 1042159 = 1563239) B1563239
theorem B8906831 : Blo 614296 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B616699 : Blo 614296 616699 := bstep (se 1 (by rfl) ⟨462524, by rfl⟩ : syracuseStep 616699 = 925049) B925049
theorem B616775 : Blo 614296 616775 := bstep (se 1 (by rfl) ⟨462581, by rfl⟩ : syracuseStep 616775 = 925163) B925163
theorem B616959 : Blo 614296 616959 := bstep (se 1 (by rfl) ⟨462719, by rfl⟩ : syracuseStep 616959 = 925439) B925439
theorem B3500819 : Blo 614296 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B617279 : Blo 614296 617279 := bstep (se 1 (by rfl) ⟨462959, by rfl⟩ : syracuseStep 617279 = 925919) B925919
theorem B617791 : Blo 614296 617791 := bstep (se 1 (by rfl) ⟨463343, by rfl⟩ : syracuseStep 617791 = 926687) B926687
theorem B617887 : Blo 614296 617887 := bstep (se 1 (by rfl) ⟨463415, by rfl⟩ : syracuseStep 617887 = 926831) B926831
theorem B618215 : Blo 614296 618215 := bstep (se 1 (by rfl) ⟨463661, by rfl⟩ : syracuseStep 618215 = 927323) B927323
theorem B27684755 : Blo 614296 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B5632487 : Blo 614296 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B12613249 : Blo 614296 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B2029331 : Blo 614296 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B3341729 : Blo 614296 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B1113599 : Blo 614296 1113599 := bstep (se 1 (by rfl) ⟨835199, by rfl⟩ : syracuseStep 1113599 = 1670399) B1670399
theorem B3112667 : Blo 614296 3112667 := bstep (se 1 (by rfl) ⟨2334500, by rfl⟩ : syracuseStep 3112667 = 4669001) B4669001
theorem B5276411 : Blo 614296 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B1968455 : Blo 614296 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B3117203 : Blo 614296 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B15798887 : Blo 614296 15798887 := bstep (se 1 (by rfl) ⟨11849165, by rfl⟩ : syracuseStep 15798887 = 23698331) B23698331
theorem B5411549 : Blo 614296 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B693247 : Blo 614296 693247 := bstep (se 1 (by rfl) ⟨519935, by rfl⟩ : syracuseStep 693247 = 1039871) B1039871
theorem B1382183 : Blo 614296 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B923855 : Blo 614296 923855 := bstep (se 1 (by rfl) ⟨692891, by rfl⟩ : syracuseStep 923855 = 1385783) B1385783
theorem B5937887 : Blo 614296 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B2333879 : Blo 614296 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B925151 : Blo 614296 925151 := bstep (se 1 (by rfl) ⟨693863, by rfl⟩ : syracuseStep 925151 = 1387727) B1387727
theorem B16817665 : Blo 614296 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B18456503 : Blo 614296 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B925931 : Blo 614296 925931 := bstep (se 1 (by rfl) ⟨694448, by rfl⟩ : syracuseStep 925931 = 1388897) B1388897
theorem B927359 : Blo 614296 927359 := bstep (se 1 (by rfl) ⟨695519, by rfl⟩ : syracuseStep 927359 = 1391039) B1391039
theorem B2075111 : Blo 614296 2075111 := bstep (se 1 (by rfl) ⟨1556333, by rfl⟩ : syracuseStep 2075111 = 3112667) B3112667
theorem B15838253 : Blo 614296 15838253 := bstep (se 3 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 15838253 = 5939345) B5939345
theorem B2075759 : Blo 614296 2075759 := bstep (se 1 (by rfl) ⟨1556819, by rfl⟩ : syracuseStep 2075759 = 3113639) B3113639
theorem B3944801 : Blo 614296 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B16921001 : Blo 614296 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B12988865 : Blo 614296 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B1389023 : Blo 614296 1389023 := bstep (se 1 (by rfl) ⟨1041767, by rfl⟩ : syracuseStep 1389023 = 2083535) B2083535
theorem B1389311 : Blo 614296 1389311 := bstep (se 1 (by rfl) ⟨1041983, by rfl⟩ : syracuseStep 1389311 = 2083967) B2083967
theorem B1389545 : Blo 614296 1389545 := bstep (se 2 (by rfl) ⟨521079, by rfl⟩ : syracuseStep 1389545 = 1042159) B1042159
theorem B2339999 : Blo 614296 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B1750319 : Blo 614296 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B2635199 : Blo 614296 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B18987473 : Blo 614296 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B2341943 : Blo 614296 2341943 := bstep (se 1 (by rfl) ⟨1756457, by rfl⟩ : syracuseStep 2341943 = 3512915) B3512915
theorem B96026795 : Blo 614296 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B12665807 : Blo 614296 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B1754567 : Blo 614296 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B1558703 : Blo 614296 1558703 := bstep (se 1 (by rfl) ⟨1169027, by rfl⟩ : syracuseStep 1558703 = 2338055) B2338055
theorem B3754991 : Blo 614296 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B4444105 : Blo 614296 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B2969597 : Blo 614296 2969597 := bstep (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) B1113599
theorem B13357649 : Blo 614296 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B11392331 : Blo 614296 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B5985785 : Blo 614296 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B1038089 : Blo 614296 1038089 := bstep (se 2 (by rfl) ⟨389283, by rfl⟩ : syracuseStep 1038089 = 778567) B778567
theorem B1627913 : Blo 614296 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B7034849 : Blo 614296 7034849 := bstep (se 2 (by rfl) ⟨2638068, by rfl⟩ : syracuseStep 7034849 = 5276137) B5276137
theorem B6642323 : Blo 614296 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B1563401 : Blo 614296 1563401 := bstep (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) B1172551
theorem B2809529 : Blo 614296 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B614719 : Blo 614296 614719 := bstep (se 1 (by rfl) ⟨461039, by rfl⟩ : syracuseStep 614719 = 922079) B922079
theorem B50750155 : Blo 614296 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B615143 : Blo 614296 615143 := bstep (se 1 (by rfl) ⟨461357, by rfl⟩ : syracuseStep 615143 = 922715) B922715
theorem B615455 : Blo 614296 615455 := bstep (se 1 (by rfl) ⟨461591, by rfl⟩ : syracuseStep 615455 = 923183) B923183
theorem B615583 : Blo 614296 615583 := bstep (se 1 (by rfl) ⟨461687, by rfl⟩ : syracuseStep 615583 = 923375) B923375
theorem B127952621 : Blo 614296 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B32041007 : Blo 614296 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B616519 : Blo 614296 616519 := bstep (se 1 (by rfl) ⟨462389, by rfl⟩ : syracuseStep 616519 = 924779) B924779
theorem B617215 : Blo 614296 617215 := bstep (se 1 (by rfl) ⟨462911, by rfl⟩ : syracuseStep 617215 = 925823) B925823
theorem B1668671 : Blo 614296 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B2227819 : Blo 614296 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B10519469 : Blo 614296 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B67666873 : Blo 614296 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B1312303 : Blo 614296 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B30379549 : Blo 614296 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B692059 : Blo 614296 692059 := bstep (se 1 (by rfl) ⟨519044, by rfl⟩ : syracuseStep 692059 = 1038089) B1038089
theorem B1085275 : Blo 614296 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B921455 : Blo 614296 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B4689899 : Blo 614296 4689899 := bstep (se 1 (by rfl) ⟨3517424, by rfl⟩ : syracuseStep 4689899 = 7034849) B7034849
theorem B15962093 : Blo 614296 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B4428215 : Blo 614296 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B1873019 : Blo 614296 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B85301747 : Blo 614296 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B924329 : Blo 614296 924329 := bstep (se 2 (by rfl) ⟨346623, by rfl⟩ : syracuseStep 924329 = 693247) B693247
theorem B1383407 : Blo 614296 1383407 := bstep (se 1 (by rfl) ⟨1037555, by rfl⟩ : syracuseStep 1383407 = 2075111) B2075111
theorem B10558835 : Blo 614296 10558835 := bstep (se 1 (by rfl) ⟨7919126, by rfl⟩ : syracuseStep 10558835 = 15838253) B15838253
theorem B1383839 : Blo 614296 1383839 := bstep (se 1 (by rfl) ⟨1037879, by rfl⟩ : syracuseStep 1383839 = 2075759) B2075759
theorem B11280667 : Blo 614296 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B8659243 : Blo 614296 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B926015 : Blo 614296 926015 := bstep (se 1 (by rfl) ⟨694511, by rfl⟩ : syracuseStep 926015 = 1389023) B1389023
theorem B926207 : Blo 614296 926207 := bstep (se 1 (by rfl) ⟨694655, by rfl⟩ : syracuseStep 926207 = 1389311) B1389311
theorem B926363 : Blo 614296 926363 := bstep (se 1 (by rfl) ⟨694772, by rfl⟩ : syracuseStep 926363 = 1389545) B1389545
theorem B12658315 : Blo 614296 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B22423553 : Blo 614296 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B3517607 : Blo 614296 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B14430797 : Blo 614296 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B2503327 : Blo 614296 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B1979731 : Blo 614296 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B2078135 : Blo 614296 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B10532591 : Blo 614296 10532591 := bstep (se 1 (by rfl) ⟨7899443, by rfl⟩ : syracuseStep 10532591 = 15798887) B15798887
theorem B1555919 : Blo 614296 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B1559999 : Blo 614296 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B1166879 : Blo 614296 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B1756799 : Blo 614296 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1561295 : Blo 614296 1561295 := bstep (se 1 (by rfl) ⟨1170971, by rfl⟩ : syracuseStep 1561295 = 2341943) B2341943
theorem B2970425 : Blo 614296 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B64017863 : Blo 614296 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B8443871 : Blo 614296 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B1169711 : Blo 614296 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B1039135 : Blo 614296 1039135 := bstep (se 1 (by rfl) ⟨779351, by rfl⟩ : syracuseStep 1039135 = 1558703) B1558703
theorem B8905099 : Blo 614296 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B615903 : Blo 614296 615903 := bstep (se 1 (by rfl) ⟨461927, by rfl⟩ : syracuseStep 615903 = 923855) B923855
theorem B3958591 : Blo 614296 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B1042267 : Blo 614296 1042267 := bstep (se 1 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 1042267 = 1563401) B1563401
theorem B616767 : Blo 614296 616767 := bstep (se 1 (by rfl) ⟨462575, by rfl⟩ : syracuseStep 616767 = 925151) B925151
theorem B5925473 : Blo 614296 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B617287 : Blo 614296 617287 := bstep (se 1 (by rfl) ⟨462965, by rfl⟩ : syracuseStep 617287 = 925931) B925931
theorem B618239 : Blo 614296 618239 := bstep (se 1 (by rfl) ⟨463679, by rfl⟩ : syracuseStep 618239 = 927359) B927359
theorem B21360671 : Blo 614296 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B1112447 : Blo 614296 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B49217341 : Blo 614296 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B15040889 : Blo 614296 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B7012979 : Blo 614296 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B16877753 : Blo 614296 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B5278121 : Blo 614296 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B2952143 : Blo 614296 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B1248679 : Blo 614296 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B922271 : Blo 614296 922271 := bstep (se 1 (by rfl) ⟨691703, by rfl⟩ : syracuseStep 922271 = 1383407) B1383407
theorem B40506065 : Blo 614296 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B922559 : Blo 614296 922559 := bstep (se 1 (by rfl) ⟨691919, by rfl⟩ : syracuseStep 922559 = 1383839) B1383839
theorem B922745 : Blo 614296 922745 := bstep (se 2 (by rfl) ⟨346029, by rfl⟩ : syracuseStep 922745 = 692059) B692059
theorem B1447033 : Blo 614296 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B14949035 : Blo 614296 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B1385423 : Blo 614296 1385423 := bstep (se 1 (by rfl) ⟨1039067, by rfl⟩ : syracuseStep 1385423 = 2078135) B2078135
theorem B1385513 : Blo 614296 1385513 := bstep (se 2 (by rfl) ⟨519567, by rfl⟩ : syracuseStep 1385513 = 1039135) B1039135
theorem B7021727 : Blo 614296 7021727 := bstep (se 1 (by rfl) ⟨5266295, by rfl⟩ : syracuseStep 7021727 = 10532591) B10532591
theorem B11873465 : Blo 614296 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B90222497 : Blo 614296 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B46182629 : Blo 614296 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B1749737 : Blo 614296 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B1389689 : Blo 614296 1389689 := bstep (se 2 (by rfl) ⟨521133, by rfl⟩ : syracuseStep 1389689 = 1042267) B1042267
theorem B3126599 : Blo 614296 3126599 := bstep (se 1 (by rfl) ⟨2344949, by rfl⟩ : syracuseStep 3126599 = 4689899) B4689899
theorem B1980283 : Blo 614296 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B42678575 : Blo 614296 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B56867831 : Blo 614296 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B3950315 : Blo 614296 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B2639641 : Blo 614296 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B2345071 : Blo 614296 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B14240447 : Blo 614296 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B9620531 : Blo 614296 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B741631 : Blo 614296 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B1037279 : Blo 614296 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B65623121 : Blo 614296 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B1039999 : Blo 614296 1039999 := bstep (se 1 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 1039999 = 1559999) B1559999
theorem B777919 : Blo 614296 777919 := bstep (se 1 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 777919 = 1166879) B1166879
theorem B1171199 : Blo 614296 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B614303 : Blo 614296 614303 := bstep (se 1 (by rfl) ⟨460727, by rfl⟩ : syracuseStep 614303 = 921455) B921455
theorem B10641395 : Blo 614296 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B1040863 : Blo 614296 1040863 := bstep (se 1 (by rfl) ⟨780647, by rfl⟩ : syracuseStep 1040863 = 1561295) B1561295
theorem B5629247 : Blo 614296 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B779807 : Blo 614296 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B616219 : Blo 614296 616219 := bstep (se 1 (by rfl) ⟨462164, by rfl⟩ : syracuseStep 616219 = 924329) B924329
theorem B7039223 : Blo 614296 7039223 := bstep (se 1 (by rfl) ⟨5279417, by rfl⟩ : syracuseStep 7039223 = 10558835) B10558835
theorem B617343 : Blo 614296 617343 := bstep (se 1 (by rfl) ⟨463007, by rfl⟩ : syracuseStep 617343 = 926015) B926015
theorem B617471 : Blo 614296 617471 := bstep (se 1 (by rfl) ⟨463103, by rfl⟩ : syracuseStep 617471 = 926207) B926207
theorem B617575 : Blo 614296 617575 := bstep (se 1 (by rfl) ⟨463181, by rfl⟩ : syracuseStep 617575 = 926363) B926363
theorem B3337769 : Blo 614296 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B10027259 : Blo 614296 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B1968095 : Blo 614296 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B27004043 : Blo 614296 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B691519 : Blo 614296 691519 := bstep (se 1 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 691519 = 1037279) B1037279
theorem B43748747 : Blo 614296 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B9966023 : Blo 614296 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B988841 : Blo 614296 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B923615 : Blo 614296 923615 := bstep (se 1 (by rfl) ⟨692711, by rfl⟩ : syracuseStep 923615 = 1385423) B1385423
theorem B923675 : Blo 614296 923675 := bstep (se 1 (by rfl) ⟨692756, by rfl⟩ : syracuseStep 923675 = 1385513) B1385513
theorem B4692815 : Blo 614296 4692815 := bstep (se 1 (by rfl) ⟨3519611, by rfl⟩ : syracuseStep 4692815 = 7039223) B7039223
theorem B6659621 : Blo 614296 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B926459 : Blo 614296 926459 := bstep (se 1 (by rfl) ⟨694844, by rfl⟩ : syracuseStep 926459 = 1389689) B1389689
theorem B28452383 : Blo 614296 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B3123197 : Blo 614296 3123197 := bstep (se 3 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 3123197 = 1171199) B1171199
theorem B1386665 : Blo 614296 1386665 := bstep (se 2 (by rfl) ⟨519999, by rfl⟩ : syracuseStep 1386665 = 1039999) B1039999
theorem B1387817 : Blo 614296 1387817 := bstep (se 2 (by rfl) ⟨520431, by rfl⟩ : syracuseStep 1387817 = 1040863) B1040863
theorem B2633543 : Blo 614296 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B11251835 : Blo 614296 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B3518747 : Blo 614296 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B3519521 : Blo 614296 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B3126761 : Blo 614296 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B2079485 : Blo 614296 2079485 := bstep (se 3 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 2079485 = 779807) B779807
theorem B7094263 : Blo 614296 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B3752831 : Blo 614296 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B7915643 : Blo 614296 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B2640377 : Blo 614296 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B60148331 : Blo 614296 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B30788419 : Blo 614296 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B1166491 : Blo 614296 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B2084399 : Blo 614296 2084399 := bstep (se 1 (by rfl) ⟨1563299, by rfl⟩ : syracuseStep 2084399 = 3126599) B3126599
theorem B1037225 : Blo 614296 1037225 := bstep (se 2 (by rfl) ⟨388959, by rfl⟩ : syracuseStep 1037225 = 777919) B777919
theorem B4675319 : Blo 614296 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B9493631 : Blo 614296 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B6413687 : Blo 614296 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B614847 : Blo 614296 614847 := bstep (se 1 (by rfl) ⟨461135, by rfl⟩ : syracuseStep 614847 = 922271) B922271
theorem B615039 : Blo 614296 615039 := bstep (se 1 (by rfl) ⟨461279, by rfl⟩ : syracuseStep 615039 = 922559) B922559
theorem B615163 : Blo 614296 615163 := bstep (se 1 (by rfl) ⟨461372, by rfl⟩ : syracuseStep 615163 = 922745) B922745
theorem B4681151 : Blo 614296 4681151 := bstep (se 1 (by rfl) ⟨3510863, by rfl⟩ : syracuseStep 4681151 = 7021727) B7021727
theorem B1929377 : Blo 614296 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B2225179 : Blo 614296 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B37911887 : Blo 614296 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B6684839 : Blo 614296 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B5145005 : Blo 614296 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B5277095 : Blo 614296 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B29165831 : Blo 614296 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B691483 : Blo 614296 691483 := bstep (se 1 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 691483 = 1037225) B1037225
theorem B659227 : Blo 614296 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B3116879 : Blo 614296 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B922025 : Blo 614296 922025 := bstep (se 2 (by rfl) ⟨345759, by rfl⟩ : syracuseStep 922025 = 691519) B691519
theorem B6329087 : Blo 614296 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B5248253 : Blo 614296 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B924443 : Blo 614296 924443 := bstep (se 1 (by rfl) ⟨693332, by rfl⟩ : syracuseStep 924443 = 1386665) B1386665
theorem B925211 : Blo 614296 925211 := bstep (se 1 (by rfl) ⟨693908, by rfl⟩ : syracuseStep 925211 = 1387817) B1387817
theorem B3120767 : Blo 614296 3120767 := bstep (se 1 (by rfl) ⟨2340575, by rfl⟩ : syracuseStep 3120767 = 4681151) B4681151
theorem B1386323 : Blo 614296 1386323 := bstep (se 1 (by rfl) ⟨1039742, by rfl⟩ : syracuseStep 1386323 = 2079485) B2079485
theorem B25274591 : Blo 614296 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B2501887 : Blo 614296 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B1389599 : Blo 614296 1389599 := bstep (se 1 (by rfl) ⟨1042199, by rfl⟩ : syracuseStep 1389599 = 2084399) B2084399
theorem B1555321 : Blo 614296 1555321 := bstep (se 2 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 1555321 = 1166491) B1166491
theorem B3128543 : Blo 614296 3128543 := bstep (se 1 (by rfl) ⟨2346407, by rfl⟩ : syracuseStep 3128543 = 4692815) B4692815
theorem B4275791 : Blo 614296 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B4439747 : Blo 614296 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B2082131 : Blo 614296 2082131 := bstep (se 1 (by rfl) ⟨1561598, by rfl⟩ : syracuseStep 2082131 = 3123197) B3123197
theorem B2966905 : Blo 614296 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B1755695 : Blo 614296 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B2345831 : Blo 614296 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B72010781 : Blo 614296 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B2346347 : Blo 614296 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B2084507 : Blo 614296 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B9459017 : Blo 614296 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B1760251 : Blo 614296 1760251 := bstep (se 1 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 1760251 = 2640377) B2640377
theorem B40098887 : Blo 614296 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B6644015 : Blo 614296 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B41051225 : Blo 614296 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B615743 : Blo 614296 615743 := bstep (se 1 (by rfl) ⟨461807, by rfl⟩ : syracuseStep 615743 = 923615) B923615
theorem B615783 : Blo 614296 615783 := bstep (se 1 (by rfl) ⟨461837, by rfl⟩ : syracuseStep 615783 = 923675) B923675
theorem B617639 : Blo 614296 617639 := bstep (se 1 (by rfl) ⟨463229, by rfl⟩ : syracuseStep 617639 = 926459) B926459
theorem B18968255 : Blo 614296 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B7501223 : Blo 614296 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B4456559 : Blo 614296 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B48007187 : Blo 614296 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B921977 : Blo 614296 921977 := bstep (se 2 (by rfl) ⟨345741, by rfl⟩ : syracuseStep 921977 = 691483) B691483
theorem B4429343 : Blo 614296 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B27367483 : Blo 614296 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B924215 : Blo 614296 924215 := bstep (se 1 (by rfl) ⟨693161, by rfl⟩ : syracuseStep 924215 = 1386323) B1386323
theorem B16849727 : Blo 614296 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B926399 : Blo 614296 926399 := bstep (se 1 (by rfl) ⟨694799, by rfl⟩ : syracuseStep 926399 = 1389599) B1389599
theorem B2073761 : Blo 614296 2073761 := bstep (se 2 (by rfl) ⟨777660, by rfl⟩ : syracuseStep 2073761 = 1555321) B1555321
theorem B2959831 : Blo 614296 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B1388087 : Blo 614296 1388087 := bstep (se 1 (by rfl) ⟨1041065, by rfl⟩ : syracuseStep 1388087 = 2082131) B2082131
theorem B3518063 : Blo 614296 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B19443887 : Blo 614296 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B1389671 : Blo 614296 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B2077919 : Blo 614296 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B6306011 : Blo 614296 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B2080511 : Blo 614296 2080511 := bstep (se 1 (by rfl) ⟨1560383, by rfl⟩ : syracuseStep 2080511 = 3120767) B3120767
theorem B5000815 : Blo 614296 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B2347001 : Blo 614296 2347001 := bstep (se 2 (by rfl) ⟨880125, by rfl⟩ : syracuseStep 2347001 = 1760251) B1760251
theorem B2085695 : Blo 614296 2085695 := bstep (se 1 (by rfl) ⟨1564271, by rfl⟩ : syracuseStep 2085695 = 3128543) B3128543
theorem B13720013 : Blo 614296 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1170463 : Blo 614296 1170463 := bstep (se 1 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 1170463 = 1755695) B1755695
theorem B3955873 : Blo 614296 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B1563887 : Blo 614296 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B1564231 : Blo 614296 1564231 := bstep (se 1 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 1564231 = 2346347) B2346347
theorem B614683 : Blo 614296 614683 := bstep (se 1 (by rfl) ⟨461012, by rfl⟩ : syracuseStep 614683 = 922025) B922025
theorem B4219391 : Blo 614296 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B3498835 : Blo 614296 3498835 := bstep (se 1 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 3498835 = 5248253) B5248253
theorem B3335849 : Blo 614296 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B616295 : Blo 614296 616295 := bstep (se 1 (by rfl) ⟨462221, by rfl⟩ : syracuseStep 616295 = 924443) B924443
theorem B26732591 : Blo 614296 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B616807 : Blo 614296 616807 := bstep (se 1 (by rfl) ⟨462605, by rfl⟩ : syracuseStep 616807 = 925211) B925211
theorem B878969 : Blo 614296 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B12645503 : Blo 614296 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B2850527 : Blo 614296 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B2952895 : Blo 614296 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B9146675 : Blo 614296 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B1382507 : Blo 614296 1382507 := bstep (se 1 (by rfl) ⟨1036880, by rfl⟩ : syracuseStep 1382507 = 2073761) B2073761
theorem B925391 : Blo 614296 925391 := bstep (se 1 (by rfl) ⟨694043, by rfl⟩ : syracuseStep 925391 = 1388087) B1388087
theorem B926447 : Blo 614296 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B8430335 : Blo 614296 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B1385279 : Blo 614296 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B4204007 : Blo 614296 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B1387007 : Blo 614296 1387007 := bstep (se 1 (by rfl) ⟨1040255, by rfl⟩ : syracuseStep 1387007 = 2080511) B2080511
theorem B4665113 : Blo 614296 4665113 := bstep (se 2 (by rfl) ⟨1749417, by rfl⟩ : syracuseStep 4665113 = 3498835) B3498835
theorem B1390463 : Blo 614296 1390463 := bstep (se 1 (by rfl) ⟨1042847, by rfl⟩ : syracuseStep 1390463 = 2085695) B2085695
theorem B6667753 : Blo 614296 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B2343917 : Blo 614296 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B2345375 : Blo 614296 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B36489977 : Blo 614296 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B12962591 : Blo 614296 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1560617 : Blo 614296 1560617 := bstep (se 2 (by rfl) ⟨585231, by rfl⟩ : syracuseStep 1560617 = 1170463) B1170463
theorem B2085641 : Blo 614296 2085641 := bstep (se 2 (by rfl) ⟨782115, by rfl⟩ : syracuseStep 2085641 = 1564231) B1564231
theorem B11884157 : Blo 614296 11884157 := bstep (se 3 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 11884157 = 4456559) B4456559
theorem B32004791 : Blo 614296 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B15785765 : Blo 614296 15785765 := bstep (se 4 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 15785765 = 2959831) B2959831
theorem B1564667 : Blo 614296 1564667 := bstep (se 1 (by rfl) ⟨1173500, by rfl⟩ : syracuseStep 1564667 = 2347001) B2347001
theorem B614651 : Blo 614296 614651 := bstep (se 1 (by rfl) ⟨460988, by rfl⟩ : syracuseStep 614651 = 921977) B921977
theorem B616143 : Blo 614296 616143 := bstep (se 1 (by rfl) ⟨462107, by rfl⟩ : syracuseStep 616143 = 924215) B924215
theorem B11233151 : Blo 614296 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B1042591 : Blo 614296 1042591 := bstep (se 1 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 1042591 = 1563887) B1563887
theorem B2812927 : Blo 614296 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B617599 : Blo 614296 617599 := bstep (se 1 (by rfl) ⟨463199, by rfl⟩ : syracuseStep 617599 = 926399) B926399
theorem B2223899 : Blo 614296 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B17821727 : Blo 614296 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B5274497 : Blo 614296 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B1900351 : Blo 614296 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B6097783 : Blo 614296 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B921671 : Blo 614296 921671 := bstep (se 1 (by rfl) ⟨691253, by rfl⟩ : syracuseStep 921671 = 1382507) B1382507
theorem B21336527 : Blo 614296 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B3937193 : Blo 614296 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B10523843 : Blo 614296 10523843 := bstep (se 1 (by rfl) ⟨7892882, by rfl⟩ : syracuseStep 10523843 = 15785765) B15785765
theorem B923519 : Blo 614296 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B924671 : Blo 614296 924671 := bstep (se 1 (by rfl) ⟨693503, by rfl⟩ : syracuseStep 924671 = 1387007) B1387007
theorem B1482599 : Blo 614296 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B926975 : Blo 614296 926975 := bstep (se 1 (by rfl) ⟨695231, by rfl⟩ : syracuseStep 926975 = 1390463) B1390463
theorem B10135205 : Blo 614296 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B3516331 : Blo 614296 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B8890337 : Blo 614296 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B24326651 : Blo 614296 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B1390121 : Blo 614296 1390121 := bstep (se 2 (by rfl) ⟨521295, by rfl⟩ : syracuseStep 1390121 = 1042591) B1042591
theorem B1390427 : Blo 614296 1390427 := bstep (se 1 (by rfl) ⟨1042820, by rfl⟩ : syracuseStep 1390427 = 2085641) B2085641
theorem B3750569 : Blo 614296 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B5620223 : Blo 614296 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B2802671 : Blo 614296 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B7488767 : Blo 614296 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B11881151 : Blo 614296 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B1562611 : Blo 614296 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B1563583 : Blo 614296 1563583 := bstep (se 1 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 1563583 = 2345375) B2345375
theorem B8641727 : Blo 614296 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B1040411 : Blo 614296 1040411 := bstep (se 1 (by rfl) ⟨780308, by rfl⟩ : syracuseStep 1040411 = 1560617) B1560617
theorem B7922771 : Blo 614296 7922771 := bstep (se 1 (by rfl) ⟨5942078, by rfl⟩ : syracuseStep 7922771 = 11884157) B11884157
theorem B616927 : Blo 614296 616927 := bstep (se 1 (by rfl) ⟨462695, by rfl⟩ : syracuseStep 616927 = 925391) B925391
theorem B1043111 : Blo 614296 1043111 := bstep (se 1 (by rfl) ⟨782333, by rfl⟩ : syracuseStep 1043111 = 1564667) B1564667
theorem B617631 : Blo 614296 617631 := bstep (se 1 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 617631 = 926447) B926447
theorem B3110075 : Blo 614296 3110075 := bstep (se 1 (by rfl) ⟨2332556, by rfl⟩ : syracuseStep 3110075 = 4665113) B4665113
theorem B1868447 : Blo 614296 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B4688441 : Blo 614296 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B14224351 : Blo 614296 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B2624795 : Blo 614296 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B7015895 : Blo 614296 7015895 := bstep (se 1 (by rfl) ⟨5261921, by rfl⟩ : syracuseStep 7015895 = 10523843) B10523843
theorem B8130377 : Blo 614296 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B988399 : Blo 614296 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B693607 : Blo 614296 693607 := bstep (se 1 (by rfl) ⟨520205, by rfl⟩ : syracuseStep 693607 = 1040411) B1040411
theorem B5281847 : Blo 614296 5281847 := bstep (se 1 (by rfl) ⟨3961385, by rfl⟩ : syracuseStep 5281847 = 7922771) B7922771
theorem B6756803 : Blo 614296 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B695407 : Blo 614296 695407 := bstep (se 1 (by rfl) ⟨521555, by rfl⟩ : syracuseStep 695407 = 1043111) B1043111
theorem B2073383 : Blo 614296 2073383 := bstep (se 1 (by rfl) ⟨1555037, by rfl⟩ : syracuseStep 2073383 = 3110075) B3110075
theorem B926747 : Blo 614296 926747 := bstep (se 1 (by rfl) ⟨695060, by rfl⟩ : syracuseStep 926747 = 1390121) B1390121
theorem B926951 : Blo 614296 926951 := bstep (se 1 (by rfl) ⟨695213, by rfl⟩ : syracuseStep 926951 = 1390427) B1390427
theorem B2500379 : Blo 614296 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B4992511 : Blo 614296 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B14987261 : Blo 614296 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B2083481 : Blo 614296 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B2084777 : Blo 614296 2084777 := bstep (se 2 (by rfl) ⟨781791, by rfl⟩ : syracuseStep 2084777 = 1563583) B1563583
theorem B7920767 : Blo 614296 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B614447 : Blo 614296 614447 := bstep (se 1 (by rfl) ⟨460835, by rfl⟩ : syracuseStep 614447 = 921671) B921671
theorem B615679 : Blo 614296 615679 := bstep (se 1 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 615679 = 923519) B923519
theorem B616447 : Blo 614296 616447 := bstep (se 1 (by rfl) ⟨462335, by rfl⟩ : syracuseStep 616447 = 924671) B924671
theorem B5761151 : Blo 614296 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B617983 : Blo 614296 617983 := bstep (se 1 (by rfl) ⟨463487, by rfl⟩ : syracuseStep 617983 = 926975) B926975
theorem B5926891 : Blo 614296 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B16217767 : Blo 614296 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B1245631 : Blo 614296 1245631 := bstep (se 1 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 1245631 = 1868447) B1868447
theorem B6656681 : Blo 614296 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B5280511 : Blo 614296 5280511 := bstep (se 1 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 5280511 = 7920767) B7920767
theorem B7902521 : Blo 614296 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B1382255 : Blo 614296 1382255 := bstep (se 1 (by rfl) ⟨1036691, by rfl⟩ : syracuseStep 1382255 = 2073383) B2073383
theorem B3840767 : Blo 614296 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B1317865 : Blo 614296 1317865 := bstep (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) B988399
theorem B924809 : Blo 614296 924809 := bstep (se 2 (by rfl) ⟨346803, by rfl⟩ : syracuseStep 924809 = 693607) B693607
theorem B927209 : Blo 614296 927209 := bstep (se 2 (by rfl) ⟨347703, by rfl⟩ : syracuseStep 927209 = 695407) B695407
theorem B3125627 : Blo 614296 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B1388987 : Blo 614296 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B1749863 : Blo 614296 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B5420251 : Blo 614296 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1389851 : Blo 614296 1389851 := bstep (se 1 (by rfl) ⟨1042388, by rfl⟩ : syracuseStep 1389851 = 2084777) B2084777
theorem B3521231 : Blo 614296 3521231 := bstep (se 1 (by rfl) ⟨2640923, by rfl⟩ : syracuseStep 3521231 = 5281847) B5281847
theorem B4504535 : Blo 614296 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B4677263 : Blo 614296 4677263 := bstep (se 1 (by rfl) ⟨3507947, by rfl⟩ : syracuseStep 4677263 = 7015895) B7015895
theorem B18965801 : Blo 614296 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B617831 : Blo 614296 617831 := bstep (se 1 (by rfl) ⟨463373, by rfl⟩ : syracuseStep 617831 = 926747) B926747
theorem B617967 : Blo 614296 617967 := bstep (se 1 (by rfl) ⟨463475, by rfl⟩ : syracuseStep 617967 = 926951) B926951
theorem B1666919 : Blo 614296 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B21623689 : Blo 614296 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B9991507 : Blo 614296 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B921503 : Blo 614296 921503 := bstep (se 1 (by rfl) ⟨691127, by rfl⟩ : syracuseStep 921503 = 1382255) B1382255
theorem B2560511 : Blo 614296 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B3118175 : Blo 614296 3118175 := bstep (se 1 (by rfl) ⟨2338631, by rfl⟩ : syracuseStep 3118175 = 4677263) B4677263
theorem B925991 : Blo 614296 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B926567 : Blo 614296 926567 := bstep (se 1 (by rfl) ⟨694925, by rfl⟩ : syracuseStep 926567 = 1389851) B1389851
theorem B115326341 : Blo 614296 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B7227001 : Blo 614296 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B13322009 : Blo 614296 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B2083751 : Blo 614296 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B1166575 : Blo 614296 1166575 := bstep (se 1 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 1166575 = 1749863) B1749863
theorem B1757153 : Blo 614296 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B2347487 : Blo 614296 2347487 := bstep (se 1 (by rfl) ⟨1760615, by rfl⟩ : syracuseStep 2347487 = 3521231) B3521231
theorem B3003023 : Blo 614296 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1660841 : Blo 614296 1660841 := bstep (se 2 (by rfl) ⟨622815, by rfl⟩ : syracuseStep 1660841 = 1245631) B1245631
theorem B17751149 : Blo 614296 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B5268347 : Blo 614296 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B616539 : Blo 614296 616539 := bstep (se 1 (by rfl) ⟨462404, by rfl⟩ : syracuseStep 616539 = 924809) B924809
theorem B12643867 : Blo 614296 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B618139 : Blo 614296 618139 := bstep (se 1 (by rfl) ⟨463604, by rfl⟩ : syracuseStep 618139 = 927209) B927209
theorem B7040681 : Blo 614296 7040681 := bstep (se 2 (by rfl) ⟨2640255, by rfl⟩ : syracuseStep 7040681 = 5280511) B5280511
theorem B1111279 : Blo 614296 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B8881339 : Blo 614296 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B1707007 : Blo 614296 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B2002015 : Blo 614296 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B11834099 : Blo 614296 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B3512231 : Blo 614296 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B1481705 : Blo 614296 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B4693787 : Blo 614296 4693787 := bstep (se 1 (by rfl) ⟨3520340, by rfl⟩ : syracuseStep 4693787 = 7040681) B7040681
theorem B38544005 : Blo 614296 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B76884227 : Blo 614296 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B1389167 : Blo 614296 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B2078783 : Blo 614296 2078783 := bstep (se 1 (by rfl) ⟨1559087, by rfl⟩ : syracuseStep 2078783 = 3118175) B3118175
theorem B1555433 : Blo 614296 1555433 := bstep (se 2 (by rfl) ⟨583287, by rfl⟩ : syracuseStep 1555433 = 1166575) B1166575
theorem B614335 : Blo 614296 614335 := bstep (se 1 (by rfl) ⟨460751, by rfl⟩ : syracuseStep 614335 = 921503) B921503
theorem B1171435 : Blo 614296 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B1564991 : Blo 614296 1564991 := bstep (se 1 (by rfl) ⟨1173743, by rfl⟩ : syracuseStep 1564991 = 2347487) B2347487
theorem B1107227 : Blo 614296 1107227 := bstep (se 1 (by rfl) ⟨830420, by rfl⟩ : syracuseStep 1107227 = 1660841) B1660841
theorem B617327 : Blo 614296 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B617711 : Blo 614296 617711 := bstep (se 1 (by rfl) ⟨463283, by rfl⟩ : syracuseStep 617711 = 926567) B926567
theorem B67433957 : Blo 614296 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B2952605 : Blo 614296 2952605 := bstep (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) B1107227
theorem B987803 : Blo 614296 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B25696003 : Blo 614296 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B51256151 : Blo 614296 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B926111 : Blo 614296 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B1385855 : Blo 614296 1385855 := bstep (se 1 (by rfl) ⟨1039391, by rfl⟩ : syracuseStep 1385855 = 2078783) B2078783
theorem B11841785 : Blo 614296 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B2341487 : Blo 614296 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B2276009 : Blo 614296 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B3129191 : Blo 614296 3129191 := bstep (se 1 (by rfl) ⟨2346893, by rfl⟩ : syracuseStep 3129191 = 4693787) B4693787
theorem B1036955 : Blo 614296 1036955 := bstep (se 1 (by rfl) ⟨777716, by rfl⟩ : syracuseStep 1036955 = 1555433) B1555433
theorem B1561913 : Blo 614296 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B7889399 : Blo 614296 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B1043327 : Blo 614296 1043327 := bstep (se 1 (by rfl) ⟨782495, by rfl⟩ : syracuseStep 1043327 = 1564991) B1564991
theorem B10677413 : Blo 614296 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B44955971 : Blo 614296 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B1968403 : Blo 614296 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B691303 : Blo 614296 691303 := bstep (se 1 (by rfl) ⟨518477, by rfl⟩ : syracuseStep 691303 = 1036955) B1036955
theorem B658535 : Blo 614296 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B923903 : Blo 614296 923903 := bstep (se 1 (by rfl) ⟨692927, by rfl⟩ : syracuseStep 923903 = 1385855) B1385855
theorem B695551 : Blo 614296 695551 := bstep (se 1 (by rfl) ⟨521663, by rfl⟩ : syracuseStep 695551 = 1043327) B1043327
theorem B7118275 : Blo 614296 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B1517339 : Blo 614296 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B5259599 : Blo 614296 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B34261337 : Blo 614296 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B29970647 : Blo 614296 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B1560991 : Blo 614296 1560991 := bstep (se 1 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 1560991 = 2341487) B2341487
theorem B2086127 : Blo 614296 2086127 := bstep (se 1 (by rfl) ⟨1564595, by rfl⟩ : syracuseStep 2086127 = 3129191) B3129191
theorem B1041275 : Blo 614296 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B34170767 : Blo 614296 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B617407 : Blo 614296 617407 := bstep (se 1 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 617407 = 926111) B926111
theorem B7894523 : Blo 614296 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B3506399 : Blo 614296 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B2624537 : Blo 614296 2624537 := bstep (se 2 (by rfl) ⟨984201, by rfl⟩ : syracuseStep 2624537 = 1968403) B1968403
theorem B921737 : Blo 614296 921737 := bstep (se 2 (by rfl) ⟨345651, by rfl⟩ : syracuseStep 921737 = 691303) B691303
theorem B694183 : Blo 614296 694183 := bstep (se 1 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 694183 = 1041275) B1041275
theorem B91363565 : Blo 614296 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B22780511 : Blo 614296 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B927401 : Blo 614296 927401 := bstep (se 2 (by rfl) ⟨347775, by rfl⟩ : syracuseStep 927401 = 695551) B695551
theorem B1390751 : Blo 614296 1390751 := bstep (se 1 (by rfl) ⟨1043063, by rfl⟩ : syracuseStep 1390751 = 2086127) B2086127
theorem B2081321 : Blo 614296 2081321 := bstep (se 2 (by rfl) ⟨780495, by rfl⟩ : syracuseStep 2081321 = 1560991) B1560991
theorem B1756093 : Blo 614296 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B5263015 : Blo 614296 5263015 := bstep (se 1 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 5263015 = 7894523) B7894523
theorem B9491033 : Blo 614296 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B19980431 : Blo 614296 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B615935 : Blo 614296 615935 := bstep (se 1 (by rfl) ⟨461951, by rfl⟩ : syracuseStep 615935 = 923903) B923903
theorem B1011559 : Blo 614296 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B7017353 : Blo 614296 7017353 := bstep (se 2 (by rfl) ⟨2631507, by rfl⟩ : syracuseStep 7017353 = 5263015) B5263015
theorem B1348745 : Blo 614296 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B925577 : Blo 614296 925577 := bstep (se 2 (by rfl) ⟨347091, by rfl⟩ : syracuseStep 925577 = 694183) B694183
theorem B927167 : Blo 614296 927167 := bstep (se 1 (by rfl) ⟨695375, by rfl⟩ : syracuseStep 927167 = 1390751) B1390751
theorem B2337599 : Blo 614296 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B1387547 : Blo 614296 1387547 := bstep (se 1 (by rfl) ⟨1040660, by rfl⟩ : syracuseStep 1387547 = 2081321) B2081321
theorem B25309421 : Blo 614296 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B1749691 : Blo 614296 1749691 := bstep (se 1 (by rfl) ⟨1312268, by rfl⟩ : syracuseStep 1749691 = 2624537) B2624537
theorem B2341457 : Blo 614296 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B15187007 : Blo 614296 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B13320287 : Blo 614296 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B614491 : Blo 614296 614491 := bstep (se 1 (by rfl) ⟨460868, by rfl⟩ : syracuseStep 614491 = 921737) B921737
theorem B60909043 : Blo 614296 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B618267 : Blo 614296 618267 := bstep (se 1 (by rfl) ⟨463700, by rfl⟩ : syracuseStep 618267 = 927401) B927401
theorem B8880191 : Blo 614296 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B2332921 : Blo 614296 2332921 := bstep (se 2 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 2332921 = 1749691) B1749691
theorem B925031 : Blo 614296 925031 := bstep (se 1 (by rfl) ⟨693773, by rfl⟩ : syracuseStep 925031 = 1387547) B1387547
theorem B81212057 : Blo 614296 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B1558399 : Blo 614296 1558399 := bstep (se 1 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 1558399 = 2337599) B2337599
theorem B1560971 : Blo 614296 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B3596653 : Blo 614296 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B4678235 : Blo 614296 4678235 := bstep (se 1 (by rfl) ⟨3508676, by rfl⟩ : syracuseStep 4678235 = 7017353) B7017353
theorem B617051 : Blo 614296 617051 := bstep (se 1 (by rfl) ⟨462788, by rfl⟩ : syracuseStep 617051 = 925577) B925577
theorem B618111 : Blo 614296 618111 := bstep (se 1 (by rfl) ⟨463583, by rfl⟩ : syracuseStep 618111 = 927167) B927167
theorem B16872947 : Blo 614296 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B10124671 : Blo 614296 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B3118823 : Blo 614296 3118823 := bstep (se 1 (by rfl) ⟨2339117, by rfl⟩ : syracuseStep 3118823 = 4678235) B4678235
theorem B54141371 : Blo 614296 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B11248631 : Blo 614296 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B4795537 : Blo 614296 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B2077865 : Blo 614296 2077865 := bstep (se 2 (by rfl) ⟨779199, by rfl⟩ : syracuseStep 2077865 = 1558399) B1558399
theorem B5920127 : Blo 614296 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B1040647 : Blo 614296 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B616687 : Blo 614296 616687 := bstep (se 1 (by rfl) ⟨462515, by rfl⟩ : syracuseStep 616687 = 925031) B925031
theorem B3110561 : Blo 614296 3110561 := bstep (se 2 (by rfl) ⟨1166460, by rfl⟩ : syracuseStep 3110561 = 2332921) B2332921
theorem B13499561 : Blo 614296 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B6394049 : Blo 614296 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B1385243 : Blo 614296 1385243 := bstep (se 1 (by rfl) ⟨1038932, by rfl⟩ : syracuseStep 1385243 = 2077865) B2077865
theorem B2073707 : Blo 614296 2073707 := bstep (se 1 (by rfl) ⟨1555280, by rfl⟩ : syracuseStep 2073707 = 3110561) B3110561
theorem B1387529 : Blo 614296 1387529 := bstep (se 2 (by rfl) ⟨520323, by rfl⟩ : syracuseStep 1387529 = 1040647) B1040647
theorem B3946751 : Blo 614296 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B2079215 : Blo 614296 2079215 := bstep (se 1 (by rfl) ⟨1559411, by rfl⟩ : syracuseStep 2079215 = 3118823) B3118823
theorem B36094247 : Blo 614296 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B8999707 : Blo 614296 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B7499087 : Blo 614296 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B4262699 : Blo 614296 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B923495 : Blo 614296 923495 := bstep (se 1 (by rfl) ⟨692621, by rfl⟩ : syracuseStep 923495 = 1385243) B1385243
theorem B1382471 : Blo 614296 1382471 := bstep (se 1 (by rfl) ⟨1036853, by rfl⟩ : syracuseStep 1382471 = 2073707) B2073707
theorem B11999609 : Blo 614296 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B925019 : Blo 614296 925019 := bstep (se 1 (by rfl) ⟨693764, by rfl⟩ : syracuseStep 925019 = 1387529) B1387529
theorem B2631167 : Blo 614296 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B1386143 : Blo 614296 1386143 := bstep (se 1 (by rfl) ⟨1039607, by rfl⟩ : syracuseStep 1386143 = 2079215) B2079215
theorem B24062831 : Blo 614296 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B4999391 : Blo 614296 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B921647 : Blo 614296 921647 := bstep (se 1 (by rfl) ⟨691235, by rfl⟩ : syracuseStep 921647 = 1382471) B1382471
theorem B7999739 : Blo 614296 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B924095 : Blo 614296 924095 := bstep (se 1 (by rfl) ⟨693071, by rfl⟩ : syracuseStep 924095 = 1386143) B1386143
theorem B1754111 : Blo 614296 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B16041887 : Blo 614296 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B3332927 : Blo 614296 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B2841799 : Blo 614296 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B615663 : Blo 614296 615663 := bstep (se 1 (by rfl) ⟨461747, by rfl⟩ : syracuseStep 615663 = 923495) B923495
theorem B616679 : Blo 614296 616679 := bstep (se 1 (by rfl) ⟨462509, by rfl⟩ : syracuseStep 616679 = 925019) B925019
theorem B10694591 : Blo 614296 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B3789065 : Blo 614296 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B1169407 : Blo 614296 1169407 := bstep (se 1 (by rfl) ⟨877055, by rfl⟩ : syracuseStep 1169407 = 1754111) B1754111
theorem B614431 : Blo 614296 614431 := bstep (se 1 (by rfl) ⟨460823, by rfl⟩ : syracuseStep 614431 = 921647) B921647
theorem B5333159 : Blo 614296 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B616063 : Blo 614296 616063 := bstep (se 1 (by rfl) ⟨462047, by rfl⟩ : syracuseStep 616063 = 924095) B924095
theorem B2221951 : Blo 614296 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B14221757 : Blo 614296 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B10104173 : Blo 614296 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B2962601 : Blo 614296 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B7129727 : Blo 614296 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B1559209 : Blo 614296 1559209 := bstep (se 2 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 1559209 = 1169407) B1169407
theorem B4753151 : Blo 614296 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B1975067 : Blo 614296 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B37924685 : Blo 614296 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B2078945 : Blo 614296 2078945 := bstep (se 2 (by rfl) ⟨779604, by rfl⟩ : syracuseStep 2078945 = 1559209) B1559209
theorem B6736115 : Blo 614296 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B4490743 : Blo 614296 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B1316711 : Blo 614296 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B1385963 : Blo 614296 1385963 := bstep (se 1 (by rfl) ⟨1039472, by rfl⟩ : syracuseStep 1385963 = 2078945) B2078945
theorem B25283123 : Blo 614296 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B3168767 : Blo 614296 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B923975 : Blo 614296 923975 := bstep (se 1 (by rfl) ⟨692981, by rfl⟩ : syracuseStep 923975 = 1385963) B1385963
theorem B16855415 : Blo 614296 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B5987657 : Blo 614296 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B877807 : Blo 614296 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B8450045 : Blo 614296 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B615983 : Blo 614296 615983 := bstep (se 1 (by rfl) ⟨461987, by rfl⟩ : syracuseStep 615983 = 923975) B923975
theorem B3991771 : Blo 614296 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B4681637 : Blo 614296 4681637 := bstep (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) B877807
theorem B5633363 : Blo 614296 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B11236943 : Blo 614296 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B3121091 : Blo 614296 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B5322361 : Blo 614296 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B3755575 : Blo 614296 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B7491295 : Blo 614296 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B39953573 : Blo 614296 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B2080727 : Blo 614296 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B7096481 : Blo 614296 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B5007433 : Blo 614296 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B1387151 : Blo 614296 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B4730987 : Blo 614296 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B6676577 : Blo 614296 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B26635715 : Blo 614296 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B924767 : Blo 614296 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B3153991 : Blo 614296 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B4451051 : Blo 614296 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B17757143 : Blo 614296 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B11838095 : Blo 614296 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B4205321 : Blo 614296 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B2967367 : Blo 614296 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B616511 : Blo 614296 616511 := bstep (se 1 (by rfl) ⟨462383, by rfl⟩ : syracuseStep 616511 = 924767) B924767
theorem B2803547 : Blo 614296 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B3956489 : Blo 614296 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B7892063 : Blo 614296 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B1869031 : Blo 614296 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B2637659 : Blo 614296 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B5261375 : Blo 614296 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B3507583 : Blo 614296 3507583 := bstep (se 1 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 3507583 = 5261375) B5261375
theorem B2492041 : Blo 614296 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B1758439 : Blo 614296 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B3322721 : Blo 614296 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2344585 : Blo 614296 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B4676777 : Blo 614296 4676777 := bstep (se 2 (by rfl) ⟨1753791, by rfl⟩ : syracuseStep 4676777 = 3507583) B3507583
theorem B3117851 : Blo 614296 3117851 := bstep (se 1 (by rfl) ⟨2338388, by rfl⟩ : syracuseStep 3117851 = 4676777) B4676777
theorem B3126113 : Blo 614296 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B2215147 : Blo 614296 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B2953529 : Blo 614296 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B2078567 : Blo 614296 2078567 := bstep (se 1 (by rfl) ⟨1558925, by rfl⟩ : syracuseStep 2078567 = 3117851) B3117851
theorem B2084075 : Blo 614296 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B1969019 : Blo 614296 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B1385711 : Blo 614296 1385711 := bstep (se 1 (by rfl) ⟨1039283, by rfl⟩ : syracuseStep 1385711 = 2078567) B2078567
theorem B1389383 : Blo 614296 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B1312679 : Blo 614296 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B923807 : Blo 614296 923807 := bstep (se 1 (by rfl) ⟨692855, by rfl⟩ : syracuseStep 923807 = 1385711) B1385711
theorem B926255 : Blo 614296 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B875119 : Blo 614296 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B615871 : Blo 614296 615871 := bstep (se 1 (by rfl) ⟨461903, by rfl⟩ : syracuseStep 615871 = 923807) B923807
theorem B617503 : Blo 614296 617503 := bstep (se 1 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 617503 = 926255) B926255
theorem B1166825 : Blo 614296 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B3111533 : Blo 614296 3111533 := bstep (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) B1166825
theorem B2074355 : Blo 614296 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B1382903 : Blo 614296 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B921935 : Blo 614296 921935 := bstep (se 1 (by rfl) ⟨691451, by rfl⟩ : syracuseStep 921935 = 1382903) B1382903
theorem B614623 : Blo 614296 614623 := bstep (se 1 (by rfl) ⟨460967, by rfl⟩ : syracuseStep 614623 = 921935) B921935

theorem C0 (j : ℕ) (h1 : 153574 ≤ j) (h2 : j ≤ 154273) : Blo 614296 (4 * j + 3) := by
  interval_cases j
  · exact B614299
  · exact B614303
  · exact B614307
  · exact B614311
  · exact B614315
  · exact B614319
  · exact B614323
  · exact B614327
  · exact B614331
  · exact B614335
  · exact B614339
  · exact B614343
  · exact B614347
  · exact B614351
  · exact B614355
  · exact B614359
  · exact B614363
  · exact B614367
  · exact B614371
  · exact B614375
  · exact B614379
  · exact B614383
  · exact B614387
  · exact B614391
  · exact B614395
  · exact B614399
  · exact B614403
  · exact B614407
  · exact B614411
  · exact B614415
  · exact B614419
  · exact B614423
  · exact B614427
  · exact B614431
  · exact B614435
  · exact B614439
  · exact B614443
  · exact B614447
  · exact B614451
  · exact B614455
  · exact B614459
  · exact B614463
  · exact B614467
  · exact B614471
  · exact B614475
  · exact B614479
  · exact B614483
  · exact B614487
  · exact B614491
  · exact B614495
  · exact B614499
  · exact B614503
  · exact B614507
  · exact B614511
  · exact B614515
  · exact B614519
  · exact B614523
  · exact B614527
  · exact B614531
  · exact B614535
  · exact B614539
  · exact B614543
  · exact B614547
  · exact B614551
  · exact B614555
  · exact B614559
  · exact B614563
  · exact B614567
  · exact B614571
  · exact B614575
  · exact B614579
  · exact B614583
  · exact B614587
  · exact B614591
  · exact B614595
  · exact B614599
  · exact B614603
  · exact B614607
  · exact B614611
  · exact B614615
  · exact B614619
  · exact B614623
  · exact B614627
  · exact B614631
  · exact B614635
  · exact B614639
  · exact B614643
  · exact B614647
  · exact B614651
  · exact B614655
  · exact B614659
  · exact B614663
  · exact B614667
  · exact B614671
  · exact B614675
  · exact B614679
  · exact B614683
  · exact B614687
  · exact B614691
  · exact B614695
  · exact B614699
  · exact B614703
  · exact B614707
  · exact B614711
  · exact B614715
  · exact B614719
  · exact B614723
  · exact B614727
  · exact B614731
  · exact B614735
  · exact B614739
  · exact B614743
  · exact B614747
  · exact B614751
  · exact B614755
  · exact B614759
  · exact B614763
  · exact B614767
  · exact B614771
  · exact B614775
  · exact B614779
  · exact B614783
  · exact B614787
  · exact B614791
  · exact B614795
  · exact B614799
  · exact B614803
  · exact B614807
  · exact B614811
  · exact B614815
  · exact B614819
  · exact B614823
  · exact B614827
  · exact B614831
  · exact B614835
  · exact B614839
  · exact B614843
  · exact B614847
  · exact B614851
  · exact B614855
  · exact B614859
  · exact B614863
  · exact B614867
  · exact B614871
  · exact B614875
  · exact B614879
  · exact B614883
  · exact B614887
  · exact B614891
  · exact B614895
  · exact B614899
  · exact B614903
  · exact B614907
  · exact B614911
  · exact B614915
  · exact B614919
  · exact B614923
  · exact B614927
  · exact B614931
  · exact B614935
  · exact B614939
  · exact B614943
  · exact B614947
  · exact B614951
  · exact B614955
  · exact B614959
  · exact B614963
  · exact B614967
  · exact B614971
  · exact B614975
  · exact B614979
  · exact B614983
  · exact B614987
  · exact B614991
  · exact B614995
  · exact B614999
  · exact B615003
  · exact B615007
  · exact B615011
  · exact B615015
  · exact B615019
  · exact B615023
  · exact B615027
  · exact B615031
  · exact B615035
  · exact B615039
  · exact B615043
  · exact B615047
  · exact B615051
  · exact B615055
  · exact B615059
  · exact B615063
  · exact B615067
  · exact B615071
  · exact B615075
  · exact B615079
  · exact B615083
  · exact B615087
  · exact B615091
  · exact B615095
  · exact B615099
  · exact B615103
  · exact B615107
  · exact B615111
  · exact B615115
  · exact B615119
  · exact B615123
  · exact B615127
  · exact B615131
  · exact B615135
  · exact B615139
  · exact B615143
  · exact B615147
  · exact B615151
  · exact B615155
  · exact B615159
  · exact B615163
  · exact B615167
  · exact B615171
  · exact B615175
  · exact B615179
  · exact B615183
  · exact B615187
  · exact B615191
  · exact B615195
  · exact B615199
  · exact B615203
  · exact B615207
  · exact B615211
  · exact B615215
  · exact B615219
  · exact B615223
  · exact B615227
  · exact B615231
  · exact B615235
  · exact B615239
  · exact B615243
  · exact B615247
  · exact B615251
  · exact B615255
  · exact B615259
  · exact B615263
  · exact B615267
  · exact B615271
  · exact B615275
  · exact B615279
  · exact B615283
  · exact B615287
  · exact B615291
  · exact B615295
  · exact B615299
  · exact B615303
  · exact B615307
  · exact B615311
  · exact B615315
  · exact B615319
  · exact B615323
  · exact B615327
  · exact B615331
  · exact B615335
  · exact B615339
  · exact B615343
  · exact B615347
  · exact B615351
  · exact B615355
  · exact B615359
  · exact B615363
  · exact B615367
  · exact B615371
  · exact B615375
  · exact B615379
  · exact B615383
  · exact B615387
  · exact B615391
  · exact B615395
  · exact B615399
  · exact B615403
  · exact B615407
  · exact B615411
  · exact B615415
  · exact B615419
  · exact B615423
  · exact B615427
  · exact B615431
  · exact B615435
  · exact B615439
  · exact B615443
  · exact B615447
  · exact B615451
  · exact B615455
  · exact B615459
  · exact B615463
  · exact B615467
  · exact B615471
  · exact B615475
  · exact B615479
  · exact B615483
  · exact B615487
  · exact B615491
  · exact B615495
  · exact B615499
  · exact B615503
  · exact B615507
  · exact B615511
  · exact B615515
  · exact B615519
  · exact B615523
  · exact B615527
  · exact B615531
  · exact B615535
  · exact B615539
  · exact B615543
  · exact B615547
  · exact B615551
  · exact B615555
  · exact B615559
  · exact B615563
  · exact B615567
  · exact B615571
  · exact B615575
  · exact B615579
  · exact B615583
  · exact B615587
  · exact B615591
  · exact B615595
  · exact B615599
  · exact B615603
  · exact B615607
  · exact B615611
  · exact B615615
  · exact B615619
  · exact B615623
  · exact B615627
  · exact B615631
  · exact B615635
  · exact B615639
  · exact B615643
  · exact B615647
  · exact B615651
  · exact B615655
  · exact B615659
  · exact B615663
  · exact B615667
  · exact B615671
  · exact B615675
  · exact B615679
  · exact B615683
  · exact B615687
  · exact B615691
  · exact B615695
  · exact B615699
  · exact B615703
  · exact B615707
  · exact B615711
  · exact B615715
  · exact B615719
  · exact B615723
  · exact B615727
  · exact B615731
  · exact B615735
  · exact B615739
  · exact B615743
  · exact B615747
  · exact B615751
  · exact B615755
  · exact B615759
  · exact B615763
  · exact B615767
  · exact B615771
  · exact B615775
  · exact B615779
  · exact B615783
  · exact B615787
  · exact B615791
  · exact B615795
  · exact B615799
  · exact B615803
  · exact B615807
  · exact B615811
  · exact B615815
  · exact B615819
  · exact B615823
  · exact B615827
  · exact B615831
  · exact B615835
  · exact B615839
  · exact B615843
  · exact B615847
  · exact B615851
  · exact B615855
  · exact B615859
  · exact B615863
  · exact B615867
  · exact B615871
  · exact B615875
  · exact B615879
  · exact B615883
  · exact B615887
  · exact B615891
  · exact B615895
  · exact B615899
  · exact B615903
  · exact B615907
  · exact B615911
  · exact B615915
  · exact B615919
  · exact B615923
  · exact B615927
  · exact B615931
  · exact B615935
  · exact B615939
  · exact B615943
  · exact B615947
  · exact B615951
  · exact B615955
  · exact B615959
  · exact B615963
  · exact B615967
  · exact B615971
  · exact B615975
  · exact B615979
  · exact B615983
  · exact B615987
  · exact B615991
  · exact B615995
  · exact B615999
  · exact B616003
  · exact B616007
  · exact B616011
  · exact B616015
  · exact B616019
  · exact B616023
  · exact B616027
  · exact B616031
  · exact B616035
  · exact B616039
  · exact B616043
  · exact B616047
  · exact B616051
  · exact B616055
  · exact B616059
  · exact B616063
  · exact B616067
  · exact B616071
  · exact B616075
  · exact B616079
  · exact B616083
  · exact B616087
  · exact B616091
  · exact B616095
  · exact B616099
  · exact B616103
  · exact B616107
  · exact B616111
  · exact B616115
  · exact B616119
  · exact B616123
  · exact B616127
  · exact B616131
  · exact B616135
  · exact B616139
  · exact B616143
  · exact B616147
  · exact B616151
  · exact B616155
  · exact B616159
  · exact B616163
  · exact B616167
  · exact B616171
  · exact B616175
  · exact B616179
  · exact B616183
  · exact B616187
  · exact B616191
  · exact B616195
  · exact B616199
  · exact B616203
  · exact B616207
  · exact B616211
  · exact B616215
  · exact B616219
  · exact B616223
  · exact B616227
  · exact B616231
  · exact B616235
  · exact B616239
  · exact B616243
  · exact B616247
  · exact B616251
  · exact B616255
  · exact B616259
  · exact B616263
  · exact B616267
  · exact B616271
  · exact B616275
  · exact B616279
  · exact B616283
  · exact B616287
  · exact B616291
  · exact B616295
  · exact B616299
  · exact B616303
  · exact B616307
  · exact B616311
  · exact B616315
  · exact B616319
  · exact B616323
  · exact B616327
  · exact B616331
  · exact B616335
  · exact B616339
  · exact B616343
  · exact B616347
  · exact B616351
  · exact B616355
  · exact B616359
  · exact B616363
  · exact B616367
  · exact B616371
  · exact B616375
  · exact B616379
  · exact B616383
  · exact B616387
  · exact B616391
  · exact B616395
  · exact B616399
  · exact B616403
  · exact B616407
  · exact B616411
  · exact B616415
  · exact B616419
  · exact B616423
  · exact B616427
  · exact B616431
  · exact B616435
  · exact B616439
  · exact B616443
  · exact B616447
  · exact B616451
  · exact B616455
  · exact B616459
  · exact B616463
  · exact B616467
  · exact B616471
  · exact B616475
  · exact B616479
  · exact B616483
  · exact B616487
  · exact B616491
  · exact B616495
  · exact B616499
  · exact B616503
  · exact B616507
  · exact B616511
  · exact B616515
  · exact B616519
  · exact B616523
  · exact B616527
  · exact B616531
  · exact B616535
  · exact B616539
  · exact B616543
  · exact B616547
  · exact B616551
  · exact B616555
  · exact B616559
  · exact B616563
  · exact B616567
  · exact B616571
  · exact B616575
  · exact B616579
  · exact B616583
  · exact B616587
  · exact B616591
  · exact B616595
  · exact B616599
  · exact B616603
  · exact B616607
  · exact B616611
  · exact B616615
  · exact B616619
  · exact B616623
  · exact B616627
  · exact B616631
  · exact B616635
  · exact B616639
  · exact B616643
  · exact B616647
  · exact B616651
  · exact B616655
  · exact B616659
  · exact B616663
  · exact B616667
  · exact B616671
  · exact B616675
  · exact B616679
  · exact B616683
  · exact B616687
  · exact B616691
  · exact B616695
  · exact B616699
  · exact B616703
  · exact B616707
  · exact B616711
  · exact B616715
  · exact B616719
  · exact B616723
  · exact B616727
  · exact B616731
  · exact B616735
  · exact B616739
  · exact B616743
  · exact B616747
  · exact B616751
  · exact B616755
  · exact B616759
  · exact B616763
  · exact B616767
  · exact B616771
  · exact B616775
  · exact B616779
  · exact B616783
  · exact B616787
  · exact B616791
  · exact B616795
  · exact B616799
  · exact B616803
  · exact B616807
  · exact B616811
  · exact B616815
  · exact B616819
  · exact B616823
  · exact B616827
  · exact B616831
  · exact B616835
  · exact B616839
  · exact B616843
  · exact B616847
  · exact B616851
  · exact B616855
  · exact B616859
  · exact B616863
  · exact B616867
  · exact B616871
  · exact B616875
  · exact B616879
  · exact B616883
  · exact B616887
  · exact B616891
  · exact B616895
  · exact B616899
  · exact B616903
  · exact B616907
  · exact B616911
  · exact B616915
  · exact B616919
  · exact B616923
  · exact B616927
  · exact B616931
  · exact B616935
  · exact B616939
  · exact B616943
  · exact B616947
  · exact B616951
  · exact B616955
  · exact B616959
  · exact B616963
  · exact B616967
  · exact B616971
  · exact B616975
  · exact B616979
  · exact B616983
  · exact B616987
  · exact B616991
  · exact B616995
  · exact B616999
  · exact B617003
  · exact B617007
  · exact B617011
  · exact B617015
  · exact B617019
  · exact B617023
  · exact B617027
  · exact B617031
  · exact B617035
  · exact B617039
  · exact B617043
  · exact B617047
  · exact B617051
  · exact B617055
  · exact B617059
  · exact B617063
  · exact B617067
  · exact B617071
  · exact B617075
  · exact B617079
  · exact B617083
  · exact B617087
  · exact B617091
  · exact B617095

theorem C1 (j : ℕ) (h1 : 154274 ≤ j) (h2 : j ≤ 154573) : Blo 614296 (4 * j + 3) := by
  interval_cases j
  · exact B617099
  · exact B617103
  · exact B617107
  · exact B617111
  · exact B617115
  · exact B617119
  · exact B617123
  · exact B617127
  · exact B617131
  · exact B617135
  · exact B617139
  · exact B617143
  · exact B617147
  · exact B617151
  · exact B617155
  · exact B617159
  · exact B617163
  · exact B617167
  · exact B617171
  · exact B617175
  · exact B617179
  · exact B617183
  · exact B617187
  · exact B617191
  · exact B617195
  · exact B617199
  · exact B617203
  · exact B617207
  · exact B617211
  · exact B617215
  · exact B617219
  · exact B617223
  · exact B617227
  · exact B617231
  · exact B617235
  · exact B617239
  · exact B617243
  · exact B617247
  · exact B617251
  · exact B617255
  · exact B617259
  · exact B617263
  · exact B617267
  · exact B617271
  · exact B617275
  · exact B617279
  · exact B617283
  · exact B617287
  · exact B617291
  · exact B617295
  · exact B617299
  · exact B617303
  · exact B617307
  · exact B617311
  · exact B617315
  · exact B617319
  · exact B617323
  · exact B617327
  · exact B617331
  · exact B617335
  · exact B617339
  · exact B617343
  · exact B617347
  · exact B617351
  · exact B617355
  · exact B617359
  · exact B617363
  · exact B617367
  · exact B617371
  · exact B617375
  · exact B617379
  · exact B617383
  · exact B617387
  · exact B617391
  · exact B617395
  · exact B617399
  · exact B617403
  · exact B617407
  · exact B617411
  · exact B617415
  · exact B617419
  · exact B617423
  · exact B617427
  · exact B617431
  · exact B617435
  · exact B617439
  · exact B617443
  · exact B617447
  · exact B617451
  · exact B617455
  · exact B617459
  · exact B617463
  · exact B617467
  · exact B617471
  · exact B617475
  · exact B617479
  · exact B617483
  · exact B617487
  · exact B617491
  · exact B617495
  · exact B617499
  · exact B617503
  · exact B617507
  · exact B617511
  · exact B617515
  · exact B617519
  · exact B617523
  · exact B617527
  · exact B617531
  · exact B617535
  · exact B617539
  · exact B617543
  · exact B617547
  · exact B617551
  · exact B617555
  · exact B617559
  · exact B617563
  · exact B617567
  · exact B617571
  · exact B617575
  · exact B617579
  · exact B617583
  · exact B617587
  · exact B617591
  · exact B617595
  · exact B617599
  · exact B617603
  · exact B617607
  · exact B617611
  · exact B617615
  · exact B617619
  · exact B617623
  · exact B617627
  · exact B617631
  · exact B617635
  · exact B617639
  · exact B617643
  · exact B617647
  · exact B617651
  · exact B617655
  · exact B617659
  · exact B617663
  · exact B617667
  · exact B617671
  · exact B617675
  · exact B617679
  · exact B617683
  · exact B617687
  · exact B617691
  · exact B617695
  · exact B617699
  · exact B617703
  · exact B617707
  · exact B617711
  · exact B617715
  · exact B617719
  · exact B617723
  · exact B617727
  · exact B617731
  · exact B617735
  · exact B617739
  · exact B617743
  · exact B617747
  · exact B617751
  · exact B617755
  · exact B617759
  · exact B617763
  · exact B617767
  · exact B617771
  · exact B617775
  · exact B617779
  · exact B617783
  · exact B617787
  · exact B617791
  · exact B617795
  · exact B617799
  · exact B617803
  · exact B617807
  · exact B617811
  · exact B617815
  · exact B617819
  · exact B617823
  · exact B617827
  · exact B617831
  · exact B617835
  · exact B617839
  · exact B617843
  · exact B617847
  · exact B617851
  · exact B617855
  · exact B617859
  · exact B617863
  · exact B617867
  · exact B617871
  · exact B617875
  · exact B617879
  · exact B617883
  · exact B617887
  · exact B617891
  · exact B617895
  · exact B617899
  · exact B617903
  · exact B617907
  · exact B617911
  · exact B617915
  · exact B617919
  · exact B617923
  · exact B617927
  · exact B617931
  · exact B617935
  · exact B617939
  · exact B617943
  · exact B617947
  · exact B617951
  · exact B617955
  · exact B617959
  · exact B617963
  · exact B617967
  · exact B617971
  · exact B617975
  · exact B617979
  · exact B617983
  · exact B617987
  · exact B617991
  · exact B617995
  · exact B617999
  · exact B618003
  · exact B618007
  · exact B618011
  · exact B618015
  · exact B618019
  · exact B618023
  · exact B618027
  · exact B618031
  · exact B618035
  · exact B618039
  · exact B618043
  · exact B618047
  · exact B618051
  · exact B618055
  · exact B618059
  · exact B618063
  · exact B618067
  · exact B618071
  · exact B618075
  · exact B618079
  · exact B618083
  · exact B618087
  · exact B618091
  · exact B618095
  · exact B618099
  · exact B618103
  · exact B618107
  · exact B618111
  · exact B618115
  · exact B618119
  · exact B618123
  · exact B618127
  · exact B618131
  · exact B618135
  · exact B618139
  · exact B618143
  · exact B618147
  · exact B618151
  · exact B618155
  · exact B618159
  · exact B618163
  · exact B618167
  · exact B618171
  · exact B618175
  · exact B618179
  · exact B618183
  · exact B618187
  · exact B618191
  · exact B618195
  · exact B618199
  · exact B618203
  · exact B618207
  · exact B618211
  · exact B618215
  · exact B618219
  · exact B618223
  · exact B618227
  · exact B618231
  · exact B618235
  · exact B618239
  · exact B618243
  · exact B618247
  · exact B618251
  · exact B618255
  · exact B618259
  · exact B618263
  · exact B618267
  · exact B618271
  · exact B618275
  · exact B618279
  · exact B618283
  · exact B618287
  · exact B618291
  · exact B618295

theorem solution (m : ℕ) (hlo : 614296 ≤ m) (hhi : m ≤ 618296) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 153574 ≤ j := by omega
    have hj2 : j ≤ 154573 := by omega
    have hb : Blo 614296 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 154274 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
