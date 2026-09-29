-- Prove2me | solution 1 for syracuse_descends_range_1413526_1415526
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:13.46616+00:00
-- url     : https://prove2.me/submissions/9816c524-7d8b-4562-8292-b0c89b2db1f0

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


theorem B2121749 : Blo 1413526 2121749 := bbase (se 6 (by rfl) ⟨49728, by rfl⟩ : syracuseStep 2121749 = 99457) (by norm_num)
theorem B2547757 : Blo 1413526 2547757 := bbase (se 3 (by rfl) ⟨477704, by rfl⟩ : syracuseStep 2547757 = 955409) (by norm_num)
theorem B2121773 : Blo 1413526 2121773 := bbase (se 3 (by rfl) ⟨397832, by rfl⟩ : syracuseStep 2121773 = 795665) (by norm_num)
theorem B8601653 : Blo 1413526 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B2121797 : Blo 1413526 2121797 := bbase (se 4 (by rfl) ⟨198918, by rfl⟩ : syracuseStep 2121797 = 397837) (by norm_num)
theorem B1433681 : Blo 1413526 1433681 := bbase (se 2 (by rfl) ⟨537630, by rfl⟩ : syracuseStep 1433681 = 1075261) (by norm_num)
theorem B3579997 : Blo 1413526 3579997 := bbase (se 3 (by rfl) ⟨671249, by rfl⟩ : syracuseStep 3579997 = 1342499) (by norm_num)
theorem B2121821 : Blo 1413526 2121821 := bbase (se 3 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 2121821 = 795683) (by norm_num)
theorem B2121845 : Blo 1413526 2121845 := bbase (se 5 (by rfl) ⟨99461, by rfl⟩ : syracuseStep 2121845 = 198923) (by norm_num)
theorem B2121869 : Blo 1413526 2121869 := bbase (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) (by norm_num)
theorem B2015389 : Blo 1413526 2015389 := bbase (se 3 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 2015389 = 755771) (by norm_num)
theorem B2121893 : Blo 1413526 2121893 := bbase (se 4 (by rfl) ⟨198927, by rfl⟩ : syracuseStep 2121893 = 397855) (by norm_num)
theorem B2121917 : Blo 1413526 2121917 := bbase (se 3 (by rfl) ⟨397859, by rfl⟩ : syracuseStep 2121917 = 795719) (by norm_num)
theorem B3580109 : Blo 1413526 3580109 := bbase (se 3 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 3580109 = 1342541) (by norm_num)
theorem B2121941 : Blo 1413526 2121941 := bbase (se 7 (by rfl) ⟨24866, by rfl⟩ : syracuseStep 2121941 = 49733) (by norm_num)
theorem B1745129 : Blo 1413526 1745129 := bbase (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) (by norm_num)
theorem B2121965 : Blo 1413526 2121965 := bbase (se 3 (by rfl) ⟨397868, by rfl⟩ : syracuseStep 2121965 = 795737) (by norm_num)
theorem B2121989 : Blo 1413526 2121989 := bbase (se 4 (by rfl) ⟨198936, by rfl⟩ : syracuseStep 2121989 = 397873) (by norm_num)
theorem B2122013 : Blo 1413526 2122013 := bbase (se 3 (by rfl) ⟨397877, by rfl⟩ : syracuseStep 2122013 = 795755) (by norm_num)
theorem B4301093 : Blo 1413526 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B2687269 : Blo 1413526 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B1433909 : Blo 1413526 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B2122037 : Blo 1413526 2122037 := bbase (se 5 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 2122037 = 198941) (by norm_num)
theorem B4776245 : Blo 1413526 4776245 := bbase (se 5 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 4776245 = 447773) (by norm_num)
theorem B2122061 : Blo 1413526 2122061 := bbase (se 3 (by rfl) ⟨397886, by rfl⟩ : syracuseStep 2122061 = 795773) (by norm_num)
theorem B2122085 : Blo 1413526 2122085 := bbase (se 4 (by rfl) ⟨198945, by rfl⟩ : syracuseStep 2122085 = 397891) (by norm_num)
theorem B5374309 : Blo 1413526 5374309 := bbase (se 4 (by rfl) ⟨503841, by rfl⟩ : syracuseStep 5374309 = 1007683) (by norm_num)
theorem B2122109 : Blo 1413526 2122109 := bbase (se 3 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 2122109 = 795791) (by norm_num)
theorem B3580301 : Blo 1413526 3580301 := bbase (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) (by norm_num)
theorem B2122133 : Blo 1413526 2122133 := bbase (se 6 (by rfl) ⟨49737, by rfl⟩ : syracuseStep 2122133 = 99475) (by norm_num)
theorem B3400085 : Blo 1413526 3400085 := bbase (se 6 (by rfl) ⟨79689, by rfl⟩ : syracuseStep 3400085 = 159379) (by norm_num)
theorem B2122157 : Blo 1413526 2122157 := bbase (se 3 (by rfl) ⟨397904, by rfl⟩ : syracuseStep 2122157 = 795809) (by norm_num)
theorem B2122181 : Blo 1413526 2122181 := bbase (se 4 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 2122181 = 397909) (by norm_num)
theorem B2122205 : Blo 1413526 2122205 := bbase (se 3 (by rfl) ⟨397913, by rfl⟩ : syracuseStep 2122205 = 795827) (by norm_num)
theorem B2122229 : Blo 1413526 2122229 := bbase (se 5 (by rfl) ⟨99479, by rfl⟩ : syracuseStep 2122229 = 198959) (by norm_num)
theorem B2122253 : Blo 1413526 2122253 := bbase (se 3 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 2122253 = 795845) (by norm_num)
theorem B2122277 : Blo 1413526 2122277 := bbase (se 4 (by rfl) ⟨198963, by rfl⟩ : syracuseStep 2122277 = 397927) (by norm_num)
theorem B2548277 : Blo 1413526 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B2122301 : Blo 1413526 2122301 := bbase (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) (by norm_num)
theorem B2122325 : Blo 1413526 2122325 := bbase (se 8 (by rfl) ⟨12435, by rfl⟩ : syracuseStep 2122325 = 24871) (by norm_num)
theorem B2122349 : Blo 1413526 2122349 := bbase (se 3 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 2122349 = 795881) (by norm_num)
theorem B6128245 : Blo 1413526 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B2122373 : Blo 1413526 2122373 := bbase (se 4 (by rfl) ⟨198972, by rfl⟩ : syracuseStep 2122373 = 397945) (by norm_num)
theorem B2122397 : Blo 1413526 2122397 := bbase (se 3 (by rfl) ⟨397949, by rfl⟩ : syracuseStep 2122397 = 795899) (by norm_num)
theorem B2122421 : Blo 1413526 2122421 := bbase (se 5 (by rfl) ⟨99488, by rfl⟩ : syracuseStep 2122421 = 198977) (by norm_num)
theorem B2122445 : Blo 1413526 2122445 := bbase (se 3 (by rfl) ⟨397958, by rfl⟩ : syracuseStep 2122445 = 795917) (by norm_num)
theorem B3580645 : Blo 1413526 3580645 := bbase (se 4 (by rfl) ⟨335685, by rfl⟩ : syracuseStep 3580645 = 671371) (by norm_num)
theorem B2122469 : Blo 1413526 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B4776677 : Blo 1413526 4776677 := bbase (se 4 (by rfl) ⟨447813, by rfl⟩ : syracuseStep 4776677 = 895627) (by norm_num)
theorem B2122493 : Blo 1413526 2122493 := bbase (se 3 (by rfl) ⟨397967, by rfl⟩ : syracuseStep 2122493 = 795935) (by norm_num)
theorem B2122517 : Blo 1413526 2122517 := bbase (se 6 (by rfl) ⟨49746, by rfl⟩ : syracuseStep 2122517 = 99493) (by norm_num)
theorem B2122541 : Blo 1413526 2122541 := bbase (se 3 (by rfl) ⟨397976, by rfl⟩ : syracuseStep 2122541 = 795953) (by norm_num)
theorem B2122565 : Blo 1413526 2122565 := bbase (se 4 (by rfl) ⟨198990, by rfl⟩ : syracuseStep 2122565 = 397981) (by norm_num)
theorem B6128453 : Blo 1413526 6128453 := bbase (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) (by norm_num)
theorem B3269453 : Blo 1413526 3269453 := bbase (se 3 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 3269453 = 1226045) (by norm_num)
theorem B3580757 : Blo 1413526 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B2122589 : Blo 1413526 2122589 := bbase (se 3 (by rfl) ⟨397985, by rfl⟩ : syracuseStep 2122589 = 795971) (by norm_num)
theorem B2122613 : Blo 1413526 2122613 := bbase (se 5 (by rfl) ⟨99497, by rfl⟩ : syracuseStep 2122613 = 198995) (by norm_num)
theorem B1434505 : Blo 1413526 1434505 := bbase (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) (by norm_num)
theorem B2122637 : Blo 1413526 2122637 := bbase (se 3 (by rfl) ⟨397994, by rfl⟩ : syracuseStep 2122637 = 795989) (by norm_num)
theorem B2122661 : Blo 1413526 2122661 := bbase (se 4 (by rfl) ⟨198999, by rfl⟩ : syracuseStep 2122661 = 397999) (by norm_num)
theorem B2122685 : Blo 1413526 2122685 := bbase (se 3 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 2122685 = 796007) (by norm_num)
theorem B2122709 : Blo 1413526 2122709 := bbase (se 7 (by rfl) ⟨24875, by rfl⟩ : syracuseStep 2122709 = 49751) (by norm_num)
theorem B1590241 : Blo 1413526 1590241 := bbase (se 2 (by rfl) ⟨596340, by rfl⟩ : syracuseStep 1590241 = 1192681) (by norm_num)
theorem B2122733 : Blo 1413526 2122733 := bbase (se 3 (by rfl) ⟨398012, by rfl⟩ : syracuseStep 2122733 = 796025) (by norm_num)
theorem B1590277 : Blo 1413526 1590277 := bbase (se 4 (by rfl) ⟨149088, by rfl⟩ : syracuseStep 1590277 = 298177) (by norm_num)
theorem B2122757 : Blo 1413526 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B3580949 : Blo 1413526 3580949 := bbase (se 6 (by rfl) ⟨83928, by rfl⟩ : syracuseStep 3580949 = 167857) (by norm_num)
theorem B2122781 : Blo 1413526 2122781 := bbase (se 3 (by rfl) ⟨398021, by rfl⟩ : syracuseStep 2122781 = 796043) (by norm_num)
theorem B1590313 : Blo 1413526 1590313 := bbase (se 2 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 1590313 = 1192735) (by norm_num)
theorem B7160885 : Blo 1413526 7160885 := bbase (se 5 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 7160885 = 671333) (by norm_num)
theorem B2122805 : Blo 1413526 2122805 := bbase (se 5 (by rfl) ⟨99506, by rfl⟩ : syracuseStep 2122805 = 199013) (by norm_num)
theorem B1721417 : Blo 1413526 1721417 := bbase (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) (by norm_num)
theorem B1590349 : Blo 1413526 1590349 := bbase (se 3 (by rfl) ⟨298190, by rfl⟩ : syracuseStep 1590349 = 596381) (by norm_num)
theorem B2122829 : Blo 1413526 2122829 := bbase (se 3 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 2122829 = 796061) (by norm_num)
theorem B2122853 : Blo 1413526 2122853 := bbase (se 4 (by rfl) ⟨199017, by rfl⟩ : syracuseStep 2122853 = 398035) (by norm_num)
theorem B1590385 : Blo 1413526 1590385 := bbase (se 2 (by rfl) ⟨596394, by rfl⟩ : syracuseStep 1590385 = 1192789) (by norm_num)
theorem B2122877 : Blo 1413526 2122877 := bbase (se 3 (by rfl) ⟨398039, by rfl⟩ : syracuseStep 2122877 = 796079) (by norm_num)
theorem B1590421 : Blo 1413526 1590421 := bbase (se 6 (by rfl) ⟨37275, by rfl⟩ : syracuseStep 1590421 = 74551) (by norm_num)
theorem B2122901 : Blo 1413526 2122901 := bbase (se 6 (by rfl) ⟨49755, by rfl⟩ : syracuseStep 2122901 = 99511) (by norm_num)
theorem B4777109 : Blo 1413526 4777109 := bbase (se 6 (by rfl) ⟨111963, by rfl⟩ : syracuseStep 4777109 = 223927) (by norm_num)
theorem B2122925 : Blo 1413526 2122925 := bbase (se 3 (by rfl) ⟨398048, by rfl⟩ : syracuseStep 2122925 = 796097) (by norm_num)
theorem B1590457 : Blo 1413526 1590457 := bbase (se 2 (by rfl) ⟨596421, by rfl⟩ : syracuseStep 1590457 = 1192843) (by norm_num)
theorem B2122949 : Blo 1413526 2122949 := bbase (se 4 (by rfl) ⟨199026, by rfl⟩ : syracuseStep 2122949 = 398053) (by norm_num)
theorem B1590493 : Blo 1413526 1590493 := bbase (se 3 (by rfl) ⟨298217, by rfl⟩ : syracuseStep 1590493 = 596435) (by norm_num)
theorem B2122973 : Blo 1413526 2122973 := bbase (se 3 (by rfl) ⟨398057, by rfl⟩ : syracuseStep 2122973 = 796115) (by norm_num)
theorem B2122997 : Blo 1413526 2122997 := bbase (se 5 (by rfl) ⟨99515, by rfl⟩ : syracuseStep 2122997 = 199031) (by norm_num)
theorem B1590529 : Blo 1413526 1590529 := bbase (se 2 (by rfl) ⟨596448, by rfl⟩ : syracuseStep 1590529 = 1192897) (by norm_num)
theorem B2123021 : Blo 1413526 2123021 := bbase (se 3 (by rfl) ⟨398066, by rfl⟩ : syracuseStep 2123021 = 796133) (by norm_num)
theorem B1590565 : Blo 1413526 1590565 := bbase (se 4 (by rfl) ⟨149115, by rfl⟩ : syracuseStep 1590565 = 298231) (by norm_num)
theorem B2123045 : Blo 1413526 2123045 := bbase (se 4 (by rfl) ⟨199035, by rfl⟩ : syracuseStep 2123045 = 398071) (by norm_num)
theorem B2123069 : Blo 1413526 2123069 := bbase (se 3 (by rfl) ⟨398075, by rfl⟩ : syracuseStep 2123069 = 796151) (by norm_num)
theorem B1590601 : Blo 1413526 1590601 := bbase (se 2 (by rfl) ⟨596475, by rfl⟩ : syracuseStep 1590601 = 1192951) (by norm_num)
theorem B2123093 : Blo 1413526 2123093 := bbase (se 12 (by rfl) ⟨777, by rfl⟩ : syracuseStep 2123093 = 1555) (by norm_num)
theorem B1590637 : Blo 1413526 1590637 := bbase (se 3 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 1590637 = 596489) (by norm_num)
theorem B3581293 : Blo 1413526 3581293 := bbase (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) (by norm_num)
theorem B2123117 : Blo 1413526 2123117 := bbase (se 3 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 2123117 = 796169) (by norm_num)
theorem B2123141 : Blo 1413526 2123141 := bbase (se 4 (by rfl) ⟨199044, by rfl⟩ : syracuseStep 2123141 = 398089) (by norm_num)
theorem B1590673 : Blo 1413526 1590673 := bbase (se 2 (by rfl) ⟨596502, by rfl⟩ : syracuseStep 1590673 = 1193005) (by norm_num)
theorem B2123165 : Blo 1413526 2123165 := bbase (se 3 (by rfl) ⟨398093, by rfl⟩ : syracuseStep 2123165 = 796187) (by norm_num)
theorem B2418101 : Blo 1413526 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B1590709 : Blo 1413526 1590709 := bbase (se 5 (by rfl) ⟨74564, by rfl⟩ : syracuseStep 1590709 = 149129) (by norm_num)
theorem B2123189 : Blo 1413526 2123189 := bbase (se 5 (by rfl) ⟨99524, by rfl⟩ : syracuseStep 2123189 = 199049) (by norm_num)
theorem B2123213 : Blo 1413526 2123213 := bbase (se 3 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 2123213 = 796205) (by norm_num)
theorem B1590745 : Blo 1413526 1590745 := bbase (se 2 (by rfl) ⟨596529, by rfl⟩ : syracuseStep 1590745 = 1193059) (by norm_num)
theorem B3581405 : Blo 1413526 3581405 := bbase (se 3 (by rfl) ⟨671513, by rfl⟩ : syracuseStep 3581405 = 1343027) (by norm_num)
theorem B2123237 : Blo 1413526 2123237 := bbase (se 4 (by rfl) ⟨199053, by rfl⟩ : syracuseStep 2123237 = 398107) (by norm_num)
theorem B2385389 : Blo 1413526 2385389 := bbase (se 3 (by rfl) ⟨447260, by rfl⟩ : syracuseStep 2385389 = 894521) (by norm_num)
theorem B1590781 : Blo 1413526 1590781 := bbase (se 3 (by rfl) ⟨298271, by rfl⟩ : syracuseStep 1590781 = 596543) (by norm_num)
theorem B2123261 : Blo 1413526 2123261 := bbase (se 3 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 2123261 = 796223) (by norm_num)
theorem B2123285 : Blo 1413526 2123285 := bbase (se 6 (by rfl) ⟨49764, by rfl⟩ : syracuseStep 2123285 = 99529) (by norm_num)
theorem B1590817 : Blo 1413526 1590817 := bbase (se 2 (by rfl) ⟨596556, by rfl⟩ : syracuseStep 1590817 = 1193113) (by norm_num)
theorem B1590853 : Blo 1413526 1590853 := bbase (se 4 (by rfl) ⟨149142, by rfl⟩ : syracuseStep 1590853 = 298285) (by norm_num)
theorem B1590889 : Blo 1413526 1590889 := bbase (se 2 (by rfl) ⟨596583, by rfl⟩ : syracuseStep 1590889 = 1193167) (by norm_num)
theorem B2385517 : Blo 1413526 2385517 := bbase (se 3 (by rfl) ⟨447284, by rfl⟩ : syracuseStep 2385517 = 894569) (by norm_num)
theorem B1590925 : Blo 1413526 1590925 := bbase (se 3 (by rfl) ⟨298298, by rfl⟩ : syracuseStep 1590925 = 596597) (by norm_num)
theorem B3581597 : Blo 1413526 3581597 := bbase (se 3 (by rfl) ⟨671549, by rfl⟩ : syracuseStep 3581597 = 1343099) (by norm_num)
theorem B1590961 : Blo 1413526 1590961 := bbase (se 2 (by rfl) ⟨596610, by rfl⟩ : syracuseStep 1590961 = 1193221) (by norm_num)
theorem B2385605 : Blo 1413526 2385605 := bbase (se 4 (by rfl) ⟨223650, by rfl⟩ : syracuseStep 2385605 = 447301) (by norm_num)
theorem B4531909 : Blo 1413526 4531909 := bbase (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) (by norm_num)
theorem B1590997 : Blo 1413526 1590997 := bbase (se 7 (by rfl) ⟨18644, by rfl⟩ : syracuseStep 1590997 = 37289) (by norm_num)
theorem B1591033 : Blo 1413526 1591033 := bbase (se 2 (by rfl) ⟨596637, by rfl⟩ : syracuseStep 1591033 = 1193275) (by norm_num)
theorem B1591069 : Blo 1413526 1591069 := bbase (se 3 (by rfl) ⟨298325, by rfl⟩ : syracuseStep 1591069 = 596651) (by norm_num)
theorem B1591105 : Blo 1413526 1591105 := bbase (se 2 (by rfl) ⟨596664, by rfl⟩ : syracuseStep 1591105 = 1193329) (by norm_num)
theorem B2385733 : Blo 1413526 2385733 := bbase (se 4 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 2385733 = 447325) (by norm_num)
theorem B1591141 : Blo 1413526 1591141 := bbase (se 4 (by rfl) ⟨149169, by rfl⟩ : syracuseStep 1591141 = 298339) (by norm_num)
theorem B1591177 : Blo 1413526 1591177 := bbase (se 2 (by rfl) ⟨596691, by rfl⟩ : syracuseStep 1591177 = 1193383) (by norm_num)
theorem B3180437 : Blo 1413526 3180437 := bbase (se 6 (by rfl) ⟨74541, by rfl⟩ : syracuseStep 3180437 = 149083) (by norm_num)
theorem B2385821 : Blo 1413526 2385821 := bbase (se 3 (by rfl) ⟨447341, by rfl⟩ : syracuseStep 2385821 = 894683) (by norm_num)
theorem B1591213 : Blo 1413526 1591213 := bbase (se 3 (by rfl) ⟨298352, by rfl⟩ : syracuseStep 1591213 = 596705) (by norm_num)
theorem B1591249 : Blo 1413526 1591249 := bbase (se 2 (by rfl) ⟨596718, by rfl⟩ : syracuseStep 1591249 = 1193437) (by norm_num)
theorem B3180509 : Blo 1413526 3180509 := bbase (se 3 (by rfl) ⟨596345, by rfl⟩ : syracuseStep 3180509 = 1192691) (by norm_num)
theorem B1591285 : Blo 1413526 1591285 := bbase (se 5 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 1591285 = 149183) (by norm_num)
theorem B3581941 : Blo 1413526 3581941 := bbase (se 5 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 3581941 = 335807) (by norm_num)
theorem B1591321 : Blo 1413526 1591321 := bbase (se 2 (by rfl) ⟨596745, by rfl⟩ : syracuseStep 1591321 = 1193491) (by norm_num)
theorem B2385949 : Blo 1413526 2385949 := bbase (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) (by norm_num)
theorem B3180581 : Blo 1413526 3180581 := bbase (se 4 (by rfl) ⟨298179, by rfl⟩ : syracuseStep 3180581 = 596359) (by norm_num)
theorem B1591357 : Blo 1413526 1591357 := bbase (se 3 (by rfl) ⟨298379, by rfl⟩ : syracuseStep 1591357 = 596759) (by norm_num)
theorem B2484317 : Blo 1413526 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B1591393 : Blo 1413526 1591393 := bbase (se 2 (by rfl) ⟨596772, by rfl⟩ : syracuseStep 1591393 = 1193545) (by norm_num)
theorem B3582053 : Blo 1413526 3582053 := bbase (se 4 (by rfl) ⟨335817, by rfl⟩ : syracuseStep 3582053 = 671635) (by norm_num)
theorem B3180653 : Blo 1413526 3180653 := bbase (se 3 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 3180653 = 1192745) (by norm_num)
theorem B2386037 : Blo 1413526 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B2721925 : Blo 1413526 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B1591429 : Blo 1413526 1591429 := bbase (se 4 (by rfl) ⟨149196, by rfl⟩ : syracuseStep 1591429 = 298393) (by norm_num)
theorem B1591465 : Blo 1413526 1591465 := bbase (se 2 (by rfl) ⟨596799, by rfl⟩ : syracuseStep 1591465 = 1193599) (by norm_num)
theorem B3180725 : Blo 1413526 3180725 := bbase (se 5 (by rfl) ⟨149096, by rfl⟩ : syracuseStep 3180725 = 298193) (by norm_num)
theorem B1591501 : Blo 1413526 1591501 := bbase (se 3 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 1591501 = 596813) (by norm_num)
theorem B1591537 : Blo 1413526 1591537 := bbase (se 2 (by rfl) ⟨596826, by rfl⟩ : syracuseStep 1591537 = 1193653) (by norm_num)
theorem B2386165 : Blo 1413526 2386165 := bbase (se 5 (by rfl) ⟨111851, by rfl⟩ : syracuseStep 2386165 = 223703) (by norm_num)
theorem B3180797 : Blo 1413526 3180797 := bbase (se 3 (by rfl) ⟨596399, by rfl⟩ : syracuseStep 3180797 = 1192799) (by norm_num)
theorem B1591573 : Blo 1413526 1591573 := bbase (se 6 (by rfl) ⟨37302, by rfl⟩ : syracuseStep 1591573 = 74605) (by norm_num)
theorem B3582245 : Blo 1413526 3582245 := bbase (se 4 (by rfl) ⟨335835, by rfl⟩ : syracuseStep 3582245 = 671671) (by norm_num)
theorem B1591609 : Blo 1413526 1591609 := bbase (se 2 (by rfl) ⟨596853, by rfl⟩ : syracuseStep 1591609 = 1193707) (by norm_num)
theorem B3180869 : Blo 1413526 3180869 := bbase (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) (by norm_num)
theorem B6793541 : Blo 1413526 6793541 := bbase (se 4 (by rfl) ⟨636894, by rfl⟩ : syracuseStep 6793541 = 1273789) (by norm_num)
theorem B7162181 : Blo 1413526 7162181 := bbase (se 4 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 7162181 = 1342909) (by norm_num)
theorem B2386253 : Blo 1413526 2386253 := bbase (se 3 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 2386253 = 894845) (by norm_num)
theorem B1591645 : Blo 1413526 1591645 := bbase (se 3 (by rfl) ⟨298433, by rfl⟩ : syracuseStep 1591645 = 596867) (by norm_num)
theorem B1591681 : Blo 1413526 1591681 := bbase (se 2 (by rfl) ⟨596880, by rfl⟩ : syracuseStep 1591681 = 1193761) (by norm_num)
theorem B3180941 : Blo 1413526 3180941 := bbase (se 3 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 3180941 = 1192853) (by norm_num)
theorem B1698197 : Blo 1413526 1698197 := bbase (se 6 (by rfl) ⟨39801, by rfl⟩ : syracuseStep 1698197 = 79603) (by norm_num)
theorem B1591717 : Blo 1413526 1591717 := bbase (se 4 (by rfl) ⟨149223, by rfl⟩ : syracuseStep 1591717 = 298447) (by norm_num)
theorem B6121925 : Blo 1413526 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B1591753 : Blo 1413526 1591753 := bbase (se 2 (by rfl) ⟨596907, by rfl⟩ : syracuseStep 1591753 = 1193815) (by norm_num)
theorem B2386381 : Blo 1413526 2386381 := bbase (se 3 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 2386381 = 894893) (by norm_num)
theorem B3181013 : Blo 1413526 3181013 := bbase (se 7 (by rfl) ⟨37277, by rfl⟩ : syracuseStep 3181013 = 74555) (by norm_num)
theorem B1591789 : Blo 1413526 1591789 := bbase (se 3 (by rfl) ⟨298460, by rfl⟩ : syracuseStep 1591789 = 596921) (by norm_num)
theorem B1698313 : Blo 1413526 1698313 := bbase (se 2 (by rfl) ⟨636867, by rfl⟩ : syracuseStep 1698313 = 1273735) (by norm_num)
theorem B1591825 : Blo 1413526 1591825 := bbase (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) (by norm_num)
theorem B3181085 : Blo 1413526 3181085 := bbase (se 3 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 3181085 = 1192907) (by norm_num)
theorem B2386469 : Blo 1413526 2386469 := bbase (se 4 (by rfl) ⟨223731, by rfl⟩ : syracuseStep 2386469 = 447463) (by norm_num)
theorem B11463221 : Blo 1413526 11463221 := bbase (se 5 (by rfl) ⟨537338, by rfl⟩ : syracuseStep 11463221 = 1074677) (by norm_num)
theorem B1591861 : Blo 1413526 1591861 := bbase (se 5 (by rfl) ⟨74618, by rfl⟩ : syracuseStep 1591861 = 149237) (by norm_num)
theorem B1509949 : Blo 1413526 1509949 := bbase (se 3 (by rfl) ⟨283115, by rfl⟩ : syracuseStep 1509949 = 566231) (by norm_num)
theorem B1591897 : Blo 1413526 1591897 := bbase (se 2 (by rfl) ⟨596961, by rfl⟩ : syracuseStep 1591897 = 1193923) (by norm_num)
theorem B3181157 : Blo 1413526 3181157 := bbase (se 4 (by rfl) ⟨298233, by rfl⟩ : syracuseStep 3181157 = 596467) (by norm_num)
theorem B1698409 : Blo 1413526 1698409 := bbase (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) (by norm_num)
theorem B2419325 : Blo 1413526 2419325 := bbase (se 3 (by rfl) ⟨453623, by rfl⟩ : syracuseStep 2419325 = 907247) (by norm_num)
theorem B1591933 : Blo 1413526 1591933 := bbase (se 3 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 1591933 = 596975) (by norm_num)
theorem B3582589 : Blo 1413526 3582589 := bbase (se 3 (by rfl) ⟨671735, by rfl⟩ : syracuseStep 3582589 = 1343471) (by norm_num)
theorem B1510021 : Blo 1413526 1510021 := bbase (se 4 (by rfl) ⟨141564, by rfl⟩ : syracuseStep 1510021 = 283129) (by norm_num)
theorem B1591969 : Blo 1413526 1591969 := bbase (se 2 (by rfl) ⟨596988, by rfl⟩ : syracuseStep 1591969 = 1193977) (by norm_num)
theorem B2386597 : Blo 1413526 2386597 := bbase (se 4 (by rfl) ⟨223743, by rfl⟩ : syracuseStep 2386597 = 447487) (by norm_num)
theorem B3181229 : Blo 1413526 3181229 := bbase (se 3 (by rfl) ⟨596480, by rfl⟩ : syracuseStep 3181229 = 1192961) (by norm_num)
theorem B11463349 : Blo 1413526 11463349 := bbase (se 5 (by rfl) ⟨537344, by rfl⟩ : syracuseStep 11463349 = 1074689) (by norm_num)
theorem B2329277 : Blo 1413526 2329277 := bbase (se 3 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 2329277 = 873479) (by norm_num)
theorem B1592005 : Blo 1413526 1592005 := bbase (se 4 (by rfl) ⟨149250, by rfl⟩ : syracuseStep 1592005 = 298501) (by norm_num)
theorem B1592041 : Blo 1413526 1592041 := bbase (se 2 (by rfl) ⟨597015, by rfl⟩ : syracuseStep 1592041 = 1194031) (by norm_num)
theorem B3582701 : Blo 1413526 3582701 := bbase (se 3 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 3582701 = 1343513) (by norm_num)
theorem B3181301 : Blo 1413526 3181301 := bbase (se 5 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 3181301 = 298247) (by norm_num)
theorem B1698553 : Blo 1413526 1698553 := bbase (se 2 (by rfl) ⟨636957, by rfl⟩ : syracuseStep 1698553 = 1273915) (by norm_num)
theorem B2386685 : Blo 1413526 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B1723141 : Blo 1413526 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B1592077 : Blo 1413526 1592077 := bbase (se 3 (by rfl) ⟨298514, by rfl⟩ : syracuseStep 1592077 = 597029) (by norm_num)
theorem B1592113 : Blo 1413526 1592113 := bbase (se 2 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 1592113 = 1194085) (by norm_num)
theorem B1510201 : Blo 1413526 1510201 := bbase (se 2 (by rfl) ⟨566325, by rfl⟩ : syracuseStep 1510201 = 1132651) (by norm_num)
theorem B3181373 : Blo 1413526 3181373 := bbase (se 3 (by rfl) ⟨596507, by rfl⟩ : syracuseStep 3181373 = 1193015) (by norm_num)
theorem B1592149 : Blo 1413526 1592149 := bbase (se 9 (by rfl) ⟨4664, by rfl⟩ : syracuseStep 1592149 = 9329) (by norm_num)
theorem B1592185 : Blo 1413526 1592185 := bbase (se 2 (by rfl) ⟨597069, by rfl⟩ : syracuseStep 1592185 = 1194139) (by norm_num)
theorem B2386813 : Blo 1413526 2386813 := bbase (se 3 (by rfl) ⟨447527, by rfl⟩ : syracuseStep 2386813 = 895055) (by norm_num)
theorem B3181445 : Blo 1413526 3181445 := bbase (se 4 (by rfl) ⟨298260, by rfl⟩ : syracuseStep 3181445 = 596521) (by norm_num)
theorem B1592221 : Blo 1413526 1592221 := bbase (se 3 (by rfl) ⟨298541, by rfl⟩ : syracuseStep 1592221 = 597083) (by norm_num)
theorem B3582893 : Blo 1413526 3582893 := bbase (se 3 (by rfl) ⟨671792, by rfl⟩ : syracuseStep 3582893 = 1343585) (by norm_num)
theorem B1592257 : Blo 1413526 1592257 := bbase (se 2 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 1592257 = 1194193) (by norm_num)
theorem B3181517 : Blo 1413526 3181517 := bbase (se 3 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 3181517 = 1193069) (by norm_num)
theorem B2386901 : Blo 1413526 2386901 := bbase (se 7 (by rfl) ⟨27971, by rfl⟩ : syracuseStep 2386901 = 55943) (by norm_num)
theorem B1592293 : Blo 1413526 1592293 := bbase (se 4 (by rfl) ⟨149277, by rfl⟩ : syracuseStep 1592293 = 298555) (by norm_num)
theorem B1592329 : Blo 1413526 1592329 := bbase (se 2 (by rfl) ⟨597123, by rfl⟩ : syracuseStep 1592329 = 1194247) (by norm_num)
theorem B3181589 : Blo 1413526 3181589 := bbase (se 6 (by rfl) ⟨74568, by rfl⟩ : syracuseStep 3181589 = 149137) (by norm_num)
theorem B1592365 : Blo 1413526 1592365 := bbase (se 3 (by rfl) ⟨298568, by rfl⟩ : syracuseStep 1592365 = 597137) (by norm_num)
theorem B4361285 : Blo 1413526 4361285 := bbase (se 4 (by rfl) ⟨408870, by rfl⟩ : syracuseStep 4361285 = 817741) (by norm_num)
theorem B1592401 : Blo 1413526 1592401 := bbase (se 2 (by rfl) ⟨597150, by rfl⟩ : syracuseStep 1592401 = 1194301) (by norm_num)
theorem B2387029 : Blo 1413526 2387029 := bbase (se 8 (by rfl) ⟨13986, by rfl⟩ : syracuseStep 2387029 = 27973) (by norm_num)
theorem B3181661 : Blo 1413526 3181661 := bbase (se 3 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 3181661 = 1193123) (by norm_num)
theorem B5368949 : Blo 1413526 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B1592437 : Blo 1413526 1592437 := bbase (se 5 (by rfl) ⟨74645, by rfl⟩ : syracuseStep 1592437 = 149291) (by norm_num)
theorem B1789057 : Blo 1413526 1789057 := bbase (se 2 (by rfl) ⟨670896, by rfl⟩ : syracuseStep 1789057 = 1341793) (by norm_num)
theorem B5442709 : Blo 1413526 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B3181733 : Blo 1413526 3181733 := bbase (se 4 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 3181733 = 596575) (by norm_num)
theorem B2387117 : Blo 1413526 2387117 := bbase (se 3 (by rfl) ⟨447584, by rfl⟩ : syracuseStep 2387117 = 895169) (by norm_num)
theorem B2419885 : Blo 1413526 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B2149573 : Blo 1413526 2149573 := bbase (se 4 (by rfl) ⟨201522, by rfl⟩ : syracuseStep 2149573 = 403045) (by norm_num)
theorem B3181805 : Blo 1413526 3181805 := bbase (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) (by norm_num)
theorem B4771061 : Blo 1413526 4771061 := bbase (se 5 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 4771061 = 447287) (by norm_num)
theorem B13593845 : Blo 1413526 13593845 := bbase (se 5 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 13593845 = 1274423) (by norm_num)
theorem B1510645 : Blo 1413526 1510645 := bbase (se 5 (by rfl) ⟨70811, by rfl⟩ : syracuseStep 1510645 = 141623) (by norm_num)
theorem B10743029 : Blo 1413526 10743029 := bbase (se 5 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 10743029 = 1007159) (by norm_num)
theorem B1789229 : Blo 1413526 1789229 := bbase (se 3 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 1789229 = 670961) (by norm_num)
theorem B2387245 : Blo 1413526 2387245 := bbase (se 3 (by rfl) ⟨447608, by rfl⟩ : syracuseStep 2387245 = 895217) (by norm_num)
theorem B3181877 : Blo 1413526 3181877 := bbase (se 5 (by rfl) ⟨149150, by rfl⟩ : syracuseStep 3181877 = 298301) (by norm_num)
theorem B2420021 : Blo 1413526 2420021 := bbase (se 5 (by rfl) ⟨113438, by rfl⟩ : syracuseStep 2420021 = 226877) (by norm_num)
theorem B1789285 : Blo 1413526 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B2420077 : Blo 1413526 2420077 := bbase (se 3 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 2420077 = 907529) (by norm_num)
theorem B1510769 : Blo 1413526 1510769 := bbase (se 2 (by rfl) ⟨566538, by rfl⟩ : syracuseStep 1510769 = 1133077) (by norm_num)
theorem B3181949 : Blo 1413526 3181949 := bbase (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) (by norm_num)
theorem B2387333 : Blo 1413526 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B1813909 : Blo 1413526 1813909 := bbase (se 6 (by rfl) ⟨42513, by rfl⟩ : syracuseStep 1813909 = 85027) (by norm_num)
theorem B5369237 : Blo 1413526 5369237 := bbase (se 6 (by rfl) ⟨125841, by rfl⟩ : syracuseStep 5369237 = 251683) (by norm_num)
theorem B1789381 : Blo 1413526 1789381 := bbase (se 4 (by rfl) ⟨167754, by rfl⟩ : syracuseStep 1789381 = 335509) (by norm_num)
theorem B3182021 : Blo 1413526 3182021 := bbase (se 4 (by rfl) ⟨298314, by rfl⟩ : syracuseStep 3182021 = 596629) (by norm_num)
theorem B2387461 : Blo 1413526 2387461 := bbase (se 4 (by rfl) ⟨223824, by rfl⟩ : syracuseStep 2387461 = 447649) (by norm_num)
theorem B3182093 : Blo 1413526 3182093 := bbase (se 3 (by rfl) ⟨596642, by rfl⟩ : syracuseStep 3182093 = 1193285) (by norm_num)
theorem B2068021 : Blo 1413526 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B3182165 : Blo 1413526 3182165 := bbase (se 8 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 3182165 = 37291) (by norm_num)
theorem B7163477 : Blo 1413526 7163477 := bbase (se 8 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 7163477 = 83947) (by norm_num)
theorem B2387549 : Blo 1413526 2387549 := bbase (se 3 (by rfl) ⟨447665, by rfl⟩ : syracuseStep 2387549 = 895331) (by norm_num)
theorem B1511021 : Blo 1413526 1511021 := bbase (se 3 (by rfl) ⟨283316, by rfl⟩ : syracuseStep 1511021 = 566633) (by norm_num)
theorem B1912429 : Blo 1413526 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B1789553 : Blo 1413526 1789553 := bbase (se 2 (by rfl) ⟨671082, by rfl⟩ : syracuseStep 1789553 = 1342165) (by norm_num)
theorem B10735253 : Blo 1413526 10735253 := bbase (se 6 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 10735253 = 503215) (by norm_num)
theorem B3182237 : Blo 1413526 3182237 := bbase (se 3 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 3182237 = 1193339) (by norm_num)
theorem B4771493 : Blo 1413526 4771493 := bbase (se 4 (by rfl) ⟨447327, by rfl⟩ : syracuseStep 4771493 = 894655) (by norm_num)
theorem B1789609 : Blo 1413526 1789609 := bbase (se 2 (by rfl) ⟨671103, by rfl⟩ : syracuseStep 1789609 = 1342207) (by norm_num)
theorem B5738165 : Blo 1413526 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B2387677 : Blo 1413526 2387677 := bbase (se 3 (by rfl) ⟨447689, by rfl⟩ : syracuseStep 2387677 = 895379) (by norm_num)
theorem B3182309 : Blo 1413526 3182309 := bbase (se 4 (by rfl) ⟨298341, by rfl⟩ : syracuseStep 3182309 = 596683) (by norm_num)
theorem B1789705 : Blo 1413526 1789705 := bbase (se 2 (by rfl) ⟨671139, by rfl⟩ : syracuseStep 1789705 = 1342279) (by norm_num)
theorem B3182381 : Blo 1413526 3182381 := bbase (se 3 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 3182381 = 1193393) (by norm_num)
theorem B2387765 : Blo 1413526 2387765 := bbase (se 5 (by rfl) ⟨111926, by rfl⟩ : syracuseStep 2387765 = 223853) (by norm_num)
theorem B1814329 : Blo 1413526 1814329 := bbase (se 2 (by rfl) ⟨680373, by rfl⟩ : syracuseStep 1814329 = 1360747) (by norm_num)
theorem B3182453 : Blo 1413526 3182453 := bbase (se 5 (by rfl) ⟨149177, by rfl⟩ : syracuseStep 3182453 = 298355) (by norm_num)
theorem B2723725 : Blo 1413526 2723725 := bbase (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) (by norm_num)
theorem B2723749 : Blo 1413526 2723749 := bbase (se 4 (by rfl) ⟨255351, by rfl⟩ : syracuseStep 2723749 = 510703) (by norm_num)
theorem B1789877 : Blo 1413526 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B2387893 : Blo 1413526 2387893 := bbase (se 5 (by rfl) ⟨111932, by rfl⟩ : syracuseStep 2387893 = 223865) (by norm_num)
theorem B3182525 : Blo 1413526 3182525 := bbase (se 3 (by rfl) ⟨596723, by rfl⟩ : syracuseStep 3182525 = 1193447) (by norm_num)
theorem B6041573 : Blo 1413526 6041573 := bbase (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) (by norm_num)
theorem B1789933 : Blo 1413526 1789933 := bbase (se 3 (by rfl) ⟨335612, by rfl⟩ : syracuseStep 1789933 = 671225) (by norm_num)
theorem B3821573 : Blo 1413526 3821573 := bbase (se 4 (by rfl) ⟨358272, by rfl⟩ : syracuseStep 3821573 = 716545) (by norm_num)
theorem B3182597 : Blo 1413526 3182597 := bbase (se 4 (by rfl) ⟨298368, by rfl⟩ : syracuseStep 3182597 = 596737) (by norm_num)
theorem B2387981 : Blo 1413526 2387981 := bbase (se 3 (by rfl) ⟨447746, by rfl⟩ : syracuseStep 2387981 = 895493) (by norm_num)
theorem B1511465 : Blo 1413526 1511465 := bbase (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) (by norm_num)
theorem B1790029 : Blo 1413526 1790029 := bbase (se 3 (by rfl) ⟨335630, by rfl⟩ : syracuseStep 1790029 = 671261) (by norm_num)
theorem B3182669 : Blo 1413526 3182669 := bbase (se 3 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 3182669 = 1193501) (by norm_num)
theorem B4771925 : Blo 1413526 4771925 := bbase (se 8 (by rfl) ⟨27960, by rfl⟩ : syracuseStep 4771925 = 55921) (by norm_num)
theorem B2420837 : Blo 1413526 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B12087413 : Blo 1413526 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B1814657 : Blo 1413526 1814657 := bbase (se 2 (by rfl) ⟨680496, by rfl⟩ : syracuseStep 1814657 = 1360993) (by norm_num)
theorem B2388109 : Blo 1413526 2388109 := bbase (se 3 (by rfl) ⟨447770, by rfl⟩ : syracuseStep 2388109 = 895541) (by norm_num)
theorem B3182741 : Blo 1413526 3182741 := bbase (se 6 (by rfl) ⟨74595, by rfl⟩ : syracuseStep 3182741 = 149191) (by norm_num)
theorem B2298013 : Blo 1413526 2298013 := bbase (se 3 (by rfl) ⟨430877, by rfl⟩ : syracuseStep 2298013 = 861755) (by norm_num)
theorem B3018941 : Blo 1413526 3018941 := bbase (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) (by norm_num)
theorem B2150621 : Blo 1413526 2150621 := bbase (se 3 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 2150621 = 806483) (by norm_num)
theorem B3182813 : Blo 1413526 3182813 := bbase (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) (by norm_num)
theorem B2388197 : Blo 1413526 2388197 := bbase (se 4 (by rfl) ⟨223893, by rfl⟩ : syracuseStep 2388197 = 447787) (by norm_num)
theorem B1790201 : Blo 1413526 1790201 := bbase (se 2 (by rfl) ⟨671325, by rfl⟩ : syracuseStep 1790201 = 1342651) (by norm_num)
theorem B6041861 : Blo 1413526 6041861 := bbase (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) (by norm_num)
theorem B2265365 : Blo 1413526 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B3182885 : Blo 1413526 3182885 := bbase (se 4 (by rfl) ⟨298395, by rfl⟩ : syracuseStep 3182885 = 596791) (by norm_num)
theorem B1790257 : Blo 1413526 1790257 := bbase (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) (by norm_num)
theorem B4591973 : Blo 1413526 4591973 := bbase (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) (by norm_num)
theorem B2388325 : Blo 1413526 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B3182957 : Blo 1413526 3182957 := bbase (se 3 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 3182957 = 1193609) (by norm_num)
theorem B1790353 : Blo 1413526 1790353 := bbase (se 2 (by rfl) ⟨671382, by rfl⟩ : syracuseStep 1790353 = 1342765) (by norm_num)
theorem B2265493 : Blo 1413526 2265493 := bbase (se 6 (by rfl) ⟨53097, by rfl⟩ : syracuseStep 2265493 = 106195) (by norm_num)
theorem B1700273 : Blo 1413526 1700273 := bbase (se 2 (by rfl) ⟨637602, by rfl⟩ : syracuseStep 1700273 = 1275205) (by norm_num)
theorem B3822005 : Blo 1413526 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B3183029 : Blo 1413526 3183029 := bbase (se 5 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 3183029 = 298409) (by norm_num)
theorem B2388413 : Blo 1413526 2388413 := bbase (se 3 (by rfl) ⟨447827, by rfl⟩ : syracuseStep 2388413 = 895655) (by norm_num)
theorem B3183101 : Blo 1413526 3183101 := bbase (se 3 (by rfl) ⟨596831, by rfl⟩ : syracuseStep 3183101 = 1193663) (by norm_num)
theorem B4772357 : Blo 1413526 4772357 := bbase (se 4 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 4772357 = 894817) (by norm_num)
theorem B1700389 : Blo 1413526 1700389 := bbase (se 4 (by rfl) ⟨159411, by rfl⟩ : syracuseStep 1700389 = 318823) (by norm_num)
theorem B5370421 : Blo 1413526 5370421 := bbase (se 5 (by rfl) ⟨251738, by rfl⟩ : syracuseStep 5370421 = 503477) (by norm_num)
theorem B1790525 : Blo 1413526 1790525 := bbase (se 3 (by rfl) ⟨335723, by rfl⟩ : syracuseStep 1790525 = 671447) (by norm_num)
theorem B2388541 : Blo 1413526 2388541 := bbase (se 3 (by rfl) ⟨447851, by rfl⟩ : syracuseStep 2388541 = 895703) (by norm_num)
theorem B3183173 : Blo 1413526 3183173 := bbase (se 4 (by rfl) ⟨298422, by rfl⟩ : syracuseStep 3183173 = 596845) (by norm_num)
theorem B1700461 : Blo 1413526 1700461 := bbase (se 3 (by rfl) ⟨318836, by rfl⟩ : syracuseStep 1700461 = 637673) (by norm_num)
theorem B1790581 : Blo 1413526 1790581 := bbase (se 5 (by rfl) ⟨83933, by rfl⟩ : syracuseStep 1790581 = 167867) (by norm_num)
theorem B2683525 : Blo 1413526 2683525 := bbase (se 4 (by rfl) ⟨251580, by rfl⟩ : syracuseStep 2683525 = 503161) (by norm_num)
theorem B4838021 : Blo 1413526 4838021 := bbase (se 4 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 4838021 = 907129) (by norm_num)
theorem B3183245 : Blo 1413526 3183245 := bbase (se 3 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 3183245 = 1193717) (by norm_num)
theorem B2388629 : Blo 1413526 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B5444309 : Blo 1413526 5444309 := bbase (se 7 (by rfl) ⟨63800, by rfl⟩ : syracuseStep 5444309 = 127601) (by norm_num)
theorem B3183317 : Blo 1413526 3183317 := bbase (se 7 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 3183317 = 74609) (by norm_num)
theorem B1790677 : Blo 1413526 1790677 := bbase (se 7 (by rfl) ⟨20984, by rfl⟩ : syracuseStep 1790677 = 41969) (by norm_num)
theorem B5100245 : Blo 1413526 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B24507157 : Blo 1413526 24507157 := bbase (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) (by norm_num)
theorem B3183389 : Blo 1413526 3183389 := bbase (se 3 (by rfl) ⟨596885, by rfl⟩ : syracuseStep 3183389 = 1193771) (by norm_num)
theorem B2683685 : Blo 1413526 2683685 := bbase (se 4 (by rfl) ⟨251595, by rfl⟩ : syracuseStep 2683685 = 503191) (by norm_num)
theorem B5370725 : Blo 1413526 5370725 := bbase (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) (by norm_num)
theorem B3183461 : Blo 1413526 3183461 := bbase (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) (by norm_num)
theorem B7164773 : Blo 1413526 7164773 := bbase (se 4 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 7164773 = 1343395) (by norm_num)
theorem B1790849 : Blo 1413526 1790849 := bbase (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) (by norm_num)
theorem B3019693 : Blo 1413526 3019693 := bbase (se 3 (by rfl) ⟨566192, by rfl⟩ : syracuseStep 3019693 = 1132385) (by norm_num)
theorem B3183533 : Blo 1413526 3183533 := bbase (se 3 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 3183533 = 1193825) (by norm_num)
theorem B2683829 : Blo 1413526 2683829 := bbase (se 5 (by rfl) ⟨125804, by rfl⟩ : syracuseStep 2683829 = 251609) (by norm_num)
theorem B4772789 : Blo 1413526 4772789 := bbase (se 5 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 4772789 = 447449) (by norm_num)
theorem B1790905 : Blo 1413526 1790905 := bbase (se 2 (by rfl) ⟨671589, by rfl⟩ : syracuseStep 1790905 = 1343179) (by norm_num)
theorem B6042613 : Blo 1413526 6042613 := bbase (se 5 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 6042613 = 566495) (by norm_num)
theorem B3183605 : Blo 1413526 3183605 := bbase (se 5 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 3183605 = 298463) (by norm_num)
theorem B5100533 : Blo 1413526 5100533 := bbase (se 5 (by rfl) ⟨239087, by rfl⟩ : syracuseStep 5100533 = 478175) (by norm_num)
theorem B1791001 : Blo 1413526 1791001 := bbase (se 2 (by rfl) ⟨671625, by rfl⟩ : syracuseStep 1791001 = 1343251) (by norm_num)
theorem B6796325 : Blo 1413526 6796325 := bbase (se 4 (by rfl) ⟨637155, by rfl⟩ : syracuseStep 6796325 = 1274311) (by norm_num)
theorem B9679925 : Blo 1413526 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B3019837 : Blo 1413526 3019837 := bbase (se 3 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 3019837 = 1132439) (by norm_num)
theorem B3183677 : Blo 1413526 3183677 := bbase (se 3 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 3183677 = 1193879) (by norm_num)
theorem B81605717 : Blo 1413526 81605717 := bbase (se 8 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 81605717 = 956317) (by norm_num)
theorem B8606837 : Blo 1413526 8606837 := bbase (se 5 (by rfl) ⟨403445, by rfl⟩ : syracuseStep 8606837 = 806891) (by norm_num)
theorem B3183749 : Blo 1413526 3183749 := bbase (se 4 (by rfl) ⟨298476, by rfl⟩ : syracuseStep 3183749 = 596953) (by norm_num)
theorem B25801877 : Blo 1413526 25801877 := bbase (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) (by norm_num)
theorem B29439125 : Blo 1413526 29439125 := bbase (se 6 (by rfl) ⟨689979, by rfl⟩ : syracuseStep 29439125 = 1379959) (by norm_num)
theorem B2151581 : Blo 1413526 2151581 := bbase (se 3 (by rfl) ⟨403421, by rfl⟩ : syracuseStep 2151581 = 806843) (by norm_num)
theorem B4027589 : Blo 1413526 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B1791173 : Blo 1413526 1791173 := bbase (se 4 (by rfl) ⟨167922, by rfl⟩ : syracuseStep 1791173 = 335845) (by norm_num)
theorem B3183821 : Blo 1413526 3183821 := bbase (se 3 (by rfl) ⟨596966, by rfl⟩ : syracuseStep 3183821 = 1193933) (by norm_num)
theorem B2684117 : Blo 1413526 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B6894821 : Blo 1413526 6894821 := bbase (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) (by norm_num)
theorem B1791229 : Blo 1413526 1791229 := bbase (se 3 (by rfl) ⟨335855, by rfl⟩ : syracuseStep 1791229 = 671711) (by norm_num)
theorem B7156997 : Blo 1413526 7156997 := bbase (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) (by norm_num)
theorem B3183893 : Blo 1413526 3183893 := bbase (se 6 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 3183893 = 149245) (by norm_num)
theorem B3183965 : Blo 1413526 3183965 := bbase (se 3 (by rfl) ⟨596993, by rfl⟩ : syracuseStep 3183965 = 1193987) (by norm_num)
theorem B1791325 : Blo 1413526 1791325 := bbase (se 3 (by rfl) ⟨335873, by rfl⟩ : syracuseStep 1791325 = 671747) (by norm_num)
theorem B4773221 : Blo 1413526 4773221 := bbase (se 4 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 4773221 = 894979) (by norm_num)
theorem B2684269 : Blo 1413526 2684269 := bbase (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) (by norm_num)
theorem B3184037 : Blo 1413526 3184037 := bbase (se 4 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 3184037 = 597007) (by norm_num)
theorem B5100965 : Blo 1413526 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B3020213 : Blo 1413526 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B3184109 : Blo 1413526 3184109 := bbase (se 3 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 3184109 = 1194041) (by norm_num)
theorem B3823109 : Blo 1413526 3823109 := bbase (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) (by norm_num)
theorem B1791497 : Blo 1413526 1791497 := bbase (se 2 (by rfl) ⟨671811, by rfl⟩ : syracuseStep 1791497 = 1343623) (by norm_num)
theorem B2012701 : Blo 1413526 2012701 := bbase (se 3 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 2012701 = 754763) (by norm_num)
theorem B3184181 : Blo 1413526 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B3184253 : Blo 1413526 3184253 := bbase (se 3 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 3184253 = 1194095) (by norm_num)
theorem B2684573 : Blo 1413526 2684573 := bbase (se 3 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 2684573 = 1006715) (by norm_num)
theorem B3184325 : Blo 1413526 3184325 := bbase (se 4 (by rfl) ⟨298530, by rfl⟩ : syracuseStep 3184325 = 597061) (by norm_num)
theorem B6043349 : Blo 1413526 6043349 := bbase (se 7 (by rfl) ⟨70820, by rfl⟩ : syracuseStep 6043349 = 141641) (by norm_num)
theorem B2266877 : Blo 1413526 2266877 := bbase (se 3 (by rfl) ⟨425039, by rfl⟩ : syracuseStep 2266877 = 850079) (by norm_num)
theorem B3184397 : Blo 1413526 3184397 := bbase (se 3 (by rfl) ⟨597074, by rfl⟩ : syracuseStep 3184397 = 1194149) (by norm_num)
theorem B4773653 : Blo 1413526 4773653 := bbase (se 6 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 4773653 = 223765) (by norm_num)
theorem B2152213 : Blo 1413526 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B3020581 : Blo 1413526 3020581 := bbase (se 4 (by rfl) ⟨283179, by rfl⟩ : syracuseStep 3020581 = 566359) (by norm_num)
theorem B3184469 : Blo 1413526 3184469 := bbase (se 9 (by rfl) ⟨9329, by rfl⟩ : syracuseStep 3184469 = 18659) (by norm_num)
theorem B3184541 : Blo 1413526 3184541 := bbase (se 3 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 3184541 = 1194203) (by norm_num)
theorem B3184613 : Blo 1413526 3184613 := bbase (se 4 (by rfl) ⟨298557, by rfl⟩ : syracuseStep 3184613 = 597115) (by norm_num)
theorem B3184685 : Blo 1413526 3184685 := bbase (se 3 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 3184685 = 1194257) (by norm_num)
theorem B2013293 : Blo 1413526 2013293 := bbase (se 3 (by rfl) ⟨377492, by rfl⟩ : syracuseStep 2013293 = 754985) (by norm_num)
theorem B3184757 : Blo 1413526 3184757 := bbase (se 5 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 3184757 = 298571) (by norm_num)
theorem B7166069 : Blo 1413526 7166069 := bbase (se 5 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 7166069 = 671819) (by norm_num)
theorem B1702013 : Blo 1413526 1702013 := bbase (se 3 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 1702013 = 638255) (by norm_num)
theorem B2013373 : Blo 1413526 2013373 := bbase (se 3 (by rfl) ⟨377507, by rfl⟩ : syracuseStep 2013373 = 755015) (by norm_num)
theorem B3184829 : Blo 1413526 3184829 := bbase (se 3 (by rfl) ⟨597155, by rfl⟩ : syracuseStep 3184829 = 1194311) (by norm_num)
theorem B3578053 : Blo 1413526 3578053 := bbase (se 4 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 3578053 = 670885) (by norm_num)
theorem B4774085 : Blo 1413526 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B3184901 : Blo 1413526 3184901 := bbase (se 4 (by rfl) ⟨298584, by rfl⟩ : syracuseStep 3184901 = 597169) (by norm_num)
theorem B3578165 : Blo 1413526 3578165 := bbase (se 5 (by rfl) ⟨167726, by rfl⟩ : syracuseStep 3578165 = 335453) (by norm_num)
theorem B2013493 : Blo 1413526 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B4905301 : Blo 1413526 4905301 := bbase (se 10 (by rfl) ⟨7185, by rfl⟩ : syracuseStep 4905301 = 14371) (by norm_num)
theorem B36256085 : Blo 1413526 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B3823973 : Blo 1413526 3823973 := bbase (se 4 (by rfl) ⟨358497, by rfl⟩ : syracuseStep 3823973 = 716995) (by norm_num)
theorem B4028773 : Blo 1413526 4028773 := bbase (se 4 (by rfl) ⟨377697, by rfl⟩ : syracuseStep 4028773 = 755395) (by norm_num)
theorem B2685325 : Blo 1413526 2685325 := bbase (se 3 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 2685325 = 1006997) (by norm_num)
theorem B2013589 : Blo 1413526 2013589 := bbase (se 6 (by rfl) ⟨47193, by rfl⟩ : syracuseStep 2013589 = 94387) (by norm_num)
theorem B1472953 : Blo 1413526 1472953 := bbase (se 2 (by rfl) ⟨552357, by rfl⟩ : syracuseStep 1472953 = 1104715) (by norm_num)
theorem B3578357 : Blo 1413526 3578357 := bbase (se 5 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 3578357 = 335471) (by norm_num)
theorem B4028933 : Blo 1413526 4028933 := bbase (se 4 (by rfl) ⟨377712, by rfl⟩ : syracuseStep 4028933 = 755425) (by norm_num)
theorem B7158293 : Blo 1413526 7158293 := bbase (se 6 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 7158293 = 335545) (by norm_num)
theorem B2685469 : Blo 1413526 2685469 := bbase (se 3 (by rfl) ⟨503525, by rfl⟩ : syracuseStep 2685469 = 1007051) (by norm_num)
theorem B1530433 : Blo 1413526 1530433 := bbase (se 2 (by rfl) ⟨573912, by rfl⟩ : syracuseStep 1530433 = 1147825) (by norm_num)
theorem B2120309 : Blo 1413526 2120309 := bbase (se 5 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 2120309 = 198779) (by norm_num)
theorem B4774517 : Blo 1413526 4774517 := bbase (se 5 (by rfl) ⟨223805, by rfl⟩ : syracuseStep 4774517 = 447611) (by norm_num)
theorem B2120333 : Blo 1413526 2120333 := bbase (se 3 (by rfl) ⟨397562, by rfl⟩ : syracuseStep 2120333 = 795125) (by norm_num)
theorem B2120357 : Blo 1413526 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2120381 : Blo 1413526 2120381 := bbase (se 3 (by rfl) ⟨397571, by rfl⟩ : syracuseStep 2120381 = 795143) (by norm_num)
theorem B2685629 : Blo 1413526 2685629 := bbase (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) (by norm_num)
theorem B2120405 : Blo 1413526 2120405 := bbase (se 7 (by rfl) ⟨24848, by rfl⟩ : syracuseStep 2120405 = 49697) (by norm_num)
theorem B3627733 : Blo 1413526 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B2120429 : Blo 1413526 2120429 := bbase (se 3 (by rfl) ⟨397580, by rfl⟩ : syracuseStep 2120429 = 795161) (by norm_num)
theorem B4528885 : Blo 1413526 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B4029173 : Blo 1413526 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B2120453 : Blo 1413526 2120453 := bbase (se 4 (by rfl) ⟨198792, by rfl⟩ : syracuseStep 2120453 = 397585) (by norm_num)
theorem B3824405 : Blo 1413526 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B2120477 : Blo 1413526 2120477 := bbase (se 3 (by rfl) ⟨397589, by rfl⟩ : syracuseStep 2120477 = 795179) (by norm_num)
theorem B2120501 : Blo 1413526 2120501 := bbase (se 5 (by rfl) ⟨99398, by rfl⟩ : syracuseStep 2120501 = 198797) (by norm_num)
theorem B2120525 : Blo 1413526 2120525 := bbase (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) (by norm_num)
theorem B3578701 : Blo 1413526 3578701 := bbase (se 3 (by rfl) ⟨671006, by rfl⟩ : syracuseStep 3578701 = 1342013) (by norm_num)
theorem B2685773 : Blo 1413526 2685773 := bbase (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) (by norm_num)
theorem B8059733 : Blo 1413526 8059733 := bbase (se 9 (by rfl) ⟨23612, by rfl⟩ : syracuseStep 8059733 = 47225) (by norm_num)
theorem B2120549 : Blo 1413526 2120549 := bbase (se 4 (by rfl) ⟨198801, by rfl⟩ : syracuseStep 2120549 = 397603) (by norm_num)
theorem B2120573 : Blo 1413526 2120573 := bbase (se 3 (by rfl) ⟨397607, by rfl⟩ : syracuseStep 2120573 = 795215) (by norm_num)
theorem B2014085 : Blo 1413526 2014085 := bbase (se 4 (by rfl) ⟨188820, by rfl⟩ : syracuseStep 2014085 = 377641) (by norm_num)
theorem B2120597 : Blo 1413526 2120597 := bbase (se 6 (by rfl) ⟨49701, by rfl⟩ : syracuseStep 2120597 = 99403) (by norm_num)
theorem B5372837 : Blo 1413526 5372837 := bbase (se 4 (by rfl) ⟨503703, by rfl⟩ : syracuseStep 5372837 = 1007407) (by norm_num)
theorem B2120621 : Blo 1413526 2120621 := bbase (se 3 (by rfl) ⟨397616, by rfl⟩ : syracuseStep 2120621 = 795233) (by norm_num)
theorem B4029365 : Blo 1413526 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B3578813 : Blo 1413526 3578813 := bbase (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) (by norm_num)
theorem B2120645 : Blo 1413526 2120645 := bbase (se 4 (by rfl) ⟨198810, by rfl⟩ : syracuseStep 2120645 = 397621) (by norm_num)
theorem B8051669 : Blo 1413526 8051669 := bbase (se 7 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 8051669 = 188711) (by norm_num)
theorem B5815253 : Blo 1413526 5815253 := bbase (se 7 (by rfl) ⟨68147, by rfl⟩ : syracuseStep 5815253 = 136295) (by norm_num)
theorem B2120669 : Blo 1413526 2120669 := bbase (se 3 (by rfl) ⟨397625, by rfl⟩ : syracuseStep 2120669 = 795251) (by norm_num)
theorem B2120693 : Blo 1413526 2120693 := bbase (se 5 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 2120693 = 198815) (by norm_num)
theorem B2120717 : Blo 1413526 2120717 := bbase (se 3 (by rfl) ⟨397634, by rfl⟩ : syracuseStep 2120717 = 795269) (by norm_num)
theorem B2120741 : Blo 1413526 2120741 := bbase (se 4 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 2120741 = 397639) (by norm_num)
theorem B4774949 : Blo 1413526 4774949 := bbase (se 4 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 4774949 = 895303) (by norm_num)
theorem B3398701 : Blo 1413526 3398701 := bbase (se 3 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 3398701 = 1274513) (by norm_num)
theorem B2120765 : Blo 1413526 2120765 := bbase (se 3 (by rfl) ⟨397643, by rfl⟩ : syracuseStep 2120765 = 795287) (by norm_num)
theorem B2866261 : Blo 1413526 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B2120789 : Blo 1413526 2120789 := bbase (se 8 (by rfl) ⟨12426, by rfl⟩ : syracuseStep 2120789 = 24853) (by norm_num)
theorem B2120813 : Blo 1413526 2120813 := bbase (se 3 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 2120813 = 795305) (by norm_num)
theorem B2686061 : Blo 1413526 2686061 := bbase (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) (by norm_num)
theorem B3579005 : Blo 1413526 3579005 := bbase (se 3 (by rfl) ⟨671063, by rfl⟩ : syracuseStep 3579005 = 1342127) (by norm_num)
theorem B2120837 : Blo 1413526 2120837 := bbase (se 4 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 2120837 = 397657) (by norm_num)
theorem B13589653 : Blo 1413526 13589653 := bbase (se 6 (by rfl) ⟨318507, by rfl⟩ : syracuseStep 13589653 = 637015) (by norm_num)
theorem B4299925 : Blo 1413526 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B2120861 : Blo 1413526 2120861 := bbase (se 3 (by rfl) ⟨397661, by rfl⟩ : syracuseStep 2120861 = 795323) (by norm_num)
theorem B2120885 : Blo 1413526 2120885 := bbase (se 5 (by rfl) ⟨99416, by rfl⟩ : syracuseStep 2120885 = 198833) (by norm_num)
theorem B5373125 : Blo 1413526 5373125 := bbase (se 4 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 5373125 = 1007461) (by norm_num)
theorem B2120909 : Blo 1413526 2120909 := bbase (se 3 (by rfl) ⟨397670, by rfl⟩ : syracuseStep 2120909 = 795341) (by norm_num)
theorem B2120933 : Blo 1413526 2120933 := bbase (se 4 (by rfl) ⟨198837, by rfl⟩ : syracuseStep 2120933 = 397675) (by norm_num)
theorem B2120957 : Blo 1413526 2120957 := bbase (se 3 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 2120957 = 795359) (by norm_num)
theorem B2686213 : Blo 1413526 2686213 := bbase (se 4 (by rfl) ⟨251832, by rfl⟩ : syracuseStep 2686213 = 503665) (by norm_num)
theorem B3022085 : Blo 1413526 3022085 := bbase (se 4 (by rfl) ⟨283320, by rfl⟩ : syracuseStep 3022085 = 566641) (by norm_num)
theorem B2120981 : Blo 1413526 2120981 := bbase (se 6 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 2120981 = 99421) (by norm_num)
theorem B2121005 : Blo 1413526 2121005 := bbase (se 3 (by rfl) ⟨397688, by rfl⟩ : syracuseStep 2121005 = 795377) (by norm_num)
theorem B2121029 : Blo 1413526 2121029 := bbase (se 4 (by rfl) ⟨198846, by rfl⟩ : syracuseStep 2121029 = 397693) (by norm_num)
theorem B2121053 : Blo 1413526 2121053 := bbase (se 3 (by rfl) ⟨397697, by rfl⟩ : syracuseStep 2121053 = 795395) (by norm_num)
theorem B2121077 : Blo 1413526 2121077 := bbase (se 5 (by rfl) ⟨99425, by rfl⟩ : syracuseStep 2121077 = 198851) (by norm_num)
theorem B2121101 : Blo 1413526 2121101 := bbase (se 3 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 2121101 = 795413) (by norm_num)
theorem B3022229 : Blo 1413526 3022229 := bbase (se 6 (by rfl) ⟨70833, by rfl⟩ : syracuseStep 3022229 = 141667) (by norm_num)
theorem B2121125 : Blo 1413526 2121125 := bbase (se 4 (by rfl) ⟨198855, by rfl⟩ : syracuseStep 2121125 = 397711) (by norm_num)
theorem B3399077 : Blo 1413526 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B2014637 : Blo 1413526 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B2121149 : Blo 1413526 2121149 := bbase (se 3 (by rfl) ⟨397715, by rfl⟩ : syracuseStep 2121149 = 795431) (by norm_num)
theorem B3579349 : Blo 1413526 3579349 := bbase (se 7 (by rfl) ⟨41945, by rfl⟩ : syracuseStep 3579349 = 83891) (by norm_num)
theorem B2121173 : Blo 1413526 2121173 := bbase (se 7 (by rfl) ⟨24857, by rfl⟩ : syracuseStep 2121173 = 49715) (by norm_num)
theorem B4775381 : Blo 1413526 4775381 := bbase (se 7 (by rfl) ⟨55961, by rfl⟩ : syracuseStep 4775381 = 111923) (by norm_num)
theorem B2121197 : Blo 1413526 2121197 := bbase (se 3 (by rfl) ⟨397724, by rfl⟩ : syracuseStep 2121197 = 795449) (by norm_num)
theorem B9068021 : Blo 1413526 9068021 := bbase (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) (by norm_num)
theorem B2121221 : Blo 1413526 2121221 := bbase (se 4 (by rfl) ⟨198864, by rfl⟩ : syracuseStep 2121221 = 397729) (by norm_num)
theorem B2121245 : Blo 1413526 2121245 := bbase (se 3 (by rfl) ⟨397733, by rfl⟩ : syracuseStep 2121245 = 795467) (by norm_num)
theorem B2121269 : Blo 1413526 2121269 := bbase (se 5 (by rfl) ⟨99434, by rfl⟩ : syracuseStep 2121269 = 198869) (by norm_num)
theorem B2686517 : Blo 1413526 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B3579461 : Blo 1413526 3579461 := bbase (se 4 (by rfl) ⟨335574, by rfl⟩ : syracuseStep 3579461 = 671149) (by norm_num)
theorem B2121293 : Blo 1413526 2121293 := bbase (se 3 (by rfl) ⟨397742, by rfl⟩ : syracuseStep 2121293 = 795485) (by norm_num)
theorem B2121317 : Blo 1413526 2121317 := bbase (se 4 (by rfl) ⟨198873, by rfl⟩ : syracuseStep 2121317 = 397747) (by norm_num)
theorem B2121341 : Blo 1413526 2121341 := bbase (se 3 (by rfl) ⟨397751, by rfl⟩ : syracuseStep 2121341 = 795503) (by norm_num)
theorem B2121365 : Blo 1413526 2121365 := bbase (se 6 (by rfl) ⟨49719, by rfl⟩ : syracuseStep 2121365 = 99439) (by norm_num)
theorem B2121389 : Blo 1413526 2121389 := bbase (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) (by norm_num)
theorem B2121413 : Blo 1413526 2121413 := bbase (se 4 (by rfl) ⟨198882, by rfl⟩ : syracuseStep 2121413 = 397765) (by norm_num)
theorem B2121437 : Blo 1413526 2121437 := bbase (se 3 (by rfl) ⟨397769, by rfl⟩ : syracuseStep 2121437 = 795539) (by norm_num)
theorem B2866933 : Blo 1413526 2866933 := bbase (se 5 (by rfl) ⟨134387, by rfl⟩ : syracuseStep 2866933 = 268775) (by norm_num)
theorem B2121461 : Blo 1413526 2121461 := bbase (se 5 (by rfl) ⟨99443, by rfl⟩ : syracuseStep 2121461 = 198887) (by norm_num)
theorem B3022589 : Blo 1413526 3022589 := bbase (se 3 (by rfl) ⟨566735, by rfl⟩ : syracuseStep 3022589 = 1133471) (by norm_num)
theorem B3579653 : Blo 1413526 3579653 := bbase (se 4 (by rfl) ⟨335592, by rfl⟩ : syracuseStep 3579653 = 671185) (by norm_num)
theorem B2121485 : Blo 1413526 2121485 := bbase (se 3 (by rfl) ⟨397778, by rfl⟩ : syracuseStep 2121485 = 795557) (by norm_num)
theorem B7159589 : Blo 1413526 7159589 := bbase (se 4 (by rfl) ⟨671211, by rfl⟩ : syracuseStep 7159589 = 1342423) (by norm_num)
theorem B2121509 : Blo 1413526 2121509 := bbase (se 4 (by rfl) ⟨198891, by rfl⟩ : syracuseStep 2121509 = 397783) (by norm_num)
theorem B2121533 : Blo 1413526 2121533 := bbase (se 3 (by rfl) ⟨397787, by rfl⟩ : syracuseStep 2121533 = 795575) (by norm_num)
theorem B2121557 : Blo 1413526 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B3399509 : Blo 1413526 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B2121581 : Blo 1413526 2121581 := bbase (se 3 (by rfl) ⟨397796, by rfl⟩ : syracuseStep 2121581 = 795593) (by norm_num)
theorem B2121605 : Blo 1413526 2121605 := bbase (se 4 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 2121605 = 397801) (by norm_num)
theorem B4775813 : Blo 1413526 4775813 := bbase (se 4 (by rfl) ⟨447732, by rfl⟩ : syracuseStep 4775813 = 895465) (by norm_num)
theorem B4030357 : Blo 1413526 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B2121629 : Blo 1413526 2121629 := bbase (se 3 (by rfl) ⟨397805, by rfl⟩ : syracuseStep 2121629 = 795611) (by norm_num)
theorem B2121653 : Blo 1413526 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B2121677 : Blo 1413526 2121677 := bbase (se 3 (by rfl) ⟨397814, by rfl⟩ : syracuseStep 2121677 = 795629) (by norm_num)
theorem B2121701 : Blo 1413526 2121701 := bbase (se 4 (by rfl) ⟨198909, by rfl⟩ : syracuseStep 2121701 = 397819) (by norm_num)
theorem B8060917 : Blo 1413526 8060917 := bbase (se 5 (by rfl) ⟨377855, by rfl⟩ : syracuseStep 8060917 = 755711) (by norm_num)
theorem B2121725 : Blo 1413526 2121725 := bbase (se 3 (by rfl) ⟨397823, by rfl⟩ : syracuseStep 2121725 = 795647) (by norm_num)
theorem B2547715 : Blo 1413526 2547715 := bstep (se 1 (by rfl) ⟨1910786, by rfl⟩ : syracuseStep 2547715 = 3821573) B3821573
theorem B2121731 : Blo 1413526 2121731 := bstep (se 1 (by rfl) ⟨1591298, by rfl⟩ : syracuseStep 2121731 = 3182597) B3182597
theorem B2121761 : Blo 1413526 2121761 := bstep (se 2 (by rfl) ⟨795660, by rfl⟩ : syracuseStep 2121761 = 1591321) B1591321
theorem B5734435 : Blo 1413526 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B2121779 : Blo 1413526 2121779 := bstep (se 1 (by rfl) ⟨1591334, by rfl⟩ : syracuseStep 2121779 = 3182669) B3182669
theorem B1613891 : Blo 1413526 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B2121809 : Blo 1413526 2121809 := bstep (se 2 (by rfl) ⟨795678, by rfl⟩ : syracuseStep 2121809 = 1591357) B1591357
theorem B2121827 : Blo 1413526 2121827 := bstep (se 1 (by rfl) ⟨1591370, by rfl⟩ : syracuseStep 2121827 = 3182741) B3182741
theorem B4030573 : Blo 1413526 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B2121857 : Blo 1413526 2121857 := bstep (se 2 (by rfl) ⟨795696, by rfl⟩ : syracuseStep 2121857 = 1591393) B1591393
theorem B1433747 : Blo 1413526 1433747 := bstep (se 1 (by rfl) ⟨1075310, by rfl⟩ : syracuseStep 1433747 = 2150621) B2150621
theorem B2121875 : Blo 1413526 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B3629233 : Blo 1413526 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B2121905 : Blo 1413526 2121905 := bstep (se 2 (by rfl) ⟨795714, by rfl⟩ : syracuseStep 2121905 = 1591429) B1591429
theorem B2867395 : Blo 1413526 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B2121923 : Blo 1413526 2121923 := bstep (se 1 (by rfl) ⟨1591442, by rfl⟩ : syracuseStep 2121923 = 3182885) B3182885
theorem B2687185 : Blo 1413526 2687185 := bstep (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) B2015389
theorem B2121953 : Blo 1413526 2121953 := bstep (se 2 (by rfl) ⟨795732, by rfl⟩ : syracuseStep 2121953 = 1591465) B1591465
theorem B2121971 : Blo 1413526 2121971 := bstep (se 1 (by rfl) ⟨1591478, by rfl⟩ : syracuseStep 2121971 = 3182957) B3182957
theorem B2122001 : Blo 1413526 2122001 := bstep (se 2 (by rfl) ⟨795750, by rfl⟩ : syracuseStep 2122001 = 1591501) B1591501
theorem B2122019 : Blo 1413526 2122019 := bstep (se 1 (by rfl) ⟨1591514, by rfl⟩ : syracuseStep 2122019 = 3183029) B3183029
theorem B2122049 : Blo 1413526 2122049 := bstep (se 2 (by rfl) ⟨795768, by rfl⟩ : syracuseStep 2122049 = 1591537) B1591537
theorem B4538701 : Blo 1413526 4538701 := bstep (se 3 (by rfl) ⟨851006, by rfl⟩ : syracuseStep 4538701 = 1702013) B1702013
theorem B2122067 : Blo 1413526 2122067 := bstep (se 1 (by rfl) ⟨1591550, by rfl⟩ : syracuseStep 2122067 = 3183101) B3183101
theorem B2122097 : Blo 1413526 2122097 := bstep (se 2 (by rfl) ⟨795786, by rfl⟩ : syracuseStep 2122097 = 1591573) B1591573
theorem B2122115 : Blo 1413526 2122115 := bstep (se 1 (by rfl) ⟨1591586, by rfl⟩ : syracuseStep 2122115 = 3183173) B3183173
theorem B2122145 : Blo 1413526 2122145 := bstep (se 2 (by rfl) ⟨795804, by rfl⟩ : syracuseStep 2122145 = 1591609) B1591609
theorem B2122163 : Blo 1413526 2122163 := bstep (se 1 (by rfl) ⟨1591622, by rfl⟩ : syracuseStep 2122163 = 3183245) B3183245
theorem B2122193 : Blo 1413526 2122193 := bstep (se 2 (by rfl) ⟨795822, by rfl⟩ : syracuseStep 2122193 = 1591645) B1591645
theorem B3629539 : Blo 1413526 3629539 := bstep (se 1 (by rfl) ⟨2722154, by rfl⟩ : syracuseStep 3629539 = 5444309) B5444309
theorem B2122211 : Blo 1413526 2122211 := bstep (se 1 (by rfl) ⟨1591658, by rfl⟩ : syracuseStep 2122211 = 3183317) B3183317
theorem B3400163 : Blo 1413526 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B2122241 : Blo 1413526 2122241 := bstep (se 2 (by rfl) ⟨795840, by rfl⟩ : syracuseStep 2122241 = 1591681) B1591681
theorem B4776461 : Blo 1413526 4776461 := bstep (se 3 (by rfl) ⟨895586, by rfl⟩ : syracuseStep 4776461 = 1791173) B1791173
theorem B3580433 : Blo 1413526 3580433 := bstep (se 2 (by rfl) ⟨1342662, by rfl⟩ : syracuseStep 3580433 = 2685325) B2685325
theorem B2122259 : Blo 1413526 2122259 := bstep (se 1 (by rfl) ⟨1591694, by rfl⟩ : syracuseStep 2122259 = 3183389) B3183389
theorem B2122289 : Blo 1413526 2122289 := bstep (se 2 (by rfl) ⟨795858, by rfl⟩ : syracuseStep 2122289 = 1591717) B1591717
theorem B3580483 : Blo 1413526 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B2122307 : Blo 1413526 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B10199621 : Blo 1413526 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B4776515 : Blo 1413526 4776515 := bstep (se 1 (by rfl) ⟨3582386, by rfl⟩ : syracuseStep 4776515 = 7164773) B7164773
theorem B2122337 : Blo 1413526 2122337 := bstep (se 2 (by rfl) ⟨795876, by rfl⟩ : syracuseStep 2122337 = 1591753) B1591753
theorem B4653677 : Blo 1413526 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B2122355 : Blo 1413526 2122355 := bstep (se 1 (by rfl) ⟨1591766, by rfl⟩ : syracuseStep 2122355 = 3183533) B3183533
theorem B2122385 : Blo 1413526 2122385 := bstep (se 2 (by rfl) ⟨795894, by rfl⟩ : syracuseStep 2122385 = 1591789) B1591789
theorem B2122403 : Blo 1413526 2122403 := bstep (se 1 (by rfl) ⟨1591802, by rfl⟩ : syracuseStep 2122403 = 3183605) B3183605
theorem B3400355 : Blo 1413526 3400355 := bstep (se 1 (by rfl) ⟨2550266, by rfl⟩ : syracuseStep 3400355 = 5100533) B5100533
theorem B2122433 : Blo 1413526 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B8053445 : Blo 1413526 8053445 := bstep (se 4 (by rfl) ⟨755010, by rfl⟩ : syracuseStep 8053445 = 1510021) B1510021
theorem B3580625 : Blo 1413526 3580625 := bstep (se 2 (by rfl) ⟨1342734, by rfl⟩ : syracuseStep 3580625 = 2685469) B2685469
theorem B2122451 : Blo 1413526 2122451 := bstep (se 1 (by rfl) ⟨1591838, by rfl⟩ : syracuseStep 2122451 = 3183677) B3183677
theorem B61170389 : Blo 1413526 61170389 := bstep (se 7 (by rfl) ⟨716840, by rfl⟩ : syracuseStep 61170389 = 1433681) B1433681
theorem B54403811 : Blo 1413526 54403811 := bstep (se 1 (by rfl) ⟨40802858, by rfl⟩ : syracuseStep 54403811 = 81605717) B81605717
theorem B7160561 : Blo 1413526 7160561 := bstep (se 2 (by rfl) ⟨2685210, by rfl⟩ : syracuseStep 7160561 = 5370421) B5370421
theorem B2122481 : Blo 1413526 2122481 := bstep (se 2 (by rfl) ⟨795930, by rfl⟩ : syracuseStep 2122481 = 1591861) B1591861
theorem B2122499 : Blo 1413526 2122499 := bstep (se 1 (by rfl) ⟨1591874, by rfl⟩ : syracuseStep 2122499 = 3183749) B3183749
theorem B58106645 : Blo 1413526 58106645 := bstep (se 6 (by rfl) ⟨1361874, by rfl⟩ : syracuseStep 58106645 = 2723749) B2723749
theorem B2122529 : Blo 1413526 2122529 := bstep (se 2 (by rfl) ⟨795948, by rfl⟩ : syracuseStep 2122529 = 1591897) B1591897
theorem B2122547 : Blo 1413526 2122547 := bstep (se 1 (by rfl) ⟨1591910, by rfl⟩ : syracuseStep 2122547 = 3183821) B3183821
theorem B34874165 : Blo 1413526 34874165 := bstep (se 5 (by rfl) ⟨1634726, by rfl⟩ : syracuseStep 34874165 = 3269453) B3269453
theorem B4596547 : Blo 1413526 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B12256069 : Blo 1413526 12256069 := bstep (se 4 (by rfl) ⟨1149006, by rfl⟩ : syracuseStep 12256069 = 2298013) B2298013
theorem B2122577 : Blo 1413526 2122577 := bstep (se 2 (by rfl) ⟨795966, by rfl⟩ : syracuseStep 2122577 = 1591933) B1591933
theorem B4776785 : Blo 1413526 4776785 := bstep (se 2 (by rfl) ⟨1791294, by rfl⟩ : syracuseStep 4776785 = 3582589) B3582589
theorem B2122595 : Blo 1413526 2122595 := bstep (se 1 (by rfl) ⟨1591946, by rfl⟩ : syracuseStep 2122595 = 3183893) B3183893
theorem B2122625 : Blo 1413526 2122625 := bstep (se 2 (by rfl) ⟨795984, by rfl⟩ : syracuseStep 2122625 = 1591969) B1591969
theorem B2122643 : Blo 1413526 2122643 := bstep (se 1 (by rfl) ⟨1591982, by rfl⟩ : syracuseStep 2122643 = 3183965) B3183965
theorem B2122673 : Blo 1413526 2122673 := bstep (se 2 (by rfl) ⟨796002, by rfl⟩ : syracuseStep 2122673 = 1592005) B1592005
theorem B2122691 : Blo 1413526 2122691 := bstep (se 1 (by rfl) ⟨1592018, by rfl⟩ : syracuseStep 2122691 = 3184037) B3184037
theorem B3400643 : Blo 1413526 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B2122721 : Blo 1413526 2122721 := bstep (se 2 (by rfl) ⟨796020, by rfl⟩ : syracuseStep 2122721 = 1592041) B1592041
theorem B6038513 : Blo 1413526 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B1590259 : Blo 1413526 1590259 := bstep (se 1 (by rfl) ⟨1192694, by rfl⟩ : syracuseStep 1590259 = 2385389) B2385389
theorem B2122739 : Blo 1413526 2122739 := bstep (se 1 (by rfl) ⟨1592054, by rfl⟩ : syracuseStep 2122739 = 3184109) B3184109
theorem B2548739 : Blo 1413526 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B2122769 : Blo 1413526 2122769 := bstep (se 2 (by rfl) ⟨796038, by rfl⟩ : syracuseStep 2122769 = 1592077) B1592077
theorem B2122787 : Blo 1413526 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B2122817 : Blo 1413526 2122817 := bstep (se 2 (by rfl) ⟨796056, by rfl⟩ : syracuseStep 2122817 = 1592113) B1592113
theorem B2122835 : Blo 1413526 2122835 := bstep (se 1 (by rfl) ⟨1592126, by rfl⟩ : syracuseStep 2122835 = 3184253) B3184253
theorem B2122865 : Blo 1413526 2122865 := bstep (se 2 (by rfl) ⟨796074, by rfl⟩ : syracuseStep 2122865 = 1592149) B1592149
theorem B1590403 : Blo 1413526 1590403 := bstep (se 1 (by rfl) ⟨1192802, by rfl⟩ : syracuseStep 1590403 = 2385605) B2385605
theorem B2122883 : Blo 1413526 2122883 := bstep (se 1 (by rfl) ⟨1592162, by rfl⟩ : syracuseStep 2122883 = 3184325) B3184325
theorem B10192013 : Blo 1413526 10192013 := bstep (se 3 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 10192013 = 3822005) B3822005
theorem B8053901 : Blo 1413526 8053901 := bstep (se 3 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 8053901 = 3020213) B3020213
theorem B2122913 : Blo 1413526 2122913 := bstep (se 2 (by rfl) ⟨796092, by rfl⟩ : syracuseStep 2122913 = 1592185) B1592185
theorem B2122931 : Blo 1413526 2122931 := bstep (se 1 (by rfl) ⟨1592198, by rfl⟩ : syracuseStep 2122931 = 3184397) B3184397
theorem B2122961 : Blo 1413526 2122961 := bstep (se 2 (by rfl) ⟨796110, by rfl⟩ : syracuseStep 2122961 = 1592221) B1592221
theorem B2122979 : Blo 1413526 2122979 := bstep (se 1 (by rfl) ⟨1592234, by rfl⟩ : syracuseStep 2122979 = 3184469) B3184469
theorem B2123009 : Blo 1413526 2123009 := bstep (se 2 (by rfl) ⟨796128, by rfl⟩ : syracuseStep 2123009 = 1592257) B1592257
theorem B1590547 : Blo 1413526 1590547 := bstep (se 1 (by rfl) ⟨1192910, by rfl⟩ : syracuseStep 1590547 = 2385821) B2385821
theorem B2123027 : Blo 1413526 2123027 := bstep (se 1 (by rfl) ⟨1592270, by rfl⟩ : syracuseStep 2123027 = 3184541) B3184541
theorem B2123057 : Blo 1413526 2123057 := bstep (se 2 (by rfl) ⟨796146, by rfl⟩ : syracuseStep 2123057 = 1592293) B1592293
theorem B2123075 : Blo 1413526 2123075 := bstep (se 1 (by rfl) ⟨1592306, by rfl⟩ : syracuseStep 2123075 = 3184613) B3184613
theorem B2123105 : Blo 1413526 2123105 := bstep (se 2 (by rfl) ⟨796164, by rfl⟩ : syracuseStep 2123105 = 1592329) B1592329
theorem B4777325 : Blo 1413526 4777325 := bstep (se 3 (by rfl) ⟨895748, by rfl⟩ : syracuseStep 4777325 = 1791497) B1791497
theorem B2123123 : Blo 1413526 2123123 := bstep (se 1 (by rfl) ⟨1592342, by rfl⟩ : syracuseStep 2123123 = 3184685) B3184685
theorem B4531601 : Blo 1413526 4531601 := bstep (se 2 (by rfl) ⟨1699350, by rfl⟩ : syracuseStep 4531601 = 3398701) B3398701
theorem B2123153 : Blo 1413526 2123153 := bstep (se 2 (by rfl) ⟨796182, by rfl⟩ : syracuseStep 2123153 = 1592365) B1592365
theorem B1590691 : Blo 1413526 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B2123171 : Blo 1413526 2123171 := bstep (se 1 (by rfl) ⟨1592378, by rfl⟩ : syracuseStep 2123171 = 3184757) B3184757
theorem B4777379 : Blo 1413526 4777379 := bstep (se 1 (by rfl) ⟨3583034, by rfl⟩ : syracuseStep 4777379 = 7166069) B7166069
theorem B2123201 : Blo 1413526 2123201 := bstep (se 2 (by rfl) ⟨796200, by rfl⟩ : syracuseStep 2123201 = 1592401) B1592401
theorem B2123219 : Blo 1413526 2123219 := bstep (se 1 (by rfl) ⟨1592414, by rfl⟩ : syracuseStep 2123219 = 3184829) B3184829
theorem B2123249 : Blo 1413526 2123249 := bstep (se 2 (by rfl) ⟨796218, by rfl⟩ : syracuseStep 2123249 = 1592437) B1592437
theorem B2385409 : Blo 1413526 2385409 := bstep (se 2 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 2385409 = 1789057) B1789057
theorem B2123267 : Blo 1413526 2123267 := bstep (se 1 (by rfl) ⟨1592450, by rfl⟩ : syracuseStep 2123267 = 3184901) B3184901
theorem B2385443 : Blo 1413526 2385443 := bstep (se 1 (by rfl) ⟨1789082, by rfl⟩ : syracuseStep 2385443 = 3578165) B3578165
theorem B1590835 : Blo 1413526 1590835 := bstep (se 1 (by rfl) ⟨1193126, by rfl⟩ : syracuseStep 1590835 = 2386253) B2386253
theorem B18114101 : Blo 1413526 18114101 := bstep (se 5 (by rfl) ⟨849098, by rfl⟩ : syracuseStep 18114101 = 1698197) B1698197
theorem B2549315 : Blo 1413526 2549315 := bstep (se 1 (by rfl) ⟨1911986, by rfl⟩ : syracuseStep 2549315 = 3823973) B3823973
theorem B4081283 : Blo 1413526 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B9676421 : Blo 1413526 9676421 := bstep (se 4 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 9676421 = 1814329) B1814329
theorem B2385571 : Blo 1413526 2385571 := bstep (se 1 (by rfl) ⟨1789178, by rfl⟩ : syracuseStep 2385571 = 3578357) B3578357
theorem B3581617 : Blo 1413526 3581617 := bstep (se 2 (by rfl) ⟨1343106, by rfl⟩ : syracuseStep 3581617 = 2686213) B2686213
theorem B1590979 : Blo 1413526 1590979 := bstep (se 1 (by rfl) ⟨1193234, by rfl⟩ : syracuseStep 1590979 = 2386469) B2386469
theorem B2385713 : Blo 1413526 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B6211405 : Blo 1413526 6211405 := bstep (se 3 (by rfl) ⟨1164638, by rfl⟩ : syracuseStep 6211405 = 2329277) B2329277
theorem B1591123 : Blo 1413526 1591123 := bstep (se 1 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 1591123 = 2386685) B2386685
theorem B2549603 : Blo 1413526 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B2418545 : Blo 1413526 2418545 := bstep (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) B1813909
theorem B2385841 : Blo 1413526 2385841 := bstep (se 2 (by rfl) ⟨894690, by rfl⟩ : syracuseStep 2385841 = 1789381) B1789381
theorem B3581891 : Blo 1413526 3581891 := bstep (se 1 (by rfl) ⟨2686418, by rfl⟩ : syracuseStep 3581891 = 5372837) B5372837
theorem B2385875 : Blo 1413526 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B5367779 : Blo 1413526 5367779 := bstep (se 1 (by rfl) ⟨4025834, by rfl⟩ : syracuseStep 5367779 = 8051669) B8051669
theorem B1591267 : Blo 1413526 1591267 := bstep (se 1 (by rfl) ⟨1193450, by rfl⟩ : syracuseStep 1591267 = 2386901) B2386901
theorem B3876835 : Blo 1413526 3876835 := bstep (se 1 (by rfl) ⟨2907626, by rfl⟩ : syracuseStep 3876835 = 5815253) B5815253
theorem B14526533 : Blo 1413526 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B2386003 : Blo 1413526 2386003 := bstep (se 1 (by rfl) ⟨1789502, by rfl⟩ : syracuseStep 2386003 = 3579005) B3579005
theorem B1591411 : Blo 1413526 1591411 := bstep (se 1 (by rfl) ⟨1193558, by rfl⟩ : syracuseStep 1591411 = 2387117) B2387117
theorem B3582083 : Blo 1413526 3582083 := bstep (se 1 (by rfl) ⟨2686562, by rfl⟩ : syracuseStep 3582083 = 5373125) B5373125
theorem B3180689 : Blo 1413526 3180689 := bstep (se 2 (by rfl) ⟨1192758, by rfl⟩ : syracuseStep 3180689 = 2385517) B2385517
theorem B3180707 : Blo 1413526 3180707 := bstep (se 1 (by rfl) ⟨2385530, by rfl⟩ : syracuseStep 3180707 = 4771061) B4771061
theorem B9062563 : Blo 1413526 9062563 := bstep (se 1 (by rfl) ⟨6796922, by rfl⟩ : syracuseStep 9062563 = 13593845) B13593845
theorem B7162019 : Blo 1413526 7162019 := bstep (se 1 (by rfl) ⟨5371514, by rfl⟩ : syracuseStep 7162019 = 10743029) B10743029
theorem B2386145 : Blo 1413526 2386145 := bstep (se 2 (by rfl) ⟨894804, by rfl⟩ : syracuseStep 2386145 = 1789609) B1789609
theorem B1591555 : Blo 1413526 1591555 := bstep (se 1 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 1591555 = 2387333) B2387333
theorem B2386273 : Blo 1413526 2386273 := bstep (se 2 (by rfl) ⟨894852, by rfl⟩ : syracuseStep 2386273 = 1789705) B1789705
theorem B2386307 : Blo 1413526 2386307 := bstep (se 1 (by rfl) ⟨1789730, by rfl⟩ : syracuseStep 2386307 = 3579461) B3579461
theorem B1591699 : Blo 1413526 1591699 := bstep (se 1 (by rfl) ⟨1193774, by rfl⟩ : syracuseStep 1591699 = 2387549) B2387549
theorem B3180977 : Blo 1413526 3180977 := bstep (se 2 (by rfl) ⟨1192866, by rfl⟩ : syracuseStep 3180977 = 2385733) B2385733
theorem B3180995 : Blo 1413526 3180995 := bstep (se 1 (by rfl) ⟨2385746, by rfl⟩ : syracuseStep 3180995 = 4771493) B4771493
theorem B2386435 : Blo 1413526 2386435 := bstep (se 1 (by rfl) ⟨1789826, by rfl⟩ : syracuseStep 2386435 = 3579653) B3579653
theorem B1591843 : Blo 1413526 1591843 := bstep (se 1 (by rfl) ⟨1193882, by rfl⟩ : syracuseStep 1591843 = 2387765) B2387765
theorem B2386577 : Blo 1413526 2386577 := bstep (se 2 (by rfl) ⟨894966, by rfl⟩ : syracuseStep 2386577 = 1789933) B1789933
theorem B1591987 : Blo 1413526 1591987 := bstep (se 1 (by rfl) ⟨1193990, by rfl⟩ : syracuseStep 1591987 = 2387981) B2387981
theorem B3181265 : Blo 1413526 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B3181283 : Blo 1413526 3181283 := bstep (se 1 (by rfl) ⟨2385962, by rfl⟩ : syracuseStep 3181283 = 4771925) B4771925
theorem B18123533 : Blo 1413526 18123533 := bstep (se 3 (by rfl) ⟨3398162, by rfl⟩ : syracuseStep 18123533 = 6796325) B6796325
theorem B2386705 : Blo 1413526 2386705 := bstep (se 2 (by rfl) ⟨895014, by rfl⟩ : syracuseStep 2386705 = 1790029) B1790029
theorem B2386739 : Blo 1413526 2386739 := bstep (se 1 (by rfl) ⟨1790054, by rfl⟩ : syracuseStep 2386739 = 3580109) B3580109
theorem B1592131 : Blo 1413526 1592131 := bstep (se 1 (by rfl) ⟨1194098, by rfl⟩ : syracuseStep 1592131 = 2388197) B2388197
theorem B4590445 : Blo 1413526 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B4770737 : Blo 1413526 4770737 := bstep (se 2 (by rfl) ⟨1789026, by rfl⟩ : syracuseStep 4770737 = 3578053) B3578053
theorem B2386867 : Blo 1413526 2386867 := bstep (se 1 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 2386867 = 3580301) B3580301
theorem B5368781 : Blo 1413526 5368781 := bstep (se 3 (by rfl) ⟨1006646, by rfl⟩ : syracuseStep 5368781 = 2013293) B2013293
theorem B7162829 : Blo 1413526 7162829 := bstep (se 3 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 7162829 = 2686061) B2686061
theorem B1592275 : Blo 1413526 1592275 := bstep (se 1 (by rfl) ⟨1194206, by rfl⟩ : syracuseStep 1592275 = 2388413) B2388413
theorem B3181553 : Blo 1413526 3181553 := bstep (se 2 (by rfl) ⟨1193082, by rfl⟩ : syracuseStep 3181553 = 2386165) B2386165
theorem B3181571 : Blo 1413526 3181571 := bstep (se 1 (by rfl) ⟨2386178, by rfl⟩ : syracuseStep 3181571 = 4772357) B4772357
theorem B8162309 : Blo 1413526 8162309 := bstep (se 4 (by rfl) ⟨765216, by rfl⟩ : syracuseStep 8162309 = 1530433) B1530433
theorem B1698851 : Blo 1413526 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B3583025 : Blo 1413526 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B2387009 : Blo 1413526 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B5737549 : Blo 1413526 5737549 := bstep (se 3 (by rfl) ⟨1075790, by rfl⟩ : syracuseStep 5737549 = 2151581) B2151581
theorem B1592419 : Blo 1413526 1592419 := bstep (se 1 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 1592419 = 2388629) B2388629
theorem B6540401 : Blo 1413526 6540401 := bstep (se 2 (by rfl) ⟨2452650, by rfl⟩ : syracuseStep 6540401 = 4905301) B4905301
theorem B2387137 : Blo 1413526 2387137 := bstep (se 2 (by rfl) ⟨895176, by rfl⟩ : syracuseStep 2387137 = 1790353) B1790353
theorem B1789123 : Blo 1413526 1789123 := bstep (se 1 (by rfl) ⟨1341842, by rfl⟩ : syracuseStep 1789123 = 2683685) B2683685
theorem B2387171 : Blo 1413526 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B3181841 : Blo 1413526 3181841 := bstep (se 2 (by rfl) ⟨1193190, by rfl⟩ : syracuseStep 3181841 = 2386381) B2386381
theorem B1789219 : Blo 1413526 1789219 := bstep (se 1 (by rfl) ⟨1341914, by rfl⟩ : syracuseStep 1789219 = 2683829) B2683829
theorem B3181859 : Blo 1413526 3181859 := bstep (se 1 (by rfl) ⟨2386394, by rfl⟩ : syracuseStep 3181859 = 4772789) B4772789
theorem B2264417 : Blo 1413526 2264417 := bstep (se 2 (by rfl) ⟨849156, by rfl⟩ : syracuseStep 2264417 = 1698313) B1698313
theorem B2387299 : Blo 1413526 2387299 := bstep (se 1 (by rfl) ⟨1790474, by rfl⟩ : syracuseStep 2387299 = 3580949) B3580949
theorem B6040973 : Blo 1413526 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B5737891 : Blo 1413526 5737891 := bstep (se 1 (by rfl) ⟨4303418, by rfl⟩ : syracuseStep 5737891 = 8606837) B8606837
theorem B4771277 : Blo 1413526 4771277 := bstep (se 3 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 4771277 = 1789229) B1789229
theorem B2264545 : Blo 1413526 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B2387441 : Blo 1413526 2387441 := bstep (se 2 (by rfl) ⟨895290, by rfl⟩ : syracuseStep 2387441 = 1790581) B1790581
theorem B8170993 : Blo 1413526 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B4771331 : Blo 1413526 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B3182129 : Blo 1413526 3182129 := bstep (se 2 (by rfl) ⟨1193298, by rfl⟩ : syracuseStep 3182129 = 2386597) B2386597
theorem B3182147 : Blo 1413526 3182147 := bstep (se 1 (by rfl) ⟨2386610, by rfl⟩ : syracuseStep 3182147 = 4773221) B4773221
theorem B12906053 : Blo 1413526 12906053 := bstep (se 4 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 12906053 = 2419885) B2419885
theorem B4836977 : Blo 1413526 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B2387569 : Blo 1413526 2387569 := bstep (se 2 (by rfl) ⟨895338, by rfl⟩ : syracuseStep 2387569 = 1790677) B1790677
theorem B2387603 : Blo 1413526 2387603 := bstep (se 1 (by rfl) ⟨1790702, by rfl⟩ : syracuseStep 2387603 = 3581405) B3581405
theorem B2297521 : Blo 1413526 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B4771601 : Blo 1413526 4771601 := bstep (se 2 (by rfl) ⟨1789350, by rfl⟩ : syracuseStep 4771601 = 3578701) B3578701
theorem B1789715 : Blo 1413526 1789715 := bstep (se 1 (by rfl) ⟨1342286, by rfl⟩ : syracuseStep 1789715 = 2684573) B2684573
theorem B2387731 : Blo 1413526 2387731 := bstep (se 1 (by rfl) ⟨1790798, by rfl⟩ : syracuseStep 2387731 = 3581597) B3581597
theorem B4534061 : Blo 1413526 4534061 := bstep (se 3 (by rfl) ⟨850136, by rfl⟩ : syracuseStep 4534061 = 1700273) B1700273
theorem B3182417 : Blo 1413526 3182417 := bstep (se 2 (by rfl) ⟨1193406, by rfl⟩ : syracuseStep 3182417 = 2386813) B2386813
theorem B1912673 : Blo 1413526 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B3182435 : Blo 1413526 3182435 := bstep (se 1 (by rfl) ⟨2386826, by rfl⟩ : syracuseStep 3182435 = 4773653) B4773653
theorem B4026257 : Blo 1413526 4026257 := bstep (se 2 (by rfl) ⟨1509846, by rfl⟩ : syracuseStep 4026257 = 3019693) B3019693
theorem B2387873 : Blo 1413526 2387873 := bstep (se 2 (by rfl) ⟨895452, by rfl⟩ : syracuseStep 2387873 = 1790905) B1790905
theorem B15290309 : Blo 1413526 15290309 := bstep (se 4 (by rfl) ⟨1433466, by rfl⟩ : syracuseStep 15290309 = 2866933) B2866933
theorem B8056817 : Blo 1413526 8056817 := bstep (se 2 (by rfl) ⟨3021306, by rfl⟩ : syracuseStep 8056817 = 6042613) B6042613
theorem B2388001 : Blo 1413526 2388001 := bstep (se 2 (by rfl) ⟨895500, by rfl⟩ : syracuseStep 2388001 = 1791001) B1791001
theorem B2388035 : Blo 1413526 2388035 := bstep (se 1 (by rfl) ⟨1791026, by rfl⟩ : syracuseStep 2388035 = 3582053) B3582053
theorem B4026449 : Blo 1413526 4026449 := bstep (se 2 (by rfl) ⟨1509918, by rfl⟩ : syracuseStep 4026449 = 3019837) B3019837
theorem B3821681 : Blo 1413526 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B3182705 : Blo 1413526 3182705 := bstep (se 2 (by rfl) ⟨1193514, by rfl⟩ : syracuseStep 3182705 = 2387029) B2387029
theorem B3182723 : Blo 1413526 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B30568589 : Blo 1413526 30568589 := bstep (se 3 (by rfl) ⟨5731610, by rfl⟩ : syracuseStep 30568589 = 11463221) B11463221
theorem B2388163 : Blo 1413526 2388163 := bstep (se 1 (by rfl) ⟨1791122, by rfl⟩ : syracuseStep 2388163 = 3582245) B3582245
theorem B24170723 : Blo 1413526 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B4772141 : Blo 1413526 4772141 := bstep (se 3 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 4772141 = 1789553) B1789553
theorem B2388305 : Blo 1413526 2388305 := bstep (se 2 (by rfl) ⟨895614, by rfl⟩ : syracuseStep 2388305 = 1791229) B1791229
theorem B4772195 : Blo 1413526 4772195 := bstep (se 1 (by rfl) ⟨3579146, by rfl⟩ : syracuseStep 4772195 = 7158293) B7158293
theorem B3182993 : Blo 1413526 3182993 := bstep (se 2 (by rfl) ⟨1193622, by rfl⟩ : syracuseStep 3182993 = 2387245) B2387245
theorem B1413539 : Blo 1413526 1413539 := bstep (se 1 (by rfl) ⟨1060154, by rfl⟩ : syracuseStep 1413539 = 2120309) B2120309
theorem B3183011 : Blo 1413526 3183011 := bstep (se 1 (by rfl) ⟨2387258, by rfl⟩ : syracuseStep 3183011 = 4774517) B4774517
theorem B1413555 : Blo 1413526 1413555 := bstep (se 1 (by rfl) ⟨1060166, by rfl⟩ : syracuseStep 1413555 = 2120333) B2120333
theorem B1413571 : Blo 1413526 1413571 := bstep (se 1 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 1413571 = 2120357) B2120357
theorem B2388433 : Blo 1413526 2388433 := bstep (se 2 (by rfl) ⟨895662, by rfl⟩ : syracuseStep 2388433 = 1791325) B1791325
theorem B1413587 : Blo 1413526 1413587 := bstep (se 1 (by rfl) ⟨1060190, by rfl⟩ : syracuseStep 1413587 = 2120381) B2120381
theorem B1790419 : Blo 1413526 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B1413603 : Blo 1413526 1413603 := bstep (se 1 (by rfl) ⟨1060202, by rfl⟩ : syracuseStep 1413603 = 2120405) B2120405
theorem B1413619 : Blo 1413526 1413619 := bstep (se 1 (by rfl) ⟨1060214, by rfl⟩ : syracuseStep 1413619 = 2120429) B2120429
theorem B2388467 : Blo 1413526 2388467 := bstep (se 1 (by rfl) ⟨1791350, by rfl⟩ : syracuseStep 2388467 = 3582701) B3582701
theorem B1413635 : Blo 1413526 1413635 := bstep (se 1 (by rfl) ⟨1060226, by rfl⟩ : syracuseStep 1413635 = 2120453) B2120453
theorem B1413651 : Blo 1413526 1413651 := bstep (se 1 (by rfl) ⟨1060238, by rfl⟩ : syracuseStep 1413651 = 2120477) B2120477
theorem B1413667 : Blo 1413526 1413667 := bstep (se 1 (by rfl) ⟨1060250, by rfl⟩ : syracuseStep 1413667 = 2120501) B2120501
theorem B1413683 : Blo 1413526 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B1790515 : Blo 1413526 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B1413699 : Blo 1413526 1413699 := bstep (se 1 (by rfl) ⟨1060274, by rfl⟩ : syracuseStep 1413699 = 2120549) B2120549
theorem B1413715 : Blo 1413526 1413715 := bstep (se 1 (by rfl) ⟨1060286, by rfl⟩ : syracuseStep 1413715 = 2120573) B2120573
theorem B1413731 : Blo 1413526 1413731 := bstep (se 1 (by rfl) ⟨1060298, by rfl⟩ : syracuseStep 1413731 = 2120597) B2120597
theorem B4772465 : Blo 1413526 4772465 := bstep (se 2 (by rfl) ⟨1789674, by rfl⟩ : syracuseStep 4772465 = 3579349) B3579349
theorem B1413747 : Blo 1413526 1413747 := bstep (se 1 (by rfl) ⟨1060310, by rfl⟩ : syracuseStep 1413747 = 2120621) B2120621
theorem B2388595 : Blo 1413526 2388595 := bstep (se 1 (by rfl) ⟨1791446, by rfl⟩ : syracuseStep 2388595 = 3582893) B3582893
theorem B1413763 : Blo 1413526 1413763 := bstep (se 1 (by rfl) ⟨1060322, by rfl⟩ : syracuseStep 1413763 = 2120645) B2120645
theorem B1413779 : Blo 1413526 1413779 := bstep (se 1 (by rfl) ⟨1060334, by rfl⟩ : syracuseStep 1413779 = 2120669) B2120669
theorem B1413795 : Blo 1413526 1413795 := bstep (se 1 (by rfl) ⟨1060346, by rfl⟩ : syracuseStep 1413795 = 2120693) B2120693
theorem B3183281 : Blo 1413526 3183281 := bstep (se 2 (by rfl) ⟨1193730, by rfl⟩ : syracuseStep 3183281 = 2387461) B2387461
theorem B1413811 : Blo 1413526 1413811 := bstep (se 1 (by rfl) ⟨1060358, by rfl⟩ : syracuseStep 1413811 = 2120717) B2120717
theorem B1413827 : Blo 1413526 1413827 := bstep (se 1 (by rfl) ⟨1060370, by rfl⟩ : syracuseStep 1413827 = 2120741) B2120741
theorem B3183299 : Blo 1413526 3183299 := bstep (se 1 (by rfl) ⟨2387474, by rfl⟩ : syracuseStep 3183299 = 4774949) B4774949
theorem B2683601 : Blo 1413526 2683601 := bstep (se 2 (by rfl) ⟨1006350, by rfl⟩ : syracuseStep 2683601 = 2012701) B2012701
theorem B1413843 : Blo 1413526 1413843 := bstep (se 1 (by rfl) ⟨1060382, by rfl⟩ : syracuseStep 1413843 = 2120765) B2120765
theorem B1413859 : Blo 1413526 1413859 := bstep (se 1 (by rfl) ⟨1060394, by rfl⟩ : syracuseStep 1413859 = 2120789) B2120789
theorem B2757361 : Blo 1413526 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B1413875 : Blo 1413526 1413875 := bstep (se 1 (by rfl) ⟨1060406, by rfl⟩ : syracuseStep 1413875 = 2120813) B2120813
theorem B1413891 : Blo 1413526 1413891 := bstep (se 1 (by rfl) ⟨1060418, by rfl⟩ : syracuseStep 1413891 = 2120837) B2120837
theorem B1413907 : Blo 1413526 1413907 := bstep (se 1 (by rfl) ⟨1060430, by rfl⟩ : syracuseStep 1413907 = 2120861) B2120861
theorem B1413923 : Blo 1413526 1413923 := bstep (se 1 (by rfl) ⟨1060442, by rfl⟩ : syracuseStep 1413923 = 2120885) B2120885
theorem B1413939 : Blo 1413526 1413939 := bstep (se 1 (by rfl) ⟨1060454, by rfl⟩ : syracuseStep 1413939 = 2120909) B2120909
theorem B1413955 : Blo 1413526 1413955 := bstep (se 1 (by rfl) ⟨1060466, by rfl⟩ : syracuseStep 1413955 = 2120933) B2120933
theorem B1413971 : Blo 1413526 1413971 := bstep (se 1 (by rfl) ⟨1060478, by rfl⟩ : syracuseStep 1413971 = 2120957) B2120957
theorem B1413987 : Blo 1413526 1413987 := bstep (se 1 (by rfl) ⟨1060490, by rfl⟩ : syracuseStep 1413987 = 2120981) B2120981
theorem B1414003 : Blo 1413526 1414003 := bstep (se 1 (by rfl) ⟨1060502, by rfl⟩ : syracuseStep 1414003 = 2121005) B2121005
theorem B1414019 : Blo 1413526 1414019 := bstep (se 1 (by rfl) ⟨1060514, by rfl⟩ : syracuseStep 1414019 = 2121029) B2121029
theorem B9065357 : Blo 1413526 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B1414035 : Blo 1413526 1414035 := bstep (se 1 (by rfl) ⟨1060526, by rfl⟩ : syracuseStep 1414035 = 2121053) B2121053
theorem B1414051 : Blo 1413526 1414051 := bstep (se 1 (by rfl) ⟨1060538, by rfl⟩ : syracuseStep 1414051 = 2121077) B2121077
theorem B6042545 : Blo 1413526 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B1414067 : Blo 1413526 1414067 := bstep (se 1 (by rfl) ⟨1060550, by rfl⟩ : syracuseStep 1414067 = 2121101) B2121101
theorem B1414083 : Blo 1413526 1414083 := bstep (se 1 (by rfl) ⟨1060562, by rfl⟩ : syracuseStep 1414083 = 2121125) B2121125
theorem B2266051 : Blo 1413526 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B3183569 : Blo 1413526 3183569 := bstep (se 2 (by rfl) ⟨1193838, by rfl⟩ : syracuseStep 3183569 = 2387677) B2387677
theorem B1414099 : Blo 1413526 1414099 := bstep (se 1 (by rfl) ⟨1060574, by rfl⟩ : syracuseStep 1414099 = 2121149) B2121149
theorem B1414115 : Blo 1413526 1414115 := bstep (se 1 (by rfl) ⟨1060586, by rfl⟩ : syracuseStep 1414115 = 2121173) B2121173
theorem B3183587 : Blo 1413526 3183587 := bstep (se 1 (by rfl) ⟨2387690, by rfl⟩ : syracuseStep 3183587 = 4775381) B4775381
theorem B1414131 : Blo 1413526 1414131 := bstep (se 1 (by rfl) ⟨1060598, by rfl⟩ : syracuseStep 1414131 = 2121197) B2121197
theorem B1414147 : Blo 1413526 1414147 := bstep (se 1 (by rfl) ⟨1060610, by rfl⟩ : syracuseStep 1414147 = 2121221) B2121221
theorem B5370893 : Blo 1413526 5370893 := bstep (se 3 (by rfl) ⟨1007042, by rfl⟩ : syracuseStep 5370893 = 2014085) B2014085
theorem B1414163 : Blo 1413526 1414163 := bstep (se 1 (by rfl) ⟨1060622, by rfl⟩ : syracuseStep 1414163 = 2121245) B2121245
theorem B1414179 : Blo 1413526 1414179 := bstep (se 1 (by rfl) ⟨1060634, by rfl⟩ : syracuseStep 1414179 = 2121269) B2121269
theorem B1791011 : Blo 1413526 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B4027441 : Blo 1413526 4027441 := bstep (se 2 (by rfl) ⟨1510290, by rfl⟩ : syracuseStep 4027441 = 3020581) B3020581
theorem B1414195 : Blo 1413526 1414195 := bstep (se 1 (by rfl) ⟨1060646, by rfl⟩ : syracuseStep 1414195 = 2121293) B2121293
theorem B1414211 : Blo 1413526 1414211 := bstep (se 1 (by rfl) ⟨1060658, by rfl⟩ : syracuseStep 1414211 = 2121317) B2121317
theorem B1414227 : Blo 1413526 1414227 := bstep (se 1 (by rfl) ⟨1060670, by rfl⟩ : syracuseStep 1414227 = 2121341) B2121341
theorem B7156835 : Blo 1413526 7156835 := bstep (se 1 (by rfl) ⟨5367626, by rfl⟩ : syracuseStep 7156835 = 10735253) B10735253
theorem B1414243 : Blo 1413526 1414243 := bstep (se 1 (by rfl) ⟨1060682, by rfl⟩ : syracuseStep 1414243 = 2121365) B2121365
theorem B1414259 : Blo 1413526 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B1414275 : Blo 1413526 1414275 := bstep (se 1 (by rfl) ⟨1060706, by rfl⟩ : syracuseStep 1414275 = 2121413) B2121413
theorem B4773005 : Blo 1413526 4773005 := bstep (se 3 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 4773005 = 1789877) B1789877
theorem B10744973 : Blo 1413526 10744973 := bstep (se 3 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 10744973 = 4029365) B4029365
theorem B1414291 : Blo 1413526 1414291 := bstep (se 1 (by rfl) ⟨1060718, by rfl⟩ : syracuseStep 1414291 = 2121437) B2121437
theorem B1414307 : Blo 1413526 1414307 := bstep (se 1 (by rfl) ⟨1060730, by rfl⟩ : syracuseStep 1414307 = 2121461) B2121461
theorem B1414323 : Blo 1413526 1414323 := bstep (se 1 (by rfl) ⟨1060742, by rfl⟩ : syracuseStep 1414323 = 2121485) B2121485
theorem B4773059 : Blo 1413526 4773059 := bstep (se 1 (by rfl) ⟨3579794, by rfl⟩ : syracuseStep 4773059 = 7159589) B7159589
theorem B1414339 : Blo 1413526 1414339 := bstep (se 1 (by rfl) ⟨1060754, by rfl⟩ : syracuseStep 1414339 = 2121509) B2121509
theorem B1414355 : Blo 1413526 1414355 := bstep (se 1 (by rfl) ⟨1060766, by rfl⟩ : syracuseStep 1414355 = 2121533) B2121533
theorem B1414371 : Blo 1413526 1414371 := bstep (se 1 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 1414371 = 2121557) B2121557
theorem B3183857 : Blo 1413526 3183857 := bstep (se 2 (by rfl) ⟨1193946, by rfl⟩ : syracuseStep 3183857 = 2387893) B2387893
theorem B1414387 : Blo 1413526 1414387 := bstep (se 1 (by rfl) ⟨1060790, by rfl⟩ : syracuseStep 1414387 = 2121581) B2121581
theorem B1414403 : Blo 1413526 1414403 := bstep (se 1 (by rfl) ⟨1060802, by rfl⟩ : syracuseStep 1414403 = 2121605) B2121605
theorem B3183875 : Blo 1413526 3183875 := bstep (se 1 (by rfl) ⟨2387906, by rfl⟩ : syracuseStep 3183875 = 4775813) B4775813
theorem B1414419 : Blo 1413526 1414419 := bstep (se 1 (by rfl) ⟨1060814, by rfl⟩ : syracuseStep 1414419 = 2121629) B2121629
theorem B1414435 : Blo 1413526 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B1414451 : Blo 1413526 1414451 := bstep (se 1 (by rfl) ⟨1060838, by rfl⟩ : syracuseStep 1414451 = 2121677) B2121677
theorem B4027715 : Blo 1413526 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B1414467 : Blo 1413526 1414467 := bstep (se 1 (by rfl) ⟨1060850, by rfl⟩ : syracuseStep 1414467 = 2121701) B2121701
theorem B1414483 : Blo 1413526 1414483 := bstep (se 1 (by rfl) ⟨1060862, by rfl⟩ : syracuseStep 1414483 = 2121725) B2121725
theorem B1414499 : Blo 1413526 1414499 := bstep (se 1 (by rfl) ⟨1060874, by rfl⟩ : syracuseStep 1414499 = 2121749) B2121749
theorem B1414515 : Blo 1413526 1414515 := bstep (se 1 (by rfl) ⟨1060886, by rfl⟩ : syracuseStep 1414515 = 2121773) B2121773
theorem B1414531 : Blo 1413526 1414531 := bstep (se 1 (by rfl) ⟨1060898, by rfl⟩ : syracuseStep 1414531 = 2121797) B2121797
theorem B1414547 : Blo 1413526 1414547 := bstep (se 1 (by rfl) ⟨1060910, by rfl⟩ : syracuseStep 1414547 = 2121821) B2121821
theorem B1414563 : Blo 1413526 1414563 := bstep (se 1 (by rfl) ⟨1060922, by rfl⟩ : syracuseStep 1414563 = 2121845) B2121845
theorem B8058275 : Blo 1413526 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B1414579 : Blo 1413526 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B1414595 : Blo 1413526 1414595 := bstep (se 1 (by rfl) ⟨1060946, by rfl⟩ : syracuseStep 1414595 = 2121893) B2121893
theorem B4773329 : Blo 1413526 4773329 := bstep (se 2 (by rfl) ⟨1789998, by rfl⟩ : syracuseStep 4773329 = 3579997) B3579997
theorem B2012627 : Blo 1413526 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B1414611 : Blo 1413526 1414611 := bstep (se 1 (by rfl) ⟨1060958, by rfl⟩ : syracuseStep 1414611 = 2121917) B2121917
theorem B1414627 : Blo 1413526 1414627 := bstep (se 1 (by rfl) ⟨1060970, by rfl⟩ : syracuseStep 1414627 = 2121941) B2121941
theorem B1414643 : Blo 1413526 1414643 := bstep (se 1 (by rfl) ⟨1060982, by rfl⟩ : syracuseStep 1414643 = 2121965) B2121965
theorem B4027907 : Blo 1413526 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B1414659 : Blo 1413526 1414659 := bstep (se 1 (by rfl) ⟨1060994, by rfl⟩ : syracuseStep 1414659 = 2121989) B2121989
theorem B3184145 : Blo 1413526 3184145 := bstep (se 2 (by rfl) ⟨1194054, by rfl⟩ : syracuseStep 3184145 = 2388109) B2388109
theorem B1414675 : Blo 1413526 1414675 := bstep (se 1 (by rfl) ⟨1061006, by rfl⟩ : syracuseStep 1414675 = 2122013) B2122013
theorem B1414691 : Blo 1413526 1414691 := bstep (se 1 (by rfl) ⟨1061018, by rfl⟩ : syracuseStep 1414691 = 2122037) B2122037
theorem B3184163 : Blo 1413526 3184163 := bstep (se 1 (by rfl) ⟨2388122, by rfl⟩ : syracuseStep 3184163 = 4776245) B4776245
theorem B1414707 : Blo 1413526 1414707 := bstep (se 1 (by rfl) ⟨1061030, by rfl⟩ : syracuseStep 1414707 = 2122061) B2122061
theorem B1414723 : Blo 1413526 1414723 := bstep (se 1 (by rfl) ⟨1061042, by rfl⟩ : syracuseStep 1414723 = 2122085) B2122085
theorem B13588037 : Blo 1413526 13588037 := bstep (se 4 (by rfl) ⟨1273878, by rfl⟩ : syracuseStep 13588037 = 2547757) B2547757
theorem B6624845 : Blo 1413526 6624845 := bstep (se 3 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 6624845 = 2484317) B2484317
theorem B2684497 : Blo 1413526 2684497 := bstep (se 2 (by rfl) ⟨1006686, by rfl⟩ : syracuseStep 2684497 = 2013373) B2013373
theorem B1414739 : Blo 1413526 1414739 := bstep (se 1 (by rfl) ⟨1061054, by rfl⟩ : syracuseStep 1414739 = 2122109) B2122109
theorem B1414755 : Blo 1413526 1414755 := bstep (se 1 (by rfl) ⟨1061066, by rfl⟩ : syracuseStep 1414755 = 2122133) B2122133
theorem B2266723 : Blo 1413526 2266723 := bstep (se 1 (by rfl) ⟨1700042, by rfl⟩ : syracuseStep 2266723 = 3400085) B3400085
theorem B1414771 : Blo 1413526 1414771 := bstep (se 1 (by rfl) ⟨1061078, by rfl⟩ : syracuseStep 1414771 = 2122157) B2122157
theorem B1414787 : Blo 1413526 1414787 := bstep (se 1 (by rfl) ⟨1061090, by rfl⟩ : syracuseStep 1414787 = 2122181) B2122181
theorem B1414803 : Blo 1413526 1414803 := bstep (se 1 (by rfl) ⟨1061102, by rfl⟩ : syracuseStep 1414803 = 2122205) B2122205
theorem B1414819 : Blo 1413526 1414819 := bstep (se 1 (by rfl) ⟨1061114, by rfl⟩ : syracuseStep 1414819 = 2122229) B2122229
theorem B4839085 : Blo 1413526 4839085 := bstep (se 3 (by rfl) ⟨907328, by rfl⟩ : syracuseStep 4839085 = 1814657) B1814657
theorem B1414835 : Blo 1413526 1414835 := bstep (se 1 (by rfl) ⟨1061126, by rfl⟩ : syracuseStep 1414835 = 2122253) B2122253
theorem B1414851 : Blo 1413526 1414851 := bstep (se 1 (by rfl) ⟨1061138, by rfl⟩ : syracuseStep 1414851 = 2122277) B2122277
theorem B1414867 : Blo 1413526 1414867 := bstep (se 1 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 1414867 = 2122301) B2122301
theorem B1414883 : Blo 1413526 1414883 := bstep (se 1 (by rfl) ⟨1061162, by rfl⟩ : syracuseStep 1414883 = 2122325) B2122325
theorem B2684657 : Blo 1413526 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B1414899 : Blo 1413526 1414899 := bstep (se 1 (by rfl) ⟨1061174, by rfl⟩ : syracuseStep 1414899 = 2122349) B2122349
theorem B3225347 : Blo 1413526 3225347 := bstep (se 1 (by rfl) ⟨2419010, by rfl⟩ : syracuseStep 3225347 = 4838021) B4838021
theorem B1414915 : Blo 1413526 1414915 := bstep (se 1 (by rfl) ⟨1061186, by rfl⟩ : syracuseStep 1414915 = 2122373) B2122373
theorem B1414931 : Blo 1413526 1414931 := bstep (se 1 (by rfl) ⟨1061198, by rfl⟩ : syracuseStep 1414931 = 2122397) B2122397
theorem B45913877 : Blo 1413526 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B1414947 : Blo 1413526 1414947 := bstep (se 1 (by rfl) ⟨1061210, by rfl⟩ : syracuseStep 1414947 = 2122421) B2122421
theorem B5371697 : Blo 1413526 5371697 := bstep (se 2 (by rfl) ⟨2014386, by rfl⟩ : syracuseStep 5371697 = 4028773) B4028773
theorem B3184433 : Blo 1413526 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B1414963 : Blo 1413526 1414963 := bstep (se 1 (by rfl) ⟨1061222, by rfl⟩ : syracuseStep 1414963 = 2122445) B2122445
theorem B7165745 : Blo 1413526 7165745 := bstep (se 2 (by rfl) ⟨2687154, by rfl⟩ : syracuseStep 7165745 = 5374309) B5374309
theorem B1414979 : Blo 1413526 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B3184451 : Blo 1413526 3184451 := bstep (se 1 (by rfl) ⟨2388338, by rfl⟩ : syracuseStep 3184451 = 4776677) B4776677
theorem B1414995 : Blo 1413526 1414995 := bstep (se 1 (by rfl) ⟨1061246, by rfl⟩ : syracuseStep 1414995 = 2122493) B2122493
theorem B1415011 : Blo 1413526 1415011 := bstep (se 1 (by rfl) ⟨1061258, by rfl⟩ : syracuseStep 1415011 = 2122517) B2122517
theorem B3020657 : Blo 1413526 3020657 := bstep (se 2 (by rfl) ⟨1132746, by rfl⟩ : syracuseStep 3020657 = 2265493) B2265493
theorem B1415027 : Blo 1413526 1415027 := bstep (se 1 (by rfl) ⟨1061270, by rfl⟩ : syracuseStep 1415027 = 2122541) B2122541
theorem B1415043 : Blo 1413526 1415043 := bstep (se 1 (by rfl) ⟨1061282, by rfl⟩ : syracuseStep 1415043 = 2122565) B2122565
theorem B4085635 : Blo 1413526 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B7157645 : Blo 1413526 7157645 := bstep (se 3 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 7157645 = 2684117) B2684117
theorem B1415059 : Blo 1413526 1415059 := bstep (se 1 (by rfl) ⟨1061294, by rfl⟩ : syracuseStep 1415059 = 2122589) B2122589
theorem B1963937 : Blo 1413526 1963937 := bstep (se 2 (by rfl) ⟨736476, by rfl⟩ : syracuseStep 1963937 = 1472953) B1472953
theorem B1415075 : Blo 1413526 1415075 := bstep (se 1 (by rfl) ⟨1061306, by rfl⟩ : syracuseStep 1415075 = 2122613) B2122613
theorem B1415091 : Blo 1413526 1415091 := bstep (se 1 (by rfl) ⟨1061318, by rfl⟩ : syracuseStep 1415091 = 2122637) B2122637
theorem B1415107 : Blo 1413526 1415107 := bstep (se 1 (by rfl) ⟨1061330, by rfl⟩ : syracuseStep 1415107 = 2122661) B2122661
theorem B1415123 : Blo 1413526 1415123 := bstep (se 1 (by rfl) ⟨1061342, by rfl⟩ : syracuseStep 1415123 = 2122685) B2122685
theorem B1415139 : Blo 1413526 1415139 := bstep (se 1 (by rfl) ⟨1061354, by rfl⟩ : syracuseStep 1415139 = 2122709) B2122709
theorem B4773869 : Blo 1413526 4773869 := bstep (se 3 (by rfl) ⟨895100, by rfl⟩ : syracuseStep 4773869 = 1790201) B1790201
theorem B1415155 : Blo 1413526 1415155 := bstep (se 1 (by rfl) ⟨1061366, by rfl⟩ : syracuseStep 1415155 = 2122733) B2122733
theorem B1415171 : Blo 1413526 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B1415187 : Blo 1413526 1415187 := bstep (se 1 (by rfl) ⟨1061390, by rfl⟩ : syracuseStep 1415187 = 2122781) B2122781
theorem B4773923 : Blo 1413526 4773923 := bstep (se 1 (by rfl) ⟨3580442, by rfl⟩ : syracuseStep 4773923 = 7160885) B7160885
theorem B6453283 : Blo 1413526 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B1415203 : Blo 1413526 1415203 := bstep (se 1 (by rfl) ⟨1061402, by rfl⟩ : syracuseStep 1415203 = 2122805) B2122805
theorem B2267185 : Blo 1413526 2267185 := bstep (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) B1700389
theorem B1415219 : Blo 1413526 1415219 := bstep (se 1 (by rfl) ⟨1061414, by rfl⟩ : syracuseStep 1415219 = 2122829) B2122829
theorem B1415235 : Blo 1413526 1415235 := bstep (se 1 (by rfl) ⟨1061426, by rfl⟩ : syracuseStep 1415235 = 2122853) B2122853
theorem B2013265 : Blo 1413526 2013265 := bstep (se 2 (by rfl) ⟨754974, by rfl⟩ : syracuseStep 2013265 = 1509949) B1509949
theorem B3184721 : Blo 1413526 3184721 := bstep (se 2 (by rfl) ⟨1194270, by rfl⟩ : syracuseStep 3184721 = 2388541) B2388541
theorem B1415251 : Blo 1413526 1415251 := bstep (se 1 (by rfl) ⟨1061438, by rfl⟩ : syracuseStep 1415251 = 2122877) B2122877
theorem B17201251 : Blo 1413526 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B19626083 : Blo 1413526 19626083 := bstep (se 1 (by rfl) ⟨14719562, by rfl⟩ : syracuseStep 19626083 = 29439125) B29439125
theorem B1415267 : Blo 1413526 1415267 := bstep (se 1 (by rfl) ⟨1061450, by rfl⟩ : syracuseStep 1415267 = 2122901) B2122901
theorem B3184739 : Blo 1413526 3184739 := bstep (se 1 (by rfl) ⟨2388554, by rfl⟩ : syracuseStep 3184739 = 4777109) B4777109
theorem B1415283 : Blo 1413526 1415283 := bstep (se 1 (by rfl) ⟨1061462, by rfl⟩ : syracuseStep 1415283 = 2122925) B2122925
theorem B2685059 : Blo 1413526 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1415299 : Blo 1413526 1415299 := bstep (se 1 (by rfl) ⟨1061474, by rfl⟩ : syracuseStep 1415299 = 2122949) B2122949
theorem B3823757 : Blo 1413526 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B6453389 : Blo 1413526 6453389 := bstep (se 3 (by rfl) ⟨1210010, by rfl⟩ : syracuseStep 6453389 = 2420021) B2420021
theorem B2267281 : Blo 1413526 2267281 := bstep (se 2 (by rfl) ⟨850230, by rfl⟩ : syracuseStep 2267281 = 1700461) B1700461
theorem B1415315 : Blo 1413526 1415315 := bstep (se 1 (by rfl) ⟨1061486, by rfl⟩ : syracuseStep 1415315 = 2122973) B2122973
theorem B1415331 : Blo 1413526 1415331 := bstep (se 1 (by rfl) ⟨1061498, by rfl⟩ : syracuseStep 1415331 = 2122997) B2122997
theorem B3578033 : Blo 1413526 3578033 := bstep (se 2 (by rfl) ⟨1341762, by rfl⟩ : syracuseStep 3578033 = 2683525) B2683525
theorem B1415347 : Blo 1413526 1415347 := bstep (se 1 (by rfl) ⟨1061510, by rfl⟩ : syracuseStep 1415347 = 2123021) B2123021
theorem B1415363 : Blo 1413526 1415363 := bstep (se 1 (by rfl) ⟨1061522, by rfl⟩ : syracuseStep 1415363 = 2123045) B2123045
theorem B1415379 : Blo 1413526 1415379 := bstep (se 1 (by rfl) ⟨1061534, by rfl⟩ : syracuseStep 1415379 = 2123069) B2123069
theorem B1415395 : Blo 1413526 1415395 := bstep (se 1 (by rfl) ⟨1061546, by rfl⟩ : syracuseStep 1415395 = 2123093) B2123093
theorem B15284465 : Blo 1413526 15284465 := bstep (se 2 (by rfl) ⟨5731674, by rfl⟩ : syracuseStep 15284465 = 11463349) B11463349
theorem B1415411 : Blo 1413526 1415411 := bstep (se 1 (by rfl) ⟨1061558, by rfl⟩ : syracuseStep 1415411 = 2123117) B2123117
theorem B1415427 : Blo 1413526 1415427 := bstep (se 1 (by rfl) ⟨1061570, by rfl⟩ : syracuseStep 1415427 = 2123141) B2123141
theorem B12245261 : Blo 1413526 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B1415443 : Blo 1413526 1415443 := bstep (se 1 (by rfl) ⟨1061582, by rfl⟩ : syracuseStep 1415443 = 2123165) B2123165
theorem B1612067 : Blo 1413526 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B1415459 : Blo 1413526 1415459 := bstep (se 1 (by rfl) ⟨1061594, by rfl⟩ : syracuseStep 1415459 = 2123189) B2123189
theorem B4028717 : Blo 1413526 4028717 := bstep (se 3 (by rfl) ⟨755384, by rfl⟩ : syracuseStep 4028717 = 1510769) B1510769
theorem B4774193 : Blo 1413526 4774193 := bstep (se 2 (by rfl) ⟨1790322, by rfl⟩ : syracuseStep 4774193 = 3580645) B3580645
theorem B1415475 : Blo 1413526 1415475 := bstep (se 1 (by rfl) ⟨1061606, by rfl⟩ : syracuseStep 1415475 = 2123213) B2123213
theorem B1415491 : Blo 1413526 1415491 := bstep (se 1 (by rfl) ⟨1061618, by rfl⟩ : syracuseStep 1415491 = 2123237) B2123237
theorem B1415507 : Blo 1413526 1415507 := bstep (se 1 (by rfl) ⟨1061630, by rfl⟩ : syracuseStep 1415507 = 2123261) B2123261
theorem B1415523 : Blo 1413526 1415523 := bstep (se 1 (by rfl) ⟨1061642, by rfl⟩ : syracuseStep 1415523 = 2123285) B2123285
theorem B32676209 : Blo 1413526 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B8059277 : Blo 1413526 8059277 := bstep (se 3 (by rfl) ⟨1511114, by rfl⟩ : syracuseStep 8059277 = 3022229) B3022229
theorem B2013601 : Blo 1413526 2013601 := bstep (se 2 (by rfl) ⟨755100, by rfl⟩ : syracuseStep 2013601 = 1510201) B1510201
theorem B5372365 : Blo 1413526 5372365 := bstep (se 3 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 5372365 = 2014637) B2014637
theorem B4028899 : Blo 1413526 4028899 := bstep (se 1 (by rfl) ⟨3021674, by rfl⟩ : syracuseStep 4028899 = 6043349) B6043349
theorem B2120291 : Blo 1413526 2120291 := bstep (se 1 (by rfl) ⟨1590218, by rfl⟩ : syracuseStep 2120291 = 3180437) B3180437
theorem B2120321 : Blo 1413526 2120321 := bstep (se 2 (by rfl) ⟨795120, by rfl⟩ : syracuseStep 2120321 = 1590241) B1590241
theorem B9058949 : Blo 1413526 9058949 := bstep (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) B1698553
theorem B2120339 : Blo 1413526 2120339 := bstep (se 1 (by rfl) ⟨1590254, by rfl⟩ : syracuseStep 2120339 = 3180509) B3180509
theorem B2120369 : Blo 1413526 2120369 := bstep (se 2 (by rfl) ⟨795138, by rfl⟩ : syracuseStep 2120369 = 1590277) B1590277
theorem B2120387 : Blo 1413526 2120387 := bstep (se 1 (by rfl) ⟨1590290, by rfl⟩ : syracuseStep 2120387 = 3180581) B3180581
theorem B2120417 : Blo 1413526 2120417 := bstep (se 2 (by rfl) ⟨795156, by rfl⟩ : syracuseStep 2120417 = 1590313) B1590313
theorem B2120435 : Blo 1413526 2120435 := bstep (se 1 (by rfl) ⟨1590326, by rfl⟩ : syracuseStep 2120435 = 3180653) B3180653
theorem B2120465 : Blo 1413526 2120465 := bstep (se 2 (by rfl) ⟨795174, by rfl⟩ : syracuseStep 2120465 = 1590349) B1590349
theorem B2120483 : Blo 1413526 2120483 := bstep (se 1 (by rfl) ⟨1590362, by rfl⟩ : syracuseStep 2120483 = 3180725) B3180725
theorem B2120513 : Blo 1413526 2120513 := bstep (se 2 (by rfl) ⟨795192, by rfl⟩ : syracuseStep 2120513 = 1590385) B1590385
theorem B4774733 : Blo 1413526 4774733 := bstep (se 3 (by rfl) ⟨895262, by rfl⟩ : syracuseStep 4774733 = 1790525) B1790525
theorem B2120531 : Blo 1413526 2120531 := bstep (se 1 (by rfl) ⟨1590398, by rfl⟩ : syracuseStep 2120531 = 3180797) B3180797
theorem B2120561 : Blo 1413526 2120561 := bstep (se 2 (by rfl) ⟨795210, by rfl⟩ : syracuseStep 2120561 = 1590421) B1590421
theorem B18119537 : Blo 1413526 18119537 := bstep (se 2 (by rfl) ⟨6794826, by rfl⟩ : syracuseStep 18119537 = 13589653) B13589653
theorem B5733233 : Blo 1413526 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B7256945 : Blo 1413526 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B2120579 : Blo 1413526 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B4529027 : Blo 1413526 4529027 := bstep (se 1 (by rfl) ⟨3396770, by rfl⟩ : syracuseStep 4529027 = 6793541) B6793541
theorem B4774787 : Blo 1413526 4774787 := bstep (se 1 (by rfl) ⟨3581090, by rfl⟩ : syracuseStep 4774787 = 7162181) B7162181
theorem B2120609 : Blo 1413526 2120609 := bstep (se 2 (by rfl) ⟨795228, by rfl⟩ : syracuseStep 2120609 = 1590457) B1590457
theorem B2866097 : Blo 1413526 2866097 := bstep (se 2 (by rfl) ⟨1074786, by rfl⟩ : syracuseStep 2866097 = 2149573) B2149573
theorem B2120627 : Blo 1413526 2120627 := bstep (se 1 (by rfl) ⟨1590470, by rfl⟩ : syracuseStep 2120627 = 3180941) B3180941
theorem B4029389 : Blo 1413526 4029389 := bstep (se 3 (by rfl) ⟨755510, by rfl⟩ : syracuseStep 4029389 = 1511021) B1511021
theorem B2120657 : Blo 1413526 2120657 := bstep (se 2 (by rfl) ⟨795246, by rfl⟩ : syracuseStep 2120657 = 1590493) B1590493
theorem B2120675 : Blo 1413526 2120675 := bstep (se 1 (by rfl) ⟨1590506, by rfl⟩ : syracuseStep 2120675 = 3181013) B3181013
theorem B2014193 : Blo 1413526 2014193 := bstep (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) B1510645
theorem B2120705 : Blo 1413526 2120705 := bstep (se 2 (by rfl) ⟨795264, by rfl⟩ : syracuseStep 2120705 = 1590529) B1590529
theorem B2685955 : Blo 1413526 2685955 := bstep (se 1 (by rfl) ⟨2014466, by rfl⟩ : syracuseStep 2685955 = 4028933) B4028933
theorem B2120723 : Blo 1413526 2120723 := bstep (se 1 (by rfl) ⟨1590542, by rfl⟩ : syracuseStep 2120723 = 3181085) B3181085
theorem B2120753 : Blo 1413526 2120753 := bstep (se 2 (by rfl) ⟨795282, by rfl⟩ : syracuseStep 2120753 = 1590565) B1590565
theorem B2120771 : Blo 1413526 2120771 := bstep (se 1 (by rfl) ⟨1590578, by rfl⟩ : syracuseStep 2120771 = 3181157) B3181157
theorem B1612883 : Blo 1413526 1612883 := bstep (se 1 (by rfl) ⟨1209662, by rfl⟩ : syracuseStep 1612883 = 2419325) B2419325
theorem B2120801 : Blo 1413526 2120801 := bstep (se 2 (by rfl) ⟨795300, by rfl⟩ : syracuseStep 2120801 = 1590601) B1590601
theorem B2120819 : Blo 1413526 2120819 := bstep (se 1 (by rfl) ⟨1590614, by rfl⟩ : syracuseStep 2120819 = 3181229) B3181229
theorem B2120849 : Blo 1413526 2120849 := bstep (se 2 (by rfl) ⟨795318, by rfl⟩ : syracuseStep 2120849 = 1590637) B1590637
theorem B3579025 : Blo 1413526 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B3226769 : Blo 1413526 3226769 := bstep (se 2 (by rfl) ⟨1210038, by rfl⟩ : syracuseStep 3226769 = 2420077) B2420077
theorem B4775057 : Blo 1413526 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B2120867 : Blo 1413526 2120867 := bstep (se 1 (by rfl) ⟨1590650, by rfl⟩ : syracuseStep 2120867 = 3181301) B3181301
theorem B2686115 : Blo 1413526 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B2120897 : Blo 1413526 2120897 := bstep (se 2 (by rfl) ⟨795336, by rfl⟩ : syracuseStep 2120897 = 1590673) B1590673
theorem B2120915 : Blo 1413526 2120915 := bstep (se 1 (by rfl) ⟨1590686, by rfl⟩ : syracuseStep 2120915 = 3181373) B3181373
theorem B5373155 : Blo 1413526 5373155 := bstep (se 1 (by rfl) ⟨4029866, by rfl⟩ : syracuseStep 5373155 = 8059733) B8059733
theorem B2120945 : Blo 1413526 2120945 := bstep (se 2 (by rfl) ⟨795354, by rfl⟩ : syracuseStep 2120945 = 1590709) B1590709
theorem B2120963 : Blo 1413526 2120963 := bstep (se 1 (by rfl) ⟨1590722, by rfl⟩ : syracuseStep 2120963 = 3181445) B3181445
theorem B2120993 : Blo 1413526 2120993 := bstep (se 2 (by rfl) ⟨795372, by rfl⟩ : syracuseStep 2120993 = 1590745) B1590745
theorem B2121011 : Blo 1413526 2121011 := bstep (se 1 (by rfl) ⟨1590758, by rfl⟩ : syracuseStep 2121011 = 3181517) B3181517
theorem B6045005 : Blo 1413526 6045005 := bstep (se 3 (by rfl) ⟨1133438, by rfl⟩ : syracuseStep 6045005 = 2266877) B2266877
theorem B2121041 : Blo 1413526 2121041 := bstep (se 2 (by rfl) ⟨795390, by rfl⟩ : syracuseStep 2121041 = 1590781) B1590781
theorem B2121059 : Blo 1413526 2121059 := bstep (se 1 (by rfl) ⟨1590794, by rfl⟩ : syracuseStep 2121059 = 3181589) B3181589
theorem B2121089 : Blo 1413526 2121089 := bstep (se 2 (by rfl) ⟨795408, by rfl⟩ : syracuseStep 2121089 = 1590817) B1590817
theorem B2907523 : Blo 1413526 2907523 := bstep (se 1 (by rfl) ⟨2180642, by rfl⟩ : syracuseStep 2907523 = 4361285) B4361285
theorem B2121107 : Blo 1413526 2121107 := bstep (se 1 (by rfl) ⟨1590830, by rfl⟩ : syracuseStep 2121107 = 3181661) B3181661
theorem B3579299 : Blo 1413526 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B2121137 : Blo 1413526 2121137 := bstep (se 2 (by rfl) ⟨795426, by rfl⟩ : syracuseStep 2121137 = 1590853) B1590853
theorem B2121155 : Blo 1413526 2121155 := bstep (se 1 (by rfl) ⟨1590866, by rfl⟩ : syracuseStep 2121155 = 3181733) B3181733
theorem B10739141 : Blo 1413526 10739141 := bstep (se 4 (by rfl) ⟨1006794, by rfl⟩ : syracuseStep 10739141 = 2013589) B2013589
theorem B2121185 : Blo 1413526 2121185 := bstep (se 2 (by rfl) ⟨795444, by rfl⟩ : syracuseStep 2121185 = 1590889) B1590889
theorem B2121203 : Blo 1413526 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B2014723 : Blo 1413526 2014723 := bstep (se 1 (by rfl) ⟨1511042, by rfl⟩ : syracuseStep 2014723 = 3022085) B3022085
theorem B2121233 : Blo 1413526 2121233 := bstep (se 2 (by rfl) ⟨795462, by rfl⟩ : syracuseStep 2121233 = 1590925) B1590925
theorem B2121251 : Blo 1413526 2121251 := bstep (se 1 (by rfl) ⟨1590938, by rfl⟩ : syracuseStep 2121251 = 3181877) B3181877
theorem B2121281 : Blo 1413526 2121281 := bstep (se 2 (by rfl) ⟨795480, by rfl⟩ : syracuseStep 2121281 = 1590961) B1590961
theorem B2121299 : Blo 1413526 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B3579491 : Blo 1413526 3579491 := bstep (se 1 (by rfl) ⟨2684618, by rfl⟩ : syracuseStep 3579491 = 5369237) B5369237
theorem B2121329 : Blo 1413526 2121329 := bstep (se 2 (by rfl) ⟨795498, by rfl⟩ : syracuseStep 2121329 = 1590997) B1590997
theorem B2121347 : Blo 1413526 2121347 := bstep (se 1 (by rfl) ⟨1591010, by rfl⟩ : syracuseStep 2121347 = 3182021) B3182021
theorem B2121377 : Blo 1413526 2121377 := bstep (se 2 (by rfl) ⟨795516, by rfl⟩ : syracuseStep 2121377 = 1591033) B1591033
theorem B6045347 : Blo 1413526 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B4775597 : Blo 1413526 4775597 := bstep (se 3 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 4775597 = 1790849) B1790849
theorem B2121395 : Blo 1413526 2121395 := bstep (se 1 (by rfl) ⟨1591046, by rfl⟩ : syracuseStep 2121395 = 3182093) B3182093
theorem B2121425 : Blo 1413526 2121425 := bstep (se 2 (by rfl) ⟨795534, by rfl⟩ : syracuseStep 2121425 = 1591069) B1591069
theorem B2121443 : Blo 1413526 2121443 := bstep (se 1 (by rfl) ⟨1591082, by rfl⟩ : syracuseStep 2121443 = 3182165) B3182165
theorem B4775651 : Blo 1413526 4775651 := bstep (se 1 (by rfl) ⟨3581738, by rfl⟩ : syracuseStep 4775651 = 7163477) B7163477
theorem B2121473 : Blo 1413526 2121473 := bstep (se 2 (by rfl) ⟨795552, by rfl⟩ : syracuseStep 2121473 = 1591105) B1591105
theorem B2121491 : Blo 1413526 2121491 := bstep (se 1 (by rfl) ⟨1591118, by rfl⟩ : syracuseStep 2121491 = 3182237) B3182237
theorem B3825443 : Blo 1413526 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B2121521 : Blo 1413526 2121521 := bstep (se 2 (by rfl) ⟨795570, by rfl⟩ : syracuseStep 2121521 = 1591141) B1591141
theorem B2121539 : Blo 1413526 2121539 := bstep (se 1 (by rfl) ⟨1591154, by rfl⟩ : syracuseStep 2121539 = 3182309) B3182309
theorem B2015059 : Blo 1413526 2015059 := bstep (se 1 (by rfl) ⟨1511294, by rfl⟩ : syracuseStep 2015059 = 3022589) B3022589
theorem B2121569 : Blo 1413526 2121569 := bstep (se 2 (by rfl) ⟨795588, by rfl⟩ : syracuseStep 2121569 = 1591177) B1591177
theorem B5373809 : Blo 1413526 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B2121587 : Blo 1413526 2121587 := bstep (se 1 (by rfl) ⟨1591190, by rfl⟩ : syracuseStep 2121587 = 3182381) B3182381
theorem B2121617 : Blo 1413526 2121617 := bstep (se 2 (by rfl) ⟨795606, by rfl⟩ : syracuseStep 2121617 = 1591213) B1591213
theorem B2121635 : Blo 1413526 2121635 := bstep (se 1 (by rfl) ⟨1591226, by rfl⟩ : syracuseStep 2121635 = 3182453) B3182453
theorem B2121665 : Blo 1413526 2121665 := bstep (se 2 (by rfl) ⟨795624, by rfl⟩ : syracuseStep 2121665 = 1591249) B1591249
theorem B2121683 : Blo 1413526 2121683 := bstep (se 1 (by rfl) ⟨1591262, by rfl⟩ : syracuseStep 2121683 = 3182525) B3182525
theorem B2121713 : Blo 1413526 2121713 := bstep (se 2 (by rfl) ⟨795642, by rfl⟩ : syracuseStep 2121713 = 1591285) B1591285
theorem B4775921 : Blo 1413526 4775921 := bstep (se 2 (by rfl) ⟨1790970, by rfl⟩ : syracuseStep 4775921 = 3581941) B3581941
theorem B10747889 : Blo 1413526 10747889 := bstep (se 2 (by rfl) ⟨4030458, by rfl⟩ : syracuseStep 10747889 = 8060917) B8060917
theorem B3022913 : Blo 1413526 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B2547787 : Blo 1413526 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B2121803 : Blo 1413526 2121803 := bstep (se 1 (by rfl) ⟨1591352, by rfl⟩ : syracuseStep 2121803 = 3182705) B3182705
theorem B2121815 : Blo 1413526 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B4530269 : Blo 1413526 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B4776029 : Blo 1413526 4776029 := bstep (se 3 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 4776029 = 1791011) B1791011
theorem B5374097 : Blo 1413526 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B16113815 : Blo 1413526 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B2121881 : Blo 1413526 2121881 := bstep (se 2 (by rfl) ⟨795705, by rfl⟩ : syracuseStep 2121881 = 1591411) B1591411
theorem B12083417 : Blo 1413526 12083417 := bstep (se 2 (by rfl) ⟨4531281, by rfl⟩ : syracuseStep 12083417 = 9062563) B9062563
theorem B4301021 : Blo 1413526 4301021 := bstep (se 3 (by rfl) ⟨806441, by rfl⟩ : syracuseStep 4301021 = 1612883) B1612883
theorem B2121995 : Blo 1413526 2121995 := bstep (se 1 (by rfl) ⟨1591496, by rfl⟩ : syracuseStep 2121995 = 3182993) B3182993
theorem B2122007 : Blo 1413526 2122007 := bstep (se 1 (by rfl) ⟨1591505, by rfl⟩ : syracuseStep 2122007 = 3183011) B3183011
theorem B2122073 : Blo 1413526 2122073 := bstep (se 2 (by rfl) ⟨795777, by rfl⟩ : syracuseStep 2122073 = 1591555) B1591555
theorem B2122187 : Blo 1413526 2122187 := bstep (se 1 (by rfl) ⟨1591640, by rfl⟩ : syracuseStep 2122187 = 3183281) B3183281
theorem B2122199 : Blo 1413526 2122199 := bstep (se 1 (by rfl) ⟨1591649, by rfl⟩ : syracuseStep 2122199 = 3183299) B3183299
theorem B40780259 : Blo 1413526 40780259 := bstep (se 1 (by rfl) ⟨30585194, by rfl⟩ : syracuseStep 40780259 = 61170389) B61170389
theorem B2122265 : Blo 1413526 2122265 := bstep (se 2 (by rfl) ⟨795849, by rfl⟩ : syracuseStep 2122265 = 1591699) B1591699
theorem B23249443 : Blo 1413526 23249443 := bstep (se 1 (by rfl) ⟨17437082, by rfl⟩ : syracuseStep 23249443 = 34874165) B34874165
theorem B2122379 : Blo 1413526 2122379 := bstep (se 1 (by rfl) ⟨1591784, by rfl⟩ : syracuseStep 2122379 = 3183569) B3183569
theorem B2122391 : Blo 1413526 2122391 := bstep (se 1 (by rfl) ⟨1591793, by rfl⟩ : syracuseStep 2122391 = 3183587) B3183587
theorem B3580595 : Blo 1413526 3580595 := bstep (se 1 (by rfl) ⟨2685446, by rfl⟩ : syracuseStep 3580595 = 5370893) B5370893
theorem B32654029 : Blo 1413526 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B2122457 : Blo 1413526 2122457 := bstep (se 2 (by rfl) ⟨795921, by rfl⟩ : syracuseStep 2122457 = 1591843) B1591843
theorem B12092165 : Blo 1413526 12092165 := bstep (se 4 (by rfl) ⟨1133640, by rfl⟩ : syracuseStep 12092165 = 2267281) B2267281
theorem B2122571 : Blo 1413526 2122571 := bstep (se 1 (by rfl) ⟨1591928, by rfl⟩ : syracuseStep 2122571 = 3183857) B3183857
theorem B2122583 : Blo 1413526 2122583 := bstep (se 1 (by rfl) ⟨1591937, by rfl⟩ : syracuseStep 2122583 = 3183875) B3183875
theorem B2122649 : Blo 1413526 2122649 := bstep (se 2 (by rfl) ⟨795993, by rfl⟩ : syracuseStep 2122649 = 1591987) B1591987
theorem B2122763 : Blo 1413526 2122763 := bstep (se 1 (by rfl) ⟨1592072, by rfl⟩ : syracuseStep 2122763 = 3184145) B3184145
theorem B1590295 : Blo 1413526 1590295 := bstep (se 1 (by rfl) ⟨1192721, by rfl⟩ : syracuseStep 1590295 = 2385443) B2385443
theorem B2122775 : Blo 1413526 2122775 := bstep (se 1 (by rfl) ⟨1592081, by rfl⟩ : syracuseStep 2122775 = 3184163) B3184163
theorem B12076067 : Blo 1413526 12076067 := bstep (se 1 (by rfl) ⟨9057050, by rfl⟩ : syracuseStep 12076067 = 18114101) B18114101
theorem B4416563 : Blo 1413526 4416563 := bstep (se 1 (by rfl) ⟨3312422, by rfl⟩ : syracuseStep 4416563 = 6624845) B6624845
theorem B2720855 : Blo 1413526 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B2122841 : Blo 1413526 2122841 := bstep (se 2 (by rfl) ⟨796065, by rfl⟩ : syracuseStep 2122841 = 1592131) B1592131
theorem B6128729 : Blo 1413526 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B6120593 : Blo 1413526 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B1590475 : Blo 1413526 1590475 := bstep (se 1 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 1590475 = 2385713) B2385713
theorem B3581131 : Blo 1413526 3581131 := bstep (se 1 (by rfl) ⟨2685848, by rfl⟩ : syracuseStep 3581131 = 5371697) B5371697
theorem B2122955 : Blo 1413526 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B4777163 : Blo 1413526 4777163 := bstep (se 1 (by rfl) ⟨3582872, by rfl⟩ : syracuseStep 4777163 = 7165745) B7165745
theorem B2122967 : Blo 1413526 2122967 := bstep (se 1 (by rfl) ⟨1592225, by rfl⟩ : syracuseStep 2122967 = 3184451) B3184451
theorem B5367005 : Blo 1413526 5367005 := bstep (se 3 (by rfl) ⟨1006313, by rfl⟩ : syracuseStep 5367005 = 2012627) B2012627
theorem B2123033 : Blo 1413526 2123033 := bstep (se 2 (by rfl) ⟨796137, by rfl⟩ : syracuseStep 2123033 = 1592275) B1592275
theorem B1590583 : Blo 1413526 1590583 := bstep (se 1 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 1590583 = 2385875) B2385875
theorem B3581273 : Blo 1413526 3581273 := bstep (se 2 (by rfl) ⟨1342977, by rfl⟩ : syracuseStep 3581273 = 2685955) B2685955
theorem B10741085 : Blo 1413526 10741085 := bstep (se 3 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 10741085 = 4027907) B4027907
theorem B9684355 : Blo 1413526 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B2123147 : Blo 1413526 2123147 := bstep (se 1 (by rfl) ⟨1592360, by rfl⟩ : syracuseStep 2123147 = 3184721) B3184721
theorem B13084055 : Blo 1413526 13084055 := bstep (se 1 (by rfl) ⟨9813041, by rfl⟩ : syracuseStep 13084055 = 19626083) B19626083
theorem B2123159 : Blo 1413526 2123159 := bstep (se 1 (by rfl) ⟨1592369, by rfl⟩ : syracuseStep 2123159 = 3184739) B3184739
theorem B2549171 : Blo 1413526 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B2385355 : Blo 1413526 2385355 := bstep (se 1 (by rfl) ⟨1789016, by rfl⟩ : syracuseStep 2385355 = 3578033) B3578033
theorem B2123225 : Blo 1413526 2123225 := bstep (se 2 (by rfl) ⟨796209, by rfl⟩ : syracuseStep 2123225 = 1592419) B1592419
theorem B1590763 : Blo 1413526 1590763 := bstep (se 1 (by rfl) ⟨1193072, by rfl⟩ : syracuseStep 1590763 = 2386145) B2386145
theorem B27198989 : Blo 1413526 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B21784139 : Blo 1413526 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B1590871 : Blo 1413526 1590871 := bstep (se 1 (by rfl) ⟨1193153, by rfl⟩ : syracuseStep 1590871 = 2386307) B2386307
theorem B2385497 : Blo 1413526 2385497 := bstep (se 2 (by rfl) ⟨894561, by rfl⟩ : syracuseStep 2385497 = 1789123) B1789123
theorem B2385625 : Blo 1413526 2385625 := bstep (se 2 (by rfl) ⟨894609, by rfl⟩ : syracuseStep 2385625 = 1789219) B1789219
theorem B6039299 : Blo 1413526 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B1591051 : Blo 1413526 1591051 := bstep (se 1 (by rfl) ⟨1193288, by rfl⟩ : syracuseStep 1591051 = 2386577) B2386577
theorem B3876697 : Blo 1413526 3876697 := bstep (se 2 (by rfl) ⟨1453761, by rfl⟩ : syracuseStep 3876697 = 2907523) B2907523
theorem B1591159 : Blo 1413526 1591159 := bstep (se 1 (by rfl) ⟨1193369, by rfl⟩ : syracuseStep 1591159 = 2386739) B2386739
theorem B3180491 : Blo 1413526 3180491 := bstep (se 1 (by rfl) ⟨2385368, by rfl⟩ : syracuseStep 3180491 = 4770737) B4770737
theorem B3180545 : Blo 1413526 3180545 := bstep (se 2 (by rfl) ⟨1192704, by rfl⟩ : syracuseStep 3180545 = 2385409) B2385409
theorem B5441539 : Blo 1413526 5441539 := bstep (se 1 (by rfl) ⟨4081154, by rfl⟩ : syracuseStep 5441539 = 8162309) B8162309
theorem B1591339 : Blo 1413526 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B4360267 : Blo 1413526 4360267 := bstep (se 1 (by rfl) ⟨3270200, by rfl⟩ : syracuseStep 4360267 = 6540401) B6540401
theorem B1591447 : Blo 1413526 1591447 := bstep (se 1 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 1591447 = 2387171) B2387171
theorem B3582103 : Blo 1413526 3582103 := bstep (se 1 (by rfl) ⟨2686577, by rfl⟩ : syracuseStep 3582103 = 5373155) B5373155
theorem B3180761 : Blo 1413526 3180761 := bstep (se 2 (by rfl) ⟨1192785, by rfl⟩ : syracuseStep 3180761 = 2385571) B2385571
theorem B1509611 : Blo 1413526 1509611 := bstep (se 1 (by rfl) ⟨1132208, by rfl⟩ : syracuseStep 1509611 = 2264417) B2264417
theorem B2386199 : Blo 1413526 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B6449453 : Blo 1413526 6449453 := bstep (se 3 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 6449453 = 2418545) B2418545
theorem B8055085 : Blo 1413526 8055085 := bstep (se 3 (by rfl) ⟨1510328, by rfl⟩ : syracuseStep 8055085 = 3020657) B3020657
theorem B3180851 : Blo 1413526 3180851 := bstep (se 1 (by rfl) ⟨2385638, by rfl⟩ : syracuseStep 3180851 = 4771277) B4771277
theorem B1591627 : Blo 1413526 1591627 := bstep (se 1 (by rfl) ⟨1193720, by rfl⟩ : syracuseStep 1591627 = 2387441) B2387441
theorem B3180887 : Blo 1413526 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B8604035 : Blo 1413526 8604035 := bstep (se 1 (by rfl) ⟨6453026, by rfl⟩ : syracuseStep 8604035 = 12906053) B12906053
theorem B2386327 : Blo 1413526 2386327 := bstep (se 1 (by rfl) ⟨1789745, by rfl⟩ : syracuseStep 2386327 = 3579491) B3579491
theorem B5237165 : Blo 1413526 5237165 := bstep (se 3 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 5237165 = 1963937) B1963937
theorem B1591735 : Blo 1413526 1591735 := bstep (se 1 (by rfl) ⟨1193801, by rfl⟩ : syracuseStep 1591735 = 2387603) B2387603
theorem B3181067 : Blo 1413526 3181067 := bstep (se 1 (by rfl) ⟨2385800, by rfl⟩ : syracuseStep 3181067 = 4771601) B4771601
theorem B2550295 : Blo 1413526 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B3181121 : Blo 1413526 3181121 := bstep (se 2 (by rfl) ⟨1192920, by rfl⟩ : syracuseStep 3181121 = 2385841) B2385841
theorem B3582539 : Blo 1413526 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B1591915 : Blo 1413526 1591915 := bstep (se 1 (by rfl) ⟨1193936, by rfl⟩ : syracuseStep 1591915 = 2387873) B2387873
theorem B10193539 : Blo 1413526 10193539 := bstep (se 1 (by rfl) ⟨7645154, by rfl⟩ : syracuseStep 10193539 = 15290309) B15290309
theorem B1592023 : Blo 1413526 1592023 := bstep (se 1 (by rfl) ⟨1194017, by rfl⟩ : syracuseStep 1592023 = 2388035) B2388035
theorem B7645913 : Blo 1413526 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B8604377 : Blo 1413526 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B3181337 : Blo 1413526 3181337 := bstep (se 2 (by rfl) ⟨1193001, by rfl⟩ : syracuseStep 3181337 = 2386003) B2386003
theorem B4303709 : Blo 1413526 4303709 := bstep (se 3 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 4303709 = 1613891) B1613891
theorem B3181427 : Blo 1413526 3181427 := bstep (se 1 (by rfl) ⟨2386070, by rfl⟩ : syracuseStep 3181427 = 4772141) B4772141
theorem B1592203 : Blo 1413526 1592203 := bstep (se 1 (by rfl) ⟨1194152, by rfl⟩ : syracuseStep 1592203 = 2388305) B2388305
theorem B3181463 : Blo 1413526 3181463 := bstep (se 1 (by rfl) ⟨2386097, by rfl⟩ : syracuseStep 3181463 = 4772195) B4772195
theorem B3582913 : Blo 1413526 3582913 := bstep (se 2 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 3582913 = 2687185) B2687185
theorem B1592311 : Blo 1413526 1592311 := bstep (se 1 (by rfl) ⟨1194233, by rfl⟩ : syracuseStep 1592311 = 2388467) B2388467
theorem B2386955 : Blo 1413526 2386955 := bstep (se 1 (by rfl) ⟨1790216, by rfl⟩ : syracuseStep 2386955 = 3580433) B3580433
theorem B3181643 : Blo 1413526 3181643 := bstep (se 1 (by rfl) ⟨2386232, by rfl⟩ : syracuseStep 3181643 = 4772465) B4772465
theorem B3181697 : Blo 1413526 3181697 := bstep (se 2 (by rfl) ⟨1193136, by rfl⟩ : syracuseStep 3181697 = 2386273) B2386273
theorem B5368963 : Blo 1413526 5368963 := bstep (se 1 (by rfl) ⟨4026722, by rfl⟩ : syracuseStep 5368963 = 8053445) B8053445
theorem B1789067 : Blo 1413526 1789067 := bstep (se 1 (by rfl) ⟨1341800, by rfl⟩ : syracuseStep 1789067 = 2683601) B2683601
theorem B2387083 : Blo 1413526 2387083 := bstep (se 1 (by rfl) ⟨1790312, by rfl⟩ : syracuseStep 2387083 = 3580625) B3580625
theorem B36269207 : Blo 1413526 36269207 := bstep (se 1 (by rfl) ⟨27201905, by rfl⟩ : syracuseStep 36269207 = 54403811) B54403811
theorem B7163153 : Blo 1413526 7163153 := bstep (se 2 (by rfl) ⟨2686182, by rfl⟩ : syracuseStep 7163153 = 5372365) B5372365
theorem B2387225 : Blo 1413526 2387225 := bstep (se 2 (by rfl) ⟨895209, by rfl⟩ : syracuseStep 2387225 = 1790419) B1790419
theorem B4025675 : Blo 1413526 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B1699159 : Blo 1413526 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B3181913 : Blo 1413526 3181913 := bstep (se 2 (by rfl) ⟨1193217, by rfl⟩ : syracuseStep 3181913 = 2386435) B2386435
theorem B4771223 : Blo 1413526 4771223 := bstep (se 1 (by rfl) ⟨3578417, by rfl⟩ : syracuseStep 4771223 = 7156835) B7156835
theorem B2387353 : Blo 1413526 2387353 := bstep (se 2 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 2387353 = 1790515) B1790515
theorem B3182003 : Blo 1413526 3182003 := bstep (se 1 (by rfl) ⟨2386502, by rfl⟩ : syracuseStep 3182003 = 4773005) B4773005
theorem B6794675 : Blo 1413526 6794675 := bstep (se 1 (by rfl) ⟨5096006, by rfl⟩ : syracuseStep 6794675 = 10192013) B10192013
theorem B5369267 : Blo 1413526 5369267 := bstep (se 1 (by rfl) ⟨4026950, by rfl⟩ : syracuseStep 5369267 = 8053901) B8053901
theorem B7163315 : Blo 1413526 7163315 := bstep (se 1 (by rfl) ⟨5372486, by rfl⟩ : syracuseStep 7163315 = 10744973) B10744973
theorem B3182039 : Blo 1413526 3182039 := bstep (se 1 (by rfl) ⟨2386529, by rfl⟩ : syracuseStep 3182039 = 4773059) B4773059
theorem B25808453 : Blo 1413526 25808453 := bstep (se 4 (by rfl) ⟨2419542, by rfl⟩ : syracuseStep 25808453 = 4839085) B4839085
theorem B3182219 : Blo 1413526 3182219 := bstep (se 1 (by rfl) ⟨2386664, by rfl⟩ : syracuseStep 3182219 = 4773329) B4773329
theorem B3182273 : Blo 1413526 3182273 := bstep (se 2 (by rfl) ⟨1193352, by rfl⟩ : syracuseStep 3182273 = 2386705) B2386705
theorem B1699543 : Blo 1413526 1699543 := bstep (se 1 (by rfl) ⟨1274657, by rfl⟩ : syracuseStep 1699543 = 2549315) B2549315
theorem B6450947 : Blo 1413526 6450947 := bstep (se 1 (by rfl) ⟨4838210, by rfl⟩ : syracuseStep 6450947 = 9676421) B9676421
theorem B1789771 : Blo 1413526 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B2150231 : Blo 1413526 2150231 := bstep (se 1 (by rfl) ⟨1612673, by rfl⟩ : syracuseStep 2150231 = 3225347) B3225347
theorem B30609251 : Blo 1413526 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B1699735 : Blo 1413526 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B3182489 : Blo 1413526 3182489 := bstep (se 2 (by rfl) ⟨1193433, by rfl⟩ : syracuseStep 3182489 = 2386867) B2386867
theorem B4771763 : Blo 1413526 4771763 := bstep (se 1 (by rfl) ⟨3578822, by rfl⟩ : syracuseStep 4771763 = 7157645) B7157645
theorem B2387927 : Blo 1413526 2387927 := bstep (se 1 (by rfl) ⟨1790945, by rfl⟩ : syracuseStep 2387927 = 3581891) B3581891
theorem B3182579 : Blo 1413526 3182579 := bstep (se 1 (by rfl) ⟨2386934, by rfl⟩ : syracuseStep 3182579 = 4773869) B4773869
theorem B3182615 : Blo 1413526 3182615 := bstep (se 1 (by rfl) ⟨2386961, by rfl⟩ : syracuseStep 3182615 = 4773923) B4773923
theorem B5369921 : Blo 1413526 5369921 := bstep (se 2 (by rfl) ⟨2013720, by rfl⟩ : syracuseStep 5369921 = 4027441) B4027441
theorem B1790039 : Blo 1413526 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B2388055 : Blo 1413526 2388055 := bstep (se 1 (by rfl) ⟨1791041, by rfl⟩ : syracuseStep 2388055 = 3582083) B3582083
theorem B4772033 : Blo 1413526 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B3182795 : Blo 1413526 3182795 := bstep (se 1 (by rfl) ⟨2387096, by rfl⟩ : syracuseStep 3182795 = 4774193) B4774193
theorem B3182849 : Blo 1413526 3182849 := bstep (se 2 (by rfl) ⟨1193568, by rfl⟩ : syracuseStep 3182849 = 2387137) B2387137
theorem B1413527 : Blo 1413526 1413527 := bstep (se 1 (by rfl) ⟨1060145, by rfl⟩ : syracuseStep 1413527 = 2120291) B2120291
theorem B1413547 : Blo 1413526 1413547 := bstep (se 1 (by rfl) ⟨1060160, by rfl⟩ : syracuseStep 1413547 = 2120321) B2120321
theorem B1413559 : Blo 1413526 1413559 := bstep (se 1 (by rfl) ⟨1060169, by rfl⟩ : syracuseStep 1413559 = 2120339) B2120339
theorem B1413579 : Blo 1413526 1413579 := bstep (se 1 (by rfl) ⟨1060184, by rfl⟩ : syracuseStep 1413579 = 2120369) B2120369
theorem B1413591 : Blo 1413526 1413591 := bstep (se 1 (by rfl) ⟨1060193, by rfl⟩ : syracuseStep 1413591 = 2120387) B2120387
theorem B3183065 : Blo 1413526 3183065 := bstep (se 2 (by rfl) ⟨1193649, by rfl⟩ : syracuseStep 3183065 = 2387299) B2387299
theorem B1413611 : Blo 1413526 1413611 := bstep (se 1 (by rfl) ⟨1060208, by rfl⟩ : syracuseStep 1413611 = 2120417) B2120417
theorem B1413623 : Blo 1413526 1413623 := bstep (se 1 (by rfl) ⟨1060217, by rfl⟩ : syracuseStep 1413623 = 2120435) B2120435
theorem B1413643 : Blo 1413526 1413643 := bstep (se 1 (by rfl) ⟨1060232, by rfl⟩ : syracuseStep 1413643 = 2120465) B2120465
theorem B1413655 : Blo 1413526 1413655 := bstep (se 1 (by rfl) ⟨1060241, by rfl⟩ : syracuseStep 1413655 = 2120483) B2120483
theorem B1413675 : Blo 1413526 1413675 := bstep (se 1 (by rfl) ⟨1060256, by rfl⟩ : syracuseStep 1413675 = 2120513) B2120513
theorem B3183155 : Blo 1413526 3183155 := bstep (se 1 (by rfl) ⟨2387366, by rfl⟩ : syracuseStep 3183155 = 4774733) B4774733
theorem B1413687 : Blo 1413526 1413687 := bstep (se 1 (by rfl) ⟨1060265, by rfl⟩ : syracuseStep 1413687 = 2120531) B2120531
theorem B1413707 : Blo 1413526 1413707 := bstep (se 1 (by rfl) ⟨1060280, by rfl⟩ : syracuseStep 1413707 = 2120561) B2120561
theorem B12079691 : Blo 1413526 12079691 := bstep (se 1 (by rfl) ⟨9059768, by rfl⟩ : syracuseStep 12079691 = 18119537) B18119537
theorem B3822155 : Blo 1413526 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B4837963 : Blo 1413526 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B1413719 : Blo 1413526 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B3019351 : Blo 1413526 3019351 := bstep (se 1 (by rfl) ⟨2264513, by rfl⟩ : syracuseStep 3019351 = 4529027) B4529027
theorem B3183191 : Blo 1413526 3183191 := bstep (se 1 (by rfl) ⟨2387393, by rfl⟩ : syracuseStep 3183191 = 4774787) B4774787
theorem B1413739 : Blo 1413526 1413739 := bstep (se 1 (by rfl) ⟨1060304, by rfl⟩ : syracuseStep 1413739 = 2120609) B2120609
theorem B1413751 : Blo 1413526 1413751 := bstep (se 1 (by rfl) ⟨1060313, by rfl⟩ : syracuseStep 1413751 = 2120627) B2120627
theorem B3019393 : Blo 1413526 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B1413771 : Blo 1413526 1413771 := bstep (se 1 (by rfl) ⟨1060328, by rfl⟩ : syracuseStep 1413771 = 2120657) B2120657
theorem B1413783 : Blo 1413526 1413783 := bstep (se 1 (by rfl) ⟨1060337, by rfl⟩ : syracuseStep 1413783 = 2120675) B2120675
theorem B1413803 : Blo 1413526 1413803 := bstep (se 1 (by rfl) ⟨1060352, by rfl⟩ : syracuseStep 1413803 = 2120705) B2120705
theorem B1413815 : Blo 1413526 1413815 := bstep (se 1 (by rfl) ⟨1060361, by rfl⟩ : syracuseStep 1413815 = 2120723) B2120723
theorem B1413835 : Blo 1413526 1413835 := bstep (se 1 (by rfl) ⟨1060376, by rfl⟩ : syracuseStep 1413835 = 2120753) B2120753
theorem B2388683 : Blo 1413526 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B1413847 : Blo 1413526 1413847 := bstep (se 1 (by rfl) ⟨1060385, by rfl⟩ : syracuseStep 1413847 = 2120771) B2120771
theorem B4772573 : Blo 1413526 4772573 := bstep (se 3 (by rfl) ⟨894857, by rfl⟩ : syracuseStep 4772573 = 1789715) B1789715
theorem B1413867 : Blo 1413526 1413867 := bstep (se 1 (by rfl) ⟨1060400, by rfl⟩ : syracuseStep 1413867 = 2120801) B2120801
theorem B1413879 : Blo 1413526 1413879 := bstep (se 1 (by rfl) ⟨1060409, by rfl⟩ : syracuseStep 1413879 = 2120819) B2120819
theorem B1413899 : Blo 1413526 1413899 := bstep (se 1 (by rfl) ⟨1060424, by rfl⟩ : syracuseStep 1413899 = 2120849) B2120849
theorem B2151179 : Blo 1413526 2151179 := bstep (se 1 (by rfl) ⟨1613384, by rfl⟩ : syracuseStep 2151179 = 3226769) B3226769
theorem B3183371 : Blo 1413526 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B1413911 : Blo 1413526 1413911 := bstep (se 1 (by rfl) ⟨1060433, by rfl⟩ : syracuseStep 1413911 = 2120867) B2120867
theorem B1790743 : Blo 1413526 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B1413931 : Blo 1413526 1413931 := bstep (se 1 (by rfl) ⟨1060448, by rfl⟩ : syracuseStep 1413931 = 2120897) B2120897
theorem B1413943 : Blo 1413526 1413943 := bstep (se 1 (by rfl) ⟨1060457, by rfl⟩ : syracuseStep 1413943 = 2120915) B2120915
theorem B3183425 : Blo 1413526 3183425 := bstep (se 2 (by rfl) ⟨1193784, by rfl⟩ : syracuseStep 3183425 = 2387569) B2387569
theorem B1413963 : Blo 1413526 1413963 := bstep (se 1 (by rfl) ⟨1060472, by rfl⟩ : syracuseStep 1413963 = 2120945) B2120945
theorem B1413975 : Blo 1413526 1413975 := bstep (se 1 (by rfl) ⟨1060481, by rfl⟩ : syracuseStep 1413975 = 2120963) B2120963
theorem B1413995 : Blo 1413526 1413995 := bstep (se 1 (by rfl) ⟨1060496, by rfl⟩ : syracuseStep 1413995 = 2120993) B2120993
theorem B1414007 : Blo 1413526 1414007 := bstep (se 1 (by rfl) ⟨1060505, by rfl⟩ : syracuseStep 1414007 = 2121011) B2121011
theorem B1414027 : Blo 1413526 1414027 := bstep (se 1 (by rfl) ⟨1060520, by rfl⟩ : syracuseStep 1414027 = 2121041) B2121041
theorem B1414039 : Blo 1413526 1414039 := bstep (se 1 (by rfl) ⟨1060529, by rfl⟩ : syracuseStep 1414039 = 2121059) B2121059
theorem B1414059 : Blo 1413526 1414059 := bstep (se 1 (by rfl) ⟨1060544, by rfl⟩ : syracuseStep 1414059 = 2121089) B2121089
theorem B5100461 : Blo 1413526 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B4027315 : Blo 1413526 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B1414071 : Blo 1413526 1414071 := bstep (se 1 (by rfl) ⟨1060553, by rfl⟩ : syracuseStep 1414071 = 2121107) B2121107
theorem B1414091 : Blo 1413526 1414091 := bstep (se 1 (by rfl) ⟨1060568, by rfl⟩ : syracuseStep 1414091 = 2121137) B2121137
theorem B1414103 : Blo 1413526 1414103 := bstep (se 1 (by rfl) ⟨1060577, by rfl⟩ : syracuseStep 1414103 = 2121155) B2121155
theorem B1414123 : Blo 1413526 1414123 := bstep (se 1 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 1414123 = 2121185) B2121185
theorem B1414135 : Blo 1413526 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B1414155 : Blo 1413526 1414155 := bstep (se 1 (by rfl) ⟨1060616, by rfl⟩ : syracuseStep 1414155 = 2121233) B2121233
theorem B1414167 : Blo 1413526 1414167 := bstep (se 1 (by rfl) ⟨1060625, by rfl⟩ : syracuseStep 1414167 = 2121251) B2121251
theorem B3183641 : Blo 1413526 3183641 := bstep (se 2 (by rfl) ⟨1193865, by rfl⟩ : syracuseStep 3183641 = 2387731) B2387731
theorem B1414187 : Blo 1413526 1414187 := bstep (se 1 (by rfl) ⟨1060640, by rfl⟩ : syracuseStep 1414187 = 2121281) B2121281
theorem B1414199 : Blo 1413526 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B3224651 : Blo 1413526 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B1414219 : Blo 1413526 1414219 := bstep (se 1 (by rfl) ⟨1060664, by rfl⟩ : syracuseStep 1414219 = 2121329) B2121329
theorem B1414231 : Blo 1413526 1414231 := bstep (se 1 (by rfl) ⟨1060673, by rfl⟩ : syracuseStep 1414231 = 2121347) B2121347
theorem B1414251 : Blo 1413526 1414251 := bstep (se 1 (by rfl) ⟨1060688, by rfl⟩ : syracuseStep 1414251 = 2121377) B2121377
theorem B3183731 : Blo 1413526 3183731 := bstep (se 1 (by rfl) ⟨2387798, by rfl⟩ : syracuseStep 3183731 = 4775597) B4775597
theorem B1414263 : Blo 1413526 1414263 := bstep (se 1 (by rfl) ⟨1060697, by rfl⟩ : syracuseStep 1414263 = 2121395) B2121395
theorem B1414283 : Blo 1413526 1414283 := bstep (se 1 (by rfl) ⟨1060712, by rfl⟩ : syracuseStep 1414283 = 2121425) B2121425
theorem B1414295 : Blo 1413526 1414295 := bstep (se 1 (by rfl) ⟨1060721, by rfl⟩ : syracuseStep 1414295 = 2121443) B2121443
theorem B3183767 : Blo 1413526 3183767 := bstep (se 1 (by rfl) ⟨2387825, by rfl⟩ : syracuseStep 3183767 = 4775651) B4775651
theorem B1414315 : Blo 1413526 1414315 := bstep (se 1 (by rfl) ⟨1060736, by rfl⟩ : syracuseStep 1414315 = 2121473) B2121473
theorem B1414327 : Blo 1413526 1414327 := bstep (se 1 (by rfl) ⟨1060745, by rfl⟩ : syracuseStep 1414327 = 2121491) B2121491
theorem B1414347 : Blo 1413526 1414347 := bstep (se 1 (by rfl) ⟨1060760, by rfl⟩ : syracuseStep 1414347 = 2121521) B2121521
theorem B1414359 : Blo 1413526 1414359 := bstep (se 1 (by rfl) ⟨1060769, by rfl⟩ : syracuseStep 1414359 = 2121539) B2121539
theorem B1414379 : Blo 1413526 1414379 := bstep (se 1 (by rfl) ⟨1060784, by rfl⟩ : syracuseStep 1414379 = 2121569) B2121569
theorem B1414391 : Blo 1413526 1414391 := bstep (se 1 (by rfl) ⟨1060793, by rfl⟩ : syracuseStep 1414391 = 2121587) B2121587
theorem B2684171 : Blo 1413526 2684171 := bstep (se 1 (by rfl) ⟨2013128, by rfl⟩ : syracuseStep 2684171 = 4026257) B4026257
theorem B1414411 : Blo 1413526 1414411 := bstep (se 1 (by rfl) ⟨1060808, by rfl⟩ : syracuseStep 1414411 = 2121617) B2121617
theorem B1414423 : Blo 1413526 1414423 := bstep (se 1 (by rfl) ⟨1060817, by rfl⟩ : syracuseStep 1414423 = 2121635) B2121635
theorem B1414443 : Blo 1413526 1414443 := bstep (se 1 (by rfl) ⟨1060832, by rfl⟩ : syracuseStep 1414443 = 2121665) B2121665
theorem B5371181 : Blo 1413526 5371181 := bstep (se 3 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 5371181 = 2014193) B2014193
theorem B1414455 : Blo 1413526 1414455 := bstep (se 1 (by rfl) ⟨1060841, by rfl⟩ : syracuseStep 1414455 = 2121683) B2121683
theorem B1414475 : Blo 1413526 1414475 := bstep (se 1 (by rfl) ⟨1060856, by rfl⟩ : syracuseStep 1414475 = 2121713) B2121713
theorem B5371211 : Blo 1413526 5371211 := bstep (se 1 (by rfl) ⟨4028408, by rfl⟩ : syracuseStep 5371211 = 8056817) B8056817
theorem B3183947 : Blo 1413526 3183947 := bstep (se 1 (by rfl) ⟨2387960, by rfl⟩ : syracuseStep 3183947 = 4775921) B4775921
theorem B7165259 : Blo 1413526 7165259 := bstep (se 1 (by rfl) ⟨5373944, by rfl⟩ : syracuseStep 7165259 = 10747889) B10747889
theorem B1414487 : Blo 1413526 1414487 := bstep (se 1 (by rfl) ⟨1060865, by rfl⟩ : syracuseStep 1414487 = 2121731) B2121731
theorem B3396953 : Blo 1413526 3396953 := bstep (se 2 (by rfl) ⟨1273857, by rfl⟩ : syracuseStep 3396953 = 2547715) B2547715
theorem B1414507 : Blo 1413526 1414507 := bstep (se 1 (by rfl) ⟨1060880, by rfl⟩ : syracuseStep 1414507 = 2121761) B2121761
theorem B1414519 : Blo 1413526 1414519 := bstep (se 1 (by rfl) ⟨1060889, by rfl⟩ : syracuseStep 1414519 = 2121779) B2121779
theorem B3184001 : Blo 1413526 3184001 := bstep (se 2 (by rfl) ⟨1194000, by rfl⟩ : syracuseStep 3184001 = 2388001) B2388001
theorem B1414539 : Blo 1413526 1414539 := bstep (se 1 (by rfl) ⟨1060904, by rfl⟩ : syracuseStep 1414539 = 2121809) B2121809
theorem B1414551 : Blo 1413526 1414551 := bstep (se 1 (by rfl) ⟨1060913, by rfl⟩ : syracuseStep 1414551 = 2121827) B2121827
theorem B1414571 : Blo 1413526 1414571 := bstep (se 1 (by rfl) ⟨1060928, by rfl⟩ : syracuseStep 1414571 = 2121857) B2121857
theorem B20379059 : Blo 1413526 20379059 := bstep (se 1 (by rfl) ⟨15284294, by rfl⟩ : syracuseStep 20379059 = 30568589) B30568589
theorem B1414583 : Blo 1413526 1414583 := bstep (se 1 (by rfl) ⟨1060937, by rfl⟩ : syracuseStep 1414583 = 2121875) B2121875
theorem B2684353 : Blo 1413526 2684353 := bstep (se 2 (by rfl) ⟨1006632, by rfl⟩ : syracuseStep 2684353 = 2013265) B2013265
theorem B1414603 : Blo 1413526 1414603 := bstep (se 1 (by rfl) ⟨1060952, by rfl⟩ : syracuseStep 1414603 = 2121905) B2121905
theorem B1414615 : Blo 1413526 1414615 := bstep (se 1 (by rfl) ⟨1060961, by rfl⟩ : syracuseStep 1414615 = 2121923) B2121923
theorem B22935001 : Blo 1413526 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B1414635 : Blo 1413526 1414635 := bstep (se 1 (by rfl) ⟨1060976, by rfl⟩ : syracuseStep 1414635 = 2121953) B2121953
theorem B1414647 : Blo 1413526 1414647 := bstep (se 1 (by rfl) ⟨1060985, by rfl⟩ : syracuseStep 1414647 = 2121971) B2121971
theorem B1414667 : Blo 1413526 1414667 := bstep (se 1 (by rfl) ⟨1061000, by rfl⟩ : syracuseStep 1414667 = 2122001) B2122001
theorem B1414679 : Blo 1413526 1414679 := bstep (se 1 (by rfl) ⟨1061009, by rfl⟩ : syracuseStep 1414679 = 2122019) B2122019
theorem B1414699 : Blo 1413526 1414699 := bstep (se 1 (by rfl) ⟨1061024, by rfl⟩ : syracuseStep 1414699 = 2122049) B2122049
theorem B10737197 : Blo 1413526 10737197 := bstep (se 3 (by rfl) ⟨2013224, by rfl⟩ : syracuseStep 10737197 = 4026449) B4026449
theorem B1414711 : Blo 1413526 1414711 := bstep (se 1 (by rfl) ⟨1061033, by rfl⟩ : syracuseStep 1414711 = 2122067) B2122067
theorem B4838977 : Blo 1413526 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B1414731 : Blo 1413526 1414731 := bstep (se 1 (by rfl) ⟨1061048, by rfl⟩ : syracuseStep 1414731 = 2122097) B2122097
theorem B1414743 : Blo 1413526 1414743 := bstep (se 1 (by rfl) ⟨1061057, by rfl⟩ : syracuseStep 1414743 = 2122115) B2122115
theorem B3823193 : Blo 1413526 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B3184217 : Blo 1413526 3184217 := bstep (se 2 (by rfl) ⟨1194081, by rfl⟩ : syracuseStep 3184217 = 2388163) B2388163
theorem B1414763 : Blo 1413526 1414763 := bstep (se 1 (by rfl) ⟨1061072, by rfl⟩ : syracuseStep 1414763 = 2122145) B2122145
theorem B1414775 : Blo 1413526 1414775 := bstep (se 1 (by rfl) ⟨1061081, by rfl⟩ : syracuseStep 1414775 = 2122163) B2122163
theorem B1414795 : Blo 1413526 1414795 := bstep (se 1 (by rfl) ⟨1061096, by rfl⟩ : syracuseStep 1414795 = 2122193) B2122193
theorem B1414807 : Blo 1413526 1414807 := bstep (se 1 (by rfl) ⟨1061105, by rfl⟩ : syracuseStep 1414807 = 2122211) B2122211
theorem B2266775 : Blo 1413526 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B1414827 : Blo 1413526 1414827 := bstep (se 1 (by rfl) ⟨1061120, by rfl⟩ : syracuseStep 1414827 = 2122241) B2122241
theorem B3184307 : Blo 1413526 3184307 := bstep (se 1 (by rfl) ⟨2388230, by rfl⟩ : syracuseStep 3184307 = 4776461) B4776461
theorem B1414839 : Blo 1413526 1414839 := bstep (se 1 (by rfl) ⟨1061129, by rfl⟩ : syracuseStep 1414839 = 2122259) B2122259
theorem B1414859 : Blo 1413526 1414859 := bstep (se 1 (by rfl) ⟨1061144, by rfl⟩ : syracuseStep 1414859 = 2122289) B2122289
theorem B17209037 : Blo 1413526 17209037 := bstep (se 3 (by rfl) ⟨3226694, by rfl⟩ : syracuseStep 17209037 = 6453389) B6453389
theorem B1414871 : Blo 1413526 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B3184343 : Blo 1413526 3184343 := bstep (se 1 (by rfl) ⟨2388257, by rfl⟩ : syracuseStep 3184343 = 4776515) B4776515
theorem B3823325 : Blo 1413526 3823325 := bstep (se 3 (by rfl) ⟨716873, by rfl⟩ : syracuseStep 3823325 = 1433747) B1433747
theorem B1414891 : Blo 1413526 1414891 := bstep (se 1 (by rfl) ⟨1061168, by rfl⟩ : syracuseStep 1414891 = 2122337) B2122337
theorem B1414903 : Blo 1413526 1414903 := bstep (se 1 (by rfl) ⟨1061177, by rfl⟩ : syracuseStep 1414903 = 2122355) B2122355
theorem B1414923 : Blo 1413526 1414923 := bstep (se 1 (by rfl) ⟨1061192, by rfl⟩ : syracuseStep 1414923 = 2122385) B2122385
theorem B6051601 : Blo 1413526 6051601 := bstep (se 2 (by rfl) ⟨2269350, by rfl⟩ : syracuseStep 6051601 = 4538701) B4538701
theorem B1414935 : Blo 1413526 1414935 := bstep (se 1 (by rfl) ⟨1061201, by rfl⟩ : syracuseStep 1414935 = 2122403) B2122403
theorem B2266903 : Blo 1413526 2266903 := bstep (se 1 (by rfl) ⟨1700177, by rfl⟩ : syracuseStep 2266903 = 3400355) B3400355
theorem B1414955 : Blo 1413526 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B1414967 : Blo 1413526 1414967 := bstep (se 1 (by rfl) ⟨1061225, by rfl⟩ : syracuseStep 1414967 = 2122451) B2122451
theorem B4773707 : Blo 1413526 4773707 := bstep (se 1 (by rfl) ⟨3580280, by rfl⟩ : syracuseStep 4773707 = 7160561) B7160561
theorem B1414987 : Blo 1413526 1414987 := bstep (se 1 (by rfl) ⟨1061240, by rfl⟩ : syracuseStep 1414987 = 2122481) B2122481
theorem B1414999 : Blo 1413526 1414999 := bstep (se 1 (by rfl) ⟨1061249, by rfl⟩ : syracuseStep 1414999 = 2122499) B2122499
theorem B38737763 : Blo 1413526 38737763 := bstep (se 1 (by rfl) ⟨29053322, by rfl⟩ : syracuseStep 38737763 = 58106645) B58106645
theorem B12089189 : Blo 1413526 12089189 := bstep (se 4 (by rfl) ⟨1133361, by rfl⟩ : syracuseStep 12089189 = 2266723) B2266723
theorem B1415019 : Blo 1413526 1415019 := bstep (se 1 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 1415019 = 2122529) B2122529
theorem B1415031 : Blo 1413526 1415031 := bstep (se 1 (by rfl) ⟨1061273, by rfl⟩ : syracuseStep 1415031 = 2122547) B2122547
theorem B2684801 : Blo 1413526 2684801 := bstep (se 2 (by rfl) ⟨1006800, by rfl⟩ : syracuseStep 2684801 = 2013601) B2013601
theorem B1415051 : Blo 1413526 1415051 := bstep (se 1 (by rfl) ⟨1061288, by rfl⟩ : syracuseStep 1415051 = 2122577) B2122577
theorem B3184523 : Blo 1413526 3184523 := bstep (se 1 (by rfl) ⟨2388392, by rfl⟩ : syracuseStep 3184523 = 4776785) B4776785
theorem B1415063 : Blo 1413526 1415063 := bstep (se 1 (by rfl) ⟨1061297, by rfl⟩ : syracuseStep 1415063 = 2122595) B2122595
theorem B1415083 : Blo 1413526 1415083 := bstep (se 1 (by rfl) ⟨1061312, by rfl⟩ : syracuseStep 1415083 = 2122625) B2122625
theorem B6043571 : Blo 1413526 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B1415095 : Blo 1413526 1415095 := bstep (se 1 (by rfl) ⟨1061321, by rfl⟩ : syracuseStep 1415095 = 2122643) B2122643
theorem B3184577 : Blo 1413526 3184577 := bstep (se 2 (by rfl) ⟨1194216, by rfl⟩ : syracuseStep 3184577 = 2388433) B2388433
theorem B4028363 : Blo 1413526 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B1415115 : Blo 1413526 1415115 := bstep (se 1 (by rfl) ⟨1061336, by rfl⟩ : syracuseStep 1415115 = 2122673) B2122673
theorem B1415127 : Blo 1413526 1415127 := bstep (se 1 (by rfl) ⟨1061345, by rfl⟩ : syracuseStep 1415127 = 2122691) B2122691
theorem B5371865 : Blo 1413526 5371865 := bstep (se 2 (by rfl) ⟨2014449, by rfl⟩ : syracuseStep 5371865 = 4028899) B4028899
theorem B1415147 : Blo 1413526 1415147 := bstep (se 1 (by rfl) ⟨1061360, by rfl⟩ : syracuseStep 1415147 = 2122721) B2122721
theorem B1415159 : Blo 1413526 1415159 := bstep (se 1 (by rfl) ⟨1061369, by rfl⟩ : syracuseStep 1415159 = 2122739) B2122739
theorem B1415179 : Blo 1413526 1415179 := bstep (se 1 (by rfl) ⟨1061384, by rfl⟩ : syracuseStep 1415179 = 2122769) B2122769
theorem B1415191 : Blo 1413526 1415191 := bstep (se 1 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 1415191 = 2122787) B2122787
theorem B1415211 : Blo 1413526 1415211 := bstep (se 1 (by rfl) ⟨1061408, by rfl⟩ : syracuseStep 1415211 = 2122817) B2122817
theorem B1415223 : Blo 1413526 1415223 := bstep (se 1 (by rfl) ⟨1061417, by rfl⟩ : syracuseStep 1415223 = 2122835) B2122835
theorem B1415243 : Blo 1413526 1415243 := bstep (se 1 (by rfl) ⟨1061432, by rfl⟩ : syracuseStep 1415243 = 2122865) B2122865
theorem B1415255 : Blo 1413526 1415255 := bstep (se 1 (by rfl) ⟨1061441, by rfl⟩ : syracuseStep 1415255 = 2122883) B2122883
theorem B4773977 : Blo 1413526 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B4298845 : Blo 1413526 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B1415275 : Blo 1413526 1415275 := bstep (se 1 (by rfl) ⟨1061456, by rfl⟩ : syracuseStep 1415275 = 2122913) B2122913
theorem B1415287 : Blo 1413526 1415287 := bstep (se 1 (by rfl) ⟨1061465, by rfl⟩ : syracuseStep 1415287 = 2122931) B2122931
theorem B1415307 : Blo 1413526 1415307 := bstep (se 1 (by rfl) ⟨1061480, by rfl⟩ : syracuseStep 1415307 = 2122961) B2122961
theorem B1415319 : Blo 1413526 1415319 := bstep (se 1 (by rfl) ⟨1061489, by rfl⟩ : syracuseStep 1415319 = 2122979) B2122979
theorem B3184793 : Blo 1413526 3184793 := bstep (se 2 (by rfl) ⟨1194297, by rfl⟩ : syracuseStep 3184793 = 2388595) B2388595
theorem B1415339 : Blo 1413526 1415339 := bstep (se 1 (by rfl) ⟨1061504, by rfl⟩ : syracuseStep 1415339 = 2123009) B2123009
theorem B1415351 : Blo 1413526 1415351 := bstep (se 1 (by rfl) ⟨1061513, by rfl⟩ : syracuseStep 1415351 = 2123027) B2123027
theorem B1415371 : Blo 1413526 1415371 := bstep (se 1 (by rfl) ⟨1061528, by rfl⟩ : syracuseStep 1415371 = 2123057) B2123057
theorem B2685143 : Blo 1413526 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B1415383 : Blo 1413526 1415383 := bstep (se 1 (by rfl) ⟨1061537, by rfl⟩ : syracuseStep 1415383 = 2123075) B2123075
theorem B1415403 : Blo 1413526 1415403 := bstep (se 1 (by rfl) ⟨1061552, by rfl⟩ : syracuseStep 1415403 = 2123105) B2123105
theorem B3184883 : Blo 1413526 3184883 := bstep (se 1 (by rfl) ⟨2388662, by rfl⟩ : syracuseStep 3184883 = 4777325) B4777325
theorem B1415415 : Blo 1413526 1415415 := bstep (se 1 (by rfl) ⟨1061561, by rfl⟩ : syracuseStep 1415415 = 2123123) B2123123
theorem B3021067 : Blo 1413526 3021067 := bstep (se 1 (by rfl) ⟨2265800, by rfl⟩ : syracuseStep 3021067 = 4531601) B4531601
theorem B1415435 : Blo 1413526 1415435 := bstep (se 1 (by rfl) ⟨1061576, by rfl⟩ : syracuseStep 1415435 = 2123153) B2123153
theorem B5372183 : Blo 1413526 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B1415447 : Blo 1413526 1415447 := bstep (se 1 (by rfl) ⟨1061585, by rfl⟩ : syracuseStep 1415447 = 2123171) B2123171
theorem B3184919 : Blo 1413526 3184919 := bstep (se 1 (by rfl) ⟨2388689, by rfl⟩ : syracuseStep 3184919 = 4777379) B4777379
theorem B1415467 : Blo 1413526 1415467 := bstep (se 1 (by rfl) ⟨1061600, by rfl⟩ : syracuseStep 1415467 = 2123201) B2123201
theorem B1415479 : Blo 1413526 1415479 := bstep (se 1 (by rfl) ⟨1061609, by rfl⟩ : syracuseStep 1415479 = 2123219) B2123219
theorem B3676481 : Blo 1413526 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B1415499 : Blo 1413526 1415499 := bstep (se 1 (by rfl) ⟨1061624, by rfl⟩ : syracuseStep 1415499 = 2123249) B2123249
theorem B1415511 : Blo 1413526 1415511 := bstep (se 1 (by rfl) ⟨1061633, by rfl⟩ : syracuseStep 1415511 = 2123267) B2123267
theorem B9058691 : Blo 1413526 9058691 := bstep (se 1 (by rfl) ⟨6794018, by rfl⟩ : syracuseStep 9058691 = 13588037) B13588037
theorem B16341425 : Blo 1413526 16341425 := bstep (se 2 (by rfl) ⟨6128034, by rfl⟩ : syracuseStep 16341425 = 12256069) B12256069
theorem B3021401 : Blo 1413526 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B3578519 : Blo 1413526 3578519 := bstep (se 1 (by rfl) ⟨2683889, by rfl⟩ : syracuseStep 3578519 = 5367779) B5367779
theorem B2120345 : Blo 1413526 2120345 := bstep (se 2 (by rfl) ⟨795129, by rfl⟩ : syracuseStep 2120345 = 1590259) B1590259
theorem B2120459 : Blo 1413526 2120459 := bstep (se 1 (by rfl) ⟨1590344, by rfl⟩ : syracuseStep 2120459 = 3180689) B3180689
theorem B7650065 : Blo 1413526 7650065 := bstep (se 2 (by rfl) ⟨2868774, by rfl⟩ : syracuseStep 7650065 = 5737549) B5737549
theorem B2120471 : Blo 1413526 2120471 := bstep (se 1 (by rfl) ⟨1590353, by rfl⟩ : syracuseStep 2120471 = 3180707) B3180707
theorem B4774679 : Blo 1413526 4774679 := bstep (se 1 (by rfl) ⟨3581009, by rfl⟩ : syracuseStep 4774679 = 7162019) B7162019
theorem B10189643 : Blo 1413526 10189643 := bstep (se 1 (by rfl) ⟨7642232, by rfl⟩ : syracuseStep 10189643 = 15284465) B15284465
theorem B2120537 : Blo 1413526 2120537 := bstep (se 2 (by rfl) ⟨795201, by rfl⟩ : syracuseStep 2120537 = 1590403) B1590403
theorem B2685811 : Blo 1413526 2685811 := bstep (se 1 (by rfl) ⟨2014358, by rfl⟩ : syracuseStep 2685811 = 4028717) B4028717
theorem B5372851 : Blo 1413526 5372851 := bstep (se 1 (by rfl) ⟨4029638, by rfl⟩ : syracuseStep 5372851 = 8059277) B8059277
theorem B2120651 : Blo 1413526 2120651 := bstep (se 1 (by rfl) ⟨1590488, by rfl⟩ : syracuseStep 2120651 = 3180977) B3180977
theorem B12409805 : Blo 1413526 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B2120663 : Blo 1413526 2120663 := bstep (se 1 (by rfl) ⟨1590497, by rfl⟩ : syracuseStep 2120663 = 3180995) B3180995
theorem B2120729 : Blo 1413526 2120729 := bstep (se 2 (by rfl) ⟨795273, by rfl⟩ : syracuseStep 2120729 = 1590547) B1590547
theorem B2120843 : Blo 1413526 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B2120855 : Blo 1413526 2120855 := bstep (se 1 (by rfl) ⟨1590641, by rfl⟩ : syracuseStep 2120855 = 3181283) B3181283
theorem B12082355 : Blo 1413526 12082355 := bstep (se 1 (by rfl) ⟨9061766, by rfl⟩ : syracuseStep 12082355 = 18123533) B18123533
theorem B2120921 : Blo 1413526 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B7650521 : Blo 1413526 7650521 := bstep (se 2 (by rfl) ⟨2868945, by rfl⟩ : syracuseStep 7650521 = 5737891) B5737891
theorem B3579187 : Blo 1413526 3579187 := bstep (se 1 (by rfl) ⟨2684390, by rfl⟩ : syracuseStep 3579187 = 5368781) B5368781
theorem B4775219 : Blo 1413526 4775219 := bstep (se 1 (by rfl) ⟨3581414, by rfl⟩ : syracuseStep 4775219 = 7162829) B7162829
theorem B2686259 : Blo 1413526 2686259 := bstep (se 1 (by rfl) ⟨2014694, by rfl⟩ : syracuseStep 2686259 = 4029389) B4029389
theorem B10894657 : Blo 1413526 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B2121035 : Blo 1413526 2121035 := bstep (se 1 (by rfl) ⟨1590776, by rfl⟩ : syracuseStep 2121035 = 3181553) B3181553
theorem B2121047 : Blo 1413526 2121047 := bstep (se 1 (by rfl) ⟨1590785, by rfl⟩ : syracuseStep 2121047 = 3181571) B3181571
theorem B2686297 : Blo 1413526 2686297 := bstep (se 2 (by rfl) ⟨1007361, by rfl⟩ : syracuseStep 2686297 = 2014723) B2014723
theorem B2121113 : Blo 1413526 2121113 := bstep (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) B1590835
theorem B3579329 : Blo 1413526 3579329 := bstep (se 2 (by rfl) ⟨1342248, by rfl⟩ : syracuseStep 3579329 = 2684497) B2684497
theorem B12090829 : Blo 1413526 12090829 := bstep (se 3 (by rfl) ⟨2267030, by rfl⟩ : syracuseStep 12090829 = 4534061) B4534061
theorem B2121227 : Blo 1413526 2121227 := bstep (se 1 (by rfl) ⟨1590920, by rfl⟩ : syracuseStep 2121227 = 3181841) B3181841
theorem B2121239 : Blo 1413526 2121239 := bstep (se 1 (by rfl) ⟨1590929, by rfl⟩ : syracuseStep 2121239 = 3181859) B3181859
theorem B4030003 : Blo 1413526 4030003 := bstep (se 1 (by rfl) ⟨3022502, by rfl⟩ : syracuseStep 4030003 = 6045005) B6045005
theorem B4775489 : Blo 1413526 4775489 := bstep (se 2 (by rfl) ⟨1790808, by rfl⟩ : syracuseStep 4775489 = 3581617) B3581617
theorem B3063361 : Blo 1413526 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B2121305 : Blo 1413526 2121305 := bstep (se 2 (by rfl) ⟨795489, by rfl⟩ : syracuseStep 2121305 = 1590979) B1590979
theorem B7159427 : Blo 1413526 7159427 := bstep (se 1 (by rfl) ⟨5369570, by rfl⟩ : syracuseStep 7159427 = 10739141) B10739141
theorem B2121419 : Blo 1413526 2121419 := bstep (se 1 (by rfl) ⟨1591064, by rfl⟩ : syracuseStep 2121419 = 3182129) B3182129
theorem B2121431 : Blo 1413526 2121431 := bstep (se 1 (by rfl) ⟨1591073, by rfl⟩ : syracuseStep 2121431 = 3182147) B3182147
theorem B8281873 : Blo 1413526 8281873 := bstep (se 2 (by rfl) ⟨3105702, by rfl⟩ : syracuseStep 8281873 = 6211405) B6211405
theorem B4030231 : Blo 1413526 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B2121497 : Blo 1413526 2121497 := bstep (se 2 (by rfl) ⟨795561, by rfl⟩ : syracuseStep 2121497 = 1591123) B1591123
theorem B2686745 : Blo 1413526 2686745 := bstep (se 2 (by rfl) ⟨1007529, by rfl⟩ : syracuseStep 2686745 = 2015059) B2015059
theorem B7642925 : Blo 1413526 7642925 := bstep (se 3 (by rfl) ⟨1433048, by rfl⟩ : syracuseStep 7642925 = 2866097) B2866097
theorem B5447513 : Blo 1413526 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B9068381 : Blo 1413526 9068381 := bstep (se 3 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 9068381 = 3400643) B3400643
theorem B19357541 : Blo 1413526 19357541 := bstep (se 4 (by rfl) ⟨1814769, by rfl⟩ : syracuseStep 19357541 = 3629539) B3629539
theorem B2121611 : Blo 1413526 2121611 := bstep (se 1 (by rfl) ⟨1591208, by rfl⟩ : syracuseStep 2121611 = 3182417) B3182417
theorem B2121623 : Blo 1413526 2121623 := bstep (se 1 (by rfl) ⟨1591217, by rfl⟩ : syracuseStep 2121623 = 3182435) B3182435
theorem B2121689 : Blo 1413526 2121689 := bstep (se 2 (by rfl) ⟨795633, by rfl⟩ : syracuseStep 2121689 = 1591267) B1591267
theorem B5169113 : Blo 1413526 5169113 := bstep (se 2 (by rfl) ⟨1938417, by rfl⟩ : syracuseStep 5169113 = 3876835) B3876835
theorem B2121743 : Blo 1413526 2121743 := bstep (se 1 (by rfl) ⟨1591307, by rfl⟩ : syracuseStep 2121743 = 3182615) B3182615
theorem B3579947 : Blo 1413526 3579947 := bstep (se 1 (by rfl) ⟨2684960, by rfl⟩ : syracuseStep 3579947 = 5369921) B5369921
theorem B2015275 : Blo 1413526 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B2121785 : Blo 1413526 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B2121863 : Blo 1413526 2121863 := bstep (se 1 (by rfl) ⟨1591397, by rfl⟩ : syracuseStep 2121863 = 3182795) B3182795
theorem B2867347 : Blo 1413526 2867347 := bstep (se 1 (by rfl) ⟨2150510, by rfl⟩ : syracuseStep 2867347 = 4301021) B4301021
theorem B2121899 : Blo 1413526 2121899 := bstep (se 1 (by rfl) ⟨1591424, by rfl⟩ : syracuseStep 2121899 = 3182849) B3182849
theorem B2121929 : Blo 1413526 2121929 := bstep (se 2 (by rfl) ⟨795723, by rfl⟩ : syracuseStep 2121929 = 1591447) B1591447
theorem B4776137 : Blo 1413526 4776137 := bstep (se 2 (by rfl) ⟨1791051, by rfl⟩ : syracuseStep 4776137 = 3582103) B3582103
theorem B2122043 : Blo 1413526 2122043 := bstep (se 1 (by rfl) ⟨1591532, by rfl⟩ : syracuseStep 2122043 = 3183065) B3183065
theorem B2122103 : Blo 1413526 2122103 := bstep (se 1 (by rfl) ⟨1591577, by rfl⟩ : syracuseStep 2122103 = 3183155) B3183155
theorem B8053127 : Blo 1413526 8053127 := bstep (se 1 (by rfl) ⟨6039845, by rfl⟩ : syracuseStep 8053127 = 12079691) B12079691
theorem B2548103 : Blo 1413526 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B2122127 : Blo 1413526 2122127 := bstep (se 1 (by rfl) ⟨1591595, by rfl⟩ : syracuseStep 2122127 = 3183191) B3183191
theorem B10740113 : Blo 1413526 10740113 := bstep (se 2 (by rfl) ⟨4027542, by rfl⟩ : syracuseStep 10740113 = 8055085) B8055085
theorem B2122169 : Blo 1413526 2122169 := bstep (se 2 (by rfl) ⟨795813, by rfl⟩ : syracuseStep 2122169 = 1591627) B1591627
theorem B8061443 : Blo 1413526 8061443 := bstep (se 1 (by rfl) ⟨6046082, by rfl⟩ : syracuseStep 8061443 = 12092165) B12092165
theorem B1434119 : Blo 1413526 1434119 := bstep (se 1 (by rfl) ⟨1075589, by rfl⟩ : syracuseStep 1434119 = 2151179) B2151179
theorem B2122247 : Blo 1413526 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2122283 : Blo 1413526 2122283 := bstep (se 1 (by rfl) ⟨1591712, by rfl⟩ : syracuseStep 2122283 = 3183425) B3183425
theorem B2122313 : Blo 1413526 2122313 := bstep (se 2 (by rfl) ⟨795867, by rfl⟩ : syracuseStep 2122313 = 1591735) B1591735
theorem B3400307 : Blo 1413526 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B2122427 : Blo 1413526 2122427 := bstep (se 1 (by rfl) ⟨1591820, by rfl⟩ : syracuseStep 2122427 = 3183641) B3183641
theorem B3400393 : Blo 1413526 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B30999257 : Blo 1413526 30999257 := bstep (se 2 (by rfl) ⟨11624721, by rfl⟩ : syracuseStep 30999257 = 23249443) B23249443
theorem B2122487 : Blo 1413526 2122487 := bstep (se 1 (by rfl) ⟨1591865, by rfl⟩ : syracuseStep 2122487 = 3183731) B3183731
theorem B4080395 : Blo 1413526 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B2122511 : Blo 1413526 2122511 := bstep (se 1 (by rfl) ⟨1591883, by rfl⟩ : syracuseStep 2122511 = 3183767) B3183767
theorem B2122553 : Blo 1413526 2122553 := bstep (se 2 (by rfl) ⟨795957, by rfl⟩ : syracuseStep 2122553 = 1591915) B1591915
theorem B13591385 : Blo 1413526 13591385 := bstep (se 2 (by rfl) ⟨5096769, by rfl⟩ : syracuseStep 13591385 = 10193539) B10193539
theorem B3580787 : Blo 1413526 3580787 := bstep (se 1 (by rfl) ⟨2685590, by rfl⟩ : syracuseStep 3580787 = 5371181) B5371181
theorem B3580807 : Blo 1413526 3580807 := bstep (se 1 (by rfl) ⟨2685605, by rfl⟩ : syracuseStep 3580807 = 5371211) B5371211
theorem B2122631 : Blo 1413526 2122631 := bstep (se 1 (by rfl) ⟨1591973, by rfl⟩ : syracuseStep 2122631 = 3183947) B3183947
theorem B4776839 : Blo 1413526 4776839 := bstep (se 1 (by rfl) ⟨3582629, by rfl⟩ : syracuseStep 4776839 = 7165259) B7165259
theorem B7160723 : Blo 1413526 7160723 := bstep (se 1 (by rfl) ⟨5370542, by rfl⟩ : syracuseStep 7160723 = 10741085) B10741085
theorem B2122667 : Blo 1413526 2122667 := bstep (se 1 (by rfl) ⟨1592000, by rfl⟩ : syracuseStep 2122667 = 3184001) B3184001
theorem B2122697 : Blo 1413526 2122697 := bstep (se 2 (by rfl) ⟨796011, by rfl⟩ : syracuseStep 2122697 = 1592023) B1592023
theorem B1590331 : Blo 1413526 1590331 := bstep (se 1 (by rfl) ⟨1192748, by rfl⟩ : syracuseStep 1590331 = 2385497) B2385497
theorem B2548795 : Blo 1413526 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B2122811 : Blo 1413526 2122811 := bstep (se 1 (by rfl) ⟨1592108, by rfl⟩ : syracuseStep 2122811 = 3184217) B3184217
theorem B2122871 : Blo 1413526 2122871 := bstep (se 1 (by rfl) ⟨1592153, by rfl⟩ : syracuseStep 2122871 = 3184307) B3184307
theorem B2122895 : Blo 1413526 2122895 := bstep (se 1 (by rfl) ⟨1592171, by rfl⟩ : syracuseStep 2122895 = 3184343) B3184343
theorem B2548883 : Blo 1413526 2548883 := bstep (se 1 (by rfl) ⟨1911662, by rfl⟩ : syracuseStep 2548883 = 3823325) B3823325
theorem B3581081 : Blo 1413526 3581081 := bstep (se 2 (by rfl) ⟨1342905, by rfl⟩ : syracuseStep 3581081 = 2685811) B2685811
theorem B2122937 : Blo 1413526 2122937 := bstep (se 2 (by rfl) ⟨796101, by rfl⟩ : syracuseStep 2122937 = 1592203) B1592203
theorem B4777217 : Blo 1413526 4777217 := bstep (se 2 (by rfl) ⟨1791456, by rfl⟩ : syracuseStep 4777217 = 3582913) B3582913
theorem B2123015 : Blo 1413526 2123015 := bstep (se 1 (by rfl) ⟨1592261, by rfl⟩ : syracuseStep 2123015 = 3184523) B3184523
theorem B2123051 : Blo 1413526 2123051 := bstep (se 1 (by rfl) ⟨1592288, by rfl⟩ : syracuseStep 2123051 = 3184577) B3184577
theorem B3581243 : Blo 1413526 3581243 := bstep (se 1 (by rfl) ⟨2685932, by rfl⟩ : syracuseStep 3581243 = 5371865) B5371865
theorem B2123081 : Blo 1413526 2123081 := bstep (se 2 (by rfl) ⟨796155, by rfl⟩ : syracuseStep 2123081 = 1592311) B1592311
theorem B2123195 : Blo 1413526 2123195 := bstep (se 1 (by rfl) ⟨1592396, by rfl⟩ : syracuseStep 2123195 = 3184793) B3184793
theorem B2123255 : Blo 1413526 2123255 := bstep (se 1 (by rfl) ⟨1592441, by rfl⟩ : syracuseStep 2123255 = 3184883) B3184883
theorem B1590799 : Blo 1413526 1590799 := bstep (se 1 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 1590799 = 2386199) B2386199
theorem B3581455 : Blo 1413526 3581455 := bstep (se 1 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 3581455 = 5372183) B5372183
theorem B2123279 : Blo 1413526 2123279 := bstep (se 1 (by rfl) ⟨1592459, by rfl⟩ : syracuseStep 2123279 = 3184919) B3184919
theorem B2450987 : Blo 1413526 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B6039127 : Blo 1413526 6039127 := bstep (se 1 (by rfl) ⟨4529345, by rfl⟩ : syracuseStep 6039127 = 9058691) B9058691
theorem B5736023 : Blo 1413526 5736023 := bstep (se 1 (by rfl) ⟨4302017, by rfl⟩ : syracuseStep 5736023 = 8604035) B8604035
theorem B3491443 : Blo 1413526 3491443 := bstep (se 1 (by rfl) ⟨2618582, by rfl⟩ : syracuseStep 3491443 = 5237165) B5237165
theorem B14526209 : Blo 1413526 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B2385679 : Blo 1413526 2385679 := bstep (se 1 (by rfl) ⟨1789259, by rfl⟩ : syracuseStep 2385679 = 3578519) B3578519
theorem B3581729 : Blo 1413526 3581729 := bstep (se 2 (by rfl) ⟨1343148, by rfl⟩ : syracuseStep 3581729 = 2686297) B2686297
theorem B5097275 : Blo 1413526 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B5736251 : Blo 1413526 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B12912473 : Blo 1413526 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B2869139 : Blo 1413526 2869139 := bstep (se 1 (by rfl) ⟨2151854, by rfl⟩ : syracuseStep 2869139 = 4303709) B4303709
theorem B3180473 : Blo 1413526 3180473 := bstep (se 2 (by rfl) ⟨1192677, by rfl⟩ : syracuseStep 3180473 = 2385355) B2385355
theorem B1591303 : Blo 1413526 1591303 := bstep (se 1 (by rfl) ⟨1193477, by rfl⟩ : syracuseStep 1591303 = 2386955) B2386955
theorem B8054903 : Blo 1413526 8054903 := bstep (se 1 (by rfl) ⟨6041177, by rfl⟩ : syracuseStep 8054903 = 12082355) B12082355
theorem B1591483 : Blo 1413526 1591483 := bstep (se 1 (by rfl) ⟨1193612, by rfl⟩ : syracuseStep 1591483 = 2387225) B2387225
theorem B3180815 : Blo 1413526 3180815 := bstep (se 1 (by rfl) ⟨2385611, by rfl⟩ : syracuseStep 3180815 = 4771223) B4771223
theorem B3180833 : Blo 1413526 3180833 := bstep (se 2 (by rfl) ⟨1192812, by rfl⟩ : syracuseStep 3180833 = 2385625) B2385625
theorem B2386219 : Blo 1413526 2386219 := bstep (se 1 (by rfl) ⟨1789664, by rfl⟩ : syracuseStep 2386219 = 3579329) B3579329
theorem B17205635 : Blo 1413526 17205635 := bstep (se 1 (by rfl) ⟨12904226, by rfl⟩ : syracuseStep 17205635 = 25808453) B25808453
theorem B2386361 : Blo 1413526 2386361 := bstep (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) B1789771
theorem B3631675 : Blo 1413526 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B12905027 : Blo 1413526 12905027 := bstep (se 1 (by rfl) ⟨9678770, by rfl⟩ : syracuseStep 12905027 = 19357541) B19357541
theorem B3181175 : Blo 1413526 3181175 := bstep (se 1 (by rfl) ⟨2385881, by rfl⟩ : syracuseStep 3181175 = 4771763) B4771763
theorem B1591951 : Blo 1413526 1591951 := bstep (se 1 (by rfl) ⟨1193963, by rfl⟩ : syracuseStep 1591951 = 2387927) B2387927
theorem B3582731 : Blo 1413526 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B10742543 : Blo 1413526 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B3181355 : Blo 1413526 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B8055611 : Blo 1413526 8055611 := bstep (se 1 (by rfl) ⟨6041708, by rfl⟩ : syracuseStep 8055611 = 12083417) B12083417
theorem B4770845 : Blo 1413526 4770845 := bstep (se 3 (by rfl) ⟨894533, by rfl⟩ : syracuseStep 4770845 = 1789067) B1789067
theorem B2387063 : Blo 1413526 2387063 := bstep (se 1 (by rfl) ⟨1790297, by rfl⟩ : syracuseStep 2387063 = 3580595) B3580595
theorem B1592455 : Blo 1413526 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B3181715 : Blo 1413526 3181715 := bstep (se 1 (by rfl) ⟨2386286, by rfl⟩ : syracuseStep 3181715 = 4772573) B4772573
theorem B3181769 : Blo 1413526 3181769 := bstep (se 2 (by rfl) ⟨1193163, by rfl⟩ : syracuseStep 3181769 = 2386327) B2386327
theorem B4025629 : Blo 1413526 4025629 := bstep (se 3 (by rfl) ⟨754805, by rfl⟩ : syracuseStep 4025629 = 1509611) B1509611
theorem B1813903 : Blo 1413526 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B6450617 : Blo 1413526 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B4025801 : Blo 1413526 4025801 := bstep (se 2 (by rfl) ⟨1509675, by rfl⟩ : syracuseStep 4025801 = 3019351) B3019351
theorem B4025857 : Blo 1413526 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B1789447 : Blo 1413526 1789447 := bstep (se 1 (by rfl) ⟨1342085, by rfl⟩ : syracuseStep 1789447 = 2684171) B2684171
theorem B2264635 : Blo 1413526 2264635 := bstep (se 1 (by rfl) ⟨1698476, by rfl⟩ : syracuseStep 2264635 = 3396953) B3396953
theorem B2387515 : Blo 1413526 2387515 := bstep (se 1 (by rfl) ⟨1790636, by rfl⟩ : syracuseStep 2387515 = 3581273) B3581273
theorem B13586039 : Blo 1413526 13586039 := bstep (se 1 (by rfl) ⟨10189529, by rfl⟩ : syracuseStep 13586039 = 20379059) B20379059
theorem B18132659 : Blo 1413526 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B2387657 : Blo 1413526 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B1511183 : Blo 1413526 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B11472691 : Blo 1413526 11472691 := bstep (se 1 (by rfl) ⟨8604518, by rfl⟩ : syracuseStep 11472691 = 17209037) B17209037
theorem B4026199 : Blo 1413526 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B3182471 : Blo 1413526 3182471 := bstep (se 1 (by rfl) ⟨2386853, by rfl⟩ : syracuseStep 3182471 = 4773707) B4773707
theorem B25825175 : Blo 1413526 25825175 := bstep (se 1 (by rfl) ⟨19368881, by rfl⟩ : syracuseStep 25825175 = 38737763) B38737763
theorem B5369753 : Blo 1413526 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B7163801 : Blo 1413526 7163801 := bstep (se 2 (by rfl) ⟨2686425, by rfl⟩ : syracuseStep 7163801 = 5372851) B5372851
theorem B1789867 : Blo 1413526 1789867 := bstep (se 1 (by rfl) ⟨1342400, by rfl⟩ : syracuseStep 1789867 = 2684801) B2684801
theorem B3182651 : Blo 1413526 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B1790095 : Blo 1413526 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B3182777 : Blo 1413526 3182777 := bstep (se 2 (by rfl) ⟨1193541, by rfl⟩ : syracuseStep 3182777 = 2387083) B2387083
theorem B8057069 : Blo 1413526 8057069 := bstep (se 3 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 8057069 = 3021401) B3021401
theorem B2388359 : Blo 1413526 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B4772249 : Blo 1413526 4772249 := bstep (se 2 (by rfl) ⟨1789593, by rfl⟩ : syracuseStep 4772249 = 3579187) B3579187
theorem B1413563 : Blo 1413526 1413563 := bstep (se 1 (by rfl) ⟨1060172, by rfl⟩ : syracuseStep 1413563 = 2120345) B2120345
theorem B2265545 : Blo 1413526 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B1413639 : Blo 1413526 1413639 := bstep (se 1 (by rfl) ⟨1060229, by rfl⟩ : syracuseStep 1413639 = 2120459) B2120459
theorem B5100043 : Blo 1413526 5100043 := bstep (se 1 (by rfl) ⟨3825032, by rfl⟩ : syracuseStep 5100043 = 7650065) B7650065
theorem B1413647 : Blo 1413526 1413647 := bstep (se 1 (by rfl) ⟨1060235, by rfl⟩ : syracuseStep 1413647 = 2120471) B2120471
theorem B3183119 : Blo 1413526 3183119 := bstep (se 1 (by rfl) ⟨2387339, by rfl⟩ : syracuseStep 3183119 = 4774679) B4774679
theorem B3183137 : Blo 1413526 3183137 := bstep (se 2 (by rfl) ⟨1193676, by rfl⟩ : syracuseStep 3183137 = 2387353) B2387353
theorem B1413691 : Blo 1413526 1413691 := bstep (se 1 (by rfl) ⟨1060268, by rfl⟩ : syracuseStep 1413691 = 2120537) B2120537
theorem B1413767 : Blo 1413526 1413767 := bstep (se 1 (by rfl) ⟨1060325, by rfl⟩ : syracuseStep 1413767 = 2120651) B2120651
theorem B1413775 : Blo 1413526 1413775 := bstep (se 1 (by rfl) ⟨1060331, by rfl⟩ : syracuseStep 1413775 = 2120663) B2120663
theorem B1413819 : Blo 1413526 1413819 := bstep (se 1 (by rfl) ⟨1060364, by rfl⟩ : syracuseStep 1413819 = 2120729) B2120729
theorem B6451969 : Blo 1413526 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B4084481 : Blo 1413526 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1413895 : Blo 1413526 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B1413903 : Blo 1413526 1413903 := bstep (se 1 (by rfl) ⟨1060427, by rfl⟩ : syracuseStep 1413903 = 2120855) B2120855
theorem B24179471 : Blo 1413526 24179471 := bstep (se 1 (by rfl) ⟨18134603, by rfl⟩ : syracuseStep 24179471 = 36269207) B36269207
theorem B1413947 : Blo 1413526 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B5100347 : Blo 1413526 5100347 := bstep (se 1 (by rfl) ⟨3825260, by rfl⟩ : syracuseStep 5100347 = 7650521) B7650521
theorem B3183479 : Blo 1413526 3183479 := bstep (se 1 (by rfl) ⟨2387609, by rfl⟩ : syracuseStep 3183479 = 4775219) B4775219
theorem B1790839 : Blo 1413526 1790839 := bstep (se 1 (by rfl) ⟨1343129, by rfl⟩ : syracuseStep 1790839 = 2686259) B2686259
theorem B2683783 : Blo 1413526 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B1414023 : Blo 1413526 1414023 := bstep (se 1 (by rfl) ⟨1060517, by rfl⟩ : syracuseStep 1414023 = 2121035) B2121035
theorem B1414031 : Blo 1413526 1414031 := bstep (se 1 (by rfl) ⟨1060523, by rfl⟩ : syracuseStep 1414031 = 2121047) B2121047
theorem B1414075 : Blo 1413526 1414075 := bstep (se 1 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 1414075 = 2121113) B2121113
theorem B2266057 : Blo 1413526 2266057 := bstep (se 2 (by rfl) ⟨849771, by rfl⟩ : syracuseStep 2266057 = 1699543) B1699543
theorem B1414151 : Blo 1413526 1414151 := bstep (se 1 (by rfl) ⟨1060613, by rfl⟩ : syracuseStep 1414151 = 2121227) B2121227
theorem B1414159 : Blo 1413526 1414159 := bstep (se 1 (by rfl) ⟨1060619, by rfl⟩ : syracuseStep 1414159 = 2121239) B2121239
theorem B3183659 : Blo 1413526 3183659 := bstep (se 1 (by rfl) ⟨2387744, by rfl⟩ : syracuseStep 3183659 = 4775489) B4775489
theorem B1414203 : Blo 1413526 1414203 := bstep (se 1 (by rfl) ⟨1060652, by rfl⟩ : syracuseStep 1414203 = 2121305) B2121305
theorem B4772951 : Blo 1413526 4772951 := bstep (se 1 (by rfl) ⟨3579713, by rfl⟩ : syracuseStep 4772951 = 7159427) B7159427
theorem B1414279 : Blo 1413526 1414279 := bstep (se 1 (by rfl) ⟨1060709, by rfl⟩ : syracuseStep 1414279 = 2121419) B2121419
theorem B1414287 : Blo 1413526 1414287 := bstep (se 1 (by rfl) ⟨1060715, by rfl⟩ : syracuseStep 1414287 = 2121431) B2121431
theorem B1414331 : Blo 1413526 1414331 := bstep (se 1 (by rfl) ⟨1060748, by rfl⟩ : syracuseStep 1414331 = 2121497) B2121497
theorem B1791163 : Blo 1413526 1791163 := bstep (se 1 (by rfl) ⟨1343372, by rfl⟩ : syracuseStep 1791163 = 2686745) B2686745
theorem B2266313 : Blo 1413526 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B33092813 : Blo 1413526 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B1414407 : Blo 1413526 1414407 := bstep (se 1 (by rfl) ⟨1060805, by rfl⟩ : syracuseStep 1414407 = 2121611) B2121611
theorem B1414415 : Blo 1413526 1414415 := bstep (se 1 (by rfl) ⟨1060811, by rfl⟩ : syracuseStep 1414415 = 2121623) B2121623
theorem B1414459 : Blo 1413526 1414459 := bstep (se 1 (by rfl) ⟨1060844, by rfl⟩ : syracuseStep 1414459 = 2121689) B2121689
theorem B3446075 : Blo 1413526 3446075 := bstep (se 1 (by rfl) ⟨2584556, by rfl⟩ : syracuseStep 3446075 = 5169113) B5169113
theorem B7255385 : Blo 1413526 7255385 := bstep (se 2 (by rfl) ⟨2720769, by rfl⟩ : syracuseStep 7255385 = 5441539) B5441539
theorem B1414535 : Blo 1413526 1414535 := bstep (se 1 (by rfl) ⟨1060901, by rfl⟩ : syracuseStep 1414535 = 2121803) B2121803
theorem B1414543 : Blo 1413526 1414543 := bstep (se 1 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 1414543 = 2121815) B2121815
theorem B3020179 : Blo 1413526 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B3184019 : Blo 1413526 3184019 := bstep (se 1 (by rfl) ⟨2388014, by rfl⟩ : syracuseStep 3184019 = 4776029) B4776029
theorem B3397049 : Blo 1413526 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B5813689 : Blo 1413526 5813689 := bstep (se 2 (by rfl) ⟨2180133, by rfl⟩ : syracuseStep 5813689 = 4360267) B4360267
theorem B1414587 : Blo 1413526 1414587 := bstep (se 1 (by rfl) ⟨1060940, by rfl⟩ : syracuseStep 1414587 = 2121881) B2121881
theorem B3184073 : Blo 1413526 3184073 := bstep (se 2 (by rfl) ⟨1194027, by rfl⟩ : syracuseStep 3184073 = 2388055) B2388055
theorem B5731793 : Blo 1413526 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B11777501 : Blo 1413526 11777501 := bstep (se 3 (by rfl) ⟨2208281, by rfl⟩ : syracuseStep 11777501 = 4416563) B4416563
theorem B1414663 : Blo 1413526 1414663 := bstep (se 1 (by rfl) ⟨1060997, by rfl⟩ : syracuseStep 1414663 = 2121995) B2121995
theorem B1414671 : Blo 1413526 1414671 := bstep (se 1 (by rfl) ⟨1061003, by rfl⟩ : syracuseStep 1414671 = 2122007) B2122007
theorem B8599069 : Blo 1413526 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B1414715 : Blo 1413526 1414715 := bstep (se 1 (by rfl) ⟨1061036, by rfl⟩ : syracuseStep 1414715 = 2122073) B2122073
theorem B4773437 : Blo 1413526 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B1414791 : Blo 1413526 1414791 := bstep (se 1 (by rfl) ⟨1061093, by rfl⟩ : syracuseStep 1414791 = 2122187) B2122187
theorem B1414799 : Blo 1413526 1414799 := bstep (se 1 (by rfl) ⟨1061099, by rfl⟩ : syracuseStep 1414799 = 2122199) B2122199
theorem B27186839 : Blo 1413526 27186839 := bstep (se 1 (by rfl) ⟨20390129, by rfl⟩ : syracuseStep 27186839 = 40780259) B40780259
theorem B1414843 : Blo 1413526 1414843 := bstep (se 1 (by rfl) ⟨1061132, by rfl⟩ : syracuseStep 1414843 = 2122265) B2122265
theorem B1414919 : Blo 1413526 1414919 := bstep (se 1 (by rfl) ⟨1061189, by rfl⟩ : syracuseStep 1414919 = 2122379) B2122379
theorem B1414927 : Blo 1413526 1414927 := bstep (se 1 (by rfl) ⟨1061195, by rfl⟩ : syracuseStep 1414927 = 2122391) B2122391
theorem B1414971 : Blo 1413526 1414971 := bstep (se 1 (by rfl) ⟨1061228, by rfl⟩ : syracuseStep 1414971 = 2122457) B2122457
theorem B1415047 : Blo 1413526 1415047 := bstep (se 1 (by rfl) ⟨1061285, by rfl⟩ : syracuseStep 1415047 = 2122571) B2122571
theorem B1415055 : Blo 1413526 1415055 := bstep (se 1 (by rfl) ⟨1061291, by rfl⟩ : syracuseStep 1415055 = 2122583) B2122583
theorem B1415099 : Blo 1413526 1415099 := bstep (se 1 (by rfl) ⟨1061324, by rfl⟩ : syracuseStep 1415099 = 2122649) B2122649
theorem B1415175 : Blo 1413526 1415175 := bstep (se 1 (by rfl) ⟨1061381, by rfl⟩ : syracuseStep 1415175 = 2122763) B2122763
theorem B1415183 : Blo 1413526 1415183 := bstep (se 1 (by rfl) ⟨1061387, by rfl⟩ : syracuseStep 1415183 = 2122775) B2122775
theorem B8050711 : Blo 1413526 8050711 := bstep (se 1 (by rfl) ⟨6038033, by rfl⟩ : syracuseStep 8050711 = 12076067) B12076067
theorem B1415227 : Blo 1413526 1415227 := bstep (se 1 (by rfl) ⟨1061420, by rfl⟩ : syracuseStep 1415227 = 2122841) B2122841
theorem B4085819 : Blo 1413526 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B1415303 : Blo 1413526 1415303 := bstep (se 1 (by rfl) ⟨1061477, by rfl⟩ : syracuseStep 1415303 = 2122955) B2122955
theorem B3184775 : Blo 1413526 3184775 := bstep (se 1 (by rfl) ⟨2388581, by rfl⟩ : syracuseStep 3184775 = 4777163) B4777163
theorem B1415311 : Blo 1413526 1415311 := bstep (se 1 (by rfl) ⟨1061483, by rfl⟩ : syracuseStep 1415311 = 2122967) B2122967
theorem B3578003 : Blo 1413526 3578003 := bstep (se 1 (by rfl) ⟨2683502, by rfl⟩ : syracuseStep 3578003 = 5367005) B5367005
theorem B1415355 : Blo 1413526 1415355 := bstep (se 1 (by rfl) ⟨1061516, by rfl⟩ : syracuseStep 1415355 = 2123033) B2123033
theorem B1415431 : Blo 1413526 1415431 := bstep (se 1 (by rfl) ⟨1061573, by rfl⟩ : syracuseStep 1415431 = 2123147) B2123147
theorem B8722703 : Blo 1413526 8722703 := bstep (se 1 (by rfl) ⟨6542027, by rfl⟩ : syracuseStep 8722703 = 13084055) B13084055
theorem B1415439 : Blo 1413526 1415439 := bstep (se 1 (by rfl) ⟨1061579, by rfl⟩ : syracuseStep 1415439 = 2123159) B2123159
theorem B43538705 : Blo 1413526 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B1415483 : Blo 1413526 1415483 := bstep (se 1 (by rfl) ⟨1061612, by rfl⟩ : syracuseStep 1415483 = 2123225) B2123225
theorem B7158131 : Blo 1413526 7158131 := bstep (se 1 (by rfl) ⟨5368598, by rfl⟩ : syracuseStep 7158131 = 10737197) B10737197
theorem B14522759 : Blo 1413526 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B6797789 : Blo 1413526 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B8059459 : Blo 1413526 8059459 := bstep (se 1 (by rfl) ⟨6044594, by rfl⟩ : syracuseStep 8059459 = 12089189) B12089189
theorem B4029047 : Blo 1413526 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B2120327 : Blo 1413526 2120327 := bstep (se 1 (by rfl) ⟨1590245, by rfl⟩ : syracuseStep 2120327 = 3180491) B3180491
theorem B2685575 : Blo 1413526 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B2120363 : Blo 1413526 2120363 := bstep (se 1 (by rfl) ⟨1590272, by rfl⟩ : syracuseStep 2120363 = 3180545) B3180545
theorem B2120393 : Blo 1413526 2120393 := bstep (se 2 (by rfl) ⟨795147, by rfl⟩ : syracuseStep 2120393 = 1590295) B1590295
theorem B16112357 : Blo 1413526 16112357 := bstep (se 4 (by rfl) ⟨1510533, by rfl⟩ : syracuseStep 16112357 = 3021067) B3021067
theorem B32275205 : Blo 1413526 32275205 := bstep (se 4 (by rfl) ⟨3025800, by rfl⟩ : syracuseStep 32275205 = 6051601) B6051601
theorem B2120507 : Blo 1413526 2120507 := bstep (se 1 (by rfl) ⟨1590380, by rfl⟩ : syracuseStep 2120507 = 3180761) B3180761
theorem B7158617 : Blo 1413526 7158617 := bstep (se 2 (by rfl) ⟨2684481, by rfl⟩ : syracuseStep 7158617 = 5368963) B5368963
theorem B4299635 : Blo 1413526 4299635 := bstep (se 1 (by rfl) ⟨3224726, by rfl⟩ : syracuseStep 4299635 = 6449453) B6449453
theorem B2120567 : Blo 1413526 2120567 := bstep (se 1 (by rfl) ⟨1590425, by rfl⟩ : syracuseStep 2120567 = 3180851) B3180851
theorem B2120591 : Blo 1413526 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B2120633 : Blo 1413526 2120633 := bstep (se 2 (by rfl) ⟨795237, by rfl⟩ : syracuseStep 2120633 = 1590475) B1590475
theorem B4774841 : Blo 1413526 4774841 := bstep (se 2 (by rfl) ⟨1790565, by rfl⟩ : syracuseStep 4774841 = 3581131) B3581131
theorem B10894283 : Blo 1413526 10894283 := bstep (se 1 (by rfl) ⟨8170712, by rfl⟩ : syracuseStep 10894283 = 16341425) B16341425
theorem B2120711 : Blo 1413526 2120711 := bstep (se 1 (by rfl) ⟨1590533, by rfl⟩ : syracuseStep 2120711 = 3181067) B3181067
theorem B2120747 : Blo 1413526 2120747 := bstep (se 1 (by rfl) ⟨1590560, by rfl⟩ : syracuseStep 2120747 = 3181121) B3181121
theorem B2120777 : Blo 1413526 2120777 := bstep (se 2 (by rfl) ⟨795291, by rfl⟩ : syracuseStep 2120777 = 1590583) B1590583
theorem B2120891 : Blo 1413526 2120891 := bstep (se 1 (by rfl) ⟨1590668, by rfl⟩ : syracuseStep 2120891 = 3181337) B3181337
theorem B2120951 : Blo 1413526 2120951 := bstep (se 1 (by rfl) ⟨1590713, by rfl⟩ : syracuseStep 2120951 = 3181427) B3181427
theorem B3579137 : Blo 1413526 3579137 := bstep (se 2 (by rfl) ⟨1342176, by rfl⟩ : syracuseStep 3579137 = 2684353) B2684353
theorem B2120975 : Blo 1413526 2120975 := bstep (se 1 (by rfl) ⟨1590731, by rfl⟩ : syracuseStep 2120975 = 3181463) B3181463
theorem B16121105 : Blo 1413526 16121105 := bstep (se 2 (by rfl) ⟨6045414, by rfl⟩ : syracuseStep 16121105 = 12090829) B12090829
theorem B30580001 : Blo 1413526 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B2121017 : Blo 1413526 2121017 := bstep (se 2 (by rfl) ⟨795381, by rfl⟩ : syracuseStep 2121017 = 1590763) B1590763
theorem B2121095 : Blo 1413526 2121095 := bstep (se 1 (by rfl) ⟨1590821, by rfl⟩ : syracuseStep 2121095 = 3181643) B3181643
theorem B5373337 : Blo 1413526 5373337 := bstep (se 2 (by rfl) ⟨2015001, by rfl⟩ : syracuseStep 5373337 = 4030003) B4030003
theorem B2121131 : Blo 1413526 2121131 := bstep (se 1 (by rfl) ⟨1590848, by rfl⟩ : syracuseStep 2121131 = 3181697) B3181697
theorem B2121161 : Blo 1413526 2121161 := bstep (se 2 (by rfl) ⟨795435, by rfl⟩ : syracuseStep 2121161 = 1590871) B1590871
theorem B4775435 : Blo 1413526 4775435 := bstep (se 1 (by rfl) ⟨3581576, by rfl⟩ : syracuseStep 4775435 = 7163153) B7163153
theorem B27172381 : Blo 1413526 27172381 := bstep (se 3 (by rfl) ⟨5094821, by rfl⟩ : syracuseStep 27172381 = 10189643) B10189643
theorem B2121275 : Blo 1413526 2121275 := bstep (se 1 (by rfl) ⟨1590956, by rfl⟩ : syracuseStep 2121275 = 3181913) B3181913
theorem B5733949 : Blo 1413526 5733949 := bstep (se 3 (by rfl) ⟨1075115, by rfl⟩ : syracuseStep 5733949 = 2150231) B2150231
theorem B4529783 : Blo 1413526 4529783 := bstep (se 1 (by rfl) ⟨3397337, by rfl⟩ : syracuseStep 4529783 = 6794675) B6794675
theorem B3579511 : Blo 1413526 3579511 := bstep (se 1 (by rfl) ⟨2684633, by rfl⟩ : syracuseStep 3579511 = 5369267) B5369267
theorem B2121335 : Blo 1413526 2121335 := bstep (se 1 (by rfl) ⟨1591001, by rfl⟩ : syracuseStep 2121335 = 3182003) B3182003
theorem B4775543 : Blo 1413526 4775543 := bstep (se 1 (by rfl) ⟨3581657, by rfl⟩ : syracuseStep 4775543 = 7163315) B7163315
theorem B2121359 : Blo 1413526 2121359 := bstep (se 1 (by rfl) ⟨1591019, by rfl⟩ : syracuseStep 2121359 = 3182039) B3182039
theorem B2121401 : Blo 1413526 2121401 := bstep (se 2 (by rfl) ⟨795525, by rfl⟩ : syracuseStep 2121401 = 1591051) B1591051
theorem B11042497 : Blo 1413526 11042497 := bstep (se 2 (by rfl) ⟨4140936, by rfl⟩ : syracuseStep 11042497 = 8281873) B8281873
theorem B3022537 : Blo 1413526 3022537 := bstep (se 2 (by rfl) ⟨1133451, by rfl⟩ : syracuseStep 3022537 = 2266903) B2266903
theorem B5373641 : Blo 1413526 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B2121479 : Blo 1413526 2121479 := bstep (se 1 (by rfl) ⟨1591109, by rfl⟩ : syracuseStep 2121479 = 3182219) B3182219
theorem B5168929 : Blo 1413526 5168929 := bstep (se 2 (by rfl) ⟨1938348, by rfl⟩ : syracuseStep 5168929 = 3876697) B3876697
theorem B2121515 : Blo 1413526 2121515 := bstep (se 1 (by rfl) ⟨1591136, by rfl⟩ : syracuseStep 2121515 = 3182273) B3182273
theorem B2121545 : Blo 1413526 2121545 := bstep (se 2 (by rfl) ⟨795579, by rfl⟩ : syracuseStep 2121545 = 1591159) B1591159
theorem B4300631 : Blo 1413526 4300631 := bstep (se 1 (by rfl) ⟨3225473, by rfl⟩ : syracuseStep 4300631 = 6450947) B6450947
theorem B5095283 : Blo 1413526 5095283 := bstep (se 1 (by rfl) ⟨3821462, by rfl⟩ : syracuseStep 5095283 = 7642925) B7642925
theorem B6045587 : Blo 1413526 6045587 := bstep (se 1 (by rfl) ⟨4534190, by rfl⟩ : syracuseStep 6045587 = 9068381) B9068381
theorem B20406167 : Blo 1413526 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B2121659 : Blo 1413526 2121659 := bstep (se 1 (by rfl) ⟨1591244, by rfl⟩ : syracuseStep 2121659 = 3182489) B3182489
theorem B2121719 : Blo 1413526 2121719 := bstep (se 1 (by rfl) ⟨1591289, by rfl⟩ : syracuseStep 2121719 = 3182579) B3182579
theorem B2121737 : Blo 1413526 2121737 := bstep (se 2 (by rfl) ⟨795651, by rfl⟩ : syracuseStep 2121737 = 1591303) B1591303
theorem B2121767 : Blo 1413526 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B2687033 : Blo 1413526 2687033 := bstep (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) B2015275
theorem B2121851 : Blo 1413526 2121851 := bstep (se 1 (by rfl) ⟨1591388, by rfl⟩ : syracuseStep 2121851 = 3182777) B3182777
theorem B2121977 : Blo 1413526 2121977 := bstep (se 2 (by rfl) ⟨795741, by rfl⟩ : syracuseStep 2121977 = 1591483) B1591483
theorem B7160075 : Blo 1413526 7160075 := bstep (se 1 (by rfl) ⟨5370056, by rfl⟩ : syracuseStep 7160075 = 10740113) B10740113
theorem B5374295 : Blo 1413526 5374295 := bstep (se 1 (by rfl) ⟨4030721, by rfl⟩ : syracuseStep 5374295 = 8061443) B8061443
theorem B2122079 : Blo 1413526 2122079 := bstep (se 1 (by rfl) ⟨1591559, by rfl⟩ : syracuseStep 2122079 = 3183119) B3183119
theorem B2122091 : Blo 1413526 2122091 := bstep (se 1 (by rfl) ⟨1591568, by rfl⟩ : syracuseStep 2122091 = 3183137) B3183137
theorem B3400231 : Blo 1413526 3400231 := bstep (se 1 (by rfl) ⟨2550173, by rfl⟩ : syracuseStep 3400231 = 5100347) B5100347
theorem B9060923 : Blo 1413526 9060923 := bstep (se 1 (by rfl) ⟨6795692, by rfl⟩ : syracuseStep 9060923 = 13591385) B13591385
theorem B2122319 : Blo 1413526 2122319 := bstep (se 1 (by rfl) ⟨1591739, by rfl⟩ : syracuseStep 2122319 = 3183479) B3183479
theorem B18621029 : Blo 1413526 18621029 := bstep (se 4 (by rfl) ⟨1745721, by rfl⟩ : syracuseStep 18621029 = 3491443) B3491443
theorem B6800057 : Blo 1413526 6800057 := bstep (se 2 (by rfl) ⟨2550021, by rfl⟩ : syracuseStep 6800057 = 5100043) B5100043
theorem B2122439 : Blo 1413526 2122439 := bstep (se 1 (by rfl) ⟨1591829, by rfl⟩ : syracuseStep 2122439 = 3183659) B3183659
theorem B4842233 : Blo 1413526 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B2122601 : Blo 1413526 2122601 := bstep (se 2 (by rfl) ⟨795975, by rfl⟩ : syracuseStep 2122601 = 1591951) B1591951
theorem B2122679 : Blo 1413526 2122679 := bstep (se 1 (by rfl) ⟨1592009, by rfl⟩ : syracuseStep 2122679 = 3184019) B3184019
theorem B2122715 : Blo 1413526 2122715 := bstep (se 1 (by rfl) ⟨1592036, by rfl⟩ : syracuseStep 2122715 = 3184073) B3184073
theorem B8602625 : Blo 1413526 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B9684139 : Blo 1413526 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B2123183 : Blo 1413526 2123183 := bstep (se 1 (by rfl) ⟨1592387, by rfl⟩ : syracuseStep 2123183 = 3184775) B3184775
theorem B2385335 : Blo 1413526 2385335 := bstep (se 1 (by rfl) ⟨1789001, by rfl⟩ : syracuseStep 2385335 = 3578003) B3578003
theorem B2123273 : Blo 1413526 2123273 := bstep (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) B1592455
theorem B29025803 : Blo 1413526 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B11470423 : Blo 1413526 11470423 := bstep (se 1 (by rfl) ⟨8602817, by rfl⟩ : syracuseStep 11470423 = 17205635) B17205635
theorem B1590907 : Blo 1413526 1590907 := bstep (se 1 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 1590907 = 2386361) B2386361
theorem B4531859 : Blo 1413526 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B7161533 : Blo 1413526 7161533 := bstep (se 3 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 7161533 = 2685575) B2685575
theorem B5367505 : Blo 1413526 5367505 := bstep (se 2 (by rfl) ⟨2012814, by rfl⟩ : syracuseStep 5367505 = 4025629) B4025629
theorem B8603351 : Blo 1413526 8603351 := bstep (se 1 (by rfl) ⟨6452513, by rfl⟩ : syracuseStep 8603351 = 12905027) B12905027
theorem B10741571 : Blo 1413526 10741571 := bstep (se 1 (by rfl) ⟨8056178, by rfl⟩ : syracuseStep 10741571 = 16112357) B16112357
theorem B7161695 : Blo 1413526 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B7751585 : Blo 1413526 7751585 := bstep (se 2 (by rfl) ⟨2906844, by rfl⟩ : syracuseStep 7751585 = 5813689) B5813689
theorem B5367809 : Blo 1413526 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B2385929 : Blo 1413526 2385929 := bstep (se 2 (by rfl) ⟨894723, by rfl⟩ : syracuseStep 2385929 = 1789447) B1789447
theorem B3180563 : Blo 1413526 3180563 := bstep (se 1 (by rfl) ⟨2385422, by rfl⟩ : syracuseStep 3180563 = 4770845) B4770845
theorem B10881053 : Blo 1413526 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B1591375 : Blo 1413526 1591375 := bstep (se 1 (by rfl) ⟨1193531, by rfl⟩ : syracuseStep 1591375 = 2387063) B2387063
theorem B7645265 : Blo 1413526 7645265 := bstep (se 2 (by rfl) ⟨2866974, by rfl⟩ : syracuseStep 7645265 = 5733949) B5733949
theorem B2386091 : Blo 1413526 2386091 := bstep (se 1 (by rfl) ⟨1789568, by rfl⟩ : syracuseStep 2386091 = 3579137) B3579137
theorem B14723329 : Blo 1413526 14723329 := bstep (se 2 (by rfl) ⟨5521248, by rfl⟩ : syracuseStep 14723329 = 11042497) B11042497
theorem B3180905 : Blo 1413526 3180905 := bstep (se 2 (by rfl) ⟨1192839, by rfl⟩ : syracuseStep 3180905 = 2385679) B2385679
theorem B6891905 : Blo 1413526 6891905 := bstep (se 2 (by rfl) ⟨2584464, by rfl⟩ : syracuseStep 6891905 = 5168929) B5168929
theorem B15296921 : Blo 1413526 15296921 := bstep (se 2 (by rfl) ⟨5736345, by rfl⟩ : syracuseStep 15296921 = 11472691) B11472691
theorem B5368265 : Blo 1413526 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B1591771 : Blo 1413526 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B3582427 : Blo 1413526 3582427 := bstep (se 1 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 3582427 = 5373641) B5373641
theorem B2386489 : Blo 1413526 2386489 := bstep (se 2 (by rfl) ⟨894933, by rfl⟩ : syracuseStep 2386489 = 1789867) B1789867
theorem B2386631 : Blo 1413526 2386631 := bstep (se 1 (by rfl) ⟨1789973, by rfl⟩ : syracuseStep 2386631 = 3579947) B3579947
theorem B10734281 : Blo 1413526 10734281 := bstep (se 2 (by rfl) ⟨4025355, by rfl⟩ : syracuseStep 10734281 = 8050711) B8050711
theorem B2386793 : Blo 1413526 2386793 := bstep (se 2 (by rfl) ⟨895047, by rfl⟩ : syracuseStep 2386793 = 1790095) B1790095
theorem B5368751 : Blo 1413526 5368751 := bstep (se 1 (by rfl) ⟨4026563, by rfl⟩ : syracuseStep 5368751 = 8053127) B8053127
theorem B1592239 : Blo 1413526 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B3181499 : Blo 1413526 3181499 := bstep (se 1 (by rfl) ⟨2386124, by rfl⟩ : syracuseStep 3181499 = 4772249) B4772249
theorem B1510363 : Blo 1413526 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B3181625 : Blo 1413526 3181625 := bstep (se 2 (by rfl) ⟨1193109, by rfl⟩ : syracuseStep 3181625 = 2386219) B2386219
theorem B2722987 : Blo 1413526 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B88247501 : Blo 1413526 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2387191 : Blo 1413526 2387191 := bstep (se 1 (by rfl) ⟨1790393, by rfl⟩ : syracuseStep 2387191 = 3580787) B3580787
theorem B3181967 : Blo 1413526 3181967 := bstep (se 1 (by rfl) ⟨2386475, by rfl⟩ : syracuseStep 3181967 = 4772951) B4772951
theorem B1699255 : Blo 1413526 1699255 := bstep (se 1 (by rfl) ⟨1274441, by rfl⟩ : syracuseStep 1699255 = 2548883) B2548883
theorem B2387387 : Blo 1413526 2387387 := bstep (se 1 (by rfl) ⟨1790540, by rfl⟩ : syracuseStep 2387387 = 3581081) B3581081
theorem B2387495 : Blo 1413526 2387495 := bstep (se 1 (by rfl) ⟨1790621, by rfl⟩ : syracuseStep 2387495 = 3581243) B3581243
theorem B2297383 : Blo 1413526 2297383 := bstep (se 1 (by rfl) ⟨1723037, by rfl⟩ : syracuseStep 2297383 = 3446075) B3446075
theorem B4836923 : Blo 1413526 4836923 := bstep (se 1 (by rfl) ⟨3627692, by rfl⟩ : syracuseStep 4836923 = 7255385) B7255385
theorem B4533857 : Blo 1413526 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B2264699 : Blo 1413526 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B3821195 : Blo 1413526 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B7851667 : Blo 1413526 7851667 := bstep (se 1 (by rfl) ⟨5888750, by rfl⟩ : syracuseStep 7851667 = 11777501) B11777501
theorem B6794941 : Blo 1413526 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B1633991 : Blo 1413526 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B3182291 : Blo 1413526 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B18124559 : Blo 1413526 18124559 := bstep (se 1 (by rfl) ⟨13593419, by rfl⟩ : syracuseStep 18124559 = 27186839) B27186839
theorem B2387785 : Blo 1413526 2387785 := bstep (se 2 (by rfl) ⟨895419, by rfl⟩ : syracuseStep 2387785 = 1790839) B1790839
theorem B2387819 : Blo 1413526 2387819 := bstep (se 1 (by rfl) ⟨1790864, by rfl⟩ : syracuseStep 2387819 = 3581729) B3581729
theorem B2723879 : Blo 1413526 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B5369935 : Blo 1413526 5369935 := bstep (se 1 (by rfl) ⟨4027451, by rfl⟩ : syracuseStep 5369935 = 8054903) B8054903
theorem B4772087 : Blo 1413526 4772087 := bstep (se 1 (by rfl) ⟨3579065, by rfl⟩ : syracuseStep 4772087 = 7158131) B7158131
theorem B2388217 : Blo 1413526 2388217 := bstep (se 2 (by rfl) ⟨895581, by rfl⟩ : syracuseStep 2388217 = 1791163) B1791163
theorem B1413551 : Blo 1413526 1413551 := bstep (se 1 (by rfl) ⟨1060163, by rfl⟩ : syracuseStep 1413551 = 2120327) B2120327
theorem B1413575 : Blo 1413526 1413575 := bstep (se 1 (by rfl) ⟨1060181, by rfl⟩ : syracuseStep 1413575 = 2120363) B2120363
theorem B1413595 : Blo 1413526 1413595 := bstep (se 1 (by rfl) ⟨1060196, by rfl⟩ : syracuseStep 1413595 = 2120393) B2120393
theorem B21516803 : Blo 1413526 21516803 := bstep (se 1 (by rfl) ⟨16137602, by rfl⟩ : syracuseStep 21516803 = 32275205) B32275205
theorem B2388487 : Blo 1413526 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B4026905 : Blo 1413526 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B7164449 : Blo 1413526 7164449 := bstep (se 2 (by rfl) ⟨2686668, by rfl⟩ : syracuseStep 7164449 = 5373337) B5373337
theorem B1413671 : Blo 1413526 1413671 := bstep (se 1 (by rfl) ⟨1060253, by rfl⟩ : syracuseStep 1413671 = 2120507) B2120507
theorem B5370407 : Blo 1413526 5370407 := bstep (se 1 (by rfl) ⟨4027805, by rfl⟩ : syracuseStep 5370407 = 8055611) B8055611
theorem B4772411 : Blo 1413526 4772411 := bstep (se 1 (by rfl) ⟨3579308, by rfl⟩ : syracuseStep 4772411 = 7158617) B7158617
theorem B1413711 : Blo 1413526 1413711 := bstep (se 1 (by rfl) ⟨1060283, by rfl⟩ : syracuseStep 1413711 = 2120567) B2120567
theorem B1413727 : Blo 1413526 1413727 := bstep (se 1 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 1413727 = 2120591) B2120591
theorem B1413755 : Blo 1413526 1413755 := bstep (se 1 (by rfl) ⟨1060316, by rfl⟩ : syracuseStep 1413755 = 2120633) B2120633
theorem B3183227 : Blo 1413526 3183227 := bstep (se 1 (by rfl) ⟨2387420, by rfl⟩ : syracuseStep 3183227 = 4774841) B4774841
theorem B7262855 : Blo 1413526 7262855 := bstep (se 1 (by rfl) ⟨5447141, by rfl⟩ : syracuseStep 7262855 = 10894283) B10894283
theorem B1413807 : Blo 1413526 1413807 := bstep (se 1 (by rfl) ⟨1060355, by rfl⟩ : syracuseStep 1413807 = 2120711) B2120711
theorem B1413831 : Blo 1413526 1413831 := bstep (se 1 (by rfl) ⟨1060373, by rfl⟩ : syracuseStep 1413831 = 2120747) B2120747
theorem B36229841 : Blo 1413526 36229841 := bstep (se 2 (by rfl) ⟨13586190, by rfl⟩ : syracuseStep 36229841 = 27172381) B27172381
theorem B11465425 : Blo 1413526 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B1413851 : Blo 1413526 1413851 := bstep (se 1 (by rfl) ⟨1060388, by rfl⟩ : syracuseStep 1413851 = 2120777) B2120777
theorem B3019513 : Blo 1413526 3019513 := bstep (se 2 (by rfl) ⟨1132317, by rfl⟩ : syracuseStep 3019513 = 2264635) B2264635
theorem B3183353 : Blo 1413526 3183353 := bstep (se 2 (by rfl) ⟨1193757, by rfl⟩ : syracuseStep 3183353 = 2387515) B2387515
theorem B1413927 : Blo 1413526 1413927 := bstep (se 1 (by rfl) ⟨1060445, by rfl⟩ : syracuseStep 1413927 = 2120891) B2120891
theorem B4772681 : Blo 1413526 4772681 := bstep (se 2 (by rfl) ⟨1789755, by rfl⟩ : syracuseStep 4772681 = 3579511) B3579511
theorem B1413967 : Blo 1413526 1413967 := bstep (se 1 (by rfl) ⟨1060475, by rfl⟩ : syracuseStep 1413967 = 2120951) B2120951
theorem B1413983 : Blo 1413526 1413983 := bstep (se 1 (by rfl) ⟨1060487, by rfl⟩ : syracuseStep 1413983 = 2120975) B2120975
theorem B20386667 : Blo 1413526 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B1414011 : Blo 1413526 1414011 := bstep (se 1 (by rfl) ⟨1060508, by rfl⟩ : syracuseStep 1414011 = 2121017) B2121017
theorem B1414063 : Blo 1413526 1414063 := bstep (se 1 (by rfl) ⟨1060547, by rfl⟩ : syracuseStep 1414063 = 2121095) B2121095
theorem B1414087 : Blo 1413526 1414087 := bstep (se 1 (by rfl) ⟨1060565, by rfl⟩ : syracuseStep 1414087 = 2121131) B2121131
theorem B2683867 : Blo 1413526 2683867 := bstep (se 1 (by rfl) ⟨2012900, by rfl⟩ : syracuseStep 2683867 = 4025801) B4025801
theorem B1414107 : Blo 1413526 1414107 := bstep (se 1 (by rfl) ⟨1060580, by rfl⟩ : syracuseStep 1414107 = 2121161) B2121161
theorem B13587421 : Blo 1413526 13587421 := bstep (se 3 (by rfl) ⟨2547641, by rfl⟩ : syracuseStep 13587421 = 5095283) B5095283
theorem B3183623 : Blo 1413526 3183623 := bstep (se 1 (by rfl) ⟨2387717, by rfl⟩ : syracuseStep 3183623 = 4775435) B4775435
theorem B1414183 : Blo 1413526 1414183 := bstep (se 1 (by rfl) ⟨1060637, by rfl⟩ : syracuseStep 1414183 = 2121275) B2121275
theorem B9057359 : Blo 1413526 9057359 := bstep (se 1 (by rfl) ⟨6793019, by rfl⟩ : syracuseStep 9057359 = 13586039) B13586039
theorem B3019855 : Blo 1413526 3019855 := bstep (se 1 (by rfl) ⟨2264891, by rfl⟩ : syracuseStep 3019855 = 4529783) B4529783
theorem B1414223 : Blo 1413526 1414223 := bstep (se 1 (by rfl) ⟨1060667, by rfl⟩ : syracuseStep 1414223 = 2121335) B2121335
theorem B3183695 : Blo 1413526 3183695 := bstep (se 1 (by rfl) ⟨2387771, by rfl⟩ : syracuseStep 3183695 = 4775543) B4775543
theorem B1414239 : Blo 1413526 1414239 := bstep (se 1 (by rfl) ⟨1060679, by rfl⟩ : syracuseStep 1414239 = 2121359) B2121359
theorem B12088439 : Blo 1413526 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B1414267 : Blo 1413526 1414267 := bstep (se 1 (by rfl) ⟨1060700, by rfl⟩ : syracuseStep 1414267 = 2121401) B2121401
theorem B1414319 : Blo 1413526 1414319 := bstep (se 1 (by rfl) ⟨1060739, by rfl⟩ : syracuseStep 1414319 = 2121479) B2121479
theorem B1414343 : Blo 1413526 1414343 := bstep (se 1 (by rfl) ⟨1060757, by rfl⟩ : syracuseStep 1414343 = 2121515) B2121515
theorem B1414363 : Blo 1413526 1414363 := bstep (se 1 (by rfl) ⟨1060772, by rfl⟩ : syracuseStep 1414363 = 2121545) B2121545
theorem B17216783 : Blo 1413526 17216783 := bstep (se 1 (by rfl) ⟨12912587, by rfl⟩ : syracuseStep 17216783 = 25825175) B25825175
theorem B13604111 : Blo 1413526 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B1414439 : Blo 1413526 1414439 := bstep (se 1 (by rfl) ⟨1060829, by rfl⟩ : syracuseStep 1414439 = 2121659) B2121659
theorem B1414479 : Blo 1413526 1414479 := bstep (se 1 (by rfl) ⟨1060859, by rfl⟩ : syracuseStep 1414479 = 2121719) B2121719
theorem B1414495 : Blo 1413526 1414495 := bstep (se 1 (by rfl) ⟨1060871, by rfl⟩ : syracuseStep 1414495 = 2121743) B2121743
theorem B1414523 : Blo 1413526 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B1414575 : Blo 1413526 1414575 := bstep (se 1 (by rfl) ⟨1060931, by rfl⟩ : syracuseStep 1414575 = 2121863) B2121863
theorem B1414599 : Blo 1413526 1414599 := bstep (se 1 (by rfl) ⟨1060949, by rfl⟩ : syracuseStep 1414599 = 2121899) B2121899
theorem B1414619 : Blo 1413526 1414619 := bstep (se 1 (by rfl) ⟨1060964, by rfl⟩ : syracuseStep 1414619 = 2121929) B2121929
theorem B3184091 : Blo 1413526 3184091 := bstep (se 1 (by rfl) ⟨2388068, by rfl⟩ : syracuseStep 3184091 = 4776137) B4776137
theorem B5371379 : Blo 1413526 5371379 := bstep (se 1 (by rfl) ⟨4028534, by rfl⟩ : syracuseStep 5371379 = 8057069) B8057069
theorem B3823129 : Blo 1413526 3823129 := bstep (se 2 (by rfl) ⟨1433673, by rfl⟩ : syracuseStep 3823129 = 2867347) B2867347
theorem B1414695 : Blo 1413526 1414695 := bstep (se 1 (by rfl) ⟨1061021, by rfl⟩ : syracuseStep 1414695 = 2122043) B2122043
theorem B1414735 : Blo 1413526 1414735 := bstep (se 1 (by rfl) ⟨1061051, by rfl⟩ : syracuseStep 1414735 = 2122103) B2122103
theorem B1414751 : Blo 1413526 1414751 := bstep (se 1 (by rfl) ⟨1061063, by rfl⟩ : syracuseStep 1414751 = 2122127) B2122127
theorem B1414779 : Blo 1413526 1414779 := bstep (se 1 (by rfl) ⟨1061084, by rfl⟩ : syracuseStep 1414779 = 2122169) B2122169
theorem B1414831 : Blo 1413526 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1414855 : Blo 1413526 1414855 := bstep (se 1 (by rfl) ⟨1061141, by rfl⟩ : syracuseStep 1414855 = 2122283) B2122283
theorem B1414875 : Blo 1413526 1414875 := bstep (se 1 (by rfl) ⟨1061156, by rfl⟩ : syracuseStep 1414875 = 2122313) B2122313
theorem B2266871 : Blo 1413526 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B1414951 : Blo 1413526 1414951 := bstep (se 1 (by rfl) ⟨1061213, by rfl⟩ : syracuseStep 1414951 = 2122427) B2122427
theorem B20666171 : Blo 1413526 20666171 := bstep (se 1 (by rfl) ⟨15499628, by rfl⟩ : syracuseStep 20666171 = 30999257) B30999257
theorem B1414991 : Blo 1413526 1414991 := bstep (se 1 (by rfl) ⟨1061243, by rfl⟩ : syracuseStep 1414991 = 2122487) B2122487
theorem B1415007 : Blo 1413526 1415007 := bstep (se 1 (by rfl) ⟨1061255, by rfl⟩ : syracuseStep 1415007 = 2122511) B2122511
theorem B16119647 : Blo 1413526 16119647 := bstep (se 1 (by rfl) ⟨12089735, by rfl⟩ : syracuseStep 16119647 = 24179471) B24179471
theorem B6043501 : Blo 1413526 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B1415035 : Blo 1413526 1415035 := bstep (se 1 (by rfl) ⟨1061276, by rfl⟩ : syracuseStep 1415035 = 2122553) B2122553
theorem B1415087 : Blo 1413526 1415087 := bstep (se 1 (by rfl) ⟨1061315, by rfl⟩ : syracuseStep 1415087 = 2122631) B2122631
theorem B3184559 : Blo 1413526 3184559 := bstep (se 1 (by rfl) ⟨2388419, by rfl⟩ : syracuseStep 3184559 = 4776839) B4776839
theorem B4773815 : Blo 1413526 4773815 := bstep (se 1 (by rfl) ⟨3580361, by rfl⟩ : syracuseStep 4773815 = 7160723) B7160723
theorem B1415111 : Blo 1413526 1415111 := bstep (se 1 (by rfl) ⟨1061333, by rfl⟩ : syracuseStep 1415111 = 2122667) B2122667
theorem B1415131 : Blo 1413526 1415131 := bstep (se 1 (by rfl) ⟨1061348, by rfl⟩ : syracuseStep 1415131 = 2122697) B2122697
theorem B1415207 : Blo 1413526 1415207 := bstep (se 1 (by rfl) ⟨1061405, by rfl⟩ : syracuseStep 1415207 = 2122811) B2122811
theorem B1415247 : Blo 1413526 1415247 := bstep (se 1 (by rfl) ⟨1061435, by rfl⟩ : syracuseStep 1415247 = 2122871) B2122871
theorem B10745945 : Blo 1413526 10745945 := bstep (se 2 (by rfl) ⟨4029729, by rfl⟩ : syracuseStep 10745945 = 8059459) B8059459
theorem B1415263 : Blo 1413526 1415263 := bstep (se 1 (by rfl) ⟨1061447, by rfl⟩ : syracuseStep 1415263 = 2122895) B2122895
theorem B1415291 : Blo 1413526 1415291 := bstep (se 1 (by rfl) ⟨1061468, by rfl⟩ : syracuseStep 1415291 = 2122937) B2122937
theorem B3184811 : Blo 1413526 3184811 := bstep (se 1 (by rfl) ⟨2388608, by rfl⟩ : syracuseStep 3184811 = 4777217) B4777217
theorem B1415343 : Blo 1413526 1415343 := bstep (se 1 (by rfl) ⟨1061507, by rfl⟩ : syracuseStep 1415343 = 2123015) B2123015
theorem B1415367 : Blo 1413526 1415367 := bstep (se 1 (by rfl) ⟨1061525, by rfl⟩ : syracuseStep 1415367 = 2123051) B2123051
theorem B1415387 : Blo 1413526 1415387 := bstep (se 1 (by rfl) ⟨1061540, by rfl⟩ : syracuseStep 1415387 = 2123081) B2123081
theorem B1415463 : Blo 1413526 1415463 := bstep (se 1 (by rfl) ⟨1061597, by rfl⟩ : syracuseStep 1415463 = 2123195) B2123195
theorem B1415503 : Blo 1413526 1415503 := bstep (se 1 (by rfl) ⟨1061627, by rfl⟩ : syracuseStep 1415503 = 2123255) B2123255
theorem B1415519 : Blo 1413526 1415519 := bstep (se 1 (by rfl) ⟨1061639, by rfl⟩ : syracuseStep 1415519 = 2123279) B2123279
theorem B3824015 : Blo 1413526 3824015 := bstep (se 1 (by rfl) ⟨2868011, by rfl⟩ : syracuseStep 3824015 = 5736023) B5736023
theorem B17201645 : Blo 1413526 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B3578377 : Blo 1413526 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B4774409 : Blo 1413526 4774409 := bstep (se 2 (by rfl) ⟨1790403, by rfl⟩ : syracuseStep 4774409 = 3580807) B3580807
theorem B3398183 : Blo 1413526 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B3824167 : Blo 1413526 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B8608315 : Blo 1413526 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B3021409 : Blo 1413526 3021409 := bstep (se 2 (by rfl) ⟨1133028, by rfl⟩ : syracuseStep 3021409 = 2266057) B2266057
theorem B2120315 : Blo 1413526 2120315 := bstep (se 1 (by rfl) ⟨1590236, by rfl⟩ : syracuseStep 2120315 = 3180473) B3180473
theorem B3824317 : Blo 1413526 3824317 := bstep (se 3 (by rfl) ⟨717059, by rfl⟩ : syracuseStep 3824317 = 1434119) B1434119
theorem B2120441 : Blo 1413526 2120441 := bstep (se 2 (by rfl) ⟨795165, by rfl⟩ : syracuseStep 2120441 = 1590331) B1590331
theorem B3398393 : Blo 1413526 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B2120543 : Blo 1413526 2120543 := bstep (se 1 (by rfl) ⟨1590407, by rfl⟩ : syracuseStep 2120543 = 3180815) B3180815
theorem B5815135 : Blo 1413526 5815135 := bstep (se 1 (by rfl) ⟨4361351, by rfl⟩ : syracuseStep 5815135 = 8722703) B8722703
theorem B2120555 : Blo 1413526 2120555 := bstep (se 1 (by rfl) ⟨1590416, by rfl⟩ : syracuseStep 2120555 = 3180833) B3180833
theorem B9681839 : Blo 1413526 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B2120783 : Blo 1413526 2120783 := bstep (se 1 (by rfl) ⟨1590587, by rfl⟩ : syracuseStep 2120783 = 3181175) B3181175
theorem B2686031 : Blo 1413526 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B2120903 : Blo 1413526 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B2866423 : Blo 1413526 2866423 := bstep (se 1 (by rfl) ⟨2149817, by rfl⟩ : syracuseStep 2866423 = 4299635) B4299635
theorem B2121065 : Blo 1413526 2121065 := bstep (se 2 (by rfl) ⟨795399, by rfl⟩ : syracuseStep 2121065 = 1590799) B1590799
theorem B4775273 : Blo 1413526 4775273 := bstep (se 2 (by rfl) ⟨1790727, by rfl⟩ : syracuseStep 4775273 = 3581455) B3581455
theorem B4029821 : Blo 1413526 4029821 := bstep (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) B1511183
theorem B9674149 : Blo 1413526 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B2121143 : Blo 1413526 2121143 := bstep (se 1 (by rfl) ⟨1590857, by rfl⟩ : syracuseStep 2121143 = 3181715) B3181715
theorem B8052169 : Blo 1413526 8052169 := bstep (se 2 (by rfl) ⟨3019563, by rfl⟩ : syracuseStep 8052169 = 6039127) B6039127
theorem B2121179 : Blo 1413526 2121179 := bstep (se 1 (by rfl) ⟨1590884, by rfl⟩ : syracuseStep 2121179 = 3181769) B3181769
theorem B10747403 : Blo 1413526 10747403 := bstep (se 1 (by rfl) ⟨8060552, by rfl⟩ : syracuseStep 10747403 = 16121105) B16121105
theorem B4030049 : Blo 1413526 4030049 := bstep (se 2 (by rfl) ⟨1511268, by rfl⟩ : syracuseStep 4030049 = 3022537) B3022537
theorem B7651037 : Blo 1413526 7651037 := bstep (se 3 (by rfl) ⟨1434569, by rfl⟩ : syracuseStep 7651037 = 2869139) B2869139
theorem B2867087 : Blo 1413526 2867087 := bstep (se 1 (by rfl) ⟨2150315, by rfl⟩ : syracuseStep 2867087 = 4300631) B4300631
theorem B2121647 : Blo 1413526 2121647 := bstep (se 1 (by rfl) ⟨1591235, by rfl⟩ : syracuseStep 2121647 = 3182471) B3182471
theorem B4030391 : Blo 1413526 4030391 := bstep (se 1 (by rfl) ⟨3022793, by rfl⟩ : syracuseStep 4030391 = 6045587) B6045587
theorem B3579835 : Blo 1413526 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B4775867 : Blo 1413526 4775867 := bstep (se 1 (by rfl) ⟨3581900, by rfl⟩ : syracuseStep 4775867 = 7163801) B7163801
theorem B7159913 : Blo 1413526 7159913 := bstep (se 2 (by rfl) ⟨2684967, by rfl⟩ : syracuseStep 7159913 = 5369935) B5369935
theorem B2121833 : Blo 1413526 2121833 := bstep (se 2 (by rfl) ⟨795687, by rfl⟩ : syracuseStep 2121833 = 1591375) B1591375
theorem B14344535 : Blo 1413526 14344535 := bstep (se 1 (by rfl) ⟨10758401, by rfl⟩ : syracuseStep 14344535 = 21516803) B21516803
theorem B4776299 : Blo 1413526 4776299 := bstep (se 1 (by rfl) ⟨3582224, by rfl⟩ : syracuseStep 4776299 = 7164449) B7164449
theorem B3580271 : Blo 1413526 3580271 := bstep (se 1 (by rfl) ⟨2685203, by rfl⟩ : syracuseStep 3580271 = 5370407) B5370407
theorem B2122151 : Blo 1413526 2122151 := bstep (se 1 (by rfl) ⟨1591613, by rfl⟩ : syracuseStep 2122151 = 3183227) B3183227
theorem B4841903 : Blo 1413526 4841903 := bstep (se 1 (by rfl) ⟨3631427, by rfl⟩ : syracuseStep 4841903 = 7262855) B7262855
theorem B2122235 : Blo 1413526 2122235 := bstep (se 1 (by rfl) ⟨1591676, by rfl⟩ : syracuseStep 2122235 = 3183353) B3183353
theorem B3228155 : Blo 1413526 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B2122361 : Blo 1413526 2122361 := bstep (se 2 (by rfl) ⟨795885, by rfl⟩ : syracuseStep 2122361 = 1591771) B1591771
theorem B4776569 : Blo 1413526 4776569 := bstep (se 2 (by rfl) ⟨1791213, by rfl⟩ : syracuseStep 4776569 = 3582427) B3582427
theorem B2122415 : Blo 1413526 2122415 := bstep (se 1 (by rfl) ⟨1591811, by rfl⟩ : syracuseStep 2122415 = 3183623) B3183623
theorem B6038239 : Blo 1413526 6038239 := bstep (se 1 (by rfl) ⟨4528679, by rfl⟩ : syracuseStep 6038239 = 9057359) B9057359
theorem B2122463 : Blo 1413526 2122463 := bstep (se 1 (by rfl) ⟨1591847, by rfl⟩ : syracuseStep 2122463 = 3183695) B3183695
theorem B11477753 : Blo 1413526 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B11477855 : Blo 1413526 11477855 := bstep (se 1 (by rfl) ⟨8608391, by rfl⟩ : syracuseStep 11477855 = 17216783) B17216783
theorem B9069407 : Blo 1413526 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B15287233 : Blo 1413526 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B1590223 : Blo 1413526 1590223 := bstep (se 1 (by rfl) ⟨1192667, by rfl⟩ : syracuseStep 1590223 = 2385335) B2385335
theorem B2122727 : Blo 1413526 2122727 := bstep (se 1 (by rfl) ⟨1592045, by rfl⟩ : syracuseStep 2122727 = 3184091) B3184091
theorem B3580919 : Blo 1413526 3580919 := bstep (se 1 (by rfl) ⟨2685689, by rfl⟩ : syracuseStep 3580919 = 5371379) B5371379
theorem B19350535 : Blo 1413526 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B5735567 : Blo 1413526 5735567 := bstep (se 1 (by rfl) ⟨4301675, by rfl⟩ : syracuseStep 5735567 = 8603351) B8603351
theorem B7161047 : Blo 1413526 7161047 := bstep (se 1 (by rfl) ⟨5370785, by rfl⟩ : syracuseStep 7161047 = 10741571) B10741571
theorem B2122985 : Blo 1413526 2122985 := bstep (se 2 (by rfl) ⟨796119, by rfl⟩ : syracuseStep 2122985 = 1592239) B1592239
theorem B2123039 : Blo 1413526 2123039 := bstep (se 1 (by rfl) ⟨1592279, by rfl⟩ : syracuseStep 2123039 = 3184559) B3184559
theorem B1590619 : Blo 1413526 1590619 := bstep (se 1 (by rfl) ⟨1192964, by rfl⟩ : syracuseStep 1590619 = 2385929) B2385929
theorem B5096843 : Blo 1413526 5096843 := bstep (se 1 (by rfl) ⟨3822632, by rfl⟩ : syracuseStep 5096843 = 7645265) B7645265
theorem B1590727 : Blo 1413526 1590727 := bstep (se 1 (by rfl) ⟨1193045, by rfl⟩ : syracuseStep 1590727 = 2386091) B2386091
theorem B2123207 : Blo 1413526 2123207 := bstep (se 1 (by rfl) ⟨1592405, by rfl⟩ : syracuseStep 2123207 = 3184811) B3184811
theorem B12912185 : Blo 1413526 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B6039197 : Blo 1413526 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B1591087 : Blo 1413526 1591087 := bstep (se 1 (by rfl) ⟨1193315, by rfl⟩ : syracuseStep 1591087 = 2386631) B2386631
theorem B1591195 : Blo 1413526 1591195 := bstep (se 1 (by rfl) ⟨1193396, by rfl⟩ : syracuseStep 1591195 = 2386793) B2386793
theorem B9062381 : Blo 1413526 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B5097505 : Blo 1413526 5097505 := bstep (se 2 (by rfl) ⟨1911564, by rfl⟩ : syracuseStep 5097505 = 3823129) B3823129
theorem B54364445 : Blo 1413526 54364445 := bstep (se 3 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 54364445 = 20386667) B20386667
theorem B1591591 : Blo 1413526 1591591 := bstep (se 1 (by rfl) ⟨1193693, by rfl⟩ : syracuseStep 1591591 = 2387387) B2387387
theorem B1591663 : Blo 1413526 1591663 := bstep (se 1 (by rfl) ⟨1193747, by rfl⟩ : syracuseStep 1591663 = 2387495) B2387495
theorem B7645565 : Blo 1413526 7645565 := bstep (se 3 (by rfl) ⟨1433543, by rfl⟩ : syracuseStep 7645565 = 2867087) B2867087
theorem B20670893 : Blo 1413526 20670893 := bstep (se 3 (by rfl) ⟨3875792, by rfl⟩ : syracuseStep 20670893 = 7751585) B7751585
theorem B1591879 : Blo 1413526 1591879 := bstep (se 1 (by rfl) ⟨1193909, by rfl⟩ : syracuseStep 1591879 = 2387819) B2387819
theorem B22940333 : Blo 1413526 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B3181391 : Blo 1413526 3181391 := bstep (se 1 (by rfl) ⟨2386043, by rfl⟩ : syracuseStep 3181391 = 4772087) B4772087
theorem B3582863 : Blo 1413526 3582863 := bstep (se 1 (by rfl) ⟨2687147, by rfl⟩ : syracuseStep 3582863 = 5374295) B5374295
theorem B19631105 : Blo 1413526 19631105 := bstep (se 2 (by rfl) ⟨7361664, by rfl⟩ : syracuseStep 19631105 = 14723329) B14723329
theorem B3181607 : Blo 1413526 3181607 := bstep (se 1 (by rfl) ⟨2386205, by rfl⟩ : syracuseStep 3181607 = 4772411) B4772411
theorem B6040615 : Blo 1413526 6040615 := bstep (se 1 (by rfl) ⟨4530461, by rfl⟩ : syracuseStep 6040615 = 9060923) B9060923
theorem B4533371 : Blo 1413526 4533371 := bstep (se 1 (by rfl) ⟨3400028, by rfl⟩ : syracuseStep 4533371 = 6800057) B6800057
theorem B24153227 : Blo 1413526 24153227 := bstep (se 1 (by rfl) ⟨18114920, by rfl⟩ : syracuseStep 24153227 = 36229841) B36229841
theorem B3181787 : Blo 1413526 3181787 := bstep (se 1 (by rfl) ⟨2386340, by rfl⟩ : syracuseStep 3181787 = 4772681) B4772681
theorem B4771169 : Blo 1413526 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B5098889 : Blo 1413526 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B4533641 : Blo 1413526 4533641 := bstep (se 2 (by rfl) ⟨1700115, by rfl⟩ : syracuseStep 4533641 = 3400231) B3400231
theorem B3181985 : Blo 1413526 3181985 := bstep (se 2 (by rfl) ⟨1193244, by rfl⟩ : syracuseStep 3181985 = 2386489) B2386489
theorem B4026017 : Blo 1413526 4026017 := bstep (se 2 (by rfl) ⟨1509756, by rfl⟩ : syracuseStep 4026017 = 3019513) B3019513
theorem B3182543 : Blo 1413526 3182543 := bstep (se 1 (by rfl) ⟨2386907, by rfl⟩ : syracuseStep 3182543 = 4773815) B4773815
theorem B18116561 : Blo 1413526 18116561 := bstep (se 2 (by rfl) ⟨6793710, by rfl⟩ : syracuseStep 18116561 = 13587421) B13587421
theorem B7254035 : Blo 1413526 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B7163963 : Blo 1413526 7163963 := bstep (se 1 (by rfl) ⟨5372972, by rfl⟩ : syracuseStep 7163963 = 10745945) B10745945
theorem B4026473 : Blo 1413526 4026473 := bstep (se 2 (by rfl) ⟨1509927, by rfl⟩ : syracuseStep 4026473 = 3019855) B3019855
theorem B49656077 : Blo 1413526 49656077 := bstep (se 3 (by rfl) ⟨9310514, by rfl⟩ : syracuseStep 49656077 = 18621029) B18621029
theorem B3821897 : Blo 1413526 3821897 := bstep (se 2 (by rfl) ⟨1433211, by rfl⟩ : syracuseStep 3821897 = 2866423) B2866423
theorem B3182921 : Blo 1413526 3182921 := bstep (se 2 (by rfl) ⟨1193595, by rfl⟩ : syracuseStep 3182921 = 2387191) B2387191
theorem B3182939 : Blo 1413526 3182939 := bstep (se 1 (by rfl) ⟨2387204, by rfl⟩ : syracuseStep 3182939 = 4774409) B4774409
theorem B2265455 : Blo 1413526 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B1413543 : Blo 1413526 1413543 := bstep (se 1 (by rfl) ⟨1060157, by rfl⟩ : syracuseStep 1413543 = 2120315) B2120315
theorem B7156187 : Blo 1413526 7156187 := bstep (se 1 (by rfl) ⟨5367140, by rfl⟩ : syracuseStep 7156187 = 10734281) B10734281
theorem B1413627 : Blo 1413526 1413627 := bstep (se 1 (by rfl) ⟨1060220, by rfl⟩ : syracuseStep 1413627 = 2120441) B2120441
theorem B12898865 : Blo 1413526 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B1413695 : Blo 1413526 1413695 := bstep (se 1 (by rfl) ⟨1060271, by rfl⟩ : syracuseStep 1413695 = 2120543) B2120543
theorem B1413703 : Blo 1413526 1413703 := bstep (se 1 (by rfl) ⟨1060277, by rfl⟩ : syracuseStep 1413703 = 2120555) B2120555
theorem B2265673 : Blo 1413526 2265673 := bstep (se 2 (by rfl) ⟨849627, by rfl⟩ : syracuseStep 2265673 = 1699255) B1699255
theorem B20402765 : Blo 1413526 20402765 := bstep (se 3 (by rfl) ⟨3825518, by rfl⟩ : syracuseStep 20402765 = 7651037) B7651037
theorem B10736225 : Blo 1413526 10736225 := bstep (se 2 (by rfl) ⟨4026084, by rfl⟩ : syracuseStep 10736225 = 8052169) B8052169
theorem B1413855 : Blo 1413526 1413855 := bstep (se 1 (by rfl) ⟨1060391, by rfl⟩ : syracuseStep 1413855 = 2120783) B2120783
theorem B1790687 : Blo 1413526 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1413935 : Blo 1413526 1413935 := bstep (se 1 (by rfl) ⟨1060451, by rfl⟩ : syracuseStep 1413935 = 2120903) B2120903
theorem B58831667 : Blo 1413526 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B1414043 : Blo 1413526 1414043 := bstep (se 1 (by rfl) ⟨1060532, by rfl⟩ : syracuseStep 1414043 = 2121065) B2121065
theorem B3183515 : Blo 1413526 3183515 := bstep (se 1 (by rfl) ⟨2387636, by rfl⟩ : syracuseStep 3183515 = 4775273) B4775273
theorem B7156673 : Blo 1413526 7156673 := bstep (se 2 (by rfl) ⟨2683752, by rfl⟩ : syracuseStep 7156673 = 5367505) B5367505
theorem B1414095 : Blo 1413526 1414095 := bstep (se 1 (by rfl) ⟨1060571, by rfl⟩ : syracuseStep 1414095 = 2121143) B2121143
theorem B1414119 : Blo 1413526 1414119 := bstep (se 1 (by rfl) ⟨1060589, by rfl⟩ : syracuseStep 1414119 = 2121179) B2121179
theorem B7164935 : Blo 1413526 7164935 := bstep (se 1 (by rfl) ⟨5373701, by rfl⟩ : syracuseStep 7164935 = 10747403) B10747403
theorem B3224615 : Blo 1413526 3224615 := bstep (se 1 (by rfl) ⟨2418461, by rfl⟩ : syracuseStep 3224615 = 4836923) B4836923
theorem B3183713 : Blo 1413526 3183713 := bstep (se 2 (by rfl) ⟨1193892, by rfl⟩ : syracuseStep 3183713 = 2387785) B2387785
theorem B8058001 : Blo 1413526 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B4773113 : Blo 1413526 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B1414431 : Blo 1413526 1414431 := bstep (se 1 (by rfl) ⟨1060823, by rfl⟩ : syracuseStep 1414431 = 2121647) B2121647
theorem B3183911 : Blo 1413526 3183911 := bstep (se 1 (by rfl) ⟨2387933, by rfl⟩ : syracuseStep 3183911 = 4775867) B4775867
theorem B1414491 : Blo 1413526 1414491 := bstep (se 1 (by rfl) ⟨1060868, by rfl⟩ : syracuseStep 1414491 = 2121737) B2121737
theorem B1414511 : Blo 1413526 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B1414567 : Blo 1413526 1414567 := bstep (se 1 (by rfl) ⟨1060925, by rfl⟩ : syracuseStep 1414567 = 2121851) B2121851
theorem B7263677 : Blo 1413526 7263677 := bstep (se 3 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 7263677 = 2723879) B2723879
theorem B7165421 : Blo 1413526 7165421 := bstep (se 3 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 7165421 = 2687033) B2687033
theorem B1414651 : Blo 1413526 1414651 := bstep (se 1 (by rfl) ⟨1060988, by rfl⟩ : syracuseStep 1414651 = 2121977) B2121977
theorem B4773383 : Blo 1413526 4773383 := bstep (se 1 (by rfl) ⟨3580037, by rfl⟩ : syracuseStep 4773383 = 7160075) B7160075
theorem B1414719 : Blo 1413526 1414719 := bstep (se 1 (by rfl) ⟨1061039, by rfl⟩ : syracuseStep 1414719 = 2122079) B2122079
theorem B1414727 : Blo 1413526 1414727 := bstep (se 1 (by rfl) ⟨1061045, by rfl⟩ : syracuseStep 1414727 = 2122091) B2122091
theorem B3184289 : Blo 1413526 3184289 := bstep (se 2 (by rfl) ⟨1194108, by rfl⟩ : syracuseStep 3184289 = 2388217) B2388217
theorem B2684603 : Blo 1413526 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B1414879 : Blo 1413526 1414879 := bstep (se 1 (by rfl) ⟨1061159, by rfl⟩ : syracuseStep 1414879 = 2122319) B2122319
theorem B1414959 : Blo 1413526 1414959 := bstep (se 1 (by rfl) ⟨1061219, by rfl⟩ : syracuseStep 1414959 = 2122439) B2122439
theorem B1415067 : Blo 1413526 1415067 := bstep (se 1 (by rfl) ⟨1061300, by rfl⟩ : syracuseStep 1415067 = 2122601) B2122601
theorem B1415119 : Blo 1413526 1415119 := bstep (se 1 (by rfl) ⟨1061339, by rfl⟩ : syracuseStep 1415119 = 2122679) B2122679
theorem B1415143 : Blo 1413526 1415143 := bstep (se 1 (by rfl) ⟨1061357, by rfl⟩ : syracuseStep 1415143 = 2122715) B2122715
theorem B3184649 : Blo 1413526 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B8058959 : Blo 1413526 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B4028545 : Blo 1413526 4028545 := bstep (se 2 (by rfl) ⟨1510704, by rfl⟩ : syracuseStep 4028545 = 3021409) B3021409
theorem B49010837 : Blo 1413526 49010837 := bstep (se 6 (by rfl) ⟨1148691, by rfl⟩ : syracuseStep 49010837 = 2297383) B2297383
theorem B14522597 : Blo 1413526 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B1415455 : Blo 1413526 1415455 := bstep (se 1 (by rfl) ⟨1061591, by rfl⟩ : syracuseStep 1415455 = 2123183) B2123183
theorem B20396357 : Blo 1413526 20396357 := bstep (se 4 (by rfl) ⟨1912158, by rfl⟩ : syracuseStep 20396357 = 3824317) B3824317
theorem B1415515 : Blo 1413526 1415515 := bstep (se 1 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 1415515 = 2123273) B2123273
theorem B10197373 : Blo 1413526 10197373 := bstep (se 3 (by rfl) ⟨1912007, by rfl⟩ : syracuseStep 10197373 = 3824015) B3824015
theorem B3021239 : Blo 1413526 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B4774355 : Blo 1413526 4774355 := bstep (se 1 (by rfl) ⟨3580766, by rfl⟩ : syracuseStep 4774355 = 7161533) B7161533
theorem B13777447 : Blo 1413526 13777447 := bstep (se 1 (by rfl) ⟨10333085, by rfl⟩ : syracuseStep 13777447 = 20666171) B20666171
theorem B4774463 : Blo 1413526 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B10746431 : Blo 1413526 10746431 := bstep (se 1 (by rfl) ⟨8059823, by rfl⟩ : syracuseStep 10746431 = 16119647) B16119647
theorem B3578489 : Blo 1413526 3578489 := bstep (se 2 (by rfl) ⟨1341933, by rfl⟩ : syracuseStep 3578489 = 2683867) B2683867
theorem B2013817 : Blo 1413526 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B3578539 : Blo 1413526 3578539 := bstep (se 1 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 3578539 = 5367809) B5367809
theorem B2120375 : Blo 1413526 2120375 := bstep (se 1 (by rfl) ⟨1590281, by rfl⟩ : syracuseStep 2120375 = 3180563) B3180563
theorem B2120603 : Blo 1413526 2120603 := bstep (se 1 (by rfl) ⟨1590452, by rfl⟩ : syracuseStep 2120603 = 3180905) B3180905
theorem B4594603 : Blo 1413526 4594603 := bstep (se 1 (by rfl) ⟨3445952, by rfl⟩ : syracuseStep 4594603 = 6891905) B6891905
theorem B10197947 : Blo 1413526 10197947 := bstep (se 1 (by rfl) ⟨7648460, by rfl⟩ : syracuseStep 10197947 = 15296921) B15296921
theorem B3578843 : Blo 1413526 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B11467763 : Blo 1413526 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B31014053 : Blo 1413526 31014053 := bstep (se 4 (by rfl) ⟨2907567, by rfl⟩ : syracuseStep 31014053 = 5815135) B5815135
theorem B4357309 : Blo 1413526 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B3579167 : Blo 1413526 3579167 := bstep (se 1 (by rfl) ⟨2684375, by rfl⟩ : syracuseStep 3579167 = 5368751) B5368751
theorem B6454559 : Blo 1413526 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B2120999 : Blo 1413526 2120999 := bstep (se 1 (by rfl) ⟨1590749, by rfl⟩ : syracuseStep 2120999 = 3181499) B3181499
theorem B6044989 : Blo 1413526 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B2121083 : Blo 1413526 2121083 := bstep (se 1 (by rfl) ⟨1590812, by rfl⟩ : syracuseStep 2121083 = 3181625) B3181625
theorem B15293897 : Blo 1413526 15293897 := bstep (se 2 (by rfl) ⟨5735211, by rfl⟩ : syracuseStep 15293897 = 11470423) B11470423
theorem B2121209 : Blo 1413526 2121209 := bstep (se 2 (by rfl) ⟨795453, by rfl⟩ : syracuseStep 2121209 = 1590907) B1590907
theorem B10468889 : Blo 1413526 10468889 := bstep (se 2 (by rfl) ⟨3925833, by rfl⟩ : syracuseStep 10468889 = 7851667) B7851667
theorem B9059921 : Blo 1413526 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B2686547 : Blo 1413526 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B2121311 : Blo 1413526 2121311 := bstep (se 1 (by rfl) ⟨1590983, by rfl⟩ : syracuseStep 2121311 = 3181967) B3181967
theorem B2686699 : Blo 1413526 2686699 := bstep (se 1 (by rfl) ⟨2015024, by rfl⟩ : syracuseStep 2686699 = 4030049) B4030049
theorem B3022571 : Blo 1413526 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B2547463 : Blo 1413526 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B2121527 : Blo 1413526 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B12083039 : Blo 1413526 12083039 := bstep (se 1 (by rfl) ⟨9062279, by rfl⟩ : syracuseStep 12083039 = 18124559) B18124559
theorem B2686927 : Blo 1413526 2686927 := bstep (se 1 (by rfl) ⟨2015195, by rfl⟩ : syracuseStep 2686927 = 4030391) B4030391
theorem B4775975 : Blo 1413526 4775975 := bstep (se 1 (by rfl) ⟨3581981, by rfl⟩ : syracuseStep 4775975 = 7163963) B7163963
theorem B33104051 : Blo 1413526 33104051 := bstep (se 1 (by rfl) ⟨24828038, by rfl⟩ : syracuseStep 33104051 = 49656077) B49656077
theorem B2547931 : Blo 1413526 2547931 := bstep (se 1 (by rfl) ⟨1910948, by rfl⟩ : syracuseStep 2547931 = 3821897) B3821897
theorem B2121947 : Blo 1413526 2121947 := bstep (se 1 (by rfl) ⟨1591460, by rfl⟩ : syracuseStep 2121947 = 3182921) B3182921
theorem B2121959 : Blo 1413526 2121959 := bstep (se 1 (by rfl) ⟨1591469, by rfl⟩ : syracuseStep 2121959 = 3182939) B3182939
theorem B15294845 : Blo 1413526 15294845 := bstep (se 3 (by rfl) ⟨2867783, by rfl⟩ : syracuseStep 15294845 = 5735567) B5735567
theorem B2122121 : Blo 1413526 2122121 := bstep (se 2 (by rfl) ⟨795795, by rfl⟩ : syracuseStep 2122121 = 1591591) B1591591
theorem B130695565 : Blo 1413526 130695565 := bstep (se 3 (by rfl) ⟨24505418, by rfl⟩ : syracuseStep 130695565 = 49010837) B49010837
theorem B2122217 : Blo 1413526 2122217 := bstep (se 2 (by rfl) ⟨795831, by rfl⟩ : syracuseStep 2122217 = 1591663) B1591663
theorem B7651835 : Blo 1413526 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B7651903 : Blo 1413526 7651903 := bstep (se 1 (by rfl) ⟨5738927, by rfl⟩ : syracuseStep 7651903 = 11477855) B11477855
theorem B6046271 : Blo 1413526 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B2122343 : Blo 1413526 2122343 := bstep (se 1 (by rfl) ⟨1591757, by rfl⟩ : syracuseStep 2122343 = 3183515) B3183515
theorem B4776623 : Blo 1413526 4776623 := bstep (se 1 (by rfl) ⟨3582467, by rfl⟩ : syracuseStep 4776623 = 7164935) B7164935
theorem B2122475 : Blo 1413526 2122475 := bstep (se 1 (by rfl) ⟨1591856, by rfl⟩ : syracuseStep 2122475 = 3183713) B3183713
theorem B2122505 : Blo 1413526 2122505 := bstep (se 2 (by rfl) ⟨795939, by rfl⟩ : syracuseStep 2122505 = 1591879) B1591879
theorem B2122607 : Blo 1413526 2122607 := bstep (se 1 (by rfl) ⟨1591955, by rfl⟩ : syracuseStep 2122607 = 3183911) B3183911
theorem B4842451 : Blo 1413526 4842451 := bstep (se 1 (by rfl) ⟨3631838, by rfl⟩ : syracuseStep 4842451 = 7263677) B7263677
theorem B4776947 : Blo 1413526 4776947 := bstep (se 1 (by rfl) ⟨3582710, by rfl⟩ : syracuseStep 4776947 = 7165421) B7165421
theorem B2122859 : Blo 1413526 2122859 := bstep (se 1 (by rfl) ⟨1592144, by rfl⟩ : syracuseStep 2122859 = 3184289) B3184289
theorem B12911741 : Blo 1413526 12911741 := bstep (se 3 (by rfl) ⟨2420951, by rfl⟩ : syracuseStep 12911741 = 4841903) B4841903
theorem B20382977 : Blo 1413526 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B2123099 : Blo 1413526 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B8054153 : Blo 1413526 8054153 := bstep (se 2 (by rfl) ⟨3020307, by rfl⟩ : syracuseStep 8054153 = 6040615) B6040615
theorem B36242963 : Blo 1413526 36242963 := bstep (se 1 (by rfl) ⟨27182222, by rfl⟩ : syracuseStep 36242963 = 54364445) B54364445
theorem B5809745 : Blo 1413526 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B5097043 : Blo 1413526 5097043 := bstep (se 1 (by rfl) ⟨3822782, by rfl⟩ : syracuseStep 5097043 = 7645565) B7645565
theorem B13780595 : Blo 1413526 13780595 := bstep (se 1 (by rfl) ⟨10335446, by rfl⟩ : syracuseStep 13780595 = 20670893) B20670893
theorem B2385659 : Blo 1413526 2385659 := bstep (se 1 (by rfl) ⟨1789244, by rfl⟩ : syracuseStep 2385659 = 3578489) B3578489
theorem B2385895 : Blo 1413526 2385895 := bstep (se 1 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 2385895 = 3578843) B3578843
theorem B7645175 : Blo 1413526 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B2386111 : Blo 1413526 2386111 := bstep (se 1 (by rfl) ⟨1789583, by rfl⟩ : syracuseStep 2386111 = 3579167) B3579167
theorem B4303039 : Blo 1413526 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B3180779 : Blo 1413526 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B3582265 : Blo 1413526 3582265 := bstep (se 2 (by rfl) ⟨1343349, by rfl⟩ : syracuseStep 3582265 = 2686699) B2686699
theorem B6039947 : Blo 1413526 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B8055359 : Blo 1413526 8055359 := bstep (se 1 (by rfl) ⟨6041519, by rfl⟩ : syracuseStep 8055359 = 12083039) B12083039
theorem B3582569 : Blo 1413526 3582569 := bstep (se 2 (by rfl) ⟨1343463, by rfl⟩ : syracuseStep 3582569 = 2686927) B2686927
theorem B12077707 : Blo 1413526 12077707 := bstep (se 1 (by rfl) ⟨9058280, by rfl⟩ : syracuseStep 12077707 = 18116561) B18116561
theorem B4836023 : Blo 1413526 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B9563023 : Blo 1413526 9563023 := bstep (se 1 (by rfl) ⟨7172267, by rfl⟩ : syracuseStep 9563023 = 14344535) B14344535
theorem B2386847 : Blo 1413526 2386847 := bstep (se 1 (by rfl) ⟨1790135, by rfl⟩ : syracuseStep 2386847 = 3580271) B3580271
theorem B4770791 : Blo 1413526 4770791 := bstep (se 1 (by rfl) ⟨3578093, by rfl⟩ : syracuseStep 4770791 = 7156187) B7156187
theorem B13601843 : Blo 1413526 13601843 := bstep (se 1 (by rfl) ⟨10201382, by rfl⟩ : syracuseStep 13601843 = 20402765) B20402765
theorem B4771115 : Blo 1413526 4771115 := bstep (se 1 (by rfl) ⟨3578336, by rfl⟩ : syracuseStep 4771115 = 7156673) B7156673
theorem B2387279 : Blo 1413526 2387279 := bstep (se 1 (by rfl) ⟨1790459, by rfl⟩ : syracuseStep 2387279 = 3580919) B3580919
theorem B18369929 : Blo 1413526 18369929 := bstep (se 2 (by rfl) ⟨6888723, by rfl⟩ : syracuseStep 18369929 = 13777447) B13777447
theorem B3182075 : Blo 1413526 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B4771385 : Blo 1413526 4771385 := bstep (se 2 (by rfl) ⟨1789269, by rfl⟩ : syracuseStep 4771385 = 3578539) B3578539
theorem B6041213 : Blo 1413526 6041213 := bstep (se 3 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 6041213 = 2265455) B2265455
theorem B3182255 : Blo 1413526 3182255 := bstep (se 1 (by rfl) ⟨2386691, by rfl⟩ : syracuseStep 3182255 = 4773383) B4773383
theorem B4026131 : Blo 1413526 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B25800713 : Blo 1413526 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B10744001 : Blo 1413526 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B7164125 : Blo 1413526 7164125 := bstep (se 3 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 7164125 = 2686547) B2686547
theorem B3182903 : Blo 1413526 3182903 := bstep (se 1 (by rfl) ⟨2387177, by rfl⟩ : syracuseStep 3182903 = 4774355) B4774355
theorem B3182975 : Blo 1413526 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B7164287 : Blo 1413526 7164287 := bstep (se 1 (by rfl) ⟨5373215, by rfl⟩ : syracuseStep 7164287 = 10746431) B10746431
theorem B1413583 : Blo 1413526 1413583 := bstep (se 1 (by rfl) ⟨1060187, by rfl⟩ : syracuseStep 1413583 = 2120375) B2120375
theorem B2388575 : Blo 1413526 2388575 := bstep (se 1 (by rfl) ⟨1791431, by rfl⟩ : syracuseStep 2388575 = 3582863) B3582863
theorem B1413735 : Blo 1413526 1413735 := bstep (se 1 (by rfl) ⟨1060301, by rfl⟩ : syracuseStep 1413735 = 2120603) B2120603
theorem B13087403 : Blo 1413526 13087403 := bstep (se 1 (by rfl) ⟨9815552, by rfl⟩ : syracuseStep 13087403 = 19631105) B19631105
theorem B16102151 : Blo 1413526 16102151 := bstep (se 1 (by rfl) ⟨12076613, by rfl⟩ : syracuseStep 16102151 = 24153227) B24153227
theorem B1413999 : Blo 1413526 1413999 := bstep (se 1 (by rfl) ⟨1060499, by rfl⟩ : syracuseStep 1413999 = 2120999) B2120999
theorem B1414055 : Blo 1413526 1414055 := bstep (se 1 (by rfl) ⟨1060541, by rfl⟩ : syracuseStep 1414055 = 2121083) B2121083
theorem B10195931 : Blo 1413526 10195931 := bstep (se 1 (by rfl) ⟨7646948, by rfl⟩ : syracuseStep 10195931 = 15293897) B15293897
theorem B1414139 : Blo 1413526 1414139 := bstep (se 1 (by rfl) ⟨1060604, by rfl⟩ : syracuseStep 1414139 = 2121209) B2121209
theorem B3396617 : Blo 1413526 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B1414207 : Blo 1413526 1414207 := bstep (se 1 (by rfl) ⟨1060655, by rfl⟩ : syracuseStep 1414207 = 2121311) B2121311
theorem B2684011 : Blo 1413526 2684011 := bstep (se 1 (by rfl) ⟨2013008, by rfl⟩ : syracuseStep 2684011 = 4026017) B4026017
theorem B27194525 : Blo 1413526 27194525 := bstep (se 3 (by rfl) ⟨5098973, by rfl⟩ : syracuseStep 27194525 = 10197947) B10197947
theorem B1414351 : Blo 1413526 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B6796673 : Blo 1413526 6796673 := bstep (se 2 (by rfl) ⟨2548752, by rfl⟩ : syracuseStep 6796673 = 5097505) B5097505
theorem B2684315 : Blo 1413526 2684315 := bstep (se 1 (by rfl) ⟨2013236, by rfl⟩ : syracuseStep 2684315 = 4026473) B4026473
theorem B4773275 : Blo 1413526 4773275 := bstep (se 1 (by rfl) ⟨3579956, by rfl⟩ : syracuseStep 4773275 = 7159913) B7159913
theorem B1414555 : Blo 1413526 1414555 := bstep (se 1 (by rfl) ⟨1060916, by rfl⟩ : syracuseStep 1414555 = 2121833) B2121833
theorem B8598973 : Blo 1413526 8598973 := bstep (se 3 (by rfl) ⟨1612307, by rfl⟩ : syracuseStep 8598973 = 3224615) B3224615
theorem B5371393 : Blo 1413526 5371393 := bstep (se 2 (by rfl) ⟨2014272, by rfl⟩ : syracuseStep 5371393 = 4028545) B4028545
theorem B3184199 : Blo 1413526 3184199 := bstep (se 1 (by rfl) ⟨2388149, by rfl⟩ : syracuseStep 3184199 = 4776299) B4776299
theorem B1414767 : Blo 1413526 1414767 := bstep (se 1 (by rfl) ⟨1061075, by rfl⟩ : syracuseStep 1414767 = 2122151) B2122151
theorem B1414823 : Blo 1413526 1414823 := bstep (se 1 (by rfl) ⟨1061117, by rfl⟩ : syracuseStep 1414823 = 2122235) B2122235
theorem B2152103 : Blo 1413526 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B8599243 : Blo 1413526 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B7157483 : Blo 1413526 7157483 := bstep (se 1 (by rfl) ⟨5368112, by rfl⟩ : syracuseStep 7157483 = 10736225) B10736225
theorem B1414907 : Blo 1413526 1414907 := bstep (se 1 (by rfl) ⟨1061180, by rfl⟩ : syracuseStep 1414907 = 2122361) B2122361
theorem B3184379 : Blo 1413526 3184379 := bstep (se 1 (by rfl) ⟨2388284, by rfl⟩ : syracuseStep 3184379 = 4776569) B4776569
theorem B1414943 : Blo 1413526 1414943 := bstep (se 1 (by rfl) ⟨1061207, by rfl⟩ : syracuseStep 1414943 = 2122415) B2122415
theorem B1414975 : Blo 1413526 1414975 := bstep (se 1 (by rfl) ⟨1061231, by rfl⟩ : syracuseStep 1414975 = 2122463) B2122463
theorem B13596497 : Blo 1413526 13596497 := bstep (se 2 (by rfl) ⟨5098686, by rfl⟩ : syracuseStep 13596497 = 10197373) B10197373
theorem B39221111 : Blo 1413526 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B1415151 : Blo 1413526 1415151 := bstep (se 1 (by rfl) ⟨1061363, by rfl⟩ : syracuseStep 1415151 = 2122727) B2122727
theorem B3020897 : Blo 1413526 3020897 := bstep (se 2 (by rfl) ⟨1132836, by rfl⟩ : syracuseStep 3020897 = 2265673) B2265673
theorem B4774031 : Blo 1413526 4774031 := bstep (se 1 (by rfl) ⟨3580523, by rfl⟩ : syracuseStep 4774031 = 7161047) B7161047
theorem B1415323 : Blo 1413526 1415323 := bstep (se 1 (by rfl) ⟨1061492, by rfl⟩ : syracuseStep 1415323 = 2122985) B2122985
theorem B2685089 : Blo 1413526 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B1415359 : Blo 1413526 1415359 := bstep (se 1 (by rfl) ⟨1061519, by rfl⟩ : syracuseStep 1415359 = 2123039) B2123039
theorem B3397895 : Blo 1413526 3397895 := bstep (se 1 (by rfl) ⟨2548421, by rfl⟩ : syracuseStep 3397895 = 5096843) B5096843
theorem B8050985 : Blo 1413526 8050985 := bstep (se 2 (by rfl) ⟨3019119, by rfl⟩ : syracuseStep 8050985 = 6038239) B6038239
theorem B1415471 : Blo 1413526 1415471 := bstep (se 1 (by rfl) ⟨1061603, by rfl⟩ : syracuseStep 1415471 = 2123207) B2123207
theorem B8608123 : Blo 1413526 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B6126137 : Blo 1413526 6126137 := bstep (se 2 (by rfl) ⟨2297301, by rfl⟩ : syracuseStep 6126137 = 4594603) B4594603
theorem B2120297 : Blo 1413526 2120297 := bstep (se 2 (by rfl) ⟨795111, by rfl⟩ : syracuseStep 2120297 = 1590223) B1590223
theorem B5372639 : Blo 1413526 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B9681731 : Blo 1413526 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B13597571 : Blo 1413526 13597571 := bstep (se 1 (by rfl) ⟨10198178, by rfl⟩ : syracuseStep 13597571 = 20396357) B20396357
theorem B2014159 : Blo 1413526 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B8059985 : Blo 1413526 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B15293555 : Blo 1413526 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B2120825 : Blo 1413526 2120825 := bstep (se 2 (by rfl) ⟨795309, by rfl⟩ : syracuseStep 2120825 = 1590619) B1590619
theorem B7158941 : Blo 1413526 7158941 := bstep (se 3 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 7158941 = 2684603) B2684603
theorem B2120927 : Blo 1413526 2120927 := bstep (se 1 (by rfl) ⟨1590695, by rfl⟩ : syracuseStep 2120927 = 3181391) B3181391
theorem B4775165 : Blo 1413526 4775165 := bstep (se 3 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 4775165 = 1790687) B1790687
theorem B2120969 : Blo 1413526 2120969 := bstep (se 2 (by rfl) ⟨795363, by rfl⟩ : syracuseStep 2120969 = 1590727) B1590727
theorem B2121071 : Blo 1413526 2121071 := bstep (se 1 (by rfl) ⟨1590803, by rfl⟩ : syracuseStep 2121071 = 3181607) B3181607
theorem B3022247 : Blo 1413526 3022247 := bstep (se 1 (by rfl) ⟨2266685, by rfl⟩ : syracuseStep 3022247 = 4533371) B4533371
theorem B20676035 : Blo 1413526 20676035 := bstep (se 1 (by rfl) ⟨15507026, by rfl⟩ : syracuseStep 20676035 = 31014053) B31014053
theorem B2121191 : Blo 1413526 2121191 := bstep (se 1 (by rfl) ⟨1590893, by rfl⟩ : syracuseStep 2121191 = 3181787) B3181787
theorem B3399259 : Blo 1413526 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B3022427 : Blo 1413526 3022427 := bstep (se 1 (by rfl) ⟨2266820, by rfl⟩ : syracuseStep 3022427 = 4533641) B4533641
theorem B2121323 : Blo 1413526 2121323 := bstep (se 1 (by rfl) ⟨1590992, by rfl⟩ : syracuseStep 2121323 = 3181985) B3181985
theorem B6979259 : Blo 1413526 6979259 := bstep (se 1 (by rfl) ⟨5234444, by rfl⟩ : syracuseStep 6979259 = 10468889) B10468889
theorem B2121449 : Blo 1413526 2121449 := bstep (se 2 (by rfl) ⟨795543, by rfl⟩ : syracuseStep 2121449 = 1591087) B1591087
theorem B2015047 : Blo 1413526 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B2121593 : Blo 1413526 2121593 := bstep (se 2 (by rfl) ⟨795597, by rfl⟩ : syracuseStep 2121593 = 1591195) B1591195
theorem B24166349 : Blo 1413526 24166349 := bstep (se 3 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 24166349 = 9062381) B9062381
theorem B2121695 : Blo 1413526 2121695 := bstep (se 1 (by rfl) ⟨1591271, by rfl⟩ : syracuseStep 2121695 = 3182543) B3182543
theorem B22069367 : Blo 1413526 22069367 := bstep (se 1 (by rfl) ⟨16552025, by rfl⟩ : syracuseStep 22069367 = 33104051) B33104051
theorem B4776083 : Blo 1413526 4776083 := bstep (se 1 (by rfl) ⟨3582062, by rfl⟩ : syracuseStep 4776083 = 7164125) B7164125
theorem B2121935 : Blo 1413526 2121935 := bstep (se 1 (by rfl) ⟨1591451, by rfl⟩ : syracuseStep 2121935 = 3182903) B3182903
theorem B2121983 : Blo 1413526 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B4776191 : Blo 1413526 4776191 := bstep (se 1 (by rfl) ⟨3582143, by rfl⟩ : syracuseStep 4776191 = 7164287) B7164287
theorem B4030847 : Blo 1413526 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B4776353 : Blo 1413526 4776353 := bstep (se 2 (by rfl) ⟨1791132, by rfl⟩ : syracuseStep 4776353 = 3582265) B3582265
theorem B7160237 : Blo 1413526 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B8724935 : Blo 1413526 8724935 := bstep (se 1 (by rfl) ⟨6543701, by rfl⟩ : syracuseStep 8724935 = 13087403) B13087403
theorem B11477497 : Blo 1413526 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B174260753 : Blo 1413526 174260753 := bstep (se 2 (by rfl) ⟨65347782, by rfl⟩ : syracuseStep 174260753 = 130695565) B130695565
theorem B18129683 : Blo 1413526 18129683 := bstep (se 1 (by rfl) ⟨13597262, by rfl⟩ : syracuseStep 18129683 = 27194525) B27194525
theorem B4531115 : Blo 1413526 4531115 := bstep (se 1 (by rfl) ⟨3398336, by rfl⟩ : syracuseStep 4531115 = 6796673) B6796673
theorem B16106525 : Blo 1413526 16106525 := bstep (se 3 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 16106525 = 6039947) B6039947
theorem B2122799 : Blo 1413526 2122799 := bstep (se 1 (by rfl) ⟨1592099, by rfl⟩ : syracuseStep 2122799 = 3184199) B3184199
theorem B1590439 : Blo 1413526 1590439 := bstep (se 1 (by rfl) ⟨1192829, by rfl⟩ : syracuseStep 1590439 = 2385659) B2385659
theorem B2122919 : Blo 1413526 2122919 := bstep (se 1 (by rfl) ⟨1592189, by rfl⟩ : syracuseStep 2122919 = 3184379) B3184379
theorem B6456601 : Blo 1413526 6456601 := bstep (se 2 (by rfl) ⟨2421225, by rfl⟩ : syracuseStep 6456601 = 4842451) B4842451
theorem B5096783 : Blo 1413526 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B5367323 : Blo 1413526 5367323 := bstep (se 1 (by rfl) ⟨4025492, by rfl⟩ : syracuseStep 5367323 = 8050985) B8050985
theorem B15492653 : Blo 1413526 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B3581759 : Blo 1413526 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B1591231 : Blo 1413526 1591231 := bstep (se 1 (by rfl) ⟨1193423, by rfl⟩ : syracuseStep 1591231 = 2386847) B2386847
theorem B3180527 : Blo 1413526 3180527 := bstep (se 1 (by rfl) ⟨2385395, by rfl⟩ : syracuseStep 3180527 = 4770791) B4770791
theorem B7161857 : Blo 1413526 7161857 := bstep (se 2 (by rfl) ⟨2685696, by rfl⟩ : syracuseStep 7161857 = 5371393) B5371393
theorem B4532345 : Blo 1413526 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B3180743 : Blo 1413526 3180743 := bstep (se 1 (by rfl) ⟨2385557, by rfl⟩ : syracuseStep 3180743 = 4771115) B4771115
theorem B1591519 : Blo 1413526 1591519 := bstep (se 1 (by rfl) ⟨1193639, by rfl⟩ : syracuseStep 1591519 = 2387279) B2387279
theorem B3180923 : Blo 1413526 3180923 := bstep (se 1 (by rfl) ⟨2385692, by rfl⟩ : syracuseStep 3180923 = 4771385) B4771385
theorem B3181193 : Blo 1413526 3181193 := bstep (se 2 (by rfl) ⟨1192947, by rfl⟩ : syracuseStep 3181193 = 2385895) B2385895
theorem B7162667 : Blo 1413526 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B3181481 : Blo 1413526 3181481 := bstep (se 2 (by rfl) ⟨1193055, by rfl⟩ : syracuseStep 3181481 = 2386111) B2386111
theorem B5737385 : Blo 1413526 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B1592383 : Blo 1413526 1592383 := bstep (se 1 (by rfl) ⟨1194287, by rfl⟩ : syracuseStep 1592383 = 2388575) B2388575
theorem B10734767 : Blo 1413526 10734767 := bstep (se 1 (by rfl) ⟨8051075, by rfl⟩ : syracuseStep 10734767 = 16102151) B16102151
theorem B2264411 : Blo 1413526 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B10202537 : Blo 1413526 10202537 := bstep (se 2 (by rfl) ⟨3825951, by rfl⟩ : syracuseStep 10202537 = 7651903) B7651903
theorem B5369435 : Blo 1413526 5369435 := bstep (se 1 (by rfl) ⟨4027076, by rfl⟩ : syracuseStep 5369435 = 8054153) B8054153
theorem B3182183 : Blo 1413526 3182183 := bstep (se 1 (by rfl) ⟨2386637, by rfl⟩ : syracuseStep 3182183 = 4773275) B4773275
theorem B1789543 : Blo 1413526 1789543 := bstep (se 1 (by rfl) ⟨1342157, by rfl⟩ : syracuseStep 1789543 = 2684315) B2684315
theorem B24161975 : Blo 1413526 24161975 := bstep (se 1 (by rfl) ⟨18121481, by rfl⟩ : syracuseStep 24161975 = 36242963) B36242963
theorem B9187063 : Blo 1413526 9187063 := bstep (se 1 (by rfl) ⟨6890297, by rfl⟩ : syracuseStep 9187063 = 13780595) B13780595
theorem B4771655 : Blo 1413526 4771655 := bstep (se 1 (by rfl) ⟨3578741, by rfl⟩ : syracuseStep 4771655 = 7157483) B7157483
theorem B12750697 : Blo 1413526 12750697 := bstep (se 2 (by rfl) ⟨4781511, by rfl⟩ : syracuseStep 12750697 = 9563023) B9563023
theorem B9064331 : Blo 1413526 9064331 := bstep (se 1 (by rfl) ⟨6798248, by rfl⟩ : syracuseStep 9064331 = 13596497) B13596497
theorem B3182687 : Blo 1413526 3182687 := bstep (se 1 (by rfl) ⟨2387015, by rfl⟩ : syracuseStep 3182687 = 4774031) B4774031
theorem B2265263 : Blo 1413526 2265263 := bstep (se 1 (by rfl) ⟨1698947, by rfl⟩ : syracuseStep 2265263 = 3397895) B3397895
theorem B4084091 : Blo 1413526 4084091 := bstep (se 1 (by rfl) ⟨3063068, by rfl⟩ : syracuseStep 4084091 = 6126137) B6126137
theorem B5370239 : Blo 1413526 5370239 := bstep (se 1 (by rfl) ⟨4027679, by rfl⟩ : syracuseStep 5370239 = 8055359) B8055359
theorem B1413531 : Blo 1413526 1413531 := bstep (se 1 (by rfl) ⟨1060148, by rfl⟩ : syracuseStep 1413531 = 2120297) B2120297
theorem B2388379 : Blo 1413526 2388379 := bstep (se 1 (by rfl) ⟨1791284, by rfl⟩ : syracuseStep 2388379 = 3582569) B3582569
theorem B5738941 : Blo 1413526 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B3224015 : Blo 1413526 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B11465297 : Blo 1413526 11465297 := bstep (se 2 (by rfl) ⟨4299486, by rfl⟩ : syracuseStep 11465297 = 8598973) B8598973
theorem B9065047 : Blo 1413526 9065047 := bstep (se 1 (by rfl) ⟨6798785, by rfl⟩ : syracuseStep 9065047 = 13597571) B13597571
theorem B10195703 : Blo 1413526 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B1413883 : Blo 1413526 1413883 := bstep (se 1 (by rfl) ⟨1060412, by rfl⟩ : syracuseStep 1413883 = 2120825) B2120825
theorem B4772627 : Blo 1413526 4772627 := bstep (se 1 (by rfl) ⟨3579470, by rfl⟩ : syracuseStep 4772627 = 7158941) B7158941
theorem B6796057 : Blo 1413526 6796057 := bstep (se 2 (by rfl) ⟨2548521, by rfl⟩ : syracuseStep 6796057 = 5097043) B5097043
theorem B1413951 : Blo 1413526 1413951 := bstep (se 1 (by rfl) ⟨1060463, by rfl⟩ : syracuseStep 1413951 = 2120927) B2120927
theorem B3183443 : Blo 1413526 3183443 := bstep (se 1 (by rfl) ⟨2387582, by rfl⟩ : syracuseStep 3183443 = 4775165) B4775165
theorem B1413979 : Blo 1413526 1413979 := bstep (se 1 (by rfl) ⟨1060484, by rfl⟩ : syracuseStep 1413979 = 2120969) B2120969
theorem B1414047 : Blo 1413526 1414047 := bstep (se 1 (by rfl) ⟨1060535, by rfl⟩ : syracuseStep 1414047 = 2121071) B2121071
theorem B11465657 : Blo 1413526 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B13784023 : Blo 1413526 13784023 := bstep (se 1 (by rfl) ⟨10338017, by rfl⟩ : syracuseStep 13784023 = 20676035) B20676035
theorem B1414127 : Blo 1413526 1414127 := bstep (se 1 (by rfl) ⟨1060595, by rfl⟩ : syracuseStep 1414127 = 2121191) B2121191
theorem B1414215 : Blo 1413526 1414215 := bstep (se 1 (by rfl) ⟨1060661, by rfl⟩ : syracuseStep 1414215 = 2121323) B2121323
theorem B4027475 : Blo 1413526 4027475 := bstep (se 1 (by rfl) ⟨3020606, by rfl⟩ : syracuseStep 4027475 = 6041213) B6041213
theorem B1414299 : Blo 1413526 1414299 := bstep (se 1 (by rfl) ⟨1060724, by rfl⟩ : syracuseStep 1414299 = 2121449) B2121449
theorem B2684087 : Blo 1413526 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B1414395 : Blo 1413526 1414395 := bstep (se 1 (by rfl) ⟨1060796, by rfl⟩ : syracuseStep 1414395 = 2121593) B2121593
theorem B16110899 : Blo 1413526 16110899 := bstep (se 1 (by rfl) ⟨12083174, by rfl⟩ : syracuseStep 16110899 = 24166349) B24166349
theorem B1414463 : Blo 1413526 1414463 := bstep (se 1 (by rfl) ⟨1060847, by rfl⟩ : syracuseStep 1414463 = 2121695) B2121695
theorem B17200475 : Blo 1413526 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B3183983 : Blo 1413526 3183983 := bstep (se 1 (by rfl) ⟨2387987, by rfl⟩ : syracuseStep 3183983 = 4775975) B4775975
theorem B1414631 : Blo 1413526 1414631 := bstep (se 1 (by rfl) ⟨1060973, by rfl⟩ : syracuseStep 1414631 = 2121947) B2121947
theorem B1414639 : Blo 1413526 1414639 := bstep (se 1 (by rfl) ⟨1060979, by rfl⟩ : syracuseStep 1414639 = 2121959) B2121959
theorem B1414747 : Blo 1413526 1414747 := bstep (se 1 (by rfl) ⟨1061060, by rfl⟩ : syracuseStep 1414747 = 2122121) B2122121
theorem B3397241 : Blo 1413526 3397241 := bstep (se 2 (by rfl) ⟨1273965, by rfl⟩ : syracuseStep 3397241 = 2547931) B2547931
theorem B1414811 : Blo 1413526 1414811 := bstep (se 1 (by rfl) ⟨1061108, by rfl⟩ : syracuseStep 1414811 = 2122217) B2122217
theorem B5101223 : Blo 1413526 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B1414895 : Blo 1413526 1414895 := bstep (se 1 (by rfl) ⟨1061171, by rfl⟩ : syracuseStep 1414895 = 2122343) B2122343
theorem B3184415 : Blo 1413526 3184415 := bstep (se 1 (by rfl) ⟨2388311, by rfl⟩ : syracuseStep 3184415 = 4776623) B4776623
theorem B1414983 : Blo 1413526 1414983 := bstep (se 1 (by rfl) ⟨1061237, by rfl⟩ : syracuseStep 1414983 = 2122475) B2122475
theorem B1415003 : Blo 1413526 1415003 := bstep (se 1 (by rfl) ⟨1061252, by rfl⟩ : syracuseStep 1415003 = 2122505) B2122505
theorem B1415071 : Blo 1413526 1415071 := bstep (se 1 (by rfl) ⟨1061303, by rfl⟩ : syracuseStep 1415071 = 2122607) B2122607
theorem B6797287 : Blo 1413526 6797287 := bstep (se 1 (by rfl) ⟨5097965, by rfl⟩ : syracuseStep 6797287 = 10195931) B10195931
theorem B3184631 : Blo 1413526 3184631 := bstep (se 1 (by rfl) ⟨2388473, by rfl⟩ : syracuseStep 3184631 = 4776947) B4776947
theorem B1415239 : Blo 1413526 1415239 := bstep (se 1 (by rfl) ⟨1061429, by rfl⟩ : syracuseStep 1415239 = 2122859) B2122859
theorem B8607827 : Blo 1413526 8607827 := bstep (se 1 (by rfl) ⟨6455870, by rfl⟩ : syracuseStep 8607827 = 12911741) B12911741
theorem B13588651 : Blo 1413526 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B16103609 : Blo 1413526 16103609 := bstep (se 2 (by rfl) ⟨6038853, by rfl⟩ : syracuseStep 16103609 = 12077707) B12077707
theorem B1415399 : Blo 1413526 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B40786253 : Blo 1413526 40786253 := bstep (se 3 (by rfl) ⟨7647422, by rfl⟩ : syracuseStep 40786253 = 15294845) B15294845
theorem B48986477 : Blo 1413526 48986477 := bstep (se 3 (by rfl) ⟨9184964, by rfl⟩ : syracuseStep 48986477 = 18369929) B18369929
theorem B26147407 : Blo 1413526 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B2685545 : Blo 1413526 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B2013931 : Blo 1413526 2013931 := bstep (se 1 (by rfl) ⟨1510448, by rfl⟩ : syracuseStep 2013931 = 3020897) B3020897
theorem B3578681 : Blo 1413526 3578681 := bstep (se 2 (by rfl) ⟨1342005, by rfl⟩ : syracuseStep 3578681 = 2684011) B2684011
theorem B2120519 : Blo 1413526 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B10746917 : Blo 1413526 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B6454487 : Blo 1413526 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B9067895 : Blo 1413526 9067895 := bstep (se 1 (by rfl) ⟨6800921, by rfl⟩ : syracuseStep 9067895 = 13601843) B13601843
theorem B5373323 : Blo 1413526 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B2014831 : Blo 1413526 2014831 := bstep (se 1 (by rfl) ⟨1511123, by rfl⟩ : syracuseStep 2014831 = 3022247) B3022247
theorem B2121383 : Blo 1413526 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B2014951 : Blo 1413526 2014951 := bstep (se 1 (by rfl) ⟨1511213, by rfl⟩ : syracuseStep 2014951 = 3022427) B3022427
theorem B2121503 : Blo 1413526 2121503 := bstep (se 1 (by rfl) ⟨1591127, by rfl⟩ : syracuseStep 2121503 = 3182255) B3182255
theorem B4652839 : Blo 1413526 4652839 := bstep (se 1 (by rfl) ⟨3489629, by rfl⟩ : syracuseStep 4652839 = 6979259) B6979259
theorem B2121791 : Blo 1413526 2121791 := bstep (se 1 (by rfl) ⟨1591343, by rfl⟩ : syracuseStep 2121791 = 3182687) B3182687
theorem B14712911 : Blo 1413526 14712911 := bstep (se 1 (by rfl) ⟨11034683, by rfl⟩ : syracuseStep 14712911 = 22069367) B22069367
theorem B22954205 : Blo 1413526 22954205 := bstep (se 3 (by rfl) ⟨4303913, by rfl⟩ : syracuseStep 22954205 = 8607827) B8607827
theorem B3580159 : Blo 1413526 3580159 := bstep (se 1 (by rfl) ⟨2685119, by rfl⟩ : syracuseStep 3580159 = 5370239) B5370239
theorem B2687231 : Blo 1413526 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B2122025 : Blo 1413526 2122025 := bstep (se 2 (by rfl) ⟨795759, by rfl⟩ : syracuseStep 2122025 = 1591519) B1591519
theorem B5816623 : Blo 1413526 5816623 := bstep (se 1 (by rfl) ⟨4362467, by rfl⟩ : syracuseStep 5816623 = 8724935) B8724935
theorem B7643531 : Blo 1413526 7643531 := bstep (se 1 (by rfl) ⟨5732648, by rfl⟩ : syracuseStep 7643531 = 11465297) B11465297
theorem B2122295 : Blo 1413526 2122295 := bstep (se 1 (by rfl) ⟨1591721, by rfl⟩ : syracuseStep 2122295 = 3183443) B3183443
theorem B7651921 : Blo 1413526 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B7643771 : Blo 1413526 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B15303329 : Blo 1413526 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B10740599 : Blo 1413526 10740599 := bstep (se 1 (by rfl) ⟨8055449, by rfl⟩ : syracuseStep 10740599 = 16110899) B16110899
theorem B13591421 : Blo 1413526 13591421 := bstep (se 3 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 13591421 = 5096783) B5096783
theorem B2122655 : Blo 1413526 2122655 := bstep (se 1 (by rfl) ⟨1591991, by rfl⟩ : syracuseStep 2122655 = 3183983) B3183983
theorem B9061409 : Blo 1413526 9061409 := bstep (se 2 (by rfl) ⟨3398028, by rfl⟩ : syracuseStep 9061409 = 6796057) B6796057
theorem B2122943 : Blo 1413526 2122943 := bstep (se 1 (by rfl) ⟨1592207, by rfl⟩ : syracuseStep 2122943 = 3184415) B3184415
theorem B48997669 : Blo 1413526 48997669 := bstep (se 4 (by rfl) ⟨4593531, by rfl⟩ : syracuseStep 48997669 = 9187063) B9187063
theorem B2123087 : Blo 1413526 2123087 := bstep (se 1 (by rfl) ⟨1592315, by rfl⟩ : syracuseStep 2123087 = 3184631) B3184631
theorem B2123177 : Blo 1413526 2123177 := bstep (se 2 (by rfl) ⟨796191, by rfl⟩ : syracuseStep 2123177 = 1592383) B1592383
theorem B27190835 : Blo 1413526 27190835 := bstep (se 1 (by rfl) ⟨20393126, by rfl⟩ : syracuseStep 27190835 = 40786253) B40786253
theorem B2385787 : Blo 1413526 2385787 := bstep (se 1 (by rfl) ⟨1789340, by rfl⟩ : syracuseStep 2385787 = 3578681) B3578681
theorem B68003717 : Blo 1413526 68003717 := bstep (se 4 (by rfl) ⟨6375348, by rfl⟩ : syracuseStep 68003717 = 12750697) B12750697
theorem B2386057 : Blo 1413526 2386057 := bstep (se 2 (by rfl) ⟨894771, by rfl⟩ : syracuseStep 2386057 = 1789543) B1789543
theorem B4302991 : Blo 1413526 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B1509607 : Blo 1413526 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B3582215 : Blo 1413526 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B6801691 : Blo 1413526 6801691 := bstep (se 1 (by rfl) ⟨5101268, by rfl⟩ : syracuseStep 6801691 = 10202537) B10202537
theorem B6203785 : Blo 1413526 6203785 := bstep (se 2 (by rfl) ⟨2326419, by rfl⟩ : syracuseStep 6203785 = 4652839) B4652839
theorem B16107983 : Blo 1413526 16107983 := bstep (se 1 (by rfl) ⟨12080987, by rfl⟩ : syracuseStep 16107983 = 24161975) B24161975
theorem B3181103 : Blo 1413526 3181103 := bstep (se 1 (by rfl) ⟨2385827, by rfl⟩ : syracuseStep 3181103 = 4771655) B4771655
theorem B9063049 : Blo 1413526 9063049 := bstep (se 2 (by rfl) ⟨3398643, by rfl⟩ : syracuseStep 9063049 = 6797287) B6797287
theorem B1510175 : Blo 1413526 1510175 := bstep (se 1 (by rfl) ⟨1132631, by rfl⟩ : syracuseStep 1510175 = 2265263) B2265263
theorem B2722727 : Blo 1413526 2722727 := bstep (se 1 (by rfl) ⟨2042045, by rfl⟩ : syracuseStep 2722727 = 4084091) B4084091
theorem B2149343 : Blo 1413526 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B116173835 : Blo 1413526 116173835 := bstep (se 1 (by rfl) ⟨87130376, by rfl⟩ : syracuseStep 116173835 = 174260753) B174260753
theorem B3181751 : Blo 1413526 3181751 := bstep (se 1 (by rfl) ⟨2386313, by rfl⟩ : syracuseStep 3181751 = 4772627) B4772627
theorem B12086455 : Blo 1413526 12086455 := bstep (se 1 (by rfl) ⟨9064841, by rfl⟩ : syracuseStep 12086455 = 18129683) B18129683
theorem B12086729 : Blo 1413526 12086729 := bstep (se 2 (by rfl) ⟨4532523, by rfl⟩ : syracuseStep 12086729 = 9065047) B9065047
theorem B1789391 : Blo 1413526 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B2264827 : Blo 1413526 2264827 := bstep (se 1 (by rfl) ⟨1698620, by rfl⟩ : syracuseStep 2264827 = 3397241) B3397241
theorem B2387839 : Blo 1413526 2387839 := bstep (se 1 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 2387839 = 3581759) B3581759
theorem B10735739 : Blo 1413526 10735739 := bstep (se 1 (by rfl) ⟨8051804, by rfl⟩ : syracuseStep 10735739 = 16103609) B16103609
theorem B34435205 : Blo 1413526 34435205 := bstep (se 4 (by rfl) ⟨3228300, by rfl⟩ : syracuseStep 34435205 = 6456601) B6456601
theorem B32657651 : Blo 1413526 32657651 := bstep (se 1 (by rfl) ⟨24493238, by rfl⟩ : syracuseStep 32657651 = 48986477) B48986477
theorem B1790363 : Blo 1413526 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B13603261 : Blo 1413526 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B1413679 : Blo 1413526 1413679 := bstep (se 1 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 1413679 = 2120519) B2120519
theorem B7164611 : Blo 1413526 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B7156511 : Blo 1413526 7156511 := bstep (se 1 (by rfl) ⟨5367383, by rfl⟩ : syracuseStep 7156511 = 10734767) B10734767
theorem B1414255 : Blo 1413526 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1414335 : Blo 1413526 1414335 := bstep (se 1 (by rfl) ⟨1060751, by rfl⟩ : syracuseStep 1414335 = 2121503) B2121503
theorem B6042887 : Blo 1413526 6042887 := bstep (se 1 (by rfl) ⟨4532165, by rfl⟩ : syracuseStep 6042887 = 9064331) B9064331
theorem B3184055 : Blo 1413526 3184055 := bstep (se 1 (by rfl) ⟨2388041, by rfl⟩ : syracuseStep 3184055 = 4776083) B4776083
theorem B1414623 : Blo 1413526 1414623 := bstep (se 1 (by rfl) ⟨1060967, by rfl⟩ : syracuseStep 1414623 = 2121935) B2121935
theorem B1414655 : Blo 1413526 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B3184127 : Blo 1413526 3184127 := bstep (se 1 (by rfl) ⟨2388095, by rfl⟩ : syracuseStep 3184127 = 4776191) B4776191
theorem B18118201 : Blo 1413526 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B3184235 : Blo 1413526 3184235 := bstep (se 1 (by rfl) ⟨2388176, by rfl⟩ : syracuseStep 3184235 = 4776353) B4776353
theorem B4773491 : Blo 1413526 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B6797135 : Blo 1413526 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B3184505 : Blo 1413526 3184505 := bstep (se 2 (by rfl) ⟨1194189, by rfl⟩ : syracuseStep 3184505 = 2388379) B2388379
theorem B3020743 : Blo 1413526 3020743 := bstep (se 1 (by rfl) ⟨2265557, by rfl⟩ : syracuseStep 3020743 = 4531115) B4531115
theorem B10737683 : Blo 1413526 10737683 := bstep (se 1 (by rfl) ⟨8053262, by rfl⟩ : syracuseStep 10737683 = 16106525) B16106525
theorem B1415199 : Blo 1413526 1415199 := bstep (se 1 (by rfl) ⟨1061399, by rfl⟩ : syracuseStep 1415199 = 2122799) B2122799
theorem B2684983 : Blo 1413526 2684983 := bstep (se 1 (by rfl) ⟨2013737, by rfl⟩ : syracuseStep 2684983 = 4027475) B4027475
theorem B34863209 : Blo 1413526 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B1415279 : Blo 1413526 1415279 := bstep (se 1 (by rfl) ⟨1061459, by rfl⟩ : syracuseStep 1415279 = 2122919) B2122919
theorem B11466983 : Blo 1413526 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B2685241 : Blo 1413526 2685241 := bstep (se 2 (by rfl) ⟨1006965, by rfl⟩ : syracuseStep 2685241 = 2013931) B2013931
theorem B3578215 : Blo 1413526 3578215 := bstep (se 1 (by rfl) ⟨2683661, by rfl⟩ : syracuseStep 3578215 = 5367323) B5367323
theorem B10328435 : Blo 1413526 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B2120351 : Blo 1413526 2120351 := bstep (se 1 (by rfl) ⟨1590263, by rfl⟩ : syracuseStep 2120351 = 3180527) B3180527
theorem B4774571 : Blo 1413526 4774571 := bstep (se 1 (by rfl) ⟨3580928, by rfl⟩ : syracuseStep 4774571 = 7161857) B7161857
theorem B3021563 : Blo 1413526 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B2120495 : Blo 1413526 2120495 := bstep (se 1 (by rfl) ⟨1590371, by rfl⟩ : syracuseStep 2120495 = 3180743) B3180743
theorem B2120585 : Blo 1413526 2120585 := bstep (se 2 (by rfl) ⟨795219, by rfl⟩ : syracuseStep 2120585 = 1590439) B1590439
theorem B2120615 : Blo 1413526 2120615 := bstep (se 1 (by rfl) ⟨1590461, by rfl⟩ : syracuseStep 2120615 = 3180923) B3180923
theorem B2120795 : Blo 1413526 2120795 := bstep (se 1 (by rfl) ⟨1590596, by rfl⟩ : syracuseStep 2120795 = 3181193) B3181193
theorem B4775111 : Blo 1413526 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B2120987 : Blo 1413526 2120987 := bstep (se 1 (by rfl) ⟨1590740, by rfl⟩ : syracuseStep 2120987 = 3181481) B3181481
theorem B3824923 : Blo 1413526 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B2686441 : Blo 1413526 2686441 := bstep (se 2 (by rfl) ⟨1007415, by rfl⟩ : syracuseStep 2686441 = 2014831) B2014831
theorem B6045263 : Blo 1413526 6045263 := bstep (se 1 (by rfl) ⟨4533947, by rfl⟩ : syracuseStep 6045263 = 9067895) B9067895
theorem B2686601 : Blo 1413526 2686601 := bstep (se 2 (by rfl) ⟨1007475, by rfl⟩ : syracuseStep 2686601 = 2014951) B2014951
theorem B3579623 : Blo 1413526 3579623 := bstep (se 1 (by rfl) ⟨2684717, by rfl⟩ : syracuseStep 3579623 = 5369435) B5369435
theorem B2121455 : Blo 1413526 2121455 := bstep (se 1 (by rfl) ⟨1591091, by rfl⟩ : syracuseStep 2121455 = 3182183) B3182183
theorem B73514789 : Blo 1413526 73514789 := bstep (se 4 (by rfl) ⟨6892011, by rfl⟩ : syracuseStep 73514789 = 13784023) B13784023
theorem B2121641 : Blo 1413526 2121641 := bstep (se 2 (by rfl) ⟨795615, by rfl⟩ : syracuseStep 2121641 = 1591231) B1591231
theorem B3579977 : Blo 1413526 3579977 := bstep (se 2 (by rfl) ⟨1342491, by rfl⟩ : syracuseStep 3579977 = 2684983) B2684983
theorem B9068921 : Blo 1413526 9068921 := bstep (se 2 (by rfl) ⟨3400845, by rfl⟩ : syracuseStep 9068921 = 6801691) B6801691
theorem B3580321 : Blo 1413526 3580321 := bstep (se 2 (by rfl) ⟨1342620, by rfl⟩ : syracuseStep 3580321 = 2685241) B2685241
theorem B5095847 : Blo 1413526 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B4776407 : Blo 1413526 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B61211213 : Blo 1413526 61211213 := bstep (se 3 (by rfl) ⟨11477102, by rfl⟩ : syracuseStep 61211213 = 22954205) B22954205
theorem B7160399 : Blo 1413526 7160399 := bstep (se 1 (by rfl) ⟨5370299, by rfl⟩ : syracuseStep 7160399 = 10740599) B10740599
theorem B18137681 : Blo 1413526 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B9060947 : Blo 1413526 9060947 := bstep (se 1 (by rfl) ⟨6795710, by rfl⟩ : syracuseStep 9060947 = 13591421) B13591421
theorem B12084065 : Blo 1413526 12084065 := bstep (se 2 (by rfl) ⟨4531524, by rfl⟩ : syracuseStep 12084065 = 9063049) B9063049
theorem B2122703 : Blo 1413526 2122703 := bstep (se 1 (by rfl) ⟨1592027, by rfl⟩ : syracuseStep 2122703 = 3184055) B3184055
theorem B2122751 : Blo 1413526 2122751 := bstep (se 1 (by rfl) ⟨1592063, by rfl⟩ : syracuseStep 2122751 = 3184127) B3184127
theorem B20382749 : Blo 1413526 20382749 := bstep (se 3 (by rfl) ⟨3821765, by rfl⟩ : syracuseStep 20382749 = 7643531) B7643531
theorem B2122823 : Blo 1413526 2122823 := bstep (se 1 (by rfl) ⟨1592117, by rfl⟩ : syracuseStep 2122823 = 3184235) B3184235
theorem B4531423 : Blo 1413526 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B2123003 : Blo 1413526 2123003 := bstep (se 1 (by rfl) ⟨1592252, by rfl⟩ : syracuseStep 2123003 = 3184505) B3184505
theorem B23242139 : Blo 1413526 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B7644655 : Blo 1413526 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B16115273 : Blo 1413526 16115273 := bstep (se 2 (by rfl) ⟨6043227, by rfl⟩ : syracuseStep 16115273 = 12086455) B12086455
theorem B3581921 : Blo 1413526 3581921 := bstep (se 2 (by rfl) ⟨1343220, by rfl⟩ : syracuseStep 3581921 = 2686441) B2686441
theorem B77449223 : Blo 1413526 77449223 := bstep (se 1 (by rfl) ⟨58086917, by rfl⟩ : syracuseStep 77449223 = 116173835) B116173835
theorem B2386415 : Blo 1413526 2386415 := bstep (se 1 (by rfl) ⟨1789811, by rfl⟩ : syracuseStep 2386415 = 3579623) B3579623
theorem B3181049 : Blo 1413526 3181049 := bstep (se 2 (by rfl) ⟨1192893, by rfl⟩ : syracuseStep 3181049 = 2385787) B2385787
theorem B9808607 : Blo 1413526 9808607 := bstep (se 1 (by rfl) ⟨7356455, by rfl⟩ : syracuseStep 9808607 = 14712911) B14712911
theorem B22956803 : Blo 1413526 22956803 := bstep (se 1 (by rfl) ⟨17217602, by rfl⟩ : syracuseStep 22956803 = 34435205) B34435205
theorem B3181409 : Blo 1413526 3181409 := bstep (se 2 (by rfl) ⟨1193028, by rfl⟩ : syracuseStep 3181409 = 2386057) B2386057
theorem B5737321 : Blo 1413526 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B10202219 : Blo 1413526 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B4770953 : Blo 1413526 4770953 := bstep (se 2 (by rfl) ⟨1789107, by rfl⟩ : syracuseStep 4770953 = 3578215) B3578215
theorem B4771007 : Blo 1413526 4771007 := bstep (se 1 (by rfl) ⟨3578255, by rfl⟩ : syracuseStep 4771007 = 7156511) B7156511
theorem B6040939 : Blo 1413526 6040939 := bstep (se 1 (by rfl) ⟨4530704, by rfl⟩ : syracuseStep 6040939 = 9061409) B9061409
theorem B10202561 : Blo 1413526 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B3182327 : Blo 1413526 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B4771709 : Blo 1413526 4771709 := bstep (se 3 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 4771709 = 1789391) B1789391
theorem B2388143 : Blo 1413526 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B6885623 : Blo 1413526 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B5099897 : Blo 1413526 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B1413567 : Blo 1413526 1413567 := bstep (se 1 (by rfl) ⟨1060175, by rfl⟩ : syracuseStep 1413567 = 2120351) B2120351
theorem B3183047 : Blo 1413526 3183047 := bstep (se 1 (by rfl) ⟨2387285, by rfl⟩ : syracuseStep 3183047 = 4774571) B4774571
theorem B1413663 : Blo 1413526 1413663 := bstep (se 1 (by rfl) ⟨1060247, by rfl⟩ : syracuseStep 1413663 = 2120495) B2120495
theorem B1413723 : Blo 1413526 1413723 := bstep (se 1 (by rfl) ⟨1060292, by rfl⟩ : syracuseStep 1413723 = 2120585) B2120585
theorem B1413743 : Blo 1413526 1413743 := bstep (se 1 (by rfl) ⟨1060307, by rfl⟩ : syracuseStep 1413743 = 2120615) B2120615
theorem B1815151 : Blo 1413526 1815151 := bstep (se 1 (by rfl) ⟨1361363, by rfl⟩ : syracuseStep 1815151 = 2722727) B2722727
theorem B8057501 : Blo 1413526 8057501 := bstep (se 3 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 8057501 = 3021563) B3021563
theorem B1413863 : Blo 1413526 1413863 := bstep (se 1 (by rfl) ⟨1060397, by rfl⟩ : syracuseStep 1413863 = 2120795) B2120795
theorem B4027133 : Blo 1413526 4027133 := bstep (se 3 (by rfl) ⟨755087, by rfl⟩ : syracuseStep 4027133 = 1510175) B1510175
theorem B3183407 : Blo 1413526 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B1413991 : Blo 1413526 1413991 := bstep (se 1 (by rfl) ⟨1060493, by rfl⟩ : syracuseStep 1413991 = 2120987) B2120987
theorem B8057819 : Blo 1413526 8057819 := bstep (se 1 (by rfl) ⟨6043364, by rfl⟩ : syracuseStep 8057819 = 12086729) B12086729
theorem B3019769 : Blo 1413526 3019769 := bstep (se 2 (by rfl) ⟨1132413, by rfl⟩ : syracuseStep 3019769 = 2264827) B2264827
theorem B181343245 : Blo 1413526 181343245 := bstep (se 3 (by rfl) ⟨34001858, by rfl⟩ : syracuseStep 181343245 = 68003717) B68003717
theorem B1791067 : Blo 1413526 1791067 := bstep (se 1 (by rfl) ⟨1343300, by rfl⟩ : syracuseStep 1791067 = 2686601) B2686601
theorem B1414303 : Blo 1413526 1414303 := bstep (se 1 (by rfl) ⟨1060727, by rfl⟩ : syracuseStep 1414303 = 2121455) B2121455
theorem B3183785 : Blo 1413526 3183785 := bstep (se 2 (by rfl) ⟨1193919, by rfl⟩ : syracuseStep 3183785 = 2387839) B2387839
theorem B49009859 : Blo 1413526 49009859 := bstep (se 1 (by rfl) ⟨36757394, by rfl⟩ : syracuseStep 49009859 = 73514789) B73514789
theorem B4027657 : Blo 1413526 4027657 := bstep (se 2 (by rfl) ⟨1510371, by rfl⟩ : syracuseStep 4027657 = 3020743) B3020743
theorem B1414427 : Blo 1413526 1414427 := bstep (se 1 (by rfl) ⟨1060820, by rfl⟩ : syracuseStep 1414427 = 2121641) B2121641
theorem B1414527 : Blo 1413526 1414527 := bstep (se 1 (by rfl) ⟨1060895, by rfl⟩ : syracuseStep 1414527 = 2121791) B2121791
theorem B7157159 : Blo 1413526 7157159 := bstep (se 1 (by rfl) ⟨5367869, by rfl⟩ : syracuseStep 7157159 = 10735739) B10735739
theorem B21771767 : Blo 1413526 21771767 := bstep (se 1 (by rfl) ⟨16328825, by rfl⟩ : syracuseStep 21771767 = 32657651) B32657651
theorem B1791487 : Blo 1413526 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B1414683 : Blo 1413526 1414683 := bstep (se 1 (by rfl) ⟨1061012, by rfl⟩ : syracuseStep 1414683 = 2122025) B2122025
theorem B4773545 : Blo 1413526 4773545 := bstep (se 2 (by rfl) ⟨1790079, by rfl⟩ : syracuseStep 4773545 = 3580159) B3580159
theorem B1414863 : Blo 1413526 1414863 := bstep (se 1 (by rfl) ⟨1061147, by rfl⟩ : syracuseStep 1414863 = 2122295) B2122295
theorem B7755497 : Blo 1413526 7755497 := bstep (se 2 (by rfl) ⟨2908311, by rfl⟩ : syracuseStep 7755497 = 5816623) B5816623
theorem B8271713 : Blo 1413526 8271713 := bstep (se 2 (by rfl) ⟨3101892, by rfl⟩ : syracuseStep 8271713 = 6203785) B6203785
theorem B1415103 : Blo 1413526 1415103 := bstep (se 1 (by rfl) ⟨1061327, by rfl⟩ : syracuseStep 1415103 = 2122655) B2122655
theorem B1415295 : Blo 1413526 1415295 := bstep (se 1 (by rfl) ⟨1061471, by rfl⟩ : syracuseStep 1415295 = 2122943) B2122943
theorem B4028591 : Blo 1413526 4028591 := bstep (se 1 (by rfl) ⟨3021443, by rfl⟩ : syracuseStep 4028591 = 6042887) B6042887
theorem B1415391 : Blo 1413526 1415391 := bstep (se 1 (by rfl) ⟨1061543, by rfl⟩ : syracuseStep 1415391 = 2123087) B2123087
theorem B1415451 : Blo 1413526 1415451 := bstep (se 1 (by rfl) ⟨1061588, by rfl⟩ : syracuseStep 1415451 = 2123177) B2123177
theorem B18127223 : Blo 1413526 18127223 := bstep (se 1 (by rfl) ⟨13595417, by rfl⟩ : syracuseStep 18127223 = 27190835) B27190835
theorem B4774301 : Blo 1413526 4774301 := bstep (se 3 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 4774301 = 1790363) B1790363
theorem B8051237 : Blo 1413526 8051237 := bstep (se 4 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 8051237 = 1509607) B1509607
theorem B7158455 : Blo 1413526 7158455 := bstep (se 1 (by rfl) ⟨5368841, by rfl⟩ : syracuseStep 7158455 = 10737683) B10737683
theorem B10738655 : Blo 1413526 10738655 := bstep (se 1 (by rfl) ⟨8053991, by rfl⟩ : syracuseStep 10738655 = 16107983) B16107983
theorem B2120735 : Blo 1413526 2120735 := bstep (se 1 (by rfl) ⟨1590551, by rfl⟩ : syracuseStep 2120735 = 3181103) B3181103
theorem B65330225 : Blo 1413526 65330225 := bstep (se 2 (by rfl) ⟨24498834, by rfl⟩ : syracuseStep 65330225 = 48997669) B48997669
theorem B1432895 : Blo 1413526 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B24157601 : Blo 1413526 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B2121167 : Blo 1413526 2121167 := bstep (se 1 (by rfl) ⟨1590875, by rfl⟩ : syracuseStep 2121167 = 3181751) B3181751
theorem B4030175 : Blo 1413526 4030175 := bstep (se 1 (by rfl) ⟨3022631, by rfl⟩ : syracuseStep 4030175 = 6045263) B6045263
theorem B3399931 : Blo 1413526 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B6045947 : Blo 1413526 6045947 := bstep (se 1 (by rfl) ⟨4534460, by rfl⟩ : syracuseStep 6045947 = 9068921) B9068921
theorem B2122031 : Blo 1413526 2122031 := bstep (se 1 (by rfl) ⟨1591523, by rfl⟩ : syracuseStep 2122031 = 3183047) B3183047
theorem B12091787 : Blo 1413526 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B2122271 : Blo 1413526 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B2122523 : Blo 1413526 2122523 := bstep (se 1 (by rfl) ⟨1591892, by rfl⟩ : syracuseStep 2122523 = 3183785) B3183785
theorem B5170331 : Blo 1413526 5170331 := bstep (se 1 (by rfl) ⟨3877748, by rfl⟩ : syracuseStep 5170331 = 7755497) B7755497
theorem B5514475 : Blo 1413526 5514475 := bstep (se 1 (by rfl) ⟨4135856, by rfl⟩ : syracuseStep 5514475 = 8271713) B8271713
theorem B12084815 : Blo 1413526 12084815 := bstep (se 1 (by rfl) ⟨9063611, by rfl⟩ : syracuseStep 12084815 = 18127223) B18127223
theorem B1590943 : Blo 1413526 1590943 := bstep (se 1 (by rfl) ⟨1193207, by rfl⟩ : syracuseStep 1590943 = 2386415) B2386415
theorem B5367491 : Blo 1413526 5367491 := bstep (se 1 (by rfl) ⟨4025618, by rfl⟩ : syracuseStep 5367491 = 8051237) B8051237
theorem B8054585 : Blo 1413526 8054585 := bstep (se 2 (by rfl) ⟨3020469, by rfl⟩ : syracuseStep 8054585 = 6040939) B6040939
theorem B6539071 : Blo 1413526 6539071 := bstep (se 1 (by rfl) ⟨4904303, by rfl⟩ : syracuseStep 6539071 = 9808607) B9808607
theorem B15304535 : Blo 1413526 15304535 := bstep (se 1 (by rfl) ⟨11478401, by rfl⟩ : syracuseStep 15304535 = 22956803) B22956803
theorem B10192873 : Blo 1413526 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B6801479 : Blo 1413526 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B3180635 : Blo 1413526 3180635 := bstep (se 1 (by rfl) ⟨2385476, by rfl⟩ : syracuseStep 3180635 = 4770953) B4770953
theorem B3180671 : Blo 1413526 3180671 := bstep (se 1 (by rfl) ⟨2385503, by rfl⟩ : syracuseStep 3180671 = 4771007) B4771007
theorem B6801707 : Blo 1413526 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B3181139 : Blo 1413526 3181139 := bstep (se 1 (by rfl) ⟨2385854, by rfl⟩ : syracuseStep 3181139 = 4771709) B4771709
theorem B2386651 : Blo 1413526 2386651 := bstep (se 1 (by rfl) ⟨1789988, by rfl⟩ : syracuseStep 2386651 = 3579977) B3579977
theorem B1592095 : Blo 1413526 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B4590415 : Blo 1413526 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B40807475 : Blo 1413526 40807475 := bstep (se 1 (by rfl) ⟨30605606, by rfl⟩ : syracuseStep 40807475 = 61211213) B61211213
theorem B6040631 : Blo 1413526 6040631 := bstep (se 1 (by rfl) ⟨4530473, by rfl⟩ : syracuseStep 6040631 = 9060947) B9060947
theorem B8056043 : Blo 1413526 8056043 := bstep (se 1 (by rfl) ⟨6042032, by rfl⟩ : syracuseStep 8056043 = 12084065) B12084065
theorem B32673239 : Blo 1413526 32673239 := bstep (se 1 (by rfl) ⟨24504929, by rfl⟩ : syracuseStep 32673239 = 49009859) B49009859
theorem B2420201 : Blo 1413526 2420201 := bstep (se 2 (by rfl) ⟨907575, by rfl⟩ : syracuseStep 2420201 = 1815151) B1815151
theorem B15494759 : Blo 1413526 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B4771439 : Blo 1413526 4771439 := bstep (se 1 (by rfl) ⟨3578579, by rfl⟩ : syracuseStep 4771439 = 7157159) B7157159
theorem B10743515 : Blo 1413526 10743515 := bstep (se 1 (by rfl) ⟨8057636, by rfl⟩ : syracuseStep 10743515 = 16115273) B16115273
theorem B3182363 : Blo 1413526 3182363 := bstep (se 1 (by rfl) ⟨2386772, by rfl⟩ : syracuseStep 3182363 = 4773545) B4773545
theorem B2387947 : Blo 1413526 2387947 := bstep (se 1 (by rfl) ⟨1790960, by rfl⟩ : syracuseStep 2387947 = 3581921) B3581921
theorem B241790993 : Blo 1413526 241790993 := bstep (se 2 (by rfl) ⟨90671622, by rfl⟩ : syracuseStep 241790993 = 181343245) B181343245
theorem B2388089 : Blo 1413526 2388089 := bstep (se 2 (by rfl) ⟨895533, by rfl⟩ : syracuseStep 2388089 = 1791067) B1791067
theorem B3182867 : Blo 1413526 3182867 := bstep (se 1 (by rfl) ⟨2387150, by rfl⟩ : syracuseStep 3182867 = 4774301) B4774301
theorem B6041897 : Blo 1413526 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B5370209 : Blo 1413526 5370209 := bstep (se 2 (by rfl) ⟨2013828, by rfl⟩ : syracuseStep 5370209 = 4027657) B4027657
theorem B4772303 : Blo 1413526 4772303 := bstep (se 1 (by rfl) ⟨3579227, by rfl⟩ : syracuseStep 4772303 = 7158455) B7158455
theorem B2388649 : Blo 1413526 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B1413823 : Blo 1413526 1413823 := bstep (se 1 (by rfl) ⟨1060367, by rfl⟩ : syracuseStep 1413823 = 2120735) B2120735
theorem B43553483 : Blo 1413526 43553483 := bstep (se 1 (by rfl) ⟨32665112, by rfl⟩ : syracuseStep 43553483 = 65330225) B65330225
theorem B1414111 : Blo 1413526 1414111 := bstep (se 1 (by rfl) ⟨1060583, by rfl⟩ : syracuseStep 1414111 = 2121167) B2121167
theorem B3397231 : Blo 1413526 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B3184271 : Blo 1413526 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B4773599 : Blo 1413526 4773599 := bstep (se 1 (by rfl) ⟨3580199, by rfl⟩ : syracuseStep 4773599 = 7160399) B7160399
theorem B5371667 : Blo 1413526 5371667 := bstep (se 1 (by rfl) ⟨4028750, by rfl⟩ : syracuseStep 5371667 = 8057501) B8057501
theorem B2684755 : Blo 1413526 2684755 := bstep (se 1 (by rfl) ⟨2013566, by rfl⟩ : syracuseStep 2684755 = 4027133) B4027133
theorem B4773761 : Blo 1413526 4773761 := bstep (se 2 (by rfl) ⟨1790160, by rfl⟩ : syracuseStep 4773761 = 3580321) B3580321
theorem B1415135 : Blo 1413526 1415135 := bstep (se 1 (by rfl) ⟨1061351, by rfl⟩ : syracuseStep 1415135 = 2122703) B2122703
theorem B5371879 : Blo 1413526 5371879 := bstep (se 1 (by rfl) ⟨4028909, by rfl⟩ : syracuseStep 5371879 = 8057819) B8057819
theorem B15284213 : Blo 1413526 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B2013179 : Blo 1413526 2013179 := bstep (se 1 (by rfl) ⟨1509884, by rfl⟩ : syracuseStep 2013179 = 3019769) B3019769
theorem B1415167 : Blo 1413526 1415167 := bstep (se 1 (by rfl) ⟨1061375, by rfl⟩ : syracuseStep 1415167 = 2122751) B2122751
theorem B13588499 : Blo 1413526 13588499 := bstep (se 1 (by rfl) ⟨10191374, by rfl⟩ : syracuseStep 13588499 = 20382749) B20382749
theorem B1415215 : Blo 1413526 1415215 := bstep (se 1 (by rfl) ⟨1061411, by rfl⟩ : syracuseStep 1415215 = 2122823) B2122823
theorem B1415335 : Blo 1413526 1415335 := bstep (se 1 (by rfl) ⟨1061501, by rfl⟩ : syracuseStep 1415335 = 2123003) B2123003
theorem B14514511 : Blo 1413526 14514511 := bstep (se 1 (by rfl) ⟨10885883, by rfl⟩ : syracuseStep 14514511 = 21771767) B21771767
theorem B7649761 : Blo 1413526 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B51632815 : Blo 1413526 51632815 := bstep (se 1 (by rfl) ⟨38724611, by rfl⟩ : syracuseStep 51632815 = 77449223) B77449223
theorem B2685727 : Blo 1413526 2685727 := bstep (se 1 (by rfl) ⟨2014295, by rfl⟩ : syracuseStep 2685727 = 4028591) B4028591
theorem B2120699 : Blo 1413526 2120699 := bstep (se 1 (by rfl) ⟨1590524, by rfl⟩ : syracuseStep 2120699 = 3181049) B3181049
theorem B2120939 : Blo 1413526 2120939 := bstep (se 1 (by rfl) ⟨1590704, by rfl⟩ : syracuseStep 2120939 = 3181409) B3181409
theorem B7159103 : Blo 1413526 7159103 := bstep (se 1 (by rfl) ⟨5369327, by rfl⟩ : syracuseStep 7159103 = 10738655) B10738655
theorem B16105067 : Blo 1413526 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B2686783 : Blo 1413526 2686783 := bstep (se 1 (by rfl) ⟨2015087, by rfl⟩ : syracuseStep 2686783 = 4030175) B4030175
theorem B2121551 : Blo 1413526 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B161193995 : Blo 1413526 161193995 := bstep (se 1 (by rfl) ⟨120895496, by rfl⟩ : syracuseStep 161193995 = 241790993) B241790993
theorem B4030631 : Blo 1413526 4030631 := bstep (se 1 (by rfl) ⟨3022973, by rfl⟩ : syracuseStep 4030631 = 6045947) B6045947
theorem B2121911 : Blo 1413526 2121911 := bstep (se 1 (by rfl) ⟨1591433, by rfl⟩ : syracuseStep 2121911 = 3182867) B3182867
theorem B3580139 : Blo 1413526 3580139 := bstep (se 1 (by rfl) ⟨2685104, by rfl⟩ : syracuseStep 3580139 = 5370209) B5370209
theorem B8061191 : Blo 1413526 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B10199681 : Blo 1413526 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B3580969 : Blo 1413526 3580969 := bstep (se 2 (by rfl) ⟨1342863, by rfl⟩ : syracuseStep 3580969 = 2685727) B2685727
theorem B2122793 : Blo 1413526 2122793 := bstep (se 2 (by rfl) ⟨796047, by rfl⟩ : syracuseStep 2122793 = 1592095) B1592095
theorem B2122847 : Blo 1413526 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B3581111 : Blo 1413526 3581111 := bstep (se 1 (by rfl) ⟨2685833, by rfl⟩ : syracuseStep 3581111 = 5371667) B5371667
theorem B3180959 : Blo 1413526 3180959 := bstep (se 1 (by rfl) ⟨2385719, by rfl⟩ : syracuseStep 3180959 = 4771439) B4771439
theorem B8718761 : Blo 1413526 8718761 := bstep (se 2 (by rfl) ⟨3269535, by rfl⟩ : syracuseStep 8718761 = 6539071) B6539071
theorem B3582377 : Blo 1413526 3582377 := bstep (se 2 (by rfl) ⟨1343391, by rfl⟩ : syracuseStep 3582377 = 2686783) B2686783
theorem B7162343 : Blo 1413526 7162343 := bstep (se 1 (by rfl) ⟨5371757, by rfl⟩ : syracuseStep 7162343 = 10743515) B10743515
theorem B7162505 : Blo 1413526 7162505 := bstep (se 2 (by rfl) ⟨2685939, by rfl⟩ : syracuseStep 7162505 = 5371879) B5371879
theorem B5368477 : Blo 1413526 5368477 := bstep (se 3 (by rfl) ⟨1006589, by rfl⟩ : syracuseStep 5368477 = 2013179) B2013179
theorem B1592059 : Blo 1413526 1592059 := bstep (se 1 (by rfl) ⟨1194044, by rfl⟩ : syracuseStep 1592059 = 2388089) B2388089
theorem B3181535 : Blo 1413526 3181535 := bstep (se 1 (by rfl) ⟨2386151, by rfl⟩ : syracuseStep 3181535 = 4772303) B4772303
theorem B4533241 : Blo 1413526 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B19352681 : Blo 1413526 19352681 := bstep (se 2 (by rfl) ⟨7257255, by rfl⟩ : syracuseStep 19352681 = 14514511) B14514511
theorem B29035655 : Blo 1413526 29035655 := bstep (se 1 (by rfl) ⟨21776741, by rfl⟩ : syracuseStep 29035655 = 43553483) B43553483
theorem B3182201 : Blo 1413526 3182201 := bstep (se 2 (by rfl) ⟨1193325, by rfl⟩ : syracuseStep 3182201 = 2386651) B2386651
theorem B8056543 : Blo 1413526 8056543 := bstep (se 1 (by rfl) ⟨6042407, by rfl⟩ : syracuseStep 8056543 = 12084815) B12084815
theorem B3182399 : Blo 1413526 3182399 := bstep (se 1 (by rfl) ⟨2386799, by rfl⟩ : syracuseStep 3182399 = 4773599) B4773599
theorem B5369723 : Blo 1413526 5369723 := bstep (se 1 (by rfl) ⟨4027292, by rfl⟩ : syracuseStep 5369723 = 8054585) B8054585
theorem B10203023 : Blo 1413526 10203023 := bstep (se 1 (by rfl) ⟨7652267, by rfl⟩ : syracuseStep 10203023 = 15304535) B15304535
theorem B3182507 : Blo 1413526 3182507 := bstep (se 1 (by rfl) ⟨2386880, by rfl⟩ : syracuseStep 3182507 = 4773761) B4773761
theorem B4534319 : Blo 1413526 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B4534471 : Blo 1413526 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B7352633 : Blo 1413526 7352633 := bstep (se 2 (by rfl) ⟨2757237, by rfl⟩ : syracuseStep 7352633 = 5514475) B5514475
theorem B24482213 : Blo 1413526 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B1413799 : Blo 1413526 1413799 := bstep (se 1 (by rfl) ⟨1060349, by rfl⟩ : syracuseStep 1413799 = 2120699) B2120699
theorem B4027087 : Blo 1413526 4027087 := bstep (se 1 (by rfl) ⟨3020315, by rfl⟩ : syracuseStep 4027087 = 6040631) B6040631
theorem B1413959 : Blo 1413526 1413959 := bstep (se 1 (by rfl) ⟨1060469, by rfl⟩ : syracuseStep 1413959 = 2120939) B2120939
theorem B5370695 : Blo 1413526 5370695 := bstep (se 1 (by rfl) ⟨4028021, by rfl⟩ : syracuseStep 5370695 = 8056043) B8056043
theorem B4772735 : Blo 1413526 4772735 := bstep (se 1 (by rfl) ⟨3579551, by rfl⟩ : syracuseStep 4772735 = 7159103) B7159103
theorem B10736711 : Blo 1413526 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B1414367 : Blo 1413526 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B3183929 : Blo 1413526 3183929 := bstep (se 2 (by rfl) ⟨1193973, by rfl⟩ : syracuseStep 3183929 = 2387947) B2387947
theorem B4027931 : Blo 1413526 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B1414687 : Blo 1413526 1414687 := bstep (se 1 (by rfl) ⟨1061015, by rfl⟩ : syracuseStep 1414687 = 2122031) B2122031
theorem B1414847 : Blo 1413526 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B1415015 : Blo 1413526 1415015 := bstep (se 1 (by rfl) ⟨1061261, by rfl⟩ : syracuseStep 1415015 = 2122523) B2122523
theorem B18118565 : Blo 1413526 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B3446887 : Blo 1413526 3446887 := bstep (se 1 (by rfl) ⟨2585165, by rfl⟩ : syracuseStep 3446887 = 5170331) B5170331
theorem B3184865 : Blo 1413526 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B68843753 : Blo 1413526 68843753 := bstep (se 2 (by rfl) ⟨25816407, by rfl⟩ : syracuseStep 68843753 = 51632815) B51632815
theorem B3578327 : Blo 1413526 3578327 := bstep (se 1 (by rfl) ⟨2683745, by rfl⟩ : syracuseStep 3578327 = 5367491) B5367491
theorem B10189475 : Blo 1413526 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B9058999 : Blo 1413526 9058999 := bstep (se 1 (by rfl) ⟨6794249, by rfl⟩ : syracuseStep 9058999 = 13588499) B13588499
theorem B2120423 : Blo 1413526 2120423 := bstep (se 1 (by rfl) ⟨1590317, by rfl⟩ : syracuseStep 2120423 = 3180635) B3180635
theorem B2120447 : Blo 1413526 2120447 := bstep (se 1 (by rfl) ⟨1590335, by rfl⟩ : syracuseStep 2120447 = 3180671) B3180671
theorem B2120759 : Blo 1413526 2120759 := bstep (se 1 (by rfl) ⟨1590569, by rfl⟩ : syracuseStep 2120759 = 3181139) B3181139
theorem B27204983 : Blo 1413526 27204983 := bstep (se 1 (by rfl) ⟨20403737, by rfl⟩ : syracuseStep 27204983 = 40807475) B40807475
theorem B2121257 : Blo 1413526 2121257 := bstep (se 2 (by rfl) ⟨795471, by rfl⟩ : syracuseStep 2121257 = 1590943) B1590943
theorem B21782159 : Blo 1413526 21782159 := bstep (se 1 (by rfl) ⟨16336619, by rfl⟩ : syracuseStep 21782159 = 32673239) B32673239
theorem B1613467 : Blo 1413526 1613467 := bstep (se 1 (by rfl) ⟨1210100, by rfl⟩ : syracuseStep 1613467 = 2420201) B2420201
theorem B10329839 : Blo 1413526 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B3579673 : Blo 1413526 3579673 := bstep (se 2 (by rfl) ⟨1342377, by rfl⟩ : syracuseStep 3579673 = 2684755) B2684755
theorem B2121575 : Blo 1413526 2121575 := bstep (se 1 (by rfl) ⟨1591181, by rfl⟩ : syracuseStep 2121575 = 3182363) B3182363
theorem B13590497 : Blo 1413526 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B107462663 : Blo 1413526 107462663 := bstep (se 1 (by rfl) ⟨80596997, by rfl⟩ : syracuseStep 107462663 = 161193995) B161193995
theorem B3022879 : Blo 1413526 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2687087 : Blo 1413526 2687087 := bstep (se 1 (by rfl) ⟨2015315, by rfl⟩ : syracuseStep 2687087 = 4030631) B4030631
theorem B4595849 : Blo 1413526 4595849 := bstep (se 2 (by rfl) ⟨1723443, by rfl⟩ : syracuseStep 4595849 = 3446887) B3446887
theorem B5374127 : Blo 1413526 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B6799787 : Blo 1413526 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B3580463 : Blo 1413526 3580463 := bstep (se 1 (by rfl) ⟨2685347, by rfl⟩ : syracuseStep 3580463 = 5370695) B5370695
theorem B2122619 : Blo 1413526 2122619 := bstep (se 1 (by rfl) ⟨1591964, by rfl⟩ : syracuseStep 2122619 = 3183929) B3183929
theorem B2122745 : Blo 1413526 2122745 := bstep (se 2 (by rfl) ⟨796029, by rfl⟩ : syracuseStep 2122745 = 1592059) B1592059
theorem B24183845 : Blo 1413526 24183845 := bstep (se 4 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 24183845 = 4534471) B4534471
theorem B2123243 : Blo 1413526 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B2385551 : Blo 1413526 2385551 := bstep (se 1 (by rfl) ⟨1789163, by rfl⟩ : syracuseStep 2385551 = 3578327) B3578327
theorem B6792983 : Blo 1413526 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B10742057 : Blo 1413526 10742057 := bstep (se 2 (by rfl) ⟨4028271, by rfl⟩ : syracuseStep 10742057 = 8056543) B8056543
theorem B6802015 : Blo 1413526 6802015 := bstep (se 1 (by rfl) ⟨5101511, by rfl⟩ : syracuseStep 6802015 = 10203023) B10203023
theorem B2386759 : Blo 1413526 2386759 := bstep (se 1 (by rfl) ⟨1790069, by rfl⟩ : syracuseStep 2386759 = 3580139) B3580139
theorem B4901755 : Blo 1413526 4901755 := bstep (se 1 (by rfl) ⟨3676316, by rfl⟩ : syracuseStep 4901755 = 7352633) B7352633
theorem B16321475 : Blo 1413526 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B3181823 : Blo 1413526 3181823 := bstep (se 1 (by rfl) ⟨2386367, by rfl⟩ : syracuseStep 3181823 = 4772735) B4772735
theorem B2387407 : Blo 1413526 2387407 := bstep (se 1 (by rfl) ⟨1790555, by rfl⟩ : syracuseStep 2387407 = 3581111) B3581111
theorem B12078665 : Blo 1413526 12078665 := bstep (se 2 (by rfl) ⟨4529499, by rfl⟩ : syracuseStep 12078665 = 9058999) B9058999
theorem B5369449 : Blo 1413526 5369449 := bstep (se 2 (by rfl) ⟨2013543, by rfl⟩ : syracuseStep 5369449 = 4027087) B4027087
theorem B12079043 : Blo 1413526 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B45895835 : Blo 1413526 45895835 := bstep (se 1 (by rfl) ⟨34421876, by rfl⟩ : syracuseStep 45895835 = 68843753) B68843753
theorem B5812507 : Blo 1413526 5812507 := bstep (se 1 (by rfl) ⟨4359380, by rfl⟩ : syracuseStep 5812507 = 8718761) B8718761
theorem B2388251 : Blo 1413526 2388251 := bstep (se 1 (by rfl) ⟨1791188, by rfl⟩ : syracuseStep 2388251 = 3582377) B3582377
theorem B1413615 : Blo 1413526 1413615 := bstep (se 1 (by rfl) ⟨1060211, by rfl⟩ : syracuseStep 1413615 = 2120423) B2120423
theorem B1413631 : Blo 1413526 1413631 := bstep (se 1 (by rfl) ⟨1060223, by rfl⟩ : syracuseStep 1413631 = 2120447) B2120447
theorem B1413839 : Blo 1413526 1413839 := bstep (se 1 (by rfl) ⟨1060379, by rfl⟩ : syracuseStep 1413839 = 2120759) B2120759
theorem B2151289 : Blo 1413526 2151289 := bstep (se 2 (by rfl) ⟨806733, by rfl⟩ : syracuseStep 2151289 = 1613467) B1613467
theorem B1414171 : Blo 1413526 1414171 := bstep (se 1 (by rfl) ⟨1060628, by rfl⟩ : syracuseStep 1414171 = 2121257) B2121257
theorem B4772897 : Blo 1413526 4772897 := bstep (se 2 (by rfl) ⟨1789836, by rfl⟩ : syracuseStep 4772897 = 3579673) B3579673
theorem B14521439 : Blo 1413526 14521439 := bstep (se 1 (by rfl) ⟨10891079, by rfl⟩ : syracuseStep 14521439 = 21782159) B21782159
theorem B6886559 : Blo 1413526 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B1414383 : Blo 1413526 1414383 := bstep (se 1 (by rfl) ⟨1060787, by rfl⟩ : syracuseStep 1414383 = 2121575) B2121575
theorem B1414607 : Blo 1413526 1414607 := bstep (se 1 (by rfl) ⟨1060955, by rfl⟩ : syracuseStep 1414607 = 2121911) B2121911
theorem B1415195 : Blo 1413526 1415195 := bstep (se 1 (by rfl) ⟨1061396, by rfl⟩ : syracuseStep 1415195 = 2122793) B2122793
theorem B7157807 : Blo 1413526 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B1415231 : Blo 1413526 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B7157969 : Blo 1413526 7157969 := bstep (se 2 (by rfl) ⟨2684238, by rfl⟩ : syracuseStep 7157969 = 5368477) B5368477
theorem B2685287 : Blo 1413526 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B6044321 : Blo 1413526 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B4774625 : Blo 1413526 4774625 := bstep (se 2 (by rfl) ⟨1790484, by rfl⟩ : syracuseStep 4774625 = 3580969) B3580969
theorem B2120639 : Blo 1413526 2120639 := bstep (se 1 (by rfl) ⟨1590479, by rfl⟩ : syracuseStep 2120639 = 3180959) B3180959
theorem B4774895 : Blo 1413526 4774895 := bstep (se 1 (by rfl) ⟨3581171, by rfl⟩ : syracuseStep 4774895 = 7162343) B7162343
theorem B4775003 : Blo 1413526 4775003 := bstep (se 1 (by rfl) ⟨3581252, by rfl⟩ : syracuseStep 4775003 = 7162505) B7162505
theorem B2121023 : Blo 1413526 2121023 := bstep (se 1 (by rfl) ⟨1590767, by rfl⟩ : syracuseStep 2121023 = 3181535) B3181535
theorem B12901787 : Blo 1413526 12901787 := bstep (se 1 (by rfl) ⟨9676340, by rfl⟩ : syracuseStep 12901787 = 19352681) B19352681
theorem B19357103 : Blo 1413526 19357103 := bstep (se 1 (by rfl) ⟨14517827, by rfl⟩ : syracuseStep 19357103 = 29035655) B29035655
theorem B18136655 : Blo 1413526 18136655 := bstep (se 1 (by rfl) ⟨13602491, by rfl⟩ : syracuseStep 18136655 = 27204983) B27204983
theorem B2121467 : Blo 1413526 2121467 := bstep (se 1 (by rfl) ⟨1591100, by rfl⟩ : syracuseStep 2121467 = 3182201) B3182201
theorem B2121599 : Blo 1413526 2121599 := bstep (se 1 (by rfl) ⟨1591199, by rfl⟩ : syracuseStep 2121599 = 3182399) B3182399
theorem B3579815 : Blo 1413526 3579815 := bstep (se 1 (by rfl) ⟨2684861, by rfl⟩ : syracuseStep 3579815 = 5369723) B5369723
theorem B2121671 : Blo 1413526 2121671 := bstep (se 1 (by rfl) ⟨1591253, by rfl⟩ : syracuseStep 2121671 = 3182507) B3182507
theorem B9060331 : Blo 1413526 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B4030505 : Blo 1413526 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B3063899 : Blo 1413526 3063899 := bstep (se 1 (by rfl) ⟨2297924, by rfl⟩ : syracuseStep 3063899 = 4595849) B4595849
theorem B30597223 : Blo 1413526 30597223 := bstep (se 1 (by rfl) ⟨22947917, by rfl⟩ : syracuseStep 30597223 = 45895835) B45895835
theorem B7750009 : Blo 1413526 7750009 := bstep (se 2 (by rfl) ⟨2906253, by rfl⟩ : syracuseStep 7750009 = 5812507) B5812507
theorem B16122563 : Blo 1413526 16122563 := bstep (se 1 (by rfl) ⟨12091922, by rfl⟩ : syracuseStep 16122563 = 24183845) B24183845
theorem B9069353 : Blo 1413526 9069353 := bstep (se 2 (by rfl) ⟨3401007, by rfl⟩ : syracuseStep 9069353 = 6802015) B6802015
theorem B1590367 : Blo 1413526 1590367 := bstep (se 1 (by rfl) ⟨1192775, by rfl⟩ : syracuseStep 1590367 = 2385551) B2385551
theorem B51618941 : Blo 1413526 51618941 := bstep (se 3 (by rfl) ⟨9678551, by rfl⟩ : syracuseStep 51618941 = 19357103) B19357103
theorem B2868385 : Blo 1413526 2868385 := bstep (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) B2151289
theorem B7161371 : Blo 1413526 7161371 := bstep (se 1 (by rfl) ⟨5371028, by rfl⟩ : syracuseStep 7161371 = 10742057) B10742057
theorem B10880983 : Blo 1413526 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B2386543 : Blo 1413526 2386543 := bstep (se 1 (by rfl) ⟨1789907, by rfl⟩ : syracuseStep 2386543 = 3579815) B3579815
theorem B71641775 : Blo 1413526 71641775 := bstep (se 1 (by rfl) ⟨53731331, by rfl⟩ : syracuseStep 71641775 = 107462663) B107462663
theorem B3582751 : Blo 1413526 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B1592167 : Blo 1413526 1592167 := bstep (se 1 (by rfl) ⟨1194125, by rfl⟩ : syracuseStep 1592167 = 2388251) B2388251
theorem B4533191 : Blo 1413526 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B2386975 : Blo 1413526 2386975 := bstep (se 1 (by rfl) ⟨1790231, by rfl⟩ : syracuseStep 2386975 = 3580463) B3580463
theorem B3181931 : Blo 1413526 3181931 := bstep (se 1 (by rfl) ⟨2386448, by rfl⟩ : syracuseStep 3181931 = 4772897) B4772897
theorem B3182345 : Blo 1413526 3182345 := bstep (se 2 (by rfl) ⟨1193379, by rfl⟩ : syracuseStep 3182345 = 2386759) B2386759
theorem B4771871 : Blo 1413526 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B4771979 : Blo 1413526 4771979 := bstep (se 1 (by rfl) ⟨3578984, by rfl⟩ : syracuseStep 4771979 = 7157969) B7157969
theorem B1790191 : Blo 1413526 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B16118189 : Blo 1413526 16118189 := bstep (se 3 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 16118189 = 6044321) B6044321
theorem B3183083 : Blo 1413526 3183083 := bstep (se 1 (by rfl) ⟨2387312, by rfl⟩ : syracuseStep 3183083 = 4774625) B4774625
theorem B3183209 : Blo 1413526 3183209 := bstep (se 2 (by rfl) ⟨1193703, by rfl⟩ : syracuseStep 3183209 = 2387407) B2387407
theorem B1413759 : Blo 1413526 1413759 := bstep (se 1 (by rfl) ⟨1060319, by rfl⟩ : syracuseStep 1413759 = 2120639) B2120639
theorem B3183263 : Blo 1413526 3183263 := bstep (se 1 (by rfl) ⟨2387447, by rfl⟩ : syracuseStep 3183263 = 4774895) B4774895
theorem B3183335 : Blo 1413526 3183335 := bstep (se 1 (by rfl) ⟨2387501, by rfl⟩ : syracuseStep 3183335 = 4775003) B4775003
theorem B1414015 : Blo 1413526 1414015 := bstep (se 1 (by rfl) ⟨1060511, by rfl⟩ : syracuseStep 1414015 = 2121023) B2121023
theorem B1414311 : Blo 1413526 1414311 := bstep (se 1 (by rfl) ⟨1060733, by rfl⟩ : syracuseStep 1414311 = 2121467) B2121467
theorem B1414399 : Blo 1413526 1414399 := bstep (se 1 (by rfl) ⟨1060799, by rfl⟩ : syracuseStep 1414399 = 2121599) B2121599
theorem B1414447 : Blo 1413526 1414447 := bstep (se 1 (by rfl) ⟨1060835, by rfl⟩ : syracuseStep 1414447 = 2121671) B2121671
theorem B12080441 : Blo 1413526 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B1791391 : Blo 1413526 1791391 := bstep (se 1 (by rfl) ⟨1343543, by rfl⟩ : syracuseStep 1791391 = 2687087) B2687087
theorem B18364157 : Blo 1413526 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B1415079 : Blo 1413526 1415079 := bstep (se 1 (by rfl) ⟨1061309, by rfl⟩ : syracuseStep 1415079 = 2122619) B2122619
theorem B1415163 : Blo 1413526 1415163 := bstep (se 1 (by rfl) ⟨1061372, by rfl⟩ : syracuseStep 1415163 = 2122745) B2122745
theorem B9680959 : Blo 1413526 9680959 := bstep (se 1 (by rfl) ⟨7260719, by rfl⟩ : syracuseStep 9680959 = 14521439) B14521439
theorem B1415495 : Blo 1413526 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B6535673 : Blo 1413526 6535673 := bstep (se 2 (by rfl) ⟨2450877, by rfl⟩ : syracuseStep 6535673 = 4901755) B4901755
theorem B4528655 : Blo 1413526 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B7159265 : Blo 1413526 7159265 := bstep (se 2 (by rfl) ⟨2684724, by rfl⟩ : syracuseStep 7159265 = 5369449) B5369449
theorem B2121215 : Blo 1413526 2121215 := bstep (se 1 (by rfl) ⟨1590911, by rfl⟩ : syracuseStep 2121215 = 3181823) B3181823
theorem B8601191 : Blo 1413526 8601191 := bstep (se 1 (by rfl) ⟨6450893, by rfl⟩ : syracuseStep 8601191 = 12901787) B12901787
theorem B8052443 : Blo 1413526 8052443 := bstep (se 1 (by rfl) ⟨6039332, by rfl⟩ : syracuseStep 8052443 = 12078665) B12078665
theorem B12091103 : Blo 1413526 12091103 := bstep (se 1 (by rfl) ⟨9068327, by rfl⟩ : syracuseStep 12091103 = 18136655) B18136655
theorem B8052695 : Blo 1413526 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B2687003 : Blo 1413526 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B40796297 : Blo 1413526 40796297 := bstep (se 2 (by rfl) ⟨15298611, by rfl⟩ : syracuseStep 40796297 = 30597223) B30597223
theorem B2122055 : Blo 1413526 2122055 := bstep (se 1 (by rfl) ⟨1591541, by rfl⟩ : syracuseStep 2122055 = 3183083) B3183083
theorem B2122139 : Blo 1413526 2122139 := bstep (se 1 (by rfl) ⟨1591604, by rfl⟩ : syracuseStep 2122139 = 3183209) B3183209
theorem B2122175 : Blo 1413526 2122175 := bstep (se 1 (by rfl) ⟨1591631, by rfl⟩ : syracuseStep 2122175 = 3183263) B3183263
theorem B10748375 : Blo 1413526 10748375 := bstep (se 1 (by rfl) ⟨8061281, by rfl⟩ : syracuseStep 10748375 = 16122563) B16122563
theorem B2122223 : Blo 1413526 2122223 := bstep (se 1 (by rfl) ⟨1591667, by rfl⟩ : syracuseStep 2122223 = 3183335) B3183335
theorem B6046235 : Blo 1413526 6046235 := bstep (se 1 (by rfl) ⟨4534676, by rfl⟩ : syracuseStep 6046235 = 9069353) B9069353
theorem B8053627 : Blo 1413526 8053627 := bstep (se 1 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 8053627 = 12080441) B12080441
theorem B4777001 : Blo 1413526 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B2122889 : Blo 1413526 2122889 := bstep (se 2 (by rfl) ⟨796083, by rfl⟩ : syracuseStep 2122889 = 1592167) B1592167
theorem B47761183 : Blo 1413526 47761183 := bstep (se 1 (by rfl) ⟨35820887, by rfl⟩ : syracuseStep 47761183 = 71641775) B71641775
theorem B5368295 : Blo 1413526 5368295 := bstep (se 1 (by rfl) ⟨4026221, by rfl⟩ : syracuseStep 5368295 = 8052443) B8052443
theorem B5368463 : Blo 1413526 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B3181247 : Blo 1413526 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B2042599 : Blo 1413526 2042599 := bstep (se 1 (by rfl) ⟨1531949, by rfl⟩ : syracuseStep 2042599 = 3063899) B3063899
theorem B3181319 : Blo 1413526 3181319 := bstep (se 1 (by rfl) ⟨2385989, by rfl⟩ : syracuseStep 3181319 = 4771979) B4771979
theorem B2386921 : Blo 1413526 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B10333345 : Blo 1413526 10333345 := bstep (se 2 (by rfl) ⟨3875004, by rfl⟩ : syracuseStep 10333345 = 7750009) B7750009
theorem B3182057 : Blo 1413526 3182057 := bstep (se 2 (by rfl) ⟨1193271, by rfl⟩ : syracuseStep 3182057 = 2386543) B2386543
theorem B12242771 : Blo 1413526 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B3182633 : Blo 1413526 3182633 := bstep (se 2 (by rfl) ⟨1193487, by rfl⟩ : syracuseStep 3182633 = 2386975) B2386975
theorem B3019103 : Blo 1413526 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B2388521 : Blo 1413526 2388521 := bstep (se 2 (by rfl) ⟨895695, by rfl⟩ : syracuseStep 2388521 = 1791391) B1791391
theorem B4772843 : Blo 1413526 4772843 := bstep (se 1 (by rfl) ⟨3579632, by rfl⟩ : syracuseStep 4772843 = 7159265) B7159265
theorem B1414143 : Blo 1413526 1414143 := bstep (se 1 (by rfl) ⟨1060607, by rfl⟩ : syracuseStep 1414143 = 2121215) B2121215
theorem B12907945 : Blo 1413526 12907945 := bstep (se 2 (by rfl) ⟨4840479, by rfl⟩ : syracuseStep 12907945 = 9680959) B9680959
theorem B10745459 : Blo 1413526 10745459 := bstep (se 1 (by rfl) ⟨8059094, by rfl⟩ : syracuseStep 10745459 = 16118189) B16118189
theorem B34412627 : Blo 1413526 34412627 := bstep (se 1 (by rfl) ⟨25809470, by rfl⟩ : syracuseStep 34412627 = 51618941) B51618941
theorem B4774247 : Blo 1413526 4774247 := bstep (se 1 (by rfl) ⟨3580685, by rfl⟩ : syracuseStep 4774247 = 7161371) B7161371
theorem B2120489 : Blo 1413526 2120489 := bstep (se 2 (by rfl) ⟨795183, by rfl⟩ : syracuseStep 2120489 = 1590367) B1590367
theorem B3824513 : Blo 1413526 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B4357115 : Blo 1413526 4357115 := bstep (se 1 (by rfl) ⟨3267836, by rfl⟩ : syracuseStep 4357115 = 6535673) B6535673
theorem B3022127 : Blo 1413526 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2121287 : Blo 1413526 2121287 := bstep (se 1 (by rfl) ⟨1590965, by rfl⟩ : syracuseStep 2121287 = 3181931) B3181931
theorem B5734127 : Blo 1413526 5734127 := bstep (se 1 (by rfl) ⟨4300595, by rfl⟩ : syracuseStep 5734127 = 8601191) B8601191
theorem B58031909 : Blo 1413526 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B8060735 : Blo 1413526 8060735 := bstep (se 1 (by rfl) ⟨6045551, by rfl⟩ : syracuseStep 8060735 = 12091103) B12091103
theorem B2121563 : Blo 1413526 2121563 := bstep (se 1 (by rfl) ⟨1591172, by rfl⟩ : syracuseStep 2121563 = 3182345) B3182345
theorem B2121755 : Blo 1413526 2121755 := bstep (se 1 (by rfl) ⟨1591316, by rfl⟩ : syracuseStep 2121755 = 3182633) B3182633
theorem B27197531 : Blo 1413526 27197531 := bstep (se 1 (by rfl) ⟨20398148, by rfl⟩ : syracuseStep 27197531 = 40796297) B40796297
theorem B4030823 : Blo 1413526 4030823 := bstep (se 1 (by rfl) ⟨3023117, by rfl⟩ : syracuseStep 4030823 = 6046235) B6046235
theorem B2549675 : Blo 1413526 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B8161847 : Blo 1413526 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B1592347 : Blo 1413526 1592347 := bstep (se 1 (by rfl) ⟨1194260, by rfl⟩ : syracuseStep 1592347 = 2388521) B2388521
theorem B3181895 : Blo 1413526 3181895 := bstep (se 1 (by rfl) ⟨2386421, by rfl⟩ : syracuseStep 3181895 = 4772843) B4772843
theorem B2723465 : Blo 1413526 2723465 := bstep (se 2 (by rfl) ⟨1021299, by rfl⟩ : syracuseStep 2723465 = 2042599) B2042599
theorem B7163639 : Blo 1413526 7163639 := bstep (se 1 (by rfl) ⟨5372729, by rfl⟩ : syracuseStep 7163639 = 10745459) B10745459
theorem B3182561 : Blo 1413526 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B22941751 : Blo 1413526 22941751 := bstep (se 1 (by rfl) ⟨17206313, by rfl⟩ : syracuseStep 22941751 = 34412627) B34412627
theorem B254726309 : Blo 1413526 254726309 := bstep (se 4 (by rfl) ⟨23880591, by rfl⟩ : syracuseStep 254726309 = 47761183) B47761183
theorem B3182831 : Blo 1413526 3182831 := bstep (se 1 (by rfl) ⟨2387123, by rfl⟩ : syracuseStep 3182831 = 4774247) B4774247
theorem B1413659 : Blo 1413526 1413659 := bstep (se 1 (by rfl) ⟨1060244, by rfl⟩ : syracuseStep 1413659 = 2120489) B2120489
theorem B2904743 : Blo 1413526 2904743 := bstep (se 1 (by rfl) ⟨2178557, by rfl⟩ : syracuseStep 2904743 = 4357115) B4357115
theorem B1414191 : Blo 1413526 1414191 := bstep (se 1 (by rfl) ⟨1060643, by rfl⟩ : syracuseStep 1414191 = 2121287) B2121287
theorem B3822751 : Blo 1413526 3822751 := bstep (se 1 (by rfl) ⟨2867063, by rfl⟩ : syracuseStep 3822751 = 5734127) B5734127
theorem B38687939 : Blo 1413526 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B1414375 : Blo 1413526 1414375 := bstep (se 1 (by rfl) ⟨1060781, by rfl⟩ : syracuseStep 1414375 = 2121563) B2121563
theorem B1791335 : Blo 1413526 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B1414703 : Blo 1413526 1414703 := bstep (se 1 (by rfl) ⟨1061027, by rfl⟩ : syracuseStep 1414703 = 2122055) B2122055
theorem B2012735 : Blo 1413526 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B1414759 : Blo 1413526 1414759 := bstep (se 1 (by rfl) ⟨1061069, by rfl⟩ : syracuseStep 1414759 = 2122139) B2122139
theorem B1414783 : Blo 1413526 1414783 := bstep (se 1 (by rfl) ⟨1061087, by rfl⟩ : syracuseStep 1414783 = 2122175) B2122175
theorem B7165583 : Blo 1413526 7165583 := bstep (se 1 (by rfl) ⟨5374187, by rfl⟩ : syracuseStep 7165583 = 10748375) B10748375
theorem B1414815 : Blo 1413526 1414815 := bstep (se 1 (by rfl) ⟨1061111, by rfl⟩ : syracuseStep 1414815 = 2122223) B2122223
theorem B3184667 : Blo 1413526 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B1415259 : Blo 1413526 1415259 := bstep (se 1 (by rfl) ⟨1061444, by rfl⟩ : syracuseStep 1415259 = 2122889) B2122889
theorem B10738169 : Blo 1413526 10738169 := bstep (se 2 (by rfl) ⟨4026813, by rfl⟩ : syracuseStep 10738169 = 8053627) B8053627
theorem B13777793 : Blo 1413526 13777793 := bstep (se 2 (by rfl) ⟨5166672, by rfl⟩ : syracuseStep 13777793 = 10333345) B10333345
theorem B3578863 : Blo 1413526 3578863 := bstep (se 1 (by rfl) ⟨2684147, by rfl⟩ : syracuseStep 3578863 = 5368295) B5368295
theorem B3578975 : Blo 1413526 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B2120831 : Blo 1413526 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B2120879 : Blo 1413526 2120879 := bstep (se 1 (by rfl) ⟨1590659, by rfl⟩ : syracuseStep 2120879 = 3181319) B3181319
theorem B17210593 : Blo 1413526 17210593 := bstep (se 2 (by rfl) ⟨6453972, by rfl⟩ : syracuseStep 17210593 = 12907945) B12907945
theorem B2014751 : Blo 1413526 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B2121371 : Blo 1413526 2121371 := bstep (se 1 (by rfl) ⟨1591028, by rfl⟩ : syracuseStep 2121371 = 3182057) B3182057
theorem B5373823 : Blo 1413526 5373823 := bstep (se 1 (by rfl) ⟨4030367, by rfl⟩ : syracuseStep 5373823 = 8060735) B8060735
theorem B30589001 : Blo 1413526 30589001 := bstep (se 2 (by rfl) ⟨11470875, by rfl⟩ : syracuseStep 30589001 = 22941751) B22941751
theorem B2121887 : Blo 1413526 2121887 := bstep (se 1 (by rfl) ⟨1591415, by rfl⟩ : syracuseStep 2121887 = 3182831) B3182831
theorem B4776893 : Blo 1413526 4776893 := bstep (se 3 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 4776893 = 1791335) B1791335
theorem B10748861 : Blo 1413526 10748861 := bstep (se 3 (by rfl) ⟨2015411, by rfl⟩ : syracuseStep 10748861 = 4030823) B4030823
theorem B4777055 : Blo 1413526 4777055 := bstep (se 1 (by rfl) ⟨3582791, by rfl⟩ : syracuseStep 4777055 = 7165583) B7165583
theorem B2123111 : Blo 1413526 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B2123129 : Blo 1413526 2123129 := bstep (se 2 (by rfl) ⟨796173, by rfl⟩ : syracuseStep 2123129 = 1592347) B1592347
theorem B5367293 : Blo 1413526 5367293 := bstep (se 3 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 5367293 = 2012735) B2012735
theorem B5097001 : Blo 1413526 5097001 := bstep (se 2 (by rfl) ⟨1911375, by rfl⟩ : syracuseStep 5097001 = 3822751) B3822751
theorem B22947457 : Blo 1413526 22947457 := bstep (se 2 (by rfl) ⟨8605296, by rfl⟩ : syracuseStep 22947457 = 17210593) B17210593
theorem B5441231 : Blo 1413526 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B9185195 : Blo 1413526 9185195 := bstep (se 1 (by rfl) ⟨6888896, by rfl⟩ : syracuseStep 9185195 = 13777793) B13777793
theorem B2385983 : Blo 1413526 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B18131687 : Blo 1413526 18131687 := bstep (se 1 (by rfl) ⟨13598765, by rfl⟩ : syracuseStep 18131687 = 27197531) B27197531
theorem B1936495 : Blo 1413526 1936495 := bstep (se 1 (by rfl) ⟨1452371, by rfl⟩ : syracuseStep 1936495 = 2904743) B2904743
theorem B25791959 : Blo 1413526 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B4771817 : Blo 1413526 4771817 := bstep (se 2 (by rfl) ⟨1789431, by rfl⟩ : syracuseStep 4771817 = 3578863) B3578863
theorem B1413887 : Blo 1413526 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B1413919 : Blo 1413526 1413919 := bstep (se 1 (by rfl) ⟨1060439, by rfl⟩ : syracuseStep 1413919 = 2120879) B2120879
theorem B1815643 : Blo 1413526 1815643 := bstep (se 1 (by rfl) ⟨1361732, by rfl⟩ : syracuseStep 1815643 = 2723465) B2723465
theorem B1414247 : Blo 1413526 1414247 := bstep (se 1 (by rfl) ⟨1060685, by rfl⟩ : syracuseStep 1414247 = 2121371) B2121371
theorem B7165097 : Blo 1413526 7165097 := bstep (se 2 (by rfl) ⟨2686911, by rfl⟩ : syracuseStep 7165097 = 5373823) B5373823
theorem B1414503 : Blo 1413526 1414503 := bstep (se 1 (by rfl) ⟨1060877, by rfl⟩ : syracuseStep 1414503 = 2121755) B2121755
theorem B679270157 : Blo 1413526 679270157 := bstep (se 3 (by rfl) ⟨127363154, by rfl⟩ : syracuseStep 679270157 = 254726309) B254726309
theorem B5372669 : Blo 1413526 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B7158779 : Blo 1413526 7158779 := bstep (se 1 (by rfl) ⟨5369084, by rfl⟩ : syracuseStep 7158779 = 10738169) B10738169
theorem B2121263 : Blo 1413526 2121263 := bstep (se 1 (by rfl) ⟨1590947, by rfl⟩ : syracuseStep 2121263 = 3181895) B3181895
theorem B6799133 : Blo 1413526 6799133 := bstep (se 3 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 6799133 = 2549675) B2549675
theorem B4775759 : Blo 1413526 4775759 := bstep (se 1 (by rfl) ⟨3581819, by rfl⟩ : syracuseStep 4775759 = 7163639) B7163639
theorem B2121707 : Blo 1413526 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B4776731 : Blo 1413526 4776731 := bstep (se 1 (by rfl) ⟨3582548, by rfl⟩ : syracuseStep 4776731 = 7165097) B7165097
theorem B452846771 : Blo 1413526 452846771 := bstep (se 1 (by rfl) ⟨339635078, by rfl⟩ : syracuseStep 452846771 = 679270157) B679270157
theorem B1590655 : Blo 1413526 1590655 := bstep (se 1 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 1590655 = 2385983) B2385983
theorem B2581993 : Blo 1413526 2581993 := bstep (se 2 (by rfl) ⟨968247, by rfl⟩ : syracuseStep 2581993 = 1936495) B1936495
theorem B3581779 : Blo 1413526 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B4532755 : Blo 1413526 4532755 := bstep (se 1 (by rfl) ⟨3399566, by rfl⟩ : syracuseStep 4532755 = 6799133) B6799133
theorem B3181211 : Blo 1413526 3181211 := bstep (se 1 (by rfl) ⟨2385908, by rfl⟩ : syracuseStep 3181211 = 4771817) B4771817
theorem B20392667 : Blo 1413526 20392667 := bstep (se 1 (by rfl) ⟨15294500, by rfl⟩ : syracuseStep 20392667 = 30589001) B30589001
theorem B2420857 : Blo 1413526 2420857 := bstep (se 2 (by rfl) ⟨907821, by rfl⟩ : syracuseStep 2420857 = 1815643) B1815643
theorem B12087791 : Blo 1413526 12087791 := bstep (se 1 (by rfl) ⟨9065843, by rfl⟩ : syracuseStep 12087791 = 18131687) B18131687
theorem B4772519 : Blo 1413526 4772519 := bstep (se 1 (by rfl) ⟨3579389, by rfl⟩ : syracuseStep 4772519 = 7158779) B7158779
theorem B6796001 : Blo 1413526 6796001 := bstep (se 2 (by rfl) ⟨2548500, by rfl⟩ : syracuseStep 6796001 = 5097001) B5097001
theorem B1414175 : Blo 1413526 1414175 := bstep (se 1 (by rfl) ⟨1060631, by rfl⟩ : syracuseStep 1414175 = 2121263) B2121263
theorem B3183839 : Blo 1413526 3183839 := bstep (se 1 (by rfl) ⟨2387879, by rfl⟩ : syracuseStep 3183839 = 4775759) B4775759
theorem B1414471 : Blo 1413526 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B1414591 : Blo 1413526 1414591 := bstep (se 1 (by rfl) ⟨1060943, by rfl⟩ : syracuseStep 1414591 = 2121887) B2121887
theorem B3184595 : Blo 1413526 3184595 := bstep (se 1 (by rfl) ⟨2388446, by rfl⟩ : syracuseStep 3184595 = 4776893) B4776893
theorem B7165907 : Blo 1413526 7165907 := bstep (se 1 (by rfl) ⟨5374430, by rfl⟩ : syracuseStep 7165907 = 10748861) B10748861
theorem B3184703 : Blo 1413526 3184703 := bstep (se 1 (by rfl) ⟨2388527, by rfl⟩ : syracuseStep 3184703 = 4777055) B4777055
theorem B1415407 : Blo 1413526 1415407 := bstep (se 1 (by rfl) ⟨1061555, by rfl⟩ : syracuseStep 1415407 = 2123111) B2123111
theorem B1415419 : Blo 1413526 1415419 := bstep (se 1 (by rfl) ⟨1061564, by rfl⟩ : syracuseStep 1415419 = 2123129) B2123129
theorem B3578195 : Blo 1413526 3578195 := bstep (se 1 (by rfl) ⟨2683646, by rfl⟩ : syracuseStep 3578195 = 5367293) B5367293
theorem B3627487 : Blo 1413526 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B30596609 : Blo 1413526 30596609 := bstep (se 2 (by rfl) ⟨11473728, by rfl⟩ : syracuseStep 30596609 = 22947457) B22947457
theorem B17194639 : Blo 1413526 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B24493853 : Blo 1413526 24493853 := bstep (se 3 (by rfl) ⟨4592597, by rfl⟩ : syracuseStep 24493853 = 9185195) B9185195
theorem B4530667 : Blo 1413526 4530667 := bstep (se 1 (by rfl) ⟨3398000, by rfl⟩ : syracuseStep 4530667 = 6796001) B6796001
theorem B12911237 : Blo 1413526 12911237 := bstep (se 4 (by rfl) ⟨1210428, by rfl⟩ : syracuseStep 12911237 = 2420857) B2420857
theorem B2122559 : Blo 1413526 2122559 := bstep (se 1 (by rfl) ⟨1591919, by rfl⟩ : syracuseStep 2122559 = 3183839) B3183839
theorem B2123063 : Blo 1413526 2123063 := bstep (se 1 (by rfl) ⟨1592297, by rfl⟩ : syracuseStep 2123063 = 3184595) B3184595
theorem B4777271 : Blo 1413526 4777271 := bstep (se 1 (by rfl) ⟨3582953, by rfl⟩ : syracuseStep 4777271 = 7165907) B7165907
theorem B2123135 : Blo 1413526 2123135 := bstep (se 1 (by rfl) ⟨1592351, by rfl⟩ : syracuseStep 2123135 = 3184703) B3184703
theorem B2385463 : Blo 1413526 2385463 := bstep (se 1 (by rfl) ⟨1789097, by rfl⟩ : syracuseStep 2385463 = 3578195) B3578195
theorem B3442657 : Blo 1413526 3442657 := bstep (se 2 (by rfl) ⟨1290996, by rfl⟩ : syracuseStep 3442657 = 2581993) B2581993
theorem B16329235 : Blo 1413526 16329235 := bstep (se 1 (by rfl) ⟨12246926, by rfl⟩ : syracuseStep 16329235 = 24493853) B24493853
theorem B3181679 : Blo 1413526 3181679 := bstep (se 1 (by rfl) ⟨2386259, by rfl⟩ : syracuseStep 3181679 = 4772519) B4772519
theorem B13595111 : Blo 1413526 13595111 := bstep (se 1 (by rfl) ⟨10196333, by rfl⟩ : syracuseStep 13595111 = 20392667) B20392667
theorem B22926185 : Blo 1413526 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B19346597 : Blo 1413526 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B8058527 : Blo 1413526 8058527 := bstep (se 1 (by rfl) ⟨6043895, by rfl⟩ : syracuseStep 8058527 = 12087791) B12087791
theorem B3184487 : Blo 1413526 3184487 := bstep (se 1 (by rfl) ⟨2388365, by rfl⟩ : syracuseStep 3184487 = 4776731) B4776731
theorem B6043673 : Blo 1413526 6043673 := bstep (se 2 (by rfl) ⟨2266377, by rfl⟩ : syracuseStep 6043673 = 4532755) B4532755
theorem B301897847 : Blo 1413526 301897847 := bstep (se 1 (by rfl) ⟨226423385, by rfl⟩ : syracuseStep 301897847 = 452846771) B452846771
theorem B2120807 : Blo 1413526 2120807 := bstep (se 1 (by rfl) ⟨1590605, by rfl⟩ : syracuseStep 2120807 = 3181211) B3181211
theorem B2120873 : Blo 1413526 2120873 := bstep (se 2 (by rfl) ⟨795327, by rfl⟩ : syracuseStep 2120873 = 1590655) B1590655
theorem B20397739 : Blo 1413526 20397739 := bstep (se 1 (by rfl) ⟨15298304, by rfl⟩ : syracuseStep 20397739 = 30596609) B30596609
theorem B4775705 : Blo 1413526 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B2122991 : Blo 1413526 2122991 := bstep (se 1 (by rfl) ⟨1592243, by rfl⟩ : syracuseStep 2122991 = 3184487) B3184487
theorem B3180617 : Blo 1413526 3180617 := bstep (se 2 (by rfl) ⟨1192731, by rfl⟩ : syracuseStep 3180617 = 2385463) B2385463
theorem B4590209 : Blo 1413526 4590209 := bstep (se 2 (by rfl) ⟨1721328, by rfl⟩ : syracuseStep 4590209 = 3442657) B3442657
theorem B9063407 : Blo 1413526 9063407 := bstep (se 1 (by rfl) ⟨6797555, by rfl⟩ : syracuseStep 9063407 = 13595111) B13595111
theorem B6040889 : Blo 1413526 6040889 := bstep (se 2 (by rfl) ⟨2265333, by rfl⟩ : syracuseStep 6040889 = 4530667) B4530667
theorem B12897731 : Blo 1413526 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B201265231 : Blo 1413526 201265231 := bstep (se 1 (by rfl) ⟨150948923, by rfl⟩ : syracuseStep 201265231 = 301897847) B301897847
theorem B1413871 : Blo 1413526 1413871 := bstep (se 1 (by rfl) ⟨1060403, by rfl⟩ : syracuseStep 1413871 = 2120807) B2120807
theorem B1413915 : Blo 1413526 1413915 := bstep (se 1 (by rfl) ⟨1060436, by rfl⟩ : syracuseStep 1413915 = 2120873) B2120873
theorem B3183803 : Blo 1413526 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B8607491 : Blo 1413526 8607491 := bstep (se 1 (by rfl) ⟨6455618, by rfl⟩ : syracuseStep 8607491 = 12911237) B12911237
theorem B1415039 : Blo 1413526 1415039 := bstep (se 1 (by rfl) ⟨1061279, by rfl⟩ : syracuseStep 1415039 = 2122559) B2122559
theorem B15284123 : Blo 1413526 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B21772313 : Blo 1413526 21772313 := bstep (se 2 (by rfl) ⟨8164617, by rfl⟩ : syracuseStep 21772313 = 16329235) B16329235
theorem B1415375 : Blo 1413526 1415375 := bstep (se 1 (by rfl) ⟨1061531, by rfl⟩ : syracuseStep 1415375 = 2123063) B2123063
theorem B3184847 : Blo 1413526 3184847 := bstep (se 1 (by rfl) ⟨2388635, by rfl⟩ : syracuseStep 3184847 = 4777271) B4777271
theorem B1415423 : Blo 1413526 1415423 := bstep (se 1 (by rfl) ⟨1061567, by rfl⟩ : syracuseStep 1415423 = 2123135) B2123135
theorem B5372351 : Blo 1413526 5372351 := bstep (se 1 (by rfl) ⟨4029263, by rfl⟩ : syracuseStep 5372351 = 8058527) B8058527
theorem B4029115 : Blo 1413526 4029115 := bstep (se 1 (by rfl) ⟨3021836, by rfl⟩ : syracuseStep 4029115 = 6043673) B6043673
theorem B2121119 : Blo 1413526 2121119 := bstep (se 1 (by rfl) ⟨1590839, by rfl⟩ : syracuseStep 2121119 = 3181679) B3181679
theorem B27196985 : Blo 1413526 27196985 := bstep (se 2 (by rfl) ⟨10198869, by rfl⟩ : syracuseStep 27196985 = 20397739) B20397739
theorem B268353641 : Blo 1413526 268353641 := bstep (se 2 (by rfl) ⟨100632615, by rfl⟩ : syracuseStep 268353641 = 201265231) B201265231
theorem B2122535 : Blo 1413526 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B2123231 : Blo 1413526 2123231 := bstep (se 1 (by rfl) ⟨1592423, by rfl⟩ : syracuseStep 2123231 = 3184847) B3184847
theorem B3581567 : Blo 1413526 3581567 := bstep (se 1 (by rfl) ⟨2686175, by rfl⟩ : syracuseStep 3581567 = 5372351) B5372351
theorem B12240557 : Blo 1413526 12240557 := bstep (se 3 (by rfl) ⟨2295104, by rfl⟩ : syracuseStep 12240557 = 4590209) B4590209
theorem B18131323 : Blo 1413526 18131323 := bstep (se 1 (by rfl) ⟨13598492, by rfl⟩ : syracuseStep 18131323 = 27196985) B27196985
theorem B5738327 : Blo 1413526 5738327 := bstep (se 1 (by rfl) ⟨4303745, by rfl⟩ : syracuseStep 5738327 = 8607491) B8607491
theorem B6042271 : Blo 1413526 6042271 := bstep (se 1 (by rfl) ⟨4531703, by rfl⟩ : syracuseStep 6042271 = 9063407) B9063407
theorem B4027259 : Blo 1413526 4027259 := bstep (se 1 (by rfl) ⟨3020444, by rfl⟩ : syracuseStep 4027259 = 6040889) B6040889
theorem B1414079 : Blo 1413526 1414079 := bstep (se 1 (by rfl) ⟨1060559, by rfl⟩ : syracuseStep 1414079 = 2121119) B2121119
theorem B8598487 : Blo 1413526 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B1415327 : Blo 1413526 1415327 := bstep (se 1 (by rfl) ⟨1061495, by rfl⟩ : syracuseStep 1415327 = 2122991) B2122991
theorem B5372153 : Blo 1413526 5372153 := bstep (se 2 (by rfl) ⟨2014557, by rfl⟩ : syracuseStep 5372153 = 4029115) B4029115
theorem B10189415 : Blo 1413526 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B14514875 : Blo 1413526 14514875 := bstep (se 1 (by rfl) ⟨10886156, by rfl⟩ : syracuseStep 14514875 = 21772313) B21772313
theorem B2120411 : Blo 1413526 2120411 := bstep (se 1 (by rfl) ⟨1590308, by rfl⟩ : syracuseStep 2120411 = 3180617) B3180617
theorem B24175097 : Blo 1413526 24175097 := bstep (se 2 (by rfl) ⟨9065661, by rfl⟩ : syracuseStep 24175097 = 18131323) B18131323
theorem B8160371 : Blo 1413526 8160371 := bstep (se 1 (by rfl) ⟨6120278, by rfl⟩ : syracuseStep 8160371 = 12240557) B12240557
theorem B3581435 : Blo 1413526 3581435 := bstep (se 1 (by rfl) ⟨2686076, by rfl⟩ : syracuseStep 3581435 = 5372153) B5372153
theorem B6792943 : Blo 1413526 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B9676583 : Blo 1413526 9676583 := bstep (se 1 (by rfl) ⟨7257437, by rfl⟩ : syracuseStep 9676583 = 14514875) B14514875
theorem B8056361 : Blo 1413526 8056361 := bstep (se 2 (by rfl) ⟨3021135, by rfl⟩ : syracuseStep 8056361 = 6042271) B6042271
theorem B2387711 : Blo 1413526 2387711 := bstep (se 1 (by rfl) ⟨1790783, by rfl⟩ : syracuseStep 2387711 = 3581567) B3581567
theorem B11464649 : Blo 1413526 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B1413607 : Blo 1413526 1413607 := bstep (se 1 (by rfl) ⟨1060205, by rfl⟩ : syracuseStep 1413607 = 2120411) B2120411
theorem B178902427 : Blo 1413526 178902427 := bstep (se 1 (by rfl) ⟨134176820, by rfl⟩ : syracuseStep 178902427 = 268353641) B268353641
theorem B1415023 : Blo 1413526 1415023 := bstep (se 1 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 1415023 = 2122535) B2122535
theorem B2684839 : Blo 1413526 2684839 := bstep (se 1 (by rfl) ⟨2013629, by rfl⟩ : syracuseStep 2684839 = 4027259) B4027259
theorem B1415487 : Blo 1413526 1415487 := bstep (se 1 (by rfl) ⟨1061615, by rfl⟩ : syracuseStep 1415487 = 2123231) B2123231
theorem B3825551 : Blo 1413526 3825551 := bstep (se 1 (by rfl) ⟨2869163, by rfl⟩ : syracuseStep 3825551 = 5738327) B5738327
theorem B5440247 : Blo 1413526 5440247 := bstep (se 1 (by rfl) ⟨4080185, by rfl⟩ : syracuseStep 5440247 = 8160371) B8160371
theorem B238536569 : Blo 1413526 238536569 := bstep (se 2 (by rfl) ⟨89451213, by rfl⟩ : syracuseStep 238536569 = 178902427) B178902427
theorem B1591807 : Blo 1413526 1591807 := bstep (se 1 (by rfl) ⟨1193855, by rfl⟩ : syracuseStep 1591807 = 2387711) B2387711
theorem B2550367 : Blo 1413526 2550367 := bstep (se 1 (by rfl) ⟨1912775, by rfl⟩ : syracuseStep 2550367 = 3825551) B3825551
theorem B16116731 : Blo 1413526 16116731 := bstep (se 1 (by rfl) ⟨12087548, by rfl⟩ : syracuseStep 16116731 = 24175097) B24175097
theorem B2387623 : Blo 1413526 2387623 := bstep (se 1 (by rfl) ⟨1790717, by rfl⟩ : syracuseStep 2387623 = 3581435) B3581435
theorem B6451055 : Blo 1413526 6451055 := bstep (se 1 (by rfl) ⟨4838291, by rfl⟩ : syracuseStep 6451055 = 9676583) B9676583
theorem B9057257 : Blo 1413526 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B5370907 : Blo 1413526 5370907 := bstep (se 1 (by rfl) ⟨4028180, by rfl⟩ : syracuseStep 5370907 = 8056361) B8056361
theorem B3579785 : Blo 1413526 3579785 := bstep (se 2 (by rfl) ⟨1342419, by rfl⟩ : syracuseStep 3579785 = 2684839) B2684839
theorem B7643099 : Blo 1413526 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B6038171 : Blo 1413526 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B2122409 : Blo 1413526 2122409 := bstep (se 2 (by rfl) ⟨795903, by rfl⟩ : syracuseStep 2122409 = 1591807) B1591807
theorem B3400489 : Blo 1413526 3400489 := bstep (se 2 (by rfl) ⟨1275183, by rfl⟩ : syracuseStep 3400489 = 2550367) B2550367
theorem B159024379 : Blo 1413526 159024379 := bstep (se 1 (by rfl) ⟨119268284, by rfl⟩ : syracuseStep 159024379 = 238536569) B238536569
theorem B7161209 : Blo 1413526 7161209 := bstep (se 2 (by rfl) ⟨2685453, by rfl⟩ : syracuseStep 7161209 = 5370907) B5370907
theorem B2386523 : Blo 1413526 2386523 := bstep (se 1 (by rfl) ⟨1789892, by rfl⟩ : syracuseStep 2386523 = 3579785) B3579785
theorem B10744487 : Blo 1413526 10744487 := bstep (se 1 (by rfl) ⟨8058365, by rfl⟩ : syracuseStep 10744487 = 16116731) B16116731
theorem B3183497 : Blo 1413526 3183497 := bstep (se 2 (by rfl) ⟨1193811, by rfl⟩ : syracuseStep 3183497 = 2387623) B2387623
theorem B3626831 : Blo 1413526 3626831 := bstep (se 1 (by rfl) ⟨2720123, by rfl⟩ : syracuseStep 3626831 = 5440247) B5440247
theorem B4300703 : Blo 1413526 4300703 := bstep (se 1 (by rfl) ⟨3225527, by rfl⟩ : syracuseStep 4300703 = 6451055) B6451055
theorem B5095399 : Blo 1413526 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B2122331 : Blo 1413526 2122331 := bstep (se 1 (by rfl) ⟨1591748, by rfl⟩ : syracuseStep 2122331 = 3183497) B3183497
theorem B2417887 : Blo 1413526 2417887 := bstep (se 1 (by rfl) ⟨1813415, by rfl⟩ : syracuseStep 2417887 = 3626831) B3626831
theorem B1591015 : Blo 1413526 1591015 := bstep (se 1 (by rfl) ⟨1193261, by rfl⟩ : syracuseStep 1591015 = 2386523) B2386523
theorem B6793865 : Blo 1413526 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B4025447 : Blo 1413526 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B7162991 : Blo 1413526 7162991 := bstep (se 1 (by rfl) ⟨5372243, by rfl⟩ : syracuseStep 7162991 = 10744487) B10744487
theorem B4533985 : Blo 1413526 4533985 := bstep (se 2 (by rfl) ⟨1700244, by rfl⟩ : syracuseStep 4533985 = 3400489) B3400489
theorem B1414939 : Blo 1413526 1414939 := bstep (se 1 (by rfl) ⟨1061204, by rfl⟩ : syracuseStep 1414939 = 2122409) B2122409
theorem B4774139 : Blo 1413526 4774139 := bstep (se 1 (by rfl) ⟨3580604, by rfl⟩ : syracuseStep 4774139 = 7161209) B7161209
theorem B212032505 : Blo 1413526 212032505 := bstep (se 2 (by rfl) ⟨79512189, by rfl⟩ : syracuseStep 212032505 = 159024379) B159024379
theorem B2867135 : Blo 1413526 2867135 := bstep (se 1 (by rfl) ⟨2150351, by rfl⟩ : syracuseStep 2867135 = 4300703) B4300703
theorem B141355003 : Blo 1413526 141355003 := bstep (se 1 (by rfl) ⟨106016252, by rfl⟩ : syracuseStep 141355003 = 212032505) B212032505
theorem B7645693 : Blo 1413526 7645693 := bstep (se 3 (by rfl) ⟨1433567, by rfl⟩ : syracuseStep 7645693 = 2867135) B2867135
theorem B3182759 : Blo 1413526 3182759 := bstep (se 1 (by rfl) ⟨2387069, by rfl⟩ : syracuseStep 3182759 = 4774139) B4774139
theorem B3223849 : Blo 1413526 3223849 := bstep (se 2 (by rfl) ⟨1208943, by rfl⟩ : syracuseStep 3223849 = 2417887) B2417887
theorem B2683631 : Blo 1413526 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B1414887 : Blo 1413526 1414887 := bstep (se 1 (by rfl) ⟨1061165, by rfl⟩ : syracuseStep 1414887 = 2122331) B2122331
theorem B4529243 : Blo 1413526 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B4775327 : Blo 1413526 4775327 := bstep (se 1 (by rfl) ⟨3581495, by rfl⟩ : syracuseStep 4775327 = 7162991) B7162991
theorem B6045313 : Blo 1413526 6045313 := bstep (se 2 (by rfl) ⟨2266992, by rfl⟩ : syracuseStep 6045313 = 4533985) B4533985
theorem B2121353 : Blo 1413526 2121353 := bstep (se 2 (by rfl) ⟨795507, by rfl⟩ : syracuseStep 2121353 = 1591015) B1591015
theorem B2121839 : Blo 1413526 2121839 := bstep (se 1 (by rfl) ⟨1591379, by rfl⟩ : syracuseStep 2121839 = 3182759) B3182759
theorem B12077981 : Blo 1413526 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B10194257 : Blo 1413526 10194257 := bstep (se 2 (by rfl) ⟨3822846, by rfl⟩ : syracuseStep 10194257 = 7645693) B7645693
theorem B7156349 : Blo 1413526 7156349 := bstep (se 3 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 7156349 = 2683631) B2683631
theorem B3183551 : Blo 1413526 3183551 := bstep (se 1 (by rfl) ⟨2387663, by rfl⟩ : syracuseStep 3183551 = 4775327) B4775327
theorem B1414235 : Blo 1413526 1414235 := bstep (se 1 (by rfl) ⟨1060676, by rfl⟩ : syracuseStep 1414235 = 2121353) B2121353
theorem B4298465 : Blo 1413526 4298465 := bstep (se 2 (by rfl) ⟨1611924, by rfl⟩ : syracuseStep 4298465 = 3223849) B3223849
theorem B8060417 : Blo 1413526 8060417 := bstep (se 2 (by rfl) ⟨3022656, by rfl⟩ : syracuseStep 8060417 = 6045313) B6045313
theorem B188473337 : Blo 1413526 188473337 := bstep (se 2 (by rfl) ⟨70677501, by rfl⟩ : syracuseStep 188473337 = 141355003) B141355003
theorem B2122367 : Blo 1413526 2122367 := bstep (se 1 (by rfl) ⟨1591775, by rfl⟩ : syracuseStep 2122367 = 3183551) B3183551
theorem B11462573 : Blo 1413526 11462573 := bstep (se 3 (by rfl) ⟨2149232, by rfl⟩ : syracuseStep 11462573 = 4298465) B4298465
theorem B4770899 : Blo 1413526 4770899 := bstep (se 1 (by rfl) ⟨3578174, by rfl⟩ : syracuseStep 4770899 = 7156349) B7156349
theorem B6796171 : Blo 1413526 6796171 := bstep (se 1 (by rfl) ⟨5097128, by rfl⟩ : syracuseStep 6796171 = 10194257) B10194257
theorem B1414559 : Blo 1413526 1414559 := bstep (se 1 (by rfl) ⟨1060919, by rfl⟩ : syracuseStep 1414559 = 2121839) B2121839
theorem B8051987 : Blo 1413526 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B5373611 : Blo 1413526 5373611 := bstep (se 1 (by rfl) ⟨4030208, by rfl⟩ : syracuseStep 5373611 = 8060417) B8060417
theorem B125648891 : Blo 1413526 125648891 := bstep (se 1 (by rfl) ⟨94236668, by rfl⟩ : syracuseStep 125648891 = 188473337) B188473337
theorem B9061561 : Blo 1413526 9061561 := bstep (se 2 (by rfl) ⟨3398085, by rfl⟩ : syracuseStep 9061561 = 6796171) B6796171
theorem B3180599 : Blo 1413526 3180599 := bstep (se 1 (by rfl) ⟨2385449, by rfl⟩ : syracuseStep 3180599 = 4770899) B4770899
theorem B5367991 : Blo 1413526 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B3582407 : Blo 1413526 3582407 := bstep (se 1 (by rfl) ⟨2686805, by rfl⟩ : syracuseStep 3582407 = 5373611) B5373611
theorem B83765927 : Blo 1413526 83765927 := bstep (se 1 (by rfl) ⟨62824445, by rfl⟩ : syracuseStep 83765927 = 125648891) B125648891
theorem B1414911 : Blo 1413526 1414911 := bstep (se 1 (by rfl) ⟨1061183, by rfl⟩ : syracuseStep 1414911 = 2122367) B2122367
theorem B7641715 : Blo 1413526 7641715 := bstep (se 1 (by rfl) ⟨5731286, by rfl⟩ : syracuseStep 7641715 = 11462573) B11462573
theorem B2388271 : Blo 1413526 2388271 := bstep (se 1 (by rfl) ⟨1791203, by rfl⟩ : syracuseStep 2388271 = 3582407) B3582407
theorem B223375805 : Blo 1413526 223375805 := bstep (se 3 (by rfl) ⟨41882963, by rfl⟩ : syracuseStep 223375805 = 83765927) B83765927
theorem B7157321 : Blo 1413526 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B10188953 : Blo 1413526 10188953 := bstep (se 2 (by rfl) ⟨3820857, by rfl⟩ : syracuseStep 10188953 = 7641715) B7641715
theorem B2120399 : Blo 1413526 2120399 := bstep (se 1 (by rfl) ⟨1590299, by rfl⟩ : syracuseStep 2120399 = 3180599) B3180599
theorem B12082081 : Blo 1413526 12082081 := bstep (se 2 (by rfl) ⟨4530780, by rfl⟩ : syracuseStep 12082081 = 9061561) B9061561
theorem B6792635 : Blo 1413526 6792635 := bstep (se 1 (by rfl) ⟨5094476, by rfl⟩ : syracuseStep 6792635 = 10188953) B10188953
theorem B148917203 : Blo 1413526 148917203 := bstep (se 1 (by rfl) ⟨111687902, by rfl⟩ : syracuseStep 148917203 = 223375805) B223375805
theorem B4771547 : Blo 1413526 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B16109441 : Blo 1413526 16109441 := bstep (se 2 (by rfl) ⟨6041040, by rfl⟩ : syracuseStep 16109441 = 12082081) B12082081
theorem B1413599 : Blo 1413526 1413599 := bstep (se 1 (by rfl) ⟨1060199, by rfl⟩ : syracuseStep 1413599 = 2120399) B2120399
theorem B3184361 : Blo 1413526 3184361 := bstep (se 2 (by rfl) ⟨1194135, by rfl⟩ : syracuseStep 3184361 = 2388271) B2388271
theorem B2122907 : Blo 1413526 2122907 := bstep (se 1 (by rfl) ⟨1592180, by rfl⟩ : syracuseStep 2122907 = 3184361) B3184361
theorem B3181031 : Blo 1413526 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B4528423 : Blo 1413526 4528423 := bstep (se 1 (by rfl) ⟨3396317, by rfl⟩ : syracuseStep 4528423 = 6792635) B6792635
theorem B99278135 : Blo 1413526 99278135 := bstep (se 1 (by rfl) ⟨74458601, by rfl⟩ : syracuseStep 99278135 = 148917203) B148917203
theorem B10739627 : Blo 1413526 10739627 := bstep (se 1 (by rfl) ⟨8054720, by rfl⟩ : syracuseStep 10739627 = 16109441) B16109441
theorem B6037897 : Blo 1413526 6037897 := bstep (se 2 (by rfl) ⟨2264211, by rfl⟩ : syracuseStep 6037897 = 4528423) B4528423
theorem B66185423 : Blo 1413526 66185423 := bstep (se 1 (by rfl) ⟨49639067, by rfl⟩ : syracuseStep 66185423 = 99278135) B99278135
theorem B1415271 : Blo 1413526 1415271 := bstep (se 1 (by rfl) ⟨1061453, by rfl⟩ : syracuseStep 1415271 = 2122907) B2122907
theorem B2120687 : Blo 1413526 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B7159751 : Blo 1413526 7159751 := bstep (se 1 (by rfl) ⟨5369813, by rfl⟩ : syracuseStep 7159751 = 10739627) B10739627
theorem B44123615 : Blo 1413526 44123615 := bstep (se 1 (by rfl) ⟨33092711, by rfl⟩ : syracuseStep 44123615 = 66185423) B66185423
theorem B1413791 : Blo 1413526 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B4773167 : Blo 1413526 4773167 := bstep (se 1 (by rfl) ⟨3579875, by rfl⟩ : syracuseStep 4773167 = 7159751) B7159751
theorem B8050529 : Blo 1413526 8050529 := bstep (se 2 (by rfl) ⟨3018948, by rfl⟩ : syracuseStep 8050529 = 6037897) B6037897
theorem B5367019 : Blo 1413526 5367019 := bstep (se 1 (by rfl) ⟨4025264, by rfl⟩ : syracuseStep 5367019 = 8050529) B8050529
theorem B3182111 : Blo 1413526 3182111 := bstep (se 1 (by rfl) ⟨2386583, by rfl⟩ : syracuseStep 3182111 = 4773167) B4773167
theorem B29415743 : Blo 1413526 29415743 := bstep (se 1 (by rfl) ⟨22061807, by rfl⟩ : syracuseStep 29415743 = 44123615) B44123615
theorem B7156025 : Blo 1413526 7156025 := bstep (se 2 (by rfl) ⟨2683509, by rfl⟩ : syracuseStep 7156025 = 5367019) B5367019
theorem B19610495 : Blo 1413526 19610495 := bstep (se 1 (by rfl) ⟨14707871, by rfl⟩ : syracuseStep 19610495 = 29415743) B29415743
theorem B2121407 : Blo 1413526 2121407 := bstep (se 1 (by rfl) ⟨1591055, by rfl⟩ : syracuseStep 2121407 = 3182111) B3182111
theorem B4770683 : Blo 1413526 4770683 := bstep (se 1 (by rfl) ⟨3578012, by rfl⟩ : syracuseStep 4770683 = 7156025) B7156025
theorem B1414271 : Blo 1413526 1414271 := bstep (se 1 (by rfl) ⟨1060703, by rfl⟩ : syracuseStep 1414271 = 2121407) B2121407
theorem B13073663 : Blo 1413526 13073663 := bstep (se 1 (by rfl) ⟨9805247, by rfl⟩ : syracuseStep 13073663 = 19610495) B19610495
theorem B3180455 : Blo 1413526 3180455 := bstep (se 1 (by rfl) ⟨2385341, by rfl⟩ : syracuseStep 3180455 = 4770683) B4770683
theorem B34863101 : Blo 1413526 34863101 := bstep (se 3 (by rfl) ⟨6536831, by rfl⟩ : syracuseStep 34863101 = 13073663) B13073663
theorem B23242067 : Blo 1413526 23242067 := bstep (se 1 (by rfl) ⟨17431550, by rfl⟩ : syracuseStep 23242067 = 34863101) B34863101
theorem B2120303 : Blo 1413526 2120303 := bstep (se 1 (by rfl) ⟨1590227, by rfl⟩ : syracuseStep 2120303 = 3180455) B3180455
theorem B991661525 : Blo 1413526 991661525 := bstep (se 7 (by rfl) ⟨11621033, by rfl⟩ : syracuseStep 991661525 = 23242067) B23242067
theorem B1413535 : Blo 1413526 1413535 := bstep (se 1 (by rfl) ⟨1060151, by rfl⟩ : syracuseStep 1413535 = 2120303) B2120303
theorem B661107683 : Blo 1413526 661107683 := bstep (se 1 (by rfl) ⟨495830762, by rfl⟩ : syracuseStep 661107683 = 991661525) B991661525
theorem B440738455 : Blo 1413526 440738455 := bstep (se 1 (by rfl) ⟨330553841, by rfl⟩ : syracuseStep 440738455 = 661107683) B661107683
theorem B587651273 : Blo 1413526 587651273 := bstep (se 2 (by rfl) ⟨220369227, by rfl⟩ : syracuseStep 587651273 = 440738455) B440738455
theorem B391767515 : Blo 1413526 391767515 := bstep (se 1 (by rfl) ⟨293825636, by rfl⟩ : syracuseStep 391767515 = 587651273) B587651273
theorem B261178343 : Blo 1413526 261178343 := bstep (se 1 (by rfl) ⟨195883757, by rfl⟩ : syracuseStep 261178343 = 391767515) B391767515
theorem B174118895 : Blo 1413526 174118895 := bstep (se 1 (by rfl) ⟨130589171, by rfl⟩ : syracuseStep 174118895 = 261178343) B261178343
theorem B116079263 : Blo 1413526 116079263 := bstep (se 1 (by rfl) ⟨87059447, by rfl⟩ : syracuseStep 116079263 = 174118895) B174118895
theorem B77386175 : Blo 1413526 77386175 := bstep (se 1 (by rfl) ⟨58039631, by rfl⟩ : syracuseStep 77386175 = 116079263) B116079263
theorem B51590783 : Blo 1413526 51590783 := bstep (se 1 (by rfl) ⟨38693087, by rfl⟩ : syracuseStep 51590783 = 77386175) B77386175
theorem B34393855 : Blo 1413526 34393855 := bstep (se 1 (by rfl) ⟨25795391, by rfl⟩ : syracuseStep 34393855 = 51590783) B51590783
theorem B45858473 : Blo 1413526 45858473 := bstep (se 2 (by rfl) ⟨17196927, by rfl⟩ : syracuseStep 45858473 = 34393855) B34393855
theorem B30572315 : Blo 1413526 30572315 := bstep (se 1 (by rfl) ⟨22929236, by rfl⟩ : syracuseStep 30572315 = 45858473) B45858473
theorem B20381543 : Blo 1413526 20381543 := bstep (se 1 (by rfl) ⟨15286157, by rfl⟩ : syracuseStep 20381543 = 30572315) B30572315
theorem B13587695 : Blo 1413526 13587695 := bstep (se 1 (by rfl) ⟨10190771, by rfl⟩ : syracuseStep 13587695 = 20381543) B20381543
theorem B9058463 : Blo 1413526 9058463 := bstep (se 1 (by rfl) ⟨6793847, by rfl⟩ : syracuseStep 9058463 = 13587695) B13587695
theorem B6038975 : Blo 1413526 6038975 := bstep (se 1 (by rfl) ⟨4529231, by rfl⟩ : syracuseStep 6038975 = 9058463) B9058463
theorem B4025983 : Blo 1413526 4025983 := bstep (se 1 (by rfl) ⟨3019487, by rfl⟩ : syracuseStep 4025983 = 6038975) B6038975
theorem B5367977 : Blo 1413526 5367977 := bstep (se 2 (by rfl) ⟨2012991, by rfl⟩ : syracuseStep 5367977 = 4025983) B4025983
theorem B3578651 : Blo 1413526 3578651 := bstep (se 1 (by rfl) ⟨2683988, by rfl⟩ : syracuseStep 3578651 = 5367977) B5367977
theorem B2385767 : Blo 1413526 2385767 := bstep (se 1 (by rfl) ⟨1789325, by rfl⟩ : syracuseStep 2385767 = 3578651) B3578651
theorem B1590511 : Blo 1413526 1590511 := bstep (se 1 (by rfl) ⟨1192883, by rfl⟩ : syracuseStep 1590511 = 2385767) B2385767
theorem B2120681 : Blo 1413526 2120681 := bstep (se 2 (by rfl) ⟨795255, by rfl⟩ : syracuseStep 2120681 = 1590511) B1590511
theorem B1413787 : Blo 1413526 1413787 := bstep (se 1 (by rfl) ⟨1060340, by rfl⟩ : syracuseStep 1413787 = 2120681) B2120681

theorem C0 (j : ℕ) (h1 : 353381 ≤ j) (h2 : j ≤ 353880) : Blo 1413526 (4 * j + 3) := by
  interval_cases j
  · exact B1413527
  · exact B1413531
  · exact B1413535
  · exact B1413539
  · exact B1413543
  · exact B1413547
  · exact B1413551
  · exact B1413555
  · exact B1413559
  · exact B1413563
  · exact B1413567
  · exact B1413571
  · exact B1413575
  · exact B1413579
  · exact B1413583
  · exact B1413587
  · exact B1413591
  · exact B1413595
  · exact B1413599
  · exact B1413603
  · exact B1413607
  · exact B1413611
  · exact B1413615
  · exact B1413619
  · exact B1413623
  · exact B1413627
  · exact B1413631
  · exact B1413635
  · exact B1413639
  · exact B1413643
  · exact B1413647
  · exact B1413651
  · exact B1413655
  · exact B1413659
  · exact B1413663
  · exact B1413667
  · exact B1413671
  · exact B1413675
  · exact B1413679
  · exact B1413683
  · exact B1413687
  · exact B1413691
  · exact B1413695
  · exact B1413699
  · exact B1413703
  · exact B1413707
  · exact B1413711
  · exact B1413715
  · exact B1413719
  · exact B1413723
  · exact B1413727
  · exact B1413731
  · exact B1413735
  · exact B1413739
  · exact B1413743
  · exact B1413747
  · exact B1413751
  · exact B1413755
  · exact B1413759
  · exact B1413763
  · exact B1413767
  · exact B1413771
  · exact B1413775
  · exact B1413779
  · exact B1413783
  · exact B1413787
  · exact B1413791
  · exact B1413795
  · exact B1413799
  · exact B1413803
  · exact B1413807
  · exact B1413811
  · exact B1413815
  · exact B1413819
  · exact B1413823
  · exact B1413827
  · exact B1413831
  · exact B1413835
  · exact B1413839
  · exact B1413843
  · exact B1413847
  · exact B1413851
  · exact B1413855
  · exact B1413859
  · exact B1413863
  · exact B1413867
  · exact B1413871
  · exact B1413875
  · exact B1413879
  · exact B1413883
  · exact B1413887
  · exact B1413891
  · exact B1413895
  · exact B1413899
  · exact B1413903
  · exact B1413907
  · exact B1413911
  · exact B1413915
  · exact B1413919
  · exact B1413923
  · exact B1413927
  · exact B1413931
  · exact B1413935
  · exact B1413939
  · exact B1413943
  · exact B1413947
  · exact B1413951
  · exact B1413955
  · exact B1413959
  · exact B1413963
  · exact B1413967
  · exact B1413971
  · exact B1413975
  · exact B1413979
  · exact B1413983
  · exact B1413987
  · exact B1413991
  · exact B1413995
  · exact B1413999
  · exact B1414003
  · exact B1414007
  · exact B1414011
  · exact B1414015
  · exact B1414019
  · exact B1414023
  · exact B1414027
  · exact B1414031
  · exact B1414035
  · exact B1414039
  · exact B1414043
  · exact B1414047
  · exact B1414051
  · exact B1414055
  · exact B1414059
  · exact B1414063
  · exact B1414067
  · exact B1414071
  · exact B1414075
  · exact B1414079
  · exact B1414083
  · exact B1414087
  · exact B1414091
  · exact B1414095
  · exact B1414099
  · exact B1414103
  · exact B1414107
  · exact B1414111
  · exact B1414115
  · exact B1414119
  · exact B1414123
  · exact B1414127
  · exact B1414131
  · exact B1414135
  · exact B1414139
  · exact B1414143
  · exact B1414147
  · exact B1414151
  · exact B1414155
  · exact B1414159
  · exact B1414163
  · exact B1414167
  · exact B1414171
  · exact B1414175
  · exact B1414179
  · exact B1414183
  · exact B1414187
  · exact B1414191
  · exact B1414195
  · exact B1414199
  · exact B1414203
  · exact B1414207
  · exact B1414211
  · exact B1414215
  · exact B1414219
  · exact B1414223
  · exact B1414227
  · exact B1414231
  · exact B1414235
  · exact B1414239
  · exact B1414243
  · exact B1414247
  · exact B1414251
  · exact B1414255
  · exact B1414259
  · exact B1414263
  · exact B1414267
  · exact B1414271
  · exact B1414275
  · exact B1414279
  · exact B1414283
  · exact B1414287
  · exact B1414291
  · exact B1414295
  · exact B1414299
  · exact B1414303
  · exact B1414307
  · exact B1414311
  · exact B1414315
  · exact B1414319
  · exact B1414323
  · exact B1414327
  · exact B1414331
  · exact B1414335
  · exact B1414339
  · exact B1414343
  · exact B1414347
  · exact B1414351
  · exact B1414355
  · exact B1414359
  · exact B1414363
  · exact B1414367
  · exact B1414371
  · exact B1414375
  · exact B1414379
  · exact B1414383
  · exact B1414387
  · exact B1414391
  · exact B1414395
  · exact B1414399
  · exact B1414403
  · exact B1414407
  · exact B1414411
  · exact B1414415
  · exact B1414419
  · exact B1414423
  · exact B1414427
  · exact B1414431
  · exact B1414435
  · exact B1414439
  · exact B1414443
  · exact B1414447
  · exact B1414451
  · exact B1414455
  · exact B1414459
  · exact B1414463
  · exact B1414467
  · exact B1414471
  · exact B1414475
  · exact B1414479
  · exact B1414483
  · exact B1414487
  · exact B1414491
  · exact B1414495
  · exact B1414499
  · exact B1414503
  · exact B1414507
  · exact B1414511
  · exact B1414515
  · exact B1414519
  · exact B1414523
  · exact B1414527
  · exact B1414531
  · exact B1414535
  · exact B1414539
  · exact B1414543
  · exact B1414547
  · exact B1414551
  · exact B1414555
  · exact B1414559
  · exact B1414563
  · exact B1414567
  · exact B1414571
  · exact B1414575
  · exact B1414579
  · exact B1414583
  · exact B1414587
  · exact B1414591
  · exact B1414595
  · exact B1414599
  · exact B1414603
  · exact B1414607
  · exact B1414611
  · exact B1414615
  · exact B1414619
  · exact B1414623
  · exact B1414627
  · exact B1414631
  · exact B1414635
  · exact B1414639
  · exact B1414643
  · exact B1414647
  · exact B1414651
  · exact B1414655
  · exact B1414659
  · exact B1414663
  · exact B1414667
  · exact B1414671
  · exact B1414675
  · exact B1414679
  · exact B1414683
  · exact B1414687
  · exact B1414691
  · exact B1414695
  · exact B1414699
  · exact B1414703
  · exact B1414707
  · exact B1414711
  · exact B1414715
  · exact B1414719
  · exact B1414723
  · exact B1414727
  · exact B1414731
  · exact B1414735
  · exact B1414739
  · exact B1414743
  · exact B1414747
  · exact B1414751
  · exact B1414755
  · exact B1414759
  · exact B1414763
  · exact B1414767
  · exact B1414771
  · exact B1414775
  · exact B1414779
  · exact B1414783
  · exact B1414787
  · exact B1414791
  · exact B1414795
  · exact B1414799
  · exact B1414803
  · exact B1414807
  · exact B1414811
  · exact B1414815
  · exact B1414819
  · exact B1414823
  · exact B1414827
  · exact B1414831
  · exact B1414835
  · exact B1414839
  · exact B1414843
  · exact B1414847
  · exact B1414851
  · exact B1414855
  · exact B1414859
  · exact B1414863
  · exact B1414867
  · exact B1414871
  · exact B1414875
  · exact B1414879
  · exact B1414883
  · exact B1414887
  · exact B1414891
  · exact B1414895
  · exact B1414899
  · exact B1414903
  · exact B1414907
  · exact B1414911
  · exact B1414915
  · exact B1414919
  · exact B1414923
  · exact B1414927
  · exact B1414931
  · exact B1414935
  · exact B1414939
  · exact B1414943
  · exact B1414947
  · exact B1414951
  · exact B1414955
  · exact B1414959
  · exact B1414963
  · exact B1414967
  · exact B1414971
  · exact B1414975
  · exact B1414979
  · exact B1414983
  · exact B1414987
  · exact B1414991
  · exact B1414995
  · exact B1414999
  · exact B1415003
  · exact B1415007
  · exact B1415011
  · exact B1415015
  · exact B1415019
  · exact B1415023
  · exact B1415027
  · exact B1415031
  · exact B1415035
  · exact B1415039
  · exact B1415043
  · exact B1415047
  · exact B1415051
  · exact B1415055
  · exact B1415059
  · exact B1415063
  · exact B1415067
  · exact B1415071
  · exact B1415075
  · exact B1415079
  · exact B1415083
  · exact B1415087
  · exact B1415091
  · exact B1415095
  · exact B1415099
  · exact B1415103
  · exact B1415107
  · exact B1415111
  · exact B1415115
  · exact B1415119
  · exact B1415123
  · exact B1415127
  · exact B1415131
  · exact B1415135
  · exact B1415139
  · exact B1415143
  · exact B1415147
  · exact B1415151
  · exact B1415155
  · exact B1415159
  · exact B1415163
  · exact B1415167
  · exact B1415171
  · exact B1415175
  · exact B1415179
  · exact B1415183
  · exact B1415187
  · exact B1415191
  · exact B1415195
  · exact B1415199
  · exact B1415203
  · exact B1415207
  · exact B1415211
  · exact B1415215
  · exact B1415219
  · exact B1415223
  · exact B1415227
  · exact B1415231
  · exact B1415235
  · exact B1415239
  · exact B1415243
  · exact B1415247
  · exact B1415251
  · exact B1415255
  · exact B1415259
  · exact B1415263
  · exact B1415267
  · exact B1415271
  · exact B1415275
  · exact B1415279
  · exact B1415283
  · exact B1415287
  · exact B1415291
  · exact B1415295
  · exact B1415299
  · exact B1415303
  · exact B1415307
  · exact B1415311
  · exact B1415315
  · exact B1415319
  · exact B1415323
  · exact B1415327
  · exact B1415331
  · exact B1415335
  · exact B1415339
  · exact B1415343
  · exact B1415347
  · exact B1415351
  · exact B1415355
  · exact B1415359
  · exact B1415363
  · exact B1415367
  · exact B1415371
  · exact B1415375
  · exact B1415379
  · exact B1415383
  · exact B1415387
  · exact B1415391
  · exact B1415395
  · exact B1415399
  · exact B1415403
  · exact B1415407
  · exact B1415411
  · exact B1415415
  · exact B1415419
  · exact B1415423
  · exact B1415427
  · exact B1415431
  · exact B1415435
  · exact B1415439
  · exact B1415443
  · exact B1415447
  · exact B1415451
  · exact B1415455
  · exact B1415459
  · exact B1415463
  · exact B1415467
  · exact B1415471
  · exact B1415475
  · exact B1415479
  · exact B1415483
  · exact B1415487
  · exact B1415491
  · exact B1415495
  · exact B1415499
  · exact B1415503
  · exact B1415507
  · exact B1415511
  · exact B1415515
  · exact B1415519
  · exact B1415523

theorem solution (m : ℕ) (hlo : 1413526 ≤ m) (hhi : m ≤ 1415526) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 353381 ≤ j := by omega
    have hj2 : j ≤ 353880 := by omega
    have hb : Blo 1413526 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
