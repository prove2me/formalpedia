-- Prove2me | solution 1 for syracuse_descends_range_475787_479787
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:05.181113+00:00
-- url     : https://prove2.me/submissions/ef928d56-1f46-4c5d-8c1c-24cf81441e88

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


theorem B917525 : Blo 475787 917525 := bbase (se 6 (by rfl) ⟨21504, by rfl⟩ : syracuseStep 917525 = 43009) (by norm_num)
theorem B983125 : Blo 475787 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B1212509 : Blo 475787 1212509 := bbase (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) (by norm_num)
theorem B1605797 : Blo 475787 1605797 := bbase (se 4 (by rfl) ⟨150543, by rfl⟩ : syracuseStep 1605797 = 301087) (by norm_num)
theorem B1245557 : Blo 475787 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1016221 : Blo 475787 1016221 := bbase (se 3 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 1016221 = 381083) (by norm_num)
theorem B1212853 : Blo 475787 1212853 := bbase (se 5 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 1212853 = 113705) (by norm_num)
theorem B2425301 : Blo 475787 2425301 := bbase (se 7 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 2425301 = 56843) (by norm_num)
theorem B557533 : Blo 475787 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B1212965 : Blo 475787 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B1606229 : Blo 475787 1606229 := bbase (se 8 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 1606229 = 18823) (by norm_num)
theorem B1016477 : Blo 475787 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B688861 : Blo 475787 688861 := bbase (se 3 (by rfl) ⟨129161, by rfl⟩ : syracuseStep 688861 = 258323) (by norm_num)
theorem B1213157 : Blo 475787 1213157 := bbase (se 4 (by rfl) ⟨113733, by rfl⟩ : syracuseStep 1213157 = 227467) (by norm_num)
theorem B1147709 : Blo 475787 1147709 := bbase (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) (by norm_num)
theorem B2032613 : Blo 475787 2032613 := bbase (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) (by norm_num)
theorem B1606661 : Blo 475787 1606661 := bbase (se 4 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 1606661 = 301249) (by norm_num)
theorem B2720789 : Blo 475787 2720789 := bbase (se 6 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 2720789 = 127537) (by norm_num)
theorem B1213501 : Blo 475787 1213501 := bbase (se 3 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 1213501 = 455063) (by norm_num)
theorem B787573 : Blo 475787 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B4097141 : Blo 475787 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B1213613 : Blo 475787 1213613 := bbase (se 3 (by rfl) ⟨227552, by rfl⟩ : syracuseStep 1213613 = 455105) (by norm_num)
theorem B1148141 : Blo 475787 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B525569 : Blo 475787 525569 := bbase (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) (by norm_num)
theorem B3441973 : Blo 475787 3441973 := bbase (se 5 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 3441973 = 322685) (by norm_num)
theorem B1213805 : Blo 475787 1213805 := bbase (se 3 (by rfl) ⟨227588, by rfl⟩ : syracuseStep 1213805 = 455177) (by norm_num)
theorem B1607093 : Blo 475787 1607093 := bbase (se 5 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 1607093 = 150665) (by norm_num)
theorem B1017365 : Blo 475787 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B1312453 : Blo 475787 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B1214149 : Blo 475787 1214149 := bbase (se 4 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 1214149 = 227653) (by norm_num)
theorem B2426597 : Blo 475787 2426597 := bbase (se 4 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 2426597 = 454987) (by norm_num)
theorem B1017605 : Blo 475787 1017605 := bbase (se 4 (by rfl) ⟨95400, by rfl⟩ : syracuseStep 1017605 = 190801) (by norm_num)
theorem B1640245 : Blo 475787 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1214261 : Blo 475787 1214261 := bbase (se 5 (by rfl) ⟨56918, by rfl⟩ : syracuseStep 1214261 = 113837) (by norm_num)
theorem B1607525 : Blo 475787 1607525 := bbase (se 4 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 1607525 = 301411) (by norm_num)
theorem B1214453 : Blo 475787 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B526381 : Blo 475787 526381 := bbase (se 3 (by rfl) ⟨98696, by rfl⟩ : syracuseStep 526381 = 197393) (by norm_num)
theorem B1935461 : Blo 475787 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1018109 : Blo 475787 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B1018117 : Blo 475787 1018117 := bbase (se 4 (by rfl) ⟨95448, by rfl⟩ : syracuseStep 1018117 = 190897) (by norm_num)
theorem B1607957 : Blo 475787 1607957 := bbase (se 6 (by rfl) ⟨37686, by rfl⟩ : syracuseStep 1607957 = 75373) (by norm_num)
theorem B2296453 : Blo 475787 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B1608389 : Blo 475787 1608389 := bbase (se 4 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 1608389 = 301573) (by norm_num)
theorem B2034389 : Blo 475787 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B2034629 : Blo 475787 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B2427893 : Blo 475787 2427893 := bbase (se 5 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 2427893 = 227615) (by norm_num)
theorem B1608821 : Blo 475787 1608821 := bbase (se 5 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 1608821 = 150827) (by norm_num)
theorem B2722997 : Blo 475787 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B724229 : Blo 475787 724229 := bbase (se 4 (by rfl) ⟨67896, by rfl⟩ : syracuseStep 724229 = 135793) (by norm_num)
theorem B691517 : Blo 475787 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B1019245 : Blo 475787 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B1609205 : Blo 475787 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B1609253 : Blo 475787 1609253 := bbase (se 4 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 1609253 = 301735) (by norm_num)
theorem B2068037 : Blo 475787 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1019621 : Blo 475787 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B724837 : Blo 475787 724837 := bbase (se 4 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 724837 = 135907) (by norm_num)
theorem B1609685 : Blo 475787 1609685 := bbase (se 7 (by rfl) ⟨18863, by rfl⟩ : syracuseStep 1609685 = 37727) (by norm_num)
theorem B11636693 : Blo 475787 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B725117 : Blo 475787 725117 := bbase (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) (by norm_num)
theorem B1610117 : Blo 475787 1610117 := bbase (se 4 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 1610117 = 301897) (by norm_num)
theorem B1151533 : Blo 475787 1151533 := bbase (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) (by norm_num)
theorem B725701 : Blo 475787 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B1610549 : Blo 475787 1610549 := bbase (se 5 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 1610549 = 150989) (by norm_num)
theorem B1151957 : Blo 475787 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B1086509 : Blo 475787 1086509 := bbase (se 3 (by rfl) ⟨203720, by rfl⟩ : syracuseStep 1086509 = 407441) (by norm_num)
theorem B1807541 : Blo 475787 1807541 := bbase (se 5 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 1807541 = 169457) (by norm_num)
theorem B2036917 : Blo 475787 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B1610981 : Blo 475787 1610981 := bbase (se 4 (by rfl) ⟨151029, by rfl⟩ : syracuseStep 1610981 = 302059) (by norm_num)
theorem B1152245 : Blo 475787 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B2299205 : Blo 475787 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1021261 : Blo 475787 1021261 := bbase (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) (by norm_num)
theorem B1807829 : Blo 475787 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B726565 : Blo 475787 726565 := bbase (se 4 (by rfl) ⟨68115, by rfl⟩ : syracuseStep 726565 = 136231) (by norm_num)
theorem B3053173 : Blo 475787 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B1939061 : Blo 475787 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B1611413 : Blo 475787 1611413 := bbase (se 6 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 1611413 = 75535) (by norm_num)
theorem B726821 : Blo 475787 726821 := bbase (se 4 (by rfl) ⟨68139, by rfl⟩ : syracuseStep 726821 = 136279) (by norm_num)
theorem B726869 : Blo 475787 726869 := bbase (se 9 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 726869 = 4259) (by norm_num)
theorem B1611845 : Blo 475787 1611845 := bbase (se 4 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 1611845 = 302221) (by norm_num)
theorem B1022149 : Blo 475787 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B956845 : Blo 475787 956845 := bbase (se 3 (by rfl) ⟨179408, by rfl⟩ : syracuseStep 956845 = 358817) (by norm_num)
theorem B1382837 : Blo 475787 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B1612277 : Blo 475787 1612277 := bbase (se 5 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 1612277 = 151151) (by norm_num)
theorem B629305 : Blo 475787 629305 := bbase (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) (by norm_num)
theorem B1809013 : Blo 475787 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B2038405 : Blo 475787 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B2038421 : Blo 475787 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B1022645 : Blo 475787 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B1809317 : Blo 475787 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B1612709 : Blo 475787 1612709 := bbase (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) (by norm_num)
theorem B859261 : Blo 475787 859261 := bbase (se 3 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 859261 = 322223) (by norm_num)
theorem B1613141 : Blo 475787 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B1023509 : Blo 475787 1023509 := bbase (se 6 (by rfl) ⟨23988, by rfl⟩ : syracuseStep 1023509 = 47977) (by norm_num)
theorem B2301605 : Blo 475787 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B1023653 : Blo 475787 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B1613573 : Blo 475787 1613573 := bbase (se 4 (by rfl) ⟨151272, by rfl⟩ : syracuseStep 1613573 = 302545) (by norm_num)
theorem B1089445 : Blo 475787 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1614005 : Blo 475787 1614005 := bbase (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) (by norm_num)
theorem B860357 : Blo 475787 860357 := bbase (se 4 (by rfl) ⟨80658, by rfl⟩ : syracuseStep 860357 = 161317) (by norm_num)
theorem B1024397 : Blo 475787 1024397 := bbase (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) (by norm_num)
theorem B762301 : Blo 475787 762301 := bbase (se 3 (by rfl) ⟨142931, by rfl⟩ : syracuseStep 762301 = 285863) (by norm_num)
theorem B860645 : Blo 475787 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B1614437 : Blo 475787 1614437 := bbase (se 4 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 1614437 = 302707) (by norm_num)
theorem B1843829 : Blo 475787 1843829 := bbase (se 5 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 1843829 = 172859) (by norm_num)
theorem B2040677 : Blo 475787 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B1811429 : Blo 475787 1811429 := bbase (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) (by norm_num)
theorem B1942501 : Blo 475787 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B1614869 : Blo 475787 1614869 := bbase (se 6 (by rfl) ⟨37848, by rfl⟩ : syracuseStep 1614869 = 75697) (by norm_num)
theorem B1090613 : Blo 475787 1090613 := bbase (se 5 (by rfl) ⟨51122, by rfl⟩ : syracuseStep 1090613 = 102245) (by norm_num)
theorem B2172101 : Blo 475787 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1811717 : Blo 475787 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B763229 : Blo 475787 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B1615301 : Blo 475787 1615301 := bbase (se 4 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 1615301 = 302869) (by norm_num)
theorem B829037 : Blo 475787 829037 := bbase (se 3 (by rfl) ⟨155444, by rfl⟩ : syracuseStep 829037 = 310889) (by norm_num)
theorem B2041573 : Blo 475787 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B861949 : Blo 475787 861949 := bbase (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) (by norm_num)
theorem B763685 : Blo 475787 763685 := bbase (se 4 (by rfl) ⟨71595, by rfl⟩ : syracuseStep 763685 = 143191) (by norm_num)
theorem B1615733 : Blo 475787 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B862093 : Blo 475787 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B1943765 : Blo 475787 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B1616165 : Blo 475787 1616165 := bbase (se 4 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 1616165 = 303031) (by norm_num)
theorem B993701 : Blo 475787 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B1812901 : Blo 475787 1812901 := bbase (se 4 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 1812901 = 339919) (by norm_num)
theorem B862669 : Blo 475787 862669 := bbase (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) (by norm_num)
theorem B1288901 : Blo 475787 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B1813205 : Blo 475787 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B1616597 : Blo 475787 1616597 := bbase (se 7 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 1616597 = 37889) (by norm_num)
theorem B535261 : Blo 475787 535261 := bbase (se 3 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 535261 = 200723) (by norm_num)
theorem B535297 : Blo 475787 535297 := bbase (se 2 (by rfl) ⟨200736, by rfl⟩ : syracuseStep 535297 = 401473) (by norm_num)
theorem B535333 : Blo 475787 535333 := bbase (se 4 (by rfl) ⟨50187, by rfl⟩ : syracuseStep 535333 = 100375) (by norm_num)
theorem B535369 : Blo 475787 535369 := bbase (se 2 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 535369 = 401527) (by norm_num)
theorem B535405 : Blo 475787 535405 := bbase (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) (by norm_num)
theorem B535441 : Blo 475787 535441 := bbase (se 2 (by rfl) ⟨200790, by rfl⟩ : syracuseStep 535441 = 401581) (by norm_num)
theorem B568237 : Blo 475787 568237 := bbase (se 3 (by rfl) ⟨106544, by rfl⟩ : syracuseStep 568237 = 213089) (by norm_num)
theorem B535477 : Blo 475787 535477 := bbase (se 5 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 535477 = 50201) (by norm_num)
theorem B535513 : Blo 475787 535513 := bbase (se 2 (by rfl) ⟨200817, by rfl⟩ : syracuseStep 535513 = 401635) (by norm_num)
theorem B1715189 : Blo 475787 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B535549 : Blo 475787 535549 := bbase (se 3 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 535549 = 200831) (by norm_num)
theorem B535585 : Blo 475787 535585 := bbase (se 2 (by rfl) ⟨200844, by rfl⟩ : syracuseStep 535585 = 401689) (by norm_num)
theorem B535621 : Blo 475787 535621 := bbase (se 4 (by rfl) ⟨50214, by rfl⟩ : syracuseStep 535621 = 100429) (by norm_num)
theorem B535657 : Blo 475787 535657 := bbase (se 2 (by rfl) ⟨200871, by rfl⟩ : syracuseStep 535657 = 401743) (by norm_num)
theorem B1617029 : Blo 475787 1617029 := bbase (se 4 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 1617029 = 303193) (by norm_num)
theorem B535693 : Blo 475787 535693 := bbase (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) (by norm_num)
theorem B765101 : Blo 475787 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B535729 : Blo 475787 535729 := bbase (se 2 (by rfl) ⟨200898, by rfl⟩ : syracuseStep 535729 = 401797) (by norm_num)
theorem B535765 : Blo 475787 535765 := bbase (se 7 (by rfl) ⟨6278, by rfl⟩ : syracuseStep 535765 = 12557) (by norm_num)
theorem B863477 : Blo 475787 863477 := bbase (se 5 (by rfl) ⟨40475, by rfl⟩ : syracuseStep 863477 = 80951) (by norm_num)
theorem B535801 : Blo 475787 535801 := bbase (se 2 (by rfl) ⟨200925, by rfl⟩ : syracuseStep 535801 = 401851) (by norm_num)
theorem B535837 : Blo 475787 535837 := bbase (se 3 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 535837 = 200939) (by norm_num)
theorem B535873 : Blo 475787 535873 := bbase (se 2 (by rfl) ⟨200952, by rfl⟩ : syracuseStep 535873 = 401905) (by norm_num)
theorem B1715525 : Blo 475787 1715525 := bbase (se 4 (by rfl) ⟨160830, by rfl⟩ : syracuseStep 1715525 = 321661) (by norm_num)
theorem B535909 : Blo 475787 535909 := bbase (se 4 (by rfl) ⟨50241, by rfl⟩ : syracuseStep 535909 = 100483) (by norm_num)
theorem B535945 : Blo 475787 535945 := bbase (se 2 (by rfl) ⟨200979, by rfl⟩ : syracuseStep 535945 = 401959) (by norm_num)
theorem B765325 : Blo 475787 765325 := bbase (se 3 (by rfl) ⟨143498, by rfl⟩ : syracuseStep 765325 = 286997) (by norm_num)
theorem B535981 : Blo 475787 535981 := bbase (se 3 (by rfl) ⟨100496, by rfl⟩ : syracuseStep 535981 = 200993) (by norm_num)
theorem B536017 : Blo 475787 536017 := bbase (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) (by norm_num)
theorem B536053 : Blo 475787 536053 := bbase (se 5 (by rfl) ⟨25127, by rfl⟩ : syracuseStep 536053 = 50255) (by norm_num)
theorem B536089 : Blo 475787 536089 := bbase (se 2 (by rfl) ⟨201033, by rfl⟩ : syracuseStep 536089 = 402067) (by norm_num)
theorem B1617461 : Blo 475787 1617461 := bbase (se 5 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 1617461 = 151637) (by norm_num)
theorem B536125 : Blo 475787 536125 := bbase (se 3 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 536125 = 201047) (by norm_num)
theorem B536161 : Blo 475787 536161 := bbase (se 2 (by rfl) ⟨201060, by rfl⟩ : syracuseStep 536161 = 402121) (by norm_num)
theorem B536197 : Blo 475787 536197 := bbase (se 4 (by rfl) ⟨50268, by rfl⟩ : syracuseStep 536197 = 100537) (by norm_num)
theorem B1748645 : Blo 475787 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B536233 : Blo 475787 536233 := bbase (se 2 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 536233 = 402175) (by norm_num)
theorem B536269 : Blo 475787 536269 := bbase (se 3 (by rfl) ⟨100550, by rfl⟩ : syracuseStep 536269 = 201101) (by norm_num)
theorem B1093349 : Blo 475787 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B536305 : Blo 475787 536305 := bbase (se 2 (by rfl) ⟨201114, by rfl⟩ : syracuseStep 536305 = 402229) (by norm_num)
theorem B536341 : Blo 475787 536341 := bbase (se 6 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 536341 = 25141) (by norm_num)
theorem B3059477 : Blo 475787 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B536377 : Blo 475787 536377 := bbase (se 2 (by rfl) ⟨201141, by rfl⟩ : syracuseStep 536377 = 402283) (by norm_num)
theorem B536413 : Blo 475787 536413 := bbase (se 3 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 536413 = 201155) (by norm_num)
theorem B4665205 : Blo 475787 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B536449 : Blo 475787 536449 := bbase (se 2 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 536449 = 402337) (by norm_num)
theorem B536485 : Blo 475787 536485 := bbase (se 4 (by rfl) ⟨50295, by rfl⟩ : syracuseStep 536485 = 100591) (by norm_num)
theorem B536521 : Blo 475787 536521 := bbase (se 2 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 536521 = 402391) (by norm_num)
theorem B1617893 : Blo 475787 1617893 := bbase (se 4 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 1617893 = 303355) (by norm_num)
theorem B536557 : Blo 475787 536557 := bbase (se 3 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 536557 = 201209) (by norm_num)
theorem B536593 : Blo 475787 536593 := bbase (se 2 (by rfl) ⟨201222, by rfl⟩ : syracuseStep 536593 = 402445) (by norm_num)
theorem B536629 : Blo 475787 536629 := bbase (se 5 (by rfl) ⟨25154, by rfl⟩ : syracuseStep 536629 = 50309) (by norm_num)
theorem B536665 : Blo 475787 536665 := bbase (se 2 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 536665 = 402499) (by norm_num)
theorem B536701 : Blo 475787 536701 := bbase (se 3 (by rfl) ⟨100631, by rfl⟩ : syracuseStep 536701 = 201263) (by norm_num)
theorem B602245 : Blo 475787 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B536737 : Blo 475787 536737 := bbase (se 2 (by rfl) ⟨201276, by rfl⟩ : syracuseStep 536737 = 402553) (by norm_num)
theorem B536773 : Blo 475787 536773 := bbase (se 4 (by rfl) ⟨50322, by rfl⟩ : syracuseStep 536773 = 100645) (by norm_num)
theorem B1061093 : Blo 475787 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B536809 : Blo 475787 536809 := bbase (se 2 (by rfl) ⟨201303, by rfl⟩ : syracuseStep 536809 = 402607) (by norm_num)
theorem B536845 : Blo 475787 536845 := bbase (se 3 (by rfl) ⟨100658, by rfl⟩ : syracuseStep 536845 = 201317) (by norm_num)
theorem B1093933 : Blo 475787 1093933 := bbase (se 3 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 1093933 = 410225) (by norm_num)
theorem B602417 : Blo 475787 602417 := bbase (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) (by norm_num)
theorem B536881 : Blo 475787 536881 := bbase (se 2 (by rfl) ⟨201330, by rfl⟩ : syracuseStep 536881 = 402661) (by norm_num)
theorem B536917 : Blo 475787 536917 := bbase (se 10 (by rfl) ⟨786, by rfl⟩ : syracuseStep 536917 = 1573) (by norm_num)
theorem B602473 : Blo 475787 602473 := bbase (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) (by norm_num)
theorem B536953 : Blo 475787 536953 := bbase (se 2 (by rfl) ⟨201357, by rfl⟩ : syracuseStep 536953 = 402715) (by norm_num)
theorem B1618325 : Blo 475787 1618325 := bbase (se 6 (by rfl) ⟨37929, by rfl⟩ : syracuseStep 1618325 = 75859) (by norm_num)
theorem B536989 : Blo 475787 536989 := bbase (se 3 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 536989 = 201371) (by norm_num)
theorem B537025 : Blo 475787 537025 := bbase (se 2 (by rfl) ⟨201384, by rfl⟩ : syracuseStep 537025 = 402769) (by norm_num)
theorem B1716677 : Blo 475787 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B602569 : Blo 475787 602569 := bbase (se 2 (by rfl) ⟨225963, by rfl⟩ : syracuseStep 602569 = 451927) (by norm_num)
theorem B537061 : Blo 475787 537061 := bbase (se 4 (by rfl) ⟨50349, by rfl⟩ : syracuseStep 537061 = 100699) (by norm_num)
theorem B4076021 : Blo 475787 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B537097 : Blo 475787 537097 := bbase (se 2 (by rfl) ⟨201411, by rfl⟩ : syracuseStep 537097 = 402823) (by norm_num)
theorem B537133 : Blo 475787 537133 := bbase (se 3 (by rfl) ⟨100712, by rfl⟩ : syracuseStep 537133 = 201425) (by norm_num)
theorem B733765 : Blo 475787 733765 := bbase (se 4 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 733765 = 137581) (by norm_num)
theorem B537169 : Blo 475787 537169 := bbase (se 2 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 537169 = 402877) (by norm_num)
theorem B9810517 : Blo 475787 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B602741 : Blo 475787 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B537205 : Blo 475787 537205 := bbase (se 5 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 537205 = 50363) (by norm_num)
theorem B537241 : Blo 475787 537241 := bbase (se 2 (by rfl) ⟨201465, by rfl⟩ : syracuseStep 537241 = 402931) (by norm_num)
theorem B602797 : Blo 475787 602797 := bbase (se 3 (by rfl) ⟨113024, by rfl⟩ : syracuseStep 602797 = 226049) (by norm_num)
theorem B537277 : Blo 475787 537277 := bbase (se 3 (by rfl) ⟨100739, by rfl⟩ : syracuseStep 537277 = 201479) (by norm_num)
theorem B537313 : Blo 475787 537313 := bbase (se 2 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 537313 = 402985) (by norm_num)
theorem B1356533 : Blo 475787 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B537349 : Blo 475787 537349 := bbase (se 4 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 537349 = 100753) (by norm_num)
theorem B602893 : Blo 475787 602893 := bbase (se 3 (by rfl) ⟨113042, by rfl⟩ : syracuseStep 602893 = 226085) (by norm_num)
theorem B1815317 : Blo 475787 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B766741 : Blo 475787 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B2044709 : Blo 475787 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B537385 : Blo 475787 537385 := bbase (se 2 (by rfl) ⟨201519, by rfl⟩ : syracuseStep 537385 = 403039) (by norm_num)
theorem B1618757 : Blo 475787 1618757 := bbase (se 4 (by rfl) ⟨151758, by rfl⟩ : syracuseStep 1618757 = 303517) (by norm_num)
theorem B537421 : Blo 475787 537421 := bbase (se 3 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 537421 = 201533) (by norm_num)
theorem B537457 : Blo 475787 537457 := bbase (se 2 (by rfl) ⟨201546, by rfl⟩ : syracuseStep 537457 = 403093) (by norm_num)
theorem B537493 : Blo 475787 537493 := bbase (se 6 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 537493 = 25195) (by norm_num)
theorem B603065 : Blo 475787 603065 := bbase (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) (by norm_num)
theorem B537529 : Blo 475787 537529 := bbase (se 2 (by rfl) ⟨201573, by rfl⟩ : syracuseStep 537529 = 403147) (by norm_num)
theorem B3683285 : Blo 475787 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B537565 : Blo 475787 537565 := bbase (se 3 (by rfl) ⟨100793, by rfl⟩ : syracuseStep 537565 = 201587) (by norm_num)
theorem B603121 : Blo 475787 603121 := bbase (se 2 (by rfl) ⟨226170, by rfl⟩ : syracuseStep 603121 = 452341) (by norm_num)
theorem B537601 : Blo 475787 537601 := bbase (se 2 (by rfl) ⟨201600, by rfl⟩ : syracuseStep 537601 = 403201) (by norm_num)
theorem B766997 : Blo 475787 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B537637 : Blo 475787 537637 := bbase (se 4 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 537637 = 100807) (by norm_num)
theorem B1815605 : Blo 475787 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B537673 : Blo 475787 537673 := bbase (se 2 (by rfl) ⟨201627, by rfl⟩ : syracuseStep 537673 = 403255) (by norm_num)
theorem B603217 : Blo 475787 603217 := bbase (se 2 (by rfl) ⟨226206, by rfl⟩ : syracuseStep 603217 = 452413) (by norm_num)
theorem B537709 : Blo 475787 537709 := bbase (se 3 (by rfl) ⟨100820, by rfl⟩ : syracuseStep 537709 = 201641) (by norm_num)
theorem B537745 : Blo 475787 537745 := bbase (se 2 (by rfl) ⟨201654, by rfl⟩ : syracuseStep 537745 = 403309) (by norm_num)
theorem B537781 : Blo 475787 537781 := bbase (se 5 (by rfl) ⟨25208, by rfl⟩ : syracuseStep 537781 = 50417) (by norm_num)
theorem B767189 : Blo 475787 767189 := bbase (se 7 (by rfl) ⟨8990, by rfl⟩ : syracuseStep 767189 = 17981) (by norm_num)
theorem B537817 : Blo 475787 537817 := bbase (se 2 (by rfl) ⟨201681, by rfl⟩ : syracuseStep 537817 = 403363) (by norm_num)
theorem B1619189 : Blo 475787 1619189 := bbase (se 5 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 1619189 = 151799) (by norm_num)
theorem B603389 : Blo 475787 603389 := bbase (se 3 (by rfl) ⟨113135, by rfl⟩ : syracuseStep 603389 = 226271) (by norm_num)
theorem B537853 : Blo 475787 537853 := bbase (se 3 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 537853 = 201695) (by norm_num)
theorem B537889 : Blo 475787 537889 := bbase (se 2 (by rfl) ⟨201708, by rfl⟩ : syracuseStep 537889 = 403417) (by norm_num)
theorem B603445 : Blo 475787 603445 := bbase (se 5 (by rfl) ⟨28286, by rfl⟩ : syracuseStep 603445 = 56573) (by norm_num)
theorem B537925 : Blo 475787 537925 := bbase (se 4 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 537925 = 100861) (by norm_num)
theorem B537961 : Blo 475787 537961 := bbase (se 2 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 537961 = 403471) (by norm_num)
theorem B537997 : Blo 475787 537997 := bbase (se 3 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 537997 = 201749) (by norm_num)
theorem B603541 : Blo 475787 603541 := bbase (se 6 (by rfl) ⟨14145, by rfl⟩ : syracuseStep 603541 = 28291) (by norm_num)
theorem B538033 : Blo 475787 538033 := bbase (se 2 (by rfl) ⟨201762, by rfl⟩ : syracuseStep 538033 = 403525) (by norm_num)
theorem B538069 : Blo 475787 538069 := bbase (se 7 (by rfl) ⟨6305, by rfl⟩ : syracuseStep 538069 = 12611) (by norm_num)
theorem B538105 : Blo 475787 538105 := bbase (se 2 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 538105 = 403579) (by norm_num)
theorem B538141 : Blo 475787 538141 := bbase (se 3 (by rfl) ⟨100901, by rfl⟩ : syracuseStep 538141 = 201803) (by norm_num)
theorem B1226285 : Blo 475787 1226285 := bbase (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) (by norm_num)
theorem B603713 : Blo 475787 603713 := bbase (se 2 (by rfl) ⟨226392, by rfl⟩ : syracuseStep 603713 = 452785) (by norm_num)
theorem B538177 : Blo 475787 538177 := bbase (se 2 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 538177 = 403633) (by norm_num)
theorem B538213 : Blo 475787 538213 := bbase (se 4 (by rfl) ⟨50457, by rfl⟩ : syracuseStep 538213 = 100915) (by norm_num)
theorem B603769 : Blo 475787 603769 := bbase (se 2 (by rfl) ⟨226413, by rfl⟩ : syracuseStep 603769 = 452827) (by norm_num)
theorem B538249 : Blo 475787 538249 := bbase (se 2 (by rfl) ⟨201843, by rfl⟩ : syracuseStep 538249 = 403687) (by norm_num)
theorem B538285 : Blo 475787 538285 := bbase (se 3 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 538285 = 201857) (by norm_num)
theorem B1717957 : Blo 475787 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B538321 : Blo 475787 538321 := bbase (se 2 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 538321 = 403741) (by norm_num)
theorem B603865 : Blo 475787 603865 := bbase (se 2 (by rfl) ⟨226449, by rfl⟩ : syracuseStep 603865 = 452899) (by norm_num)
theorem B538357 : Blo 475787 538357 := bbase (se 5 (by rfl) ⟨25235, by rfl⟩ : syracuseStep 538357 = 50471) (by norm_num)
theorem B538393 : Blo 475787 538393 := bbase (se 2 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 538393 = 403795) (by norm_num)
theorem B538429 : Blo 475787 538429 := bbase (se 3 (by rfl) ⟨100955, by rfl⟩ : syracuseStep 538429 = 201911) (by norm_num)
theorem B538465 : Blo 475787 538465 := bbase (se 2 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 538465 = 403849) (by norm_num)
theorem B604037 : Blo 475787 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B538501 : Blo 475787 538501 := bbase (se 4 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 538501 = 100969) (by norm_num)
theorem B1357717 : Blo 475787 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B538537 : Blo 475787 538537 := bbase (se 2 (by rfl) ⟨201951, by rfl⟩ : syracuseStep 538537 = 403903) (by norm_num)
theorem B604093 : Blo 475787 604093 := bbase (se 3 (by rfl) ⟨113267, by rfl⟩ : syracuseStep 604093 = 226535) (by norm_num)
theorem B538573 : Blo 475787 538573 := bbase (se 3 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 538573 = 201965) (by norm_num)
theorem B538609 : Blo 475787 538609 := bbase (se 2 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 538609 = 403957) (by norm_num)
theorem B538645 : Blo 475787 538645 := bbase (se 6 (by rfl) ⟨12624, by rfl⟩ : syracuseStep 538645 = 25249) (by norm_num)
theorem B604189 : Blo 475787 604189 := bbase (se 3 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 604189 = 226571) (by norm_num)
theorem B1357877 : Blo 475787 1357877 := bbase (se 5 (by rfl) ⟨63650, by rfl⟩ : syracuseStep 1357877 = 127301) (by norm_num)
theorem B538681 : Blo 475787 538681 := bbase (se 2 (by rfl) ⟨202005, by rfl⟩ : syracuseStep 538681 = 404011) (by norm_num)
theorem B538717 : Blo 475787 538717 := bbase (se 3 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 538717 = 202019) (by norm_num)
theorem B768125 : Blo 475787 768125 := bbase (se 3 (by rfl) ⟨144023, by rfl⟩ : syracuseStep 768125 = 288047) (by norm_num)
theorem B538753 : Blo 475787 538753 := bbase (se 2 (by rfl) ⟨202032, by rfl⟩ : syracuseStep 538753 = 404065) (by norm_num)
theorem B538789 : Blo 475787 538789 := bbase (se 4 (by rfl) ⟨50511, by rfl⟩ : syracuseStep 538789 = 101023) (by norm_num)
theorem B604361 : Blo 475787 604361 := bbase (se 2 (by rfl) ⟨226635, by rfl⟩ : syracuseStep 604361 = 453271) (by norm_num)
theorem B538825 : Blo 475787 538825 := bbase (se 2 (by rfl) ⟨202059, by rfl⟩ : syracuseStep 538825 = 404119) (by norm_num)
theorem B735437 : Blo 475787 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B1816789 : Blo 475787 1816789 := bbase (se 7 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 1816789 = 42581) (by norm_num)
theorem B538861 : Blo 475787 538861 := bbase (se 3 (by rfl) ⟨101036, by rfl⟩ : syracuseStep 538861 = 202073) (by norm_num)
theorem B604417 : Blo 475787 604417 := bbase (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) (by norm_num)
theorem B538897 : Blo 475787 538897 := bbase (se 2 (by rfl) ⟨202086, by rfl⟩ : syracuseStep 538897 = 404173) (by norm_num)
theorem B1358117 : Blo 475787 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B538933 : Blo 475787 538933 := bbase (se 5 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 538933 = 50525) (by norm_num)
theorem B538969 : Blo 475787 538969 := bbase (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) (by norm_num)
theorem B604513 : Blo 475787 604513 := bbase (se 2 (by rfl) ⟨226692, by rfl⟩ : syracuseStep 604513 = 453385) (by norm_num)
theorem B539005 : Blo 475787 539005 := bbase (se 3 (by rfl) ⟨101063, by rfl⟩ : syracuseStep 539005 = 202127) (by norm_num)
theorem B539041 : Blo 475787 539041 := bbase (se 2 (by rfl) ⟨202140, by rfl⟩ : syracuseStep 539041 = 404281) (by norm_num)
theorem B571817 : Blo 475787 571817 := bbase (se 2 (by rfl) ⟨214431, by rfl⟩ : syracuseStep 571817 = 428863) (by norm_num)
theorem B539077 : Blo 475787 539077 := bbase (se 4 (by rfl) ⟨50538, by rfl⟩ : syracuseStep 539077 = 101077) (by norm_num)
theorem B5257685 : Blo 475787 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1358309 : Blo 475787 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B539113 : Blo 475787 539113 := bbase (se 2 (by rfl) ⟨202167, by rfl⟩ : syracuseStep 539113 = 404335) (by norm_num)
theorem B768509 : Blo 475787 768509 := bbase (se 3 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 768509 = 288191) (by norm_num)
theorem B1161733 : Blo 475787 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B1817093 : Blo 475787 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B604685 : Blo 475787 604685 := bbase (se 3 (by rfl) ⟨113378, by rfl⟩ : syracuseStep 604685 = 226757) (by norm_num)
theorem B539149 : Blo 475787 539149 := bbase (se 3 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 539149 = 202181) (by norm_num)
theorem B2046485 : Blo 475787 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B539185 : Blo 475787 539185 := bbase (se 2 (by rfl) ⟨202194, by rfl⟩ : syracuseStep 539185 = 404389) (by norm_num)
theorem B604741 : Blo 475787 604741 := bbase (se 4 (by rfl) ⟨56694, by rfl⟩ : syracuseStep 604741 = 113389) (by norm_num)
theorem B539221 : Blo 475787 539221 := bbase (se 8 (by rfl) ⟨3159, by rfl⟩ : syracuseStep 539221 = 6319) (by norm_num)
theorem B539257 : Blo 475787 539257 := bbase (se 2 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 539257 = 404443) (by norm_num)
theorem B539293 : Blo 475787 539293 := bbase (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) (by norm_num)
theorem B604837 : Blo 475787 604837 := bbase (se 4 (by rfl) ⟨56703, by rfl⟩ : syracuseStep 604837 = 113407) (by norm_num)
theorem B1555109 : Blo 475787 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B539329 : Blo 475787 539329 := bbase (se 2 (by rfl) ⟨202248, by rfl⟩ : syracuseStep 539329 = 404497) (by norm_num)
theorem B572125 : Blo 475787 572125 := bbase (se 3 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 572125 = 214547) (by norm_num)
theorem B539365 : Blo 475787 539365 := bbase (se 4 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 539365 = 101131) (by norm_num)
theorem B539401 : Blo 475787 539401 := bbase (se 2 (by rfl) ⟨202275, by rfl⟩ : syracuseStep 539401 = 404551) (by norm_num)
theorem B539437 : Blo 475787 539437 := bbase (se 3 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 539437 = 202289) (by norm_num)
theorem B605009 : Blo 475787 605009 := bbase (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) (by norm_num)
theorem B539473 : Blo 475787 539473 := bbase (se 2 (by rfl) ⟨202302, by rfl⟩ : syracuseStep 539473 = 404605) (by norm_num)
theorem B539509 : Blo 475787 539509 := bbase (se 5 (by rfl) ⟨25289, by rfl⟩ : syracuseStep 539509 = 50579) (by norm_num)
theorem B605065 : Blo 475787 605065 := bbase (se 2 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 605065 = 453799) (by norm_num)
theorem B539545 : Blo 475787 539545 := bbase (se 2 (by rfl) ⟨202329, by rfl⟩ : syracuseStep 539545 = 404659) (by norm_num)
theorem B572341 : Blo 475787 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B539581 : Blo 475787 539581 := bbase (se 3 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 539581 = 202343) (by norm_num)
theorem B539617 : Blo 475787 539617 := bbase (se 2 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 539617 = 404713) (by norm_num)
theorem B605161 : Blo 475787 605161 := bbase (se 2 (by rfl) ⟨226935, by rfl⟩ : syracuseStep 605161 = 453871) (by norm_num)
theorem B539653 : Blo 475787 539653 := bbase (se 4 (by rfl) ⟨50592, by rfl⟩ : syracuseStep 539653 = 101185) (by norm_num)
theorem B539689 : Blo 475787 539689 := bbase (se 2 (by rfl) ⟨202383, by rfl⟩ : syracuseStep 539689 = 404767) (by norm_num)
theorem B539725 : Blo 475787 539725 := bbase (se 3 (by rfl) ⟨101198, by rfl⟩ : syracuseStep 539725 = 202397) (by norm_num)
theorem B539761 : Blo 475787 539761 := bbase (se 2 (by rfl) ⟨202410, by rfl⟩ : syracuseStep 539761 = 404821) (by norm_num)
theorem B605333 : Blo 475787 605333 := bbase (se 6 (by rfl) ⟨14187, by rfl⟩ : syracuseStep 605333 = 28375) (by norm_num)
theorem B1293509 : Blo 475787 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B605389 : Blo 475787 605389 := bbase (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) (by norm_num)
theorem B605485 : Blo 475787 605485 := bbase (se 3 (by rfl) ⟨113528, by rfl⟩ : syracuseStep 605485 = 227057) (by norm_num)
theorem B3620213 : Blo 475787 3620213 := bbase (se 5 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 3620213 = 339395) (by norm_num)
theorem B4078997 : Blo 475787 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B1359301 : Blo 475787 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B605657 : Blo 475787 605657 := bbase (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) (by norm_num)
theorem B2047477 : Blo 475787 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B572941 : Blo 475787 572941 := bbase (se 3 (by rfl) ⟨107426, by rfl⟩ : syracuseStep 572941 = 214853) (by norm_num)
theorem B605713 : Blo 475787 605713 := bbase (se 2 (by rfl) ⟨227142, by rfl⟩ : syracuseStep 605713 = 454285) (by norm_num)
theorem B605809 : Blo 475787 605809 := bbase (se 2 (by rfl) ⟨227178, by rfl⟩ : syracuseStep 605809 = 454357) (by norm_num)
theorem B1031837 : Blo 475787 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B605981 : Blo 475787 605981 := bbase (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) (by norm_num)
theorem B606037 : Blo 475787 606037 := bbase (se 9 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 606037 = 3551) (by norm_num)
theorem B606133 : Blo 475787 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B3686485 : Blo 475787 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B606305 : Blo 475787 606305 := bbase (se 2 (by rfl) ⟨227364, by rfl⟩ : syracuseStep 606305 = 454729) (by norm_num)
theorem B606361 : Blo 475787 606361 := bbase (se 2 (by rfl) ⟨227385, by rfl⟩ : syracuseStep 606361 = 454771) (by norm_num)
theorem B802973 : Blo 475787 802973 := bbase (se 3 (by rfl) ⟨150557, by rfl⟩ : syracuseStep 802973 = 301115) (by norm_num)
theorem B606457 : Blo 475787 606457 := bbase (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) (by norm_num)
theorem B803101 : Blo 475787 803101 := bbase (se 3 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 803101 = 301163) (by norm_num)
theorem B803189 : Blo 475787 803189 := bbase (se 5 (by rfl) ⟨37649, by rfl⟩ : syracuseStep 803189 = 75299) (by norm_num)
theorem B606629 : Blo 475787 606629 := bbase (se 4 (by rfl) ⟨56871, by rfl⟩ : syracuseStep 606629 = 113743) (by norm_num)
theorem B5816789 : Blo 475787 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B606685 : Blo 475787 606685 := bbase (se 3 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 606685 = 227507) (by norm_num)
theorem B803317 : Blo 475787 803317 := bbase (se 5 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 803317 = 75311) (by norm_num)
theorem B1360405 : Blo 475787 1360405 := bbase (se 6 (by rfl) ⟨31884, by rfl⟩ : syracuseStep 1360405 = 63769) (by norm_num)
theorem B606781 : Blo 475787 606781 := bbase (se 3 (by rfl) ⟨113771, by rfl⟩ : syracuseStep 606781 = 227543) (by norm_num)
theorem B1819205 : Blo 475787 1819205 := bbase (se 4 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 1819205 = 341101) (by norm_num)
theorem B803405 : Blo 475787 803405 := bbase (se 3 (by rfl) ⟨150638, by rfl⟩ : syracuseStep 803405 = 301277) (by norm_num)
theorem B1458773 : Blo 475787 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B508529 : Blo 475787 508529 := bbase (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) (by norm_num)
theorem B574085 : Blo 475787 574085 := bbase (se 4 (by rfl) ⟨53820, by rfl⟩ : syracuseStep 574085 = 107641) (by norm_num)
theorem B574133 : Blo 475787 574133 := bbase (se 5 (by rfl) ⟨26912, by rfl⟩ : syracuseStep 574133 = 53825) (by norm_num)
theorem B803533 : Blo 475787 803533 := bbase (se 3 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 803533 = 301325) (by norm_num)
theorem B606953 : Blo 475787 606953 := bbase (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) (by norm_num)
theorem B574229 : Blo 475787 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B607009 : Blo 475787 607009 := bbase (se 2 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 607009 = 455257) (by norm_num)
theorem B803621 : Blo 475787 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B508717 : Blo 475787 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B1819493 : Blo 475787 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B607105 : Blo 475787 607105 := bbase (se 2 (by rfl) ⟨227664, by rfl⟩ : syracuseStep 607105 = 455329) (by norm_num)
theorem B934789 : Blo 475787 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B803749 : Blo 475787 803749 := bbase (se 4 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 803749 = 150703) (by norm_num)
theorem B574393 : Blo 475787 574393 := bbase (se 2 (by rfl) ⟨215397, by rfl⟩ : syracuseStep 574393 = 430795) (by norm_num)
theorem B15516629 : Blo 475787 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B803837 : Blo 475787 803837 := bbase (se 3 (by rfl) ⟨150719, by rfl⟩ : syracuseStep 803837 = 301439) (by norm_num)
theorem B803965 : Blo 475787 803965 := bbase (se 3 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 803965 = 301487) (by norm_num)
theorem B574609 : Blo 475787 574609 := bbase (se 2 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 574609 = 430957) (by norm_num)
theorem B2802869 : Blo 475787 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B804053 : Blo 475787 804053 := bbase (se 7 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 804053 = 18845) (by norm_num)
theorem B2442469 : Blo 475787 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B967909 : Blo 475787 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B2409749 : Blo 475787 2409749 := bbase (se 6 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 2409749 = 112957) (by norm_num)
theorem B574777 : Blo 475787 574777 := bbase (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) (by norm_num)
theorem B804181 : Blo 475787 804181 := bbase (se 12 (by rfl) ⟨294, by rfl⟩ : syracuseStep 804181 = 589) (by norm_num)
theorem B804269 : Blo 475787 804269 := bbase (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) (by norm_num)
theorem B2180645 : Blo 475787 2180645 := bbase (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) (by norm_num)
theorem B1295909 : Blo 475787 1295909 := bbase (se 4 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 1295909 = 242983) (by norm_num)
theorem B804397 : Blo 475787 804397 := bbase (se 3 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 804397 = 301649) (by norm_num)
theorem B2475605 : Blo 475787 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B509537 : Blo 475787 509537 := bbase (se 2 (by rfl) ⟨191076, by rfl⟩ : syracuseStep 509537 = 382153) (by norm_num)
theorem B804485 : Blo 475787 804485 := bbase (se 4 (by rfl) ⟨75420, by rfl⟩ : syracuseStep 804485 = 150841) (by norm_num)
theorem B1296037 : Blo 475787 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1722053 : Blo 475787 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B804613 : Blo 475787 804613 := bbase (se 4 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 804613 = 150865) (by norm_num)
theorem B575305 : Blo 475787 575305 := bbase (se 2 (by rfl) ⟨215739, by rfl⟩ : syracuseStep 575305 = 431479) (by norm_num)
theorem B804701 : Blo 475787 804701 := bbase (se 3 (by rfl) ⟨150881, by rfl⟩ : syracuseStep 804701 = 301763) (by norm_num)
theorem B804829 : Blo 475787 804829 := bbase (se 3 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 804829 = 301811) (by norm_num)
theorem B1361909 : Blo 475787 1361909 := bbase (se 5 (by rfl) ⟨63839, by rfl⟩ : syracuseStep 1361909 = 127679) (by norm_num)
theorem B1820677 : Blo 475787 1820677 := bbase (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) (by norm_num)
theorem B509981 : Blo 475787 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B804917 : Blo 475787 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B1722485 : Blo 475787 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1230997 : Blo 475787 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B805045 : Blo 475787 805045 := bbase (se 5 (by rfl) ⟨37736, by rfl⟩ : syracuseStep 805045 = 75473) (by norm_num)
theorem B706765 : Blo 475787 706765 := bbase (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) (by norm_num)
theorem B542953 : Blo 475787 542953 := bbase (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) (by norm_num)
theorem B903413 : Blo 475787 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B805133 : Blo 475787 805133 := bbase (se 3 (by rfl) ⟨150962, by rfl⟩ : syracuseStep 805133 = 301925) (by norm_num)
theorem B510229 : Blo 475787 510229 := bbase (se 6 (by rfl) ⟨11958, by rfl⟩ : syracuseStep 510229 = 23917) (by norm_num)
theorem B1820981 : Blo 475787 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B969077 : Blo 475787 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B903565 : Blo 475787 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B805261 : Blo 475787 805261 := bbase (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) (by norm_num)
theorem B805349 : Blo 475787 805349 := bbase (se 4 (by rfl) ⟨75501, by rfl⟩ : syracuseStep 805349 = 151003) (by norm_num)
theorem B4573685 : Blo 475787 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B2411045 : Blo 475787 2411045 := bbase (se 4 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 2411045 = 452071) (by norm_num)
theorem B543313 : Blo 475787 543313 := bbase (se 2 (by rfl) ⟨203742, by rfl⟩ : syracuseStep 543313 = 407485) (by norm_num)
theorem B805477 : Blo 475787 805477 := bbase (se 4 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 805477 = 151027) (by norm_num)
theorem B903869 : Blo 475787 903869 := bbase (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) (by norm_num)
theorem B805565 : Blo 475787 805565 := bbase (se 3 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 805565 = 302087) (by norm_num)
theorem B510661 : Blo 475787 510661 := bbase (se 4 (by rfl) ⟨47874, by rfl⟩ : syracuseStep 510661 = 95749) (by norm_num)
theorem B1526485 : Blo 475787 1526485 := bbase (se 7 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 1526485 = 35777) (by norm_num)
theorem B510733 : Blo 475787 510733 := bbase (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) (by norm_num)
theorem B6146837 : Blo 475787 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B805693 : Blo 475787 805693 := bbase (se 3 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 805693 = 302135) (by norm_num)
theorem B805781 : Blo 475787 805781 := bbase (se 6 (by rfl) ⟨18885, by rfl⟩ : syracuseStep 805781 = 37771) (by norm_num)
theorem B4606901 : Blo 475787 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B805909 : Blo 475787 805909 := bbase (se 6 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 805909 = 37777) (by norm_num)
theorem B707621 : Blo 475787 707621 := bbase (se 4 (by rfl) ⟨66339, by rfl⟩ : syracuseStep 707621 = 132679) (by norm_num)
theorem B805997 : Blo 475787 805997 := bbase (se 3 (by rfl) ⟨151124, by rfl⟩ : syracuseStep 805997 = 302249) (by norm_num)
theorem B511105 : Blo 475787 511105 := bbase (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) (by norm_num)
theorem B806125 : Blo 475787 806125 := bbase (se 3 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 806125 = 302297) (by norm_num)
theorem B806213 : Blo 475787 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B1035605 : Blo 475787 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B2477461 : Blo 475787 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B904621 : Blo 475787 904621 := bbase (se 3 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 904621 = 339233) (by norm_num)
theorem B806341 : Blo 475787 806341 := bbase (se 4 (by rfl) ⟨75594, by rfl⟩ : syracuseStep 806341 = 151189) (by norm_num)
theorem B511481 : Blo 475787 511481 := bbase (se 2 (by rfl) ⟨191805, by rfl⟩ : syracuseStep 511481 = 383611) (by norm_num)
theorem B806429 : Blo 475787 806429 := bbase (se 3 (by rfl) ⟨151205, by rfl⟩ : syracuseStep 806429 = 302411) (by norm_num)
theorem B1363493 : Blo 475787 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B904765 : Blo 475787 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B511553 : Blo 475787 511553 := bbase (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) (by norm_num)
theorem B970309 : Blo 475787 970309 := bbase (se 4 (by rfl) ⟨90966, by rfl⟩ : syracuseStep 970309 = 181933) (by norm_num)
theorem B806557 : Blo 475787 806557 := bbase (se 3 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 806557 = 302459) (by norm_num)
theorem B904925 : Blo 475787 904925 := bbase (se 3 (by rfl) ⟨169673, by rfl⟩ : syracuseStep 904925 = 339347) (by norm_num)
theorem B806645 : Blo 475787 806645 := bbase (se 5 (by rfl) ⟨37811, by rfl⟩ : syracuseStep 806645 = 75623) (by norm_num)
theorem B511741 : Blo 475787 511741 := bbase (se 3 (by rfl) ⟨95951, by rfl⟩ : syracuseStep 511741 = 191903) (by norm_num)
theorem B2412341 : Blo 475787 2412341 := bbase (se 5 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 2412341 = 226157) (by norm_num)
theorem B905069 : Blo 475787 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B2576245 : Blo 475787 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B806773 : Blo 475787 806773 := bbase (se 5 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 806773 = 75635) (by norm_num)
theorem B511925 : Blo 475787 511925 := bbase (se 5 (by rfl) ⟨23996, by rfl⟩ : syracuseStep 511925 = 47993) (by norm_num)
theorem B806861 : Blo 475787 806861 := bbase (se 3 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 806861 = 302573) (by norm_num)
theorem B806989 : Blo 475787 806989 := bbase (se 3 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 806989 = 302621) (by norm_num)
theorem B905357 : Blo 475787 905357 := bbase (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) (by norm_num)
theorem B774293 : Blo 475787 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B807077 : Blo 475787 807077 := bbase (se 4 (by rfl) ⟨75663, by rfl⟩ : syracuseStep 807077 = 151327) (by norm_num)
theorem B1364165 : Blo 475787 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B905509 : Blo 475787 905509 := bbase (se 4 (by rfl) ⟨84891, by rfl⟩ : syracuseStep 905509 = 169783) (by norm_num)
theorem B807205 : Blo 475787 807205 := bbase (se 4 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 807205 = 151351) (by norm_num)
theorem B807293 : Blo 475787 807293 := bbase (se 3 (by rfl) ⟨151367, by rfl⟩ : syracuseStep 807293 = 302735) (by norm_num)
theorem B807421 : Blo 475787 807421 := bbase (se 3 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 807421 = 302783) (by norm_num)
theorem B1167949 : Blo 475787 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B905813 : Blo 475787 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B807509 : Blo 475787 807509 := bbase (se 8 (by rfl) ⟨4731, by rfl⟩ : syracuseStep 807509 = 9463) (by norm_num)
theorem B971365 : Blo 475787 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B1364597 : Blo 475787 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B807637 : Blo 475787 807637 := bbase (se 7 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 807637 = 18929) (by norm_num)
theorem B807725 : Blo 475787 807725 := bbase (se 3 (by rfl) ⟨151448, by rfl⟩ : syracuseStep 807725 = 302897) (by norm_num)
theorem B709517 : Blo 475787 709517 := bbase (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) (by norm_num)
theorem B807853 : Blo 475787 807853 := bbase (se 3 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 807853 = 302945) (by norm_num)
theorem B1168357 : Blo 475787 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B807941 : Blo 475787 807941 := bbase (se 4 (by rfl) ⟨75744, by rfl⟩ : syracuseStep 807941 = 151489) (by norm_num)
theorem B2413637 : Blo 475787 2413637 := bbase (se 4 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 2413637 = 452557) (by norm_num)
theorem B644213 : Blo 475787 644213 := bbase (se 5 (by rfl) ⟨30197, by rfl⟩ : syracuseStep 644213 = 60395) (by norm_num)
theorem B808069 : Blo 475787 808069 := bbase (se 4 (by rfl) ⟨75756, by rfl⟩ : syracuseStep 808069 = 151513) (by norm_num)
theorem B545945 : Blo 475787 545945 := bbase (se 2 (by rfl) ⟨204729, by rfl⟩ : syracuseStep 545945 = 409459) (by norm_num)
theorem B808157 : Blo 475787 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B2446613 : Blo 475787 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B906565 : Blo 475787 906565 := bbase (se 4 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 906565 = 169981) (by norm_num)
theorem B808285 : Blo 475787 808285 := bbase (se 3 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 808285 = 303107) (by norm_num)
theorem B1365349 : Blo 475787 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B808373 : Blo 475787 808373 := bbase (se 5 (by rfl) ⟨37892, by rfl⟩ : syracuseStep 808373 = 75785) (by norm_num)
theorem B1070549 : Blo 475787 1070549 := bbase (se 7 (by rfl) ⟨12545, by rfl⟩ : syracuseStep 1070549 = 25091) (by norm_num)
theorem B906709 : Blo 475787 906709 := bbase (se 7 (by rfl) ⟨10625, by rfl⟩ : syracuseStep 906709 = 21251) (by norm_num)
theorem B1070621 : Blo 475787 1070621 := bbase (se 3 (by rfl) ⟨200741, by rfl⟩ : syracuseStep 1070621 = 401483) (by norm_num)
theorem B1529381 : Blo 475787 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B808501 : Blo 475787 808501 := bbase (se 5 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 808501 = 75797) (by norm_num)
theorem B1070693 : Blo 475787 1070693 := bbase (se 4 (by rfl) ⟨100377, by rfl⟩ : syracuseStep 1070693 = 200755) (by norm_num)
theorem B906869 : Blo 475787 906869 := bbase (se 5 (by rfl) ⟨42509, by rfl⟩ : syracuseStep 906869 = 85019) (by norm_num)
theorem B808589 : Blo 475787 808589 := bbase (se 3 (by rfl) ⟨151610, by rfl⟩ : syracuseStep 808589 = 303221) (by norm_num)
theorem B611993 : Blo 475787 611993 := bbase (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) (by norm_num)
theorem B1070765 : Blo 475787 1070765 := bbase (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) (by norm_num)
theorem B874165 : Blo 475787 874165 := bbase (se 5 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 874165 = 81953) (by norm_num)
theorem B644797 : Blo 475787 644797 := bbase (se 3 (by rfl) ⟨120899, by rfl⟩ : syracuseStep 644797 = 241799) (by norm_num)
theorem B1038037 : Blo 475787 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B1070837 : Blo 475787 1070837 := bbase (se 5 (by rfl) ⟨50195, by rfl⟩ : syracuseStep 1070837 = 100391) (by norm_num)
theorem B907013 : Blo 475787 907013 := bbase (se 4 (by rfl) ⟨85032, by rfl⟩ : syracuseStep 907013 = 170065) (by norm_num)
theorem B808717 : Blo 475787 808717 := bbase (se 3 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 808717 = 303269) (by norm_num)
theorem B1070909 : Blo 475787 1070909 := bbase (se 3 (by rfl) ⟨200795, by rfl⟩ : syracuseStep 1070909 = 401591) (by norm_num)
theorem B808805 : Blo 475787 808805 := bbase (se 4 (by rfl) ⟨75825, by rfl⟩ : syracuseStep 808805 = 151651) (by norm_num)
theorem B1070981 : Blo 475787 1070981 := bbase (se 4 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 1070981 = 200809) (by norm_num)
theorem B677765 : Blo 475787 677765 := bbase (se 4 (by rfl) ⟨63540, by rfl⟩ : syracuseStep 677765 = 127081) (by norm_num)
theorem B645013 : Blo 475787 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B1071053 : Blo 475787 1071053 := bbase (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) (by norm_num)
theorem B677845 : Blo 475787 677845 := bbase (se 7 (by rfl) ⟨7943, by rfl⟩ : syracuseStep 677845 = 15887) (by norm_num)
theorem B7722965 : Blo 475787 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B808933 : Blo 475787 808933 := bbase (se 4 (by rfl) ⟨75837, by rfl⟩ : syracuseStep 808933 = 151675) (by norm_num)
theorem B546817 : Blo 475787 546817 := bbase (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) (by norm_num)
theorem B1071125 : Blo 475787 1071125 := bbase (se 6 (by rfl) ⟨25104, by rfl⟩ : syracuseStep 1071125 = 50209) (by norm_num)
theorem B907301 : Blo 475787 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B809021 : Blo 475787 809021 := bbase (se 3 (by rfl) ⟨151691, by rfl⟩ : syracuseStep 809021 = 303383) (by norm_num)
theorem B677965 : Blo 475787 677965 := bbase (se 3 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 677965 = 254237) (by norm_num)
theorem B1071197 : Blo 475787 1071197 := bbase (se 3 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 1071197 = 401699) (by norm_num)
theorem B1071269 : Blo 475787 1071269 := bbase (se 4 (by rfl) ⟨100431, by rfl⟩ : syracuseStep 1071269 = 200863) (by norm_num)
theorem B678061 : Blo 475787 678061 := bbase (se 3 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 678061 = 254273) (by norm_num)
theorem B907453 : Blo 475787 907453 := bbase (se 3 (by rfl) ⟨170147, by rfl⟩ : syracuseStep 907453 = 340295) (by norm_num)
theorem B809149 : Blo 475787 809149 := bbase (se 3 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 809149 = 303431) (by norm_num)
theorem B1071341 : Blo 475787 1071341 := bbase (se 3 (by rfl) ⟨200876, by rfl⟩ : syracuseStep 1071341 = 401753) (by norm_num)
theorem B809237 : Blo 475787 809237 := bbase (se 6 (by rfl) ⟨18966, by rfl⟩ : syracuseStep 809237 = 37933) (by norm_num)
theorem B645413 : Blo 475787 645413 := bbase (se 4 (by rfl) ⟨60507, by rfl⟩ : syracuseStep 645413 = 121015) (by norm_num)
theorem B1071413 : Blo 475787 1071413 := bbase (se 5 (by rfl) ⟨50222, by rfl⟩ : syracuseStep 1071413 = 100445) (by norm_num)
theorem B2414933 : Blo 475787 2414933 := bbase (se 10 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 2414933 = 7075) (by norm_num)
theorem B1071485 : Blo 475787 1071485 := bbase (se 3 (by rfl) ⟨200903, by rfl⟩ : syracuseStep 1071485 = 401807) (by norm_num)
theorem B7756181 : Blo 475787 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B809365 : Blo 475787 809365 := bbase (se 6 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 809365 = 37939) (by norm_num)
theorem B612793 : Blo 475787 612793 := bbase (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) (by norm_num)
theorem B1071557 : Blo 475787 1071557 := bbase (se 4 (by rfl) ⟨100458, by rfl⟩ : syracuseStep 1071557 = 200917) (by norm_num)
theorem B907757 : Blo 475787 907757 := bbase (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) (by norm_num)
theorem B809453 : Blo 475787 809453 := bbase (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) (by norm_num)
theorem B1071629 : Blo 475787 1071629 := bbase (se 3 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 1071629 = 401861) (by norm_num)
theorem B1071701 : Blo 475787 1071701 := bbase (se 8 (by rfl) ⟨6279, by rfl⟩ : syracuseStep 1071701 = 12559) (by norm_num)
theorem B809581 : Blo 475787 809581 := bbase (se 3 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 809581 = 303593) (by norm_num)
theorem B1071773 : Blo 475787 1071773 := bbase (se 3 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 1071773 = 401915) (by norm_num)
theorem B678557 : Blo 475787 678557 := bbase (se 3 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 678557 = 254459) (by norm_num)
theorem B1071845 : Blo 475787 1071845 := bbase (se 4 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 1071845 = 200971) (by norm_num)
theorem B1071917 : Blo 475787 1071917 := bbase (se 3 (by rfl) ⟨200984, by rfl⟩ : syracuseStep 1071917 = 401969) (by norm_num)
theorem B1071989 : Blo 475787 1071989 := bbase (se 5 (by rfl) ⟨50249, by rfl⟩ : syracuseStep 1071989 = 100499) (by norm_num)
theorem B1072061 : Blo 475787 1072061 := bbase (se 3 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 1072061 = 402023) (by norm_num)
theorem B3627989 : Blo 475787 3627989 := bbase (se 7 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 3627989 = 85031) (by norm_num)
theorem B1072133 : Blo 475787 1072133 := bbase (se 4 (by rfl) ⟨100512, by rfl⟩ : syracuseStep 1072133 = 201025) (by norm_num)
theorem B1072205 : Blo 475787 1072205 := bbase (se 3 (by rfl) ⟨201038, by rfl⟩ : syracuseStep 1072205 = 402077) (by norm_num)
theorem B5463125 : Blo 475787 5463125 := bbase (se 8 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 5463125 = 64021) (by norm_num)
theorem B1072277 : Blo 475787 1072277 := bbase (se 6 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 1072277 = 50263) (by norm_num)
theorem B679109 : Blo 475787 679109 := bbase (se 4 (by rfl) ⟨63666, by rfl⟩ : syracuseStep 679109 = 127333) (by norm_num)
theorem B1072349 : Blo 475787 1072349 := bbase (se 3 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 1072349 = 402131) (by norm_num)
theorem B908509 : Blo 475787 908509 := bbase (se 3 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 908509 = 340691) (by norm_num)
theorem B1072421 : Blo 475787 1072421 := bbase (se 4 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 1072421 = 201079) (by norm_num)
theorem B1072493 : Blo 475787 1072493 := bbase (se 3 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 1072493 = 402185) (by norm_num)
theorem B908653 : Blo 475787 908653 := bbase (se 3 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 908653 = 340745) (by norm_num)
theorem B1072565 : Blo 475787 1072565 := bbase (se 5 (by rfl) ⟨50276, by rfl⟩ : syracuseStep 1072565 = 100553) (by norm_num)
theorem B1072637 : Blo 475787 1072637 := bbase (se 3 (by rfl) ⟨201119, by rfl⟩ : syracuseStep 1072637 = 402239) (by norm_num)
theorem B908813 : Blo 475787 908813 := bbase (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) (by norm_num)
theorem B1072709 : Blo 475787 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B2416229 : Blo 475787 2416229 := bbase (se 4 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 2416229 = 453043) (by norm_num)
theorem B1072781 : Blo 475787 1072781 := bbase (se 3 (by rfl) ⟨201146, by rfl⟩ : syracuseStep 1072781 = 402293) (by norm_num)
theorem B908957 : Blo 475787 908957 := bbase (se 3 (by rfl) ⟨170429, by rfl⟩ : syracuseStep 908957 = 340859) (by norm_num)
theorem B1072853 : Blo 475787 1072853 := bbase (se 7 (by rfl) ⟨12572, by rfl⟩ : syracuseStep 1072853 = 25145) (by norm_num)
theorem B1072925 : Blo 475787 1072925 := bbase (se 3 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 1072925 = 402347) (by norm_num)
theorem B1072997 : Blo 475787 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B1073069 : Blo 475787 1073069 := bbase (se 3 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 1073069 = 402401) (by norm_num)
theorem B679861 : Blo 475787 679861 := bbase (se 5 (by rfl) ⟨31868, by rfl⟩ : syracuseStep 679861 = 63737) (by norm_num)
theorem B909245 : Blo 475787 909245 := bbase (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) (by norm_num)
theorem B1073141 : Blo 475787 1073141 := bbase (se 5 (by rfl) ⟨50303, by rfl⟩ : syracuseStep 1073141 = 100607) (by norm_num)
theorem B1073213 : Blo 475787 1073213 := bbase (se 3 (by rfl) ⟨201227, by rfl⟩ : syracuseStep 1073213 = 402455) (by norm_num)
theorem B909397 : Blo 475787 909397 := bbase (se 8 (by rfl) ⟨5328, by rfl⟩ : syracuseStep 909397 = 10657) (by norm_num)
theorem B1073285 : Blo 475787 1073285 := bbase (se 4 (by rfl) ⟨100620, by rfl⟩ : syracuseStep 1073285 = 201241) (by norm_num)
theorem B1204429 : Blo 475787 1204429 := bbase (se 3 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 1204429 = 451661) (by norm_num)
theorem B1073357 : Blo 475787 1073357 := bbase (se 3 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 1073357 = 402509) (by norm_num)
theorem B1138933 : Blo 475787 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B1073429 : Blo 475787 1073429 := bbase (se 6 (by rfl) ⟨25158, by rfl⟩ : syracuseStep 1073429 = 50317) (by norm_num)
theorem B1204541 : Blo 475787 1204541 := bbase (se 3 (by rfl) ⟨225851, by rfl⟩ : syracuseStep 1204541 = 451703) (by norm_num)
theorem B1073501 : Blo 475787 1073501 := bbase (se 3 (by rfl) ⟨201281, by rfl⟩ : syracuseStep 1073501 = 402563) (by norm_num)
theorem B909701 : Blo 475787 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B1073573 : Blo 475787 1073573 := bbase (se 4 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 1073573 = 201295) (by norm_num)
theorem B483769 : Blo 475787 483769 := bbase (se 2 (by rfl) ⟨181413, by rfl⟩ : syracuseStep 483769 = 362827) (by norm_num)
theorem B1073645 : Blo 475787 1073645 := bbase (se 3 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 1073645 = 402617) (by norm_num)
theorem B1204733 : Blo 475787 1204733 := bbase (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) (by norm_num)
theorem B1073717 : Blo 475787 1073717 := bbase (se 5 (by rfl) ⟨50330, by rfl⟩ : syracuseStep 1073717 = 100661) (by norm_num)
theorem B1532533 : Blo 475787 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B1073789 : Blo 475787 1073789 := bbase (se 3 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 1073789 = 402671) (by norm_num)
theorem B1073861 : Blo 475787 1073861 := bbase (se 4 (by rfl) ⟨100674, by rfl⟩ : syracuseStep 1073861 = 201349) (by norm_num)
theorem B680653 : Blo 475787 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B1073933 : Blo 475787 1073933 := bbase (se 3 (by rfl) ⟨201362, by rfl⟩ : syracuseStep 1073933 = 402725) (by norm_num)
theorem B1205077 : Blo 475787 1205077 := bbase (se 9 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 1205077 = 7061) (by norm_num)
theorem B1074005 : Blo 475787 1074005 := bbase (se 9 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 1074005 = 6293) (by norm_num)
theorem B2417525 : Blo 475787 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B1074077 : Blo 475787 1074077 := bbase (se 3 (by rfl) ⟨201389, by rfl⟩ : syracuseStep 1074077 = 402779) (by norm_num)
theorem B1205189 : Blo 475787 1205189 := bbase (se 4 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 1205189 = 225973) (by norm_num)
theorem B713693 : Blo 475787 713693 := bbase (se 3 (by rfl) ⟨133817, by rfl⟩ : syracuseStep 713693 = 267635) (by norm_num)
theorem B1074149 : Blo 475787 1074149 := bbase (se 4 (by rfl) ⟨100701, by rfl⟩ : syracuseStep 1074149 = 201403) (by norm_num)
theorem B713717 : Blo 475787 713717 := bbase (se 5 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 713717 = 66911) (by norm_num)
theorem B713741 : Blo 475787 713741 := bbase (se 3 (by rfl) ⟨133826, by rfl⟩ : syracuseStep 713741 = 267653) (by norm_num)
theorem B680989 : Blo 475787 680989 := bbase (se 3 (by rfl) ⟨127685, by rfl⟩ : syracuseStep 680989 = 255371) (by norm_num)
theorem B713765 : Blo 475787 713765 := bbase (se 4 (by rfl) ⟨66915, by rfl⟩ : syracuseStep 713765 = 133831) (by norm_num)
theorem B1074221 : Blo 475787 1074221 := bbase (se 3 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 1074221 = 402833) (by norm_num)
theorem B713789 : Blo 475787 713789 := bbase (se 3 (by rfl) ⟨133835, by rfl⟩ : syracuseStep 713789 = 267671) (by norm_num)
theorem B713813 : Blo 475787 713813 := bbase (se 8 (by rfl) ⟨4182, by rfl⟩ : syracuseStep 713813 = 8365) (by norm_num)
theorem B517217 : Blo 475787 517217 := bbase (se 2 (by rfl) ⟨193956, by rfl⟩ : syracuseStep 517217 = 387913) (by norm_num)
theorem B713837 : Blo 475787 713837 := bbase (se 3 (by rfl) ⟨133844, by rfl⟩ : syracuseStep 713837 = 267689) (by norm_num)
theorem B1074293 : Blo 475787 1074293 := bbase (se 5 (by rfl) ⟨50357, by rfl⟩ : syracuseStep 1074293 = 100715) (by norm_num)
theorem B910453 : Blo 475787 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B713861 : Blo 475787 713861 := bbase (se 4 (by rfl) ⟨66924, by rfl⟩ : syracuseStep 713861 = 133849) (by norm_num)
theorem B1205381 : Blo 475787 1205381 := bbase (se 4 (by rfl) ⟨113004, by rfl⟩ : syracuseStep 1205381 = 226009) (by norm_num)
theorem B713885 : Blo 475787 713885 := bbase (se 3 (by rfl) ⟨133853, by rfl⟩ : syracuseStep 713885 = 267707) (by norm_num)
theorem B713909 : Blo 475787 713909 := bbase (se 5 (by rfl) ⟨33464, by rfl⟩ : syracuseStep 713909 = 66929) (by norm_num)
theorem B1074365 : Blo 475787 1074365 := bbase (se 3 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 1074365 = 402887) (by norm_num)
theorem B713933 : Blo 475787 713933 := bbase (se 3 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 713933 = 267725) (by norm_num)
theorem B2286805 : Blo 475787 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B713957 : Blo 475787 713957 := bbase (se 4 (by rfl) ⟨66933, by rfl⟩ : syracuseStep 713957 = 133867) (by norm_num)
theorem B681205 : Blo 475787 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B713981 : Blo 475787 713981 := bbase (se 3 (by rfl) ⟨133871, by rfl⟩ : syracuseStep 713981 = 267743) (by norm_num)
theorem B1074437 : Blo 475787 1074437 := bbase (se 4 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 1074437 = 201457) (by norm_num)
theorem B910597 : Blo 475787 910597 := bbase (se 4 (by rfl) ⟨85368, by rfl⟩ : syracuseStep 910597 = 170737) (by norm_num)
theorem B714005 : Blo 475787 714005 := bbase (se 6 (by rfl) ⟨16734, by rfl⟩ : syracuseStep 714005 = 33469) (by norm_num)
theorem B582941 : Blo 475787 582941 := bbase (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) (by norm_num)
theorem B714029 : Blo 475787 714029 := bbase (se 3 (by rfl) ⟨133880, by rfl⟩ : syracuseStep 714029 = 267761) (by norm_num)
theorem B714053 : Blo 475787 714053 := bbase (se 4 (by rfl) ⟨66942, by rfl⟩ : syracuseStep 714053 = 133885) (by norm_num)
theorem B1074509 : Blo 475787 1074509 := bbase (se 3 (by rfl) ⟨201470, by rfl⟩ : syracuseStep 1074509 = 402941) (by norm_num)
theorem B714077 : Blo 475787 714077 := bbase (se 3 (by rfl) ⟨133889, by rfl⟩ : syracuseStep 714077 = 267779) (by norm_num)
theorem B714101 : Blo 475787 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B714125 : Blo 475787 714125 := bbase (se 3 (by rfl) ⟨133898, by rfl⟩ : syracuseStep 714125 = 267797) (by norm_num)
theorem B1074581 : Blo 475787 1074581 := bbase (se 6 (by rfl) ⟨25185, by rfl⟩ : syracuseStep 1074581 = 50371) (by norm_num)
theorem B714149 : Blo 475787 714149 := bbase (se 4 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 714149 = 133903) (by norm_num)
theorem B910757 : Blo 475787 910757 := bbase (se 4 (by rfl) ⟨85383, by rfl⟩ : syracuseStep 910757 = 170767) (by norm_num)
theorem B714173 : Blo 475787 714173 := bbase (se 3 (by rfl) ⟨133907, by rfl⟩ : syracuseStep 714173 = 267815) (by norm_num)
theorem B714197 : Blo 475787 714197 := bbase (se 7 (by rfl) ⟨8369, by rfl⟩ : syracuseStep 714197 = 16739) (by norm_num)
theorem B1205725 : Blo 475787 1205725 := bbase (se 3 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 1205725 = 452147) (by norm_num)
theorem B1074653 : Blo 475787 1074653 := bbase (se 3 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 1074653 = 402995) (by norm_num)
theorem B714221 : Blo 475787 714221 := bbase (se 3 (by rfl) ⟨133916, by rfl⟩ : syracuseStep 714221 = 267833) (by norm_num)
theorem B714245 : Blo 475787 714245 := bbase (se 4 (by rfl) ⟨66960, by rfl⟩ : syracuseStep 714245 = 133921) (by norm_num)
theorem B714269 : Blo 475787 714269 := bbase (se 3 (by rfl) ⟨133925, by rfl⟩ : syracuseStep 714269 = 267851) (by norm_num)
theorem B1074725 : Blo 475787 1074725 := bbase (se 4 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 1074725 = 201511) (by norm_num)
theorem B3860021 : Blo 475787 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B714293 : Blo 475787 714293 := bbase (se 5 (by rfl) ⟨33482, by rfl⟩ : syracuseStep 714293 = 66965) (by norm_num)
theorem B714317 : Blo 475787 714317 := bbase (se 3 (by rfl) ⟨133934, by rfl⟩ : syracuseStep 714317 = 267869) (by norm_num)
theorem B1205837 : Blo 475787 1205837 := bbase (se 3 (by rfl) ⟨226094, by rfl⟩ : syracuseStep 1205837 = 452189) (by norm_num)
theorem B3434069 : Blo 475787 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B714341 : Blo 475787 714341 := bbase (se 4 (by rfl) ⟨66969, by rfl⟩ : syracuseStep 714341 = 133939) (by norm_num)
theorem B1074797 : Blo 475787 1074797 := bbase (se 3 (by rfl) ⟨201524, by rfl⟩ : syracuseStep 1074797 = 403049) (by norm_num)
theorem B681581 : Blo 475787 681581 := bbase (se 3 (by rfl) ⟨127796, by rfl⟩ : syracuseStep 681581 = 255593) (by norm_num)
theorem B714365 : Blo 475787 714365 := bbase (se 3 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 714365 = 267887) (by norm_num)
theorem B714389 : Blo 475787 714389 := bbase (se 6 (by rfl) ⟨16743, by rfl⟩ : syracuseStep 714389 = 33487) (by norm_num)
theorem B485021 : Blo 475787 485021 := bbase (se 3 (by rfl) ⟨90941, by rfl⟩ : syracuseStep 485021 = 181883) (by norm_num)
theorem B714413 : Blo 475787 714413 := bbase (se 3 (by rfl) ⟨133952, by rfl⟩ : syracuseStep 714413 = 267905) (by norm_num)
theorem B1074869 : Blo 475787 1074869 := bbase (se 5 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 1074869 = 100769) (by norm_num)
theorem B714437 : Blo 475787 714437 := bbase (se 4 (by rfl) ⟨66978, by rfl⟩ : syracuseStep 714437 = 133957) (by norm_num)
theorem B714461 : Blo 475787 714461 := bbase (se 3 (by rfl) ⟨133961, by rfl⟩ : syracuseStep 714461 = 267923) (by norm_num)
theorem B714485 : Blo 475787 714485 := bbase (se 5 (by rfl) ⟨33491, by rfl⟩ : syracuseStep 714485 = 66983) (by norm_num)
theorem B1074941 : Blo 475787 1074941 := bbase (se 3 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 1074941 = 403103) (by norm_num)
theorem B714509 : Blo 475787 714509 := bbase (se 3 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 714509 = 267941) (by norm_num)
theorem B1206029 : Blo 475787 1206029 := bbase (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) (by norm_num)
theorem B4351765 : Blo 475787 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B714533 : Blo 475787 714533 := bbase (se 4 (by rfl) ⟨66987, by rfl⟩ : syracuseStep 714533 = 133975) (by norm_num)
theorem B714557 : Blo 475787 714557 := bbase (se 3 (by rfl) ⟨133979, by rfl⟩ : syracuseStep 714557 = 267959) (by norm_num)
theorem B1075013 : Blo 475787 1075013 := bbase (se 4 (by rfl) ⟨100782, by rfl⟩ : syracuseStep 1075013 = 201565) (by norm_num)
theorem B714581 : Blo 475787 714581 := bbase (se 9 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 714581 = 4187) (by norm_num)
theorem B714605 : Blo 475787 714605 := bbase (se 3 (by rfl) ⟨133988, by rfl⟩ : syracuseStep 714605 = 267977) (by norm_num)
theorem B714629 : Blo 475787 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B1075085 : Blo 475787 1075085 := bbase (se 3 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 1075085 = 403157) (by norm_num)
theorem B714653 : Blo 475787 714653 := bbase (se 3 (by rfl) ⟨133997, by rfl⟩ : syracuseStep 714653 = 267995) (by norm_num)
theorem B485281 : Blo 475787 485281 := bbase (se 2 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 485281 = 363961) (by norm_num)
theorem B714677 : Blo 475787 714677 := bbase (se 5 (by rfl) ⟨33500, by rfl⟩ : syracuseStep 714677 = 67001) (by norm_num)
theorem B714701 : Blo 475787 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B5498837 : Blo 475787 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B1075157 : Blo 475787 1075157 := bbase (se 7 (by rfl) ⟨12599, by rfl⟩ : syracuseStep 1075157 = 25199) (by norm_num)
theorem B714725 : Blo 475787 714725 := bbase (se 4 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 714725 = 134011) (by norm_num)
theorem B714749 : Blo 475787 714749 := bbase (se 3 (by rfl) ⟨134015, by rfl⟩ : syracuseStep 714749 = 268031) (by norm_num)
theorem B714773 : Blo 475787 714773 := bbase (se 6 (by rfl) ⟨16752, by rfl⟩ : syracuseStep 714773 = 33505) (by norm_num)
theorem B1075229 : Blo 475787 1075229 := bbase (se 3 (by rfl) ⟨201605, by rfl⟩ : syracuseStep 1075229 = 403211) (by norm_num)
theorem B714797 : Blo 475787 714797 := bbase (se 3 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 714797 = 268049) (by norm_num)
theorem B1468469 : Blo 475787 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B714821 : Blo 475787 714821 := bbase (se 4 (by rfl) ⟨67014, by rfl⟩ : syracuseStep 714821 = 134029) (by norm_num)
theorem B714845 : Blo 475787 714845 := bbase (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) (by norm_num)
theorem B1206373 : Blo 475787 1206373 := bbase (se 4 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 1206373 = 226195) (by norm_num)
theorem B1075301 : Blo 475787 1075301 := bbase (se 4 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 1075301 = 201619) (by norm_num)
theorem B714869 : Blo 475787 714869 := bbase (se 5 (by rfl) ⟨33509, by rfl⟩ : syracuseStep 714869 = 67019) (by norm_num)
theorem B2418821 : Blo 475787 2418821 := bbase (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) (by norm_num)
theorem B714893 : Blo 475787 714893 := bbase (se 3 (by rfl) ⟨134042, by rfl⟩ : syracuseStep 714893 = 268085) (by norm_num)
theorem B714917 : Blo 475787 714917 := bbase (se 4 (by rfl) ⟨67023, by rfl⟩ : syracuseStep 714917 = 134047) (by norm_num)
theorem B1075373 : Blo 475787 1075373 := bbase (se 3 (by rfl) ⟨201632, by rfl⟩ : syracuseStep 1075373 = 403265) (by norm_num)
theorem B714941 : Blo 475787 714941 := bbase (se 3 (by rfl) ⟨134051, by rfl⟩ : syracuseStep 714941 = 268103) (by norm_num)
theorem B1206485 : Blo 475787 1206485 := bbase (se 7 (by rfl) ⟨14138, by rfl⟩ : syracuseStep 1206485 = 28277) (by norm_num)
theorem B714965 : Blo 475787 714965 := bbase (se 7 (by rfl) ⟨8378, by rfl⟩ : syracuseStep 714965 = 16757) (by norm_num)
theorem B714989 : Blo 475787 714989 := bbase (se 3 (by rfl) ⟨134060, by rfl⟩ : syracuseStep 714989 = 268121) (by norm_num)
theorem B1075445 : Blo 475787 1075445 := bbase (se 5 (by rfl) ⟨50411, by rfl⟩ : syracuseStep 1075445 = 100823) (by norm_num)
theorem B715013 : Blo 475787 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B715037 : Blo 475787 715037 := bbase (se 3 (by rfl) ⟨134069, by rfl⟩ : syracuseStep 715037 = 268139) (by norm_num)
theorem B715061 : Blo 475787 715061 := bbase (se 5 (by rfl) ⟨33518, by rfl⟩ : syracuseStep 715061 = 67037) (by norm_num)
theorem B1075517 : Blo 475787 1075517 := bbase (se 3 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 1075517 = 403319) (by norm_num)
theorem B715085 : Blo 475787 715085 := bbase (se 3 (by rfl) ⟨134078, by rfl⟩ : syracuseStep 715085 = 268157) (by norm_num)
theorem B715109 : Blo 475787 715109 := bbase (se 4 (by rfl) ⟨67041, by rfl⟩ : syracuseStep 715109 = 134083) (by norm_num)
theorem B715133 : Blo 475787 715133 := bbase (se 3 (by rfl) ⟨134087, by rfl⟩ : syracuseStep 715133 = 268175) (by norm_num)
theorem B1075589 : Blo 475787 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B1206677 : Blo 475787 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B715157 : Blo 475787 715157 := bbase (se 6 (by rfl) ⟨16761, by rfl⟩ : syracuseStep 715157 = 33523) (by norm_num)
theorem B715181 : Blo 475787 715181 := bbase (se 3 (by rfl) ⟨134096, by rfl⟩ : syracuseStep 715181 = 268193) (by norm_num)
theorem B715205 : Blo 475787 715205 := bbase (se 4 (by rfl) ⟨67050, by rfl⟩ : syracuseStep 715205 = 134101) (by norm_num)
theorem B1075661 : Blo 475787 1075661 := bbase (se 3 (by rfl) ⟨201686, by rfl⟩ : syracuseStep 1075661 = 403373) (by norm_num)
theorem B715229 : Blo 475787 715229 := bbase (se 3 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 715229 = 268211) (by norm_num)
theorem B715253 : Blo 475787 715253 := bbase (se 5 (by rfl) ⟨33527, by rfl⟩ : syracuseStep 715253 = 67055) (by norm_num)
theorem B715277 : Blo 475787 715277 := bbase (se 3 (by rfl) ⟨134114, by rfl⟩ : syracuseStep 715277 = 268229) (by norm_num)
theorem B1075733 : Blo 475787 1075733 := bbase (se 6 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 1075733 = 50425) (by norm_num)
theorem B715301 : Blo 475787 715301 := bbase (se 4 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 715301 = 134119) (by norm_num)
theorem B715325 : Blo 475787 715325 := bbase (se 3 (by rfl) ⟨134123, by rfl⟩ : syracuseStep 715325 = 268247) (by norm_num)
theorem B715349 : Blo 475787 715349 := bbase (se 8 (by rfl) ⟨4191, by rfl⟩ : syracuseStep 715349 = 8383) (by norm_num)
theorem B1075805 : Blo 475787 1075805 := bbase (se 3 (by rfl) ⟨201713, by rfl⟩ : syracuseStep 1075805 = 403427) (by norm_num)
theorem B715373 : Blo 475787 715373 := bbase (se 3 (by rfl) ⟨134132, by rfl⟩ : syracuseStep 715373 = 268265) (by norm_num)
theorem B715397 : Blo 475787 715397 := bbase (se 4 (by rfl) ⟨67068, by rfl⟩ : syracuseStep 715397 = 134137) (by norm_num)
theorem B715421 : Blo 475787 715421 := bbase (se 3 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 715421 = 268283) (by norm_num)
theorem B1075877 : Blo 475787 1075877 := bbase (se 4 (by rfl) ⟨100863, by rfl⟩ : syracuseStep 1075877 = 201727) (by norm_num)
theorem B715445 : Blo 475787 715445 := bbase (se 5 (by rfl) ⟨33536, by rfl⟩ : syracuseStep 715445 = 67073) (by norm_num)
theorem B715469 : Blo 475787 715469 := bbase (se 3 (by rfl) ⟨134150, by rfl⟩ : syracuseStep 715469 = 268301) (by norm_num)
theorem B715493 : Blo 475787 715493 := bbase (se 4 (by rfl) ⟨67077, by rfl⟩ : syracuseStep 715493 = 134155) (by norm_num)
theorem B1207021 : Blo 475787 1207021 := bbase (se 3 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 1207021 = 452633) (by norm_num)
theorem B1075949 : Blo 475787 1075949 := bbase (se 3 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 1075949 = 403481) (by norm_num)
theorem B715517 : Blo 475787 715517 := bbase (se 3 (by rfl) ⟨134159, by rfl⟩ : syracuseStep 715517 = 268319) (by norm_num)
theorem B715541 : Blo 475787 715541 := bbase (se 6 (by rfl) ⟨16770, by rfl⟩ : syracuseStep 715541 = 33541) (by norm_num)
theorem B715565 : Blo 475787 715565 := bbase (se 3 (by rfl) ⟨134168, by rfl⟩ : syracuseStep 715565 = 268337) (by norm_num)
theorem B1076021 : Blo 475787 1076021 := bbase (se 5 (by rfl) ⟨50438, by rfl⟩ : syracuseStep 1076021 = 100877) (by norm_num)
theorem B715589 : Blo 475787 715589 := bbase (se 4 (by rfl) ⟨67086, by rfl⟩ : syracuseStep 715589 = 134173) (by norm_num)
theorem B1207133 : Blo 475787 1207133 := bbase (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) (by norm_num)
theorem B715613 : Blo 475787 715613 := bbase (se 3 (by rfl) ⟨134177, by rfl⟩ : syracuseStep 715613 = 268355) (by norm_num)
theorem B715637 : Blo 475787 715637 := bbase (se 5 (by rfl) ⟨33545, by rfl⟩ : syracuseStep 715637 = 67091) (by norm_num)
theorem B1076093 : Blo 475787 1076093 := bbase (se 3 (by rfl) ⟨201767, by rfl⟩ : syracuseStep 1076093 = 403535) (by norm_num)
theorem B715661 : Blo 475787 715661 := bbase (se 3 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 715661 = 268373) (by norm_num)
theorem B715685 : Blo 475787 715685 := bbase (se 4 (by rfl) ⟨67095, by rfl⟩ : syracuseStep 715685 = 134191) (by norm_num)
theorem B715709 : Blo 475787 715709 := bbase (se 3 (by rfl) ⟨134195, by rfl⟩ : syracuseStep 715709 = 268391) (by norm_num)
theorem B1076165 : Blo 475787 1076165 := bbase (se 4 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 1076165 = 201781) (by norm_num)
theorem B715733 : Blo 475787 715733 := bbase (se 7 (by rfl) ⟨8387, by rfl⟩ : syracuseStep 715733 = 16775) (by norm_num)
theorem B715757 : Blo 475787 715757 := bbase (se 3 (by rfl) ⟨134204, by rfl⟩ : syracuseStep 715757 = 268409) (by norm_num)
theorem B683005 : Blo 475787 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B715781 : Blo 475787 715781 := bbase (se 4 (by rfl) ⟨67104, by rfl⟩ : syracuseStep 715781 = 134209) (by norm_num)
theorem B1076237 : Blo 475787 1076237 := bbase (se 3 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 1076237 = 403589) (by norm_num)
theorem B1207325 : Blo 475787 1207325 := bbase (se 3 (by rfl) ⟨226373, by rfl⟩ : syracuseStep 1207325 = 452747) (by norm_num)
theorem B715805 : Blo 475787 715805 := bbase (se 3 (by rfl) ⟨134213, by rfl⟩ : syracuseStep 715805 = 268427) (by norm_num)
theorem B715829 : Blo 475787 715829 := bbase (se 5 (by rfl) ⟨33554, by rfl⟩ : syracuseStep 715829 = 67109) (by norm_num)
theorem B715853 : Blo 475787 715853 := bbase (se 3 (by rfl) ⟨134222, by rfl⟩ : syracuseStep 715853 = 268445) (by norm_num)
theorem B1076309 : Blo 475787 1076309 := bbase (se 8 (by rfl) ⟨6306, by rfl⟩ : syracuseStep 1076309 = 12613) (by norm_num)
theorem B715877 : Blo 475787 715877 := bbase (se 4 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 715877 = 134227) (by norm_num)
theorem B715901 : Blo 475787 715901 := bbase (se 3 (by rfl) ⟨134231, by rfl⟩ : syracuseStep 715901 = 268463) (by norm_num)
theorem B715925 : Blo 475787 715925 := bbase (se 6 (by rfl) ⟨16779, by rfl⟩ : syracuseStep 715925 = 33559) (by norm_num)
theorem B1076381 : Blo 475787 1076381 := bbase (se 3 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 1076381 = 403643) (by norm_num)
theorem B715949 : Blo 475787 715949 := bbase (se 3 (by rfl) ⟨134240, by rfl⟩ : syracuseStep 715949 = 268481) (by norm_num)
theorem B715973 : Blo 475787 715973 := bbase (se 4 (by rfl) ⟨67122, by rfl⟩ : syracuseStep 715973 = 134245) (by norm_num)
theorem B715997 : Blo 475787 715997 := bbase (se 3 (by rfl) ⟨134249, by rfl⟩ : syracuseStep 715997 = 268499) (by norm_num)
theorem B1076453 : Blo 475787 1076453 := bbase (se 4 (by rfl) ⟨100917, by rfl⟩ : syracuseStep 1076453 = 201835) (by norm_num)
theorem B716021 : Blo 475787 716021 := bbase (se 5 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 716021 = 67127) (by norm_num)
theorem B716045 : Blo 475787 716045 := bbase (se 3 (by rfl) ⟨134258, by rfl⟩ : syracuseStep 716045 = 268517) (by norm_num)
theorem B3665173 : Blo 475787 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B716069 : Blo 475787 716069 := bbase (se 4 (by rfl) ⟨67131, by rfl⟩ : syracuseStep 716069 = 134263) (by norm_num)
theorem B1076525 : Blo 475787 1076525 := bbase (se 3 (by rfl) ⟨201848, by rfl⟩ : syracuseStep 1076525 = 403697) (by norm_num)
theorem B716093 : Blo 475787 716093 := bbase (se 3 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 716093 = 268535) (by norm_num)
theorem B716117 : Blo 475787 716117 := bbase (se 11 (by rfl) ⟨524, by rfl⟩ : syracuseStep 716117 = 1049) (by norm_num)
theorem B716141 : Blo 475787 716141 := bbase (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) (by norm_num)
theorem B1207669 : Blo 475787 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B1076597 : Blo 475787 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B716165 : Blo 475787 716165 := bbase (se 4 (by rfl) ⟨67140, by rfl⟩ : syracuseStep 716165 = 134281) (by norm_num)
theorem B1535365 : Blo 475787 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B2420117 : Blo 475787 2420117 := bbase (se 6 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 2420117 = 113443) (by norm_num)
theorem B716189 : Blo 475787 716189 := bbase (se 3 (by rfl) ⟨134285, by rfl⟩ : syracuseStep 716189 = 268571) (by norm_num)
theorem B716213 : Blo 475787 716213 := bbase (se 5 (by rfl) ⟨33572, by rfl⟩ : syracuseStep 716213 = 67145) (by norm_num)
theorem B1076669 : Blo 475787 1076669 := bbase (se 3 (by rfl) ⟨201875, by rfl⟩ : syracuseStep 1076669 = 403751) (by norm_num)
theorem B1535429 : Blo 475787 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B716237 : Blo 475787 716237 := bbase (se 3 (by rfl) ⟨134294, by rfl⟩ : syracuseStep 716237 = 268589) (by norm_num)
theorem B1207781 : Blo 475787 1207781 := bbase (se 4 (by rfl) ⟨113229, by rfl⟩ : syracuseStep 1207781 = 226459) (by norm_num)
theorem B716261 : Blo 475787 716261 := bbase (se 4 (by rfl) ⟨67149, by rfl⟩ : syracuseStep 716261 = 134299) (by norm_num)
theorem B716285 : Blo 475787 716285 := bbase (se 3 (by rfl) ⟨134303, by rfl⟩ : syracuseStep 716285 = 268607) (by norm_num)
theorem B1076741 : Blo 475787 1076741 := bbase (se 4 (by rfl) ⟨100944, by rfl⟩ : syracuseStep 1076741 = 201889) (by norm_num)
theorem B716309 : Blo 475787 716309 := bbase (se 6 (by rfl) ⟨16788, by rfl⟩ : syracuseStep 716309 = 33577) (by norm_num)
theorem B716333 : Blo 475787 716333 := bbase (se 3 (by rfl) ⟨134312, by rfl⟩ : syracuseStep 716333 = 268625) (by norm_num)
theorem B716357 : Blo 475787 716357 := bbase (se 4 (by rfl) ⟨67158, by rfl⟩ : syracuseStep 716357 = 134317) (by norm_num)
theorem B1076813 : Blo 475787 1076813 := bbase (se 3 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 1076813 = 403805) (by norm_num)
theorem B716381 : Blo 475787 716381 := bbase (se 3 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 716381 = 268643) (by norm_num)
theorem B716405 : Blo 475787 716405 := bbase (se 5 (by rfl) ⟨33581, by rfl⟩ : syracuseStep 716405 = 67163) (by norm_num)
theorem B716429 : Blo 475787 716429 := bbase (se 3 (by rfl) ⟨134330, by rfl⟩ : syracuseStep 716429 = 268661) (by norm_num)
theorem B1076885 : Blo 475787 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B1207973 : Blo 475787 1207973 := bbase (se 4 (by rfl) ⟨113247, by rfl⟩ : syracuseStep 1207973 = 226495) (by norm_num)
theorem B716453 : Blo 475787 716453 := bbase (se 4 (by rfl) ⟨67167, by rfl⟩ : syracuseStep 716453 = 134335) (by norm_num)
theorem B716477 : Blo 475787 716477 := bbase (se 3 (by rfl) ⟨134339, by rfl⟩ : syracuseStep 716477 = 268679) (by norm_num)
theorem B716501 : Blo 475787 716501 := bbase (se 7 (by rfl) ⟨8396, by rfl⟩ : syracuseStep 716501 = 16793) (by norm_num)
theorem B1076957 : Blo 475787 1076957 := bbase (se 3 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 1076957 = 403859) (by norm_num)
theorem B716525 : Blo 475787 716525 := bbase (se 3 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 716525 = 268697) (by norm_num)
theorem B716549 : Blo 475787 716549 := bbase (se 4 (by rfl) ⟨67176, by rfl⟩ : syracuseStep 716549 = 134353) (by norm_num)
theorem B716573 : Blo 475787 716573 := bbase (se 3 (by rfl) ⟨134357, by rfl⟩ : syracuseStep 716573 = 268715) (by norm_num)
theorem B1077029 : Blo 475787 1077029 := bbase (se 4 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 1077029 = 201943) (by norm_num)
theorem B716597 : Blo 475787 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B716621 : Blo 475787 716621 := bbase (se 3 (by rfl) ⟨134366, by rfl⟩ : syracuseStep 716621 = 268733) (by norm_num)
theorem B716645 : Blo 475787 716645 := bbase (se 4 (by rfl) ⟨67185, by rfl⟩ : syracuseStep 716645 = 134371) (by norm_num)
theorem B1077101 : Blo 475787 1077101 := bbase (se 3 (by rfl) ⟨201956, by rfl⟩ : syracuseStep 1077101 = 403913) (by norm_num)
theorem B716669 : Blo 475787 716669 := bbase (se 3 (by rfl) ⟨134375, by rfl⟩ : syracuseStep 716669 = 268751) (by norm_num)
theorem B716693 : Blo 475787 716693 := bbase (se 6 (by rfl) ⟨16797, by rfl⟩ : syracuseStep 716693 = 33595) (by norm_num)
theorem B716717 : Blo 475787 716717 := bbase (se 3 (by rfl) ⟨134384, by rfl⟩ : syracuseStep 716717 = 268769) (by norm_num)
theorem B1077173 : Blo 475787 1077173 := bbase (se 5 (by rfl) ⟨50492, by rfl⟩ : syracuseStep 1077173 = 100985) (by norm_num)
theorem B716741 : Blo 475787 716741 := bbase (se 4 (by rfl) ⟨67194, by rfl⟩ : syracuseStep 716741 = 134389) (by norm_num)
theorem B3502037 : Blo 475787 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B716765 : Blo 475787 716765 := bbase (se 3 (by rfl) ⟨134393, by rfl⟩ : syracuseStep 716765 = 268787) (by norm_num)
theorem B716789 : Blo 475787 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B1208317 : Blo 475787 1208317 := bbase (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) (by norm_num)
theorem B1077245 : Blo 475787 1077245 := bbase (se 3 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 1077245 = 403967) (by norm_num)
theorem B716813 : Blo 475787 716813 := bbase (se 3 (by rfl) ⟨134402, by rfl⟩ : syracuseStep 716813 = 268805) (by norm_num)
theorem B716837 : Blo 475787 716837 := bbase (se 4 (by rfl) ⟨67203, by rfl⟩ : syracuseStep 716837 = 134407) (by norm_num)
theorem B716861 : Blo 475787 716861 := bbase (se 3 (by rfl) ⟨134411, by rfl⟩ : syracuseStep 716861 = 268823) (by norm_num)
theorem B1077317 : Blo 475787 1077317 := bbase (se 4 (by rfl) ⟨100998, by rfl⟩ : syracuseStep 1077317 = 201997) (by norm_num)
theorem B716885 : Blo 475787 716885 := bbase (se 8 (by rfl) ⟨4200, by rfl⟩ : syracuseStep 716885 = 8401) (by norm_num)
theorem B1208429 : Blo 475787 1208429 := bbase (se 3 (by rfl) ⟨226580, by rfl⟩ : syracuseStep 1208429 = 453161) (by norm_num)
theorem B716909 : Blo 475787 716909 := bbase (se 3 (by rfl) ⟨134420, by rfl⟩ : syracuseStep 716909 = 268841) (by norm_num)
theorem B716933 : Blo 475787 716933 := bbase (se 4 (by rfl) ⟨67212, by rfl⟩ : syracuseStep 716933 = 134425) (by norm_num)
theorem B1077389 : Blo 475787 1077389 := bbase (se 3 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 1077389 = 404021) (by norm_num)
theorem B716957 : Blo 475787 716957 := bbase (se 3 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 716957 = 268859) (by norm_num)
theorem B716981 : Blo 475787 716981 := bbase (se 5 (by rfl) ⟨33608, by rfl⟩ : syracuseStep 716981 = 67217) (by norm_num)
theorem B717005 : Blo 475787 717005 := bbase (se 3 (by rfl) ⟨134438, by rfl⟩ : syracuseStep 717005 = 268877) (by norm_num)
theorem B1077461 : Blo 475787 1077461 := bbase (se 7 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 1077461 = 25253) (by norm_num)
theorem B717029 : Blo 475787 717029 := bbase (se 4 (by rfl) ⟨67221, by rfl⟩ : syracuseStep 717029 = 134443) (by norm_num)
theorem B717053 : Blo 475787 717053 := bbase (se 3 (by rfl) ⟨134447, by rfl⟩ : syracuseStep 717053 = 268895) (by norm_num)
theorem B717077 : Blo 475787 717077 := bbase (se 6 (by rfl) ⟨16806, by rfl⟩ : syracuseStep 717077 = 33613) (by norm_num)
theorem B1077533 : Blo 475787 1077533 := bbase (se 3 (by rfl) ⟨202037, by rfl⟩ : syracuseStep 1077533 = 404075) (by norm_num)
theorem B1208621 : Blo 475787 1208621 := bbase (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) (by norm_num)
theorem B717101 : Blo 475787 717101 := bbase (se 3 (by rfl) ⟨134456, by rfl⟩ : syracuseStep 717101 = 268913) (by norm_num)
theorem B717125 : Blo 475787 717125 := bbase (se 4 (by rfl) ⟨67230, by rfl⟩ : syracuseStep 717125 = 134461) (by norm_num)
theorem B717149 : Blo 475787 717149 := bbase (se 3 (by rfl) ⟨134465, by rfl⟩ : syracuseStep 717149 = 268931) (by norm_num)
theorem B1077605 : Blo 475787 1077605 := bbase (se 4 (by rfl) ⟨101025, by rfl⟩ : syracuseStep 1077605 = 202051) (by norm_num)
theorem B717173 : Blo 475787 717173 := bbase (se 5 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 717173 = 67235) (by norm_num)
theorem B717197 : Blo 475787 717197 := bbase (se 3 (by rfl) ⟨134474, by rfl⟩ : syracuseStep 717197 = 268949) (by norm_num)
theorem B717221 : Blo 475787 717221 := bbase (se 4 (by rfl) ⟨67239, by rfl⟩ : syracuseStep 717221 = 134479) (by norm_num)
theorem B1077677 : Blo 475787 1077677 := bbase (se 3 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 1077677 = 404129) (by norm_num)
theorem B1143229 : Blo 475787 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B717245 : Blo 475787 717245 := bbase (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) (by norm_num)
theorem B717269 : Blo 475787 717269 := bbase (se 7 (by rfl) ⟨8405, by rfl⟩ : syracuseStep 717269 = 16811) (by norm_num)
theorem B717293 : Blo 475787 717293 := bbase (se 3 (by rfl) ⟨134492, by rfl⟩ : syracuseStep 717293 = 268985) (by norm_num)
theorem B1077749 : Blo 475787 1077749 := bbase (se 5 (by rfl) ⟨50519, by rfl⟩ : syracuseStep 1077749 = 101039) (by norm_num)
theorem B717317 : Blo 475787 717317 := bbase (se 4 (by rfl) ⟨67248, by rfl⟩ : syracuseStep 717317 = 134497) (by norm_num)
theorem B717341 : Blo 475787 717341 := bbase (se 3 (by rfl) ⟨134501, by rfl⟩ : syracuseStep 717341 = 269003) (by norm_num)
theorem B717365 : Blo 475787 717365 := bbase (se 5 (by rfl) ⟨33626, by rfl⟩ : syracuseStep 717365 = 67253) (by norm_num)
theorem B1077821 : Blo 475787 1077821 := bbase (se 3 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 1077821 = 404183) (by norm_num)
theorem B717389 : Blo 475787 717389 := bbase (se 3 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 717389 = 269021) (by norm_num)
theorem B717413 : Blo 475787 717413 := bbase (se 4 (by rfl) ⟨67257, by rfl⟩ : syracuseStep 717413 = 134515) (by norm_num)
theorem B717437 : Blo 475787 717437 := bbase (se 3 (by rfl) ⟨134519, by rfl⟩ : syracuseStep 717437 = 269039) (by norm_num)
theorem B1208965 : Blo 475787 1208965 := bbase (se 4 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 1208965 = 226681) (by norm_num)
theorem B1077893 : Blo 475787 1077893 := bbase (se 4 (by rfl) ⟨101052, by rfl⟩ : syracuseStep 1077893 = 202105) (by norm_num)
theorem B717461 : Blo 475787 717461 := bbase (se 6 (by rfl) ⟨16815, by rfl⟩ : syracuseStep 717461 = 33631) (by norm_num)
theorem B2323109 : Blo 475787 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B2421413 : Blo 475787 2421413 := bbase (se 4 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 2421413 = 454015) (by norm_num)
theorem B717485 : Blo 475787 717485 := bbase (se 3 (by rfl) ⟨134528, by rfl⟩ : syracuseStep 717485 = 269057) (by norm_num)
theorem B717509 : Blo 475787 717509 := bbase (se 4 (by rfl) ⟨67266, by rfl⟩ : syracuseStep 717509 = 134533) (by norm_num)
theorem B1077965 : Blo 475787 1077965 := bbase (se 3 (by rfl) ⟨202118, by rfl⟩ : syracuseStep 1077965 = 404237) (by norm_num)
theorem B717533 : Blo 475787 717533 := bbase (se 3 (by rfl) ⟨134537, by rfl⟩ : syracuseStep 717533 = 269075) (by norm_num)
theorem B1209077 : Blo 475787 1209077 := bbase (se 5 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 1209077 = 113351) (by norm_num)
theorem B717557 : Blo 475787 717557 := bbase (se 5 (by rfl) ⟨33635, by rfl⟩ : syracuseStep 717557 = 67271) (by norm_num)
theorem B717581 : Blo 475787 717581 := bbase (se 3 (by rfl) ⟨134546, by rfl⟩ : syracuseStep 717581 = 269093) (by norm_num)
theorem B1078037 : Blo 475787 1078037 := bbase (se 6 (by rfl) ⟨25266, by rfl⟩ : syracuseStep 1078037 = 50533) (by norm_num)
theorem B717605 : Blo 475787 717605 := bbase (se 4 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 717605 = 134551) (by norm_num)
theorem B717629 : Blo 475787 717629 := bbase (se 3 (by rfl) ⟨134555, by rfl⟩ : syracuseStep 717629 = 269111) (by norm_num)
theorem B717653 : Blo 475787 717653 := bbase (se 9 (by rfl) ⟨2102, by rfl⟩ : syracuseStep 717653 = 4205) (by norm_num)
theorem B1078109 : Blo 475787 1078109 := bbase (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) (by norm_num)
theorem B717677 : Blo 475787 717677 := bbase (se 3 (by rfl) ⟨134564, by rfl⟩ : syracuseStep 717677 = 269129) (by norm_num)
theorem B717701 : Blo 475787 717701 := bbase (se 4 (by rfl) ⟨67284, by rfl⟩ : syracuseStep 717701 = 134569) (by norm_num)
theorem B717725 : Blo 475787 717725 := bbase (se 3 (by rfl) ⟨134573, by rfl⟩ : syracuseStep 717725 = 269147) (by norm_num)
theorem B1078181 : Blo 475787 1078181 := bbase (se 4 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 1078181 = 202159) (by norm_num)
theorem B1209269 : Blo 475787 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B717749 : Blo 475787 717749 := bbase (se 5 (by rfl) ⟨33644, by rfl⟩ : syracuseStep 717749 = 67289) (by norm_num)
theorem B717773 : Blo 475787 717773 := bbase (se 3 (by rfl) ⟨134582, by rfl⟩ : syracuseStep 717773 = 269165) (by norm_num)
theorem B717797 : Blo 475787 717797 := bbase (se 4 (by rfl) ⟨67293, by rfl⟩ : syracuseStep 717797 = 134587) (by norm_num)
theorem B1078253 : Blo 475787 1078253 := bbase (se 3 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 1078253 = 404345) (by norm_num)
theorem B717821 : Blo 475787 717821 := bbase (se 3 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 717821 = 269183) (by norm_num)
theorem B717845 : Blo 475787 717845 := bbase (se 6 (by rfl) ⟨16824, by rfl⟩ : syracuseStep 717845 = 33649) (by norm_num)
theorem B1143845 : Blo 475787 1143845 := bbase (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) (by norm_num)
theorem B717869 : Blo 475787 717869 := bbase (se 3 (by rfl) ⟨134600, by rfl⟩ : syracuseStep 717869 = 269201) (by norm_num)
theorem B1078325 : Blo 475787 1078325 := bbase (se 5 (by rfl) ⟨50546, by rfl⟩ : syracuseStep 1078325 = 101093) (by norm_num)
theorem B717893 : Blo 475787 717893 := bbase (se 4 (by rfl) ⟨67302, by rfl⟩ : syracuseStep 717893 = 134605) (by norm_num)
theorem B717917 : Blo 475787 717917 := bbase (se 3 (by rfl) ⟨134609, by rfl⟩ : syracuseStep 717917 = 269219) (by norm_num)
theorem B717941 : Blo 475787 717941 := bbase (se 5 (by rfl) ⟨33653, by rfl⟩ : syracuseStep 717941 = 67307) (by norm_num)
theorem B1078397 : Blo 475787 1078397 := bbase (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) (by norm_num)
theorem B717965 : Blo 475787 717965 := bbase (se 3 (by rfl) ⟨134618, by rfl⟩ : syracuseStep 717965 = 269237) (by norm_num)
theorem B6124693 : Blo 475787 6124693 := bbase (se 6 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 6124693 = 287095) (by norm_num)
theorem B717989 : Blo 475787 717989 := bbase (se 4 (by rfl) ⟨67311, by rfl⟩ : syracuseStep 717989 = 134623) (by norm_num)
theorem B718013 : Blo 475787 718013 := bbase (se 3 (by rfl) ⟨134627, by rfl⟩ : syracuseStep 718013 = 269255) (by norm_num)
theorem B1078469 : Blo 475787 1078469 := bbase (se 4 (by rfl) ⟨101106, by rfl⟩ : syracuseStep 1078469 = 202213) (by norm_num)
theorem B718037 : Blo 475787 718037 := bbase (se 7 (by rfl) ⟨8414, by rfl⟩ : syracuseStep 718037 = 16829) (by norm_num)
theorem B1144037 : Blo 475787 1144037 := bbase (se 4 (by rfl) ⟨107253, by rfl⟩ : syracuseStep 1144037 = 214507) (by norm_num)
theorem B718061 : Blo 475787 718061 := bbase (se 3 (by rfl) ⟨134636, by rfl⟩ : syracuseStep 718061 = 269273) (by norm_num)
theorem B718085 : Blo 475787 718085 := bbase (se 4 (by rfl) ⟨67320, by rfl⟩ : syracuseStep 718085 = 134641) (by norm_num)
theorem B1209613 : Blo 475787 1209613 := bbase (se 3 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 1209613 = 453605) (by norm_num)
theorem B1078541 : Blo 475787 1078541 := bbase (se 3 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 1078541 = 404453) (by norm_num)
theorem B718109 : Blo 475787 718109 := bbase (se 3 (by rfl) ⟨134645, by rfl⟩ : syracuseStep 718109 = 269291) (by norm_num)
theorem B718133 : Blo 475787 718133 := bbase (se 5 (by rfl) ⟨33662, by rfl⟩ : syracuseStep 718133 = 67325) (by norm_num)
theorem B718157 : Blo 475787 718157 := bbase (se 3 (by rfl) ⟨134654, by rfl⟩ : syracuseStep 718157 = 269309) (by norm_num)
theorem B1078613 : Blo 475787 1078613 := bbase (se 13 (by rfl) ⟨197, by rfl⟩ : syracuseStep 1078613 = 395) (by norm_num)
theorem B718181 : Blo 475787 718181 := bbase (se 4 (by rfl) ⟨67329, by rfl⟩ : syracuseStep 718181 = 134659) (by norm_num)
theorem B816509 : Blo 475787 816509 := bbase (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) (by norm_num)
theorem B1209725 : Blo 475787 1209725 := bbase (se 3 (by rfl) ⟨226823, by rfl⟩ : syracuseStep 1209725 = 453647) (by norm_num)
theorem B718205 : Blo 475787 718205 := bbase (se 3 (by rfl) ⟨134663, by rfl⟩ : syracuseStep 718205 = 269327) (by norm_num)
theorem B718229 : Blo 475787 718229 := bbase (se 6 (by rfl) ⟨16833, by rfl⟩ : syracuseStep 718229 = 33667) (by norm_num)
theorem B1078685 : Blo 475787 1078685 := bbase (se 3 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 1078685 = 404507) (by norm_num)
theorem B718253 : Blo 475787 718253 := bbase (se 3 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 718253 = 269345) (by norm_num)
theorem B718277 : Blo 475787 718277 := bbase (se 4 (by rfl) ⟨67338, by rfl⟩ : syracuseStep 718277 = 134677) (by norm_num)
theorem B718301 : Blo 475787 718301 := bbase (se 3 (by rfl) ⟨134681, by rfl⟩ : syracuseStep 718301 = 269363) (by norm_num)
theorem B1078757 : Blo 475787 1078757 := bbase (se 4 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 1078757 = 202267) (by norm_num)
theorem B718325 : Blo 475787 718325 := bbase (se 5 (by rfl) ⟨33671, by rfl⟩ : syracuseStep 718325 = 67343) (by norm_num)
theorem B1144325 : Blo 475787 1144325 := bbase (se 4 (by rfl) ⟨107280, by rfl⟩ : syracuseStep 1144325 = 214561) (by norm_num)
theorem B718349 : Blo 475787 718349 := bbase (se 3 (by rfl) ⟨134690, by rfl⟩ : syracuseStep 718349 = 269381) (by norm_num)
theorem B718373 : Blo 475787 718373 := bbase (se 4 (by rfl) ⟨67347, by rfl⟩ : syracuseStep 718373 = 134695) (by norm_num)
theorem B1078829 : Blo 475787 1078829 := bbase (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) (by norm_num)
theorem B1209917 : Blo 475787 1209917 := bbase (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) (by norm_num)
theorem B718397 : Blo 475787 718397 := bbase (se 3 (by rfl) ⟨134699, by rfl⟩ : syracuseStep 718397 = 269399) (by norm_num)
theorem B718421 : Blo 475787 718421 := bbase (se 8 (by rfl) ⟨4209, by rfl⟩ : syracuseStep 718421 = 8419) (by norm_num)
theorem B718445 : Blo 475787 718445 := bbase (se 3 (by rfl) ⟨134708, by rfl⟩ : syracuseStep 718445 = 269417) (by norm_num)
theorem B3929717 : Blo 475787 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1078901 : Blo 475787 1078901 := bbase (se 5 (by rfl) ⟨50573, by rfl⟩ : syracuseStep 1078901 = 101147) (by norm_num)
theorem B718469 : Blo 475787 718469 := bbase (se 4 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 718469 = 134713) (by norm_num)
theorem B718493 : Blo 475787 718493 := bbase (se 3 (by rfl) ⟨134717, by rfl⟩ : syracuseStep 718493 = 269435) (by norm_num)
theorem B718517 : Blo 475787 718517 := bbase (se 5 (by rfl) ⟨33680, by rfl⟩ : syracuseStep 718517 = 67361) (by norm_num)
theorem B1078973 : Blo 475787 1078973 := bbase (se 3 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 1078973 = 404615) (by norm_num)
theorem B718541 : Blo 475787 718541 := bbase (se 3 (by rfl) ⟨134726, by rfl⟩ : syracuseStep 718541 = 269453) (by norm_num)
theorem B718565 : Blo 475787 718565 := bbase (se 4 (by rfl) ⟨67365, by rfl⟩ : syracuseStep 718565 = 134731) (by norm_num)
theorem B718589 : Blo 475787 718589 := bbase (se 3 (by rfl) ⟨134735, by rfl⟩ : syracuseStep 718589 = 269471) (by norm_num)
theorem B1079045 : Blo 475787 1079045 := bbase (se 4 (by rfl) ⟨101160, by rfl⟩ : syracuseStep 1079045 = 202321) (by norm_num)
theorem B718613 : Blo 475787 718613 := bbase (se 6 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 718613 = 33685) (by norm_num)
theorem B718637 : Blo 475787 718637 := bbase (se 3 (by rfl) ⟨134744, by rfl⟩ : syracuseStep 718637 = 269489) (by norm_num)
theorem B718661 : Blo 475787 718661 := bbase (se 4 (by rfl) ⟨67374, by rfl⟩ : syracuseStep 718661 = 134749) (by norm_num)
theorem B1079117 : Blo 475787 1079117 := bbase (se 3 (by rfl) ⟨202334, by rfl⟩ : syracuseStep 1079117 = 404669) (by norm_num)
theorem B718685 : Blo 475787 718685 := bbase (se 3 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 718685 = 269507) (by norm_num)
theorem B718709 : Blo 475787 718709 := bbase (se 5 (by rfl) ⟨33689, by rfl⟩ : syracuseStep 718709 = 67379) (by norm_num)
theorem B718733 : Blo 475787 718733 := bbase (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) (by norm_num)
theorem B1210261 : Blo 475787 1210261 := bbase (se 6 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 1210261 = 56731) (by norm_num)
theorem B1079189 : Blo 475787 1079189 := bbase (se 6 (by rfl) ⟨25293, by rfl⟩ : syracuseStep 1079189 = 50587) (by norm_num)
theorem B718757 : Blo 475787 718757 := bbase (se 4 (by rfl) ⟨67383, by rfl⟩ : syracuseStep 718757 = 134767) (by norm_num)
theorem B2717621 : Blo 475787 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B2422709 : Blo 475787 2422709 := bbase (se 5 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 2422709 = 227129) (by norm_num)
theorem B718781 : Blo 475787 718781 := bbase (se 3 (by rfl) ⟨134771, by rfl⟩ : syracuseStep 718781 = 269543) (by norm_num)
theorem B718805 : Blo 475787 718805 := bbase (se 7 (by rfl) ⟨8423, by rfl⟩ : syracuseStep 718805 = 16847) (by norm_num)
theorem B1079261 : Blo 475787 1079261 := bbase (se 3 (by rfl) ⟨202361, by rfl⟩ : syracuseStep 1079261 = 404723) (by norm_num)
theorem B718829 : Blo 475787 718829 := bbase (se 3 (by rfl) ⟨134780, by rfl⟩ : syracuseStep 718829 = 269561) (by norm_num)
theorem B1210373 : Blo 475787 1210373 := bbase (se 4 (by rfl) ⟨113472, by rfl⟩ : syracuseStep 1210373 = 226945) (by norm_num)
theorem B718853 : Blo 475787 718853 := bbase (se 4 (by rfl) ⟨67392, by rfl⟩ : syracuseStep 718853 = 134785) (by norm_num)
theorem B718877 : Blo 475787 718877 := bbase (se 3 (by rfl) ⟨134789, by rfl⟩ : syracuseStep 718877 = 269579) (by norm_num)
theorem B1079333 : Blo 475787 1079333 := bbase (se 4 (by rfl) ⟨101187, by rfl⟩ : syracuseStep 1079333 = 202375) (by norm_num)
theorem B718901 : Blo 475787 718901 := bbase (se 5 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 718901 = 67397) (by norm_num)
theorem B718925 : Blo 475787 718925 := bbase (se 3 (by rfl) ⟨134798, by rfl⟩ : syracuseStep 718925 = 269597) (by norm_num)
theorem B718949 : Blo 475787 718949 := bbase (se 4 (by rfl) ⟨67401, by rfl⟩ : syracuseStep 718949 = 134803) (by norm_num)
theorem B1079405 : Blo 475787 1079405 := bbase (se 3 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 1079405 = 404777) (by norm_num)
theorem B718973 : Blo 475787 718973 := bbase (se 3 (by rfl) ⟨134807, by rfl⟩ : syracuseStep 718973 = 269615) (by norm_num)
theorem B718997 : Blo 475787 718997 := bbase (se 6 (by rfl) ⟨16851, by rfl⟩ : syracuseStep 718997 = 33703) (by norm_num)
theorem B719021 : Blo 475787 719021 := bbase (se 3 (by rfl) ⟨134816, by rfl⟩ : syracuseStep 719021 = 269633) (by norm_num)
theorem B1308853 : Blo 475787 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1079477 : Blo 475787 1079477 := bbase (se 5 (by rfl) ⟨50600, by rfl⟩ : syracuseStep 1079477 = 101201) (by norm_num)
theorem B1210565 : Blo 475787 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B719045 : Blo 475787 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B719069 : Blo 475787 719069 := bbase (se 3 (by rfl) ⟨134825, by rfl⟩ : syracuseStep 719069 = 269651) (by norm_num)
theorem B719093 : Blo 475787 719093 := bbase (se 5 (by rfl) ⟨33707, by rfl⟩ : syracuseStep 719093 = 67415) (by norm_num)
theorem B719117 : Blo 475787 719117 := bbase (se 3 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 719117 = 269669) (by norm_num)
theorem B719141 : Blo 475787 719141 := bbase (se 4 (by rfl) ⟨67419, by rfl⟩ : syracuseStep 719141 = 134839) (by norm_num)
theorem B719165 : Blo 475787 719165 := bbase (se 3 (by rfl) ⟨134843, by rfl⟩ : syracuseStep 719165 = 269687) (by norm_num)
theorem B719189 : Blo 475787 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B719213 : Blo 475787 719213 := bbase (se 3 (by rfl) ⟨134852, by rfl⟩ : syracuseStep 719213 = 269705) (by norm_num)
theorem B719237 : Blo 475787 719237 := bbase (se 4 (by rfl) ⟨67428, by rfl⟩ : syracuseStep 719237 = 134857) (by norm_num)
theorem B719261 : Blo 475787 719261 := bbase (se 3 (by rfl) ⟨134861, by rfl⟩ : syracuseStep 719261 = 269723) (by norm_num)
theorem B719285 : Blo 475787 719285 := bbase (se 5 (by rfl) ⟨33716, by rfl⟩ : syracuseStep 719285 = 67433) (by norm_num)
theorem B817597 : Blo 475787 817597 := bbase (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) (by norm_num)
theorem B981445 : Blo 475787 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B719309 : Blo 475787 719309 := bbase (se 3 (by rfl) ⟨134870, by rfl⟩ : syracuseStep 719309 = 269741) (by norm_num)
theorem B719333 : Blo 475787 719333 := bbase (se 4 (by rfl) ⟨67437, by rfl⟩ : syracuseStep 719333 = 134875) (by norm_num)
theorem B588269 : Blo 475787 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B719357 : Blo 475787 719357 := bbase (se 3 (by rfl) ⟨134879, by rfl⟩ : syracuseStep 719357 = 269759) (by norm_num)
theorem B719381 : Blo 475787 719381 := bbase (se 6 (by rfl) ⟨16860, by rfl⟩ : syracuseStep 719381 = 33721) (by norm_num)
theorem B1210909 : Blo 475787 1210909 := bbase (se 3 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 1210909 = 454091) (by norm_num)
theorem B719405 : Blo 475787 719405 := bbase (se 3 (by rfl) ⟨134888, by rfl⟩ : syracuseStep 719405 = 269777) (by norm_num)
theorem B3635765 : Blo 475787 3635765 := bbase (se 5 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 3635765 = 340853) (by norm_num)
theorem B719429 : Blo 475787 719429 := bbase (se 4 (by rfl) ⟨67446, by rfl⟩ : syracuseStep 719429 = 134893) (by norm_num)
theorem B719453 : Blo 475787 719453 := bbase (se 3 (by rfl) ⟨134897, by rfl⟩ : syracuseStep 719453 = 269795) (by norm_num)
theorem B719477 : Blo 475787 719477 := bbase (se 5 (by rfl) ⟨33725, by rfl⟩ : syracuseStep 719477 = 67451) (by norm_num)
theorem B1211021 : Blo 475787 1211021 := bbase (se 3 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 1211021 = 454133) (by norm_num)
theorem B719501 : Blo 475787 719501 := bbase (se 3 (by rfl) ⟨134906, by rfl⟩ : syracuseStep 719501 = 269813) (by norm_num)
theorem B719525 : Blo 475787 719525 := bbase (se 4 (by rfl) ⟨67455, by rfl⟩ : syracuseStep 719525 = 134911) (by norm_num)
theorem B719549 : Blo 475787 719549 := bbase (se 3 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 719549 = 269831) (by norm_num)
theorem B719573 : Blo 475787 719573 := bbase (se 7 (by rfl) ⟨8432, by rfl⟩ : syracuseStep 719573 = 16865) (by norm_num)
theorem B719597 : Blo 475787 719597 := bbase (se 3 (by rfl) ⟨134924, by rfl⟩ : syracuseStep 719597 = 269849) (by norm_num)
theorem B719621 : Blo 475787 719621 := bbase (se 4 (by rfl) ⟨67464, by rfl⟩ : syracuseStep 719621 = 134929) (by norm_num)
theorem B719645 : Blo 475787 719645 := bbase (se 3 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 719645 = 269867) (by norm_num)
theorem B719669 : Blo 475787 719669 := bbase (se 5 (by rfl) ⟨33734, by rfl⟩ : syracuseStep 719669 = 67469) (by norm_num)
theorem B1211213 : Blo 475787 1211213 := bbase (se 3 (by rfl) ⟨227102, by rfl⟩ : syracuseStep 1211213 = 454205) (by norm_num)
theorem B2915189 : Blo 475787 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B687037 : Blo 475787 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B818165 : Blo 475787 818165 := bbase (se 5 (by rfl) ⟨38351, by rfl⟩ : syracuseStep 818165 = 76703) (by norm_num)
theorem B2718805 : Blo 475787 2718805 := bbase (se 8 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 2718805 = 31861) (by norm_num)
theorem B1211557 : Blo 475787 1211557 := bbase (se 4 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 1211557 = 227167) (by norm_num)
theorem B4095157 : Blo 475787 4095157 := bbase (se 5 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 4095157 = 383921) (by norm_num)
theorem B2424005 : Blo 475787 2424005 := bbase (se 4 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 2424005 = 454501) (by norm_num)
theorem B2456837 : Blo 475787 2456837 := bbase (se 4 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 2456837 = 460657) (by norm_num)
theorem B1211669 : Blo 475787 1211669 := bbase (se 6 (by rfl) ⟨28398, by rfl⟩ : syracuseStep 1211669 = 56797) (by norm_num)
theorem B4914485 : Blo 475787 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B1146325 : Blo 475787 1146325 := bbase (se 7 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 1146325 = 26867) (by norm_num)
theorem B1211861 : Blo 475787 1211861 := bbase (se 7 (by rfl) ⟨14201, by rfl⟩ : syracuseStep 1211861 = 28403) (by norm_num)
theorem B4587029 : Blo 475787 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1375829 : Blo 475787 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B917237 : Blo 475787 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B1212205 : Blo 475787 1212205 := bbase (se 3 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 1212205 = 454577) (by norm_num)
theorem B1212317 : Blo 475787 1212317 := bbase (se 3 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 1212317 = 454619) (by norm_num)
theorem B2293685 : Blo 475787 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B1310833 : Blo 475787 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B4915313 : Blo 475787 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1212529 : Blo 475787 1212529 := bstep (se 2 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 1212529 = 909397) B909397
theorem B1605905 : Blo 475787 1605905 := bstep (se 2 (by rfl) ⟨602214, by rfl⟩ : syracuseStep 1605905 = 1204429) B1204429
theorem B5439797 : Blo 475787 5439797 := bstep (se 5 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 5439797 = 509981) B509981
theorem B1933645 : Blo 475787 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B1212803 : Blo 475787 1212803 := bstep (se 1 (by rfl) ⟨909602, by rfl⟩ : syracuseStep 1212803 = 1819205) B1819205
theorem B2064781 : Blo 475787 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B1212995 : Blo 475787 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B1016401 : Blo 475787 1016401 := bstep (se 2 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 1016401 = 762301) B762301
theorem B1868579 : Blo 475787 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1606445 : Blo 475787 1606445 := bstep (se 3 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 1606445 = 602417) B602417
theorem B1606499 : Blo 475787 1606499 := bstep (se 1 (by rfl) ⟨1204874, by rfl⟩ : syracuseStep 1606499 = 2409749) B2409749
theorem B918481 : Blo 475787 918481 := bstep (se 2 (by rfl) ⟨344430, by rfl⟩ : syracuseStep 918481 = 688861) B688861
theorem B1606769 : Blo 475787 1606769 := bstep (se 2 (by rfl) ⟨602538, by rfl⟩ : syracuseStep 1606769 = 1205077) B1205077
theorem B1148035 : Blo 475787 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B1246385 : Blo 475787 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B2295053 : Blo 475787 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B2590001 : Blo 475787 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B2721221 : Blo 475787 2721221 := bstep (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) B510229
theorem B1050097 : Blo 475787 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B1213937 : Blo 475787 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B1213987 : Blo 475787 1213987 := bstep (se 1 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 1213987 = 1820981) B1820981
theorem B3049073 : Blo 475787 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B1607309 : Blo 475787 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B3049123 : Blo 475787 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B1214129 : Blo 475787 1214129 := bstep (se 2 (by rfl) ⟨455298, by rfl⟩ : syracuseStep 1214129 = 910597) B910597
theorem B1607363 : Blo 475787 1607363 := bstep (se 1 (by rfl) ⟨1205522, by rfl⟩ : syracuseStep 1607363 = 2411045) B2411045
theorem B4589297 : Blo 475787 4589297 := bstep (se 2 (by rfl) ⟨1720986, by rfl⟩ : syracuseStep 4589297 = 3441973) B3441973
theorem B4097891 : Blo 475787 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B1607633 : Blo 475787 1607633 := bstep (se 2 (by rfl) ⟨602862, by rfl⟩ : syracuseStep 1607633 = 1205725) B1205725
theorem B23169077 : Blo 475787 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B2722097 : Blo 475787 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B4360517 : Blo 475787 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B1149265 : Blo 475787 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B5802353 : Blo 475787 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B1378691 : Blo 475787 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B1608173 : Blo 475787 1608173 := bstep (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) B603065
theorem B1149457 : Blo 475787 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B1608227 : Blo 475787 1608227 := bstep (se 1 (by rfl) ⟨1206170, by rfl⟩ : syracuseStep 1608227 = 2412341) B2412341
theorem B2427569 : Blo 475787 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B1608497 : Blo 475787 1608497 := bstep (se 2 (by rfl) ⟨603186, by rfl⟩ : syracuseStep 1608497 = 1206373) B1206373
theorem B1641329 : Blo 475787 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B1609037 : Blo 475787 1609037 := bstep (se 3 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 1609037 = 603389) B603389
theorem B724339 : Blo 475787 724339 := bstep (se 1 (by rfl) ⟨543254, by rfl⟩ : syracuseStep 724339 = 1086509) B1086509
theorem B1609091 : Blo 475787 1609091 := bstep (se 1 (by rfl) ⟨1206818, by rfl⟩ : syracuseStep 1609091 = 2413637) B2413637
theorem B2035277 : Blo 475787 2035277 := bstep (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) B763229
theorem B2035313 : Blo 475787 2035313 := bstep (se 2 (by rfl) ⟨763242, by rfl⟩ : syracuseStep 2035313 = 1526485) B1526485
theorem B1609361 : Blo 475787 1609361 := bstep (se 2 (by rfl) ⟨603510, by rfl⟩ : syracuseStep 1609361 = 1207021) B1207021
theorem B1019587 : Blo 475787 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B757649 : Blo 475787 757649 := bstep (se 2 (by rfl) ⟨284118, by rfl⟩ : syracuseStep 757649 = 568237) B568237
theorem B5148643 : Blo 475787 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B3051533 : Blo 475787 3051533 := bstep (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) B1144325
theorem B10293389 : Blo 475787 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B1609901 : Blo 475787 1609901 := bstep (se 3 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 1609901 = 603713) B603713
theorem B1609955 : Blo 475787 1609955 := bstep (se 1 (by rfl) ⟨1207466, by rfl⟩ : syracuseStep 1609955 = 2414933) B2414933
theorem B4886897 : Blo 475787 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B1610225 : Blo 475787 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B1020433 : Blo 475787 1020433 := bstep (se 2 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 1020433 = 765325) B765325
theorem B3642083 : Blo 475787 3642083 := bstep (se 1 (by rfl) ⟨2731562, by rfl⟩ : syracuseStep 3642083 = 5463125) B5463125
theorem B1807373 : Blo 475787 1807373 := bstep (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) B677765
theorem B1610765 : Blo 475787 1610765 := bstep (se 3 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 1610765 = 604037) B604037
theorem B1610819 : Blo 475787 1610819 := bstep (se 1 (by rfl) ⟨1208114, by rfl⟩ : syracuseStep 1610819 = 2416229) B2416229
theorem B1611089 : Blo 475787 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B4593293 : Blo 475787 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B1611629 : Blo 475787 1611629 := bstep (se 3 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 1611629 = 604361) B604361
theorem B1611683 : Blo 475787 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B727075 : Blo 475787 727075 := bstep (se 1 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 727075 = 1090613) B1090613
theorem B13080689 : Blo 475787 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B1611953 : Blo 475787 1611953 := bstep (se 2 (by rfl) ⟨604482, by rfl⟩ : syracuseStep 1611953 = 1208965) B1208965
theorem B1022321 : Blo 475787 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B1612493 : Blo 475787 1612493 := bstep (se 3 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 1612493 = 604685) B604685
theorem B1612547 : Blo 475787 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B8166257 : Blo 475787 8166257 := bstep (se 2 (by rfl) ⟨3062346, by rfl⟩ : syracuseStep 8166257 = 6124693) B6124693
theorem B662467 : Blo 475787 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B1612817 : Blo 475787 1612817 := bstep (se 2 (by rfl) ⟨604806, by rfl⟩ : syracuseStep 1612817 = 1209613) B1209613
theorem B1809485 : Blo 475787 1809485 := bstep (se 3 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 1809485 = 678557) B678557
theorem B859267 : Blo 475787 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B2727053 : Blo 475787 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B4070897 : Blo 475787 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B1613357 : Blo 475787 1613357 := bstep (se 3 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 1613357 = 605009) B605009
theorem B859729 : Blo 475787 859729 := bstep (se 2 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 859729 = 644797) B644797
theorem B1613411 : Blo 475787 1613411 := bstep (se 1 (by rfl) ⟨1210058, by rfl⟩ : syracuseStep 1613411 = 2420117) B2420117
theorem B1384049 : Blo 475787 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B1023619 : Blo 475787 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B728899 : Blo 475787 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B2039651 : Blo 475787 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810289 : Blo 475787 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1613681 : Blo 475787 1613681 := bstep (se 2 (by rfl) ⟨605130, by rfl⟩ : syracuseStep 1613681 = 1210261) B1210261
theorem B2334691 : Blo 475787 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B729089 : Blo 475787 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B1745137 : Blo 475787 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B1614221 : Blo 475787 1614221 := bstep (se 3 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 1614221 = 605333) B605333
theorem B1548739 : Blo 475787 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1614275 : Blo 475787 1614275 := bstep (se 1 (by rfl) ⟨1210706, by rfl⟩ : syracuseStep 1614275 = 2421413) B2421413
theorem B1810957 : Blo 475787 1810957 := bstep (se 3 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 1810957 = 679109) B679109
theorem B1548977 : Blo 475787 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B762563 : Blo 475787 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B1614545 : Blo 475787 1614545 := bstep (se 2 (by rfl) ⟨605454, by rfl⟩ : syracuseStep 1614545 = 1210909) B1210909
theorem B762691 : Blo 475787 762691 := bstep (se 1 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 762691 = 1144037) B1144037
theorem B1844045 : Blo 475787 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B2761613 : Blo 475787 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B762833 : Blo 475787 762833 := bstep (se 2 (by rfl) ⟨286062, by rfl⟩ : syracuseStep 762833 = 572125) B572125
theorem B1615085 : Blo 475787 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B763121 : Blo 475787 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B1811747 : Blo 475787 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1615139 : Blo 475787 1615139 := bstep (se 1 (by rfl) ⟨1211354, by rfl⟩ : syracuseStep 1615139 = 2422709) B2422709
theorem B2729285 : Blo 475787 2729285 := bstep (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) B511741
theorem B1615409 : Blo 475787 1615409 := bstep (se 2 (by rfl) ⟨605778, by rfl⟩ : syracuseStep 1615409 = 1211557) B1211557
theorem B1943459 : Blo 475787 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B1812401 : Blo 475787 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B2729969 : Blo 475787 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B763921 : Blo 475787 763921 := bstep (se 2 (by rfl) ⟨286470, by rfl⟩ : syracuseStep 763921 = 572941) B572941
theorem B1615949 : Blo 475787 1615949 := bstep (se 3 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 1615949 = 605981) B605981
theorem B862339 : Blo 475787 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B1616003 : Blo 475787 1616003 := bstep (se 1 (by rfl) ⟨1212002, by rfl⟩ : syracuseStep 1616003 = 2424005) B2424005
theorem B3058019 : Blo 475787 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B1616273 : Blo 475787 1616273 := bstep (se 2 (by rfl) ⟨606102, by rfl⟩ : syracuseStep 1616273 = 1212205) B1212205
theorem B1452593 : Blo 475787 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B535315 : Blo 475787 535315 := bstep (se 1 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 535315 = 802973) B802973
theorem B535459 : Blo 475787 535459 := bstep (se 1 (by rfl) ⟨401594, by rfl⟩ : syracuseStep 535459 = 803189) B803189
theorem B1616813 : Blo 475787 1616813 := bstep (se 3 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 1616813 = 606305) B606305
theorem B3877859 : Blo 475787 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B1616867 : Blo 475787 1616867 := bstep (se 1 (by rfl) ⟨1212650, by rfl⟩ : syracuseStep 1616867 = 2425301) B2425301
theorem B535603 : Blo 475787 535603 := bstep (se 1 (by rfl) ⟨401702, by rfl⟩ : syracuseStep 535603 = 803405) B803405
theorem B535747 : Blo 475787 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B1354961 : Blo 475787 1354961 := bstep (se 2 (by rfl) ⟨508110, by rfl⟩ : syracuseStep 1354961 = 1016221) B1016221
theorem B765139 : Blo 475787 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B1617137 : Blo 475787 1617137 := bstep (se 2 (by rfl) ⟨606426, by rfl⟩ : syracuseStep 1617137 = 1212853) B1212853
theorem B1355075 : Blo 475787 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B535891 : Blo 475787 535891 := bstep (se 1 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 535891 = 803837) B803837
theorem B1813859 : Blo 475787 1813859 := bstep (se 1 (by rfl) ⟨1360394, by rfl⟩ : syracuseStep 1813859 = 2720789) B2720789
theorem B1813873 : Blo 475787 1813873 := bstep (se 2 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 1813873 = 1360405) B1360405
theorem B2731427 : Blo 475787 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B536035 : Blo 475787 536035 := bstep (se 1 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 536035 = 804053) B804053
theorem B2043377 : Blo 475787 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B3616325 : Blo 475787 3616325 := bstep (se 4 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 3616325 = 678061) B678061
theorem B536179 : Blo 475787 536179 := bstep (se 1 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 536179 = 804269) B804269
theorem B3321485 : Blo 475787 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B5516981 : Blo 475787 5516981 := bstep (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) B517217
theorem B1453763 : Blo 475787 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B863939 : Blo 475787 863939 := bstep (se 1 (by rfl) ⟨647954, by rfl⟩ : syracuseStep 863939 = 1295909) B1295909
theorem B5451461 : Blo 475787 5451461 := bstep (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) B1022149
theorem B1650403 : Blo 475787 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B536323 : Blo 475787 536323 := bstep (se 1 (by rfl) ⟨402242, by rfl⟩ : syracuseStep 536323 = 804485) B804485
theorem B1617677 : Blo 475787 1617677 := bstep (se 3 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 1617677 = 606629) B606629
theorem B1617731 : Blo 475787 1617731 := bstep (se 1 (by rfl) ⟨1213298, by rfl⟩ : syracuseStep 1617731 = 2426597) B2426597
theorem B2895749 : Blo 475787 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B536467 : Blo 475787 536467 := bstep (se 1 (by rfl) ⟨402350, by rfl⟩ : syracuseStep 536467 = 804701) B804701
theorem B765857 : Blo 475787 765857 := bstep (se 2 (by rfl) ⟨287196, by rfl⟩ : syracuseStep 765857 = 574393) B574393
theorem B6074309 : Blo 475787 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B536611 : Blo 475787 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B1618001 : Blo 475787 1618001 := bstep (se 2 (by rfl) ⟨606750, by rfl⟩ : syracuseStep 1618001 = 1213501) B1213501
theorem B536755 : Blo 475787 536755 := bstep (se 1 (by rfl) ⟨402566, by rfl⟩ : syracuseStep 536755 = 805133) B805133
theorem B766145 : Blo 475787 766145 := bstep (se 2 (by rfl) ⟨287304, by rfl⟩ : syracuseStep 766145 = 574609) B574609
theorem B1356077 : Blo 475787 1356077 := bstep (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) B508529
theorem B3256625 : Blo 475787 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B1290545 : Blo 475787 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B536899 : Blo 475787 536899 := bstep (se 1 (by rfl) ⟨402674, by rfl⟩ : syracuseStep 536899 = 805349) B805349
theorem B766369 : Blo 475787 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B602579 : Blo 475787 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B537043 : Blo 475787 537043 := bstep (se 1 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 537043 = 805565) B805565
theorem B1356259 : Blo 475787 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B537187 : Blo 475787 537187 := bstep (se 1 (by rfl) ⟨402890, by rfl⟩ : syracuseStep 537187 = 805781) B805781
theorem B1618541 : Blo 475787 1618541 := bstep (se 3 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 1618541 = 606953) B606953
theorem B1356419 : Blo 475787 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B1618595 : Blo 475787 1618595 := bstep (se 1 (by rfl) ⟨1213946, by rfl⟩ : syracuseStep 1618595 = 2427893) B2427893
theorem B537331 : Blo 475787 537331 := bstep (se 1 (by rfl) ⟨402998, by rfl⟩ : syracuseStep 537331 = 805997) B805997
theorem B1815331 : Blo 475787 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B537475 : Blo 475787 537475 := bstep (se 1 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 537475 = 806213) B806213
theorem B1749937 : Blo 475787 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B1618865 : Blo 475787 1618865 := bstep (se 2 (by rfl) ⟨607074, by rfl⟩ : syracuseStep 1618865 = 1214149) B1214149
theorem B537619 : Blo 475787 537619 := bstep (se 1 (by rfl) ⟨403214, by rfl⟩ : syracuseStep 537619 = 806429) B806429
theorem B4600901 : Blo 475787 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B603283 : Blo 475787 603283 := bstep (se 1 (by rfl) ⟨452462, by rfl⟩ : syracuseStep 603283 = 904925) B904925
theorem B537763 : Blo 475787 537763 := bstep (se 1 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 537763 = 806645) B806645
theorem B603379 : Blo 475787 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B537907 : Blo 475787 537907 := bstep (se 1 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 537907 = 806861) B806861
theorem B538051 : Blo 475787 538051 := bstep (se 1 (by rfl) ⟨403538, by rfl⟩ : syracuseStep 538051 = 807077) B807077
theorem B538195 : Blo 475787 538195 := bstep (se 1 (by rfl) ⟨403646, by rfl⟩ : syracuseStep 538195 = 807293) B807293
theorem B3356293 : Blo 475787 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B1717901 : Blo 475787 1717901 := bstep (se 3 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 1717901 = 644213) B644213
theorem B1357489 : Blo 475787 1357489 := bstep (se 2 (by rfl) ⟨509058, by rfl⟩ : syracuseStep 1357489 = 1018117) B1018117
theorem B603875 : Blo 475787 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B538339 : Blo 475787 538339 := bstep (se 1 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 538339 = 807509) B807509
theorem B2897669 : Blo 475787 2897669 := bstep (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) B543313
theorem B538483 : Blo 475787 538483 := bstep (se 1 (by rfl) ⟨403862, by rfl⟩ : syracuseStep 538483 = 807725) B807725
theorem B2045837 : Blo 475787 2045837 := bstep (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) B767189
theorem B3061709 : Blo 475787 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B767971 : Blo 475787 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B538627 : Blo 475787 538627 := bstep (se 1 (by rfl) ⟨403970, by rfl⟩ : syracuseStep 538627 = 807941) B807941
theorem B1554509 : Blo 475787 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B538771 : Blo 475787 538771 := bstep (se 1 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 538771 = 808157) B808157
theorem B3061937 : Blo 475787 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B538915 : Blo 475787 538915 := bstep (se 1 (by rfl) ⟨404186, by rfl⟩ : syracuseStep 538915 = 808373) B808373
theorem B604579 : Blo 475787 604579 := bstep (se 1 (by rfl) ⟨453434, by rfl⟩ : syracuseStep 604579 = 906869) B906869
theorem B1292707 : Blo 475787 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B539059 : Blo 475787 539059 := bstep (se 1 (by rfl) ⟨404294, by rfl⟩ : syracuseStep 539059 = 808589) B808589
theorem B604675 : Blo 475787 604675 := bstep (se 1 (by rfl) ⟨453506, by rfl⟩ : syracuseStep 604675 = 907013) B907013
theorem B539203 : Blo 475787 539203 := bstep (se 1 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 539203 = 808805) B808805
theorem B539347 : Blo 475787 539347 := bstep (se 1 (by rfl) ⟨404510, by rfl⟩ : syracuseStep 539347 = 809021) B809021
theorem B539491 : Blo 475787 539491 := bstep (se 1 (by rfl) ⟨404618, by rfl⟩ : syracuseStep 539491 = 809237) B809237
theorem B1358765 : Blo 475787 1358765 := bstep (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) B509537
theorem B1817549 : Blo 475787 1817549 := bstep (se 3 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 1817549 = 681581) B681581
theorem B605171 : Blo 475787 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B539635 : Blo 475787 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B1293389 : Blo 475787 1293389 := bstep (se 3 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 1293389 = 485021) B485021
theorem B1358947 : Blo 475787 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B1358993 : Blo 475787 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B2047153 : Blo 475787 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B1293745 : Blo 475787 1293745 := bstep (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) B970309
theorem B605875 : Blo 475787 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B605971 : Blo 475787 605971 := bstep (se 1 (by rfl) ⟨454478, by rfl⟩ : syracuseStep 605971 = 908957) B908957
theorem B966449 : Blo 475787 966449 := bstep (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) B724837
theorem B573571 : Blo 475787 573571 := bstep (se 1 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 573571 = 860357) B860357
theorem B802993 : Blo 475787 802993 := bstep (se 2 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 802993 = 602245) B602245
theorem B803027 : Blo 475787 803027 := bstep (se 1 (by rfl) ⟨602270, by rfl⟩ : syracuseStep 803027 = 1204541) B1204541
theorem B606467 : Blo 475787 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B5161229 : Blo 475787 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B803155 : Blo 475787 803155 := bstep (se 1 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 803155 = 1204733) B1204733
theorem B1458577 : Blo 475787 1458577 := bstep (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) B1093933
theorem B1229219 : Blo 475787 1229219 := bstep (se 1 (by rfl) ⟨921914, by rfl⟩ : syracuseStep 1229219 = 1843829) B1843829
theorem B803297 : Blo 475787 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B1360451 : Blo 475787 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B1524305 : Blo 475787 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B803425 : Blo 475787 803425 := bstep (se 2 (by rfl) ⟨301284, by rfl⟩ : syracuseStep 803425 = 602569) B602569
theorem B803459 : Blo 475787 803459 := bstep (se 1 (by rfl) ⟨602594, by rfl⟩ : syracuseStep 803459 = 1205189) B1205189
theorem B2409101 : Blo 475787 2409101 := bstep (se 3 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 2409101 = 903413) B903413
theorem B475795 : Blo 475787 475795 := bstep (se 1 (by rfl) ⟨356846, by rfl⟩ : syracuseStep 475795 = 713693) B713693
theorem B475811 : Blo 475787 475811 := bstep (se 1 (by rfl) ⟨356858, by rfl⟩ : syracuseStep 475811 = 713717) B713717
theorem B475827 : Blo 475787 475827 := bstep (se 1 (by rfl) ⟨356870, by rfl⟩ : syracuseStep 475827 = 713741) B713741
theorem B475843 : Blo 475787 475843 := bstep (se 1 (by rfl) ⟨356882, by rfl⟩ : syracuseStep 475843 = 713765) B713765
theorem B475859 : Blo 475787 475859 := bstep (se 1 (by rfl) ⟨356894, by rfl⟩ : syracuseStep 475859 = 713789) B713789
theorem B475875 : Blo 475787 475875 := bstep (se 1 (by rfl) ⟨356906, by rfl⟩ : syracuseStep 475875 = 713813) B713813
theorem B475891 : Blo 475787 475891 := bstep (se 1 (by rfl) ⟨356918, by rfl⟩ : syracuseStep 475891 = 713837) B713837
theorem B475907 : Blo 475787 475907 := bstep (se 1 (by rfl) ⟨356930, by rfl⟩ : syracuseStep 475907 = 713861) B713861
theorem B803587 : Blo 475787 803587 := bstep (se 1 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 803587 = 1205381) B1205381
theorem B1721101 : Blo 475787 1721101 := bstep (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) B645413
theorem B1557265 : Blo 475787 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B475923 : Blo 475787 475923 := bstep (se 1 (by rfl) ⟨356942, by rfl⟩ : syracuseStep 475923 = 713885) B713885
theorem B475939 : Blo 475787 475939 := bstep (se 1 (by rfl) ⟨356954, by rfl⟩ : syracuseStep 475939 = 713909) B713909
theorem B1295153 : Blo 475787 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B475955 : Blo 475787 475955 := bstep (se 1 (by rfl) ⟨356966, by rfl⟩ : syracuseStep 475955 = 713933) B713933
theorem B475971 : Blo 475787 475971 := bstep (se 1 (by rfl) ⟨356978, by rfl⟩ : syracuseStep 475971 = 713957) B713957
theorem B475987 : Blo 475787 475987 := bstep (se 1 (by rfl) ⟨356990, by rfl⟩ : syracuseStep 475987 = 713981) B713981
theorem B476003 : Blo 475787 476003 := bstep (se 1 (by rfl) ⟨357002, by rfl⟩ : syracuseStep 476003 = 714005) B714005
theorem B476019 : Blo 475787 476019 := bstep (se 1 (by rfl) ⟨357014, by rfl⟩ : syracuseStep 476019 = 714029) B714029
theorem B476035 : Blo 475787 476035 := bstep (se 1 (by rfl) ⟨357026, by rfl⟩ : syracuseStep 476035 = 714053) B714053
theorem B803729 : Blo 475787 803729 := bstep (se 2 (by rfl) ⟨301398, by rfl⟩ : syracuseStep 803729 = 602797) B602797
theorem B476051 : Blo 475787 476051 := bstep (se 1 (by rfl) ⟨357038, by rfl⟩ : syracuseStep 476051 = 714077) B714077
theorem B476067 : Blo 475787 476067 := bstep (se 1 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 476067 = 714101) B714101
theorem B967601 : Blo 475787 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B476083 : Blo 475787 476083 := bstep (se 1 (by rfl) ⟨357062, by rfl⟩ : syracuseStep 476083 = 714125) B714125
theorem B476099 : Blo 475787 476099 := bstep (se 1 (by rfl) ⟨357074, by rfl⟩ : syracuseStep 476099 = 714149) B714149
theorem B607171 : Blo 475787 607171 := bstep (se 1 (by rfl) ⟨455378, by rfl⟩ : syracuseStep 607171 = 910757) B910757
theorem B476115 : Blo 475787 476115 := bstep (se 1 (by rfl) ⟨357086, by rfl⟩ : syracuseStep 476115 = 714173) B714173
theorem B476131 : Blo 475787 476131 := bstep (se 1 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 476131 = 714197) B714197
theorem B476147 : Blo 475787 476147 := bstep (se 1 (by rfl) ⟨357110, by rfl⟩ : syracuseStep 476147 = 714221) B714221
theorem B476163 : Blo 475787 476163 := bstep (se 1 (by rfl) ⟨357122, by rfl⟩ : syracuseStep 476163 = 714245) B714245
theorem B803857 : Blo 475787 803857 := bstep (se 2 (by rfl) ⟨301446, by rfl⟩ : syracuseStep 803857 = 602893) B602893
theorem B476179 : Blo 475787 476179 := bstep (se 1 (by rfl) ⟨357134, by rfl⟩ : syracuseStep 476179 = 714269) B714269
theorem B476195 : Blo 475787 476195 := bstep (se 1 (by rfl) ⟨357146, by rfl⟩ : syracuseStep 476195 = 714293) B714293
theorem B476211 : Blo 475787 476211 := bstep (se 1 (by rfl) ⟨357158, by rfl⟩ : syracuseStep 476211 = 714317) B714317
theorem B803891 : Blo 475787 803891 := bstep (se 1 (by rfl) ⟨602918, by rfl⟩ : syracuseStep 803891 = 1205837) B1205837
theorem B476227 : Blo 475787 476227 := bstep (se 1 (by rfl) ⟨357170, by rfl⟩ : syracuseStep 476227 = 714341) B714341
theorem B476243 : Blo 475787 476243 := bstep (se 1 (by rfl) ⟨357182, by rfl⟩ : syracuseStep 476243 = 714365) B714365
theorem B476259 : Blo 475787 476259 := bstep (se 1 (by rfl) ⟨357194, by rfl⟩ : syracuseStep 476259 = 714389) B714389
theorem B1524845 : Blo 475787 1524845 := bstep (se 3 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 1524845 = 571817) B571817
theorem B476275 : Blo 475787 476275 := bstep (se 1 (by rfl) ⟨357206, by rfl⟩ : syracuseStep 476275 = 714413) B714413
theorem B476291 : Blo 475787 476291 := bstep (se 1 (by rfl) ⟨357218, by rfl⟩ : syracuseStep 476291 = 714437) B714437
theorem B3687565 : Blo 475787 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B476307 : Blo 475787 476307 := bstep (se 1 (by rfl) ⟨357230, by rfl⟩ : syracuseStep 476307 = 714461) B714461
theorem B476323 : Blo 475787 476323 := bstep (se 1 (by rfl) ⟨357242, by rfl⟩ : syracuseStep 476323 = 714485) B714485
theorem B476339 : Blo 475787 476339 := bstep (se 1 (by rfl) ⟨357254, by rfl⟩ : syracuseStep 476339 = 714509) B714509
theorem B804019 : Blo 475787 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B476355 : Blo 475787 476355 := bstep (se 1 (by rfl) ⟨357266, by rfl⟩ : syracuseStep 476355 = 714533) B714533
theorem B509123 : Blo 475787 509123 := bstep (se 1 (by rfl) ⟨381842, by rfl⟩ : syracuseStep 509123 = 763685) B763685
theorem B476371 : Blo 475787 476371 := bstep (se 1 (by rfl) ⟨357278, by rfl⟩ : syracuseStep 476371 = 714557) B714557
theorem B476387 : Blo 475787 476387 := bstep (se 1 (by rfl) ⟨357290, by rfl⟩ : syracuseStep 476387 = 714581) B714581
theorem B476403 : Blo 475787 476403 := bstep (se 1 (by rfl) ⟨357302, by rfl⟩ : syracuseStep 476403 = 714605) B714605
theorem B476419 : Blo 475787 476419 := bstep (se 1 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 476419 = 714629) B714629
theorem B3622157 : Blo 475787 3622157 := bstep (se 3 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 3622157 = 1358309) B1358309
theorem B476435 : Blo 475787 476435 := bstep (se 1 (by rfl) ⟨357326, by rfl⟩ : syracuseStep 476435 = 714653) B714653
theorem B476451 : Blo 475787 476451 := bstep (se 1 (by rfl) ⟨357338, by rfl⟩ : syracuseStep 476451 = 714677) B714677
theorem B1557809 : Blo 475787 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B476467 : Blo 475787 476467 := bstep (se 1 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 476467 = 714701) B714701
theorem B804161 : Blo 475787 804161 := bstep (se 2 (by rfl) ⟨301560, by rfl⟩ : syracuseStep 804161 = 603121) B603121
theorem B476483 : Blo 475787 476483 := bstep (se 1 (by rfl) ⟨357362, by rfl⟩ : syracuseStep 476483 = 714725) B714725
theorem B476499 : Blo 475787 476499 := bstep (se 1 (by rfl) ⟨357374, by rfl⟩ : syracuseStep 476499 = 714749) B714749
theorem B476515 : Blo 475787 476515 := bstep (se 1 (by rfl) ⟨357386, by rfl⟩ : syracuseStep 476515 = 714773) B714773
theorem B476531 : Blo 475787 476531 := bstep (se 1 (by rfl) ⟨357398, by rfl⟩ : syracuseStep 476531 = 714797) B714797
theorem B476547 : Blo 475787 476547 := bstep (se 1 (by rfl) ⟨357410, by rfl⟩ : syracuseStep 476547 = 714821) B714821
theorem B5457293 : Blo 475787 5457293 := bstep (se 3 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 5457293 = 2046485) B2046485
theorem B476563 : Blo 475787 476563 := bstep (se 1 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 476563 = 714845) B714845
theorem B476579 : Blo 475787 476579 := bstep (se 1 (by rfl) ⟨357434, by rfl⟩ : syracuseStep 476579 = 714869) B714869
theorem B476595 : Blo 475787 476595 := bstep (se 1 (by rfl) ⟨357446, by rfl⟩ : syracuseStep 476595 = 714893) B714893
theorem B804289 : Blo 475787 804289 := bstep (se 2 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 804289 = 603217) B603217
theorem B476611 : Blo 475787 476611 := bstep (se 1 (by rfl) ⟨357458, by rfl⟩ : syracuseStep 476611 = 714917) B714917
theorem B476627 : Blo 475787 476627 := bstep (se 1 (by rfl) ⟨357470, by rfl⟩ : syracuseStep 476627 = 714941) B714941
theorem B804323 : Blo 475787 804323 := bstep (se 1 (by rfl) ⟨603242, by rfl⟩ : syracuseStep 804323 = 1206485) B1206485
theorem B476643 : Blo 475787 476643 := bstep (se 1 (by rfl) ⟨357482, by rfl⟩ : syracuseStep 476643 = 714965) B714965
theorem B1295843 : Blo 475787 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B476659 : Blo 475787 476659 := bstep (se 1 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 476659 = 714989) B714989
theorem B476675 : Blo 475787 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B476691 : Blo 475787 476691 := bstep (se 1 (by rfl) ⟨357518, by rfl⟩ : syracuseStep 476691 = 715037) B715037
theorem B476707 : Blo 475787 476707 := bstep (se 1 (by rfl) ⟨357530, by rfl⟩ : syracuseStep 476707 = 715061) B715061
theorem B476723 : Blo 475787 476723 := bstep (se 1 (by rfl) ⟨357542, by rfl⟩ : syracuseStep 476723 = 715085) B715085
theorem B476739 : Blo 475787 476739 := bstep (se 1 (by rfl) ⟨357554, by rfl⟩ : syracuseStep 476739 = 715109) B715109
theorem B476755 : Blo 475787 476755 := bstep (se 1 (by rfl) ⟨357566, by rfl⟩ : syracuseStep 476755 = 715133) B715133
theorem B804451 : Blo 475787 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B476771 : Blo 475787 476771 := bstep (se 1 (by rfl) ⟨357578, by rfl⟩ : syracuseStep 476771 = 715157) B715157
theorem B476787 : Blo 475787 476787 := bstep (se 1 (by rfl) ⟨357590, by rfl⟩ : syracuseStep 476787 = 715181) B715181
theorem B476803 : Blo 475787 476803 := bstep (se 1 (by rfl) ⟨357602, by rfl⟩ : syracuseStep 476803 = 715205) B715205
theorem B476819 : Blo 475787 476819 := bstep (se 1 (by rfl) ⟨357614, by rfl⟩ : syracuseStep 476819 = 715229) B715229
theorem B476835 : Blo 475787 476835 := bstep (se 1 (by rfl) ⟨357626, by rfl⟩ : syracuseStep 476835 = 715253) B715253
theorem B476851 : Blo 475787 476851 := bstep (se 1 (by rfl) ⟨357638, by rfl⟩ : syracuseStep 476851 = 715277) B715277
theorem B476867 : Blo 475787 476867 := bstep (se 1 (by rfl) ⟨357650, by rfl⟩ : syracuseStep 476867 = 715301) B715301
theorem B476883 : Blo 475787 476883 := bstep (se 1 (by rfl) ⟨357662, by rfl⟩ : syracuseStep 476883 = 715325) B715325
theorem B476899 : Blo 475787 476899 := bstep (se 1 (by rfl) ⟨357674, by rfl⟩ : syracuseStep 476899 = 715349) B715349
theorem B804593 : Blo 475787 804593 := bstep (se 2 (by rfl) ⟨301722, by rfl⟩ : syracuseStep 804593 = 603445) B603445
theorem B476915 : Blo 475787 476915 := bstep (se 1 (by rfl) ⟨357686, by rfl⟩ : syracuseStep 476915 = 715373) B715373
theorem B476931 : Blo 475787 476931 := bstep (se 1 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 476931 = 715397) B715397
theorem B1361681 : Blo 475787 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B476947 : Blo 475787 476947 := bstep (se 1 (by rfl) ⟨357710, by rfl⟩ : syracuseStep 476947 = 715421) B715421
theorem B476963 : Blo 475787 476963 := bstep (se 1 (by rfl) ⟨357722, by rfl⟩ : syracuseStep 476963 = 715445) B715445
theorem B1820465 : Blo 475787 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B476979 : Blo 475787 476979 := bstep (se 1 (by rfl) ⟨357734, by rfl⟩ : syracuseStep 476979 = 715469) B715469
theorem B476995 : Blo 475787 476995 := bstep (se 1 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 476995 = 715493) B715493
theorem B477011 : Blo 475787 477011 := bstep (se 1 (by rfl) ⟨357758, by rfl⟩ : syracuseStep 477011 = 715517) B715517
theorem B477027 : Blo 475787 477027 := bstep (se 1 (by rfl) ⟨357770, by rfl⟩ : syracuseStep 477027 = 715541) B715541
theorem B804721 : Blo 475787 804721 := bstep (se 2 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 804721 = 603541) B603541
theorem B477043 : Blo 475787 477043 := bstep (se 1 (by rfl) ⟨357782, by rfl⟩ : syracuseStep 477043 = 715565) B715565
theorem B477059 : Blo 475787 477059 := bstep (se 1 (by rfl) ⟨357794, by rfl⟩ : syracuseStep 477059 = 715589) B715589
theorem B804755 : Blo 475787 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B477075 : Blo 475787 477075 := bstep (se 1 (by rfl) ⟨357806, by rfl⟩ : syracuseStep 477075 = 715613) B715613
theorem B477091 : Blo 475787 477091 := bstep (se 1 (by rfl) ⟨357818, by rfl⟩ : syracuseStep 477091 = 715637) B715637
theorem B477107 : Blo 475787 477107 := bstep (se 1 (by rfl) ⟨357830, by rfl⟩ : syracuseStep 477107 = 715661) B715661
theorem B477123 : Blo 475787 477123 := bstep (se 1 (by rfl) ⟨357842, by rfl⟩ : syracuseStep 477123 = 715685) B715685
theorem B477139 : Blo 475787 477139 := bstep (se 1 (by rfl) ⟨357854, by rfl⟩ : syracuseStep 477139 = 715709) B715709
theorem B477155 : Blo 475787 477155 := bstep (se 1 (by rfl) ⟨357866, by rfl⟩ : syracuseStep 477155 = 715733) B715733
theorem B477171 : Blo 475787 477171 := bstep (se 1 (by rfl) ⟨357878, by rfl⟩ : syracuseStep 477171 = 715757) B715757
theorem B477187 : Blo 475787 477187 := bstep (se 1 (by rfl) ⟨357890, by rfl⟩ : syracuseStep 477187 = 715781) B715781
theorem B804883 : Blo 475787 804883 := bstep (se 1 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 804883 = 1207325) B1207325
theorem B477203 : Blo 475787 477203 := bstep (se 1 (by rfl) ⟨357902, by rfl⟩ : syracuseStep 477203 = 715805) B715805
theorem B477219 : Blo 475787 477219 := bstep (se 1 (by rfl) ⟨357914, by rfl⟩ : syracuseStep 477219 = 715829) B715829
theorem B968753 : Blo 475787 968753 := bstep (se 2 (by rfl) ⟨363282, by rfl⟩ : syracuseStep 968753 = 726565) B726565
theorem B477235 : Blo 475787 477235 := bstep (se 1 (by rfl) ⟨357926, by rfl⟩ : syracuseStep 477235 = 715853) B715853
theorem B477251 : Blo 475787 477251 := bstep (se 1 (by rfl) ⟨357938, by rfl⟩ : syracuseStep 477251 = 715877) B715877
theorem B477267 : Blo 475787 477267 := bstep (se 1 (by rfl) ⟨357950, by rfl⟩ : syracuseStep 477267 = 715901) B715901
theorem B477283 : Blo 475787 477283 := bstep (se 1 (by rfl) ⟨357962, by rfl⟩ : syracuseStep 477283 = 715925) B715925
theorem B477299 : Blo 475787 477299 := bstep (se 1 (by rfl) ⟨357974, by rfl⟩ : syracuseStep 477299 = 715949) B715949
theorem B510067 : Blo 475787 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B477315 : Blo 475787 477315 := bstep (se 1 (by rfl) ⟨357986, by rfl⟩ : syracuseStep 477315 = 715973) B715973
theorem B477331 : Blo 475787 477331 := bstep (se 1 (by rfl) ⟨357998, by rfl⟩ : syracuseStep 477331 = 715997) B715997
theorem B805025 : Blo 475787 805025 := bstep (se 2 (by rfl) ⟨301884, by rfl⟩ : syracuseStep 805025 = 603769) B603769
theorem B477347 : Blo 475787 477347 := bstep (se 1 (by rfl) ⟨358010, by rfl⟩ : syracuseStep 477347 = 716021) B716021
theorem B575651 : Blo 475787 575651 := bstep (se 1 (by rfl) ⟨431738, by rfl⟩ : syracuseStep 575651 = 863477) B863477
theorem B477363 : Blo 475787 477363 := bstep (se 1 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 477363 = 716045) B716045
theorem B477379 : Blo 475787 477379 := bstep (se 1 (by rfl) ⟨358034, by rfl⟩ : syracuseStep 477379 = 716069) B716069
theorem B477395 : Blo 475787 477395 := bstep (se 1 (by rfl) ⟨358046, by rfl⟩ : syracuseStep 477395 = 716093) B716093
theorem B477411 : Blo 475787 477411 := bstep (se 1 (by rfl) ⟨358058, by rfl⟩ : syracuseStep 477411 = 716117) B716117
theorem B1165553 : Blo 475787 1165553 := bstep (se 2 (by rfl) ⟨437082, by rfl⟩ : syracuseStep 1165553 = 874165) B874165
theorem B477427 : Blo 475787 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B477443 : Blo 475787 477443 := bstep (se 1 (by rfl) ⟨358082, by rfl⟩ : syracuseStep 477443 = 716165) B716165
theorem B477459 : Blo 475787 477459 := bstep (se 1 (by rfl) ⟨358094, by rfl⟩ : syracuseStep 477459 = 716189) B716189
theorem B805153 : Blo 475787 805153 := bstep (se 2 (by rfl) ⟨301932, by rfl⟩ : syracuseStep 805153 = 603865) B603865
theorem B477475 : Blo 475787 477475 := bstep (se 1 (by rfl) ⟨358106, by rfl⟩ : syracuseStep 477475 = 716213) B716213
theorem B477491 : Blo 475787 477491 := bstep (se 1 (by rfl) ⟨358118, by rfl⟩ : syracuseStep 477491 = 716237) B716237
theorem B805187 : Blo 475787 805187 := bstep (se 1 (by rfl) ⟨603890, by rfl⟩ : syracuseStep 805187 = 1207781) B1207781
theorem B477507 : Blo 475787 477507 := bstep (se 1 (by rfl) ⟨358130, by rfl⟩ : syracuseStep 477507 = 716261) B716261
theorem B477523 : Blo 475787 477523 := bstep (se 1 (by rfl) ⟨358142, by rfl⟩ : syracuseStep 477523 = 716285) B716285
theorem B477539 : Blo 475787 477539 := bstep (se 1 (by rfl) ⟨358154, by rfl⟩ : syracuseStep 477539 = 716309) B716309
theorem B477555 : Blo 475787 477555 := bstep (se 1 (by rfl) ⟨358166, by rfl⟩ : syracuseStep 477555 = 716333) B716333
theorem B477571 : Blo 475787 477571 := bstep (se 1 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 477571 = 716357) B716357
theorem B477587 : Blo 475787 477587 := bstep (se 1 (by rfl) ⟨358190, by rfl⟩ : syracuseStep 477587 = 716381) B716381
theorem B477603 : Blo 475787 477603 := bstep (se 1 (by rfl) ⟨358202, by rfl⟩ : syracuseStep 477603 = 716405) B716405
theorem B477619 : Blo 475787 477619 := bstep (se 1 (by rfl) ⟨358214, by rfl⟩ : syracuseStep 477619 = 716429) B716429
theorem B805315 : Blo 475787 805315 := bstep (se 1 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 805315 = 1207973) B1207973
theorem B477635 : Blo 475787 477635 := bstep (se 1 (by rfl) ⟨358226, by rfl⟩ : syracuseStep 477635 = 716453) B716453
theorem B1165763 : Blo 475787 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B477651 : Blo 475787 477651 := bstep (se 1 (by rfl) ⟨358238, by rfl⟩ : syracuseStep 477651 = 716477) B716477
theorem B477667 : Blo 475787 477667 := bstep (se 1 (by rfl) ⟨358250, by rfl⟩ : syracuseStep 477667 = 716501) B716501
theorem B477683 : Blo 475787 477683 := bstep (se 1 (by rfl) ⟨358262, by rfl⟩ : syracuseStep 477683 = 716525) B716525
theorem B477699 : Blo 475787 477699 := bstep (se 1 (by rfl) ⟨358274, by rfl⟩ : syracuseStep 477699 = 716549) B716549
theorem B477715 : Blo 475787 477715 := bstep (se 1 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 477715 = 716573) B716573
theorem B477731 : Blo 475787 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B477747 : Blo 475787 477747 := bstep (se 1 (by rfl) ⟨358310, by rfl⟩ : syracuseStep 477747 = 716621) B716621
theorem B477763 : Blo 475787 477763 := bstep (se 1 (by rfl) ⟨358322, by rfl⟩ : syracuseStep 477763 = 716645) B716645
theorem B805457 : Blo 475787 805457 := bstep (se 2 (by rfl) ⟨302046, by rfl⟩ : syracuseStep 805457 = 604093) B604093
theorem B477779 : Blo 475787 477779 := bstep (se 1 (by rfl) ⟨358334, by rfl⟩ : syracuseStep 477779 = 716669) B716669
theorem B477795 : Blo 475787 477795 := bstep (se 1 (by rfl) ⟨358346, by rfl⟩ : syracuseStep 477795 = 716693) B716693
theorem B903793 : Blo 475787 903793 := bstep (se 2 (by rfl) ⟨338922, by rfl⟩ : syracuseStep 903793 = 677845) B677845
theorem B477811 : Blo 475787 477811 := bstep (se 1 (by rfl) ⟨358358, by rfl⟩ : syracuseStep 477811 = 716717) B716717
theorem B477827 : Blo 475787 477827 := bstep (se 1 (by rfl) ⟨358370, by rfl⟩ : syracuseStep 477827 = 716741) B716741
theorem B4573837 : Blo 475787 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B477843 : Blo 475787 477843 := bstep (se 1 (by rfl) ⟨358382, by rfl⟩ : syracuseStep 477843 = 716765) B716765
theorem B477859 : Blo 475787 477859 := bstep (se 1 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 477859 = 716789) B716789
theorem B477875 : Blo 475787 477875 := bstep (se 1 (by rfl) ⟨358406, by rfl⟩ : syracuseStep 477875 = 716813) B716813
theorem B477891 : Blo 475787 477891 := bstep (se 1 (by rfl) ⟨358418, by rfl⟩ : syracuseStep 477891 = 716837) B716837
theorem B805585 : Blo 475787 805585 := bstep (se 2 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 805585 = 604189) B604189
theorem B477907 : Blo 475787 477907 := bstep (se 1 (by rfl) ⟨358430, by rfl⟩ : syracuseStep 477907 = 716861) B716861
theorem B477923 : Blo 475787 477923 := bstep (se 1 (by rfl) ⟨358442, by rfl⟩ : syracuseStep 477923 = 716885) B716885
theorem B805619 : Blo 475787 805619 := bstep (se 1 (by rfl) ⟨604214, by rfl⟩ : syracuseStep 805619 = 1208429) B1208429
theorem B477939 : Blo 475787 477939 := bstep (se 1 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 477939 = 716909) B716909
theorem B477955 : Blo 475787 477955 := bstep (se 1 (by rfl) ⟨358466, by rfl⟩ : syracuseStep 477955 = 716933) B716933
theorem B1886989 : Blo 475787 1886989 := bstep (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) B707621
theorem B903953 : Blo 475787 903953 := bstep (se 2 (by rfl) ⟨338982, by rfl⟩ : syracuseStep 903953 = 677965) B677965
theorem B477971 : Blo 475787 477971 := bstep (se 1 (by rfl) ⟨358478, by rfl⟩ : syracuseStep 477971 = 716957) B716957
theorem B477987 : Blo 475787 477987 := bstep (se 1 (by rfl) ⟨358490, by rfl⟩ : syracuseStep 477987 = 716981) B716981
theorem B478003 : Blo 475787 478003 := bstep (se 1 (by rfl) ⟨358502, by rfl⟩ : syracuseStep 478003 = 717005) B717005
theorem B707395 : Blo 475787 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B478019 : Blo 475787 478019 := bstep (se 1 (by rfl) ⟨358514, by rfl⟩ : syracuseStep 478019 = 717029) B717029
theorem B478035 : Blo 475787 478035 := bstep (se 1 (by rfl) ⟨358526, by rfl⟩ : syracuseStep 478035 = 717053) B717053
theorem B478051 : Blo 475787 478051 := bstep (se 1 (by rfl) ⟨358538, by rfl⟩ : syracuseStep 478051 = 717077) B717077
theorem B805747 : Blo 475787 805747 := bstep (se 1 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 805747 = 1208621) B1208621
theorem B478067 : Blo 475787 478067 := bstep (se 1 (by rfl) ⟨358550, by rfl⟩ : syracuseStep 478067 = 717101) B717101
theorem B478083 : Blo 475787 478083 := bstep (se 1 (by rfl) ⟨358562, by rfl⟩ : syracuseStep 478083 = 717125) B717125
theorem B478099 : Blo 475787 478099 := bstep (se 1 (by rfl) ⟨358574, by rfl⟩ : syracuseStep 478099 = 717149) B717149
theorem B478115 : Blo 475787 478115 := bstep (se 1 (by rfl) ⟨358586, by rfl⟩ : syracuseStep 478115 = 717173) B717173
theorem B478131 : Blo 475787 478131 := bstep (se 1 (by rfl) ⟨358598, by rfl⟩ : syracuseStep 478131 = 717197) B717197
theorem B478147 : Blo 475787 478147 := bstep (se 1 (by rfl) ⟨358610, by rfl⟩ : syracuseStep 478147 = 717221) B717221
theorem B478163 : Blo 475787 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B478179 : Blo 475787 478179 := bstep (se 1 (by rfl) ⟨358634, by rfl⟩ : syracuseStep 478179 = 717269) B717269
theorem B478195 : Blo 475787 478195 := bstep (se 1 (by rfl) ⟨358646, by rfl⟩ : syracuseStep 478195 = 717293) B717293
theorem B805889 : Blo 475787 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B478211 : Blo 475787 478211 := bstep (se 1 (by rfl) ⟨358658, by rfl⟩ : syracuseStep 478211 = 717317) B717317
theorem B478227 : Blo 475787 478227 := bstep (se 1 (by rfl) ⟨358670, by rfl⟩ : syracuseStep 478227 = 717341) B717341
theorem B478243 : Blo 475787 478243 := bstep (se 1 (by rfl) ⟨358682, by rfl⟩ : syracuseStep 478243 = 717365) B717365
theorem B478259 : Blo 475787 478259 := bstep (se 1 (by rfl) ⟨358694, by rfl⟩ : syracuseStep 478259 = 717389) B717389
theorem B478275 : Blo 475787 478275 := bstep (se 1 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 478275 = 717413) B717413
theorem B478291 : Blo 475787 478291 := bstep (se 1 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 478291 = 717437) B717437
theorem B478307 : Blo 475787 478307 := bstep (se 1 (by rfl) ⟨358730, by rfl⟩ : syracuseStep 478307 = 717461) B717461
theorem B478323 : Blo 475787 478323 := bstep (se 1 (by rfl) ⟨358742, by rfl⟩ : syracuseStep 478323 = 717485) B717485
theorem B806017 : Blo 475787 806017 := bstep (se 2 (by rfl) ⟨302256, by rfl⟩ : syracuseStep 806017 = 604513) B604513
theorem B478339 : Blo 475787 478339 := bstep (se 1 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 478339 = 717509) B717509
theorem B478355 : Blo 475787 478355 := bstep (se 1 (by rfl) ⟨358766, by rfl⟩ : syracuseStep 478355 = 717533) B717533
theorem B904355 : Blo 475787 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B806051 : Blo 475787 806051 := bstep (se 1 (by rfl) ⟨604538, by rfl⟩ : syracuseStep 806051 = 1209077) B1209077
theorem B478371 : Blo 475787 478371 := bstep (se 1 (by rfl) ⟨358778, by rfl⟩ : syracuseStep 478371 = 717557) B717557
theorem B478387 : Blo 475787 478387 := bstep (se 1 (by rfl) ⟨358790, by rfl⟩ : syracuseStep 478387 = 717581) B717581
theorem B478403 : Blo 475787 478403 := bstep (se 1 (by rfl) ⟨358802, by rfl⟩ : syracuseStep 478403 = 717605) B717605
theorem B1363139 : Blo 475787 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B478419 : Blo 475787 478419 := bstep (se 1 (by rfl) ⟨358814, by rfl⟩ : syracuseStep 478419 = 717629) B717629
theorem B478435 : Blo 475787 478435 := bstep (se 1 (by rfl) ⟨358826, by rfl⟩ : syracuseStep 478435 = 717653) B717653
theorem B478451 : Blo 475787 478451 := bstep (se 1 (by rfl) ⟨358838, by rfl⟩ : syracuseStep 478451 = 717677) B717677
theorem B478467 : Blo 475787 478467 := bstep (se 1 (by rfl) ⟨358850, by rfl⟩ : syracuseStep 478467 = 717701) B717701
theorem B478483 : Blo 475787 478483 := bstep (se 1 (by rfl) ⟨358862, by rfl⟩ : syracuseStep 478483 = 717725) B717725
theorem B806179 : Blo 475787 806179 := bstep (se 1 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 806179 = 1209269) B1209269
theorem B478499 : Blo 475787 478499 := bstep (se 1 (by rfl) ⟨358874, by rfl⟩ : syracuseStep 478499 = 717749) B717749
theorem B478515 : Blo 475787 478515 := bstep (se 1 (by rfl) ⟨358886, by rfl⟩ : syracuseStep 478515 = 717773) B717773
theorem B478531 : Blo 475787 478531 := bstep (se 1 (by rfl) ⟨358898, by rfl⟩ : syracuseStep 478531 = 717797) B717797
theorem B478547 : Blo 475787 478547 := bstep (se 1 (by rfl) ⟨358910, by rfl⟩ : syracuseStep 478547 = 717821) B717821
theorem B511331 : Blo 475787 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B478563 : Blo 475787 478563 := bstep (se 1 (by rfl) ⟨358922, by rfl⟩ : syracuseStep 478563 = 717845) B717845
theorem B478579 : Blo 475787 478579 := bstep (se 1 (by rfl) ⟨358934, by rfl⟩ : syracuseStep 478579 = 717869) B717869
theorem B478595 : Blo 475787 478595 := bstep (se 1 (by rfl) ⟨358946, by rfl⟩ : syracuseStep 478595 = 717893) B717893
theorem B478611 : Blo 475787 478611 := bstep (se 1 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 478611 = 717917) B717917
theorem B478627 : Blo 475787 478627 := bstep (se 1 (by rfl) ⟨358970, by rfl⟩ : syracuseStep 478627 = 717941) B717941
theorem B806321 : Blo 475787 806321 := bstep (se 2 (by rfl) ⟨302370, by rfl⟩ : syracuseStep 806321 = 604741) B604741
theorem B478643 : Blo 475787 478643 := bstep (se 1 (by rfl) ⟨358982, by rfl⟩ : syracuseStep 478643 = 717965) B717965
theorem B478659 : Blo 475787 478659 := bstep (se 1 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 478659 = 717989) B717989
theorem B478675 : Blo 475787 478675 := bstep (se 1 (by rfl) ⟨359006, by rfl⟩ : syracuseStep 478675 = 718013) B718013
theorem B478691 : Blo 475787 478691 := bstep (se 1 (by rfl) ⟨359018, by rfl⟩ : syracuseStep 478691 = 718037) B718037
theorem B2412017 : Blo 475787 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B478707 : Blo 475787 478707 := bstep (se 1 (by rfl) ⟨359030, by rfl⟩ : syracuseStep 478707 = 718061) B718061
theorem B478723 : Blo 475787 478723 := bstep (se 1 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 478723 = 718085) B718085
theorem B478739 : Blo 475787 478739 := bstep (se 1 (by rfl) ⟨359054, by rfl⟩ : syracuseStep 478739 = 718109) B718109
theorem B478755 : Blo 475787 478755 := bstep (se 1 (by rfl) ⟨359066, by rfl⟩ : syracuseStep 478755 = 718133) B718133
theorem B806449 : Blo 475787 806449 := bstep (se 2 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 806449 = 604837) B604837
theorem B478771 : Blo 475787 478771 := bstep (se 1 (by rfl) ⟨359078, by rfl⟩ : syracuseStep 478771 = 718157) B718157
theorem B478787 : Blo 475787 478787 := bstep (se 1 (by rfl) ⟨359090, by rfl⟩ : syracuseStep 478787 = 718181) B718181
theorem B544339 : Blo 475787 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B806483 : Blo 475787 806483 := bstep (se 1 (by rfl) ⟨604862, by rfl⟩ : syracuseStep 806483 = 1209725) B1209725
theorem B478803 : Blo 475787 478803 := bstep (se 1 (by rfl) ⟨359102, by rfl⟩ : syracuseStep 478803 = 718205) B718205
theorem B478819 : Blo 475787 478819 := bstep (se 1 (by rfl) ⟨359114, by rfl⟩ : syracuseStep 478819 = 718229) B718229
theorem B478835 : Blo 475787 478835 := bstep (se 1 (by rfl) ⟨359126, by rfl⟩ : syracuseStep 478835 = 718253) B718253
theorem B478851 : Blo 475787 478851 := bstep (se 1 (by rfl) ⟨359138, by rfl⟩ : syracuseStep 478851 = 718277) B718277
theorem B478867 : Blo 475787 478867 := bstep (se 1 (by rfl) ⟨359150, by rfl⟩ : syracuseStep 478867 = 718301) B718301
theorem B478883 : Blo 475787 478883 := bstep (se 1 (by rfl) ⟨359162, by rfl⟩ : syracuseStep 478883 = 718325) B718325
theorem B478899 : Blo 475787 478899 := bstep (se 1 (by rfl) ⟨359174, by rfl⟩ : syracuseStep 478899 = 718349) B718349
theorem B478915 : Blo 475787 478915 := bstep (se 1 (by rfl) ⟨359186, by rfl⟩ : syracuseStep 478915 = 718373) B718373
theorem B806611 : Blo 475787 806611 := bstep (se 1 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 806611 = 1209917) B1209917
theorem B478931 : Blo 475787 478931 := bstep (se 1 (by rfl) ⟨359198, by rfl⟩ : syracuseStep 478931 = 718397) B718397
theorem B478947 : Blo 475787 478947 := bstep (se 1 (by rfl) ⟨359210, by rfl⟩ : syracuseStep 478947 = 718421) B718421
theorem B478963 : Blo 475787 478963 := bstep (se 1 (by rfl) ⟨359222, by rfl⟩ : syracuseStep 478963 = 718445) B718445
theorem B478979 : Blo 475787 478979 := bstep (se 1 (by rfl) ⟨359234, by rfl⟩ : syracuseStep 478979 = 718469) B718469
theorem B478995 : Blo 475787 478995 := bstep (se 1 (by rfl) ⟨359246, by rfl⟩ : syracuseStep 478995 = 718493) B718493
theorem B479011 : Blo 475787 479011 := bstep (se 1 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 479011 = 718517) B718517
theorem B479027 : Blo 475787 479027 := bstep (se 1 (by rfl) ⟨359270, by rfl⟩ : syracuseStep 479027 = 718541) B718541
theorem B479043 : Blo 475787 479043 := bstep (se 1 (by rfl) ⟨359282, by rfl⟩ : syracuseStep 479043 = 718565) B718565
theorem B479059 : Blo 475787 479059 := bstep (se 1 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 479059 = 718589) B718589
theorem B806753 : Blo 475787 806753 := bstep (se 2 (by rfl) ⟨302532, by rfl⟩ : syracuseStep 806753 = 605065) B605065
theorem B479075 : Blo 475787 479075 := bstep (se 1 (by rfl) ⟨359306, by rfl⟩ : syracuseStep 479075 = 718613) B718613
theorem B479091 : Blo 475787 479091 := bstep (se 1 (by rfl) ⟨359318, by rfl⟩ : syracuseStep 479091 = 718637) B718637
theorem B479107 : Blo 475787 479107 := bstep (se 1 (by rfl) ⟨359330, by rfl⟩ : syracuseStep 479107 = 718661) B718661
theorem B479123 : Blo 475787 479123 := bstep (se 1 (by rfl) ⟨359342, by rfl⟩ : syracuseStep 479123 = 718685) B718685
theorem B479139 : Blo 475787 479139 := bstep (se 1 (by rfl) ⟨359354, by rfl⟩ : syracuseStep 479139 = 718709) B718709
theorem B479155 : Blo 475787 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B479171 : Blo 475787 479171 := bstep (se 1 (by rfl) ⟨359378, by rfl⟩ : syracuseStep 479171 = 718757) B718757
theorem B479187 : Blo 475787 479187 := bstep (se 1 (by rfl) ⟨359390, by rfl⟩ : syracuseStep 479187 = 718781) B718781
theorem B806881 : Blo 475787 806881 := bstep (se 2 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 806881 = 605161) B605161
theorem B479203 : Blo 475787 479203 := bstep (se 1 (by rfl) ⟨359402, by rfl⟩ : syracuseStep 479203 = 718805) B718805
theorem B1363949 : Blo 475787 1363949 := bstep (se 3 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 1363949 = 511481) B511481
theorem B479219 : Blo 475787 479219 := bstep (se 1 (by rfl) ⟨359414, by rfl⟩ : syracuseStep 479219 = 718829) B718829
theorem B806915 : Blo 475787 806915 := bstep (se 1 (by rfl) ⟨605186, by rfl⟩ : syracuseStep 806915 = 1210373) B1210373
theorem B479235 : Blo 475787 479235 := bstep (se 1 (by rfl) ⟨359426, by rfl⟩ : syracuseStep 479235 = 718853) B718853
theorem B479251 : Blo 475787 479251 := bstep (se 1 (by rfl) ⟨359438, by rfl⟩ : syracuseStep 479251 = 718877) B718877
theorem B905251 : Blo 475787 905251 := bstep (se 1 (by rfl) ⟨678938, by rfl⟩ : syracuseStep 905251 = 1357877) B1357877
theorem B479267 : Blo 475787 479267 := bstep (se 1 (by rfl) ⟨359450, by rfl⟩ : syracuseStep 479267 = 718901) B718901
theorem B479283 : Blo 475787 479283 := bstep (se 1 (by rfl) ⟨359462, by rfl⟩ : syracuseStep 479283 = 718925) B718925
theorem B479299 : Blo 475787 479299 := bstep (se 1 (by rfl) ⟨359474, by rfl⟩ : syracuseStep 479299 = 718949) B718949
theorem B479315 : Blo 475787 479315 := bstep (se 1 (by rfl) ⟨359486, by rfl⟩ : syracuseStep 479315 = 718973) B718973
theorem B512083 : Blo 475787 512083 := bstep (se 1 (by rfl) ⟨384062, by rfl⟩ : syracuseStep 512083 = 768125) B768125
theorem B479331 : Blo 475787 479331 := bstep (se 1 (by rfl) ⟨359498, by rfl⟩ : syracuseStep 479331 = 718997) B718997
theorem B3625073 : Blo 475787 3625073 := bstep (se 2 (by rfl) ⟨1359402, by rfl⟩ : syracuseStep 3625073 = 2718805) B2718805
theorem B479347 : Blo 475787 479347 := bstep (se 1 (by rfl) ⟨359510, by rfl⟩ : syracuseStep 479347 = 719021) B719021
theorem B807043 : Blo 475787 807043 := bstep (se 1 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 807043 = 1210565) B1210565
theorem B479363 : Blo 475787 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B479379 : Blo 475787 479379 := bstep (se 1 (by rfl) ⟨359534, by rfl⟩ : syracuseStep 479379 = 719069) B719069
theorem B479395 : Blo 475787 479395 := bstep (se 1 (by rfl) ⟨359546, by rfl⟩ : syracuseStep 479395 = 719093) B719093
theorem B1364141 : Blo 475787 1364141 := bstep (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) B511553
theorem B479411 : Blo 475787 479411 := bstep (se 1 (by rfl) ⟨359558, by rfl⟩ : syracuseStep 479411 = 719117) B719117
theorem B905411 : Blo 475787 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B479427 : Blo 475787 479427 := bstep (se 1 (by rfl) ⟨359570, by rfl⟩ : syracuseStep 479427 = 719141) B719141
theorem B479443 : Blo 475787 479443 := bstep (se 1 (by rfl) ⟨359582, by rfl⟩ : syracuseStep 479443 = 719165) B719165
theorem B479459 : Blo 475787 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B5460209 : Blo 475787 5460209 := bstep (se 2 (by rfl) ⟨2047578, by rfl⟩ : syracuseStep 5460209 = 4095157) B4095157
theorem B479475 : Blo 475787 479475 := bstep (se 1 (by rfl) ⟨359606, by rfl⟩ : syracuseStep 479475 = 719213) B719213
theorem B479491 : Blo 475787 479491 := bstep (se 1 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 479491 = 719237) B719237
theorem B807185 : Blo 475787 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B479507 : Blo 475787 479507 := bstep (se 1 (by rfl) ⟨359630, by rfl⟩ : syracuseStep 479507 = 719261) B719261
theorem B479523 : Blo 475787 479523 := bstep (se 1 (by rfl) ⟨359642, by rfl⟩ : syracuseStep 479523 = 719285) B719285
theorem B479539 : Blo 475787 479539 := bstep (se 1 (by rfl) ⟨359654, by rfl⟩ : syracuseStep 479539 = 719309) B719309
theorem B479555 : Blo 475787 479555 := bstep (se 1 (by rfl) ⟨359666, by rfl⟩ : syracuseStep 479555 = 719333) B719333
theorem B479571 : Blo 475787 479571 := bstep (se 1 (by rfl) ⟨359678, by rfl⟩ : syracuseStep 479571 = 719357) B719357
theorem B512339 : Blo 475787 512339 := bstep (se 1 (by rfl) ⟨384254, by rfl⟩ : syracuseStep 512339 = 768509) B768509
theorem B479587 : Blo 475787 479587 := bstep (se 1 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 479587 = 719381) B719381
theorem B479603 : Blo 475787 479603 := bstep (se 1 (by rfl) ⟨359702, by rfl⟩ : syracuseStep 479603 = 719405) B719405
theorem B479619 : Blo 475787 479619 := bstep (se 1 (by rfl) ⟨359714, by rfl⟩ : syracuseStep 479619 = 719429) B719429
theorem B3068293 : Blo 475787 3068293 := bstep (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) B575305
theorem B807313 : Blo 475787 807313 := bstep (se 2 (by rfl) ⟨302742, by rfl⟩ : syracuseStep 807313 = 605485) B605485
theorem B479635 : Blo 475787 479635 := bstep (se 1 (by rfl) ⟨359726, by rfl⟩ : syracuseStep 479635 = 719453) B719453
theorem B479651 : Blo 475787 479651 := bstep (se 1 (by rfl) ⟨359738, by rfl⟩ : syracuseStep 479651 = 719477) B719477
theorem B807347 : Blo 475787 807347 := bstep (se 1 (by rfl) ⟨605510, by rfl⟩ : syracuseStep 807347 = 1211021) B1211021
theorem B479667 : Blo 475787 479667 := bstep (se 1 (by rfl) ⟨359750, by rfl⟩ : syracuseStep 479667 = 719501) B719501
theorem B1036739 : Blo 475787 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B479683 : Blo 475787 479683 := bstep (se 1 (by rfl) ⟨359762, by rfl⟩ : syracuseStep 479683 = 719525) B719525
theorem B479699 : Blo 475787 479699 := bstep (se 1 (by rfl) ⟨359774, by rfl⟩ : syracuseStep 479699 = 719549) B719549
theorem B479715 : Blo 475787 479715 := bstep (se 1 (by rfl) ⟨359786, by rfl⟩ : syracuseStep 479715 = 719573) B719573
theorem B479731 : Blo 475787 479731 := bstep (se 1 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 479731 = 719597) B719597
theorem B479747 : Blo 475787 479747 := bstep (se 1 (by rfl) ⟨359810, by rfl⟩ : syracuseStep 479747 = 719621) B719621
theorem B479763 : Blo 475787 479763 := bstep (se 1 (by rfl) ⟨359822, by rfl⟩ : syracuseStep 479763 = 719645) B719645
theorem B479779 : Blo 475787 479779 := bstep (se 1 (by rfl) ⟨359834, by rfl⟩ : syracuseStep 479779 = 719669) B719669
theorem B807475 : Blo 475787 807475 := bstep (se 1 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 807475 = 1211213) B1211213
theorem B1528433 : Blo 475787 1528433 := bstep (se 2 (by rfl) ⟨573162, by rfl⟩ : syracuseStep 1528433 = 1146325) B1146325
theorem B545443 : Blo 475787 545443 := bstep (se 1 (by rfl) ⟨409082, by rfl⟩ : syracuseStep 545443 = 818165) B818165
theorem B807617 : Blo 475787 807617 := bstep (se 2 (by rfl) ⟨302856, by rfl⟩ : syracuseStep 807617 = 605713) B605713
theorem B807745 : Blo 475787 807745 := bstep (se 2 (by rfl) ⟨302904, by rfl⟩ : syracuseStep 807745 = 605809) B605809
theorem B807779 : Blo 475787 807779 := bstep (se 1 (by rfl) ⟨605834, by rfl⟩ : syracuseStep 807779 = 1211669) B1211669
theorem B2413475 : Blo 475787 2413475 := bstep (se 1 (by rfl) ⟨1810106, by rfl⟩ : syracuseStep 2413475 = 3620213) B3620213
theorem B807907 : Blo 475787 807907 := bstep (se 1 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 807907 = 1211861) B1211861
theorem B808049 : Blo 475787 808049 := bstep (se 2 (by rfl) ⟨303018, by rfl⟩ : syracuseStep 808049 = 606037) B606037
theorem B1365133 : Blo 475787 1365133 := bstep (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) B511925
theorem B611491 : Blo 475787 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B906481 : Blo 475787 906481 := bstep (se 2 (by rfl) ⟨339930, by rfl⟩ : syracuseStep 906481 = 679861) B679861
theorem B808177 : Blo 475787 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B808211 : Blo 475787 808211 := bstep (se 1 (by rfl) ⟨606158, by rfl⟩ : syracuseStep 808211 = 1212317) B1212317
theorem B1529123 : Blo 475787 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B2446733 : Blo 475787 2446733 := bstep (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) B917525
theorem B808339 : Blo 475787 808339 := bstep (se 1 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 808339 = 1212509) B1212509
theorem B1070531 : Blo 475787 1070531 := bstep (se 1 (by rfl) ⟨802898, by rfl⟩ : syracuseStep 1070531 = 1605797) B1605797
theorem B808481 : Blo 475787 808481 := bstep (se 2 (by rfl) ⟨303180, by rfl⟩ : syracuseStep 808481 = 606361) B606361
theorem B808609 : Blo 475787 808609 := bstep (se 2 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 808609 = 606457) B606457
theorem B808643 : Blo 475787 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B2414285 : Blo 475787 2414285 := bstep (se 3 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 2414285 = 905357) B905357
theorem B1070801 : Blo 475787 1070801 := bstep (se 2 (by rfl) ⟨401550, by rfl⟩ : syracuseStep 1070801 = 803101) B803101
theorem B1070819 : Blo 475787 1070819 := bstep (se 1 (by rfl) ⟨803114, by rfl⟩ : syracuseStep 1070819 = 1606229) B1606229
theorem B972515 : Blo 475787 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B677651 : Blo 475787 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B808771 : Blo 475787 808771 := bstep (se 1 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 808771 = 1213157) B1213157
theorem B645025 : Blo 475787 645025 := bstep (se 2 (by rfl) ⟨241884, by rfl⟩ : syracuseStep 645025 = 483769) B483769
theorem B808913 : Blo 475787 808913 := bstep (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) B606685
theorem B10344419 : Blo 475787 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B1071089 : Blo 475787 1071089 := bstep (se 2 (by rfl) ⟨401658, by rfl⟩ : syracuseStep 1071089 = 803317) B803317
theorem B1071107 : Blo 475787 1071107 := bstep (se 1 (by rfl) ⟨803330, by rfl⟩ : syracuseStep 1071107 = 1606661) B1606661
theorem B809041 : Blo 475787 809041 := bstep (se 2 (by rfl) ⟨303390, by rfl⟩ : syracuseStep 809041 = 606781) B606781
theorem B809075 : Blo 475787 809075 := bstep (se 1 (by rfl) ⟨606806, by rfl⟩ : syracuseStep 809075 = 1213613) B1213613
theorem B809203 : Blo 475787 809203 := bstep (se 1 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 809203 = 1213805) B1213805
theorem B1071377 : Blo 475787 1071377 := bstep (se 2 (by rfl) ⟨401766, by rfl⟩ : syracuseStep 1071377 = 803533) B803533
theorem B907537 : Blo 475787 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B11229461 : Blo 475787 11229461 := bstep (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) B526381
theorem B1071395 : Blo 475787 1071395 := bstep (se 1 (by rfl) ⟨803546, by rfl⟩ : syracuseStep 1071395 = 1607093) B1607093
theorem B809345 : Blo 475787 809345 := bstep (se 2 (by rfl) ⟨303504, by rfl⟩ : syracuseStep 809345 = 607009) B607009
theorem B678289 : Blo 475787 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B809473 : Blo 475787 809473 := bstep (se 2 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 809473 = 607105) B607105
theorem B678403 : Blo 475787 678403 := bstep (se 1 (by rfl) ⟨508802, by rfl⟩ : syracuseStep 678403 = 1017605) B1017605
theorem B809507 : Blo 475787 809507 := bstep (se 1 (by rfl) ⟨607130, by rfl⟩ : syracuseStep 809507 = 1214261) B1214261
theorem B1071665 : Blo 475787 1071665 := bstep (se 2 (by rfl) ⟨401874, by rfl⟩ : syracuseStep 1071665 = 803749) B803749
theorem B1071683 : Blo 475787 1071683 := bstep (se 1 (by rfl) ⟨803762, by rfl⟩ : syracuseStep 1071683 = 1607525) B1607525
theorem B907939 : Blo 475787 907939 := bstep (se 1 (by rfl) ⟨680954, by rfl⟩ : syracuseStep 907939 = 1361909) B1361909
theorem B809635 : Blo 475787 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B907985 : Blo 475787 907985 := bstep (se 2 (by rfl) ⟨340494, by rfl⟩ : syracuseStep 907985 = 680989) B680989
theorem B1071953 : Blo 475787 1071953 := bstep (se 2 (by rfl) ⟨401982, by rfl⟩ : syracuseStep 1071953 = 803965) B803965
theorem B1071971 : Blo 475787 1071971 := bstep (se 1 (by rfl) ⟨803978, by rfl⟩ : syracuseStep 1071971 = 1607957) B1607957
theorem B646051 : Blo 475787 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B5823413 : Blo 475787 5823413 := bstep (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) B545945
theorem B908273 : Blo 475787 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B1530893 : Blo 475787 1530893 := bstep (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) B574085
theorem B1072241 : Blo 475787 1072241 := bstep (se 2 (by rfl) ⟨402090, by rfl⟩ : syracuseStep 1072241 = 804181) B804181
theorem B1072259 : Blo 475787 1072259 := bstep (se 1 (by rfl) ⟨804194, by rfl⟩ : syracuseStep 1072259 = 1608389) B1608389
theorem B1531021 : Blo 475787 1531021 := bstep (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) B574133
theorem B3071267 : Blo 475787 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B1531277 : Blo 475787 1531277 := bstep (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) B574229
theorem B1072529 : Blo 475787 1072529 := bstep (se 2 (by rfl) ⟨402198, by rfl⟩ : syracuseStep 1072529 = 804397) B804397
theorem B1072547 : Blo 475787 1072547 := bstep (se 1 (by rfl) ⟨804410, by rfl⟩ : syracuseStep 1072547 = 1608821) B1608821
theorem B482819 : Blo 475787 482819 := bstep (se 1 (by rfl) ⟨362114, by rfl⟩ : syracuseStep 482819 = 724229) B724229
theorem B1728049 : Blo 475787 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B5103173 : Blo 475787 5103173 := bstep (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) B956845
theorem B1072817 : Blo 475787 1072817 := bstep (se 2 (by rfl) ⟨402306, by rfl⟩ : syracuseStep 1072817 = 804613) B804613
theorem B1072835 : Blo 475787 1072835 := bstep (se 1 (by rfl) ⟨804626, by rfl⟩ : syracuseStep 1072835 = 1609253) B1609253
theorem B908995 : Blo 475787 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1892045 : Blo 475787 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B2186993 : Blo 475787 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B679747 : Blo 475787 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B2973509 : Blo 475787 2973509 := bstep (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) B557533
theorem B647041 : Blo 475787 647041 := bstep (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) B485281
theorem B1073105 : Blo 475787 1073105 := bstep (se 2 (by rfl) ⟨402414, by rfl⟩ : syracuseStep 1073105 = 804829) B804829
theorem B1073123 : Blo 475787 1073123 := bstep (se 1 (by rfl) ⟨804842, by rfl⟩ : syracuseStep 1073123 = 1609685) B1609685
theorem B7757795 : Blo 475787 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B909443 : Blo 475787 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B1073393 : Blo 475787 1073393 := bstep (se 2 (by rfl) ⟨402522, by rfl⟩ : syracuseStep 1073393 = 805045) B805045
theorem B1073411 : Blo 475787 1073411 := bstep (se 1 (by rfl) ⟨805058, by rfl⟩ : syracuseStep 1073411 = 1610117) B1610117
theorem B942353 : Blo 475787 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B909731 : Blo 475787 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B1204753 : Blo 475787 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B1073681 : Blo 475787 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B1073699 : Blo 475787 1073699 := bstep (se 1 (by rfl) ⟨805274, by rfl⟩ : syracuseStep 1073699 = 1610549) B1610549
theorem B2417201 : Blo 475787 2417201 := bstep (se 2 (by rfl) ⟨906450, by rfl⟩ : syracuseStep 2417201 = 1812901) B1812901
theorem B3072653 : Blo 475787 3072653 := bstep (se 3 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 3072653 = 1152245) B1152245
theorem B1401517 : Blo 475787 1401517 := bstep (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) B525569
theorem B1205027 : Blo 475787 1205027 := bstep (se 1 (by rfl) ⟨903770, by rfl⟩ : syracuseStep 1205027 = 1807541) B1807541
theorem B1073969 : Blo 475787 1073969 := bstep (se 2 (by rfl) ⟨402738, by rfl⟩ : syracuseStep 1073969 = 805477) B805477
theorem B1073987 : Blo 475787 1073987 := bstep (se 1 (by rfl) ⟨805490, by rfl⟩ : syracuseStep 1073987 = 1610981) B1610981
theorem B1631075 : Blo 475787 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1532803 : Blo 475787 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B680881 : Blo 475787 680881 := bstep (se 2 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 680881 = 510661) B510661
theorem B713681 : Blo 475787 713681 := bstep (se 2 (by rfl) ⟨267630, by rfl⟩ : syracuseStep 713681 = 535261) B535261
theorem B713699 : Blo 475787 713699 := bstep (se 1 (by rfl) ⟨535274, by rfl⟩ : syracuseStep 713699 = 1070549) B1070549
theorem B1205219 : Blo 475787 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B713729 : Blo 475787 713729 := bstep (se 2 (by rfl) ⟨267648, by rfl⟩ : syracuseStep 713729 = 535297) B535297
theorem B680977 : Blo 475787 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B713747 : Blo 475787 713747 := bstep (se 1 (by rfl) ⟨535310, by rfl⟩ : syracuseStep 713747 = 1070621) B1070621
theorem B713777 : Blo 475787 713777 := bstep (se 2 (by rfl) ⟨267666, by rfl⟩ : syracuseStep 713777 = 535333) B535333
theorem B713795 : Blo 475787 713795 := bstep (se 1 (by rfl) ⟨535346, by rfl⟩ : syracuseStep 713795 = 1070693) B1070693
theorem B1074257 : Blo 475787 1074257 := bstep (se 2 (by rfl) ⟨402846, by rfl⟩ : syracuseStep 1074257 = 805693) B805693
theorem B713825 : Blo 475787 713825 := bstep (se 2 (by rfl) ⟨267684, by rfl⟩ : syracuseStep 713825 = 535369) B535369
theorem B1074275 : Blo 475787 1074275 := bstep (se 1 (by rfl) ⟨805706, by rfl⟩ : syracuseStep 1074275 = 1611413) B1611413
theorem B713843 : Blo 475787 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B713873 : Blo 475787 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B713891 : Blo 475787 713891 := bstep (se 1 (by rfl) ⟨535418, by rfl⟩ : syracuseStep 713891 = 1070837) B1070837
theorem B713921 : Blo 475787 713921 := bstep (se 2 (by rfl) ⟨267720, by rfl⟩ : syracuseStep 713921 = 535441) B535441
theorem B484547 : Blo 475787 484547 := bstep (se 1 (by rfl) ⟨363410, by rfl⟩ : syracuseStep 484547 = 726821) B726821
theorem B713939 : Blo 475787 713939 := bstep (se 1 (by rfl) ⟨535454, by rfl⟩ : syracuseStep 713939 = 1070909) B1070909
theorem B484579 : Blo 475787 484579 := bstep (se 1 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 484579 = 726869) B726869
theorem B713969 : Blo 475787 713969 := bstep (se 2 (by rfl) ⟨267738, by rfl⟩ : syracuseStep 713969 = 535477) B535477
theorem B713987 : Blo 475787 713987 := bstep (se 1 (by rfl) ⟨535490, by rfl⟩ : syracuseStep 713987 = 1070981) B1070981
theorem B714017 : Blo 475787 714017 := bstep (se 2 (by rfl) ⟨267756, by rfl⟩ : syracuseStep 714017 = 535513) B535513
theorem B714035 : Blo 475787 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B714065 : Blo 475787 714065 := bstep (se 2 (by rfl) ⟨267774, by rfl⟩ : syracuseStep 714065 = 535549) B535549
theorem B910673 : Blo 475787 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B714083 : Blo 475787 714083 := bstep (se 1 (by rfl) ⟨535562, by rfl⟩ : syracuseStep 714083 = 1071125) B1071125
theorem B1074545 : Blo 475787 1074545 := bstep (se 2 (by rfl) ⟨402954, by rfl⟩ : syracuseStep 1074545 = 805909) B805909
theorem B714113 : Blo 475787 714113 := bstep (se 2 (by rfl) ⟨267792, by rfl⟩ : syracuseStep 714113 = 535585) B535585
theorem B1074563 : Blo 475787 1074563 := bstep (se 1 (by rfl) ⟨805922, by rfl⟩ : syracuseStep 1074563 = 1611845) B1611845
theorem B2712973 : Blo 475787 2712973 := bstep (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) B1017365
theorem B714131 : Blo 475787 714131 := bstep (se 1 (by rfl) ⟨535598, by rfl⟩ : syracuseStep 714131 = 1071197) B1071197
theorem B714161 : Blo 475787 714161 := bstep (se 2 (by rfl) ⟨267810, by rfl⟩ : syracuseStep 714161 = 535621) B535621
theorem B714179 : Blo 475787 714179 := bstep (se 1 (by rfl) ⟨535634, by rfl⟩ : syracuseStep 714179 = 1071269) B1071269
theorem B714209 : Blo 475787 714209 := bstep (se 2 (by rfl) ⟨267828, by rfl⟩ : syracuseStep 714209 = 535657) B535657
theorem B714227 : Blo 475787 714227 := bstep (se 1 (by rfl) ⟨535670, by rfl⟩ : syracuseStep 714227 = 1071341) B1071341
theorem B681473 : Blo 475787 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B714257 : Blo 475787 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B714275 : Blo 475787 714275 := bstep (se 1 (by rfl) ⟨535706, by rfl⟩ : syracuseStep 714275 = 1071413) B1071413
theorem B714305 : Blo 475787 714305 := bstep (se 2 (by rfl) ⟨267864, by rfl⟩ : syracuseStep 714305 = 535729) B535729
theorem B714323 : Blo 475787 714323 := bstep (se 1 (by rfl) ⟨535742, by rfl⟩ : syracuseStep 714323 = 1071485) B1071485
theorem B5170787 : Blo 475787 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B714353 : Blo 475787 714353 := bstep (se 2 (by rfl) ⟨267882, by rfl⟩ : syracuseStep 714353 = 535765) B535765
theorem B714371 : Blo 475787 714371 := bstep (se 1 (by rfl) ⟨535778, by rfl⟩ : syracuseStep 714371 = 1071557) B1071557
theorem B1074833 : Blo 475787 1074833 := bstep (se 2 (by rfl) ⟨403062, by rfl⟩ : syracuseStep 1074833 = 806125) B806125
theorem B714401 : Blo 475787 714401 := bstep (se 2 (by rfl) ⟨267900, by rfl⟩ : syracuseStep 714401 = 535801) B535801
theorem B1074851 : Blo 475787 1074851 := bstep (se 1 (by rfl) ⟨806138, by rfl⟩ : syracuseStep 1074851 = 1612277) B1612277
theorem B714419 : Blo 475787 714419 := bstep (se 1 (by rfl) ⟨535814, by rfl⟩ : syracuseStep 714419 = 1071629) B1071629
theorem B714449 : Blo 475787 714449 := bstep (se 2 (by rfl) ⟨267918, by rfl⟩ : syracuseStep 714449 = 535837) B535837
theorem B714467 : Blo 475787 714467 := bstep (se 1 (by rfl) ⟨535850, by rfl⟩ : syracuseStep 714467 = 1071701) B1071701
theorem B1631981 : Blo 475787 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B714497 : Blo 475787 714497 := bstep (se 2 (by rfl) ⟨267936, by rfl⟩ : syracuseStep 714497 = 535873) B535873
theorem B714515 : Blo 475787 714515 := bstep (se 1 (by rfl) ⟨535886, by rfl⟩ : syracuseStep 714515 = 1071773) B1071773
theorem B714545 : Blo 475787 714545 := bstep (se 2 (by rfl) ⟨267954, by rfl⟩ : syracuseStep 714545 = 535909) B535909
theorem B714563 : Blo 475787 714563 := bstep (se 1 (by rfl) ⟨535922, by rfl⟩ : syracuseStep 714563 = 1071845) B1071845
theorem B714593 : Blo 475787 714593 := bstep (se 2 (by rfl) ⟨267972, by rfl⟩ : syracuseStep 714593 = 535945) B535945
theorem B3303281 : Blo 475787 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B714611 : Blo 475787 714611 := bstep (se 1 (by rfl) ⟨535958, by rfl⟩ : syracuseStep 714611 = 1071917) B1071917
theorem B714641 : Blo 475787 714641 := bstep (se 2 (by rfl) ⟨267990, by rfl⟩ : syracuseStep 714641 = 535981) B535981
theorem B1206161 : Blo 475787 1206161 := bstep (se 2 (by rfl) ⟨452310, by rfl⟩ : syracuseStep 1206161 = 904621) B904621
theorem B714659 : Blo 475787 714659 := bstep (se 1 (by rfl) ⟨535994, by rfl⟩ : syracuseStep 714659 = 1071989) B1071989
theorem B1075121 : Blo 475787 1075121 := bstep (se 2 (by rfl) ⟨403170, by rfl⟩ : syracuseStep 1075121 = 806341) B806341
theorem B714689 : Blo 475787 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B1206211 : Blo 475787 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B1075139 : Blo 475787 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B714707 : Blo 475787 714707 := bstep (se 1 (by rfl) ⟨536030, by rfl⟩ : syracuseStep 714707 = 1072061) B1072061
theorem B2418659 : Blo 475787 2418659 := bstep (se 1 (by rfl) ⟨1813994, by rfl⟩ : syracuseStep 2418659 = 3627989) B3627989
theorem B714737 : Blo 475787 714737 := bstep (se 2 (by rfl) ⟨268026, by rfl⟩ : syracuseStep 714737 = 536053) B536053
theorem B714755 : Blo 475787 714755 := bstep (se 1 (by rfl) ⟨536066, by rfl⟩ : syracuseStep 714755 = 1072133) B1072133
theorem B714785 : Blo 475787 714785 := bstep (se 2 (by rfl) ⟨268044, by rfl⟩ : syracuseStep 714785 = 536089) B536089
theorem B714803 : Blo 475787 714803 := bstep (se 1 (by rfl) ⟨536102, by rfl⟩ : syracuseStep 714803 = 1072205) B1072205
theorem B714833 : Blo 475787 714833 := bstep (se 2 (by rfl) ⟨268062, by rfl⟩ : syracuseStep 714833 = 536125) B536125
theorem B1206353 : Blo 475787 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B714851 : Blo 475787 714851 := bstep (se 1 (by rfl) ⟨536138, by rfl⟩ : syracuseStep 714851 = 1072277) B1072277
theorem B714881 : Blo 475787 714881 := bstep (se 2 (by rfl) ⟨268080, by rfl⟩ : syracuseStep 714881 = 536161) B536161
theorem B714899 : Blo 475787 714899 := bstep (se 1 (by rfl) ⟨536174, by rfl⟩ : syracuseStep 714899 = 1072349) B1072349
theorem B714929 : Blo 475787 714929 := bstep (se 2 (by rfl) ⟨268098, by rfl⟩ : syracuseStep 714929 = 536197) B536197
theorem B714947 : Blo 475787 714947 := bstep (se 1 (by rfl) ⟨536210, by rfl⟩ : syracuseStep 714947 = 1072421) B1072421
theorem B1075409 : Blo 475787 1075409 := bstep (se 2 (by rfl) ⟨403278, by rfl⟩ : syracuseStep 1075409 = 806557) B806557
theorem B714977 : Blo 475787 714977 := bstep (se 2 (by rfl) ⟨268116, by rfl⟩ : syracuseStep 714977 = 536233) B536233
theorem B1075427 : Blo 475787 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B714995 : Blo 475787 714995 := bstep (se 1 (by rfl) ⟨536246, by rfl⟩ : syracuseStep 714995 = 1072493) B1072493
theorem B715025 : Blo 475787 715025 := bstep (se 2 (by rfl) ⟨268134, by rfl⟩ : syracuseStep 715025 = 536269) B536269
theorem B715043 : Blo 475787 715043 := bstep (se 1 (by rfl) ⟨536282, by rfl⟩ : syracuseStep 715043 = 1072565) B1072565
theorem B715073 : Blo 475787 715073 := bstep (se 2 (by rfl) ⟨268152, by rfl⟩ : syracuseStep 715073 = 536305) B536305
theorem B715091 : Blo 475787 715091 := bstep (se 1 (by rfl) ⟨536318, by rfl⟩ : syracuseStep 715091 = 1072637) B1072637
theorem B682339 : Blo 475787 682339 := bstep (se 1 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 682339 = 1023509) B1023509
theorem B715121 : Blo 475787 715121 := bstep (se 2 (by rfl) ⟨268170, by rfl⟩ : syracuseStep 715121 = 536341) B536341
theorem B715139 : Blo 475787 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B715169 : Blo 475787 715169 := bstep (se 2 (by rfl) ⟨268188, by rfl⟩ : syracuseStep 715169 = 536377) B536377
theorem B715187 : Blo 475787 715187 := bstep (se 1 (by rfl) ⟨536390, by rfl⟩ : syracuseStep 715187 = 1072781) B1072781
theorem B1534403 : Blo 475787 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B682435 : Blo 475787 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B715217 : Blo 475787 715217 := bstep (se 2 (by rfl) ⟨268206, by rfl⟩ : syracuseStep 715217 = 536413) B536413
theorem B715235 : Blo 475787 715235 := bstep (se 1 (by rfl) ⟨536426, by rfl⟩ : syracuseStep 715235 = 1072853) B1072853
theorem B6220273 : Blo 475787 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B3434993 : Blo 475787 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B1075697 : Blo 475787 1075697 := bstep (se 2 (by rfl) ⟨403386, by rfl⟩ : syracuseStep 1075697 = 806773) B806773
theorem B715265 : Blo 475787 715265 := bstep (se 2 (by rfl) ⟨268224, by rfl⟩ : syracuseStep 715265 = 536449) B536449
theorem B1075715 : Blo 475787 1075715 := bstep (se 1 (by rfl) ⟨806786, by rfl⟩ : syracuseStep 1075715 = 1613573) B1613573
theorem B715283 : Blo 475787 715283 := bstep (se 1 (by rfl) ⟨536462, by rfl⟩ : syracuseStep 715283 = 1072925) B1072925
theorem B715313 : Blo 475787 715313 := bstep (se 2 (by rfl) ⟨268242, by rfl⟩ : syracuseStep 715313 = 536485) B536485
theorem B715331 : Blo 475787 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B715361 : Blo 475787 715361 := bstep (se 2 (by rfl) ⟨268260, by rfl⟩ : syracuseStep 715361 = 536521) B536521
theorem B715379 : Blo 475787 715379 := bstep (se 1 (by rfl) ⟨536534, by rfl⟩ : syracuseStep 715379 = 1073069) B1073069
theorem B715409 : Blo 475787 715409 := bstep (se 2 (by rfl) ⟨268278, by rfl⟩ : syracuseStep 715409 = 536557) B536557
theorem B715427 : Blo 475787 715427 := bstep (se 1 (by rfl) ⟨536570, by rfl⟩ : syracuseStep 715427 = 1073141) B1073141
theorem B715457 : Blo 475787 715457 := bstep (se 2 (by rfl) ⟨268296, by rfl⟩ : syracuseStep 715457 = 536593) B536593
theorem B715475 : Blo 475787 715475 := bstep (se 1 (by rfl) ⟨536606, by rfl⟩ : syracuseStep 715475 = 1073213) B1073213
theorem B715505 : Blo 475787 715505 := bstep (se 2 (by rfl) ⟨268314, by rfl⟩ : syracuseStep 715505 = 536629) B536629
theorem B715523 : Blo 475787 715523 := bstep (se 1 (by rfl) ⟨536642, by rfl⟩ : syracuseStep 715523 = 1073285) B1073285
theorem B2419469 : Blo 475787 2419469 := bstep (se 3 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 2419469 = 907301) B907301
theorem B1075985 : Blo 475787 1075985 := bstep (se 2 (by rfl) ⟨403494, by rfl⟩ : syracuseStep 1075985 = 806989) B806989
theorem B715553 : Blo 475787 715553 := bstep (se 2 (by rfl) ⟨268332, by rfl⟩ : syracuseStep 715553 = 536665) B536665
theorem B1076003 : Blo 475787 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B715571 : Blo 475787 715571 := bstep (se 1 (by rfl) ⟨536678, by rfl⟩ : syracuseStep 715571 = 1073357) B1073357
theorem B715601 : Blo 475787 715601 := bstep (se 2 (by rfl) ⟨268350, by rfl⟩ : syracuseStep 715601 = 536701) B536701
theorem B715619 : Blo 475787 715619 := bstep (se 1 (by rfl) ⟨536714, by rfl⟩ : syracuseStep 715619 = 1073429) B1073429
theorem B715649 : Blo 475787 715649 := bstep (se 2 (by rfl) ⟨268368, by rfl⟩ : syracuseStep 715649 = 536737) B536737
theorem B715667 : Blo 475787 715667 := bstep (se 1 (by rfl) ⟨536750, by rfl⟩ : syracuseStep 715667 = 1073501) B1073501
theorem B715697 : Blo 475787 715697 := bstep (se 2 (by rfl) ⟨268386, by rfl⟩ : syracuseStep 715697 = 536773) B536773
theorem B682931 : Blo 475787 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B715715 : Blo 475787 715715 := bstep (se 1 (by rfl) ⟨536786, by rfl⟩ : syracuseStep 715715 = 1073573) B1073573
theorem B715745 : Blo 475787 715745 := bstep (se 2 (by rfl) ⟨268404, by rfl⟩ : syracuseStep 715745 = 536809) B536809
theorem B715763 : Blo 475787 715763 := bstep (se 1 (by rfl) ⟨536822, by rfl⟩ : syracuseStep 715763 = 1073645) B1073645
theorem B715793 : Blo 475787 715793 := bstep (se 2 (by rfl) ⟨268422, by rfl⟩ : syracuseStep 715793 = 536845) B536845
theorem B715811 : Blo 475787 715811 := bstep (se 1 (by rfl) ⟨536858, by rfl⟩ : syracuseStep 715811 = 1073717) B1073717
theorem B1207345 : Blo 475787 1207345 := bstep (se 2 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 1207345 = 905509) B905509
theorem B1076273 : Blo 475787 1076273 := bstep (se 2 (by rfl) ⟨403602, by rfl⟩ : syracuseStep 1076273 = 807205) B807205
theorem B715841 : Blo 475787 715841 := bstep (se 2 (by rfl) ⟨268440, by rfl⟩ : syracuseStep 715841 = 536881) B536881
theorem B1076291 : Blo 475787 1076291 := bstep (se 1 (by rfl) ⟨807218, by rfl⟩ : syracuseStep 1076291 = 1614437) B1614437
theorem B715859 : Blo 475787 715859 := bstep (se 1 (by rfl) ⟨536894, by rfl⟩ : syracuseStep 715859 = 1073789) B1073789
theorem B715889 : Blo 475787 715889 := bstep (se 2 (by rfl) ⟨268458, by rfl⟩ : syracuseStep 715889 = 536917) B536917
theorem B715907 : Blo 475787 715907 := bstep (se 1 (by rfl) ⟨536930, by rfl⟩ : syracuseStep 715907 = 1073861) B1073861
theorem B715937 : Blo 475787 715937 := bstep (se 2 (by rfl) ⟨268476, by rfl⟩ : syracuseStep 715937 = 536953) B536953
theorem B715955 : Blo 475787 715955 := bstep (se 1 (by rfl) ⟨536966, by rfl⟩ : syracuseStep 715955 = 1073933) B1073933
theorem B1961165 : Blo 475787 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B715985 : Blo 475787 715985 := bstep (se 2 (by rfl) ⟨268494, by rfl⟩ : syracuseStep 715985 = 536989) B536989
theorem B716003 : Blo 475787 716003 := bstep (se 1 (by rfl) ⟨537002, by rfl⟩ : syracuseStep 716003 = 1074005) B1074005
theorem B716033 : Blo 475787 716033 := bstep (se 2 (by rfl) ⟨268512, by rfl⟩ : syracuseStep 716033 = 537025) B537025
theorem B716051 : Blo 475787 716051 := bstep (se 1 (by rfl) ⟨537038, by rfl⟩ : syracuseStep 716051 = 1074077) B1074077
theorem B716081 : Blo 475787 716081 := bstep (se 2 (by rfl) ⟨268530, by rfl⟩ : syracuseStep 716081 = 537061) B537061
theorem B1207619 : Blo 475787 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B716099 : Blo 475787 716099 := bstep (se 1 (by rfl) ⟨537074, by rfl⟩ : syracuseStep 716099 = 1074149) B1074149
theorem B2714957 : Blo 475787 2714957 := bstep (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) B1018109
theorem B1076561 : Blo 475787 1076561 := bstep (se 2 (by rfl) ⟨403710, by rfl⟩ : syracuseStep 1076561 = 807421) B807421
theorem B716129 : Blo 475787 716129 := bstep (se 2 (by rfl) ⟨268548, by rfl⟩ : syracuseStep 716129 = 537097) B537097
theorem B1076579 : Blo 475787 1076579 := bstep (se 1 (by rfl) ⟨807434, by rfl⟩ : syracuseStep 1076579 = 1614869) B1614869
theorem B716147 : Blo 475787 716147 := bstep (se 1 (by rfl) ⟨537110, by rfl⟩ : syracuseStep 716147 = 1074221) B1074221
theorem B716177 : Blo 475787 716177 := bstep (se 2 (by rfl) ⟨268566, by rfl⟩ : syracuseStep 716177 = 537133) B537133
theorem B1535377 : Blo 475787 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B716195 : Blo 475787 716195 := bstep (se 1 (by rfl) ⟨537146, by rfl⟩ : syracuseStep 716195 = 1074293) B1074293
theorem B978353 : Blo 475787 978353 := bstep (se 2 (by rfl) ⟨366882, by rfl⟩ : syracuseStep 978353 = 733765) B733765
theorem B716225 : Blo 475787 716225 := bstep (se 2 (by rfl) ⟨268584, by rfl⟩ : syracuseStep 716225 = 537169) B537169
theorem B716243 : Blo 475787 716243 := bstep (se 1 (by rfl) ⟨537182, by rfl⟩ : syracuseStep 716243 = 1074365) B1074365
theorem B716273 : Blo 475787 716273 := bstep (se 2 (by rfl) ⟨268602, by rfl⟩ : syracuseStep 716273 = 537205) B537205
theorem B1207811 : Blo 475787 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B716291 : Blo 475787 716291 := bstep (se 1 (by rfl) ⟨537218, by rfl⟩ : syracuseStep 716291 = 1074437) B1074437
theorem B716321 : Blo 475787 716321 := bstep (se 2 (by rfl) ⟨268620, by rfl⟩ : syracuseStep 716321 = 537241) B537241
theorem B716339 : Blo 475787 716339 := bstep (se 1 (by rfl) ⟨537254, by rfl⟩ : syracuseStep 716339 = 1074509) B1074509
theorem B716369 : Blo 475787 716369 := bstep (se 2 (by rfl) ⟨268638, by rfl⟩ : syracuseStep 716369 = 537277) B537277
theorem B716387 : Blo 475787 716387 := bstep (se 1 (by rfl) ⟨537290, by rfl⟩ : syracuseStep 716387 = 1074581) B1074581
theorem B1076849 : Blo 475787 1076849 := bstep (se 2 (by rfl) ⟨403818, by rfl⟩ : syracuseStep 1076849 = 807637) B807637
theorem B716417 : Blo 475787 716417 := bstep (se 2 (by rfl) ⟨268656, by rfl⟩ : syracuseStep 716417 = 537313) B537313
theorem B1076867 : Blo 475787 1076867 := bstep (se 1 (by rfl) ⟨807650, by rfl⟩ : syracuseStep 1076867 = 1615301) B1615301
theorem B716435 : Blo 475787 716435 := bstep (se 1 (by rfl) ⟨537326, by rfl⟩ : syracuseStep 716435 = 1074653) B1074653
theorem B716465 : Blo 475787 716465 := bstep (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) B537349
theorem B716483 : Blo 475787 716483 := bstep (se 1 (by rfl) ⟨537362, by rfl⟩ : syracuseStep 716483 = 1074725) B1074725
theorem B716513 : Blo 475787 716513 := bstep (se 2 (by rfl) ⟨268692, by rfl⟩ : syracuseStep 716513 = 537385) B537385
theorem B2289379 : Blo 475787 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B716531 : Blo 475787 716531 := bstep (se 1 (by rfl) ⟨537398, by rfl⟩ : syracuseStep 716531 = 1074797) B1074797
theorem B552691 : Blo 475787 552691 := bstep (se 1 (by rfl) ⟨414518, by rfl⟩ : syracuseStep 552691 = 829037) B829037
theorem B716561 : Blo 475787 716561 := bstep (se 2 (by rfl) ⟨268710, by rfl⟩ : syracuseStep 716561 = 537421) B537421
theorem B716579 : Blo 475787 716579 := bstep (se 1 (by rfl) ⟨537434, by rfl⟩ : syracuseStep 716579 = 1074869) B1074869
theorem B716609 : Blo 475787 716609 := bstep (se 2 (by rfl) ⟨268728, by rfl⟩ : syracuseStep 716609 = 537457) B537457
theorem B716627 : Blo 475787 716627 := bstep (se 1 (by rfl) ⟨537470, by rfl⟩ : syracuseStep 716627 = 1074941) B1074941
theorem B716657 : Blo 475787 716657 := bstep (se 2 (by rfl) ⟨268746, by rfl⟩ : syracuseStep 716657 = 537493) B537493
theorem B716675 : Blo 475787 716675 := bstep (se 1 (by rfl) ⟨537506, by rfl⟩ : syracuseStep 716675 = 1075013) B1075013
theorem B1077137 : Blo 475787 1077137 := bstep (se 2 (by rfl) ⟨403926, by rfl⟩ : syracuseStep 1077137 = 807853) B807853
theorem B716705 : Blo 475787 716705 := bstep (se 2 (by rfl) ⟨268764, by rfl⟩ : syracuseStep 716705 = 537529) B537529
theorem B1077155 : Blo 475787 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B716723 : Blo 475787 716723 := bstep (se 1 (by rfl) ⟨537542, by rfl⟩ : syracuseStep 716723 = 1075085) B1075085
theorem B1568717 : Blo 475787 1568717 := bstep (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) B588269
theorem B716753 : Blo 475787 716753 := bstep (se 2 (by rfl) ⟨268782, by rfl⟩ : syracuseStep 716753 = 537565) B537565
theorem B3665891 : Blo 475787 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B716771 : Blo 475787 716771 := bstep (se 1 (by rfl) ⟨537578, by rfl⟩ : syracuseStep 716771 = 1075157) B1075157
theorem B716801 : Blo 475787 716801 := bstep (se 2 (by rfl) ⟨268800, by rfl⟩ : syracuseStep 716801 = 537601) B537601
theorem B716819 : Blo 475787 716819 := bstep (se 1 (by rfl) ⟨537614, by rfl⟩ : syracuseStep 716819 = 1075229) B1075229
theorem B978979 : Blo 475787 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B716849 : Blo 475787 716849 := bstep (se 2 (by rfl) ⟨268818, by rfl⟩ : syracuseStep 716849 = 537637) B537637
theorem B716867 : Blo 475787 716867 := bstep (se 1 (by rfl) ⟨537650, by rfl⟩ : syracuseStep 716867 = 1075301) B1075301
theorem B716897 : Blo 475787 716897 := bstep (se 2 (by rfl) ⟨268836, by rfl⟩ : syracuseStep 716897 = 537673) B537673
theorem B716915 : Blo 475787 716915 := bstep (se 1 (by rfl) ⟨537686, by rfl⟩ : syracuseStep 716915 = 1075373) B1075373
theorem B716945 : Blo 475787 716945 := bstep (se 2 (by rfl) ⟨268854, by rfl⟩ : syracuseStep 716945 = 537709) B537709
theorem B716963 : Blo 475787 716963 := bstep (se 1 (by rfl) ⟨537722, by rfl⟩ : syracuseStep 716963 = 1075445) B1075445
theorem B1077425 : Blo 475787 1077425 := bstep (se 2 (by rfl) ⟨404034, by rfl⟩ : syracuseStep 1077425 = 808069) B808069
theorem B716993 : Blo 475787 716993 := bstep (se 2 (by rfl) ⟨268872, by rfl⟩ : syracuseStep 716993 = 537745) B537745
theorem B1077443 : Blo 475787 1077443 := bstep (se 1 (by rfl) ⟨808082, by rfl⟩ : syracuseStep 1077443 = 1616165) B1616165
theorem B717011 : Blo 475787 717011 := bstep (se 1 (by rfl) ⟨537758, by rfl⟩ : syracuseStep 717011 = 1075517) B1075517
theorem B2715889 : Blo 475787 2715889 := bstep (se 2 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 2715889 = 2036917) B2036917
theorem B717041 : Blo 475787 717041 := bstep (se 2 (by rfl) ⟨268890, by rfl⟩ : syracuseStep 717041 = 537781) B537781
theorem B717059 : Blo 475787 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B717089 : Blo 475787 717089 := bstep (se 2 (by rfl) ⟨268908, by rfl⟩ : syracuseStep 717089 = 537817) B537817
theorem B717107 : Blo 475787 717107 := bstep (se 1 (by rfl) ⟨537830, by rfl⟩ : syracuseStep 717107 = 1075661) B1075661
theorem B717137 : Blo 475787 717137 := bstep (se 2 (by rfl) ⟨268926, by rfl⟩ : syracuseStep 717137 = 537853) B537853
theorem B717155 : Blo 475787 717155 := bstep (se 1 (by rfl) ⟨537866, by rfl⟩ : syracuseStep 717155 = 1075733) B1075733
theorem B717185 : Blo 475787 717185 := bstep (se 2 (by rfl) ⟨268944, by rfl⟩ : syracuseStep 717185 = 537889) B537889
theorem B717203 : Blo 475787 717203 := bstep (se 1 (by rfl) ⟨537902, by rfl⟩ : syracuseStep 717203 = 1075805) B1075805
theorem B1208753 : Blo 475787 1208753 := bstep (se 2 (by rfl) ⟨453282, by rfl⟩ : syracuseStep 1208753 = 906565) B906565
theorem B717233 : Blo 475787 717233 := bstep (se 2 (by rfl) ⟨268962, by rfl⟩ : syracuseStep 717233 = 537925) B537925
theorem B717251 : Blo 475787 717251 := bstep (se 1 (by rfl) ⟨537938, by rfl⟩ : syracuseStep 717251 = 1075877) B1075877
theorem B1077713 : Blo 475787 1077713 := bstep (se 2 (by rfl) ⟨404142, by rfl⟩ : syracuseStep 1077713 = 808285) B808285
theorem B717281 : Blo 475787 717281 := bstep (se 2 (by rfl) ⟨268980, by rfl⟩ : syracuseStep 717281 = 537961) B537961
theorem B1208803 : Blo 475787 1208803 := bstep (se 1 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 1208803 = 1813205) B1813205
theorem B1077731 : Blo 475787 1077731 := bstep (se 1 (by rfl) ⟨808298, by rfl⟩ : syracuseStep 1077731 = 1616597) B1616597
theorem B717299 : Blo 475787 717299 := bstep (se 1 (by rfl) ⟨537974, by rfl⟩ : syracuseStep 717299 = 1075949) B1075949
theorem B717329 : Blo 475787 717329 := bstep (se 2 (by rfl) ⟨268998, by rfl⟩ : syracuseStep 717329 = 537997) B537997
theorem B717347 : Blo 475787 717347 := bstep (se 1 (by rfl) ⟨538010, by rfl⟩ : syracuseStep 717347 = 1076021) B1076021
theorem B717377 : Blo 475787 717377 := bstep (se 2 (by rfl) ⟨269016, by rfl⟩ : syracuseStep 717377 = 538033) B538033
theorem B717395 : Blo 475787 717395 := bstep (se 1 (by rfl) ⟨538046, by rfl⟩ : syracuseStep 717395 = 1076093) B1076093
theorem B1208945 : Blo 475787 1208945 := bstep (se 2 (by rfl) ⟨453354, by rfl⟩ : syracuseStep 1208945 = 906709) B906709
theorem B717425 : Blo 475787 717425 := bstep (se 2 (by rfl) ⟨269034, by rfl⟩ : syracuseStep 717425 = 538069) B538069
theorem B717443 : Blo 475787 717443 := bstep (se 1 (by rfl) ⟨538082, by rfl⟩ : syracuseStep 717443 = 1076165) B1076165
theorem B717473 : Blo 475787 717473 := bstep (se 2 (by rfl) ⟨269052, by rfl⟩ : syracuseStep 717473 = 538105) B538105
theorem B717491 : Blo 475787 717491 := bstep (se 1 (by rfl) ⟨538118, by rfl⟩ : syracuseStep 717491 = 1076237) B1076237
theorem B717521 : Blo 475787 717521 := bstep (se 2 (by rfl) ⟨269070, by rfl⟩ : syracuseStep 717521 = 538141) B538141
theorem B717539 : Blo 475787 717539 := bstep (se 1 (by rfl) ⟨538154, by rfl⟩ : syracuseStep 717539 = 1076309) B1076309
theorem B1078001 : Blo 475787 1078001 := bstep (se 2 (by rfl) ⟨404250, by rfl⟩ : syracuseStep 1078001 = 808501) B808501
theorem B717569 : Blo 475787 717569 := bstep (se 2 (by rfl) ⟨269088, by rfl⟩ : syracuseStep 717569 = 538177) B538177
theorem B1078019 : Blo 475787 1078019 := bstep (se 1 (by rfl) ⟨808514, by rfl⟩ : syracuseStep 1078019 = 1617029) B1617029
theorem B717587 : Blo 475787 717587 := bstep (se 1 (by rfl) ⟨538190, by rfl⟩ : syracuseStep 717587 = 1076381) B1076381
theorem B717617 : Blo 475787 717617 := bstep (se 2 (by rfl) ⟨269106, by rfl⟩ : syracuseStep 717617 = 538213) B538213
theorem B717635 : Blo 475787 717635 := bstep (se 1 (by rfl) ⟨538226, by rfl⟩ : syracuseStep 717635 = 1076453) B1076453
theorem B717665 : Blo 475787 717665 := bstep (se 2 (by rfl) ⟨269124, by rfl⟩ : syracuseStep 717665 = 538249) B538249
theorem B717683 : Blo 475787 717683 := bstep (se 1 (by rfl) ⟨538262, by rfl⟩ : syracuseStep 717683 = 1076525) B1076525
theorem B1143683 : Blo 475787 1143683 := bstep (se 1 (by rfl) ⟨857762, by rfl⟩ : syracuseStep 1143683 = 1715525) B1715525
theorem B717713 : Blo 475787 717713 := bstep (se 2 (by rfl) ⟨269142, by rfl⟩ : syracuseStep 717713 = 538285) B538285
theorem B717731 : Blo 475787 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B2290609 : Blo 475787 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B717761 : Blo 475787 717761 := bstep (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) B538321
theorem B717779 : Blo 475787 717779 := bstep (se 1 (by rfl) ⟨538334, by rfl⟩ : syracuseStep 717779 = 1076669) B1076669
theorem B717809 : Blo 475787 717809 := bstep (se 2 (by rfl) ⟨269178, by rfl⟩ : syracuseStep 717809 = 538357) B538357
theorem B717827 : Blo 475787 717827 := bstep (se 1 (by rfl) ⟨538370, by rfl⟩ : syracuseStep 717827 = 1076741) B1076741
theorem B1078289 : Blo 475787 1078289 := bstep (se 2 (by rfl) ⟨404358, by rfl⟩ : syracuseStep 1078289 = 808717) B808717
theorem B717857 : Blo 475787 717857 := bstep (se 2 (by rfl) ⟨269196, by rfl⟩ : syracuseStep 717857 = 538393) B538393
theorem B1078307 : Blo 475787 1078307 := bstep (se 1 (by rfl) ⟨808730, by rfl⟩ : syracuseStep 1078307 = 1617461) B1617461
theorem B717875 : Blo 475787 717875 := bstep (se 1 (by rfl) ⟨538406, by rfl⟩ : syracuseStep 717875 = 1076813) B1076813
theorem B717905 : Blo 475787 717905 := bstep (se 2 (by rfl) ⟨269214, by rfl⟩ : syracuseStep 717905 = 538429) B538429
theorem B717923 : Blo 475787 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B717953 : Blo 475787 717953 := bstep (se 2 (by rfl) ⟨269232, by rfl⟩ : syracuseStep 717953 = 538465) B538465
theorem B717971 : Blo 475787 717971 := bstep (se 1 (by rfl) ⟨538478, by rfl⟩ : syracuseStep 717971 = 1076957) B1076957
theorem B718001 : Blo 475787 718001 := bstep (se 2 (by rfl) ⟨269250, by rfl⟩ : syracuseStep 718001 = 538501) B538501
theorem B718019 : Blo 475787 718019 := bstep (se 1 (by rfl) ⟨538514, by rfl⟩ : syracuseStep 718019 = 1077029) B1077029
theorem B718049 : Blo 475787 718049 := bstep (se 2 (by rfl) ⟨269268, by rfl⟩ : syracuseStep 718049 = 538537) B538537
theorem B718067 : Blo 475787 718067 := bstep (se 1 (by rfl) ⟨538550, by rfl⟩ : syracuseStep 718067 = 1077101) B1077101
theorem B718097 : Blo 475787 718097 := bstep (se 2 (by rfl) ⟨269286, by rfl⟩ : syracuseStep 718097 = 538573) B538573
theorem B718115 : Blo 475787 718115 := bstep (se 1 (by rfl) ⟨538586, by rfl⟩ : syracuseStep 718115 = 1077173) B1077173
theorem B1078577 : Blo 475787 1078577 := bstep (se 2 (by rfl) ⟨404466, by rfl⟩ : syracuseStep 1078577 = 808933) B808933
theorem B718145 : Blo 475787 718145 := bstep (se 2 (by rfl) ⟨269304, by rfl⟩ : syracuseStep 718145 = 538609) B538609
theorem B1078595 : Blo 475787 1078595 := bstep (se 1 (by rfl) ⟨808946, by rfl⟩ : syracuseStep 1078595 = 1617893) B1617893
theorem B718163 : Blo 475787 718163 := bstep (se 1 (by rfl) ⟨538622, by rfl⟩ : syracuseStep 718163 = 1077245) B1077245
theorem B718193 : Blo 475787 718193 := bstep (se 2 (by rfl) ⟨269322, by rfl⟩ : syracuseStep 718193 = 538645) B538645
theorem B718211 : Blo 475787 718211 := bstep (se 1 (by rfl) ⟨538658, by rfl⟩ : syracuseStep 718211 = 1077317) B1077317
theorem B718241 : Blo 475787 718241 := bstep (se 2 (by rfl) ⟨269340, by rfl⟩ : syracuseStep 718241 = 538681) B538681
theorem B718259 : Blo 475787 718259 := bstep (se 1 (by rfl) ⟨538694, by rfl⟩ : syracuseStep 718259 = 1077389) B1077389
theorem B718289 : Blo 475787 718289 := bstep (se 2 (by rfl) ⟨269358, by rfl⟩ : syracuseStep 718289 = 538717) B538717
theorem B718307 : Blo 475787 718307 := bstep (se 1 (by rfl) ⟨538730, by rfl⟩ : syracuseStep 718307 = 1077461) B1077461
theorem B718337 : Blo 475787 718337 := bstep (se 2 (by rfl) ⟨269376, by rfl⟩ : syracuseStep 718337 = 538753) B538753
theorem B718355 : Blo 475787 718355 := bstep (se 1 (by rfl) ⟨538766, by rfl⟩ : syracuseStep 718355 = 1077533) B1077533
theorem B718385 : Blo 475787 718385 := bstep (se 2 (by rfl) ⟨269394, by rfl⟩ : syracuseStep 718385 = 538789) B538789
theorem B718403 : Blo 475787 718403 := bstep (se 1 (by rfl) ⟨538802, by rfl⟩ : syracuseStep 718403 = 1077605) B1077605
theorem B1209937 : Blo 475787 1209937 := bstep (se 2 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 1209937 = 907453) B907453
theorem B1078865 : Blo 475787 1078865 := bstep (se 2 (by rfl) ⟨404574, by rfl⟩ : syracuseStep 1078865 = 809149) B809149
theorem B718433 : Blo 475787 718433 := bstep (se 2 (by rfl) ⟨269412, by rfl⟩ : syracuseStep 718433 = 538825) B538825
theorem B1078883 : Blo 475787 1078883 := bstep (se 1 (by rfl) ⟨809162, by rfl⟩ : syracuseStep 1078883 = 1618325) B1618325
theorem B2422385 : Blo 475787 2422385 := bstep (se 2 (by rfl) ⟨908394, by rfl⟩ : syracuseStep 2422385 = 1816789) B1816789
theorem B718451 : Blo 475787 718451 := bstep (se 1 (by rfl) ⟨538838, by rfl⟩ : syracuseStep 718451 = 1077677) B1077677
theorem B1144451 : Blo 475787 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B718481 : Blo 475787 718481 := bstep (se 2 (by rfl) ⟨269430, by rfl⟩ : syracuseStep 718481 = 538861) B538861
theorem B2717347 : Blo 475787 2717347 := bstep (se 1 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 2717347 = 4076021) B4076021
theorem B718499 : Blo 475787 718499 := bstep (se 1 (by rfl) ⟨538874, by rfl⟩ : syracuseStep 718499 = 1077749) B1077749
theorem B718529 : Blo 475787 718529 := bstep (se 2 (by rfl) ⟨269448, by rfl⟩ : syracuseStep 718529 = 538897) B538897
theorem B718547 : Blo 475787 718547 := bstep (se 1 (by rfl) ⟨538910, by rfl⟩ : syracuseStep 718547 = 1077821) B1077821
theorem B718577 : Blo 475787 718577 := bstep (se 2 (by rfl) ⟨269466, by rfl⟩ : syracuseStep 718577 = 538933) B538933
theorem B718595 : Blo 475787 718595 := bstep (se 1 (by rfl) ⟨538946, by rfl⟩ : syracuseStep 718595 = 1077893) B1077893
theorem B718625 : Blo 475787 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B718643 : Blo 475787 718643 := bstep (se 1 (by rfl) ⟨538982, by rfl⟩ : syracuseStep 718643 = 1077965) B1077965
theorem B718673 : Blo 475787 718673 := bstep (se 2 (by rfl) ⟨269502, by rfl⟩ : syracuseStep 718673 = 539005) B539005
theorem B1210211 : Blo 475787 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B718691 : Blo 475787 718691 := bstep (se 1 (by rfl) ⟨539018, by rfl⟩ : syracuseStep 718691 = 1078037) B1078037
theorem B1079153 : Blo 475787 1079153 := bstep (se 2 (by rfl) ⟨404682, by rfl⟩ : syracuseStep 1079153 = 809365) B809365
theorem B718721 : Blo 475787 718721 := bstep (se 2 (by rfl) ⟨269520, by rfl⟩ : syracuseStep 718721 = 539041) B539041
theorem B1079171 : Blo 475787 1079171 := bstep (se 1 (by rfl) ⟨809378, by rfl⟩ : syracuseStep 1079171 = 1618757) B1618757
theorem B718739 : Blo 475787 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B817057 : Blo 475787 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B1308593 : Blo 475787 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B718769 : Blo 475787 718769 := bstep (se 2 (by rfl) ⟨269538, by rfl⟩ : syracuseStep 718769 = 539077) B539077
theorem B718787 : Blo 475787 718787 := bstep (se 1 (by rfl) ⟨539090, by rfl⟩ : syracuseStep 718787 = 1078181) B1078181
theorem B718817 : Blo 475787 718817 := bstep (se 2 (by rfl) ⟨269556, by rfl⟩ : syracuseStep 718817 = 539113) B539113
theorem B2455523 : Blo 475787 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B718835 : Blo 475787 718835 := bstep (se 1 (by rfl) ⟨539126, by rfl⟩ : syracuseStep 718835 = 1078253) B1078253
theorem B718865 : Blo 475787 718865 := bstep (se 2 (by rfl) ⟨269574, by rfl⟩ : syracuseStep 718865 = 539149) B539149
theorem B1210403 : Blo 475787 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B718883 : Blo 475787 718883 := bstep (se 1 (by rfl) ⟨539162, by rfl⟩ : syracuseStep 718883 = 1078325) B1078325
theorem B718913 : Blo 475787 718913 := bstep (se 2 (by rfl) ⟨269592, by rfl⟩ : syracuseStep 718913 = 539185) B539185
theorem B718931 : Blo 475787 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B718961 : Blo 475787 718961 := bstep (se 2 (by rfl) ⟨269610, by rfl⟩ : syracuseStep 718961 = 539221) B539221
theorem B718979 : Blo 475787 718979 := bstep (se 1 (by rfl) ⟨539234, by rfl⟩ : syracuseStep 718979 = 1078469) B1078469
theorem B1079441 : Blo 475787 1079441 := bstep (se 2 (by rfl) ⟨404790, by rfl⟩ : syracuseStep 1079441 = 809581) B809581
theorem B719009 : Blo 475787 719009 := bstep (se 2 (by rfl) ⟨269628, by rfl⟩ : syracuseStep 719009 = 539257) B539257
theorem B1079459 : Blo 475787 1079459 := bstep (se 1 (by rfl) ⟨809594, by rfl⟩ : syracuseStep 1079459 = 1619189) B1619189
theorem B2717873 : Blo 475787 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B719027 : Blo 475787 719027 := bstep (se 1 (by rfl) ⟨539270, by rfl⟩ : syracuseStep 719027 = 1078541) B1078541
theorem B719057 : Blo 475787 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B719075 : Blo 475787 719075 := bstep (se 1 (by rfl) ⟨539306, by rfl⟩ : syracuseStep 719075 = 1078613) B1078613
theorem B719105 : Blo 475787 719105 := bstep (se 2 (by rfl) ⟨269664, by rfl⟩ : syracuseStep 719105 = 539329) B539329
theorem B719123 : Blo 475787 719123 := bstep (se 1 (by rfl) ⟨539342, by rfl⟩ : syracuseStep 719123 = 1078685) B1078685
theorem B719153 : Blo 475787 719153 := bstep (se 2 (by rfl) ⟨269682, by rfl⟩ : syracuseStep 719153 = 539365) B539365
theorem B719171 : Blo 475787 719171 := bstep (se 1 (by rfl) ⟨539378, by rfl⟩ : syracuseStep 719171 = 1078757) B1078757
theorem B719201 : Blo 475787 719201 := bstep (se 2 (by rfl) ⟨269700, by rfl⟩ : syracuseStep 719201 = 539401) B539401
theorem B817523 : Blo 475787 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B719219 : Blo 475787 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B719249 : Blo 475787 719249 := bstep (se 2 (by rfl) ⟨269718, by rfl⟩ : syracuseStep 719249 = 539437) B539437
theorem B2619811 : Blo 475787 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B719267 : Blo 475787 719267 := bstep (se 1 (by rfl) ⟨539450, by rfl⟩ : syracuseStep 719267 = 1078901) B1078901
theorem B719297 : Blo 475787 719297 := bstep (se 2 (by rfl) ⟨269736, by rfl⟩ : syracuseStep 719297 = 539473) B539473
theorem B719315 : Blo 475787 719315 := bstep (se 1 (by rfl) ⟨539486, by rfl⟩ : syracuseStep 719315 = 1078973) B1078973
theorem B719345 : Blo 475787 719345 := bstep (se 2 (by rfl) ⟨269754, by rfl⟩ : syracuseStep 719345 = 539509) B539509
theorem B719363 : Blo 475787 719363 := bstep (se 1 (by rfl) ⟨539522, by rfl⟩ : syracuseStep 719363 = 1079045) B1079045
theorem B719393 : Blo 475787 719393 := bstep (se 2 (by rfl) ⟨269772, by rfl⟩ : syracuseStep 719393 = 539545) B539545
theorem B719411 : Blo 475787 719411 := bstep (se 1 (by rfl) ⟨539558, by rfl⟩ : syracuseStep 719411 = 1079117) B1079117
theorem B916049 : Blo 475787 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B719441 : Blo 475787 719441 := bstep (se 2 (by rfl) ⟨269790, by rfl⟩ : syracuseStep 719441 = 539581) B539581
theorem B719459 : Blo 475787 719459 := bstep (se 1 (by rfl) ⟨539594, by rfl⟩ : syracuseStep 719459 = 1079189) B1079189
theorem B719489 : Blo 475787 719489 := bstep (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) B539617
theorem B4291213 : Blo 475787 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B719507 : Blo 475787 719507 := bstep (se 1 (by rfl) ⟨539630, by rfl⟩ : syracuseStep 719507 = 1079261) B1079261
theorem B719537 : Blo 475787 719537 := bstep (se 2 (by rfl) ⟨269826, by rfl⟩ : syracuseStep 719537 = 539653) B539653
theorem B719555 : Blo 475787 719555 := bstep (se 1 (by rfl) ⟨539666, by rfl⟩ : syracuseStep 719555 = 1079333) B1079333
theorem B719585 : Blo 475787 719585 := bstep (se 2 (by rfl) ⟨269844, by rfl⟩ : syracuseStep 719585 = 539689) B539689
theorem B719603 : Blo 475787 719603 := bstep (se 1 (by rfl) ⟨539702, by rfl⟩ : syracuseStep 719603 = 1079405) B1079405
theorem B719633 : Blo 475787 719633 := bstep (se 2 (by rfl) ⟨269862, by rfl⟩ : syracuseStep 719633 = 539725) B539725
theorem B719651 : Blo 475787 719651 := bstep (se 1 (by rfl) ⟨539738, by rfl⟩ : syracuseStep 719651 = 1079477) B1079477
theorem B719681 : Blo 475787 719681 := bstep (se 2 (by rfl) ⟨269880, by rfl⟩ : syracuseStep 719681 = 539761) B539761
theorem B1145681 : Blo 475787 1145681 := bstep (se 2 (by rfl) ⟨429630, by rfl⟩ : syracuseStep 1145681 = 859261) B859261
theorem B1211345 : Blo 475787 1211345 := bstep (se 2 (by rfl) ⟨454254, by rfl⟩ : syracuseStep 1211345 = 908509) B908509
theorem B3505123 : Blo 475787 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B1211395 : Blo 475787 1211395 := bstep (se 1 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 1211395 = 1817093) B1817093
theorem B2423843 : Blo 475787 2423843 := bstep (se 1 (by rfl) ⟨1817882, by rfl⟩ : syracuseStep 2423843 = 3635765) B3635765
theorem B2751565 : Blo 475787 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B1211537 : Blo 475787 1211537 := bstep (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) B908653
theorem B3440069 : Blo 475787 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B1637891 : Blo 475787 1637891 := bstep (se 1 (by rfl) ⟨1228418, by rfl⟩ : syracuseStep 1637891 = 2456837) B2456837
theorem B3276323 : Blo 475787 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2719331 : Blo 475787 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B917219 : Blo 475787 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B2424653 : Blo 475787 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B3276875 : Blo 475787 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B3440819 : Blo 475787 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B819479 : Blo 475787 819479 := bstep (se 1 (by rfl) ⟨614609, by rfl⟩ : syracuseStep 819479 = 1229219) B1229219
theorem B2326849 : Blo 475787 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B1606067 : Blo 475787 1606067 := bstep (se 1 (by rfl) ⟨1204550, by rfl⟩ : syracuseStep 1606067 = 2409101) B2409101
theorem B3637709 : Blo 475787 3637709 := bstep (se 3 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 3637709 = 1364141) B1364141
theorem B2753041 : Blo 475787 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1245719 : Blo 475787 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1606337 : Blo 475787 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B1016563 : Blo 475787 1016563 := bstep (se 1 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 1016563 = 1524845) B1524845
theorem B1868689 : Blo 475787 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B3638195 : Blo 475787 3638195 := bstep (se 1 (by rfl) ⟨2728646, by rfl⟩ : syracuseStep 3638195 = 5457293) B5457293
theorem B2294801 : Blo 475787 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B2032715 : Blo 475787 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B1016921 : Blo 475787 1016921 := bstep (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) B762691
theorem B2425949 : Blo 475787 2425949 := bstep (se 3 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 2425949 = 909731) B909731
theorem B1213643 : Blo 475787 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B1606877 : Blo 475787 1606877 := bstep (se 3 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 1606877 = 602579) B602579
theorem B4916753 : Blo 475787 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B4064813 : Blo 475787 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B3868235 : Blo 475787 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B919127 : Blo 475787 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B4130605 : Blo 475787 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B4065497 : Blo 475787 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B1608011 : Blo 475787 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B8259941 : Blo 475787 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B3639653 : Blo 475787 3639653 := bstep (se 4 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 3639653 = 682435) B682435
theorem B1608281 : Blo 475787 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B2034355 : Blo 475787 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B3640139 : Blo 475787 3640139 := bstep (se 1 (by rfl) ⟨2730104, by rfl⟩ : syracuseStep 3640139 = 5460209) B5460209
theorem B1149785 : Blo 475787 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B1018955 : Blo 475787 1018955 := bstep (se 1 (by rfl) ⟨764216, by rfl⟩ : syracuseStep 1018955 = 1528433) B1528433
theorem B2428055 : Blo 475787 2428055 := bstep (se 1 (by rfl) ⟨1821041, by rfl⟩ : syracuseStep 2428055 = 3642083) B3642083
theorem B1608983 : Blo 475787 1608983 := bstep (se 1 (by rfl) ⟨1206737, by rfl⟩ : syracuseStep 1608983 = 2413475) B2413475
theorem B2034989 : Blo 475787 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B8293697 : Blo 475787 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B6098449 : Blo 475787 6098449 := bstep (se 2 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 6098449 = 4573837) B4573837
theorem B6524621 : Blo 475787 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1609523 : Blo 475787 1609523 := bstep (se 1 (by rfl) ⟨1207142, by rfl⟩ : syracuseStep 1609523 = 2414285) B2414285
theorem B1609793 : Blo 475787 1609793 := bstep (se 2 (by rfl) ⟨603672, by rfl⟩ : syracuseStep 1609793 = 1207345) B1207345
theorem B8720459 : Blo 475787 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B1020185 : Blo 475787 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B5444171 : Blo 475787 5444171 := bstep (se 1 (by rfl) ⟨4083128, by rfl⟩ : syracuseStep 5444171 = 8166257) B8166257
theorem B1610333 : Blo 475787 1610333 := bstep (se 3 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 1610333 = 603875) B603875
theorem B1020595 : Blo 475787 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B1807069 : Blo 475787 1807069 := bstep (se 3 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 1807069 = 677651) B677651
theorem B725785 : Blo 475787 725785 := bstep (se 2 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 725785 = 544339) B544339
theorem B1020851 : Blo 475787 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B2200537 : Blo 475787 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B3052505 : Blo 475787 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B922699 : Blo 475787 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B628235 : Blo 475787 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B1611467 : Blo 475787 1611467 := bstep (se 1 (by rfl) ⟨1208600, by rfl⟩ : syracuseStep 1611467 = 2417201) B2417201
theorem B1021825 : Blo 475787 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B1841075 : Blo 475787 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1808345 : Blo 475787 1808345 := bstep (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) B1356259
theorem B1611737 : Blo 475787 1611737 := bstep (se 2 (by rfl) ⟨604401, by rfl⟩ : syracuseStep 1611737 = 1208803) B1208803
theorem B3447191 : Blo 475787 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1087987 : Blo 475787 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B2333249 : Blo 475787 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B2202187 : Blo 475787 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B1612439 : Blo 475787 1612439 := bstep (se 1 (by rfl) ⟨1209329, by rfl⟩ : syracuseStep 1612439 = 2418659) B2418659
theorem B3873581 : Blo 475787 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B2038679 : Blo 475787 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B1612979 : Blo 475787 1612979 := bstep (se 1 (by rfl) ⟨1209734, by rfl⟩ : syracuseStep 1612979 = 2419469) B2419469
theorem B1613249 : Blo 475787 1613249 := bstep (se 2 (by rfl) ⟨604968, by rfl⟩ : syracuseStep 1613249 = 1209937) B1209937
theorem B1809971 : Blo 475787 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B1809985 : Blo 475787 1809985 := bstep (se 2 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 1809985 = 1357489) B1357489
theorem B3677987 : Blo 475787 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B860033 : Blo 475787 860033 := bstep (se 2 (by rfl) ⟨322512, by rfl⟩ : syracuseStep 860033 = 645025) B645025
theorem B1089409 : Blo 475787 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B1023961 : Blo 475787 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B1613789 : Blo 475787 1613789 := bstep (se 3 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 1613789 = 605171) B605171
theorem B2171083 : Blo 475787 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B860363 : Blo 475787 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B762455 : Blo 475787 762455 := bstep (se 1 (by rfl) ⟨571841, by rfl⟩ : syracuseStep 762455 = 1143683) B1143683
theorem B1614923 : Blo 475787 1614923 := bstep (se 1 (by rfl) ⟨1211192, by rfl⟩ : syracuseStep 1614923 = 2422385) B2422385
theorem B762967 : Blo 475787 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B861401 : Blo 475787 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B2041139 : Blo 475787 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B1615193 : Blo 475787 1615193 := bstep (se 2 (by rfl) ⟨605697, by rfl⟩ : syracuseStep 1615193 = 1211395) B1211395
theorem B1287517 : Blo 475787 1287517 := bstep (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) B482819
theorem B1811915 : Blo 475787 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B2041291 : Blo 475787 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B1811929 : Blo 475787 1811929 := bstep (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) B1358947
theorem B13608461 : Blo 475787 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B2041361 : Blo 475787 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B2729537 : Blo 475787 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B763787 : Blo 475787 763787 := bstep (se 1 (by rfl) ⟨572840, by rfl⟩ : syracuseStep 763787 = 1145681) B1145681
theorem B1615895 : Blo 475787 1615895 := bstep (se 1 (by rfl) ⟨1211921, by rfl⟩ : syracuseStep 1615895 = 2423843) B2423843
theorem B862259 : Blo 475787 862259 := bstep (se 1 (by rfl) ⟨646694, by rfl⟩ : syracuseStep 862259 = 1293389) B1293389
theorem B2304065 : Blo 475787 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B1091927 : Blo 475787 1091927 := bstep (se 1 (by rfl) ⟨818945, by rfl⟩ : syracuseStep 1091927 = 1637891) B1637891
theorem B1812887 : Blo 475787 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B862721 : Blo 475787 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B16198157 : Blo 475787 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B1616435 : Blo 475787 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B4074245 : Blo 475787 4074245 := bstep (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) B763921
theorem B535351 : Blo 475787 535351 := bstep (se 1 (by rfl) ⟨401513, by rfl⟩ : syracuseStep 535351 = 803027) B803027
theorem B1616705 : Blo 475787 1616705 := bstep (se 2 (by rfl) ⟨606264, by rfl⟩ : syracuseStep 1616705 = 1212529) B1212529
theorem B3877733 : Blo 475787 3877733 := bstep (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) B727075
theorem B535531 : Blo 475787 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B535639 : Blo 475787 535639 := bstep (se 1 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 535639 = 803459) B803459
theorem B2043053 : Blo 475787 2043053 := bstep (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) B766145
theorem B863435 : Blo 475787 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B6991109 : Blo 475787 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B535819 : Blo 475787 535819 := bstep (se 1 (by rfl) ⟨401864, by rfl⟩ : syracuseStep 535819 = 803729) B803729
theorem B1617245 : Blo 475787 1617245 := bstep (se 3 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 1617245 = 606467) B606467
theorem B3059045 : Blo 475787 3059045 := bstep (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) B573571
theorem B535927 : Blo 475787 535927 := bstep (se 1 (by rfl) ⟨401945, by rfl⟩ : syracuseStep 535927 = 803891) B803891
theorem B1355201 : Blo 475787 1355201 := bstep (se 2 (by rfl) ⟨508200, by rfl⟩ : syracuseStep 1355201 = 1016401) B1016401
theorem B536107 : Blo 475787 536107 := bstep (se 1 (by rfl) ⟨402080, by rfl⟩ : syracuseStep 536107 = 804161) B804161
theorem B1814147 : Blo 475787 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B536215 : Blo 475787 536215 := bstep (se 1 (by rfl) ⟨402161, by rfl⟩ : syracuseStep 536215 = 804323) B804323
theorem B2076353 : Blo 475787 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B536395 : Blo 475787 536395 := bstep (se 1 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 536395 = 804593) B804593
theorem B3059531 : Blo 475787 3059531 := bstep (se 1 (by rfl) ⟨2294648, by rfl⟩ : syracuseStep 3059531 = 4589297) B4589297
theorem B2043737 : Blo 475787 2043737 := bstep (se 2 (by rfl) ⟨766401, by rfl⟩ : syracuseStep 2043737 = 1532803) B1532803
theorem B2764637 : Blo 475787 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B2731927 : Blo 475787 2731927 := bstep (se 1 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 2731927 = 4097891) B4097891
theorem B536503 : Blo 475787 536503 := bstep (se 1 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 536503 = 804755) B804755
theorem B1224641 : Blo 475787 1224641 := bstep (se 2 (by rfl) ⟨459240, by rfl⟩ : syracuseStep 1224641 = 918481) B918481
theorem B15446051 : Blo 475787 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B536683 : Blo 475787 536683 := bstep (se 1 (by rfl) ⟨402512, by rfl⟩ : syracuseStep 536683 = 805025) B805025
theorem B1814731 : Blo 475787 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B536791 : Blo 475787 536791 := bstep (se 1 (by rfl) ⟨402593, by rfl⟩ : syracuseStep 536791 = 805187) B805187
theorem B536971 : Blo 475787 536971 := bstep (se 1 (by rfl) ⟨402728, by rfl⟩ : syracuseStep 536971 = 805457) B805457
theorem B1618379 : Blo 475787 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B537079 : Blo 475787 537079 := bstep (se 1 (by rfl) ⟨402809, by rfl⟩ : syracuseStep 537079 = 805619) B805619
theorem B602635 : Blo 475787 602635 := bstep (se 1 (by rfl) ⟨451976, by rfl⟩ : syracuseStep 602635 = 903953) B903953
theorem B3617297 : Blo 475787 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B1094219 : Blo 475787 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B537259 : Blo 475787 537259 := bstep (se 1 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 537259 = 805889) B805889
theorem B1618649 : Blo 475787 1618649 := bstep (se 2 (by rfl) ⟨606993, by rfl⟩ : syracuseStep 1618649 = 1213987) B1213987
theorem B7779077 : Blo 475787 7779077 := bstep (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) B1458577
theorem B602903 : Blo 475787 602903 := bstep (se 1 (by rfl) ⟨452177, by rfl⟩ : syracuseStep 602903 = 904355) B904355
theorem B537367 : Blo 475787 537367 := bstep (se 1 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 537367 = 806051) B806051
theorem B537547 : Blo 475787 537547 := bstep (se 1 (by rfl) ⟨403160, by rfl⟩ : syracuseStep 537547 = 806321) B806321
theorem B1356851 : Blo 475787 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B537655 : Blo 475787 537655 := bstep (se 1 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 537655 = 806483) B806483
theorem B1356875 : Blo 475787 1356875 := bstep (se 1 (by rfl) ⟨1017656, by rfl⟩ : syracuseStep 1356875 = 2035313) B2035313
theorem B537835 : Blo 475787 537835 := bstep (se 1 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 537835 = 806753) B806753
theorem B505099 : Blo 475787 505099 := bstep (se 1 (by rfl) ⟨378824, by rfl⟩ : syracuseStep 505099 = 757649) B757649
theorem B537943 : Blo 475787 537943 := bstep (se 1 (by rfl) ⟨403457, by rfl⟩ : syracuseStep 537943 = 806915) B806915
theorem B6862259 : Blo 475787 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B603607 : Blo 475787 603607 := bstep (se 1 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 603607 = 905411) B905411
theorem B538123 : Blo 475787 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B12269069 : Blo 475787 12269069 := bstep (se 3 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 12269069 = 4600901) B4600901
theorem B538231 : Blo 475787 538231 := bstep (se 1 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 538231 = 807347) B807347
theorem B538411 : Blo 475787 538411 := bstep (se 1 (by rfl) ⟨403808, by rfl⟩ : syracuseStep 538411 = 807617) B807617
theorem B3323693 : Blo 475787 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B1357661 : Blo 475787 1357661 := bstep (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) B509123
theorem B1292125 : Blo 475787 1292125 := bstep (se 3 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 1292125 = 484547) B484547
theorem B538519 : Blo 475787 538519 := bstep (se 1 (by rfl) ⟨403889, by rfl⟩ : syracuseStep 538519 = 807779) B807779
theorem B538699 : Blo 475787 538699 := bstep (se 1 (by rfl) ⟨404024, by rfl⟩ : syracuseStep 538699 = 808049) B808049
theorem B4077661 : Blo 475787 4077661 := bstep (se 3 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 4077661 = 1529123) B1529123
theorem B538807 : Blo 475787 538807 := bstep (se 1 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 538807 = 808211) B808211
theorem B538987 : Blo 475787 538987 := bstep (se 1 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 538987 = 808481) B808481
theorem B3062195 : Blo 475787 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B539095 : Blo 475787 539095 := bstep (se 1 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 539095 = 808643) B808643
theorem B3455581 : Blo 475787 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B539275 : Blo 475787 539275 := bstep (se 1 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 539275 = 808913) B808913
theorem B6896279 : Blo 475787 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1817261 : Blo 475787 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B539383 : Blo 475787 539383 := bstep (se 1 (by rfl) ⟨404537, by rfl⟩ : syracuseStep 539383 = 809075) B809075
theorem B7486307 : Blo 475787 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B539563 : Blo 475787 539563 := bstep (se 1 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 539563 = 809345) B809345
theorem B539671 : Blo 475787 539671 := bstep (se 1 (by rfl) ⟨404753, by rfl⟩ : syracuseStep 539671 = 809507) B809507
theorem B605323 : Blo 475787 605323 := bstep (se 1 (by rfl) ⟨453992, by rfl⟩ : syracuseStep 605323 = 907985) B907985
theorem B965785 : Blo 475787 965785 := bstep (se 2 (by rfl) ⟨362169, by rfl⟩ : syracuseStep 965785 = 724339) B724339
theorem B2047169 : Blo 475787 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B3882275 : Blo 475787 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B1818035 : Blo 475787 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B2047511 : Blo 475787 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B1359449 : Blo 475787 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B736921 : Blo 475787 736921 := bstep (se 2 (by rfl) ⟨276345, by rfl⟩ : syracuseStep 736921 = 552691) B552691
theorem B3489581 : Blo 475787 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1261363 : Blo 475787 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1457995 : Blo 475787 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B18693989 : Blo 475787 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B1982339 : Blo 475787 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B1359767 : Blo 475787 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B6864857 : Blo 475787 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B606295 : Blo 475787 606295 := bstep (se 1 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 606295 = 909443) B909443
theorem B4145357 : Blo 475787 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B3621185 : Blo 475787 3621185 := bstep (se 2 (by rfl) ⟨1357944, by rfl⟩ : syracuseStep 3621185 = 2715889) B2715889
theorem B2048435 : Blo 475787 2048435 := bstep (se 1 (by rfl) ⟨1536326, by rfl⟩ : syracuseStep 2048435 = 3072653) B3072653
theorem B508375 : Blo 475787 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B803351 : Blo 475787 803351 := bstep (se 1 (by rfl) ⟨602513, by rfl⟩ : syracuseStep 803351 = 1205027) B1205027
theorem B1229363 : Blo 475787 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B475787 : Blo 475787 475787 := bstep (se 1 (by rfl) ⟨356840, by rfl⟩ : syracuseStep 475787 = 713681) B713681
theorem B508555 : Blo 475787 508555 := bstep (se 1 (by rfl) ⟨381416, by rfl⟩ : syracuseStep 508555 = 762833) B762833
theorem B475799 : Blo 475787 475799 := bstep (se 1 (by rfl) ⟨356849, by rfl⟩ : syracuseStep 475799 = 713699) B713699
theorem B803479 : Blo 475787 803479 := bstep (se 1 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 803479 = 1205219) B1205219
theorem B475819 : Blo 475787 475819 := bstep (se 1 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 475819 = 713729) B713729
theorem B475831 : Blo 475787 475831 := bstep (se 1 (by rfl) ⟨356873, by rfl⟩ : syracuseStep 475831 = 713747) B713747
theorem B1360577 : Blo 475787 1360577 := bstep (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) B1020433
theorem B475851 : Blo 475787 475851 := bstep (se 1 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 475851 = 713777) B713777
theorem B475863 : Blo 475787 475863 := bstep (se 1 (by rfl) ⟨356897, by rfl⟩ : syracuseStep 475863 = 713795) B713795
theorem B475883 : Blo 475787 475883 := bstep (se 1 (by rfl) ⟨356912, by rfl⟩ : syracuseStep 475883 = 713825) B713825
theorem B475895 : Blo 475787 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B475915 : Blo 475787 475915 := bstep (se 1 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 475915 = 713873) B713873
theorem B475927 : Blo 475787 475927 := bstep (se 1 (by rfl) ⟨356945, by rfl⟩ : syracuseStep 475927 = 713891) B713891
theorem B475947 : Blo 475787 475947 := bstep (se 1 (by rfl) ⟨356960, by rfl⟩ : syracuseStep 475947 = 713921) B713921
theorem B475959 : Blo 475787 475959 := bstep (se 1 (by rfl) ⟨356969, by rfl⟩ : syracuseStep 475959 = 713939) B713939
theorem B475979 : Blo 475787 475979 := bstep (se 1 (by rfl) ⟨356984, by rfl⟩ : syracuseStep 475979 = 713969) B713969
theorem B475991 : Blo 475787 475991 := bstep (se 1 (by rfl) ⟨356993, by rfl⟩ : syracuseStep 475991 = 713987) B713987
theorem B476011 : Blo 475787 476011 := bstep (se 1 (by rfl) ⟨357008, by rfl⟩ : syracuseStep 476011 = 714017) B714017
theorem B476023 : Blo 475787 476023 := bstep (se 1 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 476023 = 714035) B714035
theorem B1819523 : Blo 475787 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B476043 : Blo 475787 476043 := bstep (se 1 (by rfl) ⟨357032, by rfl⟩ : syracuseStep 476043 = 714065) B714065
theorem B607115 : Blo 475787 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B476055 : Blo 475787 476055 := bstep (se 1 (by rfl) ⟨357041, by rfl⟩ : syracuseStep 476055 = 714083) B714083
theorem B476075 : Blo 475787 476075 := bstep (se 1 (by rfl) ⟨357056, by rfl⟩ : syracuseStep 476075 = 714113) B714113
theorem B476087 : Blo 475787 476087 := bstep (se 1 (by rfl) ⟨357065, by rfl⟩ : syracuseStep 476087 = 714131) B714131
theorem B476107 : Blo 475787 476107 := bstep (se 1 (by rfl) ⟨357080, by rfl⟩ : syracuseStep 476107 = 714161) B714161
theorem B476119 : Blo 475787 476119 := bstep (se 1 (by rfl) ⟨357089, by rfl⟩ : syracuseStep 476119 = 714179) B714179
theorem B476139 : Blo 475787 476139 := bstep (se 1 (by rfl) ⟨357104, by rfl⟩ : syracuseStep 476139 = 714209) B714209
theorem B476151 : Blo 475787 476151 := bstep (se 1 (by rfl) ⟨357113, by rfl⟩ : syracuseStep 476151 = 714227) B714227
theorem B476171 : Blo 475787 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B476183 : Blo 475787 476183 := bstep (se 1 (by rfl) ⟨357137, by rfl⟩ : syracuseStep 476183 = 714275) B714275
theorem B476203 : Blo 475787 476203 := bstep (se 1 (by rfl) ⟨357152, by rfl⟩ : syracuseStep 476203 = 714305) B714305
theorem B476215 : Blo 475787 476215 := bstep (se 1 (by rfl) ⟨357161, by rfl⟩ : syracuseStep 476215 = 714323) B714323
theorem B476235 : Blo 475787 476235 := bstep (se 1 (by rfl) ⟨357176, by rfl⟩ : syracuseStep 476235 = 714353) B714353
theorem B476247 : Blo 475787 476247 := bstep (se 1 (by rfl) ⟨357185, by rfl⟩ : syracuseStep 476247 = 714371) B714371
theorem B476267 : Blo 475787 476267 := bstep (se 1 (by rfl) ⟨357200, by rfl⟩ : syracuseStep 476267 = 714401) B714401
theorem B476279 : Blo 475787 476279 := bstep (se 1 (by rfl) ⟨357209, by rfl⟩ : syracuseStep 476279 = 714419) B714419
theorem B476299 : Blo 475787 476299 := bstep (se 1 (by rfl) ⟨357224, by rfl⟩ : syracuseStep 476299 = 714449) B714449
theorem B476311 : Blo 475787 476311 := bstep (se 1 (by rfl) ⟨357233, by rfl⟩ : syracuseStep 476311 = 714467) B714467
theorem B476331 : Blo 475787 476331 := bstep (se 1 (by rfl) ⟨357248, by rfl⟩ : syracuseStep 476331 = 714497) B714497
theorem B476343 : Blo 475787 476343 := bstep (se 1 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 476343 = 714515) B714515
theorem B476363 : Blo 475787 476363 := bstep (se 1 (by rfl) ⟨357272, by rfl⟩ : syracuseStep 476363 = 714545) B714545
theorem B476375 : Blo 475787 476375 := bstep (se 1 (by rfl) ⟨357281, by rfl⟩ : syracuseStep 476375 = 714563) B714563
theorem B476395 : Blo 475787 476395 := bstep (se 1 (by rfl) ⟨357296, by rfl⟩ : syracuseStep 476395 = 714593) B714593
theorem B476407 : Blo 475787 476407 := bstep (se 1 (by rfl) ⟨357305, by rfl⟩ : syracuseStep 476407 = 714611) B714611
theorem B476427 : Blo 475787 476427 := bstep (se 1 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 476427 = 714641) B714641
theorem B804107 : Blo 475787 804107 := bstep (se 1 (by rfl) ⟨603080, by rfl⟩ : syracuseStep 804107 = 1206161) B1206161
theorem B476439 : Blo 475787 476439 := bstep (se 1 (by rfl) ⟨357329, by rfl⟩ : syracuseStep 476439 = 714659) B714659
theorem B1295639 : Blo 475787 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B476459 : Blo 475787 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B476471 : Blo 475787 476471 := bstep (se 1 (by rfl) ⟨357353, by rfl⟩ : syracuseStep 476471 = 714707) B714707
theorem B476491 : Blo 475787 476491 := bstep (se 1 (by rfl) ⟨357368, by rfl⟩ : syracuseStep 476491 = 714737) B714737
theorem B1819979 : Blo 475787 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B476503 : Blo 475787 476503 := bstep (se 1 (by rfl) ⟨357377, by rfl⟩ : syracuseStep 476503 = 714755) B714755
theorem B476523 : Blo 475787 476523 := bstep (se 1 (by rfl) ⟨357392, by rfl⟩ : syracuseStep 476523 = 714785) B714785
theorem B476535 : Blo 475787 476535 := bstep (se 1 (by rfl) ⟨357401, by rfl⟩ : syracuseStep 476535 = 714803) B714803
theorem B476555 : Blo 475787 476555 := bstep (se 1 (by rfl) ⟨357416, by rfl⟩ : syracuseStep 476555 = 714833) B714833
theorem B804235 : Blo 475787 804235 := bstep (se 1 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 804235 = 1206353) B1206353
theorem B476567 : Blo 475787 476567 := bstep (se 1 (by rfl) ⟨357425, by rfl⟩ : syracuseStep 476567 = 714851) B714851
theorem B476587 : Blo 475787 476587 := bstep (se 1 (by rfl) ⟨357440, by rfl⟩ : syracuseStep 476587 = 714881) B714881
theorem B476599 : Blo 475787 476599 := bstep (se 1 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 476599 = 714899) B714899
theorem B476619 : Blo 475787 476619 := bstep (se 1 (by rfl) ⟨357464, by rfl⟩ : syracuseStep 476619 = 714929) B714929
theorem B476631 : Blo 475787 476631 := bstep (se 1 (by rfl) ⟨357473, by rfl⟩ : syracuseStep 476631 = 714947) B714947
theorem B476651 : Blo 475787 476651 := bstep (se 1 (by rfl) ⟨357488, by rfl⟩ : syracuseStep 476651 = 714977) B714977
theorem B476663 : Blo 475787 476663 := bstep (se 1 (by rfl) ⟨357497, by rfl⟩ : syracuseStep 476663 = 714995) B714995
theorem B476683 : Blo 475787 476683 := bstep (se 1 (by rfl) ⟨357512, by rfl⟩ : syracuseStep 476683 = 715025) B715025
theorem B1820177 : Blo 475787 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B476695 : Blo 475787 476695 := bstep (se 1 (by rfl) ⟨357521, by rfl⟩ : syracuseStep 476695 = 715043) B715043
theorem B804377 : Blo 475787 804377 := bstep (se 2 (by rfl) ⟨301641, by rfl⟩ : syracuseStep 804377 = 603283) B603283
theorem B476715 : Blo 475787 476715 := bstep (se 1 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 476715 = 715073) B715073
theorem B2442797 : Blo 475787 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B476727 : Blo 475787 476727 := bstep (se 1 (by rfl) ⟨357545, by rfl⟩ : syracuseStep 476727 = 715091) B715091
theorem B476747 : Blo 475787 476747 := bstep (se 1 (by rfl) ⟨357560, by rfl⟩ : syracuseStep 476747 = 715121) B715121
theorem B476759 : Blo 475787 476759 := bstep (se 1 (by rfl) ⟨357569, by rfl⟩ : syracuseStep 476759 = 715139) B715139
theorem B476779 : Blo 475787 476779 := bstep (se 1 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 476779 = 715169) B715169
theorem B476791 : Blo 475787 476791 := bstep (se 1 (by rfl) ⟨357593, by rfl⟩ : syracuseStep 476791 = 715187) B715187
theorem B476811 : Blo 475787 476811 := bstep (se 1 (by rfl) ⟨357608, by rfl⟩ : syracuseStep 476811 = 715217) B715217
theorem B476823 : Blo 475787 476823 := bstep (se 1 (by rfl) ⟨357617, by rfl⟩ : syracuseStep 476823 = 715235) B715235
theorem B804505 : Blo 475787 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B476843 : Blo 475787 476843 := bstep (se 1 (by rfl) ⟨357632, by rfl⟩ : syracuseStep 476843 = 715265) B715265
theorem B476855 : Blo 475787 476855 := bstep (se 1 (by rfl) ⟨357641, by rfl⟩ : syracuseStep 476855 = 715283) B715283
theorem B476875 : Blo 475787 476875 := bstep (se 1 (by rfl) ⟨357656, by rfl⟩ : syracuseStep 476875 = 715313) B715313
theorem B476887 : Blo 475787 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B476907 : Blo 475787 476907 := bstep (se 1 (by rfl) ⟨357680, by rfl⟩ : syracuseStep 476907 = 715361) B715361
theorem B476919 : Blo 475787 476919 := bstep (se 1 (by rfl) ⟨357689, by rfl⟩ : syracuseStep 476919 = 715379) B715379
theorem B476939 : Blo 475787 476939 := bstep (se 1 (by rfl) ⟨357704, by rfl⟩ : syracuseStep 476939 = 715409) B715409
theorem B476951 : Blo 475787 476951 := bstep (se 1 (by rfl) ⟨357713, by rfl⟩ : syracuseStep 476951 = 715427) B715427
theorem B476971 : Blo 475787 476971 := bstep (se 1 (by rfl) ⟨357728, by rfl⟩ : syracuseStep 476971 = 715457) B715457
theorem B476983 : Blo 475787 476983 := bstep (se 1 (by rfl) ⟨357737, by rfl⟩ : syracuseStep 476983 = 715475) B715475
theorem B477003 : Blo 475787 477003 := bstep (se 1 (by rfl) ⟨357752, by rfl⟩ : syracuseStep 477003 = 715505) B715505
theorem B477015 : Blo 475787 477015 := bstep (se 1 (by rfl) ⟨357761, by rfl⟩ : syracuseStep 477015 = 715523) B715523
theorem B477035 : Blo 475787 477035 := bstep (se 1 (by rfl) ⟨357776, by rfl⟩ : syracuseStep 477035 = 715553) B715553
theorem B477047 : Blo 475787 477047 := bstep (se 1 (by rfl) ⟨357785, by rfl⟩ : syracuseStep 477047 = 715571) B715571
theorem B477067 : Blo 475787 477067 := bstep (se 1 (by rfl) ⟨357800, by rfl⟩ : syracuseStep 477067 = 715601) B715601
theorem B477079 : Blo 475787 477079 := bstep (se 1 (by rfl) ⟨357809, by rfl⟩ : syracuseStep 477079 = 715619) B715619
theorem B477099 : Blo 475787 477099 := bstep (se 1 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 477099 = 715649) B715649
theorem B477111 : Blo 475787 477111 := bstep (se 1 (by rfl) ⟨357833, by rfl⟩ : syracuseStep 477111 = 715667) B715667
theorem B477131 : Blo 475787 477131 := bstep (se 1 (by rfl) ⟨357848, by rfl⟩ : syracuseStep 477131 = 715697) B715697
theorem B477143 : Blo 475787 477143 := bstep (se 1 (by rfl) ⟨357857, by rfl⟩ : syracuseStep 477143 = 715715) B715715
theorem B477163 : Blo 475787 477163 := bstep (se 1 (by rfl) ⟨357872, by rfl⟩ : syracuseStep 477163 = 715745) B715745
theorem B477175 : Blo 475787 477175 := bstep (se 1 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 477175 = 715763) B715763
theorem B477195 : Blo 475787 477195 := bstep (se 1 (by rfl) ⟨357896, by rfl⟩ : syracuseStep 477195 = 715793) B715793
theorem B477207 : Blo 475787 477207 := bstep (se 1 (by rfl) ⟨357905, by rfl⟩ : syracuseStep 477207 = 715811) B715811
theorem B477227 : Blo 475787 477227 := bstep (se 1 (by rfl) ⟨357920, by rfl⟩ : syracuseStep 477227 = 715841) B715841
theorem B477239 : Blo 475787 477239 := bstep (se 1 (by rfl) ⟨357929, by rfl⟩ : syracuseStep 477239 = 715859) B715859
theorem B477259 : Blo 475787 477259 := bstep (se 1 (by rfl) ⟨357944, by rfl⟩ : syracuseStep 477259 = 715889) B715889
theorem B477271 : Blo 475787 477271 := bstep (se 1 (by rfl) ⟨357953, by rfl⟩ : syracuseStep 477271 = 715907) B715907
theorem B477291 : Blo 475787 477291 := bstep (se 1 (by rfl) ⟨357968, by rfl⟩ : syracuseStep 477291 = 715937) B715937
theorem B477303 : Blo 475787 477303 := bstep (se 1 (by rfl) ⟨357977, by rfl⟩ : syracuseStep 477303 = 715955) B715955
theorem B903307 : Blo 475787 903307 := bstep (se 1 (by rfl) ⟨677480, by rfl⟩ : syracuseStep 903307 = 1354961) B1354961
theorem B477323 : Blo 475787 477323 := bstep (se 1 (by rfl) ⟨357992, by rfl⟩ : syracuseStep 477323 = 715985) B715985
theorem B477335 : Blo 475787 477335 := bstep (se 1 (by rfl) ⟨358001, by rfl⟩ : syracuseStep 477335 = 716003) B716003
theorem B477355 : Blo 475787 477355 := bstep (se 1 (by rfl) ⟨358016, by rfl⟩ : syracuseStep 477355 = 716033) B716033
theorem B4475057 : Blo 475787 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B477367 : Blo 475787 477367 := bstep (se 1 (by rfl) ⟨358025, by rfl⟩ : syracuseStep 477367 = 716051) B716051
theorem B477387 : Blo 475787 477387 := bstep (se 1 (by rfl) ⟨358040, by rfl⟩ : syracuseStep 477387 = 716081) B716081
theorem B903383 : Blo 475787 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B805079 : Blo 475787 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B3623129 : Blo 475787 3623129 := bstep (se 2 (by rfl) ⟨1358673, by rfl⟩ : syracuseStep 3623129 = 2717347) B2717347
theorem B477399 : Blo 475787 477399 := bstep (se 1 (by rfl) ⟨358049, by rfl⟩ : syracuseStep 477399 = 716099) B716099
theorem B477419 : Blo 475787 477419 := bstep (se 1 (by rfl) ⟨358064, by rfl⟩ : syracuseStep 477419 = 716129) B716129
theorem B477431 : Blo 475787 477431 := bstep (se 1 (by rfl) ⟨358073, by rfl⟩ : syracuseStep 477431 = 716147) B716147
theorem B477451 : Blo 475787 477451 := bstep (se 1 (by rfl) ⟨358088, by rfl⟩ : syracuseStep 477451 = 716177) B716177
theorem B477463 : Blo 475787 477463 := bstep (se 1 (by rfl) ⟨358097, by rfl⟩ : syracuseStep 477463 = 716195) B716195
theorem B1820951 : Blo 475787 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B477483 : Blo 475787 477483 := bstep (se 1 (by rfl) ⟨358112, by rfl⟩ : syracuseStep 477483 = 716225) B716225
theorem B477495 : Blo 475787 477495 := bstep (se 1 (by rfl) ⟨358121, by rfl⟩ : syracuseStep 477495 = 716243) B716243
theorem B477515 : Blo 475787 477515 := bstep (se 1 (by rfl) ⟨358136, by rfl⟩ : syracuseStep 477515 = 716273) B716273
theorem B1362251 : Blo 475787 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B805207 : Blo 475787 805207 := bstep (se 1 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 805207 = 1207811) B1207811
theorem B477527 : Blo 475787 477527 := bstep (se 1 (by rfl) ⟨358145, by rfl⟩ : syracuseStep 477527 = 716291) B716291
theorem B477547 : Blo 475787 477547 := bstep (se 1 (by rfl) ⟨358160, by rfl⟩ : syracuseStep 477547 = 716321) B716321
theorem B477559 : Blo 475787 477559 := bstep (se 1 (by rfl) ⟨358169, by rfl⟩ : syracuseStep 477559 = 716339) B716339
theorem B2410883 : Blo 475787 2410883 := bstep (se 1 (by rfl) ⟨1808162, by rfl⟩ : syracuseStep 2410883 = 3616325) B3616325
theorem B477579 : Blo 475787 477579 := bstep (se 1 (by rfl) ⟨358184, by rfl⟩ : syracuseStep 477579 = 716369) B716369
theorem B477591 : Blo 475787 477591 := bstep (se 1 (by rfl) ⟨358193, by rfl⟩ : syracuseStep 477591 = 716387) B716387
theorem B477611 : Blo 475787 477611 := bstep (se 1 (by rfl) ⟨358208, by rfl⟩ : syracuseStep 477611 = 716417) B716417
theorem B2214323 : Blo 475787 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B477623 : Blo 475787 477623 := bstep (se 1 (by rfl) ⟨358217, by rfl⟩ : syracuseStep 477623 = 716435) B716435
theorem B477643 : Blo 475787 477643 := bstep (se 1 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 477643 = 716465) B716465
theorem B477655 : Blo 475787 477655 := bstep (se 1 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 477655 = 716483) B716483
theorem B969175 : Blo 475787 969175 := bstep (se 1 (by rfl) ⟨726881, by rfl⟩ : syracuseStep 969175 = 1453763) B1453763
theorem B575959 : Blo 475787 575959 := bstep (se 1 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 575959 = 863939) B863939
theorem B1821149 : Blo 475787 1821149 := bstep (se 3 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 1821149 = 682931) B682931
theorem B477675 : Blo 475787 477675 := bstep (se 1 (by rfl) ⟨358256, by rfl⟩ : syracuseStep 477675 = 716513) B716513
theorem B477687 : Blo 475787 477687 := bstep (se 1 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 477687 = 716531) B716531
theorem B477707 : Blo 475787 477707 := bstep (se 1 (by rfl) ⟨358280, by rfl⟩ : syracuseStep 477707 = 716561) B716561
theorem B477719 : Blo 475787 477719 := bstep (se 1 (by rfl) ⟨358289, by rfl⟩ : syracuseStep 477719 = 716579) B716579
theorem B477739 : Blo 475787 477739 := bstep (se 1 (by rfl) ⟨358304, by rfl⟩ : syracuseStep 477739 = 716609) B716609
theorem B477751 : Blo 475787 477751 := bstep (se 1 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 477751 = 716627) B716627
theorem B477771 : Blo 475787 477771 := bstep (se 1 (by rfl) ⟨358328, by rfl⟩ : syracuseStep 477771 = 716657) B716657
theorem B477783 : Blo 475787 477783 := bstep (se 1 (by rfl) ⟨358337, by rfl⟩ : syracuseStep 477783 = 716675) B716675
theorem B477803 : Blo 475787 477803 := bstep (se 1 (by rfl) ⟨358352, by rfl⟩ : syracuseStep 477803 = 716705) B716705
theorem B510571 : Blo 475787 510571 := bstep (se 1 (by rfl) ⟨382928, by rfl⟩ : syracuseStep 510571 = 765857) B765857
theorem B477815 : Blo 475787 477815 := bstep (se 1 (by rfl) ⟨358361, by rfl⟩ : syracuseStep 477815 = 716723) B716723
theorem B477835 : Blo 475787 477835 := bstep (se 1 (by rfl) ⟨358376, by rfl⟩ : syracuseStep 477835 = 716753) B716753
theorem B2443927 : Blo 475787 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B477847 : Blo 475787 477847 := bstep (se 1 (by rfl) ⟨358385, by rfl⟩ : syracuseStep 477847 = 716771) B716771
theorem B477867 : Blo 475787 477867 := bstep (se 1 (by rfl) ⟨358400, by rfl⟩ : syracuseStep 477867 = 716801) B716801
theorem B477879 : Blo 475787 477879 := bstep (se 1 (by rfl) ⟨358409, by rfl⟩ : syracuseStep 477879 = 716819) B716819
theorem B477899 : Blo 475787 477899 := bstep (se 1 (by rfl) ⟨358424, by rfl⟩ : syracuseStep 477899 = 716849) B716849
theorem B477911 : Blo 475787 477911 := bstep (se 1 (by rfl) ⟨358433, by rfl⟩ : syracuseStep 477911 = 716867) B716867
theorem B477931 : Blo 475787 477931 := bstep (se 1 (by rfl) ⟨358448, by rfl⟩ : syracuseStep 477931 = 716897) B716897
theorem B477943 : Blo 475787 477943 := bstep (se 1 (by rfl) ⟨358457, by rfl⟩ : syracuseStep 477943 = 716915) B716915
theorem B477963 : Blo 475787 477963 := bstep (se 1 (by rfl) ⟨358472, by rfl⟩ : syracuseStep 477963 = 716945) B716945
theorem B477975 : Blo 475787 477975 := bstep (se 1 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 477975 = 716963) B716963
theorem B477995 : Blo 475787 477995 := bstep (se 1 (by rfl) ⟨358496, by rfl⟩ : syracuseStep 477995 = 716993) B716993
theorem B478007 : Blo 475787 478007 := bstep (se 1 (by rfl) ⟨358505, by rfl⟩ : syracuseStep 478007 = 717011) B717011
theorem B478027 : Blo 475787 478027 := bstep (se 1 (by rfl) ⟨358520, by rfl⟩ : syracuseStep 478027 = 717041) B717041
theorem B478039 : Blo 475787 478039 := bstep (se 1 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 478039 = 717059) B717059
theorem B478059 : Blo 475787 478059 := bstep (se 1 (by rfl) ⟨358544, by rfl⟩ : syracuseStep 478059 = 717089) B717089
theorem B904051 : Blo 475787 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B478071 : Blo 475787 478071 := bstep (se 1 (by rfl) ⟨358553, by rfl⟩ : syracuseStep 478071 = 717107) B717107
theorem B478091 : Blo 475787 478091 := bstep (se 1 (by rfl) ⟨358568, by rfl⟩ : syracuseStep 478091 = 717137) B717137
theorem B478103 : Blo 475787 478103 := bstep (se 1 (by rfl) ⟨358577, by rfl⟩ : syracuseStep 478103 = 717155) B717155
theorem B478123 : Blo 475787 478123 := bstep (se 1 (by rfl) ⟨358592, by rfl⟩ : syracuseStep 478123 = 717185) B717185
theorem B478135 : Blo 475787 478135 := bstep (se 1 (by rfl) ⟨358601, by rfl⟩ : syracuseStep 478135 = 717203) B717203
theorem B805835 : Blo 475787 805835 := bstep (se 1 (by rfl) ⟨604376, by rfl⟩ : syracuseStep 805835 = 1208753) B1208753
theorem B478155 : Blo 475787 478155 := bstep (se 1 (by rfl) ⟨358616, by rfl⟩ : syracuseStep 478155 = 717233) B717233
theorem B478167 : Blo 475787 478167 := bstep (se 1 (by rfl) ⟨358625, by rfl⟩ : syracuseStep 478167 = 717251) B717251
theorem B478187 : Blo 475787 478187 := bstep (se 1 (by rfl) ⟨358640, by rfl⟩ : syracuseStep 478187 = 717281) B717281
theorem B478199 : Blo 475787 478199 := bstep (se 1 (by rfl) ⟨358649, by rfl⟩ : syracuseStep 478199 = 717299) B717299
theorem B478219 : Blo 475787 478219 := bstep (se 1 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 478219 = 717329) B717329
theorem B478231 : Blo 475787 478231 := bstep (se 1 (by rfl) ⟨358673, by rfl⟩ : syracuseStep 478231 = 717347) B717347
theorem B478251 : Blo 475787 478251 := bstep (se 1 (by rfl) ⟨358688, by rfl⟩ : syracuseStep 478251 = 717377) B717377
theorem B478263 : Blo 475787 478263 := bstep (se 1 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 478263 = 717395) B717395
theorem B805963 : Blo 475787 805963 := bstep (se 1 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 805963 = 1208945) B1208945
theorem B478283 : Blo 475787 478283 := bstep (se 1 (by rfl) ⟨358712, by rfl⟩ : syracuseStep 478283 = 717425) B717425
theorem B904279 : Blo 475787 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B478295 : Blo 475787 478295 := bstep (se 1 (by rfl) ⟨358721, by rfl⟩ : syracuseStep 478295 = 717443) B717443
theorem B478315 : Blo 475787 478315 := bstep (se 1 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 478315 = 717473) B717473
theorem B478327 : Blo 475787 478327 := bstep (se 1 (by rfl) ⟨358745, by rfl⟩ : syracuseStep 478327 = 717491) B717491
theorem B478347 : Blo 475787 478347 := bstep (se 1 (by rfl) ⟨358760, by rfl⟩ : syracuseStep 478347 = 717521) B717521
theorem B478359 : Blo 475787 478359 := bstep (se 1 (by rfl) ⟨358769, by rfl⟩ : syracuseStep 478359 = 717539) B717539
theorem B478379 : Blo 475787 478379 := bstep (se 1 (by rfl) ⟨358784, by rfl⟩ : syracuseStep 478379 = 717569) B717569
theorem B478391 : Blo 475787 478391 := bstep (se 1 (by rfl) ⟨358793, by rfl⟩ : syracuseStep 478391 = 717587) B717587
theorem B904385 : Blo 475787 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B478411 : Blo 475787 478411 := bstep (se 1 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 478411 = 717617) B717617
theorem B478423 : Blo 475787 478423 := bstep (se 1 (by rfl) ⟨358817, by rfl⟩ : syracuseStep 478423 = 717635) B717635
theorem B806105 : Blo 475787 806105 := bstep (se 2 (by rfl) ⟨302289, by rfl⟩ : syracuseStep 806105 = 604579) B604579
theorem B3493081 : Blo 475787 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1723609 : Blo 475787 1723609 := bstep (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) B1292707
theorem B478443 : Blo 475787 478443 := bstep (se 1 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 478443 = 717665) B717665
theorem B478455 : Blo 475787 478455 := bstep (se 1 (by rfl) ⟨358841, by rfl⟩ : syracuseStep 478455 = 717683) B717683
theorem B478475 : Blo 475787 478475 := bstep (se 1 (by rfl) ⟨358856, by rfl⟩ : syracuseStep 478475 = 717713) B717713
theorem B478487 : Blo 475787 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B478507 : Blo 475787 478507 := bstep (se 1 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 478507 = 717761) B717761
theorem B478519 : Blo 475787 478519 := bstep (se 1 (by rfl) ⟨358889, by rfl⟩ : syracuseStep 478519 = 717779) B717779
theorem B478539 : Blo 475787 478539 := bstep (se 1 (by rfl) ⟨358904, by rfl⟩ : syracuseStep 478539 = 717809) B717809
theorem B478551 : Blo 475787 478551 := bstep (se 1 (by rfl) ⟨358913, by rfl⟩ : syracuseStep 478551 = 717827) B717827
theorem B904537 : Blo 475787 904537 := bstep (se 2 (by rfl) ⟨339201, by rfl⟩ : syracuseStep 904537 = 678403) B678403
theorem B806233 : Blo 475787 806233 := bstep (se 2 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 806233 = 604675) B604675
theorem B478571 : Blo 475787 478571 := bstep (se 1 (by rfl) ⟨358928, by rfl⟩ : syracuseStep 478571 = 717857) B717857
theorem B478583 : Blo 475787 478583 := bstep (se 1 (by rfl) ⟨358937, by rfl⟩ : syracuseStep 478583 = 717875) B717875
theorem B478603 : Blo 475787 478603 := bstep (se 1 (by rfl) ⟨358952, by rfl⟩ : syracuseStep 478603 = 717905) B717905
theorem B478615 : Blo 475787 478615 := bstep (se 1 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 478615 = 717923) B717923
theorem B478635 : Blo 475787 478635 := bstep (se 1 (by rfl) ⟨358976, by rfl⟩ : syracuseStep 478635 = 717953) B717953
theorem B478647 : Blo 475787 478647 := bstep (se 1 (by rfl) ⟨358985, by rfl⟩ : syracuseStep 478647 = 717971) B717971
theorem B478667 : Blo 475787 478667 := bstep (se 1 (by rfl) ⟨359000, by rfl⟩ : syracuseStep 478667 = 718001) B718001
theorem B478679 : Blo 475787 478679 := bstep (se 1 (by rfl) ⟨359009, by rfl⟩ : syracuseStep 478679 = 718019) B718019
theorem B478699 : Blo 475787 478699 := bstep (se 1 (by rfl) ⟨359024, by rfl⟩ : syracuseStep 478699 = 718049) B718049
theorem B478711 : Blo 475787 478711 := bstep (se 1 (by rfl) ⟨359033, by rfl⟩ : syracuseStep 478711 = 718067) B718067
theorem B478731 : Blo 475787 478731 := bstep (se 1 (by rfl) ⟨359048, by rfl⟩ : syracuseStep 478731 = 718097) B718097
theorem B5721617 : Blo 475787 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B478743 : Blo 475787 478743 := bstep (se 1 (by rfl) ⟨359057, by rfl⟩ : syracuseStep 478743 = 718115) B718115
theorem B478763 : Blo 475787 478763 := bstep (se 1 (by rfl) ⟨359072, by rfl⟩ : syracuseStep 478763 = 718145) B718145
theorem B478775 : Blo 475787 478775 := bstep (se 1 (by rfl) ⟨359081, by rfl⟩ : syracuseStep 478775 = 718163) B718163
theorem B478795 : Blo 475787 478795 := bstep (se 1 (by rfl) ⟨359096, by rfl⟩ : syracuseStep 478795 = 718193) B718193
theorem B478807 : Blo 475787 478807 := bstep (se 1 (by rfl) ⟨359105, by rfl⟩ : syracuseStep 478807 = 718211) B718211
theorem B1363549 : Blo 475787 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B478827 : Blo 475787 478827 := bstep (se 1 (by rfl) ⟨359120, by rfl⟩ : syracuseStep 478827 = 718241) B718241
theorem B478839 : Blo 475787 478839 := bstep (se 1 (by rfl) ⟨359129, by rfl⟩ : syracuseStep 478839 = 718259) B718259
theorem B478859 : Blo 475787 478859 := bstep (se 1 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 478859 = 718289) B718289
theorem B478871 : Blo 475787 478871 := bstep (se 1 (by rfl) ⟨359153, by rfl⟩ : syracuseStep 478871 = 718307) B718307
theorem B478891 : Blo 475787 478891 := bstep (se 1 (by rfl) ⟨359168, by rfl⟩ : syracuseStep 478891 = 718337) B718337
theorem B478903 : Blo 475787 478903 := bstep (se 1 (by rfl) ⟨359177, by rfl⟩ : syracuseStep 478903 = 718355) B718355
theorem B478923 : Blo 475787 478923 := bstep (se 1 (by rfl) ⟨359192, by rfl⟩ : syracuseStep 478923 = 718385) B718385
theorem B478935 : Blo 475787 478935 := bstep (se 1 (by rfl) ⟨359201, by rfl⟩ : syracuseStep 478935 = 718403) B718403
theorem B478955 : Blo 475787 478955 := bstep (se 1 (by rfl) ⟨359216, by rfl⟩ : syracuseStep 478955 = 718433) B718433
theorem B478967 : Blo 475787 478967 := bstep (se 1 (by rfl) ⟨359225, by rfl⟩ : syracuseStep 478967 = 718451) B718451
theorem B478987 : Blo 475787 478987 := bstep (se 1 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 478987 = 718481) B718481
theorem B478999 : Blo 475787 478999 := bstep (se 1 (by rfl) ⟨359249, by rfl⟩ : syracuseStep 478999 = 718499) B718499
theorem B479019 : Blo 475787 479019 := bstep (se 1 (by rfl) ⟨359264, by rfl⟩ : syracuseStep 479019 = 718529) B718529
theorem B479031 : Blo 475787 479031 := bstep (se 1 (by rfl) ⟨359273, by rfl⟩ : syracuseStep 479031 = 718547) B718547
theorem B479051 : Blo 475787 479051 := bstep (se 1 (by rfl) ⟨359288, by rfl⟩ : syracuseStep 479051 = 718577) B718577
theorem B479063 : Blo 475787 479063 := bstep (se 1 (by rfl) ⟨359297, by rfl⟩ : syracuseStep 479063 = 718595) B718595
theorem B479083 : Blo 475787 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B479095 : Blo 475787 479095 := bstep (se 1 (by rfl) ⟨359321, by rfl⟩ : syracuseStep 479095 = 718643) B718643
theorem B479115 : Blo 475787 479115 := bstep (se 1 (by rfl) ⟨359336, by rfl⟩ : syracuseStep 479115 = 718673) B718673
theorem B806807 : Blo 475787 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B479127 : Blo 475787 479127 := bstep (se 1 (by rfl) ⟨359345, by rfl⟩ : syracuseStep 479127 = 718691) B718691
theorem B479147 : Blo 475787 479147 := bstep (se 1 (by rfl) ⟨359360, by rfl⟩ : syracuseStep 479147 = 718721) B718721
theorem B1363891 : Blo 475787 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B479159 : Blo 475787 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B479179 : Blo 475787 479179 := bstep (se 1 (by rfl) ⟨359384, by rfl⟩ : syracuseStep 479179 = 718769) B718769
theorem B479191 : Blo 475787 479191 := bstep (se 1 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 479191 = 718787) B718787
theorem B479211 : Blo 475787 479211 := bstep (se 1 (by rfl) ⟨359408, by rfl⟩ : syracuseStep 479211 = 718817) B718817
theorem B479223 : Blo 475787 479223 := bstep (se 1 (by rfl) ⟨359417, by rfl⟩ : syracuseStep 479223 = 718835) B718835
theorem B479243 : Blo 475787 479243 := bstep (se 1 (by rfl) ⟨359432, by rfl⟩ : syracuseStep 479243 = 718865) B718865
theorem B806935 : Blo 475787 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B479255 : Blo 475787 479255 := bstep (se 1 (by rfl) ⟨359441, by rfl⟩ : syracuseStep 479255 = 718883) B718883
theorem B479275 : Blo 475787 479275 := bstep (se 1 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 479275 = 718913) B718913
theorem B479287 : Blo 475787 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B479307 : Blo 475787 479307 := bstep (se 1 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 479307 = 718961) B718961
theorem B479319 : Blo 475787 479319 := bstep (se 1 (by rfl) ⟨359489, by rfl⟩ : syracuseStep 479319 = 718979) B718979
theorem B479339 : Blo 475787 479339 := bstep (se 1 (by rfl) ⟨359504, by rfl⟩ : syracuseStep 479339 = 719009) B719009
theorem B479351 : Blo 475787 479351 := bstep (se 1 (by rfl) ⟨359513, by rfl⟩ : syracuseStep 479351 = 719027) B719027
theorem B479371 : Blo 475787 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B479383 : Blo 475787 479383 := bstep (se 1 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 479383 = 719075) B719075
theorem B479403 : Blo 475787 479403 := bstep (se 1 (by rfl) ⟨359552, by rfl⟩ : syracuseStep 479403 = 719105) B719105
theorem B479415 : Blo 475787 479415 := bstep (se 1 (by rfl) ⟨359561, by rfl⟩ : syracuseStep 479415 = 719123) B719123
theorem B479435 : Blo 475787 479435 := bstep (se 1 (by rfl) ⟨359576, by rfl⟩ : syracuseStep 479435 = 719153) B719153
theorem B479447 : Blo 475787 479447 := bstep (se 1 (by rfl) ⟨359585, by rfl⟩ : syracuseStep 479447 = 719171) B719171
theorem B479467 : Blo 475787 479467 := bstep (se 1 (by rfl) ⟨359600, by rfl⟩ : syracuseStep 479467 = 719201) B719201
theorem B545015 : Blo 475787 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B479479 : Blo 475787 479479 := bstep (se 1 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 479479 = 719219) B719219
theorem B479499 : Blo 475787 479499 := bstep (se 1 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 479499 = 719249) B719249
theorem B479511 : Blo 475787 479511 := bstep (se 1 (by rfl) ⟨359633, by rfl⟩ : syracuseStep 479511 = 719267) B719267
theorem B479531 : Blo 475787 479531 := bstep (se 1 (by rfl) ⟨359648, by rfl⟩ : syracuseStep 479531 = 719297) B719297
theorem B479543 : Blo 475787 479543 := bstep (se 1 (by rfl) ⟨359657, by rfl⟩ : syracuseStep 479543 = 719315) B719315
theorem B479563 : Blo 475787 479563 := bstep (se 1 (by rfl) ⟨359672, by rfl⟩ : syracuseStep 479563 = 719345) B719345
theorem B479575 : Blo 475787 479575 := bstep (se 1 (by rfl) ⟨359681, by rfl⟩ : syracuseStep 479575 = 719363) B719363
theorem B3887461 : Blo 475787 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B479595 : Blo 475787 479595 := bstep (se 1 (by rfl) ⟨359696, by rfl⟩ : syracuseStep 479595 = 719393) B719393
theorem B479607 : Blo 475787 479607 := bstep (se 1 (by rfl) ⟨359705, by rfl⟩ : syracuseStep 479607 = 719411) B719411
theorem B479627 : Blo 475787 479627 := bstep (se 1 (by rfl) ⟨359720, by rfl⟩ : syracuseStep 479627 = 719441) B719441
theorem B479639 : Blo 475787 479639 := bstep (se 1 (by rfl) ⟨359729, by rfl⟩ : syracuseStep 479639 = 719459) B719459
theorem B479659 : Blo 475787 479659 := bstep (se 1 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 479659 = 719489) B719489
theorem B479671 : Blo 475787 479671 := bstep (se 1 (by rfl) ⟨359753, by rfl⟩ : syracuseStep 479671 = 719507) B719507
theorem B479691 : Blo 475787 479691 := bstep (se 1 (by rfl) ⟨359768, by rfl⟩ : syracuseStep 479691 = 719537) B719537
theorem B479703 : Blo 475787 479703 := bstep (se 1 (by rfl) ⟨359777, by rfl⟩ : syracuseStep 479703 = 719555) B719555
theorem B479723 : Blo 475787 479723 := bstep (se 1 (by rfl) ⟨359792, by rfl⟩ : syracuseStep 479723 = 719585) B719585
theorem B479735 : Blo 475787 479735 := bstep (se 1 (by rfl) ⟨359801, by rfl⟩ : syracuseStep 479735 = 719603) B719603
theorem B479755 : Blo 475787 479755 := bstep (se 1 (by rfl) ⟨359816, by rfl⟩ : syracuseStep 479755 = 719633) B719633
theorem B479767 : Blo 475787 479767 := bstep (se 1 (by rfl) ⟨359825, by rfl⟩ : syracuseStep 479767 = 719651) B719651
theorem B479787 : Blo 475787 479787 := bstep (se 1 (by rfl) ⟨359840, by rfl⟩ : syracuseStep 479787 = 719681) B719681
theorem B1724993 : Blo 475787 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B905843 : Blo 475787 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B807563 : Blo 475787 807563 := bstep (se 1 (by rfl) ⟨605672, by rfl⟩ : syracuseStep 807563 = 1211345) B1211345
theorem B905995 : Blo 475787 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B807691 : Blo 475787 807691 := bstep (se 1 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 807691 = 1211537) B1211537
theorem B2577197 : Blo 475787 2577197 := bstep (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) B966449
theorem B1364825 : Blo 475787 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B807833 : Blo 475787 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B2184215 : Blo 475787 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B807961 : Blo 475787 807961 := bstep (se 2 (by rfl) ⟨302985, by rfl⟩ : syracuseStep 807961 = 605971) B605971
theorem B906329 : Blo 475787 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B611479 : Blo 475787 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B1070603 : Blo 475787 1070603 := bstep (se 1 (by rfl) ⟨802952, by rfl⟩ : syracuseStep 1070603 = 1605905) B1605905
theorem B3626531 : Blo 475787 3626531 := bstep (se 1 (by rfl) ⟨2719898, by rfl⟩ : syracuseStep 3626531 = 5439797) B5439797
theorem B1070657 : Blo 475787 1070657 := bstep (se 2 (by rfl) ⟨401496, by rfl⟩ : syracuseStep 1070657 = 802993) B802993
theorem B808535 : Blo 475787 808535 := bstep (se 1 (by rfl) ⟨606401, by rfl⟩ : syracuseStep 808535 = 1212803) B1212803
theorem B906967 : Blo 475787 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B808663 : Blo 475787 808663 := bstep (se 1 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 808663 = 1212995) B1212995
theorem B2578193 : Blo 475787 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B1070873 : Blo 475787 1070873 := bstep (se 2 (by rfl) ⟨401577, by rfl⟩ : syracuseStep 1070873 = 803155) B803155
theorem B1070963 : Blo 475787 1070963 := bstep (se 1 (by rfl) ⟨803222, by rfl⟩ : syracuseStep 1070963 = 1606445) B1606445
theorem B1070999 : Blo 475787 1070999 := bstep (se 1 (by rfl) ⟨803249, by rfl⟩ : syracuseStep 1070999 = 1606499) B1606499
theorem B645067 : Blo 475787 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B2414609 : Blo 475787 2414609 := bstep (se 2 (by rfl) ⟨905478, by rfl⟩ : syracuseStep 2414609 = 1810957) B1810957
theorem B1071179 : Blo 475787 1071179 := bstep (se 1 (by rfl) ⟨803384, by rfl⟩ : syracuseStep 1071179 = 1606769) B1606769
theorem B1071233 : Blo 475787 1071233 := bstep (se 2 (by rfl) ⟨401712, by rfl⟩ : syracuseStep 1071233 = 803425) B803425
theorem B2414771 : Blo 475787 2414771 := bstep (se 1 (by rfl) ⟨1811078, by rfl⟩ : syracuseStep 2414771 = 3622157) B3622157
theorem B1530035 : Blo 475787 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1726667 : Blo 475787 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1038539 : Blo 475787 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B1366237 : Blo 475787 1366237 := bstep (se 3 (by rfl) ⟨256169, by rfl⟩ : syracuseStep 1366237 = 512339) B512339
theorem B13031725 : Blo 475787 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B809291 : Blo 475787 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B1071449 : Blo 475787 1071449 := bstep (se 2 (by rfl) ⟨401793, by rfl⟩ : syracuseStep 1071449 = 803587) B803587
theorem B1071539 : Blo 475787 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B809419 : Blo 475787 809419 := bstep (se 1 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 809419 = 1214129) B1214129
theorem B1071575 : Blo 475787 1071575 := bstep (se 1 (by rfl) ⟨803681, by rfl⟩ : syracuseStep 1071575 = 1607363) B1607363
theorem B907787 : Blo 475787 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B907841 : Blo 475787 907841 := bstep (se 2 (by rfl) ⟨340440, by rfl⟩ : syracuseStep 907841 = 680881) B680881
theorem B809561 : Blo 475787 809561 := bstep (se 2 (by rfl) ⟨303585, by rfl⟩ : syracuseStep 809561 = 607171) B607171
theorem B1071755 : Blo 475787 1071755 := bstep (se 1 (by rfl) ⟨803816, by rfl⟩ : syracuseStep 1071755 = 1607633) B1607633
theorem B1071809 : Blo 475787 1071809 := bstep (se 2 (by rfl) ⟨401928, by rfl⟩ : syracuseStep 1071809 = 803857) B803857
theorem B645835 : Blo 475787 645835 := bstep (se 1 (by rfl) ⟨484376, by rfl⟩ : syracuseStep 645835 = 968753) B968753
theorem B777035 : Blo 475787 777035 := bstep (se 1 (by rfl) ⟨582776, by rfl⟩ : syracuseStep 777035 = 1165553) B1165553
theorem B1530713 : Blo 475787 1530713 := bstep (se 2 (by rfl) ⟨574017, by rfl⟩ : syracuseStep 1530713 = 1148035) B1148035
theorem B2907011 : Blo 475787 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B1072025 : Blo 475787 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B646105 : Blo 475787 646105 := bstep (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) B484579
theorem B1072115 : Blo 475787 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B1072151 : Blo 475787 1072151 := bstep (se 1 (by rfl) ⟨804113, by rfl⟩ : syracuseStep 1072151 = 1608227) B1608227
theorem B1072331 : Blo 475787 1072331 := bstep (se 1 (by rfl) ⟨804248, by rfl⟩ : syracuseStep 1072331 = 1608497) B1608497
theorem B1072385 : Blo 475787 1072385 := bstep (se 2 (by rfl) ⟨402144, by rfl⟩ : syracuseStep 1072385 = 804289) B804289
theorem B1400129 : Blo 475787 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B908759 : Blo 475787 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B1072601 : Blo 475787 1072601 := bstep (se 2 (by rfl) ⟨402225, by rfl⟩ : syracuseStep 1072601 = 804451) B804451
theorem B1072691 : Blo 475787 1072691 := bstep (se 1 (by rfl) ⟨804518, by rfl⟩ : syracuseStep 1072691 = 1609037) B1609037
theorem B1072727 : Blo 475787 1072727 := bstep (se 1 (by rfl) ⟨804545, by rfl⟩ : syracuseStep 1072727 = 1609091) B1609091
theorem B4349533 : Blo 475787 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B1072907 : Blo 475787 1072907 := bstep (se 1 (by rfl) ⟨804680, by rfl⟩ : syracuseStep 1072907 = 1609361) B1609361
theorem B1072961 : Blo 475787 1072961 := bstep (se 2 (by rfl) ⟨402360, by rfl⟩ : syracuseStep 1072961 = 804721) B804721
theorem B909299 : Blo 475787 909299 := bstep (se 1 (by rfl) ⟨681974, by rfl⟩ : syracuseStep 909299 = 1363949) B1363949
theorem B1073177 : Blo 475787 1073177 := bstep (se 2 (by rfl) ⟨402441, by rfl⟩ : syracuseStep 1073177 = 804883) B804883
theorem B2416715 : Blo 475787 2416715 := bstep (se 1 (by rfl) ⟨1812536, by rfl⟩ : syracuseStep 2416715 = 3625073) B3625073
theorem B1073267 : Blo 475787 1073267 := bstep (se 1 (by rfl) ⟨804950, by rfl⟩ : syracuseStep 1073267 = 1609901) B1609901
theorem B1073303 : Blo 475787 1073303 := bstep (se 1 (by rfl) ⟨804977, by rfl⟩ : syracuseStep 1073303 = 1609955) B1609955
theorem B680089 : Blo 475787 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B1073483 : Blo 475787 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B1073537 : Blo 475787 1073537 := bstep (se 2 (by rfl) ⟨402576, by rfl⟩ : syracuseStep 1073537 = 805153) B805153
theorem B1532353 : Blo 475787 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B909785 : Blo 475787 909785 := bstep (se 2 (by rfl) ⟨341169, by rfl⟩ : syracuseStep 909785 = 682339) B682339
theorem B1073753 : Blo 475787 1073753 := bstep (se 2 (by rfl) ⟨402657, by rfl⟩ : syracuseStep 1073753 = 805315) B805315
theorem B1204915 : Blo 475787 1204915 := bstep (se 1 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 1204915 = 1807373) B1807373
theorem B1073843 : Blo 475787 1073843 := bstep (se 1 (by rfl) ⟨805382, by rfl⟩ : syracuseStep 1073843 = 1610765) B1610765
theorem B1532609 : Blo 475787 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B1073879 : Blo 475787 1073879 := bstep (se 1 (by rfl) ⟨805409, by rfl⟩ : syracuseStep 1073879 = 1610819) B1610819
theorem B1205057 : Blo 475787 1205057 := bstep (se 2 (by rfl) ⟨451896, by rfl⟩ : syracuseStep 1205057 = 903793) B903793
theorem B2909029 : Blo 475787 2909029 := bstep (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) B545443
theorem B1074059 : Blo 475787 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B1074113 : Blo 475787 1074113 := bstep (se 2 (by rfl) ⟨402792, by rfl⟩ : syracuseStep 1074113 = 805585) B805585
theorem B713687 : Blo 475787 713687 := bstep (se 1 (by rfl) ⟨535265, by rfl⟩ : syracuseStep 713687 = 1070531) B1070531
theorem B2515985 : Blo 475787 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B713753 : Blo 475787 713753 := bstep (se 2 (by rfl) ⟨267657, by rfl⟩ : syracuseStep 713753 = 535315) B535315
theorem B943193 : Blo 475787 943193 := bstep (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) B707395
theorem B713867 : Blo 475787 713867 := bstep (se 1 (by rfl) ⟨535400, by rfl⟩ : syracuseStep 713867 = 1070801) B1070801
theorem B713879 : Blo 475787 713879 := bstep (se 1 (by rfl) ⟨535409, by rfl⟩ : syracuseStep 713879 = 1070819) B1070819
theorem B648343 : Blo 475787 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B1074329 : Blo 475787 1074329 := bstep (se 2 (by rfl) ⟨402873, by rfl⟩ : syracuseStep 1074329 = 805747) B805747
theorem B713945 : Blo 475787 713945 := bstep (se 2 (by rfl) ⟨267729, by rfl⟩ : syracuseStep 713945 = 535459) B535459
theorem B1074419 : Blo 475787 1074419 := bstep (se 1 (by rfl) ⟨805814, by rfl⟩ : syracuseStep 1074419 = 1611629) B1611629
theorem B1074455 : Blo 475787 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B714059 : Blo 475787 714059 := bstep (se 1 (by rfl) ⟨535544, by rfl⟩ : syracuseStep 714059 = 1071089) B1071089
theorem B714071 : Blo 475787 714071 := bstep (se 1 (by rfl) ⟨535553, by rfl⟩ : syracuseStep 714071 = 1071107) B1071107
theorem B714137 : Blo 475787 714137 := bstep (se 2 (by rfl) ⟨267801, by rfl⟩ : syracuseStep 714137 = 535603) B535603
theorem B1074635 : Blo 475787 1074635 := bstep (se 1 (by rfl) ⟨805976, by rfl⟩ : syracuseStep 1074635 = 1611953) B1611953
theorem B1074689 : Blo 475787 1074689 := bstep (se 2 (by rfl) ⟨403008, by rfl⟩ : syracuseStep 1074689 = 806017) B806017
theorem B714251 : Blo 475787 714251 := bstep (se 1 (by rfl) ⟨535688, by rfl⟩ : syracuseStep 714251 = 1071377) B1071377
theorem B714263 : Blo 475787 714263 := bstep (se 1 (by rfl) ⟨535697, by rfl⟩ : syracuseStep 714263 = 1071395) B1071395
theorem B681547 : Blo 475787 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B714329 : Blo 475787 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B714443 : Blo 475787 714443 := bstep (se 1 (by rfl) ⟨535832, by rfl⟩ : syracuseStep 714443 = 1071665) B1071665
theorem B714455 : Blo 475787 714455 := bstep (se 1 (by rfl) ⟨535841, by rfl⟩ : syracuseStep 714455 = 1071683) B1071683
theorem B1074905 : Blo 475787 1074905 := bstep (se 2 (by rfl) ⟨403089, by rfl⟩ : syracuseStep 1074905 = 806179) B806179
theorem B714521 : Blo 475787 714521 := bstep (se 2 (by rfl) ⟨267945, by rfl⟩ : syracuseStep 714521 = 535891) B535891
theorem B1074995 : Blo 475787 1074995 := bstep (se 1 (by rfl) ⟨806246, by rfl⟩ : syracuseStep 1074995 = 1612493) B1612493
theorem B2418497 : Blo 475787 2418497 := bstep (se 2 (by rfl) ⟨906936, by rfl⟩ : syracuseStep 2418497 = 1813873) B1813873
theorem B1075031 : Blo 475787 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B714635 : Blo 475787 714635 := bstep (se 1 (by rfl) ⟨535976, by rfl⟩ : syracuseStep 714635 = 1071953) B1071953
theorem B714647 : Blo 475787 714647 := bstep (se 1 (by rfl) ⟨535985, by rfl⟩ : syracuseStep 714647 = 1071971) B1071971
theorem B714713 : Blo 475787 714713 := bstep (se 2 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 714713 = 536035) B536035
theorem B1075211 : Blo 475787 1075211 := bstep (se 1 (by rfl) ⟨806408, by rfl⟩ : syracuseStep 1075211 = 1612817) B1612817
theorem B1206323 : Blo 475787 1206323 := bstep (se 1 (by rfl) ⟨904742, by rfl⟩ : syracuseStep 1206323 = 1809485) B1809485
theorem B1075265 : Blo 475787 1075265 := bstep (se 2 (by rfl) ⟨403224, by rfl⟩ : syracuseStep 1075265 = 806449) B806449
theorem B714827 : Blo 475787 714827 := bstep (se 1 (by rfl) ⟨536120, by rfl⟩ : syracuseStep 714827 = 1072241) B1072241
theorem B714839 : Blo 475787 714839 := bstep (se 1 (by rfl) ⟨536129, by rfl⟩ : syracuseStep 714839 = 1072259) B1072259
theorem B714905 : Blo 475787 714905 := bstep (se 2 (by rfl) ⟨268089, by rfl⟩ : syracuseStep 714905 = 536179) B536179
theorem B12216581 : Blo 475787 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B715019 : Blo 475787 715019 := bstep (se 1 (by rfl) ⟨536264, by rfl⟩ : syracuseStep 715019 = 1072529) B1072529
theorem B715031 : Blo 475787 715031 := bstep (se 1 (by rfl) ⟨536273, by rfl⟩ : syracuseStep 715031 = 1072547) B1072547
theorem B1075481 : Blo 475787 1075481 := bstep (se 2 (by rfl) ⟨403305, by rfl⟩ : syracuseStep 1075481 = 806611) B806611
theorem B2713931 : Blo 475787 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B715097 : Blo 475787 715097 := bstep (se 2 (by rfl) ⟨268161, by rfl⟩ : syracuseStep 715097 = 536323) B536323
theorem B1075571 : Blo 475787 1075571 := bstep (se 1 (by rfl) ⟨806678, by rfl⟩ : syracuseStep 1075571 = 1613357) B1613357
theorem B1075607 : Blo 475787 1075607 := bstep (se 1 (by rfl) ⟨806705, by rfl⟩ : syracuseStep 1075607 = 1613411) B1613411
theorem B715211 : Blo 475787 715211 := bstep (se 1 (by rfl) ⟨536408, by rfl⟩ : syracuseStep 715211 = 1072817) B1072817
theorem B715223 : Blo 475787 715223 := bstep (se 1 (by rfl) ⟨536417, by rfl⟩ : syracuseStep 715223 = 1072835) B1072835
theorem B715289 : Blo 475787 715289 := bstep (se 2 (by rfl) ⟨268233, by rfl⟩ : syracuseStep 715289 = 536467) B536467
theorem B1206859 : Blo 475787 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B1075787 : Blo 475787 1075787 := bstep (se 1 (by rfl) ⟨806840, by rfl⟩ : syracuseStep 1075787 = 1613681) B1613681
theorem B1075841 : Blo 475787 1075841 := bstep (se 2 (by rfl) ⟨403440, by rfl⟩ : syracuseStep 1075841 = 806881) B806881
theorem B715403 : Blo 475787 715403 := bstep (se 1 (by rfl) ⟨536552, by rfl⟩ : syracuseStep 715403 = 1073105) B1073105
theorem B715415 : Blo 475787 715415 := bstep (se 1 (by rfl) ⟨536561, by rfl⟩ : syracuseStep 715415 = 1073123) B1073123
theorem B5171863 : Blo 475787 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B486059 : Blo 475787 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B1305305 : Blo 475787 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B1207001 : Blo 475787 1207001 := bstep (se 2 (by rfl) ⟨452625, by rfl⟩ : syracuseStep 1207001 = 905251) B905251
theorem B715481 : Blo 475787 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B3631877 : Blo 475787 3631877 := bstep (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) B680977
theorem B682777 : Blo 475787 682777 := bstep (se 2 (by rfl) ⟨256041, by rfl⟩ : syracuseStep 682777 = 512083) B512083
theorem B715595 : Blo 475787 715595 := bstep (se 1 (by rfl) ⟨536696, by rfl⟩ : syracuseStep 715595 = 1073393) B1073393
theorem B715607 : Blo 475787 715607 := bstep (se 1 (by rfl) ⟨536705, by rfl⟩ : syracuseStep 715607 = 1073411) B1073411
theorem B1076057 : Blo 475787 1076057 := bstep (se 2 (by rfl) ⟨403521, by rfl⟩ : syracuseStep 1076057 = 807043) B807043
theorem B715673 : Blo 475787 715673 := bstep (se 2 (by rfl) ⟨268377, by rfl⟩ : syracuseStep 715673 = 536755) B536755
theorem B1076147 : Blo 475787 1076147 := bstep (se 1 (by rfl) ⟨807110, by rfl⟩ : syracuseStep 1076147 = 1614221) B1614221
theorem B1076183 : Blo 475787 1076183 := bstep (se 1 (by rfl) ⟨807137, by rfl⟩ : syracuseStep 1076183 = 1614275) B1614275
theorem B715787 : Blo 475787 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B715799 : Blo 475787 715799 := bstep (se 1 (by rfl) ⟨536849, by rfl⟩ : syracuseStep 715799 = 1073699) B1073699
theorem B715865 : Blo 475787 715865 := bstep (se 2 (by rfl) ⟨268449, by rfl⟩ : syracuseStep 715865 = 536899) B536899
theorem B1535069 : Blo 475787 1535069 := bstep (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) B575651
theorem B1076363 : Blo 475787 1076363 := bstep (se 1 (by rfl) ⟨807272, by rfl⟩ : syracuseStep 1076363 = 1614545) B1614545
theorem B4091057 : Blo 475787 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B1076417 : Blo 475787 1076417 := bstep (se 2 (by rfl) ⟨403656, by rfl⟩ : syracuseStep 1076417 = 807313) B807313
theorem B715979 : Blo 475787 715979 := bstep (se 1 (by rfl) ⟨536984, by rfl⟩ : syracuseStep 715979 = 1073969) B1073969
theorem B715991 : Blo 475787 715991 := bstep (se 1 (by rfl) ⟨536993, by rfl⟩ : syracuseStep 715991 = 1073987) B1073987
theorem B716057 : Blo 475787 716057 := bstep (se 2 (by rfl) ⟨268521, by rfl⟩ : syracuseStep 716057 = 537043) B537043
theorem B4582757 : Blo 475787 4582757 := bstep (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) B859267
theorem B716171 : Blo 475787 716171 := bstep (se 1 (by rfl) ⟨537128, by rfl⟩ : syracuseStep 716171 = 1074257) B1074257
theorem B716183 : Blo 475787 716183 := bstep (se 1 (by rfl) ⟨537137, by rfl⟩ : syracuseStep 716183 = 1074275) B1074275
theorem B1076633 : Blo 475787 1076633 := bstep (se 2 (by rfl) ⟨403737, by rfl⟩ : syracuseStep 1076633 = 807475) B807475
theorem B716249 : Blo 475787 716249 := bstep (se 2 (by rfl) ⟨268593, by rfl⟩ : syracuseStep 716249 = 537187) B537187
theorem B1076723 : Blo 475787 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1207831 : Blo 475787 1207831 := bstep (se 1 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 1207831 = 1811747) B1811747
theorem B1076759 : Blo 475787 1076759 := bstep (se 1 (by rfl) ⟨807569, by rfl⟩ : syracuseStep 1076759 = 1615139) B1615139
theorem B716363 : Blo 475787 716363 := bstep (se 1 (by rfl) ⟨537272, by rfl⟩ : syracuseStep 716363 = 1074545) B1074545
theorem B716375 : Blo 475787 716375 := bstep (se 1 (by rfl) ⟨537281, by rfl⟩ : syracuseStep 716375 = 1074563) B1074563
theorem B716441 : Blo 475787 716441 := bstep (se 2 (by rfl) ⟨268665, by rfl⟩ : syracuseStep 716441 = 537331) B537331
theorem B1076939 : Blo 475787 1076939 := bstep (se 1 (by rfl) ⟨807704, by rfl⟩ : syracuseStep 1076939 = 1615409) B1615409
theorem B2420441 : Blo 475787 2420441 := bstep (se 2 (by rfl) ⟨907665, by rfl⟩ : syracuseStep 2420441 = 1815331) B1815331
theorem B1076993 : Blo 475787 1076993 := bstep (se 2 (by rfl) ⟨403872, by rfl⟩ : syracuseStep 1076993 = 807745) B807745
theorem B716555 : Blo 475787 716555 := bstep (se 1 (by rfl) ⟨537416, by rfl⟩ : syracuseStep 716555 = 1074833) B1074833
theorem B716567 : Blo 475787 716567 := bstep (se 1 (by rfl) ⟨537425, by rfl⟩ : syracuseStep 716567 = 1074851) B1074851
theorem B716633 : Blo 475787 716633 := bstep (se 2 (by rfl) ⟨268737, by rfl⟩ : syracuseStep 716633 = 537475) B537475
theorem B3108701 : Blo 475787 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B4091741 : Blo 475787 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B1208267 : Blo 475787 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B716747 : Blo 475787 716747 := bstep (se 1 (by rfl) ⟨537560, by rfl⟩ : syracuseStep 716747 = 1075121) B1075121
theorem B716759 : Blo 475787 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B1077209 : Blo 475787 1077209 := bstep (se 2 (by rfl) ⟨403953, by rfl⟩ : syracuseStep 1077209 = 807907) B807907
theorem B716825 : Blo 475787 716825 := bstep (se 2 (by rfl) ⟨268809, by rfl⟩ : syracuseStep 716825 = 537619) B537619
theorem B1077299 : Blo 475787 1077299 := bstep (se 1 (by rfl) ⟨807974, by rfl⟩ : syracuseStep 1077299 = 1615949) B1615949
theorem B1077335 : Blo 475787 1077335 := bstep (se 1 (by rfl) ⟨808001, by rfl⟩ : syracuseStep 1077335 = 1616003) B1616003
theorem B716939 : Blo 475787 716939 := bstep (se 1 (by rfl) ⟨537704, by rfl⟩ : syracuseStep 716939 = 1075409) B1075409
theorem B716951 : Blo 475787 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B815321 : Blo 475787 815321 := bstep (se 2 (by rfl) ⟨305745, by rfl⟩ : syracuseStep 815321 = 611491) B611491
theorem B717017 : Blo 475787 717017 := bstep (se 2 (by rfl) ⟨268881, by rfl⟩ : syracuseStep 717017 = 537763) B537763
theorem B1077515 : Blo 475787 1077515 := bstep (se 1 (by rfl) ⟨808136, by rfl⟩ : syracuseStep 1077515 = 1616273) B1616273
theorem B1208641 : Blo 475787 1208641 := bstep (se 2 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 1208641 = 906481) B906481
theorem B1077569 : Blo 475787 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B2289995 : Blo 475787 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B717131 : Blo 475787 717131 := bstep (se 1 (by rfl) ⟨537848, by rfl⟩ : syracuseStep 717131 = 1075697) B1075697
theorem B717143 : Blo 475787 717143 := bstep (se 1 (by rfl) ⟨537857, by rfl⟩ : syracuseStep 717143 = 1075715) B1075715
theorem B717209 : Blo 475787 717209 := bstep (se 2 (by rfl) ⟨268953, by rfl⟩ : syracuseStep 717209 = 537907) B537907
theorem B717323 : Blo 475787 717323 := bstep (se 1 (by rfl) ⟨537992, by rfl⟩ : syracuseStep 717323 = 1075985) B1075985
theorem B717335 : Blo 475787 717335 := bstep (se 1 (by rfl) ⟨538001, by rfl⟩ : syracuseStep 717335 = 1076003) B1076003
theorem B1077785 : Blo 475787 1077785 := bstep (se 2 (by rfl) ⟨404169, by rfl⟩ : syracuseStep 1077785 = 808339) B808339
theorem B717401 : Blo 475787 717401 := bstep (se 2 (by rfl) ⟨269025, by rfl⟩ : syracuseStep 717401 = 538051) B538051
theorem B1077875 : Blo 475787 1077875 := bstep (se 1 (by rfl) ⟨808406, by rfl⟩ : syracuseStep 1077875 = 1616813) B1616813
theorem B2585239 : Blo 475787 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B1077911 : Blo 475787 1077911 := bstep (se 1 (by rfl) ⟨808433, by rfl⟩ : syracuseStep 1077911 = 1616867) B1616867
theorem B717515 : Blo 475787 717515 := bstep (se 1 (by rfl) ⟨538136, by rfl⟩ : syracuseStep 717515 = 1076273) B1076273
theorem B717527 : Blo 475787 717527 := bstep (se 1 (by rfl) ⟨538145, by rfl⟩ : syracuseStep 717527 = 1076291) B1076291
theorem B717593 : Blo 475787 717593 := bstep (se 2 (by rfl) ⟨269097, by rfl⟩ : syracuseStep 717593 = 538195) B538195
theorem B1307443 : Blo 475787 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1078091 : Blo 475787 1078091 := bstep (se 1 (by rfl) ⟨808568, by rfl⟩ : syracuseStep 1078091 = 1617137) B1617137
theorem B1078145 : Blo 475787 1078145 := bstep (se 2 (by rfl) ⟨404304, by rfl⟩ : syracuseStep 1078145 = 808609) B808609
theorem B717707 : Blo 475787 717707 := bstep (se 1 (by rfl) ⟨538280, by rfl⟩ : syracuseStep 717707 = 1076561) B1076561
theorem B1209239 : Blo 475787 1209239 := bstep (se 1 (by rfl) ⟨906929, by rfl⟩ : syracuseStep 1209239 = 1813859) B1813859
theorem B717719 : Blo 475787 717719 := bstep (se 1 (by rfl) ⟨538289, by rfl⟩ : syracuseStep 717719 = 1076579) B1076579
theorem B652235 : Blo 475787 652235 := bstep (se 1 (by rfl) ⟨489176, by rfl⟩ : syracuseStep 652235 = 978353) B978353
theorem B717785 : Blo 475787 717785 := bstep (se 2 (by rfl) ⟨269169, by rfl⟩ : syracuseStep 717785 = 538339) B538339
theorem B717899 : Blo 475787 717899 := bstep (se 1 (by rfl) ⟨538424, by rfl⟩ : syracuseStep 717899 = 1076849) B1076849
theorem B717911 : Blo 475787 717911 := bstep (se 1 (by rfl) ⟨538433, by rfl⟩ : syracuseStep 717911 = 1076867) B1076867
theorem B1078361 : Blo 475787 1078361 := bstep (se 2 (by rfl) ⟨404385, by rfl⟩ : syracuseStep 1078361 = 808771) B808771
theorem B3634307 : Blo 475787 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B717977 : Blo 475787 717977 := bstep (se 2 (by rfl) ⟨269241, by rfl⟩ : syracuseStep 717977 = 538483) B538483
theorem B1078451 : Blo 475787 1078451 := bstep (se 1 (by rfl) ⟨808838, by rfl⟩ : syracuseStep 1078451 = 1617677) B1617677
theorem B1078487 : Blo 475787 1078487 := bstep (se 1 (by rfl) ⟨808865, by rfl⟩ : syracuseStep 1078487 = 1617731) B1617731
theorem B1930499 : Blo 475787 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B718091 : Blo 475787 718091 := bstep (se 1 (by rfl) ⟨538568, by rfl⟩ : syracuseStep 718091 = 1077137) B1077137
theorem B718103 : Blo 475787 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B2422061 : Blo 475787 2422061 := bstep (se 3 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 2422061 = 908273) B908273
theorem B1045811 : Blo 475787 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B718169 : Blo 475787 718169 := bstep (se 2 (by rfl) ⟨269313, by rfl⟩ : syracuseStep 718169 = 538627) B538627
theorem B1078667 : Blo 475787 1078667 := bstep (se 1 (by rfl) ⟨809000, by rfl⟩ : syracuseStep 1078667 = 1618001) B1618001
theorem B1078721 : Blo 475787 1078721 := bstep (se 2 (by rfl) ⟨404520, by rfl⟩ : syracuseStep 1078721 = 809041) B809041
theorem B718283 : Blo 475787 718283 := bstep (se 1 (by rfl) ⟨538712, by rfl⟩ : syracuseStep 718283 = 1077425) B1077425
theorem B718295 : Blo 475787 718295 := bstep (se 1 (by rfl) ⟨538721, by rfl⟩ : syracuseStep 718295 = 1077443) B1077443
theorem B718361 : Blo 475787 718361 := bstep (se 2 (by rfl) ⟨269385, by rfl⟩ : syracuseStep 718361 = 538771) B538771
theorem B718475 : Blo 475787 718475 := bstep (se 1 (by rfl) ⟨538856, by rfl⟩ : syracuseStep 718475 = 1077713) B1077713
theorem B718487 : Blo 475787 718487 := bstep (se 1 (by rfl) ⟨538865, by rfl⟩ : syracuseStep 718487 = 1077731) B1077731
theorem B1078937 : Blo 475787 1078937 := bstep (se 2 (by rfl) ⟨404601, by rfl⟩ : syracuseStep 1078937 = 809203) B809203
theorem B1210049 : Blo 475787 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B718553 : Blo 475787 718553 := bstep (se 2 (by rfl) ⟨269457, by rfl⟩ : syracuseStep 718553 = 538915) B538915
theorem B1079027 : Blo 475787 1079027 := bstep (se 1 (by rfl) ⟨809270, by rfl⟩ : syracuseStep 1079027 = 1618541) B1618541
theorem B1079063 : Blo 475787 1079063 := bstep (se 1 (by rfl) ⟨809297, by rfl⟩ : syracuseStep 1079063 = 1618595) B1618595
theorem B718667 : Blo 475787 718667 := bstep (se 1 (by rfl) ⟨539000, by rfl⟩ : syracuseStep 718667 = 1078001) B1078001
theorem B718679 : Blo 475787 718679 := bstep (se 1 (by rfl) ⟨539009, by rfl⟩ : syracuseStep 718679 = 1078019) B1078019
theorem B718745 : Blo 475787 718745 := bstep (se 2 (by rfl) ⟨269529, by rfl⟩ : syracuseStep 718745 = 539059) B539059
theorem B1079243 : Blo 475787 1079243 := bstep (se 1 (by rfl) ⟨809432, by rfl⟩ : syracuseStep 1079243 = 1618865) B1618865
theorem B1079297 : Blo 475787 1079297 := bstep (se 2 (by rfl) ⟨404736, by rfl⟩ : syracuseStep 1079297 = 809473) B809473
theorem B718859 : Blo 475787 718859 := bstep (se 1 (by rfl) ⟨539144, by rfl⟩ : syracuseStep 718859 = 1078289) B1078289
theorem B718871 : Blo 475787 718871 := bstep (se 1 (by rfl) ⟨539153, by rfl⟩ : syracuseStep 718871 = 1078307) B1078307
theorem B718937 : Blo 475787 718937 := bstep (se 2 (by rfl) ⟨269601, by rfl⟩ : syracuseStep 718937 = 539203) B539203
theorem B719051 : Blo 475787 719051 := bstep (se 1 (by rfl) ⟨539288, by rfl⟩ : syracuseStep 719051 = 1078577) B1078577
theorem B719063 : Blo 475787 719063 := bstep (se 1 (by rfl) ⟨539297, by rfl⟩ : syracuseStep 719063 = 1078595) B1078595
theorem B1210585 : Blo 475787 1210585 := bstep (se 2 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 1210585 = 907939) B907939
theorem B1079513 : Blo 475787 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B719129 : Blo 475787 719129 := bstep (se 2 (by rfl) ⟨269673, by rfl⟩ : syracuseStep 719129 = 539347) B539347
theorem B719243 : Blo 475787 719243 := bstep (se 1 (by rfl) ⟨539432, by rfl⟩ : syracuseStep 719243 = 1078865) B1078865
theorem B719255 : Blo 475787 719255 := bstep (se 1 (by rfl) ⟨539441, by rfl⟩ : syracuseStep 719255 = 1078883) B1078883
theorem B1145267 : Blo 475787 1145267 := bstep (se 1 (by rfl) ⟨858950, by rfl⟩ : syracuseStep 1145267 = 1717901) B1717901
theorem B719321 : Blo 475787 719321 := bstep (se 2 (by rfl) ⟨269745, by rfl⟩ : syracuseStep 719321 = 539491) B539491
theorem B1931779 : Blo 475787 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B719435 : Blo 475787 719435 := bstep (se 1 (by rfl) ⟨539576, by rfl⟩ : syracuseStep 719435 = 1079153) B1079153
theorem B719447 : Blo 475787 719447 := bstep (se 1 (by rfl) ⟨539585, by rfl⟩ : syracuseStep 719447 = 1079171) B1079171
theorem B883289 : Blo 475787 883289 := bstep (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) B662467
theorem B1637015 : Blo 475787 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B719513 : Blo 475787 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B719627 : Blo 475787 719627 := bstep (se 1 (by rfl) ⟨539720, by rfl⟩ : syracuseStep 719627 = 1079441) B1079441
theorem B3668753 : Blo 475787 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B719639 : Blo 475787 719639 := bstep (se 1 (by rfl) ⟨539729, by rfl⟩ : syracuseStep 719639 = 1079459) B1079459
theorem B1211699 : Blo 475787 1211699 := bstep (se 1 (by rfl) ⟨908774, by rfl⟩ : syracuseStep 1211699 = 1817549) B1817549
theorem B1146305 : Blo 475787 1146305 := bstep (se 2 (by rfl) ⟨429864, by rfl⟩ : syracuseStep 1146305 = 859729) B859729
theorem B1211993 : Blo 475787 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B2293379 : Blo 475787 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B3112921 : Blo 475787 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B2293879 : Blo 475787 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B23298293 : Blo 475787 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2425139 : Blo 475787 2425139 := bstep (se 1 (by rfl) ⟨1818854, by rfl⟩ : syracuseStep 2425139 = 3637709) B3637709
theorem B819575 : Blo 475787 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B1213015 : Blo 475787 1213015 := bstep (se 1 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 1213015 = 1819523) B1819523
theorem B2425463 : Blo 475787 2425463 := bstep (se 1 (by rfl) ⟨1819097, by rfl⟩ : syracuseStep 2425463 = 3638195) B3638195
theorem B3670721 : Blo 475787 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1213319 : Blo 475787 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B1606553 : Blo 475787 1606553 := bstep (se 2 (by rfl) ⟨602457, by rfl⟩ : syracuseStep 1606553 = 1204915) B1204915
theorem B3277835 : Blo 475787 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B1213451 : Blo 475787 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B1017289 : Blo 475787 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B1213967 : Blo 475787 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B5506627 : Blo 475787 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B2426435 : Blo 475787 2426435 := bstep (se 1 (by rfl) ⟨1819826, by rfl⟩ : syracuseStep 2426435 = 3639653) B3639653
theorem B1607255 : Blo 475787 1607255 := bstep (se 1 (by rfl) ⟨1205441, by rfl⟩ : syracuseStep 1607255 = 2410883) B2410883
theorem B1476215 : Blo 475787 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B1214099 : Blo 475787 1214099 := bstep (se 1 (by rfl) ⟨910574, by rfl⟩ : syracuseStep 1214099 = 1821149) B1821149
theorem B2426759 : Blo 475787 2426759 := bstep (se 1 (by rfl) ⟨1820069, by rfl⟩ : syracuseStep 2426759 = 3640139) B3640139
theorem B2721721 : Blo 475787 2721721 := bstep (se 2 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 2721721 = 2041291) B2041291
theorem B1607741 : Blo 475787 1607741 := bstep (se 3 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 1607741 = 602903) B602903
theorem B1739293 : Blo 475787 1739293 := bstep (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) B652235
theorem B1149995 : Blo 475787 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B2297069 : Blo 475787 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B1609145 : Blo 475787 1609145 := bstep (se 2 (by rfl) ⟨603429, by rfl⟩ : syracuseStep 1609145 = 1206859) B1206859
theorem B2788829 : Blo 475787 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B1609739 : Blo 475787 1609739 := bstep (se 1 (by rfl) ⟨1207304, by rfl⟩ : syracuseStep 1609739 = 2414609) B2414609
theorem B1609847 : Blo 475787 1609847 := bstep (se 1 (by rfl) ⟨1207385, by rfl⟩ : syracuseStep 1609847 = 2414771) B2414771
theorem B1020023 : Blo 475787 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B1151111 : Blo 475787 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B2298127 : Blo 475787 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 475787 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2298145 : Blo 475787 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B1020475 : Blo 475787 1020475 := bstep (se 1 (by rfl) ⟨765356, by rfl⟩ : syracuseStep 1020475 = 1530713) B1530713
theorem B1938007 : Blo 475787 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B8131265 : Blo 475787 8131265 := bstep (se 2 (by rfl) ⟨3049224, by rfl⟩ : syracuseStep 8131265 = 6098449) B6098449
theorem B1610441 : Blo 475787 1610441 := bstep (se 2 (by rfl) ⟨603915, by rfl⟩ : syracuseStep 1610441 = 1207831) B1207831
theorem B9966341 : Blo 475787 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2036765 : Blo 475787 2036765 := bstep (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) B763787
theorem B3642569 : Blo 475787 3642569 := bstep (se 2 (by rfl) ⟨1365963, by rfl⟩ : syracuseStep 3642569 = 2731927) B2731927
theorem B1611143 : Blo 475787 1611143 := bstep (se 1 (by rfl) ⟨1208357, by rfl⟩ : syracuseStep 1611143 = 2416715) B2416715
theorem B2299357 : Blo 475787 2299357 := bstep (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) B862259
theorem B1611521 : Blo 475787 1611521 := bstep (se 2 (by rfl) ⟨604320, by rfl⟩ : syracuseStep 1611521 = 1208641) B1208641
theorem B1021739 : Blo 475787 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B5183281 : Blo 475787 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B1677323 : Blo 475787 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B1743257 : Blo 475787 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B1612331 : Blo 475787 1612331 := bstep (se 1 (by rfl) ⟨1209248, by rfl⟩ : syracuseStep 1612331 = 2418497) B2418497
theorem B1809287 : Blo 475787 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B727951 : Blo 475787 727951 := bstep (se 1 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 727951 = 1091927) B1091927
theorem B4365373 : Blo 475787 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B2727371 : Blo 475787 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B4660739 : Blo 475787 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B3055171 : Blo 475787 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B2039363 : Blo 475787 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B1384235 : Blo 475787 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B1613627 : Blo 475787 1613627 := bstep (se 1 (by rfl) ⟨1210220, by rfl⟩ : syracuseStep 1613627 = 2420441) B2420441
theorem B2039687 : Blo 475787 2039687 := bstep (se 1 (by rfl) ⟨1529765, by rfl⟩ : syracuseStep 2039687 = 3059531) B3059531
theorem B1843091 : Blo 475787 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B2727827 : Blo 475787 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B10297367 : Blo 475787 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B1614113 : Blo 475787 1614113 := bstep (se 2 (by rfl) ⟨605292, by rfl⟩ : syracuseStep 1614113 = 1210585) B1210585
theorem B729479 : Blo 475787 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B17375633 : Blo 475787 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B5186051 : Blo 475787 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B1450649 : Blo 475787 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B1286999 : Blo 475787 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B1614707 : Blo 475787 1614707 := bstep (se 1 (by rfl) ⟨1211030, by rfl⟩ : syracuseStep 1614707 = 2422061) B2422061
theorem B861113 : Blo 475787 861113 := bstep (se 2 (by rfl) ⟨322917, by rfl⟩ : syracuseStep 861113 = 645835) B645835
theorem B861473 : Blo 475787 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B1287713 : Blo 475787 1287713 := bstep (se 2 (by rfl) ⟨482892, by rfl⟩ : syracuseStep 1287713 = 965785) B965785
theorem B22029893 : Blo 475787 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B763511 : Blo 475787 763511 := bstep (se 1 (by rfl) ⟨572633, by rfl⟩ : syracuseStep 763511 = 1145267) B1145267
theorem B2041463 : Blo 475787 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B4597519 : Blo 475787 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B4990871 : Blo 475787 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B764203 : Blo 475787 764203 := bstep (se 1 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 764203 = 1146305) B1146305
theorem B1681817 : Blo 475787 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1943993 : Blo 475787 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B1452545 : Blo 475787 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B12462659 : Blo 475787 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B1321559 : Blo 475787 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B2763571 : Blo 475787 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B2894777 : Blo 475787 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B535567 : Blo 475787 535567 := bstep (se 1 (by rfl) ⟨401675, by rfl⟩ : syracuseStep 535567 = 803351) B803351
theorem B2043137 : Blo 475787 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B1453373 : Blo 475787 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B1355143 : Blo 475787 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B1617299 : Blo 475787 1617299 := bstep (se 1 (by rfl) ⟨1212974, by rfl⟩ : syracuseStep 1617299 = 2425949) B2425949
theorem B536071 : Blo 475787 536071 := bstep (se 1 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 536071 = 804107) B804107
theorem B863759 : Blo 475787 863759 := bstep (se 1 (by rfl) ⟨647819, by rfl⟩ : syracuseStep 863759 = 1295639) B1295639
theorem B1355417 : Blo 475787 1355417 := bstep (se 2 (by rfl) ⟨508281, by rfl⟩ : syracuseStep 1355417 = 1016563) B1016563
theorem B536251 : Blo 475787 536251 := bstep (se 1 (by rfl) ⟨402188, by rfl⟩ : syracuseStep 536251 = 804377) B804377
theorem B9678565 : Blo 475787 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B3878705 : Blo 475787 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B3321917 : Blo 475787 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B602255 : Blo 475787 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B536719 : Blo 475787 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B1716689 : Blo 475787 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B766523 : Blo 475787 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B537223 : Blo 475787 537223 := bstep (se 1 (by rfl) ⟨402917, by rfl⟩ : syracuseStep 537223 = 805835) B805835
theorem B1618703 : Blo 475787 1618703 := bstep (se 1 (by rfl) ⟨1214027, by rfl⟩ : syracuseStep 1618703 = 2428055) B2428055
theorem B537403 : Blo 475787 537403 := bstep (se 1 (by rfl) ⟨403052, by rfl⟩ : syracuseStep 537403 = 806105) B806105
theorem B1356659 : Blo 475787 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B3814411 : Blo 475787 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B1618973 : Blo 475787 1618973 := bstep (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) B607115
theorem B8140013 : Blo 475787 8140013 := bstep (se 3 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 8140013 = 3052505) B3052505
theorem B537871 : Blo 475787 537871 := bstep (se 1 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 537871 = 806807) B806807
theorem B10302821 : Blo 475787 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B5813639 : Blo 475787 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B3618269 : Blo 475787 3618269 := bstep (se 3 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 3618269 = 1356851) B1356851
theorem B538375 : Blo 475787 538375 := bstep (se 1 (by rfl) ⟨403781, by rfl⟩ : syracuseStep 538375 = 807563) B807563
theorem B538555 : Blo 475787 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B1292233 : Blo 475787 1292233 := bstep (se 2 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 1292233 = 969175) B969175
theorem B767945 : Blo 475787 767945 := bstep (se 2 (by rfl) ⟨287979, by rfl⟩ : syracuseStep 767945 = 575959) B575959
theorem B3258569 : Blo 475787 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B6895817 : Blo 475787 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B539023 : Blo 475787 539023 := bstep (se 1 (by rfl) ⟨404267, by rfl⟩ : syracuseStep 539023 = 808535) B808535
theorem B1718795 : Blo 475787 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B1227383 : Blo 475787 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B539527 : Blo 475787 539527 := bstep (se 1 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 539527 = 809291) B809291
theorem B605227 : Blo 475787 605227 := bstep (se 1 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 605227 = 907841) B907841
theorem B1555499 : Blo 475787 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B539707 : Blo 475787 539707 := bstep (se 1 (by rfl) ⟨404780, by rfl⟩ : syracuseStep 539707 = 809561) B809561
theorem B1359119 : Blo 475787 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B1818065 : Blo 475787 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B933419 : Blo 475787 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B1818521 : Blo 475787 1818521 := bstep (se 2 (by rfl) ⟨681945, by rfl⟩ : syracuseStep 1818521 = 1363891) B1363891
theorem B573355 : Blo 475787 573355 := bstep (se 1 (by rfl) ⟨430016, by rfl⟩ : syracuseStep 573355 = 860033) B860033
theorem B606199 : Blo 475787 606199 := bstep (se 1 (by rfl) ⟨454649, by rfl⟩ : syracuseStep 606199 = 909299) B909299
theorem B6701173 : Blo 475787 6701173 := bstep (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) B628235
theorem B573575 : Blo 475787 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B6144173 : Blo 475787 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B606523 : Blo 475787 606523 := bstep (se 1 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 606523 = 909785) B909785
theorem B508303 : Blo 475787 508303 := bstep (se 1 (by rfl) ⟨381227, by rfl⟩ : syracuseStep 508303 = 762455) B762455
theorem B15483413 : Blo 475787 15483413 := bstep (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) B725785
theorem B2769437 : Blo 475787 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B803371 : Blo 475787 803371 := bstep (se 1 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 803371 = 1205057) B1205057
theorem B475791 : Blo 475787 475791 := bstep (se 1 (by rfl) ⟨356843, by rfl⟩ : syracuseStep 475791 = 713687) B713687
theorem B803513 : Blo 475787 803513 := bstep (se 2 (by rfl) ⟨301317, by rfl⟩ : syracuseStep 803513 = 602635) B602635
theorem B475835 : Blo 475787 475835 := bstep (se 1 (by rfl) ⟨356876, by rfl⟩ : syracuseStep 475835 = 713753) B713753
theorem B475911 : Blo 475787 475911 := bstep (se 1 (by rfl) ⟨356933, by rfl⟩ : syracuseStep 475911 = 713867) B713867
theorem B475919 : Blo 475787 475919 := bstep (se 1 (by rfl) ⟨356939, by rfl⟩ : syracuseStep 475919 = 713879) B713879
theorem B3261221 : Blo 475787 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B3457829 : Blo 475787 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B475963 : Blo 475787 475963 := bstep (se 1 (by rfl) ⟨356972, by rfl⟩ : syracuseStep 475963 = 713945) B713945
theorem B1360759 : Blo 475787 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B476039 : Blo 475787 476039 := bstep (se 1 (by rfl) ⟨357029, by rfl⟩ : syracuseStep 476039 = 714059) B714059
theorem B476047 : Blo 475787 476047 := bstep (se 1 (by rfl) ⟨357035, by rfl⟩ : syracuseStep 476047 = 714071) B714071
theorem B1360793 : Blo 475787 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B476091 : Blo 475787 476091 := bstep (se 1 (by rfl) ⟨357068, by rfl⟩ : syracuseStep 476091 = 714137) B714137
theorem B2409425 : Blo 475787 2409425 := bstep (se 2 (by rfl) ⟨903534, by rfl⟩ : syracuseStep 2409425 = 1807069) B1807069
theorem B476167 : Blo 475787 476167 := bstep (se 1 (by rfl) ⟨357125, by rfl⟩ : syracuseStep 476167 = 714251) B714251
theorem B1360907 : Blo 475787 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B476175 : Blo 475787 476175 := bstep (se 1 (by rfl) ⟨357131, by rfl⟩ : syracuseStep 476175 = 714263) B714263
theorem B1819691 : Blo 475787 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B476219 : Blo 475787 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B476295 : Blo 475787 476295 := bstep (se 1 (by rfl) ⟨357221, by rfl⟩ : syracuseStep 476295 = 714443) B714443
theorem B476303 : Blo 475787 476303 := bstep (se 1 (by rfl) ⟨357227, by rfl⟩ : syracuseStep 476303 = 714455) B714455
theorem B476347 : Blo 475787 476347 := bstep (se 1 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 476347 = 714521) B714521
theorem B476423 : Blo 475787 476423 := bstep (se 1 (by rfl) ⟨357317, by rfl⟩ : syracuseStep 476423 = 714635) B714635
theorem B476431 : Blo 475787 476431 := bstep (se 1 (by rfl) ⟨357323, by rfl⟩ : syracuseStep 476431 = 714647) B714647
theorem B2934049 : Blo 475787 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B476475 : Blo 475787 476475 := bstep (se 1 (by rfl) ⟨357356, by rfl⟩ : syracuseStep 476475 = 714713) B714713
theorem B804215 : Blo 475787 804215 := bstep (se 1 (by rfl) ⟨603161, by rfl⟩ : syracuseStep 804215 = 1206323) B1206323
theorem B476551 : Blo 475787 476551 := bstep (se 1 (by rfl) ⟨357413, by rfl⟩ : syracuseStep 476551 = 714827) B714827
theorem B476559 : Blo 475787 476559 := bstep (se 1 (by rfl) ⟨357419, by rfl⟩ : syracuseStep 476559 = 714839) B714839
theorem B1230265 : Blo 475787 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B476603 : Blo 475787 476603 := bstep (se 1 (by rfl) ⟨357452, by rfl⟩ : syracuseStep 476603 = 714905) B714905
theorem B8144387 : Blo 475787 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B476679 : Blo 475787 476679 := bstep (se 1 (by rfl) ⟨357509, by rfl⟩ : syracuseStep 476679 = 715019) B715019
theorem B476687 : Blo 475787 476687 := bstep (se 1 (by rfl) ⟨357515, by rfl⟩ : syracuseStep 476687 = 715031) B715031
theorem B476731 : Blo 475787 476731 := bstep (se 1 (by rfl) ⟨357548, by rfl⟩ : syracuseStep 476731 = 715097) B715097
theorem B476807 : Blo 475787 476807 := bstep (se 1 (by rfl) ⟨357605, by rfl⟩ : syracuseStep 476807 = 715211) B715211
theorem B476815 : Blo 475787 476815 := bstep (se 1 (by rfl) ⟨357611, by rfl⟩ : syracuseStep 476815 = 715223) B715223
theorem B575147 : Blo 475787 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B10798771 : Blo 475787 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B673465 : Blo 475787 673465 := bstep (se 2 (by rfl) ⟨252549, by rfl⟩ : syracuseStep 673465 = 505099) B505099
theorem B476859 : Blo 475787 476859 := bstep (se 1 (by rfl) ⟨357644, by rfl⟩ : syracuseStep 476859 = 715289) B715289
theorem B476935 : Blo 475787 476935 := bstep (se 1 (by rfl) ⟨357701, by rfl⟩ : syracuseStep 476935 = 715403) B715403
theorem B476943 : Blo 475787 476943 := bstep (se 1 (by rfl) ⟨357707, by rfl⟩ : syracuseStep 476943 = 715415) B715415
theorem B1296157 : Blo 475787 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B870203 : Blo 475787 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B804667 : Blo 475787 804667 := bstep (se 1 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 804667 = 1207001) B1207001
theorem B476987 : Blo 475787 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B477063 : Blo 475787 477063 := bstep (se 1 (by rfl) ⟨357797, by rfl⟩ : syracuseStep 477063 = 715595) B715595
theorem B477071 : Blo 475787 477071 := bstep (se 1 (by rfl) ⟨357803, by rfl⟩ : syracuseStep 477071 = 715607) B715607
theorem B477115 : Blo 475787 477115 := bstep (se 1 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 477115 = 715673) B715673
theorem B804809 : Blo 475787 804809 := bstep (se 2 (by rfl) ⟨301803, by rfl⟩ : syracuseStep 804809 = 603607) B603607
theorem B477191 : Blo 475787 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B477199 : Blo 475787 477199 := bstep (se 1 (by rfl) ⟨357899, by rfl⟩ : syracuseStep 477199 = 715799) B715799
theorem B9783341 : Blo 475787 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B477243 : Blo 475787 477243 := bstep (se 1 (by rfl) ⟨357932, by rfl⟩ : syracuseStep 477243 = 715865) B715865
theorem B1362035 : Blo 475787 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B477319 : Blo 475787 477319 := bstep (se 1 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 477319 = 715979) B715979
theorem B575623 : Blo 475787 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B477327 : Blo 475787 477327 := bstep (se 1 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 477327 = 715991) B715991
theorem B477371 : Blo 475787 477371 := bstep (se 1 (by rfl) ⟨358028, by rfl⟩ : syracuseStep 477371 = 716057) B716057
theorem B477447 : Blo 475787 477447 := bstep (se 1 (by rfl) ⟨358085, by rfl⟩ : syracuseStep 477447 = 716171) B716171
theorem B477455 : Blo 475787 477455 := bstep (se 1 (by rfl) ⟨358091, by rfl⟩ : syracuseStep 477455 = 716183) B716183
theorem B903467 : Blo 475787 903467 := bstep (se 1 (by rfl) ⟨677600, by rfl⟩ : syracuseStep 903467 = 1355201) B1355201
theorem B477499 : Blo 475787 477499 := bstep (se 1 (by rfl) ⟨358124, by rfl⟩ : syracuseStep 477499 = 716249) B716249
theorem B477575 : Blo 475787 477575 := bstep (se 1 (by rfl) ⟨358181, by rfl⟩ : syracuseStep 477575 = 716363) B716363
theorem B477583 : Blo 475787 477583 := bstep (se 1 (by rfl) ⟨358187, by rfl⟩ : syracuseStep 477583 = 716375) B716375
theorem B477627 : Blo 475787 477627 := bstep (se 1 (by rfl) ⟨358220, by rfl⟩ : syracuseStep 477627 = 716441) B716441
theorem B1722833 : Blo 475787 1722833 := bstep (se 2 (by rfl) ⟨646062, by rfl⟩ : syracuseStep 1722833 = 1292125) B1292125
theorem B1362433 : Blo 475787 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B477703 : Blo 475787 477703 := bstep (se 1 (by rfl) ⟨358277, by rfl⟩ : syracuseStep 477703 = 716555) B716555
theorem B477711 : Blo 475787 477711 := bstep (se 1 (by rfl) ⟨358283, by rfl⟩ : syracuseStep 477711 = 716567) B716567
theorem B477755 : Blo 475787 477755 := bstep (se 1 (by rfl) ⟨358316, by rfl⟩ : syracuseStep 477755 = 716633) B716633
theorem B1362491 : Blo 475787 1362491 := bstep (se 1 (by rfl) ⟨1021868, by rfl⟩ : syracuseStep 1362491 = 2043737) B2043737
theorem B805511 : Blo 475787 805511 := bstep (se 1 (by rfl) ⟨604133, by rfl⟩ : syracuseStep 805511 = 1208267) B1208267
theorem B477831 : Blo 475787 477831 := bstep (se 1 (by rfl) ⟨358373, by rfl⟩ : syracuseStep 477831 = 716747) B716747
theorem B477839 : Blo 475787 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B477883 : Blo 475787 477883 := bstep (se 1 (by rfl) ⟨358412, by rfl⟩ : syracuseStep 477883 = 716825) B716825
theorem B477959 : Blo 475787 477959 := bstep (se 1 (by rfl) ⟨358469, by rfl⟩ : syracuseStep 477959 = 716939) B716939
theorem B477967 : Blo 475787 477967 := bstep (se 1 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 477967 = 716951) B716951
theorem B543547 : Blo 475787 543547 := bstep (se 1 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 543547 = 815321) B815321
theorem B478011 : Blo 475787 478011 := bstep (se 1 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 478011 = 717017) B717017
theorem B1526663 : Blo 475787 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B478087 : Blo 475787 478087 := bstep (se 1 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 478087 = 717131) B717131
theorem B478095 : Blo 475787 478095 := bstep (se 1 (by rfl) ⟨358571, by rfl⟩ : syracuseStep 478095 = 717143) B717143
theorem B478139 : Blo 475787 478139 := bstep (se 1 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 478139 = 717209) B717209
theorem B1821649 : Blo 475787 1821649 := bstep (se 2 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 1821649 = 1366237) B1366237
theorem B478215 : Blo 475787 478215 := bstep (se 1 (by rfl) ⟨358661, by rfl⟩ : syracuseStep 478215 = 717323) B717323
theorem B2411531 : Blo 475787 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B478223 : Blo 475787 478223 := bstep (se 1 (by rfl) ⟨358667, by rfl⟩ : syracuseStep 478223 = 717335) B717335
theorem B478267 : Blo 475787 478267 := bstep (se 1 (by rfl) ⟨358700, by rfl⟩ : syracuseStep 478267 = 717401) B717401
theorem B478343 : Blo 475787 478343 := bstep (se 1 (by rfl) ⟨358757, by rfl⟩ : syracuseStep 478343 = 717515) B717515
theorem B478351 : Blo 475787 478351 := bstep (se 1 (by rfl) ⟨358763, by rfl⟩ : syracuseStep 478351 = 717527) B717527
theorem B2411693 : Blo 475787 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B478395 : Blo 475787 478395 := bstep (se 1 (by rfl) ⟨358796, by rfl⟩ : syracuseStep 478395 = 717593) B717593
theorem B478471 : Blo 475787 478471 := bstep (se 1 (by rfl) ⟨358853, by rfl⟩ : syracuseStep 478471 = 717707) B717707
theorem B806159 : Blo 475787 806159 := bstep (se 1 (by rfl) ⟨604619, by rfl⟩ : syracuseStep 806159 = 1209239) B1209239
theorem B478479 : Blo 475787 478479 := bstep (se 1 (by rfl) ⟨358859, by rfl⟩ : syracuseStep 478479 = 717719) B717719
theorem B478523 : Blo 475787 478523 := bstep (se 1 (by rfl) ⟨358892, by rfl⟩ : syracuseStep 478523 = 717785) B717785
theorem B904583 : Blo 475787 904583 := bstep (se 1 (by rfl) ⟨678437, by rfl⟩ : syracuseStep 904583 = 1356875) B1356875
theorem B478599 : Blo 475787 478599 := bstep (se 1 (by rfl) ⟨358949, by rfl⟩ : syracuseStep 478599 = 717899) B717899
theorem B478607 : Blo 475787 478607 := bstep (se 1 (by rfl) ⟨358955, by rfl⟩ : syracuseStep 478607 = 717911) B717911
theorem B2936249 : Blo 475787 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B478651 : Blo 475787 478651 := bstep (se 1 (by rfl) ⟨358988, by rfl⟩ : syracuseStep 478651 = 717977) B717977
theorem B4607441 : Blo 475787 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B478727 : Blo 475787 478727 := bstep (se 1 (by rfl) ⟨359045, by rfl⟩ : syracuseStep 478727 = 718091) B718091
theorem B478735 : Blo 475787 478735 := bstep (se 1 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 478735 = 718103) B718103
theorem B478779 : Blo 475787 478779 := bstep (se 1 (by rfl) ⟨359084, by rfl⟩ : syracuseStep 478779 = 718169) B718169
theorem B4574839 : Blo 475787 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B478855 : Blo 475787 478855 := bstep (se 1 (by rfl) ⟨359141, by rfl⟩ : syracuseStep 478855 = 718283) B718283
theorem B478863 : Blo 475787 478863 := bstep (se 1 (by rfl) ⟨359147, by rfl⟩ : syracuseStep 478863 = 718295) B718295
theorem B8179379 : Blo 475787 8179379 := bstep (se 1 (by rfl) ⟨6134534, by rfl⟩ : syracuseStep 8179379 = 12269069) B12269069
theorem B478907 : Blo 475787 478907 := bstep (se 1 (by rfl) ⟨359180, by rfl⟩ : syracuseStep 478907 = 718361) B718361
theorem B478983 : Blo 475787 478983 := bstep (se 1 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 478983 = 718475) B718475
theorem B478991 : Blo 475787 478991 := bstep (se 1 (by rfl) ⟨359243, by rfl⟩ : syracuseStep 478991 = 718487) B718487
theorem B806699 : Blo 475787 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B479035 : Blo 475787 479035 := bstep (se 1 (by rfl) ⟨359276, by rfl⟩ : syracuseStep 479035 = 718553) B718553
theorem B2215795 : Blo 475787 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B479111 : Blo 475787 479111 := bstep (se 1 (by rfl) ⟨359333, by rfl⟩ : syracuseStep 479111 = 718667) B718667
theorem B479119 : Blo 475787 479119 := bstep (se 1 (by rfl) ⟨359339, by rfl⟩ : syracuseStep 479119 = 718679) B718679
theorem B905107 : Blo 475787 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B479163 : Blo 475787 479163 := bstep (se 1 (by rfl) ⟨359372, by rfl⟩ : syracuseStep 479163 = 718745) B718745
theorem B479239 : Blo 475787 479239 := bstep (se 1 (by rfl) ⟨359429, by rfl⟩ : syracuseStep 479239 = 718859) B718859
theorem B479247 : Blo 475787 479247 := bstep (se 1 (by rfl) ⟨359435, by rfl⟩ : syracuseStep 479247 = 718871) B718871
theorem B479291 : Blo 475787 479291 := bstep (se 1 (by rfl) ⟨359468, by rfl⟩ : syracuseStep 479291 = 718937) B718937
theorem B479367 : Blo 475787 479367 := bstep (se 1 (by rfl) ⟨359525, by rfl⟩ : syracuseStep 479367 = 719051) B719051
theorem B479375 : Blo 475787 479375 := bstep (se 1 (by rfl) ⟨359531, by rfl⟩ : syracuseStep 479375 = 719063) B719063
theorem B807097 : Blo 475787 807097 := bstep (se 2 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 807097 = 605323) B605323
theorem B479419 : Blo 475787 479419 := bstep (se 1 (by rfl) ⟨359564, by rfl⟩ : syracuseStep 479419 = 719129) B719129
theorem B479495 : Blo 475787 479495 := bstep (se 1 (by rfl) ⟨359621, by rfl⟩ : syracuseStep 479495 = 719243) B719243
theorem B479503 : Blo 475787 479503 := bstep (se 1 (by rfl) ⟨359627, by rfl⟩ : syracuseStep 479503 = 719255) B719255
theorem B479547 : Blo 475787 479547 := bstep (se 1 (by rfl) ⟨359660, by rfl⟩ : syracuseStep 479547 = 719321) B719321
theorem B479623 : Blo 475787 479623 := bstep (se 1 (by rfl) ⟨359717, by rfl⟩ : syracuseStep 479623 = 719435) B719435
theorem B479631 : Blo 475787 479631 := bstep (se 1 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 479631 = 719447) B719447
theorem B479675 : Blo 475787 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B479751 : Blo 475787 479751 := bstep (se 1 (by rfl) ⟨359813, by rfl⟩ : syracuseStep 479751 = 719627) B719627
theorem B479759 : Blo 475787 479759 := bstep (se 1 (by rfl) ⟨359819, by rfl⟩ : syracuseStep 479759 = 719639) B719639
theorem B2413313 : Blo 475787 2413313 := bstep (se 2 (by rfl) ⟨904992, by rfl⟩ : syracuseStep 2413313 = 1809985) B1809985
theorem B1364779 : Blo 475787 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B807799 : Blo 475787 807799 := bstep (se 1 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 807799 = 1211699) B1211699
theorem B1365007 : Blo 475787 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B906299 : Blo 475787 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B807995 : Blo 475787 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B3626045 : Blo 475787 3626045 := bstep (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) B1359767
theorem B1528919 : Blo 475787 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B4150561 : Blo 475787 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 475787 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B4576571 : Blo 475787 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B2184583 : Blo 475787 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B808393 : Blo 475787 808393 := bstep (se 2 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 808393 = 606295) B606295
theorem B546319 : Blo 475787 546319 := bstep (se 1 (by rfl) ⟨409739, by rfl⟩ : syracuseStep 546319 = 819479) B819479
theorem B906785 : Blo 475787 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B2414123 : Blo 475787 2414123 := bstep (se 1 (by rfl) ⟨1810592, by rfl⟩ : syracuseStep 2414123 = 3621185) B3621185
theorem B1070711 : Blo 475787 1070711 := bstep (se 1 (by rfl) ⟨803033, by rfl⟩ : syracuseStep 1070711 = 1606067) B1606067
theorem B1365623 : Blo 475787 1365623 := bstep (se 1 (by rfl) ⟨1024217, by rfl⟩ : syracuseStep 1365623 = 2048435) B2048435
theorem B1070891 : Blo 475787 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B907051 : Blo 475787 907051 := bstep (se 1 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 907051 = 1360577) B1360577
theorem B1529867 : Blo 475787 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B809095 : Blo 475787 809095 := bstep (se 1 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 809095 = 1213643) B1213643
theorem B1071251 : Blo 475787 1071251 := bstep (se 1 (by rfl) ⟨803438, by rfl⟩ : syracuseStep 1071251 = 1606877) B1606877
theorem B678073 : Blo 475787 678073 := bstep (se 2 (by rfl) ⟨254277, by rfl⟩ : syracuseStep 678073 = 508555) B508555
theorem B1071305 : Blo 475787 1071305 := bstep (se 2 (by rfl) ⟨401739, by rfl⟩ : syracuseStep 1071305 = 803479) B803479
theorem B2709875 : Blo 475787 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B1628531 : Blo 475787 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B2578823 : Blo 475787 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B2710331 : Blo 475787 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B2415419 : Blo 475787 2415419 := bstep (se 1 (by rfl) ⟨1811564, by rfl⟩ : syracuseStep 2415419 = 3623129) B3623129
theorem B1072007 : Blo 475787 1072007 := bstep (se 1 (by rfl) ⟨804005, by rfl⟩ : syracuseStep 1072007 = 1608011) B1608011
theorem B908167 : Blo 475787 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B2415581 : Blo 475787 2415581 := bstep (se 3 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 2415581 = 905843) B905843
theorem B12409861 : Blo 475787 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B1072187 : Blo 475787 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B47733941 : Blo 475787 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B1072313 : Blo 475787 1072313 := bstep (se 2 (by rfl) ⟨402117, by rfl⟩ : syracuseStep 1072313 = 804235) B804235
theorem B2415905 : Blo 475787 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B679303 : Blo 475787 679303 := bstep (se 1 (by rfl) ⟨509477, by rfl⟩ : syracuseStep 679303 = 1018955) B1018955
theorem B908729 : Blo 475787 908729 := bstep (se 2 (by rfl) ⟨340773, by rfl⟩ : syracuseStep 908729 = 681547) B681547
theorem B6872525 : Blo 475787 6872525 := bstep (se 3 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 6872525 = 2577197) B2577197
theorem B1072655 : Blo 475787 1072655 := bstep (se 1 (by rfl) ⟨804491, by rfl⟩ : syracuseStep 1072655 = 1608983) B1608983
theorem B1072673 : Blo 475787 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B5529131 : Blo 475787 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B2711333 : Blo 475787 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B4349747 : Blo 475787 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B1073015 : Blo 475787 1073015 := bstep (se 1 (by rfl) ⟨804761, by rfl⟩ : syracuseStep 1073015 = 1609523) B1609523
theorem B1073195 : Blo 475787 1073195 := bstep (se 1 (by rfl) ⟨804896, by rfl⟩ : syracuseStep 1073195 = 1609793) B1609793
theorem B1204409 : Blo 475787 1204409 := bstep (se 2 (by rfl) ⟨451653, by rfl⟩ : syracuseStep 1204409 = 903307) B903307
theorem B680123 : Blo 475787 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B2711789 : Blo 475787 2711789 := bstep (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) B1016921
theorem B2515181 : Blo 475787 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B2416877 : Blo 475787 2416877 := bstep (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) B906329
theorem B3629447 : Blo 475787 3629447 := bstep (se 1 (by rfl) ⟨2722085, by rfl⟩ : syracuseStep 3629447 = 5444171) B5444171
theorem B1073555 : Blo 475787 1073555 := bstep (se 1 (by rfl) ⟨805166, by rfl⟩ : syracuseStep 1073555 = 1610333) B1610333
theorem B1073609 : Blo 475787 1073609 := bstep (se 2 (by rfl) ⟨402603, by rfl⟩ : syracuseStep 1073609 = 805207) B805207
theorem B909883 : Blo 475787 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B680567 : Blo 475787 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B13787941 : Blo 475787 13787941 := bstep (se 4 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 13787941 = 2585239) B2585239
theorem B680761 : Blo 475787 680761 := bstep (se 2 (by rfl) ⟨255285, by rfl⟩ : syracuseStep 680761 = 510571) B510571
theorem B2712473 : Blo 475787 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B713735 : Blo 475787 713735 := bstep (se 1 (by rfl) ⟨535301, by rfl⟩ : syracuseStep 713735 = 1070603) B1070603
theorem B2417687 : Blo 475787 2417687 := bstep (se 1 (by rfl) ⟨1813265, by rfl⟩ : syracuseStep 2417687 = 3626531) B3626531
theorem B910369 : Blo 475787 910369 := bstep (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) B682777
theorem B713771 : Blo 475787 713771 := bstep (se 1 (by rfl) ⟨535328, by rfl⟩ : syracuseStep 713771 = 1070657) B1070657
theorem B713801 : Blo 475787 713801 := bstep (se 2 (by rfl) ⟨267675, by rfl⟩ : syracuseStep 713801 = 535351) B535351
theorem B1074311 : Blo 475787 1074311 := bstep (se 1 (by rfl) ⟨805733, by rfl⟩ : syracuseStep 1074311 = 1611467) B1611467
theorem B1205401 : Blo 475787 1205401 := bstep (se 2 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 1205401 = 904051) B904051
theorem B713915 : Blo 475787 713915 := bstep (se 1 (by rfl) ⟨535436, by rfl⟩ : syracuseStep 713915 = 1070873) B1070873
theorem B713975 : Blo 475787 713975 := bstep (se 1 (by rfl) ⟨535481, by rfl⟩ : syracuseStep 713975 = 1070963) B1070963
theorem B713999 : Blo 475787 713999 := bstep (se 1 (by rfl) ⟨535499, by rfl⟩ : syracuseStep 713999 = 1070999) B1070999
theorem B714041 : Blo 475787 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B1205563 : Blo 475787 1205563 := bstep (se 1 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 1205563 = 1808345) B1808345
theorem B1074491 : Blo 475787 1074491 := bstep (se 1 (by rfl) ⟨805868, by rfl⟩ : syracuseStep 1074491 = 1611737) B1611737
theorem B714119 : Blo 475787 714119 := bstep (se 1 (by rfl) ⟨535589, by rfl⟩ : syracuseStep 714119 = 1071179) B1071179
theorem B714155 : Blo 475787 714155 := bstep (se 1 (by rfl) ⟨535616, by rfl⟩ : syracuseStep 714155 = 1071233) B1071233
theorem B1074617 : Blo 475787 1074617 := bstep (se 2 (by rfl) ⟨402981, by rfl⟩ : syracuseStep 1074617 = 805963) B805963
theorem B714185 : Blo 475787 714185 := bstep (se 2 (by rfl) ⟨267819, by rfl⟩ : syracuseStep 714185 = 535639) B535639
theorem B1205705 : Blo 475787 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B714299 : Blo 475787 714299 := bstep (se 1 (by rfl) ⟨535724, by rfl⟩ : syracuseStep 714299 = 1071449) B1071449
theorem B2451005 : Blo 475787 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B714359 : Blo 475787 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B714383 : Blo 475787 714383 := bstep (se 1 (by rfl) ⟨535787, by rfl⟩ : syracuseStep 714383 = 1071575) B1071575
theorem B714425 : Blo 475787 714425 := bstep (se 2 (by rfl) ⟨267909, by rfl⟩ : syracuseStep 714425 = 535819) B535819
theorem B714503 : Blo 475787 714503 := bstep (se 1 (by rfl) ⟨535877, by rfl⟩ : syracuseStep 714503 = 1071755) B1071755
theorem B1074959 : Blo 475787 1074959 := bstep (se 1 (by rfl) ⟨806219, by rfl⟩ : syracuseStep 1074959 = 1612439) B1612439
theorem B1206049 : Blo 475787 1206049 := bstep (se 2 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 1206049 = 904537) B904537
theorem B1074977 : Blo 475787 1074977 := bstep (se 2 (by rfl) ⟨403116, by rfl⟩ : syracuseStep 1074977 = 806233) B806233
theorem B714539 : Blo 475787 714539 := bstep (se 1 (by rfl) ⟨535904, by rfl⟩ : syracuseStep 714539 = 1071809) B1071809
theorem B714569 : Blo 475787 714569 := bstep (se 2 (by rfl) ⟨267963, by rfl⟩ : syracuseStep 714569 = 535927) B535927
theorem B2582387 : Blo 475787 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B518023 : Blo 475787 518023 := bstep (se 1 (by rfl) ⟨388517, by rfl⟩ : syracuseStep 518023 = 777035) B777035
theorem B714683 : Blo 475787 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B714743 : Blo 475787 714743 := bstep (se 1 (by rfl) ⟨536057, by rfl⟩ : syracuseStep 714743 = 1072115) B1072115
theorem B714767 : Blo 475787 714767 := bstep (se 1 (by rfl) ⟨536075, by rfl⟩ : syracuseStep 714767 = 1072151) B1072151
theorem B714809 : Blo 475787 714809 := bstep (se 2 (by rfl) ⟨268053, by rfl⟩ : syracuseStep 714809 = 536107) B536107
theorem B1075319 : Blo 475787 1075319 := bstep (se 1 (by rfl) ⟨806489, by rfl⟩ : syracuseStep 1075319 = 1612979) B1612979
theorem B714887 : Blo 475787 714887 := bstep (se 1 (by rfl) ⟨536165, by rfl⟩ : syracuseStep 714887 = 1072331) B1072331
theorem B714923 : Blo 475787 714923 := bstep (se 1 (by rfl) ⟨536192, by rfl⟩ : syracuseStep 714923 = 1072385) B1072385
theorem B714953 : Blo 475787 714953 := bstep (se 2 (by rfl) ⟨268107, by rfl⟩ : syracuseStep 714953 = 536215) B536215
theorem B1075499 : Blo 475787 1075499 := bstep (se 1 (by rfl) ⟨806624, by rfl⟩ : syracuseStep 1075499 = 1613249) B1613249
theorem B715067 : Blo 475787 715067 := bstep (se 1 (by rfl) ⟨536300, by rfl⟩ : syracuseStep 715067 = 1072601) B1072601
theorem B1206647 : Blo 475787 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B715127 : Blo 475787 715127 := bstep (se 1 (by rfl) ⟨536345, by rfl⟩ : syracuseStep 715127 = 1072691) B1072691
theorem B715151 : Blo 475787 715151 := bstep (se 1 (by rfl) ⟨536363, by rfl⟩ : syracuseStep 715151 = 1072727) B1072727
theorem B715193 : Blo 475787 715193 := bstep (se 2 (by rfl) ⟨268197, by rfl⟩ : syracuseStep 715193 = 536395) B536395
theorem B715271 : Blo 475787 715271 := bstep (se 1 (by rfl) ⟨536453, by rfl⟩ : syracuseStep 715271 = 1072907) B1072907
theorem B2451991 : Blo 475787 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B715307 : Blo 475787 715307 := bstep (se 1 (by rfl) ⟨536480, by rfl⟩ : syracuseStep 715307 = 1072961) B1072961
theorem B715337 : Blo 475787 715337 := bstep (se 2 (by rfl) ⟨268251, by rfl⟩ : syracuseStep 715337 = 536503) B536503
theorem B1075859 : Blo 475787 1075859 := bstep (se 1 (by rfl) ⟨806894, by rfl⟩ : syracuseStep 1075859 = 1613789) B1613789
theorem B715451 : Blo 475787 715451 := bstep (se 1 (by rfl) ⟨536588, by rfl⟩ : syracuseStep 715451 = 1073177) B1073177
theorem B1075913 : Blo 475787 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B715511 : Blo 475787 715511 := bstep (se 1 (by rfl) ⟨536633, by rfl⟩ : syracuseStep 715511 = 1073267) B1073267
theorem B715535 : Blo 475787 715535 := bstep (se 1 (by rfl) ⟨536651, by rfl⟩ : syracuseStep 715535 = 1073303) B1073303
theorem B715577 : Blo 475787 715577 := bstep (se 2 (by rfl) ⟨268341, by rfl⟩ : syracuseStep 715577 = 536683) B536683
theorem B715655 : Blo 475787 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B715691 : Blo 475787 715691 := bstep (se 1 (by rfl) ⟨536768, by rfl⟩ : syracuseStep 715691 = 1073537) B1073537
theorem B715721 : Blo 475787 715721 := bstep (se 2 (by rfl) ⟨268395, by rfl⟩ : syracuseStep 715721 = 536791) B536791
theorem B715835 : Blo 475787 715835 := bstep (se 1 (by rfl) ⟨536876, by rfl⟩ : syracuseStep 715835 = 1073753) B1073753
theorem B715895 : Blo 475787 715895 := bstep (se 1 (by rfl) ⟨536921, by rfl⟩ : syracuseStep 715895 = 1073843) B1073843
theorem B715919 : Blo 475787 715919 := bstep (se 1 (by rfl) ⟨536939, by rfl⟩ : syracuseStep 715919 = 1073879) B1073879
theorem B715961 : Blo 475787 715961 := bstep (se 2 (by rfl) ⟨268485, by rfl⟩ : syracuseStep 715961 = 536971) B536971
theorem B716039 : Blo 475787 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B716075 : Blo 475787 716075 := bstep (se 1 (by rfl) ⟨537056, by rfl⟩ : syracuseStep 716075 = 1074113) B1074113
theorem B716105 : Blo 475787 716105 := bstep (se 2 (by rfl) ⟨268539, by rfl⟩ : syracuseStep 716105 = 537079) B537079
theorem B1076615 : Blo 475787 1076615 := bstep (se 1 (by rfl) ⟨807461, by rfl⟩ : syracuseStep 1076615 = 1614923) B1614923
theorem B716219 : Blo 475787 716219 := bstep (se 1 (by rfl) ⟨537164, by rfl⟩ : syracuseStep 716219 = 1074329) B1074329
theorem B716279 : Blo 475787 716279 := bstep (se 1 (by rfl) ⟨537209, by rfl⟩ : syracuseStep 716279 = 1074419) B1074419
theorem B716303 : Blo 475787 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B716345 : Blo 475787 716345 := bstep (se 2 (by rfl) ⟨268629, by rfl⟩ : syracuseStep 716345 = 537259) B537259
theorem B1076795 : Blo 475787 1076795 := bstep (se 1 (by rfl) ⟨807596, by rfl⟩ : syracuseStep 1076795 = 1615193) B1615193
theorem B1207943 : Blo 475787 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B716423 : Blo 475787 716423 := bstep (se 1 (by rfl) ⟨537317, by rfl⟩ : syracuseStep 716423 = 1074635) B1074635
theorem B716459 : Blo 475787 716459 := bstep (se 1 (by rfl) ⟨537344, by rfl⟩ : syracuseStep 716459 = 1074689) B1074689
theorem B9072307 : Blo 475787 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B1207993 : Blo 475787 1207993 := bstep (se 2 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 1207993 = 905995) B905995
theorem B1076921 : Blo 475787 1076921 := bstep (se 2 (by rfl) ⟨403845, by rfl⟩ : syracuseStep 1076921 = 807691) B807691
theorem B716489 : Blo 475787 716489 := bstep (se 2 (by rfl) ⟨268683, by rfl⟩ : syracuseStep 716489 = 537367) B537367
theorem B716603 : Blo 475787 716603 := bstep (se 1 (by rfl) ⟨537452, by rfl⟩ : syracuseStep 716603 = 1074905) B1074905
theorem B716663 : Blo 475787 716663 := bstep (se 1 (by rfl) ⟨537497, by rfl⟩ : syracuseStep 716663 = 1074995) B1074995
theorem B716687 : Blo 475787 716687 := bstep (se 1 (by rfl) ⟨537515, by rfl⟩ : syracuseStep 716687 = 1075031) B1075031
theorem B716729 : Blo 475787 716729 := bstep (se 2 (by rfl) ⟨268773, by rfl⟩ : syracuseStep 716729 = 537547) B537547
theorem B716807 : Blo 475787 716807 := bstep (se 1 (by rfl) ⟨537605, by rfl⟩ : syracuseStep 716807 = 1075211) B1075211
theorem B1077263 : Blo 475787 1077263 := bstep (se 1 (by rfl) ⟨807947, by rfl⟩ : syracuseStep 1077263 = 1615895) B1615895
theorem B2420765 : Blo 475787 2420765 := bstep (se 3 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 2420765 = 907787) B907787
theorem B1077281 : Blo 475787 1077281 := bstep (se 2 (by rfl) ⟨403980, by rfl⟩ : syracuseStep 1077281 = 807961) B807961
theorem B716843 : Blo 475787 716843 := bstep (se 1 (by rfl) ⟨537632, by rfl⟩ : syracuseStep 716843 = 1075265) B1075265
theorem B716873 : Blo 475787 716873 := bstep (se 2 (by rfl) ⟨268827, by rfl⟩ : syracuseStep 716873 = 537655) B537655
theorem B716987 : Blo 475787 716987 := bstep (se 1 (by rfl) ⟨537740, by rfl⟩ : syracuseStep 716987 = 1075481) B1075481
theorem B2355437 : Blo 475787 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B717047 : Blo 475787 717047 := bstep (se 1 (by rfl) ⟨537785, by rfl⟩ : syracuseStep 717047 = 1075571) B1075571
theorem B1208591 : Blo 475787 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B717071 : Blo 475787 717071 := bstep (se 1 (by rfl) ⟨537803, by rfl⟩ : syracuseStep 717071 = 1075607) B1075607
theorem B717113 : Blo 475787 717113 := bstep (se 2 (by rfl) ⟨268917, by rfl⟩ : syracuseStep 717113 = 537835) B537835
theorem B1077623 : Blo 475787 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B717191 : Blo 475787 717191 := bstep (se 1 (by rfl) ⟨537893, by rfl⟩ : syracuseStep 717191 = 1075787) B1075787
theorem B717227 : Blo 475787 717227 := bstep (se 1 (by rfl) ⟨537920, by rfl⟩ : syracuseStep 717227 = 1075841) B1075841
theorem B717257 : Blo 475787 717257 := bstep (se 2 (by rfl) ⟨268971, by rfl⟩ : syracuseStep 717257 = 537943) B537943
theorem B2716163 : Blo 475787 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B2421251 : Blo 475787 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B1077803 : Blo 475787 1077803 := bstep (se 1 (by rfl) ⟨808352, by rfl⟩ : syracuseStep 1077803 = 1616705) B1616705
theorem B717371 : Blo 475787 717371 := bstep (se 1 (by rfl) ⟨538028, by rfl⟩ : syracuseStep 717371 = 1076057) B1076057
theorem B2585155 : Blo 475787 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B717431 : Blo 475787 717431 := bstep (se 1 (by rfl) ⟨538073, by rfl⟩ : syracuseStep 717431 = 1076147) B1076147
theorem B717455 : Blo 475787 717455 := bstep (se 1 (by rfl) ⟨538091, by rfl⟩ : syracuseStep 717455 = 1076183) B1076183
theorem B717497 : Blo 475787 717497 := bstep (se 2 (by rfl) ⟨269061, by rfl⟩ : syracuseStep 717497 = 538123) B538123
theorem B717575 : Blo 475787 717575 := bstep (se 1 (by rfl) ⟨538181, by rfl⟩ : syracuseStep 717575 = 1076363) B1076363
theorem B717611 : Blo 475787 717611 := bstep (se 1 (by rfl) ⟨538208, by rfl⟩ : syracuseStep 717611 = 1076417) B1076417
theorem B717641 : Blo 475787 717641 := bstep (se 2 (by rfl) ⟨269115, by rfl⟩ : syracuseStep 717641 = 538231) B538231
theorem B1078163 : Blo 475787 1078163 := bstep (se 1 (by rfl) ⟨808622, by rfl⟩ : syracuseStep 1078163 = 1617245) B1617245
theorem B717755 : Blo 475787 717755 := bstep (se 1 (by rfl) ⟨538316, by rfl⟩ : syracuseStep 717755 = 1076633) B1076633
theorem B1209289 : Blo 475787 1209289 := bstep (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) B906967
theorem B1078217 : Blo 475787 1078217 := bstep (se 2 (by rfl) ⟨404331, by rfl⟩ : syracuseStep 1078217 = 808663) B808663
theorem B717815 : Blo 475787 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B717839 : Blo 475787 717839 := bstep (se 1 (by rfl) ⟨538379, by rfl⟩ : syracuseStep 717839 = 1076759) B1076759
theorem B717881 : Blo 475787 717881 := bstep (se 2 (by rfl) ⟨269205, by rfl⟩ : syracuseStep 717881 = 538411) B538411
theorem B1209431 : Blo 475787 1209431 := bstep (se 1 (by rfl) ⟨907073, by rfl⟩ : syracuseStep 1209431 = 1814147) B1814147
theorem B717959 : Blo 475787 717959 := bstep (se 1 (by rfl) ⟨538469, by rfl⟩ : syracuseStep 717959 = 1076939) B1076939
theorem B717995 : Blo 475787 717995 := bstep (se 1 (by rfl) ⟨538496, by rfl⟩ : syracuseStep 717995 = 1076993) B1076993
theorem B718025 : Blo 475787 718025 := bstep (se 2 (by rfl) ⟨269259, by rfl⟩ : syracuseStep 718025 = 538519) B538519
theorem B816427 : Blo 475787 816427 := bstep (se 1 (by rfl) ⟨612320, by rfl⟩ : syracuseStep 816427 = 1224641) B1224641
theorem B718139 : Blo 475787 718139 := bstep (se 1 (by rfl) ⟨538604, by rfl⟩ : syracuseStep 718139 = 1077209) B1077209
theorem B718199 : Blo 475787 718199 := bstep (se 1 (by rfl) ⟨538649, by rfl⟩ : syracuseStep 718199 = 1077299) B1077299
theorem B718223 : Blo 475787 718223 := bstep (se 1 (by rfl) ⟨538667, by rfl⟩ : syracuseStep 718223 = 1077335) B1077335
theorem B718265 : Blo 475787 718265 := bstep (se 2 (by rfl) ⟨269349, by rfl⟩ : syracuseStep 718265 = 538699) B538699
theorem B5436881 : Blo 475787 5436881 := bstep (se 2 (by rfl) ⟨2038830, by rfl⟩ : syracuseStep 5436881 = 4077661) B4077661
theorem B718343 : Blo 475787 718343 := bstep (se 1 (by rfl) ⟨538757, by rfl⟩ : syracuseStep 718343 = 1077515) B1077515
theorem B718379 : Blo 475787 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B718409 : Blo 475787 718409 := bstep (se 2 (by rfl) ⟨269403, by rfl⟩ : syracuseStep 718409 = 538807) B538807
theorem B4093517 : Blo 475787 4093517 := bstep (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) B1535069
theorem B1078919 : Blo 475787 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B718523 : Blo 475787 718523 := bstep (se 1 (by rfl) ⟨538892, by rfl⟩ : syracuseStep 718523 = 1077785) B1077785
theorem B718583 : Blo 475787 718583 := bstep (se 1 (by rfl) ⟨538937, by rfl⟩ : syracuseStep 718583 = 1077875) B1077875
theorem B718607 : Blo 475787 718607 := bstep (se 1 (by rfl) ⟨538955, by rfl⟩ : syracuseStep 718607 = 1077911) B1077911
theorem B718649 : Blo 475787 718649 := bstep (se 2 (by rfl) ⟨269493, by rfl⟩ : syracuseStep 718649 = 538987) B538987
theorem B1079099 : Blo 475787 1079099 := bstep (se 1 (by rfl) ⟨809324, by rfl⟩ : syracuseStep 1079099 = 1618649) B1618649
theorem B718727 : Blo 475787 718727 := bstep (se 1 (by rfl) ⟨539045, by rfl⟩ : syracuseStep 718727 = 1078091) B1078091
theorem B718763 : Blo 475787 718763 := bstep (se 1 (by rfl) ⟨539072, by rfl⟩ : syracuseStep 718763 = 1078145) B1078145
theorem B1079225 : Blo 475787 1079225 := bstep (se 2 (by rfl) ⟨404709, by rfl⟩ : syracuseStep 1079225 = 809419) B809419
theorem B718793 : Blo 475787 718793 := bstep (se 2 (by rfl) ⟨269547, by rfl⟩ : syracuseStep 718793 = 539095) B539095
theorem B718907 : Blo 475787 718907 := bstep (se 1 (by rfl) ⟨539180, by rfl⟩ : syracuseStep 718907 = 1078361) B1078361
theorem B2422871 : Blo 475787 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B718967 : Blo 475787 718967 := bstep (se 1 (by rfl) ⟨539225, by rfl⟩ : syracuseStep 718967 = 1078451) B1078451
theorem B718991 : Blo 475787 718991 := bstep (se 1 (by rfl) ⟨539243, by rfl⟩ : syracuseStep 718991 = 1078487) B1078487
theorem B719033 : Blo 475787 719033 := bstep (se 2 (by rfl) ⟨269637, by rfl⟩ : syracuseStep 719033 = 539275) B539275
theorem B719111 : Blo 475787 719111 := bstep (se 1 (by rfl) ⟨539333, by rfl⟩ : syracuseStep 719111 = 1078667) B1078667
theorem B719147 : Blo 475787 719147 := bstep (se 1 (by rfl) ⟨539360, by rfl⟩ : syracuseStep 719147 = 1078721) B1078721
theorem B719177 : Blo 475787 719177 := bstep (se 2 (by rfl) ⟨269691, by rfl⟩ : syracuseStep 719177 = 539383) B539383
theorem B719291 : Blo 475787 719291 := bstep (se 1 (by rfl) ⟨539468, by rfl⟩ : syracuseStep 719291 = 1078937) B1078937
theorem B719351 : Blo 475787 719351 := bstep (se 1 (by rfl) ⟨539513, by rfl⟩ : syracuseStep 719351 = 1079027) B1079027
theorem B719375 : Blo 475787 719375 := bstep (se 1 (by rfl) ⟨539531, by rfl⟩ : syracuseStep 719375 = 1079063) B1079063
theorem B719417 : Blo 475787 719417 := bstep (se 2 (by rfl) ⟨269781, by rfl⟩ : syracuseStep 719417 = 539563) B539563
theorem B2423357 : Blo 475787 2423357 := bstep (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) B908759
theorem B719495 : Blo 475787 719495 := bstep (se 1 (by rfl) ⟨539621, by rfl⟩ : syracuseStep 719495 = 1079243) B1079243
theorem B719531 : Blo 475787 719531 := bstep (se 1 (by rfl) ⟨539648, by rfl⟩ : syracuseStep 719531 = 1079297) B1079297
theorem B719561 : Blo 475787 719561 := bstep (se 2 (by rfl) ⟨269835, by rfl⟩ : syracuseStep 719561 = 539671) B539671
theorem B719675 : Blo 475787 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B1211507 : Blo 475787 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B9305549 : Blo 475787 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B5799377 : Blo 475787 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B2588183 : Blo 475787 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B982561 : Blo 475787 982561 := bstep (se 2 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 982561 = 736921) B736921
theorem B8289869 : Blo 475787 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1212023 : Blo 475787 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B3440357 : Blo 475787 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B4096115 : Blo 475787 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B15532195 : Blo 475787 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B10322275 : Blo 475787 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B1606013 : Blo 475787 1606013 := bstep (se 3 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 1606013 = 602255) B602255
theorem B1606283 : Blo 475787 1606283 := bstep (se 1 (by rfl) ⟨1204712, by rfl⟩ : syracuseStep 1606283 = 2409425) B2409425
theorem B1213127 : Blo 475787 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B1213177 : Blo 475787 1213177 := bstep (se 2 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 1213177 = 909883) B909883
theorem B18383921 : Blo 475787 18383921 := bstep (se 2 (by rfl) ⟨6893970, by rfl⟩ : syracuseStep 18383921 = 13787941) B13787941
theorem B984143 : Blo 475787 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B6522227 : Blo 475787 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B1213825 : Blo 475787 1213825 := bstep (se 2 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 1213825 = 910369) B910369
theorem B1607201 : Blo 475787 1607201 := bstep (se 2 (by rfl) ⟨602700, by rfl⟩ : syracuseStep 1607201 = 1205401) B1205401
theorem B1148555 : Blo 475787 1148555 := bstep (se 1 (by rfl) ⟨861416, by rfl⟩ : syracuseStep 1148555 = 1722833) B1722833
theorem B1607417 : Blo 475787 1607417 := bstep (se 2 (by rfl) ⟨602781, by rfl⟩ : syracuseStep 1607417 = 1205563) B1205563
theorem B1640353 : Blo 475787 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1017775 : Blo 475787 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B1607687 : Blo 475787 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B7342169 : Blo 475787 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B1607795 : Blo 475787 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B6130025 : Blo 475787 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B1608065 : Blo 475787 1608065 := bstep (se 2 (by rfl) ⟨603024, by rfl⟩ : syracuseStep 1608065 = 1206049) B1206049
theorem B690697 : Blo 475787 690697 := bstep (se 2 (by rfl) ⟨259011, by rfl⟩ : syracuseStep 690697 = 518023) B518023
theorem B9276229 : Blo 475787 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B1018937 : Blo 475787 1018937 := bstep (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) B764203
theorem B1608875 : Blo 475787 1608875 := bstep (se 1 (by rfl) ⟨1206656, by rfl⟩ : syracuseStep 1608875 = 2413313) B2413313
theorem B1019279 : Blo 475787 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B2297261 : Blo 475787 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B2428379 : Blo 475787 2428379 := bstep (se 1 (by rfl) ⟨1821284, by rfl⟩ : syracuseStep 2428379 = 3642569) B3642569
theorem B3051047 : Blo 475787 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B1609415 : Blo 475787 1609415 := bstep (se 1 (by rfl) ⟨1207061, by rfl⟩ : syracuseStep 1609415 = 2414123) B2414123
theorem B724729 : Blo 475787 724729 := bstep (se 2 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 724729 = 543547) B543547
theorem B2428865 : Blo 475787 2428865 := bstep (se 2 (by rfl) ⟨910824, by rfl⟩ : syracuseStep 2428865 = 1821649) B1821649
theorem B1118215 : Blo 475787 1118215 := bstep (se 1 (by rfl) ⟨838661, by rfl⟩ : syracuseStep 1118215 = 1677323) B1677323
theorem B1806583 : Blo 475787 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B1085687 : Blo 475787 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B2036029 : Blo 475787 2036029 := bstep (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) B763511
theorem B1806857 : Blo 475787 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B1806887 : Blo 475787 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B1610279 : Blo 475787 1610279 := bstep (se 1 (by rfl) ⟨1207709, by rfl⟩ : syracuseStep 1610279 = 2415419) B2415419
theorem B1610387 : Blo 475787 1610387 := bstep (se 1 (by rfl) ⟨1207790, by rfl⟩ : syracuseStep 1610387 = 2415581) B2415581
theorem B2724637 : Blo 475787 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B31822627 : Blo 475787 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B6099785 : Blo 475787 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1610603 : Blo 475787 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B1610657 : Blo 475787 1610657 := bstep (se 2 (by rfl) ⟨603996, by rfl⟩ : syracuseStep 1610657 = 1207993) B1207993
theorem B2954393 : Blo 475787 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1807555 : Blo 475787 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B922823 : Blo 475787 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B1807859 : Blo 475787 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B1611251 : Blo 475787 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B857999 : Blo 475787 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B1808315 : Blo 475787 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B1611791 : Blo 475787 1611791 := bstep (se 1 (by rfl) ⟨1208843, by rfl⟩ : syracuseStep 1611791 = 2417687) B2417687
theorem B3446873 : Blo 475787 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B858475 : Blo 475787 858475 := bstep (se 1 (by rfl) ⟨643856, by rfl⟩ : syracuseStep 858475 = 1287713) B1287713
theorem B14686595 : Blo 475787 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B1612385 : Blo 475787 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B5085881 : Blo 475787 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B1088569 : Blo 475787 1088569 := bstep (se 2 (by rfl) ⟨408213, by rfl⟩ : syracuseStep 1088569 = 816427) B816427
theorem B728425 : Blo 475787 728425 := bstep (se 2 (by rfl) ⟨273159, by rfl⟩ : syracuseStep 728425 = 546319) B546319
theorem B1613843 : Blo 475787 1613843 := bstep (se 1 (by rfl) ⟨1210382, by rfl⟩ : syracuseStep 1613843 = 2420765) B2420765
theorem B1810775 : Blo 475787 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B1614167 : Blo 475787 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B3875759 : Blo 475787 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B2729011 : Blo 475787 2729011 := bstep (se 1 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 2729011 = 4093517) B4093517
theorem B1615247 : Blo 475787 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B2172379 : Blo 475787 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B4597211 : Blo 475787 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B1615571 : Blo 475787 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B4073561 : Blo 475787 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B6203699 : Blo 475787 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B764473 : Blo 475787 764473 := bstep (se 2 (by rfl) ⟨286677, by rfl⟩ : syracuseStep 764473 = 573355) B573355
theorem B3058505 : Blo 475787 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B1616759 : Blo 475787 1616759 := bstep (se 1 (by rfl) ⟨1212569, by rfl⟩ : syracuseStep 1616759 = 2425139) B2425139
theorem B1616975 : Blo 475787 1616975 := bstep (se 1 (by rfl) ⟨1212731, by rfl⟩ : syracuseStep 1616975 = 2425463) B2425463
theorem B535675 : Blo 475787 535675 := bstep (se 1 (by rfl) ⟨401756, by rfl⟩ : syracuseStep 535675 = 803513) B803513
theorem B1813661 : Blo 475787 1813661 := bstep (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) B680123
theorem B2174147 : Blo 475787 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B2305219 : Blo 475787 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B1617353 : Blo 475787 1617353 := bstep (se 2 (by rfl) ⟨606507, by rfl⟩ : syracuseStep 1617353 = 1213015) B1213015
theorem B536143 : Blo 475787 536143 := bstep (se 1 (by rfl) ⟨402107, by rfl⟩ : syracuseStep 536143 = 804215) B804215
theorem B1617623 : Blo 475787 1617623 := bstep (se 1 (by rfl) ⟨1213217, by rfl⟩ : syracuseStep 1617623 = 2426435) B2426435
theorem B1814345 : Blo 475787 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B1617839 : Blo 475787 1617839 := bstep (se 1 (by rfl) ⟨1213379, by rfl⟩ : syracuseStep 1617839 = 2426759) B2426759
theorem B536539 : Blo 475787 536539 := bstep (se 1 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 536539 = 804809) B804809
theorem B7385165 : Blo 475787 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B2044061 : Blo 475787 2044061 := bstep (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) B766523
theorem B602311 : Blo 475787 602311 := bstep (se 1 (by rfl) ⟨451733, by rfl⟩ : syracuseStep 602311 = 903467) B903467
theorem B1814845 : Blo 475787 1814845 := bstep (se 3 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 1814845 = 680567) B680567
theorem B3912065 : Blo 475787 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B537007 : Blo 475787 537007 := bstep (se 1 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 537007 = 805511) B805511
theorem B1356385 : Blo 475787 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B537439 : Blo 475787 537439 := bstep (se 1 (by rfl) ⟨403079, by rfl⟩ : syracuseStep 537439 = 806159) B806159
theorem B14398361 : Blo 475787 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B897953 : Blo 475787 897953 := bstep (se 2 (by rfl) ⟨336732, by rfl⟩ : syracuseStep 897953 = 673465) B673465
theorem B603055 : Blo 475787 603055 := bstep (se 1 (by rfl) ⟨452291, by rfl⟩ : syracuseStep 603055 = 904583) B904583
theorem B5452919 : Blo 475787 5452919 := bstep (se 1 (by rfl) ⟨4089689, by rfl⟩ : syracuseStep 5452919 = 8179379) B8179379
theorem B537799 : Blo 475787 537799 := bstep (se 1 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 537799 = 806699) B806699
theorem B767407 : Blo 475787 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B767497 : Blo 475787 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B5420843 : Blo 475787 5420843 := bstep (se 1 (by rfl) ⟨4065632, by rfl⟩ : syracuseStep 5420843 = 8131265) B8131265
theorem B1816577 : Blo 475787 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B1357843 : Blo 475787 1357843 := bstep (se 1 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 1357843 = 2036765) B2036765
theorem B604199 : Blo 475787 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B538663 : Blo 475787 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B604523 : Blo 475787 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B3684761 : Blo 475787 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B1719215 : Blo 475787 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B1162171 : Blo 475787 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B605819 : Blo 475787 605819 := bstep (se 1 (by rfl) ⟨454364, by rfl⟩ : syracuseStep 605819 = 908729) B908729
theorem B1818247 : Blo 475787 1818247 := bstep (se 1 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 1818247 = 2727371) B2727371
theorem B3686087 : Blo 475787 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B1359575 : Blo 475787 1359575 := bstep (se 1 (by rfl) ⟨1019681, by rfl⟩ : syracuseStep 1359575 = 2039363) B2039363
theorem B1359791 : Blo 475787 1359791 := bstep (se 1 (by rfl) ⟨1019843, by rfl⟩ : syracuseStep 1359791 = 2039687) B2039687
theorem B1228727 : Blo 475787 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B1818551 : Blo 475787 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B6864911 : Blo 475787 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B4079645 : Blo 475787 4079645 := bstep (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) B1529867
theorem B802939 : Blo 475787 802939 := bstep (se 1 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 802939 = 1204409) B1204409
theorem B11583755 : Blo 475787 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B3457367 : Blo 475787 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B3064169 : Blo 475787 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B6209921 : Blo 475787 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B3064193 : Blo 475787 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B967099 : Blo 475787 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B574075 : Blo 475787 574075 := bstep (se 1 (by rfl) ⟨430556, by rfl⟩ : syracuseStep 574075 = 861113) B861113
theorem B475823 : Blo 475787 475823 := bstep (se 1 (by rfl) ⟨356867, by rfl⟩ : syracuseStep 475823 = 713735) B713735
theorem B475847 : Blo 475787 475847 := bstep (se 1 (by rfl) ⟨356885, by rfl⟩ : syracuseStep 475847 = 713771) B713771
theorem B475867 : Blo 475787 475867 := bstep (se 1 (by rfl) ⟨356900, by rfl⟩ : syracuseStep 475867 = 713801) B713801
theorem B1360633 : Blo 475787 1360633 := bstep (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) B1020475
theorem B475943 : Blo 475787 475943 := bstep (se 1 (by rfl) ⟨356957, by rfl⟩ : syracuseStep 475943 = 713915) B713915
theorem B475983 : Blo 475787 475983 := bstep (se 1 (by rfl) ⟨356987, by rfl⟩ : syracuseStep 475983 = 713975) B713975
theorem B475999 : Blo 475787 475999 := bstep (se 1 (by rfl) ⟨356999, by rfl⟩ : syracuseStep 475999 = 713999) B713999
theorem B476027 : Blo 475787 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B476079 : Blo 475787 476079 := bstep (se 1 (by rfl) ⟨357059, by rfl⟩ : syracuseStep 476079 = 714119) B714119
theorem B476103 : Blo 475787 476103 := bstep (se 1 (by rfl) ⟨357077, by rfl⟩ : syracuseStep 476103 = 714155) B714155
theorem B476123 : Blo 475787 476123 := bstep (se 1 (by rfl) ⟨357092, by rfl⟩ : syracuseStep 476123 = 714185) B714185
theorem B803803 : Blo 475787 803803 := bstep (se 1 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 803803 = 1205705) B1205705
theorem B476199 : Blo 475787 476199 := bstep (se 1 (by rfl) ⟨357149, by rfl⟩ : syracuseStep 476199 = 714299) B714299
theorem B1819705 : Blo 475787 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B476239 : Blo 475787 476239 := bstep (se 1 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 476239 = 714359) B714359
theorem B1360975 : Blo 475787 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B476255 : Blo 475787 476255 := bstep (se 1 (by rfl) ⟨357191, by rfl⟩ : syracuseStep 476255 = 714383) B714383
theorem B476283 : Blo 475787 476283 := bstep (se 1 (by rfl) ⟨357212, by rfl⟩ : syracuseStep 476283 = 714425) B714425
theorem B476335 : Blo 475787 476335 := bstep (se 1 (by rfl) ⟨357251, by rfl⟩ : syracuseStep 476335 = 714503) B714503
theorem B476359 : Blo 475787 476359 := bstep (se 1 (by rfl) ⟨357269, by rfl⟩ : syracuseStep 476359 = 714539) B714539
theorem B476379 : Blo 475787 476379 := bstep (se 1 (by rfl) ⟨357284, by rfl⟩ : syracuseStep 476379 = 714569) B714569
theorem B1721591 : Blo 475787 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B3327247 : Blo 475787 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B476455 : Blo 475787 476455 := bstep (se 1 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 476455 = 714683) B714683
theorem B476495 : Blo 475787 476495 := bstep (se 1 (by rfl) ⟨357371, by rfl⟩ : syracuseStep 476495 = 714743) B714743
theorem B476511 : Blo 475787 476511 := bstep (se 1 (by rfl) ⟨357383, by rfl⟩ : syracuseStep 476511 = 714767) B714767
theorem B1820009 : Blo 475787 1820009 := bstep (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) B1365007
theorem B476539 : Blo 475787 476539 := bstep (se 1 (by rfl) ⟨357404, by rfl⟩ : syracuseStep 476539 = 714809) B714809
theorem B476591 : Blo 475787 476591 := bstep (se 1 (by rfl) ⟨357443, by rfl⟩ : syracuseStep 476591 = 714887) B714887
theorem B476615 : Blo 475787 476615 := bstep (se 1 (by rfl) ⟨357461, by rfl⟩ : syracuseStep 476615 = 714923) B714923
theorem B476635 : Blo 475787 476635 := bstep (se 1 (by rfl) ⟨357476, by rfl⟩ : syracuseStep 476635 = 714953) B714953
theorem B476711 : Blo 475787 476711 := bstep (se 1 (by rfl) ⟨357533, by rfl⟩ : syracuseStep 476711 = 715067) B715067
theorem B804431 : Blo 475787 804431 := bstep (se 1 (by rfl) ⟨603323, by rfl⟩ : syracuseStep 804431 = 1206647) B1206647
theorem B476751 : Blo 475787 476751 := bstep (se 1 (by rfl) ⟨357563, by rfl⟩ : syracuseStep 476751 = 715127) B715127
theorem B476767 : Blo 475787 476767 := bstep (se 1 (by rfl) ⟨357575, by rfl⟩ : syracuseStep 476767 = 715151) B715151
theorem B476795 : Blo 475787 476795 := bstep (se 1 (by rfl) ⟨357596, by rfl⟩ : syracuseStep 476795 = 715193) B715193
theorem B1295995 : Blo 475787 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B968363 : Blo 475787 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B476847 : Blo 475787 476847 := bstep (se 1 (by rfl) ⟨357635, by rfl⟩ : syracuseStep 476847 = 715271) B715271
theorem B476871 : Blo 475787 476871 := bstep (se 1 (by rfl) ⟨357653, by rfl⟩ : syracuseStep 476871 = 715307) B715307
theorem B8308439 : Blo 475787 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B476891 : Blo 475787 476891 := bstep (se 1 (by rfl) ⟨357668, by rfl⟩ : syracuseStep 476891 = 715337) B715337
theorem B476967 : Blo 475787 476967 := bstep (se 1 (by rfl) ⟨357725, by rfl⟩ : syracuseStep 476967 = 715451) B715451
theorem B477007 : Blo 475787 477007 := bstep (se 1 (by rfl) ⟨357755, by rfl⟩ : syracuseStep 477007 = 715511) B715511
theorem B477023 : Blo 475787 477023 := bstep (se 1 (by rfl) ⟨357767, by rfl⟩ : syracuseStep 477023 = 715535) B715535
theorem B477051 : Blo 475787 477051 := bstep (se 1 (by rfl) ⟨357788, by rfl⟩ : syracuseStep 477051 = 715577) B715577
theorem B477103 : Blo 475787 477103 := bstep (se 1 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 477103 = 715655) B715655
theorem B477127 : Blo 475787 477127 := bstep (se 1 (by rfl) ⟨357845, by rfl⟩ : syracuseStep 477127 = 715691) B715691
theorem B3065809 : Blo 475787 3065809 := bstep (se 2 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 3065809 = 2299357) B2299357
theorem B477147 : Blo 475787 477147 := bstep (se 1 (by rfl) ⟨357860, by rfl⟩ : syracuseStep 477147 = 715721) B715721
theorem B477223 : Blo 475787 477223 := bstep (se 1 (by rfl) ⟨357917, by rfl⟩ : syracuseStep 477223 = 715835) B715835
theorem B477263 : Blo 475787 477263 := bstep (se 1 (by rfl) ⟨357947, by rfl⟩ : syracuseStep 477263 = 715895) B715895
theorem B477279 : Blo 475787 477279 := bstep (se 1 (by rfl) ⟨357959, by rfl⟩ : syracuseStep 477279 = 715919) B715919
theorem B477307 : Blo 475787 477307 := bstep (se 1 (by rfl) ⟨357980, by rfl⟩ : syracuseStep 477307 = 715961) B715961
theorem B1362091 : Blo 475787 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B477359 : Blo 475787 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B477383 : Blo 475787 477383 := bstep (se 1 (by rfl) ⟨358037, by rfl⟩ : syracuseStep 477383 = 716075) B716075
theorem B968915 : Blo 475787 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B477403 : Blo 475787 477403 := bstep (se 1 (by rfl) ⟨358052, by rfl⟩ : syracuseStep 477403 = 716105) B716105
theorem B477479 : Blo 475787 477479 := bstep (se 1 (by rfl) ⟨358109, by rfl⟩ : syracuseStep 477479 = 716219) B716219
theorem B477519 : Blo 475787 477519 := bstep (se 1 (by rfl) ⟨358139, by rfl⟩ : syracuseStep 477519 = 716279) B716279
theorem B477535 : Blo 475787 477535 := bstep (se 1 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 477535 = 716303) B716303
theorem B575839 : Blo 475787 575839 := bstep (se 1 (by rfl) ⟨431879, by rfl⟩ : syracuseStep 575839 = 863759) B863759
theorem B477563 : Blo 475787 477563 := bstep (se 1 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 477563 = 716345) B716345
theorem B805295 : Blo 475787 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B477615 : Blo 475787 477615 := bstep (se 1 (by rfl) ⟨358211, by rfl⟩ : syracuseStep 477615 = 716423) B716423
theorem B903611 : Blo 475787 903611 := bstep (se 1 (by rfl) ⟨677708, by rfl⟩ : syracuseStep 903611 = 1355417) B1355417
theorem B477639 : Blo 475787 477639 := bstep (se 1 (by rfl) ⟨358229, by rfl⟩ : syracuseStep 477639 = 716459) B716459
theorem B477659 : Blo 475787 477659 := bstep (se 1 (by rfl) ⟨358244, by rfl⟩ : syracuseStep 477659 = 716489) B716489
theorem B477735 : Blo 475787 477735 := bstep (se 1 (by rfl) ⟨358301, by rfl⟩ : syracuseStep 477735 = 716603) B716603
theorem B477775 : Blo 475787 477775 := bstep (se 1 (by rfl) ⟨358331, by rfl⟩ : syracuseStep 477775 = 716663) B716663
theorem B477791 : Blo 475787 477791 := bstep (se 1 (by rfl) ⟨358343, by rfl⟩ : syracuseStep 477791 = 716687) B716687
theorem B1722977 : Blo 475787 1722977 := bstep (se 2 (by rfl) ⟨646116, by rfl⟩ : syracuseStep 1722977 = 1292233) B1292233
theorem B477819 : Blo 475787 477819 := bstep (se 1 (by rfl) ⟨358364, by rfl⟩ : syracuseStep 477819 = 716729) B716729
theorem B477871 : Blo 475787 477871 := bstep (se 1 (by rfl) ⟨358403, by rfl⟩ : syracuseStep 477871 = 716807) B716807
theorem B477895 : Blo 475787 477895 := bstep (se 1 (by rfl) ⟨358421, by rfl⟩ : syracuseStep 477895 = 716843) B716843
theorem B2214611 : Blo 475787 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B477915 : Blo 475787 477915 := bstep (se 1 (by rfl) ⟨358436, by rfl⟩ : syracuseStep 477915 = 716873) B716873
theorem B3066653 : Blo 475787 3066653 := bstep (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) B1149995
theorem B477991 : Blo 475787 477991 := bstep (se 1 (by rfl) ⟨358493, by rfl⟩ : syracuseStep 477991 = 716987) B716987
theorem B478031 : Blo 475787 478031 := bstep (se 1 (by rfl) ⟨358523, by rfl⟩ : syracuseStep 478031 = 717047) B717047
theorem B805727 : Blo 475787 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B478047 : Blo 475787 478047 := bstep (se 1 (by rfl) ⟨358535, by rfl⟩ : syracuseStep 478047 = 717071) B717071
theorem B478075 : Blo 475787 478075 := bstep (se 1 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 478075 = 717113) B717113
theorem B904097 : Blo 475787 904097 := bstep (se 2 (by rfl) ⟨339036, by rfl⟩ : syracuseStep 904097 = 678073) B678073
theorem B478127 : Blo 475787 478127 := bstep (se 1 (by rfl) ⟨358595, by rfl⟩ : syracuseStep 478127 = 717191) B717191
theorem B478151 : Blo 475787 478151 := bstep (se 1 (by rfl) ⟨358613, by rfl⟩ : syracuseStep 478151 = 717227) B717227
theorem B478171 : Blo 475787 478171 := bstep (se 1 (by rfl) ⟨358628, by rfl⟩ : syracuseStep 478171 = 717257) B717257
theorem B478247 : Blo 475787 478247 := bstep (se 1 (by rfl) ⟨358685, by rfl⟩ : syracuseStep 478247 = 717371) B717371
theorem B478287 : Blo 475787 478287 := bstep (se 1 (by rfl) ⟨358715, by rfl⟩ : syracuseStep 478287 = 717431) B717431
theorem B478303 : Blo 475787 478303 := bstep (se 1 (by rfl) ⟨358727, by rfl⟩ : syracuseStep 478303 = 717455) B717455
theorem B478331 : Blo 475787 478331 := bstep (se 1 (by rfl) ⟨358748, by rfl⟩ : syracuseStep 478331 = 717497) B717497
theorem B478383 : Blo 475787 478383 := bstep (se 1 (by rfl) ⟨358787, by rfl⟩ : syracuseStep 478383 = 717575) B717575
theorem B478407 : Blo 475787 478407 := bstep (se 1 (by rfl) ⟨358805, by rfl⟩ : syracuseStep 478407 = 717611) B717611
theorem B478427 : Blo 475787 478427 := bstep (se 1 (by rfl) ⟨358820, by rfl⟩ : syracuseStep 478427 = 717641) B717641
theorem B904439 : Blo 475787 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B478503 : Blo 475787 478503 := bstep (se 1 (by rfl) ⟨358877, by rfl⟩ : syracuseStep 478503 = 717755) B717755
theorem B478543 : Blo 475787 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B478559 : Blo 475787 478559 := bstep (se 1 (by rfl) ⟨358919, by rfl⟩ : syracuseStep 478559 = 717839) B717839
theorem B478587 : Blo 475787 478587 := bstep (se 1 (by rfl) ⟨358940, by rfl⟩ : syracuseStep 478587 = 717881) B717881
theorem B806287 : Blo 475787 806287 := bstep (se 1 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 806287 = 1209431) B1209431
theorem B478639 : Blo 475787 478639 := bstep (se 1 (by rfl) ⟨358979, by rfl⟩ : syracuseStep 478639 = 717959) B717959
theorem B478663 : Blo 475787 478663 := bstep (se 1 (by rfl) ⟨358997, by rfl⟩ : syracuseStep 478663 = 717995) B717995
theorem B478683 : Blo 475787 478683 := bstep (se 1 (by rfl) ⟨359012, by rfl⟩ : syracuseStep 478683 = 718025) B718025
theorem B5426675 : Blo 475787 5426675 := bstep (se 1 (by rfl) ⟨4070006, by rfl⟩ : syracuseStep 5426675 = 8140013) B8140013
theorem B478759 : Blo 475787 478759 := bstep (se 1 (by rfl) ⟨359069, by rfl⟩ : syracuseStep 478759 = 718139) B718139
theorem B6868547 : Blo 475787 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B478799 : Blo 475787 478799 := bstep (se 1 (by rfl) ⟨359099, by rfl⟩ : syracuseStep 478799 = 718199) B718199
theorem B478815 : Blo 475787 478815 := bstep (se 1 (by rfl) ⟨359111, by rfl⟩ : syracuseStep 478815 = 718223) B718223
theorem B48385637 : Blo 475787 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B478843 : Blo 475787 478843 := bstep (se 1 (by rfl) ⟨359132, by rfl⟩ : syracuseStep 478843 = 718265) B718265
theorem B3624587 : Blo 475787 3624587 := bstep (se 1 (by rfl) ⟨2718440, by rfl⟩ : syracuseStep 3624587 = 5436881) B5436881
theorem B2412179 : Blo 475787 2412179 := bstep (se 1 (by rfl) ⟨1809134, by rfl⟩ : syracuseStep 2412179 = 3618269) B3618269
theorem B478895 : Blo 475787 478895 := bstep (se 1 (by rfl) ⟨359171, by rfl⟩ : syracuseStep 478895 = 718343) B718343
theorem B478919 : Blo 475787 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B478939 : Blo 475787 478939 := bstep (se 1 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 478939 = 718409) B718409
theorem B479015 : Blo 475787 479015 := bstep (se 1 (by rfl) ⟨359261, by rfl⟩ : syracuseStep 479015 = 718523) B718523
theorem B479055 : Blo 475787 479055 := bstep (se 1 (by rfl) ⟨359291, by rfl⟩ : syracuseStep 479055 = 718583) B718583
theorem B479071 : Blo 475787 479071 := bstep (se 1 (by rfl) ⟨359303, by rfl⟩ : syracuseStep 479071 = 718607) B718607
theorem B970601 : Blo 475787 970601 := bstep (se 2 (by rfl) ⟨363975, by rfl⟩ : syracuseStep 970601 = 727951) B727951
theorem B479099 : Blo 475787 479099 := bstep (se 1 (by rfl) ⟨359324, by rfl⟩ : syracuseStep 479099 = 718649) B718649
theorem B479151 : Blo 475787 479151 := bstep (se 1 (by rfl) ⟨359363, by rfl⟩ : syracuseStep 479151 = 718727) B718727
theorem B479175 : Blo 475787 479175 := bstep (se 1 (by rfl) ⟨359381, by rfl⟩ : syracuseStep 479175 = 718763) B718763
theorem B479195 : Blo 475787 479195 := bstep (se 1 (by rfl) ⟨359396, by rfl⟩ : syracuseStep 479195 = 718793) B718793
theorem B511963 : Blo 475787 511963 := bstep (se 1 (by rfl) ⟨383972, by rfl⟩ : syracuseStep 511963 = 767945) B767945
theorem B479271 : Blo 475787 479271 := bstep (se 1 (by rfl) ⟨359453, by rfl⟩ : syracuseStep 479271 = 718907) B718907
theorem B806969 : Blo 475787 806969 := bstep (se 2 (by rfl) ⟨302613, by rfl⟩ : syracuseStep 806969 = 605227) B605227
theorem B479311 : Blo 475787 479311 := bstep (se 1 (by rfl) ⟨359483, by rfl⟩ : syracuseStep 479311 = 718967) B718967
theorem B5820497 : Blo 475787 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B479327 : Blo 475787 479327 := bstep (se 1 (by rfl) ⟨359495, by rfl⟩ : syracuseStep 479327 = 718991) B718991
theorem B479355 : Blo 475787 479355 := bstep (se 1 (by rfl) ⟨359516, by rfl⟩ : syracuseStep 479355 = 719033) B719033
theorem B479407 : Blo 475787 479407 := bstep (se 1 (by rfl) ⟨359555, by rfl⟩ : syracuseStep 479407 = 719111) B719111
theorem B479431 : Blo 475787 479431 := bstep (se 1 (by rfl) ⟨359573, by rfl⟩ : syracuseStep 479431 = 719147) B719147
theorem B22106317 : Blo 475787 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B479451 : Blo 475787 479451 := bstep (se 1 (by rfl) ⟨359588, by rfl⟩ : syracuseStep 479451 = 719177) B719177
theorem B479527 : Blo 475787 479527 := bstep (se 1 (by rfl) ⟨359645, by rfl⟩ : syracuseStep 479527 = 719291) B719291
theorem B479567 : Blo 475787 479567 := bstep (se 1 (by rfl) ⟨359675, by rfl⟩ : syracuseStep 479567 = 719351) B719351
theorem B479583 : Blo 475787 479583 := bstep (se 1 (by rfl) ⟨359687, by rfl⟩ : syracuseStep 479583 = 719375) B719375
theorem B479611 : Blo 475787 479611 := bstep (se 1 (by rfl) ⟨359708, by rfl⟩ : syracuseStep 479611 = 719417) B719417
theorem B479663 : Blo 475787 479663 := bstep (se 1 (by rfl) ⟨359747, by rfl⟩ : syracuseStep 479663 = 719495) B719495
theorem B479687 : Blo 475787 479687 := bstep (se 1 (by rfl) ⟨359765, by rfl⟩ : syracuseStep 479687 = 719531) B719531
theorem B479707 : Blo 475787 479707 := bstep (se 1 (by rfl) ⟨359780, by rfl⟩ : syracuseStep 479707 = 719561) B719561
theorem B905737 : Blo 475787 905737 := bstep (se 2 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 905737 = 679303) B679303
theorem B479783 : Blo 475787 479783 := bstep (se 1 (by rfl) ⟨359837, by rfl⟩ : syracuseStep 479783 = 719675) B719675
theorem B1036999 : Blo 475787 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B807671 : Blo 475787 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B10343213 : Blo 475787 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B906079 : Blo 475787 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B1725455 : Blo 475787 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B808015 : Blo 475787 808015 := bstep (se 1 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 808015 = 1212023) B1212023
theorem B808265 : Blo 475787 808265 := bstep (se 2 (by rfl) ⟨303099, by rfl⟩ : syracuseStep 808265 = 606199) B606199
theorem B546383 : Blo 475787 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B1529533 : Blo 475787 1529533 := bstep (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) B573575
theorem B808697 : Blo 475787 808697 := bstep (se 2 (by rfl) ⟨303261, by rfl⟩ : syracuseStep 808697 = 606523) B606523
theorem B2447147 : Blo 475787 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B677737 : Blo 475787 677737 := bstep (se 2 (by rfl) ⟨254151, by rfl⟩ : syracuseStep 677737 = 508303) B508303
theorem B808879 : Blo 475787 808879 := bstep (se 1 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 808879 = 1213319) B1213319
theorem B1071035 : Blo 475787 1071035 := bstep (se 1 (by rfl) ⟨803276, by rfl⟩ : syracuseStep 1071035 = 1606553) B1606553
theorem B907195 : Blo 475787 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B35739589 : Blo 475787 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B907271 : Blo 475787 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B2185223 : Blo 475787 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B808967 : Blo 475787 808967 := bstep (se 1 (by rfl) ⟨606725, by rfl⟩ : syracuseStep 808967 = 1213451) B1213451
theorem B1071161 : Blo 475787 1071161 := bstep (se 2 (by rfl) ⟨401685, by rfl⟩ : syracuseStep 1071161 = 803371) B803371
theorem B5429591 : Blo 475787 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B809311 : Blo 475787 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B1071503 : Blo 475787 1071503 := bstep (se 1 (by rfl) ⟨803627, by rfl⟩ : syracuseStep 1071503 = 1607255) B1607255
theorem B907681 : Blo 475787 907681 := bstep (se 2 (by rfl) ⟨340380, by rfl⟩ : syracuseStep 907681 = 680761) B680761
theorem B809399 : Blo 475787 809399 := bstep (se 1 (by rfl) ⟨607049, by rfl⟩ : syracuseStep 809399 = 1214099) B1214099
theorem B580135 : Blo 475787 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B1071827 : Blo 475787 1071827 := bstep (se 1 (by rfl) ⟨803870, by rfl⟩ : syracuseStep 1071827 = 1607741) B1607741
theorem B908023 : Blo 475787 908023 := bstep (se 1 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 908023 = 1362035) B1362035
theorem B908327 : Blo 475787 908327 := bstep (se 1 (by rfl) ⟨681245, by rfl⟩ : syracuseStep 908327 = 1362491) B1362491
theorem B1531379 : Blo 475787 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B1957499 : Blo 475787 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B1072763 : Blo 475787 1072763 := bstep (se 1 (by rfl) ⟨804572, by rfl⟩ : syracuseStep 1072763 = 1609145) B1609145
theorem B3071627 : Blo 475787 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B1859219 : Blo 475787 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B1728209 : Blo 475787 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B1072889 : Blo 475787 1072889 := bstep (se 2 (by rfl) ⟨402333, by rfl⟩ : syracuseStep 1072889 = 804667) B804667
theorem B26828597 : Blo 475787 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B3628961 : Blo 475787 3628961 := bstep (se 2 (by rfl) ⟨1360860, by rfl⟩ : syracuseStep 3628961 = 2721721) B2721721
theorem B1073159 : Blo 475787 1073159 := bstep (se 1 (by rfl) ⟨804869, by rfl⟩ : syracuseStep 1073159 = 1609739) B1609739
theorem B1073231 : Blo 475787 1073231 := bstep (se 1 (by rfl) ⟨804923, by rfl⟩ : syracuseStep 1073231 = 1609847) B1609847
theorem B680015 : Blo 475787 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B83845205 : Blo 475787 83845205 := bstep (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) B982561
theorem B1073627 : Blo 475787 1073627 := bstep (se 1 (by rfl) ⟨805220, by rfl⟩ : syracuseStep 1073627 = 1610441) B1610441
theorem B6644227 : Blo 475787 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B3269321 : Blo 475787 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B2417363 : Blo 475787 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B910187 : Blo 475787 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B1074095 : Blo 475787 1074095 := bstep (se 1 (by rfl) ⟨805571, by rfl⟩ : syracuseStep 1074095 = 1611143) B1611143
theorem B713807 : Blo 475787 713807 := bstep (se 1 (by rfl) ⟨535355, by rfl⟩ : syracuseStep 713807 = 1070711) B1070711
theorem B910415 : Blo 475787 910415 := bstep (se 1 (by rfl) ⟨682811, by rfl⟩ : syracuseStep 910415 = 1365623) B1365623
theorem B1074347 : Blo 475787 1074347 := bstep (se 1 (by rfl) ⟨805760, by rfl⟩ : syracuseStep 1074347 = 1611521) B1611521
theorem B713927 : Blo 475787 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B714089 : Blo 475787 714089 := bstep (se 2 (by rfl) ⟨267783, by rfl⟩ : syracuseStep 714089 = 535567) B535567
theorem B714167 : Blo 475787 714167 := bstep (se 1 (by rfl) ⟨535625, by rfl⟩ : syracuseStep 714167 = 1071251) B1071251
theorem B714203 : Blo 475787 714203 := bstep (se 1 (by rfl) ⟨535652, by rfl⟩ : syracuseStep 714203 = 1071305) B1071305
theorem B1074887 : Blo 475787 1074887 := bstep (se 1 (by rfl) ⟨806165, by rfl⟩ : syracuseStep 1074887 = 1612331) B1612331
theorem B1533725 : Blo 475787 1533725 := bstep (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) B575147
theorem B714671 : Blo 475787 714671 := bstep (se 1 (by rfl) ⟨536003, by rfl⟩ : syracuseStep 714671 = 1072007) B1072007
theorem B1206191 : Blo 475787 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B714761 : Blo 475787 714761 := bstep (se 2 (by rfl) ⟨268035, by rfl⟩ : syracuseStep 714761 = 536071) B536071
theorem B714791 : Blo 475787 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B714875 : Blo 475787 714875 := bstep (se 1 (by rfl) ⟨536156, by rfl⟩ : syracuseStep 714875 = 1072313) B1072313
theorem B715001 : Blo 475787 715001 := bstep (se 2 (by rfl) ⟨268125, by rfl⟩ : syracuseStep 715001 = 536251) B536251
theorem B12904753 : Blo 475787 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B4581683 : Blo 475787 4581683 := bstep (se 1 (by rfl) ⟨3436262, by rfl⟩ : syracuseStep 4581683 = 6872525) B6872525
theorem B3107159 : Blo 475787 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B715103 : Blo 475787 715103 := bstep (se 1 (by rfl) ⟨536327, by rfl⟩ : syracuseStep 715103 = 1072655) B1072655
theorem B715115 : Blo 475787 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B1206809 : Blo 475787 1206809 := bstep (se 2 (by rfl) ⟨452553, by rfl⟩ : syracuseStep 1206809 = 905107) B905107
theorem B1075751 : Blo 475787 1075751 := bstep (se 1 (by rfl) ⟨806813, by rfl⟩ : syracuseStep 1075751 = 1613627) B1613627
theorem B715343 : Blo 475787 715343 := bstep (se 1 (by rfl) ⟨536507, by rfl⟩ : syracuseStep 715343 = 1073015) B1073015
theorem B715463 : Blo 475787 715463 := bstep (se 1 (by rfl) ⟨536597, by rfl⟩ : syracuseStep 715463 = 1073195) B1073195
theorem B715625 : Blo 475787 715625 := bstep (se 2 (by rfl) ⟨268359, by rfl⟩ : syracuseStep 715625 = 536719) B536719
theorem B1076075 : Blo 475787 1076075 := bstep (se 1 (by rfl) ⟨807056, by rfl⟩ : syracuseStep 1076075 = 1614113) B1614113
theorem B1076129 : Blo 475787 1076129 := bstep (se 2 (by rfl) ⟨403548, by rfl⟩ : syracuseStep 1076129 = 807097) B807097
theorem B2419631 : Blo 475787 2419631 := bstep (se 1 (by rfl) ⟨1814723, by rfl⟩ : syracuseStep 2419631 = 3629447) B3629447
theorem B486319 : Blo 475787 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B715703 : Blo 475787 715703 := bstep (se 1 (by rfl) ⟨536777, by rfl⟩ : syracuseStep 715703 = 1073555) B1073555
theorem B715739 : Blo 475787 715739 := bstep (se 1 (by rfl) ⟨536804, by rfl⟩ : syracuseStep 715739 = 1073609) B1073609
theorem B1076471 : Blo 475787 1076471 := bstep (se 1 (by rfl) ⟨807353, by rfl⟩ : syracuseStep 1076471 = 1614707) B1614707
theorem B716207 : Blo 475787 716207 := bstep (se 1 (by rfl) ⟨537155, by rfl⟩ : syracuseStep 716207 = 1074311) B1074311
theorem B2584009 : Blo 475787 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B716297 : Blo 475787 716297 := bstep (se 2 (by rfl) ⟨268611, by rfl⟩ : syracuseStep 716297 = 537223) B537223
theorem B716327 : Blo 475787 716327 := bstep (se 1 (by rfl) ⟨537245, by rfl⟩ : syracuseStep 716327 = 1074491) B1074491
theorem B716411 : Blo 475787 716411 := bstep (se 1 (by rfl) ⟨537308, by rfl⟩ : syracuseStep 716411 = 1074617) B1074617
theorem B1634003 : Blo 475787 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B4484845 : Blo 475787 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B716537 : Blo 475787 716537 := bstep (se 2 (by rfl) ⟨268701, by rfl⟩ : syracuseStep 716537 = 537403) B537403
theorem B1077065 : Blo 475787 1077065 := bstep (se 2 (by rfl) ⟨403899, by rfl⟩ : syracuseStep 1077065 = 807799) B807799
theorem B716639 : Blo 475787 716639 := bstep (se 1 (by rfl) ⟨537479, by rfl⟩ : syracuseStep 716639 = 1074959) B1074959
theorem B716651 : Blo 475787 716651 := bstep (se 1 (by rfl) ⟨537488, by rfl⟩ : syracuseStep 716651 = 1074977) B1074977
theorem B716879 : Blo 475787 716879 := bstep (se 1 (by rfl) ⟨537659, by rfl⟩ : syracuseStep 716879 = 1075319) B1075319
theorem B716999 : Blo 475787 716999 := bstep (se 1 (by rfl) ⟨537749, by rfl⟩ : syracuseStep 716999 = 1075499) B1075499
theorem B717161 : Blo 475787 717161 := bstep (se 2 (by rfl) ⟨268935, by rfl⟩ : syracuseStep 717161 = 537871) B537871
theorem B5534081 : Blo 475787 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B881039 : Blo 475787 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B717239 : Blo 475787 717239 := bstep (se 1 (by rfl) ⟨537929, by rfl⟩ : syracuseStep 717239 = 1075859) B1075859
theorem B717275 : Blo 475787 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B2912777 : Blo 475787 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B1077857 : Blo 475787 1077857 := bstep (se 2 (by rfl) ⟨404196, by rfl⟩ : syracuseStep 1077857 = 808393) B808393
theorem B1929851 : Blo 475787 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B717743 : Blo 475787 717743 := bstep (se 1 (by rfl) ⟨538307, by rfl⟩ : syracuseStep 717743 = 1076615) B1076615
theorem B1078199 : Blo 475787 1078199 := bstep (se 1 (by rfl) ⟨808649, by rfl⟩ : syracuseStep 1078199 = 1617299) B1617299
theorem B717833 : Blo 475787 717833 := bstep (se 2 (by rfl) ⟨269187, by rfl⟩ : syracuseStep 717833 = 538375) B538375
theorem B717863 : Blo 475787 717863 := bstep (se 1 (by rfl) ⟨538397, by rfl⟩ : syracuseStep 717863 = 1076795) B1076795
theorem B1209401 : Blo 475787 1209401 := bstep (se 2 (by rfl) ⟨453525, by rfl⟩ : syracuseStep 1209401 = 907051) B907051
theorem B6911041 : Blo 475787 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B717947 : Blo 475787 717947 := bstep (se 1 (by rfl) ⟨538460, by rfl⟩ : syracuseStep 717947 = 1076921) B1076921
theorem B718073 : Blo 475787 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B718175 : Blo 475787 718175 := bstep (se 1 (by rfl) ⟨538631, by rfl⟩ : syracuseStep 718175 = 1077263) B1077263
theorem B718187 : Blo 475787 718187 := bstep (se 1 (by rfl) ⟨538640, by rfl⟩ : syracuseStep 718187 = 1077281) B1077281
theorem B1570291 : Blo 475787 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1078793 : Blo 475787 1078793 := bstep (se 2 (by rfl) ⟨404547, by rfl⟩ : syracuseStep 1078793 = 809095) B809095
theorem B718415 : Blo 475787 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B1144459 : Blo 475787 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B718535 : Blo 475787 718535 := bstep (se 1 (by rfl) ⟨538901, by rfl⟩ : syracuseStep 718535 = 1077803) B1077803
theorem B1079135 : Blo 475787 1079135 := bstep (se 1 (by rfl) ⟨809351, by rfl⟩ : syracuseStep 1079135 = 1618703) B1618703
theorem B718697 : Blo 475787 718697 := bstep (se 2 (by rfl) ⟨269511, by rfl⟩ : syracuseStep 718697 = 539023) B539023
theorem B718775 : Blo 475787 718775 := bstep (se 1 (by rfl) ⟨539081, by rfl⟩ : syracuseStep 718775 = 1078163) B1078163
theorem B718811 : Blo 475787 718811 := bstep (se 1 (by rfl) ⟨539108, by rfl⟩ : syracuseStep 718811 = 1078217) B1078217
theorem B1079315 : Blo 475787 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B719279 : Blo 475787 719279 := bstep (se 1 (by rfl) ⟨539459, by rfl⟩ : syracuseStep 719279 = 1078919) B1078919
theorem B1210889 : Blo 475787 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B719369 : Blo 475787 719369 := bstep (se 2 (by rfl) ⟨269763, by rfl⟩ : syracuseStep 719369 = 539527) B539527
theorem B719399 : Blo 475787 719399 := bstep (se 1 (by rfl) ⟨539549, by rfl⟩ : syracuseStep 719399 = 1079099) B1079099
theorem B719483 : Blo 475787 719483 := bstep (se 1 (by rfl) ⟨539612, by rfl⟩ : syracuseStep 719483 = 1079225) B1079225
theorem B16546481 : Blo 475787 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B719609 : Blo 475787 719609 := bstep (se 2 (by rfl) ⟨269853, by rfl⟩ : syracuseStep 719609 = 539707) B539707
theorem B1145863 : Blo 475787 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B818255 : Blo 475787 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B11599325 : Blo 475787 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B3866251 : Blo 475787 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B1212043 : Blo 475787 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B622279 : Blo 475787 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B2293571 : Blo 475787 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B1212347 : Blo 475787 1212347 := bstep (se 1 (by rfl) ⟨909260, by rfl⟩ : syracuseStep 1212347 = 1818521) B1818521
theorem B2719763 : Blo 475787 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B5963813 : Blo 475787 5963813 := bstep (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) B1118215
theorem B20709593 : Blo 475787 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B13763033 : Blo 475787 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B12255947 : Blo 475787 12255947 := bstep (se 1 (by rfl) ⟨9191960, by rfl⟩ : syracuseStep 12255947 = 18383921) B18383921
theorem B656095 : Blo 475787 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B1147727 : Blo 475787 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B1213339 : Blo 475787 1213339 := bstep (se 1 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 1213339 = 1820009) B1820009
theorem B5538959 : Blo 475787 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B3638681 : Blo 475787 3638681 := bstep (se 2 (by rfl) ⟨1364505, by rfl⟩ : syracuseStep 3638681 = 2729011) B2729011
theorem B2426273 : Blo 475787 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B1148651 : Blo 475787 1148651 := bstep (se 1 (by rfl) ⟨861488, by rfl⟩ : syracuseStep 1148651 = 1722977) B1722977
theorem B1476407 : Blo 475787 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2034031 : Blo 475787 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B2394541 : Blo 475787 2394541 := bstep (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) B897953
theorem B1608119 : Blo 475787 1608119 := bstep (se 1 (by rfl) ⟨1206089, by rfl⟩ : syracuseStep 1608119 = 2412179) B2412179
theorem B723791 : Blo 475787 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B17206337 : Blo 475787 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B4066523 : Blo 475787 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B1150303 : Blo 475787 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B920929 : Blo 475787 920929 := bstep (se 2 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 920929 = 690697) B690697
theorem B1019297 : Blo 475787 1019297 := bstep (se 2 (by rfl) ⟨382236, by rfl⟩ : syracuseStep 1019297 = 764473) B764473
theorem B1969595 : Blo 475787 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B2297915 : Blo 475787 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B3445345 : Blo 475787 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B1020919 : Blo 475787 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B1152139 : Blo 475787 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B1611197 : Blo 475787 1611197 := bstep (se 3 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 1611197 = 604199) B604199
theorem B5805701 : Blo 475787 5805701 := bstep (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) B1088569
theorem B1611575 : Blo 475787 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B1808513 : Blo 475787 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B1382665 : Blo 475787 1382665 := bstep (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) B1036999
theorem B1612061 : Blo 475787 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B1022483 : Blo 475787 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B9214721 : Blo 475787 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B3054455 : Blo 475787 3054455 := bstep (se 1 (by rfl) ⟨2290841, by rfl⟩ : syracuseStep 3054455 = 4581683) B4581683
theorem B4135799 : Blo 475787 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B2071439 : Blo 475787 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B2039003 : Blo 475787 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B1023209 : Blo 475787 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B1613087 : Blo 475787 1613087 := bstep (se 1 (by rfl) ⟨1209815, by rfl⟩ : syracuseStep 1613087 = 2419631) B2419631
theorem B1023329 : Blo 475787 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B1449431 : Blo 475787 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B1089335 : Blo 475787 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B47652785 : Blo 475787 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B1810457 : Blo 475787 1810457 := bstep (se 2 (by rfl) ⟨678921, by rfl⟩ : syracuseStep 1810457 = 1357843) B1357843
theorem B4923443 : Blo 475787 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B1941851 : Blo 475787 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B1286567 : Blo 475787 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B6103781 : Blo 475787 6103781 := bstep (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) B1144459
theorem B3613895 : Blo 475787 3613895 := bstep (se 1 (by rfl) ⟨2710421, by rfl⟩ : syracuseStep 3613895 = 5420843) B5420843
theorem B1549561 : Blo 475787 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B1615517 : Blo 475787 1615517 := bstep (se 3 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 1615517 = 605819) B605819
theorem B5155001 : Blo 475787 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B1616057 : Blo 475787 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B829705 : Blo 475787 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B33499541 : Blo 475787 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B2730469 : Blo 475787 2730469 := bstep (se 4 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 2730469 = 511963) B511963
theorem B2730743 : Blo 475787 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B1813373 : Blo 475787 1813373 := bstep (se 3 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 1813373 = 680015) B680015
theorem B2304911 : Blo 475787 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B2042779 : Blo 475787 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B4139947 : Blo 475787 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B2042795 : Blo 475787 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B1289465 : Blo 475787 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B8858969 : Blo 475787 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B765433 : Blo 475787 765433 := bstep (se 2 (by rfl) ⟨287037, by rfl⟩ : syracuseStep 765433 = 574075) B574075
theorem B1814177 : Blo 475787 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B1617569 : Blo 475787 1617569 := bstep (se 2 (by rfl) ⟨606588, by rfl⟩ : syracuseStep 1617569 = 1213177) B1213177
theorem B536287 : Blo 475787 536287 := bstep (se 1 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 536287 = 804431) B804431
theorem B765703 : Blo 475787 765703 := bstep (se 1 (by rfl) ⟨574277, by rfl⟩ : syracuseStep 765703 = 1148555) B1148555
theorem B1814633 : Blo 475787 1814633 := bstep (se 2 (by rfl) ⟨680487, by rfl⟩ : syracuseStep 1814633 = 1360975) B1360975
theorem B536863 : Blo 475787 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B602407 : Blo 475787 602407 := bstep (se 1 (by rfl) ⟨451805, by rfl⟩ : syracuseStep 602407 = 903611) B903611
theorem B4436329 : Blo 475787 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B1618433 : Blo 475787 1618433 := bstep (se 2 (by rfl) ⟨606912, by rfl⟩ : syracuseStep 1618433 = 1213825) B1213825
theorem B2044435 : Blo 475787 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B537151 : Blo 475787 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B602731 : Blo 475787 602731 := bstep (se 1 (by rfl) ⟨452048, by rfl⟩ : syracuseStep 602731 = 904097) B904097
theorem B2896505 : Blo 475787 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B602959 : Blo 475787 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B1618919 : Blo 475787 1618919 := bstep (se 1 (by rfl) ⟨1214189, by rfl⟩ : syracuseStep 1618919 = 2428379) B2428379
theorem B3617783 : Blo 475787 3617783 := bstep (se 1 (by rfl) ⟨2713337, by rfl⟩ : syracuseStep 3617783 = 5426675) B5426675
theorem B32257091 : Blo 475787 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B1619243 : Blo 475787 1619243 := bstep (se 1 (by rfl) ⟨1214432, by rfl⟩ : syracuseStep 1619243 = 2428865) B2428865
theorem B537979 : Blo 475787 537979 := bstep (se 1 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 537979 = 806969) B806969
theorem B3880331 : Blo 475787 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B1816121 : Blo 475787 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B538447 : Blo 475787 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B6895475 : Blo 475787 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B538843 : Blo 475787 538843 := bstep (se 1 (by rfl) ⟨404132, by rfl⟩ : syracuseStep 538843 = 808265) B808265
theorem B12368305 : Blo 475787 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B539131 : Blo 475787 539131 := bstep (se 1 (by rfl) ⟨404348, by rfl⟩ : syracuseStep 539131 = 808697) B808697
theorem B604847 : Blo 475787 604847 := bstep (se 1 (by rfl) ⟨453635, by rfl⟩ : syracuseStep 604847 = 907271) B907271
theorem B539311 : Blo 475787 539311 := bstep (se 1 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 539311 = 808967) B808967
theorem B1457021 : Blo 475787 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B3619727 : Blo 475787 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B539599 : Blo 475787 539599 := bstep (se 1 (by rfl) ⟨404699, by rfl⟩ : syracuseStep 539599 = 809399) B809399
theorem B3390587 : Blo 475787 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B605551 : Blo 475787 605551 := bstep (se 1 (by rfl) ⟨454163, by rfl⟩ : syracuseStep 605551 = 908327) B908327
theorem B5979793 : Blo 475787 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B966305 : Blo 475787 966305 := bstep (se 2 (by rfl) ⟨362364, by rfl⟩ : syracuseStep 966305 = 724729) B724729
theorem B2047751 : Blo 475787 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B19579117 : Blo 475787 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B803081 : Blo 475787 803081 := bstep (se 2 (by rfl) ⟨301155, by rfl⟩ : syracuseStep 803081 = 602311) B602311
theorem B29475089 : Blo 475787 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B2408777 : Blo 475787 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B2179547 : Blo 475787 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B606791 : Blo 475787 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B475871 : Blo 475787 475871 := bstep (se 1 (by rfl) ⟨356903, by rfl⟩ : syracuseStep 475871 = 713807) B713807
theorem B606943 : Blo 475787 606943 := bstep (se 1 (by rfl) ⟨455207, by rfl⟩ : syracuseStep 606943 = 910415) B910415
theorem B475951 : Blo 475787 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B476059 : Blo 475787 476059 := bstep (se 1 (by rfl) ⟨357044, by rfl⟩ : syracuseStep 476059 = 714089) B714089
theorem B476111 : Blo 475787 476111 := bstep (se 1 (by rfl) ⟨357083, by rfl⟩ : syracuseStep 476111 = 714167) B714167
theorem B476135 : Blo 475787 476135 := bstep (se 1 (by rfl) ⟨357101, by rfl⟩ : syracuseStep 476135 = 714203) B714203
theorem B3064807 : Blo 475787 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B804073 : Blo 475787 804073 := bstep (se 2 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 804073 = 603055) B603055
theorem B476447 : Blo 475787 476447 := bstep (se 1 (by rfl) ⟨357335, by rfl⟩ : syracuseStep 476447 = 714671) B714671
theorem B804127 : Blo 475787 804127 := bstep (se 1 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 804127 = 1206191) B1206191
theorem B476507 : Blo 475787 476507 := bstep (se 1 (by rfl) ⟨357380, by rfl⟩ : syracuseStep 476507 = 714761) B714761
theorem B476527 : Blo 475787 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B476583 : Blo 475787 476583 := bstep (se 1 (by rfl) ⟨357437, by rfl⟩ : syracuseStep 476583 = 714875) B714875
theorem B476667 : Blo 475787 476667 := bstep (se 1 (by rfl) ⟨357500, by rfl⟩ : syracuseStep 476667 = 715001) B715001
theorem B476735 : Blo 475787 476735 := bstep (se 1 (by rfl) ⟨357551, by rfl⟩ : syracuseStep 476735 = 715103) B715103
theorem B476743 : Blo 475787 476743 := bstep (se 1 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 476743 = 715115) B715115
theorem B2410073 : Blo 475787 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B804539 : Blo 475787 804539 := bstep (se 1 (by rfl) ⟨603404, by rfl⟩ : syracuseStep 804539 = 1206809) B1206809
theorem B476895 : Blo 475787 476895 := bstep (se 1 (by rfl) ⟨357671, by rfl⟩ : syracuseStep 476895 = 715343) B715343
theorem B476975 : Blo 475787 476975 := bstep (se 1 (by rfl) ⟨357731, by rfl⟩ : syracuseStep 476975 = 715463) B715463
theorem B477083 : Blo 475787 477083 := bstep (se 1 (by rfl) ⟨357812, by rfl⟩ : syracuseStep 477083 = 715625) B715625
theorem B477135 : Blo 475787 477135 := bstep (se 1 (by rfl) ⟨357851, by rfl⟩ : syracuseStep 477135 = 715703) B715703
theorem B477159 : Blo 475787 477159 := bstep (se 1 (by rfl) ⟨357869, by rfl⟩ : syracuseStep 477159 = 715739) B715739
theorem B477471 : Blo 475787 477471 := bstep (se 1 (by rfl) ⟨358103, by rfl⟩ : syracuseStep 477471 = 716207) B716207
theorem B477531 : Blo 475787 477531 := bstep (se 1 (by rfl) ⟨358148, by rfl⟩ : syracuseStep 477531 = 716297) B716297
theorem B477551 : Blo 475787 477551 := bstep (se 1 (by rfl) ⟨358163, by rfl⟩ : syracuseStep 477551 = 716327) B716327
theorem B477607 : Blo 475787 477607 := bstep (se 1 (by rfl) ⟨358205, by rfl⟩ : syracuseStep 477607 = 716411) B716411
theorem B903649 : Blo 475787 903649 := bstep (se 2 (by rfl) ⟨338868, by rfl⟩ : syracuseStep 903649 = 677737) B677737
theorem B477691 : Blo 475787 477691 := bstep (se 1 (by rfl) ⟨358268, by rfl⟩ : syracuseStep 477691 = 716537) B716537
theorem B477759 : Blo 475787 477759 := bstep (se 1 (by rfl) ⟨358319, by rfl⟩ : syracuseStep 477759 = 716639) B716639
theorem B477767 : Blo 475787 477767 := bstep (se 1 (by rfl) ⟨358325, by rfl⟩ : syracuseStep 477767 = 716651) B716651
theorem B477919 : Blo 475787 477919 := bstep (se 1 (by rfl) ⟨358439, by rfl⟩ : syracuseStep 477919 = 716879) B716879
theorem B1362707 : Blo 475787 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B477999 : Blo 475787 477999 := bstep (se 1 (by rfl) ⟨358499, by rfl⟩ : syracuseStep 477999 = 716999) B716999
theorem B478107 : Blo 475787 478107 := bstep (se 1 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 478107 = 717161) B717161
theorem B2608043 : Blo 475787 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B3689387 : Blo 475787 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B478159 : Blo 475787 478159 := bstep (se 1 (by rfl) ⟨358619, by rfl⟩ : syracuseStep 478159 = 717239) B717239
theorem B478183 : Blo 475787 478183 := bstep (se 1 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 478183 = 717275) B717275
theorem B478495 : Blo 475787 478495 := bstep (se 1 (by rfl) ⟨358871, by rfl⟩ : syracuseStep 478495 = 717743) B717743
theorem B478555 : Blo 475787 478555 := bstep (se 1 (by rfl) ⟨358916, by rfl⟩ : syracuseStep 478555 = 717833) B717833
theorem B478575 : Blo 475787 478575 := bstep (se 1 (by rfl) ⟨358931, by rfl⟩ : syracuseStep 478575 = 717863) B717863
theorem B806267 : Blo 475787 806267 := bstep (se 1 (by rfl) ⟨604700, by rfl⟩ : syracuseStep 806267 = 1209401) B1209401
theorem B773513 : Blo 475787 773513 := bstep (se 2 (by rfl) ⟨290067, by rfl⟩ : syracuseStep 773513 = 580135) B580135
theorem B478631 : Blo 475787 478631 := bstep (se 1 (by rfl) ⟨358973, by rfl⟩ : syracuseStep 478631 = 717947) B717947
theorem B478715 : Blo 475787 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B478783 : Blo 475787 478783 := bstep (se 1 (by rfl) ⟨359087, by rfl⟩ : syracuseStep 478783 = 718175) B718175
theorem B478791 : Blo 475787 478791 := bstep (se 1 (by rfl) ⟨359093, by rfl⟩ : syracuseStep 478791 = 718187) B718187
theorem B478943 : Blo 475787 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B479023 : Blo 475787 479023 := bstep (se 1 (by rfl) ⟨359267, by rfl⟩ : syracuseStep 479023 = 718535) B718535
theorem B479131 : Blo 475787 479131 := bstep (se 1 (by rfl) ⟨359348, by rfl⟩ : syracuseStep 479131 = 718697) B718697
theorem B479183 : Blo 475787 479183 := bstep (se 1 (by rfl) ⟨359387, by rfl⟩ : syracuseStep 479183 = 718775) B718775
theorem B479207 : Blo 475787 479207 := bstep (se 1 (by rfl) ⟨359405, by rfl⟩ : syracuseStep 479207 = 718811) B718811
theorem B1527817 : Blo 475787 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B479519 : Blo 475787 479519 := bstep (se 1 (by rfl) ⟨359639, by rfl⟩ : syracuseStep 479519 = 719279) B719279
theorem B807259 : Blo 475787 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B479579 : Blo 475787 479579 := bstep (se 1 (by rfl) ⟨359684, by rfl⟩ : syracuseStep 479579 = 719369) B719369
theorem B479599 : Blo 475787 479599 := bstep (se 1 (by rfl) ⟨359699, by rfl⟩ : syracuseStep 479599 = 719399) B719399
theorem B479655 : Blo 475787 479655 := bstep (se 1 (by rfl) ⟨359741, by rfl⟩ : syracuseStep 479655 = 719483) B719483
theorem B11030987 : Blo 475787 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B971233 : Blo 475787 971233 := bstep (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) B728425
theorem B479739 : Blo 475787 479739 := bstep (se 1 (by rfl) ⟨359804, by rfl⟩ : syracuseStep 479739 = 719609) B719609
theorem B545503 : Blo 475787 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B5428133 : Blo 475787 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B906383 : Blo 475787 906383 := bstep (se 1 (by rfl) ⟨679787, by rfl⟩ : syracuseStep 906383 = 1359575) B1359575
theorem B1529047 : Blo 475787 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B906527 : Blo 475787 906527 := bstep (se 1 (by rfl) ⟨679895, by rfl⟩ : syracuseStep 906527 = 1359791) B1359791
theorem B808231 : Blo 475787 808231 := bstep (se 1 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 808231 = 1212347) B1212347
theorem B4576607 : Blo 475787 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B1070585 : Blo 475787 1070585 := bstep (se 2 (by rfl) ⟨401469, by rfl⟩ : syracuseStep 1070585 = 802939) B802939
theorem B7722503 : Blo 475787 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1070675 : Blo 475787 1070675 := bstep (se 1 (by rfl) ⟨803006, by rfl⟩ : syracuseStep 1070675 = 1606013) B1606013
theorem B1070855 : Blo 475787 1070855 := bstep (se 1 (by rfl) ⟨803141, by rfl⟩ : syracuseStep 1070855 = 1606283) B1606283
theorem B808751 : Blo 475787 808751 := bstep (se 1 (by rfl) ⟨606563, by rfl⟩ : syracuseStep 808751 = 1213127) B1213127
theorem B4348151 : Blo 475787 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B1071467 : Blo 475787 1071467 := bstep (se 1 (by rfl) ⟨803600, by rfl⟩ : syracuseStep 1071467 = 1607201) B1607201
theorem B645575 : Blo 475787 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B1071611 : Blo 475787 1071611 := bstep (se 1 (by rfl) ⟨803708, by rfl⟩ : syracuseStep 1071611 = 1607417) B1607417
theorem B1071737 : Blo 475787 1071737 := bstep (se 2 (by rfl) ⟨401901, by rfl⟩ : syracuseStep 1071737 = 803803) B803803
theorem B1071791 : Blo 475787 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B1071863 : Blo 475787 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B645943 : Blo 475787 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B4086683 : Blo 475787 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B1072043 : Blo 475787 1072043 := bstep (se 1 (by rfl) ⟨804032, by rfl⟩ : syracuseStep 1072043 = 1608065) B1608065
theorem B3071141 : Blo 475787 3071141 := bstep (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) B575839
theorem B1072583 : Blo 475787 1072583 := bstep (se 1 (by rfl) ⟨804437, by rfl⟩ : syracuseStep 1072583 = 1608875) B1608875
theorem B1727993 : Blo 475787 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B679519 : Blo 475787 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B4579031 : Blo 475787 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B2416391 : Blo 475787 2416391 := bstep (se 1 (by rfl) ⟨1812293, by rfl⟩ : syracuseStep 2416391 = 3624587) B3624587
theorem B1072943 : Blo 475787 1072943 := bstep (se 1 (by rfl) ⟨804707, by rfl⟩ : syracuseStep 1072943 = 1609415) B1609415
theorem B2187137 : Blo 475787 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B4087745 : Blo 475787 4087745 := bstep (se 2 (by rfl) ⟨1532904, by rfl⟩ : syracuseStep 4087745 = 3065809) B3065809
theorem B1204571 : Blo 475787 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B1204591 : Blo 475787 1204591 := bstep (se 1 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 1204591 = 1806887) B1806887
theorem B1073519 : Blo 475787 1073519 := bstep (se 1 (by rfl) ⟨805139, by rfl⟩ : syracuseStep 1073519 = 1610279) B1610279
theorem B1073591 : Blo 475787 1073591 := bstep (se 1 (by rfl) ⟨805193, by rfl⟩ : syracuseStep 1073591 = 1610387) B1610387
theorem B1073735 : Blo 475787 1073735 := bstep (se 1 (by rfl) ⟨805301, by rfl⟩ : syracuseStep 1073735 = 1610603) B1610603
theorem B1073771 : Blo 475787 1073771 := bstep (se 1 (by rfl) ⟨805328, by rfl⟩ : syracuseStep 1073771 = 1610657) B1610657
theorem B615215 : Blo 475787 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B1205239 : Blo 475787 1205239 := bstep (se 1 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 1205239 = 1807859) B1807859
theorem B1074167 : Blo 475787 1074167 := bstep (se 1 (by rfl) ⟨805625, by rfl⟩ : syracuseStep 1074167 = 1611251) B1611251
theorem B1631431 : Blo 475787 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B648425 : Blo 475787 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B714023 : Blo 475787 714023 := bstep (se 1 (by rfl) ⟨535517, by rfl⟩ : syracuseStep 714023 = 1071035) B1071035
theorem B1205543 : Blo 475787 1205543 := bstep (se 1 (by rfl) ⟨904157, by rfl⟩ : syracuseStep 1205543 = 1808315) B1808315
theorem B1074527 : Blo 475787 1074527 := bstep (se 1 (by rfl) ⟨805895, by rfl⟩ : syracuseStep 1074527 = 1611791) B1611791
theorem B714107 : Blo 475787 714107 := bstep (se 1 (by rfl) ⟨535580, by rfl⟩ : syracuseStep 714107 = 1071161) B1071161
theorem B714233 : Blo 475787 714233 := bstep (se 2 (by rfl) ⟨267837, by rfl⟩ : syracuseStep 714233 = 535675) B535675
theorem B9791063 : Blo 475787 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B3073625 : Blo 475787 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B714335 : Blo 475787 714335 := bstep (se 1 (by rfl) ⟨535751, by rfl⟩ : syracuseStep 714335 = 1071503) B1071503
theorem B1074923 : Blo 475787 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B714551 : Blo 475787 714551 := bstep (se 1 (by rfl) ⟨535913, by rfl⟩ : syracuseStep 714551 = 1071827) B1071827
theorem B1075049 : Blo 475787 1075049 := bstep (se 2 (by rfl) ⟨403143, by rfl⟩ : syracuseStep 1075049 = 806287) B806287
theorem B714857 : Blo 475787 714857 := bstep (se 2 (by rfl) ⟨268071, by rfl⟩ : syracuseStep 714857 = 536143) B536143
theorem B2287997 : Blo 475787 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1304999 : Blo 475787 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B715175 : Blo 475787 715175 := bstep (se 1 (by rfl) ⟨536381, by rfl⟩ : syracuseStep 715175 = 1072763) B1072763
theorem B1239479 : Blo 475787 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B715259 : Blo 475787 715259 := bstep (se 1 (by rfl) ⟨536444, by rfl⟩ : syracuseStep 715259 = 1072889) B1072889
theorem B17885731 : Blo 475787 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B2419307 : Blo 475787 2419307 := bstep (se 1 (by rfl) ⟨1814480, by rfl⟩ : syracuseStep 2419307 = 3628961) B3628961
theorem B715385 : Blo 475787 715385 := bstep (se 2 (by rfl) ⟨268269, by rfl⟩ : syracuseStep 715385 = 536539) B536539
theorem B715439 : Blo 475787 715439 := bstep (se 1 (by rfl) ⟨536579, by rfl⟩ : syracuseStep 715439 = 1073159) B1073159
theorem B1075895 : Blo 475787 1075895 := bstep (se 1 (by rfl) ⟨806921, by rfl⟩ : syracuseStep 1075895 = 1613843) B1613843
theorem B5827261 : Blo 475787 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B715487 : Blo 475787 715487 := bstep (se 1 (by rfl) ⟨536615, by rfl⟩ : syracuseStep 715487 = 1073231) B1073231
theorem B55896803 : Blo 475787 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B1207183 : Blo 475787 1207183 := bstep (se 1 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 1207183 = 1810775) B1810775
theorem B1076111 : Blo 475787 1076111 := bstep (se 1 (by rfl) ⟨807083, by rfl⟩ : syracuseStep 1076111 = 1614167) B1614167
theorem B715751 : Blo 475787 715751 := bstep (se 1 (by rfl) ⟨536813, by rfl⟩ : syracuseStep 715751 = 1073627) B1073627
theorem B2714705 : Blo 475787 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B2419793 : Blo 475787 2419793 := bstep (se 2 (by rfl) ⟨907422, by rfl⟩ : syracuseStep 2419793 = 1814845) B1814845
theorem B716009 : Blo 475787 716009 := bstep (se 2 (by rfl) ⟨268503, by rfl⟩ : syracuseStep 716009 = 537007) B537007
theorem B716063 : Blo 475787 716063 := bstep (se 1 (by rfl) ⟨537047, by rfl⟩ : syracuseStep 716063 = 1074095) B1074095
theorem B2583839 : Blo 475787 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B1207649 : Blo 475787 1207649 := bstep (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) B905737
theorem B716231 : Blo 475787 716231 := bstep (se 1 (by rfl) ⟨537173, by rfl⟩ : syracuseStep 716231 = 1074347) B1074347
theorem B1076831 : Blo 475787 1076831 := bstep (se 1 (by rfl) ⟨807623, by rfl⟩ : syracuseStep 1076831 = 1615247) B1615247
theorem B3632849 : Blo 475787 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B42430169 : Blo 475787 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B1208105 : Blo 475787 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B716585 : Blo 475787 716585 := bstep (se 2 (by rfl) ⟨268719, by rfl⟩ : syracuseStep 716585 = 537439) B537439
theorem B716591 : Blo 475787 716591 := bstep (se 1 (by rfl) ⟨537443, by rfl⟩ : syracuseStep 716591 = 1074887) B1074887
theorem B1077047 : Blo 475787 1077047 := bstep (se 1 (by rfl) ⟨807785, by rfl⟩ : syracuseStep 1077047 = 1615571) B1615571
theorem B2715707 : Blo 475787 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1077353 : Blo 475787 1077353 := bstep (se 2 (by rfl) ⟨404007, by rfl⟩ : syracuseStep 1077353 = 808015) B808015
theorem B717065 : Blo 475787 717065 := bstep (se 2 (by rfl) ⟨268899, by rfl⟩ : syracuseStep 717065 = 537799) B537799
theorem B717167 : Blo 475787 717167 := bstep (se 1 (by rfl) ⟨537875, by rfl⟩ : syracuseStep 717167 = 1075751) B1075751
theorem B717383 : Blo 475787 717383 := bstep (se 1 (by rfl) ⟨538037, by rfl⟩ : syracuseStep 717383 = 1076075) B1076075
theorem B1077839 : Blo 475787 1077839 := bstep (se 1 (by rfl) ⟨808379, by rfl⟩ : syracuseStep 1077839 = 1616759) B1616759
theorem B717419 : Blo 475787 717419 := bstep (se 1 (by rfl) ⟨538064, by rfl⟩ : syracuseStep 717419 = 1076129) B1076129
theorem B1077983 : Blo 475787 1077983 := bstep (se 1 (by rfl) ⟨808487, by rfl⟩ : syracuseStep 1077983 = 1616975) B1616975
theorem B1209107 : Blo 475787 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B717647 : Blo 475787 717647 := bstep (se 1 (by rfl) ⟨538235, by rfl⟩ : syracuseStep 717647 = 1076471) B1076471
theorem B1078235 : Blo 475787 1078235 := bstep (se 1 (by rfl) ⟨808676, by rfl⟩ : syracuseStep 1078235 = 1617353) B1617353
theorem B1078415 : Blo 475787 1078415 := bstep (se 1 (by rfl) ⟨808811, by rfl⟩ : syracuseStep 1078415 = 1617623) B1617623
theorem B1209563 : Blo 475787 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B718043 : Blo 475787 718043 := bstep (se 1 (by rfl) ⟨538532, by rfl⟩ : syracuseStep 718043 = 1077065) B1077065
theorem B1078505 : Blo 475787 1078505 := bstep (se 2 (by rfl) ⟨404439, by rfl⟩ : syracuseStep 1078505 = 808879) B808879
theorem B1209593 : Blo 475787 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B1078559 : Blo 475787 1078559 := bstep (se 1 (by rfl) ⟨808919, by rfl⟩ : syracuseStep 1078559 = 1617839) B1617839
theorem B718217 : Blo 475787 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B2717165 : Blo 475787 2717165 := bstep (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) B1018937
theorem B587359 : Blo 475787 587359 := bstep (se 1 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 587359 = 881039) B881039
theorem B718571 : Blo 475787 718571 := bstep (se 1 (by rfl) ⟨538928, by rfl⟩ : syracuseStep 718571 = 1077857) B1077857
theorem B1079081 : Blo 475787 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B1144633 : Blo 475787 1144633 := bstep (se 2 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 1144633 = 858475) B858475
theorem B1210241 : Blo 475787 1210241 := bstep (se 2 (by rfl) ⟨453840, by rfl⟩ : syracuseStep 1210241 = 907681) B907681
theorem B9598907 : Blo 475787 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B718799 : Blo 475787 718799 := bstep (se 1 (by rfl) ⟨539099, by rfl⟩ : syracuseStep 718799 = 1078199) B1078199
theorem B3635279 : Blo 475787 3635279 := bstep (se 1 (by rfl) ⟨2726459, by rfl⟩ : syracuseStep 3635279 = 5452919) B5452919
theorem B8157509 : Blo 475787 8157509 := bstep (se 4 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 8157509 = 1529533) B1529533
theorem B1210697 : Blo 475787 1210697 := bstep (se 2 (by rfl) ⟨454011, by rfl⟩ : syracuseStep 1210697 = 908023) B908023
theorem B719195 : Blo 475787 719195 := bstep (se 1 (by rfl) ⟨539396, by rfl⟩ : syracuseStep 719195 = 1078793) B1078793
theorem B6126029 : Blo 475787 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B719423 : Blo 475787 719423 := bstep (se 1 (by rfl) ⟨539567, by rfl⟩ : syracuseStep 719423 = 1079135) B1079135
theorem B1211051 : Blo 475787 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B719543 : Blo 475787 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B2456507 : Blo 475787 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1146143 : Blo 475787 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B2424329 : Blo 475787 2424329 := bstep (se 2 (by rfl) ⟨909123, by rfl⟩ : syracuseStep 2424329 = 1818247) B1818247
theorem B2588269 : Blo 475787 2588269 := bstep (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) B970601
theorem B7732883 : Blo 475787 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B2457391 : Blo 475787 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B3276605 : Blo 475787 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B1212367 : Blo 475787 1212367 := bstep (se 1 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 1212367 = 1818551) B1818551
theorem B1605851 : Blo 475787 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B9175355 : Blo 475787 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B1606121 : Blo 475787 1606121 := bstep (se 2 (by rfl) ⟨602295, by rfl⟩ : syracuseStep 1606121 = 1204591) B1204591
theorem B5178269 : Blo 475787 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B2425787 : Blo 475787 2425787 := bstep (se 1 (by rfl) ⟨1819340, by rfl⟩ : syracuseStep 2425787 = 3638681) B3638681
theorem B1606715 : Blo 475787 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B1606985 : Blo 475787 1606985 := bstep (se 2 (by rfl) ⟨602619, by rfl⟩ : syracuseStep 1606985 = 1205239) B1205239
theorem B2066081 : Blo 475787 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B2459591 : Blo 475787 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B11470891 : Blo 475787 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B1640573 : Blo 475787 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B1313063 : Blo 475787 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B3640625 : Blo 475787 3640625 := bstep (se 2 (by rfl) ⟨1365234, by rfl⟩ : syracuseStep 3640625 = 2730469) B2730469
theorem B3051071 : Blo 475787 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B7769681 : Blo 475787 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B5148335 : Blo 475787 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B3870467 : Blo 475787 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B1609577 : Blo 475787 1609577 := bstep (se 2 (by rfl) ⟨603591, by rfl⟩ : syracuseStep 1609577 = 1207183) B1207183
theorem B2723705 : Blo 475787 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B2036303 : Blo 475787 2036303 := bstep (se 1 (by rfl) ⟨1527227, by rfl⟩ : syracuseStep 2036303 = 3054455) B3054455
theorem B2757199 : Blo 475787 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B1380959 : Blo 475787 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B2724455 : Blo 475787 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B6886133 : Blo 475787 6886133 := bstep (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) B645575
theorem B3937085 : Blo 475787 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B1151995 : Blo 475787 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B1020937 : Blo 475787 1020937 := bstep (se 2 (by rfl) ⟨382851, by rfl⟩ : syracuseStep 1020937 = 765703) B765703
theorem B3052687 : Blo 475787 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B1610927 : Blo 475787 1610927 := bstep (se 1 (by rfl) ⟨1208195, by rfl⟩ : syracuseStep 1610927 = 2416391) B2416391
theorem B2725163 : Blo 475787 2725163 := bstep (se 1 (by rfl) ⟨2043872, by rfl⟩ : syracuseStep 2725163 = 4087745) B4087745
theorem B2037089 : Blo 475787 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B3282295 : Blo 475787 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B857711 : Blo 475787 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B4069187 : Blo 475787 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B2725913 : Blo 475787 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B4593793 : Blo 475787 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B727337 : Blo 475787 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B89332109 : Blo 475787 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B6527375 : Blo 475787 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B2726621 : Blo 475787 2726621 := bstep (se 3 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 2726621 = 1022483) B1022483
theorem B2038729 : Blo 475787 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B826319 : Blo 475787 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B1612871 : Blo 475787 1612871 := bstep (se 1 (by rfl) ⟨1209653, by rfl⟩ : syracuseStep 1612871 = 2419307) B2419307
theorem B1612925 : Blo 475787 1612925 := bstep (se 3 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 1612925 = 604847) B604847
theorem B37264535 : Blo 475787 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B1809803 : Blo 475787 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B1613195 : Blo 475787 1613195 := bstep (se 1 (by rfl) ⟨1209896, by rfl⟩ : syracuseStep 1613195 = 2419793) B2419793
theorem B859643 : Blo 475787 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B5905979 : Blo 475787 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B6954781 : Blo 475787 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B28286779 : Blo 475787 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B1810471 : Blo 475787 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B1843553 : Blo 475787 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B16491073 : Blo 475787 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B21504727 : Blo 475787 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B1811443 : Blo 475787 1811443 := bstep (se 1 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 1811443 = 2717165) B2717165
theorem B861257 : Blo 475787 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B4596983 : Blo 475787 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B6399271 : Blo 475787 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B20719637 : Blo 475787 20719637 := bstep (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) B971233
theorem B3451025 : Blo 475787 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B764095 : Blo 475787 764095 := bstep (se 1 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 764095 = 1146143) B1146143
theorem B7973057 : Blo 475787 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B1616219 : Blo 475787 1616219 := bstep (se 1 (by rfl) ⟨1212164, by rfl⟩ : syracuseStep 1616219 = 2424329) B2424329
theorem B5155255 : Blo 475787 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B1616489 : Blo 475787 1616489 := bstep (se 2 (by rfl) ⟨606183, by rfl⟩ : syracuseStep 1616489 = 1212367) B1212367
theorem B1813175 : Blo 475787 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B3975875 : Blo 475787 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B13806395 : Blo 475787 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B535387 : Blo 475787 535387 := bstep (se 1 (by rfl) ⟨401540, by rfl⟩ : syracuseStep 535387 = 803081) B803081
theorem B1453031 : Blo 475787 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B8170631 : Blo 475787 8170631 := bstep (se 1 (by rfl) ⟨6127973, by rfl⟩ : syracuseStep 8170631 = 12255947) B12255947
theorem B1617515 : Blo 475787 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B536359 : Blo 475787 536359 := bstep (se 1 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 536359 = 804539) B804539
theorem B765767 : Blo 475787 765767 := bstep (se 1 (by rfl) ⟨574325, by rfl⟩ : syracuseStep 765767 = 1148651) B1148651
theorem B1617785 : Blo 475787 1617785 := bstep (se 2 (by rfl) ⟨606669, by rfl⟩ : syracuseStep 1617785 = 1213339) B1213339
theorem B1618109 : Blo 475787 1618109 := bstep (se 3 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 1618109 = 606791) B606791
theorem B3060605 : Blo 475787 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B537511 : Blo 475787 537511 := bstep (se 1 (by rfl) ⟨403133, by rfl⟩ : syracuseStep 537511 = 806267) B806267
theorem B7353991 : Blo 475787 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B3192721 : Blo 475787 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B3618755 : Blo 475787 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B604255 : Blo 475787 604255 := bstep (se 1 (by rfl) ⟨453191, by rfl⟩ : syracuseStep 604255 = 906383) B906383
theorem B604351 : Blo 475787 604351 := bstep (se 1 (by rfl) ⟨453263, by rfl⟩ : syracuseStep 604351 = 906527) B906527
theorem B539167 : Blo 475787 539167 := bstep (se 1 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 539167 = 808751) B808751
theorem B5519929 : Blo 475787 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B2898767 : Blo 475787 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1227905 : Blo 475787 1227905 := bstep (se 2 (by rfl) ⟨460464, by rfl⟩ : syracuseStep 1227905 = 920929) B920929
theorem B6143147 : Blo 475787 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B2047427 : Blo 475787 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B1359335 : Blo 475787 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B966287 : Blo 475787 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B1458091 : Blo 475787 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B31768523 : Blo 475787 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B803047 : Blo 475787 803047 := bstep (se 1 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 803047 = 1204571) B1204571
theorem B803209 : Blo 475787 803209 := bstep (se 2 (by rfl) ⟨301203, by rfl⟩ : syracuseStep 803209 = 602407) B602407
theorem B5915105 : Blo 475787 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B2409263 : Blo 475787 2409263 := bstep (se 1 (by rfl) ⟨1806947, by rfl⟩ : syracuseStep 2409263 = 3613895) B3613895
theorem B803641 : Blo 475787 803641 := bstep (se 2 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 803641 = 602731) B602731
theorem B476015 : Blo 475787 476015 := bstep (se 1 (by rfl) ⟨357011, by rfl⟩ : syracuseStep 476015 = 714023) B714023
theorem B803695 : Blo 475787 803695 := bstep (se 1 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 803695 = 1205543) B1205543
theorem B476071 : Blo 475787 476071 := bstep (se 1 (by rfl) ⟨357053, by rfl⟩ : syracuseStep 476071 = 714107) B714107
theorem B476155 : Blo 475787 476155 := bstep (se 1 (by rfl) ⟨357116, by rfl⟩ : syracuseStep 476155 = 714233) B714233
theorem B8700965 : Blo 475787 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B2049083 : Blo 475787 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B476223 : Blo 475787 476223 := bstep (se 1 (by rfl) ⟨357167, by rfl⟩ : syracuseStep 476223 = 714335) B714335
theorem B803945 : Blo 475787 803945 := bstep (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) B602959
theorem B476367 : Blo 475787 476367 := bstep (se 1 (by rfl) ⟨357275, by rfl⟩ : syracuseStep 476367 = 714551) B714551
theorem B1361225 : Blo 475787 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B476571 : Blo 475787 476571 := bstep (se 1 (by rfl) ⟨357428, by rfl⟩ : syracuseStep 476571 = 714857) B714857
theorem B1525331 : Blo 475787 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B869999 : Blo 475787 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B476783 : Blo 475787 476783 := bstep (se 1 (by rfl) ⟨357587, by rfl⟩ : syracuseStep 476783 = 715175) B715175
theorem B476839 : Blo 475787 476839 := bstep (se 1 (by rfl) ⟨357629, by rfl⟩ : syracuseStep 476839 = 715259) B715259
theorem B476923 : Blo 475787 476923 := bstep (se 1 (by rfl) ⟨357692, by rfl⟩ : syracuseStep 476923 = 715385) B715385
theorem B476959 : Blo 475787 476959 := bstep (se 1 (by rfl) ⟨357719, by rfl⟩ : syracuseStep 476959 = 715439) B715439
theorem B476991 : Blo 475787 476991 := bstep (se 1 (by rfl) ⟨357743, by rfl⟩ : syracuseStep 476991 = 715487) B715487
theorem B1820495 : Blo 475787 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B1361863 : Blo 475787 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B477167 : Blo 475787 477167 := bstep (se 1 (by rfl) ⟨357875, by rfl⟩ : syracuseStep 477167 = 715751) B715751
theorem B477339 : Blo 475787 477339 := bstep (se 1 (by rfl) ⟨358004, by rfl⟩ : syracuseStep 477339 = 716009) B716009
theorem B477375 : Blo 475787 477375 := bstep (se 1 (by rfl) ⟨358031, by rfl⟩ : syracuseStep 477375 = 716063) B716063
theorem B1722559 : Blo 475787 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B805099 : Blo 475787 805099 := bstep (se 1 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 805099 = 1207649) B1207649
theorem B477487 : Blo 475787 477487 := bstep (se 1 (by rfl) ⟨358115, by rfl⟩ : syracuseStep 477487 = 716231) B716231
theorem B1526177 : Blo 475787 1526177 := bstep (se 2 (by rfl) ⟨572316, by rfl⟩ : syracuseStep 1526177 = 1144633) B1144633
theorem B805403 : Blo 475787 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B477723 : Blo 475787 477723 := bstep (se 1 (by rfl) ⟨358292, by rfl⟩ : syracuseStep 477723 = 716585) B716585
theorem B477727 : Blo 475787 477727 := bstep (se 1 (by rfl) ⟨358295, by rfl⟩ : syracuseStep 477727 = 716591) B716591
theorem B4082309 : Blo 475787 4082309 := bstep (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) B765433
theorem B478043 : Blo 475787 478043 := bstep (se 1 (by rfl) ⟨358532, by rfl⟩ : syracuseStep 478043 = 717065) B717065
theorem B478111 : Blo 475787 478111 := bstep (se 1 (by rfl) ⟨358583, by rfl⟩ : syracuseStep 478111 = 717167) B717167
theorem B478255 : Blo 475787 478255 := bstep (se 1 (by rfl) ⟨358691, by rfl⟩ : syracuseStep 478255 = 717383) B717383
theorem B478279 : Blo 475787 478279 := bstep (se 1 (by rfl) ⟨358709, by rfl⟩ : syracuseStep 478279 = 717419) B717419
theorem B3624101 : Blo 475787 3624101 := bstep (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) B679519
theorem B806071 : Blo 475787 806071 := bstep (se 1 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 806071 = 1209107) B1209107
theorem B478431 : Blo 475787 478431 := bstep (se 1 (by rfl) ⟨358823, by rfl⟩ : syracuseStep 478431 = 717647) B717647
theorem B2411855 : Blo 475787 2411855 := bstep (se 1 (by rfl) ⟨1808891, by rfl⟩ : syracuseStep 2411855 = 3617783) B3617783
theorem B806375 : Blo 475787 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B478695 : Blo 475787 478695 := bstep (se 1 (by rfl) ⟨359021, by rfl⟩ : syracuseStep 478695 = 718043) B718043
theorem B806395 : Blo 475787 806395 := bstep (se 1 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 806395 = 1209593) B1209593
theorem B478811 : Blo 475787 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B479047 : Blo 475787 479047 := bstep (se 1 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 479047 = 718571) B718571
theorem B806827 : Blo 475787 806827 := bstep (se 1 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 806827 = 1210241) B1210241
theorem B479199 : Blo 475787 479199 := bstep (se 1 (by rfl) ⟨359399, by rfl⟩ : syracuseStep 479199 = 718799) B718799
theorem B807131 : Blo 475787 807131 := bstep (se 1 (by rfl) ⟨605348, by rfl⟩ : syracuseStep 807131 = 1210697) B1210697
theorem B479463 : Blo 475787 479463 := bstep (se 1 (by rfl) ⟨359597, by rfl⟩ : syracuseStep 479463 = 719195) B719195
theorem B4084019 : Blo 475787 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B479615 : Blo 475787 479615 := bstep (se 1 (by rfl) ⟨359711, by rfl⟩ : syracuseStep 479615 = 719423) B719423
theorem B807367 : Blo 475787 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B479695 : Blo 475787 479695 := bstep (se 1 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 479695 = 719543) B719543
theorem B807401 : Blo 475787 807401 := bstep (se 2 (by rfl) ⟨302775, by rfl⟩ : syracuseStep 807401 = 605551) B605551
theorem B971347 : Blo 475787 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B2413151 : Blo 475787 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B2904893 : Blo 475787 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B644203 : Blo 475787 644203 := bstep (se 1 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 644203 = 966305) B966305
theorem B1365167 : Blo 475787 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B2184403 : Blo 475787 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B19650059 : Blo 475787 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B26105489 : Blo 475787 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B3692639 : Blo 475787 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B874793 : Blo 475787 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B809257 : Blo 475787 809257 := bstep (se 2 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 809257 = 606943) B606943
theorem B4086409 : Blo 475787 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B1072079 : Blo 475787 1072079 := bstep (se 1 (by rfl) ⟨804059, by rfl⟩ : syracuseStep 1072079 = 1608119) B1608119
theorem B1072097 : Blo 475787 1072097 := bstep (se 2 (by rfl) ⟨402036, by rfl⟩ : syracuseStep 1072097 = 804073) B804073
theorem B1072169 : Blo 475787 1072169 := bstep (se 2 (by rfl) ⟨402063, by rfl⟩ : syracuseStep 1072169 = 804127) B804127
theorem B908471 : Blo 475787 908471 := bstep (se 1 (by rfl) ⟨681353, by rfl⟩ : syracuseStep 908471 = 1362707) B1362707
theorem B482527 : Blo 475787 482527 := bstep (se 1 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 482527 = 723791) B723791
theorem B2711015 : Blo 475787 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B515675 : Blo 475787 515675 := bstep (se 1 (by rfl) ⟨386756, by rfl⟩ : syracuseStep 515675 = 773513) B773513
theorem B679531 : Blo 475787 679531 := bstep (se 1 (by rfl) ⟨509648, by rfl⟩ : syracuseStep 679531 = 1019297) B1019297
theorem B1531943 : Blo 475787 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B1106273 : Blo 475787 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B2712041 : Blo 475787 2712041 := bstep (se 2 (by rfl) ⟨1017015, by rfl⟩ : syracuseStep 2712041 = 2034031) B2034031
theorem B1729133 : Blo 475787 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B1204865 : Blo 475787 1204865 := bstep (se 2 (by rfl) ⟨451824, by rfl⟩ : syracuseStep 1204865 = 903649) B903649
theorem B23847641 : Blo 475787 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B1074131 : Blo 475787 1074131 := bstep (se 1 (by rfl) ⟨805598, by rfl⟩ : syracuseStep 1074131 = 1611197) B1611197
theorem B713723 : Blo 475787 713723 := bstep (se 1 (by rfl) ⟨535292, by rfl⟩ : syracuseStep 713723 = 1070585) B1070585
theorem B713783 : Blo 475787 713783 := bstep (se 1 (by rfl) ⟨535337, by rfl⟩ : syracuseStep 713783 = 1070675) B1070675
theorem B713903 : Blo 475787 713903 := bstep (se 1 (by rfl) ⟨535427, by rfl⟩ : syracuseStep 713903 = 1070855) B1070855
theorem B1074383 : Blo 475787 1074383 := bstep (se 1 (by rfl) ⟨805787, by rfl⟩ : syracuseStep 1074383 = 1611575) B1611575
theorem B1205675 : Blo 475787 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B1074707 : Blo 475787 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B714311 : Blo 475787 714311 := bstep (se 1 (by rfl) ⟨535733, by rfl⟩ : syracuseStep 714311 = 1071467) B1071467
theorem B714407 : Blo 475787 714407 := bstep (se 1 (by rfl) ⟨535805, by rfl⟩ : syracuseStep 714407 = 1071611) B1071611
theorem B714491 : Blo 475787 714491 := bstep (se 1 (by rfl) ⟨535868, by rfl⟩ : syracuseStep 714491 = 1071737) B1071737
theorem B714527 : Blo 475787 714527 := bstep (se 1 (by rfl) ⟨535895, by rfl⟩ : syracuseStep 714527 = 1071791) B1071791
theorem B1533737 : Blo 475787 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B714575 : Blo 475787 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B714695 : Blo 475787 714695 := bstep (se 1 (by rfl) ⟨536021, by rfl⟩ : syracuseStep 714695 = 1072043) B1072043
theorem B682139 : Blo 475787 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B1075391 : Blo 475787 1075391 := bstep (se 1 (by rfl) ⟨806543, by rfl⟩ : syracuseStep 1075391 = 1613087) B1613087
theorem B682219 : Blo 475787 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B715049 : Blo 475787 715049 := bstep (se 2 (by rfl) ⟨268143, by rfl⟩ : syracuseStep 715049 = 536287) B536287
theorem B715055 : Blo 475787 715055 := bstep (se 1 (by rfl) ⟨536291, by rfl⟩ : syracuseStep 715055 = 1072583) B1072583
theorem B715295 : Blo 475787 715295 := bstep (se 1 (by rfl) ⟨536471, by rfl⟩ : syracuseStep 715295 = 1072943) B1072943
theorem B1206971 : Blo 475787 1206971 := bstep (se 1 (by rfl) ⟨905228, by rfl⟩ : syracuseStep 1206971 = 1810457) B1810457
theorem B715679 : Blo 475787 715679 := bstep (se 1 (by rfl) ⟨536759, by rfl⟩ : syracuseStep 715679 = 1073519) B1073519
theorem B715727 : Blo 475787 715727 := bstep (se 1 (by rfl) ⟨536795, by rfl⟩ : syracuseStep 715727 = 1073591) B1073591
theorem B715817 : Blo 475787 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B715823 : Blo 475787 715823 := bstep (se 1 (by rfl) ⟨536867, by rfl⟩ : syracuseStep 715823 = 1073735) B1073735
theorem B715847 : Blo 475787 715847 := bstep (se 1 (by rfl) ⟨536885, by rfl⟩ : syracuseStep 715847 = 1073771) B1073771
theorem B1076345 : Blo 475787 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B716111 : Blo 475787 716111 := bstep (se 1 (by rfl) ⟨537083, by rfl⟩ : syracuseStep 716111 = 1074167) B1074167
theorem B716201 : Blo 475787 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B716351 : Blo 475787 716351 := bstep (se 1 (by rfl) ⟨537263, by rfl⟩ : syracuseStep 716351 = 1074527) B1074527
theorem B1077011 : Blo 475787 1077011 := bstep (se 1 (by rfl) ⟨807758, by rfl⟩ : syracuseStep 1077011 = 1615517) B1615517
theorem B716615 : Blo 475787 716615 := bstep (se 1 (by rfl) ⟨537461, by rfl⟩ : syracuseStep 716615 = 1074923) B1074923
theorem B716699 : Blo 475787 716699 := bstep (se 1 (by rfl) ⟨537524, by rfl⟩ : syracuseStep 716699 = 1075049) B1075049
theorem B3436667 : Blo 475787 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B1077371 : Blo 475787 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B1536185 : Blo 475787 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B1077641 : Blo 475787 1077641 := bstep (se 2 (by rfl) ⟨404115, by rfl⟩ : syracuseStep 1077641 = 808231) B808231
theorem B717263 : Blo 475787 717263 := bstep (se 1 (by rfl) ⟨537947, by rfl⟩ : syracuseStep 717263 = 1075895) B1075895
theorem B717305 : Blo 475787 717305 := bstep (se 2 (by rfl) ⟨268989, by rfl⟩ : syracuseStep 717305 = 537979) B537979
theorem B1208915 : Blo 475787 1208915 := bstep (se 1 (by rfl) ⟨906686, by rfl⟩ : syracuseStep 1208915 = 1813373) B1813373
theorem B717407 : Blo 475787 717407 := bstep (se 1 (by rfl) ⟨538055, by rfl⟩ : syracuseStep 717407 = 1076111) B1076111
theorem B1536607 : Blo 475787 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B783145 : Blo 475787 783145 := bstep (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) B587359
theorem B717887 : Blo 475787 717887 := bstep (se 1 (by rfl) ⟨538415, by rfl⟩ : syracuseStep 717887 = 1076831) B1076831
theorem B717929 : Blo 475787 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B1209451 : Blo 475787 1209451 := bstep (se 1 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 1209451 = 1814177) B1814177
theorem B1078379 : Blo 475787 1078379 := bstep (se 1 (by rfl) ⟨808784, by rfl⟩ : syracuseStep 1078379 = 1617569) B1617569
theorem B2421899 : Blo 475787 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B718031 : Blo 475787 718031 := bstep (se 1 (by rfl) ⟨538523, by rfl⟩ : syracuseStep 718031 = 1077047) B1077047
theorem B1209755 : Blo 475787 1209755 := bstep (se 1 (by rfl) ⟨907316, by rfl⟩ : syracuseStep 1209755 = 1814633) B1814633
theorem B718235 : Blo 475787 718235 := bstep (se 1 (by rfl) ⟨538676, by rfl⟩ : syracuseStep 718235 = 1077353) B1077353
theorem B718457 : Blo 475787 718457 := bstep (se 2 (by rfl) ⟨269421, by rfl⟩ : syracuseStep 718457 = 538843) B538843
theorem B1078955 : Blo 475787 1078955 := bstep (se 1 (by rfl) ⟨809216, by rfl⟩ : syracuseStep 1078955 = 1618433) B1618433
theorem B718559 : Blo 475787 718559 := bstep (se 1 (by rfl) ⟨538919, by rfl⟩ : syracuseStep 718559 = 1077839) B1077839
theorem B1931003 : Blo 475787 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B718655 : Blo 475787 718655 := bstep (se 1 (by rfl) ⟨538991, by rfl⟩ : syracuseStep 718655 = 1077983) B1077983
theorem B718823 : Blo 475787 718823 := bstep (se 1 (by rfl) ⟨539117, by rfl⟩ : syracuseStep 718823 = 1078235) B1078235
theorem B1079279 : Blo 475787 1079279 := bstep (se 1 (by rfl) ⟨809459, by rfl⟩ : syracuseStep 1079279 = 1618919) B1618919
theorem B718841 : Blo 475787 718841 := bstep (se 2 (by rfl) ⟨269565, by rfl⟩ : syracuseStep 718841 = 539131) B539131
theorem B718943 : Blo 475787 718943 := bstep (se 1 (by rfl) ⟨539207, by rfl⟩ : syracuseStep 718943 = 1078415) B1078415
theorem B719003 : Blo 475787 719003 := bstep (se 1 (by rfl) ⟨539252, by rfl⟩ : syracuseStep 719003 = 1078505) B1078505
theorem B719039 : Blo 475787 719039 := bstep (se 1 (by rfl) ⟨539279, by rfl⟩ : syracuseStep 719039 = 1078559) B1078559
theorem B1079495 : Blo 475787 1079495 := bstep (se 1 (by rfl) ⟨809621, by rfl⟩ : syracuseStep 1079495 = 1619243) B1619243
theorem B719081 : Blo 475787 719081 := bstep (se 2 (by rfl) ⟨269655, by rfl⟩ : syracuseStep 719081 = 539311) B539311
theorem B2586887 : Blo 475787 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B1210747 : Blo 475787 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B719387 : Blo 475787 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B719465 : Blo 475787 719465 := bstep (se 2 (by rfl) ⟨269799, by rfl⟩ : syracuseStep 719465 = 539599) B539599
theorem B2423519 : Blo 475787 2423519 := bstep (se 1 (by rfl) ⟨1817639, by rfl⟩ : syracuseStep 2423519 = 3635279) B3635279
theorem B5438339 : Blo 475787 5438339 := bstep (se 1 (by rfl) ⟨4078754, by rfl⟩ : syracuseStep 5438339 = 8157509) B8157509
theorem B1637671 : Blo 475787 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B2260391 : Blo 475787 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B3276521 : Blo 475787 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B4096493 : Blo 475787 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B1606175 : Blo 475787 1606175 := bstep (se 1 (by rfl) ⟨1204631, by rfl⟩ : syracuseStep 1606175 = 2409263) B2409263
theorem B5800643 : Blo 475787 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B21988097 : Blo 475787 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B28672969 : Blo 475787 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B1016887 : Blo 475787 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B1213663 : Blo 475787 1213663 := bstep (se 1 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 1213663 = 1820495) B1820495
theorem B1639727 : Blo 475787 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B1017451 : Blo 475787 1017451 := bstep (se 1 (by rfl) ⟨763088, by rfl⟩ : syracuseStep 1017451 = 1526177) B1526177
theorem B2721539 : Blo 475787 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B2427083 : Blo 475787 2427083 := bstep (se 1 (by rfl) ⟨1820312, by rfl⟩ : syracuseStep 2427083 = 3640625) B3640625
theorem B1607903 : Blo 475787 1607903 := bstep (se 1 (by rfl) ⟨1205927, by rfl⟩ : syracuseStep 1607903 = 2411855) B2411855
theorem B2034047 : Blo 475787 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B5179787 : Blo 475787 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B2722679 : Blo 475787 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B1018793 : Blo 475787 1018793 := bstep (se 2 (by rfl) ⟨382047, by rfl⟩ : syracuseStep 1018793 = 764095) B764095
theorem B2296745 : Blo 475787 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B1608767 : Blo 475787 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B920639 : Blo 475787 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B4590755 : Blo 475787 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B2624723 : Blo 475787 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B1936595 : Blo 475787 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B17403659 : Blo 475787 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B2461759 : Blo 475787 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B5509549 : Blo 475787 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B24843023 : Blo 475787 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B1807343 : Blo 475787 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B3937319 : Blo 475787 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B1021295 : Blo 475787 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B1808027 : Blo 475787 1808027 := bstep (se 1 (by rfl) ⟨1356020, by rfl⟩ : syracuseStep 1808027 = 2712041) B2712041
theorem B1152755 : Blo 475787 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B15898427 : Blo 475787 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B3676265 : Blo 475787 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B1939565 : Blo 475787 1939565 := bstep (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) B727337
theorem B1022491 : Blo 475787 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B2300683 : Blo 475787 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B5315371 : Blo 475787 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B858937 : Blo 475787 858937 := bstep (se 2 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 858937 = 644203) B644203
theorem B1612601 : Blo 475787 1612601 := bstep (se 2 (by rfl) ⟨604725, by rfl⟩ : syracuseStep 1612601 = 1209451) B1209451
theorem B4070249 : Blo 475787 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B5447087 : Blo 475787 5447087 := bstep (se 1 (by rfl) ⟨4085315, by rfl⟩ : syracuseStep 5447087 = 8170631) B8170631
theorem B9805321 : Blo 475787 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B2203517 : Blo 475787 2203517 := bstep (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) B826319
theorem B1614329 : Blo 475787 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B2040403 : Blo 475787 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B1614599 : Blo 475787 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B5448545 : Blo 475787 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B1287335 : Blo 475787 1287335 := bstep (se 1 (by rfl) ⟨965501, by rfl⟩ : syracuseStep 1287335 = 1931003) B1931003
theorem B1615679 : Blo 475787 1615679 := bstep (se 1 (by rfl) ⟨1211759, by rfl⟩ : syracuseStep 1615679 = 2423519) B2423519
theorem B1944121 : Blo 475787 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B21179015 : Blo 475787 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B3943403 : Blo 475787 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B3452179 : Blo 475787 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B1617191 : Blo 475787 1617191 := bstep (se 1 (by rfl) ⟨1212893, by rfl⟩ : syracuseStep 1617191 = 2425787) B2425787
theorem B535963 : Blo 475787 535963 := bstep (se 1 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 535963 = 803945) B803945
theorem B1093715 : Blo 475787 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B536935 : Blo 475787 536935 := bstep (se 1 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 536935 = 805403) B805403
theorem B8532361 : Blo 475787 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B537583 : Blo 475787 537583 := bstep (se 1 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 537583 = 806375) B806375
theorem B1815803 : Blo 475787 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B1815817 : Blo 475787 1815817 := bstep (se 2 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 1815817 = 1361863) B1361863
theorem B538087 : Blo 475787 538087 := bstep (se 1 (by rfl) ⟨403565, by rfl⟩ : syracuseStep 538087 = 807131) B807131
theorem B538267 : Blo 475787 538267 := bstep (se 1 (by rfl) ⟨403700, by rfl⟩ : syracuseStep 538267 = 807401) B807401
theorem B1357535 : Blo 475787 1357535 := bstep (se 1 (by rfl) ⟨1018151, by rfl⟩ : syracuseStep 1357535 = 2036303) B2036303
theorem B1816303 : Blo 475787 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B1816775 : Blo 475787 1816775 := bstep (se 1 (by rfl) ⟨1362581, by rfl⟩ : syracuseStep 1816775 = 2725163) B2725163
theorem B1358059 : Blo 475787 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B571807 : Blo 475787 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B1817275 : Blo 475787 1817275 := bstep (se 1 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 1817275 = 2725913) B2725913
theorem B59554739 : Blo 475787 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B1817747 : Blo 475787 1817747 := bstep (se 1 (by rfl) ⟨1363310, by rfl⟩ : syracuseStep 1817747 = 2726621) B2726621
theorem B605647 : Blo 475787 605647 := bstep (se 1 (by rfl) ⟨454235, by rfl⟩ : syracuseStep 605647 = 908471) B908471
theorem B573095 : Blo 475787 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B737515 : Blo 475787 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B1229035 : Blo 475787 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B1819037 : Blo 475787 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B803243 : Blo 475787 803243 := bstep (se 1 (by rfl) ⟨602432, by rfl⟩ : syracuseStep 803243 = 1204865) B1204865
theorem B475815 : Blo 475787 475815 := bstep (se 1 (by rfl) ⟨356861, by rfl⟩ : syracuseStep 475815 = 713723) B713723
theorem B475855 : Blo 475787 475855 := bstep (se 1 (by rfl) ⟨356891, by rfl⟩ : syracuseStep 475855 = 713783) B713783
theorem B574171 : Blo 475787 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B1295129 : Blo 475787 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B475935 : Blo 475787 475935 := bstep (se 1 (by rfl) ⟨356951, by rfl⟩ : syracuseStep 475935 = 713903) B713903
theorem B2048809 : Blo 475787 2048809 := bstep (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) B1536607
theorem B3064655 : Blo 475787 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B803783 : Blo 475787 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B476207 : Blo 475787 476207 := bstep (se 1 (by rfl) ⟨357155, by rfl⟩ : syracuseStep 476207 = 714311) B714311
theorem B476271 : Blo 475787 476271 := bstep (se 1 (by rfl) ⟨357203, by rfl⟩ : syracuseStep 476271 = 714407) B714407
theorem B2573477 : Blo 475787 2573477 := bstep (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) B482527
theorem B476327 : Blo 475787 476327 := bstep (se 1 (by rfl) ⟨357245, by rfl⟩ : syracuseStep 476327 = 714491) B714491
theorem B476351 : Blo 475787 476351 := bstep (se 1 (by rfl) ⟨357263, by rfl⟩ : syracuseStep 476351 = 714527) B714527
theorem B476383 : Blo 475787 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B476463 : Blo 475787 476463 := bstep (se 1 (by rfl) ⟨357347, by rfl⟩ : syracuseStep 476463 = 714695) B714695
theorem B1361249 : Blo 475787 1361249 := bstep (se 2 (by rfl) ⟨510468, by rfl⟩ : syracuseStep 1361249 = 1020937) B1020937
theorem B13813091 : Blo 475787 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B476699 : Blo 475787 476699 := bstep (se 1 (by rfl) ⟨357524, by rfl⟩ : syracuseStep 476699 = 715049) B715049
theorem B476703 : Blo 475787 476703 := bstep (se 1 (by rfl) ⟨357527, by rfl⟩ : syracuseStep 476703 = 715055) B715055
theorem B476863 : Blo 475787 476863 := bstep (se 1 (by rfl) ⟨357647, by rfl⟩ : syracuseStep 476863 = 715295) B715295
theorem B804647 : Blo 475787 804647 := bstep (se 1 (by rfl) ⟨603485, by rfl⟩ : syracuseStep 804647 = 1206971) B1206971
theorem B4376393 : Blo 475787 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B477119 : Blo 475787 477119 := bstep (se 1 (by rfl) ⟨357839, by rfl⟩ : syracuseStep 477119 = 715679) B715679
theorem B477151 : Blo 475787 477151 := bstep (se 1 (by rfl) ⟨357863, by rfl⟩ : syracuseStep 477151 = 715727) B715727
theorem B968687 : Blo 475787 968687 := bstep (se 1 (by rfl) ⟨726515, by rfl⟩ : syracuseStep 968687 = 1453031) B1453031
theorem B477211 : Blo 475787 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B477215 : Blo 475787 477215 := bstep (se 1 (by rfl) ⟨357911, by rfl⟩ : syracuseStep 477215 = 715823) B715823
theorem B477231 : Blo 475787 477231 := bstep (se 1 (by rfl) ⟨357923, by rfl⟩ : syracuseStep 477231 = 715847) B715847
theorem B477407 : Blo 475787 477407 := bstep (se 1 (by rfl) ⟨358055, by rfl⟩ : syracuseStep 477407 = 716111) B716111
theorem B477467 : Blo 475787 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B477567 : Blo 475787 477567 := bstep (se 1 (by rfl) ⟨358175, by rfl⟩ : syracuseStep 477567 = 716351) B716351
theorem B477743 : Blo 475787 477743 := bstep (se 1 (by rfl) ⟨358307, by rfl⟩ : syracuseStep 477743 = 716615) B716615
theorem B510511 : Blo 475787 510511 := bstep (se 1 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 510511 = 765767) B765767
theorem B477799 : Blo 475787 477799 := bstep (se 1 (by rfl) ⟨358349, by rfl⟩ : syracuseStep 477799 = 716699) B716699
theorem B805673 : Blo 475787 805673 := bstep (se 2 (by rfl) ⟨302127, by rfl⟩ : syracuseStep 805673 = 604255) B604255
theorem B805801 : Blo 475787 805801 := bstep (se 2 (by rfl) ⟨302175, by rfl⟩ : syracuseStep 805801 = 604351) B604351
theorem B478175 : Blo 475787 478175 := bstep (se 1 (by rfl) ⟨358631, by rfl⟩ : syracuseStep 478175 = 717263) B717263
theorem B478203 : Blo 475787 478203 := bstep (se 1 (by rfl) ⟨358652, by rfl⟩ : syracuseStep 478203 = 717305) B717305
theorem B68111381 : Blo 475787 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B805943 : Blo 475787 805943 := bstep (se 1 (by rfl) ⟨604457, by rfl⟩ : syracuseStep 805943 = 1208915) B1208915
theorem B478271 : Blo 475787 478271 := bstep (se 1 (by rfl) ⟨358703, by rfl⟩ : syracuseStep 478271 = 717407) B717407
theorem B478591 : Blo 475787 478591 := bstep (se 1 (by rfl) ⟨358943, by rfl⟩ : syracuseStep 478591 = 717887) B717887
theorem B478619 : Blo 475787 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B7359905 : Blo 475787 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B478687 : Blo 475787 478687 := bstep (se 1 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 478687 = 718031) B718031
theorem B806503 : Blo 475787 806503 := bstep (se 1 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 806503 = 1209755) B1209755
theorem B478823 : Blo 475787 478823 := bstep (se 1 (by rfl) ⟨359117, by rfl⟩ : syracuseStep 478823 = 718235) B718235
theorem B478971 : Blo 475787 478971 := bstep (se 1 (by rfl) ⟨359228, by rfl⟩ : syracuseStep 478971 = 718457) B718457
theorem B479039 : Blo 475787 479039 := bstep (se 1 (by rfl) ⟨359279, by rfl⟩ : syracuseStep 479039 = 718559) B718559
theorem B479103 : Blo 475787 479103 := bstep (se 1 (by rfl) ⟨359327, by rfl⟩ : syracuseStep 479103 = 718655) B718655
theorem B2412503 : Blo 475787 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B479215 : Blo 475787 479215 := bstep (se 1 (by rfl) ⟨359411, by rfl⟩ : syracuseStep 479215 = 718823) B718823
theorem B479227 : Blo 475787 479227 := bstep (se 1 (by rfl) ⟨359420, by rfl⟩ : syracuseStep 479227 = 718841) B718841
theorem B479295 : Blo 475787 479295 := bstep (se 1 (by rfl) ⟨359471, by rfl⟩ : syracuseStep 479295 = 718943) B718943
theorem B479335 : Blo 475787 479335 := bstep (se 1 (by rfl) ⟨359501, by rfl⟩ : syracuseStep 479335 = 719003) B719003
theorem B479359 : Blo 475787 479359 := bstep (se 1 (by rfl) ⟨359519, by rfl⟩ : syracuseStep 479359 = 719039) B719039
theorem B479387 : Blo 475787 479387 := bstep (se 1 (by rfl) ⟨359540, by rfl⟩ : syracuseStep 479387 = 719081) B719081
theorem B1724591 : Blo 475787 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B479591 : Blo 475787 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B2576765 : Blo 475787 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B2183561 : Blo 475787 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B479643 : Blo 475787 479643 := bstep (se 1 (by rfl) ⟨359732, by rfl⟩ : syracuseStep 479643 = 719465) B719465
theorem B3625559 : Blo 475787 3625559 := bstep (se 1 (by rfl) ⟨2719169, by rfl⟩ : syracuseStep 3625559 = 5438339) B5438339
theorem B906041 : Blo 475787 906041 := bstep (se 2 (by rfl) ⟨339765, by rfl⟩ : syracuseStep 906041 = 679531) B679531
theorem B1364951 : Blo 475787 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B906223 : Blo 475787 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B2184347 : Blo 475787 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B2413961 : Blo 475787 2413961 := bstep (se 2 (by rfl) ⟨905235, by rfl⟩ : syracuseStep 2413961 = 1810471) B1810471
theorem B1070567 : Blo 475787 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B6116903 : Blo 475787 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B1070729 : Blo 475787 1070729 := bstep (se 2 (by rfl) ⟨401523, by rfl⟩ : syracuseStep 1070729 = 803047) B803047
theorem B1070747 : Blo 475787 1070747 := bstep (se 1 (by rfl) ⟨803060, by rfl⟩ : syracuseStep 1070747 = 1606121) B1606121
theorem B1070945 : Blo 475787 1070945 := bstep (se 2 (by rfl) ⟨401604, by rfl⟩ : syracuseStep 1070945 = 803209) B803209
theorem B1071143 : Blo 475787 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B1366055 : Blo 475787 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B1071323 : Blo 475787 1071323 := bstep (se 1 (by rfl) ⟨803492, by rfl⟩ : syracuseStep 1071323 = 1606985) B1606985
theorem B1071521 : Blo 475787 1071521 := bstep (se 2 (by rfl) ⟨401820, by rfl⟩ : syracuseStep 1071521 = 803641) B803641
theorem B1071593 : Blo 475787 1071593 := bstep (se 2 (by rfl) ⟨401847, by rfl⟩ : syracuseStep 1071593 = 803695) B803695
theorem B2415257 : Blo 475787 2415257 := bstep (se 2 (by rfl) ⟨905721, by rfl⟩ : syracuseStep 2415257 = 1811443) B1811443
theorem B875375 : Blo 475787 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B2416067 : Blo 475787 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B3432223 : Blo 475787 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B2580311 : Blo 475787 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B1073051 : Blo 475787 1073051 := bstep (se 1 (by rfl) ⟨804788, by rfl⟩ : syracuseStep 1073051 = 1609577) B1609577
theorem B15294521 : Blo 475787 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1073465 : Blo 475787 1073465 := bstep (se 2 (by rfl) ⟨402549, by rfl⟩ : syracuseStep 1073465 = 805099) B805099
theorem B909625 : Blo 475787 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B6873673 : Blo 475787 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B1073951 : Blo 475787 1073951 := bstep (se 1 (by rfl) ⟨805463, by rfl⟩ : syracuseStep 1073951 = 1610927) B1610927
theorem B910111 : Blo 475787 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B3629933 : Blo 475787 3629933 := bstep (se 3 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 3629933 = 1361225) B1361225
theorem B13100039 : Blo 475787 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B713849 : Blo 475787 713849 := bstep (se 2 (by rfl) ⟨267693, by rfl⟩ : syracuseStep 713849 = 535387) B535387
theorem B2712791 : Blo 475787 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B583195 : Blo 475787 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B1074761 : Blo 475787 1074761 := bstep (se 2 (by rfl) ⟨403035, by rfl⟩ : syracuseStep 1074761 = 806071) B806071
theorem B4351583 : Blo 475787 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B2319997 : Blo 475787 2319997 := bstep (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) B869999
theorem B714719 : Blo 475787 714719 := bstep (se 1 (by rfl) ⟨536039, by rfl⟩ : syracuseStep 714719 = 1072079) B1072079
theorem B714731 : Blo 475787 714731 := bstep (se 1 (by rfl) ⟨536048, by rfl⟩ : syracuseStep 714731 = 1072097) B1072097
theorem B1075193 : Blo 475787 1075193 := bstep (se 2 (by rfl) ⟨403197, by rfl⟩ : syracuseStep 1075193 = 806395) B806395
theorem B714779 : Blo 475787 714779 := bstep (se 1 (by rfl) ⟨536084, by rfl⟩ : syracuseStep 714779 = 1072169) B1072169
theorem B1075247 : Blo 475787 1075247 := bstep (se 1 (by rfl) ⟨806435, by rfl⟩ : syracuseStep 1075247 = 1612871) B1612871
theorem B1075283 : Blo 475787 1075283 := bstep (se 1 (by rfl) ⟨806462, by rfl⟩ : syracuseStep 1075283 = 1612925) B1612925
theorem B1206535 : Blo 475787 1206535 := bstep (se 1 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 1206535 = 1809803) B1809803
theorem B1075463 : Blo 475787 1075463 := bstep (se 1 (by rfl) ⟨806597, by rfl⟩ : syracuseStep 1075463 = 1613195) B1613195
theorem B715145 : Blo 475787 715145 := bstep (se 2 (by rfl) ⟨268179, by rfl⟩ : syracuseStep 715145 = 536359) B536359
theorem B1075769 : Blo 475787 1075769 := bstep (se 2 (by rfl) ⟨403413, by rfl⟩ : syracuseStep 1075769 = 806827) B806827
theorem B1076489 : Blo 475787 1076489 := bstep (se 2 (by rfl) ⟨403683, by rfl⟩ : syracuseStep 1076489 = 807367) B807367
theorem B716087 : Blo 475787 716087 := bstep (se 1 (by rfl) ⟨537065, by rfl⟩ : syracuseStep 716087 = 1074131) B1074131
theorem B716255 : Blo 475787 716255 := bstep (se 1 (by rfl) ⟨537191, by rfl⟩ : syracuseStep 716255 = 1074383) B1074383
theorem B716471 : Blo 475787 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B1044193 : Blo 475787 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B716681 : Blo 475787 716681 := bstep (se 2 (by rfl) ⟨268755, by rfl⟩ : syracuseStep 716681 = 537511) B537511
theorem B1535993 : Blo 475787 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B716927 : Blo 475787 716927 := bstep (se 1 (by rfl) ⟨537695, by rfl⟩ : syracuseStep 716927 = 1075391) B1075391
theorem B1077479 : Blo 475787 1077479 := bstep (se 1 (by rfl) ⟨808109, by rfl⟩ : syracuseStep 1077479 = 1616219) B1616219
theorem B2912537 : Blo 475787 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B1077659 : Blo 475787 1077659 := bstep (se 1 (by rfl) ⟨808244, by rfl⟩ : syracuseStep 1077659 = 1616489) B1616489
theorem B1208783 : Blo 475787 1208783 := bstep (se 1 (by rfl) ⟨906587, by rfl⟩ : syracuseStep 1208783 = 1813175) B1813175
theorem B2650583 : Blo 475787 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B9204263 : Blo 475787 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B717563 : Blo 475787 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B1078343 : Blo 475787 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B718007 : Blo 475787 718007 := bstep (se 1 (by rfl) ⟨538505, by rfl⟩ : syracuseStep 718007 = 1077011) B1077011
theorem B1078523 : Blo 475787 1078523 := bstep (se 1 (by rfl) ⟨808892, by rfl⟩ : syracuseStep 1078523 = 1617785) B1617785
theorem B2291111 : Blo 475787 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B718247 : Blo 475787 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1078739 : Blo 475787 1078739 := bstep (se 1 (by rfl) ⟨809054, by rfl⟩ : syracuseStep 1078739 = 1618109) B1618109
theorem B6125057 : Blo 475787 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B718427 : Blo 475787 718427 := bstep (se 1 (by rfl) ⟨538820, by rfl⟩ : syracuseStep 718427 = 1077641) B1077641
theorem B1079009 : Blo 475787 1079009 := bstep (se 2 (by rfl) ⟨404628, by rfl⟩ : syracuseStep 1079009 = 809257) B809257
theorem B718889 : Blo 475787 718889 := bstep (se 2 (by rfl) ⟨269583, by rfl⟩ : syracuseStep 718889 = 539167) B539167
theorem B718919 : Blo 475787 718919 := bstep (se 1 (by rfl) ⟨539189, by rfl⟩ : syracuseStep 718919 = 1078379) B1078379
theorem B6027709 : Blo 475787 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B719303 : Blo 475787 719303 := bstep (se 1 (by rfl) ⟨539477, by rfl⟩ : syracuseStep 719303 = 1078955) B1078955
theorem B2718305 : Blo 475787 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B719519 : Blo 475787 719519 := bstep (se 1 (by rfl) ⟨539639, by rfl⟩ : syracuseStep 719519 = 1079279) B1079279
theorem B719663 : Blo 475787 719663 := bstep (se 1 (by rfl) ⟨539747, by rfl⟩ : syracuseStep 719663 = 1079495) B1079495
theorem B1375133 : Blo 475787 1375133 := bstep (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) B515675
theorem B1932511 : Blo 475787 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B818603 : Blo 475787 818603 := bstep (se 1 (by rfl) ⟨613952, by rfl⟩ : syracuseStep 818603 = 1227905) B1227905
theorem B4095431 : Blo 475787 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B9273041 : Blo 475787 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B37715705 : Blo 475787 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B1212691 : Blo 475787 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B983353 : Blo 475787 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B1638713 : Blo 475787 1638713 := bstep (se 2 (by rfl) ⟨614517, by rfl⟩ : syracuseStep 1638713 = 1229035) B1229035
theorem B1212833 : Blo 475787 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B3867095 : Blo 475787 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2720537 : Blo 475787 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B9208727 : Blo 475787 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B1213481 : Blo 475787 1213481 := bstep (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) B910111
theorem B2917595 : Blo 475787 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B11602439 : Blo 475787 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B1608335 : Blo 475787 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B1149727 : Blo 475787 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B1608713 : Blo 475787 1608713 := bstep (se 2 (by rfl) ⟨603267, by rfl⟩ : syracuseStep 1608713 = 1206535) B1206535
theorem B2624879 : Blo 475787 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2592161 : Blo 475787 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B1609307 : Blo 475787 1609307 := bstep (se 1 (by rfl) ⟨1206980, by rfl⟩ : syracuseStep 1609307 = 2413961) B2413961
theorem B2723453 : Blo 475787 2723453 := bstep (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) B1021295
theorem B28348645 : Blo 475787 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B1610171 : Blo 475787 1610171 := bstep (se 1 (by rfl) ⟨1207628, by rfl⟩ : syracuseStep 1610171 = 2415257) B2415257
theorem B1610711 : Blo 475787 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B10196347 : Blo 475787 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B7346065 : Blo 475787 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B858223 : Blo 475787 858223 := bstep (se 1 (by rfl) ⟨643667, by rfl⟩ : syracuseStep 858223 = 1287335) B1287335
theorem B1808527 : Blo 475787 1808527 := bstep (se 1 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 1808527 = 2712791) B2712791
theorem B2628935 : Blo 475787 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B1023995 : Blo 475787 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B729143 : Blo 475787 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B1941691 : Blo 475787 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B1810745 : Blo 475787 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B6136175 : Blo 475787 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B762409 : Blo 475787 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B8036945 : Blo 475787 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1812203 : Blo 475787 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B2730287 : Blo 475787 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B25143803 : Blo 475787 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B535495 : Blo 475787 535495 := bstep (se 1 (by rfl) ⟨401621, by rfl⟩ : syracuseStep 535495 = 803243) B803243
theorem B2730995 : Blo 475787 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B14658731 : Blo 475787 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B2043103 : Blo 475787 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B535855 : Blo 475787 535855 := bstep (se 1 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 535855 = 803783) B803783
theorem B1715651 : Blo 475787 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1093151 : Blo 475787 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B2731745 : Blo 475787 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B1814359 : Blo 475787 1814359 := bstep (se 1 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 1814359 = 2721539) B2721539
theorem B536431 : Blo 475787 536431 := bstep (se 1 (by rfl) ⟨402323, by rfl⟩ : syracuseStep 536431 = 804647) B804647
theorem B1355849 : Blo 475787 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B1618055 : Blo 475787 1618055 := bstep (se 1 (by rfl) ⟨1213541, by rfl⟩ : syracuseStep 1618055 = 2427083) B2427083
theorem B1356031 : Blo 475787 1356031 := bstep (se 1 (by rfl) ⟨1017023, by rfl⟩ : syracuseStep 1356031 = 2034047) B2034047
theorem B3453191 : Blo 475787 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B1618217 : Blo 475787 1618217 := bstep (se 2 (by rfl) ⟨606831, by rfl⟩ : syracuseStep 1618217 = 1213663) B1213663
theorem B537115 : Blo 475787 537115 := bstep (se 1 (by rfl) ⟨402836, by rfl⟩ : syracuseStep 537115 = 805673) B805673
theorem B1815119 : Blo 475787 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B537295 : Blo 475787 537295 := bstep (se 1 (by rfl) ⟨402971, by rfl⟩ : syracuseStep 537295 = 805943) B805943
theorem B3453677 : Blo 475787 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B3060503 : Blo 475787 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B1291063 : Blo 475787 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1749815 : Blo 475787 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1356601 : Blo 475787 1356601 := bstep (se 2 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 1356601 = 1017451) B1017451
theorem B3093329 : Blo 475787 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1717843 : Blo 475787 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1455707 : Blo 475787 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B16562015 : Blo 475787 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B604027 : Blo 475787 604027 := bstep (se 1 (by rfl) ⟨453020, by rfl⟩ : syracuseStep 604027 = 906041) B906041
theorem B1456231 : Blo 475787 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B4077935 : Blo 475787 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B3062245 : Blo 475787 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B768503 : Blo 475787 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B10598951 : Blo 475787 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B4602905 : Blo 475787 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B1392257 : Blo 475787 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B1720207 : Blo 475787 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B8733359 : Blo 475787 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B475899 : Blo 475787 475899 := bstep (se 1 (by rfl) ⟨356924, by rfl⟩ : syracuseStep 475899 = 713849) B713849
theorem B2901055 : Blo 475787 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B476479 : Blo 475787 476479 := bstep (se 1 (by rfl) ⟨357359, by rfl⟩ : syracuseStep 476479 = 714719) B714719
theorem B476487 : Blo 475787 476487 := bstep (se 1 (by rfl) ⟨357365, by rfl⟩ : syracuseStep 476487 = 714731) B714731
theorem B476519 : Blo 475787 476519 := bstep (se 1 (by rfl) ⟨357389, by rfl⟩ : syracuseStep 476519 = 714779) B714779
theorem B476763 : Blo 475787 476763 := bstep (se 1 (by rfl) ⟨357572, by rfl⟩ : syracuseStep 476763 = 715145) B715145
theorem B477391 : Blo 475787 477391 := bstep (se 1 (by rfl) ⟨358043, by rfl⟩ : syracuseStep 477391 = 716087) B716087
theorem B477503 : Blo 475787 477503 := bstep (se 1 (by rfl) ⟨358127, by rfl⟩ : syracuseStep 477503 = 716255) B716255
theorem B477647 : Blo 475787 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B477787 : Blo 475787 477787 := bstep (se 1 (by rfl) ⟨358340, by rfl⟩ : syracuseStep 477787 = 716681) B716681
theorem B477951 : Blo 475787 477951 := bstep (se 1 (by rfl) ⟨358463, by rfl⟩ : syracuseStep 477951 = 716927) B716927
theorem B805855 : Blo 475787 805855 := bstep (se 1 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 805855 = 1208783) B1208783
theorem B478375 : Blo 475787 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B1363321 : Blo 475787 1363321 := bstep (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) B1022491
theorem B478671 : Blo 475787 478671 := bstep (se 1 (by rfl) ⟨359003, by rfl⟩ : syracuseStep 478671 = 718007) B718007
theorem B1527407 : Blo 475787 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B478831 : Blo 475787 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B4083371 : Blo 475787 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B3067577 : Blo 475787 3067577 := bstep (se 2 (by rfl) ⟨1150341, by rfl⟩ : syracuseStep 3067577 = 2300683) B2300683
theorem B478951 : Blo 475787 478951 := bstep (se 1 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 478951 = 718427) B718427
theorem B905023 : Blo 475787 905023 := bstep (se 1 (by rfl) ⟨678767, by rfl⟩ : syracuseStep 905023 = 1357535) B1357535
theorem B479259 : Blo 475787 479259 := bstep (se 1 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 479259 = 718889) B718889
theorem B479279 : Blo 475787 479279 := bstep (se 1 (by rfl) ⟨359459, by rfl⟩ : syracuseStep 479279 = 718919) B718919
theorem B18305189 : Blo 475787 18305189 := bstep (se 4 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 18305189 = 3432223) B3432223
theorem B2576681 : Blo 475787 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B479535 : Blo 475787 479535 := bstep (se 1 (by rfl) ⟨359651, by rfl⟩ : syracuseStep 479535 = 719303) B719303
theorem B1528253 : Blo 475787 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B479679 : Blo 475787 479679 := bstep (se 1 (by rfl) ⟨359759, by rfl⟩ : syracuseStep 479679 = 719519) B719519
theorem B479775 : Blo 475787 479775 := bstep (se 1 (by rfl) ⟨359831, by rfl⟩ : syracuseStep 479775 = 719663) B719663
theorem B807529 : Blo 475787 807529 := bstep (se 2 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 807529 = 605647) B605647
theorem B39703159 : Blo 475787 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B545735 : Blo 475787 545735 := bstep (se 1 (by rfl) ⟨409301, by rfl⟩ : syracuseStep 545735 = 818603) B818603
theorem B6182027 : Blo 475787 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B13129381 : Blo 475787 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B1070783 : Blo 475787 1070783 := bstep (se 1 (by rfl) ⟨803087, by rfl⟩ : syracuseStep 1070783 = 1606175) B1606175
theorem B9164897 : Blo 475787 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B907499 : Blo 475787 907499 := bstep (se 1 (by rfl) ⟨680624, by rfl⟩ : syracuseStep 907499 = 1361249) B1361249
theorem B38230625 : Blo 475787 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B645791 : Blo 475787 645791 := bstep (se 1 (by rfl) ⟨484343, by rfl⟩ : syracuseStep 645791 = 968687) B968687
theorem B1071935 : Blo 475787 1071935 := bstep (se 1 (by rfl) ⟨803951, by rfl⟩ : syracuseStep 1071935 = 1607903) B1607903
theorem B679195 : Blo 475787 679195 := bstep (se 1 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 679195 = 1018793) B1018793
theorem B1531163 : Blo 475787 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B777593 : Blo 475787 777593 := bstep (se 2 (by rfl) ⟨291597, by rfl⟩ : syracuseStep 777593 = 583195) B583195
theorem B1072511 : Blo 475787 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B613759 : Blo 475787 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B45505925 : Blo 475787 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B4906603 : Blo 475787 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B2417039 : Blo 475787 2417039 := bstep (se 1 (by rfl) ⟨1812779, by rfl⟩ : syracuseStep 2417039 = 3625559) B3625559
theorem B909967 : Blo 475787 909967 := bstep (se 1 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 909967 = 1364951) B1364951
theorem B1204895 : Blo 475787 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B680681 : Blo 475787 680681 := bstep (se 2 (by rfl) ⟨255255, by rfl⟩ : syracuseStep 680681 = 510511) B510511
theorem B713711 : Blo 475787 713711 := bstep (se 1 (by rfl) ⟨535283, by rfl⟩ : syracuseStep 713711 = 1070567) B1070567
theorem B713819 : Blo 475787 713819 := bstep (se 1 (by rfl) ⟨535364, by rfl⟩ : syracuseStep 713819 = 1070729) B1070729
theorem B713831 : Blo 475787 713831 := bstep (se 1 (by rfl) ⟨535373, by rfl⟩ : syracuseStep 713831 = 1070747) B1070747
theorem B1205351 : Blo 475787 1205351 := bstep (se 1 (by rfl) ⟨904013, by rfl⟩ : syracuseStep 1205351 = 1808027) B1808027
theorem B1074401 : Blo 475787 1074401 := bstep (se 2 (by rfl) ⟨402900, by rfl⟩ : syracuseStep 1074401 = 805801) B805801
theorem B713963 : Blo 475787 713963 := bstep (se 1 (by rfl) ⟨535472, by rfl⟩ : syracuseStep 713963 = 1070945) B1070945
theorem B714095 : Blo 475787 714095 := bstep (se 1 (by rfl) ⟨535571, by rfl⟩ : syracuseStep 714095 = 1071143) B1071143
theorem B910703 : Blo 475787 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B2450843 : Blo 475787 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B714215 : Blo 475787 714215 := bstep (se 1 (by rfl) ⟨535661, by rfl⟩ : syracuseStep 714215 = 1071323) B1071323
theorem B714347 : Blo 475787 714347 := bstep (se 1 (by rfl) ⟨535760, by rfl⟩ : syracuseStep 714347 = 1071521) B1071521
theorem B714395 : Blo 475787 714395 := bstep (se 1 (by rfl) ⟨535796, by rfl⟩ : syracuseStep 714395 = 1071593) B1071593
theorem B714617 : Blo 475787 714617 := bstep (se 2 (by rfl) ⟨267981, by rfl⟩ : syracuseStep 714617 = 535963) B535963
theorem B1075067 : Blo 475787 1075067 := bstep (se 1 (by rfl) ⟨806300, by rfl⟩ : syracuseStep 1075067 = 1612601) B1612601
theorem B2713499 : Blo 475787 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B583583 : Blo 475787 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B1075337 : Blo 475787 1075337 := bstep (se 2 (by rfl) ⟨403251, by rfl⟩ : syracuseStep 1075337 = 806503) B806503
theorem B3631391 : Blo 475787 3631391 := bstep (se 1 (by rfl) ⟨2723543, by rfl⟩ : syracuseStep 3631391 = 5447087) B5447087
theorem B1469011 : Blo 475787 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B715367 : Blo 475787 715367 := bstep (se 1 (by rfl) ⟨536525, by rfl⟩ : syracuseStep 715367 = 1073051) B1073051
theorem B715643 : Blo 475787 715643 := bstep (se 1 (by rfl) ⟨536732, by rfl⟩ : syracuseStep 715643 = 1073465) B1073465
theorem B5172173 : Blo 475787 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B1076219 : Blo 475787 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B715913 : Blo 475787 715913 := bstep (se 2 (by rfl) ⟨268467, by rfl⟩ : syracuseStep 715913 = 536935) B536935
theorem B1076399 : Blo 475787 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B715967 : Blo 475787 715967 := bstep (se 1 (by rfl) ⟨536975, by rfl⟩ : syracuseStep 715967 = 1073951) B1073951
theorem B3632363 : Blo 475787 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B2419955 : Blo 475787 2419955 := bstep (se 1 (by rfl) ⟨1814966, by rfl⟩ : syracuseStep 2419955 = 3629933) B3629933
theorem B716507 : Blo 475787 716507 := bstep (se 1 (by rfl) ⟨537380, by rfl⟩ : syracuseStep 716507 = 1074761) B1074761
theorem B1077119 : Blo 475787 1077119 := bstep (se 1 (by rfl) ⟨807839, by rfl⟩ : syracuseStep 1077119 = 1615679) B1615679
theorem B1208297 : Blo 475787 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B716777 : Blo 475787 716777 := bstep (se 2 (by rfl) ⟨268791, by rfl⟩ : syracuseStep 716777 = 537583) B537583
theorem B716795 : Blo 475787 716795 := bstep (se 1 (by rfl) ⟨537596, by rfl⟩ : syracuseStep 716795 = 1075193) B1075193
theorem B716831 : Blo 475787 716831 := bstep (se 1 (by rfl) ⟨537623, by rfl⟩ : syracuseStep 716831 = 1075247) B1075247
theorem B716855 : Blo 475787 716855 := bstep (se 1 (by rfl) ⟨537641, by rfl⟩ : syracuseStep 716855 = 1075283) B1075283
theorem B716975 : Blo 475787 716975 := bstep (se 1 (by rfl) ⟨537731, by rfl⟩ : syracuseStep 716975 = 1075463) B1075463
theorem B2421089 : Blo 475787 2421089 := bstep (se 2 (by rfl) ⟨907908, by rfl⟩ : syracuseStep 2421089 = 1815817) B1815817
theorem B717179 : Blo 475787 717179 := bstep (se 1 (by rfl) ⟨537884, by rfl⟩ : syracuseStep 717179 = 1075769) B1075769
theorem B14119343 : Blo 475787 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B717449 : Blo 475787 717449 := bstep (se 2 (by rfl) ⟨269043, by rfl⟩ : syracuseStep 717449 = 538087) B538087
theorem B717659 : Blo 475787 717659 := bstep (se 1 (by rfl) ⟨538244, by rfl⟩ : syracuseStep 717659 = 1076489) B1076489
theorem B1078127 : Blo 475787 1078127 := bstep (se 1 (by rfl) ⟨808595, by rfl⟩ : syracuseStep 1078127 = 1617191) B1617191
theorem B717689 : Blo 475787 717689 := bstep (se 2 (by rfl) ⟨269133, by rfl⟩ : syracuseStep 717689 = 538267) B538267
theorem B2421737 : Blo 475787 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B3667021 : Blo 475787 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B181630349 : Blo 475787 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B718319 : Blo 475787 718319 := bstep (se 1 (by rfl) ⟨538739, by rfl⟩ : syracuseStep 718319 = 1077479) B1077479
theorem B718439 : Blo 475787 718439 := bstep (se 1 (by rfl) ⟨538829, by rfl⟩ : syracuseStep 718439 = 1077659) B1077659
theorem B1767055 : Blo 475787 1767055 := bstep (se 1 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 1767055 = 2650583) B2650583
theorem B718895 : Blo 475787 718895 := bstep (se 1 (by rfl) ⟨539171, by rfl⟩ : syracuseStep 718895 = 1078343) B1078343
theorem B1210535 : Blo 475787 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B719015 : Blo 475787 719015 := bstep (se 1 (by rfl) ⟨539261, by rfl⟩ : syracuseStep 719015 = 1078523) B1078523
theorem B2423033 : Blo 475787 2423033 := bstep (se 2 (by rfl) ⟨908637, by rfl⟩ : syracuseStep 2423033 = 1817275) B1817275
theorem B719159 : Blo 475787 719159 := bstep (se 1 (by rfl) ⟨539369, by rfl⟩ : syracuseStep 719159 = 1078739) B1078739
theorem B1145249 : Blo 475787 1145249 := bstep (se 2 (by rfl) ⟨429468, by rfl⟩ : syracuseStep 1145249 = 858937) B858937
theorem B719339 : Blo 475787 719339 := bstep (se 1 (by rfl) ⟨539504, by rfl⟩ : syracuseStep 719339 = 1079009) B1079009
theorem B1211183 : Blo 475787 1211183 := bstep (se 1 (by rfl) ⟨908387, by rfl⟩ : syracuseStep 1211183 = 1816775) B1816775
theorem B13073761 : Blo 475787 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B1211831 : Blo 475787 1211831 := bstep (se 1 (by rfl) ⟨908873, by rfl⟩ : syracuseStep 1211831 = 1817747) B1817747
theorem B2588921 : Blo 475787 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B1311137 : Blo 475787 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B1016545 : Blo 475787 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B1213289 : Blo 475787 1213289 := bstep (se 2 (by rfl) ⟨454983, by rfl⟩ : syracuseStep 1213289 = 909967) B909967
theorem B3868073 : Blo 475787 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B7734959 : Blo 475787 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B1018271 : Blo 475787 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B2722247 : Blo 475787 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B1018835 : Blo 475787 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B2428541 : Blo 475787 2428541 := bstep (se 3 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 2428541 = 910703) B910703
theorem B2724137 : Blo 475787 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B604771093 : Blo 475787 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B1020775 : Blo 475787 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B1611359 : Blo 475787 1611359 := bstep (se 1 (by rfl) ⟨1208519, by rfl⟩ : syracuseStep 1611359 = 2417039) B2417039
theorem B1808041 : Blo 475787 1808041 := bstep (se 2 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 1808041 = 1356031) B1356031
theorem B1808801 : Blo 475787 1808801 := bstep (se 2 (by rfl) ⟨678300, by rfl⟩ : syracuseStep 1808801 = 1356601) B1356601
theorem B1808999 : Blo 475787 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B3448115 : Blo 475787 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B9772487 : Blo 475787 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B1613303 : Blo 475787 1613303 := bstep (se 1 (by rfl) ⟨1209977, by rfl⟩ : syracuseStep 1613303 = 2419955) B2419955
theorem B17505841 : Blo 475787 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B728767 : Blo 475787 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B1941641 : Blo 475787 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B2302127 : Blo 475787 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B1614059 : Blo 475787 1614059 := bstep (se 1 (by rfl) ⟨1210544, by rfl⟩ : syracuseStep 1614059 = 2421089) B2421089
theorem B9412895 : Blo 475787 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B2302451 : Blo 475787 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B2040335 : Blo 475787 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B1614491 : Blo 475787 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B121086899 : Blo 475787 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B1615355 : Blo 475787 1615355 := bstep (se 1 (by rfl) ⟨1211516, by rfl⟩ : syracuseStep 1615355 = 2423033) B2423033
theorem B763499 : Blo 475787 763499 := bstep (se 1 (by rfl) ⟨572624, by rfl⟩ : syracuseStep 763499 = 1145249) B1145249
theorem B928171 : Blo 475787 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B1092475 : Blo 475787 1092475 := bstep (se 1 (by rfl) ⟨819356, by rfl⟩ : syracuseStep 1092475 = 1638713) B1638713
theorem B1616921 : Blo 475787 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B1813691 : Blo 475787 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B6139151 : Blo 475787 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B1945063 : Blo 475787 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B1815149 : Blo 475787 1815149 := bstep (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) B680681
theorem B1749919 : Blo 475787 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1815635 : Blo 475787 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B2045051 : Blo 475787 2045051 := bstep (se 1 (by rfl) ⟨1533788, by rfl⟩ : syracuseStep 2045051 = 3067577) B3067577
theorem B1455293 : Blo 475787 1455293 := bstep (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) B545735
theorem B12203459 : Blo 475787 12203459 := bstep (se 1 (by rfl) ⟨9152594, by rfl⟩ : syracuseStep 12203459 = 18305189) B18305189
theorem B1717787 : Blo 475787 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B6109931 : Blo 475787 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B604999 : Blo 475787 604999 := bstep (se 1 (by rfl) ⟨453749, by rfl⟩ : syracuseStep 604999 = 907499) B907499
theorem B1817761 : Blo 475787 1817761 := bstep (se 2 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 1817761 = 1363321) B1363321
theorem B1752623 : Blo 475787 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B1556221 : Blo 475787 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B5357963 : Blo 475787 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B803263 : Blo 475787 803263 := bstep (se 1 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 803263 = 1204895) B1204895
theorem B475807 : Blo 475787 475807 := bstep (se 1 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 475807 = 713711) B713711
theorem B475879 : Blo 475787 475879 := bstep (se 1 (by rfl) ⟨356909, by rfl⟩ : syracuseStep 475879 = 713819) B713819
theorem B475887 : Blo 475787 475887 := bstep (se 1 (by rfl) ⟨356915, by rfl⟩ : syracuseStep 475887 = 713831) B713831
theorem B803567 : Blo 475787 803567 := bstep (se 1 (by rfl) ⟨602675, by rfl⟩ : syracuseStep 803567 = 1205351) B1205351
theorem B475975 : Blo 475787 475975 := bstep (se 1 (by rfl) ⟨356981, by rfl⟩ : syracuseStep 475975 = 713963) B713963
theorem B52937545 : Blo 475787 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B476063 : Blo 475787 476063 := bstep (se 1 (by rfl) ⟨357047, by rfl⟩ : syracuseStep 476063 = 714095) B714095
theorem B476143 : Blo 475787 476143 := bstep (se 1 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 476143 = 714215) B714215
theorem B476231 : Blo 475787 476231 := bstep (se 1 (by rfl) ⟨357173, by rfl⟩ : syracuseStep 476231 = 714347) B714347
theorem B1721417 : Blo 475787 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B476263 : Blo 475787 476263 := bstep (se 1 (by rfl) ⟨357197, by rfl⟩ : syracuseStep 476263 = 714395) B714395
theorem B476411 : Blo 475787 476411 := bstep (se 1 (by rfl) ⟨357308, by rfl⟩ : syracuseStep 476411 = 714617) B714617
theorem B1820191 : Blo 475787 1820191 := bstep (se 1 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 1820191 = 2730287) B2730287
theorem B16762535 : Blo 475787 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B476911 : Blo 475787 476911 := bstep (se 1 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 476911 = 715367) B715367
theorem B1722109 : Blo 475787 1722109 := bstep (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) B645791
theorem B477095 : Blo 475787 477095 := bstep (se 1 (by rfl) ⟨357821, by rfl⟩ : syracuseStep 477095 = 715643) B715643
theorem B1820663 : Blo 475787 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B477275 : Blo 475787 477275 := bstep (se 1 (by rfl) ⟨357956, by rfl⟩ : syracuseStep 477275 = 715913) B715913
theorem B477311 : Blo 475787 477311 := bstep (se 1 (by rfl) ⟨357983, by rfl⟩ : syracuseStep 477311 = 715967) B715967
theorem B477671 : Blo 475787 477671 := bstep (se 1 (by rfl) ⟨358253, by rfl⟩ : syracuseStep 477671 = 716507) B716507
theorem B1821163 : Blo 475787 1821163 := bstep (se 1 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 1821163 = 2731745) B2731745
theorem B805369 : Blo 475787 805369 := bstep (se 2 (by rfl) ⟨302013, by rfl⟩ : syracuseStep 805369 = 604027) B604027
theorem B805531 : Blo 475787 805531 := bstep (se 1 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 805531 = 1208297) B1208297
theorem B477851 : Blo 475787 477851 := bstep (se 1 (by rfl) ⟨358388, by rfl⟩ : syracuseStep 477851 = 716777) B716777
theorem B477863 : Blo 475787 477863 := bstep (se 1 (by rfl) ⟨358397, by rfl⟩ : syracuseStep 477863 = 716795) B716795
theorem B477887 : Blo 475787 477887 := bstep (se 1 (by rfl) ⟨358415, by rfl⟩ : syracuseStep 477887 = 716831) B716831
theorem B477903 : Blo 475787 477903 := bstep (se 1 (by rfl) ⟨358427, by rfl⟩ : syracuseStep 477903 = 716855) B716855
theorem B903899 : Blo 475787 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B477983 : Blo 475787 477983 := bstep (se 1 (by rfl) ⟨358487, by rfl⟩ : syracuseStep 477983 = 716975) B716975
theorem B2411369 : Blo 475787 2411369 := bstep (se 2 (by rfl) ⟨904263, by rfl⟩ : syracuseStep 2411369 = 1808527) B1808527
theorem B478119 : Blo 475787 478119 := bstep (se 1 (by rfl) ⟨358589, by rfl⟩ : syracuseStep 478119 = 717179) B717179
theorem B478299 : Blo 475787 478299 := bstep (se 1 (by rfl) ⟨358724, by rfl⟩ : syracuseStep 478299 = 717449) B717449
theorem B1166543 : Blo 475787 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B478439 : Blo 475787 478439 := bstep (se 1 (by rfl) ⟨358829, by rfl⟩ : syracuseStep 478439 = 717659) B717659
theorem B478459 : Blo 475787 478459 := bstep (se 1 (by rfl) ⟨358844, by rfl⟩ : syracuseStep 478459 = 717689) B717689
theorem B4082993 : Blo 475787 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B478879 : Blo 475787 478879 := bstep (se 1 (by rfl) ⟨359159, by rfl⟩ : syracuseStep 478879 = 718319) B718319
theorem B970471 : Blo 475787 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B478959 : Blo 475787 478959 := bstep (se 1 (by rfl) ⟨359219, by rfl⟩ : syracuseStep 478959 = 718439) B718439
theorem B479263 : Blo 475787 479263 := bstep (se 1 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 479263 = 718895) B718895
theorem B807023 : Blo 475787 807023 := bstep (se 1 (by rfl) ⟨605267, by rfl⟩ : syracuseStep 807023 = 1210535) B1210535
theorem B479343 : Blo 475787 479343 := bstep (se 1 (by rfl) ⟨359507, by rfl⟩ : syracuseStep 479343 = 719015) B719015
theorem B479439 : Blo 475787 479439 := bstep (se 1 (by rfl) ⟨359579, by rfl⟩ : syracuseStep 479439 = 719159) B719159
theorem B479559 : Blo 475787 479559 := bstep (se 1 (by rfl) ⟨359669, by rfl⟩ : syracuseStep 479559 = 719339) B719339
theorem B512335 : Blo 475787 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B7065967 : Blo 475787 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B905593 : Blo 475787 905593 := bstep (se 2 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 905593 = 679195) B679195
theorem B807455 : Blo 475787 807455 := bstep (se 1 (by rfl) ⟨605591, by rfl⟩ : syracuseStep 807455 = 1211183) B1211183
theorem B3068603 : Blo 475787 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B6542137 : Blo 475787 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B807887 : Blo 475787 807887 := bstep (se 1 (by rfl) ⟨605915, by rfl⟩ : syracuseStep 807887 = 1211831) B1211831
theorem B808555 : Blo 475787 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B2578063 : Blo 475787 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B5822239 : Blo 475787 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B808987 : Blo 475787 808987 := bstep (se 1 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 808987 = 1213481) B1213481
theorem B1072223 : Blo 475787 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B1072475 : Blo 475787 1072475 := bstep (se 1 (by rfl) ⟨804356, by rfl⟩ : syracuseStep 1072475 = 1608713) B1608713
theorem B1728107 : Blo 475787 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1072871 : Blo 475787 1072871 := bstep (se 1 (by rfl) ⟨804653, by rfl⟩ : syracuseStep 1072871 = 1609307) B1609307
theorem B1073447 : Blo 475787 1073447 := bstep (se 1 (by rfl) ⟨805085, by rfl⟩ : syracuseStep 1073447 = 1610171) B1610171
theorem B1073807 : Blo 475787 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B4121351 : Blo 475787 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1958681 : Blo 475787 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B1532969 : Blo 475787 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B713855 : Blo 475787 713855 := bstep (se 1 (by rfl) ⟨535391, by rfl⟩ : syracuseStep 713855 = 1070783) B1070783
theorem B713993 : Blo 475787 713993 := bstep (se 2 (by rfl) ⟨267747, by rfl⟩ : syracuseStep 713993 = 535495) B535495
theorem B1074473 : Blo 475787 1074473 := bstep (se 2 (by rfl) ⟨402927, by rfl⟩ : syracuseStep 1074473 = 805855) B805855
theorem B714473 : Blo 475787 714473 := bstep (se 2 (by rfl) ⟨267927, by rfl⟩ : syracuseStep 714473 = 535855) B535855
theorem B25487083 : Blo 475787 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B714623 : Blo 475787 714623 := bstep (se 1 (by rfl) ⟨535967, by rfl⟩ : syracuseStep 714623 = 1071935) B1071935
theorem B518395 : Blo 475787 518395 := bstep (se 1 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 518395 = 777593) B777593
theorem B715007 : Blo 475787 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B30337283 : Blo 475787 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B1206697 : Blo 475787 1206697 := bstep (se 2 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 1206697 = 905023) B905023
theorem B2419145 : Blo 475787 2419145 := bstep (se 2 (by rfl) ⟨907179, by rfl⟩ : syracuseStep 2419145 = 1814359) B1814359
theorem B715241 : Blo 475787 715241 := bstep (se 2 (by rfl) ⟨268215, by rfl⟩ : syracuseStep 715241 = 536431) B536431
theorem B682663 : Blo 475787 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B486095 : Blo 475787 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B1207163 : Blo 475787 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B4090783 : Blo 475787 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B19557445 : Blo 475787 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B716153 : Blo 475787 716153 := bstep (se 2 (by rfl) ⟨268557, by rfl⟩ : syracuseStep 716153 = 537115) B537115
theorem B1076705 : Blo 475787 1076705 := bstep (se 2 (by rfl) ⟨403764, by rfl⟩ : syracuseStep 1076705 = 807529) B807529
theorem B716267 : Blo 475787 716267 := bstep (se 1 (by rfl) ⟨537200, by rfl⟩ : syracuseStep 716267 = 1074401) B1074401
theorem B1633895 : Blo 475787 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B716393 : Blo 475787 716393 := bstep (se 2 (by rfl) ⟨268647, by rfl⟩ : syracuseStep 716393 = 537295) B537295
theorem B1208135 : Blo 475787 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B716711 : Blo 475787 716711 := bstep (se 1 (by rfl) ⟨537533, by rfl⟩ : syracuseStep 716711 = 1075067) B1075067
theorem B716891 : Blo 475787 716891 := bstep (se 1 (by rfl) ⟨537668, by rfl⟩ : syracuseStep 716891 = 1075337) B1075337
theorem B2420927 : Blo 475787 2420927 := bstep (se 1 (by rfl) ⟨1815695, by rfl⟩ : syracuseStep 2420927 = 3631391) B3631391
theorem B13595129 : Blo 475787 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B717479 : Blo 475787 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B2290457 : Blo 475787 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B717599 : Blo 475787 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B2421575 : Blo 475787 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B2356073 : Blo 475787 2356073 := bstep (se 2 (by rfl) ⟨883527, by rfl⟩ : syracuseStep 2356073 = 1767055) B1767055
theorem B1143767 : Blo 475787 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B9794753 : Blo 475787 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B718079 : Blo 475787 718079 := bstep (se 1 (by rfl) ⟨538559, by rfl⟩ : syracuseStep 718079 = 1077119) B1077119
theorem B1078703 : Blo 475787 1078703 := bstep (se 1 (by rfl) ⟨809027, by rfl⟩ : syracuseStep 1078703 = 1618055) B1618055
theorem B1144297 : Blo 475787 1144297 := bstep (se 2 (by rfl) ⟨429111, by rfl⟩ : syracuseStep 1144297 = 858223) B858223
theorem B1078811 : Blo 475787 1078811 := bstep (se 1 (by rfl) ⟨809108, by rfl⟩ : syracuseStep 1078811 = 1618217) B1618217
theorem B1210079 : Blo 475787 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B2062219 : Blo 475787 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B718751 : Blo 475787 718751 := bstep (se 1 (by rfl) ⟨539063, by rfl⟩ : syracuseStep 718751 = 1078127) B1078127
theorem B11041343 : Blo 475787 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B2718623 : Blo 475787 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B17431681 : Blo 475787 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B818345 : Blo 475787 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B2293609 : Blo 475787 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B3571975 : Blo 475787 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B25101053 : Blo 475787 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B70583393 : Blo 475787 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B11175023 : Blo 475787 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B1213775 : Blo 475787 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B1607579 : Blo 475787 1607579 := bstep (se 1 (by rfl) ⟨1205684, by rfl⟩ : syracuseStep 1607579 = 2411369) B2411369
theorem B2426921 : Blo 475787 2426921 := bstep (se 2 (by rfl) ⟨910095, by rfl⟩ : syracuseStep 2426921 = 1820191) B1820191
theorem B2721995 : Blo 475787 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B4950245 : Blo 475787 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B33982777 : Blo 475787 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B2296145 : Blo 475787 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B3050045 : Blo 475787 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B4590445 : Blo 475787 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B691193 : Blo 475787 691193 := bstep (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) B518395
theorem B1608929 : Blo 475787 1608929 := bstep (se 2 (by rfl) ⟨603348, by rfl⟩ : syracuseStep 1608929 = 1206697) B1206697
theorem B2428217 : Blo 475787 2428217 := bstep (se 2 (by rfl) ⟨910581, by rfl⟩ : syracuseStep 2428217 = 1821163) B1821163
theorem B2593417 : Blo 475787 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B2298743 : Blo 475787 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B1152071 : Blo 475787 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B1021979 : Blo 475787 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B2333225 : Blo 475787 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B20224855 : Blo 475787 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B1612763 : Blo 475787 1612763 := bstep (se 1 (by rfl) ⟨1209572, by rfl⟩ : syracuseStep 1612763 = 2419145) B2419145
theorem B1089263 : Blo 475787 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B1613951 : Blo 475787 1613951 := bstep (se 1 (by rfl) ⟨1210463, by rfl⟩ : syracuseStep 1613951 = 2420927) B2420927
theorem B1614383 : Blo 475787 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B6529835 : Blo 475787 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B8135639 : Blo 475787 8135639 := bstep (se 1 (by rfl) ⟨6101729, by rfl⟩ : syracuseStep 8135639 = 12203459) B12203459
theorem B23242241 : Blo 475787 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B4073287 : Blo 475787 4073287 := bstep (se 1 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 4073287 = 6109931) B6109931
theorem B1812415 : Blo 475787 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B23341121 : Blo 475787 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B2074961 : Blo 475787 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B3058145 : Blo 475787 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B535711 : Blo 475787 535711 := bstep (se 1 (by rfl) ⟨401783, by rfl⟩ : syracuseStep 535711 = 803567) B803567
theorem B1355393 : Blo 475787 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B5156639 : Blo 475787 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B1814831 : Blo 475787 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B2732453 : Blo 475787 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B5223149 : Blo 475787 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B1619027 : Blo 475787 1619027 := bstep (se 1 (by rfl) ⟨1214270, by rfl⟩ : syracuseStep 1619027 = 2428541) B2428541
theorem B538015 : Blo 475787 538015 := bstep (se 1 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 538015 = 807023) B807023
theorem B1816091 : Blo 475787 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B538303 : Blo 475787 538303 := bstep (se 1 (by rfl) ⟨403727, by rfl⟩ : syracuseStep 538303 = 807455) B807455
theorem B2045735 : Blo 475787 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B3880781 : Blo 475787 3880781 := bstep (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) B1455293
theorem B538591 : Blo 475787 538591 := bstep (se 1 (by rfl) ⟨403943, by rfl⟩ : syracuseStep 538591 = 807887) B807887
theorem B1456633 : Blo 475787 1456633 := bstep (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) B1092475
theorem B5454377 : Blo 475787 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B1294427 : Blo 475787 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B1360223 : Blo 475787 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B9421289 : Blo 475787 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B80724599 : Blo 475787 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B475903 : Blo 475787 475903 := bstep (se 1 (by rfl) ⟨356927, by rfl⟩ : syracuseStep 475903 = 713855) B713855
theorem B475995 : Blo 475787 475995 := bstep (se 1 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 475995 = 713993) B713993
theorem B508999 : Blo 475787 508999 := bstep (se 1 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 508999 = 763499) B763499
theorem B1361033 : Blo 475787 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B476315 : Blo 475787 476315 := bstep (se 1 (by rfl) ⟨357236, by rfl⟩ : syracuseStep 476315 = 714473) B714473
theorem B476415 : Blo 475787 476415 := bstep (se 1 (by rfl) ⟨357311, by rfl⟩ : syracuseStep 476415 = 714623) B714623
theorem B476671 : Blo 475787 476671 := bstep (se 1 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 476671 = 715007) B715007
theorem B476827 : Blo 475787 476827 := bstep (se 1 (by rfl) ⟨357620, by rfl⟩ : syracuseStep 476827 = 715241) B715241
theorem B1296253 : Blo 475787 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B2410397 : Blo 475787 2410397 := bstep (se 3 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 2410397 = 903899) B903899
theorem B804775 : Blo 475787 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B1525729 : Blo 475787 1525729 := bstep (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) B1144297
theorem B2410721 : Blo 475787 2410721 := bstep (se 2 (by rfl) ⟨904020, by rfl⟩ : syracuseStep 2410721 = 1808041) B1808041
theorem B477435 : Blo 475787 477435 := bstep (se 1 (by rfl) ⟨358076, by rfl⟩ : syracuseStep 477435 = 716153) B716153
theorem B477511 : Blo 475787 477511 := bstep (se 1 (by rfl) ⟨358133, by rfl⟩ : syracuseStep 477511 = 716267) B716267
theorem B477595 : Blo 475787 477595 := bstep (se 1 (by rfl) ⟨358196, by rfl⟩ : syracuseStep 477595 = 716393) B716393
theorem B805423 : Blo 475787 805423 := bstep (se 1 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 805423 = 1208135) B1208135
theorem B477807 : Blo 475787 477807 := bstep (se 1 (by rfl) ⟨358355, by rfl⟩ : syracuseStep 477807 = 716711) B716711
theorem B477927 : Blo 475787 477927 := bstep (se 1 (by rfl) ⟨358445, by rfl⟩ : syracuseStep 477927 = 716891) B716891
theorem B9063419 : Blo 475787 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B478319 : Blo 475787 478319 := bstep (se 1 (by rfl) ⟨358739, by rfl⟩ : syracuseStep 478319 = 717479) B717479
theorem B1526971 : Blo 475787 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B478399 : Blo 475787 478399 := bstep (se 1 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 478399 = 717599) B717599
theorem B1363367 : Blo 475787 1363367 := bstep (se 1 (by rfl) ⟨1022525, by rfl⟩ : syracuseStep 1363367 = 2045051) B2045051
theorem B478719 : Blo 475787 478719 := bstep (se 1 (by rfl) ⟨359039, by rfl⟩ : syracuseStep 478719 = 718079) B718079
theorem B806665 : Blo 475787 806665 := bstep (se 2 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 806665 = 604999) B604999
theorem B806719 : Blo 475787 806719 := bstep (se 1 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 806719 = 1210079) B1210079
theorem B479167 : Blo 475787 479167 := bstep (se 1 (by rfl) ⟨359375, by rfl⟩ : syracuseStep 479167 = 718751) B718751
theorem B7360895 : Blo 475787 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B545563 : Blo 475787 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B971689 : Blo 475787 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B1168415 : Blo 475787 1168415 := bstep (se 1 (by rfl) ⟨876311, by rfl⟩ : syracuseStep 1168415 = 1752623) B1752623
theorem B1725947 : Blo 475787 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B874091 : Blo 475787 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B808859 : Blo 475787 808859 := bstep (se 1 (by rfl) ⟨606644, by rfl⟩ : syracuseStep 808859 = 1213289) B1213289
theorem B1071017 : Blo 475787 1071017 := bstep (se 2 (by rfl) ⟨401631, by rfl⟩ : syracuseStep 1071017 = 803263) B803263
theorem B2578715 : Blo 475787 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B679223 : Blo 475787 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B777695 : Blo 475787 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B1073825 : Blo 475787 1073825 := bstep (se 2 (by rfl) ⟨402684, by rfl⟩ : syracuseStep 1073825 = 805369) B805369
theorem B1074041 : Blo 475787 1074041 := bstep (se 2 (by rfl) ⟨402765, by rfl⟩ : syracuseStep 1074041 = 805531) B805531
theorem B910217 : Blo 475787 910217 := bstep (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) B682663
theorem B1074239 : Blo 475787 1074239 := bstep (se 1 (by rfl) ⟨805679, by rfl⟩ : syracuseStep 1074239 = 1611359) B1611359
theorem B26076593 : Blo 475787 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B3225445829 : Blo 475787 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B1205867 : Blo 475787 1205867 := bstep (se 1 (by rfl) ⟨904400, by rfl⟩ : syracuseStep 1205867 = 1808801) B1808801
theorem B34891397 : Blo 475787 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B1205999 : Blo 475787 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B714815 : Blo 475787 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B714983 : Blo 475787 714983 := bstep (se 1 (by rfl) ⟨536237, by rfl⟩ : syracuseStep 714983 = 1072475) B1072475
theorem B6514991 : Blo 475787 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B1075535 : Blo 475787 1075535 := bstep (se 1 (by rfl) ⟨806651, by rfl⟩ : syracuseStep 1075535 = 1613303) B1613303
theorem B715247 : Blo 475787 715247 := bstep (se 1 (by rfl) ⟨536435, by rfl⟩ : syracuseStep 715247 = 1072871) B1072871
theorem B1534751 : Blo 475787 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B1076039 : Blo 475787 1076039 := bstep (se 1 (by rfl) ⟨807029, by rfl⟩ : syracuseStep 1076039 = 1614059) B1614059
theorem B715631 : Blo 475787 715631 := bstep (se 1 (by rfl) ⟨536723, by rfl⟩ : syracuseStep 715631 = 1073447) B1073447
theorem B1534967 : Blo 475787 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B715871 : Blo 475787 715871 := bstep (se 1 (by rfl) ⟨536903, by rfl⟩ : syracuseStep 715871 = 1073807) B1073807
theorem B1076327 : Blo 475787 1076327 := bstep (se 1 (by rfl) ⟨807245, by rfl⟩ : syracuseStep 1076327 = 1614491) B1614491
theorem B1207457 : Blo 475787 1207457 := bstep (se 2 (by rfl) ⟨452796, by rfl⟩ : syracuseStep 1207457 = 905593) B905593
theorem B2747567 : Blo 475787 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B716315 : Blo 475787 716315 := bstep (se 1 (by rfl) ⟨537236, by rfl⟩ : syracuseStep 716315 = 1074473) B1074473
theorem B1076903 : Blo 475787 1076903 := bstep (se 1 (by rfl) ⟨807677, by rfl⟩ : syracuseStep 1076903 = 1615355) B1615355
theorem B2715389 : Blo 475787 2715389 := bstep (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) B1018271
theorem B1077947 : Blo 475787 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B1209127 : Blo 475787 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B1078073 : Blo 475787 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B4092767 : Blo 475787 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B3437417 : Blo 475787 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B717803 : Blo 475787 717803 := bstep (se 1 (by rfl) ⟨538352, by rfl⟩ : syracuseStep 717803 = 1076705) B1076705
theorem B7762985 : Blo 475787 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B2749625 : Blo 475787 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B1078649 : Blo 475787 1078649 := bstep (se 2 (by rfl) ⟨404493, by rfl⟩ : syracuseStep 1078649 = 808987) B808987
theorem B1210099 : Blo 475787 1210099 := bstep (se 1 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 1210099 = 1815149) B1815149
theorem B1570715 : Blo 475787 1570715 := bstep (se 1 (by rfl) ⟨1178036, by rfl⟩ : syracuseStep 1570715 = 2356073) B2356073
theorem B1210423 : Blo 475787 1210423 := bstep (se 1 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 1210423 = 1815635) B1815635
theorem B719135 : Blo 475787 719135 := bstep (se 1 (by rfl) ⟨539351, by rfl⟩ : syracuseStep 719135 = 1078703) B1078703
theorem B1145191 : Blo 475787 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B719207 : Blo 475787 719207 := bstep (se 1 (by rfl) ⟨539405, by rfl⟩ : syracuseStep 719207 = 1078811) B1078811
theorem B5175845 : Blo 475787 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B2423681 : Blo 475787 2423681 := bstep (se 2 (by rfl) ⟨908880, by rfl⟩ : syracuseStep 2423681 = 1817761) B1817761
theorem B47055595 : Blo 475787 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B1606931 : Blo 475787 1606931 := bstep (se 1 (by rfl) ⟨1205198, by rfl⟩ : syracuseStep 1606931 = 2410397) B2410397
theorem B1607147 : Blo 475787 1607147 := bstep (se 1 (by rfl) ⟨1205360, by rfl⟩ : syracuseStep 1607147 = 2410721) B2410721
theorem B2033363 : Blo 475787 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B2427245 : Blo 475787 2427245 := bstep (se 3 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 2427245 = 910217) B910217
theorem B2034305 : Blo 475787 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B1150631 : Blo 475787 1150631 := bstep (se 1 (by rfl) ⟨862973, by rfl⟩ : syracuseStep 1150631 = 1725947) B1725947
theorem B2035961 : Blo 475787 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B726175 : Blo 475787 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B727417 : Blo 475787 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B1612169 : Blo 475787 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B1383307 : Blo 475787 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B2038763 : Blo 475787 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B1023167 : Blo 475787 1023167 := bstep (se 1 (by rfl) ⟨767375, by rfl⟩ : syracuseStep 1023167 = 1534751) B1534751
theorem B1023311 : Blo 475787 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B1613465 : Blo 475787 1613465 := bstep (se 2 (by rfl) ⟨605049, by rfl⟩ : syracuseStep 1613465 = 1210099) B1210099
theorem B1810259 : Blo 475787 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B1843181 : Blo 475787 1843181 := bstep (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) B691193
theorem B1613897 : Blo 475787 1613897 := bstep (se 2 (by rfl) ⟨605211, by rfl⟩ : syracuseStep 1613897 = 1210423) B1210423
theorem B3482099 : Blo 475787 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B2728511 : Blo 475787 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B1942177 : Blo 475787 1942177 := bstep (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) B1456633
theorem B1811261 : Blo 475787 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B2073853 : Blo 475787 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B3614381 : Blo 475787 3614381 := bstep (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) B1355393
theorem B3450563 : Blo 475787 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B1615787 : Blo 475787 1615787 := bstep (se 1 (by rfl) ⟨1211840, by rfl⟩ : syracuseStep 1615787 = 2423681) B2423681
theorem B3451805 : Blo 475787 3451805 := bstep (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) B1294427
theorem B4762633 : Blo 475787 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B53816399 : Blo 475787 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B7450015 : Blo 475787 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B1617947 : Blo 475787 1617947 := bstep (se 1 (by rfl) ⟨1213460, by rfl⟩ : syracuseStep 1617947 = 2426921) B2426921
theorem B1814663 : Blo 475787 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B17412893 : Blo 475787 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B1618811 : Blo 475787 1618811 := bstep (se 1 (by rfl) ⟨1214108, by rfl⟩ : syracuseStep 1618811 = 2428217) B2428217
theorem B768047 : Blo 475787 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B539239 : Blo 475787 539239 := bstep (se 1 (by rfl) ⟨404429, by rfl⟩ : syracuseStep 539239 = 808859) B808859
theorem B1719143 : Blo 475787 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B5423759 : Blo 475787 5423759 := bstep (se 1 (by rfl) ⟨4067819, by rfl⟩ : syracuseStep 5423759 = 8135639) B8135639
theorem B3457889 : Blo 475787 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B17384395 : Blo 475787 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B803911 : Blo 475787 803911 := bstep (se 1 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 803911 = 1205867) B1205867
theorem B803999 : Blo 475787 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B1295585 : Blo 475787 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B476543 : Blo 475787 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B476655 : Blo 475787 476655 := bstep (se 1 (by rfl) ⟨357491, by rfl⟩ : syracuseStep 476655 = 714983) B714983
theorem B4343327 : Blo 475787 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B476831 : Blo 475787 476831 := bstep (se 1 (by rfl) ⟨357623, by rfl⟩ : syracuseStep 476831 = 715247) B715247
theorem B477087 : Blo 475787 477087 := bstep (se 1 (by rfl) ⟨357815, by rfl⟩ : syracuseStep 477087 = 715631) B715631
theorem B477247 : Blo 475787 477247 := bstep (se 1 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 477247 = 715871) B715871
theorem B804971 : Blo 475787 804971 := bstep (se 1 (by rfl) ⟨603728, by rfl⟩ : syracuseStep 804971 = 1207457) B1207457
theorem B477543 : Blo 475787 477543 := bstep (se 1 (by rfl) ⟨358157, by rfl⟩ : syracuseStep 477543 = 716315) B716315
theorem B24169117 : Blo 475787 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B1821635 : Blo 475787 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B7326845 : Blo 475787 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B1526921 : Blo 475787 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B478535 : Blo 475787 478535 := bstep (se 1 (by rfl) ⟨358901, by rfl⟩ : syracuseStep 478535 = 717803) B717803
theorem B1363823 : Blo 475787 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B479423 : Blo 475787 479423 := bstep (se 1 (by rfl) ⟨359567, by rfl⟩ : syracuseStep 479423 = 719135) B719135
theorem B479471 : Blo 475787 479471 := bstep (se 1 (by rfl) ⟨359603, by rfl⟩ : syracuseStep 479471 = 719207) B719207
theorem B906815 : Blo 475787 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B6280859 : Blo 475787 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B16734035 : Blo 475787 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B907355 : Blo 475787 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B809183 : Blo 475787 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B1071719 : Blo 475787 1071719 := bstep (se 1 (by rfl) ⟨803789, by rfl⟩ : syracuseStep 1071719 = 1607579) B1607579
theorem B678665 : Blo 475787 678665 := bstep (se 2 (by rfl) ⟨254499, by rfl⟩ : syracuseStep 678665 = 508999) B508999
theorem B1072619 : Blo 475787 1072619 := bstep (se 1 (by rfl) ⟨804464, by rfl⟩ : syracuseStep 1072619 = 1608929) B1608929
theorem B908911 : Blo 475787 908911 := bstep (se 1 (by rfl) ⟨681683, by rfl⟩ : syracuseStep 908911 = 1363367) B1363367
theorem B5431049 : Blo 475787 5431049 := bstep (se 2 (by rfl) ⟨2036643, by rfl⟩ : syracuseStep 5431049 = 4073287) B4073287
theorem B1073033 : Blo 475787 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B2416553 : Blo 475787 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B4907263 : Blo 475787 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B45310369 : Blo 475787 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B1532495 : Blo 475787 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B778943 : Blo 475787 778943 := bstep (se 1 (by rfl) ⟨584207, by rfl⟩ : syracuseStep 778943 = 1168415) B1168415
theorem B1073897 : Blo 475787 1073897 := bstep (se 2 (by rfl) ⟨402711, by rfl⟩ : syracuseStep 1073897 = 805423) B805423
theorem B582727 : Blo 475787 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B6120593 : Blo 475787 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B714011 : Blo 475787 714011 := bstep (se 1 (by rfl) ⟨535508, by rfl⟩ : syracuseStep 714011 = 1071017) B1071017
theorem B681319 : Blo 475787 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B714281 : Blo 475787 714281 := bstep (se 2 (by rfl) ⟨267855, by rfl⟩ : syracuseStep 714281 = 535711) B535711
theorem B107865893 : Blo 475787 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B1075175 : Blo 475787 1075175 := bstep (se 1 (by rfl) ⟨806381, by rfl⟩ : syracuseStep 1075175 = 1612763) B1612763
theorem B1075553 : Blo 475787 1075553 := bstep (se 2 (by rfl) ⟨403332, by rfl⟩ : syracuseStep 1075553 = 806665) B806665
theorem B1075625 : Blo 475787 1075625 := bstep (se 2 (by rfl) ⟨403359, by rfl⟩ : syracuseStep 1075625 = 806719) B806719
theorem B1075967 : Blo 475787 1075967 := bstep (se 1 (by rfl) ⟨806975, by rfl⟩ : syracuseStep 1075967 = 1613951) B1613951
theorem B1076255 : Blo 475787 1076255 := bstep (se 1 (by rfl) ⟨807191, by rfl⟩ : syracuseStep 1076255 = 1614383) B1614383
theorem B715883 : Blo 475787 715883 := bstep (se 1 (by rfl) ⟨536912, by rfl⟩ : syracuseStep 715883 = 1073825) B1073825
theorem B716027 : Blo 475787 716027 := bstep (se 1 (by rfl) ⟨537020, by rfl⟩ : syracuseStep 716027 = 1074041) B1074041
theorem B13200653 : Blo 475787 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B716159 : Blo 475787 716159 := bstep (se 1 (by rfl) ⟨537119, by rfl⟩ : syracuseStep 716159 = 1074239) B1074239
theorem B6123053 : Blo 475787 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B2150297219 : Blo 475787 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B15494827 : Blo 475787 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B23260931 : Blo 475787 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B15560747 : Blo 475787 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B6221933 : Blo 475787 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B717023 : Blo 475787 717023 := bstep (se 1 (by rfl) ⟨537767, by rfl⟩ : syracuseStep 717023 = 1075535) B1075535
theorem B717353 : Blo 475787 717353 := bstep (se 2 (by rfl) ⟨269007, by rfl⟩ : syracuseStep 717353 = 538015) B538015
theorem B717359 : Blo 475787 717359 := bstep (se 1 (by rfl) ⟨538019, by rfl⟩ : syracuseStep 717359 = 1076039) B1076039
theorem B717551 : Blo 475787 717551 := bstep (se 1 (by rfl) ⟨538163, by rfl⟩ : syracuseStep 717551 = 1076327) B1076327
theorem B717737 : Blo 475787 717737 := bstep (se 2 (by rfl) ⟨269151, by rfl⟩ : syracuseStep 717737 = 538303) B538303
theorem B717935 : Blo 475787 717935 := bstep (se 1 (by rfl) ⟨538451, by rfl⟩ : syracuseStep 717935 = 1076903) B1076903
theorem B3437759 : Blo 475787 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B718121 : Blo 475787 718121 := bstep (se 2 (by rfl) ⟨269295, by rfl⟩ : syracuseStep 718121 = 538591) B538591
theorem B1209887 : Blo 475787 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B718631 : Blo 475787 718631 := bstep (se 1 (by rfl) ⟨538973, by rfl⟩ : syracuseStep 718631 = 1077947) B1077947
theorem B718715 : Blo 475787 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B2291611 : Blo 475787 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B5175323 : Blo 475787 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B1079351 : Blo 475787 1079351 := bstep (se 1 (by rfl) ⟨809513, by rfl⟩ : syracuseStep 1079351 = 1619027) B1619027
theorem B1833083 : Blo 475787 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B719099 : Blo 475787 719099 := bstep (se 1 (by rfl) ⟨539324, by rfl⟩ : syracuseStep 719099 = 1078649) B1078649
theorem B1210727 : Blo 475787 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B2587187 : Blo 475787 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B1047143 : Blo 475787 1047143 := bstep (se 1 (by rfl) ⟨785357, by rfl⟩ : syracuseStep 1047143 = 1570715) B1570715
theorem B3636251 : Blo 475787 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B6913349 : Blo 475787 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B8192501 : Blo 475787 8192501 := bstep (se 5 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 8192501 = 768047) B768047
theorem B2589569 : Blo 475787 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B1214423 : Blo 475787 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B4884563 : Blo 475787 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B1017947 : Blo 475787 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B16748957 : Blo 475787 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B9933353 : Blo 475787 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B7377637 : Blo 475787 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B1611035 : Blo 475787 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B1021663 : Blo 475787 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B3872933 : Blo 475787 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B2300375 : Blo 475787 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B2301203 : Blo 475787 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B1809773 : Blo 475787 1809773 := bstep (se 3 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 1809773 = 678665) B678665
theorem B15507287 : Blo 475787 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B3055481 : Blo 475787 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B11608595 : Blo 475787 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B2728829 : Blo 475787 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B3450215 : Blo 475787 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B1222055 : Blo 475787 1222055 := bstep (se 1 (by rfl) ⟨916541, by rfl⟩ : syracuseStep 1222055 = 1833083) B1833083
theorem B698095 : Blo 475787 698095 := bstep (se 1 (by rfl) ⟨523571, by rfl⟩ : syracuseStep 698095 = 1047143) B1047143
theorem B3615839 : Blo 475787 3615839 := bstep (se 1 (by rfl) ⟨2711879, by rfl⟩ : syracuseStep 3615839 = 5423759) B5423759
theorem B2305259 : Blo 475787 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B535999 : Blo 475787 535999 := bstep (se 1 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 535999 = 803999) B803999
theorem B863723 : Blo 475787 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B2895551 : Blo 475787 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B23179193 : Blo 475787 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B536647 : Blo 475787 536647 := bstep (se 1 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 536647 = 804971) B804971
theorem B1618163 : Blo 475787 1618163 := bstep (se 1 (by rfl) ⟨1213622, by rfl⟩ : syracuseStep 1618163 = 2427245) B2427245
theorem B1356203 : Blo 475787 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B767087 : Blo 475787 767087 := bstep (se 1 (by rfl) ⟨575315, by rfl⟩ : syracuseStep 767087 = 1150631) B1150631
theorem B1357307 : Blo 475787 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B32225489 : Blo 475787 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B11156023 : Blo 475787 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B604903 : Blo 475787 604903 := bstep (se 1 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 604903 = 907355) B907355
theorem B539455 : Blo 475787 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B5422301 : Blo 475787 5422301 := bstep (se 3 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 5422301 = 2033363) B2033363
theorem B1359175 : Blo 475787 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B20659769 : Blo 475787 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B3620699 : Blo 475787 3620699 := bstep (se 1 (by rfl) ⟨2715524, by rfl⟩ : syracuseStep 3620699 = 5431049) B5431049
theorem B1228787 : Blo 475787 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1819007 : Blo 475787 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B4080395 : Blo 475787 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B476007 : Blo 475787 476007 := bstep (se 1 (by rfl) ⟨357005, by rfl⟩ : syracuseStep 476007 = 714011) B714011
theorem B476187 : Blo 475787 476187 := bstep (se 1 (by rfl) ⟨357140, by rfl⟩ : syracuseStep 476187 = 714281) B714281
theorem B2409587 : Blo 475787 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B71910595 : Blo 475787 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B11060549 : Blo 475787 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B6899165 : Blo 475787 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B477255 : Blo 475787 477255 := bstep (se 1 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 477255 = 715883) B715883
theorem B477351 : Blo 475787 477351 := bstep (se 1 (by rfl) ⟨358013, by rfl⟩ : syracuseStep 477351 = 716027) B716027
theorem B8800435 : Blo 475787 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B477439 : Blo 475787 477439 := bstep (se 1 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 477439 = 716159) B716159
theorem B4082035 : Blo 475787 4082035 := bstep (se 1 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 4082035 = 6123053) B6123053
theorem B10373831 : Blo 475787 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B4147955 : Blo 475787 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B478015 : Blo 475787 478015 := bstep (se 1 (by rfl) ⟨358511, by rfl⟩ : syracuseStep 478015 = 717023) B717023
theorem B478235 : Blo 475787 478235 := bstep (se 1 (by rfl) ⟨358676, by rfl⟩ : syracuseStep 478235 = 717353) B717353
theorem B478239 : Blo 475787 478239 := bstep (se 1 (by rfl) ⟨358679, by rfl⟩ : syracuseStep 478239 = 717359) B717359
theorem B478367 : Blo 475787 478367 := bstep (se 1 (by rfl) ⟨358775, by rfl⟩ : syracuseStep 478367 = 717551) B717551
theorem B969889 : Blo 475787 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B478491 : Blo 475787 478491 := bstep (se 1 (by rfl) ⟨358868, by rfl⟩ : syracuseStep 478491 = 717737) B717737
theorem B478623 : Blo 475787 478623 := bstep (se 1 (by rfl) ⟨358967, by rfl⟩ : syracuseStep 478623 = 717935) B717935
theorem B478747 : Blo 475787 478747 := bstep (se 1 (by rfl) ⟨359060, by rfl⟩ : syracuseStep 478747 = 718121) B718121
theorem B806591 : Blo 475787 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B479087 : Blo 475787 479087 := bstep (se 1 (by rfl) ⟨359315, by rfl⟩ : syracuseStep 479087 = 718631) B718631
theorem B479143 : Blo 475787 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B479399 : Blo 475787 479399 := bstep (se 1 (by rfl) ⟨359549, by rfl⟩ : syracuseStep 479399 = 719099) B719099
theorem B807151 : Blo 475787 807151 := bstep (se 1 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 807151 = 1210727) B1210727
theorem B5734125917 : Blo 475787 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B4608899 : Blo 475787 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B6543017 : Blo 475787 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B60413825 : Blo 475787 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B1071287 : Blo 475787 1071287 := bstep (se 1 (by rfl) ⟨803465, by rfl⟩ : syracuseStep 1071287 = 1606931) B1606931
theorem B62740793 : Blo 475787 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B1071431 : Blo 475787 1071431 := bstep (se 1 (by rfl) ⟨803573, by rfl⟩ : syracuseStep 1071431 = 1607147) B1607147
theorem B1071881 : Blo 475787 1071881 := bstep (se 2 (by rfl) ⟨401955, by rfl⟩ : syracuseStep 1071881 = 803911) B803911
theorem B776969 : Blo 475787 776969 := bstep (se 2 (by rfl) ⟨291363, by rfl⟩ : syracuseStep 776969 = 582727) B582727
theorem B908425 : Blo 475787 908425 := bstep (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) B681319
theorem B909215 : Blo 475787 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B9167357 : Blo 475787 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B6350177 : Blo 475787 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B2418173 : Blo 475787 2418173 := bstep (se 3 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 2418173 = 906815) B906815
theorem B1074779 : Blo 475787 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B714479 : Blo 475787 714479 := bstep (se 1 (by rfl) ⟨535859, by rfl⟩ : syracuseStep 714479 = 1071719) B1071719
theorem B682111 : Blo 475787 682111 := bstep (se 1 (by rfl) ⟨511583, by rfl⟩ : syracuseStep 682111 = 1023167) B1023167
theorem B715079 : Blo 475787 715079 := bstep (se 1 (by rfl) ⟨536309, by rfl⟩ : syracuseStep 715079 = 1072619) B1072619
theorem B1075643 : Blo 475787 1075643 := bstep (se 1 (by rfl) ⟨806732, by rfl⟩ : syracuseStep 1075643 = 1613465) B1613465
theorem B1206839 : Blo 475787 1206839 := bstep (se 1 (by rfl) ⟨905129, by rfl⟩ : syracuseStep 1206839 = 1810259) B1810259
theorem B715355 : Blo 475787 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B1075931 : Blo 475787 1075931 := bstep (se 1 (by rfl) ⟨806948, by rfl⟩ : syracuseStep 1075931 = 1613897) B1613897
theorem B2321399 : Blo 475787 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B519295 : Blo 475787 519295 := bstep (se 1 (by rfl) ⟨389471, by rfl⟩ : syracuseStep 519295 = 778943) B778943
theorem B715931 : Blo 475787 715931 := bstep (se 1 (by rfl) ⟨536948, by rfl⟩ : syracuseStep 715931 = 1073897) B1073897
theorem B1207507 : Blo 475787 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B1077191 : Blo 475787 1077191 := bstep (se 1 (by rfl) ⟨807893, by rfl⟩ : syracuseStep 1077191 = 1615787) B1615787
theorem B716783 : Blo 475787 716783 := bstep (se 1 (by rfl) ⟨537587, by rfl⟩ : syracuseStep 716783 = 1075175) B1075175
theorem B717035 : Blo 475787 717035 := bstep (se 1 (by rfl) ⟨537776, by rfl⟩ : syracuseStep 717035 = 1075553) B1075553
theorem B717083 : Blo 475787 717083 := bstep (se 1 (by rfl) ⟨537812, by rfl⟩ : syracuseStep 717083 = 1075625) B1075625
theorem B717311 : Blo 475787 717311 := bstep (se 1 (by rfl) ⟨537983, by rfl⟩ : syracuseStep 717311 = 1075967) B1075967
theorem B717503 : Blo 475787 717503 := bstep (se 1 (by rfl) ⟨538127, by rfl⟩ : syracuseStep 717503 = 1076255) B1076255
theorem B35877599 : Blo 475787 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B1078631 : Blo 475787 1078631 := bstep (se 1 (by rfl) ⟨808973, by rfl⟩ : syracuseStep 1078631 = 1617947) B1617947
theorem B1209775 : Blo 475787 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B1079207 : Blo 475787 1079207 := bstep (se 1 (by rfl) ⟨809405, by rfl⟩ : syracuseStep 1079207 = 1618811) B1618811
theorem B718985 : Blo 475787 718985 := bstep (se 2 (by rfl) ⟨269619, by rfl⟩ : syracuseStep 718985 = 539239) B539239
theorem B719567 : Blo 475787 719567 := bstep (se 1 (by rfl) ⟨539675, by rfl⟩ : syracuseStep 719567 = 1079351) B1079351
theorem B1146095 : Blo 475787 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B2424167 : Blo 475787 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B1211881 : Blo 475787 1211881 := bstep (se 2 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 1211881 = 908911) B908911
theorem B1212671 : Blo 475787 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B2720263 : Blo 475787 2720263 := bstep (se 1 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 2720263 = 4080395) B4080395
theorem B1606391 : Blo 475787 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B7373699 : Blo 475787 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B44663885 : Blo 475787 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B6915887 : Blo 475787 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B3822750611 : Blo 475787 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B11733913 : Blo 475787 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B6622235 : Blo 475787 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B5442713 : Blo 475787 5442713 := bstep (se 2 (by rfl) ⟨2041017, by rfl⟩ : syracuseStep 5442713 = 4082035) B4082035
theorem B4362011 : Blo 475787 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B40275883 : Blo 475787 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B692393 : Blo 475787 692393 := bstep (se 2 (by rfl) ⟨259647, by rfl⟩ : syracuseStep 692393 = 519295) B519295
theorem B1610009 : Blo 475787 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B2036987 : Blo 475787 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B7739063 : Blo 475787 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B9836849 : Blo 475787 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B1612115 : Blo 475787 1612115 := bstep (se 1 (by rfl) ⟨1209086, by rfl⟩ : syracuseStep 1612115 = 2418173) B2418173
theorem B383523173 : Blo 475787 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B1613033 : Blo 475787 1613033 := bstep (se 2 (by rfl) ⟨604887, by rfl⟩ : syracuseStep 1613033 = 1209775) B1209775
theorem B1547599 : Blo 475787 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B2303261 : Blo 475787 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B1812233 : Blo 475787 1812233 := bstep (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) B1359175
theorem B1615841 : Blo 475787 1615841 := bstep (se 2 (by rfl) ⟨605940, by rfl⟩ : syracuseStep 1615841 = 1211881) B1211881
theorem B3614867 : Blo 475787 3614867 := bstep (se 1 (by rfl) ⟨2711150, by rfl⟩ : syracuseStep 3614867 = 5422301) B5422301
theorem B764063 : Blo 475787 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B1616111 : Blo 475787 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B13773179 : Blo 475787 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B4599443 : Blo 475787 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B3256375 : Blo 475787 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B2765303 : Blo 475787 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B930793 : Blo 475787 930793 := bstep (se 2 (by rfl) ⟨349047, by rfl⟩ : syracuseStep 930793 = 698095) B698095
theorem B537727 : Blo 475787 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B41827195 : Blo 475787 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B1293185 : Blo 475787 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B10338191 : Blo 475787 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B606143 : Blo 475787 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B6111571 : Blo 475787 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B1819219 : Blo 475787 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B476319 : Blo 475787 476319 := bstep (se 1 (by rfl) ⟨357239, by rfl⟩ : syracuseStep 476319 = 714479) B714479
theorem B476719 : Blo 475787 476719 := bstep (se 1 (by rfl) ⟨357539, by rfl⟩ : syracuseStep 476719 = 715079) B715079
theorem B804559 : Blo 475787 804559 := bstep (se 1 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 804559 = 1206839) B1206839
theorem B476903 : Blo 475787 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B2410559 : Blo 475787 2410559 := bstep (se 1 (by rfl) ⟨1807919, by rfl⟩ : syracuseStep 2410559 = 3615839) B3615839
theorem B477287 : Blo 475787 477287 := bstep (se 1 (by rfl) ⟨357965, by rfl⟩ : syracuseStep 477287 = 715931) B715931
theorem B1362217 : Blo 475787 1362217 := bstep (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) B1021663
theorem B15452795 : Blo 475787 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B477855 : Blo 475787 477855 := bstep (se 1 (by rfl) ⟨358391, by rfl⟩ : syracuseStep 477855 = 716783) B716783
theorem B478023 : Blo 475787 478023 := bstep (se 1 (by rfl) ⟨358517, by rfl⟩ : syracuseStep 478023 = 717035) B717035
theorem B478055 : Blo 475787 478055 := bstep (se 1 (by rfl) ⟨358541, by rfl⟩ : syracuseStep 478055 = 717083) B717083
theorem B904135 : Blo 475787 904135 := bstep (se 1 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 904135 = 1356203) B1356203
theorem B478207 : Blo 475787 478207 := bstep (se 1 (by rfl) ⟨358655, by rfl⟩ : syracuseStep 478207 = 717311) B717311
theorem B478335 : Blo 475787 478335 := bstep (se 1 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 478335 = 717503) B717503
theorem B511391 : Blo 475787 511391 := bstep (se 1 (by rfl) ⟨383543, by rfl⟩ : syracuseStep 511391 = 767087) B767087
theorem B806537 : Blo 475787 806537 := bstep (se 2 (by rfl) ⟨302451, by rfl⟩ : syracuseStep 806537 = 604903) B604903
theorem B904871 : Blo 475787 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B479323 : Blo 475787 479323 := bstep (se 1 (by rfl) ⟨359492, by rfl⟩ : syracuseStep 479323 = 718985) B718985
theorem B21483659 : Blo 475787 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B479711 : Blo 475787 479711 := bstep (se 1 (by rfl) ⟨359783, by rfl⟩ : syracuseStep 479711 = 719567) B719567
theorem B2413799 : Blo 475787 2413799 := bstep (se 1 (by rfl) ⟨1810349, by rfl⟩ : syracuseStep 2413799 = 3620699) B3620699
theorem B5461667 : Blo 475787 5461667 := bstep (se 1 (by rfl) ⟨4096250, by rfl⟩ : syracuseStep 5461667 = 8192501) B8192501
theorem B1726379 : Blo 475787 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B809615 : Blo 475787 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B678631 : Blo 475787 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B909481 : Blo 475787 909481 := bstep (se 2 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 909481 = 682111) B682111
theorem B3072599 : Blo 475787 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B1074023 : Blo 475787 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B16933805 : Blo 475787 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B9200573 : Blo 475787 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B2581955 : Blo 475787 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B714191 : Blo 475787 714191 := bstep (se 1 (by rfl) ⟨535643, by rfl⟩ : syracuseStep 714191 = 1071287) B1071287
theorem B714287 : Blo 475787 714287 := bstep (se 1 (by rfl) ⟨535715, by rfl⟩ : syracuseStep 714287 = 1071431) B1071431
theorem B1533583 : Blo 475787 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B714587 : Blo 475787 714587 := bstep (se 1 (by rfl) ⟨535940, by rfl⟩ : syracuseStep 714587 = 1071881) B1071881
theorem B517979 : Blo 475787 517979 := bstep (se 1 (by rfl) ⟨388484, by rfl⟩ : syracuseStep 517979 = 776969) B776969
theorem B714665 : Blo 475787 714665 := bstep (se 2 (by rfl) ⟨267999, by rfl⟩ : syracuseStep 714665 = 535999) B535999
theorem B1534135 : Blo 475787 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B1206515 : Blo 475787 1206515 := bstep (se 1 (by rfl) ⟨904886, by rfl⟩ : syracuseStep 1206515 = 1809773) B1809773
theorem B715529 : Blo 475787 715529 := bstep (se 2 (by rfl) ⟨268323, by rfl⟩ : syracuseStep 715529 = 536647) B536647
theorem B1076201 : Blo 475787 1076201 := bstep (se 2 (by rfl) ⟨403575, by rfl⟩ : syracuseStep 1076201 = 807151) B807151
theorem B814703 : Blo 475787 814703 := bstep (se 1 (by rfl) ⟨611027, by rfl⟩ : syracuseStep 814703 = 1222055) B1222055
theorem B716519 : Blo 475787 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B717095 : Blo 475787 717095 := bstep (se 1 (by rfl) ⟨537821, by rfl⟩ : syracuseStep 717095 = 1075643) B1075643
theorem B717287 : Blo 475787 717287 := bstep (se 1 (by rfl) ⟨537965, by rfl⟩ : syracuseStep 717287 = 1075931) B1075931
theorem B1536839 : Blo 475787 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B1930367 : Blo 475787 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B718127 : Blo 475787 718127 := bstep (se 1 (by rfl) ⟨538595, by rfl⟩ : syracuseStep 718127 = 1077191) B1077191
theorem B1078775 : Blo 475787 1078775 := bstep (se 1 (by rfl) ⟨809081, by rfl⟩ : syracuseStep 1078775 = 1618163) B1618163
theorem B23918399 : Blo 475787 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B14874697 : Blo 475787 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B719087 : Blo 475787 719087 := bstep (se 1 (by rfl) ⟨539315, by rfl⟩ : syracuseStep 719087 = 1078631) B1078631
theorem B719273 : Blo 475787 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B719471 : Blo 475787 719471 := bstep (se 1 (by rfl) ⟨539603, by rfl⟩ : syracuseStep 719471 = 1079207) B1079207
theorem B1211233 : Blo 475787 1211233 := bstep (se 2 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 1211233 = 908425) B908425
theorem B819191 : Blo 475787 819191 := bstep (se 1 (by rfl) ⟨614393, by rfl⟩ : syracuseStep 819191 = 1228787) B1228787
theorem B1212641 : Blo 475787 1212641 := bstep (se 2 (by rfl) ⟨454740, by rfl⟩ : syracuseStep 1212641 = 909481) B909481
theorem B79331717 : Blo 475787 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B4915799 : Blo 475787 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B2425625 : Blo 475787 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B1607039 : Blo 475787 1607039 := bstep (se 1 (by rfl) ⟨1205279, by rfl⟩ : syracuseStep 1607039 = 2410559) B2410559
theorem B2548500407 : Blo 475787 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B14322439 : Blo 475787 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B1609199 : Blo 475787 1609199 := bstep (se 1 (by rfl) ⟨1206899, by rfl⟩ : syracuseStep 1609199 = 2413799) B2413799
theorem B3641111 : Blo 475787 3641111 := bstep (se 1 (by rfl) ⟨2730833, by rfl⟩ : syracuseStep 3641111 = 5461667) B5461667
theorem B1150919 : Blo 475787 1150919 := bstep (se 1 (by rfl) ⟨863189, by rfl⟩ : syracuseStep 1150919 = 1726379) B1726379
theorem B1381277 : Blo 475787 1381277 := bstep (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) B517979
theorem B6133715 : Blo 475787 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B9182119 : Blo 475787 9182119 := bstep (se 1 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 9182119 = 13773179) B13773179
theorem B1843535 : Blo 475787 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1024559 : Blo 475787 1024559 := bstep (se 1 (by rfl) ⟨768419, by rfl⟩ : syracuseStep 1024559 = 1536839) B1536839
theorem B1286911 : Blo 475787 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B1614977 : Blo 475787 1614977 := bstep (se 2 (by rfl) ⟨605616, by rfl⟩ : syracuseStep 1614977 = 1211233) B1211233
theorem B2172541 : Blo 475787 2172541 := bstep (se 3 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 2172541 = 814703) B814703
theorem B862123 : Blo 475787 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B1616381 : Blo 475787 1616381 := bstep (se 3 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 1616381 = 606143) B606143
theorem B6892127 : Blo 475787 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B1846381 : Blo 475787 1846381 := bstep (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) B692393
theorem B10301863 : Blo 475787 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B2044777 : Blo 475787 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B537691 : Blo 475787 537691 := bstep (se 1 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 537691 = 806537) B806537
theorem B2045513 : Blo 475787 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B1816289 : Blo 475787 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B1357991 : Blo 475787 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B5159375 : Blo 475787 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B539743 : Blo 475787 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B4341833 : Blo 475787 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B2048399 : Blo 475787 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B11289203 : Blo 475787 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B26231597 : Blo 475787 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1721303 : Blo 475787 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B476127 : Blo 475787 476127 := bstep (se 1 (by rfl) ⟨357095, by rfl⟩ : syracuseStep 476127 = 714191) B714191
theorem B476191 : Blo 475787 476191 := bstep (se 1 (by rfl) ⟨357143, by rfl⟩ : syracuseStep 476191 = 714287) B714287
theorem B476391 : Blo 475787 476391 := bstep (se 1 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 476391 = 714587) B714587
theorem B476443 : Blo 475787 476443 := bstep (se 1 (by rfl) ⟨357332, by rfl⟩ : syracuseStep 476443 = 714665) B714665
theorem B2409911 : Blo 475787 2409911 := bstep (se 1 (by rfl) ⟨1807433, by rfl⟩ : syracuseStep 2409911 = 3614867) B3614867
theorem B509375 : Blo 475787 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B804343 : Blo 475787 804343 := bstep (se 1 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 804343 = 1206515) B1206515
theorem B477019 : Blo 475787 477019 := bstep (se 1 (by rfl) ⟨357764, by rfl⟩ : syracuseStep 477019 = 715529) B715529
theorem B3066295 : Blo 475787 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B477679 : Blo 475787 477679 := bstep (se 1 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 477679 = 716519) B716519
theorem B478063 : Blo 475787 478063 := bstep (se 1 (by rfl) ⟨358547, by rfl⟩ : syracuseStep 478063 = 717095) B717095
theorem B478191 : Blo 475787 478191 := bstep (se 1 (by rfl) ⟨358643, by rfl⟩ : syracuseStep 478191 = 717287) B717287
theorem B478751 : Blo 475787 478751 := bstep (se 1 (by rfl) ⟨359063, by rfl⟩ : syracuseStep 478751 = 718127) B718127
theorem B904841 : Blo 475787 904841 := bstep (se 2 (by rfl) ⟨339315, by rfl⟩ : syracuseStep 904841 = 678631) B678631
theorem B1363709 : Blo 475787 1363709 := bstep (se 3 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 1363709 = 511391) B511391
theorem B15945599 : Blo 475787 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B479391 : Blo 475787 479391 := bstep (se 1 (by rfl) ⟨359543, by rfl⟩ : syracuseStep 479391 = 719087) B719087
theorem B479515 : Blo 475787 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B479647 : Blo 475787 479647 := bstep (se 1 (by rfl) ⟨359735, by rfl⟩ : syracuseStep 479647 = 719471) B719471
theorem B2412989 : Blo 475787 2412989 := bstep (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) B904871
theorem B2184509 : Blo 475787 2184509 := bstep (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) B819191
theorem B808447 : Blo 475787 808447 := bstep (se 1 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 808447 = 1212671) B1212671
theorem B8148761 : Blo 475787 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B1070927 : Blo 475787 1070927 := bstep (se 1 (by rfl) ⟨803195, by rfl⟩ : syracuseStep 1070927 = 1606391) B1606391
theorem B3627017 : Blo 475787 3627017 := bstep (se 2 (by rfl) ⟨1360131, by rfl⟩ : syracuseStep 3627017 = 2720263) B2720263
theorem B29775923 : Blo 475787 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B4610591 : Blo 475787 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B4414823 : Blo 475787 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B3628475 : Blo 475787 3628475 := bstep (se 1 (by rfl) ⟨2721356, by rfl⟩ : syracuseStep 3628475 = 5442713) B5442713
theorem B1072745 : Blo 475787 1072745 := bstep (se 2 (by rfl) ⟨402279, by rfl⟩ : syracuseStep 1072745 = 804559) B804559
theorem B2908007 : Blo 475787 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B1073339 : Blo 475787 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B1205513 : Blo 475787 1205513 := bstep (se 2 (by rfl) ⟨452067, by rfl⟩ : syracuseStep 1205513 = 904135) B904135
theorem B1074743 : Blo 475787 1074743 := bstep (se 1 (by rfl) ⟨806057, by rfl⟩ : syracuseStep 1074743 = 1612115) B1612115
theorem B255682115 : Blo 475787 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B62580869 : Blo 475787 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B1075355 : Blo 475787 1075355 := bstep (se 1 (by rfl) ⟨806516, by rfl⟩ : syracuseStep 1075355 = 1613033) B1613033
theorem B53701177 : Blo 475787 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B716015 : Blo 475787 716015 := bstep (se 1 (by rfl) ⟨537011, by rfl⟩ : syracuseStep 716015 = 1074023) B1074023
theorem B1535507 : Blo 475787 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B1208155 : Blo 475787 1208155 := bstep (se 1 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 1208155 = 1812233) B1812233
theorem B1241057 : Blo 475787 1241057 := bstep (se 2 (by rfl) ⟨465396, by rfl⟩ : syracuseStep 1241057 = 930793) B930793
theorem B1077227 : Blo 475787 1077227 := bstep (se 1 (by rfl) ⟨807920, by rfl⟩ : syracuseStep 1077227 = 1615841) B1615841
theorem B1077407 : Blo 475787 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B716969 : Blo 475787 716969 := bstep (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) B537727
theorem B717467 : Blo 475787 717467 := bstep (se 1 (by rfl) ⟨538100, by rfl⟩ : syracuseStep 717467 = 1076201) B1076201
theorem B719183 : Blo 475787 719183 := bstep (se 1 (by rfl) ⟨539387, by rfl⟩ : syracuseStep 719183 = 1078775) B1078775
theorem B55769593 : Blo 475787 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B2063465 : Blo 475787 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B52887811 : Blo 475787 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B3277199 : Blo 475787 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B1147535 : Blo 475787 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B1606607 : Blo 475787 1606607 := bstep (se 1 (by rfl) ⟨1204955, by rfl⟩ : syracuseStep 1606607 = 2409911) B2409911
theorem B2427407 : Blo 475787 2427407 := bstep (se 1 (by rfl) ⟨1820555, by rfl⟩ : syracuseStep 2427407 = 3641111) B3641111
theorem B1149497 : Blo 475787 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B1608659 : Blo 475787 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B920851 : Blo 475787 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B71601569 : Blo 475787 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B76386341 : Blo 475787 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B2461841 : Blo 475787 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B1610873 : Blo 475787 1610873 := bstep (se 2 (by rfl) ⟨604077, by rfl⟩ : syracuseStep 1610873 = 1208155) B1208155
theorem B1938671 : Blo 475787 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B13735817 : Blo 475787 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B2726369 : Blo 475787 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B41720579 : Blo 475787 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B4594751 : Blo 475787 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B1023671 : Blo 475787 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B827371 : Blo 475787 827371 := bstep (se 1 (by rfl) ⟨620528, by rfl⟩ : syracuseStep 827371 = 1241057) B1241057
theorem B74359457 : Blo 475787 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B2894555 : Blo 475787 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B1617083 : Blo 475787 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B1699000271 : Blo 475787 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B2896721 : Blo 475787 2896721 := bstep (se 2 (by rfl) ⟨1086270, by rfl⟩ : syracuseStep 2896721 = 2172541) B2172541
theorem B603227 : Blo 475787 603227 := bstep (se 1 (by rfl) ⟨452420, by rfl⟩ : syracuseStep 603227 = 904841) B904841
theorem B10630399 : Blo 475787 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B767279 : Blo 475787 767279 := bstep (se 1 (by rfl) ⟨575459, by rfl⟩ : syracuseStep 767279 = 1150919) B1150919
theorem B1358333 : Blo 475787 1358333 := bstep (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) B509375
theorem B6863525 : Blo 475787 6863525 := bstep (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) B1286911
theorem B1229023 : Blo 475787 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B803675 : Blo 475787 803675 := bstep (se 1 (by rfl) ⟨602756, by rfl⟩ : syracuseStep 803675 = 1205513) B1205513
theorem B477343 : Blo 475787 477343 := bstep (se 1 (by rfl) ⟨358007, by rfl⟩ : syracuseStep 477343 = 716015) B716015
theorem B477979 : Blo 475787 477979 := bstep (se 1 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 477979 = 716969) B716969
theorem B478311 : Blo 475787 478311 := bstep (se 1 (by rfl) ⟨358733, by rfl⟩ : syracuseStep 478311 = 717467) B717467
theorem B1363675 : Blo 475787 1363675 := bstep (se 1 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 1363675 = 2045513) B2045513
theorem B12242825 : Blo 475787 12242825 := bstep (se 2 (by rfl) ⟨4591059, by rfl⟩ : syracuseStep 12242825 = 9182119) B9182119
theorem B905327 : Blo 475787 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B479455 : Blo 475787 479455 := bstep (se 1 (by rfl) ⟨359591, by rfl⟩ : syracuseStep 479455 = 719183) B719183
theorem B808427 : Blo 475787 808427 := bstep (se 1 (by rfl) ⟨606320, by rfl⟩ : syracuseStep 808427 = 1212641) B1212641
theorem B1365599 : Blo 475787 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B7526135 : Blo 475787 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B17487731 : Blo 475787 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1071359 : Blo 475787 1071359 := bstep (se 1 (by rfl) ⟨803519, by rfl⟩ : syracuseStep 1071359 = 1607039) B1607039
theorem B1072457 : Blo 475787 1072457 := bstep (se 2 (by rfl) ⟨402171, by rfl⟩ : syracuseStep 1072457 = 804343) B804343
theorem B1072799 : Blo 475787 1072799 := bstep (se 1 (by rfl) ⟨804599, by rfl⟩ : syracuseStep 1072799 = 1609199) B1609199
theorem B909139 : Blo 475787 909139 := bstep (se 1 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 909139 = 1363709) B1363709
theorem B4088393 : Blo 475787 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B5825357 : Blo 475787 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B5432507 : Blo 475787 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B713951 : Blo 475787 713951 := bstep (se 1 (by rfl) ⟨535463, by rfl⟩ : syracuseStep 713951 = 1070927) B1070927
theorem B4089143 : Blo 475787 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B2418011 : Blo 475787 2418011 := bstep (se 1 (by rfl) ⟨1813508, by rfl⟩ : syracuseStep 2418011 = 3627017) B3627017
theorem B19850615 : Blo 475787 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B3073727 : Blo 475787 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B2943215 : Blo 475787 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B2418983 : Blo 475787 2418983 := bstep (se 1 (by rfl) ⟨1814237, by rfl⟩ : syracuseStep 2418983 = 3628475) B3628475
theorem B715163 : Blo 475787 715163 := bstep (se 1 (by rfl) ⟨536372, by rfl⟩ : syracuseStep 715163 = 1072745) B1072745
theorem B715559 : Blo 475787 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B683039 : Blo 475787 683039 := bstep (se 1 (by rfl) ⟨512279, by rfl⟩ : syracuseStep 683039 = 1024559) B1024559
theorem B1076651 : Blo 475787 1076651 := bstep (se 1 (by rfl) ⟨807488, by rfl⟩ : syracuseStep 1076651 = 1614977) B1614977
theorem B716495 : Blo 475787 716495 := bstep (se 1 (by rfl) ⟨537371, by rfl⟩ : syracuseStep 716495 = 1074743) B1074743
theorem B170454743 : Blo 475787 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B716903 : Blo 475787 716903 := bstep (se 1 (by rfl) ⟨537677, by rfl⟩ : syracuseStep 716903 = 1075355) B1075355
theorem B716921 : Blo 475787 716921 := bstep (se 2 (by rfl) ⟨268845, by rfl⟩ : syracuseStep 716921 = 537691) B537691
theorem B1077587 : Blo 475787 1077587 := bstep (se 1 (by rfl) ⟨808190, by rfl⟩ : syracuseStep 1077587 = 1616381) B1616381
theorem B1077929 : Blo 475787 1077929 := bstep (se 2 (by rfl) ⟨404223, by rfl⟩ : syracuseStep 1077929 = 808447) B808447
theorem B718151 : Blo 475787 718151 := bstep (se 1 (by rfl) ⟨538613, by rfl⟩ : syracuseStep 718151 = 1077227) B1077227
theorem B718271 : Blo 475787 718271 := bstep (se 1 (by rfl) ⟨538703, by rfl⟩ : syracuseStep 718271 = 1077407) B1077407
theorem B1210859 : Blo 475787 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B719657 : Blo 475787 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B3439583 : Blo 475787 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B1375643 : Blo 475787 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B70517081 : Blo 475787 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B6554789 : Blo 475787 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B8161883 : Blo 475787 8161883 := bstep (se 1 (by rfl) ⟨6121412, by rfl⟩ : syracuseStep 8161883 = 12242825) B12242825
theorem B50924227 : Blo 475787 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B1641227 : Blo 475787 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B1608605 : Blo 475787 1608605 := bstep (se 3 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 1608605 = 603227) B603227
theorem B5017423 : Blo 475787 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B3641597 : Blo 475787 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B2725595 : Blo 475787 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B2726095 : Blo 475787 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B1612007 : Blo 475787 1612007 := bstep (se 1 (by rfl) ⟨1209005, by rfl⟩ : syracuseStep 1612007 = 2418011) B2418011
theorem B1612655 : Blo 475787 1612655 := bstep (se 1 (by rfl) ⟨1209491, by rfl⟩ : syracuseStep 1612655 = 2418983) B2418983
theorem B1132666847 : Blo 475787 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B765023 : Blo 475787 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B535783 : Blo 475787 535783 := bstep (se 1 (by rfl) ⟨401837, by rfl⟩ : syracuseStep 535783 = 803675) B803675
theorem B1618271 : Blo 475787 1618271 := bstep (se 1 (by rfl) ⟨1213703, by rfl⟩ : syracuseStep 1618271 = 2427407) B2427407
theorem B766331 : Blo 475787 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B603551 : Blo 475787 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B1292447 : Blo 475787 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B538951 : Blo 475787 538951 := bstep (se 1 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 538951 = 808427) B808427
theorem B9157211 : Blo 475787 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B1817579 : Blo 475787 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B3063167 : Blo 475787 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B1818233 : Blo 475787 1818233 := bstep (se 2 (by rfl) ⟨681837, by rfl⟩ : syracuseStep 1818233 = 1363675) B1363675
theorem B3883571 : Blo 475787 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B3621671 : Blo 475787 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B475967 : Blo 475787 475967 := bstep (se 1 (by rfl) ⟨356975, by rfl⟩ : syracuseStep 475967 = 713951) B713951
theorem B2049151 : Blo 475787 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B476775 : Blo 475787 476775 := bstep (se 1 (by rfl) ⟨357581, by rfl⟩ : syracuseStep 476775 = 715163) B715163
theorem B14173865 : Blo 475787 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B477039 : Blo 475787 477039 := bstep (se 1 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 477039 = 715559) B715559
theorem B7718813 : Blo 475787 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B477663 : Blo 475787 477663 := bstep (se 1 (by rfl) ⟨358247, by rfl⟩ : syracuseStep 477663 = 716495) B716495
theorem B477935 : Blo 475787 477935 := bstep (se 1 (by rfl) ⟨358451, by rfl⟩ : syracuseStep 477935 = 716903) B716903
theorem B477947 : Blo 475787 477947 := bstep (se 1 (by rfl) ⟨358460, by rfl⟩ : syracuseStep 477947 = 716921) B716921
theorem B1821437 : Blo 475787 1821437 := bstep (se 3 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 1821437 = 683039) B683039
theorem B511519 : Blo 475787 511519 := bstep (se 1 (by rfl) ⟨383639, by rfl⟩ : syracuseStep 511519 = 767279) B767279
theorem B478767 : Blo 475787 478767 := bstep (se 1 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 478767 = 718151) B718151
theorem B478847 : Blo 475787 478847 := bstep (se 1 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 478847 = 718271) B718271
theorem B807239 : Blo 475787 807239 := bstep (se 1 (by rfl) ⟨605429, by rfl⟩ : syracuseStep 807239 = 1210859) B1210859
theorem B905555 : Blo 475787 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B4575683 : Blo 475787 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B479771 : Blo 475787 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B4412645 : Blo 475787 4412645 := bstep (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) B827371
theorem B1071071 : Blo 475787 1071071 := bstep (se 1 (by rfl) ⟨803303, by rfl⟩ : syracuseStep 1071071 = 1606607) B1606607
theorem B8739197 : Blo 475787 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B1072439 : Blo 475787 1072439 := bstep (se 1 (by rfl) ⟨804329, by rfl⟩ : syracuseStep 1072439 = 1608659) B1608659
theorem B47734379 : Blo 475787 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B1073915 : Blo 475787 1073915 := bstep (se 1 (by rfl) ⟨805436, by rfl⟩ : syracuseStep 1073915 = 1610873) B1610873
theorem B11658487 : Blo 475787 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B714239 : Blo 475787 714239 := bstep (se 1 (by rfl) ⟨535679, by rfl⟩ : syracuseStep 714239 = 1071359) B1071359
theorem B27813719 : Blo 475787 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B714971 : Blo 475787 714971 := bstep (se 1 (by rfl) ⟨536228, by rfl⟩ : syracuseStep 714971 = 1072457) B1072457
theorem B715199 : Blo 475787 715199 := bstep (se 1 (by rfl) ⟨536399, by rfl⟩ : syracuseStep 715199 = 1072799) B1072799
theorem B682447 : Blo 475787 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B49572971 : Blo 475787 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B13233743 : Blo 475787 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B4911205 : Blo 475787 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B1962143 : Blo 475787 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B1078055 : Blo 475787 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B717767 : Blo 475787 717767 := bstep (se 1 (by rfl) ⟨538325, by rfl⟩ : syracuseStep 717767 = 1076651) B1076651
theorem B113636495 : Blo 475787 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B718391 : Blo 475787 718391 := bstep (se 1 (by rfl) ⟨538793, by rfl⟩ : syracuseStep 718391 = 1077587) B1077587
theorem B718619 : Blo 475787 718619 := bstep (se 1 (by rfl) ⟨538964, by rfl⟩ : syracuseStep 718619 = 1077929) B1077929
theorem B1931147 : Blo 475787 1931147 := bstep (se 1 (by rfl) ⟨1448360, by rfl⟩ : syracuseStep 1931147 = 2896721) B2896721
theorem B2293055 : Blo 475787 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B917095 : Blo 475787 917095 := bstep (se 1 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 917095 = 1375643) B1375643
theorem B1212185 : Blo 475787 1212185 := bstep (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) B909139
theorem B2589047 : Blo 475787 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B5145875 : Blo 475787 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B5441255 : Blo 475787 5441255 := bstep (se 1 (by rfl) ⟨4080941, by rfl⟩ : syracuseStep 5441255 = 8161883) B8161883
theorem B1214291 : Blo 475787 1214291 := bstep (se 1 (by rfl) ⟨910718, by rfl⟩ : syracuseStep 1214291 = 1821437) B1821437
theorem B2427731 : Blo 475787 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B3050455 : Blo 475787 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B67898969 : Blo 475787 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B1609469 : Blo 475787 1609469 := bstep (se 3 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 1609469 = 603551) B603551
theorem B31822919 : Blo 475787 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B6689897 : Blo 475787 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B755111231 : Blo 475787 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B3446525 : Blo 475787 3446525 := bstep (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) B1292447
theorem B8822495 : Blo 475787 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B2040061 : Blo 475787 2040061 := bstep (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) B765023
theorem B1287431 : Blo 475787 1287431 := bstep (se 1 (by rfl) ⟨965573, by rfl⟩ : syracuseStep 1287431 = 1931147) B1931147
theorem B6104807 : Blo 475787 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B1222793 : Blo 475787 1222793 := bstep (se 2 (by rfl) ⟨458547, by rfl⟩ : syracuseStep 1222793 = 917095) B917095
theorem B2042111 : Blo 475787 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B4369859 : Blo 475787 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B9449243 : Blo 475787 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B2732201 : Blo 475787 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B15544649 : Blo 475787 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B538159 : Blo 475787 538159 := bstep (se 1 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 538159 = 807239) B807239
theorem B603703 : Blo 475787 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B1817063 : Blo 475787 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B476159 : Blo 475787 476159 := bstep (se 1 (by rfl) ⟨357119, by rfl⟩ : syracuseStep 476159 = 714239) B714239
theorem B476647 : Blo 475787 476647 := bstep (se 1 (by rfl) ⟨357485, by rfl⟩ : syracuseStep 476647 = 714971) B714971
theorem B476799 : Blo 475787 476799 := bstep (se 1 (by rfl) ⟨357599, by rfl⟩ : syracuseStep 476799 = 715199) B715199
theorem B4376605 : Blo 475787 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B33048647 : Blo 475787 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B510887 : Blo 475787 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B478511 : Blo 475787 478511 := bstep (se 1 (by rfl) ⟨358883, by rfl⟩ : syracuseStep 478511 = 717767) B717767
theorem B478927 : Blo 475787 478927 := bstep (se 1 (by rfl) ⟨359195, by rfl⟩ : syracuseStep 478927 = 718391) B718391
theorem B479079 : Blo 475787 479079 := bstep (se 1 (by rfl) ⟨359309, by rfl⟩ : syracuseStep 479079 = 718619) B718619
theorem B1528703 : Blo 475787 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B808123 : Blo 475787 808123 := bstep (se 1 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 808123 = 1212185) B1212185
theorem B47011387 : Blo 475787 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B2414447 : Blo 475787 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B1072403 : Blo 475787 1072403 := bstep (se 1 (by rfl) ⟨804302, by rfl⟩ : syracuseStep 1072403 = 1608605) B1608605
theorem B909929 : Blo 475787 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B2941763 : Blo 475787 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B714047 : Blo 475787 714047 := bstep (se 1 (by rfl) ⟨535535, by rfl⟩ : syracuseStep 714047 = 1071071) B1071071
theorem B1074671 : Blo 475787 1074671 := bstep (se 1 (by rfl) ⟨806003, by rfl⟩ : syracuseStep 1074671 = 1612007) B1612007
theorem B5826131 : Blo 475787 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B714377 : Blo 475787 714377 := bstep (se 2 (by rfl) ⟨267891, by rfl⟩ : syracuseStep 714377 = 535783) B535783
theorem B1075103 : Blo 475787 1075103 := bstep (se 1 (by rfl) ⟨806327, by rfl⟩ : syracuseStep 1075103 = 1612655) B1612655
theorem B682025 : Blo 475787 682025 := bstep (se 2 (by rfl) ⟨255759, by rfl⟩ : syracuseStep 682025 = 511519) B511519
theorem B714959 : Blo 475787 714959 := bstep (se 1 (by rfl) ⟨536219, by rfl⟩ : syracuseStep 714959 = 1072439) B1072439
theorem B6548273 : Blo 475787 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B715943 : Blo 475787 715943 := bstep (se 1 (by rfl) ⟨536957, by rfl⟩ : syracuseStep 715943 = 1073915) B1073915
theorem B18542479 : Blo 475787 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1308095 : Blo 475787 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B1078847 : Blo 475787 1078847 := bstep (se 1 (by rfl) ⟨809135, by rfl⟩ : syracuseStep 1078847 = 1618271) B1618271
theorem B3634793 : Blo 475787 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B718601 : Blo 475787 718601 := bstep (se 2 (by rfl) ⟨269475, by rfl⟩ : syracuseStep 718601 = 538951) B538951
theorem B718703 : Blo 475787 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B75757663 : Blo 475787 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B1211719 : Blo 475787 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B1212155 : Blo 475787 1212155 := bstep (se 1 (by rfl) ⟨909116, by rfl⟩ : syracuseStep 1212155 = 1818233) B1818233
theorem B2720081 : Blo 475787 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B41452397 : Blo 475787 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B5835473 : Blo 475787 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B1019135 : Blo 475787 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B4459931 : Blo 475787 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B2297683 : Blo 475787 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B1609631 : Blo 475787 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B4067273 : Blo 475787 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B5445629 : Blo 475787 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B858287 : Blo 475787 858287 := bstep (se 1 (by rfl) ⟨643715, by rfl⟩ : syracuseStep 858287 = 1287431) B1287431
theorem B4069871 : Blo 475787 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B4365515 : Blo 475787 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B6299495 : Blo 475787 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B1615625 : Blo 475787 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B404040869 : Blo 475787 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B22032431 : Blo 475787 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B1618487 : Blo 475787 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B7844701 : Blo 475787 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B45265979 : Blo 475787 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B21215279 : Blo 475787 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B5881663 : Blo 475787 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B24723305 : Blo 475787 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B1818733 : Blo 475787 1818733 := bstep (se 3 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 1818733 = 682025) B682025
theorem B606619 : Blo 475787 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B476031 : Blo 475787 476031 := bstep (se 1 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 476031 = 714047) B714047
theorem B3884087 : Blo 475787 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B476251 : Blo 475787 476251 := bstep (se 1 (by rfl) ⟨357188, by rfl⟩ : syracuseStep 476251 = 714377) B714377
theorem B476639 : Blo 475787 476639 := bstep (se 1 (by rfl) ⟨357479, by rfl⟩ : syracuseStep 476639 = 714959) B714959
theorem B804937 : Blo 475787 804937 := bstep (se 2 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 804937 = 603703) B603703
theorem B477295 : Blo 475787 477295 := bstep (se 1 (by rfl) ⟨357971, by rfl⟩ : syracuseStep 477295 = 715943) B715943
theorem B1362365 : Blo 475787 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B1821467 : Blo 475787 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B872063 : Blo 475787 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B479067 : Blo 475787 479067 := bstep (se 1 (by rfl) ⟨359300, by rfl⟩ : syracuseStep 479067 = 718601) B718601
theorem B479135 : Blo 475787 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B808103 : Blo 475787 808103 := bstep (se 1 (by rfl) ⟨606077, by rfl⟩ : syracuseStep 808103 = 1212155) B1212155
theorem B1726031 : Blo 475787 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B3430583 : Blo 475787 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3627503 : Blo 475787 3627503 := bstep (se 1 (by rfl) ⟨2720627, by rfl⟩ : syracuseStep 3627503 = 5441255) B5441255
theorem B809527 : Blo 475787 809527 := bstep (se 1 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 809527 = 1214291) B1214291
theorem B1072979 : Blo 475787 1072979 := bstep (se 1 (by rfl) ⟨804734, by rfl⟩ : syracuseStep 1072979 = 1609469) B1609469
theorem B503407487 : Blo 475787 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B714935 : Blo 475787 714935 := bstep (se 1 (by rfl) ⟨536201, by rfl⟩ : syracuseStep 714935 = 1072403) B1072403
theorem B716447 : Blo 475787 716447 := bstep (se 1 (by rfl) ⟨537335, by rfl⟩ : syracuseStep 716447 = 1074671) B1074671
theorem B716735 : Blo 475787 716735 := bstep (se 1 (by rfl) ⟨537551, by rfl⟩ : syracuseStep 716735 = 1075103) B1075103
theorem B815195 : Blo 475787 815195 := bstep (se 1 (by rfl) ⟨611396, by rfl⟩ : syracuseStep 815195 = 1222793) B1222793
theorem B1077497 : Blo 475787 1077497 := bstep (se 2 (by rfl) ⟨404061, by rfl⟩ : syracuseStep 1077497 = 808123) B808123
theorem B717545 : Blo 475787 717545 := bstep (se 2 (by rfl) ⟨269079, by rfl⟩ : syracuseStep 717545 = 538159) B538159
theorem B62681849 : Blo 475787 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B2913239 : Blo 475787 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B719231 : Blo 475787 719231 := bstep (se 1 (by rfl) ⟨539423, by rfl⟩ : syracuseStep 719231 = 1078847) B1078847
theorem B2423195 : Blo 475787 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B1211375 : Blo 475787 1211375 := bstep (se 1 (by rfl) ⟨908531, by rfl⟩ : syracuseStep 1211375 = 1817063) B1817063
theorem B2424977 : Blo 475787 2424977 := bstep (se 2 (by rfl) ⟨909366, by rfl⟩ : syracuseStep 2424977 = 1818733) B1818733
theorem B2589391 : Blo 475787 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B1214311 : Blo 475787 1214311 := bstep (se 1 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 1214311 = 1821467) B1821467
theorem B1150687 : Blo 475787 1150687 := bstep (se 1 (by rfl) ⟨863015, by rfl⟩ : syracuseStep 1150687 = 1726031) B1726031
theorem B4199663 : Blo 475787 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B10459601 : Blo 475787 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B269360579 : Blo 475787 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B14688287 : Blo 475787 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B41787899 : Blo 475787 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B1942159 : Blo 475787 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B1615463 : Blo 475787 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B7842217 : Blo 475787 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1813387 : Blo 475787 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B2173853 : Blo 475787 2173853 := bstep (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) B815195
theorem B27634931 : Blo 475787 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B538735 : Blo 475787 538735 := bstep (se 1 (by rfl) ⟨404051, by rfl⟩ : syracuseStep 538735 = 808103) B808103
theorem B572191 : Blo 475787 572191 := bstep (se 1 (by rfl) ⟨429143, by rfl⟩ : syracuseStep 572191 = 858287) B858287
theorem B3063577 : Blo 475787 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B476623 : Blo 475787 476623 := bstep (se 1 (by rfl) ⟨357467, by rfl⟩ : syracuseStep 476623 = 714935) B714935
theorem B477631 : Blo 475787 477631 := bstep (se 1 (by rfl) ⟨358223, by rfl⟩ : syracuseStep 477631 = 716447) B716447
theorem B477823 : Blo 475787 477823 := bstep (se 1 (by rfl) ⟨358367, by rfl⟩ : syracuseStep 477823 = 716735) B716735
theorem B478363 : Blo 475787 478363 := bstep (se 1 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 478363 = 717545) B717545
theorem B14143519 : Blo 475787 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B479487 : Blo 475787 479487 := bstep (se 1 (by rfl) ⟨359615, by rfl⟩ : syracuseStep 479487 = 719231) B719231
theorem B807583 : Blo 475787 807583 := bstep (se 1 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 807583 = 1211375) B1211375
theorem B808825 : Blo 475787 808825 := bstep (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) B606619
theorem B908243 : Blo 475787 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B3890315 : Blo 475787 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B679423 : Blo 475787 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B2973287 : Blo 475787 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B581375 : Blo 475787 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B1073087 : Blo 475787 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B2711515 : Blo 475787 2711515 := bstep (se 1 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 2711515 = 4067273) B4067273
theorem B1073249 : Blo 475787 1073249 := bstep (se 2 (by rfl) ⟨402468, by rfl⟩ : syracuseStep 1073249 = 804937) B804937
theorem B3630419 : Blo 475787 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B2287055 : Blo 475787 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B2713247 : Blo 475787 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2418335 : Blo 475787 2418335 := bstep (se 1 (by rfl) ⟨1813751, by rfl⟩ : syracuseStep 2418335 = 3627503) B3627503
theorem B2910343 : Blo 475787 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B715319 : Blo 475787 715319 := bstep (se 1 (by rfl) ⟨536489, by rfl⟩ : syracuseStep 715319 = 1072979) B1072979
theorem B335604991 : Blo 475787 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B1077083 : Blo 475787 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B718331 : Blo 475787 718331 := bstep (se 1 (by rfl) ⟨538748, by rfl⟩ : syracuseStep 718331 = 1077497) B1077497
theorem B1078991 : Blo 475787 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B30177319 : Blo 475787 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B1079369 : Blo 475787 1079369 := bstep (se 2 (by rfl) ⟨404763, by rfl⟩ : syracuseStep 1079369 = 809527) B809527
theorem B16482203 : Blo 475787 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B2589545 : Blo 475787 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B10456289 : Blo 475787 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B6098813 : Blo 475787 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B3051685 : Blo 475787 3051685 := bstep (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) B572191
theorem B2593543 : Blo 475787 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B27858599 : Blo 475787 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B1808831 : Blo 475787 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B1612223 : Blo 475787 1612223 := bstep (se 1 (by rfl) ⟨1209167, by rfl⟩ : syracuseStep 1612223 = 2418335) B2418335
theorem B1449235 : Blo 475787 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B18423287 : Blo 475787 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B1550333 : Blo 475787 1550333 := bstep (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) B581375
theorem B10988135 : Blo 475787 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B3615353 : Blo 475787 3615353 := bstep (se 2 (by rfl) ⟨1355757, by rfl⟩ : syracuseStep 3615353 = 2711515) B2711515
theorem B1616651 : Blo 475787 1616651 := bstep (se 1 (by rfl) ⟨1212488, by rfl⟩ : syracuseStep 1616651 = 2424977) B2424977
theorem B1619081 : Blo 475787 1619081 := bstep (se 2 (by rfl) ⟨607155, by rfl⟩ : syracuseStep 1619081 = 1214311) B1214311
theorem B3880457 : Blo 475787 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B2799775 : Blo 475787 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B13810085 : Blo 475787 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B605495 : Blo 475787 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B18858025 : Blo 475787 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B476879 : Blo 475787 476879 := bstep (se 1 (by rfl) ⟨357659, by rfl⟩ : syracuseStep 476879 = 715319) B715319
theorem B478887 : Blo 475787 478887 := bstep (se 1 (by rfl) ⟨359165, by rfl⟩ : syracuseStep 478887 = 718331) B718331
theorem B718294877 : Blo 475787 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B905897 : Blo 475787 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B4084769 : Blo 475787 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B2417849 : Blo 475787 2417849 := bstep (se 2 (by rfl) ⟨906693, by rfl⟩ : syracuseStep 2417849 = 1813387) B1813387
theorem B6973067 : Blo 475787 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B447473321 : Blo 475787 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B1534249 : Blo 475787 1534249 := bstep (se 2 (by rfl) ⟨575343, by rfl⟩ : syracuseStep 1534249 = 1150687) B1150687
theorem B715391 : Blo 475787 715391 := bstep (se 1 (by rfl) ⟨536543, by rfl⟩ : syracuseStep 715391 = 1073087) B1073087
theorem B9792191 : Blo 475787 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B715499 : Blo 475787 715499 := bstep (se 1 (by rfl) ⟨536624, by rfl⟩ : syracuseStep 715499 = 1073249) B1073249
theorem B1076777 : Blo 475787 1076777 := bstep (se 2 (by rfl) ⟨403791, by rfl⟩ : syracuseStep 1076777 = 807583) B807583
theorem B2420279 : Blo 475787 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B1076975 : Blo 475787 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B1078433 : Blo 475787 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B718055 : Blo 475787 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B40236425 : Blo 475787 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B718313 : Blo 475787 718313 := bstep (se 2 (by rfl) ⟨269367, by rfl⟩ : syracuseStep 718313 = 538735) B538735
theorem B719327 : Blo 475787 719327 := bstep (se 1 (by rfl) ⟨539495, by rfl⟩ : syracuseStep 719327 = 1078991) B1078991
theorem B719579 : Blo 475787 719579 := bstep (se 1 (by rfl) ⟨539684, by rfl⟩ : syracuseStep 719579 = 1079369) B1079369
theorem B7928765 : Blo 475787 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B4065875 : Blo 475787 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B2723179 : Blo 475787 2723179 := bstep (se 1 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 2723179 = 4084769) B4084769
theorem B4068913 : Blo 475787 4068913 := bstep (se 2 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 4068913 = 3051685) B3051685
theorem B1611899 : Blo 475787 1611899 := bstep (se 1 (by rfl) ⟨1208924, by rfl⟩ : syracuseStep 1611899 = 2417849) B2417849
theorem B6528127 : Blo 475787 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B1613519 : Blo 475787 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B1614653 : Blo 475787 1614653 := bstep (se 3 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 1614653 = 605495) B605495
theorem B5285843 : Blo 475787 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B100576133 : Blo 475787 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B2045665 : Blo 475787 2045665 := bstep (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) B1534249
theorem B603931 : Blo 475787 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B18594845 : Blo 475787 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B3458057 : Blo 475787 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B1033555 : Blo 475787 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B7325423 : Blo 475787 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B2410235 : Blo 475787 2410235 := bstep (se 1 (by rfl) ⟨1807676, by rfl⟩ : syracuseStep 2410235 = 3615353) B3615353
theorem B476927 : Blo 475787 476927 := bstep (se 1 (by rfl) ⟨357695, by rfl⟩ : syracuseStep 476927 = 715391) B715391
theorem B476999 : Blo 475787 476999 := bstep (se 1 (by rfl) ⟨357749, by rfl⟩ : syracuseStep 476999 = 715499) B715499
theorem B478703 : Blo 475787 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B26824283 : Blo 475787 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B478875 : Blo 475787 478875 := bstep (se 1 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 478875 = 718313) B718313
theorem B479551 : Blo 475787 479551 := bstep (se 1 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 479551 = 719327) B719327
theorem B479719 : Blo 475787 479719 := bstep (se 1 (by rfl) ⟨359789, by rfl⟩ : syracuseStep 479719 = 719579) B719579
theorem B1726363 : Blo 475787 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B6970859 : Blo 475787 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B478863251 : Blo 475787 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B18572399 : Blo 475787 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B1205887 : Blo 475787 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B1074815 : Blo 475787 1074815 := bstep (se 1 (by rfl) ⟨806111, by rfl⟩ : syracuseStep 1074815 = 1612223) B1612223
theorem B12282191 : Blo 475787 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B298315547 : Blo 475787 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B7729253 : Blo 475787 7729253 := bstep (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) B1449235
theorem B1077767 : Blo 475787 1077767 := bstep (se 1 (by rfl) ⟨808325, by rfl⟩ : syracuseStep 1077767 = 1616651) B1616651
theorem B717851 : Blo 475787 717851 := bstep (se 1 (by rfl) ⟨538388, by rfl⟩ : syracuseStep 717851 = 1076777) B1076777
theorem B717983 : Blo 475787 717983 := bstep (se 1 (by rfl) ⟨538487, by rfl⟩ : syracuseStep 717983 = 1076975) B1076975
theorem B3733033 : Blo 475787 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B1079387 : Blo 475787 1079387 := bstep (se 1 (by rfl) ⟨809540, by rfl⟩ : syracuseStep 1079387 = 1619081) B1619081
theorem B718955 : Blo 475787 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B2586971 : Blo 475787 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B9206723 : Blo 475787 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B4883615 : Blo 475787 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B1606823 : Blo 475787 1606823 := bstep (se 1 (by rfl) ⟨1205117, by rfl⟩ : syracuseStep 1606823 = 2410235) B2410235
theorem B1378073 : Blo 475787 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B1607849 : Blo 475787 1607849 := bstep (se 2 (by rfl) ⟨602943, by rfl⟩ : syracuseStep 1607849 = 1205887) B1205887
theorem B67050755 : Blo 475787 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B2727553 : Blo 475787 2727553 := bstep (se 2 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 2727553 = 2045665) B2045665
theorem B198877031 : Blo 475787 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B5152835 : Blo 475787 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B6137815 : Blo 475787 6137815 := bstep (se 1 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 6137815 = 9206723) B9206723
theorem B12396563 : Blo 475787 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B9221485 : Blo 475787 9221485 := bstep (se 3 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 9221485 = 3458057) B3458057
theorem B319242167 : Blo 475787 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B3523895 : Blo 475787 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B5425217 : Blo 475787 5425217 := bstep (se 2 (by rfl) ⟨2034456, by rfl⟩ : syracuseStep 5425217 = 4068913) B4068913
theorem B805241 : Blo 475787 805241 := bstep (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) B603931
theorem B478567 : Blo 475787 478567 := bstep (se 1 (by rfl) ⟨358925, by rfl⟩ : syracuseStep 478567 = 717851) B717851
theorem B478655 : Blo 475787 478655 := bstep (se 1 (by rfl) ⟨358991, by rfl⟩ : syracuseStep 478655 = 717983) B717983
theorem B479303 : Blo 475787 479303 := bstep (se 1 (by rfl) ⟨359477, by rfl⟩ : syracuseStep 479303 = 718955) B718955
theorem B8704169 : Blo 475787 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B1724647 : Blo 475787 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B2710583 : Blo 475787 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B17882855 : Blo 475787 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B1074599 : Blo 475787 1074599 := bstep (se 1 (by rfl) ⟨805949, by rfl⟩ : syracuseStep 1074599 = 1611899) B1611899
theorem B3630905 : Blo 475787 3630905 := bstep (se 2 (by rfl) ⟨1361589, by rfl⟩ : syracuseStep 3630905 = 2723179) B2723179
theorem B4647239 : Blo 475787 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B1075679 : Blo 475787 1075679 := bstep (se 1 (by rfl) ⟨806759, by rfl⟩ : syracuseStep 1075679 = 1613519) B1613519
theorem B1076435 : Blo 475787 1076435 := bstep (se 1 (by rfl) ⟨807326, by rfl⟩ : syracuseStep 1076435 = 1614653) B1614653
theorem B12381599 : Blo 475787 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B716543 : Blo 475787 716543 := bstep (se 1 (by rfl) ⟨537407, by rfl⟩ : syracuseStep 716543 = 1074815) B1074815
theorem B8188127 : Blo 475787 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B4977377 : Blo 475787 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B718511 : Blo 475787 718511 := bstep (se 1 (by rfl) ⟨538883, by rfl⟩ : syracuseStep 718511 = 1077767) B1077767
theorem B719591 : Blo 475787 719591 := bstep (se 1 (by rfl) ⟨539693, by rfl⟩ : syracuseStep 719591 = 1079387) B1079387
theorem B9207269 : Blo 475787 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B918715 : Blo 475787 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B5802779 : Blo 475787 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B1807055 : Blo 475787 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B44700503 : Blo 475787 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B132584687 : Blo 475787 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B2299529 : Blo 475787 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B8264375 : Blo 475787 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B12295313 : Blo 475787 12295313 := bstep (se 2 (by rfl) ⟨4610742, by rfl⟩ : syracuseStep 12295313 = 9221485) B9221485
theorem B3318251 : Blo 475787 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B6138179 : Blo 475787 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B3255743 : Blo 475787 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B3616811 : Blo 475787 3616811 := bstep (se 1 (by rfl) ⟨2712608, by rfl⟩ : syracuseStep 3616811 = 5425217) B5425217
theorem B536827 : Blo 475787 536827 := bstep (se 1 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 536827 = 805241) B805241
theorem B3098159 : Blo 475787 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B477695 : Blo 475787 477695 := bstep (se 1 (by rfl) ⟨358271, by rfl⟩ : syracuseStep 477695 = 716543) B716543
theorem B5458751 : Blo 475787 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B479007 : Blo 475787 479007 := bstep (se 1 (by rfl) ⟨359255, by rfl⟩ : syracuseStep 479007 = 718511) B718511
theorem B479727 : Blo 475787 479727 := bstep (se 1 (by rfl) ⟨359795, by rfl⟩ : syracuseStep 479727 = 719591) B719591
theorem B1071215 : Blo 475787 1071215 := bstep (se 1 (by rfl) ⟨803411, by rfl⟩ : syracuseStep 1071215 = 1606823) B1606823
theorem B2349263 : Blo 475787 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B1071899 : Blo 475787 1071899 := bstep (se 1 (by rfl) ⟨803924, by rfl⟩ : syracuseStep 1071899 = 1607849) B1607849
theorem B8183753 : Blo 475787 8183753 := bstep (se 2 (by rfl) ⟨3068907, by rfl⟩ : syracuseStep 8183753 = 6137815) B6137815
theorem B11921903 : Blo 475787 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B3435223 : Blo 475787 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B716399 : Blo 475787 716399 := bstep (se 1 (by rfl) ⟨537299, by rfl⟩ : syracuseStep 716399 = 1074599) B1074599
theorem B2420603 : Blo 475787 2420603 := bstep (se 1 (by rfl) ⟨1815452, by rfl⟩ : syracuseStep 2420603 = 3630905) B3630905
theorem B717119 : Blo 475787 717119 := bstep (se 1 (by rfl) ⟨537839, by rfl⟩ : syracuseStep 717119 = 1075679) B1075679
theorem B717623 : Blo 475787 717623 := bstep (se 1 (by rfl) ⟨538217, by rfl⟩ : syracuseStep 717623 = 1076435) B1076435
theorem B8254399 : Blo 475787 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B3636737 : Blo 475787 3636737 := bstep (se 2 (by rfl) ⟨1363776, by rfl⟩ : syracuseStep 3636737 = 2727553) B2727553
theorem B212828111 : Blo 475787 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B2065439 : Blo 475787 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B8848669 : Blo 475787 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B3868519 : Blo 475787 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B3639167 : Blo 475787 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B5509583 : Blo 475787 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B8196875 : Blo 475787 8196875 := bstep (se 1 (by rfl) ⟨6147656, by rfl⟩ : syracuseStep 8196875 = 12295313) B12295313
theorem B2170495 : Blo 475787 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B1613735 : Blo 475787 1613735 := bstep (se 1 (by rfl) ⟨1210301, by rfl⟩ : syracuseStep 1613735 = 2420603) B2420603
theorem B1224953 : Blo 475787 1224953 := bstep (se 2 (by rfl) ⟨459357, by rfl⟩ : syracuseStep 1224953 = 918715) B918715
theorem B88389791 : Blo 475787 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B5455835 : Blo 475787 5455835 := bstep (se 1 (by rfl) ⟨4091876, by rfl⟩ : syracuseStep 5455835 = 8183753) B8183753
theorem B7947935 : Blo 475787 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B477599 : Blo 475787 477599 := bstep (se 1 (by rfl) ⟨358199, by rfl⟩ : syracuseStep 477599 = 716399) B716399
theorem B2411207 : Blo 475787 2411207 := bstep (se 1 (by rfl) ⟨1808405, by rfl⟩ : syracuseStep 2411207 = 3616811) B3616811
theorem B478079 : Blo 475787 478079 := bstep (se 1 (by rfl) ⟨358559, by rfl⟩ : syracuseStep 478079 = 717119) B717119
theorem B478415 : Blo 475787 478415 := bstep (se 1 (by rfl) ⟨358811, by rfl⟩ : syracuseStep 478415 = 717623) B717623
theorem B119201341 : Blo 475787 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B1204703 : Blo 475787 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B4580297 : Blo 475787 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B1533019 : Blo 475787 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B714143 : Blo 475787 714143 := bstep (se 1 (by rfl) ⟨535607, by rfl⟩ : syracuseStep 714143 = 1071215) B1071215
theorem B1566175 : Blo 475787 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B714599 : Blo 475787 714599 := bstep (se 1 (by rfl) ⟨535949, by rfl⟩ : syracuseStep 714599 = 1071899) B1071899
theorem B715769 : Blo 475787 715769 := bstep (se 2 (by rfl) ⟨268413, by rfl⟩ : syracuseStep 715769 = 536827) B536827
theorem B11005865 : Blo 475787 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B4092119 : Blo 475787 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B2424491 : Blo 475787 2424491 := bstep (se 1 (by rfl) ⟨1818368, by rfl⟩ : syracuseStep 2424491 = 3636737) B3636737
theorem B141885407 : Blo 475787 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B2426111 : Blo 475787 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B11798225 : Blo 475787 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B1607471 : Blo 475787 1607471 := bstep (se 1 (by rfl) ⟨1205603, by rfl⟩ : syracuseStep 1607471 = 2411207) B2411207
theorem B5507837 : Blo 475787 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B3673055 : Blo 475787 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B3053531 : Blo 475787 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B2728079 : Blo 475787 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B11575973 : Blo 475787 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B58926527 : Blo 475787 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B158935121 : Blo 475787 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B1616327 : Blo 475787 1616327 := bstep (se 1 (by rfl) ⟨1212245, by rfl⟩ : syracuseStep 1616327 = 2424491) B2424491
theorem B2044025 : Blo 475787 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B5158025 : Blo 475787 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B803135 : Blo 475787 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B476095 : Blo 475787 476095 := bstep (se 1 (by rfl) ⟨357071, by rfl⟩ : syracuseStep 476095 = 714143) B714143
theorem B476399 : Blo 475787 476399 := bstep (se 1 (by rfl) ⟨357299, by rfl⟩ : syracuseStep 476399 = 714599) B714599
theorem B477179 : Blo 475787 477179 := bstep (se 1 (by rfl) ⟨357884, by rfl⟩ : syracuseStep 477179 = 715769) B715769
theorem B94590271 : Blo 475787 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B5298623 : Blo 475787 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B2088233 : Blo 475787 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B5464583 : Blo 475787 5464583 := bstep (se 1 (by rfl) ⟨4098437, by rfl⟩ : syracuseStep 5464583 = 8196875) B8196875
theorem B1075823 : Blo 475787 1075823 := bstep (se 1 (by rfl) ⟨806867, by rfl⟩ : syracuseStep 1075823 = 1613735) B1613735
theorem B7337243 : Blo 475787 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B816635 : Blo 475787 816635 := bstep (se 1 (by rfl) ⟨612476, by rfl⟩ : syracuseStep 816635 = 1224953) B1224953
theorem B3637223 : Blo 475787 3637223 := bstep (se 1 (by rfl) ⟨2727917, by rfl⟩ : syracuseStep 3637223 = 5455835) B5455835
theorem B7865483 : Blo 475787 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B3671891 : Blo 475787 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B19565981 : Blo 475787 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B2035687 : Blo 475787 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B3643055 : Blo 475787 3643055 := bstep (se 1 (by rfl) ⟨2732291, by rfl⟩ : syracuseStep 3643055 = 5464583) B5464583
theorem B535423 : Blo 475787 535423 := bstep (se 1 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 535423 = 803135) B803135
theorem B1617407 : Blo 475787 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B1392155 : Blo 475787 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B1818719 : Blo 475787 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B7717315 : Blo 475787 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B105956747 : Blo 475787 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B1362683 : Blo 475787 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B544423 : Blo 475787 544423 := bstep (se 1 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 544423 = 816635) B816635
theorem B1071647 : Blo 475787 1071647 := bstep (se 1 (by rfl) ⟨803735, by rfl⟩ : syracuseStep 1071647 = 1607471) B1607471
theorem B2448703 : Blo 475787 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B3532415 : Blo 475787 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B39284351 : Blo 475787 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B1077551 : Blo 475787 1077551 := bstep (se 1 (by rfl) ⟨808163, by rfl⟩ : syracuseStep 1077551 = 1616327) B1616327
theorem B717215 : Blo 475787 717215 := bstep (se 1 (by rfl) ⟨537911, by rfl⟩ : syracuseStep 717215 = 1075823) B1075823
theorem B126120361 : Blo 475787 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B3438683 : Blo 475787 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B2424815 : Blo 475787 2424815 := bstep (se 1 (by rfl) ⟨1818611, by rfl⟩ : syracuseStep 2424815 = 3637223) B3637223
theorem B1212479 : Blo 475787 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B10289753 : Blo 475787 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B13043987 : Blo 475787 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B20974621 : Blo 475787 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B2428703 : Blo 475787 2428703 := bstep (se 1 (by rfl) ⟨1821527, by rfl⟩ : syracuseStep 2428703 = 3643055) B3643055
theorem B725897 : Blo 475787 725897 := bstep (se 2 (by rfl) ⟨272211, by rfl⟩ : syracuseStep 725897 = 544423) B544423
theorem B26189567 : Blo 475787 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B928103 : Blo 475787 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B1616543 : Blo 475787 1616543 := bstep (se 1 (by rfl) ⟨1212407, by rfl⟩ : syracuseStep 1616543 = 2424815) B2424815
theorem B478143 : Blo 475787 478143 := bstep (se 1 (by rfl) ⟨358607, by rfl⟩ : syracuseStep 478143 = 717215) B717215
theorem B3264937 : Blo 475787 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B70637831 : Blo 475787 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B2447927 : Blo 475787 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B713897 : Blo 475787 713897 := bstep (se 2 (by rfl) ⟨267711, by rfl⟩ : syracuseStep 713897 = 535423) B535423
theorem B714431 : Blo 475787 714431 := bstep (se 1 (by rfl) ⟨535823, by rfl⟩ : syracuseStep 714431 = 1071647) B1071647
theorem B2714249 : Blo 475787 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B168160481 : Blo 475787 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B37679093 : Blo 475787 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B3633821 : Blo 475787 3633821 := bstep (se 3 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 3633821 = 1362683) B1362683
theorem B1078271 : Blo 475787 1078271 := bstep (se 1 (by rfl) ⟨808703, by rfl⟩ : syracuseStep 1078271 = 1617407) B1617407
theorem B718367 : Blo 475787 718367 := bstep (se 1 (by rfl) ⟨538775, by rfl⟩ : syracuseStep 718367 = 1077551) B1077551
theorem B2292455 : Blo 475787 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B9899765 : Blo 475787 9899765 := bstep (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) B928103
theorem B47091887 : Blo 475787 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B1809499 : Blo 475787 1809499 := bstep (se 1 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 1809499 = 2714249) B2714249
theorem B112106987 : Blo 475787 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B6859835 : Blo 475787 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B8695991 : Blo 475787 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B17412997 : Blo 475787 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B1619135 : Blo 475787 1619135 := bstep (se 1 (by rfl) ⟨1214351, by rfl⟩ : syracuseStep 1619135 = 2428703) B2428703
theorem B27966161 : Blo 475787 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B475931 : Blo 475787 475931 := bstep (se 1 (by rfl) ⟨356948, by rfl⟩ : syracuseStep 475931 = 713897) B713897
theorem B476287 : Blo 475787 476287 := bstep (se 1 (by rfl) ⟨357215, by rfl⟩ : syracuseStep 476287 = 714431) B714431
theorem B25119395 : Blo 475787 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B478911 : Blo 475787 478911 := bstep (se 1 (by rfl) ⟨359183, by rfl⟩ : syracuseStep 478911 = 718367) B718367
theorem B1528303 : Blo 475787 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B808319 : Blo 475787 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B483931 : Blo 475787 483931 := bstep (se 1 (by rfl) ⟨362948, by rfl⟩ : syracuseStep 483931 = 725897) B725897
theorem B1631951 : Blo 475787 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B17459711 : Blo 475787 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B1077695 : Blo 475787 1077695 := bstep (se 1 (by rfl) ⟨808271, by rfl⟩ : syracuseStep 1077695 = 1616543) B1616543
theorem B2422547 : Blo 475787 2422547 := bstep (se 1 (by rfl) ⟨1816910, by rfl⟩ : syracuseStep 2422547 = 3633821) B3633821
theorem B718847 : Blo 475787 718847 := bstep (se 1 (by rfl) ⟨539135, by rfl⟩ : syracuseStep 718847 = 1078271) B1078271
theorem B16746263 : Blo 475787 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B31394591 : Blo 475787 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B2037737 : Blo 475787 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B1087967 : Blo 475787 1087967 := bstep (se 1 (by rfl) ⟨815975, by rfl⟩ : syracuseStep 1087967 = 1631951) B1631951
theorem B11639807 : Blo 475787 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B1615031 : Blo 475787 1615031 := bstep (se 1 (by rfl) ⟨1211273, by rfl⟩ : syracuseStep 1615031 = 2422547) B2422547
theorem B6599843 : Blo 475787 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B538879 : Blo 475787 538879 := bstep (se 1 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 538879 = 808319) B808319
theorem B23217329 : Blo 475787 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B4573223 : Blo 475787 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B479231 : Blo 475787 479231 := bstep (se 1 (by rfl) ⟨359423, by rfl⟩ : syracuseStep 479231 = 718847) B718847
theorem B2412665 : Blo 475787 2412665 := bstep (se 2 (by rfl) ⟨904749, by rfl⟩ : syracuseStep 2412665 = 1809499) B1809499
theorem B645241 : Blo 475787 645241 := bstep (se 2 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 645241 = 483931) B483931
theorem B74737991 : Blo 475787 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B5797327 : Blo 475787 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B718463 : Blo 475787 718463 := bstep (se 1 (by rfl) ⟨538847, by rfl⟩ : syracuseStep 718463 = 1077695) B1077695
theorem B1079423 : Blo 475787 1079423 := bstep (se 1 (by rfl) ⟨809567, by rfl⟩ : syracuseStep 1079423 = 1619135) B1619135
theorem B18644107 : Blo 475787 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B3048815 : Blo 475787 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B1608443 : Blo 475787 1608443 := bstep (se 1 (by rfl) ⟨1206332, by rfl⟩ : syracuseStep 1608443 = 2412665) B2412665
theorem B725311 : Blo 475787 725311 := bstep (se 1 (by rfl) ⟨543983, by rfl⟩ : syracuseStep 725311 = 1087967) B1087967
theorem B860321 : Blo 475787 860321 := bstep (se 2 (by rfl) ⟨322620, by rfl⟩ : syracuseStep 860321 = 645241) B645241
theorem B4399895 : Blo 475787 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B15478219 : Blo 475787 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B49825327 : Blo 475787 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B478975 : Blo 475787 478975 := bstep (se 1 (by rfl) ⟨359231, by rfl⟩ : syracuseStep 478975 = 718463) B718463
theorem B24858809 : Blo 475787 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B11164175 : Blo 475787 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B20929727 : Blo 475787 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B7759871 : Blo 475787 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B5433965 : Blo 475787 5433965 := bstep (se 3 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 5433965 = 2037737) B2037737
theorem B1076687 : Blo 475787 1076687 := bstep (se 1 (by rfl) ⟨807515, by rfl⟩ : syracuseStep 1076687 = 1615031) B1615031
theorem B7729769 : Blo 475787 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B718505 : Blo 475787 718505 := bstep (se 2 (by rfl) ⟨269439, by rfl⟩ : syracuseStep 718505 = 538879) B538879
theorem B719615 : Blo 475787 719615 := bstep (se 1 (by rfl) ⟨539711, by rfl⟩ : syracuseStep 719615 = 1079423) B1079423
theorem B2032543 : Blo 475787 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B20612717 : Blo 475787 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B3868325 : Blo 475787 3868325 := bstep (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) B725311
theorem B7442783 : Blo 475787 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B66433769 : Blo 475787 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B573547 : Blo 475787 573547 := bstep (se 1 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 573547 = 860321) B860321
theorem B2933263 : Blo 475787 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B3622643 : Blo 475787 3622643 := bstep (se 1 (by rfl) ⟨2716982, by rfl⟩ : syracuseStep 3622643 = 5433965) B5433965
theorem B479003 : Blo 475787 479003 := bstep (se 1 (by rfl) ⟨359252, by rfl⟩ : syracuseStep 479003 = 718505) B718505
theorem B479743 : Blo 475787 479743 := bstep (se 1 (by rfl) ⟨359807, by rfl⟩ : syracuseStep 479743 = 719615) B719615
theorem B1072295 : Blo 475787 1072295 := bstep (se 1 (by rfl) ⟨804221, by rfl⟩ : syracuseStep 1072295 = 1608443) B1608443
theorem B16572539 : Blo 475787 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B20637625 : Blo 475787 20637625 := bstep (se 2 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 20637625 = 15478219) B15478219
theorem B13953151 : Blo 475787 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B5173247 : Blo 475787 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B717791 : Blo 475787 717791 := bstep (se 1 (by rfl) ⟨538343, by rfl⟩ : syracuseStep 717791 = 1076687) B1076687
theorem B11048359 : Blo 475787 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B3448831 : Blo 475787 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B764729 : Blo 475787 764729 := bstep (se 2 (by rfl) ⟨286773, by rfl⟩ : syracuseStep 764729 = 573547) B573547
theorem B3911017 : Blo 475787 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B13741811 : Blo 475787 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B4961855 : Blo 475787 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B44289179 : Blo 475787 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B478527 : Blo 475787 478527 := bstep (se 1 (by rfl) ⟨358895, by rfl⟩ : syracuseStep 478527 = 717791) B717791
theorem B2578883 : Blo 475787 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B2415095 : Blo 475787 2415095 := bstep (se 1 (by rfl) ⟨1811321, by rfl⟩ : syracuseStep 2415095 = 3622643) B3622643
theorem B2710057 : Blo 475787 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B27516833 : Blo 475787 27516833 := bstep (se 2 (by rfl) ⟨10318812, by rfl⟩ : syracuseStep 27516833 = 20637625) B20637625
theorem B18604201 : Blo 475787 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B714863 : Blo 475787 714863 := bstep (se 1 (by rfl) ⟨536147, by rfl⟩ : syracuseStep 714863 = 1072295) B1072295
theorem B24805601 : Blo 475787 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B29526119 : Blo 475787 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B1610063 : Blo 475787 1610063 := bstep (se 1 (by rfl) ⟨1207547, by rfl⟩ : syracuseStep 1610063 = 2415095) B2415095
theorem B5214689 : Blo 475787 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B3613409 : Blo 475787 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B4598441 : Blo 475787 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B476575 : Blo 475787 476575 := bstep (se 1 (by rfl) ⟨357431, by rfl⟩ : syracuseStep 476575 = 714863) B714863
theorem B509819 : Blo 475787 509819 := bstep (se 1 (by rfl) ⟨382364, by rfl⟩ : syracuseStep 509819 = 764729) B764729
theorem B14731145 : Blo 475787 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B9161207 : Blo 475787 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B13231613 : Blo 475787 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B18344555 : Blo 475787 18344555 := bstep (se 1 (by rfl) ⟨13758416, by rfl⟩ : syracuseStep 18344555 = 27516833) B27516833
theorem B6877021 : Blo 475787 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B3476459 : Blo 475787 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B12229703 : Blo 475787 12229703 := bstep (se 1 (by rfl) ⟨9172277, by rfl⟩ : syracuseStep 12229703 = 18344555) B18344555
theorem B6107471 : Blo 475787 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B1359517 : Blo 475787 1359517 := bstep (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) B509819
theorem B2408939 : Blo 475787 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B3065627 : Blo 475787 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B16537067 : Blo 475787 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B9820763 : Blo 475787 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B19684079 : Blo 475787 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B1073375 : Blo 475787 1073375 := bstep (se 1 (by rfl) ⟨805031, by rfl⟩ : syracuseStep 1073375 = 1610063) B1610063
theorem B35284301 : Blo 475787 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B9169361 : Blo 475787 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B1605959 : Blo 475787 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B4071647 : Blo 475787 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B1812689 : Blo 475787 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B11024711 : Blo 475787 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B13122719 : Blo 475787 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B8175005 : Blo 475787 8175005 := bstep (se 3 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 8175005 = 3065627) B3065627
theorem B6112907 : Blo 475787 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B6547175 : Blo 475787 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B8153135 : Blo 475787 8153135 := bstep (se 1 (by rfl) ⟨6114851, by rfl⟩ : syracuseStep 8153135 = 12229703) B12229703
theorem B715583 : Blo 475787 715583 := bstep (se 1 (by rfl) ⟨536687, by rfl⟩ : syracuseStep 715583 = 1073375) B1073375
theorem B23522867 : Blo 475787 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B9270557 : Blo 475787 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B250910581 : Blo 475787 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B4364783 : Blo 475787 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B7349807 : Blo 475787 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B5450003 : Blo 475787 5450003 := bstep (se 1 (by rfl) ⟨4087502, by rfl⟩ : syracuseStep 5450003 = 8175005) B8175005
theorem B4075271 : Blo 475787 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B477055 : Blo 475787 477055 := bstep (se 1 (by rfl) ⟨357791, by rfl⟩ : syracuseStep 477055 = 715583) B715583
theorem B6180371 : Blo 475787 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B1070639 : Blo 475787 1070639 := bstep (se 1 (by rfl) ⟨802979, by rfl⟩ : syracuseStep 1070639 = 1605959) B1605959
theorem B2714431 : Blo 475787 2714431 := bstep (se 1 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 2714431 = 4071647) B4071647
theorem B5435423 : Blo 475787 5435423 := bstep (se 1 (by rfl) ⟨4076567, by rfl⟩ : syracuseStep 5435423 = 8153135) B8153135
theorem B1208459 : Blo 475787 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B8748479 : Blo 475787 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B3619241 : Blo 475787 3619241 := bstep (se 2 (by rfl) ⟨1357215, by rfl⟩ : syracuseStep 3619241 = 2714431) B2714431
theorem B4899871 : Blo 475787 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B334547441 : Blo 475787 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B3623615 : Blo 475787 3623615 := bstep (se 1 (by rfl) ⟨2717711, by rfl⟩ : syracuseStep 3623615 = 5435423) B5435423
theorem B805639 : Blo 475787 805639 := bstep (se 1 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 805639 = 1208459) B1208459
theorem B4120247 : Blo 475787 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B713759 : Blo 475787 713759 := bstep (se 1 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 713759 = 1070639) B1070639
theorem B2909855 : Blo 475787 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B3633335 : Blo 475787 3633335 := bstep (se 1 (by rfl) ⟨2725001, by rfl⟩ : syracuseStep 3633335 = 5450003) B5450003
theorem B2716847 : Blo 475787 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B5832319 : Blo 475787 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B1811231 : Blo 475787 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B7776425 : Blo 475787 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B223031627 : Blo 475787 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B26132645 : Blo 475787 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B475839 : Blo 475787 475839 := bstep (se 1 (by rfl) ⟨356879, by rfl⟩ : syracuseStep 475839 = 713759) B713759
theorem B2412827 : Blo 475787 2412827 := bstep (se 1 (by rfl) ⟨1809620, by rfl⟩ : syracuseStep 2412827 = 3619241) B3619241
theorem B2415743 : Blo 475787 2415743 := bstep (se 1 (by rfl) ⟨1811807, by rfl⟩ : syracuseStep 2415743 = 3623615) B3623615
theorem B1074185 : Blo 475787 1074185 := bstep (se 2 (by rfl) ⟨402819, by rfl⟩ : syracuseStep 1074185 = 805639) B805639
theorem B7759613 : Blo 475787 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B2746831 : Blo 475787 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B2422223 : Blo 475787 2422223 := bstep (se 1 (by rfl) ⟨1816667, by rfl⟩ : syracuseStep 2422223 = 3633335) B3633335
theorem B1608551 : Blo 475787 1608551 := bstep (se 1 (by rfl) ⟨1206413, by rfl⟩ : syracuseStep 1608551 = 2412827) B2412827
theorem B1610495 : Blo 475787 1610495 := bstep (se 1 (by rfl) ⟨1207871, by rfl⟩ : syracuseStep 1610495 = 2415743) B2415743
theorem B5184283 : Blo 475787 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B1614815 : Blo 475787 1614815 := bstep (se 1 (by rfl) ⟨1211111, by rfl⟩ : syracuseStep 1614815 = 2422223) B2422223
theorem B148687751 : Blo 475787 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B17421763 : Blo 475787 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B3662441 : Blo 475787 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B1207487 : Blo 475787 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B716123 : Blo 475787 716123 := bstep (se 1 (by rfl) ⟨537092, by rfl⟩ : syracuseStep 716123 = 1074185) B1074185
theorem B5173075 : Blo 475787 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B99125167 : Blo 475787 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B6897433 : Blo 475787 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B2441627 : Blo 475787 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B804991 : Blo 475787 804991 := bstep (se 1 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 804991 = 1207487) B1207487
theorem B477415 : Blo 475787 477415 := bstep (se 1 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 477415 = 716123) B716123
theorem B1072367 : Blo 475787 1072367 := bstep (se 1 (by rfl) ⟨804275, by rfl⟩ : syracuseStep 1072367 = 1608551) B1608551
theorem B1073663 : Blo 475787 1073663 := bstep (se 1 (by rfl) ⟨805247, by rfl⟩ : syracuseStep 1073663 = 1610495) B1610495
theorem B1076543 : Blo 475787 1076543 := bstep (se 1 (by rfl) ⟨807407, by rfl⟩ : syracuseStep 1076543 = 1614815) B1614815
theorem B23229017 : Blo 475787 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B6912377 : Blo 475787 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B132166889 : Blo 475787 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B15486011 : Blo 475787 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B4608251 : Blo 475787 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B9196577 : Blo 475787 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B1627751 : Blo 475787 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B1073321 : Blo 475787 1073321 := bstep (se 2 (by rfl) ⟨402495, by rfl⟩ : syracuseStep 1073321 = 804991) B804991
theorem B714911 : Blo 475787 714911 := bstep (se 1 (by rfl) ⟨536183, by rfl⟩ : syracuseStep 714911 = 1072367) B1072367
theorem B715775 : Blo 475787 715775 := bstep (se 1 (by rfl) ⟨536831, by rfl⟩ : syracuseStep 715775 = 1073663) B1073663
theorem B717695 : Blo 475787 717695 := bstep (se 1 (by rfl) ⟨538271, by rfl⟩ : syracuseStep 717695 = 1076543) B1076543
theorem B10324007 : Blo 475787 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B6131051 : Blo 475787 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B1085167 : Blo 475787 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B476607 : Blo 475787 476607 := bstep (se 1 (by rfl) ⟨357455, by rfl⟩ : syracuseStep 476607 = 714911) B714911
theorem B477183 : Blo 475787 477183 := bstep (se 1 (by rfl) ⟨357887, by rfl⟩ : syracuseStep 477183 = 715775) B715775
theorem B478463 : Blo 475787 478463 := bstep (se 1 (by rfl) ⟨358847, by rfl⟩ : syracuseStep 478463 = 717695) B717695
theorem B3072167 : Blo 475787 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B715547 : Blo 475787 715547 := bstep (se 1 (by rfl) ⟨536660, by rfl⟩ : syracuseStep 715547 = 1073321) B1073321
theorem B88111259 : Blo 475787 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B6882671 : Blo 475787 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B1446889 : Blo 475787 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B2048111 : Blo 475787 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B477031 : Blo 475787 477031 := bstep (se 1 (by rfl) ⟨357773, by rfl⟩ : syracuseStep 477031 = 715547) B715547
theorem B58740839 : Blo 475787 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B4087367 : Blo 475787 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B4588447 : Blo 475787 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B39160559 : Blo 475787 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B2724911 : Blo 475787 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B1365407 : Blo 475787 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B1929185 : Blo 475787 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B1286123 : Blo 475787 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B1816607 : Blo 475787 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B6117929 : Blo 475787 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B26107039 : Blo 475787 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B910271 : Blo 475787 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B34809385 : Blo 475787 34809385 := bstep (se 2 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 34809385 = 26107039) B26107039
theorem B4078619 : Blo 475787 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B606847 : Blo 475787 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B3429661 : Blo 475787 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B1211071 : Blo 475787 1211071 := bstep (se 1 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 1211071 = 1816607) B1816607
theorem B1614761 : Blo 475787 1614761 := bstep (se 2 (by rfl) ⟨605535, by rfl⟩ : syracuseStep 1614761 = 1211071) B1211071
theorem B46412513 : Blo 475787 46412513 := bstep (se 2 (by rfl) ⟨17404692, by rfl⟩ : syracuseStep 46412513 = 34809385) B34809385
theorem B4572881 : Blo 475787 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B809129 : Blo 475787 809129 := bstep (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) B606847
theorem B2719079 : Blo 475787 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B3048587 : Blo 475787 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B30941675 : Blo 475787 30941675 := bstep (se 1 (by rfl) ⟨23206256, by rfl⟩ : syracuseStep 30941675 = 46412513) B46412513
theorem B1812719 : Blo 475787 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B539419 : Blo 475787 539419 := bstep (se 1 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 539419 = 809129) B809129
theorem B1076507 : Blo 475787 1076507 := bstep (se 1 (by rfl) ⟨807380, by rfl⟩ : syracuseStep 1076507 = 1614761) B1614761
theorem B2032391 : Blo 475787 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B20627783 : Blo 475787 20627783 := bstep (se 1 (by rfl) ⟨15470837, by rfl⟩ : syracuseStep 20627783 = 30941675) B30941675
theorem B1208479 : Blo 475787 1208479 := bstep (se 1 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 1208479 = 1812719) B1812719
theorem B717671 : Blo 475787 717671 := bstep (se 1 (by rfl) ⟨538253, by rfl⟩ : syracuseStep 717671 = 1076507) B1076507
theorem B719225 : Blo 475787 719225 := bstep (se 2 (by rfl) ⟨269709, by rfl⟩ : syracuseStep 719225 = 539419) B539419
theorem B1611305 : Blo 475787 1611305 := bstep (se 2 (by rfl) ⟨604239, by rfl⟩ : syracuseStep 1611305 = 1208479) B1208479
theorem B1354927 : Blo 475787 1354927 := bstep (se 1 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 1354927 = 2032391) B2032391
theorem B478447 : Blo 475787 478447 := bstep (se 1 (by rfl) ⟨358835, by rfl⟩ : syracuseStep 478447 = 717671) B717671
theorem B479483 : Blo 475787 479483 := bstep (se 1 (by rfl) ⟨359612, by rfl⟩ : syracuseStep 479483 = 719225) B719225
theorem B13751855 : Blo 475787 13751855 := bstep (se 1 (by rfl) ⟨10313891, by rfl⟩ : syracuseStep 13751855 = 20627783) B20627783
theorem B1806569 : Blo 475787 1806569 := bstep (se 2 (by rfl) ⟨677463, by rfl⟩ : syracuseStep 1806569 = 1354927) B1354927
theorem B1074203 : Blo 475787 1074203 := bstep (se 1 (by rfl) ⟨805652, by rfl⟩ : syracuseStep 1074203 = 1611305) B1611305
theorem B9167903 : Blo 475787 9167903 := bstep (se 1 (by rfl) ⟨6875927, by rfl⟩ : syracuseStep 9167903 = 13751855) B13751855
theorem B6111935 : Blo 475787 6111935 := bstep (se 1 (by rfl) ⟨4583951, by rfl⟩ : syracuseStep 6111935 = 9167903) B9167903
theorem B1204379 : Blo 475787 1204379 := bstep (se 1 (by rfl) ⟨903284, by rfl⟩ : syracuseStep 1204379 = 1806569) B1806569
theorem B716135 : Blo 475787 716135 := bstep (se 1 (by rfl) ⟨537101, by rfl⟩ : syracuseStep 716135 = 1074203) B1074203
theorem B4074623 : Blo 475787 4074623 := bstep (se 1 (by rfl) ⟨3055967, by rfl⟩ : syracuseStep 4074623 = 6111935) B6111935
theorem B802919 : Blo 475787 802919 := bstep (se 1 (by rfl) ⟨602189, by rfl⟩ : syracuseStep 802919 = 1204379) B1204379
theorem B477423 : Blo 475787 477423 := bstep (se 1 (by rfl) ⟨358067, by rfl⟩ : syracuseStep 477423 = 716135) B716135
theorem B535279 : Blo 475787 535279 := bstep (se 1 (by rfl) ⟨401459, by rfl⟩ : syracuseStep 535279 = 802919) B802919
theorem B2716415 : Blo 475787 2716415 := bstep (se 1 (by rfl) ⟨2037311, by rfl⟩ : syracuseStep 2716415 = 4074623) B4074623
theorem B1810943 : Blo 475787 1810943 := bstep (se 1 (by rfl) ⟨1358207, by rfl⟩ : syracuseStep 1810943 = 2716415) B2716415
theorem B713705 : Blo 475787 713705 := bstep (se 2 (by rfl) ⟨267639, by rfl⟩ : syracuseStep 713705 = 535279) B535279
theorem B475803 : Blo 475787 475803 := bstep (se 1 (by rfl) ⟨356852, by rfl⟩ : syracuseStep 475803 = 713705) B713705
theorem B1207295 : Blo 475787 1207295 := bstep (se 1 (by rfl) ⟨905471, by rfl⟩ : syracuseStep 1207295 = 1810943) B1810943
theorem B804863 : Blo 475787 804863 := bstep (se 1 (by rfl) ⟨603647, by rfl⟩ : syracuseStep 804863 = 1207295) B1207295
theorem B536575 : Blo 475787 536575 := bstep (se 1 (by rfl) ⟨402431, by rfl⟩ : syracuseStep 536575 = 804863) B804863
theorem B715433 : Blo 475787 715433 := bstep (se 2 (by rfl) ⟨268287, by rfl⟩ : syracuseStep 715433 = 536575) B536575
theorem B476955 : Blo 475787 476955 := bstep (se 1 (by rfl) ⟨357716, by rfl⟩ : syracuseStep 476955 = 715433) B715433

theorem C0 (j : ℕ) (h1 : 118946 ≤ j) (h2 : j ≤ 119645) : Blo 475787 (4 * j + 3) := by
  interval_cases j
  · exact B475787
  · exact B475791
  · exact B475795
  · exact B475799
  · exact B475803
  · exact B475807
  · exact B475811
  · exact B475815
  · exact B475819
  · exact B475823
  · exact B475827
  · exact B475831
  · exact B475835
  · exact B475839
  · exact B475843
  · exact B475847
  · exact B475851
  · exact B475855
  · exact B475859
  · exact B475863
  · exact B475867
  · exact B475871
  · exact B475875
  · exact B475879
  · exact B475883
  · exact B475887
  · exact B475891
  · exact B475895
  · exact B475899
  · exact B475903
  · exact B475907
  · exact B475911
  · exact B475915
  · exact B475919
  · exact B475923
  · exact B475927
  · exact B475931
  · exact B475935
  · exact B475939
  · exact B475943
  · exact B475947
  · exact B475951
  · exact B475955
  · exact B475959
  · exact B475963
  · exact B475967
  · exact B475971
  · exact B475975
  · exact B475979
  · exact B475983
  · exact B475987
  · exact B475991
  · exact B475995
  · exact B475999
  · exact B476003
  · exact B476007
  · exact B476011
  · exact B476015
  · exact B476019
  · exact B476023
  · exact B476027
  · exact B476031
  · exact B476035
  · exact B476039
  · exact B476043
  · exact B476047
  · exact B476051
  · exact B476055
  · exact B476059
  · exact B476063
  · exact B476067
  · exact B476071
  · exact B476075
  · exact B476079
  · exact B476083
  · exact B476087
  · exact B476091
  · exact B476095
  · exact B476099
  · exact B476103
  · exact B476107
  · exact B476111
  · exact B476115
  · exact B476119
  · exact B476123
  · exact B476127
  · exact B476131
  · exact B476135
  · exact B476139
  · exact B476143
  · exact B476147
  · exact B476151
  · exact B476155
  · exact B476159
  · exact B476163
  · exact B476167
  · exact B476171
  · exact B476175
  · exact B476179
  · exact B476183
  · exact B476187
  · exact B476191
  · exact B476195
  · exact B476199
  · exact B476203
  · exact B476207
  · exact B476211
  · exact B476215
  · exact B476219
  · exact B476223
  · exact B476227
  · exact B476231
  · exact B476235
  · exact B476239
  · exact B476243
  · exact B476247
  · exact B476251
  · exact B476255
  · exact B476259
  · exact B476263
  · exact B476267
  · exact B476271
  · exact B476275
  · exact B476279
  · exact B476283
  · exact B476287
  · exact B476291
  · exact B476295
  · exact B476299
  · exact B476303
  · exact B476307
  · exact B476311
  · exact B476315
  · exact B476319
  · exact B476323
  · exact B476327
  · exact B476331
  · exact B476335
  · exact B476339
  · exact B476343
  · exact B476347
  · exact B476351
  · exact B476355
  · exact B476359
  · exact B476363
  · exact B476367
  · exact B476371
  · exact B476375
  · exact B476379
  · exact B476383
  · exact B476387
  · exact B476391
  · exact B476395
  · exact B476399
  · exact B476403
  · exact B476407
  · exact B476411
  · exact B476415
  · exact B476419
  · exact B476423
  · exact B476427
  · exact B476431
  · exact B476435
  · exact B476439
  · exact B476443
  · exact B476447
  · exact B476451
  · exact B476455
  · exact B476459
  · exact B476463
  · exact B476467
  · exact B476471
  · exact B476475
  · exact B476479
  · exact B476483
  · exact B476487
  · exact B476491
  · exact B476495
  · exact B476499
  · exact B476503
  · exact B476507
  · exact B476511
  · exact B476515
  · exact B476519
  · exact B476523
  · exact B476527
  · exact B476531
  · exact B476535
  · exact B476539
  · exact B476543
  · exact B476547
  · exact B476551
  · exact B476555
  · exact B476559
  · exact B476563
  · exact B476567
  · exact B476571
  · exact B476575
  · exact B476579
  · exact B476583
  · exact B476587
  · exact B476591
  · exact B476595
  · exact B476599
  · exact B476603
  · exact B476607
  · exact B476611
  · exact B476615
  · exact B476619
  · exact B476623
  · exact B476627
  · exact B476631
  · exact B476635
  · exact B476639
  · exact B476643
  · exact B476647
  · exact B476651
  · exact B476655
  · exact B476659
  · exact B476663
  · exact B476667
  · exact B476671
  · exact B476675
  · exact B476679
  · exact B476683
  · exact B476687
  · exact B476691
  · exact B476695
  · exact B476699
  · exact B476703
  · exact B476707
  · exact B476711
  · exact B476715
  · exact B476719
  · exact B476723
  · exact B476727
  · exact B476731
  · exact B476735
  · exact B476739
  · exact B476743
  · exact B476747
  · exact B476751
  · exact B476755
  · exact B476759
  · exact B476763
  · exact B476767
  · exact B476771
  · exact B476775
  · exact B476779
  · exact B476783
  · exact B476787
  · exact B476791
  · exact B476795
  · exact B476799
  · exact B476803
  · exact B476807
  · exact B476811
  · exact B476815
  · exact B476819
  · exact B476823
  · exact B476827
  · exact B476831
  · exact B476835
  · exact B476839
  · exact B476843
  · exact B476847
  · exact B476851
  · exact B476855
  · exact B476859
  · exact B476863
  · exact B476867
  · exact B476871
  · exact B476875
  · exact B476879
  · exact B476883
  · exact B476887
  · exact B476891
  · exact B476895
  · exact B476899
  · exact B476903
  · exact B476907
  · exact B476911
  · exact B476915
  · exact B476919
  · exact B476923
  · exact B476927
  · exact B476931
  · exact B476935
  · exact B476939
  · exact B476943
  · exact B476947
  · exact B476951
  · exact B476955
  · exact B476959
  · exact B476963
  · exact B476967
  · exact B476971
  · exact B476975
  · exact B476979
  · exact B476983
  · exact B476987
  · exact B476991
  · exact B476995
  · exact B476999
  · exact B477003
  · exact B477007
  · exact B477011
  · exact B477015
  · exact B477019
  · exact B477023
  · exact B477027
  · exact B477031
  · exact B477035
  · exact B477039
  · exact B477043
  · exact B477047
  · exact B477051
  · exact B477055
  · exact B477059
  · exact B477063
  · exact B477067
  · exact B477071
  · exact B477075
  · exact B477079
  · exact B477083
  · exact B477087
  · exact B477091
  · exact B477095
  · exact B477099
  · exact B477103
  · exact B477107
  · exact B477111
  · exact B477115
  · exact B477119
  · exact B477123
  · exact B477127
  · exact B477131
  · exact B477135
  · exact B477139
  · exact B477143
  · exact B477147
  · exact B477151
  · exact B477155
  · exact B477159
  · exact B477163
  · exact B477167
  · exact B477171
  · exact B477175
  · exact B477179
  · exact B477183
  · exact B477187
  · exact B477191
  · exact B477195
  · exact B477199
  · exact B477203
  · exact B477207
  · exact B477211
  · exact B477215
  · exact B477219
  · exact B477223
  · exact B477227
  · exact B477231
  · exact B477235
  · exact B477239
  · exact B477243
  · exact B477247
  · exact B477251
  · exact B477255
  · exact B477259
  · exact B477263
  · exact B477267
  · exact B477271
  · exact B477275
  · exact B477279
  · exact B477283
  · exact B477287
  · exact B477291
  · exact B477295
  · exact B477299
  · exact B477303
  · exact B477307
  · exact B477311
  · exact B477315
  · exact B477319
  · exact B477323
  · exact B477327
  · exact B477331
  · exact B477335
  · exact B477339
  · exact B477343
  · exact B477347
  · exact B477351
  · exact B477355
  · exact B477359
  · exact B477363
  · exact B477367
  · exact B477371
  · exact B477375
  · exact B477379
  · exact B477383
  · exact B477387
  · exact B477391
  · exact B477395
  · exact B477399
  · exact B477403
  · exact B477407
  · exact B477411
  · exact B477415
  · exact B477419
  · exact B477423
  · exact B477427
  · exact B477431
  · exact B477435
  · exact B477439
  · exact B477443
  · exact B477447
  · exact B477451
  · exact B477455
  · exact B477459
  · exact B477463
  · exact B477467
  · exact B477471
  · exact B477475
  · exact B477479
  · exact B477483
  · exact B477487
  · exact B477491
  · exact B477495
  · exact B477499
  · exact B477503
  · exact B477507
  · exact B477511
  · exact B477515
  · exact B477519
  · exact B477523
  · exact B477527
  · exact B477531
  · exact B477535
  · exact B477539
  · exact B477543
  · exact B477547
  · exact B477551
  · exact B477555
  · exact B477559
  · exact B477563
  · exact B477567
  · exact B477571
  · exact B477575
  · exact B477579
  · exact B477583
  · exact B477587
  · exact B477591
  · exact B477595
  · exact B477599
  · exact B477603
  · exact B477607
  · exact B477611
  · exact B477615
  · exact B477619
  · exact B477623
  · exact B477627
  · exact B477631
  · exact B477635
  · exact B477639
  · exact B477643
  · exact B477647
  · exact B477651
  · exact B477655
  · exact B477659
  · exact B477663
  · exact B477667
  · exact B477671
  · exact B477675
  · exact B477679
  · exact B477683
  · exact B477687
  · exact B477691
  · exact B477695
  · exact B477699
  · exact B477703
  · exact B477707
  · exact B477711
  · exact B477715
  · exact B477719
  · exact B477723
  · exact B477727
  · exact B477731
  · exact B477735
  · exact B477739
  · exact B477743
  · exact B477747
  · exact B477751
  · exact B477755
  · exact B477759
  · exact B477763
  · exact B477767
  · exact B477771
  · exact B477775
  · exact B477779
  · exact B477783
  · exact B477787
  · exact B477791
  · exact B477795
  · exact B477799
  · exact B477803
  · exact B477807
  · exact B477811
  · exact B477815
  · exact B477819
  · exact B477823
  · exact B477827
  · exact B477831
  · exact B477835
  · exact B477839
  · exact B477843
  · exact B477847
  · exact B477851
  · exact B477855
  · exact B477859
  · exact B477863
  · exact B477867
  · exact B477871
  · exact B477875
  · exact B477879
  · exact B477883
  · exact B477887
  · exact B477891
  · exact B477895
  · exact B477899
  · exact B477903
  · exact B477907
  · exact B477911
  · exact B477915
  · exact B477919
  · exact B477923
  · exact B477927
  · exact B477931
  · exact B477935
  · exact B477939
  · exact B477943
  · exact B477947
  · exact B477951
  · exact B477955
  · exact B477959
  · exact B477963
  · exact B477967
  · exact B477971
  · exact B477975
  · exact B477979
  · exact B477983
  · exact B477987
  · exact B477991
  · exact B477995
  · exact B477999
  · exact B478003
  · exact B478007
  · exact B478011
  · exact B478015
  · exact B478019
  · exact B478023
  · exact B478027
  · exact B478031
  · exact B478035
  · exact B478039
  · exact B478043
  · exact B478047
  · exact B478051
  · exact B478055
  · exact B478059
  · exact B478063
  · exact B478067
  · exact B478071
  · exact B478075
  · exact B478079
  · exact B478083
  · exact B478087
  · exact B478091
  · exact B478095
  · exact B478099
  · exact B478103
  · exact B478107
  · exact B478111
  · exact B478115
  · exact B478119
  · exact B478123
  · exact B478127
  · exact B478131
  · exact B478135
  · exact B478139
  · exact B478143
  · exact B478147
  · exact B478151
  · exact B478155
  · exact B478159
  · exact B478163
  · exact B478167
  · exact B478171
  · exact B478175
  · exact B478179
  · exact B478183
  · exact B478187
  · exact B478191
  · exact B478195
  · exact B478199
  · exact B478203
  · exact B478207
  · exact B478211
  · exact B478215
  · exact B478219
  · exact B478223
  · exact B478227
  · exact B478231
  · exact B478235
  · exact B478239
  · exact B478243
  · exact B478247
  · exact B478251
  · exact B478255
  · exact B478259
  · exact B478263
  · exact B478267
  · exact B478271
  · exact B478275
  · exact B478279
  · exact B478283
  · exact B478287
  · exact B478291
  · exact B478295
  · exact B478299
  · exact B478303
  · exact B478307
  · exact B478311
  · exact B478315
  · exact B478319
  · exact B478323
  · exact B478327
  · exact B478331
  · exact B478335
  · exact B478339
  · exact B478343
  · exact B478347
  · exact B478351
  · exact B478355
  · exact B478359
  · exact B478363
  · exact B478367
  · exact B478371
  · exact B478375
  · exact B478379
  · exact B478383
  · exact B478387
  · exact B478391
  · exact B478395
  · exact B478399
  · exact B478403
  · exact B478407
  · exact B478411
  · exact B478415
  · exact B478419
  · exact B478423
  · exact B478427
  · exact B478431
  · exact B478435
  · exact B478439
  · exact B478443
  · exact B478447
  · exact B478451
  · exact B478455
  · exact B478459
  · exact B478463
  · exact B478467
  · exact B478471
  · exact B478475
  · exact B478479
  · exact B478483
  · exact B478487
  · exact B478491
  · exact B478495
  · exact B478499
  · exact B478503
  · exact B478507
  · exact B478511
  · exact B478515
  · exact B478519
  · exact B478523
  · exact B478527
  · exact B478531
  · exact B478535
  · exact B478539
  · exact B478543
  · exact B478547
  · exact B478551
  · exact B478555
  · exact B478559
  · exact B478563
  · exact B478567
  · exact B478571
  · exact B478575
  · exact B478579
  · exact B478583

theorem C1 (j : ℕ) (h1 : 119646 ≤ j) (h2 : j ≤ 119946) : Blo 475787 (4 * j + 3) := by
  interval_cases j
  · exact B478587
  · exact B478591
  · exact B478595
  · exact B478599
  · exact B478603
  · exact B478607
  · exact B478611
  · exact B478615
  · exact B478619
  · exact B478623
  · exact B478627
  · exact B478631
  · exact B478635
  · exact B478639
  · exact B478643
  · exact B478647
  · exact B478651
  · exact B478655
  · exact B478659
  · exact B478663
  · exact B478667
  · exact B478671
  · exact B478675
  · exact B478679
  · exact B478683
  · exact B478687
  · exact B478691
  · exact B478695
  · exact B478699
  · exact B478703
  · exact B478707
  · exact B478711
  · exact B478715
  · exact B478719
  · exact B478723
  · exact B478727
  · exact B478731
  · exact B478735
  · exact B478739
  · exact B478743
  · exact B478747
  · exact B478751
  · exact B478755
  · exact B478759
  · exact B478763
  · exact B478767
  · exact B478771
  · exact B478775
  · exact B478779
  · exact B478783
  · exact B478787
  · exact B478791
  · exact B478795
  · exact B478799
  · exact B478803
  · exact B478807
  · exact B478811
  · exact B478815
  · exact B478819
  · exact B478823
  · exact B478827
  · exact B478831
  · exact B478835
  · exact B478839
  · exact B478843
  · exact B478847
  · exact B478851
  · exact B478855
  · exact B478859
  · exact B478863
  · exact B478867
  · exact B478871
  · exact B478875
  · exact B478879
  · exact B478883
  · exact B478887
  · exact B478891
  · exact B478895
  · exact B478899
  · exact B478903
  · exact B478907
  · exact B478911
  · exact B478915
  · exact B478919
  · exact B478923
  · exact B478927
  · exact B478931
  · exact B478935
  · exact B478939
  · exact B478943
  · exact B478947
  · exact B478951
  · exact B478955
  · exact B478959
  · exact B478963
  · exact B478967
  · exact B478971
  · exact B478975
  · exact B478979
  · exact B478983
  · exact B478987
  · exact B478991
  · exact B478995
  · exact B478999
  · exact B479003
  · exact B479007
  · exact B479011
  · exact B479015
  · exact B479019
  · exact B479023
  · exact B479027
  · exact B479031
  · exact B479035
  · exact B479039
  · exact B479043
  · exact B479047
  · exact B479051
  · exact B479055
  · exact B479059
  · exact B479063
  · exact B479067
  · exact B479071
  · exact B479075
  · exact B479079
  · exact B479083
  · exact B479087
  · exact B479091
  · exact B479095
  · exact B479099
  · exact B479103
  · exact B479107
  · exact B479111
  · exact B479115
  · exact B479119
  · exact B479123
  · exact B479127
  · exact B479131
  · exact B479135
  · exact B479139
  · exact B479143
  · exact B479147
  · exact B479151
  · exact B479155
  · exact B479159
  · exact B479163
  · exact B479167
  · exact B479171
  · exact B479175
  · exact B479179
  · exact B479183
  · exact B479187
  · exact B479191
  · exact B479195
  · exact B479199
  · exact B479203
  · exact B479207
  · exact B479211
  · exact B479215
  · exact B479219
  · exact B479223
  · exact B479227
  · exact B479231
  · exact B479235
  · exact B479239
  · exact B479243
  · exact B479247
  · exact B479251
  · exact B479255
  · exact B479259
  · exact B479263
  · exact B479267
  · exact B479271
  · exact B479275
  · exact B479279
  · exact B479283
  · exact B479287
  · exact B479291
  · exact B479295
  · exact B479299
  · exact B479303
  · exact B479307
  · exact B479311
  · exact B479315
  · exact B479319
  · exact B479323
  · exact B479327
  · exact B479331
  · exact B479335
  · exact B479339
  · exact B479343
  · exact B479347
  · exact B479351
  · exact B479355
  · exact B479359
  · exact B479363
  · exact B479367
  · exact B479371
  · exact B479375
  · exact B479379
  · exact B479383
  · exact B479387
  · exact B479391
  · exact B479395
  · exact B479399
  · exact B479403
  · exact B479407
  · exact B479411
  · exact B479415
  · exact B479419
  · exact B479423
  · exact B479427
  · exact B479431
  · exact B479435
  · exact B479439
  · exact B479443
  · exact B479447
  · exact B479451
  · exact B479455
  · exact B479459
  · exact B479463
  · exact B479467
  · exact B479471
  · exact B479475
  · exact B479479
  · exact B479483
  · exact B479487
  · exact B479491
  · exact B479495
  · exact B479499
  · exact B479503
  · exact B479507
  · exact B479511
  · exact B479515
  · exact B479519
  · exact B479523
  · exact B479527
  · exact B479531
  · exact B479535
  · exact B479539
  · exact B479543
  · exact B479547
  · exact B479551
  · exact B479555
  · exact B479559
  · exact B479563
  · exact B479567
  · exact B479571
  · exact B479575
  · exact B479579
  · exact B479583
  · exact B479587
  · exact B479591
  · exact B479595
  · exact B479599
  · exact B479603
  · exact B479607
  · exact B479611
  · exact B479615
  · exact B479619
  · exact B479623
  · exact B479627
  · exact B479631
  · exact B479635
  · exact B479639
  · exact B479643
  · exact B479647
  · exact B479651
  · exact B479655
  · exact B479659
  · exact B479663
  · exact B479667
  · exact B479671
  · exact B479675
  · exact B479679
  · exact B479683
  · exact B479687
  · exact B479691
  · exact B479695
  · exact B479699
  · exact B479703
  · exact B479707
  · exact B479711
  · exact B479715
  · exact B479719
  · exact B479723
  · exact B479727
  · exact B479731
  · exact B479735
  · exact B479739
  · exact B479743
  · exact B479747
  · exact B479751
  · exact B479755
  · exact B479759
  · exact B479763
  · exact B479767
  · exact B479771
  · exact B479775
  · exact B479779
  · exact B479783
  · exact B479787

theorem solution (m : ℕ) (hlo : 475787 ≤ m) (hhi : m ≤ 479787) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 118946 ≤ j := by omega
    have hj2 : j ≤ 119946 := by omega
    have hb : Blo 475787 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 119646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
