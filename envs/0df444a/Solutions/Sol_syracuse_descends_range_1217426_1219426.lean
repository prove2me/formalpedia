-- Prove2me | solution 1 for syracuse_descends_range_1217426_1219426
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:55.122881+00:00
-- url     : https://prove2.me/submissions/6c20183e-bc38-4fa5-aad9-8865a165a613

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


theorem B2056205 : Blo 1217426 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B1826837 : Blo 1217426 1826837 := bbase (se 6 (by rfl) ⟨42816, by rfl⟩ : syracuseStep 1826837 = 85633) (by norm_num)
theorem B1826861 : Blo 1217426 1826861 := bbase (se 3 (by rfl) ⟨342536, by rfl⟩ : syracuseStep 1826861 = 685073) (by norm_num)
theorem B1826885 : Blo 1217426 1826885 := bbase (se 4 (by rfl) ⟨171270, by rfl⟩ : syracuseStep 1826885 = 342541) (by norm_num)
theorem B1826909 : Blo 1217426 1826909 := bbase (se 3 (by rfl) ⟨342545, by rfl⟩ : syracuseStep 1826909 = 685091) (by norm_num)
theorem B1826933 : Blo 1217426 1826933 := bbase (se 5 (by rfl) ⟨85637, by rfl⟩ : syracuseStep 1826933 = 171275) (by norm_num)
theorem B5202053 : Blo 1217426 5202053 := bbase (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) (by norm_num)
theorem B1826957 : Blo 1217426 1826957 := bbase (se 3 (by rfl) ⟨342554, by rfl⟩ : syracuseStep 1826957 = 685109) (by norm_num)
theorem B2056333 : Blo 1217426 2056333 := bbase (se 3 (by rfl) ⟨385562, by rfl⟩ : syracuseStep 2056333 = 771125) (by norm_num)
theorem B8896661 : Blo 1217426 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B1646741 : Blo 1217426 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B1826981 : Blo 1217426 1826981 := bbase (se 4 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 1826981 = 342559) (by norm_num)
theorem B1827005 : Blo 1217426 1827005 := bbase (se 3 (by rfl) ⟨342563, by rfl⟩ : syracuseStep 1827005 = 685127) (by norm_num)
theorem B1827029 : Blo 1217426 1827029 := bbase (se 7 (by rfl) ⟨21410, by rfl⟩ : syracuseStep 1827029 = 42821) (by norm_num)
theorem B2056421 : Blo 1217426 2056421 := bbase (se 4 (by rfl) ⟨192789, by rfl⟩ : syracuseStep 2056421 = 385579) (by norm_num)
theorem B1827053 : Blo 1217426 1827053 := bbase (se 3 (by rfl) ⟨342572, by rfl⟩ : syracuseStep 1827053 = 685145) (by norm_num)
theorem B1827077 : Blo 1217426 1827077 := bbase (se 4 (by rfl) ⟨171288, by rfl⟩ : syracuseStep 1827077 = 342577) (by norm_num)
theorem B1827101 : Blo 1217426 1827101 := bbase (se 3 (by rfl) ⟨342581, by rfl⟩ : syracuseStep 1827101 = 685163) (by norm_num)
theorem B1827125 : Blo 1217426 1827125 := bbase (se 5 (by rfl) ⟨85646, by rfl⟩ : syracuseStep 1827125 = 171293) (by norm_num)
theorem B4112693 : Blo 1217426 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B1827149 : Blo 1217426 1827149 := bbase (se 3 (by rfl) ⟨342590, by rfl⟩ : syracuseStep 1827149 = 685181) (by norm_num)
theorem B1827173 : Blo 1217426 1827173 := bbase (se 4 (by rfl) ⟨171297, by rfl⟩ : syracuseStep 1827173 = 342595) (by norm_num)
theorem B2056549 : Blo 1217426 2056549 := bbase (se 4 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 2056549 = 385603) (by norm_num)
theorem B2343277 : Blo 1217426 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1827197 : Blo 1217426 1827197 := bbase (se 3 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 1827197 = 685199) (by norm_num)
theorem B1827221 : Blo 1217426 1827221 := bbase (se 6 (by rfl) ⟨42825, by rfl⟩ : syracuseStep 1827221 = 85651) (by norm_num)
theorem B1827245 : Blo 1217426 1827245 := bbase (se 3 (by rfl) ⟨342608, by rfl⟩ : syracuseStep 1827245 = 685217) (by norm_num)
theorem B2056637 : Blo 1217426 2056637 := bbase (se 3 (by rfl) ⟨385619, by rfl⟩ : syracuseStep 2056637 = 771239) (by norm_num)
theorem B1827269 : Blo 1217426 1827269 := bbase (se 4 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 1827269 = 342613) (by norm_num)
theorem B1827293 : Blo 1217426 1827293 := bbase (se 3 (by rfl) ⟨342617, by rfl⟩ : syracuseStep 1827293 = 685235) (by norm_num)
theorem B1827317 : Blo 1217426 1827317 := bbase (se 5 (by rfl) ⟨85655, by rfl⟩ : syracuseStep 1827317 = 171311) (by norm_num)
theorem B1827341 : Blo 1217426 1827341 := bbase (se 3 (by rfl) ⟨342626, by rfl⟩ : syracuseStep 1827341 = 685253) (by norm_num)
theorem B1827365 : Blo 1217426 1827365 := bbase (se 4 (by rfl) ⟨171315, by rfl⟩ : syracuseStep 1827365 = 342631) (by norm_num)
theorem B1827389 : Blo 1217426 1827389 := bbase (se 3 (by rfl) ⟨342635, by rfl⟩ : syracuseStep 1827389 = 685271) (by norm_num)
theorem B2056765 : Blo 1217426 2056765 := bbase (se 3 (by rfl) ⟨385643, by rfl⟩ : syracuseStep 2056765 = 771287) (by norm_num)
theorem B1827413 : Blo 1217426 1827413 := bbase (se 8 (by rfl) ⟨10707, by rfl⟩ : syracuseStep 1827413 = 21415) (by norm_num)
theorem B1827437 : Blo 1217426 1827437 := bbase (se 3 (by rfl) ⟨342644, by rfl⟩ : syracuseStep 1827437 = 685289) (by norm_num)
theorem B1827461 : Blo 1217426 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B11870869 : Blo 1217426 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B2056853 : Blo 1217426 2056853 := bbase (se 6 (by rfl) ⟨48207, by rfl⟩ : syracuseStep 2056853 = 96415) (by norm_num)
theorem B1827485 : Blo 1217426 1827485 := bbase (se 3 (by rfl) ⟨342653, by rfl⟩ : syracuseStep 1827485 = 685307) (by norm_num)
theorem B1827509 : Blo 1217426 1827509 := bbase (se 5 (by rfl) ⟨85664, by rfl⟩ : syracuseStep 1827509 = 171329) (by norm_num)
theorem B1827533 : Blo 1217426 1827533 := bbase (se 3 (by rfl) ⟨342662, by rfl⟩ : syracuseStep 1827533 = 685325) (by norm_num)
theorem B1950437 : Blo 1217426 1950437 := bbase (se 4 (by rfl) ⟨182853, by rfl⟩ : syracuseStep 1950437 = 365707) (by norm_num)
theorem B1827557 : Blo 1217426 1827557 := bbase (se 4 (by rfl) ⟨171333, by rfl⟩ : syracuseStep 1827557 = 342667) (by norm_num)
theorem B4113125 : Blo 1217426 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B1827581 : Blo 1217426 1827581 := bbase (se 3 (by rfl) ⟨342671, by rfl⟩ : syracuseStep 1827581 = 685343) (by norm_num)
theorem B1540873 : Blo 1217426 1540873 := bbase (se 2 (by rfl) ⟨577827, by rfl⟩ : syracuseStep 1540873 = 1155655) (by norm_num)
theorem B1827605 : Blo 1217426 1827605 := bbase (se 6 (by rfl) ⟨42834, by rfl⟩ : syracuseStep 1827605 = 85669) (by norm_num)
theorem B2056981 : Blo 1217426 2056981 := bbase (se 6 (by rfl) ⟨48210, by rfl⟩ : syracuseStep 2056981 = 96421) (by norm_num)
theorem B1827629 : Blo 1217426 1827629 := bbase (se 3 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 1827629 = 685361) (by norm_num)
theorem B1827653 : Blo 1217426 1827653 := bbase (se 4 (by rfl) ⟨171342, by rfl⟩ : syracuseStep 1827653 = 342685) (by norm_num)
theorem B9257813 : Blo 1217426 9257813 := bbase (se 9 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 9257813 = 54245) (by norm_num)
theorem B1827677 : Blo 1217426 1827677 := bbase (se 3 (by rfl) ⟨342689, by rfl⟩ : syracuseStep 1827677 = 685379) (by norm_num)
theorem B1950565 : Blo 1217426 1950565 := bbase (se 4 (by rfl) ⟨182865, by rfl⟩ : syracuseStep 1950565 = 365731) (by norm_num)
theorem B6169445 : Blo 1217426 6169445 := bbase (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) (by norm_num)
theorem B2057069 : Blo 1217426 2057069 := bbase (se 3 (by rfl) ⟨385700, by rfl⟩ : syracuseStep 2057069 = 771401) (by norm_num)
theorem B5202805 : Blo 1217426 5202805 := bbase (se 5 (by rfl) ⟨243881, by rfl⟩ : syracuseStep 5202805 = 487763) (by norm_num)
theorem B4752245 : Blo 1217426 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B1827701 : Blo 1217426 1827701 := bbase (se 5 (by rfl) ⟨85673, by rfl⟩ : syracuseStep 1827701 = 171347) (by norm_num)
theorem B1827725 : Blo 1217426 1827725 := bbase (se 3 (by rfl) ⟨342698, by rfl⟩ : syracuseStep 1827725 = 685397) (by norm_num)
theorem B1319825 : Blo 1217426 1319825 := bbase (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) (by norm_num)
theorem B1827749 : Blo 1217426 1827749 := bbase (se 4 (by rfl) ⟨171351, by rfl⟩ : syracuseStep 1827749 = 342703) (by norm_num)
theorem B1541045 : Blo 1217426 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B1827773 : Blo 1217426 1827773 := bbase (se 3 (by rfl) ⟨342707, by rfl⟩ : syracuseStep 1827773 = 685415) (by norm_num)
theorem B4940741 : Blo 1217426 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B1827797 : Blo 1217426 1827797 := bbase (se 7 (by rfl) ⟨21419, by rfl⟩ : syracuseStep 1827797 = 42839) (by norm_num)
theorem B1541101 : Blo 1217426 1541101 := bbase (se 3 (by rfl) ⟨288956, by rfl⟩ : syracuseStep 1541101 = 577913) (by norm_num)
theorem B1827821 : Blo 1217426 1827821 := bbase (se 3 (by rfl) ⟨342716, by rfl⟩ : syracuseStep 1827821 = 685433) (by norm_num)
theorem B2057197 : Blo 1217426 2057197 := bbase (se 3 (by rfl) ⟨385724, by rfl⟩ : syracuseStep 2057197 = 771449) (by norm_num)
theorem B4449269 : Blo 1217426 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B1827845 : Blo 1217426 1827845 := bbase (se 4 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 1827845 = 342721) (by norm_num)
theorem B1827869 : Blo 1217426 1827869 := bbase (se 3 (by rfl) ⟨342725, by rfl⟩ : syracuseStep 1827869 = 685451) (by norm_num)
theorem B1827893 : Blo 1217426 1827893 := bbase (se 5 (by rfl) ⟨85682, by rfl⟩ : syracuseStep 1827893 = 171365) (by norm_num)
theorem B2057285 : Blo 1217426 2057285 := bbase (se 4 (by rfl) ⟨192870, by rfl⟩ : syracuseStep 2057285 = 385741) (by norm_num)
theorem B1541197 : Blo 1217426 1541197 := bbase (se 3 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 1541197 = 577949) (by norm_num)
theorem B1827917 : Blo 1217426 1827917 := bbase (se 3 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 1827917 = 685469) (by norm_num)
theorem B1827941 : Blo 1217426 1827941 := bbase (se 4 (by rfl) ⟨171369, by rfl⟩ : syracuseStep 1827941 = 342739) (by norm_num)
theorem B1827965 : Blo 1217426 1827965 := bbase (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) (by norm_num)
theorem B1827989 : Blo 1217426 1827989 := bbase (se 6 (by rfl) ⟨42843, by rfl⟩ : syracuseStep 1827989 = 85687) (by norm_num)
theorem B4113557 : Blo 1217426 4113557 := bbase (se 6 (by rfl) ⟨96411, by rfl⟩ : syracuseStep 4113557 = 192823) (by norm_num)
theorem B2196629 : Blo 1217426 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2311325 : Blo 1217426 2311325 := bbase (se 3 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 2311325 = 866747) (by norm_num)
theorem B1828013 : Blo 1217426 1828013 := bbase (se 3 (by rfl) ⟨342752, by rfl⟩ : syracuseStep 1828013 = 685505) (by norm_num)
theorem B1483957 : Blo 1217426 1483957 := bbase (se 5 (by rfl) ⟨69560, by rfl⟩ : syracuseStep 1483957 = 139121) (by norm_num)
theorem B1828037 : Blo 1217426 1828037 := bbase (se 4 (by rfl) ⟨171378, by rfl⟩ : syracuseStep 1828037 = 342757) (by norm_num)
theorem B2057413 : Blo 1217426 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B15623381 : Blo 1217426 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B1828061 : Blo 1217426 1828061 := bbase (se 3 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 1828061 = 685523) (by norm_num)
theorem B9250037 : Blo 1217426 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B1828085 : Blo 1217426 1828085 := bbase (se 5 (by rfl) ⟨85691, by rfl⟩ : syracuseStep 1828085 = 171383) (by norm_num)
theorem B1541369 : Blo 1217426 1541369 := bbase (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) (by norm_num)
theorem B1828109 : Blo 1217426 1828109 := bbase (se 3 (by rfl) ⟨342770, by rfl⟩ : syracuseStep 1828109 = 685541) (by norm_num)
theorem B2057501 : Blo 1217426 2057501 := bbase (se 3 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 2057501 = 771563) (by norm_num)
theorem B1828133 : Blo 1217426 1828133 := bbase (se 4 (by rfl) ⟨171387, by rfl⟩ : syracuseStep 1828133 = 342775) (by norm_num)
theorem B1541425 : Blo 1217426 1541425 := bbase (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) (by norm_num)
theorem B7808309 : Blo 1217426 7808309 := bbase (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) (by norm_num)
theorem B5276981 : Blo 1217426 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1828157 : Blo 1217426 1828157 := bbase (se 3 (by rfl) ⟨342779, by rfl⟩ : syracuseStep 1828157 = 685559) (by norm_num)
theorem B6939989 : Blo 1217426 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B1828181 : Blo 1217426 1828181 := bbase (se 12 (by rfl) ⟨669, by rfl⟩ : syracuseStep 1828181 = 1339) (by norm_num)
theorem B1828205 : Blo 1217426 1828205 := bbase (se 3 (by rfl) ⟨342788, by rfl⟩ : syracuseStep 1828205 = 685577) (by norm_num)
theorem B1828229 : Blo 1217426 1828229 := bbase (se 4 (by rfl) ⟨171396, by rfl⟩ : syracuseStep 1828229 = 342793) (by norm_num)
theorem B5858693 : Blo 1217426 5858693 := bbase (se 4 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 5858693 = 1098505) (by norm_num)
theorem B1541521 : Blo 1217426 1541521 := bbase (se 2 (by rfl) ⟨578070, by rfl⟩ : syracuseStep 1541521 = 1156141) (by norm_num)
theorem B1828253 : Blo 1217426 1828253 := bbase (se 3 (by rfl) ⟨342797, by rfl⟩ : syracuseStep 1828253 = 685595) (by norm_num)
theorem B2057629 : Blo 1217426 2057629 := bbase (se 3 (by rfl) ⟨385805, by rfl⟩ : syracuseStep 2057629 = 771611) (by norm_num)
theorem B1828277 : Blo 1217426 1828277 := bbase (se 5 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 1828277 = 171401) (by norm_num)
theorem B1852877 : Blo 1217426 1852877 := bbase (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) (by norm_num)
theorem B1828301 : Blo 1217426 1828301 := bbase (se 3 (by rfl) ⟨342806, by rfl⟩ : syracuseStep 1828301 = 685613) (by norm_num)
theorem B3081685 : Blo 1217426 3081685 := bbase (se 7 (by rfl) ⟨36113, by rfl⟩ : syracuseStep 3081685 = 72227) (by norm_num)
theorem B1828325 : Blo 1217426 1828325 := bbase (se 4 (by rfl) ⟨171405, by rfl⟩ : syracuseStep 1828325 = 342811) (by norm_num)
theorem B2057717 : Blo 1217426 2057717 := bbase (se 5 (by rfl) ⟨96455, by rfl⟩ : syracuseStep 2057717 = 192911) (by norm_num)
theorem B1828349 : Blo 1217426 1828349 := bbase (se 3 (by rfl) ⟨342815, by rfl⟩ : syracuseStep 1828349 = 685631) (by norm_num)
theorem B1828373 : Blo 1217426 1828373 := bbase (se 6 (by rfl) ⟨42852, by rfl⟩ : syracuseStep 1828373 = 85705) (by norm_num)
theorem B1369633 : Blo 1217426 1369633 := bbase (se 2 (by rfl) ⟨513612, by rfl⟩ : syracuseStep 1369633 = 1027225) (by norm_num)
theorem B1828397 : Blo 1217426 1828397 := bbase (se 3 (by rfl) ⟨342824, by rfl⟩ : syracuseStep 1828397 = 685649) (by norm_num)
theorem B1541693 : Blo 1217426 1541693 := bbase (se 3 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 1541693 = 578135) (by norm_num)
theorem B1369669 : Blo 1217426 1369669 := bbase (se 4 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 1369669 = 256813) (by norm_num)
theorem B3081797 : Blo 1217426 3081797 := bbase (se 4 (by rfl) ⟨288918, by rfl⟩ : syracuseStep 3081797 = 577837) (by norm_num)
theorem B1828421 : Blo 1217426 1828421 := bbase (se 4 (by rfl) ⟨171414, by rfl⟩ : syracuseStep 1828421 = 342829) (by norm_num)
theorem B4113989 : Blo 1217426 4113989 := bbase (se 4 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 4113989 = 771373) (by norm_num)
theorem B5203541 : Blo 1217426 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B1828445 : Blo 1217426 1828445 := bbase (se 3 (by rfl) ⟨342833, by rfl⟩ : syracuseStep 1828445 = 685667) (by norm_num)
theorem B1369705 : Blo 1217426 1369705 := bbase (se 2 (by rfl) ⟨513639, by rfl⟩ : syracuseStep 1369705 = 1027279) (by norm_num)
theorem B1541749 : Blo 1217426 1541749 := bbase (se 5 (by rfl) ⟨72269, by rfl⟩ : syracuseStep 1541749 = 144539) (by norm_num)
theorem B1828469 : Blo 1217426 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B1369741 : Blo 1217426 1369741 := bbase (se 3 (by rfl) ⟨256826, by rfl⟩ : syracuseStep 1369741 = 513653) (by norm_num)
theorem B1828493 : Blo 1217426 1828493 := bbase (se 3 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 1828493 = 685685) (by norm_num)
theorem B1828517 : Blo 1217426 1828517 := bbase (se 4 (by rfl) ⟨171423, by rfl⟩ : syracuseStep 1828517 = 342847) (by norm_num)
theorem B1369777 : Blo 1217426 1369777 := bbase (se 2 (by rfl) ⟨513666, by rfl⟩ : syracuseStep 1369777 = 1027333) (by norm_num)
theorem B1828541 : Blo 1217426 1828541 := bbase (se 3 (by rfl) ⟨342851, by rfl⟩ : syracuseStep 1828541 = 685703) (by norm_num)
theorem B1369813 : Blo 1217426 1369813 := bbase (se 7 (by rfl) ⟨16052, by rfl⟩ : syracuseStep 1369813 = 32105) (by norm_num)
theorem B1541845 : Blo 1217426 1541845 := bbase (se 7 (by rfl) ⟨18068, by rfl⟩ : syracuseStep 1541845 = 36137) (by norm_num)
theorem B1828565 : Blo 1217426 1828565 := bbase (se 7 (by rfl) ⟨21428, by rfl⟩ : syracuseStep 1828565 = 42857) (by norm_num)
theorem B2926309 : Blo 1217426 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B1828589 : Blo 1217426 1828589 := bbase (se 3 (by rfl) ⟨342860, by rfl⟩ : syracuseStep 1828589 = 685721) (by norm_num)
theorem B1369849 : Blo 1217426 1369849 := bbase (se 2 (by rfl) ⟨513693, by rfl⟩ : syracuseStep 1369849 = 1027387) (by norm_num)
theorem B3081989 : Blo 1217426 3081989 := bbase (se 4 (by rfl) ⟨288936, by rfl⟩ : syracuseStep 3081989 = 577873) (by norm_num)
theorem B1828613 : Blo 1217426 1828613 := bbase (se 4 (by rfl) ⟨171432, by rfl⟩ : syracuseStep 1828613 = 342865) (by norm_num)
theorem B1369885 : Blo 1217426 1369885 := bbase (se 3 (by rfl) ⟨256853, by rfl⟩ : syracuseStep 1369885 = 513707) (by norm_num)
theorem B1828637 : Blo 1217426 1828637 := bbase (se 3 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 1828637 = 685739) (by norm_num)
theorem B1828661 : Blo 1217426 1828661 := bbase (se 5 (by rfl) ⟨85718, by rfl⟩ : syracuseStep 1828661 = 171437) (by norm_num)
theorem B1369921 : Blo 1217426 1369921 := bbase (se 2 (by rfl) ⟨513720, by rfl⟩ : syracuseStep 1369921 = 1027441) (by norm_num)
theorem B1828685 : Blo 1217426 1828685 := bbase (se 3 (by rfl) ⟨342878, by rfl⟩ : syracuseStep 1828685 = 685757) (by norm_num)
theorem B1369957 : Blo 1217426 1369957 := bbase (se 4 (by rfl) ⟨128433, by rfl⟩ : syracuseStep 1369957 = 256867) (by norm_num)
theorem B1828709 : Blo 1217426 1828709 := bbase (se 4 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 1828709 = 342883) (by norm_num)
theorem B1828733 : Blo 1217426 1828733 := bbase (se 3 (by rfl) ⟨342887, by rfl⟩ : syracuseStep 1828733 = 685775) (by norm_num)
theorem B1542017 : Blo 1217426 1542017 := bbase (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) (by norm_num)
theorem B1369993 : Blo 1217426 1369993 := bbase (se 2 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 1369993 = 1027495) (by norm_num)
theorem B2312077 : Blo 1217426 2312077 := bbase (se 3 (by rfl) ⟨433514, by rfl⟩ : syracuseStep 2312077 = 867029) (by norm_num)
theorem B1828757 : Blo 1217426 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B1370029 : Blo 1217426 1370029 := bbase (se 3 (by rfl) ⟨256880, by rfl⟩ : syracuseStep 1370029 = 513761) (by norm_num)
theorem B1828781 : Blo 1217426 1828781 := bbase (se 3 (by rfl) ⟨342896, by rfl⟩ : syracuseStep 1828781 = 685793) (by norm_num)
theorem B1542073 : Blo 1217426 1542073 := bbase (se 2 (by rfl) ⟨578277, by rfl⟩ : syracuseStep 1542073 = 1156555) (by norm_num)
theorem B1828805 : Blo 1217426 1828805 := bbase (se 4 (by rfl) ⟨171450, by rfl⟩ : syracuseStep 1828805 = 342901) (by norm_num)
theorem B1370065 : Blo 1217426 1370065 := bbase (se 2 (by rfl) ⟨513774, by rfl⟩ : syracuseStep 1370065 = 1027549) (by norm_num)
theorem B1828829 : Blo 1217426 1828829 := bbase (se 3 (by rfl) ⟨342905, by rfl⟩ : syracuseStep 1828829 = 685811) (by norm_num)
theorem B1370101 : Blo 1217426 1370101 := bbase (se 5 (by rfl) ⟨64223, by rfl⟩ : syracuseStep 1370101 = 128447) (by norm_num)
theorem B4114421 : Blo 1217426 4114421 := bbase (se 5 (by rfl) ⟨192863, by rfl⟩ : syracuseStep 4114421 = 385727) (by norm_num)
theorem B1828853 : Blo 1217426 1828853 := bbase (se 5 (by rfl) ⟨85727, by rfl⟩ : syracuseStep 1828853 = 171455) (by norm_num)
theorem B1828877 : Blo 1217426 1828877 := bbase (se 3 (by rfl) ⟨342914, by rfl⟩ : syracuseStep 1828877 = 685829) (by norm_num)
theorem B1370137 : Blo 1217426 1370137 := bbase (se 2 (by rfl) ⟨513801, by rfl⟩ : syracuseStep 1370137 = 1027603) (by norm_num)
theorem B1542169 : Blo 1217426 1542169 := bbase (se 2 (by rfl) ⟨578313, by rfl⟩ : syracuseStep 1542169 = 1156627) (by norm_num)
theorem B2312221 : Blo 1217426 2312221 := bbase (se 3 (by rfl) ⟨433541, by rfl⟩ : syracuseStep 2312221 = 867083) (by norm_num)
theorem B1828901 : Blo 1217426 1828901 := bbase (se 4 (by rfl) ⟨171459, by rfl⟩ : syracuseStep 1828901 = 342919) (by norm_num)
theorem B1370173 : Blo 1217426 1370173 := bbase (se 3 (by rfl) ⟨256907, by rfl⟩ : syracuseStep 1370173 = 513815) (by norm_num)
theorem B1828925 : Blo 1217426 1828925 := bbase (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) (by norm_num)
theorem B53413973 : Blo 1217426 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B1828949 : Blo 1217426 1828949 := bbase (se 8 (by rfl) ⟨10716, by rfl⟩ : syracuseStep 1828949 = 21433) (by norm_num)
theorem B3082333 : Blo 1217426 3082333 := bbase (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) (by norm_num)
theorem B2926685 : Blo 1217426 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B1853533 : Blo 1217426 1853533 := bbase (se 3 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 1853533 = 695075) (by norm_num)
theorem B1370209 : Blo 1217426 1370209 := bbase (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) (by norm_num)
theorem B1828973 : Blo 1217426 1828973 := bbase (se 3 (by rfl) ⟨342932, by rfl⟩ : syracuseStep 1828973 = 685865) (by norm_num)
theorem B4622453 : Blo 1217426 4622453 := bbase (se 5 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 4622453 = 433355) (by norm_num)
theorem B6170741 : Blo 1217426 6170741 := bbase (se 5 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 6170741 = 578507) (by norm_num)
theorem B1370245 : Blo 1217426 1370245 := bbase (se 4 (by rfl) ⟨128460, by rfl⟩ : syracuseStep 1370245 = 256921) (by norm_num)
theorem B1828997 : Blo 1217426 1828997 := bbase (se 4 (by rfl) ⟨171468, by rfl⟩ : syracuseStep 1828997 = 342937) (by norm_num)
theorem B1829021 : Blo 1217426 1829021 := bbase (se 3 (by rfl) ⟨342941, by rfl⟩ : syracuseStep 1829021 = 685883) (by norm_num)
theorem B2345125 : Blo 1217426 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B1370281 : Blo 1217426 1370281 := bbase (se 2 (by rfl) ⟨513855, by rfl⟩ : syracuseStep 1370281 = 1027711) (by norm_num)
theorem B1829045 : Blo 1217426 1829045 := bbase (se 5 (by rfl) ⟨85736, by rfl⟩ : syracuseStep 1829045 = 171473) (by norm_num)
theorem B2312381 : Blo 1217426 2312381 := bbase (se 3 (by rfl) ⟨433571, by rfl⟩ : syracuseStep 2312381 = 867143) (by norm_num)
theorem B1542341 : Blo 1217426 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B3082445 : Blo 1217426 3082445 := bbase (se 3 (by rfl) ⟨577958, by rfl⟩ : syracuseStep 3082445 = 1155917) (by norm_num)
theorem B1370317 : Blo 1217426 1370317 := bbase (se 3 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 1370317 = 513869) (by norm_num)
theorem B1951949 : Blo 1217426 1951949 := bbase (se 3 (by rfl) ⟨365990, by rfl⟩ : syracuseStep 1951949 = 731981) (by norm_num)
theorem B1829069 : Blo 1217426 1829069 := bbase (se 3 (by rfl) ⟨342950, by rfl⟩ : syracuseStep 1829069 = 685901) (by norm_num)
theorem B1583317 : Blo 1217426 1583317 := bbase (se 7 (by rfl) ⟨18554, by rfl⟩ : syracuseStep 1583317 = 37109) (by norm_num)
theorem B26699989 : Blo 1217426 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B1829093 : Blo 1217426 1829093 := bbase (se 4 (by rfl) ⟨171477, by rfl⟩ : syracuseStep 1829093 = 342955) (by norm_num)
theorem B1370353 : Blo 1217426 1370353 := bbase (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) (by norm_num)
theorem B1542397 : Blo 1217426 1542397 := bbase (se 3 (by rfl) ⟨289199, by rfl⟩ : syracuseStep 1542397 = 578399) (by norm_num)
theorem B1829117 : Blo 1217426 1829117 := bbase (se 3 (by rfl) ⟨342959, by rfl⟩ : syracuseStep 1829117 = 685919) (by norm_num)
theorem B1370389 : Blo 1217426 1370389 := bbase (se 6 (by rfl) ⟨32118, by rfl⟩ : syracuseStep 1370389 = 64237) (by norm_num)
theorem B1370425 : Blo 1217426 1370425 := bbase (se 2 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 1370425 = 1027819) (by norm_num)
theorem B2468165 : Blo 1217426 2468165 := bbase (se 4 (by rfl) ⟨231390, by rfl⟩ : syracuseStep 2468165 = 462781) (by norm_num)
theorem B2312525 : Blo 1217426 2312525 := bbase (se 3 (by rfl) ⟨433598, by rfl⟩ : syracuseStep 2312525 = 867197) (by norm_num)
theorem B1370461 : Blo 1217426 1370461 := bbase (se 3 (by rfl) ⟨256961, by rfl⟩ : syracuseStep 1370461 = 513923) (by norm_num)
theorem B1542493 : Blo 1217426 1542493 := bbase (se 3 (by rfl) ⟨289217, by rfl⟩ : syracuseStep 1542493 = 578435) (by norm_num)
theorem B1853813 : Blo 1217426 1853813 := bbase (se 5 (by rfl) ⟨86897, by rfl⟩ : syracuseStep 1853813 = 173795) (by norm_num)
theorem B1370497 : Blo 1217426 1370497 := bbase (se 2 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 1370497 = 1027873) (by norm_num)
theorem B3082637 : Blo 1217426 3082637 := bbase (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) (by norm_num)
theorem B4622741 : Blo 1217426 4622741 := bbase (se 6 (by rfl) ⟨108345, by rfl⟩ : syracuseStep 4622741 = 216691) (by norm_num)
theorem B5851541 : Blo 1217426 5851541 := bbase (se 6 (by rfl) ⟨137145, by rfl⟩ : syracuseStep 5851541 = 274291) (by norm_num)
theorem B1370533 : Blo 1217426 1370533 := bbase (se 4 (by rfl) ⟨128487, by rfl⟩ : syracuseStep 1370533 = 256975) (by norm_num)
theorem B4114853 : Blo 1217426 4114853 := bbase (se 4 (by rfl) ⟨385767, by rfl⟩ : syracuseStep 4114853 = 771535) (by norm_num)
theorem B3467717 : Blo 1217426 3467717 := bbase (se 4 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 3467717 = 650197) (by norm_num)
theorem B1370569 : Blo 1217426 1370569 := bbase (se 2 (by rfl) ⟨513963, by rfl⟩ : syracuseStep 1370569 = 1027927) (by norm_num)
theorem B1370605 : Blo 1217426 1370605 := bbase (se 3 (by rfl) ⟨256988, by rfl⟩ : syracuseStep 1370605 = 513977) (by norm_num)
theorem B6941173 : Blo 1217426 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1542665 : Blo 1217426 1542665 := bbase (se 2 (by rfl) ⟨578499, by rfl⟩ : syracuseStep 1542665 = 1156999) (by norm_num)
theorem B2927117 : Blo 1217426 2927117 := bbase (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) (by norm_num)
theorem B1370641 : Blo 1217426 1370641 := bbase (se 2 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 1370641 = 1027981) (by norm_num)
theorem B1370677 : Blo 1217426 1370677 := bbase (se 5 (by rfl) ⟨64250, by rfl⟩ : syracuseStep 1370677 = 128501) (by norm_num)
theorem B1542721 : Blo 1217426 1542721 := bbase (se 2 (by rfl) ⟨578520, by rfl⟩ : syracuseStep 1542721 = 1157041) (by norm_num)
theorem B1370713 : Blo 1217426 1370713 := bbase (se 2 (by rfl) ⟨514017, by rfl⟩ : syracuseStep 1370713 = 1028035) (by norm_num)
theorem B3902053 : Blo 1217426 3902053 := bbase (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) (by norm_num)
theorem B2312813 : Blo 1217426 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B1370749 : Blo 1217426 1370749 := bbase (se 3 (by rfl) ⟨257015, by rfl⟩ : syracuseStep 1370749 = 514031) (by norm_num)
theorem B1370785 : Blo 1217426 1370785 := bbase (se 2 (by rfl) ⟨514044, by rfl⟩ : syracuseStep 1370785 = 1028089) (by norm_num)
theorem B1542817 : Blo 1217426 1542817 := bbase (se 2 (by rfl) ⟨578556, by rfl⟩ : syracuseStep 1542817 = 1157113) (by norm_num)
theorem B1370821 : Blo 1217426 1370821 := bbase (se 4 (by rfl) ⟨128514, by rfl⟩ : syracuseStep 1370821 = 257029) (by norm_num)
theorem B3082981 : Blo 1217426 3082981 := bbase (se 4 (by rfl) ⟨289029, by rfl⟩ : syracuseStep 3082981 = 578059) (by norm_num)
theorem B1370857 : Blo 1217426 1370857 := bbase (se 2 (by rfl) ⟨514071, by rfl⟩ : syracuseStep 1370857 = 1028143) (by norm_num)
theorem B2312965 : Blo 1217426 2312965 := bbase (se 4 (by rfl) ⟨216840, by rfl⟩ : syracuseStep 2312965 = 433681) (by norm_num)
theorem B1370893 : Blo 1217426 1370893 := bbase (se 3 (by rfl) ⟨257042, by rfl⟩ : syracuseStep 1370893 = 514085) (by norm_num)
theorem B1370929 : Blo 1217426 1370929 := bbase (se 2 (by rfl) ⟨514098, by rfl⟩ : syracuseStep 1370929 = 1028197) (by norm_num)
theorem B1542989 : Blo 1217426 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B3083093 : Blo 1217426 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B1370965 : Blo 1217426 1370965 := bbase (se 9 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 1370965 = 8033) (by norm_num)
theorem B4115285 : Blo 1217426 4115285 := bbase (se 9 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 4115285 = 24113) (by norm_num)
theorem B1371001 : Blo 1217426 1371001 := bbase (se 2 (by rfl) ⟨514125, by rfl⟩ : syracuseStep 1371001 = 1028251) (by norm_num)
theorem B1543045 : Blo 1217426 1543045 := bbase (se 4 (by rfl) ⟨144660, by rfl⟩ : syracuseStep 1543045 = 289321) (by norm_num)
theorem B1371037 : Blo 1217426 1371037 := bbase (se 3 (by rfl) ⟨257069, by rfl⟩ : syracuseStep 1371037 = 514139) (by norm_num)
theorem B1371073 : Blo 1217426 1371073 := bbase (se 2 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 1371073 = 1028305) (by norm_num)
theorem B1371109 : Blo 1217426 1371109 := bbase (se 4 (by rfl) ⟨128541, by rfl⟩ : syracuseStep 1371109 = 257083) (by norm_num)
theorem B1543141 : Blo 1217426 1543141 := bbase (se 4 (by rfl) ⟨144669, by rfl⟩ : syracuseStep 1543141 = 289339) (by norm_num)
theorem B11111413 : Blo 1217426 11111413 := bbase (se 5 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 11111413 = 1041695) (by norm_num)
theorem B1371145 : Blo 1217426 1371145 := bbase (se 2 (by rfl) ⟨514179, by rfl⟩ : syracuseStep 1371145 = 1028359) (by norm_num)
theorem B2739221 : Blo 1217426 2739221 := bbase (se 6 (by rfl) ⟨64200, by rfl⟩ : syracuseStep 2739221 = 128401) (by norm_num)
theorem B3083285 : Blo 1217426 3083285 := bbase (se 6 (by rfl) ⟨72264, by rfl⟩ : syracuseStep 3083285 = 144529) (by norm_num)
theorem B1371181 : Blo 1217426 1371181 := bbase (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) (by norm_num)
theorem B2313269 : Blo 1217426 2313269 := bbase (se 5 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 2313269 = 216869) (by norm_num)
theorem B2927693 : Blo 1217426 2927693 := bbase (se 3 (by rfl) ⟨548942, by rfl⟩ : syracuseStep 2927693 = 1097885) (by norm_num)
theorem B1371217 : Blo 1217426 1371217 := bbase (se 2 (by rfl) ⟨514206, by rfl⟩ : syracuseStep 1371217 = 1028413) (by norm_num)
theorem B3386453 : Blo 1217426 3386453 := bbase (se 8 (by rfl) ⟨19842, by rfl⟩ : syracuseStep 3386453 = 39685) (by norm_num)
theorem B2739293 : Blo 1217426 2739293 := bbase (se 3 (by rfl) ⟨513617, by rfl⟩ : syracuseStep 2739293 = 1027235) (by norm_num)
theorem B1371253 : Blo 1217426 1371253 := bbase (se 5 (by rfl) ⟨64277, by rfl⟩ : syracuseStep 1371253 = 128555) (by norm_num)
theorem B1952885 : Blo 1217426 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B1543313 : Blo 1217426 1543313 := bbase (se 2 (by rfl) ⟨578742, by rfl⟩ : syracuseStep 1543313 = 1157485) (by norm_num)
theorem B1371289 : Blo 1217426 1371289 := bbase (se 2 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 1371289 = 1028467) (by norm_num)
theorem B2739365 : Blo 1217426 2739365 := bbase (se 4 (by rfl) ⟨256815, by rfl⟩ : syracuseStep 2739365 = 513631) (by norm_num)
theorem B1371325 : Blo 1217426 1371325 := bbase (se 3 (by rfl) ⟨257123, by rfl⟩ : syracuseStep 1371325 = 514247) (by norm_num)
theorem B3706069 : Blo 1217426 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B1371361 : Blo 1217426 1371361 := bbase (se 2 (by rfl) ⟨514260, by rfl⟩ : syracuseStep 1371361 = 1028521) (by norm_num)
theorem B2739437 : Blo 1217426 2739437 := bbase (se 3 (by rfl) ⟨513644, by rfl⟩ : syracuseStep 2739437 = 1027289) (by norm_num)
theorem B1371397 : Blo 1217426 1371397 := bbase (se 4 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 1371397 = 257137) (by norm_num)
theorem B1371433 : Blo 1217426 1371433 := bbase (se 2 (by rfl) ⟨514287, by rfl⟩ : syracuseStep 1371433 = 1028575) (by norm_num)
theorem B2739509 : Blo 1217426 2739509 := bbase (se 5 (by rfl) ⟨128414, by rfl⟩ : syracuseStep 2739509 = 256829) (by norm_num)
theorem B1371469 : Blo 1217426 1371469 := bbase (se 3 (by rfl) ⟨257150, by rfl⟩ : syracuseStep 1371469 = 514301) (by norm_num)
theorem B3083629 : Blo 1217426 3083629 := bbase (se 3 (by rfl) ⟨578180, by rfl⟩ : syracuseStep 3083629 = 1156361) (by norm_num)
theorem B1371505 : Blo 1217426 1371505 := bbase (se 2 (by rfl) ⟨514314, by rfl⟩ : syracuseStep 1371505 = 1028629) (by norm_num)
theorem B2600309 : Blo 1217426 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B2739581 : Blo 1217426 2739581 := bbase (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) (by norm_num)
theorem B6172037 : Blo 1217426 6172037 := bbase (se 4 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 6172037 = 1157257) (by norm_num)
theorem B1371541 : Blo 1217426 1371541 := bbase (se 6 (by rfl) ⟨32145, by rfl⟩ : syracuseStep 1371541 = 64291) (by norm_num)
theorem B1371577 : Blo 1217426 1371577 := bbase (se 2 (by rfl) ⟨514341, by rfl⟩ : syracuseStep 1371577 = 1028683) (by norm_num)
theorem B2739653 : Blo 1217426 2739653 := bbase (se 4 (by rfl) ⟨256842, by rfl⟩ : syracuseStep 2739653 = 513685) (by norm_num)
theorem B3706325 : Blo 1217426 3706325 := bbase (se 7 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 3706325 = 86867) (by norm_num)
theorem B3083741 : Blo 1217426 3083741 := bbase (se 3 (by rfl) ⟨578201, by rfl⟩ : syracuseStep 3083741 = 1156403) (by norm_num)
theorem B1371613 : Blo 1217426 1371613 := bbase (se 3 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 1371613 = 514355) (by norm_num)
theorem B1371649 : Blo 1217426 1371649 := bbase (se 2 (by rfl) ⟨514368, by rfl⟩ : syracuseStep 1371649 = 1028737) (by norm_num)
theorem B2739725 : Blo 1217426 2739725 := bbase (se 3 (by rfl) ⟨513698, by rfl⟩ : syracuseStep 2739725 = 1027397) (by norm_num)
theorem B2780693 : Blo 1217426 2780693 := bbase (se 6 (by rfl) ⟨65172, by rfl⟩ : syracuseStep 2780693 = 130345) (by norm_num)
theorem B1371685 : Blo 1217426 1371685 := bbase (se 4 (by rfl) ⟨128595, by rfl⟩ : syracuseStep 1371685 = 257191) (by norm_num)
theorem B4623925 : Blo 1217426 4623925 := bbase (se 5 (by rfl) ⟨216746, by rfl⟩ : syracuseStep 4623925 = 433493) (by norm_num)
theorem B1371721 : Blo 1217426 1371721 := bbase (se 2 (by rfl) ⟨514395, by rfl⟩ : syracuseStep 1371721 = 1028791) (by norm_num)
theorem B2739797 : Blo 1217426 2739797 := bbase (se 8 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 2739797 = 32107) (by norm_num)
theorem B3468901 : Blo 1217426 3468901 := bbase (se 4 (by rfl) ⟨325209, by rfl⟩ : syracuseStep 3468901 = 650419) (by norm_num)
theorem B4689509 : Blo 1217426 4689509 := bbase (se 4 (by rfl) ⟨439641, by rfl⟩ : syracuseStep 4689509 = 879283) (by norm_num)
theorem B1371757 : Blo 1217426 1371757 := bbase (se 3 (by rfl) ⟨257204, by rfl⟩ : syracuseStep 1371757 = 514409) (by norm_num)
theorem B1371793 : Blo 1217426 1371793 := bbase (se 2 (by rfl) ⟨514422, by rfl⟩ : syracuseStep 1371793 = 1028845) (by norm_num)
theorem B2739869 : Blo 1217426 2739869 := bbase (se 3 (by rfl) ⟨513725, by rfl⟩ : syracuseStep 2739869 = 1027451) (by norm_num)
theorem B1805981 : Blo 1217426 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B3083933 : Blo 1217426 3083933 := bbase (se 3 (by rfl) ⟨578237, by rfl⟩ : syracuseStep 3083933 = 1156475) (by norm_num)
theorem B9875125 : Blo 1217426 9875125 := bbase (se 5 (by rfl) ⟨462896, by rfl⟩ : syracuseStep 9875125 = 925793) (by norm_num)
theorem B1371829 : Blo 1217426 1371829 := bbase (se 5 (by rfl) ⟨64304, by rfl⟩ : syracuseStep 1371829 = 128609) (by norm_num)
theorem B2600677 : Blo 1217426 2600677 := bbase (se 4 (by rfl) ⟨243813, by rfl⟩ : syracuseStep 2600677 = 487627) (by norm_num)
theorem B2739941 : Blo 1217426 2739941 := bbase (se 4 (by rfl) ⟨256869, by rfl⟩ : syracuseStep 2739941 = 513739) (by norm_num)
theorem B10415861 : Blo 1217426 10415861 := bbase (se 5 (by rfl) ⟨488243, by rfl⟩ : syracuseStep 10415861 = 976487) (by norm_num)
theorem B3469061 : Blo 1217426 3469061 := bbase (se 4 (by rfl) ⟨325224, by rfl⟩ : syracuseStep 3469061 = 650449) (by norm_num)
theorem B5713669 : Blo 1217426 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B6164261 : Blo 1217426 6164261 := bbase (se 4 (by rfl) ⟨577899, by rfl⟩ : syracuseStep 6164261 = 1155799) (by norm_num)
theorem B2314021 : Blo 1217426 2314021 := bbase (se 4 (by rfl) ⟨216939, by rfl⟩ : syracuseStep 2314021 = 433879) (by norm_num)
theorem B5279525 : Blo 1217426 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B2740013 : Blo 1217426 2740013 := bbase (se 3 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 2740013 = 1027505) (by norm_num)
theorem B4624229 : Blo 1217426 4624229 := bbase (se 4 (by rfl) ⟨433521, by rfl⟩ : syracuseStep 4624229 = 867043) (by norm_num)
theorem B3518309 : Blo 1217426 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B2740085 : Blo 1217426 2740085 := bbase (se 5 (by rfl) ⟨128441, by rfl⟩ : syracuseStep 2740085 = 256883) (by norm_num)
theorem B10407797 : Blo 1217426 10407797 := bbase (se 5 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 10407797 = 975731) (by norm_num)
theorem B2314165 : Blo 1217426 2314165 := bbase (se 5 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 2314165 = 216953) (by norm_num)
theorem B2740157 : Blo 1217426 2740157 := bbase (se 3 (by rfl) ⟨513779, by rfl⟩ : syracuseStep 2740157 = 1027559) (by norm_num)
theorem B3469301 : Blo 1217426 3469301 := bbase (se 5 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 3469301 = 325247) (by norm_num)
theorem B3084277 : Blo 1217426 3084277 := bbase (se 5 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 3084277 = 289151) (by norm_num)
theorem B2740229 : Blo 1217426 2740229 := bbase (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) (by norm_num)
theorem B6582293 : Blo 1217426 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B2740301 : Blo 1217426 2740301 := bbase (se 3 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 2740301 = 1027613) (by norm_num)
theorem B2314325 : Blo 1217426 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B3084389 : Blo 1217426 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B2740373 : Blo 1217426 2740373 := bbase (se 6 (by rfl) ⟨64227, by rfl⟩ : syracuseStep 2740373 = 128455) (by norm_num)
theorem B3469493 : Blo 1217426 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B3518677 : Blo 1217426 3518677 := bbase (se 7 (by rfl) ⟨41234, by rfl⟩ : syracuseStep 3518677 = 82469) (by norm_num)
theorem B2740445 : Blo 1217426 2740445 := bbase (se 3 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 2740445 = 1027667) (by norm_num)
theorem B2314469 : Blo 1217426 2314469 := bbase (se 4 (by rfl) ⟨216981, by rfl⟩ : syracuseStep 2314469 = 433963) (by norm_num)
theorem B2740517 : Blo 1217426 2740517 := bbase (se 4 (by rfl) ⟨256923, by rfl⟩ : syracuseStep 2740517 = 513847) (by norm_num)
theorem B3084581 : Blo 1217426 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B2085197 : Blo 1217426 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B2740589 : Blo 1217426 2740589 := bbase (se 3 (by rfl) ⟨513860, by rfl⟩ : syracuseStep 2740589 = 1027721) (by norm_num)
theorem B2740661 : Blo 1217426 2740661 := bbase (se 5 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 2740661 = 256937) (by norm_num)
theorem B6943157 : Blo 1217426 6943157 := bbase (se 5 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 6943157 = 650921) (by norm_num)
theorem B2740733 : Blo 1217426 2740733 := bbase (se 3 (by rfl) ⟨513887, by rfl⟩ : syracuseStep 2740733 = 1027775) (by norm_num)
theorem B2200069 : Blo 1217426 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B2314757 : Blo 1217426 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B2470429 : Blo 1217426 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B2740805 : Blo 1217426 2740805 := bbase (se 4 (by rfl) ⟨256950, by rfl⟩ : syracuseStep 2740805 = 513901) (by norm_num)
theorem B3084925 : Blo 1217426 3084925 := bbase (se 3 (by rfl) ⟨578423, by rfl⟩ : syracuseStep 3084925 = 1156847) (by norm_num)
theorem B2740877 : Blo 1217426 2740877 := bbase (se 3 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 2740877 = 1027829) (by norm_num)
theorem B6173333 : Blo 1217426 6173333 := bbase (se 6 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 6173333 = 289375) (by norm_num)
theorem B2314909 : Blo 1217426 2314909 := bbase (se 3 (by rfl) ⟨434045, by rfl⟩ : syracuseStep 2314909 = 868091) (by norm_num)
theorem B12513973 : Blo 1217426 12513973 := bbase (se 5 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 12513973 = 1173185) (by norm_num)
theorem B2740949 : Blo 1217426 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B3085037 : Blo 1217426 3085037 := bbase (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) (by norm_num)
theorem B2741021 : Blo 1217426 2741021 := bbase (se 3 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 2741021 = 1027883) (by norm_num)
theorem B5206837 : Blo 1217426 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1733437 : Blo 1217426 1733437 := bbase (se 3 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 1733437 = 650039) (by norm_num)
theorem B2741093 : Blo 1217426 2741093 := bbase (se 4 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 2741093 = 513955) (by norm_num)
theorem B2003837 : Blo 1217426 2003837 := bbase (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) (by norm_num)
theorem B2503549 : Blo 1217426 2503549 := bbase (se 3 (by rfl) ⟨469415, by rfl⟩ : syracuseStep 2503549 = 938831) (by norm_num)
theorem B2741165 : Blo 1217426 2741165 := bbase (se 3 (by rfl) ⟨513968, by rfl⟩ : syracuseStep 2741165 = 1027937) (by norm_num)
theorem B3085229 : Blo 1217426 3085229 := bbase (se 3 (by rfl) ⟨578480, by rfl⟩ : syracuseStep 3085229 = 1156961) (by norm_num)
theorem B1733557 : Blo 1217426 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B4109237 : Blo 1217426 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B2741237 : Blo 1217426 2741237 := bbase (se 5 (by rfl) ⟨128495, by rfl⟩ : syracuseStep 2741237 = 256991) (by norm_num)
theorem B1733653 : Blo 1217426 1733653 := bbase (se 6 (by rfl) ⟨40632, by rfl⟩ : syracuseStep 1733653 = 81265) (by norm_num)
theorem B6165557 : Blo 1217426 6165557 := bbase (se 5 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 6165557 = 578021) (by norm_num)
theorem B2741309 : Blo 1217426 2741309 := bbase (se 3 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 2741309 = 1027991) (by norm_num)
theorem B2741381 : Blo 1217426 2741381 := bbase (se 4 (by rfl) ⟨257004, by rfl⟩ : syracuseStep 2741381 = 514009) (by norm_num)
theorem B16888981 : Blo 1217426 16888981 := bbase (se 6 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 16888981 = 791671) (by norm_num)
theorem B3470485 : Blo 1217426 3470485 := bbase (se 6 (by rfl) ⟨81339, by rfl⟩ : syracuseStep 3470485 = 162679) (by norm_num)
theorem B2602181 : Blo 1217426 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B2741453 : Blo 1217426 2741453 := bbase (se 3 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 2741453 = 1028045) (by norm_num)
theorem B3085573 : Blo 1217426 3085573 := bbase (se 4 (by rfl) ⟨289272, by rfl⟩ : syracuseStep 3085573 = 578545) (by norm_num)
theorem B2741525 : Blo 1217426 2741525 := bbase (se 6 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 2741525 = 128509) (by norm_num)
theorem B9385237 : Blo 1217426 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B25335125 : Blo 1217426 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B2602325 : Blo 1217426 2602325 := bbase (se 13 (by rfl) ⟨476, by rfl⟩ : syracuseStep 2602325 = 953) (by norm_num)
theorem B2741597 : Blo 1217426 2741597 := bbase (se 3 (by rfl) ⟨514049, by rfl⟩ : syracuseStep 2741597 = 1028099) (by norm_num)
theorem B4109669 : Blo 1217426 4109669 := bbase (se 4 (by rfl) ⟨385281, by rfl⟩ : syracuseStep 4109669 = 770563) (by norm_num)
theorem B3085685 : Blo 1217426 3085685 := bbase (se 5 (by rfl) ⟨144641, by rfl⟩ : syracuseStep 3085685 = 289283) (by norm_num)
theorem B2741669 : Blo 1217426 2741669 := bbase (se 4 (by rfl) ⟨257031, by rfl⟩ : syracuseStep 2741669 = 514063) (by norm_num)
theorem B3904949 : Blo 1217426 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B2741741 : Blo 1217426 2741741 := bbase (se 3 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 2741741 = 1028153) (by norm_num)
theorem B1734149 : Blo 1217426 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B2741813 : Blo 1217426 2741813 := bbase (se 5 (by rfl) ⟨128522, by rfl⟩ : syracuseStep 2741813 = 257045) (by norm_num)
theorem B3085877 : Blo 1217426 3085877 := bbase (se 5 (by rfl) ⟨144650, by rfl⟩ : syracuseStep 3085877 = 289301) (by norm_num)
theorem B31217237 : Blo 1217426 31217237 := bbase (se 8 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 31217237 = 365827) (by norm_num)
theorem B1300069 : Blo 1217426 1300069 := bbase (se 4 (by rfl) ⟨121881, by rfl⟩ : syracuseStep 1300069 = 243763) (by norm_num)
theorem B2741885 : Blo 1217426 2741885 := bbase (se 3 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 2741885 = 1028207) (by norm_num)
theorem B2602685 : Blo 1217426 2602685 := bbase (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) (by norm_num)
theorem B2741957 : Blo 1217426 2741957 := bbase (se 4 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 2741957 = 514117) (by norm_num)
theorem B2742029 : Blo 1217426 2742029 := bbase (se 3 (by rfl) ⟨514130, by rfl⟩ : syracuseStep 2742029 = 1028261) (by norm_num)
theorem B1464077 : Blo 1217426 1464077 := bbase (se 3 (by rfl) ⟨274514, by rfl⟩ : syracuseStep 1464077 = 549029) (by norm_num)
theorem B4110101 : Blo 1217426 4110101 := bbase (se 6 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 4110101 = 192661) (by norm_num)
theorem B1300249 : Blo 1217426 1300249 := bbase (se 2 (by rfl) ⟨487593, by rfl⟩ : syracuseStep 1300249 = 975187) (by norm_num)
theorem B2742101 : Blo 1217426 2742101 := bbase (se 9 (by rfl) ⟨8033, by rfl⟩ : syracuseStep 2742101 = 16067) (by norm_num)
theorem B1464193 : Blo 1217426 1464193 := bbase (se 2 (by rfl) ⟨549072, by rfl⟩ : syracuseStep 1464193 = 1098145) (by norm_num)
theorem B3086221 : Blo 1217426 3086221 := bbase (se 3 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 3086221 = 1157333) (by norm_num)
theorem B2742173 : Blo 1217426 2742173 := bbase (se 3 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 2742173 = 1028315) (by norm_num)
theorem B4626341 : Blo 1217426 4626341 := bbase (se 4 (by rfl) ⟨433719, by rfl⟩ : syracuseStep 4626341 = 867439) (by norm_num)
theorem B1464265 : Blo 1217426 1464265 := bbase (se 2 (by rfl) ⟨549099, by rfl⟩ : syracuseStep 1464265 = 1098199) (by norm_num)
theorem B11704277 : Blo 1217426 11704277 := bbase (se 7 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 11704277 = 274319) (by norm_num)
theorem B2742245 : Blo 1217426 2742245 := bbase (se 4 (by rfl) ⟨257085, by rfl⟩ : syracuseStep 2742245 = 514171) (by norm_num)
theorem B3086333 : Blo 1217426 3086333 := bbase (se 3 (by rfl) ⟨578687, by rfl⟩ : syracuseStep 3086333 = 1157375) (by norm_num)
theorem B1734701 : Blo 1217426 1734701 := bbase (se 3 (by rfl) ⟨325256, by rfl⟩ : syracuseStep 1734701 = 650513) (by norm_num)
theorem B2742317 : Blo 1217426 2742317 := bbase (se 3 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 2742317 = 1028369) (by norm_num)
theorem B4388917 : Blo 1217426 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B1464385 : Blo 1217426 1464385 := bbase (se 2 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 1464385 = 1098289) (by norm_num)
theorem B16660565 : Blo 1217426 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B2742389 : Blo 1217426 2742389 := bbase (se 5 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 2742389 = 257099) (by norm_num)
theorem B2742461 : Blo 1217426 2742461 := bbase (se 3 (by rfl) ⟨514211, by rfl⟩ : syracuseStep 2742461 = 1028423) (by norm_num)
theorem B3086525 : Blo 1217426 3086525 := bbase (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) (by norm_num)
theorem B4110533 : Blo 1217426 4110533 := bbase (se 4 (by rfl) ⟨385362, by rfl⟩ : syracuseStep 4110533 = 770725) (by norm_num)
theorem B4626629 : Blo 1217426 4626629 := bbase (se 4 (by rfl) ⟨433746, by rfl⟩ : syracuseStep 4626629 = 867493) (by norm_num)
theorem B1300693 : Blo 1217426 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B3471589 : Blo 1217426 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B2742533 : Blo 1217426 2742533 := bbase (se 4 (by rfl) ⟨257112, by rfl⟩ : syracuseStep 2742533 = 514225) (by norm_num)
theorem B6166853 : Blo 1217426 6166853 := bbase (se 4 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 6166853 = 1156285) (by norm_num)
theorem B2054477 : Blo 1217426 2054477 := bbase (se 3 (by rfl) ⟨385214, by rfl⟩ : syracuseStep 2054477 = 770429) (by norm_num)
theorem B2742605 : Blo 1217426 2742605 := bbase (se 3 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 2742605 = 1028477) (by norm_num)
theorem B1300817 : Blo 1217426 1300817 := bbase (se 2 (by rfl) ⟨487806, by rfl⟩ : syracuseStep 1300817 = 975613) (by norm_num)
theorem B17562005 : Blo 1217426 17562005 := bbase (se 6 (by rfl) ⟨411609, by rfl⟩ : syracuseStep 17562005 = 823219) (by norm_num)
theorem B2742677 : Blo 1217426 2742677 := bbase (se 6 (by rfl) ⟨64281, by rfl⟩ : syracuseStep 2742677 = 128563) (by norm_num)
theorem B1464769 : Blo 1217426 1464769 := bbase (se 2 (by rfl) ⟨549288, by rfl⟩ : syracuseStep 1464769 = 1098577) (by norm_num)
theorem B2054605 : Blo 1217426 2054605 := bbase (se 3 (by rfl) ⟨385238, by rfl⟩ : syracuseStep 2054605 = 770477) (by norm_num)
theorem B13171157 : Blo 1217426 13171157 := bbase (se 7 (by rfl) ⟨154349, by rfl⟩ : syracuseStep 13171157 = 308699) (by norm_num)
theorem B2742749 : Blo 1217426 2742749 := bbase (se 3 (by rfl) ⟨514265, by rfl⟩ : syracuseStep 2742749 = 1028531) (by norm_num)
theorem B2054693 : Blo 1217426 2054693 := bbase (se 4 (by rfl) ⟨192627, by rfl⟩ : syracuseStep 2054693 = 385255) (by norm_num)
theorem B2742821 : Blo 1217426 2742821 := bbase (se 4 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 2742821 = 514279) (by norm_num)
theorem B2603573 : Blo 1217426 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B1301069 : Blo 1217426 1301069 := bbase (se 3 (by rfl) ⟨243950, by rfl⟩ : syracuseStep 1301069 = 487901) (by norm_num)
theorem B2226781 : Blo 1217426 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B2742893 : Blo 1217426 2742893 := bbase (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) (by norm_num)
theorem B4110965 : Blo 1217426 4110965 := bbase (se 5 (by rfl) ⟨192701, by rfl⟩ : syracuseStep 4110965 = 385403) (by norm_num)
theorem B2054821 : Blo 1217426 2054821 := bbase (se 4 (by rfl) ⟨192639, by rfl⟩ : syracuseStep 2054821 = 385279) (by norm_num)
theorem B2742965 : Blo 1217426 2742965 := bbase (se 5 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 2742965 = 257153) (by norm_num)
theorem B3906245 : Blo 1217426 3906245 := bbase (se 4 (by rfl) ⟨366210, by rfl⟩ : syracuseStep 3906245 = 732421) (by norm_num)
theorem B2054909 : Blo 1217426 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B2743037 : Blo 1217426 2743037 := bbase (se 3 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 2743037 = 1028639) (by norm_num)
theorem B1735453 : Blo 1217426 1735453 := bbase (se 3 (by rfl) ⟨325397, by rfl⟩ : syracuseStep 1735453 = 650795) (by norm_num)
theorem B2603821 : Blo 1217426 2603821 := bbase (se 3 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 2603821 = 976433) (by norm_num)
theorem B2743109 : Blo 1217426 2743109 := bbase (se 4 (by rfl) ⟨257166, by rfl⟩ : syracuseStep 2743109 = 514333) (by norm_num)
theorem B2055037 : Blo 1217426 2055037 := bbase (se 3 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 2055037 = 770639) (by norm_num)
theorem B2743181 : Blo 1217426 2743181 := bbase (se 3 (by rfl) ⟨514346, by rfl⟩ : syracuseStep 2743181 = 1028693) (by norm_num)
theorem B2055125 : Blo 1217426 2055125 := bbase (se 7 (by rfl) ⟨24083, by rfl⟩ : syracuseStep 2055125 = 48167) (by norm_num)
theorem B2743253 : Blo 1217426 2743253 := bbase (se 7 (by rfl) ⟨32147, by rfl⟩ : syracuseStep 2743253 = 64295) (by norm_num)
theorem B1301513 : Blo 1217426 1301513 := bbase (se 2 (by rfl) ⟨488067, by rfl⟩ : syracuseStep 1301513 = 976135) (by norm_num)
theorem B2194445 : Blo 1217426 2194445 := bbase (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) (by norm_num)
theorem B2743325 : Blo 1217426 2743325 := bbase (se 3 (by rfl) ⟨514373, by rfl⟩ : syracuseStep 2743325 = 1028747) (by norm_num)
theorem B4111397 : Blo 1217426 4111397 := bbase (se 4 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 4111397 = 770887) (by norm_num)
theorem B4168741 : Blo 1217426 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B2194501 : Blo 1217426 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B2055253 : Blo 1217426 2055253 := bbase (se 8 (by rfl) ⟨12042, by rfl⟩ : syracuseStep 2055253 = 24085) (by norm_num)
theorem B2743397 : Blo 1217426 2743397 := bbase (se 4 (by rfl) ⟨257193, by rfl⟩ : syracuseStep 2743397 = 514387) (by norm_num)
theorem B2194589 : Blo 1217426 2194589 := bbase (se 3 (by rfl) ⟨411485, by rfl⟩ : syracuseStep 2194589 = 822971) (by norm_num)
theorem B2055341 : Blo 1217426 2055341 := bbase (se 3 (by rfl) ⟨385376, by rfl⟩ : syracuseStep 2055341 = 770753) (by norm_num)
theorem B2743469 : Blo 1217426 2743469 := bbase (se 3 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 2743469 = 1028801) (by norm_num)
theorem B2743541 : Blo 1217426 2743541 := bbase (se 5 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 2743541 = 257207) (by norm_num)
theorem B1301761 : Blo 1217426 1301761 := bbase (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) (by norm_num)
theorem B2817301 : Blo 1217426 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B2604325 : Blo 1217426 2604325 := bbase (se 4 (by rfl) ⟨244155, by rfl⟩ : syracuseStep 2604325 = 488311) (by norm_num)
theorem B2055469 : Blo 1217426 2055469 := bbase (se 3 (by rfl) ⟨385400, by rfl⟩ : syracuseStep 2055469 = 770801) (by norm_num)
theorem B2743613 : Blo 1217426 2743613 := bbase (se 3 (by rfl) ⟨514427, by rfl⟩ : syracuseStep 2743613 = 1028855) (by norm_num)
theorem B1826141 : Blo 1217426 1826141 := bbase (se 3 (by rfl) ⟨342401, by rfl⟩ : syracuseStep 1826141 = 684803) (by norm_num)
theorem B3169637 : Blo 1217426 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B4627813 : Blo 1217426 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B1408369 : Blo 1217426 1408369 := bbase (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) (by norm_num)
theorem B1826165 : Blo 1217426 1826165 := bbase (se 5 (by rfl) ⟨85601, by rfl⟩ : syracuseStep 1826165 = 171203) (by norm_num)
theorem B3128701 : Blo 1217426 3128701 := bbase (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) (by norm_num)
theorem B2055557 : Blo 1217426 2055557 := bbase (se 4 (by rfl) ⟨192708, by rfl⟩ : syracuseStep 2055557 = 385417) (by norm_num)
theorem B2743685 : Blo 1217426 2743685 := bbase (se 4 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 2743685 = 514441) (by norm_num)
theorem B1826189 : Blo 1217426 1826189 := bbase (se 3 (by rfl) ⟨342410, by rfl⟩ : syracuseStep 1826189 = 684821) (by norm_num)
theorem B1826213 : Blo 1217426 1826213 := bbase (se 4 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 1826213 = 342415) (by norm_num)
theorem B1826237 : Blo 1217426 1826237 := bbase (se 3 (by rfl) ⟨342419, by rfl⟩ : syracuseStep 1826237 = 684839) (by norm_num)
theorem B2194877 : Blo 1217426 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B1826261 : Blo 1217426 1826261 := bbase (se 7 (by rfl) ⟨21401, by rfl⟩ : syracuseStep 1826261 = 42803) (by norm_num)
theorem B4111829 : Blo 1217426 4111829 := bbase (se 7 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 4111829 = 96371) (by norm_num)
theorem B1318361 : Blo 1217426 1318361 := bbase (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) (by norm_num)
theorem B1826285 : Blo 1217426 1826285 := bbase (se 3 (by rfl) ⟨342428, by rfl⟩ : syracuseStep 1826285 = 684857) (by norm_num)
theorem B1826309 : Blo 1217426 1826309 := bbase (se 4 (by rfl) ⟨171216, by rfl⟩ : syracuseStep 1826309 = 342433) (by norm_num)
theorem B2055685 : Blo 1217426 2055685 := bbase (se 4 (by rfl) ⟨192720, by rfl⟩ : syracuseStep 2055685 = 385441) (by norm_num)
theorem B1826333 : Blo 1217426 1826333 := bbase (se 3 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 1826333 = 684875) (by norm_num)
theorem B1826357 : Blo 1217426 1826357 := bbase (se 5 (by rfl) ⟨85610, by rfl⟩ : syracuseStep 1826357 = 171221) (by norm_num)
theorem B1736245 : Blo 1217426 1736245 := bbase (se 5 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 1736245 = 162773) (by norm_num)
theorem B1826381 : Blo 1217426 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B2195021 : Blo 1217426 2195021 := bbase (se 3 (by rfl) ⟨411566, by rfl⟩ : syracuseStep 2195021 = 823133) (by norm_num)
theorem B6168149 : Blo 1217426 6168149 := bbase (se 8 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 6168149 = 72283) (by norm_num)
theorem B2055773 : Blo 1217426 2055773 := bbase (se 3 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 2055773 = 770915) (by norm_num)
theorem B1826405 : Blo 1217426 1826405 := bbase (se 4 (by rfl) ⟨171225, by rfl⟩ : syracuseStep 1826405 = 342451) (by norm_num)
theorem B1826429 : Blo 1217426 1826429 := bbase (se 3 (by rfl) ⟨342455, by rfl⟩ : syracuseStep 1826429 = 684911) (by norm_num)
theorem B2817677 : Blo 1217426 2817677 := bbase (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) (by norm_num)
theorem B1826453 : Blo 1217426 1826453 := bbase (se 6 (by rfl) ⟨42807, by rfl⟩ : syracuseStep 1826453 = 85615) (by norm_num)
theorem B4628117 : Blo 1217426 4628117 := bbase (se 6 (by rfl) ⟨108471, by rfl⟩ : syracuseStep 4628117 = 216943) (by norm_num)
theorem B1564309 : Blo 1217426 1564309 := bbase (se 6 (by rfl) ⟨36663, by rfl⟩ : syracuseStep 1564309 = 73327) (by norm_num)
theorem B1826477 : Blo 1217426 1826477 := bbase (se 3 (by rfl) ⟨342464, by rfl⟩ : syracuseStep 1826477 = 684929) (by norm_num)
theorem B1826501 : Blo 1217426 1826501 := bbase (se 4 (by rfl) ⟨171234, by rfl⟩ : syracuseStep 1826501 = 342469) (by norm_num)
theorem B1826525 : Blo 1217426 1826525 := bbase (se 3 (by rfl) ⟨342473, by rfl⟩ : syracuseStep 1826525 = 684947) (by norm_num)
theorem B2055901 : Blo 1217426 2055901 := bbase (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) (by norm_num)
theorem B1826549 : Blo 1217426 1826549 := bbase (se 5 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 1826549 = 171239) (by norm_num)
theorem B1826573 : Blo 1217426 1826573 := bbase (se 3 (by rfl) ⟨342482, by rfl⟩ : syracuseStep 1826573 = 684965) (by norm_num)
theorem B1826597 : Blo 1217426 1826597 := bbase (se 4 (by rfl) ⟨171243, by rfl⟩ : syracuseStep 1826597 = 342487) (by norm_num)
theorem B2055989 : Blo 1217426 2055989 := bbase (se 5 (by rfl) ⟨96374, by rfl⟩ : syracuseStep 2055989 = 192749) (by norm_num)
theorem B2817845 : Blo 1217426 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B1826621 : Blo 1217426 1826621 := bbase (se 3 (by rfl) ⟨342491, by rfl⟩ : syracuseStep 1826621 = 684983) (by norm_num)
theorem B1826645 : Blo 1217426 1826645 := bbase (se 9 (by rfl) ⟨5351, by rfl⟩ : syracuseStep 1826645 = 10703) (by norm_num)
theorem B5201765 : Blo 1217426 5201765 := bbase (se 4 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 5201765 = 975331) (by norm_num)
theorem B4169573 : Blo 1217426 4169573 := bbase (se 4 (by rfl) ⟨390897, by rfl⟩ : syracuseStep 4169573 = 781795) (by norm_num)
theorem B1826669 : Blo 1217426 1826669 := bbase (se 3 (by rfl) ⟨342500, by rfl⟩ : syracuseStep 1826669 = 685001) (by norm_num)
theorem B2195309 : Blo 1217426 2195309 := bbase (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) (by norm_num)
theorem B1826693 : Blo 1217426 1826693 := bbase (se 4 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 1826693 = 342505) (by norm_num)
theorem B4112261 : Blo 1217426 4112261 := bbase (se 4 (by rfl) ⟨385524, by rfl⟩ : syracuseStep 4112261 = 771049) (by norm_num)
theorem B1826717 : Blo 1217426 1826717 := bbase (se 3 (by rfl) ⟨342509, by rfl⟩ : syracuseStep 1826717 = 685019) (by norm_num)
theorem B1826741 : Blo 1217426 1826741 := bbase (se 5 (by rfl) ⟨85628, by rfl⟩ : syracuseStep 1826741 = 171257) (by norm_num)
theorem B2195381 : Blo 1217426 2195381 := bbase (se 5 (by rfl) ⟨102908, by rfl⟩ : syracuseStep 2195381 = 205817) (by norm_num)
theorem B2056117 : Blo 1217426 2056117 := bbase (se 5 (by rfl) ⟨96380, by rfl⟩ : syracuseStep 2056117 = 192761) (by norm_num)
theorem B3702725 : Blo 1217426 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B1826765 : Blo 1217426 1826765 := bbase (se 3 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 1826765 = 685037) (by norm_num)
theorem B1826789 : Blo 1217426 1826789 := bbase (se 4 (by rfl) ⟨171261, by rfl⟩ : syracuseStep 1826789 = 342523) (by norm_num)
theorem B1826813 : Blo 1217426 1826813 := bbase (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) (by norm_num)
theorem B1826819 : Blo 1217426 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B1826849 : Blo 1217426 1826849 := bstep (se 2 (by rfl) ⟨685068, by rfl⟩ : syracuseStep 1826849 = 1370137) B1370137
theorem B2056225 : Blo 1217426 2056225 := bstep (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) B1542169
theorem B1826867 : Blo 1217426 1826867 := bstep (se 1 (by rfl) ⟨1370150, by rfl⟩ : syracuseStep 1826867 = 2740301) B2740301
theorem B2056259 : Blo 1217426 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B1826897 : Blo 1217426 1826897 := bstep (se 2 (by rfl) ⟨685086, by rfl⟩ : syracuseStep 1826897 = 1370173) B1370173
theorem B5931107 : Blo 1217426 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B1826915 : Blo 1217426 1826915 := bstep (se 1 (by rfl) ⟨1370186, by rfl⟩ : syracuseStep 1826915 = 2740373) B2740373
theorem B1826945 : Blo 1217426 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1826963 : Blo 1217426 1826963 := bstep (se 1 (by rfl) ⟨1370222, by rfl⟩ : syracuseStep 1826963 = 2740445) B2740445
theorem B1826993 : Blo 1217426 1826993 := bstep (se 2 (by rfl) ⟨685122, by rfl⟩ : syracuseStep 1826993 = 1370245) B1370245
theorem B1827011 : Blo 1217426 1827011 := bstep (se 1 (by rfl) ⟨1370258, by rfl⟩ : syracuseStep 1827011 = 2740517) B2740517
theorem B2056387 : Blo 1217426 2056387 := bstep (se 1 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 2056387 = 3084581) B3084581
theorem B1827041 : Blo 1217426 1827041 := bstep (se 2 (by rfl) ⟨685140, by rfl⟩ : syracuseStep 1827041 = 1370281) B1370281
theorem B1827059 : Blo 1217426 1827059 := bstep (se 1 (by rfl) ⟨1370294, by rfl⟩ : syracuseStep 1827059 = 2740589) B2740589
theorem B1827089 : Blo 1217426 1827089 := bstep (se 2 (by rfl) ⟨685158, by rfl⟩ : syracuseStep 1827089 = 1370317) B1370317
theorem B1827107 : Blo 1217426 1827107 := bstep (se 1 (by rfl) ⟨1370330, by rfl⟩ : syracuseStep 1827107 = 2740661) B2740661
theorem B4628771 : Blo 1217426 4628771 := bstep (se 1 (by rfl) ⟨3471578, by rfl⟩ : syracuseStep 4628771 = 6943157) B6943157
theorem B4628785 : Blo 1217426 4628785 := bstep (se 2 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 4628785 = 3471589) B3471589
theorem B1827137 : Blo 1217426 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B2056529 : Blo 1217426 2056529 := bstep (se 2 (by rfl) ⟨771198, by rfl⟩ : syracuseStep 2056529 = 1542397) B1542397
theorem B1827155 : Blo 1217426 1827155 := bstep (se 1 (by rfl) ⟨1370366, by rfl⟩ : syracuseStep 1827155 = 2740733) B2740733
theorem B1827185 : Blo 1217426 1827185 := bstep (se 2 (by rfl) ⟨685194, by rfl⟩ : syracuseStep 1827185 = 1370389) B1370389
theorem B1827203 : Blo 1217426 1827203 := bstep (se 1 (by rfl) ⟨1370402, by rfl⟩ : syracuseStep 1827203 = 2740805) B2740805
theorem B4391309 : Blo 1217426 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B1827233 : Blo 1217426 1827233 := bstep (se 2 (by rfl) ⟨685212, by rfl⟩ : syracuseStep 1827233 = 1370425) B1370425
theorem B1827251 : Blo 1217426 1827251 := bstep (se 1 (by rfl) ⟨1370438, by rfl⟩ : syracuseStep 1827251 = 2740877) B2740877
theorem B1827281 : Blo 1217426 1827281 := bstep (se 2 (by rfl) ⟨685230, by rfl⟩ : syracuseStep 1827281 = 1370461) B1370461
theorem B2056657 : Blo 1217426 2056657 := bstep (se 2 (by rfl) ⟨771246, by rfl⟩ : syracuseStep 2056657 = 1542493) B1542493
theorem B1827299 : Blo 1217426 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B2056691 : Blo 1217426 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B1827329 : Blo 1217426 1827329 := bstep (se 2 (by rfl) ⟨685248, by rfl⟩ : syracuseStep 1827329 = 1370497) B1370497
theorem B4112909 : Blo 1217426 4112909 := bstep (se 3 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 4112909 = 1542341) B1542341
theorem B1827347 : Blo 1217426 1827347 := bstep (se 1 (by rfl) ⟨1370510, by rfl⟩ : syracuseStep 1827347 = 2741021) B2741021
theorem B1827377 : Blo 1217426 1827377 := bstep (se 2 (by rfl) ⟨685266, by rfl⟩ : syracuseStep 1827377 = 1370533) B1370533
theorem B1827395 : Blo 1217426 1827395 := bstep (se 1 (by rfl) ⟨1370546, by rfl⟩ : syracuseStep 1827395 = 2741093) B2741093
theorem B4112963 : Blo 1217426 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B1827425 : Blo 1217426 1827425 := bstep (se 2 (by rfl) ⟨685284, by rfl⟩ : syracuseStep 1827425 = 1370569) B1370569
theorem B1827443 : Blo 1217426 1827443 := bstep (se 1 (by rfl) ⟨1370582, by rfl⟩ : syracuseStep 1827443 = 2741165) B2741165
theorem B2056819 : Blo 1217426 2056819 := bstep (se 1 (by rfl) ⟨1542614, by rfl⟩ : syracuseStep 2056819 = 3085229) B3085229
theorem B3293827 : Blo 1217426 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B1827473 : Blo 1217426 1827473 := bstep (se 2 (by rfl) ⟨685302, by rfl⟩ : syracuseStep 1827473 = 1370605) B1370605
theorem B1827491 : Blo 1217426 1827491 := bstep (se 1 (by rfl) ⟨1370618, by rfl⟩ : syracuseStep 1827491 = 2741237) B2741237
theorem B2933425 : Blo 1217426 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B1827521 : Blo 1217426 1827521 := bstep (se 2 (by rfl) ⟨685320, by rfl⟩ : syracuseStep 1827521 = 1370641) B1370641
theorem B3293905 : Blo 1217426 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B1827539 : Blo 1217426 1827539 := bstep (se 1 (by rfl) ⟨1370654, by rfl⟩ : syracuseStep 1827539 = 2741309) B2741309
theorem B1827569 : Blo 1217426 1827569 := bstep (se 2 (by rfl) ⟨685338, by rfl⟩ : syracuseStep 1827569 = 1370677) B1370677
theorem B2056961 : Blo 1217426 2056961 := bstep (se 2 (by rfl) ⟨771360, by rfl⟩ : syracuseStep 2056961 = 1542721) B1542721
theorem B1827587 : Blo 1217426 1827587 := bstep (se 1 (by rfl) ⟨1370690, by rfl⟩ : syracuseStep 1827587 = 2741381) B2741381
theorem B1540883 : Blo 1217426 1540883 := bstep (se 1 (by rfl) ⟨1155662, by rfl⟩ : syracuseStep 1540883 = 2311325) B2311325
theorem B1827617 : Blo 1217426 1827617 := bstep (se 2 (by rfl) ⟨685356, by rfl⟩ : syracuseStep 1827617 = 1370713) B1370713
theorem B5202737 : Blo 1217426 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B1827635 : Blo 1217426 1827635 := bstep (se 1 (by rfl) ⟨1370726, by rfl⟩ : syracuseStep 1827635 = 2741453) B2741453
theorem B1827665 : Blo 1217426 1827665 := bstep (se 2 (by rfl) ⟨685374, by rfl⟩ : syracuseStep 1827665 = 1370749) B1370749
theorem B4113233 : Blo 1217426 4113233 := bstep (se 2 (by rfl) ⟨1542462, by rfl⟩ : syracuseStep 4113233 = 3084925) B3084925
theorem B1827683 : Blo 1217426 1827683 := bstep (se 1 (by rfl) ⟨1370762, by rfl⟩ : syracuseStep 1827683 = 2741525) B2741525
theorem B15827825 : Blo 1217426 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B1827713 : Blo 1217426 1827713 := bstep (se 2 (by rfl) ⟨685392, by rfl⟩ : syracuseStep 1827713 = 1370785) B1370785
theorem B2057089 : Blo 1217426 2057089 := bstep (se 2 (by rfl) ⟨771408, by rfl⟩ : syracuseStep 2057089 = 1542817) B1542817
theorem B6939533 : Blo 1217426 6939533 := bstep (se 3 (by rfl) ⟨1301162, by rfl⟩ : syracuseStep 6939533 = 2602325) B2602325
theorem B1827731 : Blo 1217426 1827731 := bstep (se 1 (by rfl) ⟨1370798, by rfl⟩ : syracuseStep 1827731 = 2741597) B2741597
theorem B2057123 : Blo 1217426 2057123 := bstep (se 1 (by rfl) ⟨1542842, by rfl⟩ : syracuseStep 2057123 = 3085685) B3085685
theorem B1827761 : Blo 1217426 1827761 := bstep (se 2 (by rfl) ⟨685410, by rfl⟩ : syracuseStep 1827761 = 1370821) B1370821
theorem B1827779 : Blo 1217426 1827779 := bstep (se 1 (by rfl) ⟨1370834, by rfl⟩ : syracuseStep 1827779 = 2741669) B2741669
theorem B52667333 : Blo 1217426 52667333 := bstep (se 4 (by rfl) ⟨4937562, by rfl⟩ : syracuseStep 52667333 = 9875125) B9875125
theorem B1827809 : Blo 1217426 1827809 := bstep (se 2 (by rfl) ⟨685428, by rfl⟩ : syracuseStep 1827809 = 1370857) B1370857
theorem B1827827 : Blo 1217426 1827827 := bstep (se 1 (by rfl) ⟨1370870, by rfl⟩ : syracuseStep 1827827 = 2741741) B2741741
theorem B1827857 : Blo 1217426 1827857 := bstep (se 2 (by rfl) ⟨685446, by rfl⟩ : syracuseStep 1827857 = 1370893) B1370893
theorem B1827875 : Blo 1217426 1827875 := bstep (se 1 (by rfl) ⟨1370906, by rfl⟩ : syracuseStep 1827875 = 2741813) B2741813
theorem B2057251 : Blo 1217426 2057251 := bstep (se 1 (by rfl) ⟨1542938, by rfl⟩ : syracuseStep 2057251 = 3085877) B3085877
theorem B1827905 : Blo 1217426 1827905 := bstep (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) B1370929
theorem B2311249 : Blo 1217426 2311249 := bstep (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) B1733437
theorem B1827923 : Blo 1217426 1827923 := bstep (se 1 (by rfl) ⟨1370942, by rfl⟩ : syracuseStep 1827923 = 2741885) B2741885
theorem B1827953 : Blo 1217426 1827953 := bstep (se 2 (by rfl) ⟨685482, by rfl⟩ : syracuseStep 1827953 = 1370965) B1370965
theorem B1827971 : Blo 1217426 1827971 := bstep (se 1 (by rfl) ⟨1370978, by rfl⟩ : syracuseStep 1827971 = 2741957) B2741957
theorem B10413197 : Blo 1217426 10413197 := bstep (se 3 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 10413197 = 3904949) B3904949
theorem B1828001 : Blo 1217426 1828001 := bstep (se 2 (by rfl) ⟨685500, by rfl⟩ : syracuseStep 1828001 = 1371001) B1371001
theorem B2057393 : Blo 1217426 2057393 := bstep (se 2 (by rfl) ⟨771522, by rfl⟩ : syracuseStep 2057393 = 1543045) B1543045
theorem B1828019 : Blo 1217426 1828019 := bstep (se 1 (by rfl) ⟨1371014, by rfl⟩ : syracuseStep 1828019 = 2742029) B2742029
theorem B1828049 : Blo 1217426 1828049 := bstep (se 2 (by rfl) ⟨685518, by rfl⟩ : syracuseStep 1828049 = 1371037) B1371037
theorem B1828067 : Blo 1217426 1828067 := bstep (se 1 (by rfl) ⟨1371050, by rfl⟩ : syracuseStep 1828067 = 2742101) B2742101
theorem B2311409 : Blo 1217426 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B1828097 : Blo 1217426 1828097 := bstep (se 2 (by rfl) ⟨685536, by rfl⟩ : syracuseStep 1828097 = 1371073) B1371073
theorem B1828115 : Blo 1217426 1828115 := bstep (se 1 (by rfl) ⟨1371086, by rfl⟩ : syracuseStep 1828115 = 2742173) B2742173
theorem B1828145 : Blo 1217426 1828145 := bstep (se 2 (by rfl) ⟨685554, by rfl⟩ : syracuseStep 1828145 = 1371109) B1371109
theorem B2057521 : Blo 1217426 2057521 := bstep (se 2 (by rfl) ⟨771570, by rfl⟩ : syracuseStep 2057521 = 1543141) B1543141
theorem B1828163 : Blo 1217426 1828163 := bstep (se 1 (by rfl) ⟨1371122, by rfl⟩ : syracuseStep 1828163 = 2742245) B2742245
theorem B2057555 : Blo 1217426 2057555 := bstep (se 1 (by rfl) ⟨1543166, by rfl⟩ : syracuseStep 2057555 = 3086333) B3086333
theorem B1828193 : Blo 1217426 1828193 := bstep (se 2 (by rfl) ⟨685572, by rfl⟩ : syracuseStep 1828193 = 1371145) B1371145
theorem B4113773 : Blo 1217426 4113773 := bstep (se 3 (by rfl) ⟨771332, by rfl⟩ : syracuseStep 4113773 = 1542665) B1542665
theorem B1828211 : Blo 1217426 1828211 := bstep (se 1 (by rfl) ⟨1371158, by rfl⟩ : syracuseStep 1828211 = 2742317) B2742317
theorem B1828241 : Blo 1217426 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B1951123 : Blo 1217426 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B3081635 : Blo 1217426 3081635 := bstep (se 1 (by rfl) ⟨2311226, by rfl⟩ : syracuseStep 3081635 = 4622453) B4622453
theorem B1828259 : Blo 1217426 1828259 := bstep (se 1 (by rfl) ⟨1371194, by rfl⟩ : syracuseStep 1828259 = 2742389) B2742389
theorem B4113827 : Blo 1217426 4113827 := bstep (se 1 (by rfl) ⟨3085370, by rfl⟩ : syracuseStep 4113827 = 6170741) B6170741
theorem B2926001 : Blo 1217426 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B1828289 : Blo 1217426 1828289 := bstep (se 2 (by rfl) ⟨685608, by rfl⟩ : syracuseStep 1828289 = 1371217) B1371217
theorem B1541587 : Blo 1217426 1541587 := bstep (se 1 (by rfl) ⟨1156190, by rfl⟩ : syracuseStep 1541587 = 2312381) B2312381
theorem B1828307 : Blo 1217426 1828307 := bstep (se 1 (by rfl) ⟨1371230, by rfl⟩ : syracuseStep 1828307 = 2742461) B2742461
theorem B2057683 : Blo 1217426 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B1828337 : Blo 1217426 1828337 := bstep (se 2 (by rfl) ⟨685626, by rfl⟩ : syracuseStep 1828337 = 1371253) B1371253
theorem B1828355 : Blo 1217426 1828355 := bstep (se 1 (by rfl) ⟨1371266, by rfl⟩ : syracuseStep 1828355 = 2742533) B2742533
theorem B1828385 : Blo 1217426 1828385 := bstep (se 2 (by rfl) ⟨685644, by rfl⟩ : syracuseStep 1828385 = 1371289) B1371289
theorem B1541683 : Blo 1217426 1541683 := bstep (se 1 (by rfl) ⟨1156262, by rfl⟩ : syracuseStep 1541683 = 2312525) B2312525
theorem B1369651 : Blo 1217426 1369651 := bstep (se 1 (by rfl) ⟨1027238, by rfl⟩ : syracuseStep 1369651 = 2054477) B2054477
theorem B1828403 : Blo 1217426 1828403 := bstep (se 1 (by rfl) ⟨1371302, by rfl⟩ : syracuseStep 1828403 = 2742605) B2742605
theorem B1828433 : Blo 1217426 1828433 := bstep (se 2 (by rfl) ⟨685662, by rfl⟩ : syracuseStep 1828433 = 1371325) B1371325
theorem B11708003 : Blo 1217426 11708003 := bstep (se 1 (by rfl) ⟨8781002, by rfl⟩ : syracuseStep 11708003 = 17562005) B17562005
theorem B3081827 : Blo 1217426 3081827 := bstep (se 1 (by rfl) ⟨2311370, by rfl⟩ : syracuseStep 3081827 = 4622741) B4622741
theorem B1828451 : Blo 1217426 1828451 := bstep (se 1 (by rfl) ⟨1371338, by rfl⟩ : syracuseStep 1828451 = 2742677) B2742677
theorem B4941425 : Blo 1217426 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B1828481 : Blo 1217426 1828481 := bstep (se 2 (by rfl) ⟨685680, by rfl⟩ : syracuseStep 1828481 = 1371361) B1371361
theorem B2311811 : Blo 1217426 2311811 := bstep (se 1 (by rfl) ⟨1733858, by rfl⟩ : syracuseStep 2311811 = 3467717) B3467717
theorem B1828499 : Blo 1217426 1828499 := bstep (se 1 (by rfl) ⟨1371374, by rfl⟩ : syracuseStep 1828499 = 2742749) B2742749
theorem B4114097 : Blo 1217426 4114097 := bstep (se 2 (by rfl) ⟨1542786, by rfl⟩ : syracuseStep 4114097 = 3085573) B3085573
theorem B1828529 : Blo 1217426 1828529 := bstep (se 2 (by rfl) ⟨685698, by rfl⟩ : syracuseStep 1828529 = 1371397) B1371397
theorem B1369795 : Blo 1217426 1369795 := bstep (se 1 (by rfl) ⟨1027346, by rfl⟩ : syracuseStep 1369795 = 2054693) B2054693
theorem B1828547 : Blo 1217426 1828547 := bstep (se 1 (by rfl) ⟨1371410, by rfl⟩ : syracuseStep 1828547 = 2742821) B2742821
theorem B7513805 : Blo 1217426 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B1828577 : Blo 1217426 1828577 := bstep (se 2 (by rfl) ⟨685716, by rfl⟩ : syracuseStep 1828577 = 1371433) B1371433
theorem B1828595 : Blo 1217426 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B1828625 : Blo 1217426 1828625 := bstep (se 2 (by rfl) ⟨685734, by rfl⟩ : syracuseStep 1828625 = 1371469) B1371469
theorem B1828643 : Blo 1217426 1828643 := bstep (se 1 (by rfl) ⟨1371482, by rfl⟩ : syracuseStep 1828643 = 2742965) B2742965
theorem B6170417 : Blo 1217426 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B1877825 : Blo 1217426 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B1828673 : Blo 1217426 1828673 := bstep (se 2 (by rfl) ⟨685752, by rfl⟩ : syracuseStep 1828673 = 1371505) B1371505
theorem B4171601 : Blo 1217426 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B1369939 : Blo 1217426 1369939 := bstep (se 1 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 1369939 = 2054909) B2054909
theorem B1828691 : Blo 1217426 1828691 := bstep (se 1 (by rfl) ⟨1371518, by rfl⟩ : syracuseStep 1828691 = 2743037) B2743037
theorem B1828721 : Blo 1217426 1828721 := bstep (se 2 (by rfl) ⟨685770, by rfl⟩ : syracuseStep 1828721 = 1371541) B1371541
theorem B1828739 : Blo 1217426 1828739 := bstep (se 1 (by rfl) ⟨1371554, by rfl⟩ : syracuseStep 1828739 = 2743109) B2743109
theorem B1828769 : Blo 1217426 1828769 := bstep (se 2 (by rfl) ⟨685788, by rfl⟩ : syracuseStep 1828769 = 1371577) B1371577
theorem B1828787 : Blo 1217426 1828787 := bstep (se 1 (by rfl) ⟨1371590, by rfl⟩ : syracuseStep 1828787 = 2743181) B2743181
theorem B1828817 : Blo 1217426 1828817 := bstep (se 2 (by rfl) ⟨685806, by rfl⟩ : syracuseStep 1828817 = 1371613) B1371613
theorem B1370083 : Blo 1217426 1370083 := bstep (se 1 (by rfl) ⟨1027562, by rfl⟩ : syracuseStep 1370083 = 2055125) B2055125
theorem B1828835 : Blo 1217426 1828835 := bstep (se 1 (by rfl) ⟨1371626, by rfl⟩ : syracuseStep 1828835 = 2743253) B2743253
theorem B1828865 : Blo 1217426 1828865 := bstep (se 2 (by rfl) ⟨685824, by rfl⟩ : syracuseStep 1828865 = 1371649) B1371649
theorem B1828883 : Blo 1217426 1828883 := bstep (se 1 (by rfl) ⟨1371662, by rfl⟩ : syracuseStep 1828883 = 2743325) B2743325
theorem B1542179 : Blo 1217426 1542179 := bstep (se 1 (by rfl) ⟨1156634, by rfl⟩ : syracuseStep 1542179 = 2313269) B2313269
theorem B1828913 : Blo 1217426 1828913 := bstep (se 2 (by rfl) ⟨685842, by rfl⟩ : syracuseStep 1828913 = 1371685) B1371685
theorem B1951795 : Blo 1217426 1951795 := bstep (se 1 (by rfl) ⟨1463846, by rfl⟩ : syracuseStep 1951795 = 2927693) B2927693
theorem B1828931 : Blo 1217426 1828931 := bstep (se 1 (by rfl) ⟨1371698, by rfl⟩ : syracuseStep 1828931 = 2743397) B2743397
theorem B1828961 : Blo 1217426 1828961 := bstep (se 2 (by rfl) ⟨685860, by rfl⟩ : syracuseStep 1828961 = 1371721) B1371721
theorem B1370227 : Blo 1217426 1370227 := bstep (se 1 (by rfl) ⟨1027670, by rfl⟩ : syracuseStep 1370227 = 2055341) B2055341
theorem B1828979 : Blo 1217426 1828979 := bstep (se 1 (by rfl) ⟨1371734, by rfl⟩ : syracuseStep 1828979 = 2743469) B2743469
theorem B1829009 : Blo 1217426 1829009 := bstep (se 2 (by rfl) ⟨685878, by rfl⟩ : syracuseStep 1829009 = 1371757) B1371757
theorem B1829027 : Blo 1217426 1829027 := bstep (se 1 (by rfl) ⟨1371770, by rfl⟩ : syracuseStep 1829027 = 2743541) B2743541
theorem B1829057 : Blo 1217426 1829057 := bstep (se 2 (by rfl) ⟨685896, by rfl⟩ : syracuseStep 1829057 = 1371793) B1371793
theorem B4114637 : Blo 1217426 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B1829075 : Blo 1217426 1829075 := bstep (se 1 (by rfl) ⟨1371806, by rfl⟩ : syracuseStep 1829075 = 2743613) B2743613
theorem B1829105 : Blo 1217426 1829105 := bstep (se 2 (by rfl) ⟨685914, by rfl⟩ : syracuseStep 1829105 = 1371829) B1371829
theorem B1370371 : Blo 1217426 1370371 := bstep (se 1 (by rfl) ⟨1027778, by rfl⟩ : syracuseStep 1370371 = 2055557) B2055557
theorem B4114691 : Blo 1217426 4114691 := bstep (se 1 (by rfl) ⟨3086018, by rfl⟩ : syracuseStep 4114691 = 6172037) B6172037
theorem B1829123 : Blo 1217426 1829123 := bstep (se 1 (by rfl) ⟨1371842, by rfl⟩ : syracuseStep 1829123 = 2743685) B2743685
theorem B3467569 : Blo 1217426 3467569 := bstep (se 2 (by rfl) ⟨1300338, by rfl⟩ : syracuseStep 3467569 = 2600677) B2600677
theorem B3901745 : Blo 1217426 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B5343565 : Blo 1217426 5343565 := bstep (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) B2003837
theorem B1853795 : Blo 1217426 1853795 := bstep (se 1 (by rfl) ⟨1390346, by rfl⟩ : syracuseStep 1853795 = 2780693) B2780693
theorem B1370515 : Blo 1217426 1370515 := bstep (se 1 (by rfl) ⟨1027886, by rfl⟩ : syracuseStep 1370515 = 2055773) B2055773
theorem B1952257 : Blo 1217426 1952257 := bstep (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) B1464193
theorem B2312707 : Blo 1217426 2312707 := bstep (se 1 (by rfl) ⟨1734530, by rfl⟩ : syracuseStep 2312707 = 3469061) B3469061
theorem B3082769 : Blo 1217426 3082769 := bstep (se 2 (by rfl) ⟨1156038, by rfl⟩ : syracuseStep 3082769 = 2312077) B2312077
theorem B4114961 : Blo 1217426 4114961 := bstep (se 2 (by rfl) ⟨1543110, by rfl⟩ : syracuseStep 4114961 = 3086221) B3086221
theorem B1370659 : Blo 1217426 1370659 := bstep (se 1 (by rfl) ⟨1027994, by rfl⟩ : syracuseStep 1370659 = 2055989) B2055989
theorem B1878563 : Blo 1217426 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B3467843 : Blo 1217426 3467843 := bstep (se 1 (by rfl) ⟨2600882, by rfl⟩ : syracuseStep 3467843 = 5201765) B5201765
theorem B3082819 : Blo 1217426 3082819 := bstep (se 1 (by rfl) ⟨2312114, by rfl⟩ : syracuseStep 3082819 = 4624229) B4624229
theorem B2779715 : Blo 1217426 2779715 := bstep (se 1 (by rfl) ⟨2084786, by rfl⟩ : syracuseStep 2779715 = 4169573) B4169573
theorem B2345539 : Blo 1217426 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B1952353 : Blo 1217426 1952353 := bstep (se 2 (by rfl) ⟨732132, by rfl⟩ : syracuseStep 1952353 = 1464265) B1464265
theorem B2468483 : Blo 1217426 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B11864717 : Blo 1217426 11864717 := bstep (se 3 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 11864717 = 4449269) B4449269
theorem B2312867 : Blo 1217426 2312867 := bstep (se 1 (by rfl) ⟨1734650, by rfl⟩ : syracuseStep 2312867 = 3469301) B3469301
theorem B1370803 : Blo 1217426 1370803 := bstep (se 1 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 1370803 = 2056205) B2056205
theorem B3082961 : Blo 1217426 3082961 := bstep (se 2 (by rfl) ⟨1156110, by rfl⟩ : syracuseStep 3082961 = 2312221) B2312221
theorem B1542883 : Blo 1217426 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B5851889 : Blo 1217426 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B1952513 : Blo 1217426 1952513 := bstep (se 2 (by rfl) ⟨732192, by rfl⟩ : syracuseStep 1952513 = 1464385) B1464385
theorem B3468035 : Blo 1217426 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1370947 : Blo 1217426 1370947 := bstep (se 1 (by rfl) ⟨1028210, by rfl⟩ : syracuseStep 1370947 = 2056421) B2056421
theorem B1542979 : Blo 1217426 1542979 := bstep (se 1 (by rfl) ⟨1157234, by rfl⟩ : syracuseStep 1542979 = 2314469) B2314469
theorem B9030541 : Blo 1217426 9030541 := bstep (se 3 (by rfl) ⟨1693226, by rfl⟩ : syracuseStep 9030541 = 3386453) B3386453
theorem B1371091 : Blo 1217426 1371091 := bstep (se 1 (by rfl) ⟨1028318, by rfl⟩ : syracuseStep 1371091 = 2056637) B2056637
theorem B4115501 : Blo 1217426 4115501 := bstep (se 3 (by rfl) ⟨771656, by rfl⟩ : syracuseStep 4115501 = 1543313) B1543313
theorem B1371235 : Blo 1217426 1371235 := bstep (se 1 (by rfl) ⟨1028426, by rfl⟩ : syracuseStep 1371235 = 2056853) B2056853
theorem B4115555 : Blo 1217426 4115555 := bstep (se 1 (by rfl) ⟨3086666, by rfl⟩ : syracuseStep 4115555 = 6173333) B6173333
theorem B9251981 : Blo 1217426 9251981 := bstep (se 3 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 9251981 = 3469493) B3469493
theorem B3124369 : Blo 1217426 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B6933701 : Blo 1217426 6933701 := bstep (se 4 (by rfl) ⟨650034, by rfl⟩ : syracuseStep 6933701 = 1300069) B1300069
theorem B5205197 : Blo 1217426 5205197 := bstep (se 3 (by rfl) ⟨975974, by rfl⟩ : syracuseStep 5205197 = 1951949) B1951949
theorem B6171875 : Blo 1217426 6171875 := bstep (se 1 (by rfl) ⟨4628906, by rfl⟩ : syracuseStep 6171875 = 9257813) B9257813
theorem B1371379 : Blo 1217426 1371379 := bstep (se 1 (by rfl) ⟨1028534, by rfl⟩ : syracuseStep 1371379 = 2057069) B2057069
theorem B2739473 : Blo 1217426 2739473 := bstep (se 2 (by rfl) ⟨1027302, by rfl⟩ : syracuseStep 2739473 = 2054605) B2054605
theorem B2739491 : Blo 1217426 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B1371523 : Blo 1217426 1371523 := bstep (se 1 (by rfl) ⟨1028642, by rfl⟩ : syracuseStep 1371523 = 2057285) B2057285
theorem B2969041 : Blo 1217426 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B10415587 : Blo 1217426 10415587 := bstep (se 1 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 10415587 = 15623381) B15623381
theorem B6581773 : Blo 1217426 6581773 := bstep (se 3 (by rfl) ⟨1234082, by rfl⟩ : syracuseStep 6581773 = 2468165) B2468165
theorem B1371667 : Blo 1217426 1371667 := bstep (se 1 (by rfl) ⟨1028750, by rfl⟩ : syracuseStep 1371667 = 2057501) B2057501
theorem B5205539 : Blo 1217426 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B3517987 : Blo 1217426 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B3468845 : Blo 1217426 3468845 := bstep (se 3 (by rfl) ⟨650408, by rfl⟩ : syracuseStep 3468845 = 1300817) B1300817
theorem B2739761 : Blo 1217426 2739761 := bstep (se 2 (by rfl) ⟨1027410, by rfl⟩ : syracuseStep 2739761 = 2054821) B2054821
theorem B2739779 : Blo 1217426 2739779 := bstep (se 1 (by rfl) ⟨2054834, by rfl⟩ : syracuseStep 2739779 = 4109669) B4109669
theorem B6934157 : Blo 1217426 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B4943501 : Blo 1217426 4943501 := bstep (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) B1853813
theorem B1371811 : Blo 1217426 1371811 := bstep (se 1 (by rfl) ⟨1028858, by rfl⟩ : syracuseStep 1371811 = 2057717) B2057717
theorem B3083953 : Blo 1217426 3083953 := bstep (se 2 (by rfl) ⟨1156482, by rfl⟩ : syracuseStep 3083953 = 2312965) B2312965
theorem B2313937 : Blo 1217426 2313937 := bstep (se 2 (by rfl) ⟨867726, by rfl⟩ : syracuseStep 2313937 = 1735453) B1735453
theorem B3469027 : Blo 1217426 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B20811491 : Blo 1217426 20811491 := bstep (se 1 (by rfl) ⟨15608618, by rfl⟩ : syracuseStep 20811491 = 31217237) B31217237
theorem B6942449 : Blo 1217426 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B2600753 : Blo 1217426 2600753 := bstep (se 2 (by rfl) ⟨975282, by rfl⟩ : syracuseStep 2600753 = 1950565) B1950565
theorem B5853005 : Blo 1217426 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2740049 : Blo 1217426 2740049 := bstep (se 2 (by rfl) ⟨1027518, by rfl⟩ : syracuseStep 2740049 = 2055037) B2055037
theorem B3338065 : Blo 1217426 3338065 := bstep (se 2 (by rfl) ⟨1251774, by rfl⟩ : syracuseStep 3338065 = 2503549) B2503549
theorem B2740067 : Blo 1217426 2740067 := bstep (se 1 (by rfl) ⟨2055050, by rfl⟩ : syracuseStep 2740067 = 4110101) B4110101
theorem B3084227 : Blo 1217426 3084227 := bstep (se 1 (by rfl) ⟨2313170, by rfl⟩ : syracuseStep 3084227 = 4626341) B4626341
theorem B7802851 : Blo 1217426 7802851 := bstep (se 1 (by rfl) ⟨5852138, by rfl⟩ : syracuseStep 7802851 = 11704277) B11704277
theorem B14815217 : Blo 1217426 14815217 := bstep (se 2 (by rfl) ⟨5555706, by rfl⟩ : syracuseStep 14815217 = 11111413) B11111413
theorem B4624397 : Blo 1217426 4624397 := bstep (se 3 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 4624397 = 1734149) B1734149
theorem B6172685 : Blo 1217426 6172685 := bstep (se 3 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 6172685 = 2314757) B2314757
theorem B5558321 : Blo 1217426 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B2740337 : Blo 1217426 2740337 := bstep (se 2 (by rfl) ⟨1027626, by rfl⟩ : syracuseStep 2740337 = 2055253) B2055253
theorem B2740355 : Blo 1217426 2740355 := bstep (se 1 (by rfl) ⟨2055266, by rfl⟩ : syracuseStep 2740355 = 4110533) B4110533
theorem B3084419 : Blo 1217426 3084419 := bstep (se 1 (by rfl) ⟨2313314, by rfl⟩ : syracuseStep 3084419 = 4626629) B4626629
theorem B3469517 : Blo 1217426 3469517 := bstep (se 3 (by rfl) ⟨650534, by rfl⟩ : syracuseStep 3469517 = 1301069) B1301069
theorem B1978609 : Blo 1217426 1978609 := bstep (se 2 (by rfl) ⟨741978, by rfl⟩ : syracuseStep 1978609 = 1483957) B1483957
theorem B12505357 : Blo 1217426 12505357 := bstep (se 3 (by rfl) ⟨2344754, by rfl⟩ : syracuseStep 12505357 = 4689509) B4689509
theorem B3756401 : Blo 1217426 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B12513649 : Blo 1217426 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B2740625 : Blo 1217426 2740625 := bstep (se 2 (by rfl) ⟨1027734, by rfl⟩ : syracuseStep 2740625 = 2055469) B2055469
theorem B2740643 : Blo 1217426 2740643 := bstep (se 1 (by rfl) ⟨2055482, by rfl⟩ : syracuseStep 2740643 = 4110965) B4110965
theorem B4108913 : Blo 1217426 4108913 := bstep (se 2 (by rfl) ⟨1540842, by rfl⟩ : syracuseStep 4108913 = 3081685) B3081685
theorem B2740913 : Blo 1217426 2740913 := bstep (se 2 (by rfl) ⟨1027842, by rfl⟩ : syracuseStep 2740913 = 2055685) B2055685
theorem B1462963 : Blo 1217426 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B2740931 : Blo 1217426 2740931 := bstep (se 1 (by rfl) ⟨2055698, by rfl⟩ : syracuseStep 2740931 = 4111397) B4111397
theorem B3904205 : Blo 1217426 3904205 := bstep (se 3 (by rfl) ⟨732038, by rfl⟩ : syracuseStep 3904205 = 1464077) B1464077
theorem B6165233 : Blo 1217426 6165233 := bstep (se 2 (by rfl) ⟨2311962, by rfl⟩ : syracuseStep 6165233 = 4623925) B4623925
theorem B2314993 : Blo 1217426 2314993 := bstep (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) B1736245
theorem B1463059 : Blo 1217426 1463059 := bstep (se 1 (by rfl) ⟨1097294, by rfl⟩ : syracuseStep 1463059 = 2194589) B2194589
theorem B4625201 : Blo 1217426 4625201 := bstep (se 2 (by rfl) ⟨1734450, by rfl⟩ : syracuseStep 4625201 = 3468901) B3468901
theorem B2085745 : Blo 1217426 2085745 := bstep (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) B1564309
theorem B1217427 : Blo 1217426 1217427 := bstep (se 1 (by rfl) ⟨913070, by rfl⟩ : syracuseStep 1217427 = 1826141) B1826141
theorem B1217443 : Blo 1217426 1217443 := bstep (se 1 (by rfl) ⟨913082, by rfl⟩ : syracuseStep 1217443 = 1826165) B1826165
theorem B1217459 : Blo 1217426 1217459 := bstep (se 1 (by rfl) ⟨913094, by rfl⟩ : syracuseStep 1217459 = 1826189) B1826189
theorem B14062517 : Blo 1217426 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B1217475 : Blo 1217426 1217475 := bstep (se 1 (by rfl) ⟨913106, by rfl⟩ : syracuseStep 1217475 = 1826213) B1826213
theorem B2741201 : Blo 1217426 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B1217491 : Blo 1217426 1217491 := bstep (se 1 (by rfl) ⟨913118, by rfl⟩ : syracuseStep 1217491 = 1826237) B1826237
theorem B1217507 : Blo 1217426 1217507 := bstep (se 1 (by rfl) ⟨913130, by rfl⟩ : syracuseStep 1217507 = 1826261) B1826261
theorem B2741219 : Blo 1217426 2741219 := bstep (se 1 (by rfl) ⟨2055914, by rfl⟩ : syracuseStep 2741219 = 4111829) B4111829
theorem B2470883 : Blo 1217426 2470883 := bstep (se 1 (by rfl) ⟨1853162, by rfl⟩ : syracuseStep 2470883 = 3706325) B3706325
theorem B1217523 : Blo 1217426 1217523 := bstep (se 1 (by rfl) ⟨913142, by rfl⟩ : syracuseStep 1217523 = 1826285) B1826285
theorem B1217539 : Blo 1217426 1217539 := bstep (se 1 (by rfl) ⟨913154, by rfl⟩ : syracuseStep 1217539 = 1826309) B1826309
theorem B7812101 : Blo 1217426 7812101 := bstep (se 4 (by rfl) ⟨732384, by rfl⟩ : syracuseStep 7812101 = 1464769) B1464769
theorem B1217555 : Blo 1217426 1217555 := bstep (se 1 (by rfl) ⟨913166, by rfl⟩ : syracuseStep 1217555 = 1826333) B1826333
theorem B1733665 : Blo 1217426 1733665 := bstep (se 2 (by rfl) ⟨650124, by rfl⟩ : syracuseStep 1733665 = 1300249) B1300249
theorem B1217571 : Blo 1217426 1217571 := bstep (se 1 (by rfl) ⟨913178, by rfl⟩ : syracuseStep 1217571 = 1826357) B1826357
theorem B3519533 : Blo 1217426 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B3085361 : Blo 1217426 3085361 := bstep (se 2 (by rfl) ⟨1157010, by rfl⟩ : syracuseStep 3085361 = 2314021) B2314021
theorem B1217587 : Blo 1217426 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B1463347 : Blo 1217426 1463347 := bstep (se 1 (by rfl) ⟨1097510, by rfl⟩ : syracuseStep 1463347 = 2195021) B2195021
theorem B1217603 : Blo 1217426 1217603 := bstep (se 1 (by rfl) ⟨913202, by rfl⟩ : syracuseStep 1217603 = 1826405) B1826405
theorem B1217619 : Blo 1217426 1217619 := bstep (se 1 (by rfl) ⟨913214, by rfl⟩ : syracuseStep 1217619 = 1826429) B1826429
theorem B1217635 : Blo 1217426 1217635 := bstep (se 1 (by rfl) ⟨913226, by rfl⟩ : syracuseStep 1217635 = 1826453) B1826453
theorem B3085411 : Blo 1217426 3085411 := bstep (se 1 (by rfl) ⟨2314058, by rfl⟩ : syracuseStep 3085411 = 4628117) B4628117
theorem B1217651 : Blo 1217426 1217651 := bstep (se 1 (by rfl) ⟨913238, by rfl⟩ : syracuseStep 1217651 = 1826477) B1826477
theorem B1217667 : Blo 1217426 1217667 := bstep (se 1 (by rfl) ⟨913250, by rfl⟩ : syracuseStep 1217667 = 1826501) B1826501
theorem B4109453 : Blo 1217426 4109453 := bstep (se 3 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 4109453 = 1541045) B1541045
theorem B5854349 : Blo 1217426 5854349 := bstep (se 3 (by rfl) ⟨1097690, by rfl⟩ : syracuseStep 5854349 = 2195381) B2195381
theorem B1217683 : Blo 1217426 1217683 := bstep (se 1 (by rfl) ⟨913262, by rfl⟩ : syracuseStep 1217683 = 1826525) B1826525
theorem B1217699 : Blo 1217426 1217699 := bstep (se 1 (by rfl) ⟨913274, by rfl⟩ : syracuseStep 1217699 = 1826549) B1826549
theorem B6943907 : Blo 1217426 6943907 := bstep (se 1 (by rfl) ⟨5207930, by rfl⟩ : syracuseStep 6943907 = 10415861) B10415861
theorem B1217715 : Blo 1217426 1217715 := bstep (se 1 (by rfl) ⟨913286, by rfl⟩ : syracuseStep 1217715 = 1826573) B1826573
theorem B4109507 : Blo 1217426 4109507 := bstep (se 1 (by rfl) ⟨3082130, by rfl⟩ : syracuseStep 4109507 = 6164261) B6164261
theorem B1217731 : Blo 1217426 1217731 := bstep (se 1 (by rfl) ⟨913298, by rfl⟩ : syracuseStep 1217731 = 1826597) B1826597
theorem B3519683 : Blo 1217426 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B1217747 : Blo 1217426 1217747 := bstep (se 1 (by rfl) ⟨913310, by rfl⟩ : syracuseStep 1217747 = 1826621) B1826621
theorem B1217763 : Blo 1217426 1217763 := bstep (se 1 (by rfl) ⟨913322, by rfl⟩ : syracuseStep 1217763 = 1826645) B1826645
theorem B2741489 : Blo 1217426 2741489 := bstep (se 2 (by rfl) ⟨1028058, by rfl⟩ : syracuseStep 2741489 = 2056117) B2056117
theorem B3085553 : Blo 1217426 3085553 := bstep (se 2 (by rfl) ⟨1157082, by rfl⟩ : syracuseStep 3085553 = 2314165) B2314165
theorem B1217779 : Blo 1217426 1217779 := bstep (se 1 (by rfl) ⟨913334, by rfl⟩ : syracuseStep 1217779 = 1826669) B1826669
theorem B1463539 : Blo 1217426 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B1217795 : Blo 1217426 1217795 := bstep (se 1 (by rfl) ⟨913346, by rfl⟩ : syracuseStep 1217795 = 1826693) B1826693
theorem B2741507 : Blo 1217426 2741507 := bstep (se 1 (by rfl) ⟨2056130, by rfl⟩ : syracuseStep 2741507 = 4112261) B4112261
theorem B1217811 : Blo 1217426 1217811 := bstep (se 1 (by rfl) ⟨913358, by rfl⟩ : syracuseStep 1217811 = 1826717) B1826717
theorem B1217827 : Blo 1217426 1217827 := bstep (se 1 (by rfl) ⟨913370, by rfl⟩ : syracuseStep 1217827 = 1826741) B1826741
theorem B1217843 : Blo 1217426 1217843 := bstep (se 1 (by rfl) ⟨913382, by rfl⟩ : syracuseStep 1217843 = 1826765) B1826765
theorem B1217859 : Blo 1217426 1217859 := bstep (se 1 (by rfl) ⟨913394, by rfl⟩ : syracuseStep 1217859 = 1826789) B1826789
theorem B1217875 : Blo 1217426 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B4388195 : Blo 1217426 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B1217891 : Blo 1217426 1217891 := bstep (se 1 (by rfl) ⟨913418, by rfl⟩ : syracuseStep 1217891 = 1826837) B1826837
theorem B3470701 : Blo 1217426 3470701 := bstep (se 3 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 3470701 = 1301513) B1301513
theorem B1217907 : Blo 1217426 1217907 := bstep (se 1 (by rfl) ⟨913430, by rfl⟩ : syracuseStep 1217907 = 1826861) B1826861
theorem B1217923 : Blo 1217426 1217923 := bstep (se 1 (by rfl) ⟨913442, by rfl⟩ : syracuseStep 1217923 = 1826885) B1826885
theorem B1217939 : Blo 1217426 1217939 := bstep (se 1 (by rfl) ⟨913454, by rfl⟩ : syracuseStep 1217939 = 1826909) B1826909
theorem B1217955 : Blo 1217426 1217955 := bstep (se 1 (by rfl) ⟨913466, by rfl⟩ : syracuseStep 1217955 = 1826933) B1826933
theorem B1217971 : Blo 1217426 1217971 := bstep (se 1 (by rfl) ⟨913478, by rfl⟩ : syracuseStep 1217971 = 1826957) B1826957
theorem B1217987 : Blo 1217426 1217987 := bstep (se 1 (by rfl) ⟨913490, by rfl⟩ : syracuseStep 1217987 = 1826981) B1826981
theorem B9246149 : Blo 1217426 9246149 := bstep (se 4 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 9246149 = 1733653) B1733653
theorem B4625869 : Blo 1217426 4625869 := bstep (se 3 (by rfl) ⟨867350, by rfl⟩ : syracuseStep 4625869 = 1734701) B1734701
theorem B4109777 : Blo 1217426 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B2471377 : Blo 1217426 2471377 := bstep (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) B1853533
theorem B1218003 : Blo 1217426 1218003 := bstep (se 1 (by rfl) ⟨913502, by rfl⟩ : syracuseStep 1218003 = 1827005) B1827005
theorem B1218019 : Blo 1217426 1218019 := bstep (se 1 (by rfl) ⟨913514, by rfl⟩ : syracuseStep 1218019 = 1827029) B1827029
theorem B1218035 : Blo 1217426 1218035 := bstep (se 1 (by rfl) ⟨913526, by rfl⟩ : syracuseStep 1218035 = 1827053) B1827053
theorem B1218051 : Blo 1217426 1218051 := bstep (se 1 (by rfl) ⟨913538, by rfl⟩ : syracuseStep 1218051 = 1827077) B1827077
theorem B2741777 : Blo 1217426 2741777 := bstep (se 2 (by rfl) ⟨1028166, by rfl⟩ : syracuseStep 2741777 = 2056333) B2056333
theorem B1218067 : Blo 1217426 1218067 := bstep (se 1 (by rfl) ⟨913550, by rfl⟩ : syracuseStep 1218067 = 1827101) B1827101
theorem B1218083 : Blo 1217426 1218083 := bstep (se 1 (by rfl) ⟨913562, by rfl⟩ : syracuseStep 1218083 = 1827125) B1827125
theorem B2741795 : Blo 1217426 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B3126833 : Blo 1217426 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B1218099 : Blo 1217426 1218099 := bstep (se 1 (by rfl) ⟨913574, by rfl⟩ : syracuseStep 1218099 = 1827149) B1827149
theorem B1218115 : Blo 1217426 1218115 := bstep (se 1 (by rfl) ⟨913586, by rfl⟩ : syracuseStep 1218115 = 1827173) B1827173
theorem B1218131 : Blo 1217426 1218131 := bstep (se 1 (by rfl) ⟨913598, by rfl⟩ : syracuseStep 1218131 = 1827197) B1827197
theorem B1218147 : Blo 1217426 1218147 := bstep (se 1 (by rfl) ⟨913610, by rfl⟩ : syracuseStep 1218147 = 1827221) B1827221
theorem B1734257 : Blo 1217426 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B35599985 : Blo 1217426 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B1218163 : Blo 1217426 1218163 := bstep (se 1 (by rfl) ⟨913622, by rfl⟩ : syracuseStep 1218163 = 1827245) B1827245
theorem B4691569 : Blo 1217426 4691569 := bstep (se 2 (by rfl) ⟨1759338, by rfl⟩ : syracuseStep 4691569 = 3518677) B3518677
theorem B1218179 : Blo 1217426 1218179 := bstep (se 1 (by rfl) ⟨913634, by rfl⟩ : syracuseStep 1218179 = 1827269) B1827269
theorem B1218195 : Blo 1217426 1218195 := bstep (se 1 (by rfl) ⟨913646, by rfl⟩ : syracuseStep 1218195 = 1827293) B1827293
theorem B1218211 : Blo 1217426 1218211 := bstep (se 1 (by rfl) ⟨913658, by rfl⟩ : syracuseStep 1218211 = 1827317) B1827317
theorem B1218227 : Blo 1217426 1218227 := bstep (se 1 (by rfl) ⟨913670, by rfl⟩ : syracuseStep 1218227 = 1827341) B1827341
theorem B1218243 : Blo 1217426 1218243 := bstep (se 1 (by rfl) ⟨913682, by rfl⟩ : syracuseStep 1218243 = 1827365) B1827365
theorem B1218259 : Blo 1217426 1218259 := bstep (se 1 (by rfl) ⟨913694, by rfl⟩ : syracuseStep 1218259 = 1827389) B1827389
theorem B1218275 : Blo 1217426 1218275 := bstep (se 1 (by rfl) ⟨913706, by rfl⟩ : syracuseStep 1218275 = 1827413) B1827413
theorem B1218291 : Blo 1217426 1218291 := bstep (se 1 (by rfl) ⟨913718, by rfl⟩ : syracuseStep 1218291 = 1827437) B1827437
theorem B1218307 : Blo 1217426 1218307 := bstep (se 1 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 1218307 = 1827461) B1827461
theorem B1218323 : Blo 1217426 1218323 := bstep (se 1 (by rfl) ⟨913742, by rfl⟩ : syracuseStep 1218323 = 1827485) B1827485
theorem B1218339 : Blo 1217426 1218339 := bstep (se 1 (by rfl) ⟨913754, by rfl⟩ : syracuseStep 1218339 = 1827509) B1827509
theorem B2742065 : Blo 1217426 2742065 := bstep (se 2 (by rfl) ⟨1028274, by rfl⟩ : syracuseStep 2742065 = 2056549) B2056549
theorem B1218355 : Blo 1217426 1218355 := bstep (se 1 (by rfl) ⟨913766, by rfl⟩ : syracuseStep 1218355 = 1827533) B1827533
theorem B1218371 : Blo 1217426 1218371 := bstep (se 1 (by rfl) ⟨913778, by rfl⟩ : syracuseStep 1218371 = 1827557) B1827557
theorem B2742083 : Blo 1217426 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B1218387 : Blo 1217426 1218387 := bstep (se 1 (by rfl) ⟨913790, by rfl⟩ : syracuseStep 1218387 = 1827581) B1827581
theorem B1218403 : Blo 1217426 1218403 := bstep (se 1 (by rfl) ⟨913802, by rfl⟩ : syracuseStep 1218403 = 1827605) B1827605
theorem B1218419 : Blo 1217426 1218419 := bstep (se 1 (by rfl) ⟨913814, by rfl⟩ : syracuseStep 1218419 = 1827629) B1827629
theorem B1218435 : Blo 1217426 1218435 := bstep (se 1 (by rfl) ⟨913826, by rfl⟩ : syracuseStep 1218435 = 1827653) B1827653
theorem B1218451 : Blo 1217426 1218451 := bstep (se 1 (by rfl) ⟨913838, by rfl⟩ : syracuseStep 1218451 = 1827677) B1827677
theorem B3168163 : Blo 1217426 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B1218467 : Blo 1217426 1218467 := bstep (se 1 (by rfl) ⟨913850, by rfl⟩ : syracuseStep 1218467 = 1827701) B1827701
theorem B1218483 : Blo 1217426 1218483 := bstep (se 1 (by rfl) ⟨913862, by rfl⟩ : syracuseStep 1218483 = 1827725) B1827725
theorem B1218499 : Blo 1217426 1218499 := bstep (se 1 (by rfl) ⟨913874, by rfl⟩ : syracuseStep 1218499 = 1827749) B1827749
theorem B1218515 : Blo 1217426 1218515 := bstep (se 1 (by rfl) ⟨913886, by rfl⟩ : syracuseStep 1218515 = 1827773) B1827773
theorem B1218531 : Blo 1217426 1218531 := bstep (se 1 (by rfl) ⟨913898, by rfl⟩ : syracuseStep 1218531 = 1827797) B1827797
theorem B4110317 : Blo 1217426 4110317 := bstep (se 3 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 4110317 = 1541369) B1541369
theorem B9254897 : Blo 1217426 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B1218547 : Blo 1217426 1218547 := bstep (se 1 (by rfl) ⟨913910, by rfl⟩ : syracuseStep 1218547 = 1827821) B1827821
theorem B1218563 : Blo 1217426 1218563 := bstep (se 1 (by rfl) ⟨913922, by rfl⟩ : syracuseStep 1218563 = 1827845) B1827845
theorem B1218579 : Blo 1217426 1218579 := bstep (se 1 (by rfl) ⟨913934, by rfl⟩ : syracuseStep 1218579 = 1827869) B1827869
theorem B4110371 : Blo 1217426 4110371 := bstep (se 1 (by rfl) ⟨3082778, by rfl⟩ : syracuseStep 4110371 = 6165557) B6165557
theorem B1218595 : Blo 1217426 1218595 := bstep (se 1 (by rfl) ⟨913946, by rfl⟩ : syracuseStep 1218595 = 1827893) B1827893
theorem B1218611 : Blo 1217426 1218611 := bstep (se 1 (by rfl) ⟨913958, by rfl⟩ : syracuseStep 1218611 = 1827917) B1827917
theorem B1218627 : Blo 1217426 1218627 := bstep (se 1 (by rfl) ⟨913970, by rfl⟩ : syracuseStep 1218627 = 1827941) B1827941
theorem B2742353 : Blo 1217426 2742353 := bstep (se 2 (by rfl) ⟨1028382, by rfl⟩ : syracuseStep 2742353 = 2056765) B2056765
theorem B1218643 : Blo 1217426 1218643 := bstep (se 1 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 1218643 = 1827965) B1827965
theorem B1218659 : Blo 1217426 1218659 := bstep (se 1 (by rfl) ⟨913994, by rfl⟩ : syracuseStep 1218659 = 1827989) B1827989
theorem B2742371 : Blo 1217426 2742371 := bstep (se 1 (by rfl) ⟨2056778, by rfl⟩ : syracuseStep 2742371 = 4113557) B4113557
theorem B1464419 : Blo 1217426 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1218675 : Blo 1217426 1218675 := bstep (se 1 (by rfl) ⟨914006, by rfl⟩ : syracuseStep 1218675 = 1828013) B1828013
theorem B1734787 : Blo 1217426 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B1218691 : Blo 1217426 1218691 := bstep (se 1 (by rfl) ⟨914018, by rfl⟩ : syracuseStep 1218691 = 1828037) B1828037
theorem B1218707 : Blo 1217426 1218707 := bstep (se 1 (by rfl) ⟨914030, by rfl⟩ : syracuseStep 1218707 = 1828061) B1828061
theorem B6166691 : Blo 1217426 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B1218723 : Blo 1217426 1218723 := bstep (se 1 (by rfl) ⟨914042, by rfl⟩ : syracuseStep 1218723 = 1828085) B1828085
theorem B1218739 : Blo 1217426 1218739 := bstep (se 1 (by rfl) ⟨914054, by rfl⟩ : syracuseStep 1218739 = 1828109) B1828109
theorem B1218755 : Blo 1217426 1218755 := bstep (se 1 (by rfl) ⟨914066, by rfl⟩ : syracuseStep 1218755 = 1828133) B1828133
theorem B5560525 : Blo 1217426 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B3086545 : Blo 1217426 3086545 := bstep (se 2 (by rfl) ⟨1157454, by rfl⟩ : syracuseStep 3086545 = 2314909) B2314909
theorem B1218771 : Blo 1217426 1218771 := bstep (se 1 (by rfl) ⟨914078, by rfl⟩ : syracuseStep 1218771 = 1828157) B1828157
theorem B16890083 : Blo 1217426 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B4626659 : Blo 1217426 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B1218787 : Blo 1217426 1218787 := bstep (se 1 (by rfl) ⟨914090, by rfl⟩ : syracuseStep 1218787 = 1828181) B1828181
theorem B16685297 : Blo 1217426 16685297 := bstep (se 2 (by rfl) ⟨6256986, by rfl⟩ : syracuseStep 16685297 = 12513973) B12513973
theorem B1218803 : Blo 1217426 1218803 := bstep (se 1 (by rfl) ⟨914102, by rfl⟩ : syracuseStep 1218803 = 1828205) B1828205
theorem B1218819 : Blo 1217426 1218819 := bstep (se 1 (by rfl) ⟨914114, by rfl⟩ : syracuseStep 1218819 = 1828229) B1828229
theorem B3905795 : Blo 1217426 3905795 := bstep (se 1 (by rfl) ⟨2929346, by rfl⟩ : syracuseStep 3905795 = 5858693) B5858693
theorem B1218835 : Blo 1217426 1218835 := bstep (se 1 (by rfl) ⟨914126, by rfl⟩ : syracuseStep 1218835 = 1828253) B1828253
theorem B1218851 : Blo 1217426 1218851 := bstep (se 1 (by rfl) ⟨914138, by rfl⟩ : syracuseStep 1218851 = 1828277) B1828277
theorem B4110641 : Blo 1217426 4110641 := bstep (se 2 (by rfl) ⟨1541490, by rfl⟩ : syracuseStep 4110641 = 3082981) B3082981
theorem B1235251 : Blo 1217426 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B1218867 : Blo 1217426 1218867 := bstep (se 1 (by rfl) ⟨914150, by rfl⟩ : syracuseStep 1218867 = 1828301) B1828301
theorem B1218883 : Blo 1217426 1218883 := bstep (se 1 (by rfl) ⟨914162, by rfl⟩ : syracuseStep 1218883 = 1828325) B1828325
theorem B1218899 : Blo 1217426 1218899 := bstep (se 1 (by rfl) ⟨914174, by rfl⟩ : syracuseStep 1218899 = 1828349) B1828349
theorem B2054497 : Blo 1217426 2054497 := bstep (se 2 (by rfl) ⟨770436, by rfl⟩ : syracuseStep 2054497 = 1540873) B1540873
theorem B1218915 : Blo 1217426 1218915 := bstep (se 1 (by rfl) ⟨914186, by rfl⟩ : syracuseStep 1218915 = 1828373) B1828373
theorem B2742641 : Blo 1217426 2742641 := bstep (se 2 (by rfl) ⟨1028490, by rfl⟩ : syracuseStep 2742641 = 2056981) B2056981
theorem B1218931 : Blo 1217426 1218931 := bstep (se 1 (by rfl) ⟨914198, by rfl⟩ : syracuseStep 1218931 = 1828397) B1828397
theorem B2054531 : Blo 1217426 2054531 := bstep (se 1 (by rfl) ⟨1540898, by rfl⟩ : syracuseStep 2054531 = 3081797) B3081797
theorem B1218947 : Blo 1217426 1218947 := bstep (se 1 (by rfl) ⟨914210, by rfl⟩ : syracuseStep 1218947 = 1828421) B1828421
theorem B2742659 : Blo 1217426 2742659 := bstep (se 1 (by rfl) ⟨2056994, by rfl⟩ : syracuseStep 2742659 = 4113989) B4113989
theorem B15604109 : Blo 1217426 15604109 := bstep (se 3 (by rfl) ⟨2925770, by rfl⟩ : syracuseStep 15604109 = 5851541) B5851541
theorem B3471761 : Blo 1217426 3471761 := bstep (se 2 (by rfl) ⟨1301910, by rfl⟩ : syracuseStep 3471761 = 2603821) B2603821
theorem B1218963 : Blo 1217426 1218963 := bstep (se 1 (by rfl) ⟨914222, by rfl⟩ : syracuseStep 1218963 = 1828445) B1828445
theorem B1218979 : Blo 1217426 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B1218995 : Blo 1217426 1218995 := bstep (se 1 (by rfl) ⟨914246, by rfl⟩ : syracuseStep 1218995 = 1828493) B1828493
theorem B1219011 : Blo 1217426 1219011 := bstep (se 1 (by rfl) ⟨914258, by rfl⟩ : syracuseStep 1219011 = 1828517) B1828517
theorem B8444357 : Blo 1217426 8444357 := bstep (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) B1583317
theorem B1735123 : Blo 1217426 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B1219027 : Blo 1217426 1219027 := bstep (se 1 (by rfl) ⟨914270, by rfl⟩ : syracuseStep 1219027 = 1828541) B1828541
theorem B1219043 : Blo 1217426 1219043 := bstep (se 1 (by rfl) ⟨914282, by rfl⟩ : syracuseStep 1219043 = 1828565) B1828565
theorem B6937073 : Blo 1217426 6937073 := bstep (se 2 (by rfl) ⟨2601402, by rfl⟩ : syracuseStep 6937073 = 5202805) B5202805
theorem B1219059 : Blo 1217426 1219059 := bstep (se 1 (by rfl) ⟨914294, by rfl⟩ : syracuseStep 1219059 = 1828589) B1828589
theorem B2054659 : Blo 1217426 2054659 := bstep (se 1 (by rfl) ⟨1540994, by rfl⟩ : syracuseStep 2054659 = 3081989) B3081989
theorem B1219075 : Blo 1217426 1219075 := bstep (se 1 (by rfl) ⟨914306, by rfl⟩ : syracuseStep 1219075 = 1828613) B1828613
theorem B1219091 : Blo 1217426 1219091 := bstep (se 1 (by rfl) ⟨914318, by rfl⟩ : syracuseStep 1219091 = 1828637) B1828637
theorem B1219107 : Blo 1217426 1219107 := bstep (se 1 (by rfl) ⟨914330, by rfl⟩ : syracuseStep 1219107 = 1828661) B1828661
theorem B1219123 : Blo 1217426 1219123 := bstep (se 1 (by rfl) ⟨914342, by rfl⟩ : syracuseStep 1219123 = 1828685) B1828685
theorem B1219139 : Blo 1217426 1219139 := bstep (se 1 (by rfl) ⟨914354, by rfl⟩ : syracuseStep 1219139 = 1828709) B1828709
theorem B1219155 : Blo 1217426 1219155 := bstep (se 1 (by rfl) ⟨914366, by rfl⟩ : syracuseStep 1219155 = 1828733) B1828733
theorem B1219171 : Blo 1217426 1219171 := bstep (se 1 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 1219171 = 1828757) B1828757
theorem B1219187 : Blo 1217426 1219187 := bstep (se 1 (by rfl) ⟨914390, by rfl⟩ : syracuseStep 1219187 = 1828781) B1828781
theorem B1219203 : Blo 1217426 1219203 := bstep (se 1 (by rfl) ⟨914402, by rfl⟩ : syracuseStep 1219203 = 1828805) B1828805
theorem B2054801 : Blo 1217426 2054801 := bstep (se 2 (by rfl) ⟨770550, by rfl⟩ : syracuseStep 2054801 = 1541101) B1541101
theorem B2742929 : Blo 1217426 2742929 := bstep (se 2 (by rfl) ⟨1028598, by rfl⟩ : syracuseStep 2742929 = 2057197) B2057197
theorem B1219219 : Blo 1217426 1219219 := bstep (se 1 (by rfl) ⟨914414, by rfl⟩ : syracuseStep 1219219 = 1828829) B1828829
theorem B2742947 : Blo 1217426 2742947 := bstep (se 1 (by rfl) ⟨2057210, by rfl⟩ : syracuseStep 2742947 = 4114421) B4114421
theorem B1219235 : Blo 1217426 1219235 := bstep (se 1 (by rfl) ⟨914426, by rfl⟩ : syracuseStep 1219235 = 1828853) B1828853
theorem B1219251 : Blo 1217426 1219251 := bstep (se 1 (by rfl) ⟨914438, by rfl⟩ : syracuseStep 1219251 = 1828877) B1828877
theorem B1219267 : Blo 1217426 1219267 := bstep (se 1 (by rfl) ⟨914450, by rfl⟩ : syracuseStep 1219267 = 1828901) B1828901
theorem B7805645 : Blo 1217426 7805645 := bstep (se 3 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 7805645 = 2927117) B2927117
theorem B1219283 : Blo 1217426 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B11107043 : Blo 1217426 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B35609315 : Blo 1217426 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B1219299 : Blo 1217426 1219299 := bstep (se 1 (by rfl) ⟨914474, by rfl⟩ : syracuseStep 1219299 = 1828949) B1828949
theorem B1219315 : Blo 1217426 1219315 := bstep (se 1 (by rfl) ⟨914486, by rfl⟩ : syracuseStep 1219315 = 1828973) B1828973
theorem B1219331 : Blo 1217426 1219331 := bstep (se 1 (by rfl) ⟨914498, by rfl⟩ : syracuseStep 1219331 = 1828997) B1828997
theorem B2054929 : Blo 1217426 2054929 := bstep (se 2 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 2054929 = 1541197) B1541197
theorem B1219347 : Blo 1217426 1219347 := bstep (se 1 (by rfl) ⟨914510, by rfl⟩ : syracuseStep 1219347 = 1829021) B1829021
theorem B1219363 : Blo 1217426 1219363 := bstep (se 1 (by rfl) ⟨914522, by rfl⟩ : syracuseStep 1219363 = 1829045) B1829045
theorem B2054963 : Blo 1217426 2054963 := bstep (se 1 (by rfl) ⟨1541222, by rfl⟩ : syracuseStep 2054963 = 3082445) B3082445
theorem B1219379 : Blo 1217426 1219379 := bstep (se 1 (by rfl) ⟨914534, by rfl⟩ : syracuseStep 1219379 = 1829069) B1829069
theorem B1219395 : Blo 1217426 1219395 := bstep (se 1 (by rfl) ⟨914546, by rfl⟩ : syracuseStep 1219395 = 1829093) B1829093
theorem B4111181 : Blo 1217426 4111181 := bstep (se 3 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 4111181 = 1541693) B1541693
theorem B1219411 : Blo 1217426 1219411 := bstep (se 1 (by rfl) ⟨914558, by rfl⟩ : syracuseStep 1219411 = 1829117) B1829117
theorem B22518641 : Blo 1217426 22518641 := bstep (se 2 (by rfl) ⟨8444490, by rfl⟩ : syracuseStep 22518641 = 16888981) B16888981
theorem B4627313 : Blo 1217426 4627313 := bstep (se 2 (by rfl) ⟨1735242, by rfl⟩ : syracuseStep 4627313 = 3470485) B3470485
theorem B4111235 : Blo 1217426 4111235 := bstep (se 1 (by rfl) ⟨3083426, by rfl⟩ : syracuseStep 4111235 = 6166853) B6166853
theorem B2743217 : Blo 1217426 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B2055091 : Blo 1217426 2055091 := bstep (se 1 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 2055091 = 3082637) B3082637
theorem B2743235 : Blo 1217426 2743235 := bstep (se 1 (by rfl) ⟨2057426, by rfl⟩ : syracuseStep 2743235 = 4114853) B4114853
theorem B6167501 : Blo 1217426 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B8780771 : Blo 1217426 8780771 := bstep (se 1 (by rfl) ⟨6585578, by rfl⟩ : syracuseStep 8780771 = 13171157) B13171157
theorem B1735681 : Blo 1217426 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B1735715 : Blo 1217426 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B3472433 : Blo 1217426 3472433 := bstep (se 2 (by rfl) ⟨1302162, by rfl⟩ : syracuseStep 3472433 = 2604325) B2604325
theorem B2055233 : Blo 1217426 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B4815949 : Blo 1217426 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B2604163 : Blo 1217426 2604163 := bstep (se 1 (by rfl) ⟨1953122, by rfl⟩ : syracuseStep 2604163 = 3906245) B3906245
theorem B4111505 : Blo 1217426 4111505 := bstep (se 2 (by rfl) ⟨1541814, by rfl⟩ : syracuseStep 4111505 = 3083629) B3083629
theorem B2055361 : Blo 1217426 2055361 := bstep (se 2 (by rfl) ⟨770760, by rfl⟩ : syracuseStep 2055361 = 1541521) B1541521
theorem B2743505 : Blo 1217426 2743505 := bstep (se 2 (by rfl) ⟨1028814, by rfl⟩ : syracuseStep 2743505 = 2057629) B2057629
theorem B2055395 : Blo 1217426 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B2743523 : Blo 1217426 2743523 := bstep (se 1 (by rfl) ⟨2057642, by rfl⟩ : syracuseStep 2743523 = 4115285) B4115285
theorem B5201165 : Blo 1217426 5201165 := bstep (se 3 (by rfl) ⟨975218, by rfl⟩ : syracuseStep 5201165 = 1950437) B1950437
theorem B1826147 : Blo 1217426 1826147 := bstep (se 1 (by rfl) ⟨1369610, by rfl⟩ : syracuseStep 1826147 = 2739221) B2739221
theorem B2055523 : Blo 1217426 2055523 := bstep (se 1 (by rfl) ⟨1541642, by rfl⟩ : syracuseStep 2055523 = 3083285) B3083285
theorem B1826177 : Blo 1217426 1826177 := bstep (se 2 (by rfl) ⟨684816, by rfl⟩ : syracuseStep 1826177 = 1369633) B1369633
theorem B1826195 : Blo 1217426 1826195 := bstep (se 1 (by rfl) ⟨1369646, by rfl⟩ : syracuseStep 1826195 = 2739293) B2739293
theorem B1301923 : Blo 1217426 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1826225 : Blo 1217426 1826225 := bstep (se 2 (by rfl) ⟨684834, by rfl⟩ : syracuseStep 1826225 = 1369669) B1369669
theorem B1826243 : Blo 1217426 1826243 := bstep (se 1 (by rfl) ⟨1369682, by rfl⟩ : syracuseStep 1826243 = 2739365) B2739365
theorem B1826273 : Blo 1217426 1826273 := bstep (se 2 (by rfl) ⟨684852, by rfl⟩ : syracuseStep 1826273 = 1369705) B1369705
theorem B2055665 : Blo 1217426 2055665 := bstep (se 2 (by rfl) ⟨770874, by rfl⟩ : syracuseStep 2055665 = 1541749) B1541749
theorem B1826291 : Blo 1217426 1826291 := bstep (se 1 (by rfl) ⟨1369718, by rfl⟩ : syracuseStep 1826291 = 2739437) B2739437
theorem B1826321 : Blo 1217426 1826321 := bstep (se 2 (by rfl) ⟨684870, by rfl⟩ : syracuseStep 1826321 = 1369741) B1369741
theorem B1826339 : Blo 1217426 1826339 := bstep (se 1 (by rfl) ⟨1369754, by rfl⟩ : syracuseStep 1826339 = 2739509) B2739509
theorem B1826369 : Blo 1217426 1826369 := bstep (se 2 (by rfl) ⟨684888, by rfl⟩ : syracuseStep 1826369 = 1369777) B1369777
theorem B2113091 : Blo 1217426 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B1826387 : Blo 1217426 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B1826417 : Blo 1217426 1826417 := bstep (se 2 (by rfl) ⟨684906, by rfl⟩ : syracuseStep 1826417 = 1369813) B1369813
theorem B2055793 : Blo 1217426 2055793 := bstep (se 2 (by rfl) ⟨770922, by rfl⟩ : syracuseStep 2055793 = 1541845) B1541845
theorem B1826435 : Blo 1217426 1826435 := bstep (se 1 (by rfl) ⟨1369826, by rfl⟩ : syracuseStep 1826435 = 2739653) B2739653
theorem B2055827 : Blo 1217426 2055827 := bstep (se 1 (by rfl) ⟨1541870, by rfl⟩ : syracuseStep 2055827 = 3083741) B3083741
theorem B1826465 : Blo 1217426 1826465 := bstep (se 2 (by rfl) ⟨684924, by rfl⟩ : syracuseStep 1826465 = 1369849) B1369849
theorem B4112045 : Blo 1217426 4112045 := bstep (se 3 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 4112045 = 1542017) B1542017
theorem B7618225 : Blo 1217426 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B1826483 : Blo 1217426 1826483 := bstep (se 1 (by rfl) ⟨1369862, by rfl⟩ : syracuseStep 1826483 = 2739725) B2739725
theorem B1826513 : Blo 1217426 1826513 := bstep (se 2 (by rfl) ⟨684942, by rfl⟩ : syracuseStep 1826513 = 1369885) B1369885
theorem B1826531 : Blo 1217426 1826531 := bstep (se 1 (by rfl) ⟨1369898, by rfl⟩ : syracuseStep 1826531 = 2739797) B2739797
theorem B4112099 : Blo 1217426 4112099 := bstep (se 1 (by rfl) ⟨3084074, by rfl⟩ : syracuseStep 4112099 = 6168149) B6168149
theorem B1826561 : Blo 1217426 1826561 := bstep (se 2 (by rfl) ⟨684960, by rfl⟩ : syracuseStep 1826561 = 1369921) B1369921
theorem B1826579 : Blo 1217426 1826579 := bstep (se 1 (by rfl) ⟨1369934, by rfl⟩ : syracuseStep 1826579 = 2739869) B2739869
theorem B2055955 : Blo 1217426 2055955 := bstep (se 1 (by rfl) ⟨1541966, by rfl⟩ : syracuseStep 2055955 = 3083933) B3083933
theorem B1826609 : Blo 1217426 1826609 := bstep (se 2 (by rfl) ⟨684978, by rfl⟩ : syracuseStep 1826609 = 1369957) B1369957
theorem B1826627 : Blo 1217426 1826627 := bstep (se 1 (by rfl) ⟨1369970, by rfl⟩ : syracuseStep 1826627 = 2739941) B2739941
theorem B1826657 : Blo 1217426 1826657 := bstep (se 2 (by rfl) ⟨684996, by rfl⟩ : syracuseStep 1826657 = 1369993) B1369993
theorem B1826675 : Blo 1217426 1826675 := bstep (se 1 (by rfl) ⟨1370006, by rfl⟩ : syracuseStep 1826675 = 2740013) B2740013
theorem B1826705 : Blo 1217426 1826705 := bstep (se 2 (by rfl) ⟨685014, by rfl⟩ : syracuseStep 1826705 = 1370029) B1370029
theorem B2056097 : Blo 1217426 2056097 := bstep (se 2 (by rfl) ⟨771036, by rfl⟩ : syracuseStep 2056097 = 1542073) B1542073
theorem B1826723 : Blo 1217426 1826723 := bstep (se 1 (by rfl) ⟨1370042, by rfl⟩ : syracuseStep 1826723 = 2740085) B2740085
theorem B6938531 : Blo 1217426 6938531 := bstep (se 1 (by rfl) ⟨5203898, by rfl⟩ : syracuseStep 6938531 = 10407797) B10407797
theorem B1826753 : Blo 1217426 1826753 := bstep (se 2 (by rfl) ⟨685032, by rfl⟩ : syracuseStep 1826753 = 1370065) B1370065
theorem B1826771 : Blo 1217426 1826771 := bstep (se 1 (by rfl) ⟨1370078, by rfl⟩ : syracuseStep 1826771 = 2740157) B2740157
theorem B1826801 : Blo 1217426 1826801 := bstep (se 2 (by rfl) ⟨685050, by rfl⟩ : syracuseStep 1826801 = 1370101) B1370101
theorem B4112369 : Blo 1217426 4112369 := bstep (se 2 (by rfl) ⟨1542138, by rfl⟩ : syracuseStep 4112369 = 3084277) B3084277
theorem B1826891 : Blo 1217426 1826891 := bstep (se 1 (by rfl) ⟨1370168, by rfl⟩ : syracuseStep 1826891 = 2740337) B2740337
theorem B1826903 : Blo 1217426 1826903 := bstep (se 1 (by rfl) ⟨1370177, by rfl⟩ : syracuseStep 1826903 = 2740355) B2740355
theorem B2056279 : Blo 1217426 2056279 := bstep (se 1 (by rfl) ⟨1542209, by rfl⟩ : syracuseStep 2056279 = 3084419) B3084419
theorem B4112477 : Blo 1217426 4112477 := bstep (se 3 (by rfl) ⟨771089, by rfl⟩ : syracuseStep 4112477 = 1542179) B1542179
theorem B4628573 : Blo 1217426 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B1826969 : Blo 1217426 1826969 := bstep (se 2 (by rfl) ⟨685113, by rfl⟩ : syracuseStep 1826969 = 1370227) B1370227
theorem B1827083 : Blo 1217426 1827083 := bstep (se 1 (by rfl) ⟨1370312, by rfl⟩ : syracuseStep 1827083 = 2740625) B2740625
theorem B7414033 : Blo 1217426 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B1827095 : Blo 1217426 1827095 := bstep (se 1 (by rfl) ⟨1370321, by rfl⟩ : syracuseStep 1827095 = 2740643) B2740643
theorem B2638145 : Blo 1217426 2638145 := bstep (se 2 (by rfl) ⟨989304, by rfl⟩ : syracuseStep 2638145 = 1978609) B1978609
theorem B1827161 : Blo 1217426 1827161 := bstep (se 2 (by rfl) ⟨685185, by rfl⟩ : syracuseStep 1827161 = 1370371) B1370371
theorem B1647001 : Blo 1217426 1647001 := bstep (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) B1235251
theorem B1827275 : Blo 1217426 1827275 := bstep (se 1 (by rfl) ⟨1370456, by rfl⟩ : syracuseStep 1827275 = 2740913) B2740913
theorem B1827287 : Blo 1217426 1827287 := bstep (se 1 (by rfl) ⟨1370465, by rfl⟩ : syracuseStep 1827287 = 2740931) B2740931
theorem B10412549 : Blo 1217426 10412549 := bstep (se 4 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 10412549 = 1952353) B1952353
theorem B1827353 : Blo 1217426 1827353 := bstep (se 2 (by rfl) ⟨685257, by rfl⟩ : syracuseStep 1827353 = 1370515) B1370515
theorem B10551883 : Blo 1217426 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B35111555 : Blo 1217426 35111555 := bstep (se 1 (by rfl) ⟨26333666, by rfl⟩ : syracuseStep 35111555 = 52667333) B52667333
theorem B1827467 : Blo 1217426 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B1827479 : Blo 1217426 1827479 := bstep (se 1 (by rfl) ⟨1370609, by rfl⟩ : syracuseStep 1827479 = 2741219) B2741219
theorem B2056907 : Blo 1217426 2056907 := bstep (se 1 (by rfl) ⟨1542680, by rfl⟩ : syracuseStep 2056907 = 3085361) B3085361
theorem B1827545 : Blo 1217426 1827545 := bstep (se 2 (by rfl) ⟨685329, by rfl⟩ : syracuseStep 1827545 = 1370659) B1370659
theorem B4629271 : Blo 1217426 4629271 := bstep (se 1 (by rfl) ⟨3471953, by rfl⟩ : syracuseStep 4629271 = 6943907) B6943907
theorem B1540939 : Blo 1217426 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B1827659 : Blo 1217426 1827659 := bstep (se 1 (by rfl) ⟨1370744, by rfl⟩ : syracuseStep 1827659 = 2741489) B2741489
theorem B2057035 : Blo 1217426 2057035 := bstep (se 1 (by rfl) ⟨1542776, by rfl⟩ : syracuseStep 2057035 = 3085553) B3085553
theorem B1827671 : Blo 1217426 1827671 := bstep (se 1 (by rfl) ⟨1370753, by rfl⟩ : syracuseStep 1827671 = 2741507) B2741507
theorem B1950617 : Blo 1217426 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B1827737 : Blo 1217426 1827737 := bstep (se 2 (by rfl) ⟨685401, by rfl⟩ : syracuseStep 1827737 = 1370803) B1370803
theorem B4391873 : Blo 1217426 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B2057177 : Blo 1217426 2057177 := bstep (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) B1542883
theorem B1827851 : Blo 1217426 1827851 := bstep (se 1 (by rfl) ⟨1370888, by rfl⟩ : syracuseStep 1827851 = 2741777) B2741777
theorem B1827863 : Blo 1217426 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B1950745 : Blo 1217426 1950745 := bstep (se 2 (by rfl) ⟨731529, by rfl⟩ : syracuseStep 1950745 = 1463059) B1463059
theorem B23733323 : Blo 1217426 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B3294283 : Blo 1217426 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B1541207 : Blo 1217426 1541207 := bstep (se 1 (by rfl) ⟨1155905, by rfl⟩ : syracuseStep 1541207 = 2311811) B2311811
theorem B1827929 : Blo 1217426 1827929 := bstep (se 2 (by rfl) ⟨685473, by rfl⟩ : syracuseStep 1827929 = 1370947) B1370947
theorem B2057305 : Blo 1217426 2057305 := bstep (se 2 (by rfl) ⟨771489, by rfl⟩ : syracuseStep 2057305 = 1542979) B1542979
theorem B1828043 : Blo 1217426 1828043 := bstep (se 1 (by rfl) ⟨1371032, by rfl⟩ : syracuseStep 1828043 = 2742065) B2742065
theorem B4113611 : Blo 1217426 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B1828055 : Blo 1217426 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B1828121 : Blo 1217426 1828121 := bstep (se 2 (by rfl) ⟨685545, by rfl⟩ : syracuseStep 1828121 = 1371091) B1371091
theorem B6169931 : Blo 1217426 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2311553 : Blo 1217426 2311553 := bstep (se 2 (by rfl) ⟨866832, by rfl⟩ : syracuseStep 2311553 = 1733665) B1733665
theorem B1828235 : Blo 1217426 1828235 := bstep (se 1 (by rfl) ⟨1371176, by rfl⟩ : syracuseStep 1828235 = 2742353) B2742353
theorem B1828247 : Blo 1217426 1828247 := bstep (se 1 (by rfl) ⟨1371185, by rfl⟩ : syracuseStep 1828247 = 2742371) B2742371
theorem B1951129 : Blo 1217426 1951129 := bstep (se 2 (by rfl) ⟨731673, by rfl⟩ : syracuseStep 1951129 = 1463347) B1463347
theorem B3081665 : Blo 1217426 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B1828313 : Blo 1217426 1828313 := bstep (se 2 (by rfl) ⟨685617, by rfl⟩ : syracuseStep 1828313 = 1371235) B1371235
theorem B4113881 : Blo 1217426 4113881 := bstep (se 2 (by rfl) ⟨1542705, by rfl⟩ : syracuseStep 4113881 = 3085411) B3085411
theorem B1828427 : Blo 1217426 1828427 := bstep (se 1 (by rfl) ⟨1371320, by rfl⟩ : syracuseStep 1828427 = 2742641) B2742641
theorem B1369687 : Blo 1217426 1369687 := bstep (se 1 (by rfl) ⟨1027265, by rfl⟩ : syracuseStep 1369687 = 2054531) B2054531
theorem B1828439 : Blo 1217426 1828439 := bstep (se 1 (by rfl) ⟨1371329, by rfl⟩ : syracuseStep 1828439 = 2742659) B2742659
theorem B5629571 : Blo 1217426 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B1951385 : Blo 1217426 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B1828505 : Blo 1217426 1828505 := bstep (se 2 (by rfl) ⟨685689, by rfl⟩ : syracuseStep 1828505 = 1371379) B1371379
theorem B2311895 : Blo 1217426 2311895 := bstep (se 1 (by rfl) ⟨1733921, by rfl⟩ : syracuseStep 2311895 = 3467843) B3467843
theorem B1369867 : Blo 1217426 1369867 := bstep (se 1 (by rfl) ⟨1027400, by rfl⟩ : syracuseStep 1369867 = 2054801) B2054801
theorem B1828619 : Blo 1217426 1828619 := bstep (se 1 (by rfl) ⟨1371464, by rfl⟩ : syracuseStep 1828619 = 2742929) B2742929
theorem B1541911 : Blo 1217426 1541911 := bstep (se 1 (by rfl) ⟨1156433, by rfl⟩ : syracuseStep 1541911 = 2312867) B2312867
theorem B1828631 : Blo 1217426 1828631 := bstep (se 1 (by rfl) ⟨1371473, by rfl⟩ : syracuseStep 1828631 = 2742947) B2742947
theorem B5203763 : Blo 1217426 5203763 := bstep (se 1 (by rfl) ⟨3902822, by rfl⟩ : syracuseStep 5203763 = 7805645) B7805645
theorem B3901259 : Blo 1217426 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B1828697 : Blo 1217426 1828697 := bstep (se 2 (by rfl) ⟨685761, by rfl⟩ : syracuseStep 1828697 = 1371523) B1371523
theorem B1369975 : Blo 1217426 1369975 := bstep (se 1 (by rfl) ⟨1027481, by rfl⟩ : syracuseStep 1369975 = 2054963) B2054963
theorem B3295169 : Blo 1217426 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B3958721 : Blo 1217426 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1828811 : Blo 1217426 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B1828823 : Blo 1217426 1828823 := bstep (se 1 (by rfl) ⟨1371617, by rfl⟩ : syracuseStep 1828823 = 2743235) B2743235
theorem B13887449 : Blo 1217426 13887449 := bstep (se 2 (by rfl) ⟨5207793, by rfl⟩ : syracuseStep 13887449 = 10415587) B10415587
theorem B8775697 : Blo 1217426 8775697 := bstep (se 2 (by rfl) ⟨3290886, by rfl⟩ : syracuseStep 8775697 = 6581773) B6581773
theorem B1828889 : Blo 1217426 1828889 := bstep (se 2 (by rfl) ⟨685833, by rfl⟩ : syracuseStep 1828889 = 1371667) B1371667
theorem B1370155 : Blo 1217426 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B4622467 : Blo 1217426 4622467 := bstep (se 1 (by rfl) ⟨3466850, by rfl⟩ : syracuseStep 4622467 = 6933701) B6933701
theorem B1829003 : Blo 1217426 1829003 := bstep (se 1 (by rfl) ⟨1371752, by rfl⟩ : syracuseStep 1829003 = 2743505) B2743505
theorem B1370263 : Blo 1217426 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B4114583 : Blo 1217426 4114583 := bstep (se 1 (by rfl) ⟨3085937, by rfl⟩ : syracuseStep 4114583 = 6171875) B6171875
theorem B1829015 : Blo 1217426 1829015 := bstep (se 1 (by rfl) ⟨1371761, by rfl⟩ : syracuseStep 1829015 = 2743523) B2743523
theorem B3467443 : Blo 1217426 3467443 := bstep (se 1 (by rfl) ⟨2600582, by rfl⟩ : syracuseStep 3467443 = 5201165) B5201165
theorem B1829081 : Blo 1217426 1829081 := bstep (se 2 (by rfl) ⟨685905, by rfl⟩ : syracuseStep 1829081 = 1371811) B1371811
theorem B1370443 : Blo 1217426 1370443 := bstep (se 1 (by rfl) ⟨1027832, by rfl⟩ : syracuseStep 1370443 = 2055665) B2055665
theorem B2312563 : Blo 1217426 2312563 := bstep (se 1 (by rfl) ⟨1734422, by rfl⟩ : syracuseStep 2312563 = 3468845) B3468845
theorem B4622771 : Blo 1217426 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B3295667 : Blo 1217426 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B1370551 : Blo 1217426 1370551 := bstep (se 1 (by rfl) ⟨1027913, by rfl⟩ : syracuseStep 1370551 = 2055827) B2055827
theorem B4450753 : Blo 1217426 4450753 := bstep (se 2 (by rfl) ⟨1669032, by rfl⟩ : syracuseStep 4450753 = 3338065) B3338065
theorem B3902003 : Blo 1217426 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B23415389 : Blo 1217426 23415389 := bstep (se 3 (by rfl) ⟨4390385, by rfl⟩ : syracuseStep 23415389 = 8780771) B8780771
theorem B6589021 : Blo 1217426 6589021 := bstep (se 3 (by rfl) ⟨1235441, by rfl⟩ : syracuseStep 6589021 = 2470883) B2470883
theorem B1370731 : Blo 1217426 1370731 := bstep (se 1 (by rfl) ⟨1028048, by rfl⟩ : syracuseStep 1370731 = 2056097) B2056097
theorem B3082931 : Blo 1217426 3082931 := bstep (se 1 (by rfl) ⟨2312198, by rfl⟩ : syracuseStep 3082931 = 4624397) B4624397
theorem B4115123 : Blo 1217426 4115123 := bstep (se 1 (by rfl) ⟨3086342, by rfl⟩ : syracuseStep 4115123 = 6172685) B6172685
theorem B1370839 : Blo 1217426 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B14822189 : Blo 1217426 14822189 := bstep (se 3 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 14822189 = 5558321) B5558321
theorem B2313011 : Blo 1217426 2313011 := bstep (se 1 (by rfl) ⟨1734758, by rfl⟩ : syracuseStep 2313011 = 3469517) B3469517
theorem B2313049 : Blo 1217426 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B1371019 : Blo 1217426 1371019 := bstep (se 1 (by rfl) ⟨1028264, by rfl⟩ : syracuseStep 1371019 = 2056529) B2056529
theorem B2927539 : Blo 1217426 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B4115393 : Blo 1217426 4115393 := bstep (se 2 (by rfl) ⟨1543272, by rfl⟩ : syracuseStep 4115393 = 3086545) B3086545
theorem B1371127 : Blo 1217426 1371127 := bstep (se 1 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 1371127 = 2056691) B2056691
theorem B16673809 : Blo 1217426 16673809 := bstep (se 2 (by rfl) ⟨6252678, by rfl⟩ : syracuseStep 16673809 = 12505357) B12505357
theorem B4623425 : Blo 1217426 4623425 := bstep (se 2 (by rfl) ⟨1733784, by rfl⟩ : syracuseStep 4623425 = 3467569) B3467569
theorem B6171713 : Blo 1217426 6171713 := bstep (se 2 (by rfl) ⟨2314392, by rfl⟩ : syracuseStep 6171713 = 4628785) B4628785
theorem B2739275 : Blo 1217426 2739275 := bstep (se 1 (by rfl) ⟨2054456, by rfl⟩ : syracuseStep 2739275 = 4108913) B4108913
theorem B2739329 : Blo 1217426 2739329 := bstep (se 2 (by rfl) ⟨1027248, by rfl⟩ : syracuseStep 2739329 = 2054497) B2054497
theorem B1371307 : Blo 1217426 1371307 := bstep (se 1 (by rfl) ⟨1028480, by rfl⟩ : syracuseStep 1371307 = 2056961) B2056961
theorem B3468491 : Blo 1217426 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B3083467 : Blo 1217426 3083467 := bstep (se 1 (by rfl) ⟨2312600, by rfl⟩ : syracuseStep 3083467 = 4625201) B4625201
theorem B1371415 : Blo 1217426 1371415 := bstep (se 1 (by rfl) ⟨1028561, by rfl⟩ : syracuseStep 1371415 = 2057123) B2057123
theorem B2313497 : Blo 1217426 2313497 := bstep (se 2 (by rfl) ⟨867561, by rfl⟩ : syracuseStep 2313497 = 1735123) B1735123
theorem B9375011 : Blo 1217426 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B2739545 : Blo 1217426 2739545 := bstep (se 2 (by rfl) ⟨1027329, by rfl⟩ : syracuseStep 2739545 = 2054659) B2054659
theorem B3083609 : Blo 1217426 3083609 := bstep (se 2 (by rfl) ⟨1156353, by rfl⟩ : syracuseStep 3083609 = 2312707) B2312707
theorem B2346355 : Blo 1217426 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B2739635 : Blo 1217426 2739635 := bstep (se 1 (by rfl) ⟨2054726, by rfl⟩ : syracuseStep 2739635 = 4109453) B4109453
theorem B3902899 : Blo 1217426 3902899 := bstep (se 1 (by rfl) ⟨2927174, by rfl⟩ : syracuseStep 3902899 = 5854349) B5854349
theorem B6942131 : Blo 1217426 6942131 := bstep (se 1 (by rfl) ⟨5206598, by rfl⟩ : syracuseStep 6942131 = 10413197) B10413197
theorem B1371595 : Blo 1217426 1371595 := bstep (se 1 (by rfl) ⟨1028696, by rfl⟩ : syracuseStep 1371595 = 2057393) B2057393
theorem B2739671 : Blo 1217426 2739671 := bstep (se 1 (by rfl) ⟨2054753, by rfl⟩ : syracuseStep 2739671 = 4109507) B4109507
theorem B2346455 : Blo 1217426 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B1371703 : Blo 1217426 1371703 := bstep (se 1 (by rfl) ⟨1028777, by rfl⟩ : syracuseStep 1371703 = 2057555) B2057555
theorem B11701853 : Blo 1217426 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B6164099 : Blo 1217426 6164099 := bstep (se 1 (by rfl) ⟨4623074, by rfl⟩ : syracuseStep 6164099 = 9246149) B9246149
theorem B2739851 : Blo 1217426 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B2739905 : Blo 1217426 2739905 := bstep (se 2 (by rfl) ⟨1027464, by rfl⟩ : syracuseStep 2739905 = 2054929) B2054929
theorem B2084555 : Blo 1217426 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B7802669 : Blo 1217426 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B5009203 : Blo 1217426 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B2780993 : Blo 1217426 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B2781067 : Blo 1217426 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B2740121 : Blo 1217426 2740121 := bstep (se 2 (by rfl) ⟨1027545, by rfl⟩ : syracuseStep 2740121 = 2055091) B2055091
theorem B2740211 : Blo 1217426 2740211 := bstep (se 1 (by rfl) ⟨2055158, by rfl⟩ : syracuseStep 2740211 = 4110317) B4110317
theorem B2314241 : Blo 1217426 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B2740247 : Blo 1217426 2740247 := bstep (se 1 (by rfl) ⟨2055185, by rfl⟩ : syracuseStep 2740247 = 4110371) B4110371
theorem B5009501 : Blo 1217426 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B11260055 : Blo 1217426 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B3084439 : Blo 1217426 3084439 := bstep (se 1 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 3084439 = 4626659) B4626659
theorem B4165825 : Blo 1217426 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B2601163 : Blo 1217426 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B2740427 : Blo 1217426 2740427 := bstep (se 1 (by rfl) ⟨2055320, by rfl⟩ : syracuseStep 2740427 = 4110641) B4110641
theorem B2740481 : Blo 1217426 2740481 := bstep (se 2 (by rfl) ⟨1027680, by rfl⟩ : syracuseStep 2740481 = 2055361) B2055361
theorem B2314507 : Blo 1217426 2314507 := bstep (se 1 (by rfl) ⟨1735880, by rfl⟩ : syracuseStep 2314507 = 3471761) B3471761
theorem B4624685 : Blo 1217426 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B4624715 : Blo 1217426 4624715 := bstep (se 1 (by rfl) ⟨3468536, by rfl⟩ : syracuseStep 4624715 = 6937073) B6937073
theorem B7909811 : Blo 1217426 7909811 := bstep (se 1 (by rfl) ⟨5932358, by rfl⟩ : syracuseStep 7909811 = 11864717) B11864717
theorem B2740697 : Blo 1217426 2740697 := bstep (se 2 (by rfl) ⟨1027761, by rfl⟩ : syracuseStep 2740697 = 2055523) B2055523
theorem B2601497 : Blo 1217426 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B2740787 : Blo 1217426 2740787 := bstep (se 1 (by rfl) ⟨2055590, by rfl⟩ : syracuseStep 2740787 = 4111181) B4111181
theorem B15012427 : Blo 1217426 15012427 := bstep (se 1 (by rfl) ⟨11259320, by rfl⟩ : syracuseStep 15012427 = 22518641) B22518641
theorem B3084875 : Blo 1217426 3084875 := bstep (se 1 (by rfl) ⟨2313656, by rfl⟩ : syracuseStep 3084875 = 4627313) B4627313
theorem B2740823 : Blo 1217426 2740823 := bstep (se 1 (by rfl) ⟨2055617, by rfl⟩ : syracuseStep 2740823 = 4111235) B4111235
theorem B94958173 : Blo 1217426 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B2314955 : Blo 1217426 2314955 := bstep (se 1 (by rfl) ⟨1736216, by rfl⟩ : syracuseStep 2314955 = 3472433) B3472433
theorem B4690649 : Blo 1217426 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B4109021 : Blo 1217426 4109021 := bstep (se 3 (by rfl) ⟨770441, by rfl⟩ : syracuseStep 4109021 = 1540883) B1540883
theorem B2741003 : Blo 1217426 2741003 := bstep (se 1 (by rfl) ⟨2055752, by rfl⟩ : syracuseStep 2741003 = 4111505) B4111505
theorem B6935341 : Blo 1217426 6935341 := bstep (se 3 (by rfl) ⟨1300376, by rfl⟩ : syracuseStep 6935341 = 2600753) B2600753
theorem B3470131 : Blo 1217426 3470131 := bstep (se 1 (by rfl) ⟨2602598, by rfl⟩ : syracuseStep 3470131 = 5205197) B5205197
theorem B2741057 : Blo 1217426 2741057 := bstep (se 2 (by rfl) ⟨1027896, by rfl⟩ : syracuseStep 2741057 = 2055793) B2055793
theorem B6255425 : Blo 1217426 6255425 := bstep (se 2 (by rfl) ⟨2345784, by rfl⟩ : syracuseStep 6255425 = 4691569) B4691569
theorem B16896869 : Blo 1217426 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B6943589 : Blo 1217426 6943589 := bstep (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) B1301923
theorem B1217431 : Blo 1217426 1217431 := bstep (se 1 (by rfl) ⟨913073, by rfl⟩ : syracuseStep 1217431 = 1826147) B1826147
theorem B1217451 : Blo 1217426 1217451 := bstep (se 1 (by rfl) ⟨913088, by rfl⟩ : syracuseStep 1217451 = 1826177) B1826177
theorem B1217463 : Blo 1217426 1217463 := bstep (se 1 (by rfl) ⟨913097, by rfl⟩ : syracuseStep 1217463 = 1826195) B1826195
theorem B3085249 : Blo 1217426 3085249 := bstep (se 2 (by rfl) ⟨1156968, by rfl⟩ : syracuseStep 3085249 = 2313937) B2313937
theorem B1217483 : Blo 1217426 1217483 := bstep (se 1 (by rfl) ⟨913112, by rfl⟩ : syracuseStep 1217483 = 1826225) B1826225
theorem B1217495 : Blo 1217426 1217495 := bstep (se 1 (by rfl) ⟨913121, by rfl⟩ : syracuseStep 1217495 = 1826243) B1826243
theorem B4625369 : Blo 1217426 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B1217515 : Blo 1217426 1217515 := bstep (se 1 (by rfl) ⟨913136, by rfl⟩ : syracuseStep 1217515 = 1826273) B1826273
theorem B1217527 : Blo 1217426 1217527 := bstep (se 1 (by rfl) ⟨913145, by rfl⟩ : syracuseStep 1217527 = 1826291) B1826291
theorem B1217547 : Blo 1217426 1217547 := bstep (se 1 (by rfl) ⟨913160, by rfl⟩ : syracuseStep 1217547 = 1826321) B1826321
theorem B1217559 : Blo 1217426 1217559 := bstep (se 1 (by rfl) ⟨913169, by rfl⟩ : syracuseStep 1217559 = 1826339) B1826339
theorem B3470359 : Blo 1217426 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B2741273 : Blo 1217426 2741273 := bstep (se 2 (by rfl) ⟨1027977, by rfl⟩ : syracuseStep 2741273 = 2055955) B2055955
theorem B1217579 : Blo 1217426 1217579 := bstep (se 1 (by rfl) ⟨913184, by rfl⟩ : syracuseStep 1217579 = 1826369) B1826369
theorem B1217591 : Blo 1217426 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B1217611 : Blo 1217426 1217611 := bstep (se 1 (by rfl) ⟨913208, by rfl⟩ : syracuseStep 1217611 = 1826417) B1826417
theorem B1217623 : Blo 1217426 1217623 := bstep (se 1 (by rfl) ⟨913217, by rfl⟩ : syracuseStep 1217623 = 1826435) B1826435
theorem B1217643 : Blo 1217426 1217643 := bstep (se 1 (by rfl) ⟨913232, by rfl⟩ : syracuseStep 1217643 = 1826465) B1826465
theorem B2741363 : Blo 1217426 2741363 := bstep (se 1 (by rfl) ⟨2056022, by rfl⟩ : syracuseStep 2741363 = 4112045) B4112045
theorem B1217655 : Blo 1217426 1217655 := bstep (se 1 (by rfl) ⟨913241, by rfl⟩ : syracuseStep 1217655 = 1826483) B1826483
theorem B1217675 : Blo 1217426 1217675 := bstep (se 1 (by rfl) ⟨913256, by rfl⟩ : syracuseStep 1217675 = 1826513) B1826513
theorem B1217687 : Blo 1217426 1217687 := bstep (se 1 (by rfl) ⟨913265, by rfl⟩ : syracuseStep 1217687 = 1826531) B1826531
theorem B13874327 : Blo 1217426 13874327 := bstep (se 1 (by rfl) ⟨10405745, by rfl⟩ : syracuseStep 13874327 = 20811491) B20811491
theorem B2741399 : Blo 1217426 2741399 := bstep (se 1 (by rfl) ⟨2056049, by rfl⟩ : syracuseStep 2741399 = 4112099) B4112099
theorem B1217707 : Blo 1217426 1217707 := bstep (se 1 (by rfl) ⟨913280, by rfl⟩ : syracuseStep 1217707 = 1826561) B1826561
theorem B1217719 : Blo 1217426 1217719 := bstep (se 1 (by rfl) ⟨913289, by rfl⟩ : syracuseStep 1217719 = 1826579) B1826579
theorem B1217739 : Blo 1217426 1217739 := bstep (se 1 (by rfl) ⟨913304, by rfl⟩ : syracuseStep 1217739 = 1826609) B1826609
theorem B1217751 : Blo 1217426 1217751 := bstep (se 1 (by rfl) ⟨913313, by rfl⟩ : syracuseStep 1217751 = 1826627) B1826627
theorem B1217771 : Blo 1217426 1217771 := bstep (se 1 (by rfl) ⟨913328, by rfl⟩ : syracuseStep 1217771 = 1826657) B1826657
theorem B1217783 : Blo 1217426 1217783 := bstep (se 1 (by rfl) ⟨913337, by rfl⟩ : syracuseStep 1217783 = 1826675) B1826675
theorem B1217803 : Blo 1217426 1217803 := bstep (se 1 (by rfl) ⟨913352, by rfl⟩ : syracuseStep 1217803 = 1826705) B1826705
theorem B1217815 : Blo 1217426 1217815 := bstep (se 1 (by rfl) ⟨913361, by rfl⟩ : syracuseStep 1217815 = 1826723) B1826723
theorem B4625687 : Blo 1217426 4625687 := bstep (se 1 (by rfl) ⟨3469265, by rfl⟩ : syracuseStep 4625687 = 6938531) B6938531
theorem B1217835 : Blo 1217426 1217835 := bstep (se 1 (by rfl) ⟨913376, by rfl⟩ : syracuseStep 1217835 = 1826753) B1826753
theorem B1217847 : Blo 1217426 1217847 := bstep (se 1 (by rfl) ⟨913385, by rfl⟩ : syracuseStep 1217847 = 1826771) B1826771
theorem B1217867 : Blo 1217426 1217867 := bstep (se 1 (by rfl) ⟨913400, by rfl⟩ : syracuseStep 1217867 = 1826801) B1826801
theorem B9876811 : Blo 1217426 9876811 := bstep (se 1 (by rfl) ⟨7407608, by rfl⟩ : syracuseStep 9876811 = 14815217) B14815217
theorem B2741579 : Blo 1217426 2741579 := bstep (se 1 (by rfl) ⟨2056184, by rfl⟩ : syracuseStep 2741579 = 4112369) B4112369
theorem B1217879 : Blo 1217426 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B1217899 : Blo 1217426 1217899 := bstep (se 1 (by rfl) ⟨913424, by rfl⟩ : syracuseStep 1217899 = 1826849) B1826849
theorem B1217911 : Blo 1217426 1217911 := bstep (se 1 (by rfl) ⟨913433, by rfl⟩ : syracuseStep 1217911 = 1826867) B1826867
theorem B2741633 : Blo 1217426 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B1217931 : Blo 1217426 1217931 := bstep (se 1 (by rfl) ⟨913448, by rfl⟩ : syracuseStep 1217931 = 1826897) B1826897
theorem B70268309 : Blo 1217426 70268309 := bstep (se 6 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 70268309 = 3293827) B3293827
theorem B3954071 : Blo 1217426 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B1217943 : Blo 1217426 1217943 := bstep (se 1 (by rfl) ⟨913457, by rfl⟩ : syracuseStep 1217943 = 1826915) B1826915
theorem B1217963 : Blo 1217426 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B1217975 : Blo 1217426 1217975 := bstep (se 1 (by rfl) ⟨913481, by rfl⟩ : syracuseStep 1217975 = 1826963) B1826963
theorem B1217995 : Blo 1217426 1217995 := bstep (se 1 (by rfl) ⟨913496, by rfl⟩ : syracuseStep 1217995 = 1826993) B1826993
theorem B1218007 : Blo 1217426 1218007 := bstep (se 1 (by rfl) ⟨913505, by rfl⟩ : syracuseStep 1218007 = 1827011) B1827011
theorem B1218027 : Blo 1217426 1218027 := bstep (se 1 (by rfl) ⟨913520, by rfl⟩ : syracuseStep 1218027 = 1827041) B1827041
theorem B1218039 : Blo 1217426 1218039 := bstep (se 1 (by rfl) ⟨913529, by rfl⟩ : syracuseStep 1218039 = 1827059) B1827059
theorem B1218059 : Blo 1217426 1218059 := bstep (se 1 (by rfl) ⟨913544, by rfl⟩ : syracuseStep 1218059 = 1827089) B1827089
theorem B1218071 : Blo 1217426 1218071 := bstep (se 1 (by rfl) ⟨913553, by rfl⟩ : syracuseStep 1218071 = 1827107) B1827107
theorem B3085847 : Blo 1217426 3085847 := bstep (se 1 (by rfl) ⟨2314385, by rfl⟩ : syracuseStep 3085847 = 4628771) B4628771
theorem B1218091 : Blo 1217426 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1218103 : Blo 1217426 1218103 := bstep (se 1 (by rfl) ⟨913577, by rfl⟩ : syracuseStep 1218103 = 1827155) B1827155
theorem B1218123 : Blo 1217426 1218123 := bstep (se 1 (by rfl) ⟨913592, by rfl⟩ : syracuseStep 1218123 = 1827185) B1827185
theorem B2504267 : Blo 1217426 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B1218135 : Blo 1217426 1218135 := bstep (se 1 (by rfl) ⟨913601, by rfl⟩ : syracuseStep 1218135 = 1827203) B1827203
theorem B2741849 : Blo 1217426 2741849 := bstep (se 2 (by rfl) ⟨1028193, by rfl⟩ : syracuseStep 2741849 = 2056387) B2056387
theorem B3905117 : Blo 1217426 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B10409573 : Blo 1217426 10409573 := bstep (se 4 (by rfl) ⟨975897, by rfl⟩ : syracuseStep 10409573 = 1951795) B1951795
theorem B1218155 : Blo 1217426 1218155 := bstep (se 1 (by rfl) ⟨913616, by rfl⟩ : syracuseStep 1218155 = 1827233) B1827233
theorem B1218167 : Blo 1217426 1218167 := bstep (se 1 (by rfl) ⟨913625, by rfl⟩ : syracuseStep 1218167 = 1827251) B1827251
theorem B1218187 : Blo 1217426 1218187 := bstep (se 1 (by rfl) ⟨913640, by rfl⟩ : syracuseStep 1218187 = 1827281) B1827281
theorem B1218199 : Blo 1217426 1218199 := bstep (se 1 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 1218199 = 1827299) B1827299
theorem B1218219 : Blo 1217426 1218219 := bstep (se 1 (by rfl) ⟨913664, by rfl⟩ : syracuseStep 1218219 = 1827329) B1827329
theorem B2741939 : Blo 1217426 2741939 := bstep (se 1 (by rfl) ⟨2056454, by rfl⟩ : syracuseStep 2741939 = 4112909) B4112909
theorem B1218231 : Blo 1217426 1218231 := bstep (se 1 (by rfl) ⟨913673, by rfl⟩ : syracuseStep 1218231 = 1827347) B1827347
theorem B1218251 : Blo 1217426 1218251 := bstep (se 1 (by rfl) ⟨913688, by rfl⟩ : syracuseStep 1218251 = 1827377) B1827377
theorem B1218263 : Blo 1217426 1218263 := bstep (se 1 (by rfl) ⟨913697, by rfl⟩ : syracuseStep 1218263 = 1827395) B1827395
theorem B2741975 : Blo 1217426 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B1218283 : Blo 1217426 1218283 := bstep (se 1 (by rfl) ⟨913712, by rfl⟩ : syracuseStep 1218283 = 1827425) B1827425
theorem B1218295 : Blo 1217426 1218295 := bstep (se 1 (by rfl) ⟨913721, by rfl⟩ : syracuseStep 1218295 = 1827443) B1827443
theorem B1218315 : Blo 1217426 1218315 := bstep (se 1 (by rfl) ⟨913736, by rfl⟩ : syracuseStep 1218315 = 1827473) B1827473
theorem B7124753 : Blo 1217426 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B1218327 : Blo 1217426 1218327 := bstep (se 1 (by rfl) ⟨913745, by rfl⟩ : syracuseStep 1218327 = 1827491) B1827491
theorem B1218347 : Blo 1217426 1218347 := bstep (se 1 (by rfl) ⟨913760, by rfl⟩ : syracuseStep 1218347 = 1827521) B1827521
theorem B1218359 : Blo 1217426 1218359 := bstep (se 1 (by rfl) ⟨913769, by rfl⟩ : syracuseStep 1218359 = 1827539) B1827539
theorem B16684865 : Blo 1217426 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B4110155 : Blo 1217426 4110155 := bstep (se 1 (by rfl) ⟨3082616, by rfl⟩ : syracuseStep 4110155 = 6165233) B6165233
theorem B1218379 : Blo 1217426 1218379 := bstep (se 1 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 1218379 = 1827569) B1827569
theorem B1218391 : Blo 1217426 1218391 := bstep (se 1 (by rfl) ⟨913793, by rfl⟩ : syracuseStep 1218391 = 1827587) B1827587
theorem B1218411 : Blo 1217426 1218411 := bstep (se 1 (by rfl) ⟨913808, by rfl⟩ : syracuseStep 1218411 = 1827617) B1827617
theorem B1218423 : Blo 1217426 1218423 := bstep (se 1 (by rfl) ⟨913817, by rfl⟩ : syracuseStep 1218423 = 1827635) B1827635
theorem B1218443 : Blo 1217426 1218443 := bstep (se 1 (by rfl) ⟨913832, by rfl⟩ : syracuseStep 1218443 = 1827665) B1827665
theorem B2742155 : Blo 1217426 2742155 := bstep (se 1 (by rfl) ⟨2056616, by rfl⟩ : syracuseStep 2742155 = 4113233) B4113233
theorem B1218455 : Blo 1217426 1218455 := bstep (se 1 (by rfl) ⟨913841, by rfl⟩ : syracuseStep 1218455 = 1827683) B1827683
theorem B1218475 : Blo 1217426 1218475 := bstep (se 1 (by rfl) ⟨913856, by rfl⟩ : syracuseStep 1218475 = 1827713) B1827713
theorem B4626355 : Blo 1217426 4626355 := bstep (se 1 (by rfl) ⟨3469766, by rfl⟩ : syracuseStep 4626355 = 6939533) B6939533
theorem B1218487 : Blo 1217426 1218487 := bstep (se 1 (by rfl) ⟨913865, by rfl⟩ : syracuseStep 1218487 = 1827731) B1827731
theorem B2742209 : Blo 1217426 2742209 := bstep (se 2 (by rfl) ⟨1028328, by rfl⟩ : syracuseStep 2742209 = 2056657) B2056657
theorem B1218507 : Blo 1217426 1218507 := bstep (se 1 (by rfl) ⟨913880, by rfl⟩ : syracuseStep 1218507 = 1827761) B1827761
theorem B1218519 : Blo 1217426 1218519 := bstep (se 1 (by rfl) ⟨913889, by rfl⟩ : syracuseStep 1218519 = 1827779) B1827779
theorem B1218539 : Blo 1217426 1218539 := bstep (se 1 (by rfl) ⟨913904, by rfl⟩ : syracuseStep 1218539 = 1827809) B1827809
theorem B1218551 : Blo 1217426 1218551 := bstep (se 1 (by rfl) ⟨913913, by rfl⟩ : syracuseStep 1218551 = 1827827) B1827827
theorem B2603009 : Blo 1217426 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B5208067 : Blo 1217426 5208067 := bstep (se 1 (by rfl) ⟨3906050, by rfl⟩ : syracuseStep 5208067 = 7812101) B7812101
theorem B1218571 : Blo 1217426 1218571 := bstep (se 1 (by rfl) ⟨913928, by rfl⟩ : syracuseStep 1218571 = 1827857) B1827857
theorem B1218583 : Blo 1217426 1218583 := bstep (se 1 (by rfl) ⟨913937, by rfl⟩ : syracuseStep 1218583 = 1827875) B1827875
theorem B1218603 : Blo 1217426 1218603 := bstep (se 1 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 1218603 = 1827905) B1827905
theorem B1218615 : Blo 1217426 1218615 := bstep (se 1 (by rfl) ⟨913961, by rfl⟩ : syracuseStep 1218615 = 1827923) B1827923
theorem B1218635 : Blo 1217426 1218635 := bstep (se 1 (by rfl) ⟨913976, by rfl⟩ : syracuseStep 1218635 = 1827953) B1827953
theorem B1218647 : Blo 1217426 1218647 := bstep (se 1 (by rfl) ⟨913985, by rfl⟩ : syracuseStep 1218647 = 1827971) B1827971
theorem B4110425 : Blo 1217426 4110425 := bstep (se 2 (by rfl) ⟨1541409, by rfl⟩ : syracuseStep 4110425 = 3082819) B3082819
theorem B3127385 : Blo 1217426 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B1218667 : Blo 1217426 1218667 := bstep (se 1 (by rfl) ⟨914000, by rfl⟩ : syracuseStep 1218667 = 1828001) B1828001
theorem B1218679 : Blo 1217426 1218679 := bstep (se 1 (by rfl) ⟨914009, by rfl⟩ : syracuseStep 1218679 = 1828019) B1828019
theorem B1218699 : Blo 1217426 1218699 := bstep (se 1 (by rfl) ⟨914024, by rfl⟩ : syracuseStep 1218699 = 1828049) B1828049
theorem B1218711 : Blo 1217426 1218711 := bstep (se 1 (by rfl) ⟨914033, by rfl⟩ : syracuseStep 1218711 = 1828067) B1828067
theorem B2742425 : Blo 1217426 2742425 := bstep (se 2 (by rfl) ⟨1028409, by rfl⟩ : syracuseStep 2742425 = 2056819) B2056819
theorem B1218731 : Blo 1217426 1218731 := bstep (se 1 (by rfl) ⟨914048, by rfl⟩ : syracuseStep 1218731 = 1828097) B1828097
theorem B1218743 : Blo 1217426 1218743 := bstep (se 1 (by rfl) ⟨914057, by rfl⟩ : syracuseStep 1218743 = 1828115) B1828115
theorem B1218763 : Blo 1217426 1218763 := bstep (se 1 (by rfl) ⟨914072, by rfl⟩ : syracuseStep 1218763 = 1828145) B1828145
theorem B1218775 : Blo 1217426 1218775 := bstep (se 1 (by rfl) ⟨914081, by rfl⟩ : syracuseStep 1218775 = 1828163) B1828163
theorem B1218795 : Blo 1217426 1218795 := bstep (se 1 (by rfl) ⟨914096, by rfl⟩ : syracuseStep 1218795 = 1828193) B1828193
theorem B2742515 : Blo 1217426 2742515 := bstep (se 1 (by rfl) ⟨2056886, by rfl⟩ : syracuseStep 2742515 = 4113773) B4113773
theorem B1218807 : Blo 1217426 1218807 := bstep (se 1 (by rfl) ⟨914105, by rfl⟩ : syracuseStep 1218807 = 1828211) B1828211
theorem B15644933 : Blo 1217426 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B1218827 : Blo 1217426 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B2054423 : Blo 1217426 2054423 := bstep (se 1 (by rfl) ⟨1540817, by rfl⟩ : syracuseStep 2054423 = 3081635) B3081635
theorem B1218839 : Blo 1217426 1218839 := bstep (se 1 (by rfl) ⟨914129, by rfl⟩ : syracuseStep 1218839 = 1828259) B1828259
theorem B2742551 : Blo 1217426 2742551 := bstep (se 1 (by rfl) ⟨2056913, by rfl⟩ : syracuseStep 2742551 = 4113827) B4113827
theorem B1218859 : Blo 1217426 1218859 := bstep (se 1 (by rfl) ⟨914144, by rfl⟩ : syracuseStep 1218859 = 1828289) B1828289
theorem B1218871 : Blo 1217426 1218871 := bstep (se 1 (by rfl) ⟨914153, by rfl⟩ : syracuseStep 1218871 = 1828307) B1828307
theorem B3086657 : Blo 1217426 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B1218891 : Blo 1217426 1218891 := bstep (se 1 (by rfl) ⟨914168, by rfl⟩ : syracuseStep 1218891 = 1828337) B1828337
theorem B1218903 : Blo 1217426 1218903 := bstep (se 1 (by rfl) ⟨914177, by rfl⟩ : syracuseStep 1218903 = 1828355) B1828355
theorem B1218923 : Blo 1217426 1218923 := bstep (se 1 (by rfl) ⟨914192, by rfl⟩ : syracuseStep 1218923 = 1828385) B1828385
theorem B1218935 : Blo 1217426 1218935 := bstep (se 1 (by rfl) ⟨914201, by rfl⟩ : syracuseStep 1218935 = 1828403) B1828403
theorem B1218955 : Blo 1217426 1218955 := bstep (se 1 (by rfl) ⟨914216, by rfl⟩ : syracuseStep 1218955 = 1828433) B1828433
theorem B2054551 : Blo 1217426 2054551 := bstep (se 1 (by rfl) ⟨1540913, by rfl⟩ : syracuseStep 2054551 = 3081827) B3081827
theorem B7805335 : Blo 1217426 7805335 := bstep (se 1 (by rfl) ⟨5854001, by rfl⟩ : syracuseStep 7805335 = 11708003) B11708003
theorem B1218967 : Blo 1217426 1218967 := bstep (se 1 (by rfl) ⟨914225, by rfl⟩ : syracuseStep 1218967 = 1828451) B1828451
theorem B1218987 : Blo 1217426 1218987 := bstep (se 1 (by rfl) ⟨914240, by rfl⟩ : syracuseStep 1218987 = 1828481) B1828481
theorem B1218999 : Blo 1217426 1218999 := bstep (se 1 (by rfl) ⟨914249, by rfl⟩ : syracuseStep 1218999 = 1828499) B1828499
theorem B2742731 : Blo 1217426 2742731 := bstep (se 1 (by rfl) ⟨2057048, by rfl⟩ : syracuseStep 2742731 = 4114097) B4114097
theorem B1219019 : Blo 1217426 1219019 := bstep (se 1 (by rfl) ⟨914264, by rfl⟩ : syracuseStep 1219019 = 1828529) B1828529
theorem B1219031 : Blo 1217426 1219031 := bstep (se 1 (by rfl) ⟨914273, by rfl⟩ : syracuseStep 1219031 = 1828547) B1828547
theorem B1219051 : Blo 1217426 1219051 := bstep (se 1 (by rfl) ⟨914288, by rfl⟩ : syracuseStep 1219051 = 1828577) B1828577
theorem B1219063 : Blo 1217426 1219063 := bstep (se 1 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 1219063 = 1828595) B1828595
theorem B2742785 : Blo 1217426 2742785 := bstep (se 2 (by rfl) ⟨1028544, by rfl⟩ : syracuseStep 2742785 = 2057089) B2057089
theorem B1219083 : Blo 1217426 1219083 := bstep (se 1 (by rfl) ⟨914312, by rfl⟩ : syracuseStep 1219083 = 1828625) B1828625
theorem B12040721 : Blo 1217426 12040721 := bstep (se 2 (by rfl) ⟨4515270, by rfl⟩ : syracuseStep 12040721 = 9030541) B9030541
theorem B1219095 : Blo 1217426 1219095 := bstep (se 1 (by rfl) ⟨914321, by rfl⟩ : syracuseStep 1219095 = 1828643) B1828643
theorem B1251883 : Blo 1217426 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1219115 : Blo 1217426 1219115 := bstep (se 1 (by rfl) ⟨914336, by rfl⟩ : syracuseStep 1219115 = 1828673) B1828673
theorem B1219127 : Blo 1217426 1219127 := bstep (se 1 (by rfl) ⟨914345, by rfl⟩ : syracuseStep 1219127 = 1828691) B1828691
theorem B1219147 : Blo 1217426 1219147 := bstep (se 1 (by rfl) ⟨914360, by rfl⟩ : syracuseStep 1219147 = 1828721) B1828721
theorem B1219159 : Blo 1217426 1219159 := bstep (se 1 (by rfl) ⟨914369, by rfl⟩ : syracuseStep 1219159 = 1828739) B1828739
theorem B1219179 : Blo 1217426 1219179 := bstep (se 1 (by rfl) ⟨914384, by rfl⟩ : syracuseStep 1219179 = 1828769) B1828769
theorem B1219191 : Blo 1217426 1219191 := bstep (se 1 (by rfl) ⟨914393, by rfl⟩ : syracuseStep 1219191 = 1828787) B1828787
theorem B1219211 : Blo 1217426 1219211 := bstep (se 1 (by rfl) ⟨914408, by rfl⟩ : syracuseStep 1219211 = 1828817) B1828817
theorem B1219223 : Blo 1217426 1219223 := bstep (se 1 (by rfl) ⟨914417, by rfl⟩ : syracuseStep 1219223 = 1828835) B1828835
theorem B1219243 : Blo 1217426 1219243 := bstep (se 1 (by rfl) ⟨914432, by rfl⟩ : syracuseStep 1219243 = 1828865) B1828865
theorem B1219255 : Blo 1217426 1219255 := bstep (se 1 (by rfl) ⟨914441, by rfl⟩ : syracuseStep 1219255 = 1828883) B1828883
theorem B1219275 : Blo 1217426 1219275 := bstep (se 1 (by rfl) ⟨914456, by rfl⟩ : syracuseStep 1219275 = 1828913) B1828913
theorem B1219287 : Blo 1217426 1219287 := bstep (se 1 (by rfl) ⟨914465, by rfl⟩ : syracuseStep 1219287 = 1828931) B1828931
theorem B2743001 : Blo 1217426 2743001 := bstep (se 2 (by rfl) ⟨1028625, by rfl⟩ : syracuseStep 2743001 = 2057251) B2057251
theorem B1219307 : Blo 1217426 1219307 := bstep (se 1 (by rfl) ⟨914480, by rfl⟩ : syracuseStep 1219307 = 1828961) B1828961
theorem B1219319 : Blo 1217426 1219319 := bstep (se 1 (by rfl) ⟨914489, by rfl⟩ : syracuseStep 1219319 = 1828979) B1828979
theorem B1219339 : Blo 1217426 1219339 := bstep (se 1 (by rfl) ⟨914504, by rfl⟩ : syracuseStep 1219339 = 1829009) B1829009
theorem B6421265 : Blo 1217426 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B4111127 : Blo 1217426 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B1219351 : Blo 1217426 1219351 := bstep (se 1 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 1219351 = 1829027) B1829027
theorem B1219371 : Blo 1217426 1219371 := bstep (se 1 (by rfl) ⟨914528, by rfl⟩ : syracuseStep 1219371 = 1829057) B1829057
theorem B2743091 : Blo 1217426 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B1219383 : Blo 1217426 1219383 := bstep (se 1 (by rfl) ⟨914537, by rfl⟩ : syracuseStep 1219383 = 1829075) B1829075
theorem B11123531 : Blo 1217426 11123531 := bstep (se 1 (by rfl) ⟨8342648, by rfl⟩ : syracuseStep 11123531 = 16685297) B16685297
theorem B1219403 : Blo 1217426 1219403 := bstep (se 1 (by rfl) ⟨914552, by rfl⟩ : syracuseStep 1219403 = 1829105) B1829105
theorem B2743127 : Blo 1217426 2743127 := bstep (se 1 (by rfl) ⟨2057345, by rfl⟩ : syracuseStep 2743127 = 4114691) B4114691
theorem B2603863 : Blo 1217426 2603863 := bstep (se 1 (by rfl) ⟨1952897, by rfl⟩ : syracuseStep 2603863 = 3905795) B3905795
theorem B3472217 : Blo 1217426 3472217 := bstep (se 2 (by rfl) ⟨1302081, by rfl⟩ : syracuseStep 3472217 = 2604163) B2604163
theorem B1219415 : Blo 1217426 1219415 := bstep (se 1 (by rfl) ⟨914561, by rfl⟩ : syracuseStep 1219415 = 1829123) B1829123
theorem B7412573 : Blo 1217426 7412573 := bstep (se 3 (by rfl) ⟨1389857, by rfl⟩ : syracuseStep 7412573 = 2779715) B2779715
theorem B1235863 : Blo 1217426 1235863 := bstep (se 1 (by rfl) ⟨926897, by rfl⟩ : syracuseStep 1235863 = 1853795) B1853795
theorem B10402739 : Blo 1217426 10402739 := bstep (se 1 (by rfl) ⟨7802054, by rfl⟩ : syracuseStep 10402739 = 15604109) B15604109
theorem B2055179 : Blo 1217426 2055179 := bstep (se 1 (by rfl) ⟨1541384, by rfl⟩ : syracuseStep 2055179 = 3082769) B3082769
theorem B2743307 : Blo 1217426 2743307 := bstep (se 1 (by rfl) ⟨2057480, by rfl⟩ : syracuseStep 2743307 = 4114961) B4114961
theorem B2743361 : Blo 1217426 2743361 := bstep (se 2 (by rfl) ⟨1028760, by rfl⟩ : syracuseStep 2743361 = 2057521) B2057521
theorem B1645655 : Blo 1217426 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B2055307 : Blo 1217426 2055307 := bstep (se 1 (by rfl) ⟨1541480, by rfl⟩ : syracuseStep 2055307 = 3082961) B3082961
theorem B4627601 : Blo 1217426 4627601 := bstep (se 2 (by rfl) ⟨1735350, by rfl⟩ : syracuseStep 4627601 = 3470701) B3470701
theorem B7404695 : Blo 1217426 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B1301675 : Blo 1217426 1301675 := bstep (se 1 (by rfl) ⟨976256, by rfl⟩ : syracuseStep 1301675 = 1952513) B1952513
theorem B10411213 : Blo 1217426 10411213 := bstep (se 3 (by rfl) ⟨1952102, by rfl⟩ : syracuseStep 10411213 = 3904205) B3904205
theorem B6167825 : Blo 1217426 6167825 := bstep (se 2 (by rfl) ⟨2312934, by rfl⟩ : syracuseStep 6167825 = 4625869) B4625869
theorem B2055449 : Blo 1217426 2055449 := bstep (se 2 (by rfl) ⟨770793, by rfl⟩ : syracuseStep 2055449 = 1541587) B1541587
theorem B2743577 : Blo 1217426 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B4111667 : Blo 1217426 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B9248093 : Blo 1217426 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B2743667 : Blo 1217426 2743667 := bstep (se 1 (by rfl) ⟨2057750, by rfl⟩ : syracuseStep 2743667 = 4115501) B4115501
theorem B2743703 : Blo 1217426 2743703 := bstep (se 1 (by rfl) ⟨2057777, by rfl⟩ : syracuseStep 2743703 = 4115555) B4115555
theorem B1826201 : Blo 1217426 1826201 := bstep (se 2 (by rfl) ⟨684825, by rfl⟩ : syracuseStep 1826201 = 1369651) B1369651
theorem B2055577 : Blo 1217426 2055577 := bstep (se 2 (by rfl) ⟨770841, by rfl⟩ : syracuseStep 2055577 = 1541683) B1541683
theorem B6167987 : Blo 1217426 6167987 := bstep (se 1 (by rfl) ⟨4625990, by rfl⟩ : syracuseStep 6167987 = 9251981) B9251981
theorem B1826315 : Blo 1217426 1826315 := bstep (se 1 (by rfl) ⟨1369736, by rfl⟩ : syracuseStep 1826315 = 2739473) B2739473
theorem B1826327 : Blo 1217426 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B4111937 : Blo 1217426 4111937 := bstep (se 2 (by rfl) ⟨1541976, by rfl⟩ : syracuseStep 4111937 = 3083953) B3083953
theorem B10157633 : Blo 1217426 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B1826393 : Blo 1217426 1826393 := bstep (se 2 (by rfl) ⟨684897, by rfl⟩ : syracuseStep 1826393 = 1369795) B1369795
theorem B1826507 : Blo 1217426 1826507 := bstep (se 1 (by rfl) ⟨1369880, by rfl⟩ : syracuseStep 1826507 = 2739761) B2739761
theorem B1826519 : Blo 1217426 1826519 := bstep (se 1 (by rfl) ⟨1369889, by rfl⟩ : syracuseStep 1826519 = 2739779) B2739779
theorem B1408727 : Blo 1217426 1408727 := bstep (se 1 (by rfl) ⟨1056545, by rfl⟩ : syracuseStep 1408727 = 2113091) B2113091
theorem B1826585 : Blo 1217426 1826585 := bstep (se 2 (by rfl) ⟨684969, by rfl⟩ : syracuseStep 1826585 = 1369939) B1369939
theorem B4628299 : Blo 1217426 4628299 := bstep (se 1 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 4628299 = 6942449) B6942449
theorem B1826699 : Blo 1217426 1826699 := bstep (se 1 (by rfl) ⟨1370024, by rfl⟩ : syracuseStep 1826699 = 2740049) B2740049
theorem B1826711 : Blo 1217426 1826711 := bstep (se 1 (by rfl) ⟨1370033, by rfl⟩ : syracuseStep 1826711 = 2740067) B2740067
theorem B2056151 : Blo 1217426 2056151 := bstep (se 1 (by rfl) ⟨1542113, by rfl⟩ : syracuseStep 2056151 = 3084227) B3084227
theorem B10403801 : Blo 1217426 10403801 := bstep (se 2 (by rfl) ⟨3901425, by rfl⟩ : syracuseStep 10403801 = 7802851) B7802851
theorem B1826777 : Blo 1217426 1826777 := bstep (se 2 (by rfl) ⟨685041, by rfl⟩ : syracuseStep 1826777 = 1370083) B1370083
theorem B1826831 : Blo 1217426 1826831 := bstep (se 1 (by rfl) ⟨1370123, by rfl⟩ : syracuseStep 1826831 = 2740247) B2740247
theorem B1826873 : Blo 1217426 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B1826951 : Blo 1217426 1826951 := bstep (se 1 (by rfl) ⟨1370213, by rfl⟩ : syracuseStep 1826951 = 2740427) B2740427
theorem B1826987 : Blo 1217426 1826987 := bstep (se 1 (by rfl) ⟨1370240, by rfl⟩ : syracuseStep 1826987 = 2740481) B2740481
theorem B1827017 : Blo 1217426 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B4112585 : Blo 1217426 4112585 := bstep (se 2 (by rfl) ⟨1542219, by rfl⟩ : syracuseStep 4112585 = 3084439) B3084439
theorem B5554433 : Blo 1217426 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1827131 : Blo 1217426 1827131 := bstep (se 1 (by rfl) ⟨1370348, by rfl⟩ : syracuseStep 1827131 = 2740697) B2740697
theorem B1827191 : Blo 1217426 1827191 := bstep (se 1 (by rfl) ⟨1370393, by rfl⟩ : syracuseStep 1827191 = 2740787) B2740787
theorem B2056583 : Blo 1217426 2056583 := bstep (se 1 (by rfl) ⟨1542437, by rfl⟩ : syracuseStep 2056583 = 3084875) B3084875
theorem B1827215 : Blo 1217426 1827215 := bstep (se 1 (by rfl) ⟨1370411, by rfl⟩ : syracuseStep 1827215 = 2740823) B2740823
theorem B1827257 : Blo 1217426 1827257 := bstep (se 2 (by rfl) ⟨685221, by rfl⟩ : syracuseStep 1827257 = 1370443) B1370443
theorem B1827335 : Blo 1217426 1827335 := bstep (se 1 (by rfl) ⟨1370501, by rfl⟩ : syracuseStep 1827335 = 2741003) B2741003
theorem B2196001 : Blo 1217426 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B1827371 : Blo 1217426 1827371 := bstep (se 1 (by rfl) ⟨1370528, by rfl⟩ : syracuseStep 1827371 = 2741057) B2741057
theorem B11264579 : Blo 1217426 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B4629059 : Blo 1217426 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B1827401 : Blo 1217426 1827401 := bstep (se 2 (by rfl) ⟨685275, by rfl⟩ : syracuseStep 1827401 = 1370551) B1370551
theorem B1827515 : Blo 1217426 1827515 := bstep (se 1 (by rfl) ⟨1370636, by rfl⟩ : syracuseStep 1827515 = 2741273) B2741273
theorem B1827575 : Blo 1217426 1827575 := bstep (se 1 (by rfl) ⟨1370681, by rfl⟩ : syracuseStep 1827575 = 2741363) B2741363
theorem B9249551 : Blo 1217426 9249551 := bstep (se 1 (by rfl) ⟨6937163, by rfl⟩ : syracuseStep 9249551 = 13874327) B13874327
theorem B1827599 : Blo 1217426 1827599 := bstep (se 1 (by rfl) ⟨1370699, by rfl⟩ : syracuseStep 1827599 = 2741399) B2741399
theorem B1827641 : Blo 1217426 1827641 := bstep (se 2 (by rfl) ⟨685365, by rfl⟩ : syracuseStep 1827641 = 1370731) B1370731
theorem B1827719 : Blo 1217426 1827719 := bstep (se 1 (by rfl) ⟨1370789, by rfl⟩ : syracuseStep 1827719 = 2741579) B2741579
theorem B4113287 : Blo 1217426 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B1541035 : Blo 1217426 1541035 := bstep (se 1 (by rfl) ⟨1155776, by rfl⟩ : syracuseStep 1541035 = 2311553) B2311553
theorem B1827755 : Blo 1217426 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B1827785 : Blo 1217426 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B2057231 : Blo 1217426 2057231 := bstep (se 1 (by rfl) ⟨1542923, by rfl⟩ : syracuseStep 2057231 = 3085847) B3085847
theorem B1827899 : Blo 1217426 1827899 := bstep (se 1 (by rfl) ⟨1370924, by rfl⟩ : syracuseStep 1827899 = 2741849) B2741849
theorem B6939715 : Blo 1217426 6939715 := bstep (se 1 (by rfl) ⟨5204786, by rfl⟩ : syracuseStep 6939715 = 10409573) B10409573
theorem B3753047 : Blo 1217426 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B1827959 : Blo 1217426 1827959 := bstep (se 1 (by rfl) ⟨1370969, by rfl⟩ : syracuseStep 1827959 = 2741939) B2741939
theorem B1541263 : Blo 1217426 1541263 := bstep (se 1 (by rfl) ⟨1155947, by rfl⟩ : syracuseStep 1541263 = 2311895) B2311895
theorem B1827983 : Blo 1217426 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B1828025 : Blo 1217426 1828025 := bstep (se 2 (by rfl) ⟨685509, by rfl⟩ : syracuseStep 1828025 = 1371019) B1371019
theorem B4113665 : Blo 1217426 4113665 := bstep (se 2 (by rfl) ⟨1542624, by rfl⟩ : syracuseStep 4113665 = 3085249) B3085249
theorem B1828103 : Blo 1217426 1828103 := bstep (se 1 (by rfl) ⟨1371077, by rfl⟩ : syracuseStep 1828103 = 2742155) B2742155
theorem B1828139 : Blo 1217426 1828139 := bstep (se 1 (by rfl) ⟨1371104, by rfl⟩ : syracuseStep 1828139 = 2742209) B2742209
theorem B2196779 : Blo 1217426 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B2639147 : Blo 1217426 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B9258299 : Blo 1217426 9258299 := bstep (se 1 (by rfl) ⟨6943724, by rfl⟩ : syracuseStep 9258299 = 13887449) B13887449
theorem B1828169 : Blo 1217426 1828169 := bstep (se 2 (by rfl) ⟨685563, by rfl⟩ : syracuseStep 1828169 = 1371127) B1371127
theorem B4392377 : Blo 1217426 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B1828283 : Blo 1217426 1828283 := bstep (se 1 (by rfl) ⟨1371212, by rfl⟩ : syracuseStep 1828283 = 2742425) B2742425
theorem B1828343 : Blo 1217426 1828343 := bstep (se 1 (by rfl) ⟨1371257, by rfl⟩ : syracuseStep 1828343 = 2742515) B2742515
theorem B10429955 : Blo 1217426 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B1369615 : Blo 1217426 1369615 := bstep (se 1 (by rfl) ⟨1027211, by rfl⟩ : syracuseStep 1369615 = 2054423) B2054423
theorem B1828367 : Blo 1217426 1828367 := bstep (se 1 (by rfl) ⟨1371275, by rfl⟩ : syracuseStep 1828367 = 2742551) B2742551
theorem B2057771 : Blo 1217426 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B1828409 : Blo 1217426 1828409 := bstep (se 2 (by rfl) ⟨685653, by rfl⟩ : syracuseStep 1828409 = 1371307) B1371307
theorem B3081847 : Blo 1217426 3081847 := bstep (se 1 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 3081847 = 4622771) B4622771
theorem B1828487 : Blo 1217426 1828487 := bstep (se 1 (by rfl) ⟨1371365, by rfl⟩ : syracuseStep 1828487 = 2742731) B2742731
theorem B1828523 : Blo 1217426 1828523 := bstep (se 1 (by rfl) ⟨1371392, by rfl⟩ : syracuseStep 1828523 = 2742785) B2742785
theorem B1828553 : Blo 1217426 1828553 := bstep (se 2 (by rfl) ⟨685707, by rfl⟩ : syracuseStep 1828553 = 1371415) B1371415
theorem B5203693 : Blo 1217426 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B1828667 : Blo 1217426 1828667 := bstep (se 1 (by rfl) ⟨1371500, by rfl⟩ : syracuseStep 1828667 = 2743001) B2743001
theorem B9881459 : Blo 1217426 9881459 := bstep (se 1 (by rfl) ⟨7411094, by rfl⟩ : syracuseStep 9881459 = 14822189) B14822189
theorem B1542007 : Blo 1217426 1542007 := bstep (se 1 (by rfl) ⟨1156505, by rfl⟩ : syracuseStep 1542007 = 2313011) B2313011
theorem B1828727 : Blo 1217426 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B7415687 : Blo 1217426 7415687 := bstep (se 1 (by rfl) ⟨5561765, by rfl⟩ : syracuseStep 7415687 = 11123531) B11123531
theorem B1828751 : Blo 1217426 1828751 := bstep (se 1 (by rfl) ⟨1371563, by rfl⟩ : syracuseStep 1828751 = 2743127) B2743127
theorem B4941715 : Blo 1217426 4941715 := bstep (se 1 (by rfl) ⟨3706286, by rfl⟩ : syracuseStep 4941715 = 7412573) B7412573
theorem B5203865 : Blo 1217426 5203865 := bstep (se 2 (by rfl) ⟨1951449, by rfl⟩ : syracuseStep 5203865 = 3902899) B3902899
theorem B1828793 : Blo 1217426 1828793 := bstep (se 2 (by rfl) ⟨685797, by rfl⟩ : syracuseStep 1828793 = 1371595) B1371595
theorem B1370119 : Blo 1217426 1370119 := bstep (se 1 (by rfl) ⟨1027589, by rfl⟩ : syracuseStep 1370119 = 2055179) B2055179
theorem B1828871 : Blo 1217426 1828871 := bstep (se 1 (by rfl) ⟨1371653, by rfl⟩ : syracuseStep 1828871 = 2743307) B2743307
theorem B3082283 : Blo 1217426 3082283 := bstep (se 1 (by rfl) ⟨2311712, by rfl⟩ : syracuseStep 3082283 = 4623425) B4623425
theorem B18999341 : Blo 1217426 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B4114475 : Blo 1217426 4114475 := bstep (se 1 (by rfl) ⟨3085856, by rfl⟩ : syracuseStep 4114475 = 6171713) B6171713
theorem B1828907 : Blo 1217426 1828907 := bstep (se 1 (by rfl) ⟨1371680, by rfl⟩ : syracuseStep 1828907 = 2743361) B2743361
theorem B1828937 : Blo 1217426 1828937 := bstep (se 2 (by rfl) ⟨685851, by rfl⟩ : syracuseStep 1828937 = 1371703) B1371703
theorem B2312327 : Blo 1217426 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B16681133 : Blo 1217426 16681133 := bstep (se 3 (by rfl) ⟨3127712, by rfl⟩ : syracuseStep 16681133 = 6255425) B6255425
theorem B7415981 : Blo 1217426 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B1370299 : Blo 1217426 1370299 := bstep (se 1 (by rfl) ⟨1027724, by rfl⟩ : syracuseStep 1370299 = 2055449) B2055449
theorem B1542331 : Blo 1217426 1542331 := bstep (se 1 (by rfl) ⟨1156748, by rfl⟩ : syracuseStep 1542331 = 2313497) B2313497
theorem B1829051 : Blo 1217426 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B1829111 : Blo 1217426 1829111 := bstep (se 1 (by rfl) ⟨1371833, by rfl⟩ : syracuseStep 1829111 = 2743667) B2743667
theorem B1829135 : Blo 1217426 1829135 := bstep (se 1 (by rfl) ⟨1371851, by rfl⟩ : syracuseStep 1829135 = 2743703) B2743703
theorem B7801235 : Blo 1217426 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B6678937 : Blo 1217426 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B6171065 : Blo 1217426 6171065 := bstep (se 2 (by rfl) ⟨2314149, by rfl⟩ : syracuseStep 6171065 = 4628299) B4628299
theorem B1370767 : Blo 1217426 1370767 := bstep (se 1 (by rfl) ⟨1028075, by rfl⟩ : syracuseStep 1370767 = 2056151) B2056151
theorem B1542827 : Blo 1217426 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B11700929 : Blo 1217426 11700929 := bstep (se 2 (by rfl) ⟨4387848, by rfl⟩ : syracuseStep 11700929 = 8775697) B8775697
theorem B7506703 : Blo 1217426 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B6163289 : Blo 1217426 6163289 := bstep (se 2 (by rfl) ⟨2311233, by rfl⟩ : syracuseStep 6163289 = 4622467) B4622467
theorem B3083123 : Blo 1217426 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B3083143 : Blo 1217426 3083143 := bstep (se 1 (by rfl) ⟨2312357, by rfl⟩ : syracuseStep 3083143 = 4624715) B4624715
theorem B4623257 : Blo 1217426 4623257 := bstep (se 2 (by rfl) ⟨1733721, by rfl⟩ : syracuseStep 4623257 = 3467443) B3467443
theorem B6941699 : Blo 1217426 6941699 := bstep (se 1 (by rfl) ⟨5206274, by rfl⟩ : syracuseStep 6941699 = 10412549) B10412549
theorem B23407703 : Blo 1217426 23407703 := bstep (se 1 (by rfl) ⟨17555777, by rfl⟩ : syracuseStep 23407703 = 35111555) B35111555
theorem B1371271 : Blo 1217426 1371271 := bstep (se 1 (by rfl) ⟨1028453, by rfl⟩ : syracuseStep 1371271 = 2056907) B2056907
theorem B1543303 : Blo 1217426 1543303 := bstep (se 1 (by rfl) ⟨1157477, by rfl⟩ : syracuseStep 1543303 = 2314955) B2314955
theorem B2739347 : Blo 1217426 2739347 := bstep (se 1 (by rfl) ⟨2054510, by rfl⟩ : syracuseStep 2739347 = 4109021) B4109021
theorem B3083417 : Blo 1217426 3083417 := bstep (se 2 (by rfl) ⟨1156281, by rfl⟩ : syracuseStep 3083417 = 2312563) B2312563
theorem B2739401 : Blo 1217426 2739401 := bstep (se 2 (by rfl) ⟨1027275, by rfl⟩ : syracuseStep 2739401 = 2054551) B2054551
theorem B10407113 : Blo 1217426 10407113 := bstep (se 2 (by rfl) ⟨3902667, by rfl⟩ : syracuseStep 10407113 = 7805335) B7805335
theorem B2927915 : Blo 1217426 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B3083579 : Blo 1217426 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B1371451 : Blo 1217426 1371451 := bstep (se 1 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 1371451 = 2057177) B2057177
theorem B15822215 : Blo 1217426 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B20016569 : Blo 1217426 20016569 := bstep (se 2 (by rfl) ⟨7506213, by rfl⟩ : syracuseStep 20016569 = 15012427) B15012427
theorem B14069177 : Blo 1217426 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B126610897 : Blo 1217426 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B8785361 : Blo 1217426 8785361 := bstep (se 2 (by rfl) ⟨3294510, by rfl⟩ : syracuseStep 8785361 = 6589021) B6589021
theorem B3083791 : Blo 1217426 3083791 := bstep (se 1 (by rfl) ⟨2312843, by rfl⟩ : syracuseStep 3083791 = 4625687) B4625687
theorem B46845539 : Blo 1217426 46845539 := bstep (se 1 (by rfl) ⟨35134154, by rfl⟩ : syracuseStep 46845539 = 70268309) B70268309
theorem B6172361 : Blo 1217426 6172361 := bstep (se 2 (by rfl) ⟨2314635, by rfl⟩ : syracuseStep 6172361 = 4629271) B4629271
theorem B13872869 : Blo 1217426 13872869 := bstep (se 4 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 13872869 = 2601163) B2601163
theorem B3084065 : Blo 1217426 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B240422741 : Blo 1217426 240422741 := bstep (se 9 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 240422741 = 1408727) B1408727
theorem B3469175 : Blo 1217426 3469175 := bstep (se 1 (by rfl) ⟨2601881, by rfl⟩ : syracuseStep 3469175 = 5203763) B5203763
theorem B2600839 : Blo 1217426 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B2740103 : Blo 1217426 2740103 := bstep (se 1 (by rfl) ⟨2055077, by rfl⟩ : syracuseStep 2740103 = 4110155) B4110155
theorem B3903385 : Blo 1217426 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B2600993 : Blo 1217426 2600993 := bstep (se 2 (by rfl) ⟨975372, by rfl⟩ : syracuseStep 2600993 = 1950745) B1950745
theorem B2740283 : Blo 1217426 2740283 := bstep (se 1 (by rfl) ⟨2055212, by rfl⟩ : syracuseStep 2740283 = 4110425) B4110425
theorem B2084923 : Blo 1217426 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B2740409 : Blo 1217426 2740409 := bstep (se 2 (by rfl) ⟨1027653, by rfl⟩ : syracuseStep 2740409 = 2055307) B2055307
theorem B13881617 : Blo 1217426 13881617 := bstep (se 2 (by rfl) ⟨5205606, by rfl⟩ : syracuseStep 13881617 = 10411213) B10411213
theorem B2601335 : Blo 1217426 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B15610259 : Blo 1217426 15610259 := bstep (se 1 (by rfl) ⟨11707694, by rfl⟩ : syracuseStep 15610259 = 23415389) B23415389
theorem B13169081 : Blo 1217426 13169081 := bstep (se 2 (by rfl) ⟨4938405, by rfl⟩ : syracuseStep 13169081 = 9876811) B9876811
theorem B4280843 : Blo 1217426 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B2740751 : Blo 1217426 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B5558813 : Blo 1217426 5558813 := bstep (se 3 (by rfl) ⟨1042277, by rfl⟩ : syracuseStep 5558813 = 2084555) B2084555
theorem B2601505 : Blo 1217426 2601505 := bstep (se 2 (by rfl) ⟨975564, by rfl⟩ : syracuseStep 2601505 = 1951129) B1951129
theorem B2740769 : Blo 1217426 2740769 := bstep (se 2 (by rfl) ⟨1027788, by rfl⟩ : syracuseStep 2740769 = 2055577) B2055577
theorem B2314811 : Blo 1217426 2314811 := bstep (se 1 (by rfl) ⟨1736108, by rfl⟩ : syracuseStep 2314811 = 3472217) B3472217
theorem B6935159 : Blo 1217426 6935159 := bstep (se 1 (by rfl) ⟨5201369, by rfl⟩ : syracuseStep 6935159 = 10402739) B10402739
theorem B3085067 : Blo 1217426 3085067 := bstep (se 1 (by rfl) ⟨2313800, by rfl⟩ : syracuseStep 3085067 = 4627601) B4627601
theorem B4936463 : Blo 1217426 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B6591269 : Blo 1217426 6591269 := bstep (se 4 (by rfl) ⟨617931, by rfl⟩ : syracuseStep 6591269 = 1235863) B1235863
theorem B2741111 : Blo 1217426 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B6165395 : Blo 1217426 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B1217467 : Blo 1217426 1217467 := bstep (se 1 (by rfl) ⟨913100, by rfl⟩ : syracuseStep 1217467 = 1826201) B1826201
theorem B23737349 : Blo 1217426 23737349 := bstep (se 4 (by rfl) ⟨2225376, by rfl⟩ : syracuseStep 23737349 = 4450753) B4450753
theorem B1217543 : Blo 1217426 1217543 := bstep (se 1 (by rfl) ⟨913157, by rfl⟩ : syracuseStep 1217543 = 1826315) B1826315
theorem B1217551 : Blo 1217426 1217551 := bstep (se 1 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 1217551 = 1826327) B1826327
theorem B2741291 : Blo 1217426 2741291 := bstep (se 1 (by rfl) ⟨2055968, by rfl⟩ : syracuseStep 2741291 = 4111937) B4111937
theorem B6771755 : Blo 1217426 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B1217595 : Blo 1217426 1217595 := bstep (se 1 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 1217595 = 1826393) B1826393
theorem B4109399 : Blo 1217426 4109399 := bstep (se 1 (by rfl) ⟨3082049, by rfl⟩ : syracuseStep 4109399 = 6164099) B6164099
theorem B1217671 : Blo 1217426 1217671 := bstep (se 1 (by rfl) ⟨913253, by rfl⟩ : syracuseStep 1217671 = 1826507) B1826507
theorem B1217679 : Blo 1217426 1217679 := bstep (se 1 (by rfl) ⟨913259, by rfl⟩ : syracuseStep 1217679 = 1826519) B1826519
theorem B3708089 : Blo 1217426 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B1217723 : Blo 1217426 1217723 := bstep (se 1 (by rfl) ⟨913292, by rfl⟩ : syracuseStep 1217723 = 1826585) B1826585
theorem B1217799 : Blo 1217426 1217799 := bstep (se 1 (by rfl) ⟨913349, by rfl⟩ : syracuseStep 1217799 = 1826699) B1826699
theorem B1217807 : Blo 1217426 1217807 := bstep (se 1 (by rfl) ⟨913355, by rfl⟩ : syracuseStep 1217807 = 1826711) B1826711
theorem B6935867 : Blo 1217426 6935867 := bstep (se 1 (by rfl) ⟨5201900, by rfl⟩ : syracuseStep 6935867 = 10403801) B10403801
theorem B1217851 : Blo 1217426 1217851 := bstep (se 1 (by rfl) ⟨913388, by rfl⟩ : syracuseStep 1217851 = 1826777) B1826777
theorem B6944089 : Blo 1217426 6944089 := bstep (se 2 (by rfl) ⟨2604033, by rfl⟩ : syracuseStep 6944089 = 5208067) B5208067
theorem B1217927 : Blo 1217426 1217927 := bstep (se 1 (by rfl) ⟨913445, by rfl⟩ : syracuseStep 1217927 = 1826891) B1826891
theorem B1217935 : Blo 1217426 1217935 := bstep (se 1 (by rfl) ⟨913451, by rfl⟩ : syracuseStep 1217935 = 1826903) B1826903
theorem B2741651 : Blo 1217426 2741651 := bstep (se 1 (by rfl) ⟨2056238, by rfl⟩ : syracuseStep 2741651 = 4112477) B4112477
theorem B3339667 : Blo 1217426 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B3085715 : Blo 1217426 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B1217979 : Blo 1217426 1217979 := bstep (se 1 (by rfl) ⟨913484, by rfl⟩ : syracuseStep 1217979 = 1826969) B1826969
theorem B2741705 : Blo 1217426 2741705 := bstep (se 2 (by rfl) ⟨1028139, by rfl⟩ : syracuseStep 2741705 = 2056279) B2056279
theorem B1218055 : Blo 1217426 1218055 := bstep (se 1 (by rfl) ⟨913541, by rfl⟩ : syracuseStep 1218055 = 1827083) B1827083
theorem B1218063 : Blo 1217426 1218063 := bstep (se 1 (by rfl) ⟨913547, by rfl⟩ : syracuseStep 1218063 = 1827095) B1827095
theorem B1758763 : Blo 1217426 1758763 := bstep (se 1 (by rfl) ⟨1319072, by rfl⟩ : syracuseStep 1758763 = 2638145) B2638145
theorem B1218107 : Blo 1217426 1218107 := bstep (se 1 (by rfl) ⟨913580, by rfl⟩ : syracuseStep 1218107 = 1827161) B1827161
theorem B4388413 : Blo 1217426 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B4109885 : Blo 1217426 4109885 := bstep (se 3 (by rfl) ⟨770603, by rfl⟩ : syracuseStep 4109885 = 1541207) B1541207
theorem B5273207 : Blo 1217426 5273207 := bstep (se 1 (by rfl) ⟨3954905, by rfl⟩ : syracuseStep 5273207 = 7909811) B7909811
theorem B1218183 : Blo 1217426 1218183 := bstep (se 1 (by rfl) ⟨913637, by rfl⟩ : syracuseStep 1218183 = 1827275) B1827275
theorem B1218191 : Blo 1217426 1218191 := bstep (se 1 (by rfl) ⟨913643, by rfl⟩ : syracuseStep 1218191 = 1827287) B1827287
theorem B3086009 : Blo 1217426 3086009 := bstep (se 2 (by rfl) ⟨1157253, by rfl⟩ : syracuseStep 3086009 = 2314507) B2314507
theorem B1218235 : Blo 1217426 1218235 := bstep (se 1 (by rfl) ⟨913676, by rfl⟩ : syracuseStep 1218235 = 1827353) B1827353
theorem B9885377 : Blo 1217426 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B1218311 : Blo 1217426 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B1218319 : Blo 1217426 1218319 := bstep (se 1 (by rfl) ⟨913739, by rfl⟩ : syracuseStep 1218319 = 1827479) B1827479
theorem B1218363 : Blo 1217426 1218363 := bstep (se 1 (by rfl) ⟨913772, by rfl⟩ : syracuseStep 1218363 = 1827545) B1827545
theorem B3127099 : Blo 1217426 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B1218439 : Blo 1217426 1218439 := bstep (se 1 (by rfl) ⟨913829, by rfl⟩ : syracuseStep 1218439 = 1827659) B1827659
theorem B1218447 : Blo 1217426 1218447 := bstep (se 1 (by rfl) ⟨913835, by rfl⟩ : syracuseStep 1218447 = 1827671) B1827671
theorem B1300411 : Blo 1217426 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B1218491 : Blo 1217426 1218491 := bstep (se 1 (by rfl) ⟨913868, by rfl⟩ : syracuseStep 1218491 = 1827737) B1827737
theorem B1218567 : Blo 1217426 1218567 := bstep (se 1 (by rfl) ⟨913925, by rfl⟩ : syracuseStep 1218567 = 1827851) B1827851
theorem B1218575 : Blo 1217426 1218575 := bstep (se 1 (by rfl) ⟨913931, by rfl⟩ : syracuseStep 1218575 = 1827863) B1827863
theorem B1669177 : Blo 1217426 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B1218619 : Blo 1217426 1218619 := bstep (se 1 (by rfl) ⟨913964, by rfl⟩ : syracuseStep 1218619 = 1827929) B1827929
theorem B1218695 : Blo 1217426 1218695 := bstep (se 1 (by rfl) ⟨914021, by rfl⟩ : syracuseStep 1218695 = 1828043) B1828043
theorem B2742407 : Blo 1217426 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B1218703 : Blo 1217426 1218703 := bstep (se 1 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 1218703 = 1828055) B1828055
theorem B1218747 : Blo 1217426 1218747 := bstep (se 1 (by rfl) ⟨914060, by rfl⟩ : syracuseStep 1218747 = 1828121) B1828121
theorem B1218823 : Blo 1217426 1218823 := bstep (se 1 (by rfl) ⟨914117, by rfl⟩ : syracuseStep 1218823 = 1828235) B1828235
theorem B2636047 : Blo 1217426 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B1218831 : Blo 1217426 1218831 := bstep (se 1 (by rfl) ⟨914123, by rfl⟩ : syracuseStep 1218831 = 1828247) B1828247
theorem B2054443 : Blo 1217426 2054443 := bstep (se 1 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 2054443 = 3081665) B3081665
theorem B1218875 : Blo 1217426 1218875 := bstep (se 1 (by rfl) ⟨914156, by rfl⟩ : syracuseStep 1218875 = 1828313) B1828313
theorem B2742587 : Blo 1217426 2742587 := bstep (se 1 (by rfl) ⟨2056940, by rfl⟩ : syracuseStep 2742587 = 4113881) B4113881
theorem B1669511 : Blo 1217426 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B1218951 : Blo 1217426 1218951 := bstep (se 1 (by rfl) ⟨914213, by rfl⟩ : syracuseStep 1218951 = 1828427) B1828427
theorem B1218959 : Blo 1217426 1218959 := bstep (se 1 (by rfl) ⟨914219, by rfl⟩ : syracuseStep 1218959 = 1828439) B1828439
theorem B9247121 : Blo 1217426 9247121 := bstep (se 2 (by rfl) ⟨3467670, by rfl⟩ : syracuseStep 9247121 = 6935341) B6935341
theorem B2603411 : Blo 1217426 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B4626841 : Blo 1217426 4626841 := bstep (se 2 (by rfl) ⟨1735065, by rfl⟩ : syracuseStep 4626841 = 3470131) B3470131
theorem B2054585 : Blo 1217426 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B2742713 : Blo 1217426 2742713 := bstep (se 2 (by rfl) ⟨1028517, by rfl⟩ : syracuseStep 2742713 = 2057035) B2057035
theorem B1219003 : Blo 1217426 1219003 := bstep (se 1 (by rfl) ⟨914252, by rfl⟩ : syracuseStep 1219003 = 1828505) B1828505
theorem B3471817 : Blo 1217426 3471817 := bstep (se 2 (by rfl) ⟨1301931, by rfl⟩ : syracuseStep 3471817 = 2603863) B2603863
theorem B8788445 : Blo 1217426 8788445 := bstep (se 3 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 8788445 = 3295667) B3295667
theorem B1219079 : Blo 1217426 1219079 := bstep (se 1 (by rfl) ⟨914309, by rfl⟩ : syracuseStep 1219079 = 1828619) B1828619
theorem B1219087 : Blo 1217426 1219087 := bstep (se 1 (by rfl) ⟨914315, by rfl⟩ : syracuseStep 1219087 = 1828631) B1828631
theorem B11123243 : Blo 1217426 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B1219131 : Blo 1217426 1219131 := bstep (se 1 (by rfl) ⟨914348, by rfl⟩ : syracuseStep 1219131 = 1828697) B1828697
theorem B1219207 : Blo 1217426 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B1219215 : Blo 1217426 1219215 := bstep (se 1 (by rfl) ⟨914411, by rfl⟩ : syracuseStep 1219215 = 1828823) B1828823
theorem B1735339 : Blo 1217426 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B1219259 : Blo 1217426 1219259 := bstep (se 1 (by rfl) ⟨914444, by rfl⟩ : syracuseStep 1219259 = 1828889) B1828889
theorem B22231745 : Blo 1217426 22231745 := bstep (se 2 (by rfl) ⟨8336904, by rfl⟩ : syracuseStep 22231745 = 16673809) B16673809
theorem B4627145 : Blo 1217426 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B6937325 : Blo 1217426 6937325 := bstep (se 3 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 6937325 = 2601497) B2601497
theorem B1219335 : Blo 1217426 1219335 := bstep (se 1 (by rfl) ⟨914501, by rfl⟩ : syracuseStep 1219335 = 1829003) B1829003
theorem B2743055 : Blo 1217426 2743055 := bstep (se 1 (by rfl) ⟨2057291, by rfl⟩ : syracuseStep 2743055 = 4114583) B4114583
theorem B1219343 : Blo 1217426 1219343 := bstep (se 1 (by rfl) ⟨914507, by rfl⟩ : syracuseStep 1219343 = 1829015) B1829015
theorem B2743073 : Blo 1217426 2743073 := bstep (se 2 (by rfl) ⟨1028652, by rfl⟩ : syracuseStep 2743073 = 2057305) B2057305
theorem B1219387 : Blo 1217426 1219387 := bstep (se 1 (by rfl) ⟨914540, by rfl⟩ : syracuseStep 1219387 = 1829081) B1829081
theorem B4111289 : Blo 1217426 4111289 := bstep (se 2 (by rfl) ⟨1541733, by rfl⟩ : syracuseStep 4111289 = 3083467) B3083467
theorem B8027147 : Blo 1217426 8027147 := bstep (se 1 (by rfl) ⟨6020360, by rfl⟩ : syracuseStep 8027147 = 12040721) B12040721
theorem B13884533 : Blo 1217426 13884533 := bstep (se 5 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 13884533 = 1301675) B1301675
theorem B2055287 : Blo 1217426 2055287 := bstep (se 1 (by rfl) ⟨1541465, by rfl⟩ : syracuseStep 2055287 = 3082931) B3082931
theorem B2743415 : Blo 1217426 2743415 := bstep (se 1 (by rfl) ⟨2057561, by rfl⟩ : syracuseStep 2743415 = 4115123) B4115123
theorem B3128473 : Blo 1217426 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B2743595 : Blo 1217426 2743595 := bstep (se 1 (by rfl) ⟨2057696, by rfl⟩ : syracuseStep 2743595 = 4115393) B4115393
theorem B1826183 : Blo 1217426 1826183 := bstep (se 1 (by rfl) ⟨1369637, by rfl⟩ : syracuseStep 1826183 = 2739275) B2739275
theorem B1826219 : Blo 1217426 1826219 := bstep (se 1 (by rfl) ⟨1369664, by rfl⟩ : syracuseStep 1826219 = 2739329) B2739329
theorem B1826249 : Blo 1217426 1826249 := bstep (se 2 (by rfl) ⟨684843, by rfl⟩ : syracuseStep 1826249 = 1369687) B1369687
theorem B20807117 : Blo 1217426 20807117 := bstep (se 3 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 20807117 = 7802669) B7802669
theorem B4111883 : Blo 1217426 4111883 := bstep (se 1 (by rfl) ⟨3083912, by rfl⟩ : syracuseStep 4111883 = 6167825) B6167825
theorem B6250007 : Blo 1217426 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B2055739 : Blo 1217426 2055739 := bstep (se 1 (by rfl) ⟨1541804, by rfl⟩ : syracuseStep 2055739 = 3083609) B3083609
theorem B1826363 : Blo 1217426 1826363 := bstep (se 1 (by rfl) ⟨1369772, by rfl⟩ : syracuseStep 1826363 = 2739545) B2739545
theorem B1826423 : Blo 1217426 1826423 := bstep (se 1 (by rfl) ⟨1369817, by rfl⟩ : syracuseStep 1826423 = 2739635) B2739635
theorem B4111991 : Blo 1217426 4111991 := bstep (se 1 (by rfl) ⟨3083993, by rfl⟩ : syracuseStep 4111991 = 6167987) B6167987
theorem B4628087 : Blo 1217426 4628087 := bstep (se 1 (by rfl) ⟨3471065, by rfl⟩ : syracuseStep 4628087 = 6942131) B6942131
theorem B1826447 : Blo 1217426 1826447 := bstep (se 1 (by rfl) ⟨1369835, by rfl⟩ : syracuseStep 1826447 = 2739671) B2739671
theorem B1564303 : Blo 1217426 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B1826489 : Blo 1217426 1826489 := bstep (se 2 (by rfl) ⟨684933, by rfl⟩ : syracuseStep 1826489 = 1369867) B1369867
theorem B2055881 : Blo 1217426 2055881 := bstep (se 2 (by rfl) ⟨770955, by rfl⟩ : syracuseStep 2055881 = 1541911) B1541911
theorem B1826567 : Blo 1217426 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B1826603 : Blo 1217426 1826603 := bstep (se 1 (by rfl) ⟨1369952, by rfl⟩ : syracuseStep 1826603 = 2739905) B2739905
theorem B1826633 : Blo 1217426 1826633 := bstep (se 2 (by rfl) ⟨684987, by rfl⟩ : syracuseStep 1826633 = 1369975) B1369975
theorem B6168473 : Blo 1217426 6168473 := bstep (se 2 (by rfl) ⟨2313177, by rfl⟩ : syracuseStep 6168473 = 4626355) B4626355
theorem B1826747 : Blo 1217426 1826747 := bstep (se 1 (by rfl) ⟨1370060, by rfl⟩ : syracuseStep 1826747 = 2740121) B2740121
theorem B1826807 : Blo 1217426 1826807 := bstep (se 1 (by rfl) ⟨1370105, by rfl⟩ : syracuseStep 1826807 = 2740211) B2740211
theorem B1826825 : Blo 1217426 1826825 := bstep (se 2 (by rfl) ⟨685059, by rfl⟩ : syracuseStep 1826825 = 1370119) B1370119
theorem B21405725 : Blo 1217426 21405725 := bstep (se 3 (by rfl) ⟨4013573, by rfl⟩ : syracuseStep 21405725 = 8027147) B8027147
theorem B1826855 : Blo 1217426 1826855 := bstep (se 1 (by rfl) ⟨1370141, by rfl⟩ : syracuseStep 1826855 = 2740283) B2740283
theorem B1826939 : Blo 1217426 1826939 := bstep (se 1 (by rfl) ⟨1370204, by rfl⟩ : syracuseStep 1826939 = 2740409) B2740409
theorem B1827065 : Blo 1217426 1827065 := bstep (se 2 (by rfl) ⟨685149, by rfl⟩ : syracuseStep 1827065 = 1370299) B1370299
theorem B2056441 : Blo 1217426 2056441 := bstep (se 2 (by rfl) ⟨771165, by rfl⟩ : syracuseStep 2056441 = 1542331) B1542331
theorem B1827167 : Blo 1217426 1827167 := bstep (se 1 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 1827167 = 2740751) B2740751
theorem B1827179 : Blo 1217426 1827179 := bstep (se 1 (by rfl) ⟨1370384, by rfl⟩ : syracuseStep 1827179 = 2740769) B2740769
theorem B2056711 : Blo 1217426 2056711 := bstep (se 1 (by rfl) ⟨1542533, by rfl⟩ : syracuseStep 2056711 = 3085067) B3085067
theorem B6169121 : Blo 1217426 6169121 := bstep (se 2 (by rfl) ⟨2313420, by rfl⟩ : syracuseStep 6169121 = 4626841) B4626841
theorem B8905249 : Blo 1217426 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B1827407 : Blo 1217426 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B4629089 : Blo 1217426 4629089 := bstep (se 2 (by rfl) ⟨1735908, by rfl⟩ : syracuseStep 4629089 = 3471817) B3471817
theorem B14811821 : Blo 1217426 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B1827527 : Blo 1217426 1827527 := bstep (se 1 (by rfl) ⟨1370645, by rfl⟩ : syracuseStep 1827527 = 2741291) B2741291
theorem B4514503 : Blo 1217426 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B5858077 : Blo 1217426 5858077 := bstep (se 3 (by rfl) ⟨1098389, by rfl⟩ : syracuseStep 5858077 = 2196779) B2196779
theorem B7037725 : Blo 1217426 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B1827689 : Blo 1217426 1827689 := bstep (se 2 (by rfl) ⟨685383, by rfl⟩ : syracuseStep 1827689 = 1370767) B1370767
theorem B1827767 : Blo 1217426 1827767 := bstep (se 1 (by rfl) ⟨1370825, by rfl⟩ : syracuseStep 1827767 = 2741651) B2741651
theorem B2057143 : Blo 1217426 2057143 := bstep (se 1 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 2057143 = 3085715) B3085715
theorem B1827803 : Blo 1217426 1827803 := bstep (se 1 (by rfl) ⟨1370852, by rfl⟩ : syracuseStep 1827803 = 2741705) B2741705
theorem B3515471 : Blo 1217426 3515471 := bstep (se 1 (by rfl) ⟨2636603, by rfl⟩ : syracuseStep 3515471 = 5273207) B5273207
theorem B2057339 : Blo 1217426 2057339 := bstep (se 1 (by rfl) ⟨1543004, by rfl⟩ : syracuseStep 2057339 = 3086009) B3086009
theorem B6587639 : Blo 1217426 6587639 := bstep (se 1 (by rfl) ⟨4940729, by rfl⟩ : syracuseStep 6587639 = 9881459) B9881459
theorem B12666227 : Blo 1217426 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B14058917 : Blo 1217426 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B1828271 : Blo 1217426 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B1828361 : Blo 1217426 1828361 := bstep (se 2 (by rfl) ⟨685635, by rfl⟩ : syracuseStep 1828361 = 1371271) B1371271
theorem B2057737 : Blo 1217426 2057737 := bstep (se 2 (by rfl) ⟨771651, by rfl⟩ : syracuseStep 2057737 = 1543303) B1543303
theorem B1828391 : Blo 1217426 1828391 := bstep (se 1 (by rfl) ⟨1371293, by rfl⟩ : syracuseStep 1828391 = 2742587) B2742587
theorem B1369723 : Blo 1217426 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B4114043 : Blo 1217426 4114043 := bstep (se 1 (by rfl) ⟨3085532, by rfl⟩ : syracuseStep 4114043 = 6171065) B6171065
theorem B1828475 : Blo 1217426 1828475 := bstep (se 1 (by rfl) ⟨1371356, by rfl⟩ : syracuseStep 1828475 = 2742713) B2742713
theorem B5858963 : Blo 1217426 5858963 := bstep (se 1 (by rfl) ⟨4394222, by rfl⟩ : syracuseStep 5858963 = 8788445) B8788445
theorem B7415495 : Blo 1217426 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B1828601 : Blo 1217426 1828601 := bstep (se 2 (by rfl) ⟨685725, by rfl⟩ : syracuseStep 1828601 = 1371451) B1371451
theorem B4114205 : Blo 1217426 4114205 := bstep (se 3 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 4114205 = 1542827) B1542827
theorem B9258785 : Blo 1217426 9258785 := bstep (se 2 (by rfl) ⟨3472044, by rfl⟩ : syracuseStep 9258785 = 6944089) B6944089
theorem B7800619 : Blo 1217426 7800619 := bstep (se 1 (by rfl) ⟨5850464, by rfl⟩ : syracuseStep 7800619 = 11700929) B11700929
theorem B14821163 : Blo 1217426 14821163 := bstep (se 1 (by rfl) ⟨11115872, by rfl⟩ : syracuseStep 14821163 = 22231745) B22231745
theorem B1828703 : Blo 1217426 1828703 := bstep (se 1 (by rfl) ⟨1371527, by rfl⟩ : syracuseStep 1828703 = 2743055) B2743055
theorem B1828715 : Blo 1217426 1828715 := bstep (se 1 (by rfl) ⟨1371536, by rfl⟩ : syracuseStep 1828715 = 2743073) B2743073
theorem B3082171 : Blo 1217426 3082171 := bstep (se 1 (by rfl) ⟨2311628, by rfl⟩ : syracuseStep 3082171 = 4623257) B4623257
theorem B168814529 : Blo 1217426 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B2345017 : Blo 1217426 2345017 := bstep (se 2 (by rfl) ⟨879381, by rfl⟩ : syracuseStep 2345017 = 1758763) B1758763
theorem B1370191 : Blo 1217426 1370191 := bstep (se 1 (by rfl) ⟨1027643, by rfl⟩ : syracuseStep 1370191 = 2055287) B2055287
theorem B1828943 : Blo 1217426 1828943 := bstep (se 1 (by rfl) ⟨1371707, by rfl⟩ : syracuseStep 1828943 = 2743415) B2743415
theorem B5851217 : Blo 1217426 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B1951943 : Blo 1217426 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B1829063 : Blo 1217426 1829063 := bstep (se 1 (by rfl) ⟨1371797, by rfl⟩ : syracuseStep 1829063 = 2743595) B2743595
theorem B13871411 : Blo 1217426 13871411 := bstep (se 1 (by rfl) ⟨10403558, by rfl⟩ : syracuseStep 13871411 = 20807117) B20807117
theorem B31230359 : Blo 1217426 31230359 := bstep (se 1 (by rfl) ⟨23422769, by rfl⟩ : syracuseStep 31230359 = 46845539) B46845539
theorem B1370587 : Blo 1217426 1370587 := bstep (se 1 (by rfl) ⟨1027940, by rfl⟩ : syracuseStep 1370587 = 2055881) B2055881
theorem B4114907 : Blo 1217426 4114907 := bstep (se 1 (by rfl) ⟨3086180, by rfl⟩ : syracuseStep 4114907 = 6172361) B6172361
theorem B3467785 : Blo 1217426 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B6588953 : Blo 1217426 6588953 := bstep (se 2 (by rfl) ⟨2470857, by rfl⟩ : syracuseStep 6588953 = 4941715) B4941715
theorem B5204513 : Blo 1217426 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B2312783 : Blo 1217426 2312783 := bstep (se 1 (by rfl) ⟨1734587, by rfl⟩ : syracuseStep 2312783 = 3469175) B3469175
theorem B1371055 : Blo 1217426 1371055 := bstep (se 1 (by rfl) ⟨1028291, by rfl⟩ : syracuseStep 1371055 = 2056583) B2056583
theorem B10406839 : Blo 1217426 10406839 := bstep (se 1 (by rfl) ⟨7805129, by rfl⟩ : syracuseStep 10406839 = 15610259) B15610259
theorem B11119589 : Blo 1217426 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B2853895 : Blo 1217426 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B3705875 : Blo 1217426 3705875 := bstep (se 1 (by rfl) ⟨2779406, by rfl⟩ : syracuseStep 3705875 = 5558813) B5558813
theorem B1543207 : Blo 1217426 1543207 := bstep (se 1 (by rfl) ⟨1157405, by rfl⟩ : syracuseStep 1543207 = 2314811) B2314811
theorem B2739257 : Blo 1217426 2739257 := bstep (se 2 (by rfl) ⟨1027221, by rfl⟩ : syracuseStep 2739257 = 2054443) B2054443
theorem B4623439 : Blo 1217426 4623439 := bstep (se 1 (by rfl) ⟨3467579, by rfl⟩ : syracuseStep 4623439 = 6935159) B6935159
theorem B4394179 : Blo 1217426 4394179 := bstep (se 1 (by rfl) ⟨3295634, by rfl⟩ : syracuseStep 4394179 = 6591269) B6591269
theorem B1371487 : Blo 1217426 1371487 := bstep (se 1 (by rfl) ⟨1028615, by rfl⟩ : syracuseStep 1371487 = 2057231) B2057231
theorem B3468673 : Blo 1217426 3468673 := bstep (se 2 (by rfl) ⟨1300752, by rfl⟩ : syracuseStep 3468673 = 2601505) B2601505
theorem B2928001 : Blo 1217426 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B2502031 : Blo 1217426 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B2739599 : Blo 1217426 2739599 := bstep (se 1 (by rfl) ⟨2054699, by rfl⟩ : syracuseStep 2739599 = 4109399) B4109399
theorem B4623911 : Blo 1217426 4623911 := bstep (se 1 (by rfl) ⟨3467933, by rfl⟩ : syracuseStep 4623911 = 6935867) B6935867
theorem B6172199 : Blo 1217426 6172199 := bstep (se 1 (by rfl) ⟨4629149, by rfl⟩ : syracuseStep 6172199 = 9258299) B9258299
theorem B2313785 : Blo 1217426 2313785 := bstep (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) B1735339
theorem B2928251 : Blo 1217426 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B4452029 : Blo 1217426 4452029 := bstep (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) B1669511
theorem B1371847 : Blo 1217426 1371847 := bstep (se 1 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 1371847 = 2057771) B2057771
theorem B2739923 : Blo 1217426 2739923 := bstep (se 1 (by rfl) ⟨2054942, by rfl⟩ : syracuseStep 2739923 = 4109885) B4109885
theorem B6590251 : Blo 1217426 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B4943791 : Blo 1217426 4943791 := bstep (se 1 (by rfl) ⟨3707843, by rfl⟩ : syracuseStep 4943791 = 7415687) B7415687
theorem B3469243 : Blo 1217426 3469243 := bstep (se 1 (by rfl) ⟨2601932, by rfl⟩ : syracuseStep 3469243 = 5203865) B5203865
theorem B9252953 : Blo 1217426 9252953 := bstep (se 2 (by rfl) ⟨3469857, by rfl⟩ : syracuseStep 9252953 = 6939715) B6939715
theorem B11120755 : Blo 1217426 11120755 := bstep (se 1 (by rfl) ⟨8340566, by rfl⟩ : syracuseStep 11120755 = 16681133) B16681133
theorem B4943987 : Blo 1217426 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B6164747 : Blo 1217426 6164747 := bstep (se 1 (by rfl) ⟨4623560, by rfl⟩ : syracuseStep 6164747 = 9247121) B9247121
theorem B3084763 : Blo 1217426 3084763 := bstep (se 1 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 3084763 = 4627145) B4627145
theorem B4624883 : Blo 1217426 4624883 := bstep (se 1 (by rfl) ⟨3468662, by rfl⟩ : syracuseStep 4624883 = 6937325) B6937325
theorem B4452889 : Blo 1217426 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B4108859 : Blo 1217426 4108859 := bstep (se 1 (by rfl) ⟨3081644, by rfl⟩ : syracuseStep 4108859 = 6163289) B6163289
theorem B2740859 : Blo 1217426 2740859 := bstep (se 1 (by rfl) ⟨2055644, by rfl⟩ : syracuseStep 2740859 = 4111289) B4111289
theorem B2740985 : Blo 1217426 2740985 := bstep (se 2 (by rfl) ⟨1027869, by rfl⟩ : syracuseStep 2740985 = 2055739) B2055739
theorem B4109129 : Blo 1217426 4109129 := bstep (se 2 (by rfl) ⟨1540923, by rfl⟩ : syracuseStep 4109129 = 3081847) B3081847
theorem B1217455 : Blo 1217426 1217455 := bstep (se 1 (by rfl) ⟨913091, by rfl⟩ : syracuseStep 1217455 = 1826183) B1826183
theorem B10548143 : Blo 1217426 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B1217479 : Blo 1217426 1217479 := bstep (se 1 (by rfl) ⟨913109, by rfl⟩ : syracuseStep 1217479 = 1826219) B1826219
theorem B1217499 : Blo 1217426 1217499 := bstep (se 1 (by rfl) ⟨913124, by rfl⟩ : syracuseStep 1217499 = 1826249) B1826249
theorem B2741255 : Blo 1217426 2741255 := bstep (se 1 (by rfl) ⟨2055941, by rfl⟩ : syracuseStep 2741255 = 4111883) B4111883
theorem B4166671 : Blo 1217426 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B1217575 : Blo 1217426 1217575 := bstep (se 1 (by rfl) ⟨913181, by rfl⟩ : syracuseStep 1217575 = 1826363) B1826363
theorem B1217615 : Blo 1217426 1217615 := bstep (se 1 (by rfl) ⟨913211, by rfl⟩ : syracuseStep 1217615 = 1826423) B1826423
theorem B2741327 : Blo 1217426 2741327 := bstep (se 1 (by rfl) ⟨2055995, by rfl⟩ : syracuseStep 2741327 = 4111991) B4111991
theorem B3085391 : Blo 1217426 3085391 := bstep (se 1 (by rfl) ⟨2314043, by rfl⟩ : syracuseStep 3085391 = 4628087) B4628087
theorem B1217631 : Blo 1217426 1217631 := bstep (se 1 (by rfl) ⟨913223, by rfl⟩ : syracuseStep 1217631 = 1826447) B1826447
theorem B1217659 : Blo 1217426 1217659 := bstep (se 1 (by rfl) ⟨913244, by rfl⟩ : syracuseStep 1217659 = 1826489) B1826489
theorem B1217711 : Blo 1217426 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B1217735 : Blo 1217426 1217735 := bstep (se 1 (by rfl) ⟨913301, by rfl⟩ : syracuseStep 1217735 = 1826603) B1826603
theorem B1217755 : Blo 1217426 1217755 := bstep (se 1 (by rfl) ⟨913316, by rfl⟩ : syracuseStep 1217755 = 1826633) B1826633
theorem B160281827 : Blo 1217426 160281827 := bstep (se 1 (by rfl) ⟨120211370, by rfl⟩ : syracuseStep 160281827 = 240422741) B240422741
theorem B1733881 : Blo 1217426 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B1217831 : Blo 1217426 1217831 := bstep (se 1 (by rfl) ⟨913373, by rfl⟩ : syracuseStep 1217831 = 1826747) B1826747
theorem B1217871 : Blo 1217426 1217871 := bstep (se 1 (by rfl) ⟨913403, by rfl⟩ : syracuseStep 1217871 = 1826807) B1826807
theorem B1217887 : Blo 1217426 1217887 := bstep (se 1 (by rfl) ⟨913415, by rfl⟩ : syracuseStep 1217887 = 1826831) B1826831
theorem B1733995 : Blo 1217426 1733995 := bstep (se 1 (by rfl) ⟨1300496, by rfl⟩ : syracuseStep 1733995 = 2600993) B2600993
theorem B1217915 : Blo 1217426 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B2225569 : Blo 1217426 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B1217967 : Blo 1217426 1217967 := bstep (se 1 (by rfl) ⟨913475, by rfl⟩ : syracuseStep 1217967 = 1826951) B1826951
theorem B1217991 : Blo 1217426 1217991 := bstep (se 1 (by rfl) ⟨913493, by rfl⟩ : syracuseStep 1217991 = 1826987) B1826987
theorem B1218011 : Blo 1217426 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B2741723 : Blo 1217426 2741723 := bstep (se 1 (by rfl) ⟨2056292, by rfl⟩ : syracuseStep 2741723 = 4112585) B4112585
theorem B9254411 : Blo 1217426 9254411 := bstep (se 1 (by rfl) ⟨6940808, by rfl⟩ : syracuseStep 9254411 = 13881617) B13881617
theorem B1218087 : Blo 1217426 1218087 := bstep (se 1 (by rfl) ⟨913565, by rfl⟩ : syracuseStep 1218087 = 1827131) B1827131
theorem B1734223 : Blo 1217426 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B1218127 : Blo 1217426 1218127 := bstep (se 1 (by rfl) ⟨913595, by rfl⟩ : syracuseStep 1218127 = 1827191) B1827191
theorem B1218143 : Blo 1217426 1218143 := bstep (se 1 (by rfl) ⟨913607, by rfl⟩ : syracuseStep 1218143 = 1827215) B1827215
theorem B1218171 : Blo 1217426 1218171 := bstep (se 1 (by rfl) ⟨913628, by rfl⟩ : syracuseStep 1218171 = 1827257) B1827257
theorem B1218223 : Blo 1217426 1218223 := bstep (se 1 (by rfl) ⟨913667, by rfl⟩ : syracuseStep 1218223 = 1827335) B1827335
theorem B6166205 : Blo 1217426 6166205 := bstep (se 3 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 6166205 = 2312327) B2312327
theorem B1218247 : Blo 1217426 1218247 := bstep (se 1 (by rfl) ⟨913685, by rfl⟩ : syracuseStep 1218247 = 1827371) B1827371
theorem B7509719 : Blo 1217426 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B3086039 : Blo 1217426 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B1218267 : Blo 1217426 1218267 := bstep (se 1 (by rfl) ⟨913700, by rfl⟩ : syracuseStep 1218267 = 1827401) B1827401
theorem B1218343 : Blo 1217426 1218343 := bstep (se 1 (by rfl) ⟨913757, by rfl⟩ : syracuseStep 1218343 = 1827515) B1827515
theorem B1218383 : Blo 1217426 1218383 := bstep (se 1 (by rfl) ⟨913787, by rfl⟩ : syracuseStep 1218383 = 1827575) B1827575
theorem B3290975 : Blo 1217426 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B6166367 : Blo 1217426 6166367 := bstep (se 1 (by rfl) ⟨4624775, by rfl⟩ : syracuseStep 6166367 = 9249551) B9249551
theorem B1218399 : Blo 1217426 1218399 := bstep (se 1 (by rfl) ⟨913799, by rfl⟩ : syracuseStep 1218399 = 1827599) B1827599
theorem B1218427 : Blo 1217426 1218427 := bstep (se 1 (by rfl) ⟨913820, by rfl⟩ : syracuseStep 1218427 = 1827641) B1827641
theorem B1218479 : Blo 1217426 1218479 := bstep (se 1 (by rfl) ⟨913859, by rfl⟩ : syracuseStep 1218479 = 1827719) B1827719
theorem B2742191 : Blo 1217426 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B4110263 : Blo 1217426 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B1218503 : Blo 1217426 1218503 := bstep (se 1 (by rfl) ⟨913877, by rfl⟩ : syracuseStep 1218503 = 1827755) B1827755
theorem B1218523 : Blo 1217426 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B15824899 : Blo 1217426 15824899 := bstep (se 1 (by rfl) ⟨11868674, by rfl⟩ : syracuseStep 15824899 = 23737349) B23737349
theorem B1218599 : Blo 1217426 1218599 := bstep (se 1 (by rfl) ⟨913949, by rfl⟩ : syracuseStep 1218599 = 1827899) B1827899
theorem B1218639 : Blo 1217426 1218639 := bstep (se 1 (by rfl) ⟨913979, by rfl⟩ : syracuseStep 1218639 = 1827959) B1827959
theorem B1218655 : Blo 1217426 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B1218683 : Blo 1217426 1218683 := bstep (se 1 (by rfl) ⟨914012, by rfl⟩ : syracuseStep 1218683 = 1828025) B1828025
theorem B2472059 : Blo 1217426 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B16685189 : Blo 1217426 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B2742443 : Blo 1217426 2742443 := bstep (se 1 (by rfl) ⟨2056832, by rfl⟩ : syracuseStep 2742443 = 4113665) B4113665
theorem B1218735 : Blo 1217426 1218735 := bstep (se 1 (by rfl) ⟨914051, by rfl⟩ : syracuseStep 1218735 = 1828103) B1828103
theorem B1218759 : Blo 1217426 1218759 := bstep (se 1 (by rfl) ⟨914069, by rfl⟩ : syracuseStep 1218759 = 1828139) B1828139
theorem B1218779 : Blo 1217426 1218779 := bstep (se 1 (by rfl) ⟨914084, by rfl⟩ : syracuseStep 1218779 = 1828169) B1828169
theorem B1218855 : Blo 1217426 1218855 := bstep (se 1 (by rfl) ⟨914141, by rfl⟩ : syracuseStep 1218855 = 1828283) B1828283
theorem B1218895 : Blo 1217426 1218895 := bstep (se 1 (by rfl) ⟨914171, by rfl⟩ : syracuseStep 1218895 = 1828343) B1828343
theorem B6953303 : Blo 1217426 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B1218911 : Blo 1217426 1218911 := bstep (se 1 (by rfl) ⟨914183, by rfl⟩ : syracuseStep 1218911 = 1828367) B1828367
theorem B10008937 : Blo 1217426 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B1218939 : Blo 1217426 1218939 := bstep (se 1 (by rfl) ⟨914204, by rfl⟩ : syracuseStep 1218939 = 1828409) B1828409
theorem B1218991 : Blo 1217426 1218991 := bstep (se 1 (by rfl) ⟨914243, by rfl⟩ : syracuseStep 1218991 = 1828487) B1828487
theorem B1219015 : Blo 1217426 1219015 := bstep (se 1 (by rfl) ⟨914261, by rfl⟩ : syracuseStep 1219015 = 1828523) B1828523
theorem B1219035 : Blo 1217426 1219035 := bstep (se 1 (by rfl) ⟨914276, by rfl⟩ : syracuseStep 1219035 = 1828553) B1828553
theorem B53377517 : Blo 1217426 53377517 := bstep (se 3 (by rfl) ⟨10008284, by rfl⟩ : syracuseStep 53377517 = 20016569) B20016569
theorem B35117549 : Blo 1217426 35117549 := bstep (se 3 (by rfl) ⟨6584540, by rfl⟩ : syracuseStep 35117549 = 13169081) B13169081
theorem B4110857 : Blo 1217426 4110857 := bstep (se 2 (by rfl) ⟨1541571, by rfl⟩ : syracuseStep 4110857 = 3083143) B3083143
theorem B1219111 : Blo 1217426 1219111 := bstep (se 1 (by rfl) ⟨914333, by rfl⟩ : syracuseStep 1219111 = 1828667) B1828667
theorem B2054713 : Blo 1217426 2054713 := bstep (se 2 (by rfl) ⟨770517, by rfl⟩ : syracuseStep 2054713 = 1541035) B1541035
theorem B1219151 : Blo 1217426 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B133487189 : Blo 1217426 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B1219167 : Blo 1217426 1219167 := bstep (se 1 (by rfl) ⟨914375, by rfl⟩ : syracuseStep 1219167 = 1828751) B1828751
theorem B1219195 : Blo 1217426 1219195 := bstep (se 1 (by rfl) ⟨914396, by rfl⟩ : syracuseStep 1219195 = 1828793) B1828793
theorem B1219247 : Blo 1217426 1219247 := bstep (se 1 (by rfl) ⟨914435, by rfl⟩ : syracuseStep 1219247 = 1828871) B1828871
theorem B2054855 : Blo 1217426 2054855 := bstep (se 1 (by rfl) ⟨1541141, by rfl⟩ : syracuseStep 2054855 = 3082283) B3082283
theorem B2742983 : Blo 1217426 2742983 := bstep (se 1 (by rfl) ⟨2057237, by rfl⟩ : syracuseStep 2742983 = 4114475) B4114475
theorem B1219271 : Blo 1217426 1219271 := bstep (se 1 (by rfl) ⟨914453, by rfl⟩ : syracuseStep 1219271 = 1828907) B1828907
theorem B1219291 : Blo 1217426 1219291 := bstep (se 1 (by rfl) ⟨914468, by rfl⟩ : syracuseStep 1219291 = 1828937) B1828937
theorem B1219367 : Blo 1217426 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B1219407 : Blo 1217426 1219407 := bstep (se 1 (by rfl) ⟨914555, by rfl⟩ : syracuseStep 1219407 = 1829111) B1829111
theorem B1219423 : Blo 1217426 1219423 := bstep (se 1 (by rfl) ⟨914567, by rfl⟩ : syracuseStep 1219423 = 1829135) B1829135
theorem B2055017 : Blo 1217426 2055017 := bstep (se 2 (by rfl) ⟨770631, by rfl⟩ : syracuseStep 2055017 = 1541263) B1541263
theorem B5200823 : Blo 1217426 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B1735607 : Blo 1217426 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B2055415 : Blo 1217426 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B4627799 : Blo 1217426 4627799 := bstep (se 1 (by rfl) ⟨3470849, by rfl⟩ : syracuseStep 4627799 = 6941699) B6941699
theorem B1826153 : Blo 1217426 1826153 := bstep (se 2 (by rfl) ⟨684807, by rfl⟩ : syracuseStep 1826153 = 1369615) B1369615
theorem B4111721 : Blo 1217426 4111721 := bstep (se 2 (by rfl) ⟨1541895, by rfl⟩ : syracuseStep 4111721 = 3083791) B3083791
theorem B15605135 : Blo 1217426 15605135 := bstep (se 1 (by rfl) ⟨11703851, by rfl⟩ : syracuseStep 15605135 = 23407703) B23407703
theorem B9256355 : Blo 1217426 9256355 := bstep (se 1 (by rfl) ⟨6942266, by rfl⟩ : syracuseStep 9256355 = 13884533) B13884533
theorem B1826231 : Blo 1217426 1826231 := bstep (se 1 (by rfl) ⟨1369673, by rfl⟩ : syracuseStep 1826231 = 2739347) B2739347
theorem B2055611 : Blo 1217426 2055611 := bstep (se 1 (by rfl) ⟨1541708, by rfl⟩ : syracuseStep 2055611 = 3083417) B3083417
theorem B1826267 : Blo 1217426 1826267 := bstep (se 1 (by rfl) ⟨1369700, by rfl⟩ : syracuseStep 1826267 = 2739401) B2739401
theorem B6938075 : Blo 1217426 6938075 := bstep (se 1 (by rfl) ⟨5203556, by rfl⟩ : syracuseStep 6938075 = 10407113) B10407113
theorem B2055719 : Blo 1217426 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B9379451 : Blo 1217426 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B5856907 : Blo 1217426 5856907 := bstep (se 1 (by rfl) ⟨4392680, by rfl⟩ : syracuseStep 5856907 = 8785361) B8785361
theorem B6938257 : Blo 1217426 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B4169465 : Blo 1217426 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B9248579 : Blo 1217426 9248579 := bstep (se 1 (by rfl) ⟨6936434, by rfl⟩ : syracuseStep 9248579 = 13872869) B13872869
theorem B2056009 : Blo 1217426 2056009 := bstep (se 2 (by rfl) ⟨771003, by rfl⟩ : syracuseStep 2056009 = 1542007) B1542007
theorem B2056043 : Blo 1217426 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B1826735 : Blo 1217426 1826735 := bstep (se 1 (by rfl) ⟨1370051, by rfl⟩ : syracuseStep 1826735 = 2740103) B2740103
theorem B4112315 : Blo 1217426 4112315 := bstep (se 1 (by rfl) ⟨3084236, by rfl⟩ : syracuseStep 4112315 = 6168473) B6168473
theorem B14270483 : Blo 1217426 14270483 := bstep (se 1 (by rfl) ⟨10702862, by rfl⟩ : syracuseStep 14270483 = 21405725) B21405725
theorem B6168635 : Blo 1217426 6168635 := bstep (se 1 (by rfl) ⟨4626476, by rfl⟩ : syracuseStep 6168635 = 9252953) B9252953
theorem B1826921 : Blo 1217426 1826921 := bstep (se 2 (by rfl) ⟨685095, by rfl⟩ : syracuseStep 1826921 = 1370191) B1370191
theorem B14827673 : Blo 1217426 14827673 := bstep (se 2 (by rfl) ⟨5560377, by rfl⟩ : syracuseStep 14827673 = 11120755) B11120755
theorem B4112747 : Blo 1217426 4112747 := bstep (se 1 (by rfl) ⟨3084560, by rfl⟩ : syracuseStep 4112747 = 6169121) B6169121
theorem B1827239 : Blo 1217426 1827239 := bstep (se 1 (by rfl) ⟨1370429, by rfl⟩ : syracuseStep 1827239 = 2740859) B2740859
theorem B13345249 : Blo 1217426 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B1827323 : Blo 1217426 1827323 := bstep (se 1 (by rfl) ⟨1370492, by rfl⟩ : syracuseStep 1827323 = 2740985) B2740985
theorem B1827449 : Blo 1217426 1827449 := bstep (se 2 (by rfl) ⟨685293, by rfl⟩ : syracuseStep 1827449 = 1370587) B1370587
theorem B4113017 : Blo 1217426 4113017 := bstep (se 2 (by rfl) ⟨1542381, by rfl⟩ : syracuseStep 4113017 = 3084763) B3084763
theorem B1827503 : Blo 1217426 1827503 := bstep (se 1 (by rfl) ⟨1370627, by rfl⟩ : syracuseStep 1827503 = 2741255) B2741255
theorem B2343647 : Blo 1217426 2343647 := bstep (se 1 (by rfl) ⟨1757735, by rfl⟩ : syracuseStep 2343647 = 3515471) B3515471
theorem B1827551 : Blo 1217426 1827551 := bstep (se 1 (by rfl) ⟨1370663, by rfl⟩ : syracuseStep 1827551 = 2741327) B2741327
theorem B2056927 : Blo 1217426 2056927 := bstep (se 1 (by rfl) ⟨1542695, by rfl⟩ : syracuseStep 2056927 = 3085391) B3085391
theorem B4391759 : Blo 1217426 4391759 := bstep (se 1 (by rfl) ⟨3293819, by rfl⟩ : syracuseStep 4391759 = 6587639) B6587639
theorem B9372611 : Blo 1217426 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B33776605 : Blo 1217426 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B1827815 : Blo 1217426 1827815 := bstep (se 1 (by rfl) ⟨1370861, by rfl⟩ : syracuseStep 1827815 = 2741723) B2741723
theorem B6169607 : Blo 1217426 6169607 := bstep (se 1 (by rfl) ⟨4627205, by rfl⟩ : syracuseStep 6169607 = 9254411) B9254411
theorem B5006479 : Blo 1217426 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B2057359 : Blo 1217426 2057359 := bstep (se 1 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 2057359 = 3086039) B3086039
theorem B9880775 : Blo 1217426 9880775 := bstep (se 1 (by rfl) ⟨7410581, by rfl⟩ : syracuseStep 9880775 = 14821163) B14821163
theorem B1828073 : Blo 1217426 1828073 := bstep (se 2 (by rfl) ⟨685527, by rfl⟩ : syracuseStep 1828073 = 1371055) B1371055
theorem B1828127 : Blo 1217426 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B112543019 : Blo 1217426 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B5555561 : Blo 1217426 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B2057609 : Blo 1217426 2057609 := bstep (se 2 (by rfl) ⟨771603, by rfl⟩ : syracuseStep 2057609 = 1543207) B1543207
theorem B3900811 : Blo 1217426 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1648039 : Blo 1217426 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B13878701 : Blo 1217426 13878701 := bstep (se 3 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 13878701 = 5204513) B5204513
theorem B1828295 : Blo 1217426 1828295 := bstep (se 1 (by rfl) ⟨1371221, by rfl⟩ : syracuseStep 1828295 = 2742443) B2742443
theorem B6170093 : Blo 1217426 6170093 := bstep (se 3 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 6170093 = 2313785) B2313785
theorem B5858905 : Blo 1217426 5858905 := bstep (se 2 (by rfl) ⟨2197089, by rfl⟩ : syracuseStep 5858905 = 4394179) B4394179
theorem B7808669 : Blo 1217426 7808669 := bstep (se 3 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 7808669 = 2928251) B2928251
theorem B2311841 : Blo 1217426 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B4392635 : Blo 1217426 4392635 := bstep (se 1 (by rfl) ⟨3294476, by rfl⟩ : syracuseStep 4392635 = 6588953) B6588953
theorem B1541855 : Blo 1217426 1541855 := bstep (se 1 (by rfl) ⟨1156391, by rfl⟩ : syracuseStep 1541855 = 2312783) B2312783
theorem B88991459 : Blo 1217426 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B1828649 : Blo 1217426 1828649 := bstep (se 2 (by rfl) ⟨685743, by rfl⟩ : syracuseStep 1828649 = 1371487) B1371487
theorem B1369903 : Blo 1217426 1369903 := bstep (se 1 (by rfl) ⟨1027427, by rfl⟩ : syracuseStep 1369903 = 2054855) B2054855
theorem B1828655 : Blo 1217426 1828655 := bstep (se 1 (by rfl) ⟨1371491, by rfl⟩ : syracuseStep 1828655 = 2742983) B2742983
theorem B2311993 : Blo 1217426 2311993 := bstep (se 2 (by rfl) ⟨866997, by rfl⟩ : syracuseStep 2311993 = 1733995) B1733995
theorem B3336041 : Blo 1217426 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B2967425 : Blo 1217426 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1370011 : Blo 1217426 1370011 := bstep (se 1 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 1370011 = 2055017) B2055017
theorem B3467215 : Blo 1217426 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B2312297 : Blo 1217426 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B7809209 : Blo 1217426 7809209 := bstep (se 2 (by rfl) ⟨2928453, by rfl⟩ : syracuseStep 7809209 = 5856907) B5856907
theorem B9251009 : Blo 1217426 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B1829129 : Blo 1217426 1829129 := bstep (se 2 (by rfl) ⟨685923, by rfl⟩ : syracuseStep 1829129 = 1371847) B1371847
theorem B6170903 : Blo 1217426 6170903 := bstep (se 1 (by rfl) ⟨4628177, by rfl⟩ : syracuseStep 6170903 = 9256355) B9256355
theorem B1370407 : Blo 1217426 1370407 := bstep (se 1 (by rfl) ⟨1027805, by rfl⟩ : syracuseStep 1370407 = 2055611) B2055611
theorem B3082607 : Blo 1217426 3082607 := bstep (se 1 (by rfl) ⟨2311955, by rfl⟩ : syracuseStep 3082607 = 4623911) B4623911
theorem B1370479 : Blo 1217426 1370479 := bstep (se 1 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 1370479 = 2055719) B2055719
theorem B4114799 : Blo 1217426 4114799 := bstep (se 1 (by rfl) ⟨3086099, by rfl⟩ : syracuseStep 4114799 = 6172199) B6172199
theorem B6252967 : Blo 1217426 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B2968019 : Blo 1217426 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B2779643 : Blo 1217426 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B1370695 : Blo 1217426 1370695 := bstep (se 1 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 1370695 = 2056043) B2056043
theorem B3295991 : Blo 1217426 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B3083255 : Blo 1217426 3083255 := bstep (se 1 (by rfl) ⟨2312441, by rfl⟩ : syracuseStep 3083255 = 4624883) B4624883
theorem B2739239 : Blo 1217426 2739239 := bstep (se 1 (by rfl) ⟨2054429, by rfl⟩ : syracuseStep 2739239 = 4108859) B4108859
theorem B9874547 : Blo 1217426 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B5205181 : Blo 1217426 5205181 := bstep (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) B1951943
theorem B2739419 : Blo 1217426 2739419 := bstep (se 1 (by rfl) ⟨2054564, by rfl⟩ : syracuseStep 2739419 = 4109129) B4109129
theorem B7032095 : Blo 1217426 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B4623713 : Blo 1217426 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B11873665 : Blo 1217426 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B2739617 : Blo 1217426 2739617 := bstep (se 2 (by rfl) ⟨1027356, by rfl⟩ : syracuseStep 2739617 = 2054713) B2054713
theorem B1371559 : Blo 1217426 1371559 := bstep (se 1 (by rfl) ⟨1028669, by rfl⟩ : syracuseStep 1371559 = 2057339) B2057339
theorem B7810769 : Blo 1217426 7810769 := bstep (se 2 (by rfl) ⟨2929038, by rfl⟩ : syracuseStep 7810769 = 5858077) B5858077
theorem B9383633 : Blo 1217426 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B4943663 : Blo 1217426 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B6172523 : Blo 1217426 6172523 := bstep (se 1 (by rfl) ⟨4629392, by rfl⟩ : syracuseStep 6172523 = 9258785) B9258785
theorem B2740175 : Blo 1217426 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B3805193 : Blo 1217426 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B6164585 : Blo 1217426 6164585 := bstep (se 2 (by rfl) ⟨2311719, by rfl⟩ : syracuseStep 6164585 = 4623439) B4623439
theorem B20820239 : Blo 1217426 20820239 := bstep (se 1 (by rfl) ⟨15615179, by rfl⟩ : syracuseStep 20820239 = 31230359) B31230359
theorem B2740553 : Blo 1217426 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B2740571 : Blo 1217426 2740571 := bstep (se 1 (by rfl) ⟨2055428, by rfl⟩ : syracuseStep 2740571 = 4110857) B4110857
theorem B4624897 : Blo 1217426 4624897 := bstep (se 2 (by rfl) ⟨1734336, by rfl⟩ : syracuseStep 4624897 = 3468673) B3468673
theorem B3904001 : Blo 1217426 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B2470583 : Blo 1217426 2470583 := bstep (se 1 (by rfl) ⟨1852937, by rfl⟩ : syracuseStep 2470583 = 3705875) B3705875
theorem B3085199 : Blo 1217426 3085199 := bstep (se 1 (by rfl) ⟨2313899, by rfl⟩ : syracuseStep 3085199 = 4627799) B4627799
theorem B1217435 : Blo 1217426 1217435 := bstep (se 1 (by rfl) ⟨913076, by rfl⟩ : syracuseStep 1217435 = 1826153) B1826153
theorem B2741147 : Blo 1217426 2741147 := bstep (se 1 (by rfl) ⟨2055860, by rfl⟩ : syracuseStep 2741147 = 4111721) B4111721
theorem B1217487 : Blo 1217426 1217487 := bstep (se 1 (by rfl) ⟨913115, by rfl⟩ : syracuseStep 1217487 = 1826231) B1826231
theorem B1217511 : Blo 1217426 1217511 := bstep (se 1 (by rfl) ⟨913133, by rfl⟩ : syracuseStep 1217511 = 1826267) B1826267
theorem B4625383 : Blo 1217426 4625383 := bstep (se 1 (by rfl) ⟨3469037, by rfl⟩ : syracuseStep 4625383 = 6938075) B6938075
theorem B10400825 : Blo 1217426 10400825 := bstep (se 2 (by rfl) ⟨3900309, by rfl⟩ : syracuseStep 10400825 = 7800619) B7800619
theorem B8787001 : Blo 1217426 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B2741345 : Blo 1217426 2741345 := bstep (se 2 (by rfl) ⟨1028004, by rfl⟩ : syracuseStep 2741345 = 2056009) B2056009
theorem B6165719 : Blo 1217426 6165719 := bstep (se 1 (by rfl) ⟨4624289, by rfl⟩ : syracuseStep 6165719 = 9248579) B9248579
theorem B6591721 : Blo 1217426 6591721 := bstep (se 2 (by rfl) ⟨2471895, by rfl⟩ : syracuseStep 6591721 = 4943791) B4943791
theorem B4109561 : Blo 1217426 4109561 := bstep (se 2 (by rfl) ⟨1541085, by rfl⟩ : syracuseStep 4109561 = 3082171) B3082171
theorem B4625657 : Blo 1217426 4625657 := bstep (se 2 (by rfl) ⟨1734621, by rfl⟩ : syracuseStep 4625657 = 3469243) B3469243
theorem B1217823 : Blo 1217426 1217823 := bstep (se 1 (by rfl) ⟨913367, by rfl⟩ : syracuseStep 1217823 = 1826735) B1826735
theorem B2741543 : Blo 1217426 2741543 := bstep (se 1 (by rfl) ⟨2056157, by rfl⟩ : syracuseStep 2741543 = 4112315) B4112315
theorem B21099865 : Blo 1217426 21099865 := bstep (se 2 (by rfl) ⟨7912449, by rfl⟩ : syracuseStep 21099865 = 15824899) B15824899
theorem B1217883 : Blo 1217426 1217883 := bstep (se 1 (by rfl) ⟨913412, by rfl⟩ : syracuseStep 1217883 = 1826825) B1826825
theorem B1217903 : Blo 1217426 1217903 := bstep (se 1 (by rfl) ⟨913427, by rfl⟩ : syracuseStep 1217903 = 1826855) B1826855
theorem B3126689 : Blo 1217426 3126689 := bstep (se 2 (by rfl) ⟨1172508, by rfl⟩ : syracuseStep 3126689 = 2345017) B2345017
theorem B1217959 : Blo 1217426 1217959 := bstep (se 1 (by rfl) ⟨913469, by rfl⟩ : syracuseStep 1217959 = 1826939) B1826939
theorem B1218043 : Blo 1217426 1218043 := bstep (se 1 (by rfl) ⟨913532, by rfl⟩ : syracuseStep 1218043 = 1827065) B1827065
theorem B4109831 : Blo 1217426 4109831 := bstep (se 1 (by rfl) ⟨3082373, by rfl⟩ : syracuseStep 4109831 = 6164747) B6164747
theorem B1218111 : Blo 1217426 1218111 := bstep (se 1 (by rfl) ⟨913583, by rfl⟩ : syracuseStep 1218111 = 1827167) B1827167
theorem B1218119 : Blo 1217426 1218119 := bstep (se 1 (by rfl) ⟨913589, by rfl⟩ : syracuseStep 1218119 = 1827179) B1827179
theorem B2741921 : Blo 1217426 2741921 := bstep (se 2 (by rfl) ⟨1028220, by rfl⟩ : syracuseStep 2741921 = 2056441) B2056441
theorem B1218271 : Blo 1217426 1218271 := bstep (se 1 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 1218271 = 1827407) B1827407
theorem B3086059 : Blo 1217426 3086059 := bstep (se 1 (by rfl) ⟨2314544, by rfl⟩ : syracuseStep 3086059 = 4629089) B4629089
theorem B1218351 : Blo 1217426 1218351 := bstep (se 1 (by rfl) ⟨913763, by rfl⟩ : syracuseStep 1218351 = 1827527) B1827527
theorem B1218459 : Blo 1217426 1218459 := bstep (se 1 (by rfl) ⟨913844, by rfl⟩ : syracuseStep 1218459 = 1827689) B1827689
theorem B1218511 : Blo 1217426 1218511 := bstep (se 1 (by rfl) ⟨913883, by rfl⟩ : syracuseStep 1218511 = 1827767) B1827767
theorem B1218535 : Blo 1217426 1218535 := bstep (se 1 (by rfl) ⟨913901, by rfl⟩ : syracuseStep 1218535 = 1827803) B1827803
theorem B2742281 : Blo 1217426 2742281 := bstep (se 2 (by rfl) ⟨1028355, by rfl⟩ : syracuseStep 2742281 = 2056711) B2056711
theorem B5937185 : Blo 1217426 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B106854551 : Blo 1217426 106854551 := bstep (se 1 (by rfl) ⟨80140913, by rfl⟩ : syracuseStep 106854551 = 160281827) B160281827
theorem B6019337 : Blo 1217426 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B1218847 : Blo 1217426 1218847 := bstep (se 1 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 1218847 = 1828271) B1828271
theorem B1218907 : Blo 1217426 1218907 := bstep (se 1 (by rfl) ⟨914180, by rfl⟩ : syracuseStep 1218907 = 1828361) B1828361
theorem B1218927 : Blo 1217426 1218927 := bstep (se 1 (by rfl) ⟨914195, by rfl⟩ : syracuseStep 1218927 = 1828391) B1828391
theorem B2742695 : Blo 1217426 2742695 := bstep (se 1 (by rfl) ⟨2057021, by rfl⟩ : syracuseStep 2742695 = 4114043) B4114043
theorem B1218983 : Blo 1217426 1218983 := bstep (se 1 (by rfl) ⟨914237, by rfl⟩ : syracuseStep 1218983 = 1828475) B1828475
theorem B3905975 : Blo 1217426 3905975 := bstep (se 1 (by rfl) ⟨2929481, by rfl⟩ : syracuseStep 3905975 = 5858963) B5858963
theorem B4110803 : Blo 1217426 4110803 := bstep (se 1 (by rfl) ⟨3083102, by rfl⟩ : syracuseStep 4110803 = 6166205) B6166205
theorem B1219067 : Blo 1217426 1219067 := bstep (se 1 (by rfl) ⟨914300, by rfl⟩ : syracuseStep 1219067 = 1828601) B1828601
theorem B2742803 : Blo 1217426 2742803 := bstep (se 1 (by rfl) ⟨2057102, by rfl⟩ : syracuseStep 2742803 = 4114205) B4114205
theorem B2193983 : Blo 1217426 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B4110911 : Blo 1217426 4110911 := bstep (se 1 (by rfl) ⟨3083183, by rfl⟩ : syracuseStep 4110911 = 6166367) B6166367
theorem B1219135 : Blo 1217426 1219135 := bstep (se 1 (by rfl) ⟨914351, by rfl⟩ : syracuseStep 1219135 = 1828703) B1828703
theorem B1219143 : Blo 1217426 1219143 := bstep (se 1 (by rfl) ⟨914357, by rfl⟩ : syracuseStep 1219143 = 1828715) B1828715
theorem B13875785 : Blo 1217426 13875785 := bstep (se 2 (by rfl) ⟨5203419, by rfl⟩ : syracuseStep 13875785 = 10406839) B10406839
theorem B2742857 : Blo 1217426 2742857 := bstep (se 2 (by rfl) ⟨1028571, by rfl⟩ : syracuseStep 2742857 = 2057143) B2057143
theorem B1219295 : Blo 1217426 1219295 := bstep (se 1 (by rfl) ⟨914471, by rfl⟩ : syracuseStep 1219295 = 1828943) B1828943
theorem B11123459 : Blo 1217426 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B1219375 : Blo 1217426 1219375 := bstep (se 1 (by rfl) ⟨914531, by rfl⟩ : syracuseStep 1219375 = 1829063) B1829063
theorem B9247607 : Blo 1217426 9247607 := bstep (se 1 (by rfl) ⟨6935705, by rfl⟩ : syracuseStep 9247607 = 13871411) B13871411
theorem B4635535 : Blo 1217426 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B2743271 : Blo 1217426 2743271 := bstep (se 1 (by rfl) ⟨2057453, by rfl⟩ : syracuseStep 2743271 = 4114907) B4114907
theorem B35585011 : Blo 1217426 35585011 := bstep (se 1 (by rfl) ⟨26688758, by rfl⟩ : syracuseStep 35585011 = 53377517) B53377517
theorem B23411699 : Blo 1217426 23411699 := bstep (se 1 (by rfl) ⟨17558774, by rfl⟩ : syracuseStep 23411699 = 35117549) B35117549
theorem B7413059 : Blo 1217426 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B2743649 : Blo 1217426 2743649 := bstep (se 2 (by rfl) ⟨1028868, by rfl⟩ : syracuseStep 2743649 = 2057737) B2057737
theorem B1826171 : Blo 1217426 1826171 := bstep (se 1 (by rfl) ⟨1369628, by rfl⟩ : syracuseStep 1826171 = 2739257) B2739257
theorem B1826297 : Blo 1217426 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B1826399 : Blo 1217426 1826399 := bstep (se 1 (by rfl) ⟨1369799, by rfl⟩ : syracuseStep 1826399 = 2739599) B2739599
theorem B10403423 : Blo 1217426 10403423 := bstep (se 1 (by rfl) ⟨7802567, by rfl⟩ : syracuseStep 10403423 = 15605135) B15605135
theorem B1826615 : Blo 1217426 1826615 := bstep (se 1 (by rfl) ⟨1369961, by rfl⟩ : syracuseStep 1826615 = 2739923) B2739923
theorem B4628285 : Blo 1217426 4628285 := bstep (se 3 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 4628285 = 1735607) B1735607
theorem B4112423 : Blo 1217426 4112423 := bstep (se 1 (by rfl) ⟨3084317, by rfl⟩ : syracuseStep 4112423 = 6168635) B6168635
theorem B1827035 : Blo 1217426 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B1827047 : Blo 1217426 1827047 := bstep (se 1 (by rfl) ⟨1370285, by rfl⟩ : syracuseStep 1827047 = 2740571) B2740571
theorem B1827209 : Blo 1217426 1827209 := bstep (se 2 (by rfl) ⟨685203, by rfl⟩ : syracuseStep 1827209 = 1370407) B1370407
theorem B1647055 : Blo 1217426 1647055 := bstep (se 1 (by rfl) ⟨1235291, by rfl⟩ : syracuseStep 1647055 = 2470583) B2470583
theorem B1827305 : Blo 1217426 1827305 := bstep (se 2 (by rfl) ⟨685239, by rfl⟩ : syracuseStep 1827305 = 1370479) B1370479
theorem B2056799 : Blo 1217426 2056799 := bstep (se 1 (by rfl) ⟨1542599, by rfl⟩ : syracuseStep 2056799 = 3085199) B3085199
theorem B1827431 : Blo 1217426 1827431 := bstep (se 1 (by rfl) ⟨1370573, by rfl⟩ : syracuseStep 1827431 = 2741147) B2741147
theorem B17793665 : Blo 1217426 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B4113071 : Blo 1217426 4113071 := bstep (se 1 (by rfl) ⟨3084803, by rfl⟩ : syracuseStep 4113071 = 6169607) B6169607
theorem B1827563 : Blo 1217426 1827563 := bstep (se 1 (by rfl) ⟨1370672, by rfl⟩ : syracuseStep 1827563 = 2741345) B2741345
theorem B1827593 : Blo 1217426 1827593 := bstep (se 2 (by rfl) ⟨685347, by rfl⟩ : syracuseStep 1827593 = 1370695) B1370695
theorem B6587183 : Blo 1217426 6587183 := bstep (se 1 (by rfl) ⟨4940387, by rfl⟩ : syracuseStep 6587183 = 9880775) B9880775
theorem B19768157 : Blo 1217426 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B1827695 : Blo 1217426 1827695 := bstep (se 1 (by rfl) ⟨1370771, by rfl⟩ : syracuseStep 1827695 = 2741543) B2741543
theorem B4113395 : Blo 1217426 4113395 := bstep (se 1 (by rfl) ⟨3085046, by rfl⟩ : syracuseStep 4113395 = 6170093) B6170093
theorem B1827947 : Blo 1217426 1827947 := bstep (se 1 (by rfl) ⟨1370960, by rfl⟩ : syracuseStep 1827947 = 2741921) B2741921
theorem B59327639 : Blo 1217426 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B1828187 : Blo 1217426 1828187 := bstep (se 1 (by rfl) ⟨1371140, by rfl⟩ : syracuseStep 1828187 = 2742281) B2742281
theorem B1541531 : Blo 1217426 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B11716001 : Blo 1217426 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B4113935 : Blo 1217426 4113935 := bstep (se 1 (by rfl) ⟨3085451, by rfl⟩ : syracuseStep 4113935 = 6170903) B6170903
theorem B6940241 : Blo 1217426 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B1828463 : Blo 1217426 1828463 := bstep (se 1 (by rfl) ⟨1371347, by rfl⟩ : syracuseStep 1828463 = 2742695) B2742695
theorem B1828535 : Blo 1217426 1828535 := bstep (se 1 (by rfl) ⟨1371401, by rfl⟩ : syracuseStep 1828535 = 2742803) B2742803
theorem B9250523 : Blo 1217426 9250523 := bstep (se 1 (by rfl) ⟨6937892, by rfl⟩ : syracuseStep 9250523 = 13875785) B13875785
theorem B1828571 : Blo 1217426 1828571 := bstep (se 1 (by rfl) ⟨1371428, by rfl⟩ : syracuseStep 1828571 = 2742857) B2742857
theorem B28133153 : Blo 1217426 28133153 := bstep (se 2 (by rfl) ⟨10549932, by rfl⟩ : syracuseStep 28133153 = 21099865) B21099865
theorem B7415639 : Blo 1217426 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B1828745 : Blo 1217426 1828745 := bstep (se 2 (by rfl) ⟨685779, by rfl⟩ : syracuseStep 1828745 = 1371559) B1371559
theorem B2197385 : Blo 1217426 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B1828847 : Blo 1217426 1828847 := bstep (se 1 (by rfl) ⟨1371635, by rfl⟩ : syracuseStep 1828847 = 2743271) B2743271
theorem B15607799 : Blo 1217426 15607799 := bstep (se 1 (by rfl) ⟨11705849, by rfl⟩ : syracuseStep 15607799 = 23411699) B23411699
theorem B4688063 : Blo 1217426 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B3082475 : Blo 1217426 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B1829099 : Blo 1217426 1829099 := bstep (se 1 (by rfl) ⟨1371824, by rfl⟩ : syracuseStep 1829099 = 2743649) B2743649
theorem B4114745 : Blo 1217426 4114745 := bstep (se 2 (by rfl) ⟨1543029, by rfl⟩ : syracuseStep 4114745 = 3086059) B3086059
theorem B3082657 : Blo 1217426 3082657 := bstep (se 2 (by rfl) ⟨1155996, by rfl⟩ : syracuseStep 3082657 = 2311993) B2311993
theorem B3295775 : Blo 1217426 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B4115015 : Blo 1217426 4115015 := bstep (se 1 (by rfl) ⟨3086261, by rfl⟩ : syracuseStep 4115015 = 6172523) B6172523
theorem B4622953 : Blo 1217426 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B9513655 : Blo 1217426 9513655 := bstep (se 1 (by rfl) ⟨7135241, by rfl⟩ : syracuseStep 9513655 = 14270483) B14270483
theorem B13880159 : Blo 1217426 13880159 := bstep (se 1 (by rfl) ⟨10410119, by rfl⟩ : syracuseStep 13880159 = 20820239) B20820239
theorem B2927839 : Blo 1217426 2927839 := bstep (se 1 (by rfl) ⟨2195879, by rfl⟩ : syracuseStep 2927839 = 4391759) B4391759
theorem B6933883 : Blo 1217426 6933883 := bstep (se 1 (by rfl) ⟨5200412, by rfl⟩ : syracuseStep 6933883 = 10400825) B10400825
theorem B2739707 : Blo 1217426 2739707 := bstep (se 1 (by rfl) ⟨2054780, by rfl⟩ : syracuseStep 2739707 = 4109561) B4109561
theorem B3083771 : Blo 1217426 3083771 := bstep (se 1 (by rfl) ⟨2312828, by rfl⟩ : syracuseStep 3083771 = 4625657) B4625657
theorem B1371739 : Blo 1217426 1371739 := bstep (se 1 (by rfl) ⟨1028804, by rfl⟩ : syracuseStep 1371739 = 2057609) B2057609
theorem B2084459 : Blo 1217426 2084459 := bstep (se 1 (by rfl) ⟨1563344, by rfl⟩ : syracuseStep 2084459 = 3126689) B3126689
theorem B14814829 : Blo 1217426 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B9252467 : Blo 1217426 9252467 := bstep (se 1 (by rfl) ⟨6939350, by rfl⟩ : syracuseStep 9252467 = 13878701) B13878701
theorem B2739887 : Blo 1217426 2739887 := bstep (se 1 (by rfl) ⟨2054915, by rfl⟩ : syracuseStep 2739887 = 4109831) B4109831
theorem B5205779 : Blo 1217426 5205779 := bstep (se 1 (by rfl) ⟨3904334, by rfl⟩ : syracuseStep 5205779 = 7808669) B7808669
theorem B6180713 : Blo 1217426 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B2224027 : Blo 1217426 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B1978283 : Blo 1217426 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B5206139 : Blo 1217426 5206139 := bstep (se 1 (by rfl) ⟨3904604, by rfl⟩ : syracuseStep 5206139 = 7809209) B7809209
theorem B2740535 : Blo 1217426 2740535 := bstep (se 1 (by rfl) ⟨2055401, by rfl⟩ : syracuseStep 2740535 = 4110803) B4110803
theorem B1978679 : Blo 1217426 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B1462655 : Blo 1217426 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B2740607 : Blo 1217426 2740607 := bstep (se 1 (by rfl) ⟨2055455, by rfl⟩ : syracuseStep 2740607 = 4110911) B4110911
theorem B6164909 : Blo 1217426 6164909 := bstep (se 3 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 6164909 = 2311841) B2311841
theorem B15831553 : Blo 1217426 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B6165071 : Blo 1217426 6165071 := bstep (se 1 (by rfl) ⟨4623803, by rfl⟩ : syracuseStep 6165071 = 9247607) B9247607
theorem B6583031 : Blo 1217426 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B7811873 : Blo 1217426 7811873 := bstep (se 2 (by rfl) ⟨2929452, by rfl⟩ : syracuseStep 7811873 = 5858905) B5858905
theorem B1217447 : Blo 1217426 1217447 := bstep (se 1 (by rfl) ⟨913085, by rfl⟩ : syracuseStep 1217447 = 1826171) B1826171
theorem B1217531 : Blo 1217426 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B1217599 : Blo 1217426 1217599 := bstep (se 1 (by rfl) ⟨913199, by rfl⟩ : syracuseStep 1217599 = 1826399) B1826399
theorem B6935615 : Blo 1217426 6935615 := bstep (se 1 (by rfl) ⟨5201711, by rfl⟩ : syracuseStep 6935615 = 10403423) B10403423
theorem B5207179 : Blo 1217426 5207179 := bstep (se 1 (by rfl) ⟨3905384, by rfl⟩ : syracuseStep 5207179 = 7810769) B7810769
theorem B6255755 : Blo 1217426 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B1217743 : Blo 1217426 1217743 := bstep (se 1 (by rfl) ⟨913307, by rfl⟩ : syracuseStep 1217743 = 1826615) B1826615
theorem B3085523 : Blo 1217426 3085523 := bstep (se 1 (by rfl) ⟨2314142, by rfl⟩ : syracuseStep 3085523 = 4628285) B4628285
theorem B2536795 : Blo 1217426 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B4109723 : Blo 1217426 4109723 := bstep (se 1 (by rfl) ⟨3082292, by rfl⟩ : syracuseStep 4109723 = 6164585) B6164585
theorem B1217947 : Blo 1217426 1217947 := bstep (se 1 (by rfl) ⟨913460, by rfl⟩ : syracuseStep 1217947 = 1826921) B1826921
theorem B15832493 : Blo 1217426 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B9885115 : Blo 1217426 9885115 := bstep (se 1 (by rfl) ⟨7413836, by rfl⟩ : syracuseStep 9885115 = 14827673) B14827673
theorem B2741831 : Blo 1217426 2741831 := bstep (se 1 (by rfl) ⟨2056373, by rfl⟩ : syracuseStep 2741831 = 4112747) B4112747
theorem B1218159 : Blo 1217426 1218159 := bstep (se 1 (by rfl) ⟨913619, by rfl⟩ : syracuseStep 1218159 = 1827239) B1827239
theorem B1218215 : Blo 1217426 1218215 := bstep (se 1 (by rfl) ⟨913661, by rfl⟩ : syracuseStep 1218215 = 1827323) B1827323
theorem B2602667 : Blo 1217426 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B1218299 : Blo 1217426 1218299 := bstep (se 1 (by rfl) ⟨913724, by rfl⟩ : syracuseStep 1218299 = 1827449) B1827449
theorem B2742011 : Blo 1217426 2742011 := bstep (se 1 (by rfl) ⟨2056508, by rfl⟩ : syracuseStep 2742011 = 4113017) B4113017
theorem B1218335 : Blo 1217426 1218335 := bstep (se 1 (by rfl) ⟨913751, by rfl⟩ : syracuseStep 1218335 = 1827503) B1827503
theorem B1562431 : Blo 1217426 1562431 := bstep (se 1 (by rfl) ⟨1171823, by rfl⟩ : syracuseStep 1562431 = 2343647) B2343647
theorem B1218367 : Blo 1217426 1218367 := bstep (se 1 (by rfl) ⟨913775, by rfl⟩ : syracuseStep 1218367 = 1827551) B1827551
theorem B8337289 : Blo 1217426 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B1218543 : Blo 1217426 1218543 := bstep (se 1 (by rfl) ⟨913907, by rfl⟩ : syracuseStep 1218543 = 1827815) B1827815
theorem B6166529 : Blo 1217426 6166529 := bstep (se 2 (by rfl) ⟨2312448, by rfl⟩ : syracuseStep 6166529 = 4624897) B4624897
theorem B4110479 : Blo 1217426 4110479 := bstep (se 1 (by rfl) ⟨3082859, by rfl⟩ : syracuseStep 4110479 = 6165719) B6165719
theorem B1218715 : Blo 1217426 1218715 := bstep (se 1 (by rfl) ⟨914036, by rfl⟩ : syracuseStep 1218715 = 1828073) B1828073
theorem B1218751 : Blo 1217426 1218751 := bstep (se 1 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 1218751 = 1828127) B1828127
theorem B75028679 : Blo 1217426 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B2742569 : Blo 1217426 2742569 := bstep (se 2 (by rfl) ⟨1028463, by rfl⟩ : syracuseStep 2742569 = 2056927) B2056927
theorem B1218863 : Blo 1217426 1218863 := bstep (se 1 (by rfl) ⟨914147, by rfl⟩ : syracuseStep 1218863 = 1828295) B1828295
theorem B1219099 : Blo 1217426 1219099 := bstep (se 1 (by rfl) ⟨914324, by rfl⟩ : syracuseStep 1219099 = 1828649) B1828649
theorem B1219103 : Blo 1217426 1219103 := bstep (se 1 (by rfl) ⟨914327, by rfl⟩ : syracuseStep 1219103 = 1828655) B1828655
theorem B6167177 : Blo 1217426 6167177 := bstep (se 2 (by rfl) ⟨2312691, by rfl⟩ : syracuseStep 6167177 = 4625383) B4625383
theorem B47446681 : Blo 1217426 47446681 := bstep (se 2 (by rfl) ⟨17792505, by rfl⟩ : syracuseStep 47446681 = 35585011) B35585011
theorem B7412381 : Blo 1217426 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B71236367 : Blo 1217426 71236367 := bstep (se 1 (by rfl) ⟨53427275, by rfl⟩ : syracuseStep 71236367 = 106854551) B106854551
theorem B6167339 : Blo 1217426 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B4012891 : Blo 1217426 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B1219419 : Blo 1217426 1219419 := bstep (se 1 (by rfl) ⟨914564, by rfl⟩ : syracuseStep 1219419 = 1829129) B1829129
theorem B6675305 : Blo 1217426 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B2743145 : Blo 1217426 2743145 := bstep (se 2 (by rfl) ⟨1028679, by rfl⟩ : syracuseStep 2743145 = 2057359) B2057359
theorem B2055071 : Blo 1217426 2055071 := bstep (se 1 (by rfl) ⟨1541303, by rfl⟩ : syracuseStep 2055071 = 3082607) B3082607
theorem B2743199 : Blo 1217426 2743199 := bstep (se 1 (by rfl) ⟨2057399, by rfl⟩ : syracuseStep 2743199 = 4114799) B4114799
theorem B2603983 : Blo 1217426 2603983 := bstep (se 1 (by rfl) ⟨1952987, by rfl⟩ : syracuseStep 2603983 = 3905975) B3905975
theorem B8788961 : Blo 1217426 8788961 := bstep (se 2 (by rfl) ⟨3295860, by rfl⟩ : syracuseStep 8788961 = 6591721) B6591721
theorem B11713693 : Blo 1217426 11713693 := bstep (se 3 (by rfl) ⟨2196317, by rfl⟩ : syracuseStep 11713693 = 4392635) B4392635
theorem B5201081 : Blo 1217426 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B4111613 : Blo 1217426 4111613 := bstep (se 3 (by rfl) ⟨770927, by rfl⟩ : syracuseStep 4111613 = 1541855) B1541855
theorem B8789309 : Blo 1217426 8789309 := bstep (se 3 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 8789309 = 3295991) B3295991
theorem B2055503 : Blo 1217426 2055503 := bstep (se 1 (by rfl) ⟨1541627, by rfl⟩ : syracuseStep 2055503 = 3083255) B3083255
theorem B1826159 : Blo 1217426 1826159 := bstep (se 1 (by rfl) ⟨1369619, by rfl⟩ : syracuseStep 1826159 = 2739239) B2739239
theorem B1826279 : Blo 1217426 1826279 := bstep (se 1 (by rfl) ⟨1369709, by rfl⟩ : syracuseStep 1826279 = 2739419) B2739419
theorem B1826411 : Blo 1217426 1826411 := bstep (se 1 (by rfl) ⟨1369808, by rfl⟩ : syracuseStep 1826411 = 2739617) B2739617
theorem B1826537 : Blo 1217426 1826537 := bstep (se 2 (by rfl) ⟨684951, by rfl⟩ : syracuseStep 1826537 = 1369903) B1369903
theorem B180141893 : Blo 1217426 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B24993629 : Blo 1217426 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B1826681 : Blo 1217426 1826681 := bstep (se 2 (by rfl) ⟨685005, by rfl⟩ : syracuseStep 1826681 = 1370011) B1370011
theorem B1826783 : Blo 1217426 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B1827023 : Blo 1217426 1827023 := bstep (se 1 (by rfl) ⟨1370267, by rfl⟩ : syracuseStep 1827023 = 2740535) B2740535
theorem B1827071 : Blo 1217426 1827071 := bstep (se 1 (by rfl) ⟨1370303, by rfl⟩ : syracuseStep 1827071 = 2740607) B2740607
theorem B11862443 : Blo 1217426 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B4391455 : Blo 1217426 4391455 := bstep (se 1 (by rfl) ⟨3293591, by rfl⟩ : syracuseStep 4391455 = 6587183) B6587183
theorem B2196073 : Blo 1217426 2196073 := bstep (se 2 (by rfl) ⟨823527, by rfl⟩ : syracuseStep 2196073 = 1647055) B1647055
theorem B4170503 : Blo 1217426 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B39551759 : Blo 1217426 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B2057015 : Blo 1217426 2057015 := bstep (se 1 (by rfl) ⟨1542761, by rfl⟩ : syracuseStep 2057015 = 3085523) B3085523
theorem B5276477 : Blo 1217426 5276477 := bstep (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) B1978679
theorem B3900413 : Blo 1217426 3900413 := bstep (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) B1462655
theorem B1827887 : Blo 1217426 1827887 := bstep (se 1 (by rfl) ⟨1370915, by rfl⟩ : syracuseStep 1827887 = 2741831) B2741831
theorem B1828007 : Blo 1217426 1828007 := bstep (se 1 (by rfl) ⟨1371005, by rfl⟩ : syracuseStep 1828007 = 2742011) B2742011
theorem B10405199 : Blo 1217426 10405199 := bstep (se 1 (by rfl) ⟨7803899, by rfl⟩ : syracuseStep 10405199 = 15607799) B15607799
theorem B1828379 : Blo 1217426 1828379 := bstep (se 1 (by rfl) ⟨1371284, by rfl⟩ : syracuseStep 1828379 = 2742569) B2742569
theorem B4941587 : Blo 1217426 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B47490911 : Blo 1217426 47490911 := bstep (se 1 (by rfl) ⟨35618183, by rfl⟩ : syracuseStep 47490911 = 71236367) B71236367
theorem B1828763 : Blo 1217426 1828763 := bstep (se 1 (by rfl) ⟨1371572, by rfl⟩ : syracuseStep 1828763 = 2743145) B2743145
theorem B1370047 : Blo 1217426 1370047 := bstep (se 1 (by rfl) ⟨1027535, by rfl⟩ : syracuseStep 1370047 = 2055071) B2055071
theorem B1828799 : Blo 1217426 1828799 := bstep (se 1 (by rfl) ⟨1371599, by rfl⟩ : syracuseStep 1828799 = 2743199) B2743199
theorem B5859307 : Blo 1217426 5859307 := bstep (se 1 (by rfl) ⟨4394480, by rfl⟩ : syracuseStep 5859307 = 8788961) B8788961
theorem B1828985 : Blo 1217426 1828985 := bstep (se 2 (by rfl) ⟨685869, by rfl⟩ : syracuseStep 1828985 = 1371739) B1371739
theorem B3467387 : Blo 1217426 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B19753105 : Blo 1217426 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B5859539 : Blo 1217426 5859539 := bstep (se 1 (by rfl) ⟨4394654, by rfl⟩ : syracuseStep 5859539 = 8789309) B8789309
theorem B1370335 : Blo 1217426 1370335 := bstep (se 1 (by rfl) ⟨1027751, by rfl⟩ : syracuseStep 1370335 = 2055503) B2055503
theorem B2083241 : Blo 1217426 2083241 := bstep (se 2 (by rfl) ⟨781215, by rfl⟩ : syracuseStep 2083241 = 1562431) B1562431
theorem B1371199 : Blo 1217426 1371199 := bstep (se 1 (by rfl) ⟨1028399, by rfl⟩ : syracuseStep 1371199 = 2056799) B2056799
theorem B4623743 : Blo 1217426 4623743 := bstep (se 1 (by rfl) ⟨3467807, by rfl⟩ : syracuseStep 4623743 = 6935615) B6935615
theorem B6163937 : Blo 1217426 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B63262241 : Blo 1217426 63262241 := bstep (se 2 (by rfl) ⟨23723340, by rfl⟩ : syracuseStep 63262241 = 47446681) B47446681
theorem B2739815 : Blo 1217426 2739815 := bstep (se 1 (by rfl) ⟨2054861, by rfl⟩ : syracuseStep 2739815 = 4109723) B4109723
theorem B7810667 : Blo 1217426 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B10554995 : Blo 1217426 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B18755435 : Blo 1217426 18755435 := bstep (se 1 (by rfl) ⟨14066576, by rfl⟩ : syracuseStep 18755435 = 28133153) B28133153
theorem B4943759 : Blo 1217426 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B2740319 : Blo 1217426 2740319 := bstep (se 1 (by rfl) ⟨2055239, by rfl⟩ : syracuseStep 2740319 = 4110479) B4110479
theorem B3125375 : Blo 1217426 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B6942905 : Blo 1217426 6942905 := bstep (se 2 (by rfl) ⟨2603589, by rfl⟩ : syracuseStep 6942905 = 5207179) B5207179
theorem B15618257 : Blo 1217426 15618257 := bstep (se 2 (by rfl) ⟨5856846, by rfl⟩ : syracuseStep 15618257 = 11713693) B11713693
theorem B5558557 : Blo 1217426 5558557 := bstep (se 3 (by rfl) ⟨1042229, by rfl⟩ : syracuseStep 5558557 = 2084459) B2084459
theorem B3903785 : Blo 1217426 3903785 := bstep (se 2 (by rfl) ⟨1463919, by rfl⟩ : syracuseStep 3903785 = 2927839) B2927839
theorem B21402085 : Blo 1217426 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B9245177 : Blo 1217426 9245177 := bstep (se 2 (by rfl) ⟨3466941, by rfl⟩ : syracuseStep 9245177 = 6933883) B6933883
theorem B9253439 : Blo 1217426 9253439 := bstep (se 1 (by rfl) ⟨6940079, by rfl⟩ : syracuseStep 9253439 = 13880159) B13880159
theorem B2741075 : Blo 1217426 2741075 := bstep (se 1 (by rfl) ⟨2055806, by rfl⟩ : syracuseStep 2741075 = 4111613) B4111613
theorem B1217439 : Blo 1217426 1217439 := bstep (se 1 (by rfl) ⟨913079, by rfl⟩ : syracuseStep 1217439 = 1826159) B1826159
theorem B1217519 : Blo 1217426 1217519 := bstep (se 1 (by rfl) ⟨913139, by rfl⟩ : syracuseStep 1217519 = 1826279) B1826279
theorem B1217607 : Blo 1217426 1217607 := bstep (se 1 (by rfl) ⟨913205, by rfl⟩ : syracuseStep 1217607 = 1826411) B1826411
theorem B1217691 : Blo 1217426 1217691 := bstep (se 1 (by rfl) ⟨913268, by rfl⟩ : syracuseStep 1217691 = 1826537) B1826537
theorem B3470519 : Blo 1217426 3470519 := bstep (se 1 (by rfl) ⟨2602889, by rfl⟩ : syracuseStep 3470519 = 5205779) B5205779
theorem B1217787 : Blo 1217426 1217787 := bstep (se 1 (by rfl) ⟨913340, by rfl⟩ : syracuseStep 1217787 = 1826681) B1826681
theorem B1217855 : Blo 1217426 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B2741615 : Blo 1217426 2741615 := bstep (se 1 (by rfl) ⟨2056211, by rfl⟩ : syracuseStep 2741615 = 4112423) B4112423
theorem B3470759 : Blo 1217426 3470759 := bstep (se 1 (by rfl) ⟨2603069, by rfl⟩ : syracuseStep 3470759 = 5206139) B5206139
theorem B1218023 : Blo 1217426 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1218031 : Blo 1217426 1218031 := bstep (se 1 (by rfl) ⟨913523, by rfl⟩ : syracuseStep 1218031 = 1827047) B1827047
theorem B1218139 : Blo 1217426 1218139 := bstep (se 1 (by rfl) ⟨913604, by rfl⟩ : syracuseStep 1218139 = 1827209) B1827209
theorem B4109939 : Blo 1217426 4109939 := bstep (se 1 (by rfl) ⟨3082454, by rfl⟩ : syracuseStep 4109939 = 6164909) B6164909
theorem B1218203 : Blo 1217426 1218203 := bstep (se 1 (by rfl) ⟨913652, by rfl⟩ : syracuseStep 1218203 = 1827305) B1827305
theorem B4110047 : Blo 1217426 4110047 := bstep (se 1 (by rfl) ⟨3082535, by rfl⟩ : syracuseStep 4110047 = 6165071) B6165071
theorem B1218287 : Blo 1217426 1218287 := bstep (se 1 (by rfl) ⟨913715, by rfl⟩ : syracuseStep 1218287 = 1827431) B1827431
theorem B2742047 : Blo 1217426 2742047 := bstep (se 1 (by rfl) ⟨2056535, by rfl⟩ : syracuseStep 2742047 = 4113071) B4113071
theorem B1218375 : Blo 1217426 1218375 := bstep (se 1 (by rfl) ⟨913781, by rfl⟩ : syracuseStep 1218375 = 1827563) B1827563
theorem B4388687 : Blo 1217426 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B1218395 : Blo 1217426 1218395 := bstep (se 1 (by rfl) ⟨913796, by rfl⟩ : syracuseStep 1218395 = 1827593) B1827593
theorem B5207915 : Blo 1217426 5207915 := bstep (se 1 (by rfl) ⟨3905936, by rfl⟩ : syracuseStep 5207915 = 7811873) B7811873
theorem B4110209 : Blo 1217426 4110209 := bstep (se 2 (by rfl) ⟨1541328, by rfl⟩ : syracuseStep 4110209 = 3082657) B3082657
theorem B13178771 : Blo 1217426 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B1218463 : Blo 1217426 1218463 := bstep (se 1 (by rfl) ⟨913847, by rfl⟩ : syracuseStep 1218463 = 1827695) B1827695
theorem B2742263 : Blo 1217426 2742263 := bstep (se 1 (by rfl) ⟨2056697, by rfl⟩ : syracuseStep 2742263 = 4113395) B4113395
theorem B21108737 : Blo 1217426 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B1218631 : Blo 1217426 1218631 := bstep (se 1 (by rfl) ⟨913973, by rfl⟩ : syracuseStep 1218631 = 1827947) B1827947
theorem B1218791 : Blo 1217426 1218791 := bstep (se 1 (by rfl) ⟨914093, by rfl⟩ : syracuseStep 1218791 = 1828187) B1828187
theorem B50739493 : Blo 1217426 50739493 := bstep (se 4 (by rfl) ⟨4756827, by rfl⟩ : syracuseStep 50739493 = 9513655) B9513655
theorem B2742623 : Blo 1217426 2742623 := bstep (se 1 (by rfl) ⟨2056967, by rfl⟩ : syracuseStep 2742623 = 4113935) B4113935
theorem B4626827 : Blo 1217426 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B4110749 : Blo 1217426 4110749 := bstep (se 3 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 4110749 = 1541531) B1541531
theorem B1218975 : Blo 1217426 1218975 := bstep (se 1 (by rfl) ⟨914231, by rfl⟩ : syracuseStep 1218975 = 1828463) B1828463
theorem B1735111 : Blo 1217426 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B1219023 : Blo 1217426 1219023 := bstep (se 1 (by rfl) ⟨914267, by rfl⟩ : syracuseStep 1219023 = 1828535) B1828535
theorem B6167015 : Blo 1217426 6167015 := bstep (se 1 (by rfl) ⟨4625261, by rfl⟩ : syracuseStep 6167015 = 9250523) B9250523
theorem B1219047 : Blo 1217426 1219047 := bstep (se 1 (by rfl) ⟨914285, by rfl⟩ : syracuseStep 1219047 = 1828571) B1828571
theorem B1219163 : Blo 1217426 1219163 := bstep (se 1 (by rfl) ⟨914372, by rfl⟩ : syracuseStep 1219163 = 1828745) B1828745
theorem B1464923 : Blo 1217426 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B3471977 : Blo 1217426 3471977 := bstep (se 2 (by rfl) ⟨1301991, by rfl⟩ : syracuseStep 3471977 = 2603983) B2603983
theorem B1219231 : Blo 1217426 1219231 := bstep (se 1 (by rfl) ⟨914423, by rfl⟩ : syracuseStep 1219231 = 1828847) B1828847
theorem B4111019 : Blo 1217426 4111019 := bstep (se 1 (by rfl) ⟨3083264, by rfl⟩ : syracuseStep 4111019 = 6166529) B6166529
theorem B8788733 : Blo 1217426 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B50019119 : Blo 1217426 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B2054983 : Blo 1217426 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B1219399 : Blo 1217426 1219399 := bstep (se 1 (by rfl) ⟨914549, by rfl⟩ : syracuseStep 1219399 = 1829099) B1829099
theorem B2743163 : Blo 1217426 2743163 := bstep (se 1 (by rfl) ⟨2057372, by rfl⟩ : syracuseStep 2743163 = 4114745) B4114745
theorem B2743343 : Blo 1217426 2743343 := bstep (se 1 (by rfl) ⟨2057507, by rfl⟩ : syracuseStep 2743343 = 4115015) B4115015
theorem B4111451 : Blo 1217426 4111451 := bstep (se 1 (by rfl) ⟨3083588, by rfl⟩ : syracuseStep 4111451 = 6167177) B6167177
theorem B3382393 : Blo 1217426 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B4111559 : Blo 1217426 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B13180153 : Blo 1217426 13180153 := bstep (se 2 (by rfl) ⟨4942557, by rfl⟩ : syracuseStep 13180153 = 9885115) B9885115
theorem B11861477 : Blo 1217426 11861477 := bstep (se 4 (by rfl) ⟨1112013, by rfl⟩ : syracuseStep 11861477 = 2224027) B2224027
theorem B17800813 : Blo 1217426 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B1826471 : Blo 1217426 1826471 := bstep (se 1 (by rfl) ⟨1369853, by rfl⟩ : syracuseStep 1826471 = 2739707) B2739707
theorem B2055847 : Blo 1217426 2055847 := bstep (se 1 (by rfl) ⟨1541885, by rfl⟩ : syracuseStep 2055847 = 3083771) B3083771
theorem B6168311 : Blo 1217426 6168311 := bstep (se 1 (by rfl) ⟨4626233, by rfl⟩ : syracuseStep 6168311 = 9252467) B9252467
theorem B5275421 : Blo 1217426 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B1826591 : Blo 1217426 1826591 := bstep (se 1 (by rfl) ⟨1369943, by rfl⟩ : syracuseStep 1826591 = 2739887) B2739887
theorem B11116385 : Blo 1217426 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B120094595 : Blo 1217426 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B16662419 : Blo 1217426 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B4120475 : Blo 1217426 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B1826879 : Blo 1217426 1826879 := bstep (se 1 (by rfl) ⟨1370159, by rfl⟩ : syracuseStep 1826879 = 2740319) B2740319
theorem B4628603 : Blo 1217426 4628603 := bstep (se 1 (by rfl) ⟨3471452, by rfl⟩ : syracuseStep 4628603 = 6942905) B6942905
theorem B10412171 : Blo 1217426 10412171 := bstep (se 1 (by rfl) ⟨7809128, by rfl⟩ : syracuseStep 10412171 = 15618257) B15618257
theorem B26337473 : Blo 1217426 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B1827113 : Blo 1217426 1827113 := bstep (se 2 (by rfl) ⟨685167, by rfl⟩ : syracuseStep 1827113 = 1370335) B1370335
theorem B6168959 : Blo 1217426 6168959 := bstep (se 1 (by rfl) ⟨4626719, by rfl⟩ : syracuseStep 6168959 = 9253439) B9253439
theorem B1827383 : Blo 1217426 1827383 := bstep (se 1 (by rfl) ⟨1370537, by rfl⟩ : syracuseStep 1827383 = 2741075) B2741075
theorem B1827743 : Blo 1217426 1827743 := bstep (se 1 (by rfl) ⟨1370807, by rfl⟩ : syracuseStep 1827743 = 2741615) B2741615
theorem B1828031 : Blo 1217426 1828031 := bstep (se 1 (by rfl) ⟨1371023, by rfl⟩ : syracuseStep 1828031 = 2742047) B2742047
theorem B2925791 : Blo 1217426 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B1828175 : Blo 1217426 1828175 := bstep (se 1 (by rfl) ⟨1371131, by rfl⟩ : syracuseStep 1828175 = 2742263) B2742263
theorem B2311591 : Blo 1217426 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B1828265 : Blo 1217426 1828265 := bstep (se 2 (by rfl) ⟨685599, by rfl⟩ : syracuseStep 1828265 = 1371199) B1371199
theorem B1828415 : Blo 1217426 1828415 := bstep (se 1 (by rfl) ⟨1371311, by rfl⟩ : syracuseStep 1828415 = 2742623) B2742623
theorem B17573537 : Blo 1217426 17573537 := bstep (se 2 (by rfl) ⟨6590076, by rfl⟩ : syracuseStep 17573537 = 13180153) B13180153
theorem B5859155 : Blo 1217426 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B1828775 : Blo 1217426 1828775 := bstep (se 1 (by rfl) ⟨1371581, by rfl⟩ : syracuseStep 1828775 = 2743163) B2743163
theorem B1828895 : Blo 1217426 1828895 := bstep (se 1 (by rfl) ⟨1371671, by rfl⟩ : syracuseStep 1828895 = 2743343) B2743343
theorem B23734417 : Blo 1217426 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B3082495 : Blo 1217426 3082495 := bstep (se 1 (by rfl) ⟨2311871, by rfl⟩ : syracuseStep 3082495 = 4623743) B4623743
theorem B50014493 : Blo 1217426 50014493 := bstep (se 3 (by rfl) ⟨9377717, by rfl⟩ : syracuseStep 50014493 = 18755435) B18755435
theorem B7907651 : Blo 1217426 7907651 := bstep (se 1 (by rfl) ⟨5930738, by rfl⟩ : syracuseStep 7907651 = 11861477) B11861477
theorem B42174827 : Blo 1217426 42174827 := bstep (se 1 (by rfl) ⟨31631120, by rfl⟩ : syracuseStep 42174827 = 63262241) B63262241
theorem B13183357 : Blo 1217426 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B10987933 : Blo 1217426 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B3516947 : Blo 1217426 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B80063063 : Blo 1217426 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B2083583 : Blo 1217426 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B7908295 : Blo 1217426 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B6163451 : Blo 1217426 6163451 := bstep (se 1 (by rfl) ⟨4622588, by rfl⟩ : syracuseStep 6163451 = 9245177) B9245177
theorem B67652657 : Blo 1217426 67652657 := bstep (se 2 (by rfl) ⟨25369746, by rfl⟩ : syracuseStep 67652657 = 50739493) B50739493
theorem B2780335 : Blo 1217426 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B1371343 : Blo 1217426 1371343 := bstep (se 1 (by rfl) ⟨1028507, by rfl⟩ : syracuseStep 1371343 = 2057015) B2057015
theorem B3517651 : Blo 1217426 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B28536113 : Blo 1217426 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B2600275 : Blo 1217426 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B2313679 : Blo 1217426 2313679 := bstep (se 1 (by rfl) ⟨1735259, by rfl⟩ : syracuseStep 2313679 = 3470519) B3470519
theorem B2928097 : Blo 1217426 2928097 := bstep (se 2 (by rfl) ⟨1098036, by rfl⟩ : syracuseStep 2928097 = 2196073) B2196073
theorem B2313839 : Blo 1217426 2313839 := bstep (se 1 (by rfl) ⟨1735379, by rfl⟩ : syracuseStep 2313839 = 3470759) B3470759
theorem B2739959 : Blo 1217426 2739959 := bstep (se 1 (by rfl) ⟨2054969, by rfl⟩ : syracuseStep 2739959 = 4109939) B4109939
theorem B2739977 : Blo 1217426 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B2740031 : Blo 1217426 2740031 := bstep (se 1 (by rfl) ⟨2055023, by rfl⟩ : syracuseStep 2740031 = 4110047) B4110047
theorem B2740139 : Blo 1217426 2740139 := bstep (se 1 (by rfl) ⟨2055104, by rfl⟩ : syracuseStep 2740139 = 4110209) B4110209
theorem B8785847 : Blo 1217426 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B4509857 : Blo 1217426 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B3084551 : Blo 1217426 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B2740499 : Blo 1217426 2740499 := bstep (se 1 (by rfl) ⟨2055374, by rfl⟩ : syracuseStep 2740499 = 4110749) B4110749
theorem B1388827 : Blo 1217426 1388827 := bstep (se 1 (by rfl) ⟨1041620, by rfl⟩ : syracuseStep 1388827 = 2083241) B2083241
theorem B2314651 : Blo 1217426 2314651 := bstep (se 1 (by rfl) ⟨1735988, by rfl⟩ : syracuseStep 2314651 = 3471977) B3471977
theorem B2740679 : Blo 1217426 2740679 := bstep (se 1 (by rfl) ⟨2055509, by rfl⟩ : syracuseStep 2740679 = 4111019) B4111019
theorem B33346079 : Blo 1217426 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B13177565 : Blo 1217426 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B2740967 : Blo 1217426 2740967 := bstep (se 1 (by rfl) ⟨2055725, by rfl⟩ : syracuseStep 2740967 = 4111451) B4111451
theorem B2741039 : Blo 1217426 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B2741129 : Blo 1217426 2741129 := bstep (se 2 (by rfl) ⟨1027923, by rfl⟩ : syracuseStep 2741129 = 2055847) B2055847
theorem B4109291 : Blo 1217426 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B9253925 : Blo 1217426 9253925 := bstep (se 4 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 9253925 = 1735111) B1735111
theorem B5207111 : Blo 1217426 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B1217647 : Blo 1217426 1217647 := bstep (se 1 (by rfl) ⟨913235, by rfl⟩ : syracuseStep 1217647 = 1826471) B1826471
theorem B1217727 : Blo 1217426 1217727 := bstep (se 1 (by rfl) ⟨913295, by rfl⟩ : syracuseStep 1217727 = 1826591) B1826591
theorem B7410923 : Blo 1217426 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B7812409 : Blo 1217426 7812409 := bstep (se 2 (by rfl) ⟨2929653, by rfl⟩ : syracuseStep 7812409 = 5859307) B5859307
theorem B1218015 : Blo 1217426 1218015 := bstep (se 1 (by rfl) ⟨913511, by rfl⟩ : syracuseStep 1218015 = 1827023) B1827023
theorem B1218047 : Blo 1217426 1218047 := bstep (se 1 (by rfl) ⟨913535, by rfl⟩ : syracuseStep 1218047 = 1827071) B1827071
theorem B2602523 : Blo 1217426 2602523 := bstep (se 1 (by rfl) ⟨1951892, by rfl⟩ : syracuseStep 2602523 = 3903785) B3903785
theorem B7411409 : Blo 1217426 7411409 := bstep (se 2 (by rfl) ⟨2779278, by rfl⟩ : syracuseStep 7411409 = 5558557) B5558557
theorem B26367839 : Blo 1217426 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B1218591 : Blo 1217426 1218591 := bstep (se 1 (by rfl) ⟨913943, by rfl⟩ : syracuseStep 1218591 = 1827887) B1827887
theorem B5855273 : Blo 1217426 5855273 := bstep (se 2 (by rfl) ⟨2195727, by rfl⟩ : syracuseStep 5855273 = 4391455) B4391455
theorem B1218671 : Blo 1217426 1218671 := bstep (se 1 (by rfl) ⟨914003, by rfl⟩ : syracuseStep 1218671 = 1828007) B1828007
theorem B6936799 : Blo 1217426 6936799 := bstep (se 1 (by rfl) ⟨5202599, by rfl⟩ : syracuseStep 6936799 = 10405199) B10405199
theorem B1218919 : Blo 1217426 1218919 := bstep (se 1 (by rfl) ⟨914189, by rfl⟩ : syracuseStep 1218919 = 1828379) B1828379
theorem B31660607 : Blo 1217426 31660607 := bstep (se 1 (by rfl) ⟨23745455, by rfl⟩ : syracuseStep 31660607 = 47490911) B47490911
theorem B3471943 : Blo 1217426 3471943 := bstep (se 1 (by rfl) ⟨2603957, by rfl⟩ : syracuseStep 3471943 = 5207915) B5207915
theorem B1219175 : Blo 1217426 1219175 := bstep (se 1 (by rfl) ⟨914381, by rfl⟩ : syracuseStep 1219175 = 1828763) B1828763
theorem B1219199 : Blo 1217426 1219199 := bstep (se 1 (by rfl) ⟨914399, by rfl⟩ : syracuseStep 1219199 = 1828799) B1828799
theorem B14072491 : Blo 1217426 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B1219323 : Blo 1217426 1219323 := bstep (se 1 (by rfl) ⟨914492, by rfl⟩ : syracuseStep 1219323 = 1828985) B1828985
theorem B3906359 : Blo 1217426 3906359 := bstep (se 1 (by rfl) ⟨2929769, by rfl⟩ : syracuseStep 3906359 = 5859539) B5859539
theorem B3906461 : Blo 1217426 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B28146653 : Blo 1217426 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B4111343 : Blo 1217426 4111343 := bstep (se 1 (by rfl) ⟨3083507, by rfl⟩ : syracuseStep 4111343 = 6167015) B6167015
theorem B1826543 : Blo 1217426 1826543 := bstep (se 1 (by rfl) ⟨1369907, by rfl⟩ : syracuseStep 1826543 = 2739815) B2739815
theorem B4112207 : Blo 1217426 4112207 := bstep (se 1 (by rfl) ⟨3084155, by rfl⟩ : syracuseStep 4112207 = 6168311) B6168311
theorem B1826729 : Blo 1217426 1826729 := bstep (se 2 (by rfl) ⟨685023, by rfl⟩ : syracuseStep 1826729 = 1370047) B1370047
theorem B11108279 : Blo 1217426 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B3006571 : Blo 1217426 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B2056367 : Blo 1217426 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B1826999 : Blo 1217426 1826999 := bstep (se 1 (by rfl) ⟨1370249, by rfl⟩ : syracuseStep 1826999 = 2740499) B2740499
theorem B31645889 : Blo 1217426 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B4112639 : Blo 1217426 4112639 := bstep (se 1 (by rfl) ⟨3084479, by rfl⟩ : syracuseStep 4112639 = 6168959) B6168959
theorem B9249065 : Blo 1217426 9249065 := bstep (se 2 (by rfl) ⟨3468399, by rfl⟩ : syracuseStep 9249065 = 6936799) B6936799
theorem B1827119 : Blo 1217426 1827119 := bstep (se 1 (by rfl) ⟨1370339, by rfl⟩ : syracuseStep 1827119 = 2740679) B2740679
theorem B1851769 : Blo 1217426 1851769 := bstep (se 2 (by rfl) ⟨694413, by rfl⟩ : syracuseStep 1851769 = 1388827) B1388827
theorem B1827311 : Blo 1217426 1827311 := bstep (se 1 (by rfl) ⟨1370483, by rfl⟩ : syracuseStep 1827311 = 2740967) B2740967
theorem B1827359 : Blo 1217426 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B1827419 : Blo 1217426 1827419 := bstep (se 1 (by rfl) ⟨1370564, by rfl⟩ : syracuseStep 1827419 = 2741129) B2741129
theorem B6169283 : Blo 1217426 6169283 := bstep (se 1 (by rfl) ⟨4626962, by rfl⟩ : syracuseStep 6169283 = 9253925) B9253925
theorem B4629257 : Blo 1217426 4629257 := bstep (se 2 (by rfl) ⟨1735971, by rfl⟩ : syracuseStep 4629257 = 3471943) B3471943
theorem B1950527 : Blo 1217426 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B4940615 : Blo 1217426 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B18760805 : Blo 1217426 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B11715691 : Blo 1217426 11715691 := bstep (se 1 (by rfl) ⟨8786768, by rfl⟩ : syracuseStep 11715691 = 17573537) B17573537
theorem B4940939 : Blo 1217426 4940939 := bstep (se 1 (by rfl) ⟨3705704, by rfl⟩ : syracuseStep 4940939 = 7411409) B7411409
theorem B10544393 : Blo 1217426 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B33342995 : Blo 1217426 33342995 := bstep (se 1 (by rfl) ⟨25007246, by rfl⟩ : syracuseStep 33342995 = 50014493) B50014493
theorem B28116551 : Blo 1217426 28116551 := bstep (se 1 (by rfl) ⟨21087413, by rfl⟩ : syracuseStep 28116551 = 42174827) B42174827
theorem B1828457 : Blo 1217426 1828457 := bstep (se 2 (by rfl) ⟨685671, by rfl⟩ : syracuseStep 1828457 = 1371343) B1371343
theorem B2344631 : Blo 1217426 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B3467033 : Blo 1217426 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B3082121 : Blo 1217426 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B5556221 : Blo 1217426 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B19024075 : Blo 1217426 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B1542559 : Blo 1217426 1542559 := bstep (se 1 (by rfl) ⟨1156919, by rfl⟩ : syracuseStep 1542559 = 2313839) B2313839
theorem B6941447 : Blo 1217426 6941447 := bstep (se 1 (by rfl) ⟨5206085, by rfl⟩ : syracuseStep 6941447 = 10412171) B10412171
theorem B17558315 : Blo 1217426 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B8785043 : Blo 1217426 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B14650577 : Blo 1217426 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B2739527 : Blo 1217426 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B18763321 : Blo 1217426 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B3903515 : Blo 1217426 3903515 := bstep (se 1 (by rfl) ⟨2927636, by rfl⟩ : syracuseStep 3903515 = 5855273) B5855273
theorem B5271767 : Blo 1217426 5271767 := bstep (se 1 (by rfl) ⟨3953825, by rfl⟩ : syracuseStep 5271767 = 7907651) B7907651
theorem B3707113 : Blo 1217426 3707113 := bstep (se 2 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 3707113 = 2780335) B2780335
theorem B21107071 : Blo 1217426 21107071 := bstep (se 1 (by rfl) ⟨15830303, by rfl⟩ : syracuseStep 21107071 = 31660607) B31660607
theorem B53375375 : Blo 1217426 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B10416545 : Blo 1217426 10416545 := bstep (se 2 (by rfl) ⟨3906204, by rfl⟩ : syracuseStep 10416545 = 7812409) B7812409
theorem B3084905 : Blo 1217426 3084905 := bstep (se 2 (by rfl) ⟨1156839, by rfl⟩ : syracuseStep 3084905 = 2313679) B2313679
theorem B3904129 : Blo 1217426 3904129 := bstep (se 2 (by rfl) ⟨1464048, by rfl⟩ : syracuseStep 3904129 = 2928097) B2928097
theorem B18764435 : Blo 1217426 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B2740895 : Blo 1217426 2740895 := bstep (se 1 (by rfl) ⟨2055671, by rfl⟩ : syracuseStep 2740895 = 4111343) B4111343
theorem B4108967 : Blo 1217426 4108967 := bstep (se 1 (by rfl) ⟨3081725, by rfl⟩ : syracuseStep 4108967 = 6163451) B6163451
theorem B45101771 : Blo 1217426 45101771 := bstep (se 1 (by rfl) ⟨33826328, by rfl⟩ : syracuseStep 45101771 = 67652657) B67652657
theorem B1217695 : Blo 1217426 1217695 := bstep (se 1 (by rfl) ⟨913271, by rfl⟩ : syracuseStep 1217695 = 1826543) B1826543
theorem B2741471 : Blo 1217426 2741471 := bstep (se 1 (by rfl) ⟨2056103, by rfl⟩ : syracuseStep 2741471 = 4112207) B4112207
theorem B1217819 : Blo 1217426 1217819 := bstep (se 1 (by rfl) ⟨913364, by rfl⟩ : syracuseStep 1217819 = 1826729) B1826729
theorem B1217919 : Blo 1217426 1217919 := bstep (se 1 (by rfl) ⟨913439, by rfl⟩ : syracuseStep 1217919 = 1826879) B1826879
theorem B3085735 : Blo 1217426 3085735 := bstep (se 1 (by rfl) ⟨2314301, by rfl⟩ : syracuseStep 3085735 = 4628603) B4628603
theorem B1218075 : Blo 1217426 1218075 := bstep (se 1 (by rfl) ⟨913556, by rfl⟩ : syracuseStep 1218075 = 1827113) B1827113
theorem B4109993 : Blo 1217426 4109993 := bstep (se 2 (by rfl) ⟨1541247, by rfl⟩ : syracuseStep 4109993 = 3082495) B3082495
theorem B22230719 : Blo 1217426 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B1218255 : Blo 1217426 1218255 := bstep (se 1 (by rfl) ⟨913691, by rfl⟩ : syracuseStep 1218255 = 1827383) B1827383
theorem B17577809 : Blo 1217426 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B3086201 : Blo 1217426 3086201 := bstep (se 2 (by rfl) ⟨1157325, by rfl⟩ : syracuseStep 3086201 = 2314651) B2314651
theorem B1218495 : Blo 1217426 1218495 := bstep (se 1 (by rfl) ⟨913871, by rfl⟩ : syracuseStep 1218495 = 1827743) B1827743
theorem B3471407 : Blo 1217426 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B1218687 : Blo 1217426 1218687 := bstep (se 1 (by rfl) ⟨914015, by rfl⟩ : syracuseStep 1218687 = 1828031) B1828031
theorem B1218783 : Blo 1217426 1218783 := bstep (se 1 (by rfl) ⟨914087, by rfl⟩ : syracuseStep 1218783 = 1828175) B1828175
theorem B1218843 : Blo 1217426 1218843 := bstep (se 1 (by rfl) ⟨914132, by rfl⟩ : syracuseStep 1218843 = 1828265) B1828265
theorem B1735015 : Blo 1217426 1735015 := bstep (se 1 (by rfl) ⟨1301261, by rfl⟩ : syracuseStep 1735015 = 2602523) B2602523
theorem B1218943 : Blo 1217426 1218943 := bstep (se 1 (by rfl) ⟨914207, by rfl⟩ : syracuseStep 1218943 = 1828415) B1828415
theorem B3906103 : Blo 1217426 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B17578559 : Blo 1217426 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B1219183 : Blo 1217426 1219183 := bstep (se 1 (by rfl) ⟨914387, by rfl⟩ : syracuseStep 1219183 = 1828775) B1828775
theorem B1219263 : Blo 1217426 1219263 := bstep (se 1 (by rfl) ⟨914447, by rfl⟩ : syracuseStep 1219263 = 1828895) B1828895
theorem B2604239 : Blo 1217426 2604239 := bstep (se 1 (by rfl) ⟨1953179, by rfl⟩ : syracuseStep 2604239 = 3906359) B3906359
theorem B2604307 : Blo 1217426 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B1826639 : Blo 1217426 1826639 := bstep (se 1 (by rfl) ⟨1369979, by rfl⟩ : syracuseStep 1826639 = 2739959) B2739959
theorem B1826651 : Blo 1217426 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B1826687 : Blo 1217426 1826687 := bstep (se 1 (by rfl) ⟨1370015, by rfl⟩ : syracuseStep 1826687 = 2740031) B2740031
theorem B1826759 : Blo 1217426 1826759 := bstep (se 1 (by rfl) ⟨1370069, by rfl⟩ : syracuseStep 1826759 = 2740139) B2740139
theorem B7405519 : Blo 1217426 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B5857231 : Blo 1217426 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B3514511 : Blo 1217426 3514511 := bstep (se 1 (by rfl) ⟨2635883, by rfl⟩ : syracuseStep 3514511 = 5271767) B5271767
theorem B2056603 : Blo 1217426 2056603 := bstep (se 1 (by rfl) ⟨1542452, by rfl⟩ : syracuseStep 2056603 = 3084905) B3084905
theorem B12509623 : Blo 1217426 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B1827263 : Blo 1217426 1827263 := bstep (se 1 (by rfl) ⟨1370447, by rfl⟩ : syracuseStep 1827263 = 2740895) B2740895
theorem B4112855 : Blo 1217426 4112855 := bstep (se 1 (by rfl) ⟨3084641, by rfl⟩ : syracuseStep 4112855 = 6169283) B6169283
theorem B2056745 : Blo 1217426 2056745 := bstep (se 2 (by rfl) ⟨771279, by rfl⟩ : syracuseStep 2056745 = 1542559) B1542559
theorem B3293743 : Blo 1217426 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B3293959 : Blo 1217426 3293959 := bstep (se 1 (by rfl) ⟨2470469, by rfl⟩ : syracuseStep 3293959 = 4940939) B4940939
theorem B1827647 : Blo 1217426 1827647 := bstep (se 1 (by rfl) ⟨1370735, by rfl⟩ : syracuseStep 1827647 = 2741471) B2741471
theorem B7029595 : Blo 1217426 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B18744367 : Blo 1217426 18744367 := bstep (se 1 (by rfl) ⟨14058275, by rfl⟩ : syracuseStep 18744367 = 28116551) B28116551
theorem B14820479 : Blo 1217426 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B2311355 : Blo 1217426 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B2057467 : Blo 1217426 2057467 := bstep (se 1 (by rfl) ⟨1543100, by rfl⟩ : syracuseStep 2057467 = 3086201) B3086201
theorem B3704147 : Blo 1217426 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B6252349 : Blo 1217426 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B4114313 : Blo 1217426 4114313 := bstep (se 2 (by rfl) ⟨1542867, by rfl⟩ : syracuseStep 4114313 = 3085735) B3085735
theorem B9767051 : Blo 1217426 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B9874025 : Blo 1217426 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B7809641 : Blo 1217426 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B1370911 : Blo 1217426 1370911 := bstep (se 1 (by rfl) ⟨1028183, by rfl⟩ : syracuseStep 1370911 = 2056367) B2056367
theorem B21097259 : Blo 1217426 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B4008761 : Blo 1217426 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B4942817 : Blo 1217426 4942817 := bstep (se 2 (by rfl) ⟨1853556, by rfl⟩ : syracuseStep 4942817 = 3707113) B3707113
theorem B2739311 : Blo 1217426 2739311 := bstep (se 1 (by rfl) ⟨2054483, by rfl⟩ : syracuseStep 2739311 = 4108967) B4108967
theorem B30067847 : Blo 1217426 30067847 := bstep (se 1 (by rfl) ⟨22550885, by rfl⟩ : syracuseStep 30067847 = 45101771) B45101771
theorem B2313353 : Blo 1217426 2313353 := bstep (se 2 (by rfl) ⟨867507, by rfl⟩ : syracuseStep 2313353 = 1735015) B1735015
theorem B2469025 : Blo 1217426 2469025 := bstep (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) B1851769
theorem B28142761 : Blo 1217426 28142761 := bstep (se 2 (by rfl) ⟨10553535, by rfl⟩ : syracuseStep 28142761 = 21107071) B21107071
theorem B5205505 : Blo 1217426 5205505 := bstep (se 2 (by rfl) ⟨1952064, by rfl⟩ : syracuseStep 5205505 = 3904129) B3904129
theorem B22228663 : Blo 1217426 22228663 := bstep (se 1 (by rfl) ⟨16671497, by rfl⟩ : syracuseStep 22228663 = 33342995) B33342995
theorem B101461733 : Blo 1217426 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B2739995 : Blo 1217426 2739995 := bstep (se 1 (by rfl) ⟨2054996, by rfl⟩ : syracuseStep 2739995 = 4109993) B4109993
theorem B11718539 : Blo 1217426 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B2314271 : Blo 1217426 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B11719039 : Blo 1217426 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B1217759 : Blo 1217426 1217759 := bstep (se 1 (by rfl) ⟨913319, by rfl⟩ : syracuseStep 1217759 = 1826639) B1826639
theorem B1217767 : Blo 1217426 1217767 := bstep (se 1 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 1217767 = 1826651) B1826651
theorem B1217791 : Blo 1217426 1217791 := bstep (se 1 (by rfl) ⟨913343, by rfl⟩ : syracuseStep 1217791 = 1826687) B1826687
theorem B1217839 : Blo 1217426 1217839 := bstep (se 1 (by rfl) ⟨913379, by rfl⟩ : syracuseStep 1217839 = 1826759) B1826759
theorem B2602343 : Blo 1217426 2602343 := bstep (se 1 (by rfl) ⟨1951757, by rfl⟩ : syracuseStep 2602343 = 3903515) B3903515
theorem B1217999 : Blo 1217426 1217999 := bstep (se 1 (by rfl) ⟨913499, by rfl⟩ : syracuseStep 1217999 = 1826999) B1826999
theorem B2741759 : Blo 1217426 2741759 := bstep (se 1 (by rfl) ⟨2056319, by rfl⟩ : syracuseStep 2741759 = 4112639) B4112639
theorem B6166043 : Blo 1217426 6166043 := bstep (se 1 (by rfl) ⟨4624532, by rfl⟩ : syracuseStep 6166043 = 9249065) B9249065
theorem B1218079 : Blo 1217426 1218079 := bstep (se 1 (by rfl) ⟨913559, by rfl⟩ : syracuseStep 1218079 = 1827119) B1827119
theorem B35583583 : Blo 1217426 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B6944363 : Blo 1217426 6944363 := bstep (se 1 (by rfl) ⟨5208272, by rfl⟩ : syracuseStep 6944363 = 10416545) B10416545
theorem B1218207 : Blo 1217426 1218207 := bstep (se 1 (by rfl) ⟨913655, by rfl⟩ : syracuseStep 1218207 = 1827311) B1827311
theorem B1218239 : Blo 1217426 1218239 := bstep (se 1 (by rfl) ⟨913679, by rfl⟩ : syracuseStep 1218239 = 1827359) B1827359
theorem B1218279 : Blo 1217426 1218279 := bstep (se 1 (by rfl) ⟨913709, by rfl⟩ : syracuseStep 1218279 = 1827419) B1827419
theorem B3086171 : Blo 1217426 3086171 := bstep (se 1 (by rfl) ⟨2314628, by rfl⟩ : syracuseStep 3086171 = 4629257) B4629257
theorem B12507203 : Blo 1217426 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B5208137 : Blo 1217426 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B1218971 : Blo 1217426 1218971 := bstep (se 1 (by rfl) ⟨914228, by rfl⟩ : syracuseStep 1218971 = 1828457) B1828457
theorem B2054747 : Blo 1217426 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B15620921 : Blo 1217426 15620921 := bstep (se 2 (by rfl) ⟨5857845, by rfl⟩ : syracuseStep 15620921 = 11715691) B11715691
theorem B3472409 : Blo 1217426 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B4627631 : Blo 1217426 4627631 := bstep (se 1 (by rfl) ⟨3470723, by rfl⟩ : syracuseStep 4627631 = 6941447) B6941447
theorem B11705543 : Blo 1217426 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B25017761 : Blo 1217426 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B5856695 : Blo 1217426 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B1736159 : Blo 1217426 1736159 := bstep (se 1 (by rfl) ⟨1302119, by rfl⟩ : syracuseStep 1736159 = 2604239) B2604239
theorem B5201405 : Blo 1217426 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B1826351 : Blo 1217426 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B2343007 : Blo 1217426 2343007 := bstep (se 1 (by rfl) ⟨1757255, by rfl⟩ : syracuseStep 2343007 = 3514511) B3514511
theorem B4391657 : Blo 1217426 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B9880319 : Blo 1217426 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B1827839 : Blo 1217426 1827839 := bstep (se 1 (by rfl) ⟨1370879, by rfl⟩ : syracuseStep 1827839 = 2741759) B2741759
theorem B4391945 : Blo 1217426 4391945 := bstep (se 2 (by rfl) ⟨1646979, by rfl⟩ : syracuseStep 4391945 = 3293959) B3293959
theorem B1827881 : Blo 1217426 1827881 := bstep (se 2 (by rfl) ⟨685455, by rfl⟩ : syracuseStep 1827881 = 1370911) B1370911
theorem B4629575 : Blo 1217426 4629575 := bstep (se 1 (by rfl) ⟨3472181, by rfl⟩ : syracuseStep 4629575 = 6944363) B6944363
theorem B2057447 : Blo 1217426 2057447 := bstep (se 1 (by rfl) ⟨1543085, by rfl⟩ : syracuseStep 2057447 = 3086171) B3086171
theorem B4629757 : Blo 1217426 4629757 := bstep (se 3 (by rfl) ⟨868079, by rfl⟩ : syracuseStep 4629757 = 1736159) B1736159
theorem B1369831 : Blo 1217426 1369831 := bstep (se 1 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 1369831 = 2054747) B2054747
theorem B2672507 : Blo 1217426 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B10413947 : Blo 1217426 10413947 := bstep (se 1 (by rfl) ⟨7810460, by rfl⟩ : syracuseStep 10413947 = 15620921) B15620921
theorem B3295211 : Blo 1217426 3295211 := bstep (se 1 (by rfl) ⟨2471408, by rfl⟩ : syracuseStep 3295211 = 4942817) B4942817
theorem B6940673 : Blo 1217426 6940673 := bstep (se 2 (by rfl) ⟨2602752, by rfl⟩ : syracuseStep 6940673 = 5205505) B5205505
theorem B1542235 : Blo 1217426 1542235 := bstep (se 1 (by rfl) ⟨1156676, by rfl⟩ : syracuseStep 1542235 = 2313353) B2313353
theorem B66717989 : Blo 1217426 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B3467603 : Blo 1217426 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B9259757 : Blo 1217426 9259757 := bstep (se 3 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 9259757 = 3472409) B3472409
theorem B6171389 : Blo 1217426 6171389 := bstep (se 3 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 6171389 = 2314271) B2314271
theorem B1371163 : Blo 1217426 1371163 := bstep (se 1 (by rfl) ⟨1028372, by rfl⟩ : syracuseStep 1371163 = 2056745) B2056745
theorem B6163613 : Blo 1217426 6163613 := bstep (se 3 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 6163613 = 2311355) B2311355
theorem B15625385 : Blo 1217426 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B13168133 : Blo 1217426 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B2469431 : Blo 1217426 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B37523681 : Blo 1217426 37523681 := bstep (se 2 (by rfl) ⟨14071380, by rfl⟩ : syracuseStep 37523681 = 28142761) B28142761
theorem B6582683 : Blo 1217426 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B5206427 : Blo 1217426 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B37491173 : Blo 1217426 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B3085087 : Blo 1217426 3085087 := bstep (se 1 (by rfl) ⟨2313815, by rfl⟩ : syracuseStep 3085087 = 4627631) B4627631
theorem B47444777 : Blo 1217426 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B7803695 : Blo 1217426 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B3904463 : Blo 1217426 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1217567 : Blo 1217426 1217567 := bstep (se 1 (by rfl) ⟨913175, by rfl⟩ : syracuseStep 1217567 = 1826351) B1826351
theorem B8336465 : Blo 1217426 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B7812359 : Blo 1217426 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B1218175 : Blo 1217426 1218175 := bstep (se 1 (by rfl) ⟨913631, by rfl⟩ : syracuseStep 1218175 = 1827263) B1827263
theorem B2741903 : Blo 1217426 2741903 := bstep (se 1 (by rfl) ⟨2056427, by rfl⟩ : syracuseStep 2741903 = 4112855) B4112855
theorem B2742137 : Blo 1217426 2742137 := bstep (se 2 (by rfl) ⟨1028301, by rfl⟩ : syracuseStep 2742137 = 2056603) B2056603
theorem B1218431 : Blo 1217426 1218431 := bstep (se 1 (by rfl) ⟨913823, by rfl⟩ : syracuseStep 1218431 = 1827647) B1827647
theorem B1734895 : Blo 1217426 1734895 := bstep (se 1 (by rfl) ⟨1301171, by rfl⟩ : syracuseStep 1734895 = 2602343) B2602343
theorem B4110695 : Blo 1217426 4110695 := bstep (se 1 (by rfl) ⟨3083021, by rfl⟩ : syracuseStep 4110695 = 6166043) B6166043
theorem B2742875 : Blo 1217426 2742875 := bstep (se 1 (by rfl) ⟨2057156, by rfl⟩ : syracuseStep 2742875 = 4114313) B4114313
theorem B8338135 : Blo 1217426 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B3472091 : Blo 1217426 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B24992489 : Blo 1217426 24992489 := bstep (se 2 (by rfl) ⟨9372183, by rfl⟩ : syracuseStep 24992489 = 18744367) B18744367
theorem B6511367 : Blo 1217426 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B2743289 : Blo 1217426 2743289 := bstep (se 2 (by rfl) ⟨1028733, by rfl⟩ : syracuseStep 2743289 = 2057467) B2057467
theorem B14064839 : Blo 1217426 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B1826207 : Blo 1217426 1826207 := bstep (se 1 (by rfl) ⟨1369655, by rfl⟩ : syracuseStep 1826207 = 2739311) B2739311
theorem B20045231 : Blo 1217426 20045231 := bstep (se 1 (by rfl) ⟨15033923, by rfl⟩ : syracuseStep 20045231 = 30067847) B30067847
theorem B29638217 : Blo 1217426 29638217 := bstep (se 2 (by rfl) ⟨11114331, by rfl⟩ : syracuseStep 29638217 = 22228663) B22228663
theorem B16678507 : Blo 1217426 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B67641155 : Blo 1217426 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B1826663 : Blo 1217426 1826663 := bstep (se 1 (by rfl) ⟨1369997, by rfl⟩ : syracuseStep 1826663 = 2739995) B2739995
theorem B2056313 : Blo 1217426 2056313 := bstep (se 2 (by rfl) ⟨771117, by rfl⟩ : syracuseStep 2056313 = 1542235) B1542235
theorem B24994115 : Blo 1217426 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B6586879 : Blo 1217426 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B31629851 : Blo 1217426 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B5202463 : Blo 1217426 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B11117513 : Blo 1217426 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B4113449 : Blo 1217426 4113449 := bstep (se 2 (by rfl) ⟨1542543, by rfl⟩ : syracuseStep 4113449 = 3085087) B3085087
theorem B1827935 : Blo 1217426 1827935 := bstep (se 1 (by rfl) ⟨1370951, by rfl⟩ : syracuseStep 1827935 = 2741903) B2741903
theorem B1828091 : Blo 1217426 1828091 := bstep (se 1 (by rfl) ⟨1371068, by rfl⟩ : syracuseStep 1828091 = 2742137) B2742137
theorem B1828217 : Blo 1217426 1828217 := bstep (se 2 (by rfl) ⟨685581, by rfl⟩ : syracuseStep 1828217 = 1371163) B1371163
theorem B2311735 : Blo 1217426 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B1828583 : Blo 1217426 1828583 := bstep (se 1 (by rfl) ⟨1371437, by rfl⟩ : syracuseStep 1828583 = 2742875) B2742875
theorem B4114259 : Blo 1217426 4114259 := bstep (se 1 (by rfl) ⟨3085694, by rfl⟩ : syracuseStep 4114259 = 6171389) B6171389
theorem B1828859 : Blo 1217426 1828859 := bstep (se 1 (by rfl) ⟨1371644, by rfl⟩ : syracuseStep 1828859 = 2743289) B2743289
theorem B13363487 : Blo 1217426 13363487 := bstep (se 1 (by rfl) ⟨10022615, by rfl⟩ : syracuseStep 13363487 = 20045231) B20045231
theorem B3124009 : Blo 1217426 3124009 := bstep (se 2 (by rfl) ⟨1171503, by rfl⟩ : syracuseStep 3124009 = 2343007) B2343007
theorem B2313193 : Blo 1217426 2313193 := bstep (se 2 (by rfl) ⟨867447, by rfl⟩ : syracuseStep 2313193 = 1734895) B1734895
theorem B2927771 : Blo 1217426 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B2927963 : Blo 1217426 2927963 := bstep (se 1 (by rfl) ⟨2195972, by rfl⟩ : syracuseStep 2927963 = 4391945) B4391945
theorem B5557643 : Blo 1217426 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B1371631 : Blo 1217426 1371631 := bstep (se 1 (by rfl) ⟨1028723, by rfl⟩ : syracuseStep 1371631 = 2057447) B2057447
theorem B1781671 : Blo 1217426 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B6942631 : Blo 1217426 6942631 := bstep (se 1 (by rfl) ⟨5206973, by rfl⟩ : syracuseStep 6942631 = 10413947) B10413947
theorem B44478659 : Blo 1217426 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B2740463 : Blo 1217426 2740463 := bstep (se 1 (by rfl) ⟨2055347, by rfl⟩ : syracuseStep 2740463 = 4110695) B4110695
theorem B6173009 : Blo 1217426 6173009 := bstep (se 2 (by rfl) ⟨2314878, by rfl⟩ : syracuseStep 6173009 = 4629757) B4629757
theorem B2314727 : Blo 1217426 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B6173171 : Blo 1217426 6173171 := bstep (se 1 (by rfl) ⟨4629878, by rfl⟩ : syracuseStep 6173171 = 9259757) B9259757
theorem B4109075 : Blo 1217426 4109075 := bstep (se 1 (by rfl) ⟨3081806, by rfl⟩ : syracuseStep 4109075 = 6163613) B6163613
theorem B10416923 : Blo 1217426 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B9376559 : Blo 1217426 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B22238009 : Blo 1217426 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B1217471 : Blo 1217426 1217471 := bstep (se 1 (by rfl) ⟨913103, by rfl⟩ : syracuseStep 1217471 = 1826207) B1826207
theorem B8778755 : Blo 1217426 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B35148917 : Blo 1217426 35148917 := bstep (se 5 (by rfl) ⟨1647605, by rfl⟩ : syracuseStep 35148917 = 3295211) B3295211
theorem B45094103 : Blo 1217426 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B1217775 : Blo 1217426 1217775 := bstep (se 1 (by rfl) ⟨913331, by rfl⟩ : syracuseStep 1217775 = 1826663) B1826663
theorem B25015787 : Blo 1217426 25015787 := bstep (se 1 (by rfl) ⟨18761840, by rfl⟩ : syracuseStep 25015787 = 37523681) B37523681
theorem B4388455 : Blo 1217426 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B3470951 : Blo 1217426 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B2602975 : Blo 1217426 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B1218559 : Blo 1217426 1218559 := bstep (se 1 (by rfl) ⟨913919, by rfl⟩ : syracuseStep 1218559 = 1827839) B1827839
theorem B1218587 : Blo 1217426 1218587 := bstep (se 1 (by rfl) ⟨913940, by rfl⟩ : syracuseStep 1218587 = 1827881) B1827881
theorem B3086383 : Blo 1217426 3086383 := bstep (se 1 (by rfl) ⟨2314787, by rfl⟩ : syracuseStep 3086383 = 4629575) B4629575
theorem B5208239 : Blo 1217426 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B4627115 : Blo 1217426 4627115 := bstep (se 1 (by rfl) ⟨3470336, by rfl⟩ : syracuseStep 4627115 = 6940673) B6940673
theorem B16661659 : Blo 1217426 16661659 := bstep (se 1 (by rfl) ⟨12496244, by rfl⟩ : syracuseStep 16661659 = 24992489) B24992489
theorem B4340911 : Blo 1217426 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B1826441 : Blo 1217426 1826441 := bstep (se 2 (by rfl) ⟨684915, by rfl⟩ : syracuseStep 1826441 = 1369831) B1369831
theorem B1646287 : Blo 1217426 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B19758811 : Blo 1217426 19758811 := bstep (se 1 (by rfl) ⟨14819108, by rfl⟩ : syracuseStep 19758811 = 29638217) B29638217
theorem B1826975 : Blo 1217426 1826975 := bstep (se 1 (by rfl) ⟨1370231, by rfl⟩ : syracuseStep 1826975 = 2740463) B2740463
theorem B16662743 : Blo 1217426 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B21086567 : Blo 1217426 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B6251039 : Blo 1217426 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B8782505 : Blo 1217426 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B1828841 : Blo 1217426 1828841 := bstep (se 2 (by rfl) ⟨685815, by rfl⟩ : syracuseStep 1828841 = 1371631) B1371631
theorem B3082313 : Blo 1217426 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B1951847 : Blo 1217426 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B5851273 : Blo 1217426 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B1951975 : Blo 1217426 1951975 := bstep (se 1 (by rfl) ⟨1463981, by rfl⟩ : syracuseStep 1951975 = 2927963) B2927963
theorem B3705095 : Blo 1217426 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B4115177 : Blo 1217426 4115177 := bstep (se 2 (by rfl) ⟨1543191, by rfl⟩ : syracuseStep 4115177 = 3086383) B3086383
theorem B1370875 : Blo 1217426 1370875 := bstep (se 1 (by rfl) ⟨1028156, by rfl⟩ : syracuseStep 1370875 = 2056313) B2056313
theorem B4115339 : Blo 1217426 4115339 := bstep (se 1 (by rfl) ⟨3086504, by rfl⟩ : syracuseStep 4115339 = 6173009) B6173009
theorem B1543151 : Blo 1217426 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B4115447 : Blo 1217426 4115447 := bstep (se 1 (by rfl) ⟨3086585, by rfl⟩ : syracuseStep 4115447 = 6173171) B6173171
theorem B2739383 : Blo 1217426 2739383 := bstep (se 1 (by rfl) ⟨2054537, by rfl⟩ : syracuseStep 2739383 = 4109075) B4109075
theorem B5852503 : Blo 1217426 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B23432611 : Blo 1217426 23432611 := bstep (se 1 (by rfl) ⟨17574458, by rfl⟩ : syracuseStep 23432611 = 35148917) B35148917
theorem B4165345 : Blo 1217426 4165345 := bstep (se 2 (by rfl) ⟨1562004, by rfl⟩ : syracuseStep 4165345 = 3124009) B3124009
theorem B3084257 : Blo 1217426 3084257 := bstep (se 2 (by rfl) ⟨1156596, by rfl⟩ : syracuseStep 3084257 = 2313193) B2313193
theorem B8908991 : Blo 1217426 8908991 := bstep (se 1 (by rfl) ⟨6681743, by rfl⟩ : syracuseStep 8908991 = 13363487) B13363487
theorem B5787881 : Blo 1217426 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B3084743 : Blo 1217426 3084743 := bstep (se 1 (by rfl) ⟨2313557, by rfl⟩ : syracuseStep 3084743 = 4627115) B4627115
theorem B1217627 : Blo 1217426 1217627 := bstep (se 1 (by rfl) ⟨913220, by rfl⟩ : syracuseStep 1217627 = 1826441) B1826441
theorem B3470633 : Blo 1217426 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B29652439 : Blo 1217426 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B6944615 : Blo 1217426 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B14825339 : Blo 1217426 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B7411675 : Blo 1217426 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B2742299 : Blo 1217426 2742299 := bstep (se 1 (by rfl) ⟨2056724, by rfl⟩ : syracuseStep 2742299 = 4113449) B4113449
theorem B6936617 : Blo 1217426 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B1218623 : Blo 1217426 1218623 := bstep (se 1 (by rfl) ⟨913967, by rfl⟩ : syracuseStep 1218623 = 1827935) B1827935
theorem B30062735 : Blo 1217426 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B1218727 : Blo 1217426 1218727 := bstep (se 1 (by rfl) ⟨914045, by rfl⟩ : syracuseStep 1218727 = 1828091) B1828091
theorem B1218811 : Blo 1217426 1218811 := bstep (se 1 (by rfl) ⟨914108, by rfl⟩ : syracuseStep 1218811 = 1828217) B1828217
theorem B16677191 : Blo 1217426 16677191 := bstep (se 1 (by rfl) ⟨12507893, by rfl⟩ : syracuseStep 16677191 = 25015787) B25015787
theorem B8780197 : Blo 1217426 8780197 := bstep (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) B1646287
theorem B1219055 : Blo 1217426 1219055 := bstep (se 1 (by rfl) ⟨914291, by rfl⟩ : syracuseStep 1219055 = 1828583) B1828583
theorem B2742839 : Blo 1217426 2742839 := bstep (se 1 (by rfl) ⟨2057129, by rfl⟩ : syracuseStep 2742839 = 4114259) B4114259
theorem B1219239 : Blo 1217426 1219239 := bstep (se 1 (by rfl) ⟨914429, by rfl⟩ : syracuseStep 1219239 = 1828859) B1828859
theorem B3472159 : Blo 1217426 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B22215545 : Blo 1217426 22215545 := bstep (se 2 (by rfl) ⟨8330829, by rfl⟩ : syracuseStep 22215545 = 16661659) B16661659
theorem B9255869 : Blo 1217426 9255869 := bstep (se 3 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 9255869 = 3470951) B3470951
theorem B26345081 : Blo 1217426 26345081 := bstep (se 2 (by rfl) ⟨9879405, by rfl⟩ : syracuseStep 26345081 = 19758811) B19758811
theorem B2375561 : Blo 1217426 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B9256841 : Blo 1217426 9256841 := bstep (se 2 (by rfl) ⟨3471315, by rfl⟩ : syracuseStep 9256841 = 6942631) B6942631
theorem B5939327 : Blo 1217426 5939327 := bstep (se 1 (by rfl) ⟨4454495, by rfl⟩ : syracuseStep 5939327 = 8908991) B8908991
theorem B11108495 : Blo 1217426 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B3858587 : Blo 1217426 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B14057711 : Blo 1217426 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B2056495 : Blo 1217426 2056495 := bstep (se 1 (by rfl) ⟨1542371, by rfl⟩ : syracuseStep 2056495 = 3084743) B3084743
theorem B11706929 : Blo 1217426 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B1827833 : Blo 1217426 1827833 := bstep (se 2 (by rfl) ⟨685437, by rfl⟩ : syracuseStep 1827833 = 1370875) B1370875
theorem B4629545 : Blo 1217426 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B4629743 : Blo 1217426 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B1828199 : Blo 1217426 1828199 := bstep (se 1 (by rfl) ⟨1371149, by rfl⟩ : syracuseStep 1828199 = 2742299) B2742299
theorem B1828559 : Blo 1217426 1828559 := bstep (se 1 (by rfl) ⟨1371419, by rfl⟩ : syracuseStep 1828559 = 2742839) B2742839
theorem B39536585 : Blo 1217426 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B6170579 : Blo 1217426 6170579 := bstep (se 1 (by rfl) ⟨4627934, by rfl⟩ : syracuseStep 6170579 = 9255869) B9255869
theorem B1583707 : Blo 1217426 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B6171227 : Blo 1217426 6171227 := bstep (se 1 (by rfl) ⟨4628420, by rfl⟩ : syracuseStep 6171227 = 9256841) B9256841
theorem B9882233 : Blo 1217426 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B4115069 : Blo 1217426 4115069 := bstep (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) B1543151
theorem B7801697 : Blo 1217426 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B2313755 : Blo 1217426 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B9883559 : Blo 1217426 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B4624411 : Blo 1217426 4624411 := bstep (se 1 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 4624411 = 6936617) B6936617
theorem B20041823 : Blo 1217426 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B2470063 : Blo 1217426 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B7803337 : Blo 1217426 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B1217983 : Blo 1217426 1217983 := bstep (se 1 (by rfl) ⟨913487, by rfl⟩ : syracuseStep 1217983 = 1826975) B1826975
theorem B2602633 : Blo 1217426 2602633 := bstep (se 2 (by rfl) ⟨975987, by rfl⟩ : syracuseStep 2602633 = 1951975) B1951975
theorem B4167359 : Blo 1217426 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B5855003 : Blo 1217426 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B44472509 : Blo 1217426 44472509 := bstep (se 3 (by rfl) ⟨8338595, by rfl⟩ : syracuseStep 44472509 = 16677191) B16677191
theorem B1219227 : Blo 1217426 1219227 := bstep (se 1 (by rfl) ⟨914420, by rfl⟩ : syracuseStep 1219227 = 1828841) B1828841
theorem B2054875 : Blo 1217426 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B1301231 : Blo 1217426 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B2743451 : Blo 1217426 2743451 := bstep (se 1 (by rfl) ⟨2057588, by rfl⟩ : syracuseStep 2743451 = 4115177) B4115177
theorem B31243481 : Blo 1217426 31243481 := bstep (se 2 (by rfl) ⟨11716305, by rfl⟩ : syracuseStep 31243481 = 23432611) B23432611
theorem B14810363 : Blo 1217426 14810363 := bstep (se 1 (by rfl) ⟨11107772, by rfl⟩ : syracuseStep 14810363 = 22215545) B22215545
theorem B2743559 : Blo 1217426 2743559 := bstep (se 1 (by rfl) ⟨2057669, by rfl⟩ : syracuseStep 2743559 = 4115339) B4115339
theorem B2743631 : Blo 1217426 2743631 := bstep (se 1 (by rfl) ⟨2057723, by rfl⟩ : syracuseStep 2743631 = 4115447) B4115447
theorem B1826255 : Blo 1217426 1826255 := bstep (se 1 (by rfl) ⟨1369691, by rfl⟩ : syracuseStep 1826255 = 2739383) B2739383
theorem B5553793 : Blo 1217426 5553793 := bstep (se 2 (by rfl) ⟨2082672, by rfl⟩ : syracuseStep 5553793 = 4165345) B4165345
theorem B17563387 : Blo 1217426 17563387 := bstep (se 1 (by rfl) ⟨13172540, by rfl⟩ : syracuseStep 17563387 = 26345081) B26345081
theorem B2056171 : Blo 1217426 2056171 := bstep (se 1 (by rfl) ⟨1542128, by rfl⟩ : syracuseStep 2056171 = 3084257) B3084257
theorem B13361215 : Blo 1217426 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B7405663 : Blo 1217426 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B2572391 : Blo 1217426 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B9371807 : Blo 1217426 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B3293417 : Blo 1217426 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B10404449 : Blo 1217426 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B2778239 : Blo 1217426 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B4113719 : Blo 1217426 4113719 := bstep (se 1 (by rfl) ⟨3085289, by rfl⟩ : syracuseStep 4113719 = 6170579) B6170579
theorem B29648339 : Blo 1217426 29648339 := bstep (se 1 (by rfl) ⟨22236254, by rfl⟩ : syracuseStep 29648339 = 44472509) B44472509
theorem B4114151 : Blo 1217426 4114151 := bstep (se 1 (by rfl) ⟨3085613, by rfl⟩ : syracuseStep 4114151 = 6171227) B6171227
theorem B6588155 : Blo 1217426 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B1828967 : Blo 1217426 1828967 := bstep (se 1 (by rfl) ⟨1371725, by rfl⟩ : syracuseStep 1828967 = 2743451) B2743451
theorem B9873575 : Blo 1217426 9873575 := bstep (se 1 (by rfl) ⟨7405181, by rfl⟩ : syracuseStep 9873575 = 14810363) B14810363
theorem B1829039 : Blo 1217426 1829039 := bstep (se 1 (by rfl) ⟨1371779, by rfl⟩ : syracuseStep 1829039 = 2743559) B2743559
theorem B1829087 : Blo 1217426 1829087 := bstep (se 1 (by rfl) ⟨1371815, by rfl⟩ : syracuseStep 1829087 = 2743631) B2743631
theorem B1542503 : Blo 1217426 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B6589039 : Blo 1217426 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B3959551 : Blo 1217426 3959551 := bstep (se 1 (by rfl) ⟨2969663, by rfl⟩ : syracuseStep 3959551 = 5939327) B5939327
theorem B2739833 : Blo 1217426 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B3903335 : Blo 1217426 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B26357723 : Blo 1217426 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B3469949 : Blo 1217426 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B20828987 : Blo 1217426 20828987 := bstep (se 1 (by rfl) ⟨15621740, by rfl⟩ : syracuseStep 20828987 = 31243481) B31243481
theorem B3470177 : Blo 1217426 3470177 := bstep (se 2 (by rfl) ⟨1301316, by rfl⟩ : syracuseStep 3470177 = 2602633) B2602633
theorem B1217503 : Blo 1217426 1217503 := bstep (se 1 (by rfl) ⟨913127, by rfl⟩ : syracuseStep 1217503 = 1826255) B1826255
theorem B23417849 : Blo 1217426 23417849 := bstep (se 2 (by rfl) ⟨8781693, by rfl⟩ : syracuseStep 23417849 = 17563387) B17563387
theorem B2741561 : Blo 1217426 2741561 := bstep (se 2 (by rfl) ⟨1028085, by rfl⟩ : syracuseStep 2741561 = 2056171) B2056171
theorem B6165881 : Blo 1217426 6165881 := bstep (se 2 (by rfl) ⟨2312205, by rfl⟩ : syracuseStep 6165881 = 4624411) B4624411
theorem B7804619 : Blo 1217426 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B2741993 : Blo 1217426 2741993 := bstep (se 2 (by rfl) ⟨1028247, by rfl⟩ : syracuseStep 2741993 = 2056495) B2056495
theorem B1218555 : Blo 1217426 1218555 := bstep (se 1 (by rfl) ⟨913916, by rfl⟩ : syracuseStep 1218555 = 1827833) B1827833
theorem B3086363 : Blo 1217426 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B2111609 : Blo 1217426 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B3086495 : Blo 1217426 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B1218799 : Blo 1217426 1218799 := bstep (se 1 (by rfl) ⟨914099, by rfl⟩ : syracuseStep 1218799 = 1828199) B1828199
theorem B1219039 : Blo 1217426 1219039 := bstep (se 1 (by rfl) ⟨914279, by rfl⟩ : syracuseStep 1219039 = 1828559) B1828559
theorem B2743379 : Blo 1217426 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B5201131 : Blo 1217426 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B7405057 : Blo 1217426 7405057 := bstep (se 2 (by rfl) ⟨2776896, by rfl⟩ : syracuseStep 7405057 = 5553793) B5553793
theorem B13885991 : Blo 1217426 13885991 := bstep (se 1 (by rfl) ⟨10414493, by rfl⟩ : syracuseStep 13885991 = 20828987) B20828987
theorem B8782445 : Blo 1217426 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B1852159 : Blo 1217426 1852159 := bstep (se 1 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 1852159 = 2778239) B2778239
theorem B1827707 : Blo 1217426 1827707 := bstep (se 1 (by rfl) ⟨1370780, by rfl⟩ : syracuseStep 1827707 = 2741561) B2741561
theorem B4113341 : Blo 1217426 4113341 := bstep (se 3 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 4113341 = 1542503) B1542503
theorem B5203079 : Blo 1217426 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B1827995 : Blo 1217426 1827995 := bstep (se 1 (by rfl) ⟨1370996, by rfl⟩ : syracuseStep 1827995 = 2741993) B2741993
theorem B2057575 : Blo 1217426 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B2057663 : Blo 1217426 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B9873409 : Blo 1217426 9873409 := bstep (se 2 (by rfl) ⟨3702528, by rfl⟩ : syracuseStep 9873409 = 7405057) B7405057
theorem B1828919 : Blo 1217426 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B1714927 : Blo 1217426 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B9874217 : Blo 1217426 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B5630957 : Blo 1217426 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B2313299 : Blo 1217426 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B2313451 : Blo 1217426 2313451 := bstep (se 1 (by rfl) ⟨1735088, by rfl⟩ : syracuseStep 2313451 = 3470177) B3470177
theorem B8785385 : Blo 1217426 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B5279401 : Blo 1217426 5279401 := bstep (se 2 (by rfl) ⟨1979775, by rfl⟩ : syracuseStep 5279401 = 3959551) B3959551
theorem B6582383 : Blo 1217426 6582383 := bstep (se 1 (by rfl) ⟨4936787, by rfl⟩ : syracuseStep 6582383 = 9873575) B9873575
theorem B6934841 : Blo 1217426 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B17568413 : Blo 1217426 17568413 := bstep (se 3 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 17568413 = 6588155) B6588155
theorem B2602223 : Blo 1217426 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B17814953 : Blo 1217426 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B6247871 : Blo 1217426 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B6936299 : Blo 1217426 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B15611899 : Blo 1217426 15611899 := bstep (se 1 (by rfl) ⟨11708924, by rfl⟩ : syracuseStep 15611899 = 23417849) B23417849
theorem B2742479 : Blo 1217426 2742479 := bstep (se 1 (by rfl) ⟨2056859, by rfl⟩ : syracuseStep 2742479 = 4113719) B4113719
theorem B4110587 : Blo 1217426 4110587 := bstep (se 1 (by rfl) ⟨3082940, by rfl⟩ : syracuseStep 4110587 = 6165881) B6165881
theorem B19765559 : Blo 1217426 19765559 := bstep (se 1 (by rfl) ⟨14824169, by rfl⟩ : syracuseStep 19765559 = 29648339) B29648339
theorem B2742767 : Blo 1217426 2742767 := bstep (se 1 (by rfl) ⟨2057075, by rfl⟩ : syracuseStep 2742767 = 4114151) B4114151
theorem B1219311 : Blo 1217426 1219311 := bstep (se 1 (by rfl) ⟨914483, by rfl⟩ : syracuseStep 1219311 = 1828967) B1828967
theorem B1219359 : Blo 1217426 1219359 := bstep (se 1 (by rfl) ⟨914519, by rfl⟩ : syracuseStep 1219359 = 1829039) B1829039
theorem B1219391 : Blo 1217426 1219391 := bstep (se 1 (by rfl) ⟨914543, by rfl⟩ : syracuseStep 1219391 = 1829087) B1829087
theorem B1826555 : Blo 1217426 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B17571815 : Blo 1217426 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B13164545 : Blo 1217426 13164545 := bstep (se 2 (by rfl) ⟨4936704, by rfl⟩ : syracuseStep 13164545 = 9873409) B9873409
theorem B6168797 : Blo 1217426 6168797 := bstep (se 3 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 6168797 = 2313299) B2313299
theorem B9257327 : Blo 1217426 9257327 := bstep (se 1 (by rfl) ⟨6942995, by rfl⟩ : syracuseStep 9257327 = 13885991) B13885991
theorem B52708157 : Blo 1217426 52708157 := bstep (se 3 (by rfl) ⟨9882779, by rfl⟩ : syracuseStep 52708157 = 19765559) B19765559
theorem B28156805 : Blo 1217426 28156805 := bstep (se 4 (by rfl) ⟨2639700, by rfl⟩ : syracuseStep 28156805 = 5279401) B5279401
theorem B2286569 : Blo 1217426 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B1828319 : Blo 1217426 1828319 := bstep (se 1 (by rfl) ⟨1371239, by rfl⟩ : syracuseStep 1828319 = 2742479) B2742479
theorem B1828511 : Blo 1217426 1828511 := bstep (se 1 (by rfl) ⟨1371383, by rfl⟩ : syracuseStep 1828511 = 2742767) B2742767
theorem B3753971 : Blo 1217426 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B4623227 : Blo 1217426 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B3468719 : Blo 1217426 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B4165247 : Blo 1217426 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B1371775 : Blo 1217426 1371775 := bstep (se 1 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 1371775 = 2057663) B2057663
theorem B2469545 : Blo 1217426 2469545 := bstep (se 2 (by rfl) ⟨926079, by rfl⟩ : syracuseStep 2469545 = 1852159) B1852159
theorem B4624199 : Blo 1217426 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B2740391 : Blo 1217426 2740391 := bstep (se 1 (by rfl) ⟨2055293, by rfl⟩ : syracuseStep 2740391 = 4110587) B4110587
theorem B3084601 : Blo 1217426 3084601 := bstep (se 2 (by rfl) ⟨1156725, by rfl⟩ : syracuseStep 3084601 = 2313451) B2313451
theorem B6582811 : Blo 1217426 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B1217703 : Blo 1217426 1217703 := bstep (se 1 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 1217703 = 1826555) B1826555
theorem B4388255 : Blo 1217426 4388255 := bstep (se 1 (by rfl) ⟨3291191, by rfl⟩ : syracuseStep 4388255 = 6582383) B6582383
theorem B11712275 : Blo 1217426 11712275 := bstep (se 1 (by rfl) ⟨8784206, by rfl⟩ : syracuseStep 11712275 = 17568413) B17568413
theorem B1218471 : Blo 1217426 1218471 := bstep (se 1 (by rfl) ⟨913853, by rfl⟩ : syracuseStep 1218471 = 1827707) B1827707
theorem B2742227 : Blo 1217426 2742227 := bstep (se 1 (by rfl) ⟨2056670, by rfl⟩ : syracuseStep 2742227 = 4113341) B4113341
theorem B1218663 : Blo 1217426 1218663 := bstep (se 1 (by rfl) ⟨913997, by rfl⟩ : syracuseStep 1218663 = 1827995) B1827995
theorem B1734815 : Blo 1217426 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B11876635 : Blo 1217426 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B1219279 : Blo 1217426 1219279 := bstep (se 1 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 1219279 = 1828919) B1828919
theorem B23419853 : Blo 1217426 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B2743433 : Blo 1217426 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B5856923 : Blo 1217426 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B11714543 : Blo 1217426 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B20815865 : Blo 1217426 20815865 := bstep (se 2 (by rfl) ⟨7805949, by rfl⟩ : syracuseStep 20815865 = 15611899) B15611899
theorem B1826927 : Blo 1217426 1826927 := bstep (se 1 (by rfl) ⟨1370195, by rfl⟩ : syracuseStep 1826927 = 2740391) B2740391
theorem B4112531 : Blo 1217426 4112531 := bstep (se 1 (by rfl) ⟨3084398, by rfl⟩ : syracuseStep 4112531 = 6168797) B6168797
theorem B15835513 : Blo 1217426 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B4112801 : Blo 1217426 4112801 := bstep (se 2 (by rfl) ⟨1542300, by rfl⟩ : syracuseStep 4112801 = 3084601) B3084601
theorem B2925503 : Blo 1217426 2925503 := bstep (se 1 (by rfl) ⟨2194127, by rfl⟩ : syracuseStep 2925503 = 4388255) B4388255
theorem B7808183 : Blo 1217426 7808183 := bstep (se 1 (by rfl) ⟨5856137, by rfl⟩ : syracuseStep 7808183 = 11712275) B11712275
theorem B1828151 : Blo 1217426 1828151 := bstep (se 1 (by rfl) ⟨1371113, by rfl⟩ : syracuseStep 1828151 = 2742227) B2742227
theorem B3082151 : Blo 1217426 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B1828955 : Blo 1217426 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B1829033 : Blo 1217426 1829033 := bstep (se 2 (by rfl) ⟨685887, by rfl⟩ : syracuseStep 1829033 = 1371775) B1371775
theorem B2312479 : Blo 1217426 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B3082799 : Blo 1217426 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B6097517 : Blo 1217426 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B7809695 : Blo 1217426 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B8776363 : Blo 1217426 8776363 := bstep (se 1 (by rfl) ⟨6582272, by rfl⟩ : syracuseStep 8776363 = 13164545) B13164545
theorem B6171551 : Blo 1217426 6171551 := bstep (se 1 (by rfl) ⟨4628663, by rfl⟩ : syracuseStep 6171551 = 9257327) B9257327
theorem B35138771 : Blo 1217426 35138771 := bstep (se 1 (by rfl) ⟨26354078, by rfl⟩ : syracuseStep 35138771 = 52708157) B52708157
theorem B18771203 : Blo 1217426 18771203 := bstep (se 1 (by rfl) ⟨14078402, by rfl⟩ : syracuseStep 18771203 = 28156805) B28156805
theorem B8777081 : Blo 1217426 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B2502647 : Blo 1217426 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B3904615 : Blo 1217426 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B4626173 : Blo 1217426 4626173 := bstep (se 3 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 4626173 = 1734815) B1734815
theorem B1218879 : Blo 1217426 1218879 := bstep (se 1 (by rfl) ⟨914159, by rfl⟩ : syracuseStep 1218879 = 1828319) B1828319
theorem B1219007 : Blo 1217426 1219007 := bstep (se 1 (by rfl) ⟨914255, by rfl⟩ : syracuseStep 1219007 = 1828511) B1828511
theorem B11107325 : Blo 1217426 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B15613235 : Blo 1217426 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B1646363 : Blo 1217426 1646363 := bstep (se 1 (by rfl) ⟨1234772, by rfl⟩ : syracuseStep 1646363 = 2469545) B2469545
theorem B13877243 : Blo 1217426 13877243 := bstep (se 1 (by rfl) ⟨10407932, by rfl⟩ : syracuseStep 13877243 = 20815865) B20815865
theorem B20824613 : Blo 1217426 20824613 := bstep (se 4 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 20824613 = 3904615) B3904615
theorem B1950335 : Blo 1217426 1950335 := bstep (se 1 (by rfl) ⟨1462751, by rfl⟩ : syracuseStep 1950335 = 2925503) B2925503
theorem B4065011 : Blo 1217426 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B4114367 : Blo 1217426 4114367 := bstep (se 1 (by rfl) ⟨3085775, by rfl⟩ : syracuseStep 4114367 = 6171551) B6171551
theorem B5851387 : Blo 1217426 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B9251495 : Blo 1217426 9251495 := bstep (se 1 (by rfl) ⟨6938621, by rfl⟩ : syracuseStep 9251495 = 13877243) B13877243
theorem B3083305 : Blo 1217426 3083305 := bstep (se 2 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 3083305 = 2312479) B2312479
theorem B21114017 : Blo 1217426 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B5205455 : Blo 1217426 5205455 := bstep (se 1 (by rfl) ⟨3904091, by rfl⟩ : syracuseStep 5205455 = 7808183) B7808183
theorem B11701817 : Blo 1217426 11701817 := bstep (se 2 (by rfl) ⟨4388181, by rfl⟩ : syracuseStep 11701817 = 8776363) B8776363
theorem B3084115 : Blo 1217426 3084115 := bstep (se 1 (by rfl) ⟨2313086, by rfl⟩ : syracuseStep 3084115 = 4626173) B4626173
theorem B5206463 : Blo 1217426 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B23425847 : Blo 1217426 23425847 := bstep (se 1 (by rfl) ⟨17569385, by rfl⟩ : syracuseStep 23425847 = 35138771) B35138771
theorem B12514135 : Blo 1217426 12514135 := bstep (se 1 (by rfl) ⟨9385601, by rfl⟩ : syracuseStep 12514135 = 18771203) B18771203
theorem B10408823 : Blo 1217426 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B29619533 : Blo 1217426 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B1668431 : Blo 1217426 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B1217951 : Blo 1217426 1217951 := bstep (se 1 (by rfl) ⟨913463, by rfl⟩ : syracuseStep 1217951 = 1826927) B1826927
theorem B2741687 : Blo 1217426 2741687 := bstep (se 1 (by rfl) ⟨2056265, by rfl⟩ : syracuseStep 2741687 = 4112531) B4112531
theorem B2741867 : Blo 1217426 2741867 := bstep (se 1 (by rfl) ⟨2056400, by rfl⟩ : syracuseStep 2741867 = 4112801) B4112801
theorem B1218767 : Blo 1217426 1218767 := bstep (se 1 (by rfl) ⟨914075, by rfl⟩ : syracuseStep 1218767 = 1828151) B1828151
theorem B2054767 : Blo 1217426 2054767 := bstep (se 1 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 2054767 = 3082151) B3082151
theorem B1219303 : Blo 1217426 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B1219355 : Blo 1217426 1219355 := bstep (se 1 (by rfl) ⟨914516, by rfl⟩ : syracuseStep 1219355 = 1829033) B1829033
theorem B2055199 : Blo 1217426 2055199 := bstep (se 1 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 2055199 = 3082799) B3082799
theorem B4390301 : Blo 1217426 4390301 := bstep (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) B1646363
theorem B6939215 : Blo 1217426 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B4449149 : Blo 1217426 4449149 := bstep (se 3 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 4449149 = 1668431) B1668431
theorem B1827791 : Blo 1217426 1827791 := bstep (se 1 (by rfl) ⟨1370843, by rfl⟩ : syracuseStep 1827791 = 2741687) B2741687
theorem B1827911 : Blo 1217426 1827911 := bstep (se 1 (by rfl) ⟨1370933, by rfl⟩ : syracuseStep 1827911 = 2741867) B2741867
theorem B14076011 : Blo 1217426 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B2926867 : Blo 1217426 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B7801211 : Blo 1217426 7801211 := bstep (se 1 (by rfl) ⟨5850908, by rfl⟩ : syracuseStep 7801211 = 11701817) B11701817
theorem B7801849 : Blo 1217426 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B15617231 : Blo 1217426 15617231 := bstep (se 1 (by rfl) ⟨11712923, by rfl⟩ : syracuseStep 15617231 = 23425847) B23425847
theorem B2739689 : Blo 1217426 2739689 := bstep (se 2 (by rfl) ⟨1027383, by rfl⟩ : syracuseStep 2739689 = 2054767) B2054767
theorem B19746355 : Blo 1217426 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B2740265 : Blo 1217426 2740265 := bstep (se 2 (by rfl) ⟨1027599, by rfl⟩ : syracuseStep 2740265 = 2055199) B2055199
theorem B3470303 : Blo 1217426 3470303 := bstep (se 1 (by rfl) ⟨2602727, by rfl⟩ : syracuseStep 3470303 = 5205455) B5205455
theorem B3470975 : Blo 1217426 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B13883075 : Blo 1217426 13883075 := bstep (se 1 (by rfl) ⟨10412306, by rfl⟩ : syracuseStep 13883075 = 20824613) B20824613
theorem B1300223 : Blo 1217426 1300223 := bstep (se 1 (by rfl) ⟨975167, by rfl⟩ : syracuseStep 1300223 = 1950335) B1950335
theorem B16685513 : Blo 1217426 16685513 := bstep (se 2 (by rfl) ⟨6257067, by rfl⟩ : syracuseStep 16685513 = 12514135) B12514135
theorem B2710007 : Blo 1217426 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B2742911 : Blo 1217426 2742911 := bstep (se 1 (by rfl) ⟨2057183, by rfl⟩ : syracuseStep 2742911 = 4114367) B4114367
theorem B4111073 : Blo 1217426 4111073 := bstep (se 2 (by rfl) ⟨1541652, by rfl⟩ : syracuseStep 4111073 = 3083305) B3083305
theorem B6167663 : Blo 1217426 6167663 := bstep (se 1 (by rfl) ⟨4625747, by rfl⟩ : syracuseStep 6167663 = 9251495) B9251495
theorem B4112153 : Blo 1217426 4112153 := bstep (se 2 (by rfl) ⟨1542057, by rfl⟩ : syracuseStep 4112153 = 3084115) B3084115
theorem B1826843 : Blo 1217426 1826843 := bstep (se 1 (by rfl) ⟨1370132, by rfl⟩ : syracuseStep 1826843 = 2740265) B2740265
theorem B2966099 : Blo 1217426 2966099 := bstep (se 1 (by rfl) ⟨2224574, by rfl⟩ : syracuseStep 2966099 = 4449149) B4449149
theorem B1828607 : Blo 1217426 1828607 := bstep (se 1 (by rfl) ⟨1371455, by rfl⟩ : syracuseStep 1828607 = 2742911) B2742911
theorem B3467261 : Blo 1217426 3467261 := bstep (se 3 (by rfl) ⟨650111, by rfl⟩ : syracuseStep 3467261 = 1300223) B1300223
theorem B3902489 : Blo 1217426 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B2313535 : Blo 1217426 2313535 := bstep (se 1 (by rfl) ⟨1735151, by rfl⟩ : syracuseStep 2313535 = 3470303) B3470303
theorem B2313983 : Blo 1217426 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B9384007 : Blo 1217426 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B1806671 : Blo 1217426 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B2740715 : Blo 1217426 2740715 := bstep (se 1 (by rfl) ⟨2055536, by rfl⟩ : syracuseStep 2740715 = 4111073) B4111073
theorem B2741435 : Blo 1217426 2741435 := bstep (se 1 (by rfl) ⟨2056076, by rfl⟩ : syracuseStep 2741435 = 4112153) B4112153
theorem B4626143 : Blo 1217426 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B1218527 : Blo 1217426 1218527 := bstep (se 1 (by rfl) ⟨913895, by rfl⟩ : syracuseStep 1218527 = 1827791) B1827791
theorem B1218607 : Blo 1217426 1218607 := bstep (se 1 (by rfl) ⟨913955, by rfl⟩ : syracuseStep 1218607 = 1827911) B1827911
theorem B9255383 : Blo 1217426 9255383 := bstep (se 1 (by rfl) ⟨6941537, by rfl⟩ : syracuseStep 9255383 = 13883075) B13883075
theorem B10402465 : Blo 1217426 10402465 := bstep (se 2 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 10402465 = 7801849) B7801849
theorem B5200807 : Blo 1217426 5200807 := bstep (se 1 (by rfl) ⟨3900605, by rfl⟩ : syracuseStep 5200807 = 7801211) B7801211
theorem B11123675 : Blo 1217426 11123675 := bstep (se 1 (by rfl) ⟨8342756, by rfl⟩ : syracuseStep 11123675 = 16685513) B16685513
theorem B26328473 : Blo 1217426 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B4111775 : Blo 1217426 4111775 := bstep (se 1 (by rfl) ⟨3083831, by rfl⟩ : syracuseStep 4111775 = 6167663) B6167663
theorem B10411487 : Blo 1217426 10411487 := bstep (se 1 (by rfl) ⟨7808615, by rfl⟩ : syracuseStep 10411487 = 15617231) B15617231
theorem B1826459 : Blo 1217426 1826459 := bstep (se 1 (by rfl) ⟨1369844, by rfl⟩ : syracuseStep 1826459 = 2739689) B2739689
theorem B1827143 : Blo 1217426 1827143 := bstep (se 1 (by rfl) ⟨1370357, by rfl⟩ : syracuseStep 1827143 = 2740715) B2740715
theorem B1827623 : Blo 1217426 1827623 := bstep (se 1 (by rfl) ⟨1370717, by rfl⟩ : syracuseStep 1827623 = 2741435) B2741435
theorem B4817789 : Blo 1217426 4817789 := bstep (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) B1806671
theorem B13869953 : Blo 1217426 13869953 := bstep (se 2 (by rfl) ⟨5201232, by rfl⟩ : syracuseStep 13869953 = 10402465) B10402465
theorem B2311507 : Blo 1217426 2311507 := bstep (se 1 (by rfl) ⟨1733630, by rfl⟩ : syracuseStep 2311507 = 3467261) B3467261
theorem B6170255 : Blo 1217426 6170255 := bstep (se 1 (by rfl) ⟨4627691, by rfl⟩ : syracuseStep 6170255 = 9255383) B9255383
theorem B7415783 : Blo 1217426 7415783 := bstep (se 1 (by rfl) ⟨5561837, by rfl⟩ : syracuseStep 7415783 = 11123675) B11123675
theorem B6940991 : Blo 1217426 6940991 := bstep (se 1 (by rfl) ⟨5205743, by rfl⟩ : syracuseStep 6940991 = 10411487) B10411487
theorem B1542655 : Blo 1217426 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B12512009 : Blo 1217426 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B3084095 : Blo 1217426 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B6934409 : Blo 1217426 6934409 := bstep (se 2 (by rfl) ⟨2600403, by rfl⟩ : syracuseStep 6934409 = 5200807) B5200807
theorem B7909597 : Blo 1217426 7909597 := bstep (se 3 (by rfl) ⟨1483049, by rfl⟩ : syracuseStep 7909597 = 2966099) B2966099
theorem B3084713 : Blo 1217426 3084713 := bstep (se 2 (by rfl) ⟨1156767, by rfl⟩ : syracuseStep 3084713 = 2313535) B2313535
theorem B2601659 : Blo 1217426 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B17552315 : Blo 1217426 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B2741183 : Blo 1217426 2741183 := bstep (se 1 (by rfl) ⟨2055887, by rfl⟩ : syracuseStep 2741183 = 4111775) B4111775
theorem B1217639 : Blo 1217426 1217639 := bstep (se 1 (by rfl) ⟨913229, by rfl⟩ : syracuseStep 1217639 = 1826459) B1826459
theorem B1217895 : Blo 1217426 1217895 := bstep (se 1 (by rfl) ⟨913421, by rfl⟩ : syracuseStep 1217895 = 1826843) B1826843
theorem B1219071 : Blo 1217426 1219071 := bstep (se 1 (by rfl) ⟨914303, by rfl⟩ : syracuseStep 1219071 = 1828607) B1828607
theorem B2056475 : Blo 1217426 2056475 := bstep (se 1 (by rfl) ⟨1542356, by rfl⟩ : syracuseStep 2056475 = 3084713) B3084713
theorem B3211859 : Blo 1217426 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B1827455 : Blo 1217426 1827455 := bstep (se 1 (by rfl) ⟨1370591, by rfl⟩ : syracuseStep 1827455 = 2741183) B2741183
theorem B2056873 : Blo 1217426 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B4113503 : Blo 1217426 4113503 := bstep (se 1 (by rfl) ⟨3085127, by rfl⟩ : syracuseStep 4113503 = 6170255) B6170255
theorem B3082009 : Blo 1217426 3082009 := bstep (se 2 (by rfl) ⟨1155753, by rfl⟩ : syracuseStep 3082009 = 2311507) B2311507
theorem B8341339 : Blo 1217426 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B4622939 : Blo 1217426 4622939 := bstep (se 1 (by rfl) ⟨3467204, by rfl⟩ : syracuseStep 4622939 = 6934409) B6934409
theorem B10546129 : Blo 1217426 10546129 := bstep (se 2 (by rfl) ⟨3954798, by rfl⟩ : syracuseStep 10546129 = 7909597) B7909597
theorem B4943855 : Blo 1217426 4943855 := bstep (se 1 (by rfl) ⟨3707891, by rfl⟩ : syracuseStep 4943855 = 7415783) B7415783
theorem B46806173 : Blo 1217426 46806173 := bstep (se 3 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 46806173 = 17552315) B17552315
theorem B1218095 : Blo 1217426 1218095 := bstep (se 1 (by rfl) ⟨913571, by rfl⟩ : syracuseStep 1218095 = 1827143) B1827143
theorem B1218415 : Blo 1217426 1218415 := bstep (se 1 (by rfl) ⟨913811, by rfl⟩ : syracuseStep 1218415 = 1827623) B1827623
theorem B9246635 : Blo 1217426 9246635 := bstep (se 1 (by rfl) ⟨6934976, by rfl⟩ : syracuseStep 9246635 = 13869953) B13869953
theorem B4627327 : Blo 1217426 4627327 := bstep (se 1 (by rfl) ⟨3470495, by rfl⟩ : syracuseStep 4627327 = 6940991) B6940991
theorem B6937757 : Blo 1217426 6937757 := bstep (se 3 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 6937757 = 2601659) B2601659
theorem B2056063 : Blo 1217426 2056063 := bstep (se 1 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 2056063 = 3084095) B3084095
theorem B31204115 : Blo 1217426 31204115 := bstep (se 1 (by rfl) ⟨23403086, by rfl⟩ : syracuseStep 31204115 = 46806173) B46806173
theorem B6169769 : Blo 1217426 6169769 := bstep (se 2 (by rfl) ⟨2313663, by rfl⟩ : syracuseStep 6169769 = 4627327) B4627327
theorem B3081959 : Blo 1217426 3081959 := bstep (se 1 (by rfl) ⟨2311469, by rfl⟩ : syracuseStep 3081959 = 4622939) B4622939
theorem B13183613 : Blo 1217426 13183613 := bstep (se 3 (by rfl) ⟨2471927, by rfl⟩ : syracuseStep 13183613 = 4943855) B4943855
theorem B1370983 : Blo 1217426 1370983 := bstep (se 1 (by rfl) ⟨1028237, by rfl⟩ : syracuseStep 1370983 = 2056475) B2056475
theorem B14061505 : Blo 1217426 14061505 := bstep (se 2 (by rfl) ⟨5273064, by rfl⟩ : syracuseStep 14061505 = 10546129) B10546129
theorem B6164423 : Blo 1217426 6164423 := bstep (se 1 (by rfl) ⟨4623317, by rfl⟩ : syracuseStep 6164423 = 9246635) B9246635
theorem B8564957 : Blo 1217426 8564957 := bstep (se 3 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 8564957 = 3211859) B3211859
theorem B4625171 : Blo 1217426 4625171 := bstep (se 1 (by rfl) ⟨3468878, by rfl⟩ : syracuseStep 4625171 = 6937757) B6937757
theorem B4109345 : Blo 1217426 4109345 := bstep (se 2 (by rfl) ⟨1541004, by rfl⟩ : syracuseStep 4109345 = 3082009) B3082009
theorem B11121785 : Blo 1217426 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B2741417 : Blo 1217426 2741417 := bstep (se 2 (by rfl) ⟨1028031, by rfl⟩ : syracuseStep 2741417 = 2056063) B2056063
theorem B1218303 : Blo 1217426 1218303 := bstep (se 1 (by rfl) ⟨913727, by rfl⟩ : syracuseStep 1218303 = 1827455) B1827455
theorem B2742335 : Blo 1217426 2742335 := bstep (se 1 (by rfl) ⟨2056751, by rfl⟩ : syracuseStep 2742335 = 4113503) B4113503
theorem B2742497 : Blo 1217426 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B5709971 : Blo 1217426 5709971 := bstep (se 1 (by rfl) ⟨4282478, by rfl⟩ : syracuseStep 5709971 = 8564957) B8564957
theorem B7414523 : Blo 1217426 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B1827611 : Blo 1217426 1827611 := bstep (se 1 (by rfl) ⟨1370708, by rfl⟩ : syracuseStep 1827611 = 2741417) B2741417
theorem B4113179 : Blo 1217426 4113179 := bstep (se 1 (by rfl) ⟨3084884, by rfl⟩ : syracuseStep 4113179 = 6169769) B6169769
theorem B1827977 : Blo 1217426 1827977 := bstep (se 2 (by rfl) ⟨685491, by rfl⟩ : syracuseStep 1827977 = 1370983) B1370983
theorem B1828223 : Blo 1217426 1828223 := bstep (se 1 (by rfl) ⟨1371167, by rfl⟩ : syracuseStep 1828223 = 2742335) B2742335
theorem B1828331 : Blo 1217426 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B20802743 : Blo 1217426 20802743 := bstep (se 1 (by rfl) ⟨15602057, by rfl⟩ : syracuseStep 20802743 = 31204115) B31204115
theorem B3083447 : Blo 1217426 3083447 := bstep (se 1 (by rfl) ⟨2312585, by rfl⟩ : syracuseStep 3083447 = 4625171) B4625171
theorem B2739563 : Blo 1217426 2739563 := bstep (se 1 (by rfl) ⟨2054672, by rfl⟩ : syracuseStep 2739563 = 4109345) B4109345
theorem B18748673 : Blo 1217426 18748673 := bstep (se 2 (by rfl) ⟨7030752, by rfl⟩ : syracuseStep 18748673 = 14061505) B14061505
theorem B4109615 : Blo 1217426 4109615 := bstep (se 1 (by rfl) ⟨3082211, by rfl⟩ : syracuseStep 4109615 = 6164423) B6164423
theorem B2054639 : Blo 1217426 2054639 := bstep (se 1 (by rfl) ⟨1540979, by rfl⟩ : syracuseStep 2054639 = 3081959) B3081959
theorem B8789075 : Blo 1217426 8789075 := bstep (se 1 (by rfl) ⟨6591806, by rfl⟩ : syracuseStep 8789075 = 13183613) B13183613
theorem B1369759 : Blo 1217426 1369759 := bstep (se 1 (by rfl) ⟨1027319, by rfl⟩ : syracuseStep 1369759 = 2054639) B2054639
theorem B5859383 : Blo 1217426 5859383 := bstep (se 1 (by rfl) ⟨4394537, by rfl⟩ : syracuseStep 5859383 = 8789075) B8789075
theorem B4943015 : Blo 1217426 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B2739743 : Blo 1217426 2739743 := bstep (se 1 (by rfl) ⟨2054807, by rfl⟩ : syracuseStep 2739743 = 4109615) B4109615
theorem B15226589 : Blo 1217426 15226589 := bstep (se 3 (by rfl) ⟨2854985, by rfl⟩ : syracuseStep 15226589 = 5709971) B5709971
theorem B1218407 : Blo 1217426 1218407 := bstep (se 1 (by rfl) ⟨913805, by rfl⟩ : syracuseStep 1218407 = 1827611) B1827611
theorem B2742119 : Blo 1217426 2742119 := bstep (se 1 (by rfl) ⟨2056589, by rfl⟩ : syracuseStep 2742119 = 4113179) B4113179
theorem B1218651 : Blo 1217426 1218651 := bstep (se 1 (by rfl) ⟨913988, by rfl⟩ : syracuseStep 1218651 = 1827977) B1827977
theorem B12499115 : Blo 1217426 12499115 := bstep (se 1 (by rfl) ⟨9374336, by rfl⟩ : syracuseStep 12499115 = 18748673) B18748673
theorem B1218815 : Blo 1217426 1218815 := bstep (se 1 (by rfl) ⟨914111, by rfl⟩ : syracuseStep 1218815 = 1828223) B1828223
theorem B1218887 : Blo 1217426 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B13868495 : Blo 1217426 13868495 := bstep (se 1 (by rfl) ⟨10401371, by rfl⟩ : syracuseStep 13868495 = 20802743) B20802743
theorem B2055631 : Blo 1217426 2055631 := bstep (se 1 (by rfl) ⟨1541723, by rfl⟩ : syracuseStep 2055631 = 3083447) B3083447
theorem B1826375 : Blo 1217426 1826375 := bstep (se 1 (by rfl) ⟨1369781, by rfl⟩ : syracuseStep 1826375 = 2739563) B2739563
theorem B1828079 : Blo 1217426 1828079 := bstep (se 1 (by rfl) ⟨1371059, by rfl⟩ : syracuseStep 1828079 = 2742119) B2742119
theorem B3295343 : Blo 1217426 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B15625021 : Blo 1217426 15625021 := bstep (se 3 (by rfl) ⟨2929691, by rfl⟩ : syracuseStep 15625021 = 5859383) B5859383
theorem B40604237 : Blo 1217426 40604237 := bstep (se 3 (by rfl) ⟨7613294, by rfl⟩ : syracuseStep 40604237 = 15226589) B15226589
theorem B2740841 : Blo 1217426 2740841 := bstep (se 2 (by rfl) ⟨1027815, by rfl⟩ : syracuseStep 2740841 = 2055631) B2055631
theorem B9245663 : Blo 1217426 9245663 := bstep (se 1 (by rfl) ⟨6934247, by rfl⟩ : syracuseStep 9245663 = 13868495) B13868495
theorem B1217583 : Blo 1217426 1217583 := bstep (se 1 (by rfl) ⟨913187, by rfl⟩ : syracuseStep 1217583 = 1826375) B1826375
theorem B33330973 : Blo 1217426 33330973 := bstep (se 3 (by rfl) ⟨6249557, by rfl⟩ : syracuseStep 33330973 = 12499115) B12499115
theorem B1826345 : Blo 1217426 1826345 := bstep (se 2 (by rfl) ⟨684879, by rfl⟩ : syracuseStep 1826345 = 1369759) B1369759
theorem B1826495 : Blo 1217426 1826495 := bstep (se 1 (by rfl) ⟨1369871, by rfl⟩ : syracuseStep 1826495 = 2739743) B2739743
theorem B1827227 : Blo 1217426 1827227 := bstep (se 1 (by rfl) ⟨1370420, by rfl⟩ : syracuseStep 1827227 = 2740841) B2740841
theorem B20833361 : Blo 1217426 20833361 := bstep (se 2 (by rfl) ⟨7812510, by rfl⟩ : syracuseStep 20833361 = 15625021) B15625021
theorem B2196895 : Blo 1217426 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B27069491 : Blo 1217426 27069491 := bstep (se 1 (by rfl) ⟨20302118, by rfl⟩ : syracuseStep 27069491 = 40604237) B40604237
theorem B6163775 : Blo 1217426 6163775 := bstep (se 1 (by rfl) ⟨4622831, by rfl⟩ : syracuseStep 6163775 = 9245663) B9245663
theorem B1217563 : Blo 1217426 1217563 := bstep (se 1 (by rfl) ⟨913172, by rfl⟩ : syracuseStep 1217563 = 1826345) B1826345
theorem B1217663 : Blo 1217426 1217663 := bstep (se 1 (by rfl) ⟨913247, by rfl⟩ : syracuseStep 1217663 = 1826495) B1826495
theorem B1218719 : Blo 1217426 1218719 := bstep (se 1 (by rfl) ⟨914039, by rfl⟩ : syracuseStep 1218719 = 1828079) B1828079
theorem B44441297 : Blo 1217426 44441297 := bstep (se 2 (by rfl) ⟨16665486, by rfl⟩ : syracuseStep 44441297 = 33330973) B33330973
theorem B13888907 : Blo 1217426 13888907 := bstep (se 1 (by rfl) ⟨10416680, by rfl⟩ : syracuseStep 13888907 = 20833361) B20833361
theorem B2929193 : Blo 1217426 2929193 := bstep (se 2 (by rfl) ⟨1098447, by rfl⟩ : syracuseStep 2929193 = 2196895) B2196895
theorem B4109183 : Blo 1217426 4109183 := bstep (se 1 (by rfl) ⟨3081887, by rfl⟩ : syracuseStep 4109183 = 6163775) B6163775
theorem B29627531 : Blo 1217426 29627531 := bstep (se 1 (by rfl) ⟨22220648, by rfl⟩ : syracuseStep 29627531 = 44441297) B44441297
theorem B1218151 : Blo 1217426 1218151 := bstep (se 1 (by rfl) ⟨913613, by rfl⟩ : syracuseStep 1218151 = 1827227) B1827227
theorem B18046327 : Blo 1217426 18046327 := bstep (se 1 (by rfl) ⟨13534745, by rfl⟩ : syracuseStep 18046327 = 27069491) B27069491
theorem B19751687 : Blo 1217426 19751687 := bstep (se 1 (by rfl) ⟨14813765, by rfl⟩ : syracuseStep 19751687 = 29627531) B29627531
theorem B24061769 : Blo 1217426 24061769 := bstep (se 2 (by rfl) ⟨9023163, by rfl⟩ : syracuseStep 24061769 = 18046327) B18046327
theorem B9259271 : Blo 1217426 9259271 := bstep (se 1 (by rfl) ⟨6944453, by rfl⟩ : syracuseStep 9259271 = 13888907) B13888907
theorem B1952795 : Blo 1217426 1952795 := bstep (se 1 (by rfl) ⟨1464596, by rfl⟩ : syracuseStep 1952795 = 2929193) B2929193
theorem B2739455 : Blo 1217426 2739455 := bstep (se 1 (by rfl) ⟨2054591, by rfl⟩ : syracuseStep 2739455 = 4109183) B4109183
theorem B16041179 : Blo 1217426 16041179 := bstep (se 1 (by rfl) ⟨12030884, by rfl⟩ : syracuseStep 16041179 = 24061769) B24061769
theorem B13167791 : Blo 1217426 13167791 := bstep (se 1 (by rfl) ⟨9875843, by rfl⟩ : syracuseStep 13167791 = 19751687) B19751687
theorem B6172847 : Blo 1217426 6172847 := bstep (se 1 (by rfl) ⟨4629635, by rfl⟩ : syracuseStep 6172847 = 9259271) B9259271
theorem B5207453 : Blo 1217426 5207453 := bstep (se 3 (by rfl) ⟨976397, by rfl⟩ : syracuseStep 5207453 = 1952795) B1952795
theorem B1826303 : Blo 1217426 1826303 := bstep (se 1 (by rfl) ⟨1369727, by rfl⟩ : syracuseStep 1826303 = 2739455) B2739455
theorem B4115231 : Blo 1217426 4115231 := bstep (se 1 (by rfl) ⟨3086423, by rfl⟩ : syracuseStep 4115231 = 6172847) B6172847
theorem B10694119 : Blo 1217426 10694119 := bstep (se 1 (by rfl) ⟨8020589, by rfl⟩ : syracuseStep 10694119 = 16041179) B16041179
theorem B8778527 : Blo 1217426 8778527 := bstep (se 1 (by rfl) ⟨6583895, by rfl⟩ : syracuseStep 8778527 = 13167791) B13167791
theorem B1217535 : Blo 1217426 1217535 := bstep (se 1 (by rfl) ⟨913151, by rfl⟩ : syracuseStep 1217535 = 1826303) B1826303
theorem B3471635 : Blo 1217426 3471635 := bstep (se 1 (by rfl) ⟨2603726, by rfl⟩ : syracuseStep 3471635 = 5207453) B5207453
theorem B5852351 : Blo 1217426 5852351 := bstep (se 1 (by rfl) ⟨4389263, by rfl⟩ : syracuseStep 5852351 = 8778527) B8778527
theorem B2314423 : Blo 1217426 2314423 := bstep (se 1 (by rfl) ⟨1735817, by rfl⟩ : syracuseStep 2314423 = 3471635) B3471635
theorem B14258825 : Blo 1217426 14258825 := bstep (se 2 (by rfl) ⟨5347059, by rfl⟩ : syracuseStep 14258825 = 10694119) B10694119
theorem B2743487 : Blo 1217426 2743487 := bstep (se 1 (by rfl) ⟨2057615, by rfl⟩ : syracuseStep 2743487 = 4115231) B4115231
theorem B3901567 : Blo 1217426 3901567 := bstep (se 1 (by rfl) ⟨2926175, by rfl⟩ : syracuseStep 3901567 = 5852351) B5852351
theorem B1828991 : Blo 1217426 1828991 := bstep (se 1 (by rfl) ⟨1371743, by rfl⟩ : syracuseStep 1828991 = 2743487) B2743487
theorem B9505883 : Blo 1217426 9505883 := bstep (se 1 (by rfl) ⟨7129412, by rfl⟩ : syracuseStep 9505883 = 14258825) B14258825
theorem B3085897 : Blo 1217426 3085897 := bstep (se 2 (by rfl) ⟨1157211, by rfl⟩ : syracuseStep 3085897 = 2314423) B2314423
theorem B5202089 : Blo 1217426 5202089 := bstep (se 2 (by rfl) ⟨1950783, by rfl⟩ : syracuseStep 5202089 = 3901567) B3901567
theorem B4114529 : Blo 1217426 4114529 := bstep (se 2 (by rfl) ⟨1542948, by rfl⟩ : syracuseStep 4114529 = 3085897) B3085897
theorem B25349021 : Blo 1217426 25349021 := bstep (se 3 (by rfl) ⟨4752941, by rfl⟩ : syracuseStep 25349021 = 9505883) B9505883
theorem B1219327 : Blo 1217426 1219327 := bstep (se 1 (by rfl) ⟨914495, by rfl⟩ : syracuseStep 1219327 = 1828991) B1828991
theorem B3468059 : Blo 1217426 3468059 := bstep (se 1 (by rfl) ⟨2601044, by rfl⟩ : syracuseStep 3468059 = 5202089) B5202089
theorem B2743019 : Blo 1217426 2743019 := bstep (se 1 (by rfl) ⟨2057264, by rfl⟩ : syracuseStep 2743019 = 4114529) B4114529
theorem B16899347 : Blo 1217426 16899347 := bstep (se 1 (by rfl) ⟨12674510, by rfl⟩ : syracuseStep 16899347 = 25349021) B25349021
theorem B1828679 : Blo 1217426 1828679 := bstep (se 1 (by rfl) ⟨1371509, by rfl⟩ : syracuseStep 1828679 = 2743019) B2743019
theorem B2312039 : Blo 1217426 2312039 := bstep (se 1 (by rfl) ⟨1734029, by rfl⟩ : syracuseStep 2312039 = 3468059) B3468059
theorem B11266231 : Blo 1217426 11266231 := bstep (se 1 (by rfl) ⟨8449673, by rfl⟩ : syracuseStep 11266231 = 16899347) B16899347
theorem B1541359 : Blo 1217426 1541359 := bstep (se 1 (by rfl) ⟨1156019, by rfl⟩ : syracuseStep 1541359 = 2312039) B2312039
theorem B15021641 : Blo 1217426 15021641 := bstep (se 2 (by rfl) ⟨5633115, by rfl⟩ : syracuseStep 15021641 = 11266231) B11266231
theorem B1219119 : Blo 1217426 1219119 := bstep (se 1 (by rfl) ⟨914339, by rfl⟩ : syracuseStep 1219119 = 1828679) B1828679
theorem B10014427 : Blo 1217426 10014427 := bstep (se 1 (by rfl) ⟨7510820, by rfl⟩ : syracuseStep 10014427 = 15021641) B15021641
theorem B2055145 : Blo 1217426 2055145 := bstep (se 2 (by rfl) ⟨770679, by rfl⟩ : syracuseStep 2055145 = 1541359) B1541359
theorem B2740193 : Blo 1217426 2740193 := bstep (se 2 (by rfl) ⟨1027572, by rfl⟩ : syracuseStep 2740193 = 2055145) B2055145
theorem B13352569 : Blo 1217426 13352569 := bstep (se 2 (by rfl) ⟨5007213, by rfl⟩ : syracuseStep 13352569 = 10014427) B10014427
theorem B284854805 : Blo 1217426 284854805 := bstep (se 6 (by rfl) ⟨6676284, by rfl⟩ : syracuseStep 284854805 = 13352569) B13352569
theorem B1826795 : Blo 1217426 1826795 := bstep (se 1 (by rfl) ⟨1370096, by rfl⟩ : syracuseStep 1826795 = 2740193) B2740193
theorem B189903203 : Blo 1217426 189903203 := bstep (se 1 (by rfl) ⟨142427402, by rfl⟩ : syracuseStep 189903203 = 284854805) B284854805
theorem B1217863 : Blo 1217426 1217863 := bstep (se 1 (by rfl) ⟨913397, by rfl⟩ : syracuseStep 1217863 = 1826795) B1826795
theorem B126602135 : Blo 1217426 126602135 := bstep (se 1 (by rfl) ⟨94951601, by rfl⟩ : syracuseStep 126602135 = 189903203) B189903203
theorem B84401423 : Blo 1217426 84401423 := bstep (se 1 (by rfl) ⟨63301067, by rfl⟩ : syracuseStep 84401423 = 126602135) B126602135
theorem B56267615 : Blo 1217426 56267615 := bstep (se 1 (by rfl) ⟨42200711, by rfl⟩ : syracuseStep 56267615 = 84401423) B84401423
theorem B37511743 : Blo 1217426 37511743 := bstep (se 1 (by rfl) ⟨28133807, by rfl⟩ : syracuseStep 37511743 = 56267615) B56267615
theorem B50015657 : Blo 1217426 50015657 := bstep (se 2 (by rfl) ⟨18755871, by rfl⟩ : syracuseStep 50015657 = 37511743) B37511743
theorem B133375085 : Blo 1217426 133375085 := bstep (se 3 (by rfl) ⟨25007828, by rfl⟩ : syracuseStep 133375085 = 50015657) B50015657
theorem B88916723 : Blo 1217426 88916723 := bstep (se 1 (by rfl) ⟨66687542, by rfl⟩ : syracuseStep 88916723 = 133375085) B133375085
theorem B59277815 : Blo 1217426 59277815 := bstep (se 1 (by rfl) ⟨44458361, by rfl⟩ : syracuseStep 59277815 = 88916723) B88916723
theorem B39518543 : Blo 1217426 39518543 := bstep (se 1 (by rfl) ⟨29638907, by rfl⟩ : syracuseStep 39518543 = 59277815) B59277815
theorem B26345695 : Blo 1217426 26345695 := bstep (se 1 (by rfl) ⟨19759271, by rfl⟩ : syracuseStep 26345695 = 39518543) B39518543
theorem B35127593 : Blo 1217426 35127593 := bstep (se 2 (by rfl) ⟨13172847, by rfl⟩ : syracuseStep 35127593 = 26345695) B26345695
theorem B23418395 : Blo 1217426 23418395 := bstep (se 1 (by rfl) ⟨17563796, by rfl⟩ : syracuseStep 23418395 = 35127593) B35127593
theorem B15612263 : Blo 1217426 15612263 := bstep (se 1 (by rfl) ⟨11709197, by rfl⟩ : syracuseStep 15612263 = 23418395) B23418395
theorem B10408175 : Blo 1217426 10408175 := bstep (se 1 (by rfl) ⟨7806131, by rfl⟩ : syracuseStep 10408175 = 15612263) B15612263
theorem B6938783 : Blo 1217426 6938783 := bstep (se 1 (by rfl) ⟨5204087, by rfl⟩ : syracuseStep 6938783 = 10408175) B10408175
theorem B4625855 : Blo 1217426 4625855 := bstep (se 1 (by rfl) ⟨3469391, by rfl⟩ : syracuseStep 4625855 = 6938783) B6938783
theorem B3083903 : Blo 1217426 3083903 := bstep (se 1 (by rfl) ⟨2312927, by rfl⟩ : syracuseStep 3083903 = 4625855) B4625855
theorem B2055935 : Blo 1217426 2055935 := bstep (se 1 (by rfl) ⟨1541951, by rfl⟩ : syracuseStep 2055935 = 3083903) B3083903
theorem B1370623 : Blo 1217426 1370623 := bstep (se 1 (by rfl) ⟨1027967, by rfl⟩ : syracuseStep 1370623 = 2055935) B2055935
theorem B1827497 : Blo 1217426 1827497 := bstep (se 2 (by rfl) ⟨685311, by rfl⟩ : syracuseStep 1827497 = 1370623) B1370623
theorem B1218331 : Blo 1217426 1218331 := bstep (se 1 (by rfl) ⟨913748, by rfl⟩ : syracuseStep 1218331 = 1827497) B1827497

theorem C0 (j : ℕ) (h1 : 304356 ≤ j) (h2 : j ≤ 304855) : Blo 1217426 (4 * j + 3) := by
  interval_cases j
  · exact B1217427
  · exact B1217431
  · exact B1217435
  · exact B1217439
  · exact B1217443
  · exact B1217447
  · exact B1217451
  · exact B1217455
  · exact B1217459
  · exact B1217463
  · exact B1217467
  · exact B1217471
  · exact B1217475
  · exact B1217479
  · exact B1217483
  · exact B1217487
  · exact B1217491
  · exact B1217495
  · exact B1217499
  · exact B1217503
  · exact B1217507
  · exact B1217511
  · exact B1217515
  · exact B1217519
  · exact B1217523
  · exact B1217527
  · exact B1217531
  · exact B1217535
  · exact B1217539
  · exact B1217543
  · exact B1217547
  · exact B1217551
  · exact B1217555
  · exact B1217559
  · exact B1217563
  · exact B1217567
  · exact B1217571
  · exact B1217575
  · exact B1217579
  · exact B1217583
  · exact B1217587
  · exact B1217591
  · exact B1217595
  · exact B1217599
  · exact B1217603
  · exact B1217607
  · exact B1217611
  · exact B1217615
  · exact B1217619
  · exact B1217623
  · exact B1217627
  · exact B1217631
  · exact B1217635
  · exact B1217639
  · exact B1217643
  · exact B1217647
  · exact B1217651
  · exact B1217655
  · exact B1217659
  · exact B1217663
  · exact B1217667
  · exact B1217671
  · exact B1217675
  · exact B1217679
  · exact B1217683
  · exact B1217687
  · exact B1217691
  · exact B1217695
  · exact B1217699
  · exact B1217703
  · exact B1217707
  · exact B1217711
  · exact B1217715
  · exact B1217719
  · exact B1217723
  · exact B1217727
  · exact B1217731
  · exact B1217735
  · exact B1217739
  · exact B1217743
  · exact B1217747
  · exact B1217751
  · exact B1217755
  · exact B1217759
  · exact B1217763
  · exact B1217767
  · exact B1217771
  · exact B1217775
  · exact B1217779
  · exact B1217783
  · exact B1217787
  · exact B1217791
  · exact B1217795
  · exact B1217799
  · exact B1217803
  · exact B1217807
  · exact B1217811
  · exact B1217815
  · exact B1217819
  · exact B1217823
  · exact B1217827
  · exact B1217831
  · exact B1217835
  · exact B1217839
  · exact B1217843
  · exact B1217847
  · exact B1217851
  · exact B1217855
  · exact B1217859
  · exact B1217863
  · exact B1217867
  · exact B1217871
  · exact B1217875
  · exact B1217879
  · exact B1217883
  · exact B1217887
  · exact B1217891
  · exact B1217895
  · exact B1217899
  · exact B1217903
  · exact B1217907
  · exact B1217911
  · exact B1217915
  · exact B1217919
  · exact B1217923
  · exact B1217927
  · exact B1217931
  · exact B1217935
  · exact B1217939
  · exact B1217943
  · exact B1217947
  · exact B1217951
  · exact B1217955
  · exact B1217959
  · exact B1217963
  · exact B1217967
  · exact B1217971
  · exact B1217975
  · exact B1217979
  · exact B1217983
  · exact B1217987
  · exact B1217991
  · exact B1217995
  · exact B1217999
  · exact B1218003
  · exact B1218007
  · exact B1218011
  · exact B1218015
  · exact B1218019
  · exact B1218023
  · exact B1218027
  · exact B1218031
  · exact B1218035
  · exact B1218039
  · exact B1218043
  · exact B1218047
  · exact B1218051
  · exact B1218055
  · exact B1218059
  · exact B1218063
  · exact B1218067
  · exact B1218071
  · exact B1218075
  · exact B1218079
  · exact B1218083
  · exact B1218087
  · exact B1218091
  · exact B1218095
  · exact B1218099
  · exact B1218103
  · exact B1218107
  · exact B1218111
  · exact B1218115
  · exact B1218119
  · exact B1218123
  · exact B1218127
  · exact B1218131
  · exact B1218135
  · exact B1218139
  · exact B1218143
  · exact B1218147
  · exact B1218151
  · exact B1218155
  · exact B1218159
  · exact B1218163
  · exact B1218167
  · exact B1218171
  · exact B1218175
  · exact B1218179
  · exact B1218183
  · exact B1218187
  · exact B1218191
  · exact B1218195
  · exact B1218199
  · exact B1218203
  · exact B1218207
  · exact B1218211
  · exact B1218215
  · exact B1218219
  · exact B1218223
  · exact B1218227
  · exact B1218231
  · exact B1218235
  · exact B1218239
  · exact B1218243
  · exact B1218247
  · exact B1218251
  · exact B1218255
  · exact B1218259
  · exact B1218263
  · exact B1218267
  · exact B1218271
  · exact B1218275
  · exact B1218279
  · exact B1218283
  · exact B1218287
  · exact B1218291
  · exact B1218295
  · exact B1218299
  · exact B1218303
  · exact B1218307
  · exact B1218311
  · exact B1218315
  · exact B1218319
  · exact B1218323
  · exact B1218327
  · exact B1218331
  · exact B1218335
  · exact B1218339
  · exact B1218343
  · exact B1218347
  · exact B1218351
  · exact B1218355
  · exact B1218359
  · exact B1218363
  · exact B1218367
  · exact B1218371
  · exact B1218375
  · exact B1218379
  · exact B1218383
  · exact B1218387
  · exact B1218391
  · exact B1218395
  · exact B1218399
  · exact B1218403
  · exact B1218407
  · exact B1218411
  · exact B1218415
  · exact B1218419
  · exact B1218423
  · exact B1218427
  · exact B1218431
  · exact B1218435
  · exact B1218439
  · exact B1218443
  · exact B1218447
  · exact B1218451
  · exact B1218455
  · exact B1218459
  · exact B1218463
  · exact B1218467
  · exact B1218471
  · exact B1218475
  · exact B1218479
  · exact B1218483
  · exact B1218487
  · exact B1218491
  · exact B1218495
  · exact B1218499
  · exact B1218503
  · exact B1218507
  · exact B1218511
  · exact B1218515
  · exact B1218519
  · exact B1218523
  · exact B1218527
  · exact B1218531
  · exact B1218535
  · exact B1218539
  · exact B1218543
  · exact B1218547
  · exact B1218551
  · exact B1218555
  · exact B1218559
  · exact B1218563
  · exact B1218567
  · exact B1218571
  · exact B1218575
  · exact B1218579
  · exact B1218583
  · exact B1218587
  · exact B1218591
  · exact B1218595
  · exact B1218599
  · exact B1218603
  · exact B1218607
  · exact B1218611
  · exact B1218615
  · exact B1218619
  · exact B1218623
  · exact B1218627
  · exact B1218631
  · exact B1218635
  · exact B1218639
  · exact B1218643
  · exact B1218647
  · exact B1218651
  · exact B1218655
  · exact B1218659
  · exact B1218663
  · exact B1218667
  · exact B1218671
  · exact B1218675
  · exact B1218679
  · exact B1218683
  · exact B1218687
  · exact B1218691
  · exact B1218695
  · exact B1218699
  · exact B1218703
  · exact B1218707
  · exact B1218711
  · exact B1218715
  · exact B1218719
  · exact B1218723
  · exact B1218727
  · exact B1218731
  · exact B1218735
  · exact B1218739
  · exact B1218743
  · exact B1218747
  · exact B1218751
  · exact B1218755
  · exact B1218759
  · exact B1218763
  · exact B1218767
  · exact B1218771
  · exact B1218775
  · exact B1218779
  · exact B1218783
  · exact B1218787
  · exact B1218791
  · exact B1218795
  · exact B1218799
  · exact B1218803
  · exact B1218807
  · exact B1218811
  · exact B1218815
  · exact B1218819
  · exact B1218823
  · exact B1218827
  · exact B1218831
  · exact B1218835
  · exact B1218839
  · exact B1218843
  · exact B1218847
  · exact B1218851
  · exact B1218855
  · exact B1218859
  · exact B1218863
  · exact B1218867
  · exact B1218871
  · exact B1218875
  · exact B1218879
  · exact B1218883
  · exact B1218887
  · exact B1218891
  · exact B1218895
  · exact B1218899
  · exact B1218903
  · exact B1218907
  · exact B1218911
  · exact B1218915
  · exact B1218919
  · exact B1218923
  · exact B1218927
  · exact B1218931
  · exact B1218935
  · exact B1218939
  · exact B1218943
  · exact B1218947
  · exact B1218951
  · exact B1218955
  · exact B1218959
  · exact B1218963
  · exact B1218967
  · exact B1218971
  · exact B1218975
  · exact B1218979
  · exact B1218983
  · exact B1218987
  · exact B1218991
  · exact B1218995
  · exact B1218999
  · exact B1219003
  · exact B1219007
  · exact B1219011
  · exact B1219015
  · exact B1219019
  · exact B1219023
  · exact B1219027
  · exact B1219031
  · exact B1219035
  · exact B1219039
  · exact B1219043
  · exact B1219047
  · exact B1219051
  · exact B1219055
  · exact B1219059
  · exact B1219063
  · exact B1219067
  · exact B1219071
  · exact B1219075
  · exact B1219079
  · exact B1219083
  · exact B1219087
  · exact B1219091
  · exact B1219095
  · exact B1219099
  · exact B1219103
  · exact B1219107
  · exact B1219111
  · exact B1219115
  · exact B1219119
  · exact B1219123
  · exact B1219127
  · exact B1219131
  · exact B1219135
  · exact B1219139
  · exact B1219143
  · exact B1219147
  · exact B1219151
  · exact B1219155
  · exact B1219159
  · exact B1219163
  · exact B1219167
  · exact B1219171
  · exact B1219175
  · exact B1219179
  · exact B1219183
  · exact B1219187
  · exact B1219191
  · exact B1219195
  · exact B1219199
  · exact B1219203
  · exact B1219207
  · exact B1219211
  · exact B1219215
  · exact B1219219
  · exact B1219223
  · exact B1219227
  · exact B1219231
  · exact B1219235
  · exact B1219239
  · exact B1219243
  · exact B1219247
  · exact B1219251
  · exact B1219255
  · exact B1219259
  · exact B1219263
  · exact B1219267
  · exact B1219271
  · exact B1219275
  · exact B1219279
  · exact B1219283
  · exact B1219287
  · exact B1219291
  · exact B1219295
  · exact B1219299
  · exact B1219303
  · exact B1219307
  · exact B1219311
  · exact B1219315
  · exact B1219319
  · exact B1219323
  · exact B1219327
  · exact B1219331
  · exact B1219335
  · exact B1219339
  · exact B1219343
  · exact B1219347
  · exact B1219351
  · exact B1219355
  · exact B1219359
  · exact B1219363
  · exact B1219367
  · exact B1219371
  · exact B1219375
  · exact B1219379
  · exact B1219383
  · exact B1219387
  · exact B1219391
  · exact B1219395
  · exact B1219399
  · exact B1219403
  · exact B1219407
  · exact B1219411
  · exact B1219415
  · exact B1219419
  · exact B1219423

theorem solution (m : ℕ) (hlo : 1217426 ≤ m) (hhi : m ≤ 1219426) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 304356 ≤ j := by omega
    have hj2 : j ≤ 304855 := by omega
    have hb : Blo 1217426 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
